// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_xhp.ml`. See `hh/PORTING.md`.
use oxidized::aast;
use oxidized::ast_defs;
use oxidized::message::Message;
use oxidized::nast;
use oxidized::pos::Pos;

use crate::decl_entry;
use crate::folded_class as cls;
use crate::naming_special_names as sn;
use crate::s_set;
use crate::typing_defs::ClassElt;
use crate::typing_defs::ExpandEnv;
use crate::typing_defs::empty_expand_env;
use crate::typing_defs::get_ce_xhp_attr;
use crate::typing_defs::is_dynamic;
use crate::typing_defs_core::ShapeType;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_reason;
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::Lazy;
use crate::typing_error::primary;
use crate::typing_error_utils;
use crate::typing_make_type as make_type;
use crate::typing_phase as phase;
use crate::typing_print;
use crate::typing_reason as reason;
use crate::typing_reason::Ureason;
use crate::typing_solver;
use crate::typing_utils as tutils;

fn raise_xhp_required(env: &Env, pos: &Pos, ureason: &Ureason, ty: &Ty) -> typing_error::T {
    let ty_str = {
        let env = env.clone();
        let ty = ty.clone();
        Lazy::new(move || typing_print::error(None, &env, &ty))
    };
    let msgl = {
        let r = get_reason(ty).clone();
        ty_str.map(move |ty_str| {
            reason::to_string(&format!("This is {}", ty_str), &r)
                .into_iter()
                .map(|(p, s)| Message(p, s.into()))
                .collect()
        })
    };
    typing_error::xhp(primary::xhp::T::XhpRequired {
        pos: pos.clone(),
        why_xhp: reason::string_of_ureason(ureason),
        ty_reason_msg: msgl,
    })
}

/// Given class info, produces the subset of props that are XHP attributes
fn xhp_attributes_for_class(info: &cls::T) -> Vec<(String, ClassElt)> {
    cls::props(info)
        .into_iter()
        .filter(|(_, elt_)| get_ce_xhp_attr(elt_).is_some())
        .collect()
}

/// The XHP classes found (the type, its type arguments and the class) and the
/// types that are not XHP.
type Gathered = (Vec<(Ty, Vec<Ty>, cls::T)>, Vec<Ty>);

/// Walks a type and gathers all the XHP, adding an error when we encounter a
/// type that is not XHP.
fn walk_and_gather_xhp_(env: &mut Env, pos: &Pos, cty: Ty) -> Gathered {
    let (ty_err_opt, cty) =
        typing_solver::expand_type_and_solve(env, None, "an XHP instance", pos.clone(), cty);
    if let Some(err) = &ty_err_opt {
        typing_error_utils::add_typing_error(err, env)
    }
    match get_node(&cty) {
        Ty_::Tany(_) | Ty_::Tdynamic(_) => (vec![], vec![]),
        Ty_::Tunion(tyl) => {
            // If it's a union, make sure it can only be XHP and add every
            // possible class.
            walk_list_and_gather_xhp(env, pos, tyl)
        }
        Ty_::Tintersection(tyl) => {
            // If any conjunct is dynamic then we let it pass
            if tyl.iter().any(is_dynamic) {
                (vec![], vec![])
            } else {
                let (xhp, non_xhp) = walk_list_and_gather_xhp(env, pos, tyl);
                // ok to have non_xhp if there are some xhp
                let non_xhp = if !xhp.is_empty() { vec![] } else { non_xhp };
                (xhp, non_xhp)
            }
        }
        Ty_::Tgeneric(name) if name == "this" => {
            // This is unsound, but we want to do best-effort checking
            // of attribute spreads even on XHP classes not marked `final`. We should
            // implement <<__ConsistentAttributes>> as a way to make this hacky
            // inference sound and check it before doing this conversion.
            match env::get_self_ty(env) {
                None => (vec![], vec![]),
                Some(ty) => walk_and_gather_xhp_(env, pos, ty),
            }
        }
        Ty_::Tgeneric(_) | Ty_::Tdependent(..) | Ty_::Tnewtype(..) => {
            let tyl = tutils::get_concrete_supertypes(None, None, None, true, env, cty.clone());
            walk_list_and_gather_xhp(env, pos, &tyl)
        }
        Ty_::Tclass(sid, _, tyl) => {
            // Here's where we actually check the declaration
            match env::get_class(env, &sid.1) {
                decl_entry::T::Found(class_) if cls::is_xhp(&class_) => {
                    (vec![(cty.clone(), tyl.clone(), class_)], vec![])
                }
                _ => (vec![], vec![cty.clone()]),
            }
        }
        Ty_::Tnonnull
        | Ty_::TvecOrDict(..)
        | Ty_::Toption(_)
        | Ty_::Tprim(_)
        | Ty_::Tvar(_)
        | Ty_::Tfun(_)
        | Ty_::Tlabel(_)
        | Ty_::Ttuple(_)
        | Ty_::Tshape(ShapeType::ShapeSimple(_) | ShapeType::ShapeSplat(_))
        | Ty_::Tneg(_) => (vec![], vec![cty.clone()]),
        Ty_::Taccess(_) => (vec![], vec![cty.clone()]),
        Ty_::TclassPtr(_) => {
            // TODO(T199606542) Does it matter if we have a class pointer to an XHP class?
            (vec![], vec![cty.clone()])
        }
    }
}

/// `List.fold`, putting the results of each type before those of the types
/// before it (`xhp_acc' @ xhp_acc`).
fn walk_list_and_gather_xhp(env: &mut Env, pos: &Pos, tyl: &[Ty]) -> Gathered {
    let mut xhp_acc = vec![];
    let mut non_xhp_acc = vec![];
    for ty in tyl {
        let (mut xhp_acc_, mut non_xhp_acc_) = walk_and_gather_xhp_(env, pos, ty.clone());
        xhp_acc_.extend(xhp_acc);
        non_xhp_acc_.extend(non_xhp_acc);
        xhp_acc = xhp_acc_;
        non_xhp_acc = non_xhp_acc_;
    }
    (xhp_acc, non_xhp_acc)
}

/// This is used in computing all possible attributes for XHP spreads.
///
/// Given a type `cty` that should represent an XHP instance, gather all the
/// XHP attributes and their localized types to verify compatibility with the
/// XHP onto which we are spreading.
///
/// For a given type, enforce that we have an XHP class and return the complete
/// list of possible attributes for typechecking the spread operator.
pub fn get_spread_attributes(
    env: &mut Env,
    pos: &Pos,
    onto_xhp: &cls::T,
    cty: &Ty,
) -> (Option<typing_error::T>, Vec<(aast::Pstring, (Pos, Ty))>) {
    let onto_attrs: s_set::T = xhp_attributes_for_class(onto_xhp)
        .into_iter()
        .map(|(k, _)| k)
        .collect();
    let (possible_xhp, non_xhp) = walk_and_gather_xhp_(env, pos, cty.clone());
    let xhp_required_err_opt = typing_error::multiple_opt(
        non_xhp
            .iter()
            .map(|ty| raise_xhp_required(env, pos, &Ureason::URxhpSpread, ty))
            .collect(),
    );
    let xhp_to_attrs = |env: &mut Env, (xhp_ty, tparams, xhp_info): &(Ty, Vec<Ty>, cls::T)| {
        let attrs = xhp_attributes_for_class(xhp_info);
        // Compute the intersection and then localize the types
        let attrs: Vec<(String, ClassElt)> = attrs
            .into_iter()
            .filter(|(k, _)| onto_attrs.contains(k))
            .collect();
        // XHP does not allow generics in the class declaration, so
        // we don't need to perform any substitutions
        let ety_env = ExpandEnv {
            this_ty: xhp_ty.clone(),
            substs: tutils::make_locl_subst_for_class_tparams(xhp_info, tparams),
            ..empty_expand_env()
        };
        crate::common::list::map_env_ty_err_opt(
            env,
            &attrs,
            |env: &mut Env, (k, ce): &(String, ClassElt)| {
                let ty = &*ce.ce_type;
                let (ty_err, ty) = phase::localize(&ety_env, env, ty);
                (ty_err, ((pos.clone(), k.clone()), (pos.clone(), ty)))
            },
            typing_error::multiple_opt,
        )
    };
    let (locl_ty_err_opt, attrs) =
        crate::common::list::map_env_ty_err_opt(env, &possible_xhp, xhp_to_attrs, typing_error::multiple_opt);
    let ty_err_opt = match (xhp_required_err_opt, locl_ty_err_opt) {
        (Some(e1), Some(e2)) => Some(typing_error::both(e1, e2)),
        (Some(e), None) | (None, Some(e)) => Some(e),
        (None, None) => None,
    };
    (ty_err_opt, attrs.into_iter().flatten().collect())
}

/// Verify that an XHP body expression is legal.
///
/// Typing rules for the body expressions of an XHP literal.
pub fn is_xhp_child(env: &Env, pos: &Pos, ty: &Ty) -> (bool, Option<typing_error::T>) {
    let r = reason::witness(pos.clone());
    // XHPChild
    let ty_child = make_type::class_type(r.clone(), sn::classes::XHP_CHILD.to_string(), vec![]);
    // Any Traversable
    let ty_traversable = make_type::traversable(r.clone(), make_type::mixed(r.clone()));
    typing_solver::is_sub_type(
        env,
        ty,
        &make_type::nullable(
            r.clone(),
            make_type::union(
                r.clone(),
                vec![make_type::dynamic(r), ty_child, ty_traversable],
            ),
        ),
    )
}

/// Rewrites an Xml node into a New node. The resulting New expression has
/// four arguments. This mimics the rewrite undergone before the emitter is
/// run.
///
/// For example,
/// `<p colour='blue'>Hi</p>;`
/// becomes
/// `new :p(darray['colour' => 'blue'], varray['Hi'],"",1);`
///
/// The first two arguments are for the attributes and children. The last two
/// arguments are for the filename and line number. These are irrelevant from a
/// typing perspective, so they are set to arbitrary defaults.
pub fn rewrite_xml_into_new(
    pos: Pos,
    sid: aast::Sid,
    attributes: Vec<nast::XhpAttribute>,
    children: Vec<nast::Expr>,
) -> nast::Expr {
    let sid_ann = sid.0.clone();
    let cid = aast::ClassId_::CI(sid);
    let mk_attribute = |ix: usize, attr: nast::XhpAttribute| match attr {
        aast::XhpAttribute::XhpSimple(aast::XhpSimple {
            name: (attr_pos, attr_key),
            expr: exp,
            ..
        }) => {
            let attr_aux = attr_pos;
            let key = aast::Expr((), attr_aux, aast::Expr_::String(attr_key.into()));
            aast::Field(key, exp)
        }
        aast::XhpAttribute::XhpSpread(exp) => {
            let attr_key = format!("...${}", ix);
            let attr_key_ann = pos.clone();
            let key = aast::Expr((), attr_key_ann, aast::Expr_::String(attr_key.into()));
            aast::Field(key, exp)
        }
    };
    let attributes = {
        let attributes: Vec<nast::Field> = attributes
            .into_iter()
            .enumerate()
            .map(|(ix, attr)| mk_attribute(ix, attr))
            .collect();
        aast::Expr(
            (),
            pos.clone(),
            aast::Expr_::KeyValCollection(Box::new((
                (pos.clone(), aast::KvcKind::Dict),
                None,
                attributes,
            ))),
        )
    };
    let children = aast::Expr(
        (),
        pos.clone(),
        aast::Expr_::ValCollection(Box::new(((pos.clone(), aast::VcKind::Vec), None, children))),
    );
    let file = aast::Expr((), pos.clone(), aast::Expr_::String("".into()));
    let line = aast::Expr((), pos, aast::Expr_::Int("1".to_string()));
    let args: Vec<nast::Argument> = vec![attributes, children, file, line]
        .into_iter()
        .map(aast::Argument::Anormal)
        .collect();
    aast::Expr(
        (),
        sid_ann.clone(),
        aast::Expr_::New(Box::new((
            aast::ClassId((), sid_ann, cid),
            vec![],
            args,
            None,
            (),
        ))),
    )
}

/// Rewrites an Xml attribute access into a call to getAttribute. The
/// resulting Call expression has one argument fake string argument to match the
/// expected parameter of getAttribute.
///
/// For example,
/// `$xml->:attr;`
/// becomes
/// `$xml->getAttribute('');`
///
/// The null flavor argument is indicates an expression of the form
/// `$xml?->:attr`
pub fn rewrite_attribute_access_into_call(
    pos: Pos,
    exp: nast::Expr,
    nullflavor: aast::OperatorNullFlavor,
) -> nast::Expr {
    let obj_get_exp = aast::Expr(
        (),
        pos.clone(),
        aast::Expr_::ObjGet(Box::new((
            exp,
            aast::Expr(
                (),
                pos.clone(),
                aast::Expr_::Id(Box::new(ast_defs::Id(
                    pos.clone(),
                    "getAttribute".to_string(),
                ))),
            ),
            nullflavor,
            ast_defs::PropOrMethod::IsMethod,
        ))),
    );
    aast::Expr(
        (),
        pos.clone(),
        aast::Expr_::Call(Box::new(aast::CallExpr {
            func: obj_get_exp,
            targs: vec![],
            args: vec![aast::Argument::Anormal(aast::Expr(
                (),
                pos,
                aast::Expr_::String("".into()),
            ))],
            unpacked_arg: None,
        })),
    )
}
