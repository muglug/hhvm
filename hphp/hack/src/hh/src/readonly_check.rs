// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `readonly_check.ml`. See `hh/PORTING.md`.
//!
//! - `check` is an object that inherits `Tast_visitor.iter`: [`Check`], a
//!   visitor with the methods of [`tast_visitor::iter_methods`].
//! - The handler keeps `fun_has_readonly` in a `ref` of the object, and the
//!   object is a value of the module: one for the process, which keeps its
//!   value from one definition (and one file) to the next. Here it is a
//!   thread-local ([`FUN_HAS_READONLY`]): one file is checked on one thread.
//! - `grab_class_elts_from_ty` is given an `Ast_defs.id` (from `Obj_get`) or a
//!   `pstring` (from `Class_get`), the same type in OCaml and two here; it
//!   reads only the name, which it is given.

use std::cell::Cell;

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::aast_visitor::Node;
use oxidized::aast_visitor::Visitor;
use oxidized::ast_defs;
use oxidized::ast_defs::PropOrMethod;
use oxidized::pos::Pos;

use crate::aast_utils;
use crate::decl_entry;
use crate::pos_or_decl;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::typing_defs::*;
use crate::typing_error;
use crate::typing_error::primary::readonly as ro;
use crate::typing_error_utils;
/// `module MakeType = Typing_make_type`
use crate::typing_make_type as make_type;
/// `module Reason = Typing_reason`
use crate::typing_reason as reason;
use crate::typing_set;
use crate::typing_subtype;
use crate::typing_utils;
use crate::utils;

/// `S_set.t`
type SSet = im::OrdSet<String>;

/// `SN.Classes.cString` (which `naming_special_names_rust::classes` does
/// not have).
const C_STRING: &str = "\\HH\\string";

/// Create a synthetic function type out of two fun_ty that has the correct readonlyness by being conservative
fn union_fty_readonly(fty1: FunType, fty2: FunType) -> FunType {
    let union_fp_readonly = |fp1: &FunParam, fp2: &FunParam| -> FunParam {
        match (get_fp_readonly(fp1), get_fp_readonly(fp2)) {
            (true, _) => fp2.clone(), // Must both be readonly to be readonly
            (false, _) => fp1.clone(),
        }
    };

    // Not readonly

    // Must both be readonly to be considered a readonly call
    let fty_readonly_this = get_ft_readonly_this(&fty1) && get_ft_readonly_this(&fty2);
    // If either are readonly, consider readonly return
    let fty_returns_readonly = get_ft_returns_readonly(&fty1) || get_ft_returns_readonly(&fty2);
    let fty = set_ft_readonly_this(fty1.clone(), fty_readonly_this);
    let fty = set_ft_returns_readonly(fty, fty_returns_readonly);
    // List.map2 fty1.ft_params fty2.ft_params ~f:union_fp_readonly
    let fps = if fty1.params.len() == fty2.params.len() {
        Some(
            fty1.params
                .iter()
                .zip(fty2.params.iter())
                .map(|(fp1, fp2)| union_fp_readonly(fp1, fp2))
                .collect::<Vec<_>>(),
        )
    } else {
        None
    };
    // If lenghts unequal we have other problems and errors, just return the first one
    let fps = match fps {
        None => fty1.params,
        Some(fp) => fp,
    };
    FunType { params: fps, ..fty }
}

/// (The function type is shared with the type, not copied.)
fn get_fty(env: &Env, ty: &Ty) -> Option<std::rc::Rc<FunType>> {
    let (_, ty) = tast_env::strip_supportdyn(env, ty.clone());
    match get_node(&ty) {
        Ty_::Tunion(tyl) => {
            // Filter out dynamic types
            let ftys: Vec<std::rc::Rc<FunType>> = tyl.iter().filter_map(|ty| get_fty(env, ty)).collect();
            // Because Typing_union already aggressively simplifies function unions to a single function type,
            // there should be a single function type here 99% of the time.
            let mut ftys = ftys.into_iter();
            match ftys.next() {
                // Not calling a function, ignore
                None => None,
                // In the rare case where union did not simplify, use readonly union to merge all fty's together with a union into a single function type, and return it.
                Some(fty1) => {
                    let rest = ftys;
                    let result = rest.fold(fty1, |fty1, fty2| {
                        std::rc::Rc::new(union_fty_readonly(
                            std::rc::Rc::unwrap_or_clone(fty1),
                            std::rc::Rc::unwrap_or_clone(fty2),
                        ))
                    });
                    Some(result)
                }
            }
        }
        _ => match tast_env::get_underlying_function_type(env, ty.clone()) {
            None => None,
            Some((_, ft)) => Some(ft),
        },
    }
}

/// `rty`
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Rty {
    Readonly,
    Mut,
}

/// Returns true if rty_sub is a subtype of rty_sup.
/// TODO: Later, we'll have to consider the regular type as well, for example
/// we could allow readonly int as equivalent to an int for devX purposes.
/// This would require TIC to handle correctly, though.
fn subtype_rty(rty_sub: Rty, rty_sup: Rty) -> bool {
    match (rty_sub, rty_sup) {
        (Rty::Readonly, Rty::Mut) => false,
        _ => true,
    }
}

fn param_to_rty(param: &FunParam) -> Rty {
    if get_fp_readonly(param) {
        Rty::Readonly
    } else {
        Rty::Mut
    }
}

/// (`prop_id` is `snd prop_id`.)
fn grab_class_elts_from_ty(
    static_: bool,
    seen: Option<SSet>,
    env: &Env,
    ty: &Ty,
    prop_id: &str,
) -> Vec<ClassElt> {
    let seen = seen.unwrap_or_default();
    // Given a list of types, find recurse on the first type that
    // has the property and return the result
    let find_first_in_list = |seen: &SSet, tyl: &[Ty]| -> Option<Vec<ClassElt>> {
        tyl.iter().find_map(|ty| {
            match grab_class_elts_from_ty(static_, Some(seen.clone()), env, ty, prop_id) {
                tyl if tyl.is_empty() => None,
                tyl => Some(tyl),
            }
        })
    };
    match get_node(ty) {
        Ty_::Tclass(id, _exact, _args) => {
            let class_decl = tast_env::get_class(env, &id.1);
            match class_decl {
                decl_entry::T::Found(class_decl) => {
                    let prop = if static_ {
                        tast_env::get_static_member(
                            /*is_method*/ false,
                            env,
                            &class_decl,
                            prop_id,
                        )
                    } else {
                        tast_env::get_prop(env, &class_decl, prop_id)
                    };
                    prop.into_iter().collect()
                }
                decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => vec![],
            }
        }
        // Accessing a property off of an intersection type
        // should involve exactly one kind of readonlyness, since for
        // the intersection type to exist, the property must be related
        // by some subtyping relationship anyways, and property readonlyness
        // is invariant. Thus we just grab the first one from the list where the prop exists.
        Ty_::Tintersection(tyl) if tyl.is_empty() => vec![],
        Ty_::Tintersection(tyl) => find_first_in_list(&seen, tyl).unwrap_or_default(),
        // A union type is more interesting, where we must return all possible cases
        // and be conservative in our use case.
        Ty_::Tunion(tyl) => tyl
            .iter()
            .flat_map(|ty| grab_class_elts_from_ty(static_, Some(seen.clone()), env, ty, prop_id))
            .collect(),
        // Generic types can be treated similarly to an intersection type
        // where we find the first prop that works from the upper bounds
        Ty_::Tgeneric(name) => {
            // Avoid circular generics with a set
            if seen.contains(name) {
                vec![]
            } else {
                let new_seen = seen.update(name.clone());
                let upper_bounds = tast_env::get_upper_bounds(env, name);
                find_first_in_list(&new_seen, &typing_set::elements(&upper_bounds))
                    .unwrap_or_default()
            }
        }
        Ty_::Tdependent(_, ty) => {
            // Dependent types have an upper bound that's a class or generic
            grab_class_elts_from_ty(static_, Some(seen), env, ty, prop_id)
        }
        Ty_::Toption(ty) => {
            // If it's nullable, take the
            grab_class_elts_from_ty(static_, Some(seen), env, ty, prop_id)
        }
        _ => vec![],
    }
}

/// Return a list of possible static prop elts given a class_get expression
fn get_static_prop_elts(env: &Env, class_id: &tast::ClassId, prop_id: &str) -> Vec<ClassElt> {
    let aast::ClassId(ty, _, _) = class_id;
    grab_class_elts_from_ty(true, None, env, ty, prop_id)
}

/// Return a list of possible prop elts given an obj get expression
fn get_prop_elts(env: &Env, obj: &tast::Expr, get: &tast::Expr) -> Vec<ClassElt> {
    let mut env = env.clone();
    let ty = tast_env::expand_type(&mut env, tast::get_type(obj).clone());
    match get {
        aast::Expr(_, _, aast::Expr_::Id(prop_id)) => {
            grab_class_elts_from_ty(false, None, &env, &ty, &prop_id.1)
        }
        // TODO: Handle more complex  cases
        _ => vec![],
    }
}

fn ty_expr(env: &Env, aast::Expr(_, _, expr_): &tast::Expr) -> Rty {
    match expr_ {
        aast::Expr_::ReadonlyExpr(_) => Rty::Readonly,
        // Obj_get, array_get, and class_get are here for better error messages when used as lval
        aast::Expr_::ObjGet(og) if matches!(og.3, PropOrMethod::IsProp) => {
            let (e1, e2, _, _) = &**og;
            match ty_expr(env, e1) {
                Rty::Readonly => Rty::Readonly,
                Rty::Mut => {
                    // In the mut case, we need to check if the property is marked readonly
                    let prop_elts = get_prop_elts(env, e1, e2);
                    let readonly_prop = prop_elts
                        .iter()
                        .find(|ce| get_ce_readonly_prop_or_needs_concrete(ce));
                    readonly_prop.map_or(Rty::Mut, |_| Rty::Readonly)
                }
            }
        }
        aast::Expr_::ClassGet(cg) if matches!(cg.2, PropOrMethod::IsProp) => {
            let (class_id, expr, _) = &**cg;
            // If any of the static props could be readonly, treat the expression as readonly
            let class_elts = get_static_prop_elts(env, class_id, &expr.1);
            // Note that the empty list case (when the prop doesn't exist) returns Mut
            if class_elts
                .iter()
                .any(get_ce_readonly_prop_or_needs_concrete)
            {
                Rty::Readonly
            } else {
                Rty::Mut
            }
        }
        aast::Expr_::ArrayGet(ag) => ty_expr(env, &ag.0),
        _ => Rty::Mut,
    }
}

fn is_value_collection_ty(env: &Env, ty: &Ty) -> bool {
    let mixed = make_type::mixed(reason::none());
    let ty = tast_env::strip_dynamic(env, ty.clone());
    let hackarray = make_type::any_array(reason::none(), mixed.clone(), mixed);
    // Subtype against an empty open shape (shape(...))
    let shape = make_type::open_shape(
        make_type::mixed(reason::none()),
        reason::none(),
        t_shape_map::T::new(),
    );
    typing_utils::is_sub_type(env, &ty, &hackarray) || typing_utils::is_sub_type(env, &ty, &shape)
}

/// Check if type is safe to convert from readonly to mut
/// TODO(readonly): Update to include more complex types.
///
/// (`TShapeMap.for_all` is applied to the fields in the order of their
/// names: `Map.for_all` applies it to the root of the tree first. The
/// predicate gives the same result in either order; only which dependencies
/// its subtyping checks record can differ.)
fn is_safe_mut_ty(env: &Env, seen: &SSet, ty: &Ty) -> bool {
    let mut env = env.clone();
    let ty = tast_env::expand_type(&mut env, ty.clone());
    // Strip dynamic from like types (~T = T | dynamic) so we check
    // the underlying type. Without this, ~(function(): void) would pass
    // because dynamic is not disjoint from primitives.
    let ty = tast_env::strip_dynamic(&env, ty);
    let env = &env;
    match get_node(&ty) {
        // Allow all primitive types
        Ty_::Tprim(_) => true,
        // Open shapes can technically have objects in them, but as long as the current fields don't have objects in them
        // we will allow you to call the function. Note that the function fails at runtime if any shape fields are objects.
        Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple { fields, .. })) => {
            fields.values().all(|v| is_safe_mut_ty(env, seen, &v.ty))
        }
        Ty_::Tshape(ShapeType::ShapeSplat(_)) => false,
        // Nullable types: check the inner type. ?vec<string> is safe, ?Foo is not.
        Ty_::Toption(ty_inner) => is_safe_mut_ty(env, seen, ty_inner),
        // For newtypes (including supportdyn<T>), check through the bound.
        // supportdyn<T> has bound T; newtype Foo as Bar has bound Bar.
        // This lets us see through opaque type aliases to the underlying type.
        Ty_::Tnewtype(_, _, bound) => is_safe_mut_ty(env, seen, bound),
        // If it's a Tclass it's an array type by is_value_collection
        Ty_::Tintersection(tyl) => tyl.iter().any(|l| is_safe_mut_ty(env, seen, l)),
        // Only error if there isn't a type that it could be that's primitive
        Ty_::Tunion(tyl) => tyl.iter().any(|ty| is_safe_mut_ty(env, seen, ty)),
        // See comment about open shapes
        Ty_::Ttuple(TupleType {
            required: t_required,
            optional: t_optional,
            extra: t_extra,
        }) => {
            t_required.iter().all(|ty| is_safe_mut_ty(env, seen, ty))
                && t_optional.iter().all(|ty| is_safe_mut_ty(env, seen, ty))
                && match t_extra {
                    TupleExtra::Tvariadic(_) => true,
                    TupleExtra::Tsplat(t_splat) => is_safe_mut_ty(env, seen, t_splat),
                }
        }
        Ty_::Tdependent(_, upper) => {
            // check upper bounds
            is_safe_mut_ty(env, seen, upper)
        }
        Ty_::Tclass((_, id), _, _) if C_STRING == id => true,
        Ty_::Tclass(_, _, tyl) if is_value_collection_ty(env, &ty) => {
            tyl.iter().all(|l| is_safe_mut_ty(env, seen, l))
        }
        Ty_::Tgeneric(name) => {
            // Avoid circular generics with a set
            if seen.contains(name) {
                false
            } else {
                let new_seen = seen.update(name.clone());
                let upper_bounds = tast_env::get_upper_bounds(env, name);
                typing_set::exists(|l| is_safe_mut_ty(env, &new_seen, l), &upper_bounds)
            }
        }
        _ => {
            // Otherwise, check if there's any primitive type it could be
            let primitive_types = vec![
                make_type::bool(reason::none()),
                make_type::int(reason::none()),
                make_type::arraykey(reason::none()),
                make_type::string(reason::none()),
                make_type::float(reason::none()),
                make_type::num(reason::none()),
                // Keysets only contain arraykeys so if they're readonly its safe to remove
                make_type::keyset(reason::none(), make_type::arraykey(reason::none())),
                // We don't put null here because we want to exclude ?Foo.
                // as_mut(null) itself is allowed by the Tprim above
            ];
            // Make sure that a primitive *could* be this type by intersecting all primitives and subtyping.
            let union = make_type::union(reason::none(), primitive_types);
            !typing_subtype::is_type_disjoint(env, &ty, &union)
        }
    }
}

/// Check that function calls which return readonly are wrapped in readonly
fn check_readonly_return_call(env: &Env, pos: &Pos, caller_ty: &Ty, is_readonly: bool) {
    if is_readonly {
    } else {
        match get_node(caller_ty) {
            Ty_::Tunion(tyl) => tyl
                .iter()
                .for_each(|ty| check_readonly_return_call(env, pos, ty, is_readonly)),
            _ => match get_fty(env, caller_ty) {
                Some(fty) if get_ft_returns_readonly(&fty) => typing_error_utils::add_typing_error(
                    &typing_error::readonly(ro::T::Explicit_readonly_cast {
                        pos: pos.clone(),
                        kind: ro::Kind::fn_call,
                        decl_pos: get_pos(caller_ty),
                    }),
                    env,
                ),
                _ => {}
            },
        }
    }
}

fn check_readonly_property(env: &Env, obj: &tast::Expr, get: &tast::Expr, obj_ro: Rty) {
    let prop_elts = get_prop_elts(env, obj, get);
    // If there's any property in the list of possible properties that could be readonly,
    // it must be explicitly cast to readonly
    let readonly_prop = prop_elts
        .iter()
        .find(|ce| get_ce_readonly_prop_or_needs_concrete(ce));
    match (readonly_prop, obj_ro) {
        (Some(elt), Rty::Mut) => typing_error_utils::add_typing_error(
            &typing_error::readonly(ro::T::Explicit_readonly_cast {
                pos: tast::get_position(get).clone(),
                kind: ro::Kind::property,
                decl_pos: (*elt.ce_pos).clone(),
            }),
            env,
        ),
        _ => {}
    }
}

fn check_static_readonly_property(
    pos: &Pos,
    env: &Env,
    class_: &tast::ClassId,
    get: &aast::Pstring,
    obj_ro: Rty,
) {
    let prop_elts = get_static_prop_elts(env, class_, &get.1);
    // If there's any property in the list of possible properties that could be readonly,
    // it must be explicitly cast to readonly
    let readonly_prop = prop_elts
        .iter()
        .find(|ce| get_ce_readonly_prop_or_needs_concrete(ce));
    match (readonly_prop, obj_ro) {
        (Some(elt), Rty::Mut) if get_ce_readonly_prop_or_needs_concrete(elt) => {
            typing_error_utils::add_typing_error(
                &typing_error::readonly(ro::T::Explicit_readonly_cast {
                    pos: pos.clone(),
                    kind: ro::Kind::static_property,
                    decl_pos: (*elt.ce_pos).clone(),
                }),
                env,
            )
        }
        _ => {}
    }
}

fn is_method_caller(caller: &tast::Expr) -> bool {
    match caller {
        aast::Expr(_, _, aast::Expr_::ReadonlyExpr(inner)) if matches!(&inner.2, aast::Expr_::ObjGet(og) if matches!(og.3, PropOrMethod::IsMethod)) => {
            true
        }
        aast::Expr(_, _, aast::Expr_::ObjGet(og)) if matches!(og.3, PropOrMethod::IsMethod) => true,
        _ => false,
    }
}

fn is_special_builtin(s: &str) -> bool {
    match s {
        // none of these functions require readonly checks, and can take in readonly values safely
        "HH\\dict" | "HH\\varray" | "HH\\darray" | "HH\\vec" | "HH\\keyset" | "hphp_array_idx" => {
            true
        }
        _ => false,
    }
}

fn assign(env: &Env, lval: &tast::Expr, rval: &tast::Expr) {
    // Check that we're assigning a readonly value to a readonly property
    let check_ro_prop_assignment = |prop_elts: Vec<ClassElt>| {
        let mutable_prop = prop_elts
            .iter()
            .find(|r| !get_ce_readonly_prop_or_needs_concrete(r));
        match mutable_prop {
            Some(elt) if !get_ce_readonly_prop_or_needs_concrete(elt) => {
                typing_error_utils::add_typing_error(
                    &typing_error::readonly(ro::T::Readonly_mismatch {
                        pos: tast::get_position(lval).clone(),
                        what: ro::What::prop_assign,
                        pos_sub: pos_or_decl::of_raw_pos(tast::get_position(rval).clone()),
                        pos_super: (*elt.ce_pos).clone(),
                    }),
                    env,
                )
            }
            _ => {}
        }
    };
    match lval {
        // List assignment
        aast::Expr(_, _, aast::Expr_::List(exprs)) => {
            exprs.iter().for_each(|lval| assign(env, lval, rval))
        }
        // Shape/tuple destructuring: propagate readonly from RHS to each target
        aast::Expr(_, _, aast::Expr_::DestructureShape(ds)) => ds
            .fields
            .iter()
            .for_each(|dsf| assign_destructure_target(env, &dsf.target, rval)),
        aast::Expr(_, _, aast::Expr_::DestructureTuple(dt)) => dt
            .entries
            .iter()
            .for_each(|dte| assign_destructure_target(env, &dte.target, rval)),
        aast::Expr(_, _, aast::Expr_::ArrayGet(ag)) => {
            let (array, _) = &**ag;
            // (ty_expr env array, ty_expr env rval): OCaml evaluates the
            // components of a tuple from right to left.
            let rval_rty = ty_expr(env, rval);
            let array_rty = ty_expr(env, array);
            match (array_rty, rval_rty) {
                (Rty::Readonly, _) if is_value_collection_ty(env, tast::get_type(array)) => {
                    // In the case of (expr)[0] = rvalue, where expr is a value collection like vec,
                    // we need to check assignment recursively because ($x->prop)[0] is only valid if $x is mutable and prop is readonly.
                    match array {
                        aast::Expr(_, _, aast::Expr_::ArrayGet(_))
                        | aast::Expr(_, _, aast::Expr_::ObjGet(_)) => assign(env, array, rval),
                        _ => {}
                    }
                }
                (Rty::Mut, Rty::Readonly) => typing_error_utils::add_typing_error(
                    &typing_error::readonly(ro::T::Readonly_mismatch {
                        pos: tast::get_position(lval).clone(),
                        what: ro::What::collection_mod,
                        pos_sub: pos_or_decl::of_raw_pos(tast::get_position(rval).clone()),
                        pos_super: pos_or_decl::of_raw_pos(tast::get_position(array).clone()),
                    }),
                    env,
                ),
                (Rty::Readonly, _) => typing_error_utils::add_typing_error(
                    &typing_error::readonly(ro::T::Readonly_modified {
                        pos: tast::get_position(array).clone(),
                        reason_opt: None,
                    }),
                    env,
                ),
                (Rty::Mut, Rty::Mut) => {}
            }
        }
        aast::Expr(_, _, aast::Expr_::ClassGet(cg)) if matches!(cg.2, PropOrMethod::IsProp) => {
            let (id, expr, _) = &**cg;
            match ty_expr(env, rval) {
                Rty::Readonly => {
                    let prop_elts = get_static_prop_elts(env, id, &expr.1);
                    check_ro_prop_assignment(prop_elts)
                }
                _ => {}
            }
        }
        aast::Expr(_, _, aast::Expr_::ObjGet(og)) if matches!(og.3, PropOrMethod::IsProp) => {
            let (obj, get, _, _) = &**og;
            // Here to check for nested property accesses that are accessing readonly values
            match ty_expr(env, obj) {
                Rty::Readonly => typing_error_utils::add_typing_error(
                    &typing_error::readonly(ro::T::Readonly_modified {
                        pos: tast::get_position(obj).clone(),
                        reason_opt: None,
                    }),
                    env,
                ),
                Rty::Mut => {}
            };
            match ty_expr(env, rval) {
                Rty::Readonly => {
                    let prop_elts = get_prop_elts(env, obj, get);
                    // If there's a mutable prop, then there's a chance we're assigning to one
                    check_ro_prop_assignment(prop_elts)
                }
                _ => {}
            }
        }
        // TODO: make this exhaustive
        _ => {}
    }
}

fn assign_destructure_target(env: &Env, target: &tast::DestructureTarget, rval: &tast::Expr) {
    let aast::DestructureTarget(_, _, target_) = target;
    match target_ {
        aast::DestructureTarget_::DtLvar(_) | aast::DestructureTarget_::DtWildcard(_) => {}
        aast::DestructureTarget_::DtShape(ds) => ds
            .fields
            .iter()
            .for_each(|dsf| assign_destructure_target(env, &dsf.target, rval)),
        aast::DestructureTarget_::DtTuple(dt) => dt
            .entries
            .iter()
            .for_each(|dte| assign_destructure_target(env, &dte.target, rval)),
    }
}

/// Method call invocation
fn method_call(env: &Env, caller: &tast::Expr) {
    match caller {
        // Readonly call checks
        aast::Expr(ty, _, aast::Expr_::ReadonlyExpr(inner)) if matches!(&inner.2, aast::Expr_::ObjGet(og) if matches!(og.3, PropOrMethod::IsMethod)) =>
        {
            let aast::Expr_::ObjGet(og) = &inner.2 else {
                unreachable!()
            };
            let e1 = &og.0;
            match get_fty(env, ty) {
                Some(fty) if !get_ft_readonly_this(&fty) => typing_error_utils::add_typing_error(
                    &typing_error::readonly(ro::T::Readonly_method_call {
                        pos: tast::get_position(e1).clone(),
                        decl_pos: get_pos(ty),
                    }),
                    env,
                ),
                _ => {}
            }
        }
        _ => {}
    }
}

fn check_special_function(env: &Env, caller: &tast::Expr, args: &[tast::Argument]) {
    match (caller, args) {
        (aast::Expr(_, _, aast::Expr_::Id(id)), [arg])
            if utils::strip_ns(&id.1) == utils::strip_ns(sn::readonly::AS_MUT) =>
        {
            let pos = &id.0;
            let arg = aast_utils::arg_to_expr(arg);
            let arg_ty = tast::get_type(arg);
            if !is_safe_mut_ty(env, &SSet::new(), arg_ty) {
                typing_error_utils::add_typing_error(
                    &typing_error::readonly(ro::T::Readonly_invalid_as_mut(pos.clone())),
                    env,
                )
            } else {
            }
        }
        _ => {}
    }
}

/// Checks related to calling a function or method
/// is_readonly is true when the call is allowed to return readonly
fn call(
    is_readonly: bool,
    method_call: bool,
    env: &Env,
    pos: &Pos,
    caller_ty: &Ty,
    caller_rty: Rty,
    args: &[tast::Argument],
    unpacked_arg: Option<&tast::Expr>,
) {
    let mut env = env.clone();
    let caller_ty = tast_env::expand_type(&mut env, caller_ty.clone());
    let env = &env;
    let check_readonly_closure =
        |caller_ty: &Ty, caller_rty: Rty| match (get_fty(env, caller_ty), caller_rty) {
            (Some(fty), Rty::Readonly) if (!get_ft_readonly_this(&fty)) && !method_call => {
                // Get the position of why this function is its current type (usually a typehint)
                let reason = get_reason(caller_ty);
                let f_pos = reason::to_pos(get_reason(caller_ty));
                let suggestion =
                // If we got this function from a typehint, we suggest marking the function (readonly function)
                if reason::predicates::is_hint(reason) {
                    let fty = crate::typing_defs_core::set_ft_readonly_this(std::rc::Rc::unwrap_or_clone(fty), true);
                    let suggested_fty = mk((reason.clone(), Ty_::Tfun(std::rc::Rc::new(fty))));
                    let suggested_fty_str = tast_env::print_ty(env, &suggested_fty);
                    format!("annotate this typehint as a {}", suggested_fty_str)
                }
                // Otherwise, it's likely from a Rwitness, but we suggest declaring it as readonly
                else {
                    "declare this as a `readonly` function".to_string()
                };
                typing_error_utils::add_typing_error(
                    &typing_error::readonly(ro::T::Readonly_closure_call {
                        pos: pos.clone(),
                        decl_pos: f_pos,
                        suggestion,
                    }),
                    env,
                )
            }
            _ => {}
        };
    // Checks a single arg against a parameter
    let check_arg = |env: &Env, param: &FunParam, arg: &tast::Argument| {
        let arg = aast_utils::arg_to_expr(arg);
        let param_rty = param_to_rty(param);
        let arg_rty = ty_expr(env, arg);
        if !subtype_rty(arg_rty, param_rty) {
            typing_error_utils::add_typing_error(
                &typing_error::readonly(ro::T::Readonly_mismatch {
                    pos: tast::get_position(arg).clone(),
                    what: match arg_rty {
                        Rty::Readonly => ro::What::arg_readonly,
                        Rty::Mut => ro::What::arg_mut,
                    },
                    pos_sub: pos_or_decl::of_raw_pos(tast::get_position(arg).clone()),
                    pos_super: param.pos.clone(),
                }),
                env,
            )
        }
    };

    // Check that readonly arguments match their parameters
    let check_args =
        |env: &Env, caller_ty: &Ty, args: &[tast::Argument], unpacked_arg: Option<&tast::Expr>| {
            match get_fty(env, caller_ty) {
                Some(fty) => {
                    let named_variadic_param = ft_named_variadic_param(&fty);
                    let params: &[FunParam] = match named_variadic_param {
                        // List.drop_last_exn
                        Some(_) => &fty.params[..fty.params.len() - 1],
                        None => &fty.params,
                    };
                    // List.fold_right params ~init:([], S_map.empty) ~f:(fun fp
                    // (positional, named) -> ...): from the last parameter to the
                    // first, so the first of two parameters with the same name is
                    // the one that stays.
                    let (positional_params, named_params) = {
                        let mut positional: Vec<&FunParam> = vec![];
                        let mut named: im::OrdMap<String, &FunParam> = im::OrdMap::new();
                        for fp in params.iter().rev() {
                            match named_params::name_of_named_param(fp) {
                                Some(name) => {
                                    named.insert(name, fp);
                                }
                                None => positional.push(fp),
                            }
                        }
                        positional.reverse();
                        (positional, named)
                    };
                    let check_arg_and_remaining_positional_params =
                        |positional_remaining: Vec<_>, arg: &tast::Argument| -> Vec<_> {
                            match arg {
                                aast::Argument::Anamed(ast_defs::Id(_, name), _) => {
                                    let param = match named_params.get(name) {
                                        Some(param) => Some(*param),
                                        None => named_variadic_param,
                                    };
                                    if let Some(param) = param {
                                        check_arg(env, param, arg)
                                    }
                                    positional_remaining
                                }
                                aast::Argument::Anormal(_) | aast::Argument::Ainout(_, _) => {
                                    match positional_remaining.as_slice() {
                                        [param] if get_ft_variadic(&fty) => {
                                            check_arg(env, *param, arg);
                                            positional_remaining
                                        }
                                        [param, remaining @ ..] => {
                                            check_arg(env, *param, arg);
                                            remaining.to_vec()
                                        }
                                        [] => {
                                            // Too many positional arguments: already reported during typing.
                                            vec![]
                                        }
                                    }
                                }
                            }
                        };
                    let positional_remaining =
                        args.iter()
                            .fold(positional_params, |positional_remaining, arg| {
                                check_arg_and_remaining_positional_params(positional_remaining, arg)
                            });
                    if let Some(arg) = unpacked_arg {
                        let _: Vec<&FunParam> = check_arg_and_remaining_positional_params(
                            positional_remaining,
                            &aast::Argument::Anormal(arg.clone()),
                        );
                    }
                }
                None => {}
            }
        };
    check_readonly_closure(&caller_ty, caller_rty);
    check_readonly_return_call(env, pos, &caller_ty, is_readonly);
    check_args(env, &caller_ty, args, unpacked_arg)
}

fn caller_is_special_builtin(caller: &tast::Expr) -> bool {
    match caller {
        aast::Expr(_, _, aast::Expr_::Id(id)) if is_special_builtin(utils::strip_ns(&id.1)) => true,
        _ => false,
    }
}

/// The class of the object `check` (which inherits `Tast_visitor.iter`).
struct Check;

/// `let check = object (self) inherit Tast_visitor.iter as super ... end`
fn check() -> Check {
    Check
}

type Res = Result<(), ()>;

impl<'a> Visitor<'a> for Check {
    type Params = tast_visitor::IterParams;

    fn object(&mut self) -> &mut dyn Visitor<'a, Params = Self::Params> {
        self
    }

    tast_visitor::iter_methods!('a);

    fn visit_expr(&mut self, env: &mut Env, e: &'a tast::Expr) -> Res {
        match &e.2 {
            aast::Expr_::Assign(a) => {
                let (lhs, _, rhs) = &**a;
                assign(env, lhs, rhs);
                self.visit_expr(env, rhs)
            }
            aast::Expr_::ReadonlyExpr(inner) if matches!(&inner.2, aast::Expr_::Call(_)) => {
                let aast::Expr_::Call(call_expr) = &inner.2 else {
                    unreachable!()
                };
                let aast::CallExpr {
                    func,
                    args,
                    unpacked_arg,
                    ..
                } = &**call_expr;
                // let default () =
                //   (* Skip the recursive step into ReadonlyExpr to avoid erroring *)
                //   self#on_Call env call_expr
                //
                // (`if ... then default () else call ...; check_special_function
                // ...; method_call ...; default ()`: the `if` ends at the first
                // `;`, so a special builtin is visited twice, as in OCaml.)
                if caller_is_special_builtin(func) {
                    self.visit_call_expr(env, call_expr)?
                } else {
                    call(
                        true,
                        is_method_caller(func),
                        env,
                        tast::get_position(func),
                        tast::get_type(func),
                        ty_expr(env, func),
                        args,
                        unpacked_arg.as_ref(),
                    )
                };
                check_special_function(env, func, args);
                method_call(env, func);
                self.visit_call_expr(env, call_expr)
            }
            // Non readonly calls
            aast::Expr_::Call(c) => {
                let aast::CallExpr {
                    func,
                    args,
                    unpacked_arg,
                    ..
                } = &**c;
                // (As above, a special builtin is visited twice.)
                if caller_is_special_builtin(func) {
                    e.recurse(env, self)?
                } else {
                    call(
                        false,
                        is_method_caller(func),
                        env,
                        tast::get_position(func),
                        tast::get_type(func),
                        ty_expr(env, func),
                        args,
                        unpacked_arg.as_ref(),
                    )
                };
                check_special_function(env, func, args);
                method_call(env, func);
                e.recurse(env, self)
            }
            aast::Expr_::ReadonlyExpr(inner) if matches!(&inner.2, aast::Expr_::ObjGet(_)) => {
                let aast::Expr_::ObjGet(og) = &inner.2 else {
                    unreachable!()
                };
                let (obj, get, nullable, is_prop_call) = &**og;
                // Skip the recursive step into ReadonlyExpr to avoid erroring
                // (self#on_Obj_get env obj get nullable is_prop_call)
                obj.accept(env, self)?;
                get.accept(env, self)?;
                nullable.accept(env, self)?;
                is_prop_call.accept(env, self)
            }
            aast::Expr_::ReadonlyExpr(inner) if matches!(&inner.2, aast::Expr_::ClassGet(_)) => {
                let aast::Expr_::ClassGet(cg) = &inner.2 else {
                    unreachable!()
                };
                let (class_, get, x) = &**cg;
                // Skip the recursive step into ReadonlyExpr to avoid erroring
                // (self#on_Class_get env class_ get x)
                class_.accept(env, self)?;
                get.accept(env, self)?;
                x.accept(env, self)
            }
            aast::Expr_::ObjGet(og) if matches!(og.3, PropOrMethod::IsProp) => {
                let (obj, get, _nullable, _) = &**og;
                check_readonly_property(env, obj, get, Rty::Mut);
                e.recurse(env, self)
            }
            aast::Expr_::ClassGet(cg) if matches!(cg.2, PropOrMethod::IsProp) => {
                let pos = &e.1;
                let (class_, get, _) = &**cg;
                check_static_readonly_property(pos, env, class_, get, Rty::Mut);
                e.recurse(env, self)
            }
            aast::Expr_::New(n) => {
                let pos = &e.1;
                let (_, _, args, unpacked_arg, constructor_fty) = &**n;
                // Constructors never return readonly, so that specific check is irrelevant
                call(
                    false,
                    false,
                    env,
                    pos,
                    constructor_fty,
                    Rty::Mut,
                    args,
                    unpacked_arg.as_ref(),
                );
                e.recurse(env, self)
            }
            aast::Expr_::ObjGet(_)
            | aast::Expr_::ClassGet(_)
            | aast::Expr_::This
            | aast::Expr_::ValCollection(_)
            | aast::Expr_::KeyValCollection(_)
            | aast::Expr_::Lvar(_)
            | aast::Expr_::Clone(_)
            | aast::Expr_::ArrayGet(_)
            | aast::Expr_::Yield(_)
            | aast::Expr_::Await(_)
            | aast::Expr_::Delay(_)
            | aast::Expr_::Tuple(_)
            | aast::Expr_::List(_)
            | aast::Expr_::Cast(_)
            | aast::Expr_::Unop(_)
            | aast::Expr_::Pipe(_)
            | aast::Expr_::Eif(_)
            | aast::Expr_::Is(_)
            | aast::Expr_::As(_)
            | aast::Expr_::Upcast(_)
            | aast::Expr_::Import(_)
            | aast::Expr_::Lplaceholder(_)
            | aast::Expr_::Pair(_)
            | aast::Expr_::ReadonlyExpr(_)
            | aast::Expr_::Binop(_)
            | aast::Expr_::ExpressionTree(_)
            | aast::Expr_::Xml(_)
            | aast::Expr_::Efun(_)
            // Neither this nor any of the *_id expressions call the function
            | aast::Expr_::MethodCaller(_)
            | aast::Expr_::FunctionPointer(_)
            | aast::Expr_::Lfun(_)
            | aast::Expr_::Null
            | aast::Expr_::True
            | aast::Expr_::False
            | aast::Expr_::Omitted
            | aast::Expr_::Id(_)
            | aast::Expr_::Shape(_)
            | aast::Expr_::EnumClassLabel(_)
            | aast::Expr_::ETSplice(_)
            | aast::Expr_::Int(_)
            | aast::Expr_::Dollardollar(_)
            | aast::Expr_::String(_)
            | aast::Expr_::String2(_)
            | aast::Expr_::Collection(_)
            | aast::Expr_::ClassConst(_)
            | aast::Expr_::Float(_)
            | aast::Expr_::PrefixedString(_)
            | aast::Expr_::Hole(_)
            | aast::Expr_::Nameof(_)
            | aast::Expr_::Package(_)
            | aast::Expr_::DestructureShape(_)
            | aast::Expr_::DestructureTuple(_) => e.recurse(env, self),
            // Stop at invalid marker
            aast::Expr_::Invalid(_) => Ok(()),
        }
    }
}

thread_local! {
    /// The `fun_has_readonly` ref of the handler object.
    /// Ref updated before every function def
    static FUN_HAS_READONLY: Cell<bool> = const { Cell::new(false) };
}

/// `let handler = object inherit Tast_visitor.handler_base ... end`
struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_method_(&mut self, env: &Env, m: &'a tast::Method_) {
        let mut env = env.clone();
        tast_env::restore_method_env(&mut env, m);
        if tast_env::fun_has_readonly(&env) {
            FUN_HAS_READONLY.set(true);
            let _ = check().visit_method_(&mut env, m);
        } else {
            FUN_HAS_READONLY.set(false);
        }
    }

    fn at_fun_def(&mut self, env: &Env, f: &'a tast::FunDef) {
        let mut env = env.clone();
        tast_env::restore_fun_env(&mut env, &f.fun);
        if tast_env::fun_has_readonly(&env) {
            FUN_HAS_READONLY.set(true);
            let _ = check().visit_fun_def(&mut env, f);
        } else {
            FUN_HAS_READONLY.set(false);
        }
    }

    // The following error checks are ones that need to run even if
    // readonly analysis is not enabled by the file attribute.
    fn at_Call(&mut self, env: &Env, call_expr: &'a tast::CallExpr) {
        let aast::CallExpr { func, .. } = call_expr;
        // this check is already handled by the readonly analysis,
        // which handles cases when there's a readonly keyword
        if FUN_HAS_READONLY.get() {
        } else {
            let caller_pos = tast::get_position(func);
            let caller_ty = tast::get_type(func);
            let caller_ty = tast_env::expand_type(&mut env.clone(), caller_ty.clone());
            check_readonly_return_call(env, caller_pos, &caller_ty, false)
        }
    }

    fn at_expr(&mut self, env: &Env, e: &'a tast::Expr) {
        // this check is already handled by the readonly analysis,
        // which handles cases when there's a readonly keyword
        let fun_has_readonly = FUN_HAS_READONLY.get();
        let check = |e: &tast::Expr| {
            if fun_has_readonly {
            } else {
                let val_kind = tast_env::get_val_kind(env);
                match (e, val_kind) {
                    (aast::Expr(_, _, aast::Expr_::Assign(a)), _) => {
                        let (lhs, _, rhs) = &**a;
                        // Check property assignments to make sure they're safe
                        assign(env, lhs, rhs)
                    }
                    // Assume obj is mutable here since you can't have a readonly thing
                    // without readonly keyword/analysis
                    // Only check this for rvalues, not lvalues
                    (aast::Expr(_, _, aast::Expr_::ObjGet(og)), ValKind::Other)
                        if matches!(og.3, PropOrMethod::IsProp) =>
                    {
                        let (obj, get, _, _) = &**og;
                        check_readonly_property(env, obj, get, Rty::Mut)
                    }
                    (aast::Expr(_, pos, aast::Expr_::ClassGet(cg)), ValKind::Other)
                        if matches!(cg.2, PropOrMethod::IsProp) =>
                    {
                        let (class_id, get, _) = &**cg;
                        check_static_readonly_property(pos, env, class_id, get, Rty::Mut)
                    }
                    _ => {}
                }
            }
        };
        match e {
            aast::Expr(_, _, aast::Expr_::Invalid(_)) => {}
            _ => check(e),
        }
    }
}

/// `val handler : Tast_visitor.handler`
pub fn handler() -> Box<dyn for<'a> tast_visitor::Handler<'a>> {
    Box::new(Handler)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn subtype_rty_only_rejects_readonly_into_mut() {
        assert!(!subtype_rty(Rty::Readonly, Rty::Mut));
        assert!(subtype_rty(Rty::Mut, Rty::Readonly));
        assert!(subtype_rty(Rty::Readonly, Rty::Readonly));
        assert!(subtype_rty(Rty::Mut, Rty::Mut));
    }

    #[test]
    fn special_builtins() {
        for name in [
            "HH\\dict",
            "HH\\varray",
            "HH\\darray",
            "HH\\vec",
            "HH\\keyset",
            "hphp_array_idx",
        ] {
            assert!(is_special_builtin(name));
        }
        assert!(!is_special_builtin("\\HH\\vec"));
        assert!(!is_special_builtin("HH\\idx"));
    }
}
