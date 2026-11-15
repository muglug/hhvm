// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `decl/decl_utils.ml`. See `hh/PORTING.md`.

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::ast_defs;
use oxidized::file_info::Names;
use oxidized::pos::Pos;
use oxidized::s_set::SSet;
use oxidized::typing_defs_core::ConsistentKind;
use pos::BPos;
use pos::Positioned;
use pos::TypeName;
use ty::decl::ShallowClass;
use ty::decl::Ty;
use ty::decl::Ty_;
use ty::decl::UserAttribute;
use ty::reason::Reason;
use ty::reason::ReasonImpl;

use crate::ctx::R;

/// `Typing_reason.to_pos`, for the reason of a decl type.
///
/// Not `ty::reason::Reason::pos`: for the reason of an instantiated generic
/// (`Instantiate { type_; var_name; var }`) hackrs gives the position of
/// `var`, the OCaml that of `type_` ("report the type application rather than
/// the definition").
pub(crate) fn reason_to_pos(r: &R) -> BPos {
    match r.as_impl() {
        ReasonImpl::NoReason => BPos::none(),
        ReasonImpl::FromWitnessDecl(_) => r.pos().clone(),
        ReasonImpl::Instantiate(type_, _, _) => reason_to_pos(type_),
    }
}

/// `Typing_defs.get_pos`, for a decl type (see `reason_to_pos`).
pub(crate) fn get_pos(ty: &Ty<R>) -> BPos {
    reason_to_pos(ty.reason())
}

/// `Typing_defs.Attributes.mem`, on the user attributes of a declaration.
pub(crate) fn attributes_mem(x: &str, xs: &[UserAttribute<BPos>]) -> bool {
    xs.iter().any(|ua| x == ua.name.id_ref().as_str())
}

pub fn unwrap_class_hint(
    hint: &aast::Hint,
) -> (
    (Pos, String, Vec<aast::Hint>),
    Option<crate::typing_error::T>,
) {
    let aast::Hint(p, hint_) = hint;
    match &**hint_ {
        aast::Hint_::Happly(ast_defs::Id(pos, class_name), type_parameters) => (
            (pos.clone(), class_name.clone(), type_parameters.clone()),
            None,
        ),
        aast::Hint_::Habstr(_) => {
            let err =
                crate::typing_error::primary(crate::typing_error::primary::T::ExpectedClass {
                    suffix: Some(" or interface but got a generic".to_string().into()),
                    pos: p.clone(),
                });
            ((Pos::NONE, String::new(), vec![]), Some(err))
        }
        _ => {
            let err =
                crate::typing_error::primary(crate::typing_error::primary::T::ExpectedClass {
                    suffix: Some(" or interface".to_string().into()),
                    pos: p.clone(),
                });
            ((Pos::NONE, String::new(), vec![]), Some(err))
        }
    }
}

pub fn unwrap_class_type(ty: &Ty<R>) -> (R, Positioned<TypeName, BPos>, Vec<Ty<R>>) {
    let r = ty.reason().clone();
    match ty.node_ref() {
        Ty_::Tapply(id_and_args) => {
            let (name, tparaml) = &**id_and_args;
            (r, name.clone(), tparaml.to_vec())
        }
        Ty_::Tgeneric(_) => {
            let p = reason_to_pos(&r);
            (r, Positioned::new(p, TypeName::new("")), vec![])
        }
        _ => {
            let p = reason_to_pos(&r);
            (r, Positioned::new(p, TypeName::new("")), vec![])
        }
    }
}

/// The names of all the parentish things of a shallow class
/// from `extends`, `implements`, `uses`, `require extends`, `require implements`,
/// and XHP attribute uses.
pub fn parentish_names(sc: &ShallowClass<R>) -> im::OrdSet<String> {
    let ShallowClass {
        mode: _,
        is_final: _,
        is_abstract: _,
        is_xhp: _,
        is_internal: _,
        has_xhp_keyword: _,
        kind: _,
        module: _,
        name: _,
        tparams: _,
        extends: sc_extends,
        uses: sc_uses,
        xhp_attr_uses: sc_xhp_attr_uses,
        xhp_enum_values: _,
        xhp_marked_empty: _,
        req_extends: sc_req_extends,
        req_implements: sc_req_implements,
        req_constraints: _,
        implements: sc_implements,
        support_dynamic_type: _,
        consts: _,
        typeconsts: _,
        props: _,
        static_props: _,
        constructor: _,
        static_methods: _,
        methods: _,
        user_attributes: _,
        enum_type: _,
        docs_url: _,
        package: _,
    } = sc;
    let get_names = |tys: &[Ty<R>], acc: im::OrdSet<String>| {
        tys.iter().fold(acc, |mut acc, ty| {
            let (_, name, _) = unwrap_class_type(ty);
            acc.insert(name.id_ref().as_str().to_string());
            acc
        })
    };
    let acc = crate::im_empty::ord_set();
    let acc = get_names(sc_extends, acc);
    let acc = get_names(sc_implements, acc);
    let acc = get_names(sc_uses, acc);
    let acc = get_names(sc_req_extends, acc);
    let acc = get_names(sc_req_implements, acc);
    get_names(sc_xhp_attr_uses, acc)
}

/// Given sets A and B return a tuple (AnB, A\B), i.e split A into the part
/// that is common with B, and which is unique to A
fn split_sets(defs: &SSet, split_if_in_defs: &SSet) -> (SSet, SSet) {
    defs.iter()
        .cloned()
        .partition(|x| split_if_in_defs.contains(x))
}

/// Given name sets A and B return a tuple (AnB, A\B), i.e split A into the part
/// that is common with B, and which is unique to A
pub fn split_defs(defs: &Names, split_if_in_defs: &Names) -> (Names, Names) {
    let (n_funs1, n_funs2) = split_sets(&defs.funs, &split_if_in_defs.funs);
    let (n_classes1, n_classes2) = split_sets(&defs.classes, &split_if_in_defs.classes);
    let (n_types1, n_types2) = split_sets(&defs.types, &split_if_in_defs.types);
    let (n_consts1, n_consts2) = split_sets(&defs.consts, &split_if_in_defs.consts);
    let (n_modules1, n_modules2) = split_sets(&defs.modules, &split_if_in_defs.modules);
    let r1 = Names {
        funs: n_funs1,
        classes: n_classes1,
        types: n_types1,
        consts: n_consts1,
        modules: n_modules1,
    };
    let r2 = Names {
        funs: n_funs2,
        classes: n_classes2,
        types: n_types2,
        consts: n_consts2,
        modules: n_modules2,
    };
    (r1, r2)
}

pub fn is_literal_with_trivially_inferable_type<Ex, En>(e: &aast::Expr<Ex, En>) -> bool {
    let aast::Expr(_, _, expr_) = e;
    match expr_ {
        aast::Expr_::String(_)
        | aast::Expr_::True
        | aast::Expr_::False
        | aast::Expr_::Int(_)
        | aast::Expr_::Float(_)
        | aast::Expr_::Null => true,
        aast::Expr_::Unop(unop) => match &**unop {
            (
                ast_defs::Uop::Uminus | ast_defs::Uop::Uplus,
                aast::Expr(_, _, aast::Expr_::Int(_) | aast::Expr_::Float(_)),
            ) => true,
            _ => false,
        },
        _ => {
            // We can't infer the type of everything here. Notably, if you
            // define a const in terms of another const, we need an annotation,
            // since the other const may not have been declared yet.
            //
            // Also note that a number of expressions are considered invalid
            // as constant initializers, even if we can infer their type; see
            // Naming.check_constant_expr.
            false
        }
    }
}

pub fn coalesce_consistent(parent: ConsistentKind, current: ConsistentKind) -> ConsistentKind {
    // If the parent's constructor is consistent via <<__ConsistentConstruct>>, then
    // we want to carry this forward even if the child is final. Example:
    //
    // <<__ConsistentConstruct>>
    // class C {
    //   public static function f(): void {
    //     new static();
    //   }
    // }
    // final class D<reify T> extends C {}
    //
    // Even though D's consistency locally comes from the fact that D was
    // declared as a final class, calling [new static()] via [D::f] will cause
    // a runtime exception because D has reified generics.
    match parent {
        ConsistentKind::Inconsistent => current,
        ConsistentKind::ConsistentConstruct => parent,
        // This case is unreachable in a correct program, because parent would have to
        // be a final class
        ConsistentKind::FinalClass => parent,
    }
}

pub fn consistent_construct_kind(cls: &ShallowClass<R>) -> ConsistentKind {
    if cls.is_final {
        ConsistentKind::FinalClass
    } else {
        let consistent_attr_present = attributes_mem(
            sn::user_attributes::CONSISTENT_CONSTRUCT,
            &cls.user_attributes,
        );
        if consistent_attr_present {
            ConsistentKind::ConsistentConstruct
        } else {
            ConsistentKind::Inconsistent
        }
    }
}

#[cfg(test)]
mod tests {
    use ty::decl::Prim;

    use super::*;

    #[test]
    fn unwrap_class_type_of_a_class_and_of_something_else() {
        let name = Positioned::new(BPos::none(), TypeName::new("\\C"));
        let int = Ty::prim(R::none(), Prim::Tint);
        let ty = Ty::apply(R::none(), name.clone(), Box::new([int.clone()]));
        let (_, id, args) = unwrap_class_type(&ty);
        assert_eq!(id, name);
        assert_eq!(args, vec![int.clone()]);
        let (_, id, args) = unwrap_class_type(&int);
        assert_eq!(id.id_ref().as_str(), "");
        assert!(args.is_empty());
        let (_, id, args) = unwrap_class_type(&Ty::generic(R::none(), TypeName::new("T")));
        assert_eq!(id.id_ref().as_str(), "");
        assert!(args.is_empty());
    }

    #[test]
    fn position_of_an_instantiated_generic_is_that_of_the_type_application() {
        use oxidized::file_pos_large::FilePosLarge;
        use pos::Prefix;
        use pos::RelativePath;
        let file = RelativePath::new(Prefix::Root, "a.php");
        let pos = |line: usize| {
            BPos::new(
                file,
                FilePosLarge::from_lnum_bol_offset(line, 0, 0),
                FilePosLarge::from_lnum_bol_offset(line, 0, 3),
            )
        };
        let type_ = R::hint(pos(1));
        let var = R::witness_from_decl(pos(2));
        let r = R::instantiate(type_, TypeName::new("T"), var);
        assert_eq!(reason_to_pos(&r), pos(1));
        assert!(reason_to_pos(&R::none()).is_none());
    }

    #[test]
    fn coalesce() {
        use ConsistentKind::*;
        assert_eq!(coalesce_consistent(Inconsistent, FinalClass), FinalClass);
        assert_eq!(
            coalesce_consistent(ConsistentConstruct, FinalClass),
            ConsistentConstruct
        );
        assert_eq!(coalesce_consistent(FinalClass, Inconsistent), FinalClass);
    }

    #[test]
    fn split() {
        let names = |funs: &[&str]| Names {
            funs: funs.iter().map(|s| s.to_string()).collect(),
            classes: Default::default(),
            types: Default::default(),
            consts: Default::default(),
            modules: Default::default(),
        };
        let (common, unique) = split_defs(&names(&["a", "b", "c"]), &names(&["b", "d"]));
        assert_eq!(common.funs, names(&["b"]).funs);
        assert_eq!(unique.funs, names(&["a", "c"]).funs);
    }

    #[test]
    fn trivially_inferable_literals() {
        use oxidized::aast::Expr;
        use oxidized::aast::Expr_;
        let e = |e: Expr_<(), ()>| Expr((), Pos::NONE, e);
        assert!(is_literal_with_trivially_inferable_type(&e(Expr_::Int(
            "1".into()
        ))));
        assert!(is_literal_with_trivially_inferable_type(&e(Expr_::Null)));
        assert!(is_literal_with_trivially_inferable_type(&e(Expr_::Unop(
            Box::new((ast_defs::Uop::Uminus, e(Expr_::Float("1.0".into()))))
        ))));
        assert!(!is_literal_with_trivially_inferable_type(&e(Expr_::Unop(
            Box::new((ast_defs::Uop::Unot, e(Expr_::Int("1".into()))))
        ))));
        assert!(!is_literal_with_trivially_inferable_type(&e(Expr_::Unop(
            Box::new((ast_defs::Uop::Uminus, e(Expr_::Null)))
        ))));
    }
}
