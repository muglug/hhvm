// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

use nast::Class_;
use nast::ClassHint;
use nast::ClassReq;
use nast::ClassVar;
use nast::ClassishKind;
use nast::Expr_;
use nast::Hint;
use nast::Hint_;
use nast::RequireKind;
use nast::ShapeFieldInfo;
use nast::Targ;
use nast::Tparam;
use nast::TraitHint;
use nast::TypeHint;
use nast::Variance;
use nast::XhpAttr;
use nast::XhpAttrHint;

use crate::prelude::*;

/// Port of `Naming_elab_this_hint` (the fields are those of
/// `Naming_phase_env.Elab_this_hint`).
#[derive(Copy, Clone, Default)]
pub struct ElabHintThisPass {
    /// `this` is forbidden as a hint in this context
    forbid_this: bool,
    lsb: Option<bool>,
    in_interface: bool,
    in_req_extends: bool,
    in_extends: bool,
    is_top_level_haccess_root: bool,
    in_invariant_final: bool,
}

impl ElabHintThisPass {
    fn reset(&mut self) {
        self.forbid_this = false;
        self.lsb = None;
    }
}

impl Pass for ElabHintThisPass {
    // We want to disallow `this` hints in:
    // - _class_ and _abstract class_ type parameters
    // - non-late static bound class_var
    // - `extends` and `require extends` clauses _unless_ it appears as the
    //   top-level root of a type access
    fn on_ty_hint_top_down(&mut self, env: &Env, elem: &mut Hint) -> ControlFlow<()> {
        let forbid_in_extends = (self.in_req_extends || self.in_extends)
            && !self.in_interface
            && !self.is_top_level_haccess_root
            && !self.in_invariant_final;
        let Hint(pos, box hint_) = elem;
        match &hint_ {
            Hint_::Hthis if self.forbid_this || forbid_in_extends => {
                env.emit_error(NamingError::ThisTypeForbidden {
                    pos: pos.clone(),
                    in_extends: self.in_extends,
                    in_req_extends: self.in_req_extends,
                });
            }
            Hint_::Haccess(..) => self.is_top_level_haccess_root = true,
            _ => self.is_top_level_haccess_root = false,
        }
        Continue(())
    }

    fn on_ty_class__top_down(&mut self, _: &Env, elem: &mut Class_) -> ControlFlow<()> {
        self.in_interface = matches!(elem.kind, ClassishKind::Cinterface);
        self.in_invariant_final = elem.final_
            && elem
                .tparams
                .iter()
                .all(|tp| matches!(tp.variance, Variance::Invariant));
        Continue(())
    }

    fn on_fld_class__tparams_top_down(&mut self, _: &Env, _: &mut Vec<Tparam>) -> ControlFlow<()> {
        self.forbid_this = true;
        Continue(())
    }

    fn on_fld_class__extends_top_down(
        &mut self,
        _: &Env,
        _: &mut Vec<ClassHint>,
    ) -> ControlFlow<()> {
        self.in_extends = true;
        Continue(())
    }

    fn on_fld_class__uses_top_down(&mut self, _: &Env, _: &mut Vec<TraitHint>) -> ControlFlow<()> {
        self.forbid_this = false;
        Continue(())
    }

    fn on_fld_class__xhp_attrs_top_down(
        &mut self,
        _: &Env,
        _: &mut Vec<XhpAttr>,
    ) -> ControlFlow<()> {
        self.forbid_this = false;
        Continue(())
    }

    fn on_fld_class__xhp_attr_uses_top_down(
        &mut self,
        _: &Env,
        _: &mut Vec<XhpAttrHint>,
    ) -> ControlFlow<()> {
        self.forbid_this = false;
        Continue(())
    }

    fn on_fld_class__reqs_top_down(&mut self, _: &Env, _: &mut Vec<ClassReq>) -> ControlFlow<()> {
        self.forbid_this = false;
        Continue(())
    }

    fn on_ty_class_req_top_down(&mut self, _: &Env, elem: &mut ClassReq) -> ControlFlow<()> {
        self.in_req_extends = matches!(elem.1, RequireKind::RequireExtends);
        Continue(())
    }

    fn on_fld_class__implements_top_down(
        &mut self,
        _: &Env,
        _: &mut Vec<ClassHint>,
    ) -> ControlFlow<()> {
        self.forbid_this = false;
        Continue(())
    }

    fn on_ty_class_var_top_down(&mut self, _: &Env, elem: &mut ClassVar) -> ControlFlow<()> {
        self.lsb = if elem.is_static {
            Some(
                !elem
                    .user_attributes
                    .iter()
                    .any(|ua| ua.name.name() == sn::user_attributes::LSB),
            )
        } else {
            None
        };
        Continue(())
    }

    fn on_fld_class_var_type__top_down(&mut self, _: &Env, _: &mut TypeHint) -> ControlFlow<()> {
        self.forbid_this = self.lsb.unwrap_or(false);
        self.lsb = None;
        Continue(())
    }

    fn on_fld_fun__ret_top_down(&mut self, _: &Env, _: &mut TypeHint) -> ControlFlow<()> {
        self.reset();
        Continue(())
    }

    fn on_ty_expr__top_down(&mut self, _: &Env, elem: &mut Expr_) -> ControlFlow<()> {
        match elem {
            Expr_::Cast(..) | Expr_::Is(..) | Expr_::As(..) | Expr_::Upcast(..) => self.reset(),
            _ => (),
        }
        Continue(())
    }

    fn on_ty_shape_field_info_top_down(
        &mut self,
        _: &Env,
        _: &mut ShapeFieldInfo,
    ) -> ControlFlow<()> {
        self.reset();
        Continue(())
    }

    fn on_fld_hint_fun_return_ty_top_down(&mut self, _: &Env, _: &mut Hint) -> ControlFlow<()> {
        self.reset();
        Continue(())
    }

    fn on_ty_targ_top_down(&mut self, _: &Env, _: &mut Targ) -> ControlFlow<()> {
        self.reset();
        Continue(())
    }
}

#[cfg(test)]
mod tests {

    use std::sync::Arc;

    use oxidized::file_info::Mode;
    use nast::Id;
    use nast::Pos;
    use nast::UserAttribute;
    use nast::UserAttributes;
    use oxidized::namespace_env;
    use oxidized::namespace_env::Mode as NamespaceMode;
    use oxidized::s_map::SMap;

    use super::*;

    fn make_class(
        kind: ClassishKind,
        name: &str,
        final_: bool,
        tparams: Vec<Tparam>,
        extends: Vec<ClassHint>,
        reqs: Vec<ClassReq>,
    ) -> Class_ {
        Class_ {
            span: Default::default(),
            annotation: (),
            mode: Mode::Mstrict,
            final_,
            is_xhp: Default::default(),
            has_xhp_keyword: Default::default(),
            kind,
            name: Id(Pos::default(), name.to_string()),
            tparams,
            extends,
            uses: Default::default(),
            xhp_attr_uses: Default::default(),
            xhp_category: Default::default(),
            reqs,
            implements: Default::default(),
            consts: Default::default(),
            typeconsts: Default::default(),
            vars: Default::default(),
            methods: Default::default(),
            xhp_children: Default::default(),
            xhp_attrs: Default::default(),
            namespace: Arc::new(namespace_env::Env {
                ns_uses: SMap::default(),
                class_uses: SMap::default(),
                fun_uses: SMap::default(),
                const_uses: SMap::default(),
                name: None,
                mode: NamespaceMode::ForTypecheck,
                disable_xhp_element_mangling: false,
            }),
            user_attributes: Default::default(),
            file_attributes: Default::default(),
            docs_url: Default::default(),
            enum_: Default::default(),
            doc_comment: Default::default(),
            emit_id: Default::default(),
            internal: Default::default(),
            module: Default::default(),
            package: None,
        }
    }

    fn make_static_class_var(name: &str, type_: TypeHint, lsb: bool) -> ClassVar {
        let user_attributes = if lsb {
            UserAttributes(vec![UserAttribute {
                name: Id(Default::default(), sn::user_attributes::LSB.to_string()),
                params: vec![],
            }])
        } else {
            UserAttributes(vec![])
        };
        ClassVar {
            final_: Default::default(),
            xhp_attr: Default::default(),
            abstract_: Default::default(),
            readonly: Default::default(),
            visibility: nast::Visibility::Public,
            type_,
            id: Id(Default::default(), name.to_string()),
            expr: Default::default(),
            user_attributes,
            doc_comment: Default::default(),
            is_static: true,
            span: Default::default(),
        }
    }
    // -- `this` in extends clause ---------------------------------------------

    #[test]
    // We allow `this` as a generic on a super type when the class is final
    // and not generic
    fn test_final_extends_non_generic_valid() {
        let env = Env::default();

        let mut pass = ElabHintThisPass::default();
        // final class C extends B<this> {}
        let mut elem: Class_ = make_class(
            ClassishKind::Cclass(nast::Abstraction::Concrete),
            "C",
            true,
            vec![],
            vec![Hint(
                Pos::default(),
                Box::new(Hint_::Happly(
                    Id(Pos::default(), "B".to_string()),
                    vec![Hint(Pos::default(), Box::new(Hint_::Hthis))],
                )),
            )],
            vec![],
        );

        elem.transform(&env, &mut pass);

        // Expect no errors
        assert!(env.into_errors().is_empty());
        assert!(match elem.extends.pop() {
            Some(Hint(_, box Hint_::Happly(_, hints))) => match hints.as_slice() {
                [Hint(_, box Hint_::Hthis)] => true,
                _ => false,
            },
            _ => false,
        })
    }

    #[test]
    // We allow `this` as a generic on a super type when the class is final
    // and invariant in all type parameters
    fn test_final_extends_invariant_valid() {
        let env = Env::default();

        let mut pass = ElabHintThisPass::default();
        // final class C<T> extends B<this> {}
        let mut elem: Class_ = make_class(
            ClassishKind::Cclass(nast::Abstraction::Concrete),
            "C",
            true,
            vec![Tparam {
                variance: Variance::Invariant,
                name: Id(Pos::default(), "T".to_string()),
                constraints: Default::default(),
                reified: nast::ReifyKind::Erased,
                user_attributes: Default::default(),
            }],
            vec![Hint(
                Pos::default(),
                Box::new(Hint_::Happly(
                    Id(Pos::default(), "B".to_string()),
                    vec![Hint(Pos::default(), Box::new(Hint_::Hthis))],
                )),
            )],
            vec![],
        );

        elem.transform(&env, &mut pass);

        // Expect no errors
        assert!(env.into_errors().is_empty());
        assert!(match elem.extends.pop() {
            Some(Hint(_, box Hint_::Happly(_, hints))) => match hints.as_slice() {
                [Hint(_, box Hint_::Hthis)] => true,
                _ => false,
            },
            _ => false,
        })
    }

    #[test]
    // We disallow `this` as a generic on a super type when the class is final
    // and but invariant in some type parameter
    fn test_final_extends_covariant_invalid() {
        let env = Env::default();

        let mut pass = ElabHintThisPass::default();
        // final class C<+T> extends B<this> {}
        let mut elem: Class_ = make_class(
            ClassishKind::Cclass(nast::Abstraction::Concrete),
            "C",
            true,
            vec![Tparam {
                variance: Variance::Covariant,
                name: Id(Pos::default(), "T".to_string()),
                constraints: Default::default(),
                reified: nast::ReifyKind::Erased,
                user_attributes: Default::default(),
            }],
            vec![Hint(
                Pos::default(),
                Box::new(Hint_::Happly(
                    Id(Pos::default(), "B".to_string()),
                    vec![Hint(Pos::default(), Box::new(Hint_::Hthis))],
                )),
            )],
            vec![],
        );

        elem.transform(&env, &mut pass);

        let this_type_forbidden_err_opt = env.into_errors().pop();
        assert!(match this_type_forbidden_err_opt {
            Some(NamingPhaseError::Naming(NamingError::ThisTypeForbidden {
                in_extends,
                in_req_extends,
                ..
            })) => in_extends && !in_req_extends,
            _ => false,
        });
    }

    // -- `this` hint in require extends ---------------------------------------

    #[test]
    // We disallow `this` as a generic in require extends clauses
    fn test_req_extends_generic_invalid() {
        let env = Env::default();

        let mut pass = ElabHintThisPass::default();
        // trait C<T> { require extends B<this>; }
        let mut elem: Class_ = make_class(
            ClassishKind::Ctrait,
            "C",
            false,
            vec![Tparam {
                variance: Variance::Invariant,
                name: Id(Pos::default(), "T".to_string()),
                constraints: Default::default(),
                reified: nast::ReifyKind::Erased,
                user_attributes: Default::default(),
            }],
            vec![],
            vec![ClassReq(
                Hint(
                    Pos::default(),
                    Box::new(Hint_::Happly(
                        Id(Pos::default(), "B".to_string()),
                        vec![Hint(Pos::default(), Box::new(Hint_::Hthis))],
                    )),
                ),
                RequireKind::RequireExtends,
            )],
        );

        elem.transform(&env, &mut pass);

        let this_type_forbidden_err_opt = env.into_errors().pop();
        assert!(match this_type_forbidden_err_opt {
            Some(NamingPhaseError::Naming(NamingError::ThisTypeForbidden {
                in_extends,
                in_req_extends,
                ..
            })) => !in_extends && in_req_extends,
            _ => false,
        });
    }

    #[test]
    // We disallow `this` as a top-level hint in require extends clauses
    fn test_req_extends_top_level_invalid() {
        let env = Env::default();

        let mut pass = ElabHintThisPass::default();
        // trait C<T> { require extends this; }
        let mut elem: Class_ = make_class(
            ClassishKind::Ctrait,
            "C",
            false,
            vec![Tparam {
                variance: Variance::Invariant,
                name: Id(Pos::default(), "T".to_string()),
                constraints: Default::default(),
                reified: nast::ReifyKind::Erased,
                user_attributes: Default::default(),
            }],
            vec![],
            vec![ClassReq(
                Hint(Pos::default(), Box::new(Hint_::Hthis)),
                RequireKind::RequireExtends,
            )],
        );

        elem.transform(&env, &mut pass);

        let this_type_forbidden_err_opt = env.into_errors().pop();
        assert!(match this_type_forbidden_err_opt {
            Some(NamingPhaseError::Naming(NamingError::ThisTypeForbidden {
                in_extends,
                in_req_extends,
                ..
            })) => !in_extends && in_req_extends,
            _ => false,
        });
    }

    // -- `this` in static class var -------------------------------------------

    #[test]
    fn test_lsb_static_class_var_valid() {
        let env = Env::default();

        let mut pass = ElabHintThisPass::default();
        let mut elem: ClassVar = make_static_class_var(
            "x",
            TypeHint(
                (),
                Some(Hint(
                    Default::default(),
                    Box::new(Hint_::Hoption(Hint(
                        Default::default(),
                        Box::new(Hint_::Hthis),
                    ))),
                )),
            ),
            true,
        );

        elem.transform(&env, &mut pass);

        assert!(env.into_errors().is_empty());

        let TypeHint(_, hint_opt) = elem.type_;
        assert!(matches!(
            hint_opt,
            Some(Hint(_, box Hint_::Hoption(Hint(_, box Hint_::Hthis))))
        ));
    }

    #[test]
    fn test_non_lsb_static_class_var_invalid() {
        let env = Env::default();

        let mut pass = ElabHintThisPass::default();
        let mut elem: ClassVar = make_static_class_var(
            "x",
            TypeHint(
                (),
                Some(Hint(
                    Default::default(),
                    Box::new(Hint_::Hoption(Hint(
                        Default::default(),
                        Box::new(Hint_::Hthis),
                    ))),
                )),
            ),
            false,
        );

        elem.transform(&env, &mut pass);

        let this_type_forbidden_err_opt = env.into_errors().pop();
        assert!(match this_type_forbidden_err_opt {
            Some(NamingPhaseError::Naming(NamingError::ThisTypeForbidden {
                in_extends,
                in_req_extends,
                ..
            })) => !in_extends && !in_req_extends,
            _ => false,
        });
    }
}
