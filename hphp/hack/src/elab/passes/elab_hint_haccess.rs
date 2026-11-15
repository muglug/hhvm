// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

use nast::Class_;
use nast::Contexts;
use nast::Hint;
use nast::Hint_;
use nast::Id;
use nast::WhereConstraintHint;
use oxidized::aast_visitor::AstParams;
use oxidized::aast_visitor::Node;
use oxidized::aast_visitor::Visitor;

use crate::prelude::*;

/// Port of `Naming_elab_haccess_hint` (the fields are those of
/// `Naming_phase_env.Elab_haccess_hint`).
#[derive(Clone, Default)]
pub struct ElabHintHaccessPass {
    current_class: Option<Rc<Id>>,
    in_where_clause: bool,
    in_generated_where_clause: bool,
    in_context: bool,
    in_haccess: bool,
}

/// `SN.Coeffects.generated_generic_prefix`
const GENERATED_GENERIC_PREFIX: &str = "T/";

/// Does the hint mention a generic generated for a polymorphic context?
struct IsGeneratedHint(bool);

impl<'ast> Visitor<'ast> for IsGeneratedHint {
    type Params = AstParams<(), ()>;

    fn object(&mut self) -> &mut dyn Visitor<'ast, Params = Self::Params> {
        self
    }

    fn visit_hint(&mut self, c: &mut (), hint: &'ast Hint) -> Result<(), ()> {
        match &*hint.1 {
            Hint_::Happly(Id(_, name), _)
                if name.starts_with(GENERATED_GENERIC_PREFIX) =>
            {
                self.0 = true;
                Ok(())
            }
            _ => hint.recurse(c, self.object()),
        }
    }
}

fn is_generated_hint(hint: &Hint) -> bool {
    let mut visitor = IsGeneratedHint(false);
    let _ = visitor.visit_hint(&mut (), hint);
    visitor.0
}

impl Pass for ElabHintHaccessPass {
    fn on_ty_hint_top_down(&mut self, env: &Env, elem: &mut Hint) -> ControlFlow<()> {
        let res = if self.in_haccess {
            let Hint(pos, hint_) = elem;
            match &mut **hint_ {
                // TODO[mjt] we appear to be discarding type parameters on `Happly` here
                // - should we change the representation of `Haccess` or handle
                // erroneous type parameters?
                Hint_::Happly(id, hints) if id.name() == sn::classes::SELF => {
                    match self.current_class.as_deref() {
                        Some(class_id) => {
                            *id = class_id.clone();
                            hints.clear();
                            Ok(())
                        }
                        None => Err(NamingError::SelfOutsideClass(id.0.clone())),
                    }
                }
                // TODO[mjt] is this ever exercised? The cases is handles appear to
                // be a parse errors
                Hint_::Happly(id, _)
                    if id.name() == sn::classes::STATIC || id.name() == sn::classes::PARENT =>
                {
                    Err(NamingError::InvalidTypeAccessRoot {
                        pos: id.pos().clone(),
                        id: Some(id.name().to_string()),
                    })
                }
                Hint_::Hthis | Hint_::Happly(..) => Ok(()),
                Hint_::Habstr(..) if self.in_generated_where_clause || self.in_context => Ok(()),
                Hint_::Habstr(..) if self.in_where_clause => {
                    Err(NamingError::InvalidTypeAccessInWhere(pos.clone()))
                }
                // TODO[mjt] why are we allow `Hvar`?
                Hint_::Hvar(..) => Ok(()),
                _ => Err(NamingError::InvalidTypeAccessRoot {
                    pos: pos.clone(),
                    id: None,
                }),
            }
        } else {
            Ok(())
        };
        self.in_haccess = matches!(&*elem.1, Hint_::Haccess(..));
        match res {
            Ok(()) => Continue(()),
            Err(err) => {
                env.emit_error(err);
                Break(())
            }
        }
    }

    fn on_ty_class__top_down(&mut self, _: &Env, elem: &mut Class_) -> ControlFlow<()> {
        self.current_class = Some(Rc::new(elem.name.clone()));
        Continue(())
    }

    fn on_ty_where_constraint_hint_top_down(
        &mut self,
        _: &Env,
        elem: &mut WhereConstraintHint,
    ) -> ControlFlow<()> {
        let WhereConstraintHint(hint1, _, hint2) = elem;
        self.in_where_clause = true;
        self.in_generated_where_clause = is_generated_hint(hint1) || is_generated_hint(hint2);
        Continue(())
    }

    fn on_ty_contexts_top_down(&mut self, _: &Env, _: &mut Contexts) -> ControlFlow<()> {
        self.in_context = true;
        Continue(())
    }
}

#[cfg(test)]
mod tests {

    use nast::ConstraintKind;
    use nast::Id;
    use nast::Pos;

    use super::*;

    // -- type access through `self` -------------------------------------------

    #[test]
    // type access through `self` is valid inside a class
    fn test_haccess_self_in_class_valid() {
        let env = Env::default();

        let class_name = "Classy";
        let mut pass = ElabHintHaccessPass {
            current_class: Some(Rc::new(Id(Default::default(), "Classy".to_string()))),
            ..Default::default()
        };
        let mut elem = Hint(
            Pos::default(),
            Box::new(Hint_::Haccess(
                Hint(
                    Pos::default(),
                    Box::new(Hint_::Happly(
                        Id(Pos::default(), sn::classes::SELF.to_string()),
                        vec![],
                    )),
                ),
                vec![Id(Pos::default(), "T".to_string())],
            )),
        );
        elem.transform(&env, &mut pass);

        assert!(env.into_errors().is_empty());
        assert!(match elem {
            Hint(_, box Hint_::Haccess(Hint(_, box Hint_::Happly(id, hints)), _)) =>
                id.name() == class_name && hints.is_empty(),
            _ => false,
        })
    }

    #[test]
    // currently we erase any type params to which `self` is applied; adding
    // test for tracking
    fn test_haccess_self_in_class_erased_tparams_valid() {
        let env = Env::default();

        let class_name = "Classy";
        let mut pass = ElabHintHaccessPass {
            current_class: Some(Rc::new(Id(Default::default(), "Classy".to_string()))),
            ..Default::default()
        };
        let mut elem = Hint(
            Pos::default(),
            Box::new(Hint_::Haccess(
                Hint(
                    Pos::default(),
                    Box::new(Hint_::Happly(
                        Id(Pos::default(), sn::classes::SELF.to_string()),
                        vec![Hint(Pos::default(), Box::new(Hint_::Hmixed))],
                    )),
                ),
                vec![Id(Pos::default(), "T".to_string())],
            )),
        );
        elem.transform(&env, &mut pass);

        assert!(env.into_errors().is_empty());
        assert!(match elem {
            Hint(_, box Hint_::Haccess(Hint(_, box Hint_::Happly(id, hints)), _)) =>
                id.name() == class_name && hints.is_empty(),
            _ => false,
        })
    }

    #[test]
    // type access through `self` is invalid outside a class
    fn test_haccess_self_outside_class_invalid() {
        let env = Env::default();

        let mut pass = ElabHintHaccessPass::default();
        let mut elem = Hint(
            Pos::default(),
            Box::new(Hint_::Haccess(
                Hint(
                    Pos::default(),
                    Box::new(Hint_::Happly(
                        Id(Pos::default(), sn::classes::SELF.to_string()),
                        vec![],
                    )),
                ),
                vec![Id(Pos::default(), "T".to_string())],
            )),
        );
        elem.transform(&env, &mut pass);

        let err_opt = env.into_errors().pop();
        assert!(matches!(
            err_opt,
            Some(NamingPhaseError::Naming(NamingError::SelfOutsideClass(..)))
        ));
    }
    // -- type access through `this` -------------------------------------------

    #[test]
    // type access through `this` is always valid
    fn test_haccess_this_valid() {
        let env = Env::default();

        let mut pass = ElabHintHaccessPass::default();
        let mut elem = Hint(
            Pos::default(),
            Box::new(Hint_::Haccess(
                Hint(Pos::default(), Box::new(Hint_::Hthis)),
                vec![Id(Pos::default(), "T".to_string())],
            )),
        );
        elem.transform(&env, &mut pass);

        assert!(env.into_errors().is_empty());
        assert!(matches!(
            elem,
            Hint(_, box Hint_::Haccess(Hint(_, box Hint_::Hthis), _))
        ))
    }

    // -- type access through `static` / `parent` ------------------------------
    #[test]
    // type access through `static` is invalid
    fn test_haccess_static_in_class_invalid() {
        let env = Env::default();

        let mut pass = ElabHintHaccessPass {
            current_class: Some(Rc::new(Id(Default::default(), "Classy".to_string()))),
            ..Default::default()
        };
        let mut elem = Hint(
            Pos::default(),
            Box::new(Hint_::Haccess(
                Hint(
                    Pos::default(),
                    Box::new(Hint_::Happly(
                        Id(Pos::default(), sn::classes::STATIC.to_string()),
                        vec![],
                    )),
                ),
                vec![Id(Pos::default(), "T".to_string())],
            )),
        );
        elem.transform(&env, &mut pass);

        let err_opt = env.into_errors().pop();
        assert!(matches!(
            err_opt,
            Some(NamingPhaseError::Naming(
                NamingError::InvalidTypeAccessRoot { .. }
            ))
        ));
    }

    // -- type access through type param ---------------------------------------

    #[test]
    // type access through type parameter is valid inside a context
    fn test_haccess_tparam_in_context_valid() {
        let env = Env::default();

        let mut pass = ElabHintHaccessPass::default();
        let mut elem = Contexts(
            Pos::default(),
            vec![Hint(
                Pos::default(),
                Box::new(Hint_::Haccess(
                    Hint(
                        Pos::default(),
                        Box::new(Hint_::Habstr("T".to_string())),
                    ),
                    vec![Id(Pos::default(), "C".to_string())],
                )),
            )],
        );
        elem.transform(&env, &mut pass);

        assert!(env.into_errors().is_empty());
        let Contexts(_, mut hints) = elem;
        assert!(matches!(
            hints.pop(),
            Some(Hint(_, box Hint_::Haccess(Hint(_, box Hint_::Habstr(..)), _)))
        ))
    }

    #[test]
    // type access through type parameter is an error inside a where clause
    // (unless the where clause is generated for a polymorphic context)
    fn test_haccess_tparam_in_where_clause_invalid() {
        let env = Env::default();

        let mut pass = ElabHintHaccessPass::default();
        let mut elem = WhereConstraintHint(
            Hint(
                Pos::default(),
                Box::new(Hint_::Haccess(
                    Hint(
                        Pos::default(),
                        Box::new(Hint_::Habstr("T".to_string())),
                    ),
                    vec![Id(Pos::default(), "C".to_string())],
                )),
            ),
            ConstraintKind::ConstraintSuper,
            Hint(Pos::default(), Box::new(Hint_::Hmixed)),
        );
        elem.transform(&env, &mut pass);

        assert!(matches!(
            env.into_errors().pop(),
            Some(NamingPhaseError::Naming(
                NamingError::InvalidTypeAccessInWhere(_)
            ))
        ));
        let WhereConstraintHint(hint, _, _) = elem;
        assert!(matches!(
            hint,
            Hint(_, box Hint_::Haccess(Hint(_, box Hint_::Habstr(..)), _))
        ))
    }

    #[test]
    // type access through type parameter in any other context is invalid
    fn test_haccess_tparam_invalid() {
        let env = Env::default();

        let mut pass = ElabHintHaccessPass::default();
        let mut elem = Hint(
            Pos::default(),
            Box::new(Hint_::Haccess(
                Hint(
                    Pos::default(),
                    Box::new(Hint_::Habstr("T".to_string())),
                ),
                vec![Id(Pos::default(), "C".to_string())],
            )),
        );
        elem.transform(&env, &mut pass);

        let err_opt = env.into_errors().pop();
        assert!(matches!(
            err_opt,
            Some(NamingPhaseError::Naming(
                NamingError::InvalidTypeAccessRoot { .. }
            ))
        ));
    }
}
