// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

use nast::Class_;
use nast::Expr_;
use nast::ShapeExprField;
use nast::ShapeFieldInfo;
use nast::ShapeFieldName;

use crate::prelude::*;

#[derive(Clone, Default)]
pub struct ElabShapeFieldNamePass {
    current_class: Option<Rc<String>>,
}

impl ElabShapeFieldNamePass {
    pub fn in_class(&mut self, cls: &Class_) {
        self.current_class = Some(Rc::new(cls.name.name().to_string()));
    }
}

impl Pass for ElabShapeFieldNamePass {
    fn on_ty_class__top_down(&mut self, _: &Env, elem: &mut Class_) -> ControlFlow<()> {
        self.in_class(elem);
        Continue(())
    }

    fn on_ty_expr__bottom_up(&mut self, env: &Env, elem: &mut Expr_) -> ControlFlow<()> {
        if let Expr_::Shape(fields) = elem {
            for field in fields.iter_mut() {
                match field {
                    ShapeExprField::SFField(nm, _) => {
                        if let Err(err) = canonical_shape_name(nm, self.current_class.as_deref()) {
                            env.emit_error(err)
                        }
                    }
                    ShapeExprField::SFSplat(_) => {}
                }
            }
        }
        Continue(())
    }

    fn on_ty_shape_field_info_bottom_up(
        &mut self,
        env: &Env,
        elem: &mut ShapeFieldInfo,
    ) -> ControlFlow<()> {
        match canonical_shape_name(&mut elem.name, self.current_class.as_deref()) {
            Ok(()) => Continue(()),
            Err(err) => {
                env.emit_error(err);
                Break(())
            }
        }
    }
}

// We permit class constants to be used as shape field names. Here we replace
// uses of `self` with the class to which they refer or `unknown` if the shape
// is not defined within the context of a class
//
// TODO(T199272576) I believe all of this code should be dead by parse error,
// check and eliminate.
fn canonical_shape_name(
    nm: &mut ShapeFieldName,
    current_class: Option<&String>,
) -> Result<(), NamingError> {
    match nm {
        ShapeFieldName::SFclassname(id) | ShapeFieldName::SFclassConst(id, _)
            if id.name() == sn::classes::SELF =>
        {
            match current_class {
                Some(cls_nm) => {
                    id.1 = cls_nm.to_string();
                    Ok(())
                }
                None => {
                    id.1 = sn::classes::UNKNOWN.to_string();
                    Err(NamingError::SelfOutsideClass(id.0.clone()))
                }
            }
        }
        _ => Ok(()),
    }
}

#[cfg(test)]
mod tests {

    use nast::Hint;
    use nast::Hint_;
    use nast::Id;
    use nast::Pos;

    use super::*;

    // -- Valid cases ----------------------------------------------------------

    #[test]
    fn test_shape_in_class() {
        let env = Env::default();

        let class_name = "Classy";
        let mut pass = ElabShapeFieldNamePass {
            current_class: Some(Rc::new(class_name.to_string())),
        };
        let mut elem = Expr_::Shape(vec![ShapeExprField::SFField(
            ShapeFieldName::SFclassConst(
                Id(Pos::default(), sn::classes::SELF.to_string()),
                (Pos::default(), String::default()),
            ),
            elab_utils::expr::null(),
        )]);
        elem.transform(&env, &mut pass);

        // Expect no errors
        assert!(env.into_errors().is_empty());

        assert!(if let Expr_::Shape(mut fields) = elem {
            let field_opt = fields.pop();
            match field_opt {
                Some(ShapeExprField::SFField(ShapeFieldName::SFclassConst(id, _), _)) => {
                    id.name() == class_name
                }
                _ => false,
            }
        } else {
            false
        })
    }

    #[test]
    fn test_shape_field_info_in_class() {
        let env = Env::default();

        let class_name = "Classy";
        let mut pass = ElabShapeFieldNamePass {
            current_class: Some(Rc::new(class_name.to_string())),
        };
        let mut elem = ShapeFieldInfo {
            optional: Default::default(),
            hint: Hint(Pos::default(), Box::new(Hint_::Hmixed)),
            name: ShapeFieldName::SFclassConst(
                Id(Pos::default(), sn::classes::SELF.to_string()),
                (Pos::default(), String::default()),
            ),
        };
        elem.transform(&env, &mut pass);

        // Expect no errors
        assert!(env.into_errors().is_empty());

        assert!(match elem.name {
            ShapeFieldName::SFclassConst(id, _) => id.name() == class_name,
            _ => false,
        })
    }

    // -- Invalid cases --------------------------------------------------------

    #[test]
    fn test_shape_not_in_class() {
        let env = Env::default();

        let mut pass = ElabShapeFieldNamePass::default();
        let mut elem = Expr_::Shape(vec![ShapeExprField::SFField(
            ShapeFieldName::SFclassConst(
                Id(Pos::default(), sn::classes::SELF.to_string()),
                (Pos::default(), String::default()),
            ),
            elab_utils::expr::null(),
        )]);
        elem.transform(&env, &mut pass);

        let self_outside_class_err_opt = env.into_errors().pop();
        assert!(matches!(
            self_outside_class_err_opt,
            Some(NamingPhaseError::Naming(NamingError::SelfOutsideClass(..)))
        ));

        assert!(if let Expr_::Shape(mut fields) = elem {
            let field_opt = fields.pop();
            match field_opt {
                Some(ShapeExprField::SFField(ShapeFieldName::SFclassConst(id, _), _)) => {
                    id.name() == sn::classes::UNKNOWN
                }
                _ => false,
            }
        } else {
            false
        })
    }

    #[test]
    fn test_shape_field_info_not_in_class() {
        let env = Env::default();

        let mut pass = ElabShapeFieldNamePass::default();
        let mut elem = ShapeFieldInfo {
            optional: Default::default(),
            hint: Hint(Pos::default(), Box::new(Hint_::Hmixed)),
            name: ShapeFieldName::SFclassConst(
                Id(Pos::default(), sn::classes::SELF.to_string()),
                (Pos::default(), String::default()),
            ),
        };
        elem.transform(&env, &mut pass);

        let self_outside_class_err_opt = env.into_errors().pop();
        assert!(matches!(
            self_outside_class_err_opt,
            Some(NamingPhaseError::Naming(NamingError::SelfOutsideClass(..)))
        ));

        assert!(match elem.name {
            ShapeFieldName::SFclassConst(id, _) => id.name() == sn::classes::UNKNOWN,
            _ => false,
        })
    }
}
