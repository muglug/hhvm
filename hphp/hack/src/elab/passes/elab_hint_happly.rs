// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

use std::collections::BTreeMap;

use nast::Class_;
use nast::Expr_;
use nast::FunDef;
use nast::Gconst;
use nast::Hint;
use nast::Hint_;
use nast::HintFun;
use nast::HintTparam;
use nast::Id;
use nast::Method_;
use nast::ModuleDef;
use nast::Pos;
use nast::Tparam;
use nast::Tprim;
use nast::Typedef;

use crate::prelude::*;

/// Port of `Naming_elab_happly_hint`.
#[derive(Clone, Default)]
pub struct ElabHintHapplyPass {
    /// The type parameters in scope, with the position they were bound at.
    tparams: Rc<BTreeMap<String, Pos>>,
}

impl ElabHintHapplyPass {
    fn extend_tparams(&mut self, tps: &[Tparam]) {
        if tps.is_empty() {
            return;
        }
        let tparams = Rc::make_mut(&mut self.tparams);
        for Tparam {
            name: Id(pos, nm), ..
        } in tps
        {
            tparams.insert(nm.clone(), pos.clone());
        }
    }

    fn extend_hint_tparams(&mut self, tps: &[HintTparam]) {
        if tps.is_empty() {
            return;
        }
        let tparams = Rc::make_mut(&mut self.tparams);
        for HintTparam {
            name: Id(pos, nm), ..
        } in tps
        {
            tparams.insert(nm.clone(), pos.clone());
        }
    }

    fn reset_tparams(&mut self) {
        self.tparams = Rc::new(BTreeMap::new());
    }

    fn set_tparams(&mut self, tps: &[Tparam]) {
        self.reset_tparams();
        self.extend_tparams(tps);
    }

    /// Disallow rebinding type parameters that occur in class or method
    /// position but allow names to be reused across different first-class
    /// polymorphic function hints
    fn validate_hint_tparams(&self, env: &Env, tps: &[HintTparam]) {
        if tps.is_empty() {
            return;
        }
        let mut bound: BTreeMap<String, Pos> = (*self.tparams).clone();
        for HintTparam {
            name: Id(pos, tparam_name),
            ..
        } in tps
        {
            match bound.get(tparam_name) {
                Some(prev_pos) => env.emit_error(NamingError::ShadowedTparam {
                    pos: pos.clone(),
                    tparam_name: tparam_name.clone(),
                    prev_pos: prev_pos.clone(),
                }),
                None => {
                    bound.insert(tparam_name.clone(), pos.clone());
                }
            }
        }
    }
}

impl Pass for ElabHintHapplyPass {
    fn on_ty_typedef_top_down(&mut self, _: &Env, elem: &mut Typedef) -> ControlFlow<()> {
        self.set_tparams(&elem.tparams);
        Continue(())
    }

    fn on_ty_gconst_top_down(&mut self, _: &Env, _: &mut Gconst) -> ControlFlow<()> {
        self.reset_tparams();
        Continue(())
    }

    fn on_ty_fun_def_top_down(&mut self, _: &Env, elem: &mut FunDef) -> ControlFlow<()> {
        self.set_tparams(&elem.tparams);
        Continue(())
    }

    fn on_ty_module_def_top_down(&mut self, _: &Env, _: &mut ModuleDef) -> ControlFlow<()> {
        self.reset_tparams();
        Continue(())
    }

    fn on_ty_class__top_down(&mut self, _: &Env, elem: &mut Class_) -> ControlFlow<()> {
        self.set_tparams(&elem.tparams);
        Continue(())
    }

    fn on_ty_method__top_down(&mut self, _: &Env, elem: &mut Method_) -> ControlFlow<()> {
        self.extend_tparams(&elem.tparams);
        Continue(())
    }

    fn on_ty_expr__top_down(&mut self, env: &Env, elem: &mut Expr_) -> ControlFlow<()> {
        let fun_ = match elem {
            Expr_::Lfun(box (fun_, _)) => fun_,
            Expr_::Efun(efun) => &efun.fun,
            _ => return Continue(()),
        };
        self.validate_hint_tparams(env, &fun_.tparams);
        self.extend_hint_tparams(&fun_.tparams);
        Continue(())
    }

    fn on_ty_hint_fun_top_down(&mut self, env: &Env, elem: &mut HintFun) -> ControlFlow<()> {
        self.validate_hint_tparams(env, &elem.tparams);
        self.extend_hint_tparams(&elem.tparams);
        Continue(())
    }

    fn on_ty_hint_top_down(&mut self, env: &Env, elem: &mut Hint) -> ControlFlow<()> {
        let Hint(hint_pos, hint_) = elem;
        if let Hint_::Happly(tycon, hints) = &mut **hint_ {
            match canonicalize_happly(&self.tparams, hint_pos, tycon, hints) {
                Ok((new_hint, err_opt)) => {
                    if let Some(new_hint) = new_hint {
                        *elem = new_hint;
                    }
                    if let Some(err) = err_opt {
                        env.emit_error(err)
                    }
                    Continue(())
                }
                Err(err) => {
                    env.emit_error(err);
                    Break(())
                }
            }
        } else {
            Continue(())
        }
    }
}

enum CanonResult {
    Concrete(Hint_),
    This,
    Classname,
    Tycon,
    Typaram,
    Varray,
    Darray,
    VecOrDict,
    CanonErr(NamingError),
}

/// A number of hints are represented by `Happly` after lowering; we elaborate
/// to the canonical representation here taking care to separate the result
/// so we can apply subsequent validation of the hint based on where it appeared
fn canonical_tycon(tparams: &BTreeMap<String, Pos>, Id(pos, name): &Id) -> CanonResult {
    let name = name.as_str();
    if name == sn::typehints::INT {
        CanonResult::Concrete(Hint_::Hprim(Tprim::Tint))
    } else if name == sn::typehints::BOOL {
        CanonResult::Concrete(Hint_::Hprim(Tprim::Tbool))
    } else if name == sn::typehints::FLOAT {
        CanonResult::Concrete(Hint_::Hprim(Tprim::Tfloat))
    } else if name == sn::typehints::DARRAY {
        CanonResult::Darray
    } else if name == sn::typehints::VARRAY {
        CanonResult::Varray
    } else if name == sn::typehints::VARRAY_OR_DARRAY || name == sn::typehints::VEC_OR_DICT {
        // TODO[mjt] `vec_or_dict` is currently special cased since the canonical representation
        // requires us to have no arity mismatches or throw away info. We do not use that repr here
        // to avoid having to do so. Ultimately, we should remove that special case
        CanonResult::VecOrDict
    } else if name == sn::typehints::VOID {
        CanonResult::Concrete(Hint_::Hprim(Tprim::Tvoid))
    } else if name == sn::typehints::NORETURN {
        CanonResult::Concrete(Hint_::Hprim(Tprim::Tnoreturn))
    } else if name == sn::typehints::NULL {
        CanonResult::Concrete(Hint_::Hprim(Tprim::Tnull))
    } else if name == sn::typehints::NUM {
        CanonResult::Concrete(Hint_::Hprim(Tprim::Tnum))
    } else if name == sn::typehints::RESOURCE {
        CanonResult::Concrete(Hint_::Hprim(Tprim::Tresource))
    } else if name == sn::typehints::ARRAYKEY {
        CanonResult::Concrete(Hint_::Hprim(Tprim::Tarraykey))
    } else if name == sn::typehints::MIXED {
        CanonResult::Concrete(Hint_::Hmixed)
    } else if name == sn::typehints::NONNULL {
        CanonResult::Concrete(Hint_::Hnonnull)
    } else if name == sn::typehints::NOTHING {
        CanonResult::Concrete(Hint_::Hnothing)
    } else if name == sn::typehints::DYNAMIC {
        CanonResult::Concrete(Hint_::Hdynamic)
    } else if name == sn::typehints::THIS {
        CanonResult::This
    } else if is_toplevel_prim(name) {
        CanonResult::CanonErr(NamingError::PrimitiveTopLevel(pos.clone()))
    } else if name == sn::classes::CLASS_NAME || name == "classname" {
        // TODO[mjt] why wouldn't be have a fully qualified name here?
        CanonResult::Classname
    } else if tparams.contains_key(name) {
        CanonResult::Typaram
    } else {
        CanonResult::Tycon
    }
}

fn is_toplevel_prim(name: &str) -> bool {
    match name.strip_prefix('\\') {
        Some(name) => {
            name == sn::typehints::VOID
                || name == sn::typehints::NULL
                || name == sn::typehints::NORETURN
                || name == sn::typehints::INT
                || name == sn::typehints::BOOL
                || name == sn::typehints::FLOAT
                || name == sn::typehints::NUM
                || name == sn::typehints::RESOURCE
                || name == sn::typehints::MIXED
                || name == sn::typehints::NONNULL
                || name == sn::typehints::ARRAYKEY
                || name == sn::typehints::NOTHING
        }
        None => false,
    }
}

/// After lowering many hints are represented as `Happly(...,...)`. Here
/// we canonicalise the representation of type constructor then handle
/// errors and further elaboration.
///
/// `Ok((Some(hint), _))` is the hint to use in place of the `Happly`;
/// `Ok((None, _))` means it was updated in place (or is to be left alone).
/// `Err(_)` means the hint was malformed: it is left as it is and must not be
/// elaborated further.
fn canonicalize_happly(
    tparams: &BTreeMap<String, Pos>,
    hint_pos: &Pos,
    tycon: &mut Id,
    hints: &mut Vec<Hint>,
) -> Result<(Option<Hint>, Option<NamingError>), NamingError> {
    let mk = |pos: &Pos, hint_: Hint_| Some(Hint(pos.clone(), Box::new(hint_)));
    match canonical_tycon(tparams, tycon) {
        // The hint was malformed
        CanonResult::CanonErr(err) => Err(err),
        // The type constructors canonical representation is a concrete type
        CanonResult::Concrete(hint_) => {
            // We can't represent a concrete type applied to other types
            // so we raise an error here
            let err_opt = if !hints.is_empty() {
                Some(NamingError::UnexpectedTypeArguments(tycon.0.clone()))
            } else {
                None
            };
            Ok((mk(hint_pos, hint_), err_opt))
        }
        // The type constructors corresponds to an in-scope type parameter
        CanonResult::Typaram => {
            let err_opt = if hints.is_empty() {
                None
            } else {
                Some(NamingError::TparamAppliedToType {
                    pos: hint_pos.clone(),
                    tparam_name: tycon.1.clone(),
                })
            };
            let hint_ = Hint_::Habstr(std::mem::take(&mut tycon.1));
            Ok((mk(hint_pos, hint_), err_opt))
        }
        // The type constructors canonical representation is `Happly` but
        // additional elaboration / validation is required
        CanonResult::This => {
            let err_opt = if !hints.is_empty() {
                Some(NamingError::ThisNoArgument(hint_pos.clone()))
            } else {
                None
            };
            Ok((mk(&tycon.0, Hint_::Hthis), err_opt))
        }
        CanonResult::Classname => {
            // TODO[mjt] currently if `classname` is not applied to exactly
            // one type parameter, it canonicalizes to `Hprim Tstring`.
            // Investigate why this happens and if we can delay treatment to
            // typing
            if hints.len() == 1 {
                tycon.1 = sn::classes::CLASS_NAME.to_string();
                Ok((None, None))
            } else {
                let pos = tycon.0.clone();
                let hint_ = Hint_::Happly(
                    Id(pos.clone(), sn::typehints::HH_STRING.to_string()),
                    vec![],
                );
                Ok((mk(hint_pos, hint_), Some(NamingError::ClassnameParam(pos))))
            }
        }
        CanonResult::Darray => {
            tycon.1 = sn::collections::DICT.to_string();
            Ok((None, None))
        }
        CanonResult::Varray => {
            tycon.1 = sn::collections::VEC.to_string();
            Ok((None, None))
        }
        // TODO[mjt] should we really be special casing `vec_or_dict` both in
        // its representation and error handling?
        CanonResult::VecOrDict => match hints.len() {
            0 => Ok((
                None,
                Some(NamingError::TooFewTypeArguments(hint_pos.clone())),
            )),
            1 => {
                let val_hint = hints.pop().unwrap();
                Ok((mk(hint_pos, Hint_::HvecOrDict(None, val_hint)), None))
            }
            2 => {
                let val_hint = hints.pop().unwrap();
                let key_hint = hints.pop().unwrap();
                Ok((
                    mk(hint_pos, Hint_::HvecOrDict(Some(key_hint), val_hint)),
                    None,
                ))
            }
            _ => Ok((
                None,
                Some(NamingError::TooManyTypeArguments(hint_pos.clone())),
            )),
        },
        // The type constructors canonical representation is `Happly`
        CanonResult::Tycon => Ok((None, None)),
    }
}

#[cfg(test)]
mod tests {

    use nast::ClassConcreteTypeconst;
    use nast::ClassTypeconst;

    use super::*;
    #[test]
    fn test_int() {
        let env = Env::default();

        let mut pass = ElabHintHapplyPass::default();

        let mut elem = Hint(
            Pos::NONE,
            Box::new(Hint_::Happly(
                Id(Pos::NONE, sn::typehints::INT.to_string()),
                vec![],
            )),
        );

        elem.transform(&env, &mut pass);
        let Hint(_, hint_) = elem;
        assert!(matches!(&*hint_, Hint_::Hprim(Tprim::Tint)))
    }

    #[test]
    fn test_typconst_int() {
        let env = Env::default();

        let mut pass = ElabHintHapplyPass::default();

        let mut elem = ClassTypeconst::TCConcrete(ClassConcreteTypeconst {
            c_tc_type: Hint(
                Pos::NONE,
                Box::new(Hint_::Happly(
                    Id(Pos::NONE, sn::typehints::INT.to_string()),
                    vec![],
                )),
            ),
        });

        elem.transform(&env, &mut pass);
        assert!(matches!(
            elem,
            ClassTypeconst::TCConcrete(ClassConcreteTypeconst {
                c_tc_type: Hint(_, box Hint_::Hprim(Tprim::Tint)),
            })
        ))
    }

    #[test]
    fn test_vec_or_dict_two_tyargs() {
        let env = Env::default();

        let mut pass = ElabHintHapplyPass::default();

        let mut elem = Hint(
            Pos::NONE,
            Box::new(Hint_::Happly(
                Id(Pos::NONE, sn::typehints::VEC_OR_DICT.to_string()),
                vec![
                    Hint(Pos::NONE, Box::new(Hint_::Hmixed)),
                    Hint(Pos::NONE, Box::new(Hint_::Hnothing)),
                ],
            )),
        );

        elem.transform(&env, &mut pass);
        let Hint(_, hint_) = elem;
        assert!(match &*hint_ {
            Hint_::HvecOrDict(Some(h1), h2) => {
                let Hint(_, h1_) = h1 as &Hint;
                let Hint(_, h2_) = h2 as &Hint;
                matches!(**h1_, Hint_::Hmixed) && matches!(**h2_, Hint_::Hnothing)
            }
            _ => false,
        })
    }

    #[test]
    fn test_vec_or_dict_one_tyargs() {
        let env = Env::default();

        let mut pass = ElabHintHapplyPass::default();

        let mut elem = Hint(
            Pos::NONE,
            Box::new(Hint_::Happly(
                Id(Pos::NONE, sn::typehints::VEC_OR_DICT.to_string()),
                vec![Hint(Pos::NONE, Box::new(Hint_::Hnothing))],
            )),
        );

        elem.transform(&env, &mut pass);
        let Hint(_, hint_) = elem;
        assert!(match &*hint_ {
            Hint_::HvecOrDict(None, h) => {
                let Hint(_, h_) = h as &Hint;
                matches!(**h_, Hint_::Hnothing)
            }
            _ => false,
        })
    }
}
