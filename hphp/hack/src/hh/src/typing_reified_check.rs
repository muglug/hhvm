// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_reified_check.ml`. See `hh/PORTING.md`.
//!
//! The object `validator` (which inherits `Type_validator.type_validator`) is
//! the type [`Validator`], which implements
//! [`TypeValidator`](crate::type_validator::TypeValidator); `validator ()` is
//! the value, so `Typing_reified_check.validator#validate_hint env h
//! ~reification emit` is `validator().validate_hint(env, h, Some(reification),
//! emit)` (with the trait in scope).

use naming_special_names_rust as sn;
use oxidized::aast;
use pos::Positioned;
use pos::TypeName;
use ty::decl::ty as d;
use ty::reason::Reason as _;

use crate::ctx::R;
use crate::folded_class as cls;
use crate::type_validator::Reification;
use crate::type_validator::TypeValidator;
use crate::type_validator::ValidationState;
use crate::type_validator::inherited;
use crate::typing_defs::*;
/// `module Env = Typing_env`
use crate::typing_env as env;

/// The position type of declarations.
type DeclPos = <R as ty::reason::Reason>::Pos;

/// The class of the object `validator`.
#[derive(Clone, Copy, Debug, Default)]
pub struct Validator;

/// `let validator = object (this) inherit Type_validator.type_validator as
/// super ... end`
pub fn validator() -> Validator {
    Validator
}

impl TypeValidator for Validator {
    fn on_tapply(
        &self,
        acc: ValidationState,
        r: &R,
        id: &Positioned<TypeName, DeclPos>,
        tyl: &[DeclTy],
    ) -> ValidationState {
        let h = id.id_ref().as_str();
        if h == sn::classes::TYPE_NAME {
            self.invalid(acc, r, "a typename")
        } else if h == sn::classes::CLASS_NAME {
            self.invalid(acc, r, "a classname")
        } else {
            inherited::on_tapply(self, acc, r, id, tyl)
        }
    }

    fn on_tclass_ptr(&self, acc: ValidationState, r: &R, _ty: &DeclTy) -> ValidationState {
        // TODO(T199611023) allow when we enforce inner type
        self.invalid(acc, r, "a class pointer type")
    }

    fn on_twildcard(&self, acc: ValidationState, r: &R) -> ValidationState {
        if acc.env.allow_wildcards {
            acc
        } else {
            self.invalid(acc, r, "a wildcard")
        }
    }

    fn on_tgeneric(&self, acc: ValidationState, r: &R, t: &str) -> ValidationState {
        match env::get_reified(&acc.env, t) {
            aast::ReifyKind::Erased => self.invalid(acc, r, "not reified"),
            aast::ReifyKind::SoftReified => self.invalid(acc, r, "soft reified"),
            aast::ReifyKind::Reified => acc,
        }
    }

    fn on_tfun(&self, acc: ValidationState, r: &R, _ft: &DeclFunType) -> ValidationState {
        self.invalid(acc, r, "a function type")
    }

    fn on_typeconst(
        &self,
        acc: ValidationState,
        _class: &cls::T,
        typeconst: &TypeconstType,
    ) -> ValidationState {
        match acc.reification {
            Reification::TypeStructure => acc,
            Reification::Unresolved | Reification::Resolved => match &typeconst.kind {
                Typeconst::TCConcrete(ConcreteTypeconst { ty: tc_type }) => {
                    self.on_type(acc, tc_type)
                }
                Typeconst::TCAbstract(AbstractTypeconst {
                    as_constraint: _,
                    super_constraint: _,
                    default: atc_default,
                }) => match &typeconst.reifiable {
                    None => {
                        let r = R::witness_from_decl(typeconst.name.pos().clone());
                        let kind = "an abstract type constant without the __Reifiable attribute";
                        self.invalid(acc, &r, kind)
                    }
                    Some(_) => atc_default.iter().fold(acc, |acc, ty| self.on_type(acc, ty)),
                },
            },
        }
    }

    fn on_taccess(
        &self,
        acc: ValidationState,
        r: &R,
        ta: &d::TaccessType<R, DeclTy>,
    ) -> ValidationState {
        let root = &ta.ty;
        let acc = match acc.reification {
            Reification::Unresolved => match root.node_ref() {
                d::Ty_::Tthis => ValidationState {
                    reification: Reification::Resolved,
                    ..acc
                },
                _ => self.on_type(acc, root),
            },
            Reification::TypeStructure | Reification::Resolved => acc,
        };
        inherited::on_taccess(self, acc, r, ta)
    }

    fn on_tthis(&self, acc: ValidationState, r: &R) -> ValidationState {
        match &acc.class_from_taccess_lhs {
            Some(final_class) if cls::final_(final_class) => {
                // in a final class, `this` is the lexical class, since there are no subclasses
                let has_tparams = !cls::tparams(final_class).is_empty();
                if has_tparams {
                    // Ban because:
                    //  `final class C<T> { type Tc = this }` is a way of expressing the same thing as
                    //  `class C<T> { type Tc = C<T> }` which is banned (probably due to type constants being reified)
                    self.invalid(
                        acc,
                        r,
                        "the late static bound `this` type of a class with type parameters",
                    )
                } else {
                    acc
                }
            }
            Some(_non_final_class) => self.invalid(
                acc,
                r,
                "the late static bound `this` type of a non-final class",
            ),
            None => self.invalid(acc, r, "the late static bound `this` type"),
        }
    }

    fn on_trefinement(
        &self,
        acc: ValidationState,
        r: &R,
        _ty: &DeclTy,
        _rs: &DeclClassRefinement,
    ) -> ValidationState {
        self.invalid(acc, r, "type refinement")
    }
}
