// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_enforceable_hint.ml`. See `hh/PORTING.md`.
//!
//! The object `validator` (which inherits `Type_validator.type_validator`) is
//! the type [`Validator`], which implements
//! [`TypeValidator`](crate::type_validator::TypeValidator); `validator ()` is
//! the value. The methods the object adds (`is_wildcard`,
//! `check_for_wildcards`, `check_generic`) are inherent methods of
//! [`Validator`].

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::message::Message;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use pos::Positioned;
use pos::TypeName;
use ty::decl::ty as d;
use ty::reason::Reason as _;

use crate::ctx::R;
use crate::decl_entry;
/// `module Cls = Folded_class`
use crate::folded_class as cls;
use crate::type_validator::TypeValidator;
use crate::type_validator::ValidationState;
use crate::type_validator::inherited;
use crate::typing_defs::*;
/// `module Env = Typing_env`
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_error;

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

/// `Typing_defs.is_nothing`, on a declared type.
fn is_nothing(t: &DeclTy) -> bool {
    match t.node_ref() {
        d::Ty_::Tunion(tyl) if tyl.is_empty() => true,
        _ => false,
    }
}

impl TypeValidator for Validator {
    /// Only comes about because naming has reported an error and left Hany
    fn on_tany(&self, acc: ValidationState, _r: &R) -> ValidationState {
        acc
    }

    fn on_tprim(&self, acc: ValidationState, r: &R, prim: aast::Tprim) -> ValidationState {
        match prim {
            aast::Tprim::Tvoid => self.invalid(acc, r, "the `void` type"),
            aast::Tprim::Tnoreturn => self.invalid(acc, r, "the `noreturn` type"),
            _ => acc,
        }
    }

    fn on_tfun(&self, acc: ValidationState, r: &R, _fun_type: &DeclFunType) -> ValidationState {
        self.invalid(acc, r, "a function type")
    }

    fn on_tvar(&self, acc: ValidationState, r: &R, _id: isize) -> ValidationState {
        self.invalid(acc, r, "an unknown type")
    }

    fn on_typeconst(
        &self,
        acc: ValidationState,
        class_: &cls::T,
        typeconst: &TypeconstType,
    ) -> ValidationState {
        match &typeconst.kind {
            Typeconst::TCConcrete(_) => inherited::on_typeconst(self, acc, class_, typeconst),
            Typeconst::TCAbstract(_)
                if
                // get_typeconst_enforceability should always return Some here, since we
                // know the typeconst exists (else we wouldn't be in this method).
                // But since we have to map it to a bool anyway, we just use
                // Option.value_map.
                cls::get_typeconst_enforceability(class_, typeconst.name.id_ref().as_str())
                    .map_or(false, |(_, b)| b) =>
            {
                // We don't need to look further into the abstract type constant, as it's guaranteed to be enforceable.
                // In particular, it doesn't matter if its as-bound isn't enforceable
                acc
            }
            Typeconst::TCAbstract(_) => {
                let pos = typeconst.name.pos();
                let tconst = typeconst.name.id_ref().as_str();
                let r = R::witness_from_decl(pos.clone());
                self.invalid(
                    acc,
                    &r,
                    &format!(
                        "the abstract type constant {} because it is not marked `<<__Enforceable>>`",
                        tconst
                    ),
                )
            }
        }
    }

    fn on_tgeneric(&self, acc: ValidationState, r: &R, name: &str) -> ValidationState {
        self.check_generic(acc, r, name)
    }

    fn on_newtype(
        &self,
        acc: ValidationState,
        r: &R,
        sid: &Positioned<TypeName, DeclPos>,
        _tyl: &[DeclTy],
        as_cstr: &DeclTy,
        _super_cstr: &DeclTy,
        _ty: &DeclTy,
    ) -> ValidationState {
        if sid.id_ref().as_str() == sn::classes::SUPPORT_DYN {
            // `with_reason as_cstr r`
            self.on_type(acc, &DeclTy::new(r.clone(), as_cstr.node_ref().clone()))
        } else {
            self.invalid(acc, r, "a `newtype`")
        }
    }

    fn on_tlike(&self, acc: ValidationState, _r: &R, ty: &DeclTy) -> ValidationState {
        self.on_type(acc, ty)
    }

    fn on_class(
        &self,
        acc: ValidationState,
        r: &R,
        cls: &Positioned<TypeName, DeclPos>,
        tyl: &[DeclTy],
    ) -> ValidationState {
        match env::get_class(&acc.env, cls.id_ref().as_str()) {
            decl_entry::T::Found(tc) => match cls::kind(&tc) {
                oxidized::ast_defs::ClassishKind::Ctrait => self.invalid(acc, r, "a trait name"),
                _ => {
                    let tparams = cls::tparams(&tc);
                    match tyl {
                        [] => acc,
                        // this case should really be handled by the fold2,
                        // but we still allow class hints without args in certain places
                        targs => {
                            // List.fold2 checks the lengths before it folds.
                            if targs.len() != tparams.len() {
                                // arity error elsewhere
                                acc
                            } else {
                                let mut acc = acc;
                                for (targ, tparam) in targs.iter().zip(tparams.iter()) {
                                    let inside_reified_class_generic_position =
                                        acc.inside_reified_class_generic_position;
                                    acc = if self.is_wildcard(targ) {
                                        if inside_reified_class_generic_position {
                                            self.invalid(
                                                acc,
                                                r,
                                                "a reified type containing a wildcard (`_`)",
                                            )
                                        } else {
                                            acc
                                        }
                                    } else if tparam.reified == aast::ReifyKind::Reified {
                                        let old_inside_reified_class_generic_position =
                                            inside_reified_class_generic_position;
                                        let acc = self.on_type(
                                            ValidationState {
                                                inside_reified_class_generic_position: true,
                                                ..acc
                                            },
                                            targ,
                                        );
                                        ValidationState {
                                            inside_reified_class_generic_position:
                                                old_inside_reified_class_generic_position,
                                            ..acc
                                        }
                                    } else if inside_reified_class_generic_position {
                                        self.on_type(acc, targ)
                                    } else {
                                        let error_message =
                                            "a type with an erased generic type argument";
                                        self.invalid(acc, r, error_message)
                                    }
                                }
                                acc
                            }
                        }
                    }
                }
            },
            decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => acc,
        }
    }

    fn on_alias(
        &self,
        acc: ValidationState,
        r: &R,
        _id: &Positioned<TypeName, DeclPos>,
        tyl: &[DeclTy],
        ty: &DeclTy,
    ) -> ValidationState {
        if tyl.iter().filter(|ty| !self.is_wildcard(ty)).count() == 0 {
            self.on_type(acc, ty)
        } else {
            self.invalid(
                acc,
                r,
                "a type with generics, because generics are erased at runtime",
            )
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

    fn on_tunion(&self, acc: ValidationState, r: &R, tyl: &[DeclTy]) -> ValidationState {
        match tyl {
            [] => self.invalid(acc, r, "the `nothing` type"),
            _ => inherited::on_tunion(self, acc, r, tyl),
        }
    }

    fn on_tintersection(&self, acc: ValidationState, r: &R, _tyl: &[DeclTy]) -> ValidationState {
        self.invalid(
            acc,
            r,
            "an intersection type, which is restricted to coeffects",
        )
    }

    fn on_ttuple(&self, acc: ValidationState, r: &R, t: &d::TupleType<R>) -> ValidationState {
        let d::TupleType(t_required, t_optional, t_extra) = t;
        let acc = t_required.iter().fold(acc, |acc, ty| self.on_type(acc, ty));
        match t_extra {
            d::TupleExtra::Tvariadic(t_variadic) => {
                // HHVM doesn't currently support is/as on open tuples, so let's reject it in Hack
                if !is_nothing(t_variadic) || !t_optional.is_empty() {
                    self.invalid(acc, r, "a tuple type with optional or variadic elements")
                } else {
                    self.check_for_wildcards(acc, t_required, "tuple")
                }
            }
            d::TupleExtra::Tsplat(_) => {
                // HHVM doesn't currently support is/as on type splats, so let's reject it in Hack
                self.invalid(acc, r, "a tuple type with a splat element")
            }
        }
    }

    fn on_tshape(&self, acc: ValidationState, r: &R, st: &d::ShapeType<R>) -> ValidationState {
        match st {
            d::ShapeType::Splat(_) => {
                // Reject is/as on shape splats. HHVM's is/as matcher
                // (runtime/base/type-structure-helpers.cpp) only understands a
                // *resolved* shape type structure: it reads the [fields] dict and has
                // no awareness of a splat's [splat_elem_types]. To accept it, HHVM
                // would first have to resolve the splat into a plain shape via the
                // rightmost-wins merge ([TypeStructure::mergeResolvedShapeSplat]) and
                // match against that, and reject any operand it cannot resolve at
                // runtime (e.g. an erased generic, whose type structure is not
                // available). Until that machinery exists we forbid it statically.
                self.invalid(acc, r, "a shape type with a splat element")
            }
            d::ShapeType::Simple(d::ShapeTypeSimple(s_unknown_value, fdm)) => {
                // `TShapeMap.values` is `Wrapped_map.values`, `fold (fun _ v acc ->
                // v :: acc) m []`: in decreasing order of the names of the fields
                // (and the first invalid field is the one reported).
                let mut fields: Vec<_> = fdm.iter().collect();
                fields.sort_by(|a, b| decl_tshape_field_name_compare(b.0, a.0));
                let tyl: Vec<DeclTy> = fields.into_iter().map(|(_, s)| s.ty.clone()).collect();
                let acc = tyl.iter().fold(acc, |acc, ty| self.on_type(acc, ty));
                fn is_nothing_or_mixed(ty: &DeclTy) -> bool {
                    match ty.node_ref() {
                        d::Ty_::Tmixed => true,
                        d::Ty_::Tunion(tyl) if tyl.is_empty() => true,
                        d::Ty_::Tapply(id_and_tyl)
                            if id_and_tyl.1.len() == 1
                                && id_and_tyl.0.id_ref().as_str() == sn::classes::SUPPORT_DYN =>
                        {
                            is_nothing_or_mixed(&id_and_tyl.1[0])
                        }
                        _ => false,
                    }
                }
                // HHVM doesn't currently support is/as on typed open shapes, so let's reject it in Hack
                if is_nothing_or_mixed(s_unknown_value) {
                    self.check_for_wildcards(acc, &tyl, "shape")
                } else {
                    self.invalid(
                        acc,
                        s_unknown_value.reason(),
                        "a shape type with a typed variadic element",
                    )
                }
            }
        }
    }

    fn on_tclass_ptr(&self, acc: ValidationState, r: &R, _ty: &DeclTy) -> ValidationState {
        // TODO(T199611023) allow when we enforce inner type
        self.invalid(acc, r, "a class pointer type")
    }
}

impl Validator {
    pub fn is_wildcard(&self, ty: &DeclTy) -> bool {
        match ty.node_ref() {
            d::Ty_::Twildcard => true,
            _ => false,
        }
    }

    pub fn check_for_wildcards(
        &self,
        acc: ValidationState,
        tyl: &[DeclTy],
        s: &str,
    ) -> ValidationState {
        let tyl: Vec<&DeclTy> = tyl.iter().filter(|ty| self.is_wildcard(ty)).collect();
        match tyl.as_slice() {
            [] => acc,
            tyl => self.invalid_list(
                acc,
                tyl.iter()
                    .map(|ty| {
                        (
                            ty.reason().clone(),
                            format!("_ in a {} (use `mixed` instead)", s),
                        )
                    })
                    .collect(),
            ),
        }
    }

    pub fn check_generic(&self, acc: ValidationState, r: &R, name: &str) -> ValidationState {
        // No need to look at type arguments of generic var, as higher-kinded type params
        // cannot be enforcable
        // TODO(T70069116) implement enforcability check
        // (OCaml evaluates the components of the tuple from right to left.)
        let enforceable = env::get_enforceable(&acc.env, name);
        let reified = env::get_reified(&acc.env, name);
        match (reified, enforceable) {
            (aast::ReifyKind::Erased, _) => self.invalid(acc, r, "an erased generic type parameter"),
            (aast::ReifyKind::SoftReified, _) => {
                self.invalid(acc, r, "a soft reified generic type parameter")
            }
            (aast::ReifyKind::Reified, false) => {
                // If a reified generic is an argument to a reified class it does not
                // need to be enforceable
                if acc.inside_reified_class_generic_position {
                    acc
                } else {
                    self.invalid(
                        acc,
                        r,
                        "a reified type parameter that is not marked `<<__Enforceable>>`",
                    )
                }
            }
            (aast::ReifyKind::Reified, true) => acc,
        }
    }
}

/// `validator#validate_hint ?reification:None`
pub fn validate_hint(
    env: &Env,
    hint: &aast::Hint,
    emit_error: impl FnMut(Pos, typing_error::Lazy<Vec<Message<PosOrDecl>>>),
) {
    validator().validate_hint(env, hint, None, emit_error)
}

/// `validator#validate_type ?reification:None`
pub fn validate_type(
    env: &Env,
    use_pos: Pos,
    ty: &DeclTy,
    emit_error: impl FnMut(Pos, typing_error::Lazy<Vec<Message<PosOrDecl>>>),
) {
    validator().validate_type(env, use_pos, ty, None, emit_error)
}

/// `is this` and `as this` check only the class at runtime, so in a generic
/// class they would refine to an instantiation that was never checked.
pub fn check_this_refinement_in_generic_class(env: &Env, hint: &aast::Hint) {
    let aast::Hint(pos, _) = hint;
    match env::get_self_class(env) {
        decl_entry::T::Found(cls) if !cls::tparams(&cls).is_empty() => {
            struct MentionsThis;
            impl crate::type_visitor::DeclTypeVisitor<bool> for MentionsThis {
                fn on_tthis(&mut self, _: bool, _: &R) -> bool {
                    true
                }

                // `this::T` names a type constant, not the class
                fn on_taccess(
                    &mut self,
                    found: bool,
                    _: &R,
                    _: &d::TaccessType<R, DeclTy>,
                ) -> bool {
                    found
                }

                // (`method! on_type found ty = found || parent#on_type found
                // ty` only stops early: every other method returns what it
                // is given.)
            }
            use crate::type_visitor::DeclTypeVisitor as _;
            if MentionsThis.on_type(false, &crate::decl_hint::hint(&env.decl_env, hint)) {
                crate::typing_error_utils::add_typing_error(
                    &typing_error::primary(
                        typing_error::primary::T::ThisRefinementInGenericClass {
                            pos: pos.clone(),
                            class_name: cls::name(&cls),
                            decl_pos: cls::pos(&cls),
                        },
                    ),
                    env,
                )
            }
        }
        _ => {}
    }
}
