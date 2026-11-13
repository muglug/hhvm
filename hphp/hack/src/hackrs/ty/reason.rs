// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

use std::fmt::Debug;
use std::hash::Hash;
use std::sync::Arc;
use std::sync::LazyLock;

use eq_modulo_pos::EqModuloPos;
use hcons::Conser;
use oxidized::ast::FunKind;
pub use oxidized::typing_reason::ArgPosition;
pub use oxidized::typing_reason::BlameSource;
pub use oxidized::typing_reason::PessimiseReason;
use pos::BPos;
use pos::NPos;
use pos::Pos;
use pos::Symbol;
use pos::ToOxidized;
use pos::TypeName;
use serde::Deserialize;
use serde::Serialize;
use serde::de::DeserializeOwned;

use crate::decl;
use crate::visitor::Walkable;

pub trait Reason:
    Eq
    + EqModuloPos
    + Hash
    + Clone
    + Walkable<Self>
    + std::fmt::Debug
    + Send
    + Sync
    + Serialize
    + DeserializeOwned
    + for<'a> From<oxidized::typing_reason::T_>
    + ToOxidized<Output = oxidized::typing_reason::T_>
    + 'static
{
    /// Position type.
    type Pos: Pos + Send + Sync + 'static;

    /// Make a new instance. If the implementing Reason is stateful,
    /// it will call cons() to obtain the ReasonImpl to construct the instance.
    fn mk(cons: impl FnOnce() -> ReasonImpl<Self, Self::Pos>) -> Self;

    fn none() -> Self;

    fn witness_from_decl(pos: Self::Pos) -> Self {
        Self::mk(|| ReasonImpl::FromWitnessDecl(WitnessDecl::WitnessFromDecl(pos)))
    }

    fn hint(pos: Self::Pos) -> Self {
        Self::mk(|| ReasonImpl::FromWitnessDecl(WitnessDecl::Hint(pos)))
    }

    fn instantiate(r1: Self, ty_name: TypeName, r2: Self) -> Self {
        Self::mk(|| ReasonImpl::Instantiate(r1, ty_name, r2))
    }

    fn class_class(pos: Self::Pos, ty_name: TypeName) -> Self {
        Self::mk(|| ReasonImpl::FromWitnessDecl(WitnessDecl::ClassClass(pos, ty_name)))
    }

    fn pos(&self) -> &Self::Pos;

    fn decl_ty_conser() -> &'static Conser<decl::Ty_<Self>>;

    fn from_oxidized(reason: oxidized::typing_reason::T_) -> Self {
        Self::mk(|| {
            use ReasonImpl as RI;
            use oxidized::typing_reason::T_ as OR;
            use oxidized::typing_reason::WitnessDecl as WD;

            match reason {
                OR::NoReason => RI::NoReason,
                OR::FromWitnessDecl(WD::WitnessFromDecl(pos)) => {
                    RI::FromWitnessDecl(WitnessDecl::WitnessFromDecl(pos.into()))
                }

                OR::FromWitnessDecl(WD::Hint(pos)) => {
                    RI::FromWitnessDecl(WitnessDecl::Hint(pos.into()))
                }

                OR::FromWitnessDecl(WD::ClassClass(pos, s)) => RI::FromWitnessDecl(
                    WitnessDecl::ClassClass(pos.into(), TypeName(Symbol::new(s))),
                ),

                OR::FromWitnessDecl(WD::VarParamFromDecl(pos)) => {
                    RI::FromWitnessDecl(WitnessDecl::VarParamFromDecl(pos.into()))
                }

                OR::FromWitnessDecl(WD::TupleFromSplat(pos)) => {
                    RI::FromWitnessDecl(WitnessDecl::TupleFromSplat(pos.into()))
                }

                OR::FromWitnessDecl(WD::VecOrDictKey(pos)) => {
                    RI::FromWitnessDecl(WitnessDecl::VecOrDictKey(pos.into()))
                }

                OR::FromWitnessDecl(WD::RetFunKindFromDecl(pos, fun_kind)) => {
                    RI::FromWitnessDecl(WitnessDecl::RetFunKindFromDecl(pos.into(), fun_kind))
                }

                OR::FromWitnessDecl(witness) => {
                    use WitnessDecl as W;
                    let sym = |s: String| Symbol::new(s);
                    RI::FromWitnessDecl(match witness {
                        // Handled above.
                        WD::WitnessFromDecl(p) => W::WitnessFromDecl(p.into()),
                        WD::Hint(p) => W::Hint(p.into()),
                        WD::ClassClass(p, s) => W::ClassClass(p.into(), TypeName(sym(s))),
                        WD::VarParamFromDecl(p) => W::VarParamFromDecl(p.into()),
                        WD::TupleFromSplat(p) => W::TupleFromSplat(p.into()),
                        WD::VecOrDictKey(p) => W::VecOrDictKey(p.into()),
                        WD::RetFunKindFromDecl(p, k) => W::RetFunKindFromDecl(p.into(), k),
                        WD::IdxVectorFromDecl(p) => W::IdxVectorFromDecl(p.into()),
                        WD::IdxStringFromDecl(p) => W::IdxStringFromDecl(p.into()),
                        WD::InoutParam(p) => W::InoutParam(p.into()),
                        WD::TconstNoCstr((p, s)) => W::TconstNoCstr((p.into(), sym(s))),
                        WD::VarrayOrDarrayKey(p) => W::VarrayOrDarrayKey(p.into()),
                        WD::MissingOptionalField(p, s) => W::MissingOptionalField(p.into(), sym(s)),
                        WD::ImplicitUpperBound(p, s) => W::ImplicitUpperBound(p.into(), sym(s)),
                        WD::GlobalTypeVariableGenerics(p, a, b) => {
                            W::GlobalTypeVariableGenerics(p.into(), sym(a), sym(b))
                        }
                        WD::SolveFail(p) => W::SolveFail(p.into()),
                        WD::CstrOnGenerics(p, (q, s)) => {
                            W::CstrOnGenerics(p.into(), (q.into(), sym(s)))
                        }
                        WD::Enforceable(p) => W::Enforceable(p.into()),
                        WD::GlobalClassProp(p) => W::GlobalClassProp(p.into()),
                        WD::GlobalFunParam(p) => W::GlobalFunParam(p.into()),
                        WD::GlobalFunRet(p) => W::GlobalFunRet(p.into()),
                        WD::DefaultCapability(p) => W::DefaultCapability(p.into()),
                        WD::SupportDynamicType(p) => W::SupportDynamicType(p.into()),
                        WD::PessimisedInout(p) => W::PessimisedInout(p.into()),
                        WD::PessimisedReturn(p, r) => W::PessimisedReturn(p.into(), r),
                        WD::PessimisedProp(p, r) => W::PessimisedProp(p.into(), r),
                        WD::PessimisedThis(p) => W::PessimisedThis(p.into()),
                        WD::IllegalRecursiveType(p, s) => W::IllegalRecursiveType(p.into(), sym(s)),
                        WD::SupportDynamicTypeAssume(p) => W::SupportDynamicTypeAssume(p.into()),
                        WD::PolymorphicTypeParam(p, a, b, n) => {
                            W::PolymorphicTypeParam(p.into(), sym(a), sym(b), n)
                        }
                        WD::EnforcedType(p) => W::EnforcedType(p.into()),
                    })
                }

                OR::Instantiate {
                    type__: r1,
                    var_name: sym,
                    var: r2,
                } => RI::Instantiate((*r1).into(), TypeName(Symbol::new(sym)), (*r2).into()),
                _ => {
                    panic!("Error occurred: {:#?}", reason)
                }
            }
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq, EqModuloPos, Hash, Serialize, Deserialize)]
pub struct Blame<P>(pub P, pub BlameSource);

#[derive(Debug, Clone, PartialEq, Eq, EqModuloPos, Hash, Serialize, Deserialize)]
pub enum ExprDepTypeReason {
    ERexpr(isize),
    ERstatic,
    ERclass(Symbol),
    ERparent(Symbol),
    ERself(Symbol),
    ERpu(Symbol),
}

#[derive(Debug, Clone, PartialEq, Eq, EqModuloPos, Hash, Serialize, Deserialize)]
pub enum WitnessDecl<P> {
    WitnessFromDecl(P),
    IdxVectorFromDecl(P),
    IdxStringFromDecl(P),
    Hint(P),
    ClassClass(P, TypeName),
    VarParamFromDecl(P),
    TupleFromSplat(P),
    VecOrDictKey(P),
    RetFunKindFromDecl(P, FunKind),
    InoutParam(P),
    TconstNoCstr((P, Symbol)),
    VarrayOrDarrayKey(P),
    MissingOptionalField(P, Symbol),
    ImplicitUpperBound(P, Symbol),
    GlobalTypeVariableGenerics(P, Symbol, Symbol),
    SolveFail(P),
    CstrOnGenerics(P, (P, Symbol)),
    Enforceable(P),
    GlobalClassProp(P),
    GlobalFunParam(P),
    GlobalFunRet(P),
    DefaultCapability(P),
    SupportDynamicType(P),
    PessimisedInout(P),
    PessimisedReturn(P, PessimiseReason),
    PessimisedProp(P, PessimiseReason),
    PessimisedThis(P),
    IllegalRecursiveType(P, Symbol),
    SupportDynamicTypeAssume(P),
    PolymorphicTypeParam(P, Symbol, Symbol, isize),
    EnforcedType(P),
}

#[derive(Debug, Clone, PartialEq, Eq, EqModuloPos, Hash, Serialize, Deserialize)]
pub enum ReasonImpl<R, P> {
    FromWitnessDecl(WitnessDecl<P>),
    Instantiate(R, TypeName, R),
    NoReason,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct BReason(Arc<ReasonImpl<BReason, BPos>>);

impl Reason for BReason {
    type Pos = BPos;

    fn mk(cons: impl FnOnce() -> ReasonImpl<Self, Self::Pos>) -> Self {
        let x = cons();
        Self(Arc::new(x))
    }

    fn none() -> Self {
        BReason(Arc::new(ReasonImpl::NoReason))
    }

    fn pos(&self) -> &BPos {
        use ReasonImpl::*;
        use WitnessDecl::*;
        match &*self.0 {
            NoReason => {
                static NONE: LazyLock<BPos> = LazyLock::new(BPos::none);
                &NONE
            }
            FromWitnessDecl(witness) => match witness {
                WitnessFromDecl(p)
                | IdxVectorFromDecl(p)
                | IdxStringFromDecl(p)
                | Hint(p)
                | ClassClass(p, _)
                | VarParamFromDecl(p)
                | TupleFromSplat(p)
                | VecOrDictKey(p)
                | RetFunKindFromDecl(p, _)
                | InoutParam(p)
                | TconstNoCstr((p, _))
                | VarrayOrDarrayKey(p)
                | MissingOptionalField(p, _)
                | ImplicitUpperBound(p, _)
                | GlobalTypeVariableGenerics(p, _, _)
                | SolveFail(p)
                | CstrOnGenerics(p, _)
                | Enforceable(p)
                | GlobalClassProp(p)
                | GlobalFunParam(p)
                | GlobalFunRet(p)
                | DefaultCapability(p)
                | SupportDynamicType(p)
                | PessimisedInout(p)
                | PessimisedReturn(p, _)
                | PessimisedProp(p, _)
                | PessimisedThis(p)
                | IllegalRecursiveType(p, _)
                | SupportDynamicTypeAssume(p)
                | PolymorphicTypeParam(p, _, _, _)
                | EnforcedType(p) => p,
            },
            // As `Typing_reason.to_pos`: the position of the type substituted in.
            Instantiate(r, _, _) => r.pos(),
        }
    }

    #[inline]
    fn decl_ty_conser() -> &'static Conser<decl::Ty_<BReason>> {
        static CONSER: LazyLock<Conser<decl::Ty_<BReason>>> = LazyLock::new(Conser::new);
        &CONSER
    }
}

impl BReason {
    /// What the reason says, beyond its position.
    pub fn as_impl(&self) -> &ReasonImpl<BReason, BPos> {
        &self.0
    }
}

impl Walkable<BReason> for BReason {}

impl From<oxidized::typing_reason::T_> for BReason {
    fn from(reason: oxidized::typing_reason::T_) -> Self {
        Self::from_oxidized(reason)
    }
}

impl ToOxidized for BReason {
    type Output = oxidized::typing_reason::Reason;

    fn to_oxidized(self) -> Self::Output {
        use WitnessDecl as W;
        use oxidized::typing_reason::T_ as OR;
        use oxidized::typing_reason::WitnessDecl as WD;
        let pos = |p: &BPos| p.clone().to_oxidized();
        let string = |s: &Symbol| s.as_str().to_string();
        match &*self.0 {
            ReasonImpl::NoReason => OR::NoReason,
            ReasonImpl::Instantiate(r1, name, r2) => OR::Instantiate {
                type__: Box::new(r1.clone().to_oxidized()),
                var_name: name.as_str().to_string(),
                var: Box::new(r2.clone().to_oxidized()),
            },
            ReasonImpl::FromWitnessDecl(witness) => OR::FromWitnessDecl(match witness {
                W::WitnessFromDecl(p) => WD::WitnessFromDecl(pos(p)),
                W::IdxVectorFromDecl(p) => WD::IdxVectorFromDecl(pos(p)),
                W::IdxStringFromDecl(p) => WD::IdxStringFromDecl(pos(p)),
                W::Hint(p) => WD::Hint(pos(p)),
                W::ClassClass(p, name) => WD::ClassClass(pos(p), name.as_str().to_string()),
                W::VarParamFromDecl(p) => WD::VarParamFromDecl(pos(p)),
                W::TupleFromSplat(p) => WD::TupleFromSplat(pos(p)),
                W::VecOrDictKey(p) => WD::VecOrDictKey(pos(p)),
                W::RetFunKindFromDecl(p, k) => WD::RetFunKindFromDecl(pos(p), *k),
                W::InoutParam(p) => WD::InoutParam(pos(p)),
                W::TconstNoCstr((p, s)) => WD::TconstNoCstr((pos(p), string(s))),
                W::VarrayOrDarrayKey(p) => WD::VarrayOrDarrayKey(pos(p)),
                W::MissingOptionalField(p, s) => WD::MissingOptionalField(pos(p), string(s)),
                W::ImplicitUpperBound(p, s) => WD::ImplicitUpperBound(pos(p), string(s)),
                W::GlobalTypeVariableGenerics(p, a, b) => {
                    WD::GlobalTypeVariableGenerics(pos(p), string(a), string(b))
                }
                W::SolveFail(p) => WD::SolveFail(pos(p)),
                W::CstrOnGenerics(p, (q, s)) => WD::CstrOnGenerics(pos(p), (pos(q), string(s))),
                W::Enforceable(p) => WD::Enforceable(pos(p)),
                W::GlobalClassProp(p) => WD::GlobalClassProp(pos(p)),
                W::GlobalFunParam(p) => WD::GlobalFunParam(pos(p)),
                W::GlobalFunRet(p) => WD::GlobalFunRet(pos(p)),
                W::DefaultCapability(p) => WD::DefaultCapability(pos(p)),
                W::SupportDynamicType(p) => WD::SupportDynamicType(pos(p)),
                W::PessimisedInout(p) => WD::PessimisedInout(pos(p)),
                W::PessimisedReturn(p, r) => WD::PessimisedReturn(pos(p), *r),
                W::PessimisedProp(p, r) => WD::PessimisedProp(pos(p), *r),
                W::PessimisedThis(p) => WD::PessimisedThis(pos(p)),
                W::IllegalRecursiveType(p, s) => WD::IllegalRecursiveType(pos(p), string(s)),
                W::SupportDynamicTypeAssume(p) => WD::SupportDynamicTypeAssume(pos(p)),
                W::PolymorphicTypeParam(p, a, b, n) => {
                    WD::PolymorphicTypeParam(pos(p), string(a), string(b), *n)
                }
                W::EnforcedType(p) => WD::EnforcedType(pos(p)),
            }),
        }
    }
}

impl EqModuloPos for BReason {
    fn eq_modulo_pos(&self, rhs: &Self) -> bool {
        self.0.eq_modulo_pos(&rhs.0)
    }
    fn eq_modulo_pos_and_reason(&self, _rhs: &Self) -> bool {
        true
    }
}

/// A stateless sentinal Reason.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct NReason;

impl Reason for NReason {
    type Pos = NPos;

    fn mk(_cons: impl FnOnce() -> ReasonImpl<Self, Self::Pos>) -> Self {
        NReason
    }

    fn none() -> Self {
        NReason
    }

    fn pos(&self) -> &NPos {
        &NPos
    }

    #[inline]
    fn decl_ty_conser() -> &'static Conser<decl::Ty_<NReason>> {
        static CONSER: LazyLock<Conser<decl::Ty_<NReason>>> = LazyLock::new(Conser::new);
        &CONSER
    }
}

impl Walkable<NReason> for NReason {}

impl From<oxidized::typing_reason::T_> for NReason {
    fn from(reason: oxidized::typing_reason::T_) -> Self {
        Self::from_oxidized(reason)
    }
}

impl ToOxidized for NReason {
    type Output = oxidized::typing_reason::Reason;

    fn to_oxidized(self) -> Self::Output {
        oxidized::typing_reason::Reason::NoReason
    }
}

impl EqModuloPos for NReason {
    fn eq_modulo_pos(&self, _rhs: &Self) -> bool {
        true
    }
    fn eq_modulo_pos_and_reason(&self, _rhs: &Self) -> bool {
        true
    }
}
