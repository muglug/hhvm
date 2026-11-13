// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_make_type.ml`. See `hh/PORTING.md`.
//!
//! The functions make localized types ([`Ty`], see `typing_defs_core.rs`),
//! except the ones that OCaml can only use on declared types, which make
//! `hackrs` types ([`DeclTy`]): [`is_dynamic_or_like_or_mixed`], [`like`],
//! [`apply`], [`decl_string`] and [`default_capability_decl`]. The functions
//! that OCaml can use in both phases (`mixed`, `nullable`, `void`, `union`,
//! ...) are here for the localized phase only; `ty::decl::Ty` has its own
//! constructors.

use naming_special_names_rust as sn;
use oxidized::aast_defs::Sid;
use oxidized::ast_defs;
use oxidized::ast_defs::Tprim;
use oxidized::nast;
use oxidized::pos_or_decl::PosOrDecl;
use oxidized::typing_defs_flags::FunParamFlags;
use oxidized::typing_defs_flags::FunTypeFlags;
use pos::Positioned;
use pos::TypeName;
use ty::reason::Reason as _;

use crate::typing_defs::*;
use crate::typing_defs_constraints::*;
/// `module Reason = Typing_reason`
use crate::typing_reason as reason;
use crate::typing_reason::T as Reason;

/// The names of `Naming_special_names` that `naming_special_names_rust` does
/// not have (or has under another module), with the OCaml values.
mod missing_special_names {
    /// `Classes.cString`
    pub const C_STRING: &str = "\\HH\\string";
    /// `Classes.cFunctionRef`
    pub const C_FUNCTION_REF: &str = "\\HH\\FunctionRef";

    /// `Capabilities`
    pub mod capabilities {
        pub const WRITE_PROPERTY: &str = "\\HH\\Capabilities\\WriteProperty";
        pub const ACCESS_GLOBALS: &str = "\\HH\\Capabilities\\AccessGlobals";
        pub const RX_LOCAL: &str = "\\HH\\Capabilities\\RxLocal";
        pub const SYSTEM_LOCAL: &str = "\\HH\\Capabilities\\SystemLocal";
        pub const IMPLICIT_POLICY_LOCAL: &str = "\\HH\\Capabilities\\ImplicitPolicyLocal";
        pub const IO: &str = "\\HH\\Capabilities\\IO";
    }
}

/// `Typing_defs_flags.Fun.make`
fn fun_flags_make(
    kind: ast_defs::FunKind,
    return_disposable: bool,
    returns_readonly: bool,
    readonly_this: bool,
    support_dynamic_type: bool,
    is_memoized: bool,
    variadic: bool,
    named_variadic: bool,
) -> FunTypeFlags {
    let mut flags = match kind {
        ast_defs::FunKind::FSync => FunTypeFlags::empty(),
        ast_defs::FunKind::FAsync => FunTypeFlags::ASYNC,
        ast_defs::FunKind::FGenerator => FunTypeFlags::GENERATOR,
        ast_defs::FunKind::FAsyncGenerator => FunTypeFlags::ASYNC | FunTypeFlags::GENERATOR,
    };
    flags.set(FunTypeFlags::RETURN_DISPOSABLE, return_disposable);
    flags.set(FunTypeFlags::RETURNS_READONLY, returns_readonly);
    flags.set(FunTypeFlags::READONLY_THIS, readonly_this);
    flags.set(FunTypeFlags::SUPPORT_DYNAMIC_TYPE, support_dynamic_type);
    flags.set(FunTypeFlags::IS_MEMOIZED, is_memoized);
    flags.set(FunTypeFlags::VARIADIC, variadic);
    flags.set(FunTypeFlags::NAMED_VARIADIC, named_variadic);
    flags
}

/// `Typing_defs_flags.FunParam.make`
fn fun_param_flags_make(
    inout: bool,
    accept_disposable: bool,
    is_optional: bool,
    readonly: bool,
    ignore_readonly_error: bool,
    splat: bool,
    named: bool,
) -> FunParamFlags {
    let mut flags = FunParamFlags::empty();
    flags.set(FunParamFlags::INOUT, inout);
    flags.set(FunParamFlags::ACCEPT_DISPOSABLE, accept_disposable);
    flags.set(FunParamFlags::IS_OPTIONAL, is_optional);
    flags.set(FunParamFlags::READONLY, readonly);
    flags.set(FunParamFlags::IGNORE_READONLY_ERROR, ignore_readonly_error);
    flags.set(FunParamFlags::SPLAT, splat);
    flags.set(FunParamFlags::NAMED, named);
    flags
}

pub fn class_type(r: Reason, name: String, tyl: Vec<Ty>) -> Ty {
    let pos = reason::to_pos(&r);
    mk((r, Ty_::Tclass((pos, name), nonexact(), tyl)))
}

pub fn prim_type(r: Reason, t: Tprim) -> Ty {
    mk((r, Ty_::Tprim(t)))
}

/// Make a negation type
pub fn neg(r: Reason, neg_t: TypePredicate) -> Ty {
    match &neg_t.1 {
        // Represent the negation of Tnull as Tnonnull, instead of Tneg Tnull
        TypePredicate_::IsTag(TypeTag::NullTag) => mk((r, Ty_::Tnonnull)),
        // Represent the negation of IsNot(NullTag) (= nonnull) as Tnull
        TypePredicate_::IsNot(p) if matches!(&p.1, TypePredicate_::IsTag(TypeTag::NullTag)) => {
            mk((r, Ty_::Tprim(Tprim::Tnull)))
        }
        _ => mk((r, Ty_::Tneg(neg_t))),
    }
}

pub fn traversable(r: Reason, ty: Ty) -> Ty {
    class_type(r, sn::collections::TRAVERSABLE.to_string(), vec![ty])
}

pub fn keyed_traversable(r: Reason, kty: Ty, vty: Ty) -> Ty {
    class_type(
        r,
        sn::collections::KEYED_TRAVERSABLE.to_string(),
        vec![kty, vty],
    )
}

pub fn keyed_container(r: Reason, kty: Ty, vty: Ty) -> Ty {
    class_type(
        r,
        sn::collections::KEYED_CONTAINER.to_string(),
        vec![kty, vty],
    )
}

pub fn awaitable(r: Reason, ty: Ty) -> Ty {
    class_type(r, sn::classes::AWAITABLE.to_string(), vec![ty])
}

pub fn generator(r: Reason, key: Ty, value: Ty, send: Ty) -> Ty {
    class_type(
        r,
        sn::classes::GENERATOR.to_string(),
        vec![key, value, send],
    )
}

pub fn async_generator(r: Reason, key: Ty, value: Ty, send: Ty) -> Ty {
    class_type(
        r,
        sn::classes::ASYNC_GENERATOR.to_string(),
        vec![key, value, send],
    )
}

pub fn async_iterator(r: Reason, ty: Ty) -> Ty {
    class_type(r, sn::classes::ASYNC_ITERATOR.to_string(), vec![ty])
}

pub fn async_keyed_iterator(r: Reason, ty1: Ty, ty2: Ty) -> Ty {
    class_type(
        r,
        sn::classes::ASYNC_KEYED_ITERATOR.to_string(),
        vec![ty1, ty2],
    )
}

pub fn pair(r: Reason, ty1: Ty, ty2: Ty) -> Ty {
    class_type(r, sn::collections::PAIR.to_string(), vec![ty1, ty2])
}

pub fn dict(r: Reason, kty: Ty, vty: Ty) -> Ty {
    class_type(r, sn::collections::DICT.to_string(), vec![kty, vty])
}

pub fn keyset(r: Reason, ty: Ty) -> Ty {
    class_type(r, sn::collections::KEYSET.to_string(), vec![ty])
}

pub fn vec(r: Reason, ty: Ty) -> Ty {
    class_type(r, sn::collections::VEC.to_string(), vec![ty])
}

pub fn any_array(r: Reason, kty: Ty, vty: Ty) -> Ty {
    class_type(r, sn::collections::ANY_ARRAY.to_string(), vec![kty, vty])
}

pub fn container(r: Reason, ty: Ty) -> Ty {
    class_type(r, sn::collections::CONTAINER.to_string(), vec![ty])
}

pub fn throwable(r: Reason) -> Ty {
    class_type(r, sn::classes::THROWABLE.to_string(), vec![])
}

pub fn datetime(r: Reason) -> Ty {
    class_type(r, sn::classes::DATE_TIME.to_string(), vec![])
}

pub fn datetime_immutable(r: Reason) -> Ty {
    class_type(r, sn::classes::DATE_TIME_IMMUTABLE.to_string(), vec![])
}

pub fn const_vector(r: Reason, ty: Ty) -> Ty {
    class_type(r, sn::collections::CONST_VECTOR.to_string(), vec![ty])
}

pub fn const_collection(r: Reason, ty: Ty) -> Ty {
    class_type(r, sn::collections::CONST_COLLECTION.to_string(), vec![ty])
}

pub fn collection(r: Reason, ty: Ty) -> Ty {
    class_type(r, sn::collections::COLLECTION.to_string(), vec![ty])
}

pub fn spliceable(r: Reason, ty1: Ty, ty2: Ty, ty3: Ty) -> Ty {
    class_type(r, sn::classes::SPLICEABLE.to_string(), vec![ty1, ty2, ty3])
}

pub fn vec_or_dict(r: Reason, kty: Ty, vty: Ty) -> Ty {
    mk((r, Ty_::TvecOrDict(kty, vty)))
}

pub fn int(r: Reason) -> Ty {
    prim_type(r, Tprim::Tint)
}

pub fn bool(r: Reason) -> Ty {
    prim_type(r, Tprim::Tbool)
}

pub fn string(r: Reason) -> Ty {
    class_type(r, missing_special_names::C_STRING.to_string(), vec![])
}

/// Mirror of the classname.hhi definition. This sucks: the type of the ::class
/// constant is burned into decls at folding time so this supports the case when
/// you want to wrap a locl ty e.g. from [Typing.class_expr] in a classname.
/// TODO: eliminate the use site of this for CIexpr and make class_expr
/// produce a class type directly
pub fn typename(r: Reason, tyl: Vec<Ty>) -> Ty {
    let cstr = string(r.clone());
    mk((
        r,
        Ty_::Tnewtype(sn::classes::TYPE_NAME.to_string(), tyl, cstr),
    ))
}

pub fn classname(r: Reason, tyl: Vec<Ty>) -> Ty {
    let cstr = typename(r.clone(), tyl.clone());
    mk((
        r,
        Ty_::Tnewtype(sn::classes::CLASS_NAME.to_string(), tyl, cstr),
    ))
}

pub fn class_or_classname(r: Reason, tyl: Vec<Ty>) -> Ty {
    let cstr = mk((r.clone(), Ty_::Tnonnull));
    mk((
        r,
        Ty_::Tnewtype(sn::classes::CLASS_OR_CLASSNAME.to_string(), tyl, cstr),
    ))
}

pub fn float(r: Reason) -> Ty {
    prim_type(r, Tprim::Tfloat)
}

pub fn num(r: Reason) -> Ty {
    prim_type(r, Tprim::Tnum)
}

pub fn arraykey(r: Reason) -> Ty {
    prim_type(r, Tprim::Tarraykey)
}

pub fn void(r: Reason) -> Ty {
    prim_type(r, Tprim::Tvoid)
}

pub fn null(r: Reason) -> Ty {
    prim_type(r, Tprim::Tnull)
}

pub fn nonnull(r: Reason) -> Ty {
    mk((r, Ty_::Tnonnull))
}

pub fn dynamic(r: Reason) -> Ty {
    mk((r, Ty_::Tdynamic(None)))
}

pub fn is_dynamic_or_like_or_mixed(ty: &DeclTy) -> bool {
    match ty.node_ref() {
        ty::decl::Ty_::Tdynamic | ty::decl::Ty_::Tlike(_) | ty::decl::Ty_::Tmixed => true,
        _ => false,
    }
}

pub fn like(r: crate::ctx::R, ty: DeclTy) -> DeclTy {
    if is_dynamic_or_like_or_mixed(&ty) {
        ty
    } else {
        match ty.node_ref() {
            ty::decl::Ty_::Tapply(id_and_tyl)
                if id_and_tyl.0.id_ref().as_str() == sn::classes::SUPPORT_DYN
                    && id_and_tyl.1.len() == 1
                    && is_dynamic_or_like_or_mixed(&id_and_tyl.1[0]) =>
            {
                ty
            }
            _ => DeclTy::new(r, ty::decl::Ty_::Tlike(ty)),
        }
    }
}

/// A locl type already subsumes dynamic if adding ~ty would be redundant.
/// Do NOT simplify mixed (?nonnull) here: downstream code (e.g. type_switch
/// refinement) relies on detecting dynamic in a Tunion to preserve like-type
/// wrapping through predicate-based refinement.
pub fn is_locl_supertype_of_dynamic(ty: &Ty) -> bool {
    match get_node(ty) {
        Ty_::Tdynamic(_) => true,
        Ty_::Tany(_) => true,
        Ty_::Toption(inner) => is_locl_supertype_of_dynamic(inner),
        Ty_::Tnewtype(n, tyl, _) if tyl.len() == 1 && n == sn::classes::SUPPORT_DYN => {
            is_locl_supertype_of_dynamic(&tyl[0])
        }
        Ty_::Tunion(tys) => tys.iter().any(is_locl_supertype_of_dynamic),
        _ => false,
    }
}

pub fn locl_like(r: Reason, ty: Ty) -> Ty {
    match get_node(&ty) {
        Ty_::Tprim(Tprim::Tnoreturn) => ty,
        _ if is_locl_supertype_of_dynamic(&ty) => ty,
        _ => {
            let dynamic = dynamic(r.clone());
            mk((r, Ty_::Tunion(vec![dynamic, ty])))
        }
    }
}

/// Wrap supportdyn around a type unless it's already got it
/// or trivially supports dynamic
pub fn supportdyn(r: Reason, ty: Ty) -> Ty {
    match get_node(&ty) {
        Ty_::Tnewtype(c, _, _) if c == sn::classes::SUPPORT_DYN => ty,
        Ty_::Tunion(tyl) if tyl.is_empty() => ty,
        Ty_::Tdynamic(_) | Ty_::Tprim(_) => ty,
        _ => mk((
            r,
            Ty_::Tnewtype(sn::classes::SUPPORT_DYN.to_string(), vec![ty.clone()], ty),
        )),
    }
}

pub fn supportdyn_nonnull(r: Reason) -> Ty {
    let ty = nonnull(r.clone());
    supportdyn(r, ty)
}

pub fn mixed(r: Reason) -> Ty {
    let ty = nonnull(r.clone());
    mk((r, Ty_::Toption(ty)))
}

pub fn nothing(r: Reason) -> Ty {
    mk((r, Ty_::Tunion(vec![])))
}

pub fn shape(r: Reason, kind: Ty, map: t_shape_map::T<ShapeFieldType>) -> Ty {
    mk((
        r,
        Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
            origin: TypeOrigin::MissingOrigin,
            unknown_value: kind,
            fields: map,
        })),
    ))
}

pub fn closed_shape(r: Reason, map: t_shape_map::T<ShapeFieldType>) -> Ty {
    let kind = nothing(r.clone());
    shape(r, kind, map)
}

pub fn open_shape(kind: Ty, r: Reason, map: t_shape_map::T<ShapeFieldType>) -> Ty {
    shape(r, kind, map)
}

pub fn top_shape(r: Reason) -> Ty {
    let kind = mixed(r.clone());
    shape(r, kind, t_shape_map::T::new())
}

pub fn supportdyn_mixed(r: Reason) -> Ty {
    let ty = mixed(r.clone());
    supportdyn(r, ty)
}

pub fn representable_as(r: Reason, ty: Ty) -> Ty {
    let cstr = mixed(r.clone());
    mk((
        r,
        Ty_::Tnewtype(sn::classes::REPRESENTABLE_AS.to_string(), vec![ty], cstr),
    ))
}

pub fn resource(r: Reason) -> Ty {
    prim_type(r, Tprim::Tresource)
}

pub fn tyvar(r: Reason, v: isize) -> Ty {
    mk((r, Ty_::Tvar(v)))
}

pub fn generic(r: Reason, n: String) -> Ty {
    mk((r, Ty_::Tgeneric(n)))
}

pub fn this(r: Reason) -> Ty {
    mk((r, Ty_::Tgeneric(sn::typehints::THIS.to_string())))
}

pub fn taccess(r: Reason, ty: Ty, id: PosId) -> Ty {
    mk((r, Ty_::Taccess(TaccessType(ty, id))))
}

pub fn nullable(r: Reason, ty: Ty) -> Ty {
    // Cheap avoidance of double nullable
    match get_node(&ty) {
        Ty_::Toption(_) => {
            // The node is shared, as in OCaml.
            let Ty(_, ty_) = ty;
            Ty(r, ty_)
        }
        Ty_::Tunion(tyl) if tyl.is_empty() => null(r),
        _ => mk((r, Ty_::Toption(ty))),
    }
}

pub fn apply(
    r: crate::ctx::R,
    id: Positioned<TypeName, <crate::ctx::R as ty::reason::Reason>::Pos>,
    tyl: Vec<DeclTy>,
) -> DeclTy {
    DeclTy::new(
        r,
        ty::decl::Ty_::Tapply(Box::new((id, tyl.into_boxed_slice()))),
    )
}

pub fn decl_string(r: crate::ctx::R) -> DeclTy {
    let id = Positioned::new(
        r.pos().clone(),
        TypeName::new(missing_special_names::C_STRING),
    );
    apply(r, id, vec![])
}

pub fn tuple(r: Reason, tyl: Vec<Ty>) -> Ty {
    let nothing = nothing(r.clone());
    mk((
        r,
        Ty_::Ttuple(TupleType {
            required: tyl,
            optional: vec![],
            extra: TupleExtra::Tvariadic(nothing),
        }),
    ))
}

pub fn union(r: Reason, mut tyl: Vec<Ty>) -> Ty {
    if tyl.len() == 1 {
        tyl.pop().unwrap()
    } else {
        mk((r, Ty_::Tunion(tyl)))
    }
}

pub fn intersection(r: Reason, mut tyl: Vec<Ty>) -> Ty {
    match tyl.len() {
        0 => mixed(r),
        1 => tyl.pop().unwrap(),
        _ => mk((r, Ty_::Tintersection(tyl))),
    }
}

pub fn function_ref(r: Reason, ty: Ty) -> Ty {
    mk((
        r,
        Ty_::Tnewtype(
            missing_special_names::C_FUNCTION_REF.to_string(),
            vec![ty.clone()],
            ty,
        ),
    ))
}

pub fn label(r: Reason, ty_in: Ty, ty_out: Ty) -> Ty {
    let cstr = mixed(r.clone());
    mk((
        r,
        Ty_::Tnewtype(
            sn::classes::ENUM_CLASS_LABEL.to_string(),
            vec![ty_in, ty_out],
            cstr,
        ),
    ))
}

pub fn has_member(
    r: Reason,
    name: Sid,
    ty: Ty,
    class_id: nast::ClassId_,
    methd: Option<HasMemberMethod>,
) -> InternalType {
    InternalType::ConstraintType(mk_constraint_type((
        r,
        ConstraintType_::ThasMember(HasMember {
            name,
            type_: ty,
            class_id,
            method: methd,
        }),
    )))
}

pub fn list_destructure(r: Reason, tyl: Vec<Ty>) -> InternalType {
    InternalType::ConstraintType(mk_constraint_type((
        r,
        ConstraintType_::Tdestructure(Destructure {
            required: tyl,
            optional: vec![],
            variadic: None,
            kind: DestructureKind::ListDestructure,
        }),
    )))
}

pub fn simple_variadic_splat(r: Reason, ty: Ty) -> InternalType {
    InternalType::ConstraintType(mk_constraint_type((
        r,
        ConstraintType_::Tdestructure(Destructure {
            required: vec![],
            optional: vec![],
            variadic: Some(ty),
            kind: DestructureKind::SplatUnpack,
        }),
    )))
}

pub fn capability(r: Reason, name: String) -> Ty {
    class_type(r, name, vec![])
}

pub fn default_capability(p: PosOrDecl) -> Ty {
    // Not in the OCaml, which builds the type again at each call (the
    // capability of every call of a function without contexts): the type
    // depends only on the position, and is kept per thread for the last
    // positions (by their file and their span, which is all a position is).
    thread_local! {
        static MEMO: std::cell::RefCell<Vec<Option<(PosOrDecl, Ty)>>> =
            std::cell::RefCell::new(vec![None; 64]);
    }
    let same = |p1: &PosOrDecl, p2: &PosOrDecl| {
        p1.interned_filename().ptr_eq(p2.interned_filename()) && p1.to_raw_span() == p2.to_raw_span()
    };
    let slot = (p.start_offset() ^ p.end_offset().rotate_left(3)) & 63;
    if let Some(ty) = MEMO.with_borrow(|m| match &m[slot] {
        Some((p1, ty)) if same(p1, &p) => Some(ty.clone()),
        _ => None,
    }) {
        return ty;
    }
    let ty = default_capability_uncached(p);
    MEMO.with_borrow_mut(|m| m[slot] = Some((p, ty.clone())));
    ty
}

fn default_capability_uncached(p: PosOrDecl) -> Ty {
    use missing_special_names::capabilities::*;
    let r = reason::default_capability(p);
    let tyl = vec![
        class_type(r.clone(), WRITE_PROPERTY.to_string(), vec![]),
        class_type(r.clone(), ACCESS_GLOBALS.to_string(), vec![]),
        class_type(r.clone(), RX_LOCAL.to_string(), vec![]),
        class_type(r.clone(), SYSTEM_LOCAL.to_string(), vec![]),
        class_type(r.clone(), IMPLICIT_POLICY_LOCAL.to_string(), vec![]),
        class_type(r.clone(), IO.to_string(), vec![]),
    ];
    intersection(r, tyl)
}

pub fn default_capability_decl(p: <crate::ctx::R as ty::reason::Reason>::Pos) -> DeclTy {
    use missing_special_names::capabilities::*;
    use ty::reason::Reason as _;
    let r: crate::ctx::R = crate::ctx::R::mk(|| {
        ty::reason::ReasonImpl::FromWitnessDecl(ty::reason::WitnessDecl::DefaultCapability(
            p.clone(),
        ))
    });
    let tyl: Vec<DeclTy> = [
        WRITE_PROPERTY,
        ACCESS_GLOBALS,
        RX_LOCAL,
        SYSTEM_LOCAL,
        IMPLICIT_POLICY_LOCAL,
        IO,
    ]
    .into_iter()
    .map(|name| {
        apply(
            r.clone(),
            Positioned::new(p.clone(), TypeName::new(name)),
            vec![],
        )
    })
    .collect();
    DeclTy::new(r, ty::decl::Ty_::Tintersection(tyl.into_boxed_slice()))
}

pub fn default_capability_unsafe(p: PosOrDecl) -> Ty {
    mixed(reason::hint(p))
}

/// Construct the default type for `__construct`
pub fn default_construct(r: Reason) -> Ty {
    let pos = reason::to_pos(&r);
    let ft_ret = void(r.clone());
    mk((
        r,
        Ty_::Tfun(std::rc::Rc::new(FunType {
            tparams: vec![],
            where_constraints: vec![],
            params: vec![],
            implicit_params: FunImplicitParams {
                capability: Capability::CapDefaults(pos),
            },
            flags: fun_flags_make(
                ast_defs::FunKind::FSync,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
            ),
            ret: ft_ret,
            instantiated: true,
        })),
    ))
}

pub fn make_dynamic_tfun(r: Reason) -> Ty {
    let fp_type = dynamic(r.clone());
    let ft_ret = dynamic(r.clone());
    mk((
        r.clone(),
        Ty_::Tfun(std::rc::Rc::new(FunType {
            tparams: vec![],
            where_constraints: vec![],
            params: vec![FunParam {
                pos: reason::to_pos(&r),
                name: None,
                type_: fp_type,
                flags: fun_param_flags_make(false, false, false, false, false, true, false),
                def_value: None,
            }],
            implicit_params: FunImplicitParams {
                capability: Capability::CapDefaults(reason::to_pos(&r)),
            },
            flags: fun_flags_make(
                ast_defs::FunKind::FSync,
                false,
                false,
                false,
                false,
                false,
                true,
                false,
            ),
            ret: ft_ret,
            instantiated: true,
        })),
    ))
}

#[cfg(test)]
mod tests {
    use oxidized::pos::Pos;

    use super::*;

    fn r() -> Reason {
        crate::typing_reason::none()
    }

    fn pred(p: TypePredicate_) -> TypePredicate {
        TypePredicate(r(), p)
    }

    #[test]
    fn class_types() {
        let ty = vec(r(), int(r()));
        match get_node(&ty) {
            Ty_::Tclass((_, name), exact, tyl) => {
                assert_eq!(name, "\\HH\\vec");
                assert!(is_nonexact(exact));
                assert!(is_prim(Tprim::Tint, &tyl[0]));
            }
            _ => panic!(),
        }
        assert!(is_string(&string(r())));
        // classname<T> is a newtype whose bound is typename<T>, whose bound is string
        let ty = classname(r(), vec![int(r())]);
        match get_node(&ty) {
            Ty_::Tnewtype(n, tyl, bound) => {
                assert_eq!(n, "\\HH\\classname");
                assert_eq!(tyl.len(), 1);
                match get_node(bound) {
                    Ty_::Tnewtype(n, tyl, bound) => {
                        assert_eq!(n, "\\HH\\typename");
                        assert_eq!(tyl.len(), 1);
                        assert!(is_string(bound));
                    }
                    _ => panic!(),
                }
            }
            _ => panic!(),
        }
    }

    #[test]
    fn negation() {
        let is_null = || pred(TypePredicate_::IsTag(TypeTag::NullTag));
        let is_int = || pred(TypePredicate_::IsTag(TypeTag::IntTag));
        assert!(is_nonnull(&neg(r(), is_null())));
        assert!(is_prim(
            Tprim::Tnull,
            &neg(r(), pred(TypePredicate_::IsNot(Box::new(is_null()))))
        ));
        assert!(is_neg(&neg(r(), is_int())));
        assert!(is_neg(&neg(
            r(),
            pred(TypePredicate_::IsNot(Box::new(is_int())))
        )));
    }

    #[test]
    fn unions_and_options() {
        assert!(is_nothing(&nothing(r())));
        let m = mixed(r());
        assert!(matches!(get_node(&m), Ty_::Toption(ty) if is_nonnull(ty)));
        // union and intersection of one type are that type
        assert!(is_prim(Tprim::Tint, &union(r(), vec![int(r())])));
        assert!(is_nothing(&union(r(), vec![])));
        assert!(is_union(&union(r(), vec![int(r()), float(r())])));
        assert!(is_prim(Tprim::Tint, &intersection(r(), vec![int(r())])));
        assert!(equal_locl_ty(&intersection(r(), vec![]), &mixed(r())));
        assert!(matches!(
            get_node(&intersection(r(), vec![int(r()), float(r())])),
            Ty_::Tintersection(tyl) if tyl.len() == 2
        ));
        // nullable: no double option, ?nothing is null
        let n = nullable(r(), int(r()));
        assert!(matches!(get_node(&n), Ty_::Toption(ty) if is_prim(Tprim::Tint, ty)));
        let nn = nullable(crate::typing_reason::invalid(), n);
        assert!(matches!(get_node(&nn), Ty_::Toption(ty) if is_prim(Tprim::Tint, ty)));
        assert!(matches!(&**get_reason(&nn), crate::typing_reason::T_::Invalid));
        assert!(is_prim(Tprim::Tnull, &nullable(r(), nothing(r()))));
    }

    #[test]
    fn likes_and_supportdyn() {
        // locl_like
        assert!(is_prim(
            Tprim::Tnoreturn,
            &locl_like(r(), prim_type(r(), Tprim::Tnoreturn))
        ));
        assert!(is_dynamic(&locl_like(r(), dynamic(r()))));
        let l = locl_like(r(), int(r()));
        assert!(matches!(
            get_node(&l),
            Ty_::Tunion(tyl) if tyl.len() == 2 && is_dynamic(&tyl[0]) && is_prim(Tprim::Tint, &tyl[1])
        ));
        // already a supertype of dynamic: unchanged
        assert!(equal_locl_ty(&locl_like(r(), l.clone()), &l));
        let opt_dyn = nullable(r(), dynamic(r()));
        assert!(is_locl_supertype_of_dynamic(&opt_dyn));
        // mixed is not simplified
        assert!(!is_locl_supertype_of_dynamic(&mixed(r())));
        let sd_dyn = mk((
            r(),
            Ty_::Tnewtype(
                "\\HH\\supportdyn".to_string(),
                vec![dynamic(r())],
                dynamic(r()),
            ),
        ));
        assert!(is_locl_supertype_of_dynamic(&sd_dyn));
        // supportdyn
        assert!(is_prim(Tprim::Tint, &supportdyn(r(), int(r()))));
        assert!(is_nothing(&supportdyn(r(), nothing(r()))));
        assert!(is_dynamic(&supportdyn(r(), dynamic(r()))));
        let sd = supportdyn_nonnull(r());
        assert!(matches!(
            get_node(&sd),
            Ty_::Tnewtype(n, tyl, bound)
                if n == "\\HH\\supportdyn" && is_nonnull(&tyl[0]) && is_nonnull(bound)
        ));
        assert!(equal_locl_ty(&supportdyn(r(), sd.clone()), &sd));
    }

    #[test]
    fn shapes_and_tuples() {
        let s = closed_shape(r(), t_shape_map::T::new());
        assert!(matches!(
            get_node(&s),
            Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple { origin: TypeOrigin::MissingOrigin, unknown_value, fields }))
                if is_nothing(unknown_value) && fields.is_empty()
        ));
        let s = top_shape(r());
        assert!(matches!(
            get_node(&s),
            Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple { unknown_value, .. }))
                if equal_locl_ty(unknown_value, &mixed(r()))
        ));
        let s = open_shape(int(r()), r(), t_shape_map::T::new());
        assert!(matches!(
            get_node(&s),
            Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple { unknown_value, .. }))
                if is_prim(Tprim::Tint, unknown_value)
        ));
        let t = tuple(r(), vec![int(r()), float(r())]);
        assert!(matches!(
            get_node(&t),
            Ty_::Ttuple(TupleType { required, optional, extra: TupleExtra::Tvariadic(v) })
                if required.len() == 2 && optional.is_empty() && is_nothing(v)
        ));
    }

    #[test]
    fn functions_and_capabilities() {
        let c = default_construct(r());
        match get_node(&c) {
            Ty_::Tfun(ft) => {
                assert!(ft.params.is_empty() && ft.instantiated);
                assert!(is_prim(Tprim::Tvoid, &ft.ret));
                assert_eq!(ft.flags.bits(), 0);
                assert!(matches!(
                    ft.implicit_params.capability,
                    Capability::CapDefaults(_)
                ));
            }
            _ => panic!(),
        }
        let d = make_dynamic_tfun(r());
        match get_node(&d) {
            Ty_::Tfun(ft) => {
                assert_eq!(ft.params.len(), 1);
                assert!(is_dynamic(&ft.params[0].type_));
                assert!(get_fp_splat(&ft.params[0]));
                assert_eq!(get_fp_mode(&ft.params[0]), ParamMode::FPnormal);
                assert!(get_ft_variadic(ft) && !get_ft_named_variadic(ft));
                assert_eq!(get_ft_fun_kind(ft), ast_defs::FunKind::FSync);
                assert!(is_dynamic(&ft.ret));
            }
            _ => panic!(),
        }
        let cap = default_capability(Pos::NONE);
        match get_node(&cap) {
            Ty_::Tintersection(tyl) => {
                let names: Vec<&str> = tyl
                    .iter()
                    .map(|ty| match get_node(ty) {
                        Ty_::Tclass((_, n), _, _) => n.as_str(),
                        _ => panic!(),
                    })
                    .collect();
                assert_eq!(
                    names,
                    vec![
                        "\\HH\\Capabilities\\WriteProperty",
                        "\\HH\\Capabilities\\AccessGlobals",
                        "\\HH\\Capabilities\\RxLocal",
                        "\\HH\\Capabilities\\SystemLocal",
                        "\\HH\\Capabilities\\ImplicitPolicyLocal",
                        "\\HH\\Capabilities\\IO",
                    ]
                );
            }
            _ => panic!(),
        }
        assert!(matches!(
            &**get_reason(&cap),
            crate::typing_reason::T_::FromWitnessDecl(reason::WitnessDecl::DefaultCapability(_))
        ));
        let unsafe_cap = default_capability_unsafe(Pos::NONE);
        assert!(equal_locl_ty(&unsafe_cap, &mixed(r())));
        assert!(matches!(
            &**get_reason(&unsafe_cap),
            crate::typing_reason::T_::FromWitnessDecl(reason::WitnessDecl::Hint(_))
        ));
    }

    #[test]
    fn constraint_types() {
        let d = list_destructure(r(), vec![int(r())]);
        assert!(matches!(
            &d,
            InternalType::ConstraintType(ConstraintType(_, c))
                if matches!(&**c, ConstraintType_::Tdestructure(Destructure { required, variadic: None, kind: DestructureKind::ListDestructure, .. }) if required.len() == 1)
        ));
        let s = simple_variadic_splat(r(), int(r()));
        assert!(matches!(
            &s,
            InternalType::ConstraintType(ConstraintType(_, c))
                if matches!(&**c, ConstraintType_::Tdestructure(Destructure { required, variadic: Some(_), kind: DestructureKind::SplatUnpack, .. }) if required.is_empty())
        ));
        let m = has_member(
            r(),
            ast_defs::Id(Pos::NONE, "m".to_string()),
            int(r()),
            nast::ClassId_::CIself,
            None,
        );
        assert!(matches!(&m, InternalType::ConstraintType(c) if is_has_member(c)));
    }

    #[test]
    fn decl_types() {
        use pos::Pos as _;
        type R = crate::ctx::R;
        let none = || R::none();
        let int = || DeclTy::prim(none(), Tprim::Tint);
        let dynamic = || DeclTy::new(none(), ty::decl::Ty_::Tdynamic);
        let supportdyn = |ty: DeclTy| {
            apply(
                none(),
                Positioned::new(pos::BPos::none(), TypeName::new("\\HH\\supportdyn")),
                vec![ty],
            )
        };
        assert!(is_dynamic_or_like_or_mixed(&dynamic()));
        assert!(is_dynamic_or_like_or_mixed(&DeclTy::mixed(none())));
        assert!(!is_dynamic_or_like_or_mixed(&int()));
        let l = like(none(), int());
        assert!(matches!(l.node_ref(), ty::decl::Ty_::Tlike(_)));
        // no like of a like, of dynamic, of mixed or of supportdyn of those
        assert!(equal_decl_ty(&like(none(), l.clone()), &l));
        assert!(equal_decl_ty(&like(none(), dynamic()), &dynamic()));
        let sd = supportdyn(DeclTy::mixed(none()));
        assert!(equal_decl_ty(&like(none(), sd.clone()), &sd));
        let sd_int = supportdyn(int());
        assert!(matches!(
            like(none(), sd_int).node_ref(),
            ty::decl::Ty_::Tlike(_)
        ));
        let s = decl_string(none());
        assert!(matches!(
            s.node_ref(),
            ty::decl::Ty_::Tapply(a) if a.0.id_ref().as_str() == "\\HH\\string" && a.1.is_empty()
        ));
    }
}
