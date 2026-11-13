// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/nast_init_check.ml`: checking that all the class members
//! are properly initialized. To be more precise, this checks that if the
//! constructor does not throw, it initializes all members.
//!
//! The OCaml check asks the typechecker two things, which are answered here
//! from the declarations alone:
//!
//! - whether a property type requires initialization
//!   (`type_does_not_require_init`: `null <: ty`, or `ty` is `dynamic`).
//!   `Typer::requires_init` decides this for the types where it does not
//!   take inference; for the others (a case type, a newtype with a lower
//!   bound, a type parameter a type alias is applied to, ...) the answer is
//!   `Unknown`. When that is the answer for a property that the constructor
//!   may have to initialize, nothing of what the constructor is checked for
//!   is reported for the class: a wrong list of uninitialized properties is
//!   worse than none.
//! - whether an expression is a call to a `noreturn` function or static
//!   method (`Typing_func_terminality.expression_exits`).

use std::cell::Cell;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::sync::Arc;

use oxidized::aast_defs::TypedefVisibility;
use oxidized::ast_defs::Bop;
use oxidized::ast_defs::ClassishKind;
use oxidized::ast_defs::ConstraintKind;
use oxidized::ast_defs::PropOrMethod;
use oxidized::ast_defs::Tprim;
use oxidized::ast_defs::Visibility;
use oxidized::file_info::Mode;
use oxidized::nast;
use oxidized::nast_check_error::NastCheckError;
use oxidized::pos::Pos;
use pos::FunName;
use pos::MethodName;
use pos::PropName;
use pos::ToOxidized;
use pos::TypeConstName;
use pos::TypeName;
use ty::decl;
use ty::decl::folded::FoldedClass;

use super::Errors;
use super::attrs;
use super::decl_init_check as di_check;
use super::decl_init_check::PARENT_INIT_PROP;
use super::decl_init_check::Props;
use super::sn;
use super::tcopt;
use crate::ctx::Ctx;
use crate::ctx::R;

/// `SSetWTop`: a set of properties, or `Top`, the set of all the properties
/// there can be (what a block that always throws initializes).
#[derive(Clone)]
enum S<'a> {
    Top,
    Set(Props<'a>),
}

impl<'a> S<'a> {
    fn empty() -> Self {
        S::Set(Props::new())
    }

    fn union(self, other: Self) -> Self {
        match (self, other) {
            (S::Top, _) | (_, S::Top) => S::Top,
            (S::Set(mut s1), S::Set(s2)) => {
                s1.extend(s2);
                S::Set(s1)
            }
        }
    }

    fn inter(self, other: Self) -> Self {
        match (self, other) {
            (S::Top, s) | (s, S::Top) => s,
            (S::Set(s1), S::Set(s2)) => S::Set(s1.intersection(&s2).copied().collect()),
        }
    }

    fn inter_list(sl: impl IntoIterator<Item = Self>) -> Self {
        sl.into_iter().fold(S::Top, S::inter)
    }

    fn add(mut self, x: &'a str) -> Self {
        if let S::Set(s) = &mut self {
            s.insert(x);
        }
        self
    }

    fn mem(&self, x: &str) -> bool {
        match self {
            S::Top => true,
            S::Set(s) => s.contains(x),
        }
    }
}

/// Raised when we hit a return statement and the initialization is not over.
/// When that is the case, we bubble up back to the toplevel environment.
/// An example (right hand side is the set of things initialized):
///
/// ```text
///  $this->x = 0;  // { x }
///  if(...) {
///     $this->y = 1; // { x, y }
///     if(...) {
///        $this->z = 2; // { x, y, z }
///        return; // raise InitReturn with set { x, y, z}
///     } // exception caught, re-raise with { x, y }
///  } // exception caught, re-reraise with { x }
/// ```
///
///  What is effectively initialized: `{ x }`
struct InitReturn<'a>(S<'a>);

type StmtResult<'a> = Result<S<'a>, InitReturn<'a>>;

/// Whether a property of some type has to be initialized.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Requires {
    Yes,
    No,
    Unknown,
}

/// Where a declared type comes from: how to read its type parameters.
#[derive(Clone, Copy)]
struct TyContext<'t> {
    /// The class the type is written in, when it is not the class being
    /// checked: an ancestor, a type of which has to be instantiated for the
    /// class that inherits it (`Decl_instantiate.instantiate` with the
    /// `dc_substs` of the ancestor).
    ancestor: Option<&'t TypeName>,
    /// Whether the type parameters that are left are those of the class
    /// being checked (and not, say, those of a type alias).
    own_generics: bool,
}

impl TyContext<'_> {
    /// A type written in the class being checked, or instantiated for it.
    const OWN: Self = TyContext {
        ancestor: None,
        own_generics: true,
    };

    /// The body of a type alias: its type parameters are not instantiated.
    const ALIAS: Self = TyContext {
        ancestor: None,
        own_generics: false,
    };
}

/// How many type aliases and type constants are expanded for one type.
const FUEL: usize = 20;

/// What stands for the typing environment.
struct Typer<'a> {
    ctx: &'a Ctx,
    class: &'a nast::Class_,
    folded: Arc<FoldedClass<R>>,
    /// Whether an answer that was needed could not be given.
    unknown: Cell<bool>,
    /// The lookups of the typing environment to make as the OCaml makes them
    /// (see [`Lookups`]), when the dependency edges are recorded.
    lookups: Option<&'a dyn Lookups>,
}

/// Not in the OCaml: the lookups that the OCaml's check makes through the
/// typing environment (`Typing_env.get_prop`, `Typing_phase.localize`,
/// `Typing_subtype.is_sub_type`, `Typing_env.get_fun`, ...), which record the
/// dependency edges of the class being checked. This port answers from the
/// declarations alone, which records nothing; when the edges are recorded,
/// `Typing_class` checks the class a second time with these lookups
/// ([`record_dependency_edges`]), only for their edges. Edges are a set: only
/// which lookups are made matters, not their order.
pub(crate) trait Lookups {
    /// `lookup_props` of one property, then, if `with_type`,
    /// `type_does_not_require_init` of its type.
    fn lookup_prop(&self, name: &str, with_type: bool);
    /// `type_does_not_require_init` of `Decl_hint.hint` of the hint of a
    /// static property.
    fn static_prop_hint(&self, hint: &nast::Hint);
    /// `Typing_func_terminality.get_fun`
    fn get_fun(&self, name: &str);
    /// `Typing_func_terminality.static_meth_is_noreturn`
    fn static_meth(&self, class_id: &nast::ClassId_, meth_name: &str);
    /// `class_prop_pos`
    fn class_prop_pos(&self, name: &str);
}

impl<'a> Typer<'a> {
    /// The context of a type written in the class `origin`.
    fn context_of<'t>(&self, origin: &'t TypeName) -> TyContext<'t> {
        if *origin == self.folded.name {
            TyContext::OWN
        } else {
            TyContext {
                ancestor: Some(origin),
                own_generics: false,
            }
        }
    }

    /// The negation of `type_does_not_require_init`, for a declared type.
    fn requires_init(&self, ty: &decl::Ty<R>, cx: TyContext<'_>, fuel: usize) -> Requires {
        use decl::Ty_;
        if fuel == 0 {
            return Requires::Unknown;
        }
        match ty.node_ref() {
            // `null` is a subtype of these.
            Ty_::Tmixed | Ty_::Toption(_) | Ty_::Tany | Ty_::Tprim(Tprim::Tnull) => Requires::No,
            // `dynamic`, and `~t` which is `dynamic | t`.
            Ty_::Tdynamic | Ty_::Tlike(_) => Requires::No,
            Ty_::Tprim(Tprim::Tvoid) => Requires::Unknown,
            Ty_::Tprim(_)
            | Ty_::Tnonnull
            | Ty_::Tthis
            | Ty_::Tfun(_)
            | Ty_::Ttuple(_)
            | Ty_::Tshape(_)
            | Ty_::TvecOrDict(_)
            | Ty_::TclassPtr(_) => Requires::Yes,
            Ty_::Trefinement(refinement) => self.requires_init(&refinement.ty, cx, fuel),
            Ty_::Tunion(tys) => {
                let all: Vec<_> = tys
                    .iter()
                    .map(|ty| self.requires_init(ty, cx, fuel))
                    .collect();
                if all.contains(&Requires::No) {
                    Requires::No
                } else if all.contains(&Requires::Unknown) {
                    Requires::Unknown
                } else {
                    Requires::Yes
                }
            }
            Ty_::Tintersection(tys) => {
                let all: Vec<_> = tys
                    .iter()
                    .map(|ty| self.requires_init(ty, cx, fuel))
                    .collect();
                if all.contains(&Requires::Yes) {
                    Requires::Yes
                } else if all.contains(&Requires::Unknown) {
                    Requires::Unknown
                } else {
                    Requires::No
                }
            }
            Ty_::Tgeneric(name) => {
                // A type parameter of an ancestor: what the class being
                // checked instantiates it with.
                if let Some(ancestor) = cx.ancestor {
                    return match self
                        .folded
                        .substs
                        .get(ancestor)
                        .and_then(|subst_context| subst_context.subst.0.get(name))
                    {
                        Some(ty) => self.requires_init(ty, TyContext::OWN, fuel - 1),
                        None => Requires::Unknown,
                    };
                }
                // `null` is a subtype of a type parameter only by way of a
                // lower bound of the parameter.
                let tparam = self
                    .class
                    .tparams
                    .iter()
                    .find(|tparam| tparam.name.1 == name.as_str());
                match tparam {
                    Some(tparam)
                        if cx.own_generics
                            && !tparam.constraints.iter().any(|(kind, _)| {
                                matches!(kind, ConstraintKind::ConstraintSuper)
                            }) =>
                    {
                        Requires::Yes
                    }
                    _ => Requires::Unknown,
                }
            }
            Ty_::Tapply(apply) => {
                let (name, args) = &**apply;
                let name = *name.id_ref();
                if name.as_str() == sn::typehints::HH_SUPPORTDYN {
                    // `null <: supportdyn<t>` if `null <: t` (and
                    // `null <: dynamic`).
                    return match &**args {
                        [arg] => self.requires_init(arg, cx, fuel),
                        _ => Requires::Unknown,
                    };
                }
                if name.as_str() == sn::typehints::POISON_MARKER && args.len() == 1 {
                    // Localized as `~t`.
                    return Requires::No;
                }
                // A class type, or the opaque type of an enum.
                if let Ok(Some(_)) = self.ctx.shallow_decls.get_class(name) {
                    return Requires::Yes;
                }
                let Ok(Some(typedef)) = self.ctx.shallow_decls.get_typedef(name) else {
                    // A name that is not bound is localized as a class.
                    return Requires::Yes;
                };
                match &typedef.type_assignment {
                    decl::ty::TypedefTypeAssignment::SimpleTypeDef(vis, ty) => {
                        // `Typing_env.should_expand_type_alias`
                        let should_expand = match vis {
                            TypedefVisibility::Transparent => true,
                            TypedefVisibility::Opaque => {
                                typedef.pos.clone().to_oxidized().filename()
                                    == self.class.name.0.filename()
                            }
                            TypedefVisibility::OpaqueModule => {
                                self.class.module.as_ref().map(|id| id.1.as_str())
                                    == typedef.module.as_ref().map(|id| id.id_ref().as_str())
                            }
                        };
                        if should_expand {
                            self.requires_init(ty, TyContext::ALIAS, fuel - 1)
                        } else if typedef.super_constraint.is_none() {
                            // A newtype that is not visible: `null` is a
                            // subtype of it only by way of a lower bound.
                            Requires::Yes
                        } else {
                            Requires::Unknown
                        }
                    }
                    decl::ty::TypedefTypeAssignment::CaseType(_, _) => Requires::Unknown,
                }
            }
            Ty_::Taccess(access) => {
                // `this::T`, where `T` is a type constant of the class.
                if !matches!(access.ty.node_ref(), Ty_::Tthis) {
                    return Requires::Unknown;
                }
                let name = TypeConstName::new(access.type_const.id_ref().as_str());
                match self.folded.type_consts.get(&name) {
                    Some(tc) => match &tc.kind {
                        decl::Typeconst::TCConcrete(concrete) => {
                            self.requires_init(&concrete.ty, self.context_of(&tc.origin), fuel - 1)
                        }
                        decl::Typeconst::TCAbstract(abstract_) => {
                            if abstract_.super_constraint.is_none() {
                                Requires::Yes
                            } else {
                                Requires::Unknown
                            }
                        }
                    },
                    None => Requires::Unknown,
                }
            }
            Ty_::Twildcard => Requires::Unknown,
        }
    }

    fn requires_init_or_unknown(&self, ty: &decl::Ty<R>, cx: TyContext<'_>) -> bool {
        match self.requires_init(ty, cx, FUEL) {
            Requires::Yes => true,
            Requires::No => false,
            Requires::Unknown => {
                self.unknown.set(true);
                true
            }
        }
    }

    /// `lookup_props`, then `not (type_does_not_require_init ...)`, for one
    /// property: whether the property is one of the class (its own, or an
    /// inherited one) and has to be initialized.
    fn prop_requires_init(&self, name: &str) -> bool {
        if name == PARENT_INIT_PROP {
            // `nonnull`
            return true;
        }
        if let Some(lookups) = self.lookups {
            lookups.lookup_prop(name, true);
        }
        let name = PropName::new(name);
        // `Typing_env.get_prop`
        let Some(elt) = self.folded.props.get(&name) else {
            return false;
        };
        // `ce_type`: the type the property is declared with in the class it
        // comes from, instantiated for this class.
        let origin = match self.ctx.shallow_decls.get_class(elt.origin) {
            Ok(Some(origin)) => origin,
            _ => {
                self.unknown.set(true);
                return true;
            }
        };
        match origin.props.iter().find(|prop| *prop.name.id_ref() == name) {
            Some(prop) => self.requires_init_or_unknown(&prop.ty, self.context_of(&elt.origin)),
            None => {
                self.unknown.set(true);
                true
            }
        }
    }

    /// `filter_props_by_type`, and the same filter on the result of
    /// `lookup_props`.
    fn filter_props_by_type(&self, props: Props<'a>) -> Props<'a> {
        props
            .into_iter()
            .filter(|name| self.prop_requires_init(name))
            .collect()
    }

    /// `class_prop_pos`: where a property of the class is declared.
    fn class_prop_pos(&self, prop_name: &str) -> Pos {
        if let Some(lookups) = self.lookups {
            lookups.class_prop_pos(prop_name);
        }
        let name = PropName::new(prop_name);
        let Some(elt) = self.folded.props.get(&name) else {
            return Pos::NONE;
        };
        let Ok(Some(origin)) = self.ctx.shallow_decls.get_class(elt.origin) else {
            return Pos::NONE;
        };
        match origin.props.iter().find(|prop| *prop.name.id_ref() == name) {
            Some(prop) => prop.name.pos().clone().to_oxidized(),
            None => Pos::NONE,
        }
    }

    fn fun_is_noreturn(ty: &decl::Ty<R>) -> bool {
        match ty.node_ref() {
            decl::Ty_::Tfun(ft) => matches!(ft.ret.node_ref(), decl::Ty_::Tprim(Tprim::Tnoreturn)),
            _ => false,
        }
    }

    /// `Typing_func_terminality.static_meth_is_noreturn`
    fn static_meth_is_noreturn(&self, class_id: &nast::ClassId, meth_name: &str) -> bool {
        if let Some(lookups) = self.lookups {
            lookups.static_meth(&class_id.2, meth_name);
        }
        let class_name = match &class_id.2 {
            nast::ClassId_::CI(nast::Id(_, name)) => Some(name.as_str()),
            nast::ClassId_::CIself | nast::ClassId_::CIstatic => Some(self.class.name.1.as_str()),
            // `Typing_env_from_def.set_parent`
            nast::ClassId_::CIparent => match self.class.extends.first() {
                Some(nast::Hint(_, hint_)) => match &**hint_ {
                    nast::Hint_::Happly(nast::Id(_, parent_id), _) => Some(parent_id.as_str()),
                    _ => None,
                },
                None => None,
            },
            nast::ClassId_::CIexpr(_) | nast::ClassId_::CIreified(_) => None,
        };
        let Some(class_name) = class_name else {
            return false;
        };
        let Ok(Some(class)) = self.ctx.folded_decls.get_class(TypeName::new(class_name)) else {
            return false;
        };
        let meth_name = MethodName::new(meth_name);
        let Some(elt) = class.static_methods.get(&meth_name) else {
            return false;
        };
        let Ok(Some(origin)) = self.ctx.shallow_decls.get_class(elt.origin) else {
            return false;
        };
        origin
            .static_methods
            .iter()
            .find(|meth| *meth.name.id_ref() == meth_name)
            .is_some_and(|meth| Self::fun_is_noreturn(&meth.ty))
    }

    /// `Typing_func_terminality.expression_exits`
    fn expression_exits(&self, e: &nast::Expr) -> bool {
        let nast::Expr_::Call(call) = &e.2 else {
            return false;
        };
        match &call.func.2 {
            nast::Expr_::Id(id) => match {
                if let Some(lookups) = self.lookups {
                    lookups.get_fun(&id.1);
                }
                self.ctx.shallow_decls.get_fun(FunName::new(&id.1))
            } {
                Ok(Some(fun)) => Self::fun_is_noreturn(&fun.ty),
                _ => false,
            },
            nast::Expr_::ClassConst(cc) => self.static_meth_is_noreturn(&cc.0, &cc.1.1),
            _ => false,
        }
    }
}

/// `Env.t`
///
/// Originally, every class member has 2 possible states,
/// - Vok: when it is declared as optional, it is the job of the typer to make
///   sure it is always check for the null case, not our problem here
/// - Vnull: the value is now null, it MUST be initialized, and cannot be used
///   before it has been initialized.
///
/// Concerning the methods, basically the information we are interested in
/// is, which class members do they initialize? But we don't want to recompute
/// it every time it is called. So we memoize the result: hence the type
/// method status.
struct Env<'a> {
    typer: Typer<'a>,
    /// The private methods: `Todo body` (`Some`) before the method has been
    /// computed, `Done` (`None`) afterwards.
    methods: BTreeMap<&'a str, Cell<Option<&'a nast::FuncBody>>>,
    /// The properties that have to be initialized.
    props: Props<'a>,
    parent_cstr_props: Props<'a>,
    init_not_required_props: Props<'a>,
}

impl<'a> Env<'a> {
    /// `Env.make`
    fn make(typer: Typer<'a>, errors: &mut Errors) -> Self {
        let c = typer.class;
        // `split_methods`: the methods that are neither the constructor nor
        // static.
        let mut methods = BTreeMap::new();
        for m in &c.methods {
            if m.name.1 == sn::members::__CONSTRUCT || m.static_ {
                continue;
            }
            // `Env.method_`
            if m.visibility != Visibility::Private {
                continue;
            }
            if attrs::mem(
                sn::user_attributes::TESTS_BYPASS_VISIBILITY,
                &m.user_attributes,
            ) {
                continue;
            }
            methods.insert(m.name.1.as_str(), Cell::new(Some(&m.body)));
        }

        // Error when an abstract class has private properties but lacks a
        // constructor
        let has_own_cstr = di_check::constructor(c).is_some_and(|m| !m.abstract_);
        let private_props = di_check::private_deferred_init_props(has_own_cstr, c);
        let abstract_without_cstr = matches!(
            c.kind,
            ClassishKind::Cclass(oxidized::ast_defs::Abstraction::Abstract)
        ) && !has_own_cstr;
        // (`lookup_props tenv (snd c.c_name) private_props`, whose types are
        // only checked for an abstract class without a constructor.)
        if let (Some(lookups), false) = (typer.lookups, abstract_without_cstr) {
            for name in &private_props {
                if *name != PARENT_INIT_PROP {
                    lookups.lookup_prop(name, false);
                }
            }
        }
        if abstract_without_cstr {
            let uninit = typer.filter_props_by_type(private_props);
            if !uninit.is_empty() {
                errors.add(NastCheckError::ConstructorRequired {
                    pos: c.name.0.clone(),
                    class_name: c.name.1.clone(),
                    prop_names: uninit.iter().map(|name| name.to_string()).collect(),
                });
            }
        }

        let mut init_not_required_props = Props::new();
        di_check::init_not_required_props(c, &mut init_not_required_props);
        let parent_cstr_props =
            typer.filter_props_by_type(di_check::parent_initialized_members(typer.ctx, c));

        let mut props = Props::new();
        di_check::own_props(c, &mut props);
        // If we define our own constructor, we need to pretend any traits we
        // use did *not* define a constructor, because they are not reachable
        // through parent::__construct or similar functions.
        di_check::trait_props(typer.ctx, c, &mut props);
        di_check::parent_props(typer.ctx, c, &mut props);
        di_check::parent(typer.ctx, c, &mut props);
        let props = typer.filter_props_by_type(props);

        Env {
            typer,
            methods,
            props,
            parent_cstr_props,
            init_not_required_props,
        }
    }
}

/// List of functions that can use `$this` before the initialization is over.
fn is_whitelisted(x: &str) -> bool {
    x == sn::std_lib_functions::GET_CLASS
}

fn is_lateinit(cv: &nast::ClassVar) -> bool {
    attrs::mem(sn::user_attributes::LATE_INIT, &cv.user_attributes)
}

/// `Aast_utils.arg_to_expr`
fn arg_to_expr(arg: &nast::Argument) -> &nast::Expr {
    match arg {
        nast::Argument::Anormal(e)
        | nast::Argument::Ainout(_, e)
        | nast::Argument::Anamed(_, e) => e,
    }
}

/// `Aast_utils.get_param_default`
fn get_param_default(param: &nast::FunParam) -> Option<&nast::Expr> {
    match &param.info {
        nast::FunParamInfo::ParamOptional(e) => e.as_ref(),
        nast::FunParamInfo::ParamRequired | nast::FunParamInfo::ParamVariadic => None,
    }
}

/// `Obj_get ((_, _, This), (_, _, Id id), _, prop_or_method)`: the member of
/// `$this` that an expression is.
fn this_member<'a>(e: &'a nast::Expr_, kind: PropOrMethod) -> Option<&'a nast::Id> {
    match e {
        nast::Expr_::ObjGet(og) => match &**og {
            (
                nast::Expr(_, _, nast::Expr_::This),
                nast::Expr(_, _, nast::Expr_::Id(id)),
                _,
                prop_or_method,
            ) if *prop_or_method == kind => Some(id),
            _ => None,
        },
        _ => None,
    }
}

/// The traversal of the constructor (and of the private methods it calls).
///
/// The functions return the set of properties initialized. More exactly,
/// they return an `S`, i.e. either a set, or `Top`, which is the top element
/// of the set of sets of properties, i.e. a set containing all the possible
/// properties. `Top` is returned for a block of statements if this block
/// always throws. It is an abstract construct used to deal gracefully with
/// control flow.
///
/// For example, if we have an `if` statement like:
///
/// ```text
/// if (...) {
///   // This branch initialize a set of properties S1
///   ...
/// } else {
///   // This branch initialize another set of properties S2
///   ...
/// }
/// ```
///
/// then the set `S` of properties initialized by this `if` statement is the
/// intersection `S1 /\ S2`. If one of the branches throws, say the first
/// branch, then the set `S` of properties initialized by the `if` statement
/// is equal to the set of properties initialized by the branch that does not
/// throw, i.e. `S = S2`. This amounts to saying that `S1` is some top element
/// of the set of sets of variables, which we call `Top`, which has the
/// property that for all set S of properties, S is included in `Top`, such
/// that `S = S1 /\ S2` still holds.
struct Checker<'a, 'e> {
    env: Env<'a>,
    errors: &'e mut Errors,
}

impl<'a, 'e> Checker<'a, 'e> {
    fn constructor(&mut self, cstr: Option<&'a nast::Method_>) -> S<'a> {
        match cstr {
            None => S::empty(),
            Some(cstr) => {
                for p in &cstr.params {
                    if let Some(e) = get_param_default(p) {
                        self.expr(S::empty(), e);
                    }
                }
                self.toplevel(S::empty(), &cstr.body.fb_ast)
            }
        }
    }

    fn assign_expr(&mut self, acc: S<'a>, e1: &'a nast::Expr) -> S<'a> {
        if let Some(nast::Id(_, y)) = this_member(&e1.2, PropOrMethod::IsProp) {
            return acc.add(y);
        }
        match &e1.2 {
            nast::Expr_::List(el) => el.iter().fold(acc, |acc, e| self.assign_expr(acc, e)),
            _ => acc,
        }
    }

    fn argument_list(&mut self, acc: S<'a>, el: &'a [nast::Argument]) -> S<'a> {
        el.iter()
            .fold(acc, |acc, arg| self.expr(acc, arg_to_expr(arg)))
    }

    fn stmt(&mut self, acc: S<'a>, st: &'a nast::Stmt) -> StmtResult<'a> {
        use nast::Stmt_;
        Ok(match &st.1 {
            Stmt_::Expr(e) => {
                // only in top level!
                if let nast::Expr_::Call(call) = &e.2 {
                    if let nast::Expr_::ClassConst(cc) = &call.func.2 {
                        if matches!(cc.0.2, nast::ClassId_::CIparent)
                            && cc.1.1 == sn::members::__CONSTRUCT
                        {
                            let acc = self.argument_list(acc, &call.args);
                            return Ok(acc.add(PARENT_INIT_PROP));
                        }
                    }
                }
                let res = self.expr(acc, e);
                if self.env.typer.expression_exits(e) {
                    S::Top
                } else {
                    res
                }
            }
            Stmt_::Break => acc,
            Stmt_::Continue => acc,
            Stmt_::Throw(e) => {
                // Run on exception object but $this initialisation checks,
                // but ignore the argument as it is no return.
                self.expr(acc, e);
                S::Top
            }
            Stmt_::Return(e) => {
                let acc = match &**e {
                    None => acc,
                    Some(x) => self.expr(acc, x),
                };
                if self.are_all_init(&acc) {
                    acc
                } else {
                    return Err(InitReturn(acc));
                }
            }
            Stmt_::YieldBreak => S::Top,
            Stmt_::Awaitall(awaitall) => {
                let (el, b) = &**awaitall;
                let acc = el.iter().fold(acc, |acc, (_, e2)| self.expr(acc, e2));
                self.block(acc, b)?
            }
            Stmt_::Concurrent(b) => self.block(acc, b)?,
            Stmt_::If(if_) => {
                let (e1, b1, b2) = &**if_;
                let acc = self.expr(acc, e1);
                let b1 = self.block(acc.clone(), b1)?;
                let b2 = self.block(acc.clone(), b2)?;
                acc.union(b1.inter(b2))
            }
            Stmt_::Do(do_) => {
                let (b, nast::LoopCond(_, _, e)) = &**do_;
                let acc = self.block(acc, b)?;
                self.expr(acc, e)
            }
            Stmt_::While(while_) => {
                // Run on the body for $this initialisation checks but ignore
                // the accumulated initialisations because while body can run
                // zero times.
                let (nast::LoopCond(_, _, e), b) = &**while_;
                self.block(acc.clone(), b)?;
                self.expr(acc, e)
            }
            Stmt_::Using(us) => {
                let acc = us.exprs.1.iter().fold(acc, |acc, e| self.expr(acc, e));
                self.block(acc, &us.block)?
            }
            Stmt_::For(for_) => {
                // Run on the body, condition, increment, for $this
                // initialisation checks but ignore the accumulated
                // initialisations because while body can run zero times.
                let (el1, e_opt, nast::LoopIter(_, _, el2), b) = &**for_;
                if let Some(nast::LoopCond(_, _, e)) = e_opt {
                    self.expr(acc.clone(), e);
                }
                self.exprl(acc.clone(), el2);
                self.block(acc.clone(), b)?;
                self.exprl(acc, el1)
            }
            Stmt_::Switch(switch) => {
                let (e, cl, dfl) = &**switch;
                let acc = self.expr(acc, e);
                // Filter out cases that fallthrough
                // NOTE: 'default' never fallthough
                let case_is_empty_or_exactly_fallthrough = |case: &nast::Case| {
                    matches!(
                        case.1.0.as_slice(),
                        [nast::Stmt(_, Stmt_::Fallthrough)] | []
                    )
                };
                let mut cl_results = vec![];
                for case in cl {
                    if !case_is_empty_or_exactly_fallthrough(case) {
                        cl_results.push(self.block(acc.clone(), &case.1)?);
                    }
                }
                let cdfl = match dfl {
                    Some(nast::DefaultCase(_, b)) => Some(self.block(acc.clone(), b)?),
                    None => None,
                };
                let c = S::inter_list(cl_results);
                let c = match cdfl {
                    Some(cdfl) => c.inter(cdfl),
                    None => c,
                };
                acc.union(c)
            }
            Stmt_::Match(stmt_match) => {
                let acc = self.expr(acc, &stmt_match.expr);
                let mut arms = vec![];
                for arm in &stmt_match.arms {
                    arms.push(self.block(acc.clone(), &arm.body)?);
                }
                let c = S::inter_list(arms);
                acc.union(c)
            }
            Stmt_::Foreach(foreach) => {
                let (e, _, b) = &**foreach;
                self.block(acc.clone(), b)?;
                self.expr(acc, e)
            }
            Stmt_::Try(try_) => {
                let (b, cl, fb) = &**try_;
                let c = self.block(acc.clone(), b)?;
                let f = self.stmts_as_block(acc.clone(), &fb.0)?;
                let mut all = vec![c];
                for nast::Catch(_, _, b) in cl {
                    all.push(self.block(acc.clone(), b)?);
                }
                let c = S::inter_list(all);
                // the finally block executes even if *none* of try and catch do
                let acc = acc.union(f);
                acc.union(c)
            }
            Stmt_::Fallthrough => S::empty(),
            Stmt_::Noop => acc,
            Stmt_::Block(block) => self.block(acc, &block.1)?,
            Stmt_::Markup(_) => acc,
        })
    }

    fn toplevel(&mut self, acc: S<'a>, l: &'a nast::Block) -> S<'a> {
        let mut acc = acc;
        for st in &l.0 {
            acc = match self.stmt(acc, st) {
                Ok(acc) => acc,
                Err(InitReturn(acc)) => return acc,
            };
        }
        acc
    }

    fn block(&mut self, acc: S<'a>, l: &'a nast::Block) -> StmtResult<'a> {
        self.stmts_as_block(acc, &l.0)
    }

    fn stmts_as_block(&mut self, acc: S<'a>, l: &'a [nast::Stmt]) -> StmtResult<'a> {
        let acc_before_block = acc.clone();
        let mut acc = acc;
        for st in l {
            acc = match self.stmt(acc, st) {
                Ok(acc) => acc,
                // The block has a return statement, forget what was
                // initialized in it
                Err(InitReturn(_)) => return Err(InitReturn(acc_before_block)),
            };
        }
        Ok(acc)
    }

    fn are_all_init(&self, set: &S<'a>) -> bool {
        self.env.props.iter().all(|cv| set.mem(cv))
    }

    fn check_all_init(&mut self, pos: &Pos, acc: &S<'a>) {
        for prop_name in &self.env.props {
            if !acc.mem(prop_name) {
                self.errors.add(NastCheckError::CallBeforeInit {
                    pos: pos.clone(),
                    prop_name: prop_name.to_string(),
                });
            }
        }
    }

    fn exprl(&mut self, acc: S<'a>, l: &'a [nast::Expr]) -> S<'a> {
        l.iter().fold(acc, |acc, e| self.expr(acc, e))
    }

    fn expr_opt(&mut self, acc: S<'a>, e: &'a Option<nast::Expr>) -> S<'a> {
        match e {
            Some(e) => self.expr(acc, e),
            None => acc,
        }
    }

    fn expr(&mut self, acc: S<'a>, e: &'a nast::Expr) -> S<'a> {
        use nast::Expr_;
        let nast::Expr(_, p, e_) = e;
        if let Some(nast::Id(pos, vx)) = this_member(e_, PropOrMethod::IsProp) {
            let env = &self.env;
            let read_before_write = (env.props.contains(vx.as_str())
                && !acc.mem(vx)
                && !env.init_not_required_props.contains(vx.as_str()))
                // We're reading a property that's initialised in the parent
                // constructor, but we haven't called the parent constructor
                // yet.
                || (env.parent_cstr_props.contains(vx.as_str())
                    && !env.init_not_required_props.contains(vx.as_str())
                    && !acc.mem(vx)
                    && !acc.mem(PARENT_INIT_PROP));
            if read_before_write {
                self.errors.add(NastCheckError::ReadBeforeWrite {
                    pos: pos.clone(),
                    member_name: vx.clone(),
                });
            }
            return acc;
        }
        match e_ {
            Expr_::ValCollection(vc) => self.exprl(acc, &vc.2),
            Expr_::KeyValCollection(kvc) => kvc.2.iter().fold(acc, |acc, nast::Field(e1, e2)| {
                let acc = self.expr(acc, e1);
                self.expr(acc, e2)
            }),
            Expr_::This => {
                self.check_all_init(p, &acc);
                acc
            }
            Expr_::MethodCaller(_) | Expr_::EnumClassLabel(_) | Expr_::Id(_) => acc,
            Expr_::Lvar(_) | Expr_::Lplaceholder(_) | Expr_::Dollardollar(_) => acc,
            Expr_::Clone(e) => self.expr(acc, e),
            Expr_::ObjGet(og) => {
                let (e1, e2, _, _) = &**og;
                let acc = self.expr(acc, e1);
                self.expr(acc, e2)
            }
            Expr_::ArrayGet(ag) => {
                let (e, eo) = &**ag;
                let acc = self.expr(acc, e);
                self.expr_opt(acc, eo)
            }
            Expr_::ClassConst(_) | Expr_::ClassGet(_) => acc,
            Expr_::Call(call) => {
                let nast::CallExpr {
                    func,
                    targs: _,
                    args,
                    unpacked_arg,
                } = &**call;
                if let Some(nast::Id(_, f)) = this_member(&func.2, PropOrMethod::IsMethod) {
                    let p = &func.1;
                    return match self.env.methods.get(f.as_str()) {
                        None => {
                            self.check_all_init(p, &acc);
                            acc
                        }
                        Some(method) => match method.take() {
                            // Done
                            None => acc,
                            // Todo
                            Some(b) => {
                                // First time we encounter this private
                                // method. Let's check its arguments first,
                                // and then recurse into the method body.
                                let acc = self.argument_list(acc, args);
                                let acc = self.expr_opt(acc, unpacked_arg);
                                self.toplevel(acc, &b.fb_ast)
                            }
                        },
                    };
                }
                let whitelisted = matches!(&func.2, Expr_::Id(id) if is_whitelisted(&id.1));
                let acc = args.iter().fold(acc, |acc, arg| {
                    let arg = arg_to_expr(arg);
                    if whitelisted && matches!(arg.2, Expr_::This) {
                        acc
                    } else {
                        self.expr(acc, arg)
                    }
                });
                let acc = self.expr_opt(acc, unpacked_arg);
                self.expr(acc, func)
            }
            Expr_::True
            | Expr_::False
            | Expr_::Int(_)
            | Expr_::Float(_)
            | Expr_::Null
            | Expr_::String(_)
            | Expr_::String2(_)
            | Expr_::Nameof(_)
            | Expr_::PrefixedString(_) => acc,
            Expr_::Yield(e) => match &**e {
                nast::Afield::AFvalue(e) => self.expr(acc, e),
                nast::Afield::AFkvalue(e1, e2) => {
                    let acc = self.expr(acc, e1);
                    self.expr(acc, e2)
                }
            },
            Expr_::Await(e) => self.expr(acc, e),
            Expr_::Delay(e) => self.expr(acc, e),
            Expr_::Tuple(el) => self.exprl(acc, el),
            // List is always an lvalue
            Expr_::List(_) => acc,
            Expr_::New(new) => {
                let (_, _, el, unpacked_element, _) = &**new;
                let acc = self.argument_list(acc, el);
                self.expr_opt(acc, unpacked_element)
            }
            Expr_::Pair(pair) => {
                let (_, e1, e2) = &**pair;
                let acc = self.expr(acc, e1);
                self.expr(acc, e2)
            }
            Expr_::Cast(cast) => self.expr(acc, &cast.1),
            Expr_::Unop(unop) => self.expr(acc, &unop.1),
            Expr_::Assign(assign) => {
                let (e1, bop, e2) = &**assign;
                match bop {
                    None => {
                        let acc = self.expr(acc, e2);
                        self.assign_expr(acc, e1)
                    }
                    Some(_) => {
                        let acc = self.expr(acc, e1);
                        self.expr(acc, e2)
                    }
                }
            }
            Expr_::Binop(binop) => match binop.bop {
                Bop::Ampamp | Bop::Barbar => self.expr(acc, &binop.lhs),
                _ => {
                    let acc = self.expr(acc, &binop.lhs);
                    self.expr(acc, &binop.rhs)
                }
            },
            Expr_::Pipe(pipe) => {
                let (_, e1, e2, _) = &**pipe;
                let acc = self.expr(acc, e1);
                self.expr(acc, e2)
            }
            Expr_::Eif(eif) => {
                let (e1, e2, e3) = &**eif;
                let acc = self.expr(acc, e1);
                let acc = self.expr_opt(acc, e2);
                self.expr(acc, e3)
            }
            Expr_::Is(is) => self.expr(acc, &is.0),
            Expr_::As(as_) => self.expr(acc, &as_.expr),
            Expr_::Upcast(upcast) => self.expr(acc, &upcast.0),
            // We don't need to analyze the body of closures
            Expr_::Efun(efun) => self.fun_paraml(acc, &efun.fun.params),
            Expr_::Lfun(lfun) => self.fun_paraml(acc, &lfun.0.params),
            Expr_::Xml(xml) => {
                let (_, l, el) = &**xml;
                // `get_xhp_attr_expr`
                let acc = l.iter().fold(acc, |acc, attr| match attr {
                    nast::XhpAttribute::XhpSimple(simple) => self.expr(acc, &simple.expr),
                    nast::XhpAttribute::XhpSpread(e) => self.expr(acc, e),
                });
                self.exprl(acc, el)
            }
            Expr_::Shape(fdm) => fdm.iter().fold(acc, |acc, (_, v)| self.expr(acc, v)),
            Expr_::ExpressionTree(_) => acc,
            Expr_::Omitted => acc,
            Expr_::Import(_) => acc,
            Expr_::Collection(_) => acc,
            Expr_::FunctionPointer(_) => acc,
            Expr_::ETSplice(splice) => self.expr(acc, &splice.spliced_expr),
            Expr_::ReadonlyExpr(e) => self.expr(acc, e),
            Expr_::Hole(hole) => self.expr(acc, &hole.0),
            // Don't analyze invalid expressions
            Expr_::Invalid(_) => acc,
            Expr_::Package(_) => acc,
            Expr_::DestructureShape(_) => acc,
            Expr_::DestructureTuple(_) => acc,
        }
    }

    fn fun_paraml(&mut self, acc: S<'a>, l: &'a [nast::FunParam]) -> S<'a> {
        l.iter()
            .fold(acc, |acc, param| match get_param_default(param) {
                Some(x) => self.expr(acc, x),
                None => acc,
            })
    }
}

/// `Nast_init_check.class_`
pub fn class_(ctx: &Ctx, c: &nast::Class_, out: &mut Errors) {
    class_with_lookups(ctx, c, out, None)
}

#[cfg(feature = "port")]
/// [`class_`], making the lookups of the typing environment that the OCaml
/// makes, for their dependency edges (see [`Lookups`]); the errors found are
/// not reported (`class_` reports them).
pub(crate) fn record_dependency_edges(env: &crate::typing_env_types::Env, c: &nast::Class_) {
    let lookups = TypingLookups {
        env: std::cell::RefCell::new(env.clone()),
        class_name: c.name.1.clone(),
    };
    let ctx = crate::typing_env::get_ctx(env);
    class_with_lookups(&ctx, c, &mut Errors::default(), Some(&lookups))
}

#[cfg(feature = "port")]
/// The [`Lookups`] of the OCaml, through the typing environment of the
/// class (a copy: only the edges its lookups record are wanted).
struct TypingLookups {
    env: std::cell::RefCell<crate::typing_env_types::Env>,
    class_name: String,
}

#[cfg(feature = "port")]
impl TypingLookups {
    /// `type_does_not_require_init env (Some ty)`
    fn type_does_not_require_init(env: &mut crate::typing_env_types::Env, ty: &decl::Ty<R>) {
        use crate::typing_make_type as mk;
        use crate::typing_reason as reason;
        use crate::typing_subtype::is_sub_type;
        let (_ty_err_opt, ty) = crate::typing_phase::localize_no_subst(env, true, ty);
        let null = mk::null(reason::none());
        let _ = is_sub_type(env, &null, &ty) || {
            let dynamic = mk::dynamic(reason::none());
            is_sub_type(env, &dynamic, &ty) && is_sub_type(env, &ty, &dynamic)
        };
    }
}

#[cfg(feature = "port")]
impl Lookups for TypingLookups {
    fn lookup_prop(&self, name: &str, with_type: bool) {
        use crate::decl_entry;
        use crate::typing_env;
        let mut env = self.env.borrow_mut();
        let ce = match typing_env::get_class(&env, &self.class_name) {
            decl_entry::T::Found(cls) => typing_env::get_prop(&env, &cls, name),
            _ => None,
        };
        if let (Some(ce), true) = (ce, with_type) {
            let ty = (*ce.ce_type).clone();
            Self::type_does_not_require_init(&mut env, &ty);
        }
    }

    fn static_prop_hint(&self, hint: &nast::Hint) {
        let mut env = self.env.borrow_mut();
        let ty = crate::decl_hint::hint(&env.decl_env, hint);
        Self::type_does_not_require_init(&mut env, &ty);
    }

    fn get_fun(&self, name: &str) {
        let env = self.env.borrow();
        let _ = crate::typing_env::get_fun(&env, name);
    }

    fn static_meth(&self, class_id: &nast::ClassId_, meth_name: &str) {
        use crate::decl_entry;
        use crate::typing_env;
        let env = self.env.borrow();
        let class_name = match class_id {
            nast::ClassId_::CI(nast::Id(_, cls_id)) => Some(cls_id.clone()),
            nast::ClassId_::CIself | nast::ClassId_::CIstatic => typing_env::get_self_id(&env),
            nast::ClassId_::CIparent => typing_env::get_parent_id(&env),
            nast::ClassId_::CIexpr(_) | nast::ClassId_::CIreified(_) => None,
        };
        if let Some(class_name) = class_name {
            if let decl_entry::T::Found(cls) = typing_env::get_class(&env, &class_name) {
                let _ = typing_env::get_static_member(true, &env, &cls, meth_name);
            }
        }
    }

    fn class_prop_pos(&self, name: &str) {
        use crate::decl_entry;
        use crate::typing_env;
        let env = self.env.borrow();
        if let decl_entry::T::Found(decl) = typing_env::get_class(&env, &self.class_name) {
            let _ = typing_env::get_prop(&env, &decl, name);
        }
    }
}

fn class_with_lookups(
    ctx: &Ctx,
    c: &nast::Class_,
    out: &mut Errors,
    lookups: Option<&dyn Lookups>,
) {
    // `Typing_class.class_def` checks nothing when there is no declaration
    // for the class.
    let Ok(Some(folded)) = ctx.folded_decls.get_class(TypeName::new(&c.name.1)) else {
        return;
    };
    // The declarations are those of the first class of that name: this may be
    // another one (which OCaml checks against those declarations all the
    // same).
    let is_declared_here = folded.pos.clone().to_oxidized() == c.name.0;
    let typer = Typer {
        ctx,
        class: c,
        folded,
        unknown: Cell::new(false),
        lookups,
    };

    let is_hhi = matches!(c.mode, Mode::Mhhi);
    if !is_hhi {
        let shallow = ctx
            .shallow_decls
            .get_class(typer.folded.name)
            .ok()
            .flatten();
        for cv in &c.vars {
            match &cv.expr {
                Some(_) if is_lateinit(cv) => {
                    out.add(NastCheckError::LateinitWithDefault(cv.id.0.clone()));
                }
                None if cv.is_static => {
                    if is_lateinit(cv) || cv.abstract_ {
                        continue;
                    }
                    // `type_does_not_require_init` of `Decl_hint.hint` of the
                    // hint of the property, which is the type the property
                    // is declared with.
                    let requires_init = match &cv.type_.1 {
                        None => Requires::No,
                        Some(hint) => {
                            if let Some(lookups) = typer.lookups {
                                lookups.static_prop_hint(hint);
                            }
                            let prop =
                                shallow
                                    .as_ref()
                                    .filter(|_| is_declared_here)
                                    .and_then(|shallow| {
                                        shallow.static_props.iter().find(|prop| {
                                            let name = prop.name.id_ref().as_str();
                                            name.strip_prefix('$').unwrap_or(name) == cv.id.1
                                        })
                                    });
                            match prop {
                                Some(prop) => typer.requires_init(&prop.ty, TyContext::OWN, FUEL),
                                None => Requires::Unknown,
                            }
                        }
                    };
                    // Nothing is reported when the answer is not known.
                    if requires_init == Requires::Yes {
                        out.add(NastCheckError::MissingAssign(cv.id.0.clone()));
                    }
                }
                _ => {}
            }
        }
    }

    let c_constructor = di_check::constructor(c);
    let skip = match c_constructor {
        _ if matches!(c.kind, ClassishKind::Cinterface) => true,
        Some(_) if is_hhi => true,
        // If we're checking a `__Native` constructor then all bets are off:
        // there's no way to verify that properties are initialized
        // correctly, including if we've called parent::__construct.
        // (`Typing_native.is_native_meth`: `is_systemlib` and `__Native`.
        // While `is_systemlib` is not known, see `tcopt`, a `__Native`
        // constructor is skipped all the same: whether its class is checked
        // depends on the option.)
        Some(m)
            if tcopt::is_systemlib(ctx) != Some(false)
                && attrs::mem(sn::user_attributes::NATIVE, &m.user_attributes) =>
        {
            true
        }
        _ => false,
    };
    if skip {
        return;
    }

    let p = match c_constructor {
        Some(m) => &m.name.0,
        None => &c.name.0,
    };
    // What is found from here on is only reported at the end, if every type
    // that had to be understood was.
    let mut found = Errors::default();
    let errors = &mut found;
    let env = Env::make(typer, errors);
    let mut checker = Checker { env, errors };
    let inits = checker.constructor(c_constructor);
    let Checker { env, errors } = checker;

    let is_trait_or_abstract = matches!(
        c.kind,
        ClassishKind::Ctrait | ClassishKind::Cclass(oxidized::ast_defs::Abstraction::Abstract)
    );
    let has_constructor = c_constructor.is_some_and(|m| !m.abstract_);
    // `check_throws_or_init_all`: when the constructor always throws,
    // checking that all properties are initialized is irrelevant.
    if let (S::Set(inits), true) = (inits, !is_trait_or_abstract || has_constructor) {
        // `check_inits`
        let uninit_props: BTreeSet<&str> = env
            .props
            .iter()
            .copied()
            .filter(|k| !inits.contains(k))
            .collect();
        if !uninit_props.is_empty() {
            if uninit_props.contains(PARENT_INIT_PROP) {
                errors.add(NastCheckError::NoConstructParent(p.clone()));
            } else {
                let class_uninit_props: Vec<&str> = uninit_props
                    .iter()
                    .copied()
                    .filter(|prop| !env.init_not_required_props.contains(prop))
                    .collect();
                if !class_uninit_props.is_empty() && !is_hhi {
                    errors.add(NastCheckError::NotInitialized {
                        pos: p.clone(),
                        class_name: c.name.1.clone(),
                        props: class_uninit_props
                            .into_iter()
                            .map(|name| (env.typer.class_prop_pos(name), name.to_string()))
                            .collect(),
                    });
                }
            }
        }
    }
    if !env.typer.unknown.get() {
        out.0.extend(found.0);
    }
}
