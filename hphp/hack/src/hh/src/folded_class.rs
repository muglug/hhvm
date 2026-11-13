// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `folded_class.ml`. See `hh/PORTING.md`.
//!
//! The class API of the typechecker (`Cls` in the OCaml typing code): a view
//! of a folded class (`ty::decl::FoldedClass`) that includes all inherited
//! members and their types.
//!
//! A folded class does not hold the types of its methods and properties, only
//! the class each of them comes from (`ty::decl::FoldedElement`). The type of
//! a member is found in the shallow declaration of that class and brought to
//! the folded class by the substitutions the folded class recorded
//! (`FoldedClass::substs`). The OCaml does this in `Decl_class`, through
//! `Decl_members`; hackrs has no equivalent (its `ShallowDeclStore` gives the
//! type a member was declared with, nothing more).
//!
//! `Folded_class` is built from five OCaml modules that have no file in this
//! crate. What `Folded_class` and `Decl_provider` use of them is ported here,
//! each in a module named after it, ready to be moved to a file of its own:
//!
//! - [`typing_class_types`] (`typing/typing_class_types.ml`);
//! - [`decl_counters`] (`decl/decl_counters.ml`);
//! - [`decl_class`] (`decl/decl_class.ml`);
//! - [`decl_members`] (`decl/decl_members.ml`, applied to
//!   `Decl_enforceability_shallow.Provider`);
//! - [`decl_inherit`] (`decl/decl_inherit.ml`: `find_overridden_method`
//!   only).
//!
//! None of the functions here records a dependency: as in the OCaml, that is
//! done by the functions of `Typing_env` that wrap them.

use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;
use std::sync::Arc;
use std::sync::LazyLock;
use std::sync::Mutex;

use hash::IndexMap;
use naming_special_names_rust as sn;
use oxidized::aast_defs::PackageMembership;
use oxidized::ast_defs::ClassishKind;
use oxidized::ast_defs::XhpEnumValue;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use oxidized::typing_defs::PackageRequirement;
use oxidized::typing_defs_core::CeVisibility;
use oxidized::typing_defs_core::ConsistentKind;
use oxidized::typing_defs_flags::ClassEltFlags;
use pos::BPos;
use pos::ClassConstName;
use pos::MethodName;
use pos::PropName;
use pos::ToOxidized;
use pos::TypeConstName;
use pos::TypeName;
use ty::decl::ClassConst;
use ty::decl::EnumType;
use ty::decl::FoldedClass;
use ty::decl::Requirement;
use ty::decl::Tparam;
use ty::decl::Ty;
use ty::decl::Ty_;
use ty::decl::TypeConst;
use ty::decl::folded::ConstraintRequirement;
use ty::decl_error::DeclError;

use crate::ctx::Ctx;
use crate::ctx::R;
use crate::decl_provider::decl_provider_internals;
use crate::decl_utils;
use crate::folded_class::decl_counters::SubdeclKind;
use crate::folded_class::typing_class_types::ClassT as TypingClassT;

/// `'a Lazy.t`: computed the first time it is dereferenced, and shared by its
/// clones.
pub type Lazy<A> = Arc<LazyLock<A, Box<dyn FnOnce() -> A + Send>>>;

/// `lazy (f ())`
pub fn lazy<A>(f: impl FnOnce() -> A + Send + 'static) -> Lazy<A> {
    Arc::new(LazyLock::new(Box::new(f)))
}

/// `Typing_defs.class_elt`: a method or a property of a class, inherited ones
/// included.
///
/// `oxidized::typing_defs::ClassElt` is not it: its type is an oxidized type
/// that has to be there when the element is built, whereas the type of an
/// element is a decl type (`ty::decl::Ty`) that is only looked up when it is
/// asked for (`Lazy.force ce.ce_type` is `&*ce.ce_type`, or
/// `LazyLock::force(&ce.ce_type)`).
#[derive(Clone)]
pub struct ClassElt {
    pub ce_visibility: CeVisibility,
    pub ce_type: Lazy<Ty<R>>,
    /// identifies the class from which this elt originates
    pub ce_origin: String,
    pub ce_deprecated: Option<String>,
    /// pos of the type of the elt
    pub ce_pos: Lazy<PosOrDecl>,
    pub ce_flags: ClassEltFlags,
    pub ce_sealed_allowlist: Option<im::OrdSet<String>>,
    pub ce_overlapping_tparams: Option<im::OrdSet<String>>,
    pub ce_package_requirement: Option<PackageRequirement>,
}

impl fmt::Debug for ClassElt {
    // `[@@deriving show]` forces the lazy values.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ClassElt")
            .field("ce_visibility", &self.ce_visibility)
            .field("ce_type", &**self.ce_type)
            .field("ce_origin", &self.ce_origin)
            .field("ce_deprecated", &self.ce_deprecated)
            .field("ce_pos", &**self.ce_pos)
            .field("ce_flags", &self.ce_flags)
            .field("ce_sealed_allowlist", &self.ce_sealed_allowlist)
            .field("ce_overlapping_tparams", &self.ce_overlapping_tparams)
            .field("ce_package_requirement", &self.ce_package_requirement)
            .finish()
    }
}

pub mod typing_class_types {
    //! Port of `typing_class_types.ml`, except for `inherited_members`, which
    //! nothing uses.

    use super::*;

    pub struct EagerMembers {
        pub props: Mutex<HashMap<String, ClassElt>>,
        pub static_props: Mutex<HashMap<String, ClassElt>>,
        pub methods: Mutex<HashMap<String, ClassElt>>,
        pub static_methods: Mutex<HashMap<String, ClassElt>>,
        pub construct: Mutex<Option<(Option<ClassElt>, ConsistentKind)>>,
    }

    pub fn create_eager_members() -> EagerMembers {
        EagerMembers {
            methods: Mutex::new(HashMap::new()),
            static_methods: Mutex::new(HashMap::new()),
            props: Mutex::new(HashMap::new()),
            static_props: Mutex::new(HashMap::new()),
            construct: Mutex::new(None),
        }
    }

    /// class_t:
    /// This type is an abstraction layer over the way folded decls are stored, and
    /// provides a view of classes which includes all inherited members and their types.
    ///
    /// This view is constructed by merging a single heap entry for the folded class
    /// with many entries for the types of each of its members (those member entries are
    /// looked up lazily, as needed).
    ///
    /// `Decl_defs.decl_class_type * eager_members`. The members are shared by
    /// the clones of a `ClassT`, as they are by the copies of the OCaml pair.
    ///
    /// A `ClassT` lives in the class cache of one thread
    /// (`Decl_provider.get_class`), which hands out a copy at every lookup:
    /// the handles are `Rc`s so that copying one does not write the reference
    /// count of the folded class, which all the threads share.
    #[derive(Clone)]
    pub struct ClassT(pub Rc<Arc<FoldedClass<R>>>, pub Rc<EagerMembers>);

    impl fmt::Debug for ClassT {
        // `[@@deriving show]`, with `eager_members` opaque.
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.debug_tuple("")
                .field(&self.0)
                .field(&format_args!("<opaque>"))
                .finish()
        }
    }

    pub fn make_class_t(decl: Arc<FoldedClass<R>>) -> ClassT {
        ClassT(Rc::new(decl), Rc::new(create_eager_members()))
    }
}

pub mod decl_counters {
    //! Port of `decl_counters.ml`: the telemetry of decl accesses.
    //!
    //! Only the mode in which nothing is counted (`DeclingOff`, the default)
    //! is ported in full. The two others report to `Counters` and
    //! `Hack_event_logger`, which do not exist in this crate.

    use std::sync::atomic::AtomicU8;
    use std::sync::atomic::Ordering;

    /// `Hack_event_logger.PerFileProfilingConfig.profile_decling`, which has
    /// no module in this crate.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub enum ProfileDecling {
        DeclingOff,
        DeclingTopCounts,
        DeclingAllTelemetry { callstacks: bool },
    }

    /// `let mode = ref Hack_event_logger.PerFileProfilingConfig.DeclingOff`
    static MODE: AtomicU8 = AtomicU8::new(0);

    fn mode() -> ProfileDecling {
        match MODE.load(Ordering::Relaxed) {
            0 => ProfileDecling::DeclingOff,
            1 => ProfileDecling::DeclingTopCounts,
            2 => ProfileDecling::DeclingAllTelemetry { callstacks: false },
            _ => ProfileDecling::DeclingAllTelemetry { callstacks: true },
        }
    }

    #[allow(non_camel_case_types)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub enum DeclKind {
        Class,
        Fun,
        GConst,
        Typedef,
        Module_decl,
    }

    /// The idea of [origin] is so that callsites have a way of characterizing
    /// what they are, and have this characterization end up in telemetry.
    /// That's all.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub enum Origin {
        /// block, expr, statement
        Body,
        /// typing_toplevel stuff, well-formedness
        TopLevel,
        /// tast_env
        Tast,
        /// typing_variance
        Variance,
        /// typing/nast_check
        NastCheck,
        /// typing/tast_check
        TastCheck,
    }

    #[allow(non_camel_case_types)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub enum SubdeclKind<'a> {
        // Shallow
        Abstract,
        Final,
        Const,
        Kind,
        Is_xhp,
        Name,
        Module,
        Internal,
        TestsBypassVisibility,
        AllowUncheckedEnumValues,
        IsModuleLevelTrait,
        Pos,
        Tparams,
        Enum_type,
        Xhp_enum_values,
        Xhp_marked_empty,
        Sealed_whitelist,
        Docs_url,
        Decl_errors,
        Support_dynamic_type,
        // Lazy
        Construct,
        Need_init,
        Get_ancestor(&'a str),
        Has_ancestor(&'a str),
        Requires_ancestor(&'a str),
        Extends(&'a str),
        Is_disposable,
        Get_const(&'a str),
        Has_const(&'a str),
        Get_typeconst(&'a str),
        Has_typeconst(&'a str),
        Get_typeconst_enforceability(&'a str),
        Get_prop(&'a str),
        Has_prop(&'a str),
        Get_sprop(&'a str),
        Has_sprop(&'a str),
        Get_method(&'a str),
        Has_method(&'a str),
        Get_smethod(&'a str),
        Has_smethod(&'a str),
        // Eager
        Members_fully_known,
        All_ancestor_req_names,
        All_extends_ancestors,
        All_ancestors,
        All_ancestor_names,
        All_ancestor_reqs,
        Consts,
        Typeconsts,
        Props,
        SProps,
        Methods,
        SMethods,
        Overridden_method,
        // Misc
        Deferred_init_members,
    }

    /// `oxidized::decl_counters::TracingInfo` is `()`: the type is opaque
    /// there.
    #[derive(Clone, Debug)]
    pub struct TracingInfo {
        pub origin: Origin,
        pub file: relative_path::RelativePath,
    }

    /// This opaque type carries decl_counter-specific context that will be used
    /// in telemetry to relate the subdecl accessors like "get member foo of class",
    /// back to the original decl accessor "get the class named Bar" which got this
    /// specific class in the first place.
    ///
    /// (Boxed: an `Option<Decl>` is in every `Folded_class.t` that
    /// `get_class` returns, and only telemetry, which is not ported, makes
    /// one; boxed, it is one word, not the size of the fields.)
    #[derive(Clone, Debug)]
    pub struct Decl(#[allow(dead_code)] Box<DeclFields>);

    #[allow(dead_code)]
    #[derive(Clone, Debug)]
    struct DeclFields {
        /// a randomly generated ID unique to this particular top-level retrieval,
        /// i.e. invocation of get_class / get_fun / ...
        decl_id: String,
        /// name of the top-level class/fun/... that was retrieved
        decl_name: String,
        /// a classification of what larger purpose the code was engaged in,
        /// at the moment of top-level decl retrieval.
        decl_origin: Option<Origin>,
        /// the file we were typechecking at the moment of top-level decl retrieval.
        decl_file: Option<relative_path::RelativePath>,
        /// callstack at the moment of top-level decl retrieval.
        decl_callstack: Option<String>,
        /// wall-time at the moment of top-level decl retrieval
        decl_start_time: f64,
    }

    pub fn set_mode(new_mode: ProfileDecling) {
        let mode = match new_mode {
            ProfileDecling::DeclingOff => 0,
            ProfileDecling::DeclingTopCounts => 1,
            ProfileDecling::DeclingAllTelemetry { callstacks: false } => 2,
            ProfileDecling::DeclingAllTelemetry { callstacks: true } => 3,
        };
        MODE.store(mode, Ordering::Relaxed)
    }

    /// E.g. 'count_decl Class "Foo" (fun d -> <implementation>)'. The idea is that
    /// <implementation> is the body of work which fetches the decl of class "foo",
    /// and we want to record telemetry about its performance.
    ///
    /// The callback takes a parameter [d]. This is for use of subsidiary decl accessors,
    /// e.g. 'count_subdecl d (Get_method "bar") (fun () -> <implementation2>)'.
    /// [d] is optional; it will be None if e.g. the original call to count_decl established
    /// that no telemetry should be collected during this run.
    pub fn count_decl<A>(
        tracing_info: Option<&TracingInfo>,
        decl_kind: DeclKind,
        decl_name: &str,
        f: impl FnOnce(Option<Decl>) -> A,
    ) -> A {
        match mode() {
            ProfileDecling::DeclingOff => {
                // CARE! This path must be highly performant.
                f(None)
            }
            ProfileDecling::DeclingTopCounts => {
                todo!("Counters.count Counters.Category.Decl_provider_get: Counters is not ported")
            }
            ProfileDecling::DeclingAllTelemetry { callstacks: _ } => {
                let _ = (tracing_info, decl_kind, decl_name);
                todo!(
                    "Hack_event_logger.ProfileDecl.count_decl: Hack_event_logger is not ported (nor Random_id, for the id of the decl)"
                )
            }
        }
    }

    /// E.g. 'count_subdecl d (Get_method "bar") (fun () -> <implementation2>)'. The idea
    /// is that <implementation2> is the body of work which fetches the decl of method 'bar'
    /// of some class, and we want to record telemetry about its performance.
    pub fn count_subdecl<A>(
        decl: Option<&Decl>,
        subdecl_kind: SubdeclKind<'_>,
        f: impl FnOnce() -> A,
    ) -> A {
        match decl {
            None => {
                // CARE! This path must be highly performant. It's called tens of thousands of times
                // per file. The earlier function count_decl had used "decl=None" to signal that no logging
                // is needed for subdecl accesses, and here we're (cheaply) picking up that fact.
                f()
            }
            Some(_decl) => {
                let _ = subdecl_kind;
                todo!("Hack_event_logger.ProfileDecl.count_decl: Hack_event_logger is not ported")
            }
        }
    }
}

pub mod decl_members {
    //! Port of `decl_members.ml`:
    //! `Decl_members.Make (Decl_enforceability_shallow.Provider)`.
    //!
    //! This modules transforms member types from Shallow_decl_defs like
    //! `shallow_method` into member types from Typing_defs like `fun_elt`.
    //! It may perform pessimization along the way.

    use ty::decl::ShallowClass;
    use ty::decl::ShallowMethod;
    use ty::decl::ShallowProp;
    use ty::decl::ty::FunElt;

    use super::*;
    use crate::decl_enforceability::FunKind;
    // module Pessimize = Decl_enforceability.Pessimize (Provider)
    use crate::decl_enforceability::pessimize;
    use crate::decl_provider::decl_enforceability_shallow::Provider;

    /// May pessimize the property.
    pub fn build_property(
        ctx: &Arc<Ctx>,
        this_class: Option<&Arc<ShallowClass<R>>>,
        sp: &ShallowProp<R>,
    ) -> Ty<R> {
        let ShallowProp {
            name: _,
            xhp_attr: sp_xhp_attr,
            ty: sp_type,
            visibility: _,
            flags: sp_flags,
        } = sp;
        let is_xhp_attr = sp_xhp_attr.is_some();
        let no_auto_likes = sp_flags.no_auto_likes();
        pessimize::pessimise_prop_type::<Provider>(
            is_xhp_attr,
            this_class,
            no_auto_likes,
            ctx,
            &decl_utils::get_pos(sp_type),
            sp_type,
        )
    }

    pub fn build_constructor(sm: &ShallowMethod<R>) -> FunElt<R> {
        let ShallowMethod {
            name: sm_name,
            ty: sm_type,
            visibility: _,
            deprecated: sm_deprecated,
            flags: _,
            attributes: _,
            package_requirement: sm_package_requirement,
        } = sm;
        let fe_pos = sm_name.pos();
        FunElt {
            module: None,
            package: None,
            pos: fe_pos.clone(),
            internal: false,
            deprecated: *sm_deprecated,
            ty: sm_type.clone(),
            php_std_lib: false,
            support_dynamic_type: false,
            no_auto_dynamic: false,
            no_auto_likes: false,
            gated_by_feature_flag: None,
            package_requirement: sm_package_requirement.clone(),
        }
    }

    /// May pessimize the method.
    pub fn build_method(
        ctx: &Arc<Ctx>,
        this_class: Option<&Arc<ShallowClass<R>>>,
        no_auto_likes: bool,
        sm: &ShallowMethod<R>,
    ) -> FunElt<R> {
        let ShallowMethod {
            name: sm_name,
            ty: sm_type,
            visibility: sm_visibility,
            deprecated: _,
            flags: sm_flags,
            attributes: sm_attributes,
            package_requirement: sm_package_requirement,
        } = sm;
        let pos = sm_name.pos();
        let support_dynamic_type = sm_flags.supports_dynamic_type();
        let fe_no_auto_dynamic =
            decl_utils::attributes_mem(sn::user_attributes::NO_AUTO_DYNAMIC, sm_attributes);
        let fe_no_auto_likes = no_auto_likes
            || decl_utils::attributes_mem(sn::user_attributes::NO_AUTO_LIKES, sm_attributes);
        let cannot_override = match this_class {
            Some(c) => {
                c.is_final
                    || sm_flags.is_final()
                    || *sm_visibility == oxidized::ast_defs::Visibility::Private
                        && !(c.kind == ClassishKind::Ctrait)
            }
            None => true,
        };
        FunElt {
            module: None,
            package: None,
            pos: pos.clone(),
            internal: false,
            deprecated: None,
            ty: if !fe_no_auto_dynamic
                && pessimize::implicit_sdt_for_class::<Provider>(ctx, this_class)
            {
                pessimize::pessimise_fun_type::<Provider>(
                    if sm_flags.is_abstract() {
                        FunKind::AbstractMethod
                    } else {
                        FunKind::ConcreteMethod
                    },
                    this_class,
                    fe_no_auto_likes,
                    cannot_override,
                    ctx,
                    pos,
                    sm_type,
                )
            } else {
                sm_type.clone()
            },
            php_std_lib: false,
            support_dynamic_type,
            no_auto_dynamic: fe_no_auto_dynamic,
            no_auto_likes: fe_no_auto_likes,
            gated_by_feature_flag: None,
            package_requirement: sm_package_requirement.clone(),
        }
    }
}

pub mod decl_class {
    //! Port of `decl_class.ml`.
    //!
    //! This modules deals with looking up class members of folded classes.
    //! Folded classes do not store type information of their members for storage
    //! efficiency, since folded class members pertains to multiple folded classes.
    //! Therefore we need to lookup type information for those members from inside
    //! shallow classes. This is what this module does.

    use ty::decl::FoldedElement;
    use ty::decl::SubstContext;
    use ty::decl::folded::Constructor;
    use ty::decl::ty::FunElt;

    // module Members = Decl_members.Make (Decl_enforceability_shallow.Provider)
    use super::decl_members as members;
    use super::*;
    use crate::decl_instantiate as inst;

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub enum MemberLookupError {
        MLEShallowClassNotFound,
        MLEMemberNotFound,
    }

    fn show_member_lookup_error(err: MemberLookupError) -> &'static str {
        match err {
            MemberLookupError::MLEShallowClassNotFound => "Decl_class.MLEShallowClassNotFound",
            MemberLookupError::MLEMemberNotFound => "Decl_class.MLEMemberNotFound",
        }
    }

    /// Raise an exception when the class element can't be found.
    ///
    /// Note that this exception can be raised in two modes:
    ///
    /// 1. A Provider_context.t was not available (e.g, Zoncolan execution) and the
    ///    element was not in the member heaps. A bug in decling or invalidation has
    ///    occurred, potentially due to files being changed on disk while Hack was
    ///    decling. No [member_lookup_error] is available, because we didn't do
    ///    a lazy member lookup.
    /// 2. A Provider_context.t was available (regular Hack execution with eviction),
    ///    the element was not in the member heap, so we tried falling back to disk.
    ///    However, the element could not be found in the origin class. This might be
    ///    due to an inconsistent decl heap (e.g., due to files being changed on disk
    ///    while Hack was decling) or because the file containing the element was
    ///    changed while type checking. In this case, we have a
    ///    [member_lookup_error] available.
    ///
    /// `exception Decl_heap_elems_bug of string` is a panic: nothing in the
    /// typechecker handles it.
    fn raise_decl_heap_elems_bug(
        err: Option<MemberLookupError>,
        child_class_name: &str,
        elt_origin: &str,
        member_name: &str,
    ) -> ! {
        let data = format!(
            "could not find {}::{} (inherited by {}) ({})",
            elt_origin,
            member_name,
            child_class_name,
            err.map(show_member_lookup_error)
                .unwrap_or("no lazy member lookup performed")
        );
        // `Hh_logger.log` and `Hack_event_logger.decl_consistency_bug` only log.
        panic!("Decl_class.Decl_heap_elems_bug({:?})", data)
    }

    fn unpack_member_lookup_result<A>(
        child_class_name: &str,
        elt_origin: &str,
        member_name: &str,
        res: Option<Result<A, MemberLookupError>>,
    ) -> A {
        let res = match res {
            None => Err(None),
            Some(res) => res.map_err(Some),
        };
        match res {
            Ok(a) => a,
            Err(err) => raise_decl_heap_elems_bug(err, child_class_name, elt_origin, member_name),
        }
    }

    fn apply_substs(
        substs: &IndexMap<TypeName, SubstContext<R>>,
        class_context: TypeName,
        (pos, ty): (BPos, Ty<R>),
    ) -> (BPos, Ty<R>) {
        match substs.get(&class_context) {
            None => (pos, ty),
            Some(SubstContext {
                subst,
                class_context: next_class_context,
                from_req_extends: _,
            }) => apply_substs(
                substs,
                *next_class_context,
                (pos, inst::instantiate(subst, &ty)),
            ),
        }
    }

    fn element_to_class_elt(pty: Lazy<(BPos, Ty<R>)>, elt: &FoldedElement) -> ClassElt {
        let FoldedElement {
            flags: ce_flags,
            origin: ce_origin,
            visibility: ce_visibility,
            deprecated: ce_deprecated,
            sealed_allowlist: ce_sealed_allowlist,
            overlapping_tparams: ce_overlapping_tparams,
            package_requirement: ce_package_requirement,
        } = elt;
        let (ce_pos, ce_type) = {
            let pty2 = Arc::clone(&pty);
            (
                lazy(move || PosOrDecl::from(LazyLock::force(&pty2).0.clone())),
                lazy(move || LazyLock::force(&pty).1.clone()),
            )
        };
        ClassElt {
            ce_visibility: ce_visibility.clone().to_oxidized(),
            ce_origin: ce_origin.as_str().to_string(),
            ce_type,
            ce_deprecated: ce_deprecated.map(|x| String::from_utf8_lossy(x.as_bytes()).to_string()),
            ce_pos,
            ce_flags: *ce_flags,
            ce_sealed_allowlist: (ce_sealed_allowlist.as_ref())
                .map(|s| s.iter().map(|x| x.as_str().to_string()).collect()),
            ce_overlapping_tparams: (ce_overlapping_tparams.as_ref())
                .map(|s| s.iter().map(|x| x.as_str().to_string()).collect()),
            ce_package_requirement: ce_package_requirement.clone(),
        }
    }

    fn fun_elt_to_ty(fe: FunElt<R>) -> (BPos, Ty<R>) {
        (fe.pos, fe.ty)
    }

    /// `Decl_store.lookup_or ~bypass kind x f`, where `bypass` is false without
    /// a context and `not (Typechecker_options.populate_member_heaps tcopt)`
    /// with one.
    ///
    /// The member heaps of `Decl_store` hold what `f` computes (class folding
    /// puts it there, and `lookup_or` does when it is missing): they are a
    /// cache of `f x`. The Rust decl layer has no such heap (the member stores
    /// of hackrs's `ShallowDeclStore` hold the types the members were declared
    /// with, not the result of `Decl_members.build_*`), so the result is
    /// always `f x`, as it is in the OCaml when `bypass` is true.
    fn lookup_store_or<K, V>(_ctx: Option<&Arc<Ctx>>, x: K, f: impl FnOnce(K) -> V) -> V {
        f(x)
    }

    fn find_method_in_shallow_class(
        ctx: &Arc<Ctx>,
        is_static: bool,
        elt_origin: &str,
        no_auto_likes: bool,
        sm_name: &str,
    ) -> Result<FunElt<R>, MemberLookupError> {
        match decl_provider_internals::get_shallow_class(ctx, elt_origin) {
            None => Err(MemberLookupError::MLEShallowClassNotFound),
            Some(class_) => {
                let methods = if is_static {
                    &class_.static_methods
                } else {
                    &class_.methods
                };
                match (methods.iter()).find(|m| m.name.id_ref().as_str() == sm_name) {
                    None => Err(MemberLookupError::MLEMemberNotFound),
                    Some(sm) => Ok(members::build_method(ctx, Some(&class_), no_auto_likes, sm)),
                }
            }
        }
    }

    fn find_method(
        ctx: Option<&Arc<Ctx>>,
        child_class_name: &str,
        no_auto_likes: bool,
        x: (&str, &str),
    ) -> (BPos, Ty<R>) {
        let fun_elt = lookup_store_or(ctx, x, |x| {
            let (elt_origin, sm_name) = x;
            unpack_member_lookup_result(
                child_class_name,
                elt_origin,
                sm_name,
                ctx.map(|ctx| {
                    find_method_in_shallow_class(ctx, false, elt_origin, no_auto_likes, sm_name)
                }),
            )
        });
        fun_elt_to_ty(fun_elt)
    }

    fn find_static_method(
        ctx: Option<&Arc<Ctx>>,
        child_class_name: &str,
        no_auto_likes: bool,
        x: (&str, &str),
    ) -> (BPos, Ty<R>) {
        let fun_elt = lookup_store_or(ctx, x, |x| {
            let (elt_origin, sm_name) = x;
            unpack_member_lookup_result(
                child_class_name,
                elt_origin,
                sm_name,
                ctx.map(|ctx| {
                    find_method_in_shallow_class(ctx, true, elt_origin, no_auto_likes, sm_name)
                }),
            )
        });
        fun_elt_to_ty(fun_elt)
    }

    fn find_property_in_shallow_class(
        ctx: &Arc<Ctx>,
        elt_origin: &str,
        sp_name: &str,
    ) -> Result<Ty<R>, MemberLookupError> {
        match decl_provider_internals::get_shallow_class(ctx, elt_origin) {
            None => Err(MemberLookupError::MLEShallowClassNotFound),
            Some(class_) => {
                match (class_.props.iter()).find(|prop| prop.name.id_ref().as_str() == sp_name) {
                    None => Err(MemberLookupError::MLEMemberNotFound),
                    Some(sp) => Ok(members::build_property(ctx, Some(&class_), sp)),
                }
            }
        }
    }

    fn find_property(
        ctx: Option<&Arc<Ctx>>,
        child_class_name: &str,
        x: (&str, &str),
    ) -> (BPos, Ty<R>) {
        let ty = lookup_store_or(ctx, x, |x| {
            let (elt_origin, sp_name) = x;
            unpack_member_lookup_result(
                child_class_name,
                elt_origin,
                sp_name,
                ctx.map(|ctx| find_property_in_shallow_class(ctx, elt_origin, sp_name)),
            )
        });
        (decl_utils::get_pos(&ty), ty)
    }

    fn find_static_property_in_shallow_class(
        ctx: &Arc<Ctx>,
        elt_origin: &str,
        sp_name: &str,
    ) -> Result<Ty<R>, MemberLookupError> {
        match decl_provider_internals::get_shallow_class(ctx, elt_origin) {
            None => Err(MemberLookupError::MLEShallowClassNotFound),
            Some(class_) => {
                match (class_.static_props.iter())
                    .find(|prop| prop.name.id_ref().as_str() == sp_name)
                {
                    None => Err(MemberLookupError::MLEMemberNotFound),
                    Some(sp) => Ok(members::build_property(ctx, Some(&class_), sp)),
                }
            }
        }
    }

    fn find_static_property(
        ctx: Option<&Arc<Ctx>>,
        child_class_name: &str,
        x: (&str, &str),
    ) -> (BPos, Ty<R>) {
        let ty = lookup_store_or(ctx, x, |x| {
            let (elt_origin, sp_name) = x;
            unpack_member_lookup_result(
                child_class_name,
                elt_origin,
                sp_name,
                ctx.map(|ctx| find_static_property_in_shallow_class(ctx, elt_origin, sp_name)),
            )
        });
        (decl_utils::get_pos(&ty), ty)
    }

    fn find_constructor_in_shallow_class(
        ctx: &Arc<Ctx>,
        elt_origin: &str,
    ) -> Result<FunElt<R>, MemberLookupError> {
        match decl_provider_internals::get_shallow_class(ctx, elt_origin) {
            None => Err(MemberLookupError::MLEShallowClassNotFound),
            Some(class_) => match &class_.constructor {
                None => Err(MemberLookupError::MLEMemberNotFound),
                Some(method_) => Ok(members::build_constructor(method_)),
            },
        }
    }

    fn find_constructor(
        ctx: Option<&Arc<Ctx>>,
        child_class_name: &str,
        elt_origin: &str,
    ) -> FunElt<R> {
        lookup_store_or(ctx, elt_origin, |elt_origin| {
            unpack_member_lookup_result(
                child_class_name,
                elt_origin,
                sn::members::__CONSTRUCT,
                ctx.map(|ctx| find_constructor_in_shallow_class(ctx, elt_origin)),
            )
        })
    }

    /// The OCaml is given `dc.dc_substs`. The lazy value has to own them: it is
    /// given the folded class they are part of.
    fn map_element(
        dc: &Arc<FoldedClass<R>>,
        find: impl FnOnce((&str, &str)) -> (BPos, Ty<R>) + Send + 'static,
        name: &str,
        elt: &FoldedElement,
    ) -> ClassElt {
        let pty = {
            let dc = Arc::clone(dc);
            let elt_origin = elt.origin;
            let name = name.to_string();
            lazy(move || {
                let pty = find((elt_origin.as_str(), &name));
                apply_substs(&dc.substs, elt_origin, pty)
            })
        };
        element_to_class_elt(pty, elt)
    }

    /// Lookup the type signature of a class property.
    ///
    /// [Decl_defs.element] only points to where the type signature of an element
    /// can be found (i.e. in which class). This function looks up the actual type
    /// signature and returns it, together with the original metadata.
    ///
    /// If no [Provider_context.t] is passed or it cannot be found
    /// a [Decl_heap_elems_bug] exception is raised.
    ///
    /// Note that the lookup is lazy. The type signature is wrapped in a lazy value.
    /// The lookup will only happen when you try to force the lazy value. (See the
    /// definition of [Typing_defs.class_elt].)
    pub fn lookup_property_type_lazy(
        ctx: Option<&Arc<Ctx>>,
        dc: &Arc<FoldedClass<R>>,
        name: &str,
        elt: &FoldedElement,
    ) -> ClassElt {
        let ctx = ctx.cloned();
        let child_class_name = dc.name;
        map_element(
            dc,
            move |x| find_property(ctx.as_ref(), child_class_name.as_str(), x),
            name,
            elt,
        )
    }

    /// Lookup the type of a class static property.
    ///
    /// See [lookup_property_type_lazy] for more information.
    pub fn lookup_static_property_type_lazy(
        ctx: Option<&Arc<Ctx>>,
        dc: &Arc<FoldedClass<R>>,
        name: &str,
        elt: &FoldedElement,
    ) -> ClassElt {
        let ctx = ctx.cloned();
        let child_class_name = dc.name;
        map_element(
            dc,
            move |x| find_static_property(ctx.as_ref(), child_class_name.as_str(), x),
            name,
            elt,
        )
    }

    /// Lookup the type of a class method.
    ///
    /// See [lookup_property_type_lazy] for more information.
    pub fn lookup_method_type_lazy(
        ctx: Option<&Arc<Ctx>>,
        dc: &Arc<FoldedClass<R>>,
        name: &str,
        element: &FoldedElement,
    ) -> ClassElt {
        let ctx = ctx.cloned();
        let child_class_name = dc.name;
        let no_auto_likes = element.flags.contains(ClassEltFlags::NO_AUTO_LIKES);
        map_element(
            dc,
            move |x| find_method(ctx.as_ref(), child_class_name.as_str(), no_auto_likes, x),
            name,
            element,
        )
    }

    /// Lookup the type of a class static method.
    ///
    /// See [lookup_property_type_lazy] for more information.
    pub fn lookup_static_method_type_lazy(
        ctx: Option<&Arc<Ctx>>,
        dc: &Arc<FoldedClass<R>>,
        name: &str,
        element: &FoldedElement,
    ) -> ClassElt {
        let ctx = ctx.cloned();
        let child_class_name = dc.name;
        let no_auto_likes = element.flags.contains(ClassEltFlags::NO_AUTO_LIKES);
        map_element(
            dc,
            move |x| find_static_method(ctx.as_ref(), child_class_name.as_str(), no_auto_likes, x),
            name,
            element,
        )
    }

    /// Lookup the type of a class constructor.
    ///
    /// See [lookup_property_type_lazy] for more information.
    ///
    /// The OCaml is given `dc_substs` and `dc_construct`. The lazy value has to
    /// own the substitutions: this is given the folded class they are part of
    /// (`dc.substs`, and `dc.constructor` for `dc_construct`).
    pub fn lookup_constructor_lazy(
        ctx: Option<&Arc<Ctx>>,
        child_class_name: &str,
        dc: &Arc<FoldedClass<R>>,
    ) -> (Option<ClassElt>, ConsistentKind) {
        let Constructor { elt, consistency } = &dc.constructor;
        match (elt, *consistency) {
            (None, consistent) => (None, consistent),
            (Some(elt), consistent) => {
                let pty = {
                    let ctx = ctx.cloned();
                    let child_class_name = child_class_name.to_string();
                    let dc = Arc::clone(dc);
                    let elt_origin = elt.origin;
                    lazy(move || {
                        let pty = fun_elt_to_ty(find_constructor(
                            ctx.as_ref(),
                            &child_class_name,
                            elt_origin.as_str(),
                        ));
                        apply_substs(&dc.substs, elt_origin, pty)
                    })
                };
                let class_elt = element_to_class_elt(pty, elt);
                (Some(class_elt), consistent)
            }
        }
    }
}

pub mod decl_inherit {
    //! Port of `Decl_inherit.find_overridden_method` and of what it uses in
    //! `decl_inherit.ml`.
    //!
    //! The rest of `decl_inherit.ml`, the inheritance of members when a class
    //! is folded, is hackrs's (`folded_decl_provider/inherit.rs`, which is
    //! private to class folding).

    use oxidized::ast_defs::Abstraction;
    use ty::decl::ShallowClass;
    use ty::decl::ty::DeclConstraintRequirement;

    use super::*;

    // module Typing_defs_class_elt : Member_S with type t = Typing_defs.class_elt

    /// `Typing_defs.get_ce_abstract`
    fn is_abstract(m: &ClassElt) -> bool {
        m.ce_flags.contains(ClassEltFlags::ABSTRACT)
    }

    /// `Typing_defs.get_ce_synthesized`
    fn is_synthesized(m: &ClassElt) -> bool {
        m.ce_flags.contains(ClassEltFlags::SYNTHESIZED)
    }

    /// `Typing_defs.get_ce_lsb`
    fn has_lsb(m: &ClassElt) -> bool {
        m.ce_flags.contains(ClassEltFlags::LSB)
    }

    fn visibility(m: &ClassElt) -> &CeVisibility {
        &m.ce_visibility
    }

    /// The override precedence of a member is used to determine if a member overrides
    /// previous members from other parents with the same name.
    #[derive(Clone, Copy)]
    struct OverridePrecedence {
        is_concrete: bool,
        is_not_synthesized: bool,
    }

    impl OverridePrecedence {
        fn make(member: &ClassElt) -> Self {
            Self {
                is_concrete: !is_abstract(member),
                is_not_synthesized: !is_synthesized(member),
            }
        }

        fn to_int(self) -> isize {
            let bool_to_int = |b: bool| if b { 1 } else { 0 };
            (2 * bool_to_int(self.is_concrete)) + bool_to_int(self.is_not_synthesized)
        }

        /// `( > )`
        fn gt(self, y: Self) -> bool {
            self.to_int() > y.to_int()
        }

        fn is_highest(self) -> bool {
            self.is_concrete && self.is_not_synthesized
        }
    }

    fn is_private(member: &ClassElt) -> bool {
        match visibility(member) {
            CeVisibility::Vprivate(_) => !has_lsb(member),
            CeVisibility::Vpublic
            | CeVisibility::Vprotected(_)
            | CeVisibility::Vinternal(_)
            | CeVisibility::VprotectedInternal { .. } => false,
        }
    }

    fn parents_which_provide_members(c: &ShallowClass<R>) -> Vec<Ty<R>> {
        // /!\ For soundness, the traversal order below
        // must be consistent with traversal order for ancestors
        // used in decl_folded_class.ml
        // In an abstract class or a trait, we assume the interfaces
        // will be implemented in the future, so we take them as
        // part of the class (as requested by dependency injection implementers)
        match c.kind {
            ClassishKind::Cclass(Abstraction::Abstract) => (c.implements.iter())
                .chain(c.extends.iter())
                .cloned()
                .collect(),
            ClassishKind::Ctrait => (c.implements.iter())
                .chain(c.extends.iter())
                .chain(c.req_implements.iter())
                .cloned()
                .collect(),
            ClassishKind::Cclass(_)
            | ClassishKind::Cinterface
            | ClassishKind::Cenum
            | ClassishKind::CenumClass(_) => c.extends.to_vec(),
        }
    }

    fn has_highest_precedence<A>(x: &Option<(OverridePrecedence, A)>) -> bool {
        match x {
            Some((precedence, _)) => precedence.is_highest(),
            _ => false,
        }
    }

    fn max_precedence<A>(
        x: Option<(OverridePrecedence, A)>,
        y: Option<(OverridePrecedence, A)>,
    ) -> Option<(OverridePrecedence, A)> {
        // Option.merge
        match (x, y) {
            (None, y) => y,
            (x, None) => x,
            (Some(x), Some(y)) => {
                let (x_precedence, y_precedence) = (x.0, y.0);
                if y_precedence.gt(x_precedence) {
                    Some(y)
                } else {
                    Some(x)
                }
            }
        }
    }

    /// `( >?? )`
    fn or_max_precedence<A>(
        x: Option<(OverridePrecedence, A)>,
        y: impl FnOnce() -> Option<(OverridePrecedence, A)>,
    ) -> Option<(OverridePrecedence, A)> {
        if has_highest_precedence(&x) {
            x
        } else {
            max_precedence(x, y())
        }
    }

    fn find_first_with_highest_precedence<X, A>(
        l: &[X],
        mut f: impl FnMut(&X) -> Option<(OverridePrecedence, A)>,
    ) -> Option<(OverridePrecedence, A)> {
        let mut found = None;
        for x in l {
            let x = f(x);
            if has_highest_precedence(&x) {
                return x;
            } else {
                found = max_precedence(found, x)
            }
        }
        found
    }

    #[derive(Clone, Copy)]
    enum ParentKind {
        Parent,
        Requirement,
        Trait,
    }

    type Parent = Ty<R>;

    mod ordered_parents {
        use super::*;

        pub struct T(Vec<(ParentKind, Vec<Parent>)>);

        /// `Shallow_decl_defs.to_decl_constraint`
        fn to_decl_constraint(dcr: &DeclConstraintRequirement<R>) -> Ty<R> {
            match dcr {
                DeclConstraintRequirement::DCREqual(ty)
                | DeclConstraintRequirement::DCRSubtype(ty) => ty.clone(),
            }
        }

        /// This provides the parent traversal order for member folding.
        /// This is appropriate for all members except XHP attributes and constants.
        /// The order is different for those and these are handled elsewhere.
        pub fn get(c: &ShallowClass<R>) -> T {
            // /!\ For soundness, the traversal order below
            // must be consistent with traversal order for ancestors
            // used in decl_folded_class.ml
            T(vec![
                (
                    ParentKind::Parent,
                    parents_which_provide_members(c).into_iter().rev().collect(),
                ),
                (
                    ParentKind::Requirement,
                    (c.req_constraints.iter().map(to_decl_constraint))
                        .chain(c.req_extends.iter().cloned())
                        .collect(),
                ),
                (ParentKind::Trait, c.uses.to_vec()),
            ])
        }

        /// Reverse the ordered parents.
        pub fn rev(t: T) -> T {
            T((t.0.into_iter().rev())
                .map(|(parent_kind, parents)| (parent_kind, parents.into_iter().rev().collect()))
                .collect())
        }

        /// Apply [f] to each parent to obtain a result and a precedence.
        /// Return the result with the highest precedence.
        /// If two results have the same highest precedence, return the first one.
        pub fn find_map_first_with_highest_precedence<Res>(
            t: &T,
            mut f: impl FnMut(ParentKind, &Parent) -> Option<(OverridePrecedence, Res)>,
        ) -> Option<(OverridePrecedence, Res)> {
            (t.0.iter()).fold(None, |acc, (parent_kind, parents)| {
                or_max_precedence(acc, || {
                    find_first_with_highest_precedence(parents, |parent| f(*parent_kind, parent))
                })
            })
        }
    }

    pub fn find_overridden_method(
        cls: &ShallowClass<R>,
        get_method: impl Fn(&Ty<R>) -> Option<ClassElt>,
    ) -> Option<ClassElt> {
        let is_not_private = |m: &ClassElt| !is_private(m);
        let precedence = OverridePrecedence::make;
        let get_method_with_precedence = |_: ParentKind, ty: &Ty<R>| {
            get_method(ty)
                .filter(is_not_private)
                .map(|method_| (precedence(&method_), method_))
        };
        let parents = ordered_parents::rev(ordered_parents::get(cls));
        ordered_parents::find_map_first_with_highest_precedence(
            &parents,
            get_method_with_precedence,
        )
        .map(|(_, method_)| method_)
    }
}

// This entire file is "private". Its sole consumer is Decl_provider.ml.

pub type ClassT = TypingClassT;

pub fn make(x: TypingClassT) -> ClassT {
    x
}

/// This type "t" is what all APIs operate upon. It includes
/// a "decl option". This provides context about how the specified
/// class_t was fetched in the first place. It's used solely for telemetry,
/// so that telemetry about APIs can be easily correlated with telemetry
/// to the original call to the [get] which fetched the class_t in the
/// first place.
///
/// It also references the provider context that was used to query the class_t,
/// as it might be needed when querying its members when the shallow decl where it
/// was defines is evicted. For Zoncolan, this Provider_context.t is not
/// available, as Zoncolan doesn't support eviction.
#[derive(Clone)]
pub struct T(
    pub Option<decl_counters::Decl>,
    pub ClassT,
    /// An `Rc` handle that the thread shares (see `Decl_provider.get_class`),
    /// so that copying a `T` does not write the reference count of the
    /// context, which all the threads share.
    pub Option<Rc<Arc<Ctx>>>,
);

impl fmt::Debug for T {
    // `[@@deriving show]`, with the first and the last components opaque.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("")
            .field(&format_args!("<opaque>"))
            .field(&self.1)
            .field(&format_args!("<opaque>"))
            .finish()
    }
}

/// `S_map.bindings`: the bindings of a map of the folded class, in increasing
/// order of the keys.
fn bindings<K: AsRef<str>, V>(m: &IndexMap<K, V>) -> Vec<(&str, &V)> {
    let mut l: Vec<(&str, &V)> = m.iter().map(|(k, v)| (k.as_ref(), v)).collect();
    l.sort_by(|(k1, _), (k2, _)| k1.cmp(k2));
    l
}

// module ApiShallow

pub fn abstract_(t: &T) -> bool {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Abstract, || {
        let TypingClassT(c, _) = t;
        // `dc_abstract` is `Decl_folded_class.class_is_abstract`
        c.is_abstract()
    })
}

pub fn final_(t: &T) -> bool {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Final, || {
        let TypingClassT(c, _) = t;
        c.is_final
    })
}

pub fn has_const_attribute(t: &T) -> bool {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Const, || {
        let TypingClassT(c, _) = t;
        c.is_const
    })
}

pub fn kind(t: &T) -> ClassishKind {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Kind, || {
        let TypingClassT(c, _) = t;
        c.kind
    })
}

pub fn allow_multiple_instantiations(t: &T) -> bool {
    let T(_decl, TypingClassT(c, _), _ctx) = t;
    c.allow_multiple_instantiations
}

pub fn is_xhp(t: &T) -> bool {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Is_xhp, || {
        let TypingClassT(c, _) = t;
        c.is_xhp
    })
}

pub fn name(t: &T) -> String {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Name, || {
        let TypingClassT(c, _) = t;
        c.name.as_str().to_string()
    })
}

pub fn pos(t: &T) -> PosOrDecl {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Pos, || {
        let TypingClassT(c, _) = t;
        PosOrDecl::from(c.pos.clone())
    })
}

/// `Pos_or_decl.is_hhi (pos t)`, without converting the position of the
/// declaration (which allocates) only to read the prefix of its file.
pub fn pos_is_hhi(t: &T) -> bool {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Pos, || {
        let TypingClassT(c, _) = t;
        pos::Pos::is_hhi(&c.pos)
    })
}

pub fn tparams(t: &T) -> Vec<Tparam<R, Ty<R>>> {
    tparams_ref(t).to_vec()
}

/// [`tparams`], borrowed from the class: OCaml returns the list of the class
/// itself, and most callers only read it.
pub fn tparams_ref(t: &T) -> &[Tparam<R, Ty<R>>] {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Tparams, || {
        let TypingClassT(c, _) = t;
        &c.tparams[..]
    })
}

pub fn enum_type(t: &T) -> Option<EnumType<R>> {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Enum_type, || {
        let TypingClassT(c, _) = t;
        c.enum_type.clone()
    })
}

pub fn xhp_enum_values(t: &T) -> im::OrdMap<String, Vec<XhpEnumValue>> {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Xhp_enum_values, || {
        let TypingClassT(c, _) = t;
        (c.xhp_enum_values.iter())
            .map(|(k, v)| {
                (
                    k.as_str().to_string(),
                    v.iter()
                        .map(|x| x.clone().to_oxidized())
                        .collect::<Vec<_>>(),
                )
            })
            .collect()
    })
}

pub fn xhp_marked_empty(t: &T) -> bool {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Xhp_marked_empty, || {
        let TypingClassT(c, _) = t;
        c.xhp_marked_empty
    })
}

pub fn sealed_whitelist(t: &T) -> Option<im::OrdSet<String>> {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Sealed_whitelist, || {
        let TypingClassT(c, _) = t;
        (c.sealed_whitelist.as_ref()).map(|s| s.iter().map(|x| x.as_str().to_string()).collect())
    })
}

pub fn get_docs_url(t: &T) -> Option<String> {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Docs_url, || {
        let TypingClassT(c, _) = t;
        c.docs_url.clone()
    })
}

pub fn get_module(t: &T) -> Option<String> {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Module, || {
        let TypingClassT(c, _) = t;
        c.module.as_ref().map(|m| m.id_ref().as_str().to_string())
    })
}

pub fn get_package(t: &T) -> Option<PackageMembership> {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Module, || {
        let TypingClassT(c, _) = t;
        c.package.clone()
    })
}

pub fn internal(t: &T) -> bool {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Internal, || {
        let TypingClassT(c, _) = t;
        c.is_internal
    })
}

pub fn tests_bypass_visibility(t: &T) -> bool {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::TestsBypassVisibility, || {
        let TypingClassT(c, _) = t;
        c.tests_bypass_visibility
    })
}

pub fn allow_unchecked_enum_values(t: &T) -> bool {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::AllowUncheckedEnumValues, || {
        let TypingClassT(c, _) = t;
        c.allow_unchecked_enum_values
    })
}

pub fn is_module_level_trait(t: &T) -> bool {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::IsModuleLevelTrait, || {
        let TypingClassT(c, _) = t;
        c.is_module_level_trait
    })
}

pub fn decl_errors(t: &T) -> Vec<DeclError<BPos>> {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Decl_errors, || {
        let TypingClassT(c, _) = t;
        c.decl_errors.to_vec()
    })
}

pub fn get_support_dynamic_type(t: &T) -> bool {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Support_dynamic_type, || {
        let TypingClassT(c, _) = t;
        c.support_dynamic_type
    })
}

// module ApiLazy

/// Direct use of `construct` will not register a dependency. You probably
/// want to use `Typing_env.get_construct` instead
pub fn construct(t: &T) -> (Option<ClassElt>, ConsistentKind) {
    let T(decl, t, ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Construct, || {
        let TypingClassT(cls, members) = t;
        let mut construct = members.construct.lock().unwrap();
        match &*construct {
            Some(x) => x.clone(),
            None => {
                let x = decl_class::lookup_constructor_lazy(ctx.as_deref(), cls.name.as_str(), cls);
                *construct = Some(x.clone());
                x
            }
        }
    })
}

pub fn need_init(t: &T) -> bool {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Need_init, || {
        let TypingClassT(c, _) = t;
        // `dc_need_init` is `has_concrete_cstr` in `Decl_folded_class.class_decl`
        c.has_concrete_constructor()
    })
}

pub fn get_ancestor(t: &T, ancestor: &str) -> Option<Ty<R>> {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Get_ancestor(ancestor), || {
        let TypingClassT(c, _) = t;
        c.ancestors.get(&TypeName(crate::ctx::symbol(ancestor))).cloned()
    })
}

pub fn has_ancestor(t: &T, ancestor: &str) -> bool {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Has_ancestor(ancestor), || {
        let TypingClassT(c, _) = t;
        c.ancestors.contains_key(&TypeName(crate::ctx::symbol(ancestor)))
    })
}

pub fn requires_ancestor(t: &T, ancestor: &str) -> bool {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(
        decl.as_ref(),
        SubdeclKind::Requires_ancestor(ancestor),
        || {
            let TypingClassT(c, _) = t;
            c.req_ancestors_extends.contains(&TypeName(crate::ctx::symbol(ancestor)))
        },
    )
}

/// Direct use of `get_const` will not register a dependency. You probably
/// want to use `Typing_env.get_const` instead
pub fn get_const(t: &T, id: &str) -> Option<ClassConst<R>> {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Get_const(id), || {
        let TypingClassT(c, _) = t;
        c.consts.get(&ClassConstName(crate::ctx::symbol(id))).cloned()
    })
}

pub fn has_const(t: &T, id: &str) -> bool {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Has_const(id), || {
        let TypingClassT(c, _) = t;
        c.consts.contains_key(&ClassConstName(crate::ctx::symbol(id)))
    })
}

/// Direct use of `get_typeconst` will not register a dependency. You
/// probably want to use `Typing_env.get_typeconst` instead
pub fn get_typeconst(t: &T, id: &str) -> Option<TypeConst<R>> {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Get_typeconst(id), || {
        let TypingClassT(c, _) = t;
        c.type_consts.get(&TypeConstName(crate::ctx::symbol(id))).cloned()
    })
}

pub fn has_typeconst(t: &T, id: &str) -> bool {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Has_typeconst(id), || {
        let TypingClassT(c, _) = t;
        c.type_consts.contains_key(&TypeConstName(crate::ctx::symbol(id)))
    })
}

/// Return the enforceability of the typeconst with the given name. A
/// typeconst is enforceable if it was declared with the <<__Enforceable>>
/// attribute, or if it overrides some ancestor typeconst with that attribute.
/// Only enforceable typeconsts may be used in [is] or [as] expressions. The
/// overriding behavior makes this expensive to compute in shallow decl, which
/// is why this separate accessor is provided (rather than making this
/// information available in the [ttc_enforceable] field, whose semantics
/// differ between legacy and shallow decl due to the perf cost in shallow).
pub fn get_typeconst_enforceability(t: &T, id: &str) -> Option<(PosOrDecl, bool)> {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(
        decl.as_ref(),
        SubdeclKind::Get_typeconst_enforceability(id),
        || {
            let TypingClassT(c, _) = t;
            (c.type_consts.get(&TypeConstName(crate::ctx::symbol(id)))).map(|t| {
                // `ttc_enforceable`: `ty::decl::ty::Enforceable` is the position
                // of the attribute, if there is one.
                match &t.enforceable.0 {
                    Some(pos) => (PosOrDecl::from(pos.clone()), true),
                    None => (Pos::NONE, false),
                }
            })
        },
    )
}

/// Direct use of `get_prop` will not register a dependency. You probably
/// want to use `Typing_env.get_prop` instead
pub fn get_prop(t: &T, id: &str) -> Option<ClassElt> {
    let T(decl, t, ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Get_prop(id), || {
        let TypingClassT(c, members) = t;
        let mut props = members.props.lock().unwrap();
        match props.get(id) {
            Some(elt) => Some(elt.clone()),
            None => match c.props.get(&PropName(crate::ctx::symbol(id))) {
                None => None,
                Some(elt) => {
                    let elt = decl_class::lookup_property_type_lazy(ctx.as_deref(), c, id, elt);
                    props.insert(id.to_string(), elt.clone());
                    Some(elt)
                }
            },
        }
    })
}

pub fn has_prop(t: &T, id: &str) -> bool {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Has_prop(id), || {
        let TypingClassT(c, _) = t;
        c.props.contains_key(&PropName(crate::ctx::symbol(id)))
    })
}

/// Direct use of `get_sprop` will not register a dependency. You probably
/// want to use `Typing_env.get_static_member` instead
pub fn get_sprop(t: &T, id: &str) -> Option<ClassElt> {
    let T(decl, t, ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Get_sprop(id), || {
        let TypingClassT(c, members) = t;
        let mut static_props = members.static_props.lock().unwrap();
        match static_props.get(id) {
            Some(elt) => Some(elt.clone()),
            None => match c.static_props.get(&PropName(crate::ctx::symbol(id))) {
                None => None,
                Some(elt) => {
                    let elt =
                        decl_class::lookup_static_property_type_lazy(ctx.as_deref(), c, id, elt);
                    static_props.insert(id.to_string(), elt.clone());
                    Some(elt)
                }
            },
        }
    })
}

pub fn has_sprop(t: &T, id: &str) -> bool {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Has_sprop(id), || {
        let TypingClassT(c, _) = t;
        c.static_props.contains_key(&PropName(crate::ctx::symbol(id)))
    })
}

/// Direct use of `get_method` will not register a dependency. You probably
/// want to use `Typing_env.get_method` instead
pub fn get_method(t: &T, id: &str) -> Option<ClassElt> {
    let T(decl, t, ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Get_method(id), || {
        let TypingClassT(c, members) = t;
        let mut methods = members.methods.lock().unwrap();
        match methods.get(id) {
            Some(elt) => Some(elt.clone()),
            None => match c.methods.get(&MethodName(crate::ctx::symbol(id))) {
                None => None,
                Some(elt) => {
                    let elt = decl_class::lookup_method_type_lazy(ctx.as_deref(), c, id, elt);
                    methods.insert(id.to_string(), elt.clone());
                    Some(elt)
                }
            },
        }
    })
}

pub fn has_method(t: &T, id: &str) -> bool {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Has_method(id), || {
        let TypingClassT(c, _) = t;
        c.methods.contains_key(&MethodName(crate::ctx::symbol(id)))
    })
}

/// Direct use of `get_smethod` will not register a dependency. You probably
/// want to use `Typing_env.get_static_member` instead
pub fn get_smethod(t: &T, id: &str) -> Option<ClassElt> {
    let T(decl, t, ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Get_smethod(id), || {
        let TypingClassT(c, members) = t;
        let mut static_methods = members.static_methods.lock().unwrap();
        match static_methods.get(id) {
            Some(elt) => Some(elt.clone()),
            None => match c.static_methods.get(&MethodName(crate::ctx::symbol(id))) {
                None => None,
                Some(elt) => {
                    let elt = decl_class::lookup_static_method_type_lazy(ctx.as_deref(), c, id, elt);
                    static_methods.insert(id.to_string(), elt.clone());
                    Some(elt)
                }
            },
        }
    })
}

pub fn has_smethod(t: &T, id: &str) -> bool {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Has_smethod(id), || {
        let TypingClassT(c, _) = t;
        c.static_methods.contains_key(&MethodName(crate::ctx::symbol(id)))
    })
}

pub fn get_any_method(is_static: bool, cls: &T, id: &str) -> Option<ClassElt> {
    // tally is already done inside the following three methods
    if id == sn::members::__CONSTRUCT {
        construct(cls).0
    } else if is_static {
        get_smethod(cls, id)
    } else {
        get_method(cls, id)
    }
}

// module ApiEager

pub fn all_ancestor_req_names(t: &T) -> Vec<String> {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::All_ancestor_req_names, || {
        // The two below will traverse ancestors in different orders.
        // But if the typechecker discovers errors in different order, no matter.
        let TypingClassT(c, _) = t;
        // S_set.elements
        let mut names: Vec<String> = (c.req_ancestors_extends.iter())
            .map(|x| x.as_str().to_string())
            .collect();
        names.sort();
        names
    })
}

pub fn all_ancestors(t: &T) -> Vec<(String, Ty<R>)> {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::All_ancestors, || {
        let TypingClassT(c, _) = t;
        (bindings(&c.ancestors).into_iter())
            .map(|(k, ty)| (k.to_string(), ty.clone()))
            .collect()
    })
}

pub fn all_ancestor_names(t: &T) -> Vec<String> {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::All_ancestors, || {
        let TypingClassT(c, _) = t;
        // S_map.ordered_keys
        (bindings(&c.ancestors).into_iter())
            .map(|(k, _)| k.to_string())
            .collect()
    })
}

/// All the require extends and require implements requirements
/// These requirements impose a strict subtype constraint
pub fn all_ancestor_reqs(t: &T) -> Vec<Requirement<R>> {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::All_ancestor_reqs, || {
        let TypingClassT(c, _) = t;
        c.req_ancestors.to_vec()
    })
}

/// All the require class and require this as requirements
/// These requirements impose non-strict subtype constraint
/// and are not included in all_ancestor_reqs or
/// all_ancestor_req_names.
pub fn all_ancestor_req_constraints_requirements(t: &T) -> Vec<ConstraintRequirement<R>> {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::All_ancestor_reqs, || {
        let TypingClassT(c, _) = t;
        c.req_constraints_ancestors.to_vec()
    })
}

/// Projection out of all_ancestor_req_constraints_requirements
pub fn all_ancestor_req_class_requirements(t: &T) -> Vec<Requirement<R>> {
    (all_ancestor_req_constraints_requirements(t).into_iter())
        .filter_map(|r| match r {
            ConstraintRequirement::CREqual(c) => Some(c),
            ConstraintRequirement::CRSubtype(_) => None,
        })
        .collect()
}

/// Projection out of all_ancestor_req_constraints_requirements
pub fn all_ancestor_req_this_as_requirements(t: &T) -> Vec<Requirement<R>> {
    (all_ancestor_req_constraints_requirements(t).into_iter())
        .filter_map(|r| match r {
            ConstraintRequirement::CREqual(_) => None,
            ConstraintRequirement::CRSubtype(c) => Some(c),
        })
        .collect()
}

/// `Typing_defs.to_requirement`
fn to_requirement(cr: ConstraintRequirement<R>) -> Requirement<R> {
    match cr {
        ConstraintRequirement::CREqual(r) | ConstraintRequirement::CRSubtype(r) => r,
    }
}

pub fn upper_bounds_on_this(t: &T) -> Vec<Ty<R>> {
    upper_bounds_on_this_iter(t).cloned().collect()
}

/// [`upper_bounds_on_this`], borrowed from the class (in the same order: the
/// constraint requirements, then the other requirements), without copying
/// the requirements first.
pub fn upper_bounds_on_this_iter(t: &T) -> impl Iterator<Item = &Ty<R>> {
    // tally is already done by all_ancestors and upper_bounds
    let T(decl, tc, _ctx) = t;
    let TypingClassT(c, _) = tc;
    let reqs = decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::All_ancestor_reqs, || {
        &c.req_ancestors[..]
    });
    let constraint_reqs =
        decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::All_ancestor_reqs, || {
            &c.req_constraints_ancestors[..]
        });
    (constraint_reqs.iter())
        .map(|cr| match cr {
            ConstraintRequirement::CREqual(r) | ConstraintRequirement::CRSubtype(r) => &r.ty,
        })
        .chain(reqs.iter().map(|req| &req.ty))
}

/// Direct use of `consts` will not register a dependency. You probably want
/// to use `Typing_env.consts` instead
pub fn consts(t: &T) -> Vec<(String, ClassConst<R>)> {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Consts, || {
        let TypingClassT(c, _) = t;
        (bindings(&c.consts).into_iter())
            .map(|(id, cc)| (id.to_string(), cc.clone()))
            .collect()
    })
}

pub fn typeconsts(t: &T) -> Vec<(String, TypeConst<R>)> {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Typeconsts, || {
        let TypingClassT(c, _) = t;
        (bindings(&c.type_consts).into_iter())
            .map(|(id, tc)| (id.to_string(), tc.clone()))
            .collect()
    })
}

pub fn props(t: &T) -> Vec<(String, ClassElt)> {
    let T(decl, t, ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Props, || {
        let TypingClassT(c, _) = t;
        (bindings(&c.props).into_iter())
            .map(|(id, elt)| {
                (
                    id.to_string(),
                    decl_class::lookup_property_type_lazy(ctx.as_deref(), c, id, elt),
                )
            })
            .collect()
    })
}

/// Not in the OCaml: the `ce_origin` of the property `id` of `props t`
/// (what `List.find (props t)` by name, then `ce_origin`, gives), without
/// building the class elements of all the properties.
pub fn prop_origin(t: &T, id: &str) -> Option<String> {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Props, || {
        let TypingClassT(c, _) = t;
        (c.props.get(&PropName(crate::ctx::symbol(id)))).map(|elt| elt.origin.as_str().to_string())
    })
}

pub fn sprops(t: &T) -> Vec<(String, ClassElt)> {
    let T(decl, t, ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::SProps, || {
        let TypingClassT(c, _) = t;
        (bindings(&c.static_props).into_iter())
            .map(|(id, elt)| {
                (
                    id.to_string(),
                    decl_class::lookup_static_property_type_lazy(ctx.as_deref(), c, id, elt),
                )
            })
            .collect()
    })
}

pub fn methods(t: &T) -> Vec<(String, ClassElt)> {
    let T(decl, t, ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Methods, || {
        let TypingClassT(c, _) = t;
        (bindings(&c.methods).into_iter())
            .map(|(id, elt)| {
                (
                    id.to_string(),
                    decl_class::lookup_method_type_lazy(ctx.as_deref(), c, id, elt),
                )
            })
            .collect()
    })
}

pub fn smethods(t: &T) -> Vec<(String, ClassElt)> {
    let T(decl, t, ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::SMethods, || {
        let TypingClassT(c, _) = t;
        (bindings(&c.static_methods).into_iter())
            .map(|(id, elt)| {
                (
                    id.to_string(),
                    decl_class::lookup_static_method_type_lazy(ctx.as_deref(), c, id, elt),
                )
            })
            .collect()
    })
}

pub fn overridden_method(
    t: &T,
    method_name: &str,
    is_static: bool,
    get_class: impl Fn(&Arc<Ctx>, &str) -> Option<T>,
) -> Option<ClassElt> {
    let T(decl, t, ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Overridden_method, || {
        let ctx = ctx.as_deref()?;
        let get_method = |ty: &Ty<R>| -> Option<ClassElt> {
            let (_, class_name, _) = decl_utils::unwrap_class_type(ty);
            let cls = get_class(ctx, class_name.id_ref().as_str())?;
            get_any_method(is_static, &cls, method_name)
        };
        let TypingClassT(cls, _members) = t;
        let shallow_class = decl_provider_internals::get_shallow_class(ctx, cls.name.as_str())?;
        decl_inherit::find_overridden_method(&shallow_class, get_method)
    })
}

fn get_static_member_from_req_constraints(
    t: &T,
    get_member: impl Fn(&T) -> Option<ClassElt>,
    get_class: impl Fn(&Arc<Ctx>, &str) -> Option<T>,
) -> Option<ClassElt> {
    let T(decl, _t, ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::All_ancestor_reqs, || {
        let ctx = ctx.as_deref()?;
        let req_constraints: Vec<Ty<R>> = (all_ancestor_req_constraints_requirements(t)
            .into_iter())
        .map(|cr| to_requirement(cr).ty)
        .collect();
        req_constraints
            .iter()
            .find_map(|req_ty| match req_ty.node_ref() {
                Ty_::Tapply(id_and_args) => {
                    let cn = id_and_args.0.id_ref().as_str();
                    let req_class = get_class(ctx, cn)?;
                    get_member(&req_class)
                }
                _ => None,
            })
    })
}

/// For a trait with `require class Foo` or `require this as Foo`, search `Foo`
/// for a static method. Returns the class element if found.
/// Intended for use in IDE and Glean after the innitial decl search failed.
pub fn get_smethod_from_req_constraints(
    cls: &T,
    method_name: &str,
    get_class: impl Fn(&Arc<Ctx>, &str) -> Option<T>,
) -> Option<ClassElt> {
    get_static_member_from_req_constraints(
        cls,
        |req_class| get_smethod(req_class, method_name),
        get_class,
    )
}

/// For a trait with `require class Foo` or `require this as Foo`, search `Foo`
/// for a static property. Returns the class element if found.
/// Intended for use in IDE and Glean after the innitial decl search failed.
pub fn get_sprop_from_req_constraints(
    cls: &T,
    prop_name: &str,
    get_class: impl Fn(&Arc<Ctx>, &str) -> Option<T>,
) -> Option<ClassElt> {
    get_static_member_from_req_constraints(
        cls,
        |req_class| get_sprop(req_class, prop_name),
        get_class,
    )
}

pub fn deferred_init_members(t: &T) -> im::OrdSet<String> {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Deferred_init_members, || {
        let TypingClassT(c, _) = t;
        (c.deferred_init_members.iter())
            .map(|x| x.as_str().to_string())
            .collect()
    })
}

pub fn valid_newable_class(cls: &T) -> bool {
    // `Ast_defs.is_c_class`
    if matches!(kind(cls), ClassishKind::Cclass(_)) {
        final_(cls) || !(construct(cls).1 == ConsistentKind::Inconsistent)
    }
    // There is currently a bug with interfaces that allows constructors to change
    // their signature, so they are not considered here. TODO: T41093452
    else {
        false
    }
}

#[cfg(test)]
mod tests {
    use oxidized::typechecker_options::TypecheckerOptions;
    use ty::decl::Typeconst;

    use super::*;
    use crate::decl_entry;
    use crate::decl_provider;
    use crate::decl_provider::testing::class;
    use crate::decl_provider::testing::ctx_of;

    const SRC: &str = r#"<?hh

interface I<Ti> {
  const type TI = int;
  public function iface(Ti $x): void;
}

abstract class A<Ta1, Ta2> implements I<Ta2> {
  const int CA = 1;
  abstract const type TAbs as arraykey;
  const type TConcrete = string;
  <<__Enforceable>>
  const type TEnf = int;
  public ?Ta1 $prop_a = null;
  protected static vec<Ta2> $sprop_a = vec[];
  private int $priv_a = 0;
  public function __construct(protected Ta1 $ctor_prop) {}
  public function test(Ta1 $x, Ta2 $y): void {}
  public function iface(Ta2 $x): void {}
  public static function smeth(Ta1 $x): Ta2 { throw new Exception(); }
  final protected function prot(): Ta2 { throw new Exception(); }
  public function generic<Tm>(Tm $x, Ta1 $y): Tm { return $x; }
  public function cast<Tb>(Ta1 $x): Tb { throw new Exception(); }
  abstract public function abs(): Ta1;
  private function priv(): void {}
}

class B<Tb> extends A<Tb, int> {
  const type TAbs = int;
  public function abs(): Tb { throw new Exception(); }
}

final class C extends B<string> {
  const string CC = 'c';
  public function own(): void {}
}

trait Tr {
  require extends B<int>;
  require implements I<int>;
  public function from_trait(): this { return $this; }
  public static int $tr_sprop = 0;
}

trait TrClass {
  require class C;
  public static function tr_static(): int { return 1; }
}

class D extends B<int> {
  use Tr;
}

enum E: int as arraykey {
  X = 1;
  Y = 2;
}

enum class EC: arraykey {
  int ONE = 1;
}

<<__ConsistentConstruct>>
class Consistent {
  public function __construct(int $x) {}
}

class ConsistentChild extends Consistent {}

class NoCtor {}

abstract class AbsCtor {
  abstract public function __construct();
}
"#;

    fn ctx() -> Arc<Ctx> {
        static CTX: LazyLock<Arc<Ctx>> =
            LazyLock::new(|| ctx_of(SRC, TypecheckerOptions::default()));
        Arc::clone(&CTX)
    }

    fn cls(name: &str) -> T {
        class(&ctx(), name)
    }

    /// The declared type of an element, as hackrs prints decl types.
    fn ty(ce: &ClassElt) -> String {
        (**ce.ce_type).to_string()
    }

    fn names<A>(l: Vec<(String, A)>) -> Vec<String> {
        l.into_iter().map(|(name, _)| name).collect()
    }

    /// The line, and the first and last columns, of a position.
    fn span(pos: &Pos) -> (usize, usize, usize) {
        pos.info_pos()
    }

    /// The elements can; a class (`T`) stays on the thread whose class
    /// cache it comes from (its handles are `Rc`s: see `TypingClassT`).
    #[test]
    fn elements_can_be_shared_between_threads() {
        fn assert_send_sync<A: Send + Sync>() {}
        assert_send_sync::<ClassElt>();
    }

    #[test]
    fn what_the_class_was_declared_as() {
        let (a, b, c, i) = (cls("\\A"), cls("\\B"), cls("\\C"), cls("\\I"));
        assert_eq!(name(&c), "\\C");
        assert_eq!(
            kind(&c),
            ClassishKind::Cclass(oxidized::ast_defs::Abstraction::Concrete)
        );
        assert_eq!(
            kind(&a),
            ClassishKind::Cclass(oxidized::ast_defs::Abstraction::Abstract)
        );
        assert_eq!(kind(&i), ClassishKind::Cinterface);
        assert_eq!(kind(&cls("\\Tr")), ClassishKind::Ctrait);
        assert_eq!(kind(&cls("\\E")), ClassishKind::Cenum);
        assert_eq!(
            (abstract_(&a), abstract_(&b), abstract_(&c), abstract_(&i)),
            (true, false, false, true)
        );
        assert_eq!((final_(&a), final_(&b), final_(&c)), (false, false, true));
        assert!(!has_const_attribute(&c) && !is_xhp(&c) && !internal(&c));
        assert_eq!(get_module(&c), None);
        assert_eq!(get_docs_url(&c), None);
        assert_eq!(sealed_whitelist(&c), None);
        assert!(decl_errors(&c).is_empty());
        assert!(!get_support_dynamic_type(&c));
        // `class C` is on line 33 of the file.
        assert_eq!(pos(&c).filename().path_str(), "test.php");
        assert_eq!(span(&pos(&c)), (33, 13, 13));
        let tparam_names = |t: &T| -> Vec<String> {
            (tparams(t).iter())
                .map(|tp| tp.name.id_ref().as_str().to_string())
                .collect()
        };
        assert_eq!(tparam_names(&a), vec!["Ta1", "Ta2"]);
        assert_eq!(tparam_names(&b), vec!["Tb"]);
        assert!(tparam_names(&c).is_empty());
    }

    #[test]
    fn ancestors_have_their_type_arguments() {
        let (a, b, c) = (cls("\\A"), cls("\\B"), cls("\\C"));
        let ancestor = |t: &T, name: &str| get_ancestor(t, name).map(|ty| ty.to_string());
        assert_eq!(ancestor(&c, "\\B").as_deref(), Some("B<string>"));
        assert_eq!(ancestor(&c, "\\A").as_deref(), Some("A<string, int>"));
        assert_eq!(ancestor(&c, "\\I").as_deref(), Some("I<int>"));
        assert_eq!(ancestor(&b, "\\A").as_deref(), Some("A<Tb, int>"));
        assert_eq!(ancestor(&b, "\\I").as_deref(), Some("I<int>"));
        assert_eq!(ancestor(&a, "\\I").as_deref(), Some("I<Ta2>"));
        assert_eq!(ancestor(&c, "\\C"), None);
        assert_eq!(ancestor(&c, "\\Nope"), None);
        assert!(has_ancestor(&c, "\\A") && has_ancestor(&c, "\\I"));
        assert!(!has_ancestor(&a, "\\B") && !has_ancestor(&c, "\\Nope"));
        // In the order of the names, as `S_map.bindings` gives them.
        let all: Vec<(String, String)> = (all_ancestors(&c).into_iter())
            .map(|(name, ty)| (name, ty.to_string()))
            .collect();
        assert_eq!(
            all,
            vec![
                ("\\A".to_string(), "A<string, int>".to_string()),
                ("\\B".to_string(), "B<string>".to_string()),
                ("\\I".to_string(), "I<int>".to_string()),
            ]
        );
        assert_eq!(all_ancestor_names(&c), vec!["\\A", "\\B", "\\I"]);
        assert_eq!(
            all_ancestor_names(&cls("\\D")),
            vec!["\\A", "\\B", "\\I", "\\Tr"]
        );
    }

    #[test]
    fn inherited_methods_have_the_types_of_the_inheriting_class() {
        let (a, b, c) = (cls("\\A"), cls("\\B"), cls("\\C"));
        let method = |t: &T, name: &str| {
            let ce = get_method(t, name).unwrap_or_else(|| panic!("no method {}", name));
            (ty(&ce), ce.ce_origin.clone())
        };
        let from_a = |ty: &str| (ty.to_string(), "\\A".to_string());
        assert_eq!(
            method(&a, "test"),
            from_a("(function(Ta1 $x, Ta2 $y): void)")
        );
        assert_eq!(
            method(&b, "test"),
            from_a("(function(Tb $x, int $y): void)")
        );
        assert_eq!(
            method(&c, "test"),
            from_a("(function(string $x, int $y): void)")
        );
        assert_eq!(method(&c, "iface"), from_a("(function(int $x): void)"));
        assert_eq!(method(&c, "prot"), from_a("(function(): int)"));
        // Overridden in B.
        assert_eq!(method(&a, "abs"), from_a("(function(): Ta1)"));
        assert_eq!(
            method(&c, "abs"),
            ("(function(): string)".to_string(), "\\B".to_string())
        );
        assert_eq!(
            method(&c, "own"),
            ("(function(): void)".to_string(), "\\C".to_string())
        );
        // Through a trait.
        assert_eq!(
            method(&cls("\\D"), "from_trait"),
            ("(function(): this)".to_string(), "\\Tr".to_string())
        );
        assert_eq!(
            method(&cls("\\D"), "test"),
            from_a("(function(int $x, int $y): void)")
        );

        assert!(has_method(&c, "test") && !has_method(&c, "smeth") && !has_method(&c, "nope"));
        assert!(get_method(&c, "nope").is_none() && get_method(&c, "smeth").is_none());

        let smeth = get_smethod(&c, "smeth").unwrap();
        assert_eq!(ty(&smeth), "(function(string $x): int)");
        assert_eq!(smeth.ce_origin, "\\A");
        assert_eq!(
            ty(&get_smethod(&b, "smeth").unwrap()),
            "(function(Tb $x): int)"
        );
        assert!(has_smethod(&c, "smeth") && !has_smethod(&c, "test"));
        assert!(get_smethod(&c, "test").is_none());

        assert_eq!(
            names(methods(&c)),
            vec!["abs", "cast", "generic", "iface", "own", "prot", "test"]
        );
        assert_eq!(names(smethods(&c)), vec!["smeth"]);
        let all: Vec<String> = methods(&c).iter().map(|(_, ce)| ty(ce)).collect();
        assert_eq!(all[6], "(function(string $x, int $y): void)");
    }

    #[test]
    fn type_parameters_of_methods() {
        let (a, b, c) = (cls("\\A"), cls("\\B"), cls("\\C"));
        let method = |t: &T, name: &str| ty(&get_method(t, name).unwrap());
        // A method's own type parameter is not substituted.
        assert_eq!(method(&a, "generic"), "(function<Tm>(Tm $x, Ta1 $y): Tm)");
        assert_eq!(
            method(&c, "generic"),
            "(function<Tm>(Tm $x, string $y): Tm)"
        );
        // `A::cast<Tb>(Ta1): Tb` in `B<Tb> extends A<Tb, int>`: the method's
        // `Tb` is renamed away from the `Tb` that `Ta1` becomes.
        assert_eq!(method(&a, "cast"), "(function<Tb>(Ta1 $x): Tb)");
        assert_eq!(method(&b, "cast"), "(function<Tb#0>(Tb $x): Tb#0)");
        assert_eq!(method(&c, "cast"), "(function<Tb#0>(string $x): Tb#0)");
    }

    #[test]
    fn visibility_origin_and_flags_of_elements() {
        let (a, c) = (cls("\\A"), cls("\\C"));
        let test = get_method(&c, "test").unwrap();
        assert_eq!(test.ce_visibility, CeVisibility::Vpublic);
        assert_eq!(test.ce_origin, "\\A");
        assert_eq!(test.ce_deprecated, None);
        assert_eq!(test.ce_flags, ClassEltFlags::empty());
        // The position of the element is where it was declared: line 18 of
        // the file, in `A`.
        assert_eq!(span(&test.ce_pos), (18, 19, 22));

        let prot = get_method(&c, "prot").unwrap();
        assert_eq!(
            prot.ce_visibility,
            CeVisibility::Vprotected("\\A".to_string())
        );
        assert!(prot.ce_flags.contains(ClassEltFlags::FINAL));

        // Private members are not inherited.
        let private = CeVisibility::Vprivate("\\A".to_string());
        assert_eq!(get_method(&a, "priv").unwrap().ce_visibility, private);
        assert!(get_method(&c, "priv").is_none() && !has_method(&c, "priv"));
        assert_eq!(get_prop(&a, "priv_a").unwrap().ce_visibility, private);
        assert!(get_prop(&c, "priv_a").is_none() && !has_prop(&c, "priv_a"));

        assert!(
            get_method(&a, "abs")
                .unwrap()
                .ce_flags
                .contains(ClassEltFlags::ABSTRACT)
        );
        assert!(
            !get_method(&c, "abs")
                .unwrap()
                .ce_flags
                .contains(ClassEltFlags::ABSTRACT)
        );
    }

    #[test]
    fn properties() {
        let (a, b, c) = (cls("\\A"), cls("\\B"), cls("\\C"));
        let prop = |t: &T, name: &str| ty(&get_prop(t, name).unwrap());
        assert_eq!(prop(&a, "prop_a"), "?Ta1");
        assert_eq!(prop(&b, "prop_a"), "?Tb");
        assert_eq!(prop(&c, "prop_a"), "?string");
        // Declared by the constructor of A.
        let ctor_prop = get_prop(&c, "ctor_prop").unwrap();
        assert_eq!(ty(&ctor_prop), "string");
        assert_eq!(ctor_prop.ce_origin, "\\A");
        assert_eq!(
            ctor_prop.ce_visibility,
            CeVisibility::Vprotected("\\A".to_string())
        );
        assert_eq!(names(props(&c)), vec!["ctor_prop", "prop_a"]);
        assert_eq!(names(props(&a)), vec!["ctor_prop", "priv_a", "prop_a"]);
        assert!(has_prop(&c, "prop_a") && !has_prop(&c, "$sprop_a") && !has_prop(&c, "nope"));

        // Static properties are named with their `$`.
        let sprop = get_sprop(&c, "$sprop_a").unwrap();
        assert_eq!(ty(&sprop), "HH\\vec<int>");
        assert_eq!(sprop.ce_origin, "\\A");
        assert_eq!(ty(&get_sprop(&a, "$sprop_a").unwrap()), "HH\\vec<Ta2>");
        assert!(get_sprop(&c, "sprop_a").is_none() && get_sprop(&c, "prop_a").is_none());
        assert!(has_sprop(&c, "$sprop_a") && !has_sprop(&c, "prop_a"));
        assert_eq!(names(sprops(&c)), vec!["$sprop_a"]);
        assert_eq!(names(sprops(&cls("\\D"))), vec!["$sprop_a", "$tr_sprop"]);
        assert!(deferred_init_members(&c).is_empty());
    }

    #[test]
    fn constructors() {
        let ctor = |name: &str| {
            let (ce, consistent) = construct(&cls(name));
            (ce.map(|ce| (ty(&ce), ce.ce_origin.clone())), consistent)
        };
        let from_a = |ty: &str| Some((ty.to_string(), "\\A".to_string()));
        assert_eq!(
            ctor("\\A"),
            (
                from_a("(function(Ta1 $ctor_prop): void)"),
                ConsistentKind::Inconsistent
            )
        );
        assert_eq!(
            ctor("\\B"),
            (
                from_a("(function(Tb $ctor_prop): void)"),
                ConsistentKind::Inconsistent
            )
        );
        assert_eq!(
            ctor("\\C"),
            (
                from_a("(function(string $ctor_prop): void)"),
                ConsistentKind::FinalClass
            )
        );
        let consistent = Some((
            "(function(int $x): void)".to_string(),
            "\\Consistent".to_string(),
        ));
        assert_eq!(
            ctor("\\Consistent"),
            (consistent.clone(), ConsistentKind::ConsistentConstruct)
        );
        assert_eq!(
            ctor("\\ConsistentChild"),
            (consistent, ConsistentKind::ConsistentConstruct)
        );
        assert_eq!(ctor("\\NoCtor"), (None, ConsistentKind::Inconsistent));
        assert_eq!(ctor("\\I"), (None, ConsistentKind::Inconsistent));

        // A class needs to be initialised when it has a constructor that is
        // not abstract.
        assert!(need_init(&cls("\\A")) && need_init(&cls("\\C")));
        assert!(need_init(&cls("\\ConsistentChild")));
        assert!(!need_init(&cls("\\NoCtor")) && !need_init(&cls("\\AbsCtor")));
        assert!(construct(&cls("\\AbsCtor")).0.is_some());

        // `new static()` is fine in a final class and in one whose
        // constructor is consistent.
        assert!(valid_newable_class(&cls("\\C")));
        assert!(valid_newable_class(&cls("\\Consistent")));
        assert!(valid_newable_class(&cls("\\ConsistentChild")));
        assert!(!valid_newable_class(&cls("\\B")) && !valid_newable_class(&cls("\\NoCtor")));
        assert!(!valid_newable_class(&cls("\\I")) && !valid_newable_class(&cls("\\Tr")));

        let c = cls("\\C");
        let any =
            |is_static: bool, name: &str| get_any_method(is_static, &c, name).map(|ce| ty(&ce));
        assert_eq!(
            any(false, "__construct").as_deref(),
            Some("(function(string $ctor_prop): void)")
        );
        assert_eq!(
            any(true, "__construct").as_deref(),
            Some("(function(string $ctor_prop): void)")
        );
        assert_eq!(
            any(true, "smeth").as_deref(),
            Some("(function(string $x): int)")
        );
        assert_eq!(any(false, "smeth"), None);
        assert_eq!(any(false, "own").as_deref(), Some("(function(): void)"));
        assert_eq!(any(true, "own"), None);
        // The constructor is not a method.
        assert!(get_method(&c, "__construct").is_none());
    }

    #[test]
    fn constants() {
        let (a, c) = (cls("\\A"), cls("\\C"));
        let cc = get_const(&c, "CC").unwrap();
        assert_eq!(cc.ty.to_string(), "string");
        assert_eq!(cc.origin.as_str(), "\\C");
        assert_eq!(cc.kind, ty::decl::ClassConstKind::CCConcrete);
        let ca = get_const(&c, "CA").unwrap();
        assert_eq!(ca.ty.to_string(), "int");
        assert_eq!(ca.origin.as_str(), "\\A");
        assert!(get_const(&a, "CC").is_none() && get_const(&c, "Nope").is_none());
        assert!(has_const(&c, "CA") && has_const(&c, "CC"));
        assert!(!has_const(&a, "CC") && !has_const(&c, "Nope"));
        // Every class has a constant `class`, and one for each type constant.
        assert_eq!(
            names(consts(&c)),
            vec!["CA", "CC", "TAbs", "TConcrete", "TEnf", "TI", "class"]
        );
        assert_eq!(
            get_const(&a, "TAbs").unwrap().kind,
            ty::decl::ClassConstKind::CCAbstract(false)
        );
        assert_eq!(
            get_const(&c, "TAbs").unwrap().kind,
            ty::decl::ClassConstKind::CCConcrete
        );
        assert_eq!(get_const(&c, "class").unwrap().origin.as_str(), "\\C");
    }

    #[test]
    fn type_constants() {
        let (a, c) = (cls("\\A"), cls("\\C"));
        match get_typeconst(&a, "TAbs").unwrap().kind {
            Typeconst::TCAbstract(atc) => {
                assert_eq!(atc.as_constraint.unwrap().to_string(), "arraykey");
                assert!(atc.super_constraint.is_none() && atc.default.is_none());
            }
            Typeconst::TCConcrete(_) => panic!(),
        }
        // Made concrete by B.
        let tabs = get_typeconst(&c, "TAbs").unwrap();
        assert_eq!(tabs.origin.as_str(), "\\B");
        match tabs.kind {
            Typeconst::TCConcrete(tc) => assert_eq!(tc.ty.to_string(), "int"),
            Typeconst::TCAbstract(_) => panic!(),
        }
        // From the interface.
        let ti = get_typeconst(&c, "TI").unwrap();
        assert_eq!(ti.origin.as_str(), "\\I");
        assert_eq!(ti.name.id_ref().as_str(), "TI");
        assert!(get_typeconst(&c, "CA").is_none() && get_typeconst(&c, "Nope").is_none());
        assert!(has_typeconst(&c, "TConcrete") && !has_typeconst(&c, "CA"));
        assert_eq!(
            names(typeconsts(&c)),
            vec!["TAbs", "TConcrete", "TEnf", "TI"]
        );

        assert_eq!(
            get_typeconst_enforceability(&c, "TAbs"),
            Some((Pos::NONE, false))
        );
        assert_eq!(get_typeconst_enforceability(&c, "Nope"), None);
        // The position is that of the attribute, on line 12 of the file.
        let (pos, enforceable) = get_typeconst_enforceability(&c, "TEnf").unwrap();
        assert!(enforceable);
        assert_eq!(span(&pos).0, 12);
    }

    #[test]
    fn enums() {
        let e = cls("\\E");
        let enum_type_ = enum_type(&e).unwrap();
        assert_eq!(enum_type_.base.to_string(), "int");
        assert_eq!(
            enum_type_.constraint.as_ref().unwrap().to_string(),
            "arraykey"
        );
        assert!(enum_type_.includes.is_empty());
        assert_eq!(
            get_ancestor(&e, "\\HH\\BuiltinEnum").unwrap().to_string(),
            "HH\\BuiltinEnum<E>"
        );
        // The constants of an enum have the type of the enum.
        assert_eq!(get_const(&e, "X").unwrap().ty.to_string(), "E");
        assert_eq!(names(consts(&e)), vec!["X", "Y", "class"]);
        // Its methods are those of `BuiltinEnum<E>`.
        let get_values = get_smethod(&e, "getValues").unwrap();
        assert_eq!(ty(&get_values), "(function(): HH\\dict<string, E>)");
        assert_eq!(get_values.ce_origin, "\\HH\\BuiltinEnum");

        let ec = cls("\\EC");
        assert_eq!(
            kind(&ec),
            ClassishKind::CenumClass(oxidized::ast_defs::Abstraction::Concrete)
        );
        let enum_type_ = enum_type(&ec).unwrap();
        assert_eq!(enum_type_.base.to_string(), "arraykey");
        assert!(enum_type_.constraint.is_none());
        assert_eq!(
            get_const(&ec, "ONE").unwrap().ty.to_string(),
            "HH\\MemberOf<EC, int>"
        );
        assert_eq!(
            get_ancestor(&ec, "\\HH\\BuiltinEnumClass")
                .unwrap()
                .to_string(),
            "HH\\BuiltinEnumClass<HH\\MemberOf<EC, arraykey>>"
        );

        assert!(enum_type(&cls("\\C")).is_none());

        // What `Decl_enum` makes of them.
        let enum_kind = |t: &T, is_enum_class: bool| {
            let name = pos::Positioned::new(BPos::none(), TypeName::new(name(t)));
            crate::decl_enum::enum_kind(
                &name,
                is_enum_class,
                false,
                enum_type(t).as_ref(),
                None,
                |ancestor| get_ancestor(t, ancestor),
            )
        };
        let kind_e = enum_kind(&e, false).unwrap();
        assert_eq!(kind_e.base.to_string(), "int");
        assert_eq!(kind_e.type_.to_string(), "E");
        assert_eq!(kind_e.constraint_.unwrap().to_string(), "arraykey");
        assert!(kind_e.interface.is_none());
        let kind_ec = enum_kind(&ec, true).unwrap();
        assert_eq!(kind_ec.base.to_string(), "HH\\MemberOf<EC, arraykey>");
        assert_eq!(kind_ec.type_.to_string(), "EC");
        assert_eq!(kind_ec.interface.unwrap().to_string(), "arraykey");
        assert!(enum_kind(&cls("\\C"), false).is_none());
    }

    #[test]
    fn requirements() {
        let tr = cls("\\Tr");
        let reqs: Vec<String> = (all_ancestor_reqs(&tr).iter())
            .map(|req| req.ty.to_string())
            .collect();
        assert_eq!(reqs, vec!["B<int>", "I<int>"]);
        assert!(requires_ancestor(&tr, "\\B") && requires_ancestor(&tr, "\\I"));
        assert!(!requires_ancestor(&tr, "\\C"));
        // `require extends B<int>` also requires what B extends.
        assert_eq!(all_ancestor_req_names(&tr), vec!["\\A", "\\B", "\\I"]);
        assert!(all_ancestor_req_constraints_requirements(&tr).is_empty());
        let upper_bounds: Vec<String> = (upper_bounds_on_this(&tr).iter())
            .map(|ty| ty.to_string())
            .collect();
        assert_eq!(upper_bounds, vec!["B<int>", "I<int>"]);
        // The members of the required class are members of the trait.
        assert_eq!(
            ty(&get_method(&tr, "test").unwrap()),
            "(function(int $x, int $y): void)"
        );
        assert!(
            get_method(&tr, "test")
                .unwrap()
                .ce_flags
                .contains(ClassEltFlags::SYNTHESIZED)
        );

        let tr_class = cls("\\TrClass");
        assert!(all_ancestor_reqs(&tr_class).is_empty());
        assert!(all_ancestor_req_names(&tr_class).is_empty());
        let req_classes: Vec<String> = (all_ancestor_req_class_requirements(&tr_class).iter())
            .map(|req| req.ty.to_string())
            .collect();
        assert_eq!(req_classes, vec!["C"]);
        assert!(all_ancestor_req_this_as_requirements(&tr_class).is_empty());
        let upper_bounds: Vec<String> = (upper_bounds_on_this(&tr_class).iter())
            .map(|ty| ty.to_string())
            .collect();
        assert_eq!(upper_bounds, vec!["C"]);

        // `require class C` does not make the members of C members of the
        // trait: they are looked for in C.
        assert!(get_smethod(&tr_class, "smeth").is_none());
        let get_class = |ctx: &Arc<Ctx>, name: &str| {
            decl_entry::to_option(decl_provider::get_class(None, ctx, name))
        };
        let smeth = get_smethod_from_req_constraints(&tr_class, "smeth", get_class).unwrap();
        assert_eq!(ty(&smeth), "(function(string $x): int)");
        assert!(get_smethod_from_req_constraints(&tr_class, "nope", get_class).is_none());
        let sprop = get_sprop_from_req_constraints(&tr_class, "$sprop_a", get_class).unwrap();
        assert_eq!(ty(&sprop), "HH\\vec<int>");
        assert!(get_sprop_from_req_constraints(&tr, "$sprop_a", get_class).is_none());
    }

    #[test]
    fn elements_are_looked_up_once_for_a_class() {
        let c = cls("\\C");
        let test1 = get_method(&c, "test").unwrap();
        let test2 = get_method(&c, "test").unwrap();
        // The same lazy type.
        assert!(Arc::ptr_eq(&test1.ce_type, &test2.ce_type));
        assert!(Arc::ptr_eq(&test1.ce_pos, &test2.ce_pos));
        let (ctor1, _) = construct(&c);
        let (ctor2, _) = construct(&c);
        assert!(Arc::ptr_eq(
            &ctor1.unwrap().ce_type,
            &ctor2.unwrap().ce_type
        ));
        // And for the class as it is fetched again.
        let test3 = get_method(&cls("\\C"), "test").unwrap();
        assert!(Arc::ptr_eq(&test1.ce_type, &test3.ce_type));
        // `methods` looks every element up again.
        let (_, test4) = methods(&c).pop().unwrap();
        assert!(!Arc::ptr_eq(&test1.ce_type, &test4.ce_type));
        assert_eq!(ty(&test1), ty(&test4));
    }

    #[test]
    fn the_type_of_an_element_is_only_looked_up_when_asked_for() {
        // Without a context there is nowhere to look the type up, which is
        // only found out when the type is asked for.
        let T(_, class_t, _) = cls("\\C");
        let class_t = typing_class_types::make_class_t(Arc::clone(&class_t.0));
        let c = T(None, make(class_t), None);
        let test = get_method(&c, "test").unwrap();
        assert_eq!(test.ce_origin, "\\A");
        assert_eq!(test.ce_visibility, CeVisibility::Vpublic);
        let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| ty(&test)));
        let message = *panic.unwrap_err().downcast::<String>().unwrap();
        assert_eq!(
            message,
            "Decl_class.Decl_heap_elems_bug(\"could not find \\\\A::test (inherited by \\\\C) (no lazy member lookup performed)\")"
        );
        let (ctor, consistent) = construct(&c);
        assert_eq!(consistent, ConsistentKind::FinalClass);
        let ctor = ctor.unwrap();
        let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| ty(&ctor)));
        assert!(panic.is_err());
    }

    #[test]
    fn instantiate_ce() {
        use ty::reason::Reason;
        let b = cls("\\B");
        let test = get_method(&b, "test").unwrap();
        let float = Ty::prim(R::none(), ty::decl::Prim::Tfloat);
        let subst = crate::decl_instantiate::make_subst(&tparams(&b), &[float]);
        let instantiated = crate::decl_instantiate::instantiate_ce(&subst, &test);
        assert_eq!(ty(&instantiated), "(function(float $x, int $y): void)");
        assert_eq!(ty(&test), "(function(Tb $x, int $y): void)");
        assert!(Arc::ptr_eq(&instantiated.ce_pos, &test.ce_pos));
        assert_eq!(instantiated.ce_origin, "\\A");
    }

    #[test]
    fn member_types_are_pessimised_with_everything_sdt() {
        let src = r#"<?hh
class P<Tc> {
  public int $enforced = 0;
  public function two<T>(T $x, Tc $y): int { return 1; }
  public static function stwo<T>(T $x, int $y): void {}
}

class P2 extends P<float> {}

<<__NoAutoDynamic>>
class Q<Tc> {
  public function two<T>(T $x, Tc $y): int { return 1; }
}
"#;
        let mut tco = TypecheckerOptions::default();
        tco.po.everything_sdt = true;
        let ctx = ctx_of(src, tco);
        // The type parameters of a method are made to support dynamic
        // (`Decl_enforceability.Pessimize`), before the substitution.
        let p2 = class(&ctx, "\\P2");
        assert_eq!(
            ty(&get_method(&p2, "two").unwrap()),
            "(function<T as HH\\supportdyn<mixed>>(T $x, float $y): int)"
        );
        assert_eq!(
            ty(&get_smethod(&p2, "stwo").unwrap()),
            "(function<T as HH\\supportdyn<mixed>>(T $x, int $y): void)"
        );
        // An enforced type is left alone.
        assert_eq!(ty(&get_prop(&p2, "enforced").unwrap()), "int");
        assert!(get_support_dynamic_type(&p2));
        // Not in a class that opts out.
        let q = class(&ctx, "\\Q");
        assert_eq!(
            ty(&get_method(&q, "two").unwrap()),
            "(function<T>(T $x, Tc $y): int)"
        );
        assert!(!get_support_dynamic_type(&q));

        // Without the option nothing is.
        let ctx = ctx_of(src, TypecheckerOptions::default());
        let p2 = class(&ctx, "\\P2");
        assert_eq!(
            ty(&get_method(&p2, "two").unwrap()),
            "(function<T>(T $x, float $y): int)"
        );
    }
}
