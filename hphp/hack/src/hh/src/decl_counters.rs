// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `decl/decl_counters.ml`: the telemetry of decl accesses.
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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DeclKind {
    Class,
    Fun,
    GConst,
    Typedef,
    ModuleDecl,
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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SubdeclKind<'a> {
    // Shallow
    Abstract,
    Final,
    Const,
    Kind,
    IsXhp,
    Name,
    Module,
    Internal,
    TestsBypassVisibility,
    AllowUncheckedEnumValues,
    IsModuleLevelTrait,
    Pos,
    Tparams,
    EnumType,
    XhpEnumValues,
    XhpMarkedEmpty,
    SealedWhitelist,
    DocsUrl,
    DeclErrors,
    SupportDynamicType,
    // Lazy
    Construct,
    NeedInit,
    GetAncestor(&'a str),
    HasAncestor(&'a str),
    RequiresAncestor(&'a str),
    Extends(&'a str),
    IsDisposable,
    GetConst(&'a str),
    HasConst(&'a str),
    GetTypeconst(&'a str),
    HasTypeconst(&'a str),
    GetTypeconstEnforceability(&'a str),
    GetProp(&'a str),
    HasProp(&'a str),
    GetSprop(&'a str),
    HasSprop(&'a str),
    GetMethod(&'a str),
    HasMethod(&'a str),
    GetSmethod(&'a str),
    HasSmethod(&'a str),
    // Eager
    MembersFullyKnown,
    AllAncestorReqNames,
    AllExtendsAncestors,
    AllAncestors,
    AllAncestorNames,
    AllAncestorReqs,
    Consts,
    Typeconsts,
    Props,
    SProps,
    Methods,
    SMethods,
    OverriddenMethod,
    // Misc
    DeferredInitMembers,
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
