// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `diagnostics.ml`, the OCaml module `Diagnostics` (`crate::diagnostics`
//! was already taken by the formatting helpers). See `hh/PORTING.md`.
//!
//! The types are the ones of `oxidized::diagnostics`, re-exported; [`T`] is
//! `Diagnostics.t`.
//!
//! # State
//!
//! OCaml keeps the error accumulator in global refs. Here:
//!
//! - The accumulator (`error_map`, `accumulate_errors`, `current_file`,
//!   `current_span`, `in_lazy_decl`, ...) and the three fixme hooks are
//!   **thread local**: one file is checked on one thread. A new thread starts
//!   in the state an OCaml process starts in.
//! - `allowed_fixme_codes_strict` and `code_agnostic_fixme` are configuration
//!   that OCaml sets once from the options before any worker is forked. They
//!   are **process wide** here, so that setting them at startup reaches every
//!   thread.
//! - The fixmes of each file (`Fixme_provider`, in shared memory in OCaml) are
//!   in [`fixme_provider`], thread local as well: a file's comments are
//!   installed by the thread that parses and checks it
//!   ([`fixme_provider::provide_scoured_comments`]).
//!
//! As in OCaml, nothing accumulates until a `do_`/`try_` is running: adding an
//! error outside of one is a bug and panics (`add_error_impl`).
//!
//! The lists of the accumulator are cons lists in OCaml, most recent error
//! first. Here they are `Vec`s with the most recent error **last** (so that
//! adding is a push); the places where the order matters say so. The lists of
//! a [`T`] that a function returns or takes are in the OCaml order, element 0
//! being the head.
//!
//! # `try_` and the borrow checker
//!
//! `try_ f1 f2` takes two closures that usually both need the environment.
//! When they cannot both borrow it, return the error from the handler and act
//! on it afterwards:
//!
//! ```ignore
//! match try_with_result(|| Ok(f1(env)), |_, err| Err(err)) {
//!     Ok(x) => x,
//!     Err(err) => f2(env, err),
//! }
//! ```
//!
//! # Not ported
//!
//! What only the server, the client or the IDE use: `finalized_diagnostic`
//! and what is defined on it (`sort_and_finalize`, `to_string`,
//! `FinalizedErrorSet`), `ErrorSet`, `convert_errors_to_string`,
//! `as_telemetry`, `as_telemetry_summary`, the derived `hash_diagnostic`,
//! `show`/`pp`, and of `Fixme_provider`: `UnusedFixmes`.

#![allow(non_upper_case_globals)]

use std::backtrace::Backtrace;
use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::rc::Rc;
use std::sync::LazyLock;
use std::sync::RwLock;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering as AtomicOrdering;

use bstr::BString;
pub use oxidized::diagnostics::*;
use oxidized::error_codes;
use oxidized::explanation::Explanation;
use oxidized::i_map::IMap;
use oxidized::i_set::ISet;
use oxidized::message::Message;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use oxidized::pos_span_raw::PosSpanRaw;
use oxidized::quickfix::Quickfix;
use oxidized::user_diagnostic::UserDiagnostic;
use oxidized::warnings_saved_state::ErrorHash;
use oxidized::warnings_saved_state_impl::WarningsSavedState;
use relative_path::RelativePath;

/// `Diagnostics.t`: the errors of each file.
///
/// The lists are OCaml lists, element 0 being the head.
pub type T = Diagnostics;

/// The type of the three hooks `get_hh_fixme_pos`, `get_disallowed_fixme_pos`
/// and `get_ignore_pos`: the position of the comment that suppresses the code
/// at that position, if there is one.
pub type FixmePosFn = Rc<dyn Fn(&Pos, ErrorCode) -> Option<Pos>>;

// ~~ what the port needs from modules that are not ported ~~~~~~~~~~~~~~~~~~~

/// `Error_message_sentinel.please_file_a_bug_message`
/// (`error_message_sentinel.stubs.ml`).
const ERROR_MESSAGE_SENTINEL_PLEASE_FILE_A_BUG_MESSAGE: &str =
    "If remediation attempts don't work, please file a bug report.";

/// `Pos.contains`
fn pos_contains(pos_container: &Pos, pos: &Pos) -> bool {
    let (cstart, cend) = pos_container.info_raw();
    let (pstart, pend) = pos.info_raw();
    pos_container.filename() == pos.filename() && pstart >= cstart && pend <= cend
}

/// `Pos.make_from`
fn pos_make_from(file: RelativePath) -> Pos {
    Pos::from_raw_span(std::sync::Arc::new(file), PosSpanRaw::make_dummy())
}

/// `Error_codes.Warning.of_enum`
fn warning_of_enum(code: ErrorCode) -> Option<error_codes::Warning> {
    use error_codes::Warning::*;
    Some(match code {
        12001 => SketchyEquality,
        12004 => NonDisjointCheck,
        12005 => CastNonPrimitive,
        12006 => TruthinessTest,
        12007 => EqualityCheck,
        12008 => DuplicateProperties,
        12009 => IsIsAlwaysTrue,
        12010 => IsIsAlwaysFalse,
        12011 => AsAlwaysSucceeds,
        12012 => AsAlwaysFails,
        12013 => ClassPointerToString,
        12017 => NoDisjointUnion,
        12018 => SafeAbstractConstAccess,
        12019 => SwitchRedundancy,
        12020 => StaticCallOnTrait,
        12021 => StaticPropertyOverride,
        12022 => StringToClassPointer,
        12023 => NullCoalesceAlways,
        12024 => CallNeedsConcrete,
        12028 => ExpectBoolForCondition,
        12029 => RedundantNullsafeMemberSelect,
        12030 => NullsafeMemberSelectOnNull,
        12031 => RedundantNullsafePipe,
        12032 => NullsafePipeOnNull,
        12033 => UnboundNameWarning,
        12034 => SetOrKeysetArrayGet,
        12035 => SealedNotSubtype,
        12036 => TanyFound,
        12037 => ConsistentConstructAbstractFinal,
        12038 => DynamicMethodCall,
        12039 => DynamicFunctionCall,
        12040 => DynamicArrayAccess,
        12041 => SealedNotOverride,
        12042 => DynamicPropertyAccess,
        12043 => RedundantRequireThisAs,
        12044 => DynamicReturn,
        12045 => ReadonlyPropertyOverride,
        12048 => RedundantConcurrent,
        _ => return None,
    })
}

/// `User_diagnostic.make` (`is_fixmed` is always left to its default).
#[allow(clippy::too_many_arguments)]
fn make<PP, P>(
    severity: Severity,
    code: ErrorCode,
    quickfixes: Vec<Quickfix<PP>>,
    custom_msgs: Vec<String>,
    function_pos: Option<PP>,
    claim: Message<PP>,
    reasons: Vec<Message<P>>,
    explanation: Explanation<P>,
) -> UserDiagnostic<PP, P> {
    UserDiagnostic {
        severity,
        code,
        claim,
        reasons,
        explanation,
        quickfixes,
        custom_msgs,
        is_fixmed: false,
        function_pos,
    }
}

/// `User_diagnostic.make_err` without optional arguments.
fn make_err(
    code: ErrorCode,
    claim: Message<Pos>,
    reasons: Vec<Message<PosOrDecl>>,
    explanation: Explanation<PosOrDecl>,
) -> Diagnostic {
    make(
        Severity::Err,
        code,
        vec![],
        vec![],
        None,
        claim,
        reasons,
        explanation,
    )
}

/// `User_diagnostic.to_list_`
fn to_list_(error: &Diagnostic) -> Vec<Message<PosOrDecl>> {
    let mut list = Vec::with_capacity(error.reasons.len() + 1);
    list.push(claim_as_reason(error.claim.clone()));
    list.extend(error.reasons.iter().cloned());
    list
}

/// `User_diagnostic.equal_severity`: `is_trusted` is not compared.
fn equal_severity(x: &Severity, y: &Severity) -> bool {
    matches!(
        (x, y),
        (Severity::Warning { .. }, Severity::Warning { .. }) | (Severity::Err, Severity::Err)
    )
}

/// `User_diagnostic.compare_severity`: `is_trusted` is not compared.
fn compare_severity(x: &Severity, y: &Severity) -> Ordering {
    match (x, y) {
        (Severity::Warning { .. }, Severity::Warning { .. }) => Ordering::Equal,
        (Severity::Warning { .. }, Severity::Err) => Ordering::Less,
        (Severity::Err, Severity::Warning { .. }) => Ordering::Greater,
        (Severity::Err, Severity::Err) => Ordering::Equal,
    }
}

/// `equal_diagnostic`, as derived in OCaml: the explanation and the
/// `is_trusted` of a warning are not compared.
pub fn equal_diagnostic(x: &Diagnostic, y: &Diagnostic) -> bool {
    equal_severity(&x.severity, &y.severity)
        && x.code == y.code
        && x.claim == y.claim
        && x.reasons == y.reasons
        && x.quickfixes == y.quickfixes
        && x.custom_msgs == y.custom_msgs
        && x.is_fixmed == y.is_fixmed
        && x.function_pos == y.function_pos
}

/// `Utils.try_finally`: runs `finally` when dropped, whether the scope is left
/// normally or by a panic.
struct Finally<F: FnOnce()>(Option<F>);

impl<F: FnOnce()> Drop for Finally<F> {
    fn drop(&mut self) {
        if let Some(finally) = self.0.take() {
            finally()
        }
    }
}

fn finally<F: FnOnce()>(f: F) -> Finally<F> {
    Finally(Some(f))
}

/// `Utils.assert_false_log_backtrace`
fn assert_false_log_backtrace(msg: Option<&str>) -> ! {
    eprintln!("assert false with backtrace:");
    if let Some(msg) = msg {
        eprintln!("{}", msg);
    }
    eprint!("{}", Backtrace::force_capture());
    panic!("assert false")
}

/// `Exit_status.exit_code Exit_status.Lazy_decl_bug`
const EXIT_STATUS_LAZY_DECL_BUG: i32 = 208;

// ~~ the state ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

struct State {
    /// The file of analysis being currently performed
    current_file: RelativePath,
    current_span: Pos,
    ignore_pos_outside_current_span: bool,
    allow_errors_in_default_path: bool,
    get_hh_fixme_pos: FixmePosFn,
    get_disallowed_fixme_pos: FixmePosFn,
    get_ignore_pos: FixmePosFn,
    /// The lists are in the order the errors were added in: the reverse of
    /// the OCaml lists.
    error_map: BTreeMap<RelativePath, Vec<Diagnostic>>,
    accumulate_errors: bool,
    /// Are we in the middle of folding a decl? ("lazy" means it happens
    /// on-demand during the course of the typecheck, rather than all
    /// upfront).
    in_lazy_decl: bool,
    /// How many of [`do_`] and [`try_with_result`] (which give `f` an
    /// accumulator of its own) are running (no OCaml counterpart).
    depth: u32,
    /// See [`start_recording_warning_keys`] (no OCaml counterpart): the
    /// depth of the accumulator whose warnings are recorded, and their keys.
    warning_keys: Option<(u32, Vec<(isize, Pos)>)>,
}

impl State {
    fn new() -> Self {
        State {
            current_file: RelativePath::EMPTY,
            current_span: Pos::NONE,
            ignore_pos_outside_current_span: false,
            allow_errors_in_default_path: true,
            // The refs start as `fun _ _ -> None` in OCaml and the
            // initialiser of `Fixme_provider` sets them to these.
            get_hh_fixme_pos: Rc::new(fixme_provider::get_hh_fixme_pos),
            get_disallowed_fixme_pos: Rc::new(fixme_provider::get_disallowed_fixme_pos),
            get_ignore_pos: Rc::new(fixme_provider::get_ignore_pos),
            error_map: BTreeMap::new(),
            accumulate_errors: false,
            in_lazy_decl: false,
            depth: 0,
            warning_keys: None,
        }
    }
}

thread_local! {
    static STATE: RefCell<State> = RefCell::new(State::new());
}

/// Not in the OCaml (whose worker process fails, and is started afresh):
/// after a panic was caught in the check of a file, the state of this thread
/// starts again as at the start of the thread (see
/// `crate::rt::decl_epoch::after_panic`); so does the flag of the warning
/// checks.
pub fn reset_thread_after_panic() {
    STATE.with(|state| *state.borrow_mut() = State::new());
    RECORDING_WARNING_CHECK.set(false);
}

/// Read or change the state. `f` must not call back into this module: no
/// borrow is ever held while a caller's closure runs.
fn with<R>(f: impl FnOnce(&mut State) -> R) -> R {
    STATE.with(|state| f(&mut state.borrow_mut()))
}

/// `with` for the `finally` of a scope, which may run while unwinding.
fn restore(f: impl FnOnce(&mut State)) {
    let _ = STATE.try_with(|state| {
        if let Ok(mut state) = state.try_borrow_mut() {
            f(&mut state)
        }
    });
}

/// Error codes that can be suppressed in strict mode with a FIXME based on
/// configuration. Process wide.
static ALLOWED_FIXME_CODES_STRICT: RwLock<ISet> = RwLock::new(ISet::new());

/// Process wide.
static CODE_AGNOSTIC_FIXME: AtomicBool = AtomicBool::new(false);

/// `!allowed_fixme_codes_strict`
pub fn allowed_fixme_codes_strict() -> ISet {
    ALLOWED_FIXME_CODES_STRICT
        .read()
        .unwrap_or_else(|e| e.into_inner())
        .clone()
}

/// `allowed_fixme_codes_strict := codes`, for every thread.
pub fn set_allowed_fixme_codes_strict(codes: ISet) {
    *ALLOWED_FIXME_CODES_STRICT
        .write()
        .unwrap_or_else(|e| e.into_inner()) = codes;
}

/// `!code_agnostic_fixme`
pub fn code_agnostic_fixme() -> bool {
    CODE_AGNOSTIC_FIXME.load(AtomicOrdering::Relaxed)
}

/// `code_agnostic_fixme := x`, for every thread.
pub fn set_code_agnostic_fixme(x: bool) {
    CODE_AGNOSTIC_FIXME.store(x, AtomicOrdering::Relaxed)
}

/// `!get_hh_fixme_pos pos code`
pub fn get_hh_fixme_pos(pos: &Pos, code: ErrorCode) -> Option<Pos> {
    let f = with(|s| s.get_hh_fixme_pos.clone());
    f(pos, code)
}

/// `get_hh_fixme_pos := f`, for this thread.
pub fn set_get_hh_fixme_pos(f: FixmePosFn) {
    with(|s| s.get_hh_fixme_pos = f)
}

/// `!get_disallowed_fixme_pos pos code`
pub fn get_disallowed_fixme_pos(pos: &Pos, code: ErrorCode) -> Option<Pos> {
    let f = with(|s| s.get_disallowed_fixme_pos.clone());
    f(pos, code)
}

/// `get_disallowed_fixme_pos := f`, for this thread.
pub fn set_get_disallowed_fixme_pos(f: FixmePosFn) {
    with(|s| s.get_disallowed_fixme_pos = f)
}

/// `!get_ignore_pos pos code`
pub fn get_ignore_pos(pos: &Pos, code: ErrorCode) -> Option<Pos> {
    let f = with(|s| s.get_ignore_pos.clone());
    f(pos, code)
}

/// `get_ignore_pos := f`, for this thread.
pub fn set_get_ignore_pos(f: FixmePosFn) {
    with(|s| s.get_ignore_pos = f)
}

// ~~ diagnostics.ml ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

fn claim_as_reason(claim: Message<Pos>) -> Message<PosOrDecl> {
    // `Pos_or_decl.of_raw_pos` is the identity.
    claim
}

fn has_severity_err(e: &Diagnostic) -> bool {
    match e.severity {
        Severity::Err => true,
        Severity::Warning { .. } => false,
    }
}

/// `files_t_merge f x y` is a merge by file, i.e. given `x: t` and `y: t` it
/// goes through every file mentioned in `x`, and combines the error lists
/// using the provided callback. Cost is O(x).
fn files_t_merge(
    mut f: impl FnMut(
        &RelativePath,
        Option<Vec<Diagnostic>>,
        Option<Vec<Diagnostic>>,
    ) -> Option<Vec<Diagnostic>>,
    x: T,
    y: T,
) -> T {
    let mut acc = y;
    for (path, x) in x {
        // Each path of `x` is visited once, so what `acc` has for it is still
        // what `y` had.
        let y = acc.remove(&path);
        if let Some(data) = f(&path, Some(x), y) {
            acc.insert(path, data);
        }
    }
    acc
}

fn files_t_to_list(x: T) -> Vec<Diagnostic> {
    x.into_values().flatten().collect()
}

/// Values constructed here should not be used with incremental mode.
/// See assert in incremental_update.
pub fn from_diagnostic_list(errors: Vec<Diagnostic>) -> T {
    let mut map = T::new();
    if !errors.is_empty() {
        map.insert(RelativePath::EMPTY, errors);
    }
    map
}

/// Get most recently-ish added error.
///
/// `error_map` is the accumulator, whose lists are the reverse of the OCaml
/// ones: the last element of the OCaml list is the first one here. (Which
/// makes this the error that was added *first* to the greatest file, in OCaml
/// as well.)
fn get_last(error_map: &BTreeMap<RelativePath, Vec<Diagnostic>>) -> Option<&Diagnostic> {
    // If this map has more than one element, we pick an arbitrary file.
    // Because of that, we might not end up with the most recent error and
    // generate a less-specific error message. This should be rare.
    match error_map.last_key_value() {
        None => None,
        Some((_, error_list)) => error_list.first(),
    }
}

/// `Diagnostics.Error`
pub mod error {
    use super::Diagnostic;
    use super::ErrorHash;

    pub type T = Diagnostic;

    pub fn hash_for_saved_state(error: &T) -> ErrorHash {
        // `User_diagnostic.hash_diagnostic_for_saved_state` is an external
        // implemented by this function.
        error.hash_for_saved_state()
    }
}

pub fn drop_fixmed_errors<A, B>(errs: Vec<UserDiagnostic<A, B>>) -> Vec<UserDiagnostic<A, B>> {
    errs.into_iter().filter(|e| !e.is_fixmed).collect()
}

pub fn drop_fixmed_errors_in_files(t: T) -> T {
    let mut acc = T::new();
    for (file, errs) in t {
        let errs_without_fixmes = drop_fixmed_errors(errs);
        if !errs_without_fixmes.is_empty() {
            acc.insert(file, errs_without_fixmes);
        }
    }
    acc
}

fn drop_fixmes_if(err: T, drop: bool) -> T {
    if drop {
        drop_fixmed_errors_in_files(err)
    } else {
        err
    }
}

/// Get all errors emitted. Drops errors with valid HH_FIXME comments unless
/// `drop_fixmed` is `Some(false)`.
pub fn get_diagnostic_list(drop_fixmed: Option<bool>, err: T) -> Vec<Diagnostic> {
    let drop_fixmed = drop_fixmed.unwrap_or(true);
    files_t_to_list(drop_fixmes_if(err, drop_fixmed))
}

static badpos_message: LazyLock<String> = LazyLock::new(|| {
    format!(
        "Incomplete position information! Your type error is in this file, but we could only find related positions in another file. {}",
        ERROR_MESSAGE_SENTINEL_PLEASE_FILE_A_BUG_MESSAGE
    )
});

static badpos_message_2: LazyLock<String> = LazyLock::new(|| {
    format!(
        "Incomplete position information! We couldn't find the exact line of your type error in this definition. {}",
        ERROR_MESSAGE_SENTINEL_PLEASE_FILE_A_BUG_MESSAGE
    )
});

/// Run a computation; if it produces an error, call the continuation with
/// both the result and the error. The continuation can inspect or transform
/// the result. See [`try_`] for warning behavior.
pub fn try_with_result<Res>(
    f1: impl FnOnce() -> Res,
    f2: impl FnOnce(Res, Diagnostic) -> Res,
) -> Res {
    let (error_map_copy, accumulate_errors_copy, get_hh_fixme_pos_copy) = with(|s| {
        let error_map_copy = std::mem::take(&mut s.error_map);
        let accumulate_errors_copy = s.accumulate_errors;
        let no_fixme: FixmePosFn = Rc::new(|_, _| None);
        let get_hh_fixme_pos_copy = std::mem::replace(&mut s.get_hh_fixme_pos, no_fixme);
        s.accumulate_errors = true;
        s.depth += 1;
        (
            error_map_copy,
            accumulate_errors_copy,
            get_hh_fixme_pos_copy,
        )
    });
    let (result, errors) = {
        let _finally = finally(move || {
            restore(|s| {
                s.error_map = error_map_copy;
                s.accumulate_errors = accumulate_errors_copy;
                s.get_hh_fixme_pos = get_hh_fixme_pos_copy;
                s.depth -= 1;
            })
        });
        let result = f1();
        let errors = with(|s| std::mem::take(&mut s.error_map));
        (result, errors)
    };
    match get_last(&errors) {
        None => result,
        Some(UserDiagnostic {
            severity,
            code,
            claim,
            reasons,
            explanation,
            quickfixes,
            custom_msgs,
            function_pos,
            is_fixmed: _,
        }) => {
            let severity = *severity;
            // Remove bad position sentinel if present: we might be about to
            // add a new primary error position.
            let (claim, reasons) = {
                let Message(prim_pos, msg) = claim;
                if *msg == badpos_message.as_str() || *msg == badpos_message_2.as_str() {
                    match reasons.split_first() {
                        None => panic!("in try_with_result"),
                        Some((Message(_p, claim), reasons)) => (
                            Message(prim_pos.clone(), claim.clone()),
                            reasons.to_vec(),
                        ),
                    }
                } else {
                    (claim.clone(), reasons.clone())
                }
            };
            let error = make(
                severity,
                *code,
                quickfixes.clone(),
                custom_msgs.clone(),
                function_pos.clone(),
                claim,
                reasons,
                explanation.clone(),
            );
            // We ensure warnings do not affect typechecker behavior and are
            // not lost
            match severity {
                Severity::Err => f2(result, error),
                Severity::Warning { .. } => {
                    with(|s| {
                        if s.accumulate_errors {
                            record_warning_key(s, &error);
                            // `error :: current_list`
                            match s.error_map.get_mut(&s.current_file) {
                                Some(current_list) => current_list.push(error),
                                None => {
                                    s.error_map.insert(s.current_file.clone(), vec![error]);
                                }
                            }
                        }
                    });
                    result
                }
            }
        }
    }
}

/// Reset errors before running `f` so that we can return the errors caused by
/// `f`. These errors are not added in the global list of errors.
///
/// `drop_fixmed` defaults to `true`.
pub fn do_<A>(drop_fixmed: Option<bool>, f: impl FnOnce() -> A) -> (T, A) {
    let drop_fixmed = drop_fixmed.unwrap_or(true);
    let (error_map_copy, accumulate_errors_copy, get_hh_fixme_pos_copy) = with(|s| {
        let error_map_copy = std::mem::take(&mut s.error_map);
        let accumulate_errors_copy = s.accumulate_errors;
        s.accumulate_errors = true;
        s.depth += 1;
        let get_hh_fixme_pos_copy = s.get_hh_fixme_pos.clone();
        (
            error_map_copy,
            accumulate_errors_copy,
            get_hh_fixme_pos_copy,
        )
    });
    let (result, out_errors) = {
        let _finally = finally(move || {
            restore(|s| {
                s.error_map = error_map_copy;
                s.accumulate_errors = accumulate_errors_copy;
                s.get_hh_fixme_pos = get_hh_fixme_pos_copy;
                s.depth -= 1;
            })
        });
        let result = f();
        let out_errors = with(|s| std::mem::take(&mut s.error_map));
        (result, out_errors)
    };
    // `files_t_map ~f:List.rev out_errors`: the lists of the accumulator are
    // already in the order the errors were added in.
    (drop_fixmes_if(out_errors, drop_fixmed), result)
}

pub fn run_in_context<A>(path: RelativePath, f: impl FnOnce() -> A) -> A {
    let context_copy = with(|s| std::mem::replace(&mut s.current_file, path));
    let _finally = finally(move || restore(|s| s.current_file = context_copy));
    f()
}

/// Run this function with span for the definition being checked. This is used
/// to check that the primary position for errors is not located outside the
/// span of the definition.
pub fn run_with_span<A>(span: Pos, f: impl FnOnce() -> A) -> A {
    let old_span = with(|s| std::mem::replace(&mut s.current_span, span));
    let _finally = finally(move || restore(|s| s.current_span = old_span));
    f()
}

/// Log important data if lazy_decl triggers a crash
fn lazy_decl_error_logging(error: &str) -> ! {
    let error_list = with(|s| files_t_to_list(s.error_map.clone()));
    // Print the current error list, which should be empty
    eprintln!("Error list(should be empty):");
    for err in &error_list {
        eprintln!("{}", crate::diagnostics::to_plain_string(err));
    }
    eprintln!("Offending error:");
    eprint!("{}", error);

    // Print out a larger stack trace
    eprintln!("Callstack:");
    eprint!("{}", Backtrace::force_capture());

    // Exit with special error code so we can see the log after
    std::process::exit(EXIT_STATUS_LAZY_DECL_BUG)
}

/// `compare_internal`, with the codes to compare `x` and `y` by.
fn compare_internal_with_codes(
    x: &Diagnostic,
    y: &Diagnostic,
    x_code: ErrorCode,
    y_code: ErrorCode,
) -> Ordering {
    // /!\ KEEP THIS IN SYNC WITH errors_impl.rs, `fn cmp_impl`
    // order by severity
    compare_severity(&x.severity, &y.severity)
        // order by file
        .then_with(|| x.claim.0.filename().cmp(y.claim.0.filename()))
        // Then within each file, sort by phase
        .then_with(|| {
            let x_phase = x_code / 1000;
            let y_phase = y_code / 1000;
            x_phase.cmp(&y_phase)
        })
        // If the phases are the same, sort by position
        .then_with(|| x.claim.0.cmp(&y.claim.0))
        // If the primary positions are also the same, sort by message text
        .then_with(|| x.claim.1.cmp(&y.claim.1))
        // If the message text is also the same, then continue comparing the
        // reason messages (which indicate the reason why Hack believes there
        // is an error reported in the claim message)
        .then_with(|| x.reasons.cmp(&y.reasons))
        // If everything else is the same, compare by code
        .then_with(|| x_code.cmp(&y_code))
}

fn compare_internal(x: &Diagnostic, y: &Diagnostic) -> Ordering {
    compare_internal_with_codes(x, y, x.code, y.code)
}

/// Sort and remove duplicates.
///
/// This is `crate::diagnostics::sort_and_dedup`, except that the `is_trusted`
/// of a warning takes no part in the order, as in OCaml (the `Ord` that
/// `oxidized` derives for `Severity` compares it).
pub fn sort(mut err: Vec<Diagnostic>) -> Vec<Diagnostic> {
    err.sort_by(compare_internal);
    // If two errors have the exact same messages and positions but different
    // codes, consider them equal for deduplication. The first one is kept.
    err.dedup_by(|y, x| {
        compare_internal_with_codes(x, y, x.code / 1000 * 1000, y.code / 1000 * 1000).is_eq()
    });
    err
}

pub fn get_sorted_diagnostic_list(drop_fixmed: Option<bool>, err: T) -> Vec<Diagnostic> {
    let drop_fixmed = drop_fixmed.unwrap_or(true);
    sort(files_t_to_list(drop_fixmes_if(err, drop_fixmed)))
}

/// Runs callback and returns `true` iff error count changed.
/// This seems evil, please avoid. Current uses are for sound dynamic
pub fn run_and_check_for_errors<Res>(f: impl FnOnce() -> Res) -> (Res, bool) {
    // `get_current_list`
    let count_errors = || {
        with(|s| match s.error_map.get(&s.current_file) {
            None => 0,
            Some(lst) => lst.iter().filter(|e| has_severity_err(e)).count(),
        })
    };
    let old_count = count_errors();
    let result = f();
    let new_count = count_errors();
    (result, old_count != new_count)
}

/// Return the list of errors caused by the function passed as parameter along
/// with its result.
pub fn do_with_context<A>(
    drop_fixmed: Option<bool>,
    path: RelativePath,
    f: impl FnOnce() -> A,
) -> (T, A) {
    run_in_context(path, || do_(drop_fixmed, f))
}

/// Turn on lazy decl mode for the duration of the closure. This runs without
/// returning the original state, since we collect it later in
/// do_with_lazy_decls_
pub fn run_in_decl_mode<A>(f: impl FnOnce() -> A) -> A {
    let old_in_lazy_decl = with(|s| std::mem::replace(&mut s.in_lazy_decl, true));
    let _finally = finally(move || restore(|s| s.in_lazy_decl = old_in_lazy_decl));
    f()
}

/// The text of the hhi files that are not on disk, by absolute path.
///
/// OCaml extracts the hhi files (and the `--extra-builtin` files of
/// `hh_single_type_check`) into a temporary directory, the `Hhi` prefix, and
/// `read_lines` reads them there. Here they are in the binary, under a `Hhi`
/// prefix that is not a directory; `read_lines` finds their text here.
static HHI_SOURCES: LazyLock<RwLock<BTreeMap<String, String>>> =
    LazyLock::new(|| RwLock::new(BTreeMap::new()));

/// Makes the text of an hhi file that is not on disk available to
/// [`read_lines`]. `path` is its absolute path (under the `Hhi` prefix).
pub fn register_hhi_source(path: String, contents: String) {
    HHI_SOURCES.write().unwrap().insert(path, contents);
}

/// The text of an hhi file that is not on disk: one that was registered, or
/// one of the binary's.
fn hhi_source(path: &str) -> Option<String> {
    if let Some(contents) = HHI_SOURCES.read().unwrap().get(path) {
        return Some(contents.clone());
    }
    let hhi_path = crate::relative_path::path_of_prefix(crate::relative_path::Prefix::Hhi).ok()?;
    if hhi_path.is_empty() {
        return None;
    }
    let name = path.strip_prefix(&hhi_path)?;
    let name = name.strip_prefix('/').unwrap_or(name);
    hhi::HHI_CONTENTS
        .iter()
        .find(|(hhi_name, _)| *hhi_name == name)
        .map(|(_, contents)| contents.to_string())
}

/// `In_channel.read_lines`: no last empty line, and no `\r` at the end of a
/// line.
fn lines_of(contents: &str) -> Vec<String> {
    contents.lines().map(|line| line.to_string()).collect()
}

/// The lines of `read_lines path`, and whether each of them is valid UTF-8
/// (`Stdlib.String.is_valid_utf_8`; the lines here are made valid).
pub fn read_lines_with_validity(path: &str) -> (Vec<String>, bool) {
    match std::fs::read(path) {
        Ok(contents) => (
            lines_of(&String::from_utf8_lossy(&contents)),
            std::str::from_utf8(&contents).is_ok(),
        ),
        // `Sys_error`: maybe a part of a multifile, else no lines.
        Err(_) => {
            let lines = crate::multifile::read_file_from_multifile(path).unwrap_or_default();
            if !lines.is_empty() {
                (lines, true)
            } else {
                match hhi_source(path) {
                    Some(contents) => (lines_of(&contents), true),
                    None => (vec![], true),
                }
            }
        }
    }
}

pub fn read_lines(path: &str) -> Vec<String> {
    read_lines_with_validity(path).0
}

pub fn read_lines_for_highlighted(path: &str) -> Option<Vec<String>> {
    let (lines, valid) = read_lines_with_validity(path);
    if valid { Some(lines) } else { None }
}

/// `int_of_float (Float.log10 (float_of_int x)) + 1`. For `x <= 0` the
/// logarithm is `-inf` or NaN, which `int_of_float` (a hardware conversion,
/// then OCaml's 63-bit tagging) turns into 0, hence 1; the `as` conversion
/// saturates instead, so the tagging is redone here.
pub fn num_digits(x: isize) -> isize {
    let truncated = (x as f64).log10() as i64;
    ((truncated << 1) >> 1) as isize + 1
}

/// Sort `xs` such that all the values that return the same value for `f x`
/// are consecutive. For any two elements x1 and x2 in xs where
/// `f x1 = f x2`, if x1 occurs before x2 in xs, then x1 also occurs before x2
/// in the returned list.
pub fn combining_sort<A>(xs: Vec<A>, f: impl Fn(&A) -> String) -> Vec<A> {
    let mut grouped: BTreeMap<String, Vec<A>> = BTreeMap::new();
    // In the order the keys were first seen in.
    let mut keys: Vec<String> = vec![];
    for x in xs {
        let key = f(&x);
        match grouped.get_mut(&key) {
            Some(members) => members.push(x),
            None => {
                grouped.insert(key.clone(), vec![x]);
                keys.push(key);
            }
        }
    }
    keys.into_iter()
        .flat_map(|key| grouped.remove(&key).unwrap_or_default())
        .collect()
}

/// Takes an error format option and gives back the error format that was
/// passed or the default formatter.
pub fn format_or_default(format: Option<Format>) -> Format {
    match format {
        Some(error_format) => error_format,
        None => Format::Highlighted,
    }
}

/// Returns a summary string indicating things like how many errors were
/// found, how many are displayed and how many were dropped.
///
/// E.g. "10 errors, 11 warnings found."
pub fn format_summary(
    format: Format,
    error_count: isize,
    warning_count: isize,
    dropped_count: Option<isize>,
    max_errors: Option<isize>,
) -> Option<String> {
    let no_errors_string = "No errors!";
    match format {
        Format::Context | Format::Agent | Format::Highlighted | Format::PlainHighlighted => {
            let error_count_message = if error_count == 0 {
                no_errors_string.to_string()
            } else {
                format!(
                    "{} error{}",
                    error_count,
                    if error_count == 1 { "" } else { "s" }
                )
            };
            let warning_count_message = if warning_count == 0 {
                "".to_string()
            } else {
                format!(
                    "{} {} warning{}",
                    if error_count == 0 { "" } else { "," },
                    warning_count,
                    if warning_count == 1 { "" } else { "s" }
                )
            };
            let found_s = if error_count + warning_count > 0 {
                " found"
            } else {
                ""
            };
            let truncated_message = match (max_errors, dropped_count) {
                (Some(max_errors), Some(dropped_count)) if dropped_count > 0 => format!(
                    " (only showing first {}, dropped {})",
                    max_errors, dropped_count
                ),
                (Some(max_errors), None) if error_count + warning_count >= max_errors => {
                    format!(" (max-errors is {}; more errors may exist)", max_errors)
                }
                _ => "".to_string(),
            };
            Some(format!(
                "{}{}{}{}\n",
                error_count_message, warning_count_message, found_s, truncated_message
            ))
        }
        Format::Extended | Format::Raw | Format::Plain => {
            if error_count + warning_count == 0 {
                Some(format!("{}\n", no_errors_string))
            } else {
                None
            }
        }
    }
}

fn log_unexpected(_error: &Diagnostic, _path: &RelativePath, desc: &str) {
    // `Hack_event_logger.invariant_violation_bug` does nothing in this build.
    // `Hh_logger.log`:
    eprintln!("UNEXPECTED: {}\n{}", desc, Backtrace::force_capture());
}

thread_local! {
    static ADDED_COUNT: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// How many diagnostics this thread has added so far (for code that memoises
/// work: an unchanged count means that the work reported nothing).
pub fn added_count() -> u64 {
    ADDED_COUNT.with(std::cell::Cell::get)
}

fn add_error_impl(error: Diagnostic) {
    ADDED_COUNT.with(|c| c.set(c.get() + 1));
    if with(|s| s.accumulate_errors) {
        let unexpected_path = with(|s| {
            if s.current_file.is_empty() && !s.allow_errors_in_default_path {
                Some(s.current_file.clone())
            } else {
                None
            }
        });
        if let Some(path) = unexpected_path {
            log_unexpected(&error, &path, "adding an error in default path");
        }
        with(|s| {
            record_warning_key(s, &error);
            // Cheap test to avoid duplicating most recent error
            match s.error_map.get_mut(&s.current_file) {
                Some(error_list) => match error_list.last() {
                    Some(old_error) if equal_diagnostic(&error, old_error) => {}
                    _ => error_list.push(error),
                },
                None => {
                    s.error_map.insert(s.current_file.clone(), vec![error]);
                }
            }
        })
    } else {
        // We have an error, but haven't handled it in any way
        //
        // (`User_diagnostic.to_absolute |> to_string`; the paths are
        // relative here.)
        let msg = crate::diagnostics::to_plain_string(&error);
        if with(|s| s.in_lazy_decl) {
            lazy_decl_error_logging(&msg)
        } else if error.is_fixmed {
        } else {
            assert_false_log_backtrace(Some(&msg))
        }
    }
}

/// Whether we've found at least one error (not warning)
pub fn currently_has_errors() -> bool {
    with(|s| match s.error_map.get(&s.current_file) {
        None => false,
        Some(lst) => lst.iter().any(has_severity_err),
    })
}

// HH_FIXMEs hook

/// The 'phps FixmeAllHackErrors' tool must be kept in sync with this list
static hard_banned_codes: LazyLock<ISet> = LazyLock::new(|| {
    ISet::from([
        Typing::InvalidIsAsExpressionHint as isize,
        Typing::InvalidEnforceableTypeArgument as isize,
        Typing::RequireArgsReify as isize,
        Typing::InvalidReifiedArgument as isize,
        Typing::GenericsNotAllowed as isize,
        Typing::InvalidNewableTypeArgument as isize,
        Typing::InvalidNewableTypeParamConstraints as isize,
        Typing::NewWithoutNewable as isize,
        Typing::NewClassReified as isize,
        Typing::MemoizeReified as isize,
        Typing::ClassGetReified as isize,
    ])
});

pub fn set_allow_errors_in_default_path(x: bool) {
    with(|s| s.allow_errors_in_default_path = x)
}

fn is_allowed_code_strict(code: ErrorCode) -> bool {
    ALLOWED_FIXME_CODES_STRICT
        .read()
        .unwrap_or_else(|e| e.into_inner())
        .contains(&code)
}

// Errors accumulator.

/// We still want to error somewhere to avoid silencing any kind of errors,
/// which could cause errors to creep into the codebase.
fn wrap_error_in_different_file(
    current_file: RelativePath,
    current_span: Pos,
    claim: Message<PosOrDecl>,
    reasons: Vec<Message<PosOrDecl>>,
) -> (Message<Pos>, Vec<Message<PosOrDecl>>) {
    let reasons = {
        let mut list = Vec::with_capacity(reasons.len() + 1);
        list.push(claim);
        list.extend(reasons);
        list
    };
    // `Hack_event_logger.type_check_primary_position_bug` (with the messages
    // and the call stack) does nothing in this build.
    let claim = if current_span.is_none() {
        Message(
            pos_make_from(current_file),
            BString::from(badpos_message.as_str()),
        )
    } else {
        Message(current_span, BString::from(badpos_message_2.as_str()))
    };
    (claim, reasons)
}

/// If primary position in error list isn't in current file, wrap with a
/// sentinel error
fn check_pos_msg(
    (claim, reasons): (Message<Pos>, Vec<Message<PosOrDecl>>),
) -> (Message<Pos>, Vec<Message<PosOrDecl>>) {
    let pos = &claim.0;
    // If error is reported inside the current span, or no span has been set
    // but the error is reported in the current file, then accept the error
    let outside = with(|s| {
        if s.ignore_pos_outside_current_span
            || pos_contains(&s.current_span, pos)
            || s.current_span.is_none() && *pos.filename() == s.current_file
            || s.current_file.is_empty()
        {
            None
        } else {
            Some((s.current_file.clone(), s.current_span.clone()))
        }
    });
    match outside {
        None => (claim, reasons),
        Some((current_file, current_span)) => wrap_error_in_different_file(
            current_file,
            current_span,
            claim_as_reason(claim),
            reasons,
        ),
    }
}

fn add_error_with_fixme_error(error: Diagnostic, explanation: String, fixme_pos: Pos) {
    let fixme_error = make(
        error.severity,
        error.code,
        error.quickfixes.clone(),
        error.custom_msgs.clone(),
        error.function_pos.clone(),
        Message(fixme_pos, BString::from(explanation)),
        vec![],
        Explanation::Empty,
    );
    add_error_impl(error);
    add_error_impl(fixme_error)
}

fn add_applied_fixme(error: Diagnostic) {
    let error = Diagnostic {
        is_fixmed: true,
        ..error
    };
    add_error_impl(error)
}

fn get_fixme(pos: &Pos, code: ErrorCode) -> Option<(Pos, SuppressionKind)> {
    match get_hh_fixme_pos(pos, code) {
        Some(pos) => Some((
            pos,
            SuppressionKind::Fixme {
                forbidden_decl_fixme: false,
            },
        )),
        None => match get_ignore_pos(pos, code) {
            Some(pos) => Some((pos, SuppressionKind::Ignore)),
            None => match get_disallowed_fixme_pos(pos, code) {
                Some(pos) => Some((
                    pos,
                    SuppressionKind::Fixme {
                        forbidden_decl_fixme: true,
                    },
                )),
                None => None,
            },
        },
    }
}

fn try_apply_fixme(pos: &Pos, code: ErrorCode, severity: Severity) -> FixmeOutcome {
    match get_fixme(pos, code) {
        None => {
            // Fixmes and banned decl fixmes are separated by the parser
            // because Errors can't recover the position information after the
            // fact. This is the default case, where an HH_FIXME comment is
            // not present. Therefore, the remaining cases are variations on
            // behavior when a fixme is present
            FixmeOutcome::NotFixmed(None)
        }
        Some((fixme_pos, fixme_kind)) => {
            // We use severity based on code for warning-to-error migration
            // scenarios. Sometimes we want to introduce an new error as a
            // warning first. In that case, to avoid having to codemod any
            // HH_IGNORE along with their codes when the warnings become
            // errors, we'll first make the errors have a non-warning code but
            // have warning severity at first, and we'll force suppression
            // using HH_FIXME instead of HH_IGNORE.
            let severity_based_on_code = match warning_of_enum(code) {
                Some(_) => Severity::Warning { is_trusted: true },
                None => Severity::Err,
            };
            match (severity_based_on_code, fixme_kind) {
                (
                    Severity::Err,
                    SuppressionKind::Fixme {
                        forbidden_decl_fixme,
                    },
                ) => {
                    if hard_banned_codes.contains(&code) {
                        let explanation = format!(
                            "You cannot use `HH_FIXME` or `HH_IGNORE_ERROR` comments to suppress error {}, and this cannot be enabled by configuration",
                            code
                        );
                        FixmeOutcome::NotFixmed(Some(FixmeError {
                            explanation,
                            fixme_pos,
                        }))
                    } else if pos.filename().prefix().is_hhi() {
                        FixmeOutcome::Fixmed
                    } else if forbidden_decl_fixme {
                        let explanation = format!(
                            "You cannot use `HH_FIXME` or `HH_IGNORE_ERROR` comments to suppress error {} in declarations",
                            code
                        );
                        FixmeOutcome::NotFixmed(Some(FixmeError {
                            explanation,
                            fixme_pos,
                        }))
                    } else if is_allowed_code_strict(code) {
                        FixmeOutcome::Fixmed
                    } else {
                        let explanation = format!(
                            "You cannot use `HH_FIXME` or `HH_IGNORE_ERROR` comments to suppress error {}",
                            code
                        );
                        FixmeOutcome::NotFixmed(Some(FixmeError {
                            explanation,
                            fixme_pos,
                        }))
                    }
                }
                (Severity::Warning { .. }, SuppressionKind::Fixme { .. }) => {
                    let explanation = format!(
                        "You cannot use `HH_FIXME` comments to suppress warnings. Use `HH_IGNORE[{}]` instead.",
                        code
                    );
                    FixmeOutcome::NotFixmed(Some(FixmeError {
                        explanation,
                        fixme_pos,
                    }))
                }
                (Severity::Warning { .. }, SuppressionKind::Ignore) => FixmeOutcome::Fixmed,
                (Severity::Err, SuppressionKind::Ignore) => {
                    let explanation = match severity {
                        Severity::Err => format!(
                            "You cannot use `HH_IGNORE` to suppress non-warning code {}. Hack errors should not be suppressed. You should try your best to fix the code causing the error, or incidents will happen.",
                            code
                        ),
                        Severity::Warning { .. } => format!(
                            "This warning code {} will soon be migrated to be an error. Try your best to fix it, or if not possible, suppress it with `HH_FIXME` instead of `HH_IGNORE` and report your case to us.",
                            code
                        ),
                    };
                    FixmeOutcome::NotFixmed(Some(FixmeError {
                        explanation,
                        fixme_pos,
                    }))
                }
            }
        }
    }
}

pub fn is_suppressed<P>(error: &UserDiagnostic<Pos, P>) -> bool {
    let Message(pos, _) = &error.claim;
    match try_apply_fixme(pos, error.code, error.severity) {
        FixmeOutcome::Fixmed => true,
        FixmeOutcome::NotFixmed(_) => false,
    }
}

pub fn add_diagnostic(diag: Diagnostic) {
    let UserDiagnostic {
        severity,
        code,
        claim,
        reasons,
        explanation,
        quickfixes,
        custom_msgs,
        function_pos,
        is_fixmed: _,
    } = diag;
    let (claim, reasons) = check_pos_msg((claim, reasons));
    let diag = make(
        severity,
        code,
        quickfixes,
        custom_msgs,
        function_pos,
        claim,
        reasons,
        explanation,
    );

    match try_apply_fixme(&diag.claim.0, code, severity) {
        FixmeOutcome::NotFixmed(None) => add_error_impl(diag),
        FixmeOutcome::NotFixmed(Some(FixmeError {
            explanation,
            fixme_pos,
        })) => add_error_with_fixme_error(diag, explanation, fixme_pos),
        FixmeOutcome::Fixmed => add_applied_fixme(diag),
    }
}

/// For each file of `err_`, its errors are put (reversed) in front of the
/// ones `err` has for that file.
pub fn merge(err_: T, err: T) -> T {
    let append = |_: &RelativePath, x: Option<Vec<Diagnostic>>, y: Option<Vec<Diagnostic>>| {
        let x = x.unwrap_or_default();
        let y = y.unwrap_or_default();
        // `List.rev_append x y`
        let mut list = Vec::with_capacity(x.len() + y.len());
        list.extend(x.into_iter().rev());
        list.extend(y);
        Some(list)
    };
    files_t_merge(append, err_, err)
}

/// `incremental_update old new_ rechecked` is for updating errors. It starts
/// with `old`, removes every error in `rechecked`, then adds every error
/// mentioned in `new_`.
pub fn incremental_update(old: T, new_: T, rechecked: &BTreeSet<RelativePath>) -> T {
    // Helper to detect coding oversight
    let assert_path_is_real = |path: &RelativePath| {
        if path.is_empty() {
            assert_false_log_backtrace(Some(concat!(
                "Default (untracked) error sources should not get into incremental ",
                "mode. There might be a missing call to `Diagnostics.do_with_context`/",
                "`run_in_context` somwhere or incorrectly used `Diagnostics.from_diagnostic_list`.",
            )))
        }
    };
    let new_paths: BTreeSet<RelativePath> = new_.keys().cloned().collect();

    // Replace old errors with new
    let res = files_t_merge(
        |path, new_, old| {
            assert_path_is_real(path);
            match new_ {
                Some(new_) => Some(new_),
                None => old,
            }
        },
        new_,
        old,
    );
    // For files that were rechecked, but had no errors - remove them from maps
    let mut res = res;
    for path in rechecked {
        if !new_paths.contains(path) {
            res.remove(path);
        }
    }
    res
}

fn add_list(
    severity: Severity,
    code: ErrorCode,
    quickfixes: Option<Vec<Quickfix<Pos>>>,
    claim: Message<Pos>,
    reasons: Vec<Message<PosOrDecl>>,
    explanation: Explanation<PosOrDecl>,
) {
    add_diagnostic(make(
        severity,
        code,
        quickfixes.unwrap_or_default(),
        vec![],
        None,
        claim,
        reasons,
        explanation,
    ))
}

fn add(severity: Severity, code: ErrorCode, pos: Pos, msg: String) {
    add_list(
        severity,
        code,
        None,
        Message(pos, BString::from(msg)),
        vec![],
        Explanation::Empty,
    )
}

pub fn count(drop_fixmed: Option<bool>, err: &T) -> isize {
    let drop_fixmed = drop_fixmed.unwrap_or(true);
    err.values()
        .map(|x| per_file_diagnostic_count(Some(drop_fixmed), x))
        .sum()
}

/// `has_no_errors_or_warnings t` returns true if there are no errors or
/// warnings. Please use this function *only* where you want to know if
/// there's anything to show the user (e.g., deciding whether to print an
/// "Errors:" section). Avoid using this for anything non-display related, and
/// especially do not have different type checker code paths based on
/// warnings.
pub fn has_no_errors_or_warnings(drop_fixmed: Option<bool>, err: &T) -> bool {
    if drop_fixmed.unwrap_or(true) {
        err.values().all(|errs| errs.iter().all(|e| e.is_fixmed))
    } else {
        err.is_empty()
    }
}

/// `has_errors t` returns true iff there is at least one actual error in `t`.
/// Warnings (severity=Warning) do not affect return value.
pub fn has_errors(drop_fixmed: Option<bool>, err: &T) -> bool {
    let drop_fixmed = drop_fixmed.unwrap_or(true);
    err.values().any(|errors| {
        errors
            .iter()
            .any(|e| !(drop_fixmed && e.is_fixmed) && has_severity_err(e))
    })
}

/// `has_no_errors t` is `not (has_errors t)`.
pub fn has_no_errors(drop_fixmed: Option<bool>, err: &T) -> bool {
    !has_errors(drop_fixmed, err)
}

pub fn get_current_span() -> Pos {
    with(|s| s.current_span.clone())
}

/// `Diagnostics.empty`
pub const empty: T = T::new();

pub fn from_file_diagnostic_list(errors: Vec<(RelativePath, Diagnostic)>) -> T {
    let mut map = T::new();
    for (file, diag) in errors {
        map.entry(file).or_default().push(diag);
    }
    // `diag :: errors_for_file`: the last error of a file comes first.
    for errors_for_file in map.values_mut() {
        errors_for_file.reverse();
    }
    map
}

pub fn as_map(t: T) -> relative_path::map::Map<Vec<Diagnostic>> {
    t
}

/// Add `errors` to the errors accumulated so far, each file's after the ones
/// it has. (`error_map := merge errors !error_map`)
pub fn merge_into_current(errors: T) {
    with(|s| {
        for diag in errors.values().flatten() {
            record_warning_key(s, diag)
        }
        for (path, x) in errors {
            // `List.rev_append x y` with `y` the list of the accumulator,
            // which is kept reversed here.
            s.error_map.entry(path).or_default().extend(x);
        }
    })
}

// Accessors.

fn per_file_diagnostic_count(drop_fixmed: Option<bool>, errors: &PerFileDiagnostics) -> isize {
    let drop_fixmed = drop_fixmed.unwrap_or(true);
    errors
        .iter()
        .filter(|e| !(drop_fixmed && e.is_fixmed))
        .count() as isize
}

pub fn get_file_diagnostics(
    drop_fixmed: Option<bool>,
    t: &T,
    file: &RelativePath,
) -> PerFileDiagnostics {
    let drop_fixmed = drop_fixmed.unwrap_or(true);
    match t.get(file) {
        None => vec![],
        Some(errors) => {
            if drop_fixmed {
                drop_fixmed_errors(errors.clone())
            } else {
                errors.clone()
            }
        }
    }
}

pub fn fold_per_file_diagnostics<Acc>(
    errors: &PerFileDiagnostics,
    init: Acc,
    f: impl FnMut(Acc, &Diagnostic) -> Acc,
) -> Acc {
    errors.iter().fold(init, f)
}

pub fn iter_diagnostic_list(drop_fixmed: Option<bool>, f: impl FnMut(&Diagnostic), err: &T) {
    get_sorted_diagnostic_list(drop_fixmed, err.clone())
        .iter()
        .for_each(f)
}

pub fn fold_errors<A>(
    drop_fixmed: Option<bool>,
    t: &T,
    init: A,
    mut f: impl FnMut(&RelativePath, &Diagnostic, A) -> A,
) -> A {
    let drop_fixmed = drop_fixmed.unwrap_or(true);
    let mut acc = init;
    for (source, errors) in t {
        // `List.fold_right`
        for error in errors.iter().rev() {
            if !(drop_fixmed && error.is_fixmed) {
                acc = f(source, error, acc);
            }
        }
    }
    acc
}

/// Get paths that have errors which haven't been HH_FIXME'd.
pub fn get_failed_files(err: &T) -> BTreeSet<RelativePath> {
    err.iter()
        .filter(|(_, errs)| errs.iter().any(|e| !e.is_fixmed))
        .map(|(source, _)| source.clone())
        .collect()
}

/// Count of warnings by error code, excluding fixme'd diagnostics.
pub fn warning_counts_by_code(errors: &T) -> IMap<isize> {
    let mut acc: IMap<isize> = IMap::new();
    for diag in errors.values().flatten() {
        if diag.is_fixmed {
            continue;
        }
        match diag.severity {
            Severity::Warning { .. } => *acc.entry(diag.code).or_insert(0) += 1,
            Severity::Err => {}
        }
    }
    acc
}

/// This ignores warnings.
fn first_n_distinct_error_codes<'a>(
    n: usize,
    errors: impl Iterator<Item = &'a Diagnostic>,
) -> Vec<ErrorCode> {
    let mut codes = ISet::new();
    for diag in errors {
        match diag.severity {
            Severity::Err => {
                codes.insert(diag.code);
                if codes.len() >= n {
                    break;
                }
            }
            Severity::Warning { .. } => {}
        }
    }
    codes.into_iter().collect()
}

/// Get the error code of the first error which hasn't been HH_FIXME'd.
pub fn choose_code_opt(t: &T) -> Option<isize> {
    first_n_distinct_error_codes(1, t.values().flatten().filter(|e| !e.is_fixmed))
        .first()
        .copied()
}

// Specific errors

pub fn experimental_feature(pos: Pos, msg: &str) {
    add(
        Severity::Err,
        0,
        pos,
        format!("Cannot use experimental feature: {}", msg),
    )
}

// Typing errors

fn log_exception_occurred(pos: &Pos, e: &crate::exception::T) {
    // (`Pos.to_absolute`: the path is relative here.)
    let pos_str = pos.string().to_string();
    // `Hack_event_logger.type_check_exn_bug` does nothing in this build.
    // `Hh_logger.error`:
    eprintln!(
        "Exception while typechecking at position {}\n{}",
        pos_str,
        crate::exception::to_string(e)
    );
}

fn log_invariant_violation(desc: &str, pos: &Pos, telemetry: crate::telemetry::T) {
    // (`Pos.to_absolute`: the path is relative here.)
    let pos_str = pos.string().to_string();
    // `Hack_event_logger.invariant_violation_bug` does nothing in this build.
    // `Hh_logger.error`:
    eprintln!(
        "Invariant violation at position {}\n{}",
        pos_str,
        crate::telemetry::to_string(
            None,
            &crate::telemetry::string_(None, "desc", desc, telemetry)
        )
    );
}

/// The contents of the following error message can trigger `hh rage` in
/// sandcastle. If you change it, please make sure the existing trigger in
/// `flib/intern/sandcastle/hack/SandcastleCheckHackOnDiffsStep.php` still
/// catches this error message.
static please_file_a_bug_message: LazyLock<String> = LazyLock::new(|| {
    let hacklang_feedback_support_link = "https://fb.workplace.com/groups/hackforhiphop/";
    let hh_rage = crate::typing_reason::md_codify("hh rage");
    format!(
        "Please run {} and post in {}.",
        hh_rage, hacklang_feedback_support_link
    )
});

static remediation_message: LazyLock<String> = LazyLock::new(|| {
    format!(
        "Addressing other errors, restarting the typechecker with {}, or rebasing might resolve this error.",
        crate::typing_reason::md_codify("hh restart")
    )
});

static internal_compiler_error_msg: LazyLock<String> = LazyLock::new(|| {
    format!(
        "Encountered an internal compiler error while typechecking this. {} {}",
        remediation_message.as_str(),
        please_file_a_bug_message.as_str()
    )
});

/// The intention is to introduce invariant violations with `report_to_user`
/// set to `false` initially. Then we observe and confirm that the invariant
/// is not repeatedly violated. Only then, we set it to `true` in a subsequent
/// release. This should prevent us from blocking users unexpectedly while
/// gradually introducing signal for unexpected compiler states.
pub fn invariant_violation(
    pos: Pos,
    telemetry: crate::telemetry::T,
    desc: &str,
    report_to_user: bool,
) {
    log_invariant_violation(desc, &pos, telemetry);
    if report_to_user {
        add_diagnostic(make_err(
            Typing::InvariantViolated as isize,
            Message(pos, BString::from(internal_compiler_error_msg.as_str())),
            vec![],
            Explanation::Empty,
        ))
    }
}

pub fn exception_occurred(pos: Pos, exn: &crate::exception::T) {
    log_exception_occurred(&pos, exn);
    add_diagnostic(make_err(
        Typing::ExceptionOccurred as isize,
        Message(pos, BString::from(internal_compiler_error_msg.as_str())),
        vec![],
        Explanation::Empty,
    ))
}

pub fn internal_error(pos: Pos, msg: &str) {
    add_diagnostic(make_err(
        Typing::InternalError as isize,
        Message(pos, BString::from(format!("Internal error: {}", msg))),
        vec![],
        Explanation::Empty,
    ))
}

pub fn typechecker_timeout(pos: Pos, fn_name: &str, seconds: isize) {
    let claim = Message(
        pos,
        BString::from(format!(
            "Type checker timed out after {} seconds whilst checking function {}",
            seconds, fn_name
        )),
    );
    add_diagnostic(make_err(
        Typing::TypecheckerTimeout as isize,
        claim,
        vec![],
        Explanation::Empty,
    ))
}

// Typing decl errors

/// TODO: Remove use of `User_diagnostic.t` representation for nested error
pub fn function_is_not_dynamically_callable(function_name: &str, error: &Diagnostic) {
    let function_name =
        crate::typing_reason::md_codify(crate::typing_reason::strip_ns(function_name));
    let nested_error_reason = to_list_(error);
    add_list(
        Severity::Err,
        error.code,
        None,
        Message(
            error.claim.0.clone(),
            BString::from(format!(
                "Function  {} is not dynamically callable.",
                function_name
            )),
        ),
        nested_error_reason,
        Explanation::Empty,
    )
}

/// TODO: Remove use of `User_diagnostic.t` representation for nested error
pub fn method_is_not_dynamically_callable(
    pos: Pos,
    method_name: &str,
    class_name: &str,
    support_dynamic_type_attribute: bool,
    parent_class_opt: Option<(PosOrDecl, String)>,
    error_opt: Option<&Diagnostic>,
) {
    let method_name = crate::typing_reason::md_codify(crate::typing_reason::strip_ns(method_name));
    let class_name = crate::typing_reason::md_codify(crate::typing_reason::strip_ns(class_name));

    let (code, pos, nested_error_reason) = match error_opt {
        None => (Typing::ImplementsDynamic as isize, pos, vec![]),
        Some(error) => (error.code, error.claim.0.clone(), to_list_(error)),
    };

    let parent_class_reason = match parent_class_opt {
        None => vec![],
        Some((parent_class_pos, parent_class_name)) => {
            let parent_class_name = crate::typing_reason::md_codify(
                crate::typing_reason::strip_ns(&parent_class_name),
            );
            vec![Message(
                parent_class_pos,
                BString::from(format!(
                    "Method {} is defined in the super class {} and is not overridden",
                    method_name, parent_class_name
                )),
            )]
        }
    };

    let attribute_reason = match support_dynamic_type_attribute {
        true => vec![],
        false => vec![Message(
            pos.clone(),
            BString::from(format!(
                "A parameter of {} is not enforceable. Try adding the <<{}>> attribute to the method to check if its code is safe for dynamic calling.",
                method_name,
                naming_special_names_rust::user_attributes::SUPPORT_DYNAMIC_TYPE
            )),
        )],
    };

    let mut reasons = parent_class_reason;
    reasons.extend(attribute_reason);
    reasons.extend(nested_error_reason);
    add_list(
        Severity::Err,
        code,
        None,
        Message(
            pos,
            BString::from(format!(
                "Method  {} in class {} is not dynamically callable.",
                method_name, class_name
            )),
        ),
        reasons,
        Explanation::Empty,
    )
}

/// Raise different types of error for accessing global variables.
pub fn global_access_error(error_code: GlobalAccessCheck, pos: Pos, message: String) {
    add(Severity::Err, error_code as isize, pos, message)
}

// Try if errors.

/// Run a callback; if it produces an error, call the error handler instead of
/// adding the error to the error map. Warnings are added to the error map and
/// don't trigger the error handler.
///
/// The error given to the handler is the first one that was added (for the
/// file that sorts last, when there are several). When that one is a warning,
/// the handler is not called and everything else `f1` added is dropped: as
/// the OCaml says, a `try_` around something that warns is a bug.
pub fn try_<A>(f1: impl FnOnce() -> A, f2: impl FnOnce(Diagnostic) -> A) -> A {
    try_with_result(f1, |_, err| f2(err))
}

/// Run the callback and return `true` iff no errors, `false` otherwise.
/// Warnings (severity=Warning) do not affect the return value. The result of
/// the callback is discarded.
pub fn try_no_errors<Res>(f: impl FnOnce() -> Res) -> bool {
    try_(
        || {
            let _ = f();
            true
        },
        |_| false,
    )
}

// Do.

/// ignore errors produced by function passed in argument.
pub fn ignore_<Res>(f: impl FnOnce() -> Res) -> Res {
    let (allow_errors_in_default_path_copy, ignore_pos_outside_current_span_copy) = with(|s| {
        (
            s.allow_errors_in_default_path,
            s.ignore_pos_outside_current_span,
        )
    });
    set_allow_errors_in_default_path(true);
    with(|s| s.ignore_pos_outside_current_span = true);
    let (_, result) = do_(None, f);
    // (Not restored when `f` panics, as in OCaml when it raises.)
    set_allow_errors_in_default_path(allow_errors_in_default_path_copy);
    with(|s| s.ignore_pos_outside_current_span = ignore_pos_outside_current_span_copy);
    result
}

/// Like [`try_`] but only calls the error handler if both an error occurs and
/// the condition holds. Otherwise adds the error to the error map.
pub fn try_when<Res>(
    f: impl FnOnce() -> Res,
    if_error_and: impl FnOnce() -> bool,
    then_: impl FnOnce(Diagnostic),
) -> Res {
    try_with_result(f, |result, error| {
        // Note: we only reach here for errors proper (severity = Err)
        if if_error_and() {
            then_(error)
        } else {
            add_diagnostic(error)
        }
        result
    })
}

pub fn filter(errors: T, mut f: impl FnMut(&RelativePath, &Diagnostic) -> bool) -> T {
    let mut map = T::new();
    for (path, errors) in errors {
        let errors: Vec<Diagnostic> = errors.into_iter().filter(|e| f(&path, e)).collect();
        if !errors.is_empty() {
            map.insert(path, errors);
        }
    }
    map
}

fn fold<Acc>(
    errors: &T,
    init: Acc,
    mut f: impl FnMut(&RelativePath, &Diagnostic, Acc) -> Acc,
) -> Acc {
    let mut acc = init;
    for (path, errors) in errors {
        for error in errors {
            acc = f(path, error, acc);
        }
    }
    acc
}

pub fn count_errors_and_warnings<A, B>(error_list: &[UserDiagnostic<A, B>]) -> (isize, isize) {
    error_list
        .iter()
        .fold((0, 0), |(err_count, warn_count), e| match e.severity {
            Severity::Warning { .. } => (err_count, warn_count + 1),
            Severity::Err => (err_count + 1, warn_count),
        })
}

pub fn filter_out_mergebase_warnings(
    mergebase_warning_hashes: Option<&WarningsSavedState>,
    errors: T,
) -> T {
    match mergebase_warning_hashes {
        None => errors,
        Some(mergebase_warning_hashes) => filter(errors, |_path, error| match error.severity {
            Severity::Err => true,
            Severity::Warning { .. } => {
                !mergebase_warning_hashes.contains(&error::hash_for_saved_state(error))
            }
        }),
    }
}

pub fn filter_out_warnings(errors: T) -> T {
    filter(errors, |_path, error| match error.severity {
        Severity::Err => true,
        Severity::Warning { .. } => false,
    })
}

pub fn make_warning_saved_state(errors: &T) -> WarningsSavedState {
    fold(
        errors,
        WarningsSavedState::new(),
        |_path, error, mut ss| match error.severity {
            Severity::Err => ss,
            Severity::Warning { .. } => {
                let hash = error::hash_for_saved_state(error);
                ss.insert(hash);
                ss
            }
        },
    )
}

thread_local! {
    /// Whether the diagnostics added now come from a warning check (see
    /// [`start_recording_warning_keys`]). A cell of its own: `Tast_visitor`
    /// sets it around the warning handlers at every node.
    static RECORDING_WARNING_CHECK: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Record the key of `diag` if it is a warning added by a warning check to
/// the accumulator of [`start_recording_warning_keys`].
fn record_warning_key(s: &mut State, diag: &Diagnostic) {
    if let Some((depth, keys)) = &mut s.warning_keys {
        if *depth == s.depth
            && matches!(diag.severity, Severity::Warning { .. })
            && RECORDING_WARNING_CHECK.get()
        {
            keys.push((diag.code, diag.claim.0.clone()))
        }
    }
}

/// Start recording the `(code, pos)` of the warnings that the warning checks
/// add to the current accumulator, from now to
/// [`take_recorded_warning_keys`] (no OCaml counterpart). The warning checks
/// mark the time they run with [`set_recording_warning_check`].
///
/// `Typing_check_job` runs the warning checks a second time, on their own,
/// in [`collect_warning_keys`], to know the keys of the warnings they give.
/// When that second run is on the same TAST as the first (a definition
/// without a dynamic TAST), its keys are those of the warnings the first run
/// added to the accumulator: the same handlers, on the same TAST, in the
/// same environments. A warning that the first run does not add because it
/// is the same as the last diagnostic (`add_error_impl`) is recorded too:
/// the second run, which starts with an empty accumulator, would add it.
/// The warnings added in a nested accumulator ([`do_`], [`try_with_result`])
/// are not recorded unless they are added to this one in the end, as in the
/// second run.
pub fn start_recording_warning_keys() {
    RECORDING_WARNING_CHECK.set(false);
    with(|s| s.warning_keys = Some((s.depth, vec![])))
}

/// The keys recorded since [`start_recording_warning_keys`] (in the order the
/// warnings were added), and stop recording.
pub fn take_recorded_warning_keys() -> Vec<(isize, Pos)> {
    RECORDING_WARNING_CHECK.set(false);
    with(|s| s.warning_keys.take().map_or(vec![], |(_, keys)| keys))
}

/// Whether the warning checks are running (see
/// [`start_recording_warning_keys`]).
pub fn set_recording_warning_check(b: bool) {
    RECORDING_WARNING_CHECK.set(b)
}

/// Run `f` in an isolated error context and return the set of `(code, pos)`
/// pairs for any warnings produced. The warnings are not added to the current
/// accumulator.
pub fn collect_warning_keys(f: impl FnOnce()) -> Vec<(isize, Pos)> {
    let (errors, ()) = do_(Some(false), f);
    let mut acc = vec![];
    for diag in errors.values().flatten() {
        match diag.severity {
            Severity::Warning { .. } => acc.push((diag.code, diag.claim.0.clone())),
            Severity::Err => {}
        }
    }
    // Each key was consed onto `acc`.
    acc.reverse();
    acc
}

fn trust_warning(diag: &mut Diagnostic) {
    diag.severity = Severity::Warning { is_trusted: true };
}

/// For each accumulated warning with `is_trusted = false` whose `(code, pos)`
/// appears in `keys`, set `is_trusted = true`.
pub fn mark_warnings_trusted(keys: &[(isize, Pos)]) {
    let key_set: BTreeSet<(isize, &Pos)> = keys.iter().map(|(code, pos)| (*code, pos)).collect();
    with(|s| {
        for diag in s.error_map.values_mut().flatten() {
            match diag.severity {
                Severity::Warning { is_trusted: false }
                    if key_set.contains(&(diag.code, &diag.claim.0)) =>
                {
                    trust_warning(diag)
                }
                _ => {}
            }
        }
    })
}

/// Whether an accumulated warning has `is_trusted = false` (otherwise
/// [`mark_warnings_trusted`] changes nothing, whatever its keys). Not in the
/// OCaml.
pub fn has_untrusted_warnings() -> bool {
    with(|s| {
        s.error_map
            .values()
            .flatten()
            .any(|diag| matches!(diag.severity, Severity::Warning { is_trusted: false }))
    })
}

/// Mark all accumulated warnings as `is_trusted = true`. Used when no dynamic
/// TAST exists (all params are enforceable).
pub fn mark_all_warnings_trusted() {
    with(|s| {
        for diag in s.error_map.values_mut().flatten() {
            match diag.severity {
                Severity::Warning { is_trusted: false } => trust_warning(diag),
                _ => {}
            }
        }
    })
}

/// Port of `fixme_provider.ml` (`Fixme_provider`): the table containing all
/// the HH_FIXMEs found in the source code. Associates:
///
///   filename =>
///   line number guarded by HH_FIXME =>
///   error_node_number =>
///   position of HH_FIXME comment
///
/// The tables are thread local (they are in shared memory in OCaml, for every
/// worker): a file's comments must be provided on the thread that reports the
/// file's errors.
pub mod fixme_provider {
    use std::cell::RefCell;
    use std::collections::BTreeMap;
    use std::collections::BTreeSet;

    use oxidized::i_map::IMap;
    use oxidized::i_set::ISet;
    use oxidized::pos::Pos;
    use oxidized::scoured_comments::ScouredComments;
    use relative_path::RelativePath;

    use super::ErrorCode;

    /// `Fixme_provider.FixmeMap`
    pub mod fixme_map {
        pub type T = oxidized::scoured_comments::Fixmes;
    }

    #[derive(Clone, Default)]
    struct Fixmes {
        hh_fixmes: BTreeMap<RelativePath, fixme_map::T>,
        decl_hh_fixmes: BTreeMap<RelativePath, fixme_map::T>,
        disallowed_fixmes: BTreeMap<RelativePath, fixme_map::T>,
        ignores: BTreeMap<RelativePath, fixme_map::T>,
    }

    thread_local! {
        static FIXMES: RefCell<Fixmes> = RefCell::new(Fixmes::default());
    }

    /// One of the `get_*` functions of OCaml, on the tables of this thread.
    type GetMap = for<'a> fn(&'a Fixmes, &RelativePath) -> Option<&'a fixme_map::T>;

    fn get_fixmes<'a>(fixmes: &'a Fixmes, filename: &RelativePath) -> Option<&'a fixme_map::T> {
        match fixmes.hh_fixmes.get(filename) {
            None => fixmes.decl_hh_fixmes.get(filename),
            Some(x) => Some(x),
        }
    }

    fn get_hh_fixmes_<'a>(fixmes: &'a Fixmes, filename: &RelativePath) -> Option<&'a fixme_map::T> {
        fixmes.hh_fixmes.get(filename)
    }

    fn get_decl_hh_fixmes_<'a>(
        fixmes: &'a Fixmes,
        filename: &RelativePath,
    ) -> Option<&'a fixme_map::T> {
        fixmes.decl_hh_fixmes.get(filename)
    }

    fn get_disallowed_fixmes<'a>(
        fixmes: &'a Fixmes,
        filename: &RelativePath,
    ) -> Option<&'a fixme_map::T> {
        fixmes.disallowed_fixmes.get(filename)
    }

    fn get_ignores<'a>(fixmes: &'a Fixmes, filename: &RelativePath) -> Option<&'a fixme_map::T> {
        fixmes.ignores.get(filename)
    }

    /// `Fixme_provider.get_fixmes filename` (added by F6 for `UnusedFixmes`).
    pub fn get_fixmes_of_file(filename: &RelativePath) -> Option<fixme_map::T> {
        FIXMES.with(|fixmes| get_fixmes(&fixmes.borrow(), filename).cloned())
    }

    /// `Fixme_provider.get_ignores filename` (added by F6 for `UnusedFixmes`).
    pub fn get_ignores_of_file(filename: &RelativePath) -> Option<fixme_map::T> {
        FIXMES.with(|fixmes| get_ignores(&fixmes.borrow(), filename).cloned())
    }

    pub fn get_hh_fixmes(filename: &RelativePath) -> Option<fixme_map::T> {
        FIXMES.with(|fixmes| get_hh_fixmes_(&fixmes.borrow(), filename).cloned())
    }

    pub fn get_decl_hh_fixmes(filename: &RelativePath) -> Option<fixme_map::T> {
        FIXMES.with(|fixmes| get_decl_hh_fixmes_(&fixmes.borrow(), filename).cloned())
    }

    pub fn provide_hh_fixmes(filename: RelativePath, fixme_map: fixme_map::T) {
        if !fixme_map.is_empty() {
            FIXMES.with(|fixmes| fixmes.borrow_mut().hh_fixmes.insert(filename, fixme_map));
        }
    }

    pub fn provide_decl_hh_fixmes(filename: RelativePath, fixme_map: fixme_map::T) {
        if !fixme_map.is_empty() {
            FIXMES.with(|fixmes| {
                fixmes
                    .borrow_mut()
                    .decl_hh_fixmes
                    .insert(filename, fixme_map)
            });
        }
    }

    pub fn provide_disallowed_fixmes(filename: RelativePath, fixme_map: fixme_map::T) {
        if !fixme_map.is_empty() {
            FIXMES.with(|fixmes| {
                fixmes
                    .borrow_mut()
                    .disallowed_fixmes
                    .insert(filename, fixme_map)
            });
        }
    }

    pub fn provide_ignores(filename: RelativePath, fixme_map: fixme_map::T) {
        if !fixme_map.is_empty() {
            FIXMES.with(|fixmes| fixmes.borrow_mut().ignores.insert(filename, fixme_map));
        }
    }

    /// Install the comments of `file`, as found by the parser: what
    /// `Full_fidelity_ast.process_scour_comments` does with them (it also
    /// reports `sc_error_pos` and `sc_bad_ignore_pos` as parsing errors, which
    /// this does not do).
    ///
    /// `quick_mode` is the parser's (declarations only). As in OCaml, a table
    /// that is empty does not replace what a previous parse of `file`
    /// provided on this thread; use [`remove_batch`] for that.
    pub fn provide_scoured_comments(file: &RelativePath, sc: &ScouredComments, quick_mode: bool) {
        provide_disallowed_fixmes(file.clone(), sc.misuses.clone());
        provide_ignores(file.clone(), sc.ignores.clone());
        if quick_mode {
            provide_decl_hh_fixmes(file.clone(), sc.fixmes.clone())
        } else {
            provide_hh_fixmes(file.clone(), sc.fixmes.clone())
        }
    }

    thread_local! {
        /// The tables as they were at each `local_changes_push_sharedmem_stack`
        /// that is not popped yet (P0).
        static LOCAL_CHANGES: RefCell<Vec<Fixmes>> = const { RefCell::new(Vec::new()) };
    }

    /// `local_changes_push_sharedmem_stack`: `HH_FIXMES`, `DECL_HH_FIXMES`,
    /// `DISALLOWED_FIXMES` and `IGNORES` `.LocalChanges.push_stack`. What
    /// is provided or removed until the matching pop is forgotten then: the
    /// tables of this thread are saved, and restored by the pop (added by P0
    /// for `Provider_utils.respect_but_quarantine_unsaved_changes`).
    pub fn local_changes_push_sharedmem_stack() {
        let saved = FIXMES.with(|fixmes| fixmes.borrow().clone());
        LOCAL_CHANGES.with_borrow_mut(|stack| stack.push(saved))
    }

    /// `local_changes_pop_sharedmem_stack`
    pub fn local_changes_pop_sharedmem_stack() {
        match LOCAL_CHANGES.with_borrow_mut(|stack| stack.pop()) {
            // `Shared_mem.LocalChanges.pop_stack`
            None => panic!("There are no active local change stacks. Nothing to pop!"),
            Some(saved) => FIXMES.with(|fixmes| *fixmes.borrow_mut() = saved),
        }
    }

    /// Not in the OCaml: the tables of this thread stand for those in shared
    /// memory, from which `Fixme_provider.remove_batch` removes the changed
    /// files for every worker; here every file is removed from them, on this
    /// thread, when the files may have changed (see `crate::rt::decl_epoch`).
    pub fn forget_thread_tables() {
        FIXMES.with(|fixmes| *fixmes.borrow_mut() = Fixmes::default());
        // (The tables saved by a push are emptied too: the pop then gives
        // empty tables, at the same depth.)
        LOCAL_CHANGES.with_borrow_mut(|stack| {
            stack.iter_mut().for_each(|saved| *saved = Fixmes::default())
        })
    }

    pub fn remove_batch(paths: &BTreeSet<RelativePath>) {
        FIXMES.with(|fixmes| {
            let mut fixmes = fixmes.borrow_mut();
            for path in paths {
                fixmes.hh_fixmes.remove(path);
                fixmes.decl_hh_fixmes.remove(path);
                fixmes.disallowed_fixmes.remove(path);
                fixmes.ignores.remove(path);
            }
        })
    }

    // We register the function that can look up a position and determine if a
    // given position is affected by an HH_FIXME. We use a reference to avoid a
    // cyclic dependency: everything depends on the Errors module (the module
    // defining all the errors), because of that making the Errors module call
    // into anything that isn't in the standard library is very unwise,
    // because that code won't be able to add errors.

    fn get_entries(get_map: GetMap, pos: &Pos) -> IMap<Pos> {
        let filename = pos.filename();
        let (line, _, _) = pos.info_pos();
        FIXMES.with(|fixmes| {
            get_map(&fixmes.borrow(), filename)
                .and_then(|map| map.get(&(line as isize)))
                .cloned()
                .unwrap_or_default()
        })
    }

    fn get_fixmes_for_pos(pos: &Pos) -> IMap<Pos> {
        get_entries(get_fixmes, pos)
    }

    pub fn get_fixme_codes_for_pos(pos: &Pos) -> ISet {
        get_fixmes_for_pos(pos).into_keys().collect()
    }

    fn get_entry(get_map: GetMap, pos: &Pos, code: ErrorCode) -> Option<Pos> {
        get_entries(get_map, pos).remove(&code)
    }

    /// What `Diagnostics.get_disallowed_fixme_pos` is set to.
    pub fn get_disallowed_fixme_pos(pos: &Pos, code: ErrorCode) -> Option<Pos> {
        get_entry(get_disallowed_fixmes, pos, code)
    }

    /// What `Diagnostics.get_ignore_pos` is set to.
    pub fn get_ignore_pos(pos: &Pos, code: ErrorCode) -> Option<Pos> {
        get_entry(get_ignores, pos, code)
    }

    const inf_err_codes: [ErrorCode; 3] = [4110, 4323, 4324];

    fn is_inf_err_code(err_code: ErrorCode) -> bool {
        inf_err_codes.contains(&err_code)
    }

    fn any_inf_err_code(imap: &IMap<Pos>) -> Option<Pos> {
        inf_err_codes
            .iter()
            .find_map(|code| imap.get(code))
            .cloned()
    }

    /// What `Diagnostics.get_hh_fixme_pos` is set to.
    pub fn get_hh_fixme_pos(err_pos: &Pos, err_code: ErrorCode) -> Option<Pos> {
        let imap = get_fixmes_for_pos(err_pos);
        if super::code_agnostic_fixme() {
            if imap.is_empty() {
                None
            } else {
                Some(err_pos.clone())
            }
        } else {
            match imap.get(&err_code) {
                None if is_inf_err_code(err_code) => any_inf_err_code(&imap),
                x => x.cloned(),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;
    use std::sync::Mutex;
    use std::sync::MutexGuard;

    use oxidized::scoured_comments::ScouredComments;
    use relative_path::Prefix;

    use super::*;

    /// `allowed_fixme_codes_strict` and `code_agnostic_fixme` are process
    /// wide: the tests that set them, or whose outcome depends on them, hold
    /// this lock.
    static CONFIG: Mutex<()> = Mutex::new(());

    fn config(allowed: &[isize]) -> MutexGuard<'static, ()> {
        let guard = CONFIG.lock().unwrap_or_else(|e| e.into_inner());
        set_allowed_fixme_codes_strict(allowed.iter().copied().collect());
        set_code_agnostic_fixme(false);
        guard
    }

    fn path(name: &str) -> RelativePath {
        RelativePath::make(Prefix::Root, name.into())
    }

    fn pos_in(file: &RelativePath, line: usize, cols: std::ops::Range<usize>) -> Pos {
        let bol = line * 100;
        Pos::from_lnum_bol_offset(
            Arc::new(file.clone()),
            (line, bol, bol + cols.start),
            (line, bol, bol + cols.end),
        )
    }

    /// A position in `a.php`.
    fn pos(line: usize, cols: std::ops::Range<usize>) -> Pos {
        pos_in(&path("a.php"), line, cols)
    }

    fn msg(pos: Pos, text: &str) -> Message<Pos> {
        Message(pos, BString::from(text))
    }

    fn err(code: isize, pos: Pos, text: &str) -> Diagnostic {
        make_err(code, msg(pos, text), vec![], Explanation::Empty)
    }

    fn warning(code: isize, pos: Pos, text: &str, is_trusted: bool) -> Diagnostic {
        Diagnostic {
            severity: Severity::Warning { is_trusted },
            ..err(code, pos, text)
        }
    }

    fn fixmed(diag: Diagnostic) -> Diagnostic {
        Diagnostic {
            is_fixmed: true,
            ..diag
        }
    }

    /// The claims of every diagnostic, in the order of the map.
    fn claims(errors: &T) -> Vec<String> {
        errors
            .values()
            .flatten()
            .map(|d| d.claim.1.to_string())
            .collect()
    }

    /// The diagnostics (fixmed ones included) that `f` adds while `a.php` is
    /// being checked.
    fn added(f: impl FnOnce()) -> Vec<Diagnostic> {
        let (errors, ()) = do_with_context(Some(false), path("a.php"), f);
        get_diagnostic_list(Some(false), errors)
    }

    fn install(file: &str, f: impl FnOnce(&mut ScouredComments)) {
        let mut sc = ScouredComments::new();
        f(&mut sc);
        fixme_provider::provide_scoured_comments(&path(file), &sc, false);
    }

    fn is_initial_state() -> bool {
        with(|s| {
            s.current_file.is_empty()
                && s.current_span.is_none()
                && !s.ignore_pos_outside_current_span
                && s.allow_errors_in_default_path
                && s.error_map.is_empty()
                && !s.accumulate_errors
                && !s.in_lazy_decl
        })
    }

    // ~~ do_ ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

    #[test]
    #[should_panic(expected = "assert false")]
    fn adding_an_error_outside_of_do_is_a_bug() {
        add_diagnostic(err(4110, pos(1, 0..1), "e"));
    }

    #[test]
    fn do_returns_the_errors_in_the_order_they_were_added() {
        let (errors, result) = do_(None, || {
            add_diagnostic(err(4110, pos(3, 0..1), "first"));
            add_diagnostic(err(4110, pos(1, 0..1), "second"));
            add_diagnostic(warning(12001, pos(2, 0..1), "third", true));
            42
        });
        assert_eq!(result, 42);
        // Outside of `run_in_context`, the errors are those of the default
        // path.
        assert_eq!(errors.keys().collect::<Vec<_>>(), [&RelativePath::EMPTY]);
        assert_eq!(claims(&errors), ["first", "second", "third"]);
        assert!(is_initial_state());
    }

    #[test]
    fn do_with_context_files_the_errors_under_the_path() {
        let (errors, ()) = do_with_context(None, path("a.php"), || {
            add_diagnostic(err(4110, pos(3, 0..1), "first"));
            // An error for another file is added when its file is the current
            // one.
            run_in_context(path("b.php"), || {
                add_diagnostic(err(4110, pos_in(&path("b.php"), 1, 0..1), "in b"))
            });
            add_diagnostic(err(4110, pos(4, 0..1), "second"));
        });
        assert_eq!(
            errors.keys().collect::<Vec<_>>(),
            [&path("a.php"), &path("b.php")]
        );
        assert_eq!(claims(&errors), ["first", "second", "in b"]);
        assert!(is_initial_state());
    }

    #[test]
    fn a_nested_do_keeps_its_errors_to_itself() {
        let (outer, inner) = do_(None, || {
            add_diagnostic(err(4110, pos(1, 0..1), "outer 1"));
            let (inner, ()) = do_(None, || add_diagnostic(err(4110, pos(2, 0..1), "inner")));
            add_diagnostic(err(4110, pos(3, 0..1), "outer 2"));
            inner
        });
        assert_eq!(claims(&outer), ["outer 1", "outer 2"]);
        assert_eq!(claims(&inner), ["inner"]);
    }

    #[test]
    fn an_error_equal_to_the_most_recent_one_is_not_added() {
        let e1 = err(4110, pos(1, 0..1), "e1");
        let e2 = err(4110, pos(2, 0..1), "e2");
        let (errors, ()) = do_(None, || {
            add_diagnostic(e1.clone());
            add_diagnostic(e1.clone());
            add_diagnostic(e2.clone());
            add_diagnostic(e1.clone());
            // The same warning, trusted or not, is the same diagnostic...
            add_diagnostic(warning(12001, pos(5, 0..1), "w", false));
            add_diagnostic(warning(12001, pos(5, 0..1), "w", true));
            // ... but an error is not a warning.
            add_diagnostic(err(12001, pos(5, 0..1), "w"));
        });
        assert_eq!(claims(&errors), ["e1", "e2", "e1", "w", "w"]);
        let list = get_diagnostic_list(None, errors);
        assert_eq!(list[3].severity, Severity::Warning { is_trusted: false });
        assert_eq!(list[4].severity, Severity::Err);
    }

    #[test]
    fn the_state_is_restored_when_the_callback_panics() {
        let result = std::panic::catch_unwind(|| {
            do_with_context(None, path("a.php"), || {
                run_with_span(pos(1, 0..50), || {
                    run_in_decl_mode(|| {
                        try_(
                            || {
                                add_diagnostic(err(4110, pos(1, 0..1), "e"));
                                panic!("boom")
                            },
                            |_| (),
                        )
                    })
                })
            })
        });
        assert!(result.is_err());
        assert!(is_initial_state());
        // And the fixme hook that `try_` turns off is back.
        let _config = config(&[4110]);
        install("a.php", |sc| sc.add_to_fixmes(3, 4110, pos(2, 0..9)));
        assert_eq!(
            added(|| add_diagnostic(err(4110, pos(3, 0..1), "e"))),
            [fixmed(err(4110, pos(3, 0..1), "e"))]
        );
    }

    // ~~ try_ ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

    #[test]
    fn try_without_error_returns_the_result() {
        let (errors, result) = do_(None, || try_(|| 1, |_| panic!("no error was added")));
        assert_eq!(result, 1);
        assert!(errors.is_empty());
        assert!(is_initial_state());
    }

    #[test]
    fn try_gives_the_first_error_to_the_handler() {
        let (errors, result) = do_(None, || {
            add_diagnostic(err(4110, pos(1, 0..1), "before"));
            let result = try_(
                || {
                    add_diagnostic(err(4110, pos(2, 0..1), "first"));
                    add_diagnostic(err(4110, pos(3, 0..1), "second"));
                    None
                },
                Some,
            );
            add_diagnostic(err(4110, pos(4, 0..1), "after"));
            result
        });
        assert_eq!(result, Some(err(4110, pos(2, 0..1), "first")));
        // What was added in the `try_` is not reported.
        assert_eq!(claims(&errors), ["before", "after"]);
    }

    #[test]
    fn try_with_several_files_gives_the_first_error_of_the_last_file() {
        let (_, result) = do_(None, || {
            try_(
                || {
                    run_in_context(path("b.php"), || {
                        add_diagnostic(err(4110, pos_in(&path("b.php"), 1, 0..1), "b 1"));
                        add_diagnostic(err(4110, pos_in(&path("b.php"), 2, 0..1), "b 2"));
                    });
                    run_in_context(path("a.php"), || {
                        add_diagnostic(err(4110, pos(1, 0..1), "a 1"))
                    });
                    "no error".to_string()
                },
                |e| e.claim.1.to_string(),
            )
        });
        assert_eq!(result, "b 1");
    }

    #[test]
    fn try_with_result_gives_the_result_to_the_handler() {
        let (errors, result) = do_(None, || {
            try_with_result(
                || {
                    add_diagnostic(err(4110, pos(2, 0..1), "e"));
                    vec![1, 2]
                },
                |mut result, e| {
                    result.push(e.code);
                    result
                },
            )
        });
        assert_eq!(result, [1, 2, 4110]);
        assert!(errors.is_empty());
    }

    #[test]
    fn an_error_added_by_the_handler_is_reported() {
        let (errors, ()) = do_(None, || {
            try_(
                || add_diagnostic(err(4110, pos(2, 0..1), "specific")),
                |_| add_diagnostic(err(4110, pos(2, 0..1), "general")),
            )
        });
        assert_eq!(claims(&errors), ["general"]);
    }

    #[test]
    fn nested_try() {
        let (errors, result) = do_(None, || {
            try_(
                || {
                    // The error of the inner `try_` is handled there...
                    let inner = try_(
                        || {
                            add_diagnostic(err(4110, pos(2, 0..1), "inner"));
                            "no error"
                        },
                        |_| "inner error",
                    );
                    assert_eq!(inner, "inner error");
                    assert!(!currently_has_errors());
                    // ... unless its handler reports one.
                    try_(
                        || add_diagnostic(err(4110, pos(3, 0..1), "inner 2")),
                        |_| add_diagnostic(err(4110, pos(3, 0..1), "from the handler")),
                    );
                    assert!(currently_has_errors());
                    "no error".to_string()
                },
                |e| e.claim.1.to_string(),
            )
        });
        assert_eq!(result, "from the handler");
        assert!(errors.is_empty());
    }

    #[test]
    fn a_warning_does_not_trigger_the_handler_and_is_kept() {
        let (errors, result) = do_with_context(None, path("a.php"), || {
            try_(
                || {
                    add_diagnostic(warning(12001, pos(2, 0..1), "w", false));
                    "no error"
                },
                |_| "error",
            )
        });
        assert_eq!(result, "no error");
        assert_eq!(
            get_diagnostic_list(None, errors),
            [warning(12001, pos(2, 0..1), "w", false)]
        );
    }

    /// Only the first diagnostic of a `try_` is looked at. (The OCaml says
    /// that a `try_` around something that warns is a bug.)
    #[test]
    fn only_the_first_diagnostic_of_a_try_counts() {
        // A warning, then an error: the error is lost.
        let (errors, result) = do_(None, || {
            try_(
                || {
                    add_diagnostic(warning(12001, pos(2, 0..1), "w", true));
                    add_diagnostic(err(4110, pos(3, 0..1), "e"));
                    "no error"
                },
                |_| "error",
            )
        });
        assert_eq!(result, "no error");
        assert_eq!(claims(&errors), ["w"]);

        // An error, then a warning: the warning is lost.
        let (errors, result) = do_(None, || {
            try_(
                || {
                    add_diagnostic(err(4110, pos(3, 0..1), "e"));
                    add_diagnostic(warning(12001, pos(2, 0..1), "w", true));
                    "no error"
                },
                |_| "error",
            )
        });
        assert_eq!(result, "error");
        assert!(errors.is_empty());
    }

    #[test]
    fn try_when_calls_the_handler_only_if_the_condition_holds() {
        let handled = std::cell::RefCell::new(vec![]);
        let (errors, result) = do_(None, || {
            let x = try_when(
                || {
                    add_diagnostic(err(4110, pos(2, 0..1), "handled"));
                    1
                },
                || true,
                |e| handled.borrow_mut().push(e),
            );
            let y = try_when(
                || {
                    add_diagnostic(err(4110, pos(3, 0..1), "not handled"));
                    2
                },
                || false,
                |e| handled.borrow_mut().push(e),
            );
            let z = try_when(|| 3, || panic!("no error"), |_| panic!("no error"));
            (x, y, z)
        });
        assert_eq!(result, (1, 2, 3));
        assert_eq!(*handled.borrow(), [err(4110, pos(2, 0..1), "handled")]);
        assert_eq!(claims(&errors), ["not handled"]);
    }

    #[test]
    fn try_no_errors_ignores_warnings() {
        let (errors, result) = do_(None, || {
            (
                try_no_errors(|| 1),
                try_no_errors(|| add_diagnostic(err(4110, pos(2, 0..1), "e"))),
                try_no_errors(|| add_diagnostic(warning(12001, pos(3, 0..1), "w", true))),
            )
        });
        assert_eq!(result, (true, false, true));
        assert_eq!(claims(&errors), ["w"]);
    }

    // ~~ ignore_, run_and_check_for_errors ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

    #[test]
    fn ignore_drops_the_errors() {
        let (errors, result) = do_(None, || {
            add_diagnostic(err(4110, pos(1, 0..1), "kept"));
            ignore_(|| {
                add_diagnostic(err(4110, pos(2, 0..1), "ignored"));
                add_diagnostic(warning(12001, pos(2, 0..1), "ignored", true));
                5
            })
        });
        assert_eq!(result, 5);
        assert_eq!(claims(&errors), ["kept"]);
        assert!(is_initial_state());
        // It needs no `do_` around it.
        assert_eq!(
            ignore_(|| {
                add_diagnostic(err(4110, pos(2, 0..1), "ignored"));
                6
            }),
            6
        );
        assert!(is_initial_state());
    }

    #[test]
    fn positions_are_not_checked_inside_ignore() {
        let in_b = err(4110, pos_in(&path("b.php"), 1, 0..1), "in b");
        let (wrapped, not_wrapped) = run_in_context(path("a.php"), || {
            let (wrapped, ()) = do_(None, || add_diagnostic(in_b.clone()));
            let not_wrapped = ignore_(|| do_(None, || add_diagnostic(in_b.clone())).0);
            (wrapped, not_wrapped)
        });
        assert_ne!(get_diagnostic_list(None, wrapped), [in_b.clone()]);
        assert_eq!(get_diagnostic_list(None, not_wrapped), [in_b]);
    }

    #[test]
    fn run_and_check_for_errors_counts_the_errors_of_the_current_file() {
        let (errors, result) = do_with_context(None, path("a.php"), || {
            let (x, nothing) = run_and_check_for_errors(|| 1);
            let (_, a_warning) = run_and_check_for_errors(|| {
                add_diagnostic(warning(12001, pos(1, 0..1), "w", true))
            });
            assert!(!currently_has_errors());
            let (_, an_error) =
                run_and_check_for_errors(|| add_diagnostic(err(4110, pos(2, 0..1), "e")));
            assert!(currently_has_errors());
            let (_, a_duplicate) =
                run_and_check_for_errors(|| add_diagnostic(err(4110, pos(2, 0..1), "e")));
            let (_, ignored) = run_and_check_for_errors(|| {
                ignore_(|| add_diagnostic(err(4110, pos(3, 0..1), "e")))
            });
            (x, nothing, a_warning, an_error, a_duplicate, ignored)
        });
        assert_eq!(result, (1, false, false, true, false, false));
        assert_eq!(claims(&errors), ["w", "e"]);
    }

    // ~~ the primary position ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

    #[test]
    fn an_error_in_another_file_is_reported_in_the_current_one() {
        let in_b = pos_in(&path("b.php"), 7, 0..1);
        let reason = msg(pos_in(&path("c.php"), 1, 0..1), "reason");
        let diags = added(|| {
            add_diagnostic(make_err(
                4110,
                msg(in_b.clone(), "in b"),
                vec![reason.clone()],
                Explanation::Empty,
            ))
        });
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, 4110);
        assert_eq!(diags[0].claim.0, pos_make_from(path("a.php")));
        assert!(!diags[0].claim.0.is_none());
        assert_eq!(
            diags[0].claim.1.to_string(),
            "Incomplete position information! Your type error is in this file, but we could only find related positions in another file. If remediation attempts don't work, please file a bug report."
        );
        assert_eq!(diags[0].reasons, [msg(in_b, "in b"), reason]);
    }

    #[test]
    fn an_error_outside_of_the_current_span_is_reported_on_the_span() {
        let span = pos(10, 0..50);
        let diags = added(|| {
            run_with_span(span.clone(), || {
                assert_eq!(get_current_span(), span);
                add_diagnostic(err(4110, pos(10, 3..7), "inside"));
                add_diagnostic(err(4110, pos(20, 3..7), "outside"));
                add_diagnostic(err(4110, pos_in(&path("b.php"), 10, 3..7), "in b"));
            });
            assert!(get_current_span().is_none());
        });
        let badpos_2 = "Incomplete position information! We couldn't find the exact line of your type error in this definition. If remediation attempts don't work, please file a bug report.";
        assert_eq!(
            diags,
            [
                err(4110, pos(10, 3..7), "inside"),
                make_err(
                    4110,
                    msg(span.clone(), badpos_2),
                    vec![msg(pos(20, 3..7), "outside")],
                    Explanation::Empty
                ),
                make_err(
                    4110,
                    msg(span, badpos_2),
                    vec![msg(pos_in(&path("b.php"), 10, 3..7), "in b")],
                    Explanation::Empty
                ),
            ]
        );
    }

    #[test]
    fn positions_are_not_checked_in_the_default_path() {
        let in_b = err(4110, pos_in(&path("b.php"), 1, 0..1), "in b");
        let (errors, ()) = do_(None, || add_diagnostic(in_b.clone()));
        assert_eq!(get_diagnostic_list(None, errors), [in_b]);
    }

    #[test]
    fn try_removes_the_bad_position_sentinel() {
        let in_b = pos_in(&path("b.php"), 7, 0..1);
        let reason = msg(pos_in(&path("c.php"), 1, 0..1), "reason");
        let (_, handled) = do_with_context(None, path("a.php"), || {
            try_(
                || {
                    add_diagnostic(make_err(
                        4110,
                        msg(in_b.clone(), "in b"),
                        vec![reason.clone()],
                        Explanation::Empty,
                    ));
                    None
                },
                Some,
            )
        });
        // The claim is the original message, at the position of the sentinel.
        assert_eq!(
            handled,
            Some(make_err(
                4110,
                msg(pos_make_from(path("a.php")), "in b"),
                vec![reason],
                Explanation::Empty
            ))
        );
    }

    // ~~ fixmes ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

    fn cannot_fixme(code: isize) -> String {
        format!(
            "You cannot use `HH_FIXME` or `HH_IGNORE_ERROR` comments to suppress error {}",
            code
        )
    }

    #[test]
    fn hh_fixme_of_an_allowed_code() {
        let _config = config(&[4110]);
        install("a.php", |sc| sc.add_to_fixmes(3, 4110, pos(2, 0..9)));
        let error = err(4110, pos(3, 4..5), "e");
        // The error is kept, marked.
        assert_eq!(
            added(|| add_diagnostic(error.clone())),
            [fixmed(error.clone())]
        );
        assert!(is_suppressed(&error));
        // `do_` drops it unless asked not to.
        let (errors, ()) = do_with_context(None, path("a.php"), || add_diagnostic(error.clone()));
        assert!(errors.is_empty());
        // Another code, another line.
        let other_code = err(4111, pos(3, 4..5), "e");
        let other_line = err(4110, pos(4, 4..5), "e");
        assert!(!is_suppressed(&other_code));
        assert!(!is_suppressed(&other_line));
        assert_eq!(
            added(|| {
                add_diagnostic(other_code.clone());
                add_diagnostic(other_line.clone());
            }),
            [other_code, other_line]
        );
        // A suppressed error is not an error for the checks on the state.
        let (_, (changed, has_errors)) = do_with_context(None, path("a.php"), || {
            let ((), changed) = run_and_check_for_errors(|| add_diagnostic(error.clone()));
            (changed, currently_has_errors())
        });
        // (It is counted: `is_fixmed` is not looked at.)
        assert!(changed);
        assert!(has_errors);
    }

    #[test]
    fn a_suppressed_error_outside_of_do_is_dropped() {
        let _config = config(&[4110]);
        install("a.php", |sc| sc.add_to_fixmes(3, 4110, pos(2, 0..9)));
        add_diagnostic(err(4110, pos(3, 4..5), "e"));
        assert!(is_initial_state());
    }

    #[test]
    fn hh_fixme_of_a_code_that_is_not_allowed() {
        let _config = config(&[4111]);
        install("a.php", |sc| sc.add_to_fixmes(3, 4110, pos(2, 0..9)));
        let error = err(4110, pos(3, 4..5), "e");
        assert!(!is_suppressed(&error));
        assert_eq!(
            added(|| add_diagnostic(error.clone())),
            [error, err(4110, pos(2, 0..9), &cannot_fixme(4110))]
        );
    }

    #[test]
    fn the_error_about_the_fixme_keeps_the_rest_of_the_error() {
        let _config = config(&[]);
        install("a.php", |sc| sc.add_to_fixmes(3, 4110, pos(2, 0..9)));
        let error = Diagnostic {
            reasons: vec![msg(pos(1, 0..1), "reason")],
            custom_msgs: vec!["custom".to_string()],
            function_pos: Some(pos(1, 0..90)),
            ..err(4110, pos(3, 4..5), "e")
        };
        assert_eq!(
            added(|| add_diagnostic(error.clone())),
            [
                error,
                Diagnostic {
                    custom_msgs: vec!["custom".to_string()],
                    function_pos: Some(pos(1, 0..90)),
                    ..err(4110, pos(2, 0..9), &cannot_fixme(4110))
                }
            ]
        );
    }

    #[test]
    fn hh_fixme_of_a_banned_code() {
        // 4195 is `InvalidIsAsExpressionHint`.
        let _config = config(&[4195]);
        install("a.php", |sc| sc.add_to_fixmes(3, 4195, pos(2, 0..9)));
        let error = err(4195, pos(3, 4..5), "e");
        assert_eq!(
            added(|| add_diagnostic(error.clone())),
            [
                error,
                err(
                    4195,
                    pos(2, 0..9),
                    "You cannot use `HH_FIXME` or `HH_IGNORE_ERROR` comments to suppress error 4195, and this cannot be enabled by configuration"
                )
            ]
        );
    }

    #[test]
    fn hh_fixme_in_an_hhi_file() {
        let _config = config(&[]);
        let hhi = RelativePath::make(Prefix::Hhi, "builtins.hhi".into());
        let mut sc = ScouredComments::new();
        sc.add_to_fixmes(3, 4110, pos_in(&hhi, 2, 0..9));
        sc.add_to_fixmes(3, 4195, pos_in(&hhi, 2, 0..9));
        fixme_provider::provide_scoured_comments(&hhi, &sc, false);
        let error = err(4110, pos_in(&hhi, 3, 4..5), "e");
        let banned = err(4195, pos_in(&hhi, 3, 4..5), "e");
        let (errors, ()) = do_with_context(Some(false), hhi.clone(), || {
            add_diagnostic(error.clone());
            add_diagnostic(banned.clone());
        });
        let diags = get_diagnostic_list(Some(false), errors);
        // Any code can be suppressed, but the banned ones.
        assert_eq!(diags.len(), 3);
        assert_eq!(diags[0], fixmed(error));
        assert_eq!(diags[1], banned);
        assert_eq!(diags[2].claim.0, pos_in(&hhi, 2, 0..9));
    }

    #[test]
    fn hh_fixme_in_a_declaration() {
        // The parser files the fixmes that are in declarations as misuses.
        let _config = config(&[4110]);
        install("a.php", |sc| sc.add_to_misuses(3, 4110, pos(2, 0..9)));
        let error = err(4110, pos(3, 4..5), "e");
        assert!(!is_suppressed(&error));
        assert_eq!(
            added(|| add_diagnostic(error.clone())),
            [
                error,
                err(
                    4110,
                    pos(2, 0..9),
                    "You cannot use `HH_FIXME` or `HH_IGNORE_ERROR` comments to suppress error 4110 in declarations"
                )
            ]
        );
    }

    #[test]
    fn hh_fixme_of_a_warning() {
        let _config = config(&[12001]);
        install("a.php", |sc| sc.add_to_fixmes(3, 12001, pos(2, 0..9)));
        let w = warning(12001, pos(3, 4..5), "w", false);
        assert_eq!(
            added(|| add_diagnostic(w.clone())),
            [
                w,
                // With the severity of the warning.
                warning(
                    12001,
                    pos(2, 0..9),
                    "You cannot use `HH_FIXME` comments to suppress warnings. Use `HH_IGNORE[12001]` instead.",
                    false
                )
            ]
        );
    }

    #[test]
    fn hh_ignore_of_a_warning() {
        let _config = config(&[]);
        install("a.php", |sc| sc.add_to_ignores(3, 12001, pos(2, 0..9)));
        let w = warning(12001, pos(3, 4..5), "w", false);
        assert!(is_suppressed(&w));
        assert_eq!(added(|| add_diagnostic(w.clone())), [fixmed(w)]);
    }

    #[test]
    fn hh_ignore_of_an_error_code() {
        let _config = config(&[4110]);
        install("a.php", |sc| sc.add_to_ignores(3, 4110, pos(2, 0..9)));
        let e = err(4110, pos(3, 4..5), "e");
        // A warning that is being migrated to an error has the code of an
        // error.
        let w = warning(4110, pos(3, 4..5), "w", true);
        assert!(!is_suppressed(&e));
        assert!(!is_suppressed(&w));
        assert_eq!(
            added(|| {
                add_diagnostic(e.clone());
                add_diagnostic(w.clone());
            }),
            [
                e,
                err(
                    4110,
                    pos(2, 0..9),
                    "You cannot use `HH_IGNORE` to suppress non-warning code 4110. Hack errors should not be suppressed. You should try your best to fix the code causing the error, or incidents will happen."
                ),
                w,
                warning(
                    4110,
                    pos(2, 0..9),
                    "This warning code 4110 will soon be migrated to be an error. Try your best to fix it, or if not possible, suppress it with `HH_FIXME` instead of `HH_IGNORE` and report your case to us.",
                    true
                ),
            ]
        );
    }

    #[test]
    fn a_fixme_is_looked_for_before_an_ignore_and_before_a_misuse() {
        let _config = config(&[4110]);
        install("a.php", |sc| {
            sc.add_to_fixmes(3, 4110, pos(2, 0..9));
            sc.add_to_ignores(3, 4110, pos(2, 10..19));
            sc.add_to_misuses(3, 4110, pos(2, 20..29));
            sc.add_to_ignores(5, 4110, pos(4, 10..19));
            sc.add_to_misuses(5, 4110, pos(4, 20..29));
        });
        assert!(is_suppressed(&err(4110, pos(3, 4..5), "e")));
        let diags = added(|| add_diagnostic(err(4110, pos(5, 4..5), "e")));
        assert_eq!(diags.len(), 2);
        assert_eq!(diags[1].claim.0, pos(4, 10..19));
    }

    #[test]
    fn hh_fixme_is_not_looked_at_inside_try() {
        let _config = config(&[4110]);
        install("a.php", |sc| {
            sc.add_to_fixmes(3, 4110, pos(2, 0..9));
            sc.add_to_ignores(5, 12001, pos(4, 0..9));
        });
        let error = err(4110, pos(3, 4..5), "e");
        let (errors, handled) = do_with_context(Some(false), path("a.php"), || {
            let handled = try_(
                || {
                    add_diagnostic(error.clone());
                    // Neither in a `do_` inside the `try_`.
                    let (inner, ()) = do_(Some(false), || add_diagnostic(error.clone()));
                    assert_eq!(get_diagnostic_list(Some(false), inner), [error.clone()]);
                    None
                },
                Some,
            );
            // After the `try_`, it is again.
            add_diagnostic(error.clone());
            handled
        });
        assert_eq!(handled, Some(error.clone()));
        assert_eq!(get_diagnostic_list(Some(false), errors), [fixmed(error)]);

        // HH_IGNORE is looked at, but the warning that leaves the `try_` is
        // built anew and is no longer marked.
        let w = warning(12001, pos(5, 4..5), "w", true);
        assert_eq!(
            added(|| try_(|| add_diagnostic(w.clone()), |_| ())),
            [w.clone()]
        );
        assert_eq!(added(|| add_diagnostic(w.clone())), [fixmed(w)]);
    }

    #[test]
    fn a_fixme_for_a_subtyping_error_covers_the_other_subtyping_codes() {
        let _config = config(&[4110, 4323]);
        install("a.php", |sc| {
            sc.add_to_fixmes(3, 4110, pos(2, 0..9));
            sc.add_to_fixmes(5, 4324, pos(4, 0..9));
            sc.add_to_fixmes(7, 4111, pos(6, 0..9));
        });
        // 4323 is suppressed by the fixme for 4110, if 4323 is allowed.
        assert!(is_suppressed(&err(4323, pos(3, 4..5), "e")));
        assert_eq!(
            added(|| add_diagnostic(err(4324, pos(3, 4..5), "e"))),
            [
                err(4324, pos(3, 4..5), "e"),
                err(4324, pos(2, 0..9), &cannot_fixme(4324))
            ]
        );
        assert!(is_suppressed(&err(4110, pos(5, 4..5), "e")));
        // But not by a fixme for another code, nor are other codes
        // suppressed by a fixme for a subtyping error.
        assert_eq!(
            added(|| add_diagnostic(err(4110, pos(7, 4..5), "e"))),
            [err(4110, pos(7, 4..5), "e")]
        );
        assert_eq!(
            added(|| add_diagnostic(err(4111, pos(3, 4..5), "e"))),
            [err(4111, pos(3, 4..5), "e")]
        );
    }

    #[test]
    fn with_code_agnostic_fixme_a_fixme_is_for_every_code() {
        let _config = config(&[4005]);
        install("a.php", |sc| sc.add_to_fixmes(3, 4110, pos(2, 0..9)));
        let error = err(4005, pos(3, 4..5), "e");
        assert!(!is_suppressed(&error));
        set_code_agnostic_fixme(true);
        assert!(code_agnostic_fixme());
        assert!(is_suppressed(&error));
        // The code still has to be allowed; the error about the fixme is then
        // at the position of the error.
        assert_eq!(
            added(|| add_diagnostic(err(4006, pos(3, 4..5), "e"))),
            [
                err(4006, pos(3, 4..5), "e"),
                err(4006, pos(3, 4..5), &cannot_fixme(4006))
            ]
        );
        assert!(!is_suppressed(&err(4005, pos(4, 4..5), "e")));
        set_code_agnostic_fixme(false);
    }

    #[test]
    fn the_fixme_tables() {
        let _config = config(&[4110]);
        let a = path("a.php");
        let error = err(4110, pos(3, 4..5), "e");
        assert!(!is_suppressed(&error));
        assert_eq!(fixme_provider::get_hh_fixmes(&a), None);

        // The fixmes found when parsing declarations only are used when the
        // file was not parsed in full.
        let mut sc = ScouredComments::new();
        sc.add_to_fixmes(3, 4110, pos(2, 0..9));
        sc.add_to_fixmes(3, 4111, pos(2, 10..19));
        fixme_provider::provide_scoured_comments(&a, &sc, true);
        assert_eq!(fixme_provider::get_hh_fixmes(&a), None);
        assert_eq!(
            fixme_provider::get_decl_hh_fixmes(&a),
            Some(sc.fixmes.clone())
        );
        assert!(is_suppressed(&error));
        assert_eq!(
            fixme_provider::get_fixme_codes_for_pos(&pos(3, 4..5)),
            ISet::from([4110, 4111])
        );
        assert!(fixme_provider::get_fixme_codes_for_pos(&pos(4, 4..5)).is_empty());

        let mut full = ScouredComments::new();
        full.add_to_fixmes(4, 4110, pos(2, 0..9));
        fixme_provider::provide_scoured_comments(&a, &full, false);
        assert_eq!(fixme_provider::get_hh_fixmes(&a), Some(full.fixmes.clone()));
        assert!(!is_suppressed(&error));
        assert!(is_suppressed(&err(4110, pos(4, 4..5), "e")));

        // Empty tables are not stored.
        fixme_provider::provide_scoured_comments(&a, &ScouredComments::new(), false);
        assert!(is_suppressed(&err(4110, pos(4, 4..5), "e")));

        fixme_provider::remove_batch(&BTreeSet::from([a.clone()]));
        assert_eq!(fixme_provider::get_hh_fixmes(&a), None);
        assert_eq!(fixme_provider::get_decl_hh_fixmes(&a), None);
        assert!(!is_suppressed(&err(4110, pos(4, 4..5), "e")));
    }

    #[test]
    fn the_fixme_hooks_can_be_replaced() {
        let _config = config(&[4110]);
        let error = err(4110, pos(3, 4..5), "e");
        assert!(!is_suppressed(&error));
        set_get_hh_fixme_pos(Rc::new(|pos, code| {
            if code == 4110 {
                Some(pos.clone())
            } else {
                None
            }
        }));
        assert_eq!(get_hh_fixme_pos(&pos(3, 4..5), 4110), Some(pos(3, 4..5)));
        assert_eq!(get_hh_fixme_pos(&pos(3, 4..5), 4111), None);
        assert!(is_suppressed(&error));
        set_get_hh_fixme_pos(Rc::new(fixme_provider::get_hh_fixme_pos));
        assert!(!is_suppressed(&error));
        assert_eq!(get_ignore_pos(&pos(3, 4..5), 4110), None);
        assert_eq!(get_disallowed_fixme_pos(&pos(3, 4..5), 4110), None);
    }

    // ~~ collections of errors ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

    #[test]
    fn sort_orders_and_removes_duplicates() {
        let a = path("a.php");
        let b = path("b.php");
        let sorted = sort(vec![
            err(4110, pos_in(&b, 1, 0..1), "b typing"),
            err(4110, pos_in(&a, 9, 0..1), "a typing 9"),
            err(4110, pos_in(&a, 2, 0..1), "a typing 2"),
            err(2049, pos_in(&a, 9, 0..1), "a naming"),
            // Same position: by message, then by reasons.
            err(4110, pos_in(&a, 2, 0..1), "a typing 2 bis"),
            make_err(
                4110,
                msg(pos_in(&a, 2, 0..1), "a typing 2"),
                vec![msg(pos_in(&a, 1, 0..1), "reason")],
                Explanation::Empty,
            ),
            // The same error with another code of the same phase is dropped
            // (the lowest code is kept), with a code of another phase it is
            // not.
            err(4111, pos_in(&a, 9, 0..1), "a typing 9"),
            err(4003, pos_in(&a, 9, 0..1), "a typing 9"),
            err(3001, pos_in(&a, 9, 0..1), "a typing 9"),
            // Warnings come first, whether they are trusted or not.
            warning(12001, pos_in(&b, 5, 0..1), "b warning", true),
            warning(12001, pos_in(&a, 5, 0..1), "a warning 5", true),
            warning(12001, pos_in(&a, 3, 0..1), "a warning 3", false),
            warning(12001, pos_in(&a, 7, 0..1), "a warning 7", false),
            warning(12001, pos_in(&a, 7, 0..1), "a warning 7", true),
        ]);
        assert_eq!(
            sorted
                .iter()
                .map(|d| (d.code, d.claim.1.to_string(), d.reasons.len()))
                .collect::<Vec<_>>(),
            [
                (12001, "a warning 3".to_string(), 0),
                (12001, "a warning 5".to_string(), 0),
                (12001, "a warning 7".to_string(), 0),
                (12001, "b warning".to_string(), 0),
                (2049, "a naming".to_string(), 0),
                (3001, "a typing 9".to_string(), 0),
                (4110, "a typing 2".to_string(), 0),
                (4110, "a typing 2".to_string(), 1),
                (4110, "a typing 2 bis".to_string(), 0),
                (4003, "a typing 9".to_string(), 0),
                (4110, "b typing".to_string(), 0),
            ]
        );
        // Of two warnings that only differ by `is_trusted`, the first is
        // kept.
        assert_eq!(sorted[2].severity, Severity::Warning { is_trusted: false });
    }

    #[test]
    fn sorted_list_of_a_collection() {
        let _config = config(&[4110]);
        install("a.php", |sc| sc.add_to_fixmes(3, 4110, pos(2, 0..9)));
        let (errors, ()) = do_with_context(Some(false), path("a.php"), || {
            add_diagnostic(err(4110, pos(5, 0..1), "5"));
            add_diagnostic(err(4110, pos(3, 0..1), "3"));
            add_diagnostic(err(4110, pos(1, 0..1), "1"));
            add_diagnostic(err(4110, pos(5, 0..1), "5"));
        });
        let texts = |list: Vec<Diagnostic>| -> Vec<String> {
            list.iter().map(|d| d.claim.1.to_string()).collect()
        };
        assert_eq!(
            texts(get_diagnostic_list(None, errors.clone())),
            ["5", "1", "5"]
        );
        assert_eq!(
            texts(get_diagnostic_list(Some(false), errors.clone())),
            ["5", "3", "1", "5"]
        );
        assert_eq!(
            texts(get_sorted_diagnostic_list(None, errors.clone())),
            ["1", "5"]
        );
        assert_eq!(
            texts(get_sorted_diagnostic_list(Some(false), errors.clone())),
            ["1", "3", "5"]
        );
        let mut seen = vec![];
        iter_diagnostic_list(None, |d| seen.push(d.claim.1.to_string()), &errors);
        assert_eq!(seen, ["1", "5"]);

        assert_eq!(count(None, &errors), 3);
        assert_eq!(count(Some(false), &errors), 4);
        assert!(has_errors(None, &errors));
        assert!(!has_no_errors(None, &errors));
        assert!(!has_no_errors_or_warnings(None, &errors));
        assert_eq!(get_file_diagnostics(None, &errors, &path("a.php")).len(), 3);
        assert_eq!(
            get_file_diagnostics(Some(false), &errors, &path("a.php")).len(),
            4
        );
        assert!(get_file_diagnostics(None, &errors, &path("b.php")).is_empty());
        assert_eq!(choose_code_opt(&errors), Some(4110));
        assert_eq!(get_failed_files(&errors), BTreeSet::from([path("a.php")]));

        // A file whose errors are all suppressed.
        let (only_fixmed, ()) = do_with_context(Some(false), path("a.php"), || {
            add_diagnostic(err(4110, pos(3, 0..1), "3"));
            add_diagnostic(warning(12001, pos(4, 0..1), "w", true));
        });
        let (only_fixmed, only_warning) = (
            filter(only_fixmed.clone(), |_, d| d.is_fixmed),
            filter(only_fixmed, |_, d| !d.is_fixmed),
        );
        assert_eq!(count(None, &only_fixmed), 0);
        assert!(!has_errors(None, &only_fixmed));
        assert!(has_errors(Some(false), &only_fixmed));
        assert!(has_no_errors_or_warnings(None, &only_fixmed));
        assert!(!has_no_errors_or_warnings(Some(false), &only_fixmed));
        assert_eq!(choose_code_opt(&only_fixmed), None);
        assert!(get_failed_files(&only_fixmed).is_empty());
        assert!(drop_fixmed_errors_in_files(only_fixmed).is_empty());
        // Warnings are not errors, but they are something to show.
        assert!(has_no_errors(None, &only_warning));
        assert!(!has_no_errors_or_warnings(None, &only_warning));
        assert_eq!(choose_code_opt(&only_warning), None);
        assert_eq!(warning_counts_by_code(&only_warning), IMap::from([(12001, 1)]));
        assert_eq!(
            count_errors_and_warnings(&get_diagnostic_list(None, only_warning.clone())),
            (0, 1)
        );
        assert!(filter_out_warnings(only_warning.clone()).is_empty());
        let saved_state = make_warning_saved_state(&only_warning);
        assert_eq!(saved_state.len(), 1);
        assert!(filter_out_mergebase_warnings(Some(&saved_state), only_warning.clone()).is_empty());
        assert_eq!(
            filter_out_mergebase_warnings(None, only_warning.clone()),
            only_warning
        );
    }

    #[test]
    fn merging() {
        let a = path("a.php");
        let b = path("b.php");
        let c = path("c.php");
        let e = |file: &RelativePath, text: &str| err(4110, pos_in(file, 1, 0..1), text);
        let x = from_file_diagnostic_list(vec![
            (a.clone(), e(&a, "x a 1")),
            (b.clone(), e(&b, "x b 1")),
            (a.clone(), e(&a, "x a 2")),
        ]);
        // Each error is put in front of the ones of its file.
        assert_eq!(claims(&x), ["x a 2", "x a 1", "x b 1"]);
        let y = from_file_diagnostic_list(vec![
            (a.clone(), e(&a, "y a 1")),
            (c.clone(), e(&c, "y c 1")),
            (a.clone(), e(&a, "y a 2")),
        ]);
        // `List.rev_append`
        assert_eq!(
            claims(&merge(x.clone(), y.clone())),
            ["x a 1", "x a 2", "y a 2", "y a 1", "x b 1", "y c 1"]
        );
        assert_eq!(merge(empty, y.clone()), y);
        assert_eq!(as_map(merge(x.clone(), empty)).len(), 2);

        // The errors of a `do_` are in the order they were added in, and so
        // are they after they have been merged into the current ones.
        let (errors, ()) = do_with_context(None, a.clone(), || {
            add_diagnostic(e(&a, "1"));
            let (inner, ()) = do_(None, || {
                add_diagnostic(e(&a, "2"));
                add_diagnostic(e(&a, "3"));
                run_in_context(b.clone(), || add_diagnostic(e(&b, "b")));
            });
            assert_eq!(claims(&inner), ["2", "3", "b"]);
            merge_into_current(inner);
            add_diagnostic(e(&a, "4"));
            // No check for a duplicate when merging.
            merge_into_current(from_file_diagnostic_list(vec![(a.clone(), e(&a, "4"))]));
        });
        assert_eq!(claims(&errors), ["1", "2", "3", "4", "4", "b"]);

        assert_eq!(
            claims(&from_diagnostic_list(vec![e(&a, "1"), e(&b, "2")])),
            ["1", "2"]
        );
        assert!(from_diagnostic_list(vec![]).is_empty());

        let mut folded = vec![];
        fold_errors(None, &x, (), |file, d, ()| {
            folded.push((file.clone(), d.claim.1.to_string()))
        });
        // `List.fold_right`
        assert_eq!(
            folded,
            [
                (a.clone(), "x a 1".to_string()),
                (a.clone(), "x a 2".to_string()),
                (b.clone(), "x b 1".to_string())
            ]
        );
        assert_eq!(
            fold_per_file_diagnostics(&x[&a], String::new(), |acc, d| acc + &d.claim.1.to_string()),
            "x a 2x a 1"
        );
    }

    #[test]
    fn incremental_update_replaces_the_errors_of_rechecked_files() {
        let a = path("a.php");
        let b = path("b.php");
        let c = path("c.php");
        let d = path("d.php");
        let e = |file: &RelativePath, text: &str| (file.clone(), err(4110, pos_in(file, 1, 0..1), text));
        let old = from_file_diagnostic_list(vec![e(&a, "old a"), e(&b, "old b"), e(&c, "old c")]);
        let new_ = from_file_diagnostic_list(vec![e(&a, "new a"), e(&d, "new d")]);
        let rechecked = BTreeSet::from([a.clone(), b.clone(), d.clone()]);
        let updated = incremental_update(old, new_, &rechecked);
        assert_eq!(claims(&updated), ["new a", "old c", "new d"]);
    }

    #[test]
    fn trusting_warnings() {
        let w = |line: usize, code: isize, is_trusted: bool| {
            warning(code, pos(line, 0..1), "w", is_trusted)
        };
        let (errors, ()) = do_with_context(None, path("a.php"), || {
            add_diagnostic(w(1, 12001, false));
            add_diagnostic(w(2, 12001, false));
            add_diagnostic(w(2, 12004, false));
            add_diagnostic(err(12001, pos(3, 0..1), "e"));
            let keys = collect_warning_keys(|| {
                add_diagnostic(w(2, 12001, false));
                add_diagnostic(err(4110, pos(2, 0..1), "e"));
                add_diagnostic(w(9, 12001, true));
            });
            assert_eq!(keys, [(12001, pos(9, 0..1)), (12001, pos(2, 0..1))]);
            mark_warnings_trusted(&keys);
        });
        assert_eq!(
            get_diagnostic_list(None, errors),
            [
                w(1, 12001, false),
                w(2, 12001, true),
                w(2, 12004, false),
                err(12001, pos(3, 0..1), "e"),
            ]
        );

        let (errors, ()) = do_with_context(None, path("a.php"), || {
            add_diagnostic(w(1, 12001, false));
            add_diagnostic(err(4110, pos(3, 0..1), "e"));
            run_in_context(path("b.php"), || {
                add_diagnostic(warning(12004, pos_in(&path("b.php"), 1, 0..1), "w", false))
            });
            mark_all_warnings_trusted();
            add_diagnostic(w(4, 12001, false));
        });
        assert_eq!(
            get_diagnostic_list(None, errors),
            [
                w(1, 12001, true),
                err(4110, pos(3, 0..1), "e"),
                w(4, 12001, false),
                warning(12004, pos_in(&path("b.php"), 1, 0..1), "w", true),
            ]
        );
    }

    // ~~ specific errors ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

    #[test]
    fn specific_errors() {
        let diags = added(|| {
            internal_error(pos(1, 0..1), "oops");
            experimental_feature(pos(2, 0..1), "feature");
            typechecker_timeout(pos(3, 0..1), "f", 10);
            global_access_error(
                GlobalAccessCheck::DefiniteGlobalRead,
                pos(4, 0..1),
                "a global is read".to_string(),
            );
        });
        assert_eq!(
            diags,
            [
                err(0, pos(1, 0..1), "Internal error: oops"),
                err(0, pos(2, 0..1), "Cannot use experimental feature: feature"),
                err(
                    4304,
                    pos(3, 0..1),
                    "Type checker timed out after 10 seconds whilst checking function f"
                ),
                err(11004, pos(4, 0..1), "a global is read"),
            ]
        );
    }

    #[test]
    fn not_dynamically_callable() {
        let nested = make_err(
            4110,
            msg(pos(7, 0..1), "Invalid return type"),
            vec![msg(pos(6, 0..1), "Expected `int`")],
            Explanation::Empty,
        );
        let diags = added(|| {
            function_is_not_dynamically_callable("\\f", &nested);
            method_is_not_dynamically_callable(
                pos(5, 0..1),
                "m",
                "\\C",
                true,
                None,
                None,
            );
            method_is_not_dynamically_callable(
                pos(5, 0..1),
                "m",
                "\\C",
                false,
                Some((pos(1, 0..1), "\\HH\\Traversable".to_string())),
                Some(&nested),
            );
        });
        assert_eq!(
            diags,
            [
                make_err(
                    4110,
                    msg(pos(7, 0..1), "Function  `f` is not dynamically callable."),
                    vec![
                        msg(pos(7, 0..1), "Invalid return type"),
                        msg(pos(6, 0..1), "Expected `int`")
                    ],
                    Explanation::Empty
                ),
                err(
                    4402,
                    pos(5, 0..1),
                    "Method  `m` in class `C` is not dynamically callable."
                ),
                make_err(
                    4110,
                    msg(
                        pos(7, 0..1),
                        "Method  `m` in class `C` is not dynamically callable."
                    ),
                    vec![
                        msg(
                            pos(1, 0..1),
                            "Method `m` is defined in the super class `Traversable` and is not overridden"
                        ),
                        msg(
                            pos(7, 0..1),
                            "A parameter of `m` is not enforceable. Try adding the <<__SupportDynamicType>> attribute to the method to check if its code is safe for dynamic calling."
                        ),
                        msg(pos(7, 0..1), "Invalid return type"),
                        msg(pos(6, 0..1), "Expected `int`")
                    ],
                    Explanation::Empty
                ),
            ]
        );
    }

    // ~~ printing ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

    #[test]
    fn summaries() {
        let summary = |format, errors, warnings, dropped, max| {
            format_summary(format, errors, warnings, dropped, max)
        };
        assert_eq!(
            summary(Format::Highlighted, 0, 0, None, None).as_deref(),
            Some("No errors!\n")
        );
        assert_eq!(
            summary(Format::Highlighted, 1, 0, None, None).as_deref(),
            Some("1 error found\n")
        );
        assert_eq!(
            summary(Format::Context, 10, 11, None, None).as_deref(),
            Some("10 errors, 11 warnings found\n")
        );
        assert_eq!(
            summary(Format::Agent, 0, 1, None, None).as_deref(),
            Some("No errors! 1 warning found\n")
        );
        assert_eq!(
            summary(Format::PlainHighlighted, 5, 0, Some(3), Some(2)).as_deref(),
            Some("5 errors found (only showing first 2, dropped 3)\n")
        );
        assert_eq!(
            summary(Format::Highlighted, 5, 0, None, Some(5)).as_deref(),
            Some("5 errors found (max-errors is 5; more errors may exist)\n")
        );
        assert_eq!(
            summary(Format::Plain, 0, 0, None, None).as_deref(),
            Some("No errors!\n")
        );
        assert_eq!(summary(Format::Raw, 1, 0, None, None), None);
        assert_eq!(summary(Format::Extended, 0, 1, None, None), None);
        assert_eq!(format_or_default(None), Format::Highlighted);
        assert_eq!(format_or_default(Some(Format::Raw)), Format::Raw);
    }

    #[test]
    fn helpers() {
        assert_eq!(
            combining_sort(vec!["b1", "a1", "b2", "c1", "a2"], |x| x[..1].to_string()),
            ["b1", "b2", "a1", "a2", "c1"]
        );
        assert_eq!(num_digits(1), 1);
        assert_eq!(num_digits(9), 1);
        assert_eq!(num_digits(10), 2);
        assert_eq!(num_digits(12345), 5);
        // `int_of_float neg_infinity` is 0 in OCaml native code.
        assert_eq!(num_digits(0), 1);
        assert_eq!(num_digits(-3), 1);
        assert!(pos_contains(&pos(1, 0..9), &pos(1, 2..9)));
        assert!(!pos_contains(&pos(1, 0..9), &pos(1, 2..10)));
        assert!(!pos_contains(&pos(1, 0..9), &pos_in(&path("b.php"), 1, 2..9)));
        assert_eq!(warning_of_enum(12001), Some(error_codes::Warning::SketchyEquality));
        assert_eq!(warning_of_enum(12043), Some(error_codes::Warning::RedundantRequireThisAs));
        assert_eq!(warning_of_enum(12003), None);
        assert_eq!(warning_of_enum(4110), None);
        for code in 12000..12100 {
            if let Some(warning) = warning_of_enum(code) {
                assert_eq!(warning as isize, code);
            }
        }
    }
}
