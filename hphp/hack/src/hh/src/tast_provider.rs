// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `providers/tast_provider.ml`.
//!
//! Owned by **P0** (plan §7.3).
//!
//! The typed AST and the diagnostics of an entry (a file of a context,
//! possibly with unsaved contents): its parse (`Ast_provider`), its naming
//! (`Naming.program`) and its typing (`Typing_toplevel.nast_to_tast`), memoized
//! in the entry. `entry.tast` is kept per thread
//! (`Provider_context.get_entry_tast`, a TAST is not `Send`);
//! `entry.all_diagnostics` is in the entry.
//!
//! The GADT `_ compute_tast_mode` is the private [`Mode`]; its results are
//! [`ComputeTastResult`] and [`ComputeTastAndErrors`].

use std::sync::Arc;

use crate::ast_provider;
use crate::counters;
use crate::diagnostics_state;
use crate::filter_diagnostics;
use crate::hh_logger;
use crate::provider_context;
use crate::tast;
use crate::tast_with_dynamic;
use crate::telemetry;

/// `Compute_tast.t`
pub struct ComputeTastResult {
    pub tast: tast_with_dynamic::T<tast::Program>,
    pub telemetry: telemetry::T,
}

/// `Compute_tast_and_errors.t`
pub struct ComputeTastAndErrors {
    pub tast: tast_with_dynamic::T<tast::Program>,
    pub diagnostics: diagnostics_state::T,
    pub telemetry: telemetry::T,
}

/// `ErrorFilter.t`
#[derive(Clone, Debug)]
pub struct ErrorFilter {
    pub error_filter: filter_diagnostics::filter::T,
    pub warnings_saved_state: Option<oxidized::warnings_saved_state_impl::WarningsSavedState>,
}

impl ErrorFilter {
    /// `ErrorFilter.default`
    pub fn default() -> Self {
        Self {
            error_filter: filter_diagnostics::filter::make(true, vec![], vec![]),
            warnings_saved_state: None,
        }
    }

    /// `ErrorFilter.apply`
    fn apply(&self, errors: diagnostics_state::T) -> diagnostics_state::T {
        let errors = diagnostics_state::filter_out_mergebase_warnings(
            self.warnings_saved_state.as_ref(),
            errors,
        );
        filter_diagnostics::filter_rel(&self.error_filter, errors)
    }
}

/// `_ compute_tast_mode`
#[derive(Clone, Copy)]
enum Mode<'a> {
    ComputeTastOnly,
    ComputeTastAndErrors(&'a ErrorFilter),
}

/// What [`compute_tast_and_errors_unquarantined_internal`] returns for a
/// [`Mode`]: the diagnostics only for `Compute_tast_and_errors`.
struct Computed {
    tast: tast_with_dynamic::T<tast::Program>,
    diagnostics: Option<diagnostics_state::T>,
    telemetry: telemetry::T,
}

/// `seconds_since_epoch`
type SecondsSinceEpoch = f64;

/// `start_telemetry`
struct StartTelemetry {
    prev_ctx_telemetry: telemetry::T,
    start_gc_telemetry: telemetry::T,
    start_tally_state: counters::T,
    start_time: SecondsSinceEpoch,
}

/// `Unix.gettimeofday ()`
fn gettimeofday() -> f64 {
    match std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH) {
        Ok(d) => d.as_secs_f64(),
        Err(e) => -e.duration().as_secs_f64(),
    }
}

/// `Telemetry.quick_gc_stat ()`: the statistics of the OCaml GC, which has
/// no counterpart (an empty object).
fn quick_gc_stat() -> telemetry::T {
    telemetry::create()
}

/// `prepare_logging ctx`
fn prepare_logging(ctx: &provider_context::T) -> StartTelemetry {
    provider_context::reset_telemetry(ctx);
    let prev_ctx_telemetry = provider_context::get_telemetry(ctx);
    // `Decl_counters.set_mode Hack_event_logger.PerFileProfilingConfig.DeclingTopCounts`:
    // not done. Its only effect is to count the decl accesses of the typing
    // into the telemetry below (`Counters.Category.Decl_provider_get`); the
    // mode is a global of the process here (the OCaml sets it in the process
    // that serves the request, not in its workers), and its counting path is
    // not ported (`crate::folded_class::decl_counters::count_decl`).
    StartTelemetry {
        prev_ctx_telemetry,
        start_gc_telemetry: quick_gc_stat(),
        start_tally_state: counters::reset(),
        start_time: gettimeofday(),
    }
}

/// `log_and_telemetry ctx start_telemetry entry ~ast_errors ~naming_errors ~typing_errors`
fn log_and_telemetry(
    ctx: &provider_context::T,
    start: StartTelemetry,
    entry: &provider_context::Entry,
    ast_errors: &diagnostics_state::T,
    naming_errors: &diagnostics_state::T,
    typing_errors: &diagnostics_state::T,
) -> telemetry::T {
    let StartTelemetry {
        prev_ctx_telemetry,
        start_gc_telemetry,
        start_tally_state,
        start_time,
    } = start;
    let debug = hh_logger::level::passes_min_level(hh_logger::level::T::Debug);
    let ctx_telemetry = if debug {
        telemetry::diff(
            true,
            None,
            &provider_context::get_telemetry(ctx),
            &prev_ctx_telemetry,
        )
    } else {
        provider_context::get_telemetry(ctx)
    };
    let gc_telemetry = if debug {
        telemetry::diff(true, None, &quick_gc_stat(), &start_gc_telemetry)
    } else {
        quick_gc_stat()
    };
    let telemetry = counters::get_counters();
    counters::restore_state(start_tally_state);
    let telemetry = telemetry::object_("ctx", ctx_telemetry, telemetry);
    let telemetry = telemetry::object_("gc", gc_telemetry, telemetry);
    let telemetry = telemetry::int_(
        "errors.ast",
        diagnostics_state::count(None, ast_errors),
        telemetry,
    );
    let telemetry = telemetry::int_(
        "errors.nast",
        diagnostics_state::count(None, naming_errors),
        telemetry,
    );
    let telemetry = telemetry::int_(
        "errors.tast",
        diagnostics_state::count(None, typing_errors),
        telemetry,
    );
    let telemetry = telemetry::float_(
        "duration_decl_and_typecheck",
        gettimeofday() - start_time,
        telemetry,
    );
    let telemetry = telemetry::int_(
        "filesize",
        provider_context::get_file_contents_if_present(entry)
            .unwrap_or_default()
            .len() as isize,
        telemetry,
    );
    hh_logger::debug(
        None,
        None,
        &format!(
            "compute_tast: {}\n{}",
            crate::relative_path::suffix(&entry.path),
            telemetry::to_string(None, &telemetry)
        ),
    );
    // `Hack_event_logger.ProfileTypeCheck.compute_tast ~telemetry ~path ~start_time`:
    // a no-op in the open-source build.
    telemetry
}

/// `compute_tast_and_errors_unquarantined_internal ~ctx ~entry ~mode`
fn compute_tast_and_errors_unquarantined_internal(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    mode: Mode<'_>,
) -> Computed {
    let tast = provider_context::get_entry_tast(entry);
    let all_diagnostics = entry.all_diagnostics.lock().unwrap().clone();
    match (mode, tast, all_diagnostics) {
        (Mode::ComputeTastOnly, Some(tast), _) => Computed {
            tast,
            diagnostics: None,
            telemetry: telemetry::create(),
        },
        (Mode::ComputeTastAndErrors(_), Some(tast), Some(diagnostics)) => Computed {
            tast,
            diagnostics: Some(diagnostics),
            telemetry: telemetry::create(),
        },
        (_, _, _) => {
            let start_telemetry = prepare_logging(ctx);

            let (crate::parser_return::T { ast, .. }, ast_errors) =
                ast_provider::compute_parser_return_and_ast_errors(
                    provider_context::get_popt(ctx),
                    entry,
                );
            let (naming_errors, nast) =
                diagnostics_state::do_with_context(None, entry.path.clone(), || {
                    crate::naming::program(ctx, ast)
                });
            let (typing_errors, tast) = {
                let do_tast_checks = match mode {
                    Mode::ComputeTastOnly => false,
                    Mode::ComputeTastAndErrors(_) => true,
                };
                diagnostics_state::do_with_context(None, entry.path.clone(), || {
                    crate::typing_toplevel::nast_to_tast(do_tast_checks, ctx, &nast)
                })
            };

            let telemetry = log_and_telemetry(
                ctx,
                start_telemetry,
                entry,
                &ast_errors,
                &naming_errors,
                &typing_errors,
            );

            match mode {
                Mode::ComputeTastAndErrors(error_filter) => {
                    // `naming_errors |> Diagnostics.merge typing_errors |> Diagnostics.merge ast_errors`
                    // (F7: the piped value is the second argument of `merge`.)
                    let diagnostics = diagnostics_state::merge(typing_errors, naming_errors);
                    let diagnostics = diagnostics_state::merge(ast_errors, diagnostics);
                    let diagnostics = error_filter.apply(diagnostics);
                    provider_context::set_entry_tast(entry, Some(tast.clone()));
                    *entry.all_diagnostics.lock().unwrap() = Some(diagnostics.clone());
                    Computed {
                        tast,
                        diagnostics: Some(diagnostics),
                        telemetry,
                    }
                }
                Mode::ComputeTastOnly => {
                    provider_context::set_entry_tast(entry, Some(tast.clone()));
                    Computed {
                        tast,
                        diagnostics: None,
                        telemetry,
                    }
                }
            }
        }
    }
}

fn with_errors(computed: Computed) -> ComputeTastAndErrors {
    let Computed {
        tast,
        diagnostics,
        telemetry,
    } = computed;
    ComputeTastAndErrors {
        tast,
        diagnostics: diagnostics.expect("Compute_tast_and_errors gives the diagnostics"),
        telemetry,
    }
}

fn without_errors(computed: Computed) -> ComputeTastResult {
    ComputeTastResult {
        tast: computed.tast,
        telemetry: computed.telemetry,
    }
}

/// `compute_tast_and_errors_unquarantined ~ctx ~entry ~error_filter`:
/// This function computes TAST and error-list (both "naming" errors and
/// typing errors, and also "name already bound" errors) by taking the AST in
/// a context entry, and typechecking it, and memoizing the result (caching
/// the results in the context entry). CAUTION: this function doesn't use a
/// quarantine, and so is inappropriate for IDE scenarios.
pub fn compute_tast_and_errors_unquarantined(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    error_filter: &ErrorFilter,
) -> ComputeTastAndErrors {
    with_errors(compute_tast_and_errors_unquarantined_internal(
        ctx,
        entry,
        Mode::ComputeTastAndErrors(error_filter),
    ))
}

/// `compute_tast_unquarantined ~ctx ~entry`: computes TAST by taking the
/// AST in a context entry, and typechecking it, and memoizing the result
/// (caching the results in the context entry). CAUTION: this function
/// doesn't use a quarantine, and so is inappropriate for IDE scenarios.
/// Also, it doesn't compute the full error list.
pub fn compute_tast_unquarantined(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
) -> ComputeTastResult {
    without_errors(compute_tast_and_errors_unquarantined_internal(
        ctx,
        entry,
        Mode::ComputeTastOnly,
    ))
}

/// `compute_tast_and_errors_quarantined ~ctx ~entry ~error_filter`: this
/// function computes the TAST and error-list (naming, typing, name already
/// bound) of an entry, memoizing them in the entry; the suffix
/// "quarantined" means that this function enforces a quarantine in case one
/// isn't yet in force. CAUTION: this function is only appropriate for IDE
/// scenarios.
pub fn compute_tast_and_errors_quarantined(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    error_filter: &ErrorFilter,
) -> ComputeTastAndErrors {
    // If results have already been memoized, don't bother quarantining anything
    let tast = provider_context::get_entry_tast(entry);
    let all_diagnostics = entry.all_diagnostics.lock().unwrap().clone();
    match (tast, all_diagnostics) {
        (Some(tast), Some(diagnostics)) => ComputeTastAndErrors {
            tast,
            diagnostics,
            telemetry: telemetry::create(),
        },
        // Okay, we don't have memoized results, let's ensure we are quarantined before computing
        _ => {
            let f = || compute_tast_and_errors_unquarantined(ctx, entry, error_filter);
            if provider_context::is_quarantined() {
                f()
            } else {
                crate::provider_utils::respect_but_quarantine_unsaved_changes(ctx, f)
            }
        }
    }
}

/// `compute_tast_quarantined ~ctx ~entry`: same as
/// [`compute_tast_and_errors_quarantined`], but skips computing the full
/// error list. If the errors are needed at a later time, you'll have to
/// incur the full cost of recomputing the entire TAST and errors.
pub fn compute_tast_quarantined(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
) -> ComputeTastResult {
    // If results have already been memoized, don't bother quarantining anything
    match provider_context::get_entry_tast(entry) {
        Some(tast) => ComputeTastResult {
            tast,
            telemetry: telemetry::create(),
        },
        // Okay, we don't have memoized results, let's ensure we are quarantined before computing
        None => {
            let f = || {
                without_errors(compute_tast_and_errors_unquarantined_internal(
                    ctx,
                    entry,
                    Mode::ComputeTastOnly,
                ))
            };
            if provider_context::is_quarantined() {
                f()
            } else {
                crate::provider_utils::respect_but_quarantine_unsaved_changes(ctx, f)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;
    use std::sync::Mutex;

    use bstr::BString;
    use pos::Prefix;

    use super::*;
    use crate::ctx::Ctx;

    /// The decl store of the process is global (`hh_single_type_check::install`):
    /// one test at a time.
    static ONE_AT_A_TIME: Mutex<()> = Mutex::new(());

    /// Runs `f` on a thread with the stack of a checker thread, one test at
    /// a time.
    fn run(f: impl FnOnce() + Send + 'static) {
        let _guard = ONE_AT_A_TIME.lock().unwrap_or_else(|e| e.into_inner());
        if let Err(e) = crate::check::run_on_large_stack("tast_provider test", f) {
            std::panic::resume_unwind(e)
        }
    }

    fn path(name: &str) -> pos::RelativePath {
        pos::RelativePath::new(Prefix::Root, name)
    }

    fn ox(name: &str) -> relative_path::RelativePath {
        path(name).into()
    }

    /// A context as `hh single` makes one (its options, the hhi files, the
    /// magic builtins) with `files` on "disk", declared.
    fn base_ctx(files: &[(&str, &str)]) -> provider_context::T {
        let tco = crate::hh_single_type_check::make_tcopt(&Default::default())
            .unwrap()
            .tcopt;
        let root = Path::new("/hh_tast_provider_test_root");
        crate::hh_single_type_check::set_path_prefixes(root);
        let mut ctx = Ctx::new(root, tco).unwrap();
        ctx.add_magic_builtins();
        let mut paths = ctx.hhi_paths.clone();
        for (name, text) in files {
            ctx.files.set(path(name), *text);
            paths.push(path(name));
        }
        let mut stats = Default::default();
        crate::check::declare_files(&ctx, &paths, &mut stats);
        let ctx = Arc::new(ctx);
        crate::hh_single_type_check::install(&ctx);
        ctx
    }

    fn sorted(errors: diagnostics_state::T) -> Vec<String> {
        diagnostics_state::get_sorted_diagnostic_list(None, errors)
            .iter()
            .map(|d| format!("{:?}", d))
            .collect()
    }

    fn codes(errors: &diagnostics_state::T) -> Vec<isize> {
        diagnostics_state::get_sorted_diagnostic_list(None, errors.clone())
            .iter()
            .map(|d| d.code)
            .collect()
    }

    const A: &str = "<?hh
class C {
  public function m(): int { return 1; }
}
function f(C $c): string {
  return $c->m();
}
function g(): void {
  undefined_function();
}
";

    /// The TAST and the diagnostics of an entry are those of `hh single` on
    /// the same contents.
    #[test]
    fn same_as_hh_single() {
        run(|| {
            for text in [A, "<?hh\nfunction f(): int { return ; }\nfunction g(\n"] {
                let ctx = base_ctx(&[("a.php", text)]);
                // `hh single`: `parse_name_and_decl`, then `check_file`.
                let files = vec![ox("a.php")];
                let errors = crate::hh_single_type_check::parse_name_and_decl(&ctx, &files);
                let expected = crate::hh_single_type_check::check_file(&ctx, errors, &files);
                let full_ast = crate::ast_provider::get_ast(true, &ctx, &ox("a.php"));
                let (_, expected_tast) =
                    crate::typing_check_job::calc_errors_and_tast(&ctx, None, &ox("a.php"), full_ast);

                let (ctx, entry) =
                    provider_context::add_or_overwrite_entry_contents(&ctx, ox("a.php"), BString::from(text));
                let ComputeTastAndErrors {
                    tast, diagnostics, ..
                } = compute_tast_and_errors_unquarantined(&ctx, &entry, &ErrorFilter::default());
                assert!(!diagnostics_state::has_no_errors(None, &diagnostics));
                assert_eq!(sorted(diagnostics.clone()), sorted(expected));
                // The definitions of `Typing_check_job`, by name.
                let defs = |tast: &tast_with_dynamic::T<tast::Program>| {
                    let mut defs: Vec<String> =
                        tast.under_normal_assumptions.0.iter().map(|d| format!("{:?}", d)).collect();
                    defs.sort();
                    defs
                };
                let mut expected_defs: Vec<String> = expected_tast
                    .fun_tasts
                    .values()
                    .chain(expected_tast.class_tasts.values())
                    .map(|d| format!("{:?}", d.under_normal_assumptions))
                    .chain(
                        expected_tast
                            .typedef_tasts
                            .values()
                            .chain(expected_tast.gconst_tasts.values())
                            .chain(expected_tast.module_tasts.values())
                            .map(|d| format!("{:?}", d)),
                    )
                    .collect();
                expected_defs.sort();
                assert_eq!(defs(&tast), expected_defs);

                // Memoized: the same, without computing again.
                let again = compute_tast_and_errors_quarantined(&ctx, &entry, &ErrorFilter::default());
                assert_eq!(sorted(again.diagnostics), sorted(diagnostics));
                assert_eq!(again.telemetry, telemetry::create());
                assert_eq!(defs(&again.tast), defs(&tast));
            }
        })
    }

    const DISK_A: &str = "<?hh
function f(): int { return 1; }
";

    const DISK_B: &str = "<?hh
function g(): int { h(); return f(); }
function k(): int { return f(); }
";

    const UNSAVED_A: &str = "<?hh
function f(): string { return 'a'; }
function h(): void {}
function i(): int { return j(); }
function j(): string { return 'b'; }
";

    /// Unsaved contents that change a signature are seen by the entry and by
    /// a dependent entry inside the quarantine, and by nobody after it.
    ///
    /// As with the OCaml (`Shared_memory` backend): a lookup finds the
    /// declarations of the disk first; the contents of an entry are parsed
    /// when a lookup misses a name only the entry declares (`h`, `j`), and
    /// then its declarations replace those of the disk (`f`).
    #[test]
    fn quarantine_sees_unsaved_contents_and_leaks_nothing() {
        run(|| {
            let root = base_ctx(&[("a.php", DISK_A), ("b.php", DISK_B)]);
            let (ctx, _a) =
                provider_context::add_or_overwrite_entry_contents(&root, ox("a.php"), BString::from(UNSAVED_A));
            let (ctx, b) =
                provider_context::add_or_overwrite_entry_contents(&ctx, ox("b.php"), BString::from(DISK_B));
            let lc = provider_context::local_changes::of_ctx(&ctx).unwrap();
            let fun_ret = |ctx: &provider_context::T, name: &str| {
                let decl = ctx
                    .shallow_decls
                    .get_fun(pos::FunName::new(format!("\\{}", name)))
                    .unwrap();
                decl.map(|d| format!("{:?}", d.ty))
            };
            let disk_f = fun_ret(&root, "f").unwrap();
            assert_eq!(fun_ret(&root, "h"), None);
            let errors = crate::provider_utils::respect_but_quarantine_unsaved_changes(&ctx, || {
                assert!(provider_context::is_quarantined());
                assert_eq!(lc.depth(), 1);
                // The dependent entry: `h()` makes `a.php` parsed, then `f`
                // is the unsaved one: two "Invalid return type".
                let b_errors = compute_tast_and_errors_quarantined(&ctx, &b, &ErrorFilter::default());
                assert_ne!(fun_ret(&ctx, "f"), Some(disk_f.clone()));
                assert!(fun_ret(&ctx, "h").is_some());
                // The entry itself: `j` is only in the unsaved contents.
                let (ctx2, a2) =
                    provider_context::add_entry_if_missing(&ctx, ox("a.php"));
                assert!(Arc::ptr_eq(&ctx2, &ctx));
                let a_errors = compute_tast_and_errors_quarantined(&ctx, &a2, &ErrorFilter::default());
                (b_errors.diagnostics, a_errors.diagnostics)
            });
            let (b_errors, a_errors) = errors;
            assert_eq!(codes(&b_errors), vec![4110, 4110], "{:?}", sorted(b_errors.clone()));
            assert_eq!(codes(&a_errors), vec![4110], "{:?}", sorted(a_errors.clone()));
            // After: nothing left.
            assert!(!provider_context::is_quarantined());
            assert_eq!(lc.depth(), 0);
            assert_eq!(fun_ret(&root, "f"), Some(disk_f.clone()));
            assert_eq!(fun_ret(&root, "h"), None);
            // The context of the quarantine itself: its frame is gone.
            assert_eq!(fun_ret(&ctx, "f"), Some(disk_f.clone()));
            // A new context on the disk contents: `h` is unbound (Naming[2049],
            // Typing[4107]), `f` is `int`.
            let (ctx3, b3) =
                provider_context::add_or_overwrite_entry_contents(&root, ox("b.php"), BString::from(DISK_B));
            let b3_errors = compute_tast_and_errors_quarantined(&ctx3, &b3, &ErrorFilter::default());
            assert_eq!(codes(&b3_errors.diagnostics), vec![2049, 4107]);
            // The decls of the disk win over those of an entry when no lookup
            // misses, as in the OCaml: `k` sees `f: int`; and as `k` is at
            // another line on disk, the decl that wins `k` is not this
            // definition (`Decl_provider.is_this_def_the_winner` compares
            // the positions of the decl and of the AST): "Name already bound".
            let (ctx4, _) =
                provider_context::add_or_overwrite_entry_contents(&root, ox("a.php"), BString::from(UNSAVED_A));
            let (ctx4, b4) = provider_context::add_or_overwrite_entry_contents(
                &ctx4,
                ox("b.php"),
                BString::from("<?hh\nfunction k(): int { return f(); }\n"),
            );
            let b4_errors = compute_tast_and_errors_quarantined(&ctx4, &b4, &ErrorFilter::default());
            assert_eq!(codes(&b4_errors.diagnostics), vec![2012], "{:?}", sorted(b4_errors.diagnostics.clone()));
        })
    }

    /// The OCaml's assertions about nested quarantines: entering one inside
    /// another raises, and leaves everything as the outer one had it; the
    /// `_quarantined` functions do not enter a second one.
    #[test]
    fn nested_quarantine() {
        run(|| {
            let root = base_ctx(&[("a.php", DISK_A)]);
            let (ctx, a) =
                provider_context::add_or_overwrite_entry_contents(&root, ox("a.php"), BString::from(UNSAVED_A));
            let lc = provider_context::local_changes::of_ctx(&ctx).unwrap();
            crate::provider_utils::respect_but_quarantine_unsaved_changes(&ctx, || {
                let nested = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    crate::provider_utils::respect_but_quarantine_unsaved_changes(&ctx, || ())
                }));
                let message = crate::exception::get_ctor_string(&crate::exception::wrap(nested.unwrap_err()));
                assert!(message.contains("set_is_quarantined: was already quarantined at"), "{}", message);
                assert!(provider_context::is_quarantined());
                assert_eq!(lc.depth(), 1);
                // Inside a quarantine, no other one.
                let result = compute_tast_quarantined(&ctx, &a);
                assert!(!result.tast.under_normal_assumptions.0.is_empty());
            });
            assert!(!provider_context::is_quarantined());
            assert_eq!(lc.depth(), 0);
            // A raise inside the quarantine leaves it.
            let raised = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                crate::provider_utils::respect_but_quarantine_unsaved_changes(&ctx, || panic!("in f"))
            }));
            assert!(raised.is_err());
            assert!(!provider_context::is_quarantined());
            assert_eq!(lc.depth(), 0);
        })
    }

    /// `test/integration_ml/ide/test_unsaved_changes.ml`, the part this layer
    /// answers: an unsaved `foo.php` does not affect `bar.php`, whether the
    /// context has `bar.php` alone (as the IDE daemon makes it) or both
    /// (`foo` is found on disk: no lookup misses).
    #[test]
    fn ide_unsaved_changes() {
        run(|| {
            let foo_takes_int = "<?hh // strict\n\nfunction foo(int $x) : void {}\n";
            let foo_takes_string = "<?hh // strict\n\nfunction foo(string $x) : void {}\n";
            let bar = "<?hh // strict\n\nfunction test(mixed $x): void {\n  foo($x);\n}\n";
            let root = base_ctx(&[("bar.php", bar), ("foo.php", foo_takes_int)]);
            let disk_diagnostics = |errors: diagnostics_state::T| {
                let errors = sorted(errors);
                assert_eq!(errors.len(), 1, "{:?}", errors);
                // ERROR: File "/bar.php", line 4, characters 7-8:
                // Invalid argument (Typing[4110])
                //   File "/foo.php", line 3, characters 14-16:
                //   Expected `int`
                //   File "/bar.php", line 3, characters 15-19:
                //   But got `mixed`
                assert!(errors[0].contains("code: 4110"), "{}", errors[0]);
                assert!(errors[0].contains("root|bar.php(4:6-8)"), "{}", errors[0]);
                assert!(errors[0].contains("root|foo.php(3:13-16)"), "{}", errors[0]);
                assert!(errors[0].contains("root|bar.php(3:14-19)"), "{}", errors[0]);
            };
            let (ctx, entry) =
                provider_context::add_or_overwrite_entry_contents(&root, ox("bar.php"), BString::from(bar));
            disk_diagnostics(
                compute_tast_and_errors_quarantined(&ctx, &entry, &ErrorFilter::default()).diagnostics,
            );
            let (ctx, _) = provider_context::add_or_overwrite_entry_contents(
                &root,
                ox("foo.php"),
                BString::from(foo_takes_string),
            );
            let (ctx, entry) =
                provider_context::add_or_overwrite_entry_contents(&ctx, ox("bar.php"), BString::from(bar));
            disk_diagnostics(
                compute_tast_and_errors_quarantined(&ctx, &entry, &ErrorFilter::default()).diagnostics,
            );
        })
    }

    /// `test/integration_ml/ide/test_union_intersection_type_hints_single_file.ml`:
    /// `Typing_toplevel.nast_to_tast` applies the `__EnableUnstableFeatures`
    /// file attribute (no spurious GatedByFeatureFlag, Typing[4509]).
    #[test]
    fn ide_union_intersection_type_hints_single_file() {
        run(|| {
            let gated_def = "<?hh
<<file: __EnableUnstableFeatures('union_intersection_type_hints')>>

<<__GatedByFeatureFlag('union_intersection_type_hints')>>
newtype MyGated<T> = T;
";
            let use_gated = "<?hh
<<file: __EnableUnstableFeatures('union_intersection_type_hints')>>

type UseGated = MyGated<int>;
";
            let root = base_ctx(&[("gated_def.php", gated_def), ("use_gated.php", use_gated)]);
            let (ctx, entry) = provider_context::add_entry_if_missing(&root, ox("use_gated.php"));
            // (Read from "disk": the contents of the context's files.)
            *entry.contents.lock().unwrap() =
                provider_context::EntryContents::ProvidedContents(BString::from(use_gated));
            let errors = compute_tast_and_errors_quarantined(&ctx, &entry, &ErrorFilter::default());
            assert_eq!(sorted(errors.diagnostics), Vec::<String>::new());
        })
    }

    /// A typedef lookup reads the typedef store alone, as the OCaml's
    /// (`Decl_provider_internals.get_typedef_without_pessimise`,
    /// `Shared_memory`): it does not look for a class of that name first,
    /// whose miss would ask the naming table, which reads the entries (here
    /// one whose file cannot be read: that read raises). Found by F2:
    /// `hh single subtype_bug_6.php --hover 18 15` (test/typecheck).
    #[test]
    fn typedef_lookup_does_not_read_the_entries() {
        run(|| {
            let root = base_ctx(&[("file1.php", "<?hh\nnewtype ID as int = int;\n")]);
            let (ctx, entry) = provider_context::add_entry_if_missing(&root, ox("not_on_disk.php"));
            let found = crate::decl_entry::to_option(crate::decl_provider::get_typedef(None, &ctx, "\\ID"));
            assert!(found.is_some());
            // The entry was not read.
            assert!(matches!(
                &*entry.contents.lock().unwrap(),
                provider_context::EntryContents::NotYetReadFromDisk
            ));
            // A class lookup that misses does read it (as the OCaml's
            // `Naming_provider.get_class_path`, entries first), and raises.
            let class = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                crate::decl_provider::get_class(None, &ctx, "\\NoSuchClass")
            }));
            assert!(class.is_err());
        })
    }
}
