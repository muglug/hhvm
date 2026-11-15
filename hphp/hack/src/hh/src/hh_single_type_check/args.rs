// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! The option table of `parse_options` of `hh_single_type_check.ml`, for
//! `Arg.parse` (`crate::rt::ocaml_arg`): every option the OCaml accepts, with
//! its kind of argument and its documentation, in its order, so that an
//! unknown option, a missing or wrong argument, a second mode and `--help`
//! are reported as the OCaml's `Arg` reports them (on stderr, exit 2; the
//! help on stdout, exit 0). The table was translated mechanically from the
//! OCaml list (`--help` output checked against the OCaml binary's). The
//! options themselves are interpreted by `hh_single_cli.rs`, after this
//! validation; the functions here only check the modes.

use std::cell::Cell;

use crate::rt::ocaml_arg;
use crate::rt::ocaml_arg::Exn;
use crate::rt::ocaml_arg::Spec;

/// `set_mode x ()`: `raise (Arg.Bad "only a single mode should be specified")`
/// when a mode is already set.
fn set_mode(m: &Cell<bool>) -> ocaml_arg::Res {
    if m.get() {
        Err(Exn::Bad("only a single mode should be specified".to_string()))
    } else {
        m.set(true);
        Ok(())
    }
}

/// `Arg.parse (Arg.align ~limit:25 options) anon usage` over `args` (the
/// arguments after the program name `argv0`): prints and exits as the OCaml
/// does on an error or on `--help`; returns otherwise.
pub fn parse(argv0: &str, args: &[String]) {
    let mode_set = Cell::new(false);
    let m = &mode_set;
    let mode = |m: &Cell<bool>| set_mode(m);
    let options: ocaml_arg::Speclist<'_> = vec![
        ("--config".to_string(), Spec::String(Box::new(move |_| Ok(()))), "<option=value> Set one hhconfig option; can be used multiple times".to_string()),
        ("--no-print-position".to_string(), Spec::Unit(Box::new(move || Ok(()))), " Don't print positions while printing TASTs and NASTs".to_string()),
        ("--naming-table".to_string(), Spec::String(Box::new(move |_| Ok(()))), " Naming table, to look up undefined symbols; needs --root. (Hint: buck2 run //hphp/hack/src/hh_naming_table_builder)".to_string()),
        ("--root".to_string(), Spec::String(Box::new(move |_| Ok(()))), " Root for where to look up undefined symbols; needs --naming-table".to_string()),
        ("--extra-builtin".to_string(), Spec::String(Box::new(move |_| Ok(()))), " HHI file to parse and declare".to_string()),
        ("--refactor-sound-dynamic".to_string(), Spec::Tuple(vec![Spec::String(Box::new(move |_| Ok(()))), Spec::String(Box::new(move |_| Ok(()))), Spec::String(Box::new(move |_| mode(m)))]), " Run the flow analysis".to_string()),
        ("--deregister-attributes".to_string(), Spec::Unit(Box::new(move || Ok(()))), " Ignore all functions with attribute '__PHPStdLib'".to_string()),
        ("--auto-namespace-map".to_string(), Spec::String(Box::new(move |_| Ok(()))), " Alias namespaces".to_string()),
        ("--no-strict-contexts".to_string(), Spec::Unit(Box::new(move || Ok(()))), " Do not enforce contexts to be defined within Contexts namespace".to_string()),
        ("--cst-search".to_string(), Spec::Unit(Box::new(move || mode(m))), " Search the concrete syntax tree of the given file using the pattern given on stdin. (The pattern is a JSON object adhering to the search DSL.)".to_string()),
        ("--dump-symbol-info".to_string(), Spec::Unit(Box::new(move || mode(m))), " Dump all symbol information".to_string()),
        ("--run-simplihack".to_string(), Spec::Unit(Box::new(move || mode(m))), " Run SimpliHack on the file and print the prompts that are produced".to_string()),
        ("--glean-index".to_string(), Spec::String(Box::new(move |_| mode(m))), " Run indexer and output json in provided dir".to_string()),
        ("--glean-sym-hash".to_string(), Spec::Unit(Box::new(move || mode(m))), " Print symbols hashes used by incremental indexer".to_string()),
        ("--error-format".to_string(), Spec::String(Box::new(move |_| Ok(()))), "<format> Error formatting style (default: highlighted); valid formats: agent, extended, raw, context, highlighted, plain, plain_highlighted".to_string()),
        ("--lint".to_string(), Spec::Unit(Box::new(move || mode(m))), " Produce lint errors".to_string()),
        ("--lint-json".to_string(), Spec::Unit(Box::new(move || mode(m))), " Produce json lint output".to_string()),
        ("--no-builtins".to_string(), Spec::Unit(Box::new(move || Ok(()))), " Don't use builtins (e.g. ConstSet); implied by --root".to_string()),
        ("--out-extension".to_string(), Spec::String(Box::new(move |_| Ok(()))), " output file extension (default .out)".to_string()),
        ("--dump-deps".to_string(), Spec::Unit(Box::new(move || mode(m))), " Print dependencies".to_string()),
        ("--dump-dep-hashes".to_string(), Spec::Unit(Box::new(move || mode(m))), " Print dependency hashes".to_string()),
        ("--dump-inheritance".to_string(), Spec::Unit(Box::new(move || mode(m))), " Print inheritance".to_string()),
        ("--get-some-file-deps".to_string(), Spec::Int(Box::new(move |_| mode(m))), " Print a list of files this file depends on. The provided integer is the depth of the traversal. Requires --root, --naming-table and --depth".to_string()),
        ("--get-some-file-deps-full-hierarchy".to_string(), Spec::Unit(Box::new(move || Ok(()))), " Include all dependencies from class hierarchies in the list of files this file depends on regardless of their depth.".to_string()),
        ("--ide-code-actions".to_string(), Spec::String(Box::new(move |_| mode(m))), "<title_prefix> Apply a code action with the given title prefix to the given file, where the selection is indicated with markers in comments: `/*range-start*/the_code_here/*range-end*/` or `^ at-caret` with the caret pointing to the previous line.".to_string()),
        ("--ide-code-actions-no-experimental-capabilities".to_string(), Spec::String(Box::new(move |_| mode(m))), "<title_prefix> Like --ide-code-actions, but do not use any nonstandard LSP features (experimental capabilities).".to_string()),
        ("--ide-diagnostics".to_string(), Spec::Unit(Box::new(move || mode(m))), " Compute where IDE diagnostics (squiggles and dotted lines) will be displayed.".to_string()),
        ("--ide-signature-help".to_string(), Spec::Unit(Box::new(move || mode(m))), " Show signature help at the position indicated by `^ at-caret` comment.Exercises most of the functionality of textDocument/signatureHelp.".to_string()),
        ("--dump-classish-positions".to_string(), Spec::Unit(Box::new(move || mode(m))), " Dump certain positional information calculated for the given file.".to_string()),
        ("--identify-symbol".to_string(), Spec::Tuple(vec![Spec::Int(Box::new(move |_| Ok(()))), Spec::Int(Box::new(move |_| mode(m)))]), "<pos> Show info about symbol at given line and column".to_string()),
        ("--find-local".to_string(), Spec::Tuple(vec![Spec::Int(Box::new(move |_| Ok(()))), Spec::Int(Box::new(move |_| mode(m)))]), "<pos> Find all usages of local at given line and column".to_string()),
        ("--max-errors".to_string(), Spec::Int(Box::new(move |_| Ok(()))), " Maximum number of errors to display".to_string()),
        ("--outline".to_string(), Spec::Unit(Box::new(move || mode(m))), " Print file outline".to_string()),
        ("--outline-for-agents".to_string(), Spec::Unit(Box::new(move || mode(m))), " <file> (mode) outline the file, including line spans, to help agents efficiently navigate large files.".to_string()),
        ("--nast".to_string(), Spec::Unit(Box::new(move || mode(m))), " Print out the named AST".to_string()),
        ("--tast".to_string(), Spec::Unit(Box::new(move || mode(m))), " Print out the typed AST".to_string()),
        ("--infer-dynamic".to_string(), Spec::Unit(Box::new(move || mode(m))), " Infer types for dynamic locals".to_string()),
        ("--infer-dynamic-as-data".to_string(), Spec::Unit(Box::new(move || mode(m))), " Infer types for dynamic locals, interpreting indexed access as shapes/vecs".to_string()),
        ("--stripped-tast".to_string(), Spec::Unit(Box::new(move || mode(m))), " Print out the typed AST, stripped of type information. This can be compared against the named AST to look for holes.".to_string()),
        ("--find-refs".to_string(), Spec::Tuple(vec![Spec::Int(Box::new(move |_| Ok(()))), Spec::Int(Box::new(move |_| mode(m)))]), "<pos> Find all usages of a symbol at given line and column".to_string()),
        ("--go-to-impl".to_string(), Spec::Tuple(vec![Spec::Int(Box::new(move |_| Ok(()))), Spec::Int(Box::new(move |_| mode(m)))]), "<pos> Find all implementations of a symbol at given line and column".to_string()),
        ("--highlight-refs".to_string(), Spec::Tuple(vec![Spec::Int(Box::new(move |_| Ok(()))), Spec::Int(Box::new(move |_| mode(m)))]), "<pos> Highlight all usages of a symbol at given line and column".to_string()),
        ("--get-member".to_string(), Spec::String(Box::new(move |_| mode(m))), " Given ClassName::MemberName, fetch the decl of members with that name and print them.".to_string()),
        ("--log-inference-constraints".to_string(), Spec::Unit(Box::new(move || Ok(()))), " Log inference constraints to Scuba.".to_string()),
        ("--timeout".to_string(), Spec::Int(Box::new(move |_| Ok(()))), " Timeout in seconds for checking a function or a class.".to_string()),
        ("--hh-log-level".to_string(), Spec::Tuple(vec![Spec::String(Box::new(move |_| Ok(()))), Spec::Int(Box::new(move |_| Ok(())))]), " Set the log level for a key".to_string()),
        ("--batch-files".to_string(), Spec::Unit(Box::new(move || Ok(()))), " Typecheck each file passed in independently".to_string()),
        ("--skip-hierarchy-checks".to_string(), Spec::Unit(Box::new(move || Ok(()))), " Do not apply checks on class hierarchy (override, implements, etc)".to_string()),
        ("--skip-tast-checks".to_string(), Spec::Unit(Box::new(move || Ok(()))), " Do not apply checks using TAST visitors".to_string()),
        ("--skip-check-under-dynamic".to_string(), Spec::Unit(Box::new(move || Ok(()))), " Do not apply second check to functions and methods under dynamic assumptions".to_string()),
        ("--implicit-pess".to_string(), Spec::Unit(Box::new(move || Ok(()))), " Enables implicit pessimisation".to_string()),
        ("--explicit-pess".to_string(), Spec::String(Box::new(move |_| Ok(()))), " Enables checking explicitly pessimised files. Requires path to pessimised .hhi files ".to_string()),
        ("--enable-supportdyn-hint".to_string(), Spec::Unit(Box::new(move || Ok(()))), " Allow the supportdyn type hint".to_string()),
        ("--glean-reponame".to_string(), Spec::String(Box::new(move |_| Ok(()))), " glean repo name".to_string()),
        ("--disable-xhp-element-mangling".to_string(), Spec::Unit(Box::new(move || Ok(()))), " Disable mangling of XHP elements :foo. That is, :foo:bar is now \\foo\\bar, not xhp_foo__bar".to_string()),
        ("--keep-user-attributes".to_string(), Spec::Unit(Box::new(move || Ok(()))), " Keep user attributes when parsing decls".to_string()),
        ("--enable-xhp-class-modifier".to_string(), Spec::Unit(Box::new(move || Ok(()))), " Enable the XHP class modifier, xhp class name {} will define an xhp class.".to_string()),
        ("--allowed-fixme-codes-strict".to_string(), Spec::String(Box::new(move |_| Ok(()))), " List of fixmes that are allowed in strict mode.".to_string()),
        ("--allowed-decl-fixme-codes".to_string(), Spec::String(Box::new(move |_| Ok(()))), " List of fixmes that are allowed in declarations.".to_string()),
        ("--report-pos-from-reason".to_string(), Spec::Unit(Box::new(move || Ok(()))), " Flag errors whose position is derived from reason information in types.".to_string()),
        ("--consider-type-const-enforceable".to_string(), Spec::Unit(Box::new(move || Ok(()))), " Consider type constants to potentially be enforceable.".to_string()),
        ("--interpret-soft-types-as-like-types".to_string(), Spec::Unit(Box::new(move || Ok(()))), " Types declared with <<__Soft>> (runtime logs but doesn't throw) become like types.".to_string()),
        ("--meth-caller-only-public-visibility".to_string(), Spec::Bool(Box::new(move |_| Ok(()))), " Controls whether meth_caller can be used on non-public methods".to_string()),
        ("--hover".to_string(), Spec::Tuple(vec![Spec::Int(Box::new(move |_| Ok(()))), Spec::Int(Box::new(move |_| mode(m)))]), "<pos> Display hover tooltip".to_string()),
        ("--hover-at-caret".to_string(), Spec::Unit(Box::new(move || mode(m))), " Show the hover information indicated by // ^ hover-at-caret".to_string()),
        ("--enforcement".to_string(), Spec::Tuple(vec![Spec::Int(Box::new(move |_| Ok(()))), Spec::Int(Box::new(move |_| mode(m)))]), "<pos> Display enforcement at position".to_string()),
        ("--enforcement-at-caret".to_string(), Spec::Unit(Box::new(move || mode(m))), " Show the enforcement indicated by // ^ enforcement-at-caret".to_string()),
        ("--enforcement-at-caret-batch".to_string(), Spec::Unit(Box::new(move || mode(m))), " Show enforcement at all // ^ enforcement-at-caret positions".to_string()),
        ("--fix".to_string(), Spec::Unit(Box::new(move || mode(m))), " Apply quickfixes for all the errors in the file, and print the resulting code. Prefer --ide-code-actions, which tests more.".to_string()),
        ("--custom-hhi-path".to_string(), Spec::String(Box::new(move |_| Ok(()))), " Use custom hhis".to_string()),
        ("--force-allow-builtins-in-custom-hhi-path-FLAKEY".to_string(), Spec::Unit(Box::new(move || Ok(()))), " (FLAKEY) allow builtins to be written into the custom hhi path".to_string()),
        ("--explicit-consistent-constructors".to_string(), Spec::Int(Box::new(move |_| Ok(()))), " Raise an error for <<__ConsistentConstruct>> without an explicit constructor; 1 for traits, 2 for all ".to_string()),
        ("--require-types-class-consts".to_string(), Spec::Int(Box::new(move |_| Ok(()))), " Raise an error for class constants missing types; 1 for abstract constants, 2 for all ".to_string()),
        ("--profile-type-check-twice".to_string(), Spec::Unit(Box::new(move || Ok(()))), " Typecheck the file twice".to_string()),
        ("--profile-type-check-multi".to_string(), Spec::Int(Box::new(move |_| Ok(()))), " Typecheck the files n times extra (!)".to_string()),
        ("--profile-top-level-definitions".to_string(), Spec::Unit(Box::new(move || Ok(()))), " Profile typechecking of top-level definitions".to_string()),
        ("--memtrace".to_string(), Spec::String(Box::new(move |_| Ok(()))), " Write memtrace to this file (typical extension .ctf)".to_string()),
        ("--type-printer-fuel".to_string(), Spec::Int(Box::new(move |_| Ok(()))), " Sets the amount of fuel that the type printer can use to display an individual type. Default: 100".to_string()),
        ("--enable-global-access-check".to_string(), Spec::Unit(Box::new(move || Ok(()))), " Run global access checker to check global writes and reads".to_string()),
        ("--overwrite-loop-iteration-upper-bound".to_string(), Spec::Int(Box::new(move |_| Ok(()))), " Sets the maximum number of iterations that will be used to typecheck loops".to_string()),
        ("--remove-dead-unsafe-casts".to_string(), Spec::Unit(Box::new(move || mode(m))), " Removes dead unsafe casts from a file".to_string()),
        ("--count-imprecise-types".to_string(), Spec::Unit(Box::new(move || mode(m))), " Counts the number of mixed, dynamic, and nonnull types in a file".to_string()),
        ("--custom-error-config-path".to_string(), Spec::String(Box::new(move |_| Ok(()))), " Config file for custom error messages".to_string()),
        ("--map-reduce".to_string(), Spec::Unit(Box::new(move || mode(m))), " Run the map reducers and print the result".to_string()),
    ];
    let mut options = ocaml_arg::align(options, Some(25));
    let usage = format!("Usage: {} filename\n", argv0);
    let mut argv = vec![argv0.to_string()];
    argv.extend(args.iter().cloned());
    let mut anon = |_: String| -> ocaml_arg::Res { Ok(()) };
    let _ = ocaml_arg::parse(&argv, &mut options, &mut anon, &usage);
}
