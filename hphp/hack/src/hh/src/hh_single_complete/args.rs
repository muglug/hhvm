// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! The option table of `parse_options` of `hh_single_complete.ml`, for
//! `Arg.parse` (`crate::rt::ocaml_arg`): every option the OCaml accepts, with
//! its kind of argument and its documentation, in its order, so that an
//! unknown option, a missing or wrong argument, a second mode and `--help`
//! are reported as the OCaml's `Arg` reports them (on stderr, exit 2; the
//! help on stdout, exit 0), and `set "manifold api key"` raises its
//! `Failure` from inside `Arg.parse`. The options themselves are interpreted
//! by `hh_single_cli.rs`, after this validation; the functions here only
//! check the modes and the options that may be set once.

use std::cell::Cell;

use crate::rt::ocaml_arg;
use crate::rt::ocaml_arg::Exn;
use crate::rt::ocaml_arg::Spec;
use crate::rt::ocaml_exn::Uncaught;

type Res = Result<(), Exn<Uncaught>>;

/// `set_mode x ()`: `raise (Arg.Bad "only a single mode should be specified")`
/// when a mode is already set.
fn set_mode(m: &Cell<bool>) -> Res {
    if m.get() {
        Err(Exn::Bad("only a single mode should be specified".to_string()))
    } else {
        m.set(true);
        Ok(())
    }
}

/// `set name reference value`: `failwith "Attempted to set NAME twice"` when
/// the option was already given.
fn set(name: &str, reference: &Cell<bool>) -> Res {
    if reference.get() {
        Err(Exn::Raise(Uncaught::failure(format!(
            "Attempted to set {} twice",
            name
        ))))
    } else {
        reference.set(true);
        Ok(())
    }
}

/// `Arg.parse (Arg.align ~limit:25 options) anon usage` over `args` (the
/// arguments after the program name `argv0`): prints and exits as the OCaml
/// does on an error or on `--help`; an exception raised by an option (a
/// `Failure`) is returned.
pub fn parse_options(argv0: &str, args: &[String]) -> Result<(), Uncaught> {
    let mode_set = Cell::new(false);
    let m = &mode_set;
    let manifold_api_key_set = Cell::new(false);
    let k = &manifold_api_key_set;
    let mode = |m: &Cell<bool>| set_mode(m);
    let ok = || -> Res { Ok(()) };
    let options: ocaml_arg::Speclist<'_, Uncaught> = vec![
        ("--extra-builtin".to_string(), Spec::String(Box::new(move |_| ok())), " HHI file to parse and declare".to_string()),
        ("--no-builtins".to_string(), Spec::Unit(Box::new(move || ok())), " Don't use builtins (e.g. ConstSet); implied by --root".to_string()),
        ("--disable-xhp-element-mangling".to_string(), Spec::Unit(Box::new(move || ok())), "Disable mangling of XHP elements :foo. That is, :foo:bar is now \\foo\\bar, not xhp_foo__bar".to_string()),
        ("--disable-xhp-children-declarations".to_string(), Spec::Unit(Box::new(move || ok())), "Disable XHP children declarations, e.g. children (foo, bar+)".to_string()),
        ("--enable-xhp-class-modifier".to_string(), Spec::Unit(Box::new(move || ok())), "Enable the XHP class modifier, xhp class name {} will define an xhp class.".to_string()),
        ("--auto-namespace-map".to_string(), Spec::String(Box::new(move |_| ok())), " Alias namespaces".to_string()),
        ("--auto-complete".to_string(), Spec::Unit(Box::new(move || mode(m))), " Produce autocomplete suggestions as if triggered by trigger character".to_string()),
        ("--hh-log-level".to_string(), Spec::Tuple(vec![Spec::String(Box::new(move |_| ok())), Spec::Int(Box::new(move |_| ok()))]), " Set the log level for a key".to_string()),
        ("--auto-complete-manually-invoked".to_string(), Spec::Unit(Box::new(move || mode(m))), " Produce autocomplete suggestions as if manually triggered by user".to_string()),
        ("--auto-complete-show-glean".to_string(), Spec::Unit(Box::new(move || mode(m))), " Show the glean query for the prefix contained in the file".to_string()),
        ("--auto-complete-glean".to_string(), Spec::Unit(Box::new(move || mode(m))), " Show the glean query for the prefix contained in the file, and run that query".to_string()),
        ("--search-show-glean".to_string(), Spec::Unit(Box::new(move || mode(m))), " Show the glean query for newline-separated queries in file".to_string()),
        ("--search-glean".to_string(), Spec::Unit(Box::new(move || mode(m))), " Show+run the glean query for newline-separated queries in file".to_string()),
        ("--search".to_string(), Spec::Unit(Box::new(move || mode(m))), " Run the search (including new definitions) for newline-separated queries in file".to_string()),
        ("--find-refs-show-glean".to_string(), Spec::Unit(Box::new(move || mode(m))), " Show the glean query for newline-separated queries in file".to_string()),
        ("--find-refs-glean".to_string(), Spec::Unit(Box::new(move || mode(m))), " Show+run the glean query for newline-separated queries in file".to_string()),
        ("--manifold-api-key".to_string(), Spec::String(Box::new(move |_| set("manifold api key", k))), " API key used to download a saved state from Manifold (optional)".to_string()),
        ("--naming-table".to_string(), Spec::String(Box::new(move |_| ok())), " Naming table, to typecheck undefined symbols; needs --root. (Hint: buck2 run //hphp/hack/src/hh_naming_table_builder)".to_string()),
        ("--resolve".to_string(), Spec::Unit(Box::new(move || mode(m))), " Produce what is returned from Completion_resolve requests - including signature and docblock".to_string()),
        ("--xhp-close".to_string(), Spec::Unit(Box::new(move || mode(m))), " Produce what is returned from AutoClose requests, aka the closing xhp tag".to_string()),
        ("--root".to_string(), Spec::String(Box::new(move |_| ok())), " Root for where to typecheck undefined symbols; needs --naming-table".to_string()),
        ("--glean-reponame".to_string(), Spec::String(Box::new(move |_| ok())), " Glean repo for autocompleting undefined symbols".to_string()),
    ];
    let mut options = ocaml_arg::align(options, Some(25));
    let usage = format!("Usage: {} filename\n", argv0);
    let mut argv = vec![argv0.to_string()];
    argv.extend(args.iter().cloned());
    let mut anon = |_: String| -> Res { Ok(()) };
    ocaml_arg::parse(&argv, &mut options, &mut anon, &usage)
}
