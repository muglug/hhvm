# Porting the typechecker from OCaml to Rust

The OCaml typechecker (`hphp/hack/src/**/*.ml`) is being ported into this crate
(`hh`). The OCaml is no longer built; it is the specification. Many people port
different modules at the same time, so the port follows fixed rules: two people
who port a caller and its callee independently must end up with code that fits.

## The one rule

**Transliterate.** Port each OCaml module to one Rust module that has the same
functions, with the same names, doing the same thing in the same order, raising
the same errors with the same positions. Do not redesign, merge, simplify or
"improve" while porting, and do not skip branches you think are rare. Outputs
are compared with the OCaml typechecker's byte for byte, and behaviour that
looks accidental in the OCaml is still the behaviour.

When something cannot be ported yet (it needs a module nobody has written),
leave `todo!("Module.function: <what is missing>")` in that branch, never a
guess or a silent default.

## Where things go

| OCaml | Rust |
|---|---|
| module `Foo_bar` (`foo_bar.ml`, any directory) | `crate::foo_bar`, file `hh/src/foo_bar.rs` |
| submodule `Foo_bar.Baz` | `pub mod baz` inside `foo_bar.rs` (or `foo_bar/baz.rs`) |
| function / value `some_name` | `some_name` (prefix `r#` or append `_` only for Rust keywords: `fun_`, `class_`, `type_`, `match_`) |
| type `t` of module `Foo_bar` | `foo_bar::T` |
| other types `some_type` | `SomeType` |
| constructors, record fields | same names (`Tclass`, `ft_params` → keep the OCaml field name without inventing a new one) |

The crate is flat on purpose: it mirrors OCaml's flat module namespace, so the
Rust path of anything is known from its OCaml name without looking it up.
Register a new module in `hh/src/lib.rs` (keep the list sorted; add only your
own lines).

A module's public surface is what its `.mli` exports (everything, if there is
no `.mli`).

## Signatures

- **Labelled and optional arguments** become ordinary positional parameters in
  the order they are declared in the `.mli` (or the `let`); optional arguments
  become `Option<T>` (pass `None` for the default, and apply the default inside
  the function).
- **The typing environment** (`Typing_env_types.env`) is `&mut Env`
  (`crate::typing_env_types::Env`), always the first parameter where OCaml has
  it first. A function that returns `(env, x)` returns `x`; one that returns
  `env` returns `()`. Functions that only read the environment take `&Env`.
  See "The environment" below: this is where most porting mistakes happen.
- **Other threaded state** follows the same rule (`Typing_inference_env.t`
  etc.: `&mut T` in, the non-state part of the result out).
- **Values** are passed by reference when the callee only reads them (`&Ty`,
  `&Pos`, `&[T]`, `&str`) and by value when it stores or returns them. Return
  owned values.
- **`'a option`** → `Option<T>`; **lists** → `Vec<T>` (`&[T]` as parameters);
  **tuples** → tuples; **`ref`** in a record → `Rc<RefCell<T>>` only if it is
  really shared, otherwise a plain field.
- **`'a Lazy.t`**: three wrappers exist; use the one of the type you build:
  `crate::typing_error::Lazy<T>` in typing errors (`Rc`-based, memoised;
  `Lazy::new(move || e)`, `.force()`), `crate::folded_class::Lazy<T>` in class
  elements (`Arc<LazyLock>`), `crate::typing_warning::Lazy` in warnings. For
  a lazy value of your own, compute it eagerly when that is cheap and has no
  effect (no error reported, no dependency recorded, no environment change);
  otherwise keep it lazy (`std::cell::LazyCell`, or `typing_error::Lazy`).
- **Physical equality** (`phys_equal`): inferred types and constraint types
  share their node through an `Rc` (`Ty(Reason, Rc<Ty_>)`), so cloning a type
  is cheap and keeps its identity, as in OCaml. Port `phys_equal t1 t2` on
  types as `typing_defs_core::phys_equal(&t1, &t2)` (and
  `typing_defs_constraints::phys_equal_constraint_type` /
  `phys_equal_internal_type`), never as `==` (which is `ty_compare` and
  ignores reasons): several of these checks change what is reported. For this
  to work, return `ty.clone()` (not a rebuilt type) wherever OCaml returns the
  same value. Build types with `mk`; to change a node, `Rc::unwrap_or_clone`
  it. On other values, `phys_equal` that only skips work ("nothing changed")
  may become `==` or be dropped; anything else, keep the OCaml outcome and say
  how in your report.
- **Maps and sets** that the OCaml copies freely (`SMap`, `IMap`, `SSet`,
  `Local_id.Map`, `Typing_set`...) → persistent collections from the `im`
  crate (`im::OrdMap`, `im::OrdSet`) so that clones stay cheap and iteration
  order matches OCaml's ordered maps. Use `Vec`/`BTreeMap` for collections
  that are built once and read.
- **Exceptions** become `Result`s wherever that is practical: an exception
  with a handler (`try ... with`) is a `Result<_, E>` with a small error type
  named after it, returned with `?` through the functions between the raise
  and the handler. This is the rule for all new code and for the server
  layer. `panic_any` + `catch_unwind` is kept only for the exceptions of the
  typing core that are raised deep inside inference and handled at the top
  (`typing_inference_env::InconsistentTypeVarState`,
  `decl_defs::DeclNotFound`, timeouts, `typing_deps::DepgraphUnavailable`),
  until the signatures in between are converted. A panic that is caught
  costs an unwind and prints through the panic hook, so never use one for
  something that happens in normal operation. `failwith`/`assert false` on
  "cannot happen" paths become `panic!` with the same message.
- **Higher-order arguments** are `impl Fn`/`impl FnMut` (or `&mut dyn FnMut`
  when the function is recursive or stored).

## What already exists

Read the source of a module before you call it, and use its real signatures.
These are ported (a few are being finished; their API is settled):

| Area | Modules (`crate::...`) |
|---|---|
| environment | `typing_env_types` (the `Env`, `Genv`, `LocalEnv` records), `typing_env` (everything in `typing_env.mli`, and `typing_env::deps` for `Deps`), `typing_lenv`, `typing_per_cont_env`, `typing_per_cont_ops`, `typing_continuations`, `typing_fake_members`, `typing_local_types`, `typing_env_return_info`, `decl_env` |
| inference | `typing_inference_env`, `type_parameter_env`, `type_parameter_env_ops`, `typing_kinding_defs`, `typing_tyvar_occurrences`, `typing_set`, `internal_type_set`, `typing_logic`, `typing_logic_helpers`, `tvid`, `expression_id`, `ident_provider` |
| types | `typing_defs_core`, `typing_defs`, `typing_defs_constraints`, `typing_defs_flags`, `typing_make_type`, `type_mapper`, `type_mapper_generic`, `type_visitor`, `type_force_lazy_values`, `tany_sentinel`, `typing_cont_key`, `tast` |
| reasons and printing | `typing_reason`, `typing_print` (`PrintEnv` is implemented for `Env`), `typing_log_value` |
| errors | `typing_error` (the data), `typing_error_utils` (`add_typing_error`), `diagnostics_state` (the stateful `Diagnostics` API, fixmes), `typing_warning`, `typing_warning_utils`, `naming_errors` (rendering of naming and NAST-check errors; `naming_errors::render` has `strip_ns`, `md_codify`, `suggestion_message`, `highlight_differences`) |
| declarations | `folded_class` (the `Cls` API and `ClassElt`), `decl_provider`, `decl_entry`, `decl_subst`, `decl_instantiate`, `decl_utils`, `decl_enum`, `decl_hint`, `decl_enforceability`, `decl_class`, `decl_members`, `decl_counters`, `typing_class_types`, `typing_deps` |
| utilities | `utils`, `string_utils`, `markdown_lite`, `render`, `pos`, `pos_or_decl`, `relative_path`, `local_id`, `quickfix`, `ast_defs`, `exception`, `telemetry`, `hh_logger`, `hack_event_logger`, `typechecker_options` |
| NAST checks | `nast_check` (with `nast_check::nast_visitor`, `nast_check_env`, `stateful_aast_visitor`, `nast_init_check`, `decl_init_check`) |
| naming | the `elab` crate (`hphp/hack/src/elab`); `crate::naming` gives it the OCaml interface (`Naming.fun_def`, `class_`, `typedef`, `global_const`, `module_`, `fun_def_of_stmts`), `crate::package_provider`, `crate::multifile` |

`typing.ml` and `typing_subtype.ml` are split between many people along their
recursive modules. Their layout is fixed in `hh/src/typing/mod.rs` and
`hh/src/typing_subtype/mod.rs`: read the one that concerns you before writing
into it or calling into it.

## Types that already exist

| OCaml | Rust |
|---|---|
| `Pos.t`, `Pos_or_decl.t` | `oxidized::pos::Pos`, `oxidized::pos_or_decl::PosOrDecl` (the same type); the functions `oxidized` lacks are in `crate::pos` / `crate::pos_or_decl` |
| `Relative_path.t` | `relative_path::RelativePath` (in an `Arc` where shared); functions in `crate::relative_path` |
| `Aast`, `Nast` | `oxidized::aast`, `oxidized::nast` |
| `Tast` (AST annotated with types) | `crate::tast` (port of `tast.ml`: `oxidized::aast` instantiated with `Ty`) |
| `Ast_defs`, `Aast_defs` | `oxidized::ast_defs`, `oxidized::aast_defs` |
| `Local_id.t` | `oxidized::local_id::LocalId`; functions in `crate::local_id` |
| `Typing_defs.locl_ty`, `locl_phase ty_`, `locl_fun_type`, ... (inferred types) | `crate::typing_defs_core::{Ty, Ty_, FunType, ...}`: defined in the crate. **`oxidized` only has the declared phase** (no `Tvar`, `Tclass`, `Tnewtype`, ...): never use `oxidized::typing_defs_core::Ty` for an inferred type |
| `Typing_reason.t` | `crate::typing_reason::T` (the full reason type; `oxidized::typing_reason` has declared-phase reasons only). It is `Rc<T_>`, a shared handle that is cheap to clone, as in OCaml: build reasons with the `typing_reason` constructor functions, pass `r.clone()` (never a copy of `*r`), match with `match &**r { T_::Flow { .. } => .. }` |
| `Typing_defs.decl_ty` and all decl data | `ty::decl::Ty<BReason>` and friends from `hphp/hack/src/hackrs/ty` (`crate::ctx::R` is `BReason`; `crate::typing_defs_core::DeclTy` etc. are aliases); `to_oxidized()` gives the oxidized form when a function needs it |
| folded class (`Folded_class.t`, `Cls`) | `crate::folded_class::T` (wraps `ty::decl::FoldedClass<R>`) |
| `Typechecker_options.t`, `Global_options.t`, `Parser_options.t` | `oxidized::typechecker_options::TypecheckerOptions` (= `GlobalOptions`), ...; the accessor functions are in `crate::typechecker_options` |
| `Message.t` | `oxidized::message::Message<P>` (its text is a `bstr::BString`) |
| `Provider_context.t` (`ctx`) | `std::sync::Arc<crate::ctx::Ctx>` |
| naming / nast-check / parsing errors | `oxidized::naming_error`, `nast_check_error`, `parsing_error`; rendered by `crate::naming_errors` |
| `Naming_special_names` (`SN`) | `naming_special_names_rust` |
| `Diagnostics.diagnostic` | `oxidized::diagnostics::Diagnostic` |
| error codes | `oxidized::error_codes` |

**Read the definition before you match on a type; never guess a constructor or
field name.** Two naming styles exist among the types already ported, and both
are settled:

- The types of `typing_defs_core`, `typing_defs`, `typing_reason` and anything
  else that mirrors `oxidized` follow the `oxidized` style: constructors in
  camel case (`TvecOrDict`, `TclassPtr`), record fields without the prefix the
  OCaml fields share (`ft_params` is `ft.params`, `fp_type` is `fp.type_`).
- The error and warning types (`typing_error`, `typing_warning`) have
  constructors in the UpperCamelCase of their OCaml names (`Unify_error` is
  `UnifyError`, the tag `` `read `` is `Read`) and the OCaml spelling of
  fields (`SubtypingError { ty_sub, .. }`), with a trailing `_` on Rust
  keywords.

New types that you define follow the first style.

`oxidized` types mirror the OCaml definitions field for field. Do not edit
`oxidized` or `hackrs` to suit a port; if a definition is missing or differs
from the OCaml you are reading, write the function you need in the module that
OCaml has it in, and report the gap.

## State that OCaml keeps globally

- **Errors** (`Diagnostics.add_diagnostic`, `try_`, `do_`, `ignore_`, ...):
  `crate::diagnostics_state` keeps the same state per thread (one file is
  checked on one thread). Call the functions with the OCaml names; never
  collect errors some other way.
- **Typing errors** are values of `crate::typing_error::T`, reported with
  `crate::typing_error_utils::add_typing_error(err, env)`, exactly as in OCaml.
  Do not format messages at the place an error is raised.
- **Dependencies** (`Typing_deps.add_idep` and friends): call
  `crate::typing_deps` with the same arguments. They feed incremental checking
  and saved states.
- **Counters and fresh identifiers** (`Ident_provider`, `Tvid`, expression
  ids): the providers live where OCaml has them (in the environment).
- **Options** are read from the environment or the context, as in OCaml.

## The environment

OCaml threads the environment as a value: every function takes one and returns
a new one, and the old one stays valid. Here there is one `Env`, mutated in
place. The two agree only if every old environment that OCaml goes on using is
saved before it is changed. Check each `env` binding of the code you port
against this table:

| OCaml | Rust |
|---|---|
| `let (env, x) = f env in let (env, y) = g env x in (env, y)` | `let x = f(env); g(env, x)` |
| `let (_env, x) = f env in ...` or `let (_, x) = f env` (the new environment is dropped) | `let x = f(&mut env.clone());` |
| `let (env1, x) = f env in let (env2, y) = g env in ... env1 ... env2` (two environments from the same one, e.g. the branches of a conditional) | `let saved = env.clone(); let x = f(env); let mut env2 = saved; let y = g(&mut env2);`, then merge or pick as the OCaml does, ending with the right one in `*env` |
| `let (env, x) = f env in ... (old_env, z)` (returns an earlier environment) | save `old_env` with `clone()` at the point OCaml names it; finish with `*env = old_env;` |
| `List.fold_left l ~init:(env, acc) ~f:(fun (env, acc) x -> ...)` | a `for` loop over `l` that mutates `env` |
| `List.map_env env l ~f` (and `_env` / `fold_env` variants) | `l.iter().map(\|x\| f(env, x)).collect::<Vec<_>>()` (left to right, like OCaml) |
| `Typing_lenv` / continuation save and restore | the `typing_lenv` / `typing_per_cont_env` functions, as in OCaml |

`Env` is cheap to clone (its collections are persistent), so clone whenever
the OCaml keeps an environment; never reason that "it probably does not
matter".

## Evaluation order

OCaml evaluates the arguments of a call, the components of a tuple, the fields
of a record and the elements of a list literal **from right to left**; Rust
evaluates them from left to right. When more than one of them has an effect,
the order is observable: a fresh type variable takes the next number (it shows
in messages as `#3`, and orders sets of types), an error is reported, a
dependency is recorded, the environment changes, or a lazy value that does any
of these is forced. In that case bind them to variables first, the last one
first:

```rust
// OCaml: f (fresh_tyvar env p1) (fresh_tyvar env p2)
let b = fresh_tyvar(env, p2);
let a = fresh_tyvar(env, p1);
f(a, b)
```

Sequenced `let ... in` bindings already have an explicit order; this concerns
only several effectful expressions inside one call, tuple, record or list.

## Speculation (`Diagnostics.try_` and friends)

OCaml tries something and falls back when it reports an error:
`Diagnostics.try_ (fun () -> f1 env) (fun err -> f2 env)`. Two things do not
carry over by themselves:

- Both closures need the environment, which the borrow checker does not allow.
  Return the error from the handler and act on it afterwards (the module
  documentation of `crate::diagnostics_state` shows the pattern with
  `try_with_result`).
- In OCaml the fallback runs with the environment as it was *before* the
  attempt, because the attempt only produced a new value. Here the attempt
  mutated `env`. So clone the environment before the attempt and restore it
  (`*env = saved;`) on the fallback path, whenever the OCaml fallback uses the
  old `env`. The same holds for every other place where OCaml drops the
  environment an attempt returned.

```rust
let saved = env.clone();
match diagnostics_state::try_with_result(|| Ok(f1(env)), |_, err| Err(err)) {
    Ok(x) => x,
    Err(err) => {
        *env = saved;
        f2(env, err)
    }
}
```

## Working in the shared tree

Everybody works in the same checkout and the same cargo target directory.

- Edit only the files you were given. Never revert, reformat or "fix" someone
  else's file, and never run a git command that changes anything.
- Modules being ported are registered in `hh/src/lib.rs` behind the cargo
  feature `port`, and their files already exist (empty). You do not need to
  touch `lib.rs`. Without the feature the crate builds as before, which other
  people rely on to run tests, so never register a module outside the feature.
- `cd hphp/hack/src && CARGO_TARGET_DIR=../../../_build/rust cargo +nightly check --release -p hh --features port --message-format=short 2>&1 | grep 'hh/src/<your_file>'`
  shows the errors of your file. Errors in other files are not yours: other
  modules are mid-port. Your file must have none when you finish (other than
  calls into modules that are still empty, which you list), and should not
  have syntax errors for more than a moment (a file that does not parse stops
  the check of every other file).
- A crate module named after an OCaml module whose *types* already exist in
  `oxidized` re-exports them (`pub use oxidized::typing_defs_core::*;` in
  `crate::typing_defs_core`), so `crate::<ocaml module>::<Type>` always works.
- `hh/Cargo.toml` already has `im`, `itertools`, `indexmap` and the common
  in-tree crates. If you need another dependency, add one line to it (re-read
  the file first: others add lines too).
- If you call a function of a module that does not exist yet, call it by the
  name these rules give it. Do not create or stub another person's module; do
  list what you called that did not exist. Exception: a small OCaml utility
  module from outside `typing/`, `decl/`, `naming/`, `providers/` and `lints/`
  that has no Rust module yet, and that you need, you may port (the functions
  you need, each in full) under its OCaml name and register behind `port` in
  `lib.rs` (re-read `lib.rs` just before the edit; add only your line). If it
  already exists, add the functions you need without changing what is there.
- If a signature in someone else's module does not suit your call, adapt your
  call. If it is wrong by these rules, report it; do not change it.
- Release profile and the existing target directory only. Do not build
  scratch crates outside the tree (disk space, and contention on the target
  directory): the `port` build does not compile as a whole until the modules
  are integrated, so verify your files with the check command (no errors in
  them other than names that other people are still writing) and with the
  coverage tool below. Write `#[cfg(test)]` tests for logic that stands on its
  own; they run once the port builds.
- `python3 hh/tools/port_coverage.py <ocaml file>[:<first>-<last>] <your .rs files or directories>`
  lists the OCaml definitions that have no Rust function of the same name, and
  the OCaml string literals (split at `%s`-style conversions) that do not
  appear in your Rust. Run it before you report: both lists should be empty,
  or each remaining item explained.

## Report

When you finish, say: which functions are ported in full; which contain
`todo!` and what each waits for; what you called that did not exist yet; every
place where the OCaml and the existing Rust types disagreed; and anything you
verified by running versus by reading.

## The server layer (feature `server`)

`hh_server`, `hh_client`, saved states, incremental rechecking and the IDE are
ported under the same rules, with these additions. The design they follow is
given with each assignment.

- The server layer is compiled with the cargo feature `server`
  (`#[cfg(feature = "server")]` in `lib.rs`), which implies `port` (the
  incremental daemon needs the typechecker); typing, naming and decl modules
  stay behind `port`, so that `port` alone still builds `hh` as before. The
  utility modules `string_utils`, `exception`, `utils`, `wrapped_map`,
  `s_map`, `s_set`, `i_map`, `i_set`, `yojson`, `telemetry`, `hh_logger`,
  `relative_path`, `path`, `sys_utils`, `tty`, `pos`, `pos_or_decl`,
  `quickfix`, `markdown_lite`, `error_codes`, `user_diagnostic`,
  `diagnostics_state`, `find_utils`, `files_to_ignore`, `hack_event_logger`
  and `typechecker_options` are compiled
  with either feature (`#[cfg(any(feature = "port", feature = "server"))]`), so
  what you add to one of them must not use anything that is behind `port`
  alone.
- The `server` build has a target directory of its own:
  `cd hphp/hack/src && CARGO_TARGET_DIR=../../../_build/rust-server cargo +nightly check --release -p hh --features server --message-format=short`,
  and `cargo +nightly test --release -p hh --features server --lib <module>`
  (same target directory) runs your tests. Unlike the `port` build, the
  `server` build compiles as a whole: leave no errors in your files, and do not
  fix other people's (report them).
- Infrastructure that has no OCaml counterpart (the process model, the socket
  protocol, file-watcher backends, the emulation of OCaml's `Arg`) goes in
  `hh/src/rt/` (`crate::rt::<name>`), so that its names cannot collide with
  OCaml module names. Register it in `hh/src/rt/mod.rs` (add only your lines).
- Binaries go in `hh/src/bin/<name>.rs`, declared in `hh/Cargo.toml` with
  `required-features = ["server"]`.
- When you need the *types* of a module that a later assignment of the
  server layer owns (an RPC command's argument or result type, say), port
  those type definitions, in full, in that module's file (create and register
  it if needed), and say at the top of the file that only the types are
  ported so far and by whom. The later assignment completes the module and
  keeps the types. Never import a module that does not exist: the `server`
  build must compile at every moment, because everyone tests with it. An
  action whose code belongs to a later assignment fails loudly
  (`todo!("Module.function: <what is missing>")`).
- What can be seen from outside the process stays exactly as in the OCaml:
  command lines and `--help` text, output formats, exit codes, the files under
  `/tmp/hh_server` and their formats, the naming-table schema, the saved-state
  layout. What the OCaml does with forked processes, shared memory and
  marshalling is redesigned (one process, threads, a socket protocol of our
  own), but the decisions it takes (what to recheck, when to answer, which
  message to print, which exit code to use) are transliterated.
- Test suites under `hphp/hack/test/` that need a binary run against the Rust
  binaries: say in your report which ones you ran, how, and with what result.
