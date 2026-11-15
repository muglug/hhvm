# CLAUDE.md — Hack Typechecker

This covers the Hack frontend: parser, typechecker (`hh_server`/`hh_client`), bytecode emitter, and associated tooling. Written in OCaml and Rust, built with dune.

**This branch builds two Hack typecheckers side by side**: the OCaml one described below and a Rust port of it (`src/hh`), which is meant to be a drop-in replacement: same command lines, same output, same exit codes, same files. See "The Rust typechecker" below. The OCaml sources are also the reference the Rust port follows; do not delete them.

## Build

The top-level CMake target `hack` builds everything via CMake which invokes dune. From the repo root:

```bash
cmake --build ./_build --target hack
```

Main executables: `hh_server`, `hh_client`, `hh_single_type_check`, `hh_single_complete`, `hh_single_ide_format`, `hh_parse`, `hackfmt`, `generate_full_fidelity`.

### Rust integration

Rust crates live under `src/` alongside OCaml (workspace root: `src/Cargo.toml` with 100+ crates). Dune invokes Cargo via `scripts/invoke_cargo.sh`. The `ocamlrep` library marshals types between OCaml and Rust. Generated Rust type equivalents live in `src/oxidized/`.

## The Rust typechecker (`src/hh`)

Built by cargo alone (nightly toolchain): it needs no OCaml, opam or dune, and neither does what HHVM links (the parser and `hackc`, through `cxx`).

```bash
# Both typecheckers, the formatters and the FFI bridge HHVM links (not part of `all`)
cmake --build ./_build --target hack

# Only the Rust typechecker (copied to <build>/hphp/hack/bin/: hh, hh_server_rust, hh_client_rust)
cmake --build ./_build --target hh

# Directly with cargo
cd hphp/hack/src && cargo +nightly build --release -p hh --features server \
  --bin hh --bin hh_server_rust --bin hh_client_rust
cd hphp/hack/src && cargo +nightly build --release -p hackfmt   # installed as hackfmt_rust
```

The OCaml build is controlled by the CMake option `BUILD_HACK_OCAML` (default `ON`): it adds the `hack_dune` targets (opam switch set up by `opam_setup.sh`, then dune), and `hack` depends on them. With `-DBUILD_HACK_OCAML=OFF` nothing needs OCaml, opam or dune.

| Binary           | Source                        | What it is                                                                           |
| ---------------- | ----------------------------- | ------------------------------------------------------------------------------------ |
| `hh`             | `src/hh/src/main.rs`          | `hh check ROOT` (batch check), `hh single` (= `hh_single_type_check`), `hh single-complete` (= `hh_single_complete`) |
| `hh_server_rust` | `src/hh/src/bin/hh_server.rs` | the command line of `hh_server`: `--check [--json] ROOT`, the daemon with its monitor |
| `hh_client_rust` | `src/hh/src/bin/hh_client.rs` | the command line of `hh_client`: `check`, `start`, `stop`, `restart`, `lsp`, ...     |
| `hh_dispatch`    | `src/hh/src/bin/hh_dispatch.rs` | installed as `hh_client` and `hh_server`: runs the OCaml or the Rust one (below)      |
| `hackfmt_rust`   | `src/hackfmt/rust/`           | the formatter: the command line of `hackfmt.ml`, the output of `hakana format` (`--hackfmt-compat` for OCaml's) |

The client and server carry the `_rust` suffix so that they install next to the OCaml `hh_client`/`hh_server`; each finds its siblings by its own suffix (`src/hh/src/rt/exe_suffix.rs`). What they print ("hh_server", "hh_client" in usage and logs) is the OCaml's.

`cmake --install` puts the OCaml client and server in as `hh_client_ocaml`/`hh_server_ocaml`, and `hh_dispatch` as `hh_client` and `hh_server`. It execs the `_ocaml` or `_rust` binary next to it, using the first of these that is set: `--typechecker-implementation=ocaml|rust` (removed from the arguments), `$HH_TYPECHECKER_IMPLEMENTATION`, `typechecker_implementation = ocaml|rust` in the root's `.hhconfig`, else `ocaml` (`rust` when the OCaml binary is not installed). It exports the choice in `$HH_TYPECHECKER_IMPLEMENTATION`, so the server a client starts is of the same implementation (`src/hh/src/typechecker_implementation.rs`). The build directory's `bin/hh_client` and `bin/hh_server` stay the OCaml binaries.

Cargo features of the `hh` crate: none = a placeholder checker only; `port` = the typechecker; `server` (implies `port`) = everything below. All binaries are built with `server`.

- The typechecker: parsing and lowering, naming, declarations and folding (with `hackrs/`), typing, NAST and TAST checks, linters, error formatting in every `--error-format`.
- `hh single` / `hh single-complete`: every mode of `hh_single_type_check` and `hh_single_complete` (errors, `--batch-files`, `--tast`, `--nast`, hover, identify-symbol, find-refs, code actions, lint, ...), with the OCaml's option table, messages and exit codes.
- `hh_server_rust`: the batch check (what CI runs), and the daemon: monitor, incremental recheck on file changes (watchman), saved states (`--save-state`, `--save-naming`, loading with `--with-mini-state` or from the config), the IDE daemon (`clientIdeDaemon`) and the LSP server (`hh_client_rust lsp`), streaming errors, progress files.
- `hh_client_rust`: the client commands against that daemon (status, type-at-pos, ide-* queries, find-refs, rename, lint, `--show-tast`, ...).

Porting rules (one OCaml module = one Rust module, same logic and order, byte-identical output): `src/hh/PORTING.md`. Error codes, messages, positions and their order have to match exactly: the `.exp` files and the OCaml programs' output are compared byte for byte.

```bash
# Conformance against the typecheck suite: exact comparison with the .exp files
python3 hphp/hack/src/hh/conformance.py --hh <path to hh> --failures /tmp/failures.txt

# The other suites under test/ (hover, identify_symbol, ide_code_actions, lint, tast, ...), run as verify.py runs
# them with `hh single`; --expect-ocaml compares with the OCaml binaries' output instead of the .exp files
python3 hphp/hack/src/hh/suite.py --hh <path to hh> --all [--expect-ocaml <dir of the OCaml binaries>]

# Unit tests, the ported integration_ml tests, the monitor's process tests
cd hphp/hack/src && cargo +nightly test --release -p hh --features server --lib
cd hphp/hack/src && cargo +nightly test --release -p hh --features server --test integration_ml -- [FILTER]
cd hphp/hack/src && cargo +nightly test --release -p hh --features server --test monitor
```

`conformance.py` groups tests by what they expect. The rows that expect errors measure what the checker finds; the "no errors" row measures what it wrongly reports and must not regress. Use `--filter` for a subset.

## Testing

Tests live in `test/` organized by feature. Most suites use `test/verify.py` to compare program output against `.exp` expected-output files.

```bash
# ALWAYS invoke ./_build/hphp/hack/hack_oss_dune_invoke.sh from under hphp/hack.

# Run all tests
./_build/hphp/hack/hack_oss_dune_invoke.sh runtest

# Run a specific test suite via dune alias
./_build/hphp/hack/hack_oss_dune_invoke.sh build @typecheck            # typechecker tests
./_build/hphp/hack/hack_oss_dune_invoke.sh build @typecheck_w_timeout  # typechecker tests with 20s timeout
./_build/hphp/hack/hack_oss_dune_invoke.sh build @autocomplete         # autocomplete tests

```

Key test suites and their programs:

- `test/typecheck/` — type checking (`hh_single_type_check`)
- `test/autocomplete/` — autocomplete (`hh_single_complete`)
- `test/hover/` — hover info (`hh_single_type_check --ide-hover`)
- `test/find_refs/` — find references (`hh_single_type_check`)
- `test/full_fidelity/` — parser (`hh_parse`)
- `test/hackfmt/` — formatter (`hackfmt`)
- `test/decl/` — declarations (`hh_single_decl`)
- `test/lint/` — lint rules
- `test/ide_diagnostics/` — IDE diagnostics
- `test/incremental/` — incremental checking
- `test/unit/` — OCaml unit tests (OUnit)

Each test is a `.php` file with companion files: `.exp` (expected output), `HH_FLAGS` (flags for the test runner, per-directory or per-test).

## Architecture

Pipeline: source → parser → named AST → type checking → bytecode emission.

```
Source (.hack/.php)
  → [parser/]       Full-fidelity recursive descent parser (Rust with OCaml bindings)
  → [naming/]       Name resolution (Rust)
  → [elab/]         Elaboration (Rust)
  → [decl/]         Declaration extraction
  → [typing/]       Type inference and checking (OCaml)
  → [hackc/]        HHBC bytecode compilation (Rust)
```

### Key directories under `src/`

| Directory            | Description                                                            |
| -------------------- | ---------------------------------------------------------------------- |
| `parser/`            | Full-fidelity parser (Rust core, OCaml bindings)                       |
| `naming/`            | Name resolution phase                                                  |
| `elab/`              | AST elaboration                                                        |
| `decl/`              | Declaration extraction from source                                     |
| `typing/`            | Core type checking engine                                              |
| `hackc/`             | Bytecode compiler (HHBC emission, Rust)                                |
| `hackfmt/`           | Code formatter                                                         |
| `client_and_server/` | Shared IDE services: autocomplete, go-to-def, find-refs, hover, config |
| `server/`            | `hh_server` daemon: file watching, incremental rechecking              |
| `client/`            | `hh_client` CLI                                                        |
| `monitor/`           | Server process lifecycle                                               |
| `oxidized/`          | Generated Rust equivalents of OCaml types                              |
| `providers/`         | Abstract data-provider interfaces                                      |
| `deps/`              | Dependency tracking                                                    |
| `search/`            | Symbol search                                                          |
| `lints/`             | Lint rules                                                             |
| `package/`           | Module/package system                                                  |
| `diagnostics/`       | Error reporting                                                        |
| `hhi/`               | Built-in HHI stubs                                                     |
| `utils/`             | Shared utilities (OCaml + Rust)                                        |
| `hh_codegen/`        | Code generation tools                                                  |
| `hh_oxidize/`        | Tool to generate Rust types from OCaml type definitions                |
| `stubs/`             | Stub implementations for optional features                             |

### Entry points

| Binary                 | Source                        | Purpose                                     |
| ---------------------- | ----------------------------- | ------------------------------------------- |
| `hh_server`            | `src/hh_server.ml`            | Typechecker daemon with filesystem watching |
| `hh_client`            | `src/hh_client.ml`            | CLI client to talk to hh_server             |
| `hh_single_type_check` | `src/hh_single_type_check.ml` | Batch single-invocation typechecker         |
| `hh_single_complete`   | `src/hh_single_complete.ml`   | Batch autocomplete                          |
| `hh_parse`             | `src/hh_parse.ml`             | Standalone parser                           |
| `hackfmt`              | `src/hackfmt/`                | Code formatter                              |

## OCaml Coding Conventions

Full guide: `src/style_guide.md`. Formatting enforced by `.ocamlformat`.

- **Module naming**: `Underscore_separated_words` for top-level modules, `CamelCase` within files. Prefix with directory name (e.g., `Typing_foo` for `typing/foo.ml`).
- **Variants**: `Capitalized_underscore_separated_words` (including polymorphic variants).
- **Functions**: multi-line bodies in `begin...end`; single-line use parentheses.
- **Boolean params**: always labeled.
- **Matching**: prefer exhaustive matching; avoid wildcard `_`.
- **Module opens**: reserve top-level opens for very common modules. Prefer `module LMN = Long_module_name` or local opens.
- **Indentation**: `ocp-indent` is the final word. `.ocamlformat` is configured and enforced.

## Rust Conventions

Rust crates follow standard `cargo fmt` / `clippy`. FFI crates use the `_ffi` suffix. The `ocamlrep` crate handles OCaml ↔ Rust type marshaling. When adding new OCaml types that need Rust equivalents, use `hh_oxidize` to generate them into `oxidized/`.

**Shared crates must keep building for the OCaml side.** In crates outside `src/hh` (`oxidized`, the parser, the decl parser, `relative_path`, `pos`, `hackrs`, ...), leave the `ToOcamlRep` / `FromOcamlRep` derives and the `#[rust_to_ocaml(...)]` attributes as upstream has them (do not strip them or put them behind a Cargo feature), and when you add a field or a type to a shared type that the OCaml mirrors, derive or write its conversion too. `ocamlrep` and `ocamlrep_derive` are pure Rust; the crates that link the OCaml runtime (`ocamlrep_ocamlpool`, `ocamlrep_custom`, `ocamlrep_caml_builtins`, `ocamlrep_marshal`) need an OCaml toolchain, so do not add a dependency on one of them to a crate the Rust typechecker or `hackc` builds (`cargo tree -p hh -p hackc` must show only `ocamlrep`, `ocamlrep_derive` and `rust_to_ocaml_attr`): `file_info` converts its `Int64.t` hashes itself for that reason. Keep needs of the Rust typechecker inside the `hh` crate where possible.

The `#[rust_to_ocaml(...)]` attributes under `oxidized/gen` are inert in a build (`rust_to_ocaml_attr`) and are what `src/rust_to_ocaml` reads to generate OCaml from Rust. `hh_codegen elab-transform` reads `#[rust_to_ocaml(attr = "transform.opaque")]` / `"transform.explicit"` on the AST types to generate `elab/pass.rs` and `elab/transform.rs`.
