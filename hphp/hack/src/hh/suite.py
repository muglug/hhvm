#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the "hack" directory of this source tree.
"""Run a test suite of `hphp/hack/test` against its `.exp` files, the way
`hphp/hack/test/verify.py` runs it, with `hh single` (or `hh single-complete`)
in place of `hh_single_type_check` (or `hh_single_complete`).

    suite.py --hh path/to/hh SUITE [SUITE...] [--failures FILE] [--out-dir DIR]
             [--filter SUBSTRING] [--jobs N] [--timeout S] [--diff N] [--rule N]
    suite.py --ocaml BINDIR SUITE...       # the OCaml binaries (the oracle)
    suite.py --hh hh --expect-ocaml BINDIR SUITE...  # compare with the OCaml's
                                           # output instead of the .exp files
    suite.py --hh path/to/hh --all         # every suite of the table below
    suite.py --show SUITE                  # print the verify.py arguments used

SUITE is a directory (or one test file) under `hphp/hack/test`, absolute or
relative to the current directory or to `hphp/hack/test` (`hover`,
`ide_code_actions/flip_around_comma`, `lint/implicit_pess/foo.php`).

How a suite is run (as its dune rule runs verify.py):
- The verify.py arguments come from the `(run .../verify.py ...)` action of
  the nearest `dune` file at or above SUITE (`--rule N` picks the N-th rule
  of that file, default 0); suites that have no dune rule in this tree (their
  rule is a Meta TARGETS file) use the table SUITES_WITHOUT_DUNE below,
  and RULE_OVERRIDES replaces the dune rules that the OCaml itself fails.
  The tests are those verify.py would list for the rule (`list_test_files`:
  `--in-extension`, `--disabled-extension`, no `disabled` directories),
  restricted to SUITE.
- Each test is run from its directory as verify.py's `run_test_program` does:
  `PROGRAM [--mode-flag] TEST.php FLAGS... HH_FLAGS... TEST.flags...` (the
  suite's `--flags`, then the directory's `HH_FLAGS`, then `<test>.flags`),
  stdin = the test with `--stdin` (no file argument then), stderr merged
  into the output unless `--no-stderr`, `FORCE_ERROR_COLOR` set.
- `--batch` suites (`run_batch_tests`): the OCaml is run with
  `--batch-files --out-extension EXT` one file at a time and EXT read and
  removed; `hh single` is run on the file alone and its stdout taken (it
  prints what the batch mode writes, see conformance.py), stderr not.
- Output and expected text are compared as verify.py's `check_result`
  (lines stripped, `/tmp/<dir>/x.hhi` normalised, OCaml stack-trace lines
  dropped, `--default-expect-regex`, `--check-expected-included-in-actual`,
  `--ignore-error-text`); `--expect-extension` / `--fallback-expect-extension`.

A test is `pass`, `fail`, `not-ported` (the output says "mode not ported:",
see hh_single_modes.rs), `crash` (killed by a signal, or a Rust panic: exit
101), or `timeout`. `--failures FILE` lists every test that did not pass
(`status<TAB>path`), `--out-dir DIR` writes the actual output of each of them
to DIR/<path>.out, `--diff N` prints the diffs of the first N.
"""

import argparse
import concurrent.futures
import difflib
import os
import re
import shlex
import subprocess
import sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
# hphp/hack/test (this file is hphp/hack/src/hh*/suite.py)
TEST_ROOT = os.path.normpath(os.path.join(HERE, "..", "..", "test"))

# Suites whose rule is not in this tree (Meta's TARGETS files): the
# verify.py arguments, as for a dune rule. The mode flag was found by
# running the OCaml oracle (`--ocaml`) on the suite.
SUITES_WITHOUT_DUNE = {
    "hover": "--flags --hover-at-caret",
    "enforcement": "--flags --enforcement-at-caret",
    "enforcement_batch": "--flags --enforcement-at-caret-batch",
    "ide_diagnostics": "--flags --ide-diagnostics",
    "classish_positions": "--flags --dump-classish-positions",
    "outline_for_agents": "",  # the mode is in HH_FLAGS
    "infer_dynamic": "",  # the mode is in HH_FLAGS
    "map_reduce": "",  # the mode is in HH_FLAGS
    "simplihack": "--flags --run-simplihack",
}

# Rules of this tree's dune files that the OCaml itself fails, replaced by
# what passes with the OCaml: the refactor_sd rules give the mode both in
# `--flags` and in HH_FLAGS ("only a single mode should be specified").
RULE_OVERRIDES = {
    "refactor_sd/dump_constraints/class": "--in-extension .php --flags --error-format plain",
    "refactor_sd/dump_constraints/function": "--in-extension .php --flags --error-format plain",
    "refactor_sd/simplify_constraints/class": "--in-extension .php --flags --error-format plain",
    "refactor_sd/simplify_constraints/function": "--in-extension .php --flags --error-format plain",
}

# The suites of the IDE services and other `hh single` modes (`--all`), in
# the order of the mode table (hh_single_modes.rs).
ALL_SUITES = [
    "identify_symbol",
    "hover",
    "ide_signature_help",
    "autocomplete",
    "autoclose",
    "outline",
    "outline_for_agents",
    "highlight_refs",
    "find_local",
    "find_refs",
    "go_to_impl",
    "ide_code_actions",
    "quickfixes",
    "ide_diagnostics",
    "classish_positions",
    "lint",
    "dumpsymbolinfo",
    "dump_inheritance",
    "cst_search",
    "deps",
    "nast",
    "tast",
    "holes",
    "infer_dynamic",
    "enforcement",
    "enforcement_batch",
    "count_imprecise_types",
    "remove_dead_unsafe_casts",
    "refactor_sd",
    "map_reduce",
    "simplihack",
]

OCAML_PROGRAMS = {
    "hh_single_type_check": "hh_single_type_check",
    "hh_single_complete": "hh_single_complete",
}
RUST_SUBCOMMANDS = {
    "hh_single_type_check": "single",
    "hh_single_complete": "single-complete",
}


# ---------------------------------------------------------------------------
# verify.py's argument parser (the arguments that change how tests run)


def verify_arg_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(add_help=False)
    p.add_argument("test_path")
    p.add_argument("--program")
    p.add_argument("--out-extension", default=".out")
    p.add_argument("--expect-extension", default=".exp")
    p.add_argument("--fallback-expect-extension")
    p.add_argument("--default-expect-regex")
    p.add_argument("--in-extension", default=".php")
    p.add_argument("--include-directories", action="store_true")
    p.add_argument("--disabled-extension", default=".no_typecheck")
    p.add_argument("--verbose", action="store_true")
    p.add_argument("--idempotence", action="store_true")
    p.add_argument("--max-workers", type=int, default=48)
    p.add_argument("--diff", action="store_true")
    p.add_argument("--mode-flag")
    p.add_argument("--flags", nargs=argparse.REMAINDER)
    p.add_argument("--stdin", action="store_true")
    p.add_argument("--no-stderr", action="store_true")
    p.add_argument("--batch", action="store_true")
    p.add_argument("--ignore-error-text", action="store_true")
    p.add_argument("--only-compare-error-lines", action="store_true")
    p.add_argument("--check-expected-included-in-actual", action="store_true")
    p.add_argument("--timeout", type=int)
    p.add_argument("--force-color", action="store_true")
    p.add_argument("--no-hh-flags", action="store_true")
    p.add_argument("--zoncolan-order", action="store_true")
    p.add_argument("--verify-pessimisation", default="no")
    p.add_argument("--normalize-paths", action="store_true")
    p.add_argument("--filter-glog-failures", action="store_true")
    return p


RUN_RE = re.compile(r"\(run\s+%\{project_root\}/hack/test/verify\.py(.*?)\)\s*\)", re.S)
EXE_RE = re.compile(r"%\{exe:[^}]*?([a-z_]+)\.exe\}")


def dune_rules(dune_file: str) -> list:
    """The verify.py argument lists of the rules of a dune file."""
    with open(dune_file) as f:
        text = f.read()
    rules = []
    for m in RUN_RE.finditer(text):
        body = m.group(1)
        body = EXE_RE.sub(lambda e: e.group(1), body)
        body = body.replace("%{project_root}/hack/test", TEST_ROOT)
        rules.append(shlex.split(body))
    return rules


def find_rule(path: str, rule_index: int):
    """(verify.py arguments, where they come from) for a suite path."""
    d = path if os.path.isdir(path) else os.path.dirname(path)
    while True:
        dune = os.path.join(d, "dune")
        rel = os.path.relpath(d, TEST_ROOT)
        if rel in RULE_OVERRIDES:
            args = [d, "--program", "hh_single_type_check"]
            return args + shlex.split(RULE_OVERRIDES[rel]), "suite.py override"
        if os.path.isfile(dune):
            rules = dune_rules(dune)
            if rules:
                if rule_index >= len(rules):
                    sys.exit(f"{dune} has {len(rules)} verify.py rules")
                return rules[rule_index], f"{os.path.relpath(dune, TEST_ROOT)}#{rule_index}"
        rel = os.path.relpath(d, TEST_ROOT)
        if rel in SUITES_WITHOUT_DUNE:
            args = [d, "--program", "hh_single_type_check"]
            args += shlex.split(SUITES_WITHOUT_DUNE[rel])
            return args, "suite.py table"
        if os.path.normpath(d) == TEST_ROOT or os.path.dirname(d) == d:
            # No rule: verify.py's defaults, hh_single_type_check.
            return [path, "--program", "hh_single_type_check"], "default"
        d = os.path.dirname(d)


# ---------------------------------------------------------------------------
# verify.py's test listing and flags


def files_with_ext(files, ext):
    return [os.path.splitext(f)[0] for f in files if os.path.splitext(f)[1] == ext]


def list_test_files(root, disabled_ext, test_ext, include_directories):
    if os.path.isfile(root):
        return [root] if root.endswith(test_ext) else []
    if os.path.isdir(root):
        result = []
        if include_directories and root.endswith(test_ext):
            result.append(root)
        children = os.listdir(root)
        disabled = files_with_ext(children, disabled_ext)
        for child in children:
            if child != "disabled" and child not in disabled:
                result.extend(
                    list_test_files(
                        os.path.join(root, child),
                        disabled_ext,
                        test_ext,
                        include_directories,
                    )
                )
        return result
    return []


def get_hh_flags(test_dir):
    path = os.path.join(test_dir, "HH_FLAGS")
    if not os.path.isfile(path):
        return []
    with open(path) as f:
        return shlex.split(f.read())


def get_test_flags(path):
    path = os.path.splitext(path)[0] + ".flags"
    if not os.path.isfile(path):
        return []
    with open(path) as f:
        return shlex.split(f.read().strip())


def get_content(file_path, ext="", fallback_ext=None):
    for e in [ext] + ([fallback_ext] if fallback_ext is not None else []):
        try:
            with open(file_path + e, "r", errors="replace") as f:
                return f.read()
        except FileNotFoundError:
            pass
    return ""


# ---------------------------------------------------------------------------
# verify.py's comparison


def filter_ocaml_stacktrace(text):
    out = []
    for x in text.splitlines():
        s = x.lstrip()
        if not (s.startswith("Called") or s.startswith("Raised")):
            out.append(x)
    return "\n".join(out)


def filter_temp_hhi_path(text):
    return re.sub(r"/tmp/[^/]*/([a-zA-Z0-9_]+\.hhi)", "/tmp/hhi_dir/\\1", text)


def strip_lines(text):
    return "\n".join(line.strip() for line in text.splitlines())


def check_included(expected, output):
    sections = output.split("--\n")
    expected_sections = expected.split("--\n")
    for section, expected_section in zip(sections, expected_sections):
        elts = set(section.splitlines())
        for e in set(expected_section.splitlines()):
            if e not in elts:
                return False
    return True


def is_ok(va, expected, out):
    if va.check_expected_included_in_actual:
        return check_included(expected, out)
    expected = filter_temp_hhi_path(strip_lines(expected))
    normalized = filter_temp_hhi_path(strip_lines(out))
    if expected == normalized:
        return True
    # compare_expected, verify_pessimisation = no
    if va.ignore_error_text and not (expected == "No errors" or normalized == "No errors"):
        return True
    if expected == filter_ocaml_stacktrace(normalized):
        return True
    return (
        va.default_expect_regex is not None
        and re.search(va.default_expect_regex, normalized) is not None
        and expected == ""
    )


# ---------------------------------------------------------------------------
# Running


def ocaml_cmd(kind, bindir):
    exe = os.path.join(bindir, OCAML_PROGRAMS.get(kind, kind))
    return [exe] if os.path.isfile(exe) else None


def program_cmd(kind, opts):
    if opts.ocaml:
        return ocaml_cmd(kind, opts.ocaml)
    if kind not in RUST_SUBCOMMANDS:
        return None
    return [opts.hh, RUST_SUBCOMMANDS[kind]]


def invoke(test, va, program, is_ocaml, opts):
    """(output, status or None, command) of one run of `program` on a test."""
    test_dir, test_name = os.path.split(test)
    # get_flags_cache: the suite's flags, then HH_FLAGS (or HH_FLAGS first
    # with --zoncolan-order); get_flags_dummy with --no-hh-flags.
    if va.no_hh_flags:
        flags = va.flags or []
    elif va.zoncolan_order:
        flags = get_hh_flags(test_dir) + (va.flags or [])
    else:
        flags = (va.flags or []) + get_hh_flags(test_dir)
    test_flags = get_test_flags(test)
    mode_flag = [va.mode_flag] if va.mode_flag else []
    stdin = get_content(test) if va.stdin else None
    env = os.environ.copy()
    env["FORCE_ERROR_COLOR"] = "true" if va.force_color else "false"
    timeout = va.timeout or opts.timeout
    status = None
    out_file = None
    if va.batch:
        cmd = list(program) + mode_flag
        if is_ocaml:
            ext = f".suite{os.getpid()}.{abs(hash(test)) % 10**8}.out"
            cmd += ["--batch-files", "--out-extension", ext]
            out_file = test + ext
        cmd += flags + test_flags + [test_name]
        if is_ocaml:
            # verify.py's batch flags come before the suite's (which may set
            # --out-extension again): ours must win.
            cmd += ["--out-extension", ext]
    else:
        cmd = list(program) + mode_flag
        if stdin is None:
            cmd.append(test_name)
        cmd += flags + test_flags
    try:
        proc = subprocess.run(
            cmd,
            cwd=test_dir,
            input=stdin.encode() if stdin is not None else None,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE if (va.batch or va.no_stderr) else subprocess.STDOUT,
            env=env,
            timeout=timeout,
        )
        if out_file is not None:
            try:
                with open(out_file, errors="replace") as f:
                    output = f.read()
                os.remove(out_file)
            except FileNotFoundError:
                output = "Output file " + os.path.realpath(out_file) + " was not found!"
        else:
            output = proc.stdout.decode(errors="replace")
        err = proc.stderr.decode(errors="replace") if proc.stderr else ""
        if "mode not ported:" in output or "mode not ported:" in err:
            status = "not-ported"
        elif proc.returncode < 0 or proc.returncode == 101:
            status = "crash"
    except subprocess.TimeoutExpired:
        output, status = "Timed out.", "timeout"
        if out_file is not None and os.path.exists(out_file):
            os.remove(out_file)
    return output, status, cmd


def run_one(test, va, program, oracle, opts):
    if oracle is not None:
        # --expect-ocaml: the expected output is the OCaml's.
        expected, _, _ = invoke(test, va, oracle, True, opts)
    else:
        expected = get_content(test, va.expect_extension, va.fallback_expect_extension)
    output, status, cmd = invoke(test, va, program, bool(opts.ocaml), opts)
    if status is None:
        status = "pass" if is_ok(va, expected, output) else "fail"
    return test, status, expected, output, cmd


def resolve_suite(s):
    # A name under hphp/hack/test first (`deps` is also a directory of
    # hphp/hack/src), then a path from the current directory.
    for cand in (os.path.join(TEST_ROOT, s), s):
        if os.path.exists(cand):
            return os.path.abspath(cand)
    sys.exit(f"no such suite: {s}")


def expand_suite(path, rule):
    """[(suite path, rule index)]: a directory that no rule covers, with
    rules in its subdirectories (`ide_code_actions`, `refactor_sd`), is the
    list of those; `rule` "all" is every rule of the dune file."""
    args, origin = find_rule(path, 0)
    if origin == "default" and os.path.isdir(path):
        subs = []
        for dirpath, dirnames, filenames in os.walk(path):
            dirnames.sort()
            if "dune" in filenames and dune_rules(os.path.join(dirpath, "dune")):
                subs.append(dirpath)
                dirnames[:] = []
        if subs:
            return [x for sub in subs for x in expand_suite(sub, rule)]
    if rule == "all":
        d = path if os.path.isdir(path) else os.path.dirname(path)
        while not os.path.isfile(os.path.join(d, "dune")) and d != TEST_ROOT and os.path.dirname(d) != d:
            d = os.path.dirname(d)
        dune = os.path.join(d, "dune")
        n = len(dune_rules(dune)) if os.path.isfile(dune) else 0
        return [(path, i) for i in range(max(n, 1))]
    return [(path, int(rule))]


def plan_suite(suite, rule, opts):
    args, origin = find_rule(suite, rule)
    va, unknown = verify_arg_parser().parse_known_args(args)
    if unknown:
        print(f"warning: verify.py arguments not understood: {unknown}", file=sys.stderr)
    kind = os.path.basename(va.program or "hh_single_type_check")
    tests = list_test_files(
        os.path.abspath(va.test_path),
        va.disabled_extension,
        va.in_extension,
        va.include_directories,
    )
    tests = [
        t
        for t in tests
        if t == suite or t.startswith(suite.rstrip(os.sep) + os.sep)
    ]
    if opts.filter:
        tests = [t for t in tests if opts.filter in t]
    tests.sort()
    return va, kind, origin, args, tests


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("suites", nargs="*")
    parser.add_argument("--hh", help="the Rust hh binary")
    parser.add_argument("--ocaml", help="directory of the OCaml binaries (oracle)")
    parser.add_argument(
        "--expect-ocaml",
        metavar="BINDIR",
        help="compare with the output of the OCaml binaries of BINDIR, not the .exp files",
    )
    parser.add_argument("--all", action="store_true", help="every suite of ALL_SUITES")
    parser.add_argument("--show", action="store_true", help="print how each suite is run")
    parser.add_argument("--failures", help="write the tests that did not pass here")
    parser.add_argument("--out-dir", help="write the output of failing tests here")
    parser.add_argument("--diff", type=int, default=0, help="print the first N diffs")
    parser.add_argument("--filter", help="only tests whose path contains this")
    parser.add_argument("--rule", default="0", help="which rule of the dune file (N or all)")
    parser.add_argument("--jobs", type=int, default=os.cpu_count())
    parser.add_argument("--timeout", type=int, default=60)
    opts = parser.parse_args()
    if opts.hh:
        opts.hh = os.path.abspath(opts.hh)
    if opts.ocaml:
        opts.ocaml = os.path.abspath(opts.ocaml)
    if opts.expect_ocaml:
        opts.expect_ocaml = os.path.abspath(opts.expect_ocaml)
    suites = list(opts.suites) + (ALL_SUITES if opts.all else [])
    if not suites:
        parser.error("no suite given")
    if not opts.show and not (opts.hh or opts.ocaml):
        parser.error("--hh or --ocaml is required")

    planned = []
    for s in suites:
        expanded = expand_suite(resolve_suite(s), opts.rule)
        for path, rule in expanded:
            name = os.path.relpath(path, TEST_ROOT)
            if rule:
                name += f"#{rule}"
            planned.append((name, *plan_suite(path, rule, opts)))
    if opts.show:
        for s, va, kind, origin, args, tests in planned:
            print(f"{s}: {len(tests)} tests, {kind}, from {origin}")
            print("    verify.py " + " ".join(shlex.quote(a) for a in args))
        return 0

    rows = []
    failures = []
    shown = 0
    width = max(len(p[0]) for p in planned)
    print(f"{'suite':<{width}} {'tests':>6} {'pass':>6} {'fail':>6} {'unport':>6} {'crash':>6} {'tmout':>6}")
    total = Counter()
    for s, va, kind, origin, args, tests in planned:
        program = program_cmd(kind, opts)
        oracle = ocaml_cmd(kind, opts.expect_ocaml) if opts.expect_ocaml else None
        if opts.expect_ocaml and oracle is None:
            program = None
        c = Counter()
        if program is None:
            c["no-program"] = len(tests)
            for t in tests:
                failures.append(("no-program", t))
        else:
            with concurrent.futures.ThreadPoolExecutor(opts.jobs) as pool:
                results = list(pool.map(lambda t: run_one(t, va, program, oracle, opts), tests))
            for test, status, expected, output, cmd in results:
                c[status] += 1
                if status == "pass":
                    continue
                failures.append((status, test))
                if opts.out_dir:
                    dest = os.path.join(opts.out_dir, os.path.relpath(test, TEST_ROOT) + ".out")
                    os.makedirs(os.path.dirname(dest), exist_ok=True)
                    with open(dest, "w") as f:
                        f.write(output)
                if shown < opts.diff:
                    shown += 1
                    print(f"--- {os.path.relpath(test, TEST_ROOT)} ({status})")
                    print("    cd " + shlex.quote(os.path.dirname(test)) + " && " + " ".join(shlex.quote(a) for a in cmd))
                    sys.stdout.writelines(
                        difflib.unified_diff(
                            expected.splitlines(True),
                            output.splitlines(True),
                            "expected",
                            "actual",
                        )
                    )
                    print()
        total.update(c)
        total["tests"] += len(tests)
        extra = f"  (no {kind} program)" if program is None else ""
        print(
            f"{s:<{width}} {len(tests):>6} {c['pass']:>6} {c['fail']:>6} "
            f"{c['not-ported']:>6} {c['crash']:>6} {c['timeout']:>6}{extra}",
            flush=True,
        )
    if len(planned) > 1:
        print(
            f"{'total':<{width}} {total['tests']:>6} {total['pass']:>6} {total['fail']:>6} "
            f"{total['not-ported']:>6} {total['crash']:>6} {total['timeout']:>6}"
        )
    if opts.failures:
        with open(opts.failures, "w") as f:
            for status, test in sorted(failures, key=lambda x: x[1]):
                f.write(f"{status}\t{os.path.relpath(test, TEST_ROOT)}\n")
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())
