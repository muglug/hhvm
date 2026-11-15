#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the "hack" directory of this source tree.
"""Measure `hh single` against the expected outputs of a test suite.

    conformance.py --hh path/to/hh [--suite hphp/hack/test/typecheck]
                   [--failures FILE] [--jobs N] [--filter SUBSTRING]

Every `<test>.php` with a `<test>.php.exp` next to it is run (outside the
directories named `disabled`, which verify.py skips), with the flags
verify.py would pass. A test passes when the output is exactly the expected
output.

Tests are grouped by what they expect, because a checker that reports nothing
passes every "No errors" test: the groups that expect errors are the measure
of what the checker can find, and the "No errors" group is the measure of
what it wrongly reports.
"""

import argparse
import concurrent.futures
import os
import re
import shlex
import subprocess
import sys
from collections import Counter, defaultdict

PHASE = re.compile(r"\((Parsing|Naming|NastCheck|Typing|Lint|Init)\[\d+\]\)")


def category(expected: str) -> str:
    if expected.strip() == "No errors":
        return "no errors"
    phases = set(PHASE.findall(expected))
    if not phases:
        return "other output"
    if phases <= {"Parsing"}:
        return "parsing errors only"
    if phases <= {"Parsing", "Naming", "NastCheck"}:
        return "naming errors"
    return "typing errors"


# The flags the `typecheck` suite is run with (hphp/hack/test/typecheck/dune).
SUITE_FLAGS = ["--error-format", "plain_highlighted", "--config", "everything_sdt=false"]


def read_flags(path: str) -> list:
    if not os.path.isfile(path):
        return []
    flags = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if line and not line.startswith("#"):
                flags.extend(shlex.split(line))
    return flags


def flags_for(test: str) -> list:
    """As verify.py: the suite's flags, then those of the `HH_FLAGS` file in
    the directory of the test, then those of `<test>.flags`."""
    return (
        SUITE_FLAGS
        + read_flags(os.path.join(os.path.dirname(test), "HH_FLAGS"))
        + read_flags(os.path.splitext(test)[0] + ".flags")
    )


def run(hh: str, test: str, suite: str, timeout: int):
    with open(test + ".exp", errors="replace") as f:
        expected = f.read()
    # As verify.py runs the suite (`--batch`): `--batch-files --out-extension
    # EXT` writes the output of each file (hh_show, the diagnostics or "No
    # errors") to `<file>EXT`. (A `hh` that does not write it printed the same
    # on stdout.)
    ext = f".conformance{os.getpid()}.out"
    out_file = test + ext
    cmd = [hh, "single", "--batch-files", "--out-extension", ext] + flags_for(test)
    cmd += [os.path.basename(test), "--out-extension", ext]
    try:
        proc = subprocess.run(
            cmd,
            cwd=os.path.dirname(test),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout,
        )
        if os.path.exists(out_file):
            with open(out_file, errors="replace") as f:
                actual = f.read()
            os.remove(out_file)
        else:
            actual = proc.stdout.decode(errors="replace")
        # `hh_single_type_check` exits with 2 when there are errors.
        status = "crash" if proc.returncode not in (0, 1, 2) else None
    except subprocess.TimeoutExpired:
        actual, status = "", "timeout"
        if os.path.exists(out_file):
            os.remove(out_file)
    if status is None:
        status = "pass" if actual == expected else "fail"
    return test, category(expected), status, expected, actual


def main() -> int:
    here = os.path.dirname(os.path.abspath(__file__))
    parser = argparse.ArgumentParser()
    parser.add_argument("--hh", required=True)
    parser.add_argument(
        "--suite", default=os.path.join(here, "..", "..", "test", "typecheck")
    )
    parser.add_argument("--failures", help="write the failing tests to this file")
    parser.add_argument("--jobs", type=int, default=os.cpu_count())
    parser.add_argument("--timeout", type=int, default=30)
    parser.add_argument("--filter", help="only tests whose path contains this")
    args = parser.parse_args()

    suite = os.path.abspath(args.suite)
    hh = os.path.abspath(args.hh)
    tests = []
    for dirpath, dirnames, filenames in os.walk(suite):
        # As verify.py's `list_test_files`: a directory named `disabled` is
        # not part of the suite.
        dirnames[:] = [d for d in dirnames if d != "disabled"]
        for name in filenames:
            if name.endswith(".php") and name + ".exp" in filenames:
                path = os.path.join(dirpath, name)
                if not args.filter or args.filter in path:
                    tests.append(path)
    tests.sort()

    totals = Counter()
    by_status = defaultdict(Counter)
    failures = []
    # Among the failures of tests that expect no errors: what was reported.
    false_positive_codes = Counter()
    with concurrent.futures.ThreadPoolExecutor(args.jobs) as pool:
        futures = [pool.submit(run, hh, t, suite, args.timeout) for t in tests]
        for future in concurrent.futures.as_completed(futures):
            test, cat, status, expected, actual = future.result()
            totals[cat] += 1
            by_status[cat][status] += 1
            if status != "pass":
                failures.append((test, cat, status))
                if cat == "no errors":
                    for code in re.findall(r"\((\w+\[\d+\])\)", actual):
                        false_positive_codes[code] += 1

    order = [
        "parsing errors only",
        "naming errors",
        "typing errors",
        "other output",
        "no errors",
    ]
    print(f"{'expects':<22}{'tests':>7}{'pass':>7}{'fail':>7}{'crash':>7}{'timeout':>9}")
    total_pass = 0
    for cat in order:
        if not totals[cat]:
            continue
        s = by_status[cat]
        total_pass += s["pass"]
        print(
            f"{cat:<22}{totals[cat]:>7}{s['pass']:>7}{s['fail']:>7}"
            f"{s['crash']:>7}{s['timeout']:>9}"
        )
    print(f"{'total':<22}{len(tests):>7}{total_pass:>7}")
    if false_positive_codes:
        print("\nerrors reported for tests that expect none:")
        for code, n in false_positive_codes.most_common(15):
            print(f"  {n:>5}  {code}")

    if args.failures:
        failures.sort()
        with open(args.failures, "w") as f:
            for test, cat, status in failures:
                f.write(f"{status}\t{cat}\t{os.path.relpath(test, suite)}\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
