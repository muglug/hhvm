#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the "hack" directory of this source tree.
"""Check that a Rust port covers its OCaml source.

    port_coverage.py OCAML_FILE[:FIRST-LAST] RUST_FILE_OR_DIR...

Reports:

- the definitions of the OCaml (module-level `let` / `let rec` / `and`, in
  any nested `struct`) that have no Rust `fn` of the same name (Rust keywords
  get a trailing `_` or `r#`; a trailing `'` becomes `_prime`);
- the string literals of the OCaml that do not appear in the Rust. A literal
  with `Printf` conversions (`%s`, `%d`, ...) is split at them and each piece
  of three characters or more is looked for separately, since the Rust uses
  `format!`.

Both lists should be empty, or every remaining item explained in your report
(for example a function the OCaml defines twice, or text built differently).
"""

import os
import re
import sys

RUST_KEYWORDS = {
    'as', 'break', 'const', 'continue', 'crate', 'else', 'enum', 'extern', 'false', 'fn', 'for',
    'if', 'impl', 'in', 'let', 'loop', 'match', 'mod', 'move', 'mut', 'pub', 'ref', 'return',
    'self', 'static', 'struct', 'super', 'trait', 'true', 'type', 'unsafe', 'use', 'where',
    'while', 'async', 'await', 'dyn', 'abstract', 'become', 'box', 'do', 'final', 'macro',
    'override', 'priv', 'typeof', 'unsized', 'virtual', 'yield', 'try', 'gen',
}

STRUCT_OPEN = re.compile(r'^(\s*)(?:module\b.*|and\s+[A-Z]\w*.*|end\s*:?.*)=\s*struct\b\s*$')
STRUCT_OPEN_INLINE = re.compile(r'^(\s*)(?:module|and)\s+(?:rec\s+)?[A-Z]\w*\s*(?::[^=]*)?=\s*struct\b')
SIG_OPEN = re.compile(r'^(\s*)(?:module|and)\s+(?:rec\s+)?(?:type\s+)?[A-Z]\w*\s*:\s*sig\b')
END = re.compile(r'^(\s*)end\b')
DEF = re.compile(r"^(\s*)(?:let\s+rec|let|and)\s+([a-z_][A-Za-z0-9_']*)\b")


def strip_comments(src):
    """Blank out (* ... *) comments, which nest, keeping line structure."""
    out = []
    depth = 0
    i = 0
    in_str = False
    while i < len(src):
        c = src[i]
        if depth == 0 and not in_str and c == '"':
            in_str = True
            out.append(c)
            i += 1
            continue
        if in_str:
            if c == '\\':
                out.append(src[i:i + 2])
                i += 2
                continue
            if c == '"':
                in_str = False
            out.append(c)
            i += 1
            continue
        if src.startswith('(*', i):
            depth += 1
            out.append('  ')
            i += 2
            continue
        if depth and src.startswith('*)', i):
            depth -= 1
            out.append('  ')
            i += 2
            continue
        out.append(c if (depth == 0 or c == '\n') else ' ')
        i += 1
    return ''.join(out)


def ocaml_definitions(lines):
    """Names of module-level definitions, with line numbers."""
    defs = []
    stack = []  # indentation at which definitions of the current struct live
    in_sig = []
    for no, line in lines:
        if not line.strip():
            continue
        m = SIG_OPEN.match(line)
        if m and not line.rstrip().endswith('end'):
            in_sig.append(len(m.group(1)))
            continue
        if in_sig:
            m = END.match(line)
            if m and len(m.group(1)) == in_sig[-1]:
                in_sig.pop()
                if re.search(r'=\s*struct\b', line):
                    stack.append(len(m.group(1)) + 2)
            continue
        m = STRUCT_OPEN.match(line) or STRUCT_OPEN_INLINE.match(line)
        if m:
            stack.append(len(m.group(1)) + 2)
            continue
        m = END.match(line)
        if m and stack and len(m.group(1)) == stack[-1] - 2:
            stack.pop()
            continue
        m = DEF.match(line)
        if m:
            indent = len(m.group(1))
            level = stack[-1] if stack else 0
            if indent == level and m.group(2) != '_':
                defs.append((no, m.group(2)))
    return defs


def ocaml_strings(text):
    out = []
    for m in re.finditer(r'"((?:[^"\\]|\\.)*)"|\{([a-z_]*)\|(.*?)\|\2\}', text, re.S):
        s = m.group(1) if m.group(1) is not None else m.group(3)
        s = s.replace('\\n', '\n').replace('\\"', '"').replace('\\\\', '\\').replace('\\t', '\t')
        out.append(s)
    return out


def rust_text(paths):
    chunks = []
    for p in paths:
        if os.path.isdir(p):
            for dp, _dn, fn in os.walk(p):
                for f in sorted(fn):
                    if f.endswith('.rs'):
                        chunks.append(open(os.path.join(dp, f), errors='replace').read())
        else:
            chunks.append(open(p, errors='replace').read())
    return '\n'.join(chunks)


def rust_string_contents(text):
    out = []
    for m in re.finditer(r'r(#*)"(.*?)"\1|"((?:[^"\\]|\\.)*)"', text, re.S):
        if m.group(2) is not None:
            out.append(m.group(2))
        else:
            s = m.group(3)
            s = re.sub(r'\\\n\s*', '', s)
            s = s.replace('\\n', '\n').replace('\\"', '"').replace('\\\\', '\\').replace('\\t', '\t')
            out.append(s.replace('{{', '{').replace('}}', '}'))
    return '\x00'.join(out)


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        sys.exit(2)
    spec = sys.argv[1]
    m = re.match(r'^(.*?):(\d+)-(\d+)$', spec)
    path, lo, hi = (m.group(1), int(m.group(2)), int(m.group(3))) if m else (spec, None, None)
    src = strip_comments(open(path, errors='replace').read())
    all_lines = src.split('\n')
    lines = [(i + 1, l) for i, l in enumerate(all_lines) if lo is None or lo <= i + 1 <= hi]
    text = '\n'.join(l for _, l in lines)
    rust = rust_text(sys.argv[2:])
    fns = set(re.findall(r'\bfn\s+(?:r#)?([A-Za-z_][A-Za-z0-9_]*)', rust))

    missing_defs = []
    for no, name in ocaml_definitions(lines):
        cands = {name.replace("'", '_prime'), name + '_', name.rstrip('_')}
        if name in RUST_KEYWORDS:
            cands.add(name + '_')
        if not cands & fns:
            missing_defs.append((no, name))

    rust_strs = rust_string_contents(rust)
    missing_strs = []
    for s in ocaml_strings(text):
        pieces = [p for p in re.split(r'%[-+ #0-9.]*[sdifcbxXuSBLnN%a]|@[\[\]., ;]', s) if len(p.strip()) >= 3]
        for p in pieces:
            if p not in rust_strs and p not in rust:
                missing_strs.append(p)

    print(f'{path}' + (f' lines {lo}-{hi}' if lo else ''))
    print(f'definitions without a Rust fn of the same name: {len(missing_defs)}')
    for no, name in missing_defs:
        print(f'  line {no}: {name}')
    seen = set()
    uniq = [s for s in missing_strs if not (s in seen or seen.add(s))]
    print(f'string literal pieces not found in the Rust: {len(uniq)}')
    for s in uniq:
        print(f'  {s!r}')
    sys.exit(1 if (missing_defs or uniq) else 0)


if __name__ == '__main__':
    main()
