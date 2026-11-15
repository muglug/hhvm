#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the "hack" directory of this source tree.

"""Generates the Rust modules of the Glean schema (`glean/hack.rs`,
`glean/src.rs`, `glean/fbthrift.rs`, `glean/gencode.rs`) from the OCaml
modules of the same names in `hphp/hack/src/typing/write_symbol_info/glean/`.

Those OCaml modules are themselves generated from the Glean schema (Meta's
`glean/schema/gen:gen-schema --ocaml`, not in the open-source tree), so they
are the specification: this script reads the type declarations and the
`to_json*` functions of each module and writes, for each OCaml module
`Foo` of `hack.ml`, a Rust module `hack::foo` with

- the types (`t` -> `T`, `key` -> `Key`, `value` -> `Value`, the other
  records of the module in camel case), with the OCaml constructor and field
  names (constructors in camel case, a trailing `_` kept; fields unchanged,
  Rust keywords get a trailing `_`), deriving `Ord` (the OCaml
  `[@@deriving ord]`: constructors in declaration order, records field by
  field, lists lexicographically, `None` first);
- the `to_json*` functions, giving the same JSON as the OCaml: the same keys
  in the same order (the optional fields of a record are consed in front of
  the list of the others, in the order the OCaml does it), the same values.

`Hh_json.json` is `crate::yojson::safe::T` here: every OCaml `Hh_json`
value of these modules is turned into `Yojson.Safe.t` by
`Hh_json.to_yojson` before it is written (`Predicate.Fact_acc.add_fact`),
and `to_yojson` maps `JSON_Number (string_of_int i)` to `` `Int i``, the
other constructors one to one.

The `key` of a predicate is boxed (`T::Key(Box<Key>)`) when it is a record
or a variant, so that the recursive types have a size; `T::key(k)` builds
`Key k`.

Usage (from this directory):

  python3 glean_schema_gen.py OCAML_GLEAN_DIR .

with OCAML_GLEAN_DIR = hphp/hack/src/typing/write_symbol_info/glean. The
script fails on any declaration or expression form it does not know, so a
regenerated schema with new forms is noticed.
"""

import os
import re
import sys

FILES = ["hack", "src", "fbthrift", "gencode"]
# The modules of the `glean_schema` library (unwrapped): a qualified name
# `Src.File.t` starting with one of these refers to another file.
TOP = {
    "Hack": "hack",
    "Src": "src",
    "Fbthrift": "fbthrift",
    "Gencode": "gencode",
    "Builtin": "builtin",
}
GLEAN = "crate::write_symbol_info::glean"

RUST_KEYWORDS = {
    "as", "break", "const", "continue", "crate", "else", "enum", "extern",
    "false", "fn", "for", "if", "impl", "in", "let", "loop", "match", "mod",
    "move", "mut", "pub", "ref", "return", "self", "Self", "static", "struct",
    "super", "trait", "true", "type", "unsafe", "use", "where", "while",
    "async", "await", "dyn", "abstract", "become", "box", "do", "final",
    "macro", "override", "priv", "typeof", "unsized", "virtual", "yield",
    "try", "gen",
}


def snake(name):
    """OCaml module name (`NamespaceQName`, `Package_`) -> Rust module name
    (`namespace_q_name`, `package_`)."""
    trailing = name.endswith("_")
    base = name.rstrip("_")
    s = re.sub(r"([A-Z]+)([A-Z][a-z])", r"\1_\2", base)
    s = re.sub(r"([a-z0-9])([A-Z])", r"\1_\2", s)
    s = s.lower()
    if trailing:
        s += "_"
    if s in RUST_KEYWORDS:
        s += "_"
    return s


def camel(name):
    """OCaml type or constructor name (`vect_or_dict`, `Class_args`,
    `Union_`) -> Rust (`VectOrDict`, `ClassArgs`, `Union_`)."""
    trailing = name.endswith("_")
    parts = [p for p in name.split("_") if p]
    s = "".join(p[0].upper() + p[1:] for p in parts)
    if trailing:
        s += "_"
    return s


def field(name):
    return name + "_" if name in RUST_KEYWORDS else name


class Fail(Exception):
    pass


# ---------------------------------------------------------------------------
# Parsing


def strip_comments(text):
    out = []
    i = 0
    depth = 0
    while i < len(text):
        if text.startswith("(*", i):
            depth += 1
            i += 2
        elif depth and text.startswith("*)", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def parse_type_expr(s):
    """`X.t list option` -> ('option', ('list', ('named', 'X.t')))."""
    toks = s.split()
    if not toks:
        raise Fail("empty type expression")
    ty = ("named", toks[0])
    for t in toks[1:]:
        if t in ("list", "option"):
            ty = (t, ty)
        else:
            raise Fail("type expression: %r" % s)
    return ty


def parse_type_body(body):
    body = body.strip()
    if body.startswith("{"):
        if not body.endswith("}"):
            raise Fail("record: %r" % body)
        fields = []
        for f in body[1:-1].split(";"):
            f = f.strip()
            if not f:
                continue
            m = re.fullmatch(r"(\w+)\s*:\s*(.+)", f, re.S)
            if not m:
                raise Fail("record field: %r" % f)
            fields.append((m.group(1), parse_type_expr(m.group(2))))
        return ("record", fields)
    if body.startswith("|"):
        ctors = []
        for c in body.split("|")[1:]:
            c = c.strip()
            m = re.fullmatch(r"(\w+)(?:\s+of\s+(.+))?", c, re.S)
            if not m:
                raise Fail("constructor: %r" % c)
            ctors.append(
                (m.group(1), parse_type_expr(m.group(2)) if m.group(2) else None)
            )
        return ("variant", ctors)
    return ("alias", parse_type_expr(body))


def split_functions(text):
    """The `let rec`/`and` functions of a module body: (name, params, body)."""
    parts = re.split(r"(?m)^\s*(?:let rec|and)\s+(\w+)", text)
    if parts[0].strip():
        raise Fail("text before the functions: %r" % parts[0])
    funs = []
    for i in range(1, len(parts), 2):
        name = parts[i]
        rest = parts[i + 1]
        m = re.match(r"\s*(\{[^}]*\}|\w+)?\s*=\s*(.*)$", rest, re.S)
        if not m:
            raise Fail("function header: %s %r" % (name, rest[:80]))
        funs.append((name, m.group(1), m.group(2).strip()))
    return funs


def parse_module(name, struct):
    struct = struct.replace("[@@deriving ord]", "")
    m = re.search(r"(?m)^\s*let rec ", struct)
    if not m:
        raise Fail("no to_json in %s" % name)
    types_text, funs_text = struct[: m.start()], struct[m.start():]
    types = []
    pieces = re.split(r"(?m)^\s*(?:type|and)\s+(\w+)\s*=", types_text)
    if pieces[0].strip():
        raise Fail("text before the types of %s: %r" % (name, pieces[0]))
    for i in range(1, len(pieces), 2):
        types.append((pieces[i], parse_type_body(pieces[i + 1])))
    return {"name": name, "types": types, "funs": split_functions(funs_text)}


def parse_file(path):
    text = strip_comments(open(path).read())
    mods = []
    for m in re.finditer(
        r"(?ms)^(?:module rec|and) (\w+): sig\n.*?^end = struct\n(.*?)^end\s*$",
        text,
    ):
        mods.append(parse_module(m.group(1), m.group(2)))
    return mods


# ---------------------------------------------------------------------------
# Rust generation


class Gen:
    def __init__(self, file, mods):
        self.file = file
        self.mods = mods
        self.out = []

    def mod_path(self, qual):
        """`X` (a module of this file) or `Src.X` -> the Rust module path."""
        parts = qual.split(".")
        if parts[0] == "Fact_id":
            if len(parts) != 1:
                raise Fail("Fact_id path %r" % qual)
            return GLEAN + "::fact_id"
        if parts[0] == "Util":
            return GLEAN + "::util"
        if parts[0] in TOP:
            return "::".join([GLEAN, TOP[parts[0]]] + [snake(p) for p in parts[1:]])
        if len(parts) != 1:
            raise Fail("module path %r" % qual)
        return "super::" + snake(parts[0])

    def rust_type(self, ty, local, binary=False):
        kind = ty[0]
        if kind == "list":
            return "Vec<%s>" % self.rust_type(ty[1], local, binary)
        if kind == "option":
            return "Option<%s>" % self.rust_type(ty[1], local, binary)
        n = ty[1]
        if n == "string":
            return "Vec<u8>" if binary else "String"
        if n == "int":
            return "isize"
        if n == "bool":
            return "bool"
        if n == "unit":
            return "()"
        if n in local:
            return camel(n)
        if n.endswith(".t"):
            return self.mod_path(n[:-2]) + "::T"
        raise Fail("type %r" % n)

    # Expressions of the OCaml to_json functions. `env` is the set of bound
    # variables (all bound to references).
    def expr(self, e, env):
        e = e.strip()
        while e.startswith("(") and matching_paren(e) == len(e) - 1:
            e = e[1:-1].strip()
        m = re.fullmatch(r"ignore (\w+); JSON_Object \[\]", e)
        if m and m.group(1) in env:
            return "{ let _ = %s; Json::Assoc(vec![]) }" % var(m.group(1))
        if e == "JSON_Object []":
            return "Json::Assoc(vec![])"
        m = re.fullmatch(r"Util\.id (\w+)", e)
        if m and m.group(1) in env:
            return GLEAN + "::util::id(*%s)" % var(m.group(1))
        m = re.fullmatch(r"Util\.key \((\w+) (\w+)\)", e)
        if m and m.group(2) in env:
            return GLEAN + "::util::key(%s(%s))" % (m.group(1), var(m.group(2)))
        m = re.fullmatch(r"JSON_String (\w+)", e)
        if m and m.group(1) in env:
            return "Json::String(%s.clone())" % var(m.group(1))
        m = re.fullmatch(r"JSON_Bool (\w+)", e)
        if m and m.group(1) in env:
            return "Json::Bool(*%s)" % var(m.group(1))
        m = re.fullmatch(r"JSON_Number \(string_of_int (\w+)\)", e)
        if m:
            if m.group(1) in env:
                return "Json::Int(*%s)" % var(m.group(1))
            if re.fullmatch(r"\d+", m.group(1)):
                return "Json::Int(%s)" % m.group(1)
        m = re.fullmatch(
            r'JSON_String \(List\.map ~f:Base64\.encode_string (\w+)\s*\|>\s*String\.concat ~sep:""\)',
            e,
        )
        if m and m.group(1) in env:
            return (
                "Json::String(%s.iter().map(|s| %s::util::base64_encode_string(s)).collect::<String>())"
                % (var(m.group(1)), GLEAN)
            )
        m = re.fullmatch(
            r"JSON_Array \(List\.map ~f:\(fun (\w+) -> (.*)\) (\w+)\)", e, re.S
        )
        if m and m.group(3) in env:
            inner = self.expr(m.group(2), env | {m.group(1)})
            return "Json::List(%s.iter().map(|%s| %s).collect())" % (
                var(m.group(3)),
                var(m.group(1)),
                inner,
            )
        m = re.fullmatch(r"((?:[A-Z]\w*\.)+)to_json (\w+)", e)
        if m and m.group(2) in env:
            return "%s::to_json(%s)" % (self.mod_path(m.group(1)[:-1]), var(m.group(2)))
        m = re.fullmatch(r"(\w*to_json\w*) (\w+)", e)
        if m and m.group(2) in env:
            return "%s(%s)" % (m.group(1), var(m.group(2)))
        raise Fail("expression %r" % e)

    # The inverse of `expr` (for the tests only): the Rust expression that
    # reads, from the JSON `j` (a `&Json`), the value that `e` writes.
    def inv(self, e, j):
        e = e.strip()
        while e.startswith("(") and matching_paren(e) == len(e) - 1:
            e = e[1:-1].strip()
        if re.fullmatch(r"ignore (\w+); JSON_Object \[\]", e) or e == "JSON_Object []":
            return "{ let _ = %s; () }" % j
        if re.fullmatch(r"JSON_String (\w+)", e):
            return "%s::util::test_json::string(%s)" % (GLEAN, j)
        if re.fullmatch(r"JSON_Bool (\w+)", e):
            return "%s::util::test_json::bool(%s)" % (GLEAN, j)
        if re.fullmatch(r"JSON_Number \(string_of_int (\w+)\)", e):
            return "%s::util::test_json::int(%s)" % (GLEAN, j)
        if re.fullmatch(r'JSON_String \(List\.map ~f:Base64\.encode_string (\w+)\s*\|>\s*String\.concat ~sep:""\)', e):
            return "%s::util::test_json::binaries(%s)" % (GLEAN, j)
        m = re.fullmatch(r"JSON_Array \(List\.map ~f:\(fun (\w+) -> (.*)\) (\w+)\)", e, re.S)
        if m:
            return "%s::util::test_json::list(%s).iter().map(|y| %s).collect()" % (
                GLEAN, j, self.inv(m.group(2), "y"))
        m = re.fullmatch(r"((?:[A-Z]\w*\.)+)to_json (\w+)", e)
        if m:
            return "%s::of_json(%s)" % (self.mod_path(m.group(1)[:-1]), j)
        m = re.fullmatch(r"(\w*)to_json(\w*) (\w+)", e)
        if m:
            return "%sof_json%s(%s)" % (m.group(1), m.group(2), j)
        raise Fail("inverse of %r" % e)

    def binary_fields(self, mod):
        """Names (fields or constructors) whose strings are binary: their
        JSON is the concatenated base64 of each string."""
        b = set()
        for (_, params, body) in mod["funs"]:
            for m in re.finditer(r'\("(\w+)", JSON_String \(List\.map ~f:Base64', body):
                b.add(m.group(1))
            for m in re.finditer(r"\|\s*(\w+)\s+\w+\s*->[^\n]*Base64", body):
                b.add(m.group(1))
            if "Base64" in body and params and not params.startswith("{"):
                b.add(params)
        return b

    def gen_module(self, mod):
        name = mod["name"]
        local = {t for (t, _) in mod["types"]}
        tydefs = dict(mod["types"])
        is_pred = (
            "t" in tydefs
            and tydefs["t"][0] == "variant"
            and [c for (c, _) in tydefs["t"][1]] == ["Id", "Key"]
        )
        boxed_key = is_pred and tydefs["key"][0] in ("record", "variant")
        binary = self.binary_fields(mod)
        w = self.out.append
        w("")
        w("/// `%s.%s`." % (camel_file(self.file), name))
        w("pub mod %s {" % snake(name))
        w("    #![allow(unused_imports, clippy::all)]")
        w("    use crate::yojson::safe::T as Json;")
        for (tname, body) in mod["types"]:
            rname = camel(tname)
            w("")
            w("    /// `%s.%s.%s`." % (camel_file(self.file), name, tname))
            if body[0] == "alias":
                bin_alias = (tname == "value" and "x" in binary)
                w("    pub type %s = %s;" % (rname, self.rust_type(body[1], local, bin_alias)))
                continue
            w("    #[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]")
            if body[0] == "record":
                w("    pub struct %s {" % rname)
                for (f, fty) in body[1]:
                    w("        pub %s: %s," % (field(f), self.rust_type(fty, local, f in binary)))
                w("    }")
            else:
                w("    pub enum %s {" % rname)
                for (c, cty) in body[1]:
                    if cty is None:
                        w("        %s," % camel(c))
                    elif is_pred and tname == "t" and c == "Key" and boxed_key:
                        w("        Key(Box<Key>),")
                    else:
                        w("        %s(%s)," % (camel(c), self.rust_type(cty, local, c in binary)))
                w("    }")
        if is_pred:
            w("")
            w("    impl T {")
            w("        /// `Key k`.")
            w("        pub fn key(k: Key) -> T {")
            w("            T::Key(%s)" % ("Box::new(k)" if boxed_key else "k"))
            w("        }")
            w("    }")
        for (fname, params, body) in mod["funs"]:
            self.gen_fun(mod, tydefs, fname, params, body)
        w("}")

    def fun_type(self, tydefs, fname):
        if fname == "to_json":
            t = "t"
        elif fname.startswith("to_json_"):
            t = fname[len("to_json_"):]
        elif fname.endswith("_to_json"):
            t = fname[: -len("_to_json")]
        else:
            raise Fail("function %s" % fname)
        if t not in tydefs:
            raise Fail("function %s: no type %s" % (fname, t))
        return t

    def gen_fun(self, mod, tydefs, fname, params, body):
        self.gen_to_json(mod, tydefs, fname, params, body)
        self.gen_of_json(mod, tydefs, fname, params, body)

    def gen_of_json(self, mod, tydefs, fname, params, body):
        """The inverse of `fname` (tests only)."""
        w = self.out.append
        t = self.fun_type(tydefs, fname)
        rty = camel(t)
        tbody = tydefs[t]
        oname = fname.replace("to_json", "of_json")
        w("")
        w("    #[cfg(test)]")
        w("    pub fn %s(j: &Json) -> %s {" % (oname, rty))
        if params is None and body.startswith("function"):
            ctors = dict(tbody[1])
            arms = [a.strip() for a in re.split(r"(?m)^\s*\|", body[len("function"):]) if a.strip()]
            consts = []
            objs = []
            for a in arms:
                m = re.fullmatch(r"(\w+)(?:\s+(\w+))?\s*->\s*(.*)", a, re.S)
                c, v, e = m.group(1), m.group(2), m.group(3).strip()
                if v is None:
                    m2 = re.fullmatch(r"JSON_Number \(string_of_int (\d+)\)", e)
                    if not m2:
                        raise Fail("inverse of constant arm %r" % a)
                    consts.append((m2.group(1), c))
                    continue
                if c == "Id" and fname == "to_json":
                    objs.append(("id", "%s::Id(%s::util::test_json::int(v))" % (rty, GLEAN)))
                    continue
                if c == "Key" and fname == "to_json":
                    objs.append(("key", "%s::key(of_json_key(v))" % rty))
                    continue
                m2 = re.fullmatch(r'JSON_Object \[\("(\w+)", (.*)\)\]', e, re.S)
                if not m2:
                    raise Fail("inverse of arm %r" % a)
                objs.append((m2.group(1), "%s::%s(%s)" % (rty, camel(c), self.inv(m2.group(2), "v"))))
            if consts:
                w("        match %s::util::test_json::int(j) {" % GLEAN)
                for (n, c) in consts:
                    w("            %s => %s::%s," % (n, rty, camel(c)))
                w('            n => panic!("%s: {n}"),' % oname)
                w("        }")
            else:
                w("        let (k, v) = %s::util::test_json::single(j);" % GLEAN)
                w("        match k {")
                for (k, e) in objs:
                    w('            "%s" => %s,' % (k, e))
                w('            k => panic!("%s: {k}"),' % oname)
                w("        }")
            w("    }")
            return
        if params is not None and params.startswith("{"):
            m = re.fullmatch(r"let fields = \[(.*?)\] in(.*)JSON_Object fields", body, re.S)
            base = re.findall(r'\("(\w+)", (.*?)\);\s*\n', m.group(1) + "\n")
            opts = re.findall(
                r"let fields =\s*match (\w+) with\s*\| None -> fields\s*\| Some (\w+) -> "
                r'\("(\w+)", (.*?)\) :: fields in', m.group(2), re.S)
            by_field = {}
            for (j, e) in base:
                mv = re.search(r"(\w+)\)*$", e.strip())
                by_field[mv.group(1)] = ("req", j, e)
            for (fv, sv, j, e) in opts:
                by_field[fv] = ("opt", j, e)
            w("        %s {" % rty)
            for (f, _) in tbody[1]:
                if f not in by_field:
                    raise Fail("inverse: field %s not serialised" % f)
                kind, j, e = by_field[f]
                if kind == "req":
                    w('            %s: { let y = %s::util::test_json::field(j, "%s"); %s },' % (field(f), GLEAN, j, self.inv(e, "y")))
                else:
                    w('            %s: %s::util::test_json::field_opt(j, "%s").map(|y| %s),' % (field(f), GLEAN, j, self.inv(e, "y")))
            w("        }")
            w("    }")
            return
        w("        %s" % self.inv(body, "j"))
        w("    }")

    def gen_to_json(self, mod, tydefs, fname, params, body):
        w = self.out.append
        t = self.fun_type(tydefs, fname)
        rty = camel(t)
        tbody = tydefs[t]
        w("")
        w("    /// `%s.%s.%s`." % (camel_file(self.file), mod["name"], fname))
        if body == "function":
            raise Fail("empty function")
        if params is None and body.startswith("function"):
            # a match on the constructors
            if tbody[0] != "variant":
                raise Fail("function on a non-variant: %s.%s" % (mod["name"], fname))
            ctors = dict(tbody[1])
            arms = [a.strip() for a in re.split(r"(?m)^\s*\|", body[len("function"):]) if a.strip()]
            w("    pub fn %s(x: &%s) -> Json {" % (fname, rty))
            w("        match x {")
            seen = []
            for a in arms:
                m = re.fullmatch(r"(\w+)(?:\s+(\w+))?\s*->\s*(.*)", a, re.S)
                if not m:
                    raise Fail("arm %r" % a)
                c, v, e = m.group(1), m.group(2), m.group(3).strip()
                if c not in ctors:
                    raise Fail("arm of unknown constructor %s" % c)
                seen.append(c)
                if v is None:
                    if ctors[c] is not None:
                        raise Fail("arm without variable: %s" % c)
                    w("            %s::%s => %s," % (rty, camel(c), self.expr(e, set())))
                    continue
                m2 = re.fullmatch(r'JSON_Object \[\("(\w+)", (.*)\)\]', e, re.S)
                if m2:
                    inner = self.expr(m2.group(2), {v})
                    w(
                        '            %s::%s(%s) => Json::Assoc(vec![("%s".to_string(), %s)]),'
                        % (rty, camel(c), var(v), m2.group(1), inner)
                    )
                else:
                    w("            %s::%s(%s) => %s," % (rty, camel(c), var(v), self.expr(e, {v})))
            if seen != [c for (c, _) in tbody[1]]:
                raise Fail("arms of %s.%s: %s" % (mod["name"], fname, seen))
            w("        }")
            w("    }")
            return
        if params is not None and params.startswith("{"):
            if tbody[0] != "record":
                raise Fail("record pattern on a non-record")
            names = [p.strip() for p in params[1:-1].split(";") if p.strip()]
            if names != [f for (f, _) in tbody[1]]:
                raise Fail("record pattern %s vs %s" % (names, tbody[1]))
            m = re.fullmatch(
                r"let fields = \[(.*?)\] in(.*)JSON_Object fields", body, re.S
            )
            if not m:
                raise Fail("record body %r" % body[:100])
            base = re.findall(r'\("(\w+)", (.*?)\);\s*\n', m.group(1) + "\n")
            if len(base) != len([x for x in m.group(1).split("\n") if x.strip()]):
                raise Fail("record base fields: %r" % m.group(1))
            opts_text = m.group(2)
            opts = re.findall(
                r"let fields =\s*match (\w+) with\s*\| None -> fields\s*\| Some (\w+) -> "
                r'\("(\w+)", (.*?)\) :: fields in',
                opts_text,
                re.S,
            )
            if len(opts) != opts_text.count("let fields"):
                raise Fail("record optional fields: %r" % opts_text)
            env = set(names)
            w("    pub fn %s(x: &%s) -> Json {" % (fname, rty))
            w(
                "        let %s { %s } = x;"
                % (rty, ", ".join(field(n) if field(n) == n else "%s: %s" % (field(n), var(n)) for n in names))
            )
            mut = "mut " if opts else ""
            w("        let %sfields: Vec<(String, Json)> = vec![" % mut)
            for (j, e) in base:
                w('            ("%s".to_string(), %s),' % (j, self.expr(e, env)))
            w("        ];")
            for (fv, sv, j, e) in opts:
                if fv not in env:
                    raise Fail("optional field %s" % fv)
                w("        if let Some(%s) = %s {" % (var(sv), var(fv)))
                w('            fields.insert(0, ("%s".to_string(), %s));' % (j, self.expr(e, env | {sv})))
                w("        }")
            w("        Json::Assoc(fields)")
            w("    }")
            return
        # one variable (or `_`) and an expression
        if params is None:
            raise Fail("function without parameter: %s" % fname)
        if params == "_":
            w("    pub fn %s(_: &%s) -> Json {" % (fname, rty))
            w("        %s" % self.expr(body, set()))
        else:
            w("    pub fn %s(%s: &%s) -> Json {" % (fname, var(params), rty))
            w("        %s" % self.expr(body, {params}))
        w("    }")

    def run(self):
        w = self.out.append
        w("// Copyright (c) Meta Platforms, Inc. and affiliates.")
        w("//")
        w("// This source code is licensed under the MIT license found in the")
        w('// LICENSE file in the "hack" directory of this source tree.')
        w("//")
        w("// @" + "generated by glean_schema_gen.py from")
        w("// hphp/hack/src/typing/write_symbol_info/glean/%s.ml: do not edit." % self.file)
        w("")
        w("//! `%s` (`write_symbol_info/glean/%s.ml`, generated from the Glean schema):" % (camel_file(self.file), self.file))
        w("//! the types of the facts of the schema and their JSON serialisers. See")
        w("//! `glean_schema_gen.py` for how the OCaml names and JSON map to the Rust.")
        w("")
        w("#![allow(non_camel_case_types, clippy::all)]")
        for mod in self.mods:
            self.gen_module(mod)
        w("")
        w("/// Tests only: the JSON of `of_json_key` of the key of a fact of the")
        w("/// predicate `name` (`\"ClassDeclaration\"`), `None` for a name that is")
        w("/// not a predicate of this module.")
        w("#[cfg(test)]")
        w("pub fn round_trip_key(name: &str, key: &crate::yojson::safe::T) -> Option<crate::yojson::safe::T> {")
        w("    match name {")
        for mod in self.mods:
            tydefs = dict(mod["types"])
            if "key" in tydefs and any(f == "to_json_key" for (f, _, _) in mod["funs"]):
                w('        "%s" => Some(%s::to_json_key(&%s::of_json_key(key))),' % (mod["name"], snake(mod["name"]), snake(mod["name"])))
        w("        _ => None,")
        w("    }")
        w("}")
        return "\n".join(self.out) + "\n"


def var(v):
    return v + "_" if v in RUST_KEYWORDS else v


def camel_file(f):
    return f[0].upper() + f[1:]


def matching_paren(e):
    depth = 0
    for i, c in enumerate(e):
        if c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0:
                return i
    return -1


def main():
    src_dir, out_dir = sys.argv[1], sys.argv[2]
    for f in FILES:
        mods = parse_file(os.path.join(src_dir, f + ".ml"))
        try:
            text = Gen(f, mods).run()
        except Fail as e:
            sys.exit("%s.ml: %s" % (f, e))
        with open(os.path.join(out_dir, f + ".rs"), "w") as out:
            out.write(text)
        print("%s.rs: %d modules" % (f, len(mods)))


if __name__ == "__main__":
    main()
