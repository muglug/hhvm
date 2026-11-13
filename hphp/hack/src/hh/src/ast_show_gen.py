#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the "hack" directory of this source tree.

"""Generates `ast_show.rs`: the `[@@deriving show]` printers (`pp_*`) of the
types of `Ast_defs` and `Aast_defs`, as ppx_deriving's `show` plugin
(`ppx_deriving_show.ml`) writes them, over the `oxidized` types.

Inputs: the OCaml type declarations of the two modules after preprocessing
(`ocamlc -dsource -stop-after parsing -c X.pp.ml 2> X.src.ml` on the
`X.pp.ml` of an OCaml build: dune's `.pp.ml` are binary ASTs), and the
`oxidized` sources, whose types mirror the OCaml ones constructor for
constructor and field for field (matched here by position).

  python3 ast_show_gen.py AST_DEFS_SRC AAST_DEFS_SRC OXIDIZED_DIR > ast_show.rs
"""

import re
import sys

# ---------------------------------------------------------------------------
# OCaml type declarations


def ocaml_tokens(text):
    """Tokens of OCaml type declarations; attributes become ('attr', name,
    payload) tokens."""
    toks = []
    i = 0
    n = len(text)
    while i < n:
        c = text[i]
        if c.isspace():
            i += 1
        elif text.startswith("(*", i):
            depth = 0
            while i < n:
                if text.startswith("(*", i):
                    depth += 1
                    i += 2
                elif text.startswith("*)", i):
                    depth -= 1
                    i += 2
                    if depth == 0:
                        break
                else:
                    i += 1
        elif text.startswith("[@", i):
            # attribute: up to the matching ]
            j = i + 1
            while j < n and text[j] == "@":
                j += 1
            depth = 1
            k = j
            while k < n and depth > 0:
                if text[k] == '"':
                    k += 1
                    while text[k] != '"':
                        if text[k] == "\\":
                            k += 1
                        k += 1
                elif text[k] == "[":
                    depth += 1
                elif text[k] == "]":
                    depth -= 1
                k += 1
            body = text[j : k - 1].strip()
            m = re.match(r"[A-Za-z_.]+", body)
            name = m.group(0) if m else ""
            toks.append(("attr", name, body[len(name) :].strip(), text[i:j]))
            i = k
        elif c == '"':
            j = i + 1
            while text[j] != '"':
                if text[j] == "\\":
                    j += 1
                j += 1
            toks.append(("str", text[i : j + 1]))
            i = j + 1
        elif c == "'" and i + 1 < n and (text[i + 1].isalpha() or text[i + 1] == "_"):
            m = re.compile(r"'[A-Za-z_][A-Za-z0-9_']*").match(text, i)
            toks.append(("tyvar", m.group(0)[1:]))
            i = m.end()
        elif c.isalpha() or c == "_":
            m = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)*").match(
                text, i
            )
            toks.append(("id", m.group(0)))
            i = m.end()
        elif text.startswith("->", i):
            toks.append(("p", "->"))
            i += 2
        else:
            toks.append(("p", c))
            i += 1
    return toks


class Ty:
    """An OCaml type expression: kind in 'var', 'constr', 'tuple'."""

    def __init__(self, kind, name=None, args=(), attrs=()):
        self.kind = kind
        self.name = name
        self.args = list(args)
        self.attrs = list(attrs)

    def opaque(self):
        return any(a[1] == "opaque" for a in self.attrs)

    def printer(self):
        for a in self.attrs:
            if a[1] == "printer":
                return a[2]
        return None

    def __repr__(self):
        if self.kind == "var":
            return "'" + self.name
        if self.kind == "tuple":
            return "(" + " * ".join(map(repr, self.args)) + ")"
        return "%s(%s)" % (self.name, ", ".join(map(repr, self.args)))


class Parser:
    def __init__(self, toks):
        self.toks = toks
        self.i = 0

    def peek(self, k=0):
        j = self.i + k
        return self.toks[j] if j < len(self.toks) else ("eof",)

    def next(self):
        t = self.peek()
        self.i += 1
        return t

    def expect(self, kind, val=None):
        t = self.next()
        if t[0] != kind or (val is not None and t[1] != val):
            raise Exception("expected %s %s, got %s at %d" % (kind, val, t, self.i))
        return t

    def is_p(self, v, k=0):
        t = self.peek(k)
        return t[0] == "p" and t[1] == v

    def attrs(self):
        res = []
        while self.peek()[0] == "attr" and self.peek()[3] == "[@":
            res.append(self.next())
        return res

    # typexpr := app ('*' app)*
    def typexpr(self):
        items = [self.app()]
        while self.is_p("*"):
            self.next()
            items.append(self.app())
        if len(items) == 1:
            return items[0]
        return Ty("tuple", args=items)

    # app := atom constr*
    def app(self):
        t = self.atom()
        while self.peek()[0] == "id" and self.peek()[1] not in ("of", "and", "type"):
            name = self.next()[1]
            t = Ty("constr", name, t if isinstance(t, list) else [t])
            t.attrs += self.attrs()
        if isinstance(t, list):
            raise Exception("type argument list without a constructor")
        return t

    def atom(self):
        t = self.peek()
        if t[0] == "tyvar":
            self.next()
            ty = Ty("var", t[1])
            ty.attrs += self.attrs()
            return ty
        if t[0] == "id":
            self.next()
            ty = Ty("constr", t[1])
            ty.attrs += self.attrs()
            return ty
        if self.is_p("("):
            self.next()
            first = self.typexpr()
            if self.is_p(","):
                args = [first]
                while self.is_p(","):
                    self.next()
                    args.append(self.typexpr())
                self.expect("p", ")")
                return args  # arguments of the next constructor
            self.expect("p", ")")
            first.attrs += self.attrs()
            return first
        raise Exception("unexpected %s at %d" % (t, self.i))


class Decl:
    def __init__(self, name, params, kind, body, manifest, attrs):
        self.name = name
        self.params = params
        self.kind = kind  # 'alias', 'variant', 'record'
        self.body = body
        self.manifest = manifest
        self.attrs = attrs


def parse_record(p):
    p.expect("p", "{")
    fields = []
    while not p.is_p("}"):
        if p.peek()[0] == "id" and p.peek()[1] == "mutable":
            p.next()
        name = p.expect("id")[1]
        p.expect("p", ":")
        ty = p.typexpr()
        ty.attrs += p.attrs()
        if p.is_p(";"):
            p.next()
        ty.attrs += p.attrs()
        fields.append((name, ty))
    p.expect("p", "}")
    return fields


def parse_variant(p):
    ctors = []
    while p.is_p("|"):
        p.next()
        name = p.expect("id")[1]
        args = None  # ('tuple', [ty]) or ('record', fields)
        if p.peek()[0] == "id" and p.peek()[1] == "of":
            p.next()
            if p.is_p("{"):
                args = ("record", parse_record(p))
            else:
                items = [p.app()]
                while p.is_p("*"):
                    p.next()
                    items.append(p.app())
                args = ("tuple", items)
        else:
            args = ("tuple", [])
        attrs = p.attrs()
        ctors.append((name, args, attrs))
    return ctors


def parse_decls(text):
    """The type declarations of a -dsource'd module, with their deriving
    options: [(decl, with_path)]."""
    lines = text.split("\n")
    groups = []
    cur = None
    for line in lines:
        starts_type = line.startswith("type ")
        starts_and_type = line.startswith("and ") and re.match(
            r"and (\('[a-z]+(, '[a-z]+)*\) |'[a-z]+ )?[a-z_][A-Za-z0-9_']* *=", line
        )
        if starts_type:
            cur = [line]
            groups.append(cur)
        elif starts_and_type and cur is not None:
            cur.append(line)
        elif line[:1] and not line[:1].isspace() and not line.startswith("["):
            cur = None
        elif cur is not None:
            cur.append(line)
    res = []
    for g in groups:
        text = "\n".join(g)
        toks = ocaml_tokens(text)
        with_path = True
        for t in toks:
            if t[0] == "attr" and t[1] == "deriving" and re.search(
                r"show\s*\{\s*with_path\s*=\s*false", t[2]
            ):
                with_path = False
        p = Parser(toks)
        decls = []
        while p.peek()[0] != "eof":
            kw = p.next()
            if kw[0] == "attr":
                continue
            assert kw[0] == "id" and kw[1] in ("type", "and"), kw
            params = []
            if p.peek()[0] == "tyvar":
                params = [p.next()[1]]
            elif p.is_p("("):
                p.next()
                while not p.is_p(")"):
                    t = p.next()
                    if t[0] == "tyvar":
                        params.append(t[1])
                p.next()
            name = p.expect("id")[1]
            p.expect("p", "=")
            manifest = None
            if p.is_p("|"):
                kind, body = "variant", parse_variant(p)
            elif p.is_p("{"):
                kind, body = "record", parse_record(p)
            else:
                ty = p.typexpr()
                ty.attrs += p.attrs()
                if p.is_p("="):
                    p.next()
                    manifest = ty
                    if p.is_p("|"):
                        kind, body = "variant", parse_variant(p)
                    else:
                        kind, body = "record", parse_record(p)
                else:
                    kind, body = "alias", ty
            attrs = []
            while p.peek()[0] == "attr":
                attrs.append(p.next())
            decls.append(Decl(name, params, kind, body, manifest, attrs))
        for d in decls:
            res.append((d, with_path))
    return res


# ---------------------------------------------------------------------------
# Rust (oxidized) type declarations


def strip_rust(text):
    out = []
    i = 0
    n = len(text)
    while i < n:
        if text.startswith("//", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
        elif text.startswith("#[", i) or text.startswith("#![", i):
            depth = 0
            j = text.index("[", i)
            while True:
                if text[j] == "[":
                    depth += 1
                elif text[j] == "]":
                    depth -= 1
                    if depth == 0:
                        break
                elif text[j] == '"':
                    j += 1
                    while text[j] != '"':
                        if text[j] == "\\":
                            j += 1
                        j += 1
                j += 1
            i = j + 1
        elif text[i] == '"':
            j = i + 1
            while text[j] != '"':
                if text[j] == "\\":
                    j += 1
                j += 1
            out.append(text[i : j + 1])
            i = j + 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def split_top(s, sep=","):
    """Split at `sep` outside <>, (), {}, []."""
    parts = []
    depth = 0
    cur = []
    for c in s:
        if c in "<({[":
            depth += 1
        elif c in ">)}]":
            depth -= 1
        if c == sep and depth == 0:
            parts.append("".join(cur))
            cur = []
        else:
            cur.append(c)
    if "".join(cur).strip():
        parts.append("".join(cur))
    return [x.strip() for x in parts]


def matching(s, i):
    """Index of the bracket closing the one at s[i]."""
    o = s[i]
    c = {"(": ")", "{": "}", "<": ">", "[": "]"}[o]
    depth = 0
    for j in range(i, len(s)):
        if s[j] in "({<[":
            depth += 1
        elif s[j] in ")}>]":
            depth -= 1
            if depth == 0:
                return j
    raise Exception("unbalanced")


class RItem:
    def __init__(self, kind, name, generics, body):
        self.kind = kind  # 'tstruct' (tuple struct), 'struct', 'enum', 'type'
        self.name = name
        self.generics = generics
        self.body = body


def parse_rust(text):
    text = strip_rust(text)
    items = {}
    uses = {}
    for m in re.finditer(r"pub use ([a-z_:]+)::([A-Z][A-Za-z0-9_]*);", text):
        uses[m.group(2)] = m.group(1)
    pat = re.compile(r"pub (struct|enum|type) ([A-Z][A-Za-z0-9_]*)")
    for m in pat.finditer(text):
        kind, name = m.group(1), m.group(2)
        i = m.end()
        generics = []
        if text[i] == "<":
            j = matching(text, i)
            generics = [g.split(":")[0].strip() for g in split_top(text[i + 1 : j])]
            i = j + 1
        while text[i].isspace():
            i += 1
        if kind == "type":
            assert text[i] == "=", (name, text[i : i + 20])
            j = text.index(";", i)
            # (types with ; inside do not occur in type aliases here)
            items[name] = RItem("type", name, generics, text[i + 1 : j].strip())
        elif kind == "struct":
            if text[i] == "(":
                j = matching(text, i)
                fields = [f[len("pub ") :] if f.startswith("pub ") else f for f in split_top(text[i + 1 : j])]
                items[name] = RItem("tstruct", name, generics, fields)
            else:
                j = matching(text, i)
                fields = []
                for f in split_top(text[i + 1 : j]):
                    f = f[len("pub ") :] if f.startswith("pub ") else f
                    fname, fty = f.split(":", 1)
                    fields.append((fname.strip(), fty.strip()))
                items[name] = RItem("struct", name, generics, fields)
        else:
            j = matching(text, i)
            variants = []
            for v in split_top(text[i + 1 : j]):
                vm = re.match(r"([A-Z][A-Za-z0-9_]*)\s*(.*)$", v, re.S)
                vname, rest = vm.group(1), vm.group(2).strip()
                if rest.startswith("("):
                    variants.append((vname, "tuple", split_top(rest[1:-1])))
                elif rest.startswith("{"):
                    fs = []
                    for f in split_top(rest[1:-1]):
                        fname, fty = f.split(":", 1)
                        fs.append((fname.strip(), fty.strip()))
                    variants.append((vname, "struct", fs))
                else:
                    variants.append((vname, "unit", []))
            items[name] = RItem("enum", name, generics, variants)
    return items, uses


def rust_ty_parse(s):
    """A Rust type as (head, [args]) with head a path, '()' for tuples, '&'
    for references."""
    s = s.strip()
    if s.startswith("("):
        j = matching(s, 0)
        inner = split_top(s[1:j])
        return ("()", [rust_ty_parse(x) for x in inner])
    if s.startswith("&"):
        return ("&", [rust_ty_parse(re.sub(r"^&('[a-z]+ )?", "", s))])
    m = re.match(r"([A-Za-z0-9_:]+)\s*(<.*>)?$", s, re.S)
    head = m.group(1)
    args = []
    if m.group(2):
        args = [rust_ty_parse(x) for x in split_top(m.group(2)[1:-1])]
    return (head, args)


def rust_ty_str(t):
    head, args = t
    if head == "()":
        return "(" + ", ".join(rust_ty_str(a) for a in args) + ("," if len(args) == 1 else "") + ")"
    if head == "&":
        return "&" + rust_ty_str(args[0])
    if args:
        return head + "<" + ", ".join(rust_ty_str(a) for a in args) + ">"
    return head


# ---------------------------------------------------------------------------
# Generation


def camel(name):
    trailing = name.endswith("_")
    parts = [p for p in name.split("_") if p]
    res = "".join(p[0].upper() + p[1:] for p in parts)
    return res + ("_" if trailing else "")


# Printers of types of other modules (hand-written in ast_show.rs).
EXTERN = {
    ("Pos", "t"): "super::pp_pos_t",
    ("Local_id", "t"): "super::pp_local_id_t",
    ("File_info", "mode"): "super::pp_file_info_mode",
    ("Namespace_env", "env"): "super::pp_namespace_env",
}

# OCaml types whose Rust type is not in the module's oxidized file.
RUST_TYPE = {
    ("Ast_defs", "pos"): "oxidized::pos::Pos",
    ("Aast_defs", "pos"): "oxidized::pos::Pos",
    ("Aast_defs", "local_id"): "oxidized::local_id::LocalId",
}

# `string`s that are bytes in Rust in some places.
BYTES = {("Ast_defs", "byte_string"), ("Aast_defs", "byte_string")}

BOXES = ("Box", "std::boxed::Box", "Rc", "std::rc::Rc", "Arc", "std::sync::Arc")


class Gen:
    def __init__(self, modules, rust):
        # modules: {ocaml module name: {type name: (decl, with_path)}}
        self.modules = modules
        self.rust = rust  # {rust module: (items, uses)}
        self.out = []
        self.var = 0
        self.errors = []

    def fresh(self, base="a"):
        self.var += 1
        return "%s%d" % (base, self.var)

    def rust_item(self, rmod, rname):
        items, uses = self.rust[rmod]
        if rname in items:
            return rmod, items[rname]
        if rname in uses:
            m = uses[rname].split("::")[-1]
            if m in self.rust:
                return self.rust_item(m, rname)
        return None, None

    # statements printing `expr` (a Rust expression of type `&rty`) as the
    # OCaml type `ty` is printed
    def walk(self, ty, rty, expr, omod):
        if any(a[1] == "visitors.opaque" for a in ty.attrs):
            # `Aast.map` does not visit this value: its positions stay.
            inner = Ty(ty.kind, ty.name, ty.args, [a for a in ty.attrs if a[1] != "visitors.opaque"])
            v = self.fresh("pos_none")
            return (
                ["let %s = std::mem::replace(&mut p.pos_none, false);" % v]
                + self.walk(inner, rty, expr, omod)
                + ["p.pos_none = %s;" % v]
            )
        out = []
        head, rargs = rty
        printer = ty.printer()
        if printer is not None:
            raise Exception("[@printer] not supported: %s" % printer)
        if ty.opaque():
            return ['ps(p, "<opaque>");']
        if head in BOXES and not (ty.kind == "constr" and ty.name in ("ref",)):
            return self.walk(ty, rargs[0], "&**(%s)" % expr, omod)
        if ty.kind == "var":
            if ty.name == "ex":
                return ["(p.ex)(p.fmt, %s);" % expr]
            if ty.name == "en":
                return ["(p.en)(p.fmt, %s);" % expr]
            raise Exception("type variable %s" % ty.name)
        if ty.kind == "tuple":
            if head != "()" or len(rargs) != len(ty.args):
                raise Exception("tuple %r vs %s" % (ty, rust_ty_str(rty)))
            vs = [self.fresh() for _ in ty.args]
            out.append("{")
            out.append("let (%s) = %s;" % (", ".join(vs) + ("," if len(vs) == 1 else ""), expr))
            out.append('fprintf_open_tuple(p);')
            for i, (a, ra, v) in enumerate(zip(ty.args, rargs, vs)):
                if i > 0:
                    out.append('comma_space(p);')
                out += self.walk(a, ra, v, omod)
            out.append('fprintf_close_tuple(p);')
            out.append("}")
            return out
        name = ty.name
        if name in ("list",):
            if head not in ("Vec", "std::vec::Vec"):
                raise Exception("list vs %s" % rust_ty_str(rty))
            v = self.fresh("x")
            i = self.fresh("i")
            out.append('list_open(p);')
            out.append("for (%s, %s) in (%s).iter().enumerate() {" % (i, v, expr))
            out.append("if %s > 0 { semi_space(p); }" % i)
            out += self.walk(ty.args[0], rargs[0], v, omod)
            out.append("}")
            out.append('list_close(p);')
            return out
        if name == "option":
            if head not in ("Option", "std::option::Option"):
                raise Exception("option vs %s" % rust_ty_str(rty))
            v = self.fresh("x")
            out.append("match %s {" % expr)
            out.append('None => ps(p, "None"),')
            out.append("Some(%s) => {" % v)
            out.append('ps(p, "(Some ");')
            out += self.walk(ty.args[0], rargs[0], v, omod)
            out.append('ps(p, ")");')
            out.append("}")
            out.append("}")
            return out
        if name == "int":
            return ["pp_int(p, *%s as isize);" % expr]
        if name == "bool":
            return ["pp_bool(p, *%s);" % expr]
        if name in ("string", "String.t"):
            return ["pp_string(p, %s);" % expr]
        if name == "float":
            return ["pp_float(p, *%s);" % expr]
        if name == "unit":
            return ['ps(p, "()");']
        # a named type
        if "." in name:
            m, n = name.rsplit(".", 1)
        else:
            m, n = omod, name
        fn = self.fn_path(m, n, ty)
        return ["%s(p, %s);" % (fn, expr)]

    def fn_path(self, m, n, ty):
        if m in self.modules and n in self.modules[m]:
            for a in ty.args:
                if a.kind != "var":
                    raise Exception("non-variable type argument of %s.%s" % (m, n))
            return "%s::pp_%s" % (m.lower(), n)
        if (m, n) in EXTERN:
            return EXTERN[(m, n)]
        raise Exception("no printer for %s.%s" % (m, n))

    def gen_module(self, omod, rmod):
        self.out.append("pub mod %s {" % omod.lower())
        self.out.append("#![allow(unused_variables, unused_braces, clippy::all)]")
        self.out.append("use super::*;")
        for name, (d, with_path) in self.modules[omod].items():
            try:
                self.gen_decl(omod, rmod, d, with_path)
            except Exception as e:
                self.errors.append("%s.%s: %s" % (omod, name, e))
                self.out.append(
                    "pub fn pp_%s<Ex, En, T: ?Sized>(_p: &mut P<'_, Ex, En>, _x: &T) { todo!(\"%s.pp_%s: %s\") }"
                    % (d.name, omod, d.name, str(e).replace('"', "'"))
                )
        self.out.append("}")

    def gen_decl(self, omod, rmod, d, with_path):
        path = [omod]
        if d.manifest is not None and d.manifest.kind == "constr":
            path = d.manifest.name.split(".")[:-1]
        prefix = ".".join(path) + "." if with_path and path else ""
        rname = camel(d.name)
        self.var = 0
        body = []
        if (omod, d.name) in RUST_TYPE:
            rty_full = RUST_TYPE[(omod, d.name)]
            item = RItem("type", rname, [], rty_full)
            gens = []
        else:
            rm, item = self.rust_item(rmod, rname)
            if item is None:
                for other in self.rust:
                    rm, item = self.rust_item(other, rname)
                    if item is not None:
                        break
            if item is None:
                raise Exception("no Rust type %s in %s" % (rname, rmod))
            rpath = "oxidized::%s::%s" % (rm, rname)
            gens = item.generics
            rty_full = rpath + ("<%s>" % ", ".join(gens) if gens else "")
        if d.kind == "alias" and d.name == "pos":
            # `on_pos` is the method that `print_*_without_position`
            # overrides: the `[@visitors.opaque]` of `Pos.t` does not keep the
            # position.
            d.body.attrs = [a for a in d.body.attrs if a[1] != "visitors.opaque"]
        if d.kind == "alias":
            if item.kind == "type":
                body += self.walk(d.body, rust_ty_parse(item.body), "x", omod)
            elif item.kind == "tstruct":
                if d.body.kind == "tuple" and len(d.body.args) == len(item.body) and len(item.body) > 1:
                    vs = ["&x.%d" % i for i in range(len(item.body))]
                    body.append("fprintf_open_tuple(p);")
                    for i, (a, rf) in enumerate(zip(d.body.args, item.body)):
                        if i > 0:
                            body.append("comma_space(p);")
                        body += self.walk(a, rust_ty_parse(rf), vs[i], omod)
                    body.append("fprintf_close_tuple(p);")
                elif len(item.body) == 1:
                    body += self.walk(d.body, rust_ty_parse(item.body[0]), "&x.0", omod)
                else:
                    raise Exception("alias %r vs struct %s" % (d.body, item.body))
            else:
                raise Exception("alias vs %s" % item.kind)
        elif d.kind == "record":
            if item.kind != "struct" or len(item.body) != len(d.body):
                raise Exception("record vs %s" % item.kind)
            body.append('ps(p, "@[<2>{ ");'.replace('ps(p, "@[<2>{ ");', 'open_box(p, 2); ps(p, "{ ");'))
            for i, ((fname, fty), (rf, rft)) in enumerate(zip(d.body, item.body)):
                if i > 0:
                    body.append("semi_space(p);")
                label = (prefix + fname) if i == 0 else fname
                body.append('field_open(p, "%s");' % label)
                body += self.walk(fty, rust_ty_parse(rft), "&x.%s" % rf, omod)
                body.append("close_box(p);")
            body.append('space(p); ps(p, "}"); close_box(p);')
        else:
            if item.kind != "enum" or len(item.body) != len(d.body):
                raise Exception("variant vs %s (%d vs %d)" % (item.kind, len(item.body), len(d.body) if d.kind == 'variant' else -1))
            body.append("match x {")
            for (cname, cargs, _), (vname, vkind, vfields) in zip(d.body, item.body):
                label = prefix + cname
                if cargs[0] == "tuple":
                    tys = cargs[1]
                    if not tys:
                        if vkind != "unit":
                            raise Exception("%s: constant vs %s" % (cname, vkind))
                        body.append('%s::%s => ps(p, "%s"),' % (rpath, vname, label))
                        continue
                    vs = [self.fresh() for _ in tys]
                    if vkind == "tuple" and len(vfields) == len(tys):
                        body.append("%s::%s(%s) => {" % (rpath, vname, ", ".join(vs)))
                        rtys = [rust_ty_parse(f) for f in vfields]
                    elif vkind == "tuple" and len(vfields) == 1 and len(tys) > 1:
                        b = self.fresh("b")
                        body.append("%s::%s(%s) => {" % (rpath, vname, b))
                        rt = rust_ty_parse(vfields[0])
                        bexpr = b
                        while rt[0] in BOXES:
                            rt = rt[1][0]
                            bexpr = "&**" + bexpr if bexpr == b else "&**(%s)" % bexpr
                        if rt[0] != "()" or len(rt[1]) != len(tys):
                            raise Exception("%s: %d args vs %s" % (cname, len(tys), vfields[0]))
                        body.append("let (%s) = %s;" % (", ".join(vs), bexpr))
                        rtys = rt[1]
                    else:
                        raise Exception("%s: %d args vs %s %s" % (cname, len(tys), vkind, vfields))
                    if len(tys) == 1:
                        body.append('ps(p, "("); open_box(p, 2); ps(p, "%s"); space(p);' % label)
                        body += self.walk(tys[0], rtys[0], vs[0], omod)
                        body.append('close_box(p); ps(p, ")");')
                    else:
                        body.append('ps(p, "("); open_box(p, 2); ps(p, "%s ("); cut(p);' % label)
                        for i, (t, rt, v) in enumerate(zip(tys, rtys, vs)):
                            if i > 0:
                                body.append("comma_space(p);")
                            body += self.walk(t, rt, v, omod)
                        body.append('cut(p); ps(p, "))"); close_box(p);')
                    body.append("}")
                else:
                    fields = cargs[1]
                    if vkind == "struct" and len(vfields) == len(fields):
                        vs = [self.fresh() for _ in fields]
                        body.append(
                            "%s::%s { %s } => {"
                            % (rpath, vname, ", ".join("%s: %s" % (rf, v) for (rf, _), v in zip(vfields, vs)))
                        )
                        rtys = [rust_ty_parse(t) for _, t in vfields]
                        exprs = vs
                    elif vkind == "tuple" and len(vfields) == 1:
                        b = self.fresh("b")
                        body.append("%s::%s(%s) => {" % (rpath, vname, b))
                        rt = rust_ty_parse(vfields[0])
                        while rt[0] in BOXES:
                            rt = rt[1][0]
                        rm2, sitem = self.rust_item(rmod, rt[0].split("::")[-1])
                        if sitem is None or sitem.kind != "struct" or len(sitem.body) != len(fields):
                            raise Exception("%s: inline record vs %s" % (cname, vfields[0]))
                        rtys = [rust_ty_parse(t) for _, t in sitem.body]
                        exprs = ["&%s.%s" % (b, rf) for rf, _ in sitem.body]
                    else:
                        raise Exception("%s: inline record vs %s" % (cname, vkind))
                    body.append('open_box(p, 2); ps(p, "%s {"); cut(p);' % label)
                    for i, ((fname, fty), rt, e) in enumerate(zip(fields, rtys, exprs)):
                        if i > 0:
                            body.append("semi_space(p);")
                        body.append('field_open(p, "%s");' % fname)
                        body += self.walk(fty, rt, e, omod)
                        body.append("close_box(p);")
                    body.append('close_box(p); ps(p, "}");')
                    body.append("}")
            body.append("}")
        if (omod, d.name) in BYTES:
            # (`byte_string` is a `String` in some places and a `BString` in others.)
            rty_full = "(impl AsRef<[u8]> + ?Sized)"
        self.out.append("/// `pp_%s`" % d.name)
        self.out.append(
            "pub fn pp_%s<Ex, En>(p: &mut P<'_, Ex, En>, x: &%s) {" % (d.name, rty_full)
            if not gens or gens == ["Ex", "En"] or gens == ["Ex"] or gens == ["En"]
            else "pub fn pp_%s<Ex, En>(p: &mut P<'_, Ex, En>, x: &%s) {" % (d.name, rty_full)
        )
        self.out += body
        self.out.append("}")


def main():
    ast_defs_src, aast_defs_src, oxidized = sys.argv[1:4]
    modules = {}
    for omod, f in (("Ast_defs", ast_defs_src), ("Aast_defs", aast_defs_src)):
        decls = parse_decls(open(f).read())
        modules[omod] = {}
        for d, wp in decls:
            modules[omod][d.name] = (d, wp)
    rust = {}
    for rmod in ("ast_defs", "aast_defs"):
        rust[rmod] = parse_rust(open("%s/gen/%s.rs" % (oxidized, rmod)).read())
    g = Gen(modules, rust)
    g.gen_module("Ast_defs", "ast_defs")
    g.gen_module("Aast_defs", "aast_defs")
    for e in g.errors:
        print("// ERROR " + e, file=sys.stderr)
    print("\n".join(g.out))


if __name__ == "__main__":
    main()
