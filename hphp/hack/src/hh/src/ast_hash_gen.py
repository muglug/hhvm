#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the "hack" directory of this source tree.

"""Generates the generated part of `ast_hash.rs`: the `[@@deriving hash]`
folders (`hash_fold_*`) of the types of `Ast_defs` and `Aast_defs`, as
ppx_hash's expander (`ppx_hash_expander.ml`) writes them, over the
`oxidized` types.

The inputs and the matching of the OCaml declarations with the `oxidized`
ones are those of `ast_show_gen.py` (next to this file), whose parsers this
uses:

  python3 ast_hash_gen.py AST_DEFS_SRC AAST_DEFS_SRC OXIDIZED_DIR > generated.rs

The rules of ppx_hash: a record folds its fields in order, a tuple its
components in order; a variant with more than one constructor folds the
index of the constructor (`Hash.fold_int`, counting every constructor in
declaration order) and then its arguments, a variant with a single
constructor only its arguments; a component or field marked `[@hash.ignore]`
(or `[@compare.ignore]`, `[@ignore]`) is not folded; `list` folds its length
then its elements, `option` 0 or 1 then the value, `bool` 0 or 1 as an int,
`string` its bytes (`Hash.fold_string`), `unit` nothing.
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from ast_show_gen import (  # noqa: E402
    BOXES,
    BYTES,
    RUST_TYPE,
    Gen,
    RItem,
    Ty,
    camel,
    parse_decls,
    parse_rust,
    rust_ty_parse,
    rust_ty_str,
)

# Folders of types of other modules (hand-written in ast_hash.rs).
EXTERN = {
    ("Pos", "t"): "super::hash_fold_pos_t",
    ("Local_id", "t"): "super::hash_fold_local_id_t",
    ("File_info", "mode"): "super::hash_fold_file_info_mode",
    ("Namespace_env", "env"): "super::hash_fold_namespace_env",
}

IGNORE = ("hash.ignore", "compare.ignore", "ignore")


def ignored(ty):
    return any(a[1] in IGNORE for a in ty.attrs)


class HashGen(Gen):
    # statements folding `expr` (a Rust expression of type `&rty`) as the
    # OCaml type `ty` is folded
    def walk(self, ty, rty, expr, omod):
        if ignored(ty):
            return []
        out = []
        head, rargs = rty
        if head in BOXES:
            return self.walk(ty, rargs[0], "&**(%s)" % expr, omod)
        if ty.kind == "var":
            if ty.name == "ex":
                return ["{ let f = h.ex; f(h, %s); }" % expr]
            if ty.name == "en":
                return ["{ let f = h.en; f(h, %s); }" % expr]
            raise Exception("type variable %s" % ty.name)
        if ty.kind == "tuple":
            if head != "()" or len(rargs) != len(ty.args):
                raise Exception("tuple %r vs %s" % (ty, rust_ty_str(rty)))
            vs = [self.fresh() for _ in ty.args]
            out.append("{")
            out.append("let (%s) = %s;" % (", ".join(vs) + ("," if len(vs) == 1 else ""), expr))
            for a, ra, v in zip(ty.args, rargs, vs):
                out += self.walk(a, ra, v, omod)
            out.append("}")
            return out
        name = ty.name
        if name == "list":
            if head not in ("Vec", "std::vec::Vec"):
                raise Exception("list vs %s" % rust_ty_str(rty))
            v = self.fresh("x")
            out.append("fold_int(&mut h.s, (%s).len() as i64);" % expr)
            out.append("for %s in (%s).iter() {" % (v, expr))
            out += self.walk(ty.args[0], rargs[0], v, omod)
            out.append("}")
            return out
        if name == "option":
            if head not in ("Option", "std::option::Option"):
                raise Exception("option vs %s" % rust_ty_str(rty))
            v = self.fresh("x")
            out.append("match %s {" % expr)
            out.append("None => fold_int(&mut h.s, 0),")
            out.append("Some(%s) => {" % v)
            out.append("fold_int(&mut h.s, 1);")
            out += self.walk(ty.args[0], rargs[0], v, omod)
            out.append("}")
            out.append("}")
            return out
        if name == "int":
            return ["fold_int(&mut h.s, *%s as i64);" % expr]
        if name == "bool":
            return ["fold_int(&mut h.s, if *%s { 1 } else { 0 });" % expr]
        if name in ("string", "String.t"):
            return ["fold_bytes(&mut h.s, %s);" % expr]
        if name == "float":
            return ["fold_float(&mut h.s, *%s);" % expr]
        if name == "unit":
            return []
        # a named type
        if "." in name:
            m, n = name.rsplit(".", 1)
        else:
            m, n = omod, name
        fn = self.fn_path(m, n, ty)
        return ["%s(h, %s);" % (fn, expr)]

    def fn_path(self, m, n, ty):
        if m in self.modules and n in self.modules[m]:
            for a in ty.args:
                if a.kind != "var":
                    raise Exception("non-variable type argument of %s.%s" % (m, n))
            return "%s::hash_fold_%s" % (m.lower(), n)
        if (m, n) in EXTERN:
            return EXTERN[(m, n)]
        raise Exception("no folder for %s.%s" % (m, n))

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
                    "pub fn hash_fold_%s<Ex, En, T: ?Sized>(_h: &mut H<Ex, En>, _x: &T) { todo!(\"%s.hash_fold_%s: %s\") }"
                    % (d.name, omod, d.name, str(e).replace('"', "'"))
                )
        self.out.append("}")

    def gen_decl(self, omod, rmod, d, with_path):
        rname = camel(d.name)
        self.var = 0
        body = []
        if (omod, d.name) in RUST_TYPE:
            rty_full = RUST_TYPE[(omod, d.name)]
            item = RItem("type", rname, [], rty_full)
            gens = []
            rpath = rty_full
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
        if d.kind == "alias":
            if item.kind == "type":
                body += self.walk(d.body, rust_ty_parse(item.body), "x", omod)
            elif item.kind == "tstruct":
                if d.body.kind == "tuple" and len(d.body.args) == len(item.body) and len(item.body) > 1:
                    for i, (a, rf) in enumerate(zip(d.body.args, item.body)):
                        body += self.walk(a, rust_ty_parse(rf), "&x.%d" % i, omod)
                elif len(item.body) == 1:
                    body += self.walk(d.body, rust_ty_parse(item.body[0]), "&x.0", omod)
                else:
                    raise Exception("alias %r vs struct %s" % (d.body, item.body))
            else:
                raise Exception("alias vs %s" % item.kind)
        elif d.kind == "record":
            if item.kind != "struct" or len(item.body) != len(d.body):
                raise Exception("record vs %s" % item.kind)
            for (fname, fty), (rf, rft) in zip(d.body, item.body):
                body += self.walk(fty, rust_ty_parse(rft), "&x.%s" % rf, omod)
        else:
            if item.kind != "enum" or len(item.body) != len(d.body):
                raise Exception(
                    "variant vs %s (%d vs %d)"
                    % (item.kind, len(item.body), len(d.body) if d.kind == "variant" else -1)
                )
            several = len(d.body) > 1
            body.append("match x {")
            for index, ((cname, cargs, _), (vname, vkind, vfields)) in enumerate(zip(d.body, item.body)):
                tag = ["fold_int(&mut h.s, %d);" % index] if several else []
                if cargs[0] == "tuple":
                    tys = cargs[1]
                    if not tys:
                        if vkind != "unit":
                            raise Exception("%s: constant vs %s" % (cname, vkind))
                        body.append("%s::%s => { %s }" % (rpath, vname, " ".join(tag)))
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
                    body += tag
                    for t, rt, v in zip(tys, rtys, vs):
                        body += self.walk(t, rt, v, omod)
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
                    body += tag
                    for (fname, fty), rt, e in zip(fields, rtys, exprs):
                        body += self.walk(fty, rt, e, omod)
                    body.append("}")
            body.append("}")
        if (omod, d.name) in BYTES:
            rty_full = "(impl AsRef<[u8]> + ?Sized)"
        self.out.append("/// `hash_fold_%s`" % d.name)
        self.out.append("pub fn hash_fold_%s<Ex, En>(h: &mut H<Ex, En>, x: &%s) {" % (d.name, rty_full))
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
    g = HashGen(modules, rust)
    g.gen_module("Ast_defs", "ast_defs")
    g.gen_module("Aast_defs", "aast_defs")
    for e in g.errors:
        print("// ERROR " + e, file=sys.stderr)
    print("\n".join(g.out))


if __name__ == "__main__":
    main()
