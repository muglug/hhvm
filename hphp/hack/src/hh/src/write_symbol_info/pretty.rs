// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Write_symbol_info.Pretty` (`write_symbol_info/pretty.ml`): pretty-printers
//! for hints and contexts.

use oxidized::aast;
use oxidized::aast_defs::Hint;
use oxidized::aast_defs::Hint_;
use oxidized::ast_defs;

use super::glean::hack::field_class_const;
use super::glean::hack::hint;
use super::glean::hack::name;
use super::glean::hack::shape_kv;
use super::glean::hack::type_;
use super::util;
use crate::full_fidelity_source_text;
use crate::typing_print;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Pos {
    pub start: isize,
    pub length: isize,
}

pub fn compare_pos(a: &Pos, b: &Pos) -> std::cmp::Ordering {
    a.cmp(b)
}

/// The state of `hint_to_string_and_symbols`: the OCaml's module-level
/// `buf` (reset at each call) and the `xrefs` it collects.
struct Printer {
    buf: Vec<u8>,
    xrefs: Vec<(oxidized::pos::Pos, Pos)>,
}

/// `` `E | `L | `U `` of `parse_bound`.
#[derive(Clone, Copy)]
enum Bound {
    E,
    L,
    U,
}

impl Printer {
    fn append(&mut self, annot: Option<&oxidized::pos::Pos>, s: &[u8]) {
        let length = s.len() as isize;
        let pos = Pos {
            start: self.buf.len() as isize,
            length,
        };
        self.buf.extend_from_slice(s);
        if let Some(file_pos) = annot {
            self.xrefs.push((file_pos.clone(), pos))
        }
    }

    fn a(&mut self, s: &str) {
        self.append(None, s.as_bytes())
    }

    fn parse_gen_seq<X>(&mut self, sep: &str, l: &[X], mut f: impl FnMut(&mut Self, &X)) {
        match l {
            [] => {}
            [x] => f(self, x),
            [x, xs @ ..] => {
                f(self, x);
                for x in xs {
                    self.a(sep);
                    f(self, x)
                }
            }
        }
    }

    fn parse(&mut self, is_ctx: bool, t: &Hint) {
        match &*t.1 {
            Hint_::Hmixed => self.a("mixed"),
            Hint_::Hwildcard => self.a("_"),
            Hint_::Hnonnull => self.a("nonnull"),
            Hint_::Hthis => self.a("this"),
            Hint_::Hdynamic => self.a("dynamic"),
            Hint_::Hnothing => self.a("nothing"),
            Hint_::Hoption(hint) => {
                self.a("?");
                self.parse(is_ctx, hint)
            }
            Hint_::Hlike(hint) => {
                self.a("~");
                self.parse(is_ctx, hint)
            }
            Hint_::Hsoft(hint) => {
                self.a("@");
                self.parse(is_ctx, hint)
            }
            Hint_::Hvar(v) => self.a(v),
            Hint_::Habstr(name) => self.a(&typing_print::strip_ns(name)),
            Hint_::Happly(id, hints) if id.1 == "\\HH\\supportdyn" && hints.len() == 1 => {
                self.parse(is_ctx, &hints[0])
            }
            Hint_::Happly(id, _) if id.1 == "\\HH\\string" => self.a("string"),
            Hint_::Happly(ast_defs::Id(file_pos, cn), hints) if hints.is_empty() => {
                self.append(Some(file_pos), typing_print::strip_ns(cn).as_bytes())
            }
            Hint_::Happly(ast_defs::Id(file_pos, cn), hints) => {
                self.append(Some(file_pos), typing_print::strip_ns(cn).as_bytes());
                self.a("<");
                self.parse_gen_seq(", ", hints, |p, h| p.parse(is_ctx, h));
                self.a(">")
            }
            // TODO optional and variadic components T201398626 T201398652
            Hint_::Htuple(aast::TupleInfo { required, extra: _ }) => {
                self.a("(");
                self.parse_gen_seq(", ", required, |p, h| p.parse(is_ctx, h));
                self.a(")")
            }
            Hint_::Hprim(p) => self.a(&crate::aast_defs::string_of_tprim(*p)),
            Hint_::Haccess(hint, sids) => {
                self.parse(is_ctx, hint);
                for ast_defs::Id(file_pos, sid) in sids {
                    self.a("::");
                    self.append(Some(file_pos), sid.as_bytes())
                }
            }
            Hint_::Hfun(hf) => {
                self.a("(function(");
                self.parse_fun(&hf.param_tys, &hf.param_info, &hf.variadic_ty);
                self.a(")");
                if let Some(aast::Contexts(_, ctxs)) = &hf.ctxs {
                    self.a("[");
                    self.parse_gen_seq(", ", ctxs, |p, h| p.parse(true, h));
                    self.a("]")
                }
                self.a(": ");
                self.parse(is_ctx, &hf.return_ty);
                self.a(")")
            }
            Hint_::HfunContext(name) => {
                self.a("ctx ");
                self.a(&typing_print::strip_ns(name))
            }
            Hint_::HclassPtr(kind, hint) => {
                match kind {
                    aast::ClassPtrKind::CKclass => self.a("class<"),
                    aast::ClassPtrKind::CKenum => self.a("enum<"),
                }
                self.parse(is_ctx, hint);
                self.a(">")
            }
            Hint_::Hshape(aast::NastShapeInfo {
                allows_unknown_fields,
                field_map,
                unknown_fields_type,
            }) => {
                self.a("shape(");
                self.parse_shape(*allows_unknown_fields, field_map, unknown_fields_type);
                self.a(")")
            }
            Hint_::Hrefinement(hint, members) => {
                self.parse(false, hint);
                self.a(" with { ");
                self.parse_gen_seq("; ", members, |p, m| p.parse_member(m));
                self.a(" }")
            }
            Hint_::HvecOrDict(None, vhint) => {
                self.a("vec_or_dict");
                self.a("<");
                self.parse(is_ctx, vhint);
                self.a(">")
            }
            Hint_::HvecOrDict(Some(khint), vhint) => {
                self.a("vec_or_dict");
                self.a("<");
                self.parse(is_ctx, khint);
                self.a(", ");
                self.parse(is_ctx, vhint);
                self.a(">")
            }
            Hint_::Hunion(hints) => {
                self.a("(");
                self.parse_gen_seq("|", hints, |p, h| p.parse(is_ctx, h));
                self.a(")")
            }
            Hint_::Hintersection(hints) if is_ctx => {
                self.a("[");
                self.parse_gen_seq(", ", hints, |p, h| p.parse(is_ctx, h));
                self.a("]")
            }
            Hint_::Hintersection(hints) => {
                self.a("(");
                self.parse_gen_seq("&", hints, |p, h| p.parse(is_ctx, h));
                self.a(")")
            }
        }
    }

    fn parse_bound(&mut self, is_ctx: bool, (kind, hint): &(Bound, &Hint)) {
        let constraint_ = match kind {
            Bound::E => "= ",
            Bound::L => "super ",
            Bound::U => "as ",
        };
        self.a(constraint_);
        self.parse(is_ctx, hint)
    }

    fn parse_member(&mut self, m: &aast::Refinement) {
        match m {
            aast::Refinement::Rtype(ident, ref_) => {
                self.a("type ");
                self.a(&ident.1);
                self.a(" ");
                let bounds: Vec<(Bound, &Hint)> = match ref_ {
                    aast::TypeRefinement::TRexact(hint) => vec![(Bound::E, hint)],
                    aast::TypeRefinement::TRloose(aast::TypeRefinementBounds { lower, upper }) => lower
                        .iter()
                        .map(|x| (Bound::L, x))
                        .chain(upper.iter().map(|x| (Bound::U, x)))
                        .collect(),
                };
                self.parse_gen_seq(" ", &bounds, |p, b| p.parse_bound(false, b))
            }
            aast::Refinement::Rctx(ident, ref_) => {
                self.a("ctx ");
                self.a(&ident.1);
                self.a(" ");
                let bounds: Vec<(Bound, &Hint)> = match ref_ {
                    aast::CtxRefinement::CRexact(hint) => vec![(Bound::E, hint)],
                    aast::CtxRefinement::CRloose(aast::CtxRefinementBounds { lower, upper }) => lower
                        .iter()
                        .map(|x| (Bound::L, x))
                        .chain(upper.iter().map(|x| (Bound::U, x)))
                        .collect(),
                };
                self.parse_gen_seq(" ", &bounds, |p, b| p.parse_bound(true, b))
            }
        }
    }

    fn parse_shape(&mut self, open_: bool, nsi_field_map: &[aast::ShapeElement], unknown_fields_type: &Option<Hint>) {
        self.parse_gen_seq(", ", nsi_field_map, |p, e| match e {
            aast::ShapeElement::SEField(sfi) => p.parse_shape_field(sfi),
            aast::ShapeElement::SESplat(h) => {
                p.a("...");
                p.parse(false, h)
            }
        });
        match unknown_fields_type {
            Some(h) => {
                if !nsi_field_map.is_empty() {
                    self.a(", ");
                }
                self.parse(false, h);
                self.a("...")
            }
            None => {
                if open_ {
                    if !nsi_field_map.is_empty() {
                        self.a(", ");
                    }
                    self.a("...")
                }
            }
        }
    }

    fn parse_shape_field(&mut self, f: &aast::ShapeFieldInfo) {
        if f.optional {
            self.a("?");
        }
        self.parse_shape_field_name(&f.name);
        self.a(" => ");
        self.parse(false, &f.hint)
    }

    fn parse_shape_field_name(&mut self, n: &ast_defs::ShapeFieldName) {
        match n {
            ast_defs::ShapeFieldName::SFlitStr((_, s)) => {
                let mut v = b"'".to_vec();
                v.extend_from_slice(s);
                v.push(b'\'');
                self.append(None, &v)
            }
            ast_defs::ShapeFieldName::SFclassname(ast_defs::Id(_, c)) => {
                self.a(&format!("nameof {}", typing_print::strip_ns(c)))
            }
            ast_defs::ShapeFieldName::SFclassConst(ast_defs::Id(pos, c), (_, s)) => {
                self.append(Some(pos), typing_print::strip_ns(c).as_bytes());
                self.a("::");
                self.a(s)
            }
        }
    }

    fn parse_variadic(&mut self, first: bool, variadic: &Option<Hint>) {
        if let Some(hint) = variadic {
            if !first {
                self.a(", ");
            }
            self.parse(false, hint);
            self.a("...")
        }
    }

    fn parse_fun(&mut self, hf_param_tys: &[Hint], hf_param_info: &[Option<aast::HfParamInfo>], variadic: &Option<Hint>) {
        let hf_param_modifiers: Vec<(bool, bool, bool, bool)> = hf_param_info
            .iter()
            .map(|i| match i {
                None => (false, false, false, false),
                Some(i) => {
                    let inout = match i.kind {
                        ast_defs::ParamKind::Pnormal => false,
                        ast_defs::ParamKind::Pinout(_) => true,
                    };
                    let readonly = i.readonlyness.is_some();
                    let named = i.named.is_some();
                    let optional = i.optional.is_some();
                    (inout, readonly, named, optional)
                }
            })
            .collect();
        // `List.zip_exn`
        if hf_param_modifiers.len() != hf_param_tys.len() {
            panic!("List.zip_exn: lists of different lengths")
        }
        let ats: Vec<_> = hf_param_modifiers.into_iter().zip(hf_param_tys.iter()).collect();
        match ats.as_slice() {
            [] => self.parse_variadic(true, variadic),
            ats => {
                self.parse_gen_seq(", ", ats, |p, a| p.parse_annotated_hint(a));
                self.parse_variadic(false, variadic)
            }
        }
    }

    fn parse_annotated_hint(&mut self, ((inout, readonly, named, optional), hint): &((bool, bool, bool, bool), &Hint)) {
        if *named {
            self.a("named ");
        }
        if *optional {
            self.a("optional ");
        }
        if *inout {
            self.a("inout ");
        }
        if *readonly {
            self.a("readonly ");
        }
        self.parse(false, hint)
    }
}

/// Pretty-printer for hints. Also generate xrefs
/// (maps symbols within types to their defining entity).
///
/// The xrefs are in the OCaml's order (consed: the last one appended first).
pub fn hint_to_string_and_symbols(is_ctx: bool, hint: &Hint) -> (String, Vec<(oxidized::pos::Pos, Pos)>) {
    let mut p = Printer {
        buf: Vec::with_capacity(1024),
        xrefs: vec![],
    };
    p.parse(is_ctx, hint);
    p.xrefs.reverse();
    (String::from_utf8_lossy(&p.buf).into_owned(), p.xrefs)
}

pub fn hint_to_string(is_ctx: bool, hint: &Hint) -> String {
    hint_to_string_and_symbols(is_ctx, hint).0
}

/// Pretty-printer for expressions. Fetch representation from the source.
/// Strip enclosing double/single quotes if any.
/// TODO: 1. replace with Hint_print.pp_expr. 2. why stripping?
pub fn expr_to_string<Ex, En>(source_text: &full_fidelity_source_text::T, expr: &aast::Expr<Ex, En>) -> String {
    let pos = &expr.1;
    let strip_nested_quotes = |s: String| -> String {
        let b = s.as_bytes();
        let len = b.len();
        // (`str.[0]` raises `Invalid_argument "index out of bounds"` on an
        // empty string, before the length is tested.)
        let firstc = *b.first().expect("index out of bounds");
        let lastc = b[len - 1];
        if len >= 2 && ((b'"' == firstc && b'"' == lastc) || (b'\'' == firstc && b'\'' == lastc)) {
            String::from_utf8_lossy(&b[1..len - 1]).into_owned()
        } else {
            s
        }
    };
    // Replace any codepoints that are not valid UTF-8 with
    // the unrepresentable character.
    let check_utf8 = |s: &[u8]| -> String {
        let mut b = String::with_capacity(s.len());
        for item in util::uutf_decode(s) {
            match item {
                Ok(u) => b.push(u),
                Err(_) => b.push('\u{FFFD}'),
            }
        }
        b
    };
    let source_at_span = |pos: &oxidized::pos::Pos| -> String {
        let st = pos.start_offset() as isize;
        let fi = pos.end_offset() as isize;
        let source_text = full_fidelity_source_text::sub(source_text, st, fi - st);
        check_utf8(&source_text)
    };
    strip_nested_quotes(source_at_span(pos))
}

/// Convert ContainerName<TParam> to ContainerName - see D21428855
pub fn strip_tparams(name: &str) -> String {
    match name.find('<') {
        None => name.to_string(),
        Some(i) => name[..i].to_string(),
    }
}

pub fn hint_to_angle(h: &Hint) -> hint::T {
    let key = |k: hint::Key| hint::T::key(k);
    match &*h.1 {
        Hint_::Hlike(h) => key(hint::Key::Like(hint_to_angle(h))),
        Hint_::Hsoft(h) => key(hint::Key::Like(hint_to_angle(h))),
        Hint_::Hvar(h) => key(hint::Key::Var_(h.clone())),
        // TODO splat fields T203492030
        Hint_::Htuple(aast::TupleInfo {
            required,
            extra: aast::TupleExtra::Hextra(aast::TupleExtraInfo { optional, variadic }),
        }) => {
            let req = required.iter().map(hint_to_angle).collect();
            let opt = optional.iter().map(hint_to_angle).collect();
            let variadic = variadic.as_ref().map(hint_to_angle);
            key(hint::Key::Tuple(hint::Tuple { req, opt, variadic }))
        }
        Hint_::Hprim(t) => key(hint::Key::Prim(type_::T::key(crate::aast_defs::string_of_tprim(*t)))),
        // (`Naming_special_names.Classes.cString`.)
        Hint_::Happly(ast_defs::Id(_, cn), _) if cn == "\\HH\\string" => {
            key(hint::Key::Prim(type_::T::key("string".to_string())))
        }
        // TODO(T199610905) update glean schema
        Hint_::HclassPtr(_kind, hint) => key(hint::Key::ClassArgs(hint_to_angle(hint))),
        Hint_::HfunContext(c) => key(hint::Key::FunContext(c.clone())),
        Hint_::HvecOrDict(maybe_k, v) => key(hint::Key::VectOrDict(hint::VectOrDict {
            maybe_key: maybe_k.as_ref().map(hint_to_angle),
            value_: hint_to_angle(v),
        })),
        Hint_::Hintersection(hints) => {
            let values = hints.iter().map(hint_to_angle).collect();
            key(hint::Key::Intersection(values))
        }
        Hint_::Hunion(hints) => {
            let values = hints.iter().map(hint_to_angle).collect();
            key(hint::Key::Union_(values))
        }
        Hint_::Hoption(h) => key(hint::Key::Option(hint_to_angle(h))),
        Hint_::Hshape(aast::NastShapeInfo {
            allows_unknown_fields,
            field_map,
            unknown_fields_type,
        }) => {
            let shape_field_name_to_hint = |n: &ast_defs::ShapeFieldName| match n {
                ast_defs::ShapeFieldName::SFlitStr((_, s)) => {
                    shape_kv::Key::SfLitString(String::from_utf8_lossy(s).into_owned())
                }
                ast_defs::ShapeFieldName::SFclassname(ast_defs::Id(_, c)) => {
                    shape_kv::Key::SfClassConst(field_class_const::T {
                        container: util::make_qname(c),
                        name: name::T::key("class".to_string()),
                    })
                }
                ast_defs::ShapeFieldName::SFclassConst(ast_defs::Id(_pos, c), (_, s)) => {
                    shape_kv::Key::SfClassConst(field_class_const::T {
                        container: util::make_qname(c),
                        name: name::T::key(s.clone()),
                    })
                }
            };
            let f = |sfi: &aast::ShapeFieldInfo| shape_kv::T {
                key: shape_field_name_to_hint(&sfi.name),
                value: hint_to_angle(&sfi.hint),
                opt: sfi.optional,
            };
            let fields: Option<Vec<shape_kv::T>> = field_map
                .iter()
                .map(|e| match e {
                    aast::ShapeElement::SEField(sfi) => Some(f(sfi)),
                    aast::ShapeElement::SESplat(_) => None,
                })
                .collect();
            match (unknown_fields_type, fields) {
                (None, Some(map_)) => key(hint::Key::Shape(hint::Shape {
                    open_: *allows_unknown_fields,
                    map_,
                })),
                (Some(_), _) | (_, None) => key(hint::Key::Other(type_::T::key(hint_to_string(false, h)))),
            }
        }
        Hint_::Happly(ast_defs::Id(_file_pos, cn), hints) => {
            let values = hints.iter().map(hint_to_angle).collect();
            key(hint::Key::Apply(hint::Apply {
                class_name: util::make_qname(cn),
                values,
            }))
        }
        Hint_::Hmixed => key(hint::Key::Mixed(())),
        Hint_::Hwildcard => key(hint::Key::Wildcard(())),
        Hint_::Hnonnull => key(hint::Key::Nonnull(())),
        Hint_::Hdynamic => key(hint::Key::Dynamic(())),
        Hint_::Hnothing => key(hint::Key::Nothing(())),
        Hint_::Hthis => key(hint::Key::This_(())),
        Hint_::Hrefinement(..) | Hint_::Hfun(_) | Hint_::Htuple(_) | Hint_::Haccess(_, _) | Hint_::Habstr(_) => {
            key(hint::Key::Other(type_::T::key(hint_to_string(false, h))))
        }
    }
}
