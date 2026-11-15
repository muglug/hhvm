// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `naming/nast.ml`. See `hh/PORTING.md`.
//!
//! The types are those of `oxidized::nast` (`Aast` with no annotations),
//! re-exported; `Nast.program` is [`Program`], `Nast.def` is [`Def`], ...
//!
//! # What is ported
//!
//! The functions that `typing/`, `decl/`, `naming/`, `typing/tast_check/`,
//! `typing/nast_check/` and `providers/` call, each in full:
//! [`class_id_to_str`], [`equal_class_id_`] (derived), [`is_kvc_kind`],
//! [`get_kvc_kind`], [`kvc_kind_to_name`], [`is_vc_kind`], [`get_vc_kind`],
//! [`vc_kind_to_name`], [`get_xhp_attr_expr`], [`get_defs`],
//! [`get_def_names`], [`deregister_ignored_attributes`] and the visitor
//! [`visitor_deprecated`]; and, being small, [`show_tprim`],
//! [`map_xhp_attr`] and [`get_simple_xhp_attrs`].
//!
//! Not ported (nothing in those directories calls them):
//! `remove_pos_and_docblock` and its `ast_no_pos_or_docblock_mapper`,
//! `generate_ast_decl_hash` (a digest of the marshalled OCaml value, which
//! has no Rust counterpart), and the derived `equal_expr`,
//! `equal_user_attribute`, `pp_*` and `show_*` (`show_program`, `show_expr`,
//! `show_user_attribute`, `show_sid`).
//!
//! # Representation
//!
//! - `program` is `def list` in OCaml and a newtype here: the functions take
//!   and return a [`Program`]; the visitor, which also visits the `def list`
//!   of a namespace, takes a `&[Def]`.
//! - A `block` (and a `finally_block`) is a `stmt list`: the visitor takes a
//!   `&[Stmt]`.

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::aast_visitor::AstParams;
use oxidized::aast_visitor::NodeMut;
use oxidized::aast_visitor::VisitorMut;
use oxidized::file_info;
pub use oxidized::nast::*;

pub fn show_tprim(t: &Tprim) -> String {
    match t {
        Tprim::Tnull => sn::typehints::NULL,
        Tprim::Tvoid => sn::typehints::VOID,
        Tprim::Tint => sn::typehints::INT,
        Tprim::Tbool => sn::typehints::BOOL,
        Tprim::Tfloat => sn::typehints::FLOAT,
        Tprim::Tnum => sn::typehints::NUM,
        Tprim::Tresource => sn::typehints::RESOURCE,
        Tprim::Tarraykey => sn::typehints::ARRAYKEY,
        Tprim::Tnoreturn => sn::typehints::NORETURN,
    }
    .to_string()
}

/// `module ShapeMap = Ast_defs.ShapeMap`
pub use oxidized::shape_map;

pub fn class_id_to_str<Ex, En>(cid: &aast::ClassId_<Ex, En>) -> String {
    match cid {
        aast::ClassId_::CIparent => sn::classes::PARENT.to_string(),
        aast::ClassId_::CIself => sn::classes::SELF.to_string(),
        aast::ClassId_::CIstatic => sn::classes::STATIC.to_string(),
        aast::ClassId_::CIexpr(aast::Expr(_, _, aast::Expr_::This)) => {
            sn::special_idents::THIS.to_string()
        }
        aast::ClassId_::CIexpr(aast::Expr(_, _, aast::Expr_::Lvar(lid))) => {
            let aast::Lid(_, x) = &**lid;
            format!("${}", crate::local_id::to_string(x))
        }
        aast::ClassId_::CIexpr(aast::Expr(_, _, aast::Expr_::Lplaceholder(_))) => {
            sn::special_idents::PLACEHOLDER.to_string()
        }
        aast::ClassId_::CIexpr(aast::Expr(_, _, aast::Expr_::Dollardollar(_))) => {
            sn::special_idents::DOLLAR_DOLLAR.to_string()
        }
        aast::ClassId_::CIexpr(_) => panic!("Nast.class_id_to_str: assert false"),
        aast::ClassId_::CI(Id(_, x)) => x.clone(),
        aast::ClassId_::CIreified(Id(_, x)) => x.clone(),
    }
}

/// `equal_class_id_` (`[@@deriving eq]`)
pub fn equal_class_id_(x: &ClassId_, y: &ClassId_) -> bool {
    x == y
}

pub fn is_kvc_kind(name: &str) -> bool {
    name == sn::collections::MAP
        || name == sn::collections::IMM_MAP
        || name == sn::collections::DICT
}

pub fn get_kvc_kind(name: &str) -> KvcKind {
    match name {
        x if x == sn::collections::MAP => KvcKind::Map,
        x if x == sn::collections::IMM_MAP => KvcKind::ImmMap,
        x if x == sn::collections::DICT => KvcKind::Dict,
        _ => {
            crate::diagnostics::internal_error(
                Pos::NONE,
                &format!("Invalid KeyValueCollection name: {}", name),
            );
            KvcKind::Map
        }
    }
}

pub fn kvc_kind_to_name(kind: &KvcKind) -> String {
    match kind {
        KvcKind::Map => sn::collections::MAP,
        KvcKind::ImmMap => sn::collections::IMM_MAP,
        KvcKind::Dict => sn::collections::DICT,
    }
    .to_string()
}

pub fn is_vc_kind(name: &str) -> bool {
    name == sn::collections::VECTOR
        || name == sn::collections::IMM_VECTOR
        || name == sn::collections::SET
        || name == sn::collections::IMM_SET
        || name == sn::collections::KEYSET
        || name == sn::collections::VEC
}

pub fn get_vc_kind(name: &str) -> VcKind {
    match name {
        x if x == sn::collections::VECTOR => VcKind::Vector,
        x if x == sn::collections::IMM_VECTOR => VcKind::ImmVector,
        x if x == sn::collections::VEC => VcKind::Vec,
        x if x == sn::collections::SET => VcKind::Set,
        x if x == sn::collections::IMM_SET => VcKind::ImmSet,
        x if x == sn::collections::KEYSET => VcKind::Keyset,
        _ => {
            crate::diagnostics::internal_error(
                Pos::NONE,
                &format!("Invalid ValueCollection name: {}", name),
            );
            VcKind::Set
        }
    }
}

pub fn vc_kind_to_name(kind: &VcKind) -> String {
    match kind {
        VcKind::Vector => sn::collections::VECTOR,
        VcKind::ImmVector => sn::collections::IMM_VECTOR,
        VcKind::Vec => sn::collections::VEC,
        VcKind::Set => sn::collections::SET,
        VcKind::ImmSet => sn::collections::IMM_SET,
        VcKind::Keyset => sn::collections::KEYSET,
    }
    .to_string()
}

// XHP attribute helpers
pub fn map_xhp_attr(
    f: impl FnOnce(Pstring) -> Pstring,
    g: impl FnOnce(Expr) -> Expr,
    attr: XhpAttribute,
) -> XhpAttribute {
    match attr {
        XhpAttribute::XhpSimple(XhpSimple {
            name: id,
            type_: xs_type,
            expr: e,
        }) => {
            // The fields of an OCaml record are evaluated from the last to
            // the first.
            let xs_expr = g(e);
            let xs_name = f(id);
            XhpAttribute::XhpSimple(XhpSimple {
                name: xs_name,
                type_: xs_type,
                expr: xs_expr,
            })
        }
        XhpAttribute::XhpSpread(e) => XhpAttribute::XhpSpread(g(e)),
    }
}

pub fn get_xhp_attr_expr<Ex, En>(attr: aast::XhpAttribute<Ex, En>) -> aast::Expr<Ex, En> {
    match attr {
        aast::XhpAttribute::XhpSimple(aast::XhpSimple { expr: e, .. })
        | aast::XhpAttribute::XhpSpread(e) => e,
    }
}

pub fn get_simple_xhp_attrs<Ex, En>(
    attrs: Vec<aast::XhpAttribute<Ex, En>>,
) -> Vec<(Pstring, aast::Expr<Ex, En>)> {
    attrs
        .into_iter()
        .filter_map(|attr| match attr {
            aast::XhpAttribute::XhpSimple(aast::XhpSimple {
                name: id, expr: e, ..
            }) => Some((id, e)),
            aast::XhpAttribute::XhpSpread(_) => None,
        })
        .collect()
}

/// Definitions appearing in a Nast.program
#[derive(Clone, Debug)]
pub struct Defs {
    pub funs: Vec<(file_info::Id, FunDef)>,
    pub classes: Vec<(file_info::Id, Class_)>,
    pub typedefs: Vec<(file_info::Id, Typedef)>,
    pub constants: Vec<(file_info::Id, Gconst)>,
    pub modules: Vec<(file_info::Id, ModuleDef)>,
    pub stmts: Vec<(file_info::Id, Stmt)>,
}

/// `File_info.pos_full`
fn pos_full(
    (p, name, decl_hash): (Pos, String, Option<file_info::decl_hash::DeclHash>),
) -> file_info::Id {
    let pos = file_info::Pos::Full(p);
    file_info::Id {
        pos,
        name,
        decl_hash,
    }
}

/// Given a Nast.program, give me the list of entities it defines
pub fn get_defs(ast: Program) -> Defs {
    // fold_right traverses the file from top to bottom, and as such gives nicer
    // error messages than fold_left. E.g. in the case where a function is
    // declared twice in the same file, the error will say that the declaration
    // with the larger line number is a duplicate.
    let to_id = |Id(a, b): &Id| (a.clone(), b.clone(), None);
    // TODO(hgoldstein): Just have this return four values, not five
    //
    // `List.fold_right`: the definitions are seen from the last to the first
    // (the statements are numbered in that order), and each is consed onto
    // its list. Here each is pushed, and the lists are reversed at the end.
    fn get_defs_(
        ast: Vec<Def>,
        acc: (Defs, isize),
        to_id: &impl Fn(&Id) -> (Pos, String, Option<file_info::decl_hash::DeclHash>),
    ) -> (Defs, isize) {
        let mut acc = acc;
        for def in ast.into_iter().rev() {
            let (mut defs, stmt_count) = acc;
            acc = match def {
                Def::Fun(f) => {
                    let f = (pos_full(to_id(&f.name)), *f);
                    defs.funs.push(f);
                    (defs, stmt_count)
                }
                Def::Class(c) => {
                    let c = (pos_full(to_id(&c.name)), *c);
                    defs.classes.push(c);
                    (defs, stmt_count)
                }
                Def::Typedef(t) => {
                    let t = (pos_full(to_id(&t.name)), *t);
                    defs.typedefs.push(t);
                    (defs, stmt_count)
                }
                Def::Constant(cst) => {
                    let cst = (pos_full(to_id(&cst.name)), *cst);
                    defs.constants.push(cst);
                    (defs, stmt_count)
                }
                Def::Module(md) => {
                    let md = (pos_full(to_id(&md.name)), *md);
                    defs.modules.push(md);
                    (defs, stmt_count)
                }
                Def::Stmt(st) => {
                    let pos = st.0.clone();
                    let id = format!("#stmt_{}", stmt_count);
                    let st = (pos_full((pos, id, None)), *st);
                    defs.stmts.push(st);
                    (defs, stmt_count + 1)
                }
                Def::Namespace(ns) => {
                    let (_, ds) = *ns;
                    get_defs_(ds, (defs, stmt_count), to_id)
                }
                Def::ClassAlias(_)
                | Def::NamespaceUse(_)
                | Def::SetNamespaceEnv(_)
                | Def::SetModule(_) => (defs, stmt_count),
                Def::FileAttributes(_) => (defs, stmt_count),
            };
        }
        acc
    }
    let acc = (
        Defs {
            funs: vec![],
            classes: vec![],
            typedefs: vec![],
            constants: vec![],
            modules: vec![],
            stmts: vec![],
        },
        0,
    );
    let (mut defs, _) = get_defs_(ast.0, acc, &to_id);
    defs.funs.reverse();
    defs.classes.reverse();
    defs.typedefs.reverse();
    defs.constants.reverse();
    defs.modules.reverse();
    defs.stmts.reverse();
    defs
}

pub fn get_def_names(ast: &Program) -> file_info::Ids {
    // The OCaml takes the names of `get_defs ast`. Here the names are read
    // from the program it borrows, in the order of `get_defs` (the
    // definitions from the last, consed, then reversed): `get_defs` takes
    // the program, and a copy of the whole AST at each call made every
    // naming lookup in a context with entries (`get_entry_symbols`) copy the
    // AST of each entry (the Glean indexer: about 4 times slower).
    fn go(defs: &[Def], ids: &mut file_info::Ids) {
        let id = |Id(p, name): &Id| pos_full((p.clone(), name.clone(), None));
        for def in defs.iter().rev() {
            match def {
                Def::Fun(f) => ids.funs.push(id(&f.name)),
                Def::Class(c) => ids.classes.push(id(&c.name)),
                Def::Typedef(t) => ids.typedefs.push(id(&t.name)),
                Def::Constant(cst) => ids.consts.push(id(&cst.name)),
                Def::Module(md) => ids.modules.push(id(&md.name)),
                Def::Namespace(ns) => go(&ns.1, ids),
                Def::Stmt(_)
                | Def::ClassAlias(_)
                | Def::NamespaceUse(_)
                | Def::SetNamespaceEnv(_)
                | Def::SetModule(_)
                | Def::FileAttributes(_) => {}
            }
        }
    }
    let mut ids = file_info::Ids {
        funs: vec![],
        classes: vec![],
        typedefs: vec![],
        consts: vec![],
        modules: vec![],
    };
    go(&ast.0, &mut ids);
    ids.funs.reverse();
    ids.classes.reverse();
    ids.typedefs.reverse();
    ids.consts.reverse();
    ids.modules.reverse();
    ids
}

#[derive(Clone, Debug)]
pub struct IgnoreAttributeEnv {
    pub ignored_attributes: Vec<String>,
}

// Some utility functions

/// `ast_deregister_attributes_mapper`: an `Aast.endo` mapper, here a
/// `VisitorMut` that changes the program in place.
struct AstDeregisterAttributesMapper;

fn ast_deregister_attributes_mapper() -> AstDeregisterAttributesMapper {
    AstDeregisterAttributesMapper
}

impl AstDeregisterAttributesMapper {
    fn ignored_attr(&self, env: &IgnoreAttributeEnv, l: &UserAttributes) -> bool {
        l.0.iter().any(|attr| {
            env.ignored_attributes
                .iter()
                .any(|ignored| *ignored == attr.name.1)
        })
    }
}

impl<'node> VisitorMut<'node> for AstDeregisterAttributesMapper {
    type Params = AstParams<IgnoreAttributeEnv, std::convert::Infallible>;

    fn object(&mut self) -> &mut dyn VisitorMut<'node, Params = Self::Params> {
        self
    }

    // Filter all functions and classes with the user attributes banned
    fn visit_program(
        &mut self,
        env: &mut IgnoreAttributeEnv,
        toplevels: &'node mut Program,
    ) -> Result<(), std::convert::Infallible> {
        toplevels.0.retain(|toplevel| match toplevel {
            Def::Fun(f) if self.ignored_attr(env, &f.fun.user_attributes) => false,
            Def::Class(c) if self.ignored_attr(env, &c.user_attributes) => false,
            _ => true,
        });
        toplevels.recurse(env, self.object())
    }

    fn visit_class_(
        &mut self,
        env: &mut IgnoreAttributeEnv,
        this: &'node mut Class_,
    ) -> Result<(), std::convert::Infallible> {
        // Filter out class elements which are methods with wrong attributes
        let methods: Vec<Method_> = std::mem::take(&mut this.methods)
            .into_iter()
            .filter(|m| !self.ignored_attr(env, &m.user_attributes))
            .collect();
        let cvars: Vec<ClassVar> = std::mem::take(&mut this.vars)
            .into_iter()
            .filter(|cv| !self.ignored_attr(env, &cv.user_attributes))
            .collect();
        this.methods = methods;
        this.vars = cvars;
        this.recurse(env, self.object())
    }
}

pub fn deregister_ignored_attributes(ast: Program) -> Program {
    let mut env = IgnoreAttributeEnv {
        // For now, only ignore the __PHPStdLib
        ignored_attributes: vec![sn::user_attributes::PHP_STD_LIB.to_string()],
    };
    let mut ast = ast;
    match ast_deregister_attributes_mapper().visit_program(&mut env, &mut ast) {
        Ok(()) => {}
        Err(e) => match e {},
    }
    ast
}

/// This module defines a visitor on the Nast data structure.
/// To use it you must implement [`Visitor`] and redefine the appropriate
/// methods; the function of the same name as a method is what the method
/// does by default (`parent#on_expr acc e` is `visitor_deprecated::on_expr(self,
/// acc, e)`).
///
/// It has been deprecated because it contains holes and needs to be updated
/// manually. Please use the autogenerated visitors instead.
pub mod visitor_deprecated {
    use bstr::BStr;
    use bstr::ByteSlice;
    use oxidized::nast::*;
    use oxidized::pos::Pos;

    /// `type id = lid`
    pub type Id = Lid;

    /// `class type ['a] visitor_type` (the signature of the visitor) and
    /// `class virtual ['a] visitor` (the generic visitor: the default methods;
    /// `'a` is the type of the accumulator).
    pub trait Visitor<A> {
        fn on_block(&mut self, acc: A, b: &[Stmt]) -> A {
            on_block(self, acc, b)
        }

        fn on_break(&mut self, acc: A) -> A {
            on_break(self, acc)
        }

        fn on_case(&mut self, acc: A, c: &Case) -> A {
            on_case(self, acc, c)
        }

        fn on_default_case(&mut self, acc: A, c: &DefaultCase) -> A {
            on_default_case(self, acc, c)
        }

        fn on_catch(&mut self, acc: A, c: &Catch) -> A {
            on_catch(self, acc, c)
        }

        fn on_continue(&mut self, acc: A) -> A {
            on_continue(self, acc)
        }

        fn on_do(&mut self, acc: A, b: &[Stmt], cond: &LoopCond) -> A {
            on_do(self, acc, b, cond)
        }

        fn on_expr(&mut self, acc: A, e: &Expr) -> A {
            on_expr(self, acc, e)
        }

        fn on_expr_(&mut self, acc: A, e: &Expr_) -> A {
            on_expr_(self, acc, e)
        }

        fn on_for(
            &mut self,
            acc: A,
            e1: &[Expr],
            e2: Option<&LoopCond>,
            e3: &LoopIter,
            b: &[Stmt],
        ) -> A {
            on_for(self, acc, e1, e2, e3, b)
        }

        fn on_foreach(&mut self, acc: A, e: &Expr, ae: &AsExpr, b: &[Stmt]) -> A {
            on_foreach(self, acc, e, ae, b)
        }

        fn on_if(&mut self, acc: A, e: &Expr, b1: &[Stmt], b2: &[Stmt]) -> A {
            on_if(self, acc, e, b1, b2)
        }

        fn on_noop(&mut self, acc: A) -> A {
            on_noop(self, acc)
        }

        fn on_fallthrough(&mut self, acc: A) -> A {
            on_fallthrough(self, acc)
        }

        fn on_return(&mut self, acc: A, eopt: Option<&Expr>) -> A {
            on_return(self, acc, eopt)
        }

        fn on_awaitall(&mut self, acc: A, el: &[(Id, Expr)], b: &[Stmt]) -> A {
            on_awaitall(self, acc, el, b)
        }

        fn on_concurrent(&mut self, acc: A, b: &[Stmt]) -> A {
            on_concurrent(self, acc, b)
        }

        fn on_stmt(&mut self, acc: A, s: &Stmt) -> A {
            on_stmt(self, acc, s)
        }

        fn on_stmt_(&mut self, acc: A, stmt: &Stmt_) -> A {
            on_stmt_(self, acc, stmt)
        }

        fn on_switch(&mut self, acc: A, e: &Expr, cl: &[Case], dfl: Option<&DefaultCase>) -> A {
            on_switch(self, acc, e, cl, dfl)
        }

        fn on_stmt_match(&mut self, acc: A, sm: &StmtMatch) -> A {
            on_stmt_match(self, acc, sm)
        }

        fn on_stmt_match_arm(&mut self, acc: A, arm: &StmtMatchArm) -> A {
            on_stmt_match_arm(self, acc, arm)
        }

        fn on_pattern(&mut self, acc: A, p: &Pattern) -> A {
            on_pattern(self, acc, p)
        }

        fn on_pat_var(&mut self, acc: A, pv: &PatVar) -> A {
            on_pat_var(self, acc, pv)
        }

        fn on_pat_refinement(&mut self, acc: A, pr: &PatRefinement) -> A {
            on_pat_refinement(self, acc, pr)
        }

        fn on_throw(&mut self, acc: A, e: &Expr) -> A {
            on_throw(self, acc, e)
        }

        fn on_try(&mut self, acc: A, b: &[Stmt], cl: &[Catch], fb: &[Stmt]) -> A {
            on_try(self, acc, b, cl, fb)
        }

        fn on_while(&mut self, acc: A, cond: &LoopCond, b: &[Stmt]) -> A {
            on_while(self, acc, cond, b)
        }

        fn on_using(&mut self, acc: A, us: &UsingStmt) -> A {
            on_using(self, acc, us)
        }

        fn on_as_expr(&mut self, acc: A, ae: &AsExpr) -> A {
            on_as_expr(self, acc, ae)
        }

        fn on_shape(&mut self, acc: A, sm: &[ShapeExprField]) -> A {
            on_shape(self, acc, sm)
        }

        fn on_val_collection(
            &mut self,
            acc: A,
            _s: &(Pos, VcKind),
            ta: Option<&Targ>,
            el: &[Expr],
        ) -> A {
            on_val_collection(self, acc, _s, ta, el)
        }

        fn on_key_val_collection(
            &mut self,
            acc: A,
            _s: &(Pos, KvcKind),
            tap: Option<&(Targ, Targ)>,
            fieldl: &[Field],
        ) -> A {
            on_key_val_collection(self, acc, _s, tap, fieldl)
        }

        fn on_collection(&mut self, acc: A, tal: Option<&CollectionTarg>, afl: &[Afield]) -> A {
            on_collection(self, acc, tal, afl)
        }

        fn on_this(&mut self, acc: A) -> A {
            on_this(self, acc)
        }

        fn on_id(&mut self, acc: A, _sid: &Sid) -> A {
            on_id(self, acc, _sid)
        }

        fn on_lvar(&mut self, acc: A, _id: &Id) -> A {
            on_lvar(self, acc, _id)
        }

        fn on_dollardollar(&mut self, acc: A, id: &Id) -> A {
            on_dollardollar(self, acc, id)
        }

        fn on_method_caller(&mut self, acc: A, _sid: &Sid, _pstr: &Pstring) -> A {
            on_method_caller(self, acc, _sid, _pstr)
        }

        fn on_obj_get(&mut self, acc: A, e1: &Expr, e2: &Expr) -> A {
            on_obj_get(self, acc, e1, e2)
        }

        fn on_array_get(&mut self, acc: A, e: &Expr, e_opt: Option<&Expr>) -> A {
            on_array_get(self, acc, e, e_opt)
        }

        fn on_class_get(&mut self, acc: A, cid: &ClassId, _e: &Pstring) -> A {
            on_class_get(self, acc, cid, _e)
        }

        fn on_class_const(&mut self, acc: A, cid: &ClassId, _id: &Pstring) -> A {
            on_class_const(self, acc, cid, _id)
        }

        fn on_call(
            &mut self,
            acc: A,
            e: &Expr,
            el: &[Argument],
            unpacked_element: Option<&Expr>,
        ) -> A {
            on_call(self, acc, e, el, unpacked_element)
        }

        fn on_argument(&mut self, acc: A, arg: &Argument) -> A {
            on_argument(self, acc, arg)
        }

        fn on_function_pointer(&mut self, acc: A, e: &FunctionPtrId, targs: &[Targ]) -> A {
            on_function_pointer(self, acc, e, targs)
        }

        fn on_true(&mut self, acc: A) -> A {
            on_true(self, acc)
        }

        fn on_false(&mut self, acc: A) -> A {
            on_false(self, acc)
        }

        fn on_int(&mut self, acc: A, _n: &str) -> A {
            on_int(self, acc, _n)
        }

        fn on_float(&mut self, acc: A, _n: &str) -> A {
            on_float(self, acc, _n)
        }

        fn on_null(&mut self, acc: A) -> A {
            on_null(self, acc)
        }

        fn on_string(&mut self, acc: A, _s: &BStr) -> A {
            on_string(self, acc, _s)
        }

        fn on_string2(&mut self, acc: A, el: &[Expr]) -> A {
            on_string2(self, acc, el)
        }

        fn on_yield_break(&mut self, acc: A) -> A {
            on_yield_break(self, acc)
        }

        fn on_yield(&mut self, acc: A, e: &Afield) -> A {
            on_yield(self, acc, e)
        }

        fn on_await(&mut self, acc: A, e: &Expr) -> A {
            on_await(self, acc, e)
        }

        fn on_delay(&mut self, acc: A, e: &Expr) -> A {
            on_delay(self, acc, e)
        }

        fn on_list(&mut self, acc: A, el: &[Expr]) -> A {
            on_list(self, acc, el)
        }

        fn on_pair(&mut self, acc: A, tap: Option<&(Targ, Targ)>, e1: &Expr, e2: &Expr) -> A {
            on_pair(self, acc, tap, e1, e2)
        }

        fn on_cast(&mut self, acc: A, _h: &Hint, e: &Expr) -> A {
            on_cast(self, acc, _h, e)
        }

        fn on_expression_tree(&mut self, acc: A, et: &ExpressionTree) -> A {
            on_expression_tree(self, acc, et)
        }

        fn on_unop(&mut self, acc: A, _uop: &Uop, e: &Expr) -> A {
            on_unop(self, acc, _uop, e)
        }

        fn on_binop(&mut self, acc: A, _bop: &Bop, e1: &Expr, e2: &Expr) -> A {
            on_binop(self, acc, _bop, e1, e2)
        }

        fn on_assign(&mut self, acc: A, e1: &Expr, _bop: Option<&Bop>, e2: &Expr) -> A {
            on_assign(self, acc, e1, _bop, e2)
        }

        fn on_pipe(
            &mut self,
            acc: A,
            _id: &Id,
            e1: &Expr,
            e2: &Expr,
            _null_flavor: &OperatorNullFlavor,
        ) -> A {
            on_pipe(self, acc, _id, e1, e2, _null_flavor)
        }

        fn on_eif(&mut self, acc: A, e1: &Expr, e2: Option<&Expr>, e3: &Expr) -> A {
            on_eif(self, acc, e1, e2, e3)
        }

        fn on_is(&mut self, acc: A, e: &Expr, _h: &Hint) -> A {
            on_is(self, acc, e, _h)
        }

        fn on_as(&mut self, acc: A, e: &Expr, _h: &Hint, _is_nullable: bool) -> A {
            on_as(self, acc, e, _h, _is_nullable)
        }

        fn on_upcast(&mut self, acc: A, e: &Expr, _h: &Hint) -> A {
            on_upcast(self, acc, e, _h)
        }

        fn on_omitted(&mut self, acc: A) -> A {
            on_omitted(self, acc)
        }

        fn on_class_id(&mut self, acc: A, cid: &ClassId) -> A {
            on_class_id(self, acc, cid)
        }

        fn on_class_id_(&mut self, acc: A, cid: &ClassId_) -> A {
            on_class_id_(self, acc, cid)
        }

        fn on_new(
            &mut self,
            acc: A,
            cid: &ClassId,
            el: &[Argument],
            unpacked_element: Option<&Expr>,
        ) -> A {
            on_new(self, acc, cid, el, unpacked_element)
        }

        fn on_record(&mut self, acc: A, _sid: &Sid, fl: &[Field]) -> A {
            on_record(self, acc, _sid, fl)
        }

        fn on_efun(&mut self, acc: A, ef: &Efun) -> A {
            on_efun(self, acc, ef)
        }

        fn on_lfun(&mut self, acc: A, f: &Fun_, _idl: &[CaptureLid]) -> A {
            on_lfun(self, acc, f, _idl)
        }

        fn on_xml(&mut self, acc: A, _sid: &Sid, attrl: &[XhpAttribute], el: &[Expr]) -> A {
            on_xml(self, acc, _sid, attrl, el)
        }

        fn on_param_kind(&mut self, acc: A, _pk: &ParamKind) -> A {
            on_param_kind(self, acc, _pk)
        }

        fn on_clone(&mut self, acc: A, e: &Expr) -> A {
            on_clone(self, acc, e)
        }

        fn on_field(&mut self, acc: A, f: &Field) -> A {
            on_field(self, acc, f)
        }

        fn on_afield(&mut self, acc: A, af: &Afield) -> A {
            on_afield(self, acc, af)
        }

        fn on_class_typeconst_def(&mut self, acc: A, t: &ClassTypeconstDef) -> A {
            on_class_typeconst_def(self, acc, t)
        }

        fn on_class_c_const(&mut self, acc: A, c_const: &ClassConst) -> A {
            on_class_c_const(self, acc, c_const)
        }

        fn on_class_var(&mut self, acc: A, c_var: &ClassVar) -> A {
            on_class_var(self, acc, c_var)
        }

        fn on_class_use(&mut self, acc: A, h: &Hint) -> A {
            on_class_use(self, acc, h)
        }

        fn on_class_req(&mut self, acc: A, req: &ClassReq) -> A {
            on_class_req(self, acc, req)
        }

        fn on_func_body(&mut self, acc: A, fb: &FuncBody) -> A {
            on_func_body(self, acc, fb)
        }

        fn on_method_(&mut self, acc: A, m: &Method_) -> A {
            on_method_(self, acc, m)
        }

        fn on_fun_def(&mut self, acc: A, f: &FunDef) -> A {
            on_fun_def(self, acc, f)
        }

        fn on_fun_(&mut self, acc: A, f: &Fun_) -> A {
            on_fun_(self, acc, f)
        }

        fn on_class_(&mut self, acc: A, c: &Class_) -> A {
            on_class_(self, acc, c)
        }

        fn on_gconst(&mut self, acc: A, g: &Gconst) -> A {
            on_gconst(self, acc, g)
        }

        fn on_typedef(&mut self, acc: A, t: &Typedef) -> A {
            on_typedef(self, acc, t)
        }

        fn on_hint(&mut self, acc: A, _h: &Hint) -> A {
            on_hint(self, acc, _h)
        }

        fn on_type_hint(&mut self, acc: A, _h: &TypeHint) -> A {
            on_type_hint(self, acc, _h)
        }

        fn on_targ(&mut self, acc: A, _t: &Targ) -> A {
            on_targ(self, acc, _t)
        }

        fn on_def(&mut self, acc: A, d: &Def) -> A {
            on_def(self, acc, d)
        }

        fn on_program(&mut self, acc: A, p: &[Def]) -> A {
            on_program(self, acc, p)
        }

        fn on_markup(&mut self, acc: A, _s: &Pstring) -> A {
            on_markup(self, acc, _s)
        }

        fn on_enum_class_label(&mut self, acc: A, opt_sid: Option<&Sid>, name: &str) -> A {
            on_enum_class_label(self, acc, opt_sid, name)
        }

        fn on_function_ptr_id(&mut self, acc: A, fpi: &FunctionPtrId) -> A {
            on_function_ptr_id(self, acc, fpi)
        }

        fn on_et_splice(&mut self, acc: A, e: &Expr) -> A {
            on_et_splice(self, acc, e)
        }

        fn on_readonly_expr(&mut self, acc: A, e: &Expr) -> A {
            on_readonly_expr(self, acc, e)
        }
    }

    /// `visitor_type`, the signature of [`Visitor`]
    pub use Visitor as VisitorType;

    pub fn on_break<A, V: Visitor<A> + ?Sized>(_this: &mut V, acc: A) -> A {
        acc
    }

    pub fn on_continue<A, V: Visitor<A> + ?Sized>(_this: &mut V, acc: A) -> A {
        acc
    }

    pub fn on_noop<A, V: Visitor<A> + ?Sized>(_this: &mut V, acc: A) -> A {
        acc
    }

    pub fn on_fallthrough<A, V: Visitor<A> + ?Sized>(_this: &mut V, acc: A) -> A {
        acc
    }

    pub fn on_markup<A, V: Visitor<A> + ?Sized>(_this: &mut V, acc: A, _s: &Pstring) -> A {
        acc
    }

    pub fn on_throw<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, e: &Expr) -> A {
        let acc = this.on_expr(acc, e);
        acc
    }

    pub fn on_return<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, eopt: Option<&Expr>) -> A {
        match eopt {
            None => acc,
            Some(e) => this.on_expr(acc, e),
        }
    }

    pub fn on_awaitall<A, V: Visitor<A> + ?Sized>(
        this: &mut V,
        acc: A,
        el: &[(Id, Expr)],
        b: &[Stmt],
    ) -> A {
        let mut acc = acc;
        for (x, y) in el {
            acc = this.on_lvar(acc, x);
            acc = this.on_expr(acc, y);
        }
        let acc = this.on_block(acc, b);
        acc
    }

    pub fn on_concurrent<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, b: &[Stmt]) -> A {
        this.on_block(acc, b)
    }

    pub fn on_if<A, V: Visitor<A> + ?Sized>(
        this: &mut V,
        acc: A,
        e: &Expr,
        b1: &[Stmt],
        b2: &[Stmt],
    ) -> A {
        let acc = this.on_expr(acc, e);
        let acc = this.on_block(acc, b1);
        let acc = this.on_block(acc, b2);
        acc
    }

    pub fn on_do<A, V: Visitor<A> + ?Sized>(
        this: &mut V,
        acc: A,
        b: &[Stmt],
        cond: &LoopCond,
    ) -> A {
        let LoopCond(_, _, e) = cond;
        let acc = this.on_block(acc, b);
        let acc = this.on_expr(acc, e);
        acc
    }

    pub fn on_while<A, V: Visitor<A> + ?Sized>(
        this: &mut V,
        acc: A,
        cond: &LoopCond,
        b: &[Stmt],
    ) -> A {
        let LoopCond(_, _, e) = cond;
        let acc = this.on_expr(acc, e);
        let acc = this.on_block(acc, b);
        acc
    }

    pub fn on_using<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, us: &UsingStmt) -> A {
        let mut acc = acc;
        for e in &us.exprs.1 {
            acc = this.on_expr(acc, e);
        }
        let acc = this.on_block(acc, &us.block.0);
        acc
    }

    pub fn on_for<A, V: Visitor<A> + ?Sized>(
        this: &mut V,
        acc: A,
        e1: &[Expr],
        e2: Option<&LoopCond>,
        e3: &LoopIter,
        b: &[Stmt],
    ) -> A {
        let LoopIter(_, _, e3) = e3;
        let mut on_expr_list = |acc: A, es: &[Expr]| {
            let mut acc = acc;
            for e in es {
                acc = this.on_expr(acc, e);
            }
            acc
        };

        let acc = on_expr_list(acc, e1);
        let acc = on_expr_list(acc, e3);
        let acc = match e2 {
            None => acc,
            Some(LoopCond(_, _, e)) => this.on_expr(acc, e),
        };
        let acc = this.on_block(acc, b);
        acc
    }

    pub fn on_switch<A, V: Visitor<A> + ?Sized>(
        this: &mut V,
        acc: A,
        e: &Expr,
        cl: &[Case],
        dfl: Option<&DefaultCase>,
    ) -> A {
        let mut acc = this.on_expr(acc, e);
        for c in cl {
            acc = this.on_case(acc, c);
        }
        let acc = match dfl {
            None => acc,
            Some(dfl) => this.on_default_case(acc, dfl),
        };
        acc
    }

    pub fn on_stmt_match<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, sm: &StmtMatch) -> A {
        let StmtMatch {
            expr: sm_expr,
            arms: sm_arms,
        } = sm;
        let mut acc = this.on_expr(acc, sm_expr);
        for arm in sm_arms {
            acc = this.on_stmt_match_arm(acc, arm);
        }
        acc
    }

    pub fn on_stmt_match_arm<A, V: Visitor<A> + ?Sized>(
        this: &mut V,
        acc: A,
        arm: &StmtMatchArm,
    ) -> A {
        let StmtMatchArm {
            pat: sma_pat,
            body: sma_body,
        } = arm;
        let acc = this.on_pattern(acc, sma_pat);
        let acc = this.on_block(acc, &sma_body.0);
        acc
    }

    pub fn on_pattern<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, p: &Pattern) -> A {
        match p {
            Pattern::PVar(pv) => this.on_pat_var(acc, pv),
            Pattern::PRefinement(pr) => this.on_pat_refinement(acc, pr),
        }
    }

    pub fn on_pat_var<A, V: Visitor<A> + ?Sized>(_this: &mut V, acc: A, pv: &PatVar) -> A {
        let PatVar { pos: _, id: _ } = pv;
        acc
    }

    pub fn on_pat_refinement<A, V: Visitor<A> + ?Sized>(
        this: &mut V,
        acc: A,
        pr: &PatRefinement,
    ) -> A {
        let PatRefinement {
            pos: _,
            id: _,
            hint: pr_hint,
        } = pr;
        let acc = this.on_hint(acc, pr_hint);
        acc
    }

    pub fn on_foreach<A, V: Visitor<A> + ?Sized>(
        this: &mut V,
        acc: A,
        e: &Expr,
        ae: &AsExpr,
        b: &[Stmt],
    ) -> A {
        let acc = this.on_expr(acc, e);
        let acc = this.on_as_expr(acc, ae);
        let acc = this.on_block(acc, b);
        acc
    }

    pub fn on_try<A, V: Visitor<A> + ?Sized>(
        this: &mut V,
        acc: A,
        b: &[Stmt],
        cl: &[Catch],
        fb: &[Stmt],
    ) -> A {
        let mut acc = this.on_block(acc, b);
        for c in cl {
            acc = this.on_catch(acc, c);
        }
        let acc = this.on_block(acc, fb);
        acc
    }

    pub fn on_block<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, b: &[Stmt]) -> A {
        let mut acc = acc;
        for s in b {
            acc = this.on_stmt(acc, s);
        }
        acc
    }

    pub fn on_case<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, c: &Case) -> A {
        let Case(e, b) = c;
        let acc = this.on_expr(acc, e);
        let acc = this.on_block(acc, &b.0);
        acc
    }

    pub fn on_default_case<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, c: &DefaultCase) -> A {
        let DefaultCase(_, dfl) = c;
        this.on_block(acc, &dfl.0)
    }

    pub fn on_as_expr<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, ae: &AsExpr) -> A {
        match ae {
            AsExpr::AsV(e) | AsExpr::AwaitAsV(_, e) => {
                let acc = this.on_expr(acc, e);
                acc
            }
            AsExpr::AsKv(e1, e2) | AsExpr::AwaitAsKv(_, e1, e2) => {
                let acc = this.on_expr(acc, e1);
                let acc = this.on_expr(acc, e2);
                acc
            }
        }
    }

    pub fn on_catch<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, c: &Catch) -> A {
        let Catch(_, _, b) = c;
        this.on_block(acc, &b.0)
    }

    pub fn on_stmt<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, s: &Stmt) -> A {
        let Stmt(_, stmt) = s;
        this.on_stmt_(acc, stmt)
    }

    pub fn on_stmt_<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, stmt: &Stmt_) -> A {
        match stmt {
            Stmt_::Expr(e) => this.on_expr(acc, e),
            Stmt_::Break => this.on_break(acc),
            Stmt_::Continue => this.on_continue(acc),
            Stmt_::Throw(e) => this.on_throw(acc, e),
            Stmt_::Return(eopt) => this.on_return(acc, (**eopt).as_ref()),
            Stmt_::YieldBreak => this.on_yield_break(acc),
            Stmt_::If(x) => {
                let (e, b1, b2) = &**x;
                this.on_if(acc, e, &b1.0, &b2.0)
            }
            Stmt_::Do(x) => {
                let (b, e) = &**x;
                this.on_do(acc, &b.0, e)
            }
            Stmt_::While(x) => {
                let (e, b) = &**x;
                this.on_while(acc, e, &b.0)
            }
            Stmt_::Using(us) => this.on_using(acc, us),
            Stmt_::For(x) => {
                let (e1, e2, e3, b) = &**x;
                this.on_for(acc, e1, e2.as_ref(), e3, &b.0)
            }
            Stmt_::Switch(x) => {
                let (e, cl, dfl) = &**x;
                this.on_switch(acc, e, cl, dfl.as_ref())
            }
            Stmt_::Match(sm) => this.on_stmt_match(acc, sm),
            Stmt_::Foreach(x) => {
                let (e, ae, b) = &**x;
                this.on_foreach(acc, e, ae, &b.0)
            }
            Stmt_::Try(x) => {
                let (b, cl, fb) = &**x;
                this.on_try(acc, &b.0, cl, &fb.0)
            }
            Stmt_::Noop => this.on_noop(acc),
            Stmt_::Fallthrough => this.on_fallthrough(acc),
            Stmt_::Awaitall(x) => {
                let (el, b) = &**x;
                this.on_awaitall(acc, el, &b.0)
            }
            Stmt_::Concurrent(b) => this.on_concurrent(acc, &b.0),
            Stmt_::Block(x) => match &**x {
                (Some(lids), b) => {
                    let mut acc = acc;
                    for lid in lids {
                        acc = this.on_lvar(acc, lid);
                    }
                    this.on_block(acc, &b.0)
                }
                (None, b) => this.on_block(acc, &b.0),
            },
            Stmt_::Markup(s) => this.on_markup(acc, s),
        }
    }

    pub fn on_expr<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, e: &Expr) -> A {
        let Expr(_, _, e) = e;
        this.on_expr_(acc, e)
    }

    pub fn on_expr_<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, e: &Expr_) -> A {
        match e {
            Expr_::Shape(sh) => this.on_shape(acc, sh),
            Expr_::True => this.on_true(acc),
            Expr_::False => this.on_false(acc),
            Expr_::Int(n) => this.on_int(acc, n),
            Expr_::Float(n) => this.on_float(acc, n),
            Expr_::Null => this.on_null(acc),
            Expr_::String(s) => this.on_string(acc, s.as_bstr()),
            Expr_::This => this.on_this(acc),
            Expr_::Id(sid) => this.on_id(acc, sid),
            Expr_::Lplaceholder(_pos) => acc,
            Expr_::Dollardollar(id) => this.on_dollardollar(acc, id),
            Expr_::Lvar(id) => this.on_lvar(acc, id),
            Expr_::MethodCaller(x) => {
                let (sid, pstr) = &**x;
                this.on_method_caller(acc, sid, pstr)
            }
            Expr_::Yield(e) => this.on_yield(acc, e),
            Expr_::Await(e) => this.on_await(acc, e),
            Expr_::Delay(e) => this.on_delay(acc, e),
            Expr_::Tuple(el) => this.on_list(acc, el),
            Expr_::List(el) => this.on_list(acc, el),
            Expr_::Clone(e) => this.on_clone(acc, e),
            Expr_::ObjGet(x) => {
                let (e1, e2, _, _) = &**x;
                this.on_obj_get(acc, e1, e2)
            }
            Expr_::ArrayGet(x) => {
                let (e1, e2) = &**x;
                this.on_array_get(acc, e1, e2.as_ref())
            }
            Expr_::ClassGet(x) => {
                let (cid, e, _) = &**x;
                this.on_class_get(acc, cid, e)
            }
            Expr_::ClassConst(x) => {
                let (cid, id) = &**x;
                this.on_class_const(acc, cid, id)
            }
            Expr_::Call(call) => {
                let CallExpr {
                    func: e,
                    args: el,
                    unpacked_arg,
                    ..
                } = &**call;
                this.on_call(acc, e, el, unpacked_arg.as_ref())
            }
            Expr_::FunctionPointer(x) => {
                let (fpid, targs, _) = &**x;
                this.on_function_pointer(acc, fpid, targs)
            }
            Expr_::String2(el) => this.on_string2(acc, el),
            Expr_::PrefixedString(x) => {
                let (_, e) = &**x;
                this.on_expr(acc, e)
            }
            Expr_::Pair(x) => {
                let (ta, e1, e2) = &**x;
                this.on_pair(acc, ta.as_ref(), e1, e2)
            }
            Expr_::Cast(x) => {
                let (hint, e) = &**x;
                this.on_cast(acc, hint, e)
            }
            Expr_::ExpressionTree(et) => this.on_expression_tree(acc, et),
            Expr_::Unop(x) => {
                let (uop, e) = &**x;
                this.on_unop(acc, uop, e)
            }
            Expr_::Binop(x) => {
                let Binop { bop, lhs, rhs } = &**x;
                this.on_binop(acc, bop, lhs, rhs)
            }
            Expr_::Assign(x) => {
                let (lhs, bop, rhs) = &**x;
                this.on_assign(acc, lhs, bop.as_ref(), rhs)
            }
            Expr_::Pipe(x) => {
                let (id, e1, e2, null_flavor) = &**x;
                this.on_pipe(acc, id, e1, e2, null_flavor)
            }
            Expr_::Eif(x) => {
                let (e1, e2, e3) = &**x;
                this.on_eif(acc, e1, e2.as_ref(), e3)
            }
            Expr_::Is(x) => {
                let (e, h) = &**x;
                this.on_is(acc, e, h)
            }
            Expr_::As(x) => {
                let As_ {
                    expr,
                    hint,
                    is_nullable,
                    enforce_deep: _,
                } = &**x;
                this.on_as(acc, expr, hint, *is_nullable)
            }
            Expr_::Upcast(x) => {
                let (e, h) = &**x;
                this.on_upcast(acc, e, h)
            }
            Expr_::New(x) => {
                let (cid, _, el, unpacked_element, _) = &**x;
                this.on_new(acc, cid, el, unpacked_element.as_ref())
            }
            Expr_::Efun(ef) => this.on_efun(acc, ef),
            Expr_::Xml(x) => {
                let (sid, attrl, el) = &**x;
                this.on_xml(acc, sid, attrl, el)
            }
            Expr_::ValCollection(x) => {
                let (s, ta, el) = &**x;
                this.on_val_collection(acc, s, ta.as_ref(), el)
            }
            Expr_::KeyValCollection(x) => {
                let (s, tap, fl) = &**x;
                this.on_key_val_collection(acc, s, tap.as_ref(), fl)
            }
            Expr_::Omitted => this.on_omitted(acc),
            Expr_::Lfun(x) => {
                let (f, idl) = &**x;
                this.on_lfun(acc, f, idl)
            }
            Expr_::Import(x) => {
                let (_, e) = &**x;
                this.on_expr(acc, e)
            }
            Expr_::Collection(x) => {
                let (_, tal, fl) = &**x;
                this.on_collection(acc, tal.as_ref(), fl)
            }
            Expr_::ETSplice(x) => {
                let EtSplice {
                    spliced_expr,
                    extract_client_type: _,
                    contains_await: _,
                    macro_variables: _,
                    temp_lid: _,
                } = &**x;
                this.on_et_splice(acc, spliced_expr)
            }
            Expr_::EnumClassLabel(x) => {
                let (opt_sid, name) = &**x;
                this.on_enum_class_label(acc, opt_sid.as_ref(), name)
            }
            Expr_::ReadonlyExpr(e) => this.on_readonly_expr(acc, e),
            Expr_::Hole(x) => {
                let (e, _, _, _) = &**x;
                this.on_expr(acc, e)
            }
            Expr_::Package(id) => this.on_id(acc, id),
            Expr_::Nameof(ci) => this.on_class_id(acc, ci),
            Expr_::Invalid(e) => match &**e {
                Some(e) => this.on_expr(acc, e),
                None => acc,
            },
            Expr_::DestructureShape(_) => acc,
            Expr_::DestructureTuple(_) => acc,
        }
    }

    pub fn on_collection<A, V: Visitor<A> + ?Sized>(
        this: &mut V,
        acc: A,
        tal: Option<&CollectionTarg>,
        afl: &[Afield],
    ) -> A {
        let mut acc = match tal {
            Some(CollectionTarg::CollectionTKV(tk, tv)) => {
                let acc = this.on_targ(acc, tk);
                let acc = this.on_targ(acc, tv);
                acc
            }
            Some(CollectionTarg::CollectionTV(tv)) => this.on_targ(acc, tv),
            None => acc,
        };
        for af in afl {
            acc = this.on_afield(acc, af);
        }
        acc
    }

    pub fn on_shape<A, V: Visitor<A> + ?Sized>(
        this: &mut V,
        acc: A,
        sm: &[ShapeExprField],
    ) -> A {
        let mut acc = acc;
        for field in sm {
            acc = match field {
                ShapeExprField::SFField(_, e) => this.on_expr(acc, e),
                ShapeExprField::SFSplat(e) => this.on_expr(acc, e),
            };
        }
        acc
    }

    pub fn on_val_collection<A, V: Visitor<A> + ?Sized>(
        this: &mut V,
        acc: A,
        _s: &(Pos, VcKind),
        ta: Option<&Targ>,
        el: &[Expr],
    ) -> A {
        let mut acc = match ta {
            Some(t) => this.on_targ(acc, t),
            None => acc,
        };
        for e in el {
            acc = this.on_expr(acc, e);
        }
        acc
    }

    pub fn on_key_val_collection<A, V: Visitor<A> + ?Sized>(
        this: &mut V,
        acc: A,
        _s: &(Pos, KvcKind),
        tap: Option<&(Targ, Targ)>,
        fieldl: &[Field],
    ) -> A {
        let mut acc = match tap {
            Some((t1, t2)) => {
                let acc = this.on_targ(acc, t1);
                let acc = this.on_targ(acc, t2);
                acc
            }
            None => acc,
        };
        for f in fieldl {
            acc = this.on_field(acc, f);
        }
        acc
    }

    pub fn on_this<A, V: Visitor<A> + ?Sized>(_this: &mut V, acc: A) -> A {
        acc
    }

    pub fn on_id<A, V: Visitor<A> + ?Sized>(_this: &mut V, acc: A, _sid: &Sid) -> A {
        acc
    }

    pub fn on_lvar<A, V: Visitor<A> + ?Sized>(_this: &mut V, acc: A, _id: &Id) -> A {
        acc
    }

    pub fn on_dollardollar<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, id: &Id) -> A {
        this.on_lvar(acc, id)
    }

    pub fn on_method_caller<A, V: Visitor<A> + ?Sized>(
        _this: &mut V,
        acc: A,
        _sid: &Sid,
        _pstr: &Pstring,
    ) -> A {
        acc
    }

    pub fn on_obj_get<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, e1: &Expr, e2: &Expr) -> A {
        let acc = this.on_expr(acc, e1);
        let acc = this.on_expr(acc, e2);
        acc
    }

    pub fn on_array_get<A, V: Visitor<A> + ?Sized>(
        this: &mut V,
        acc: A,
        e: &Expr,
        e_opt: Option<&Expr>,
    ) -> A {
        let acc = this.on_expr(acc, e);
        let acc = match e_opt {
            None => acc,
            Some(e) => this.on_expr(acc, e),
        };
        acc
    }

    pub fn on_class_get<A, V: Visitor<A> + ?Sized>(
        this: &mut V,
        acc: A,
        cid: &ClassId,
        _e: &Pstring,
    ) -> A {
        this.on_class_id(acc, cid)
    }

    pub fn on_class_const<A, V: Visitor<A> + ?Sized>(
        this: &mut V,
        acc: A,
        cid: &ClassId,
        _id: &Pstring,
    ) -> A {
        this.on_class_id(acc, cid)
    }

    pub fn on_call<A, V: Visitor<A> + ?Sized>(
        this: &mut V,
        acc: A,
        e: &Expr,
        el: &[Argument],
        unpacked_element: Option<&Expr>,
    ) -> A {
        let mut acc = this.on_expr(acc, e);
        for arg in el {
            acc = this.on_argument(acc, arg);
        }
        let acc = match unpacked_element {
            Some(e) => this.on_expr(acc, e),
            None => acc,
        };
        acc
    }

    pub fn on_argument<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, arg: &Argument) -> A {
        match arg {
            Argument::Anormal(e) => this.on_expr(acc, e),
            Argument::Ainout(_pos, e) => this.on_expr(acc, e),
            Argument::Anamed(_name, e) => this.on_expr(acc, e),
        }
    }

    pub fn on_function_pointer<A, V: Visitor<A> + ?Sized>(
        this: &mut V,
        acc: A,
        e: &FunctionPtrId,
        targs: &[Targ],
    ) -> A {
        let mut acc = this.on_function_ptr_id(acc, e);
        for t in targs {
            acc = this.on_targ(acc, t);
        }
        acc
    }

    pub fn on_true<A, V: Visitor<A> + ?Sized>(_this: &mut V, acc: A) -> A {
        acc
    }

    pub fn on_false<A, V: Visitor<A> + ?Sized>(_this: &mut V, acc: A) -> A {
        acc
    }

    pub fn on_int<A, V: Visitor<A> + ?Sized>(_this: &mut V, acc: A, _n: &str) -> A {
        acc
    }

    pub fn on_float<A, V: Visitor<A> + ?Sized>(_this: &mut V, acc: A, _n: &str) -> A {
        acc
    }

    pub fn on_null<A, V: Visitor<A> + ?Sized>(_this: &mut V, acc: A) -> A {
        acc
    }

    pub fn on_string<A, V: Visitor<A> + ?Sized>(_this: &mut V, acc: A, _s: &BStr) -> A {
        acc
    }

    pub fn on_string2<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, el: &[Expr]) -> A {
        let mut acc = acc;
        for e in el {
            acc = this.on_expr(acc, e);
        }
        acc
    }

    pub fn on_yield_break<A, V: Visitor<A> + ?Sized>(_this: &mut V, acc: A) -> A {
        acc
    }

    pub fn on_yield<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, e: &Afield) -> A {
        this.on_afield(acc, e)
    }

    pub fn on_await<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, e: &Expr) -> A {
        this.on_expr(acc, e)
    }

    pub fn on_delay<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, e: &Expr) -> A {
        this.on_expr(acc, e)
    }

    pub fn on_list<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, el: &[Expr]) -> A {
        let mut acc = acc;
        for e in el {
            acc = this.on_expr(acc, e);
        }
        acc
    }

    pub fn on_pair<A, V: Visitor<A> + ?Sized>(
        this: &mut V,
        acc: A,
        tap: Option<&(Targ, Targ)>,
        e1: &Expr,
        e2: &Expr,
    ) -> A {
        let acc = match tap {
            Some((t1, t2)) => {
                let acc = this.on_targ(acc, t1);
                let acc = this.on_targ(acc, t2);
                acc
            }
            None => acc,
        };
        let acc = this.on_expr(acc, e1);
        let acc = this.on_expr(acc, e2);
        acc
    }

    pub fn on_cast<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, _h: &Hint, e: &Expr) -> A {
        this.on_expr(acc, e)
    }

    pub fn on_expression_tree<A, V: Visitor<A> + ?Sized>(
        this: &mut V,
        acc: A,
        et: &ExpressionTree,
    ) -> A {
        let acc = this.on_id(acc, &et.class);
        let acc = this.on_expr(acc, &et.runtime_expr);
        acc
    }

    pub fn on_unop<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, _uop: &Uop, e: &Expr) -> A {
        this.on_expr(acc, e)
    }

    pub fn on_binop<A, V: Visitor<A> + ?Sized>(
        this: &mut V,
        acc: A,
        _bop: &Bop,
        e1: &Expr,
        e2: &Expr,
    ) -> A {
        let acc = this.on_expr(acc, e1);
        let acc = this.on_expr(acc, e2);
        acc
    }

    pub fn on_assign<A, V: Visitor<A> + ?Sized>(
        this: &mut V,
        acc: A,
        e1: &Expr,
        _bop: Option<&Bop>,
        e2: &Expr,
    ) -> A {
        let acc = this.on_expr(acc, e1);
        let acc = this.on_expr(acc, e2);
        acc
    }

    pub fn on_pipe<A, V: Visitor<A> + ?Sized>(
        this: &mut V,
        acc: A,
        _id: &Id,
        e1: &Expr,
        e2: &Expr,
        _null_flavor: &OperatorNullFlavor,
    ) -> A {
        let acc = this.on_expr(acc, e1);
        let acc = this.on_expr(acc, e2);
        acc
    }

    pub fn on_eif<A, V: Visitor<A> + ?Sized>(
        this: &mut V,
        acc: A,
        e1: &Expr,
        e2: Option<&Expr>,
        e3: &Expr,
    ) -> A {
        let acc = this.on_expr(acc, e1);
        let acc = match e2 {
            None => acc,
            Some(e) => this.on_expr(acc, e),
        };
        let acc = this.on_expr(acc, e3);
        acc
    }

    pub fn on_is<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, e: &Expr, _h: &Hint) -> A {
        this.on_expr(acc, e)
    }

    pub fn on_as<A, V: Visitor<A> + ?Sized>(
        this: &mut V,
        acc: A,
        e: &Expr,
        _h: &Hint,
        _is_nullable: bool,
    ) -> A {
        this.on_expr(acc, e)
    }

    pub fn on_upcast<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, e: &Expr, _h: &Hint) -> A {
        this.on_expr(acc, e)
    }

    pub fn on_omitted<A, V: Visitor<A> + ?Sized>(_this: &mut V, acc: A) -> A {
        acc
    }

    pub fn on_class_id<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, cid: &ClassId) -> A {
        let ClassId(_, _, cid) = cid;
        this.on_class_id_(acc, cid)
    }

    pub fn on_class_id_<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, cid: &ClassId_) -> A {
        match cid {
            ClassId_::CIexpr(e) => this.on_expr(acc, e),
            _ => acc,
        }
    }

    pub fn on_new<A, V: Visitor<A> + ?Sized>(
        this: &mut V,
        acc: A,
        cid: &ClassId,
        el: &[Argument],
        unpacked_element: Option<&Expr>,
    ) -> A {
        let mut acc = this.on_class_id(acc, cid);
        for arg in el {
            acc = this.on_argument(acc, arg);
        }
        let acc = match unpacked_element {
            Some(e) => this.on_expr(acc, e),
            None => acc,
        };
        acc
    }

    pub fn on_efun<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, ef: &Efun) -> A {
        this.on_block(acc, &ef.fun.body.fb_ast.0)
    }

    pub fn on_lfun<A, V: Visitor<A> + ?Sized>(
        this: &mut V,
        acc: A,
        f: &Fun_,
        _idl: &[CaptureLid],
    ) -> A {
        this.on_block(acc, &f.body.fb_ast.0)
    }

    pub fn on_record<A, V: Visitor<A> + ?Sized>(
        this: &mut V,
        acc: A,
        _sid: &Sid,
        fl: &[Field],
    ) -> A {
        let mut acc = acc;
        for f in fl {
            acc = this.on_field(acc, f);
        }
        acc
    }

    pub fn on_xml<A, V: Visitor<A> + ?Sized>(
        this: &mut V,
        acc: A,
        _sid: &Sid,
        attrl: &[XhpAttribute],
        el: &[Expr],
    ) -> A {
        let mut acc = acc;
        for attr in attrl {
            acc = match attr {
                XhpAttribute::XhpSimple(XhpSimple { expr: e, .. }) | XhpAttribute::XhpSpread(e) => {
                    this.on_expr(acc, e)
                }
            };
        }
        for e in el {
            acc = this.on_expr(acc, e);
        }
        acc
    }

    pub fn on_param_kind<A, V: Visitor<A> + ?Sized>(_this: &mut V, acc: A, _pk: &ParamKind) -> A {
        acc
    }

    pub fn on_clone<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, e: &Expr) -> A {
        this.on_expr(acc, e)
    }

    pub fn on_field<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, f: &Field) -> A {
        let Field(e1, e2) = f;
        let acc = this.on_expr(acc, e1);
        let acc = this.on_expr(acc, e2);
        acc
    }

    pub fn on_afield<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, af: &Afield) -> A {
        match af {
            Afield::AFvalue(e) => this.on_expr(acc, e),
            Afield::AFkvalue(e1, e2) => {
                let acc = this.on_expr(acc, e1);
                let acc = this.on_expr(acc, e2);
                acc
            }
        }
    }

    pub fn on_hint<A, V: Visitor<A> + ?Sized>(_this: &mut V, acc: A, _h: &Hint) -> A {
        acc
    }

    pub fn on_type_hint<A, V: Visitor<A> + ?Sized>(_this: &mut V, acc: A, _h: &TypeHint) -> A {
        acc
    }

    pub fn on_targ<A, V: Visitor<A> + ?Sized>(_this: &mut V, acc: A, _t: &Targ) -> A {
        acc
    }

    pub fn on_fun_<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, f: &Fun_) -> A {
        let acc = this.on_func_body(acc, &f.body);
        // `hint_of_type_hint`
        let acc = match &f.ret.1 {
            Some(h) => this.on_hint(acc, h),
            None => acc,
        };
        acc
    }

    pub fn on_func_body<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, fb: &FuncBody) -> A {
        this.on_block(acc, &fb.fb_ast.0)
    }

    pub fn on_method_<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, m: &Method_) -> A {
        let acc = this.on_id(acc, &m.name);
        let acc = this.on_func_body(acc, &m.body);
        acc
    }

    pub fn on_class_<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, c: &Class_) -> A {
        let mut acc = this.on_id(acc, &c.name);
        for h in &c.extends {
            acc = this.on_hint(acc, h);
        }
        for h in &c.uses {
            acc = this.on_hint(acc, h);
        }
        for h in &c.implements {
            acc = this.on_hint(acc, h);
        }
        for t in &c.typeconsts {
            acc = this.on_class_typeconst_def(acc, t);
        }
        for c_const in &c.consts {
            acc = this.on_class_c_const(acc, c_const);
        }
        for c_var in &c.vars {
            acc = this.on_class_var(acc, c_var);
        }
        for h in &c.uses {
            acc = this.on_class_use(acc, h);
        }
        for req in &c.reqs {
            acc = this.on_class_req(acc, req);
        }
        for m in &c.methods {
            acc = this.on_method_(acc, m);
        }
        acc
    }

    pub fn on_fun_def<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, f: &FunDef) -> A {
        let acc = this.on_id(acc, &f.name);
        this.on_fun_(acc, &f.fun)
    }

    pub fn on_class_typeconst_def<A, V: Visitor<A> + ?Sized>(
        this: &mut V,
        acc: A,
        t: &ClassTypeconstDef,
    ) -> A {
        let acc = this.on_id(acc, &t.name);
        match &t.kind {
            ClassTypeconst::TCAbstract(ClassAbstractTypeconst {
                as_constraint: c_atc_as_constraint,
                super_constraint: c_atc_super_constraint,
                default: c_atc_default,
            }) => {
                let acc = match c_atc_as_constraint {
                    Some(cstr) => this.on_hint(acc, cstr),
                    None => acc,
                };
                let acc = match c_atc_super_constraint {
                    Some(cstr) => this.on_hint(acc, cstr),
                    None => acc,
                };
                match c_atc_default {
                    Some(d) => this.on_hint(acc, d),
                    None => acc,
                }
            }
            ClassTypeconst::TCConcrete(ClassConcreteTypeconst { c_tc_type }) => {
                this.on_hint(acc, c_tc_type)
            }
        }
    }

    pub fn on_class_c_const<A, V: Visitor<A> + ?Sized>(
        this: &mut V,
        acc: A,
        c_const: &ClassConst,
    ) -> A {
        let acc = match &c_const.type_ {
            Some(h) => this.on_hint(acc, h),
            None => acc,
        };
        let acc = this.on_id(acc, &c_const.id);
        let acc = match &c_const.kind {
            ClassConstKind::CCConcrete(e) => this.on_expr(acc, e),
            ClassConstKind::CCAbstract(Some(default)) => this.on_expr(acc, default),
            ClassConstKind::CCAbstract(None) => acc,
        };
        acc
    }

    pub fn on_readonly_expr<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, e: &Expr) -> A {
        let acc = this.on_expr(acc, e);
        acc
    }

    pub fn on_class_var<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, c_var: &ClassVar) -> A {
        let acc = this.on_id(acc, &c_var.id);
        // `hint_of_type_hint`
        let acc = match &c_var.type_.1 {
            Some(h) => this.on_hint(acc, h),
            None => acc,
        };
        let acc = match &c_var.expr {
            Some(e) => this.on_expr(acc, e),
            None => acc,
        };
        acc
    }

    pub fn on_class_use<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, h: &Hint) -> A {
        this.on_hint(acc, h)
    }

    pub fn on_class_req<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, req: &ClassReq) -> A {
        let ClassReq(h, _) = req;
        this.on_hint(acc, h)
    }

    pub fn on_gconst<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, g: &Gconst) -> A {
        let acc = this.on_id(acc, &g.name);
        let acc = this.on_expr(acc, &g.value);
        let acc = match &g.type_ {
            Some(h) => this.on_hint(acc, h),
            None => acc,
        };
        acc
    }

    pub fn on_enum_class_label<A, V: Visitor<A> + ?Sized>(
        this: &mut V,
        acc: A,
        opt_sid: Option<&Sid>,
        name: &str,
    ) -> A {
        let acc = match opt_sid {
            Some(sid) => this.on_id(acc, sid),
            None => acc,
        };
        this.on_string(acc, name.as_bytes().as_bstr())
    }

    pub fn on_function_ptr_id<A, V: Visitor<A> + ?Sized>(
        this: &mut V,
        acc: A,
        fpi: &FunctionPtrId,
    ) -> A {
        match fpi {
            FunctionPtrId::FPId(sid) => this.on_id(acc, sid),
            FunctionPtrId::FPClassConst(cid, _) => this.on_class_id(acc, cid),
        }
    }

    pub fn on_et_splice<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, e: &Expr) -> A {
        this.on_expr(acc, e)
    }

    pub fn on_typedef<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, t: &Typedef) -> A {
        let acc = this.on_id(acc, &t.name);
        let acc = match &t.assignment {
            TypedefAssignment::SimpleTypeDef(TypedefVisibilityAndHint {
                vis: _,
                hint: tvh_hint,
            }) => this.on_hint(acc, tvh_hint),
            TypedefAssignment::CaseType(variant, variants) => {
                let mut acc = acc;
                for variant in std::iter::once(variant).chain(variants.iter()) {
                    acc = this.on_hint(acc, &variant.hint);
                }
                acc
            }
        };
        let acc = match &t.as_constraint {
            Some(c) => this.on_hint(acc, c),
            None => acc,
        };
        let acc = match &t.super_constraint {
            Some(c) => this.on_hint(acc, c),
            None => acc,
        };
        acc
    }

    pub fn on_def<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, d: &Def) -> A {
        match d {
            Def::Fun(f) => this.on_fun_def(acc, f),
            Def::Class(c) => this.on_class_(acc, c),
            Def::Stmt(s) => this.on_stmt(acc, s),
            Def::Typedef(t) => this.on_typedef(acc, t),
            Def::Constant(g) => this.on_gconst(acc, g),
            Def::Namespace(x) => {
                let (_, p) = &**x;
                this.on_program(acc, p)
            }
            Def::ClassAlias(_)
            | Def::NamespaceUse(_)
            | Def::SetNamespaceEnv(_)
            | Def::FileAttributes(_)
            | Def::SetModule(_)
            | Def::Module(_) => acc,
        }
    }

    pub fn on_program<A, V: Visitor<A> + ?Sized>(this: &mut V, acc: A, p: &[Def]) -> A {
        let mut acc = acc;
        for d in p {
            acc = this.on_def(acc, d);
        }
        acc
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use oxidized::namespace_env;

    use super::visitor_deprecated::Visitor;
    use super::*;

    fn id(name: &str) -> Id {
        Id(Pos::NONE, name.to_string())
    }

    fn expr(e: Expr_) -> Expr {
        aast::Expr((), Pos::NONE, e)
    }

    fn lvar(name: &str) -> Expr {
        expr(Expr_::Lvar(Box::new(Lid(Pos::NONE, (0, name.to_string())))))
    }

    fn stmt(e: Expr) -> Stmt {
        aast::Stmt(Pos::NONE, Stmt_::Expr(Box::new(e)))
    }

    fn user_attributes(names: &[&str]) -> UserAttributes {
        aast::UserAttributes(
            names
                .iter()
                .map(|n| aast::UserAttribute {
                    name: id(n),
                    params: vec![],
                })
                .collect(),
        )
    }

    fn fun_(body: Vec<Stmt>, attrs: &[&str]) -> Fun_ {
        aast::Fun_ {
            span: Pos::NONE,
            readonly_this: None,
            annotation: (),
            readonly_ret: None,
            tparams: vec![],
            ret: aast::TypeHint((), None),
            params: vec![],
            ctxs: None,
            unsafe_ctxs: None,
            body: aast::FuncBody {
                fb_ast: aast::Block(body),
            },
            fun_kind: FunKind::FSync,
            user_attributes: user_attributes(attrs),
            external: false,
            hidden: false,
            doc_comment: None,
        }
    }

    fn fun_def(name: &str, body: Vec<Stmt>, attrs: &[&str]) -> Def {
        Def::Fun(Box::new(aast::FunDef {
            namespace: Arc::new(namespace_env::Env::empty(
                vec![],
                namespace_env::Mode::ForTypecheck,
                false,
            )),
            file_attributes: vec![],
            mode: file_info::Mode::Mstrict,
            name: id(name),
            fun: fun_(body, attrs),
            internal: false,
            module: None,
            tparams: vec![],
            where_constraints: vec![],
            package: None,
        }))
    }

    #[test]
    fn class_ids() {
        assert_eq!(class_id_to_str(&ClassId_::CIparent), "parent");
        assert_eq!(class_id_to_str(&ClassId_::CIself), "self");
        assert_eq!(class_id_to_str(&ClassId_::CIstatic), "static");
        assert_eq!(
            class_id_to_str(&ClassId_::CIexpr(expr(Expr_::This))),
            "$this"
        );
        assert_eq!(class_id_to_str(&ClassId_::CIexpr(lvar("$x"))), "$$x");
        assert_eq!(class_id_to_str(&ClassId_::CI(id("\\C"))), "\\C");
        assert!(equal_class_id_(&ClassId_::CIparent, &ClassId_::CIparent));
        assert!(!equal_class_id_(&ClassId_::CIparent, &ClassId_::CIself));
    }

    #[test]
    fn collection_kinds() {
        assert!(is_vc_kind("\\HH\\Vector"));
        assert!(is_vc_kind("\\HH\\keyset"));
        assert!(!is_vc_kind("\\HH\\Map"));
        assert!(is_kvc_kind("\\HH\\dict"));
        assert_eq!(get_vc_kind("\\HH\\vec"), VcKind::Vec);
        assert_eq!(get_kvc_kind("\\HH\\ImmMap"), KvcKind::ImmMap);
        assert_eq!(vc_kind_to_name(&VcKind::ImmSet), "\\HH\\ImmSet");
        assert_eq!(kvc_kind_to_name(&KvcKind::Dict), "\\HH\\dict");
        assert_eq!(show_tprim(&Tprim::Tarraykey), "arraykey");
    }

    #[test]
    fn defs() {
        let ns = Def::Namespace(Box::new((
            id("NS"),
            vec![
                fun_def("\\NS\\g", vec![], &[]),
                Def::Stmt(Box::new(stmt(lvar("$b")))),
            ],
        )));
        let program = Program(vec![
            Def::Stmt(Box::new(stmt(lvar("$a")))),
            fun_def("\\f", vec![], &[]),
            ns,
            Def::Stmt(Box::new(stmt(lvar("$c")))),
        ]);
        let names = get_def_names(&program);
        let fun_names: Vec<&str> = names.funs.iter().map(|id| id.name.as_str()).collect();
        assert_eq!(fun_names, vec!["\\f", "\\NS\\g"]);
        let defs = get_defs(program);
        // The statements are numbered from the last one.
        let stmt_names: Vec<&str> = defs.stmts.iter().map(|(id, _)| id.name.as_str()).collect();
        assert_eq!(stmt_names, vec!["#stmt_2", "#stmt_1", "#stmt_0"]);
    }

    #[test]
    fn deregister() {
        let program = Program(vec![
            fun_def("\\f", vec![], &["__PHPStdLib"]),
            fun_def("\\g", vec![], &["__Memoize"]),
            Def::Namespace(Box::new((
                id("NS"),
                vec![fun_def("\\NS\\h", vec![], &["__PHPStdLib"])],
            ))),
        ]);
        let program = deregister_ignored_attributes(program);
        let names = get_def_names(&program);
        let fun_names: Vec<&str> = names.funs.iter().map(|id| id.name.as_str()).collect();
        // Only the top-level definitions are filtered (`on_program` is not
        // called on the definitions of a namespace).
        assert_eq!(fun_names, vec!["\\g", "\\NS\\h"]);
    }

    /// The locals that a block uses, except in lambdas.
    struct Locals;

    impl Visitor<Vec<String>> for Locals {
        fn on_lvar(&mut self, mut acc: Vec<String>, lid: &visitor_deprecated::Id) -> Vec<String> {
            acc.push(lid.1.1.clone());
            acc
        }

        fn on_expr(&mut self, acc: Vec<String>, e: &Expr) -> Vec<String> {
            match &e.2 {
                Expr_::Lfun(_) => acc,
                _ => visitor_deprecated::on_expr(self, acc, e),
            }
        }
    }

    #[test]
    fn visitor() {
        let lambda = expr(Expr_::Lfun(Box::new((
            fun_(vec![stmt(lvar("$in_lambda"))], &[]),
            vec![],
        ))));
        let pair = expr(Expr_::Binop(Box::new(aast::Binop {
            bop: Bop::Plus,
            lhs: lvar("$x"),
            rhs: lvar("$y"),
        })));
        let block = vec![stmt(pair), stmt(lambda), stmt(lvar("$z"))];
        let locals = Locals.on_block(vec![], &block);
        assert_eq!(locals, vec!["$x", "$y", "$z"]);
    }
}
