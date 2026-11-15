// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/tast.ml`. See `hh/PORTING.md`.
//!
//! The typed AST is `oxidized::aast` with the localized type ([`Ty`]) for the
//! annotation of expressions (`'ex`) and [`SavedEnv`] for the environment
//! annotation (`'en`).
//!
//! `include Aast_defs`: everything of `oxidized::aast_defs` is re-exported
//! (`tast::CheckStatus`, `tast::Hint`, `tast::Expr_::Call`, ...); the names
//! that `tast.ml` redefines for the typed AST (`expr`, `stmt`, `fun_`, ...)
//! are the aliases below, as in OCaml.
//!
//! The types defined here are named the way `oxidized` names types (see
//! `typing_defs_core.rs`): `dl_name` is `DynamicLocalInfo::name`.
//!
//! Not ported: `to_nast`, `to_nast_expr` and `to_nast_class_id_` are `todo!`.
//! They are `Aast.map` with `on_'ex` and `on_'en` that change the type of the
//! annotations, and `oxidized::aast_visitor` can only visit an AST in place.

use std::sync::Arc;

use oxidized::aast as generic;
pub use oxidized::aast_defs::*;
use oxidized::aast_visitor;
use oxidized::aast_visitor::NodeMut;
use oxidized::aast_visitor::VisitorMut;
use oxidized::nast;
use oxidized::typechecker_options::TypecheckerOptions;

use crate::tast_with_dynamic;

/// `S_map.t`
type SMap<V> = im::OrdMap<String, V>;

/// This is the current notion of type in the typed AST.
/// In future we might want to reconsider this and define a new representation
/// that omits type inference artefacts such as type variables and lambda
/// identifiers.
pub type Ty = crate::typing_defs::Ty;

pub type DeclTy = crate::typing_defs::DeclTy;

pub type ValKind = crate::typing_defs::ValKind;

/// Contains information about a specific function that we
/// a) want to make available to TAST checks
/// b) isn't otherwise (space-efficiently) present in the saved typing env
#[derive(Clone, Debug, PartialEq)]
pub struct DynamicLocalInfo {
    pub name: String,
    pub pos: Pos,
    /// A `Tvid.t`.
    pub shadow_tvid: isize,
}

#[derive(Clone, Debug, PartialEq)]
pub struct FunTastInfo {
    pub has_implicit_return: bool,
    /// True if there are leaves of the function's imaginary CFG without a return statement
    pub has_readonly: bool,
    /// Locals with type dynamic and their shadow tyvars
    pub dynamic_locals: Vec<DynamicLocalInfo>,
}

pub fn is_under_dynamic_assumptions(c: CheckStatus) -> bool {
    match c {
        CheckStatus::COnce | CheckStatus::CUnderNormalAssumptions => false,
        CheckStatus::CUnderDynamicAssumptions => true,
    }
}

#[derive(Clone, Debug)]
pub struct SavedEnv {
    pub tcopt: Arc<TypecheckerOptions>,
    pub inference_env: crate::typing_inference_env::T,
    pub tpenv: crate::type_parameter_env::T,
    pub fun_tast_info: Option<FunTastInfo>,
    /// Indicates how many types the callable was checked and under what
    /// assumptions.
    pub checked: CheckStatus,
}

pub type Program = generic::Program<Ty, SavedEnv>;

pub type Def = generic::Def<Ty, SavedEnv>;

pub type DefWithDynamic = tast_with_dynamic::T<Def>;

pub type Expr = generic::Expr<Ty, SavedEnv>;

pub type Expr_ = generic::Expr_<Ty, SavedEnv>;

pub type Argument = generic::Argument<Ty, SavedEnv>;

pub type Stmt = generic::Stmt<Ty, SavedEnv>;

pub type Stmt_ = generic::Stmt_<Ty, SavedEnv>;

pub type Case = generic::Case<Ty, SavedEnv>;

pub type Block = generic::Block<Ty, SavedEnv>;

pub type Class_ = generic::Class_<Ty, SavedEnv>;

pub type ClassId = generic::ClassId<Ty, SavedEnv>;

pub type TypeHint = generic::TypeHint<Ty>;

pub type Targ = generic::Targ<Ty>;

pub type ClassTypeconstDef = generic::ClassTypeconstDef<Ty, SavedEnv>;

pub type UserAttribute = generic::UserAttribute<Ty, SavedEnv>;

pub type CaptureLid = generic::CaptureLid<Ty>;

pub type Fun_ = generic::Fun_<Ty, SavedEnv>;

pub type Efun = generic::Efun<Ty, SavedEnv>;

pub type FileAttribute = generic::FileAttribute<Ty, SavedEnv>;

pub type FunDef = generic::FunDef<Ty, SavedEnv>;

pub type FunParam = generic::FunParam<Ty, SavedEnv>;

pub type FuncBody = generic::FuncBody<Ty, SavedEnv>;

pub type Method_ = generic::Method_<Ty, SavedEnv>;

pub type ClassVar = generic::ClassVar<Ty, SavedEnv>;

pub type ClassConst = generic::ClassConst<Ty, SavedEnv>;

pub type Tparam = generic::Tparam<Ty, SavedEnv>;

pub type Typedef = generic::Typedef<Ty, SavedEnv>;

pub type Gconst = generic::Gconst<Ty, SavedEnv>;

pub type ModuleDef = generic::ModuleDef<Ty, SavedEnv>;

pub type CallExpr = generic::CallExpr<Ty, SavedEnv>;

pub type DestructureShape = generic::DestructureShape<Ty, SavedEnv>;

pub type DestructureShapeField = generic::DestructureShapeField<Ty, SavedEnv>;

pub type DestructureTuple = generic::DestructureTuple<Ty, SavedEnv>;

pub type DestructureTupleEntry = generic::DestructureTupleEntry<Ty, SavedEnv>;

pub type DestructureTarget = generic::DestructureTarget<Ty, SavedEnv>;

#[derive(Clone)]
pub struct ByNames {
    pub fun_tasts: SMap<tast_with_dynamic::T<Def>>,
    pub class_tasts: SMap<tast_with_dynamic::T<Def>>,
    pub typedef_tasts: SMap<Def>,
    pub gconst_tasts: SMap<Def>,
    pub module_tasts: SMap<Def>,
}

pub fn empty_by_names() -> ByNames {
    ByNames {
        fun_tasts: SMap::new(),
        class_tasts: SMap::new(),
        typedef_tasts: SMap::new(),
        gconst_tasts: SMap::new(),
        module_tasts: SMap::new(),
    }
}

pub fn map_by_names(x: ByNames, f: impl Fn(Def) -> Def) -> ByNames {
    let ByNames {
        fun_tasts,
        class_tasts,
        typedef_tasts,
        gconst_tasts,
        module_tasts,
    } = x;
    ByNames {
        fun_tasts: fun_tasts
            .into_iter()
            .map(|(k, v)| (k, tast_with_dynamic::map(&f, v)))
            .collect(),
        class_tasts: class_tasts
            .into_iter()
            .map(|(k, v)| (k, tast_with_dynamic::map(&f, v)))
            .collect(),
        typedef_tasts: typedef_tasts.into_iter().map(|(k, v)| (k, f(v))).collect(),
        gconst_tasts: gconst_tasts.into_iter().map(|(k, v)| (k, f(v))).collect(),
        module_tasts: module_tasts.into_iter().map(|(k, v)| (k, f(v))).collect(),
    }
}

pub fn program_by_names(program: tast_with_dynamic::T<Program>) -> ByNames {
    fn add(
        under_normal_assumptions: bool,
        name: &str,
        def: Def,
        map: &mut SMap<tast_with_dynamic::T<Def>>,
    ) {
        let entry = match map.get(name) {
            None => tast_with_dynamic::mk_without_dynamic(def.clone()),
            Some(entry) => entry.clone(),
        };
        let entry = if under_normal_assumptions {
            tast_with_dynamic::T {
                under_normal_assumptions: def,
                ..entry
            }
        } else {
            tast_with_dynamic::T {
                under_dynamic_assumptions: Some(def),
                ..entry
            }
        };
        map.insert(name.to_string(), entry);
    }
    fn program_by_names(
        under_normal_assumptions: bool,
        by_names: ByNames,
        program: Program,
    ) -> ByNames {
        let mut acc = by_names;
        for def in program.0 {
            match &def {
                generic::Def::Fun(f) => {
                    let name = f.name.1.clone();
                    add(under_normal_assumptions, &name, def, &mut acc.fun_tasts)
                }
                generic::Def::Class(c) => {
                    let name = c.name.1.clone();
                    add(under_normal_assumptions, &name, def, &mut acc.class_tasts)
                }
                generic::Def::Typedef(td) => {
                    let name = td.name.1.clone();
                    acc.typedef_tasts.insert(name, def);
                }
                generic::Def::Constant(c) => {
                    let name = c.name.1.clone();
                    acc.gconst_tasts.insert(name, def);
                }
                generic::Def::Module(m) => {
                    let name = m.name.1.clone();
                    acc.module_tasts.insert(name, def);
                }
                generic::Def::ClassAlias(_)
                | generic::Def::Stmt(_)
                | generic::Def::Namespace(_)
                | generic::Def::NamespaceUse(_)
                | generic::Def::SetNamespaceEnv(_)
                | generic::Def::FileAttributes(_)
                | generic::Def::SetModule(_) => {}
            }
        }
        acc
    }
    let tast_with_dynamic::T {
        under_normal_assumptions,
        under_dynamic_assumptions,
    } = program;
    let by_names = empty_by_names();
    let by_names = program_by_names(true, by_names, under_normal_assumptions);
    let by_names = match under_dynamic_assumptions {
        None => by_names,
        Some(program) => program_by_names(false, by_names, program),
    };
    by_names
}

pub fn tasts_as_list(by_names: ByNames) -> Vec<tast_with_dynamic::T<Def>> {
    let ByNames {
        fun_tasts,
        class_tasts,
        typedef_tasts,
        gconst_tasts,
        module_tasts,
    } = by_names;
    // S_map.values is `fold (fun _ v acc -> v :: acc) m []`: the values in the
    // reverse of the order of the keys.
    fn values<V: Clone>(m: SMap<V>) -> impl Iterator<Item = V> {
        m.into_iter().rev().map(|(_, v)| v)
    }
    values(fun_tasts)
        .chain(values(class_tasts))
        .chain(values(typedef_tasts).map(tast_with_dynamic::mk_without_dynamic))
        .chain(values(gconst_tasts).map(tast_with_dynamic::mk_without_dynamic))
        .chain(values(module_tasts).map(tast_with_dynamic::mk_without_dynamic))
        .collect()
}

pub fn empty_saved_env(tcopt: Arc<TypecheckerOptions>) -> SavedEnv {
    SavedEnv {
        tcopt,
        inference_env: crate::typing_inference_env::empty_inference_env(),
        tpenv: crate::type_parameter_env::empty(),
        fun_tast_info: None,
        checked: CheckStatus::COnce,
    }
}

/// Used when an env is needed in codegen.
/// TODO: (arkumar,wilfred,thomasjiang) T42509373 Fix when when needed
pub fn dummy_saved_env() -> SavedEnv {
    // Global_options.default
    empty_saved_env(Arc::new(TypecheckerOptions::default()))
}

pub fn dummy_type_hint(hint: Option<Hint>) -> TypeHint {
    generic::TypeHint(
        crate::typing_defs::mk((
            crate::typing_reason::none(),
            crate::typing_defs::Ty_::Tdynamic(None),
        )),
        hint,
    )
}

/// Helper function to create an annotation for a typed and positioned expression.
/// Do not construct this tuple directly - at some point we will build
/// some abstraction in so that we can change the representation (e.g. put
/// further annotations on the expression) as we see fit.
pub fn make_expr_annotation(_p: &Pos, ty: Ty) -> Ty {
    ty
}

/// Helper function to create a typed and positioned expression.
/// Do not construct this triple directly - at some point we will build
/// some abstraction in so that we can change the representation (e.g. put
/// further annotations on the expression) as we see fit.
pub fn make_typed_expr(p: Pos, ty: Ty, te: Expr_) -> Expr {
    let annotation = make_expr_annotation(&p, ty);
    generic::Expr(annotation, p, te)
}

/// Get the position of an expression
pub fn get_position(e: &Expr) -> &Pos {
    let generic::Expr(_, p, _) = e;
    p
}

/// Get the type of an expression
pub fn get_type(e: &Expr) -> &Ty {
    let generic::Expr(ty, _, _) = e;
    ty
}

// `nast_converter` is
//
//   object
//     inherit [_] Aast.map as super
//     method on_'ex _ _ = ()
//     method on_'en _ _ = ()
//     method! on_Hole _ ex _ _ src =
//       let ((_, pos, ex_) as ex) = super#on_expr () ex in
//       let mk_call hints name =
//         let targs = List.map ~f:(fun hint -> ((), super#on_hint () hint)) hints in
//         let func = ((), pos, Aast.Id (pos, name)) in
//         let args = [Aast.Anormal ex] in
//         Aast.Call { func; targs; args; unpacked_arg = None }
//       in
//       match src with
//       | Aast.UnsafeCast hints -> mk_call hints SN.PseudoFunctions.unsafe_cast
//       | Aast.UnsafeNonnullCast -> mk_call [] SN.PseudoFunctions.unsafe_nonnull_cast
//       | Aast.EnforcedCast hints -> mk_call hints SN.PseudoFunctions.enforced_cast
//       | _ -> ex_
//   end

// `nast_converter`: `Aast.map` with `on_'ex` and `on_'en` giving `()`, and
// `on_Hole` turning the holes of casts back into calls.
//
// The Rust AST has no mapper that changes the annotation types, so the
// annotations are dropped by a serde round trip: the typed AST is encoded
// with its annotations written as nothing (the `Serialize` impls below), and
// decoded as a NAST, whose annotations are `()`. `on_Hole` is then applied
// to the NAST in place, bottom-up, which is what the OCaml computes (the
// conversion of a hole depends only on its position, its source and the
// converted inner expression).

/// Writes nothing: a locl type is only ever serialized to be dropped, by
/// [`to_nast`] and friends.
impl serde::Serialize for Ty {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_unit()
    }
}

/// Writes nothing: see the `Serialize` impl of [`Ty`].
impl serde::Serialize for SavedEnv {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_unit()
    }
}

/// The same AST with `()` annotations: `Ty` and `SavedEnv` are encoded as
/// units, which decode as `()`.
fn drop_annotations<T: serde::Serialize, U: serde::de::DeserializeOwned>(x: &T) -> U {
    let config = bincode::config::standard();
    let bytes = bincode::serde::encode_to_vec(x, config)
        .expect("Tast.to_nast: the typed AST cannot be encoded");
    bincode::serde::decode_from_slice(&bytes, config)
        .expect("Tast.to_nast: the encoded AST cannot be decoded as a NAST")
        .0
}

/// `nast_converter#on_Hole`, applied to every hole of a NAST (inner holes
/// first).
fn convert_holes<T: for<'a> aast_visitor::NodeMut<NastParams>>(node: &mut T) {
    struct Visitor;
    impl<'node> VisitorMut<'node> for Visitor {
        type Params = NastParams;
        fn object(&mut self) -> &mut dyn VisitorMut<'node, Params = Self::Params> {
            self
        }
        fn visit_expr(
            &mut self,
            c: &mut (),
            e: &'node mut nast::Expr,
        ) -> Result<(), std::convert::Infallible> {
            e.recurse(c, self)?;
            let nast::Expr(_, _, expr_) = e;
            if let nast::Expr_::Hole(_) = expr_ {
                let nast::Expr_::Hole(hole) =
                    std::mem::replace(expr_, nast::Expr_::Null)
                else {
                    unreachable!()
                };
                let (ex, (), (), src) = *hole;
                // `let ((_, pos, ex_) as ex) = super#on_expr () ex`: the
                // position of the call is that of the inner expression.
                let pos = ex.1.clone();
                let mk_call = |hints: Vec<nast::Hint>, name: &str, ex: nast::Expr| {
                    let targs = hints.into_iter().map(|hint| nast::Targ((), hint)).collect();
                    let func = nast::Expr((), pos.clone(), nast::Expr_::Id(Box::new(
                        oxidized::ast_defs::Id(pos.clone(), name.to_string()),
                    )));
                    let args = vec![nast::Argument::Anormal(ex)];
                    nast::Expr_::Call(Box::new(nast::CallExpr {
                        func,
                        targs,
                        args,
                        unpacked_arg: None,
                    }))
                };
                use naming_special_names_rust::pseudo_functions as pf;
                *expr_ = match src {
                    nast::HoleSource::UnsafeCast(hints) => mk_call(hints, pf::UNSAFE_CAST, ex),
                    nast::HoleSource::UnsafeNonnullCast => {
                        mk_call(vec![], pf::UNSAFE_NONNULL_CAST, ex)
                    }
                    nast::HoleSource::EnforcedCast(hints) => {
                        mk_call(hints, pf::ENFORCED_CAST, ex)
                    }
                    nast::HoleSource::Typing => ex.2,
                };
            }
            Ok(())
        }
    }
    match node.accept(&mut (), &mut Visitor) {
        Ok(()) => {}
        Err(e) => match e {},
    }
}

/// The parameters of an `oxidized::aast_visitor` over a NAST.
struct NastParams;

impl aast_visitor::Params for NastParams {
    type Context = ();
    type Error = std::convert::Infallible;
    type Ex = ();
    type En = ();
}

pub fn to_nast(p: Program) -> nast::Program {
    let mut program: nast::Program = drop_annotations(&p);
    convert_holes(&mut program);
    program
}

pub fn to_nast_expr(tast: Expr) -> nast::Expr {
    let mut expr: nast::Expr = drop_annotations(&tast);
    convert_holes(&mut expr);
    expr
}

pub fn to_nast_class_id_(cid: generic::ClassId_<Ty, SavedEnv>) -> nast::ClassId_ {
    let mut cid: nast::ClassId_ = drop_annotations(&cid);
    convert_holes(&mut cid);
    cid
}

pub fn force_lazy_values_saved_env(saved_env: SavedEnv) -> SavedEnv {
    let mut saved_env = saved_env;
    force_lazy_values_saved_env_in_place(&mut saved_env);
    saved_env
}

/// [`force_lazy_values_saved_env`], on a saved environment that is in an AST.
fn force_lazy_values_saved_env_in_place(saved_env: &mut SavedEnv) {
    let SavedEnv {
        tcopt: _,
        inference_env,
        tpenv,
        fun_tast_info: _,
        checked: _,
    } = saved_env;
    crate::typing_inference_env::force_lazy_values(inference_env);
    crate::type_parameter_env::force_lazy_values(tpenv);
}

/// The parameters of an `oxidized::aast_visitor` over a typed AST.
struct TastParams;

impl aast_visitor::Params for TastParams {
    type Context = ();
    type Error = std::convert::Infallible;
    type Ex = Ty;
    type En = SavedEnv;
}

/// Force any lazy value in the TAST. This is useful to serialize the TAST,
/// for example prior to returning over RPC or storing in the shared heap.
pub fn force_lazy_values(program: Program) -> Program {
    struct Visitor;

    impl<'node> VisitorMut<'node> for Visitor {
        type Params = TastParams;

        fn object(&mut self) -> &mut dyn VisitorMut<'node, Params = Self::Params> {
            self
        }

        // method on_'ex _env ty = Type_force_lazy_values.locl_ty ty
        fn visit_ex(
            &mut self,
            _env: &mut (),
            ty: &'node mut Ty,
        ) -> Result<(), std::convert::Infallible> {
            let placeholder = crate::typing_defs::mk((
                crate::typing_reason::none(),
                crate::typing_defs::Ty_::Tnonnull,
            ));
            let forced = crate::type_force_lazy_values::locl_ty(std::mem::replace(ty, placeholder));
            *ty = forced;
            Ok(())
        }

        // method on_'en _env (saved_env : saved_env) =
        //   force_lazy_values_saved_env saved_env
        fn visit_en(
            &mut self,
            _env: &mut (),
            saved_env: &'node mut SavedEnv,
        ) -> Result<(), std::convert::Infallible> {
            force_lazy_values_saved_env_in_place(saved_env);
            Ok(())
        }
    }

    let mut program = program;
    match program.accept(&mut (), &mut Visitor) {
        Ok(()) => {}
        Err(e) => match e {},
    }
    program
}

#[cfg(test)]
mod tests {
    use oxidized::ast_defs;

    use super::*;
    use crate::typing_defs::Ty_;
    use crate::typing_defs::get_node;
    use crate::typing_defs::mk;

    fn int() -> Ty {
        mk((
            crate::typing_reason::none(),
            Ty_::Tprim(ast_defs::Tprim::Tint),
        ))
    }

    fn id(name: &str) -> ast_defs::Id {
        ast_defs::Id(Pos::NONE, name.to_string())
    }

    fn module_def(name: &str) -> Def {
        generic::Def::Module(Box::new(generic::ModuleDef {
            annotation: dummy_saved_env(),
            name: id(name),
            user_attributes: generic::UserAttributes(vec![]),
            file_attributes: vec![],
            span: Pos::NONE,
            mode: oxidized::file_info::Mode::Mstrict,
            doc_comment: None,
        }))
    }

    /// `function name(): void {}`, with `kind` to tell two definitions apart.
    fn fun_def(name: &str, kind: ast_defs::FunKind) -> Def {
        generic::Def::Fun(Box::new(generic::FunDef {
            namespace: std::sync::Arc::new(oxidized::namespace_env::Env::empty(
                vec![],
                oxidized::namespace_env::Mode::ForTypecheck,
                false,
            )),
            file_attributes: vec![],
            mode: oxidized::file_info::Mode::Mstrict,
            name: id(name),
            fun: generic::Fun_ {
                span: Pos::NONE,
                readonly_this: None,
                annotation: dummy_saved_env(),
                readonly_ret: None,
                tparams: vec![],
                ret: dummy_type_hint(None),
                params: vec![],
                ctxs: None,
                unsafe_ctxs: None,
                body: generic::FuncBody {
                    fb_ast: generic::Block(vec![]),
                },
                fun_kind: kind,
                user_attributes: generic::UserAttributes(vec![]),
                external: false,
                hidden: false,
                doc_comment: None,
            },
            internal: false,
            module: None,
            tparams: vec![],
            where_constraints: vec![],
            package: None,
        }))
    }

    fn fun_kind(def: &Def) -> ast_defs::FunKind {
        match def {
            generic::Def::Fun(f) => f.fun.fun_kind,
            _ => panic!("not a function"),
        }
    }

    fn def_name(def: &Def) -> &str {
        match def {
            generic::Def::Fun(f) => &f.name.1,
            generic::Def::Module(m) => &m.name.1,
            _ => panic!("unexpected definition"),
        }
    }

    #[test]
    fn typed_exprs() {
        let e = make_typed_expr(Pos::NONE, int(), generic::Expr_::Null);
        assert!(matches!(
            get_node(get_type(&e)),
            Ty_::Tprim(ast_defs::Tprim::Tint)
        ));
        assert_eq!(get_position(&e), &Pos::NONE);
        let generic::TypeHint(ty, hint) = dummy_type_hint(None);
        assert!(matches!(get_node(&ty), Ty_::Tdynamic(None)));
        assert!(hint.is_none());
        assert!(is_under_dynamic_assumptions(
            CheckStatus::CUnderDynamicAssumptions
        ));
        assert!(!is_under_dynamic_assumptions(CheckStatus::COnce));
        assert!(!is_under_dynamic_assumptions(
            CheckStatus::CUnderNormalAssumptions
        ));
        let env = dummy_saved_env();
        assert!(env.fun_tast_info.is_none());
        assert_eq!(env.checked, CheckStatus::COnce);
    }

    #[test]
    fn by_names() {
        use ast_defs::FunKind::*;
        let noop = || generic::Def::Stmt(Box::new(generic::Stmt(Pos::NONE, generic::Stmt_::Noop)));
        let normal = generic::Program(vec![
            fun_def("\\g", FSync),
            noop(),
            module_def("m2"),
            fun_def("\\f", FSync),
            module_def("m1"),
        ]);
        // only f is checked under dynamic assumptions too
        let dynamic = generic::Program(vec![fun_def("\\f", FAsync)]);
        let by_names = program_by_names(tast_with_dynamic::T {
            under_normal_assumptions: normal,
            under_dynamic_assumptions: Some(dynamic),
        });
        assert_eq!(by_names.fun_tasts.len(), 2);
        assert_eq!(by_names.module_tasts.len(), 2);
        assert!(by_names.class_tasts.is_empty());
        assert!(by_names.typedef_tasts.is_empty() && by_names.gconst_tasts.is_empty());
        let f = &by_names.fun_tasts["\\f"];
        assert_eq!(fun_kind(&f.under_normal_assumptions), FSync);
        assert_eq!(
            f.under_dynamic_assumptions.as_ref().map(fun_kind),
            Some(FAsync)
        );
        let g = &by_names.fun_tasts["\\g"];
        assert_eq!(fun_kind(&g.under_normal_assumptions), FSync);
        assert!(g.under_dynamic_assumptions.is_none());

        // functions, then classes, typedefs, constants and modules, each in the
        // reverse of the order of the names
        let list = tasts_as_list(by_names.clone());
        let names: Vec<&str> = list
            .iter()
            .map(|d| def_name(&d.under_normal_assumptions))
            .collect();
        assert_eq!(names, vec!["\\g", "\\f", "m2", "m1"]);
        assert!(list[2].under_dynamic_assumptions.is_none());

        // map_by_names maps both versions of a definition
        let mapped = map_by_names(by_names, |def| match def {
            generic::Def::Fun(_) => fun_def("\\renamed", FGenerator),
            def => def,
        });
        let f = &mapped.fun_tasts["\\f"];
        assert_eq!(fun_kind(&f.under_normal_assumptions), FGenerator);
        assert_eq!(
            f.under_dynamic_assumptions.as_ref().map(fun_kind),
            Some(FGenerator)
        );
        assert_eq!(mapped.module_tasts.len(), 2);

        // a definition that is only checked under dynamic assumptions
        let by_names = program_by_names(tast_with_dynamic::T {
            under_normal_assumptions: generic::Program(vec![]),
            under_dynamic_assumptions: Some(generic::Program(vec![fun_def("\\f", FAsync)])),
        });
        let f = &by_names.fun_tasts["\\f"];
        assert_eq!(fun_kind(&f.under_normal_assumptions), FAsync);
        assert_eq!(
            f.under_dynamic_assumptions.as_ref().map(fun_kind),
            Some(FAsync)
        );
    }
}
