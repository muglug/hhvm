// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_print.ml`: pretty printing of types, as they appear in
//! error messages.
//!
//! - Decl types are printed from their oxidized form
//!   (`oxidized::typing_defs_core::Ty`; a `ty::decl::Ty` has `to_oxidized`).
//! - Locl types, constraint types and internal types are the ones of
//!   [`locl`]: `oxidized` only has the types of the decl phase.
//! - The typing environment is whatever implements [`PrintEnv`]: the real
//!   environment (with `--features port`) and [`SimpleEnv`].
//!
//! The OCaml builds a `Doc.t` and has `Libhackfmt.format_doc_unbroken` lay it
//! out on one line. [`doc`] has the part of that which matters here.
//!
//! Not ported: `full_with_identity` and `full_decl_with_identity` (hover and
//! other IDE services; they need `Symbol_occurrence`, `Symbol_definition` and
//! the line-breaking layout of `Libhackfmt.format_doc`), `subtype_prop`
//! (debugging; needs `Typing_logic`) and the JSON output.

/// The types of the locl phase.
///
/// Without the `port` feature, the provisional definitions of `locl.rs`. With
/// it, the ports of `typing_defs_core.ml` and `typing_defs_constraints.ml`,
/// which define the same types (same constructors, same fields).
#[cfg(not(feature = "port"))]
pub mod locl;
#[cfg(feature = "port")]
pub mod locl {
    pub use crate::typing_defs_constraints::*;
    pub use crate::typing_defs_core::*;
}

use std::borrow::Cow;
use std::collections::BTreeSet;

use naming_special_names_rust as sn;
use oxidized::ast_defs::Abstraction;
use oxidized::ast_defs::ClassishKind;
use oxidized::ast_defs::ConstraintKind;
use oxidized::ast_defs::ReifyKind;
use oxidized::ast_defs::Tprim;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use oxidized::t_shape_map::TShapeField;
use oxidized::t_shape_map::TShapeMap;
use oxidized::typechecker_options::TypecheckerOptions;
use oxidized::typing_defs_core as decl;
use oxidized::typing_defs_core::TshapeFieldName;
use oxidized::typing_defs_core::TypeOrigin;
use oxidized::typing_defs_flags::FunParamFlags;
use oxidized::typing_defs_flags::FunTypeFlags;

use self::doc::Doc;
use self::doc::text;
use self::locl::ConstraintType;
use self::locl::ConstraintType_;
use self::locl::Exact;
use self::locl::InternalType;
use self::locl::Ty;
use self::locl::Ty_;
use self::locl::TypePredicate;
use self::locl::TypePredicate_;
use self::locl::TypeTag;
use self::locl::TypeTagGeneric;
use crate::typing_reason as reason;
use crate::typing_reason::Tvid;

/// `Typing_defs.decl_ty`, in its oxidized form.
pub type DeclTy = decl::Ty;

/// `Tvid.Set.t`
type TvidSet = BTreeSet<Tvid>;

// ~~ The functions of `Typing_defs` that the printer uses ~~~~~~~~~~~~~~~~~~~~
//
// They are written here, on the structure of the types, so that the printer
// only depends on the shape of the locl types, not on which module has them.

/// `mk`
#[cfg(not(feature = "port"))]
fn mk(r: reason::T, node: Ty_) -> Ty {
    locl::Ty(r, std::rc::Rc::new(node))
}

/// `mk`
#[cfg(feature = "port")]
fn mk(r: reason::T, node: Ty_) -> Ty {
    locl::Ty(r, std::rc::Rc::new(locl::TyNode::new(node)))
}

/// `Typing_defs.is_nothing`
fn is_nothing(ty: &Ty) -> bool {
    matches!(ty.get_node(), Ty_::Tunion(tyl) if tyl.is_empty())
}

/// `Typing_defs.is_dynamic`
fn is_dynamic(ty: &Ty) -> bool {
    matches!(ty.get_node(), Ty_::Tdynamic(_))
}

/// `Typing_defs.DependentKind.to_string`
fn dependent_kind_to_string(dep: &locl::DependentType) -> String {
    match dep {
        locl::DependentType::DTexpr(i) => reason::expression_id_display(*i),
    }
}

/// `Typing_defs.DependentKind.is_generic_dep_ty`
fn is_generic_dep_ty(s: &str) -> bool {
    s.contains("::") || s == sn::typehints::THIS
}

/// `refined_const_kind_str`
fn refined_const_kind_str(is_ctx: bool) -> &'static str {
    if is_ctx { "ctx" } else { "type" }
}

/// `ty_equal ~normalize_lists:true`
fn ty_equal_normalize_lists(ty1: &Ty, ty2: &Ty) -> bool {
    #[cfg(not(feature = "port"))]
    let equal = locl::ty_equal(true, ty1, ty2);
    #[cfg(feature = "port")]
    let equal = locl::ty_equal(Some(true), ty1, ty2);
    equal
}

// ~~ The environment ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// What the printer reads from the typing environment
/// (`Typing_env_types.env`). Whoever writes the environment implements this
/// for it.
pub trait PrintEnv {
    /// `Typing_inference_env.expand_type env.inference_env ty` (without the
    /// environment it returns): if `ty` is a type variable, its current
    /// solution (itself if it has none); any other type is returned as it is.
    ///
    /// This also stands for `Typing_inference_env.expand_var`, which is
    /// `expand_type` of a `Tvar`.
    fn expand_type<'a>(&'a self, ty: &'a Ty) -> Cow<'a, Ty>;

    /// `Typing_env_types.get_log_level env key`: the level set by
    /// `hh_log_level(key, level)` or the `log_levels` option, 0 by default.
    /// The printer asks for the key `"show"`.
    fn get_log_level(&self, key: &str) -> isize;

    /// `env.genv.tcopt`. The printer reads `Typechecker_options.everything_sdt`
    /// (`po.everything_sdt`) and `type_printer_fuel` (`tco_type_printer_fuel`).
    fn get_tcopt(&self) -> &TypecheckerOptions;

    /// `TySet.elements (Typing_env_types.get_lower_bounds env name)`: the
    /// lower bounds of the type parameter `name`, from the local and the
    /// global type parameter environments, in the order of `Typing_set`.
    fn get_lower_bounds(&self, name: &str) -> Vec<Ty>;

    /// `TySet.elements (Typing_env_types.get_upper_bounds env name)`.
    ///
    /// (`Typing_env_types.get_equal_bounds` is the intersection of the two.)
    fn get_upper_bounds(&self, name: &str) -> Vec<Ty>;

    /// `ITySet.elements (Typing_inference_env.get_tyvar_upper_bounds
    /// env.inference_env var)`. Only [`coeffects`] uses it.
    fn get_tyvar_upper_bounds(&self, var: Tvid) -> Vec<InternalType>;
}

/// A small environment for tests and for printing outside of a typing
/// environment: options, log levels, solved type variables and bounds are
/// plain fields, all empty by default (no type variable is solved).
#[derive(Clone, Debug, Default)]
pub struct SimpleEnv {
    pub tcopt: TypecheckerOptions,
    pub log_levels: std::collections::BTreeMap<String, isize>,
    /// The solutions of the solved type variables.
    pub tyvars: std::collections::BTreeMap<Tvid, Ty>,
    pub lower_bounds: std::collections::BTreeMap<String, BTreeSet<Ty>>,
    pub upper_bounds: std::collections::BTreeMap<String, BTreeSet<Ty>>,
    pub tyvar_upper_bounds: std::collections::BTreeMap<Tvid, Vec<InternalType>>,
}

impl PrintEnv for SimpleEnv {
    fn expand_type<'a>(&'a self, ty: &'a Ty) -> Cow<'a, Ty> {
        let mut ty = ty;
        // A bound on the number of steps, in case of a cycle.
        for _ in 0..=self.tyvars.len() {
            match ty.get_node() {
                Ty_::Tvar(v) => match self.tyvars.get(v) {
                    Some(solution) => ty = solution,
                    None => break,
                },
                _ => break,
            }
        }
        Cow::Borrowed(ty)
    }

    fn get_log_level(&self, key: &str) -> isize {
        self.log_levels.get(key).copied().unwrap_or(0)
    }

    fn get_tcopt(&self) -> &TypecheckerOptions {
        &self.tcopt
    }

    fn get_lower_bounds(&self, name: &str) -> Vec<Ty> {
        match self.lower_bounds.get(name) {
            Some(bounds) => bounds.iter().cloned().collect(),
            None => vec![],
        }
    }

    fn get_upper_bounds(&self, name: &str) -> Vec<Ty> {
        match self.upper_bounds.get(name) {
            Some(bounds) => bounds.iter().cloned().collect(),
            None => vec![],
        }
    }

    fn get_tyvar_upper_bounds(&self, var: Tvid) -> Vec<InternalType> {
        self.tyvar_upper_bounds
            .get(&var)
            .cloned()
            .unwrap_or_default()
    }
}

/// The typing environment, once it exists (`--features port`).
#[cfg(feature = "port")]
impl PrintEnv for crate::typing_env_types::Env {
    fn expand_type<'a>(&'a self, ty: &'a Ty) -> Cow<'a, Ty> {
        match ty.get_node() {
            Ty_::Tvar(_) => {
                // `Typing_inference_env.expand_type` returns an environment
                // (with shorter paths between type variables) that the
                // printer drops: it works on a copy.
                let mut inference_env = self.inference_env.clone();
                Cow::Owned(crate::typing_inference_env::expand_type(
                    &mut inference_env,
                    ty.clone(),
                ))
            }
            _ => Cow::Borrowed(ty),
        }
    }

    fn get_log_level(&self, key: &str) -> isize {
        crate::typing_env_types::get_log_level(self, key)
    }

    fn get_tcopt(&self) -> &TypecheckerOptions {
        &self.genv.tcopt
    }

    fn get_lower_bounds(&self, name: &str) -> Vec<Ty> {
        crate::typing_env_types::get_lower_bounds(self, name)
            .iter()
            .cloned()
            .collect()
    }

    fn get_upper_bounds(&self, name: &str) -> Vec<Ty> {
        crate::typing_env_types::get_upper_bounds(self, name)
            .iter()
            .cloned()
            .collect()
    }

    fn get_tyvar_upper_bounds(&self, var: Tvid) -> Vec<InternalType> {
        crate::typing_inference_env::get_tyvar_upper_bounds(&self.inference_env, var)
            .iter()
            .cloned()
            .collect()
    }
}

// ~~ Doc ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// The part of hackfmt's `Doc.t` that the printer builds, and its one-line
/// layout (`Libhackfmt.format_doc_unbroken`).
///
/// On one line, the solver's hints are inert: `Split` is nothing, and `Nest`,
/// `Span` and `WithRule` are `Concat`. What remains is `Space`: it does not
/// print a space, it asks for one before the next text, so that several spaces
/// in a row, or spaces around a `Split`, print one space, and a space that no
/// text follows prints nothing.
pub(crate) mod doc {
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Doc {
        Nothing,
        Concat(Vec<Doc>),
        Text(String),
        Newline,
        Space,
        /// `Split`: breaking point for the line solver
        Split,
        /// `SplitWith Cost.Base`
        SplitWithBase,
        /// `Nest`: indented if it breaks across lines
        Nest(Vec<Doc>),
        /// `Span`: prefers to stay on one line
        Span(Vec<Doc>),
        /// `WithRule (Rule.Parental, doc)`
        WithRuleParental(Box<Doc>),
    }

    /// `Doc.text`
    pub fn text(s: impl Into<String>) -> Doc {
        Doc::Text(s.into())
    }

    /// `a ^^ b`
    pub fn cat(a: Doc, b: Doc) -> Doc {
        Doc::Concat(vec![a, b])
    }

    /// `Libhackfmt.format_doc_unbroken env doc`, without the newline that ends
    /// the output (every caller strips the result).
    ///
    /// A `Newline` starts a new line unless nothing was printed yet; the line
    /// is not indented (no caller puts a `Newline` inside a `Nest`).
    pub fn format_doc_unbroken(doc: &Doc) -> String {
        struct State {
            out: String,
            pending_space: bool,
            pending_newline: bool,
        }
        fn go(doc: &Doc, st: &mut State) {
            match doc {
                Doc::Nothing | Doc::Split | Doc::SplitWithBase => {}
                Doc::Concat(docs) | Doc::Nest(docs) | Doc::Span(docs) => docs.iter().for_each(|d| go(d, st)),
                Doc::WithRuleParental(d) => go(d, st),
                Doc::Text(s) => {
                    if st.pending_newline {
                        // The chunk after a hard split starts its line: the
                        // space asked for before it is not printed.
                        st.out.push('\n');
                    } else if st.pending_space {
                        st.out.push(' ');
                    }
                    st.pending_newline = false;
                    st.pending_space = false;
                    st.out.push_str(s);
                }
                Doc::Newline => {
                    if !st.out.is_empty() {
                        st.pending_newline = true;
                    }
                }
                Doc::Space => st.pending_space = true,
            }
        }
        let mut st = State {
            out: String::new(),
            pending_space: false,
            pending_newline: false,
        };
        go(doc, &mut st);
        st.out
    }

    /// `Libhackfmt.format_doc env doc` with the printer's `format_env`
    /// (`Format_env.{ default with line_width = 60 }`): the doc laid out by
    /// hackfmt's line solver, which breaks lines at the splits.
    pub fn format_doc(doc: &Doc) -> String {
        use hackfmt::doc as h;
        fn conv(doc: &Doc) -> h::Doc<'_> {
            fn list(docs: &[Doc]) -> Vec<h::Doc<'_>> {
                docs.iter().map(conv).collect()
            }
            match doc {
                Doc::Nothing => h::Doc::Nothing,
                Doc::Concat(docs) => h::Doc::Concat(list(docs)),
                Doc::Text(s) => h::Doc::text(s.as_bytes()),
                Doc::Newline => h::Doc::Newline,
                Doc::Space => h::Doc::Space,
                Doc::Split => h::Doc::Split,
                Doc::SplitWithBase => h::Doc::SplitWith(h::Cost::Base),
                Doc::Nest(docs) => h::Doc::Nest(list(docs)),
                Doc::Span(docs) => h::Doc::Span(list(docs)),
                Doc::WithRuleParental(d) => h::Doc::with_rule(h::RuleKind::Parental, conv(d)),
            }
        }
        let env = hackfmt::Env {
            line_width: 60,
            // OCaml hackfmt's layout.
            hakana_rules: false,
            ..hackfmt::Env::default()
        };
        let doc = conv(doc);
        let chunk_groups = hackfmt::chunk_builder::build(&env, &doc);
        let out = hackfmt::line_splitter::solve(&env, None, true, true, None, &chunk_groups);
        String::from_utf8_lossy(&out).into_owned()
    }

    /// `String.strip`: drop the leading and trailing whitespace, where
    /// whitespace is what `Char.is_whitespace` says.
    pub fn strip(s: &str) -> &str {
        s.trim_matches(|c| matches!(c, ' ' | '\t' | '\n' | '\x0b' | '\x0c' | '\r'))
    }
}

use self::doc::cat;

// ~~ Fuel ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// Fuel ensures that types are curtailed while printing them. This avoids
/// performance regressions and increases readibility of errors overall.
///
/// The OCaml threads the fuel through every function (`~fuel` in, `fuel` out).
/// Here it is one value that the printers decrement in place, in the same
/// order.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Fuel(isize);

impl Fuel {
    fn init(fuel: isize) -> Self {
        Fuel(fuel)
    }

    fn deplete(&mut self) {
        self.0 -= 1;
    }

    fn has_enough(&self) -> bool {
        self.0 >= 0
    }

    /// `provide fuel f` consumes one unit of fuel to call f, plus fuel
    /// consumed by f itself, provided there's enough fuel. If not, it returns
    /// the text doc "[truncated]".
    fn provide(&mut self, f: impl FnOnce(&mut Fuel) -> Doc) -> Doc {
        if self.has_enough() {
            self.deplete();
            f(self)
        } else {
            text("[truncated]")
        }
    }

    /// `provide_list fuel f inputs ~out_of_fuel_message` consumes fuel to call
    /// f on each element of a list of inputs until we're out of fuel. It
    /// consumes one unit of fuel per call to f plus the fuel consumed by f
    /// itself. When out of fuel, it appends the text doc
    /// "[out_of_fuel_message]" to the results.
    ///
    /// (An input for which `f` gives `None` consumes no fuel.)
    fn provide_list<I>(
        &mut self,
        mut f: impl FnMut(I, &mut Fuel) -> Option<Doc>,
        inputs: impl IntoIterator<Item = I>,
        out_of_fuel_message: &str,
    ) -> Vec<Doc> {
        let mut acc = vec![];
        for input in inputs {
            if !self.has_enough() {
                acc.push(text(format!("[{}]", out_of_fuel_message)));
                break;
            }
            let fuel = *self;
            self.deplete();
            match f(input, self) {
                Some(doc) => acc.push(doc),
                None => *self = fuel,
            }
        }
        acc
    }
}

/// For sake of typing_print, either we wish to print a locl_ty in which case we
/// need the env to look up the typing environment and constraints and the
/// like, or a decl_ty in which case we don't need anything. [penv] stands for
/// "printing env".
enum Penv<'a, E: ?Sized> {
    Loclenv(&'a E),
    Declenv,
}

// Not derived: `E` need not be `Clone`.
impl<E: ?Sized> Clone for Penv<'_, E> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<E: ?Sized> Copy for Penv<'_, E> {}

/// `SN.Coeffects.is_generated_generic`
fn is_generated_generic(name: &str) -> bool {
    name.starts_with("T/")
}

/// `SN.Coeffects.unwrap_generated_generic`: "T/[ctx $foo]" to "ctx $foo".
fn unwrap_generated_generic(name: &str) -> &str {
    let name = name.strip_prefix("T/[").unwrap_or(name);
    name.strip_suffix(']').unwrap_or(name)
}

/// Split type parameters [tparams] into normal user-denoted type parameters,
/// and a list of polymorphic context names that were desugared to type
/// parameters.
pub fn split_desugared_ctx_tparams_gen<A>(
    tparams: Vec<A>,
    param_name: impl Fn(&A) -> String,
) -> (Vec<String>, Vec<A>) {
    let (generated_tparams, other_tparams): (Vec<A>, Vec<A>) = tparams
        .into_iter()
        .partition(|param| is_generated_generic(&param_name(param)));
    let desugared_tparams = generated_tparams
        .iter()
        .map(|param| unwrap_generated_generic(&param_name(param)).to_string())
        .collect();
    (desugared_tparams, other_tparams)
}

pub fn strip_ns(id: &str) -> String {
    reason::strip_ns(id).to_string()
}

fn show_supportdyn<E: PrintEnv + ?Sized>(env: &E) -> bool {
    !env.get_tcopt().po.everything_sdt || env.get_log_level("show") >= 1
}

// ~~ Views ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
//
// In OCaml the function, tuple, shape and refinement types are polymorphic in
// the phase (`'phase ty fun_type`), and so are the functions that print them.
// Here the decl types are `oxidized`'s and the locl types are `locl`'s: two
// families of unrelated structs. The printers they share are generic in the
// type `T` and read these views, which each family builds from its own
// structs (`views!` below).

struct TparamView<'a, T> {
    name: &'a str,
    constraints: Vec<(ConstraintKind, &'a T)>,
    reified: ReifyKind,
}

struct FunParamView<'a, T> {
    name: Option<&'a str>,
    type_: &'a T,
    flags: FunParamFlags,
}

enum CapabilityView<'a, T> {
    CapDefaults,
    CapTy(&'a T),
}

struct FunTypeView<'a, T> {
    tparams: Vec<TparamView<'a, T>>,
    where_constraints: Vec<(&'a T, ConstraintKind, &'a T)>,
    params: Vec<FunParamView<'a, T>>,
    capability: CapabilityView<'a, T>,
    ret: &'a T,
    flags: FunTypeFlags,
}

enum TupleExtraView<'a, T> {
    Tvariadic(&'a T),
    Tsplat(&'a T),
}

struct ShapeFieldView<'a, T> {
    name: &'a TShapeField,
    optional: bool,
    ty: &'a T,
}

enum RefinedConstBoundView<'a, T> {
    TRexact(&'a T),
    TRloose { lower: &'a [T], upper: &'a [T] },
}

struct RefinedConstView<'a, T> {
    name: &'a str,
    is_ctx: bool,
    bound: RefinedConstBoundView<'a, T>,
}

macro_rules! views {
    ($name:ident, $($family:tt)+) => {
        mod $name {
            use $($family)+ as f;

            use super::*;

            pub(super) fn fun_type(ft: &f::FunType) -> FunTypeView<'_, f::Ty> {
                FunTypeView {
                    tparams: ft
                        .tparams
                        .iter()
                        .map(|tp| TparamView {
                            name: &tp.name.1,
                            constraints: tp.constraints.iter().map(|(ck, ty)| (*ck, ty)).collect(),
                            reified: tp.reified,
                        })
                        .collect(),
                    where_constraints: ft
                        .where_constraints
                        .iter()
                        .map(|f::WhereConstraint(l, ck, r)| (l, *ck, r))
                        .collect(),
                    params: ft
                        .params
                        .iter()
                        .map(|p| FunParamView {
                            name: p.name.as_deref(),
                            type_: &p.type_,
                            flags: p.flags,
                        })
                        .collect(),
                    capability: match &ft.implicit_params.capability {
                        f::Capability::CapDefaults(_) => CapabilityView::CapDefaults,
                        f::Capability::CapTy(t) => CapabilityView::CapTy(t),
                    },
                    ret: &ft.ret,
                    flags: ft.flags,
                }
            }

            pub(super) fn tuple_extra(extra: &f::TupleExtra) -> TupleExtraView<'_, f::Ty> {
                match extra {
                    f::TupleExtra::Tvariadic(t) => TupleExtraView::Tvariadic(t),
                    f::TupleExtra::Tsplat(t) => TupleExtraView::Tsplat(t),
                }
            }

            /// `TShapeMap.bindings`
            pub(super) fn shape_fields(
                fields: &TShapeMap<f::ShapeFieldType>,
            ) -> Vec<ShapeFieldView<'_, f::Ty>> {
                fields
                    .iter()
                    .map(|(name, sft)| ShapeFieldView {
                        name,
                        optional: sft.optional,
                        ty: &sft.ty,
                    })
                    .collect()
            }

            /// `S_map.bindings cr_consts`
            pub(super) fn refinement(r: &f::ClassRefinement) -> Vec<RefinedConstView<'_, f::Ty>> {
                r.cr_consts
                    .iter()
                    .map(|(name, rc)| RefinedConstView {
                        name,
                        is_ctx: rc.is_ctx,
                        bound: match &rc.bound {
                            f::RefinedConstBound::TRexact(ty) => RefinedConstBoundView::TRexact(ty),
                            f::RefinedConstBound::TRloose(bounds) => RefinedConstBoundView::TRloose {
                                lower: &bounds.lower,
                                upper: &bounds.upper,
                            },
                        },
                    })
                    .collect()
            }
        }
    };
}

views!(decl_views, oxidized::typing_defs_core);
views!(locl_views, super::locl);

/// `Typing_defs.TShapeField.name`
fn tshape_field_name(field: &TshapeFieldName) -> String {
    match field {
        TshapeFieldName::TSFregexGroup(decl::PosString(_, s)) => s.clone(),
        // (An OCaml string is bytes; a field name that is not UTF-8 cannot be
        // printed exactly here.)
        TshapeFieldName::TSFlitStr(decl::PosByteString(_, s)) => {
            String::from_utf8_lossy(s.as_slice()).into_owned()
        }
        TshapeFieldName::TSFclassConst((_, s1), decl::PosString(_, s2)) => {
            format!("{}::{}", s1, s2)
        }
    }
}

// ~~ Pretty-printer of the "full" type ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// `Full`: the pretty-printer of the "full" type.
mod full {
    use super::*;

    /// How a name is turned into a doc (`to_doc`).
    pub(super) type ToDoc<'a> = &'a dyn Fn(&str) -> Doc;

    /// A printer of the types of one phase, with everything but the fuel and
    /// the type applied (`k`, or `ty ~fuel to_doc st penv`).
    pub(super) type TyPrinter<'a, T> = &'a dyn Fn(&mut Fuel, &T) -> Doc;

    pub(super) fn text_strip_ns(s: &str) -> Doc {
        text(reason::strip_ns(s))
    }

    pub(super) fn text_strip_all_ns(s: &str) -> Doc {
        text(reason::utils_strip_all_ns(s))
    }

    pub(super) fn doc_text(s: &str) -> Doc {
        text(s)
    }

    fn show_verbose<E: PrintEnv + ?Sized>(penv: Penv<'_, E>) -> bool {
        match penv {
            Penv::Loclenv(env) => env.get_log_level("show") > 1,
            Penv::Declenv => false,
        }
    }

    /// Until we support NoAutoDynamic, all types under everything-sdt support
    /// dynamic so displaying supportdyn is redundant
    fn show_supportdyn_penv<E: PrintEnv + ?Sized>(penv: Penv<'_, E>) -> bool {
        match penv {
            Penv::Loclenv(env) => show_supportdyn(env),
            Penv::Declenv => false,
        }
    }

    fn comma_sep() -> Doc {
        Doc::Concat(vec![text(","), Doc::Space])
    }

    fn semi_sep() -> Doc {
        Doc::Concat(vec![text(";"), Doc::Space])
    }

    fn id(_fuel: &mut Fuel, x: Doc) -> Doc {
        x
    }

    fn list_sep<A>(fuel: &mut Fuel, s: Doc, f: impl FnMut(&mut Fuel, A) -> Doc, l: Vec<A>) -> Doc {
        list_sep_split(fuel, true, s, f, l)
    }

    /// `list_sep ~fuel ~split s f l`
    fn list_sep_split<A>(
        fuel: &mut Fuel,
        split: bool,
        s: Doc,
        mut f: impl FnMut(&mut Fuel, A) -> Doc,
        l: Vec<A>,
    ) -> Doc {
        let split = || if split { Doc::Split } else { Doc::Nothing };
        let max_idx = l.len().wrapping_sub(1);
        let elements: Vec<Doc> = l
            .into_iter()
            .enumerate()
            .map(|(idx, element)| {
                let d = f(fuel, element);
                if idx == max_idx {
                    d
                } else {
                    Doc::Concat(vec![d, s.clone(), split()])
                }
            })
            .collect();
        match elements.len() {
            0 => Doc::Nothing,
            _ => Doc::Nest(vec![split(), Doc::Concat(elements), split()]),
        }
    }

    fn delimited_list<A>(
        fuel: &mut Fuel,
        sep: Doc,
        skip_brackets_for_singleton: bool,
        left_delimiter: &str,
        f: impl FnMut(&mut Fuel, A) -> Doc,
        l: Vec<A>,
        right_delimiter: &str,
    ) -> Doc {
        let len = l.len();
        let doc = list_sep(fuel, sep, f, l);
        if skip_brackets_for_singleton && len == 1 {
            doc
        } else {
            Doc::Span(vec![
                text(left_delimiter),
                Doc::WithRuleParental(Box::new(Doc::Concat(vec![doc, text(right_delimiter)]))),
            ])
        }
    }

    fn list<A>(
        fuel: &mut Fuel,
        ld: &str,
        printer: impl FnMut(&mut Fuel, A) -> Doc,
        items: Vec<A>,
        rd: &str,
    ) -> Doc {
        delimited_list(fuel, comma_sep(), false, ld, printer, items, rd)
    }

    fn shape_filter_map<'a, T>(
        fuel: &mut Fuel,
        fdm: Vec<ShapeFieldView<'a, T>>,
        f_field: impl FnMut(ShapeFieldView<'a, T>, &mut Fuel) -> Option<Doc>,
    ) -> Vec<Doc> {
        let mut fields: Vec<(String, ShapeFieldView<'a, T>)> = fdm
            .into_iter()
            .map(|field| (tshape_field_name(&field.name.0), field))
            .collect();
        // `List.sort` is stable.
        fields.sort_by(|(k1, _), (k2, _)| k1.as_bytes().cmp(k2.as_bytes()));
        fuel.provide_list(
            f_field,
            fields.into_iter().map(|(_, field)| field),
            "shape was truncated",
        )
    }

    /// Split type parameters [tparams] into normal user-denoted type
    /// parameters, and a list of polymorphic context names that were
    /// desugared to type parameters.
    fn split_desugared_ctx_tparams<'t, 'a, T>(
        tparams: &'t [TparamView<'a, T>],
    ) -> (Vec<String>, Vec<&'t TparamView<'a, T>>) {
        split_desugared_ctx_tparams_gen(tparams.iter().collect(), |tp| tp.name.to_string())
    }

    fn where_constraint<T>(
        fuel: &mut Fuel,
        ty: TyPrinter<'_, T>,
        (left_ty, kind, right_ty): &(&T, ConstraintKind, &T),
    ) -> Doc {
        let left_ty_doc = ty(fuel, left_ty);
        let kind_doc = match kind {
            ConstraintKind::ConstraintAs => text("as"),
            ConstraintKind::ConstraintEq => text("="),
            ConstraintKind::ConstraintSuper => text("super"),
        };
        let right_ty_doc = ty(fuel, right_ty);
        Doc::Concat(vec![
            left_ty_doc,
            Doc::Space,
            kind_doc,
            Doc::Space,
            right_ty_doc,
        ])
    }

    pub(super) fn is_supportdyn_mixed_decl<E: PrintEnv + ?Sized>(env: Penv<'_, E>, t: &DeclTy) -> bool {
        match t.get_node() {
            decl::Ty_::Tapply((_, n), tyl)
                if tyl.len() == 1
                    && n == sn::classes::SUPPORT_DYN
                    && !show_supportdyn_penv(env) =>
            {
                is_supportdyn_mixed_decl(env, &tyl[0])
            }
            decl::Ty_::Toption(t) => matches!(t.get_node(), decl::Ty_::Tnonnull),
            decl::Ty_::Tmixed => true,
            _ => false,
        }
    }

    pub(super) fn is_supportdyn_mixed_locl<E: PrintEnv + ?Sized>(env: Penv<'_, E>, t: &Ty) -> bool {
        match t.get_node() {
            Ty_::Tnewtype(n, tyl, _)
                if tyl.len() == 1
                    && n == sn::classes::SUPPORT_DYN
                    && !show_supportdyn_penv(env) =>
            {
                is_supportdyn_mixed_locl(env, &tyl[0])
            }
            Ty_::Toption(t) => matches!(t.get_node(), Ty_::Tnonnull),
            _ => false,
        }
    }

    /// The docs `(return_disposable_doc, async_doc, tparams_doc)`.
    pub(super) fn fun_type<T>(
        fuel: &mut Fuel,
        ty: TyPrinter<'_, T>,
        is_supportdyn_mixed: &dyn Fn(&T) -> bool,
        verbose: bool,
        ft: &FunTypeView<'_, T>,
        fun_implicit_params: &dyn Fn(&mut Fuel, &[TparamView<'_, T>], &CapabilityView<'_, T>) -> Doc,
    ) -> (Doc, Doc, Doc) {
        let return_disposable_doc = if verbose && ft.flags.return_disposable() {
            Doc::Concat(vec![text("<<__ReturnDisposable>>"), Doc::Space])
        } else {
            Doc::Nothing
        };
        let async_doc = if verbose && ft.flags.is_async() {
            Doc::Concat(vec![text("async"), Doc::Space])
        } else {
            Doc::Nothing
        };
        let params: Vec<Doc> = {
            let param_count = ft.params.len() as isize;
            let variadic_idx = if ft.flags.variadic() {
                Some(param_count - if ft.flags.named_variadic() { 2 } else { 1 })
            } else {
                None
            };
            let named_variadic_idx = if ft.flags.named_variadic() {
                Some(param_count - 1)
            } else {
                None
            };
            ft.params
                .iter()
                .enumerate()
                .map(|(i, p)| {
                    let d = fun_param(fuel, ty, verbose, p);
                    let is_variadic = variadic_idx == Some(i as isize);
                    let is_named_variadic = named_variadic_idx == Some(i as isize);
                    if is_variadic || is_named_variadic {
                        Doc::Concat(vec![d, text("...")])
                    } else {
                        d
                    }
                })
                .collect()
        };

        let tparams_doc = {
            let (_, tparams) = split_desugared_ctx_tparams(&ft.tparams);
            if tparams.is_empty() {
                Doc::Nothing
            } else {
                list(
                    fuel,
                    "<",
                    |fuel, tp| tparam(fuel, ty, is_supportdyn_mixed, tp),
                    tparams,
                    ">",
                )
            }
        };
        let return_doc = ty(fuel, ft.ret);
        let capabilities_doc = fun_implicit_params(fuel, &ft.tparams, &ft.capability);
        let params_doc = list(fuel, "(", id, params, ")");
        let where_doc = if verbose {
            if ft.where_constraints.is_empty() {
                Doc::Nothing
            } else {
                let where_doc = list_sep(
                    fuel,
                    comma_sep(),
                    |fuel, w| where_constraint(fuel, ty, w),
                    ft.where_constraints.iter().collect(),
                );
                Doc::Concat(vec![Doc::Space, text("where"), Doc::Space, where_doc])
            }
        } else {
            Doc::Nothing
        };
        let tparams_doc = Doc::Span(vec![
            tparams_doc,
            params_doc,
            capabilities_doc,
            Doc::Space,
            if ft.flags.returns_readonly() {
                cat(text("readonly"), Doc::Space)
            } else {
                Doc::Nothing
            },
            return_doc,
            where_doc,
        ]);
        (return_disposable_doc, async_doc, tparams_doc)
    }

    fn fun_param<T>(
        fuel: &mut Fuel,
        ty: TyPrinter<'_, T>,
        verbose: bool,
        p: &FunParamView<'_, T>,
    ) -> Doc {
        let flags = p.flags;
        // (The type is printed once here and, unless the parameter is the
        // synthetic "..." or has no type, a second time below: the fuel is
        // consumed twice, as in OCaml.)
        let d = ty(fuel, p.type_);
        let d = match (p.name, &d) {
            // "..." is a synthetic name for a named-variadic parameter
            // We do not render it.
            // [fun_type] adds the ellipses when
            // when [get_ft_named_variadic ft] is `true`.
            (Some("..."), _) => d,
            (None, _) => ty(fuel, p.type_),
            // Handle the case of missing a type by not printing it
            (Some(param_name), Doc::Text(t)) if t == "_" => text(param_name),
            (Some(param_name), _) => {
                let d = ty(fuel, p.type_);
                Doc::Concat(vec![d, Doc::Space, text(param_name)])
            }
        };
        let flag = |b: bool, s: &str| {
            if b {
                cat(text(s), Doc::Space)
            } else {
                Doc::Nothing
            }
        };
        Doc::Concat(vec![
            flag(
                verbose && flags.accepts_disposable(),
                "<<__AcceptDisposable>>",
            ),
            flag(flags.is_optional(), "optional"),
            flag(flags.is_inout(), "inout"),
            flag(flags.is_named(), "named"),
            flag(flags.is_readonly(), "readonly"),
            if flags.is_splat() {
                text("...")
            } else {
                Doc::Nothing
            },
            d,
        ])
    }

    fn tparam<T>(
        fuel: &mut Fuel,
        ty: TyPrinter<'_, T>,
        is_supportdyn_mixed: &dyn Fn(&T) -> bool,
        tp: &TparamView<'_, T>,
    ) -> Doc {
        let cstrl: Vec<&(ConstraintKind, &T)> = tp
            .constraints
            .iter()
            .filter(|(ck, cty)| {
                !(matches!(ck, ConstraintKind::ConstraintAs) && is_supportdyn_mixed(cty))
            })
            .collect();
        let tparam_constraints_doc = list_sep_split(
            fuel,
            false,
            Doc::Space,
            |fuel, (ck, cty)| tparam_constraint(fuel, ty, *ck, cty),
            cstrl,
        );
        Doc::Concat(vec![
            match tp.reified {
                ReifyKind::Erased => Doc::Nothing,
                ReifyKind::SoftReified => cat(text("<<__Soft>> reify"), Doc::Space),
                ReifyKind::Reified => cat(text("reify"), Doc::Space),
            },
            text(tp.name),
            tparam_constraints_doc,
        ])
    }

    fn tparam_constraint<T>(
        fuel: &mut Fuel,
        ty: TyPrinter<'_, T>,
        ck: ConstraintKind,
        cty: &T,
    ) -> Doc {
        let constraint_ty_doc = ty(fuel, cty);
        Doc::Concat(vec![
            Doc::Space,
            text(match ck {
                ConstraintKind::ConstraintAs => "as",
                ConstraintKind::ConstraintSuper => "super",
                ConstraintKind::ConstraintEq => "=",
            }),
            Doc::Space,
            constraint_ty_doc,
        ])
    }

    fn tprim(x: &Tprim) -> Doc {
        // Aast_defs.string_of_tprim
        text(match x {
            Tprim::Tnull => "null",
            Tprim::Tvoid => "void",
            Tprim::Tint => "int",
            Tprim::Tnum => "num",
            Tprim::Tfloat => "float",
            Tprim::Tarraykey => "arraykey",
            Tprim::Tresource => "resource",
            Tprim::Tnoreturn => "noreturn",
            Tprim::Tbool => "bool",
        })
    }

    fn tfun<T>(
        fuel: &mut Fuel,
        ty: TyPrinter<'_, T>,
        is_supportdyn_mixed: &dyn Fn(&T) -> bool,
        verbose: bool,
        ft: &FunTypeView<'_, T>,
        fun_implicit_params: &dyn Fn(&mut Fuel, &[TparamView<'_, T>], &CapabilityView<'_, T>) -> Doc,
    ) -> Doc {
        let (return_disposable_doc, async_doc, fun_type_doc) = fun_type(
            fuel,
            ty,
            is_supportdyn_mixed,
            verbose,
            ft,
            fun_implicit_params,
        );
        Doc::Concat(vec![
            return_disposable_doc,
            text("("),
            async_doc,
            if ft.flags.readonly_this() {
                text("readonly ")
            } else {
                Doc::Nothing
            },
            text("function"),
            fun_type_doc,
            text(")"),
        ])
    }

    fn ttuple<T>(
        fuel: &mut Fuel,
        k: TyPrinter<'_, T>,
        is_nothing: &dyn Fn(&T) -> bool,
        t_required: &[T],
        t_optional: &[T],
        t_extra: TupleExtraView<'_, T>,
    ) -> Doc {
        let tuple_elem =
            |fuel: &mut Fuel, (is_optional, is_variadic, is_splat, ty): (bool, bool, bool, &T)| {
                let doc = k(fuel, ty);
                if is_optional {
                    Doc::Concat(vec![text("optional "), doc])
                } else if is_variadic {
                    Doc::Concat(vec![doc, text("...")])
                } else if is_splat {
                    Doc::Concat(vec![text("..."), doc])
                } else {
                    doc
                }
            };
        let optional_list = t_optional.iter().map(|ty| (true, false, false, ty));
        let extra = match t_extra {
            TupleExtraView::Tsplat(t_splat) => vec![(false, false, true, t_splat)],
            TupleExtraView::Tvariadic(t_variadic) => {
                if is_nothing(t_variadic) {
                    vec![]
                } else {
                    vec![(false, true, false, t_variadic)]
                }
            }
        };
        let required = t_required.iter().map(|ty| (false, false, false, ty));
        list(
            fuel,
            "(",
            tuple_elem,
            required.chain(optional_list).chain(extra).collect(),
            ")",
        )
    }

    fn tshape<T>(
        fuel: &mut Fuel,
        k: TyPrinter<'_, T>,
        to_doc: ToDoc<'_>,
        is_nothing: &dyn Fn(&T) -> bool,
        shape_kind: &T,
        fdm: Vec<ShapeFieldView<'_, T>>,
        open_mixed: bool,
    ) -> Doc {
        let is_closed = is_nothing(shape_kind);
        let mut fields_doc = {
            let f_field = |field: ShapeFieldView<'_, T>, fuel: &mut Fuel| {
                let ShapeFieldView {
                    name: shape_map_key,
                    optional: sft_optional,
                    ty: sft_ty,
                } = field;
                let is_nothing = is_nothing(sft_ty);
                let key_delim = || match &shape_map_key.0 {
                    TshapeFieldName::TSFlitStr(_) => text("'"),
                    _ => Doc::Nothing,
                };
                if sft_optional && is_nothing {
                    if is_closed {
                        None
                    } else {
                        Some(Doc::Concat(vec![
                            text("absent "),
                            key_delim(),
                            to_doc(&tshape_field_name(&shape_map_key.0)),
                            key_delim(),
                        ]))
                    }
                } else {
                    let sft_ty_doc = k(fuel, sft_ty);
                    Some(Doc::Concat(vec![
                        if sft_optional {
                            text("?")
                        } else {
                            Doc::Nothing
                        },
                        key_delim(),
                        to_doc(&tshape_field_name(&shape_map_key.0)),
                        key_delim(),
                        Doc::Space,
                        text("=>"),
                        Doc::Space,
                        sft_ty_doc,
                    ]))
                }
            };
            shape_filter_map(fuel, fdm, f_field)
        };
        if is_closed {
        } else if open_mixed {
            fields_doc.push(text("..."));
        } else {
            let ty_doc = k(fuel, shape_kind);
            fields_doc.push(Doc::Concat(vec![ty_doc, text("...")]));
        }
        list(fuel, "shape(", id, fields_doc, ")")
    }

    fn refinement<T>(
        fuel: &mut Fuel,
        k: TyPrinter<'_, T>,
        cr_consts: Vec<RefinedConstView<'_, T>>,
    ) -> Doc {
        let f_rc = |fuel: &mut Fuel, rc: RefinedConstView<'_, T>| {
            let rc_doc = match rc.bound {
                RefinedConstBoundView::TRexact(ty) => {
                    let ty_doc = k(fuel, ty);
                    Doc::Concat(vec![text("= "), ty_doc])
                }
                RefinedConstBoundView::TRloose {
                    lower: ls,
                    upper: us,
                } => {
                    // Each bound is put in front of the ones printed before it.
                    let mut docs = vec![];
                    for ty in ls {
                        let ty_doc = k(fuel, ty);
                        docs.push(cat(text("super "), ty_doc));
                    }
                    for ty in us {
                        let ty_doc = k(fuel, ty);
                        docs.push(cat(text("as "), ty_doc));
                    }
                    docs.reverse();
                    list_sep(fuel, Doc::Space, id, docs)
                }
            };
            cat(
                text(format!(
                    "{} {} ",
                    refined_const_kind_str(rc.is_ctx),
                    rc.name
                )),
                rc_doc,
            )
        };
        delimited_list(fuel, semi_sep(), false, "{ ", f_rc, cr_consts, " }")
    }

    fn refinements(fuel: &mut Fuel, k: TyPrinter<'_, Ty>, e: &Exact) -> Doc {
        match e {
            Exact::Exact => Doc::Nothing,
            Exact::Nonexact(r) => {
                // Class_refinement.is_empty
                if r.cr_consts.is_empty() {
                    Doc::Nothing
                } else {
                    let r_doc = refinement(fuel, k, locl_views::refinement(r));
                    Doc::Concat(vec![Doc::Space, text("with"), Doc::Space, r_doc])
                }
            }
        }
    }

    fn thas_member(fuel: &mut Fuel, k: TyPrinter<'_, Ty>, hm: &locl::HasMember) -> Doc {
        let name = &hm.name.1;
        // TODO: T71614503 print explicit type arguments appropriately
        let printed_explicit_targs = match hm.method {
            None => text("None"),
            Some(_) => text("Some <targs>"),
        };
        let hm_ty_doc = k(fuel, &hm.type_);
        Doc::Concat(vec![
            text("has_member"),
            text("("),
            text(name.as_str()),
            comma_sep(),
            hm_ty_doc,
            comma_sep(),
            printed_explicit_targs,
            text(")"),
        ])
    }

    fn tcan_index(fuel: &mut Fuel, k: TyPrinter<'_, Ty>, ci: &locl::CanIndex) -> Doc {
        let key_doc = k(fuel, &ci.key);
        let val_doc = k(fuel, &ci.val);
        Doc::Concat(vec![
            text("can_index"),
            text("("),
            key_doc,
            comma_sep(),
            val_doc,
            text(")"),
        ])
    }

    fn tcan_index_assign(fuel: &mut Fuel, k: TyPrinter<'_, Ty>, cia: &locl::CanIndexAssign) -> Doc {
        let key_doc = k(fuel, &cia.key);
        let write_doc = k(fuel, &cia.write);
        let val_doc = k(fuel, &cia.val);
        Doc::Concat(vec![
            text("can_index_assign"),
            text("("),
            key_doc,
            comma_sep(),
            write_doc,
            comma_sep(),
            val_doc,
            text(")"),
        ])
    }

    fn tcan_traverse(fuel: &mut Fuel, k: TyPrinter<'_, Ty>, ct: &locl::CanTraverse) -> Doc {
        match &ct.key {
            None => {
                let val_doc = k(fuel, &ct.val);
                Doc::Concat(vec![
                    text("can_traverse"),
                    text("("),
                    val_doc,
                    comma_sep(),
                    text("is_await:"),
                    text(ct.is_await.to_string()),
                    text(")"),
                ])
            }
            Some(ct_key) => {
                let key_doc = k(fuel, ct_key);
                let val_doc = k(fuel, &ct.val);
                Doc::Concat(vec![
                    text("can_traverse"),
                    text("("),
                    key_doc,
                    comma_sep(),
                    val_doc,
                    comma_sep(),
                    text("is_await:"),
                    text(ct.is_await.to_string()),
                    text(")"),
                ])
            }
        }
    }

    fn thas_type_member(fuel: &mut Fuel, k: TyPrinter<'_, Ty>, htm: &locl::HasTypeMember) -> Doc {
        let subtype = || Doc::Concat(vec![Doc::Space, text("<:"), Doc::Space]);
        let lo_doc = k(fuel, &htm.lower);
        let up_doc = k(fuel, &htm.upper);
        Doc::Concat(vec![
            text("has_type_member("),
            lo_doc,
            subtype(),
            text(htm.id.as_str()),
            subtype(),
            up_doc,
            text(")"),
        ])
    }

    fn tdestructure(fuel: &mut Fuel, k: TyPrinter<'_, Ty>, d: &locl::Destructure) -> Doc {
        let mut docs: Vec<Doc> = d.required.iter().map(|ty| k(fuel, ty)).collect();
        for v in &d.optional {
            let ty_doc = k(fuel, v);
            docs.push(Doc::Concat(vec![text("=_"), ty_doc]));
        }
        if let Some(v) = &d.variadic {
            let ty_doc = k(fuel, v);
            docs.push(Doc::Concat(vec![text("..."), ty_doc]));
        }
        let prefix = match d.kind {
            locl::DestructureKind::ListDestructure => text("list"),
            locl::DestructureKind::SplatUnpack => text("splat"),
        };
        let doc = list(fuel, "(", id, docs, ")");
        Doc::Concat(vec![prefix, doc])
    }

    fn is_open_mixed_decl<E: PrintEnv + ?Sized>(penv: Penv<'_, E>, t: &DeclTy) -> bool {
        match t.get_node() {
            decl::Ty_::Tapply((_, n), tyl)
                if tyl.len() == 1
                    && n == sn::classes::SUPPORT_DYN
                    && !show_supportdyn_penv(penv) =>
            {
                is_open_mixed_decl(penv, &tyl[0])
            }
            decl::Ty_::Toption(t) => matches!(t.get_node(), decl::Ty_::Tnonnull),
            _ => false,
        }
    }

    /// The end of `fun_implicit_params`, once the capability has been printed
    /// ([capabilities]).
    fn fun_implicit_params<T>(capabilities: Option<Vec<Doc>>, tparams: &[TparamView<'_, T>]) -> Doc {
        let (ctx_names, _) = split_desugared_ctx_tparams(tparams);
        let ctx_names: Vec<Doc> = ctx_names.into_iter().map(text).collect();
        match (capabilities, ctx_names.is_empty()) {
            (None, true) => text(":"),
            (None, false) => Doc::Concat(vec![text("["), Doc::Concat(ctx_names), text("]:")]),
            (Some(mut capabilities), _) => {
                capabilities.extend(ctx_names);
                Doc::Concat(vec![text("["), Doc::Concat(capabilities), text("]:")])
            }
        }
    }

    /// `SN.Capabilities`: the capabilities of
    /// `Typing_make_type.default_capability`, in its order.
    const DEFAULT_CAPABILITIES: [&str; 6] = [
        "\\HH\\Capabilities\\WriteProperty",
        "\\HH\\Capabilities\\AccessGlobals",
        "\\HH\\Capabilities\\RxLocal",
        "\\HH\\Capabilities\\SystemLocal",
        "\\HH\\Capabilities\\ImplicitPolicyLocal",
        "\\HH\\Capabilities\\IO",
    ];

    /// `ty_equal ~normalize_lists:true t (Typing_make_type.default_capability_decl
    /// Pos_or_decl.none)`: the default capability is the intersection of the
    /// classes above, without type arguments, and the comparison sorts the
    /// members of an intersection.
    fn is_default_capability_decl(t: &DeclTy) -> bool {
        match t.get_node() {
            decl::Ty_::Tintersection(tyl) => {
                let mut names = vec![];
                for ty in tyl {
                    match ty.get_node() {
                        decl::Ty_::Tapply((_, name), targs) if targs.is_empty() => {
                            names.push(name.as_str())
                        }
                        _ => return false,
                    }
                }
                names.sort();
                let mut default = DEFAULT_CAPABILITIES.to_vec();
                default.sort();
                names == default
            }
            _ => false,
        }
    }

    /// `Typing_make_type.default_capability Pos_or_decl.none`
    fn default_capability(p: PosOrDecl) -> Ty {
        let r = reason::default_capability(p);
        mk(
            r.clone(),
            Ty_::Tintersection(
                DEFAULT_CAPABILITIES
                    .iter()
                    .map(|name| {
                        // class_type r name []
                        mk(
                            r.clone(),
                            Ty_::Tclass(
                                (reason::to_pos(&r), name.to_string()),
                                locl::nonexact(),
                                vec![],
                            ),
                        )
                    })
                    .collect(),
            ),
        )
    }

    /// Prints a decl_ty. If there isn't enough fuel, the type is omitted. Each
    /// recursive call to print a type depletes the fuel by one.
    pub(super) fn decl_ty<E: PrintEnv + ?Sized>(
        fuel: &mut Fuel,
        to_doc: ToDoc<'_>,
        st: &TvidSet,
        penv: Penv<'_, E>,
        verbose_fun: bool,
        omit_likes: bool,
        x: &DeclTy,
    ) -> Doc {
        fuel.provide(|fuel| {
            decl_ty_(
                fuel,
                to_doc,
                st,
                penv,
                verbose_fun,
                omit_likes,
                x.get_node(),
            )
        })
    }

    fn decl_ty_<E: PrintEnv + ?Sized>(
        fuel: &mut Fuel,
        to_doc: ToDoc<'_>,
        st: &TvidSet,
        penv: Penv<'_, E>,
        verbose_fun: bool,
        omit_likes: bool,
        x: &decl::Ty_,
    ) -> Doc {
        use decl::Ty_::*;
        let ty = |fuel: &mut Fuel, x: &DeclTy| {
            decl_ty(fuel, to_doc, st, penv, verbose_fun, omit_likes, x)
        };
        let k: TyPrinter<'_, DeclTy> = &ty;
        let is_nothing = |t: &DeclTy| matches!(t.get_node(), Tunion(tyl) if tyl.is_empty());
        match x {
            Tany(_) => text("_"),
            Tthis => text(sn::typehints::THIS),
            Tmixed => text("mixed"),
            Twildcard => text("_"),
            Tdynamic(_) => text("dynamic"),
            Tnonnull => text("nonnull"),
            TvecOrDict(x, y) => list(fuel, "vec_or_dict<", |fuel, t| k(fuel, t), vec![x, y], ">"),
            Tapply((_, s), tyl) if tyl.is_empty() => {
                if s == sn::typehints::HH_STRING {
                    to_doc(reason::strip_ns(s))
                } else {
                    to_doc(s)
                }
            }
            Tgeneric(s) => to_doc(s),
            Taccess(decl::TaccessType(root_ty, id)) => {
                let root_ty_doc = k(fuel, root_ty);
                Doc::Concat(vec![root_ty_doc, text("::"), to_doc(&id.1)])
            }
            Trefinement(root_ty, r) => {
                let root_ty_doc = k(fuel, root_ty);
                let rs_doc = refinement(fuel, k, decl_views::refinement(r));
                cat(cat(root_ty_doc, text(" with ")), rs_doc)
            }
            Toption(x) => {
                let ty_doc = k(fuel, x);
                Doc::Concat(vec![text("?"), ty_doc])
            }
            Tlike(x) => {
                let ty_doc = k(fuel, x);
                if omit_likes {
                    ty_doc
                } else {
                    Doc::Concat(vec![text("~"), ty_doc])
                }
            }
            Tprim(x) => tprim(x),
            Tfun(ft) => tfun(
                fuel,
                k,
                &|t| is_supportdyn_mixed_decl(penv, t),
                verbose_fun,
                &decl_views::fun_type(ft),
                &|fuel, tparams, capability| {
                    fun_decl_implicit_params(fuel, k, tparams, capability)
                },
            ),
            Tapply((_, n), tyl)
                if tyl.len() == 1
                    && n == sn::classes::SUPPORT_DYN
                    && !show_supportdyn_penv(penv) =>
            {
                k(fuel, &tyl[0])
            }
            // Don't strip_ns here! We want the FULL type, including the initial slash.
            Tapply((_, s), tyl) => {
                let tys_doc = list(fuel, "<", |fuel, t| k(fuel, t), tyl.iter().collect(), ">");
                cat(to_doc(s), tys_doc)
            }
            Ttuple(t) => ttuple(
                fuel,
                k,
                &is_nothing,
                &t.required,
                &t.optional,
                decl_views::tuple_extra(&t.extra),
            ),
            Tunion(tyl) if tyl.is_empty() => text("nothing"),
            Tunion(tyl) => {
                // Typing_make_type.nothing Reason.none
                let nothing = decl::Ty(oxidized::typing_reason::T_::NoReason, Box::new(Tunion(vec![])));
                let tys_doc = ttuple(
                    fuel,
                    k,
                    &is_nothing,
                    tyl,
                    &[],
                    TupleExtraView::Tvariadic(&nothing),
                );
                Doc::Concat(vec![text("|"), tys_doc])
            }
            Tintersection(tyl) if tyl.is_empty() => text("mixed"),
            Tintersection(tyl) => delimited_list(
                fuel,
                cat(cat(Doc::Space, text("&")), Doc::Space),
                true,
                "(",
                |fuel, t| k(fuel, t),
                tyl.iter().collect(),
                ")",
            ),
            Tshape(decl::ShapeType::ShapeSimple(s)) => tshape(
                fuel,
                k,
                to_doc,
                &is_nothing,
                &s.unknown_value,
                decl_views::shape_fields(&s.fields),
                is_open_mixed_decl(penv, &s.unknown_value),
            ),
            Tshape(decl::ShapeType::ShapeSplat(decl::ShapeTypeSplat { ss_elems })) => {
                let elems_docs: Vec<Doc> = ss_elems
                    .iter()
                    .map(|ty| {
                        let doc = k(fuel, ty);
                        cat(text("..."), doc)
                    })
                    .collect();
                Doc::Concat(vec![
                    text("shape("),
                    Doc::Concat(intersperse(elems_docs, || text(", "))),
                    text(")"),
                ])
            }
            TclassPtr(x) => {
                let ty_doc = k(fuel, x);
                Doc::Concat(vec![text("class<"), ty_doc, text(">")])
            }
        }
    }

    /// `List.intersperse`
    fn intersperse(docs: Vec<Doc>, sep: impl Fn() -> Doc) -> Vec<Doc> {
        let mut res = Vec::with_capacity(docs.len() * 2);
        for (i, doc) in docs.into_iter().enumerate() {
            if i > 0 {
                res.push(sep());
            }
            res.push(doc);
        }
        res
    }

    pub(super) fn fun_decl_implicit_params(
        fuel: &mut Fuel,
        ty: TyPrinter<'_, DeclTy>,
        tparams: &[TparamView<'_, DeclTy>],
        capability: &CapabilityView<'_, DeclTy>,
    ) -> Doc {
        let capabilities = match capability {
            CapabilityView::CapDefaults => None,
            CapabilityView::CapTy(t) => {
                if is_default_capability_decl(t) {
                    None
                } else {
                    match t.get_node() {
                        decl::Ty_::Tintersection(tyl) if tyl.is_empty() => Some(vec![]),
                        decl::Ty_::Toption(t) => match t.get_node() {
                            decl::Ty_::Tnonnull => Some(vec![]),
                            // (What is printed is the type under the option.)
                            _ => Some(vec![ty(fuel, t)]),
                        },
                        _ => Some(vec![ty(fuel, t)]),
                    }
                }
            }
        };
        fun_implicit_params(capabilities, tparams)
    }

    /// For a given type parameter, construct a list of its constraints
    fn get_constraints_on_tparam<E: PrintEnv + ?Sized>(
        penv: &E,
        tparam: &str,
    ) -> Vec<(String, ConstraintKind, Ty)> {
        let lower = penv.get_lower_bounds(tparam);
        let upper = penv.get_upper_bounds(tparam);
        // Typing_env_types.get_equal_bounds: `TySet.inter lower upper`, which
        // keeps the elements of `lower`.
        let equ: Vec<&Ty> = lower.iter().filter(|ty| upper.contains(ty)).collect();
        let upper: Vec<&Ty> = if show_supportdyn(penv) {
            upper.iter().collect()
        } else {
            // Don't show "as mixed" if we're not printing supportdyn
            let mixed = || {
                mk(
                    reason::none(),
                    Ty_::Toption(mk(reason::none(), Ty_::Tnonnull)),
                )
            };
            // Typing_make_type.(supportdyn Reason.none (mixed Reason.none))
            let supportdyn_mixed = mk(
                reason::none(),
                Ty_::Tnewtype(sn::classes::SUPPORT_DYN.to_string(), vec![mixed()], mixed()),
            );
            upper.iter().filter(|ty| **ty != supportdyn_mixed).collect()
        };
        // If we have an equality we can ignore the other bounds
        if !equ.is_empty() {
            equ.into_iter()
                .map(|ty| (tparam.to_string(), ConstraintKind::ConstraintEq, ty.clone()))
                .collect()
        } else {
            lower
                .iter()
                .map(|ty| {
                    (
                        tparam.to_string(),
                        ConstraintKind::ConstraintSuper,
                        ty.clone(),
                    )
                })
                .chain(
                    upper
                        .into_iter()
                        .map(|ty| (tparam.to_string(), ConstraintKind::ConstraintAs, ty.clone())),
                )
                .collect()
        }
    }

    fn is_open_mixed<E: PrintEnv + ?Sized>(env: &E, t: &Ty) -> bool {
        match t.get_node() {
            Ty_::Tnewtype(n, _, ty) if n == sn::classes::SUPPORT_DYN && !show_supportdyn(env) => {
                is_open_mixed(env, ty)
            }
            Ty_::Toption(t) => {
                let t = env.expand_type(t);
                matches!(t.get_node(), Ty_::Tnonnull)
            }
            _ => false,
        }
    }

    /// Prints a locl_ty. If there isn't enough fuel, the type is omitted. Each
    /// recursive call to print a type depletes the fuel by one.
    pub(super) fn locl_ty<E: PrintEnv + ?Sized>(
        fuel: &mut Fuel,
        hide_internals: bool,
        to_doc: ToDoc<'_>,
        st: &TvidSet,
        penv: Penv<'_, E>,
        ty: &Ty,
    ) -> Doc {
        fuel.provide(|fuel| locl_ty_(fuel, hide_internals, to_doc, st, penv, ty.get_node()))
    }

    fn locl_ty_<E: PrintEnv + ?Sized>(
        fuel: &mut Fuel,
        hide_internals: bool,
        to_doc: ToDoc<'_>,
        st: &TvidSet,
        penv: Penv<'_, E>,
        x: &Ty_,
    ) -> Doc {
        use Ty_::*;
        let verbose = show_verbose(penv);
        let env = match penv {
            Penv::Declenv => panic!("must provide a locl-env here"),
            Penv::Loclenv(env) => env,
        };
        let ty = |fuel: &mut Fuel, x: &Ty| {
            locl_ty(fuel, hide_internals, to_doc, st, Penv::Loclenv(env), x)
        };
        let k: TyPrinter<'_, Ty> = &ty;
        let union_sep = || cat(cat(Doc::Space, text("|")), Doc::Space);
        match x {
            Tany(_) => text("_"),
            Tdynamic(_) => text("dynamic"),
            Tnonnull => text("nonnull"),
            TvecOrDict(x, y) => list(fuel, "vec_or_dict<", |fuel, t| k(fuel, t), vec![x, y], ">"),
            Toption(ty) => {
                let ty = env.expand_type(ty);
                match ty.get_node() {
                    Tnonnull => text("mixed"),
                    Tunion(tyl) if tyl.iter().any(is_dynamic) => {
                        // Unions with null become Toption, which leads to the awkward ?~...
                        // The Tunion case can better handle this
                        let r = ty.get_reason();
                        let mut tyl2 = vec![mk(r.clone(), Tprim(oxidized::ast_defs::Tprim::Tnull))];
                        tyl2.extend(tyl.iter().cloned());
                        k(fuel, &mk(r.clone(), Tunion(tyl2)))
                    }
                    // Drop the extra option
                    Toption(_) => locl_ty(fuel, hide_internals, to_doc, st, penv, &ty),
                    _ => {
                        let d = k(fuel, &ty);
                        Doc::Concat(vec![text("?"), d])
                    }
                }
            }
            Tprim(x) => tprim(x),
            Tneg(predicate) => {
                type_predicate(fuel, true, hide_internals, to_doc, st, penv, predicate)
            }
            Tvar(n) => {
                let tvar = mk(reason::none(), Tvar(*n));
                let ety = env.expand_type(&tvar);
                match ety.get_node() {
                    // For unsolved type variables, always show the type variable
                    Tvar(n_) => {
                        if st.contains(n_) {
                            text("[rec]")
                        } else if hide_internals {
                            text("_")
                        } else {
                            text(format!("#{}", n_))
                        }
                    }
                    _ => {
                        let prepend = if st.contains(n) {
                            text("[rec]")
                        } else if
                        // For hh_show_env we further show the type variable number
                        show_verbose(penv) {
                            text(format!("#{}", n))
                        } else {
                            Doc::Nothing
                        };
                        let mut st = st.clone();
                        st.insert(*n);
                        let ty_doc = locl_ty(fuel, hide_internals, to_doc, &st, penv, &ety);
                        Doc::Concat(vec![prepend, ty_doc])
                    }
                }
            }
            Tfun(ft) => tfun(
                fuel,
                k,
                &|t| is_supportdyn_mixed_locl(penv, t),
                false,
                &locl_views::fun_type(ft),
                &|fuel, tparams, capability| {
                    fun_locl_implicit_params(fuel, k, tparams, capability)
                },
            ),
            Tclass((_, s), exact, tyl) => {
                let targs_doc = if tyl.is_empty() {
                    Doc::Nothing
                } else {
                    list(fuel, "<", |fuel, t| k(fuel, t), tyl.iter().collect(), ">")
                };
                let with_doc = refinements(fuel, k, exact);
                let class_doc = cat(cat(to_doc(reason::strip_ns(s)), targs_doc), with_doc);
                match exact {
                    Exact::Exact if !hide_internals => {
                        Doc::Concat(vec![text("exact"), Doc::Space, class_doc])
                    }
                    _ => class_doc,
                }
            }
            Tgeneric(s) if is_generated_generic(s) => match s.as_bytes()[2] {
                // has the form T/[...]
                b'[' => to_doc(&s[3..s.len() - 1]),
                // Generic replacement type for parameter used for dependent context
                b'$' => match get_constraints_on_tparam(env, s).as_slice() {
                    [(_, ConstraintKind::ConstraintAs, ty)] => {
                        locl_ty(fuel, hide_internals, to_doc, st, Penv::Loclenv(env), ty)
                    }
                    // this case shouldn't occur
                    _ => to_doc(s),
                },
                _ => to_doc(s),
            },
            Tgeneric(s) => to_doc(s),
            Tnewtype(s, tyl, _) if tyl.is_empty() => to_doc(s),
            Tnewtype(n, tyl, _)
                if tyl.len() == 1
                    && n == sn::classes::SUPPORT_DYN
                    && !show_supportdyn_penv(penv) =>
            {
                k(fuel, &tyl[0])
            }
            Tnewtype(s, tyl, _) => {
                let tys_doc = list(fuel, "<", |fuel, t| k(fuel, t), tyl.iter().collect(), ">");
                cat(to_doc(s), tys_doc)
            }
            Tdependent(dep, cstr) => {
                let cstr_doc = k(fuel, cstr);
                let cstr_info = Doc::Concat(vec![Doc::Space, text("as"), Doc::Space, cstr_doc]);
                Doc::Concat(vec![
                    to_doc(&dependent_kind_to_string(dep)),
                    cstr_info,
                ])
            }
            // Don't strip_ns here! We want the FULL type, including the initial slash.
            Ttuple(t) => ttuple(
                fuel,
                k,
                &is_nothing,
                &t.required,
                &t.optional,
                locl_views::tuple_extra(&t.extra),
            ),
            Tunion(tyl) if tyl.is_empty() => text("nothing"),
            Tunion(tyl) => {
                // `List.fold_right tyl ~init:TySet.empty ~f:TySet.add |>
                // TySet.elements`: sorted, and of the types that compare
                // equal, the last one of the list is the one kept.
                let mut set: BTreeSet<&Ty> = BTreeSet::new();
                for ty in tyl.iter().rev() {
                    set.insert(ty);
                }
                let mut dynamic = vec![];
                let mut null = vec![];
                let mut nonnull = vec![];
                for t in set {
                    match t.get_node() {
                        Tdynamic(_) => dynamic.push(t),
                        Tprim(oxidized::ast_defs::Tprim::Tnull) => null.push(t),
                        _ => nonnull.push(t),
                    }
                }
                let delimited = |fuel: &mut Fuel, nonnull: Vec<&Ty>| {
                    delimited_list(
                        fuel,
                        union_sep(),
                        true,
                        "(",
                        |fuel, t| k(fuel, t),
                        nonnull,
                        ")",
                    )
                };
                match (!dynamic.is_empty(), !null.is_empty(), nonnull.len()) {
                    (false, false, 0) => text("nothing"),
                    // type isn't nullable or dynamic
                    (false, false, 1) => {
                        if verbose {
                            let ty_doc = k(fuel, nonnull[0]);
                            Doc::Concat(vec![text("("), ty_doc, text(")")])
                        } else {
                            k(fuel, nonnull[0])
                        }
                    }
                    (false, false, _) => delimited(fuel, nonnull),
                    // Type only is null
                    (false, true, 0) => {
                        if verbose {
                            text("(null)")
                        } else {
                            text("null")
                        }
                    }
                    // Type only is dynamic
                    (true, false, 0) => {
                        if verbose {
                            text("(dynamic)")
                        } else {
                            text("dynamic")
                        }
                    }
                    // Type is nullable single type
                    (false, true, 1) => {
                        let ty_doc = k(fuel, nonnull[0]);
                        if verbose {
                            Doc::Concat(vec![text("(null |"), ty_doc, text(")")])
                        } else {
                            Doc::Concat(vec![text("?"), ty_doc])
                        }
                    }
                    // Type is like single type
                    (true, false, 1) => {
                        let ty_doc = k(fuel, nonnull[0]);
                        if verbose {
                            Doc::Concat(vec![text("(dynamic |"), ty_doc, text(")")])
                        } else {
                            Doc::Concat(vec![text("~"), ty_doc])
                        }
                    }
                    // Type is like null
                    (true, true, 0) => {
                        if verbose {
                            text("(dynamic | null)")
                        } else {
                            text("~null")
                        }
                    }
                    // Type is like nullable single type
                    (true, true, 1) => {
                        let ty_doc = k(fuel, nonnull[0]);
                        if verbose {
                            Doc::Concat(vec![text("(dynamic | null |"), ty_doc, text(")")])
                        } else {
                            Doc::Concat(vec![text("~?"), ty_doc])
                        }
                    }
                    (true, false, _) => {
                        let tys_doc = delimited(fuel, nonnull);
                        Doc::Concat(vec![text("~"), tys_doc])
                    }
                    (false, true, _) => {
                        let tys_doc = delimited(fuel, nonnull);
                        Doc::Concat(vec![text("?"), tys_doc])
                    }
                    (true, true, _) => {
                        let tys_doc = delimited(fuel, nonnull);
                        Doc::Concat(vec![text("~"), text("?"), tys_doc])
                    }
                }
            }
            Tintersection(tyl) if tyl.is_empty() => text("mixed"),
            Tintersection(tyl) => delimited_list(
                fuel,
                cat(cat(Doc::Space, text("&")), Doc::Space),
                true,
                "(",
                |fuel, t| k(fuel, t),
                tyl.iter().collect(),
                ")",
            ),
            Tshape(locl::ShapeType::ShapeSimple(s)) => tshape(
                fuel,
                k,
                to_doc,
                &is_nothing,
                &s.unknown_value,
                locl_views::shape_fields(&s.fields),
                is_open_mixed(env, &s.unknown_value),
            ),
            Tshape(locl::ShapeType::ShapeSplat(locl::ShapeTypeSplat { ss_elems })) => {
                // A type variable can resolve to another splat after the row was first
                // normalized. The ordinary printer recursion is bottom-up, so its child
                // types have already become documents by the time the parent could merge
                // them. Expand and flatten the types first, for display only.
                fn expand_splat_elem<E: PrintEnv + ?Sized>(
                    env: &E,
                    seen: &TvidSet,
                    ty: &Ty,
                    acc: &mut Vec<Ty>,
                ) {
                    match ty.get_node() {
                        Tvar(v) if !seen.contains(v) => {
                            let ty = env.expand_type(ty).into_owned();
                            let mut seen = seen.clone();
                            seen.insert(*v);
                            expand_splat_elem(env, &seen, &ty, acc)
                        }
                        Tshape(locl::ShapeType::ShapeSplat(locl::ShapeTypeSplat { ss_elems })) => {
                            for ty in ss_elems.iter() {
                                expand_splat_elem(env, seen, ty, acc)
                            }
                        }
                        _ => acc.push(ty.clone()),
                    }
                }
                let expanded: Vec<Ty> = {
                    let mut acc = vec![];
                    for ty in ss_elems.iter() {
                        expand_splat_elem(env, st, ty, &mut acc)
                    }
                    acc
                };
                let all_simple = expanded.iter().all(|ty| {
                    matches!(ty.get_node(), Tshape(locl::ShapeType::ShapeSimple(_)))
                });
                if all_simple {
                    // Expand before checking: a field type may be a solved type variable
                    // that resolves to nothing (e.g. an Opt fresh var from super-right
                    // decomposition). nothing is the union identity, so drop it.
                    let is_nothing = |ty: &Ty| {
                        let ty = env.expand_type(ty);
                        matches!(ty.get_node(), Tunion(tyl) if tyl.is_empty())
                    };
                    let smart_union = |r: reason::T, tys: [&Ty; 2]| {
                        let tys: Vec<&Ty> = tys.into_iter().filter(|ty| !is_nothing(ty)).collect();
                        match tys.as_slice() {
                            [] => mk(r, Tunion(vec![])),
                            [ty] => (*ty).clone(),
                            _ => mk(r, Tunion(tys.into_iter().cloned().collect())),
                        }
                    };
                    let mut acc = locl::ShapeTypeSimple {
                        origin: TypeOrigin::MissingOrigin,
                        unknown_value: mk(reason::none(), Tunion(vec![])),
                        fields: TShapeMap::new(),
                    };
                    for ty in &expanded {
                        if let Tshape(locl::ShapeType::ShapeSimple(right)) = ty.get_node() {
                            let all_keys: BTreeSet<&TShapeField> =
                                acc.fields.keys().chain(right.fields.keys()).collect();
                            let proj = |fields: &TShapeMap<locl::ShapeFieldType>,
                                        unk: &Ty,
                                        key: &TShapeField| {
                                match fields.get(key) {
                                    Some(fd) => fd.clone(),
                                    None => locl::ShapeFieldType {
                                        optional: true,
                                        ty: unk.clone(),
                                    },
                                }
                            };
                            let mut merged_fields = TShapeMap::new();
                            for key in all_keys {
                                let l = proj(&acc.fields, &acc.unknown_value, key);
                                let r = proj(&right.fields, &right.unknown_value, key);
                                let merged_fd = match (l.optional, r.optional) {
                                    (_, false) => locl::ShapeFieldType {
                                        optional: false,
                                        ty: r.ty,
                                    },
                                    (false, true) => locl::ShapeFieldType {
                                        optional: false,
                                        ty: smart_union(reason::none(), [&l.ty, &r.ty]),
                                    },
                                    (true, true) => locl::ShapeFieldType {
                                        optional: true,
                                        ty: smart_union(reason::none(), [&l.ty, &r.ty]),
                                    },
                                };
                                merged_fields.insert(key.clone(), merged_fd);
                            }
                            acc = locl::ShapeTypeSimple {
                                origin: TypeOrigin::MissingOrigin,
                                unknown_value: smart_union(
                                    reason::none(),
                                    [&acc.unknown_value, &right.unknown_value],
                                ),
                                fields: merged_fields,
                            };
                        }
                    }
                    let merged = acc;
                    tshape(
                        fuel,
                        k,
                        to_doc,
                        &is_nothing,
                        &merged.unknown_value,
                        locl_views::shape_fields(&merged.fields),
                        is_open_mixed(env, &merged.unknown_value),
                    )
                } else {
                    let elems_docs: Vec<Doc> = expanded
                        .iter()
                        .map(|ty| {
                            let doc = k(fuel, ty);
                            cat(text("..."), doc)
                        })
                        .collect();
                    Doc::Concat(vec![
                        text("shape("),
                        Doc::Concat(intersperse(elems_docs, || text(", "))),
                        text(")"),
                    ])
                }
            }
            Taccess(locl::TaccessType(root_ty, id)) => {
                let root_ty_doc = k(fuel, root_ty);
                Doc::Concat(vec![root_ty_doc, text("::"), to_doc(&id.1)])
            }
            Tlabel(name) => Doc::Concat(vec![text("#"), text(name.as_str())]),
            TclassPtr(ty) => {
                let ty_doc = k(fuel, ty);
                Doc::Concat(vec![text("class<"), ty_doc, text(">")])
            }
        }
    }

    fn type_predicate<E: PrintEnv + ?Sized>(
        fuel: &mut Fuel,
        negate: bool,
        hide_internals: bool,
        to_doc: ToDoc<'_>,
        st: &TvidSet,
        penv: Penv<'_, E>,
        predicate: &TypePredicate,
    ) -> Doc {
        let k = |fuel: &mut Fuel, lty: &Ty| locl_ty(fuel, hide_internals, to_doc, st, penv, lty);
        let g = |fuel: &mut Fuel, g: &TypeTagGeneric| match g {
            TypeTagGeneric::Wildcard(id) => text(format!(
                "_{}",
                if hide_internals {
                    String::new()
                } else {
                    id.to_string()
                }
            )),
            TypeTagGeneric::Filled(ty) => k(fuel, ty),
        };
        let tag_doc = |fuel: &mut Fuel, tag: &TypeTag| match tag {
            TypeTag::BoolTag => text("bool"),
            TypeTag::IntTag => text("int"),
            TypeTag::ArraykeyTag => text("arraykey"),
            TypeTag::FloatTag => text("float"),
            TypeTag::NumTag => text("num"),
            TypeTag::ResourceTag => text("resource"),
            TypeTag::NullTag => text("null"),
            TypeTag::ClassTag(s, generics) => {
                let targs_doc = if generics.is_empty() {
                    Doc::Nothing
                } else {
                    list(fuel, "<", g, generics.iter().collect(), ">")
                };
                cat(to_doc(s), targs_doc)
            }
            TypeTag::EnumTag(s) => to_doc(s),
            TypeTag::GenericTag { name, from_like: _ } => to_doc(name),
        };
        fn predicate_doc(
            fuel: &mut Fuel,
            tag_doc: &dyn Fn(&mut Fuel, &TypeTag) -> Doc,
            predicate: &TypePredicate,
        ) -> Doc {
            fuel.provide(|fuel| match &predicate.1 {
                TypePredicate_::IsTag(tag) => tag_doc(fuel, tag),
                TypePredicate_::IsTupleOf(locl::TuplePredicate { required }) => {
                    let texts: Vec<Doc> = required
                        .iter()
                        .map(|p| predicate_doc(fuel, tag_doc, p))
                        .collect();
                    let mut docs = vec![text("(")];
                    docs.extend(intersperse(texts, || text(", ")));
                    docs.push(text(")"));
                    Doc::Concat(docs)
                }
                TypePredicate_::IsShapeOf(locl::ShapePredicate {
                    fields,
                    allows_unknown_fields,
                }) => {
                    let mut texts: Vec<Doc> = fields
                        .iter()
                        // `TShapeMap.elements`: the bindings from the last to the first.
                        .rev()
                        .map(|(key, field)| {
                            let key_delim = || match &key.0 {
                                TshapeFieldName::TSFlitStr(_) => text("'"),
                                _ => Doc::Nothing,
                            };
                            let pdoc = predicate_doc(fuel, tag_doc, &field.predicate);
                            Doc::Concat(vec![
                                if field.optional {
                                    text("?")
                                } else {
                                    Doc::Nothing
                                },
                                key_delim(),
                                text_strip_ns(&tshape_field_name(&key.0)),
                                key_delim(),
                                Doc::Space,
                                text("=>"),
                                Doc::Space,
                                pdoc,
                            ])
                        })
                        .collect();
                    if *allows_unknown_fields {
                        texts.push(text("..."));
                    }
                    let mut docs = vec![text("shape(")];
                    docs.extend(intersperse(texts, || text(", ")));
                    docs.push(text(")"));
                    Doc::Concat(docs)
                }
                TypePredicate_::IsUnionOf(predicates) => {
                    let texts: Vec<Doc> = predicates
                        .iter()
                        .map(|p| predicate_doc(fuel, tag_doc, p))
                        .collect();
                    Doc::Concat(intersperse(texts, || {
                        Doc::Concat(vec![Doc::Space, text("|"), Doc::Space])
                    }))
                }
                TypePredicate_::IsNot(inner) => {
                    let inner_doc = predicate_doc(fuel, tag_doc, inner);
                    Doc::Concat(vec![text("not "), inner_doc])
                }
            })
        }
        let pdoc = predicate_doc(fuel, &tag_doc, predicate);
        Doc::Concat(vec![text(if negate { "not " } else { "is " }), pdoc])
    }

    pub(super) fn fun_locl_implicit_params(
        fuel: &mut Fuel,
        ty: TyPrinter<'_, Ty>,
        tparams: &[TparamView<'_, Ty>],
        capability: &CapabilityView<'_, Ty>,
    ) -> Doc {
        let capabilities = match capability {
            CapabilityView::CapDefaults => None,
            CapabilityView::CapTy(t) => {
                if ty_equal_normalize_lists(t, &default_capability(Pos::NONE)) {
                    None
                } else {
                    match t.get_node() {
                        Ty_::Tintersection(tyl) if tyl.is_empty() => Some(vec![]),
                        Ty_::Toption(t) => match t.get_node() {
                            Ty_::Tnonnull => Some(vec![]),
                            // (What is printed is the type under the option.)
                            _ => Some(vec![ty(fuel, t)]),
                        },
                        _ => Some(vec![ty(fuel, t)]),
                    }
                }
            }
        };
        fun_implicit_params(capabilities, tparams)
    }

    fn constraint_type_<E: PrintEnv + ?Sized>(
        fuel: &mut Fuel,
        hide_internals: bool,
        to_doc: ToDoc<'_>,
        st: &TvidSet,
        penv: Penv<'_, E>,
        x: &ConstraintType_,
    ) -> Doc {
        let ty = |fuel: &mut Fuel, lty: &Ty| locl_ty(fuel, hide_internals, to_doc, st, penv, lty);
        let k: TyPrinter<'_, Ty> = &ty;
        match x {
            ConstraintType_::ThasMember(hm) => thas_member(fuel, k, hm),
            ConstraintType_::ThasTypeMember(htm) => thas_type_member(fuel, k, htm),
            ConstraintType_::Tdestructure(d) => tdestructure(fuel, k, d),
            ConstraintType_::TcanIndex(ci) => tcan_index(fuel, k, ci),
            ConstraintType_::TcanIndexAssign(cia) => tcan_index_assign(fuel, k, cia),
            ConstraintType_::TcanTraverse(ct) => tcan_traverse(fuel, k, ct),
            ConstraintType_::TtypeSwitch {
                predicate,
                ty_true,
                ty_false,
            } => {
                let predicate_doc =
                    type_predicate(fuel, false, hide_internals, to_doc, st, penv, predicate);
                let ty_true_doc = k(fuel, ty_true);
                let ty_false_doc = k(fuel, ty_false);
                Doc::Concat(vec![
                    text("("),
                    predicate_doc,
                    text("?"),
                    ty_true_doc,
                    text(":"),
                    ty_false_doc,
                    text(")"),
                ])
            }
            ConstraintType_::ThasConst { name, ty } => {
                let ty_doc = k(fuel, ty);
                Doc::Concat(vec![
                    text("has_const("),
                    text(name.as_str()),
                    text(":"),
                    Doc::Space,
                    ty_doc,
                    text(")"),
                ])
            }
        }
    }

    fn constraint_type<E: PrintEnv + ?Sized>(
        fuel: &mut Fuel,
        hide_internals: bool,
        to_doc: ToDoc<'_>,
        st: &TvidSet,
        penv: Penv<'_, E>,
        ty: &ConstraintType,
    ) -> Doc {
        constraint_type_(fuel, hide_internals, to_doc, st, penv, &ty.1)
    }

    pub(super) fn internal_type<E: PrintEnv + ?Sized>(
        fuel: &mut Fuel,
        hide_internals: bool,
        to_doc: ToDoc<'_>,
        st: &TvidSet,
        penv: Penv<'_, E>,
        ty: &InternalType,
    ) -> Doc {
        match ty {
            InternalType::LoclType(ty) => locl_ty(fuel, hide_internals, to_doc, st, penv, ty),
            InternalType::ConstraintType(ty) => {
                constraint_type(fuel, hide_internals, to_doc, st, penv, ty)
            }
        }
    }

    /// `to_string ~fuel ~ty to_doc env x`, where [ty] has already been given
    /// `to_doc`, the empty set of type variables, `env` and `x`.
    pub(super) fn to_string(fuel: &mut Fuel, ty: impl FnOnce(&mut Fuel, &TvidSet) -> Doc) -> String {
        let doc = ty(fuel, &TvidSet::new());
        doc::strip(&doc::format_doc_unbroken(&doc)).to_string()
    }

    /// `Typing_env_types.get_tparams_in_ty_and_acc env S_set.empty ty`: the
    /// type parameters that occur in a type (`Type_visitor.locl_type_visitor`
    /// with `on_tgeneric` and `on_tvar` overridden).
    fn get_tparams_in_ty_and_acc<E: PrintEnv + ?Sized>(
        env: &E,
        acc: &mut BTreeSet<String>,
        ty: &Ty,
    ) {
        use Ty_::*;
        let mut on_type = |ty: &Ty| get_tparams_in_ty_and_acc(env, acc, ty);
        match ty.get_node() {
            Tany(_) | Tnonnull | Tdynamic(_) | Tprim(_) | Tlabel(_) => {}
            Toption(ty) => on_type(ty),
            Tvar(_) => {
                let ety = env.expand_type(ty);
                match ety.get_node() {
                    Tvar(_) => {}
                    _ => on_type(&ety),
                }
            }
            Tfun(ft) => {
                ft.params.iter().for_each(|p| on_type(&p.type_));
                ft.tparams
                    .iter()
                    .for_each(|t| t.constraints.iter().for_each(|(_, ty)| on_type(ty)));
                on_type(&ft.ret)
            }
            // Not traversing args, although they may contain Tgenerics (higher kinds only)
            Tgeneric(s) => {
                acc.insert(s.clone());
            }
            Tnewtype(_, tyl, ty) => {
                tyl.iter().for_each(&mut on_type);
                on_type(ty)
            }
            Tdependent(_, ty) => on_type(ty),
            Ttuple(t) => {
                match &t.extra {
                    locl::TupleExtra::Tsplat(t) | locl::TupleExtra::Tvariadic(t) => on_type(t),
                }
                t.optional.iter().for_each(&mut on_type);
                t.required.iter().for_each(&mut on_type)
            }
            Tunion(tyl) | Tintersection(tyl) => tyl.iter().for_each(&mut on_type),
            Tshape(locl::ShapeType::ShapeSimple(s)) => {
                on_type(&s.unknown_value);
                s.fields.values().for_each(|sft| on_type(&sft.ty))
            }
            Tshape(locl::ShapeType::ShapeSplat(s)) => s.ss_elems.iter().for_each(&mut on_type),
            Tclass(_, exact, tyl) => {
                match exact {
                    Exact::Exact => {}
                    Exact::Nonexact(cr) => {
                        for rc in cr.cr_consts.values() {
                            match &rc.bound {
                                locl::RefinedConstBound::TRexact(ty) => on_type(ty),
                                locl::RefinedConstBound::TRloose(bounds) => {
                                    bounds.upper.iter().for_each(&mut on_type);
                                    bounds.lower.iter().for_each(&mut on_type)
                                }
                            }
                        }
                    }
                }
                tyl.iter().for_each(&mut on_type)
            }
            TvecOrDict(ty1, ty2) => {
                on_type(ty1);
                on_type(ty2)
            }
            Taccess(locl::TaccessType(ty, _)) => on_type(ty),
            Tneg(neg_ty) => match &neg_ty.1 {
                TypePredicate_::IsTag(TypeTag::ClassTag(_, args)) => {
                    for g in args {
                        match g {
                            TypeTagGeneric::Filled(ty) => on_type(ty),
                            TypeTagGeneric::Wildcard(_) => {}
                        }
                    }
                }
                _ => {}
            },
            TclassPtr(ty) => on_type(ty),
        }
    }

    /// Print a suffix for type parameters in [typ] that have constraints
    /// If the type itself is a type parameter with a single constraint, just
    /// represent this as `as t` or `super t`, otherwise use full `where` syntax
    pub(super) fn constraints_for_type<E: PrintEnv + ?Sized>(
        fuel: &mut Fuel,
        hide_internals: bool,
        to_doc: ToDoc<'_>,
        env: &E,
        typ: &Ty,
    ) -> Doc {
        let mut tparams = BTreeSet::new();
        get_tparams_in_ty_and_acc(env, &mut tparams, typ);
        let constraints: Vec<(String, ConstraintKind, Ty)> = tparams
            .iter()
            .flat_map(|tparam| get_constraints_on_tparam(env, tparam))
            .collect();
        let typ = env.expand_type(typ);
        let penv = Penv::Loclenv(env);
        let st = TvidSet::new();
        let ty = |fuel: &mut Fuel, x: &Ty| locl_ty(fuel, hide_internals, to_doc, &st, penv, x);
        let k: TyPrinter<'_, Ty> = &ty;
        match (typ.get_node(), constraints.as_slice()) {
            (_, []) => Doc::Nothing,
            (Ty_::Tgeneric(tparam), [(tparam_, ck, typ)]) if tparam == tparam_ => {
                tparam_constraint(fuel, k, *ck, typ)
            }
            _ => {
                let to_tparam_constraint_doc =
                    |fuel: &mut Fuel, (tparam, ck, typ): &(String, ConstraintKind, Ty)| {
                        let tparam_constraint_doc = tparam_constraint(fuel, k, *ck, typ);
                        Doc::Concat(vec![text(tparam.as_str()), tparam_constraint_doc])
                    };
                let tparam_constraints_doc = list_sep(
                    fuel,
                    comma_sep(),
                    to_tparam_constraint_doc,
                    constraints.iter().collect(),
                );
                Doc::Concat(vec![
                    Doc::Newline,
                    text("where"),
                    Doc::Space,
                    Doc::WithRuleParental(Box::new(tparam_constraints_doc)),
                ])
            }
        }
    }

    pub(super) fn to_string_rec<E: PrintEnv + ?Sized>(
        fuel: &mut Fuel,
        hide_internals: bool,
        penv: Penv<'_, E>,
        n: Tvid,
        x: &Ty,
    ) -> String {
        let mut st = TvidSet::new();
        st.insert(n);
        let doc = locl_ty(fuel, hide_internals, &text_strip_ns, &st, penv, x);
        doc::strip(&doc::format_doc_unbroken(&doc)).to_string()
    }
}

// ~~ Computes the string representing a type in an error message ~~~~~~~~~~~~

mod error_string {
    use super::*;

    fn tprim(tp: &Tprim) -> &'static str {
        match tp {
            Tprim::Tnull => "null",
            Tprim::Tvoid => "void",
            Tprim::Tint => "an int",
            Tprim::Tbool => "a bool",
            Tprim::Tfloat => "a float",
            Tprim::Tnum => "a num (int | float)",
            Tprim::Tresource => "a resource",
            Tprim::Tarraykey => "an array key (int | string)",
            Tprim::Tnoreturn => "noreturn (throws or exits)",
        }
    }

    fn type_<E: PrintEnv + ?Sized>(
        fuel: &mut Fuel,
        ignore_dynamic: bool,
        env: &E,
        ety: &Ty,
    ) -> String {
        use Ty_::*;
        let ety_to_string = |fuel: &mut Fuel, ety: &Ty| {
            full::to_string(fuel, |fuel, st| {
                full::locl_ty(
                    fuel,
                    true,
                    &full::text_strip_ns,
                    st,
                    Penv::Loclenv(env),
                    ety,
                )
            })
        };
        match ety.get_node() {
            Tany(_) => "an untyped value".to_string(),
            Tdynamic(_) => "a dynamic value".to_string(),
            Tunion(l) if ignore_dynamic => union(
                fuel,
                env,
                l.iter().filter(|x| !is_dynamic(x)).collect(),
            ),
            Tunion(l) => union(fuel, env, l.iter().collect()),
            Tintersection(l) if l.is_empty() => "a mixed value".to_string(),
            Tintersection(l) => intersection(fuel, env, l),
            TvecOrDict(..) => "a vec_or_dict".to_string(),
            Ttuple(locl::TupleType {
                required,
                optional,
                extra: locl::TupleExtra::Tvariadic(t_variadic),
            }) => format!(
                "{}{}",
                if optional.is_empty() && is_nothing(t_variadic) {
                    "a tuple of size "
                } else {
                    "a tuple of size at least "
                },
                required.len()
            ),
            Ttuple(locl::TupleType {
                required,
                optional: _,
                extra: locl::TupleExtra::Tsplat(_),
            }) => format!("a tuple of size at least {}", required.len()),
            Tnonnull => "a nonnull value".to_string(),
            Toption(x) => match x.get_node() {
                Tnonnull => "a mixed value".to_string(),
                _ => "a nullable type".to_string(),
            },
            Tprim(tp) => tprim(tp).to_string(),
            Tvar(_) => "some value".to_string(),
            Tfun(_) => "a function".to_string(),
            Tgeneric(s) if is_generic_dep_ty(s) => {
                let ty_str = ety_to_string(fuel, ety);
                format!("the expression dependent type {}", ty_str)
            }
            Tgeneric(_) => {
                let ty_str = ety_to_string(fuel, ety);
                format!("a value of generic type {}", ty_str)
            }
            Tnewtype(n, tyl, _)
                if tyl.len() == 1 && n == sn::classes::SUPPORT_DYN && !show_supportdyn(env) =>
            {
                type_(fuel, false, env, &tyl[0])
            }
            Tnewtype(x, tyl, _) if tyl.len() == 1 && x == sn::classes::CLASS_NAME => {
                let ty_str = ety_to_string(fuel, &tyl[0]);
                format!("a classname string for {}", ty_str)
            }
            Tnewtype(x, tyl, _) if tyl.len() == 1 && x == sn::classes::CLASS_OR_CLASSNAME => {
                let ty_str = ety_to_string(fuel, &tyl[0]);
                format!("a class or classname for {}", ty_str)
            }
            TclassPtr(ty) => {
                let ty_str = ety_to_string(fuel, ty);
                format!("a class pointer for {}", ty_str)
            }
            Tnewtype(x, tyl, _) if tyl.len() == 1 && x == sn::classes::TYPE_NAME => {
                let ty_str = ety_to_string(fuel, &tyl[0]);
                format!("a typename string for {}", ty_str)
            }
            Tnewtype(..) => {
                let ty_str = ety_to_string(fuel, ety);
                format!("a value of type {}", ty_str)
            }
            Tdependent(dep, _cstr) => dependent(dep),
            Tclass((_, id), _, _) if id == sn::typehints::HH_STRING => "a string".to_string(),
            Tclass(_, e, _) => {
                let ty_str = ety_to_string(fuel, ety);
                let prefix = match e {
                    Exact::Exact => "an object of exactly the class ",
                    Exact::Nonexact(_) => "an object of type ",
                };
                format!("{}{}", prefix, ty_str)
            }
            Tshape(_) => "a shape".to_string(),
            Taccess(_) => "a type constant".to_string(),
            Tlabel(name) => format!("a label (#{})", name),
            Tneg(predicate) => {
                let tag_str = |tag: &TypeTag| match tag {
                    TypeTag::BoolTag => "a bool".to_string(),
                    TypeTag::IntTag => "an int".to_string(),
                    TypeTag::ArraykeyTag => "an arraykey".to_string(),
                    TypeTag::FloatTag => "a float".to_string(),
                    TypeTag::NumTag => "a num".to_string(),
                    TypeTag::ResourceTag => "a resource".to_string(),
                    TypeTag::NullTag => "null".to_string(),
                    TypeTag::ClassTag(s, _) => format!("a {}", reason::strip_ns(s)),
                    TypeTag::EnumTag(s) => format!("a {}", reason::strip_ns(s)),
                    TypeTag::GenericTag { name, from_like: _ } => format!("a {}", name),
                };
                fn pred_str(tag_str: &dyn Fn(&TypeTag) -> String, predicate: &TypePredicate_) -> String {
                    match predicate {
                        TypePredicate_::IsTag(tag) => tag_str(tag),
                        TypePredicate_::IsTupleOf(locl::TuplePredicate { required }) => {
                            let strings: Vec<String> =
                                required.iter().map(|p| pred_str(tag_str, &p.1)).collect();
                            format!("({})", strings.join(", "))
                        }
                        TypePredicate_::IsShapeOf(locl::ShapePredicate {
                            fields,
                            allows_unknown_fields,
                        }) => {
                            let mut texts: Vec<String> = fields
                                .iter()
                                // `TShapeMap.elements`: the bindings from the last to the first.
                                .rev()
                                .map(|(key, field)| {
                                    let key_delim = match &key.0 {
                                        TshapeFieldName::TSFlitStr(_) => "'",
                                        _ => "",
                                    };
                                    [
                                        if field.optional { "?" } else { "" },
                                        key_delim,
                                        &tshape_field_name(&key.0),
                                        key_delim,
                                        " => ",
                                        &pred_str(tag_str, &field.predicate.1),
                                    ]
                                    .concat()
                                })
                                .collect();
                            if *allows_unknown_fields {
                                texts.push("...".to_string());
                            }
                            format!("shape({})", texts.join(", "))
                        }
                        TypePredicate_::IsUnionOf(predicates) => {
                            let strings: Vec<String> =
                                predicates.iter().map(|p| pred_str(tag_str, &p.1)).collect();
                            strings.join(" | ")
                        }
                        TypePredicate_::IsNot(pred) => format!("not {}", pred_str(tag_str, &pred.1)),
                        // TODO: T196048813, dedupe?, fuel?
                    }
                }
                format!("anything but {}", pred_str(&tag_str, &predicate.1))
            }
        }
    }

    fn dependent(dep: &locl::DependentType) -> String {
        let x = dependent_kind_to_string(dep);
        let x = reason::strip_ns(&x);
        match dep {
            locl::DependentType::DTexpr(_) => format!("the expression dependent type {}", x),
        }
    }

    fn union<E: PrintEnv + ?Sized>(fuel: &mut Fuel, env: &E, l: Vec<&Ty>) -> String {
        let (null, nonnull): (Vec<&Ty>, Vec<&Ty>) = l
            .into_iter()
            // equal_locl_ty_ (get_node ty) (Tprim Nast.Tnull)
            .partition(|ty| matches!(ty.get_node(), Ty_::Tprim(Tprim::Tnull)));
        let l: Vec<String> = nonnull
            .into_iter()
            .map(|ty| to_string(fuel, false, env, ty))
            .collect();
        // S_set: sorted, without duplicates.
        let s: BTreeSet<String> = l.into_iter().collect();
        let l: Vec<String> = s.into_iter().collect();
        if null.is_empty() {
            union_(&l)
        } else {
            "a nullable type".to_string()
        }
    }

    fn union_(l: &[String]) -> String {
        match l {
            [] => "an undefined value".to_string(),
            [x] => x.clone(),
            [x, rl @ ..] => format!("{} or {}", x, union_(rl)),
        }
    }

    fn intersection<E: PrintEnv + ?Sized>(fuel: &mut Fuel, env: &E, l: &[Ty]) -> String {
        let l: Vec<String> = l.iter().map(|ty| to_string(fuel, false, env, ty)).collect();
        l.join(" and ")
    }

    pub(super) fn classish_kind(c_kind: &ClassishKind, final_: bool) -> String {
        let fs = if final_ { " final" } else { "" };
        match c_kind {
            ClassishKind::Cclass(k) => match k {
                Abstraction::Abstract => format!("an abstract{} class", fs),
                Abstraction::Concrete => format!("a{} class", fs),
            },
            ClassishKind::Cinterface => "an interface".to_string(),
            ClassishKind::Ctrait => "a trait".to_string(),
            ClassishKind::Cenum => "an enum".to_string(),
            ClassishKind::CenumClass(k) => match k {
                Abstraction::Abstract => "an abstract enum class".to_string(),
                Abstraction::Concrete => "an enum class".to_string(),
            },
        }
    }

    pub(super) fn to_string<E: PrintEnv + ?Sized>(
        fuel: &mut Fuel,
        ignore_dynamic: bool,
        env: &E,
        ty: &Ty,
    ) -> String {
        let ety = env.expand_type(ty);
        type_(fuel, ignore_dynamic, env, &ety)
    }
}

// ~~ Fuel for the printers ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

fn supply_fuel(
    msg: Option<bool>,
    tcopt: &TypecheckerOptions,
    printer: impl FnOnce(&mut Fuel) -> String,
) -> String {
    let msg = msg.unwrap_or(true);
    let type_printer_fuel = tcopt.tco_type_printer_fuel;
    let mut fuel = Fuel::init(type_printer_fuel);
    let str = printer(&mut fuel);
    if fuel.has_enough() || !msg {
        str
    } else {
        format!(
            "{} [This type was truncated. If you need more of the type, use `hh stop; hh --config type_printer_fuel=N`. At this time, N is {}.]",
            str, type_printer_fuel
        )
    }
}

// ~~ User API ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// The description of a type in an error message: "an int", "an object of
/// type C", "a shape"...
pub fn error<E: PrintEnv + ?Sized>(ignore_dynamic: Option<bool>, env: &E, ty: &Ty) -> String {
    let ignore_dynamic = ignore_dynamic.unwrap_or(false);
    supply_fuel(None, env.get_tcopt(), |fuel| {
        error_string::to_string(fuel, ignore_dynamic, env, ty)
    })
}

pub fn full<E: PrintEnv + ?Sized>(hide_internals: bool, env: &E, ty: &Ty) -> String {
    supply_fuel(None, env.get_tcopt(), |fuel| {
        full::to_string(fuel, |fuel, st| {
            full::locl_ty(
                fuel,
                hide_internals,
                &full::doc_text,
                st,
                Penv::Loclenv(env),
                ty,
            )
        })
    })
}

pub fn full_i<E: PrintEnv + ?Sized>(hide_internals: bool, env: &E, ty: &InternalType) -> String {
    supply_fuel(None, env.get_tcopt(), |fuel| {
        full::to_string(fuel, |fuel, st| {
            full::internal_type(
                fuel,
                hide_internals,
                &full::doc_text,
                st,
                Penv::Loclenv(env),
                ty,
            )
        })
    })
}

pub fn full_rec<E: PrintEnv + ?Sized>(hide_internals: bool, env: &E, n: Tvid, ty: &Ty) -> String {
    supply_fuel(None, env.get_tcopt(), |fuel| {
        full::to_string_rec(fuel, hide_internals, Penv::Loclenv(env), n, ty)
    })
}

/// The type as it is written in error messages (namespaces stripped).
pub fn full_strip_ns<E: PrintEnv + ?Sized>(hide_internals: bool, env: &E, ty: &Ty) -> String {
    supply_fuel(None, env.get_tcopt(), |fuel| {
        full::to_string(fuel, |fuel, st| {
            full::locl_ty(
                fuel,
                hide_internals,
                &full::text_strip_ns,
                st,
                Penv::Loclenv(env),
                ty,
            )
        })
    })
}

pub fn full_strip_ns_i<E: PrintEnv + ?Sized>(
    hide_internals: bool,
    env: &E,
    ty: &InternalType,
) -> String {
    supply_fuel(None, env.get_tcopt(), |fuel| {
        full::to_string(fuel, |fuel, st| {
            full::internal_type(
                fuel,
                hide_internals,
                &full::text_strip_ns,
                st,
                Penv::Loclenv(env),
                ty,
            )
        })
    })
}

/// Print a decl type, stripping backslash namespaces.
///
/// - `msg`: if fuel reaches 0, if msg = true, an error message is added to the
///   type representation. msg is true by default
/// - `verbose_fun`: print function types verbosely, with type parameters,
///   `async` keyword, `where` constraints and disposable attributes.
pub fn full_strip_ns_decl<E: PrintEnv + ?Sized>(
    msg: Option<bool>,
    verbose_fun: bool,
    env: &E,
    ty: &DeclTy,
) -> String {
    supply_fuel(msg, env.get_tcopt(), |fuel| {
        full::to_string(fuel, |fuel, st| {
            full::decl_ty(
                fuel,
                &full::text_strip_ns,
                st,
                Penv::Loclenv(env),
                verbose_fun,
                false,
                ty,
            )
        })
    })
}

pub fn full_decl(msg: Option<bool>, tcopt: &TypecheckerOptions, ty: &DeclTy) -> String {
    supply_fuel(msg, tcopt, |fuel| {
        // Full.to_string_decl
        full::to_string(fuel, |fuel, st| {
            full::decl_ty::<SimpleEnv>(fuel, &full::doc_text, st, Penv::Declenv, false, false, ty)
        })
    })
}

/// Print a locl_type to a string, stripping namespaces, including exact
/// annotations and type variable numbering
pub fn debug<E: PrintEnv + ?Sized>(env: &E, ty: &Ty) -> String {
    full_strip_ns(false, env, ty)
}

pub fn debug_decl<E: PrintEnv + ?Sized>(env: &E, ty: &DeclTy) -> String {
    full_strip_ns_decl(None, true, env, ty)
}

/// Print an internal type to a string, stripping namespaces, including exact
/// annotations and type variable numbering
pub fn debug_i<E: PrintEnv + ?Sized>(env: &E, ty: &InternalType) -> String {
    full_strip_ns_i(false, env, ty)
}

pub fn constraints_for_type<E: PrintEnv + ?Sized>(
    hide_internals: bool,
    env: &E,
    ty: &Ty,
) -> String {
    supply_fuel(None, env.get_tcopt(), |fuel| {
        let doc = full::constraints_for_type(fuel, hide_internals, &full::text_strip_ns, env, ty);
        doc::strip(&doc::format_doc_unbroken(&doc)).to_string()
    })
}

pub fn classish_kind(c_kind: &ClassishKind, final_: bool) -> String {
    error_string::classish_kind(c_kind, final_)
}

/// `exception UndesugarableCoeffect of locl_ty`
struct UndesugarableCoeffect;

pub fn coeffects<E: PrintEnv + ?Sized>(env: &E, ty: &Ty) -> String {
    supply_fuel(None, env.get_tcopt(), |fuel| {
        let to_string = |fuel: &mut Fuel, ty: &Ty| {
            full::to_string(fuel, |fuel, st| {
                full::locl_ty(
                    fuel,
                    true,
                    &full::text_strip_all_ns,
                    st,
                    Penv::Loclenv(env),
                    ty,
                )
            })
        };
        // We are interested in the upper bounds because coeffects are parameters (contravariant).
        // Similar to Typing_subtype.describe_ty_super, we ignore Tvars appearing in bounds
        let upper_bounds = |v: Tvid| -> Vec<Ty> {
            env.get_tyvar_upper_bounds(v)
                .into_iter()
                .filter_map(|ity| match ity {
                    InternalType::LoclType(lty) => match lty.get_node() {
                        Ty_::Tvar(_) => None,
                        _ => Some(lty),
                    },
                    InternalType::ConstraintType(_) => None,
                })
                .collect()
        };
        fn desugar_simple_intersection(
            fuel: &mut Fuel,
            to_string: &dyn Fn(&mut Fuel, &Ty) -> String,
            upper_bounds: &dyn Fn(Tvid) -> Vec<Ty>,
            ty: &Ty,
        ) -> Result<Vec<String>, UndesugarableCoeffect> {
            match ty.get_node() {
                Ty_::Tvar(v) => {
                    let mut res = vec![];
                    for ty in upper_bounds(*v) {
                        res.extend(desugar_simple_intersection(
                            fuel,
                            to_string,
                            upper_bounds,
                            &ty,
                        )?);
                    }
                    Ok(res)
                }
                Ty_::Tintersection(tyl) => {
                    let mut res = vec![];
                    for ty in tyl {
                        res.extend(desugar_simple_intersection(
                            fuel,
                            to_string,
                            upper_bounds,
                            ty,
                        )?);
                    }
                    Ok(res)
                }
                Ty_::Tunion(tyl) if tyl.len() == 1 => {
                    desugar_simple_intersection(fuel, to_string, upper_bounds, &tyl[0])
                }
                Ty_::Tunion(_) | Ty_::Tnonnull | Ty_::Tdynamic(_) => Err(UndesugarableCoeffect),
                Ty_::Toption(ty_) => match ty_.get_node() {
                    // another special case of `mixed`
                    Ty_::Tnonnull => Ok(vec![]),
                    _ => Err(UndesugarableCoeffect),
                },
                _ => Ok(vec![to_string(fuel, ty)]),
            }
        }

        let attempt = |fuel: &mut Fuel| -> Result<String, UndesugarableCoeffect> {
            let ty = env.expand_type(ty);
            let ty: Cow<'_, Ty> = match ty.get_node() {
                Ty_::Tvar(v) => {
                    let upper_bounds = upper_bounds(*v);
                    match upper_bounds.len() {
                        0 => return Err(UndesugarableCoeffect),
                        // Typing_make_type.intersection r upper_bounds
                        1 => Cow::Owned(upper_bounds.into_iter().next().unwrap()),
                        _ => Cow::Owned(mk(
                            ty.get_reason().clone(),
                            Ty_::Tintersection(upper_bounds),
                        )),
                    }
                }
                _ => ty,
            };
            let tyl = desugar_simple_intersection(fuel, &to_string, &upper_bounds, &ty)?;
            Ok(match tyl.as_slice() {
                [cap] => format!("the capability {}", cap),
                _ => {
                    // List.dedup_and_sort
                    let caps: BTreeSet<String> = tyl.into_iter().collect();
                    let caps: Vec<String> = caps.into_iter().collect();
                    format!("the capability set {{{}}}", caps.join(", "))
                }
            })
        };
        // (The fuel is not threaded out of the `try`: what was spent before the
        // exception is given back.)
        let fuel_before = *fuel;
        match attempt(fuel) {
            Ok(coeffect_str) => coeffect_str,
            Err(UndesugarableCoeffect) => {
                *fuel = fuel_before;
                to_string(fuel, ty)
            }
        }
    })
}

#[cfg(feature = "port")]
mod identity;
#[cfg(feature = "port")]
pub use identity::full_decl_with_identity;
#[cfg(feature = "port")]
pub use identity::full_with_identity;

#[cfg(test)]
mod tests;
