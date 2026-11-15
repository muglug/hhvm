// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_env_types.ml`. See `hh/PORTING.md`.
//!
//! # Cloning
//!
//! [`Env`] is the environment that every typing function takes as `&mut Env`.
//! Cloning it is cheap: the collections are persistent (`im`), and the two
//! records that OCaml allocates separately and shares between copies of the
//! environment, [`Genv`] and `Decl_env.env`, are behind an [`Rc`] (they hold
//! strings). Read them as in OCaml (`env.genv.tcopt`); to update a field, use
//! the functions of `typing_env`, or `Rc::make_mut(&mut env.genv).field = ..`,
//! which is OCaml's `{ env with genv = { env.genv with field } }`.
//!
//! # State shared between copies of an environment
//!
//! In OCaml three fields are mutable values that every copy of an environment
//! shares: `expression_id_provider` and `tvar_id_provider` (`Ident_provider.t`
//! is an `int ref`) and `big_envs` (a `ref`). Here too: `big_envs` is an
//! `Rc<RefCell<..>>`, and `expression_id::Provider` and `tvid::Provider`
//! (`crate::ident_provider::T`) are handles on a shared counter, so that a
//! clone of an environment hands out the identifiers that follow those of the
//! original (they are printed: `<expr#1>`). This is also why the functions
//! that only read the environment (`&Env`) can still make a fresh identifier
//! (`typing_env::make_expression_id`), as in OCaml.
//!
//! `Env` is not `Send` (`Rc`): one file is checked on one thread.

use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Arc;

use oxidized::aast;
use oxidized::ast_defs;
use oxidized::file_info;
use oxidized::local_id::LocalId;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use oxidized::typechecker_options::TypecheckerOptions;
use relative_path::RelativePath;

use crate::ctx::Ctx;
use crate::decl_counters;
use crate::decl_env;
use crate::expression_id;
use crate::tast;
use crate::tvid;
use crate::type_parameter_env;
use crate::type_visitor;
use crate::typing_continuations as c;
use crate::typing_defs_core::DeclTy;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::ValKind;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::mk;
use crate::typing_deps::dep;
use crate::typing_env_return_info;
use crate::typing_inference_env;
use crate::typing_kinding_defs;
use crate::typing_local_types;
use crate::typing_per_cont_env;
use crate::typing_reason;
use crate::typing_reason::T as Reason;
use crate::typing_set;

/// `S_set.t`
type SSet = im::OrdSet<String>;

/// Local environment includes types of locals and bounds on type parameters.
#[derive(Clone)]
pub struct LocalEnv {
    pub per_cont_env: typing_per_cont_env::T,
    /// Local variables that were assigned in a `using` clause
    pub local_using_vars: crate::pmap::Set<LocalId>,
}

/// Contains contextual information useful when type checking an
/// expression tree.
#[derive(Clone)]
pub struct ExprTreeEnv {
    /// The DSL the expression tree is representing. For instance in:
    ///
    /// SomeDSL`1 + 1`
    ///
    /// This hint would reference `SomeDsl`
    pub dsl: aast::ClassName,
    /// The set of locals defined outside the expression tree. Ex:
    ///   $x = 10;
    ///   SomeDSL`1 + 1`;
    ///
    /// `$x` would be in this set
    pub outer_locals: typing_local_types::T,
}

/// `Typing_env_types.env`, an immutable record in OCaml: keeping an old
/// environment costs nothing there, as every update builds a new record and
/// the old one stays valid.
///
/// Here the environment is a handle on a shared [`EnvData`]: cloning it bumps
/// a reference count, and the fields are read through `Deref`. The first
/// write through a handle that shares its data with another copy (through
/// `DerefMut`, `Rc::make_mut`) copies the fields, so that the other copies
/// keep the old values, as in OCaml; later writes are in place. Functions
/// that may not write should therefore read through `&Env` (or `&**env`)
/// until they know they will write.
#[derive(Clone)]
pub struct Env(Rc<EnvData>);

impl std::ops::Deref for Env {
    type Target = EnvData;
    #[inline]
    fn deref(&self) -> &EnvData {
        &self.0
    }
}

impl std::ops::DerefMut for Env {
    #[inline]
    fn deref_mut(&mut self) -> &mut EnvData {
        Rc::make_mut(&mut self.0)
    }
}

impl Env {
    pub fn new(data: EnvData) -> Env {
        Env(Rc::new(data))
    }

    /// Whether the two handles share their fields (no write happened through
    /// either since one was cloned from the other).
    pub fn ptr_eq(a: &Env, b: &Env) -> bool {
        Rc::ptr_eq(&a.0, &b.0)
    }
}

/// The fields of [`Env`]. Cheap to clone too: see the documentation of the
/// module.
///
/// Not in the OCaml: the fields that are rarely written are in [`EnvCold`],
/// behind one more `Rc`, which `Deref`/`DerefMut` reach (`env.genv`,
/// `env.in_expr_tree = ..` work as for the other fields). The first write
/// after a copy of the environment (one per expression: see
/// `typing::expr`) then copies only the fields here and that `Rc`.
#[derive(Clone)]
pub struct EnvData {
    /// Shared between the copies of an environment.
    pub expression_id_provider: expression_id::Provider,
    /// Shared between the copies of an environment.
    pub tvar_id_provider: tvid::Provider,
    pub lenv: LocalEnv,
    pub in_loop: bool,
    pub in_try: bool,
    pub in_lambda: bool,
    /// Set to true when checking if a <<__SoundDynamicallyCallable>> method body
    /// is well-typed under dyn..dyn->dyn assumptions, that is if it can be safely called
    /// in a dynamic environment.
    pub checked: tast::CheckStatus,
    /// A set of constraints that are global to a given method
    pub tpenv: type_parameter_env::T,
    pub inference_env: typing_inference_env::T,
    /// The rank at which fresh type variables and type parameters should be generated
    pub rank: isize,
    /// Heuristic to determine when we need to check ranks during subtyping
    pub check_rank: bool,
    pub allow_wildcards: bool,
    /// Gates which expressions emit class pointer to string coercion errors
    pub emit_string_coercion_error: bool,
    pub cold: Rc<EnvCold>,
}

/// The fields of [`EnvData`] that are rarely written.
#[derive(Clone)]
pub struct EnvCold {
    pub fresh_typarams: crate::pmap::Set<String>,
    pub genv: Rc<Genv>,
    pub decl_env: Rc<decl_env::Env>,
    /// If set to Some(_), then we are performing type checking within a
    /// expression tree.
    pub in_expr_tree: Option<ExprTreeEnv>,
    /// If set to Some(local_env) then we are type checking within a splice that
    /// contains nested expression trees with free variables. local_env contains
    /// the bindings for those free variables
    pub in_macro_splice: Option<typing_local_types::T>,
    /// Tracing_info is a way, when we record telemetry on costs, to also record which
    /// area of the typing code should be considered the originator of that work,
    /// so we can add up which area contributed most to overall costs.
    ///
    /// Behind an `Rc` (not in the OCaml): it holds a path.
    pub tracing_info: Option<Rc<decl_counters::TracingInfo>>,
    pub log_levels: crate::pmap::Map<String, isize>,
    /// Shared between the copies of an environment (a `ref` in OCaml). The
    /// head of the OCaml list is the last element: `big_envs := x :: !big_envs`
    /// is `env.big_envs.borrow_mut().push(x)`.
    pub big_envs: Rc<RefCell<Vec<(Pos, Env)>>>,
    /// This is only filled in after type-checking the function in question
    pub fun_tast_info: Option<tast::FunTastInfo>,
}

impl std::ops::Deref for EnvData {
    type Target = EnvCold;
    #[inline]
    fn deref(&self) -> &EnvCold {
        &self.cold
    }
}

impl std::ops::DerefMut for EnvData {
    #[inline]
    fn deref_mut(&mut self) -> &mut EnvCold {
        Rc::make_mut(&mut self.cold)
    }
}

/// `Typing_env_types.genv`. The fields `return`, `self` and `static` of the
/// OCaml record are Rust keywords: they are `return_`, `self_` and `static_`.
#[derive(Clone)]
pub struct Genv {
    pub tcopt: Arc<TypecheckerOptions>,
    /// position of the function/method name being checked
    pub callable_pos: Pos,
    /// position of the full function/method being checked
    pub function_pos: Pos,
    /// Whether readonly analysis is needed on this function
    pub readonly: bool,
    pub return_: typing_env_return_info::T,
    /// For each function/method parameter, its type, position, and inout "return" type.
    pub params: im::OrdMap<LocalId, (Ty, Pos, Option<Ty>)>,
    /// Identifier and type of the parent class if it exists
    pub parent: Option<(String, DeclTy)>,
    /// Identifier and type (instatiated at its generic parameters) of
    /// the enclosing class if there is one
    pub self_: Option<(String, Ty)>,
    pub static_: bool,
    pub fun_kind: ast_defs::FunKind,
    pub val_kind: ValKind,
    /// Is the method a constructor?
    pub fun_is_ctor: bool,
    /// The file containing the top-level definition that we are checking
    pub file: Arc<RelativePath>,
    /// The module of the top-level definition that we are checking
    pub current_module: Option<ast_defs::Id>,
    /// The package membership of a top-level definition that we're checking
    pub current_package: Option<aast::PackageMembership>,
    /// The __SoftRequirePackage annotation on the current function/method if present
    pub soft_package_requirement: Option<ast_defs::Id>,
    /// Is the definition that we are checking marked internal?
    pub this_internal: bool,
    /// Is the definition that we are checking marked <<__SupportDynamicType>>?
    pub this_support_dynamic_type: bool,
    /// Is the definition that we are checking marked <<__NoAutoLikes>>?
    pub no_auto_likes: bool,
    /// Is the definition that we are checking marked <<__NeedsConcrete>>?
    pub needs_concrete: bool,
}

/// `Typing_env.show_env`: the environment is not printed.
impl std::fmt::Debug for Env {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("<env>")
    }
}

fn initial_local(tpenv: type_parameter_env::T) -> LocalEnv {
    LocalEnv {
        per_cont_env: typing_per_cont_env::initial_locals(typing_per_cont_env::PerContEntry {
            tpenv,
            ..typing_per_cont_env::empty_entry()
        }),
        local_using_vars: crate::pmap::Set::new(),
    }
}

pub fn empty(
    origin: Option<decl_counters::Origin>,
    mode: Option<file_info::Mode>,
    ctx: Arc<Ctx>,
    file: Arc<RelativePath>,
    droot: Option<dep::Variant>,
) -> Env {
    let mode = mode.unwrap_or(file_info::Mode::Mstrict);
    // `Provider_context.get_tcopt ctx`
    let tcopt = Arc::clone(&ctx.tco);
    Env::new(EnvData {
        expression_id_provider: expression_id::make_provider(),
        tvar_id_provider: tvid::make_provider(),
        lenv: initial_local(type_parameter_env::empty()),
        in_loop: false,
        in_try: false,
        in_lambda: false,
        checked: tast::CheckStatus::COnce,
        tpenv: type_parameter_env::empty(),
        inference_env: typing_inference_env::empty_inference_env(),
        rank: 0,
        check_rank: false,
        allow_wildcards: false,
        emit_string_coercion_error: true,
        cold: Rc::new(EnvCold {
            fresh_typarams: crate::pmap::Set::new(),
            in_expr_tree: None,
            in_macro_splice: None,
            decl_env: Rc::new(decl_env::Env {
                mode,
                droot,
                droot_member: None,
                ctx,
            }),
            tracing_info: origin.map(|origin| {
                Rc::new(decl_counters::TracingInfo {
                    origin,
                    file: RelativePath::clone(&file),
                })
            }),
            // `Typechecker_options.log_levels`
            log_levels: tcopt
                .log_levels
                .iter()
                .map(|(key, level)| (key.clone(), *level))
                .collect(),
            genv: Rc::new(Genv {
                tcopt,
                callable_pos: Pos::NONE,
                function_pos: Pos::NONE,
                readonly: false,
                return_: typing_env_return_info::T {
                    // Actually should get set straight away anyway
                    return_type: mk((typing_reason::none(), Ty_::Tunion(vec![]))),
                    return_disposable: false,
                    return_ignore_readonly: false,
                },
                params: im::OrdMap::new(),
                self_: None,
                static_: false,
                val_kind: ValKind::Other,
                parent: None,
                fun_kind: ast_defs::FunKind::FSync,
                fun_is_ctor: false,
                file,
                current_module: None,
                current_package: None,
                soft_package_requirement: None,
                this_internal: false,
                this_support_dynamic_type: false,
                no_auto_likes: false,
                needs_concrete: false,
            }),
            big_envs: Rc::new(RefCell::new(vec![])),
            fun_tast_info: None,
        }),
    })
}

pub fn get_log_level(env: &Env, key: &str) -> isize {
    env.log_levels.get(key).copied().unwrap_or(0)
}

pub fn next_cont_opt(env: &Env) -> Option<typing_per_cont_env::PerContEntry> {
    typing_per_cont_env::get_cont_option(c::T::Next, &env.lenv.per_cont_env)
}

pub fn get_tpenv(env: &Env) -> type_parameter_env::T {
    // `next_cont_opt env`, without copying the rest of the entry.
    match env.lenv.per_cont_env.get(&c::T::Next) {
        None => type_parameter_env::empty(),
        Some(entry) => entry.tpenv.clone(),
    }
}

pub fn get_pos_and_kind_of_generic(
    env: &Env,
    name: &str,
) -> Option<(PosOrDecl, typing_kinding_defs::Kind)> {
    match type_parameter_env::get_with_pos(name, &get_tpenv(env)) {
        Some(r) => Some(r),
        None => type_parameter_env::get_with_pos(name, &env.tpenv),
    }
}

pub fn get_lower_bounds(env: &Env, name: &str) -> type_parameter_env::TparamBounds {
    let tpenv = get_tpenv(env);
    let local = type_parameter_env::get_lower_bounds(&tpenv, name);
    let global = type_parameter_env::get_lower_bounds(&env.tpenv, name);
    typing_set::union(&local, &global)
}

pub fn get_upper_bounds(env: &Env, name: &str) -> type_parameter_env::TparamBounds {
    let tpenv = get_tpenv(env);
    let local = type_parameter_env::get_upper_bounds(&tpenv, name);
    let global = type_parameter_env::get_upper_bounds(&env.tpenv, name);
    typing_set::union(&local, &global)
}

/// Get bounds that are both an upper and lower of a given generic
pub fn get_equal_bounds(env: &Env, name: &str) -> type_parameter_env::TparamBounds {
    let lower = get_lower_bounds(env, name);
    let upper = get_upper_bounds(env, name);
    typing_set::inter(&lower, &upper)
}

pub fn get_tparams_in_ty_and_acc(env: &Env, acc: SSet, ty: &Ty) -> SSet {
    struct TparamsVisitor<'a> {
        env: &'a Env,
    }
    impl type_visitor::LoclTypeVisitor<SSet> for TparamsVisitor<'_> {
        fn on_tgeneric(&mut self, mut acc: SSet, _r: &Reason, s: &str) -> SSet {
            // Not traversing args, although they may contain Tgenerics (higher kinds only)
            acc.insert(s.to_string());
            acc
        }

        fn on_tvar(&mut self, acc: SSet, r: &Reason, ix: tvid::T) -> SSet {
            // The OCaml drops the inference environment that `expand_var`
            // returns: expand in a copy.
            let mut inference_env = self.env.inference_env.clone();
            let ty = typing_inference_env::expand_var(&mut inference_env, r.clone(), ix);
            match get_node(&ty) {
                Ty_::Tvar(_) => acc,
                _ => self.on_type(acc, &ty),
            }
        }
    }
    let mut tparams_visitor = TparamsVisitor { env };
    type_visitor::LoclTypeVisitor::on_type(&mut tparams_visitor, acc, ty)
}

pub fn get_rank(env: &Env) -> isize {
    env.rank
}

pub fn increment_rank(env: &mut Env) {
    env.rank += 1;
    env.check_rank = true;
}

pub fn decrement_rank(env: &mut Env) {
    env.rank -= 1;
}

pub fn should_check_rank(env: &Env) -> bool {
    env.check_rank
}
