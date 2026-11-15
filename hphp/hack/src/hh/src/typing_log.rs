// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_log.ml`. See `hh/PORTING.md`.
//!
//! Logging of types and of the typing environment, for `hh_show`,
//! `hh_show_env` and the log levels (`hh_log_level`, the `log_levels`
//! option). The functions log only when the level of their category asks for
//! it, as in OCaml.
//!
//! # State
//!
//! The global `ref`s of the OCaml (the output channel, the pieces of the line
//! being logged, the indentation, the last environment shown, the number of
//! times each position was logged) are `thread_local!` statics with the OCaml
//! names in upper case: one file is checked on one thread. [`OUT_CHANNEL`] is the one the
//! `.mli` exports (`Typing_log.out_channel := oc` is
//! `typing_log::OUT_CHANNEL.with(|c| *c.borrow_mut() = oc)`); it is stdout
//! by default, and is flushed after every line, as in OCaml.
//!
//! The logging functions call back the functions they are given (`f`), which
//! may log too: no state is borrowed while they run.
//!
//! # Formatting
//!
//! `lprintf c fmt args` is `lprintf(c, format!(fmt, args))`.
//!
//! Some functions that the OCaml calls in other modules are missing there;
//! they are written here, private, under the name of their module:
//! `Typing_print.subtype_prop` (`crate::typing_print` does not have it),
//! `Ast_defs.show_id`, `Aast_defs.show_class_name` and
//! `Tast.show_check_status` (`[@@deriving show]`).

use std::cell::Cell;
use std::cell::RefCell;
use std::io::Write;
use std::sync::Arc;

use ::pos::ToOxidized;
use oxidized::aast;
use oxidized::ast_defs;
use oxidized::parser_options::ParserOptions;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use oxidized::typechecker_options::TypecheckerOptions;

use crate::expression_id;
use crate::hh_logger;
use crate::local_id;
use crate::measure;
use crate::s_map;
use crate::s_set;
use crate::tast;
use crate::tty;
use crate::tty::ColorMode;
use crate::tty::RawColor::Green;
use crate::tty::RawColor::Red;
use crate::tty::RawColor::White;
use crate::tty::RawColor::Yellow;
use crate::tty::Style;
use crate::tvid;
use crate::type_parameter_env;
use crate::typing_continuations;
use crate::typing_defs_constraints::InternalType;
use crate::typing_defs_constraints::equal_internal_type;
use crate::typing_defs_core::DeclTparam;
use crate::typing_defs_core::DeclTy;
use crate::typing_defs_core::PosId;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::ValKind;
use crate::typing_env_return_info;
use crate::typing_env_types;
use crate::typing_env_types::Env;
use crate::typing_env_types::ExprTreeEnv;
use crate::typing_env_types::Genv;
use crate::typing_env_types::LocalEnv;
use crate::typing_fake_members;
use crate::typing_inference_env as inf;
use crate::typing_kinding_defs;
use crate::typing_local_packages;
use crate::typing_local_types;
use crate::typing_log_value::Value;
use crate::typing_log_value::bool_as_value;
use crate::typing_log_value::local_id_as_string;
use crate::typing_log_value::local_id_set_as_value;
use crate::typing_log_value::make_map;
use crate::typing_log_value::pos_as_value;
use crate::typing_log_value::string_as_value;
use crate::typing_logic;
use crate::typing_logic::SubtypeProp;
use crate::typing_per_cont_env;
use crate::typing_print as pr;
use crate::typing_set as ty_set;

// ~~ Logging type inference environment ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// `Stdlib.out_channel`
pub type OutChannel = Box<dyn std::io::Write>;

thread_local! {
    /// Eventual input to Tty.cprint
    pub static OUT_CHANNEL: RefCell<OutChannel> = RefCell::new(Box::new(std::io::stdout()));

    /// The pieces of the line being logged. The head of the OCaml list is the
    /// last element.
    static LOG_BUFFER: RefCell<Vec<(Style, String)>> = const { RefCell::new(Vec::new()) };

    /// Controls the current indentation
    static INDENT_LEVEL: Cell<isize> = const { Cell::new(0) };

    static ACCUMULATED_LENGTH: Cell<isize> = const { Cell::new(0) };

    /// Most recent environment. We only display diffs.
    ///
    /// `None` stands for the initial value, the empty environment of
    /// [`lastenv_initial`], which is made when it is first read (OCaml makes
    /// it when the module is initialised; making it has no other effect).
    static LASTENV: RefCell<Option<Env>> = const { RefCell::new(None) };

    static ITERATIONS: RefCell<crate::pos::map::T<isize>> =
        RefCell::new(crate::pos::map::T::new());

    static ITERATIONS_DECL: RefCell<crate::pos_or_decl::map::T<isize>> =
        RefCell::new(crate::pos_or_decl::map::T::new());
}

/// `String.make n c`
fn string_make(n: isize, c: char) -> String {
    if n < 0 {
        panic!("Invalid_argument: String.make")
    }
    std::iter::repeat_n(c, n as usize).collect()
}

/// Writes what's in `logBuffer` on a new line, respecting
/// the current identation from `indentLevel`.
/// Flush the channel and reset `logBuffer`
fn lnewline() {
    let log_buffer = LOG_BUFFER.with(|b| b.borrow().clone());
    match log_buffer.as_slice() {
        [] => (),
        _ => {
            let mut strs = Vec::with_capacity(log_buffer.len() + 2);
            strs.push((Style::Normal(White), string_make(2 * INDENT_LEVEL.get(), ' ')));
            strs.extend(log_buffer);
            strs.push((Style::Normal(White), "\n".to_string()));
            OUT_CHANNEL.with(|oc| {
                let mut oc = oc.borrow_mut();
                tty::cprint(Some(ColorMode::ColorAuto), Some(&mut **oc), &strs);
                if let Err(e) = oc.flush() {
                    panic!("Sys_error: {}", e)
                }
            });
            ACCUMULATED_LENGTH.set(0);
            LOG_BUFFER.with(|b| b.borrow_mut().clear())
        }
    }
}

/// Accumulate input format string into logBuffer,
/// possibly printing a line if the buffer gets to big.
fn lprintf(c: Style, s: String) {
    let len = s.len() as isize;
    LOG_BUFFER.with(|b| b.borrow_mut().push((c, s)));
    if ACCUMULATED_LENGTH.get() + len > 80 {
        lnewline()
    } else {
        ACCUMULATED_LENGTH.set(ACCUMULATED_LENGTH.get() + len)
    }
}

/// Prints a new line and ident
fn lnewline_open() {
    lnewline();
    INDENT_LEVEL.set(INDENT_LEVEL.get() + 1)
}

/// Prints a new line and unident
fn lnewline_close() {
    lnewline();
    INDENT_LEVEL.set(INDENT_LEVEL.get() - 1)
}

fn with_indent<R>(f: impl FnOnce() -> R) -> R {
    lnewline_open();
    let res = f();
    lnewline_close();
    res
}

/// `color` defaults to `Normal Yellow`.
fn indent_env<R>(color: Option<Style>, message: &str, f: impl FnOnce() -> R) -> R {
    let color = color.unwrap_or(Style::Normal(Yellow));
    lnewline();
    lprintf(color, message.to_string());
    with_indent(f)
}

/// The initial value of `lastenv`.
fn lastenv_initial() -> Env {
    typing_env_types::empty(
        None,
        None,
        crate::provider_context::empty_for_debugging(
            ParserOptions::default(),
            TypecheckerOptions::default(),
            crate::typing_deps_mode::T::InMemoryMode(None),
        ),
        Arc::new(crate::relative_path::DEFAULT),
        None,
    )
}

/// `!lastenv`
fn lastenv_get() -> Env {
    let env = LASTENV.with(|e| e.borrow().clone());
    match env {
        Some(env) => env,
        None => {
            let env = lastenv_initial();
            LASTENV.with(|e| *e.borrow_mut() = Some(env.clone()));
            env
        }
    }
}

/// Universal representation of a delta between values
#[derive(Clone, Debug)]
enum Delta {
    /// For bools, atoms, lists, replaced sets, replaced maps
    Updated(Value),
    Unchanged,
    /// Set has had some elements removed, some added
    SetDelta { added: s_set::T, removed: s_set::T },
    /// Map has some new keys, some removed keys, and deltas to existing keys.
    /// All other keys assumed to be unchanged.
    MapDelta {
        added: s_map::T<Value>,
        removed: s_set::T,
        changed: s_map::T<Delta>,
    },
}

/// `S_set.diff s1 s2`
fn s_set_diff(s1: &s_set::T, s2: &s_set::T) -> s_set::T {
    s1.iter().filter(|x| !s2.contains(*x)).cloned().collect()
}

fn compute_value_delta(oldval: &Value, newval: &Value) -> Delta {
    match (oldval, newval) {
        (Value::Bool(b1), Value::Bool(b2)) => {
            if b1 == b2 {
                Delta::Unchanged
            } else {
                Delta::Updated(newval.clone())
            }
        }
        (Value::Atom(s1), Value::Atom(s2)) => {
            if s1 == s2 {
                Delta::Unchanged
            } else {
                Delta::Updated(newval.clone())
            }
        }
        (Value::Type(t1), Value::Type(t2)) => {
            if equal_internal_type(t1, t2) {
                Delta::Unchanged
            } else {
                Delta::Updated(newval.clone())
            }
        }
        (Value::SubtypeProp(p1), Value::SubtypeProp(p2)) => {
            if typing_logic::equal_subtype_prop(p1, p2) {
                Delta::Unchanged
            } else {
                Delta::Updated(newval.clone())
            }
        }
        (Value::Set(s1), Value::Set(s2)) => {
            let added = s_set_diff(s2, s1);
            let removed = s_set_diff(s1, s2);
            if added.is_empty() && removed.is_empty() {
                Delta::Unchanged
            } else {
                Delta::SetDelta { added, removed }
            }
        }
        (Value::List(l1), Value::List(l2)) => {
            if l1.len() == l2.len()
                && l1
                    .iter()
                    .zip(l2.iter())
                    .all(|(v1, v2)| crate::typing_log_value::equal_value(v1, v2))
            {
                Delta::Unchanged
            } else {
                Delta::Updated(newval.clone())
            }
        }
        (Value::Map(m1), Value::Map(m2)) => {
            let mut removed = s_set::T::new();
            for (i, _) in m1.iter() {
                match m2.get(i) {
                    None => {
                        removed.insert(i.clone());
                    }
                    Some(_) => (),
                }
            }
            let mut added = s_map::T::new();
            for (i, v) in m2.iter() {
                match m1.get(i) {
                    None => {
                        added.insert(i.clone(), v.clone());
                    }
                    _ => (),
                }
            }
            let mut changed = s_map::T::new();
            for (i, oldx) in m1.iter() {
                match m2.get(i) {
                    None => (),
                    Some(newx) => match compute_value_delta(oldx, newx) {
                        Delta::Unchanged => (),
                        d => {
                            changed.insert(i.clone(), d);
                        }
                    },
                }
            }
            if removed.is_empty() && added.is_empty() && changed.is_empty() {
                Delta::Unchanged
            } else {
                Delta::MapDelta {
                    removed,
                    added,
                    changed,
                }
            }
        }
        // Type has changed!
        (_, _) => Delta::Updated(newval.clone()),
    }
}

fn is_leaf_value(v: &Value) -> bool {
    match v {
        Value::Atom(_) | Value::Bool(_) | Value::List(_) => true,
        Value::Map(m) if m.is_empty() => true,
        Value::Set(_) => true,
        _ => false,
    }
}

pub fn log_key(key: &str) {
    lprintf(Style::Normal(Yellow), key.to_string())
}

fn log_sset(s: &s_set::T) {
    let elements: Vec<&String> = s.iter().collect();
    match elements.as_slice() {
        [] => lprintf(Style::Normal(Green), "{}".to_string()),
        [s] => lprintf(Style::Normal(Green), format!("{{{}}}", s)),
        [s, ss @ ..] => {
            lprintf(Style::Normal(Green), "{".to_string());
            lprintf(Style::Normal(Green), s.to_string());
            for s in ss {
                lprintf(Style::Normal(Green), format!(",{}", s))
            }
            lprintf(Style::Normal(Green), "}".to_string())
        }
    }
}

fn log_value(env: &Env, value: &Value) {
    match value {
        Value::Atom(s) => lprintf(Style::Normal(Green), s.clone()),
        Value::Bool(b) => lprintf(
            Style::Normal(Green),
            (if *b { "true" } else { "false" }).to_string(),
        ),
        Value::List(l) => match l.as_slice() {
            [] => lprintf(Style::Normal(Green), "[]".to_string()),
            [v, vs @ ..] => {
                lprintf(Style::Normal(Green), "[".to_string());
                log_value(env, v);
                for v in vs {
                    lprintf(Style::Normal(Green), ",".to_string());
                    log_value(env, v)
                }
                lprintf(Style::Normal(Green), "]".to_string())
            }
        },
        Value::Map(m) => {
            if m.is_empty() {
                lprintf(Style::Normal(Green), "{}".to_string())
            } else {
                for (k, v) in m.iter() {
                    log_key_value(env, "", k, v)
                }
            }
        }
        Value::Set(s) => log_sset(s),
        Value::Type(ty) => lprintf(Style::Normal(Green), pr::debug_i(env, ty)),
        Value::SubtypeProp(prop) => {
            lprintf(Style::Normal(Green), pr::subtype_prop(env, prop))
        }
    }
}

fn log_key_value(env: &Env, prefix: &str, k: &str, v: &Value) {
    if is_leaf_value(v) {
        lprintf(Style::Normal(Green), prefix.to_string());
        log_key(k);
        lprintf(Style::Normal(Yellow), " ".to_string());
        log_value(env, v);
        lnewline()
    } else {
        lnewline();
        lprintf(Style::Normal(Green), prefix.to_string());
        log_key(k);
        with_indent(|| log_value(env, v))
    }
}

fn is_leaf_delta(d: &Delta) -> bool {
    match d {
        Delta::Updated(v) => is_leaf_value(v),
        // | Added d | Removed d | Updated d -> is_leaf_delta d
        _ => false,
    }
}

fn log_delta(env: &Env, delta: &Delta) {
    match delta {
        Delta::Updated(v) => log_value(env, v),
        Delta::Unchanged => (),
        Delta::SetDelta { added, removed } => {
            if !added.is_empty() {
                lprintf(Style::Bold(Green), " += ".to_string());
                log_sset(added)
            }
            if !removed.is_empty() {
                lprintf(Style::Bold(Red), " -= ".to_string());
                log_sset(removed)
            }
        }
        Delta::MapDelta {
            added,
            removed,
            changed,
        } => {
            for k in removed.iter() {
                lprintf(Style::Bold(Red), "-".to_string());
                log_key(k);
                lnewline()
            }
            for (k, v) in added.iter() {
                log_key_value(env, "+", k, v)
            }
            for (k, d) in changed.iter() {
                log_key_delta(env, k, d)
            }
        }
    }
}

fn log_key_delta(env: &Env, k: &str, d: &Delta) {
    if is_leaf_delta(d) {
        log_key(k);
        lprintf(Style::Normal(Yellow), " ".to_string());
        log_delta(env, d);
        lnewline()
    } else {
        lnewline();
        log_key(k);
        lprintf(Style::Normal(Yellow), " ".to_string());
        with_indent(|| log_delta(env, d))
    }
}

fn type_as_value(env: &Env, ty: &Ty) -> Value {
    Value::Atom(pr::debug(env, ty))
}

fn decl_type_as_value(env: &Env, ty: &DeclTy) -> Value {
    Value::Atom(pr::debug_decl(env, &ty.clone().to_oxidized()))
}

fn return_info_as_value(env: &Env, return_info: &typing_env_return_info::T) -> Value {
    let typing_env_return_info::T {
        return_type,
        return_disposable,
        return_ignore_readonly,
    } = return_info;
    make_map(vec![
        ("return_type".to_string(), type_as_value(env, return_type)),
        (
            "return_disposable".to_string(),
            Value::Bool(*return_disposable),
        ),
        (
            "return_ignore_readonly".to_string(),
            Value::Bool(*return_ignore_readonly),
        ),
    ])
}

fn local_id_map_as_value<A: Clone, M: crate::wrapped_map::MapLike<local_id::T, A>>(
    f: impl Fn(&A) -> Value,
    m: &M,
) -> Value {
    let mut res = s_map::T::new();
    for (id, x) in m.ml_iter() {
        res.insert(local_id_as_string(id), f(x));
    }
    Value::Map(res)
}

fn reify_kind_as_value(k: &aast::ReifyKind) -> Value {
    string_as_value(
        match k {
            aast::ReifyKind::Erased => "erased",
            aast::ReifyKind::SoftReified => "soft_reified",
            aast::ReifyKind::Reified => "reified",
        }
        .to_string(),
    )
}

fn tyset_as_value(env: &Env, tys: &ty_set::T) -> Value {
    let mut s = s_set::T::new();
    for t in tys.iter() {
        s.insert(pr::debug(env, t));
    }
    Value::Set(s)
}

fn tparam_info_as_value(env: &Env, tpinfo: &typing_kinding_defs::Kind) -> Value {
    let typing_kinding_defs::Kind {
        lower_bounds,
        upper_bounds,
        reified,
        enforceable,
        newable,
        require_dynamic,
        rank,
    } = tpinfo;
    make_map(vec![
        ("lower_bounds".to_string(), tyset_as_value(env, lower_bounds)),
        ("upper_bounds".to_string(), tyset_as_value(env, upper_bounds)),
        ("reified".to_string(), reify_kind_as_value(reified)),
        ("enforceable".to_string(), bool_as_value(*enforceable)),
        ("newable".to_string(), bool_as_value(*newable)),
        ("require_dynamic".to_string(), bool_as_value(*require_dynamic)),
        ("rank".to_string(), string_as_value(rank.to_string())),
    ])
}

fn tpenv_as_value(env: &Env, tpenv: &type_parameter_env::T) -> Value {
    make_map(vec![
        (
            "tparams".to_string(),
            Value::Map(type_parameter_env::fold(
                |name, tpinfo, mut m: s_map::T<Value>| {
                    m.insert(name.to_string(), tparam_info_as_value(env, tpinfo));
                    m
                },
                tpenv,
                s_map::T::new(),
            )),
        ),
        (
            "consistent".to_string(),
            bool_as_value(type_parameter_env::is_consistent(tpenv)),
        ),
    ])
}

fn per_cont_entry_as_value(
    env: &Env,
    f: impl Fn(&typing_local_types::Local) -> Value,
    entry: &typing_per_cont_env::PerContEntry,
) -> Value {
    make_map(vec![
        (
            "local_types".to_string(),
            local_id_map_as_value(f, &entry.local_types),
        ),
        (
            "fake_members".to_string(),
            typing_fake_members::as_log_value(&entry.fake_members),
        ),
        ("tpenv".to_string(), tpenv_as_value(env, &entry.tpenv)),
        (
            "loaded_packages".to_string(),
            typing_local_packages::as_log_value(&entry.loaded_packages),
        ),
    ])
}

fn continuations_map_as_value<A>(
    f: impl Fn(&A) -> Value,
    m: &typing_continuations::map::T<A>,
) -> Value {
    let mut res = s_map::T::new();
    for (k, x) in m.iter() {
        res.insert(typing_continuations::to_string(k), f(x));
    }
    Value::Map(res)
}

fn local_as_value(env: &Env, local: &typing_local_types::Local) -> Value {
    let typing_local_types::Local {
        ty,
        pos: _,
        eid,
        macro_splice_vars: _,
    } = local;
    Value::Atom(format!(
        "{} [expr_id={}]",
        pr::debug(env, ty),
        expression_id::debug(*eid)
    ))
}

fn per_cont_env_as_value(env: &Env, per_cont_env: &typing_per_cont_env::T) -> Value {
    continuations_map_as_value(
        |entry| per_cont_entry_as_value(env, |local| local_as_value(env, local), entry),
        per_cont_env,
    )
}

/// `function_name` is the OCaml's `?function_name`.
fn log_position(p: &Pos, function_name: Option<&str>, f: impl FnOnce()) {
    let n = ITERATIONS.with(|its| {
        let mut its = its.borrow_mut();
        match its.get(p).copied() {
            None => {
                its.insert(p.clone(), 1);
                1
            }
            Some(n) => {
                its.insert(p.clone(), n + 1);
                n + 1
            }
        }
    });
    // If we've hit this many iterations then something must have gone wrong
    // so let's not bother spewing to the log
    if n > 10000 {
    } else {
        let message = crate::pos::string(&crate::pos::to_absolute(p))
            + &(if n == 1 {
                "".to_string()
            } else {
                "[".to_string() + &n.to_string() + "]"
            })
            + &match function_name {
                None => "".to_string(),
                Some(n) => " {".to_string() + n + "}",
            };
        indent_env(Some(Style::Bold(Yellow)), &message, f)
    }
}

/// `function_name` is the OCaml's `?function_name`.
fn log_pos_or_decl<R>(p: &PosOrDecl, function_name: Option<&str>, f: impl FnOnce() -> R) -> R {
    let n = ITERATIONS_DECL.with(|its| {
        let mut its = its.borrow_mut();
        match its.get(p).copied() {
            None => {
                its.insert(p.clone(), 1);
                1
            }
            Some(n) => {
                its.insert(p.clone(), n + 1);
                n + 1
            }
        }
    });
    // If we've hit this many iterations then something must have gone wrong
    // so let's not bother spewing to the log
    if n > 10000 {
        f()
    } else {
        let message = crate::pos_or_decl::show_as_absolute_file_line_characters(p)
            + &(if n == 1 {
                "".to_string()
            } else {
                "[".to_string() + &n.to_string() + "]"
            })
            + &match function_name {
                None => "".to_string(),
                Some(n) => " {".to_string() + n + "}",
            };
        indent_env(Some(Style::Bold(Yellow)), &message, f)
    }
}

pub fn should_log(env: &Env, category: &str, level: isize) -> bool {
    typing_env_types::get_log_level(env, category) >= level
}

/// [`log_with_level`]`(env, level_category, level, log_f)` executes the the
/// logging function `log_f` if the configured level for the provided category
/// is higher than `level`.
pub fn log_with_level(env: &Env, category: &str, level: isize, log_f: impl FnOnce()) {
    if should_log(env, category, level) {
        log_f()
    }
}

fn log_subtype_prop(env: &Env, message: &str, prop: &SubtypeProp) {
    lprintf(Style::Bold(Green), format!("{}: ", message));
    lprintf(Style::Normal(Green), pr::subtype_prop(env, prop));
    lnewline()
}

fn fun_kind_to_string(k: &ast_defs::FunKind) -> String {
    match k {
        ast_defs::FunKind::FSync => "normal",
        ast_defs::FunKind::FAsync => "async",
        ast_defs::FunKind::FGenerator => "generator",
        ast_defs::FunKind::FAsyncGenerator => "async generator",
    }
    .to_string()
}

fn val_kind_to_string(k: &ValKind) -> String {
    match k {
        ValKind::Other => "other",
        ValKind::Lval => "lval",
        ValKind::LvalSubexpr => "lval subexpression",
    }
    .to_string()
}

fn lenv_as_value(env: &Env, lenv: &LocalEnv) -> Value {
    let LocalEnv {
        per_cont_env,
        local_using_vars,
    } = lenv;
    make_map(vec![
        (
            "per_cont_env".to_string(),
            per_cont_env_as_value(env, per_cont_env),
        ),
        (
            "local_using_vars".to_string(),
            local_id_set_as_value(local_using_vars),
        ),
    ])
}

fn param_as_value(env: &Env, (ty, _pos, ty_opt): &(Ty, Pos, Option<Ty>)) -> Value {
    let ty_str = pr::debug(env, ty);
    match ty_opt {
        None => Value::Atom(ty_str),
        Some(ty2) => {
            let ty2_str = pr::debug(env, ty2);
            Value::Atom(format!("{} inout {}", ty_str, ty2_str))
        }
    }
}

fn genv_as_value(env: &Env, genv: &Genv) -> Value {
    let Genv {
        tcopt: _,
        callable_pos,
        function_pos,
        readonly,
        return_,
        params,
        parent,
        self_,
        static_,
        val_kind,
        fun_kind,
        fun_is_ctor,
        file: _,
        current_module,
        current_package,
        soft_package_requirement,
        this_internal,
        this_support_dynamic_type,
        no_auto_likes,
        needs_concrete,
    } = genv;
    let mut l = vec![
        ("readonly".to_string(), bool_as_value(*readonly)),
        ("return".to_string(), return_info_as_value(env, return_)),
        ("callable_pos".to_string(), pos_as_value(callable_pos)),
        ("function_pos".to_string(), pos_as_value(function_pos)),
        (
            "params".to_string(),
            local_id_map_as_value(|p| param_as_value(env, p), params),
        ),
        ("static".to_string(), bool_as_value(*static_)),
        (
            "val_kind".to_string(),
            string_as_value(val_kind_to_string(val_kind)),
        ),
        (
            "fun_kind".to_string(),
            string_as_value(fun_kind_to_string(fun_kind)),
        ),
        ("fun_is_ctor".to_string(), bool_as_value(*fun_is_ctor)),
        ("this_internal".to_string(), bool_as_value(*this_internal)),
        (
            "this_support_dynamic_type".to_string(),
            bool_as_value(*this_support_dynamic_type),
        ),
        ("no_auto_likes".to_string(), bool_as_value(*no_auto_likes)),
        ("needs_concrete".to_string(), bool_as_value(*needs_concrete)),
    ];
    l.extend(match current_module {
        Some(current_module) => vec![(
            "current_module".to_string(),
            string_as_value(crate::ast_defs::show_id(current_module)),
        )],
        None => vec![],
    });
    l.extend(match current_package {
        Some(
            aast::PackageMembership::PackageConfigAssignment(pkg)
            | aast::PackageMembership::PackageOverride(_, pkg),
        ) => vec![("current_package".to_string(), string_as_value(pkg.clone()))],
        None => vec![],
    });
    l.extend(match soft_package_requirement {
        Some(soft_package_requirement) => vec![(
            "soft_package_requirement".to_string(),
            string_as_value(crate::ast_defs::show_id(soft_package_requirement)),
        )],
        None => vec![],
    });
    l.extend(match parent {
        Some((parent_id, parent_ty)) => vec![
            ("parent_id".to_string(), string_as_value(parent_id.clone())),
            ("parent_ty".to_string(), decl_type_as_value(env, parent_ty)),
        ],
        None => vec![],
    });
    l.extend(match self_ {
        Some((self_id, self_ty)) => vec![
            ("self_id".to_string(), string_as_value(self_id.clone())),
            ("self_ty".to_string(), type_as_value(env, self_ty)),
        ],
        None => vec![],
    });
    make_map(l)
}

fn fun_tast_info_as_map(r: Option<&tast::FunTastInfo>) -> Value {
    match r {
        None => make_map(vec![]),
        Some(r) => {
            let tast::FunTastInfo {
                has_implicit_return,
                has_readonly,
                dynamic_locals: _,
            } = r;
            make_map(vec![
                (
                    "has_implicit_return".to_string(),
                    bool_as_value(*has_implicit_return),
                ),
                ("has_readonly".to_string(), bool_as_value(*has_readonly)),
            ])
        }
    }
}

fn checked_as_value(check_status: &tast::CheckStatus) -> Value {
    Value::Atom(crate::aast_defs::show_check_status(check_status))
}

fn in_expr_tree_as_value(env: &Env, in_expr_tree: Option<&ExprTreeEnv>) -> Value {
    match in_expr_tree {
        None => bool_as_value(false),
        Some(ExprTreeEnv {
            dsl: cls,
            outer_locals,
        }) => make_map(vec![
            (
                "dsl".to_string(),
                Value::Atom(crate::aast_defs::show_class_name(cls)),
            ),
            (
                "outer_locals".to_string(),
                local_id_map_as_value(|local| local_as_value(env, local), outer_locals),
            ),
        ]),
    }
}

fn in_macro_splice_as_value(env: &Env, in_macro_splice: Option<&typing_local_types::T>) -> Value {
    match in_macro_splice {
        None => bool_as_value(false),
        Some(macro_vars) => make_map(vec![(
            "macro_vars".to_string(),
            local_id_map_as_value(|local| local_as_value(env, local), macro_vars),
        )]),
    }
}

fn env_as_value(env: &Env) -> Value {
    let crate::typing_env_types::EnvData {
        expression_id_provider: _,
        tvar_id_provider: _,
        lenv,
        in_loop,
        in_try,
        in_lambda,
        checked,
        tpenv,
        allow_wildcards,
        inference_env,
        rank,
        emit_string_coercion_error: _,
        check_rank: _,
        cold,
    } = &**env;
    let crate::typing_env_types::EnvCold {
        fresh_typarams,
        genv,
        decl_env: _,
        tracing_info: _,
        in_expr_tree,
        in_macro_splice,
        log_levels: _,
        big_envs: _,
        fun_tast_info,
    } = &**cold;
    let inside_constructor = env.genv.fun_is_ctor;
    make_map(vec![
        (
            "fresh_typarams".to_string(),
            Value::Set(fresh_typarams.iter().cloned().collect()),
        ),
        ("lenv".to_string(), lenv_as_value(env, lenv)),
        ("genv".to_string(), genv_as_value(env, genv)),
        ("in_loop".to_string(), bool_as_value(*in_loop)),
        ("in_try".to_string(), bool_as_value(*in_try)),
        ("in_lambda".to_string(), bool_as_value(*in_lambda)),
        (
            "in_expr_tree".to_string(),
            in_expr_tree_as_value(env, in_expr_tree.as_ref()),
        ),
        (
            "in_macro_splice".to_string(),
            in_macro_splice_as_value(env, in_macro_splice.as_ref()),
        ),
        (
            "inside_constructor".to_string(),
            bool_as_value(inside_constructor),
        ),
        ("checked".to_string(), checked_as_value(checked)),
        ("tpenv".to_string(), tpenv_as_value(env, tpenv)),
        ("allow_wildcards".to_string(), bool_as_value(*allow_wildcards)),
        (
            "inference_env".to_string(),
            inf::log::inference_env_as_value(inference_env),
        ),
        ("rank".to_string(), string_as_value(rank.to_string())),
        (
            "fun_tast_info".to_string(),
            fun_tast_info_as_map(fun_tast_info.as_ref()),
        ),
    ])
}

/// `function_name` is the OCaml's `?function_name`.
pub fn log_env_diff(p: &Pos, function_name: Option<&str>, old_env: &Env, new_env: &Env) {
    let value = env_as_value(new_env);
    let old_value = env_as_value(old_env);
    let d = compute_value_delta(&old_value, &value);
    match d {
        Delta::Unchanged => (),
        _ => log_position(p, function_name, || log_delta(new_env, &d)),
    }
}

/// Log the environment: local_types, subst, tenv and tpenv
pub fn hh_show_env(function_name: Option<&str>, p: &Pos, env: &Env) {
    log_with_level(env, "show", 0, || {
        let old_env = lastenv_get();
        LASTENV.with(|e| *e.borrow_mut() = Some(env.clone()));
        log_env_diff(p, function_name, &old_env, env)
    })
}

pub fn hh_show_full_env(p: &Pos, env: &Env) {
    log_with_level(env, "show", 0, || {
        let mut empty_env = env.clone();
        empty_env.inference_env = inf::empty_inference_env();
        log_env_diff(p, None, &empty_env, env)
    })
}

/// Log the type of an expression
pub fn hh_show(p: &Pos, env: &Env, ty: &Ty) {
    log_with_level(env, "show", 0, || {
        let s1 = pr::full_strip_ns(typing_env_types::get_log_level(env, "show") == 0, env, ty);
        let s2 = pr::constraints_for_type(false, env, ty);
        log_position(p, None, || {
            lprintf(Style::Normal(Green), s1);
            if s2 != "" {
                lprintf(Style::Normal(Green), format!(" {}", s2))
            }
            lnewline()
        })
    })
}

/// Simple type of possible log data
#[derive(Clone, Debug)]
pub enum LogStructure {
    LogHead(String, Vec<LogStructure>),
    LogType(String, Ty),
    LogDeclType(String, DeclTy),
    LogTypeI(String, InternalType),
}

fn print_key_value((key, value): (&str, &str)) {
    lprintf(Style::Bold(Green), format!("{}: ", key));
    lprintf(Style::Normal(Green), value.to_string());
    lnewline()
}

/// Logs a log_structure, which itself is a way to specify how to log types.
pub fn log_types(p: &PosOrDecl, env: &Env, items: &[LogStructure]) {
    log_pos_or_decl(p, None, || {
        fn go(env: &Env, items: &[LogStructure]) {
            for item in items {
                match item {
                    LogStructure::LogHead(message, items) => {
                        indent_env(Some(Style::Normal(Yellow)), message, || go(env, items))
                    }
                    LogStructure::LogType(message, ty) => {
                        print_key_value((message, &pr::debug(env, ty)))
                    }
                    LogStructure::LogDeclType(message, ty) => print_key_value((
                        message,
                        &pr::debug_decl(env, &ty.clone().to_oxidized()),
                    )),
                    LogStructure::LogTypeI(message, ty) => {
                        print_key_value((message, &pr::debug_i(env, ty)))
                    }
                }
            }
        }
        go(env, items)
    })
}

/// [`log_function`]`(pos, function_name, arguments, result, f)`
/// write to output something like
///
/// ```text
/// File "file.php", line 16, characters 10-13:[4]
///   <function_name>
///     <arg1>: <value1>
///     <arg2>: <value2>
///       <any logging produced by f, indented>
///     <function_name result>: <result>
/// ```
pub fn log_function<A>(
    p: &PosOrDecl,
    function_name: &str,
    arguments: &[(String, String)],
    result: impl FnOnce(&A) -> Option<String>,
    f: impl FnOnce() -> A,
) -> A {
    log_pos_or_decl(p, None, || {
        indent_env(Some(Style::Normal(Yellow)), function_name, || {
            for (key, value) in arguments {
                print_key_value((key, value))
            }
            let res = with_indent(f);
            match result(&res) {
                None => (),
                Some(res) => print_key_value((&format!("{} result", function_name), &res)),
            }
            res
        })
    })
}

/// `level` defaults to 1.
pub fn log_escape(level: Option<isize>, p: &PosOrDecl, env: &Env, msg: &str, vars: &[String]) {
    let level = level.unwrap_or(1);
    log_with_level(env, "escape", level, || {
        log_pos_or_decl(p, None, || {
            indent_env(Some(Style::Normal(Yellow)), msg, || ());
            if !vars.is_empty() {
                lnewline();
                for var in vars {
                    lprintf(Style::Normal(Green), format!("{} ", var))
                }
            }
        })
    })
}

pub fn log_prop(level: isize, p: &PosOrDecl, message: &str, env: &Env, prop: &SubtypeProp) {
    log_with_level(env, "prop", level, || {
        log_pos_or_decl(p, None, || log_subtype_prop(env, message, prop))
    })
}

fn log_new_tvar(env: &Env, p: &Pos, tvar: &Ty, message: String) {
    log_with_level(env, "prop", 2, || {
        log_types(
            &crate::pos_or_decl::of_raw_pos(p.clone()),
            env,
            &[LogStructure::LogHead(
                message,
                vec![LogStructure::LogType(
                    "type variable".to_string(),
                    tvar.clone(),
                )],
            )],
        )
    })
}

pub fn log_tparam_instantiation(env: &Env, p: &Pos, tparam_name: &str, tvar: &Ty) {
    let message = format!("Instantiating type parameter {} with", tparam_name);
    log_new_tvar(env, p, tvar, message)
}

/// `cname` is `'a * string`; `tparam` is the `'b Typing_defs.tparam` of the
/// one caller (`Typing.new_object`), a declared type parameter.
pub fn log_new_tvar_for_new_object<A>(
    env: &Env,
    p: &Pos,
    tvar: &Ty,
    cname: &(A, String),
    tparam: &DeclTparam,
) {
    let message = format!(
        "Creating new type var for type parameter {} while instantiating object {}",
        tparam.name.id().as_str(),
        cname.1
    );
    log_new_tvar(env, p, tvar, message)
}

pub fn log_new_tvar_for_tconst(
    env: &Env,
    (p, tvar): (&Pos, tvid::T),
    (_p, tconstid): &PosId,
    tvar_for_tconst: &Ty,
) {
    let message = format!(
        "Creating new type var for #{}::{}",
        tvid::show(tvar),
        tconstid
    );
    log_new_tvar(env, p, tvar_for_tconst, message)
}

pub fn log_new_tvar_for_tconst_access(
    env: &Env,
    p: &Pos,
    tvar: &Ty,
    class_name: &str,
    (_p, tconst): &PosId,
) {
    let message = format!(
        "Creating type var with the same constraints as {}::{}",
        class_name, tconst
    );
    log_new_tvar(env, p, tvar, message)
}

/// OCaml's `(env, result_ty)` argument and result: the environment is only
/// read, and the type is returned.
pub fn log_type_access(
    level: isize,
    root: &Ty,
    (p, type_const_name): &PosId,
    (env, result_ty): (&Env, Ty),
) -> Ty {
    log_with_level(env, "tyconst", level, || {
        log_types(
            p,
            env,
            &[LogStructure::LogHead(
                "Accessing type constant ".to_string() + type_const_name + " of",
                vec![
                    LogStructure::LogType("type".to_string(), root.clone()),
                    LogStructure::LogType("result".to_string(), result_ty.clone()),
                ],
            )],
        )
    });
    result_ty
}

/// `level` defaults to 1.
fn log_pessimise_(level: Option<isize>, env: &Env, kind: &str, pos: &PosOrDecl, name: &str) {
    let level = level.unwrap_or(1);
    let log_level = typing_env_types::get_log_level(env, "pessimise");
    if log_level >= level {
        let p = crate::pos_or_decl::unsafe_to_raw_pos(pos.clone());
        let (file, line) = {
            let p = crate::pos::to_absolute(&p);
            (crate::pos::filename(&p), crate::pos::line(&p))
        };
        if log_level > 1 {
            hh_logger::log(&format!("pessimise:\t{},{},{},{}", kind, file, line, name))
        } else {
            lnewline();
            lprintf(
                Style::Normal(Yellow),
                format!("pessimise:\t{},{},{},{}", kind, file, line, name),
            );
            lnewline()
        }
    }
}

pub fn log_pessimise_prop(env: &Env, pos: &Pos, prop_name: &str) {
    log_pessimise_(
        None,
        env,
        "prop",
        &crate::pos_or_decl::of_raw_pos(pos.clone()),
        &("$".to_string() + prop_name),
    )
}

pub fn log_pessimise_param(
    env: &Env,
    is_promoted_property: bool,
    pos: &Pos,
    mode: &ast_defs::ParamKind,
    param_name: &str,
) {
    if is_promoted_property
        || (match mode {
            ast_defs::ParamKind::Pinout(_) => true,
            _ => false,
        })
        || typing_env_types::get_log_level(env, "pessimise.params") >= 1
    {
        log_pessimise_(
            None,
            env,
            if is_promoted_property {
                "prop"
            } else {
                "param"
            },
            &crate::pos_or_decl::of_raw_pos(pos.clone()),
            param_name,
        )
    }
}

pub fn log_pessimise_return(level: Option<isize>, env: &Env, pos: &Pos, opt_bound: Option<&str>) {
    log_pessimise_(
        level,
        env,
        "ret",
        &crate::pos_or_decl::of_raw_pos(pos.clone()),
        opt_bound.unwrap_or(""),
    )
}

pub fn log_pessimise_poisoned_return(level: Option<isize>, env: &Env, pos: &Pos, member: &str) {
    log_pessimise_(
        level,
        env,
        "ret",
        &crate::pos_or_decl::of_raw_pos(pos.clone()),
        &("^".to_string() + member),
    )
}

/// `level` defaults to 1.
pub fn log_sd_pass(level: Option<isize>, env: &Env, pos: &Pos) {
    let level = level.unwrap_or(1);
    log_with_level(env, "sd_pass", level, || {
        let (file, line) = {
            let p = crate::pos::to_absolute(pos);
            (crate::pos::filename(&p), crate::pos::line(&p))
        };
        lnewline();
        lprintf(
            Style::Normal(Yellow),
            format!("sound dynamic pass:\t{},{}", file, line),
        );
        lnewline()
    })
}

pub fn increment_feature_count(env: &Env, s: &str) {
    if env.genv.tcopt.tco_language_feature_logging {
        measure::sample(None, None, s, 1.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// What is written to [`OUT_CHANNEL`] while `f` runs.
    fn logged(f: impl FnOnce()) -> String {
        #[derive(Clone)]
        struct Shared(std::rc::Rc<RefCell<Vec<u8>>>);
        impl std::io::Write for Shared {
            fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
                self.0.borrow_mut().extend_from_slice(buf);
                Ok(buf.len())
            }
            fn flush(&mut self) -> std::io::Result<()> {
                Ok(())
            }
        }
        let buf = Shared(std::rc::Rc::new(RefCell::new(vec![])));
        let previous = OUT_CHANNEL.with(|oc| oc.replace(Box::new(buf.clone())));
        f();
        OUT_CHANNEL.with(|oc| oc.replace(previous));
        String::from_utf8(buf.0.borrow().clone()).unwrap()
    }

    #[test]
    fn lines_and_indentation() {
        // (Colors are applied only when stdout is a terminal, or when
        // FORCE_ERROR_COLOR is set.)
        if tty::should_color(ColorMode::ColorAuto) {
            return;
        }
        assert_eq!(
            logged(|| {
                indent_env(None, "header", || {
                    log_key("key");
                    lprintf(Style::Normal(Green), " value".to_string());
                    lnewline();
                    with_indent(|| print_key_value(("k", "v")))
                })
            }),
            "header\n  key value\n    k: v\n"
        );
        // A line is printed as soon as it is longer than 80.
        let long = "x".repeat(50);
        assert_eq!(
            logged(|| {
                lprintf(Style::Normal(Green), long.clone());
                lprintf(Style::Normal(Green), long.clone());
                lprintf(Style::Normal(Green), "y".to_string());
                lnewline();
            }),
            format!("{0}{0}\ny\n", long)
        );
        // An empty buffer prints nothing.
        assert_eq!(logged(lnewline), "");
    }

    #[test]
    fn sets_and_values() {
        if tty::should_color(ColorMode::ColorAuto) {
            return;
        }
        let set: s_set::T = ["b".to_string(), "a".to_string()].into_iter().collect();
        assert_eq!(
            logged(|| {
                log_sset(&set);
                lnewline()
            }),
            "{a,b}\n"
        );
        assert_eq!(
            logged(|| {
                log_sset(&s_set::T::new());
                log_sset(&["c".to_string()].into_iter().collect());
                lnewline()
            }),
            "{}{c}\n"
        );
    }

    #[test]
    fn deltas() {
        let atom = |s: &str| Value::Atom(s.to_string());
        let old = make_map(vec![
            ("a".to_string(), atom("1")),
            ("b".to_string(), atom("2")),
            (
                "s".to_string(),
                Value::Set(["x".to_string()].into_iter().collect()),
            ),
        ]);
        let new = make_map(vec![
            ("a".to_string(), atom("1")),
            ("c".to_string(), atom("3")),
            (
                "s".to_string(),
                Value::Set(["y".to_string()].into_iter().collect()),
            ),
        ]);
        match compute_value_delta(&old, &new) {
            Delta::MapDelta {
                added,
                removed,
                changed,
            } => {
                assert_eq!(added.keys().cloned().collect::<Vec<_>>(), vec!["c"]);
                assert_eq!(removed.iter().cloned().collect::<Vec<_>>(), vec!["b"]);
                assert_eq!(changed.keys().cloned().collect::<Vec<_>>(), vec!["s"]);
                match changed.get("s") {
                    Some(Delta::SetDelta { added, removed }) => {
                        assert_eq!(added.iter().cloned().collect::<Vec<_>>(), vec!["y"]);
                        assert_eq!(removed.iter().cloned().collect::<Vec<_>>(), vec!["x"]);
                    }
                    _ => panic!("expected a set delta"),
                }
            }
            _ => panic!("expected a map delta"),
        }
        assert!(matches!(
            compute_value_delta(&old, &old),
            Delta::Unchanged
        ));
        assert!(matches!(
            compute_value_delta(&atom("1"), &Value::Bool(true)),
            Delta::Updated(Value::Bool(true))
        ));
    }
}
