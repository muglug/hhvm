// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `type_driven_code_health_logger.ml`. See `hh/PORTING.md`.

use std::sync::Arc;

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::aast_visitor::Visitor;
use oxidized::ast_defs::Id;
use oxidized::local_id::LocalId;
use oxidized::pos::Pos;

use crate::ctx::Ctx;
use crate::hh_logger;
use crate::local_id;
use crate::pos;
use crate::provider_context;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::mk;
use crate::typing_env;
use crate::typing_make_type as make_type;
use crate::typing_reason as reason;
use crate::typing_utils;
use crate::yojson::safe as yojson;

/// `catch` of a TAST.
type Catch = aast::Catch<tast::Ty, tast::SavedEnv>;

#[allow(non_camel_case_types)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    HH_FIXME,
    UNSAFE_CAST,
    PHPISM,
    EXPLICIT_DYNAMIC,
    TYPE_ASSERTION,
    UNSURFACED_EXCEPTION,
    ALWAYS_FALSE_ASSERTION,
    ALWAYS_FALSE_TYPE_TEST,
}

/// `[@@deriving show { with_path = false }]`
pub fn show_kind(kind: Kind) -> String {
    match kind {
        Kind::HH_FIXME => "HH_FIXME",
        Kind::UNSAFE_CAST => "UNSAFE_CAST",
        Kind::PHPISM => "PHPISM",
        Kind::EXPLICIT_DYNAMIC => "EXPLICIT_DYNAMIC",
        Kind::TYPE_ASSERTION => "TYPE_ASSERTION",
        Kind::UNSURFACED_EXCEPTION => "UNSURFACED_EXCEPTION",
        Kind::ALWAYS_FALSE_ASSERTION => "ALWAYS_FALSE_ASSERTION",
        Kind::ALWAYS_FALSE_TYPE_TEST => "ALWAYS_FALSE_TYPE_TEST",
    }
    .to_string()
}

pub fn find_level(kind: Kind) -> isize {
    match kind {
        Kind::HH_FIXME
        | Kind::UNSAFE_CAST
        | Kind::PHPISM
        | Kind::EXPLICIT_DYNAMIC
        | Kind::TYPE_ASSERTION => 1,
        Kind::UNSURFACED_EXCEPTION
        | Kind::ALWAYS_FALSE_ASSERTION
        | Kind::ALWAYS_FALSE_TYPE_TEST => 2,
    }
}

#[allow(non_upper_case_globals)]
pub const nPHPism_FIXME: &str = "\\PHPism_FIXME";

pub fn log(level: isize, pos: &Pos, kind: Kind) {
    if find_level(kind) <= level {
        let json = yojson::T::Assoc(vec![
            ("kind".to_string(), yojson::T::String(show_kind(kind))),
            (
                "pos".to_string(),
                pos::multiline_json(&pos::to_relative_string(pos)),
            ),
        ]);
        // unsorted: telemetry/logging, not snapshot-tested
        hh_logger::log(&format!("[TDCH] {}", yojson::to_string(&json)))
    }
}

pub fn nothing_ty() -> Ty {
    make_type::nothing(reason::none())
}

pub fn replace_placeholders_with_tvars(env: &mut Env, ty: Ty) -> Ty {
    let replace_placeholder = |env: &mut Env, ty: &Ty| match get_node(ty) {
        Ty_::Tgeneric(name) if name.contains('#') => typing_env::fresh_type(env, Pos::NONE),
        _ => ty.clone(),
    };
    match get_node(&ty) {
        Ty_::Tclass(id, exact, targs) => {
            let targs = targs
                .iter()
                .map(|ty| replace_placeholder(env, ty))
                .collect();
            mk((reason::none(), Ty_::Tclass(id.clone(), exact.clone(), targs)))
        }
        _ => ty,
    }
}

pub fn always_false(level: isize, pos: &Pos, kind: Kind, env: &Env, lhs_ty: Ty, rhs_ty: Ty) {
    let mut env = env.clone();
    let lhs_ty = tast_env::expand_type(&mut env, lhs_ty);
    let rhs_ty = tast_env::expand_type(&mut env, rhs_ty);
    let lhs_ty = tast_env::strip_dynamic(&env, lhs_ty);
    let rhs_ty = tast_env::strip_dynamic(&env, rhs_ty);
    let mut env_with_tyvars = env.clone();
    typing_env::open_tyvars(&mut env_with_tyvars, Pos::NONE);
    let rhs_ty = replace_placeholders_with_tvars(&mut env_with_tyvars, rhs_ty);
    if tast_env::is_sub_type(&env, &lhs_ty, &nothing_ty()) {
        // If we have a nothing in our hands, there was a bigger problem
        // originating from earlier in the program. Don't flag it here, as it is
        // merely a symptom.
    } else {
        let lhs_ty = tast_env::expand_type(&mut env, lhs_ty);
        let rhs_ty = tast_env::expand_type(&mut env.clone(), rhs_ty);
        if typing_utils::is_type_disjoint(&env_with_tyvars, &lhs_ty, &rhs_ty) {
            log(level, pos, kind)
        }
    }
}

pub fn is_toplevelish_dynamic(env: &Env, (ty, hint_opt): (&Ty, &Option<aast::Hint>)) -> Option<Pos> {
    match hint_opt {
        Some(aast::Hint(pos, _)) => {
            fn is_toplevelish_dynamic(env: &Env, ty: &Ty) -> bool {
                let ty = tast_env::expand_type(&mut env.clone(), ty.clone());
                let ty = tast_env::strip_dynamic(env, ty);
                let ty = tast_env::expand_type(&mut env.clone(), ty);
                match get_node(&ty) {
                    Ty_::Tdynamic(_) => true,
                    Ty_::Toption(ty) => is_toplevelish_dynamic(env, ty),
                    Ty_::Tclass((_, id), _, tys) if tys.len() == 1 && id == sn::classes::AWAITABLE => {
                        is_toplevelish_dynamic(env, &tys[0])
                    }
                    Ty_::Tclass((_, id), _, tys)
                        if tys.len() == 1
                            && [sn::collections::VEC, sn::collections::VECTOR]
                                .contains(&id.as_str()) =>
                    {
                        is_toplevelish_dynamic(env, &tys[0])
                    }
                    Ty_::Tclass((_, id), _, tys)
                        if tys.len() == 2
                            && [sn::collections::DICT, sn::collections::MAP]
                                .contains(&id.as_str()) =>
                    {
                        is_toplevelish_dynamic(env, &tys[1])
                    }
                    _ => false,
                }
            }
            if is_toplevelish_dynamic(env, ty) {
                Some(pos.clone())
            } else {
                None
            }
        }
        _ => None,
    }
}

pub fn log_explicit_dynamic(level: isize, env: &Env, hint: &tast::TypeHint) {
    let aast::TypeHint(ty, hint_opt) = hint;
    match is_toplevelish_dynamic(env, (ty, hint_opt)) {
        Some(pos) => log(level, &pos, Kind::EXPLICIT_DYNAMIC),
        None => {}
    }
}

pub fn log_callable_def(level: isize, env: &Env, ret: &tast::TypeHint, params: &[tast::FunParam]) {
    log_explicit_dynamic(level, env, ret);
    for param in params {
        log_explicit_dynamic(level, env, &param.type_hint)
    }
}

#[allow(non_upper_case_globals)]
pub const generic_exceptions: &[&str] = &[
    "\\Exception",
    "\\ViolationException",
    "\\InvariantViolationException",
    "\\InvalidOperationException",
    "\\RuntimeException",
];

pub fn references(bl: &tast::Block, binding: &LocalId) -> bool {
    /// The object `references` (it inherits `Aast.reduce`, with `zero` false
    /// and `plus` `||`): whether some `lid` is `binding`.
    struct References<'b> {
        binding: &'b LocalId,
        acc: bool,
    }

    impl<'a, 'b> Visitor<'a> for References<'b> {
        type Params = tast_visitor::Params<()>;

        fn object(&mut self) -> &mut dyn Visitor<'a, Params = Self::Params> {
            self
        }

        fn visit_lid(&mut self, _env: &mut (), lid: &'a aast::Lid) -> tast_visitor::Res {
            let aast::Lid(_, lid) = lid;
            self.acc = self.acc || local_id::equal(self.binding, lid);
            Ok(())
        }
    }

    let mut references = References {
        binding,
        acc: false,
    };
    let _ = references.visit_block(&mut (), bl);
    references.acc
}

pub fn log_on_unsurfaced_exception(level: isize, catch: &Catch) {
    let aast::Catch(Id(_, exn), aast::Lid(pos, exn_binding), bl) = catch;
    let is_placeholder =
        |lid: &LocalId| local_id::get_name(lid) == sn::special_idents::PLACEHOLDER;
    if generic_exceptions
        .iter()
        .any(|generic_exn| exn.ends_with(generic_exn))
        && (is_placeholder(exn_binding) || !references(bl, exn_binding))
    {
        log(level, pos, Kind::UNSURFACED_EXCEPTION)
    }
}

struct Handler {
    level: isize,
}

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_fun_(&mut self, env: &Env, f: &'a tast::Fun_) {
        log_callable_def(self.level, env, &f.ret, &f.params)
    }

    fn at_method_(&mut self, env: &Env, m: &'a tast::Method_) {
        log_callable_def(self.level, env, &m.ret, &m.params)
    }

    fn at_expr(&mut self, env: &Env, e: &'a tast::Expr) {
        let level = self.level;
        let aast::Expr(_, pos, expr) = e;
        let log = |kind| log(level, pos, kind);
        match expr {
            aast::Expr_::Hole(hole) => {
                let (_, _, _, kind) = &**hole;
                match kind {
                    aast::HoleSource::Typing => log(Kind::HH_FIXME),
                    aast::HoleSource::UnsafeCast(_) => log(Kind::UNSAFE_CAST),
                    aast::HoleSource::UnsafeNonnullCast => log(Kind::UNSAFE_CAST),
                    _ => {}
                }
            }
            aast::Expr_::As(as_) if !as_.is_nullable => {
                let aast::As_ {
                    expr: aast::Expr(lhs_ty, _, _),
                    hint,
                    is_nullable: _,
                    enforce_deep: _,
                } = &**as_;
                log(Kind::TYPE_ASSERTION);
                let mut env = env.clone();
                let hint_ty = tast_env::localize_hint_for_refinement(&mut env, hint);
                always_false(
                    level,
                    pos,
                    Kind::ALWAYS_FALSE_ASSERTION,
                    &env,
                    lhs_ty.clone(),
                    hint_ty,
                )
            }
            aast::Expr_::Is(is) => {
                let (aast::Expr(lhs_ty, _, _), hint) = &**is;
                let mut env = env.clone();
                let hint_ty = tast_env::localize_hint_for_refinement(&mut env, hint);
                always_false(
                    level,
                    pos,
                    Kind::ALWAYS_FALSE_TYPE_TEST,
                    &env,
                    lhs_ty.clone(),
                    hint_ty,
                )
            }
            aast::Expr_::Call(call)
                if matches!(
                    &call.func,
                    aast::Expr(_, _, aast::Expr_::ClassConst(cc))
                        if matches!(&cc.0, aast::ClassId(_, _, aast::ClassId_::CI(Id(_, cid))) if cid == nPHPism_FIXME)
                ) =>
            {
                log(Kind::PHPISM)
            }
            _ => {}
        }
    }

    fn at_stmt(&mut self, _env: &Env, s: &'a tast::Stmt) {
        let aast::Stmt(_, stmt) = s;
        match stmt {
            aast::Stmt_::Try(try_) => {
                let (_, catch_list, _) = &**try_;
                for catch in catch_list {
                    log_on_unsurfaced_exception(self.level, catch)
                }
            }
            _ => {}
        }
    }
}

pub fn create_handler<'a>(ctx: &Arc<Ctx>) -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    let level = provider_context::get_tcopt(ctx)
        .log_levels
        .get("type_driven_code_health")
        .copied()
        .unwrap_or(1);
    Box::new(Handler { level })
}
