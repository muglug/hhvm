// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_local_ops.ml`. See `hh/PORTING.md`.
//!
//! The error callbacks (`mk_err_opt`) see the environment that the OCaml
//! closes them over, which is the one before `mk_required` runs: they are
//! given a copy of it.

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::ast_defs::Uop;
use oxidized::error_codes::Typing as ErrorCode;
use oxidized::message::Message;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;

use crate::aast_utils;
use crate::tast;
use crate::typing_coeffects;
use crate::typing_defs;
use crate::typing_defs_core::ShapeType;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::get_node;
/// `module Env = Typing_env`
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::Lazy;
use crate::typing_error_utils;
use crate::typing_local_types::Local;
use crate::typing_reason as reason;
use crate::typing_subtype;
use crate::typing_utils;

/// `SN.Classes.cString` (`naming_special_names_rust` has it as
/// `typehints::HH_STRING` only).
const C_STRING: &str = sn::typehints::HH_STRING;

fn check_local_capability(
    mk_required: impl FnOnce(&mut Env) -> Ty,
    mk_err_opt: impl FnOnce(&Local, &Ty) -> Option<typing_error::T>,
    env: &mut Env,
) {
    // gate the check behavior on coeffects TC option
    let tcopt = env::get_tcopt(env);
    // `Typechecker_options.local_coeffects`
    let should_skip_check =
        !tcopt.tco_coeffects_local || tast::is_under_dynamic_assumptions(env.checked);
    if !should_skip_check {
        let available = env::get_local(env, &typing_coeffects::local_capability_id());
        let required = mk_required(env);
        let err_opt = mk_err_opt(&available, &required);
        let ty_err_opt = typing_subtype::sub_type_or_fail(env, available.ty, required, err_opt);
        if let Some(ty_err) = &ty_err_opt {
            typing_error_utils::add_typing_error(ty_err, env)
        }
    } else {
    }
}

fn enforce_local_capability(
    // Run-time enforced ops must have the default as it's unfixmeable
    err_code: Option<ErrorCode>,
    suggestion: Option<Lazy<Vec<Message<PosOrDecl>>>>,
    mk_required: impl FnOnce(&mut Env) -> Ty,
    op: &str,
    op_pos: Pos,
    env: &mut Env,
) {
    let err_code = err_code.unwrap_or(ErrorCode::OpCoeffects);
    let env0 = env.clone();
    check_local_capability(
        mk_required,
        |available, required| {
            Some(typing_error::coeffect(
                typing_error::primary::coeffect::T::Op_coeffect_error {
                    pos: op_pos,
                    op_name: op.to_string(),
                    locally_available: typing_coeffects::pretty(&env0, &available.ty),
                    available_pos: typing_defs::get_pos(&available.ty),
                    required: typing_coeffects::pretty(&env0, required),
                    err_code,
                    suggestion,
                },
            ))
        },
        env,
    )
}

/// `module Capabilities` (not exported by the `.mli`; the names of
/// `include SN.Capabilities` are all here, used or not).
#[allow(non_upper_case_globals, dead_code)]
mod capabilities {
    use pos::Positioned;
    use pos::TypeName;
    use ty::reason::Reason as _;

    use crate::ctx::R;
    use crate::typing_defs_core::Ty;
    use crate::typing_env_types::Env;
    use crate::typing_error_utils;
    use crate::typing_make_type;
    use crate::typing_phase;

    // `include SN.Capabilities` (missing from `naming_special_names_rust`)

    pub const defaults: &str = "\\HH\\Contexts\\defaults";

    pub const write_props: &str = "\\HH\\Contexts\\write_props";

    pub const prefix: &str = "\\HH\\Capabilities\\";

    pub const writeProperty: &str = "\\HH\\Capabilities\\WriteProperty";

    pub const accessGlobals: &str = "\\HH\\Capabilities\\AccessGlobals";

    pub const readGlobals: &str = "\\HH\\Capabilities\\ReadGlobals";

    pub const systemLocal: &str = "\\HH\\Capabilities\\SystemLocal";

    pub const implicitPolicy: &str = "\\HH\\Capabilities\\ImplicitPolicy";

    pub const implicitPolicyLocal: &str = "\\HH\\Capabilities\\ImplicitPolicyLocal";

    pub const io: &str = "\\HH\\Capabilities\\IO";

    pub const rx: &str = "\\HH\\Capabilities\\Rx";

    pub const rxLocal: &str = "\\HH\\Capabilities\\RxLocal";

    thread_local! {
        /// The declared types of `mk`, by name: building one hash-conses it in
        /// the table that all the threads share, at every assignment.
        static DECL_TYS: std::cell::RefCell<hash::HashMap<String, crate::typing_defs_core::DeclTy>> =
            Default::default();
    }

    pub fn mk(special_name: &str, env: &mut Env) -> Ty {
        // `MakeType.apply Reason.none (Reason.to_pos r, special_name) []`, a
        // value that only depends on `special_name`.
        let decl_ty = DECL_TYS.with_borrow_mut(|tys| {
            if let Some(ty) = tys.get(special_name) {
                return ty.clone();
            }
            // `Reason.none`, of the declared phase
            let r = R::none();
            let id = Positioned::new(r.pos().clone(), TypeName::new(special_name));
            let ty = typing_make_type::apply(r, id, vec![]);
            tys.insert(special_name.to_string(), ty.clone());
            ty
        });
        let (ty_err_opt, res) = typing_phase::localize_no_subst(env, true, &decl_ty);
        if let Some(ty_err) = &ty_err_opt {
            typing_error_utils::add_typing_error(ty_err, env)
        }
        res
    }

    #[cfg(test)]
    mod tests {
        /// The values of `Naming_special_names.Capabilities`.
        #[test]
        fn same_names_as_ocaml() {
            let ml = include_str!("../../naming/naming_special_names.ml");
            let start = ml.find("\nmodule Capabilities = struct").unwrap();
            let ml = &ml[start..];
            let ml = &ml[..ml.find("\nend").unwrap()];
            assert!(ml.contains("let defaults = Coeffects.contexts ^ \"\\\\defaults\""));
            assert!(ml.contains("let write_props = Coeffects.contexts ^ \"\\\\write_props\""));
            assert!(ml.contains("let prefix = \"\\\\HH\\\\Capabilities\\\\\""));
            for (name, suffix, value) in [
                ("writeProperty", "WriteProperty", super::writeProperty),
                ("accessGlobals", "AccessGlobals", super::accessGlobals),
                ("readGlobals", "ReadGlobals", super::readGlobals),
                ("systemLocal", "SystemLocal", super::systemLocal),
                ("implicitPolicy", "ImplicitPolicy", super::implicitPolicy),
                ("implicitPolicyLocal", "ImplicitPolicyLocal", super::implicitPolicyLocal),
                ("io", "IO", super::io),
                ("rx", "Rx", super::rx),
            ] {
                assert!(
                    ml.contains(&format!("let {} = prefix ^ \"{}\"", name, suffix)),
                    "{}",
                    name
                );
                assert_eq!(value, format!("{}{}", super::prefix, suffix));
            }
            assert!(ml.contains("let rxLocal = rx ^ \"Local\""));
            assert_eq!(super::rxLocal, format!("{}Local", super::rx));
        }
    }
}

pub fn enforce_memoize_object(pos: Pos, env: &mut Env) {
    // Allow zoned_shallow/local policies to memoize objects,
    // since those will convert to PolicyShardedMemoize after conversion to zoned
    // We use ImplicitPolicy instead of ImplicitPolicyShallow just to not error
    // for zoned, since memoizing a zoned function already has a different error
    // associated with it.
    let zoned = capabilities::mk(capabilities::implicitPolicy, env);
    let access_globals = capabilities::mk(capabilities::accessGlobals, env);

    let mk_zoned_or_access_globals = |_env: &mut Env| {
        let r = reason::none();
        crate::typing_make_type::union(r, vec![zoned, access_globals.clone()])
    };
    let env0 = env.clone();
    check_local_capability(
        mk_zoned_or_access_globals,
        |available, _required| {
            Some(typing_error::coeffect(
                typing_error::primary::coeffect::T::Op_coeffect_error {
                    pos,
                    op_name: "Memoizing object parameters".to_string(),
                    locally_available: typing_coeffects::pretty(&env0, &available.ty),
                    available_pos: typing_defs::get_pos(&available.ty),
                    // Use access globals in error message
                    required: typing_coeffects::pretty(&env0, &access_globals),
                    // Temporarily FIXMEable error for memoizing objects. Once ~65 current cases are removed
                    // we can change this
                    err_code: ErrorCode::MemoizeObjectWithoutGlobals,
                    suggestion: None,
                },
            ))
        },
        env,
    )
}

pub fn enforce_io(op_pos: Pos, env: &mut Env) {
    enforce_local_capability(
        None,
        None,
        |env| capabilities::mk(capabilities::io, env),
        "`echo` or `print` builtin",
        op_pos,
        env,
    )
}

pub fn enforce_enum_class_variant(op_pos: Pos, env: &mut Env) {
    enforce_local_capability(
        None,
        None,
        |env| capabilities::mk(capabilities::writeProperty, env),
        "Accessing an enum class constant",
        op_pos,
        env,
    )
}

// basic local mutability checks
fn is_byval_collection_or_string_or_any_type(env: &Env, ty: &Ty) -> bool {
    let check = |ty: &Ty| {
        // The environment of `expand_type` is the one the recursive calls see.
        let mut env = env.clone();
        let ty = env::expand_type(&mut env, ty.clone());
        match get_node(&ty) {
            Ty_::Toption(inner) => is_byval_collection_or_string_or_any_type(&env, inner),
            Ty_::Tclass((_, x), _, _) => {
                x == sn::collections::VEC
                    || x == sn::collections::DICT
                    || x == sn::collections::KEYSET
                    || x == C_STRING
            }
            Ty_::TvecOrDict(_, _)
            | Ty_::Ttuple(_)
            | Ty_::Tshape(ShapeType::ShapeSimple(_) | ShapeType::ShapeSplat(_))
            | Ty_::Tdynamic(_)
            | Ty_::Tany(_) => true,
            Ty_::Tunion(tyl) => tyl
                .iter()
                .all(|ty| is_byval_collection_or_string_or_any_type(&env, ty)),
            Ty_::Tintersection(tyl) => tyl
                .iter()
                .any(|ty| is_byval_collection_or_string_or_any_type(&env, ty)),
            Ty_::Tgeneric(_) | Ty_::Tnewtype(_, _, _) | Ty_::Tdependent(_, _) => {
                // FIXME we should probably look at the upper bounds here.
                false
            }
            Ty_::Tnonnull
            | Ty_::Tprim(_)
            | Ty_::Tfun(_)
            | Ty_::Tvar(_)
            | Ty_::Taccess(_)
            | Ty_::Tlabel(_)
            | Ty_::Tneg(_)
            | Ty_::TclassPtr(_) => false,
        }
    };
    // The environment this returns is dropped.
    let tl = typing_utils::get_concrete_supertypes(
        None,
        None,
        None,
        true,
        &mut env.clone(),
        ty.clone(),
    );
    tl.iter().all(check)
}

fn mutating_this_in_ctor(env: &Env, aast::Expr(_, _, e): &tast::Expr) -> bool {
    match e {
        aast::Expr_::This if env::fun_is_constructor(env) => true,
        _ => false,
    }
}

fn is_valid_mutable_subscript_expression_target(env: &Env, v: &tast::Expr) -> bool {
    match v {
        aast::Expr(_, _, aast::Expr_::Hole(b)) => {
            let (e, _, _, _) = &**b;
            is_valid_mutable_subscript_expression_target(env, e)
        }
        aast::Expr(ty, _, aast::Expr_::Lvar(_)) => is_byval_collection_or_string_or_any_type(env, ty),
        aast::Expr(ty, _, aast::Expr_::ArrayGet(b)) => {
            let (e, _) = &**b;
            is_byval_collection_or_string_or_any_type(env, ty)
                && is_valid_mutable_subscript_expression_target(env, e)
        }
        aast::Expr(ty, _, aast::Expr_::ObjGet(b)) => {
            let (e, _, _, _) = &**b;
            is_byval_collection_or_string_or_any_type(env, ty)
                && (is_valid_mutable_subscript_expression_target(env, e)
                    || mutating_this_in_ctor(env, e))
        }
        aast::Expr(_, _, aast::Expr_::ReadonlyExpr(e)) => {
            is_valid_mutable_subscript_expression_target(env, e)
        }
        _ => false,
    }
}

fn is_valid_append_target(_env: &Env, ty: &Ty) -> bool {
    // TODO(coeffects) move this to typing.ml and completely redesign
    // the line below (as it was in Tast_check) doesn't do the right thing
    // let (_env, ty) = Env.expand_type _env ty in
    match get_node(ty) {
        Ty_::Tclass((_, n), _, tyl) if tyl.is_empty() => {
            n != sn::collections::VECTOR && n != sn::collections::SET && n != sn::collections::MAP
        }
        Ty_::Tclass((_, n), _, tyl) if tyl.len() == 1 => {
            n != sn::collections::VECTOR && n != sn::collections::SET
        }
        Ty_::Tclass((_, n), _, tyl) if tyl.len() == 2 => n != sn::collections::MAP,
        _ => true,
    }
}

fn check_assignment_or_unset_target(
    is_assignment: bool,
    append_pos_opt: Option<&Pos>,
    env: &Env,
    te1: &tast::Expr,
    capability_available: &Local,
    capability_required: &Ty,
) -> Option<typing_error::T> {
    let fail = |suggestion: Option<Lazy<Vec<Message<PosOrDecl>>>>, op_name: String, pos: Pos| {
        Some(typing_error::coeffect(
            typing_error::primary::coeffect::T::Op_coeffect_error {
                pos,
                op_name,
                suggestion,
                locally_available: typing_coeffects::pretty(env, &capability_available.ty),
                available_pos: typing_defs::get_pos(&capability_available.ty),
                required: typing_coeffects::pretty(env, capability_required),
                err_code: ErrorCode::OpCoeffects,
            },
        ))
    };
    let aast::Expr(_, p, expr_) = te1;
    match expr_ {
        aast::Expr_::Hole(b) => {
            let (e, _, _, _) = &**b;
            check_assignment_or_unset_target(
                is_assignment,
                append_pos_opt,
                env,
                e,
                capability_available,
                capability_required,
            )
        }
        aast::Expr_::ObjGet(b) if mutating_this_in_ctor(env, &b.0) => None,
        aast::Expr_::ArrayGet(b) if is_assignment && !is_valid_append_target(env, &(b.0).0) => {
            let (_, i) = &**b;
            let is_append = i.is_none();
            let msg_prefix = if is_append {
                "Appending to a Hack Collection object"
            } else {
                "Assigning to an element of a Hack Collection object via `[]`"
            };
            fail(
                None,
                msg_prefix.to_string(),
                append_pos_opt.unwrap_or(p).clone(),
            )
        }
        aast::Expr_::ArrayGet(b) if is_valid_mutable_subscript_expression_target(env, &b.0) => None,
        // we already report errors about statics in rx context, no need to do it twice
        aast::Expr_::ClassGet(_) => None,
        aast::Expr_::ObjGet(_) | aast::Expr_::ArrayGet(_) => {
            if is_assignment {
                fail(
                    None,
                    "This object's property is being mutated (used as an lvalue)".to_string()
                        + "\nSetting non-mutable object properties",
                    p.clone(),
                )
            } else {
                fail(None, "Non-mutable argument for `unset`".to_string(), p.clone())
            }
        }
        _ => None,
    }
}

// END logic from Typed AST check in basic_reactivity_check

pub fn check_assignment(env: &mut Env, te: &tast::Expr) {
    let aast::Expr(x, append_pos_opt, te_) = te;
    check_assignment_parts(env, x, append_pos_opt, te_)
}

/// `check_assignment env (x, append_pos_opt, te_)`, on the components of the
/// expression (the `Hole` case recurses with the same `x` and position).
fn check_assignment_parts(env: &mut Env, x: &Ty, append_pos_opt: &Pos, te_: &tast::Expr_) {
    let check = |env: &mut Env, te1: &tast::Expr| {
        let env0 = env.clone();
        check_local_capability(
            |env| capabilities::mk(capabilities::writeProperty, env),
            |available, required| {
                check_assignment_or_unset_target(
                    true,
                    Some(append_pos_opt),
                    &env0,
                    te1,
                    available,
                    required,
                )
            },
            env,
        )
    };
    match te_ {
        aast::Expr_::Hole(b) => {
            let (aast::Expr(_, _, e), _, _, _) = &**b;
            check_assignment_parts(env, x, append_pos_opt, e)
        }
        aast::Expr_::Unop(b) if matches!(b.0, Uop::Uincr | Uop::Udecr | Uop::Upincr | Uop::Updecr) => {
            let (_, te1) = &**b;
            check(env, te1)
        }
        aast::Expr_::Assign(b) => {
            let (te1, _, _) = &**b;
            check(env, te1)
        }
        _ => {}
    }
}

pub fn check_unset_target(env: &mut Env, tel: &[tast::Argument]) {
    for arg in tel {
        let env0 = env.clone();
        check_local_capability(
            |env| capabilities::mk(capabilities::writeProperty, env),
            |available, required| {
                check_assignment_or_unset_target(
                    false,
                    None,
                    &env0,
                    aast_utils::arg_to_expr(arg),
                    available,
                    required,
                )
            },
            env,
        )
    }
}
