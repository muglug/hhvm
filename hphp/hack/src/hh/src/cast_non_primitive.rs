// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/tast_check/cast_non_primitive.ml`. See `hh/PORTING.md`.

use oxidized::aast;
use oxidized::ast_defs::Tprim;

use crate::error_codes;
use crate::tast;
use crate::tast_env;
use crate::tast_visitor;
use crate::typing_defs as t;
use crate::typing_make_type as make_type;
use crate::typing_reason as reason;
use crate::typing_utils as t_utils;
use crate::typing_warning;
use crate::typing_warning_utils;

pub const WARNING_KIND: typing_warning::Kind<
    typing_warning::cast_non_primitive::T,
    typing_warning::Migrated,
> = typing_warning::Kind::CAST_NON_PRIMITIVE;

pub fn error_codes() -> Vec<error_codes::warning::T> {
    typing_warning_utils::codes(&WARNING_KIND)
}

pub fn is_always_castable(env: &tast_env::Env, ty: &t::Ty) -> bool {
    let r = reason::none();
    let castable_ty = make_type::locl_like(
        r.clone(),
        make_type::nullable(
            r.clone(),
            make_type::union(
                r.clone(),
                vec![
                    make_type::arraykey(r.clone()),
                    make_type::num(r.clone()),
                    make_type::bool(r),
                ],
            ),
        ),
    );
    tast_env::is_sub_type(env, ty, &castable_ty)
}

pub fn is_bool_castable(env: &tast_env::Env, ty: &t::Ty) -> bool {
    let r = reason::none();
    let mixed = make_type::mixed(r.clone());
    let bool_castable_ty = make_type::locl_like(
        r.clone(),
        make_type::nullable(
            r.clone(),
            make_type::union(
                r.clone(),
                vec![
                    make_type::vec_or_dict(r.clone(), make_type::arraykey(r.clone()), mixed),
                    make_type::keyset(r.clone(), make_type::arraykey(r)),
                ],
            ),
        ),
    );
    tast_env::is_sub_type(env, ty, &bool_castable_ty)
}

pub fn is_not_castable_but_leads_to_too_many_false_positives(
    env: &tast_env::Env,
    ty: &t::Ty,
) -> bool {
    let mut env = env.clone();
    let env = &mut env;
    let ty = tast_env::expand_type(env, ty.clone());
    let r = reason::none();
    let nonnull = make_type::nonnull(r.clone());
    let dynamic = make_type::dynamic(r);
    tast_env::is_sub_type(env, &nonnull, &ty)
        || tast_env::is_sub_type(env, &dynamic, &ty)
        || match t::get_node(&ty) {
            t::Ty_::Tgeneric(_) | t::Ty_::Tnewtype(_, _, _) => true,
            _ => false,
        }
}

/// The object `handler ~as_lint`.
struct CastNonPrimitive {
    as_lint: bool,
}

impl<'a> tast_visitor::Handler<'a> for CastNonPrimitive {
    fn at_expr(&mut self, env: &tast_env::Env, e: &tast::Expr) {
        let aast::Expr(_, pos, e) = e;
        match e {
            aast::Expr_::Cast(cast)
                if {
                    let (hint, aast::Expr(ty, _, _)) = &**cast;
                    !t_utils::is_nothing(env, ty)
                        && !is_always_castable(env, ty)
                        && !(is_bool_castable(env, ty)
                            && matches!(&*hint.1, aast::Hint_::Hprim(Tprim::Tbool)))
                        && !is_not_castable_but_leads_to_too_many_false_positives(env, ty)
                } =>
            {
                let (hint, aast::Expr(ty, _, _)) = &**cast;
                typing_warning_utils::add_for_migration(
                    &tast_env::get_tcopt(env),
                    if self.as_lint { Some(None) } else { None },
                    (
                        pos.clone(),
                        typing_warning::Kind::CAST_NON_PRIMITIVE,
                        typing_warning::cast_non_primitive::T {
                            cast_hint: tast_env::print_hint(env, hint),
                            ty: tast_env::print_ty(env, ty),
                        },
                    ),
                )
            }
            _ => {}
        }
    }
}

/// This linter catches dangerous uses of `(int)`, `(string)`, `(bool)`, and
/// `(float)` casts. These are safe to perform on the following inductive set
/// - primitives
/// - format strings
/// - nullables of safe types to perform casts.
///
/// Additionally, collections can be cast using `(bool)`.
///
/// Although, it is not known to be safe to perform casts on `mixed`,
/// `dynamic`, `nothing`, or genericly typed values, we do not lint against
/// them to prevent excessive false positives.
pub fn handler<'a>(as_lint: bool) -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(CastNonPrimitive { as_lint })
}
