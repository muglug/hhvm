// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `tast_check.ml`. See `hh/PORTING.md`.
//!
//! A handler is a `Box<dyn tast_visitor::Handler<'a> + 'a>`, where `'a` is
//! the lifetime of the TAST it is given; the first-class modules of
//! `warning_checks` are `handler::warning::S` records.

use std::sync::Arc;

use crate::abstract_class_check;
use crate::analyze_list_logger;
use crate::callconv_check;
use crate::cast_non_primitive;
use crate::class_const_origin_check;
use crate::class_inherited_member_case_check;
use crate::class_parent_check;
use crate::class_pointer_check;
use crate::const_write_check;
use crate::ctx::Ctx;
use crate::destructure_check;
use crate::discarded_awaitable_check;
use crate::disjoint_types;
use crate::duplicate_properties;
use crate::dynamic_call_check;
use crate::dynamic_return_check;
use crate::enforceable_hint_check;
use crate::enum_check;
use crate::enum_duplicate_value_check;
use crate::equality_check;
use crate::expression_tree_check;
use crate::fbid_igid_type_logger;
use crate::global_access_check;
use crate::handler;
use crate::instantiability_check;
use crate::invalid_index_check;
use crate::is_check;
use crate::meth_caller_check;
use crate::method_type_param_check;
use crate::no_disjoint_union_check;
use crate::nothing_property_logger;
use crate::obj_get_check;
use crate::provider_context;
use crate::pseudofunctions_check;
use crate::readonly_check;
use crate::redundant_generics_check;
use crate::private_member_variance_check;
use crate::redundant_concurrent;
use crate::redundant_nullsafe;
use crate::reified_check;
use crate::rvalue_check;
use crate::set_or_keyset_array_get;
use crate::shape_field_check;
use crate::simplihack_check;
use crate::static_memoized_check;
use crate::static_method_generics_check;
use crate::string_cast_check;
use crate::switch_exhaustivity_check;
use crate::tany_check;
use crate::tast;
use crate::tast_visitor;
use crate::tany_logger;
use crate::tautology_check;
use crate::this_hint_check;
use crate::truthiness_test;
use crate::type_const_check;
use crate::type_driven_code_health_logger;
use crate::typing_warning_utils;
use crate::unresolved_type_variable_check;
use crate::void_return_check;
use crate::xhp_attr_value;
use crate::xhp_check;
use crate::xhp_required_check;

/// `Tast_visitor.handler`
type Handler<'a> = Box<dyn tast_visitor::Handler<'a> + 'a>;

/// `Remove_dead_unsafe_casts.patch_location_collection_handler`
fn remove_dead_unsafe_casts_patch_location_collection_handler<'a>() -> Handler<'a> {
    crate::remove_dead_unsafe_casts::patch_location_collection_handler()
}

pub fn logger_handlers<'a>() -> Vec<(&'static str, fn(&Arc<Ctx>) -> Handler<'a>)> {
    vec![
        ("tany", tany_logger::create_handler),
        ("nothing_property", nothing_property_logger::create_handler),
        ("fbid_igid_type", fbid_igid_type_logger::create_handler),
        (
            "type_driven_code_health",
            type_driven_code_health_logger::create_handler,
        ),
        ("list_logger", analyze_list_logger::create_handler),
    ]
}

/// Handlers that are enabled through 'log_levels' configuration.
pub fn select_logger_handlers<'a>(ctx: &Arc<Ctx>) -> Vec<Handler<'a>> {
    let tco = provider_context::get_tcopt(ctx);
    let log_levels = &tco.log_levels;
    // `List.fold ~init:[] ~f:add_handler logger_handlers`: each handler is
    // put in front of the ones before it.
    let mut handlers = vec![];
    for (key, handler) in logger_handlers() {
        match log_levels.get(key) {
            Some(level) if *level > 0 => handlers.insert(0, handler(ctx)),
            _ => {}
        }
    }
    handlers
}

pub fn warning_checks<'a>() -> Vec<handler::warning::S<'a>> {
    vec![
        handler::warning::S {
            error_codes: is_check::error_codes,
            handler: is_check::handler,
        },
        handler::warning::S {
            error_codes: disjoint_types::error_codes,
            handler: disjoint_types::handler,
        },
        handler::warning::S {
            error_codes: cast_non_primitive::error_codes,
            handler: cast_non_primitive::handler,
        },
        handler::warning::S {
            error_codes: truthiness_test::error_codes,
            handler: truthiness_test::handler,
        },
        handler::warning::S {
            error_codes: equality_check::error_codes,
            handler: equality_check::handler,
        },
        handler::warning::S {
            error_codes: duplicate_properties::error_codes,
            handler: duplicate_properties::handler,
        },
        handler::warning::S {
            error_codes: redundant_nullsafe::error_codes,
            handler: redundant_nullsafe::handler,
        },
        handler::warning::S {
            error_codes: redundant_concurrent::error_codes,
            handler: redundant_concurrent::handler,
        },
        handler::warning::S {
            error_codes: set_or_keyset_array_get::error_codes,
            handler: set_or_keyset_array_get::handler,
        },
        handler::warning::S {
            error_codes: tany_check::error_codes,
            handler: tany_check::handler,
        },
        handler::warning::S {
            error_codes: dynamic_call_check::error_codes,
            handler: dynamic_call_check::handler,
        },
        handler::warning::S {
            error_codes: dynamic_return_check::error_codes,
            handler: dynamic_return_check::handler,
        },
    ]
}

pub fn visitor<'a>(ctx: &Arc<Ctx>) -> tast_visitor::IterWith<'a> {
    visitor_(ctx, false)
}

/// `visitor`; with `record_warnings`, the visitor marks the time the warning
/// checks run (see [`def_recording_warning_keys`]).
fn visitor_<'a>(ctx: &Arc<Ctx>, record_warnings: bool) -> tast_visitor::IterWith<'a> {
    // Handlers that are not TAST checks to produce errors, but are used for
    // telemetry that processes TASTs.
    let irregular_handlers = select_logger_handlers(ctx);
    let tcopt = provider_context::get_tcopt(ctx);
    let hierarchy_check = |handler: Handler<'a>| -> Option<Handler<'a>> {
        if tcopt.tco_skip_hierarchy_checks {
            None
        } else {
            Some(handler)
        }
    };

    let warning_handlers: Vec<Handler<'a>> = warning_checks()
        .into_iter()
        .filter_map(|m| {
            if (m.error_codes)()
                .into_iter()
                .any(|code| typing_warning_utils::code_is_enabled(&tcopt, code))
            {
                Some((m.handler)(false))
            } else {
                None
            }
        })
        .collect();
    let regular_handlers: Vec<Option<Handler<'a>>> = vec![
        xhp_required_check::create_handler(ctx),
        redundant_generics_check::create_handler(ctx),
        Some(shape_field_check::handler()),
        Some(string_cast_check::handler()),
        Some(tautology_check::handler()),
        Some(enforceable_hint_check::handler()),
        Some(const_write_check::handler()),
        Some(switch_exhaustivity_check::handler()),
        Some(void_return_check::handler()),
        Some(rvalue_check::handler()),
        Some(callconv_check::handler()),
        Some(xhp_check::handler()),
        Some(discarded_awaitable_check::handler()),
        Some(invalid_index_check::handler()),
        Some(pseudofunctions_check::handler()),
        Some(reified_check::handler()),
        Some(instantiability_check::handler()),
        Some(static_memoized_check::handler()),
        Some(abstract_class_check::handler()),
        hierarchy_check(class_parent_check::handler()),
        Some(method_type_param_check::handler()),
        Some(obj_get_check::handler()),
        Some(this_hint_check::handler()),
        Some(unresolved_type_variable_check::handler()),
        Some(type_const_check::handler()),
        Some(static_method_generics_check::handler()),
        hierarchy_check(class_inherited_member_case_check::handler()),
        Some(readonly_check::handler()),
        Some(destructure_check::handler()),
        Some(meth_caller_check::handler()),
        Some(expression_tree_check::handler()),
        Some(xhp_attr_value::handler()),
        hierarchy_check(class_const_origin_check::handler()),
        if tcopt.tco_global_access_check_enabled {
            Some(global_access_check::handler())
        } else {
            None
        },
        hierarchy_check(enum_check::handler()),
        if tcopt.tco_check_duplicate_enum_values {
            hierarchy_check(enum_duplicate_value_check::handler())
        } else {
            None
        },
        if tcopt.tco_populate_dead_unsafe_cast_heap {
            Some(remove_dead_unsafe_casts_patch_location_collection_handler())
        } else {
            None
        },
        Some(class_pointer_check::handler()),
        Some(private_member_variance_check::handler()),
        Some(no_disjoint_union_check::handler()),
        Some(simplihack_check::handler()),
    ];
    let mut handlers = irregular_handlers;
    let warning_start = handlers.len();
    handlers.extend(warning_handlers);
    let warning_end = handlers.len();
    handlers.extend(regular_handlers.into_iter().flatten());
    let handlers = if provider_context::get_tcopt(ctx).tco_skip_tast_checks {
        vec![]
    } else {
        handlers
    };
    if record_warnings && !handlers.is_empty() {
        tast_visitor::iter_with_recording_warnings(None, handlers, warning_start..warning_end)
    } else {
        tast_visitor::iter_with(None, handlers)
    }
}

pub fn program(ctx: &Arc<Ctx>, program: &tast::Program) {
    visitor(ctx).go(ctx, &program.0)
}

pub fn def(ctx: &Arc<Ctx>, def: &tast::Def) {
    crate::tast_env::clear_merge_memo();
    visitor(ctx).go_def(ctx, def)
}

/// [`def`], which also returns the keys that [`warning_def`] on the same
/// definition would collect (`Diagnostics.collect_warning_keys`): those of
/// the warnings that its warning checks add (see
/// `diagnostics_state::start_recording_warning_keys`). No OCaml counterpart:
/// `Typing_check_job` uses it instead of running the warning checks a second
/// time on the same TAST.
pub fn def_recording_warning_keys(ctx: &Arc<Ctx>, def: &tast::Def) -> Vec<(isize, oxidized::pos::Pos)> {
    crate::tast_env::clear_merge_memo();
    crate::diagnostics_state::start_recording_warning_keys();
    visitor_(ctx, true).go_def(ctx, def);
    crate::diagnostics_state::take_recorded_warning_keys()
}

/// A visitor that only runs warning checks (no error-producing checks).
/// Used to run warning checks on the dynamic TAST for trusted/untrusted
/// intersection.
pub fn warning_visitor<'a>(ctx: &Arc<Ctx>) -> tast_visitor::IterWith<'a> {
    let tcopt = provider_context::get_tcopt(ctx);
    let handlers: Vec<Handler<'a>> = if tcopt.tco_skip_tast_checks {
        vec![]
    } else {
        warning_checks()
            .into_iter()
            .filter_map(|m| {
                if (m.error_codes)()
                    .into_iter()
                    .any(|code| typing_warning_utils::code_is_enabled(&tcopt, code))
                {
                    Some((m.handler)(false))
                } else {
                    None
                }
            })
            .collect()
    };
    tast_visitor::iter_with(Some(true), handlers)
}

/// Run only warning-producing TAST checks. Used for running warning checks
/// on the dynamic TAST to determine which warnings are trusted.
pub fn warning_def(ctx: &Arc<Ctx>, def: &tast::Def) {
    warning_visitor(ctx).go_def(ctx, def)
}

/// Run only warning-producing TAST checks on a full program.
pub fn warning_program(ctx: &Arc<Ctx>, program: &tast::Program) {
    warning_visitor(ctx).go(ctx, &program.0)
}
