// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! The Hack typechecker.
//!
//! The pipeline for a set of files is:
//!
//! 1. `decls`: every file is parsed by the direct decl parser, and its shallow
//!    declarations are added to the decl store. This also gives the naming
//!    table (which symbol is defined where).
//! 2. `check`: every file is parsed to an AST, named (the `elab` crate), and
//!    its definitions are typechecked against the (lazily folded) decls.
//!
//! Both phases run file by file in parallel; nothing is shared between files
//! except the decl stores.

pub mod check;
pub mod ctx;
pub mod diagnostics;
pub mod files;
pub mod im_empty;
pub mod naming_errors;
pub mod nast_check;
pub mod parse;
pub mod plist;
pub mod pmap;
pub mod typing_slice;
pub mod typing_print;
pub mod typing_reason;

// Modules that are being ported (see PORTING.md). They are compiled only with
// `--features port` until they build together.
#[cfg(feature = "port")]
pub mod aast;
#[cfg(feature = "port")]
pub mod aast_defs;
#[cfg(feature = "port")]
pub mod aast_utils;
#[cfg(feature = "port")]
pub mod ast_defs;
#[cfg(feature = "port")]
pub mod autocomplete_types;
#[cfg(feature = "port")]
pub mod counters;
#[cfg(feature = "port")]
pub mod decl_enforceability;
#[cfg(feature = "port")]
pub mod decl_entry;
#[cfg(feature = "port")]
pub mod decl_enum;
#[cfg(feature = "port")]
pub mod decl_env;
#[cfg(feature = "port")]
pub mod decl_hint;
#[cfg(feature = "port")]
pub mod decl_instantiate;
#[cfg(feature = "port")]
pub mod decl_provider;
#[cfg(feature = "port")]
pub mod decl_subst;
#[cfg(feature = "port")]
pub mod decl_utils;
#[cfg(feature = "port")]
pub mod deps;
#[cfg(any(feature = "port", feature = "server"))]
pub mod diagnostics_state;
#[cfg(any(feature = "port", feature = "server"))]
pub mod exception;
#[cfg(feature = "port")]
pub mod feature_logging;
#[cfg(any(feature = "port", feature = "server"))]
pub mod file_info;
#[cfg(feature = "port")]
pub mod folded_class;
#[cfg(any(feature = "port", feature = "server"))]
pub mod format;
#[cfg(any(feature = "port", feature = "server"))]
pub mod hack_event_logger;
#[cfg(feature = "port")]
pub mod hh_autoimport;
#[cfg(any(feature = "port", feature = "server"))]
pub mod hh_json_helpers;
#[cfg(any(feature = "port", feature = "server"))]
pub mod hh_logger;
#[cfg(feature = "port")]
pub mod hh_single_type_check;
#[cfg(any(feature = "port", feature = "server"))]
pub mod i_map;
#[cfg(any(feature = "port", feature = "server"))]
pub mod i_set;
#[cfg(feature = "port")]
pub mod local_id;
#[cfg(any(feature = "port", feature = "server"))]
pub mod markdown_lite;
#[cfg(any(feature = "port", feature = "server"))]
pub mod measure;
#[cfg(feature = "port")]
pub mod naming_attributes_params;
#[cfg(feature = "port")]
pub mod naming_special_names;
#[cfg(feature = "port")]
pub mod nast_eval;
#[cfg(feature = "port")]
pub mod old_shallow_classes_provider;
#[cfg(feature = "port")]
pub mod package;
#[cfg(feature = "port")]
pub mod package_info;
#[cfg(feature = "port")]
pub mod package_config;
#[cfg(any(feature = "port", feature = "server"))]
pub mod path;
#[cfg(any(feature = "port", feature = "server"))]
pub mod pos;
#[cfg(any(feature = "port", feature = "server"))]
pub mod pos_or_decl;
#[cfg(any(feature = "port", feature = "server"))]
pub mod quickfix;
#[cfg(any(feature = "port", feature = "server"))]
pub mod relative_path;
#[cfg(feature = "port")]
pub mod render;
#[cfg(any(feature = "port", feature = "server"))]
pub mod s_map;
#[cfg(any(feature = "port", feature = "server"))]
pub mod s_set;
#[cfg(feature = "port")]
pub mod sqlite_utils;
#[cfg(any(feature = "port", feature = "server"))]
pub mod string_utils;
#[cfg(any(feature = "port", feature = "server"))]
pub mod sys_utils;
#[cfg(feature = "port")]
pub mod tast;
#[cfg(any(feature = "port", feature = "server"))]
pub mod telemetry;
#[cfg(any(feature = "port", feature = "server"))]
pub mod tty;
#[cfg(feature = "port")]
pub mod type_mapper;
#[cfg(feature = "port")]
pub mod type_mapper_generic;
#[cfg(feature = "port")]
pub mod type_parameter_env;
#[cfg(feature = "port")]
pub mod type_parameter_env_ops;
#[cfg(feature = "port")]
pub mod type_visitor;
#[cfg(any(feature = "port", feature = "server"))]
pub mod typechecker_options;
#[cfg(feature = "port")]
pub mod typing_continuations;
#[cfg(feature = "port")]
pub mod typing_defs;
#[cfg(feature = "port")]
pub mod typing_defs_constraints;
#[cfg(feature = "port")]
pub mod typing_defs_core;
#[cfg(feature = "port")]
pub mod typing_deps;
#[cfg(feature = "port")]
pub mod typing_env;
#[cfg(feature = "port")]
pub mod typing_env_return_info;
#[cfg(feature = "port")]
pub mod typing_env_types;
#[cfg(feature = "port")]
pub mod typing_error;
#[cfg(feature = "port")]
pub mod typing_error_utils;
#[cfg(feature = "port")]
pub mod typing_fake_members;
#[cfg(feature = "port")]
pub mod typing_inference_env;
#[cfg(feature = "port")]
pub mod typing_kinding_defs;
#[cfg(feature = "port")]
pub mod typing_lenv;
#[cfg(feature = "port")]
pub mod typing_local_types;
#[cfg(feature = "port")]
pub mod typing_make_type;
#[cfg(feature = "port")]
pub mod typing_per_cont_env;
#[cfg(feature = "port")]
pub mod typing_per_cont_ops;
#[cfg(feature = "port")]
pub mod typing_tyvar_occurrences;
#[cfg(feature = "port")]
pub mod typing_warning;
#[cfg(feature = "port")]
pub mod typing_warning_utils;
#[cfg(any(feature = "port", feature = "server"))]
pub mod utils;
#[cfg(any(feature = "port", feature = "server"))]
pub mod wrapped_map;
#[cfg(any(feature = "port", feature = "server"))]
pub mod yojson;
#[cfg(feature = "port")]
pub mod tvid;
#[cfg(feature = "port")]
pub mod expression_id;
#[cfg(feature = "port")]
pub mod ident_provider;
#[cfg(feature = "port")]
pub mod typing_set;
#[cfg(feature = "port")]
pub mod internal_type_set;
#[cfg(feature = "port")]
pub mod typing_logic;
#[cfg(feature = "port")]
pub mod typing_logic_helpers;
#[cfg(feature = "port")]
pub mod typing_log_value;
#[cfg(feature = "port")]
pub mod type_force_lazy_values;
#[cfg(feature = "port")]
pub mod tany_sentinel;
#[cfg(feature = "port")]
pub mod typing_cont_key;
#[cfg(feature = "port")]
pub mod typing_defs_flags;
#[cfg(feature = "port")]
pub mod typing_class_types;
#[cfg(feature = "port")]
pub mod decl;
#[cfg(feature = "port")]
pub mod decl_counters;
#[cfg(feature = "port")]
pub mod decl_members;
#[cfg(feature = "port")]
pub mod decl_class;
#[cfg(feature = "port")]
pub mod decl_provider_internals;
#[cfg(feature = "port")]
pub mod typing_extends;
#[cfg(feature = "port")]
pub mod typing_class;
#[cfg(feature = "port")]
pub mod typing_toplevel;
#[cfg(feature = "port")]
pub mod typing_typedef;
#[cfg(feature = "port")]
pub mod typing_check_job;
#[cfg(feature = "port")]
pub mod typing_env_from_def;
#[cfg(feature = "port")]
pub mod typing_memoize;
#[cfg(feature = "port")]
pub mod typing_toplevel_enable;
#[cfg(feature = "port")]
pub mod typing_toplevel_profile;
#[cfg(feature = "port")]
pub mod typing_phase;
#[cfg(feature = "port")]
pub mod typing_tdef;
#[cfg(feature = "port")]
pub mod typing_tdef_locl;
#[cfg(feature = "port")]
pub mod type_expansions;
#[cfg(feature = "port")]
pub mod typing_expand;
#[cfg(feature = "port")]
pub mod derive_type_instantiation;
#[cfg(feature = "port")]
pub mod typing_generic_constraint;
#[cfg(feature = "port")]
pub mod typing_dependent_type;
#[cfg(feature = "port")]
pub mod typing_object_get;
#[cfg(feature = "port")]
pub mod typing_visibility;
#[cfg(feature = "port")]
pub mod typing_class_pointers;
#[cfg(feature = "port")]
pub mod typing_modules;
#[cfg(feature = "port")]
pub mod typing_refinement;
#[cfg(feature = "port")]
pub mod typing_data_type;
#[cfg(feature = "port")]
pub mod typing_tag_defs;
#[cfg(feature = "port")]
pub mod typing_atomic_data_types;
#[cfg(feature = "port")]
pub mod class_refinement;
#[cfg(feature = "port")]
pub mod typing_utils;
#[cfg(feature = "port")]
pub mod typing_solver;
#[cfg(feature = "port")]
pub mod typing_solver_utils;
#[cfg(feature = "port")]
pub mod typing_shadow_solver;
#[cfg(feature = "port")]
pub mod typing_ops;
#[cfg(feature = "port")]
pub mod typing_subtype_method;
#[cfg(feature = "port")]
pub mod typing_subtype_tconst;
#[cfg(feature = "port")]
pub mod typing_algebra;
#[cfg(feature = "port")]
pub mod recursion_tracker;
#[cfg(feature = "port")]
pub mod subtype_recursion_tracker;
#[cfg(feature = "port")]
pub mod typing_union;
#[cfg(feature = "port")]
pub mod typing_intersection;
#[cfg(feature = "port")]
pub mod typing_dynamic;
#[cfg(feature = "port")]
pub mod typing_dynamic_utils;
#[cfg(feature = "port")]
pub mod typing_coercion;
#[cfg(feature = "port")]
pub mod typing_partial_enforcement;
#[cfg(feature = "port")]
pub mod typing_enforceability;
#[cfg(feature = "port")]
pub mod typing_shapes;
#[cfg(feature = "port")]
pub mod typing_shape_disjointness;
#[cfg(feature = "port")]
pub mod typing_shape_normalize;
#[cfg(feature = "port")]
pub mod typing_shape_splat_key;
#[cfg(feature = "port")]
pub mod typing_structure;
#[cfg(feature = "port")]
pub mod typing_variance;
#[cfg(feature = "port")]
pub mod typing_type_wellformedness;
#[cfg(feature = "port")]
pub mod typing_type_integrity;
#[cfg(feature = "port")]
pub mod type_validator;
#[cfg(feature = "port")]
pub mod typing_enforceable_hint;
#[cfg(feature = "port")]
pub mod typing_reified_check;
#[cfg(feature = "port")]
pub mod typing_const_reifiable;
#[cfg(feature = "port")]
pub mod typing_array_access;
#[cfg(feature = "port")]
pub mod typing_array_access_util;
#[cfg(feature = "port")]
pub mod typing_taccess;
#[cfg(feature = "port")]
pub mod typing_type_member;
#[cfg(feature = "port")]
pub mod typing_escape;
#[cfg(feature = "port")]
pub mod type_mapper_forget;
#[cfg(feature = "port")]
pub mod typing_corners;
#[cfg(feature = "port")]
pub mod typing_skeleton;
#[cfg(feature = "port")]
pub mod typing_alias;
#[cfg(feature = "port")]
pub mod typing_sequencing;
#[cfg(feature = "port")]
pub mod typing_func_terminality;
#[cfg(feature = "port")]
pub mod typing_arithmetic;
#[cfg(feature = "port")]
pub mod typing_destructure;
#[cfg(feature = "port")]
pub mod typing_return;
#[cfg(feature = "port")]
pub mod typing_local_ops;
#[cfg(feature = "port")]
pub mod typing_async;
#[cfg(feature = "port")]
pub mod typing_equality_check;
#[cfg(feature = "port")]
pub mod typing_argument;
#[cfg(feature = "port")]
pub mod typing_param;
#[cfg(feature = "port")]
pub mod typing_helpers;
#[cfg(feature = "port")]
pub mod typing_coeffects;
#[cfg(feature = "port")]
pub mod typing_try;
#[cfg(feature = "port")]
pub mod typing_substring;
#[cfg(feature = "port")]
pub mod typing_named_params;
#[cfg(feature = "port")]
pub mod typing_disposable;
#[cfg(feature = "port")]
pub mod typing_native;
#[cfg(feature = "port")]
pub mod typing_enum;
#[cfg(feature = "port")]
pub mod typing_xhp;
#[cfg(feature = "port")]
pub mod xhp_attribute;
#[cfg(feature = "port")]
pub mod typing_regex;
// `Pcre` (pcre-ocaml), for `typing_regex`; links the system `libpcre`.
#[cfg(feature = "port")]
pub mod pcre;
#[cfg(feature = "port")]
pub mod typing_exts;
#[cfg(feature = "port")]
pub mod typing_packages;
#[cfg(feature = "port")]
pub mod typing_local_packages;
#[cfg(feature = "port")]
pub mod typing_attributes;
#[cfg(feature = "port")]
pub mod typing_requirements;
#[cfg(feature = "port")]
pub mod typing_needs_concrete;
#[cfg(feature = "port")]
pub mod typing_generic_rules;
#[cfg(feature = "port")]
pub mod typing_case_type_variant;
#[cfg(feature = "port")]
pub mod typing_case_type_check;
#[cfg(feature = "port")]
pub mod typing_case_type_utils;
#[cfg(feature = "port")]
pub mod typing_implemented_by;
#[cfg(feature = "port")]
pub mod trait_reuse_check;
#[cfg(feature = "port")]
pub mod ancestor_route;
#[cfg(feature = "port")]
pub mod tast_env;
#[cfg(feature = "port")]
pub mod tast_visitor;
#[cfg(feature = "port")]
pub mod tast_utils;
#[cfg(feature = "port")]
pub mod tast_expand;
#[cfg(feature = "port")]
pub mod tast_type_collector;
#[cfg(feature = "port")]
pub mod tast_with_dynamic;
#[cfg(feature = "port")]
pub mod typing_extract_method;
#[cfg(feature = "port")]
pub mod decl_fun_utils;
#[cfg(feature = "port")]
pub mod decl_nast;
#[cfg(feature = "port")]
pub mod hint_print;
#[cfg(feature = "port")]
pub mod typing_log;
#[cfg(feature = "port")]
pub mod typing_logger;
#[cfg(feature = "port")]
pub mod typing_json;
#[cfg(feature = "port")]
pub mod typing_debug;
#[cfg(feature = "port")]
pub mod typing_ast_print;
#[cfg(feature = "port")]
pub mod format_helpers;
#[cfg(feature = "port")]
pub mod abstract_class_check;
#[cfg(feature = "port")]
pub mod analyze_list_logger;
#[cfg(feature = "port")]
pub mod analyze_list_logger_types;
#[cfg(feature = "port")]
pub mod callconv_check;
#[cfg(feature = "port")]
pub mod cast_non_primitive;
#[cfg(feature = "port")]
pub mod class_const_origin_check;
#[cfg(feature = "port")]
pub mod class_inherited_member_case_check;
#[cfg(feature = "port")]
pub mod class_parent_check;
#[cfg(feature = "port")]
pub mod class_pointer_check;
#[cfg(feature = "port")]
pub mod const_write_check;
#[cfg(feature = "port")]
pub mod destructure_check;
#[cfg(feature = "port")]
pub mod discarded_awaitable_check;
#[cfg(feature = "port")]
pub mod disjoint_types;
#[cfg(feature = "port")]
pub mod duplicate_properties;
#[cfg(feature = "port")]
pub mod dynamic_call_check;
#[cfg(feature = "port")]
pub mod enforceable_hint_check;
#[cfg(feature = "port")]
pub mod enum_check;
#[cfg(feature = "port")]
pub mod enum_duplicate_value_check;
#[cfg(feature = "port")]
pub mod equality_check;
#[cfg(feature = "port")]
pub mod expression_tree_check;
#[cfg(feature = "port")]
pub mod fbid_igid_type_logger;
#[cfg(feature = "port")]
pub mod global_access_check;
#[cfg(feature = "port")]
pub mod handler;
#[cfg(feature = "port")]
pub mod if_enum_or_enum_class;
#[cfg(feature = "port")]
pub mod instantiability_check;
#[cfg(feature = "port")]
pub mod invalid_index_check;
#[cfg(feature = "port")]
pub mod is_check;
#[cfg(feature = "port")]
pub mod meth_caller_check;
#[cfg(feature = "port")]
pub mod method_type_param_check;
#[cfg(feature = "port")]
pub mod no_disjoint_union_check;
#[cfg(feature = "port")]
pub mod nothing_property_logger;
#[cfg(feature = "port")]
pub mod obj_get_check;
#[cfg(feature = "port")]
pub mod pseudofunctions_check;
#[cfg(feature = "port")]
pub mod readonly_check;
#[cfg(feature = "port")]
pub mod redundant_generics_check;
#[cfg(feature = "port")]
pub mod redundant_nullsafe;
#[cfg(feature = "port")]
pub mod reified_check;
#[cfg(feature = "port")]
pub mod rvalue_check;
#[cfg(feature = "port")]
pub mod set_or_keyset_array_get;
#[cfg(feature = "port")]
pub mod shape_field_check;
#[cfg(feature = "port")]
pub mod simplihack_check;
#[cfg(feature = "port")]
pub mod simplihack_interpreter;
#[cfg(feature = "port")]
pub mod simplihack_intf;
#[cfg(feature = "port")]
pub mod simplihack_prompt_context_provider;
#[cfg(feature = "port")]
pub mod static_memoized_check;
#[cfg(feature = "port")]
pub mod static_method_generics_check;
#[cfg(feature = "port")]
pub mod string_cast_check;
#[cfg(feature = "port")]
pub mod switch_exhaustivity_check;
#[cfg(feature = "port")]
pub mod tany_check;
#[cfg(feature = "port")]
pub mod tast_check;
#[cfg(feature = "port")]
pub mod tast_logger_util;
#[cfg(feature = "port")]
pub mod tautology_check;
#[cfg(feature = "port")]
pub mod this_hint_check;
#[cfg(feature = "port")]
pub mod truthiness_test;
#[cfg(feature = "port")]
pub mod type_const_check;
#[cfg(feature = "port")]
pub mod type_driven_code_health_logger;
#[cfg(feature = "port")]
pub mod unresolved_type_variable_check;
#[cfg(feature = "port")]
pub mod void_return_check;
#[cfg(feature = "port")]
pub mod xhp_attr_value;
#[cfg(feature = "port")]
pub mod xhp_check;
#[cfg(feature = "port")]
pub mod xhp_required_check;
#[cfg(feature = "port")]
pub mod decl_defs;
#[cfg(feature = "port")]
pub mod decl_requirements;
#[cfg(feature = "port")]
pub mod decl_folded_class;
#[cfg(feature = "port")]
pub mod decl_inherit;
#[cfg(feature = "port")]
pub mod provider_context;
#[cfg(feature = "port")]
pub mod naming_provider;
#[cfg(feature = "port")]
pub mod ast_provider;
#[cfg(feature = "port")]
pub mod file_provider;
#[cfg(feature = "port")]
pub mod worker_cancel;
#[cfg(feature = "port")]
pub mod naming_attributes;
#[cfg(feature = "port")]
pub mod lints_core;
#[cfg(feature = "port")]
pub mod lints_codes;
#[cfg(feature = "port")]
pub mod lints_diagnostics;
#[cfg(feature = "port")]
pub mod lint;
#[cfg(feature = "port")]
pub mod lint_codes;
#[cfg(any(feature = "port", feature = "server"))]
pub mod files_to_ignore;
#[cfg(any(feature = "port", feature = "server"))]
pub mod find_utils;
#[cfg(feature = "port")]
pub mod full_fidelity_ast;
#[cfg(feature = "port")]
pub mod full_fidelity_source_text;
#[cfg(feature = "port")]
pub mod parser_return;
#[cfg(feature = "port")]
pub mod typing_pessimisation_deps;
#[cfg(feature = "port")]
pub mod typing_deps_mode;
#[cfg(feature = "port")]
pub mod approx_set_intf;
#[cfg(feature = "port")]
pub mod approx_set;
#[cfg(feature = "port")]
pub mod bdd_set;
#[cfg(feature = "port")]
pub mod set_relation;
#[cfg(feature = "port")]
pub mod partition_intf;
#[cfg(feature = "port")]
pub mod partition;
#[cfg(feature = "port")]
pub mod typing_subtype;
#[cfg(feature = "port")]
pub mod typing;
#[cfg(any(feature = "port", feature = "server"))]
pub mod user_diagnostic;
#[cfg(any(feature = "port", feature = "server"))]
pub mod error_codes;
#[cfg(feature = "port")]
pub mod custom_error;
#[cfg(feature = "port")]
pub mod custom_error_config;
#[cfg(feature = "port")]
pub mod custom_error_config_loader;
#[cfg(feature = "port")]
pub mod tany_logger;
#[cfg(feature = "port")]
pub mod tany_logger_common;
#[cfg(feature = "port")]
pub mod tany_logger_file;
#[cfg(feature = "port")]
pub mod tany_logger_types;
#[cfg(feature = "port")]
pub mod custom_error_eval;
#[cfg(feature = "port")]
pub mod error_message;
#[cfg(feature = "port")]
pub mod patt_binding_ty;
#[cfg(feature = "port")]
pub mod patt_error;
#[cfg(feature = "port")]
pub mod patt_file;
#[cfg(feature = "port")]
pub mod patt_locl_ty;
#[cfg(feature = "port")]
pub mod patt_member_name;
#[cfg(feature = "port")]
pub mod patt_name;
#[cfg(feature = "port")]
pub mod patt_naming_error;
#[cfg(feature = "port")]
pub mod patt_string;
#[cfg(feature = "port")]
pub mod patt_typing_error;
#[cfg(feature = "port")]
pub mod patt_var;
#[cfg(feature = "port")]
pub mod validation_err;
#[cfg(feature = "port")]
pub mod positioned;
#[cfg(feature = "port")]
pub mod decl_store;
#[cfg(feature = "port")]
pub mod nast;
pub mod multifile;
pub mod hh_single_type_check_flags;
#[cfg(feature = "port")]
pub mod naming;
#[cfg(feature = "port")]
pub mod package_provider;

// The server layer (PORTING.md, "The server layer").
// (`rt::ocaml_filename` and `rt::ocaml_list` are also used by the error
// formatters, which `hh single` needs with `port`.)
#[cfg(any(feature = "port", feature = "server"))]
pub mod rt;
#[cfg(feature = "server")]
pub mod client_connect;
#[cfg(feature = "server")]
pub mod client_restart;
#[cfg(feature = "server")]
pub mod client_spinner;
#[cfg(feature = "server")]
pub mod server_command_types;
#[cfg(feature = "server")]
pub mod server_notifier;
#[cfg(feature = "server")]
pub mod server_progress_lwt;
#[cfg(feature = "server")]
pub mod connection_tracker;
#[cfg(feature = "server")]
pub mod infer_at_pos_service;
#[cfg(feature = "server")]
pub mod infer_error_at_pos_service;
#[cfg(feature = "server")]
pub mod save_state_service_types;
#[cfg(feature = "server")]
pub mod server_command_types_utils;
#[cfg(feature = "server")]
pub mod server_lint_types;
#[cfg(feature = "server")]
pub mod server_rage_types;
#[cfg(feature = "server")]
pub mod server_rename_types;
#[cfg(feature = "server")]
pub mod socket;
#[cfg(feature = "server")]
pub mod stats;
#[cfg(any(feature = "port", feature = "server"))]
pub mod symbol_definition;
#[cfg(any(feature = "port", feature = "server"))]
pub mod symbol_occurrence;
#[cfg(feature = "server")]
pub mod tast_holes_service;
#[cfg(any(feature = "port", feature = "server"))]
pub mod agent_diagnostic_formatter;
#[cfg(feature = "server")]
pub mod client_jsonl_printer;
#[cfg(any(feature = "port", feature = "server"))]
pub mod contextual_diagnostic_formatter;
#[cfg(any(feature = "port", feature = "server"))]
pub mod extended_diagnostic_formatter;
#[cfg(any(feature = "port", feature = "server"))]
pub mod filter_diagnostics;
#[cfg(any(feature = "port", feature = "server"))]
pub mod highlighted_diagnostic_formatter;
#[cfg(any(feature = "port", feature = "server"))]
pub mod plain_highlighted_diagnostic_formatter;
#[cfg(any(feature = "port", feature = "server"))]
pub mod raw_diagnostic_formatter;
#[cfg(feature = "server")]
pub mod server_error;
#[cfg(feature = "server")]
pub mod ai_options;
#[cfg(feature = "server")]
pub mod build_banner;
#[cfg(feature = "server")]
pub mod buffered_line_reader;
#[cfg(feature = "server")]
pub mod bucket;
#[cfg(any(feature = "port", feature = "server"))]
pub mod build_id;
#[cfg(feature = "server")]
pub mod cli_args;
#[cfg(feature = "server")]
pub mod client_args;
#[cfg(feature = "server")]
pub mod client_command;
#[cfg(feature = "server")]
pub mod client_decompress_zhhdg;
#[cfg(feature = "server")]
pub mod client_download_saved_state;
#[cfg(feature = "server")]
pub mod client_env;
#[cfg(feature = "server")]
pub mod client_lsp;
#[cfg(feature = "server")]
pub mod client_rage;
#[cfg(feature = "server")]
pub mod client_start;
#[cfg(feature = "server")]
pub mod client_stop;
#[cfg(any(feature = "port", feature = "server"))]
pub mod config_file;
#[cfg(any(feature = "port", feature = "server"))]
pub mod config_file_common;
#[cfg(any(feature = "port", feature = "server"))]
pub mod config_file_version;
#[cfg(any(feature = "port", feature = "server"))]
pub mod config_keys;
#[cfg(any(feature = "port", feature = "server"))]
pub mod exit;
#[cfg(any(feature = "port", feature = "server"))]
pub mod exit_status;
#[cfg(any(feature = "port", feature = "server"))]
pub mod experimental_features;
#[cfg(any(feature = "port", feature = "server"))]
pub mod experiments_config_file;
#[cfg(any(feature = "port", feature = "server"))]
pub mod file_content;
#[cfg(feature = "server")]
pub mod file_url;
#[cfg(feature = "server")]
pub mod find;
#[cfg(any(feature = "port", feature = "server"))]
pub mod find_refs_wire_format;
#[cfg(any(feature = "port", feature = "server"))]
pub mod global_config;
#[cfg(any(feature = "port", feature = "server"))]
pub mod hack_event_logger_types;
#[cfg(any(feature = "port", feature = "server"))]
pub mod hg_states;
#[cfg(feature = "server")]
pub mod hh_client;
#[cfg(feature = "server")]
pub mod hh_version;
#[cfg(feature = "server")]
pub mod http_lite;
#[cfg(feature = "server")]
pub mod jsonrpc;
#[cfg(feature = "server")]
pub mod lock;
#[cfg(any(feature = "port", feature = "server"))]
pub mod lsp;
#[cfg(any(feature = "port", feature = "server"))]
pub mod lsp_fmt;
#[cfg(feature = "server")]
pub mod lsp_helpers;
#[cfg(feature = "server")]
pub mod marshal_tools;
#[cfg(feature = "server")]
pub mod pid_log;
#[cfg(feature = "server")]
pub mod proc;
#[cfg(any(feature = "port", feature = "server"))]
pub mod random_id;
#[cfg(feature = "server")]
pub mod repo_root_ffi;
#[cfg(any(feature = "port", feature = "server"))]
pub mod saved_state_rollouts;
// F4: used by the symbol index (`port`).
#[cfg(any(feature = "port", feature = "server"))]
pub mod search_types;
#[cfg(feature = "server")]
pub mod server_args;
// `hh_server --check`, which needs the typing port.
#[cfg(all(feature = "port", feature = "server"))]
pub mod monitor_start;
#[cfg(all(feature = "port", feature = "server"))]
pub mod server_main;
#[cfg(any(feature = "port", feature = "server"))]
pub mod server_config;
#[cfg(feature = "server")]
pub mod server_files;
#[cfg(any(feature = "port", feature = "server"))]
pub mod server_local_config;
#[cfg(any(feature = "port", feature = "server"))]
pub mod server_local_config_knobs;
#[cfg(any(feature = "port", feature = "server"))]
pub mod server_local_config_load;
#[cfg(any(feature = "port", feature = "server"))]
pub mod server_local_config_qe;
#[cfg(any(feature = "port", feature = "server"))]
pub mod server_local_config_sandbox_experiment;
#[cfg(feature = "server")]
pub mod server_notifier_types;
#[cfg(feature = "server")]
pub mod server_progress;
#[cfg(any(feature = "port", feature = "server"))]
pub mod shared_mem;
#[cfg(any(feature = "port", feature = "server"))]
pub mod tmp;
#[cfg(feature = "server")]
pub mod wwwroot;
#[cfg(feature = "port")]
pub mod class_diff;
#[cfg(feature = "port")]
pub mod decl_compare;
#[cfg(feature = "port")]
pub mod decl_pos_utils;
#[cfg(feature = "port")]
pub mod fanout;
#[cfg(feature = "port")]
pub mod shallow_class_diff;
#[cfg(feature = "port")]
pub mod shallow_class_fanout;
#[cfg(feature = "port")]
pub mod shallow_decl_compare;

// The incremental daemon (plan /tmp/hh-port/incr/PLAN.md, §3.1). Typing,
// naming and decl modules are behind `port`; the server modules behind
// `server` (which implies `port`).
#[cfg(feature = "port")]
pub mod decl_redecl_service;
#[cfg(feature = "port")]
pub mod direct_decl_service;
#[cfg(feature = "port")]
pub mod naming_global;
#[cfg(feature = "port")]
pub mod naming_heap;
#[cfg(feature = "port")]
pub mod naming_table;
#[cfg(feature = "port")]
pub mod typing_check_service;
#[cfg(feature = "server")]
pub mod client_check;
#[cfg(feature = "server")]
pub mod client_check_status;
#[cfg(feature = "server")]
pub mod server_check_utils;
#[cfg(feature = "server")]
pub mod server_command;
#[cfg(feature = "server")]
pub mod server_env;
#[cfg(feature = "server")]
pub mod server_incremental;
#[cfg(feature = "server")]
pub mod server_init;
#[cfg(feature = "server")]
pub mod server_init_common;
#[cfg(feature = "server")]
pub mod server_lazy_init;
#[cfg(feature = "server")]
pub mod server_rpc;
#[cfg(feature = "server")]
pub mod server_type_check;
#[cfg(feature = "server")]
pub mod server_utils;

// Registrations by assignment (plan /tmp/hh-port/incr/PLAN.md §3.1, §7.3).
// Each assignment appends its `pub mod` lines (with their `#[cfg]`) at the end
// of its own block, before its `end` line, and edits no other block: that
// keeps three-way merges of concurrent registrations conflict-free. Modules
// registered before W0b stay where they are, above.
//
//
// ---- TCS: typing service ----
// ---- end TCS ----
//
//
// ---- N1: naming + Ctx ----
// ---- end N1 ----
//
//
// ---- R1: redecl ----
// ---- end R1 ----
//
//
// ---- MEMO: invalidation ----
// ---- end MEMO ----
//
//
// ---- MON: monitor ----
#[cfg(feature = "server")]
pub mod monitor_main;
#[cfg(feature = "server")]
pub mod server_controller;
#[cfg(feature = "server")]
pub mod server_process;
#[cfg(feature = "server")]
pub mod informant;
// ---- end MON ----
//
//
// ---- SRV: server loop ----
#[cfg(feature = "server")]
pub mod client_command_handler;
#[cfg(feature = "server")]
pub mod server_env_build;
#[cfg(feature = "server")]
pub mod server_idle;
#[cfg(feature = "server")]
pub mod periodical;
#[cfg(feature = "server")]
pub mod deferral_tracker;
#[cfg(feature = "server")]
pub mod hhi_root;
// ---- end SRV ----
//
//
// ---- ERR: streaming errors ----
// ---- end ERR ----
//
//
// ---- STATUS: status end to end ----
// ---- end STATUS ----
//
//
// ---- S1: recheck + init ----
#[cfg(feature = "server")]
pub mod server_init_types;
// ---- end S1 ----
//
//
// ---- T1: in-process harness ----
// ---- end T1 ----
//
//
// ---- T2: acceptance + suites ----
// ---- end T2 ----
//
//
// ---- X2: depgraph compaction ----
// ---- end X2 ----
//
//
// ---- P0: providers for services ----
#[cfg(feature = "port")]
pub mod tast_provider;
#[cfg(feature = "port")]
pub mod provider_utils;
// ---- end P0 ----
//
//
// ---- F0: hh single modes ----
#[cfg(feature = "port")]
pub mod hh_single_modes;
// ---- end F0 ----
//
//
// ---- F1: identify & definitions ----
#[cfg(feature = "port")]
pub mod identify_symbol_service;
#[cfg(feature = "port")]
pub mod server_symbol_definition;
#[cfg(feature = "server")]
pub mod server_go_to_definition;
#[cfg(feature = "server")]
pub mod server_type_definition;
#[cfg(feature = "port")]
pub mod server_identify_function;
#[cfg(feature = "port")]
pub mod server_find_type_var;
#[cfg(feature = "port")]
pub mod client_get_definition;
// ---- end F1 ----
//
//
// ---- F2: hover, docblocks, signature help ----
#[cfg(feature = "port")]
pub mod ide_hover;
#[cfg(feature = "port")]
pub mod server_docblock_at;
#[cfg(feature = "port")]
pub mod docblock_finder;
#[cfg(feature = "port")]
pub mod docblock_service;
#[cfg(feature = "port")]
pub mod server_signature_help;
#[cfg(feature = "port")]
pub mod hover_service;
#[cfg(feature = "port")]
pub mod docblock_parser;
// ---- end F2 ----
//
//
// ---- F3: autocomplete ----
#[cfg(feature = "port")]
pub mod autocomplete_service;
#[cfg(feature = "port")]
pub mod server_auto_complete;
#[cfg(feature = "port")]
pub mod user_attributes_as_map;
#[cfg(feature = "port")]
pub mod client_autocomplete;
// ---- end F3 ----
//
//
// ---- F4: search, symbol index, autoclose ----
#[cfg(feature = "port")]
pub mod symbol_index;
#[cfg(feature = "port")]
pub mod symbol_index_core;
#[cfg(feature = "port")]
pub mod local_search_service;
#[cfg(feature = "port")]
pub mod search_utils;
#[cfg(feature = "port")]
pub mod ide_search;
#[cfg(feature = "port")]
pub mod autoclose_tags;
#[cfg(feature = "port")]
pub mod class_method_search;
#[cfg(feature = "port")]
pub mod custom_search_service;
#[cfg(feature = "port")]
pub mod glean;
#[cfg(feature = "port")]
pub mod glean_autocomplete_query;
// ---- end F4 ----
//
//
// ---- F5: outline, highlight, locals ----
#[cfg(feature = "port")]
pub mod file_outline;
#[cfg(feature = "port")]
pub mod ide_highlight_refs;
#[cfg(feature = "port")]
pub mod server_find_locals;
#[cfg(feature = "port")]
pub mod ide_top_level_def_name_at_pos;
#[cfg(feature = "port")]
pub mod outline_for_agents;
#[cfg(feature = "port")]
pub mod ide_parser_cache;
#[cfg(feature = "port")]
pub mod ide_api_types;
#[cfg(feature = "port")]
pub mod nuclide_rpc_message_printer;
#[cfg(feature = "port")]
pub mod client_outline;
#[cfg(feature = "port")]
pub mod client_highlight_refs;
// ---- end F5 ----
//
//
// ---- F6: find refs, impl, rename, method jumps ----
#[cfg(feature = "port")]
pub mod find_refs_service;
// (`server`: they take `Server_env` and `Server_command_types`.)
#[cfg(feature = "server")]
pub mod server_find_refs;
#[cfg(feature = "server")]
pub mod server_go_to_impl;
#[cfg(feature = "server")]
pub mod server_rename;
#[cfg(feature = "server")]
pub mod method_jumps;
// ---- end F6 ----
//
//
// ---- F7: code actions I ----
// (`server`: the code actions are built on the `Lsp` types, which are
// `server`-only.)
#[cfg(feature = "server")]
pub mod code_actions;
#[cfg(feature = "server")]
pub mod lsp_extra_commands;
#[cfg(feature = "port")]
pub mod classish_positions;
#[cfg(feature = "server")]
pub mod classish_positions_cli_lib;
// ---- end F7 ----
//
//
// ---- F8: code actions II ----
// ---- end F8 ----
//
//
// ---- LINT: linters ----
#[cfg(feature = "port")]
pub mod linting_main;
#[cfg(feature = "port")]
pub mod linting_visitors;
#[cfg(feature = "server")]
pub mod server_lint;
#[cfg(feature = "server")]
pub mod client_lint;
#[cfg(feature = "port")]
pub mod linter_ast;
#[cfg(feature = "port")]
pub mod linter_async_lambda;
#[cfg(feature = "port")]
pub mod linter_branches_return_same_value;
#[cfg(feature = "port")]
pub mod linter_class_overrides_trait;
#[cfg(feature = "port")]
pub mod linter_clone;
#[cfg(feature = "port")]
pub mod linter_comparing_booleans;
#[cfg(feature = "port")]
pub mod linter_expr_tree_types;
#[cfg(feature = "port")]
pub mod linter_foreach_shadow;
#[cfg(feature = "port")]
pub mod linter_internal_class;
#[cfg(feature = "port")]
pub mod linter_invariant_violation;
#[cfg(feature = "port")]
pub mod linter_missing_override_attribute;
#[cfg(feature = "port")]
pub mod linter_pointless_booleans;
#[cfg(feature = "port")]
pub mod linter_redundant_cast;
#[cfg(feature = "port")]
pub mod linter_redundant_generics;
#[cfg(feature = "port")]
pub mod linter_unconditional_recursion;
// ---- end LINT ----
//
//
// ---- FMT: IDE formatting ----
// `ide_format` is behind `server`, as `lsp` (which it uses) is; it uses F5's
// `ide_api_types`.
#[cfg(feature = "server")]
pub mod ide_format;
#[cfg(feature = "port")]
pub mod hackfmt_error;
#[cfg(feature = "port")]
pub mod server_format_types;
// ---- end FMT ----
//
//
// ---- E1: position RPCs ----
#[cfg(any(feature = "port", feature = "server"))]
pub mod server_infer_type;
#[cfg(feature = "server")]
pub mod server_infer_type_batch;
#[cfg(feature = "server")]
pub mod server_infer_type_error;
#[cfg(feature = "server")]
pub mod server_is_subtype;
#[cfg(feature = "server")]
pub mod server_status_single;
#[cfg(feature = "server")]
pub mod client_type_at_pos;
// ---- end E1 ----
//
//
// ---- E2: global RPCs ----
#[cfg(feature = "server")]
pub mod server_file_dependents;
#[cfg(feature = "server")]
pub mod client_rename;
#[cfg(feature = "server")]
pub mod client_method_jumps;
// ---- end E2 ----
//
//
// ---- E3: Meta-ish RPCs ----
#[cfg(feature = "port")]
pub mod ast_show;
#[cfg(feature = "port")]
pub mod naming_ast_print;
#[cfg(feature = "port")]
pub mod enforcement_at_pos_service;
#[cfg(feature = "port")]
pub mod server_enforcement_at_pos;
#[cfg(feature = "port")]
pub mod server_infer_dynamic;
#[cfg(feature = "port")]
pub mod schema_definition;
#[cfg(feature = "port")]
pub mod cst_search_service;
// ---- end E3 ----
//
//
// ---- SS1: naming SQLite ----
#[cfg(feature = "port")]
pub mod naming_sqlite;
#[cfg(feature = "port")]
pub mod db_path_provider;
// ---- end SS1 ----
//
//
// ---- L0: lazy Ctx ----
#[cfg(feature = "port")]
pub mod lfu_cache;
#[cfg(feature = "port")]
pub mod provider_backend;
#[cfg(all(test, feature = "port"))]
mod lazy_ctx_tests;
// ---- end L0 ----
//
//
// ---- SS3: saved-state load ----
#[cfg(feature = "server")]
pub mod save_state_service;
#[cfg(feature = "server")]
pub mod server_prechecked_files;
#[cfg(feature = "server")]
pub mod diff_naming_table;
// ---- end SS3 ----
//
//
// ---- SS4: saved-state production ----
#[cfg(feature = "server")]
pub mod save_state_writer;
// ---- end SS4 ----
//
//
// ---- G1: IDE daemon ----
#[cfg(feature = "server")]
pub mod client_ide_daemon;
#[cfg(feature = "server")]
pub mod client_ide_init;
#[cfg(feature = "server")]
pub mod client_ide_incremental;
#[cfg(feature = "server")]
pub mod client_ide_message;
#[cfg(feature = "server")]
pub mod client_ide_utils;
#[cfg(feature = "server")]
pub mod client_ide_service;
#[cfg(feature = "server")]
pub mod ide_diagnostics;
#[cfg(feature = "server")]
pub mod ide_diagnostics_cli_lib;
#[cfg(feature = "server")]
pub mod lwt_message_queue;
// ---- end G1 ----
//
//
// ---- G3: Client_lsp core ----
// ---- end G3 ----
//
//
// ---- G4: Client_lsp handlers ----
// ---- end G4 ----
//
//
// ---- P2-INF: informant Active ----
#[cfg(feature = "server")]
pub mod informant_notifier;
#[cfg(feature = "server")]
pub mod server_revision_tracker;
// ---- end P2-INF ----
