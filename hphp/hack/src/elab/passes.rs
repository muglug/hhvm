// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

// The passes codegen runs.
pub mod drop_unsafe_cast;
pub mod elab_expr_package;
pub mod elab_require_package;
pub mod remove_memo_attr;

// The naming passes of the typechecker, in the order of `naming/naming.ml`.
pub mod guard_invalid;
pub mod elab_defs;
pub mod elab_func_body;
pub mod elab_block;
pub mod elab_hint_hsoft;
pub mod elab_hint_happly;
pub mod elab_class_id;
pub mod elab_expr_collection;
pub mod elab_user_attributes;
pub mod elab_expr_import;
pub mod elab_expr_lvar;
pub mod elab_enum_class;
pub mod elab_class_members;
pub mod elab_call;
pub mod elab_expr_call_hh_invariant;
pub mod elab_hint_retonly;
pub mod elab_hint_wildcard;
pub mod elab_shape_field_name;
pub mod elab_hint_this;
pub mod elab_hint_haccess;
pub mod elab_dynamic_class_name;
pub mod elab_const_expr;
pub mod elab_as_expr;
pub mod validate_expr_cast;
pub mod validate_dynamic_hint;
pub mod validate_fun_params;
pub mod validate_class_req;
pub mod validate_xhp_name;
pub mod validate_polymorphic_lambda_expr;
pub mod elab_everything_sdt;
pub mod validate_class_consistent_construct;
pub mod validate_supportdyn;
pub mod validate_module;
pub mod validate_function_hint_optional_parameters;
pub mod validate_typed_open_shape;
pub mod validate_named_variadic_type;
pub mod validate_variadic_named_parameter;
pub mod validate_clone_return_type;
