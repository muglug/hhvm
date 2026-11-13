// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! The flags of `hh_single_type_check.ml` that make its options (the `ref`s
//! of its `parse_options`), apart from `crate::hh_single_type_check` (a
//! `port` module) so that `main.rs` can parse them in every configuration.

use oxidized::global_options::GlobalOptions;
use oxidized::i_set::ISet;
use oxidized::s_map::SMap;

/// The `ref`s of `parse_options` that the options are made of, as the
/// command line leaves them (`Default` is their initial values). `main.rs`
/// parses the command line into this; `crate::hh_single_type_check::make_tcopt` is
/// what `parse_options` does with them.
#[derive(Clone, Debug)]
pub struct Flags {
    /// `--config`, in the order of the command line
    pub config_overrides: Vec<String>,
    pub deregister_attributes: Option<bool>,
    pub auto_namespace_map: Option<Vec<(String, String)>>,
    pub log_inference_constraints: Option<bool>,
    pub timeout: Option<isize>,
    pub log_levels: SMap<isize>,
    pub skip_hierarchy_checks: bool,
    pub skip_tast_checks: bool,
    pub skip_check_under_dynamic: bool,
    pub call_coeffects: bool,
    pub local_coeffects: bool,
    pub strict_contexts: bool,
    pub enable_supportdyn_hint: bool,
    pub glean_reponame: String,
    pub disable_xhp_element_mangling: bool,
    pub keep_user_attributes: bool,
    pub enable_xhp_class_modifier: bool,
    pub allowed_fixme_codes_strict: Option<ISet>,
    pub allowed_decl_fixme_codes: Option<ISet>,
    pub consider_type_const_enforceable: bool,
    pub interpret_soft_types_as_like_types: bool,
    pub meth_caller_only_public_visibility: bool,
    pub explicit_consistent_constructors: isize,
    pub require_types_class_consts: isize,
    pub type_printer_fuel: isize,
    pub profile_top_level_definitions: bool,
    pub enable_global_access_check: bool,
    pub custom_error_config_path: Option<String>,
    pub allow_all_files_for_module_declarations: bool,
    pub loop_iteration_upper_bound: Option<isize>,
    pub enable_class_pointer_hint: bool,
    pub disallow_non_annotated_memoize: bool,
    pub treat_non_annotated_memoize_as_kbic: bool,
}

impl Default for Flags {
    fn default() -> Self {
        let default = GlobalOptions::default();
        Flags {
            config_overrides: vec![],
            deregister_attributes: None,
            auto_namespace_map: None,
            log_inference_constraints: None,
            timeout: None,
            log_levels: SMap::new(),
            skip_hierarchy_checks: false,
            skip_tast_checks: false,
            skip_check_under_dynamic: false,
            call_coeffects: true,
            local_coeffects: true,
            strict_contexts: true,
            enable_supportdyn_hint: false,
            // `Glean_options.reponame Global_options.default`
            glean_reponame: default.glean_reponame.clone(),
            disable_xhp_element_mangling: false,
            keep_user_attributes: false,
            enable_xhp_class_modifier: false,
            allowed_fixme_codes_strict: None,
            allowed_decl_fixme_codes: None,
            consider_type_const_enforceable: false,
            interpret_soft_types_as_like_types: false,
            meth_caller_only_public_visibility: true,
            explicit_consistent_constructors: 0,
            require_types_class_consts: 0,
            type_printer_fuel: default.tco_type_printer_fuel,
            profile_top_level_definitions: default.tco_profile_top_level_definitions,
            enable_global_access_check: false,
            custom_error_config_path: None,
            allow_all_files_for_module_declarations: true,
            loop_iteration_upper_bound: None,
            enable_class_pointer_hint: true,
            disallow_non_annotated_memoize: false,
            treat_non_annotated_memoize_as_kbic: false,
        }
    }
}
