// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_visibility.ml`. See `hh/PORTING.md`.
//!
//! The functions of the `.mli` are public, in its order of arguments. The
//! positions, names and visibilities that end up in the errors these
//! functions return are taken by value; what is only read is borrowed.
//!
//! The polymorphic variants of `Typing_packages` that the checks match on are
//! `typing_packages::CheckReason` (`check_reason`, named in OCaml),
//! `typing_packages::CanAccessByPackageRulesResult` (the result of
//! `can_access_by_package_rules`) and
//! `typing_packages::CanAccessIgnoringPackageOverrideResult` (the result of
//! `can_access_ignoring_package_override`), with the OCaml tags.

use oxidized::aast_defs::PackageMembership;
use oxidized::nast;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;

use crate::ast_defs;
use crate::decl_entry;
use crate::folded_class as cls;
use crate::tast;
use crate::typechecker_options;
use crate::typing_defs::PackageRequirement;
use crate::typing_defs_core::CeVisibility;
use crate::typing_defs_core::DeclTy;
use crate::typing_defs_core::DeclTy_;
use crate::typing_defs_core::string_of_visibility;
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::primary;
use crate::typing_error::primary::modules::T as Modules;
use crate::typing_error::primary::package::T as Package;
use crate::typing_error_utils;
use crate::typing_modules;
use crate::typing_modules::CanAccessInternalResult;
use crate::typing_packages;
use crate::typing_packages::CanAccessByPackageRulesResult;
use crate::typing_packages::CanAccessIgnoringPackageOverrideResult;
use crate::typing_packages::CheckReason;
use crate::typing_packages::PackageErrorInfo;
use crate::typing_packages::PackageWarningInfo;
use crate::typing_utils as tutils;
use crate::utils::strip_ns;

/// `Naming_special_names.UserAttributes.uaGatedByFeatureFlag`
/// (`naming_special_names_rust` does not have it).
const UA_GATED_BY_FEATURE_FLAG: &str = "__GatedByFeatureFlag";

pub enum PackageAccessResult {
    PackageAccessOk,
    PackageAccessError(typing_error::T),
    PackageAccessLinterError((Pos, PackageWarningInfo)),
}

#[derive(Clone, Copy)]
enum TestsBypassVisibilityHint {
    NoTestsBypassVisibilityHint,
    AddTestsBypassVisibilityAttribute,
    EnableTestsBypassVisibilityStaticProperties,
}

/// `Option.merge`
fn option_merge<A>(a: Option<A>, b: Option<A>, f: impl FnOnce(A, A) -> A) -> Option<A> {
    match (a, b) {
        (None, b) => b,
        (a, None) => a,
        (Some(a), Some(b)) => Some(f(a, b)),
    }
}

/// `fun s1 s2 -> s1 ^ "\n" ^ s2`
fn join_lines(s1: String, s2: String) -> String {
    s1 + "\n" + &s2
}

/// Is a private member defined on class/trait [origin_id] visible
/// from code in class/trait [self_id]?
///
/// For almost all circumstances, this is just a case of checking
/// that they are the same, *except* for the special case of
/// where-constraints on the this type defined on a trait, for example:
///
/// class C { private static function foo():void { } }
/// trait TR where this = C {
///   ...C::foo...
/// }
///
/// Using `require_class` also allows a trait to access the private
/// method from the class it requires
fn is_private_visible(env: &Env, origin_id: &str, self_id: &str) -> Option<String> {
    if origin_id == self_id {
        None
    } else {
        let in_bounds = |bounds: &[DeclTy]| {
            bounds.iter().any(|t| match t.node_ref() {
                DeclTy_::Tapply(id_and_args) => origin_id == id_and_args.0.id_ref().as_str(),
                _ => false,
            })
        };
        match env::get_class(env, self_id) {
            decl_entry::T::Found(cls) if ast_defs::is_c_trait(cls::kind(&cls)) => {
                // If the right class is required via `require class`, give access;
                // `require this as` constraints are not sufficient to give access
                let bounds_from_require_class_constraints: Vec<DeclTy> =
                    cls::all_ancestor_req_class_requirements(&cls)
                        .into_iter()
                        .map(|req| req.ty)
                        .collect();
                if in_bounds(&bounds_from_require_class_constraints) {
                    None
                } else {
                    Some("You cannot access this member".to_string())
                }
            }
            _ => Some("You cannot access this member".to_string()),
        }
    }
}

fn is_protected_visible(env: &Env, origin_id: &str, self_id: &str) -> Option<String> {
    if tutils::has_ancestor_including_req_refl(env, self_id, origin_id) {
        None
    } else {
        match env::get_class(env, origin_id) {
            decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => None,
            decl_entry::T::Found(origin_class) => {
                // Parents can call direct children's protected methods
                // (like a constructor)
                if cls::has_ancestor(&origin_class, self_id) {
                    None
                } else {
                    Some(format!(
                        "Cannot access this protected member, you don't extend {}",
                        strip_ns(origin_id)
                    ))
                }
            }
        }
    }
}

fn is_private_visible_for_class(
    env: &Env,
    x: &str,
    self_id: &str,
    cid: &nast::ClassId_,
    class_: &cls::T,
) -> Option<String> {
    match cid {
        nast::ClassId_::CIstatic => {
            let my_class = env::get_class(env, self_id);
            match my_class {
                decl_entry::T::Found(cls) if cls::final_(&cls) => None,
                _ => Some(
                    "Private members cannot be accessed with static:: since a child class may also have an identically named private member"
                        .to_string(),
                ),
            }
        }
        nast::ClassId_::CIparent => {
            Some("You cannot access a private member with parent::".to_string())
        }
        nast::ClassId_::CIself => is_private_visible(env, x, self_id),
        nast::ClassId_::CI(ast_defs::Id(_, called_ci)) => {
            match is_private_visible(env, x, self_id) {
                None => None,
                Some(_) => match env::get_class(env, called_ci) {
                    decl_entry::T::Found(cls) if ast_defs::is_c_trait(cls::kind(&cls)) => Some(
                        "You cannot access private members using the trait's name (did you mean to use self::?)"
                            .to_string(),
                    ),
                    _ => Some("You cannot access this member".to_string()),
                },
            }
        }
        nast::ClassId_::CIreified(_) => Some("You cannot access this member".to_string()),
        nast::ClassId_::CIexpr(_) => {
            if cls::final_(class_) && self_id == cls::name(class_) {
                None
            } else {
                Some(
                    "Private members cannot be accessed dynamically. Did you mean to use 'self::'?"
                        .to_string(),
                )
            }
        }
    }
}

fn is_internal_visible(env: &Env, target: &str) -> Option<String> {
    match typing_modules::can_access_internal(
        env,
        env::get_current_module(env),
        Some(target.to_string()),
    ) {
        CanAccessInternalResult::Yes => None,
        CanAccessInternalResult::Disjoint(current, target) => Some(format!(
            "You cannot access internal members from module `{}` in module `{}`",
            target, current
        )),
        CanAccessInternalResult::Outside(_) => {
            Some("You cannot access internal members outside of a module".to_string())
        }
        CanAccessInternalResult::OutsideViaTrait(_) => {
            Some("You cannot access internal members inside a public trait".to_string())
        }
    }
}

pub fn check_internal_access(
    in_signature: bool,
    tests_bypass_visibility_context: bool,
    env: &Env,
    target: Option<String>,
    pos: Pos,
    decl_pos: PosOrDecl,
) -> Option<typing_error::T> {
    let module_err_opt = match typing_modules::can_access_internal(
        env,
        env::get_current_module(env),
        target,
    ) {
        CanAccessInternalResult::Yes if in_signature && !env::get_internal(env) => {
            Some(Modules::Module_hint { pos, decl_pos })
        }
        CanAccessInternalResult::Yes => None,
        CanAccessInternalResult::Disjoint(current, target) => Some(Modules::Module_mismatch {
            pos,
            decl_pos,
            current_module_opt: Some(current),
            target_module: target,
            tests_bypass_visibility_context,
        }),
        CanAccessInternalResult::Outside(target) => Some(Modules::Module_mismatch {
            pos,
            decl_pos,
            current_module_opt: None,
            target_module: target,
            tests_bypass_visibility_context,
        }),
        CanAccessInternalResult::OutsideViaTrait(trait_pos) => {
            Some(Modules::Module_unsafe_trait_access {
                access_pos: pos,
                trait_pos,
            })
        }
    };
    module_err_opt.map(typing_error::modules)
}

/// Checks whether access to a symbol is permitted according to package visibility rules.
pub fn check_package_access(
    should_check_package_boundary: CheckReason,
    use_pos: Pos,
    def_pos: PosOrDecl,
    env: &Env,
    target_package_membership: Option<&PackageMembership>,
    target_id: String,
) -> PackageAccessResult {
    match should_check_package_boundary {
        CheckReason::No => PackageAccessResult::PackageAccessOk,
        CheckReason::Yes(target_symbol_spec) => {
            // (The OCaml computes the two lists first; they only read the
            // environment, and are needed only for the errors: computed there.)
            match typing_packages::can_access_by_package_rules(
                env,
                target_package_membership,
                &def_pos,
                target_id,
            ) {
                CanAccessByPackageRulesResult::Yes => PackageAccessResult::PackageAccessOk,
                CanAccessByPackageRulesResult::YesWarning(w) => {
                    PackageAccessResult::PackageAccessLinterError((use_pos, w))
                }
                CanAccessByPackageRulesResult::PackageNotSatisfied(PackageErrorInfo {
                    current_package,
                    current_package_assignment_kind,
                    target_package,
                    target_package_assignment_kind,
                    target_id,
                }) => PackageAccessResult::PackageAccessError(typing_error::package(
                    Package::Cross_pkg_access {
                        current_filename: crate::pos::filename(&use_pos),
                        target_filename: crate::pos_or_decl::filename(&def_pos),
                        pos: use_pos,
                        decl_pos: def_pos,
                        current_package,
                        current_package_assignment_kind,
                        target_package,
                        target_package_assignment_kind,
                        target_id,
                        target_symbol_spec,
                        loaded_packages: env::get_loaded_packages_list(env),
                        included_packages: env::get_included_packages(env),
                    },
                )),
                CanAccessByPackageRulesResult::PackageSoftIncludes(PackageErrorInfo {
                    current_package,
                    current_package_assignment_kind,
                    target_package,
                    target_package_assignment_kind,
                    target_id,
                }) => PackageAccessResult::PackageAccessError(typing_error::package(
                    Package::Soft_included_access {
                        current_filename: crate::pos::filename(&use_pos),
                        target_filename: crate::pos_or_decl::filename(&def_pos),
                        pos: use_pos,
                        decl_pos: def_pos,
                        current_package,
                        current_package_assignment_kind,
                        target_package,
                        target_package_assignment_kind,
                        target_id,
                        target_symbol_spec,
                        loaded_packages: env::get_loaded_packages_list(env),
                        included_packages: env::get_included_packages(env),
                    },
                )),
                CanAccessByPackageRulesResult::ExcludedPathAccess(PackageErrorInfo {
                    target_package,
                    target_id,
                    ..
                }) => PackageAccessResult::PackageAccessError(typing_error::package(
                    Package::Excluded_path_access {
                        target_filename: crate::pos_or_decl::filename(&def_pos),
                        pos: use_pos,
                        decl_pos: def_pos,
                        package: target_package,
                        target_id,
                        target_symbol_spec,
                    },
                )),
            }
        }
        CheckReason::LintOnly => {
            match typing_packages::can_access_by_package_rules(
                env,
                target_package_membership,
                &def_pos,
                target_id,
            ) {
                CanAccessByPackageRulesResult::Yes => PackageAccessResult::PackageAccessOk,
                CanAccessByPackageRulesResult::YesWarning(w) => {
                    PackageAccessResult::PackageAccessLinterError((use_pos, w))
                }
                CanAccessByPackageRulesResult::PackageNotSatisfied(_) => {
                    PackageAccessResult::PackageAccessOk
                }
                CanAccessByPackageRulesResult::PackageSoftIncludes(_) => {
                    PackageAccessResult::PackageAccessOk
                }
                CanAccessByPackageRulesResult::ExcludedPathAccess(_) => {
                    PackageAccessResult::PackageAccessOk
                }
            }
        }
        CheckReason::ClassPtrLinterOnly => {
            let current_file = env::get_file(env);
            let target_file = crate::pos_or_decl::filename(&def_pos);
            if typing_packages::is_excluded(env, &current_file)
                || typing_packages::is_excluded(env, &target_file)
            {
                PackageAccessResult::PackageAccessOk
            } else {
                let current_package = env::get_current_package(env).map(|p| p.name);
                let current_package_membership = env::get_current_package_membership(env);
                let check_classptr_access = || {
                    let (_, target_package, _) =
                        typing_packages::get_package_profile(env, target_package_membership);
                    match typing_packages::can_access_ignoring_package_override(
                        env,
                        current_package.clone(),
                        current_package
                            .as_ref()
                            .map(|crate::package::PosId(_, name)| name.clone()),
                        typing_packages::has_package_override(
                            current_package_membership.as_ref(),
                        ),
                        target_package,
                        typing_packages::has_package_override(target_package_membership),
                        &crate::pos_or_decl::filename(&def_pos),
                        true,
                    ) {
                        CanAccessIgnoringPackageOverrideResult::Yes => {
                            PackageAccessResult::PackageAccessOk
                        }
                        CanAccessIgnoringPackageOverrideResult::YesWarning(w) => {
                            PackageAccessResult::PackageAccessLinterError((use_pos.clone(), w))
                        }
                    }
                };
                match &current_package_membership {
                    Some(PackageMembership::PackageConfigAssignment(_)) => {
                        check_classptr_access()
                    }
                    Some(PackageMembership::PackageOverride(_, current_override_pkg)) => {
                        // When source has PackageOverride, only warn if target does NOT have
                        // PackageOverride to the same package. If target also overrides to the
                        // same package, both are effectively in the same package.
                        match target_package_membership {
                            Some(PackageMembership::PackageOverride(_, target_override_pkg))
                                if current_override_pkg == target_override_pkg =>
                            {
                                // Both override to the same package, no lint needed
                                PackageAccessResult::PackageAccessOk
                            }
                            _ => {
                                // Target has no override, or overrides to a different package.
                                // Check if source's override package includes target's original package.
                                check_classptr_access()
                            }
                        }
                    }
                    None => PackageAccessResult::PackageAccessOk,
                }
            }
        }
    }
}

fn is_visible_for_obj(
    is_method: bool,
    is_receiver_interface: bool,
    env: &Env,
    vis: &CeVisibility,
) -> Option<String> {
    let member_ty = if is_method { "method" } else { "property" };
    let check_protected = |x: &str| {
        if is_receiver_interface {
            Some("You cannot invoke a protected method on an interface".to_string())
        } else {
            match env::get_self_id(env) {
                None => Some(format!("You cannot access this {}", member_ty)),
                Some(self_id) => is_protected_visible(env, x, &self_id),
            }
        }
    };
    match vis {
        CeVisibility::Vpublic => None,
        CeVisibility::Vprivate(x) => match env::get_self_id(env) {
            None => Some(format!("You cannot access this {}", member_ty)),
            Some(self_id) => is_private_visible(env, x, &self_id),
        },
        CeVisibility::Vprotected(x) => check_protected(x),
        CeVisibility::Vinternal(m) => is_internal_visible(env, m),
        CeVisibility::VprotectedInternal { class_id, module__ } => {
            // OCaml evaluates the arguments of `Option.merge` right to left.
            let internal = is_internal_visible(env, module__);
            let protected = check_protected(class_id);
            option_merge(protected, internal, join_lines)
        }
    }
}

/// The only permitted way to access an LSB property is via
/// static::, ClassName::, or $class_name::
fn is_lsb_permitted(cid: &nast::ClassId_) -> Option<String> {
    match cid {
        nast::ClassId_::CIself => {
            Some("__LSB properties cannot be accessed with self::".to_string())
        }
        nast::ClassId_::CIparent => {
            Some("__LSB properties cannot be accessed with parent::".to_string())
        }
        _ => None,
    }
}

/// LSB property accessibility is relative to the defining class
fn is_lsb_accessible(env: &Env, vis: &CeVisibility) -> Option<String> {
    let check_protected = |x: &str| match env::get_self_id(env) {
        None => Some("You cannot access this property".to_string()),
        Some(self_id) => is_protected_visible(env, x, &self_id),
    };
    match vis {
        CeVisibility::Vpublic => None,
        CeVisibility::Vprivate(x) => match env::get_self_id(env) {
            None => Some("You cannot access this property".to_string()),
            Some(self_id) => is_private_visible(env, x, &self_id),
        },
        CeVisibility::Vprotected(x) => check_protected(x),
        CeVisibility::Vinternal(m) => is_internal_visible(env, m),
        CeVisibility::VprotectedInternal { class_id, module__ } => {
            // OCaml evaluates the arguments of `Option.merge` right to left.
            let internal = is_internal_visible(env, module__);
            let protected = check_protected(class_id);
            option_merge(protected, internal, join_lines)
        }
    }
}

fn is_lsb_visible_for_class(
    env: &Env,
    vis: &CeVisibility,
    cid: &nast::ClassId_,
) -> Option<String> {
    match is_lsb_permitted(cid) {
        Some(x) => Some(x),
        None => is_lsb_accessible(env, vis),
    }
}

fn is_visible_for_class(
    is_method: bool,
    env: &Env,
    (vis, lsb): (&CeVisibility, bool),
    cid: &nast::ClassId_,
    cty: &cls::T,
) -> Option<String> {
    if lsb {
        is_lsb_visible_for_class(env, vis, cid)
    } else {
        let member_ty = if is_method { "method" } else { "property" };
        let check_protected = |x: &str| match env::get_self_id(env) {
            None => Some(format!("You cannot access this {}", member_ty)),
            Some(self_id) => {
                let their_class = env::get_class(env, x);
                match (cid, their_class) {
                    (nast::ClassId_::CI(_), decl_entry::T::Found(cls))
                        if ast_defs::is_c_trait(cls::kind(&cls)) =>
                    {
                        Some(
                            "You cannot access protected members using the trait's name (did you mean to use static:: or self::?)"
                                .to_string(),
                        )
                    }
                    _ => is_protected_visible(env, x, &self_id),
                }
            }
        };
        match vis {
            CeVisibility::Vpublic => None,
            CeVisibility::Vprivate(x) => match env::get_self_id(env) {
                None => Some(format!("You cannot access this {}", member_ty)),
                Some(self_id) => is_private_visible_for_class(env, x, &self_id, cid, cty),
            },
            CeVisibility::Vprotected(x) => check_protected(x),
            CeVisibility::Vinternal(m) => is_internal_visible(env, m),
            CeVisibility::VprotectedInternal { class_id, module__ } => {
                // OCaml evaluates the arguments of `Option.merge` right to left.
                let internal = is_internal_visible(env, module__);
                let protected = check_protected(class_id);
                option_merge(protected, internal, join_lines)
            }
        }
    }
}

pub fn is_visible(
    is_method: bool,
    env: &Env,
    (vis, lsb): (&CeVisibility, bool),
    cid: Option<&nast::ClassId_>,
    class_: &cls::T,
) -> bool {
    let msg_opt = match cid {
        Some(cid) => is_visible_for_class(is_method, env, (vis, lsb), cid, class_),
        None => is_visible_for_obj(is_method, false, env, vis),
    };
    msg_opt.is_none()
}

fn visibility_error(
    tests_bypass_visibility_hint: TestsBypassVisibilityHint,
    p: Pos,
    msg: String,
    (p_vis, vis): (PosOrDecl, &CeVisibility),
) -> typing_error::T {
    let s = string_of_visibility(vis);
    let hint = match tests_bypass_visibility_hint {
        TestsBypassVisibilityHint::NoTestsBypassVisibilityHint => "",
        TestsBypassVisibilityHint::AddTestsBypassVisibilityAttribute => {
            ". To allow access from test contexts, add `<<__TestsBypassVisibility>>` to this member"
        }
        TestsBypassVisibilityHint::EnableTestsBypassVisibilityStaticProperties => {
            ". To allow static property access from test contexts, set `tests_bypass_visibility_static_properties = true` in `.hhconfig`"
        }
    };
    let msg_vis = format!("This member is {}{}", s, hint);
    typing_error::primary(primary::T::Visibility {
        pos: p,
        msg,
        decl_pos: p_vis,
        reason_msg: msg_vis,
    })
}

/// `vis` without what makes it internal, for the visibility check that
/// follows the module check.
fn vis_without_internal(vis: &CeVisibility) -> CeVisibility {
    match vis {
        CeVisibility::Vinternal(_) => CeVisibility::Vpublic,
        CeVisibility::VprotectedInternal { class_id, .. } => {
            CeVisibility::Vprotected(class_id.clone())
        }
        other => other.clone(),
    }
}

pub fn check_obj_access(
    is_method: bool,
    is_receiver_interface: bool,
    use_pos: Pos,
    def_pos: PosOrDecl,
    tests_bypass_visibility: bool,
    env: &Env,
    vis: &CeVisibility,
) -> Vec<typing_error::T> {
    let tests_bypass_visibility_context = tutils::is_tests_bypass_visibility_context(env);
    if tests_bypass_visibility && tests_bypass_visibility_context {
        vec![]
    } else {
        let check_visibility = |visibility_to_check: &CeVisibility| {
            is_visible_for_obj(is_method, is_receiver_interface, env, visibility_to_check).map(
                |msg| {
                    let tests_bypass_visibility_hint = if tests_bypass_visibility_context {
                        TestsBypassVisibilityHint::AddTestsBypassVisibilityAttribute
                    } else {
                        TestsBypassVisibilityHint::NoTestsBypassVisibilityHint
                    };
                    visibility_error(
                        tests_bypass_visibility_hint,
                        use_pos.clone(),
                        msg,
                        (def_pos.clone(), vis),
                    )
                },
            )
        };
        if env::get_tcopt(env).tco_use_module_error_for_member_access {
            let module_error = match vis {
                CeVisibility::Vinternal(m) => check_internal_access(
                    false,
                    tests_bypass_visibility_context,
                    env,
                    Some(m.clone()),
                    use_pos.clone(),
                    def_pos.clone(),
                ),
                CeVisibility::VprotectedInternal { module__, .. } => check_internal_access(
                    false,
                    tests_bypass_visibility_context,
                    env,
                    Some(module__.clone()),
                    use_pos.clone(),
                    def_pos.clone(),
                ),
                _ => None,
            };
            let vis_without_internal = vis_without_internal(vis);
            let visibility_error = check_visibility(&vis_without_internal);
            vec![module_error, visibility_error]
                .into_iter()
                .flatten()
                .collect()
        } else {
            check_visibility(vis).into_iter().collect()
        }
    }
}

pub fn check_top_level_access(
    should_check_package_boundary: CheckReason,
    in_signature: bool,
    use_pos: Pos,
    def_pos: PosOrDecl,
    tests_bypass_visibility: bool,
    target_supports_tests_bypass_visibility: bool,
    env: &Env,
    is_internal: bool,
    target_module: Option<String>,
    target_package: Option<&PackageMembership>,
    target_id: String,
) -> (Vec<typing_error::T>, Vec<(Pos, PackageWarningInfo)>) {
    let in_test_context = tutils::is_tests_bypass_visibility_context(env);
    let module_error = if is_internal && !(tests_bypass_visibility && in_test_context) {
        let tests_bypass_visibility_context =
            target_supports_tests_bypass_visibility && !tests_bypass_visibility && in_test_context;
        check_internal_access(
            in_signature,
            tests_bypass_visibility_context,
            env,
            target_module,
            use_pos.clone(),
            def_pos.clone(),
        )
    } else {
        None
    };
    let package_error = check_package_access(
        should_check_package_boundary,
        use_pos,
        def_pos,
        env,
        target_package,
        target_id,
    );
    match (module_error, package_error) {
        (Some(e1), PackageAccessResult::PackageAccessError(e2)) => (vec![e1, e2], vec![]),
        (Some(e), PackageAccessResult::PackageAccessLinterError(w)) => (vec![e], vec![w]),
        (Some(e), PackageAccessResult::PackageAccessOk) => (vec![e], vec![]),
        (None, PackageAccessResult::PackageAccessError(e)) => (vec![e], vec![]),
        (None, PackageAccessResult::PackageAccessLinterError(w)) => (vec![], vec![w]),
        (None, PackageAccessResult::PackageAccessOk) => (vec![], vec![]),
    }
}

/// Expression Trees can only access publicly accessible properties
pub fn check_expression_tree_vis(
    use_pos: Pos,
    def_pos: PosOrDecl,
    env: &Env,
    vis: &CeVisibility,
) -> Option<typing_error::T> {
    if env::is_in_expr_tree(env) {
        match vis {
            CeVisibility::Vpublic => None,
            _ => Some(typing_error::expr_tree(
                primary::expr_tree::T::Expression_tree_non_public_member {
                    pos: use_pos,
                    decl_pos: def_pos,
                },
            )),
        }
    } else {
        None
    }
}

pub fn check_meth_caller_access(
    use_pos: Pos,
    def_pos: PosOrDecl,
    tests_bypass_visibility: bool,
    env: &Env,
    vis: &CeVisibility,
) -> Option<typing_error::T> {
    if tests_bypass_visibility && tutils::is_tests_bypass_visibility_context(env) {
        None
    } else {
        match vis {
            CeVisibility::Vprivate(_) => {
                Some(typing_error::primary(primary::T::Private_meth_caller {
                    decl_pos: def_pos,
                    pos: use_pos,
                }))
            }
            CeVisibility::Vprotected(_) => {
                Some(typing_error::primary(primary::T::Protected_meth_caller {
                    decl_pos: def_pos,
                    pos: use_pos,
                }))
            }
            CeVisibility::Vinternal(_) => {
                Some(typing_error::primary(primary::T::Internal_meth_caller {
                    decl_pos: def_pos,
                    pos: use_pos,
                }))
            }
            CeVisibility::VprotectedInternal { .. } => Some(typing_error::primary(
                primary::T::Protected_internal_meth_caller {
                    decl_pos: def_pos,
                    pos: use_pos,
                },
            )),
            _ => None,
        }
    }
}

pub fn check_class_access(
    is_method: bool,
    use_pos: Pos,
    def_pos: PosOrDecl,
    tests_bypass_visibility: bool,
    tests_bypass_visibility_static_properties_blocked: bool,
    env: &Env,
    (vis, lsb): (&CeVisibility, bool),
    cid: &nast::ClassId_,
    class_: &cls::T,
) -> Vec<typing_error::T> {
    if tests_bypass_visibility && tutils::is_tests_bypass_visibility_context(env) {
        vec![]
    } else {
        let tests_bypass_visibility_context = tutils::is_tests_bypass_visibility_context(env);
        let check_visibility = |visibility_to_check: &CeVisibility| {
            is_visible_for_class(is_method, env, (visibility_to_check, lsb), cid, class_).map(
                |msg| {
                    let tests_bypass_visibility_hint = if tests_bypass_visibility_context {
                        if tests_bypass_visibility_static_properties_blocked {
                            TestsBypassVisibilityHint::EnableTestsBypassVisibilityStaticProperties
                        } else {
                            TestsBypassVisibilityHint::AddTestsBypassVisibilityAttribute
                        }
                    } else {
                        TestsBypassVisibilityHint::NoTestsBypassVisibilityHint
                    };
                    visibility_error(
                        tests_bypass_visibility_hint,
                        use_pos.clone(),
                        msg,
                        (def_pos.clone(), vis),
                    )
                },
            )
        };
        if env::get_tcopt(env).tco_use_module_error_for_member_access {
            let module_error = match vis {
                CeVisibility::Vinternal(m) => check_internal_access(
                    false,
                    tests_bypass_visibility_context,
                    env,
                    Some(m.clone()),
                    use_pos.clone(),
                    def_pos.clone(),
                ),
                CeVisibility::VprotectedInternal { module__, .. } => check_internal_access(
                    false,
                    tests_bypass_visibility_context,
                    env,
                    Some(module__.clone()),
                    use_pos.clone(),
                    def_pos.clone(),
                ),
                _ => None,
            };
            let vis_without_internal = vis_without_internal(vis);
            let visibility_error = check_visibility(&vis_without_internal);
            vec![module_error, visibility_error]
                .into_iter()
                .flatten()
                .collect()
        } else {
            check_visibility(vis).into_iter().collect()
        }
    }
}

/// Checks whether a function call satisfies the callee's package requirement annotation
/// (RequirePackage or SoftRequirePackage).
///
/// This function validates that the caller's per-continuation package environment
/// includes the required package. For soft requirements, it also considers whether
/// the caller has a matching [__SoftRequirePackage] annotation to allow soft-to-soft
/// calls during migration.
pub fn check_cross_package(
    use_pos: Pos,
    _def_pos: &PosOrDecl,
    env: &Env,
    package_requirement: Option<PackageRequirement>,
) -> Option<typing_error::T> {
    let current_pkg = env::get_current_package(env);
    let current_file = env::get_file(env);

    let can_call_in_continuation = |target: &str| {
        let target_pkg = env::get_package_by_name(env, target);
        typing_packages::get_package_violation(env, current_pkg.as_ref(), target_pkg.as_ref())
    };

    let in_exclude_patterns = |target_pos: &PosOrDecl| {
        let target_file = crate::pos_or_decl::filename(target_pos);
        let accessing_hhi = crate::pos_or_decl::is_hhi(target_pos);
        accessing_hhi
            || typing_packages::is_excluded(env, &current_file)
            || typing_packages::is_excluded(env, &target_file)
    };

    match package_requirement {
        Some(PackageRequirement::RPRequire(crate::typing_defs_core::PosString(
            target_pos,
            target,
        ))) => {
            if in_exclude_patterns(&target_pos) {
                None
            } else {
                match can_call_in_continuation(&target) {
                    Some(_) => {
                        // Convert from Package.t option to (string * Pos.t) option
                        let current_package = current_pkg.as_ref().map(|pkg| pkg.name.clone());
                        Some(typing_error::package(
                            Package::Cross_pkg_access_with_requirepackage {
                                pos: use_pos,
                                decl_pos: target_pos,
                                target_package: target,
                                current_package,
                                loaded_packages: env::get_loaded_packages_list(env),
                                included_packages: env::get_included_packages(env),
                            },
                        ))
                    }
                    _ => None,
                }
            }
        }
        Some(PackageRequirement::RPSoft(crate::typing_defs_core::PosString(soft_pos, soft))) => {
            if in_exclude_patterns(&soft_pos) {
                None
            } else {
                // If the per-continuation environment does not provide the softly-required
                // package, we have one more option -- a __SoftRequirePackage function may
                // call another __SoftRequirePackage function to aid monolithic migration
                // to __RequirePackage. In the soft-soft case, the choice of error is
                // arbitrary; we'll focus on the soft annotation rather than the per-cont
                // environment packages.
                match can_call_in_continuation(&soft) {
                    Some(_) => match env::get_soft_package_requirement(env) {
                        Some(ast_defs::Id(env_soft_pos, env_soft)) => {
                            let env_soft_pkg = env::get_package_by_name(env, &env_soft);
                            let soft_pkg = env::get_package_by_name(env, &soft);
                            match typing_packages::get_package_violation(
                                env,
                                env_soft_pkg.as_ref(),
                                soft_pkg.as_ref(),
                            ) {
                                Some(_) => Some(typing_error::package(
                                    Package::Cross_pkg_access_with_softrequirepackage {
                                        pos: use_pos,
                                        decl_pos: soft_pos,
                                        current_soft_package_opt: Some((env_soft_pos, env_soft)),
                                        target_package: soft,
                                        loaded_packages: env::get_loaded_packages_list(env),
                                        included_packages: env::get_included_packages(env),
                                    },
                                )),
                                None => None,
                            }
                        }
                        None => Some(typing_error::package(
                            Package::Cross_pkg_access_with_softrequirepackage {
                                pos: use_pos,
                                decl_pos: soft_pos,
                                current_soft_package_opt: None,
                                target_package: soft,
                                loaded_packages: env::get_loaded_packages_list(env),
                                included_packages: env::get_included_packages(env),
                            },
                        )),
                    },
                    _ => None,
                }
            }
        }
        Some(PackageRequirement::RPNormal) => None,
        None => None,
    }
}

pub fn check_deprecated(
    use_pos: Pos,
    def_pos: PosOrDecl,
    env: &Env,
    deprecated: Option<String>,
) -> Option<typing_error::T> {
    if tast::is_under_dynamic_assumptions(env.checked) {
        None
    } else {
        deprecated.map(|s| {
            typing_error::primary(primary::T::Deprecated_use {
                pos: use_pos,
                decl_pos_opt: Some(def_pos),
                msg: s,
            })
        })
    }
}

/// Check if a declaration is gated behind a feature flag via
/// [__GatedByFeatureFlag('feature')].  Emits error 4509 if the feature
/// is not enabled.  [attrs] are the user attributes from the already-loaded
/// decl so no additional decl fetch is needed.
///
/// The attributes of a declaration are `hackrs` ones here, whose `String`
/// parameters are byte strings: they are read as UTF-8 (lossily).
pub fn check_gated_by_feature_flag(
    env: &Env,
    pos: PosOrDecl,
    name: String,
    attrs: &[ty::decl::UserAttribute<pos::BPos>],
) {
    let feature_opt = attrs.iter().find_map(|ua| {
        if ua.name.id_ref().as_str() == UA_GATED_BY_FEATURE_FLAG {
            ua.params.iter().find_map(|param| match param {
                ty::decl::ty::UserAttributeParam::String(s) => {
                    Some(String::from_utf8_lossy(s.as_bytes()).into_owned())
                }
                _ => None,
            })
        } else {
            None
        }
    });
    if let Some(feature_name) = feature_opt {
        let tcopt = env::get_tcopt(env);
        if !typechecker_options::is_unstable_feature_enabled(&tcopt, &feature_name) {
            typing_error_utils::add_typing_error(
                &typing_error::primary(primary::T::Gated_by_feature_flag {
                    pos: crate::pos_or_decl::unsafe_to_raw_pos(pos),
                    name,
                    feature: feature_name,
                }),
                env,
            )
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn option_merge_joins_both() {
        assert_eq!(option_merge(None, None, join_lines), None);
        assert_eq!(
            option_merge(Some("a".to_string()), None, join_lines),
            Some("a".to_string())
        );
        assert_eq!(
            option_merge(None, Some("b".to_string()), join_lines),
            Some("b".to_string())
        );
        assert_eq!(
            option_merge(Some("a".to_string()), Some("b".to_string()), join_lines),
            Some("a\nb".to_string())
        );
    }

    #[test]
    fn vis_without_internal_strips_module() {
        assert_eq!(
            vis_without_internal(&CeVisibility::Vinternal("M".to_string())),
            CeVisibility::Vpublic
        );
        assert_eq!(
            vis_without_internal(&CeVisibility::VprotectedInternal {
                class_id: "\\C".to_string(),
                module__: "M".to_string(),
            }),
            CeVisibility::Vprotected("\\C".to_string())
        );
        assert_eq!(
            vis_without_internal(&CeVisibility::Vprivate("\\C".to_string())),
            CeVisibility::Vprivate("\\C".to_string())
        );
    }

    #[test]
    fn lsb_permitted() {
        assert_eq!(
            is_lsb_permitted(&nast::ClassId_::CIself),
            Some("__LSB properties cannot be accessed with self::".to_string())
        );
        assert_eq!(
            is_lsb_permitted(&nast::ClassId_::CIparent),
            Some("__LSB properties cannot be accessed with parent::".to_string())
        );
        assert_eq!(is_lsb_permitted(&nast::ClassId_::CIstatic), None);
    }
}
