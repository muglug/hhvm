// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `decl/decl_defs.ml`. See `hh/PORTING.md`.
//!
//! # Types
//!
//! Decl data stays in the representation of hackrs (`hphp/hack/src/hackrs`),
//! which folds the classes: these are its types, under their OCaml names.
//!
//! | OCaml | Rust |
//! |---|---|
//! | `subst_context` | `ty::decl::SubstContext<R>` |
//! | `source_type` | `oxidized::decl_defs::SourceType` |
//! | `decl_error` | `ty::decl_error::DeclError<BPos>` (`Cyclic_class_def`'s stack is a list, in increasing order) |
//! | `element` | `ty::decl::FoldedElement` |
//! | `decl_class_type` | `Arc<ty::decl::FoldedClass<R>>`, as the decl stores keep it (also `crate::decl_store::DeclClassType` and `crate::decl_env::DeclClassType`) |
//! | `class_requirements` | `folded_decl_provider::decl_requirements::ClassRequirements<R>` |
//!
//! The fields of `decl_class_type` that `ty::decl::FoldedClass` does not
//! have are computed from the others, as `Decl_folded_class.class_decl` sets
//! them: `dc_abstract` is `FoldedClass::is_abstract` and `dc_need_init` is
//! `FoldedClass::has_concrete_constructor`.

use std::sync::Arc;

use oxidized::xhp_attribute::XhpAttribute;
use pos::BPos;

use crate::ctx::R;
use crate::exception;
use crate::hack_event_logger;
use crate::hh_logger;
use crate::relative_path;
use crate::relative_path::RelativePath;
use crate::typing_defs_flags;

/// Exception representing not finding a class during decl
///
/// `exception Decl_not_found of string`: it is caught far from where it is
/// raised (by the workers and the servers), so it is the payload of a panic:
/// `std::panic::panic_any(DeclNotFound(..))` raises it, and
/// `std::panic::catch_unwind` with a downcast catches it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeclNotFound(pub String);

impl std::fmt::Display for DeclNotFound {
    /// `Printexc.to_string (Decl_not_found s)`
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Decl_defs.Decl_not_found({:?})", self.0)
    }
}

impl std::error::Error for DeclNotFound {}

pub fn raise_decl_not_found(path: Option<&RelativePath>, name: &str) -> ! {
    hack_event_logger::decl_consistency_bug(path, None, Some(name), "Decl_not_found");
    let err_str = format!(
        "{} not found in {}",
        name,
        match path {
            None => "_".to_string(),
            Some(path) => relative_path::to_absolute(path),
        }
    );
    hh_logger::log(&format!(
        "Decl_not_found: {}\n{}",
        err_str,
        exception::clean_stack(&exception::get_current_callstack_string(99))
    ));
    std::panic::panic_any(DeclNotFound(err_str))
}

/// A substitution context contains all the information necessary for
/// changing the type of an inherited class element to the class that is
/// inheriting the class element. It's best illustrated via an example.
///
/// ```text
/// class A<Ta1, Ta2> { public function test(Ta1 $x, Ta2 $y): void {} }
///
/// class B<Tb> extends A<Tb, int> {}
///
/// class C extends B<string> {}
/// ```
///
/// The method `A::test()` has the type (function(Ta1, Ta2): void) in the
/// context of class A. However in the context of class B, it will have type
/// (function(Tb, int): void).
///
/// The substitution that leads to this change is [Ta1 -> Tb, Ta2 -> int],
/// which will produce a new type in the context of class B. It's subst_context
/// would then be:
///
/// ```text
/// { sc_subst            = [Ta1 -> Tb, Ta2 -> int];
///   sc_class_context    = 'B';
///   sc_from_req_extends = false;
/// }
/// ```
///
/// The `sc_from_req_extends` field is set to true if the context was inherited
/// via a require extends type. This information is relevant when folding
/// `dc_substs` during inheritance. See Decl_inherit module.
pub type SubstContext = ty::decl::SubstContext<R>;

/// `source_type`
pub use oxidized::decl_defs::SourceType;

/// `decl_error`
pub type DeclError = ty::decl_error::DeclError<BPos>;

/// `element`
pub type Element = ty::decl::FoldedElement;

/// `decl_class_type`
pub type DeclClassType = Arc<ty::decl::FoldedClass<R>>;

/// `class_requirements`
pub type ClassRequirements = folded_decl_provider::decl_requirements::ClassRequirements<R>;

pub fn get_elt_abstract(elt: &Element) -> bool {
    typing_defs_flags::class_elt::is_abstract(elt.flags)
}

pub fn get_elt_final(elt: &Element) -> bool {
    typing_defs_flags::class_elt::is_final(elt.flags)
}

pub fn get_elt_lsb(elt: &Element) -> bool {
    typing_defs_flags::class_elt::has_lsb(elt.flags)
}

/// Whether a class element comes from a `require extends`.
pub fn get_elt_synthesized(elt: &Element) -> bool {
    typing_defs_flags::class_elt::is_synthesized(elt.flags)
}

pub fn get_elt_xhp_attr(elt: &Element) -> Option<XhpAttribute> {
    typing_defs_flags::class_elt::get_xhp_attr(elt.flags)
}

pub fn get_elt_needs_init(elt: &Element) -> bool {
    typing_defs_flags::class_elt::needs_init(elt.flags)
}

pub fn set_elt_synthesized(elt: Element) -> Element {
    Element {
        flags: typing_defs_flags::class_elt::set_synthesized(elt.flags),
        ..elt
    }
}

pub fn reset_elt_superfluous_override(elt: Element) -> Element {
    Element {
        flags: typing_defs_flags::class_elt::reset_superfluous_override(elt.flags),
        ..elt
    }
}

#[cfg(test)]
mod tests {
    use oxidized::typing_defs_flags::ClassEltFlags;
    use pos::TypeName;
    use ty::decl::CeVisibility;

    use super::*;

    fn elt(flags: ClassEltFlags) -> Element {
        Element {
            flags,
            origin: TypeName::new("\\C"),
            visibility: CeVisibility::Public,
            deprecated: None,
            sealed_allowlist: None,
            overlapping_tparams: None,
            package_requirement: None,
        }
    }

    #[test]
    fn flags_of_elements() {
        let e = elt(ClassEltFlags::ABSTRACT | ClassEltFlags::SUPERFLUOUS_OVERRIDE);
        assert!(get_elt_abstract(&e));
        assert!(!get_elt_final(&e) && !get_elt_lsb(&e) && !get_elt_needs_init(&e));
        assert!(!get_elt_synthesized(&e));
        assert_eq!(get_elt_xhp_attr(&e), None);
        let e = set_elt_synthesized(e);
        assert!(get_elt_synthesized(&e) && get_elt_abstract(&e));
        let e = reset_elt_superfluous_override(e);
        assert_eq!(
            e.flags,
            ClassEltFlags::ABSTRACT | ClassEltFlags::SYNTHESIZED
        );
    }

    #[test]
    fn decl_not_found_is_raised_as_a_panic() {
        let res = std::panic::catch_unwind(|| raise_decl_not_found(None, "\\Nope"));
        let payload = res.unwrap_err();
        let DeclNotFound(s) = payload.downcast_ref::<DeclNotFound>().unwrap();
        assert_eq!(s, "\\Nope not found in _");
    }
}
