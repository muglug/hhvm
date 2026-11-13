// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `class_parent_check.ml`. See `hh/PORTING.md`.

use oxidized::aast;
use oxidized::aast::RequireKind;
use oxidized::naming_phase_error::NamingPhaseError;
use oxidized::nast_check_error::NastCheckError;
use oxidized::nast_check_error::Verb;

use crate::ast_defs;
use crate::decl_entry;
use crate::diagnostics_state;
use crate::folded_class as cls;
use crate::pos_or_decl;
use crate::tast;
use crate::tast_env;
use crate::tast_visitor;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error_utils;
use crate::typing_warning;

/// `Diagnostics.add_diagnostic (Nast_check_error.to_user_diagnostic err)`
fn add_nast_check_error(err: NastCheckError) {
    if let Some(diagnostic) = crate::naming_errors::to_diagnostic(NamingPhaseError::NastCheck(err))
    {
        diagnostics_state::add_diagnostic(diagnostic)
    }
}

/// `Aast.split_reqs`: the `require extends`, `require implements`,
/// `require class` and `require this as` hints, each in the order of the
/// class.
fn split_reqs(
    c_reqs: &[aast::ClassReq],
) -> (
    Vec<&aast::Hint>,
    Vec<&aast::Hint>,
    Vec<&aast::Hint>,
    Vec<&aast::Hint>,
) {
    let mut extends = vec![];
    let mut implements = vec![];
    let mut class_ = vec![];
    let mut this_as = vec![];
    for aast::ClassReq(h, require_kind) in c_reqs {
        match require_kind {
            RequireKind::RequireExtends => extends.push(h),
            RequireKind::RequireImplements => implements.push(h),
            RequireKind::RequireClass => class_.push(h),
            RequireKind::RequireThisAs => this_as.push(h),
        }
    }
    (extends, implements, class_, this_as)
}

pub fn check_is_class(
    env: &tast_env::Env,
    require_constraint_check: Option<RequireKind>,
    hint: &aast::Hint,
) {
    let aast::Hint(p, h) = hint;
    let (is_req_class_check, is_req_this_as_check) = match require_constraint_check {
        Some(RequireKind::RequireClass) => (true, false),
        Some(RequireKind::RequireThisAs) => (false, true),
        _ => (false, false),
    };
    match &**h {
        aast::Hint_::Happly(ast_defs::Id(_, name), _) => match tast_env::get_class(env, name) {
            decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {}
            decl_entry::T::Found(cls) => {
                let kind = cls::kind(&cls);
                let name = cls::name(&cls);
                let is_interface = ast_defs::is_c_interface(cls::kind(&cls));
                if ast_defs::is_c_class(kind) {
                    if cls::final_(&cls) && !is_req_class_check {
                        add_nast_check_error(NastCheckError::RequiresFinalClass {
                            pos: p.clone(),
                            name,
                            is_req_this_as_check,
                        })
                    } else if cls::final_(&cls) && is_req_this_as_check {
                        add_nast_check_error(NastCheckError::RequiresFinalClass {
                            pos: p.clone(),
                            name,
                            is_req_this_as_check,
                        })
                    }
                } else {
                    add_nast_check_error(NastCheckError::RequiresNonClass {
                        pos: p.clone(),
                        name,
                        kind: ast_defs::string_of_classish_kind(kind),
                        is_interface,
                        is_req_this_as_check,
                    })
                }
            }
        },
        aast::Hint_::Habstr(name) => add_nast_check_error(NastCheckError::RequiresNonClass {
            pos: p.clone(),
            name: name.clone(),
            kind: "a generic".to_string(),
            is_interface: false,
            is_req_this_as_check,
        }),
        _ => add_nast_check_error(NastCheckError::RequiresNonClass {
            pos: p.clone(),
            name: "This".to_string(),
            kind: "an invalid type hint".to_string(),
            is_interface: false,
            is_req_this_as_check,
        }),
    }
}

pub fn check_is_interface((env, error_verb): (&tast_env::Env, Verb), hint: &aast::Hint) {
    let aast::Hint(p, h) = hint;
    match &**h {
        aast::Hint_::Happly(ast_defs::Id(_, name), _) => match tast_env::get_class(env, name) {
            decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {}
            decl_entry::T::Found(cls) if ast_defs::is_c_interface(cls::kind(&cls)) => {}
            decl_entry::T::Found(cls) => add_nast_check_error(NastCheckError::NonInterface {
                pos: p.clone(),
                name: cls::name(&cls),
                verb: error_verb,
            }),
        },
        aast::Hint_::Habstr(_) => add_nast_check_error(NastCheckError::NonInterface {
            pos: p.clone(),
            name: "generic".to_string(),
            verb: error_verb,
        }),
        _ => add_nast_check_error(NastCheckError::NonInterface {
            pos: p.clone(),
            name: "invalid type hint".to_string(),
            verb: error_verb,
        }),
    }
}

pub fn check_is_trait(env: &tast_env::Env, hint: &aast::Hint) {
    let aast::Hint(p, h) = hint;
    match &**h {
        aast::Hint_::Happly(ast_defs::Id(_, name), _) => {
            let type_info = tast_env::get_class(env, name);
            match type_info {
                decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {}
                decl_entry::T::Found(cls) if ast_defs::is_c_trait(cls::kind(&cls)) => {}
                decl_entry::T::Found(cls) => {
                    let name = cls::name(&cls);
                    let kind = cls::kind(&cls);
                    add_nast_check_error(NastCheckError::UsesNonTrait {
                        pos: p.clone(),
                        name,
                        kind: ast_defs::string_of_classish_kind(kind),
                    })
                }
            }
        }
        _ => panic!("assertion failure: trait isn't an Happly"),
    }
}

pub fn hint_happly_to_string(h: &aast::Hint_) -> Option<String> {
    match h {
        aast::Hint_::Happly(ast_defs::Id(_, name), _) => Some(name.clone()),
        _ => None,
    }
}

pub fn duplicated_used_traits(env: &Env, c: &tast::Class_) {
    let mut traits = base_hashtbl::StringMultiTable::create();
    for aast::Hint(p, h) in &c.uses {
        match hint_happly_to_string(h) {
            Some(s) => traits.add_multi(s, p.clone()),
            None => {}
        }
    }
    traits.iteri(|key, data| {
        if data.len() > 1 {
            let ast_defs::Id(pos, class_name) = &c.name;
            typing_error_utils::add_typing_error(
                &typing_error::primary(typing_error::primary::T::Trait_reuse_inside_class {
                    class_name: class_name.clone(),
                    pos: pos.clone(),
                    trait_name: key.to_string(),
                    // `List.rev_map data ~f:Pos_or_decl.of_raw_pos`
                    occurrences: data
                        .iter()
                        .rev()
                        .map(|p| pos_or_decl::of_raw_pos(p.clone()))
                        .collect(),
                }),
                env,
            )
        }
    })
}

pub fn check_redundant_require_this_as(
    env: &tast_env::Env,
    c: &tast::Class_,
    req_this_as: &[&aast::Hint],
) {
    // Only check for traits
    if !ast_defs::is_c_trait(c.kind) {
    } else {
        let ast_defs::Id(_, trait_name) = &c.name;
        for aast::Hint(p, h) in req_this_as.iter().copied() {
            match &**h {
                aast::Hint_::Happly(ast_defs::Id(_, class_name), _) => {
                    match tast_env::get_class(env, class_name) {
                        decl_entry::T::Found(cls) => {
                            // Check if the class uses this trait (directly or transitively)
                            if !cls::has_ancestor(&cls, trait_name) {
                                // Class does not use the trait, emit warning
                                tast_env::add_warning(
                                    env,
                                    (
                                        p.clone(),
                                        typing_warning::Kind::Redundant_require_this_as,
                                        typing_warning::redundant_require_this_as::T {
                                            trait_name: trait_name.clone(),
                                            class_name: class_name.clone(),
                                        },
                                    ),
                                )
                            }
                        }
                        _ => {}
                    }
                }
                _ => {}
            }
        }
    }
}

/// The object `handler`.
struct ClassParentCheck;

impl<'a> tast_visitor::Handler<'a> for ClassParentCheck {
    fn at_class_(&mut self, env: &tast_env::Env, c: &'a tast::Class_) {
        let (req_extends, req_implements, req_class, req_this_as) = split_reqs(&c.reqs);
        for h in &c.uses {
            check_is_trait(env, h)
        }
        duplicated_used_traits(env, c);
        for h in req_extends {
            check_is_class(env, None, h)
        }
        for h in &c.implements {
            check_is_interface((env, Verb::Vimplement), h)
        }
        for h in req_implements {
            check_is_interface((env, Verb::VreqImplement), h)
        }
        for h in req_class {
            check_is_class(env, Some(RequireKind::RequireClass), h)
        }
        for h in req_this_as.iter().copied() {
            check_is_class(env, Some(RequireKind::RequireThisAs), h)
        }
        // Check for redundant require this as
        check_redundant_require_this_as(env, c, &req_this_as)
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(ClassParentCheck)
}

/// A table of Base (`Core.Hashtbl.create (module String)`) filled with
/// `Hashtbl.add_multi` and read with `Hashtbl.iteri`, whose order of
/// iteration shows in the order the TAST checks report errors
/// (`duplicated_used_traits` here, `Duplicate_properties.handler`).
///
/// `Base.Hashtbl` is an array of buckets: a key goes in bucket
/// `String.hash key land (length - 1)`, and each bucket is an AVL tree
/// ordered by `String.compare`. The array starts with one bucket
/// (`?size` defaults to 0, which is rounded up to 1) and doubles when a new
/// key makes the number of keys exceed its length, so a table of `n` keys has
/// `ceil_pow2 n` buckets. `iteri` goes through the buckets in order and
/// through each tree in increasing order of the keys. `String.hash` is
/// `Base_hash_string`: MurmurHash3's mix of the string (OCaml's
/// `caml_hash_mix_string` with seed 0) and its final mix, masked to 30 bits
/// (the value `Stdlib.Hashtbl.hash` gives a string).
pub(crate) mod base_hashtbl {
    use std::collections::BTreeMap;

    /// `Base_hash_string`
    pub fn hash_string(s: &[u8]) -> u32 {
        fn mix(h: u32, d: u32) -> u32 {
            let d = d.wrapping_mul(0xcc9e2d51);
            let d = d.rotate_left(15);
            let d = d.wrapping_mul(0x1b873593);
            let h = h ^ d;
            let h = h.rotate_left(13);
            h.wrapping_mul(5).wrapping_add(0xe6546b64)
        }
        // `caml_hash_mix_string`
        let mut h: u32 = 0;
        let len = s.len();
        let mut i = 0;
        while i + 4 <= len {
            let w = u32::from_le_bytes([s[i], s[i + 1], s[i + 2], s[i + 3]]);
            h = mix(h, w);
            i += 4;
        }
        let mut w: u32 = 0;
        let rest = len & 3;
        if rest == 3 {
            w = (s[i + 2] as u32) << 16;
        }
        if rest >= 2 {
            w |= (s[i + 1] as u32) << 8;
        }
        if rest >= 1 {
            w |= s[i] as u32;
            h = mix(h, w);
        }
        h ^= len as u32;
        // `FINAL_MIX`
        h ^= h >> 16;
        h = h.wrapping_mul(0x85ebca6b);
        h ^= h >> 13;
        h = h.wrapping_mul(0xc2b2ae35);
        h ^= h >> 16;
        h & 0x3FFF_FFFF
    }

    /// `(string, 'a list) Hashtbl.t`, filled by `add_multi`.
    pub struct StringMultiTable<V> {
        /// The list of each key, head first.
        bindings: BTreeMap<String, Vec<V>>,
    }

    impl<V> StringMultiTable<V> {
        /// `Hashtbl.create (module String)`
        pub fn create() -> Self {
            StringMultiTable {
                bindings: BTreeMap::new(),
            }
        }

        /// `Hashtbl.add_multi t ~key ~data`: `data` goes at the head of the
        /// list of `key`.
        pub fn add_multi(&mut self, key: String, data: V) {
            self.bindings.entry(key).or_default().insert(0, data)
        }

        /// `Hashtbl.iteri t ~f:(fun ~key ~data -> ...)`, in Base's order.
        pub fn iteri(&self, mut f: impl FnMut(&str, &[V])) {
            let n = self.bindings.len();
            if n == 0 {
                return;
            }
            let buckets = n.next_power_of_two() as u32;
            let mut keys: Vec<(u32, &String)> = self
                .bindings
                .keys()
                .map(|k| (hash_string(k.as_bytes()) & (buckets - 1), k))
                .collect();
            // By bucket, then by key (`String.compare`, the order of the
            // `BTreeMap`); the sort is stable.
            keys.sort_by_key(|(slot, _)| *slot);
            for (_, k) in keys {
                f(k, &self.bindings[k])
            }
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn hash_string_is_ocaml_hash() {
            // `Hashtbl.hash s` in OCaml 5.1.1.
            assert_eq!(hash_string(b""), 0);
            assert_eq!(hash_string(b"a"), 721651713);
            assert_eq!(hash_string(b"abcd"), 65890154);
            assert_eq!(hash_string(b"\\T1"), 754484068);
            assert_eq!(hash_string(b"\\Foo\\Bar"), 558758832);
            assert_eq!(hash_string(b"prop"), 709159502);
            assert_eq!(hash_string(b"x"), 780510073);
        }

        #[test]
        fn iteration_order() {
            let mut t = StringMultiTable::create();
            for (k, v) in [("a", 1), ("x", 2), ("a", 3), ("prop", 4)] {
                t.add_multi(k.to_string(), v)
            }
            // Three keys: four buckets. "a" is in bucket 1, "x" in bucket 1,
            // "prop" in bucket 2.
            let mut seen = vec![];
            t.iteri(|k, d| seen.push((k.to_string(), d.to_vec())));
            assert_eq!(
                seen,
                vec![
                    ("a".to_string(), vec![3, 1]),
                    ("x".to_string(), vec![2]),
                    ("prop".to_string(), vec![4]),
                ]
            );
        }
    }
}
