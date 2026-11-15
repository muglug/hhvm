// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `decl/decl_compare.ml`. See `hh/PORTING.md`.
//!
//! Module used when we want to figure out what has changed.
//! 1) The user modifies a file
//! 2) We compute the type of the file (cf typing_redecl_service.ml)
//! 3) We compare the old type and the new type of the class (or function)
//!    to see if anything has changed. This is where the code of this module
//!    comes into play. This code compares the old and the new class type
//!    and computes the set of dependencies if something needs to be
//!    either redeclared or checked again.
//!
//! # Data
//!
//! `File_info.names` is `oxidized::file_info::Names` (whose sets are
//! `BTreeSet`s; the `VersionedSSet`s built from them are `s_set::T`s).
//! A folded class (`Decl_heap.Class.t`) is a `ty::decl::FoldedClass<R>`, and
//! the values of the old decl maps the callers give (`Funs.value`,
//! `Typedef.t`, `GConsts.value`, `Modules.value`) are the `Arc`s of
//! `crate::decl_provider` (`FunDecl`, `TypedefDecl`, `GconstDecl`,
//! `ModuleDecl`), as the decl stores of a `Ctx` keep them.
//!
//! # Backends
//!
//! The functions that look up the new declarations match on
//! `Provider_backend.get ()`. The OCaml daemon and `hh_single_type_check` run
//! the `Shared_memory` backend (`rust_provider_backend` is turned off at
//! startup since `shm_use_sharded_hashtbl` is false): the branch ported is
//! `| _ -> Decl_heap.Funs.get fid` (and `Typedefs`, `GConsts`, `Modules`),
//! a read of the heap of shallow declarations without any lazy parse on a
//! miss. Those heaps are the decl stores of the `Ctx`, read directly
//! (`ctx.shallow_decls.get_*`).
//!
//! `Class_elt_diff` reads the member heaps of `Decl_heap` (`Props`,
//! `StaticProps`, `Methods`, `StaticMethods`, `Constructors`), old and new.
//! They have no Rust counterpart either (the decl stores of a `Ctx` have no
//! member heaps, and nothing is "oldified": see the design of the server
//! layer, 7.4), so the functions that read them, in the private module
//! `decl_heap` below, are `todo!`. Nothing calls `Class_elt_diff.compare` in
//! the OCaml.

use std::collections::BTreeMap;
use std::collections::BTreeSet;

use oxidized::file_info::Names;
use ty::decl::FoldedClass;

use crate::ctx::R;
use crate::decl_pos_utils;
use crate::decl_provider::FunDecl;
use crate::decl_provider::GconstDecl;
use crate::decl_provider::ModuleDecl;
use crate::decl_provider::TypedefDecl;
use crate::fanout;
use crate::file_info;
use crate::format;
use crate::format::Formatter;
use crate::provider_context;
use crate::s_map;
use crate::s_set;
use crate::typing_deps;
use crate::typing_deps::dep;
use crate::typing_deps::dep_set;
use crate::typing_deps::visited_set;
use crate::typing_deps_mode;

/// `S_map.find`, which raises `Not_found`.
fn s_map_find<'a, A>(x: &str, m: &'a s_map::T<A>) -> &'a A {
    match m.get(x) {
        Some(v) => v,
        None => panic!("Not_found"),
    }
}

/// `S_set` of the `BTreeSet` of an `oxidized` record.
fn s_set_of(set: &BTreeSet<String>) -> s_set::T {
    set.iter().cloned().collect()
}

/// ppx_deriving's printer of a record: `"@[<2>{ "`, the fields separated by
/// `";@ "`, then `"@ }@]"`; a field is `"@[%s =@ "`, its value, `"@]"`.
fn pp_record(fmt: &mut Formatter, fields: &[(&str, &dyn Fn(&mut Formatter))]) {
    format::pp_open_box(fmt, 2);
    format::pp_print_string(fmt, "{ ");
    for (i, (name, pp_value)) in fields.iter().enumerate() {
        if i > 0 {
            format::pp_print_char(fmt, ';');
            format::pp_print_space(fmt);
        }
        format::pp_open_box(fmt, 0);
        format::pp_print_string(fmt, name);
        format::pp_print_string(fmt, " =");
        format::pp_print_space(fmt);
        pp_value(fmt);
        format::pp_close_box(fmt);
    }
    format::pp_print_space(fmt);
    format::pp_print_char(fmt, '}');
    format::pp_close_box(fmt);
}

pub mod versioned_names {
    use super::*;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct T {
        pub old_names: file_info::old_names::T,
        pub new_names: Names,
    }

    /// `[@@deriving show]`
    pub fn pp(fmt: &mut Formatter, x: &T) {
        pp_record(
            fmt,
            &[
                ("Decl_compare.VersionedNames.old_names", &|fmt| {
                    file_info::old_names::pp(fmt, &x.old_names)
                }),
                ("new_names", &|fmt| file_info::pp_names(fmt, &x.new_names)),
            ],
        )
    }

    /// `[@@deriving show]`
    pub fn show(x: &T) -> String {
        format::asprintf(|fmt| pp(fmt, x))
    }

    /// `empty` (a value in OCaml)
    pub fn empty() -> T {
        T {
            old_names: file_info::old_names::empty(),
            new_names: file_info::empty_names(),
        }
    }

    pub fn make_unchanged(names: Names) -> T {
        T {
            old_names: file_info::old_names::of_names(&names),
            new_names: names,
        }
    }

    pub fn merge(left: &T, right: &T) -> T {
        let T {
            old_names: left_old_names,
            new_names: left_new_names,
        } = left;
        let T {
            old_names: right_old_names,
            new_names: right_new_names,
        } = right;
        // Record fields are evaluated from right to left.
        let new_names = file_info::merge_names(left_new_names, right_new_names);
        let old_names = file_info::old_names::merge(left_old_names, right_old_names);
        T {
            old_names,
            new_names,
        }
    }
}

pub mod versioned_s_set {
    use super::*;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct T {
        pub old: s_set::T,
        pub new_: s_set::T,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct Diff {
        pub removed: s_set::T,
        pub kept: s_set::T,
        pub added: s_set::T,
    }

    /// `empty` (a value in OCaml)
    pub fn empty() -> T {
        T {
            old: s_set::T::new(),
            new_: s_set::T::new(),
        }
    }

    fn project(project: impl Fn(&Names) -> s_set::T, names: &versioned_names::T) -> T {
        let versioned_names::T {
            old_names,
            new_names,
        } = names;
        // Record fields are evaluated from right to left.
        let new_ = project(new_names);
        let old = project(&file_info::old_names::to_names(old_names));
        T { old, new_ }
    }

    pub fn get_classes(names: &versioned_names::T) -> T {
        project(|names| s_set_of(&names.classes), names)
    }

    pub fn merge(left: &T, right: &T) -> T {
        let T {
            old: old_left,
            new_: new_left,
        } = left;
        let T {
            old: old_right,
            new_: new_right,
        } = right;
        T {
            old: old_left.clone().union(old_right.clone()),
            new_: new_left.clone().union(new_right.clone()),
        }
    }

    /// `empty_diff` (a value in OCaml)
    fn empty_diff() -> Diff {
        Diff {
            removed: s_set::T::new(),
            kept: s_set::T::new(),
            added: s_set::T::new(),
        }
    }

    pub fn diff(t: &T) -> Diff {
        let T { old, new_ } = t;
        // `S_set.fold` visits the elements in increasing order.
        let mut diff = empty_diff();
        for old_name in old.iter() {
            // `S_set.find_opt old_name new_`
            let found = if new_.contains(old_name) {
                Some(old_name.clone())
            } else {
                None
            };
            match found {
                None => diff.removed = diff.removed.update(old_name.clone()),
                Some(n) => diff.kept = diff.kept.update(n),
            }
        }
        // `S_set.diff new_ old`
        let added: s_set::T = new_.iter().filter(|x| !old.contains(*x)).cloned().collect();
        Diff { added, ..diff }
    }

    pub fn diff_cardinal(d: &Diff) -> isize {
        let Diff {
            removed,
            kept,
            added,
        } = d;
        removed.len() as isize + kept.len() as isize + added.len() as isize
    }
}

pub mod versioned_file_info {
    use super::*;

    #[derive(Clone, Debug, PartialEq, Eq)]
    struct T {
        funs: versioned_s_set::T,
        types: versioned_s_set::T,
        gconsts: versioned_s_set::T,
        modules: versioned_s_set::T,
    }

    fn transpose(names: &versioned_names::T) -> T {
        let versioned_names::T {
            old_names,
            new_names,
        } = names;
        let Names {
            funs: old_funs,
            classes: _,
            types: old_types,
            consts: old_gconsts,
            modules: old_modules,
        } = file_info::old_names::to_names(old_names);
        let Names {
            funs: new_funs,
            classes: _,
            types: new_types,
            consts: new_gconsts,
            modules: new_modules,
        } = new_names;
        T {
            funs: versioned_s_set::T {
                old: s_set_of(&old_funs),
                new_: s_set_of(new_funs),
            },
            types: versioned_s_set::T {
                old: s_set_of(&old_types),
                new_: s_set_of(new_types),
            },
            gconsts: versioned_s_set::T {
                old: s_set_of(&old_gconsts),
                new_: s_set_of(new_gconsts),
            },
            modules: versioned_s_set::T {
                old: s_set_of(&old_modules),
                new_: s_set_of(new_modules),
            },
        }
    }

    pub mod diff {
        use super::*;

        #[derive(Clone, Debug, PartialEq, Eq)]
        pub struct T {
            pub funs: versioned_s_set::Diff,
            pub types: versioned_s_set::Diff,
            pub gconsts: versioned_s_set::Diff,
            pub modules: versioned_s_set::Diff,
        }
    }

    fn diff(t: &T) -> diff::T {
        let T {
            funs,
            types,
            gconsts,
            modules,
        } = t;
        // Record fields are evaluated from right to left.
        let modules = versioned_s_set::diff(modules);
        let gconsts = versioned_s_set::diff(gconsts);
        let types = versioned_s_set::diff(types);
        let funs = versioned_s_set::diff(funs);
        diff::T {
            funs,
            types,
            gconsts,
            modules,
        }
    }

    pub fn diff_names(names: &versioned_names::T) -> diff::T {
        diff(&transpose(names))
    }
}

/// Given two classes give back the set of functions or classes that need
/// to be rechecked
pub mod class_diff {
    use std::hash::Hash;

    use super::*;

    fn smap_left<K: AsRef<str> + Eq + Hash, V: PartialEq>(
        s1: &hash::IndexMap<K, V>,
        s2: &hash::IndexMap<K, V>,
    ) -> s_set::T {
        // `S_map.fold`; the order of the bindings does not matter, as they are
        // added to a set.
        let mut diff = s_set::T::new();
        for (x, ty1) in s1.iter() {
            let ty2 = s2.get(x);
            diff = match ty2 {
                Some(ty2) => {
                    // `Poly.( = )`
                    if ty1 == ty2 {
                        diff
                    } else {
                        diff.update(x.as_ref().to_string())
                    }
                }
                None => diff.update(x.as_ref().to_string()),
            };
        }
        diff
    }

    fn smap<K: AsRef<str> + Eq + Hash, V: PartialEq>(
        s1: &hash::IndexMap<K, V>,
        s2: &hash::IndexMap<K, V>,
    ) -> s_set::T {
        // The arguments are evaluated from right to left.
        let right = smap_left(s2, s1);
        let left = smap_left(s1, s2);
        left.union(right)
    }

    pub fn compare(class1: &FoldedClass<R>, class2: &FoldedClass<R>) -> bool {
        let is_unchanged = true;
        // compare class constants
        let consts_diff = smap(&class1.consts, &class2.consts);
        let is_unchanged = is_unchanged && consts_diff.is_empty();
        // compare class members
        let props_diff = smap(&class1.props, &class2.props);
        let is_unchanged = is_unchanged && props_diff.is_empty();
        // compare class static members
        let sprops_diff = smap(&class1.static_props, &class2.static_props);
        let is_unchanged = is_unchanged && sprops_diff.is_empty();
        // compare class methods
        let methods_diff = smap(&class1.methods, &class2.methods);
        let is_unchanged = is_unchanged && methods_diff.is_empty();
        // compare class static methods
        let smethods_diff = smap(&class1.static_methods, &class2.static_methods);
        let is_unchanged = is_unchanged && smethods_diff.is_empty();
        // compare class constructors
        let ctor_diff = class1.constructor != class2.constructor;
        let is_unchanged = is_unchanged && !ctor_diff;
        // compare class type constants
        let typeconsts_diff = smap(&class1.type_consts, &class2.type_consts);
        is_unchanged && typeconsts_diff.is_empty()
    }
}

/// Given two classes give back the set of functions or classes that need
/// to be rechecked because the type of their member changed
pub mod class_elt_diff {
    use std::hash::Hash;

    use ty::decl::FoldedElement;

    use super::*;
    use crate::decl_heap::EltHeap;

    /// ``[> `Changed | `Unchanged ]``
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum ChangedOrUnchanged {
        Changed,
        Unchanged,
    }

    fn acc_diff(is_unchanged: ChangedOrUnchanged, xmap: &s_map::T<()>) -> ChangedOrUnchanged {
        match is_unchanged {
            ChangedOrUnchanged::Unchanged if !xmap.is_empty() => ChangedOrUnchanged::Changed,
            x => x,
        }
    }

    fn diff_elts<H: EltHeap, K: AsRef<str> + Eq + Hash>(
        cid: &str,
        elts1: &hash::IndexMap<K, FoldedElement>,
        elts2: &hash::IndexMap<K, FoldedElement>,
        normalize: impl Fn(&H::Value) -> H::Value,
    ) -> s_map::T<()>
    where
        H::Value: PartialEq,
    {
        // `S_map.merge`: the bindings of both maps, by name. (The order in
        // which `merge` calls its function is not observable: the function
        // only reads heaps.)
        let elts1: BTreeMap<&str, &FoldedElement> =
            elts1.iter().map(|(k, v)| (k.as_ref(), v)).collect();
        let elts2: BTreeMap<&str, &FoldedElement> =
            elts2.iter().map(|(k, v)| (k.as_ref(), v)).collect();
        let names: BTreeSet<&str> = elts1.keys().chain(elts2.keys()).copied().collect();
        let mut result = s_map::T::new();
        for name in names {
            let elt1 = elts1.get(name);
            let elt2 = elts2.get(name);
            let key = (cid.to_string(), name.to_string());
            let match1 = match elt1 {
                Some(elt) => elt.origin.as_str() == cid,
                _ => false,
            };
            let match2 = match elt2 {
                Some(elt) => elt.origin.as_str() == cid,
                _ => false,
            };
            let changed = if match1 || match2 {
                // The components of the tuple are evaluated from right to
                // left.
                let new = H::get(&key);
                let old = H::get_old(&key);
                match (old, new) {
                    (None, _) | (_, None) => Some(()),
                    (Some(x1), Some(x2)) => {
                        let ty1 = normalize(&x1);
                        let ty2 = normalize(&x2);
                        if ty1 == ty2 { None } else { Some(()) }
                    }
                }
            } else {
                None
            };
            if let Some(()) = changed {
                result.insert(name.to_string(), ());
            }
        }
        result
    }

    fn compare_props(
        class1: &FoldedClass<R>,
        class2: &FoldedClass<R>,
        acc: ChangedOrUnchanged,
    ) -> ChangedOrUnchanged {
        let cid = class1.name.as_str();
        let (elts1, elts2) = (&class1.props, &class2.props);
        let diff =
            diff_elts::<crate::decl_heap::Props, _>(cid, elts1, elts2, decl_pos_utils::normalize_sig::ty);
        acc_diff(acc, &diff)
    }

    fn compare_sprops(
        class1: &FoldedClass<R>,
        class2: &FoldedClass<R>,
        acc: ChangedOrUnchanged,
    ) -> ChangedOrUnchanged {
        let cid = class1.name.as_str();
        let (elts1, elts2) = (&class1.static_props, &class2.static_props);
        let diff = diff_elts::<crate::decl_heap::StaticProps, _>(
            cid,
            elts1,
            elts2,
            decl_pos_utils::normalize_sig::ty,
        );
        acc_diff(acc, &diff)
    }

    fn compare_meths(
        class1: &FoldedClass<R>,
        class2: &FoldedClass<R>,
        acc: ChangedOrUnchanged,
    ) -> ChangedOrUnchanged {
        let cid = class1.name.as_str();
        let (elts1, elts2) = (&class1.methods, &class2.methods);
        let diff = diff_elts::<crate::decl_heap::Methods, _>(
            cid,
            elts1,
            elts2,
            decl_pos_utils::normalize_sig::fun_elt,
        );
        acc_diff(acc, &diff)
    }

    fn compare_smeths(
        class1: &FoldedClass<R>,
        class2: &FoldedClass<R>,
        acc: ChangedOrUnchanged,
    ) -> ChangedOrUnchanged {
        let cid = class1.name.as_str();
        let (elts1, elts2) = (&class1.static_methods, &class2.static_methods);
        let diff = diff_elts::<crate::decl_heap::StaticMethods, _>(
            cid,
            elts1,
            elts2,
            decl_pos_utils::normalize_sig::fun_elt,
        );
        acc_diff(acc, &diff)
    }

    fn compare_cstrs(class1: &FoldedClass<R>, class2: &FoldedClass<R>) -> ChangedOrUnchanged {
        let cid = class1.name.as_str();
        let match1 = match &class1.constructor.elt {
            Some(elt) => elt.origin.as_str() == cid,
            _ => false,
        };
        let match2 = match &class2.constructor.elt {
            Some(elt) => elt.origin.as_str() == cid,
            _ => false,
        };
        if match1 || match2 {
            // The components of the tuple are evaluated from right to left.
            let new = crate::decl_heap::constructors::get(cid);
            let old = crate::decl_heap::constructors::get_old(cid);
            match (old, new) {
                (None, _) | (_, None) => ChangedOrUnchanged::Changed,
                (Some(fe1), Some(fe2)) => {
                    let fe1 = decl_pos_utils::normalize_sig::fun_elt(&fe1);
                    let fe2 = decl_pos_utils::normalize_sig::fun_elt(&fe2);
                    if fe1 == fe2 {
                        ChangedOrUnchanged::Unchanged
                    } else {
                        ChangedOrUnchanged::Changed
                    }
                }
            }
        } else {
            ChangedOrUnchanged::Unchanged
        }
    }

    pub fn compare(class1: &FoldedClass<R>, class2: &FoldedClass<R>) -> ChangedOrUnchanged {
        let acc = compare_cstrs(class1, class2);
        let acc = compare_props(class1, class2, acc);
        let acc = compare_sprops(class1, class2, acc);
        let acc = compare_meths(class1, class2, acc);
        compare_smeths(class1, class2, acc)
    }
}

pub fn get_extend_deps(
    mode: &typing_deps_mode::T,
    cid_hash: dep_set::Elt,
    acc: &dep_set::T,
) -> dep_set::T {
    typing_deps::get_extend_deps(mode, &mut visited_set::make(), cid_hash, acc)
}

fn add_fanout(
    make_dep: impl Fn(&str) -> dep::Variant,
    mode: &typing_deps_mode::T,
    id: &str,
    fanout_acc: fanout::T,
) -> fanout::T {
    fanout::add_fanout_of(mode, &make_dep(id), fanout_acc)
}

fn add_fun_fanout(mode: &typing_deps_mode::T, id: &str, fanout_acc: fanout::T) -> fanout::T {
    add_fanout(|id| dep::Variant::Fun(id.to_string()), mode, id, fanout_acc)
}

fn add_type_fanout(mode: &typing_deps_mode::T, id: &str, fanout_acc: fanout::T) -> fanout::T {
    add_fanout(
        |id| dep::Variant::Type(id.to_string()),
        mode,
        id,
        fanout_acc,
    )
}

fn add_gconst_fanout(mode: &typing_deps_mode::T, id: &str, fanout: fanout::T) -> fanout::T {
    let fanout = add_fanout(|id| dep::Variant::GConst(id.to_string()), mode, id, fanout);
    add_fanout(
        |id| dep::Variant::GConstName(id.to_string()),
        mode,
        id,
        fanout,
    )
}

fn add_module_fanout(mode: &typing_deps_mode::T, id: &str, fanout_acc: fanout::T) -> fanout::T {
    add_fanout(
        |id| dep::Variant::Module(id.to_string()),
        mode,
        id,
        fanout_acc,
    )
}

/// Determine which functions/classes have to be rechecked after comparing
/// the old and the new type signature of "fid" (function identifier).
fn get_fun_deps(
    ctx: &provider_context::T,
    mode: &typing_deps_mode::T,
    old_funs: &s_map::T<Option<FunDecl>>,
    fid: &str,
    (fanout_acc, old_funs_missing): (fanout::T, isize),
) -> (fanout::T, isize) {
    // The components of the tuple are evaluated from right to left: the new
    // declaration is looked up before the old one.
    // `match Provider_backend.get () with ... | _ -> Decl_heap.*.get`
    let new = crate::decl_heap::funs::get(ctx, fid);
    let old = s_map_find(fid, old_funs);
    match (old, new) {
        // Note that we must include all dependencies even if we get the None, None
        // case. Due to the fact we can declare types lazily, there may be no
        // existing declaration in the old Decl_heap that corresponds to a function
        // `foo` in the AST. Then when the user deletes `foo`, the new Decl_heap
        // will also lack a definition of `foo`. Now we must recheck all the use
        // sites of `foo` to make sure there are no dangling references.
        (None, _) | (_, None) => {
            let fanout_acc = add_fun_fanout(mode, fid, fanout_acc);
            (fanout_acc, old_funs_missing + 1)
        }
        (Some(fe1), Some(fe2)) => {
            let fe1 = decl_pos_utils::normalize_sig::fun_elt(fe1);
            let fe2 = decl_pos_utils::normalize_sig::fun_elt(&fe2);
            if fe1 == fe2 {
                (fanout_acc, old_funs_missing)
            } else {
                let fanout_acc = add_fun_fanout(mode, fid, fanout_acc);
                (fanout_acc, old_funs_missing)
            }
        }
    }
}

pub fn get_funs_deps(
    ctx: &provider_context::T,
    old_funs: &s_map::T<Option<FunDecl>>,
    funs: &versioned_s_set::Diff,
) -> (fanout::T, isize) {
    let mode = provider_context::get_deps_mode(ctx);
    let versioned_s_set::Diff {
        removed,
        kept,
        added,
    } = funs;
    let mut fanout = fanout::empty();
    for id in removed.iter() {
        fanout = add_fun_fanout(&mode, id, fanout);
    }
    for id in added.iter() {
        fanout = add_fun_fanout(&mode, id, fanout);
    }
    let mut acc = (fanout, 0);
    for fid in kept.iter() {
        acc = get_fun_deps(ctx, &mode, old_funs, fid, acc);
    }
    acc
}

/// Determine which functions/classes have to be rechecked after comparing
/// the old and the new typedef
fn get_type_deps(
    ctx: &provider_context::T,
    mode: &typing_deps_mode::T,
    old_types: &s_map::T<Option<TypedefDecl>>,
    tid: &str,
    (fanout_acc, old_types_missing): (fanout::T, isize),
) -> (fanout::T, isize) {
    // The components of the tuple are evaluated from right to left: the new
    // declaration is looked up before the old one.
    // `match Provider_backend.get () with ... | _ -> Decl_heap.*.get`
    let new = crate::decl_heap::typedefs::get(ctx, tid);
    let old = s_map_find(tid, old_types);
    match (old, new) {
        (None, _) | (_, None) => {
            let fanout_acc = add_type_fanout(mode, tid, fanout_acc);
            (fanout_acc, old_types_missing + 1)
        }
        (Some(tdef1), Some(tdef2)) => {
            let tdef1 = decl_pos_utils::normalize_sig::typedef(tdef1);
            let tdef2 = decl_pos_utils::normalize_sig::typedef(&tdef2);
            let is_same_signature = tdef1 == tdef2;
            if is_same_signature {
                (fanout_acc, old_types_missing)
            } else {
                let fanout_acc = add_type_fanout(mode, tid, fanout_acc);
                (fanout_acc, old_types_missing)
            }
        }
    }
}

pub fn get_types_deps(
    ctx: &provider_context::T,
    old_types: &s_map::T<Option<TypedefDecl>>,
    types: &versioned_s_set::Diff,
) -> (fanout::T, isize) {
    let mode = provider_context::get_deps_mode(ctx);
    let versioned_s_set::Diff {
        removed,
        kept,
        added,
    } = types;
    let mut fanout = fanout::empty();
    for id in removed.iter() {
        fanout = add_type_fanout(&mode, id, fanout);
    }
    for id in added.iter() {
        fanout = add_type_fanout(&mode, id, fanout);
    }
    let mut acc = (fanout, 0);
    for tid in kept.iter() {
        acc = get_type_deps(ctx, &mode, old_types, tid, acc);
    }
    acc
}

/// Determine which top level definitions have to be rechecked if the constant
/// changed.
fn get_gconst_deps(
    ctx: &provider_context::T,
    mode: &typing_deps_mode::T,
    old_gconsts: &s_map::T<Option<GconstDecl>>,
    cst_id: &str,
    (fanout_acc, old_gconsts_missing): (fanout::T, isize),
) -> (fanout::T, isize) {
    let cst1 = s_map_find(cst_id, old_gconsts);
    // `match Provider_backend.get () with ... | _ -> Decl_heap.*.get`
    let cst2 = crate::decl_heap::gconsts::get(ctx, cst_id);
    match (cst1, cst2) {
        (None, _) | (_, None) => {
            let fanout_acc = add_gconst_fanout(mode, cst_id, fanout_acc);
            (fanout_acc, old_gconsts_missing + 1)
        }
        (Some(cst1), Some(cst2)) => {
            // `Poly.( = )`, positions included: the constants are not
            // normalized.
            let is_same_signature = *cst1 == cst2;
            if is_same_signature {
                (fanout_acc, old_gconsts_missing)
            } else {
                let dep = dep::Variant::GConst(cst_id.to_string());
                let fanout_acc = fanout::add_fanout_of(mode, &dep, fanout_acc);
                (fanout_acc, old_gconsts_missing)
            }
        }
    }
}

pub fn get_gconsts_deps(
    ctx: &provider_context::T,
    old_gconsts: &s_map::T<Option<GconstDecl>>,
    gconsts: &versioned_s_set::Diff,
) -> (fanout::T, isize) {
    let mode = provider_context::get_deps_mode(ctx);
    let versioned_s_set::Diff {
        removed,
        kept,
        added,
    } = gconsts;
    let mut fanout = fanout::empty();
    for id in removed.iter() {
        fanout = add_gconst_fanout(&mode, id, fanout);
    }
    for id in added.iter() {
        fanout = add_gconst_fanout(&mode, id, fanout);
    }
    let mut acc = (fanout, 0);
    for cst_id in kept.iter() {
        acc = get_gconst_deps(ctx, &mode, old_gconsts, cst_id, acc);
    }
    acc
}

fn get_module_deps(
    ctx: &provider_context::T,
    mode: &typing_deps_mode::T,
    old_modules: &s_map::T<Option<ModuleDecl>>,
    mid: &str,
    (fanout_acc, old_modules_missing): (fanout::T, isize),
) -> (fanout::T, isize) {
    // The components of the tuple are evaluated from right to left: the new
    // declaration is looked up before the old one.
    // `match Provider_backend.get () with ... | _ -> Decl_heap.*.get`
    let new = crate::decl_heap::modules::get(ctx, mid);
    let old = s_map_find(mid, old_modules);
    match (old, new) {
        (None, _) | (_, None) => {
            let fanout_acc = add_module_fanout(mode, mid, fanout_acc);
            (fanout_acc, old_modules_missing + 1)
        }
        (Some(_), Some(_)) => (fanout_acc, old_modules_missing),
    }
}

pub fn get_modules_deps(
    ctx: &provider_context::T,
    old_modules: &s_map::T<Option<ModuleDecl>>,
    modules: &versioned_s_set::Diff,
) -> (fanout::T, isize) {
    let mode = provider_context::get_deps_mode(ctx);
    let versioned_s_set::Diff {
        removed,
        kept,
        added,
    } = modules;
    let mut fanout = fanout::empty();
    for id in removed.iter() {
        fanout = add_module_fanout(&mode, id, fanout);
    }
    for id in added.iter() {
        fanout = add_module_fanout(&mode, id, fanout);
    }
    let mut acc = (fanout, 0);
    for mid in kept.iter() {
        acc = get_module_deps(ctx, &mode, old_modules, mid, acc);
    }
    acc
}

#[cfg(test)]
mod tests {
    use oxidized::typechecker_options::TypecheckerOptions;

    use pos::TypeName;

    use super::*;
    use crate::decl_provider::testing::ctx_of;

    fn s(names: &[&str]) -> s_set::T {
        names.iter().map(|x| x.to_string()).collect()
    }

    fn b(names: &[&str]) -> BTreeSet<String> {
        names.iter().map(|x| x.to_string()).collect()
    }

    fn deps(vs: &[dep::Variant]) -> dep_set::T {
        dep_set::of_list(&vs.iter().map(dep::make).collect::<Vec<_>>())
    }

    /// `VersionedNames.pp` is ppx_deriving's printer of a record: the first
    /// field with the path of the module, boxes and breaks as ppx_deriving
    /// writes them.
    #[test]
    fn records_are_printed_as_ppx_deriving_prints_them() {
        let pp = |a: &str, b: &str| {
            format::asprintf(|fmt| {
                pp_record(
                    fmt,
                    &[
                        ("M.a", &|fmt| format::pp_print_string(fmt, a)),
                        ("b", &|fmt| format::pp_print_string(fmt, b)),
                    ],
                )
            })
        };
        assert_eq!(pp("1", "2"), "{ M.a = 1; b = 2 }");
        // `@[<2>{ `: a field that does not fit goes to the next line,
        // indented by 2.
        let x = "x".repeat(50);
        let y = "y".repeat(50);
        assert_eq!(pp(&x, &y), format!("{{ M.a = {x};\n  b = {y} }}"));
    }

    #[test]
    fn versioned_s_set_diff() {
        let t = versioned_s_set::T {
            old: s(&["a", "b", "c"]),
            new_: s(&["b", "c", "d", "e"]),
        };
        let d = versioned_s_set::diff(&t);
        assert_eq!(
            d,
            versioned_s_set::Diff {
                removed: s(&["a"]),
                kept: s(&["b", "c"]),
                added: s(&["d", "e"]),
            }
        );
        assert_eq!(versioned_s_set::diff_cardinal(&d), 5);
        let m = versioned_s_set::merge(
            &t,
            &versioned_s_set::T {
                old: s(&["z"]),
                new_: s(&[]),
            },
        );
        assert_eq!(m.old, s(&["a", "b", "c", "z"]));
        assert_eq!(m.new_, s(&["b", "c", "d", "e"]));
        assert_eq!(
            versioned_s_set::empty(),
            versioned_s_set::T {
                old: s(&[]),
                new_: s(&[]),
            }
        );
    }

    #[test]
    fn diff_of_the_names_of_a_file() {
        let names = versioned_names::T {
            old_names: file_info::old_names::of_names(&Names {
                funs: b(&["\\f", "\\g"]),
                classes: b(&["\\C"]),
                types: b(&["\\T"]),
                consts: b(&["\\X"]),
                modules: b(&[]),
            }),
            new_names: Names {
                funs: b(&["\\g", "\\h"]),
                classes: b(&["\\D"]),
                types: b(&[]),
                consts: b(&["\\X"]),
                modules: b(&["m"]),
            },
        };
        let d = versioned_file_info::diff_names(&names);
        assert_eq!(d.funs.removed, s(&["\\f"]));
        assert_eq!(d.funs.kept, s(&["\\g"]));
        assert_eq!(d.funs.added, s(&["\\h"]));
        assert_eq!(d.types.removed, s(&["\\T"]));
        assert_eq!(d.gconsts.kept, s(&["\\X"]));
        assert_eq!(d.modules.added, s(&["m"]));
        let classes = versioned_s_set::get_classes(&names);
        assert_eq!(classes.old, s(&["\\C"]));
        assert_eq!(classes.new_, s(&["\\D"]));
        assert_eq!(
            versioned_names::make_unchanged(names.new_names.clone()).old_names,
            file_info::old_names::of_names(&names.new_names)
        );
    }

    const OLD: &str = "<?hh
const int Y = 1;
function f(): int { return 1; }
function g(): int { return 1; }
function h(): int { return 1; }
type T = int;
type U = int;
const int X = 1;
new module m {}
";

    // `Y` unchanged (at the same position); `f` moved, `g` changed, `h`
    // removed, `i` added; `T` moved, `U` changed; `X` moved; `m` moved.
    const NEW: &str = "<?hh
const int Y = 1;

function f(): int { return 1; }
function g(): string { return ''; }
function i(): int { return 1; }
type  T = int;
type U = string;
 const int X = 1;
new module m {}
";

    #[test]
    fn fanout_of_funs_types_gconsts_modules() {
        let old_ctx = ctx_of(OLD, TypecheckerOptions::default());
        let new_ctx = ctx_of(NEW, TypecheckerOptions::default());
        let names = |l: &[&str]| -> Vec<String> { l.iter().map(|x| x.to_string()).collect() };

        let old_funs: s_map::T<Option<FunDecl>> = names(&["\\f", "\\g", "\\h"])
            .into_iter()
            .map(|n| (n.clone(), crate::decl_heap::funs::get(&old_ctx, &n)))
            .collect();
        let (fanout, missing) = get_funs_deps(
            &new_ctx,
            &old_funs,
            &versioned_s_set::Diff {
                removed: s(&["\\h"]),
                kept: s(&["\\f", "\\g"]),
                added: s(&["\\i"]),
            },
        );
        assert_eq!(missing, 0);
        assert_eq!(
            fanout.changed,
            deps(&[
                dep::Variant::Fun("\\g".to_string()),
                dep::Variant::Fun("\\h".to_string()),
                dep::Variant::Fun("\\i".to_string()),
            ])
        );
        // A kept function that is in neither version counts as missing.
        let old_missing: s_map::T<Option<FunDecl>> =
            [("\\h".to_string(), None)].into_iter().collect();
        let (fanout, missing) = get_funs_deps(
            &new_ctx,
            &old_missing,
            &versioned_s_set::Diff {
                removed: s(&[]),
                kept: s(&["\\h"]),
                added: s(&[]),
            },
        );
        assert_eq!(missing, 1);
        assert_eq!(
            fanout.changed,
            deps(&[dep::Variant::Fun("\\h".to_string())])
        );
        // `S_map.find` raises `Not_found` for a kept name without an old entry.
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                get_funs_deps(
                    &new_ctx,
                    &s_map::T::new(),
                    &versioned_s_set::Diff {
                        removed: s(&[]),
                        kept: s(&["\\f"]),
                        added: s(&[]),
                    },
                )
            }))
            .is_err()
        );

        let old_types: s_map::T<Option<TypedefDecl>> = names(&["\\T", "\\U"])
            .into_iter()
            .map(|n| (n.clone(), crate::decl_heap::typedefs::get(&old_ctx, &n)))
            .collect();
        let (fanout, missing) = get_types_deps(
            &new_ctx,
            &old_types,
            &versioned_s_set::Diff {
                removed: s(&[]),
                kept: s(&["\\T", "\\U"]),
                added: s(&[]),
            },
        );
        assert_eq!(missing, 0);
        assert_eq!(
            fanout.changed,
            deps(&[dep::Variant::Type("\\U".to_string())])
        );

        // Global constants are compared with their positions: `X` moved, so
        // it changed (only `GConst`, not `GConstName`, for a kept constant).
        let old_gconsts: s_map::T<Option<GconstDecl>> = names(&["\\X", "\\Y"])
            .into_iter()
            .map(|n| (n.clone(), crate::decl_heap::gconsts::get(&old_ctx, &n)))
            .collect();
        let (fanout, missing) = get_gconsts_deps(
            &new_ctx,
            &old_gconsts,
            &versioned_s_set::Diff {
                removed: s(&["\\Z"]),
                kept: s(&["\\X", "\\Y"]),
                added: s(&[]),
            },
        );
        assert_eq!(missing, 0);
        assert_eq!(
            fanout.changed,
            deps(&[
                dep::Variant::GConst("\\X".to_string()),
                dep::Variant::GConst("\\Z".to_string()),
                dep::Variant::GConstName("\\Z".to_string()),
            ])
        );
        // A kept constant missing from one of the versions is a change of
        // both its dependencies, and counts as missing.
        let old_missing: s_map::T<Option<GconstDecl>> =
            [("\\X".to_string(), None)].into_iter().collect();
        let (fanout, missing) = get_gconsts_deps(
            &new_ctx,
            &old_missing,
            &versioned_s_set::Diff {
                removed: s(&[]),
                kept: s(&["\\X"]),
                added: s(&[]),
            },
        );
        assert_eq!(missing, 1);
        assert_eq!(
            fanout.changed,
            deps(&[
                dep::Variant::GConst("\\X".to_string()),
                dep::Variant::GConstName("\\X".to_string()),
            ])
        );

        let old_modules: s_map::T<Option<ModuleDecl>> = names(&["m"])
            .into_iter()
            .map(|n| (n.clone(), crate::decl_heap::modules::get(&old_ctx, &n)))
            .collect();
        let (fanout, missing) = get_modules_deps(
            &new_ctx,
            &old_modules,
            &versioned_s_set::Diff {
                removed: s(&["gone"]),
                kept: s(&["m"]),
                added: s(&[]),
            },
        );
        assert_eq!(missing, 0);
        assert_eq!(
            fanout.changed,
            deps(&[dep::Variant::Module("gone".to_string())])
        );
    }

    #[test]
    fn folded_classes() {
        let src1 = "<?hh\nclass C { const int X = 1; public function m(): int { return 1; } }\n";
        let src2 = "<?hh\n\nclass C { const int X = 1; public function m(): int { return 1; } }\n";
        let src3 = "<?hh\nclass C { const int X = 2; public function m(): int { return 1; } public function n(): void {} }\n";
        let c = |src| {
            let ctx = ctx_of(src, TypecheckerOptions::default());
            ctx.folded_decls
                .get_class(TypeName::new("\\C"))
                .unwrap()
                .unwrap()
        };
        let (f1, f2, f3) = (c(src1), c(src2), c(src3));
        assert!(class_diff::compare(&f1, &f1));
        // The positions of the constants are compared.
        assert!(!class_diff::compare(&f1, &f2));
        assert!(!class_diff::compare(&f1, &f3));
        // Normalizing the classes removes the positions of the constants.
        assert_eq!(
            decl_pos_utils::normalize_sig::class_type(&f1).consts,
            decl_pos_utils::normalize_sig::class_type(&f2).consts
        );
        assert!(
            decl_pos_utils::normalize_sig::class_type(&f1)
                .decl_errors
                .is_empty()
        );
    }
}
