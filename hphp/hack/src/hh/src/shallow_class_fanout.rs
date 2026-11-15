// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `decl/shallow_class_fanout.ml`. See `hh/PORTING.md`.
//!
//! The fanout of the changes of classes ([`fanout_of_changes`]), as
//! `Shallow_decl_compare.compute_changes` computes them: a major change
//! rechecks the dependents of the class and of all its descendants; a minor
//! change rechecks the dependents of the members that changed.

use crate::class_diff;
use crate::class_diff::MemberChange;
use crate::class_diff::MemberDiff;
use crate::fanout;
use crate::hack_event_logger;
use crate::hh_logger;
use crate::naming_provider;
use crate::provider_context;
use crate::relative_path::RelativePath;
use crate::s_map;
use crate::s_set;
use crate::typechecker_options;
use crate::typing_deps;
use crate::typing_deps::dep;
use crate::typing_deps::dep_set;
use crate::typing_deps_mode;

/// `changed_class`
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChangedClass {
    pub name: String,
    pub diff: class_diff::T,
    pub dep: dep::T,
    pub descendant_deps: dep_set::T,
}

fn get_all_deps(ctx: &provider_context::T, changed_class: &ChangedClass) -> dep_set::T {
    let mode = provider_context::get_deps_mode(ctx);
    typing_deps::add_typing_deps(&mode, &changed_class.descendant_deps)
}

fn get_maximum_fanout(ctx: &provider_context::T, changed_class: &ChangedClass) -> fanout::T {
    // Record fields are evaluated from right to left.
    let to_recheck_if_errors = dep_set::make();
    let to_recheck = get_all_deps(ctx, changed_class);
    let changed = dep_set::singleton(changed_class.dep);
    fanout::T {
        changed,
        to_recheck,
        to_recheck_if_errors,
    }
}

pub fn class_names_from_deps(
    ctx: &provider_context::T,
    get_classes_in_file: impl Fn(&RelativePath) -> s_set::T,
    deps: &dep_set::T,
) -> s_set::T {
    let filenames = naming_provider::get_files(ctx, deps);
    // `Relative_path.Set.fold` and `S_set.fold` visit the elements in
    // increasing order.
    let mut acc = s_set::T::new();
    for file in filenames.iter() {
        for cid in get_classes_in_file(file).iter() {
            if dep_set::mem(deps, dep::make(&dep::Variant::Type(cid.clone()))) {
                acc.insert(cid.clone());
            }
        }
    }
    acc
}

fn include_fanout_of_dep(mode: &typing_deps_mode::T, dep: dep::T, deps: dep_set::T) -> dep_set::T {
    let fanout = typing_deps::get_ideps_from_hash(mode, dep);
    dep_set::union(&fanout, &deps)
}

fn get_minor_change_fanout(
    ctx: &provider_context::T,
    changed_class: &ChangedClass,
    member_diff: &MemberDiff,
) -> fanout::T {
    let mode = provider_context::get_deps_mode(ctx);
    let acc = dep_set::singleton(changed_class.dep);
    let MemberDiff {
        consts,
        typeconsts,
        props,
        sprops,
        methods,
        smethods,
        constructor,
    } = member_diff;
    // Recheck any file with a dependency on the provided member
    // in the changed class and in each of its descendants,
    // even if the member was overridden in a subclass. This deals with the case
    // where adding, removing, or changing the abstract-ness of a member causes
    // some subclass which inherits a member of that name from multiple parents
    // to resolve the conflict in a different way than it did previously.
    let recheck_descendants_and_their_member_dependents =
        |acc: dep_set::T, member: &dep::member::T| -> dep_set::T {
            dep_set::fold(&changed_class.descendant_deps, acc, |dep, acc| {
                let acc = dep_set::add(&acc, dep);
                include_fanout_of_dep(&mode, dep::make_member_dep_from_type_dep(dep, member), acc)
            })
        };
    let add_member_fanout = |is_const: bool,
                             member: &dep::member::T,
                             change: &MemberChange,
                             acc: dep_set::T|
     -> dep_set::T {
        // Consts and typeconsts have their types copied into descendant classes in
        // folded decl (rather than being stored in a separate heap as methods and
        // properties are). As a result, when using a const, we register a
        // dependency only upon the class type at the use site. In contrast, if we
        // use a method or property B::f which was inherited from A, we register a
        // dependency both upon B::f and A::f, which is what allows us to avoid the
        // more expensive use of recheck_descendants_and_their_member_dependents
        // here. Since we don't register a dependency upon the const at its class of
        // origin in this way, we must always take the more expensive path for
        // consts.
        if is_const || class_diff::method_or_property_change_affects_descendants(change) {
            recheck_descendants_and_their_member_dependents(acc, member)
        } else {
            include_fanout_of_dep(
                &mode,
                dep::make_member_dep_from_type_dep(changed_class.dep, member),
                acc,
            )
        }
    };
    let add_member_fanouts = |is_const: bool,
                              changes: &s_map::T<MemberChange>,
                              make_member: fn(&str) -> dep::member::T,
                              acc: dep_set::T|
     -> dep_set::T {
        // `S_map.fold` visits the bindings in increasing order of the names.
        let mut acc = acc;
        for (name, change) in changes.iter() {
            acc = add_member_fanout(is_const, &make_member(name), change, acc);
        }
        acc
    };
    let mut acc = acc;
    for (name, change) in consts.iter() {
        let acc1 = {
            // If a const has been added or removed in an enum type, we must recheck
            // all switch statements which need to have a case for each variant
            // (exhaustive switch statements add an AllMembers dependency).
            // We don't bother to test whether the class is an enum type because
            // non-enum classes will have no AllMembers dependents anyway.
            match change {
                MemberChange::Added
                | MemberChange::Removed
                | MemberChange::ChangedInheritance
                | MemberChange::Modified(_) => {
                    recheck_descendants_and_their_member_dependents(acc, &dep::member::ALL)
                }
                MemberChange::PrivateChangeNotInTrait => acc,
            }
        };
        acc = add_member_fanout(true, &dep::member::const_(name), change, acc1);
    }
    let acc = add_member_fanouts(true, typeconsts, dep::member::const_, acc);
    let acc = add_member_fanouts(false, props, dep::member::prop, acc);
    let acc = add_member_fanouts(false, sprops, dep::member::sprop, acc);
    let acc = add_member_fanouts(false, methods, dep::member::method_, acc);
    let acc = add_member_fanouts(false, smethods, dep::member::smethod, acc);
    let acc = match constructor {
        None => acc,
        Some(change) => add_member_fanout(false, &dep::member::CONSTRUCTOR, change, acc),
    };
    // Record fields are evaluated from right to left.
    let to_recheck_if_errors = dep_set::make();
    let changed = dep_set::singleton(changed_class.dep);
    fanout::T {
        changed,
        to_recheck: acc,
        to_recheck_if_errors,
    }
}

fn get_fanout(ctx: &provider_context::T, changed_class: &ChangedClass) -> fanout::T {
    match &changed_class.diff {
        class_diff::T::MajorChange(_change) => get_maximum_fanout(ctx, changed_class),
        class_diff::T::MinorChange(minor_change) => {
            get_minor_change_fanout(ctx, changed_class, minor_change)
        }
    }
}

fn direct_references_cardinal(mode: &typing_deps_mode::T, dep: dep::T) -> isize {
    dep_set::cardinal(&typing_deps::get_ideps_from_hash(mode, dep))
}

fn descendants_cardinal(descendant_deps: &dep_set::T) -> isize {
    dep_set::cardinal(descendant_deps) - 1
}

fn children_cardinal(mode: &typing_deps_mode::T, class_name: &str) -> isize {
    dep_set::cardinal(&typing_deps::get_ideps(
        mode,
        &dep::Variant::Extends(class_name.to_string()),
    ))
}

mod log {
    use super::*;

    fn do_log(ctx: &provider_context::T, fanout_cardinal: isize) -> bool {
        typechecker_options::log_fanout(&provider_context::get_tcopt(ctx), fanout_cardinal)
    }

    const MAX_CLASS_CNT: isize = 10;

    pub fn log_class_fanout(
        ctx: &provider_context::T,
        class_cnt: isize,
        changed_class: &ChangedClass,
        fanout: &fanout::T,
    ) {
        let ChangedClass {
            name,
            diff,
            dep,
            descendant_deps,
        } = changed_class;
        let fanout_cardinal = fanout::cardinal(fanout);
        if class_cnt < MAX_CLASS_CNT {
            // The arguments are evaluated from right to left.
            let truncated = if fanout_cardinal > 5 {
                " (truncated)"
            } else {
                ""
            };
            let l = dep_set::elements(&fanout.to_recheck);
            let first = l
                .into_iter()
                .take(5)
                .map(dep::to_hex_string)
                .collect::<Vec<_>>()
                .join(", ");
            hh_logger::log(&format!(
                "Fanout of {} (hash: {}) is {} deps: {}{}",
                name,
                dep::to_hex_string(*dep),
                fanout_cardinal,
                first,
                truncated
            ))
        } else if class_cnt == MAX_CLASS_CNT {
            hh_logger::log("(truncated)")
        }
        if do_log(ctx, fanout_cardinal) {
            let mode = provider_context::get_deps_mode(ctx);
            // The arguments are evaluated from right to left.
            let children_cardinal = children_cardinal(&mode, name);
            let descendants_cardinal = descendants_cardinal(descendant_deps);
            let direct_references_cardinal = direct_references_cardinal(&mode, *dep);
            let class_diff_category = class_diff::to_category_json(diff);
            let class_diff = class_diff::show(diff);
            hack_event_logger::fanouts::log_class(
                name,
                &class_diff,
                &class_diff_category,
                fanout_cardinal,
                direct_references_cardinal,
                descendants_cardinal,
                children_cardinal,
            )
        }
    }

    pub fn log_fanout<A>(
        ctx: &provider_context::T,
        changes: &[A],
        fanout: &fanout::T,
        max_class_fanout_cardinal: isize,
    ) {
        let fanout_cardinal = fanout::cardinal(fanout);
        if do_log(ctx, fanout_cardinal) {
            hack_event_logger::fanouts::log(
                changes.len() as isize,
                fanout_cardinal,
                max_class_fanout_cardinal,
            )
        }
    }
}

fn add_fanout(
    class_cnt: isize,
    ctx: &provider_context::T,
    (fanout_acc, max_class_fanout_cardinal): (fanout::T, isize),
    changed_class: &ChangedClass,
) -> (fanout::T, isize) {
    let fanout = get_fanout(ctx, changed_class);
    log::log_class_fanout(ctx, class_cnt, changed_class, &fanout);
    let fanout_acc = fanout::union(&fanout_acc, &fanout);
    let max_class_fanout_cardinal =
        std::cmp::max(max_class_fanout_cardinal, fanout::cardinal(&fanout));
    (fanout_acc, max_class_fanout_cardinal)
}

pub fn fanout_of_changes(ctx: &provider_context::T, changes: &[ChangedClass]) -> fanout::T {
    // `List.foldi`
    let mut acc = (fanout::empty(), 0);
    for (i, changed_class) in changes.iter().enumerate() {
        acc = add_fanout(i as isize, ctx, acc, changed_class);
    }
    let (fanout, max_class_fanout_cardinal) = acc;
    log::log_fanout(ctx, changes, &fanout, max_class_fanout_cardinal);
    fanout
}

#[cfg(test)]
mod tests {
    use oxidized::typechecker_options::TypecheckerOptions;

    use super::*;
    use crate::class_diff::major_change;
    use crate::class_diff::member_modification;
    use crate::decl_provider::testing::ctx_of;
    use crate::fanout::testing::with_edges;

    fn set(deps: &[&dep::Variant]) -> dep_set::T {
        dep_set::of_list(&deps.iter().map(|d| dep::make(d)).collect::<Vec<_>>())
    }

    fn c(name: &str) -> String {
        format!("\\TestShallowClassFanout{}", name)
    }

    fn fun(name: &str) -> dep::Variant {
        dep::Variant::Fun(format!("\\test_shallow_class_fanout_{}", name))
    }

    /// `A`; `B extends A`; `f` uses `A`, `g` uses `A::m`, `h` uses `B::m`,
    /// `i` uses `A::X`, `j` uses `B::X`, `k` uses all the members of `A`,
    /// `l` uses `A::$p`, `n` uses the constructor of `A`, `o` uses `B`.
    fn edges() -> Vec<(dep::Variant, dep::Variant)> {
        use dep::Variant::*;
        vec![
            (Type(c("B")), Extends(c("A"))),
            (fun("f"), Type(c("A"))),
            (fun("g"), Method(c("A"), "m".to_string())),
            (fun("h"), Method(c("B"), "m".to_string())),
            (fun("i"), Const(c("A"), "X".to_string())),
            (fun("j"), Const(c("B"), "X".to_string())),
            (fun("k"), AllMembers(c("A"))),
            (fun("l"), Prop(c("A"), "p".to_string())),
            (fun("n"), Constructor(c("A"))),
            (fun("o"), Type(c("B"))),
        ]
    }

    fn ctx() -> provider_context::T {
        ctx_of("<?hh\n", TypecheckerOptions::default())
    }

    fn changed_class(ctx: &provider_context::T, name: &str, diff: class_diff::T) -> ChangedClass {
        let dep = dep::make(&dep::Variant::Type(name.to_string()));
        ChangedClass {
            name: name.to_string(),
            diff,
            dep,
            descendant_deps: typing_deps::add_extend_deps(
                &provider_context::get_deps_mode(ctx),
                &dep_set::singleton(dep),
            ),
        }
    }

    fn minor(f: impl FnOnce(&mut MemberDiff)) -> class_diff::T {
        let mut d = class_diff::empty_member_diff();
        f(&mut d);
        class_diff::T::MinorChange(d)
    }

    #[test]
    fn major_change_rechecks_the_dependents_of_descendants() {
        with_edges(
            module_path!(),
            "major_change_rechecks_the_dependents_of_descendants",
            &edges(),
            || {
                let ctx = ctx();
                let a = changed_class(
                    &ctx,
                    &c("A"),
                    class_diff::T::MajorChange(major_change::T::Removed),
                );
                assert_eq!(
                    a.descendant_deps,
                    set(&[&dep::Variant::Type(c("A")), &dep::Variant::Type(c("B"))])
                );
                let fanout = fanout_of_changes(&ctx, &[a.clone()]);
                assert_eq!(fanout.changed, dep_set::singleton(a.dep));
                // The descendants and their typing dependents.
                assert_eq!(
                    fanout.to_recheck,
                    set(&[
                        &dep::Variant::Type(c("A")),
                        &dep::Variant::Type(c("B")),
                        &fun("f"),
                        &fun("o"),
                    ])
                );
                assert_eq!(fanout.to_recheck_if_errors, dep_set::make());
            },
        );
    }

    #[test]
    fn minor_change_of_a_method() {
        with_edges(module_path!(), "minor_change_of_a_method", &edges(), || {
            let ctx = ctx();
            // A modified method that does not affect descendants: only the
            // dependents of `A::m`.
            let a = changed_class(
                &ctx,
                &c("A"),
                minor(|d| {
                    d.methods.insert(
                        "m".to_string(),
                        MemberChange::Modified(member_modification::T::Other),
                    );
                }),
            );
            let fanout = fanout_of_changes(&ctx, &[a.clone()]);
            assert_eq!(fanout.changed, dep_set::singleton(a.dep));
            assert_eq!(
                fanout.to_recheck,
                set(&[&dep::Variant::Type(c("A")), &fun("g")])
            );
            // So does a private member added or removed.
            let a = changed_class(
                &ctx,
                &c("A"),
                minor(|d| {
                    d.methods
                        .insert("m".to_string(), MemberChange::PrivateChangeNotInTrait);
                }),
            );
            let fanout = fanout_of_changes(&ctx, &[a]);
            assert_eq!(
                fanout.to_recheck,
                set(&[&dep::Variant::Type(c("A")), &fun("g")])
            );

            // A removed method affects descendants: the descendants and the
            // dependents of their `m`.
            let a = changed_class(
                &ctx,
                &c("A"),
                minor(|d| {
                    d.methods.insert("m".to_string(), MemberChange::Removed);
                }),
            );
            let fanout = fanout_of_changes(&ctx, &[a]);
            assert_eq!(
                fanout.to_recheck,
                set(&[
                    &dep::Variant::Type(c("A")),
                    &dep::Variant::Type(c("B")),
                    &fun("g"),
                    &fun("h"),
                ])
            );
            // So does a change that affects inheritance (and a removed
            // method does not take `AllMembers`).
            let a = changed_class(
                &ctx,
                &c("A"),
                minor(|d| {
                    d.methods
                        .insert("m".to_string(), MemberChange::ChangedInheritance);
                }),
            );
            let fanout = fanout_of_changes(&ctx, &[a]);
            assert_eq!(
                fanout.to_recheck,
                set(&[
                    &dep::Variant::Type(c("A")),
                    &dep::Variant::Type(c("B")),
                    &fun("g"),
                    &fun("h"),
                ])
            );
        });
    }

    #[test]
    fn minor_change_of_a_const_property_and_constructor() {
        with_edges(
            module_path!(),
            "minor_change_of_a_const_property_and_constructor",
            &edges(),
            || {
                let ctx = ctx();
                // A modified constant always takes the descendants, and (as an
                // added or removed one) `AllMembers` of the descendants: its
                // type may have changed, which exhaustive switches depend on.
                let a = changed_class(
                    &ctx,
                    &c("A"),
                    minor(|d| {
                        d.consts.insert(
                            "X".to_string(),
                            MemberChange::Modified(member_modification::T::Other),
                        );
                    }),
                );
                let fanout = fanout_of_changes(&ctx, &[a]);
                assert_eq!(
                    fanout.to_recheck,
                    set(&[
                        &dep::Variant::Type(c("A")),
                        &dep::Variant::Type(c("B")),
                        &fun("i"),
                        &fun("j"),
                        &fun("k"),
                    ])
                );
                // An added or removed constant also takes `AllMembers` of
                // the descendants.
                for change in [MemberChange::Added, MemberChange::Removed] {
                    let a = changed_class(
                        &ctx,
                        &c("A"),
                        minor(|d| {
                            d.consts.insert("X".to_string(), change);
                        }),
                    );
                    let fanout = fanout_of_changes(&ctx, &[a]);
                    assert_eq!(
                        fanout.to_recheck,
                        set(&[
                            &dep::Variant::Type(c("A")),
                            &dep::Variant::Type(c("B")),
                            &fun("i"),
                            &fun("j"),
                            &fun("k"),
                        ])
                    );
                }
                // A type constant is a constant, but only a constant takes
                // `AllMembers`.
                let a = changed_class(
                    &ctx,
                    &c("A"),
                    minor(|d| {
                        d.typeconsts.insert("X".to_string(), MemberChange::Added);
                    }),
                );
                let fanout = fanout_of_changes(&ctx, &[a]);
                assert_eq!(
                    fanout.to_recheck,
                    set(&[
                        &dep::Variant::Type(c("A")),
                        &dep::Variant::Type(c("B")),
                        &fun("i"),
                        &fun("j"),
                    ])
                );
                // A property and the constructor.
                let a = changed_class(
                    &ctx,
                    &c("A"),
                    minor(|d| {
                        d.props.insert(
                            "p".to_string(),
                            MemberChange::Modified(member_modification::T::Other),
                        );
                        d.constructor = Some(MemberChange::Modified(member_modification::T::Other));
                    }),
                );
                let fanout = fanout_of_changes(&ctx, &[a]);
                assert_eq!(
                    fanout.to_recheck,
                    set(&[&dep::Variant::Type(c("A")), &fun("l"), &fun("n")])
                );
            },
        );
    }

    #[test]
    fn fanouts_of_several_classes_are_united() {
        with_edges(
            module_path!(),
            "fanouts_of_several_classes_are_united",
            &edges(),
            || {
                let ctx = ctx();
                let a = changed_class(&ctx, &c("A"), minor(|_| ()));
                let b = changed_class(
                    &ctx,
                    &c("B"),
                    class_diff::T::MajorChange(major_change::T::Added),
                );
                let fanout = fanout_of_changes(&ctx, &[a.clone(), b.clone()]);
                assert_eq!(fanout.changed, dep_set::of_list(&[a.dep, b.dep]));
                assert_eq!(
                    fanout.to_recheck,
                    set(&[
                        &dep::Variant::Type(c("A")),
                        &dep::Variant::Type(c("B")),
                        &fun("o"),
                    ])
                );
                assert_eq!(descendants_cardinal(&a.descendant_deps), 1);
                assert_eq!(
                    children_cardinal(&provider_context::get_deps_mode(&ctx), &c("A")),
                    1
                );
                assert_eq!(
                    direct_references_cardinal(&provider_context::get_deps_mode(&ctx), a.dep),
                    1
                );
                assert_eq!(fanout_of_changes(&ctx, &[]), fanout::empty());
            },
        );
    }
}
