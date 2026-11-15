// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `decl/shallow_decl_compare.ml`. See `hh/PORTING.md`.
//!
//! The changes of the classes of the files being redeclared
//! ([`compute_changes`]): the old shallow declarations (those that
//! `Decl_redecl_service` set aside before declaring the files again) against
//! the new ones.

use std::sync::Arc;
use std::sync::LazyLock;

use ty::decl::ShallowClass;

use crate::class_diff;
use crate::class_diff::UnknownKind;
use crate::class_diff::major_change;
use crate::ctx::R;
use crate::decl_compare::versioned_s_set;
use crate::decl_provider;
use crate::hh_logger;
use crate::old_decl_provider;
use crate::provider_context;
use crate::s_map;
use crate::s_set;
use crate::shallow_class_diff;
use crate::shallow_class_fanout;
use crate::typing_deps;
use crate::typing_deps::dep;
use crate::typing_deps::dep_set;
use crate::yojson::safe::T as Json;

fn diff_class_in_changed_file(
    enable_annotation_agnostic_decl_diffing: bool,
    old_classes: &s_map::T<Option<Arc<ShallowClass<R>>>>,
    new_classes: &s_map::T<Option<Arc<ShallowClass<R>>>>,
    class_name: &str,
) -> Option<class_diff::T> {
    // `S_map.find` raises `Not_found`.
    let old_class_opt = match old_classes.get(class_name) {
        Some(c) => c,
        None => panic!("Not_found"),
    };
    let new_class_opt = match new_classes.get(class_name) {
        Some(c) => c,
        None => panic!("Not_found"),
    };
    match (old_class_opt, new_class_opt) {
        (Some(old_class), Some(new_class)) => shallow_class_diff::diff_class(
            enable_annotation_agnostic_decl_diffing,
            old_class,
            new_class,
        ),
        (None, None) => Some(class_diff::T::MajorChange(major_change::T::Unknown(
            UnknownKind::NeitherFound,
        ))),
        (None, Some(_)) => Some(class_diff::T::MajorChange(major_change::T::Unknown(
            UnknownKind::OldDeclNotFound,
        ))),
        (Some(_), None) => Some(class_diff::T::MajorChange(major_change::T::Unknown(
            UnknownKind::NewDeclNotFound,
        ))),
    }
}

/// The diffs of the classes, in the order of the OCaml list (which is built
/// by consing): the kept classes that changed, then the removed ones, then
/// the added ones, each in decreasing order of the names.
fn compute_class_diffs(
    ctx: &provider_context::T,
    during_init: bool,
    class_names: &versioned_s_set::Diff,
) -> Vec<(String, class_diff::T)> {
    let enable_annotation_agnostic_decl_diffing =
        provider_context::get_tcopt(ctx).tco_enable_annotation_agnostic_decl_diffing;
    let versioned_s_set::Diff {
        added,
        kept,
        removed,
    } = class_names;
    let (added, kept, removed): (&s_set::T, &s_set::T, &s_set::T) = (added, kept, removed);
    // `acc` is the OCaml list reversed: consing is pushing.
    let mut acc: Vec<(String, class_diff::T)> = vec![];
    for name in added.iter() {
        acc.push((
            name.clone(),
            class_diff::T::MajorChange(major_change::T::Added),
        ));
    }
    for name in removed.iter() {
        acc.push((
            name.clone(),
            class_diff::T::MajorChange(major_change::T::Removed),
        ));
    }
    let old_classes: s_map::T<Option<Arc<ShallowClass<R>>>> =
        old_decl_provider::get_old_classes_batch(ctx, during_init, kept);
    let mut new_classes: s_map::T<Option<Arc<ShallowClass<R>>>> = s_map::T::new();
    for name in kept.iter() {
        new_classes.insert(name.clone(), decl_provider::get_shallow_class(ctx, name));
    }
    for cid in kept.iter() {
        let diff = diff_class_in_changed_file(
            enable_annotation_agnostic_decl_diffing,
            &old_classes,
            &new_classes,
            cid,
        );
        match diff {
            Some(diff) => acc.push((cid.clone(), diff)),
            None => (),
        }
    }
    acc.reverse();
    acc
}

/// `Yojson.Safe.pretty_to_string` (Yojson 2.0.2, `write2.ml`):
/// `Pretty.to_string ?std x`, with `std` false.
///
/// (`crate::yojson` has only the compact printer; this belongs there.)
fn yojson_safe_pretty_to_string(x: &Json) -> String {
    yojson_safe_pretty::to_string(x)
}

mod yojson_safe_pretty {
    //! `Yojson.Safe.Pretty` (Yojson 2.0.2, `lib/pretty.ml` with `INT`,
    //! `INTLIT`, `FLOAT`, `STRING`, `TUPLE` and `VARIANT` defined), on
    //! `crate::format`, with `std` false (the only value
    //! `Yojson.Safe.pretty_to_string` gives it here). `crate::yojson::safe::T`
    //! has no `` `Tuple`` and no `` `Variant``, so their cases are not here.
    //!
    //! Pretty-print JSON data in an attempt to maximize readability.
    //!
    //! 1. What fits on one line stays on one line.
    //! 2. What doesn't fit on one line gets printed more vertically so as to
    //!    not exceed a reasonable page width, if possible.

    use super::Json;
    use crate::format;
    use crate::format::Formatter;
    use crate::yojson;

    /// `json_string_of_string`: the string in double quotes, escaped as the
    /// compact printer escapes it (`write_string`).
    fn json_string_of_string(s: &str) -> String {
        yojson::safe::to_string(&Json::String(s.to_string()))
    }

    /// `json_string_of_float` (`write_float`, not the `std` one).
    fn json_string_of_float(x: f64) -> String {
        yojson::safe::to_string(&Json::Float(x))
    }

    /// `json_string_of_int` (`string_of_int`)
    fn json_string_of_int(x: isize) -> String {
        x.to_string()
    }

    fn pp_list<A>(sep: &str, ppx: impl Fn(&mut Formatter, &A), out: &mut Formatter, l: &[A]) {
        // `let pp_sep out () = Format.fprintf out "%s@ " sep in
        //  Format.pp_print_list ~pp_sep ppx out l`
        for (i, x) in l.iter().enumerate() {
            if i > 0 {
                format::pp_print_string(out, sep);
                format::pp_print_space(out);
            }
            ppx(out, x);
        }
    }

    fn is_atom(x: &Json) -> bool {
        match x {
            Json::Null
            | Json::Bool(_)
            | Json::Int(_)
            | Json::Float(_)
            | Json::String(_)
            | Json::Intlit(_) => true,
            Json::List(l) => l.is_empty(),
            Json::Assoc(l) => l.is_empty(),
        }
    }

    fn is_atom_list(l: &[Json]) -> bool {
        l.iter().all(is_atom)
    }

    /// inside_box: indicates that we're already within a box that imposes
    /// a certain style and we shouldn't create a new one. This is used for
    /// printing field values like this:
    ///
    /// ```text
    ///   foo: [
    ///     bar
    ///   ]
    /// ```
    ///
    /// rather than something else like
    ///
    /// ```text
    ///   foo:
    ///     [
    ///       bar
    ///     ]
    /// ```
    fn format(inside_box: bool, out: &mut Formatter, x: &Json) {
        match x {
            Json::Null => format::pp_print_string(out, "null"),
            // `Format.pp_print_bool`
            Json::Bool(x) => format::pp_print_string(out, if *x { "true" } else { "false" }),
            Json::Int(x) => format::pp_print_string(out, &json_string_of_int(*x)),
            Json::Float(x) => format::pp_print_string(out, &json_string_of_float(*x)),
            Json::String(s) => format::pp_print_string(out, &json_string_of_string(s)),
            Json::Intlit(s) => format::pp_print_string(out, s),
            Json::List(l) if l.is_empty() => format::pp_print_string(out, "[]"),
            Json::List(l) => {
                if !inside_box {
                    // "@[<hv2>"
                    format::pp_open_hvbox(out, 2);
                }
                if is_atom_list(l) {
                    // use line wrapping like we would do for a paragraph of text
                    // "[@;<1 0>@[<hov>%a@]@;<1 -2>]"
                    format::pp_print_char(out, '[');
                    format::pp_print_break(out, 1, 0);
                    format::pp_open_hovbox(out, 0);
                    pp_list(",", |out, x| format(false, out, x), out, l);
                    format::pp_close_box(out);
                    format::pp_print_break(out, 1, -2);
                    format::pp_print_char(out, ']');
                } else {
                    // print the elements horizontally if they fit on the line,
                    // otherwise print them in a column
                    // "[@;<1 0>@[<hv>%a@]@;<1 -2>]"
                    format::pp_print_char(out, '[');
                    format::pp_print_break(out, 1, 0);
                    format::pp_open_hvbox(out, 0);
                    pp_list(",", |out, x| format(false, out, x), out, l);
                    format::pp_close_box(out);
                    format::pp_print_break(out, 1, -2);
                    format::pp_print_char(out, ']');
                }
                if !inside_box {
                    // "@]"
                    format::pp_close_box(out);
                }
            }
            Json::Assoc(l) if l.is_empty() => format::pp_print_string(out, "{}"),
            Json::Assoc(l) => {
                if !inside_box {
                    // "@[<hv2>"
                    format::pp_open_hvbox(out, 2);
                }
                // "{@;<1 0>%a@;<1 -2>}"
                format::pp_print_char(out, '{');
                format::pp_print_break(out, 1, 0);
                pp_list(",", format_field, out, l);
                format::pp_print_break(out, 1, -2);
                format::pp_print_char(out, '}');
                if !inside_box {
                    // "@]"
                    format::pp_close_box(out);
                }
            }
        }
    }

    fn format_field(out: &mut Formatter, (name, x): &(String, Json)) {
        // "@[<hv2>%s: %a@]"
        format::pp_open_hvbox(out, 2);
        format::pp_print_string(out, &json_string_of_string(name));
        format::pp_print_string(out, ": ");
        format(true, out, x);
        format::pp_close_box(out);
    }

    pub fn pp(out: &mut Formatter, x: &Json) {
        // "@[<hv2>%a@]"
        format::pp_open_hvbox(out, 2);
        format(true, out, x);
        format::pp_close_box(out);
    }

    pub fn to_string(x: &Json) -> String {
        format::asprintf(|out| pp(out, x))
    }
}

fn log_changes(changes: &[(String, class_diff::T)]) {
    let change_count = changes.len();
    if changes.is_empty() {
        hh_logger::log("No class changes detected")
    } else {
        hh_logger::log(&format!("Found {} changed classes:", change_count))
    }
    let max = 1000;
    hh_logger::log_lazy(
        None,
        None,
        &LazyLock::new(|| {
            yojson_safe_pretty_to_string(&Json::Assoc(vec![
                (
                    "diffs".to_string(),
                    Json::Assoc(
                        changes
                            .iter()
                            .take(max)
                            .map(|(name, diff)| {
                                (name.clone(), Json::String(class_diff::show(diff)))
                            })
                            .collect(),
                    ),
                ),
                ("truncated".to_string(), Json::Bool(change_count > max)),
            ]))
        }),
    );
}

pub fn compute_changes(
    ctx: &provider_context::T,
    during_init: bool,
    class_names: &versioned_s_set::Diff,
) -> Vec<shallow_class_fanout::ChangedClass> {
    hh_logger::log(&format!(
        "Detecting changes to {} classes",
        versioned_s_set::diff_cardinal(class_names)
    ));

    let changes = compute_class_diffs(ctx, during_init, class_names);
    log_changes(&changes);
    changes
        .into_iter()
        .map(|(class_name, diff)| {
            let class_dep = dep::make(&dep::Variant::Type(class_name.clone()));
            let descendant_deps = typing_deps::add_extend_deps(
                &provider_context::get_deps_mode(ctx),
                &dep_set::singleton(class_dep),
            );
            shallow_class_fanout::ChangedClass {
                name: class_name,
                diff,
                dep: class_dep,
                descendant_deps,
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use oxidized::typechecker_options::TypecheckerOptions;

    use super::*;
    use crate::decl_provider::testing::ctx_of;

    fn classes(src: &str, names: &[&str]) -> s_map::T<Option<Arc<ShallowClass<R>>>> {
        let ctx = ctx_of(src, TypecheckerOptions::default());
        names
            .iter()
            .map(|name| {
                (
                    name.to_string(),
                    decl_provider::get_shallow_class(&ctx, name),
                )
            })
            .collect()
    }

    #[test]
    fn diffs_in_a_changed_file() {
        let names = ["\\A", "\\B", "\\C", "\\D"];
        let old = classes("<?hh\nclass A {}\nclass B {}\nclass C {}\n", &names);
        let new = classes(
            "<?hh\nclass A {}\nclass B { const int X = 1; }\nclass D {}\n",
            &names,
        );
        let diff = |name| diff_class_in_changed_file(false, &old, &new, name);
        assert_eq!(diff("\\A"), None);
        assert!(matches!(diff("\\B"), Some(class_diff::T::MinorChange(_))));
        assert_eq!(
            diff("\\C"),
            Some(class_diff::T::MajorChange(major_change::T::Unknown(
                UnknownKind::NewDeclNotFound
            )))
        );
        assert_eq!(
            diff("\\D"),
            Some(class_diff::T::MajorChange(major_change::T::Unknown(
                UnknownKind::OldDeclNotFound
            )))
        );
        let none = classes("<?hh\n", &["\\E"]);
        assert_eq!(
            diff_class_in_changed_file(false, &none, &none, "\\E"),
            Some(class_diff::T::MajorChange(major_change::T::Unknown(
                UnknownKind::NeitherFound
            )))
        );
        // `S_map.find` raises `Not_found` for a name that is in neither map.
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                diff_class_in_changed_file(false, &old, &new, "\\F")
            }))
            .is_err()
        );
    }

    /// The list is built by consing, as in OCaml: the kept classes that
    /// changed, then the removed ones, then the added ones, each in
    /// decreasing order of the names. A class that comes back
    /// (`test/integration_ml/test_added_parent.ml`, where `Foo`'s file was
    /// empty) is a `Major_change Added`.
    ///
    /// (`kept` is empty: `Old_decl_provider.get_old_classes_batch` is
    /// called with no name.)
    #[test]
    fn class_diffs_in_the_order_of_the_ocaml_list() {
        let ctx = ctx_of(
            "<?hh\nclass A {}\nclass B {}\n",
            TypecheckerOptions::default(),
        );
        let set = |names: &[&str]| names.iter().map(|n| n.to_string()).collect::<s_set::T>();
        let class_names = versioned_s_set::Diff {
            removed: set(&["\\C", "\\D"]),
            kept: set(&[]),
            added: set(&["\\A", "\\B"]),
        };
        let added = class_diff::T::MajorChange(major_change::T::Added);
        let removed = class_diff::T::MajorChange(major_change::T::Removed);
        assert_eq!(
            compute_class_diffs(&ctx, false, &class_names),
            vec![
                ("\\D".to_string(), removed.clone()),
                ("\\C".to_string(), removed),
                ("\\B".to_string(), added.clone()),
                ("\\A".to_string(), added),
            ]
        );
    }

    /// `Yojson.Safe.pretty_to_string`, on what `log_changes` logs: what fits
    /// on one line stays on one line, the rest is printed vertically.
    #[test]
    fn pretty_json() {
        let small = Json::Assoc(vec![
            ("diffs".to_string(), Json::Assoc(vec![])),
            ("truncated".to_string(), Json::Bool(false)),
        ]);
        assert_eq!(
            yojson_safe_pretty_to_string(&small),
            r#"{ "diffs": {}, "truncated": false }"#
        );
        let large = Json::Assoc(vec![
            (
                "diffs".to_string(),
                Json::Assoc(vec![
                    ("\\A".to_string(), Json::String("a".repeat(30))),
                    ("\\B".to_string(), Json::String("b".repeat(30))),
                ]),
            ),
            ("truncated".to_string(), Json::Bool(false)),
        ]);
        assert_eq!(
            yojson_safe_pretty_to_string(&large),
            concat!(
                "{\n",
                "  \"diffs\": {\n",
                "    \"\\\\A\": \"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\",\n",
                "    \"\\\\B\": \"bbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\"\n",
                "  },\n",
                "  \"truncated\": false\n",
                "}"
            )
        );
        // A list of atoms is filled like a paragraph; other lists are
        // horizontal when they fit.
        let list = Json::List(vec![
            Json::Int(1),
            Json::Null,
            Json::List(vec![]),
            Json::Assoc(vec![]),
        ]);
        assert_eq!(yojson_safe_pretty_to_string(&list), "[ 1, null, [], {} ]");
        let nested = Json::List(vec![Json::List(vec![Json::Int(1)]), Json::Int(2)]);
        assert_eq!(yojson_safe_pretty_to_string(&nested), "[ [ 1 ], 2 ]");
    }
}
