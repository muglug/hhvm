// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `decl/class_diff.ml`. See `hh/PORTING.md`.
//!
//! The description of how a class changed between two versions of its shallow
//! declaration, which `Shallow_class_diff` computes and `Shallow_class_fanout`
//! turns into a fanout.
//!
//! The `[@@deriving eq, show, yojson_of]` functions that the `.mli` exports
//! (and those the exported ones are built from) are written out:
//!
//! - `equal_*`: the types derive `PartialEq` where the derived equality of
//!   OCaml is structural; [`EnumTypeChange`] holds declared types, which OCaml
//!   compares with `equal_decl_ty` (reasons ignored), so its `PartialEq` is
//!   [`equal_enum_type_change`], and [`value_diff::T`] has no `PartialEq` (use
//!   [`value_diff::equal`]).
//! - `pp_*` and `show_*`: the printers ppx_deriving generates (ppx_deriving
//!   5.2.1), on `crate::format`, so that the text, line breaks included, is
//!   OCaml's. The OCaml format strings are quoted in comments next to the
//!   calls they stand for. Constructors are printed with their OCaml names
//!   (`Changed_inheritance`, not `ChangedInheritance`).
//! - `yojson_of_*`: what ppx_yojson_conv generates (v0.16): a record is an
//!   object of its fields in order, `None` is `null`, a constructor is a list
//!   of its name and its arguments, `()` is `null`.
//!
//! Printers this module needs from other modules that do not have them yet are
//! private here: `S_map.pp`, `Ast_defs.pp_classish_kind`,
//! `Ast_defs.yojson_of_classish_kind`, `Printf`'s `%S`.

use std::cmp::Ordering;

use oxidized::ast_defs::Abstraction;
use oxidized::ast_defs::ClassishKind;

use crate::format;
use crate::format::Formatter;
use crate::rt::ocaml_printf::sprintf_s;
use crate::s_map;
use crate::typing_defs_core::DeclTy;
use crate::typing_defs_core::equal_decl_ty;
use crate::utils;
use crate::yojson::safe::T as Json;

// ---------------------------------------------------------------------------
// Printing and JSON helpers (what ppx_deriving and ppx_yojson_conv generate)
// ---------------------------------------------------------------------------

/// ppx_deriving's printer of a constructor with one argument:
/// `"(@[<2>Name@ "`, the argument, `"@])"`.
fn pp_constructor1(fmt: &mut Formatter, name: &str, pp_arg: impl FnOnce(&mut Formatter)) {
    format::pp_print_char(fmt, '(');
    format::pp_open_box(fmt, 2);
    format::pp_print_string(fmt, name);
    format::pp_print_space(fmt);
    pp_arg(fmt);
    format::pp_close_box(fmt);
    format::pp_print_char(fmt, ')');
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

/// ppx_deriving's printer of an option.
fn pp_option<A>(pp_a: impl FnOnce(&mut Formatter, &A), fmt: &mut Formatter, x: &Option<A>) {
    match x {
        None => format::pp_print_string(fmt, "None"),
        Some(x) => {
            format::pp_print_string(fmt, "(Some ");
            pp_a(fmt, x);
            format::pp_print_string(fmt, ")")
        }
    }
}

/// ppx_deriving's printer of a `bool`: `"%B"`.
fn pp_bool(fmt: &mut Formatter, b: bool) {
    format::pp_print_string(fmt, if b { "true" } else { "false" })
}

/// ppx_deriving's printer of `unit`.
fn pp_unit(fmt: &mut Formatter, (): &()) {
    format::pp_print_string(fmt, "()")
}

/// `S_map.pp pp_data`: `Wrapped_map.make_pp` with keys printed by `"%S"`.
fn s_map_pp<A>(pp_data: impl Fn(&mut Formatter, &A), fmt: &mut Formatter, x: &s_map::T<A>) {
    // "@[<hv 2>{"
    format::pp_open_hvbox(fmt, 2);
    format::pp_print_char(fmt, '{');
    if !x.is_empty() {
        // " "
        format::pp_print_char(fmt, ' ');
    }
    let mut sep = false;
    for (key, data) in x.iter() {
        if sep {
            // ";@ "
            format::pp_print_char(fmt, ';');
            format::pp_print_space(fmt);
        }
        // "@["
        format::pp_open_box(fmt, 0);
        format::pp_print_string(fmt, &sprintf_s(key));
        // " ->@ "
        format::pp_print_string(fmt, " ->");
        format::pp_print_space(fmt);
        pp_data(fmt, data);
        // "@]"
        format::pp_close_box(fmt);
        sep = true;
    }
    if !x.is_empty() {
        format::pp_print_char(fmt, ' ');
    }
    // "}@]"
    format::pp_print_char(fmt, '}');
    format::pp_close_box(fmt);
}

/// `Ast_defs.pp_abstraction` (`show { with_path = false }`)
fn pp_abstraction(fmt: &mut Formatter, x: &Abstraction) {
    match x {
        Abstraction::Concrete => format::pp_print_string(fmt, "Concrete"),
        Abstraction::Abstract => format::pp_print_string(fmt, "Abstract"),
    }
}

/// `Ast_defs.pp_classish_kind` (`show { with_path = false }`)
fn pp_classish_kind(fmt: &mut Formatter, x: &ClassishKind) {
    match x {
        ClassishKind::Cclass(a0) => pp_constructor1(fmt, "Cclass", |fmt| pp_abstraction(fmt, a0)),
        ClassishKind::Cinterface => format::pp_print_string(fmt, "Cinterface"),
        ClassishKind::Ctrait => format::pp_print_string(fmt, "Ctrait"),
        ClassishKind::Cenum => format::pp_print_string(fmt, "Cenum"),
        ClassishKind::CenumClass(a0) => {
            pp_constructor1(fmt, "Cenum_class", |fmt| pp_abstraction(fmt, a0))
        }
    }
}

/// `Typing_defs.pp_decl_ty`
fn pp_decl_ty(_fmt: &mut Formatter, _ty: &DeclTy) {
    todo!(
        "Typing_defs.pp_decl_ty: Typing_defs_core.Pp.pp_ty and Typing_reason.pp_t_ (the printers of declared types and of their reasons, on Format) are not ported: crate::typing_defs_core::pp has no pp_* function"
    )
}

/// A constructor, as ppx_yojson_conv writes it: its name and its arguments.
fn yojson_of_constructor(name: &str, args: Vec<Json>) -> Json {
    let mut l = Vec::with_capacity(args.len() + 1);
    l.push(Json::String(name.to_string()));
    l.extend(args);
    Json::List(l)
}

/// A record, as ppx_yojson_conv writes it.
fn yojson_of_record(fields: Vec<(&str, Json)>) -> Json {
    Json::Assoc(
        fields
            .into_iter()
            .map(|(name, value)| (name.to_string(), value))
            .collect(),
    )
}

/// `yojson_of_option`
fn yojson_of_option<A>(yojson_of_a: impl FnOnce(&A) -> Json, x: &Option<A>) -> Json {
    match x {
        None => Json::Null,
        Some(x) => yojson_of_a(x),
    }
}

/// `yojson_of_bool`
fn yojson_of_bool(b: bool) -> Json {
    Json::Bool(b)
}

/// `yojson_of_unit`
fn yojson_of_unit((): &()) -> Json {
    Json::Null
}

/// `Ast_defs.yojson_of_abstraction`
fn yojson_of_abstraction(x: &Abstraction) -> Json {
    match x {
        Abstraction::Concrete => yojson_of_constructor("Concrete", vec![]),
        Abstraction::Abstract => yojson_of_constructor("Abstract", vec![]),
    }
}

/// `Ast_defs.yojson_of_classish_kind`
fn yojson_of_classish_kind(x: &ClassishKind) -> Json {
    match x {
        ClassishKind::Cclass(a0) => {
            yojson_of_constructor("Cclass", vec![yojson_of_abstraction(a0)])
        }
        ClassishKind::Cinterface => yojson_of_constructor("Cinterface", vec![]),
        ClassishKind::Ctrait => yojson_of_constructor("Ctrait", vec![]),
        ClassishKind::Cenum => yojson_of_constructor("Cenum", vec![]),
        ClassishKind::CenumClass(a0) => {
            yojson_of_constructor("Cenum_class", vec![yojson_of_abstraction(a0)])
        }
    }
}

// ---------------------------------------------------------------------------
// Members
// ---------------------------------------------------------------------------

pub mod member_modification {
    //! `MemberModification`

    use super::*;

    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub enum T {
        Asyncified,
        Deasyncified,
        Other,
    }

    /// `[@@deriving eq]`
    pub fn equal(a: &T, b: &T) -> bool {
        a == b
    }

    /// `[@@deriving ord]`: in the order of the constructors.
    pub fn compare(a: &T, b: &T) -> Ordering {
        a.cmp(b)
    }

    pub fn pp(fmt: &mut Formatter, x: &T) {
        match x {
            T::Asyncified => format::pp_print_string(fmt, "Asyncified"),
            T::Deasyncified => format::pp_print_string(fmt, "Deasyncified"),
            T::Other => format::pp_print_string(fmt, "Other"),
        }
    }

    pub fn show(x: &T) -> String {
        format::asprintf(|fmt| pp(fmt, x))
    }

    pub fn yojson_of_t(x: &T) -> Json {
        match x {
            T::Asyncified => yojson_of_constructor("Asyncified", vec![]),
            T::Deasyncified => yojson_of_constructor("Deasyncified", vec![]),
            T::Other => yojson_of_constructor("Other", vec![]),
        }
    }
}

mod member_modification_set {
    //! `MemberModificationSet`: `Set.Make (MemberModification)`.

    use super::*;

    pub type T = im::OrdSet<member_modification::T>;

    pub fn yojson_of_t(t: &T) -> Json {
        // `elements t |> yojson_of_list MemberModification.yojson_of_t`
        Json::List(t.iter().map(member_modification::yojson_of_t).collect())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum MemberChange {
    Added,
    Removed,
    /// Modified in a way that affects inheritance
    ChangedInheritance,
    /// Modified in a way that does not affect inheritance
    Modified(member_modification::T),
    /// Added/removed a private member
    PrivateChangeNotInTrait,
}

/// `[@@deriving eq]`
pub fn equal_member_change(a: &MemberChange, b: &MemberChange) -> bool {
    a == b
}

pub fn pp_member_change(fmt: &mut Formatter, x: &MemberChange) {
    match x {
        MemberChange::Added => format::pp_print_string(fmt, "Added"),
        MemberChange::Removed => format::pp_print_string(fmt, "Removed"),
        MemberChange::ChangedInheritance => format::pp_print_string(fmt, "Changed_inheritance"),
        MemberChange::Modified(a0) => {
            // "(@[<2>Modified@ "
            pp_constructor1(fmt, "Modified", |fmt| member_modification::pp(fmt, a0))
        }
        MemberChange::PrivateChangeNotInTrait => {
            format::pp_print_string(fmt, "Private_change_not_in_trait")
        }
    }
}

pub fn show_member_change(x: &MemberChange) -> String {
    format::asprintf(|fmt| pp_member_change(fmt, x))
}

fn yojson_of_member_change(x: &MemberChange) -> Json {
    match x {
        MemberChange::Added => yojson_of_constructor("Added", vec![]),
        MemberChange::Removed => yojson_of_constructor("Removed", vec![]),
        MemberChange::ChangedInheritance => yojson_of_constructor("Changed_inheritance", vec![]),
        MemberChange::Modified(a0) => {
            yojson_of_constructor("Modified", vec![member_modification::yojson_of_t(a0)])
        }
        MemberChange::PrivateChangeNotInTrait => {
            yojson_of_constructor("Private_change_not_in_trait", vec![])
        }
    }
}

/// Order member_change values by corresponding fanout size.
fn ord_member_change(x: &MemberChange) -> isize {
    match x {
        MemberChange::PrivateChangeNotInTrait => 0,
        MemberChange::Modified(_) => 1,
        MemberChange::ChangedInheritance => 2,
        MemberChange::Added => 3,
        MemberChange::Removed => 4,
    }
}

/// Compare member_change values by corresponding fanout size.
fn compare_member_change(x: &MemberChange, y: &MemberChange) -> isize {
    ord_member_change(x) - ord_member_change(y)
}

/// Returns true if the member changed in a way that affects what a descendant
/// might inherit. This is trivially true for Added/Removed. The
/// Changed_inheritance case captures situations where member metadata is used to
/// select which member is used when a member of the same name is inherited from
/// multiple parents.
///
/// For example, if we have:
///
/// ```text
/// class A { public function f(): void {} }
/// trait T { public abstract function f(): void; }
/// class B extends A { use T; }
/// ```
///
/// Then B inherits the concrete method A::f even though trait methods normally
/// overwrite parent methods in folded methods tables--we use the fact that A::f
/// is concrete and T::f is not to choose which member to inherit in B. Since
/// changes to the abstractness of A::f or T::f can affect what appears in B's
/// member collection, we categorize these changes with Changed_inheritance.
///
/// We must handle changes which affect descendants in this way differently from
/// changes which do not because of how we record member dependencies in the
/// dependency graph (see Shallow_class_fanout for this handling).
///
/// Other changes to members are categorized with Modified. In these cases, we
/// need to recheck uses of the member, but this is straightforward to do using
/// the dependency graph.
///
/// Adding or removing a private member can be handled in the same way as
/// Modified. We need to recheck uses of the member (if any exist), but the
/// presence of a private member does not affect descendants (descendants are not
/// prevented from defining a member of the same name, since each class gets its
/// own "namespace" for private members in the runtime).
///
/// Changes in positions in members are not considered a change at all by this
/// module, since we re-typecheck all files with errors for every global check
/// (so errors with positions referring to moved members will be recomputed).
pub fn method_or_property_change_affects_descendants(member_change: &MemberChange) -> bool {
    match member_change {
        MemberChange::Added | MemberChange::Removed | MemberChange::ChangedInheritance => true,
        MemberChange::Modified(_) | MemberChange::PrivateChangeNotInTrait => false,
    }
}

pub type ConstructorChange = Option<MemberChange>;

/// `[@@deriving eq]`
pub fn equal_constructor_change(a: &ConstructorChange, b: &ConstructorChange) -> bool {
    a == b
}

/// `[@@deriving ord]`, with `compare_member_change` (the order by fanout
/// size) for the members: `None` is smaller than any `Some`.
fn compare_constructor_change(a: &ConstructorChange, b: &ConstructorChange) -> isize {
    match (a, b) {
        (None, None) => 0,
        (Some(a), Some(b)) => compare_member_change(a, b),
        (None, Some(_)) => -1,
        (Some(_), None) => 1,
    }
}

fn yojson_of_constructor_change(x: &ConstructorChange) -> Json {
    yojson_of_option(yojson_of_member_change, x)
}

mod members_change_category {
    //! `MembersChangeCategory`

    use super::*;

    pub struct T {
        pub some_added: bool,
        pub some_removed: bool,
        pub some_changed_inheritance: bool,
        pub some_modified: member_modification_set::T,
        pub some_private_change: bool,
    }

    pub fn yojson_of_t(x: &T) -> Json {
        yojson_of_record(vec![
            ("some_added", yojson_of_bool(x.some_added)),
            ("some_removed", yojson_of_bool(x.some_removed)),
            (
                "some_changed_inheritance",
                yojson_of_bool(x.some_changed_inheritance),
            ),
            (
                "some_modified",
                member_modification_set::yojson_of_t(&x.some_modified),
            ),
            ("some_private_change", yojson_of_bool(x.some_private_change)),
        ])
    }

    pub fn no_change() -> T {
        T {
            some_added: false,
            some_removed: false,
            some_changed_inheritance: false,
            some_modified: member_modification_set::T::new(),
            some_private_change: false,
        }
    }

    pub fn of_member_change_map(changes: &s_map::T<MemberChange>) -> Option<T> {
        if changes.is_empty() {
            None
        } else {
            let mut acc = no_change();
            for (_, change) in changes.iter() {
                match change {
                    MemberChange::Added => acc.some_added = true,
                    MemberChange::Removed => acc.some_removed = true,
                    MemberChange::ChangedInheritance => acc.some_changed_inheritance = true,
                    MemberChange::Modified(modif) => {
                        acc.some_modified = acc.some_modified.update(*modif)
                    }
                    MemberChange::PrivateChangeNotInTrait => acc.some_private_change = true,
                }
            }
            Some(acc)
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MemberDiff {
    pub consts: s_map::T<MemberChange>,
    pub typeconsts: s_map::T<MemberChange>,
    pub props: s_map::T<MemberChange>,
    pub sprops: s_map::T<MemberChange>,
    pub methods: s_map::T<MemberChange>,
    pub smethods: s_map::T<MemberChange>,
    pub constructor: ConstructorChange,
}

/// `[@@deriving eq]`
pub fn equal_member_diff(a: &MemberDiff, b: &MemberDiff) -> bool {
    a == b
}

mod member_diff_category {
    //! `MemberDiffCategory`

    use super::*;

    pub struct T {
        pub consts_category: Option<members_change_category::T>,
        pub typeconsts_category: Option<members_change_category::T>,
        pub props_category: Option<members_change_category::T>,
        pub sprops_category: Option<members_change_category::T>,
        pub methods_category: Option<members_change_category::T>,
        pub smethods_category: Option<members_change_category::T>,
        pub constructor_category: ConstructorChange,
    }

    pub fn yojson_of_t(x: &T) -> Json {
        let category = |c: &Option<members_change_category::T>| {
            yojson_of_option(members_change_category::yojson_of_t, c)
        };
        yojson_of_record(vec![
            ("consts_category", category(&x.consts_category)),
            ("typeconsts_category", category(&x.typeconsts_category)),
            ("props_category", category(&x.props_category)),
            ("sprops_category", category(&x.sprops_category)),
            ("methods_category", category(&x.methods_category)),
            ("smethods_category", category(&x.smethods_category)),
            (
                "constructor_category",
                yojson_of_constructor_change(&x.constructor_category),
            ),
        ])
    }

    pub fn of_member_diff(
        MemberDiff {
            consts,
            typeconsts,
            props,
            sprops,
            methods,
            smethods,
            constructor,
        }: &MemberDiff,
    ) -> T {
        T {
            consts_category: members_change_category::of_member_change_map(consts),
            typeconsts_category: members_change_category::of_member_change_map(typeconsts),
            props_category: members_change_category::of_member_change_map(props),
            sprops_category: members_change_category::of_member_change_map(sprops),
            methods_category: members_change_category::of_member_change_map(methods),
            smethods_category: members_change_category::of_member_change_map(smethods),
            constructor_category: *constructor,
        }
    }
}

pub fn empty_member_diff() -> MemberDiff {
    MemberDiff {
        consts: s_map::T::new(),
        typeconsts: s_map::T::new(),
        props: s_map::T::new(),
        sprops: s_map::T::new(),
        smethods: s_map::T::new(),
        methods: s_map::T::new(),
        constructor: None,
    }
}

/// (OCaml compares with the polymorphic `=`; against the empty maps that is
/// the comparison of the bindings.)
pub fn is_empty_member_diff(member_diff: &MemberDiff) -> bool {
    *member_diff == empty_member_diff()
}

/// This is written explicitly instead of derived so that we can omit empty
/// fields of the member_diff record (to make logs easier to read).
pub fn pp_member_diff(fmt: &mut Formatter, member_diff: &MemberDiff) {
    // "@[<2>{"
    format::pp_open_box(fmt, 2);
    format::pp_print_char(fmt, '{');

    let mut sep = false;
    let mut pp_smap_field = |fmt: &mut Formatter, name: &str, data: &s_map::T<MemberChange>| {
        if !data.is_empty() {
            if sep {
                // ";@ "
                format::pp_print_char(fmt, ';');
                format::pp_print_space(fmt);
            } else {
                // " "
                format::pp_print_char(fmt, ' ');
                sep = true;
            }
            // "@[%s =@ "
            format::pp_open_box(fmt, 0);
            format::pp_print_string(fmt, name);
            format::pp_print_string(fmt, " =");
            format::pp_print_space(fmt);
            s_map_pp(pp_member_change, fmt, data);
            // "@]"
            format::pp_close_box(fmt);
        }
    };
    let MemberDiff {
        consts,
        typeconsts,
        props,
        sprops,
        methods,
        smethods,
        constructor,
    } = member_diff;
    pp_smap_field(fmt, "consts", consts);
    pp_smap_field(fmt, "typeconsts", typeconsts);
    pp_smap_field(fmt, "props", props);
    pp_smap_field(fmt, "sprops", sprops);
    pp_smap_field(fmt, "methods", methods);
    pp_smap_field(fmt, "smethods", smethods);

    match constructor {
        None => (),
        Some(member_change) => {
            if sep {
                format::pp_print_char(fmt, ';');
                format::pp_print_space(fmt);
            } else {
                sep = true;
            }
            // "@[%s =@ " "constructor"
            format::pp_open_box(fmt, 0);
            format::pp_print_string(fmt, "constructor");
            format::pp_print_string(fmt, " =");
            format::pp_print_space(fmt);
            pp_member_change(fmt, member_change);
            format::pp_close_box(fmt);
        }
    }

    if sep {
        // "@ "
        format::pp_print_space(fmt);
    }

    // "}@]"
    format::pp_print_char(fmt, '}');
    format::pp_close_box(fmt);
}

pub fn show_member_diff(member_diff: &MemberDiff) -> String {
    format::asprintf(|fmt| pp_member_diff(fmt, member_diff))
}

/// The maximum of two constructor changes is the change which has the largest fanout.
pub fn max_constructor_change(
    left: ConstructorChange,
    right: ConstructorChange,
) -> ConstructorChange {
    if compare_constructor_change(&left, &right) >= 0 {
        left
    } else {
        right
    }
}

// ---------------------------------------------------------------------------
// Class shells
// ---------------------------------------------------------------------------

pub mod value_change {
    //! `ValueChange`

    use super::*;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum T<C> {
        Added,
        Removed,
        Modified(C),
    }

    /// `[@@deriving eq]`
    pub fn equal<C>(poly_change: impl Fn(&C, &C) -> bool, a: &T<C>, b: &T<C>) -> bool {
        match (a, b) {
            (T::Added, T::Added) | (T::Removed, T::Removed) => true,
            (T::Modified(a), T::Modified(b)) => poly_change(a, b),
            (T::Added | T::Removed | T::Modified(_), _) => false,
        }
    }

    pub fn pp<C>(poly_change: impl Fn(&mut Formatter, &C), fmt: &mut Formatter, x: &T<C>) {
        match x {
            T::Added => format::pp_print_string(fmt, "Added"),
            T::Removed => format::pp_print_string(fmt, "Removed"),
            T::Modified(a0) => pp_constructor1(fmt, "Modified", |fmt| poly_change(fmt, a0)),
        }
    }

    pub fn show<C>(poly_change: impl Fn(&mut Formatter, &C), x: &T<C>) -> String {
        format::asprintf(|fmt| pp(poly_change, fmt, x))
    }

    pub fn yojson_of_t<C>(yojson_of_change: impl Fn(&C) -> Json, x: &T<C>) -> Json {
        match x {
            T::Added => yojson_of_constructor("Added", vec![]),
            T::Removed => yojson_of_constructor("Removed", vec![]),
            T::Modified(v0) => yojson_of_constructor("Modified", vec![yojson_of_change(v0)]),
        }
    }

    pub fn map<C, D>(f: impl FnOnce(&C) -> D, x: &T<C>) -> T<D> {
        match x {
            T::Added => T::Added,
            T::Removed => T::Removed,
            T::Modified(x) => T::Modified(f(x)),
        }
    }
}

pub mod named_items_list_change {
    //! `NamedItemsListChange`

    use super::*;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct T<C> {
        pub per_name_changes: s_map::T<value_change::T<C>>,
        /// The order has changed if there exists x and y
        /// such that x comes before y in the list pre-change,
        /// but y comes before x in the list post-change,
        /// i.e. if there exists two elements which are in both lists
        /// and have been swapped.
        pub order_change: bool,
    }

    /// `[@@deriving eq]`
    pub fn equal<C: Clone>(poly_change: impl Fn(&C, &C) -> bool, a: &T<C>, b: &T<C>) -> bool {
        // `S_map.equal (ValueChange.equal poly_change)`
        a.per_name_changes.len() == b.per_name_changes.len()
            && a.per_name_changes
                .iter()
                .zip(b.per_name_changes.iter())
                .all(|((k1, v1), (k2, v2))| k1 == k2 && value_change::equal(&poly_change, v1, v2))
            && a.order_change == b.order_change
    }

    pub fn pp<C: Clone>(poly_change: impl Fn(&mut Formatter, &C), fmt: &mut Formatter, x: &T<C>) {
        pp_record(
            fmt,
            &[
                ("per_name_changes", &|fmt| {
                    s_map_pp(
                        |fmt, v| value_change::pp(&poly_change, fmt, v),
                        fmt,
                        &x.per_name_changes,
                    )
                }),
                ("order_change", &|fmt| pp_bool(fmt, x.order_change)),
            ],
        )
    }

    pub fn show<C: Clone>(poly_change: impl Fn(&mut Formatter, &C), x: &T<C>) -> String {
        format::asprintf(|fmt| pp(poly_change, fmt, x))
    }
}

/// `unit NamedItemsListChange.t NamedItemsListChange.t`
type NestedListChange = named_items_list_change::T<named_items_list_change::T<()>>;

/// The printer of `unit NamedItemsListChange.t NamedItemsListChange.t option`.
fn pp_nested_list_change_option(fmt: &mut Formatter, x: &Option<NestedListChange>) {
    pp_option(
        |fmt, x| {
            named_items_list_change::pp(
                |fmt, y| named_items_list_change::pp(pp_unit, fmt, y),
                fmt,
                x,
            )
        },
        fmt,
        x,
    )
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParentChanges {
    pub extends_changes: Option<NestedListChange>,
    pub implements_changes: Option<NestedListChange>,
    pub req_extends_changes: Option<NestedListChange>,
    pub req_implements_changes: Option<NestedListChange>,
    /// For req constraints a coarse-grained analysis is sufficient
    pub req_constraints_changes: bool,
    pub uses_changes: Option<NestedListChange>,
    pub xhp_attr_changes: Option<NestedListChange>,
}

/// `[@@deriving eq]`
pub fn equal_parent_changes(a: &ParentChanges, b: &ParentChanges) -> bool {
    a == b
}

fn pp_parent_changes(fmt: &mut Formatter, x: &ParentChanges) {
    pp_record(
        fmt,
        &[
            ("extends_changes", &|fmt| {
                pp_nested_list_change_option(fmt, &x.extends_changes)
            }),
            ("implements_changes", &|fmt| {
                pp_nested_list_change_option(fmt, &x.implements_changes)
            }),
            ("req_extends_changes", &|fmt| {
                pp_nested_list_change_option(fmt, &x.req_extends_changes)
            }),
            ("req_implements_changes", &|fmt| {
                pp_nested_list_change_option(fmt, &x.req_implements_changes)
            }),
            ("req_constraints_changes", &|fmt| {
                pp_bool(fmt, x.req_constraints_changes)
            }),
            ("uses_changes", &|fmt| {
                pp_nested_list_change_option(fmt, &x.uses_changes)
            }),
            ("xhp_attr_changes", &|fmt| {
                pp_nested_list_change_option(fmt, &x.xhp_attr_changes)
            }),
        ],
    )
}

pub mod kind_change {
    //! `KindChange`

    use super::*;

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct T {
        pub new_kind: ClassishKind,
    }

    /// `[@@deriving eq]`
    pub fn equal(a: &T, b: &T) -> bool {
        a == b
    }

    pub fn pp(fmt: &mut Formatter, x: &T) {
        pp_record(
            fmt,
            &[("new_kind", &|fmt| pp_classish_kind(fmt, &x.new_kind))],
        )
    }

    pub fn show(x: &T) -> String {
        format::asprintf(|fmt| pp(fmt, x))
    }

    pub fn yojson_of_t(x: &T) -> Json {
        yojson_of_record(vec![("new_kind", yojson_of_classish_kind(&x.new_kind))])
    }
}

pub mod bool_change {
    //! `BoolChange`

    use super::*;

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum T {
        Became,
        NoMore,
    }

    /// `[@@deriving eq]`
    pub fn equal(a: &T, b: &T) -> bool {
        a == b
    }

    pub fn pp(fmt: &mut Formatter, x: &T) {
        match x {
            T::Became => format::pp_print_string(fmt, "Became"),
            T::NoMore => format::pp_print_string(fmt, "No_more"),
        }
    }

    pub fn show(x: &T) -> String {
        format::asprintf(|fmt| pp(fmt, x))
    }

    pub fn yojson_of_t(x: &T) -> Json {
        match x {
            T::Became => yojson_of_constructor("Became", vec![]),
            T::NoMore => yojson_of_constructor("No_more", vec![]),
        }
    }
}

pub mod value_diff {
    //! `ValueDiff`
    //!
    //! No `PartialEq`: it holds declared types, whose OCaml equality is not
    //! that of `ty::decl::Ty` (see [`equal`]).

    use super::*;

    #[derive(Clone, Debug)]
    pub struct T<V> {
        pub old_value: V,
        pub new_value: V,
    }

    /// `[@@deriving eq]`
    pub fn equal<V>(poly_value: impl Fn(&V, &V) -> bool, a: &T<V>, b: &T<V>) -> bool {
        poly_value(&a.old_value, &b.old_value) && poly_value(&a.new_value, &b.new_value)
    }

    pub fn pp<V>(poly_value: impl Fn(&mut Formatter, &V), fmt: &mut Formatter, x: &T<V>) {
        pp_record(
            fmt,
            &[
                ("old_value", &|fmt| poly_value(fmt, &x.old_value)),
                ("new_value", &|fmt| poly_value(fmt, &x.new_value)),
            ],
        )
    }

    pub fn show<V>(poly_value: impl Fn(&mut Formatter, &V), x: &T<V>) -> String {
        format::asprintf(|fmt| pp(poly_value, fmt, x))
    }
}

/// Its `PartialEq` is [`equal_enum_type_change`], OCaml's derived equality:
/// the declared types are compared with `equal_decl_ty`.
#[derive(Clone, Debug)]
pub struct EnumTypeChange {
    pub base_change: Option<value_diff::T<DeclTy>>,
    pub constraint_change: Option<value_change::T<value_diff::T<DeclTy>>>,
    pub includes_change: Option<NestedListChange>,
}

/// `[@@deriving eq]`
pub fn equal_enum_type_change(a: &EnumTypeChange, b: &EnumTypeChange) -> bool {
    let equal_ty_diff = |x: &value_diff::T<DeclTy>, y: &value_diff::T<DeclTy>| {
        value_diff::equal(equal_decl_ty, x, y)
    };
    (match (&a.base_change, &b.base_change) {
        (None, None) => true,
        (Some(x), Some(y)) => equal_ty_diff(x, y),
        (None, Some(_)) | (Some(_), None) => false,
    }) && (match (&a.constraint_change, &b.constraint_change) {
        (None, None) => true,
        (Some(x), Some(y)) => value_change::equal(equal_ty_diff, x, y),
        (None, Some(_)) | (Some(_), None) => false,
    }) && a.includes_change == b.includes_change
}

impl PartialEq for EnumTypeChange {
    fn eq(&self, other: &Self) -> bool {
        equal_enum_type_change(self, other)
    }
}

impl Eq for EnumTypeChange {}

pub fn pp_enum_type_change(fmt: &mut Formatter, x: &EnumTypeChange) {
    pp_record(
        fmt,
        &[
            ("base_change", &|fmt| {
                pp_option(
                    |fmt, d| value_diff::pp(pp_decl_ty, fmt, d),
                    fmt,
                    &x.base_change,
                )
            }),
            ("constraint_change", &|fmt| {
                pp_option(
                    |fmt, c| value_change::pp(|fmt, d| value_diff::pp(pp_decl_ty, fmt, d), fmt, c),
                    fmt,
                    &x.constraint_change,
                )
            }),
            ("includes_change", &|fmt| {
                pp_nested_list_change_option(fmt, &x.includes_change)
            }),
        ],
    )
}

pub fn show_enum_type_change(x: &EnumTypeChange) -> String {
    format::asprintf(|fmt| pp_enum_type_change(fmt, x))
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClassShellChange {
    /// The new classish kind will be in kind_change if it has changed.
    pub old_classish_kind: ClassishKind,
    pub parent_changes: Option<ParentChanges>,
    pub type_parameters_change: Option<named_items_list_change::T<()>>,
    pub kind_change: Option<kind_change::T>,
    pub final_change: Option<bool_change::T>,
    pub abstract_change: Option<bool_change::T>,
    pub is_xhp_change: Option<bool_change::T>,
    pub internal_change: Option<bool_change::T>,
    pub has_xhp_keyword_change: Option<bool_change::T>,
    pub support_dynamic_type_change: Option<bool_change::T>,
    pub module_change: Option<value_change::T<()>>,
    pub package_change: Option<value_change::T<()>>,
    pub xhp_enum_values_change: bool,
    pub user_attributes_changes: Option<NestedListChange>,
    pub enum_type_change: Option<value_change::T<EnumTypeChange>>,
}

/// `[@@deriving eq]`
pub fn equal_class_shell_change(a: &ClassShellChange, b: &ClassShellChange) -> bool {
    a == b
}

pub fn pp_class_shell_change(fmt: &mut Formatter, x: &ClassShellChange) {
    let pp_bool_change_option =
        |fmt: &mut Formatter, c: &Option<bool_change::T>| pp_option(bool_change::pp, fmt, c);
    let pp_unit_value_change_option = |fmt: &mut Formatter, c: &Option<value_change::T<()>>| {
        pp_option(|fmt, c| value_change::pp(pp_unit, fmt, c), fmt, c)
    };
    pp_record(
        fmt,
        &[
            ("old_classish_kind", &|fmt| {
                pp_classish_kind(fmt, &x.old_classish_kind)
            }),
            ("parent_changes", &|fmt| {
                pp_option(pp_parent_changes, fmt, &x.parent_changes)
            }),
            ("type_parameters_change", &|fmt| {
                pp_option(
                    |fmt, c| named_items_list_change::pp(pp_unit, fmt, c),
                    fmt,
                    &x.type_parameters_change,
                )
            }),
            ("kind_change", &|fmt| {
                pp_option(kind_change::pp, fmt, &x.kind_change)
            }),
            ("final_change", &|fmt| {
                pp_bool_change_option(fmt, &x.final_change)
            }),
            ("abstract_change", &|fmt| {
                pp_bool_change_option(fmt, &x.abstract_change)
            }),
            ("is_xhp_change", &|fmt| {
                pp_bool_change_option(fmt, &x.is_xhp_change)
            }),
            ("internal_change", &|fmt| {
                pp_bool_change_option(fmt, &x.internal_change)
            }),
            ("has_xhp_keyword_change", &|fmt| {
                pp_bool_change_option(fmt, &x.has_xhp_keyword_change)
            }),
            ("support_dynamic_type_change", &|fmt| {
                pp_bool_change_option(fmt, &x.support_dynamic_type_change)
            }),
            ("module_change", &|fmt| {
                pp_unit_value_change_option(fmt, &x.module_change)
            }),
            ("package_change", &|fmt| {
                pp_unit_value_change_option(fmt, &x.package_change)
            }),
            ("xhp_enum_values_change", &|fmt| {
                pp_bool(fmt, x.xhp_enum_values_change)
            }),
            ("user_attributes_changes", &|fmt| {
                pp_nested_list_change_option(fmt, &x.user_attributes_changes)
            }),
            ("enum_type_change", &|fmt| {
                pp_option(
                    |fmt, c| value_change::pp(pp_enum_type_change, fmt, c),
                    fmt,
                    &x.enum_type_change,
                )
            }),
        ],
    )
}

pub fn show_class_shell_change(x: &ClassShellChange) -> String {
    format::asprintf(|fmt| pp_class_shell_change(fmt, x))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnknownKind {
    OldDeclNotFound,
    NewDeclNotFound,
    NeitherFound,
}

/// `[@@deriving eq]`
pub fn equal_unknown_kind(a: &UnknownKind, b: &UnknownKind) -> bool {
    a == b
}

pub fn pp_unknown_kind(fmt: &mut Formatter, x: &UnknownKind) {
    match x {
        UnknownKind::OldDeclNotFound => format::pp_print_string(fmt, "Old_decl_not_found"),
        UnknownKind::NewDeclNotFound => format::pp_print_string(fmt, "New_decl_not_found"),
        UnknownKind::NeitherFound => format::pp_print_string(fmt, "Neither_found"),
    }
}

pub fn show_unknown_kind(x: &UnknownKind) -> String {
    format::asprintf(|fmt| pp_unknown_kind(fmt, x))
}

fn yojson_of_unknown_kind(x: &UnknownKind) -> Json {
    match x {
        UnknownKind::OldDeclNotFound => yojson_of_constructor("Old_decl_not_found", vec![]),
        UnknownKind::NewDeclNotFound => yojson_of_constructor("New_decl_not_found", vec![]),
        UnknownKind::NeitherFound => yojson_of_constructor("Neither_found", vec![]),
    }
}

pub mod major_change {
    //! `MajorChange`

    use super::*;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum T {
        Unknown(UnknownKind),
        Added,
        Removed,
        Modified(ClassShellChange, MemberDiff),
    }

    /// `[@@deriving eq]`
    pub fn equal(a: &T, b: &T) -> bool {
        a == b
    }

    pub fn pp(fmt: &mut Formatter, x: &T) {
        match x {
            T::Unknown(a0) => pp_constructor1(fmt, "Unknown", |fmt| pp_unknown_kind(fmt, a0)),
            T::Added => format::pp_print_string(fmt, "Added"),
            T::Removed => format::pp_print_string(fmt, "Removed"),
            T::Modified(a0, a1) => {
                // "(@[<2>Modified (@,"
                format::pp_print_char(fmt, '(');
                format::pp_open_box(fmt, 2);
                format::pp_print_string(fmt, "Modified (");
                format::pp_print_cut(fmt);
                pp_class_shell_change(fmt, a0);
                // ",@ "
                format::pp_print_char(fmt, ',');
                format::pp_print_space(fmt);
                pp_member_diff(fmt, a1);
                // "@,))@]"
                format::pp_print_cut(fmt);
                format::pp_print_string(fmt, "))");
                format::pp_close_box(fmt);
            }
        }
    }

    pub fn show(x: &T) -> String {
        format::asprintf(|fmt| pp(fmt, x))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum T {
    MajorChange(major_change::T),
    MinorChange(MemberDiff),
}

/// `[@@deriving eq]`
pub fn equal(a: &T, b: &T) -> bool {
    a == b
}

pub fn pp(fmt: &mut Formatter, x: &T) {
    match x {
        T::MajorChange(a0) => pp_constructor1(fmt, "Major_change", |fmt| major_change::pp(fmt, a0)),
        T::MinorChange(a0) => pp_constructor1(fmt, "Minor_change", |fmt| pp_member_diff(fmt, a0)),
    }
}

pub fn show(x: &T) -> String {
    format::asprintf(|fmt| pp(fmt, x))
}

/// `String.trim`: without the leading and trailing `' '`, `'\012'`, `'\n'`,
/// `'\r'` and `'\t'`.
fn string_trim(s: &str) -> &str {
    s.trim_matches(|c| matches!(c, ' ' | '\x0c' | '\n' | '\r' | '\t'))
}

pub fn pretty(name: &str, diff: &T) -> String {
    let buf = String::with_capacity(512);
    let mut fmt = format::formatter_of_buffer(buf);
    format::pp_set_margin(&mut fmt, 120);
    // "%s  @[<2>%s:@ %a@]@?"
    format::pp_print_string(&mut fmt, &" ".repeat(35)); // indentation hack (width of log timestamp)
    format::pp_print_string(&mut fmt, "  ");
    format::pp_open_box(&mut fmt, 2);
    format::pp_print_string(&mut fmt, utils::strip_ns(name));
    format::pp_print_char(&mut fmt, ':');
    format::pp_print_space(&mut fmt);
    pp(&mut fmt, diff);
    format::pp_close_box(&mut fmt);
    format::pp_print_flush(&mut fmt);
    let diffstr = format::flush_buffer_formatter(&mut fmt);
    // indentation hack
    format!("  {}", string_trim(&diffstr))
}

// ---------------------------------------------------------------------------
// Categories (for logging)
// ---------------------------------------------------------------------------

mod class_shell_change_category {
    //! `ClassShellChangeCategory`

    use super::*;

    pub mod list_change {
        //! `ClassShellChangeCategory.ListChange`

        use super::*;

        pub struct T {
            pub some_added: bool,
            pub some_removed: bool,
            pub some_modified: bool,
            pub order_change: bool,
        }

        pub fn yojson_of_t(x: &T) -> Json {
            yojson_of_record(vec![
                ("some_added", yojson_of_bool(x.some_added)),
                ("some_removed", yojson_of_bool(x.some_removed)),
                ("some_modified", yojson_of_bool(x.some_modified)),
                ("order_change", yojson_of_bool(x.order_change)),
            ])
        }

        pub fn no_change() -> T {
            T {
                some_added: false,
                some_removed: false,
                some_modified: false,
                order_change: false,
            }
        }

        pub fn of_list_change_map<C>(
            named_items_list_change::T {
                per_name_changes: changes,
                order_change,
            }: &named_items_list_change::T<C>,
        ) -> T {
            let mut acc = T {
                order_change: *order_change,
                ..no_change()
            };
            for (_, change) in changes.iter() {
                match change {
                    value_change::T::Added => acc.some_added = true,
                    value_change::T::Removed => acc.some_removed = true,
                    value_change::T::Modified(_) => acc.some_modified = true,
                }
            }
            acc
        }

        pub fn of_bool(b: bool) -> Option<T> {
            if b {
                Some(T {
                    some_added: true,
                    some_removed: true,
                    some_modified: true,
                    order_change: true,
                })
            } else {
                None
            }
        }
    }

    pub mod parents_change_category {
        //! `ClassShellChangeCategory.ParentsChangeCategory`

        use super::*;

        pub struct T {
            pub extends_changes_category: Option<list_change::T>,
            pub implements_changes_category: Option<list_change::T>,
            pub req_extends_changes_category: Option<list_change::T>,
            pub req_implements_changes_category: Option<list_change::T>,
            pub req_constraints_changes_category: Option<list_change::T>,
            pub uses_changes_category: Option<list_change::T>,
            pub xhp_attr_changes_category: Option<list_change::T>,
        }

        pub fn yojson_of_t(x: &T) -> Json {
            let category =
                |c: &Option<list_change::T>| yojson_of_option(list_change::yojson_of_t, c);
            yojson_of_record(vec![
                (
                    "extends_changes_category",
                    category(&x.extends_changes_category),
                ),
                (
                    "implements_changes_category",
                    category(&x.implements_changes_category),
                ),
                (
                    "req_extends_changes_category",
                    category(&x.req_extends_changes_category),
                ),
                (
                    "req_implements_changes_category",
                    category(&x.req_implements_changes_category),
                ),
                (
                    "req_constraints_changes_category",
                    category(&x.req_constraints_changes_category),
                ),
                ("uses_changes_category", category(&x.uses_changes_category)),
                (
                    "xhp_attr_changes_category",
                    category(&x.xhp_attr_changes_category),
                ),
            ])
        }

        pub fn of_parents_change(
            ParentChanges {
                extends_changes,
                implements_changes,
                req_extends_changes,
                req_implements_changes,
                req_constraints_changes,
                uses_changes,
                xhp_attr_changes,
            }: &ParentChanges,
        ) -> T {
            T {
                extends_changes_category: extends_changes
                    .as_ref()
                    .map(list_change::of_list_change_map),
                implements_changes_category: implements_changes
                    .as_ref()
                    .map(list_change::of_list_change_map),
                req_extends_changes_category: req_extends_changes
                    .as_ref()
                    .map(list_change::of_list_change_map),
                req_implements_changes_category: req_implements_changes
                    .as_ref()
                    .map(list_change::of_list_change_map),
                req_constraints_changes_category: list_change::of_bool(*req_constraints_changes),
                uses_changes_category: uses_changes.as_ref().map(list_change::of_list_change_map),
                xhp_attr_changes_category: xhp_attr_changes
                    .as_ref()
                    .map(list_change::of_list_change_map),
            }
        }
    }

    pub mod enum_type_change_category {
        //! `ClassShellChangeCategory.EnumTypeChangeCategory`

        use super::*;

        pub struct T {
            pub has_base_change: bool,
            pub constraint_change_category: Option<value_change::T<()>>,
            pub includes_change_category: Option<list_change::T>,
        }

        pub fn yojson_of_t(x: &T) -> Json {
            yojson_of_record(vec![
                ("has_base_change", yojson_of_bool(x.has_base_change)),
                (
                    "constraint_change_category",
                    yojson_of_option(
                        |c| value_change::yojson_of_t(yojson_of_unit, c),
                        &x.constraint_change_category,
                    ),
                ),
                (
                    "includes_change_category",
                    yojson_of_option(list_change::yojson_of_t, &x.includes_change_category),
                ),
            ])
        }

        pub fn of_enum_type_change(change: &EnumTypeChange) -> T {
            let EnumTypeChange {
                base_change,
                constraint_change,
                includes_change,
            } = change;
            T {
                has_base_change: base_change.is_some(),
                constraint_change_category: constraint_change
                    .as_ref()
                    .map(|c| value_change::map(|_| (), c)),
                includes_change_category: includes_change
                    .as_ref()
                    .map(list_change::of_list_change_map),
            }
        }
    }

    pub struct T {
        pub old_classish_kind: ClassishKind,
        pub parent_changes_category: Option<parents_change_category::T>,
        pub type_parameters_change_category: Option<list_change::T>,
        pub kind_change_category: Option<kind_change::T>,
        pub final_change_category: Option<bool_change::T>,
        pub abstract_change_category: Option<bool_change::T>,
        pub is_xhp_change_category: Option<bool_change::T>,
        pub internal_change_category: Option<bool_change::T>,
        pub has_xhp_keyword_change_category: Option<bool_change::T>,
        pub support_dynamic_type_change_category: Option<bool_change::T>,
        pub module_change_category: Option<value_change::T<()>>,
        pub package_change_category: Option<value_change::T<()>>,
        pub xhp_enum_values_change_category: bool,
        pub user_attributes_changes_category: Option<list_change::T>,
        pub enum_type_change_category: Option<value_change::T<enum_type_change_category::T>>,
    }

    pub fn yojson_of_t(x: &T) -> Json {
        let bool_change =
            |c: &Option<bool_change::T>| yojson_of_option(bool_change::yojson_of_t, c);
        let unit_value_change = |c: &Option<value_change::T<()>>| {
            yojson_of_option(|c| value_change::yojson_of_t(yojson_of_unit, c), c)
        };
        yojson_of_record(vec![
            (
                "old_classish_kind",
                yojson_of_classish_kind(&x.old_classish_kind),
            ),
            (
                "parent_changes_category",
                yojson_of_option(
                    parents_change_category::yojson_of_t,
                    &x.parent_changes_category,
                ),
            ),
            (
                "type_parameters_change_category",
                yojson_of_option(list_change::yojson_of_t, &x.type_parameters_change_category),
            ),
            (
                "kind_change_category",
                yojson_of_option(kind_change::yojson_of_t, &x.kind_change_category),
            ),
            (
                "final_change_category",
                bool_change(&x.final_change_category),
            ),
            (
                "abstract_change_category",
                bool_change(&x.abstract_change_category),
            ),
            (
                "is_xhp_change_category",
                bool_change(&x.is_xhp_change_category),
            ),
            (
                "internal_change_category",
                bool_change(&x.internal_change_category),
            ),
            (
                "has_xhp_keyword_change_category",
                bool_change(&x.has_xhp_keyword_change_category),
            ),
            (
                "support_dynamic_type_change_category",
                bool_change(&x.support_dynamic_type_change_category),
            ),
            (
                "module_change_category",
                unit_value_change(&x.module_change_category),
            ),
            (
                "package_change_category",
                unit_value_change(&x.package_change_category),
            ),
            (
                "xhp_enum_values_change_category",
                yojson_of_bool(x.xhp_enum_values_change_category),
            ),
            (
                "user_attributes_changes_category",
                yojson_of_option(
                    list_change::yojson_of_t,
                    &x.user_attributes_changes_category,
                ),
            ),
            (
                "enum_type_change_category",
                yojson_of_option(
                    |c| value_change::yojson_of_t(enum_type_change_category::yojson_of_t, c),
                    &x.enum_type_change_category,
                ),
            ),
        ])
    }

    pub fn of_class_shell_change(
        ClassShellChange {
            old_classish_kind,
            parent_changes,
            type_parameters_change,
            kind_change,
            final_change,
            abstract_change,
            is_xhp_change,
            internal_change,
            has_xhp_keyword_change,
            support_dynamic_type_change,
            module_change,
            package_change,
            xhp_enum_values_change,
            user_attributes_changes,
            enum_type_change,
        }: &ClassShellChange,
    ) -> T {
        T {
            old_classish_kind: *old_classish_kind,
            parent_changes_category: parent_changes
                .as_ref()
                .map(parents_change_category::of_parents_change),
            type_parameters_change_category: type_parameters_change
                .as_ref()
                .map(list_change::of_list_change_map),
            kind_change_category: *kind_change,
            final_change_category: *final_change,
            abstract_change_category: *abstract_change,
            is_xhp_change_category: *is_xhp_change,
            internal_change_category: *internal_change,
            has_xhp_keyword_change_category: *has_xhp_keyword_change,
            support_dynamic_type_change_category: *support_dynamic_type_change,
            module_change_category: module_change.clone(),
            package_change_category: package_change.clone(),
            xhp_enum_values_change_category: *xhp_enum_values_change,
            user_attributes_changes_category: user_attributes_changes
                .as_ref()
                .map(list_change::of_list_change_map),
            enum_type_change_category: enum_type_change
                .as_ref()
                .map(|c| value_change::map(enum_type_change_category::of_enum_type_change, c)),
        }
    }
}

mod major_change_category {
    //! `MajorChangeCategory`

    use super::*;

    pub enum T {
        Unknown(UnknownKind),
        Added,
        Removed,
        Modified(class_shell_change_category::T, member_diff_category::T),
    }

    pub fn yojson_of_t(x: &T) -> Json {
        match x {
            T::Unknown(v0) => yojson_of_constructor("Unknown", vec![yojson_of_unknown_kind(v0)]),
            T::Added => yojson_of_constructor("Added", vec![]),
            T::Removed => yojson_of_constructor("Removed", vec![]),
            T::Modified(v0, v1) => yojson_of_constructor(
                "Modified",
                vec![
                    class_shell_change_category::yojson_of_t(v0),
                    member_diff_category::yojson_of_t(v1),
                ],
            ),
        }
    }

    pub fn of_major_change(x: &major_change::T) -> T {
        match x {
            major_change::T::Unknown(k) => T::Unknown(*k),
            major_change::T::Added => T::Added,
            major_change::T::Removed => T::Removed,
            major_change::T::Modified(change, member_diff) => T::Modified(
                class_shell_change_category::of_class_shell_change(change),
                member_diff_category::of_member_diff(member_diff),
            ),
        }
    }
}

mod change_category {
    //! `ChangeCategory`

    use super::*;

    pub enum T {
        CMajorChange(major_change_category::T),
        CMinorChange(member_diff_category::T),
    }

    pub fn yojson_of_t(x: &T) -> Json {
        match x {
            T::CMajorChange(v0) => yojson_of_constructor(
                "CMajor_change",
                vec![major_change_category::yojson_of_t(v0)],
            ),
            T::CMinorChange(v0) => {
                yojson_of_constructor("CMinor_change", vec![member_diff_category::yojson_of_t(v0)])
            }
        }
    }

    pub fn of_change(x: &super::T) -> T {
        match x {
            super::T::MajorChange(change) => {
                T::CMajorChange(major_change_category::of_major_change(change))
            }
            super::T::MinorChange(member_diff) => {
                T::CMinorChange(member_diff_category::of_member_diff(member_diff))
            }
        }
    }
}

pub fn to_category_json(x: &T) -> Json {
    change_category::yojson_of_t(&change_category::of_change(x))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::yojson;

    fn smap(bindings: &[(&str, MemberChange)]) -> s_map::T<MemberChange> {
        bindings
            .iter()
            .map(|(name, change)| (name.to_string(), *change))
            .collect()
    }

    #[test]
    fn constructor_changes_are_ordered_by_fanout() {
        use MemberChange::*;
        let modified = Some(Modified(member_modification::T::Other));
        assert_eq!(max_constructor_change(None, None), None);
        assert_eq!(max_constructor_change(None, Some(Added)), Some(Added));
        assert_eq!(
            max_constructor_change(Some(PrivateChangeNotInTrait), None),
            Some(PrivateChangeNotInTrait)
        );
        assert_eq!(
            max_constructor_change(modified, Some(ChangedInheritance)),
            Some(ChangedInheritance)
        );
        assert_eq!(
            max_constructor_change(Some(Removed), Some(Added)),
            Some(Removed)
        );
        // On a tie, the left one.
        assert_eq!(
            max_constructor_change(
                Some(Modified(member_modification::T::Asyncified)),
                Some(Modified(member_modification::T::Other))
            ),
            Some(Modified(member_modification::T::Asyncified))
        );
    }

    #[test]
    fn affects_descendants() {
        use MemberChange::*;
        assert!(method_or_property_change_affects_descendants(&Added));
        assert!(method_or_property_change_affects_descendants(&Removed));
        assert!(method_or_property_change_affects_descendants(
            &ChangedInheritance
        ));
        assert!(!method_or_property_change_affects_descendants(&Modified(
            member_modification::T::Deasyncified
        )));
        assert!(!method_or_property_change_affects_descendants(
            &PrivateChangeNotInTrait
        ));
    }

    #[test]
    fn empty_member_diffs() {
        assert!(is_empty_member_diff(&empty_member_diff()));
        let diff = MemberDiff {
            constructor: Some(MemberChange::Added),
            ..empty_member_diff()
        };
        assert!(!is_empty_member_diff(&diff));
        let diff = MemberDiff {
            smethods: smap(&[("m", MemberChange::Removed)]),
            ..empty_member_diff()
        };
        assert!(!is_empty_member_diff(&diff));
    }

    #[test]
    fn show_member_diffs() {
        assert_eq!(show_member_diff(&empty_member_diff()), "{}");
        let diff = MemberDiff {
            methods: smap(&[("f", MemberChange::Removed)]),
            ..empty_member_diff()
        };
        assert_eq!(
            show_member_diff(&diff),
            r#"{ methods = { "f" -> Removed } }"#
        );
        // The constructor alone is not preceded by a space.
        let diff = MemberDiff {
            constructor: Some(MemberChange::ChangedInheritance),
            ..empty_member_diff()
        };
        assert_eq!(
            show_member_diff(&diff),
            "{constructor = Changed_inheritance }"
        );
        let diff = MemberDiff {
            consts: smap(&[("A", MemberChange::Added)]),
            constructor: Some(MemberChange::Removed),
            ..empty_member_diff()
        };
        assert_eq!(
            show_member_diff(&diff),
            r#"{ consts = { "A" -> Added }; constructor = Removed }"#
        );
    }

    #[test]
    fn show_changes() {
        assert_eq!(
            show(&T::MajorChange(major_change::T::Added)),
            "(Major_change Added)"
        );
        assert_eq!(
            show(&T::MajorChange(major_change::T::Unknown(
                UnknownKind::NeitherFound
            ))),
            "(Major_change (Unknown Neither_found))"
        );
        assert_eq!(
            show(&T::MinorChange(empty_member_diff())),
            "(Minor_change {})"
        );
        let diff = T::MinorChange(MemberDiff {
            methods: smap(&[("f", MemberChange::Removed)]),
            ..empty_member_diff()
        });
        assert_eq!(
            show(&diff),
            r#"(Minor_change { methods = { "f" -> Removed } })"#
        );
        assert_eq!(
            pretty("\\Foo", &diff),
            r#"  Foo: (Minor_change { methods = { "f" -> Removed } })"#
        );
        // Keys are printed as OCaml string literals.
        assert_eq!(sprintf_s("a\"b\\c\u{e9}"), r#""a\"b\\c\195\169""#);
    }

    #[test]
    fn show_shell_parts() {
        assert_eq!(
            kind_change::show(&kind_change::T {
                new_kind: ClassishKind::Cinterface
            }),
            "{ new_kind = Cinterface }"
        );
        assert_eq!(
            kind_change::show(&kind_change::T {
                new_kind: ClassishKind::Cclass(Abstraction::Concrete)
            }),
            "{ new_kind = (Cclass Concrete) }"
        );
        assert_eq!(bool_change::show(&bool_change::T::NoMore), "No_more");
        let list_change = named_items_list_change::T {
            per_name_changes: [("T".to_string(), value_change::T::Modified(()))]
                .into_iter()
                .collect(),
            order_change: true,
        };
        assert_eq!(
            named_items_list_change::show(pp_unit, &list_change),
            r#"{ per_name_changes = { "T" -> (Modified ()) }; order_change = true }"#
        );
        assert_eq!(
            value_change::show(pp_unit, &value_change::T::<()>::Added),
            "Added"
        );
    }

    #[test]
    fn category_json() {
        let json = |x: &T| yojson::safe::to_string(&to_category_json(x));
        assert_eq!(
            json(&T::MajorChange(major_change::T::Added)),
            r#"["CMajor_change",["Added"]]"#
        );
        assert_eq!(
            json(&T::MajorChange(major_change::T::Unknown(
                UnknownKind::OldDeclNotFound
            ))),
            r#"["CMajor_change",["Unknown",["Old_decl_not_found"]]]"#
        );
        let diff = T::MinorChange(MemberDiff {
            methods: smap(&[
                ("f", MemberChange::Modified(member_modification::T::Other)),
                (
                    "g",
                    MemberChange::Modified(member_modification::T::Asyncified),
                ),
            ]),
            constructor: Some(MemberChange::Added),
            ..empty_member_diff()
        });
        assert_eq!(
            json(&diff),
            concat!(
                r#"["CMinor_change",{"consts_category":null,"typeconsts_category":null,"#,
                r#""props_category":null,"sprops_category":null,"methods_category":"#,
                r#"{"some_added":false,"some_removed":false,"some_changed_inheritance":false,"#,
                r#""some_modified":[["Asyncified"],["Other"]],"some_private_change":false},"#,
                r#""smethods_category":null,"constructor_category":["Added"]}]"#
            )
        );
    }

    #[test]
    fn category_json_of_shells() {
        let list_change = named_items_list_change::T {
            per_name_changes: [("T".to_string(), value_change::T::Removed)]
                .into_iter()
                .collect(),
            order_change: false,
        };
        let change = ClassShellChange {
            old_classish_kind: ClassishKind::CenumClass(Abstraction::Abstract),
            parent_changes: Some(ParentChanges {
                extends_changes: None,
                implements_changes: None,
                req_extends_changes: None,
                req_implements_changes: None,
                req_constraints_changes: true,
                uses_changes: None,
                xhp_attr_changes: None,
            }),
            type_parameters_change: Some(list_change),
            kind_change: None,
            final_change: None,
            abstract_change: Some(bool_change::T::Became),
            is_xhp_change: None,
            internal_change: None,
            has_xhp_keyword_change: None,
            support_dynamic_type_change: None,
            module_change: None,
            package_change: Some(value_change::T::Added),
            xhp_enum_values_change: true,
            user_attributes_changes: None,
            enum_type_change: Some(value_change::T::Removed),
        };
        let json = yojson::safe::to_string(&to_category_json(&T::MajorChange(
            major_change::T::Modified(change, empty_member_diff()),
        )));
        assert_eq!(
            json,
            concat!(
                r#"["CMajor_change",["Modified",{"old_classish_kind":["Cenum_class",["Abstract"]],"#,
                r#""parent_changes_category":{"extends_changes_category":null,"#,
                r#""implements_changes_category":null,"req_extends_changes_category":null,"#,
                r#""req_implements_changes_category":null,"req_constraints_changes_category":"#,
                r#"{"some_added":true,"some_removed":true,"some_modified":true,"order_change":true},"#,
                r#""uses_changes_category":null,"xhp_attr_changes_category":null},"#,
                r#""type_parameters_change_category":{"some_added":false,"some_removed":true,"#,
                r#""some_modified":false,"order_change":false},"kind_change_category":null,"#,
                r#""final_change_category":null,"abstract_change_category":["Became"],"#,
                r#""is_xhp_change_category":null,"internal_change_category":null,"#,
                r#""has_xhp_keyword_change_category":null,"support_dynamic_type_change_category":null,"#,
                r#""module_change_category":null,"package_change_category":["Added"],"#,
                r#""xhp_enum_values_change_category":true,"user_attributes_changes_category":null,"#,
                r#""enum_type_change_category":["Removed"]},"#,
                r#"{"consts_category":null,"typeconsts_category":null,"props_category":null,"#,
                r#""sprops_category":null,"methods_category":null,"smethods_category":null,"#,
                r#""constructor_category":null}]]"#
            )
        );
    }
}
