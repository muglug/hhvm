// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `deps/file_info.ml`. See `hh/PORTING.md`.
//!
//! This module defines the data structured used to describe the content of
//! a file.
//! The parser constructs File_info.t structs, that contain names and positions
//! plus some extra info required for the build.
//! After the names have been checked (Naming.make_env), we "simplify" the
//! struct and only keep the names defined in the files we know about.
//!
//! # Types
//!
//! The types are those of `oxidized::file_info`, re-exported here: `mode` is
//! [`Mode`], `name_type` is [`NameType`], `si_kind` is [`SiKind`],
//! `si_addendum` is [`SiAddendum`] (fields without the prefix `sia_`), `pos`
//! is [`Pos`], `id` is [`Id`], `hash_type` is [`HashType`] (a newtype over
//! `Int64.t option`), `ids` is [`Ids`], `t` is [`FileInfo`] ([`T`]), `names`
//! is [`Names`] (fields without the prefix `n_`), `saved_names` is
//! [`SavedNames`] (without `sn_`), `diff` is [`Diff`], `pfh_hash` is
//! [`PfhHash`], `change` is [`Change`], and `Prim_defs.comment` is
//! [`Comment`]. `Decl_hash.t` is `i64` ([`decl_hash::T`]).
//!
//! An id contains a pos, name and a optional decl hash. The decl hash is None
//! only in the case when we didn't compute it for performance reasons.
//! [`Names`] is a cut-down version of [`T`], one that we use internally for
//! decl-diffing and other fanout calculations.
//!
//! The sets of [`Names`], [`SavedNames`] and [`Diff`] are `BTreeSet<String>`
//! in `oxidized` (not `s_set::T`): they are ordered as `S_set.t` is.
//!
//! `saved` has no `oxidized` type: it is [`Saved`] here, abstract as in the
//! `.mli` (fields without the prefix `s_`).
//!
//! # What `[@@deriving]` gives
//!
//! - `eq`: `==` on the Rust types, and the `equal_*` functions.
//! - `ord`: [`compare_mode`] and [`compare_name_type`]. The derived `Ord` of
//!   [`NameType`] orders the constructors by their `[@value]` (`Class`,
//!   `Typedef`, `Fun`, `Const`, `Module`); OCaml's `compare_name_type`
//!   orders them as they are declared (`Fun`, `Class`, `Typedef`, `Const`,
//!   `Module`). Use [`compare_name_type`] where the OCaml compares them.
//! - `enum`: `*_to_enum`, `*_of_enum`, `min_*` and `max_*`.
//! - `show`: `pp_*` and `show_*`, on `crate::format`, printing what ppx_deriving
//!   prints. As in the OCaml, [`pp_mode`] is the one written in
//!   `file_info.ml` (`Mhhi`), but [`show_mode`] is the derived one, which
//!   calls the derived printer (`File_info.Mhhi`), defined before it.
//! - Not here: `hash` (`hash_mode`, `hash_fold_mode`: the Rust types derive
//!   `Hash`) and `sexp_of_mode` (the crate has no S-expressions).

use std::cmp::Ordering;
use std::collections::BTreeSet;
use std::sync::Arc;

pub use oxidized::file_info::*;

use crate::format;
use crate::format::Formatter;
use crate::relative_path::RelativePath;
use crate::rt::ocaml_printf::sprintf_s_bytes;

/// `t`: the record produced by the parsing phase.
///
/// `File_info.t` is (1) what we get out of the parser, with Full positions;
/// (2) the API for putting stuff into and taking stuff out of saved-state
/// naming table (with File positions)
pub type T = FileInfo;

// ---------------------------------------------------------------------------
// Printers of `[@@deriving show]`
// ---------------------------------------------------------------------------

/// `Format.fprintf fmt "%B"`
fn pp_bool(fmt: &mut Formatter, b: bool) {
    format::pp_print_string(fmt, if b { "true" } else { "false" })
}

/// `Format.fprintf fmt "%LdL"`: the printer of `Int64.t`.
fn pp_int64(fmt: &mut Formatter, n: i64) {
    format::pp_print_string(fmt, &format!("{}L", n))
}

/// The printer of `'a option`: `"None"`, or `"(Some "`, the value, `")"`.
fn pp_option<A>(fmt: &mut Formatter, x: &Option<A>, pp: impl Fn(&mut Formatter, &A)) {
    match x {
        None => format::pp_print_string(fmt, "None"),
        Some(x) => {
            format::pp_print_string(fmt, "(Some ");
            pp(fmt, x);
            format::pp_print_string(fmt, ")");
        }
    }
}

/// The printer of `'a list`: `"@[<2>["`, the elements separated by `";@ "`,
/// `"@,]@]"`.
fn pp_list<A>(fmt: &mut Formatter, l: &[A], pp: impl Fn(&mut Formatter, &A)) {
    format::pp_open_box(fmt, 2);
    format::pp_print_string(fmt, "[");
    let mut sep = false;
    for x in l {
        if sep {
            format::pp_print_string(fmt, ";");
            format::pp_print_space(fmt);
        }
        pp(fmt, x);
        sep = true;
    }
    format::pp_print_cut(fmt);
    format::pp_print_string(fmt, "]");
    format::pp_close_box(fmt);
}

/// The printer of a record: `"@[<2>{ "`, the fields separated by `";@ "`,
/// `"@ }@]"`; a field is `"@[%s =@ "`, its value, `"@]"`. The first field is
/// qualified by the module (`with_path`).
fn pp_record(fmt: &mut Formatter, fields: &[(&str, &dyn Fn(&mut Formatter))]) {
    format::pp_open_box(fmt, 2);
    format::pp_print_string(fmt, "{ ");
    for (i, (name, pp_value)) in fields.iter().enumerate() {
        if i > 0 {
            format::pp_print_string(fmt, ";");
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
    format::pp_print_string(fmt, "}");
    format::pp_close_box(fmt);
}

/// The printer of a constructor with one argument: `"(@[<2>Name@ "`, the
/// argument, `"@])"`.
fn pp_constr1(fmt: &mut Formatter, name: &str, pp_arg: impl FnOnce(&mut Formatter)) {
    format::pp_print_string(fmt, "(");
    format::pp_open_box(fmt, 2);
    format::pp_print_string(fmt, name);
    format::pp_print_space(fmt);
    pp_arg(fmt);
    format::pp_close_box(fmt);
    format::pp_print_string(fmt, ")");
}

/// `Pos.pp`
fn pos_pp(fmt: &mut Formatter, p: &oxidized::pos::Pos) {
    let mut s = String::new();
    // Writing to a `String` cannot fail.
    crate::pos::pp(&mut s, p).unwrap();
    format::pp_print_string(fmt, &s)
}

/// `Prim_defs.pp_comment` (`[@@deriving show]` of `Prim_defs.comment`).
fn prim_defs_pp_comment(fmt: &mut Formatter, c: &Comment) {
    match c {
        Comment::CmtLine(s) => pp_constr1(fmt, "Prim_defs.CmtLine", |fmt| {
            format::pp_print_string(fmt, &sprintf_s_bytes(s.as_bytes()))
        }),
        Comment::CmtBlock(s) => pp_constr1(fmt, "Prim_defs.CmtBlock", |fmt| {
            format::pp_print_string(fmt, &sprintf_s_bytes(s.as_bytes()))
        }),
    }
}

/// `S_set.pp` on a set of `oxidized`.
fn pp_s_set(fmt: &mut Formatter, set: &BTreeSet<String>) {
    crate::s_set::pp(fmt, &set.iter().cloned().collect())
}

// ---------------------------------------------------------------------------
// Parsing modes
// ---------------------------------------------------------------------------

pub fn is_strict(mode: Mode) -> bool {
    match mode {
        Mode::Mstrict => true,
        Mode::Mhhi => false,
    }
}

pub fn is_hhi(mode: Mode) -> bool {
    match mode {
        Mode::Mstrict => false,
        Mode::Mhhi => true,
    }
}

pub fn string_of_mode(mode: Mode) -> String {
    match mode {
        Mode::Mhhi => "hhi",
        Mode::Mstrict => "strict",
    }
    .to_string()
}

/// The printer that `file_info.ml` defines after the type, in place of the
/// derived one.
pub fn pp_mode(fmt: &mut Formatter, mode: Mode) {
    format::pp_print_string(
        fmt,
        match mode {
            Mode::Mhhi => "Mhhi",
            Mode::Mstrict => "Mstrict",
        },
    )
}

/// The derived `pp_mode`, which `show_mode` calls.
fn derived_pp_mode(fmt: &mut Formatter, mode: Mode) {
    format::pp_print_string(
        fmt,
        match mode {
            Mode::Mhhi => "File_info.Mhhi",
            Mode::Mstrict => "File_info.Mstrict",
        },
    )
}

/// `[@@deriving show]`: the derived printer (see the module documentation).
pub fn show_mode(mode: Mode) -> String {
    format::asprintf(|fmt| derived_pp_mode(fmt, mode))
}

/// `[@@deriving eq]`
pub fn equal_mode(m1: Mode, m2: Mode) -> bool {
    m1 == m2
}

/// `[@@deriving ord]`: the constructors in the order they are declared.
pub fn compare_mode(m1: Mode, m2: Mode) -> Ordering {
    mode_to_enum(m1).cmp(&mode_to_enum(m2))
}

/// `[@@deriving enum]`
pub const MIN_MODE: isize = 0;

/// `[@@deriving enum]`
pub const MAX_MODE: isize = 1;

/// `[@@deriving enum]`
pub fn mode_to_enum(mode: Mode) -> isize {
    match mode {
        Mode::Mhhi => 0,
        Mode::Mstrict => 1,
    }
}

/// `[@@deriving enum]`
pub fn mode_of_enum(i: isize) -> Option<Mode> {
    match i {
        0 => Some(Mode::Mhhi),
        1 => Some(Mode::Mstrict),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Positions of names in a file
// ---------------------------------------------------------------------------

/// `[@@deriving show { with_path = false }]`
pub fn pp_name_type(fmt: &mut Formatter, name_type: NameType) {
    format::pp_print_string(
        fmt,
        match name_type {
            NameType::Fun => "Fun",
            NameType::Class => "Class",
            NameType::Typedef => "Typedef",
            NameType::Const => "Const",
            NameType::Module => "Module",
        },
    )
}

/// `[@@deriving show { with_path = false }]`
pub fn show_name_type(name_type: NameType) -> String {
    format::asprintf(|fmt| pp_name_type(fmt, name_type))
}

/// `[@@deriving eq]`
pub fn equal_name_type(n1: NameType, n2: NameType) -> bool {
    n1 == n2
}

/// The position of a constructor in the declaration of `name_type`, which
/// `[@@deriving ord]` compares.
fn name_type_index(name_type: NameType) -> isize {
    match name_type {
        NameType::Fun => 0,
        NameType::Class => 1,
        NameType::Typedef => 2,
        NameType::Const => 3,
        NameType::Module => 4,
    }
}

/// `[@@deriving ord]`: the constructors in the order they are declared (not
/// the order of their `[@value]`, which the derived `Ord` of [`NameType`]
/// follows).
pub fn compare_name_type(n1: NameType, n2: NameType) -> Ordering {
    name_type_index(n1).cmp(&name_type_index(n2))
}

/// `[@@deriving enum]`
pub const MIN_NAME_TYPE: isize = 0;

/// `[@@deriving enum]`
pub const MAX_NAME_TYPE: isize = 5;

/// `[@@deriving enum]`: the `[@value]` of the constructor.
pub fn name_type_to_enum(name_type: NameType) -> isize {
    match name_type {
        NameType::Fun => 3,
        NameType::Class => 0,
        NameType::Typedef => 1,
        NameType::Const => 4,
        NameType::Module => 5,
    }
}

/// `[@@deriving enum]`
pub fn name_type_of_enum(i: isize) -> Option<NameType> {
    match i {
        3 => Some(NameType::Fun),
        0 => Some(NameType::Class),
        1 => Some(NameType::Typedef),
        4 => Some(NameType::Const),
        5 => Some(NameType::Module),
        _ => None,
    }
}

/// `[@@deriving show { with_path = false }]`
pub fn pp_si_kind(fmt: &mut Formatter, kind: SiKind) {
    format::pp_print_string(
        fmt,
        match kind {
            SiKind::SIClass => "SI_Class",
            SiKind::SIInterface => "SI_Interface",
            SiKind::SIEnum => "SI_Enum",
            SiKind::SITrait => "SI_Trait",
            SiKind::SIUnknown => "SI_Unknown",
            SiKind::SIMixed => "SI_Mixed",
            SiKind::SIFunction => "SI_Function",
            SiKind::SITypedef => "SI_Typedef",
            SiKind::SIGlobalConstant => "SI_GlobalConstant",
            SiKind::SIXHP => "SI_XHP",
            SiKind::SINamespace => "SI_Namespace",
            SiKind::SIClassMethod => "SI_ClassMethod",
            SiKind::SILiteral => "SI_Literal",
            SiKind::SIClassConstant => "SI_ClassConstant",
            SiKind::SIProperty => "SI_Property",
            SiKind::SILocalVariable => "SI_LocalVariable",
            SiKind::SIKeyword => "SI_Keyword",
            SiKind::SIConstructor => "SI_Constructor",
        },
    )
}

/// `[@@deriving show { with_path = false }]`
pub fn show_si_kind(kind: SiKind) -> String {
    format::asprintf(|fmt| pp_si_kind(fmt, kind))
}

/// `[@@deriving eq]`
pub fn equal_si_kind(k1: SiKind, k2: SiKind) -> bool {
    k1 == k2
}

/// `[@@deriving show]`
pub fn pp_si_addendum(fmt: &mut Formatter, x: &SiAddendum) {
    pp_record(
        fmt,
        &[
            ("File_info.sia_name", &|fmt| {
                format::pp_print_string(fmt, &sprintf_s_bytes(x.name.as_bytes()))
            }),
            ("sia_kind", &|fmt| pp_si_kind(fmt, x.kind)),
            ("sia_is_abstract", &|fmt| pp_bool(fmt, x.is_abstract)),
            ("sia_is_final", &|fmt| pp_bool(fmt, x.is_final)),
        ],
    )
}

/// `[@@deriving show]`
pub fn show_si_addendum(x: &SiAddendum) -> String {
    format::asprintf(|fmt| pp_si_addendum(fmt, x))
}

/// `[@@deriving show]`
pub fn pp_pos(fmt: &mut Formatter, pos: &Pos) {
    match pos {
        Pos::Full(p) => pp_constr1(fmt, "File_info.Full", |fmt| pos_pp(fmt, p)),
        Pos::File(name_type, path) => {
            // "(@[<2>File_info.File (@," a0 ",@ " a1 "@,))@]"
            format::pp_print_string(fmt, "(");
            format::pp_open_box(fmt, 2);
            format::pp_print_string(fmt, "File_info.File (");
            format::pp_print_cut(fmt);
            pp_name_type(fmt, *name_type);
            format::pp_print_string(fmt, ",");
            format::pp_print_space(fmt);
            crate::relative_path::pp(fmt, path);
            format::pp_print_cut(fmt);
            format::pp_print_string(fmt, "))");
            format::pp_close_box(fmt);
        }
    }
}

/// `[@@deriving show]`
pub fn show_pos(pos: &Pos) -> String {
    format::asprintf(|fmt| pp_pos(fmt, pos))
}

/// `[@@deriving eq]`
pub fn equal_pos(p1: &Pos, p2: &Pos) -> bool {
    p1 == p2
}

/// `Decl_hash`: the OCaml equivalent of Rust's `hh24_types::DeclHash`.
/// Values originate from calling `hh_hash::hash` on an
/// `oxidized::shallow_decl_defs::Decl` in Rust and enter OCaml through the
/// FFI or by loading a previously stored hash.
pub mod decl_hash {
    pub use oxidized::file_info::decl_hash::DeclHash;

    use super::*;

    /// `Decl_hash.t`
    pub type T = DeclHash;

    /// The only escape hatch for creating these values in OCaml. Only for
    /// reading declaration hashes from the `DECL_HASH` column of the
    /// `NAMING_SYMBOLS` table.
    pub fn from_naming_table(hash: i64) -> T {
        hash
    }

    pub fn to_int64(hash: T) -> i64 {
        hash
    }

    /// `[@@deriving eq]`
    pub fn equal(h1: &T, h2: &T) -> bool {
        h1 == h2
    }

    /// `[@@deriving show]` of `t = Int64.t`
    pub fn pp(fmt: &mut Formatter, hash: &T) {
        pp_int64(fmt, *hash)
    }

    /// `[@@deriving show]`
    pub fn show(hash: &T) -> String {
        format::asprintf(|fmt| pp(fmt, hash))
    }
}

/// `[@@deriving show]`
pub fn pp_id(fmt: &mut Formatter, id: &Id) {
    pp_record(
        fmt,
        &[
            ("File_info.pos", &|fmt| pp_pos(fmt, &id.pos)),
            ("name", &|fmt| {
                format::pp_print_string(fmt, &sprintf_s_bytes(id.name.as_bytes()))
            }),
            ("decl_hash", &|fmt| {
                pp_option(fmt, &id.decl_hash, decl_hash::pp)
            }),
        ],
    )
}

/// `[@@deriving show]`
pub fn show_id(id: &Id) -> String {
    format::asprintf(|fmt| pp_id(fmt, id))
}

/// `[@@deriving eq]`
pub fn equal_id(id1: &Id, id2: &Id) -> bool {
    id1 == id2
}

// ---------------------------------------------------------------------------
// The record produced by the parsing phase.
// ---------------------------------------------------------------------------

/// `[@@deriving eq]`
pub fn equal_hash_type(h1: &HashType, h2: &HashType) -> bool {
    h1 == h2
}

pub fn pp_hash_type(fmt: &mut Formatter, hash: &HashType) {
    match hash.0 {
        None => format::pp_print_string(fmt, "None"),
        Some(hash) => {
            // `Format.fprintf fmt "Some (%s)" (Int64.to_string hash)`
            format::pp_print_string(fmt, "Some (");
            format::pp_print_string(fmt, &hash.to_string());
            format::pp_print_string(fmt, ")");
        }
    }
}

/// `[@@deriving show]`
pub fn pp_ids(fmt: &mut Formatter, ids: &Ids) {
    pp_record(
        fmt,
        &[
            ("File_info.funs", &|fmt| pp_list(fmt, &ids.funs, pp_id)),
            ("classes", &|fmt| pp_list(fmt, &ids.classes, pp_id)),
            ("typedefs", &|fmt| pp_list(fmt, &ids.typedefs, pp_id)),
            ("consts", &|fmt| pp_list(fmt, &ids.consts, pp_id)),
            ("modules", &|fmt| pp_list(fmt, &ids.modules, pp_id)),
        ],
    )
}

/// `[@@deriving show]`
pub fn show_ids(ids: &Ids) -> String {
    format::asprintf(|fmt| pp_ids(fmt, ids))
}

/// `[@@deriving show]` of `t`
pub fn pp(fmt: &mut Formatter, t: &T) {
    pp_record(
        fmt,
        &[
            ("File_info.position_free_decl_hash", &|fmt| {
                pp_hash_type(fmt, &t.position_free_decl_hash)
            }),
            ("file_mode", &|fmt| {
                pp_option(fmt, &t.file_mode, |fmt, mode| pp_mode(fmt, *mode))
            }),
            ("ids", &|fmt| pp_ids(fmt, &t.ids)),
            ("comments", &|fmt| {
                pp_option(fmt, &t.comments, |fmt, comments| {
                    pp_list(fmt, comments, |fmt, (p, comment)| {
                        // "(@[" a0 ",@ " a1 "@])"
                        format::pp_print_string(fmt, "(");
                        format::pp_open_box(fmt, 0);
                        pos_pp(fmt, p);
                        format::pp_print_string(fmt, ",");
                        format::pp_print_space(fmt);
                        prim_defs_pp_comment(fmt, comment);
                        format::pp_close_box(fmt);
                        format::pp_print_string(fmt, ")");
                    })
                })
            }),
        ],
    )
}

/// `[@@deriving show]` of `t`
pub fn show(t: &T) -> String {
    format::asprintf(|fmt| pp(fmt, t))
}

/// `empty_ids` (a value in OCaml)
pub fn empty_ids() -> Ids {
    Ids {
        funs: vec![],
        classes: vec![],
        typedefs: vec![],
        consts: vec![],
        modules: vec![],
    }
}

/// `empty_t` (a value in OCaml)
pub fn empty_t() -> T {
    FileInfo {
        position_free_decl_hash: HashType(None),
        file_mode: None,
        ids: empty_ids(),
        comments: Some(vec![]),
    }
}

pub fn pos_full((p, name, decl_hash): (oxidized::pos::Pos, String, Option<decl_hash::T>)) -> Id {
    let pos = Pos::Full(p);
    Id {
        pos,
        name,
        decl_hash,
    }
}

pub fn get_pos_filename(pos: &Pos) -> RelativePath {
    match pos {
        Pos::Full(p) => p.filename().clone(),
        Pos::File(_, fn_) => RelativePath::clone(fn_),
    }
}

// ---------------------------------------------------------------------------
// The simplified record used after parsing.
// ---------------------------------------------------------------------------

/// `[@@deriving show]`
pub fn pp_names(fmt: &mut Formatter, names: &Names) {
    pp_record(
        fmt,
        &[
            ("File_info.n_funs", &|fmt| pp_s_set(fmt, &names.funs)),
            ("n_classes", &|fmt| pp_s_set(fmt, &names.classes)),
            ("n_types", &|fmt| pp_s_set(fmt, &names.types)),
            ("n_consts", &|fmt| pp_s_set(fmt, &names.consts)),
            ("n_modules", &|fmt| pp_s_set(fmt, &names.modules)),
        ],
    )
}

/// `[@@deriving show]`
pub fn show_names(names: &Names) -> String {
    format::asprintf(|fmt| pp_names(fmt, names))
}

/// `saved`: the data structure stored in the saved state.
///
/// Although [`T`] is the public API for storing/retrieving entries in the
/// naming-table, we actually store the naming-table on disk as [`Saved`] -
/// it's basically the same but has a slightly more compact representation in
/// order to save space. It is abstract, as in the `.mli`: [`to_saved`],
/// [`from_saved`] and [`saved_to_names`] are its API.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Saved {
    names: SavedNames,
    position_free_decl_hash: Option<i64>,
    mode: Option<Mode>,
}

impl Saved {
    /// The record from its fields: for the `Marshal` codec of the
    /// `NAMING_LOCAL_CHANGES` blob of `crate::naming_sqlite`, whose OCaml
    /// marshals the record itself (`s_names`, `s_position_free_decl_hash`,
    /// `s_mode`).
    pub fn of_fields(
        names: SavedNames,
        position_free_decl_hash: Option<i64>,
        mode: Option<Mode>,
    ) -> Saved {
        Saved {
            names,
            position_free_decl_hash,
            mode,
        }
    }

    /// The fields of the record (see [`Saved::of_fields`]).
    pub fn fields(&self) -> (&SavedNames, Option<i64>, Option<Mode>) {
        (&self.names, self.position_free_decl_hash, self.mode)
    }
}

/// `empty_names` (a value in OCaml)
pub fn empty_names() -> Names {
    Names {
        funs: BTreeSet::new(),
        classes: BTreeSet::new(),
        types: BTreeSet::new(),
        consts: BTreeSet::new(),
        modules: BTreeSet::new(),
    }
}

pub mod old_names {
    use super::*;
    use crate::s_map;

    /// Each key is a symbol in a file's old contents (i.e., previous contents
    /// before the ongoing incremental re-check). The hashes describe the old
    /// hash of the winning decl for that symbol.
    /// The "winning" part is subtle:
    /// - If there was no duplicate naming error it just means "the previous
    ///   version of this decl in this file"
    /// - if there was a duplicate naming error, the winning (i.e., actually
    ///   used) definition may have been in a different file. In that case, the
    ///   hash is for that declaration in a different file!
    ///
    /// These hashes are used for validating the old version of the decl (if we
    /// can recover it), prior to old decl comparison. That's why we only care
    /// about the winning decl: If there was a duplicate name error before and
    /// we have access to an old decl, it will only ever be the winning version.
    ///
    /// Note that this validation is different from deciding fanout:
    /// - What these hashes are used for: Deciding whether a given decl is
    ///   indeed a valid baseline (i.e., it represents the state of the decl
    ///   prior to the current re-check).
    /// - What they are not used for: Deciding whether a decl hash changed
    ///   between the previous and current recheck.
    ///
    /// `None` means that the expected hash is unknown; the old declaration may
    /// still be available in the old decl store.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct T {
        pub funs: s_map::T<Option<decl_hash::T>>,
        pub classes: s_map::T<Option<decl_hash::T>>,
        pub types: s_map::T<Option<decl_hash::T>>,
        pub consts: s_map::T<Option<decl_hash::T>>,
        pub modules: s_map::T<Option<decl_hash::T>>,
    }

    /// `[@@deriving show]`
    pub fn pp(fmt: &mut Formatter, x: &T) {
        let pp_hashes = |fmt: &mut Formatter, hashes: &s_map::T<Option<decl_hash::T>>| {
            s_map::pp(
                |fmt, hash| pp_option(fmt, hash, |fmt, hash| decl_hash::pp(fmt, hash)),
                fmt,
                hashes,
            )
        };
        pp_record(
            fmt,
            &[
                ("File_info.Old_names.n_funs", &|fmt| {
                    pp_hashes(fmt, &x.funs)
                }),
                ("n_classes", &|fmt| pp_hashes(fmt, &x.classes)),
                ("n_types", &|fmt| pp_hashes(fmt, &x.types)),
                ("n_consts", &|fmt| pp_hashes(fmt, &x.consts)),
                ("n_modules", &|fmt| pp_hashes(fmt, &x.modules)),
            ],
        )
    }

    /// `[@@deriving show]`
    pub fn show(x: &T) -> String {
        format::asprintf(|fmt| pp(fmt, x))
    }

    pub fn empty() -> T {
        T {
            funs: s_map::T::new(),
            classes: s_map::T::new(),
            types: s_map::T::new(),
            consts: s_map::T::new(),
            modules: s_map::T::new(),
        }
    }

    pub fn of_names(names: &Names) -> T {
        let unknown_hashes = |names: &BTreeSet<String>| -> s_map::T<Option<decl_hash::T>> {
            names.iter().map(|name| (name.clone(), None)).collect()
        };
        let Names {
            funs: n_funs,
            classes: n_classes,
            types: n_types,
            consts: n_consts,
            modules: n_modules,
        } = names;
        T {
            funs: unknown_hashes(n_funs),
            classes: unknown_hashes(n_classes),
            types: unknown_hashes(n_types),
            consts: unknown_hashes(n_consts),
            modules: unknown_hashes(n_modules),
        }
    }

    /// Keep the first occurrence of each exact name within a declaration
    /// kind, including an unknown hash. IDs must be supplied in source order,
    /// and their hashes must already describe the previous winning
    /// declarations.
    pub fn of_ids(ids: &Ids) -> T {
        let hashes = |ids: &[Id]| -> s_map::T<Option<decl_hash::T>> {
            let mut acc = s_map::T::new();
            for Id {
                name, decl_hash, ..
            } in ids
            {
                if !acc.contains_key(name) {
                    acc.insert(name.clone(), *decl_hash);
                }
            }
            acc
        };
        let Ids {
            funs,
            classes,
            typedefs,
            consts,
            modules,
        } = ids;
        T {
            funs: hashes(funs),
            classes: hashes(classes),
            types: hashes(typedefs),
            consts: hashes(consts),
            modules: hashes(modules),
        }
    }

    pub fn to_names(old_names: &T) -> Names {
        let names = |hashes: &s_map::T<Option<decl_hash::T>>| -> BTreeSet<String> {
            hashes.keys().cloned().collect()
        };
        let T {
            funs: n_funs,
            classes: n_classes,
            types: n_types,
            consts: n_consts,
            modules: n_modules,
        } = old_names;
        Names {
            funs: names(n_funs),
            classes: names(n_classes),
            types: names(n_types),
            consts: names(n_consts),
            modules: names(n_modules),
        }
    }

    /// Preserve matching winning hashes when the same symbol occurs in
    /// several files. Conflicting or unknown hashes merge to an unknown hash.
    pub fn merge(left: &T, right: &T) -> T {
        let merge_hash = |_name: &String,
                          left: Option<&Option<decl_hash::T>>,
                          right: Option<&Option<decl_hash::T>>|
         -> Option<Option<decl_hash::T>> {
            match (left, right) {
                (Some(left), Some(right)) => Some(if left == right { *left } else { None }),
                (Some(_), None) => left.copied(),
                (None, Some(_)) => right.copied(),
                (None, None) => None,
            }
        };
        let merge_hashes = |left: &s_map::T<Option<decl_hash::T>>,
                            right: &s_map::T<Option<decl_hash::T>>| {
            s_map::merge(merge_hash, left, right)
        };
        T {
            funs: merge_hashes(&left.funs, &right.funs),
            classes: merge_hashes(&left.classes, &right.classes),
            types: merge_hashes(&left.types, &right.types),
            consts: merge_hashes(&left.consts, &right.consts),
            modules: merge_hashes(&left.modules, &right.modules),
        }
    }
}

// ---------------------------------------------------------------------------
// Functions simplifying the file information.
// ---------------------------------------------------------------------------

fn name_set_of_idl(idl: &[Id]) -> BTreeSet<String> {
    let mut acc = BTreeSet::new();
    for id in idl {
        acc.insert(id.name.clone());
    }
    acc
}

pub fn ids_to_names(ids: &Ids) -> Names {
    let Ids {
        funs,
        classes,
        typedefs,
        consts,
        modules,
    } = ids;
    Names {
        funs: name_set_of_idl(funs),
        classes: name_set_of_idl(classes),
        types: name_set_of_idl(typedefs),
        consts: name_set_of_idl(consts),
        modules: name_set_of_idl(modules),
    }
}

pub fn simplify(info: &T) -> Names {
    ids_to_names(&info.ids)
}

pub fn to_saved(info: &T) -> Saved {
    let FileInfo {
        ids:
            Ids {
                funs,
                classes,
                typedefs,
                consts,
                modules,
            },
        file_mode,
        position_free_decl_hash,
        comments: _,
    } = info;
    let sn_funs = name_set_of_idl(funs);
    let sn_classes = name_set_of_idl(classes);
    let sn_types = name_set_of_idl(typedefs);
    let sn_consts = name_set_of_idl(consts);
    let sn_modules = name_set_of_idl(modules);
    let s_names = SavedNames {
        funs: sn_funs,
        classes: sn_classes,
        types: sn_types,
        consts: sn_consts,
        modules: sn_modules,
    };
    Saved {
        names: s_names,
        mode: *file_mode,
        position_free_decl_hash: position_free_decl_hash.0,
    }
}

pub fn from_saved(fn_: RelativePath, saved: &Saved) -> T {
    let Saved {
        names: s_names,
        mode: s_mode,
        position_free_decl_hash: s_position_free_decl_hash,
    } = saved;
    let SavedNames {
        funs: sn_funs,
        classes: sn_classes,
        types: sn_types,
        consts: sn_consts,
        modules: sn_modules,
    } = s_names;
    let fn_ = Arc::new(fn_);
    // `S_set.elements` is in increasing order.
    let funs = sn_funs
        .iter()
        .map(|x| Id {
            pos: Pos::File(NameType::Fun, Arc::clone(&fn_)),
            name: x.clone(),
            decl_hash: None,
        })
        .collect();
    let classes = sn_classes
        .iter()
        .map(|x| Id {
            pos: Pos::File(NameType::Class, Arc::clone(&fn_)),
            name: x.clone(),
            decl_hash: None,
        })
        .collect();
    let typedefs = sn_types
        .iter()
        .map(|x| Id {
            pos: Pos::File(NameType::Typedef, Arc::clone(&fn_)),
            name: x.clone(),
            decl_hash: None,
        })
        .collect();
    let consts = sn_consts
        .iter()
        .map(|x| Id {
            pos: Pos::File(NameType::Const, Arc::clone(&fn_)),
            name: x.clone(),
            decl_hash: None,
        })
        .collect();
    let modules = sn_modules
        .iter()
        .map(|m| Id {
            pos: Pos::File(NameType::Module, Arc::clone(&fn_)),
            name: m.clone(),
            decl_hash: None,
        })
        .collect();
    FileInfo {
        file_mode: *s_mode,
        position_free_decl_hash: HashType(*s_position_free_decl_hash),
        ids: Ids {
            funs,
            classes,
            typedefs,
            consts,
            modules,
        },
        comments: None,
    }
}

pub fn saved_to_names(saved: &Saved) -> Names {
    Names {
        funs: saved.names.funs.clone(),
        classes: saved.names.classes.clone(),
        types: saved.names.types.clone(),
        consts: saved.names.consts.clone(),
        modules: saved.names.modules.clone(),
    }
}

/// `S_set.union`
fn s_set_union(s1: &BTreeSet<String>, s2: &BTreeSet<String>) -> BTreeSet<String> {
    s1.union(s2).cloned().collect()
}

/// `S_set.diff`
fn s_set_diff(s1: &BTreeSet<String>, s2: &BTreeSet<String>) -> BTreeSet<String> {
    s1.difference(s2).cloned().collect()
}

pub fn merge_names(t_names1: &Names, t_names2: &Names) -> Names {
    let Names {
        funs: n_funs,
        classes: n_classes,
        types: n_types,
        consts: n_consts,
        modules: n_modules,
    } = t_names1;
    Names {
        funs: s_set_union(n_funs, &t_names2.funs),
        classes: s_set_union(n_classes, &t_names2.classes),
        types: s_set_union(n_types, &t_names2.types),
        consts: s_set_union(n_consts, &t_names2.consts),
        modules: s_set_union(n_modules, &t_names2.modules),
    }
}

fn ids_to_string(ids: &Ids) -> String {
    let Ids {
        classes,
        typedefs,
        consts,
        modules,
        funs,
    } = ids;
    let without_decl_hash = |l: &[Id]| -> Vec<Id> {
        l.iter()
            .map(|id| Id {
                decl_hash: None,
                ..id.clone()
            })
            .collect()
    };
    let funs = without_decl_hash(funs);
    let classes = without_decl_hash(classes);
    let typedefs = without_decl_hash(typedefs);
    let consts = without_decl_hash(consts);
    let modules = without_decl_hash(modules);
    [
        ("funs", funs),
        ("classes", classes),
        ("typedefs", typedefs),
        ("consts", consts),
        ("modules", modules),
    ]
    .into_iter()
    .filter(|(_, l)| !l.is_empty())
    .map(|(kind, l)| {
        format!(
            "{}: {} {}",
            kind,
            l.iter()
                .map(|id| id.name.as_str())
                .collect::<Vec<_>>()
                .join(","),
            l.iter()
                .map(|id| match id.decl_hash {
                    None => "0".to_string(),
                    Some(hash) => decl_hash::to_int64(hash).to_string(),
                })
                .collect::<Vec<_>>()
                .join(",")
        )
    })
    .collect::<Vec<_>>()
    .join(";")
}

pub fn to_string(t: &T) -> String {
    let FileInfo {
        ids,
        file_mode: _,
        position_free_decl_hash: _,
        comments: _,
    } = t;
    ids_to_string(ids)
}

/// Returns `None` when the position-free decl hashes of both files match.
/// Otherwise, as the OCaml does, `None` when some name was removed or added
/// (the flag that it calls `is_empty` is true when a set is *not* empty), and
/// `Some` of the (empty) differences when none was.
pub fn diff(f1: &T, f2: &T) -> Option<Diff> {
    let matches_hash = match (f1.position_free_decl_hash.0, f2.position_free_decl_hash.0) {
        (Some(h1), Some(h2)) => h1 == h2,
        _ => false,
    };
    if matches_hash {
        None
    } else {
        let diff_ids = |ids1: &BTreeSet<String>, ids2: &BTreeSet<String>| {
            let removed_ids = s_set_diff(ids1, ids2);
            let added_ids = s_set_diff(ids2, ids1);
            (removed_ids, added_ids)
        };
        let f1 = simplify(f1);
        let f2 = simplify(f2);
        let (removed_funs, added_funs) = diff_ids(&f1.funs, &f2.funs);
        let (removed_classes, added_classes) = diff_ids(&f1.classes, &f2.classes);
        let (removed_types, added_types) = diff_ids(&f1.types, &f2.types);
        let (removed_consts, added_consts) = diff_ids(&f1.consts, &f2.consts);
        let (removed_modules, added_modules) = diff_ids(&f1.modules, &f2.modules);
        let is_empty = [
            &removed_funs,
            &added_funs,
            &removed_classes,
            &added_classes,
            &removed_types,
            &added_types,
            &removed_consts,
            &added_consts,
            &removed_modules,
            &added_modules,
        ]
        .into_iter()
        .fold(false, |acc, s| !s.is_empty() || acc);
        if is_empty {
            None
        } else {
            Some(Diff {
                removed_funs,
                added_funs,
                removed_classes,
                added_classes,
                removed_types,
                added_types,
                removed_consts,
                added_consts,
                removed_modules,
                added_modules,
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use relative_path::Prefix;

    use super::*;

    fn path(name: &str) -> RelativePath {
        RelativePath::make(Prefix::Root, name.into())
    }

    fn id(pos: Pos, name: &str, decl_hash: Option<i64>) -> Id {
        Id {
            pos,
            name: name.to_string(),
            decl_hash,
        }
    }

    fn set(names: &[&str]) -> BTreeSet<String> {
        names.iter().map(|s| s.to_string()).collect()
    }

    fn file(name_type: NameType) -> Pos {
        Pos::File(name_type, Arc::new(path("a.php")))
    }

    #[test]
    fn old_names_of_names_and_ids() {
        let names = Names {
            funs: set(&["\\f", "\\g"]),
            classes: set(&["\\C"]),
            ..empty_names()
        };
        let unknown = old_names::of_names(&names);
        assert_eq!(unknown.funs.get("\\f"), Some(&None));
        assert_eq!(old_names::to_names(&unknown), names);
        assert_eq!(old_names::to_names(&old_names::empty()), empty_names());
        // The first occurrence of a name wins, an unknown hash included.
        let ids = Ids {
            funs: vec![
                id(file(NameType::Fun), "\\f", Some(1)),
                id(file(NameType::Fun), "\\f", Some(2)),
                id(file(NameType::Fun), "\\g", None),
                id(file(NameType::Fun), "\\g", Some(3)),
            ],
            typedefs: vec![id(file(NameType::Typedef), "\\T", Some(4))],
            ..empty_ids()
        };
        let known = old_names::of_ids(&ids);
        assert_eq!(known.funs.get("\\f"), Some(&Some(1)));
        assert_eq!(known.funs.get("\\g"), Some(&None));
        assert_eq!(known.types.get("\\T"), Some(&Some(4)));
        // Matching hashes are kept; conflicting or unknown ones are unknown.
        let other = old_names::of_ids(&Ids {
            funs: vec![
                id(file(NameType::Fun), "\\f", Some(1)),
                id(file(NameType::Fun), "\\h", Some(5)),
            ],
            typedefs: vec![id(file(NameType::Typedef), "\\T", Some(6))],
            ..empty_ids()
        });
        let merged = old_names::merge(&known, &other);
        assert_eq!(merged.funs.get("\\f"), Some(&Some(1)));
        assert_eq!(merged.funs.get("\\g"), Some(&None));
        assert_eq!(merged.funs.get("\\h"), Some(&Some(5)));
        assert_eq!(merged.types.get("\\T"), Some(&None));
        assert_eq!(
            old_names::show(&old_names::of_ids(&Ids {
                funs: vec![id(file(NameType::Fun), "\\f", Some(1))],
                ..empty_ids()
            })),
            "{ File_info.Old_names.n_funs = { \"\\\\f\" -> (Some 1L) }; n_classes = {};\n  n_types = {}; n_consts = {}; n_modules = {} }"
        );
    }

    fn info() -> T {
        FileInfo {
            position_free_decl_hash: HashType(Some(42)),
            file_mode: Some(Mode::Mstrict),
            ids: Ids {
                funs: vec![
                    id(file(NameType::Fun), "\\g", Some(7)),
                    id(file(NameType::Fun), "\\f", Some(8)),
                ],
                classes: vec![id(file(NameType::Class), "\\C", None)],
                typedefs: vec![],
                consts: vec![id(file(NameType::Const), "\\X", Some(-1))],
                modules: vec![id(file(NameType::Module), "m", None)],
            },
            comments: Some(vec![]),
        }
    }

    /// The text the printer prints on a line wide enough for all of it.
    fn one_line(printer: impl FnOnce(&mut Formatter)) -> String {
        let mut fmt = format::formatter_of_buffer(String::new());
        format::pp_set_margin(&mut fmt, 1_000_000);
        printer(&mut fmt);
        format::flush_buffer_formatter(&mut fmt)
    }

    #[test]
    fn modes() {
        assert!(is_strict(Mode::Mstrict));
        assert!(!is_strict(Mode::Mhhi));
        assert!(is_hhi(Mode::Mhhi));
        assert!(!is_hhi(Mode::Mstrict));
        assert_eq!(string_of_mode(Mode::Mhhi), "hhi");
        assert_eq!(string_of_mode(Mode::Mstrict), "strict");
        assert_eq!(format::asprintf(|fmt| pp_mode(fmt, Mode::Mhhi)), "Mhhi");
        assert_eq!(show_mode(Mode::Mstrict), "File_info.Mstrict");
        for i in MIN_MODE..=MAX_MODE {
            assert_eq!(mode_to_enum(mode_of_enum(i).unwrap()), i);
        }
        assert_eq!(mode_of_enum(2), None);
        assert_eq!(compare_mode(Mode::Mhhi, Mode::Mstrict), Ordering::Less);
    }

    #[test]
    fn name_types() {
        let all = [
            NameType::Fun,
            NameType::Class,
            NameType::Typedef,
            NameType::Const,
            NameType::Module,
        ];
        for nt in all {
            assert_eq!(name_type_of_enum(name_type_to_enum(nt)), Some(nt));
            // The `[@value]`s are the discriminants of the Rust type.
            assert_eq!(name_type_to_enum(nt), nt as isize);
        }
        assert_eq!(name_type_of_enum(2), None);
        assert_eq!(MIN_NAME_TYPE, 0);
        assert_eq!(MAX_NAME_TYPE, 5);
        // Declaration order, unlike the derived `Ord`.
        assert_eq!(
            compare_name_type(NameType::Fun, NameType::Class),
            Ordering::Less
        );
        assert!(NameType::Fun > NameType::Class);
        let mut sorted = all.to_vec();
        sorted.reverse();
        sorted.sort_by(|a, b| compare_name_type(*a, *b));
        assert_eq!(sorted, all.to_vec());
        assert_eq!(show_name_type(NameType::Typedef), "Typedef");
        assert_eq!(show_si_kind(SiKind::SIGlobalConstant), "SI_GlobalConstant");
        assert_eq!(show_si_kind(SiKind::SIXHP), "SI_XHP");
    }

    #[test]
    fn positions() {
        let p = file(NameType::Class);
        assert_eq!(get_pos_filename(&p), path("a.php"));
        let full = pos_full((oxidized::pos::Pos::NONE, "\\f".to_string(), Some(3)));
        assert_eq!(full.pos, Pos::Full(oxidized::pos::Pos::NONE));
        assert_eq!(full.name, "\\f");
        assert_eq!(full.decl_hash, Some(3));
        assert_eq!(decl_hash::to_int64(decl_hash::from_naming_table(-5)), -5);
        assert_eq!(decl_hash::show(&12), "12L");
    }

    #[test]
    fn names() {
        let names = simplify(&info());
        assert_eq!(names.funs, set(&["\\f", "\\g"]));
        assert_eq!(names.classes, set(&["\\C"]));
        assert_eq!(names.types, set(&[]));
        assert_eq!(names.consts, set(&["\\X"]));
        assert_eq!(names.modules, set(&["m"]));
        assert_eq!(ids_to_names(&info().ids), names);
        assert_eq!(ids_to_names(&empty_ids()), empty_names());
        assert_eq!(simplify(&empty_t()), empty_names());
        let other = Names {
            funs: set(&["\\h"]),
            types: set(&["\\T"]),
            ..empty_names()
        };
        let merged = merge_names(&names, &other);
        assert_eq!(merged.funs, set(&["\\f", "\\g", "\\h"]));
        assert_eq!(merged.types, set(&["\\T"]));
        assert_eq!(merged.classes, set(&["\\C"]));
        assert_eq!(merge_names(&empty_names(), &names), names);
    }

    #[test]
    fn saved() {
        let saved = to_saved(&info());
        assert_eq!(saved_to_names(&saved), simplify(&info()));
        let restored = from_saved(path("b.php"), &saved);
        assert_eq!(restored.file_mode, Some(Mode::Mstrict));
        assert_eq!(restored.position_free_decl_hash, HashType(Some(42)));
        assert_eq!(restored.comments, None);
        let b = |nt| Pos::File(nt, Arc::new(path("b.php")));
        // The names come back sorted, with File positions and no hash.
        assert_eq!(
            restored.ids.funs,
            vec![
                id(b(NameType::Fun), "\\f", None),
                id(b(NameType::Fun), "\\g", None),
            ]
        );
        assert_eq!(
            restored.ids.classes,
            vec![id(b(NameType::Class), "\\C", None)]
        );
        assert_eq!(restored.ids.typedefs, vec![]);
        assert_eq!(
            restored.ids.consts,
            vec![id(b(NameType::Const), "\\X", None)]
        );
        assert_eq!(
            restored.ids.modules,
            vec![id(b(NameType::Module), "m", None)]
        );
        assert_eq!(to_saved(&restored), saved);
    }

    #[test]
    fn to_string_drops_the_hashes() {
        // `ids_to_string` sets every `decl_hash` to `None` before printing
        // them, so they are all printed as `0`.
        assert_eq!(
            to_string(&info()),
            "funs: \\g,\\f 0,0;classes: \\C 0;consts: \\X 0;modules: m 0"
        );
        assert_eq!(to_string(&empty_t()), "");
    }

    #[test]
    fn diffs() {
        let f1 = info();
        // Same position-free hash.
        assert_eq!(diff(&f1, &f1.clone()), None);
        // No hash, same names: the empty difference.
        let f1 = FileInfo {
            position_free_decl_hash: HashType(None),
            ..info()
        };
        let empty = Diff {
            removed_funs: set(&[]),
            added_funs: set(&[]),
            removed_classes: set(&[]),
            added_classes: set(&[]),
            removed_types: set(&[]),
            added_types: set(&[]),
            removed_consts: set(&[]),
            added_consts: set(&[]),
            removed_modules: set(&[]),
            added_modules: set(&[]),
        };
        assert_eq!(diff(&f1, &f1.clone()), Some(empty.clone()));
        // Different hashes, same names.
        let f2 = FileInfo {
            position_free_decl_hash: HashType(Some(43)),
            ..info()
        };
        assert_eq!(diff(&info(), &f2), Some(empty));
        // Names removed and added: `None`, as in the OCaml.
        let mut f3 = f1.clone();
        f3.ids.funs.pop();
        f3.ids
            .typedefs
            .push(id(file(NameType::Typedef), "\\T", None));
        assert_eq!(diff(&f1, &f3), None);
    }

    #[test]
    fn printers() {
        assert_eq!(
            show_pos(&file(NameType::Fun)),
            "(File_info.File (Fun, (Relative_path.Root, \"a.php\")))"
        );
        assert_eq!(
            show_pos(&Pos::Full(oxidized::pos::Pos::NONE)),
            "(File_info.Full [Pos.none])"
        );
        assert_eq!(
            show_id(&id(file(NameType::Const), "\\X", Some(-1))),
            "{ File_info.pos = (File_info.File (Const, (Relative_path.Root, \"a.php\")));\n  name = \"\\\\X\"; decl_hash = (Some -1L) }"
        );
        assert_eq!(
            one_line(|fmt| pp_id(fmt, &id(file(NameType::Const), "\\X", Some(-1)))),
            "{ File_info.pos = (File_info.File (Const, (Relative_path.Root, \"a.php\"))); name = \"\\\\X\"; decl_hash = (Some -1L) }"
        );
        let names = Names {
            funs: set(&["\\f", "\\g"]),
            ..empty_names()
        };
        assert_eq!(
            one_line(|fmt| pp_names(fmt, &names)),
            "{ File_info.n_funs = { \"\\\\f\"; \"\\\\g\" }; n_classes = {}; n_types = {}; n_consts = {}; n_modules = {} }"
        );
        let mut t = empty_t();
        t.ids.modules.push(id(file(NameType::Module), "m", None));
        t.comments = Some(vec![(
            oxidized::pos::Pos::NONE,
            Comment::CmtLine("// x\n".to_string()),
        )]);
        assert_eq!(
            one_line(|fmt| pp(fmt, &t)),
            "{ File_info.position_free_decl_hash = None; file_mode = None; ids = { File_info.funs = []; classes = []; typedefs = []; consts = []; modules = [{ File_info.pos = (File_info.File (Module, (Relative_path.Root, \"a.php\"))); name = \"m\"; decl_hash = None }] }; comments = (Some [([Pos.none], (Prim_defs.CmtLine \"// x\\n\"))]) }"
        );
        let t = FileInfo {
            position_free_decl_hash: HashType(Some(5)),
            file_mode: Some(Mode::Mhhi),
            comments: None,
            ..empty_t()
        };
        assert_eq!(
            one_line(|fmt| pp(fmt, &t)),
            "{ File_info.position_free_decl_hash = Some (5); file_mode = (Some Mhhi); ids = { File_info.funs = []; classes = []; typedefs = []; consts = []; modules = [] }; comments = None }"
        );
        let sia = SiAddendum {
            name: "C".to_string(),
            kind: SiKind::SIClass,
            is_abstract: true,
            is_final: false,
        };
        assert_eq!(
            show_si_addendum(&sia),
            "{ File_info.sia_name = \"C\"; sia_kind = SI_Class; sia_is_abstract = true;\n  sia_is_final = false }"
        );
    }
}
