// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `search/utils/search_types.ml`. See `hh/PORTING.md`.
//!
//! The autocomplete and symbol-index types are those of `oxidized`
//! (`oxidized::search_types`, re-exported): `autocomplete_type` is
//! [`AutocompleteType`], `si_file` [`SiFile`], `si_item` [`SiItem`] (fields
//! without the prefix `si_`), `si_complete` [`SiComplete`].
//! `Find_refs.member` and `Find_refs.action` have no `[@@deriving show]`
//! printers here (`Find_refs_wire_format.CliArgs` builds them when it parses
//! `--ide-find-refs-by-symbol`).

pub use oxidized::search_types::*;

use crate::file_info::SiKind;
use crate::format;
use crate::format::Formatter;

/// `[@@deriving show { with_path = false }]` of `autocomplete_type`.
pub fn pp_autocomplete_type(fmt: &mut Formatter, x: AutocompleteType) {
    format::pp_print_string(
        fmt,
        match x {
            AutocompleteType::Acid => "Acid",
            AutocompleteType::Acclassish => "Acclassish",
            AutocompleteType::Acnew => "Acnew",
            AutocompleteType::Actype => "Actype",
            AutocompleteType::ActraitOnly => "Actrait_only",
            AutocompleteType::AcWorkspaceSymbol => "Ac_workspace_symbol",
        },
    )
}

pub fn show_autocomplete_type(x: AutocompleteType) -> String {
    format::asprintf(|fmt| pp_autocomplete_type(fmt, x))
}

/// `[@@deriving eq]`
pub fn equal_autocomplete_type(a: AutocompleteType, b: AutocompleteType) -> bool {
    a == b
}

/// `[@@deriving eq]`
pub fn equal_si_complete(a: SiComplete, b: SiComplete) -> bool {
    a == b
}

/// Convert the enum to an integer whose value will not change accidentally.
///
/// Although [@@deriving] would be a very ocaml-ish way to solve this same
/// problem, we would run the risk that anyone who edits the code to reorder
/// list of si_kinds, perhaps by adding something new in its correct
/// alphabetic order, would cause unexpected autocomplete behavior due to
/// mismatches between the [@@deriving] ordinal values and the integers
/// stored in sqlite.
pub fn kind_to_int(kind: SiKind) -> isize {
    match kind {
        SiKind::SIClass => 1,
        SiKind::SIInterface => 2,
        SiKind::SIEnum => 3,
        SiKind::SITrait => 4,
        SiKind::SIUnknown => 5,
        SiKind::SIMixed => 6,
        SiKind::SIFunction => 7,
        SiKind::SITypedef => 8,
        SiKind::SIGlobalConstant => 9,
        SiKind::SIXHP => 10,
        SiKind::SINamespace => 11,
        SiKind::SIClassMethod => 12,
        SiKind::SILiteral => 13,
        SiKind::SIClassConstant => 14,
        SiKind::SIProperty => 15,
        SiKind::SILocalVariable => 16,
        SiKind::SIKeyword => 17,
        SiKind::SIConstructor => 18,
    }
}

/// Convert an integer back to an enum
pub fn int_to_kind(kind_num: isize) -> SiKind {
    match kind_num {
        1 => SiKind::SIClass,
        2 => SiKind::SIInterface,
        3 => SiKind::SIEnum,
        4 => SiKind::SITrait,
        5 => SiKind::SIUnknown,
        6 => SiKind::SIMixed,
        7 => SiKind::SIFunction,
        8 => SiKind::SITypedef,
        9 => SiKind::SIGlobalConstant,
        10 => SiKind::SIXHP,
        11 => SiKind::SINamespace,
        12 => SiKind::SIClassMethod,
        13 => SiKind::SILiteral,
        14 => SiKind::SIClassConstant,
        15 => SiKind::SIProperty,
        16 => SiKind::SILocalVariable,
        17 => SiKind::SIKeyword,
        18 => SiKind::SIConstructor,
        _ => SiKind::SIUnknown,
    }
}

/// ACID represents a statement.  Everything other than interfaces are valid
pub fn valid_for_acid(kind: SiKind) -> bool {
    !matches!(kind, SiKind::SIMixed | SiKind::SIUnknown | SiKind::SIInterface)
}

/// ACTYPE represents a type definition that can be passed as a parameter
pub fn valid_for_actype(kind: SiKind) -> bool {
    !matches!(
        kind,
        SiKind::SIMixed
            | SiKind::SIUnknown
            | SiKind::SITrait
            | SiKind::SIFunction
            | SiKind::SIGlobalConstant
    )
}

/// Acclassish represents entities that parse as ClassishDeclaration
pub fn valid_for_acclassish(kind: SiKind) -> bool {
    matches!(
        kind,
        SiKind::SIClass | SiKind::SIInterface | SiKind::SIEnum | SiKind::SITrait | SiKind::SIXHP
    )
}

/// ACNEW represents instantiation of an object. (Caller should also verify that it's not abstract.)
pub fn valid_for_acnew(kind: SiKind) -> bool {
    matches!(kind, SiKind::SIClass | SiKind::SIXHP)
}

/// `Search_types.Find_refs`
pub mod find_refs {
    use crate::file_content;
    use crate::relative_path::RelativePath;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Member {
        Method(String),
        Property(String),
        ClassConst(String),
        Typeconst(String),
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Action {
        /// When user does find-all-refs on Foo::f or self::f or parent::f, it
        /// produces `Class "Foo"` and passes this to serverFindRefs. As
        /// expected, it will find all references to the class Foo, including
        /// self:: and parent:: references. Class is used for all typelikes --
        /// typedefs, enums, enum classes, classes, interfaces, traits
        Class(String),
        /// When user does rename of Foo to Bar, then serverRename produces
        /// `ExplicitClass "Foo"` and passes this to serverFindRefs. This will
        /// only find the explicit references to the class Foo, not including
        /// self:: and parent::, since they shouldn't be renamed.
        ExplicitClass(String),
        Member(String, Member),
        Function(String),
        GConst(String),
        LocalVar {
            filename: RelativePath,
            file_content: String,
            pos: file_content::position::T,
        },
    }

    // `'a result`, `t` and `absolute`, used by
    // `Server_command_types.Find_refs` (they cross the socket, so `Result` is
    // `serde`; `Member` and `Action` get theirs in `crate::rt::protocol`).

    /// `'a result`
    #[derive(Clone, Debug, PartialEq, serde::Serialize, serde::Deserialize)]
    pub struct Result<P> {
        pub name: String,
        pub pos: P,
    }

    /// Read: Pos.t and Pos.absolute
    pub type T = Result<oxidized::pos::Pos>;

    pub type Absolute = Result<crate::pos::Absolute>;
}
