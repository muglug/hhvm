// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/symbol_definition.ml`. See `hh/PORTING.md`.
//!
//! The types were ported by the client-connection assignment (D1):
//! `Server_command_types` carries them over the socket, so they are `serde`.
//! The functions are F1's. The derived `show`/`pp` are not ported (nothing in
//! scope prints them); the derived `compare` is not used by any caller in scope.
//!
//! `'a Pos.pos` is the type parameter `P`: `oxidized::pos::Pos`
//! (`Relative_path.t Pos.pos`) or `crate::pos::Absolute` (`string Pos.pos`).

use crate::pos::Absolute;
use crate::pos::Pos;
use serde::Deserialize;
use serde::Serialize;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum ClassishKind {
    Class,
    Interface,
    Trait,
    Enum,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum Modifier {
    Final,
    Static,
    Abstract,
    Private,
    Public,
    Protected,
    Async,
    Inout,
    Internal,
    ProtectedInternal,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum MemberKind {
    Method,
    Property,
    ClassConst,
    TypeConst,
}

/// `'a kind`
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum Kind<P> {
    Function,
    Classish {
        classish_kind: ClassishKind,
        members: Vec<T<P>>,
    },
    Member {
        member_kind: MemberKind,
        class_name: String,
    },
    GlobalConst,
    LocalVar,
    TypeVar,
    Param,
    Typedef,
    Module,
}

/// `'a t`
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct T<P> {
    pub kind: Kind<P>,
    pub name: String,
    /// covers the span of just the identifier
    pub pos: P,
    /// covers the span of the entire construct, including children
    pub span: P,
    pub modifiers: Vec<Modifier>,
    /// For functions and methods, the list of its parameter definitions
    pub params: Option<Vec<T<P>>>,
    /// Only provided on some code paths,
    /// such as FileOutline.outline (but not FileOutline.outline_entry_no_comments)
    pub docblock: Option<String>,
    /// misc. unstructured information about the symbol.
    /// For functions, we include function signature with param names added.
    /// Current use case is providing additional context for AI coding assistants.
    /// Only provided on some code paths: File_outline.outline
    pub detail: Option<String>,
}

pub fn to_absolute(x: &T<Pos>) -> T<Absolute> {
    let T {
        kind,
        name,
        pos,
        span,
        modifiers,
        params,
        docblock,
        detail,
    } = x;
    T {
        kind: kind_to_absolute(kind),
        name: name.clone(),
        pos: crate::pos::to_absolute(pos),
        span: crate::pos::to_absolute(span),
        modifiers: modifiers.clone(),
        params: params.as_ref().map(|x| x.iter().map(to_absolute).collect()),
        docblock: docblock.clone(),
        detail: detail.clone(),
    }
}

fn kind_to_absolute(kind: &Kind<Pos>) -> Kind<Absolute> {
    match kind {
        Kind::Classish {
            classish_kind,
            members,
        } => Kind::Classish {
            classish_kind: *classish_kind,
            members: members.iter().map(to_absolute).collect(),
        },
        Kind::Function => Kind::Function,
        Kind::Member {
            member_kind,
            class_name,
        } => Kind::Member {
            member_kind: *member_kind,
            class_name: class_name.clone(),
        },
        Kind::GlobalConst => Kind::GlobalConst,
        Kind::LocalVar => Kind::LocalVar,
        Kind::TypeVar => Kind::TypeVar,
        Kind::Param => Kind::Param,
        Kind::Typedef => Kind::Typedef,
        Kind::Module => Kind::Module,
    }
}

pub fn to_relative(x: &T<Absolute>) -> T<Pos> {
    let T {
        kind,
        name,
        pos,
        span,
        modifiers,
        params,
        docblock,
        detail,
    } = x;
    T {
        kind: kind_to_relative(kind),
        name: name.clone(),
        pos: crate::pos::to_relative(pos),
        span: crate::pos::to_relative(span),
        modifiers: modifiers.clone(),
        params: params.as_ref().map(|x| x.iter().map(to_relative).collect()),
        docblock: docblock.clone(),
        detail: detail.clone(),
    }
}

fn kind_to_relative(kind: &Kind<Absolute>) -> Kind<Pos> {
    match kind {
        Kind::Classish {
            classish_kind,
            members,
        } => Kind::Classish {
            classish_kind: *classish_kind,
            members: members.iter().map(to_relative).collect(),
        },
        Kind::Function => Kind::Function,
        Kind::Member {
            member_kind,
            class_name,
        } => Kind::Member {
            member_kind: *member_kind,
            class_name: class_name.clone(),
        },
        Kind::GlobalConst => Kind::GlobalConst,
        Kind::LocalVar => Kind::LocalVar,
        Kind::TypeVar => Kind::TypeVar,
        Kind::Param => Kind::Param,
        Kind::Typedef => Kind::Typedef,
        Kind::Module => Kind::Module,
    }
}

pub fn full_name<P>(def: &T<P>) -> String {
    match &def.kind {
        Kind::Member { class_name, .. } => format!("{}::{}", class_name, def.name),
        Kind::Classish { .. }
        | Kind::Typedef
        | Kind::Param
        | Kind::Function
        | Kind::GlobalConst
        | Kind::LocalVar
        | Kind::Module
        | Kind::TypeVar => def.name.clone(),
    }
}

pub fn identifier<P>(def: &T<P>) -> Option<String> {
    match &def.kind {
        Kind::TypeVar => Some(def.name.clone()),
        _ => {
            let kind_string = match &def.kind {
                Kind::Member { member_kind, .. } => match member_kind {
                    MemberKind::Property => Some("property"),
                    MemberKind::ClassConst | MemberKind::TypeConst => Some("class_const"),
                    MemberKind::Method => Some("method"),
                },
                Kind::Classish { .. } | Kind::Typedef => Some("type_id"),
                Kind::Function => Some("function"),
                Kind::GlobalConst => Some("global_const"),
                Kind::Module => Some("module"),
                Kind::TypeVar | Kind::LocalVar | Kind::Param => None,
            };
            match kind_string {
                None => None,
                Some(kind_string) => {
                    let full_name = full_name(def);
                    Some(format!("{}::{}", kind_string, full_name))
                }
            }
        }
    }
}

pub fn string_of_kind<P>(kind: &Kind<P>) -> &'static str {
    match kind {
        Kind::Function => "function",
        Kind::Classish { classish_kind, .. } => match classish_kind {
            ClassishKind::Class => "class",
            ClassishKind::Enum => "enum",
            ClassishKind::Trait => "trait",
            ClassishKind::Interface => "interface",
        },
        Kind::Member { member_kind, .. } => match member_kind {
            MemberKind::Method => "method",
            MemberKind::Property => "property",
            MemberKind::ClassConst => "class constant",
            MemberKind::TypeConst => "typeconst",
        },
        Kind::GlobalConst => "const",
        Kind::LocalVar => "local",
        Kind::TypeVar => "type_var",
        Kind::Param => "param",
        Kind::Typedef => "typedef",
        Kind::Module => "module",
    }
}

pub fn string_of_modifier(m: &Modifier) -> &'static str {
    match m {
        Modifier::Final => "final",
        Modifier::Static => "static",
        Modifier::Abstract => "abstract",
        Modifier::Private => "private",
        Modifier::Public => "public",
        Modifier::Protected => "protected",
        Modifier::Async => "async",
        Modifier::Inout => "inout",
        Modifier::Internal => "internal",
        Modifier::ProtectedInternal => "protected internal",
    }
}

pub fn is_static(l: &[Modifier]) -> bool {
    l.contains(&Modifier::Static)
}
