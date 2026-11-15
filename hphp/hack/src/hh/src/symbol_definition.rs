// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/symbol_definition.ml`. See `hh/PORTING.md`.
//!
//! `Server_command_types` carries the types over the socket, so they are
//! `serde`. The derived `show`/`pp` are not ported (nothing in
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

/// The derived `compare` of `'a kind` (`compare Relative_path.compare`).
fn compare_kind(x: &Kind<Pos>, y: &Kind<Pos>) -> std::cmp::Ordering {
    use std::cmp::Ordering;
    fn rank<P>(k: &Kind<P>) -> u8 {
        match k {
            Kind::Function => 0,
            Kind::Classish { .. } => 1,
            Kind::Member { .. } => 2,
            Kind::GlobalConst => 3,
            Kind::LocalVar => 4,
            Kind::TypeVar => 5,
            Kind::Param => 6,
            Kind::Typedef => 7,
            Kind::Module => 8,
        }
    }
    match (x, y) {
        (
            Kind::Classish {
                classish_kind: k1,
                members: m1,
            },
            Kind::Classish {
                classish_kind: k2,
                members: m2,
            },
        ) => (*k1 as u8).cmp(&(*k2 as u8)).then_with(|| compare_list(m1, m2)),
        (
            Kind::Member {
                member_kind: k1,
                class_name: c1,
            },
            Kind::Member {
                member_kind: k2,
                class_name: c2,
            },
        ) => (*k1 as u8).cmp(&(*k2 as u8)).then_with(|| c1.as_bytes().cmp(c2.as_bytes())),
        _ => match rank(x).cmp(&rank(y)) {
            Ordering::Equal => Ordering::Equal,
            o => o,
        },
    }
}

fn compare_list(a: &[T<Pos>], b: &[T<Pos>]) -> std::cmp::Ordering {
    use std::cmp::Ordering;
    for (x, y) in a.iter().zip(b) {
        match compare(x, y) {
            Ordering::Equal => {}
            o => return o,
        }
    }
    a.len().cmp(&b.len())
}

fn compare_opt<A>(a: &Option<A>, b: &Option<A>, f: impl Fn(&A, &A) -> std::cmp::Ordering) -> std::cmp::Ordering {
    use std::cmp::Ordering;
    match (a, b) {
        (None, None) => Ordering::Equal,
        (None, Some(_)) => Ordering::Less,
        (Some(_), None) => Ordering::Greater,
        (Some(a), Some(b)) => f(a, b),
    }
}

/// The derived `compare` of `'a t`, for `Relative_path.t` (`Symbol_definition.compare
/// Relative_path.compare`): the fields in order.
pub fn compare(x: &T<Pos>, y: &T<Pos>) -> std::cmp::Ordering {
    let cmp_pos = |a: &Pos, b: &Pos| {
        crate::pos::compare_pos(|f1, f2| crate::relative_path::compare(f1, f2), a, b)
    };
    compare_kind(&x.kind, &y.kind)
        .then_with(|| x.name.as_bytes().cmp(y.name.as_bytes()))
        .then_with(|| cmp_pos(&x.pos, &y.pos))
        .then_with(|| cmp_pos(&x.span, &y.span))
        .then_with(|| x.modifiers.cmp(&y.modifiers))
        .then_with(|| compare_opt(&x.params, &y.params, |a, b| compare_list(a, b)))
        .then_with(|| compare_opt(&x.docblock, &y.docblock, |a, b| a.as_bytes().cmp(b.as_bytes())))
        .then_with(|| compare_opt(&x.detail, &y.detail, |a, b| a.as_bytes().cmp(b.as_bytes())))
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

/// For a class member definition, a string like `ClassName::memberName`.
/// Otherwise just the `name`.
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

/// A string like <kind>::Type or <kind>::Type::member where `kind` is one of
/// "function", "type_id", "method", etc. None for type var, local var and
/// params
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

/// Whether the list of modifiers contain the 'static' modifier
pub fn is_static(l: &[Modifier]) -> bool {
    l.contains(&Modifier::Static)
}
