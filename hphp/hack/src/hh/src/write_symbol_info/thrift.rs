// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Write_symbol_info.Thrift` (`write_symbol_info/thrift.ml`).
//!
//! This module is used to generate fbthrift.declaration facts from
//! hack entities generated from Thrift.
//!
//! For generated hack classes or field/function members,
//! a thrift declaration can be constructed from one or more
//! of the following:
//! - the doc comment of the generated entity
//! - the entity name (for union, and enum fields).
//! - the context in which it appears (enclosing class,
//!     thrift source of generated file...)
//!
//! The entity comment isn't always sufficient and some context [t] must
//! be maintain at the file level

use std::collections::HashMap;
use std::sync::LazyLock;

use oxidized::aast;
use oxidized::aast_defs;
use oxidized::ast_defs;
use regex::Regex;

use super::glean::fbthrift::constant;
use super::glean::fbthrift::declaration;
use super::glean::fbthrift::enum_value;
use super::glean::fbthrift::exception_name;
use super::glean::fbthrift::field_decl;
use super::glean::fbthrift::field_kind;
use super::glean::fbthrift::file;
use super::glean::fbthrift::function_name;
use super::glean::fbthrift::identifier;
use super::glean::fbthrift::named_decl;
use super::glean::fbthrift::named_kind;
use super::glean::fbthrift::named_type;
use super::glean::fbthrift::qual_name;
use super::glean::fbthrift::service_name;
use super::glean::fbthrift::x_ref_target;
use super::glean::src;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kind {
    Exception,
    Struct,
    Union,
    Service,
    Enum,
}

#[derive(Clone, Debug)]
struct Container {
    name: String,
    kind: Kind,
}

/// Defines a mutable context used when processing generated entities.
pub struct T {
    thrift_path: String,
    services: HashMap<String, String>,
    cur_container: Option<Container>,
    cur_union_fields: Vec<String>,
}

/// Empty context, [thrift_path] is the path relative to repo root
/// of the source thrift file
pub fn empty(thrift_path: String) -> T {
    T {
        thrift_path,
        services: HashMap::new(),
        cur_container: None,
        cur_union_fields: vec![],
    }
}

fn add(t: &mut T, interface: &str, service: &str) {
    t.services.insert(interface.to_string(), service.to_string());
}

fn lookup(t: &T, interfaces: &[String]) -> Option<String> {
    interfaces.iter().find_map(|i| t.services.get(i).cloned())
}

const REX_ID: &str = r"(\w(?:\w|\.)+)";

const REX_TY: &str = r"(?:\w|<|>|\.|, )+";

/// `"(?:\\s|\\*|\\d|\\:|\\-)*"` (PCRE's `\:` and `\-` are `:` and `-`).
const REX_SP: &str = r"(?:\s|\*|\d|:|-)*";

/// The PCRE regexps (without the UTF flag: `\w`, `\s`, `\d` are ASCII
/// classes, as with `(?-u)`; `MULTILINE` changes nothing here, they have no
/// `^` or `$`).
static REX_CONTAINER: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(&format!(
        "(?m-u)Original thrift (struct|service|exception|union|enum):-{}{}",
        REX_SP, REX_ID
    ))
    .unwrap()
});

static REX_MEMBER: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(&format!(
        "(?m-u)Original thrift (field|definition|constant):-{}{}{}{}",
        REX_SP, REX_TY, REX_SP, REX_ID
    ))
    .unwrap()
});

fn get_thrift_from_container_aux(thrift_path: &str, doc: &str) -> Option<(Container, declaration::T)> {
    let substrings = REX_CONTAINER.captures(doc)?;
    let kind = substrings.get(1)?.as_str();
    let name = substrings.get(2)?.as_str().to_string();
    let identifier = identifier::T::key(name.clone());
    let file = file::T::key(src::file::T::key(thrift_path.to_string()));
    let qname = qual_name::T::key(qual_name::Key {
        file,
        name: identifier,
    });
    let named = |kind| {
        x_ref_target::T::Named(named_decl::T::key(named_decl::Key {
            name: named_type::T { name: qname.clone(), kind },
        }))
    };
    match kind {
        "service" => {
            let serv = service_name::T::key(service_name::Key { name: qname.clone() });
            let xref_target = x_ref_target::T::Service_(serv);
            Some((Container { name, kind: Kind::Service }, xref_target))
        }
        "struct" => Some((Container { name, kind: Kind::Struct }, named(named_kind::T::Struct_))),
        "union" => Some((Container { name, kind: Kind::Union }, named(named_kind::T::Union_))),
        "enum" => Some((Container { name, kind: Kind::Enum }, named(named_kind::T::Enum_))),
        "exception" => {
            let xref_target = x_ref_target::T::Exception_(exception_name::T::key(exception_name::Key {
                name: qname.clone(),
            }));
            Some((Container { name, kind: Kind::Exception }, xref_target))
        }
        // (`failwith "internal error"`, caught by the `with _ -> None` of
        // the function.)
        _ => None,
    }
}

/// Parses a hack container doc comment and generate thrift decl fact.
///
/// Side effect: store in context Thrift container declaration
pub fn get_thrift_from_container<Ex, En>(t: &mut T, con: &aast_defs::Class_<Ex, En>) -> Option<declaration::T> {
    let (container, fact) = match &con.doc_comment {
        Some((_, doc)) => match get_thrift_from_container_aux(&t.thrift_path, doc) {
            Some((container, fact)) => (Some(container), Some(fact)),
            None => (None, None),
        },
        None => (None, None),
    };
    if let (
        Some(Container {
            name,
            kind: Kind::Service,
        }),
        ast_defs::ClassishKind::Cinterface,
    ) = (&container, &con.kind)
    {
        add(t, &con.name.1, name)
    }
    let implements_to_string = |h: &aast::Hint| match &*h.1 {
        aast_defs::Hint_::Happly(ast_defs::Id(_, x), _) => Some(x.clone()),
        _ => None,
    };
    let container = match (&con.kind, &container) {
        (ast_defs::ClassishKind::Cclass(_), None) => {
            let interfaces: Vec<String> = con.implements.iter().filter_map(implements_to_string).collect();
            match lookup(t, &interfaces) {
                Some(service) => Some(Container {
                    name: service,
                    kind: Kind::Service,
                }),
                None => container,
            }
        }
        _ => container,
    };
    if let Some(container) = container {
        t.cur_container = Some(container)
    }
    t.cur_union_fields = vec![];
    fact
}

fn make_member_decl(member_name: &str, container_qname: qual_name::T, kind: Kind) -> x_ref_target::T {
    let name = container_qname;
    let mname = identifier::T::key(member_name.to_string());
    let field = |kind| {
        x_ref_target::T::Field(field_decl::T::key(field_decl::Key {
            qname: name.clone(),
            kind,
            name: mname.clone(),
        }))
    };
    match kind {
        Kind::Service => x_ref_target::T::Function_(function_name::T::key(function_name::Key {
            service_: service_name::T::key(service_name::Key { name: name.clone() }),
            name: mname.clone(),
        })),
        Kind::Struct => field(field_kind::T::Struct_),
        Kind::Union => field(field_kind::T::Union_),
        Kind::Exception => field(field_kind::T::Exception_),
        Kind::Enum => x_ref_target::T::EnumValue(enum_value::T::key(enum_value::Key {
            enum_: named_type::T {
                name: name.clone(),
                kind: named_kind::T::Enum_,
            },
            name: mname.clone(),
        })),
    }
}

/// Parses a hack member function or field doc comment and generates
/// the corresponding declaration thrift fact. Assumes
/// [get_thrift_from_container] was called immediately before on
/// the enclosing container.
///
/// Side effect, for hack fields generated from Thrift union field, remember
/// Thrift field name in context [t]
pub fn get_thrift_from_comment(t: &mut T, doc: &str) -> Option<declaration::T> {
    let substrings = REX_MEMBER.captures(doc)?;
    let member_name = substrings.get(2)?.as_str().to_string();
    let file = file::T::key(src::file::T::key(t.thrift_path.clone()));
    match t.cur_container.clone() {
        Some(Container { name, kind }) => {
            if kind == Kind::Union {
                t.cur_union_fields.insert(0, member_name.clone())
            }
            let name = identifier::T::key(name);
            let container_qname = qual_name::T::key(qual_name::Key { file, name });
            Some(make_member_decl(&member_name, container_qname, kind))
        }
        None => {
            let member_name = identifier::T::key(member_name);
            let name = qual_name::T::key(qual_name::Key {
                file,
                name: member_name,
            });
            Some(x_ref_target::T::Constant(constant::T::key(constant::Key { name })))
        }
    }
}

/// Generate thrift declaration fact from an enumerator.
/// Assume [get_thrift_from_container] was called immediately before on the
/// enclosing enum declaration.
pub fn get_thrift_from_enum(t: &T, member_name: &str) -> Option<declaration::T> {
    let Container { name, kind } = t.cur_container.clone()?;
    let name = identifier::T::key(name);
    let file = file::T::key(src::file::T::key(t.thrift_path.clone()));
    let container_qname = qual_name::T::key(qual_name::Key { file, name });
    Some(make_member_decl(member_name, container_qname, kind))
}

/// Generate thrift declaration fact for class members generated from union fields.
/// Assume [get_thrift_from_container] was called on the enclosing container,
/// and [get_thrift_from_comment] on the first union field.
pub fn get_thrift_from_union_member(t: &T, member_name: &str) -> Option<declaration::T> {
    let Container { name, kind } = t.cur_container.clone()?;
    let union_field_name = t
        .cur_union_fields
        .iter()
        .find(|suffix| member_name.ends_with(suffix.as_str()))?;
    match kind {
        Kind::Union => {
            let file = file::T::key(src::file::T::key(t.thrift_path.clone()));
            let name = identifier::T::key(name);
            let container_qname = qual_name::T::key(qual_name::Key { file, name });
            Some(make_member_decl(union_field_name, container_qname, kind))
        }
        _ => None,
    }
}
