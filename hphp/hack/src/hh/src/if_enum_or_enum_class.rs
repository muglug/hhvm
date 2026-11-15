// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/tast_check/if_enum_or_enum_class.ml`. See `hh/PORTING.md`.

use naming_special_names_rust as sn;

use crate::decl_entry;
use crate::decl_provider;
use crate::tast_env;
use crate::tast_env::Env;
use crate::typing_defs::Ty;
use crate::typing_defs::Ty_;
use crate::typing_defs::get_node;

#[derive(Clone, Debug)]
pub enum Kind {
    Enum {
        name: String,
        class_decl: decl_provider::ClassDecl,
    },
    EnumClass {
        name: String,
        interface: Ty,
        class_decl: decl_provider::ClassDecl,
    },
    EnumClassLabel {
        name: String,
        interface: Ty,
        class_decl: decl_provider::ClassDecl,
    },
}

pub fn name(k: &Kind) -> String {
    match k {
        Kind::Enum {
            name,
            class_decl: _,
        }
        | Kind::EnumClass {
            name,
            interface: _,
            class_decl: _,
        }
        | Kind::EnumClassLabel {
            name,
            interface: _,
            class_decl: _,
        } => name.clone(),
    }
}

pub fn decl(k: &Kind) -> decl_provider::ClassDecl {
    match k {
        Kind::Enum {
            name: _,
            class_decl,
        }
        | Kind::EnumClass {
            name: _,
            interface: _,
            class_decl,
        }
        | Kind::EnumClassLabel {
            name: _,
            interface: _,
            class_decl,
        } => class_decl.clone(),
    }
}

/// The polymorphic variant `` [`EnumClass | `EnumClassLabel] `` of `check_ec`.
#[derive(Clone, Copy)]
enum EcKind {
    EnumClass,
    EnumClassLabel,
}

/// Small reminder:
/// - enums are localized to `Tnewtype (name, _, _)` where name is the name of
///   the enum. This can be checked using `Env.is_enum`
/// - enum classes are not inhabited by design. The type of elements is
///   `HH\MemberOf<name, interface>` were name is the name of the enum class.
///   This is localized as `Tnewtype("HH\MemberOf", [enum; interface])` where
///   enum is localized as Tclass(name, _, _) where Env.is_enum_class name is
///   true.
///
/// Wrapper to share the logic that detects if a type is an enum or an enum
/// class, or something else.
pub fn apply<A>(
    env: &Env,
    default: A,
    f: impl FnOnce(Kind) -> A,
    name: &decl_provider::TypeKey,
    args: &[Ty],
) -> A {
    fn check_ec<A>(
        env: &Env,
        default: A,
        f: impl FnOnce(Kind) -> A,
        kind: EcKind,
        args: &[Ty],
    ) -> A {
        match args {
            [enum_, interface] => match get_node(enum_) {
                Ty_::Tclass((_, cid), _, _) if tast_env::is_enum_class(env, cid) => {
                    // `Option.value_map ~default (Tast_env.get_enum env cid |> Decl_entry.to_option) ~f`
                    match decl_entry::to_option(tast_env::get_enum(env, cid)) {
                        None => default,
                        Some(class_decl) => match kind {
                            EcKind::EnumClass => f(Kind::EnumClass {
                                name: cid.clone(),
                                interface: interface.clone(),
                                class_decl,
                            }),
                            EcKind::EnumClassLabel => f(Kind::EnumClassLabel {
                                name: cid.clone(),
                                interface: interface.clone(),
                                class_decl,
                            }),
                        },
                    }
                }
                _ => default,
            },
            _ => default,
        }
    }
    match tast_env::get_enum(env, name) {
        decl_entry::T::Found(class_decl) => f(Kind::Enum {
            name: name.clone(),
            class_decl,
        }),
        decl_entry::T::DoesNotExist => {
            if name == sn::classes::MEMBER_OF {
                check_ec(env, default, f, EcKind::EnumClass, args)
            } else if name == sn::classes::ENUM_CLASS_LABEL {
                check_ec(env, default, f, EcKind::EnumClassLabel, args)
            } else {
                default
            }
        }
        decl_entry::T::NotYetAvailable => default,
    }
}
