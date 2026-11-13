// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Ast_defs` (`ast/ast_defs.ml`). See `hh/PORTING.md`.
//!
//! The types are those of `oxidized::ast_defs`, re-exported here. This module
//! has the functions of `ast_defs.ml` that `oxidized` lacks and that the port
//! has needed so far.

pub use oxidized::ast_defs::*;

pub fn is_c_interface(kind: ClassishKind) -> bool {
    match kind {
        ClassishKind::Cinterface => true,
        ClassishKind::Cclass(_)
        | ClassishKind::CenumClass(_)
        | ClassishKind::Ctrait
        | ClassishKind::Cenum => false,
    }
}

pub fn is_c_trait(kind: ClassishKind) -> bool {
    match kind {
        ClassishKind::Ctrait => true,
        ClassishKind::Cinterface
        | ClassishKind::CenumClass(_)
        | ClassishKind::Cclass(_)
        | ClassishKind::Cenum => false,
    }
}

pub fn string_of_classish_kind(kind: ClassishKind) -> String {
    match kind {
        ClassishKind::Cclass(c) => match c {
            Abstraction::Abstract => "an abstract class",
            Abstraction::Concrete => "a class",
        },
        ClassishKind::Cinterface => "an interface",
        ClassishKind::Ctrait => "a trait",
        ClassishKind::Cenum => "an enum",
        ClassishKind::CenumClass(c) => match c {
            Abstraction::Abstract => "an abstract enum class",
            Abstraction::Concrete => "an enum class",
        },
    }
    .to_string()
}

// The other functions of `ast_defs.ml` that the typechecker uses (`get_pos`,
// `get_id`, `is_c_class`, `is_c_enum`, `swap_variance`...): see
// `ast_defs/rest.rs`.
mod rest;
pub use rest::*;
