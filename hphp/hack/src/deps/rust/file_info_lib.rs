// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

// `Id` and `HashType` are converted by hand (see `ocamlrep_impls`), so no
// derive brings their `#[rust_to_ocaml(...)]` attributes into scope.
#[macro_use]
extern crate rust_to_ocaml_attr;

pub(crate) use rc_pos as pos;

mod file_info;
pub use file_info::*;

pub mod prim_defs;

pub mod decl_hash {
    pub type DeclHash = i64;
}

mod s_set {
    pub type SSet = std::collections::BTreeSet<String>;
}

use naming_types::KindOfType;
use relative_path::RelativePath;
use rusqlite::types::FromSql;
use rusqlite::types::FromSqlError;
use rusqlite::types::FromSqlResult;
use rusqlite::types::ValueRef;

impl From<Mode> for parser_core_types::FileMode {
    fn from(mode: Mode) -> Self {
        match mode {
            Mode::Mhhi => Self::Hhi,
            Mode::Mstrict => Self::Strict,
        }
    }
}
impl From<parser_core_types::FileMode> for Mode {
    fn from(mode: parser_core_types::FileMode) -> Self {
        match mode {
            parser_core_types::FileMode::Hhi => Self::Mhhi,
            parser_core_types::FileMode::Strict => Self::Mstrict,
        }
    }
}
impl std::cmp::PartialEq<parser_core_types::FileMode> for Mode {
    fn eq(&self, other: &parser_core_types::FileMode) -> bool {
        self.eq(&Self::from(*other))
    }
}
impl std::cmp::PartialEq<Mode> for parser_core_types::FileMode {
    fn eq(&self, other: &Mode) -> bool {
        self.eq(&Self::from(*other))
    }
}

impl Pos {
    pub fn path(&self) -> &RelativePath {
        match self {
            Pos::Full(pos) => pos.filename(),
            Pos::File(_, path) => path,
        }
    }
}

impl From<KindOfType> for NameType {
    fn from(kind: KindOfType) -> Self {
        match kind {
            KindOfType::TClass => NameType::Class,
            KindOfType::TTypedef => NameType::Typedef,
        }
    }
}

#[derive(Copy, Clone, Debug, thiserror::Error)]
#[error("Expected type kind, but got: {0:?}")]
pub struct FromNameTypeError(NameType);

impl TryFrom<NameType> for KindOfType {
    type Error = FromNameTypeError;
    fn try_from(name_type: NameType) -> Result<Self, Self::Error> {
        match name_type {
            NameType::Class => Ok(KindOfType::TClass),
            NameType::Typedef => Ok(KindOfType::TTypedef),
            _ => Err(FromNameTypeError(name_type)),
        }
    }
}

impl From<NameType> for typing_deps_hash::DepType {
    fn from(name_type: NameType) -> Self {
        match name_type {
            NameType::Fun => Self::KFun,
            NameType::Class => Self::KType,
            NameType::Typedef => Self::KType,
            NameType::Const => Self::KGConst,
            NameType::Module => Self::KModule,
        }
    }
}

impl FromSql for NameType {
    fn column_result(value: ValueRef<'_>) -> FromSqlResult<Self> {
        match value {
            ValueRef::Integer(i) => {
                if i == NameType::Fun as i64 {
                    Ok(NameType::Fun)
                } else if i == NameType::Const as i64 {
                    Ok(NameType::Const)
                } else if i == NameType::Class as i64 {
                    Ok(NameType::Class)
                } else if i == NameType::Typedef as i64 {
                    Ok(NameType::Typedef)
                } else if i == NameType::Module as i64 {
                    Ok(NameType::Module)
                } else {
                    Err(FromSqlError::OutOfRange(i))
                }
            }
            _ => Err(FromSqlError::InvalidType),
        }
    }
}

impl rusqlite::ToSql for NameType {
    fn to_sql(&self) -> rusqlite::Result<rusqlite::types::ToSqlOutput<'_>> {
        Ok(rusqlite::types::ToSqlOutput::from(*self as i64))
    }
}

impl Ids {
    pub fn as_vec(&self) -> Vec<(NameType, Id)> {
        let Ids {
            funs,
            classes,
            typedefs,
            consts,
            modules,
        } = self;
        funs.iter()
            .map(|id| (NameType::Fun, id.clone()))
            .chain(classes.iter().map(|id| (NameType::Class, id.clone())))
            .chain(typedefs.iter().map(|id| (NameType::Typedef, id.clone())))
            .chain(consts.iter().map(|id| (NameType::Const, id.clone())))
            .chain(modules.iter().map(|id| (NameType::Module, id.clone())))
            .collect()
    }
}

/// The hashes are `Int64.t` in OCaml (a boxed integer) and `i64` here, so the
/// types that hold one are converted by hand. `ocamlrep_caml_builtins::Int64`
/// would do it, but that crate links the OCaml runtime (through
/// `ocamlrep_ocamlpool`), which the binaries built without OCaml cannot have;
/// the conversion is the same one, and only a binary that converts a hash
/// refers to `caml_int64_ops`.
mod ocamlrep_impls {
    use ocamlrep::Allocator;
    use ocamlrep::CUSTOM_TAG;
    use ocamlrep::FromError;
    use ocamlrep::FromOcamlRep;
    use ocamlrep::ToOcamlRep;
    use ocamlrep::Value;
    use ocamlrep::from;

    use super::*;

    /// The runtime's `struct custom_operations`, only ever taken by address.
    #[repr(C)]
    struct CustomOperations {
        _private: [u8; 0],
    }

    unsafe extern "C" {
        static caml_int64_ops: CustomOperations;
    }

    #[derive(Clone, Copy)]
    struct Int64(i64);

    impl ToOcamlRep for Int64 {
        fn to_ocamlrep<'a, A: Allocator>(&'a self, alloc: &'a A) -> Value<'a> {
            let mut block = alloc.block_with_size_and_tag(2, CUSTOM_TAG);
            alloc.set_field(&mut block, 0, unsafe {
                Value::from_bits(std::ptr::addr_of!(caml_int64_ops) as usize)
            });
            alloc.set_field(&mut block, 1, unsafe { Value::from_bits(self.0 as usize) });
            block.build()
        }
    }

    impl FromOcamlRep for Int64 {
        fn from_ocamlrep(value: Value<'_>) -> Result<Self, FromError> {
            let block = from::expect_block_with_size_and_tag(value, 2, CUSTOM_TAG)?;
            Ok(Self(block[1].to_bits() as i64))
        }
    }

    fn add_hash<'a, A: Allocator>(alloc: &'a A, hash: Option<i64>) -> Value<'a> {
        alloc.add_copy(hash.map(Int64))
    }

    fn hash_field(block: ocamlrep::Block<'_>, field: usize) -> Result<Option<i64>, FromError> {
        let hash: Option<Int64> = from::field(block, field)?;
        Ok(hash.map(|Int64(hash)| hash))
    }

    impl ToOcamlRep for HashType {
        fn to_ocamlrep<'a, A: Allocator>(&'a self, alloc: &'a A) -> Value<'a> {
            add_hash(alloc, self.0)
        }
    }

    impl FromOcamlRep for HashType {
        fn from_ocamlrep(value: Value<'_>) -> Result<Self, FromError> {
            let hash = Option::<Int64>::from_ocamlrep(value)?;
            Ok(HashType(hash.map(|Int64(hash)| hash)))
        }
    }

    impl ToOcamlRep for Id {
        fn to_ocamlrep<'a, A: Allocator>(&'a self, alloc: &'a A) -> Value<'a> {
            let mut block = alloc.block_with_size(3);
            alloc.set_field(&mut block, 0, alloc.add(&self.pos));
            alloc.set_field(&mut block, 1, alloc.add(&self.name));
            alloc.set_field(&mut block, 2, add_hash(alloc, self.decl_hash));
            block.build()
        }
    }

    impl FromOcamlRep for Id {
        fn from_ocamlrep(value: Value<'_>) -> Result<Self, FromError> {
            let block = from::expect_tuple(value, 3)?;
            Ok(Id {
                pos: from::field(block, 0)?,
                name: from::field(block, 1)?,
                decl_hash: hash_field(block, 2)?,
            })
        }
    }

    impl ToOcamlRep for Change {
        fn to_ocamlrep<'a, A: Allocator>(&'a self, alloc: &'a A) -> Value<'a> {
            let mut block = alloc.block_with_size(4);
            alloc.set_field(&mut block, 0, alloc.add(&self.path));
            alloc.set_field(&mut block, 1, alloc.add(&self.old_ids));
            alloc.set_field(&mut block, 2, alloc.add(&self.new_ids));
            alloc.set_field(&mut block, 3, add_hash(alloc, self.new_pfh_hash));
            block.build()
        }
    }

    impl FromOcamlRep for Change {
        fn from_ocamlrep(value: Value<'_>) -> Result<Self, FromError> {
            let block = from::expect_tuple(value, 4)?;
            Ok(Change {
                path: from::field(block, 0)?,
                old_ids: from::field(block, 1)?,
                new_ids: from::field(block, 2)?,
                new_pfh_hash: hash_field(block, 3)?,
            })
        }
    }
}
