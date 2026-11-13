// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.
//
// @generated <<SignedSource::*O*zOeWoEQle#+L!plEphiEmie@IsG>>
//
// To regenerate this file, run:
//   buck run @fbcode//mode/dev-nosan-lg fbcode//hphp/hack/src:oxidized_regen
use arena_trait::TrivialDrop;
use eq_modulo_pos::EqModuloPos;
use no_pos_hash::NoPosHash;
use serde::Deserialize;
use serde::Serialize;

#[allow(unused_imports)]
use crate::*;

pub use prim_defs::*;

#[derive(
    Clone,
    Copy,
    Debug,
    Deserialize,
    Eq,
    EqModuloPos,
    Hash,
    NoPosHash,
    Ord,
    PartialEq,
    PartialOrd,
    Serialize
)]
#[repr(u8)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::FromOcamlRepIn, ocamlrep::ToOcamlRep))]
pub enum Mode {
    /// just declare signatures, don't check anything
    Mhhi,
    /// check everything!
    Mstrict,
}
impl TrivialDrop for Mode {}
arena_deserializer::impl_deserialize_in_arena!(Mode);

/// This type replicates what's in Naming_types.name_kind, but with less structure.
/// It'd be nice to unify them.
#[derive(
    Clone,
    Copy,
    Debug,
    Deserialize,
    Eq,
    Hash,
    NoPosHash,
    Ord,
    PartialEq,
    PartialOrd,
    Serialize
)]
#[repr(u8)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::FromOcamlRepIn, ocamlrep::ToOcamlRep))]
pub enum NameType {
    Fun = 3,
    Class = 0,
    Typedef = 1,
    Const = 4,
    Module = 5,
}
impl TrivialDrop for NameType {}
arena_deserializer::impl_deserialize_in_arena!(NameType);

/// And here's a version with more detail and still less structure! This
/// one is good for members as well as top-level symbols. It's used to get
/// a bit more out of direct-decl-parse, used to populate the search indexer
/// (e.g. the icon that apepars in autocomplete suggestions).
#[derive(
    Clone,
    Copy,
    Debug,
    Deserialize,
    Eq,
    EqModuloPos,
    Hash,
    NoPosHash,
    Ord,
    PartialEq,
    PartialOrd,
    Serialize
)]
#[repr(u8)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::FromOcamlRepIn, ocamlrep::ToOcamlRep))]
pub enum SiKind {
    SIClass,
    SIInterface,
    SIEnum,
    SITrait,
    SIUnknown,
    SIMixed,
    SIFunction,
    SITypedef,
    SIGlobalConstant,
    SIXHP,
    SINamespace,
    SIClassMethod,
    SILiteral,
    SIClassConstant,
    SIProperty,
    SILocalVariable,
    SIKeyword,
    SIConstructor,
}
impl TrivialDrop for SiKind {}
arena_deserializer::impl_deserialize_in_arena!(SiKind);

/// Yet more details. The "is_abstract" and "is_final" are used e.g. for autocomplete
/// items and to determine whether a type can be suggested e.g. for "$x = new |".
#[derive(
    Clone,
    Debug,
    Deserialize,
    Eq,
    EqModuloPos,
    Hash,
    NoPosHash,
    Ord,
    PartialEq,
    PartialOrd,
    Serialize
)]
#[repr(C)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::ToOcamlRep))]
pub struct SiAddendum {
    /// This is expected not to contain the leading namespace backslash! See [Utils.strip_ns].
    pub name: String,
    pub kind: SiKind,
    pub is_abstract: bool,
    pub is_final: bool,
}

/// We define two types of positions establishing the location of a given name:
/// a Full position contains the exact position of a name in a file, and a
/// File position contains just the file and the type of toplevel entity,
/// allowing us to lazily retrieve the name's exact location if necessary.
#[derive(Clone, Debug, Deserialize, Eq, Hash, NoPosHash, Ord, PartialEq, PartialOrd, Serialize)]
#[repr(C, u8)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::ToOcamlRep))]
pub enum Pos {
    Full(pos::Pos),
    File(NameType, std::sync::Arc<relative_path::RelativePath>),
}

/// An id contains a pos, name and a optional decl hash. The decl hash is None
/// only in the case when we didn't compute it for performance reasons
#[derive(Clone, Debug, Deserialize, Eq, Hash, NoPosHash, Ord, PartialEq, PartialOrd, Serialize)]
#[repr(C)]
pub struct Id {
    pub pos: Pos,
    pub name: String,
    pub decl_hash: Option<decl_hash::DeclHash>,
}

#[derive(
    Clone,
    Debug,
    Deserialize,
    Eq,
    EqModuloPos,
    Hash,
    NoPosHash,
    Ord,
    PartialEq,
    PartialOrd,
    Serialize
)]
#[repr(C)]
pub struct HashType(pub Option<i64>);

#[derive(Clone, Debug, Deserialize, Eq, Hash, NoPosHash, Ord, PartialEq, PartialOrd, Serialize)]
#[repr(C)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::ToOcamlRep))]
pub struct Ids {
    pub funs: Vec<Id>,
    pub classes: Vec<Id>,
    pub typedefs: Vec<Id>,
    pub consts: Vec<Id>,
    pub modules: Vec<Id>,
}

/// The record produced by the parsing phase.
#[derive(Clone, Debug, Deserialize, Eq, Hash, NoPosHash, Ord, PartialEq, PartialOrd, Serialize)]
#[repr(C)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::ToOcamlRep))]
pub struct FileInfo {
    /// The hash value of all the decls stripped of their positions.
    /// We use this to see if two versions of a file are "similar", i.e. their
    /// declarations only differ by position information.
    pub position_free_decl_hash: HashType,
    pub file_mode: Option<Mode>,
    pub ids: Ids,
    /// None if loaded from saved state
    pub comments: Option<Vec<(pos::Pos, Comment)>>,
}

/// a position-free hash of decls in the file, generated by [Direct_decl_parser.parse_and_hash_decls]
pub type PfhHash = i64;

#[derive(Clone, Debug, Deserialize, Eq, Hash, NoPosHash, Ord, PartialEq, PartialOrd, Serialize)]
#[repr(C)]
pub struct Change {
    pub path: relative_path::RelativePath,
    /// [old_ids] is None if the file didn't previously exist
    pub old_ids: Option<Ids>,
    /// [new_ids] is None if the file has been deleted
    pub new_ids: Option<Ids>,
    /// [new_pfh_hash] is None if the file has been deleted
    pub new_pfh_hash: Option<PfhHash>,
}

/// The simplified record used after parsing.
#[derive(Clone, Debug, Deserialize, Eq, Hash, NoPosHash, Ord, PartialEq, PartialOrd, Serialize)]
#[repr(C)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::ToOcamlRep))]
pub struct Names {
    pub funs: s_set::SSet,
    pub classes: s_set::SSet,
    pub types: s_set::SSet,
    pub consts: s_set::SSet,
    pub modules: s_set::SSet,
}

/// The simplified record stored in saved-state.
#[derive(Clone, Debug, Deserialize, Eq, Hash, NoPosHash, Ord, PartialEq, PartialOrd, Serialize)]
#[repr(C)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::ToOcamlRep))]
pub struct SavedNames {
    pub funs: s_set::SSet,
    pub classes: s_set::SSet,
    pub types: s_set::SSet,
    pub consts: s_set::SSet,
    pub modules: s_set::SSet,
}

#[derive(Clone, Debug, Deserialize, Eq, Hash, NoPosHash, Ord, PartialEq, PartialOrd, Serialize)]
#[repr(C)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::ToOcamlRep))]
pub struct Diff {
    pub removed_funs: s_set::SSet,
    pub added_funs: s_set::SSet,
    pub removed_classes: s_set::SSet,
    pub added_classes: s_set::SSet,
    pub removed_types: s_set::SSet,
    pub added_types: s_set::SSet,
    pub removed_consts: s_set::SSet,
    pub added_consts: s_set::SSet,
    pub removed_modules: s_set::SSet,
    pub added_modules: s_set::SSet,
}

// ---- OCaml interop (feature "ocamlrep") ----
/// The hashes are `Int64.t` in OCaml (a boxed integer) and `i64` here: the
/// types that hold one are converted by hand, as the records they are.
#[cfg(feature = "ocamlrep")]
mod ocamlrep_impls {
    use ocamlrep::Allocator;
    use ocamlrep::FromError;
    use ocamlrep::FromOcamlRep;
    use ocamlrep::ToOcamlRep;
    use ocamlrep::Value;
    use ocamlrep::from;
    use ocamlrep_caml_builtins::Int64;

    use super::*;

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
