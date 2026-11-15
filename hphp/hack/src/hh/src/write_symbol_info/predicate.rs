// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Write_symbol_info.Predicate` (`write_symbol_info/predicate.ml`).

use std::collections::BTreeMap;
use std::collections::HashMap;

use oxidized::ast_defs::ClassishKind;

use super::glean::fact_id;
use super::glean::hack::class_declaration;
use super::glean::hack::container_declaration;
use super::glean::hack::declaration;
use super::glean::hack::interface_declaration;
use super::glean::hack::q_name;
use super::glean::hack::trait_declaration;
use super::xrefs;
use crate::yojson::safe as yojson;

/// Predicate types for the JSON facts emitted
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Hack {
    ClassConstDeclaration,
    ClassConstDefinition,
    ClassDeclaration,
    ClassDefinition,
    DeclarationComment,
    DeclarationLocation,
    DeclarationSpan,
    EnumDeclaration,
    EnumDefinition,
    Enumerator,
    FileDeclarations,
    FilePackage,
    FileXRefs,
    FunctionDeclaration,
    FunctionDefinition,
    GlobalConstDeclaration,
    GlobalConstDefinition,
    InheritedMembers,
    InterfaceDeclaration,
    InterfaceDefinition,
    MemberCluster,
    MethodDeclaration,
    MethodDefinition,
    MethodOccurrence,
    MethodOverrides,
    NamespaceDeclaration,
    PropertyDeclaration,
    PropertyDefinition,
    TargetNotUsedInProdBuild,
    TraitDeclaration,
    TraitDefinition,
    TypeConstDeclaration,
    TypeConstDefinition,
    TypedefDeclaration,
    TypedefDefinition,
    ModuleDeclaration,
    ModuleDefinition,
    FileCall,
    GlobalNamespaceAlias,
    IndexerInputsHash,
    TypeInfo,
    HackToThrift,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Src {
    FileLines,
    IndexFailure,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Gencode {
    GenCode,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum T {
    Hack(Hack),
    Src(Src),
    Gencode(Gencode),
}

pub type Predicate = T;

pub fn compare_predicate(a: &T, b: &T) -> std::cmp::Ordering {
    a.cmp(b)
}

pub fn gencode_to_string(x: Gencode) -> &'static str {
    match x {
        Gencode::GenCode => "GenCode",
    }
}

pub fn hack_to_string(x: Hack) -> &'static str {
    match x {
        Hack::ClassConstDeclaration => "ClassConstDeclaration",
        Hack::ClassConstDefinition => "ClassConstDefinition",
        Hack::ClassDeclaration => "ClassDeclaration",
        Hack::ClassDefinition => "ClassDefinition",
        Hack::DeclarationComment => "DeclarationComment",
        Hack::DeclarationLocation => "DeclarationLocation",
        Hack::DeclarationSpan => "DeclarationSpan",
        Hack::EnumDeclaration => "EnumDeclaration",
        Hack::EnumDefinition => "EnumDefinition",
        Hack::Enumerator => "Enumerator",
        Hack::FileDeclarations => "FileDeclarations",
        Hack::FilePackage => "FilePackage",
        Hack::FileXRefs => "FileXRefs",
        Hack::FunctionDeclaration => "FunctionDeclaration",
        Hack::FunctionDefinition => "FunctionDefinition",
        Hack::GlobalConstDeclaration => "GlobalConstDeclaration",
        Hack::GlobalConstDefinition => "GlobalConstDefinition",
        Hack::InheritedMembers => "InheritedMembers",
        Hack::InterfaceDeclaration => "InterfaceDeclaration",
        Hack::InterfaceDefinition => "InterfaceDefinition",
        Hack::MemberCluster => "MemberCluster",
        Hack::MethodDeclaration => "MethodDeclaration",
        Hack::MethodDefinition => "MethodDefinition",
        Hack::MethodOccurrence => "MethodOccurrence",
        Hack::MethodOverrides => "MethodOverrides",
        Hack::NamespaceDeclaration => "NamespaceDeclaration",
        Hack::PropertyDeclaration => "PropertyDeclaration",
        Hack::PropertyDefinition => "PropertyDefinition",
        Hack::TargetNotUsedInProdBuild => "TargetNotUsedInProdBuild",
        Hack::TraitDeclaration => "TraitDeclaration",
        Hack::TraitDefinition => "TraitDefinition",
        Hack::TypeConstDeclaration => "TypeConstDeclaration",
        Hack::TypeConstDefinition => "TypeConstDefinition",
        Hack::TypedefDeclaration => "TypedefDeclaration",
        Hack::TypedefDefinition => "TypedefDefinition",
        Hack::ModuleDeclaration => "ModuleDeclaration",
        Hack::ModuleDefinition => "ModuleDefinition",
        Hack::FileCall => "FileCall",
        Hack::GlobalNamespaceAlias => "GlobalNamespaceAlias",
        Hack::IndexerInputsHash => "IndexerInputsHash",
        Hack::TypeInfo => "TypeInfo",
        Hack::HackToThrift => "HackToThrift",
    }
}

/// List of all predicates, in the order in which they should appear in the JSON.
/// This guarantee that facts are introduced before they are referenced.
pub const ORDERED_ALL: [T; 45] = [
    T::Gencode(Gencode::GenCode),
    T::Hack(Hack::MethodOccurrence),
    T::Hack(Hack::NamespaceDeclaration),
    T::Hack(Hack::GlobalConstDeclaration),
    T::Hack(Hack::TypedefDeclaration),
    T::Hack(Hack::ModuleDeclaration),
    T::Hack(Hack::InterfaceDeclaration),
    T::Hack(Hack::TraitDeclaration),
    T::Hack(Hack::ClassDeclaration),
    T::Hack(Hack::EnumDeclaration),
    T::Hack(Hack::Enumerator),
    T::Hack(Hack::FunctionDeclaration),
    T::Hack(Hack::TypeConstDeclaration),
    T::Hack(Hack::PropertyDeclaration),
    T::Hack(Hack::ClassConstDeclaration),
    T::Hack(Hack::MethodDeclaration),
    T::Hack(Hack::TypeInfo),
    T::Hack(Hack::DeclarationSpan),
    T::Hack(Hack::DeclarationLocation),
    T::Hack(Hack::DeclarationComment),
    T::Hack(Hack::MemberCluster),
    T::Hack(Hack::InheritedMembers),
    T::Hack(Hack::GlobalConstDefinition),
    T::Hack(Hack::TypedefDefinition),
    T::Hack(Hack::ModuleDefinition),
    T::Hack(Hack::InterfaceDefinition),
    T::Hack(Hack::TraitDefinition),
    T::Hack(Hack::ClassDefinition),
    T::Hack(Hack::TypeConstDefinition),
    T::Hack(Hack::PropertyDefinition),
    T::Hack(Hack::ClassConstDefinition),
    T::Hack(Hack::EnumDefinition),
    T::Hack(Hack::FunctionDefinition),
    T::Hack(Hack::MethodDefinition),
    T::Hack(Hack::MethodOverrides),
    T::Hack(Hack::FileXRefs),
    T::Hack(Hack::FileDeclarations),
    T::Hack(Hack::FilePackage),
    T::Hack(Hack::TargetNotUsedInProdBuild),
    T::Hack(Hack::FileCall),
    T::Hack(Hack::GlobalNamespaceAlias),
    T::Hack(Hack::IndexerInputsHash),
    T::Hack(Hack::HackToThrift),
    T::Src(Src::FileLines),
    T::Src(Src::IndexFailure),
];

pub fn src_to_string(x: Src) -> &'static str {
    match x {
        Src::FileLines => "FileLines",
        Src::IndexFailure => "IndexFailure",
    }
}

pub fn to_string(x: T) -> String {
    match x {
        T::Hack(x) => format!("hack.{}.6", hack_to_string(x)),
        T::Src(x) => format!("src.{}.1", src_to_string(x)),
        T::Gencode(x) => format!("gencode.{}.1", gencode_to_string(x)),
    }
}

/// Containers in inheritance relationships which share the four member
/// types (excludes enum)
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ParentContainerType {
    ClassContainer,
    InterfaceContainer,
    TraitContainer,
}

pub fn parent_decl_predicate(parent_container_type: ParentContainerType) -> T {
    match parent_container_type {
        ParentContainerType::ClassContainer => T::Hack(Hack::ClassDeclaration),
        ParentContainerType::InterfaceContainer => T::Hack(Hack::InterfaceDeclaration),
        ParentContainerType::TraitContainer => T::Hack(Hack::TraitDeclaration),
    }
}

pub fn container_decl(container_type: ParentContainerType, id: fact_id::T) -> container_declaration::T {
    match container_type {
        ParentContainerType::ClassContainer => {
            container_declaration::T::Class_(class_declaration::T::Id(id))
        }
        ParentContainerType::InterfaceContainer => {
            container_declaration::T::Interface_(interface_declaration::T::Id(id))
        }
        ParentContainerType::TraitContainer => {
            container_declaration::T::Trait(trait_declaration::T::Id(id))
        }
    }
}

pub fn container_decl_qname(container_type: ParentContainerType, name: q_name::T) -> container_declaration::T {
    match container_type {
        ParentContainerType::ClassContainer => container_declaration::T::Class_(
            class_declaration::T::key(class_declaration::Key { name }),
        ),
        ParentContainerType::InterfaceContainer => container_declaration::T::Interface_(
            interface_declaration::T::key(interface_declaration::Key { name }),
        ),
        ParentContainerType::TraitContainer => container_declaration::T::Trait(
            trait_declaration::T::key(trait_declaration::Key { name }),
        ),
    }
}

pub fn container_ref(container_type: ParentContainerType, id: fact_id::T) -> declaration::T {
    declaration::T::Container(container_decl(container_type, id))
}

/// `Failure` raised by `classish_to_predicate` and `get_parent_kind` (the
/// message of the exception).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Failure(pub String);

impl Failure {
    /// `Exn.to_string` of the exception: its S-expression,
    /// `(Failure "the message")`.
    pub fn exn_to_string(&self) -> String {
        crate::rt::ocaml_exn::Uncaught::failure(self.0.as_str()).to_string()
    }
}

/// will fail if kind is an enum
pub fn classish_to_predicate(kind: &ClassishKind) -> Result<(ParentContainerType, T), Failure> {
    match kind {
        ClassishKind::Cinterface => Ok((
            ParentContainerType::InterfaceContainer,
            T::Hack(Hack::InterfaceDeclaration),
        )),
        ClassishKind::Ctrait => Ok((ParentContainerType::TraitContainer, T::Hack(Hack::TraitDeclaration))),
        ClassishKind::Cclass(_) => Ok((ParentContainerType::ClassContainer, T::Hack(Hack::ClassDeclaration))),
        _ => Err(Failure("Unexpected enum class".to_string())),
    }
}

pub fn get_parent_kind(kind: &ClassishKind) -> Result<ParentContainerType, Failure> {
    match kind {
        ClassishKind::CenumClass(_) => Err(Failure(
            "Unexpected enum class as parent container kind".to_string(),
        )),
        ClassishKind::Cenum => Err(Failure("Unexpected enum as parent container kind".to_string())),
        ClassishKind::Cinterface => Ok(ParentContainerType::InterfaceContainer),
        ClassishKind::Ctrait => Ok(ParentContainerType::TraitContainer),
        ClassishKind::Cclass(_) => Ok(ParentContainerType::ClassContainer),
    }
}

pub fn should_cache(p: T) -> bool {
    matches!(
        p,
        T::Hack(
            Hack::ClassConstDeclaration
                | Hack::ClassDeclaration
                | Hack::EnumDeclaration
                | Hack::Enumerator
                | Hack::FunctionDeclaration
                | Hack::GlobalConstDeclaration
                | Hack::InterfaceDeclaration
                | Hack::MethodDeclaration
                | Hack::PropertyDeclaration
                | Hack::TraitDeclaration
                | Hack::TypeConstDeclaration
                | Hack::TypedefDeclaration
                | Hack::ModuleDeclaration
        )
    )
}

/// `Predicate.Map`.
pub type Map<V> = BTreeMap<T, V>;

pub mod fact_acc {
    //! fact accumulator. This is used to maintain state through indexing
    //! a batch. State is mostly generated facts

    use super::*;

    pub type OwnershipUnit = Option<String>;

    /// `owned_facts`: `(ownership_unit * Yojson.Safe.t list) list`. The
    /// OCaml list is built by consing at its head, and each list of facts
    /// too; here both are vectors in the order they were built, so the head
    /// of each OCaml list is the LAST element of its vector (`to_json`
    /// reverses).
    pub type OwnedFacts = Vec<(OwnershipUnit, Vec<yojson::T>)>;

    /// The fact accumulator. The OCaml record is threaded as a value whose
    /// maps are persistent; every caller uses only the latest one, so here it
    /// is one value changed in place (`&mut T`).
    pub struct T {
        result_json: Map<OwnedFacts>,
        /// `factIds`: `Fact_id.t JsonPredicateMap.t`, keyed by
        /// `(ownership_unit, json, predicate)` compared with
        /// `Stdlib.compare`. It is only looked up, never iterated, so it is a
        /// hash table here, keyed by the compact JSON text of the key (two
        /// `Yojson.Safe.t` are equal under `Stdlib.compare` exactly when their
        /// texts are: these keys hold no floats).
        fact_ids: HashMap<(OwnershipUnit, String, Predicate), fact_id::T>,
        ownership_unit: OwnershipUnit,
        xrefs: Option<xrefs::PosMap>,
        generated_from: Option<String>,
        ownership: bool,
    }

    /// if ownership is set, we distinguish facts with different owners,
    /// otherwise we "collapse" the ownership_unit to None.
    fn cache_key(
        ownership: bool,
        ownership_unit: &OwnershipUnit,
        json_key: &yojson::T,
        predicate: Predicate,
    ) -> (OwnershipUnit, String, Predicate) {
        if ownership {
            (ownership_unit.clone(), yojson::to_string(json_key), predicate)
        } else {
            (None, yojson::to_string(json_key), predicate)
        }
    }

    fn add_to_owned_facts(ownership_unit: &OwnershipUnit, json: yojson::T, l: &mut OwnedFacts) {
        match l.last_mut() {
            Some((ou, jsons)) if ou == ownership_unit => jsons.push(json),
            _ => l.push((ownership_unit.clone(), vec![json])),
        }
    }

    fn update_glean_json(
        predicate: Predicate,
        json: yojson::T,
        factkey_opt: Option<(fact_id::T, (OwnershipUnit, String, Predicate))>,
        fa: &mut T,
    ) {
        match fa.result_json.get_mut(&predicate) {
            Some(facts) => add_to_owned_facts(&fa.ownership_unit, json, facts),
            None => panic!("All predicate keys should be in the map"),
        }
        if let Some((fact_id, key)) = factkey_opt {
            fa.fact_ids.insert(key, fact_id);
        }
    }

    /// [add_fact pred fact t] returns an [id] and a new accumulator [t'].
    /// If a fact already exists in [t] for this [pred], returns [t] unchanged
    /// together with its id. Otherwise, [id] is a new fact id, and a fact
    /// of the form { 'id': id, 'key': fact } is added to the accumulator.
    ///
    /// If [ownership] is set, we distinguish between identical facts with different
    /// owners
    pub fn add_fact(
        predicate: Predicate,
        json_key: yojson::T,
        value: Option<yojson::T>,
        fa: &mut T,
    ) -> fact_id::T {
        // (`Hh_json.to_yojson` of the key and the value: they are built as
        // `Yojson.Safe.t` here, see `glean_schema_gen.py`.)
        let fact_id = fact_id::next();
        if should_cache(predicate) {
            let key = cache_key(fa.ownership, &fa.ownership_unit, &json_key, predicate);
            if let Some(fid) = fa.fact_ids.get(&key) {
                return *fid;
            }
            let json_fact = json_fact(fact_id, json_key, value);
            update_glean_json(predicate, json_fact, Some((fact_id, key)), fa);
        } else {
            let json_fact = json_fact(fact_id, json_key, value);
            update_glean_json(predicate, json_fact, None, fa);
        }
        fact_id
    }

    /// `` `Assoc (("id", id) :: ("key", json_key) :: value) `` of `add_fact`.
    fn json_fact(fact_id: fact_id::T, json_key: yojson::T, value: Option<yojson::T>) -> yojson::T {
        let mut fields = vec![
            ("id".to_string(), fact_id::to_json_number(fact_id)),
            ("key".to_string(), json_key),
        ];
        if let Some(v) = value {
            fields.push(("value".to_string(), v));
        }
        yojson::T::Assoc(fields)
    }

    pub fn init(ownership: bool) -> T {
        let mut result_json = Map::new();
        for k in ORDERED_ALL {
            result_json.insert(k, vec![]);
        }
        T {
            result_json,
            fact_ids: HashMap::new(),
            ownership_unit: None,
            ownership,
            generated_from: None,
            xrefs: None,
        }
    }

    /// set the current ownership unit. All facts added after the unit is set
    /// will be marked with this owner. Initially, ownership_unit is set to None
    /// which corresponds to fact with no owners. If [ownership] is false,
    /// the ownership_unit is ignored.
    pub fn set_ownership_unit(t: &mut T, ou: Option<String>) {
        t.ownership_unit = ou
    }

    /// set the path of the generating source file if any. To be set for each file
    pub fn set_generated_from(t: &mut T, from: Option<String>) {
        t.generated_from = from
    }

    pub fn get_generated_from(t: &T) -> Option<&String> {
        t.generated_from.as_ref()
    }

    /// The facts of one predicate: `owned_facts` is in the OCaml's order
    /// (most recent group first, most recent fact first).
    fn owned_facts_to_json(ownership: bool, predicate: String, owned_facts: &OwnedFacts, out: &mut Vec<yojson::T>) {
        let fact_object = |ou: &OwnershipUnit, facts: Vec<yojson::T>| -> yojson::T {
            let mut obj = vec![
                ("predicate".to_string(), yojson::T::String(predicate.clone())),
                ("facts".to_string(), yojson::T::List(facts)),
            ];
            if let Some(ou) = ou {
                obj.insert(0, ("unit".to_string(), yojson::T::String(ou.clone())));
            }
            yojson::T::Assoc(obj)
        };
        if ownership {
            for (ou, facts) in owned_facts.iter().rev() {
                out.push(fact_object(ou, facts.iter().rev().cloned().collect()))
            }
        } else {
            let facts = owned_facts
                .iter()
                .rev()
                .flat_map(|(_, facts)| facts.iter().rev().cloned())
                .collect();
            out.push(fact_object(&None, facts))
        }
    }

    /// Returns a list of json objects. If [ownership] is false, objects
    /// are of the form {'predicate': PREDICATE, 'facts': FACTS'} and all
    /// predicates are different. If [ownership] is set, objects are of the form
    /// {'unit: UNIT, 'predicate': PREDICATE, 'facts': FACTS}.
    pub fn to_json(fa: &T) -> Vec<yojson::T> {
        let mut out = vec![];
        for pred in ORDERED_ALL {
            owned_facts_to_json(fa.ownership, super::to_string(pred), &fa.result_json[&pred], &mut out)
        }
        out
    }

    pub fn set_pos_map(t: &mut T, xrefs: xrefs::PosMap) {
        t.xrefs = Some(xrefs)
    }

    pub fn get_pos_map(t: &T) -> Option<&xrefs::PosMap> {
        t.xrefs.as_ref()
    }
}
