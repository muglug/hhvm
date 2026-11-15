// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! The `write_symbol_info` library (`typing/write_symbol_info/`, wrapped:
//! `Write_symbol_info.Entrypoint` etc.): the Glean indexer of
//! `hh_server --write-symbol-info` and `hh_single_type_check --glean-index`
//! / `--glean-sym-hash`. `glean` is the `glean_schema` library (the schema's
//! types and their JSON).

pub mod glean;

pub mod add_fact;
pub mod build_fact;
pub mod entrypoint;
pub mod file_info;
pub mod gencode_utils;
pub mod index_batch;
pub mod index_decls;
pub mod index_xrefs;
pub mod indexable;
pub mod indexer_options;
pub mod predicate;
pub mod pretty;
pub mod sym_def;
pub mod sym_hash;
pub mod thrift;
pub mod util;
pub mod xrefs;

/// `test/unit/typing/writeSymbolInfoTest.ml`.
#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::glean::fact_id;
    use super::glean::hack::declaration;
    use super::glean::hack::module_declaration;
    use super::glean::hack::name;
    use super::glean::hack::x_ref;
    use super::glean::hack::x_ref_target;
    use super::predicate::Hack;
    use super::predicate::T as P;
    use super::predicate::fact_acc;
    use crate::yojson::safe as yojson;

    fn extract_facts_exn(pred_name: &str, json_objects: &[yojson::T]) -> Vec<yojson::T> {
        let facts: Vec<&Vec<yojson::T>> = json_objects
            .iter()
            .filter_map(|o| match o {
                yojson::T::Assoc(l) => match l.as_slice() {
                    [(k1, yojson::T::String(p)), (k2, yojson::T::List(l))]
                        if k1 == "predicate" && k2 == "facts" && p == pred_name =>
                    {
                        Some(l)
                    }
                    _ => None,
                },
                _ => None,
            })
            .collect();
        match facts.as_slice() {
            [facts] => facts.to_vec(),
            _ => panic!("There should be exactly one predicate {}", pred_name),
        }
    }

    fn get<'a>(j: &'a yojson::T, path: &[&str]) -> &'a yojson::T {
        path.iter().fold(j, |j, k| super::glean::util::test_json::field(j, k))
    }

    #[test]
    fn test_add_fact() {
        let mut fa = fact_acc::init(false);
        let json_key = yojson::T::Assoc(vec![(
            "name".to_string(),
            yojson::T::Assoc(vec![(
                "key".to_string(),
                yojson::T::Assoc(vec![(
                    "name".to_string(),
                    yojson::T::Assoc(vec![("key".to_string(), yojson::T::String("TestName".to_string()))]),
                )]),
            )]),
        )]);
        let res_id = fact_acc::add_fact(P::Hack(Hack::ClassDeclaration), json_key.clone(), None, &mut fa);
        let facts = extract_facts_exn("hack.ClassDeclaration.6", &fact_acc::to_json(&fa));
        assert_eq!(1, facts.len(), "One class decl fact added to JSON");
        assert_eq!(&yojson::T::Int(res_id), get(&facts[0], &["id"]), "Id returned is JSON id of new fact");
        let res_id2 = fact_acc::add_fact(P::Hack(Hack::ClassDeclaration), json_key.clone(), None, &mut fa);
        let facts = extract_facts_exn("hack.ClassDeclaration.6", &fact_acc::to_json(&fa));
        assert_eq!(res_id, res_id2, "Adding identical facts results in same ids");
        assert_eq!(1, facts.len(), "Only one class decl fact in JSON after identical addition");
        let res_id3 = fact_acc::add_fact(P::Hack(Hack::FunctionDeclaration), json_key, None, &mut fa);
        let facts = extract_facts_exn("hack.FunctionDeclaration.6", &fact_acc::to_json(&fa));
        assert_ne!(res_id, res_id3, "Identical keys for different predicates are separate facts");
        assert_eq!(1, facts.len(), "One function decl fact added to JSON");
    }

    #[test]
    fn test_add_decl_fact() {
        let mut fa = fact_acc::init(false);
        let gconst_name = "TestGConst";
        let id = super::add_fact::gconst_decl(gconst_name, &mut fa);
        let facts = extract_facts_exn("hack.GlobalConstDeclaration.6", &fact_acc::to_json(&fa));
        assert_eq!(1, facts.len(), "One gconst fact added");
        assert_eq!(&yojson::T::Int(id), get(&facts[0], &["id"]), "Id returned is JSON id of new fact");
        assert_eq!(
            &yojson::T::String(gconst_name.to_string()),
            get(&facts[0], &["key", "name", "key", "name", "key"]),
            "Nested fact contains name"
        );
    }

    #[test]
    fn test_build_xrefs() {
        let mut xrefs = super::xrefs::empty();
        let file = Arc::new(crate::relative_path::from_root("test.php"));
        let decl_name = "TestDecl";
        let target = x_ref_target::T::Declaration(declaration::T::Module(module_declaration::T::key(
            module_declaration::Key {
                name: name::T::key(decl_name.to_string()),
            },
        )));
        let target_id = fact_id::next();
        let pos = |start: (usize, usize, usize), end: (usize, usize, usize)| {
            oxidized::pos::Pos::from_lnum_bol_offset(Arc::clone(&file), start, end)
        };
        let ref_pos = pos((2, 5, 10), (2, 5, 15));
        let dup_ref_pos = pos((2, 5, 10), (2, 5, 15));
        let next_ref_pos = pos((3, 25, 40), (3, 25, 45));
        let target = super::xrefs::TargetInfo {
            target,
            receiver_type: None,
            fact_id: target_id,
        };
        super::xrefs::add(&mut xrefs, target_id, next_ref_pos, target.clone());
        super::xrefs::add(&mut xrefs, target_id, ref_pos, target.clone());
        super::xrefs::add(&mut xrefs, target_id, dup_ref_pos, target);
        let result = x_ref::to_json(&super::build_fact::xrefs(&xrefs.fact_map)[0]);
        assert_eq!(
            &yojson::T::String(decl_name.to_string()),
            get(&result, &["target", "declaration", "module", "key", "name", "key"]),
            "TestDecl"
        );
        let ranges = super::glean::util::test_json::list(get(&result, &["ranges"]));
        assert_eq!(2, ranges.len(), "Duplicate references removed");
        assert_eq!(
            &yojson::T::Int(30),
            get(&ranges[1], &["offset"]),
            "Byte offset between references calculated correctly"
        );
    }
}
