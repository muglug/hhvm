// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `analyze/list/list_logger_types/analyze_list_logger_types.ml`
//! (the part the typechecker needs: the types and their conversion to JSON,
//! which `Analyze_list_logger` logs). See `hh/PORTING.md`.
//!
//! Not ported: the conversions from JSON (`bucket_of_yojson`,
//! `lvalue_kind_of_yojson`, `receiver_kind_of_yojson`, the derived
//! `*_of_yojson` of the records, `of_json_string`) and the derived `show` /
//! `pp`, which only the offline analysis (`analyze/list/`) uses.
//!
//! The JSON is what `[@@deriving yojson]` gives: the fields of a record in the
//! order they are declared, a `[@yojson.option]` field left out when it is
//! `None`, and `complex_lvalue_elements` (`[@yojson_drop_if List.is_empty]`)
//! left out when it is empty.

use crate::yojson::safe as yojson;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Bucket {
    Tuple,
    Vec,
    Pair,
    Union,
    Intersection,
    Dynamic,
    Generic,
    Misc,
}

pub fn yojson_of_bucket(b: Bucket) -> yojson::T {
    yojson::T::String(
        match b {
            Bucket::Tuple => "Tuple",
            Bucket::Vec => "Vec",
            Bucket::Pair => "Pair",
            Bucket::Union => "Union",
            Bucket::Intersection => "Intersection",
            Bucket::Dynamic => "Dynamic",
            Bucket::Generic => "Generic",
            Bucket::Misc => "Misc",
        }
        .to_string(),
    )
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LvalueKind {
    ArrayAppend,
    ArrayGet,
    ObjGet,
    ClassGet,
    Call,
    ReadonlyExpr,
    Other,
}

pub fn yojson_of_lvalue_kind(k: LvalueKind) -> yojson::T {
    yojson::T::String(
        match k {
            LvalueKind::ArrayAppend => "Array_append",
            LvalueKind::ArrayGet => "Array_get",
            LvalueKind::ObjGet => "Obj_get",
            LvalueKind::ClassGet => "Class_get",
            LvalueKind::Call => "Call",
            LvalueKind::ReadonlyExpr => "ReadonlyExpr",
            LvalueKind::Other => "Other",
        }
        .to_string(),
    )
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReceiverKind {
    Self_,
    Static,
    Parent,
    Explicit,
    Expr,
}

pub fn yojson_of_receiver_kind(k: ReceiverKind) -> yojson::T {
    yojson::T::String(
        match k {
            ReceiverKind::Self_ => "Self",
            ReceiverKind::Static => "Static",
            ReceiverKind::Parent => "Parent",
            ReceiverKind::Explicit => "Explicit",
            ReceiverKind::Expr => "Expr",
        }
        .to_string(),
    )
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PosInfo {
    pub filename: String,
    pub line: isize,
    pub char_start: isize,
    pub char_end: isize,
}

/// `yojson_of_pos_info` (`[@@deriving yojson]`)
pub fn yojson_of_pos_info(p: &PosInfo) -> yojson::T {
    yojson::T::Assoc(vec![
        (
            "filename".to_string(),
            yojson::T::String(p.filename.clone()),
        ),
        ("line".to_string(), yojson::T::Int(p.line)),
        ("char_start".to_string(), yojson::T::Int(p.char_start)),
        ("char_end".to_string(), yojson::T::Int(p.char_end)),
    ])
}

/// `complex_lvalue_element`; the fields are `lvalue_kind`, `lvalue_pos`, ...
/// without their common prefix.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComplexLvalueElement {
    pub kind: LvalueKind,
    pub pos: PosInfo,
    pub code: String,
    pub involves_call: bool,
    pub receiver_kind: Option<ReceiverKind>,
}

/// `yojson_of_complex_lvalue_element` (`[@@deriving yojson]`)
pub fn yojson_of_complex_lvalue_element(e: &ComplexLvalueElement) -> yojson::T {
    let mut bnds = vec![
        ("lvalue_kind".to_string(), yojson_of_lvalue_kind(e.kind)),
        ("lvalue_pos".to_string(), yojson_of_pos_info(&e.pos)),
        ("lvalue_code".to_string(), yojson::T::String(e.code.clone())),
        (
            "lvalue_involves_call".to_string(),
            yojson::T::Bool(e.involves_call),
        ),
    ];
    // `[@yojson.option]`
    if let Some(k) = e.receiver_kind {
        bnds.push((
            "lvalue_receiver_kind".to_string(),
            yojson_of_receiver_kind(k),
        ));
    }
    yojson::T::Assoc(bnds)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct T {
    pub bucket: Bucket,
    pub type_string: String,
    pub has_complex_lvalue: bool,
    pub pos: PosInfo,
    pub lhs_code: String,
    pub total_lvalue_count: isize,
    pub is_generated: bool,
    pub ty_node_kind: Option<String>,
    pub complex_lvalue_elements: Vec<ComplexLvalueElement>,
}

/// `yojson_of_t` (`[@@deriving yojson]`)
pub fn yojson_of_t(t: &T) -> yojson::T {
    let mut bnds = vec![
        ("bucket".to_string(), yojson_of_bucket(t.bucket)),
        (
            "type_string".to_string(),
            yojson::T::String(t.type_string.clone()),
        ),
        (
            "has_complex_lvalue".to_string(),
            yojson::T::Bool(t.has_complex_lvalue),
        ),
        ("pos".to_string(), yojson_of_pos_info(&t.pos)),
        (
            "lhs_code".to_string(),
            yojson::T::String(t.lhs_code.clone()),
        ),
        (
            "total_lvalue_count".to_string(),
            yojson::T::Int(t.total_lvalue_count),
        ),
        ("is_generated".to_string(), yojson::T::Bool(t.is_generated)),
    ];
    // `[@yojson.option]`
    if let Some(k) = &t.ty_node_kind {
        bnds.push(("ty_node_kind".to_string(), yojson::T::String(k.clone())));
    }
    // `[@default []] [@yojson_drop_if List.is_empty]`
    if !t.complex_lvalue_elements.is_empty() {
        bnds.push((
            "complex_lvalue_elements".to_string(),
            yojson::T::List(
                t.complex_lvalue_elements
                    .iter()
                    .map(yojson_of_complex_lvalue_element)
                    .collect(),
            ),
        ));
    }
    yojson::T::Assoc(bnds)
}

pub fn to_json_string(entry: &T) -> String {
    yojson::to_string(&yojson_of_t(entry))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pos_info() -> PosInfo {
        PosInfo {
            filename: "a.php".to_string(),
            line: 3,
            char_start: 1,
            char_end: 9,
        }
    }

    #[test]
    fn optional_fields_are_left_out() {
        let entry = T {
            bucket: Bucket::Tuple,
            type_string: "(int, string)".to_string(),
            has_complex_lvalue: false,
            pos: pos_info(),
            lhs_code: "list($a, $b)".to_string(),
            total_lvalue_count: 2,
            is_generated: false,
            ty_node_kind: None,
            complex_lvalue_elements: vec![],
        };
        assert_eq!(
            to_json_string(&entry),
            r#"{"bucket":"Tuple","type_string":"(int, string)","has_complex_lvalue":false,"pos":{"filename":"a.php","line":3,"char_start":1,"char_end":9},"lhs_code":"list($a, $b)","total_lvalue_count":2,"is_generated":false}"#
        );
    }

    #[test]
    fn optional_fields_are_written() {
        let entry = T {
            bucket: Bucket::Misc,
            type_string: "mixed".to_string(),
            has_complex_lvalue: true,
            pos: pos_info(),
            lhs_code: "list($a[], $b)".to_string(),
            total_lvalue_count: 2,
            is_generated: true,
            ty_node_kind: Some("Toption".to_string()),
            complex_lvalue_elements: vec![ComplexLvalueElement {
                kind: LvalueKind::ArrayAppend,
                pos: pos_info(),
                code: "$a[]".to_string(),
                involves_call: false,
                receiver_kind: Some(ReceiverKind::Self_),
            }],
        };
        assert_eq!(
            to_json_string(&entry),
            r#"{"bucket":"Misc","type_string":"mixed","has_complex_lvalue":true,"pos":{"filename":"a.php","line":3,"char_start":1,"char_end":9},"lhs_code":"list($a[], $b)","total_lvalue_count":2,"is_generated":true,"ty_node_kind":"Toption","complex_lvalue_elements":[{"lvalue_kind":"Array_append","lvalue_pos":{"filename":"a.php","line":3,"char_start":1,"char_end":9},"lvalue_code":"$a[]","lvalue_involves_call":false,"lvalue_receiver_kind":"Self"}]}"#
        );
    }
}
