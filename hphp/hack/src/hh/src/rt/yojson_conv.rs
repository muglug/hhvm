// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of what the code that `ppx_yojson_conv` derives
//! (`[@@deriving yojson_of]`, `[@@deriving of_yojson]`) calls in
//! `Ppx_yojson_conv_lib`: the converters of the primitive types and the errors
//! of record conversion. The derived functions themselves are written out where
//! the OCaml derives them.
//!
//! A conversion error is `Ppx_yojson_conv_lib.Yojson_conv.Of_yojson_error`,
//! which is caught far from where it is raised: the converters return
//! `Result<_, OfYojsonError>` (PORTING.md, "Exceptions"), and the functions
//! between them and the handler pass it on with `?`.

use crate::yojson::safe as yojson;

/// `Ppx_yojson_conv_lib.Yojson_conv.Of_yojson_error of exn * Yojson.Safe.t`,
/// where the exception is always `Failure` of the message.
#[derive(Clone, PartialEq)]
pub struct OfYojsonError(pub String, pub yojson::T);

impl std::fmt::Debug for OfYojsonError {
    /// `Printexc.to_string`: neither argument is a string or an int, so
    /// both are printed as `_`.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Ppx_yojson_conv_lib__Yojson_conv.Of_yojson_error(_, _)")
    }
}

/// `of_yojson_error what yojson`: the error to return.
pub fn of_yojson_error<A>(what: &str, yojson: &yojson::T) -> Result<A, OfYojsonError> {
    Err(OfYojsonError(what.to_string(), yojson.clone()))
}

pub fn yojson_of_int(n: isize) -> yojson::T {
    yojson::T::Int(n)
}

pub fn yojson_of_string(s: &str) -> yojson::T {
    yojson::T::String(s.to_string())
}

pub fn yojson_of_option<A>(f: impl FnOnce(&A) -> yojson::T, x: &Option<A>) -> yojson::T {
    match x {
        None => yojson::T::Null,
        Some(x) => f(x),
    }
}

pub fn int_of_yojson(yojson: &yojson::T) -> Result<isize, OfYojsonError> {
    match yojson {
        yojson::T::Int(v) => Ok(*v),
        _ => of_yojson_error("int_of_yojson: integer needed", yojson),
    }
}

pub fn string_of_yojson(yojson: &yojson::T) -> Result<String, OfYojsonError> {
    match yojson {
        yojson::T::String(s) => Ok(s.clone()),
        _ => of_yojson_error("string_of_yojson: string needed", yojson),
    }
}

// ~~ Yojson_conv_error ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// The value given to a record conversion is not an object.
pub fn record_list_instead_atom(loc: &str, yojson: &yojson::T) -> Result<(), OfYojsonError> {
    of_yojson_error(
        &format!("{}_of_yojson: list instead of atom for record expected", loc),
        yojson,
    )
}

/// `fld_names` in the order of the OCaml list: the last one found first.
pub fn record_duplicate_fields(loc: &str, fld_names: &[String], yojson: &yojson::T) -> Result<(), OfYojsonError> {
    let fld_names_str = fld_names.iter().rev().cloned().collect::<Vec<_>>().join(" ");
    of_yojson_error(
        &format!("{}_of_yojson: duplicate fields: {}", loc, fld_names_str),
        yojson,
    )
}

/// `fld_names` in the order of the OCaml list: the last one found first.
pub fn record_extra_fields(loc: &str, fld_names: &[String], yojson: &yojson::T) -> Result<(), OfYojsonError> {
    let fld_names_str = fld_names.iter().rev().cloned().collect::<Vec<_>>().join(" ");
    of_yojson_error(
        &format!("{}_of_yojson: extra fields: {}", loc, fld_names_str),
        yojson,
    )
}

/// `lst`: for each field of the record, in order, whether it is undefined.
pub fn record_undefined_elements(
    loc: &str,
    yojson: &yojson::T,
    lst: &[(bool, &str)],
) -> Result<(), OfYojsonError> {
    let undefined: Vec<&str> = lst
        .iter()
        .filter(|(is_undefined, _)| *is_undefined)
        .map(|(_, field)| *field)
        .collect();
    of_yojson_error(
        &format!(
            "{}_of_yojson: the following record elements were undefined: {}",
            loc,
            undefined.join(" ")
        ),
        yojson,
    )
}

/// The conversion that `[@@deriving of_yojson]` gives a record: each field
/// of the object is converted, in order, by the converter of the field of
/// the record with its name (`fields`, in the order of the record), which
/// keeps the value; then duplicate fields, extra fields and missing fields
/// are errors, in this order. When this returns, every converter has been
/// called once.
pub fn record_of_yojson(
    loc: &str,
    yojson: &yojson::T,
    fields: &mut [(&str, &mut dyn FnMut(&yojson::T) -> Result<(), OfYojsonError>)],
) -> Result<(), OfYojsonError> {
    match yojson {
        yojson::T::Assoc(field_yojsons) => {
            let mut seen: Vec<bool> = fields.iter().map(|_| false).collect();
            let mut duplicates: Vec<String> = vec![];
            let mut extra: Vec<String> = vec![];
            for (field_name, field_yojson) in field_yojsons {
                match fields.iter().position(|(name, _)| name == field_name) {
                    Some(i) => {
                        if !seen[i] {
                            (fields[i].1)(field_yojson)?;
                            seen[i] = true
                        } else {
                            duplicates.insert(0, field_name.clone())
                        }
                    }
                    // `record_check_extra_fields` is true.
                    None => extra.insert(0, field_name.clone()),
                }
            }
            if !duplicates.is_empty() {
                record_duplicate_fields(loc, &duplicates, yojson)
            } else if !extra.is_empty() {
                record_extra_fields(loc, &extra, yojson)
            } else if !seen.iter().all(|b| *b) {
                let lst: Vec<(bool, &str)> = fields
                    .iter()
                    .zip(seen.iter())
                    .map(|((name, _), seen)| (!*seen, *name))
                    .collect();
                record_undefined_elements(loc, yojson, &lst)
            } else {
                Ok(())
            }
        }
        _ => record_list_instead_atom(loc, yojson),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn error_of<A>(r: Result<A, OfYojsonError>) -> String {
        match r {
            Ok(_) => panic!("an Of_yojson_error"),
            Err(e) => e.0,
        }
    }

    fn assoc(fields: &[(&str, yojson::T)]) -> yojson::T {
        yojson::T::Assoc(
            fields
                .iter()
                .map(|(k, v)| (k.to_string(), v.clone()))
                .collect(),
        )
    }

    fn pair(json: &yojson::T) -> Result<(isize, isize), OfYojsonError> {
        let mut a = None;
        let mut b = None;
        record_of_yojson(
            "f.ml.t",
            json,
            &mut [
                ("a", &mut |j| {
                    a = Some(int_of_yojson(j)?);
                    Ok(())
                }),
                ("b", &mut |j| {
                    b = Some(int_of_yojson(j)?);
                    Ok(())
                }),
            ],
        )?;
        Ok((a.unwrap(), b.unwrap()))
    }

    #[test]
    fn records() {
        let i = yojson::T::Int;
        assert_eq!(pair(&assoc(&[("b", i(2)), ("a", i(1))])), Ok((1, 2)));
        assert_eq!(
            error_of(pair(&assoc(&[("a", i(1)), ("a", i(2)), ("b", i(3)), ("c", i(4))]))),
            "f.ml.t_of_yojson: duplicate fields: a"
        );
        assert_eq!(
            error_of(pair(&assoc(&[("a", i(1)), ("c", i(2)), ("b", i(3)), ("d", i(4))]))),
            "f.ml.t_of_yojson: extra fields: c d"
        );
        assert_eq!(
            error_of(pair(&assoc(&[]))),
            "f.ml.t_of_yojson: the following record elements were undefined: a b"
        );
        assert_eq!(
            error_of(pair(&assoc(&[("a", yojson::T::Null)]))),
            "int_of_yojson: integer needed"
        );
        assert_eq!(
            error_of(pair(&yojson::T::Null)),
            "f.ml.t_of_yojson: list instead of atom for record expected"
        );
        assert_eq!(
            yojson_of_option(|s: &String| yojson_of_string(s), &None),
            yojson::T::Null
        );
    }
}
