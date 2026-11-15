// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `notebook_convert/notebook_convert.ml` and of what its
//! internal modules do in the OSS build. See `hh/PORTING.md`.
//!
//! In the OSS build `Declarations_rewriter.rename_decls` is a stub that
//! returns `""` (`stubs/declarations_rewriter.ml`): `Notebook_convert_rewrite.
//! mangle` and `unmangle` turn any Hack into `""`. So:
//! - `notebook_to_hack` prints `hackfmt ""` = `""` for any notebook that
//!   `Ipynb.ipynb_of_json` accepts (the cells are cut into chunks and turned
//!   into Hack, which the stub then drops: that work, which cannot fail on
//!   accepted input, is not redone here), and the OCaml's error messages
//!   otherwise;
//! - `hack_to_notebook` finds the notebook-level metadata comment, checks the
//!   notebook number, and prints a notebook of one empty Hack cell (the
//!   chunks of `""`: none; `Ipynb.ipynb_of_chunks` adds the empty cell).
//! The errors are printed as `Exn.to_string` prints them (checked on the
//! oracle): `("<Printexc.to_string>")` for `Yojson.Safe.Util.Type_error`,
//! `(Not_found_s "List.Assoc.find_exn: not found")` for a missing field.

use crate::exit_status;
use crate::yojson::safe as yojson;
use crate::yojson::safe::T as J;

/// `Exn.to_string` of `Yojson.Safe.Util.Type_error (msg, _)`
fn type_error(expected: &str, j: &J) -> String {
    let msg = format!("Expected {}, got {}", expected, crate::yojson::safe::util::typeof_(j));
    format!("({:?})", format!("Yojson.Safe.Util.Type_error({:?}, _)", msg))
}

/// `Exn.to_string` of `List.Assoc.find_exn`'s `Not_found_s`
fn not_found() -> String {
    "(Not_found_s \"List.Assoc.find_exn: not found\")".to_string()
}

fn to_assoc(j: &J) -> Result<&[(String, J)], String> {
    match j {
        J::Assoc(l) => Ok(l),
        j => Err(type_error("object", j)),
    }
}

fn to_list(j: &J) -> Result<&[J], String> {
    match j {
        J::List(l) => Ok(l),
        j => Err(type_error("array", j)),
    }
}

fn find_exn<'j>(obj: &'j [(String, J)], key: &str) -> Result<&'j J, String> {
    obj.iter().find(|(k, _)| k == key).map(|(_, v)| v).ok_or_else(not_found)
}

const NOTEBOOK_NUMBER_PAT: &str = "N[0-9]+";

/// `Notebook_convert_rewrite.create_notebook_number raw` (`Str.string_match`:
/// a prefix match)
fn create_notebook_number(raw: &str) -> Result<String, String> {
    let digits = raw.strip_prefix('N').map(|r| r.bytes().take_while(u8::is_ascii_digit).count());
    match digits {
        Some(n) if n > 0 => Ok(raw.to_string()),
        _ => Err(format!(
            "Invalid notebook number: {}. Expected the notebook number to match regexp /^{}$/",
            raw, NOTEBOOK_NUMBER_PAT
        )),
    }
}

/// `Ipynb.ipynb_of_json`, keeping only whether it succeeds.
fn ipynb_of_json(ipynb_json: &J) -> Result<(), String> {
    let cell_of_json_exn = |cell_json: &J| -> Result<(), String> {
        let obj = to_assoc(cell_json)?;
        let _type_json = find_exn(obj, "cell_type")?;
        let source_json = find_exn(obj, "source")?;
        for l in to_list(source_json)? {
            match l {
                J::String(_) => {}
                j => return Err(type_error("string", j)),
            }
        }
        Ok(())
    };
    let obj = to_assoc(ipynb_json)?;
    let cells_json = find_exn(obj, "cells")?;
    let metadata = to_assoc(find_exn(obj, "metadata")?)?;
    let _kernelspec = find_exn(metadata, "kernelspec")?;
    for c in to_list(cells_json)? {
        cell_of_json_exn(c)?
    }
    Ok(())
}

/// `Notebook_to_hack.notebook_to_hack ~notebook_number ~header ipynb_json`
fn notebook_to_hack_json(raw_notebook_number: &str, _header: &str, ipynb_json: &J) -> Result<String, String> {
    create_notebook_number(raw_notebook_number)?;
    ipynb_of_json(ipynb_json)?;
    // `hack_of_ipynb_exn`: `... |> Notebook_convert_rewrite.mangle |>
    // Notebook_convert_util.hackfmt`, i.e. `hackfmt ""` with the OSS stub.
    Ok(String::new())
}

/// Given a notebook (`source`, read from stdin) in .ipnyb (JSON) format, a
/// notebook number (such as N12345) and a header (such as a comment with
/// copyright information), print the result of converting to standard Hack
/// or (on bad input) return Exit_status.Input_error and print errors to
/// stderr. This conversion mainly involves:
/// - validation
/// - concatenating code cells (preserving cell information)
/// - placing the `header` between the <?hh and cell contents
/// - Markdown cells converted to comments
/// - Moving top-level statements into a function body.
pub fn notebook_to_hack(notebook_number: &str, header: &str, source: &str) -> exit_status::T {
    // workaround for hh_json not dealing with unicode characters encoded as \u....
    let hack = match yojson::from_string(source) {
        Err(e) => Err(e.0),
        Ok(ipynb_yojson) => notebook_to_hack_json(notebook_number, header, &ipynb_yojson),
    };
    match hack {
        Ok(hack) => {
            print!("{}", hack);
            exit_status::T::NoError
        }
        Err(err) => {
            eprint!(
                " Received input that was not in the expected .ipynb format
(https://github.com/jupyter/nbformat/blob/main/nbformat/v4/nbformat.v4.schema.json)
Error:
{}\"
",
                err
            );
            exit_status::T::InputError
        }
    }
}

/// `Notebook_level_metadata.of_comment line`: `(notebook_number, kernelspec)`
fn metadata_of_comment(line: &str) -> Option<(String, J)> {
    // `Str.regexp {|^ *//@bento-notebook:\(.*\)$|}` with `string_match line 0`
    let rest = line.trim_start_matches(' ').strip_prefix("//@bento-notebook:")?;
    // (`.*` stops at a newline; `$` matches before one.)
    let json_string = rest.split('\n').next().unwrap_or("");
    let obj = match yojson::from_string(json_string) {
        Ok(J::Assoc(obj)) => obj,
        _ => return None,
    };
    let notebook_number = match obj.iter().find(|(k, _)| k == "notebook_number").map(|(_, v)| v)? {
        J::String(name) => name.clone(),
        _ => return None,
    };
    let kernelspec = obj.iter().find(|(k, _)| k == "kernelspec").map(|(_, v)| v.clone())?;
    Some((notebook_number, kernelspec))
}

/// `Hack_to_notebook.hack_to_notebook hack`
fn hack_to_notebook_json(hack: &str) -> Result<J, String> {
    let (raw_notebook_number, kernelspec) = crate::rt::ocaml_string::split_lines(hack)
        .into_iter()
        .take(50)
        .find_map(|l| metadata_of_comment(&l))
        .ok_or_else(|| {
            r#"Could not find notebook-level metadata. Expected a valid comment like: //@bento-notebook:{"notebook_number": "notebook_number", kernelspec: $THE_KERNEL_SPEC_SEE_IPYNB_SPEC}"#
                .to_string()
        })?;
    create_notebook_number(&raw_notebook_number)?;
    // `unmangle` gives `""` (OSS stub): no chunks; `Ipynb.ipynb_of_chunks`
    // makes the one empty Hack cell; `ipynb_to_json`.
    let nb_format = J::Int(4);
    Ok(J::Assoc(vec![
        (
            "cells".to_string(),
            J::List(vec![J::Assoc(vec![
                ("cell_type".to_string(), J::String("code".to_string())),
                ("source".to_string(), J::List(vec![])),
                ("outputs".to_string(), J::List(vec![])),
                ("execution_count".to_string(), J::Null),
                ("metadata".to_string(), J::Assoc(vec![])),
            ])]),
        ),
        (
            "metadata".to_string(),
            J::Assoc(vec![
                ("kernelspec".to_string(), kernelspec),
                ("orig_nbformat".to_string(), nb_format.clone()),
            ]),
        ),
        ("nbformat".to_string(), nb_format),
    ]))
}

/// Convert a Hack (.php) file (`hack`, read from stdin) back to a notebook.
///
/// Note: We're careful to distinguish user errors from internal errors
/// because .php files may be edited in userland.
/// (unlike .ipynb JSON, which is typically not human-edited)
pub fn hack_to_notebook(hack: &str) -> exit_status::T {
    match hack_to_notebook_json(hack) {
        Ok(ipynb_json) => {
            // (`validate_hack_to_notebook_exn ipynb_json`: converting that
            // notebook back succeeds.)
            println!("{}", crate::yojson::safe::pretty_to_string(&ipynb_json));
            exit_status::T::NoError
        }
        Err(msg) => {
            eprint!(
                " Received input that was not in the expected format.
Expected a valid Hack file with special comments for notebook cell information.
Such files should only be created via `hh --notebook-to-hack`. Error:
{}
",
                msg
            );
            exit_status::T::InputError
        }
    }
}
