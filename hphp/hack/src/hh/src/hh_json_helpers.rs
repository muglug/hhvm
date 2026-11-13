// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Hh_json_helpers` (`utils/hh_json/hh_json_helpers.ml`). See
//! `hh/PORTING.md`.
//!
//! Only what the port uses so far: the `Yojson.Safe.t` accessors and the
//! monadic `Access` API that `Typing_json.to_locl_ty` reads JSON with, and
//! `Jget` and `Jprint`, which `Lsp_fmt` reads and writes LSP messages with.
//! Not here: `get_number_exn`,
//! `get_number_int_exn`, `Access.return`, `Access.counit_with`,
//! `Access.to_option`, `Access.get_number`, `Access.get_number_int`,
//! `json_truncate_string`, `get_field`, `get_field_opt`. `AdhocJsonHelpers`
//! (in part) and `json_truncate` were added for the file watchers.
//!
//! The `_exn` accessors `assert false` on a value of the wrong kind, and the
//! accessors of `Access` catch that `Assert_failure`: here they return
//! `Err(AssertFailure)`, which `Access` turns into its errors.

use crate::yojson::safe as yojson;

/// `Assert_failure`, raised by the `_exn` accessors on a value of the wrong
/// kind.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AssertFailure;

pub fn get_object_exn(v: &yojson::T) -> Result<&Vec<(String, yojson::T)>, AssertFailure> {
    match v {
        yojson::T::Assoc(o) => Ok(o),
        _ => Err(AssertFailure),
    }
}

pub fn get_array_exn(v: &yojson::T) -> Result<&Vec<yojson::T>, AssertFailure> {
    match v {
        yojson::T::List(a) => Ok(a),
        _ => Err(AssertFailure),
    }
}

pub fn get_string_exn(v: &yojson::T) -> Result<&String, AssertFailure> {
    match v {
        yojson::T::String(s) => Ok(s),
        _ => Err(AssertFailure),
    }
}

pub fn get_bool_exn(v: &yojson::T) -> Result<bool, AssertFailure> {
    match v {
        yojson::T::Bool(b) => Ok(*b),
        _ => Err(AssertFailure),
    }
}

// ~~ Monadic API for traversing a JSON object ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum JsonType {
    ObjectT,
    ArrayT,
    StringT,
    NumberT,
    IntegerT,
    BoolT,
}

fn json_type_to_string(t: JsonType) -> &'static str {
    match t {
        JsonType::ObjectT => "Object",
        JsonType::ArrayT => "Array",
        JsonType::StringT => "String",
        JsonType::NumberT => "Number",
        JsonType::IntegerT => "Integer",
        JsonType::BoolT => "Bool",
    }
}

/// `module Access`
pub mod access {
    use super::AssertFailure;
    use super::JsonType;
    use super::json_type_to_string;
    use super::yojson;

    /// `string list`, in the order of the OCaml list: the head (the last key
    /// that was accessed) first.
    pub type Keytrace = Vec<String>;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum AccessFailure {
        NotAnObject(Keytrace),
        MissingKeyError(String, Keytrace),
        WrongTypeError(Keytrace, JsonType),
    }

    /// `'a m`
    pub type M<A> = Result<(A, Keytrace), AccessFailure>;

    pub fn keytrace_to_string(x: &[String]) -> String {
        if x.is_empty() {
            "".to_string()
        } else {
            let res = x
                .iter()
                .rev()
                .map(|s| s.as_str())
                .collect::<Vec<&str>>()
                .join(".");
            " (at field `".to_string() + &res + "`)"
        }
    }

    pub fn access_failure_to_string(failure: &AccessFailure) -> String {
        match failure {
            AccessFailure::NotAnObject(x) => {
                format!("Value is not an object {}", keytrace_to_string(x))
            }
            AccessFailure::MissingKeyError(x, y) => {
                format!("Missing key: {}{}", x, keytrace_to_string(y))
            }
            AccessFailure::WrongTypeError(x, y) => format!(
                "Value expected to be {}{}",
                json_type_to_string(*y),
                keytrace_to_string(x)
            ),
        }
    }

    /// `(>>=)`
    pub fn bind<A, B>(m: M<A>, f: impl FnOnce((A, Keytrace)) -> M<B>) -> M<B> {
        match m {
            Err(x) => Err(x),
            Ok(x) => f(x),
        }
    }

    /// The `Failure "int_of_string"` that OCaml also catches here can only
    /// come from `get_number_int_exn`, which is not ported.
    fn catch_type_error<A>(
        exp: JsonType,
        f: impl FnOnce(&yojson::T) -> Result<A, AssertFailure>,
        (v, keytrace): (yojson::T, Keytrace),
    ) -> M<A> {
        match f(&v) {
            Ok(x) => Ok((x, keytrace)),
            Err(AssertFailure) => Err(AccessFailure::WrongTypeError(keytrace, exp)),
        }
    }

    pub fn get_val(k: &str, (v, keytrace): (&yojson::T, &Keytrace)) -> M<yojson::T> {
        match super::get_object_exn(v) {
            Err(AssertFailure) => Err(AccessFailure::NotAnObject(keytrace.clone())),
            Ok(obj) => {
                // The first binding of `k`.
                let mut candidate = None;
                for (key, json) in obj {
                    if candidate.is_some() {
                    } else if key == k {
                        candidate = Some(json)
                    }
                }
                match candidate {
                    None => Err(AccessFailure::MissingKeyError(
                        k.to_string(),
                        keytrace.clone(),
                    )),
                    Some(obj) => {
                        let mut keytrace_ = Vec::with_capacity(keytrace.len() + 1);
                        keytrace_.push(k.to_string());
                        keytrace_.extend(keytrace.iter().cloned());
                        Ok((obj.clone(), keytrace_))
                    }
                }
            }
        }
    }

    fn make_object_json(v: &yojson::T) -> Result<yojson::T, AssertFailure> {
        Ok(yojson::T::Assoc(super::get_object_exn(v)?.clone()))
    }

    pub fn get_obj(k: &str, v_keytrace: (&yojson::T, &Keytrace)) -> M<yojson::T> {
        bind(get_val(k, v_keytrace), |x| {
            catch_type_error(JsonType::ObjectT, make_object_json, x)
        })
    }

    pub fn get_bool(k: &str, v_keytrace: (&yojson::T, &Keytrace)) -> M<bool> {
        bind(get_val(k, v_keytrace), |x| {
            catch_type_error(JsonType::BoolT, super::get_bool_exn, x)
        })
    }

    pub fn get_string(k: &str, v_keytrace: (&yojson::T, &Keytrace)) -> M<String> {
        bind(get_val(k, v_keytrace), |x| {
            catch_type_error(
                JsonType::StringT,
                |v| super::get_string_exn(v).cloned(),
                x,
            )
        })
    }

    pub fn get_array(k: &str, v_keytrace: (&yojson::T, &Keytrace)) -> M<Vec<yojson::T>> {
        bind(get_val(k, v_keytrace), |x| {
            catch_type_error(JsonType::ArrayT, |v| super::get_array_exn(v).cloned(), x)
        })
    }
}

// ~~ Helpers for parsing & printing ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// `module Jget`
///
/// Helpers for the various "option" monads in use for Json, to succinctly
/// capture the spirit of JSON (tolerance for missing values) and the spirit
/// of LSP (loads of nested optional members with obvious defaults)
/// and the usefuless of error-checking (in case a required field is absent)...
/// - We use "json option" throughout. Things which you might expect to return
///   a json are instead lifted to return a json option, so you can use all the
///   accessors on them more easily. When you attempt to get string "o.m", either
///   it's present both because "o" is Some, and because "m" is a string member
///   Or it's absent because any of those three things is false...
/// - The "_opt" accessors uniformally return Some (present) or None (absent),
///   regardless of which of the two things caused absence.
/// - The "_d" accessors uniformally return a value (present) or default.
/// - The "_exn" accessors uniformally return a value (present) or throw.
///
/// The effect of this is you lose precise information about what exactly
/// caused an absence (which is usually only of marginal benefit), and in
/// return you gain a consistent way to handle both optionals and requireds.
///
/// Note one exception to the above: if you wish to get an int/float, and it's
/// present as a number but not parseable as an int/float, then all
/// accessors will throw.
///
/// A `json option` is an `Option<&yojson::T>`; the accessors that give one
/// back borrow it from their argument.
///
/// `exception Parse of string` is the `Err` of the accessors that raise it
/// (PORTING.md, "Exceptions"): it is caught far from where it is raised
/// (`Lsp_extra_commands`, and the catch-all handlers of `Client_lsp`), and
/// the functions in between pass it on with `?`.
pub mod jget {
    use super::yojson;

    /// `exception Parse of string`
    #[derive(Clone, PartialEq, Eq)]
    pub struct Parse(pub String);

    impl std::fmt::Debug for Parse {
        /// `Printexc.to_string`
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(
                f,
                "Hh_json_helpers.Jget.Parse({})",
                ocaml_string_literal(&self.0)
            )
        }
    }

    /// `%S`: the string as an OCaml string literal (`String.escaped`).
    fn ocaml_string_literal(s: &str) -> String {
        let mut res = String::with_capacity(s.len() + 2);
        res.push('"');
        for c in s.bytes() {
            match c {
                b'"' => res.push_str("\\\""),
                b'\\' => res.push_str("\\\\"),
                b'\n' => res.push_str("\\n"),
                b'\t' => res.push_str("\\t"),
                b'\r' => res.push_str("\\r"),
                0x08 => res.push_str("\\b"),
                b' '..=b'~' => res.push(c as char),
                _ => res.push_str(&format!("\\{:03}", c)),
            }
        }
        res.push('"');
        res
    }

    fn raise_parse<A>(s: String) -> Result<A, Parse> {
        Err(Parse(s))
    }

    /// `Base.Int.of_string`: an OCaml integer literal (a sign, `0x`, `0o`,
    /// `0b` or `0u`, digits and `_`), within the range of an OCaml `int`.
    fn int_of_string_opt(s: &str) -> Option<isize> {
        const MAX: i128 = (1 << 62) - 1;
        let (negative, s) = match s.strip_prefix('-') {
            Some(s) => (true, s),
            None => (false, s.strip_prefix('+').unwrap_or(s)),
        };
        let (radix, digits, decimal) = if let Some(d) =
            s.strip_prefix("0x").or_else(|| s.strip_prefix("0X"))
        {
            (16, d, false)
        } else if let Some(d) = s.strip_prefix("0o").or_else(|| s.strip_prefix("0O")) {
            (8, d, false)
        } else if let Some(d) = s.strip_prefix("0b").or_else(|| s.strip_prefix("0B")) {
            (2, d, false)
        } else if let Some(d) = s.strip_prefix("0u").or_else(|| s.strip_prefix("0U")) {
            (10, d, false)
        } else {
            (10, s, true)
        };
        if !digits.chars().next()?.is_digit(radix) {
            return None;
        }
        let mut n: i128 = 0;
        for c in digits.chars() {
            if c == '_' {
                continue;
            }
            n = n * radix as i128 + c.to_digit(radix)? as i128;
            if n > 2 * MAX + 1 {
                return None;
            }
        }
        let n = if decimal {
            if n > MAX + (negative as i128) {
                return None;
            }
            n
        } else if n > MAX {
            // The 63 bits of an unsigned literal wrap around.
            n - 2 * (MAX + 1)
        } else {
            n
        };
        Some((if negative { -n } else { n }) as isize)
    }

    /// `Base.Float.of_string`: OCaml's float literals, which `str::parse`
    /// reads but for the `_` separators.
    fn float_of_string_opt(s: &str) -> Option<f64> {
        let s: String = s.chars().filter(|c| *c != '_').collect();
        s.parse::<f64>().ok()
    }

    pub fn member<'a>(key: &str, json: &'a yojson::T) -> Option<&'a yojson::T> {
        match json {
            // `List.Assoc.find`: the first binding of the key.
            yojson::T::Assoc(obj) => obj.iter().find(|(k, _)| k == key).map(|(_, v)| v),
            _ => None,
        }
    }

    // Accessors which return None on absence

    pub fn string_opt(json: Option<&yojson::T>, key: &str) -> Option<String> {
        match json {
            None => None,
            Some(json) => match member(key, json) {
                Some(yojson::T::String(s)) => Some(s.clone()),
                _ => None,
            },
        }
    }

    pub fn bool_opt(json: Option<&yojson::T>, key: &str) -> Option<bool> {
        match json {
            None => None,
            Some(json) => match member(key, json) {
                Some(yojson::T::Bool(b)) => Some(*b),
                _ => None,
            },
        }
    }

    pub fn obj_opt<'a>(json: Option<&'a yojson::T>, key: &str) -> Option<&'a yojson::T> {
        match json {
            None => None,
            Some(json) => match member(key, json) {
                Some(obj @ yojson::T::Assoc(_)) => Some(obj),
                _ => None,
            },
        }
    }

    pub fn val_opt<'a>(json: Option<&'a yojson::T>, key: &str) -> Option<&'a yojson::T> {
        match json {
            None => None,
            Some(json) => member(key, json),
        }
    }

    pub fn int_opt(json: Option<&yojson::T>, key: &str) -> Result<Option<isize>, Parse> {
        Ok(match json {
            None => None,
            Some(json) => match member(key, json) {
                Some(yojson::T::Int(i)) => Some(*i),
                Some(yojson::T::Intlit(s)) => match int_of_string_opt(s) {
                    Some(i) => Some(i),
                    None => return raise_parse(format!("not an int: {}", s)),
                },
                _ => None,
            },
        })
    }

    pub fn float_opt(json: Option<&yojson::T>, key: &str) -> Result<Option<f64>, Parse> {
        Ok(match json {
            None => None,
            Some(json) => match member(key, json) {
                Some(yojson::T::Float(f)) => Some(*f),
                Some(yojson::T::Int(i)) => Some(*i as f64),
                Some(yojson::T::Intlit(s)) => match float_of_string_opt(s) {
                    Some(f) => Some(f),
                    None => return raise_parse(format!("not a float: {}", s)),
                },
                _ => None,
            },
        })
    }

    pub fn array_opt<'a>(
        json: Option<&'a yojson::T>,
        key: &str,
    ) -> Option<Vec<Option<&'a yojson::T>>> {
        match json {
            None => None,
            Some(json) => match member(key, json) {
                Some(yojson::T::List(l)) => Some(l.iter().map(Some).collect()),
                _ => None,
            },
        }
    }

    /// (`opt_getter` returns what it raises as its `Err`.)
    pub fn get_exn<'a, A>(
        opt_getter: impl FnOnce(Option<&'a yojson::T>, &str) -> Result<Option<A>, Parse>,
        json: Option<&'a yojson::T>,
        key: &str,
    ) -> Result<A, Parse> {
        match opt_getter(json, key)? {
            None => raise_parse(key.to_string()),
            Some(v) => Ok(v),
        }
    }

    // Accessors which return a supplied default on absence

    pub fn string_d(json: Option<&yojson::T>, key: &str, default: String) -> String {
        string_opt(json, key).unwrap_or(default)
    }

    pub fn bool_d(json: Option<&yojson::T>, key: &str, default: bool) -> bool {
        bool_opt(json, key).unwrap_or(default)
    }

    pub fn int_d(json: Option<&yojson::T>, key: &str, default: isize) -> Result<isize, Parse> {
        Ok(int_opt(json, key)?.unwrap_or(default))
    }

    pub fn float_d(json: Option<&yojson::T>, key: &str, default: f64) -> Result<f64, Parse> {
        Ok(float_opt(json, key)?.unwrap_or(default))
    }

    pub fn array_d<'a>(
        json: Option<&'a yojson::T>,
        key: &str,
        default: Vec<Option<&'a yojson::T>>,
    ) -> Vec<Option<&'a yojson::T>> {
        array_opt(json, key).unwrap_or(default)
    }

    // Accessors which throw "Error.Parse key" on absence

    pub fn bool_exn(json: Option<&yojson::T>, key: &str) -> Result<bool, Parse> {
        get_exn(|j, k| Ok(bool_opt(j, k)), json, key)
    }

    pub fn string_exn(json: Option<&yojson::T>, key: &str) -> Result<String, Parse> {
        get_exn(|j, k| Ok(string_opt(j, k)), json, key)
    }

    pub fn val_exn<'a>(json: Option<&'a yojson::T>, key: &str) -> Result<&'a yojson::T, Parse> {
        get_exn(|j, k| Ok(val_opt(j, k)), json, key)
    }

    pub fn int_exn(json: Option<&yojson::T>, key: &str) -> Result<isize, Parse> {
        get_exn(int_opt, json, key)
    }

    pub fn float_exn(json: Option<&yojson::T>, key: &str) -> Result<f64, Parse> {
        get_exn(float_opt, json, key)
    }

    pub fn array_exn<'a>(
        json: Option<&'a yojson::T>,
        key: &str,
    ) -> Result<Vec<Option<&'a yojson::T>>, Parse> {
        get_exn(|j, k| Ok(array_opt(j, k)), json, key)
    }

    /// obj_exn lifts the result into the "json option" monad
    pub fn obj_exn<'a>(
        json: Option<&'a yojson::T>,
        key: &str,
    ) -> Result<Option<&'a yojson::T>, Parse> {
        Ok(Some(get_exn(|j, k| Ok(obj_opt(j, k)), json, key)?))
    }

    pub fn string_array_exn(json: Option<&yojson::T>, key: &str) -> Result<Vec<String>, Parse> {
        array_exn(json, key)?
            .into_iter()
            // `Option.value_exn`: the elements of `array_exn` are all `Some`.
            .map(|opt| opt.unwrap())
            .map(|v| match v {
                yojson::T::String(s) => Ok(s.clone()),
                _ => raise_parse("expected string in array".to_string()),
            })
            .collect()
    }
}

/// `module Jprint`
pub mod jprint {
    use super::yojson;

    /// object_opt is like `Assoc constructor except it takes
    /// key * (value option): if a value is None, then it omits this member.
    pub fn object_opt(keyvalues: Vec<(String, Option<yojson::T>)>) -> yojson::T {
        yojson::T::Assoc(
            keyvalues
                .into_iter()
                .filter_map(|(key, value)| value.map(|value| (key, value)))
                .collect(),
        )
    }

    /// Convenience function to convert string list to `List
    pub fn string_array(l: &[String]) -> yojson::T {
        yojson::T::List(l.iter().map(|s| yojson::T::String(s.clone())).collect())
    }
}

/// `module AdhocJsonHelpers` (added for the file watchers): the functions
/// that `Files_to_ignore` and the Watchman backend use. Not here:
/// `get_number_exn`, `get_number_val`. `exception Not_found` is the error
/// [`adhoc_json_helpers::NotFound`].
pub mod adhoc_json_helpers {
    use super::yojson;

    /// `exception Not_found`
    #[derive(Clone, Copy, PartialEq, Eq)]
    pub struct NotFound;

    impl std::fmt::Debug for NotFound {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.write_str("Hh_json_helpers.AdhocJsonHelpers.Not_found")
        }
    }

    pub fn get_object_exn(json: &yojson::T) -> Result<&Vec<(String, yojson::T)>, NotFound> {
        match json {
            yojson::T::Assoc(obj) => Ok(obj),
            _ => Err(NotFound),
        }
    }

    /// `Base.List.Assoc.find`: the first binding of `key`.
    pub fn try_get_val<'a>(key: &str, json: &'a yojson::T) -> Result<Option<&'a yojson::T>, NotFound> {
        let obj = get_object_exn(json)?;
        Ok(obj.iter().find(|(k, _)| k == key).map(|(_, v)| v))
    }

    pub fn get_string_exn(json: &yojson::T) -> Result<&String, NotFound> {
        match json {
            yojson::T::String(s) => Ok(s),
            _ => Err(NotFound),
        }
    }

    pub fn get_bool_exn(json: &yojson::T) -> Result<bool, NotFound> {
        match json {
            yojson::T::Bool(b) => Ok(*b),
            _ => Err(NotFound),
        }
    }

    pub fn get_array_exn(json: &yojson::T) -> Result<&Vec<yojson::T>, NotFound> {
        match json {
            yojson::T::List(l) => Ok(l),
            _ => Err(NotFound),
        }
    }

    pub fn get_string_val(
        key: &str,
        default: Option<String>,
        json: &yojson::T,
    ) -> Result<String, NotFound> {
        let v = try_get_val(key, json)?;
        match (v, default) {
            (Some(v), _) => Ok(get_string_exn(v)?.clone()),
            (None, Some(def)) => Ok(def),
            (None, None) => Err(NotFound),
        }
    }

    pub fn get_bool_val(key: &str, default: Option<bool>, json: &yojson::T) -> Result<bool, NotFound> {
        let v = try_get_val(key, json)?;
        match (v, default) {
            (Some(v), _) => get_bool_exn(v),
            (None, Some(def)) => Ok(def),
            (None, None) => Err(NotFound),
        }
    }

    pub fn get_array_val(
        key: &str,
        default: Option<Vec<yojson::T>>,
        json: &yojson::T,
    ) -> Result<Vec<yojson::T>, NotFound> {
        let v = try_get_val(key, json)?;
        match (v, default) {
            (Some(v), _) => Ok(get_array_exn(v)?.clone()),
            (None, Some(def)) => Ok(def),
            (None, None) => Err(NotFound),
        }
    }

    pub fn strlist(args: &[&str]) -> yojson::T {
        yojson::T::List(
            args.iter()
                .map(|arg| yojson::T::String(arg.to_string()))
                .collect(),
        )
    }

    /// Prepend a string to a JSON array of strings. pred stands for predicate,
    /// because that's how they are typically represented in watchman. See e.g.
    /// https://facebook.github.io/watchman/docs/expr/allof.html
    pub fn pred(name: &str, args: Vec<yojson::T>) -> yojson::T {
        let mut l = Vec::with_capacity(args.len() + 1);
        l.push(yojson::T::String(name.to_string()));
        l.extend(args);
        yojson::T::List(l)
    }
}

/// `lhs >=@ rhs`
fn ge_opt(lhs: isize, rhs: Option<isize>) -> bool {
    match rhs {
        None => false,
        Some(rhs) => lhs >= rhs,
    }
}

/// `json_truncate ?max_string_length ?max_object_child_count
/// ?max_array_elt_count ?max_depth ?max_total_count ?has_changed json`
/// (added for the file watchers). OCaml cuts a string at a byte; a cut in
/// the middle of a UTF-8 character leaves U+FFFD here.
pub fn json_truncate(
    max_string_length: Option<isize>,
    max_object_child_count: Option<isize>,
    max_array_elt_count: Option<isize>,
    max_depth: Option<isize>,
    max_total_count: Option<isize>,
    mut has_changed: Option<&mut bool>,
    json: &yojson::T,
) -> yojson::T {
    struct St<'a, 'b> {
        total_count: isize,
        has_changed: &'a mut Option<&'b mut bool>,
    }
    impl St<'_, '_> {
        fn mark_changed(&mut self) {
            if let Some(r) = self.has_changed.as_mut() {
                **r = true
            }
        }
    }
    fn truncate_children<A: Clone>(
        st: &mut St<'_, '_>,
        max_total_count: Option<isize>,
        children: &[A],
        max_child_count: Option<isize>,
        f: &mut dyn FnMut(&mut St<'_, '_>, &A) -> A,
    ) -> Vec<A> {
        let mut res = vec![];
        let mut child_count = 0;
        for c in children {
            if ge_opt(st.total_count, max_total_count) {
                st.mark_changed();
                break;
            }
            if ge_opt(child_count, max_child_count) {
                st.mark_changed();
                break;
            }
            st.total_count += 1;
            res.push(f(st, c));
            child_count += 1;
        }
        res
    }
    #[allow(clippy::too_many_arguments)]
    fn truncate(
        st: &mut St<'_, '_>,
        limits: (Option<isize>, Option<isize>, Option<isize>, Option<isize>, Option<isize>),
        depth: isize,
        json: &yojson::T,
    ) -> yojson::T {
        let (max_string_length, max_object_child_count, max_array_elt_count, max_depth, max_total_count) =
            limits;
        match json {
            yojson::T::Assoc(props) if props.is_empty() => json.clone(),
            yojson::T::List(values) if values.is_empty() => json.clone(),
            yojson::T::Int(_)
            | yojson::T::Intlit(_)
            | yojson::T::Float(_)
            | yojson::T::Bool(_)
            | yojson::T::Null => json.clone(),
            yojson::T::Assoc(props) => {
                if ge_opt(depth, max_depth) {
                    st.mark_changed();
                    yojson::T::Assoc(vec![])
                } else {
                    yojson::T::Assoc(truncate_children(
                        st,
                        max_total_count,
                        props,
                        max_object_child_count,
                        &mut |st, (k, v)| (k.clone(), truncate(st, limits, depth + 1, v)),
                    ))
                }
            }
            yojson::T::List(values) => {
                if ge_opt(depth, max_depth) {
                    st.mark_changed();
                    yojson::T::List(vec![])
                } else {
                    yojson::T::List(truncate_children(
                        st,
                        max_total_count,
                        values,
                        max_array_elt_count,
                        &mut |st, v| truncate(st, limits, depth + 1, v),
                    ))
                }
            }
            yojson::T::String(s) => match max_string_length {
                None => json.clone(),
                Some(max_string_length) => {
                    if s.len() as isize <= max_string_length {
                        yojson::T::String(s.clone())
                    } else {
                        st.mark_changed();
                        let cut = &s.as_bytes()[..max_string_length.max(0) as usize];
                        yojson::T::String(format!("{}...", String::from_utf8_lossy(cut)))
                    }
                }
            },
        }
    }
    let mut st = St {
        total_count: 0,
        has_changed: &mut has_changed,
    };
    truncate(
        &mut st,
        (
            max_string_length,
            max_object_child_count,
            max_array_elt_count,
            max_depth,
            max_total_count,
        ),
        0,
        json,
    )
}

#[cfg(test)]
mod adhoc_tests {
    use super::adhoc_json_helpers::*;
    use super::*;

    #[test]
    fn adhoc_helpers() {
        let json = yojson::T::Assoc(vec![
            ("a".to_string(), yojson::T::String("x".to_string())),
            ("a".to_string(), yojson::T::String("shadowed".to_string())),
            ("b".to_string(), yojson::T::Bool(true)),
            ("l".to_string(), strlist(&["p", "q"])),
        ]);
        assert_eq!(get_string_val("a", None, &json), Ok("x".to_string()));
        assert_eq!(get_string_val("z", Some("d".to_string()), &json), Ok("d".to_string()));
        assert_eq!(get_string_val("z", None, &json), Err(NotFound));
        assert_eq!(get_string_val("b", None, &json), Err(NotFound));
        assert_eq!(get_bool_val("b", None, &json), Ok(true));
        assert_eq!(get_array_val("l", None, &json).map(|l| l.len()), Ok(2));
        assert_eq!(get_string_val("a", None, &yojson::T::Null), Err(NotFound));
        assert_eq!(
            yojson::to_string(&pred("anyof", vec![strlist(&["name", "x"])])),
            r#"["anyof",["name","x"]]"#
        );
    }

    #[test]
    fn truncation() {
        let json = yojson::T::Assoc(vec![(
            "files".to_string(),
            strlist(&["1", "2", "3", "4", "5", "6", "7"]),
        )]);
        let mut has_changed = false;
        let t = json_truncate(None, None, Some(5), None, None, Some(&mut has_changed), &json);
        assert!(has_changed);
        assert_eq!(yojson::to_string(&t), r#"{"files":["1","2","3","4","5"]}"#);
        let mut has_changed = false;
        let small = strlist(&["1"]);
        let t = json_truncate(None, None, Some(5), None, None, Some(&mut has_changed), &small);
        assert!(!has_changed);
        assert_eq!(t, small);
        let t = json_truncate(Some(2), None, None, Some(1), None, None, &json);
        assert_eq!(yojson::to_string(&t), r#"{"files":[]}"#);
        let t = json_truncate(Some(2), None, None, None, None, None, &yojson::T::String("abcd".to_string()));
        assert_eq!(yojson::to_string(&t), r#""ab...""#);
    }
}

#[cfg(test)]
mod jget_tests {
    use super::jget::*;
    use super::jprint::*;
    use super::*;

    fn s(x: &str) -> yojson::T {
        yojson::T::String(x.to_string())
    }

    fn catch_parse<A>(r: Result<A, Parse>) -> Result<A, String> {
        r.map_err(|Parse(s)| s)
    }

    #[test]
    fn accessors() {
        let json = yojson::T::Assoc(vec![
            ("s".to_string(), s("a")),
            ("s".to_string(), s("shadowed")),
            ("i".to_string(), yojson::T::Int(3)),
            ("big".to_string(), yojson::T::Intlit("99999999999999999999".to_string())),
            ("lit".to_string(), yojson::T::Intlit("0x10".to_string())),
            ("f".to_string(), yojson::T::Float(1.5)),
            ("b".to_string(), yojson::T::Bool(true)),
            ("o".to_string(), yojson::T::Assoc(vec![("x".to_string(), yojson::T::Null)])),
            ("l".to_string(), yojson::T::List(vec![s("x"), s("y")])),
            ("n".to_string(), yojson::T::List(vec![yojson::T::Int(1)])),
        ]);
        let j = Some(&json);
        assert_eq!(string_opt(j, "s"), Some("a".to_string()));
        assert_eq!(string_opt(j, "i"), None);
        assert_eq!(string_opt(None, "s"), None);
        assert_eq!(int_opt(j, "i"), Ok(Some(3)));
        assert_eq!(int_opt(j, "lit"), Ok(Some(16)));
        assert_eq!(
            catch_parse(int_opt(j, "big")),
            Err("not an int: 99999999999999999999".to_string())
        );
        assert_eq!(float_opt(j, "i"), Ok(Some(3.0)));
        assert_eq!(float_opt(j, "f"), Ok(Some(1.5)));
        assert_eq!(float_opt(j, "big"), Ok(Some(99999999999999999999.0)));
        assert_eq!(bool_d(j, "b", false), true);
        assert_eq!(bool_d(j, "s", false), false);
        assert_eq!(int_d(j, "missing", 7), Ok(7));
        assert!(obj_opt(j, "o").is_some());
        assert!(obj_opt(j, "l").is_none());
        assert_eq!(val_opt(j, "i"), Some(&yojson::T::Int(3)));
        assert_eq!(array_opt(j, "l").map(|l| l.len()), Some(2));
        assert_eq!(
            string_array_exn(j, "l"),
            Ok(vec!["x".to_string(), "y".to_string()])
        );
        assert_eq!(
            catch_parse(string_array_exn(j, "n")),
            Err("expected string in array".to_string())
        );
        assert_eq!(catch_parse(string_exn(j, "missing")), Err("missing".to_string()));
        assert_eq!(catch_parse(obj_exn(j, "l")), Err("l".to_string()));
        assert_eq!(
            format!("{:?}", Parse("a\"b".to_string())),
            "Hh_json_helpers.Jget.Parse(\"a\\\"b\")"
        );
    }

    #[test]
    fn printers() {
        assert_eq!(
            object_opt(vec![
                ("a".to_string(), Some(yojson::T::Int(1))),
                ("b".to_string(), None),
                ("c".to_string(), Some(yojson::T::Null)),
            ]),
            yojson::T::Assoc(vec![
                ("a".to_string(), yojson::T::Int(1)),
                ("c".to_string(), yojson::T::Null)
            ])
        );
        assert_eq!(
            yojson::to_string(&string_array(&["x".to_string(), "\"".to_string()])),
            r#"["x","\""]"#
        );
    }
}

#[cfg(test)]
mod tests {
    use super::access::*;
    use super::*;

    fn s(x: &str) -> yojson::T {
        yojson::T::String(x.to_string())
    }

    #[test]
    fn accessors() {
        let json = yojson::T::Assoc(vec![
            ("kind".to_string(), s("class")),
            ("kind".to_string(), s("shadowed")),
            ("args".to_string(), yojson::T::List(vec![])),
            (
                "inner".to_string(),
                yojson::T::Assoc(vec![("b".to_string(), yojson::T::Bool(true))]),
            ),
        ]);
        let root: Keytrace = vec!["0".to_string(), "args".to_string()];
        assert_eq!(
            get_string("kind", (&json, &root)),
            Ok((
                "class".to_string(),
                vec!["kind".to_string(), "0".to_string(), "args".to_string()]
            ))
        );
        assert_eq!(
            get_array("args", (&json, &vec![])),
            Ok((vec![], vec!["args".to_string()]))
        );
        let (inner, kt) = get_obj("inner", (&json, &vec![])).unwrap();
        assert_eq!(get_bool("b", (&inner, &kt)).map(|(b, _)| b), Ok(true));
        let missing = get_bool("missing", (&json, &root)).unwrap_err();
        assert_eq!(
            missing,
            AccessFailure::MissingKeyError("missing".to_string(), root.clone())
        );
        assert_eq!(
            access_failure_to_string(&missing),
            "Missing key: missing (at field `args.0`)"
        );
        let wrong = get_bool("kind", (&json, &vec![])).unwrap_err();
        assert_eq!(
            access_failure_to_string(&wrong),
            "Value expected to be Bool (at field `kind`)"
        );
        let not_an_object = get_val("kind", (&s("x"), &vec![])).unwrap_err();
        assert_eq!(
            access_failure_to_string(&not_an_object),
            "Value is not an object "
        );
        assert_eq!(keytrace_to_string(&[]), "");
    }
}
