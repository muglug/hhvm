// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/tast_check/global_access_check.ml`. See `hh/PORTING.md`.
//!
//! This global access checker raises an error when:
//! - a global variable is written:
//!   - a global variable is directly written (e.g. (Foo::$bar)->prop = 1;)
//!   - a global variable is written via references (e.g. $a = Foo::$bar; $a->prop = 1;)
//!   - a global variable is passed to a function call, in which it may be written.
//! - or a global variable is read.
//!
//! Notice that the return value of a memoized function (if it is mutable)
//! is treated as a global variable as well.
//!
//! By default, this checker is turned off.
//! To turn on this checker, use the argument --enable-global-access-check.
//!
//! A trick to run this checker on a specific list of files is to
//!   use "--config enable_type_check_filter_files=true" togehter with above arguments,
//!   which runs typechecker only on files listed in ~/.hack_type_check_files_filter.
//!
//! `visitor` inherits `Tast_visitor.iter_with_state` with the state
//! `(ctx, fun_name)`: its context is `(env, (ctx, fun_name))`.
//!
//! `ctx` is a record of two references (a hash table and a set) that the
//! traversal shares and updates; the references are never aliased by two
//! records, so a `ctx` is an `Rc` of two `RefCell`s. `current_ctx`, a global
//! value in OCaml, is per thread.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::HashMap;
use std::rc::Rc;
use std::sync::LazyLock;

use oxidized::aast::Argument;
use oxidized::aast::ClassId;
use oxidized::aast::ClassId_;
use oxidized::aast::Expr;
use oxidized::aast::Expr_;
use oxidized::aast::Hint;
use oxidized::aast::Hint_;
use oxidized::aast::Lid;
use oxidized::aast::Stmt_;
use oxidized::aast_visitor::Node;
use oxidized::aast_visitor::Visitor;
use oxidized::ast_defs::Bop;
use oxidized::ast_defs::Id;
use oxidized::ast_defs::PropOrMethod;
use oxidized::ast_defs::Pstring;
use oxidized::ast_defs::Tprim;
use oxidized::ast_defs::Uop;
use oxidized::error_codes::GlobalAccessCheck;
use oxidized::pos::Pos;

use crate::aast_utils;
use crate::decl_entry;
use crate::diagnostics;
use crate::local_id;
use crate::s_set::T as SSet;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_env::print_ty;
use crate::tast_visitor;
use crate::typing_defs;
use crate::typing_defs::ClassElt;
use crate::typing_defs::ShapeType;
use crate::typing_defs::ShapeTypeSimple;
use crate::typing_defs::TupleExtra;
use crate::typing_defs::TupleType;
use crate::typing_defs::Ty;
use crate::typing_defs::Ty_;
use crate::typing_defs::get_node;
use crate::typing_make_type as make_type;
use crate::typing_reason as reason;
use crate::typing_set;
use crate::typing_subtype;
use crate::typing_utils;

/// `String.sub s ~pos:1 ~len:(String.length s - 1)`: `s` without its first
/// byte.
fn string_sub_from_1(s: &str) -> String {
    if s.is_empty() {
        panic!("String.sub / Bytes.sub")
    }
    match s.get(1..) {
        Some(rest) => rest.to_string(),
        None => String::from_utf8_lossy(&s.as_bytes()[1..]).into_owned(),
    }
}

/// Recognize common patterns for global access (only writes for now).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum GlobalAccessPattern {
    /// Write to a global variable whose value is null
    Singleton,
    /// Write to a global collection when the element is null or does not exist
    Caching,
    /// Increase a global variable by 1 or -1
    CounterIncrement,
    /// Assign null or empty string to a global variable
    WriteEmptyOrNull,
    /// Assign a literal to a global variable
    WriteLiteral,
    /// Assign a global variable to another one
    WriteGlobalToGlobal,
    /// Write non-sensitive data to a global variable
    WriteNonSensitive,
    /// Global write via super global functions
    SuperGlobalWrite,
    /// Global read via super global functions
    SuperGlobalRead,
    /// No pattern above is recognized
    NoPattern,
}

/// `[@@deriving show { with_path = false }]`
fn show_global_access_pattern(p: GlobalAccessPattern) -> String {
    match p {
        GlobalAccessPattern::Singleton => "Singleton",
        GlobalAccessPattern::Caching => "Caching",
        GlobalAccessPattern::CounterIncrement => "CounterIncrement",
        GlobalAccessPattern::WriteEmptyOrNull => "WriteEmptyOrNull",
        GlobalAccessPattern::WriteLiteral => "WriteLiteral",
        GlobalAccessPattern::WriteGlobalToGlobal => "WriteGlobalToGlobal",
        GlobalAccessPattern::WriteNonSensitive => "WriteNonSensitive",
        GlobalAccessPattern::SuperGlobalWrite => "SuperGlobalWrite",
        GlobalAccessPattern::SuperGlobalRead => "SuperGlobalRead",
        GlobalAccessPattern::NoPattern => "NoPattern",
    }
    .to_string()
}

/// `GlobalAccessPatternSet` (`Stdlib.Set.Make`, ordered by the derived
/// `compare_global_access_pattern`, which is the order of the constructors).
type GlobalAccessPatternSet = BTreeSet<GlobalAccessPattern>;

/// Raise a global access error if the corresponding write/read mode is enabled.
fn raise_global_access_error(
    pos: &Pos,
    fun_name: &str,
    data_type: &str,
    global_set: &SSet,
    patterns: &GlobalAccessPatternSet,
    error_code: GlobalAccessCheck,
) {
    let error_message = match error_code {
        GlobalAccessCheck::DefiniteGlobalWrite => "definitely written.",
        GlobalAccessCheck::PossibleGlobalWriteViaReference => "possibly written via reference.",
        GlobalAccessCheck::PossibleGlobalWriteViaFunctionCall => {
            "possibly written via function call."
        }
        GlobalAccessCheck::DefiniteGlobalRead => "definitely read.",
    };
    let global_vars_str = global_set
        .iter()
        .map(|s| s.as_str())
        .collect::<Vec<_>>()
        .join(";");
    let print_pattern = |p: GlobalAccessPattern| match p {
        GlobalAccessPattern::NoPattern => None,
        p => Some(show_global_access_pattern(p)),
    };
    let patterns_str = patterns
        .iter()
        .filter_map(|p| print_pattern(*p))
        .collect::<Vec<_>>()
        .join(",");
    let message = "[".to_string()
        + fun_name
        + "]{"
        + &global_vars_str
        + "}("
        + data_type
        + ")"
        + &(if !patterns_str.is_empty() {
            "<".to_string() + &patterns_str + ">"
        } else {
            "".to_string()
        })
        + " A global variable is "
        + error_message;
    diagnostics::global_access_error(error_code, pos.clone(), message)
}

/// Various types of data sources for a local variable.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum DataSource {
    /// A reference to a mutable global var
    GlobalReference(String),
    /// The value of a immutable global var
    GlobalValue(String),
    /// null or empty string
    NullOrEmpty,
    /// Boolean, integer, floating-point, or string literals
    Literal,
    /// E.g. timer, site var
    NonSensitive,
    /// Other sources that have not been identified yet
    Unknown,
}

/// `[@@deriving show]` (with the path of the constructors)
fn show_data_source(s: &DataSource) -> String {
    match s {
        DataSource::GlobalReference(s) => {
            format!("(Global_access_check.GlobalReference {})", crate::rt::ocaml_printf::sprintf_s(s))
        }
        DataSource::GlobalValue(s) => {
            format!("(Global_access_check.GlobalValue {})", crate::rt::ocaml_printf::sprintf_s(s))
        }
        DataSource::NullOrEmpty => "Global_access_check.NullOrEmpty".to_string(),
        DataSource::Literal => "Global_access_check.Literal".to_string(),
        DataSource::NonSensitive => "Global_access_check.NonSensitive".to_string(),
        DataSource::Unknown => "Global_access_check.Unknown".to_string(),
    }
}

/// `DataSourceSet` (`Stdlib.Set.Make`, ordered by the derived
/// `compare_data_source`).
type DataSourceSet = BTreeSet<DataSource>;

fn data_source_set_singleton(s: DataSource) -> DataSourceSet {
    BTreeSet::from([s])
}

/// `DataSourceSet.union`
fn data_source_set_union(s1: DataSourceSet, s2: DataSourceSet) -> DataSourceSet {
    let mut s = s1;
    s.extend(s2);
    s
}

/// Given the data sources of written data (i.e. RHS of assignment),
/// return the recognized patterns. Specially, if there is unknown
/// data sources, no pattern is recognized.
fn get_patterns_from_written_data_srcs(srcs: &DataSourceSet) -> GlobalAccessPatternSet {
    let is_unknown = |s: &DataSource| match s {
        DataSource::Unknown => true,
        _ => false,
    };
    if !srcs.iter().any(is_unknown) {
        let add_src_to_patterns = |s: &DataSource, mut acc: GlobalAccessPatternSet| {
            let p = match s {
                DataSource::GlobalReference(_) | DataSource::GlobalValue(_) => {
                    GlobalAccessPattern::WriteGlobalToGlobal
                }
                DataSource::NullOrEmpty => GlobalAccessPattern::WriteEmptyOrNull,
                DataSource::Literal => GlobalAccessPattern::WriteLiteral,
                DataSource::NonSensitive => GlobalAccessPattern::WriteNonSensitive,
                DataSource::Unknown => GlobalAccessPattern::NoPattern,
            };
            acc.insert(p);
            acc
        };
        srcs.iter().fold(GlobalAccessPatternSet::new(), |acc, s| {
            add_src_to_patterns(s, acc)
        })
    } else {
        GlobalAccessPatternSet::new()
    }
}

/// The set of safe/non-sensitive functions or classes
const SAFE_FUNC_IDS: &[&str] = &["\\microtime", "\\FlibSL\\PHP\\microtime"];

const SAFE_CLASS_IDS: &[&str] = &["\\Time"];

/// The set of functions whose return value's data sources are
/// the union of the data sources of all its parameters.
const SRC_FROM_PARA_FUNC_IDS: &[&str] = &[
    "\\FlibSL\\Dict\\merge",
    "\\HH\\Lib\\Dict\\merge",
    "\\FlibSL\\Keyset\\union",
    "\\HH\\Lib\\Keyset\\union",
];

/// Functions whose return value is from only its first parameter.
const SRC_FROM_FIRST_PARA_FUNC_IDS: &[&str] = &[
    "\\HH\\idx",
    "\\FlibSL\\Dict\\filter_keys",
    "\\HH\\Lib\\Dict\\filter_keys",
];

/// Functions that check if its first parameter is not null.
const CHECK_NON_NULL_FUNC_IDS: &[&str] =
    &["\\FlibSL\\C\\contains_key", "\\HH\\Lib\\C\\contains_key"];

/// `S_set.mem x set` on the sets above
fn mem(x: &str, set: &[&str]) -> bool {
    set.contains(&x)
}

/// The type to represent the super global classes under www/flib/core/superglobals.
struct SuperGlobalClassDetail {
    /// global_variable is None if the corresponding super global variable is not fixed,
    /// but is given as the parameter of get/set methods, e.g. in GlobalVARIABLES.
    global_variable: Option<&'static str>,
    global_write_methods: BTreeSet<&'static str>,
    global_read_methods: BTreeSet<&'static str>,
}

/// Map from super global class names to the corresponding details.
static SUPER_GLOBAL_CLASS_MAP: LazyLock<BTreeMap<&'static str, SuperGlobalClassDetail>> =
    LazyLock::new(|| {
        let s_set = |l: &[&'static str]| l.iter().copied().collect::<BTreeSet<&'static str>>();
        BTreeMap::from([
            (
                "\\GlobalCOOKIE",
                SuperGlobalClassDetail {
                    global_variable: Some("$_COOKIE"),
                    global_write_methods: s_set(&[
                        "redactCookieSuperglobal",
                        "overrideCookieSuperglobalForEmulation",
                        "setForCookieMonsterInternalTest",
                    ]),
                    global_read_methods: s_set(&[
                        "getInitialKeys",
                        "getCopy_COOKIE_MONSTER_INTERNAL_ONLY",
                        "getCopyForEmulation",
                    ]),
                },
            ),
            (
                "\\GlobalENV",
                SuperGlobalClassDetail {
                    global_variable: Some("$_ENV"),
                    global_write_methods: s_set(&["set_ENV_DO_NOT_USE", "set"]),
                    global_read_methods: s_set(&[
                        "getCopy_DO_NOT_USE",
                        "get",
                        "getReadonly",
                        "idx",
                        "idxReadonly",
                    ]),
                },
            ),
            (
                "\\GlobalFILES",
                SuperGlobalClassDetail {
                    global_variable: Some("$_FILES"),
                    global_write_methods: s_set(&["set_FILES_DO_NOT_USE", "set"]),
                    global_read_methods: s_set(&[
                        "getCopy_DO_NOT_USE",
                        "get",
                        "getReadonly",
                        "idx",
                    ]),
                },
            ),
            (
                "\\GlobalGET",
                SuperGlobalClassDetail {
                    global_variable: Some("$_GET"),
                    global_write_methods: s_set(&["set_GET_DO_NOT_USE", "set"]),
                    global_read_methods: s_set(&[
                        "getCopy_DO_NOT_USE",
                        "get",
                        "getReadonly",
                        "idx",
                        "idxReadonly",
                    ]),
                },
            ),
            (
                "\\GlobalPOST",
                SuperGlobalClassDetail {
                    global_variable: Some("$_POST"),
                    global_write_methods: s_set(&["set_POST_DO_NOT_USE", "set"]),
                    global_read_methods: s_set(&[
                        "getCopy_DO_NOT_USE",
                        "get",
                        "getReadonly",
                        "idx",
                        "idxReadonly",
                    ]),
                },
            ),
            (
                "\\GlobalREQUEST",
                SuperGlobalClassDetail {
                    global_variable: Some("$_REQUEST"),
                    global_write_methods: s_set(&[
                        "set_REQUEST_DO_NOT_USE",
                        "set",
                        "redactCookiesFromRequestSuperglobal",
                    ]),
                    global_read_methods: s_set(&[
                        "getCopy_DO_NOT_USE",
                        "get",
                        "getReadonly",
                        "idx",
                    ]),
                },
            ),
            (
                "\\GlobalSERVER",
                SuperGlobalClassDetail {
                    global_variable: Some("$_SERVER"),
                    global_write_methods: s_set(&["set_SERVER_DO_NOT_USE", "set"]),
                    global_read_methods: s_set(&[
                        "getCopy_DO_NOT_USE",
                        "getDocumentRoot",
                        "getPHPRoot",
                        "getPHPSelf",
                        "getRequestTime",
                        "getParentRequestTime",
                        "getRequestTimeFloat",
                        "getParentRequestTimeFloat",
                        "getScriptName",
                        "getServerAddress",
                        "getArgv",
                        "getArgc",
                        "getHTTPAuthorization",
                        "getHTTPHost",
                        "getHTTPReferer_DO_NOT_USE",
                        "getHTTPUserAgent",
                        "getRequestMethod",
                        "getSecFetchDest",
                        "getSecFetchMode",
                        "getSecFetchSite",
                        "getSecFetchUser",
                        "getXFBLSD",
                        "getTFBENV",
                        "getRequestURIString",
                        "getRequestURI_UNSAFE_TO_LOG",
                        "getServerName",
                        "getUserName",
                        "getLocalCanaryID",
                        "getInterestingIniKeys",
                        "idx",
                        "idxReadonly",
                        "get",
                        "getReadonly",
                        "idxString_UNSAFE",
                        "idxArgv",
                    ]),
                },
            ),
            // GlobalSESSION is not implemented and hence omitted.
            (
                "\\GlobalVARIABLES",
                SuperGlobalClassDetail {
                    // The global variable is not fixed but given as the methods's parameter.
                    global_variable: None,
                    global_write_methods: s_set(&["set"]),
                    global_read_methods: s_set(&["idxReadonly", "idx", "get", "getReadonly"]),
                },
            ),
        ])
    });

/// Given an expression, check if it's a call of static method from some super global class.
/// If so, raise the global read/write error, and return true; otherwise, return false.
fn check_super_global_method(expr: &tast::Expr_, env: &Env, external_fun_name: &str) -> bool {
    match expr {
        Expr_::Call(call) => match &call.func {
            Expr(func_ty, pos, Expr_::ClassConst(cc)) => match &**cc {
                (ClassId(_, _, ClassId_::CI(Id(_, class_name))), (_, method_name)) => {
                    let args = &call.args;
                    // Check if the class is a super global class
                    match SUPER_GLOBAL_CLASS_MAP.get(class_name.as_str()) {
                        Some(class_detail) => {
                            // Check if the method is write or read or not recognized.
                            let error_code_pattern_opt = if class_detail
                                .global_write_methods
                                .contains(method_name.as_str())
                            {
                                Some((
                                    GlobalAccessCheck::DefiniteGlobalWrite,
                                    GlobalAccessPattern::SuperGlobalWrite,
                                ))
                            } else if class_detail
                                .global_read_methods
                                .contains(method_name.as_str())
                            {
                                Some((
                                    GlobalAccessCheck::DefiniteGlobalRead,
                                    GlobalAccessPattern::SuperGlobalRead,
                                ))
                            } else {
                                None
                            };
                            if error_code_pattern_opt.is_some() {
                                let func_ty_str = print_ty(env, func_ty);
                                let (error_code, pattern) = error_code_pattern_opt.unwrap();
                                let default_global_var_name = "$_";
                                let global_var_name = match class_detail.global_variable {
                                    Some(var_name) => var_name.to_string(),
                                    None => {
                                        // If the super global class does not have fixed global var name,
                                        // then the 1st parameter of those get/set methods is assumed to
                                        // be the global var; and if it's a string literal, we simply use
                                        // it, otherwise we don't know and use default name.
                                        match args.as_slice() {
                                            [arg, ..] => match aast_utils::arg_to_expr(arg) {
                                                Expr(_, _, Expr_::String(s)) => {
                                                    "$".to_string() + &String::from_utf8_lossy(s)
                                                }
                                                _ => default_global_var_name.to_string(),
                                            },
                                            [] => default_global_var_name.to_string(),
                                        }
                                    }
                                };
                                raise_global_access_error(
                                    pos,
                                    external_fun_name,
                                    &("superglobal ".to_string() + &func_ty_str),
                                    &SSet::unit(global_var_name),
                                    &GlobalAccessPatternSet::from([pattern]),
                                    error_code,
                                );
                                true
                            } else {
                                false
                            }
                        }
                        _ => false,
                    }
                }
                _ => false,
            },
            _ => false,
        },
        _ => false,
    }
}

/// The context maintains:
/// (1) A hash table from local variables to the corresponding data sources.
/// For any local variable, if its data sources contain GlobalReference(s), then
/// it is potentially a reference to global variable. Notice that a local variable
/// may refers to multiple global variables, for example:
/// "if (condition) { $a = Foo::$bar; } else { $a = memoized_func(); }"
/// after the above code, $a has a reference to either Foo::$bar or memoized_func,
/// thus var_data_src_tbl is like {"a" => {GlobalReference of "Foo::$bar",
/// GlobalReference of "\memoized_func"}}.
/// (2) A set of global variables whose values are null, which can be used to
/// identify singletons. For example, consider the following program:
/// "if (Foo::$bar is null) { Foo::$bar = new Bar(); }"
/// inside the true branch, null_global_var_set is {"Foo::$bar"}, and
/// the assignment to Foo::$bar shall be identified as a singleton.
struct Ctx {
    /// `(string, DataSourceSet.t) Hashtbl.t ref`
    var_data_src_tbl: RefCell<HashMap<String, DataSourceSet>>,
    /// `S_set.t ref`
    null_global_var_set: RefCell<SSet>,
}

thread_local! {
    static CURRENT_CTX: Rc<Ctx> = Rc::new(Ctx {
        var_data_src_tbl: RefCell::new(HashMap::new()),
        null_global_var_set: RefCell::new(SSet::new()),
    });
}

/// Add the key (a variable name) and the value (a set of data srcs) to the table.
fn add_var_data_srcs_to_tbl(
    tbl: &mut HashMap<String, DataSourceSet>,
    var: &str,
    srcs: &DataSourceSet,
) {
    let pre_data_src_set = if tbl.contains_key(var) {
        tbl.get(var).unwrap().clone()
    } else {
        DataSourceSet::new()
    };
    tbl.insert(
        var.to_string(),
        data_source_set_union(pre_data_src_set, srcs.clone()),
    );
}

fn replace_var_data_srcs_in_tbl(
    tbl: &mut HashMap<String, DataSourceSet>,
    var: &str,
    srcs: &DataSourceSet,
) {
    tbl.insert(var.to_string(), srcs.clone());
}

/// Given two hash tables of type (string, DataSourceSet.t) Hashtbl.t, merge the second
/// table into the first one.
fn merge_var_data_srcs_tbls(
    tbl1: &mut HashMap<String, DataSourceSet>,
    tbl2: &HashMap<String, DataSourceSet>,
) {
    for (var, srcs) in tbl2 {
        add_var_data_srcs_to_tbl(tbl1, var, srcs)
    }
}

/// For a hash table whose value is DataSourceSet, get its total cardinal.
fn get_tbl_total_cardinal(tbl: &HashMap<String, DataSourceSet>) -> usize {
    tbl.values()
        .fold(0, |cur_cardinal, v| cur_cardinal + v.len())
}

fn grab_class_elts_from_ty(
    static_: bool,
    seen: Option<&SSet>,
    env: &Env,
    ty: &Ty,
    prop_id: &Pstring,
) -> Vec<ClassElt> {
    let empty = SSet::new();
    let seen = seen.unwrap_or(&empty);
    // Given a list of types, find recurse on the first type that
    // has the property and return the result
    let find_first_in_list = |seen: &SSet, tyl: &[Ty]| {
        tyl.iter().find_map(|ty| {
            match grab_class_elts_from_ty(static_, Some(seen), env, ty, prop_id) {
                tyl if tyl.is_empty() => None,
                tyl => Some(tyl),
            }
        })
    };
    match get_node(ty) {
        Ty_::Tclass(id, _exact, _args) => {
            let class_decl = tast_env::get_class(env, &id.1);
            match class_decl {
                decl_entry::T::Found(class_decl) => {
                    let prop = if static_ {
                        tast_env::get_static_member(false, env, &class_decl, &prop_id.1)
                    } else {
                        tast_env::get_prop(env, &class_decl, &prop_id.1)
                    };
                    prop.into_iter().collect()
                }
                decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => vec![],
            }
        }
        // Accessing a property off of an intersection type
        // should involve exactly one kind of readonlyness, since for
        // the intersection type to exist, the property must be related
        // by some subtyping relationship anyways, and property readonlyness
        // is invariant. Thus we just grab the first one from the list where the prop exists.
        Ty_::Tintersection(tyl) if tyl.is_empty() => vec![],
        Ty_::Tintersection(tyl) => find_first_in_list(seen, tyl).unwrap_or_default(),
        // A union type is more interesting, where we must return all possible cases
        // and be conservative in our use case.
        Ty_::Tunion(tyl) => tyl
            .iter()
            .flat_map(|ty| grab_class_elts_from_ty(static_, Some(seen), env, ty, prop_id))
            .collect(),
        // Generic types can be treated similarly to an intersection type
        // where we find the first prop that works from the upper bounds
        Ty_::Tgeneric(name) => {
            // Avoid circular generics with a set
            if seen.contains(name) {
                vec![]
            } else {
                let new_seen = seen.update(name.clone());
                let upper_bounds = tast_env::get_upper_bounds(env, name);
                find_first_in_list(&new_seen, &typing_set::elements(&upper_bounds))
                    .unwrap_or_default()
            }
        }
        Ty_::Tdependent(_, ty) => {
            // Dependent types have an upper bound that's a class or generic
            grab_class_elts_from_ty(static_, Some(seen), env, ty, prop_id)
        }
        Ty_::Toption(ty) => {
            // If it's nullable, take the
            grab_class_elts_from_ty(static_, Some(seen), env, ty, prop_id)
        }
        _ => vec![],
    }
}

/// Return a list of possible static prop elts given a class_get expression
fn get_static_prop_elts(env: &Env, class_id: &tast::ClassId, prop_id: &Pstring) -> Vec<ClassElt> {
    let ClassId(ty, _, _) = class_id;
    grab_class_elts_from_ty(true, None, env, ty, prop_id)
}

/// Check if an expression is directly from a static variable or not,
/// e.g. it returns true for Foo::$bar or (Foo::$bar)->prop.
fn is_expr_static(env: &Env, Expr(_, _, te): &tast::Expr) -> bool {
    match te {
        Expr_::ClassGet(cg) if matches!(cg.2, PropOrMethod::IsProp) => {
            let (class_id, expr, _) = &**cg;
            // Ignore static variables annotated with <<__SafeForGlobalAccessCheck>>
            let class_elts = get_static_prop_elts(env, class_id, expr);
            !class_elts
                .iter()
                .any(typing_defs::get_ce_safe_global_variable)
        }
        Expr_::ObjGet(og) if matches!(og.3, PropOrMethod::IsProp) => is_expr_static(env, &og.0),
        Expr_::ArrayGet(ag) => is_expr_static(env, &ag.0),
        _ => false,
    }
}

/// Print out global variables, e.g. Foo::$bar => "Foo::$bar", self::$bar => "Foo::$bar",
/// static::$bar => "this::$bar", memoized_func => "\memoized_func", $baz->memoized_method
/// => "Baz->memoized_method", Baz::memoized_method => "Baz::memoized_method",
/// $this->memoized_method => "this->memoized_method".
/// Notice that this does not handle arbitrary expressions.
fn print_global_expr(env: &Env, expr: &tast::Expr_) -> String {
    match expr {
        Expr_::Call(call) => {
            // For function/method calls, we print the caller expression, which could be
            // Id (e.g. memoized_func()) or Obj_get (e.g. $baz->memoized_method()).
            let Expr(_, _, caller_expr) = &call.func;
            print_global_expr(env, caller_expr)
        }
        Expr_::ClassGet(cg) => {
            // For static properties, we concatenate the class type (instead of class_id_, which
            // could be self, parent, static) and the property name.
            let (ClassId(c_ty, _, _), expr, _) = &**cg;
            let class_ty_str = print_ty(env, c_ty);
            class_ty_str + "::" + &expr.1
        }
        Expr_::ClassConst(cc) => {
            // For static method calls, we concatenate the class type and the method name.
            let (ClassId(c_ty, _, _), (_, const_str)) = &**cc;
            print_ty(env, c_ty) + "::" + const_str
        }
        Expr_::Id(id) => {
            let Id(_, name) = &**id;
            name.clone()
        }
        Expr_::ObjGet(og) => {
            // For Obj_get (e.g. $baz->memoized_method()), we concatenate the class type and the method id.
            let (obj, m, _, _) = &**og;
            let class_ty_str = print_ty(env, tast::get_type(obj));
            let Expr(_, _, m_id) = m;
            // For the case $obj?->method(), the question mark is removed from the class type,
            // since we are not interested in the case where $obj is null.
            let remove_question_mark_prefix = |str: String| {
                if str.starts_with('?') {
                    str[1..].to_string()
                } else {
                    str
                }
            };
            // The arguments of `^` are evaluated right to left, as in OCaml.
            let m_str = print_global_expr(env, m_id);
            remove_question_mark_prefix(class_ty_str) + "->" + &m_str
        }
        _ => "Unknown".to_string(),
    }
}

/// Given a function call of type Aast.expr_, if it's memoized, return its function
/// name, otherwise return None.
fn check_func_is_memoized(func_expr: &tast::Expr, env: &Env) -> Option<String> {
    let Expr(func_ty, _, te) = func_expr;
    match tast_env::get_underlying_function_type(env, func_ty.clone()) {
        Some((_, fty)) if typing_defs::get_ft_is_memoized(&fty) => Some(print_global_expr(env, te)),
        _ => None,
    }
}

/// Check if type is a collection.
fn is_value_collection_ty(env: &Env, ty: &Ty) -> bool {
    let mixed = make_type::mixed(reason::none());
    let hackarray = make_type::any_array(reason::none(), mixed.clone(), mixed);
    // Subtype against an empty open shape (shape(...))
    let shape = make_type::open_shape(
        make_type::mixed(reason::none()),
        reason::none(),
        typing_defs::t_shape_map::T::new(),
    );
    typing_utils::is_sub_type(env, ty, &hackarray) || typing_utils::is_sub_type(env, ty, &shape)
}

/// Check if the variable type does NOT has a reference to any object:
/// if so, then it is OK to write to this variable.
/// Copied from is_safe_mut_ty in readonly_check.ml.
/// To do: check if any change is needed for the global write checker.
fn has_no_object_ref_ty(env: &Env, seen: &SSet, ty: &Ty) -> bool {
    let mut env = env.clone();
    let ty = tast_env::expand_type(&mut env, ty.clone());
    let ty = tast_env::strip_dynamic(&env, ty);
    let env = &env;
    match get_node(&ty) {
        // Allow all primitive types
        Ty_::Tprim(_) => true,
        // Open shapes can technically have objects in them, but as long as the current fields don't have objects in them
        // we will allow you to call the function. Note that the function fails at runtime if any shape fields are objects.
        Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple { fields, .. })) => fields
            .values()
            .all(|v| has_no_object_ref_ty(env, seen, &v.ty)),
        Ty_::Tshape(ShapeType::ShapeSplat(_)) => false,
        // If it's a Tclass it's an array type by is_value_collection
        Ty_::Tintersection(tyl) => tyl.iter().any(|l| has_no_object_ref_ty(env, seen, l)),
        // Only error if there isn't a type that it could be that's primitive
        Ty_::Tunion(tyl) => tyl.iter().any(|l| has_no_object_ref_ty(env, seen, l)),
        Ty_::Ttuple(TupleType {
            required,
            optional,
            extra,
        }) => {
            required.iter().all(|l| has_no_object_ref_ty(env, seen, l))
                && optional.iter().all(|l| has_no_object_ref_ty(env, seen, l))
                && match extra {
                    TupleExtra::Tvariadic(t_variadic) => {
                        has_no_object_ref_ty(env, seen, t_variadic)
                    }
                    TupleExtra::Tsplat(t_splat) => has_no_object_ref_ty(env, seen, t_splat),
                }
        }
        Ty_::Tdependent(_, upper) => {
            // check upper bounds
            has_no_object_ref_ty(env, seen, upper)
        }
        Ty_::Tclass((_, id), _, tyl)
            if is_value_collection_ty(env, &ty) || id == "\\HH\\Awaitable" =>
        {
            tyl.iter().all(|l| has_no_object_ref_ty(env, seen, l))
        }
        Ty_::Tgeneric(name) => {
            // Avoid circular generics with a set
            if seen.contains(name) {
                false
            } else {
                let new_seen = seen.update(name.clone());
                let upper_bounds = tast_env::get_upper_bounds(env, name);
                typing_set::exists(|l| has_no_object_ref_ty(env, &new_seen, l), &upper_bounds)
            }
        }
        _ => {
            // Otherwise, check if there's any primitive type it could be
            let primitive_types = vec![
                make_type::bool(reason::none()),
                make_type::int(reason::none()),
                make_type::arraykey(reason::none()),
                make_type::string(reason::none()),
                make_type::float(reason::none()),
                make_type::num(reason::none()),
                // Keysets only contain arraykeys so if they're readonly its safe to remove
                make_type::keyset(reason::none(), make_type::arraykey(reason::none())),
                // We don't put null here because we want to exclude ?Foo.
                // as_mut(null) itself is allowed by the Tprim above
            ];
            // Make sure that a primitive *could* be this type by intersecting all primitives and subtyping.
            let union = make_type::union(reason::none(), primitive_types);
            !typing_subtype::is_type_disjoint(env, &ty, &union)
        }
    }
}

/// Get all possible data sources for the given expression.
fn get_data_srcs_from_expr(env: &Env, ctx: &Ctx, Expr(tp, _, te): &tast::Expr) -> DataSourceSet {
    let is_immutable_ty = has_no_object_ref_ty(env, &SSet::new(), tp);
    let convert_ref_to_val = |srcs: DataSourceSet| {
        srcs.into_iter()
            .map(|src| match src {
                DataSource::GlobalReference(s) => DataSource::GlobalValue(s),
                s => s,
            })
            .collect::<DataSourceSet>()
    };
    // For a collection (Varray, ValCollection and List) that uses a list of expressions
    // (e.g. vec[$a, $b] uses the list [$a; $b]), the function get_data_srcs_of_expr_list
    // gets the data source for each expression in the list and do the union; specially,
    // if the list is empty (e.g. vec[]), the data source is NullOrEmpty.
    let get_data_srcs_of_expr_list = |list: &[tast::Expr]| {
        if list.is_empty() {
            data_source_set_singleton(DataSource::NullOrEmpty)
        } else {
            list.iter().fold(DataSourceSet::new(), |cur_src_set, e| {
                data_source_set_union(cur_src_set, get_data_srcs_from_expr(env, ctx, e))
            })
        }
    };
    // For a collection (Shape and KeyValCollection) that uses a list of expression
    // pairs (e.g. dict[0 => $a, 1 => $b] uses the list [(0, $a); (1, $b)]), the function
    // get_data_srcs_of_pair_expr_list gets the data source for the 2nd expression in each
    // pair and do the union; specially, return NullOrEmpty if the list is empty (e.g. dict[]).
    let get_data_srcs_of_pair_expr_list = |list: Vec<&tast::Expr>| {
        if list.is_empty() {
            data_source_set_singleton(DataSource::NullOrEmpty)
        } else {
            list.into_iter()
                .fold(DataSourceSet::new(), |cur_src_set, e| {
                    data_source_set_union(cur_src_set, get_data_srcs_from_expr(env, ctx, e))
                })
        }
    };
    // `DataSourceSet.union (f e1) (f e2)`: the arguments are evaluated right
    // to left, as in OCaml.
    let union_of = |e1: &tast::Expr, e2: &tast::Expr| {
        let s2 = get_data_srcs_from_expr(env, ctx, e2);
        let s1 = get_data_srcs_from_expr(env, ctx, e1);
        data_source_set_union(s1, s2)
    };
    match te {
        Expr_::ClassGet(cg) if matches!(cg.2, PropOrMethod::IsProp) => {
            let (class_id, expr, _) = &**cg;
            // Static variables annotated with <<__SafeForGlobalAccessCheck>> are
            // treated as non-sensitive.
            let class_elts = get_static_prop_elts(env, class_id, expr);
            if class_elts
                .iter()
                .any(typing_defs::get_ce_safe_global_variable)
            {
                data_source_set_singleton(DataSource::NonSensitive)
            } else {
                let expr_str = print_global_expr(env, te);
                if is_immutable_ty {
                    data_source_set_singleton(DataSource::GlobalValue(expr_str))
                } else {
                    data_source_set_singleton(DataSource::GlobalReference(expr_str))
                }
            }
        }
        Expr_::Lvar(lid) => {
            let Lid(_, id) = &**lid;
            let tbl = ctx.var_data_src_tbl.borrow();
            let id = local_id::to_string(id);
            if tbl.contains_key(&id) {
                tbl.get(&id).unwrap().clone()
            } else {
                data_source_set_singleton(DataSource::Unknown)
            }
        }
        Expr_::Call(call) => {
            let caller = &call.func;
            let Expr(_, _, func_expr) = caller;
            let args = &call.args;
            match check_func_is_memoized(caller, env) {
                Some(func_name) => {
                    // If the called function is memoized, then its return is global.
                    if is_immutable_ty {
                        data_source_set_singleton(DataSource::GlobalValue(func_name))
                    } else {
                        data_source_set_singleton(DataSource::GlobalReference(func_name))
                    }
                }
                None => {
                    // Otherwise, the function call is treated as a black boxes, except
                    // for some special function (i.e. idx), the data source of its return
                    // is assumed to be the same as its first parameter.
                    match func_expr {
                        Expr_::Id(id) if mem(&id.1, SRC_FROM_FIRST_PARA_FUNC_IDS) => {
                            match args.as_slice() {
                                [para_expr, ..] => get_data_srcs_from_expr(
                                    env,
                                    ctx,
                                    aast_utils::arg_to_expr(para_expr),
                                ),
                                [] => data_source_set_singleton(DataSource::Unknown),
                            }
                        }
                        Expr_::Id(id) => {
                            let func_id = &id.1;
                            if mem(func_id, SAFE_FUNC_IDS) {
                                data_source_set_singleton(DataSource::NonSensitive)
                            } else if mem(func_id, SRC_FROM_PARA_FUNC_IDS) {
                                args.iter()
                                    .fold(DataSourceSet::new(), |cur_src_set, para_expr| {
                                        data_source_set_union(
                                            cur_src_set,
                                            get_data_srcs_from_expr(
                                                env,
                                                ctx,
                                                aast_utils::arg_to_expr(para_expr),
                                            ),
                                        )
                                    })
                            } else {
                                data_source_set_singleton(DataSource::Unknown)
                            }
                        }
                        Expr_::ClassConst(cc) => match &cc.0 {
                            ClassId(_, _, ClassId_::CI(Id(_, class_name))) => {
                                // A static method call is safe if the class name is in "safe_class_ids",
                                // or it starts with "SV_" (i.e. it's a site var).
                                let is_class_safe = mem(class_name, SAFE_CLASS_IDS)
                                    || class_name.starts_with("\\SV_");
                                if is_class_safe {
                                    data_source_set_singleton(DataSource::NonSensitive)
                                } else {
                                    data_source_set_singleton(DataSource::Unknown)
                                }
                            }
                            _ => data_source_set_singleton(DataSource::Unknown),
                        },
                        _ => data_source_set_singleton(DataSource::Unknown),
                    }
                }
            }
        }
        Expr_::Shape(tpl) => get_data_srcs_of_pair_expr_list(
            tpl.iter()
                .map(|field| match field {
                    oxidized::aast::ShapeExprField::SFField(_, e)
                    | oxidized::aast::ShapeExprField::SFSplat(e) => e,
                })
                .collect(),
        ),
        Expr_::ValCollection(vc) => get_data_srcs_of_expr_list(&vc.2),
        Expr_::KeyValCollection(kvc) => {
            get_data_srcs_of_pair_expr_list(kvc.2.iter().map(|tast_field| &tast_field.1).collect())
        }
        Expr_::Null => data_source_set_singleton(DataSource::NullOrEmpty),
        Expr_::Clone(e) => get_data_srcs_from_expr(env, ctx, e),
        Expr_::ArrayGet(ag) => get_data_srcs_from_expr(env, ctx, &ag.0),
        Expr_::ObjGet(og) if matches!(og.3, PropOrMethod::IsProp) => {
            let obj_expr = &og.0;
            let obj_data_srcs = get_data_srcs_from_expr(env, ctx, obj_expr);
            if is_immutable_ty {
                convert_ref_to_val(obj_data_srcs)
            } else {
                obj_data_srcs
            }
        }
        Expr_::ClassConst(_) => data_source_set_singleton(DataSource::NonSensitive),
        Expr_::Await(e) => get_data_srcs_from_expr(env, ctx, e),
        Expr_::Delay(e) => get_data_srcs_from_expr(env, ctx, e),
        Expr_::ReadonlyExpr(e) => get_data_srcs_from_expr(env, ctx, e),
        Expr_::Tuple(el) | Expr_::List(el) => get_data_srcs_of_expr_list(el),
        Expr_::Cast(c) => get_data_srcs_from_expr(env, ctx, &c.1),
        Expr_::Unop(u) => get_data_srcs_from_expr(env, ctx, &u.1),
        Expr_::Binop(b) => union_of(&b.lhs, &b.rhs),
        Expr_::Assign(a) => union_of(&a.0, &a.2),
        Expr_::Pipe(p) => get_data_srcs_from_expr(env, ctx, &p.2),
        Expr_::Eif(eif) => {
            let (_, e1, e2) = &**eif;
            // The arguments of `DataSourceSet.union` are evaluated right to
            // left, as in OCaml.
            let s2 = get_data_srcs_from_expr(env, ctx, e2);
            let s1 = match e1 {
                Some(e) => get_data_srcs_from_expr(env, ctx, e),
                None => DataSourceSet::new(),
            };
            data_source_set_union(s1, s2)
        }
        Expr_::As(as_) => get_data_srcs_from_expr(env, ctx, &as_.expr),
        Expr_::Upcast(u) => get_data_srcs_from_expr(env, ctx, &u.0),
        Expr_::Pair(p) => union_of(&p.1, &p.2),
        Expr_::True
        | Expr_::False
        | Expr_::Int(_)
        | Expr_::Float(_)
        | Expr_::String(_)
        | Expr_::String2(_)
        | Expr_::PrefixedString(_)
        | Expr_::Nameof(_)
        | Expr_::ExpressionTree(_) => data_source_set_singleton(DataSource::Literal),
        Expr_::This
        | Expr_::Omitted
        | Expr_::Id(_)
        | Expr_::Dollardollar(_)
        | Expr_::ObjGet(_)
        | Expr_::ClassGet(_)
        | Expr_::FunctionPointer(_)
        | Expr_::Yield(_)
        | Expr_::Is(_)
        | Expr_::New(_)
        | Expr_::Efun(_)
        | Expr_::Lfun(_)
        | Expr_::Xml(_)
        | Expr_::Import(_)
        | Expr_::Collection(_)
        | Expr_::Lplaceholder(_)
        | Expr_::MethodCaller(_)
        | Expr_::ETSplice(_)
        | Expr_::EnumClassLabel(_)
        | Expr_::Hole(_)
        | Expr_::Invalid(_)
        | Expr_::Package(_)
        | Expr_::DestructureShape(_)
        | Expr_::DestructureTuple(_) => data_source_set_singleton(DataSource::Unknown),
    }
}

/// Get the global variable names from the given expression's data sources.
/// By default, include_immutable is true, and we return both GlobalReference
/// and GlobalValue; otherwise, we return only GlobalReference. If no such
/// global variable exists, None is returned.
fn get_global_vars_from_expr(
    include_immutable: Option<bool>,
    env: &Env,
    ctx: &Ctx,
    expr: &tast::Expr,
) -> Option<SSet> {
    let include_immutable = include_immutable.unwrap_or(true);
    let is_src_global = |src: &DataSource| match src {
        DataSource::GlobalReference(_) => true,
        DataSource::GlobalValue(_) => include_immutable,
        _ => false,
    };
    let print_src = |src: &DataSource| match src {
        DataSource::GlobalReference(str) | DataSource::GlobalValue(str) => str.clone(),
        s => show_data_source(s),
    };
    let data_srcs = get_data_srcs_from_expr(env, ctx, expr);
    let global_srcs: DataSourceSet = data_srcs.into_iter().filter(is_src_global).collect();
    if global_srcs.is_empty() {
        None
    } else {
        Some(
            global_srcs
                .iter()
                .fold(SSet::new(), |s, src| s.update(print_src(src))),
        )
    }
}

/// Given an expression that appears on LHS of an assignment,
/// this method gets the set of variables whose value may be assigned.
fn get_vars_in_expr(vars: &mut SSet, Expr(_, _, te): &tast::Expr) {
    match te {
        Expr_::Lvar(lid) => {
            let Lid(_, id) = &**lid;
            vars.insert(local_id::to_string(id));
        }
        Expr_::ObjGet(og) if matches!(og.3, PropOrMethod::IsProp) => get_vars_in_expr(vars, &og.0),
        Expr_::ArrayGet(ag) => get_vars_in_expr(vars, &ag.0),
        Expr_::ReadonlyExpr(e) => get_vars_in_expr(vars, e),
        Expr_::List(el) => el.iter().for_each(|e| get_vars_in_expr(vars, e)),
        _ => {}
    }
}

/// Suppose te is on LHS of an assignment, check if we can write to global variables
/// by accessing either directly static variables or an object's properties.
fn has_global_write_access(Expr(_, _, te): &tast::Expr) -> bool {
    match te {
        Expr_::ClassGet(cg) if matches!(cg.2, PropOrMethod::IsProp) => true,
        Expr_::ObjGet(og) if matches!(og.3, PropOrMethod::IsProp) => true,
        Expr_::List(el) => el.iter().any(has_global_write_access),
        Expr_::Lvar(_) | Expr_::ReadonlyExpr(_) | Expr_::ArrayGet(_) | _ => false,
    }
}

/// `(env, (ctx, fun_name))`
type Context = (Env, (Rc<Ctx>, String));

/// Run `visit` with `ctx` as the `ctx` of the state, then restore it.
fn with_ctx(
    c: &mut Context,
    ctx: &Rc<Ctx>,
    visit: impl FnOnce(&mut Context) -> Result<(), ()>,
) -> Result<(), ()> {
    let saved = std::mem::replace(&mut (c.1).0, Rc::clone(ctx));
    let result = visit(c);
    (c.1).0 = saved;
    result
}

/// `{ var_data_src_tbl = ref (Hashtbl.copy !(ctx.var_data_src_tbl));
///    null_global_var_set = ref !(ctx.null_global_var_set) }`
fn copy_ctx(ctx: &Ctx) -> Rc<Ctx> {
    // The fields of the record are evaluated right to left, as in OCaml.
    let null_global_var_set = ctx.null_global_var_set.borrow().clone();
    let var_data_src_tbl = ctx.var_data_src_tbl.borrow().clone();
    Rc::new(Ctx {
        var_data_src_tbl: RefCell::new(var_data_src_tbl),
        null_global_var_set: RefCell::new(null_global_var_set),
    })
}

/// `visitor`
struct GlobalVisitor;

fn visitor() -> GlobalVisitor {
    GlobalVisitor
}

impl<'a> tast_visitor::IterWithState<'a, (Rc<Ctx>, String)> for GlobalVisitor {}

impl<'a> Visitor<'a> for GlobalVisitor {
    type Params = tast_visitor::StateParams<(Rc<Ctx>, String)>;

    fn object(&mut self) -> &mut dyn Visitor<'a, Params = Self::Params> {
        self
    }

    crate::tast_visitor::iter_with_state_methods!('a; expr_, class_var, expression_tree);

    fn visit_method_(&mut self, c: &mut Context, m: &'a tast::Method_) -> Result<(), ()> {
        {
            let ctx = &(c.1).0;
            ctx.var_data_src_tbl.borrow_mut().clear();
            *ctx.null_global_var_set.borrow_mut() = SSet::new();
        }
        // `super#on_method_`
        tast_visitor::iter_with_state::on_method_(self, c, m)
    }

    fn visit_fun_def(&mut self, c: &mut Context, f: &'a tast::FunDef) -> Result<(), ()> {
        {
            let ctx = &(c.1).0;
            ctx.var_data_src_tbl.borrow_mut().clear();
            *ctx.null_global_var_set.borrow_mut() = SSet::new();
        }
        // `super#on_fun_def`
        f.recurse(c, self)
    }

    fn visit_fun_(&mut self, c: &mut Context, f: &'a tast::Fun_) -> Result<(), ()> {
        let ctx = Rc::clone(&(c.1).0);
        let var_data_src_tbl_cpy = ctx.var_data_src_tbl.borrow().clone();
        let null_global_var_set_cpy = ctx.null_global_var_set.borrow().clone();
        // `super#on_fun_`
        let result = tast_visitor::iter_with_state::on_fun_(self, c, f);
        *ctx.var_data_src_tbl.borrow_mut() = var_data_src_tbl_cpy;
        *ctx.null_global_var_set.borrow_mut() = null_global_var_set_cpy;
        result
    }

    fn visit_stmt_(&mut self, c: &mut Context, s: &'a tast::Stmt_) -> Result<(), ()> {
        let ctx = Rc::clone(&(c.1).0);
        match s {
            Stmt_::If(if_) => {
                let (cond_expr_, b1, b2) = &**if_;
                let Expr(_, _, cond) = cond_expr_;
                // Make a copy of null_global_var_set, and reset afterwards.
                let null_global_var_set_cpy = ctx.null_global_var_set.borrow().clone();
                let ctx_else_branch = copy_ctx(&ctx);
                // From the condition, we get the expression whose value is null in one brach
                // (true represents the if branch, while false represents the else branch).
                let nullable_expr_in_cond_opt: Option<(&tast::Expr, bool)> = match cond {
                    // For the condition of format "expr is null", "expr === null" or "expr == null",
                    // return expr and true (i.e. if branch).
                    Expr_::Is(is) if matches!(&is.1, Hint(_, h) if matches!(&**h, Hint_::Hprim(Tprim::Tnull))) => {
                        Some((&is.0, true))
                    }
                    Expr_::Binop(b)
                        if matches!(b.bop, Bop::Eqeqeq | Bop::Eqeq)
                            && matches!(&b.rhs, Expr(_, _, Expr_::Null)) =>
                    {
                        Some((&b.lhs, true))
                    }
                    // For the condition of format "!C\contains_key(expr, $key)" where expr shall be a
                    // dictionary, return expr and true (i.e. if branch).
                    // (No other case matches a `Unop`.)
                    Expr_::Unop(u) => match &**u {
                        (Uop::Unot, Expr(_, _, Expr_::Call(call)))
                            if matches!(&call.func, Expr(_, _, Expr_::Id(id))
                                if mem(&id.1, CHECK_NON_NULL_FUNC_IDS)) =>
                        {
                            match call.args.as_slice() {
                                [] => None,
                                [para_expr, ..] => Some((aast_utils::arg_to_expr(para_expr), true)),
                            }
                        }
                        _ => None,
                    },
                    // For the condition of format "expr is nonnull", "expr !== null" or "expr != null",
                    // return expr and false (i.e. else branch).
                    Expr_::Is(is) if matches!(&is.1, Hint(_, h) if matches!(&**h, Hint_::Hnonnull)) => {
                        Some((&is.0, false))
                    }
                    Expr_::Binop(b)
                        if matches!(b.bop, Bop::Diff | Bop::Diff2)
                            && matches!(&b.rhs, Expr(_, _, Expr_::Null)) =>
                    {
                        Some((&b.lhs, false))
                    }
                    // For the condition of format "C\contains_key(expr, $key)" where expr shall be a
                    // dictionary, return expr and false (i.e. else branch).
                    Expr_::Call(call)
                        if matches!(&call.func, Expr(_, _, Expr_::Id(id))
                            if mem(&id.1, CHECK_NON_NULL_FUNC_IDS)) =>
                    {
                        match call.args.as_slice() {
                            [] => None,
                            [para_expr, ..] => Some((aast_utils::arg_to_expr(para_expr), false)),
                        }
                    }
                    _ => None,
                };
                match nullable_expr_in_cond_opt {
                    None => {}
                    Some((nullable_expr, if_branch)) => {
                        let nullable_global_vars_opt =
                            get_global_vars_from_expr(None, &c.0, &ctx, nullable_expr);
                        // Add nullable global variables to null_global_var_set of the right branch.
                        match (nullable_global_vars_opt, if_branch) {
                            (None, _) => {}
                            (Some(vars), true) => {
                                let mut set = ctx.null_global_var_set.borrow_mut();
                                *set = set.clone().union(vars);
                            }
                            (Some(vars), false) => {
                                let mut set = ctx_else_branch.null_global_var_set.borrow_mut();
                                *set = set.clone().union(vars);
                            }
                        }
                    }
                }
                // Check the condition expression and report global reads/writes if any.
                // For example, a global read is reported if a global varialbe is directly used;
                // a global write is reported if a global variable is passed to a function call
                // (which is very likely to happen) or it is directly mutated inside the condition
                // (which is uncommon but possible).
                cond_expr_.recurse(c, self)?;
                // Check two branches separately, then merge the table of global variables
                // and reset the set of nullable variables.
                b1.recurse(c, self)?;
                with_ctx(c, &ctx_else_branch, |c| b2.recurse(c, self))?;
                merge_var_data_srcs_tbls(
                    &mut ctx.var_data_src_tbl.borrow_mut(),
                    &ctx_else_branch.var_data_src_tbl.borrow(),
                );
                *ctx.null_global_var_set.borrow_mut() = null_global_var_set_cpy;
                Ok(())
            }
            Stmt_::Do(_) | Stmt_::While(_) | Stmt_::For(_) | Stmt_::Foreach(_) => {
                let b = match s {
                    Stmt_::Do(x) => &x.0,
                    Stmt_::While(x) => &x.1,
                    Stmt_::For(x) => &x.3,
                    Stmt_::Foreach(x) => &x.2,
                    _ => panic!("Global_access_check: not a loop"),
                };
                s.recurse(c, self)?;
                // Iterate the block and update the set of global varialbes until
                // no new global variable is found
                let ctx_cpy = copy_ctx(&ctx);
                let mut ctx_len = get_tbl_total_cardinal(&ctx.var_data_src_tbl.borrow());
                let mut has_context_change = true;
                // Continue the loop until no more data sources are found.
                while has_context_change {
                    with_ctx(c, &ctx_cpy, |c| b.recurse(c, self))?;
                    merge_var_data_srcs_tbls(
                        &mut ctx.var_data_src_tbl.borrow_mut(),
                        &ctx_cpy.var_data_src_tbl.borrow(),
                    );
                    let new_ctx_tbl_cardinal =
                        get_tbl_total_cardinal(&ctx.var_data_src_tbl.borrow());
                    if new_ctx_tbl_cardinal != ctx_len {
                        ctx_len = new_ctx_tbl_cardinal
                    } else {
                        has_context_change = false
                    }
                }
                Ok(())
            }
            Stmt_::Return(r) => {
                match &**r {
                    Some(e) => {
                        let Expr(ty, p, _) = e;
                        match get_global_vars_from_expr(Some(false), &c.0, &ctx, e) {
                            Some(global_set) => raise_global_access_error(
                                p,
                                &(c.1).1,
                                &print_ty(&c.0, ty),
                                &global_set,
                                &GlobalAccessPatternSet::from([GlobalAccessPattern::NoPattern]),
                                GlobalAccessCheck::PossibleGlobalWriteViaFunctionCall,
                            ),
                            None => {}
                        }
                    }
                    None => {}
                }
                s.recurse(c, self)
            }
            _ => s.recurse(c, self),
        }
    }

    fn visit_expr(&mut self, c: &mut Context, te: &'a tast::Expr) -> Result<(), ()> {
        let Expr(ty, p, e) = te;
        let ctx = Rc::clone(&(c.1).0);
        let fun_name = (c.1).1.clone();
        match e {
            // For the case where the expression is directly a static variable or a memoized
            // function, and we report a global read. Notice that if the expression is on
            // the LHS of an assignment, we will not run on_expr on it, hence no global
            // reads would be reported; similarly, for the unary operation like "Foo::$prop++",
            // we don't report a global read.
            Expr_::ClassGet(cg) if matches!(cg.2, PropOrMethod::IsProp) => {
                let env = &c.0;
                let (class_id, expr, _) = &**cg;
                // Ignore static variables annotated with <<__SafeForGlobalAccessCheck>>
                let class_elts = get_static_prop_elts(env, class_id, expr);
                let is_annotated_safe = class_elts
                    .iter()
                    .any(typing_defs::get_ce_safe_global_variable);
                if !is_annotated_safe {
                    let expr_str = print_global_expr(env, e);
                    let ty_str = print_ty(env, ty);
                    raise_global_access_error(
                        p,
                        &fun_name,
                        &ty_str,
                        &SSet::unit(expr_str),
                        &GlobalAccessPatternSet::from([GlobalAccessPattern::NoPattern]),
                        GlobalAccessCheck::DefiniteGlobalRead,
                    )
                }
                Ok(())
            }
            Expr_::Call(call) => {
                let env = &c.0;
                let func_expr = &call.func;
                let Expr(func_ty, _, _) = func_expr;
                let args = &call.args;
                // First check if the called functions is from super globals.
                let is_super_global_call = check_super_global_method(e, env, &fun_name);
                if !is_super_global_call {
                    // If not super global, then check if the function is memoized.
                    let func_ty_str = print_ty(env, func_ty);
                    match check_func_is_memoized(func_expr, env) {
                        Some(memoized_func_name) => raise_global_access_error(
                            p,
                            &fun_name,
                            &func_ty_str,
                            &SSet::unit(memoized_func_name),
                            &GlobalAccessPatternSet::from([GlobalAccessPattern::NoPattern]),
                            GlobalAccessCheck::DefiniteGlobalRead,
                        ),
                        None => {}
                    }
                }
                // Lastly, check if a global variable is used as the parameter.
                for arg in args {
                    let (ty, pos, e_global_opt) = match arg {
                        Argument::Ainout(_, expr) => {
                            let Expr(ty, pos, _) = expr;
                            (ty, pos, get_global_vars_from_expr(None, env, &ctx, expr))
                        }
                        Argument::Anormal(expr) => {
                            let Expr(ty, pos, _) = expr;
                            (
                                ty,
                                pos,
                                get_global_vars_from_expr(Some(false), env, &ctx, expr),
                            )
                        }
                        Argument::Anamed(_, expr) => {
                            let Expr(ty, pos, _) = expr;
                            (
                                ty,
                                pos,
                                get_global_vars_from_expr(Some(false), env, &ctx, expr),
                            )
                        }
                    };
                    if e_global_opt.is_some() {
                        raise_global_access_error(
                            pos,
                            &fun_name,
                            &print_ty(env, ty),
                            &e_global_opt.unwrap(),
                            &GlobalAccessPatternSet::from([GlobalAccessPattern::NoPattern]),
                            GlobalAccessCheck::PossibleGlobalWriteViaFunctionCall,
                        )
                    }
                }
                te.recurse(c, self)
            }
            Expr_::Assign(a) => {
                let (lhs, bop_opt, rhs) = &**a;
                self.visit_expr(c, rhs)?;
                let env = &c.0;
                let re_ty = print_ty(env, tast::get_type(rhs));
                let le_global_opt = get_global_vars_from_expr(None, env, &ctx, lhs);
                // When write to a global variable whose value is null or does not exist:
                // if the written variable is in a collection (e.g. $global[$key] = $val),
                // then it's asumed to be caching; otherwise, it's a singleton.
                let singleton_or_caching = match lhs {
                    Expr(_, _, Expr_::ArrayGet(_)) => GlobalAccessPattern::Caching,
                    _ => GlobalAccessPattern::Singleton,
                };
                let le_pattern = match (&le_global_opt, bop_opt) {
                    (None, _) => GlobalAccessPattern::NoPattern,
                    (Some(_), Some(Bop::QuestionQuestion)) => singleton_or_caching,
                    (Some(le_global), _) => {
                        let null_global_var_set = ctx.null_global_var_set.borrow();
                        if le_global.iter().any(|v| null_global_var_set.contains(v)) {
                            singleton_or_caching
                        } else {
                            GlobalAccessPattern::NoPattern
                        }
                    }
                };
                let re_data_srcs = get_data_srcs_from_expr(env, &ctx, rhs);
                let re_patterns = get_patterns_from_written_data_srcs(&re_data_srcs);
                // Distinguish directly writing to static variables from writing to a variable
                // that has references to static variables.
                if is_expr_static(env, lhs) && le_global_opt.is_some() {
                    let mut patterns = re_patterns;
                    patterns.insert(le_pattern);
                    raise_global_access_error(
                        p,
                        &fun_name,
                        &re_ty,
                        le_global_opt.as_ref().unwrap(),
                        &patterns,
                        GlobalAccessCheck::DefiniteGlobalWrite,
                    )
                } else {
                    let mut vars_in_le = SSet::new();
                    get_vars_in_expr(&mut vars_in_le, lhs);
                    if has_global_write_access(lhs) {
                        if le_global_opt.is_some() {
                            let mut patterns = re_patterns;
                            patterns.insert(le_pattern);
                            raise_global_access_error(
                                p,
                                &fun_name,
                                &re_ty,
                                le_global_opt.as_ref().unwrap(),
                                &patterns,
                                GlobalAccessCheck::PossibleGlobalWriteViaReference,
                            );
                        }
                        let mut tbl = ctx.var_data_src_tbl.borrow_mut();
                        for v in vars_in_le.iter() {
                            add_var_data_srcs_to_tbl(&mut tbl, v, &re_data_srcs)
                        }
                    } else {
                        let mut tbl = ctx.var_data_src_tbl.borrow_mut();
                        for v in vars_in_le.iter() {
                            replace_var_data_srcs_in_tbl(&mut tbl, v, &re_data_srcs)
                        }
                    }
                }
                rhs.recurse(c, self)
                // add_var_refs_to_tbl !(ctx.global_var_refs_tbl) !vars_in_le
            }
            Expr_::Unop(u) => {
                let (op, e) = &**u;
                let env = &c.0;
                let e_global_opt = get_global_vars_from_expr(None, env, &ctx, e);
                if e_global_opt.is_some() {
                    let e_global = e_global_opt.unwrap();
                    let e_ty = print_ty(env, tast::get_type(e));
                    match op {
                        Uop::Uincr | Uop::Udecr | Uop::Upincr | Uop::Updecr => {
                            // Distinguish directly writing to static variables from writing to a variable that has references to static variables.
                            if is_expr_static(env, e) {
                                raise_global_access_error(
                                    p,
                                    &fun_name,
                                    &e_ty,
                                    &e_global,
                                    &GlobalAccessPatternSet::from([
                                        GlobalAccessPattern::CounterIncrement,
                                    ]),
                                    GlobalAccessCheck::DefiniteGlobalWrite,
                                )
                            } else if has_global_write_access(e) {
                                raise_global_access_error(
                                    p,
                                    &fun_name,
                                    &e_ty,
                                    &e_global,
                                    &GlobalAccessPatternSet::from([
                                        GlobalAccessPattern::CounterIncrement,
                                    ]),
                                    GlobalAccessCheck::PossibleGlobalWriteViaReference,
                                )
                            }
                            Ok(())
                        }
                        _ => e.recurse(c, self),
                    }
                } else {
                    Ok(())
                }
            }
            Expr_::New(n) => {
                let el = &n.2;
                let env = &c.0;
                for arg in el {
                    let expr = aast_utils::arg_to_expr(arg);
                    let Expr(ty, pos, _) = expr;
                    let e_global_opt = get_global_vars_from_expr(Some(false), env, &ctx, expr);
                    if e_global_opt.is_some() {
                        raise_global_access_error(
                            pos,
                            &fun_name,
                            &print_ty(env, ty),
                            &e_global_opt.unwrap(),
                            &GlobalAccessPatternSet::from([GlobalAccessPattern::NoPattern]),
                            GlobalAccessCheck::PossibleGlobalWriteViaFunctionCall,
                        )
                    }
                }
                te.recurse(c, self)
            }
            _ => te.recurse(c, self),
        }
    }
}

/// `handler`
struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_method_(&mut self, env: &Env, m: &'a tast::Method_) {
        let class_name = tast_env::get_self_id(env);
        let Id(_, method_name) = &m.name;
        let full_name = match class_name {
            Some(s) => s + "::" + method_name,
            _ => method_name.clone(),
        };
        // Class name starts with '\' or ';'
        let full_name = string_sub_from_1(&full_name);
        let ctx = CURRENT_CTX.with(Rc::clone);
        let _ = visitor().visit_method_(&mut (env.clone(), (ctx, full_name)), m);
    }

    fn at_fun_def(&mut self, env: &Env, f: &'a tast::FunDef) {
        let Id(_, function_name) = &f.name;
        // Function name starts with '\'
        let function_name = string_sub_from_1(function_name);
        let ctx = CURRENT_CTX.with(Rc::clone);
        let _ = visitor().visit_fun_def(&mut (env.clone(), (ctx, function_name)), f);
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(Handler)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn data_sources_are_ordered_as_their_constructors() {
        let srcs: DataSourceSet = [
            DataSource::Unknown,
            DataSource::Literal,
            DataSource::GlobalValue("a".to_string()),
            DataSource::GlobalReference("b".to_string()),
            DataSource::NullOrEmpty,
            DataSource::GlobalReference("a".to_string()),
            DataSource::NonSensitive,
        ]
        .into_iter()
        .collect();
        assert_eq!(
            srcs.into_iter().collect::<Vec<_>>(),
            vec![
                DataSource::GlobalReference("a".to_string()),
                DataSource::GlobalReference("b".to_string()),
                DataSource::GlobalValue("a".to_string()),
                DataSource::NullOrEmpty,
                DataSource::Literal,
                DataSource::NonSensitive,
                DataSource::Unknown,
            ]
        );
    }

    #[test]
    fn patterns_of_written_data() {
        let srcs: DataSourceSet = [
            DataSource::Literal,
            DataSource::GlobalValue("A::$x".to_string()),
            DataSource::NullOrEmpty,
            DataSource::GlobalReference("B::$y".to_string()),
        ]
        .into_iter()
        .collect();
        assert_eq!(
            get_patterns_from_written_data_srcs(&srcs)
                .into_iter()
                .collect::<Vec<_>>(),
            vec![
                GlobalAccessPattern::WriteEmptyOrNull,
                GlobalAccessPattern::WriteLiteral,
                GlobalAccessPattern::WriteGlobalToGlobal,
            ]
        );
        let mut with_unknown = srcs;
        with_unknown.insert(DataSource::Unknown);
        assert!(get_patterns_from_written_data_srcs(&with_unknown).is_empty());
    }

    #[test]
    fn shows() {
        assert_eq!(
            show_global_access_pattern(GlobalAccessPattern::CounterIncrement),
            "CounterIncrement"
        );
        assert_eq!(
            show_data_source(&DataSource::GlobalReference("a\"b\\c\n\u{e9}".to_string())),
            "(Global_access_check.GlobalReference \"a\\\"b\\\\c\\n\\195\\169\")"
        );
        assert_eq!(
            show_data_source(&DataSource::NullOrEmpty),
            "Global_access_check.NullOrEmpty"
        );
    }

    #[test]
    fn tables() {
        let mut tbl1: HashMap<String, DataSourceSet> = HashMap::new();
        add_var_data_srcs_to_tbl(
            &mut tbl1,
            "a",
            &data_source_set_singleton(DataSource::Literal),
        );
        add_var_data_srcs_to_tbl(
            &mut tbl1,
            "a",
            &data_source_set_singleton(DataSource::Unknown),
        );
        let mut tbl2: HashMap<String, DataSourceSet> = HashMap::new();
        replace_var_data_srcs_in_tbl(
            &mut tbl2,
            "a",
            &data_source_set_singleton(DataSource::NullOrEmpty),
        );
        replace_var_data_srcs_in_tbl(
            &mut tbl2,
            "b",
            &data_source_set_singleton(DataSource::Literal),
        );
        replace_var_data_srcs_in_tbl(
            &mut tbl2,
            "b",
            &data_source_set_singleton(DataSource::Unknown),
        );
        assert_eq!(get_tbl_total_cardinal(&tbl1), 2);
        assert_eq!(get_tbl_total_cardinal(&tbl2), 2);
        merge_var_data_srcs_tbls(&mut tbl1, &tbl2);
        assert_eq!(get_tbl_total_cardinal(&tbl1), 4);
        assert_eq!(tbl1["a"].len(), 3);
        assert_eq!(tbl1["b"], data_source_set_singleton(DataSource::Unknown));
    }

    #[test]
    fn sub_from_1() {
        assert_eq!(string_sub_from_1("\\Foo::bar"), "Foo::bar");
        assert_eq!(string_sub_from_1("f"), "");
    }

    #[test]
    #[should_panic(expected = "String.sub / Bytes.sub")]
    fn sub_from_1_of_empty() {
        string_sub_from_1("");
    }
}
