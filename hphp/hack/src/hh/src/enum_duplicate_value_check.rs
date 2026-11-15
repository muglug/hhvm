// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/tast_check/enum_duplicate_value_check.ml`.
//! See `hh/PORTING.md`.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use oxidized::ast_defs::Id;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use pos::ToOxidized;

use crate::ast_defs;
use crate::decl_entry;
use crate::folded_class as cls;
use crate::pos_or_decl;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::typing_defs::ClassConst;
use crate::typing_defs::const_value;
use crate::typing_error;
use crate::typing_error::primary::T as Primary;
use crate::utils;

/// `origin_opts_out`: the function that `memoized_origin_opts_out` returns.
type OriginOptsOut = Rc<dyn Fn(&str) -> bool>;

/// A predicate on a class constant (`is_local`, `is_own_uncheckable`,
/// `is_from_opted_out_origin`).
type CcPredicate = Rc<dyn Fn(&ClassConst) -> bool>;

/// Whether the named enum carries `<<__AllowUncheckedEnumValues>>`.
fn memoized_origin_opts_out(env: &Env) -> OriginOptsOut {
    let env = env.clone();
    let cache: RefCell<HashMap<String, bool>> = RefCell::new(HashMap::new());
    Rc::new(move |origin: &str| {
        // `Hashtbl.find_or_add cache origin ~default`
        let found = cache.borrow().get(origin).copied();
        match found {
            Some(b) => b,
            None => {
                let b = match tast_env::get_class(&env, origin) {
                    decl_entry::T::Found(ocls) => cls::allow_unchecked_enum_values(&ocls),
                    decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => false,
                };
                cache.borrow_mut().insert(origin.to_string(), b);
                b
            }
        }
    })
}

/// Whether the members of [base] named by [targets] have concrete, pairwise
/// distinct values. Asking per named member, rather than about [base] as a
/// whole, keeps one unevaluable member from disqualifying every enum that
/// aliases it.
///
/// A target that is itself an access counts as uncheckable, so this never
/// follows alias chains. So does a target inherited from an opted-out enum,
/// which keeps `<<__AllowUncheckedEnumValues>>` downward-closed.
fn aliased_members_are_distinct(
    env: &Env,
    origin_opts_out: &OriginOptsOut,
    base: &str,
    targets: &[String],
) -> bool {
    match tast_env::get_class(env, base) {
        decl_entry::T::Found(bcls) if ast_defs::is_c_enum(cls::kind(&bcls)) => {
            let value_of = |target: &String| {
                match tast_env::get_const(env, &bcls, target) {
                    Some(cc)
                        if (!const_value::is_uncheckable(&cc.value))
                            && !origin_opts_out(cc.origin.as_str()) =>
                    {
                        // `CVLabel` stands for the aliased member's own name, not the
                        // aliasing member's.
                        Some(const_value::value_repr(target, &cc.value))
                    }
                    _ => None,
                }
            };
            // `Option.all (List.map targets ~f:value_of)`: every target is
            // looked at, before any `None` decides.
            let values: Vec<Option<String>> = targets.iter().map(value_of).collect();
            match values.into_iter().collect::<Option<Vec<String>>>() {
                None => false,
                Some(values) => !contains_dup(&values),
            }
        }
        _ => false,
    }
}

/// `List.contains_dup values ~compare:String.compare`
fn contains_dup(values: &[String]) -> bool {
    let mut sorted: Vec<&String> = values.iter().collect();
    sorted.sort();
    sorted.windows(2).any(|w| w[0] == w[1])
}

/// True when [accesses] are all `Base::X` on a single enum whose aliased members
/// have distinct concrete values -- i.e. this enum is a 1:1 relabeling of part of
/// [base], so it can't introduce duplicate values. [n_local] is the enum's own
/// (non-synthesized) member count; requiring [accesses] to cover all of them
/// means every member is such an access.
fn is_pure_alias_with_distinct_values(
    env: &Env,
    origin_opts_out: &OriginOptsOut,
    accesses: &[(String, String)],
    n_local: usize,
) -> bool {
    match accesses {
        [] => false,
        [(base, _), rest @ ..] => {
            let all_members_are_accesses = accesses.len() == n_local;
            let all_on_same_base = rest.iter().all(|(b, _)| b == base);
            all_members_are_accesses
                && all_on_same_base
                && aliased_members_are_distinct(
                    env,
                    origin_opts_out,
                    base,
                    &accesses
                        .iter()
                        .map(|(_, target)| target.clone())
                        .collect::<Vec<_>>(),
                )
        }
    }
}

/// Aliasing exemption: an enum with no `use` inclusions that is a 1:1 relabeling
/// of members of a single enum can't itself have duplicate values, so it needs no
/// opt-out and is exempt from the check.
fn is_alias_exempt(
    env: &Env,
    cls: &cls::T,
    consts: &[(String, ClassConst)],
    is_local: &CcPredicate,
    origin_opts_out: &OriginOptsOut,
) -> bool {
    let own_consts: Vec<&(String, ClassConst)> = consts
        .iter()
        .filter(|(_, cc)| is_local(cc) && !cc.is_synthesized)
        .collect();
    let accesses: Vec<(String, String)> = own_consts
        .iter()
        .filter_map(|(_, cc)| const_value::const_access_target(&cc.value))
        .collect();
    let n_local = own_consts.len();
    let has_no_includes = match cls::enum_type(cls) {
        None => false,
        Some(te) => te.includes.is_empty(),
    };
    has_no_includes && is_pure_alias_with_distinct_values(env, origin_opts_out, &accesses, n_local)
}

/// Cap on how many reasons we render in an "uncheckable" error. An enum that
/// `use`s many uncheckable enums could otherwise produce an unbounded list.
const MAX_REASONS: usize = 5;

/// The polymorphic variant `` [`Own of Pos_or_decl.t * string | `Used of string] ``
enum ReasonItem {
    Own(PosOrDecl, String),
    Used(String),
}

/// The enum can't be checked as a whole (one of its own values is unevaluable, or
/// it `use`s an enum that opted out), so emit a single Enum_uncheckable_value and
/// do NOT report duplicates -- a partial report would give a false sense of
/// safety. The human-readable reasons are built lazily only if the error is
/// rendered. [reasons] pairs the (capped) list of reasons with a count of how
/// many further reasons were omitted.
fn report_uncheckable_enum(
    env: &Env,
    enum_pos: &Pos,
    enum_decl_name: &str,
    is_own_uncheckable: &CcPredicate,
    is_from_opted_out_origin: &CcPredicate,
    consts: &[(String, ClassConst)],
) {
    let reasons = {
        let env = env.clone();
        let enum_pos = enum_pos.clone();
        let is_own_uncheckable = Rc::clone(is_own_uncheckable);
        let is_from_opted_out_origin = Rc::clone(is_from_opted_out_origin);
        let consts = consts.to_vec();
        typing_error::Lazy::new(move || {
            let own: Vec<ReasonItem> = consts
                .iter()
                .filter_map(|(member_name, cc)| {
                    // `Option.some_if`
                    if is_own_uncheckable(cc) {
                        Some(ReasonItem::Own(
                            cc.pos.clone().to_oxidized(),
                            member_name.clone(),
                        ))
                    } else {
                        None
                    }
                })
                .collect();
            let used: Vec<ReasonItem> = {
                let mut origins: Vec<String> = consts
                    .iter()
                    .filter_map(|(_, cc)| {
                        if is_from_opted_out_origin(cc) {
                            Some(cc.origin.as_str().to_string())
                        } else {
                            None
                        }
                    })
                    .collect();
                // `List.dedup_and_sort ~compare:String.compare`
                origins.sort();
                origins.dedup();
                origins.into_iter().map(ReasonItem::Used).collect()
            };
            let all: Vec<ReasonItem> = own.into_iter().chain(used).collect();
            let render = |r: &ReasonItem| match r {
                ReasonItem::Own(pos, member_name) => {
                    (pos.clone(), format!("`{}` cannot be checked", member_name))
                }
                ReasonItem::Used(origin) => {
                    // Point at the used enum's own declaration, not the enum being
                    // checked, so the reason directs the reader to the enum they need to
                    // fix or opt out.
                    let origin_pos = match tast_env::get_class(&env, origin) {
                        decl_entry::T::Found(ocls) => cls::pos(&ocls),
                        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {
                            pos_or_decl::of_raw_pos(enum_pos.clone())
                        }
                    };
                    (
                        origin_pos,
                        format!(
                            "it uses `{}`, which cannot be checked for duplicate values",
                            utils::strip_ns(origin)
                        ),
                    )
                }
            };
            // The components of the pair are evaluated right to left, as in
            // OCaml.
            let omitted = std::cmp::max(0, all.len() as isize - MAX_REASONS as isize);
            let rendered = all.iter().take(MAX_REASONS).map(render).collect();
            (rendered, omitted)
        })
    };
    tast_env::add_typing_error(
        &typing_error::primary(Primary::EnumUncheckableValue {
            pos: enum_pos.clone(),
            name: enum_decl_name.to_string(),
            reasons,
        }),
        env,
    )
}

/// The enum is fully checkable: flag duplicate values. The folded consts merge
/// `use`-included members, so one pass catches own, included, and cross-include
/// clashes. Maps each value to the first member that defines it; a later member
/// with the same value is a clash. An inherited `CVConstAccess` can reach here
/// (a local access would make the enum uncheckable and never get this far), so it
/// participates in duplicate detection via its `value_repr`.
fn report_duplicate_values(
    env: &Env,
    enum_pos: &Pos,
    is_local: &CcPredicate,
    consts: &[(String, ClassConst)],
) {
    let mut seen: HashMap<String, (String, ClassConst)> = HashMap::new();
    for (member_name, cc) in consts {
        if const_value::is_absent(&cc.value) {
        } else {
            let value = const_value::value_repr(member_name, &cc.value);
            match seen.get(&value) {
                None => {
                    seen.insert(value, (member_name.clone(), cc.clone()));
                }
                Some((prev_name, prev_cc)) => {
                    // A clash between two members inherited from the *same* enum is
                    // reported when that enum is checked, not again on every enum that
                    // uses it.
                    let both_inherited_same_origin =
                        (!is_local(cc)) && (!is_local(prev_cc)) && cc.origin == prev_cc.origin;
                    if !both_inherited_same_origin {
                        tast_env::add_typing_error(
                            &typing_error::primary(Primary::EnumDuplicateValue {
                                pos: enum_pos.clone(),
                                value,
                                member_name: member_name.clone(),
                                member_pos: cc.pos.clone().to_oxidized(),
                                prev_name: prev_name.clone(),
                                prev_pos: prev_cc.pos.clone().to_oxidized(),
                            }),
                            env,
                        )
                    }
                }
            }
        }
    }
}

/// `handler`
struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_class_(&mut self, env: &Env, c: &'a tast::Class_) {
        if ast_defs::is_c_enum(c.kind) {
            let Id(enum_pos, enum_name) = &c.name;
            match tast_env::get_class(env, enum_name) {
                decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {}
                // An enum carrying the opt-out attribute is exempt from the whole check
                // (read from the decl, so included enums are visible below); an opted-out
                // enum falls through to the no-op arm below.
                decl_entry::T::Found(cls) if !cls::allow_unchecked_enum_values(&cls) => {
                    let enum_decl_name = cls::name(&cls);
                    let is_local: CcPredicate = {
                        let enum_decl_name = enum_decl_name.clone();
                        Rc::new(move |cc: &ClassConst| cc.origin.as_str() == enum_decl_name)
                    };
                    let consts = tast_env::consts(env, &cls);
                    let origin_opts_out = memoized_origin_opts_out(env);
                    // A local member whose value can't be statically evaluated.
                    let is_own_uncheckable: CcPredicate = {
                        let is_local = Rc::clone(&is_local);
                        Rc::new(move |cc: &ClassConst| {
                            is_local(cc)
                                && (!cc.is_synthesized)
                                && const_value::is_uncheckable(&cc.value)
                        })
                    };
                    // A member inherited from an enum that opted out of the check. An
                    // inherited enum whose own values are uncheckable is flagged on its
                    // own definition and, once it opts out, is caught here -- so the
                    // opt-out check alone is sufficient for inherited members.
                    let is_from_opted_out_origin: CcPredicate = {
                        let is_local = Rc::clone(&is_local);
                        let origin_opts_out = Rc::clone(&origin_opts_out);
                        Rc::new(move |cc: &ClassConst| {
                            (!is_local(cc)) && origin_opts_out(cc.origin.as_str())
                        })
                    };
                    // Three-way dispatch: an alias-exempt enum can't have duplicates, so
                    // report nothing; an enum with an unevaluable or inherited opted-out
                    // value is reported uncheckable as a whole; otherwise scan its members
                    // for duplicate values.
                    if is_alias_exempt(env, &cls, &consts, &is_local, &origin_opts_out) {
                    } else if consts
                        .iter()
                        .any(|(_, cc)| is_own_uncheckable(cc) || is_from_opted_out_origin(cc))
                    {
                        report_uncheckable_enum(
                            env,
                            enum_pos,
                            &enum_decl_name,
                            &is_own_uncheckable,
                            &is_from_opted_out_origin,
                            &consts,
                        )
                    } else {
                        report_duplicate_values(env, enum_pos, &is_local, &consts)
                    }
                }
                decl_entry::T::Found(_) => {}
            }
        }
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(Handler)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dups() {
        let v = |l: &[&str]| l.iter().map(|s| s.to_string()).collect::<Vec<_>>();
        assert!(!contains_dup(&v(&[])));
        assert!(!contains_dup(&v(&["1", "\"a\"", "2"])));
        assert!(contains_dup(&v(&["2", "1", "\"a\"", "1"])));
    }
}
