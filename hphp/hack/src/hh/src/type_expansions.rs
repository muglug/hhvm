// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `type_expansions.ml`. See `hh/PORTING.md`.
//!
//! The list of expansions is a `crate::plist::List` kept in the order of the OCaml
//! list (the most recent expansion first): `Typing_defs.expand_env`, which
//! holds a [`T`], is copied at every `{ ety_env with ... }`, so the copy has to
//! be cheap.

use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;

use crate::typing_error;
use crate::typing_error::primary;
use crate::typing_error::reasons_callback;
use crate::typing_error::secondary;

/// `module Expandable`
pub mod expandable {
    /// `Expandable.t` (`[@@deriving eq]`: `PartialEq`)
    #[derive(Clone, Debug, PartialEq, Eq, Hash)]
    pub enum T {
        Enum(String),
        TypeAlias(String),
        TypeConstant {
            receiver_name: String,
            type_const_name: String,
        },
    }

    /// `[@@deriving eq]`
    pub fn equal(x: &T, y: &T) -> bool {
        x == y
    }

    pub fn to_string(t: &T) -> String {
        match t {
            T::Enum(x) | T::TypeAlias(x) => x.clone(),
            T::TypeConstant {
                receiver_name,
                type_const_name,
            } => format!("{}::{}", receiver_name, type_const_name),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Expansion {
    pub name: expandable::T,
    /// Position of the reference to the thing to expand.
    pub use_pos: PosOrDecl,
    /// Position of the definition of the type alias or type constant. Optionally populated.
    pub def_pos: Option<PosOrDecl>,
}

/// A list of the type defs and type access we have expanded thus far. Used
/// to prevent entering into a cycle when expanding these types.
#[derive(Clone, Debug)]
pub struct T {
    /// If we are expanding the RHS of a type definition, [report_cycle] contains
    /// the position and id of the LHS. This way, if the RHS expands at some point
    /// to the LHS id, we are able to report a cycle.
    ///
    /// (Shared: the record is copied at every `{ ety_env with ... }`.)
    report_cycle: Option<std::rc::Rc<(Pos, expandable::T)>>,
    /// The type defs and type access we have expanded thus far, at what position. Used
    /// to prevent entering into a cycle when expanding these types.
    /// We preserve order (i.e. use a list instead of set) for error reporting.
    /// (The most recent expansion first, as in the OCaml list.)
    expansions: crate::plist::List<Expansion>,
    /// true if we've ever detected a cycle during add_and_check_cycles
    cyclic_expansion: bool,
}

#[derive(Clone, Debug)]
pub enum Cycle {
    /// There was a cycle but not a cycle we want to report.
    NotToReport,
    ToReport {
        report_cycle: (Pos, expandable::T),
        expansions: crate::plist::List<Expansion>,
        last_expansion: Expansion,
    },
}

pub type CycleReporter = (Cycle, Option<reasons_callback::T>);

/// If we are expanding the RHS of a type definition, [report_cycle] contains
/// the position and id of the LHS. This way, if the RHS expands at some point
/// to the LHS id, we are able to report a cycle.
pub fn empty_w_cycle_report(report_cycle: Option<(Pos, expandable::T)>) -> T {
    T {
        report_cycle: report_cycle.map(std::rc::Rc::new),
        expansions: crate::plist::List::new(),
        cyclic_expansion: false,
    }
}

pub fn empty() -> T {
    empty_w_cycle_report(None)
}

fn add(exps: &T, exp: Expansion) -> T {
    let mut expansions = exps.expansions.clone();
    expansions.push_front(exp);
    T {
        expansions,
        ..exps.clone()
    }
}

/// [add_and_check_cycles expansions expansion] adds and [expansion] to [expansions]
/// and check that that [expansion] hasn't already been done, ;
/// i.e. wasn't already in [expansions].
pub fn add_and_check_cycles(t: &T, expansion: Expansion) -> Result<T, Cycle> {
    // Not in the OCaml: see `recording`.
    let name = recording::is_active().then(|| expansion.name.clone());
    let res = add_and_check_cycles_(t, expansion);
    if let Some(name) = name {
        recording::record(name, res.is_err());
    }
    res
}

fn add_and_check_cycles_(t: &T, expansion: Expansion) -> Result<T, Cycle> {
    let T {
        report_cycle,
        expansions,
        ..
    } = t;
    match report_cycle.as_deref() {
        Some((p_, x)) if expandable::equal(&expansion.name, x) => Err(Cycle::ToReport {
            report_cycle: (p_.clone(), x.clone()),
            expansions: expansions.clone(),
            last_expansion: expansion,
        }),
        Some(_) | None => {
            if expansions
                .iter()
                .any(|exp| expandable::equal(&expansion.name, &exp.name))
            {
                Err(Cycle::NotToReport)
            } else {
                Ok(add(t, expansion))
            }
        }
    }
}

/// Build a string like `report on C; A -> B::T -> C` where `A`, `B::T` and `C`
/// are the successive expansions seen so far.
pub fn to_log_string(t: &T) -> String {
    let T {
        report_cycle,
        expansions,
        cyclic_expansion: _,
    } = t;
    let report_cycle_s = match report_cycle.as_deref() {
        None => String::new(),
        Some((_p, exp)) => format!("report on {}; ", expandable::to_string(exp)),
    };
    let expansions_s = expansions
        .iter()
        .collect::<Vec<_>>()
        .into_iter()
        .rev()
        .map(|x| expandable::to_string(&x.name))
        .collect::<Vec<_>>()
        .join(" -> ");
    format!("{}expansions: {}", report_cycle_s, expansions_s)
}

pub fn report(cycles: &[CycleReporter]) -> Option<typing_error::T> {
    typing_error::multiple_opt(
        cycles
            .iter()
            .filter_map(|(cycle, on_error)| match cycle {
                Cycle::NotToReport => None,
                Cycle::ToReport {
                    report_cycle: (pos, first_exp),
                    expansions,
                    last_expansion,
                } => match first_exp {
                    expandable::T::Enum(_name) => on_error.as_ref().map(|on_error| {
                        typing_error::apply_reasons(
                            secondary::T::Cyclic_enum_constraint(
                                // TODO remove Pos_or_decl.of_raw_pos
                                crate::pos_or_decl::of_raw_pos(pos.clone()),
                            ),
                            on_error.clone(),
                        )
                    }),
                    expandable::T::TypeAlias(_name) => {
                        Some(typing_error::primary(primary::T::Cyclic_typedef {
                            def_pos: pos.clone(),
                            use_pos: last_expansion.use_pos.clone(),
                        }))
                    }
                    expandable::T::TypeConstant { .. } => {
                        let seen = std::iter::once(&last_expansion.name)
                            .chain(expansions.iter().map(|x| &x.name))
                            .chain(std::iter::once(first_exp))
                            .map(expandable::to_string)
                            .collect();
                        Some(typing_error::primary(primary::T::Cyclic_typeconst {
                            pos: pos.clone(),
                            tyconst_names: seen,
                        }))
                    }
                },
            })
            .collect(),
    )
}

/// Positions of the definitions of the type aliases or type constants that were successively expanded.
pub fn def_positions(t: &T) -> Vec<PosOrDecl> {
    let T {
        report_cycle,
        expansions,
        ..
    } = t;
    report_cycle
        .iter()
        .map(|rc| &**rc)
        .map(|(p, _)| crate::pos_or_decl::of_raw_pos(p.clone()))
        .chain(
            expansions
                .iter()
                .collect::<Vec<_>>()
                .into_iter()
                .rev()
                .filter_map(|x| x.def_pos.clone()),
        )
        .collect()
}

/// Returns true if there was an attempt to add a cycle to the expansion list.
/// No expansion in progress, none to report, and no cycle found: what
/// [`empty`] gives.
pub fn is_empty(exps: &T) -> bool {
    exps.report_cycle.is_none() && exps.expansions.is_empty() && !exps.cyclic_expansion
}

pub fn cyclic_expansion(exps: &T) -> bool {
    exps.cyclic_expansion
}

/// Not in the OCaml: whether adding an expansion of `name` to `t` would be a
/// cycle (`name` is being expanded, or is the one whose cycles are reported).
pub fn mentions(t: &T, name: &expandable::T) -> bool {
    matches!(&t.report_cycle, Some(rc) if &rc.1 == name)
        || t.expansions.iter().any(|exp| &exp.name == name)
}

/// Not in the OCaml. The cache of localized types of `Typing_phase` keeps,
/// besides what OCaml keeps, types whose localization OCaml would do again
/// (see `typing_phase::MakeTyCache`). Using one of those is only the same as
/// localizing again if no expansion that localizing does would be a cycle
/// where the type is used. So such a type is localized while recording the
/// names it expands (and whether one of them was a cycle), and it is used only
/// where none of those names is being expanded.
pub mod recording {
    use std::cell::RefCell;
    use std::rc::Rc;

    use super::expandable;

    /// What a localization expanded.
    #[derive(Default)]
    pub struct Recorded {
        /// The names of the type aliases, type constants and enums expanded,
        /// those of the cached types used included.
        pub names: Vec<expandable::T>,
        /// An expansion was a cycle, or a cached type whose expansions are not
        /// known was used.
        pub tainted: bool,
        /// The elements of `names` once there are more than a few, to keep
        /// them distinct without searching the list.
        seen: hash::HashSet<expandable::T>,
        /// The dependencies recorded for the definition being checked
        /// (`Typing_env.Deps.add_dependency_edge`), those of the cached types
        /// used included, when dependency edges are recorded: a cached type
        /// used for another definition records them again for it.
        pub deps: Vec<crate::typing_deps::dep::Variant>,
        /// The elements of `deps`, to keep them distinct.
        deps_seen: hash::HashSet<crate::typing_deps::dep::Variant>,
    }

    impl Recorded {
        fn add(&mut self, name: &expandable::T) {
            const FEW: usize = 8;
            if self.names.len() < FEW {
                if !self.names.contains(name) {
                    self.names.push(name.clone())
                }
                return;
            }
            if self.seen.is_empty() {
                self.seen.extend(self.names.iter().cloned());
            }
            if !self.seen.contains(name) {
                self.seen.insert(name.clone());
                self.names.push(name.clone())
            }
        }

        fn add_dep(&mut self, dep: &crate::typing_deps::dep::Variant) {
            if !self.deps_seen.contains(dep) {
                self.deps_seen.insert(dep.clone());
                self.deps.push(dep.clone())
            }
        }
    }

    thread_local! {
        /// The localizations being recorded, innermost last.
        static ACTIVE: RefCell<Vec<Recorded>> = const { RefCell::new(Vec::new()) };
    }

    /// After a panic was caught in the check of a file: no recording is in
    /// progress (see `crate::rt::decl_epoch::after_panic`).
    pub fn reset_after_panic() {
        ACTIVE.with_borrow_mut(|active| active.clear())
    }

    /// Starts recording; returns what `stop` takes.
    pub fn start() -> usize {
        ACTIVE.with_borrow_mut(|active| {
            active.push(Recorded::default());
            active.len() - 1
        })
    }

    /// Stops the recording that `start` returned `depth` for (and any that
    /// was started within it and not stopped).
    pub fn stop(depth: usize) -> Recorded {
        ACTIVE.with_borrow_mut(|active| {
            let recorded = if depth < active.len() {
                std::mem::take(&mut active[depth])
            } else {
                Recorded {
                    names: vec![],
                    tainted: true,
                    seen: hash::HashSet::default(),
                    deps: vec![],
                    deps_seen: hash::HashSet::default(),
                }
            };
            active.truncate(depth);
            recorded
        })
    }

    pub(crate) fn is_active() -> bool {
        ACTIVE.with_borrow(|active| !active.is_empty())
    }

    /// Records an expansion of `name` (`cycle`: it was refused as a cycle).
    pub(super) fn record(name: expandable::T, cycle: bool) {
        ACTIVE.with_borrow_mut(|active| {
            for recorded in active.iter_mut() {
                recorded.add(&name);
                recorded.tainted |= cycle
            }
        })
    }

    /// Records the expansions of a cached type that is used.
    pub fn extend(names: &Rc<Vec<expandable::T>>) {
        ACTIVE.with_borrow_mut(|active| {
            for recorded in active.iter_mut() {
                for name in names.iter() {
                    recorded.add(name)
                }
            }
        })
    }

    /// Records a dependency recorded for the definition being checked.
    pub(crate) fn record_dep(dep: &crate::typing_deps::dep::Variant) {
        ACTIVE.with_borrow_mut(|active| {
            for recorded in active.iter_mut() {
                recorded.add_dep(dep)
            }
        })
    }

    /// Records the dependencies of a cached type that is used.
    pub fn extend_deps(deps: &[crate::typing_deps::dep::Variant]) {
        ACTIVE.with_borrow_mut(|active| {
            for recorded in active.iter_mut() {
                for dep in deps {
                    recorded.add_dep(dep)
                }
            }
        })
    }

    /// A cached type whose expansions are not known is used.
    pub fn taint() {
        ACTIVE.with_borrow_mut(|active| {
            for recorded in active.iter_mut() {
                recorded.tainted = true
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn alias(name: &str) -> Expansion {
        Expansion {
            name: expandable::T::TypeAlias(name.to_string()),
            use_pos: Pos::NONE,
            def_pos: None,
        }
    }

    fn tconst(receiver_name: &str, type_const_name: &str) -> expandable::T {
        expandable::T::TypeConstant {
            receiver_name: receiver_name.to_string(),
            type_const_name: type_const_name.to_string(),
        }
    }

    #[test]
    fn expansions_and_cycles() {
        let t = empty();
        let t = add_and_check_cycles(&t, alias("A")).unwrap();
        let t = add_and_check_cycles(&t, alias("B")).unwrap();
        assert_eq!(to_log_string(&t), "expansions: A -> B");
        // expanding A again is a cycle, not to report
        assert!(matches!(
            add_and_check_cycles(&t, alias("A")),
            Err(Cycle::NotToReport)
        ));
        // `add_and_check_cycles` never sets the flag
        assert!(!cyclic_expansion(&t));
        assert!(def_positions(&t).is_empty());
    }

    #[test]
    fn reported_cycles() {
        let t = empty_w_cycle_report(Some((Pos::NONE, tconst("C", "T"))));
        assert_eq!(to_log_string(&t), "report on C::T; expansions: ");
        let t = add_and_check_cycles(
            &t,
            Expansion {
                name: tconst("A", "T"),
                use_pos: Pos::NONE,
                def_pos: Some(Pos::NONE),
            },
        )
        .unwrap();
        assert_eq!(def_positions(&t).len(), 2);
        let cycle = match add_and_check_cycles(
            &t,
            Expansion {
                name: tconst("C", "T"),
                use_pos: Pos::NONE,
                def_pos: None,
            },
        ) {
            Err(cycle @ Cycle::ToReport { .. }) => cycle,
            _ => panic!("expected a cycle to report"),
        };
        match report(&[(cycle, None), (Cycle::NotToReport, None)]) {
            Some(typing_error::T::Primary(prim)) => match &*prim {
                primary::T::Cyclic_typeconst { tyconst_names, .. } => {
                    assert_eq!(*tyconst_names, vec!["C::T", "A::T", "C::T"])
                }
                _ => panic!("expected Cyclic_typeconst"),
            },
            _ => panic!("expected Cyclic_typeconst"),
        }
        assert!(report(&[(Cycle::NotToReport, None)]).is_none());
    }

    #[test]
    fn enum_cycles_need_a_callback() {
        let t = empty_w_cycle_report(Some((
            Pos::NONE,
            expandable::T::Enum("E".to_string()),
        )));
        let cycle = add_and_check_cycles(
            &t,
            Expansion {
                name: expandable::T::Enum("E".to_string()),
                use_pos: Pos::NONE,
                def_pos: None,
            },
        )
        .unwrap_err();
        assert!(report(&[(cycle, None)]).is_none());
    }
}
