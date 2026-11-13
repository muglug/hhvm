// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `class_const_origin_check.ml`. See `hh/PORTING.md`.

use std::collections::BTreeSet;

use oxidized::pos_or_decl::PosOrDecl;

use crate::decl_entry;
use crate::tast;
use crate::tast_env;
use crate::tast_visitor;
use crate::typing_defs::ClassConstFrom;
use crate::typing_error;
use crate::typing_error_utils;

/// `StringPair.t`: ordered and compared as a pair of strings.
pub type StringPair = (String, String);

/// `SPSet` (`Stdlib.Set.Make (StringPair)`)
type SPSet = BTreeSet<StringPair>;

/// Check that a constant does not depend on itself when initialized.
/// The cycle can span multiple classes. We're using the decl info
/// that tells us what are the constants *directly* used to initialize
/// `class_name::constant_name` to build a transitive set and check for cycles.
///
/// Note that some constant are using `self` instead of the current class
/// name, so we always carry the class where refs come from to be able
/// to perform the correct naming resolution.
pub fn find_cycle(env: &tast_env::Env, class_name: &str, constant_name: &str) -> bool {
    /// The references of a constant, as `(from, name)`.
    type Refs = Vec<(ClassConstFrom, String)>;
    let get_origin_and_refs = |class_name: &str, constant_name: &str| -> Option<(String, Refs)> {
        let cls = tast_env::get_class(env, class_name);
        let cls = decl_entry::to_option(cls)?;
        let class_const = tast_env::get_const(env, &cls, constant_name)?;
        Some((
            class_const.origin.as_str().to_string(),
            class_const
                .refs
                .iter()
                .map(|r| (r.0.clone(), r.1.as_str().to_string()))
                .collect(),
        ))
    };
    let target: StringPair = (class_name.to_string(), constant_name.to_string());
    // Todo is a list of pairs: a class name and class constant references
    // for constants within this class. It is used to resolve `self` correctly.
    // (The head of the OCaml list is the last element of the vector.)
    let spot_target = |mut visited: SPSet, mut todo: Vec<(String, Refs)>| -> bool {
        loop {
            match todo.pop() {
                None => return false,
                Some((current_class, refs)) => {
                    // Normalize refs
                    let refs: Vec<StringPair> = refs
                        .into_iter()
                        .map(|r| match r {
                            (ClassConstFrom::Self_, name) => (current_class.clone(), name),
                            (ClassConstFrom::From(class_name), name) => {
                                // Do deal with inherited constants we need to check the
                                // origin of constants from the decls.
                                let class_name = class_name.as_str();
                                let origin = (|| {
                                    let cls = tast_env::get_class(env, class_name);
                                    let cls = decl_entry::to_option(cls)?;
                                    let class_const = tast_env::get_const(env, &cls, &name)?;
                                    Some(class_const.origin.as_str().to_string())
                                })();
                                let origin = origin.unwrap_or_else(|| class_name.to_string());
                                (origin, name)
                            }
                        })
                        .collect();
                    let mut spotted = false;
                    for (c_name, name) in refs {
                        spotted = spotted || target == (c_name.clone(), name.clone());
                        if spotted {
                        } else if visited.contains(&(c_name.clone(), name.clone())) {
                        } else {
                            visited.insert((c_name.clone(), name.clone()));
                            match get_origin_and_refs(&c_name, &name) {
                                None => {}
                                Some((origin, refs)) => todo.push((origin, refs)),
                            }
                        }
                    }
                    // `spotted || spot_target visited todo`
                    if spotted {
                        return true;
                    }
                }
            }
        }
    };
    let empty = SPSet::new();
    let init = get_origin_and_refs(class_name, constant_name);
    let init = init.unwrap_or_else(|| (class_name.to_string(), vec![]));
    spot_target(empty, vec![init])
}

/// The object `handler`.
struct ClassConstOriginCheck;

impl<'a> tast_visitor::Handler<'a> for ClassConstOriginCheck {
    fn at_class_(&mut self, env: &tast_env::Env, c: &'a tast::Class_) {
        let c_name = &c.name.1;
        let c_consts = &c.consts;
        let cls = tast_env::get_class(env, c_name);
        match cls {
            decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {}
            decl_entry::T::Found(cls) => {
                for cc in c_consts {
                    let cc_name = &cc.id.1;
                    let cc = tast_env::get_const(env, &cls, cc_name);
                    match cc {
                        None => {}
                        Some(cc) => {
                            // This class constant may be inherited from an ancestor class, in which
                            // case we don't want to fire the error in this file.
                            if let Some(cc_pos) = tast_env::fill_in_pos_filename_if_in_current_decl(
                                env,
                                &PosOrDecl::from(cc.pos.clone()),
                            ) {
                                if find_cycle(env, c_name, cc_name) {
                                    typing_error_utils::add_typing_error(
                                        &typing_error::primary(
                                            typing_error::primary::T::Cyclic_class_constant {
                                                pos: cc_pos,
                                                class_name: c_name.clone(),
                                                const_name: cc_name.clone(),
                                            },
                                        ),
                                        env,
                                    )
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(ClassConstOriginCheck)
}
