// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `duplicate_properties.ml`. See `hh/PORTING.md`.

#![allow(non_upper_case_globals)]

use std::collections::BTreeSet;

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::aast_visitor::AstParams;
use oxidized::aast_visitor::Node;
use oxidized::aast_visitor::Visitor;
use oxidized::ast_defs;
use oxidized::nast;
use oxidized::pos::Pos;
use relative_path::RelativePath;

use crate::ast_provider;
use crate::class_parent_check::base_hashtbl;
use crate::ctx::Ctx;
use crate::decl_entry;
use crate::error_codes;
use crate::folded_class as cls;
use crate::naming;
use crate::naming_provider;
use crate::tast;
use crate::tast_env;
use crate::tast_visitor;
use crate::typing_defs::ClassElt;
use crate::typing_warning;
use crate::typing_warning_utils;

pub const warning_kind: typing_warning::Kind<
    typing_warning::duplicate_properties::T,
    typing_warning::Migrated,
> = typing_warning::Kind::Duplicate_properties;

pub fn error_codes() -> Vec<error_codes::warning::T> {
    typing_warning_utils::codes(&warning_kind)
}

/// efficient check for List.length l > 1
pub fn more_than_one<A>(l: &[A]) -> bool {
    match l {
        [_, _, ..] => true,
        _ => false,
    }
}

/// All the trait names that appear in a use T statement inside class c
pub fn traits(c: &tast::Class_) -> Vec<(Pos, String)> {
    c.uses
        .iter()
        .filter_map(|aast::Hint(pos, trait_hint)| match &**trait_hint {
            aast::Hint_::Happly(ast_defs::Id(_, trait_name), _) => {
                Some((pos.clone(), trait_name.clone()))
            }
            _ => None,
        })
        .collect()
}

/// All the properites of class or trait [type name], flattened
pub fn properties(env: &tast_env::Env, type_name: &str) -> Vec<(String, ClassElt)> {
    let decl = tast_env::get_class(env, type_name);
    match decl {
        decl_entry::T::Found(decl) => {
            // `Cls.props decl @ Cls.sprops decl`: the arguments of `@` are
            // evaluated from right to left.
            let sprops = cls::sprops(&decl);
            let mut props = cls::props(&decl);
            props.extend(sprops);
            props
        }
        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => vec![],
    }
}

pub fn is_trait_name(env: &tast_env::Env, type_name: &str) -> bool {
    let decl = tast_env::get_class(env, type_name);
    match decl {
        decl_entry::T::Found(decl) => crate::ast_defs::is_c_trait(cls::kind(&decl)),
        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => false,
    }
}

/// All the parent classes, used traits, and implemented interfaces of
/// [type_name]. This is the flattened inheritance tree.
pub fn all_ancestor_names(env: &tast_env::Env, type_name: &str) -> Vec<String> {
    let decl = tast_env::get_class(env, type_name);
    match decl {
        decl_entry::T::Found(decl) => cls::all_ancestor_names(&decl),
        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => vec![],
    }
}

/// All the used traits of [type_name]. This is the flattened inheritance tree.
pub fn all_trait_ancestors(ctx: &tast_env::Env, trait_name: &str) -> Vec<String> {
    let ancestors = all_ancestor_names(ctx, trait_name);
    // Trait ancestors can be other traits or interfaces.
    let ancestor_traits = ancestors.into_iter().filter(|a| is_trait_name(ctx, a));
    std::iter::once(trait_name.to_string())
        .chain(ancestor_traits)
        .collect()
}

pub fn get_class_nast(
    ctx: &std::sync::Arc<Ctx>,
    file_path: &RelativePath,
    c_name: &str,
) -> Option<nast::Class_> {
    let ast = ast_provider::find_class_in_file(true, ctx, file_path, c_name);
    ast.map(|ast| naming::class_(ctx, ast))
}

pub fn check_initialisation(ast: &nast::Class_, expr: &nast::Expr) -> bool {
    /// The object `checker` (which inherits from `Aast.iter`).
    struct Checker {
        result: bool,
    }
    impl<'a> Visitor<'a> for Checker {
        type Params = AstParams<(), ()>;

        fn object(&mut self) -> &mut dyn Visitor<'a, Params = Self::Params> {
            self
        }

        fn visit_expr(&mut self, ast: &mut (), expr: &'a nast::Expr) -> Result<(), ()> {
            let aast::Expr(_, _, expr_) = expr;
            // super#on_expr
            expr.recurse(ast, self)?;
            match expr_ {
                aast::Expr_::ClassConst(cc) => {
                    let (_, (_, s)) = &**cc;
                    if s != sn::members::M_CLASS {
                        self.result = true
                    }
                }
                _ => {}
            }
            Ok(())
        }
    }
    // The class is the environment of the visitor, which does not read it.
    let _ = ast;
    let mut checker = Checker { result: false };
    let _ = checker.visit_expr(&mut (), expr);
    checker.result
}

pub fn add_warning(
    env: &tast_env::Env,
    pos: &Pos,
    as_lint: bool,
    class_name: &str,
    prop_name: &str,
    class_names: Vec<String>,
    initialized_with_constant: bool,
) {
    typing_warning_utils::add_for_migration(
        &tast_env::get_tcopt(env),
        if as_lint { Some(None) } else { None },
        (
            pos.clone(),
            warning_kind,
            typing_warning::duplicate_properties::T {
                class_name: class_name.to_string(),
                prop_name: prop_name.to_string(),
                class_names,
                initialized_with_constant,
            },
        ),
    )
}

/// The object `handler ~as_lint`.
struct DuplicateProperties {
    as_lint: bool,
}

impl<'a> tast_visitor::Handler<'a> for DuplicateProperties {
    fn at_class_(&mut self, env: &tast_env::Env, c: &'a tast::Class_) {
        let as_lint = self.as_lint;
        let ctx = tast_env::get_ctx(env);
        let ast_defs::Id(cls_pos, class_name) = &c.name;

        // This map contains
        // - the property names of each trait used by cls to their origin
        // - the properties defined by cls itself to cls
        // If a property is inherited multiple times, props_seen will report multiple origins
        let mut props_seen: base_hashtbl::StringMultiTable<String> =
            base_hashtbl::StringMultiTable::create();

        // In decls, static properties are stored with a leading dollar,
        // but in class_var without a leading dollar.
        // So normalise by removing leading dollars
        let strip_dollar = |s: &str| s.trim_start_matches('$').to_string();

        // add the properties defined in the class itself to props_seen
        for v in &c.vars {
            props_seen.add_multi(v.id.1.clone(), class_name.clone())
        }

        // for each used trait add the properties defined in the trait, mapped to their origin
        for (_, type_name) in traits(c) {
            let all_trait_ancestors: BTreeSet<String> =
                all_trait_ancestors(env, &type_name).into_iter().collect();
            for (prop_name, prop_elt) in properties(env, &type_name) {
                // but do not add properties that are imported via require extends
                if all_trait_ancestors.contains(&prop_elt.ce_origin) {
                    props_seen.add_multi(strip_dollar(&prop_name), prop_elt.ce_origin.clone())
                }
            }
        }

        // if the props_seen reports multiple origins for a property,
        // ensure that in none of the origins it is initialised
        // with an enum or class constant
        props_seen.iteri(|prop_name, data| {
            if more_than_one(data) {
                // property key is inherited multiple times, possibly via diamond inclusion
                // ensure that is never initialised with an enum or class constant
                let is_initialised_with_class_constant =
                    data.iter().fold(false, |status, origin| {
                        let res = (|| {
                            let opt_origin_file_path =
                                naming_provider::get_class_path(&ctx, origin);
                            let file_path = opt_origin_file_path?;
                            let ast = get_class_nast(&ctx, &file_path, origin)?;
                            let opt_var = ast.vars.iter().find(|v| v.id.1 == prop_name);
                            let var = opt_var?;
                            let expr = var.expr.as_ref()?;
                            Some(status || check_initialisation(&ast, expr))
                        })();
                        res.unwrap_or(status)
                    });
                // remove duplicate trait names arising from diamond inclusion from data
                let class_names = {
                    let mut l = data.to_vec();
                    l.sort();
                    l.dedup();
                    l
                };

                if is_initialised_with_class_constant {
                    // HHVM will unconditinally fatal, so report a linter error
                    add_warning(
                        env,
                        cls_pos,
                        as_lint,
                        class_name,
                        prop_name,
                        class_names,
                        true,
                    )
                } else if more_than_one(&class_names) {
                    // there is a duplicate property not arising from diamond inclusion, warn about it
                    add_warning(
                        env,
                        cls_pos,
                        as_lint,
                        class_name,
                        prop_name,
                        class_names,
                        false,
                    )
                }
            }
        })
    }
}

pub fn handler<'a>(as_lint: bool) -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(DuplicateProperties { as_lint })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn more_than_one_element() {
        assert!(!more_than_one::<u8>(&[]));
        assert!(!more_than_one(&[1]));
        assert!(more_than_one(&[1, 2]));
        assert!(more_than_one(&[1, 2, 3]));
    }
}
