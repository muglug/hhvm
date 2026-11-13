// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_case_type_utils.ml`. See `hh/PORTING.md`.

use oxidized::aast;
use pos::Positioned;
use pos::TypeName;

use crate::ctx::R;
use crate::decl_entry;
use crate::decl_hint;
use crate::s_set;
use crate::type_visitor::DeclTypeVisitor;
use crate::typing_defs::TypedefTypeAssignment;
use crate::typing_defs_core::DeclTy;
use crate::typing_defs_core::DeclTy_;
use crate::typing_env as env;
use crate::typing_env::ClassOrTypedefResult;
use crate::typing_env_types::Env;

/// The position type of declarations.
type DeclPos = <R as ty::reason::Reason>::Pos;

/// The visitor of `visit seen`: `Type_visitor.decl_type_visitor` with
/// `on_tapply` overridden.
struct MentionsVisitor<'a> {
    env: &'a Env,
    name: &'a str,
    seen: &'a s_set::T,
}

impl DeclTypeVisitor<Vec<DeclTy>> for MentionsVisitor<'_> {
    fn on_tapply(
        &mut self,
        acc: Vec<DeclTy>,
        reason: &R,
        id: &Positioned<TypeName, DeclPos>,
        args: &[DeclTy],
    ) -> Vec<DeclTy> {
        let sid = id.id_ref().as_str();
        let mut mentions = if sid == self.name {
            vec![DeclTy::new(
                reason.clone(),
                DeclTy_::Tapply(Box::new((id.clone(), args.to_vec().into_boxed_slice()))),
            )]
        } else if self.seen.contains(sid) {
            vec![]
        } else {
            let mut seen = self.seen.clone();
            seen.insert(sid.to_string());
            match env::get_class_or_typedef(self.env, sid) {
                decl_entry::T::Found(ClassOrTypedefResult::TypedefResult(typedef_info)) => {
                    match &typedef_info.type_assignment {
                        TypedefTypeAssignment::SimpleTypeDef(_, hint) => {
                            visit(self.env, self.name, &seen, hint)
                        }
                        TypedefTypeAssignment::CaseType(variant, variants) => {
                            let hints: Vec<&DeclTy> = std::iter::once(variant)
                                .chain(variants.iter())
                                .flat_map(|v| {
                                    std::iter::once(&v.hint).chain(
                                        v.where_constraints
                                            .iter()
                                            .flat_map(|wc| [&wc.0, &wc.2].into_iter()),
                                    )
                                })
                                .collect();
                            hints
                                .into_iter()
                                .flat_map(|hint| visit(self.env, self.name, &seen, hint))
                                .collect()
                        }
                    }
                }
                _ => vec![],
            }
        };
        // `super#on_tapply acc reason id args`
        let rest = args.iter().fold(acc, |acc, ty| self.on_type(acc, ty));
        mentions.extend(rest);
        mentions
    }
}

fn visit(env: &Env, name: &str, seen: &s_set::T, ty: &DeclTy) -> Vec<DeclTy> {
    let mut visitor = MentionsVisitor { env, name, seen };
    visitor.on_type(vec![], ty)
}

pub fn find_recursive_mentions_in_decl_ty_via_typedef(
    env: &Env,
    name: &str,
    ty: &DeclTy,
) -> Vec<DeclTy> {
    visit(env, name, &s_set::T::new(), ty)
}

pub fn decl_ty_mentions_name_via_typedef(env: &Env, name: &str, ty: &DeclTy) -> bool {
    !find_recursive_mentions_in_decl_ty_via_typedef(env, name, ty).is_empty()
}

pub fn find_where_clause_recursive_mentions(
    env: &Env,
    t_name: &aast::Sid,
    where_constraints: &[aast::WhereConstraintHint],
) -> Vec<(aast::WhereConstraintHint, Vec<DeclTy>)> {
    let find_recursive_mentions = |hint: &aast::Hint| {
        let ty = decl_hint::hint(&env.decl_env, hint);
        let oxidized::ast_defs::Id(_pos, name) = t_name;
        find_recursive_mentions_in_decl_ty_via_typedef(env, name, &ty)
    };
    where_constraints
        .iter()
        .map(|wc| {
            let aast::WhereConstraintHint(h1, _, h2) = wc;
            // `find_recursive_mentions h1 @ find_recursive_mentions h2`: the
            // right operand first.
            let mentions2 = find_recursive_mentions(h2);
            let mut mentions = find_recursive_mentions(h1);
            mentions.extend(mentions2);
            (wc.clone(), mentions)
        })
        .collect()
}

pub fn filter_where_clauses_with_recursive_mentions(
    env: &Env,
    t_name: &aast::Sid,
    where_constraints: &[aast::WhereConstraintHint],
) -> Vec<aast::WhereConstraintHint> {
    find_where_clause_recursive_mentions(env, t_name, where_constraints)
        .into_iter()
        .filter_map(
            |(wc, mentions)| {
                if mentions.is_empty() { Some(wc) } else { None }
            },
        )
        .collect()
}
