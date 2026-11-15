// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/tast_type_collector.ml`. See `hh/PORTING.md`.

use std::sync::Arc;

use oxidized::aast;
use oxidized::aast_visitor::Node;
use oxidized::aast_visitor::Visitor;
use oxidized::ast_defs;

use crate::ctx::Ctx;
use crate::diagnostics;
use crate::pos;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::tast_visitor::Reduce;
use crate::tast_visitor::Res;
use crate::tast_visitor::reduce;
use crate::typing_defs::PhaseTy;

pub type CollectedType = (tast_env::Env, PhaseTy);

/// `collected_type list Pos.AbsolutePosMap.t`
pub type CollectedTypes = pos::absolute_pos_map::T<Vec<CollectedType>>;

fn singleton(p: pos::Absolute, l: Vec<CollectedType>) -> CollectedTypes {
    CollectedTypes::unit(p, l)
}

/// The class of `type_collector`: a `reduce` visitor.
struct TypeCollector {
    acc: CollectedTypes,
}

/// `type_collector`
fn type_collector() -> TypeCollector {
    TypeCollector {
        acc: CollectedTypes::new(),
    }
}

impl<'a> Reduce<'a> for TypeCollector {
    type Acc = CollectedTypes;

    fn zero(&self) -> CollectedTypes {
        CollectedTypes::new()
    }

    /// `Pos.AbsolutePosMap.union ~combine:(fun _ a b -> Some (a @ b))`
    fn plus(&self, a: CollectedTypes, b: CollectedTypes) -> CollectedTypes {
        a.union_with(b, |mut a, b| {
            a.extend(b);
            a
        })
    }

    fn acc(&mut self) -> &mut CollectedTypes {
        &mut self.acc
    }
}

impl<'a> Visitor<'a> for TypeCollector {
    type Params = tast_visitor::IterParams;

    fn object(&mut self) -> &mut dyn Visitor<'a, Params = Self::Params> {
        self
    }

    tast_visitor::reduce_methods!('a);

    fn visit_expr(&mut self, env: &mut Env, x: &'a tast::Expr) -> Res {
        let aast::Expr(ty, p, _) = x;
        // `self#plus (singleton ..) (super#on_expr env (ty, p, expr_))`: the
        // arguments are evaluated from the last one.
        let (res, children) = reduce::result(self, |v| x.recurse(env, v));
        res?;
        let here = singleton(
            pos::to_absolute(p),
            vec![(env.clone(), PhaseTy::LoclTy(ty.clone()))],
        );
        let r = self.plus(here, children);
        reduce::add(self, r);
        Ok(())
    }

    fn visit_class_id(&mut self, env: &mut Env, x: &'a tast::ClassId) -> Res {
        let aast::ClassId(ty, _, cid) = x;
        let r = match cid {
            aast::ClassId_::CI(ast_defs::Id(p, _)) => singleton(
                pos::to_absolute(p),
                vec![(env.clone(), PhaseTy::LoclTy(ty.clone()))],
            ),
            _ => CollectedTypes::new(),
        };
        reduce::add(self, r);
        Ok(())
    }

    fn visit_fun_param(&mut self, env: &mut Env, fp: &'a tast::FunParam) -> Res {
        let (res, children) = reduce::result(self, |v| fp.recurse(env, v));
        res?;
        let here = singleton(
            pos::to_absolute(&fp.pos),
            vec![(env.clone(), PhaseTy::LoclTy(fp.annotation.clone()))],
        );
        let r = self.plus(here, children);
        reduce::add(self, r);
        Ok(())
    }

    fn visit_hint(&mut self, env: &mut Env, hint: &'a tast::Hint) -> Res {
        let aast::Hint(pos, _) = hint;
        let ty = tast_env::hint_to_ty(env, hint);
        let r = singleton(
            pos::to_absolute(pos),
            vec![(env.clone(), PhaseTy::DeclTy(ty))],
        );
        reduce::add(self, r);
        Ok(())
    }

    /// Coeffects are irrelevant to this collector's consumers (CST search
    /// and the lambda parameter rewriter), so don't traverse them.
    fn visit_contexts(&mut self, _env: &mut Env, _ctxs: &'a tast::Contexts) -> Res {
        Ok(())
    }
}

/// `type_collector#go`
fn type_collector_go(ctx: &Arc<Ctx>, program: &[tast::Def]) -> CollectedTypes {
    reduce::go(&mut type_collector(), ctx, program)
}

/// OCaml: `let collect_types tast = Diagnostics.ignore_ (fun () ->
/// type_collector#go tast)`, applied to the context and the program. The
/// `tast` of this definition is the context: all that runs under
/// `Diagnostics.ignore_` is the partial application `type_collector#go ctx`,
/// and the traversal runs when the closure it returns is applied to the
/// program, outside of `ignore_`.
pub fn collect_types(ctx: &Arc<Ctx>, tast: &[tast::Def]) -> CollectedTypes {
    let go = diagnostics::ignore_(|| {
        move |program: &[tast::Def]| type_collector_go(ctx, program)
    });
    go(tast)
}

/// `Pos.advance_one` on a `Pos.absolute`. `crate::pos::advance_one` takes a
/// `Pos` (`Relative_path.t pos`) only, and an absolute position cannot be
/// built from its parts outside `crate::pos`: the end is advanced on the
/// relative position, and `merge_absolute` gives the file and the start of
/// `position` with that end (an end one column further, so the later one).
fn advance_one_absolute(position: &pos::Absolute) -> pos::Absolute {
    let advanced = pos::to_absolute(&pos::advance_one(&pos::to_relative(position)));
    pos::merge_absolute(position, &advanced)
}

/// Ideally this would be just Pos.AbsolutePosMap.find_opt, however the positions
/// in the Tast are off by 1 from positions in the full fidelity parse trees.
///
/// TODO: Fix this when the full fidelity parse tree becomes the parser for type checking.
pub fn get_from_pos_map(position: &pos::Absolute, map: &CollectedTypes) -> Option<Vec<CollectedType>> {
    let position = advance_one_absolute(position);
    map.get(&position).cloned()
}
