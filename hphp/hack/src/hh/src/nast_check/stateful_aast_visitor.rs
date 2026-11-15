// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/stateful_aast_visitor.ml`: a traversal where each check
//! has a state of its own, which a node can change for what is below it.

use oxidized::aast_visitor::AstParams;
use oxidized::aast_visitor::Node;
use oxidized::aast_visitor::Visitor;
use oxidized::ast_defs::ShapeFieldName;
use oxidized::nast;

use super::Errors;

/// `nast_visitor_with_state`. Where the OCaml methods return the state for
/// the children of the node, these update it in place; the traversal restores
/// it once the children are done.
#[allow(unused_variables)]
pub trait NastVisitorWithState<'a> {
    type State: Clone;

    fn initial_state(&self) -> Self::State;

    fn at_fun_def(&mut self, state: &mut Self::State, x: &'a nast::FunDef, errors: &mut Errors) {}
    fn at_class_(&mut self, state: &mut Self::State, x: &'a nast::Class_, errors: &mut Errors) {}
    fn at_method_(&mut self, state: &mut Self::State, x: &'a nast::Method_, errors: &mut Errors) {}
    fn at_expr(&mut self, state: &mut Self::State, x: &'a nast::Expr, errors: &mut Errors) {}
    fn at_stmt(&mut self, state: &mut Self::State, x: &'a nast::Stmt, errors: &mut Errors) {}
    fn at_hint(&mut self, state: &mut Self::State, x: &'a nast::Hint, errors: &mut Errors) {}
    fn at_typedef(&mut self, state: &mut Self::State, x: &'a nast::Typedef, errors: &mut Errors) {}
    fn at_gconst(&mut self, state: &mut Self::State, x: &'a nast::Gconst, errors: &mut Errors) {}
    fn at_file_attribute(
        &mut self,
        state: &mut Self::State,
        x: &'a nast::FileAttribute,
        errors: &mut Errors,
    ) {
    }
    fn at_shape_field_name(
        &mut self,
        state: &mut Self::State,
        x: &'a ShapeFieldName,
        errors: &mut Errors,
    ) {
    }
    fn at_user_attribute(
        &mut self,
        state: &mut Self::State,
        x: &'a nast::UserAttribute,
        errors: &mut Errors,
    ) {
    }
    fn at_class_id(&mut self, state: &mut Self::State, x: &'a nast::ClassId, errors: &mut Errors) {}
    fn at_catch(&mut self, state: &mut Self::State, x: &'a nast::Catch, errors: &mut Errors) {}
    fn at_targ(&mut self, state: &mut Self::State, x: &'a nast::Targ, errors: &mut Errors) {}
    fn at_class_hint(&mut self, state: &mut Self::State, x: &'a nast::Hint, errors: &mut Errors) {}
    fn at_trait_hint(&mut self, state: &mut Self::State, x: &'a nast::Hint, errors: &mut Errors) {}
    fn at_xhp_attr_hint(
        &mut self,
        state: &mut Self::State,
        x: &'a nast::Hint,
        errors: &mut Errors,
    ) {
    }
}

/// `combine_visitors`
pub struct Combined<A, B>(pub A, pub B);

macro_rules! combine {
    ($($method:ident: $ty:ty,)*) => {
        $(
            fn $method(&mut self, state: &mut Self::State, x: &'a $ty, errors: &mut Errors) {
                self.0.$method(&mut state.0, x, errors);
                self.1.$method(&mut state.1, x, errors);
            }
        )*
    };
}

impl<'a, A: NastVisitorWithState<'a>, B: NastVisitorWithState<'a>> NastVisitorWithState<'a>
    for Combined<A, B>
{
    type State = (A::State, B::State);

    fn initial_state(&self) -> Self::State {
        (self.0.initial_state(), self.1.initial_state())
    }

    combine! {
        at_fun_def: nast::FunDef,
        at_class_: nast::Class_,
        at_method_: nast::Method_,
        at_expr: nast::Expr,
        at_stmt: nast::Stmt,
        at_hint: nast::Hint,
        at_typedef: nast::Typedef,
        at_gconst: nast::Gconst,
        at_file_attribute: nast::FileAttribute,
        at_shape_field_name: ShapeFieldName,
        at_user_attribute: nast::UserAttribute,
        at_class_id: nast::ClassId,
        at_catch: nast::Catch,
        at_targ: nast::Targ,
        at_class_hint: nast::Hint,
        at_trait_hint: nast::Hint,
        at_xhp_attr_hint: nast::Hint,
    }
}

/// `checker`
pub struct Checker<'e, V> {
    pub visitor: V,
    pub errors: &'e mut Errors,
}

impl<'a, 'e, V: NastVisitorWithState<'a>> Checker<'e, V> {
    /// `v#on_def v#initial_state def`
    pub fn on_def(&mut self, def: &'a nast::Def) {
        let mut state = self.visitor.initial_state();
        let _ = self.visit_def(&mut state, def);
    }
}

/// `let env = visitor#at_x env x in super#on_x env x`
macro_rules! at_then_recurse {
    ($($visit:ident, $at:ident: $ty:ty;)*) => {
        $(
            fn $visit(&mut self, state: &mut V::State, x: &'a $ty) -> Result<(), ()> {
                let saved = state.clone();
                self.visitor.$at(state, x, self.errors);
                let result = x.recurse(state, self);
                *state = saved;
                result
            }
        )*
    };
}

/// `class_hint`, `trait_hint` and `xhp_attr_hint` are aliases of `hint` that
/// the OCaml visitor tells apart; here they are told apart by the field of
/// the class they are in.
macro_rules! aliased_hints {
    ($self:ident, $state:ident, $at:ident, $hints:expr) => {
        for hint in $hints {
            let saved = $state.clone();
            $self.visitor.$at($state, hint, $self.errors);
            let result = $self.visit_hint($state, hint);
            *$state = saved;
            result?;
        }
    };
}

impl<'a, 'e, V: NastVisitorWithState<'a>> Visitor<'a> for Checker<'e, V> {
    type Params = AstParams<V::State, ()>;

    fn object(&mut self) -> &mut dyn Visitor<'a, Params = Self::Params> {
        self
    }

    at_then_recurse! {
        visit_fun_def, at_fun_def: nast::FunDef;
        visit_method_, at_method_: nast::Method_;
        visit_stmt, at_stmt: nast::Stmt;
        visit_hint, at_hint: nast::Hint;
        visit_typedef, at_typedef: nast::Typedef;
        visit_gconst, at_gconst: nast::Gconst;
        visit_file_attribute, at_file_attribute: nast::FileAttribute;
        visit_shape_field_name, at_shape_field_name: ShapeFieldName;
        visit_user_attribute, at_user_attribute: nast::UserAttribute;
        visit_class_id, at_class_id: nast::ClassId;
        visit_catch, at_catch: nast::Catch;
        visit_targ, at_targ: nast::Targ;
    }

    fn visit_expr(&mut self, state: &mut V::State, x: &'a nast::Expr) -> Result<(), ()> {
        if let nast::Expr_::Invalid(_) = &x.2 {
            return Ok(());
        }
        let saved = state.clone();
        self.visitor.at_expr(state, x, self.errors);
        let result = x.recurse(state, self);
        *state = saved;
        result
    }

    fn visit_class_(&mut self, state: &mut V::State, c: &'a nast::Class_) -> Result<(), ()> {
        let saved = state.clone();
        self.visitor.at_class_(state, c, self.errors);
        // `Class_::recurse`, field by field, for the sake of the aliased
        // hints. The fields that have nothing to visit are left out.
        let result = (|| {
            c.tparams.accept(state, self)?;
            aliased_hints!(self, state, at_class_hint, &c.extends);
            aliased_hints!(self, state, at_trait_hint, &c.uses);
            aliased_hints!(self, state, at_xhp_attr_hint, &c.xhp_attr_uses);
            aliased_hints!(self, state, at_class_hint, c.reqs.iter().map(|req| &req.0));
            aliased_hints!(self, state, at_class_hint, &c.implements);
            c.consts.accept(state, self)?;
            c.typeconsts.accept(state, self)?;
            c.vars.accept(state, self)?;
            c.methods.accept(state, self)?;
            c.xhp_children.accept(state, self)?;
            c.xhp_attrs.accept(state, self)?;
            c.user_attributes.accept(state, self)?;
            c.file_attributes.accept(state, self)?;
            c.enum_.accept(state, self)
        })();
        *state = saved;
        result
    }
}
