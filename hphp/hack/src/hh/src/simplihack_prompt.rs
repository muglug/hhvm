// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `simplihack/simplihack_prompt.ml`. See `hh/PORTING.md`.

use bstr::BString;
use naming_special_names_rust as sn;
use oxidized::aast;

use crate::code_actions::aast_reduce;
use crate::code_actions::aast_reduce::Reducer;
use crate::code_actions::aast_reduce::SNode;
use crate::pos::Pos;
use crate::provider_context;
use crate::simplihack_interpreter;
use crate::tast;
use crate::tast_env::Env;
use crate::tast_visitor::IterParams;

pub struct T<'a> {
    pub param_pos: Pos,
    pub derive_prompt: Box<dyn Fn() -> Option<BString> + 'a>,
    pub edit_span: Pos,
}

/// `derive_prompt env e ()`: the prompt is the bytes of the OCaml string
/// the attribute evaluates to.
fn derive_prompt<'a>(env: &Env, e: &'a tast::Expr) -> Box<dyn Fn() -> Option<BString> + 'a> {
    let env = env.clone();
    Box::new(move || simplihack_interpreter::eval(&env, e).ok())
}

type Acc<'a> = Vec<T<'a>>;

/// `List.fold ~init:acc ~f:(user_attribute env edit_span) uas`: each prompt
/// goes before the ones found so far.
fn user_attributes<'a>(
    env: &Env,
    edit_span: &Pos,
    mut acc: Acc<'a>,
    uas: &'a [aast::UserAttribute<tast::Ty, tast::SavedEnv>],
) -> Acc<'a> {
    for ua in uas {
        let attribute_name = &ua.name.1;
        if attribute_name == sn::user_attributes::SIMPLIHACK {
            match ua.params.as_slice() {
                [arg] => {
                    let param_pos = crate::pos::btw(&ua.name.0, &arg.1);
                    acc.insert(
                        0,
                        T {
                            param_pos,
                            edit_span: edit_span.clone(),
                            derive_prompt: derive_prompt(env, arg),
                        },
                    )
                }
                [arg1, arg2] => {
                    let param_pos = crate::pos::btw(&ua.name.0, &arg2.1);
                    acc.insert(
                        0,
                        T {
                            param_pos,
                            edit_span: edit_span.clone(),
                            derive_prompt: derive_prompt(env, arg1),
                        },
                    )
                }
                _ => {}
            }
        }
    }
    acc
}

struct Visitor;

impl<'a> Reducer<'a, IterParams, Acc<'a>> for Visitor {
    fn object(&mut self) -> &mut dyn Reducer<'a, IterParams, Acc<'a>> {
        self
    }
    fn zero(&mut self) -> Acc<'a> {
        vec![]
    }
    fn plus(&mut self, mut a: Acc<'a>, b: Acc<'a>) -> Acc<'a> {
        a.extend(b);
        a
    }
    aast_reduce::tast::tast_methods!('a, Acc<'a>; expr_, expression_tree);

    fn visit_class_(&mut self, env: &mut Env, cls: &'a tast::Class_) -> Acc<'a> {
        let acc = cls.srecurse(env, self);
        user_attributes(env, &cls.span, acc, &cls.user_attributes.0)
    }

    fn visit_method_(&mut self, env: &mut Env, meth: &'a tast::Method_) -> Acc<'a> {
        let acc = aast_reduce::tast::on_method_(self, env, meth);
        user_attributes(env, &meth.span, acc, &meth.user_attributes.0)
    }

    fn visit_fun_(&mut self, env: &mut Env, func: &'a tast::Fun_) -> Acc<'a> {
        let acc = aast_reduce::tast::on_fun_(self, env, func);
        user_attributes(env, &func.span, acc, &func.user_attributes.0)
    }

    fn visit_class_var(&mut self, env: &mut Env, cv: &'a tast::ClassVar) -> Acc<'a> {
        let acc = aast_reduce::tast::on_class_var(self, env, cv);
        user_attributes(env, &cv.span, acc, &cv.user_attributes.0)
    }

    fn visit_typedef(&mut self, env: &mut Env, x: &'a tast::Typedef) -> Acc<'a> {
        let acc = x.srecurse(env, self);
        user_attributes(env, &x.span, acc, &x.user_attributes.0)
    }

    fn visit_class_const(&mut self, env: &mut Env, x: &'a aast::ClassConst<tast::Ty, tast::SavedEnv>) -> Acc<'a> {
        let acc = x.srecurse(env, self);
        user_attributes(env, &x.span, acc, &x.user_attributes.0)
    }

    fn visit_fun_param(&mut self, env: &mut Env, x: &'a tast::FunParam) -> Acc<'a> {
        let acc = x.srecurse(env, self);
        match x.visibility {
            None => acc,
            Some(_) => user_attributes(env, &x.pos, acc, &x.user_attributes.0),
        }
    }

    fn visit_file_attribute(
        &mut self,
        env: &mut Env,
        x: &'a aast::FileAttribute<tast::Ty, tast::SavedEnv>,
    ) -> Acc<'a> {
        let acc = x.srecurse(env, self);
        user_attributes(env, &Pos::NONE, acc, &x.user_attributes.0)
    }

    fn visit_tparam(&mut self, env: &mut Env, x: &'a aast::Tparam<tast::Ty, tast::SavedEnv>) -> Acc<'a> {
        let acc = x.srecurse(env, self);
        user_attributes(env, &x.name.0, acc, &x.user_attributes.0)
    }

    fn visit_class_typeconst_def(
        &mut self,
        env: &mut Env,
        x: &'a aast::ClassTypeconstDef<tast::Ty, tast::SavedEnv>,
    ) -> Acc<'a> {
        let acc = x.srecurse(env, self);
        user_attributes(env, &x.span, acc, &x.user_attributes.0)
    }

    fn visit_module_def(&mut self, env: &mut Env, x: &'a aast::ModuleDef<tast::Ty, tast::SavedEnv>) -> Acc<'a> {
        let acc = x.srecurse(env, self);
        user_attributes(env, &x.span, acc, &x.user_attributes.0)
    }
}

pub fn find<'a>(ctx: &provider_context::T, tast: &'a [tast::Def]) -> Vec<T<'a>> {
    aast_reduce::tast::go(&mut Visitor, ctx, tast)
}
