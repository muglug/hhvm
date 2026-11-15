// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/nast_check/unbound_name_check.ml`.
//!
//! Checks to determine whether names referenced in a file are defined
//! globally.
//!
//! Not ported: the dependencies that the OCaml check records for the names
//! it looks up (there is no dependency graph), and the warning that replaces
//! the error in files under `repo_stdlib_path` (nothing is reported for
//! them).

use std::collections::BTreeMap;
use std::rc::Rc;

use oxidized::ast_defs::ReifyKind;
use oxidized::ast_defs::ShapeFieldName;
use oxidized::name_context::NameContext;
use oxidized::naming_error::NamingError;
use oxidized::nast;
use oxidized::nast_check_error::NastCheckError;
use oxidized::pos::Pos;
use pos::ConstName;
use pos::FunName;
use pos::ModuleName;
use pos::ToOxidized;
use pos::TypeName;

use super::Errors;
use super::sn;
use super::stateful_aast_visitor::NastVisitorWithState;
use crate::ctx::Ctx;

/// A persistent list: states are copied at every node.
struct Cons<T> {
    head: T,
    tail: List<T>,
}

type List<T> = Option<Rc<Cons<T>>>;

fn cons<T>(head: T, tail: &List<T>) -> List<T> {
    Some(Rc::new(Cons {
        head,
        tail: tail.clone(),
    }))
}

fn find<T>(list: &List<T>, pred: impl Fn(&T) -> bool) -> Option<&T> {
    let mut list = list;
    while let Some(node) = list {
        if pred(&node.head) {
            return Some(&node.head);
        }
        list = &node.tail;
    }
    None
}

#[derive(Clone)]
pub struct Env<'a> {
    type_params: Rc<BTreeMap<&'a str, ReifyKind>>,
    /// Need some context to differentiate global consts and other `Id`s.
    /// The most recent binding of a name comes first.
    seen_names: List<(&'a str, &'a Pos)>,
    /// Contexts where typedefs are valid typenames
    class_id_allow_typedef: bool,
    hint_allow_typedef: bool,
    hint_context: NameContext,
}

pub struct UnboundNameCheck<'a> {
    ctx: &'a Ctx,
    /// When the names of the context are those of a naming table (the
    /// daemon, the IDE: `Ctx::names_are_a_naming_table`), the context as a
    /// `Provider_context.t`, whose `crate::naming_provider` answers the
    /// lookups, as the OCaml's `Naming_provider` does; otherwise (the batch
    /// checker) the decl stores, which hold exactly the bound names, do.
    naming: Option<std::sync::Arc<Ctx>>,
}

enum TypeKind {
    Class,
    /// With the position of its declaration.
    Typedef(Pos),
}

impl<'a> UnboundNameCheck<'a> {
    pub fn new(ctx: &'a Ctx) -> Self {
        let naming = crate::ctx::naming_table_lookups::provider(ctx);
        Self { ctx, naming }
    }

    fn handle_unbound_name(&self, pos: &Pos, name: &str, kind: NameContext, errors: &mut Errors) {
        // We've already errored in naming if we get *Unknown* class
        if name == sn::classes::UNKNOWN {
            return;
        }
        if let Some(prefix) = &self.ctx.tco.tco_repo_stdlib_path {
            if pos.filename().path_str().starts_with(prefix.as_str()) {
                // `Typing_warning.Unbound_name_warning`: warnings are not
                // reported yet.
                return;
            }
        }
        errors.add(NamingError::UnboundName {
            pos: pos.clone(),
            name: name.to_string(),
            kind,
        });
    }

    /// `Naming_provider.get_type_kind`, with the position that
    /// `Naming_global.GEnv.get_type_full_pos` gives for a typedef.
    fn get_type_kind(&self, name: &str) -> Option<TypeKind> {
        if let Some(ctx) = &self.naming {
            return match crate::ctx::naming_table_lookups::get_type_kind(ctx, name) {
                Some(oxidized::naming_types::KindOfType::TTypedef) => {
                    Some(TypeKind::Typedef(crate::ctx::naming_table_lookups::type_full_pos(ctx, name)))
                }
                Some(oxidized::naming_types::KindOfType::TClass) => Some(TypeKind::Class),
                None => None,
            };
        }
        let name = TypeName::new(name);
        if let Ok(Some(_)) = self.ctx.shallow_decls.get_class(name) {
            return Some(TypeKind::Class);
        }
        if let Ok(Some(typedef)) = self.ctx.shallow_decls.get_typedef(name) {
            return Some(TypeKind::Typedef(typedef.pos.clone().to_oxidized()));
        }
        None
    }

    /// `Naming_global.GEnv.type_pos`
    fn type_pos(&self, name: TypeName) -> Option<Pos> {
        if let Some(ctx) = &self.naming {
            return crate::ctx::naming_table_lookups::type_pos(ctx, name.as_str());
        }
        if let Ok(Some(class)) = self.ctx.shallow_decls.get_class(name) {
            return Some(class.name.pos().clone().to_oxidized());
        }
        if let Ok(Some(typedef)) = self.ctx.shallow_decls.get_typedef(name) {
            return Some(typedef.pos.clone().to_oxidized());
        }
        None
    }

    /// `Naming_global.GEnv.fun_pos`
    fn fun_pos(&self, name: FunName) -> Option<Pos> {
        if let Some(ctx) = &self.naming {
            return crate::ctx::naming_table_lookups::fun_pos(ctx, name.as_str());
        }
        match self.ctx.shallow_decls.get_fun(name) {
            Ok(Some(fun)) => Some(fun.pos.clone().to_oxidized()),
            _ => None,
        }
    }

    /// `has_canon_name`: report the declared spelling of a name that only
    /// differs from it by case, if there is one.
    fn has_canon_name(
        &self,
        suggestion: Option<(&str, Option<Pos>)>,
        pos: &Pos,
        name: &str,
        errors: &mut Errors,
    ) -> bool {
        match suggestion {
            Some((suggest_name, Some(suggest_pos))) => {
                errors.add(NamingError::DidYouMean {
                    pos: pos.clone(),
                    name: name.to_string(),
                    suggest_pos,
                    suggest_name: suggest_name.to_string(),
                });
                true
            }
            _ => false,
        }
    }

    fn check_fun_name(&self, nast::Id(pos, name): &nast::Id, errors: &mut Errors) {
        if sn::pre_namespaced_functions::is_pre_namespaced_function(name) {
            return;
        }
        let canon = match &self.naming {
            Some(ctx) => {
                if crate::ctx::naming_table_lookups::fun_exists(ctx, name) {
                    return;
                }
                crate::ctx::naming_table_lookups::get_fun_canon_name(ctx, name).map(|canon| FunName::new(&canon))
            }
            None => {
                if let Ok(Some(_)) = self.ctx.shallow_decls.get_fun(FunName::new(name)) {
                    return;
                }
                self.ctx.get_fun_canon_name(name)
            }
        };
        let suggestion = canon.map(|canon| (canon.as_str(), self.fun_pos(canon)));
        if self.has_canon_name(suggestion, pos, name, errors) {
            return;
        }
        self.handle_unbound_name(pos, name, NameContext::FunctionNamespace, errors);
    }

    fn check_const_name(&self, nast::Id(pos, name): &nast::Id, errors: &mut Errors) {
        let exists = match &self.naming {
            Some(ctx) => crate::ctx::naming_table_lookups::const_exists(ctx, name),
            None => matches!(self.ctx.shallow_decls.get_const(ConstName::new(name)), Ok(Some(_))),
        };
        if exists {
            return;
        }
        self.handle_unbound_name(pos, name, NameContext::ConstantNamespace, errors);
    }

    fn check_module_name(&self, nast::Id(pos, name): &nast::Id, errors: &mut Errors) {
        let exists = match &self.naming {
            Some(ctx) => crate::ctx::naming_table_lookups::module_exists(ctx, name),
            None => matches!(self.ctx.shallow_decls.get_module(ModuleName::new(name)), Ok(Some(_))),
        };
        if exists {
            return;
        }
        self.handle_unbound_name(pos, name, NameContext::ModuleNamespace, errors);
    }

    fn check_module_if_present(&self, id: &Option<nast::Id>, errors: &mut Errors) {
        if let Some(id) = id {
            self.check_module_name(id, errors);
        }
    }

    fn check_package_name(&self, pos: &Pos, name: &str, errors: &mut Errors) {
        // `Package_info.package_exists`
        if super::package_expression_check::lookup_package(self.ctx, name).is_some() {
            return;
        }
        errors.add(NamingError::UnboundName {
            pos: pos.clone(),
            name: name.to_string(),
            kind: NameContext::PackageNamespace,
        });
    }

    fn check_type_name(
        &self,
        env: &Env<'a>,
        pos: &Pos,
        name: &str,
        kind: NameContext,
        allow_typedef: bool,
        allow_generics: bool,
        errors: &mut Errors,
    ) {
        if name == sn::classes::HH_BUILTIN_ENUM {
            return;
        }
        match env.type_params.get(name) {
            Some(reified) => {
                // TODO: These throw typing errors instead of naming errors
                if !allow_generics {
                    errors.add(NastCheckError::GenericsNotAllowed(pos.clone()));
                }
                let prefix = match reified {
                    ReifyKind::Erased => "Erased",
                    ReifyKind::SoftReified => "Soft reified",
                    ReifyKind::Reified => return,
                };
                errors.add(NastCheckError::GenericAtRuntime {
                    pos: pos.clone(),
                    prefix: prefix.to_string(),
                });
            }
            None => match self.get_type_kind(name) {
                Some(TypeKind::Typedef(decl_pos)) if !allow_typedef => {
                    errors.add(NamingError::UnexpectedTypedef {
                        pos: pos.clone(),
                        decl_pos,
                        expected_kind: kind,
                    });
                }
                Some(_) => {}
                None => {
                    let canon = match &self.naming {
                        Some(ctx) => crate::ctx::naming_table_lookups::get_type_canon_name(ctx, name).map(|canon| TypeName::new(&canon)),
                        None => self.ctx.get_type_canon_name(name),
                    };
                    let suggestion = canon.map(|canon| (canon.as_str(), self.type_pos(canon)));
                    if self.has_canon_name(suggestion, pos, name, errors) {
                        return;
                    }
                    self.handle_unbound_name(pos, name, kind, errors);
                }
            },
        }
    }

    fn check_type_hint(
        &self,
        env: &Env<'a>,
        nast::Id(pos, name): &nast::Id,
        kind: NameContext,
        allow_typedef: bool,
        allow_generics: bool,
        errors: &mut Errors,
    ) {
        if name == sn::typehints::WILDCARD {
            return;
        }
        self.check_type_name(env, pos, name, kind, allow_typedef, allow_generics, errors);
    }

    /// `check_type_name ~allow_typedef:false ~allow_generics:false
    /// ~kind:Name_context.ClassContext`
    fn check_class_name(&self, env: &Env<'a>, pos: &Pos, name: &str, errors: &mut Errors) {
        self.check_type_name(
            env,
            pos,
            name,
            NameContext::ClassContext,
            false,
            false,
            errors,
        );
    }
}

fn extend_type_params<'a>(
    init: &Rc<BTreeMap<&'a str, ReifyKind>>,
    params: &'a [nast::Tparam],
) -> Rc<BTreeMap<&'a str, ReifyKind>> {
    if params.is_empty() {
        return Rc::clone(init);
    }
    let mut type_params = BTreeMap::clone(init);
    // `List.fold_right`: of two parameters with the same name, the first one
    // is the one that stays.
    for tparam in params.iter().rev() {
        type_params.insert(tparam.name.1.as_str(), tparam.reified);
    }
    Rc::new(type_params)
}

impl<'a> NastVisitorWithState<'a> for UnboundNameCheck<'a> {
    type State = Env<'a>;

    // The following are all setting the environments / context correctly

    fn initial_state(&self) -> Env<'a> {
        Env {
            type_params: Rc::new(BTreeMap::new()),
            seen_names: None,
            class_id_allow_typedef: false,
            hint_allow_typedef: true,
            hint_context: NameContext::TypeNamespace,
        }
    }

    fn at_class_(&mut self, env: &mut Env<'a>, c: &'a nast::Class_, errors: &mut Errors) {
        env.type_params = extend_type_params(&Rc::new(BTreeMap::new()), &c.tparams);
        self.check_module_if_present(&c.module, errors);
    }

    fn at_typedef(&mut self, env: &mut Env<'a>, td: &'a nast::Typedef, errors: &mut Errors) {
        env.type_params = extend_type_params(&Rc::new(BTreeMap::new()), &td.tparams);
        self.check_module_if_present(&td.module, errors);
    }

    fn at_fun_def(&mut self, env: &mut Env<'a>, fd: &'a nast::FunDef, errors: &mut Errors) {
        env.type_params = extend_type_params(&env.type_params, &fd.tparams);
        self.check_module_if_present(&fd.module, errors);
    }

    fn at_gconst(&mut self, _env: &mut Env<'a>, gconst: &'a nast::Gconst, errors: &mut Errors) {
        self.check_module_if_present(&gconst.module, errors);
    }

    fn at_method_(&mut self, env: &mut Env<'a>, m: &'a nast::Method_, _errors: &mut Errors) {
        env.type_params = extend_type_params(&env.type_params, &m.tparams);
    }

    fn at_targ(&mut self, env: &mut Env<'a>, _targ: &'a nast::Targ, _errors: &mut Errors) {
        env.hint_allow_typedef = true;
    }

    fn at_class_hint(&mut self, env: &mut Env<'a>, _h: &'a nast::Hint, _errors: &mut Errors) {
        env.hint_context = NameContext::ClassContext;
        env.hint_allow_typedef = false;
    }

    fn at_trait_hint(&mut self, env: &mut Env<'a>, _h: &'a nast::Hint, _errors: &mut Errors) {
        env.hint_context = NameContext::TraitContext;
        env.hint_allow_typedef = false;
    }

    fn at_xhp_attr_hint(&mut self, env: &mut Env<'a>, _h: &'a nast::Hint, _errors: &mut Errors) {
        env.hint_allow_typedef = false;
    }

    // Below are the methods where we check for unbound names

    fn at_expr(&mut self, env: &mut Env<'a>, e: &'a nast::Expr, errors: &mut Errors) {
        match &e.2 {
            nast::Expr_::FunctionPointer(fp) if matches!(fp.0, nast::FunctionPtrId::FPId(_)) => {
                if let nast::FunctionPtrId::FPId(id) = &fp.0 {
                    self.check_fun_name(id, errors);
                    env.seen_names = cons((id.1.as_str(), &id.0), &env.seen_names);
                }
            }
            nast::Expr_::Call(call) if matches!(call.func.2, nast::Expr_::Id(_)) => {
                if let nast::Expr_::Id(id) = &call.func.2 {
                    self.check_fun_name(id, errors);
                    env.seen_names = cons((id.1.as_str(), &id.0), &env.seen_names);
                }
            }
            nast::Expr_::Id(id) => {
                let nast::Id(p, name) = &**id;
                match find(&env.seen_names, |(seen, _)| seen == name) {
                    Some((_, pos)) if *pos == p => {}
                    _ => self.check_const_name(id, errors),
                }
            }
            nast::Expr_::MethodCaller(mc) => {
                let nast::Id(pos, name) = &mc.0;
                self.check_class_name(env, pos, name, errors);
            }
            nast::Expr_::Xml(xml) => {
                let nast::Id(pos, name) = &xml.0;
                self.check_class_name(env, pos, name, errors);
            }
            nast::Expr_::ClassConst(cc)
                if cc.1.1 == "class" && matches!(cc.0.2, nast::ClassId_::CI(_)) =>
            {
                env.class_id_allow_typedef = true;
            }
            nast::Expr_::Nameof(_) => {
                env.class_id_allow_typedef = true;
            }
            nast::Expr_::ObjGet(og) => {
                if let nast::Expr(_, _, nast::Expr_::Id(id)) = &og.1 {
                    env.seen_names = cons((id.1.as_str(), &id.0), &env.seen_names);
                }
            }
            nast::Expr_::EnumClassLabel(label) => {
                if let Some(nast::Id(pos, name)) = &label.0 {
                    // we might reconsider this ?
                    self.check_class_name(env, pos, name, errors);
                }
            }
            nast::Expr_::Package(pkg) => {
                self.check_package_name(&pkg.0, &pkg.1, errors);
            }
            _ => {}
        }
    }

    fn at_shape_field_name(
        &mut self,
        env: &mut Env<'a>,
        sfn: &'a ShapeFieldName,
        errors: &mut Errors,
    ) {
        if let ShapeFieldName::SFclassConst(nast::Id(pos, name), _) = sfn {
            self.check_class_name(env, pos, name, errors);
        }
    }

    fn at_user_attribute(
        &mut self,
        env: &mut Env<'a>,
        ua: &'a nast::UserAttribute,
        errors: &mut Errors,
    ) {
        let nast::Id(pos, name) = &ua.name;
        if !sn::user_attributes::is_reserved(name) {
            self.check_class_name(env, pos, name, errors);
        }
        for attribute in [
            sn::user_attributes::REQUIRE_PACKAGE,
            sn::user_attributes::PACKAGE_OVERRIDE,
        ] {
            if name == attribute {
                for param in &ua.params {
                    if let nast::Expr(_, pos, nast::Expr_::String(pkg_name)) = param {
                        self.check_package_name(pos, &pkg_name.to_string(), errors);
                    }
                }
            }
        }
    }

    fn at_class_id(&mut self, env: &mut Env<'a>, ci: &'a nast::ClassId, errors: &mut Errors) {
        let nast::Id(pos, name) = match &ci.2 {
            nast::ClassId_::CI(id) => id,
            // TODO(T259578698) eliminate reified lookup shared w/ hint check
            nast::ClassId_::CIreified(id) => id,
            _ => return,
        };
        self.check_type_name(
            env,
            pos,
            name,
            NameContext::ClassContext,
            env.class_id_allow_typedef,
            true,
            errors,
        );
    }

    fn at_catch(&mut self, env: &mut Env<'a>, catch: &'a nast::Catch, errors: &mut Errors) {
        let nast::Id(pos, name) = &catch.0;
        self.check_class_name(env, pos, name, errors);
    }

    fn at_hint(&mut self, env: &mut Env<'a>, h: &'a nast::Hint, errors: &mut Errors) {
        match &*h.1 {
            nast::Hint_::Hfun(hf) => {
                if !hf.tparams.is_empty() {
                    let mut type_params = BTreeMap::clone(&env.type_params);
                    for tparam in &hf.tparams {
                        type_params.insert(tparam.name.1.as_str(), ReifyKind::Erased);
                    }
                    env.type_params = Rc::new(type_params);
                }
            }
            nast::Hint_::Happly(id, _) => {
                self.check_type_hint(
                    env,
                    id,
                    env.hint_context,
                    env.hint_allow_typedef,
                    false,
                    errors,
                );
                // Intentionally set allow_typedef to true for a hint's type
                // parameters because there are no runtime restrictions
                env.hint_allow_typedef = true;
            }
            _ => {}
        }
    }
}
