// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/nast_check_env.ml`: what the checks know about where they
//! are in a definition.

use oxidized::aast::PackageMembership;
use oxidized::ast_defs::ClassishKind;
use oxidized::ast_defs::FunKind;
use oxidized::ast_defs::Id;
use oxidized::file_info::Mode;
use oxidized::nast;

use crate::ctx::Ctx;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ControlContext {
    Toplevel,
    LoopContext,
    SwitchContext,
}

#[derive(Clone, Copy)]
pub struct Env<'a> {
    pub ctx: &'a Ctx,
    pub classish_kind: Option<ClassishKind>,
    pub class_name: Option<&'a str>,
    pub is_final: bool,
    pub function_name: Option<&'a Id>,
    /// No check reads it (yet).
    #[allow(dead_code)]
    pub file_mode: Mode,
    pub function_kind: Option<FunKind>,
    pub is_finally: bool,
    pub control_context: ControlContext,
    pub array_append_allowed: bool,
    pub module: Option<&'a Id>,
    pub package: Option<&'a PackageMembership>,
}

impl<'a> Env<'a> {
    /// `fun_env`
    pub fn fun_env(&self, f: &'a nast::Fun_) -> Self {
        Self {
            function_kind: Some(f.fun_kind),
            ..*self
        }
    }

    /// `fun_def_env`
    pub fn fun_def_env(&self, fd: &'a nast::FunDef) -> Self {
        Self {
            function_name: Some(&fd.name),
            file_mode: fd.mode,
            module: fd.module.as_ref(),
            package: fd.package.as_ref(),
            ..self.fun_env(&fd.fun)
        }
    }

    /// `method_env`
    pub fn method_env(&self, m: &'a nast::Method_) -> Self {
        Self {
            function_name: Some(&m.name),
            function_kind: Some(m.fun_kind),
            ..*self
        }
    }

    /// `class_env`
    pub fn class_env(&self, c: &'a nast::Class_) -> Self {
        Self {
            classish_kind: Some(c.kind),
            class_name: Some(&c.name.1),
            is_final: c.final_,
            file_mode: c.mode,
            module: c.module.as_ref(),
            package: c.package.as_ref(),
            ..*self
        }
    }

    /// `typedef_env`
    pub fn typedef_env(&self, t: &'a nast::Typedef) -> Self {
        Self {
            file_mode: t.mode,
            module: t.module.as_ref(),
            ..*self
        }
    }

    /// `get_empty_env`
    pub fn get_empty_env(ctx: &'a Ctx) -> Self {
        Self {
            ctx,
            classish_kind: None,
            class_name: None,
            is_final: false,
            function_name: None,
            file_mode: Mode::Mstrict,
            function_kind: None,
            is_finally: false,
            control_context: ControlContext::Toplevel,
            array_append_allowed: false,
            module: None,
            package: None,
        }
    }

    /// `def_env`
    pub fn def_env(ctx: &'a Ctx, def: &'a nast::Def) -> Self {
        let empty = Self::get_empty_env(ctx);
        match def {
            nast::Def::Fun(f) => empty.fun_def_env(f),
            nast::Def::Class(c) => empty.class_env(c),
            nast::Def::Typedef(t) => empty.typedef_env(t),
            nast::Def::ClassAlias(_)
            | nast::Def::SetModule(_)
            | nast::Def::Constant(_)
            | nast::Def::Stmt(_)
            | nast::Def::Namespace(_)
            | nast::Def::NamespaceUse(_)
            | nast::Def::SetNamespaceEnv(_)
            | nast::Def::FileAttributes(_)
            | nast::Def::Module(_) => empty,
        }
    }
}
