// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_find_type_var.ml`. See `hh/PORTING.md`.
//!
//! Owned by **F1** (plan §7.3; the plan names no owner for this module, which
//! only `Server_symbol_definition` uses).

use oxidized::aast;

use crate::pos::Pos;
use crate::symbol_definition;

/// Is this [def] a class or function that contains this position?
fn cls_or_fun_at_pos<Ex, En>(pos: &Pos, def: &aast::Def<Ex, En>) -> bool {
    match def {
        aast::Def::Fun(fd) => crate::pos::contains(&fd.fun.span, pos),
        aast::Def::Class(c) => crate::pos::contains(&c.span, pos),
        _ => false,
    }
}

/// Find the method that contains [pos], if any.
fn method_at_pos<'a, Ex, En>(
    methods: &'a [aast::Method_<Ex, En>],
    pos: &Pos,
) -> Option<&'a aast::Method_<Ex, En>> {
    methods.iter().find(|m| crate::pos::contains(&m.span, pos))
}

/// Find the type parameter named [name].
fn tparam_with_name<'a, Ex, En>(
    params: &'a [aast::Tparam<Ex, En>],
    name: &str,
) -> Option<&'a aast::Tparam<Ex, En>> {
    params.iter().find(|tp| tp.name.1 == name)
}

fn sym_def_of_tparam<Ex, En>(tp: &aast::Tparam<Ex, En>) -> symbol_definition::T<Pos> {
    let oxidized::ast_defs::Id(pos, name) = &tp.name;
    let name_with_constraints =
        crate::format::asprintf(|fmt| crate::hint_print::pp_tparam(fmt, tp));
    // `String.strip`: the whitespace of `Char.is_whitespace`.
    let name_with_constraints = name_with_constraints
        .trim_matches(|c| matches!(c, ' ' | '\t' | '\n' | '\r' | '\x0b' | '\x0c'))
        .to_string();
    let docblock = if *name == name_with_constraints {
        None
    } else {
        Some(name_with_constraints)
    };
    symbol_definition::T {
        kind: symbol_definition::Kind::TypeVar,
        name: name.clone(),
        pos: pos.clone(),
        span: pos.clone(),
        modifiers: vec![],
        params: None,
        docblock,
        detail: None,
    }
}

/// Find the type param definition corresponding to the type variable
/// [name] at [pos].
fn find_tparam_def<'a, Ex, En>(
    program: &'a [aast::Def<Ex, En>],
    pos: &Pos,
    name: &str,
) -> Option<&'a aast::Tparam<Ex, En>> {
    let def_at_pos = program.iter().find(|def| cls_or_fun_at_pos(pos, def));
    match def_at_pos {
        Some(aast::Def::Fun(fd)) => tparam_with_name(&fd.tparams, name),
        Some(aast::Def::Class(c)) => {
            let class_tparam = tparam_with_name(&c.tparams, name);
            match class_tparam {
                Some(tp) => Some(tp),
                None => {
                    // This type parameter didn't occur on the class, try the
                    // method. Type parameters on methods cannot shadow type
                    // parameters on classes, so we don't need to worry about
                    // clashes.
                    match method_at_pos(&c.methods, pos) {
                        Some(m) => tparam_with_name(&m.tparams, name),
                        None => None,
                    }
                }
            }
        }
        _ => None,
    }
}

pub fn go<Ex, En>(
    program: &[aast::Def<Ex, En>],
    pos: &Pos,
    name: &str,
) -> Option<symbol_definition::T<Pos>> {
    find_tparam_def(program, pos, name).map(sym_def_of_tparam)
}
