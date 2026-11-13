// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `enum_check.ml`. See `hh/PORTING.md`.

use oxidized::ast_defs;
use oxidized::s_set::SSet;

use crate::decl_entry;
use crate::folded_class as cls;
use crate::tast;
use crate::tast_env;
use crate::tast_visitor;
use crate::typing_defs::DeclTy;
use crate::typing_defs::DeclTy_;
use crate::typing_error;
use crate::typing_error_utils;

pub fn get_name(dty: &DeclTy) -> Option<String> {
    match dty.node_ref() {
        DeclTy_::Tapply(tapply) if tapply.1.is_empty() => {
            Some(tapply.0.id_ref().as_str().to_string())
        }
        _ => None,
    }
}

/// Check that the base type of an enum or (enum class) is not an alias
/// to the enum being defined:
///
/// ```text
/// enum Foo : Foo {}
/// enum Bar0 : Bar1 {}
/// enum Bar1 : Bar0 {}
/// ```
///
/// Such code would make HHVM fatal.
///
/// Note that we have a similar check for enum/class constants themselves in
/// Cyclic_class_constant but it doesn't take into account the empty enums.
pub fn find_cycle(env: &tast_env::Env, class_name: &str) -> Option<SSet> {
    // Note w.r.t. Cyclic_class_constant:
    // Since `self` is not allowed (parsing error) in this position, we just
    // keep track of the hints we see.
    fn spot_target(env: &tast_env::Env, mut seen: SSet, current: &str) -> Option<SSet> {
        let enum_def = tast_env::get_enum(env, current);
        let enum_info = decl_entry::to_option(enum_def).and_then(|tc| cls::enum_type(&tc));
        let te_base = enum_info.and_then(|info| get_name(&info.base));
        match te_base {
            None => None,
            Some(base) => {
                if seen.contains(&base) {
                    Some(seen)
                } else {
                    seen.insert(base.clone());
                    spot_target(env, seen, &base)
                }
            }
        }
    }
    spot_target(env, SSet::new(), class_name)
}

/// The object `handler`.
struct EnumCheck;

impl<'a> tast_visitor::Handler<'a> for EnumCheck {
    fn at_class_(&mut self, env: &tast_env::Env, c: &'a tast::Class_) {
        let ast_defs::Id(pos, c_name) = &c.name;
        match find_cycle(env, c_name) {
            Some(stack) => typing_error_utils::add_typing_error(
                &typing_error::primary(typing_error::primary::T::Cyclic_class_def {
                    pos: pos.clone(),
                    stack,
                }),
                env,
            ),
            None => {}
        }
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(EnumCheck)
}
