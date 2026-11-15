// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `deps/utils/dep_hash_to_symbol.ml`. See `hh/PORTING.md`.
//!
//! The OCaml's `Aast.reduce` visitor only maps the definitions and the class
//! members (the nodes it overrides): here they are walked directly. Its
//! `DepMap.union ~combine:report_collision` fails on any hash present twice;
//! so does the insertion here.

use std::collections::BTreeMap;

use oxidized::aast;
use oxidized::nast;

use crate::typing_deps::dep;
use crate::typing_deps::dep::Variant;

pub type DepMap = BTreeMap<dep::T, Variant>;

fn report_collision(hash: dep::T, sym1: &Variant, sym2: &Variant) -> ! {
    panic!(
        "Failure: Hash collision detected! Hash: {}; Symbols: {}, {}",
        dep::to_hex_string(hash),
        dep::variant_to_string(sym1),
        dep::variant_to_string(sym2)
    )
}

fn add(map: &mut DepMap, variant: Variant) {
    let dep = dep::make(&variant);
    match map.get(&dep) {
        Some(existing) => report_collision(dep, &variant, existing),
        None => {
            map.insert(dep, variant);
        }
    }
}

fn from_defs(map: &mut DepMap, defs: &[nast::Def]) {
    for def in defs {
        match def {
            aast::Def::Fun(fd) => add(map, Variant::Fun(fd.name.1.clone())),
            aast::Def::Class(x) => {
                let c = &x.name.1;
                add(map, Variant::Type(c.clone()));
                add(map, Variant::Constructor(c.clone()));
                add(map, Variant::Extends(c.clone()));
                add(map, Variant::AllMembers(c.clone()));
                for cc in &x.consts {
                    add(map, Variant::Const(c.clone(), cc.id.1.clone()))
                }
                for tc in &x.typeconsts {
                    add(map, Variant::Const(c.clone(), tc.name.1.clone()))
                }
                for cv in &x.vars {
                    if cv.is_static {
                        add(map, Variant::SProp(c.clone(), cv.id.1.clone()))
                    } else {
                        add(map, Variant::Prop(c.clone(), cv.id.1.clone()))
                    }
                }
                for m in &x.methods {
                    if m.static_ {
                        add(map, Variant::SMethod(c.clone(), m.name.1.clone()))
                    } else {
                        add(map, Variant::Method(c.clone(), m.name.1.clone()))
                    }
                }
            }
            aast::Def::Typedef(t) => add(map, Variant::Type(t.name.1.clone())),
            aast::Def::Constant(cst) => add(map, Variant::GConst(cst.name.1.clone())),
            aast::Def::Namespace(x) => from_defs(map, &x.1),
            _ => {}
        }
    }
}

pub fn from_nast(nast: &nast::Program) -> DepMap {
    let mut map = DepMap::new();
    from_defs(&mut map, &nast.0);
    map
}

pub fn dump(nast: &nast::Program) {
    let map = from_nast(nast);
    for (dep, variant) in &map {
        println!("{} {}", dep::to_hex_string(*dep), dep::variant_to_string(variant));
    }
}
