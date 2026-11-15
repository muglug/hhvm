// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `decl/decl_requirements.ml`. See `hh/PORTING.md`.
//!
//! The requirements of a class are computed by hackrs's class folding, in
//! `folded_decl_provider::decl_requirements`, which follows
//! `decl_requirements.ml` function by function (`make_substitution`,
//! `flatten_parent_class_reqs`, `declared_class_req`,
//! `declared_class_req_non_strict`, `flatten_parent_class_reqs_non_strict`,
//! `naive_dedup`, `get_class_requirements`). This module gives it the
//! interface of `decl_requirements.mli`.
//!
//! The OCaml looks the ancestors up with `Decl_env.get_class_and_add_dep
//! ~cache:class_cache ~shmem_fallback:false ~fallback:Decl_env.no_fallback`,
//! which only reads the cache and records no dependency: hackrs looks them up
//! in the same classes.

use folded_decl_provider::decl_requirements as hackrs;
use pos::TypeName;
use ty::decl::ShallowClass;

use crate::ctx::R;
use crate::decl_defs::ClassRequirements;
use crate::decl_env;

pub fn get_class_requirements(
    env: &decl_env::Env,
    class_cache: &decl_env::ClassCache,
    shallow_class: &ShallowClass<R>,
) -> ClassRequirements {
    let _ = env;
    let class_cache: hackrs::ClassCache<R> = (class_cache.iter())
        .map(|(name, (decl, _members))| (TypeName::new(name), decl.clone()))
        .collect();
    hackrs::get_class_requirements(&class_cache, shallow_class)
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use oxidized::file_info::Mode;
    use oxidized::typechecker_options::TypecheckerOptions;

    use super::*;
    use crate::ctx::Ctx;
    use crate::decl_provider::testing::ctx_of;
    use crate::decl_provider_internals;

    const SRC: &str = r#"<?hh
class Base {}
interface IReq {}
interface IReq2 extends IReq {}

trait TReq1 {
  require extends Base;
  require implements IReq2;
}

trait TReq2 {
  require extends Base;
}

trait TUses {
  use TReq1;
  use TReq2;
}

class RC1 {}

trait TC1 {
  require this as RC1;
}

trait TC2 {
  use TC1;
}
"#;

    fn ctx() -> Arc<Ctx> {
        ctx_of(SRC, TypecheckerOptions::default())
    }

    fn cache(ctx: &Arc<Ctx>, names: &[&str]) -> decl_env::ClassCache {
        (names.iter())
            .map(|name| {
                let cls = (ctx.folded_decls.get_class(TypeName::new(*name)))
                    .unwrap()
                    .unwrap();
                (name.to_string(), (cls, None))
            })
            .collect()
    }

    fn env(ctx: &Arc<Ctx>) -> decl_env::Env {
        decl_env::Env {
            mode: Mode::Mstrict,
            droot: None,
            droot_member: None,
            ctx: Arc::clone(ctx),
        }
    }

    #[test]
    fn requirements_of_a_trait_that_uses_traits() {
        let ctx = ctx();
        let tuses = decl_provider_internals::get_shallow_class(&ctx, "\\TUses").unwrap();
        let cr = get_class_requirements(&env(&ctx), &cache(&ctx, &["\\TReq1", "\\TReq2"]), &tuses);
        let reqs: Vec<String> = (cr.req_ancestors.iter())
            .map(|req| req.ty.to_string())
            .collect();
        assert_eq!(reqs, vec!["IReq2", "Base"]);
        let mut extends: Vec<&str> = (cr.req_ancestors_extends.iter())
            .map(|x| x.as_str())
            .collect();
        extends.sort();
        assert_eq!(extends, vec!["\\Base", "\\IReq", "\\IReq2"]);
        // The same as the folded class.
        let folded = ctx
            .folded_decls
            .get_class(TypeName::new("\\TUses"))
            .unwrap()
            .unwrap();
        assert_eq!(&folded.req_ancestors[..], &cr.req_ancestors[..]);

        // Without the used traits in the cache, nothing is inherited.
        let cr = get_class_requirements(&env(&ctx), &cache(&ctx, &[]), &tuses);
        assert!(cr.req_ancestors.is_empty() && cr.req_ancestors_extends.is_empty());

        let tc2 = decl_provider_internals::get_shallow_class(&ctx, "\\TC2").unwrap();
        let cr = get_class_requirements(&env(&ctx), &cache(&ctx, &["\\TC1"]), &tc2);
        assert_eq!(cr.req_constraints_ancestors.len(), 1);
    }
}
