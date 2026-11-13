// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `decl_inherit.ml`. See `hh/PORTING.md`.
//!
//! Module dealing with inheritance.
//! When we want to declare a new class, we first have to retrieve all the
//! types that where inherited from their parents.
//!
//! The inheritance of members when a class is folded is done by hackrs, in
//! `folded_decl_provider::inherit`, which follows `decl_inherit.ml` function
//! by function (`should_keep_old_sig`, `add_method`, `add_const`,
//! `add_typeconst`, `add_constructor`, `add_inherited`,
//! `mark_as_synthesized`, `filter_privates`, `chown_private_and_protected`,
//! `inherit_hack_class`, `from_class`, ..., `OrderedParents.get`/`fold`,
//! `make`). This module gives it the interface of `decl_inherit.mli`:
//!
//! - [`make`] is `Decl_inherit.make`;
//! - [`find_overridden_method`] is `Decl_inherit.find_overridden_method`
//!   (with the `Typing_defs_class_elt` instance of `Member_S`, and the parts
//!   of `OverridePrecedence` and `OrderedParents` it uses), which
//!   `crate::folded_class` ports in its module `decl_inherit`.
//!
//! The maps of [`Inherited`] are those of hackrs (`IndexMap`s by the interned
//! names): they are not in the order of the names, as `S_map`s are.

use folded_decl_provider::inherit as hackrs;
pub use folded_decl_provider::inherit::ParentKind;
use hash::IndexMap;
use pos::ClassConstName;
use pos::MethodName;
use pos::PropName;
use pos::TypeConstName;
use pos::TypeName;
use ty::decl::ClassConst;
use ty::decl::ShallowClass;
use ty::decl::TypeConst;
use ty::decl::ty::ConsistentKind;

use crate::ctx::R;
use crate::decl_defs::Element;
use crate::decl_defs::SubstContext;
use crate::decl_env::ClassCache;
/// [find_overridden_method cls ~get_method] finds in the parents and
/// used traits of [cls] a method overridden by [cls].
pub use crate::folded_class::decl_inherit::find_overridden_method;
use crate::typing_defs::FunElt;
use crate::typing_defs_core::DeclTy;

/// `inherited`
#[derive(Clone, Debug)]
pub struct Inherited {
    /// `ih_substs`
    pub substs: IndexMap<TypeName, SubstContext>,
    /// `ih_cstr`
    pub cstr: (Option<(Element, Option<FunElt>)>, ConsistentKind),
    /// `ih_consts`
    pub consts: IndexMap<ClassConstName, ClassConst<R>>,
    /// `ih_typeconsts`
    pub typeconsts: IndexMap<TypeConstName, TypeConst<R>>,
    /// `ih_props`
    pub props: IndexMap<PropName, (Element, Option<DeclTy>)>,
    /// `ih_sprops`
    pub sprops: IndexMap<PropName, (Element, Option<DeclTy>)>,
    /// `ih_methods`
    pub methods: IndexMap<MethodName, (Element, Option<FunElt>)>,
    /// `ih_smethods`
    pub smethods: IndexMap<MethodName, (Element, Option<FunElt>)>,
    /// `ih_support_dynamic_type`
    pub support_dynamic_type: bool,
}

/// `pair_with_heap_entries`: the members of the member heaps that are paired
/// with the elements. hackrs's inheritance does not record which ancestor
/// gave an inherited element, so it cannot find its entry in the member
/// heaps of that ancestor; it does not need to when no ancestor has member
/// heap entries (`Decl_store.class_entries` with `None` members), and they
/// are all `None`. That is always the case with the decl store of a `Ctx`
/// (`crate::decl_store::rust_provider_backend_decl_store`), whose
/// `get_class` folds every class there is.
fn pair_with_heap_entries<K: std::hash::Hash + Eq, A>(
    elts: IndexMap<K, Element>,
) -> IndexMap<K, (Element, Option<A>)> {
    (elts.into_iter())
        .map(|(name, elt)| (name, (elt, None)))
        .collect()
}

/// Builds the [inherited] type by fetching any ancestor from the heap.
/// The [cache] parameter is a map of heap entries we might already have at hand
/// which acts as a cache for the shared heap.
pub fn make(c: &ShallowClass<R>, cache: &ClassCache) -> Inherited {
    if cache.values().any(|(_, members)| members.is_some()) {
        todo!(
            "Decl_inherit.pair_with_heap_entries: hackrs's inheritance \
             (folded_decl_provider::inherit) does not record which ancestor gave an \
             inherited element, to find its member heap entry in the members of that \
             ancestor's Decl_store.class_entries"
        )
    }
    let parents: hackrs::Parents<R> = (cache.iter())
        .map(|(name, (decl, _members))| (TypeName::new(name), decl.clone()))
        .collect();
    let hackrs::Inherited {
        substs,
        props,
        static_props,
        methods,
        static_methods,
        constructor,
        consts,
        type_consts,
        support_dynamic_type,
    } = hackrs::make(c, &parents);
    Inherited {
        substs,
        cstr: (
            constructor.elt.map(|cstr| (cstr, None)),
            constructor.consistency,
        ),
        consts,
        typeconsts: type_consts,
        props: pair_with_heap_entries(props),
        sprops: pair_with_heap_entries(static_props),
        methods: pair_with_heap_entries(methods),
        smethods: pair_with_heap_entries(static_methods),
        support_dynamic_type,
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use oxidized::typechecker_options::TypecheckerOptions;
    use oxidized::typing_defs_flags::ClassEltFlags;
    use ty::decl::CeVisibility;

    use super::*;
    use crate::ctx::Ctx;
    use crate::decl_provider::testing::ctx_of;
    use crate::decl_provider_internals;

    const SRC: &str = r#"<?hh
class Base<T> {
  public function m(): void {}
  private function priv(): void {}
  abstract const type TC;
}

trait Tr {
  require extends Base<mixed>;
  public function from_trait(): void {}
}

class Child extends Base<int> {
  use Tr;
}
"#;

    fn ctx() -> Arc<Ctx> {
        ctx_of(SRC, TypecheckerOptions::default())
    }

    fn cache(ctx: &Arc<Ctx>, names: &[&str]) -> ClassCache {
        (names.iter())
            .map(|name| {
                let cls = (ctx.folded_decls.get_class(TypeName::new(*name)))
                    .unwrap()
                    .unwrap();
                (name.to_string(), (cls, None))
            })
            .collect()
    }

    #[test]
    fn members_and_substitutions_from_parents_requirements_and_traits() {
        let ctx = ctx();
        let child = decl_provider_internals::get_shallow_class(&ctx, "\\Child").unwrap();
        let ih = make(&child, &cache(&ctx, &["\\Base", "\\Tr"]));
        // The substitution of the actual extends wins over the one of the
        // `require extends` of the trait.
        let sc = ih.substs.get(&TypeName::new("\\Base")).unwrap();
        assert_eq!(sc.class_context, TypeName::new("\\Child"));
        assert!(!sc.from_req_extends);
        assert_eq!(
            sc.subst.0.get(&TypeName::new("T")).map(|ty| ty.to_string()),
            Some("int".to_string())
        );
        let (m, heap) = ih.methods.get(&MethodName::new("m")).unwrap();
        assert!(heap.is_none());
        assert_eq!(m.origin, TypeName::new("\\Base"));
        assert!(!m.flags.contains(ClassEltFlags::SYNTHESIZED));
        assert!(ih.methods.get(&MethodName::new("priv")).is_none());
        let (t, _) = ih.methods.get(&MethodName::new("from_trait")).unwrap();
        assert_eq!(t.visibility, CeVisibility::Public);
        assert!(ih.typeconsts.contains_key(&TypeConstName::new("TC")));
        // The folded class has the same members.
        let folded = (ctx.folded_decls.get_class(TypeName::new("\\Child")))
            .unwrap()
            .unwrap();
        let mut names: Vec<&str> = ih.methods.keys().map(|k| k.as_str()).collect();
        names.sort();
        let mut folded_names: Vec<&str> = folded.methods.keys().map(|k| k.as_str()).collect();
        folded_names.sort();
        assert_eq!(names, folded_names);
    }

    #[test]
    fn only_what_is_in_the_cache_is_inherited() {
        let ctx = ctx();
        let child = decl_provider_internals::get_shallow_class(&ctx, "\\Child").unwrap();
        let ih = make(&child, &cache(&ctx, &[]));
        assert!(ih.methods.is_empty() && ih.substs.is_empty());
        assert_eq!(ih.cstr.1, ConsistentKind::Inconsistent);
    }
}
