// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `decl/decl_inherit.ml`. See `hh/PORTING.md`.
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
//!   of `OverridePrecedence` and `OrderedParents` it uses).
//!
//! The maps of [`Inherited`] are those of hackrs (`IndexMap`s by the interned
//! names): they are not in the order of the names, as `S_map`s are.

use folded_decl_provider::inherit as hackrs;
pub use folded_decl_provider::inherit::ParentKind;
use hash::IndexMap;
use oxidized::ast_defs::Abstraction;
use oxidized::ast_defs::ClassishKind;
use oxidized::typing_defs_core::CeVisibility;
use oxidized::typing_defs_core::ConsistentKind;
use oxidized::typing_defs_flags::ClassEltFlags;
use pos::ClassConstName;
use pos::MethodName;
use pos::PropName;
use pos::TypeConstName;
use pos::TypeName;
use ty::decl::ClassConst;
use ty::decl::ShallowClass;
use ty::decl::Ty;
use ty::decl::TypeConst;
use ty::decl::ty::DeclConstraintRequirement;

use crate::ctx::R;
use crate::decl_defs::Element;
use crate::decl_defs::SubstContext;
use crate::decl_env::ClassCache;
use crate::folded_class::*;
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
/// (`crate::decl_store::shared_memory_store_of_ctx`), whose
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

// module Typing_defs_class_elt : Member_S with type t = Typing_defs.class_elt

/// `Typing_defs.get_ce_abstract`
fn is_abstract(m: &ClassElt) -> bool {
    m.ce_flags.contains(ClassEltFlags::ABSTRACT)
}

/// `Typing_defs.get_ce_synthesized`
fn is_synthesized(m: &ClassElt) -> bool {
    m.ce_flags.contains(ClassEltFlags::SYNTHESIZED)
}

/// `Typing_defs.get_ce_lsb`
fn has_lsb(m: &ClassElt) -> bool {
    m.ce_flags.contains(ClassEltFlags::LSB)
}

fn visibility(m: &ClassElt) -> &CeVisibility {
    &m.ce_visibility
}

/// The override precedence of a member is used to determine if a member overrides
/// previous members from other parents with the same name.
#[derive(Clone, Copy)]
struct OverridePrecedence {
    is_concrete: bool,
    is_not_synthesized: bool,
}

impl OverridePrecedence {
    fn make(member: &ClassElt) -> Self {
        Self {
            is_concrete: !is_abstract(member),
            is_not_synthesized: !is_synthesized(member),
        }
    }

    fn to_int(self) -> isize {
        let bool_to_int = |b: bool| if b { 1 } else { 0 };
        (2 * bool_to_int(self.is_concrete)) + bool_to_int(self.is_not_synthesized)
    }

    /// `( > )`
    fn gt(self, y: Self) -> bool {
        self.to_int() > y.to_int()
    }

    fn is_highest(self) -> bool {
        self.is_concrete && self.is_not_synthesized
    }
}

fn is_private(member: &ClassElt) -> bool {
    match visibility(member) {
        CeVisibility::Vprivate(_) => !has_lsb(member),
        CeVisibility::Vpublic
        | CeVisibility::Vprotected(_)
        | CeVisibility::Vinternal(_)
        | CeVisibility::VprotectedInternal { .. } => false,
    }
}

fn parents_which_provide_members(c: &ShallowClass<R>) -> Vec<Ty<R>> {
    // /!\ For soundness, the traversal order below
    // must be consistent with traversal order for ancestors
    // used in decl_folded_class.ml
    // In an abstract class or a trait, we assume the interfaces
    // will be implemented in the future, so we take them as
    // part of the class (as requested by dependency injection implementers)
    match c.kind {
        ClassishKind::Cclass(Abstraction::Abstract) => (c.implements.iter())
            .chain(c.extends.iter())
            .cloned()
            .collect(),
        ClassishKind::Ctrait => (c.implements.iter())
            .chain(c.extends.iter())
            .chain(c.req_implements.iter())
            .cloned()
            .collect(),
        ClassishKind::Cclass(_)
        | ClassishKind::Cinterface
        | ClassishKind::Cenum
        | ClassishKind::CenumClass(_) => c.extends.to_vec(),
    }
}

fn has_highest_precedence<A>(x: &Option<(OverridePrecedence, A)>) -> bool {
    match x {
        Some((precedence, _)) => precedence.is_highest(),
        _ => false,
    }
}

fn max_precedence<A>(
    x: Option<(OverridePrecedence, A)>,
    y: Option<(OverridePrecedence, A)>,
) -> Option<(OverridePrecedence, A)> {
    // Option.merge
    match (x, y) {
        (None, y) => y,
        (x, None) => x,
        (Some(x), Some(y)) => {
            let (x_precedence, y_precedence) = (x.0, y.0);
            if y_precedence.gt(x_precedence) {
                Some(y)
            } else {
                Some(x)
            }
        }
    }
}

/// `( >?? )`
fn or_max_precedence<A>(
    x: Option<(OverridePrecedence, A)>,
    y: impl FnOnce() -> Option<(OverridePrecedence, A)>,
) -> Option<(OverridePrecedence, A)> {
    if has_highest_precedence(&x) {
        x
    } else {
        max_precedence(x, y())
    }
}

fn find_first_with_highest_precedence<X, A>(
    l: &[X],
    mut f: impl FnMut(&X) -> Option<(OverridePrecedence, A)>,
) -> Option<(OverridePrecedence, A)> {
    let mut found = None;
    for x in l {
        let x = f(x);
        if has_highest_precedence(&x) {
            return x;
        } else {
            found = max_precedence(found, x)
        }
    }
    found
}

type Parent = Ty<R>;

mod ordered_parents {
    use super::*;

    pub struct T(Vec<(ParentKind, Vec<Parent>)>);

    /// `Shallow_decl_defs.to_decl_constraint`
    fn to_decl_constraint(dcr: &DeclConstraintRequirement<R>) -> Ty<R> {
        match dcr {
            DeclConstraintRequirement::DCREqual(ty)
            | DeclConstraintRequirement::DCRSubtype(ty) => ty.clone(),
        }
    }

    /// This provides the parent traversal order for member folding.
    /// This is appropriate for all members except XHP attributes and constants.
    /// The order is different for those and these are handled elsewhere.
    pub fn get(c: &ShallowClass<R>) -> T {
        // /!\ For soundness, the traversal order below
        // must be consistent with traversal order for ancestors
        // used in decl_folded_class.ml
        T(vec![
            (
                ParentKind::Parent,
                parents_which_provide_members(c).into_iter().rev().collect(),
            ),
            (
                ParentKind::Requirement,
                (c.req_constraints.iter().map(to_decl_constraint))
                    .chain(c.req_extends.iter().cloned())
                    .collect(),
            ),
            (ParentKind::Trait, c.uses.to_vec()),
        ])
    }

    /// Reverse the ordered parents.
    pub fn rev(t: T) -> T {
        T((t.0.into_iter().rev())
            .map(|(parent_kind, parents)| (parent_kind, parents.into_iter().rev().collect()))
            .collect())
    }

    /// Apply [f] to each parent to obtain a result and a precedence.
    /// Return the result with the highest precedence.
    /// If two results have the same highest precedence, return the first one.
    pub fn find_map_first_with_highest_precedence<Res>(
        t: &T,
        mut f: impl FnMut(ParentKind, &Parent) -> Option<(OverridePrecedence, Res)>,
    ) -> Option<(OverridePrecedence, Res)> {
        (t.0.iter()).fold(None, |acc, (parent_kind, parents)| {
            or_max_precedence(acc, || {
                find_first_with_highest_precedence(parents, |parent| f(*parent_kind, parent))
            })
        })
    }
}

/// [find_overridden_method cls ~get_method] finds in the parents and
/// used traits of [cls] a method overridden by [cls].
/// [find_overridden_method cls ~get_method] finds in the parents and
/// used traits of [cls] a method overridden by [cls].
pub fn find_overridden_method(
    cls: &ShallowClass<R>,
    get_method: impl Fn(&Ty<R>) -> Option<ClassElt>,
) -> Option<ClassElt> {
    let is_not_private = |m: &ClassElt| !is_private(m);
    let precedence = OverridePrecedence::make;
    let get_method_with_precedence = |_: ParentKind, ty: &Ty<R>| {
        get_method(ty)
            .filter(is_not_private)
            .map(|method_| (precedence(&method_), method_))
    };
    let parents = ordered_parents::rev(ordered_parents::get(cls));
    ordered_parents::find_map_first_with_highest_precedence(
        &parents,
        get_method_with_precedence,
    )
    .map(|(_, method_)| method_)
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
