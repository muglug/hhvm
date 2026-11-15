// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `decl/decl_folded_class.ml`. See `hh/PORTING.md`.
//!
//! Module used to declare class types.
//! For each class we want to build a complete type, that is the type of
//! the methods defined in the class plus everything that was inherited.
//!
//! A class is folded by hackrs: `folded_decl_provider::fold` follows
//! `class_decl` function by function (`check_extend_kind`,
//! `check_use_kind`, `add_grand_parents_or_traits`,
//! `get_class_parents_and_traits`, `synthesize_typeconst_defaults`,
//! `get_instantiated_ancestors_and_self`, `visibility`, `build_constructor`,
//! `constructor_decl_eager`, `class_const_fold`, `class_class_decl`,
//! `prop_decl_eager`, `typeconst_fold`, `method_decl_eager`, ...), and the
//! `LazyFoldedDeclProvider` of a `Ctx` (`ctx.folded_decls`) does the
//! recursion over the ancestors of `declare_class_and_parents`,
//! `class_parents_decl` and `class_decl_if_missing` for its store. This module
//! gives it the interface of `decl_folded_class.mli`, through `Decl_store`
//! as the OCaml goes: [`class_decl_if_missing`] and [`class_decl`].
//!
//! The member heaps (`Decl_store.class_members`, filled when
//! `Typechecker_options.populate_member_heaps` is set) are built here, as
//! `class_decl` builds them: hackrs's folded classes do not hold the types
//! of their members. `prop_decl_eager`, `static_prop_decl_eager`,
//! `method_decl_eager`, `build_constructor` and `constructor_decl_eager`
//! pair the element that hackrs builds with the member type built here, and
//! run before hackrs folds the class, so that the member heaps are filled
//! before `StringishObject` is declared, as in the OCaml.
//!
//! `~sh:Shared_mem.uses`, the witness that shared memory is initialised, is
//! dropped: it carries nothing and `Shared_mem` has no `uses` in this crate.

use std::sync::Arc;

use folded_decl_provider::fold;
use folded_decl_provider::fold::DeclFolder;
use hash::IndexMap;
use oxidized::decl_fold_options::DeclFoldOptions;
use oxidized::s_map::SMap;
use pos::BPos;
use pos::MethodName;
use pos::PropName;
use pos::TypeName;
use ty::decl::ShallowClass;
use ty::decl::ShallowMethod;
use ty::decl::ShallowProp;
use ty::decl::Ty_;
use ty::decl::folded::Constructor;
use ty::decl::ty::ConsistentKind;

use crate::ctx::Ctx;
use crate::ctx::R;
use crate::decl_defs::DeclClassType;
use crate::decl_defs::DeclError;
use crate::decl_defs::Element;
use crate::decl_env::ClassCache;
use crate::decl_inherit;
use crate::decl_members as members;
use crate::decl_provider_internals;
use crate::decl_store;
use crate::decl_store::ClassMembers;
use crate::typing_defs::FunElt;
use crate::typing_defs_core::DeclTy;
use crate::worker_cancel;

/// `class_entries`
pub type ClassEntries = decl_store::ClassEntries;

pub fn member_heaps_enabled(ctx: &Arc<Ctx>) -> bool {
    // Provider_context.get_tcopt ctx
    let tco = &ctx.tco;
    tco.tco_populate_member_heaps
}

/// `class_env`
#[derive(Clone)]
struct ClassEnv {
    ctx: Arc<Ctx>,
    stack: im::OrdSet<String>,
}

fn check_if_cyclic(class_env: &ClassEnv, (pos, cid): (&BPos, &str)) -> Option<DeclError> {
    let stack = &class_env.stack;
    let is_cyclic = stack.contains(cid);
    if is_cyclic {
        Some(DeclError::CyclicClassDef(
            pos.clone(),
            stack.iter().map(TypeName::new).collect(),
        ))
    } else {
        None
    }
}

fn build_constructor_fun_elt(
    ctx: &Arc<Ctx>,
    elt_origin: &str,
    method_: &ShallowMethod<R>,
) -> FunElt {
    let fe = members::build_constructor(method_);
    if member_heaps_enabled(ctx) {
        (decl_store::get().add_constructor)(elt_origin, fe.clone());
    }
    fe
}

fn build_prop_sprop_ty(
    ctx: &Arc<Ctx>,
    this_class: Option<&Arc<ShallowClass<R>>>,
    is_static: bool,
    elt_origin: &str,
    sp: &ShallowProp<R>,
) -> DeclTy {
    let ty = members::build_property(ctx, this_class, sp);
    if member_heaps_enabled(ctx) {
        let name = sp.name.id().as_str().to_string();
        if is_static {
            (decl_store::get().add_static_prop)(&(elt_origin.to_string(), name), ty.clone())
        } else {
            (decl_store::get().add_prop)(&(elt_origin.to_string(), name), ty.clone())
        }
    }
    ty
}

fn build_method_fun_elt(
    ctx: &Arc<Ctx>,
    this_class: Option<&Arc<ShallowClass<R>>>,
    is_static: bool,
    elt_origin: &str,
    no_auto_likes: bool,
    m: &ShallowMethod<R>,
) -> FunElt {
    let fe = members::build_method(ctx, this_class, no_auto_likes, m);
    if member_heaps_enabled(ctx) {
        let id = m.name.id().as_str().to_string();
        if is_static {
            (decl_store::get().add_static_method)(&(elt_origin.to_string(), id), fe.clone())
        } else {
            (decl_store::get().add_method)(&(elt_origin.to_string(), id), fe.clone())
        }
    }
    fe
}

/// `declare_class_and_parents ~sh class_env shallow_class`
fn declare_class_and_parents(
    class_env: &ClassEnv,
    shallow_class: &Arc<ShallowClass<R>>,
) -> ClassEntries {
    let name = shallow_class.name.id().as_str().to_string();
    let class_env = ClassEnv {
        stack: class_env.stack.update(name),
        ..class_env.clone()
    };
    let (class_, member_heaps_values) = {
        let (parents, errors) = class_parents_decl(&class_env, shallow_class);
        class_decl(&class_env.ctx, shallow_class, &parents, errors)
    };
    (class_, Some(member_heaps_values))
}

/// `class_parents_decl ~sh class_env c`
fn class_parents_decl(class_env: &ClassEnv, c: &ShallowClass<R>) -> (ClassCache, Vec<DeclError>) {
    let class_type_decl = |(mut parents, mut errs): (ClassCache, Vec<DeclError>),
                           class_ty: &DeclTy| {
        match class_ty.node_ref() {
            Ty_::Tapply(id_and_args) => {
                let (pos_id, _) = &**id_and_args;
                let (pos, class_name) = (pos_id.pos(), pos_id.id());
                // `Pos_or_decl.unsafe_to_raw_pos pos`
                match check_if_cyclic(class_env, (pos, class_name.as_str())) {
                    Some(err) => {
                        // err :: errs
                        errs.insert(0, err);
                        (parents, errs)
                    }
                    None => match class_decl_if_missing_in_env(class_env, class_name.as_str()) {
                        None => (parents, errs),
                        Some(decls) => {
                            parents.insert(class_name.as_str().to_string(), decls);
                            (parents, errs)
                        }
                    },
                }
            }
            _ => (parents, errs),
        }
    };
    let acc = (ClassCache::new(), vec![]);
    let acc = c.extends.iter().fold(acc, class_type_decl);
    let acc = c.implements.iter().fold(acc, class_type_decl);
    let acc = c.uses.iter().fold(acc, class_type_decl);
    let acc = c.xhp_attr_uses.iter().fold(acc, class_type_decl);
    let acc = c.req_extends.iter().fold(acc, class_type_decl);
    let acc = c.req_implements.iter().fold(acc, class_type_decl);
    // Aast.enum_includes_map ~f:(fun et -> et.te_includes) c.sc_enum_type
    let enum_includes: &[DeclTy] = match &c.enum_type {
        None => &[],
        Some(et) => &et.includes,
    };
    enum_includes.iter().fold(acc, class_type_decl)
}

/// The `class_decl_if_missing ~sh class_env class_name` of the recursion
/// (the OCaml defines `class_decl_if_missing` twice: this one, and the one
/// of the interface, which shadows it).
fn class_decl_if_missing_in_env(class_env: &ClassEnv, class_name: &str) -> Option<ClassEntries> {
    match (decl_store::get().get_class)(class_name) {
        Some(decl) => Some((decl, None)),
        None => match decl_provider_internals::get_shallow_class(&class_env.ctx, class_name) {
            None => None,
            Some(shallow_class) => {
                let result = declare_class_and_parents(class_env, &shallow_class);
                let (class_, _) = &result;
                (decl_store::get().add_class)(class_name, Arc::clone(class_));
                Some(result)
            }
        },
    }
}

/// `build_constructor ~ctx ~origin_class method_`: the element is built by
/// hackrs (`folded_decl_provider::fold::build_constructor`), the `fun_elt`
/// here.
fn build_constructor(
    ctx: &Arc<Ctx>,
    origin_class: &ShallowClass<R>,
    method_: &ShallowMethod<R>,
) -> Option<(Element, Option<FunElt>)> {
    let class_name = origin_class.name.id();
    let cstr = match fold::build_constructor(origin_class, method_) {
        Some(cstr) => cstr,
        None => panic!("Decl_folded_class.build_constructor: no element"),
    };
    let fe = build_constructor_fun_elt(ctx, class_name.as_str(), method_);
    Some((cstr, Some(fe)))
}

/// `constructor_decl_eager ~sh ~ctx (parent_cstr, pconsist) class_`: the
/// consistency is computed by hackrs (`fold::constructor_decl_eager`).
fn constructor_decl_eager(
    ctx: &Arc<Ctx>,
    (parent_cstr, pconsist): (Option<(Element, Option<FunElt>)>, ConsistentKind),
    class_: &ShallowClass<R>,
) -> (Option<(Element, Option<FunElt>)>, ConsistentKind) {
    // constructors in children of class_ must be consistent?
    // (`Decl_utils.coalesce_consistent pconsist cconsist`)
    let consistency = fold::constructor_decl_eager(
        Constructor::new(parent_cstr.as_ref().map(|(elt, _)| elt.clone()), pconsist),
        class_,
    )
    .consistency;
    let cstr = match &class_.constructor {
        None => parent_cstr,
        Some(method_) => build_constructor(ctx, class_, method_),
    };
    (cstr, consistency)
}

/// `prop_decl_eager ~ctx c acc sp`: the element is built by hackrs
/// (`fold::prop_decl_eager`, which does not look at `acc`), the type here.
fn prop_decl_eager(
    ctx: &Arc<Ctx>,
    c: &Arc<ShallowClass<R>>,
    acc: &mut IndexMap<PropName, (Element, Option<DeclTy>)>,
    sp: &ShallowProp<R>,
) {
    let elt_origin = c.name.id();
    let ty = build_prop_sprop_ty(ctx, Some(c), false, elt_origin.as_str(), sp);
    let mut elts = IndexMap::default();
    fold::prop_decl_eager(c, &mut elts, sp);
    let elt = elts.swap_remove(&sp.name.id()).unwrap();
    acc.insert(sp.name.id(), (elt, Some(ty)));
}

/// `static_prop_decl_eager ~ctx c acc sp`, as [`prop_decl_eager`].
fn static_prop_decl_eager(
    ctx: &Arc<Ctx>,
    c: &Arc<ShallowClass<R>>,
    acc: &mut IndexMap<PropName, (Element, Option<DeclTy>)>,
    sp: &ShallowProp<R>,
) {
    let elt_origin = c.name.id();
    let ty = build_prop_sprop_ty(ctx, Some(c), true, elt_origin.as_str(), sp);
    let mut elts = IndexMap::default();
    fold::static_prop_decl_eager(c, &mut elts, sp);
    let elt = elts.swap_remove(&sp.name.id()).unwrap();
    acc.insert(sp.name.id(), (elt, Some(ty)));
}

/// `method_decl_eager ~ctx ~is_static c acc m`: the element is built by
/// hackrs (`fold::method_decl_eager`, which only looks at the entry of `acc`
/// named as `m`), the `fun_elt` here.
fn method_decl_eager(
    ctx: &Arc<Ctx>,
    is_static: bool,
    c: &Arc<ShallowClass<R>>,
    acc: &mut IndexMap<MethodName, (Element, Option<FunElt>)>,
    m: &ShallowMethod<R>,
) {
    let id = m.name.id();
    let mut elts: IndexMap<MethodName, Element> = (acc.get(&id).into_iter())
        .map(|(elt, _)| (id, elt.clone()))
        .collect();
    fold::method_decl_eager(c, &mut elts, m);
    let elt = elts.swap_remove(&id).unwrap();
    let parent_no_auto_likes = match acc.get(&id) {
        Some((elt, _)) => crate::typing_defs_flags::class_elt::is_no_auto_likes(elt.flags),
        None => false,
    };
    let no_auto_likes = parent_no_auto_likes || m.flags.is_no_auto_likes();
    let fe = build_method_fun_elt(
        ctx,
        Some(c),
        is_static,
        elt.origin.as_str(),
        no_auto_likes,
        m,
    );
    acc.insert(id, (elt, Some(fe)));
}

/// `filter_snd`
fn filter_snd<K: AsRef<str>, E, V>(map: impl IntoIterator<Item = (K, (E, Option<V>))>) -> SMap<V> {
    (map.into_iter())
        .filter_map(|(k, (_, v))| v.map(|v| (k.as_ref().to_string(), v)))
        .collect()
}

/// The elements of the class (`dc_props`, ...) are those of the class that
/// hackrs folds (`DeclFolder::decl_class`, which is the rest of
/// `class_decl`); the members of the member heaps are built here first, in
/// the order of the OCaml, before hackrs declares `StringishObject`.
pub fn class_decl(
    ctx: &Arc<Ctx>,
    c: &Arc<ShallowClass<R>>,
    parents: &ClassCache,
    decl_errors: Vec<DeclError>,
) -> (DeclClassType, ClassMembers) {
    let inherited = decl_inherit::make(c, parents);
    let mut props = inherited.props;
    for sp in c.props.iter() {
        prop_decl_eager(ctx, c, &mut props, sp);
    }
    let mut methods = inherited.methods;
    for m in c.methods.iter() {
        method_decl_eager(ctx, false, c, &mut methods, m);
    }
    let mut static_props = inherited.sprops;
    for sp in c.static_props.iter() {
        static_prop_decl_eager(ctx, c, &mut static_props, sp);
    }
    let mut static_methods = inherited.smethods;
    for m in c.static_methods.iter() {
        method_decl_eager(ctx, true, c, &mut static_methods, m);
    }
    let parent_cstr = inherited.cstr;
    let cstr = constructor_decl_eager(ctx, parent_cstr, c);
    // The folded class, by hackrs. It declares `StringishObject` (`Ensure
    // stringishObject is declared.`) with an empty stack.
    let tc = {
        let opts = DeclFoldOptions::from_global_options(&ctx.tco);
        let parents: fold::Parents<R> = (parents.iter())
            .map(|(name, (decl, _members))| (TypeName::new(name), Arc::clone(decl)))
            .collect();
        let mut class_decl_if_missing = |class_name: TypeName| {
            let class_env = ClassEnv {
                ctx: Arc::clone(ctx),
                stack: im::OrdSet::new(),
            };
            Ok(class_decl_if_missing_in_env(&class_env, class_name.as_str()).map(|(cls, _)| cls))
        };
        match DeclFolder::decl_class(&opts, c, &parents, decl_errors, &mut class_decl_if_missing) {
            Ok(tc) => tc,
            Err(err) => panic!("Decl_folded_class.class_decl: {}", err),
        }
    };
    let member_heaps_values = ClassMembers {
        static_properties: filter_snd(static_props),
        properties: filter_snd(props),
        static_methods: filter_snd(static_methods),
        methods: filter_snd(methods),
        constructor: (cstr.0).and_then(|(_, fe)| fe),
    };
    (tc, member_heaps_values)
}

/// Check if the class is already in the heap, and if not,
/// declare it, its members and its ancestors and add them to
/// their respective shared heaps.
/// Return what has been added in the multiple heaps, i.e. the class
/// heap entry and the entries in the various member heaps. There is no
/// guarantee that it returns all the member heap entries for that class
/// as some might have already been added previously when decling the ancestors.
pub fn class_decl_if_missing(ctx: &Arc<Ctx>, class_name: &str) -> Option<ClassEntries> {
    match (decl_store::get().get_class)(class_name) {
        Some(class_) => Some((class_, None)),
        None => {
            // Class elements are in memory if and only if the class itself is there.
            // Exiting before class declaration is ready would break this invariant
            worker_cancel::with_no_cancellations(|| {
                class_decl_if_missing_in_env(
                    &ClassEnv {
                        ctx: Arc::clone(ctx),
                        stack: im::OrdSet::new(),
                    },
                    class_name,
                )
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use oxidized::typechecker_options::TypecheckerOptions;
    use pos::PropName;

    use super::*;
    use crate::decl_provider::testing::ctx_of;

    const SRC: &str = r#"<?hh
interface I<Ti> {}

abstract class A<Ta1, Ta2> implements I<Ta2> {
  public int $p = 0;
  public function __construct() {}
  public function m(): Ta1 { throw new Exception(); }
  public static function sm(): void {}
}

class B<Tb> extends A<Tb, int> {
  public function m(): Tb { throw new Exception(); }
}

class Cyc1 extends Cyc2 {}
class Cyc2 extends Cyc1 {}
"#;

    fn ctx() -> Arc<Ctx> {
        ctx_of(SRC, TypecheckerOptions::default())
    }

    #[test]
    fn class_decl_folds_with_hackrs_and_builds_the_member_heaps() {
        let ctx = ctx();
        decl_store::set(decl_store::shared_memory_store_of_ctx(Arc::clone(
            &ctx,
        )));
        let b = decl_provider_internals::get_shallow_class(&ctx, "\\B").unwrap();
        let a = (ctx.folded_decls.get_class(TypeName::new("\\A")))
            .unwrap()
            .unwrap();
        let mut parents = ClassCache::new();
        parents.insert("\\A".to_string(), (a, None));
        let (tc, members) = class_decl(&ctx, &b, &parents, vec![]);
        assert_eq!(tc.name, TypeName::new("\\B"));
        assert_eq!(
            tc.ancestors
                .get(&TypeName::new("\\I"))
                .map(|ty| ty.to_string()),
            Some("I<int>".to_string())
        );
        assert!(tc.props.contains_key(&PropName::new("p")));
        // The same as the folded class of the `Ctx`.
        let folded = (ctx.folded_decls.get_class(TypeName::new("\\B")))
            .unwrap()
            .unwrap();
        assert_eq!(*tc, *folded);
        // Only B's own members have entries: those of A were not given.
        assert_eq!(members.methods.keys().collect::<Vec<_>>(), vec!["m"]);
        assert!(members.properties.is_empty() && members.static_methods.is_empty());
        assert!(members.constructor.is_none());
        assert_eq!(members.methods["m"].ty.to_string(), "(function(): Tb)");
    }

    #[test]
    fn class_decl_if_missing_goes_through_the_decl_store() {
        let ctx = ctx();
        decl_store::set(decl_store::shared_memory_store_of_ctx(Arc::clone(
            &ctx,
        )));
        let (b, members) = class_decl_if_missing(&ctx, "\\B").unwrap();
        assert_eq!(b.name, TypeName::new("\\B"));
        assert!(members.is_none());
        assert!(class_decl_if_missing(&ctx, "\\Nope").is_none());
    }

    #[test]
    fn cycles_are_reported_with_the_stack() {
        let ctx = ctx();
        let class_env = ClassEnv {
            ctx: Arc::clone(&ctx),
            stack: ["\\Cyc1".to_string(), "\\Cyc2".to_string()]
                .into_iter()
                .collect(),
        };
        let cyc1 = decl_provider_internals::get_shallow_class(&ctx, "\\Cyc2").unwrap();
        let (parents, errors) = class_parents_decl(&class_env, &cyc1);
        assert!(parents.is_empty());
        match &errors[..] {
            [DeclError::CyclicClassDef(_, stack)] => {
                let stack: Vec<&str> = stack.iter().map(|x| x.as_str()).collect();
                assert_eq!(stack, vec!["\\Cyc1", "\\Cyc2"]);
            }
            errs => panic!("{:?}", errs),
        }
    }
}
