// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Folding of small Hack classes, checked against what
//! `Decl_folded_class` / `Decl_inherit` / `Decl_requirements` produce.

use std::path::PathBuf;
use std::sync::Arc;

use datastore::NonEvictingStore;
use decl_parser::DeclParser;
use decl_parser::DeclParserOptions;
use oxidized::decl_fold_options::DeclFoldOptions;
use pos::MethodName;
use pos::Positioned;
use pos::Prefix;
use pos::PropName;
use pos::RelativePath;
use pos::RelativePathCtx;
use pos::TypeConstName;
use pos::TypeName;
use shallow_decl_provider::EagerShallowDeclProvider;
use shallow_decl_provider::ShallowDeclStore;
use ty::decl::CeVisibility;
use ty::decl::ClassEltFlags;
use ty::decl::FoldedClass;
use ty::decl::FunParam;
use ty::decl::FunType;
use ty::decl::Prim;
use ty::decl::Tparam;
use ty::decl::Ty;
use ty::decl::Ty_;
use ty::decl::WhereConstraint;
use ty::decl::folded::ConstraintRequirement;
use ty::decl::subst::Subst;
use ty::decl::ty::Capability;
use ty::decl::ty::FunImplicitParams;
use ty::decl::ty::ShapeType;
use ty::decl::ty::ShapeTypeSimple;
use ty::decl_error::DeclError;
use ty::reason::BReason;
use ty::reason::Reason;

use super::FoldedDeclProvider;
use super::LazyFoldedDeclProvider;
use super::Substitution;

type R = BReason;

const SRC: &str = r#"<?hh

interface StringishObject {}

interface I<Ti> {
  const type TI = int;
}

abstract class A<Ta1, Ta2> implements I<Ta2> {
  const int CA = 1;
  <<__NoAutoLikes, __Overlapping("Ta1")>>
  public function __construct() {}
  public function m(): void {}
  protected function prot(): void {}
  private function priv(): void {}
}

class B<Tb> extends A<Tb, int> {}

final class C extends B<string> {
  public function __toString(): string { return ""; }
}

class Base {}
class Base2 {}
interface IReq {}

trait TReq1 {
  require extends Base;
  require implements IReq;
}

trait TReq2 {
  require extends Base;
}

trait TUses {
  use TReq1;
  use TReq2;
}

class RC1 {}
class RC2 {}

trait TC1 {
  require this as RC1;
  require this as RC2;
}

trait TC2 {
  require this as RC2;
}

trait TC3 {
  use TC1;
  use TC2;
}

interface IErr extends Base, Base2 {}

class Cyc1 extends Cyc2 {}
class Cyc2 extends Cyc1 {}

trait TProt {
  protected function p(): void {}
  private function q(): void {}
}

class UsesTProt {
  use TProt;
}
"#;

const MODULE_SRC: &str = r#"<?hh
new module m {}
"#;

const IN_MODULE_SRC: &str = r#"<?hh
module m;

trait TPI {
  protected internal function pi(): void {}
}

class UsesTPI {
  use TPI;
}
"#;

fn provider() -> LazyFoldedDeclProvider<R> {
    let path_ctx = Arc::new(RelativePathCtx {
        root: PathBuf::from("/"),
        hhi: PathBuf::new(),
        dummy: PathBuf::new(),
        tmp: PathBuf::new(),
    });
    let decl_parser = DeclParser::<R>::new(
        Arc::new(file_provider::DiskProvider::new(path_ctx, None)),
        DeclParserOptions::default(),
    );
    let shallow_decls = Arc::new(ShallowDeclStore::with_no_member_stores(
        Arc::new(NonEvictingStore::default()),
        Arc::new(NonEvictingStore::default()),
        Arc::new(NonEvictingStore::default()),
        Arc::new(NonEvictingStore::default()),
        Arc::new(NonEvictingStore::default()),
    ));
    for (name, src) in [
        ("test.php", SRC),
        ("module.php", MODULE_SRC),
        ("in_module.php", IN_MODULE_SRC),
    ] {
        let path = RelativePath::new(Prefix::Root, name);
        let mut decls = decl_parser.parse_with_text(path, src.as_bytes()).unwrap();
        decls.reverse();
        shallow_decls.add_decls(decls).unwrap();
    }
    LazyFoldedDeclProvider::new(
        Arc::new(DeclFoldOptions::default()),
        Arc::new(NonEvictingStore::default()),
        Arc::new(EagerShallowDeclProvider::new(shallow_decls)),
    )
}

fn cls(p: &LazyFoldedDeclProvider<R>, name: &str) -> Arc<FoldedClass<R>> {
    p.get_class(TypeName::new(name)).unwrap().unwrap()
}

fn line(pos: &<R as Reason>::Pos) -> usize {
    oxidized::pos::Pos::from(pos.clone()).info_pos().0
}

#[test]
fn ancestors_have_their_type_arguments() {
    let p = provider();
    let c = cls(&p, "\\C");
    let ancestor = |name: &str| {
        c.ancestors
            .get(&TypeName::new(name))
            .map(|ty| ty.to_string())
    };
    assert_eq!(ancestor("\\B").as_deref(), Some("B<string>"));
    assert_eq!(ancestor("\\A").as_deref(), Some("A<string, int>"));
    assert_eq!(ancestor("\\I").as_deref(), Some("I<int>"));
    // `__toString` makes `StringishObject` an ancestor.
    assert_eq!(
        ancestor("\\StringishObject").as_deref(),
        Some("StringishObject")
    );
    let b = cls(&p, "\\B");
    assert_eq!(
        (b.ancestors.get(&TypeName::new("\\A"))).map(|ty| ty.to_string()),
        Some("A<Tb, int>".to_string())
    );
    assert_eq!(b.ancestors.get(&TypeName::new("\\StringishObject")), None);
}

#[test]
fn substitutions_lead_back_to_the_origin_of_members() {
    let p = provider();
    let c = cls(&p, "\\C");
    // The substitution of A in C is the one of `B<Tb> extends A<Tb, int>`,
    // in the context of B.
    let sc = c.substs.get(&TypeName::new("\\A")).unwrap();
    assert_eq!(sc.class_context, TypeName::new("\\B"));
    assert!(!sc.from_req_extends);
    let subst: Vec<(String, String)> = (sc.subst.0.iter())
        .map(|(k, v)| (k.as_str().to_string(), v.to_string()))
        .collect();
    assert_eq!(
        subst,
        vec![
            ("Ta1".to_string(), "Tb".to_string()),
            ("Ta2".to_string(), "int".to_string())
        ]
    );
    let sc = c.substs.get(&TypeName::new("\\B")).unwrap();
    assert_eq!(sc.class_context, TypeName::new("\\C"));
    // Inherited members keep their origin; private ones are not inherited.
    let m = c.methods.get(&MethodName::new("m")).unwrap();
    assert_eq!(m.origin, TypeName::new("\\A"));
    assert!(c.methods.get(&MethodName::new("priv")).is_none());
    assert!(matches!(
        c.methods.get(&MethodName::new("prot")).unwrap().visibility,
        CeVisibility::Protected(cls) if cls == TypeName::new("\\A")
    ));
    // Constants are inherited.
    assert!(c.consts.contains_key(&pos::ClassConstName::new("CA")));
    assert!(c.type_consts.contains_key(&TypeConstName::new("TI")));
}

#[test]
fn constructors() {
    let p = provider();
    let a = cls(&p, "\\A");
    let cstr = a.constructor.elt.as_ref().unwrap();
    // `build_constructor`: `~no_auto_likes:(sm_no_auto_likes method_)` and
    // `elt_overlapping_tparams = get_overlapping_tparams method_`.
    assert!(cstr.flags.contains(ClassEltFlags::NO_AUTO_LIKES));
    assert_eq!(
        cstr.overlapping_tparams
            .as_ref()
            .map(|s| s.iter().map(|x| x.as_str().to_string()).collect::<Vec<_>>()),
        Some(vec!["Ta1".to_string()])
    );
    let c = cls(&p, "\\C");
    assert_eq!(
        c.constructor.elt.as_ref().map(|e| e.origin),
        Some(TypeName::new("\\A"))
    );
    assert!(c.has_concrete_constructor());
}

#[test]
fn requirements_are_in_the_order_of_the_ocaml_lists() {
    let p = provider();
    let tuses = cls(&p, "\\TUses");
    // `naive_dedup` keeps the requirement on `Base` that came last (through
    // `TReq2`), and the list is in the order the requirements were found.
    let reqs: Vec<(String, usize)> = (tuses.req_ancestors.iter())
        .map(|req| (req.ty.to_string(), line(&req.pos)))
        .collect();
    assert_eq!(
        reqs,
        vec![("IReq".to_string(), 38), ("Base".to_string(), 39)]
    );
    let mut extends: Vec<&str> = tuses
        .req_ancestors_extends
        .iter()
        .map(|x| x.as_str())
        .collect();
    extends.sort();
    assert_eq!(extends, vec!["\\Base", "\\IReq"]);

    // `require this as`: each one is consed, and those of the used traits
    // are `rev_map_append`ed, without a final reversal.
    let tc1 = cls(&p, "\\TC1");
    let names = |c: &FoldedClass<R>| -> Vec<String> {
        (c.req_constraints_ancestors.iter())
            .map(|cr| match cr {
                ConstraintRequirement::CREqual(req) => format!("= {}", req.ty),
                ConstraintRequirement::CRSubtype(req) => format!("as {}", req.ty),
            })
            .collect()
    };
    assert_eq!(names(&tc1), vec!["as RC2", "as RC1"]);
    let tc3 = cls(&p, "\\TC3");
    assert_eq!(names(&tc3), vec!["as RC2", "as RC1", "as RC2"]);
    let lines: Vec<usize> = (tc3.req_constraints_ancestors.iter())
        .map(|cr| match cr {
            ConstraintRequirement::CREqual(req) | ConstraintRequirement::CRSubtype(req) => {
                line(&req.pos)
            }
        })
        .collect();
    // `use TC2;` is on line 56, `use TC1;` on line 55.
    assert_eq!(lines, vec![56, 55, 55]);
}

#[test]
fn decl_errors_are_in_the_order_of_the_ocaml_list() {
    let p = provider();
    let ierr = cls(&p, "\\IErr");
    let parents: Vec<&str> = (ierr.decl_errors.iter())
        .map(|err| match err {
            DeclError::WrongExtendKind { parent_name, .. } => parent_name.as_str(),
            _ => panic!("{:?}", err),
        })
        .collect();
    assert_eq!(parents, vec!["\\Base2", "\\Base"]);

    let _ = cls(&p, "\\Cyc1");
    let cyc2 = cls(&p, "\\Cyc2");
    match &cyc2.decl_errors[..] {
        [DeclError::CyclicClassDef(_, stack)] => {
            let stack: Vec<&str> = stack.iter().map(|x| x.as_str()).collect();
            assert_eq!(stack, vec!["\\Cyc1", "\\Cyc2"]);
        }
        errs => panic!("{:?}", errs),
    }
}

#[test]
fn traits_give_their_private_and_protected_members_to_the_class() {
    let p = provider();
    let c = cls(&p, "\\UsesTProt");
    let vis = |name: &str| {
        c.methods
            .get(&MethodName::new(name))
            .unwrap()
            .visibility
            .clone()
    };
    assert_eq!(
        vis("p"),
        CeVisibility::Protected(TypeName::new("\\UsesTProt"))
    );
    assert_eq!(
        vis("q"),
        CeVisibility::Private(TypeName::new("\\UsesTProt"))
    );
    assert!(c.props.get(&PropName::new("nope")).is_none());
}

#[test]
fn traits_give_their_protected_internal_members_to_the_class() {
    let p = provider();
    let c = cls(&p, "\\UsesTPI");
    let vis = c
        .methods
        .get(&MethodName::new("pi"))
        .unwrap()
        .visibility
        .clone();
    assert_eq!(
        vis,
        CeVisibility::ProtectedInternal(TypeName::new("\\UsesTPI"), pos::ModuleName::new("m"))
    );
}

fn generic(name: &str) -> Ty<R> {
    Ty::generic(R::none(), TypeName::new(name))
}

fn tparam(name: &str) -> Tparam<R, Ty<R>> {
    Tparam {
        variance: oxidized::ast_defs::Variance::Invariant,
        name: Positioned::new(<R as Reason>::Pos::none(), TypeName::new(name)),
        constraints: Box::new([]),
        reified: oxidized::aast_defs::ReifyKind::Erased,
        user_attributes: Box::new([]),
    }
}

fn param(ty: Ty<R>) -> FunParam<R, Ty<R>> {
    FunParam {
        pos: <R as Reason>::Pos::none(),
        name: None,
        ty,
        flags: ty::decl::ty::FunParamFlags::empty(),
        def_value: None,
    }
}

#[test]
fn instantiation_renames_the_type_parameters_of_functions() {
    // `class Base<T> { public function cast<TF>(T $x): TF where TF as T; }`
    // seen from `class Derived<TF> extends Base<TF>`: T := TF.
    let ft = Ty::new(
        R::none(),
        Ty_::Tfun(Box::new(FunType {
            tparams: Box::new([tparam("TF")]),
            where_constraints: Box::new([WhereConstraint(
                generic("TF"),
                oxidized::ast_defs::ConstraintKind::ConstraintAs,
                generic("T"),
            )]),
            params: Box::new([param(generic("T"))]),
            implicit_params: FunImplicitParams {
                capability: Capability::CapDefaults(<R as Reason>::Pos::none()),
            },
            ret: generic("TF"),
            flags: ty::decl::ty::FunTypeFlags::empty(),
            instantiated: false,
        })),
    );
    let subst = Subst(std::iter::once((TypeName::new("T"), generic("TF"))).collect());
    let substitution = Substitution { subst: &subst };
    let Ty_::Tfun(ft) = substitution.instantiate(&ft).node_ref().clone() else {
        panic!()
    };
    assert_eq!(ft.tparams[0].name.id(), TypeName::new("TF#0"));
    assert_eq!(ft.params[0].ty.to_string(), "TF");
    assert_eq!(ft.ret.to_string(), "TF#0");
    let WhereConstraint(ty1, _, ty2) = &ft.where_constraints[0];
    assert_eq!(
        (ty1.to_string(), ty2.to_string()),
        ("TF#0".to_string(), "TF".to_string())
    );

    // A function's own type parameter shadows the one of the class, on both
    // sides of its where constraints.
    let ft = Ty::new(
        R::none(),
        Ty_::Tfun(Box::new(FunType {
            tparams: Box::new([tparam("T")]),
            where_constraints: Box::new([WhereConstraint(
                generic("T"),
                oxidized::ast_defs::ConstraintKind::ConstraintAs,
                generic("T"),
            )]),
            params: Box::new([]),
            implicit_params: FunImplicitParams {
                capability: Capability::CapDefaults(<R as Reason>::Pos::none()),
            },
            ret: generic("T"),
            flags: ty::decl::ty::FunTypeFlags::empty(),
            instantiated: false,
        })),
    );
    let int = Ty::prim(R::none(), Prim::Tint);
    let subst = Subst(std::iter::once((TypeName::new("T"), int)).collect());
    let substitution = Substitution { subst: &subst };
    let Ty_::Tfun(ft) = substitution.instantiate(&ft).node_ref().clone() else {
        panic!()
    };
    let WhereConstraint(ty1, _, ty2) = &ft.where_constraints[0];
    assert_eq!(
        (ty1.to_string(), ty2.to_string()),
        ("T".to_string(), "T".to_string())
    );
    assert_eq!(ft.ret.to_string(), "T");
}

#[test]
fn instantiation_leaves_the_unknown_fields_of_shapes_alone() {
    let shape = Ty::new(
        R::none(),
        Ty_::Tshape(Box::new(ShapeType::Simple(ShapeTypeSimple(
            generic("T"),
            Default::default(),
        )))),
    );
    let int = Ty::prim(R::none(), Prim::Tint);
    let subst = Subst(std::iter::once((TypeName::new("T"), int)).collect());
    let substitution = Substitution { subst: &subst };
    match substitution.instantiate(&shape).node_ref() {
        Ty_::Tshape(s) => match &**s {
            ShapeType::Simple(ShapeTypeSimple(kind, _)) => {
                assert!(matches!(kind.node_ref(), Ty_::Tgeneric(n) if *n == TypeName::new("T")))
            }
            ShapeType::Splat(_) => panic!(),
        },
        _ => panic!(),
    }
}

#[test]
fn equality_of_requirements_ignores_what_ty_compare_ignores() {
    use super::decl_requirements::equal::equal_decl_ty;
    let p1 = FunParam {
        name: Some(pos::Symbol::new("$x")),
        ..param(generic("T"))
    };
    let p2 = FunParam {
        name: Some(pos::Symbol::new("$y")),
        ..param(generic("T"))
    };
    let fun = |p: FunParam<R, Ty<R>>| {
        Ty::new(
            R::none(),
            Ty_::Tfun(Box::new(FunType {
                tparams: Box::new([]),
                where_constraints: Box::new([]),
                params: Box::new([p]),
                implicit_params: FunImplicitParams {
                    capability: Capability::CapDefaults(<R as Reason>::Pos::none()),
                },
                ret: generic("T"),
                flags: ty::decl::ty::FunTypeFlags::empty(),
                instantiated: false,
            })),
        )
    };
    // The names of parameters that are not named do not count.
    assert!(equal_decl_ty(&fun(p1), &fun(p2)));
    assert!(!equal_decl_ty(&generic("T"), &generic("U")));
    assert!(equal_decl_ty(
        &Ty::any(R::none()),
        &Ty::any(R::witness_from_decl(<R as Reason>::Pos::none()))
    ));
}
