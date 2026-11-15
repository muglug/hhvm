// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! No OCaml counterpart: unit tests of `typing_print`.
//!
//! The expected strings marked `// exp` occur in the expected outputs of
//! `hphp/hack/test/typecheck`, as a printed type (after "Expected" or "But
//! got", or in another message) or as a part of one: the test builds a type
//! that prints that way and compares. The others, and all the decl types,
//! were written from the OCaml alone.

use oxidized::ast_defs::Variance;
use oxidized::typing_defs_core::PosByteString;
use oxidized::typing_defs_core::PosString;

use super::locl::*;
use super::*;

// ~~ Building locl types ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

fn mk(node: Ty_) -> Ty {
    super::mk(reason::none(), node)
}

/// `Tfun ft`: the port shares the function type (`Rc<FunType>`), the
/// provisional definitions of `locl.rs` do not.
fn tfun(ft: FunType) -> Ty_ {
    #[cfg(feature = "port")]
    let ft = std::rc::Rc::new(ft);
    Ty_::Tfun(ft)
}

fn prim(p: Tprim) -> Ty {
    mk(Ty_::Tprim(p))
}

fn int() -> Ty {
    prim(Tprim::Tint)
}

fn bool_() -> Ty {
    prim(Tprim::Tbool)
}

fn float() -> Ty {
    prim(Tprim::Tfloat)
}

fn num() -> Ty {
    prim(Tprim::Tnum)
}

fn arraykey() -> Ty {
    prim(Tprim::Tarraykey)
}

fn void() -> Ty {
    prim(Tprim::Tvoid)
}

fn null() -> Ty {
    prim(Tprim::Tnull)
}

fn class(name: &str, targs: Vec<Ty>) -> Ty {
    mk(Ty_::Tclass((Pos::NONE, name.to_string()), nonexact(), targs))
}

fn string() -> Ty {
    class("\\HH\\string", vec![])
}

fn nonnull() -> Ty {
    mk(Ty_::Tnonnull)
}

fn mixed() -> Ty {
    mk(Ty_::Toption(nonnull()))
}

fn dynamic() -> Ty {
    mk(Ty_::Tdynamic(None))
}

fn nothing() -> Ty {
    mk(Ty_::Tunion(vec![]))
}

fn any() -> Ty {
    mk(Ty_::Tany(oxidized::tany_sentinel::TanySentinel))
}

fn option(ty: Ty) -> Ty {
    mk(Ty_::Toption(ty))
}

fn union(tyl: Vec<Ty>) -> Ty {
    mk(Ty_::Tunion(tyl))
}

fn inter(tyl: Vec<Ty>) -> Ty {
    mk(Ty_::Tintersection(tyl))
}

fn like(ty: Ty) -> Ty {
    union(vec![dynamic(), ty])
}

fn generic(name: &str) -> Ty {
    mk(Ty_::Tgeneric(name.to_string()))
}

fn newtype(name: &str, targs: Vec<Ty>) -> Ty {
    mk(Ty_::Tnewtype(name.to_string(), targs, mixed()))
}

fn supportdyn(ty: Ty) -> Ty {
    mk(Ty_::Tnewtype(
        "\\HH\\supportdyn".to_string(),
        vec![ty.clone()],
        ty,
    ))
}

fn tvar(n: Tvid) -> Ty {
    mk(Ty_::Tvar(n))
}

fn dependent(n: isize, ty: Ty) -> Ty {
    mk(Ty_::Tdependent(DependentType::DTexpr(n), ty))
}

fn tuple(required: Vec<Ty>) -> Ty {
    tuple_with(required, vec![], TupleExtra::Tvariadic(nothing()))
}

fn tuple_with(required: Vec<Ty>, optional: Vec<Ty>, extra: TupleExtra) -> Ty {
    mk(Ty_::Ttuple(TupleType {
        required,
        optional,
        extra,
    }))
}

fn lit(name: &str) -> TShapeField {
    TShapeField(TshapeFieldName::TSFlitStr(PosByteString(
        Pos::NONE,
        name.into(),
    )))
}

/// A shape with fields `(name, optional, type)`.
fn shape(fields: Vec<(&str, bool, Ty)>, unknown_value: Ty) -> Ty {
    mk(Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
        origin: TypeOrigin::MissingOrigin,
        unknown_value,
        fields: fields
            .into_iter()
            .map(|(name, optional, ty)| (lit(name), ShapeFieldType { optional, ty }))
            .collect(),
    })))
}

fn param(name: Option<&str>, ty: Ty, flags: FunParamFlags) -> FunParam {
    FunParam {
        pos: Pos::NONE,
        name: name.map(|s| s.to_string()),
        type_: ty,
        flags,
        def_value: None,
    }
}

fn tparam(name: &str, constraints: Vec<(ConstraintKind, Ty)>) -> Tparam {
    Tparam {
        variance: Variance::Invariant,
        name: (Pos::NONE, name.to_string()),
        constraints,
        reified: ReifyKind::Erased,
        user_attributes: vec![],
    }
}

fn fun_type(params: Vec<FunParam>, ret: Ty) -> FunType {
    FunType {
        tparams: vec![],
        where_constraints: vec![],
        params,
        implicit_params: FunImplicitParams {
            capability: Capability::CapDefaults(Pos::NONE),
        },
        ret,
        flags: FunTypeFlags::empty(),
        instantiated: true,
    }
}

fn fun(params: Vec<FunParam>, ret: Ty) -> Ty {
    mk(tfun(fun_type(params, ret)))
}

fn neg(p: TypePredicate_) -> Ty {
    mk(Ty_::Tneg(pred(p)))
}

fn pred(p: TypePredicate_) -> TypePredicate {
    TypePredicate(reason::none(), p)
}

fn class_tag(name: &str, generics: Vec<TypeTagGeneric>) -> TypePredicate_ {
    TypePredicate_::IsTag(TypeTag::ClassTag(name.to_string(), generics))
}

fn refined(name: &str, consts: Vec<(&str, RefinedConst)>) -> Ty {
    mk(Ty_::Tclass(
        (Pos::NONE, name.to_string()),
        Exact::Nonexact(ClassRefinement {
            cr_consts: consts
                .into_iter()
                .map(|(name, rc)| (name.to_string(), rc))
                .collect(),
        }),
        vec![],
    ))
}

fn env() -> SimpleEnv {
    SimpleEnv::default()
}

/// The type as an error message has it.
fn show(ty: &Ty) -> String {
    full_strip_ns(true, &env(), ty)
}

// ~~ Locl types ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

#[test]
fn primitives_and_top_bottom() {
    assert_eq!(show(&int()), "int"); // exp
    assert_eq!(show(&bool_()), "bool"); // exp
    assert_eq!(show(&float()), "float"); // exp
    assert_eq!(show(&num()), "num"); // exp
    assert_eq!(show(&arraykey()), "arraykey"); // exp
    assert_eq!(show(&void()), "void"); // exp
    assert_eq!(show(&null()), "null"); // exp
    assert_eq!(show(&prim(Tprim::Tnoreturn)), "noreturn");
    assert_eq!(show(&prim(Tprim::Tresource)), "resource");
    assert_eq!(show(&string()), "string"); // exp
    assert_eq!(show(&mixed()), "mixed"); // exp
    assert_eq!(show(&inter(vec![])), "mixed");
    assert_eq!(show(&nonnull()), "nonnull"); // exp
    assert_eq!(show(&dynamic()), "dynamic"); // exp
    assert_eq!(show(&nothing()), "nothing"); // exp
    assert_eq!(show(&any()), "_");
    assert_eq!(show(&mk(Ty_::Tlabel("StringE".to_string()))), "#StringE"); // exp
}

#[test]
fn options_unions_and_likes() {
    assert_eq!(show(&option(int())), "?int"); // exp
    assert_eq!(show(&option(any())), "?_"); // exp
    // The extra option is dropped.
    assert_eq!(show(&option(option(int()))), "?int");
    assert_eq!(show(&like(int())), "~int"); // exp
    assert_eq!(show(&like(any())), "~_"); // exp
    assert_eq!(show(&like(nonnull())), "~nonnull"); // exp
    assert_eq!(show(&union(vec![null(), int()])), "?int");
    assert_eq!(show(&union(vec![null()])), "null");
    assert_eq!(show(&union(vec![dynamic()])), "dynamic");
    assert_eq!(show(&union(vec![dynamic(), null()])), "~null");
    assert_eq!(show(&union(vec![int(), null(), dynamic()])), "~?int"); // exp
    // An option of a like type is printed as the union with null.
    assert_eq!(show(&option(like(int()))), "~?int");
    assert_eq!(show(&union(vec![int()])), "int");
    // The members are sorted (`Typing_set`) whatever their order in the type,
    // and duplicates are dropped.
    assert_eq!(show(&union(vec![string(), int()])), "(int | string)"); // exp
    assert_eq!(show(&union(vec![int(), string(), int()])), "(int | string)");
    assert_eq!(
        show(&class("\\HH\\vec", vec![union(vec![string(), int()])])),
        "vec<(int | string)>"
    ); // exp
    assert_eq!(
        show(&union(vec![
            neg(TypePredicate_::IsTag(TypeTag::ArraykeyTag)),
            int()
        ])),
        "(int | not arraykey)"
    ); // exp
    assert_eq!(
        show(&option(union(vec![
            class("\\C", vec![]),
            dependent(25, class("\\E", vec![]))
        ]))),
        "?(<expr#25> as E | C)"
    ); // exp
    assert_eq!(show(&option(union(vec![tvar(1), int()]))), "?(int | _)"); // exp
    assert_eq!(
        show(&option(union(vec![
            inter(vec![
                neg(TypePredicate_::IsTag(TypeTag::NumTag)),
                nonnull()
            ]),
            arraykey(),
            float(),
        ]))),
        "?(float | arraykey | (not num & nonnull))"
    ); // exp
    assert_eq!(
        show(&union(vec![
            dynamic(),
            class("\\A", vec![]),
            class("\\B", vec![])
        ])),
        "~(A | B)"
    );
    assert_eq!(
        show(&union(vec![
            dynamic(),
            null(),
            class("\\A", vec![]),
            class("\\B", vec![])
        ])),
        "~?(A | B)"
    );
    assert_eq!(
        show(&like(tuple(vec![int(), int()]))),
        "~(int, int)"
    ); // exp
}

#[test]
fn verbose_unions() {
    // hh_log_level('show', 2)
    let mut env = env();
    env.log_levels.insert("show".to_string(), 2);
    let show = |ty: &Ty| full_strip_ns(true, &env, ty);
    assert_eq!(show(&union(vec![int()])), "(int)");
    assert_eq!(show(&union(vec![null()])), "(null)");
    assert_eq!(show(&union(vec![dynamic()])), "(dynamic)");
    assert_eq!(show(&union(vec![null(), int()])), "(null |int)");
    assert_eq!(show(&like(int())), "(dynamic |int)");
    assert_eq!(show(&union(vec![dynamic(), null()])), "(dynamic | null)");
    assert_eq!(
        show(&union(vec![dynamic(), null(), int()])),
        "(dynamic | null |int)"
    );
    // A solved type variable shows its number.
    env.tyvars.insert(3, int());
    assert_eq!(full_strip_ns(true, &env, &tvar(3)), "#3int");
}

#[test]
fn intersections() {
    assert_eq!(
        show(&inter(vec![generic("T2"), generic("T1")])),
        "(T2 & T1)"
    ); // exp
    assert_eq!(show(&inter(vec![int()])), "int");
    assert_eq!(
        show(&inter(vec![
            class("\\HH\\vec", vec![mixed()]),
            tuple(vec![int(), arraykey()])
        ])),
        "(vec<mixed> & (int, arraykey))"
    ); // exp
    assert_eq!(
        show(&class(
            "\\HH\\Map",
            vec![inter(vec![arraykey(), tvar(1)]), tvar(2)]
        )),
        "Map<(arraykey & _), _>"
    ); // exp
    let wildcard = |n| TypeTagGeneric::Wildcard(n);
    assert_eq!(
        show(&option(inter(vec![
            nonnull(),
            neg(class_tag("\\HH\\AnyArray", vec![wildcard(1), wildcard(2)]))
        ]))),
        "?(nonnull & not AnyArray<_, _>)"
    ); // exp
    assert_eq!(
        show(&option(inter(vec![
            neg(class_tag("\\HH\\dict", vec![wildcard(1), wildcard(2)])),
            nonnull(),
            neg(class_tag("\\HH\\vec", vec![wildcard(3)]))
        ]))),
        "?(not dict<_, _> & nonnull & not vec<_>)"
    ); // exp
    assert_eq!(
        show(&inter(vec![
            class("\\HH\\dict", vec![arraykey(), mixed()]),
            shape(vec![("a", false, int())], nothing())
        ])),
        "(dict<arraykey, mixed> & shape('a' => int))"
    ); // exp
}

#[test]
fn classes_newtypes_and_names() {
    assert_eq!(show(&class("\\C", vec![])), "C"); // exp
    assert_eq!(show(&class("\\HH\\vec", vec![int()])), "vec<int>"); // exp
    assert_eq!(
        show(&class("\\Generator", vec![any(), any(), any()])),
        "Generator<_, _, _>"
    ); // exp
    assert_eq!(show(&class("\\N\\C", vec![])), "N\\C");
    // Only the names that are imported automatically lose `HH\`.
    assert_eq!(
        show(&newtype("\\HH\\FunctionRef", vec![any()])),
        "HH\\FunctionRef<_>"
    ); // exp
    assert_eq!(
        show(&newtype(
            "\\HH\\class_or_classname",
            vec![class("\\C", vec![])]
        )),
        "HH\\class_or_classname<C>"
    ); // exp
    assert_eq!(show(&newtype("\\FooType", vec![])), "FooType");
    assert_eq!(
        show(&newtype("\\HH\\classname", vec![class("\\C", vec![])])),
        "classname<C>"
    );
    assert_eq!(show(&supportdyn(mixed())), "supportdyn<mixed>"); // exp
    assert_eq!(
        show(&mk(Ty_::TclassPtr(class("\\A", vec![])))),
        "class<A>"
    ); // exp
    assert_eq!(show(&mk(Ty_::TclassPtr(mixed()))), "class<mixed>"); // exp
    assert_eq!(
        show(&mk(Ty_::TvecOrDict(int(), string()))),
        "vec_or_dict<int, string>"
    ); // exp
    assert_eq!(
        show(&mk(Ty_::TvecOrDict(arraykey(), nothing()))),
        "vec_or_dict<arraykey, nothing>"
    ); // exp
    // `full` does not strip namespaces, except from a class name.
    let ty = newtype("\\HH\\classname", vec![class("\\N\\C", vec![])]);
    assert_eq!(full(true, &env(), &ty), "\\HH\\classname<N\\C>");
    // Exact classes are marked only when internals are shown.
    let exact = mk(Ty_::Tclass(
        (Pos::NONE, "\\C".to_string()),
        Exact::Exact,
        vec![int()],
    ));
    assert_eq!(show(&exact), "C<int>");
    assert_eq!(full_strip_ns(false, &env(), &exact), "exact C<int>");
    assert_eq!(debug(&env(), &exact), "exact C<int>");
}

#[test]
fn everything_sdt_hides_supportdyn() {
    let mut env = env();
    env.tcopt.po.everything_sdt = true;
    assert_eq!(full_strip_ns(true, &env, &supportdyn(mixed())), "mixed");
    assert_eq!(
        full_strip_ns(true, &env, &supportdyn(class("\\C", vec![]))),
        "C"
    );
    // An open shape whose unknown fields are supportdyn<mixed> is `...`.
    assert_eq!(
        full_strip_ns(
            true,
            &env,
            &shape(vec![("a", false, int())], supportdyn(mixed()))
        ),
        "shape('a' => int, ...)"
    );
    assert_eq!(
        error(None, &env, &supportdyn(class("\\C", vec![]))),
        "an object of type C"
    );
    // ... unless `hh_log_level('show', 1)`.
    env.log_levels.insert("show".to_string(), 1);
    assert_eq!(
        full_strip_ns(true, &env, &supportdyn(mixed())),
        "supportdyn<mixed>"
    );
}

#[test]
fn generics_and_dependent_types() {
    assert_eq!(show(&generic("T")), "T"); // exp
    assert_eq!(show(&generic("this")), "this"); // exp
    assert_eq!(show(&generic("T#1")), "T#1"); // exp
    assert_eq!(show(&generic("<expr#13>::T")), "<expr#13>::T"); // exp
    assert_eq!(show(&generic("this::T")), "this::T"); // exp
    assert_eq!(
        show(&dependent(2, class("\\Foo", vec![]))),
        "<expr#2> as Foo"
    ); // exp
    assert_eq!(
        show(&option(dependent(2, class("\\B", vec![])))),
        "?<expr#2> as B"
    ); // exp
    assert_eq!(
        show(&mk(Ty_::Taccess(TaccessType(
            generic("TIn"),
            (Pos::NONE, "TBase".to_string())
        )))),
        "TIn::TBase"
    ); // exp
    // The generic that stands for a context: `T/[ctx $f]`.
    assert_eq!(show(&generic("T/[ctx $f]")), "ctx $f");
    // The generic that stands for the type of a parameter used in a dependent
    // context is printed as its bound, when it has exactly one.
    let mut env = env();
    assert_eq!(full_strip_ns(true, &env, &generic("T/$f")), "T/$f");
    env.upper_bounds
        .insert("T/$f".to_string(), [class("\\C", vec![])].into());
    assert_eq!(full_strip_ns(true, &env, &generic("T/$f")), "C");
}

#[test]
fn type_variables() {
    assert_eq!(show(&tvar(7)), "_");
    assert_eq!(full_strip_ns(false, &env(), &tvar(7)), "#7");
    assert_eq!(debug(&env(), &tvar(7)), "#7");
    let mut env = env();
    env.tyvars.insert(7, class("\\HH\\vec", vec![int()]));
    env.tyvars.insert(8, tvar(7));
    assert_eq!(full_strip_ns(true, &env, &tvar(7)), "vec<int>");
    assert_eq!(full_strip_ns(true, &env, &tvar(8)), "vec<int>");
    assert_eq!(full_strip_ns(true, &env, &option(tvar(7))), "?vec<int>");
    // A type variable solved to mixed, under an option.
    env.tyvars.insert(9, mixed());
    assert_eq!(full_strip_ns(true, &env, &option(tvar(9))), "mixed");
    // `full_rec`: the type variable that is being solved, inside its bound.
    assert_eq!(
        full_rec(true, &env, 11, &class("\\HH\\Vector", vec![tvar(11)])),
        "Vector<[rec]>"
    ); // exp
}

#[test]
fn tuples() {
    assert_eq!(show(&tuple(vec![])), "()"); // exp
    assert_eq!(show(&tuple(vec![int(), arraykey()])), "(int, arraykey)");
    assert_eq!(
        show(&tuple_with(
            vec![int()],
            vec![],
            TupleExtra::Tvariadic(mixed())
        )),
        "(int, mixed...)"
    ); // exp
    assert_eq!(
        show(&tuple_with(
            vec![],
            vec![],
            TupleExtra::Tvariadic(mixed())
        )),
        "(mixed...)"
    ); // exp
    assert_eq!(
        show(&tuple_with(
            vec![arraykey()],
            vec![],
            TupleExtra::Tvariadic(num())
        )),
        "(arraykey, num...)"
    ); // exp
    assert_eq!(
        show(&tuple_with(
            vec![],
            vec![arraykey(), bool_()],
            TupleExtra::Tvariadic(nothing())
        )),
        "(optional arraykey, optional bool)"
    ); // exp
    assert_eq!(
        show(&tuple_with(
            vec![int()],
            vec![string()],
            TupleExtra::Tvariadic(nothing())
        )),
        "(int, optional string)"
    ); // exp
    assert_eq!(
        show(&tuple_with(
            vec![int()],
            vec![],
            TupleExtra::Tsplat(generic("T"))
        )),
        "(int, ...T)"
    );
    assert_eq!(show(&option(tuple(vec![int(), arraykey()]))), "?(int, arraykey)"); // exp
}

#[test]
fn shapes() {
    assert_eq!(show(&shape(vec![], nothing())), "shape()"); // exp
    assert_eq!(show(&shape(vec![], mixed())), "shape(...)"); // exp
    // The fields are sorted by name.
    assert_eq!(
        show(&shape(
            vec![
                ("z", false, float()),
                ("x", false, int()),
                ("y", false, string())
            ],
            nothing()
        )),
        "shape('x' => int, 'y' => string, 'z' => float)"
    ); // exp
    assert_eq!(
        show(&shape(vec![("y", true, any())], mixed())),
        "shape(?'y' => _, ...)"
    ); // exp
    assert_eq!(
        show(&shape(
            vec![("a", false, int()), ("b", false, bool_())],
            mixed()
        )),
        "shape('a' => int, 'b' => bool, ...)"
    ); // exp
    assert_eq!(
        show(&shape(vec![("x", false, option(int()))], mixed())),
        "shape('x' => ?int, ...)"
    ); // exp
    // The unknown fields have another type than mixed.
    assert_eq!(
        show(&shape(vec![("a", false, int())], supportdyn(mixed()))),
        "shape('a' => int, supportdyn<mixed>...)"
    );
    // An optional field whose type is nothing is absent.
    assert_eq!(
        show(&shape(vec![("x", true, nothing())], mixed())),
        "shape(absent 'x', ...)"
    );
    // A class constant as a field name.
    let field = TShapeField(TshapeFieldName::TSFclassConst(
        (Pos::NONE, "\\C".to_string()),
        PosString(Pos::NONE, "X".to_string()),
    ));
    let ty = mk(Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
        origin: TypeOrigin::MissingOrigin,
        unknown_value: nothing(),
        fields: [(
            field,
            ShapeFieldType {
                optional: false,
                ty: int(),
            },
        )]
        .into(),
    })));
    assert_eq!(show(&ty), "shape(C::X => int)");
    assert_eq!(full(true, &env(), &ty), "shape(\\C::X => int)");
}

#[test]
fn shape_splats() {
    let splat = |elems| mk(Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems: elems })));
    assert_eq!(show(&splat(vec![generic("T")])), "shape(...T)");
    assert_eq!(
        show(&splat(vec![
            generic("T"),
            shape(vec![("a", false, int())], nothing())
        ])),
        "shape(...T, ...shape('a' => int))"
    ); // exp
    // When every element is a shape, they are merged: a field of the right
    // shape replaces the one of the left, unless it is optional.
    assert_eq!(
        show(&splat(vec![
            shape(
                vec![("a", false, int()), ("b", false, int())],
                nothing()
            ),
            shape(
                vec![("b", false, string()), ("c", true, bool_())],
                nothing()
            ),
        ])),
        "shape('a' => int, 'b' => string, ?'c' => bool)"
    );
    assert_eq!(
        show(&splat(vec![
            shape(vec![("a", false, int())], nothing()),
            shape(vec![("a", true, string())], mixed()),
        ])),
        "shape('a' => (int | string), ...)"
    );
    // Through a solved type variable.
    let mut env = env();
    env.tyvars
        .insert(1, shape(vec![("a", false, int())], nothing()));
    assert_eq!(
        full_strip_ns(
            true,
            &env,
            &splat(vec![tvar(1), shape(vec![("b", false, int())], nothing())])
        ),
        "shape('a' => int, 'b' => int)"
    );
}

#[test]
fn functions() {
    let none = FunParamFlags::empty();
    assert_eq!(show(&fun(vec![], int())), "(function(): int)"); // exp
    assert_eq!(
        show(&fun(vec![param(None, int(), none)], void())),
        "(function(int): void)"
    ); // exp
    assert_eq!(
        show(&fun(vec![param(None, int(), none)], like(option(int())))),
        "(function(int): ~?int)"
    ); // exp
    assert_eq!(
        show(&fun(vec![param(Some("$x"), arraykey(), none)], arraykey())),
        "(function(arraykey $x): arraykey)"
    ); // exp
    // A parameter without a type is printed as its name.
    assert_eq!(
        show(&fun(vec![param(Some("$x"), tvar(1), none)], tvar(2))),
        "(function($x): _)"
    ); // exp
    assert_eq!(
        show(&fun(
            vec![
                param(
                    Some("$x"),
                    like(generic("T")),
                    FunParamFlags::INOUT
                ),
                param(Some("$y"), generic("T"), none)
            ],
            void()
        )),
        "(function(inout ~T $x, T $y): void)"
    ); // exp
    assert_eq!(
        show(&fun(
            vec![
                param(
                    Some("$x"),
                    int(),
                    FunParamFlags::IS_OPTIONAL | FunParamFlags::NAMED
                ),
                param(Some("$y"), int(), FunParamFlags::NAMED),
                param(Some("$z"), bool_(), none)
            ],
            void()
        )),
        "(function(optional named int $x, named int $y, bool $z): void)"
    ); // exp
    assert_eq!(
        show(&fun(
            vec![
                param(Some("$a"), int(), none),
                param(
                    Some("$b"),
                    option(int()),
                    FunParamFlags::IS_OPTIONAL
                )
            ],
            void()
        )),
        "(function(int $a, optional ?int $b): void)"
    ); // exp
    assert_eq!(
        show(&fun(
            vec![
                param(
                    None,
                    class("\\C", vec![]),
                    FunParamFlags::READONLY
                ),
                param(None, generic("T"), FunParamFlags::SPLAT)
            ],
            void()
        )),
        "(function(readonly C, ...T): void)"
    );

    // Variadic parameters.
    let mut ft = fun_type(
        vec![
            param(Some("$x"), int(), FunParamFlags::IS_OPTIONAL),
            param(Some("$args"), string(), none),
        ],
        void(),
    );
    ft.flags = FunTypeFlags::VARIADIC;
    assert_eq!(
        show(&mk(tfun(ft))),
        "(function(optional int $x, string $args...): void)"
    ); // exp
    let mut ft = fun_type(
        vec![
            param(Some("$x"), int(), none),
            param(Some("..."), string(), FunParamFlags::NAMED),
        ],
        void(),
    );
    ft.flags = FunTypeFlags::NAMED_VARIADIC;
    assert_eq!(
        show(&mk(tfun(ft))),
        "(function(int $x, named string...): void)"
    ); // exp
    // Both: the variadic parameter comes before the named variadic one.
    let mut ft = fun_type(
        vec![
            param(Some("$args"), int(), none),
            param(Some("..."), string(), FunParamFlags::NAMED),
        ],
        void(),
    );
    ft.flags = FunTypeFlags::VARIADIC | FunTypeFlags::NAMED_VARIADIC;
    assert_eq!(
        show(&mk(tfun(ft))),
        "(function(int $args..., named string...): void)"
    );

    // `readonly` on `$this` and on the result.
    let mut ft = fun_type(vec![param(Some("$value"), int(), none)], int());
    ft.flags = FunTypeFlags::READONLY_THIS;
    ft.tparams = vec![tparam("T", vec![])];
    assert_eq!(
        show(&mk(tfun(ft))),
        "(readonly function<T>(int $value): int)"
    ); // exp
    let mut ft = fun_type(vec![], class("\\C", vec![]));
    ft.flags = FunTypeFlags::RETURNS_READONLY;
    assert_eq!(show(&mk(tfun(ft))), "(function(): readonly C)");

    // Type parameters with their constraints (but not `as supportdyn<mixed>`
    // when supportdyn is not shown, nor `as mixed`).
    let tinner = RefinedConst {
        bound: RefinedConstBound::TRexact(generic("TVal")),
        is_ctx: false,
    };
    let mut ft = fun_type(
        vec![
            param(Some("$b"), generic("TBox"), none),
            param(Some("$v"), generic("TVal"), none),
        ],
        void(),
    );
    ft.flags = FunTypeFlags::READONLY_THIS;
    ft.tparams = vec![
        tparam(
            "TBox",
            vec![(
                ConstraintKind::ConstraintAs,
                refined("\\MyBox", vec![("TInner", tinner)]),
            )],
        ),
        tparam("TVal", vec![(ConstraintKind::ConstraintAs, mixed())]),
    ];
    assert_eq!(
        show(&mk(tfun(ft))),
        "(readonly function<TBox as MyBox with { type TInner = TVal }, TVal>(TBox $b, TVal $v): void)"
    ); // exp
    let mut ft = fun_type(vec![param(None, generic("U"), none)], like(void()));
    ft.tparams = vec![tparam(
        "U",
        vec![(
            ConstraintKind::ConstraintAs,
            class("\\Box", vec![generic("T")]),
        )],
    )];
    assert_eq!(
        show(&mk(tfun(ft))),
        "(function<U as Box<T>>(U): ~void)"
    ); // exp (inside a larger type)
    let mut ft = fun_type(vec![], void());
    ft.tparams = vec![Tparam {
        reified: ReifyKind::Reified,
        ..tparam(
            "T",
            vec![
                (ConstraintKind::ConstraintSuper, int()),
                (ConstraintKind::ConstraintAs, num()),
            ],
        )
    }];
    assert_eq!(
        show(&mk(tfun(ft))),
        "(function<reify T super int as num>(): void)"
    );
}

#[test]
fn capabilities() {
    let none = FunParamFlags::empty();
    let with_cap = |params, ret, tparams, cap: Ty| {
        let mut ft = fun_type(params, ret);
        ft.tparams = tparams;
        ft.implicit_params.capability = Capability::CapTy(cap);
        mk(tfun(ft))
    };
    // The pure context.
    let mut ft = fun_type(vec![param(None, mixed(), none)], like(tvar(1)));
    ft.flags = FunTypeFlags::READONLY_THIS | FunTypeFlags::VARIADIC;
    ft.implicit_params.capability = Capability::CapTy(inter(vec![]));
    assert_eq!(
        show(&mk(tfun(ft))),
        "(readonly function(mixed...)[]: ~_)"
    ); // exp
    assert_eq!(
        show(&with_cap(vec![], void(), vec![], mixed())),
        "(function()[]: void)"
    );
    // A capability that is not known yet.
    assert_eq!(
        show(&like(with_cap(
            vec![param(None, inter(vec![arraykey(), tvar(1)]), none)],
            like(tvar(2)),
            vec![],
            tvar(3)
        ))),
        "~(function((arraykey & _))[_]: ~_)"
    ); // exp
    // The default capability is not printed, in whatever order it is.
    let cap = |name: &str| class(&format!("\\HH\\Capabilities\\{}", name), vec![]);
    let defaults = [
        "IO",
        "WriteProperty",
        "AccessGlobals",
        "RxLocal",
        "SystemLocal",
        "ImplicitPolicyLocal",
    ];
    assert_eq!(
        show(&with_cap(
            vec![],
            void(),
            vec![],
            inter(defaults.iter().map(|name| cap(name)).collect())
        )),
        "(function(): void)"
    );
    assert_eq!(
        show(&with_cap(
            vec![],
            void(),
            vec![],
            inter(vec![cap("WriteProperty"), cap("IO")])
        )),
        "(function()[(HH\\Capabilities\\WriteProperty & HH\\Capabilities\\IO)]: void)"
    );
    // The contexts that were desugared to type parameters.
    assert_eq!(
        show(&with_cap(
            vec![],
            void(),
            vec![tparam("T/[ctx $f]", vec![]), tparam("T", vec![])],
            inter(defaults.iter().map(|name| cap(name)).collect())
        )),
        "(function<T>()[ctx $f]: void)"
    );
    assert_eq!(
        show(&with_cap(
            vec![],
            void(),
            vec![tparam("T/[ctx $f]", vec![])],
            generic("T/[ctx $f]")
        )),
        "(function()[ctx $fctx $f]: void)"
    );
}

#[test]
fn refinements() {
    let exact = |ty| RefinedConst {
        bound: RefinedConstBound::TRexact(ty),
        is_ctx: false,
    };
    assert_eq!(
        show(&refined("\\Box", vec![("T", exact(int()))])),
        "Box with { type T = int }"
    ); // exp
    assert_eq!(
        show(&refined("\\MyBox", vec![("TInner", exact(generic("TVal#1")))])),
        "MyBox with { type TInner = TVal#1 }"
    ); // exp
    // The upper bounds come before the lower bounds.
    let loose = RefinedConst {
        bound: RefinedConstBound::TRloose(RefinedConstBounds {
            lower: vec![class("\\C4", vec![])],
            upper: vec![class("\\C2", vec![])],
        }),
        is_ctx: false,
    };
    assert_eq!(
        show(&refined("\\Box", vec![("T", loose.clone())])),
        "Box with { type T as C2 super C4 }"
    ); // exp
    let ctx = RefinedConst {
        bound: RefinedConstBound::TRexact(inter(vec![])),
        is_ctx: true,
    };
    assert_eq!(
        show(&refined("\\Box", vec![("T", loose), ("C", ctx)])),
        "Box with { ctx C = mixed; type T as C2 super C4 }"
    );
    assert_eq!(show(&refined("\\Box", vec![])), "Box");
}

#[test]
fn negations() {
    assert_eq!(show(&neg(class_tag("\\A", vec![]))), "not A"); // exp
    assert_eq!(
        show(&neg(class_tag(
            "\\MyReifiedClass",
            vec![TypeTagGeneric::Filled(string())]
        ))),
        "not MyReifiedClass<string>"
    ); // exp
    assert_eq!(
        full_strip_ns(
            false,
            &env(),
            &neg(class_tag(
                "\\HH\\vec",
                vec![TypeTagGeneric::Wildcard(4)]
            ))
        ),
        "not vec<_4>"
    );
    let field = |p: TypePredicate_| ShapeFieldPredicate {
        optional: false,
        predicate: pred(p),
    };
    // The fields of a shape predicate are printed from the last to the first.
    let shape_pred = |allows_unknown_fields| {
        TypePredicate_::IsShapeOf(ShapePredicate {
            allows_unknown_fields,
            fields: [
                (lit("x"), field(TypePredicate_::IsTag(TypeTag::IntTag))),
                (
                    lit("y"),
                    field(class_tag("\\HH\\string", vec![])),
                ),
                (lit("z"), field(TypePredicate_::IsTag(TypeTag::IntTag))),
            ]
            .into(),
        })
    };
    assert_eq!(
        show(&neg(shape_pred(false))),
        "not shape('z' => int, 'y' => string, 'x' => int)"
    ); // exp
    assert_eq!(
        show(&neg(shape_pred(true))),
        "not shape('z' => int, 'y' => string, 'x' => int, ...)"
    );
    assert_eq!(
        show(&neg(TypePredicate_::IsTupleOf(TuplePredicate {
            required: vec![
                pred(TypePredicate_::IsTag(TypeTag::IntTag)),
                pred(TypePredicate_::IsTag(TypeTag::NullTag))
            ]
        }))),
        "not (int, null)"
    );
    assert_eq!(
        show(&neg(TypePredicate_::IsUnionOf(vec![
            pred(TypePredicate_::IsTag(TypeTag::BoolTag)),
            pred(TypePredicate_::IsNot(Box::new(pred(TypePredicate_::IsTag(
                TypeTag::FloatTag
            ))))),
            pred(TypePredicate_::IsTag(TypeTag::EnumTag("\\E".to_string()))),
            pred(TypePredicate_::IsTag(TypeTag::GenericTag {
                name: "T".to_string(),
                from_like: false
            })),
            pred(TypePredicate_::IsTag(TypeTag::ResourceTag)),
        ]))),
        "not bool | not float | E | T | resource"
    );
    assert_eq!(
        error(None, &env(), &neg(class_tag("\\A", vec![]))),
        "anything but a A"
    );
    assert_eq!(
        error(None, &env(), &neg(shape_pred(true))),
        "anything but shape('z' => an int, 'y' => a string, 'x' => an int, ...)"
    );
}

#[test]
fn internal_types() {
    let i = |c: ConstraintType_| {
        InternalType::ConstraintType(ConstraintType(reason::none(), std::rc::Rc::new(c)))
    };
    let show_i = |ty: &InternalType| full_strip_ns_i(true, &env(), ty);
    assert_eq!(show_i(&InternalType::LoclType(int())), "int");
    assert_eq!(debug_i(&env(), &InternalType::LoclType(tvar(1))), "#1");
    assert_eq!(
        show_i(&i(ConstraintType_::ThasConst {
            name: "X".to_string(),
            ty: int()
        })),
        "has_const(X: int)"
    );
    assert_eq!(
        show_i(&i(ConstraintType_::ThasTypeMember(HasTypeMember {
            id: "T".to_string(),
            lower: nothing(),
            upper: mixed(),
        }))),
        "has_type_member(nothing <: T <: mixed)"
    );
    assert_eq!(
        show_i(&i(ConstraintType_::Tdestructure(Destructure {
            required: vec![int()],
            optional: vec![string()],
            variadic: Some(bool_()),
            kind: DestructureKind::ListDestructure,
        }))),
        "list(int, =_string, ...bool)"
    );
    assert_eq!(
        show_i(&i(ConstraintType_::Tdestructure(Destructure {
            required: vec![],
            optional: vec![],
            variadic: None,
            kind: DestructureKind::SplatUnpack,
        }))),
        "splat()"
    );
    assert_eq!(
        show_i(&i(ConstraintType_::TcanTraverse(CanTraverse {
            key: None,
            val: int(),
            is_await: false,
            reason: reason::none(),
        }))),
        "can_traverse(int, is_await:false)"
    );
    assert_eq!(
        show_i(&i(ConstraintType_::TcanTraverse(CanTraverse {
            key: Some(string()),
            val: int(),
            is_await: true,
            reason: reason::none(),
        }))),
        "can_traverse(string, int, is_await:true)"
    );
    assert_eq!(
        show_i(&i(ConstraintType_::TtypeSwitch {
            predicate: pred(TypePredicate_::IsTag(TypeTag::IntTag)),
            ty_true: int(),
            ty_false: string(),
        })),
        "(is int?int:string)"
    );
}

// ~~ Constraints ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

#[test]
fn constraints() {
    let mut env = env();
    assert_eq!(constraints_for_type(true, &env, &generic("T")), "");
    env.upper_bounds
        .insert("T".to_string(), [supportdyn(mixed())].into());
    // "(function(inout ~T $x, T $y): void) where T as supportdyn<mixed>" // exp
    assert_eq!(
        constraints_for_type(
            true,
            &env,
            &fun(
                vec![param(Some("$y"), generic("T"), FunParamFlags::empty())],
                void()
            )
        ),
        "where T as supportdyn<mixed>"
    );
    // "T as supportdyn<mixed>": the type is the type parameter itself.
    assert_eq!(
        constraints_for_type(true, &env, &generic("T")),
        "as supportdyn<mixed>"
    );
    // "this::T2 where this::T2 super this::T, this::T2 as B1::T2" // exp
    env.lower_bounds
        .insert("this::T2".to_string(), [generic("this::T")].into());
    env.upper_bounds
        .insert("this::T2".to_string(), [generic("B1::T2")].into());
    assert_eq!(
        constraints_for_type(true, &env, &generic("this::T2")),
        "where this::T2 super this::T, this::T2 as B1::T2"
    );
    // "Tin = Tb::Ta::T" // exp: a bound that is both lower and upper.
    env.lower_bounds
        .insert("Tin".to_string(), [generic("Tb::Ta::T")].into());
    env.upper_bounds.insert(
        "Tin".to_string(),
        [generic("Tb::Ta::T"), mixed()].into(),
    );
    assert_eq!(
        constraints_for_type(true, &env, &generic("Tin")),
        "= Tb::Ta::T"
    );
    // The type parameters of every part of the type, in the order of their
    // names; the name is not stripped:
    // "C::T where \C::T super <expr#13>::T, \C::T super <expr#15>::T, \C::T as num" // exp
    env.lower_bounds.insert(
        "\\C::T".to_string(),
        [generic("<expr#15>::T"), generic("<expr#13>::T")].into(),
    );
    env.upper_bounds
        .insert("\\C::T".to_string(), [num()].into());
    assert_eq!(
        constraints_for_type(true, &env, &generic("\\C::T")),
        "where \\C::T super <expr#13>::T, \\C::T super <expr#15>::T, \\C::T as num"
    );
    // With everything_sdt, `as supportdyn<mixed>` is not a constraint.
    env.tcopt.po.everything_sdt = true;
    assert_eq!(constraints_for_type(true, &env, &generic("T")), "");
}

// ~~ Fuel ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

#[test]
fn fuel() {
    // test/typecheck/massive_type.php
    fn nested(depth: usize) -> Ty {
        if depth == 0 {
            int()
        } else {
            // 'a1', 'a2', then 'b1', 'b2', ... 'n1', 'n2'
            let letter = (b'a' + (depth - 1) as u8) as char;
            let name1 = format!("{}1", letter);
            let name2 = format!("{}2", letter);
            shape(
                vec![
                    (&name1, false, nested(depth - 1)),
                    (&name2, false, nested(depth - 1)),
                ],
                nothing(),
            )
        }
    }
    let ty = nested(14);
    assert_eq!(
        show(&ty),
        "shape('n1' => shape('m1' => shape('l1' => shape('k1' => shape('j1' => shape('i1' => shape('h1' => shape('g1' => shape('f1' => shape('e1' => shape('d1' => shape('c1' => shape('b1' => shape('a1' => int, 'a2' => int), 'b2' => shape('a1' => int, 'a2' => int)), 'c2' => shape('b1' => shape('a1' => int, 'a2' => int), 'b2' => shape('a1' => int, 'a2' => int))), 'd2' => shape('c1' => shape('b1' => shape('a1' => int, 'a2' => int), 'b2' => shape('a1' => int, 'a2' => int)), 'c2' => shape('b1' => shape('a1' => int, 'a2' => int), 'b2' => shape('a1' => int, 'a2' => int)))), 'e2' => shape('d1' => shape('c1' => shape('b1' => shape('a1' => int, 'a2' => int), 'b2' => shape('a1' => int, 'a2' => int)), 'c2' => shape([shape was truncated])), [shape was truncated])), [shape was truncated]), [shape was truncated]), [shape was truncated]), [shape was truncated]), [shape was truncated]), [shape was truncated]), [shape was truncated]), [shape was truncated]), [shape was truncated]) [This type was truncated. If you need more of the type, use `hh stop; hh --config type_printer_fuel=N`. At this time, N is 100.]"
    ); // exp: test/typecheck/massive_type.php.exp
    // Types other than shapes are cut with "[truncated]".
    let mut env = env();
    env.tcopt.tco_type_printer_fuel = 2;
    assert_eq!(
        full_strip_ns(
            true,
            &env,
            &class("\\A", vec![class("\\B", vec![class("\\C", vec![int()])])])
        ),
        "A<B<C<[truncated]>>> [This type was truncated. If you need more of the type, use `hh stop; hh --config type_printer_fuel=N`. At this time, N is 2.]"
    );
    // The type of a named parameter is printed twice, so costs twice: four
    // types are printed for the three there are, which is one more than
    // this fuel allows. Nothing is cut (the fuel runs out on the last one),
    // but the message is added.
    env.tcopt.tco_type_printer_fuel = 3;
    assert_eq!(
        full_strip_ns(
            true,
            &env,
            &fun(
                vec![param(Some("$x"), int(), FunParamFlags::empty())],
                class("\\A", vec![])
            )
        ),
        "(function(int $x): A) [This type was truncated. If you need more of the type, use `hh stop; hh --config type_printer_fuel=N`. At this time, N is 3.]"
    );
}

// ~~ Error strings ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

#[test]
fn error_strings() {
    let err = |ty: &Ty| error(None, &env(), ty);
    assert_eq!(err(&any()), "an untyped value");
    assert_eq!(err(&dynamic()), "a dynamic value"); // exp
    assert_eq!(err(&inter(vec![])), "a mixed value");
    assert_eq!(err(&mixed()), "a mixed value"); // exp
    assert_eq!(err(&nonnull()), "a nonnull value"); // exp
    assert_eq!(err(&option(int())), "a nullable type"); // exp
    assert_eq!(err(&null()), "null");
    assert_eq!(err(&void()), "void");
    assert_eq!(err(&int()), "an int");
    assert_eq!(err(&bool_()), "a bool");
    assert_eq!(err(&float()), "a float");
    assert_eq!(err(&num()), "a num (int | float)");
    assert_eq!(err(&prim(Tprim::Tresource)), "a resource");
    assert_eq!(err(&arraykey()), "an array key (int | string)"); // exp
    assert_eq!(
        err(&prim(Tprim::Tnoreturn)),
        "noreturn (throws or exits)"
    );
    assert_eq!(err(&string()), "a string");
    assert_eq!(err(&tvar(1)), "some value"); // exp
    assert_eq!(err(&fun(vec![], void())), "a function"); // exp
    assert_eq!(err(&shape(vec![], nothing())), "a shape"); // exp
    assert_eq!(
        err(&mk(Ty_::TvecOrDict(int(), int()))),
        "a vec_or_dict"
    ); // exp
    assert_eq!(err(&tuple(vec![int(), int()])), "a tuple of size 2");
    assert_eq!(
        err(&tuple_with(
            vec![int()],
            vec![int()],
            TupleExtra::Tvariadic(nothing())
        )),
        "a tuple of size at least 1"
    );
    assert_eq!(
        err(&tuple_with(
            vec![int()],
            vec![],
            TupleExtra::Tsplat(generic("T"))
        )),
        "a tuple of size at least 1"
    );
    assert_eq!(err(&generic("T")), "a value of generic type T"); // exp
    assert_eq!(
        err(&generic("this")),
        "the expression dependent type this"
    );
    assert_eq!(
        err(&generic("<expr#3>::T")),
        "the expression dependent type <expr#3>::T"
    );
    assert_eq!(
        err(&dependent(3, class("\\C", vec![]))),
        "the expression dependent type <expr#3>"
    ); // exp
    assert_eq!(err(&class("\\C", vec![])), "an object of type C"); // exp
    assert_eq!(
        err(&class("\\HH\\vec", vec![int()])),
        "an object of type vec<int>"
    ); // exp
    assert_eq!(
        err(&mk(Ty_::Tclass(
            (Pos::NONE, "\\IntBox".to_string()),
            Exact::Exact,
            vec![]
        ))),
        "an object of exactly the class IntBox"
    ); // exp
    assert_eq!(err(&newtype("\\FooType", vec![])), "a value of type FooType"); // exp
    assert_eq!(
        err(&newtype("\\HH\\classname", vec![class("\\C", vec![])])),
        "a classname string for C"
    );
    assert_eq!(
        err(&newtype("\\HH\\typename", vec![class("\\C", vec![])])),
        "a typename string for C"
    );
    assert_eq!(
        err(&newtype(
            "\\HH\\class_or_classname",
            vec![class("\\C", vec![])]
        )),
        "a class or classname for C"
    );
    assert_eq!(
        err(&mk(Ty_::TclassPtr(class("\\A", vec![])))),
        "a class pointer for A"
    ); // exp
    assert_eq!(err(&supportdyn(mixed())), "a value of type supportdyn<mixed>");
    assert_eq!(
        err(&mk(Ty_::Taccess(TaccessType(
            generic("T"),
            (Pos::NONE, "U".to_string())
        )))),
        "a type constant"
    ); // exp
    assert_eq!(
        err(&mk(Ty_::Tlabel("A".to_string()))),
        "a label (#A)"
    );
    // Unions: the descriptions, sorted and without duplicates.
    assert_eq!(err(&nothing()), "an undefined value"); // exp
    assert_eq!(
        err(&union(vec![string(), int(), int()])),
        "a string or an int"
    );
    assert_eq!(err(&union(vec![int(), null()])), "a nullable type");
    assert_eq!(
        err(&union(vec![dynamic(), class("\\C", vec![])])),
        "a dynamic value or an object of type C"
    );
    assert_eq!(
        error(
            Some(true),
            &env(),
            &union(vec![dynamic(), class("\\C", vec![])])
        ),
        "an object of type C"
    );
    assert_eq!(
        err(&inter(vec![class("\\NoTB1", vec![]), class("\\NoTB2", vec![])])),
        "an object of type NoTB1 and an object of type NoTB2"
    ); // exp
    // A solved type variable is described by its solution.
    let mut env = env();
    env.tyvars.insert(1, int());
    assert_eq!(error(None, &env, &tvar(1)), "an int");
}

#[test]
fn classish_kinds() {
    use Abstraction::*;
    use ClassishKind::*;
    assert_eq!(classish_kind(&Cclass(Abstract), false), "an abstract class");
    assert_eq!(
        classish_kind(&Cclass(Abstract), true),
        "an abstract final class"
    );
    assert_eq!(classish_kind(&Cclass(Concrete), false), "a class");
    assert_eq!(classish_kind(&Cclass(Concrete), true), "a final class");
    assert_eq!(classish_kind(&Cinterface, false), "an interface");
    assert_eq!(classish_kind(&Ctrait, false), "a trait");
    assert_eq!(classish_kind(&Cenum, false), "an enum");
    assert_eq!(
        classish_kind(&CenumClass(Abstract), false),
        "an abstract enum class"
    );
    assert_eq!(classish_kind(&CenumClass(Concrete), true), "an enum class");
}

// ~~ Coeffects ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

#[test]
fn coeffect_strings() {
    let cap = |name: &str| class(&format!("\\HH\\Capabilities\\{}", name), vec![]);
    assert_eq!(coeffects(&env(), &inter(vec![])), "the capability set {}"); // exp
    assert_eq!(coeffects(&env(), &mixed()), "the capability set {}");
    assert_eq!(
        coeffects(&env(), &cap("WriteProperty")),
        "the capability WriteProperty"
    ); // exp
    assert_eq!(
        coeffects(
            &env(),
            &inter(vec![
                cap("WriteProperty"),
                cap("AccessGlobals"),
                cap("RxLocal"),
                cap("SystemLocal"),
                cap("ImplicitPolicyLocal"),
                cap("IO"),
            ])
        ),
        "the capability set {AccessGlobals, IO, ImplicitPolicyLocal, RxLocal, SystemLocal, WriteProperty}"
    ); // exp
    assert_eq!(
        coeffects(
            &env(),
            &inter(vec![cap("Rx"), inter(vec![cap("WriteProperty"), cap("Rx")])])
        ),
        "the capability set {Rx, WriteProperty}"
    ); // exp
    assert_eq!(
        coeffects(
            &env(),
            &class(
                "\\HH\\Contexts\\zoned_with",
                vec![class("\\A", vec![])]
            )
        ),
        "the capability zoned_with<A>"
    ); // exp
    // A type that is not an intersection of capabilities is printed as it is.
    assert_eq!(coeffects(&env(), &nonnull()), "nonnull");
    assert_eq!(
        coeffects(&env(), &union(vec![cap("IO"), cap("Rx")])),
        "(IO | Rx)"
    );
    // A type variable stands for its upper bounds.
    let mut env = env();
    assert_eq!(coeffects(&env, &tvar(1)), "_");
    env.tyvar_upper_bounds.insert(
        1,
        vec![
            InternalType::LoclType(cap("IO")),
            InternalType::LoclType(tvar(2)),
        ],
    );
    assert_eq!(coeffects(&env, &tvar(1)), "the capability IO");
    env.tyvar_upper_bounds.insert(
        1,
        vec![
            InternalType::LoclType(cap("IO")),
            InternalType::LoclType(cap("Rx")),
        ],
    );
    assert_eq!(coeffects(&env, &tvar(1)), "the capability set {IO, Rx}");
}

// ~~ Decl types ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

mod decl_types {
    use oxidized::typing_defs_core as d;
    use oxidized::typing_reason::T_ as DeclReason;

    use super::*;
    // Under `port`, `super::locl` also exports a `DeclTy` (the hackrs one);
    // the printer prints the oxidized one.
    use super::super::DeclTy;

    fn mk(node: d::Ty_) -> DeclTy {
        d::Ty(DeclReason::NoReason, Box::new(node))
    }

    fn apply(name: &str, targs: Vec<DeclTy>) -> DeclTy {
        mk(d::Ty_::Tapply((Pos::NONE, name.to_string()), targs))
    }

    fn prim(p: Tprim) -> DeclTy {
        mk(d::Ty_::Tprim(p))
    }

    fn int() -> DeclTy {
        prim(Tprim::Tint)
    }

    fn mixed() -> DeclTy {
        mk(d::Ty_::Tmixed)
    }

    fn generic(name: &str) -> DeclTy {
        mk(d::Ty_::Tgeneric(name.to_string()))
    }

    fn nothing() -> DeclTy {
        mk(d::Ty_::Tunion(vec![]))
    }

    fn shape(fields: Vec<(&str, bool, DeclTy)>, unknown_value: DeclTy) -> DeclTy {
        mk(d::Ty_::Tshape(d::ShapeType::ShapeSimple(
            d::ShapeTypeSimple {
                origin: TypeOrigin::MissingOrigin,
                unknown_value,
                fields: fields
                    .into_iter()
                    .map(|(name, optional, ty)| (lit(name), d::ShapeFieldType { optional, ty }))
                    .collect(),
            },
        )))
    }

    fn fun_type(params: Vec<(Option<&str>, DeclTy)>, ret: DeclTy) -> d::FunType {
        d::FunType {
            tparams: vec![],
            where_constraints: vec![],
            params: params
                .into_iter()
                .map(|(name, ty)| d::FunParam {
                    pos: Pos::NONE,
                    name: name.map(|s| s.to_string()),
                    type_: ty,
                    flags: FunParamFlags::empty(),
                    def_value: None,
                })
                .collect(),
            implicit_params: d::FunImplicitParams {
                capability: d::Capability::CapDefaults(Pos::NONE),
            },
            ret,
            flags: FunTypeFlags::empty(),
            instantiated: true,
        }
    }

    fn show(ty: &DeclTy) -> String {
        full_strip_ns_decl(None, false, &env(), ty)
    }

    #[test]
    fn simple() {
        assert_eq!(show(&int()), "int");
        assert_eq!(show(&mixed()), "mixed");
        assert_eq!(show(&mk(d::Ty_::Tthis)), "this");
        assert_eq!(show(&mk(d::Ty_::Twildcard)), "_");
        assert_eq!(
            show(&mk(d::Ty_::Tany(oxidized::tany_sentinel::TanySentinel))),
            "_"
        );
        assert_eq!(show(&mk(d::Ty_::Tnonnull)), "nonnull");
        assert_eq!(show(&mk(d::Ty_::Tdynamic(None))), "dynamic");
        assert_eq!(show(&generic("T")), "T");
        assert_eq!(show(&apply("\\HH\\string", vec![])), "string");
        assert_eq!(show(&apply("\\N\\C", vec![])), "N\\C");
        assert_eq!(show(&apply("\\HH\\vec", vec![int()])), "vec<int>");
        assert_eq!(show(&mk(d::Ty_::Toption(int()))), "?int");
        // Unlike a locl type, `?nonnull` is not printed as `mixed`.
        assert_eq!(
            show(&mk(d::Ty_::Toption(mk(d::Ty_::Tnonnull)))),
            "?nonnull"
        );
        assert_eq!(show(&mk(d::Ty_::Tlike(int()))), "~int");
        assert_eq!(show(&mk(d::Ty_::TclassPtr(apply("\\C", vec![])))), "class<C>");
        assert_eq!(
            show(&mk(d::Ty_::TvecOrDict(int(), mixed()))),
            "vec_or_dict<int, mixed>"
        );
        assert_eq!(
            show(&mk(d::Ty_::Taccess(d::TaccessType(
                mk(d::Ty_::Tthis),
                (Pos::NONE, "T".to_string())
            )))),
            "this::T"
        );
        assert_eq!(
            show(&apply("\\HH\\supportdyn", vec![mixed()])),
            "supportdyn<mixed>"
        );
        // `full_decl` keeps the namespaces (but not the one of `string`) and
        // never shows supportdyn.
        let tcopt = TypecheckerOptions::default();
        assert_eq!(full_decl(None, &tcopt, &apply("\\N\\C", vec![])), "\\N\\C");
        assert_eq!(
            full_decl(None, &tcopt, &apply("\\HH\\string", vec![])),
            "string"
        );
        assert_eq!(
            full_decl(None, &tcopt, &apply("\\HH\\vec", vec![int()])),
            "\\HH\\vec<int>"
        );
        assert_eq!(
            full_decl(
                None,
                &tcopt,
                &apply("\\HH\\supportdyn", vec![apply("\\C", vec![])])
            ),
            "\\C"
        );
    }

    #[test]
    fn unions_and_intersections() {
        assert_eq!(show(&nothing()), "nothing");
        // A decl union is printed like a tuple after a bar.
        assert_eq!(
            show(&mk(d::Ty_::Tunion(vec![int(), apply("\\C", vec![])]))),
            "|(int, C)"
        );
        assert_eq!(show(&mk(d::Ty_::Tintersection(vec![]))), "mixed");
        assert_eq!(
            show(&mk(d::Ty_::Tintersection(vec![
                apply("\\A", vec![]),
                apply("\\B", vec![])
            ]))),
            "(A & B)"
        );
        assert_eq!(
            show(&mk(d::Ty_::Tintersection(vec![apply("\\A", vec![])]))),
            "A"
        );
    }

    #[test]
    fn tuples_and_shapes() {
        assert_eq!(
            show(&mk(d::Ty_::Ttuple(d::TupleType {
                required: vec![int()],
                optional: vec![generic("T")],
                extra: d::TupleExtra::Tvariadic(mixed()),
            }))),
            "(int, optional T, mixed...)"
        );
        assert_eq!(
            show(&mk(d::Ty_::Ttuple(d::TupleType {
                required: vec![int()],
                optional: vec![],
                extra: d::TupleExtra::Tsplat(generic("T")),
            }))),
            "(int, ...T)"
        );
        assert_eq!(
            show(&shape(vec![("b", true, int()), ("a", false, mixed())], nothing())),
            "shape('a' => mixed, ?'b' => int)"
        );
        // An open decl shape has `?nonnull` for its unknown fields.
        assert_eq!(
            show(&shape(
                vec![("a", false, int())],
                mk(d::Ty_::Toption(mk(d::Ty_::Tnonnull)))
            )),
            "shape('a' => int, ...)"
        );
        assert_eq!(
            show(&shape(vec![("a", false, int())], mixed())),
            "shape('a' => int, mixed...)"
        );
        assert_eq!(
            show(&mk(d::Ty_::Tshape(d::ShapeType::ShapeSplat(
                d::ShapeTypeSplat {
                    ss_elems: vec![generic("T"), shape(vec![("a", false, int())], nothing())]
                }
            )))),
            "shape(...T, ...shape('a' => int))"
        );
    }

    #[test]
    fn refinement() {
        let ty = mk(d::Ty_::Trefinement(
            apply("\\Box", vec![]),
            d::ClassRefinement {
                cr_consts: [(
                    "T".to_string(),
                    d::RefinedConst {
                        bound: d::RefinedConstBound::TRexact(int()),
                        is_ctx: false,
                    },
                )]
                .into(),
            },
        ));
        assert_eq!(show(&ty), "Box with { type T = int }");
    }

    #[test]
    fn functions() {
        assert_eq!(
            show(&mk(d::Ty_::Tfun(fun_type(
                vec![(Some("$x"), int()), (None, mixed())],
                mk(d::Ty_::Tprim(Tprim::Tvoid))
            )))),
            "(function(int $x, mixed): void)"
        );
        // verbose_fun: `async`, the attributes and the `where` constraints.
        let mut ft = fun_type(vec![(Some("$x"), generic("T"))], apply("\\HH\\Awaitable", vec![int()]));
        ft.flags = FunTypeFlags::ASYNC | FunTypeFlags::RETURN_DISPOSABLE;
        ft.params[0].flags = FunParamFlags::ACCEPT_DISPOSABLE;
        ft.tparams = vec![d::Tparam {
            variance: Variance::Invariant,
            name: (Pos::NONE, "T".to_string()),
            constraints: vec![
                (ConstraintKind::ConstraintAs, apply("\\C", vec![])),
                (ConstraintKind::ConstraintAs, mixed()),
            ],
            reified: ReifyKind::SoftReified,
            user_attributes: vec![],
        }];
        ft.where_constraints = vec![d::WhereConstraint(
            generic("T"),
            ConstraintKind::ConstraintSuper,
            int(),
        )];
        let ty = mk(d::Ty_::Tfun(ft));
        assert_eq!(
            show(&ty),
            "(function<<<__Soft>> reify T as C>(T $x): Awaitable<int>)"
        );
        assert_eq!(
            debug_decl(&env(), &ty),
            "<<__ReturnDisposable>> (async function<<<__Soft>> reify T as C>(<<__AcceptDisposable>> T $x): Awaitable<int> where T super int)"
        );
        // Capabilities.
        let cap = |name: &str| apply(&format!("\\HH\\Capabilities\\{}", name), vec![]);
        let with_cap = |capability: DeclTy| {
            let mut ft = fun_type(vec![], int());
            ft.implicit_params.capability = d::Capability::CapTy(capability);
            mk(d::Ty_::Tfun(ft))
        };
        assert_eq!(
            show(&with_cap(mk(d::Ty_::Tintersection(vec![])))),
            "(function()[]: int)"
        );
        assert_eq!(
            show(&with_cap(mk(d::Ty_::Toption(mk(d::Ty_::Tnonnull))))),
            "(function()[]: int)"
        );
        assert_eq!(
            show(&with_cap(mk(d::Ty_::Tintersection(vec![
                cap("IO"),
                cap("ImplicitPolicyLocal"),
                cap("SystemLocal"),
                cap("RxLocal"),
                cap("AccessGlobals"),
                cap("WriteProperty"),
            ])))),
            "(function(): int)"
        );
        assert_eq!(
            show(&with_cap(cap("IO"))),
            "(function()[HH\\Capabilities\\IO]: int)"
        );
        // What is under an option is printed without it.
        assert_eq!(
            show(&with_cap(mk(d::Ty_::Toption(cap("IO"))))),
            "(function()[HH\\Capabilities\\IO]: int)"
        );
    }

    #[test]
    fn fuel() {
        let mut env = env();
        env.tcopt.tco_type_printer_fuel = 1;
        let ty = apply("\\A", vec![apply("\\B", vec![apply("\\C", vec![])])]);
        assert_eq!(
            full_strip_ns_decl(None, false, &env, &ty),
            "A<B<[truncated]>> [This type was truncated. If you need more of the type, use `hh stop; hh --config type_printer_fuel=N`. At this time, N is 1.]"
        );
        assert_eq!(
            full_strip_ns_decl(Some(false), false, &env, &ty),
            "A<B<[truncated]>>"
        );
    }
}

// ~~ Comparison ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

// (The comparison functions of the provisional definitions.)
#[cfg(not(feature = "port"))]
#[test]
fn comparison() {
    use std::cmp::Ordering::*;
    // The order of the constructors: `ty_con_ordinal_`.
    let sorted = [
        any(),
        mixed(),
        nonnull(),
        dynamic(),
        option(int()),
        int(),
        fun(vec![], void()),
        tuple(vec![]),
        shape(vec![], nothing()),
        tvar(1),
        generic("T"),
        union(vec![]),
        inter(vec![]),
        mk(Ty_::Taccess(TaccessType(
            generic("T"),
            (Pos::NONE, "U".to_string()),
        ))),
        mk(Ty_::TvecOrDict(int(), int())),
        mk(Ty_::TclassPtr(int())),
        newtype("\\N", vec![]),
        dependent(1, int()),
        class("\\C", vec![]),
        neg(TypePredicate_::IsTag(TypeTag::IntTag)),
        mk(Ty_::Tlabel("A".to_string())),
    ];
    for (i, ty1) in sorted.iter().enumerate() {
        for (j, ty2) in sorted.iter().enumerate() {
            assert_eq!(ty_compare(false, ty1, ty2), i.cmp(&j), "{:?} {:?}", ty1, ty2);
        }
    }
    // Primitive types, in the order of their declaration.
    assert_eq!(ty_compare(false, &float(), &arraykey()), Less);
    assert_eq!(ty_compare(false, &null(), &int()), Less);
    // Lists are compared in order, unless normalized.
    let u1 = union(vec![int(), string()]);
    let u2 = union(vec![string(), int()]);
    assert_ne!(ty_compare(false, &u1, &u2), Equal);
    assert!(ty_equal(true, &u1, &u2));
    assert!(!ty_equal(false, &u1, &u2));
    // ... but the arguments of a class are never normalized.
    let c1 = class("\\C", vec![u1.clone()]);
    let c2 = class("\\C", vec![u2.clone()]);
    assert!(!ty_equal(true, &c1, &c2));
    // Reasons and positions are ignored.
    assert!(ty_equal(
        false,
        &Ty(reason::witness(Pos::NONE), std::rc::Rc::new(Ty_::Tprim(Tprim::Tint))),
        &int()
    ));
    // Two shapes that come from the same alias are equal.
    let from_alias = |fields| {
        mk(Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
            origin: TypeOrigin::FromAlias("\\A".to_string(), None),
            unknown_value: nothing(),
            fields,
        })))
    };
    assert!(ty_equal(
        false,
        &from_alias(TShapeMap::new()),
        &from_alias(
            [(
                lit("a"),
                ShapeFieldType {
                    optional: false,
                    ty: int()
                }
            )]
            .into()
        )
    ));
    assert_eq!(
        ty_compare(
            false,
            &shape(vec![("a", false, int())], nothing()),
            &shape(vec![("a", true, int())], nothing())
        ),
        Less
    );
    // Exact comes before nonexact.
    let exact = mk(Ty_::Tclass(
        (Pos::NONE, "\\C".to_string()),
        Exact::Exact,
        vec![],
    ));
    assert_eq!(ty_compare(false, &exact, &class("\\C", vec![])), Less);
}

#[test]
fn docs() {
    use super::doc::*;
    let d = Doc::Concat(vec![
        Doc::Space,
        text("a"),
        Doc::Space,
        Doc::Space,
        Doc::Nothing,
        text("b"),
        text("c"),
        Doc::Space,
    ]);
    assert_eq!(format_doc_unbroken(&d), " a bc");
    assert_eq!(strip(&format_doc_unbroken(&d)), "a bc");
    let d = Doc::Concat(vec![
        Doc::Newline,
        text("where"),
        Doc::Space,
        Doc::Newline,
        text("x"),
    ]);
    assert_eq!(format_doc_unbroken(&d), "where\nx");
    assert_eq!(strip(" \t\na b\r\n"), "a b");
}

#[test]
fn desugared_contexts() {
    assert_eq!(
        split_desugared_ctx_tparams_gen(
            vec!["T/[ctx $f]", "T", "T/[$x::C]", "U"],
            |s| s.to_string()
        ),
        (
            vec!["ctx $f".to_string(), "$x::C".to_string()],
            vec!["T", "U"]
        )
    );
    assert_eq!(strip_ns("\\HH\\vec"), "vec");
}
