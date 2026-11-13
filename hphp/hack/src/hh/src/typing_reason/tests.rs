// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! The texts were compared with the expected outputs of
//! `hphp/hack/test/typecheck` (the second line of each `File` entry, with the
//! types replaced); where a comment names a file, that file has the text. The
//! texts that no test produces were written from the OCaml alone.

use std::sync::Arc;

use relative_path::Prefix;
use relative_path::RelativePath;

use super::*;

/// A position on line `line`.
fn p(line: usize) -> Pos {
    let file = Arc::new(RelativePath::make(Prefix::Root, "a.php".into()));
    Pos::from_line_cols_offset(file, line, 0..1, line * 100)
}

/// The lines of `r` after "Expected `int`", with the line of each position.
fn lines(r: &T_) -> Vec<(usize, String)> {
    to_string("Expected `int`", r)
        .into_iter()
        .map(|(pos, s)| (if pos.is_none() { 0 } else { pos.line() }, s))
        .collect()
}

/// The text of a reason that gives one line, at line 1.
fn one(r: T) -> String {
    match lines(&r).as_slice() {
        [(1, s)] => s.clone(),
        l => panic!("expected one line at line 1, got {:?}", l),
    }
}

fn e(suffix: &str) -> String {
    format!("Expected `int`{}", suffix)
}

#[test]
fn strip_ns_and_autoimport() {
    assert_eq!(strip_ns("\\Foo\\Bar"), "Foo\\Bar");
    assert_eq!(strip_ns("\\HH\\vec"), "vec");
    assert_eq!(strip_ns("\\HH\\Lib\\Vec"), "HH\\Lib\\Vec");
    assert_eq!(strip_ns("HH\\Traversable"), "Traversable");
    assert_eq!(strip_ns("\\HH\\string"), "string");
    assert_eq!(strip_ns("\\HH\\supportdyn"), "supportdyn");
    assert_eq!(strip_ns("\\HH\\FunctionRef"), "HH\\FunctionRef");
    // test/typecheck/class_pointers/case_types.php.exp:
    // "`HH\class_or_classname<C>`"
    assert_eq!(
        strip_ns("\\HH\\class_or_classname"),
        "HH\\class_or_classname"
    );
    assert_eq!(utils_strip_all_ns("\\Foo\\Bar"), "Bar");
    assert_eq!(utils_strip_all_ns("Bar"), "Bar");
}

#[test]
fn witness_locl() {
    assert_eq!(one(witness(p(1))), e(""));
    assert_eq!(
        one(idx_vector(p(1))),
        e(" because only `int` can be used to index into a `Vector` or `vec`.")
    );
    assert_eq!(
        one(idx_string(p(1))),
        e(" because only `int` can be used to index into a `string`.")
    );
    assert_eq!(
        one(foreach(p(1))),
        e(" because this is used in a `foreach` statement")
    );
    assert_eq!(
        one(asyncforeach(p(1))),
        e(" because this is used in a `foreach` statement with `await as`")
    );
    assert_eq!(
        one(arith(p(1))),
        e(" because this is used in an arithmetic operation")
    );
    assert_eq!(
        one(arith_ret(p(1))),
        e(" because this is the result of an arithmetic operation")
    );
    assert_eq!(
        one(arith_ret_int(p(1))),
        e(" because this is the result of an integer arithmetic operation")
    );
    assert_eq!(
        one(arith_dynamic(p(1))),
        e(
            " because this is the result of an arithmetic operation with two arguments typed `dynamic`"
        )
    );
    assert_eq!(
        one(bitwise_dynamic(p(1))),
        e(
            " because this is the result of a bitwise operation with all arguments typed `dynamic`"
        )
    );
    assert_eq!(
        one(incdec_dynamic(p(1))),
        e(
            " because this is the result of an increment/decrement of an argument typed `dynamic`"
        )
    );
    assert_eq!(
        one(comp(p(1))),
        e(" because this is the result of a comparison")
    );
    assert_eq!(
        one(concat_ret(p(1))),
        e(" because this is the result of a concatenation")
    );
    assert_eq!(
        one(condition(p(1))),
        e(" because this is used as a condition")
    );
    assert_eq!(
        one(logic_ret(p(1))),
        e(" because this is the result of a logical operation")
    );
    assert_eq!(
        one(bitwise(p(1))),
        e(" because this is used in a bitwise operation")
    );
    assert_eq!(
        one(bitwise_ret(p(1))),
        e(" because this is the result of a bitwise operation")
    );
    assert_eq!(
        one(no_return(p(1))),
        e(" because this function does not always return a value")
    );
    assert_eq!(
        one(no_return_async(p(1))),
        e(" because this function does not always return a value")
    );
    assert_eq!(
        one(ret_fun_kind((p(1), FunKind::FAsyncGenerator))),
        e(" (result of `async function` containing a `yield`)")
    );
    assert_eq!(
        one(ret_fun_kind((p(1), FunKind::FGenerator))),
        e(" (result of function containing a `yield`)")
    );
    assert_eq!(
        one(ret_fun_kind((p(1), FunKind::FAsync))),
        e(" (result of an `async` function)")
    );
    assert_eq!(one(ret_fun_kind((p(1), FunKind::FSync))), e(""));
    assert_eq!(
        one(throw(p(1))),
        e(" because it is used as an exception")
    );
    assert_eq!(
        one(placeholder(p(1))),
        e(" (`$_` is a placeholder variable not meant to be used)")
    );
    assert_eq!(
        one(ret_div(p(1))),
        e(" because it is the result of a division `/`")
    );
    assert_eq!(
        one(yield_gen(p(1))),
        e(" (result of function with `yield` in the body)")
    );
    assert_eq!(
        one(yield_asyncgen(p(1))),
        e(" (result of `async function` with `yield` in the body)")
    );
    assert_eq!(
        one(yield_asyncnull(p(1))),
        e(" because `yield x` is equivalent to `yield null => x` in an `async` function")
    );
    assert_eq!(
        one(yield_send(p(1))),
        e(" (`$generator->send()` can always send a `null` back to a `yield`)")
    );
    assert_eq!(
        one(unknown_class(p(1))),
        e("; this class name is unknown to Hack")
    );
    assert_eq!(one(var_param(p(1))), e(" (variadic argument)"));
    assert_eq!(
        one(unpack_param((p(1), p(2), 0))),
        e(" (it is unpacked with `...`)")
    );
    assert_eq!(one(nullsafe_op(p(1))), e(" (use of `?->` operator)"));
    assert_eq!(one(nullsafe_pipe_op(p(1))), e(" (use of `|?>` operator)"));
    assert_eq!(
        one(predicated((p(1), "is_int".to_string()))),
        e(" from the argument to this is_int test")
    );
    assert_eq!(
        one(is_refinement(p(1))),
        e(" from this `is` expression test")
    );
    assert_eq!(one(as_refinement(p(1))), e(" from this \"as\" assertion"));
    assert_eq!(one(equal(p(1))), e(" from this equality test"));
    assert_eq!(
        one(using(p(1))),
        e(" because it was assigned in a `using` clause")
    );
    assert_eq!(
        one(dynamic_prop(p(1))),
        e(", the result of accessing a property of a `dynamic` type")
    );
    assert_eq!(
        one(dynamic_call(p(1))),
        e(", the result of calling a `dynamic` type as a function")
    );
    assert_eq!(
        one(dynamic_construct(p(1))),
        e(", the result of constructing an object with a `dynamic` type")
    );
    assert_eq!(
        one(idx_dict(p(1))),
        e(
            " because only array keys can be used to index into a `Map`, `dict`, `darray`, `Set`, or `keyset`"
        )
    );
    assert_eq!(
        one(idx_set_element(p(1))),
        e(" because only array keys can be used as elements of `keyset` or `Set`")
    );
    assert_eq!(
        one(unset_field((p(1), "x".to_string()))),
        e(" because the field `x` was unset here")
    );
    assert_eq!(one(regex(p(1))), e(" resulting from this regex pattern"));
    assert_eq!(
        one(type_variable(p(1), 3)),
        e(" because a type could not be determined here")
    );
    // (This text, for other names: test/typecheck/gen1.php.imp_pess_exp)
    assert_eq!(
        one(type_variable_generics(
            (p(1), "T".to_string(), "f".to_string()),
            3
        )),
        e(
            " because type parameter `T` of `f` could not be determined. Please add explicit type parameters to the invocation of `f`"
        )
    );
    assert_eq!(
        one(type_variable_error(p(1), 3)),
        e(" because there was another error")
    );
    assert_eq!(
        one(shape((p(1), "Shapes::idx".to_string()))),
        e(" because `Shapes::idx` expects a shape")
    );
    assert_eq!(one(shape_literal(p(1))), e(""));
    assert_eq!(
        one(destructure(p(1))),
        e(" resulting from a list destructuring assignment or a splat")
    );
    assert_eq!(
        one(shape_or_tuple_destructure(p(1))),
        e(" resulting from a shape or tuple destructuring pattern")
    );
    // These three do not use the prefix.
    assert_eq!(
        one(key_value_collection_key(p(1))),
        "This is a key-value collection, which requires `arraykey`-typed keys"
    );
    assert_eq!(one(concat_operand(p(1))), "Expected `string` or `int`");
    assert_eq!(one(interp_operand(p(1))), "Expected `string` or `int`");
    assert_eq!(
        one(splice(p(1))),
        e(" because this is being spliced into another Expression Tree")
    );
    assert_eq!(
        one(et_boolean(p(1))),
        e(" because Expression Trees do not allow coercion of truthy values")
    );
    assert_eq!(one(missing_class(p(1))), e(" because class was missing"));
    assert_eq!(
        one(captured_like(p(1))),
        e(" because this is the type of a local that was captured in a closure")
    );
    // test/typecheck/mismatch_through_unsafe_cast.php.exp
    assert_eq!(
        one(unsafe_cast(p(1))),
        e(
            " because the expression went through a `HH\\FIXME\\UNSAFE_CAST`. The type might be a lie!"
        )
    );
    assert_eq!(one(pattern(p(1))), e(" because of this pattern"));
    assert_eq!(one(join_point(p(1))), e(" because of this statement"));
    assert_eq!(
        one(static_prop_access(p(1))),
        e(" because of this static property access")
    );
    assert_eq!(
        one(class_const_access(p(1))),
        e(" because of this class constant access")
    );
}

#[test]
fn witness_decl() {
    assert_eq!(one(witness_from_decl(p(1))), e(""));
    assert_eq!(
        one(idx_vector_from_decl(p(1))),
        e(" because only `int` can be used to index into a `Vector` or `vec`.")
    );
    assert_eq!(
        one(idx_string_from_decl(p(1))),
        e(" because only `int` can be used to index into a `string`.")
    );
    assert_eq!(
        one(ret_fun_kind_from_decl((p(1), FunKind::FAsync))),
        e(" (result of an `async` function)")
    );
    assert_eq!(one(hint(p(1))), e(""));
    assert_eq!(
        one(class_class((p(1), "\\C".to_string()))),
        e("; implicitly defined constant `::class` is a reference to class `C`")
    );
    assert_eq!(one(var_param_from_decl(p(1))), e(" (variadic argument)"));
    assert_eq!(one(tuple_from_splat(p(1))), e(" (tuple from parameters)"));
    assert_eq!(one(inout_param(p(1))), e(" (`inout` parameter)"));
    assert_eq!(
        one(tconst_no_cstr((p(1), "Ti".to_string()))),
        e(" because the type constant Ti lacks a constraint")
    );
    assert_eq!(
        one(varray_or_darray_key(p(1))),
        "This is varray_or_darray, which requires arraykey-typed keys when used with an array (used like a hashtable)"
    );
    assert_eq!(
        one(vec_or_dict_key(p(1))),
        "This is vec_or_dict, which requires keys that have type arraykey"
    );
    assert_eq!(
        one(missing_optional_field((p(1), "x".to_string()))),
        e(" because the field `x` may be set to any type in this shape")
    );
    assert_eq!(
        one(implicit_upper_bound((p(1), "nonnull".to_string()))),
        e(" arising from an implicit `as nonnull` constraint on this type")
    );
    assert_eq!(
        one(global_type_variable_generics((
            p(1),
            "T".to_string(),
            "f".to_string()
        ))),
        e(
            " because type parameter `T` of `f` could not be determined. Please add explicit type parameters to the invocation of `f`"
        )
    );
    assert_eq!(
        one(solve_fail(p(1))),
        e(" because a type could not be determined here")
    );
    assert_eq!(
        one(cstr_on_generics((p(1), (p(2), "T".to_string())))),
        e("")
    );
    assert_eq!(
        one(enforceable(p(1))),
        e(" because it is an unenforceable type")
    );
    assert_eq!(one(global_class_prop(p(1))), e(""));
    assert_eq!(one(global_fun_param(p(1))), e(""));
    assert_eq!(one(global_fun_ret(p(1))), e(""));
    assert_eq!(
        one(default_capability(p(1))),
        e(" because the function did not have an explicit context")
    );
    assert_eq!(
        one(support_dynamic_type(p(1))),
        e(" because method or function was called on dynamic or like-type")
    );
    assert_eq!(
        one(support_dynamic_type_assume(p(1))),
        e(" because method must be callable in a dynamic context")
    );
    assert_eq!(
        one(pessimised_inout(p(1))),
        e(" because the type of this inout parameter is implicitly a like-type")
    );
    assert_eq!(
        one(pessimised_return(p(1), PessimiseReason::PRgenericParam)),
        e(
            " because the type of this return is implicitly a like-type due to unenforced generic parameter"
        )
    );
    assert_eq!(
        one(pessimised_prop(p(1), PessimiseReason::PRenum)),
        e(
            " because the type of this property is implicitly a like-type due to enum enforced only at base type"
        )
    );
    assert_eq!(
        one(pessimised_this(p(1))),
        e(
            " from \"as this\" or \"is this\" in a class whose generic parameters (or those of a subclass) are erased at runtime"
        )
    );
    // test/typecheck/typedef_cycles_via_constraints2.php.exp
    assert_eq!(
        one(illegal_recursive_type(p(1), "\\A".to_string())),
        e(
            ". Using `mixed` instead of A because this is an illegal recursive use of A in the definition of A"
        )
    );
    assert_eq!(one(enforced_type(p(1))), e(""));
}

#[test]
fn polymorphic_type_param() {
    // test/typecheck/first_class_polymorphism/polymorphic_function_hint_sub_bad.php.exp
    let r = super::polymorphic_type_param((p(1), "T#1".to_string(), "T".to_string(), 1));
    assert_eq!(
        to_string("Expected `T#1`", &r)[0].1,
        "Expected `T#1` which corresponds to the rank-2 type parameter `T` in the polymorphic function"
    );
    assert_eq!(
        to_string("But got `vec<T#1>`", &r)[0].1,
        "But got `vec<T#1>` where `T#1` corresponds to the rank-2 type parameter `T` in the polymorphic function"
    );
}

#[test]
fn pessimise_reasons() {
    use PessimiseReason::*;
    let all = [
        (PRabstract, "abstract", "unknown enforcement for abstract method"),
        (PRgenericParam, "generic_param", "unenforced generic parameter"),
        (PRthis, "this", "unenforced this"),
        (PRgenericApply, "generic_apply", "unenforced generic type arguments"),
        (PRtupleOrShape, "tuple_or_shape", "unenforced tuple or shape"),
        (PRtypeconst, "typeconst", "unenforced type constant"),
        (PRcase, "case", "unenforced case type"),
        (PRenum, "enum", "enum enforced only at base type"),
        (PRopaque, "opaque", "opaque type"),
        (PRdynamic, "dynamic", "unenforced dynamic"),
        (PRfun, "function", "unenforced function type"),
        (PRclassptr, "classptr", "unenforced class pointer type"),
        (PRvoidOrNoreturn, "void_or_noreturn", "unenforced void or noreturn type"),
        (PRrefinement, "type_refinement", "unenforced type refinement"),
        (
            PRunionOrIntersection,
            "union_or_intersection",
            "unenforced union or intersection",
        ),
        (PRxhp, "xhp", "unenforced XHP attribute"),
    ];
    for (pr, short, long) in all {
        assert_eq!(string_of_pessimise_reason(pr), short);
        assert_eq!(pessimise_reason_to_string(pr), long);
    }
    assert_eq!(
        to_constructor_string(&pessimised_return(p(1), PRthis)),
        "Rpessimised_return_this"
    );
}

#[test]
fn markers() {
    assert_eq!(lines(&none()), vec![(0, e(""))]);
    assert_eq!(lines(&invalid()), vec![(0, e(""))]);
    assert_eq!(lines(&missing_field()), vec![(0, e(""))]);
}

#[test]
fn flows() {
    // The origin of a flow is what is reported.
    let r = flow_assign(arith_ret(p(1)), witness(p(2)));
    assert_eq!(
        lines(&r),
        vec![(1, e(" because this is the result of an arithmetic operation"))]
    );
    assert_eq!(to_pos(&r), p(1));
    // `flow` keeps flows right-nested.
    let r = flow_local(flow_assign(witness(p(1)), witness(p(2))), witness(p(3)));
    match &*r {
        T_::Flow { from, into, kind } => {
            assert!(matches!(**from, T_::FromWitnessLocl(_)));
            assert!(matches!(kind, FlowKind::FlowAssign));
            assert!(matches!(
                **into,
                T_::Flow {
                    kind: FlowKind::FlowLocal,
                    ..
                }
            ));
        }
        _ => panic!(),
    }
    // An array access reports the access, then the definition.
    let r = flow_array_get(witness(p(1)), witness(p(2)));
    assert_eq!(
        lines(&r),
        vec![(2, e("")), (1, "  from this definition".to_string())]
    );
    // With the solution of a type variable in scope, the flow is followed
    // into the variable, and the solution is reported.
    let r = solved(
        7,
        arith_ret(p(5)),
        flow_assign(type_variable(p(1), 7), witness(p(2))),
    );
    assert_eq!(
        lines(&r),
        vec![(5, e(" because this is the result of an arithmetic operation"))]
    );
    // ... and without it, the variable itself.
    let r = flow_assign(type_variable(p(1), 7), witness(p(2)));
    assert_eq!(
        lines(&r),
        vec![(1, e(" because a type could not be determined here"))]
    );
    // A flow that does not go through the variable still reports its origin.
    let r = solved(7, arith_ret(p(5)), flow_assign(witness(p(1)), witness(p(2))));
    assert_eq!(lines(&r), vec![(1, e(""))]);
    // A flow that reaches the variable later.
    let r = solved(
        7,
        arith_ret(p(5)),
        flow_assign(witness(p(1)), type_variable(p(2), 7)),
    );
    assert_eq!(
        lines(&r),
        vec![(5, e(" because this is the result of an arithmetic operation"))]
    );
    // reverse_flow
    let r = flow_local(flow_assign(witness(p(1)), witness(p(2))), witness(p(3)));
    assert_eq!(to_pos(&reverse_flow(&r)), p(3));
    assert_eq!(to_pos(&reverse_flow(&witness(p(4)))), p(4));
}

#[test]
fn projections_and_axioms() {
    let sub = witness(p(1));
    let sup = witness(p(2));
    // Covariant constructor argument: nothing is added.
    let r = prj_ctor_co(
        sub.clone(),
        witness(p(3)),
        sup.clone(),
        CtorKind::CtorClass,
        "\\Box".to_string(),
        0,
        false,
    );
    assert_eq!(lines(&r), vec![(3, e(""))]);
    // test/typecheck/contravariance_bad2.php.exp
    let r = prj_ctor_contra(
        sub.clone(),
        sup.clone(),
        witness(p(3)),
        CtorKind::CtorClass,
        "\\Box".to_string(),
        0,
        false,
    );
    assert_eq!(
        lines(&r),
        vec![
            (3, e("")),
            (
                3,
                "This type argument to `Box` only allows supertypes (it is contravariant)"
                    .to_string()
            )
        ]
    );
    // test/typecheck/new_static2.php.exp
    let r = prj_ctor_co(
        sub.clone(),
        witness(p(3)),
        sup.clone(),
        CtorKind::CtorClass,
        "\\HH\\Vector".to_string(),
        0,
        true,
    );
    assert_eq!(
        lines(&r),
        vec![
            (3, e("")),
            (
                3,
                "This type argument to `Vector` must match exactly (it is invariant)"
                    .to_string()
            )
        ]
    );
    // The same notes under a lower bound.
    let lower = trans_lower_bound(witness(p(4)), r);
    assert_eq!(
        lines(&lower),
        vec![
            (4, e("")),
            (
                4,
                "This type argument to `Vector` must match exactly (it is invariant)"
                    .to_string()
            )
        ]
    );
    assert_eq!(
        lines(&trans_lower_bound(witness(p(4)), witness(p(5)))),
        vec![(4, e(""))]
    );
    assert_eq!(
        lines(&prj_union_sub(witness(p(1)), witness(p(2)))),
        vec![(2, e(""))]
    );
    assert_eq!(
        lines(&definition(p(9), witness(p(2)))),
        vec![(2, e(""))]
    );
    assert_eq!(
        lines(&axiom_extends(witness(p(1)), witness(p(2)))),
        vec![(2, e(""))]
    );
    // (This text, for other names: test/typecheck/tconst_unsoundness.php.constraint_method_call.exp)
    assert_eq!(
        lines(&axiom_upper_bound(
            witness(p(2)),
            witness(p(1)),
            "\\T".to_string()
        )),
        vec![(1, e("")), (2, "  by the definition of `T`".to_string())]
    );
    for internal in ["this", "T#1", "<expr#1>::T", "$x", "\\HH\\supportdyn"] {
        assert_eq!(
            lines(&axiom_upper_bound(
                witness(p(2)),
                witness(p(1)),
                internal.to_string()
            )),
            vec![(1, e(""))]
        );
    }
    assert_eq!(
        get_top_fun_param_prj_idx(&prj_fn_param(
            witness(p(1)),
            witness(p(2)),
            witness(p(3)),
            4,
            5
        )),
        Some(5)
    );
}

#[test]
fn legacy_reasons() {
    assert_eq!(
        lines(&idx((p(1), none()))),
        vec![
            (1, e("")),
            (1, "This can only be indexed with integers".to_string())
        ]
    );
    assert_eq!(
        lines(&idx((p(1), witness(p(2))))),
        vec![
            (1, e("")),
            (2, "This can only be indexed with integers".to_string())
        ]
    );
    // test/typecheck/error_messages/float.php.exp, test/typecheck/mul_union.php.exp
    assert_eq!(
        lines(&arith_ret_float((p(1), witness(p(2)), ArgPosition::Afirst))),
        vec![
            (
                1,
                e(
                    " because this is the result of an arithmetic operation with a `float` as the first argument."
                )
            ),
            (
                2,
                "Here is why I think the argument is a `float`: this is a `float`".to_string()
            )
        ]
    );
    assert_eq!(
        lines(&arith_ret_num((
            p(1),
            arith_ret_num((p(2), witness(p(3)), ArgPosition::Aonly)),
            ArgPosition::Asecond
        ))),
        vec![
            (
                1,
                e(
                    " because this is the result of an arithmetic operation with a `num` as the second argument, and no `float`s."
                )
            ),
            (
                3,
                "Here is why I think the argument is a `num`: this is a `num`".to_string()
            )
        ]
    );
    for (source, cause) in [
        (BlameSource::BSlambda, "by this lambda function"),
        (BlameSource::BScall, "during this call"),
        (BlameSource::BSassignment, "by this assignment"),
        (BlameSource::BSoutOfScope, "because of scope change"),
    ] {
        assert_eq!(
            lines(&lost_info((
                "\\C::$x".to_string(),
                witness(p(1)),
                Blame::Blame(p(2), source)
            ))),
            vec![
                (1, e("")),
                (
                    2,
                    format!(
                        "All the local information about `C::$x` has been invalidated {}.\nThis is a limitation of the type-checker; use a local if that's the problem.",
                        cause
                    )
                )
            ]
        );
    }
    // test/typecheck/printf.php.exp
    assert_eq!(
        lines(&format((p(1), "%d".to_string(), none()))),
        vec![(1, e(" because of the `%d` format specifier"))]
    );
    assert_eq!(
        lines(&format((p(1), "%d".to_string(), arith(p(2))))),
        vec![
            (1, e(" because of the `%d` format specifier")),
            (
                2,
                " because this is used in an arithmetic operation".to_string()
            )
        ]
    );
    assert_eq!(
        lines(&instantiate(witness(p(1)), "T".to_string(), witness(p(2)))),
        vec![(1, e("")), (2, "  via this generic `T`".to_string())]
    );
    assert_eq!(to_pos(&instantiate(witness(p(1)), "T".to_string(), witness(p(2)))), p(1));
    assert_eq!(
        lines(&typeconst((
            none(),
            (p(1), "T".to_string()),
            "`C`".into(),
            witness(p(2))
        ))),
        vec![
            (
                1,
                "Expected `int`\n  by accessing the type constant `T`".to_string()
            ),
            (2, "on `C`".to_string())
        ]
    );
    assert_eq!(
        to_string(
            "",
            &typeconst((
                none(),
                (p(1), "T".to_string()),
                "`C`".into(),
                witness(p(2))
            ))
        )[0]
        .1,
        "by accessing the type constant `T`"
    );
    assert_eq!(
        lines(&typeconst((
            witness(p(3)),
            (p(1), "T".to_string()),
            "`C`".into(),
            witness(p(2))
        ))),
        vec![
            (3, e("")),
            (
                1,
                "  resulting from accessing the type constant 'T'".to_string()
            ),
            (2, "  on `C`".to_string())
        ]
    );
    assert_eq!(
        lines(&type_access((
            witness(p(1)),
            vec![(witness(p(2)), "T".into()), (witness(p(3)), "U".into())]
        ))),
        vec![
            (1, e("")),
            (
                2,
                "  resulting from expanding the type constant `T`".to_string()
            ),
            (3, "  then expanding the type constant `U`".to_string())
        ]
    );
    assert_eq!(
        lines(&type_access((witness(p(1)), vec![]))),
        vec![(1, e(""))]
    );
    // A type access of a type constant reason drops the type constant.
    assert_eq!(
        lines(&type_access((
            typeconst((
                none(),
                (p(1), "T".to_string()),
                "`C`".into(),
                witness(p(2))
            )),
            vec![(witness(p(3)), "T".into())]
        ))),
        vec![(3, e(""))]
    );
    // Nested type accesses are flattened, the outer expansions first.
    assert_eq!(
        lines(&type_access((
            type_access((witness(p(1)), vec![(witness(p(2)), "T".into())])),
            vec![(witness(p(3)), "U".into())]
        ))),
        vec![
            (1, e("")),
            (
                3,
                "  resulting from expanding the type constant `U`".to_string()
            ),
            (2, "  then expanding the type constant `T`".to_string())
        ]
    );
    // test/typecheck/escape/escape_reason.php.exp
    assert_eq!(
        lines(&expr_dep_type((
            witness(p(1)),
            p(2),
            ExprDepTypeReason::ERexpr(1)
        ))),
        vec![
            (1, e("")),
            (
                2,
                "  where `<expr#1>` is a reference to this expression".to_string()
            )
        ]
    );
    assert_eq!(
        expr_dep_type_reason_string(&ExprDepTypeReason::ERstatic),
        "where `<static>` refers to the late bound type of the enclosing class"
    );
    assert_eq!(
        expr_dep_type_reason_string(&ExprDepTypeReason::ERclass("\\C".to_string())),
        "where the class `C` was referenced here"
    );
    assert_eq!(
        expr_dep_type_reason_string(&ExprDepTypeReason::ERparent("\\C".to_string())),
        "where the class `C` (the parent of the enclosing) class was referenced here"
    );
    assert_eq!(
        expr_dep_type_reason_string(&ExprDepTypeReason::ERself("\\C".to_string())),
        "where the class `C` was referenced here via the keyword `self`"
    );
    assert_eq!(
        expr_dep_type_reason_string(&ExprDepTypeReason::ERpu("T".to_string())),
        "where `T` is a type projected from this expression"
    );
    let no_hint = " because the type of the lambda parameter could not be determined. Please add a type hint to the parameter";
    assert_eq!(
        lines(&lambda_param((p(1), type_variable(p(2), 3)))),
        vec![(1, e(no_hint))]
    );
    assert_eq!(
        lines(&lambda_param((p(1), solve_fail(p(2))))),
        vec![(1, e(no_hint))]
    );
    assert_eq!(
        lines(&lambda_param((p(1), arith(p(2))))),
        vec![(2, e(" because this is used in an arithmetic operation"))]
    );
    assert_eq!(
        lines(&solved(
            3,
            arith(p(4)),
            lambda_param((p(1), type_variable(p(2), 3)))
        )),
        vec![(4, e(" because this is used in an arithmetic operation"))]
    );
    assert_eq!(
        lines(&dynamic_coercion(arith(p(2)))),
        vec![(2, e(" because this is used in an arithmetic operation"))]
    );
    assert_eq!(
        lines(&dynamic_partial_enforcement((
            p(1),
            "\\N\\C".to_string(),
            witness(p(2))
        ))),
        vec![
            (2, e("")),
            (1, "while allowing dynamic to flow into C".to_string())
        ]
    );
    // test/typecheck/escape/escape_reason.php.exp
    assert_eq!(
        lines(&rigid_tvar_escape((
            p(1),
            "lambda".to_string(),
            "T#1".to_string(),
            witness(p(2))
        ))),
        vec![
            (1, e(" because `T#1` escaped from lambda")),
            (2, "  where `T#1` originates from".to_string())
        ]
    );
    assert_eq!(
        lines(&support_dynamic_type_call((p(1), witness(p(2))))),
        vec![
            (
                1,
                e(
                    " because this dynamic or like type value passed through a function that supports dynamic calling"
                )
            ),
            (2, "The type originated from here".to_string())
        ]
    );
    assert_eq!(
        lines(&like_call((p(1), witness(p(2))))),
        vec![
            (
                1,
                e(
                    " because this dynamic or like type value was used as a receiver in a method call"
                )
            ),
            (2, "The type originated from here".to_string())
        ]
    );
    // test/typecheck/modules/internal_keyword.php.exp
    assert_eq!(
        lines(&opaque_type_from_module((
            p(1),
            "A".to_string(),
            witness(p(2))
        ))),
        vec![
            (
                1,
                e(
                    " because this is an internal symbol from module A, which is opaque outside of the module."
                )
            ),
            (2, "The type originated from here".to_string())
        ]
    );
}

#[test]
fn positions_and_priorities() {
    assert!(to_pos(&none()).is_none());
    assert_eq!(to_pos(&idx((p(1), witness(p(2))))), p(1));
    assert_eq!(to_pos(&lost_info(("x".to_string(), witness(p(1)), Blame::Blame(p(2), BlameSource::BScall)))), p(1));
    assert_eq!(
        to_pos(&typeconst((
            none(),
            (p(1), "T".to_string()),
            "C".into(),
            witness(p(2))
        ))),
        p(1)
    );
    assert_eq!(
        to_pos(&typeconst((
            witness(p(3)),
            (p(1), "T".to_string()),
            "C".into(),
            witness(p(2))
        ))),
        p(3)
    );
    assert_eq!(
        to_pos(&expr_dep_type((witness(p(1)), p(2), ExprDepTypeReason::ERstatic))),
        p(1)
    );
    assert_eq!(to_pos(&like_call((p(1), witness(p(2))))), p(1));
    assert_eq!(to_pos(&solved(1, witness(p(1)), witness(p(2)))), p(1));
    assert_eq!(get_pri(&none()), 0);
    assert_eq!(get_pri(&foreach(p(1))), 1);
    assert_eq!(get_pri(&arith(p(1))), 2);
    assert_eq!(get_pri(&witness(p(1))), 3);
    assert_eq!(get_pri(&hint(p(1))), 2);
    assert_eq!(
        get_pri(&lost_info((
            "x".to_string(),
            none(),
            Blame::Blame(p(1), BlameSource::BScall)
        ))),
        5
    );
    // Higher priorities first, then by position.
    assert!(compare(&witness(p(9)), &arith(p(1))) < 0);
    assert!(compare(&arith(p(1)), &arith(p(2))) < 0);
    assert_eq!(compare(&arith(p(1)), &hint(p(1))), 0);
    let moved = map_pos(&|_| p(7), &|_| p(8), &flow_assign(witness(p(1)), hint(p(2))));
    assert_eq!(to_pos(&moved), p(7));
    match &*moved {
        T_::Flow { into, .. } => assert_eq!(to_pos(&into), p(8)),
        _ => panic!(),
    }
}

#[test]
fn predicates_and_localize() {
    use oxidized::typing_reason::T_ as D;
    let r = localize(&D::FromWitnessDecl(WitnessDecl::Hint(p(1))));
    assert!(predicates::is_hint(&r));
    assert!(predicates::is_hint(&flow_assign(r.clone(), witness(p(2)))));
    assert!(!predicates::is_hint(&witness(p(1))));
    assert!(predicates::is_none(&localize(&D::NoReason)));
    assert!(matches!(*localize(&D::Invalid), T_::Invalid));
    let r = localize(&D::ExprDepType(
        Box::new(D::FromWitnessDecl(WitnessDecl::Hint(p(1)))),
        p(2),
        ExprDepTypeReason::ERstatic,
    ));
    assert!(predicates::unpack_expr_dep_type_opt(&r).is_some());
    let r = localize(&D::Typeconst(
        Box::new(D::NoReason),
        (p(1), "T".to_string()),
        oxidized::lazy::Lazy("`C`".to_string()),
        Box::new(D::FromWitnessDecl(WitnessDecl::Hint(p(2)))),
    ));
    assert_eq!(lines(&r)[1], (2, "on `C`".to_string()));
    let r = localize(&D::Instantiate {
        type__: Box::new(D::FromWitnessDecl(WitnessDecl::Hint(p(1)))),
        var_name: "T".to_string(),
        var: Box::new(D::FromWitnessDecl(WitnessDecl::Hint(p(2)))),
    });
    assert!(predicates::is_instantiate(&r));
    assert_eq!(predicates::outer_constructor_string(&r), "Rinstantiate");
    // The outermost reason of a solved type variable is its solution's.
    let r = solved(3, captured_like(p(1)), type_variable(p(2), 3));
    assert!(predicates::is_captured_like(&r));
    assert_eq!(
        predicates::unpack_unpack_param_opt(&unpack_param((p(1), p(2), 3))),
        Some((p(1), p(2), 3))
    );
    assert_eq!(
        predicates::unpack_shape_literal_opt(&shape_literal(p(1))),
        Some(p(1))
    );
    assert!(predicates::is_enforced_type(&enforced_type(p(1))));
    assert!(predicates::is_opaque_type_from_module(
        &opaque_type_from_module((p(1), "m".to_string(), none()))
    ));
    assert!(
        predicates::unpack_cstr_on_generics_opt(&cstr_on_generics((
            p(1),
            (p(2), "T".to_string())
        )))
        .is_some()
    );
    // A lazy string is forced once, when the reason is rendered.
    let lazy = LazyString::new(|| "`D`".to_string());
    let r = typeconst((none(), (p(1), "T".to_string()), lazy, none()));
    assert_eq!(lines(&force_lazy_values(&r))[1].1, "on `D`");
}

#[test]
fn ureasons() {
    use Ureason::*;
    // The claims of the subtyping errors (most of them occur in the expected
    // outputs of test/typecheck).
    assert_eq!(string_of_ureason(&URnone), "Typing error");
    assert_eq!(string_of_ureason(&URreturn), "Invalid return type");
    assert_eq!(string_of_ureason(&URhint), "Wrong type hint");
    assert_eq!(string_of_ureason(&URassign), "Invalid assignment");
    assert_eq!(
        string_of_ureason(&URassignInout),
        "Invalid assignment to an `inout` parameter"
    );
    assert_eq!(string_of_ureason(&URforeach), "Invalid `foreach`");
    assert_eq!(string_of_ureason(&URthrow), "Invalid exception");
    assert_eq!(
        string_of_ureason(&URvector),
        "Some elements in this collection are incompatible"
    );
    assert_eq!(
        string_of_ureason(&URkey("\\HH\\dict".to_string())),
        "The keys of this `dict` are incompatible"
    );
    assert_eq!(
        string_of_ureason(&URvalue("\\HH\\Map".to_string())),
        "The values of this `Map` are incompatible"
    );
    assert_eq!(
        string_of_ureason(&URawait),
        "`await` can only operate on an `Awaitable`"
    );
    assert_eq!(
        string_of_ureason(&URdelay),
        "`delay` can only operate on an `Awaitable`"
    );
    assert_eq!(string_of_ureason(&URyield), "Invalid `yield`");
    assert_eq!(
        string_of_ureason(&URxhp("\\:foo".to_string(), "bar".to_string())),
        "Invalid xhp value for attribute `bar` in `:foo`"
    );
    assert_eq!(
        string_of_ureason(&URxhpSpread),
        "The attribute spread operator cannot be called on non-XHP"
    );
    assert_eq!(
        string_of_ureason(&index_array()),
        "Invalid index type for this array"
    );
    assert_eq!(
        string_of_ureason(&index_tuple()),
        "Invalid index type for this tuple"
    );
    assert_eq!(
        string_of_ureason(&index_shape()),
        "Invalid index type for this shape"
    );
    assert_eq!(
        string_of_ureason(&index_class("\\HH\\Vector")),
        "Invalid index type for this Vector"
    );
    assert_eq!(
        string_of_ureason(&set_element("\\HH\\keyset")),
        "Invalid element type for this keyset"
    );
    assert_eq!(string_of_ureason(&URparam), "Invalid argument");
    assert_eq!(
        string_of_ureason(&URparamInout),
        "Invalid argument to an `inout` parameter"
    );
    assert_eq!(string_of_ureason(&URarrayValue), "Incompatible field values");
    assert_eq!(string_of_ureason(&URpairValue), "Incompatible pair values");
    assert_eq!(
        string_of_ureason(&URtupleAccess),
        "Tuple elements can only be accessed with an integer literal"
    );
    assert_eq!(
        string_of_ureason(&URtupleOOB),
        "Tuple accessed with an index out of bounds"
    );
    assert_eq!(
        string_of_ureason(&URpairAccess),
        "Pair elements can only be accessed with an integer literal"
    );
    assert_eq!(
        string_of_ureason(&URnewtypeCstr),
        "Invalid constraint on `newtype`"
    );
    assert_eq!(
        string_of_ureason(&URclassReq),
        "Unable to satisfy trait/interface requirement"
    );
    assert_eq!(
        string_of_ureason(&URenum),
        "Constant does not match the type of the enum it is in"
    );
    assert_eq!(
        string_of_ureason(&URenumInclude),
        "Inclusion of enum of incompatible type"
    );
    assert_eq!(string_of_ureason(&URenumCstr), "Invalid constraint on enum");
    assert_eq!(
        string_of_ureason(&URenumUnderlying),
        "Invalid underlying type for enum"
    );
    assert_eq!(
        string_of_ureason(&URenumIncompatibleCstr),
        "Underlying type for enum is incompatible with constraint"
    );
    assert_eq!(
        string_of_ureason(&URtypeconstCstr),
        "Unable to satisfy constraint on this type constant"
    );
    assert_eq!(
        string_of_ureason(&URsubsumeTconstCstr),
        "The constraint on this type constant is inconsistent with its parent"
    );
    assert_eq!(
        string_of_ureason(&URsubsumeTconstAssign),
        "The assigned type of this type constant is inconsistent with its parent"
    );
    assert_eq!(
        string_of_ureason(&URclone),
        "Clone cannot be called on non-object"
    );
    assert_eq!(
        string_of_ureason(&URusing),
        "Using cannot be used on non-disposable expression"
    );
    assert_eq!(
        string_of_ureason(&URstrConcat),
        "String concatenation can only be performed on string and int arguments"
    );
    assert_eq!(
        string_of_ureason(&URstrInterp),
        "Only string and int values can be used in string interpolation"
    );
    assert_eq!(string_of_ureason(&URdynamicProp), "Dynamic access of property");
    assert_eq!(
        string_of_ureason(&URlabel),
        "This label is not a valid reference to a member of the given enum class"
    );
    assert_eq!(
        string_of_ureason(&URcondition),
        "Only bool values can be used as a condition. Use a type-specific test instead."
    );
}

#[test]
fn constructor_strings() {
    assert_eq!(to_constructor_string(&none()), "Rnone");
    assert_eq!(to_constructor_string(&witness(p(1))), "Rwitness");
    assert_eq!(to_constructor_string(&hint(p(1))), "Rhint");
    assert_eq!(
        to_constructor_string(&flow_assign(witness(p(1)), witness(p(2)))),
        "Rflow"
    );
    assert_eq!(
        to_constructor_string(&support_dynamic_type_call((p(1), none()))),
        "RSDT_call"
    );
}
