// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

use std::cell::Cell;
use std::rc::Rc;
use std::sync::Arc;

use oxidized::error_codes::Typing;
use oxidized::message::Message;
use oxidized::pos::Pos;
use relative_path::Prefix;
use relative_path::RelativePath;

use super::primary::enum_::const_;
use super::*;

fn pos(line: usize) -> Pos {
    let file = Arc::new(RelativePath::make(Prefix::Dummy, "a.php".into()));
    Pos::from_line_cols_offset(file, line, 0..1, 0)
}

fn prim(line: usize) -> T {
    primary(primary::T::Unresolved_tyvar(pos(line)))
}

fn snd(line: usize) -> secondary::T {
    secondary::T::Missing_constructor(pos(line))
}

fn is_prim_at(t: &T, line: usize) -> bool {
    matches!(t, T::Primary(prim) if matches!(&**prim, primary::T::Unresolved_tyvar(p) if *p == pos(line)))
}

/// The primary error of `T::Primary`.
fn prim_of(t: &T) -> &primary::T {
    match t {
        T::Primary(prim) => prim,
        t => panic!("not a primary error: {:?}", t),
    }
}

// -- Lazy ---------------------------------------------------------------------

#[test]
fn lazy_is_forced_once_and_shared_by_clones() {
    let forced = Rc::new(Cell::new(0));
    let l = {
        let forced = Rc::clone(&forced);
        Lazy::new(move || {
            forced.set(forced.get() + 1);
            "T".to_string()
        })
    };
    let l2 = l.clone();
    assert!(!l.is_val());
    assert_eq!(forced.get(), 0);
    assert_eq!(l2.force(), "T");
    assert!(l.is_val());
    assert_eq!(l.force(), "T");
    assert_eq!(forced.get(), 1);
}

#[test]
fn lazy_debug_does_not_force() {
    let l = Lazy::new(|| 1);
    assert_eq!(format!("{:?}", l), "<not evaluated>");
    assert!(!l.is_val());
    l.force();
    assert_eq!(format!("{:?}", l), "1");
    assert_eq!(format!("{:?}", Lazy::from_val("x")), "\"x\"");
}

#[test]
fn lazy_map_and_bind_are_lazy() {
    let l = Lazy::new(|| 20);
    let m = l.map(|x| x + 1);
    let b = m.bind(|x| Lazy::from_val(x * 2));
    assert!(!l.is_val() && !m.is_val() && !b.is_val());
    assert_eq!(*b.force(), 42);
    assert!(l.is_val() && m.is_val());
    let v: Lazy<i32> = 3.into();
    assert!(v.is_val());
}

// -- Error --------------------------------------------------------------------

#[test]
fn grouping_a_singleton_is_the_element() {
    assert!(is_prim_at(&multiple(vec![prim(1)]), 1));
    assert!(is_prim_at(&union(vec![prim(2)]), 2));
    assert!(is_prim_at(&intersect(vec![prim(3)]), 3));
}

#[test]
fn grouping_several_keeps_the_order() {
    match multiple(vec![prim(1), prim(2), prim(3)]) {
        T::Multiple(ts) => {
            assert_eq!(ts.len(), 3);
            assert!(ts.iter().zip(1..).all(|(t, line)| is_prim_at(t, line)));
        }
        t => panic!("{:?}", t),
    }
    assert!(matches!(union(vec![prim(1), prim(2)]), T::Union(ts) if ts.len() == 2));
    assert!(matches!(intersect(vec![prim(1), prim(2)]), T::Intersection(ts) if ts.len() == 2));
}

#[test]
fn grouping_opt() {
    assert!(multiple_opt(vec![]).is_none());
    assert!(union_opt(vec![]).is_none());
    assert!(intersect_opt(vec![]).is_none());
    assert!(is_prim_at(&multiple_opt(vec![prim(1)]).unwrap(), 1));
    assert!(matches!(
        union_opt(vec![prim(1), prim(2)]),
        Some(T::Union(_))
    ));
    assert!(matches!(
        intersect_opt(vec![prim(1), prim(2)]),
        Some(T::Intersection(_))
    ));
}

#[test]
#[should_panic(expected = "called on empty list")]
fn multiple_of_nothing_fails() {
    multiple(vec![]);
}

#[test]
#[should_panic(expected = "called on empty list")]
fn union_of_nothing_fails() {
    union(vec![]);
}

#[test]
#[should_panic(expected = "called on empty list")]
fn intersect_of_nothing_fails() {
    intersect(vec![]);
}

#[test]
fn both_is_multiple_of_two() {
    match both(prim(1), prim(2)) {
        T::Multiple(ts) => {
            assert_eq!(ts.len(), 2);
            assert!(is_prim_at(&ts[0], 1) && is_prim_at(&ts[1], 2));
        }
        t => panic!("{:?}", t),
    }
}

#[test]
fn apply_and_with_code_wrap_the_error() {
    match apply(prim(1), callback::unify_error()) {
        T::Apply(cb, t) => match &*cb {
            callback::T::With_code(Typing::UnifyError, qfxs) => {
                assert!(qfxs.is_empty());
                assert!(is_prim_at(&t, 1));
            }
            cb => panic!("{:?}", cb),
        },
        t => panic!("{:?}", t),
    }
    assert!(matches!(
        with_code(prim(1), Typing::InvalidTypeHint),
        T::With_code(t, Typing::InvalidTypeHint) if is_prim_at(&t, 1)
    ));
    match apply_reasons(snd(4), reasons_callback::unify_error_at(pos(1))) {
        T::Apply_reasons(reasons_callback::T::Of_error(_), snd_err) => match &*snd_err {
            secondary::T::Missing_constructor(p) => assert_eq!(*p, pos(4)),
            snd_err => panic!("{:?}", snd_err),
        },
        t => panic!("{:?}", t),
    }
}

#[test]
fn count_counts_the_leaves() {
    assert_eq!(count(&prim(1)), 1);
    let t = multiple(vec![
        prim(1),
        union(vec![prim(2), with_code(prim(3), Typing::UnifyError)]),
        apply(intersect(vec![prim(4), prim(5)]), callback::unify_error()),
        apply_reasons(snd(6), reasons_callback::unify_error_at(pos(6))),
        T::With_pos(Rc::new(prim(7)), pos(8)),
    ]);
    assert_eq!(count(&t), 7);
    assert_eq!(count(&T::Multiple(vec![])), 0);
}

#[test]
fn show_is_debug() {
    let t = prim(1);
    assert_eq!(show(&t), format!("{:?}", t));
    assert!(show(&t).starts_with("Primary(Unresolved_tyvar("));
}

// -- Callback -----------------------------------------------------------------

#[test]
fn callback_using_error() {
    match callback::using_error(pos(1), true) {
        callback::T::With_claim_as_reason(
            t,
            primary::T::Using_error {
                pos: p,
                has_await: true,
            },
        ) => {
            assert_eq!(p, pos(1));
            match *t {
                callback::T::Retain_code(t) => assert!(matches!(
                    *t,
                    callback::T::With_code(Typing::UnifyError, ref qfxs) if qfxs.is_empty()
                )),
                t => panic!("{:?}", t),
            }
        }
        t => panic!("{:?}", t),
    }
}

#[test]
fn callback_with_side_effect_shares_the_effect() {
    let n = Rc::new(Cell::new(0));
    let t = {
        let n = Rc::clone(&n);
        callback::with_side_effect(callback::unify_error(), move || n.set(n.get() + 1))
    };
    let t2 = t.clone();
    for t in [&t, &t2] {
        match t {
            callback::T::With_side_effect(_, eff) => eff(),
            t => panic!("{:?}", t),
        }
    }
    assert_eq!(n.get(), 2);
    assert_eq!(
        format!("{:?}", t),
        "With_side_effect(With_code(UnifyError, []), <fun>)"
    );
}

// -- Reasons_callback ---------------------------------------------------------

#[test]
fn reasons_callback_unify_error_at() {
    match reasons_callback::unify_error_at(pos(1)) {
        reasons_callback::T::Of_error(t) => match prim_of(&t) {
            primary::T::Unify_error {
                pos: p,
                msg_opt: None,
                reasons_opt: None,
            } => assert_eq!(*p, pos(1)),
            t => panic!("{:?}", t),
        },
        t => panic!("{:?}", t),
    }
}

#[test]
fn reasons_callback_retain_and_prepend_on_apply() {
    use reasons_callback::Component;
    use reasons_callback::Op;
    use reasons_callback::T as R;

    let base = || reasons_callback::unify_error_at(pos(1));
    assert!(matches!(
        reasons_callback::retain_code(base()),
        R::Retain(t, Component::Code) if matches!(*t, R::Of_error(_))
    ));
    assert!(matches!(
        reasons_callback::retain_reasons(base()),
        R::Retain(_, Component::Reasons)
    ));
    assert!(matches!(
        reasons_callback::retain_quickfixes(base()),
        R::Retain(_, Component::Quickfixes)
    ));
    assert!(matches!(
        reasons_callback::append_incoming_reasons(base()),
        R::Incoming_reasons(_, Op::Append)
    ));
    assert!(matches!(
        reasons_callback::prepend_incoming_reasons(base()),
        R::Incoming_reasons(_, Op::Prepend)
    ));
    match reasons_callback::prepend_on_apply(base(), snd(2)) {
        R::Prepend_on_apply(t, snd_err) => assert!(
            matches!(*t, R::Of_error(_))
                && matches!(&*snd_err, secondary::T::Missing_constructor(p) if *p == pos(2))
        ),
        t => panic!("{:?}", t),
    }
    assert!(matches!(
        reasons_callback::drop_reasons_on_apply(base()),
        R::Drop_reasons_on_apply(_)
    ));
    assert!(matches!(
        reasons_callback::with_code(base(), Typing::TypeConstantMismatch),
        R::With_code(_, Typing::TypeConstantMismatch)
    ));
    assert!(matches!(reasons_callback::always(prim(1)), R::Always(t) if is_prim_at(&t, 1)));
    let reason = Lazy::from_val(Message(pos(3), "r".into()));
    assert!(matches!(
        reasons_callback::prepend_reason(base(), reason.clone()),
        R::Add_reason(_, Op::Prepend, _)
    ));
    assert!(matches!(
        reasons_callback::append_reason(base(), reason),
        R::Add_reason(_, Op::Append, _)
    ));
}

#[test]
fn reasons_callback_specific_callbacks_nest_as_in_ocaml() {
    use reasons_callback::Component;
    use reasons_callback::Op;
    use reasons_callback::T as R;

    // retain_code @@ retain_quickfixes @@ of_error @@ ...
    match reasons_callback::bad_enum_decl(pos(1)) {
        R::Retain(t, Component::Code) => match std::rc::Rc::unwrap_or_clone(t) {
            R::Retain(t, Component::Quickfixes) => match std::rc::Rc::unwrap_or_clone(t) {
                R::Of_error(t) => {
                    assert!(matches!(prim_of(&t), primary::T::Bad_enum_decl(p) if *p == pos(1)))
                }
                t => panic!("{:?}", t),
            },
            t => panic!("{:?}", t),
        },
        t => panic!("{:?}", t),
    }
    // retain_quickfixes @@ retain_code @@ of_primary_error @@ ...
    match reasons_callback::rigid_tvar_escape_at(pos(1), "x".to_string()) {
        R::Retain(t, Component::Quickfixes) => {
            assert!(matches!(*t, R::Retain(_, Component::Code)))
        }
        t => panic!("{:?}", t),
    }
    // append_incoming_reasons @@ retain_quickfixes @@ of_primary_error @@ ...
    match reasons_callback::bad_decl_override("f".to_string(), pos(2), "P".to_string()) {
        R::Incoming_reasons(t, Op::Append) => match std::rc::Rc::unwrap_or_clone(t) {
            R::Retain(t, Component::Quickfixes) => match std::rc::Rc::unwrap_or_clone(t) {
                R::Of_error(t) => match prim_of(&t) {
                    primary::T::Bad_decl_override {
                        pos: p,
                        name,
                        parent_name,
                    } => {
                        assert_eq!(*p, pos(2));
                        assert_eq!((name.as_str(), parent_name.as_str()), ("f", "P"));
                    }
                    t => panic!("{:?}", t),
                },
                t => panic!("{:?}", t),
            },
            t => panic!("{:?}", t),
        },
        t => panic!("{:?}", t),
    }
    // retain_quickfixes @@ with_code ~code t
    assert!(matches!(
        reasons_callback::type_constant_mismatch(reasons_callback::unify_error_at(pos(1))),
        R::Retain(t, Component::Quickfixes)
            if matches!(*t, R::With_code(_, Typing::TypeConstantMismatch))
    ));
    assert!(matches!(
        reasons_callback::index_type_mismatch_at(pos(1)),
        R::Of_error(t) if matches!(
            prim_of(&t),
            primary::T::Index_type_mismatch {
                is_covariant_container: false,
                msg_opt: None,
                reasons_opt: None,
                ..
            }
        )
    ));
}

#[test]
fn reasons_callback_expr_tree_splice_error() {
    use reasons_callback::Op;
    use reasons_callback::T as R;

    let docs_url_forced = Rc::new(Cell::new(false));
    let docs_url = {
        let forced = Rc::clone(&docs_url_forced);
        Lazy::new(move || {
            forced.set(true);
            None
        })
    };
    let t =
        reasons_callback::expr_tree_splice_error(pos(1), pos(2), None, Some("\\MyDsl"), docs_url);
    match t {
        R::Add_reason(t, Op::Append, reason) => {
            match std::rc::Rc::unwrap_or_clone(t) {
                R::Of_error(t) => match prim_of(&t) {
                    primary::T::Unify_error {
                        pos: p,
                        msg_opt,
                        reasons_opt: None,
                    } => {
                        assert_eq!(*p, pos(1));
                        assert_eq!(
                            msg_opt.as_deref(),
                            Some(
                                "This value cannot be inserted (spliced) into a `MyDsl` expression tree"
                            )
                        );
                    }
                    t => panic!("{:?}", t),
                },
                t => panic!("{:?}", t),
            }
            assert!(!docs_url_forced.get());
            let Message(p, msg) = reason.force();
            assert!(docs_url_forced.get());
            assert_eq!(*p, pos(2));
            assert_eq!(
                msg.to_string(),
                "Hack values need to be converted (lifted) to compatible types before splicing. \
                 For more information see: https://docs.hhvm.com/hack/expression-trees/splicing"
            );
        }
        t => panic!("{:?}", t),
    }

    let reasons = Lazy::from_val(vec![]);
    let t = reasons_callback::expr_tree_splice_error(
        pos(1),
        pos(2),
        Some(reasons),
        None,
        Lazy::from_val(Some("https://example.com".to_string())),
    );
    match t {
        R::With_reasons(t, _) => match std::rc::Rc::unwrap_or_clone(t) {
            R::Add_reason(t, Op::Append, reason) => {
                assert!(matches!(
                    std::rc::Rc::unwrap_or_clone(t),
                    R::Of_error(t) if matches!(
                        prim_of(&t),
                        primary::T::Unify_error { msg_opt: Some(msg), .. }
                            if msg == "This value cannot be inserted (spliced) into an expression tree"
                    )
                ));
                assert!(
                    reason
                        .force()
                        .1
                        .to_string()
                        .ends_with("see: https://example.com")
                );
            }
            t => panic!("{:?}", t),
        },
        t => panic!("{:?}", t),
    }
}

#[test]
fn reasons_callback_from_on_error_is_opaque() {
    let seen = Rc::new(Cell::new(None));
    let t = {
        let seen = Rc::clone(&seen);
        reasons_callback::from_on_error(move |code, quickfixes, reasons| {
            seen.set(Some((code, quickfixes.map(|q| q.len()), reasons.len())))
        })
    };
    match &t {
        reasons_callback::T::From_on_error(f) => f(Some(4110), None, vec![]),
        t => panic!("{:?}", t),
    }
    assert_eq!(seen.get(), Some((Some(4110), None, 0)));
    assert_eq!(format!("{:?}", t), "From_on_error(<opaque>)");
}

// -- Primary ------------------------------------------------------------------

#[test]
fn enum_const() {
    let label = const_::T::Label {
        class_: "C".to_string(),
        const_: "A".to_string(),
    };
    assert_eq!(const_::to_user_string(&const_::T::Null), "null");
    assert_eq!(const_::to_user_string(&label), "A");
    assert_eq!(const_::to_user_string(&const_::T::Bool(true)), "true");
    assert_eq!(const_::to_user_string(&const_::T::Bool(false)), "false");
    assert_eq!(const_::to_user_string(&const_::T::Int(None)), "int");
    assert_eq!(
        const_::to_user_string(&const_::T::Int(Some("0x1".to_string()))),
        "0x1"
    );
    assert_eq!(const_::to_user_string(&const_::T::String(None)), "string");
    assert_eq!(
        const_::to_user_string(&const_::T::String(Some("'a'".to_string()))),
        "'a'"
    );
    assert_eq!(const_::opt_to_user_string(&None), "default");
    assert_eq!(const_::opt_to_user_string(&Some(label.clone())), "A");
    assert_eq!(
        const_::if_int(&const_::T::Int(Some("12".to_string())), |n| n.len(), 0),
        2
    );
    assert_eq!(const_::if_int(&const_::T::Int(None), |n| n.len(), 0), 0);
    assert_eq!(const_::if_int(&label, |n| n.len(), 0), 0);
    // `[@@deriving ord]`: constructors in declaration order, then arguments.
    assert!(const_::T::Null < label);
    assert!(label < const_::T::Bool(false));
    assert!(const_::T::Bool(false) < const_::T::Bool(true));
    assert!(const_::T::Int(None) < const_::T::Int(Some("1".to_string())));
    assert!(const_::T::Int(Some("9".to_string())) < const_::T::String(None));
}

#[test]
fn package_target_symbol_spec_to_string() {
    use primary::package::TargetSymbolSpec;
    use primary::package::target_symbol_spec_to_string;

    assert_eq!(
        target_symbol_spec_to_string(&TargetSymbolSpec::Func),
        "function"
    );
    assert_eq!(
        target_symbol_spec_to_string(&TargetSymbolSpec::Reifiable_type_const {
            reifiable_attr_pos: pos(1),
            tconst_name: "T".to_string(),
        }),
        "reifiable type constant"
    );
    assert_eq!(
        target_symbol_spec_to_string(&TargetSymbolSpec::As_expression),
        "asserted type"
    );
    assert_eq!(
        target_symbol_spec_to_string(&TargetSymbolSpec::Type_hint),
        "type"
    );
}

#[test]
fn names_follow_the_ocaml() {
    // Fields with the same polymorphic variant have the same type, under the
    // name of each field.
    let ctxt: primary::NullMemberCtxt = primary::ArrayAccessCtxt::read;
    let _: secondary::NonObjectMemberCtxt = ctxt;
    let _: secondary::SmemberNotFoundKind = primary::SmemberNotFoundKind::static_method;
    let _: primary::shape::ShapesKeyExistsAlwaysFalseReason = NothingOrUndefined::Undefined;
    let _: primary::shape::Reason = primary::shape::NothingOrUndefined::Undefined;
    // Two tags: `<Tag1>Or<Tag2>` as well.
    let _: primary::InvalidIsAsExpressionHintOp = primary::IsOrAs::as_;
    let _: primary::NewInconsistentConstructKind = primary::StaticOrClassname::static_;
    let _: secondary::ViolatedRefinementConstraintCstr = secondary::AsOrSuper::Super;
    let _: primary::ReadOrWrite = secondary::ReadOrWrite::write;
    // Keywords: both spellings of the modules, and of `enum`.
    let _: primary::r#enum::r#const::T = const_::T::Null;
    let _: primary::case_type::T = primary::casetype::T::Invalid_recursive {
        pos: pos(1),
        name: "N".to_string(),
    };
    assert!(matches!(
        r#enum(primary::enum_::T::Enum_switch_not_const(pos(1))),
        T::Primary(prim) if matches!(&*prim, primary::T::Enum(_))
    ));
    let _: error_code::T = Typing::UnifyError;
    let _: error::T = prim(1);
}
