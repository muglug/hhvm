// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Typing_error_utils.Common`. See `mod.rs`.
//!
//! `Lazy` is re-exported here because the claims and reasons of every
//! evaluated error are lazy (`Eval_primary.t`, `Eval_error.t`, ...), so every
//! part of `typing_error_utils` needs it: it is the `'a Lazy.t` of
//! `crate::typing_error`, whose errors carry their lazy fields in it.

use oxidized::error_codes::Typing;
use oxidized::message::Message;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use relative_path::RelativePath;

use crate::naming_errors::render;
use crate::naming_errors::render::md_codify;
pub use crate::typing_error::Lazy;
use crate::typing_error::primary::InstanceOrStatic;
use crate::typing_error::primary::NonObjectMemberKind;
use crate::typing_error::primary::ReadOrWrite;
use crate::typing_error::primary::SmemberNotFoundKind;

pub fn map2<A: 'static, B: 'static, C: 'static>(
    f: impl FnOnce(&A, &B) -> C + 'static,
    x: Lazy<A>,
    y: Lazy<B>,
) -> Lazy<C> {
    Lazy::new(move || {
        let x = x.force();
        let y = y.force();
        f(x, y)
    })
}

// The contents of the following error message can trigger `hh rage` in
// sandcastle. If you change it, please make sure the existing trigger in
// `flib/intern/sandcastle/hack/SandcastleCheckHackOnDiffsStep.php` still
// catches this error message.
pub fn please_file_a_bug_message() -> String {
    let hacklang_feedback_support_link = "https://fb.workplace.com/groups/hackforhiphop/";
    let hh_rage = md_codify("hh rage");
    format!(
        "Please run {} and post in {}.",
        hh_rage, hacklang_feedback_support_link
    )
}

pub fn reasons_of_trail(trail: &[PosOrDecl]) -> Vec<Message<PosOrDecl>> {
    trail
        .iter()
        .map(|pos| Message(pos.clone(), "Typedef definition comes from here".into()))
        .collect()
}

pub fn typing_too_many_args(
    pos: Pos,
    decl_pos: PosOrDecl,
    actual: isize,
    expected: isize,
    hint_convert_to_optional: Option<PosOrDecl>,
) -> (Typing, Lazy<Message<Pos>>, Lazy<Vec<Message<PosOrDecl>>>) {
    let claim = Lazy::new(move || {
        Message(
            pos,
            format!(
                "Too many positional arguments (expected {} but got {})",
                expected, actual
            )
            .into(),
        )
    });
    let reasons = Lazy::new(move || {
        let mut reasons = vec![Message(decl_pos, "Definition is here".into())];
        if let Some(pos) = hint_convert_to_optional {
            reasons.push(Message(
                pos,
                "Try converting this argument as optional".into(),
            ))
        }
        reasons
    });
    (Typing::TypingTooManyArgs, claim, reasons)
}

pub fn typing_too_few_args(
    pos: Pos,
    decl_pos: PosOrDecl,
    actual: isize,
    expected: isize,
    hint_missing_optional: Option<PosOrDecl>,
) -> (Typing, Lazy<Message<Pos>>, Lazy<Vec<Message<PosOrDecl>>>) {
    let claim = Lazy::new(move || {
        Message(
            pos,
            format!(
                "Too few positional arguments (required {} but got {})",
                expected, actual
            )
            .into(),
        )
    });
    let reasons = Lazy::new(move || {
        let mut reasons = vec![Message(decl_pos, "Definition is here".into())];
        if let Some(pos) = hint_missing_optional {
            reasons.push(Message(pos, "Optional arguments are missing".into()))
        }
        reasons
    });
    (Typing::TypingTooFewArgs, claim, reasons)
}

pub fn missing_named_args(
    pos: Pos,
    decl_pos: PosOrDecl,
    missing_names: Vec<String>,
) -> (Typing, Lazy<Message<Pos>>, Lazy<Vec<Message<PosOrDecl>>>) {
    let names_str = missing_names.join(", ");
    let claim = Lazy::new(move || {
        Message(
            pos,
            format!(
                "Missing required named argument{}: {}",
                if missing_names.len() > 1 { "s" } else { "" },
                names_str
            )
            .into(),
        )
    });
    let reasons = Lazy::new(move || vec![Message(decl_pos, "Definition is here".into())]);
    (Typing::MissingNamedArgs, claim, reasons)
}

pub fn unexpected_named_args(
    pos: Pos,
    decl_pos: PosOrDecl,
    unexpected_names: Vec<String>,
) -> (Typing, Lazy<Message<Pos>>, Lazy<Vec<Message<PosOrDecl>>>) {
    let names_str = unexpected_names.join(", ");
    let claim = Lazy::new(move || {
        Message(
            pos,
            format!(
                "Unexpected named argument{}: {}",
                if unexpected_names.len() > 1 { "s" } else { "" },
                names_str
            )
            .into(),
        )
    });
    let reasons = Lazy::new(move || vec![Message(decl_pos, "Definition is here".into())]);
    (Typing::UnexpectedNamedArgs, claim, reasons)
}

pub fn duplicate_named_args(
    pos: Pos,
    duplicate_names: Vec<String>,
) -> (Typing, Lazy<Message<Pos>>, Lazy<Vec<Message<PosOrDecl>>>) {
    let names_str = duplicate_names.join(", ");
    let claim = Lazy::new(move || {
        Message(
            pos,
            format!(
                "Duplicate named argument{}: {}",
                if duplicate_names.len() > 1 { "s" } else { "" },
                names_str
            )
            .into(),
        )
    });
    let reasons = Lazy::new(Vec::new);
    (Typing::DuplicateNamedArgs, claim, reasons)
}

/// `Render.suggestion_message ?modifier orig hint hint_pos`.
///
/// `render::suggestion_message` has no `modifier`. Both of its messages are
/// `"Did you mean %s%s instead..."` with the modifier first, so the modifier
/// goes right after `"Did you mean "`.
fn suggestion_message(
    modifier: Option<&str>,
    orig: &str,
    hint: &str,
    hint_pos: PosOrDecl,
) -> Message<PosOrDecl> {
    const PREFIX: &str = "Did you mean ";
    let (hint_pos, s) = render::suggestion_message(orig, hint, hint_pos);
    let s = match (modifier, s.strip_prefix(PREFIX)) {
        (None, _) => s,
        (Some(modifier), Some(rest)) => format!("{}{}{}", PREFIX, modifier, rest),
        (Some(_), None) => panic!("Render.suggestion_message: unexpected message {:?}", s),
    };
    Message(hint_pos, s.into())
}

/// `Render.string_of_class_member_kind`, for the kinds of a static member.
///
/// The OCaml function takes any of six polymorphic variant tags. The two
/// callers below pass two different subsets of them, which are two enums in
/// `crate::typing_error`, so it is one function for each here; `render` has
/// neither.
fn string_of_smember_kind(kind: SmemberNotFoundKind) -> &'static str {
    match kind {
        SmemberNotFoundKind::class_constant => "class constant",
        SmemberNotFoundKind::static_method => "static method",
        SmemberNotFoundKind::class_variable => "class variable",
        SmemberNotFoundKind::class_typeconst => "type constant",
    }
}

/// `Render.string_of_class_member_kind`, for the kinds of a member accessed
/// on something that is not an object.
fn string_of_non_object_member_kind(kind: NonObjectMemberKind) -> &'static str {
    match kind {
        NonObjectMemberKind::class_typeconst => "type constant",
        NonObjectMemberKind::method_ => "method",
        NonObjectMemberKind::property => "property",
    }
}

pub fn snot_found_suggestion(
    orig: &str,
    similar: (InstanceOrStatic, PosOrDecl, String),
    kind: SmemberNotFoundKind,
) -> Message<PosOrDecl> {
    match similar {
        (InstanceOrStatic::instance, pos, v) => match kind {
            SmemberNotFoundKind::static_method => {
                suggestion_message(Some("instance method "), orig, &v, pos)
            }
            SmemberNotFoundKind::class_constant => {
                suggestion_message(Some("instance property "), orig, &v, pos)
            }
            SmemberNotFoundKind::class_variable | SmemberNotFoundKind::class_typeconst => {
                suggestion_message(None, orig, &v, pos)
            }
        },
        (InstanceOrStatic::static_, pos, v) => suggestion_message(None, orig, &v, pos),
    }
}

pub fn smember_not_found(
    pos: Pos,
    kind: SmemberNotFoundKind,
    member_name: String,
    class_name: String,
    class_pos: PosOrDecl,
    hint: Option<(InstanceOrStatic, PosOrDecl, String)>,
) -> (Typing, Lazy<Message<Pos>>, Lazy<Vec<Message<PosOrDecl>>>) {
    let claim = {
        let member_name = member_name.clone();
        let class_name = class_name.clone();
        Lazy::new(move || {
            Message(
                pos,
                format!(
                    "No {} {} in {}",
                    string_of_smember_kind(kind),
                    md_codify(&member_name),
                    md_codify(render::strip_ns(&class_name))
                )
                .into(),
            )
        })
    };
    let reasons = Lazy::new(move || {
        let default = vec![Message(
            class_pos,
            format!(
                "Declaration of {} is here",
                md_codify(render::strip_ns(&class_name))
            )
            .into(),
        )];
        match hint {
            None => default,
            Some(similar) => {
                let mut reasons = vec![snot_found_suggestion(&member_name, similar, kind)];
                reasons.extend(default);
                reasons
            }
        }
    });
    (Typing::SmemberNotFound, claim, reasons)
}

pub fn non_object_member(
    pos: Pos,
    ctxt: ReadOrWrite,
    ty_name: String,
    member_name: String,
    kind: NonObjectMemberKind,
    decl_pos: PosOrDecl,
) -> (Typing, Lazy<Message<Pos>>, Lazy<Vec<Message<PosOrDecl>>>) {
    let code = match ctxt {
        ReadOrWrite::read => Typing::NonObjectMemberRead,
        ReadOrWrite::write => Typing::NonObjectMemberWrite,
    };
    let claim = Lazy::new(move || {
        let msg_start = format!(
            "You are trying to access the {} {} but this is {}",
            string_of_non_object_member_kind(kind),
            md_codify(&member_name),
            ty_name
        );
        let msg = if ty_name == "a shape" {
            format!(
                "{}. Did you mean `$foo['{}']` instead?",
                msg_start, member_name
            )
        } else {
            msg_start
        };
        Message(pos, msg.into())
    });
    let reasons = Lazy::new(move || vec![Message(decl_pos, "Definition is here".into())]);
    (code, claim, reasons)
}

pub fn badpos_message() -> String {
    format!(
        "Incomplete position information! Your type error is in this file, but we could only find related positions in another file. {}",
        please_file_a_bug_message()
    )
}

pub fn badpos_message_2() -> String {
    format!(
        "Incomplete position information! We couldn't find the exact line of your type error in this definition. {}",
        please_file_a_bug_message()
    )
}

pub fn wrap_error_in_different_file(
    current_file: RelativePath,
    current_span: Pos,
    reasons: Vec<Message<PosOrDecl>>,
) -> (Lazy<Message<Pos>>, Vec<Message<PosOrDecl>>) {
    let claim = {
        let reasons = reasons.clone();
        Lazy::new(move || {
            let message: Vec<String> = reasons
                .iter()
                .map(|Message(pos, msg)| {
                    // `Pos_or_decl.unsafe_to_raw_pos pos`: `PosOrDecl` is `Pos`.
                    format!("{}: {}", crate::pos::print_verbose_relative(pos), msg)
                })
                .collect();
            let stack = crate::exception::clean_stack(
                &crate::exception::get_current_callstack_string(99),
            );
            crate::hh_logger::log(&format!(
                "TYPE_CHECK_PRIMARY_POSITION_BUG in {}\n{}\n{}",
                crate::relative_path::to_absolute(&current_file),
                message.join("\n"),
                stack
            ));
            crate::hack_event_logger::type_check_primary_position_bug(
                &current_file,
                &message,
                &stack,
            );
            // `Pos.equal current_span Pos.none`
            if current_span.is_none() {
                Message(crate::pos::make_from(current_file), badpos_message().into())
            } else {
                Message(current_span, badpos_message_2().into())
            }
        })
    };
    (claim, reasons)
}

/// What the tests of `typing_error_utils` share: positions like the ones in
/// the `.exp` files, and the `plain` rendering of a code, a claim and reasons.
#[cfg(test)]
pub(crate) mod testing {
    use std::path::PathBuf;
    use std::sync::Arc;

    use bstr::ByteSlice;
    use relative_path::Prefix;

    use super::*;

    /// `File "<file>", line <line>, characters <start>-<end>`
    pub(crate) fn pos(file: &str, line: usize, start: usize, end: usize) -> Pos {
        let file = Arc::new(RelativePath::make(Prefix::Root, PathBuf::from(file)));
        Pos::from_lnum_bol_offset(file, (line, 0, start - 1), (line, 0, end))
    }

    /// The error as `hh single` prints it (and as the `.exp` files have it).
    pub(crate) fn render(
        code: Typing,
        claim: &Lazy<Message<Pos>>,
        reasons: &Lazy<Vec<Message<PosOrDecl>>>,
    ) -> String {
        let Message(pos, msg) = claim.force().clone();
        let reasons = reasons
            .force()
            .iter()
            .map(|Message(pos, msg)| (pos.clone(), msg.to_str().unwrap().to_string()))
            .collect();
        crate::diagnostics::to_plain_string(&crate::diagnostics::error_with_reasons(
            code as isize,
            pos,
            msg.to_str().unwrap(),
            reasons,
        ))
    }
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;
    use std::rc::Rc;

    use super::testing::pos;
    use super::testing::render;
    use super::*;

    fn render3(
        (code, claim, reasons): (Typing, Lazy<Message<Pos>>, Lazy<Vec<Message<PosOrDecl>>>),
    ) -> String {
        render(code, &claim, &reasons)
    }

    #[test]
    fn lazy_is_forced_once_and_shared() {
        let count = Rc::new(RefCell::new(0));
        let l = {
            let count = count.clone();
            Lazy::new(move || {
                *count.borrow_mut() += 1;
                "x".to_string()
            })
        };
        let l2 = l.clone();
        let mapped = l.clone().map(|s| format!("{}y", s));
        assert_eq!(*count.borrow(), 0);
        assert_eq!(mapped.force(), "xy");
        assert_eq!(l2.force(), "x");
        assert_eq!(l.force(), "x");
        assert_eq!(*count.borrow(), 1);
        assert_eq!(Lazy::from_val(3).bind(|x| Lazy::from_val(x + 1)).force(), &4);
    }

    #[test]
    fn map2_forces_x_then_y() {
        let order = Rc::new(RefCell::new(vec![]));
        let mk = |name: &'static str| {
            let order = order.clone();
            Lazy::new(move || {
                order.borrow_mut().push(name);
                name.to_string()
            })
        };
        let l = map2(|x: &String, y: &String| format!("{}{}", x, y), mk("x"), mk("y"));
        assert!(order.borrow().is_empty());
        assert_eq!(l.force(), "xy");
        assert_eq!(*order.borrow(), vec!["x", "y"]);
    }

    #[test]
    fn messages() {
        assert_eq!(
            please_file_a_bug_message(),
            "Please run `hh rage` and post in https://fb.workplace.com/groups/hackforhiphop/."
        );
        // hphp/hack/test/typecheck/class_abstract_final_11_bad_position.php.exp
        assert_eq!(
            badpos_message_2(),
            "Incomplete position information! We couldn't find the exact line of your type error in this definition. Please run `hh rage` and post in https://fb.workplace.com/groups/hackforhiphop/."
        );
        assert_eq!(
            badpos_message(),
            "Incomplete position information! Your type error is in this file, but we could only find related positions in another file. Please run `hh rage` and post in https://fb.workplace.com/groups/hackforhiphop/."
        );
        assert_eq!(
            reasons_of_trail(&[pos("a.php", 1, 1, 2), pos("a.php", 3, 1, 2)]),
            vec![
                Message(
                    pos("a.php", 1, 1, 2),
                    "Typedef definition comes from here".into()
                ),
                Message(
                    pos("a.php", 3, 1, 2),
                    "Typedef definition comes from here".into()
                ),
            ]
        );
    }

    #[test]
    fn arity() {
        // hphp/hack/test/typecheck/class_meth5.php.exp
        assert_eq!(
            render3(typing_too_many_args(
                pos("class_meth5.php", 20, 10, 18),
                pos("class_meth5.php", 19, 8, 14),
                1,
                0,
                None
            )),
            "ERROR: File \"class_meth5.php\", line 20, characters 10-18:\n\
             Too many positional arguments (expected 0 but got 1) (Typing[4105])\n  \
             File \"class_meth5.php\", line 19, characters 8-14:\n  \
             Definition is here\n"
        );
        let (_, _, reasons) = typing_too_many_args(
            pos("a.php", 2, 1, 2),
            pos("a.php", 1, 1, 2),
            2,
            1,
            Some(pos("a.php", 1, 5, 6)),
        );
        assert_eq!(
            reasons.force()[1],
            Message(
                pos("a.php", 1, 5, 6),
                "Try converting this argument as optional".into()
            )
        );
        // hphp/hack/test/typecheck/named_parameters/named_params_errors.php.exp
        assert_eq!(
            render3(typing_too_few_args(
                pos("named_params_errors.php", 13, 3, 26),
                pos("named_params_errors.php", 3, 10, 19),
                0,
                1,
                None
            )),
            "ERROR: File \"named_params_errors.php\", line 13, characters 3-26:\n\
             Too few positional arguments (required 1 but got 0) (Typing[4104])\n  \
             File \"named_params_errors.php\", line 3, characters 10-19:\n  \
             Definition is here\n"
        );
        let (_, _, reasons) = typing_too_few_args(
            pos("a.php", 2, 1, 2),
            pos("a.php", 1, 1, 2),
            0,
            1,
            Some(pos("a.php", 1, 5, 6)),
        );
        assert_eq!(
            reasons.force()[1],
            Message(
                pos("a.php", 1, 5, 6),
                "Optional arguments are missing".into()
            )
        );
        assert_eq!(
            render3(missing_named_args(
                pos("named_params_errors.php", 16, 3, 32),
                pos("named_params_errors.php", 3, 10, 19),
                vec!["label".to_string()]
            )),
            "ERROR: File \"named_params_errors.php\", line 16, characters 3-32:\n\
             Missing required named argument: label (Typing[4499])\n  \
             File \"named_params_errors.php\", line 3, characters 10-19:\n  \
             Definition is here\n"
        );
        assert_eq!(
            missing_named_args(
                pos("a.php", 2, 1, 2),
                pos("a.php", 1, 1, 2),
                vec!["a".to_string(), "b".to_string()]
            )
            .1
            .force()
            .1,
            "Missing required named arguments: a, b"
        );
        // hphp/hack/test/typecheck/named_parameters/named_params_arity_too_many.php.exp
        assert_eq!(
            render3(unexpected_named_args(
                pos("named_params_arity_too_many.php", 10, 3, 46),
                pos("named_params_arity_too_many.php", 4, 10, 14),
                vec!["extra1".to_string(), "extra2".to_string()]
            )),
            "ERROR: File \"named_params_arity_too_many.php\", line 10, characters 3-46:\n\
             Unexpected named arguments: extra1, extra2 (Typing[4500])\n  \
             File \"named_params_arity_too_many.php\", line 4, characters 10-14:\n  \
             Definition is here\n"
        );
        assert_eq!(
            render3(unexpected_named_args(
                pos("named_params_arity_too_many.php", 8, 3, 19),
                pos("named_params_arity_too_many.php", 3, 10, 11),
                vec!["extra1".to_string()]
            )),
            "ERROR: File \"named_params_arity_too_many.php\", line 8, characters 3-19:\n\
             Unexpected named argument: extra1 (Typing[4500])\n  \
             File \"named_params_arity_too_many.php\", line 3, characters 10-11:\n  \
             Definition is here\n"
        );
        // hphp/hack/test/typecheck/named_parameters/named_params_duplicate_args.php.exp
        assert_eq!(
            render3(duplicate_named_args(
                pos("named_params_duplicate_args.php", 18, 3, 49),
                vec!["c".to_string(), "b".to_string()]
            )),
            "ERROR: File \"named_params_duplicate_args.php\", line 18, characters 3-49:\n\
             Duplicate named arguments: c, b (Typing[4501])\n"
        );
        assert_eq!(
            render3(duplicate_named_args(
                pos("named_params_duplicate_args.php", 12, 3, 36),
                vec!["b".to_string()]
            )),
            "ERROR: File \"named_params_duplicate_args.php\", line 12, characters 3-36:\n\
             Duplicate named argument: b (Typing[4501])\n"
        );
    }

    #[test]
    fn smember_not_found_with_instance_hint() {
        // hphp/hack/test/typecheck/method_dispatch_13.php.exp
        assert_eq!(
            render3(smember_not_found(
                pos("method_dispatch_13.php", 26, 11, 12),
                SmemberNotFoundKind::static_method,
                "f1".to_string(),
                "\\B".to_string(),
                pos("method_dispatch_13.php", 21, 7, 7),
                Some((
                    InstanceOrStatic::instance,
                    pos("method_dispatch_13.php", 22, 19, 20),
                    "f1".to_string()
                )),
            )),
            "ERROR: File \"method_dispatch_13.php\", line 26, characters 11-12:\n\
             No static method `f1` in `B` (Typing[4090])\n  \
             File \"method_dispatch_13.php\", line 22, characters 19-20:\n  \
             Did you mean instance method `f1` instead?\n  \
             File \"method_dispatch_13.php\", line 21, characters 7-7:\n  \
             Declaration of `B` is here\n"
        );
        // hphp/hack/test/typecheck/instance_property_as_class_constant.php.exp
        assert_eq!(
            render3(smember_not_found(
                pos("instance_property_as_class_constant.php", 17, 17, 19),
                SmemberNotFoundKind::class_constant,
                "foo".to_string(),
                "\\X".to_string(),
                pos("instance_property_as_class_constant.php", 12, 7, 7),
                Some((
                    InstanceOrStatic::instance,
                    pos("instance_property_as_class_constant.php", 13, 12, 18),
                    "foo".to_string()
                )),
            )),
            "ERROR: File \"instance_property_as_class_constant.php\", line 17, characters 17-19:\n\
             No class constant `foo` in `X` (Typing[4090])\n  \
             File \"instance_property_as_class_constant.php\", line 13, characters 12-18:\n  \
             Did you mean instance property `foo` instead?\n  \
             File \"instance_property_as_class_constant.php\", line 12, characters 7-7:\n  \
             Declaration of `X` is here\n"
        );
    }

    #[test]
    fn snot_found_suggestions() {
        let p = || pos("a.php", 1, 1, 2);
        let text = |similar, kind| {
            let Message(_, msg) = snot_found_suggestion("Foo", similar, kind);
            msg.to_string()
        };
        // Only the case differs: the differences are highlighted, after the
        // modifier.
        assert_eq!(
            text(
                (InstanceOrStatic::instance, p(), "foo".to_string()),
                SmemberNotFoundKind::static_method
            ),
            "Did you mean instance method `~~f~~oo` instead (which only differs by case)?"
        );
        assert_eq!(
            text(
                (InstanceOrStatic::instance, p(), "bar".to_string()),
                SmemberNotFoundKind::class_variable
            ),
            "Did you mean `bar` instead?"
        );
        assert_eq!(
            text(
                (InstanceOrStatic::instance, p(), "bar".to_string()),
                SmemberNotFoundKind::class_typeconst
            ),
            "Did you mean `bar` instead?"
        );
        assert_eq!(
            text(
                (InstanceOrStatic::static_, p(), "bar".to_string()),
                SmemberNotFoundKind::static_method
            ),
            "Did you mean `bar` instead?"
        );
        // Without a hint only the declaration is given.
        let (_, _, reasons) = smember_not_found(
            p(),
            SmemberNotFoundKind::class_typeconst,
            "T".to_string(),
            "\\HH\\Vector".to_string(),
            p(),
            None,
        );
        assert_eq!(
            *reasons.force(),
            vec![Message(p(), "Declaration of `Vector` is here".into())]
        );
    }

    #[test]
    fn non_object_member_of_a_shape() {
        // hphp/hack/test/typecheck/anonymous_shape4.php.exp (there the error
        // is a secondary one, so the claim is the first reason)
        let (code, claim, reasons) = non_object_member(
            pos("anonymous_shape4.php", 4, 7, 7),
            ReadOrWrite::read,
            "a shape".to_string(),
            "x".to_string(),
            NonObjectMemberKind::property,
            pos("anonymous_shape4.php", 3, 15, 31),
        );
        assert_eq!(code, Typing::NonObjectMemberRead);
        assert_eq!(code as isize, 4062);
        assert_eq!(
            claim.force().1,
            "You are trying to access the property `x` but this is a shape. Did you mean `$foo['x']` instead?"
        );
        assert_eq!(
            *reasons.force(),
            vec![Message(
                pos("anonymous_shape4.php", 3, 15, 31),
                "Definition is here".into()
            )]
        );
        let (code, claim, _) = non_object_member(
            pos("a.php", 4, 7, 7),
            ReadOrWrite::write,
            "an int".to_string(),
            "f".to_string(),
            NonObjectMemberKind::method_,
            pos("a.php", 3, 15, 31),
        );
        assert_eq!(code, Typing::NonObjectMemberWrite);
        assert_eq!(
            claim.force().1,
            "You are trying to access the method `f` but this is an int"
        );
    }

    #[test]
    fn wrap_error_in_different_file_with_a_span() {
        // hphp/hack/test/typecheck/class_abstract_final_11_bad_position.php.exp
        let file = "class_abstract_final_11_bad_position.php";
        let reasons = vec![
            Message(pos(file, 3, 22, 23), "`C2` is uninstantiable".into()),
            Message(pos(file, 3, 22, 23), "Declaration is here".into()),
        ];
        let (claim, reasons) = wrap_error_in_different_file(
            pos(file, 1, 1, 1).filename().clone(),
            pos(file, 4, 3, 67),
            reasons,
        );
        assert_eq!(
            render(Typing::UninstantiableClass, &claim, &Lazy::from_val(reasons)),
            "ERROR: File \"class_abstract_final_11_bad_position.php\", line 4, characters 3-67:\n\
             Incomplete position information! We couldn't find the exact line of your type error in this definition. Please run `hh rage` and post in https://fb.workplace.com/groups/hackforhiphop/. (Typing[4002])\n  \
             File \"class_abstract_final_11_bad_position.php\", line 3, characters 22-23:\n  \
             `C2` is uninstantiable\n  \
             File \"class_abstract_final_11_bad_position.php\", line 3, characters 22-23:\n  \
             Declaration is here\n"
        );
        // Without a span the claim is at the file, with the other message.
        let (claim, _) = wrap_error_in_different_file(
            pos(file, 1, 1, 1).filename().clone(),
            Pos::NONE,
            vec![],
        );
        let Message(claim_pos, msg) = claim.force();
        assert_eq!(claim_pos.filename().path_str(), file);
        assert_eq!(*msg, badpos_message());
    }
}
