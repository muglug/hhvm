// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of `Typing_error_utils.Eval_primary`. See `mod.rs`.
//!
//! The first half of the functions of `Eval_primary` (`typing_error_utils.ml`
//! from `unify_error` up to, not including, `immutable_local`), in the order
//! of the OCaml file.
//!
//! Notes on the transliteration:
//!
//! - `lazy e` is `Lazy::new(move || e)`: what OCaml computes when the claim or
//!   the reasons are forced is computed when they are forced here, and what it
//!   computes when the function is called (`Render.strip_ns` on some names,
//!   `Lazy.force ty_name` in `non_object_member`, the quickfixes) is computed
//!   when the function is called.
//! - A parameter that a `lazy` captures, or that ends up in the result, is
//!   taken by value; one that is only read when the function is called is
//!   taken by reference.
//! - `Pos_or_decl.t` and `Pos.t` are the same Rust type, so
//!   `Pos_or_decl.of_raw_pos` and `Message.map ~f:Pos_or_decl.of_raw_pos`
//!   disappear, and `Pos_or_decl.equal` is `==`.
//! - `Printf.sprintf` and chains of `^` are `format!` with the same pieces.

use bstr::ByteSlice;
use naming_special_names_rust as sn;
use oxidized::ast_defs::ClassishKind;
use oxidized::error_codes::Typing as ErrorCode;
use oxidized::message::Message;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use oxidized::quickfix::Edits;
use oxidized::quickfix::Quickfix;
use oxidized::s_set::SSet;

use super::super::common;
use super::T;
use super::create;
use crate::naming_errors::render;
use crate::naming_errors::render::highlight_differences;
use crate::naming_errors::render::md_codify;
use crate::naming_errors::render::strip_ns;
use crate::naming_errors::render::utils_strip_ns;
use crate::typing_error::Lazy;
use crate::typing_error::primary::CallNeedsConcreteVia;
use crate::typing_error::primary::ClassMemberKind;
use crate::typing_error::primary::CoOrContra;
use crate::typing_error::primary::ConstantOrParam;
use crate::typing_error::primary::ImplementsInfo;
use crate::typing_error::primary::InstanceOrStatic;
use crate::typing_error::primary::IsOrAs;
use crate::typing_error::primary::MethOrProp;
use crate::typing_error::primary::MethodOrProperty;
use crate::typing_error::primary::NonObjectMemberKind;
use crate::typing_error::primary::ReadOrWrite;
use crate::typing_error::primary::ReifiableAttrKind;

/// `Pos_or_decl.t Message.t list Lazy.t`
type Reasons = Lazy<Vec<Message<PosOrDecl>>>;

/// `String.capitalize`
fn string_capitalize(s: &str) -> String {
    let mut s = s.to_string();
    if let Some(first) = s.get_mut(0..1) {
        first.make_ascii_uppercase();
    }
    s
}

/// `Render.suggestion_message ?modifier orig hint hint_pos`.
///
/// `render::suggestion_message` has no `modifier`. Both of its messages are
/// `"Did you mean %s%s instead..."` with the modifier first, so the modifier
/// goes right after `"Did you mean "`. (`Common` has the same function, which
/// is private there.)
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

pub fn unify_error(pos: Pos, msg_opt: Option<String>, reasons_opt: Option<Reasons>) -> T {
    let claim = Lazy::new(move || {
        Message(
            pos,
            msg_opt.unwrap_or_else(|| "Typing error".to_string()).into(),
        )
    });
    create(ErrorCode::UnifyError, claim, reasons_opt, None)
}

pub fn generic_unify(pos: Pos, msg: String) -> T {
    let claim = Lazy::new(move || Message(pos, msg.into()));
    create(ErrorCode::GenericUnify, claim, None, None)
}

pub fn unresolved_tyvar(pos: Pos) -> T {
    let claim = Lazy::new(move || {
        Message(
            pos,
            "The type of this expression contains an unresolved type variable".into(),
        )
    });
    create(ErrorCode::UnresolvedTypeVariable, claim, None, None)
}

pub fn using_error(pos: Pos, has_await: bool) -> T {
    let claim = Lazy::new(move || {
        let (note, cls) = if has_await {
            (" with await", sn::classes::IASYNC_DISPOSABLE)
        } else {
            ("", sn::classes::IDISPOSABLE)
        };
        Message(
            pos,
            format!(
                "This expression is used in a `using` clause{} so it must have type `{}`",
                note, cls
            )
            .into(),
        )
    });
    create(ErrorCode::UnifyError, claim, None, None)
}

pub fn bad_enum_decl(pos: Pos) -> T {
    let claim = Lazy::new(move || Message(pos, "This enum declaration is invalid.".into()));
    create(ErrorCode::BadEnumExtends, claim, None, None)
}

pub fn bad_conditional_support_dynamic(
    pos: Pos,
    child: String,
    parent: String,
    ty_name: Lazy<String>,
    self_ty_name: Lazy<String>,
) -> T {
    let claim = Lazy::new(move || {
        let ty_name = ty_name.force();
        let self_ty_name = self_ty_name.force();
        let statement = format!(
            "{} is subtype of dynamic implies {} is subtype of dynamic",
            ty_name, self_ty_name
        );
        Message(
            pos,
            format!(
                "Class {} must support dynamic at least as often as {}:\n{}",
                strip_ns(&child),
                strip_ns(&parent),
                statement
            )
            .into(),
        )
    });
    create(ErrorCode::BadConditionalSupportDynamic, claim, None, None)
}

pub fn bad_decl_override(name: &str, parent_pos: Pos, parent_name: &str) -> T {
    let name = md_codify(strip_ns(name));
    let parent_name = md_codify(strip_ns(parent_name));
    let claim = Lazy::new(move || {
        Message(
            parent_pos,
            format!(
                "Some members in class {} are incompatible with those declared in type {}",
                name, parent_name
            )
            .into(),
        )
    });
    create(ErrorCode::BadDeclOverride, claim, None, None)
}

pub fn explain_where_constraint(pos: Pos, decl_pos: PosOrDecl, in_class: bool) -> T {
    let claim =
        Lazy::new(move || Message(pos, "A `where` type constraint is violated here".into()));
    let reasons = Lazy::new(move || {
        vec![Message(
            decl_pos,
            format!(
                "This is the {} with `where` type constraints",
                if in_class { "class" } else { "method" }
            )
            .into(),
        )]
    });
    create(
        ErrorCode::TypeConstraintViolation,
        claim,
        Some(reasons),
        None,
    )
}

pub fn explain_constraint(pos: Pos) -> T {
    let claim =
        Lazy::new(move || Message(pos, "Some type arguments violate their constraints".into()));
    create(ErrorCode::TypeConstraintViolation, claim, None, None)
}

pub fn rigid_tvar_escape(pos: Pos, what: String) -> T {
    let claim = Lazy::new(move || {
        Message(
            pos,
            format!("Rigid type variable escapes its {}", what).into(),
        )
    });
    create(ErrorCode::RigidTVarEscape, claim, None, None)
}

pub fn invalid_type_hint(pos: Pos) -> T {
    let claim = Lazy::new(move || Message(pos, "Invalid type hint".into()));
    create(ErrorCode::InvalidTypeHint, claim, None, None)
}

pub fn unsatisfied_req(pos: Pos, trait_pos: PosOrDecl, req_name: String, req_pos: PosOrDecl) -> T {
    let reasons = Lazy::new(move || {
        let r = Message(
            trait_pos.clone(),
            format!(
                "This requires to extend or implement {}",
                strip_ns(&req_name)
            )
            .into(),
        );
        if trait_pos == req_pos {
            vec![r]
        } else {
            vec![r, Message(req_pos, "Required here".into())]
        }
    });
    let claim = Lazy::new(move || {
        Message(
            pos,
            "This class does not satisfy all the requirements of its traits or interfaces.".into(),
        )
    });
    create(ErrorCode::UnsatisfiedReq, claim, Some(reasons), None)
}

pub fn unsatisfied_req_class(
    pos: Pos,
    trait_pos: PosOrDecl,
    req_name: String,
    req_pos: PosOrDecl,
) -> T {
    let reasons = Lazy::new(move || {
        let r = Message(
            trait_pos.clone(),
            format!("This requires to be exactly {}", strip_ns(&req_name)).into(),
        );
        if trait_pos == req_pos {
            vec![r]
        } else {
            vec![r, Message(req_pos, "Required here".into())]
        }
    });
    let claim = Lazy::new(move || {
        Message(
            pos,
            "This class does not satisfy all the requirements of its traits or interfaces.".into(),
        )
    });
    create(ErrorCode::UnsatisfiedReq, claim, Some(reasons), None)
}

pub fn unsatisfied_req_this_as(
    pos: Pos,
    trait_pos: PosOrDecl,
    req_name: String,
    req_pos: PosOrDecl,
) -> T {
    let reasons = Lazy::new(move || {
        let r = Message(
            trait_pos.clone(),
            format!("This requires to be a subtype of {}", strip_ns(&req_name)).into(),
        );
        if trait_pos == req_pos {
            vec![r]
        } else {
            vec![r, Message(req_pos, "Required here".into())]
        }
    });
    let claim = Lazy::new(move || {
        Message(
            pos,
            "This class does not satisfy all the requirements of its traits or interfaces.".into(),
        )
    });
    create(ErrorCode::UnsatisfiedReq, claim, Some(reasons), None)
}

pub fn req_class_not_final(pos: Pos, trait_pos: PosOrDecl, req_pos: PosOrDecl) -> T {
    let reasons = Lazy::new(move || {
        let r = Message(
            trait_pos.clone(),
            "The trait with a require class constraint is used here".into(),
        );
        if trait_pos == req_pos {
            vec![r]
        } else {
            vec![
                r,
                Message(req_pos, "The require class constraint is here".into()),
            ]
        }
    });
    let claim = Lazy::new(move || {
        Message(
            pos,
            "This class must be final because it uses a trait with a require class constraint."
                .into(),
        )
    });
    create(ErrorCode::UnsatisfiedReq, claim, Some(reasons), None)
}

pub fn incompatible_reqs(
    pos: Pos,
    req_name: String,
    req_class_pos: PosOrDecl,
    req_extends_pos: PosOrDecl,
) -> T {
    let reasons = Lazy::new(move || {
        let r1 = Message(
            req_class_pos,
            format!("This requires exactly class {}", strip_ns(&req_name)).into(),
        );
        let r2 = Message(
            req_extends_pos,
            format!("This requires a subtype of class {}", strip_ns(&req_name)).into(),
        );
        vec![r1, r2]
    });
    let claim =
        Lazy::new(move || Message(pos, "This trait defines incompatible requirements.".into()));
    create(ErrorCode::UnsatisfiedReq, claim, Some(reasons), None)
}

pub fn trait_not_used(
    pos: Pos,
    trait_name: String,
    req_class_pos: PosOrDecl,
    class_pos: PosOrDecl,
    class_name: &str,
) -> T {
    let class_name = strip_ns(class_name).to_string();
    let reasons = {
        let class_name = class_name.clone();
        Lazy::new(move || {
            vec![
                Message(
                    class_pos,
                    format!("Class {} is defined here.", class_name).into(),
                ),
                Message(
                    req_class_pos,
                    "The require class requirement is here.".into(),
                ),
            ]
        })
    };
    let claim = Lazy::new(move || {
        Message(
            pos,
            format!(
                "Trait {} requires class {} but {} does not use it. Either use the trait or delete it.",
                strip_ns(&trait_name),
                strip_ns(&class_name),
                strip_ns(&class_name)
            )
            .into(),
        )
    });
    create(ErrorCode::TraitNotUsed, claim, Some(reasons), None)
}

pub fn invalid_echo_argument(pos: Pos) -> T {
    let claim = Lazy::new(move || {
        Message(
            pos,
            format!(
                "Invalid {}/{} argument",
                md_codify("echo"),
                md_codify("print")
            )
            .into(),
        )
    });
    create(ErrorCode::InvalidEchoArgument, claim, None, None)
}

pub fn index_type_mismatch(
    pos: Pos,
    is_covariant_container: bool,
    msg_opt: Option<String>,
    reasons_opt: Option<Reasons>,
) -> T {
    let code = if is_covariant_container {
        ErrorCode::CovariantIndexTypeMismatch
    } else {
        ErrorCode::IndexTypeMismatch
    };
    let claim = Lazy::new(move || {
        Message(
            pos,
            msg_opt
                .unwrap_or_else(|| "Invalid index expression".to_string())
                .into(),
        )
    });
    let reasons = reasons_opt.unwrap_or_else(|| Lazy::new(Vec::new));
    create(code, claim, Some(reasons), None)
}

pub fn member_not_found(
    pos: Pos,
    kind: MethodOrProperty,
    member_name: String,
    class_name: String,
    class_pos: PosOrDecl,
    hint: Option<(InstanceOrStatic, PosOrDecl, String)>,
    reason: Reasons,
) -> T {
    let kind_str = match kind {
        MethodOrProperty::method_ => "instance method",
        MethodOrProperty::property => "property",
    };
    let claim = {
        let pos = pos.clone();
        let member_name = member_name.clone();
        let class_name = class_name.clone();
        Lazy::new(move || {
            Message(
                pos,
                format!(
                    "No {} {} in {}",
                    kind_str,
                    md_codify(&member_name),
                    md_codify(strip_ns(&class_name))
                )
                .into(),
            )
        })
    };
    let default = reason.map(move |reason| {
        let mut reasons = reason.clone();
        reasons.push(Message(
            class_pos,
            format!(
                "Declaration of {} is here",
                md_codify(strip_ns(&class_name))
            )
            .into(),
        ));
        reasons
    });
    let reasons = match hint.clone() {
        None => default,
        Some((InstanceOrStatic::instance, pos, v)) => default.map(move |default| {
            let mut reasons = vec![suggestion_message(None, &member_name, &v, pos)];
            reasons.extend(default.iter().cloned());
            reasons
        }),
        Some((InstanceOrStatic::static_, pos, v)) => {
            let modifier = match kind {
                MethodOrProperty::method_ => "static method ",
                MethodOrProperty::property => "static property ",
            };
            default.map(move |default| {
                let mut reasons = vec![suggestion_message(Some(modifier), &member_name, &v, pos)];
                reasons.extend(default.iter().cloned());
                reasons
            })
        }
    };
    let quickfixes = match hint {
        None => vec![],
        Some((_, _, new_text)) => vec![crate::quickfix::make_eager_default_hint_style(
            format!("Change to ->{}", new_text),
            new_text,
            pos,
        )],
    };
    create(
        ErrorCode::MemberNotFound,
        claim,
        Some(reasons),
        Some(quickfixes),
    )
}

pub fn construct_not_instance_method(pos: Pos) -> T {
    let claim = Lazy::new(move || {
        Message(
            pos,
            "`__construct` is not an instance method and shouldn't be invoked directly".into(),
        )
    });
    create(ErrorCode::ConstructNotInstanceMethod, claim, None, None)
}

pub fn ambiguous_inheritance(pos: Pos, origin: String, class_name: String) -> T {
    let claim = Lazy::new(move || {
        Message(
            pos,
            format!(
                "This declaration was inherited from an object of type {}. Redeclare this member in {} with a compatible signature.",
                md_codify(&origin),
                md_codify(&class_name)
            )
            .into(),
        )
    });
    create(ErrorCode::UnifyError, claim, None, None)
}

pub fn expected_tparam(pos: Pos, n: isize, decl_pos: PosOrDecl) -> T {
    let claim = Lazy::new(move || {
        Message(
            pos,
            format!(
                "Expected {}",
                match n {
                    0 => "no type parameters".to_string(),
                    1 => "exactly one type parameter".to_string(),
                    n => format!("{} type parameters", n),
                }
            )
            .into(),
        )
    });
    let reasons = Lazy::new(move || vec![Message(decl_pos, "Definition is here".into())]);
    create(ErrorCode::ExpectedTparam, claim, Some(reasons), None)
}

pub fn typeconst_concrete_concrete_override(pos: Pos, decl_pos: PosOrDecl) -> T {
    let reasons = Lazy::new(move || vec![Message(decl_pos, "Previously defined here".into())]);
    let claim = Lazy::new(move || Message(pos, "Cannot re-declare this type constant".into()));
    create(
        ErrorCode::TypeconstConcreteConcreteOverride,
        claim,
        Some(reasons),
        None,
    )
}

pub fn constant_multiple_concrete_conflict(
    pos: Pos,
    name: String,
    definitions: Vec<(PosOrDecl, Option<String>)>,
) -> T {
    let reasons = Lazy::new(move || {
        definitions
            .into_iter()
            .enumerate()
            .map(|(i, (p, via))| {
                let first = if i == 0 { "One" } else { "Another" };
                let message = format!("{} conflicting definition is here", first);
                let full_message = match via {
                    Some(parent_name) => {
                        format!("{}, inherited through {}", message, parent_name)
                    }
                    None => message,
                };
                Message(p, full_message.into())
            })
            .collect()
    });

    let claim = Lazy::new(move || {
        Message(
            pos,
            format!(
                "Constant {} is defined concretely in multiple ancestors",
                name
            )
            .into(),
        )
    });
    create(
        ErrorCode::ConcreteConstInterfaceOverride,
        claim,
        Some(reasons),
        None,
    )
}

pub fn invalid_memoized_param(pos: Pos, reasons: Reasons) -> T {
    let claim = Lazy::new(move || {
        Message(
            pos,
            "Parameters to memoized function must be null, bool, int, float, string, an object deriving IMemoizeParam, or a Container thereof. See also http://docs.hhvm.com/hack/attributes/special#__memoize".into(),
        )
    });
    create(ErrorCode::InvalidMemoizedParam, claim, Some(reasons), None)
}

pub fn invalid_arraykey(
    pos: Pos,
    container_pos: PosOrDecl,
    container_ty_name: String,
    key_pos: PosOrDecl,
    key_ty_name: String,
    ctxt: ReadOrWrite,
) -> T {
    let reasons = Lazy::new(move || {
        vec![
            Message(
                container_pos,
                format!("This container is {}", container_ty_name).into(),
            ),
            Message(
                key_pos,
                format!(
                    "{} cannot be used as a key for {}",
                    string_capitalize(&key_ty_name),
                    container_ty_name
                )
                .into(),
            ),
        ]
    });
    let claim = Lazy::new(move || {
        Message(
            pos,
            "This value is not a valid key type for this container".into(),
        )
    });
    let code = match ctxt {
        ReadOrWrite::read => ErrorCode::IndexTypeMismatch,
        ReadOrWrite::write => ErrorCode::InvalidArrayKeyWrite,
    };
    create(code, claim, Some(reasons), None)
}

pub fn invalid_keyset_value(
    pos: Pos,
    container_pos: PosOrDecl,
    container_ty_name: String,
    value_pos: PosOrDecl,
    value_ty_name: String,
) -> T {
    let reasons = Lazy::new(move || {
        vec![
            Message(
                container_pos,
                format!("This container is {}", container_ty_name).into(),
            ),
            Message(
                value_pos,
                format!("{} is not an arraykey", string_capitalize(&value_ty_name)).into(),
            ),
        ]
    });
    let claim = Lazy::new(move || Message(pos, "Keyset values must be arraykeys".into()));
    create(ErrorCode::IndexTypeMismatch, claim, Some(reasons), None)
}

pub fn invalid_set_value(
    pos: Pos,
    container_pos: PosOrDecl,
    container_ty_name: String,
    value_pos: PosOrDecl,
    value_ty_name: String,
) -> T {
    let reasons = Lazy::new(move || {
        vec![
            Message(
                container_pos,
                format!("This container is {}", container_ty_name).into(),
            ),
            Message(
                value_pos,
                format!("{} is not an arraykey", string_capitalize(&value_ty_name)).into(),
            ),
        ]
    });
    let claim = Lazy::new(move || Message(pos, "Set values must be arraykeys".into()));
    create(ErrorCode::IndexTypeMismatch, claim, Some(reasons), None)
}

pub fn invalid_substring(pos: Pos, ty_name: Lazy<String>) -> T {
    let claim = Lazy::new(move || {
        Message(
            pos,
            format!(
                "Expected an object convertible to string but got {}",
                ty_name.force()
            )
            .into(),
        )
    });
    create(ErrorCode::InvalidSubString, claim, None, None)
}

pub fn nullable_cast(pos: Pos, ty_pos: PosOrDecl, ty_name: Lazy<String>) -> T {
    let reasons = ty_name.map(move |ty_name| {
        vec![Message(
            ty_pos,
            format!("This is {}", md_codify(ty_name)).into(),
        )]
    });
    let claim = Lazy::new(move || Message(pos, "Casting from a nullable type is forbidden".into()));
    create(ErrorCode::NullableCast, claim, Some(reasons), None)
}

pub fn hh_expect(pos: Pos, equivalent: bool) -> T {
    let (claim, code) = if equivalent {
        (
            Lazy::new(move || Message(pos, "hh_expect_equivalent type mismatch".into())),
            ErrorCode::HHExpectEquivalentFailure,
        )
    } else {
        (
            Lazy::new(move || Message(pos, "hh_expect type mismatch".into())),
            ErrorCode::HHExpectFailure,
        )
    };
    create(code, claim, None, None)
}

pub fn null_member(
    pos: Pos,
    obj_pos_opt: Option<&Pos>,
    ctxt: ReadOrWrite,
    kind: MethodOrProperty,
    member_name: String,
    reasons: Reasons,
) -> T {
    let claim = {
        let pos = pos.clone();
        Lazy::new(move || {
            Message(
                pos,
                format!(
                    "You are trying to access the {} {} but this object can be null.",
                    match kind {
                        MethodOrProperty::method_ => "method",
                        MethodOrProperty::property => "property",
                    },
                    md_codify(&member_name)
                )
                .into(),
            )
        })
    };
    let code = match ctxt {
        ReadOrWrite::read => ErrorCode::NullMemberRead,
        ReadOrWrite::write => ErrorCode::NullMemberWrite,
    };
    let quickfixes = match obj_pos_opt {
        Some(obj_pos) => {
            let (obj_pos_start_line, _) = crate::pos::line_column(obj_pos);
            let (rhs_pos_start_line, rhs_pos_start_column) = crate::pos::line_column(&pos);
            // heuristic: if the lhs and rhs of the Objget are on the same line, then we assume they are
            // separated by two characters (`->`). So we do not generate a quickfix for chained Objgets:
            // ```
            // obj
            // ->rhs
            // ```
            if obj_pos_start_line == rhs_pos_start_line {
                let width = 2; // length of "->"
                let quickfix_pos = crate::pos::set_col_end(
                    rhs_pos_start_column,
                    &crate::pos::set_col_start(rhs_pos_start_column - width, &pos),
                );
                vec![crate::quickfix::make_eager_default_hint_style(
                    "Add null-safe get".to_string(),
                    "?->".to_string(),
                    quickfix_pos,
                )]
            } else {
                vec![]
            }
        }
        None => vec![],
    };
    create(code, claim, Some(reasons), Some(quickfixes))
}

pub fn typing_too_many_args(
    pos: Pos,
    decl_pos: PosOrDecl,
    actual: isize,
    expected: isize,
    hint_convert_to_optional: Option<PosOrDecl>,
) -> T {
    let (code, claim, reasons) =
        common::typing_too_many_args(pos, decl_pos, actual, expected, hint_convert_to_optional);
    create(code, claim, Some(reasons), None)
}

pub fn typing_too_few_args(
    pos: Pos,
    decl_pos: PosOrDecl,
    actual: isize,
    expected: isize,
    hint_missing_optional: Option<PosOrDecl>,
) -> T {
    let (code, claim, reasons) =
        common::typing_too_few_args(pos, decl_pos, actual, expected, hint_missing_optional);
    create(code, claim, Some(reasons), None)
}

pub fn missing_named_args(pos: Pos, decl_pos: PosOrDecl, missing_names: Vec<String>) -> T {
    let (code, claim, reasons) = common::missing_named_args(pos, decl_pos, missing_names);
    create(code, claim, Some(reasons), None)
}

pub fn unexpected_named_args(pos: Pos, decl_pos: PosOrDecl, unexpected_names: Vec<String>) -> T {
    let (code, claim, reasons) = common::unexpected_named_args(pos, decl_pos, unexpected_names);
    create(code, claim, Some(reasons), None)
}

pub fn duplicate_named_args(pos: Pos, duplicate_names: Vec<String>) -> T {
    let (code, claim, reasons) = common::duplicate_named_args(pos, duplicate_names);
    create(code, claim, Some(reasons), None)
}

pub fn non_object_member(
    pos: Pos,
    ctxt: ReadOrWrite,
    ty_name: &Lazy<String>,
    member_name: String,
    kind: NonObjectMemberKind,
    decl_pos: PosOrDecl,
) -> T {
    let (code, claim, reasons) = common::non_object_member(
        pos,
        ctxt,
        ty_name.force().clone(),
        member_name,
        kind,
        decl_pos,
    );
    create(code, claim, Some(reasons), None)
}

pub fn static_instance_intersection(
    class_pos: Pos,
    instance_pos: Lazy<PosOrDecl>,
    static_pos: Lazy<PosOrDecl>,
    member_name: String,
    kind: MethOrProp,
) -> T {
    let claim = Lazy::new(move || {
        Message(
            class_pos,
            "This class overrides some members with a different staticness".into(),
        )
    });
    let reasons = Lazy::new(move || {
        // OCaml builds a list literal from its last element to its first: it
        // forces `static_pos` before `instance_pos`.
        let static_reason = Message(
            static_pos.force().clone(),
            "But it conflicts with an inherited static declaration here".into(),
        );
        let instance_reason = Message(
            instance_pos.force().clone(),
            format!(
                "The {} {} is declared as non-static here",
                match kind {
                    MethOrProp::meth => "method",
                    MethOrProp::prop => "property",
                },
                md_codify(&member_name)
            )
            .into(),
        );
        vec![instance_reason, static_reason]
    });
    create(ErrorCode::StaticDynamic, claim, Some(reasons), None)
}

pub fn nullsafe_property_write_context(pos: Pos) -> T {
    let claim = Lazy::new(move || {
        Message(
            pos,
            "`?->` syntax not supported here, this function effectively does a write".into(),
        )
    });
    create(ErrorCode::NullsafePropertyWriteContext, claim, None, None)
}

pub fn uninstantiable_class(
    pos: Pos,
    class_name: String,
    reason_ty_opt: Option<(Pos, Lazy<String>)>,
    decl_pos: PosOrDecl,
) -> T {
    let default_claim = Lazy::new(move || {
        Message(
            pos,
            format!("{} is uninstantiable", md_codify(strip_ns(&class_name))).into(),
        )
    });
    let default_reasons = Lazy::new(move || vec![Message(decl_pos, "Declaration is here".into())]);
    let (claim, reasons) = match reason_ty_opt {
        Some((reason_pos, ty_name)) => {
            let claim = ty_name.map(move |ty_name| {
                Message(
                    reason_pos,
                    format!("This would be {} which must be instantiable", ty_name).into(),
                )
            });
            let reasons = Lazy::new(move || {
                let claim = default_claim.force();
                let reasons = default_reasons.force();
                // `Message.map ~f:Pos_or_decl.of_raw_pos claim :: reasons`
                let mut all = vec![claim.clone()];
                all.extend(reasons.iter().cloned());
                all
            });
            (claim, reasons)
        }
        None => (default_claim, default_reasons),
    };
    create(ErrorCode::UninstantiableClass, claim, Some(reasons), None)
}

pub fn abstract_const_usage(pos: Pos, name: String, decl_pos: PosOrDecl) -> T {
    let claim = Lazy::new(move || {
        Message(
            pos,
            format!(
                "Cannot reference abstract constant {} directly",
                md_codify(strip_ns(&name))
            )
            .into(),
        )
    });
    let reasons = Lazy::new(move || vec![Message(decl_pos, "Declaration is here".into())]);
    create(ErrorCode::AbstractConstUsage, claim, Some(reasons), None)
}

pub fn type_arity_mismatch(pos: Pos, decl_pos: PosOrDecl, actual: isize, expected: isize) -> T {
    let claim = Lazy::new(move || {
        Message(
            pos,
            format!(
                "Wrong number of type arguments (expected {}, got {})",
                expected, actual
            )
            .into(),
        )
    });
    let reasons = Lazy::new(move || vec![Message(decl_pos, "Definition is here".into())]);
    create(ErrorCode::TypeArityMismatch, claim, Some(reasons), None)
}

pub fn member_not_implemented(
    parent_pos: Pos,
    member_name: String,
    decl_pos: PosOrDecl,
    quickfixes: Vec<Quickfix<Pos>>,
) -> T {
    let claim = Lazy::new(move || {
        Message(
            parent_pos,
            "This interface is not properly implemented".into(),
        )
    });
    let reasons = Lazy::new(move || {
        vec![Message(
            decl_pos,
            format!(
                "Method {} does not have an implementation",
                md_codify(&member_name)
            )
            .into(),
        )]
    });
    create(
        ErrorCode::MemberNotImplemented,
        claim,
        Some(reasons),
        Some(quickfixes),
    )
}

pub fn kind_mismatch(
    pos: Pos,
    decl_pos: PosOrDecl,
    tparam_name: String,
    expected_kind: String,
    actual_kind: String,
) -> T {
    let claim = {
        let expected_kind = expected_kind.clone();
        Lazy::new(move || {
            Message(
                pos,
                format!(
                    "This is {}, but {} was expected here.",
                    actual_kind, expected_kind
                )
                .into(),
            )
        })
    };
    let reasons = Lazy::new(move || {
        vec![Message(
            decl_pos,
            format!(
                "We are expecting {} due to the definition of {} here.",
                expected_kind, tparam_name
            )
            .into(),
        )]
    });
    create(ErrorCode::KindMismatch, claim, Some(reasons), None)
}

pub fn trait_parent_construct_inconsistent(pos: Pos, decl_pos: PosOrDecl) -> T {
    let claim = Lazy::new(move || {
        Message(
            pos,
            "This use of `parent::__construct` requires that the parent class be marked <<__ConsistentConstruct>>".into(),
        )
    });
    let reasons = Lazy::new(move || vec![Message(decl_pos, "Parent definition is here".into())]);
    create(
        ErrorCode::TraitParentConstructInconsistent,
        claim,
        Some(reasons),
        None,
    )
}

pub fn top_member(
    pos: Pos,
    ctxt: ReadOrWrite,
    ty_name: Lazy<String>,
    decl_pos: PosOrDecl,
    kind: MethodOrProperty,
    name: String,
    is_nullable: bool,
    ty_reasons: Lazy<Vec<(PosOrDecl, String)>>,
) -> T {
    let claim = ty_name.map(move |ty_name| {
        let kind_str = match kind {
            MethodOrProperty::method_ => "method",
            MethodOrProperty::property => "property",
        };
        Message(
            pos,
            format!(
                "You are trying to access the {} {} but this is {}. Use a **specific** class or interface name.",
                kind_str,
                md_codify(&name),
                ty_name
            )
            .into(),
        )
    });
    let reasons = Lazy::new(move || {
        let reasons = ty_reasons.force();
        if reasons.is_empty() {
            vec![Message(decl_pos, "Definition is here".into())]
        } else {
            reasons
                .iter()
                .map(|(pos, msg)| Message(pos.clone(), msg.clone().into()))
                .collect()
        }
    });
    let code = match ctxt {
        ReadOrWrite::read if is_nullable => ErrorCode::NullMemberRead,
        ReadOrWrite::write if is_nullable => ErrorCode::NullMemberWrite,
        ReadOrWrite::read => ErrorCode::NonObjectMemberRead,
        ReadOrWrite::write => ErrorCode::NonObjectMemberWrite,
    };
    create(code, claim, Some(reasons), None)
}

pub fn unresolved_tyvar_projection(pos: Pos, proj_pos: PosOrDecl, tconst_name: String) -> T {
    let claim = {
        let pos = pos.clone();
        Lazy::new(move || {
            Message(
                pos,
                format!(
                    "Can't access a type constant {} from an unresolved type",
                    tconst_name
                )
                .into(),
            )
        })
    };
    let reasons = Lazy::new(move || {
        vec![
            Message(proj_pos, "Access happens here".into()),
            Message(
                pos,
                "Disambiguate the types using explicit type annotations here.".into(),
            ),
        ]
    });
    create(
        ErrorCode::UnresolvedTypeVariableProjection,
        claim,
        Some(reasons),
        None,
    )
}

pub fn cyclic_class_constant(pos: Pos, class_name: String, const_name: String) -> T {
    let claim = Lazy::new(move || {
        Message(
            pos,
            format!(
                "Cannot declare self-referencing constant {} in {}",
                const_name,
                strip_ns(&class_name)
            )
            .into(),
        )
    });
    create(ErrorCode::CyclicClassConstant, claim, None, None)
}

pub fn inout_annotation_missing(pos1: Pos, pos2: PosOrDecl) -> T {
    let pos = crate::pos::shrink_to_start(&pos1);
    let claim = Lazy::new(move || {
        Message(
            pos1,
            "This argument should be annotated with `inout`".into(),
        )
    });
    let reasons =
        Lazy::new(move || vec![Message(pos2, "Because this is an `inout` parameter".into())]);
    let quickfixes = vec![crate::quickfix::make_eager_default_hint_style(
        "Insert `inout` annotation".to_string(),
        "inout ".to_string(),
        pos,
    )];
    create(
        ErrorCode::InoutAnnotationMissing,
        claim,
        Some(reasons),
        Some(quickfixes),
    )
}

pub fn inout_annotation_unexpected(
    pos1: Pos,
    pos2: PosOrDecl,
    pos2_is_variadic: bool,
    pos3: Pos,
) -> T {
    let claim =
        Lazy::new(move || Message(pos1, "Unexpected `inout` annotation for argument".into()));
    let reasons = Lazy::new(move || {
        vec![Message(
            pos2,
            if pos2_is_variadic {
                "A variadic parameter can never be `inout`"
            } else {
                "This is a normal parameter (does not have `inout`)"
            }
            .into(),
        )]
    });
    let quickfixes = vec![crate::quickfix::make_eager_default_hint_style(
        "Remove `inout` annotation".to_string(),
        "".to_string(),
        pos3,
    )];
    create(
        ErrorCode::InoutAnnotationUnexpected,
        claim,
        Some(reasons),
        Some(quickfixes),
    )
}

pub fn inout_argument_bad_type(pos: Pos, reasons: Reasons) -> T {
    let claim = Lazy::new(move || {
        Message(
            pos,
            "Expected argument marked `inout` to be contained in a local or a value-typed container (e.g. vec, dict, keyset, array). To use `inout` here, assign to/from a temporary local variable.".into(),
        )
    });
    create(ErrorCode::InoutArgumentBadType, claim, Some(reasons), None)
}

pub fn invalid_meth_caller_inout_parameter(pos: Pos, decl_pos: PosOrDecl) -> T {
    let claim = Lazy::new(move || {
        Message(
            pos,
            "`meth_caller` does not support methods with the `inout` calling convention".into(),
        )
    });
    let reasons = Lazy::new(move || {
        vec![Message(
            decl_pos,
            "This is why I think this method uses the `inout` calling convention".into(),
        )]
    });
    create(
        ErrorCode::InvalidMethCallerCallingConvention,
        claim,
        Some(reasons),
        None,
    )
}

pub fn invalid_meth_caller_named_parameter(pos: Pos, decl_pos: PosOrDecl) -> T {
    let claim = Lazy::new(move || {
        Message(
            pos,
            "`meth_caller` does not support methods with named parameters".into(),
        )
    });
    let reasons = Lazy::new(move || vec![Message(decl_pos, "This parameter is named".into())]);
    create(
        ErrorCode::InvalidMethCallerNamedParameter,
        claim,
        Some(reasons),
        None,
    )
}

pub fn invalid_meth_caller_readonly_return(pos: Pos, decl_pos: PosOrDecl) -> T {
    let claim = Lazy::new(move || {
        Message(
            pos,
            "`meth_caller` does not support methods that return `readonly` objects".into(),
        )
    });
    let reasons = Lazy::new(move || {
        vec![Message(
            decl_pos,
            "This is why I think this method returns a `readonly` object".into(),
        )]
    });
    create(
        ErrorCode::InvalidMethCallerReadonlyReturn,
        claim,
        Some(reasons),
        None,
    )
}

pub fn this_as_function_pointer_param(pos: Pos, decl_pos: PosOrDecl) -> T {
    let claim = Lazy::new(move || {
        Message(
            pos,
            "Cannot take a pointer to this method because a value of type `this` can be obtained from two or more of its parameters (counting the implicit receiver of an instance method), so the function pointer could be used to relate two unrelated subtypes of `this`".into(),
        )
    });
    let reasons = Lazy::new(move || {
        vec![Message(
            decl_pos,
            "a value of type `this` can be obtained from this parameter".into(),
        )]
    });
    create(
        ErrorCode::ThisAsFunctionPointerParam,
        claim,
        Some(reasons),
        None,
    )
}

pub fn invalid_new_disposable(pos: Pos) -> T {
    let claim = Lazy::new(move || {
        Message(
            pos,
            "Disposable objects may only be created in a `using` statement or `return` from function marked `<<__ReturnDisposable>>`".into(),
        )
    });
    create(ErrorCode::InvalidNewDisposable, claim, None, None)
}

pub fn invalid_return_disposable(pos: Pos) -> T {
    let claim = Lazy::new(move || {
        Message(
            pos,
            "Return expression must be new disposable in function marked `<<__ReturnDisposable>>`"
                .into(),
        )
    });
    create(ErrorCode::InvalidReturnDisposable, claim, None, None)
}

pub fn invalid_disposable_hint(pos: Pos, class_name: String) -> T {
    let claim = Lazy::new(move || {
        Message(
            pos,
            format!(
                "Parameter with type {} must not implement `IDisposable` or `IAsyncDisposable`. Please use `<<__AcceptDisposable>>` attribute or create disposable object with `using` statement instead.",
                md_codify(&class_name)
            )
            .into(),
        )
    });
    create(ErrorCode::InvalidDisposableHint, claim, None, None)
}

pub fn invalid_disposable_return_hint(pos: Pos, class_name: String) -> T {
    let claim = Lazy::new(move || {
        Message(
            pos,
            format!(
                "Return type {} must not implement `IDisposable` or `IAsyncDisposable`. Please add `<<__ReturnDisposable>>` attribute.",
                md_codify(&class_name)
            )
            .into(),
        )
    });
    create(ErrorCode::InvalidDisposableReturnHint, claim, None, None)
}

pub fn ambiguous_lambda(pos: Pos, uses: Reasons) -> T {
    let claim = {
        let pos = pos.clone();
        Lazy::new(move || {
            Message(
                pos,
                "Lambda has parameter types that could not be determined at definition site."
                    .into(),
            )
        })
    };
    let reasons = uses.map(move |uses| {
        let mut reasons = vec![Message(
            pos,
            format!(
                "{} distinct use types were determined: please add type hints to lambda parameters.",
                uses.len()
            )
            .into(),
        )];
        reasons.extend(uses.iter().map(|Message(pos, ty)| {
            Message(
                pos.clone(),
                format!("This use has type {}", md_codify(&ty.to_str_lossy())).into(),
            )
        }));
        reasons
    });
    create(ErrorCode::AmbiguousLambda, claim, Some(reasons), None)
}

pub fn smember_not_found(
    pos: Pos,
    kind: ClassMemberKind,
    member_name: String,
    class_name: String,
    class_pos: PosOrDecl,
    hint: Option<(InstanceOrStatic, PosOrDecl, String)>,
    quickfixes: Vec<Quickfix<Pos>>,
) -> T {
    let (code, claim, reasons) =
        common::smember_not_found(pos, kind, member_name, class_name, class_pos, hint);
    create(code, claim, Some(reasons), Some(quickfixes))
}

pub fn wrong_extend_kind(
    pos: Pos,
    kind: ClassishKind,
    name: String,
    parent_pos: PosOrDecl,
    parent_kind: ClassishKind,
    parent_name: String,
) -> T {
    let reasons = Lazy::new(move || {
        let parent_kind_str = crate::ast_defs::string_of_classish_kind(parent_kind);
        vec![Message(
            parent_pos,
            format!("This is {}.", parent_kind_str).into(),
        )]
    });
    let claim = Lazy::new(move || {
        let parent_name = strip_ns(&parent_name);
        let child_name = strip_ns(&name);
        let use_msg = format!(
            " Did you mean to add `use {};` within the body of {}?",
            parent_name,
            md_codify(child_name)
        );
        let child_msg = match kind {
            ClassishKind::Cclass(_) => {
                let extends_msg = "Classes can only extend other classes.";
                let suggestion = if crate::ast_defs::is_c_interface(parent_kind) {
                    format!(" Did you mean `implements {}`?", parent_name)
                } else if crate::ast_defs::is_c_trait(parent_kind) {
                    use_msg
                } else {
                    "".to_string()
                };
                format!("{}{}", extends_msg, suggestion)
            }
            ClassishKind::Cinterface => {
                let extends_msg = "Interfaces can only extend other interfaces.";
                let suggestion = if crate::ast_defs::is_c_trait(parent_kind) {
                    use_msg
                } else {
                    "".to_string()
                };
                format!("{}{}", extends_msg, suggestion)
            }
            ClassishKind::CenumClass(_) => {
                "Enum classes can only extend other enum classes.".to_string()
            }
            ClassishKind::Cenum => {
                // This case should never happen, as the type checker will have already caught
                // it with EnumTypeBad. But just in case, report this error here too.
                "Enums can only extend int, string, or arraykey.".to_string()
            }
            ClassishKind::Ctrait => {
                // This case should never happen, as the parser will have caught it before
                // we get here.
                "A trait cannot use `extends`. This is a parser error.".to_string()
            }
        };
        Message(pos, child_msg.into())
    });
    create(ErrorCode::WrongExtendKind, claim, Some(reasons), None)
}

pub fn wrong_use_kind(pos: Pos, name: &str, parent_pos: PosOrDecl, parent_name: &str) -> T {
    let parent_name = strip_ns(parent_name).to_string();
    let child_name = strip_ns(name).to_string();
    let reasons = Lazy::new(move || {
        vec![Message(
            parent_pos,
            format!("Trait {} is internal.", parent_name).into(),
        )]
    });
    let claim = Lazy::new(move || {
        Message(
            pos,
            format!(
                "Module level trait {} cannot use internal traits.",
                child_name
            )
            .into(),
        )
    });
    create(ErrorCode::WrongUseKind, claim, Some(reasons), None)
}

pub fn cyclic_class_def(pos: Pos, stack: SSet) -> T {
    let claim = Lazy::new(move || {
        // `S_set.fold f stack ""`: the elements in increasing order, each one
        // put in front of what has been accumulated.
        let stack = stack.iter().fold("".to_string(), |y, x| {
            format!("{} {}", md_codify(strip_ns(x)), y)
        });

        Message(pos, format!("Cyclic class definition : {}", stack).into())
    });
    create(ErrorCode::CyclicClassDef, claim, None, None)
}

pub fn trait_reuse_with_final_method(
    use_pos: Pos,
    trait_name: String,
    parent_cls_name: String,
    reasons: Reasons,
) -> T {
    let claim = Lazy::new(move || {
        Message(
            use_pos,
            format!(
                "Traits with final methods cannot be reused, and `{}` is already used by `{}`.",
                strip_ns(&trait_name),
                strip_ns(&parent_cls_name)
            )
            .into(),
        )
    });
    create(ErrorCode::TraitReuse, claim, Some(reasons), None)
}

pub fn trait_reuse_inside_class(
    c_pos: Pos,
    c_name: String,
    trait_: String,
    occurrences: Vec<PosOrDecl>,
) -> T {
    let claim = Lazy::new(move || {
        let c_name = md_codify(strip_ns(&c_name));
        let trait_ = md_codify(strip_ns(&trait_));
        let err = format!("Class {} uses trait {} multiple times", c_name, trait_);
        Message(c_pos, err.into())
    });
    let reasons = Lazy::new(move || {
        occurrences
            .into_iter()
            .map(|p| Message(p, "used here".into()))
            .collect()
    });
    create(ErrorCode::TraitReuseInsideClass, claim, Some(reasons), None)
}

pub fn invalid_is_as_expression_hint(hint_pos: Pos, op: IsOrAs, reasons: Reasons) -> T {
    let op = match op {
        IsOrAs::is => "is",
        IsOrAs::as_ => "as",
    };
    let claim = Lazy::new(move || {
        Message(
            hint_pos,
            format!("Invalid {} expression hint", md_codify(op)).into(),
        )
    });
    let reasons = reasons.map(move |reasons| {
        reasons
            .iter()
            .map(|Message(ty_pos, ty_str)| {
                Message(
                    ty_pos.clone(),
                    format!(
                        "The {} operator cannot be used with {}",
                        md_codify(op),
                        ty_str.to_str_lossy()
                    )
                    .into(),
                )
            })
            .collect()
    });
    create(
        ErrorCode::InvalidIsAsExpressionHint,
        claim,
        Some(reasons),
        None,
    )
}

pub fn invalid_enforceable_type(
    targ_pos: Pos,
    ty_info: Reasons,
    kind: ConstantOrParam,
    tp_pos: PosOrDecl,
    tp_name: String,
) -> T {
    let claim = Lazy::new(move || Message(targ_pos, "Invalid type".into()));
    let reasons = ty_info.map(move |ty_info| {
        let kind_str = match kind {
            ConstantOrParam::constant => "constant",
            ConstantOrParam::param => "parameter",
        };
        let Message(ty_pos, ty_str) = ty_info.first().expect("List.hd_exn");
        vec![
            Message(
                tp_pos,
                format!(
                    "Type {} {} was declared `__Enforceable` here",
                    kind_str,
                    md_codify(&tp_name)
                )
                .into(),
            ),
            Message(
                ty_pos.clone(),
                format!(
                    "This type is not enforceable because it has {}",
                    ty_str.to_str_lossy()
                )
                .into(),
            ),
        ]
    });
    create(
        ErrorCode::InvalidEnforceableTypeArgument,
        claim,
        Some(reasons),
        None,
    )
}

pub fn reifiable_attr(
    attr_pos: PosOrDecl,
    kind: ReifiableAttrKind,
    decl_pos: Pos,
    ty_info: Reasons,
) -> T {
    let claim = Lazy::new(move || {
        let decl_kind = match kind {
            ReifiableAttrKind::ty => "type",
            ReifiableAttrKind::cnstr => "constraint",
            ReifiableAttrKind::super_cnstr => "super_constraint",
        };
        Message(decl_pos, format!("Invalid {}", decl_kind).into())
    });
    let reasons = ty_info.map(move |ty_info| {
        let Message(ty_pos, ty_msg) = ty_info.first().expect("List.hd_exn");
        vec![
            Message(
                attr_pos,
                "This type constant has the `__Reifiable` attribute".into(),
            ),
            Message(
                ty_pos.clone(),
                format!("It cannot contain {}", ty_msg.to_str_lossy()).into(),
            ),
        ]
    });
    create(ErrorCode::DisallowPHPArraysAttr, claim, Some(reasons), None)
}

pub fn invalid_newable_type_argument(pos: Pos, tp_pos: PosOrDecl, tp_name: String) -> T {
    let claim = Lazy::new(move || {
        Message(
            pos,
            "A newable type argument must be a concrete class or a newable type parameter.".into(),
        )
    });
    let reasons = Lazy::new(move || {
        vec![Message(
            tp_pos,
            format!(
                "Type parameter {} was declared `__Newable` here",
                md_codify(&tp_name)
            )
            .into(),
        )]
    });
    create(
        ErrorCode::InvalidNewableTypeArgument,
        claim,
        Some(reasons),
        None,
    )
}

pub fn invalid_newable_type_param_constraints(
    (tparam_pos, tparam_name): (Pos, String),
    constraint_list: Vec<String>,
) -> T {
    let claim = Lazy::new(move || {
        let partial = if constraint_list.is_empty() {
            "No constraints".to_string()
        } else {
            format!(
                "The constraints {}",
                constraint_list
                    .iter()
                    .map(|c| strip_ns(c))
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        };
        let msg = format!(
            "The type parameter {} has the `<<__Newable>>` attribute. Newable type parameters must be constrained with `as`, and exactly one of those constraints must be a valid newable class. The class must either be final, or it must have the `<<__ConsistentConstruct>>` attribute or extend a class that has it. {} are valid newable classes",
            md_codify(&tparam_name),
            partial
        );
        Message(tparam_pos, msg.into())
    });
    create(
        ErrorCode::InvalidNewableTypeParamConstraints,
        claim,
        None,
        None,
    )
}

pub fn override_per_trait(
    class_name: (Pos, String),
    meth_name: String,
    trait_name: String,
    m_pos: PosOrDecl,
) -> T {
    let claim = {
        let meth_name = meth_name.clone();
        Lazy::new(move || {
            let (c_pos, c_name) = class_name;
            let err_msg = format!(
                "`{}::{}` is marked `__Override` but `{}` does not define or inherit a `{}` method.",
                strip_ns(&trait_name),
                meth_name,
                strip_ns(&c_name),
                meth_name
            );
            Message(c_pos, err_msg.into())
        })
    };
    let reasons = Lazy::new(move || {
        vec![Message(
            m_pos,
            format!("Declaration of {} is here", md_codify(&meth_name)).into(),
        )]
    });
    create(ErrorCode::OverridePerTrait, claim, Some(reasons), None)
}

pub fn should_not_be_override(pos: Pos, class_id: String, id: String) -> T {
    let claim = Lazy::new(move || {
        Message(
            pos,
            format!(
                "{} has no parent class with a method {} to override",
                md_codify(strip_ns(&class_id)),
                md_codify(&id)
            )
            .into(),
        )
    });
    create(ErrorCode::ShouldNotBeOverride, claim, None, None)
}

pub fn needs_concrete_in_final_class(pos: Pos, class_name: String, meth_name: String) -> T {
    let claim = Lazy::new(move || {
        Message(
            pos,
            format!(
                "The {} attribute is not allowed on {} because {} is a final class. The {} attribute is for safe inheritance so should only be used in non-final classes.",
                md_codify(sn::user_attributes::NEEDS_CONCRETE),
                md_codify(&format!("{}::{}", strip_ns(&class_name), meth_name)),
                md_codify(strip_ns(&class_name)),
                md_codify(sn::user_attributes::NEEDS_CONCRETE)
            )
            .into(),
        )
    });
    create(ErrorCode::NeedsConcreteInFinalClass, claim, None, None)
}

pub fn needs_concrete_on_instance_method(pos: Pos, class_name: String, meth_name: String) -> T {
    let claim = Lazy::new(move || {
        Message(
            pos,
            format!(
                "The {} attribute is not allowed on {} (a nonstatic method). The {} attribute is only meaningful on static methods.",
                md_codify(sn::user_attributes::NEEDS_CONCRETE),
                md_codify(&format!("{}::{}", strip_ns(&class_name), meth_name)),
                md_codify(sn::user_attributes::NEEDS_CONCRETE)
            )
            .into(),
        )
    });
    create(ErrorCode::NeedsConcreteOnInstanceMethod, claim, None, None)
}

pub fn needs_concrete_on_constructor(pos: Pos, _class_name: &str) -> T {
    let claim = Lazy::new(move || {
        Message(
            pos,
            format!(
                "The {} attribute is not allowed on a constructor. The {} attribute is only meaningful on static methods.",
                md_codify(sn::user_attributes::NEEDS_CONCRETE),
                md_codify(sn::user_attributes::NEEDS_CONCRETE)
            )
            .into(),
        )
    });
    create(ErrorCode::NeedsConcreteOnConstructor, claim, None, None)
}

pub fn call_needs_concrete(
    pos: Pos,
    class_name: &str,
    meth_name: &str,
    decl_pos: PosOrDecl,
    via: CallNeedsConcreteVia,
) -> T {
    let class_name = strip_ns(class_name).to_string();
    let member = md_codify(&format!("{}::{}", class_name, meth_name));
    let claim = Lazy::new(move || {
        Message(
            pos,
            match via {
                CallNeedsConcreteVia::Id => format!(
                    "Dangerous call to {} (a `<<__NeedsConcrete>>` method). It is expecting a concrete receiver but {} is not concrete.",
                    member,
                    md_codify(&class_name)
                ),
                CallNeedsConcreteVia::Static => format!(
                    "Dangerous call to {} (a `<<__NeedsConcrete>>` method) via `static`. It requires `static` to refer to a concrete class but `static` may not be concrete.",
                    member
                ),
                CallNeedsConcreteVia::Self_ | CallNeedsConcreteVia::Parent => {
                    let via = match via {
                        CallNeedsConcreteVia::Self_ => "`self`",
                        CallNeedsConcreteVia::Parent => "`parent`",
                        CallNeedsConcreteVia::Id | CallNeedsConcreteVia::Static => unreachable!(),
                    };
                    format!(
                        "Dangerous call to {} (a `<<__NeedsConcrete>>` method) via {}. It requires `static` to refer to a concrete class, but {} sets `static` to a class that may not be concrete.",
                        member, via, via
                    )
                }
            }
            .into(),
        )
    });
    let reasons = Lazy::new(move || vec![Message(decl_pos, "Declaration is here".into())]);
    create(ErrorCode::CallNeedsConcrete, claim, Some(reasons), None)
}

pub fn abstract_access_via_static(
    pos: Pos,
    class_name: String,
    member_name: String,
    decl_pos: PosOrDecl,
    containing_method_pos: Option<Pos>,
) -> T {
    let claim = Lazy::new(move || {
        Message(
            pos,
            format!(
                "Dangerous access of abstract member {}; it may be abstract and `static` might refer to an abstract class here. Consider adding the `__NeedsConcrete` attribute to the containing method.",
                md_codify(&format!("{}::{}", strip_ns(&class_name), member_name))
            )
            .into(),
        )
    });
    let reasons = Lazy::new(move || vec![Message(decl_pos, "Declaration is here".into())]);
    let quickfixes = match containing_method_pos {
        Some(function_pos) => vec![crate::quickfix::make(
            format!("Add {} attribute", sn::user_attributes::NEEDS_CONCRETE),
            Edits::AddFunctionAttribute {
                function_pos,
                attribute_name: sn::user_attributes::NEEDS_CONCRETE.to_string(),
            },
            vec![],
        )],
        None => vec![],
    };
    create(
        ErrorCode::AbstractAccessViaStatic,
        claim,
        Some(reasons),
        Some(quickfixes),
    )
}

pub fn uninstantiable_class_via_static(
    pos: Pos,
    _class_name: &str,
    decl_pos: PosOrDecl,
    containing_method_pos: Option<Pos>,
) -> T {
    let claim = Lazy::new(move || {
        Message(
            pos,
            "Dangerous instantiation via `static`: `static` might refer to a non-concrete class here. Consider adding the `__NeedsConcrete` attribute to the containing method.".into(),
        )
    });
    let reasons = Lazy::new(move || vec![Message(decl_pos, "Declaration is here".into())]);
    let quickfixes = match containing_method_pos {
        Some(function_pos) => vec![crate::quickfix::make(
            format!("Add {} attribute", sn::user_attributes::NEEDS_CONCRETE),
            Edits::AddFunctionAttribute {
                function_pos,
                attribute_name: sn::user_attributes::NEEDS_CONCRETE.to_string(),
            },
            vec![],
        )],
        None => vec![],
    };
    create(
        ErrorCode::UninstantiableClassViaStatic,
        claim,
        Some(reasons),
        Some(quickfixes),
    )
}

pub fn needs_concrete_override(
    pos: Pos,
    method_pos: PosOrDecl,
    parent_pos: PosOrDecl,
    method_name_for_method_defined_outside_class: Option<&str>,
) -> T {
    let method_text = match method_name_for_method_defined_outside_class {
        Some(method_name) => format!("Method `{}`", method_name),
        None => "This method".to_string(),
    };
    let claim = Lazy::new(move || {
        Message(
            pos,
            format!(
                "{} is declared as `__NeedsConcrete` but overrides a non-`__NeedsConcrete` method. Please add `__NeedsConcrete` to the overridden method or remove it from the current method. (The `__NeedsConcrete` attribute indicates that a method requires `static` to point to a concrete class)",
                method_text
            )
            .into(),
        )
    });
    let reasons = Lazy::new(move || {
        vec![
            Message(
                method_pos,
                "It is unsafe to declare this method as `__NeedsConcrete`, since it overrides a non-`__NeedsConcrete` method".into(),
            ),
            Message(parent_pos, "Previously defined here".into()),
        ]
    });
    create(ErrorCode::NeedsConcreteOverride, claim, Some(reasons), None)
}

pub fn typedef_trail_entry<P>(pos: P) -> Message<P> {
    Message(pos, "Typedef definition comes from here".into())
}

pub fn trivial_strict_eq(
    p: Pos,
    b: bool,
    left: Reasons,
    right: Reasons,
    left_trail: Vec<PosOrDecl>,
    right_trail: Vec<PosOrDecl>,
) -> T {
    let claim = Lazy::new(move || {
        let b = md_codify(if b { "true" } else { "false" });
        let msg = format!("This expression is always {}", b);
        Message(p, msg.into())
    });
    let reasons = Lazy::new(move || {
        let left = left.force();
        let right = right.force();
        let left_trail = left_trail.into_iter().map(typedef_trail_entry);
        let right_trail = right_trail.into_iter().map(typedef_trail_entry);
        left.iter()
            .cloned()
            .chain(left_trail)
            .chain(right.iter().cloned())
            .chain(right_trail)
            .collect()
    });
    create(ErrorCode::TrivialStrictEq, claim, Some(reasons), None)
}

pub fn trivial_strict_not_nullable_compare_null(p: Pos, result: bool, reasons: Reasons) -> T {
    let claim = Lazy::new(move || {
        let b = md_codify(if result { "true" } else { "false" });
        let msg = format!("This expression is always {}", b);
        Message(p, msg.into())
    });
    create(
        ErrorCode::NotNullableCompareNullTrivial,
        claim,
        Some(reasons),
        None,
    )
}

pub fn eq_incompatible_types(
    p: Pos,
    left: Vec<Message<PosOrDecl>>,
    right: Vec<Message<PosOrDecl>>,
) -> T {
    let claim = Lazy::new(move || Message(p, "This equality test has incompatible types".into()));
    let reasons = Lazy::new(move || left.into_iter().chain(right).collect());
    create(ErrorCode::EqIncompatibleTypes, claim, Some(reasons), None)
}

pub fn comparison_invalid_types(
    p: Pos,
    left: Vec<Message<PosOrDecl>>,
    right: Vec<Message<PosOrDecl>>,
) -> T {
    let claim = Lazy::new(move || {
        Message(
            p,
            "This comparison has invalid types.  Only comparisons in which both arguments are strings, nums, DateTime, or DateTimeImmutable are allowed".into(),
        )
    });
    let reasons = Lazy::new(move || left.into_iter().chain(right).collect());
    create(
        ErrorCode::ComparisonInvalidTypes,
        claim,
        Some(reasons),
        None,
    )
}

pub fn strict_eq_value_incompatible_types(
    p: Pos,
    left: Vec<Message<PosOrDecl>>,
    right: Vec<Message<PosOrDecl>>,
) -> T {
    let claim = Lazy::new(move || {
        Message(
            p,
            "The arguments to this value equality test are not the same types or are not the allowed types (int, bool, float, string, vec, keyset, dict). The behavior for this test is changing and will soon either be universally false or throw an exception.".into(),
        )
    });
    let reasons = Lazy::new(move || left.into_iter().chain(right).collect());
    create(
        ErrorCode::StrictEqValueIncompatibleTypes,
        claim,
        Some(reasons),
        None,
    )
}

/// `deprecated_use pos ?(pos_def = None) msg`: the optional argument is itself
/// an option.
pub fn deprecated_use(pos: Pos, pos_def: Option<Option<PosOrDecl>>, msg: String) -> T {
    let pos_def = pos_def.unwrap_or(None);
    let claim = Lazy::new(move || Message(pos, msg.into()));
    let reasons = Lazy::new(move || match pos_def {
        Some(pos_def) => vec![Message(pos_def, "Definition is here".into())],
        None => vec![],
    });
    create(ErrorCode::DeprecatedUse, claim, Some(reasons), None)
}

pub fn cannot_declare_constant(pos: Pos, (class_pos, class_name): (Pos, String)) -> T {
    let claim = Lazy::new(move || Message(pos, "Cannot declare a constant in an enum".into()));
    let reasons = Lazy::new(move || {
        vec![Message(
            class_pos,
            format!(
                "{} was defined as an enum here",
                md_codify(strip_ns(&class_name))
            )
            .into(),
        )]
    });
    create(ErrorCode::CannotDeclareConstant, claim, Some(reasons), None)
}

pub fn redeclaring_promoted_property(
    pos: Pos,
    prop_name: String,
    parent_pos: PosOrDecl,
    parent_name: String,
) -> T {
    let claim = {
        let prop_name = prop_name.clone();
        Lazy::new(move || {
            Message(
                pos,
                format!(
                    "Cannot redeclare the promoted property {} here because it is already declared by an ancestor. Remove the visibility modifier from this constructor parameter.",
                    md_codify(&prop_name)
                )
                .into(),
            )
        })
    };
    let reasons = Lazy::new(move || {
        vec![Message(
            parent_pos,
            format!(
                "{} was previously declared in {}",
                md_codify(&prop_name),
                md_codify(strip_ns(&parent_name))
            )
            .into(),
        )]
    });
    create(
        ErrorCode::RedeclaringPromotedProperty,
        claim,
        Some(reasons),
        None,
    )
}

pub fn invalid_classname(p: Pos) -> T {
    let claim = Lazy::new(move || Message(p, "Not a valid class name".into()));
    create(ErrorCode::InvalidClassname, claim, None, None)
}

pub fn illegal_type_structure(pos: Pos, msg: String, fn_: String) -> T {
    let claim = Lazy::new(move || {
        let msg = format!(
            "The two arguments to `{}()` must be:\n - first: `ValidClassname::class` or an object of that class\n - second: a single-quoted string literal containing the name of a type constant of that class\n{}",
            utils_strip_ns(&fn_),
            msg
        );
        Message(pos, msg.into())
    });
    create(ErrorCode::IllegalTypeStructure, claim, None, None)
}

pub fn illegal_typeconst_direct_access(pos: Pos) -> T {
    let claim = Lazy::new(move || {
        let msg = "Type constants cannot be directly accessed. Use `type_structure(ValidClassname::class, 'TypeConstName')` instead";
        Message(pos, msg.into())
    });
    create(ErrorCode::IllegalTypeStructure, claim, None, None)
}

pub fn wrong_expression_kind_attribute(
    expr_kind: String,
    pos: Pos,
    attr: String,
    attr_class_pos: PosOrDecl,
    attr_class_name: String,
    intf_name: String,
) -> T {
    let claim = {
        let expr_kind = expr_kind.clone();
        Lazy::new(move || {
            Message(
                pos,
                format!(
                    "The {} attribute cannot be used on {}.",
                    md_codify(strip_ns(&attr)),
                    expr_kind
                )
                .into(),
            )
        })
    };
    let reasons = Lazy::new(move || {
        vec![Message(
            attr_class_pos,
            format!(
                "The attribute's class is defined here. To be available for use on {}, the {} class must implement {}.",
                expr_kind,
                md_codify(strip_ns(&attr_class_name)),
                md_codify(strip_ns(&intf_name))
            )
            .into(),
        )]
    });
    create(
        ErrorCode::WrongExpressionKindAttribute,
        claim,
        Some(reasons),
        None,
    )
}

pub fn ambiguous_object_access(
    pos: Pos,
    name: String,
    self_pos: PosOrDecl,
    vis: String,
    subclass_pos: PosOrDecl,
    class_self: String,
    class_subclass: String,
) -> T {
    let reasons = Lazy::new(move || {
        let class_self = strip_ns(&class_self);
        let class_subclass = strip_ns(&class_subclass);
        vec![
            Message(
                self_pos,
                format!(
                    "You will access the private instance declared in {}",
                    md_codify(class_self)
                )
                .into(),
            ),
            Message(
                subclass_pos,
                format!(
                    "Instead of the {} instance declared in {}",
                    vis,
                    md_codify(class_subclass)
                )
                .into(),
            ),
        ]
    });
    let claim = Lazy::new(move || {
        Message(
            pos,
            format!("This object access to {} is ambiguous", md_codify(&name)).into(),
        )
    });
    create(ErrorCode::AmbiguousObjectAccess, claim, Some(reasons), None)
}

pub fn invalid_arraykey_constraint(pos: Pos, t: String) -> T {
    let claim = Lazy::new(move || {
        Message(
            pos,
            format!(
                "This type is {}, which cannot be used as an arraykey (string | int)",
                t
            )
            .into(),
        )
    });
    create(ErrorCode::InvalidArrayKeyConstraint, claim, None, None)
}

pub fn redundant_generic(pos: Pos, variance: CoOrContra, msg: String, suggest: String) -> T {
    let variance_msg = match variance {
        CoOrContra::Co => "covariant (output)",
        CoOrContra::Contra => "contravariant (input)",
    };
    let claim = Lazy::new(move || {
        Message(
            pos,
            format!(
                "This generic parameter is redundant because it only appears in a {} position{}. Consider replacing uses of generic parameter with {} or specifying `<<__Explicit>>` on the generic parameter",
                variance_msg,
                msg,
                md_codify(&suggest)
            )
            .into(),
        )
    });
    create(ErrorCode::RedundantGeneric, claim, None, None)
}

pub fn meth_caller_trait(pos: Pos, trait_name: String) -> T {
    let claim = Lazy::new(move || {
        Message(
            pos,
            format!(
                "{} is a trait which cannot be used with `meth_caller`. Use a class instead.",
                md_codify(strip_ns(&trait_name))
            )
            .into(),
        )
    });
    create(ErrorCode::MethCallerTrait, claim, None, None)
}

pub fn duplicate_interface(pos: Pos, name: String, others: Vec<PosOrDecl>) -> T {
    let claim = Lazy::new(move || {
        Message(
            pos,
            format!(
                "Interface {} is used more than once in this declaration.",
                md_codify(strip_ns(&name))
            )
            .into(),
        )
    });
    let reasons = Lazy::new(move || {
        others
            .into_iter()
            .map(|pos| Message(pos, "Here is another occurrence".into()))
            .collect()
    });
    create(ErrorCode::DuplicateInterface, claim, Some(reasons), None)
}

pub fn enum_duplicate_value(
    pos: Pos,
    value: String,
    member_name: String,
    member_pos: PosOrDecl,
    prev_name: String,
    prev_pos: PosOrDecl,
) -> T {
    let claim = {
        let member_name = member_name.clone();
        let prev_name = prev_name.clone();
        Lazy::new(move || {
            Message(
                pos,
                format!(
                    "This enum has members {} and {} with the same value {}. Duplicate enum values are not allowed.",
                    md_codify(&prev_name),
                    md_codify(&member_name),
                    md_codify(&value)
                )
                .into(),
            )
        })
    };
    let reasons = Lazy::new(move || {
        vec![
            Message(
                prev_pos,
                format!("{} is declared here", md_codify(&prev_name)).into(),
            ),
            Message(
                member_pos,
                format!("{} is declared here", md_codify(&member_name)).into(),
            ),
        ]
    });
    create(ErrorCode::EnumDuplicateValue, claim, Some(reasons), None)
}

pub fn enum_uncheckable_value(
    pos: Pos,
    name: String,
    reasons: Lazy<(Vec<(PosOrDecl, String)>, isize)>,
) -> T {
    let claim = {
        let pos = pos.clone();
        Lazy::new(move || {
            Message(
                pos,
                format!(
                    "{} cannot be statically checked for duplicate values. Member values must be int or string literals, `nameof`, or `::class` to be checked; references to global constants (or other computed expressions) cannot be. Fix the flagged values and only include enums that can be checked, or add `<<__AllowUncheckedEnumValues>>` to the enum.",
                    md_codify(strip_ns(&name))
                )
                .into(),
            )
        })
    };
    let reasons = Lazy::new(move || {
        let (reasons, num_omitted) = reasons.force();
        let mut reasons: Vec<Message<PosOrDecl>> = reasons
            .iter()
            .map(|(pos, msg)| Message(pos.clone(), msg.clone().into()))
            .collect();
        if *num_omitted > 0 {
            reasons.push(Message(pos, format!("(and {} more)", num_omitted).into()));
        }
        reasons
    });
    create(ErrorCode::EnumUncheckableValue, claim, Some(reasons), None)
}

pub fn reified_function_reference(call_pos: Pos) -> T {
    let claim = Lazy::new(move || {
        Message(
            call_pos,
            "Invalid function reference. This function requires reified generics. Prefer using a lambda instead.".into(),
        )
    });
    create(ErrorCode::ReifiedFunctionReference, claim, None, None)
}

pub fn reinheriting_classish_const(
    dest_classish_pos: Pos,
    dest_classish_name: String,
    src_classish_pos: Pos,
    src_classish_name: String,
    existing_const_origin: String,
    const_name: String,
) -> T {
    let claim = Lazy::new(move || {
        Message(
            src_classish_pos,
            format!(
                "{} cannot re-inherit constant {} from {}",
                strip_ns(&dest_classish_name),
                const_name,
                strip_ns(&src_classish_name)
            )
            .into(),
        )
    });
    let reasons = Lazy::new(move || {
        vec![Message(
            dest_classish_pos,
            format!(
                "because it already inherited it via {}",
                strip_ns(&existing_const_origin)
            )
            .into(),
        )]
    });
    create(
        ErrorCode::RedeclaringClassishConstant,
        claim,
        Some(reasons),
        None,
    )
}

pub fn redeclaring_classish_const(
    classish_pos: Pos,
    classish_name: String,
    redeclaration_pos: Pos,
    existing_const_origin: String,
    const_name: String,
) -> T {
    let claim = Lazy::new(move || {
        Message(
            redeclaration_pos,
            format!(
                "{} cannot re-declare constant {}",
                strip_ns(&classish_name),
                const_name
            )
            .into(),
        )
    });
    let reasons = Lazy::new(move || {
        vec![Message(
            classish_pos,
            format!(
                "because it already inherited it via {}",
                strip_ns(&existing_const_origin)
            )
            .into(),
        )]
    });
    create(
        ErrorCode::RedeclaringClassishConstant,
        claim,
        Some(reasons),
        None,
    )
}

pub fn abstract_function_pointer(
    cname: String,
    meth_name: String,
    call_pos: Pos,
    decl_pos: PosOrDecl,
) -> T {
    let claim = Lazy::new(move || {
        Message(
            call_pos,
            format!(
                "Cannot create a function pointer to {}; it is abstract",
                md_codify(&format!("{}::{}", strip_ns(&cname), meth_name))
            )
            .into(),
        )
    });
    let reasons = Lazy::new(move || vec![Message(decl_pos, "Declaration is here".into())]);
    create(
        ErrorCode::AbstractFunctionPointer,
        claim,
        Some(reasons),
        None,
    )
}

pub fn inherited_class_member_with_different_case(
    member_type: String,
    name: &str,
    name_prev: &str,
    p: Pos,
    child_class: String,
    prev_class: String,
    prev_class_pos: PosOrDecl,
) -> T {
    let name = strip_ns(name).to_string();
    let name_prev = strip_ns(name_prev).to_string();
    let claim = {
        let member_type = member_type.clone();
        let name = name.clone();
        let name_prev = name_prev.clone();
        Lazy::new(move || {
            let child_class = strip_ns(&child_class);
            Message(
                p,
                format!(
                    "{} inherits a {} named {} whose name differs from this one ({}) only by case.",
                    child_class,
                    member_type,
                    md_codify(&name_prev),
                    md_codify(&name)
                )
                .into(),
            )
        })
    };
    let reasons = Lazy::new(move || {
        let prev_class = strip_ns(&prev_class);
        vec![Message(
            prev_class_pos,
            format!(
                "It was inherited from {} as {}. If you meant to override it, please use the same casing as the inherited {}. Otherwise, please choose a different name for the new {}",
                prev_class,
                md_codify(&highlight_differences(&name, &name_prev)),
                member_type,
                member_type
            )
            .into(),
        )]
    });
    create(
        ErrorCode::InheritedMethodCaseDiffers,
        claim,
        Some(reasons),
        None,
    )
}

pub fn multiple_inherited_class_member_with_different_case(
    member_type: String,
    name1: &str,
    name2: &str,
    class1: &str,
    class2: &str,
    child_class: String,
    child_p: Pos,
    p1: PosOrDecl,
    p2: PosOrDecl,
) -> T {
    let name1 = strip_ns(name1).to_string();
    let name2 = strip_ns(name2).to_string();
    let class1 = strip_ns(class1).to_string();
    let class2 = strip_ns(class2).to_string();
    let claim = {
        let member_type = member_type.clone();
        let name1 = name1.clone();
        Lazy::new(move || {
            let child_class = strip_ns(&child_class);
            Message(
                child_p,
                format!(
                    "{} inherited two versions of the {} {} whose names differ only by case.",
                    md_codify(child_class),
                    member_type,
                    md_codify(&name1)
                )
                .into(),
            )
        })
    };
    let reasons = Lazy::new(move || {
        vec![
            Message(
                p1,
                format!("It inherited {} from {} here.", md_codify(&name1), class1).into(),
            ),
            Message(
                p2,
                format!(
                    "And {} from {} here. Please rename these {}s to the same casing.",
                    md_codify(&name2),
                    class2,
                    member_type
                )
                .into(),
            ),
        ]
    });
    create(
        ErrorCode::InheritedMethodCaseDiffers,
        claim,
        Some(reasons),
        None,
    )
}

pub fn multiple_instantiation_inheritence(
    type_name: &str,
    implements_or_extends: String,
    interface_name: &str,
    winning_implements: ImplementsInfo,
    losing_implements: ImplementsInfo,
) -> T {
    // [p(Y)]       This makes [C] implement [or extend] [I]<[T1]> but it already implements [or extends] [I] at another instantiation
    // [p(X)]       it already implemented [I]<[T2]> [via [X]]
    // [[p(I<T1>)]  this is where [Y] implements/extends [I]]
    // [[p(I<T2>)]  this is where [X] implements/extends [I]]
    // [p(?)]           [I]<[T1]> should be a subtype of [I]<[T2]>
    // ... subtype error...
    let ImplementsInfo {
        pos: winning_itf_pos,
        instantiation: winning_instantiation,
        via_direct_parent: (winning_pos, winning_parent),
    } = winning_implements;
    let ImplementsInfo {
        pos: losing_itf_pos,
        instantiation: losing_instantiation,
        via_direct_parent: (losing_pos, losing_parent),
    } = losing_implements;
    let type_name = strip_ns(type_name).to_string();
    let interface_name = strip_ns(interface_name).to_string();
    let winning_parent = strip_ns(&winning_parent).to_string();
    let losing_parent = strip_ns(&losing_parent).to_string();
    let winning_is_indirect = winning_parent != interface_name;
    let losing_is_indirect = losing_parent != interface_name;
    let winning_instantiation = format!("{}<{}>", interface_name, winning_instantiation.join(", "));
    let losing_instantiation = format!("{}<{}>", interface_name, losing_instantiation.join(", "));
    let claim = {
        let implements_or_extends = implements_or_extends.clone();
        let losing_instantiation = losing_instantiation.clone();
        let interface_name = interface_name.clone();
        Lazy::new(move || {
            let msg = format!(
                "{}{} {} {} but it already {} {} at another instantiation",
                if losing_is_indirect {
                    "This makes "
                } else {
                    ""
                },
                type_name,
                implements_or_extends,
                losing_instantiation,
                implements_or_extends,
                interface_name
            );
            Message(losing_pos, msg.into())
        })
    };
    let reasons = Lazy::new(move || {
        let mut reasons = vec![Message(
            winning_pos,
            format!(
                "It already {} {}{}",
                implements_or_extends,
                winning_instantiation,
                if winning_parent == interface_name {
                    "".to_string()
                } else {
                    format!(" via {}", winning_parent)
                }
            )
            .into(),
        )];
        if winning_is_indirect {
            reasons.push(Message(
                winning_itf_pos.clone(),
                format!(
                    "This is where {} implements {}",
                    winning_parent, interface_name
                )
                .into(),
            ));
        }
        if losing_is_indirect {
            reasons.push(Message(
                losing_itf_pos,
                format!(
                    "This is where {} implements {}",
                    losing_parent, interface_name
                )
                .into(),
            ));
        }
        reasons.push(Message(
            winning_itf_pos,
            format!(
                "{} should be a subtype of {}, but it's not because",
                winning_instantiation, losing_instantiation
            )
            .into(),
        ));
        reasons
    });
    create(
        ErrorCode::MultipleInstantiationInheritence,
        claim,
        Some(reasons),
        None,
    )
}

pub fn classish_kind_to_string(kind: ClassishKind) -> &'static str {
    match kind {
        ClassishKind::Cclass(_) => "class ",
        ClassishKind::Ctrait => "trait ",
        ClassishKind::Cinterface => "interface ",
        ClassishKind::CenumClass(_) => "enum class ",
        ClassishKind::Cenum => "enum ",
    }
}

pub fn parent_support_dynamic_type(
    pos: Pos,
    (child_name, child_kind): (String, ClassishKind),
    (parent_name, parent_kind): (String, ClassishKind),
    child_support_dynamic_type: bool,
) -> T {
    let claim = Lazy::new(move || {
        let kinds_to_use =
            |child_kind: ClassishKind, parent_kind: ClassishKind| match (child_kind, parent_kind) {
                (_, ClassishKind::Cclass(_)) => "extends ",
                (_, ClassishKind::Ctrait) => "uses ",
                (ClassishKind::Cinterface, ClassishKind::Cinterface) => "extends ",
                (_, ClassishKind::Cinterface) => "implements ",
                (_, ClassishKind::CenumClass(_)) | (_, ClassishKind::Cenum) => "",
            };
        let child_name = md_codify(strip_ns(&child_name));
        let child_kind_s = classish_kind_to_string(child_kind);
        let parent_name = md_codify(strip_ns(&parent_name));
        let parent_kind_s = classish_kind_to_string(parent_kind);
        Message(
            pos,
            format!(
                "{}{}{}declare <<__SupportDynamicType>> because it {}{}{} which does{}",
                string_capitalize(child_kind_s),
                child_name,
                if child_support_dynamic_type {
                    " cannot "
                } else {
                    " must "
                },
                kinds_to_use(child_kind, parent_kind),
                parent_kind_s,
                parent_name,
                if child_support_dynamic_type {
                    " not"
                } else {
                    ""
                }
            )
            .into(),
        )
    });
    create(ErrorCode::ImplementsDynamic, claim, None, None)
}

pub fn property_is_not_enforceable(
    pos: Pos,
    prop_name: &str,
    class_name: String,
    (prop_pos, prop_type): (PosOrDecl, String),
) -> T {
    let prop_name = md_codify(prop_name);
    let claim = {
        let prop_name = prop_name.clone();
        Lazy::new(move || {
            let class_name = md_codify(strip_ns(&class_name));
            Message(
                pos,
                format!(
                    "Class {} cannot support dynamic because property {} does not have an enforceable type",
                    class_name, prop_name
                )
                .into(),
            )
        })
    };
    let reasons = Lazy::new(move || {
        let prop_type = md_codify(&prop_type);
        vec![Message(
            prop_pos,
            format!("Property {} has type {}", prop_name, prop_type).into(),
        )]
    });
    create(ErrorCode::ImplementsDynamic, claim, Some(reasons), None)
}

pub fn property_is_not_dynamic(
    pos: Pos,
    prop_name: &str,
    class_name: String,
    (prop_pos, prop_type): (PosOrDecl, String),
) -> T {
    let prop_name = md_codify(prop_name);
    let claim = {
        let prop_name = prop_name.clone();
        Lazy::new(move || {
            let class_name = md_codify(strip_ns(&class_name));
            Message(
                pos,
                format!(
                    "Class {} cannot support dynamic because property {} cannot be assigned to dynamic",
                    class_name, prop_name
                )
                .into(),
            )
        })
    };
    let reasons = Lazy::new(move || {
        let prop_type = md_codify(&prop_type);
        vec![Message(
            prop_pos,
            format!("Property {} has type {}", prop_name, prop_type).into(),
        )]
    });
    create(ErrorCode::ImplementsDynamic, claim, Some(reasons), None)
}

pub fn private_property_is_not_enforceable(
    pos: Pos,
    prop_name: &str,
    class_name: String,
    (prop_pos, prop_type): (PosOrDecl, String),
) -> T {
    let prop_name = md_codify(prop_name);
    let claim = {
        let prop_name = prop_name.clone();
        Lazy::new(move || {
            let class_name = md_codify(strip_ns(&class_name));

            Message(
                pos,
                format!(
                    "Cannot write to property {} through dynamic type because private property in {} does not have an enforceable type",
                    prop_name, class_name
                )
                .into(),
            )
        })
    };
    let reasons = Lazy::new(move || {
        let prop_type = md_codify(&prop_type);

        vec![Message(
            prop_pos,
            format!("Property {} has type {}", prop_name, prop_type).into(),
        )]
    });
    create(ErrorCode::PrivateDynamicWrite, claim, Some(reasons), None)
}

pub fn private_property_is_not_dynamic(
    pos: Pos,
    prop_name: &str,
    class_name: String,
    (prop_pos, prop_type): (PosOrDecl, String),
) -> T {
    let prop_name = md_codify(prop_name);
    let claim = {
        let prop_name = prop_name.clone();
        Lazy::new(move || {
            let class_name = md_codify(strip_ns(&class_name));

            Message(
                pos,
                format!(
                    "Cannot read from property {} through dynamic type because private property in {} cannot be assigned to dynamic",
                    prop_name, class_name
                )
                .into(),
            )
        })
    };
    let reasons = Lazy::new(move || {
        let prop_type = md_codify(&prop_type);

        vec![Message(
            prop_pos,
            format!("Property {} has type {}", prop_name, prop_type).into(),
        )]
    });
    create(ErrorCode::PrivateDynamicRead, claim, Some(reasons), None)
}

#[cfg(test)]
mod tests {
    use std::cell::Cell;
    use std::cell::RefCell;
    use std::rc::Rc;

    use oxidized::ast_defs::Abstraction;

    use super::*;
    use crate::typing_error_utils::common::testing::pos;

    // Each raw string is copied from an `.exp` file named above its test (in
    // `hphp/hack/test/typecheck`); the arguments are the positions, the names
    // and the already printed types of that error. Expected texts that are
    // not in an `.exp` file are ordinary (not raw) strings.

    /// The error as `hh single` prints it.
    fn render(t: &T) -> String {
        crate::typing_error_utils::common::testing::render(t.code, &t.claim, &t.reasons)
    }

    fn s(x: &str) -> String {
        x.to_string()
    }

    fn m(pos: PosOrDecl, msg: &str) -> Message<PosOrDecl> {
        Message(pos, msg.into())
    }

    // T90599414.php.exp
    // new_static2.php.exp
    #[test]
    fn test_unify_error() {
        assert_eq!(
            render(&unify_error(pos("T90599414.php", 6, 3, 10), None, None)),
            r#"ERROR: File "T90599414.php", line 6, characters 3-10:
Typing error (Typing[4110])
"#
        );
        assert_eq!(
            render(&unify_error(
                pos("new_static2.php", 23, 12, 23),
                Some(s("Invalid return type")),
                Some(Lazy::from_val(vec![
                    m(pos("new_static2.php", 13, 18, 18), "Expected `T`"),
                    m(pos("new_static2.php", 22, 35, 37), "But got `int`"),
                    m(
                        pos("new_static2.php", 22, 35, 37),
                        "This type argument to `A` must match exactly (it is invariant)"
                    ),
                ]))
            )),
            r#"ERROR: File "new_static2.php", line 23, characters 12-23:
Invalid return type (Typing[4110])
  File "new_static2.php", line 13, characters 18-18:
  Expected `T`
  File "new_static2.php", line 22, characters 35-37:
  But got `int`
  File "new_static2.php", line 22, characters 35-37:
  This type argument to `A` must match exactly (it is invariant)
"#
        );
    }

    // using/using_bad.php.exp
    #[test]
    fn test_using_error() {
        assert_eq!(
            render(&using_error(pos("using_bad.php", 29, 10, 31), false)),
            r#"ERROR: File "using_bad.php", line 29, characters 10-31:
This expression is used in a `using` clause so it must have type `\IDisposable` (Typing[4110])
"#
        );
        assert_eq!(
            render(&using_error(pos("using_bad.php", 33, 15, 31), true)),
            r#"ERROR: File "using_bad.php", line 33, characters 15-31:
This expression is used in a `using` clause with await so it must have type `\IAsyncDisposable` (Typing[4110])
"#
        );
    }

    // abstract_typeconsts/multiple-definitions/class_extends_implements_bounds_not_subtypes.php.exp
    #[test]
    fn test_bad_decl_override() {
        assert_eq!(
            render(&bad_decl_override(
                "\\C3",
                pos(
                    "class_extends_implements_bounds_not_subtypes.php",
                    30,
                    27,
                    28
                ),
                "\\C1"
            )),
            r#"ERROR: File "class_extends_implements_bounds_not_subtypes.php", line 30, characters 27-28:
Some members in class `C3` are incompatible with those declared in type `C1` (Typing[4340])
"#
        );
    }

    // class_pointers/tyvar_upper_bound/level_1/transitivity.php.exp
    #[test]
    fn test_explain_where_constraint() {
        assert_eq!(
            render(&explain_where_constraint(
                pos("transitivity.php", 24, 11, 21),
                pos("transitivity.php", 7, 10, 20),
                false
            )),
            r#"ERROR: File "transitivity.php", line 24, characters 11-21:
A `where` type constraint is violated here (Typing[4323])
  File "transitivity.php", line 7, characters 10-20:
  This is the method with `where` type constraints
"#
        );
    }

    // escape/expr_dep_escapes_1.php.exp
    #[test]
    fn test_rigid_tvar_escape() {
        assert_eq!(
            render(&rigid_tvar_escape(
                pos("expr_dep_escapes_1.php", 13, 8, 67),
                s("lambda")
            )),
            r#"ERROR: File "expr_dep_escapes_1.php", line 13, characters 8-67:
Rigid type variable escapes its lambda (Typing[4442])
"#
        );
    }

    // shape_splat/error_splat_non_shape.php.exp
    #[test]
    fn test_invalid_type_hint() {
        assert_eq!(
            render(&invalid_type_hint(pos(
                "error_splat_non_shape.php",
                6,
                13,
                45
            ))),
            r#"ERROR: File "error_splat_non_shape.php", line 6, characters 13-45:
Invalid type hint (Typing[4419])
"#
        );
    }

    // trait_require_error_noimplement.php.exp
    #[test]
    fn test_unsatisfied_req() {
        assert_eq!(
            render(&unsatisfied_req(
                pos("trait_require_error_noimplement.php", 28, 16, 17),
                pos("trait_require_error_noimplement.php", 29, 7, 12),
                s("\\I1"),
                pos("trait_require_error_noimplement.php", 17, 22, 23)
            )),
            r#"ERROR: File "trait_require_error_noimplement.php", line 28, characters 16-17:
This class does not satisfy all the requirements of its traits or interfaces. (Typing[4111])
  File "trait_require_error_noimplement.php", line 29, characters 7-12:
  This requires to extend or implement I1
  File "trait_require_error_noimplement.php", line 17, characters 22-23:
  Required here
"#
        );
        // When the requirement is at the position of the trait, it is not
        // repeated.
        let t = unsatisfied_req(
            pos("a.php", 28, 16, 17),
            pos("a.php", 29, 7, 12),
            s("\\I1"),
            pos("a.php", 29, 7, 12),
        );
        assert_eq!(t.reasons.force().len(), 1);
    }

    // require_class/requireclass_hierarchy_04.bad.php.exp
    #[test]
    fn test_unsatisfied_req_class() {
        assert_eq!(
            render(&unsatisfied_req_class(
                pos("requireclass_hierarchy_04.bad.php", 18, 7, 7),
                pos("requireclass_hierarchy_04.bad.php", 19, 7, 8),
                s("\\C"),
                pos("requireclass_hierarchy_04.bad.php", 9, 17, 17)
            )),
            r#"ERROR: File "requireclass_hierarchy_04.bad.php", line 18, characters 7-7:
This class does not satisfy all the requirements of its traits or interfaces. (Typing[4111])
  File "requireclass_hierarchy_04.bad.php", line 19, characters 7-8:
  This requires to be exactly C
  File "requireclass_hierarchy_04.bad.php", line 9, characters 17-17:
  Required here
"#
        );
    }

    // require_class/requireclass_abstract_01.bad.php.exp
    #[test]
    fn test_req_class_not_final() {
        assert_eq!(
            render(&req_class_not_final(
                pos("requireclass_abstract_01.bad.php", 5, 16, 16),
                pos("requireclass_abstract_01.bad.php", 6, 7, 7),
                pos("requireclass_abstract_01.bad.php", 10, 17, 17)
            )),
            r#"ERROR: File "requireclass_abstract_01.bad.php", line 5, characters 16-16:
This class must be final because it uses a trait with a require class constraint. (Typing[4111])
  File "requireclass_abstract_01.bad.php", line 6, characters 7-7:
  The trait with a require class constraint is used here
  File "requireclass_abstract_01.bad.php", line 10, characters 17-17:
  The require class constraint is here
"#
        );
    }

    // require_class/requireclass_conflict_01.bad.php.exp
    #[test]
    fn test_incompatible_reqs() {
        assert_eq!(
            render(&incompatible_reqs(
                pos("requireclass_conflict_01.bad.php", 10, 7, 7),
                s("\\C"),
                pos("requireclass_conflict_01.bad.php", 7, 26, 26),
                pos("requireclass_conflict_01.bad.php", 8, 28, 28)
            )),
            r#"ERROR: File "requireclass_conflict_01.bad.php", line 10, characters 7-7:
This trait defines incompatible requirements. (Typing[4111])
  File "requireclass_conflict_01.bad.php", line 7, characters 26-26:
  This requires exactly class C
  File "requireclass_conflict_01.bad.php", line 8, characters 28-28:
  This requires a subtype of class C
"#
        );
    }

    // require_class/requireclass_nouse_01.bad.php.exp
    #[test]
    fn test_trait_not_used() {
        assert_eq!(
            render(&trait_not_used(
                pos("requireclass_nouse_01.bad.php", 8, 7, 8),
                s("\\T1"),
                pos("requireclass_nouse_01.bad.php", 9, 17, 17),
                pos("requireclass_nouse_01.bad.php", 16, 13, 13),
                "\\C"
            )),
            r#"ERROR: File "requireclass_nouse_01.bad.php", line 8, characters 7-8:
Trait T1 requires class C but C does not use it. Either use the trait or delete it. (Typing[4466])
  File "requireclass_nouse_01.bad.php", line 16, characters 13-13:
  Class C is defined here.
  File "requireclass_nouse_01.bad.php", line 9, characters 17-17:
  The require class requirement is here.
"#
        );
    }

    // new_static2.php.exp
    // static_and_arrow3.php.exp
    #[test]
    fn test_member_not_found() {
        assert_eq!(
            render(&member_not_found(
                pos("new_static2.php", 19, 9, 11),
                MethodOrProperty::method_,
                s("xxx"),
                s("\\A"),
                pos("new_static2.php", 13, 16, 16),
                Some((
                    InstanceOrStatic::instance,
                    pos("new_static2.php", 15, 19, 21),
                    s("foo")
                )),
                Lazy::from_val(vec![m(
                    pos("new_static2.php", 13, 16, 16),
                    "This is why I think it is an object of type A"
                )]),
            )),
            r#"ERROR: File "new_static2.php", line 19, characters 9-11:
No instance method `xxx` in `A` (Typing[4053])
  File "new_static2.php", line 15, characters 19-21:
  Did you mean `foo` instead?
  File "new_static2.php", line 13, characters 16-16:
  This is why I think it is an object of type A
  File "new_static2.php", line 13, characters 16-16:
  Declaration of `A` is here
"#
        );
        assert_eq!(
            render(&member_not_found(
                pos("static_and_arrow3.php", 18, 12, 13),
                MethodOrProperty::method_,
                s("f2"),
                s("\\Foo"),
                pos("static_and_arrow3.php", 16, 7, 9),
                Some((
                    InstanceOrStatic::static_,
                    pos("static_and_arrow3.php", 13, 26, 27),
                    s("f2")
                )),
                Lazy::from_val(vec![m(
                    pos("static_and_arrow3.php", 16, 7, 9),
                    "This is why I think it is an object of type Foo"
                )]),
            )),
            r#"ERROR: File "static_and_arrow3.php", line 18, characters 12-13:
No instance method `f2` in `Foo` (Typing[4053])
  File "static_and_arrow3.php", line 13, characters 26-27:
  Did you mean static method `f2` instead?
  File "static_and_arrow3.php", line 16, characters 7-9:
  This is why I think it is an object of type Foo
  File "static_and_arrow3.php", line 16, characters 7-9:
  Declaration of `Foo` is here
"#
        );
        // The quickfix replaces the member name by the suggestion.
        let t = member_not_found(
            pos("new_static2.php", 19, 9, 11),
            MethodOrProperty::method_,
            s("xxx"),
            s("\\A"),
            pos("new_static2.php", 13, 16, 16),
            Some((
                InstanceOrStatic::instance,
                pos("new_static2.php", 15, 19, 21),
                s("foo"),
            )),
            Lazy::from_val(vec![]),
        );
        assert_eq!(
            t.quickfixes,
            vec![Quickfix {
                title: s("Change to ->foo"),
                edits: Edits::Eager(vec![(s("foo"), pos("new_static2.php", 19, 9, 11))]),
                hint_styles: vec![],
            }]
        );
        // Without a hint there is neither a suggestion nor a quickfix, and a
        // property is a "property".
        let t = member_not_found(
            pos("a.php", 3, 5, 6),
            MethodOrProperty::property,
            s("x"),
            s("\\Foo"),
            pos("a.php", 1, 7, 9),
            None,
            Lazy::from_val(vec![]),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"a.php\", line 3, characters 5-6:\n\
             No property `x` in `Foo` (Typing[4053])\n  \
             File \"a.php\", line 1, characters 7-9:\n  \
             Declaration of `Foo` is here\n"
        );
        assert_eq!(t.quickfixes, vec![]);
    }

    // meth_caller/meth_caller_magic.php.exp
    #[test]
    fn test_construct_not_instance_method() {
        assert_eq!(
            render(&construct_not_instance_method(pos(
                "meth_caller_magic.php",
                8,
                30,
                42
            ))),
            r#"ERROR: File "meth_caller_magic.php", line 8, characters 30-42:
`__construct` is not an instance method and shouldn't be invoked directly (Typing[4463])
"#
        );
    }

    // reified_generics/function_missing_args.php.exp
    // function_pointer/simple_function_pointer_targs_bad_mismatch.php.exp
    // funcall_explicit_arg_arity_error.php.exp
    #[test]
    fn test_expected_tparam() {
        assert_eq!(
            render(&expected_tparam(
                pos("function_missing_args.php", 9, 3, 3),
                0,
                pos("function_missing_args.php", 5, 10, 10)
            )),
            r#"ERROR: File "function_missing_args.php", line 9, characters 3-3:
Expected no type parameters (Typing[4029])
  File "function_missing_args.php", line 5, characters 10-10:
  Definition is here
"#
        );
        assert_eq!(
            render(&expected_tparam(
                pos("simple_function_pointer_targs_bad_mismatch.php", 7, 8, 10),
                1,
                pos("simple_function_pointer_targs_bad_mismatch.php", 3, 10, 12)
            )),
            r#"ERROR: File "simple_function_pointer_targs_bad_mismatch.php", line 7, characters 8-10:
Expected exactly one type parameter (Typing[4029])
  File "simple_function_pointer_targs_bad_mismatch.php", line 3, characters 10-12:
  Definition is here
"#
        );
        assert_eq!(
            render(&expected_tparam(
                pos("funcall_explicit_arg_arity_error.php", 8, 10, 12),
                2,
                pos("funcall_explicit_arg_arity_error.php", 3, 10, 12)
            )),
            r#"ERROR: File "funcall_explicit_arg_arity_error.php", line 8, characters 10-12:
Expected 2 type parameters (Typing[4029])
  File "funcall_explicit_arg_arity_error.php", line 3, characters 10-12:
  Definition is here
"#
        );
    }

    // typeconsts/stricter_typeconsts/concrete_concrete_error.php.exp
    #[test]
    fn test_typeconst_concrete_concrete_override() {
        assert_eq!(
            render(&typeconst_concrete_concrete_override(
                pos("concrete_concrete_error.php", 9, 14, 14),
                pos("concrete_concrete_error.php", 4, 14, 14)
            )),
            r#"ERROR: File "concrete_concrete_error.php", line 9, characters 14-14:
Cannot re-declare this type constant (Typing[4430])
  File "concrete_concrete_error.php", line 4, characters 14-14:
  Previously defined here
"#
        );
    }

    // parent_override_trait1.php.exp
    #[test]
    fn test_constant_multiple_concrete_conflict() {
        assert_eq!(
            render(&constant_multiple_concrete_conflict(
                pos("parent_override_trait1.php", 20, 7, 7),
                s("FOO1"),
                vec![
                    (pos("parent_override_trait1.php", 4, 9, 12), Some(s("T1"))),
                    (pos("parent_override_trait1.php", 10, 9, 12), Some(s("B"))),
                ]
            )),
            r#"ERROR: File "parent_override_trait1.php", line 20, characters 7-7:
Constant FOO1 is defined concretely in multiple ancestors (Typing[4374])
  File "parent_override_trait1.php", line 4, characters 9-12:
  One conflicting definition is here, inherited through T1
  File "parent_override_trait1.php", line 10, characters 9-12:
  Another conflicting definition is here, inherited through B
"#
        );
    }

    // memoize/bad_shape2.php.exp
    #[test]
    fn test_invalid_memoized_param() {
        assert_eq!(
            render(&invalid_memoized_param(
                pos("bad_shape2.php", 12, 32, 33),
                Lazy::from_val(vec![m(
                    pos("bad_shape2.php", 7, 16, 18),
                    "This is an object of type Bar"
                )])
            )),
            r#"ERROR: File "bad_shape2.php", line 12, characters 32-33:
Parameters to memoized function must be null, bool, int, float, string, an object deriving IMemoizeParam, or a Container thereof. See also http://docs.hhvm.com/hack/attributes/special#__memoize (Typing[4149])
  File "bad_shape2.php", line 7, characters 16-18:
  This is an object of type Bar
"#
        );
    }

    // invalid_arraykey/invalid_arraykey.php.exp
    #[test]
    fn test_invalid_arraykey() {
        assert_eq!(
            render(&invalid_arraykey(
                pos("invalid_arraykey.php", 6, 3, 14),
                pos("invalid_arraykey.php", 4, 8, 13),
                s("an object of type dict<string, int>"),
                pos("invalid_arraykey.php", 6, 6, 9),
                s("null"),
                ReadOrWrite::write,
            )),
            r#"ERROR: File "invalid_arraykey.php", line 6, characters 3-14:
This value is not a valid key type for this container (Typing[4371])
  File "invalid_arraykey.php", line 4, characters 8-13:
  This container is an object of type dict<string, int>
  File "invalid_arraykey.php", line 6, characters 6-9:
  Null cannot be used as a key for an object of type dict<string, int>
"#
        );
        assert_eq!(
            render(&invalid_arraykey(
                pos("invalid_arraykey.php", 7, 3, 13),
                pos("invalid_arraykey.php", 4, 8, 13),
                s("an object of type dict<?string, int>"),
                pos("invalid_arraykey.php", 7, 6, 8),
                s("a float"),
                ReadOrWrite::write,
            )),
            r#"ERROR: File "invalid_arraykey.php", line 7, characters 3-13:
This value is not a valid key type for this container (Typing[4371])
  File "invalid_arraykey.php", line 4, characters 8-13:
  This container is an object of type dict<?string, int>
  File "invalid_arraykey.php", line 7, characters 6-8:
  A float cannot be used as a key for an object of type dict<?string, int>
"#
        );
        // Reading has the code of an index type mismatch.
        let t = invalid_arraykey(
            pos("a.php", 6, 3, 14),
            pos("a.php", 4, 8, 13),
            s("a dict"),
            pos("a.php", 6, 6, 9),
            s("null"),
            ReadOrWrite::read,
        );
        assert_eq!(t.code, ErrorCode::IndexTypeMismatch);
    }

    // array_append_set_bad.php.exp
    #[test]
    fn test_invalid_set_value() {
        assert_eq!(
            render(&invalid_set_value(
                pos("array_append_set_bad.php", 20, 3, 12),
                pos("array_append_set_bad.php", 19, 8, 12),
                s("an object of type Set<(arraykey & _)>"),
                pos("array_append_set_bad.php", 20, 10, 12),
                s("a float"),
            )),
            r#"ERROR: File "array_append_set_bad.php", line 20, characters 3-12:
Set values must be arraykeys (Typing[4324])
  File "array_append_set_bad.php", line 19, characters 8-12:
  This container is an object of type Set<(arraykey & _)>
  File "array_append_set_bad.php", line 20, characters 10-12:
  A float is not an arraykey
"#
        );
    }

    // hh_expect.php.exp
    #[test]
    fn test_hh_expect() {
        assert_eq!(
            render(&hh_expect(pos("hh_expect.php", 6, 3, 24), false)),
            r#"ERROR: File "hh_expect.php", line 6, characters 3-24:
hh_expect type mismatch (Typing[4453])
"#
        );
        assert_eq!(
            render(&hh_expect(pos("hh_expect.php", 11, 3, 33), true)),
            r#"ERROR: File "hh_expect.php", line 11, characters 3-33:
hh_expect_equivalent type mismatch (Typing[4452])
"#
        );
    }

    // eq_constraint.php.exp
    #[test]
    fn test_null_member() {
        assert_eq!(
            render(&null_member(
                pos("eq_constraint.php", 34, 20, 30),
                None,
                ReadOrWrite::read,
                MethodOrProperty::method_,
                s("assertIsFoo"),
                Lazy::from_val(vec![
                    m(pos("eq_constraint.php", 31, 40, 43), "This can be null"),
                    m(
                        pos("eq_constraint.php", 27, 30, 35),
                        "  via this generic `Tclass`"
                    ),
                ]),
            )),
            r#"ERROR: File "eq_constraint.php", line 34, characters 20-30:
You are trying to access the method `assertIsFoo` but this object can be null. (Typing[4064])
  File "eq_constraint.php", line 31, characters 40-43:
  This can be null
  File "eq_constraint.php", line 27, characters 30-35:
    via this generic `Tclass`
"#
        );
        // `$x->assertIsFoo()` with the receiver on the same line: the quickfix
        // replaces the two characters before the member name.
        let t = null_member(
            pos("eq_constraint.php", 34, 20, 30),
            Some(&pos("eq_constraint.php", 34, 14, 17)),
            ReadOrWrite::read,
            MethodOrProperty::method_,
            s("assertIsFoo"),
            Lazy::from_val(vec![]),
        );
        assert_eq!(
            t.quickfixes,
            vec![Quickfix {
                title: s("Add null-safe get"),
                edits: Edits::Eager(vec![(s("?->"), pos("eq_constraint.php", 34, 18, 19))]),
                hint_styles: vec![],
            }]
        );
        // The receiver is on another line: no quickfix. Writing a property
        // has its own code.
        let t = null_member(
            pos("eq_constraint.php", 34, 20, 30),
            Some(&pos("eq_constraint.php", 33, 14, 17)),
            ReadOrWrite::write,
            MethodOrProperty::property,
            s("i"),
            Lazy::from_val(vec![]),
        );
        assert_eq!(t.quickfixes, vec![]);
        assert_eq!(
            render(&t),
            "ERROR: File \"eq_constraint.php\", line 34, characters 20-30:\n\
             You are trying to access the property `i` but this object can be null. (Typing[4372])\n"
        );
    }

    // class_meth5.php.exp
    // named_parameters/named_params_errors.php.exp
    // named_parameters/named_params_methods.php.exp
    // named_parameters/named_params_lambda_synthesis_2_errors.php.exp
    // named_parameters/named_params_duplicate_args.php.exp
    #[test]
    fn test_typing_arity() {
        assert_eq!(
            render(&typing_too_many_args(
                pos("class_meth5.php", 20, 10, 18),
                pos("class_meth5.php", 19, 8, 14),
                1,
                0,
                None
            )),
            r#"ERROR: File "class_meth5.php", line 20, characters 10-18:
Too many positional arguments (expected 0 but got 1) (Typing[4105])
  File "class_meth5.php", line 19, characters 8-14:
  Definition is here
"#
        );
        assert_eq!(
            render(&typing_too_few_args(
                pos("named_params_errors.php", 13, 3, 26),
                pos("named_params_errors.php", 3, 10, 19),
                0,
                1,
                None
            )),
            r#"ERROR: File "named_params_errors.php", line 13, characters 3-26:
Too few positional arguments (required 1 but got 0) (Typing[4104])
  File "named_params_errors.php", line 3, characters 10-19:
  Definition is here
"#
        );
        assert_eq!(
            render(&missing_named_args(
                pos("named_params_methods.php", 20, 9, 40),
                pos("named_params_methods.php", 7, 19, 42),
                vec![s("c")]
            )),
            r#"ERROR: File "named_params_methods.php", line 20, characters 9-40:
Missing required named argument: c (Typing[4499])
  File "named_params_methods.php", line 7, characters 19-42:
  Definition is here
"#
        );
        assert_eq!(
            render(&unexpected_named_args(
                pos("named_params_lambda_synthesis_2_errors.php", 11, 14, 69),
                pos("named_params_lambda_synthesis_2_errors.php", 11, 14, 51),
                vec![s("z")]
            )),
            r#"ERROR: File "named_params_lambda_synthesis_2_errors.php", line 11, characters 14-69:
Unexpected named argument: z (Typing[4500])
  File "named_params_lambda_synthesis_2_errors.php", line 11, characters 14-51:
  Definition is here
"#
        );
        assert_eq!(
            render(&duplicate_named_args(
                pos("named_params_duplicate_args.php", 12, 3, 36),
                vec![s("b")]
            )),
            r#"ERROR: File "named_params_duplicate_args.php", line 12, characters 3-36:
Duplicate named argument: b (Typing[4501])
"#
        );
    }

    // test_array9.php.exp
    #[test]
    fn test_non_object_member() {
        assert_eq!(
            render(&non_object_member(
                pos("test_array9.php", 16, 16, 30),
                ReadOrWrite::read,
                &Lazy::from_val(s("an int")),
                s("unknownFunction"),
                NonObjectMemberKind::method_,
                pos("test_array9.php", 15, 24, 24),
            )),
            r#"ERROR: File "test_array9.php", line 16, characters 16-30:
You are trying to access the method `unknownFunction` but this is an int (Typing[4062])
  File "test_array9.php", line 15, characters 24-24:
  Definition is here
"#
        );
        // `ty_name` is forced when the function is called, not when the claim
        // is.
        let forced = Rc::new(Cell::new(false));
        let ty_name = {
            let forced = forced.clone();
            Lazy::new(move || {
                forced.set(true);
                s("an int")
            })
        };
        let _t = non_object_member(
            pos("a.php", 2, 1, 2),
            ReadOrWrite::write,
            &ty_name,
            s("x"),
            NonObjectMemberKind::property,
            pos("a.php", 1, 1, 2),
        );
        assert!(forced.get());
    }

    // trait_bad_override.php.exp
    #[test]
    fn test_static_instance_intersection() {
        assert_eq!(
            render(&static_instance_intersection(
                pos("trait_bad_override.php", 20, 7, 14),
                Lazy::from_val(pos("trait_bad_override.php", 5, 10, 12)),
                Lazy::from_val(pos("trait_bad_override.php", 13, 20, 22)),
                s("$x"),
                MethOrProp::prop,
            )),
            r#"ERROR: File "trait_bad_override.php", line 20, characters 7-14:
This class overrides some members with a different staticness (Typing[4091])
  File "trait_bad_override.php", line 5, characters 10-12:
  The property `$x` is declared as non-static here
  File "trait_bad_override.php", line 13, characters 20-22:
  But it conflicts with an inherited static declaration here
"#
        );
        assert_eq!(
            render(&static_instance_intersection(
                pos("trait_bad_override.php", 20, 7, 14),
                Lazy::from_val(pos("trait_bad_override.php", 9, 22, 24)),
                Lazy::from_val(pos("trait_bad_override.php", 17, 26, 28)),
                s("lol"),
                MethOrProp::meth,
            )),
            r#"ERROR: File "trait_bad_override.php", line 20, characters 7-14:
This class overrides some members with a different staticness (Typing[4091])
  File "trait_bad_override.php", line 9, characters 22-24:
  The method `lol` is declared as non-static here
  File "trait_bad_override.php", line 17, characters 26-28:
  But it conflicts with an inherited static declaration here
"#
        );
        // The positions are forced by the reasons, `static_pos` first (OCaml
        // evaluates the elements of a list literal from the last one).
        let order = Rc::new(RefCell::new(vec![]));
        let mk = |name: &'static str, line: usize| {
            let order = order.clone();
            Lazy::new(move || {
                order.borrow_mut().push(name);
                pos("a.php", line, 1, 2)
            })
        };
        let t = static_instance_intersection(
            pos("a.php", 3, 1, 2),
            mk("instance_pos", 1),
            mk("static_pos", 2),
            s("x"),
            MethOrProp::prop,
        );
        t.claim.force();
        assert!(order.borrow().is_empty());
        t.reasons.force();
        assert_eq!(*order.borrow(), vec!["static_pos", "instance_pos"]);
    }

    // typing_fail_uninstantiable_variadic_func.php.exp
    // classname/new_abstract_final.php.exp
    #[test]
    fn test_uninstantiable_class() {
        assert_eq!(
            render(&uninstantiable_class(
                pos("typing_fail_uninstantiable_variadic_func.php", 12, 24, 51),
                s("\\CannotBeInstantiatedWithT"),
                None,
                pos("typing_fail_uninstantiable_variadic_func.php", 11, 22, 46)
            )),
            r#"ERROR: File "typing_fail_uninstantiable_variadic_func.php", line 12, characters 24-51:
`CannotBeInstantiatedWithT` is uninstantiable (Typing[4002])
  File "typing_fail_uninstantiable_variadic_func.php", line 11, characters 22-46:
  Declaration is here
"#
        );
        assert_eq!(
            render(&uninstantiable_class(
                pos("new_abstract_final.php", 5, 18, 20),
                s("\\Foo"),
                Some((
                    pos("new_abstract_final.php", 6, 7, 8),
                    Lazy::from_val(s("an object of type Foo"))
                )),
                pos("new_abstract_final.php", 3, 22, 24),
            )),
            r#"ERROR: File "new_abstract_final.php", line 6, characters 7-8:
This would be an object of type Foo which must be instantiable (Typing[4002])
  File "new_abstract_final.php", line 5, characters 18-20:
  `Foo` is uninstantiable
  File "new_abstract_final.php", line 3, characters 22-24:
  Declaration is here
"#
        );
    }

    // abstract_constant_shape_keys.php.exp
    #[test]
    fn test_abstract_const_usage() {
        assert_eq!(
            render(&abstract_const_usage(
                pos("abstract_constant_shape_keys.php", 6, 37, 47),
                s("\\MagicFactory::MAGIC"),
                pos("abstract_constant_shape_keys.php", 4, 25, 29)
            )),
            r#"ERROR: File "abstract_constant_shape_keys.php", line 6, characters 37-47:
Cannot reference abstract constant `MagicFactory::MAGIC` directly (Typing[4129])
  File "abstract_constant_shape_keys.php", line 4, characters 25-29:
  Declaration is here
"#
        );
    }

    // new_expression_targ_num_mismatch.php.exp
    #[test]
    fn test_type_arity_mismatch() {
        assert_eq!(
            render(&type_arity_mismatch(
                pos("new_expression_targ_num_mismatch.php", 8, 7, 9),
                pos("new_expression_targ_num_mismatch.php", 3, 7, 9),
                2,
                1
            )),
            r#"ERROR: File "new_expression_targ_num_mismatch.php", line 8, characters 7-9:
Wrong number of type arguments (expected 1, got 2) (Typing[4101])
  File "new_expression_targ_num_mismatch.php", line 3, characters 7-9:
  Definition is here
"#
        );
    }

    // typing_fail_cast.php.exp
    #[test]
    fn test_member_not_implemented() {
        assert_eq!(
            render(&member_not_implemented(
                pos("typing_fail_cast.php", 17, 41, 41),
                s("g"),
                pos("typing_fail_cast.php", 13, 19, 19),
                vec![]
            )),
            r#"ERROR: File "typing_fail_cast.php", line 17, characters 41-41:
This interface is not properly implemented (Typing[4054])
  File "typing_fail_cast.php", line 13, characters 19-19:
  Method `g` does not have an implementation
"#
        );
    }

    // construct/parent_construct17.php.exp
    #[test]
    fn test_trait_parent_construct_inconsistent() {
        assert_eq!(
            render(&trait_parent_construct_inconsistent(
                pos("parent_construct17.php", 11, 5, 10),
                pos("parent_construct17.php", 3, 16, 24)
            )),
            r#"ERROR: File "parent_construct17.php", line 11, characters 5-10:
This use of `parent::__construct` requires that the parent class be marked <<__ConsistentConstruct>> (Typing[4451])
  File "parent_construct17.php", line 3, characters 16-24:
  Parent definition is here
"#
        );
    }

    // mixed/mixed_member_access.php.exp
    #[test]
    fn test_top_member() {
        assert_eq!(
            render(&top_member(
                pos("mixed_member_access.php", 4, 9, 11),
                ReadOrWrite::read,
                Lazy::from_val(s("a mixed value")),
                pos("mixed_member_access.php", 3, 23, 27),
                MethodOrProperty::method_,
                s("bar"),
                true,
                Lazy::from_val(vec![]),
            )),
            r#"ERROR: File "mixed_member_access.php", line 4, characters 9-11:
You are trying to access the method `bar` but this is a mixed value. Use a **specific** class or interface name. (Typing[4064])
  File "mixed_member_access.php", line 3, characters 23-27:
  Definition is here
"#
        );
        assert_eq!(
            render(&top_member(
                pos("mixed_member_access.php", 16, 9, 11),
                ReadOrWrite::read,
                Lazy::from_val(s("a nonnull value")),
                pos("mixed_member_access.php", 15, 25, 31),
                MethodOrProperty::method_,
                s("bar"),
                false,
                Lazy::from_val(vec![]),
            )),
            r#"ERROR: File "mixed_member_access.php", line 16, characters 9-11:
You are trying to access the method `bar` but this is a nonnull value. Use a **specific** class or interface name. (Typing[4062])
  File "mixed_member_access.php", line 15, characters 25-31:
  Definition is here
"#
        );
        // The reasons of the type replace the definition, and writes have
        // their own codes.
        let t = top_member(
            pos("a.php", 4, 9, 11),
            ReadOrWrite::write,
            Lazy::from_val(s("a mixed value")),
            pos("a.php", 3, 23, 27),
            MethodOrProperty::property,
            s("bar"),
            true,
            Lazy::from_val(vec![(pos("a.php", 2, 1, 5), s("This can be null"))]),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"a.php\", line 4, characters 9-11:\n\
             You are trying to access the property `bar` but this is a mixed value. Use a **specific** class or interface name. (Typing[4372])\n  \
             File \"a.php\", line 2, characters 1-5:\n  \
             This can be null\n"
        );
        let t = top_member(
            pos("a.php", 4, 9, 11),
            ReadOrWrite::write,
            Lazy::from_val(s("a mixed value")),
            pos("a.php", 3, 23, 27),
            MethodOrProperty::property,
            s("bar"),
            false,
            Lazy::from_val(vec![]),
        );
        assert_eq!(t.code, ErrorCode::NonObjectMemberWrite);
    }

    // tconst_unsoundness.php.constraint_method_call.exp
    #[test]
    fn test_unresolved_tyvar_projection() {
        assert_eq!(
            render(&unresolved_tyvar_projection(
                pos("tconst_unsoundness.php", 20, 10, 10),
                pos("tconst_unsoundness.php", 14, 68, 68),
                s("T")
            )),
            r#"ERROR: File "tconst_unsoundness.php", line 20, characters 10-10:
Can't access a type constant T from an unresolved type (Typing[4436])
  File "tconst_unsoundness.php", line 14, characters 68-68:
  Access happens here
  File "tconst_unsoundness.php", line 20, characters 10-10:
  Disambiguate the types using explicit type annotations here.
"#
        );
    }

    // class_constant_cycle.php.exp
    #[test]
    fn test_cyclic_class_constant() {
        assert_eq!(
            render(&cyclic_class_constant(
                pos("class_constant_cycle.php", 5, 13, 13),
                s("\\C0"),
                s("A")
            )),
            r#"ERROR: File "class_constant_cycle.php", line 5, characters 13-13:
Cannot declare self-referencing constant A in C0 (Typing[4424])
"#
        );
    }

    // class_meth12.php.exp
    #[test]
    fn test_inout_annotation_missing() {
        assert_eq!(
            render(&inout_annotation_missing(
                pos("class_meth12.php", 16, 14, 16),
                pos("class_meth12.php", 7, 51, 52)
            )),
            r#"ERROR: File "class_meth12.php", line 16, characters 14-16:
This argument should be annotated with `inout` (Typing[4182])
  File "class_meth12.php", line 7, characters 51-52:
  Because this is an `inout` parameter
"#
        );
        // The quickfix inserts `inout ` at the start of the argument.
        let t = inout_annotation_missing(
            pos("class_meth12.php", 16, 14, 16),
            pos("class_meth12.php", 7, 51, 52),
        );
        assert_eq!(t.quickfixes.len(), 1);
        assert_eq!(t.quickfixes[0].title, "Insert `inout` annotation");
        match &t.quickfixes[0].edits {
            Edits::Eager(edits) => {
                assert_eq!(edits.len(), 1);
                assert_eq!(edits[0].0, "inout ");
                assert_eq!(edits[0].1.info_raw(), (13, 13));
            }
            edits => panic!("unexpected edits {:?}", edits),
        }
    }

    // shape/shape_put_no_inout.php.exp
    #[test]
    fn test_inout_annotation_unexpected() {
        assert_eq!(
            render(&inout_annotation_unexpected(
                pos("shape_put_no_inout.php", 4, 22, 33),
                pos("Shapes.hhi", 109, 18, 23),
                false,
                pos("shape_put_no_inout.php", 4, 22, 27)
            )),
            r#"ERROR: File "shape_put_no_inout.php", line 4, characters 22-33:
Unexpected `inout` annotation for argument (Typing[4183])
  File "Shapes.hhi", line 109, characters 18-23:
  This is a normal parameter (does not have `inout`)
"#
        );
        let t = inout_annotation_unexpected(
            pos("a.php", 4, 22, 33),
            pos("a.php", 1, 18, 23),
            true,
            pos("a.php", 4, 22, 27),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"a.php\", line 4, characters 22-33:\n\
             Unexpected `inout` annotation for argument (Typing[4183])\n  \
             File \"a.php\", line 1, characters 18-23:\n  \
             A variadic parameter can never be `inout`\n"
        );
        assert_eq!(
            t.quickfixes,
            vec![Quickfix {
                title: s("Remove `inout` annotation"),
                edits: Edits::Eager(vec![(s(""), pos("a.php", 4, 22, 27))]),
                hint_styles: vec![],
            }]
        );
    }

    // inout/bad_inout_use_arg19.php.exp
    #[test]
    fn test_inout_argument_bad_type() {
        assert_eq!(
            render(&inout_argument_bad_type(
                pos("bad_inout_use_arg19.php", 15, 11, 15),
                Lazy::from_val(vec![m(
                    pos("bad_inout_use_arg19.php", 10, 3, 81),
                    "This is an object of type Pair<int, int> or an object of type vec<int> because of this statement",
                )])
            )),
            r#"ERROR: File "bad_inout_use_arg19.php", line 15, characters 11-15:
Expected argument marked `inout` to be contained in a local or a value-typed container (e.g. vec, dict, keyset, array). To use `inout` here, assign to/from a temporary local variable. (Typing[4208])
  File "bad_inout_use_arg19.php", line 10, characters 3-81:
  This is an object of type Pair<int, int> or an object of type vec<int> because of this statement
"#
        );
    }

    // meth_caller/meth_caller_named.php.exp
    // readonly/meth_caller.php.exp
    #[test]
    fn test_invalid_meth_caller() {
        assert_eq!(
            render(&invalid_meth_caller_named_parameter(
                pos("meth_caller_named.php", 19, 3, 52),
                pos("meth_caller_named.php", 5, 38, 39)
            )),
            r#"ERROR: File "meth_caller_named.php", line 19, characters 3-52:
`meth_caller` does not support methods with named parameters (Typing[4527])
  File "meth_caller_named.php", line 5, characters 38-39:
  This parameter is named
"#
        );
        assert_eq!(
            render(&invalid_meth_caller_readonly_return(
                pos("meth_caller.php", 12, 8, 48),
                pos("meth_caller.php", 6, 19, 34)
            )),
            r#"ERROR: File "meth_caller.php", line 12, characters 8-48:
`meth_caller` does not support methods that return `readonly` objects (Typing[4464])
  File "meth_caller.php", line 6, characters 19-34:
  This is why I think this method returns a `readonly` object
"#
        );
    }

    // first_class_polymorphism/this_param_callbacks.php.exp
    #[test]
    fn test_this_as_function_pointer_param() {
        assert_eq!(
            render(&this_as_function_pointer_param(
                pos("this_param_callbacks.php", 45, 14, 26),
                pos("this_param_callbacks.php", 17, 24, 25)
            )),
            r#"ERROR: File "this_param_callbacks.php", line 45, characters 14-26:
Cannot take a pointer to this method because a value of type `this` can be obtained from two or more of its parameters (counting the implicit receiver of an instance method), so the function pointer could be used to relate two unrelated subtypes of `this` (Typing[4517])
  File "this_param_callbacks.php", line 17, characters 24-25:
  a value of type `this` can be obtained from this parameter
"#
        );
    }

    // using/using_bad_new.php.exp
    // using/using_bad_return_disposable.php.exp
    // using/using_bad_hints.php.exp
    #[test]
    fn test_disposable() {
        assert_eq!(
            render(&invalid_new_disposable(pos(
                "using_bad_new.php",
                14,
                12,
                17
            ))),
            r#"ERROR: File "using_bad_new.php", line 14, characters 12-17:
Disposable objects may only be created in a `using` statement or `return` from function marked `<<__ReturnDisposable>>` (Typing[4187])
"#
        );
        assert_eq!(
            render(&invalid_return_disposable(pos(
                "using_bad_return_disposable.php",
                14,
                12,
                16
            ))),
            r#"ERROR: File "using_bad_return_disposable.php", line 14, characters 12-16:
Return expression must be new disposable in function marked `<<__ReturnDisposable>>` (Typing[4205])
"#
        );
        assert_eq!(
            render(&invalid_disposable_hint(
                pos("using_bad_hints.php", 13, 22, 23),
                s("Handle")
            )),
            r#"ERROR: File "using_bad_hints.php", line 13, characters 22-23:
Parameter with type `Handle` must not implement `IDisposable` or `IAsyncDisposable`. Please use `<<__AcceptDisposable>>` attribute or create disposable object with `using` statement instead. (Typing[4190])
"#
        );
        assert_eq!(
            render(&invalid_disposable_return_hint(
                pos("using_bad_hints.php", 20, 26, 31),
                s("Handle")
            )),
            r#"ERROR: File "using_bad_hints.php", line 20, characters 26-31:
Return type `Handle` must not implement `IDisposable` or `IAsyncDisposable`. Please add `<<__ReturnDisposable>>` attribute. (Typing[4206])
"#
        );
    }

    // extends/bad/class_extends_trait_bad.php.exp
    // extends/bad/abstract_class_extends_interface_bad.php.exp
    // extends/bad/interface_extends_abstract_class_bad.php.exp
    #[test]
    fn test_wrong_extend_kind() {
        assert_eq!(
            render(&wrong_extend_kind(
                pos("class_extends_trait_bad.php", 13, 7, 7),
                ClassishKind::Cclass(Abstraction::Concrete),
                s("\\B"),
                pos("class_extends_trait_bad.php", 13, 17, 17),
                ClassishKind::Ctrait,
                s("\\A"),
            )),
            r#"ERROR: File "class_extends_trait_bad.php", line 13, characters 7-7:
Classes can only extend other classes. Did you mean to add `use A;` within the body of `B`? (Typing[4115])
  File "class_extends_trait_bad.php", line 13, characters 17-17:
  This is a trait.
"#
        );
        assert_eq!(
            render(&wrong_extend_kind(
                pos("abstract_class_extends_interface_bad.php", 13, 16, 16),
                ClassishKind::Cclass(Abstraction::Abstract),
                s("\\B"),
                pos("abstract_class_extends_interface_bad.php", 13, 26, 26),
                ClassishKind::Cinterface,
                s("\\A"),
            )),
            r#"ERROR: File "abstract_class_extends_interface_bad.php", line 13, characters 16-16:
Classes can only extend other classes. Did you mean `implements A`? (Typing[4115])
  File "abstract_class_extends_interface_bad.php", line 13, characters 26-26:
  This is an interface.
"#
        );
        assert_eq!(
            render(&wrong_extend_kind(
                pos("interface_extends_abstract_class_bad.php", 13, 11, 11),
                ClassishKind::Cinterface,
                s("\\B"),
                pos("interface_extends_abstract_class_bad.php", 13, 21, 21),
                ClassishKind::Cclass(Abstraction::Abstract),
                s("\\A"),
            )),
            r#"ERROR: File "interface_extends_abstract_class_bad.php", line 13, characters 11-11:
Interfaces can only extend other interfaces. (Typing[4115])
  File "interface_extends_abstract_class_bad.php", line 13, characters 21-21:
  This is an abstract class.
"#
        );
    }

    // modules/module_level_traits_hierarchy_1b.bad.php.exp
    #[test]
    fn test_wrong_use_kind() {
        assert_eq!(
            render(&wrong_use_kind(
                pos("module_level_traits_hierarchy_1b.bad.php--A.php", 12, 7, 8),
                "\\T2",
                pos("module_level_traits_hierarchy_1b.bad.php--A.php", 13, 7, 8),
                "\\T1"
            )),
            r#"ERROR: File "module_level_traits_hierarchy_1b.bad.php--A.php", line 12, characters 7-8:
Module level trait T2 cannot use internal traits. (Typing[4477])
  File "module_level_traits_hierarchy_1b.bad.php--A.php", line 13, characters 7-8:
  Trait T1 is internal.
"#
        );
    }

    // cyclic_require.php.exp
    // trait_reuse/trait_reuse_cyclic.php.exp
    #[test]
    fn test_cyclic_class_def() {
        assert_eq!(
            render(&cyclic_class_def(
                pos("cyclic_require.php", 5, 22, 22),
                [s("\\I"), s("\\J")].into_iter().collect()
            )),
            r#"ERROR: File "cyclic_require.php", line 5, characters 22-22:
Cyclic class definition : `J` `I`  (Typing[4013])
"#
        );
        assert_eq!(
            render(&cyclic_class_def(
                pos("trait_reuse_cyclic.php", 11, 7, 17),
                [
                    s("\\MyParent"),
                    s("\\ReusedTrait"),
                    s("\\BadClass"),
                    s("\\OtherTrait"),
                ]
                .into_iter()
                .collect(),
            )),
            r#"ERROR: File "trait_reuse_cyclic.php", line 11, characters 7-17:
Cyclic class definition : `ReusedTrait` `OtherTrait` `MyParent` `BadClass`  (Typing[4013])
"#
        );
    }

    // override/override_final5.php.exp
    #[test]
    fn test_trait_reuse_with_final_method() {
        assert_eq!(
            render(&trait_reuse_with_final_method(
                pos("override_final5.php", 21, 7, 7),
                s("\\T"),
                s("\\ParentClass"),
                Lazy::from_val(vec![
                    m(
                        pos("override_final5.php", 16, 7, 17),
                        "`ParentClass` is defined here"
                    ),
                    m(
                        pos("override_final5.php", 17, 7, 7),
                        "`ParentClass` uses `T`"
                    ),
                    m(
                        pos("override_final5.php", 13, 32, 32),
                        "`T` has a final method `f`"
                    ),
                ]),
            )),
            r#"ERROR: File "override_final5.php", line 21, characters 7-7:
Traits with final methods cannot be reused, and `T` is already used by `ParentClass`. (Typing[4186])
  File "override_final5.php", line 16, characters 7-17:
  `ParentClass` is defined here
  File "override_final5.php", line 17, characters 7-7:
  `ParentClass` uses `T`
  File "override_final5.php", line 13, characters 32-32:
  `T` has a final method `f`
"#
        );
    }

    // trait_use/use_trait_multiple_times_fail.php.exp
    #[test]
    fn test_trait_reuse_inside_class() {
        assert_eq!(
            render(&trait_reuse_inside_class(
                pos("use_trait_multiple_times_fail.php", 6, 7, 7),
                s("\\C"),
                s("\\T"),
                vec![
                    pos("use_trait_multiple_times_fail.php", 8, 7, 7),
                    pos("use_trait_multiple_times_fail.php", 9, 7, 7),
                    pos("use_trait_multiple_times_fail.php", 10, 7, 7)
                ]
            )),
            r#"ERROR: File "use_trait_multiple_times_fail.php", line 6, characters 7-7:
Class `C` uses trait `T` multiple times (Typing[4365])
  File "use_trait_multiple_times_fail.php", line 8, characters 7-7:
  used here
  File "use_trait_multiple_times_fail.php", line 9, characters 7-7:
  used here
  File "use_trait_multiple_times_fail.php", line 10, characters 7-7:
  used here
"#
        );
    }

    // invalid_as_nothing.php.exp
    #[test]
    fn test_invalid_is_as_expression_hint() {
        assert_eq!(
            render(&invalid_is_as_expression_hint(
                pos("invalid_as_nothing.php", 5, 9, 15),
                IsOrAs::as_,
                Lazy::from_val(vec![m(
                    pos("invalid_as_nothing.php", 5, 9, 15),
                    "the `nothing` type"
                )])
            )),
            r#"ERROR: File "invalid_as_nothing.php", line 5, characters 9-15:
Invalid `as` expression hint (Typing[4195])
  File "invalid_as_nothing.php", line 5, characters 9-15:
  The `as` operator cannot be used with the `nothing` type
"#
        );
        let t = invalid_is_as_expression_hint(
            pos("a.php", 5, 9, 15),
            IsOrAs::is,
            Lazy::from_val(vec![m(pos("a.php", 5, 9, 15), "the `nothing` type")]),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"a.php\", line 5, characters 9-15:\n\
             Invalid `is` expression hint (Typing[4195])\n  \
             File \"a.php\", line 5, characters 9-15:\n  \
             The `is` operator cannot be used with the `nothing` type\n"
        );
    }

    // trait_not_enforceable.php.exp
    #[test]
    fn test_invalid_enforceable_type() {
        assert_eq!(
            render(&invalid_enforceable_type(
                pos("trait_not_enforceable.php", 12, 7, 14),
                Lazy::from_val(vec![m(
                    pos("trait_not_enforceable.php", 12, 7, 14),
                    "a trait name"
                )]),
                ConstantOrParam::param,
                pos("trait_not_enforceable.php", 7, 38, 38),
                s("T"),
            )),
            r#"ERROR: File "trait_not_enforceable.php", line 12, characters 7-14:
Invalid type (Typing[4302])
  File "trait_not_enforceable.php", line 7, characters 38-38:
  Type parameter `T` was declared `__Enforceable` here
  File "trait_not_enforceable.php", line 12, characters 7-14:
  This type is not enforceable because it has a trait name
"#
        );
    }

    // reified_generics/reifiable3.php.exp
    #[test]
    fn test_reifiable_attr() {
        assert_eq!(
            render(&reifiable_attr(
                pos("reifiable3.php", 16, 5, 15),
                ReifiableAttrKind::ty,
                pos("reifiable3.php", 17, 14, 15),
                Lazy::from_val(vec![m(
                    pos("reifiable3.php", 14, 23, 24),
                    "an abstract type constant without the __Reifiable attribute",
                )]),
            )),
            r#"ERROR: File "reifiable3.php", line 17, characters 14-15:
Invalid type (Typing[4322])
  File "reifiable3.php", line 16, characters 5-15:
  This type constant has the `__Reifiable` attribute
  File "reifiable3.php", line 14, characters 23-24:
  It cannot contain an abstract type constant without the __Reifiable attribute
"#
        );
    }

    // reified_generics/newable_targ_basic.php.exp
    #[test]
    fn test_invalid_newable_type_argument() {
        assert_eq!(
            render(&invalid_newable_type_argument(
                pos("newable_targ_basic.php", 14, 5, 6),
                pos("newable_targ_basic.php", 11, 32, 32),
                s("T")
            )),
            r#"ERROR: File "newable_targ_basic.php", line 14, characters 5-6:
A newable type argument must be a concrete class or a newable type parameter. (Typing[4307])
  File "newable_targ_basic.php", line 11, characters 32-32:
  Type parameter `T` was declared `__Newable` here
"#
        );
    }

    // reified_generics/newable_tparams.php.exp
    #[test]
    fn test_invalid_newable_type_param_constraints() {
        assert_eq!(
            render(&invalid_newable_type_param_constraints(
                (pos("newable_tparams.php", 16, 23, 24), s("Tc")),
                vec![s("\\C"), s("\\E")]
            )),
            r#"ERROR: File "newable_tparams.php", line 16, characters 23-24:
The type parameter `Tc` has the `<<__Newable>>` attribute. Newable type parameters must be constrained with `as`, and exactly one of those constraints must be a valid newable class. The class must either be final, or it must have the `<<__ConsistentConstruct>>` attribute or extend a class that has it. The constraints C, E are valid newable classes (Typing[4308])
"#
        );
        assert_eq!(
            render(&invalid_newable_type_param_constraints(
                (pos("newable_tparams.php", 19, 25, 26), s("Tm")),
                vec![]
            )),
            r#"ERROR: File "newable_tparams.php", line 19, characters 25-26:
The type parameter `Tm` has the `<<__Newable>>` attribute. Newable type parameters must be constrained with `as`, and exactly one of those constraints must be a valid newable class. The class must either be final, or it must have the `<<__ConsistentConstruct>>` attribute or extend a class that has it. No constraints are valid newable classes (Typing[4308])
"#
        );
    }

    // override/override_attr_09.php.exp
    #[test]
    fn test_override_per_trait() {
        assert_eq!(
            render(&override_per_trait(
                (pos("override_attr_09.php", 17, 7, 8), s("\\C1")),
                s("foo"),
                s("\\ATr"),
                pos("override_attr_09.php", 14, 26, 28)
            )),
            r#"ERROR: File "override_attr_09.php", line 17, characters 7-8:
`ATr::foo` is marked `__Override` but `C1` does not define or inherit a `foo` method. (Typing[4071])
  File "override_attr_09.php", line 14, characters 26-28:
  Declaration of `foo` is here
"#
        );
    }

    // incomplete_method_override.php.exp
    #[test]
    fn test_should_not_be_override() {
        assert_eq!(
            render(&should_not_be_override(
                pos("incomplete_method_override.php", 9, 19, 26),
                s("\\FooChild"),
                s("vAUTO332")
            )),
            r#"ERROR: File "incomplete_method_override.php", line 9, characters 19-26:
`FooChild` has no parent class with a method `vAUTO332` to override (Typing[4087])
"#
        );
    }

    // needs_concrete/needs_concrete_in_final_class_1.php.exp
    // needs_concrete/needs_concrete_on_nonstatic_method_1.php.exp
    // needs_concrete/needs_concrete_on_constructor_1.php.exp
    #[test]
    fn test_needs_concrete_attribute() {
        assert_eq!(
            render(&needs_concrete_in_final_class(
                pos("needs_concrete_in_final_class_1.php", 5, 26, 27),
                s("\\Finale"),
                s("m1")
            )),
            r#"ERROR: File "needs_concrete_in_final_class_1.php", line 5, characters 26-27:
The `__NeedsConcrete` attribute is not allowed on `Finale::m1` because `Finale` is a final class. The `__NeedsConcrete` attribute is for safe inheritance so should only be used in non-final classes. (Typing[4505])
"#
        );
        assert_eq!(
            render(&needs_concrete_on_instance_method(
                pos("needs_concrete_on_nonstatic_method_1.php", 5, 19, 20),
                s("\\A"),
                s("m1")
            )),
            r#"ERROR: File "needs_concrete_on_nonstatic_method_1.php", line 5, characters 19-20:
The `__NeedsConcrete` attribute is not allowed on `A::m1` (a nonstatic method). The `__NeedsConcrete` attribute is only meaningful on static methods. (Typing[4506])
"#
        );
        assert_eq!(
            render(&needs_concrete_on_constructor(
                pos("needs_concrete_on_constructor_1.php", 5, 19, 29),
                "\\A"
            )),
            r#"ERROR: File "needs_concrete_on_constructor_1.php", line 5, characters 19-29:
The `__NeedsConcrete` attribute is not allowed on a constructor. The `__NeedsConcrete` attribute is only meaningful on static methods. (Typing[4507])
"#
        );
    }

    // needs_concrete/needs_concrete_fine_grained/needs_concrete_fine_grained.php.exp
    #[test]
    fn test_call_needs_concrete() {
        assert_eq!(
            render(&call_needs_concrete(
                pos("needs_concrete_fine_grained.php", 23, 11, 22),
                "\\Child",
                "concreteOnly",
                pos("needs_concrete_fine_grained.php", 12, 26, 37),
                CallNeedsConcreteVia::Self_
            )),
            r#"ERROR: File "needs_concrete_fine_grained.php", line 23, characters 11-22:
Dangerous call to `Child::concreteOnly` (a `<<__NeedsConcrete>>` method) via `self`. It requires `static` to refer to a concrete class, but `self` sets `static` to a class that may not be concrete. (Typing[4528])
  File "needs_concrete_fine_grained.php", line 12, characters 26-37:
  Declaration is here
"#
        );
        assert_eq!(
            render(&call_needs_concrete(
                pos("needs_concrete_fine_grained.php", 24, 13, 24),
                "\\Base",
                "concreteOnly",
                pos("needs_concrete_fine_grained.php", 12, 26, 37),
                CallNeedsConcreteVia::Parent
            )),
            r#"ERROR: File "needs_concrete_fine_grained.php", line 24, characters 13-24:
Dangerous call to `Base::concreteOnly` (a `<<__NeedsConcrete>>` method) via `parent`. It requires `static` to refer to a concrete class, but `parent` sets `static` to a class that may not be concrete. (Typing[4528])
  File "needs_concrete_fine_grained.php", line 12, characters 26-37:
  Declaration is here
"#
        );
        // The other two have the text of the warnings of
        // needs_concrete/needs_concrete_fine_grained/needs_concrete_fine_grained.php.exp
        // and needs_concrete/needs_concrete_abstract_concrete_2.php.exp.
        let t = call_needs_concrete(
            pos("a.php", 4, 9, 20),
            "\\Base",
            "concreteOnly",
            pos("a.php", 12, 26, 37),
            CallNeedsConcreteVia::Id,
        );
        assert_eq!(
            t.claim.force().1,
            "Dangerous call to `Base::concreteOnly` (a `<<__NeedsConcrete>>` method). It is expecting a concrete receiver but `Base` is not concrete."
        );
        let t = call_needs_concrete(
            pos("a.php", 21, 13, 14),
            "\\C2",
            "nc",
            pos("a.php", 7, 26, 27),
            CallNeedsConcreteVia::Static,
        );
        assert_eq!(
            t.claim.force().1,
            "Dangerous call to `C2::nc` (a `<<__NeedsConcrete>>` method) via `static`. It requires `static` to refer to a concrete class but `static` may not be concrete."
        );
    }

    // needs_concrete/needs_concrete_fine_grained/needs_concrete_fine_grained.php.exp
    #[test]
    fn test_uninstantiable_class_via_static() {
        assert_eq!(
            render(&uninstantiable_class_via_static(
                pos("needs_concrete_fine_grained.php", 16, 9, 14),
                "\\Base",
                pos("needs_concrete_fine_grained.php", 8, 16, 19),
                None
            )),
            r#"ERROR: File "needs_concrete_fine_grained.php", line 16, characters 9-14:
Dangerous instantiation via `static`: `static` might refer to a non-concrete class here. Consider adding the `__NeedsConcrete` attribute to the containing method. (Typing[4530])
  File "needs_concrete_fine_grained.php", line 8, characters 16-19:
  Declaration is here
"#
        );
        let t = uninstantiable_class_via_static(
            pos("a.php", 16, 9, 14),
            "\\Base",
            pos("a.php", 8, 16, 19),
            Some(pos("a.php", 15, 26, 28)),
        );
        assert_eq!(
            t.quickfixes,
            vec![Quickfix {
                title: s("Add __NeedsConcrete attribute"),
                edits: Edits::AddFunctionAttribute {
                    function_pos: pos("a.php", 15, 26, 28),
                    attribute_name: s("__NeedsConcrete"),
                },
                hint_styles: vec![],
            }]
        );
        // The text of the warning of needs_concrete/needs_concrete_non_meth_1.php.exp.
        let t = abstract_access_via_static(
            pos("a.php", 11, 13, 15),
            s("\\A"),
            s("abs"),
            pos("a.php", 7, 35, 37),
            Some(pos("a.php", 10, 26, 28)),
        );
        assert_eq!(
            t.claim.force().1,
            "Dangerous access of abstract member `A::abs`; it may be abstract and `static` might refer to an abstract class here. Consider adding the `__NeedsConcrete` attribute to the containing method."
        );
        assert_eq!(t.quickfixes.len(), 1);
        assert_eq!(t.quickfixes[0].title, "Add __NeedsConcrete attribute");
    }

    // needs_concrete/needs_concrete_override_check_error/needs_concrete_override_check_1.php.exp
    #[test]
    fn test_needs_concrete_override() {
        assert_eq!(
            render(&needs_concrete_override(
                pos("needs_concrete_override_check_1.php", 9, 26, 28),
                pos("needs_concrete_override_check_1.php", 9, 26, 28),
                pos("needs_concrete_override_check_1.php", 4, 26, 28),
                None
            )),
            r#"ERROR: File "needs_concrete_override_check_1.php", line 9, characters 26-28:
This method is declared as `__NeedsConcrete` but overrides a non-`__NeedsConcrete` method. Please add `__NeedsConcrete` to the overridden method or remove it from the current method. (The `__NeedsConcrete` attribute indicates that a method requires `static` to point to a concrete class) (Typing[4526])
  File "needs_concrete_override_check_1.php", line 9, characters 26-28:
  It is unsafe to declare this method as `__NeedsConcrete`, since it overrides a non-`__NeedsConcrete` method
  File "needs_concrete_override_check_1.php", line 4, characters 26-28:
  Previously defined here
"#
        );
        // The text of the warning of
        // needs_concrete/needs_concrete_override_check_true/needs_concrete_override_traits_1.php.exp.
        let t = needs_concrete_override(
            pos("a.php", 12, 16, 17),
            pos("a.php", 9, 26, 27),
            pos("a.php", 4, 26, 27),
            Some("m1"),
        );
        assert_eq!(
            t.claim.force().1,
            "Method `m1` is declared as `__NeedsConcrete` but overrides a non-`__NeedsConcrete` method. Please add `__NeedsConcrete` to the overridden method or remove it from the current method. (The `__NeedsConcrete` attribute indicates that a method requires `static` to point to a concrete class)"
        );
    }

    // enum_eq_bad.php.exp
    // unresolved_compare.php.exp
    #[test]
    fn test_incompatible_types() {
        assert_eq!(
            render(&eq_incompatible_types(
                pos("enum_eq_bad.php", 17, 7, 15),
                vec![m(
                    pos("enum_eq_bad.php", 4, 9, 11),
                    "This is a value of type E"
                )],
                vec![m(
                    pos("enum_eq_bad.php", 9, 9, 11),
                    "This is a value of type F"
                )],
            )),
            r#"ERROR: File "enum_eq_bad.php", line 17, characters 7-15:
This equality test has incompatible types (Typing[4157])
  File "enum_eq_bad.php", line 4, characters 9-11:
  This is a value of type E
  File "enum_eq_bad.php", line 9, characters 9-11:
  This is a value of type F
"#
        );
        assert_eq!(
            render(&comparison_invalid_types(
                pos("unresolved_compare.php", 13, 10, 16),
                vec![m(
                    pos("unresolved_compare.php", 11, 15, 15),
                    "This is an object of exactly the class A"
                )],
                vec![m(
                    pos("unresolved_compare.php", 3, 23, 23),
                    "  via this generic `T`"
                )],
            )),
            r#"ERROR: File "unresolved_compare.php", line 13, characters 10-16:
This comparison has invalid types.  Only comparisons in which both arguments are strings, nums, DateTime, or DateTimeImmutable are allowed (Typing[4240])
  File "unresolved_compare.php", line 11, characters 15-15:
  This is an object of exactly the class A
  File "unresolved_compare.php", line 3, characters 23-23:
    via this generic `T`
"#
        );
    }

    // deprecated_method.php.exp
    #[test]
    fn test_deprecated_use() {
        assert_eq!(
            render(&deprecated_use(
                pos("deprecated_method.php", 9, 6, 8),
                Some(Some(pos("deprecated_method.php", 5, 26, 28))),
                s("The method foo is deprecated: use bar() instead")
            )),
            r#"ERROR: File "deprecated_method.php", line 9, characters 6-8:
The method foo is deprecated: use bar() instead (Typing[4128])
  File "deprecated_method.php", line 5, characters 26-28:
  Definition is here
"#
        );
        // Without a definition (the default of the optional argument, or
        // `None` given for it) there is no reason.
        for pos_def in [None, Some(None)] {
            let t = deprecated_use(pos("a.php", 9, 6, 8), pos_def, s("Deprecated"));
            assert_eq!(
                render(&t),
                "ERROR: File \"a.php\", line 9, characters 6-8:\nDeprecated (Typing[4128])\n"
            );
        }
    }

    // construct/promoted_prop_redeclaration/parent_construct22.php.exp
    #[test]
    fn test_redeclaring_promoted_property() {
        assert_eq!(
            render(&redeclaring_promoted_property(
                pos("parent_construct22.php", 15, 55, 61),
                s("config"),
                pos("parent_construct22.php", 8, 41, 47),
                s("\\EntFooBase")
            )),
            r#"ERROR: File "parent_construct22.php", line 15, characters 55-61:
Cannot redeclare the promoted property `config` here because it is already declared by an ancestor. Remove the visibility modifier from this constructor parameter. (Typing[4524])
  File "parent_construct22.php", line 8, characters 41-47:
  `config` was previously declared in `EntFooBase`
"#
        );
    }

    // classname/primitive.php.exp
    #[test]
    fn test_invalid_classname() {
        assert_eq!(
            render(&invalid_classname(pos("primitive.php", 3, 22, 24))),
            r#"ERROR: File "primitive.php", line 3, characters 22-24:
Not a valid class name (Typing[4148])
"#
        );
    }

    // type_structure/classname_tyvar.php.exp
    // type_structure/type_structure10.php.exp
    #[test]
    fn test_illegal_type_structure() {
        assert_eq!(
            render(&illegal_type_structure(
                pos("classname_tyvar.php", 15, 19, 45),
                s("The type constant does not resolve to a classish type"),
                s("\\HH\\type_structure_classname"),
            )),
            r#"ERROR: File "classname_tyvar.php", line 15, characters 19-45:
The two arguments to `HH\type_structure_classname()` must be:
 - first: `ValidClassname::class` or an object of that class
 - second: a single-quoted string literal containing the name of a type constant of that class
The type constant does not resolve to a classish type (Typing[4150])
"#
        );
        assert_eq!(
            render(&illegal_typeconst_direct_access(pos(
                "type_structure10.php",
                8,
                11,
                11
            ))),
            r#"ERROR: File "type_structure10.php", line 8, characters 11-11:
Type constants cannot be directly accessed. Use `type_structure(ValidClassname::class, 'TypeConstName')` instead (Typing[4150])
"#
        );
    }

    // variadic_parameters.php.exp
    #[test]
    fn test_wrong_expression_kind_attribute() {
        assert_eq!(
            render(&wrong_expression_kind_attribute(
                s("a parameter"),
                pos("variadic_parameters.php", 8, 5, 23),
                s("\\AttributeForTesting"),
                pos("variadic_parameters.php", 3, 7, 25),
                s("\\AttributeForTesting"),
                s("\\HH\\ParameterAttribute"),
            )),
            r#"ERROR: File "variadic_parameters.php", line 8, characters 5-23:
The `AttributeForTesting` attribute cannot be used on a parameter. (Typing[4231])
  File "variadic_parameters.php", line 3, characters 7-25:
  The attribute's class is defined here. To be available for use on a parameter, the `AttributeForTesting` class must implement `HH\ParameterAttribute`.
"#
        );
    }

    // visibilities/method_shadow.php.constraint_method_call.exp
    #[test]
    fn test_ambiguous_object_access() {
        assert_eq!(
            render(&ambiguous_object_access(
                pos("method_shadow.php", 6, 16, 18),
                s("get"),
                pos("method_shadow.php", 8, 20, 22),
                s("public"),
                pos("method_shadow.php", 17, 19, 21),
                s("\\A"),
                s("\\B"),
            )),
            r#"ERROR: File "method_shadow.php", line 6, characters 16-18:
This object access to `get` is ambiguous (Typing[4256])
  File "method_shadow.php", line 8, characters 20-22:
  You will access the private instance declared in `A`
  File "method_shadow.php", line 17, characters 19-21:
  Instead of the public instance declared in `B`
"#
        );
    }

    // generic_capture_bad.php.exp
    #[test]
    fn test_redundant_generic() {
        assert_eq!(
            render(&redundant_generic(
                pos("generic_capture_bad.php", 5, 33, 34),
                CoOrContra::Co,
                s(""),
                s("nothing")
            )),
            r#"ERROR: File "generic_capture_bad.php", line 5, characters 33-34:
This generic parameter is redundant because it only appears in a covariant (output) position. Consider replacing uses of generic parameter with `nothing` or specifying `<<__Explicit>>` on the generic parameter (Typing[4366])
"#
        );
        let t = redundant_generic(
            pos("a.php", 5, 33, 34),
            CoOrContra::Contra,
            s(""),
            s("mixed"),
        );
        assert_eq!(
            t.claim.force().1,
            "This generic parameter is redundant because it only appears in a contravariant (input) position. Consider replacing uses of generic parameter with `mixed` or specifying `<<__Explicit>>` on the generic parameter"
        );
    }

    // meth_caller/trait.php.exp
    #[test]
    fn test_meth_caller_trait() {
        assert_eq!(
            render(&meth_caller_trait(
                pos("trait.php", 8, 15, 21),
                s("\\MyTrait")
            )),
            r#"ERROR: File "trait.php", line 8, characters 15-21:
`MyTrait` is a trait which cannot be used with `meth_caller`. Use a class instead. (Typing[4375])
"#
        );
    }

    // multiple_instantiation_interface/insts1.php.exp
    #[test]
    fn test_duplicate_interface() {
        assert_eq!(
            render(&duplicate_interface(
                pos("insts1.php", 12, 21, 26),
                s("\\J"),
                vec![pos("insts1.php", 12, 29, 29)]
            )),
            r#"ERROR: File "insts1.php", line 12, characters 21-26:
Interface `J` is used more than once in this declaration. (Typing[4377])
  File "insts1.php", line 12, characters 29-29:
  Here is another occurrence
"#
        );
    }

    // enum/duplicate_values/enum_dup_intish_arraykey.php.exp
    #[test]
    fn test_enum_duplicate_value() {
        assert_eq!(
            render(&enum_duplicate_value(
                pos("enum_dup_intish_arraykey.php", 22, 6, 25),
                s("4611686018427387904"),
                s("HEX_INT"),
                pos("enum_dup_intish_arraykey.php", 23, 3, 9),
                s("DECIMAL_STRING"),
                pos("enum_dup_intish_arraykey.php", 24, 3, 16),
            )),
            r#"ERROR: File "enum_dup_intish_arraykey.php", line 22, characters 6-25:
This enum has members `DECIMAL_STRING` and `HEX_INT` with the same value `4611686018427387904`. Duplicate enum values are not allowed. (Typing[4519])
  File "enum_dup_intish_arraykey.php", line 24, characters 3-16:
  `DECIMAL_STRING` is declared here
  File "enum_dup_intish_arraykey.php", line 23, characters 3-9:
  `HEX_INT` is declared here
"#
        );
    }

    // enum/duplicate_values/enum_uncheckable_values.php.exp
    // enum/duplicate_values/enum_alias_exempt.php.exp
    #[test]
    fn test_enum_uncheckable_value() {
        assert_eq!(
            render(&enum_uncheckable_value(
                pos("enum_uncheckable_values.php", 45, 6, 24),
                s("\\EnumManyUncheckable"),
                Lazy::from_val((
                    vec![
                        (
                            pos("enum_uncheckable_values.php", 46, 3, 4),
                            s("`R1` cannot be checked")
                        ),
                        (
                            pos("enum_uncheckable_values.php", 47, 3, 4),
                            s("`R2` cannot be checked")
                        ),
                        (
                            pos("enum_uncheckable_values.php", 48, 3, 4),
                            s("`R3` cannot be checked")
                        ),
                        (
                            pos("enum_uncheckable_values.php", 49, 3, 4),
                            s("`R4` cannot be checked")
                        ),
                        (
                            pos("enum_uncheckable_values.php", 50, 3, 4),
                            s("`R5` cannot be checked")
                        ),
                    ],
                    2,
                )),
            )),
            r#"ERROR: File "enum_uncheckable_values.php", line 45, characters 6-24:
`EnumManyUncheckable` cannot be statically checked for duplicate values. Member values must be int or string literals, `nameof`, or `::class` to be checked; references to global constants (or other computed expressions) cannot be. Fix the flagged values and only include enums that can be checked, or add `<<__AllowUncheckedEnumValues>>` to the enum. (Typing[4520])
  File "enum_uncheckable_values.php", line 46, characters 3-4:
  `R1` cannot be checked
  File "enum_uncheckable_values.php", line 47, characters 3-4:
  `R2` cannot be checked
  File "enum_uncheckable_values.php", line 48, characters 3-4:
  `R3` cannot be checked
  File "enum_uncheckable_values.php", line 49, characters 3-4:
  `R4` cannot be checked
  File "enum_uncheckable_values.php", line 50, characters 3-4:
  `R5` cannot be checked
  File "enum_uncheckable_values.php", line 45, characters 6-24:
  (and 2 more)
"#
        );
        assert_eq!(
            render(&enum_uncheckable_value(
                pos("enum_alias_exempt.php", 43, 6, 26),
                s("\\PartlyUncheckableBase"),
                Lazy::from_val((
                    vec![(
                        pos("enum_alias_exempt.php", 46, 3, 4),
                        s("`PC` cannot be checked")
                    )],
                    0
                )),
            )),
            r#"ERROR: File "enum_alias_exempt.php", line 43, characters 6-26:
`PartlyUncheckableBase` cannot be statically checked for duplicate values. Member values must be int or string literals, `nameof`, or `::class` to be checked; references to global constants (or other computed expressions) cannot be. Fix the flagged values and only include enums that can be checked, or add `<<__AllowUncheckedEnumValues>>` to the enum. (Typing[4520])
  File "enum_alias_exempt.php", line 46, characters 3-4:
  `PC` cannot be checked
"#
        );
    }

    // function_pointer/reified_meth_caller2.php.exp
    #[test]
    fn test_reified_function_reference() {
        assert_eq!(
            render(&reified_function_reference(pos(
                "reified_meth_caller2.php",
                8,
                3,
                36
            ))),
            r#"ERROR: File "reified_meth_caller2.php", line 8, characters 3-36:
Invalid function reference. This function requires reified generics. Prefer using a lambda instead. (Typing[4381])
"#
        );
    }

    // enum_class/typing.multiple.extends.vshape.bad.php.exp
    #[test]
    fn test_classish_const() {
        assert_eq!(
            render(&reinheriting_classish_const(
                pos("typing.multiple.extends.vshape.bad.php", 17, 12, 13),
                s("\\V0"),
                pos("typing.multiple.extends.vshape.bad.php", 17, 35, 36),
                s("\\F0"),
                s("\\E0"),
                s("B"),
            )),
            r#"ERROR: File "typing.multiple.extends.vshape.bad.php", line 17, characters 35-36:
V0 cannot re-inherit constant B from F0 (Typing[4389])
  File "typing.multiple.extends.vshape.bad.php", line 17, characters 12-13:
  because it already inherited it via E0
"#
        );
        assert_eq!(
            render(&redeclaring_classish_const(
                pos("typing.multiple.extends.vshape.bad.php", 50, 12, 13),
                s("\\V3"),
                pos("typing.multiple.extends.vshape.bad.php", 51, 11, 11),
                s("\\F3"),
                s("C")
            )),
            r#"ERROR: File "typing.multiple.extends.vshape.bad.php", line 51, characters 11-11:
V3 cannot re-declare constant C (Typing[4389])
  File "typing.multiple.extends.vshape.bad.php", line 50, characters 12-13:
  because it already inherited it via F3
"#
        );
    }

    // function_pointer/class_meth_abstract_trait.php.exp
    #[test]
    fn test_abstract_function_pointer() {
        assert_eq!(
            render(&abstract_function_pointer(
                s("\\Foo"),
                s("bar"),
                pos("class_meth_abstract_trait.php", 8, 8, 10),
                pos("class_meth_abstract_trait.php", 4, 35, 37)
            )),
            r#"ERROR: File "class_meth_abstract_trait.php", line 8, characters 8-10:
Cannot create a function pointer to `Foo::bar`; it is abstract (Typing[4391])
  File "class_meth_abstract_trait.php", line 4, characters 35-37:
  Declaration is here
"#
        );
    }

    // case_sensitive_inheritance7.php.exp
    // case_sensitive_inheritance9.php.exp
    #[test]
    fn test_inherited_class_member_with_different_case() {
        assert_eq!(
            render(&inherited_class_member_with_different_case(
                s("method"),
                "foo",
                "FOO",
                pos("case_sensitive_inheritance7.php", 7, 26, 28),
                s("\\B"),
                s("\\A"),
                pos("case_sensitive_inheritance7.php", 3, 19, 21),
            )),
            r#"ERROR: File "case_sensitive_inheritance7.php", line 7, characters 26-28:
B inherits a method named `FOO` whose name differs from this one (`foo`) only by case. (Typing[4393])
  File "case_sensitive_inheritance7.php", line 3, characters 19-21:
  It was inherited from A as `~~FOO~~`. If you meant to override it, please use the same casing as the inherited method. Otherwise, please choose a different name for the new method
"#
        );
        assert_eq!(
            render(&multiple_inherited_class_member_with_different_case(
                s("method"),
                "FOO",
                "foO",
                "\\A",
                "\\T",
                s("\\B"),
                pos("case_sensitive_inheritance9.php", 16, 7, 7),
                pos("case_sensitive_inheritance9.php", 8, 19, 21),
                pos("case_sensitive_inheritance9.php", 11, 26, 28),
            )),
            r#"ERROR: File "case_sensitive_inheritance9.php", line 16, characters 7-7:
`B` inherited two versions of the method `FOO` whose names differ only by case. (Typing[4393])
  File "case_sensitive_inheritance9.php", line 8, characters 19-21:
  It inherited `FOO` from A here.
  File "case_sensitive_inheritance9.php", line 11, characters 26-28:
  And `foO` from T here. Please rename these methods to the same casing.
"#
        );
    }

    // multiple_instantiation_inheritence1.php.exp
    // multiple_instantiation_interface/insts3.php.exp
    #[test]
    fn test_multiple_instantiation_inheritence() {
        assert_eq!(
            render(&multiple_instantiation_inheritence(
                "\\C",
                s("implements"),
                "\\I",
                ImplementsInfo {
                    pos: pos("multiple_instantiation_inheritence1.php", 9, 39, 39),
                    instantiation: vec![s("int")],
                    via_direct_parent: (
                        pos("multiple_instantiation_inheritence1.php", 9, 39, 44),
                        s("\\I")
                    ),
                },
                ImplementsInfo {
                    pos: pos("multiple_instantiation_inheritence1.php", 7, 29, 29),
                    instantiation: vec![s("string")],
                    via_direct_parent: (
                        pos("multiple_instantiation_inheritence1.php", 9, 26, 26),
                        s("\\D")
                    ),
                },
            )),
            r#"ERROR: File "multiple_instantiation_inheritence1.php", line 9, characters 26-26:
This makes C implements I<string> but it already implements I at another instantiation (Typing[4480])
  File "multiple_instantiation_inheritence1.php", line 9, characters 39-44:
  It already implements I<int>
  File "multiple_instantiation_inheritence1.php", line 7, characters 29-29:
  This is where D implements I
  File "multiple_instantiation_inheritence1.php", line 9, characters 39-39:
  I<int> should be a subtype of I<string>, but it's not because
"#
        );
        assert_eq!(
            render(&multiple_instantiation_inheritence(
                "\\GG",
                s("implements"),
                "\\J",
                ImplementsInfo {
                    pos: pos("insts3.php", 21, 21, 21),
                    instantiation: vec![s("mixed")],
                    via_direct_parent: (pos("insts3.php", 24, 31, 31), s("\\K")),
                },
                ImplementsInfo {
                    pos: pos("insts3.php", 11, 20, 20),
                    instantiation: vec![s("arraykey")],
                    via_direct_parent: (pos("insts3.php", 24, 18, 18), s("\\E")),
                },
            )),
            r#"ERROR: File "insts3.php", line 24, characters 18-18:
This makes GG implements J<arraykey> but it already implements J at another instantiation (Typing[4480])
  File "insts3.php", line 24, characters 31-31:
  It already implements J<mixed> via K
  File "insts3.php", line 21, characters 21-21:
  This is where K implements J
  File "insts3.php", line 11, characters 20-20:
  This is where E implements J
  File "insts3.php", line 21, characters 21-21:
  J<mixed> should be a subtype of J<arraykey>, but it's not because
"#
        );
    }

    // test_index_type_error_message_tuple.php.exp
    #[test]
    fn test_generic_unify() {
        assert_eq!(
            render(&generic_unify(
                pos("test_index_type_error_message_tuple.php", 14, 6, 8),
                s("Tuple elements can only be accessed with an integer literal")
            )),
            r#"ERROR: File "test_index_type_error_message_tuple.php", line 14, characters 6-8:
Tuple elements can only be accessed with an integer literal (Typing[4116])
"#
        );
    }

    // const_type_violated_constraint.php.exp
    #[test]
    fn test_explain_constraint() {
        assert_eq!(
            render(&explain_constraint(pos(
                "const_type_violated_constraint.php",
                4,
                9,
                29
            ))),
            r#"ERROR: File "const_type_violated_constraint.php", line 4, characters 9-29:
Some type arguments violate their constraints (Typing[4323])
"#
        );
    }

    // new_inference/index_array_bad.php.exp
    #[test]
    fn test_index_type_mismatch() {
        assert_eq!(
            render(&index_type_mismatch(
                pos("index_array_bad.php", 19, 13, 15),
                false,
                Some(s("Invalid index type for this KeyedContainer")),
                Some(Lazy::from_val(vec![
                    m(pos("index_array_bad.php", 9, 18, 20), "This is an int"),
                    m(
                        pos("index_array_bad.php", 19, 13, 15),
                        "It is incompatible with a string"
                    ),
                ])),
            )),
            r#"ERROR: File "index_array_bad.php", line 19, characters 13-15:
Invalid index type for this KeyedContainer (Typing[4324])
  File "index_array_bad.php", line 9, characters 18-20:
  This is an int
  File "index_array_bad.php", line 19, characters 13-15:
  It is incompatible with a string
"#
        );
        // The defaults, and the code for a covariant container.
        let t = index_type_mismatch(pos("a.php", 19, 13, 15), true, None, None);
        assert_eq!(
            render(&t),
            "ERROR: File \"a.php\", line 19, characters 13-15:\nInvalid index expression (Typing[4449])\n"
        );
    }

    // trait_private_bad2.php.exp
    // string_no_members.php.exp
    #[test]
    fn test_smember_not_found() {
        assert_eq!(
            render(&smember_not_found(
                pos("trait_private_bad2.php", 24, 18, 20),
                ClassMemberKind::static_method,
                s("foo"),
                s("\\B"),
                pos("trait_private_bad2.php", 22, 7, 7),
                Some((
                    InstanceOrStatic::instance,
                    pos("trait_private_bad2.php", 23, 19, 21),
                    s("bar")
                )),
                vec![],
            )),
            r#"ERROR: File "trait_private_bad2.php", line 24, characters 18-20:
No static method `foo` in `B` (Typing[4090])
  File "trait_private_bad2.php", line 23, characters 19-21:
  Did you mean instance method `bar` instead?
  File "trait_private_bad2.php", line 22, characters 7-7:
  Declaration of `B` is here
"#
        );
        assert_eq!(
            render(&smember_not_found(
                pos("string_no_members.php", 4, 11, 15),
                ClassMemberKind::class_constant,
                s("class"),
                s("\\HH\\string"),
                pos("string.hhi", 6, 15, 20),
                None,
                vec![],
            )),
            r#"ERROR: File "string_no_members.php", line 4, characters 11-15:
No class constant `class` in `string` (Typing[4090])
  File "string.hhi", line 6, characters 15-20:
  Declaration of `string` is here
"#
        );
    }

    // meth_caller/meth_caller_named.php.exp
    #[test]
    fn test_invalid_meth_caller_inout_parameter() {
        assert_eq!(
            render(&invalid_meth_caller_inout_parameter(
                pos("meth_caller_named.php", 23, 3, 59),
                pos("meth_caller_named.php", 13, 45, 46)
            )),
            r#"ERROR: File "meth_caller_named.php", line 23, characters 3-59:
`meth_caller` does not support methods with the `inout` calling convention (Typing[4416])
  File "meth_caller_named.php", line 13, characters 45-46:
  This is why I think this method uses the `inout` calling convention
"#
        );
    }

    // No `.exp` file has the errors below: the expected texts are read off the
    // OCaml.

    #[test]
    fn test_trivial_strict_eq() {
        // The reasons are: left, its typedef trail, right, its typedef trail.
        let t = trivial_strict_eq(
            pos("a.php", 9, 7, 15),
            false,
            Lazy::from_val(vec![m(pos("a.php", 4, 9, 11), "This is an int")]),
            Lazy::from_val(vec![m(pos("a.php", 6, 9, 14), "This is a string")]),
            vec![pos("a.php", 1, 6, 7)],
            vec![pos("a.php", 2, 6, 7), pos("a.php", 3, 6, 7)],
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"a.php\", line 9, characters 7-15:\n\
             This expression is always `false` (Typing[4118])\n  \
             File \"a.php\", line 4, characters 9-11:\n  \
             This is an int\n  \
             File \"a.php\", line 1, characters 6-7:\n  \
             Typedef definition comes from here\n  \
             File \"a.php\", line 6, characters 9-14:\n  \
             This is a string\n  \
             File \"a.php\", line 2, characters 6-7:\n  \
             Typedef definition comes from here\n  \
             File \"a.php\", line 3, characters 6-7:\n  \
             Typedef definition comes from here\n"
        );
        let t = trivial_strict_not_nullable_compare_null(
            pos("a.php", 9, 7, 15),
            true,
            Lazy::from_val(vec![m(pos("a.php", 4, 9, 11), "This is an int")]),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"a.php\", line 9, characters 7-15:\n\
             This expression is always `true` (Typing[4151])\n  \
             File \"a.php\", line 4, characters 9-11:\n  \
             This is an int\n"
        );
    }

    #[test]
    fn test_bad_conditional_support_dynamic() {
        // `ty_name` is forced before `self_ty_name`, and only by the claim.
        let order = Rc::new(RefCell::new(vec![]));
        let mk = |name: &'static str| {
            let order = order.clone();
            Lazy::new(move || {
                order.borrow_mut().push(name);
                name.to_string()
            })
        };
        let t = bad_conditional_support_dynamic(
            pos("a.php", 3, 7, 7),
            s("\\C"),
            s("\\HH\\Traversable"),
            mk("T"),
            mk("C<T>"),
        );
        assert!(order.borrow().is_empty());
        assert_eq!(
            render(&t),
            "ERROR: File \"a.php\", line 3, characters 7-7:\n\
             Class C must support dynamic at least as often as Traversable:\n\
             T is subtype of dynamic implies C<T> is subtype of dynamic (Typing[4433])\n"
        );
        assert_eq!(*order.borrow(), vec!["T", "C<T>"]);
    }

    #[test]
    fn test_kind_mismatch() {
        let t = kind_mismatch(
            pos("a.php", 5, 10, 12),
            pos("a.php", 3, 12, 13),
            s("T"),
            s("a type constructor"),
            s("a fully-applied type"),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"a.php\", line 5, characters 10-12:\n\
             This is a fully-applied type, but a type constructor was expected here. (Typing[4383])\n  \
             File \"a.php\", line 3, characters 12-13:\n  \
             We are expecting a type constructor due to the definition of T here.\n"
        );
    }

    #[test]
    fn test_ambiguous_lambda() {
        let t = ambiguous_lambda(
            pos("a.php", 5, 10, 20),
            Lazy::from_val(vec![
                m(pos("a.php", 6, 3, 4), "int"),
                m(pos("a.php", 7, 3, 4), "string"),
            ]),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"a.php\", line 5, characters 10-20:\n\
             Lambda has parameter types that could not be determined at definition site. (Typing[4222])\n  \
             File \"a.php\", line 5, characters 10-20:\n  \
             2 distinct use types were determined: please add type hints to lambda parameters.\n  \
             File \"a.php\", line 6, characters 3-4:\n  \
             This use has type `int`\n  \
             File \"a.php\", line 7, characters 3-4:\n  \
             This use has type `string`\n"
        );
    }

    #[test]
    fn test_parent_support_dynamic_type() {
        let claim = |child_kind, parent_kind, child_support_dynamic_type| {
            let t = parent_support_dynamic_type(
                pos("a.php", 3, 7, 7),
                (s("\\C"), child_kind),
                (s("\\P"), parent_kind),
                child_support_dynamic_type,
            );
            assert_eq!(t.code, ErrorCode::ImplementsDynamic);
            assert!(t.reasons.force().is_empty());
            t.claim.force().1.to_string()
        };
        let class = ClassishKind::Cclass(Abstraction::Concrete);
        assert_eq!(
            claim(class, class, false),
            "Class `C` must declare <<__SupportDynamicType>> because it extends class `P` which does"
        );
        assert_eq!(
            claim(class, ClassishKind::Cinterface, true),
            "Class `C` cannot declare <<__SupportDynamicType>> because it implements interface `P` which does not"
        );
        assert_eq!(
            claim(ClassishKind::Cinterface, ClassishKind::Cinterface, false),
            "Interface `C` must declare <<__SupportDynamicType>> because it extends interface `P` which does"
        );
        assert_eq!(
            claim(ClassishKind::Ctrait, ClassishKind::Ctrait, false),
            "Trait `C` must declare <<__SupportDynamicType>> because it uses trait `P` which does"
        );
        assert_eq!(
            claim(
                ClassishKind::CenumClass(Abstraction::Concrete),
                ClassishKind::CenumClass(Abstraction::Abstract),
                false
            ),
            "Enum class `C` must declare <<__SupportDynamicType>> because it enum class `P` which does"
        );
    }

    #[test]
    fn test_property_is_not_dynamic() {
        let t = property_is_not_enforceable(
            pos("a.php", 3, 7, 7),
            "x",
            s("\\C"),
            (pos("a.php", 4, 14, 15), s("vec<int>")),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"a.php\", line 3, characters 7-7:\n\
             Class `C` cannot support dynamic because property `x` does not have an enforceable type (Typing[4402])\n  \
             File \"a.php\", line 4, characters 14-15:\n  \
             Property `x` has type `vec<int>`\n"
        );
        let t = property_is_not_dynamic(
            pos("a.php", 3, 7, 7),
            "x",
            s("\\C"),
            (pos("a.php", 4, 14, 15), s("vec<int>")),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"a.php\", line 3, characters 7-7:\n\
             Class `C` cannot support dynamic because property `x` cannot be assigned to dynamic (Typing[4402])\n  \
             File \"a.php\", line 4, characters 14-15:\n  \
             Property `x` has type `vec<int>`\n"
        );
        let t = private_property_is_not_enforceable(
            pos("a.php", 3, 7, 7),
            "x",
            s("\\C"),
            (pos("a.php", 4, 14, 15), s("vec<int>")),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"a.php\", line 3, characters 7-7:\n\
             Cannot write to property `x` through dynamic type because private property in `C` does not have an enforceable type (Typing[4426])\n  \
             File \"a.php\", line 4, characters 14-15:\n  \
             Property `x` has type `vec<int>`\n"
        );
        let t = private_property_is_not_dynamic(
            pos("a.php", 3, 7, 7),
            "x",
            s("\\C"),
            (pos("a.php", 4, 14, 15), s("vec<int>")),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"a.php\", line 3, characters 7-7:\n\
             Cannot read from property `x` through dynamic type because private property in `C` cannot be assigned to dynamic (Typing[4425])\n  \
             File \"a.php\", line 4, characters 14-15:\n  \
             Property `x` has type `vec<int>`\n"
        );
    }
    #[test]
    fn test_claims_without_exp() {
        let p = || pos("a.php", 3, 5, 9);
        let claim = |t: T| {
            assert!(t.reasons.force().is_empty());
            assert!(t.quickfixes.is_empty());
            let Message(pos, msg) = t.claim.force();
            assert_eq!(*pos, p());
            (t.code, msg.to_string())
        };
        assert_eq!(
            claim(unresolved_tyvar(p())),
            (
                ErrorCode::UnresolvedTypeVariable,
                s("The type of this expression contains an unresolved type variable")
            )
        );
        assert_eq!(
            claim(bad_enum_decl(p())),
            (
                ErrorCode::BadEnumExtends,
                s("This enum declaration is invalid.")
            )
        );
        assert_eq!(
            claim(invalid_echo_argument(p())),
            (
                ErrorCode::InvalidEchoArgument,
                s("Invalid `echo`/`print` argument")
            )
        );
        // The text of a reason of ambiguous_inheritance.php.exp.
        assert_eq!(
            claim(ambiguous_inheritance(p(), s("I1"), s("C"))),
            (
                ErrorCode::UnifyError,
                s(
                    "This declaration was inherited from an object of type `I1`. Redeclare this member in `C` with a compatible signature."
                )
            )
        );
        assert_eq!(
            claim(invalid_substring(p(), Lazy::from_val(s("an int")))),
            (
                ErrorCode::InvalidSubString,
                s("Expected an object convertible to string but got an int")
            )
        );
        assert_eq!(
            claim(nullsafe_property_write_context(p())),
            (
                ErrorCode::NullsafePropertyWriteContext,
                s("`?->` syntax not supported here, this function effectively does a write")
            )
        );
        assert_eq!(
            claim(invalid_arraykey_constraint(p(), s("a float"))),
            (
                ErrorCode::InvalidArrayKeyConstraint,
                s("This type is a float, which cannot be used as an arraykey (string | int)")
            )
        );
    }

    #[test]
    fn test_reasons_without_exp() {
        let t = unsatisfied_req_this_as(
            pos("a.php", 18, 7, 7),
            pos("a.php", 19, 7, 8),
            s("\\C"),
            pos("a.php", 9, 17, 17),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"a.php\", line 18, characters 7-7:\n\
             This class does not satisfy all the requirements of its traits or interfaces. (Typing[4111])\n  \
             File \"a.php\", line 19, characters 7-8:\n  \
             This requires to be a subtype of C\n  \
             File \"a.php\", line 9, characters 17-17:\n  \
             Required here\n"
        );
        let t = invalid_keyset_value(
            pos("a.php", 20, 3, 12),
            pos("a.php", 19, 8, 12),
            s("an object of type keyset<(arraykey & _)>"),
            pos("a.php", 20, 10, 12),
            s("a float"),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"a.php\", line 20, characters 3-12:\n\
             Keyset values must be arraykeys (Typing[4324])\n  \
             File \"a.php\", line 19, characters 8-12:\n  \
             This container is an object of type keyset<(arraykey & _)>\n  \
             File \"a.php\", line 20, characters 10-12:\n  \
             A float is not an arraykey\n"
        );
        let t = nullable_cast(
            pos("a.php", 4, 10, 17),
            pos("a.php", 3, 14, 17),
            Lazy::from_val(s("?int")),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"a.php\", line 4, characters 10-17:\n\
             Casting from a nullable type is forbidden (Typing[4167])\n  \
             File \"a.php\", line 3, characters 14-17:\n  \
             This is `?int`\n"
        );
        let t = strict_eq_value_incompatible_types(
            pos("a.php", 17, 7, 15),
            vec![m(pos("a.php", 4, 9, 11), "This is an int")],
            vec![m(pos("a.php", 9, 9, 11), "This is a string")],
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"a.php\", line 17, characters 7-15:\n\
             The arguments to this value equality test are not the same types or are not the allowed types (int, bool, float, string, vec, keyset, dict). The behavior for this test is changing and will soon either be universally false or throw an exception. (Typing[4443])\n  \
             File \"a.php\", line 4, characters 9-11:\n  \
             This is an int\n  \
             File \"a.php\", line 9, characters 9-11:\n  \
             This is a string\n"
        );
        let t = cannot_declare_constant(pos("a.php", 5, 9, 9), (pos("a.php", 3, 6, 6), s("\\E")));
        assert_eq!(
            render(&t),
            "ERROR: File \"a.php\", line 5, characters 9-9:\n\
             Cannot declare a constant in an enum (Typing[4130])\n  \
             File \"a.php\", line 3, characters 6-6:\n  \
             `E` was defined as an enum here\n"
        );
    }
}
