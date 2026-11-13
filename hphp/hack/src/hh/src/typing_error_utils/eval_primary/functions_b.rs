// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of `Typing_error_utils.Eval_primary`. See `mod.rs`.
//!
//! The second half of the functions of `Eval_primary` (`typing_error_utils.ml`
//! from `immutable_local` to the end of the module), in the order of the OCaml
//! file, ending with `to_error`.
//!
//! Notes on the transliteration:
//!
//! - `lazy e` is `lazy!(e)`: what OCaml computes when the claim or the reasons
//!   are forced is computed when they are forced here, and what it computes
//!   when the function is called (the quickfixes, `Render.strip_ns` on some
//!   names) is computed when the function is called.
//! - A parameter that a `lazy` captures, or that ends up in the result, is
//!   taken by value; one that is only read when the function is called is
//!   taken by reference (as in `functions_a.rs`).
//! - `Pos_or_decl.t` and `Pos.t` are the same Rust type, and
//!   `Pos_or_decl.of_raw_pos` is the identity in OCaml too, so it (and
//!   `Message.map ~f:Pos_or_decl.of_raw_pos`) disappears.
//! - `Pos_or_decl.(equal p none)` is `p.is_none()`. The one other use of
//!   `Pos_or_decl.equal` (`require_dynamic_obj_get`) is `==`, which compares
//!   the file and the offsets where the derived OCaml equality is structural.
//! - A chain of `^` is `[..].concat()` with the same pieces; `Printf.sprintf`
//!   is `format!`.
//! - The functions of `Pos` and `Quickfix` that `oxidized` does not have are
//!   called where the porting rules put them: `crate::pos` and
//!   `crate::quickfix`.

use oxidized::classish_positions_types;
use oxidized::error_codes::Typing as ErrorCode;
use oxidized::message::Message;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use oxidized::quickfix::Edits;
use oxidized::quickfix::HintStyle;
use oxidized::quickfix::Quickfix;

use super::super::common::Lazy;
use super::T;
use super::create;
use super::functions_a::*;
use super::nested::eval_casetype;
use super::nested::eval_coeffect;
use super::nested::eval_destructure;
use super::nested::eval_enum;
use super::nested::eval_expr_tree;
use super::nested::eval_modules;
use super::nested::eval_package;
use super::nested::eval_readonly;
use super::nested::eval_shape;
use super::nested::eval_shape_splat;
use super::nested::eval_simplihack;
use super::nested::eval_switch;
use super::nested::eval_wellformedness;
use super::nested::eval_xhp;
use crate::naming_errors::render::md_codify;
use crate::naming_errors::render::strip_ns;
use crate::naming_errors::render::utils_strip_ns;
use crate::typing_error::primary;

/// `lazy e`
macro_rules! lazy {
    ($e:expr) => {
        Lazy::new(move || $e)
    };
}

/// `Pos_or_decl.t Message.t list Lazy.t`
type Reasons = Lazy<Vec<Message<PosOrDecl>>>;

/// `String.capitalize` (Core): the first byte, if it is an ASCII lowercase
/// letter, in upper case.
fn string_capitalize(s: &str) -> String {
    let mut s = s.to_string();
    if let Some(first) = s.get_mut(0..1) {
        first.make_ascii_uppercase();
    }
    s
}

pub fn immutable_local(pos: Pos) -> T {
    let claim = lazy!(Message(
        pos,
        // TODO: generalize this error message in the future for arbitrary immutable locals
        "This variable cannot be reassigned because it is used for a dependent context".into(),
    ));
    create(ErrorCode::ImmutableLocal, claim, None, None)
}

pub fn require_dynamic_obj_get(
    receiver_pos: Pos,
    receiver_ty: Lazy<String>,
    receiver_ty_pos: PosOrDecl,
    member_kind: primary::RequireDynamicObjGetMemberKind,
    member_name: Option<primary::DynamicObjGetMember>,
) -> T {
    let member_kind = match member_kind {
        primary::RequireDynamicObjGetMemberKind::Property => "property",
        primary::RequireDynamicObjGetMemberKind::Method => "method",
    };
    let claim = {
        let receiver_pos = receiver_pos.clone();
        lazy!(Message(
            receiver_pos,
            format!(
                "Dynamic access of a {} is only permitted on a receiver of type `dynamic`, but this receiver has type {}",
                member_kind,
                md_codify(receiver_ty.force())
            ).into(),
        ))
    };
    let receiver_ty_reason: Vec<Message<PosOrDecl>> = {
        let receiver_pos: PosOrDecl = receiver_pos;
        if receiver_ty_pos.is_none() || receiver_ty_pos == receiver_pos {
            vec![]
        } else {
            vec![Message(
                receiver_ty_pos,
                "The receiver's type is defined here".into(),
            )]
        }
    };
    let (reasons, quickfixes) = match member_name {
        Some(primary::DynamicObjGetMember {
            member_pos,
            member_name_pos,
            member_name,
        }) => {
            let member_name = match member_name.strip_prefix('$') {
                Some(member_name) => member_name.to_string(),
                None => member_name,
            };
            let suggestion = format!("->{}", member_name);
            let reasons = {
                let suggestion = suggestion.clone();
                lazy!({
                    let mut reasons = vec![Message(
                        member_name_pos,
                        format!("Did you mean {} instead?", md_codify(&suggestion)).into(),
                    )];
                    reasons.extend(receiver_ty_reason);
                    reasons
                })
            };
            let quickfixes = vec![crate::quickfix::make_eager(
                ["Change to ", &suggestion].concat(),
                member_name,
                vec![HintStyle::HintStyleSilent(
                    classish_positions_types::Pos::Precomputed(member_pos.clone()),
                )],
                member_pos,
            )];
            (reasons, quickfixes)
        }
        None => (lazy!(receiver_ty_reason), vec![]),
    };
    create(
        ErrorCode::RequireDynamicObjGet,
        claim,
        Some(reasons),
        Some(quickfixes),
    )
}

pub fn nonsense_member_selection(pos: Pos, kind: String) -> T {
    let claim = lazy!(Message(
        pos,
        [
            "Dynamic member access requires a local variable, not `",
            &kind,
            "`.",
        ]
        .concat()
        .into(),
    ));
    create(ErrorCode::NonsenseMemberSelection, claim, None, None)
}

pub fn consider_meth_caller(pos: Pos, class_name: String, meth_name: String) -> T {
    let claim = lazy!(Message(
        pos,
        [
            "Function pointer syntax requires a static method. ",
            "Use `meth_caller(",
            strip_ns(&class_name),
            "::class, '",
            &meth_name,
            "')` to create a function pointer to the instance method",
        ]
        .concat()
        .into(),
    ));
    create(ErrorCode::ConsiderMethCaller, claim, None, None)
}

pub fn method_import_via_diamond(
    pos: Pos,
    class_name: String,
    method_pos: PosOrDecl,
    method_name: String,
    trace1: Reasons,
    trace2: Reasons,
) -> T {
    let claim = lazy!({
        let class_name = md_codify(strip_ns(&class_name));
        let method_name = md_codify(strip_ns(&method_name));
        Message(
            pos,
            [
                "Class ",
                &class_name,
                " inherits trait method ",
                &method_name,
                " via multiple traits.  Add the __EnableMethodTraitDiamond attribute to ",
                &class_name,
                ", remove the multiple paths, or override the method",
            ]
            .concat()
            .into(),
        )
    });
    let reasons = lazy!({
        let trace1 = trace1.force();
        let trace2 = trace2.force();
        let mut reasons = vec![Message(method_pos, "Trait method is defined here".into())];
        reasons.extend(trace1.iter().cloned());
        reasons.extend(trace2.iter().cloned());
        reasons
    });
    create(ErrorCode::DiamondTraitMethod, claim, Some(reasons), None)
}

pub fn property_import_via_diamond(
    generic: bool,
    pos: Pos,
    class_name: String,
    property_pos: PosOrDecl,
    property_name: String,
    trace1: Reasons,
    trace2: Reasons,
) -> T {
    let claim = lazy!({
        let class_name = md_codify(strip_ns(&class_name));
        let property_name = md_codify(strip_ns(&property_name));
        Message(
            pos,
            [
                "Class ",
                &class_name,
                " inherits ",
                (if generic { "generic " } else { "" }),
                "trait property ",
                &property_name,
                " via multiple paths",
                (if generic { " at different types." } else { "." }),
                &(if !generic {
                    [
                        " Currently, traits with properties are not supported by ",
                        "the <<__EnableMethodTraitDiamond>> experimental feature.",
                    ]
                    .concat()
                } else {
                    "".to_string()
                }),
            ]
            .concat()
            .into(),
        )
    });
    let reasons = lazy!({
        let trace1 = trace1.force();
        let trace2 = trace2.force();
        let mut reasons = vec![Message(
            property_pos,
            "Trait property is defined here".into(),
        )];
        reasons.extend(trace1.iter().cloned());
        reasons.extend(trace2.iter().cloned());
        reasons
    });
    create(ErrorCode::DiamondTraitProperty, claim, Some(reasons), None)
}

pub fn unification_cycle(pos: Pos, ty: String) -> T {
    let claim = lazy!(Message(
        pos,
        [
            "Type circularity: in order to type-check this expression it ",
            "is necessary for a type [rec] to be equal to type ",
            &md_codify(&ty),
        ]
        .concat()
        .into(),
    ));
    create(ErrorCode::UnificationCycle, claim, None, None)
}

pub fn method_variance(pos: Pos) -> T {
    let claim = lazy!(Message(
        pos,
        "Covariance or contravariance is not allowed in type parameters of methods or functions."
            .into(),
    ));
    create(ErrorCode::MethodVariance, claim, None, None)
}

pub fn explain_tconst_where_constraint(
    use_pos: Pos,
    definition_pos: PosOrDecl,
    msgl: Reasons,
) -> T {
    let claim = lazy!(Message(
        use_pos,
        "A `where` type constraint is violated here".into(),
    ));
    let reasons = lazy!({
        let msgl = msgl.force();
        let mut reasons = vec![Message(
            definition_pos,
            "This method's `where` constraints contain a generic type access".into(),
        )];
        reasons.extend(msgl.iter().cloned());
        reasons
    });
    create(
        ErrorCode::TypeConstraintViolation,
        claim,
        Some(reasons),
        None,
    )
}

pub fn format_string(
    pos: Pos,
    snippet: String,
    s: String,
    class_pos: PosOrDecl,
    fname: String,
    class_suggest: String,
) -> T {
    let claim = lazy!(Message(
        pos,
        [
            "Invalid format string ",
            &md_codify(&snippet),
            " in ",
            &md_codify(&["\"", &s, "\""].concat()),
        ]
        .concat()
        .into(),
    ));
    let reasons = lazy!(vec![Message(
        class_pos,
        [
            "You can add a new format specifier by adding ",
            &md_codify(&[&fname, "()"].concat()),
            " to ",
            &md_codify(&class_suggest),
        ]
        .concat()
        .into(),
    )]);
    create(ErrorCode::FormatString, claim, Some(reasons), None)
}

pub fn expected_literal_format_string(pos: Pos) -> T {
    let claim = lazy!(Message(
        pos,
        "This argument must be a literal format string".into(),
    ));
    create(ErrorCode::ExpectedLiteralFormatString, claim, None, None)
}

pub fn re_prefixed_non_string(pos: Pos, reason: primary::RePrefixedNonStringReason) -> T {
    let claim = lazy!({
        let non_strings = match reason {
            primary::RePrefixedNonStringReason::embedded_expr => {
                "Strings with embedded expressions"
            }
            primary::RePrefixedNonStringReason::non_string => "Non-strings",
        };
        Message(
            pos,
            [non_strings, " are not allowed to be to be `re`-prefixed"]
                .concat()
                .into(),
        )
    });
    create(ErrorCode::RePrefixedNonString, claim, None, None)
}

pub fn bad_regex_pattern(pos: Pos, reason: primary::BadRegexPatternReason) -> T {
    let claim = lazy!({
        let s = match reason {
            primary::BadRegexPatternReason::bad_patt(s) => s,
            primary::BadRegexPatternReason::empty_patt => "This pattern is empty".to_string(),
            primary::BadRegexPatternReason::missing_delim => "Missing delimiter(s)".to_string(),
            primary::BadRegexPatternReason::invalid_option => {
                "Invalid global option(s)".to_string()
            }
        };
        Message(pos, ["Bad regex pattern; ", &s, "."].concat().into())
    });
    create(ErrorCode::BadRegexPattern, claim, None, None)
}

pub fn option_return_only_typehint(p: Pos, kind: primary::OptionReturnOnlyTypehintKind) -> T {
    let claim = lazy!({
        let (typehint, reason) = match kind {
            primary::OptionReturnOnlyTypehintKind::void => ("?void", "only return implicitly"),
            primary::OptionReturnOnlyTypehintKind::noreturn => ("?noreturn", "never return"),
        };
        Message(
            p,
            [
                &md_codify(typehint),
                " is a nonsensical typehint; a function cannot both ",
                reason,
                " and return null.",
            ]
            .concat()
            .into(),
        )
    });
    create(ErrorCode::OptionReturnOnlyTypehint, claim, None, None)
}

pub fn redeclaring_missing_method(p: Pos, trait_method: String) -> T {
    let claim = lazy!(Message(
        p,
        [
            "Attempting to redeclare a trait method ",
            &md_codify(&trait_method),
            " which was never inherited. ",
            "You might be trying to redeclare a non-static method as `static` or vice-versa.",
        ]
        .concat()
        .into(),
    ));
    create(ErrorCode::RedeclaringMissingMethod, claim, None, None)
}

pub fn expecting_type_hint(p: Pos) -> T {
    let claim = lazy!(Message(p, "Was expecting a type hint".into()));
    create(ErrorCode::ExpectingTypeHint, claim, None, None)
}

pub fn expecting_type_hint_variadic(p: Pos) -> T {
    let claim = lazy!(Message(
        p,
        "Was expecting a type hint on this variadic parameter".into(),
    ));
    create(ErrorCode::ExpectingTypeHintVariadic, claim, None, None)
}

pub fn expecting_return_type_hint(p: Pos) -> T {
    let claim = lazy!(Message(p, "Was expecting a return type hint".into()));
    create(ErrorCode::ExpectingReturnTypeHint, claim, None, None)
}

pub fn duplicate_using_var(pos: Pos) -> T {
    let claim = lazy!(Message(
        pos,
        "Local variable already used in `using` statement".into(),
    ));
    create(ErrorCode::DuplicateUsingVar, claim, None, None)
}

pub fn illegal_disposable(pos: Pos, verb: primary::IllegalDisposableVerb) -> T {
    let claim = lazy!({
        let verb = match verb {
            primary::IllegalDisposableVerb::assigned => "assigned",
        };
        Message(
            pos,
            [
                "Disposable objects must only be ",
                verb,
                " in a `using` statement",
            ]
            .concat()
            .into(),
        )
    });
    create(ErrorCode::IllegalDisposable, claim, None, None)
}

pub fn escaping_disposable(pos: Pos) -> T {
    let claim = lazy!(Message(
        pos,
        [
            "Variable from `using` clause may only be used as receiver in method invocation ",
            "or passed to function with `<<__AcceptDisposable>>` parameter attribute",
        ]
        .concat()
        .into(),
    ));
    create(ErrorCode::EscapingDisposable, claim, None, None)
}

pub fn escaping_disposable_parameter(pos: Pos) -> T {
    let claim = lazy!(Message(
        pos,
        [
            "Parameter with `<<__AcceptDisposable>>` attribute may only be used as receiver in method invocation ",
            "or passed to another function with `<<__AcceptDisposable>>` parameter attribute",
        ]
        .concat().into(),
    ));
    create(ErrorCode::EscapingDisposableParameter, claim, None, None)
}

pub fn escaping_this(pos: Pos) -> T {
    let claim = lazy!(Message(
        pos,
        [
            "`$this` implementing `IDisposable` or `IAsyncDisposable` may only be used as receiver in method invocation ",
            "or passed to another function with `<<__AcceptDisposable>>` parameter attribute",
        ]
        .concat().into(),
    ));
    create(ErrorCode::EscapingThis, claim, None, None)
}

pub fn must_extend_disposable(pos: Pos) -> T {
    let claim = lazy!(Message(
        pos,
        "A disposable type may not extend a class or use a trait that is not disposable".into(),
    ));
    create(ErrorCode::MustExtendDisposable, claim, None, None)
}

pub fn field_kinds(pos1: Pos, pos2: PosOrDecl) -> T {
    let claim = lazy!(Message(
        pos1,
        "You cannot use this kind of field (value)".into()
    ));
    let reasons = lazy!(vec![Message(
        pos2,
        "Mixed with this kind of field (key => value)".into(),
    )]);
    create(ErrorCode::FieldKinds, claim, Some(reasons), None)
}

pub fn unbound_name_typing(pos: Pos, name: String, class_exists: bool) -> T {
    let quickfixes = match class_exists {
        true => {
            let newpos = crate::pos::shrink_to_start(&pos);
            vec![crate::quickfix::make_eager_default_hint_style(
                ["Add ", &md_codify("new")].concat(),
                "new ".to_string(),
                newpos,
            )]
        }
        false => vec![],
    };
    let claim = lazy!(Message(
        pos,
        ["Unbound name (typing): ", &md_codify(strip_ns(&name))]
            .concat()
            .into(),
    ));
    create(ErrorCode::UnboundNameTyping, claim, None, Some(quickfixes))
}

pub fn previous_default(p: Pos) -> T {
    let claim = lazy!(Message(
        p,
        [
            "A previous parameter has a default value.\n",
            "Remove all the default values for the preceding parameters,\n",
            "or add a default value to this one.",
        ]
        .concat()
        .into(),
    ));
    create(ErrorCode::PreviousDefault, claim, None, None)
}

pub fn previous_default_or_optional(p: Pos) -> T {
    let claim = lazy!(Message(
        p,
        [
            "A previous parameter has a default value or is optional.\n",
            "Remove all the optional or default values for the preceding parameters,\n",
            "or add a default value or optional to this one.",
        ]
        .concat()
        .into(),
    ));
    create(ErrorCode::PreviousDefault, claim, None, None)
}

pub fn optional_parameter_not_supported(p: Pos) -> T {
    let claim = lazy!(Message(
        p,
        "Optional parameters are not supported. Use a default value instead.\n".into(),
    ));
    create(ErrorCode::OptionalParameterNotSupported, claim, None, None)
}

pub fn optional_parameter_not_abstract(p: Pos) -> T {
    let claim = lazy!(Message(
        p,
        "Optional parameters are not supported on top-level functions or non-abstract methods. Use a default value instead.\n".into(),
    ));
    create(ErrorCode::OptionalParameterNotSupported, claim, None, None)
}

pub fn return_in_void(pos1: Pos, pos2: Pos) -> T {
    let claim = lazy!(Message(pos1, "You cannot return a value".into()));
    let reasons = lazy!({
        let pos2: PosOrDecl = pos2;
        vec![Message(pos2, "This is a `void` function".into())]
    });
    create(ErrorCode::ReturnInVoid, claim, Some(reasons), None)
}

pub fn this_var_outside_class(p: Pos) -> T {
    let claim = lazy!(Message(p, "Can't use `$this` outside of a class".into()));
    create(ErrorCode::ThisVarOutsideClass, claim, None, None)
}

pub fn unbound_global(cst_pos: Pos) -> T {
    let claim = lazy!(Message(cst_pos, "Unbound global constant (Typing)".into()));
    create(ErrorCode::UnboundGlobal, claim, None, None)
}

pub fn private_meth_caller(use_pos: Pos, def_pos: PosOrDecl) -> T {
    let claim = lazy!(Message(
        use_pos,
        "You cannot access this method with `meth_caller` (even from the same class hierarchy)"
            .into(),
    ));
    let reasons = lazy!(vec![Message(
        def_pos,
        "It is declared as `private` here".into()
    )]);
    create(ErrorCode::PrivateMethCaller, claim, Some(reasons), None)
}

pub fn protected_meth_caller(use_pos: Pos, def_pos: PosOrDecl) -> T {
    let claim = lazy!(Message(
        use_pos,
        "You cannot access this method with `meth_caller` (even from the same class hierarchy)"
            .into(),
    ));
    let reasons = lazy!(vec![Message(
        def_pos,
        "It is declared as `protected` here".into()
    )]);
    create(ErrorCode::ProtectedMethCaller, claim, Some(reasons), None)
}

pub fn internal_meth_caller(use_pos: Pos, def_pos: PosOrDecl) -> T {
    let claim = lazy!(Message(
        use_pos,
        "You cannot access this method with `meth_caller` (even from the same module)".into(),
    ));
    let reasons = lazy!(vec![Message(
        def_pos,
        "It is declared as `internal` here".into()
    )]);
    create(ErrorCode::InternalMethCaller, claim, Some(reasons), None)
}

pub fn protected_internal_meth_caller(use_pos: Pos, def_pos: PosOrDecl) -> T {
    let claim = lazy!(Message(
        use_pos,
        "You cannot access this method with `meth_caller` (even from the same module and the same class hierarchy)".into(),
    ));
    let reasons = lazy!(vec![Message(
        def_pos,
        "It is declared as `protected internal` here".into(),
    )]);
    create(
        ErrorCode::ProtectedInternalMethCaller,
        claim,
        Some(reasons),
        None,
    )
}

pub fn array_cast(pos: Pos) -> T {
    let claim = lazy!(Message(
        pos,
        "(array) cast forbidden; arrays with unspecified key and value types are not allowed"
            .into(),
    ));
    create(ErrorCode::ArrayCast, claim, None, None)
}

pub fn string_cast(pos: Pos, ty: String) -> T {
    let claim = lazy!(Message(
        pos,
        format!(
            "Cannot cast a value of type {} to string. Only primitives may be used in a `(string)` cast.",
            md_codify(&ty)
        ).into(),
    ));
    create(ErrorCode::StringCast, claim, None, None)
}

pub fn static_outside_class(pos: Pos) -> T {
    let claim = lazy!(Message(
        pos,
        "`static` is undefined outside of a class".into()
    ));
    create(ErrorCode::StaticOutsideClass, claim, None, None)
}

pub fn self_outside_class(pos: Pos) -> T {
    let claim = lazy!(Message(
        pos,
        "`self` is undefined outside of a class".into()
    ));
    create(ErrorCode::SelfOutsideClass, claim, None, None)
}

pub fn new_inconsistent_construct(
    new_pos: Pos,
    (cpos, cname): (PosOrDecl, String),
    kind: primary::NewInconsistentConstructKind,
) -> T {
    let claim = lazy!({
        let name = strip_ns(&cname);
        let preamble = match kind {
            primary::NewInconsistentConstructKind::static_ => {
                ["Can't use `new static()` for ", &md_codify(name)].concat()
            }
            primary::NewInconsistentConstructKind::classname => [
                "Can't use `new` on ",
                &md_codify(&["classname<", name, ">"].concat()),
            ]
            .concat(),
        };
        Message(
            new_pos,
            [
                &preamble,
                "; `__construct` arguments are not guaranteed to be consistent in child classes",
            ]
            .concat()
            .into(),
        )
    });
    let reasons = lazy!(vec![Message(
        cpos,
        "This declaration is neither `final` nor uses the `<<__ConsistentConstruct>>` attribute"
            .into(),
    )]);
    create(ErrorCode::NewStaticInconsistent, claim, Some(reasons), None)
}

pub fn parent_outside_class(pos: Pos) -> T {
    let claim = lazy!(Message(
        pos,
        "`parent` is undefined outside of a class".into()
    ));
    create(ErrorCode::ParentOutsideClass, claim, None, None)
}

pub fn parent_abstract_call(call_pos: Pos, meth_name: String, decl_pos: PosOrDecl) -> T {
    let claim = lazy!(Message(
        call_pos,
        [
            "Cannot call ",
            &md_codify(&["parent::", &meth_name, "()"].concat()),
            "; it is abstract",
        ]
        .concat()
        .into(),
    ));
    let reasons = lazy!(vec![Message(decl_pos, "Declaration is here".into())]);
    create(ErrorCode::AbstractCall, claim, Some(reasons), None)
}

pub fn self_abstract_call(
    call_pos: Pos,
    meth_name: String,
    self_pos: Pos,
    decl_pos: PosOrDecl,
) -> T {
    let quickfixes = vec![crate::quickfix::make_eager_default_hint_style(
        ["Change to ", &md_codify(&["static::", &meth_name].concat())].concat(),
        "static".to_string(),
        self_pos,
    )];
    let claim = lazy!(Message(
        call_pos,
        [
            "Cannot call ",
            &md_codify(&["self::", &meth_name, "()"].concat()),
            "; it is abstract. Did you mean ",
            &md_codify(&["static::", &meth_name, "()"].concat()),
            "?",
        ]
        .concat()
        .into(),
    ));
    let reasons = lazy!(vec![Message(decl_pos, "Declaration is here".into())]);
    create(
        ErrorCode::AbstractCall,
        claim,
        Some(reasons),
        Some(quickfixes),
    )
}

pub fn classname_abstract_call(
    call_pos: Pos,
    meth_name: String,
    cname: String,
    decl_pos: PosOrDecl,
) -> T {
    let claim = lazy!(Message(
        call_pos,
        [
            "Cannot call ",
            &md_codify(&[strip_ns(&cname), "::", &meth_name, "()"].concat()),
            "; it is abstract",
        ]
        .concat()
        .into(),
    ));
    let reasons = lazy!(vec![Message(decl_pos, "Declaration is here".into())]);
    create(ErrorCode::AbstractCall, claim, Some(reasons), None)
}

pub fn static_synthetic_method(
    call_pos: Pos,
    meth_name: String,
    cname: &str,
    decl_pos: PosOrDecl,
) -> T {
    let cname = strip_ns(cname).to_string();
    let claim = lazy!(Message(
        call_pos,
        [
            "Cannot call ",
            &md_codify(&[&cname, "::", &meth_name, "()"].concat()),
            "; ",
            &md_codify(&meth_name),
            " is not defined in ",
            &md_codify(&cname),
        ]
        .concat()
        .into(),
    ));
    let reasons = lazy!(vec![Message(decl_pos, "Declaration is here".into())]);
    create(ErrorCode::StaticSyntheticMethod, claim, Some(reasons), None)
}

pub fn static_call_on_trait_require_non_strict(
    call_pos: Pos,
    meth_name: String,
    trait_name: &str,
    req_constraint_name: &str,
    req_constraint_kind: primary::StaticCallOnTraitRequireNonStrictReqConstraintKind,
    trait_pos: PosOrDecl,
) -> T {
    let trait_name = strip_ns(trait_name).to_string();
    let req_constraint_name = strip_ns(req_constraint_name).to_string();
    match req_constraint_kind {
        primary::StaticCallOnTraitRequireNonStrictReqConstraintKind::class_ => create(
            ErrorCode::StaticCallOnTraitRequireClass,
            lazy!(Message(
                call_pos,
                [
                    "Invoking static methods on traits is dangerous and must be avoided. Since trait ",
                    &trait_name,
                    " has a ",
                    &md_codify(&["require class ", &req_constraint_name].concat()),
                    " constraint, replace ",
                    &md_codify(&[&trait_name, "::", &meth_name, "(...)"].concat()),
                    " with ",
                    &md_codify(&[&req_constraint_name, "::", &meth_name, "(...)"].concat()),
                    ".",
                ]
                .concat().into(),
            )),
            None,
            None,
        ),
        primary::StaticCallOnTraitRequireNonStrictReqConstraintKind::this_as => {
            let claim = {
                let trait_name = trait_name.clone();
                lazy!(Message(
                    call_pos,
                    [
                        "Invoking static methods on traits is dangerous and is forbidden on trait ",
                        &trait_name,
                        " because it has a ",
                        &md_codify(&["require this as ", &req_constraint_name].concat()),
                        " constraint.",
                    ]
                    .concat().into(),
                ))
            };
            create(
                ErrorCode::StaticCallOnTraitRequireThisAs,
                claim,
                Some(lazy!(vec![Message(
                    trait_pos,
                    format!("{} is defined here", trait_name).into(),
                )])),
                None,
            )
        }
    }
}

pub fn static_prop_on_trait(
    call_pos: Pos,
    prop_name: &str,
    trait_name: &str,
    trait_pos: PosOrDecl,
) -> T {
    let trait_name = strip_ns(trait_name).to_string();
    let trait_prop = md_codify(&format!("{}::{}", utils_strip_ns(&trait_name), prop_name));
    create(
        ErrorCode::StaticPropOnTrait,
        lazy!(Message(
            call_pos,
            format!("Static property access on a trait: {}", trait_prop).into(),
        )),
        Some(lazy!(vec![Message(
            trait_pos,
            format!("{} is defined here", trait_name).into(),
        )])),
        None,
    )
}

pub fn isset_in_strict(pos: Pos) -> T {
    create(
        ErrorCode::IssetEmptyInStrict,
        lazy!(Message(
            pos,
            [
                "`isset` tends to hide errors due to variable typos and so is limited to dynamic checks in ",
                "`strict` mode",
            ]
            .concat().into(),
        )),
        None,
        None,
    )
}

pub fn isset_inout_arg(pos: Pos) -> T {
    create(
        ErrorCode::InoutInPseudofunction,
        lazy!(Message(
            pos,
            "`isset` does not allow arguments to be passed by `inout`".into(),
        )),
        None,
        None,
    )
}

pub fn unset_nonidx_in_strict(pos: Pos, reasons: Reasons) -> T {
    create(
        ErrorCode::UnsetNonidxInStrict,
        lazy!(Message(
            pos,
            [
                "In `strict` mode, `unset` is banned except on dynamic, ",
                "darray, keyset, or dict indexing",
            ]
            .concat()
            .into(),
        )),
        Some(reasons),
        None,
    )
}

pub fn unpacking_disallowed_builtin_function(pos: Pos, name: String) -> T {
    create(
        ErrorCode::UnpackingDisallowed,
        lazy!(Message(
            pos,
            [
                "Arg unpacking is disallowed for ",
                &md_codify(strip_ns(&name)),
            ]
            .concat()
            .into(),
        )),
        None,
        None,
    )
}

pub fn array_get_arity(pos1: Pos, name: String, pos2: PosOrDecl) -> T {
    create(
        ErrorCode::ArrayGetArity,
        lazy!(Message(
            pos1,
            ["You cannot use this ", &md_codify(strip_ns(&name))]
                .concat()
                .into(),
        )),
        Some(lazy!(vec![Message(
            pos2,
            "It is missing its type parameters".into(),
        )])),
        None,
    )
}

pub fn undefined_field(use_pos: Pos, name: String, shape_type_pos: PosOrDecl) -> T {
    let claim = lazy!(Message(
        use_pos,
        ["This shape doesn't have a field ", &md_codify(&name)]
            .concat()
            .into(),
    ));
    let reasons = lazy!(vec![Message(
        shape_type_pos,
        "The shape is defined here".into()
    )]);
    create(ErrorCode::UndefinedField, claim, Some(reasons), None)
}

pub fn array_access(code: ErrorCode, pos1: Pos, pos2: PosOrDecl, ty: String) -> T {
    create(
        code,
        lazy!(Message(
            pos1,
            [
                "This is not an object of type `KeyedContainer`, this is ",
                &ty,
            ]
            .concat()
            .into(),
        )),
        Some(lazy!(if !pos2.is_none() {
            vec![Message(pos2, "Definition is here".into())]
        } else {
            vec![]
        })),
        None,
    )
}

pub fn array_access_read(pos1: Pos, pos2: PosOrDecl, ty: String) -> T {
    array_access(ErrorCode::ArrayAccessRead, pos1, pos2, ty)
}

pub fn array_access_write(pos1: Pos, pos2: PosOrDecl, ty: String) -> T {
    array_access(ErrorCode::ArrayAccessWrite, pos1, pos2, ty)
}

pub fn keyset_set(pos1: Pos, pos2: PosOrDecl) -> T {
    let claim = lazy!(Message(
        pos1,
        "Elements in a keyset cannot be assigned, use append instead.".into(),
    ));
    let reasons = lazy!(if !pos2.is_none() {
        vec![Message(pos2, "Definition is here".into())]
    } else {
        vec![]
    });
    create(ErrorCode::KeysetSet, claim, Some(reasons), None)
}

pub fn array_append(pos1: Pos, pos2: PosOrDecl, ty: String) -> T {
    let claim = lazy!(Message(
        pos1,
        [&ty, " does not allow array append"].concat().into()
    ));
    let reasons = lazy!(if !pos2.is_none() {
        vec![Message(pos2, "Definition is here".into())]
    } else {
        vec![]
    });
    create(ErrorCode::ArrayAppend, claim, Some(reasons), None)
}

pub fn const_mutation(pos1: Pos, pos2: PosOrDecl, ty: String) -> T {
    let claim = lazy!(Message(pos1, "You cannot mutate this".into()));
    let reasons = lazy!(if !pos2.is_none() {
        vec![Message(pos2, ["This is ", &ty].concat().into())]
    } else {
        vec![]
    });
    create(ErrorCode::ConstMutation, claim, Some(reasons), None)
}

pub fn expected_class(pos: Pos, suffix: String) -> T {
    create(
        ErrorCode::ExpectedClass,
        lazy!(Message(
            pos,
            ["Was expecting a class", &suffix].concat().into()
        )),
        None,
        None,
    )
}

pub fn unknown_type(pos: Pos, description: String, reasons: Reasons) -> T {
    let claim = lazy!(Message(
        pos,
        ["Was expecting ", &description, " but type is unknown"]
            .concat()
            .into(),
    ));
    create(ErrorCode::UnknownType, claim, Some(reasons), None)
}

pub fn parent_in_trait(pos: Pos) -> T {
    create(
        ErrorCode::ParentInTrait,
        lazy!(Message(
            pos,
            [
                "You can only use `parent::` in traits that `require extends`, `require class` ",
                "or `require this as` a valid class",
            ]
            .concat()
            .into(),
        )),
        None,
        None,
    )
}

pub fn parent_undefined(pos: Pos, trait_reqs: Option<Vec<PosOrDecl>>) -> T {
    let claim = lazy!(Message(pos, "parent is undefined".into()));
    let reasons = match trait_reqs {
        Some(reqs) => lazy!(
            reqs.into_iter()
                .map(|p| Message(p, "The class required here has no parent".into()))
                .collect::<Vec<_>>()
        ),
        None => lazy!(vec![]),
    };
    create(ErrorCode::ParentUndefined, claim, Some(reasons), None)
}

pub fn constructor_no_args(pos: Pos) -> T {
    create(
        ErrorCode::ConstructorNoArgs,
        lazy!(Message(pos, "This constructor expects no argument".into())),
        None,
        None,
    )
}

pub fn visibility(p: Pos, msg1: String, p_vis: PosOrDecl, msg2: String) -> T {
    let claim = lazy!(Message(p, msg1.into()));
    let reasons = lazy!(vec![Message(p_vis, msg2.into())]);
    create(ErrorCode::Visibility, claim, Some(reasons), None)
}

pub fn bad_call(pos: Pos, ty: String) -> T {
    create(
        ErrorCode::BadCall,
        lazy!(Message(
            pos,
            ["This call is invalid, this is not a function, it is ", &ty,]
                .concat()
                .into(),
        )),
        None,
        None,
    )
}

pub fn extend_final(extend_pos: Pos, decl_pos: PosOrDecl, name: String) -> T {
    let claim = lazy!(Message(
        extend_pos,
        [
            "You cannot extend final class ",
            &md_codify(strip_ns(&name)),
        ]
        .concat()
        .into(),
    ));
    let reasons = lazy!(vec![Message(decl_pos, "Declaration is here".into())]);
    create(ErrorCode::ExtendFinal, claim, Some(reasons), None)
}

pub fn extend_sealed(
    child_pos: Pos,
    parent_pos: PosOrDecl,
    parent_name: String,
    parent_kind: primary::ExtendSealedParentKind,
    verb: primary::ExtendSealedVerb,
) -> T {
    let claim = lazy!({
        let parent_kind = match parent_kind {
            primary::ExtendSealedParentKind::intf => "interface",
            primary::ExtendSealedParentKind::trait_ => "trait",
            primary::ExtendSealedParentKind::class_ => "class",
            primary::ExtendSealedParentKind::enum_ => "enum",
            primary::ExtendSealedParentKind::enum_class => "enum class",
        };
        let verb = match verb {
            primary::ExtendSealedVerb::extend => "extend",
            primary::ExtendSealedVerb::implement => "implement",
            primary::ExtendSealedVerb::use_ => "use",
        };
        let name = strip_ns(&parent_name);
        Message(
            child_pos,
            [
                "You cannot ",
                verb,
                " sealed ",
                parent_kind,
                " ",
                &md_codify(name),
            ]
            .concat()
            .into(),
        )
    });
    let reasons = lazy!(vec![Message(parent_pos, "Declaration is here".into())]);
    create(ErrorCode::ExtendSealed, claim, Some(reasons), None)
}

pub fn trait_prop_const_class(pos: Pos, x: String) -> T {
    create(
        ErrorCode::TraitPropConstClass,
        lazy!(Message(
            pos,
            [
                "Trait declaration of non-const property ",
                &md_codify(&x),
                " is incompatible with a const class",
            ]
            .concat()
            .into(),
        )),
        None,
        None,
    )
}

pub fn implement_abstract(
    pos1: Pos,
    is_final: bool,
    pos2: PosOrDecl,
    x: String,
    kind: primary::ImplementAbstractKind,
    quickfixes: Vec<Quickfix<Pos>>,
    trace: Reasons,
) -> T {
    let kind = match kind {
        primary::ImplementAbstractKind::meth => "method",
        primary::ImplementAbstractKind::prop => "property",
        primary::ImplementAbstractKind::const_ => "constant",
        primary::ImplementAbstractKind::ty_const => "type constant",
    };
    let claim = lazy!({
        let name = ["abstract ", kind, " ", &md_codify(&x)].concat();
        let msg1 = if is_final {
            [
                "This class was declared as `final`. It must provide an implementation for the ",
                &name,
            ]
            .concat()
        } else {
            [
                "This class must be declared `abstract`, or provide an implementation for the ",
                &name,
            ]
            .concat()
        };
        Message(pos1, msg1.into())
    });
    let reasons = lazy!({
        let mut reasons = trace.force().clone();
        reasons.push(Message(
            pos2,
            format!("The {} is defined here", kind).into(),
        ));
        reasons
    });
    create(
        ErrorCode::ImplementAbstract,
        claim,
        Some(reasons),
        Some(quickfixes),
    )
}

pub fn abstract_member_in_concrete_class(
    member_pos: Pos,
    class_name_pos: Pos,
    is_final: bool,
    member_kind: primary::AbstractMemberInConcreteClassMemberKind,
    member_name: String,
) -> T {
    let claim = lazy!(Message(
        member_pos,
        format!(
            "{} `{}{}` is abstract but the class is {}. Either provide an implementation here.",
            match member_kind {
                primary::AbstractMemberInConcreteClassMemberKind::method_ => "Method",
                primary::AbstractMemberInConcreteClassMemberKind::property => "Property",
                primary::AbstractMemberInConcreteClassMemberKind::constant => "Constant",
                primary::AbstractMemberInConcreteClassMemberKind::type_constant => "Type constant",
            },
            match member_kind {
                primary::AbstractMemberInConcreteClassMemberKind::property => "$",
                _ => "",
            },
            member_name,
            if is_final { "final" } else { "concrete" }
        )
        .into(),
    ));
    let reasons = lazy!({
        let class_name_pos: PosOrDecl = class_name_pos;
        vec![Message(
            class_name_pos,
            format!(
                "Or make the class abstract{}.",
                if is_final { " and not final" } else { "" }
            )
            .into(),
        )]
    });
    create(
        ErrorCode::AbstractMemberInConcreteClass,
        claim,
        Some(reasons),
        None,
    )
}

pub fn generic_static(pos: Pos, x: String) -> T {
    create(
        ErrorCode::GenericStatic,
        lazy!(Message(
            pos,
            [
                "This static variable cannot use the type parameter ",
                &md_codify(&x),
                ".",
            ]
            .concat()
            .into(),
        )),
        None,
        None,
    )
}

pub fn object_string(pos1: Pos, pos2: PosOrDecl) -> T {
    let claim = lazy!(Message(
        pos1,
        "You cannot use this object as a string".into()
    ));
    let reasons = lazy!(vec![Message(
        pos2,
        "This object doesn't implement `__toString`".into(),
    )]);
    create(ErrorCode::ObjectString, claim, Some(reasons), None)
}

pub fn object_string_deprecated(pos: Pos) -> T {
    create(
        ErrorCode::ObjectString,
        lazy!(Message(
            pos,
            "You cannot use this object as a string\nImplicit conversions of Stringish objects to string are deprecated.".into(),
        )),
        None,
        None,
    )
}

pub fn cyclic_typedef(def_pos: Pos, use_pos: PosOrDecl) -> T {
    let claim = lazy!(Message(def_pos, "Cyclic type definition".into()));
    let reasons = lazy!(vec![Message(use_pos, "Cyclic use is here".into())]);
    create(ErrorCode::CyclicTypedef, claim, Some(reasons), None)
}

pub fn require_args_reify(arg_pos: Pos, def_pos: PosOrDecl) -> T {
    let claim = lazy!(Message(
        arg_pos,
        "All type arguments must be specified because a type parameter is reified".into(),
    ));
    let reasons = lazy!(vec![Message(def_pos, "Definition is here".into())]);
    create(ErrorCode::RequireArgsReify, claim, Some(reasons), None)
}

pub fn require_generic_explicit(arg_pos: Pos, def_pos: PosOrDecl, def_name: String) -> T {
    let claim = lazy!(Message(
        arg_pos,
        [
            "Illegal wildcard (`_`): generic type parameter ",
            &md_codify(&def_name),
            " must be specified explicitly",
        ]
        .concat()
        .into(),
    ));
    let reasons = lazy!(vec![Message(def_pos, "Definition is here".into())]);
    create(
        ErrorCode::RequireGenericExplicit,
        claim,
        Some(reasons),
        None,
    )
}

pub fn invalid_reified_argument(
    hint_pos: Pos,
    def_name: String,
    def_pos: PosOrDecl,
    arg_info: Reasons,
) -> T {
    let claim = lazy!(Message(hint_pos, "Invalid reified hint".into()));
    let reasons = lazy!({
        let arg_info = arg_info.force();
        let Message(arg_pos, arg_kind) = match arg_info.first() {
            Some(hd) => hd.clone(),
            None => panic!("List.hd_exn"),
        };
        vec![
            Message(
                arg_pos,
                [
                    b"This is ".as_slice(),
                    arg_kind.as_slice(),
                    b", it cannot be used as a reified type argument",
                ]
                .concat()
                .into(),
            ),
            Message(
                def_pos,
                [&md_codify(&def_name), " is reified"].concat().into(),
            ),
        ]
    });
    create(
        ErrorCode::InvalidReifiedArgument,
        claim,
        Some(reasons),
        None,
    )
}

pub fn invalid_reified_argument_reifiable(
    arg_pos: Pos,
    def_name: String,
    def_pos: PosOrDecl,
    ty_pos: PosOrDecl,
    ty_msg: String,
) -> T {
    let claim = lazy!(Message(
        arg_pos,
        "PHP arrays cannot be used as a reified type argument".into(),
    ));
    let reasons = lazy!(vec![
        Message(ty_pos, string_capitalize(&ty_msg).into()),
        Message(
            def_pos,
            [&md_codify(&def_name), " is reified"].concat().into()
        ),
    ]);
    create(
        ErrorCode::InvalidReifiedArgument,
        claim,
        Some(reasons),
        None,
    )
}

pub fn new_class_reified(pos: Pos, class_type: String, suggested_class: Option<String>) -> T {
    let claim = lazy!({
        let suggestion = match suggested_class {
            Some(s) => {
                let s = strip_ns(&s);
                format!(". Try `new {}` instead.", s)
            }
            None => "".to_string(),
        };
        Message(
            pos,
            format!(
                "Cannot call `new {}` because the current class has reified generics{}",
                class_type, suggestion
            )
            .into(),
        )
    });
    create(ErrorCode::NewClassReified, claim, None, None)
}

pub fn class_get_reified(pos: Pos) -> T {
    create(
        ErrorCode::ClassGetReified,
        lazy!(Message(
            pos,
            "Cannot access static properties on reified generics".into(),
        )),
        None,
        None,
    )
}

pub fn static_meth_with_class_reified_generic(meth_pos: Pos, generic_pos: Pos) -> T {
    let claim = lazy!(Message(
        meth_pos,
        "Static methods cannot use generics reified at the class level. Try reifying them at the static method itself.".into(),
    ));
    let reasons = lazy!({
        let generic_pos: PosOrDecl = generic_pos;
        vec![Message(
            generic_pos,
            "Class-level reified generic used here.".into(),
        )]
    });
    create(
        ErrorCode::StaticMethWithClassReifiedGeneric,
        claim,
        Some(reasons),
        None,
    )
}

pub fn consistent_construct_reified(pos: Pos) -> T {
    create(
        ErrorCode::ConsistentConstructReified,
        lazy!(Message(
            pos,
            "This class or one of its ancestors is annotated with `<<__ConsistentConstruct>>`. It cannot have reified generics.".into(),
        )),
        None,
        None,
    )
}

pub fn bad_function_pointer_construction(pos: Pos) -> T {
    create(
        ErrorCode::BadFunctionPointerConstruction,
        lazy!(Message(
            pos,
            "Function pointers must be explicitly named".into()
        )),
        None,
        None,
    )
}

pub fn reified_generics_not_allowed(pos: Pos) -> T {
    create(
        ErrorCode::InvalidReifiedFunctionPointer,
        lazy!(Message(
            pos,
            "Creating function pointers with reified generics is not currently allowed".into(),
        )),
        None,
        None,
    )
}

pub fn new_without_newable(pos: Pos, name: String) -> T {
    create(
        ErrorCode::NewWithoutNewable,
        lazy!(Message(
            pos,
            [
                &md_codify(&name),
                " cannot be used with `new` because it does not have the `<<__Newable>>` attribute",
            ]
            .concat()
            .into(),
        )),
        None,
        None,
    )
}

pub fn discarded_awaitable(pos1: Pos, pos2: PosOrDecl) -> T {
    let claim = lazy!(Message(
        pos1,
        [
            "This expression is of type `Awaitable`, but it's ",
            "either being discarded or used in a dangerous way before ",
            "being awaited",
        ]
        .concat()
        .into(),
    ));
    let reasons = lazy!(vec![Message(
        pos2,
        "This is why I think it is `Awaitable`".into(),
    )]);
    // We add a quickfix for this error in Quickfixes_from_refactors
    create(ErrorCode::DiscardedAwaitable, claim, Some(reasons), None)
}

pub fn elt_type_to_string(elt: primary::MethOrProp) -> &'static str {
    match elt {
        primary::MethOrProp::meth => "method",
        primary::MethOrProp::prop => "property",
    }
}

pub fn unknown_object_member(pos: Pos, s: String, elt: primary::MethOrProp, reasons: Reasons) -> T {
    let claim = lazy!({
        let elt = elt_type_to_string(elt);
        let msg = format!(
            "You are trying to access the {} {} on a value whose class is unknown.",
            elt,
            md_codify(&s)
        );
        Message(pos, msg.into())
    });
    create(ErrorCode::UnknownObjectMember, claim, Some(reasons), None)
}

pub fn non_class_member(
    pos1: Pos,
    s: String,
    elt: primary::MethOrProp,
    ty: String,
    pos2: PosOrDecl,
) -> T {
    let claim = lazy!({
        let elt = elt_type_to_string(elt);
        let msg = format!(
            "You are trying to access the static {} {} but this is {}",
            elt,
            md_codify(&s),
            ty
        );
        Message(pos1, msg.into())
    });
    let reasons = lazy!(vec![Message(pos2, "Definition is here".into())]);
    create(ErrorCode::NonClassMember, claim, Some(reasons), None)
}

pub fn null_container(p: Pos, reasons: Reasons) -> T {
    let claim = lazy!(Message(
        p,
        [
            "You are trying to access an element of this container",
            " but the container could be `null`. ",
        ]
        .concat()
        .into(),
    ));
    create(ErrorCode::NullContainer, claim, Some(reasons), None)
}

pub fn declared_covariant(pos1: Pos, pos2: Pos, emsg: Lazy<Vec<Message<Pos>>>) -> T {
    let claim = lazy!(Message(
        pos2,
        "Illegal usage of a covariant type parameter".into()
    ));
    let reasons = lazy!({
        let emsg = emsg.force();
        let pos1: PosOrDecl = pos1;
        let mut reasons = vec![Message(
            pos1,
            "This is where the parameter was declared as covariant `+`".into(),
        )];
        reasons.extend(emsg.iter().map(|Message(pos, msg)| {
            let pos: PosOrDecl = pos.clone();
            Message(pos, msg.clone())
        }));
        reasons
    });
    create(ErrorCode::DeclaredCovariant, claim, Some(reasons), None)
}

pub fn declared_contravariant(pos1: Pos, pos2: Pos, emsg: Lazy<Vec<Message<Pos>>>) -> T {
    let claim = lazy!(Message(
        pos2,
        "Illegal usage of a contravariant type parameter".into(),
    ));
    let reasons = lazy!({
        let emsg = emsg.force();
        let pos1: PosOrDecl = pos1;
        let mut reasons = vec![Message(
            pos1,
            "This is where the parameter was declared as contravariant `-`".into(),
        )];
        reasons.extend(emsg.iter().map(|Message(pos, msg)| {
            let pos: PosOrDecl = pos.clone();
            Message(pos, msg.clone())
        }));
        reasons
    });
    create(ErrorCode::DeclaredContravariant, claim, Some(reasons), None)
}

pub fn static_property_type_generic_param(
    generic_pos: Pos,
    class_pos: PosOrDecl,
    var_type_pos: PosOrDecl,
) -> T {
    let claim = lazy!(Message(
        generic_pos,
        "A generic parameter cannot be used in the type of a static property".into(),
    ));
    let reasons = lazy!(vec![
        Message(
            var_type_pos,
            "This is where the type of the static property was declared".into(),
        ),
        Message(
            class_pos,
            "This is the class containing the static property".into(),
        ),
    ]);
    create(
        ErrorCode::ClassVarTypeGenericParam,
        claim,
        Some(reasons),
        None,
    )
}

pub fn contravariant_this(pos: Pos, class_name: String, tp: String) -> T {
    create(
        ErrorCode::ContravariantThis,
        lazy!(Message(
            pos,
            [
                "The `this` type cannot be used in this ",
                "contravariant position because its enclosing class ",
                &md_codify(&class_name),
                " ",
                "is final and has a variant type parameter ",
                &md_codify(&tp),
            ]
            .concat()
            .into(),
        )),
        None,
        None,
    )
}

pub fn cyclic_typeconst(pos: Pos, sl: Vec<String>) -> T {
    let claim = lazy!({
        let sl: Vec<String> = sl.iter().map(|s| md_codify(strip_ns(s))).collect();
        Message(
            pos,
            ["Cyclic type constant:\n  ", &sl.join(" -> ")]
                .concat()
                .into(),
        )
    });
    create(ErrorCode::CyclicTypeconst, claim, None, None)
}

pub fn array_get_with_optional_field(
    field_pos: Pos,
    recv_pos: &Pos,
    decl_pos: PosOrDecl,
    name: String,
) -> T {
    let (_, recv_end_col) = crate::pos::end_line_column(recv_pos);
    let open_bracket_pos = crate::pos::set_col_end(
        recv_end_col + 1,
        &crate::pos::set_col_start(recv_end_col, recv_pos),
    );
    let (_, field_end_col) = crate::pos::end_line_column(&field_pos);
    let close_bracket_pos = crate::pos::set_col_end(
        field_end_col + 1,
        &crate::pos::set_col_start(field_end_col, &field_pos),
    );

    let quickfixes = {
        let edits = Edits::Eager(vec![
            (")".to_string(), close_bracket_pos),
            (", ".to_string(), open_bracket_pos),
            (
                "Shapes::idx(".to_string(),
                crate::pos::shrink_to_start(recv_pos),
            ),
        ]);
        vec![crate::quickfix::make(
            "Change to `Shapes::idx()`".to_string(),
            edits,
            vec![],
        )]
    };
    let claim = lazy!(Message(
        field_pos,
        format!(
            "The field {} may not be present in this shape. Use `??` or `Shapes::idx()` instead.",
            md_codify(&name)
        )
        .into(),
    ));
    let reasons = lazy!(vec![Message(
        decl_pos,
        "This is where the field was declared as optional.".into(),
    )]);
    create(
        ErrorCode::ArrayGetWithOptionalField,
        claim,
        Some(reasons),
        Some(quickfixes),
    )
}

pub fn mutating_const_property(pos: Pos) -> T {
    create(
        ErrorCode::AssigningToConst,
        lazy!(Message(pos, "Cannot mutate a `__Const` property".into())),
        None,
        None,
    )
}

pub fn self_const_parent_not(pos: Pos) -> T {
    create(
        ErrorCode::SelfConstParentNot,
        lazy!(Message(
            pos,
            "A `__Const` class may only extend other `__Const` classes".into(),
        )),
        None,
        None,
    )
}

pub fn unexpected_ty_in_tast(pos: Pos, actual_ty: String, expected_ty: String) -> T {
    create(
        ErrorCode::UnexpectedTy,
        lazy!(Message(
            pos,
            [
                "Unexpected type in TAST: expected ",
                &md_codify(&expected_ty),
                ", got ",
                &md_codify(&actual_ty),
            ]
            .concat()
            .into(),
        )),
        None,
        None,
    )
}

pub fn call_lvalue(pos: Pos) -> T {
    create(
        ErrorCode::CallLvalue,
        lazy!(Message(
            pos,
            "Array updates cannot be applied to function results. Use a local variable instead."
                .into(),
        )),
        None,
        None,
    )
}

pub fn unsafe_cast_await(pos: Pos) -> T {
    create(
        ErrorCode::UnsafeCastAwait,
        lazy!(Message(
            pos,
            "UNSAFE_CAST cannot be used as the operand of an await operation".into(),
        )),
        None,
        None,
    )
}

pub fn match_not_exhaustive(pos: Pos, ty: String) -> T {
    let backticks = |ty: &str| ["`", ty, "`"].concat();
    create(
        ErrorCode::MatchNotExhaustive,
        lazy!(Message(
            pos,
            [
                "This match statement is not exhaustive: there is no arm matching values of type ",
                &backticks(&ty),
            ]
            .concat()
            .into(),
        )),
        None,
        None,
    )
}

pub fn match_on_unsupported_type(pos: Pos, expr_ty: String, unsupported_tys: Vec<String>) -> T {
    let backticks = |ty: &str| ["`", ty, "`"].concat();
    create(
        ErrorCode::MatchOnUnsupportedType,
        lazy!(Message(
            pos,
            [
                "This expression has type ",
                &backticks(&expr_ty),
                ", which is not supported in match statements",
                &(match &unsupported_tys[..] {
                    [] => "".to_string(),
                    [ty] if *ty == expr_ty => "".to_string(),
                    [ty] => [" because it contains the type ", &backticks(ty)].concat(),
                    _ => [
                        " because it contains the following types: ",
                        &unsupported_tys
                            .iter()
                            .map(|ty| backticks(ty))
                            .collect::<Vec<_>>()
                            .join(", "),
                    ]
                    .concat(),
                }),
            ]
            .concat()
            .into(),
        )),
        None,
        None,
    )
}

pub fn class_const_to_string(pos: Pos, cid_str: &str) -> T {
    let cid_str = utils_strip_ns(cid_str).to_string();
    let nameof = ["nameof ", &cid_str].concat();
    let nameof_md = md_codify(&nameof);
    let quickfixes = vec![crate::quickfix::make_eager_default_hint_style(
        ["Change to ", &nameof_md].concat(),
        nameof,
        pos.clone(),
    )];
    let claim = lazy!(Message(
        pos,
        [
            "Using `",
            &cid_str,
            "::class` in this position will trigger an implicit runtime conversion to string, please use ",
            &nameof_md,
        ]
        .concat().into(),
    ));
    create(
        ErrorCode::ClassPointerToString,
        claim,
        None,
        Some(quickfixes),
    )
}

pub fn class_pointer_to_string(pos: Pos, ty: String) -> T {
    let class_to_classname = "HH\\class_to_classname";
    let class_to_classname_md = md_codify(class_to_classname);
    create(
        ErrorCode::ClassPointerToString,
        lazy!(Message(
            pos,
            [
                "Using ",
                &ty,
                " in this position will trigger an implicit runtime conversion to string. ",
                "You may use ",
                &class_to_classname_md,
                " to get the class name as a string.",
            ]
            .concat()
            .into(),
        )),
        None,
        None,
    )
}

pub fn string_to_class_pointer(pos: Pos, cls_name: &str, ty_pos: PosOrDecl) -> T {
    let cls_name = utils_strip_ns(cls_name);
    let classname_ty = format!("classname<{}>", cls_name);
    let classname_ty_md = md_codify(&classname_ty);
    let class_ptr_ty = format!("class<{}>", cls_name);
    let class_ptr_ty_md = md_codify(&class_ptr_ty);
    create(
        ErrorCode::ClassPointerToString,
        lazy!(Message(
            pos,
            [
                "It is no longer allowed to use a ",
                &classname_ty_md,
                " in this position. Please use a ",
                &class_ptr_ty_md,
                " instead.",
            ]
            .concat()
            .into(),
        )),
        Some(lazy!(vec![Message(ty_pos, "Definition is here".into())])),
        None,
    )
}

/// `val to_error : Typing_error.Primary.t -> env:'a -> t`: nothing looks at the
/// environment (every nested `to_error` is `~env:_`), and its type is free in
/// OCaml too.
///
/// Where an arm forces several lazy values to call a function, they are
/// forced from the last argument to the first: OCaml leaves the order
/// unspecified, and that is the order its compilers use.
pub fn to_error(t: primary::T, env: &crate::typing_env_types::Env) -> T {
    use primary::T::*;
    match t {
        Coeffect(err) => eval_coeffect::to_error(err, env),
        Enum(err) => eval_enum::to_error(err, env),
        Expr_tree(err) => eval_expr_tree::to_error(err, env),
        Modules(err) => eval_modules::to_error(err, env),
        Package(err) => eval_package::to_error(err, env),
        Readonly(err) => eval_readonly::to_error(err, env),
        Shape(err) => eval_shape::to_error(err, env),
        Shape_and_tuple_destructure(err) => eval_destructure::to_error(err, env),
        Switch(err) => eval_switch::to_error(err, env),
        Wellformedness(err) => eval_wellformedness::to_error(err, env),
        Xhp(err) => eval_xhp::to_error(err, env),
        CaseType(err) => eval_casetype::to_error(err, env),
        SimpliHack(err) => eval_simplihack::to_error(err, env),
        Unify_error {
            pos,
            msg_opt,
            reasons_opt,
        } => unify_error(pos, msg_opt, reasons_opt),
        Generic_unify { pos, msg } => generic_unify(pos, msg),
        Unresolved_tyvar(pos) => unresolved_tyvar(pos),
        Using_error { pos, has_await } => using_error(pos, has_await),
        Bad_enum_decl(pos) => bad_enum_decl(pos),
        Bad_conditional_support_dynamic {
            pos,
            child,
            parent,
            ty_name,
            self_ty_name,
        } => bad_conditional_support_dynamic(pos, child, parent, ty_name, self_ty_name),
        Bad_decl_override {
            pos,
            name,
            parent_name,
        } => bad_decl_override(&name, pos, &parent_name),
        Explain_where_constraint {
            pos,
            decl_pos,
            in_class,
        } => explain_where_constraint(pos, decl_pos, in_class),
        Explain_constraint(pos) => explain_constraint(pos),
        Rigid_tvar_escape { pos, what } => rigid_tvar_escape(pos, what),
        Invalid_type_hint(pos) => invalid_type_hint(pos),
        Shape_splat(err) => eval_shape_splat::to_error(err, env),
        Gated_by_feature_flag { pos, name, feature } => {
            let claim = lazy!(Message(
                pos,
                format!(
                    "`{}` requires the unstable feature `{}`. Add `<<file: __EnableUnstableFeatures('{}')>>` to use it.",
                    utils_strip_ns(&name),
                    feature,
                    feature
                )
                .into(),
            ));
            create(ErrorCode::GatedByFeatureFlag, claim, None, None)
        }
        Tests_bypass_visibility_on_member_without_class {
            pos,
            member_name,
            class_name,
        } => {
            let claim = lazy!(Message(
                pos,
                format!(
                    "`{}` has `<<__TestsBypassVisibility>>` but its containing `internal` class `{}` does not",
                    member_name,
                    utils_strip_ns(&class_name)
                )
                .into(),
            ));
            create(
                ErrorCode::TestsBypassVisibilityOnMemberWithoutClass,
                claim,
                None,
                None,
            )
        }
        Unsatisfied_req {
            pos,
            trait_pos,
            req_name,
            req_pos,
        } => unsatisfied_req(pos, trait_pos, req_name, req_pos),
        Unsatisfied_req_class {
            pos,
            trait_pos,
            req_name,
            req_pos,
        } => unsatisfied_req_class(pos, trait_pos, req_name, req_pos),
        Unsatisfied_req_this_as {
            pos,
            trait_pos,
            req_name,
            req_pos,
        } => unsatisfied_req_this_as(pos, trait_pos, req_name, req_pos),
        Incompatible_reqs {
            pos,
            req_name,
            req_class_pos,
            req_extends_pos,
        } => incompatible_reqs(pos, req_name, req_class_pos, req_extends_pos),
        Trait_not_used {
            pos,
            trait_name,
            req_class_pos,
            class_pos,
            class_name,
            req_constraint_kind,
        } => trait_not_used(
            pos,
            trait_name,
            req_class_pos,
            class_pos,
            &class_name,
            req_constraint_kind,
        ),
        Invalid_echo_argument(pos) => invalid_echo_argument(pos),
        Index_type_mismatch {
            pos,
            is_covariant_container,
            msg_opt,
            reasons_opt,
        } => index_type_mismatch(pos, is_covariant_container, msg_opt, reasons_opt),
        Member_not_found {
            pos,
            kind,
            member_name,
            class_name,
            class_pos,
            hint,
            reason,
        } => member_not_found(
            pos,
            kind,
            member_name,
            class_name,
            class_pos,
            hint.force().clone(),
            reason,
        ),
        Construct_not_instance_method(pos) => construct_not_instance_method(pos),
        Ambiguous_inheritance {
            pos,
            origin,
            class_name,
        } => ambiguous_inheritance(pos, origin, class_name),
        Expected_tparam { pos, n, decl_pos } => expected_tparam(pos, n, decl_pos),
        Typeconst_concrete_concrete_override { pos, decl_pos } => {
            typeconst_concrete_concrete_override(pos, decl_pos)
        }
        Constant_multiple_concrete_conflict {
            pos,
            name,
            definitions,
        } => constant_multiple_concrete_conflict(pos, name, definitions),
        Invalid_memoized_param { pos, reason, .. } => invalid_memoized_param(pos, reason),
        Invalid_arraykey {
            pos,
            container_pos,
            container_ty_name,
            key_pos,
            key_ty_name,
            ctxt,
        } => {
            let key_ty_name = key_ty_name.force().clone();
            let container_ty_name = container_ty_name.force().clone();
            invalid_arraykey(
                pos,
                container_pos,
                container_ty_name,
                key_pos,
                key_ty_name,
                ctxt,
            )
        }
        Invalid_keyset_value {
            pos,
            container_pos,
            container_ty_name,
            value_pos,
            value_ty_name,
        } => {
            let value_ty_name = value_ty_name.force().clone();
            let container_ty_name = container_ty_name.force().clone();
            invalid_keyset_value(
                pos,
                container_pos,
                container_ty_name,
                value_pos,
                value_ty_name,
            )
        }
        Invalid_set_value {
            pos,
            container_pos,
            container_ty_name,
            value_pos,
            value_ty_name,
        } => {
            let value_ty_name = value_ty_name.force().clone();
            let container_ty_name = container_ty_name.force().clone();
            invalid_set_value(
                pos,
                container_pos,
                container_ty_name,
                value_pos,
                value_ty_name,
            )
        }
        Object_string_deprecated(pos) => object_string_deprecated(pos),
        Invalid_substring { pos, ty_name } => invalid_substring(pos, ty_name),
        Unset_nonidx_in_strict { pos, reason } => unset_nonidx_in_strict(pos, reason),
        Nullable_cast {
            pos,
            ty_pos,
            ty_name,
        } => nullable_cast(pos, ty_pos, ty_name),
        Hh_expect { pos, equivalent } => hh_expect(pos, equivalent),
        Null_member {
            pos,
            obj_pos_opt,
            ctxt,
            kind,
            member_name,
            reason,
        } => null_member(pos, obj_pos_opt.as_ref(), ctxt, kind, member_name, reason),
        Typing_too_many_args {
            pos,
            decl_pos,
            actual,
            expected,
        } => typing_too_many_args(pos, decl_pos, actual, expected),
        Typing_too_few_args {
            pos,
            decl_pos,
            actual,
            expected,
            hint_missing_optional,
        } => typing_too_few_args(pos, decl_pos, actual, expected, hint_missing_optional),
        Missing_named_args {
            pos,
            decl_pos,
            missing_names,
        } => missing_named_args(pos, decl_pos, missing_names),
        Unexpected_named_args {
            pos,
            decl_pos,
            unexpected_names,
        } => unexpected_named_args(pos, decl_pos, unexpected_names),
        Duplicate_named_args {
            pos,
            duplicate_names,
        } => duplicate_named_args(pos, duplicate_names),
        Non_object_member {
            pos,
            ctxt,
            ty_name,
            member_name,
            kind,
            decl_pos,
        } => non_object_member(pos, ctxt, &ty_name, member_name, kind, decl_pos),
        Static_instance_intersection {
            class_pos,
            instance_pos,
            static_pos,
            member_name,
            kind,
        } => static_instance_intersection(class_pos, instance_pos, static_pos, member_name, kind),
        Nullsafe_property_write_context(pos) => nullsafe_property_write_context(pos),
        Uninstantiable_class {
            pos,
            class_name,
            reason_ty_opt,
            decl_pos,
        } => uninstantiable_class(pos, class_name, reason_ty_opt, decl_pos),
        Abstract_const_usage {
            pos,
            name,
            decl_pos,
        } => abstract_const_usage(pos, name, decl_pos),
        Type_arity_mismatch {
            pos,
            decl_pos,
            actual,
            expected,
        } => type_arity_mismatch(pos, decl_pos, actual, expected),
        Member_not_implemented {
            pos,
            member_name,
            decl_pos,
            quickfixes,
        } => member_not_implemented(pos, member_name, decl_pos, quickfixes),
        Kind_mismatch {
            pos,
            decl_pos,
            tparam_name,
            expected_kind,
            actual_kind,
        } => kind_mismatch(pos, decl_pos, tparam_name, expected_kind, actual_kind),
        Trait_parent_construct_inconsistent { pos, decl_pos } => {
            trait_parent_construct_inconsistent(pos, decl_pos)
        }
        Top_member {
            pos,
            ctxt,
            ty_name,
            decl_pos,
            kind,
            name,
            is_nullable,
            ty_reasons,
        } => top_member(
            pos,
            ctxt,
            ty_name,
            decl_pos,
            kind,
            name,
            is_nullable,
            ty_reasons,
        ),
        Unresolved_tyvar_projection {
            pos,
            proj_pos,
            tconst_name,
        } => unresolved_tyvar_projection(pos, proj_pos, tconst_name),
        Cyclic_class_constant {
            pos,
            class_name,
            const_name,
        } => cyclic_class_constant(pos, class_name, const_name),
        Inout_annotation_missing { pos, decl_pos } => inout_annotation_missing(pos, decl_pos),
        Inout_annotation_unexpected {
            pos,
            decl_pos,
            param_is_variadic,
            qfx_pos,
        } => inout_annotation_unexpected(pos, decl_pos, param_is_variadic, qfx_pos),
        Inout_argument_bad_type { pos, reasons } => inout_argument_bad_type(pos, reasons),
        Invalid_meth_caller_inout_parameter { pos, decl_pos } => {
            invalid_meth_caller_inout_parameter(pos, decl_pos)
        }
        Invalid_meth_caller_named_parameter { pos, decl_pos } => {
            invalid_meth_caller_named_parameter(pos, decl_pos)
        }
        Invalid_meth_caller_readonly_return { pos, decl_pos } => {
            invalid_meth_caller_readonly_return(pos, decl_pos)
        }
        This_as_function_pointer_param { pos, decl_pos } => {
            this_as_function_pointer_param(pos, decl_pos)
        }
        Invalid_new_disposable(pos) => invalid_new_disposable(pos),
        Invalid_return_disposable(pos) => invalid_return_disposable(pos),
        Invalid_disposable_hint { pos, class_name } => invalid_disposable_hint(pos, class_name),
        Invalid_disposable_return_hint { pos, class_name } => {
            invalid_disposable_return_hint(pos, class_name)
        }
        Ambiguous_lambda { pos, uses } => ambiguous_lambda(pos, uses),
        Wrong_extend_kind {
            pos,
            kind,
            name,
            parent_pos,
            parent_kind,
            parent_name,
        } => wrong_extend_kind(pos, kind, name, parent_pos, parent_kind, parent_name),
        Wrong_use_kind {
            pos,
            name,
            parent_pos,
            parent_name,
        } => wrong_use_kind(pos, &name, parent_pos, &parent_name),
        Smember_not_found {
            pos,
            kind,
            member_name,
            class_name,
            class_pos,
            hint,
            quickfixes,
        } => smember_not_found(
            pos,
            kind,
            member_name,
            class_name,
            class_pos,
            hint,
            quickfixes,
        ),
        Cyclic_class_def { pos, stack } => cyclic_class_def(pos, stack),
        Trait_reuse_with_final_method {
            pos,
            trait_name,
            parent_cls_name,
            trace,
        } => {
            // `parent_cls_name = (lazy parent_cls_name)`: forced by the pattern.
            let parent_cls_name = parent_cls_name.force().clone();
            trait_reuse_with_final_method(pos, trait_name, parent_cls_name, trace)
        }
        Trait_reuse_inside_class {
            pos,
            class_name,
            trait_name,
            occurrences,
        } => trait_reuse_inside_class(pos, class_name, trait_name, occurrences),
        Invalid_is_as_expression_hint { pos, op, reasons } => {
            invalid_is_as_expression_hint(pos, op, reasons)
        }
        Invalid_enforceable_type {
            pos,
            ty_info,
            tp_pos,
            tp_name,
            kind,
        } => invalid_enforceable_type(pos, ty_info, kind, tp_pos, tp_name),
        Reifiable_attr {
            pos,
            ty_info,
            attr_pos,
            kind,
        } => reifiable_attr(attr_pos, kind, pos, ty_info),
        Invalid_newable_type_argument {
            pos,
            tp_pos,
            tp_name,
        } => invalid_newable_type_argument(pos, tp_pos, tp_name),
        Invalid_newable_typaram_constraints {
            pos,
            tp_name,
            constraints,
        } => invalid_newable_type_param_constraints((pos, tp_name), constraints),
        Override_per_trait {
            pos,
            class_name,
            meth_name,
            trait_name,
            meth_pos,
        } => override_per_trait((pos, class_name), meth_name, trait_name, meth_pos),
        Should_not_be_override { pos, class_id, id } => should_not_be_override(pos, class_id, id),
        Needs_concrete_in_final_class {
            pos,
            class_name,
            meth_name,
        } => needs_concrete_in_final_class(pos, class_name, meth_name),
        Needs_concrete_on_instance_method {
            pos,
            class_name,
            meth_name,
        } => needs_concrete_on_instance_method(pos, class_name, meth_name),
        Needs_concrete_on_constructor { pos, class_name } => {
            needs_concrete_on_constructor(pos, &class_name)
        }
        Call_needs_concrete {
            pos,
            class_name,
            meth_name,
            decl_pos,
            via,
        } => call_needs_concrete(pos, &class_name, &meth_name, decl_pos, via),
        Abstract_access_via_static {
            pos,
            class_name,
            member_name,
            decl_pos,
            containing_method_pos,
        } => abstract_access_via_static(
            pos,
            class_name,
            member_name,
            decl_pos,
            containing_method_pos,
        ),
        Uninstantiable_class_via_static {
            pos,
            class_name,
            decl_pos,
            containing_method_pos,
        } => uninstantiable_class_via_static(pos, &class_name, decl_pos, containing_method_pos),
        This_refinement_in_generic_class {
            pos,
            class_name,
            decl_pos,
        } => this_refinement_in_generic_class(pos, class_name, decl_pos),
        Private_member_variance {
            pos,
            class_name,
            member_name,
            is_write,
            tparam_name,
            variance,
            use_pos,
            decl_pos,
        } => private_member_variance(
            pos,
            class_name,
            member_name,
            is_write,
            tparam_name,
            variance,
            use_pos,
            decl_pos,
        ),
        Memoize_erased_generic_return {
            pos,
            tparam_name,
            attr_pos,
            via_param,
        } => memoize_erased_generic_return(pos, tparam_name, attr_pos, via_param),
        Needs_concrete_override {
            pos,
            method_pos,
            parent_pos,
            method_name_for_method_defined_outside_class,
        } => needs_concrete_override(
            pos,
            method_pos,
            parent_pos,
            method_name_for_method_defined_outside_class.as_deref(),
        ),
        Trivial_strict_eq {
            pos,
            result,
            left,
            right,
            left_trail,
            right_trail,
        } => trivial_strict_eq(pos, result, left, right, left_trail, right_trail),
        Trivial_strict_not_nullable_compare_null {
            pos,
            result,
            ty_reason_msg,
        } => trivial_strict_not_nullable_compare_null(pos, result, ty_reason_msg),
        Eq_incompatible_types { pos, left, right } => {
            let right = right.force().clone();
            let left = left.force().clone();
            eq_incompatible_types(pos, left, right)
        }
        Comparison_invalid_types { pos, left, right } => {
            let right = right.force().clone();
            let left = left.force().clone();
            comparison_invalid_types(pos, left, right)
        }
        Strict_eq_value_incompatible_types { pos, left, right } => {
            let right = right.force().clone();
            let left = left.force().clone();
            strict_eq_value_incompatible_types(pos, left, right)
        }
        Deprecated_use {
            pos,
            decl_pos_opt,
            msg,
        } => deprecated_use(pos, Some(decl_pos_opt), msg),
        Cannot_declare_constant {
            pos,
            class_pos,
            class_name,
        } => cannot_declare_constant(pos, (class_pos, class_name)),
        Redeclaring_promoted_property {
            pos,
            prop_name,
            parent_pos,
            parent_name,
        } => redeclaring_promoted_property(pos, prop_name, parent_pos, parent_name),
        Invalid_classname(pos) => invalid_classname(pos),
        Illegal_type_structure { pos, msg, fn_ } => illegal_type_structure(pos, msg, fn_),
        Illegal_typeconst_direct_access(pos) => illegal_typeconst_direct_access(pos),
        Wrong_expression_kind_attribute {
            pos,
            attr_name,
            expr_kind,
            attr_class_pos,
            attr_class_name,
            intf_name,
        } => wrong_expression_kind_attribute(
            expr_kind,
            pos,
            attr_name,
            attr_class_pos,
            attr_class_name,
            intf_name,
        ),
        Ambiguous_object_access {
            pos,
            name,
            self_pos,
            vis,
            subclass_pos,
            class_self,
            class_subclass,
        } => ambiguous_object_access(
            pos,
            name,
            self_pos,
            vis,
            subclass_pos,
            class_self,
            class_subclass,
        ),
        Invalid_arraykey_constraint { pos, ty_name } => {
            invalid_arraykey_constraint(pos, ty_name.force().clone())
        }
        Redundant_generic {
            pos,
            variance,
            msg,
            suggest,
        } => redundant_generic(pos, variance, msg, suggest),
        Meth_caller_trait { pos, trait_name } => meth_caller_trait(pos, trait_name),
        Duplicate_interface { pos, name, others } => duplicate_interface(pos, name, others),
        Enum_duplicate_value {
            pos,
            value,
            member_name,
            member_pos,
            prev_name,
            prev_pos,
        } => enum_duplicate_value(pos, value, member_name, member_pos, prev_name, prev_pos),
        Enum_uncheckable_value { pos, name, reasons } => enum_uncheckable_value(pos, name, reasons),
        Reified_function_reference(pos) => reified_function_reference(pos),
        Reinheriting_classish_const {
            pos,
            classish_name,
            src_pos,
            src_classish_name,
            existing_const_origin,
            const_name,
        } => reinheriting_classish_const(
            pos,
            classish_name,
            src_pos,
            src_classish_name,
            existing_const_origin,
            const_name,
        ),
        Redeclaring_classish_const {
            pos,
            classish_name,
            redeclaration_pos,
            existing_const_origin,
            const_name,
        } => redeclaring_classish_const(
            pos,
            classish_name,
            redeclaration_pos,
            existing_const_origin,
            const_name,
        ),
        Abstract_function_pointer {
            pos,
            class_name,
            meth_name,
            decl_pos,
        } => abstract_function_pointer(class_name, meth_name, pos, decl_pos),
        Inherited_class_member_with_different_case {
            pos,
            member_type,
            name,
            name_prev,
            child_class,
            prev_class,
            prev_class_pos,
        } => inherited_class_member_with_different_case(
            member_type,
            &name,
            &name_prev,
            pos,
            child_class,
            prev_class,
            prev_class_pos,
        ),
        Multiple_inherited_class_member_with_different_case {
            pos,
            child_class_name,
            member_type,
            class1_name,
            class1_pos,
            name1,
            class2_name,
            class2_pos,
            name2,
        } => multiple_inherited_class_member_with_different_case(
            member_type,
            &name1,
            &name2,
            &class1_name,
            &class2_name,
            child_class_name,
            pos,
            class1_pos,
            class2_pos,
        ),
        Multiple_instantiation_inheritence {
            type_name,
            implements_or_extends,
            interface_name,
            winning_implements,
            losing_implements,
        } => multiple_instantiation_inheritence(
            &type_name,
            implements_or_extends,
            &interface_name,
            winning_implements,
            losing_implements,
        ),
        Parent_support_dynamic_type {
            pos,
            child_name,
            child_kind,
            parent_name,
            parent_kind,
            child_support_dyn,
        } => parent_support_dynamic_type(
            pos,
            (child_name, child_kind),
            (parent_name, parent_kind),
            child_support_dyn,
        ),
        Property_is_not_enforceable {
            pos,
            prop_name,
            class_name,
            prop_pos,
            prop_type,
        } => property_is_not_enforceable(pos, &prop_name, class_name, (prop_pos, prop_type)),
        Property_is_not_dynamic {
            pos,
            prop_name,
            class_name,
            prop_pos,
            prop_type,
        } => property_is_not_dynamic(pos, &prop_name, class_name, (prop_pos, prop_type)),
        Private_property_is_not_enforceable {
            pos,
            prop_name,
            class_name,
            prop_pos,
            prop_type,
        } => {
            private_property_is_not_enforceable(pos, &prop_name, class_name, (prop_pos, prop_type))
        }
        Private_property_is_not_dynamic {
            pos,
            prop_name,
            class_name,
            prop_pos,
            prop_type,
        } => private_property_is_not_dynamic(pos, &prop_name, class_name, (prop_pos, prop_type)),
        Immutable_local(pos) => immutable_local(pos),
        Require_dynamic_obj_get {
            receiver_pos,
            receiver_ty,
            receiver_ty_pos,
            member_kind,
            member_name,
        } => require_dynamic_obj_get(
            receiver_pos,
            receiver_ty,
            receiver_ty_pos,
            member_kind,
            member_name,
        ),
        Nonsense_member_selection { pos, kind } => nonsense_member_selection(pos, kind),
        Consider_meth_caller {
            pos,
            class_name,
            meth_name,
        } => consider_meth_caller(pos, class_name, meth_name),
        Method_import_via_diamond {
            pos,
            class_name,
            method_pos,
            method_name,
            trace1,
            trace2,
        } => method_import_via_diamond(pos, class_name, method_pos, method_name, trace1, trace2),
        Property_import_via_diamond {
            generic,
            pos,
            class_name,
            property_pos,
            property_name,
            trace1,
            trace2,
        } => property_import_via_diamond(
            generic,
            pos,
            class_name,
            property_pos,
            property_name,
            trace1,
            trace2,
        ),
        Unification_cycle { pos, ty_name } => unification_cycle(pos, ty_name.force().clone()),
        Method_variance(pos) => method_variance(pos),
        Explain_tconst_where_constraint {
            pos,
            decl_pos,
            msgs,
        } => explain_tconst_where_constraint(pos, decl_pos, msgs),
        Format_string {
            pos,
            snippet,
            fmt_string,
            class_pos,
            fn_name,
            class_suggest,
        } => format_string(pos, snippet, fmt_string, class_pos, fn_name, class_suggest),
        Expected_literal_format_string(pos) => expected_literal_format_string(pos),
        Re_prefixed_non_string { pos, reason } => re_prefixed_non_string(pos, reason),
        Bad_regex_pattern { pos, reason } => bad_regex_pattern(pos, reason),
        Option_return_only_typehint { pos, kind } => option_return_only_typehint(pos, kind),
        Redeclaring_missing_method { pos, trait_method } => {
            redeclaring_missing_method(pos, trait_method)
        }
        Expecting_type_hint(pos) => expecting_type_hint(pos),
        Expecting_type_hint_variadic(pos) => expecting_type_hint_variadic(pos),
        Expecting_return_type_hint(pos) => expecting_return_type_hint(pos),
        Duplicate_using_var(pos) => duplicate_using_var(pos),
        Illegal_disposable { pos, verb } => illegal_disposable(pos, verb),
        Escaping_disposable(pos) => escaping_disposable(pos),
        Escaping_disposable_param(pos) => escaping_disposable_parameter(pos),
        Escaping_this(pos) => escaping_this(pos),
        Must_extend_disposable(pos) => must_extend_disposable(pos),
        Field_kinds { pos, decl_pos } => field_kinds(pos, decl_pos),
        Unbound_name {
            pos,
            name,
            class_exists,
        } => unbound_name_typing(pos, name, class_exists),
        Previous_default(pos) => previous_default(pos),
        Previous_default_or_optional(pos) => previous_default_or_optional(pos),
        Return_in_void { pos, decl_pos } => return_in_void(pos, decl_pos),
        This_var_outside_class(pos) => this_var_outside_class(pos),
        Unbound_global(pos) => unbound_global(pos),
        Private_meth_caller { pos, decl_pos } => private_meth_caller(pos, decl_pos),
        Protected_meth_caller { pos, decl_pos } => protected_meth_caller(pos, decl_pos),
        Internal_meth_caller { pos, decl_pos } => internal_meth_caller(pos, decl_pos),
        Protected_internal_meth_caller { pos, decl_pos } => {
            protected_internal_meth_caller(pos, decl_pos)
        }
        Array_cast(pos) => array_cast(pos),
        String_cast { pos, ty_name } => string_cast(pos, ty_name.force().clone()),
        Static_outside_class(pos) => static_outside_class(pos),
        Self_outside_class(pos) => self_outside_class(pos),
        New_inconsistent_construct {
            pos,
            class_pos,
            class_name,
            kind,
        } => new_inconsistent_construct(pos, (class_pos, class_name), kind),
        Parent_outside_class(pos) => parent_outside_class(pos),
        Parent_abstract_call {
            pos,
            meth_name,
            decl_pos,
        } => parent_abstract_call(pos, meth_name, decl_pos),
        Self_abstract_call {
            pos,
            self_pos,
            meth_name,
            decl_pos,
        } => self_abstract_call(pos, meth_name, self_pos, decl_pos),
        Classname_abstract_call {
            pos,
            meth_name,
            class_name,
            decl_pos,
        } => classname_abstract_call(pos, meth_name, class_name, decl_pos),
        Static_synthetic_method {
            pos,
            meth_name,
            class_name,
            decl_pos,
        } => static_synthetic_method(pos, meth_name, &class_name, decl_pos),
        Static_call_on_trait_require_non_strict {
            pos,
            meth_name,
            trait_name,
            req_constraint_name,
            req_constraint_kind,
            trait_pos,
        } => static_call_on_trait_require_non_strict(
            pos,
            meth_name,
            &trait_name,
            &req_constraint_name,
            req_constraint_kind,
            trait_pos,
        ),
        Static_prop_on_trait {
            pos,
            meth_name,
            trait_name,
            trait_pos,
        } => static_prop_on_trait(pos, &meth_name, &trait_name, trait_pos),
        Isset_in_strict(pos) => isset_in_strict(pos),
        Isset_inout_arg(pos) => isset_inout_arg(pos),
        Unpacking_disallowed_builtin_function { pos, fn_name } => {
            unpacking_disallowed_builtin_function(pos, fn_name)
        }
        Array_get_arity {
            pos,
            name,
            decl_pos,
        } => array_get_arity(pos, name, decl_pos),
        Undefined_field {
            pos,
            name,
            decl_pos,
        } => undefined_field(pos, name, decl_pos),
        Array_access {
            pos,
            ctxt: primary::ReadOrWrite::read,
            ty_name,
            decl_pos,
        } => array_access_read(pos, decl_pos, ty_name.force().clone()),
        Array_access {
            pos,
            ctxt: primary::ReadOrWrite::write,
            ty_name,
            decl_pos,
        } => array_access_write(pos, decl_pos, ty_name.force().clone()),
        Keyset_set { pos, decl_pos } => keyset_set(pos, decl_pos),
        Array_append {
            pos,
            ty_name,
            decl_pos,
        } => array_append(pos, decl_pos, ty_name.force().clone()),
        Const_mutation {
            pos,
            ty_name,
            decl_pos,
        } => const_mutation(pos, decl_pos, ty_name.force().clone()),
        Expected_class { pos, suffix } => expected_class(
            pos,
            match suffix {
                None => "".to_string(),
                Some(suffix) => suffix.force().clone(),
            },
        ),
        Unknown_type {
            pos,
            expected,
            reason,
        } => unknown_type(pos, expected, reason),
        Parent_in_trait(pos) => parent_in_trait(pos),
        Parent_undefined { pos, trait_reqs } => parent_undefined(pos, trait_reqs),
        Constructor_no_args(pos) => constructor_no_args(pos),
        Visibility {
            pos,
            msg,
            decl_pos,
            reason_msg,
        } => visibility(pos, msg, decl_pos, reason_msg),
        Bad_call { pos, ty_name } => bad_call(pos, ty_name.force().clone()),
        Extend_final {
            pos,
            name,
            decl_pos,
        } => extend_final(pos, decl_pos, name),
        Extend_sealed {
            pos,
            parent_pos,
            parent_name,
            parent_kind,
            verb,
        } => extend_sealed(pos, parent_pos, parent_name, parent_kind, verb),
        Trait_prop_const_class { pos, name } => trait_prop_const_class(pos, name),
        Implement_abstract {
            pos,
            is_final,
            decl_pos,
            trace,
            name,
            kind,
            quickfixes,
        } => implement_abstract(pos, is_final, decl_pos, name, kind, quickfixes, trace),
        Abstract_member_in_concrete_class {
            pos,
            class_name_pos,
            is_final,
            member_kind,
            member_name,
        } => abstract_member_in_concrete_class(
            pos,
            class_name_pos,
            is_final,
            member_kind,
            member_name,
        ),
        Generic_static { pos, typaram_name } => generic_static(pos, typaram_name),
        Object_string { pos, decl_pos } => object_string(pos, decl_pos),
        Cyclic_typedef { def_pos, use_pos } => cyclic_typedef(def_pos, use_pos),
        Require_args_reify { pos, decl_pos } => require_args_reify(pos, decl_pos),
        Require_generic_explicit {
            pos,
            param_name,
            decl_pos,
        } => require_generic_explicit(pos, decl_pos, param_name),
        Invalid_reified_arg {
            pos,
            param_name,
            decl_pos,
            arg_info,
        } => invalid_reified_argument(pos, param_name, decl_pos, arg_info),
        Invalid_reified_arg_reifiable {
            pos,
            param_name,
            decl_pos,
            ty_pos,
            ty_msg,
        } => invalid_reified_argument_reifiable(
            pos,
            param_name,
            decl_pos,
            ty_pos,
            ty_msg.force().clone(),
        ),
        New_class_reified {
            pos,
            class_kind,
            suggested_class_name,
        } => new_class_reified(pos, class_kind, suggested_class_name),
        Class_get_reified(pos) => class_get_reified(pos),
        Static_meth_with_class_reified_generic { pos, generic_pos } => {
            static_meth_with_class_reified_generic(pos, generic_pos)
        }
        Consistent_construct_reified(pos) => consistent_construct_reified(pos),
        Bad_fn_ptr_construction(pos) => bad_function_pointer_construction(pos),
        Reified_generics_not_allowed(pos) => reified_generics_not_allowed(pos),
        New_without_newable { pos, name } => new_without_newable(pos, name),
        Discarded_awaitable { pos, decl_pos } => discarded_awaitable(pos, decl_pos),
        Unknown_object_member {
            pos,
            member_name,
            elt,
            reason,
        } => unknown_object_member(pos, member_name, elt, reason),
        Non_class_member {
            pos,
            member_name,
            elt,
            ty_name,
            decl_pos,
        } => non_class_member(pos, member_name, elt, ty_name.force().clone(), decl_pos),
        Null_container { pos, null_witness } => null_container(pos, null_witness),
        Declared_covariant {
            pos,
            param_pos,
            msgs,
        } => declared_covariant(param_pos, pos, msgs),
        Declared_contravariant {
            pos,
            param_pos,
            msgs,
        } => declared_contravariant(pos, param_pos, msgs),
        Static_prop_type_generic_param {
            pos,
            var_ty_pos,
            class_pos,
        } => static_property_type_generic_param(pos, class_pos, var_ty_pos),
        Contravariant_this {
            pos,
            class_name,
            typaram_name,
        } => contravariant_this(pos, class_name, typaram_name),
        Cyclic_typeconst { pos, tyconst_names } => cyclic_typeconst(pos, tyconst_names),
        Array_get_with_optional_field {
            recv_pos,
            field_pos,
            field_name,
            decl_pos,
        } => array_get_with_optional_field(field_pos, &recv_pos, decl_pos, field_name),
        Mutating_const_property(pos) => mutating_const_property(pos),
        Self_const_parent_not(pos) => self_const_parent_not(pos),
        Unexpected_ty_in_tast {
            pos,
            expected_ty,
            actual_ty,
        } => {
            let expected_ty = expected_ty.force().clone();
            let actual_ty = actual_ty.force().clone();
            unexpected_ty_in_tast(pos, actual_ty, expected_ty)
        }
        Call_lvalue(pos) => call_lvalue(pos),
        Unsafe_cast_await(pos) => unsafe_cast_await(pos),
        Match_not_exhaustive {
            pos,
            ty_not_covered,
        } => match_not_exhaustive(pos, ty_not_covered.force().clone()),
        Match_on_unsupported_type {
            pos,
            expr_ty,
            unsupported_tys,
        } => {
            let unsupported_tys = unsupported_tys
                .iter()
                .map(|ty| ty.force().clone())
                .collect();
            let expr_ty = expr_ty.force().clone();
            match_on_unsupported_type(pos, expr_ty, unsupported_tys)
        }
        Class_const_to_string { pos, cls_name } => class_const_to_string(pos, &cls_name),
        Class_pointer_to_string { pos, ty } => class_pointer_to_string(pos, ty),
        String_to_class_pointer {
            pos,
            cls_name,
            ty_pos,
        } => string_to_class_pointer(pos, &cls_name, ty_pos),
        Optional_parameter_not_supported(pos) => optional_parameter_not_supported(pos),
        Optional_parameter_not_abstract(pos) => optional_parameter_not_abstract(pos),
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;
    use std::sync::Arc;

    use relative_path::Prefix;
    use relative_path::RelativePath;

    use super::*;

    fn env() -> crate::typing_env_types::Env {
        let ctx = crate::ctx::Ctx::new(
            std::path::Path::new("/"),
            oxidized::typechecker_options::TypecheckerOptions::default(),
        )
        .unwrap();
        crate::typing_env_types::empty(
            None,
            None,
            Arc::new(ctx),
            Arc::new(RelativePath::make(Prefix::Root, PathBuf::from("foo.php"))),
            None,
        )
    }

    /// The code, the message and the messages of the reasons.
    fn render(err: T) -> (isize, String, Vec<String>) {
        let Message(_, claim) = err.claim.force();
        (
            err.code as isize,
            claim.to_string(),
            err.reasons
                .force()
                .iter()
                .map(|Message(_, msg)| msg.to_string())
                .collect(),
        )
    }

    /// The position of the claim and the positions of the reasons.
    fn positions(err: &T) -> (Pos, Vec<PosOrDecl>) {
        let Message(pos, _) = err.claim.force();
        (
            pos.clone(),
            err.reasons
                .force()
                .iter()
                .map(|Message(pos, _)| pos.clone())
                .collect(),
        )
    }

    /// Columns `start..end` of line `line` of `a.php`.
    fn pos(line: usize, start: usize, end: usize) -> Pos {
        let file = Arc::new(RelativePath::make(Prefix::Root, PathBuf::from("a.php")));
        let bol = line * 100;
        Pos::from_lnum_bol_offset(file, (line, bol, bol + start), (line, bol, bol + end))
    }

    fn s(s: &str) -> String {
        s.to_string()
    }

    fn strings(l: &[&str]) -> Vec<String> {
        l.iter().map(|s| s.to_string()).collect()
    }

    fn reasons(l: &[(&Pos, &str)]) -> Reasons {
        let l: Vec<Message<PosOrDecl>> = l
            .iter()
            .map(|(pos, msg)| Message((*pos).clone(), (*msg).into()))
            .collect();
        lazy!(l)
    }

    // The expected messages are those of hphp/hack/test/typecheck (the file
    // is named above each assertion).

    #[test]
    fn test_require_dynamic_obj_get() {
        // nonsense_member_access.php
        assert_eq!(
            render(require_dynamic_obj_get(
                pos(5, 4, 9),
                lazy!(s("this")),
                Pos::NONE,
                primary::RequireDynamicObjGetMemberKind::Property,
                None,
            )),
            (
                4525,
                s(
                    "Dynamic access of a property is only permitted on a receiver of type `dynamic`, but this receiver has type `this`"
                ),
                vec![],
            )
        );
        // The type of the receiver is the receiver itself: no reason either.
        assert_eq!(
            render(require_dynamic_obj_get(
                pos(7, 4, 9),
                lazy!(s("this")),
                pos(7, 4, 9),
                primary::RequireDynamicObjGetMemberKind::Method,
                None,
            )),
            (
                4525,
                s(
                    "Dynamic access of a method is only permitted on a receiver of type `dynamic`, but this receiver has type `this`"
                ),
                vec![],
            )
        );
        // dynamic_obj_get_non_dynamic.bad.php
        assert_eq!(
            render(require_dynamic_obj_get(
                pos(18, 2, 7),
                lazy!(s("dict<string, int>")),
                pos(17, 23, 40),
                primary::RequireDynamicObjGetMemberKind::Property,
                None,
            )),
            (
                4525,
                s(
                    "Dynamic access of a property is only permitted on a receiver of type `dynamic`, but this receiver has type `dict<string, int>`"
                ),
                strings(&["The receiver's type is defined here"]),
            )
        );
    }

    #[test]
    fn test_nonsense_member_selection() {
        // nonsense_member_access.php
        assert_eq!(
            render(nonsense_member_selection(Pos::NONE, s("$this"))),
            (
                4406,
                s("Dynamic member access requires a local variable, not `$this`."),
                vec![],
            )
        );
    }

    #[test]
    fn test_consider_meth_caller() {
        // function_pointer/instance_method.php
        assert_eq!(
            render(consider_meth_caller(Pos::NONE, s("\\A"), s("foo"))),
            (
                4407,
                s(
                    "Function pointer syntax requires a static method. Use `meth_caller(A::class, 'foo')` to create a function pointer to the instance method"
                ),
                vec![],
            )
        );
    }

    #[test]
    fn test_method_import_via_diamond() {
        // trait_reuse/trait_diamond_no_attr_1.bad.php
        let (p, method_pos, p1, p2, p3) = (
            pos(13, 6, 13),
            pos(7, 18, 25),
            pos(15, 6, 14),
            pos(10, 6, 14),
            pos(14, 6, 14),
        );
        let err = method_import_via_diamond(
            p.clone(),
            s("\\MyClass"),
            method_pos.clone(),
            s("testFun"),
            reasons(&[
                (&p1, "`MyClass` uses `MyTrait2`"),
                (&p2, "`MyTrait2` uses `MyTrait1`"),
            ]),
            reasons(&[(&p3, "`MyClass` uses `MyTrait1`")]),
        );
        assert_eq!(positions(&err), (p, vec![method_pos, p1, p2, p3]));
        assert_eq!(
            render(err),
            (
                4439,
                s(
                    "Class `MyClass` inherits trait method `testFun` via multiple traits.  Add the __EnableMethodTraitDiamond attribute to `MyClass`, remove the multiple paths, or override the method"
                ),
                strings(&[
                    "Trait method is defined here",
                    "`MyClass` uses `MyTrait2`",
                    "`MyTrait2` uses `MyTrait1`",
                    "`MyClass` uses `MyTrait1`",
                ]),
            )
        );
    }

    #[test]
    fn test_property_import_via_diamond() {
        // trait_reuse/trait_diamond_property_2.bad.php
        assert_eq!(
            render(property_import_via_diamond(
                true,
                Pos::NONE,
                s("\\MyClass"),
                Pos::NONE,
                s("myprop"),
                reasons(&[
                    (&Pos::NONE, "`MyClass` uses `MyTrait2`"),
                    (&Pos::NONE, "`MyTrait2` uses `MyTrait1`"),
                ]),
                reasons(&[(&Pos::NONE, "`MyClass` uses `MyTrait1`")]),
            )),
            (
                4462,
                s(
                    "Class `MyClass` inherits generic trait property `myprop` via multiple paths at different types."
                ),
                strings(&[
                    "Trait property is defined here",
                    "`MyClass` uses `MyTrait2`",
                    "`MyTrait2` uses `MyTrait1`",
                    "`MyClass` uses `MyTrait1`",
                ]),
            )
        );
        // trait_reuse/trait_diamond_property_mtd_01.bad.php
        assert_eq!(
            render(property_import_via_diamond(
                false,
                Pos::NONE,
                s("\\MyClass"),
                Pos::NONE,
                s("myprop"),
                reasons(&[]),
                reasons(&[]),
            )),
            (
                4462,
                s(
                    "Class `MyClass` inherits trait property `myprop` via multiple paths. Currently, traits with properties are not supported by the <<__EnableMethodTraitDiamond>> experimental feature."
                ),
                strings(&["Trait property is defined here"]),
            )
        );
    }

    #[test]
    fn test_unification_cycle() {
        // new_inference/recursive_type_expansion.php
        assert_eq!(
            render(unification_cycle(Pos::NONE, s("Vector<[rec]>"))),
            (
                4155,
                s(
                    "Type circularity: in order to type-check this expression it is necessary for a type [rec] to be equal to type `Vector<[rec]>`"
                ),
                vec![],
            )
        );
    }

    #[test]
    fn test_format_string() {
        // printf3.php
        assert_eq!(
            render(format_string(
                Pos::NONE,
                s("%s"),
                s("%s"),
                Pos::NONE,
                s("format_s"),
                s("X"),
            )),
            (
                4038,
                s("Invalid format string `%s` in `\"%s\"`"),
                strings(&["You can add a new format specifier by adding `format_s()` to `X`"]),
            )
        );
        // printf3.php
        assert_eq!(
            render(expecting_return_type_hint(Pos::NONE)),
            (4030, s("Was expecting a return type hint"), vec![])
        );
    }

    #[test]
    fn test_re_prefixed_strings() {
        // re_prefixed_string/re_prefixed_string.php
        assert_eq!(
            render(re_prefixed_non_string(
                Pos::NONE,
                primary::RePrefixedNonStringReason::embedded_expr,
            )),
            (
                4274,
                s("Strings with embedded expressions are not allowed to be to be `re`-prefixed"),
                vec![],
            )
        );
        // re_prefixed_string/simple_re.php
        assert_eq!(
            render(bad_regex_pattern(
                Pos::NONE,
                primary::BadRegexPatternReason::missing_delim,
            )),
            (4275, s("Bad regex pattern; Missing delimiter(s)."), vec![])
        );
        assert_eq!(
            render(bad_regex_pattern(
                Pos::NONE,
                primary::BadRegexPatternReason::bad_patt(s("unmatched parentheses [2]")),
            )),
            (
                4275,
                s("Bad regex pattern; unmatched parentheses [2]."),
                vec![],
            )
        );
    }

    #[test]
    fn test_option_return_only_typehint() {
        // void_option2.php
        assert_eq!(
            render(option_return_only_typehint(
                Pos::NONE,
                primary::OptionReturnOnlyTypehintKind::void,
            )),
            (
                4066,
                s(
                    "`?void` is a nonsensical typehint; a function cannot both only return implicitly and return null."
                ),
                vec![],
            )
        );
        // noreturn_option.php
        assert_eq!(
            render(option_return_only_typehint(
                Pos::NONE,
                primary::OptionReturnOnlyTypehintKind::noreturn,
            )),
            (
                4066,
                s(
                    "`?noreturn` is a nonsensical typehint; a function cannot both never return and return null."
                ),
                vec![],
            )
        );
    }

    #[test]
    fn test_using() {
        // using/using_bad.php
        assert_eq!(
            render(illegal_disposable(
                Pos::NONE,
                primary::IllegalDisposableVerb::assigned,
            )),
            (
                4179,
                s("Disposable objects must only be assigned in a `using` statement"),
                vec![],
            )
        );
        assert_eq!(
            render(duplicate_using_var(Pos::NONE)),
            (
                4178,
                s("Local variable already used in `using` statement"),
                vec![],
            )
        );
    }

    #[test]
    fn test_unbound_name_typing() {
        // string_no_call.php
        let err = unbound_name_typing(Pos::NONE, s("\\HH\\String\\__primitive_length"), false);
        assert!(err.quickfixes.is_empty());
        assert_eq!(
            render(err),
            (
                4107,
                s("Unbound name (typing): `HH\\String\\__primitive_length`"),
                vec![],
            )
        );
    }

    #[test]
    fn test_previous_default() {
        // function_default.php
        assert_eq!(
            render(previous_default(Pos::NONE)),
            (
                4077,
                s(
                    "A previous parameter has a default value.\nRemove all the default values for the preceding parameters,\nor add a default value to this one."
                ),
                vec![],
            )
        );
    }

    #[test]
    fn test_meth_caller_visibility() {
        // function_pointer/function_pointer.php
        assert_eq!(
            render(private_meth_caller(Pos::NONE, Pos::NONE)),
            (
                4431,
                s(
                    "You cannot access this method with `meth_caller` (even from the same class hierarchy)"
                ),
                strings(&["It is declared as `private` here"]),
            )
        );
        // meth_caller_internal.php
        assert_eq!(
            render(internal_meth_caller(Pos::NONE, Pos::NONE)),
            (
                4481,
                s("You cannot access this method with `meth_caller` (even from the same module)"),
                strings(&["It is declared as `internal` here"]),
            )
        );
        assert_eq!(
            render(protected_internal_meth_caller(Pos::NONE, Pos::NONE)).0,
            4496
        );
    }

    #[test]
    fn test_new_inconsistent_construct() {
        // new_static3.php
        let (new_pos, cpos) = (pos(21, 13, 19), pos(19, 6, 7));
        let err = new_inconsistent_construct(
            new_pos.clone(),
            (cpos.clone(), s("\\B")),
            primary::NewInconsistentConstructKind::static_,
        );
        assert_eq!(positions(&err), (new_pos, vec![cpos]));
        assert_eq!(
            render(err),
            (
                4060,
                s(
                    "Can't use `new static()` for `B`; `__construct` arguments are not guaranteed to be consistent in child classes"
                ),
                strings(&[
                    "This declaration is neither `final` nor uses the `<<__ConsistentConstruct>>` attribute"
                ]),
            )
        );
        // classname/new_needs_consistent_construct.php
        assert_eq!(
            render(new_inconsistent_construct(
                Pos::NONE,
                (Pos::NONE, s("\\C")),
                primary::NewInconsistentConstructKind::classname,
            )),
            (
                4060,
                s(
                    "Can't use `new` on `classname<C>`; `__construct` arguments are not guaranteed to be consistent in child classes"
                ),
                strings(&[
                    "This declaration is neither `final` nor uses the `<<__ConsistentConstruct>>` attribute"
                ]),
            )
        );
    }

    #[test]
    fn test_abstract_calls() {
        // parent_abstract_call.php
        assert_eq!(
            render(parent_abstract_call(Pos::NONE, s("XYZ"), Pos::NONE)),
            (
                4073,
                s("Cannot call `parent::XYZ()`; it is abstract"),
                strings(&["Declaration is here"]),
            )
        );
        // self_abstract_call.php
        let self_pos = pos(8, 4, 8);
        let err = self_abstract_call(pos(8, 10, 11), s("f"), self_pos.clone(), pos(5, 34, 35));
        assert_eq!(
            err.quickfixes,
            vec![Quickfix {
                title: s("Change to `static::f`"),
                edits: Edits::Eager(vec![(s("static"), self_pos)]),
                hint_styles: vec![],
            }]
        );
        assert_eq!(
            render(err),
            (
                4073,
                s("Cannot call `self::f()`; it is abstract. Did you mean `static::f()`?"),
                strings(&["Declaration is here"]),
            )
        );
        // trait_static_method.php
        assert_eq!(
            render(static_synthetic_method(
                Pos::NONE,
                s("bad"),
                "\\R_Trait",
                Pos::NONE,
            )),
            (
                4185,
                s("Cannot call `R_Trait::bad()`; `bad` is not defined in `R_Trait`"),
                strings(&["Declaration is here"]),
            )
        );
    }

    #[test]
    fn test_static_call_on_trait_require_non_strict() {
        // require_class/static_access_04.bad.php
        assert_eq!(
            render(static_call_on_trait_require_non_strict(
                Pos::NONE,
                s("foo"),
                "\\T",
                "\\C",
                primary::StaticCallOnTraitRequireNonStrictReqConstraintKind::class_,
                Pos::NONE,
            )),
            (
                4476,
                s(
                    "Invoking static methods on traits is dangerous and must be avoided. Since trait T has a `require class C` constraint, replace `T::foo(...)` with `C::foo(...)`."
                ),
                vec![],
            )
        );
        // require_class/requirethis_static_04.bad.php
        assert_eq!(
            render(static_call_on_trait_require_non_strict(
                Pos::NONE,
                s("foo"),
                "\\T",
                "\\C",
                primary::StaticCallOnTraitRequireNonStrictReqConstraintKind::this_as,
                Pos::NONE,
            )),
            (
                4486,
                s(
                    "Invoking static methods on traits is dangerous and is forbidden on trait T because it has a `require this as C` constraint."
                ),
                strings(&["T is defined here"]),
            )
        );
    }

    #[test]
    fn test_static_prop_on_trait() {
        // static_prop_on_trait1.bad.php
        assert_eq!(
            render(static_prop_on_trait(
                Pos::NONE,
                "$ints",
                "\\MyTrait",
                Pos::NONE,
            )),
            (
                4497,
                s("Static property access on a trait: `MyTrait::$ints`"),
                strings(&["MyTrait is defined here"]),
            )
        );
    }

    #[test]
    fn test_unpacking_disallowed_builtin_function() {
        // argument_unpacking/unpack_call8_isset.php
        assert_eq!(
            render(unpacking_disallowed_builtin_function(Pos::NONE, s("isset"))),
            (4147, s("Arg unpacking is disallowed for `isset`"), vec![])
        );
    }

    #[test]
    fn test_undefined_field() {
        // shape_coalesce.php
        assert_eq!(
            render(undefined_field(Pos::NONE, s("bar"), Pos::NONE)),
            (
                4108,
                s("This shape doesn't have a field `bar`"),
                strings(&["The shape is defined here"]),
            )
        );
    }

    #[test]
    fn test_array_access() {
        // test_array13.php
        let (p1, p2) = (pos(14, 2, 16), pos(13, 37, 38));
        let err = array_access_write(p1.clone(), p2.clone(), s("an int"));
        assert_eq!(positions(&err), (p1.clone(), vec![p2.clone()]));
        assert_eq!(
            render(err),
            (
                4370,
                s("This is not an object of type `KeyedContainer`, this is an int"),
                strings(&["Definition is here"]),
            )
        );
        // No reason when the type has no position. (No test of the suite
        // expects the code of a read.)
        assert_eq!(
            render(array_access_read(p1.clone(), Pos::NONE, s("an int"))),
            (
                ErrorCode::ArrayAccessRead as isize,
                s("This is not an object of type `KeyedContainer`, this is an int"),
                vec![],
            )
        );
        // cannot_append.php
        assert_eq!(
            render(array_append(
                p1.clone(),
                p2.clone(),
                s("an object of type dict<int, string>"),
            )),
            (
                4006,
                s("an object of type dict<int, string> does not allow array append"),
                strings(&["Definition is here"]),
            )
        );
        assert_eq!(
            render(array_append(p1.clone(), Pos::NONE, s("a keyset"))).2,
            Vec::<String>::new()
        );
        // immmap_mutate.php
        assert_eq!(
            render(const_mutation(
                p1.clone(),
                p2,
                s("an object of type ImmMap<int, int>"),
            )),
            (
                4011,
                s("You cannot mutate this"),
                strings(&["This is an object of type ImmMap<int, int>"]),
            )
        );
        assert_eq!(
            render(const_mutation(p1.clone(), Pos::NONE, s("a keyset"))).2,
            Vec::<String>::new()
        );
        // array_set_error.php
        assert_eq!(
            render(keyset_set(p1.clone(), pos(3, 13, 24))),
            (
                4156,
                s("Elements in a keyset cannot be assigned, use append instead."),
                strings(&["Definition is here"]),
            )
        );
        assert_eq!(render(keyset_set(p1, Pos::NONE)).2, Vec::<String>::new());
    }

    #[test]
    fn test_expected_class() {
        // dynamic_class.php
        assert_eq!(
            render(expected_class(Pos::NONE, s(", but got a string"))),
            (4026, s("Was expecting a class, but got a string"), vec![])
        );
    }

    #[test]
    fn test_parent_undefined() {
        // no_parent.php
        assert_eq!(
            render(parent_undefined(Pos::NONE, None)),
            (4076, s("parent is undefined"), vec![])
        );
    }

    #[test]
    fn test_extend_final() {
        // stdclass_final.php
        let (extend_pos, decl_pos) = (pos(3, 6, 18), pos(31, 14, 22));
        let err = extend_final(extend_pos.clone(), decl_pos.clone(), s("\\stdClass"));
        assert_eq!(positions(&err), (extend_pos, vec![decl_pos]));
        assert_eq!(
            render(err),
            (
                4035,
                s("You cannot extend final class `stdClass`"),
                strings(&["Declaration is here"]),
            )
        );
    }

    #[test]
    fn test_extend_sealed() {
        // sealed/interface2.php
        assert_eq!(
            render(extend_sealed(
                Pos::NONE,
                Pos::NONE,
                s("\\A"),
                primary::ExtendSealedParentKind::intf,
                primary::ExtendSealedVerb::implement,
            )),
            (
                4238,
                s("You cannot implement sealed interface `A`"),
                strings(&["Declaration is here"]),
            )
        );
    }

    #[test]
    fn test_implement_abstract() {
        // typing_fail_implement_abstract.php
        let (p1, p2, trace_pos) = (pos(16, 6, 7), pos(13, 27, 28), pos(16, 16, 17));
        let err = implement_abstract(
            p1.clone(),
            false,
            p2.clone(),
            s("f"),
            primary::ImplementAbstractKind::meth,
            vec![],
            reasons(&[(&trace_pos, "`B` uses `A`")]),
        );
        assert_eq!(positions(&err), (p1, vec![trace_pos, p2]));
        assert_eq!(
            render(err),
            (
                4047,
                s(
                    "This class must be declared `abstract`, or provide an implementation for the abstract method `f`"
                ),
                strings(&["`B` uses `A`", "The method is defined here"]),
            )
        );
        // tconst/abstract_final_tconst2.php
        assert_eq!(
            render(implement_abstract(
                Pos::NONE,
                true,
                Pos::NONE,
                s("T"),
                primary::ImplementAbstractKind::ty_const,
                vec![],
                reasons(&[(&Pos::NONE, "`C` uses `I`")]),
            )),
            (
                4047,
                s(
                    "This class was declared as `final`. It must provide an implementation for the abstract type constant `T`"
                ),
                strings(&["`C` uses `I`", "The type constant is defined here"]),
            )
        );
    }

    #[test]
    fn test_abstract_member_in_concrete_class() {
        // test_consts12.php
        assert_eq!(
            render(abstract_member_in_concrete_class(
                Pos::NONE,
                Pos::NONE,
                false,
                primary::AbstractMemberInConcreteClassMemberKind::constant,
                s("X"),
            )),
            (
                4465,
                s(
                    "Constant `X` is abstract but the class is concrete. Either provide an implementation here."
                ),
                strings(&["Or make the class abstract."]),
            )
        );
        // xhp_attr_13.php
        assert_eq!(
            render(abstract_member_in_concrete_class(
                Pos::NONE,
                Pos::NONE,
                false,
                primary::AbstractMemberInConcreteClassMemberKind::type_constant,
                s("TInner"),
            )),
            (
                4465,
                s(
                    "Type constant `TInner` is abstract but the class is concrete. Either provide an implementation here."
                ),
                strings(&["Or make the class abstract."]),
            )
        );
    }

    #[test]
    fn test_reified() {
        // function_pointer/explicit_targs2.php
        assert_eq!(
            render(require_generic_explicit(Pos::NONE, Pos::NONE, s("T"))),
            (
                4347,
                s(
                    "Illegal wildcard (`_`): generic type parameter `T` must be specified explicitly"
                ),
                strings(&["Definition is here"]),
            )
        );
        // reified_generics/valid_targ_funcall.php
        let (hint_pos, def_pos, arg_pos) = (pos(7, 4, 5), pos(4, 17, 22), pos(7, 4, 5));
        let err = invalid_reified_argument(
            hint_pos.clone(),
            s("Tpain"),
            def_pos.clone(),
            reasons(&[(&arg_pos, "not reified")]),
        );
        assert_eq!(positions(&err), (hint_pos, vec![arg_pos, def_pos]));
        assert_eq!(
            render(err),
            (
                4305,
                s("Invalid reified hint"),
                strings(&[
                    "This is not reified, it cannot be used as a reified type argument",
                    "`Tpain` is reified",
                ]),
            )
        );
        // reified_generics/new_static.php
        assert_eq!(
            render(new_class_reified(Pos::NONE, s("static"), None)),
            (
                4310,
                s("Cannot call `new static` because the current class has reified generics"),
                vec![],
            )
        );
        // reified_generics/new_self_new_parent.php
        assert_eq!(
            render(new_class_reified(Pos::NONE, s("self"), Some(s("\\C")))),
            (
                4310,
                s(
                    "Cannot call `new self` because the current class has reified generics. Try `new C` instead."
                ),
                vec![],
            )
        );
    }

    #[test]
    fn test_non_class_member() {
        // constraints/tparam_class_variable_bad.php
        assert_eq!(
            render(non_class_member(
                Pos::NONE,
                s("$doesNotExist"),
                primary::MethOrProp::prop,
                s("a value of generic type T"),
                Pos::NONE,
            )),
            (
                4252,
                s(
                    "You are trying to access the static property `$doesNotExist` but this is a value of generic type T"
                ),
                strings(&["Definition is here"]),
            )
        );
    }

    #[test]
    fn test_declared_variance() {
        // case_type/recursive/variance1.php
        // `Declared_contravariant { pos; param_pos; msgs }` is rendered with
        // `declared_contravariant pos param_pos msgs`: the claim is on the
        // second position, the first reason on the first one.
        let (pos1, pos2, p) = (pos(10, 13, 14), pos(10, 27, 28), pos(10, 25, 29));
        let emsg: Lazy<Vec<Message<Pos>>> = {
            let (pos2, p) = (pos2.clone(), p.clone());
            lazy!(vec![
                Message(
                    pos2,
                    "This position is covariant (+) because it is the composition of (-)(-)(+)"
                        .into(),
                ),
                Message(
                    p,
                    "(-) This type parameter was declared as contravariant (-) (cf 'Contra')"
                        .into(),
                ),
            ])
        };
        let err = declared_contravariant(pos1.clone(), pos2.clone(), emsg.clone());
        assert_eq!(
            positions(&err),
            (pos2.clone(), vec![pos1.clone(), pos2.clone(), p.clone()])
        );
        assert_eq!(
            render(err),
            (
                4121,
                s("Illegal usage of a contravariant type parameter"),
                strings(&[
                    "This is where the parameter was declared as contravariant `-`",
                    "This position is covariant (+) because it is the composition of (-)(-)(+)",
                    "(-) This type parameter was declared as contravariant (-) (cf 'Contra')",
                ]),
            )
        );
        let err = declared_covariant(pos1.clone(), pos2.clone(), emsg);
        assert_eq!(positions(&err), (pos2.clone(), vec![pos1, pos2, p]));
        let (code, claim, reasons) = render(err);
        assert_eq!(
            (code, claim, &reasons[0][..]),
            (
                4120,
                s("Illegal usage of a covariant type parameter"),
                "This is where the parameter was declared as covariant `+`",
            )
        );
    }

    #[test]
    fn test_static_property_type_generic_param() {
        // typing_fail_static_generic1.php
        let (generic_pos, class_pos, var_type_pos) =
            (pos(15, 16, 17), pos(14, 6, 7), pos(15, 16, 18));
        let err = static_property_type_generic_param(
            generic_pos.clone(),
            class_pos.clone(),
            var_type_pos.clone(),
        );
        assert_eq!(
            positions(&err),
            (generic_pos, vec![var_type_pos, class_pos])
        );
        assert_eq!(
            render(err),
            (
                4279,
                s("A generic parameter cannot be used in the type of a static property"),
                strings(&[
                    "This is where the type of the static property was declared",
                    "This is the class containing the static property",
                ]),
            )
        );
    }

    #[test]
    fn test_contravariant_this() {
        // contravariant_this2.php
        assert_eq!(
            render(contravariant_this(Pos::NONE, s("C"), s("T"))),
            (
                4158,
                s(
                    "The `this` type cannot be used in this contravariant position because its enclosing class `C` is final and has a variant type parameter `T`"
                ),
                vec![],
            )
        );
    }

    #[test]
    fn test_cyclic_typeconst() {
        // tconst/recursive_typeconst_bad.php
        assert_eq!(
            render(cyclic_typeconst(
                Pos::NONE,
                strings(&[
                    "\\MyParent::MyParentShape",
                    "\\MyParentFix::MyParentShapeFix",
                    "\\MyParent::MyParentShape",
                ]),
            )),
            (
                4131,
                s(
                    "Cyclic type constant:\n  `MyParent::MyParentShape` -> `MyParentFix::MyParentShapeFix` -> `MyParent::MyParentShape`"
                ),
                vec![],
            )
        );
    }

    #[test]
    fn test_array_get_with_optional_field() {
        // shape_coalesce.php for the messages. The suite does not print
        // quickfixes: the edits are those the OCaml computes for a receiver
        // at columns 2-4 and a field at columns 5-10 (`$s['bar']`).
        let (field_pos, recv_pos) = (pos(12, 5, 10), pos(12, 2, 4));
        let err = array_get_with_optional_field(field_pos.clone(), &recv_pos, Pos::NONE, s("bar"));
        assert_eq!(
            err.quickfixes,
            vec![Quickfix {
                title: s("Change to `Shapes::idx()`"),
                edits: Edits::Eager(vec![
                    (s(")"), pos(12, 10, 11)),
                    (s(", "), pos(12, 4, 5)),
                    (s("Shapes::idx("), pos(12, 2, 2)),
                ]),
                hint_styles: vec![],
            }]
        );
        assert_eq!(
            render(err),
            (
                4165,
                s(
                    "The field `bar` may not be present in this shape. Use `??` or `Shapes::idx()` instead."
                ),
                strings(&["This is where the field was declared as optional."]),
            )
        );
    }

    #[test]
    fn test_match() {
        // match_statement/bad/nonexhaustive.php
        assert_eq!(
            render(match_not_exhaustive(Pos::NONE, s("B"))),
            (
                4478,
                s(
                    "This match statement is not exhaustive: there is no arm matching values of type `B`"
                ),
                vec![],
            )
        );
        // match_statement/bad/unsupported_scrutinee_types.php
        assert_eq!(
            render(match_on_unsupported_type(
                Pos::NONE,
                s("mixed"),
                strings(&["mixed"]),
            )),
            (
                4479,
                s("This expression has type `mixed`, which is not supported in match statements"),
                vec![],
            )
        );
        assert_eq!(
            render(match_on_unsupported_type(
                Pos::NONE,
                s("(int | vec<int>)"),
                strings(&["vec<int>"]),
            )),
            (
                4479,
                s(
                    "This expression has type `(int | vec<int>)`, which is not supported in match statements because it contains the type `vec<int>`"
                ),
                vec![],
            )
        );
    }

    #[test]
    fn test_position_only() {
        // The functions whose only argument is the position of the claim, and
        // the test of the suite that expects each message.
        let cases: Vec<(fn(Pos) -> T, isize, &str)> = vec![
            // coeffects/poly_var_reassign/catch.php
            (
                immutable_local as fn(Pos) -> T,
                4404,
                "This variable cannot be reassigned because it is used for a dependent context",
            ),
            // method_variance/method_variance_check.php
            (
                method_variance as fn(Pos) -> T,
                4313,
                "Covariance or contravariance is not allowed in type parameters of methods or functions.",
            ),
            // printf2.php
            (
                expected_literal_format_string as fn(Pos) -> T,
                4027,
                "This argument must be a literal format string",
            ),
            // as_expression/any.php
            (
                expecting_type_hint as fn(Pos) -> T,
                4032,
                "Was expecting a type hint",
            ),
            // ddd.php
            (
                expecting_type_hint_variadic as fn(Pos) -> T,
                4033,
                "Was expecting a type hint on this variadic parameter",
            ),
            // arithmetic_any.php
            (
                expecting_return_type_hint as fn(Pos) -> T,
                4030,
                "Was expecting a return type hint",
            ),
            // using/using_bad.php
            (
                duplicate_using_var as fn(Pos) -> T,
                4178,
                "Local variable already used in `using` statement",
            ),
            // using/extend_non_disposable_interface_bad.php
            (
                escaping_disposable as fn(Pos) -> T,
                4180,
                "Variable from `using` clause may only be used as receiver in method invocation or passed to function with `<<__AcceptDisposable>>` parameter attribute",
            ),
            // using/extend_non_disposable_interface_bad.php
            (
                escaping_disposable_parameter as fn(Pos) -> T,
                4188,
                "Parameter with `<<__AcceptDisposable>>` attribute may only be used as receiver in method invocation or passed to another function with `<<__AcceptDisposable>>` parameter attribute",
            ),
            // using/using_bad_escaping_this.php
            (
                escaping_this as fn(Pos) -> T,
                4192,
                "`$this` implementing `IDisposable` or `IAsyncDisposable` may only be used as receiver in method invocation or passed to another function with `<<__AcceptDisposable>>` parameter attribute",
            ),
            // using/using_bad_extend_disposable.php
            (
                must_extend_disposable as fn(Pos) -> T,
                4194,
                "A disposable type may not extend a class or use a trait that is not disposable",
            ),
            // anon12.php
            (
                previous_default as fn(Pos) -> T,
                4077,
                "A previous parameter has a default value.\nRemove all the default values for the preceding parameters,\nor add a default value to this one.",
            ),
            // optional_parameters/optional_parameters_bad.php
            (
                previous_default_or_optional as fn(Pos) -> T,
                4077,
                "A previous parameter has a default value or is optional.\nRemove all the optional or default values for the preceding parameters,\nor add a default value or optional to this one.",
            ),
            // optional_parameters/optional_parameters_bad.php
            (
                optional_parameter_not_abstract as fn(Pos) -> T,
                4484,
                "Optional parameters are not supported on top-level functions or non-abstract methods. Use a default value instead.\n",
            ),
            // argument_unpacking/unpack_call10_unset.php
            (
                unbound_global as fn(Pos) -> T,
                4106,
                "Unbound global constant (Typing)",
            ),
            // classname/static_class_bad.php
            (
                static_outside_class as fn(Pos) -> T,
                4061,
                "`static` is undefined outside of a class",
            ),
            // attributes/attribute_reference_self.php
            (
                self_outside_class as fn(Pos) -> T,
                4059,
                "`self` is undefined outside of a class",
            ),
            // sealed/sealed_classes19.php
            (
                parent_outside_class as fn(Pos) -> T,
                4075,
                "`parent` is undefined outside of a class",
            ),
            // condition_isset_local.php
            (
                isset_in_strict as fn(Pos) -> T,
                4016,
                "`isset` tends to hide errors due to variable typos and so is limited to dynamic checks in `strict` mode",
            ),
            // inout/pseudofunction_etc.php.constraint_method_call
            (
                isset_inout_arg as fn(Pos) -> T,
                4450,
                "`isset` does not allow arguments to be passed by `inout`",
            ),
            // require_class/parent_04.bad.php
            (
                parent_in_trait as fn(Pos) -> T,
                4074,
                "You can only use `parent::` in traits that `require extends`, `require class` or `require this as` a valid class",
            ),
            // argument_unpacking/unpack_default_constructor.php
            (
                constructor_no_args as fn(Pos) -> T,
                4012,
                "This constructor expects no argument",
            ),
            // const_attribute/static/reified_generic_static_const.php
            (
                class_get_reified as fn(Pos) -> T,
                4346,
                "Cannot access static properties on reified generics",
            ),
            // reified_generics/consistent_construct_final_parent.php
            (
                consistent_construct_reified as fn(Pos) -> T,
                4312,
                "This class or one of its ancestors is annotated with `<<__ConsistentConstruct>>`. It cannot have reified generics.",
            ),
            // const_attribute/const_props_vs_readonly_props.php.constraint_method_call
            (
                mutating_const_property as fn(Pos) -> T,
                4196,
                "Cannot mutate a `__Const` property",
            ),
            // const_attribute/const_with_non_const_parent.php
            (
                self_const_parent_not as fn(Pos) -> T,
                4197,
                "A `__Const` class may only extend other `__Const` classes",
            ),
            // unsafe_cast/await.php
            (
                unsafe_cast_await as fn(Pos) -> T,
                4455,
                "UNSAFE_CAST cannot be used as the operand of an await operation",
            ),
        ];
        for (f, code, claim) in cases {
            let p = pos(1, 2, 3);
            let err = f(p.clone());
            assert!(err.quickfixes.is_empty());
            assert_eq!(positions(&err), (p, vec![]));
            assert_eq!(render(err), (code, s(claim), vec![]));
        }
    }

    #[test]
    fn test_to_error() {
        // shape_splat/typaram_alias_requires_feature.php
        assert_eq!(
            render(to_error(
                primary::T::Gated_by_feature_flag {
                    pos: Pos::NONE,
                    name: s("\\T"),
                    feature: s("shape_splat_type_parameters"),
                },
                &env(),
            )),
            (
                4509,
                s(
                    "`T` requires the unstable feature `shape_splat_type_parameters`. Add `<<file: __EnableUnstableFeatures('shape_splat_type_parameters')>>` to use it."
                ),
                vec![],
            )
        );
        // tests_bypass_visibility/internal_class_missing_attr.php
        assert_eq!(
            render(to_error(
                primary::T::Tests_bypass_visibility_on_member_without_class {
                    pos: Pos::NONE,
                    member_name: s("secret"),
                    class_name: s("\\BadClass"),
                },
                &env(),
            )),
            (
                4515,
                s(
                    "`secret` has `<<__TestsBypassVisibility>>` but its containing `internal` class `BadClass` does not"
                ),
                vec![],
            )
        );
        // stdclass_final.php: `Extend_final { pos; name; decl_pos }` is
        // `extend_final pos decl_pos name`.
        let (extend_pos, decl_pos) = (pos(3, 6, 18), pos(31, 14, 22));
        let err = to_error(
            primary::T::Extend_final {
                pos: extend_pos.clone(),
                name: s("\\stdClass"),
                decl_pos: decl_pos.clone(),
            },
            &env(),
        );
        assert_eq!(positions(&err), (extend_pos, vec![decl_pos]));
        assert_eq!(
            render(err),
            (
                4035,
                s("You cannot extend final class `stdClass`"),
                strings(&["Declaration is here"]),
            )
        );
        // printf3.php
        assert_eq!(
            render(to_error(
                primary::T::Expecting_return_type_hint(Pos::NONE),
                &env()
            )),
            (4030, s("Was expecting a return type hint"), vec![])
        );
    }

    #[test]
    fn test_class_pointers() {
        // class_class_bad_syntax.php
        let p = pos(16, 9, 18);
        let err = class_const_to_string(p.clone(), "");
        assert_eq!(
            err.quickfixes,
            vec![Quickfix {
                title: s("Change to `nameof `"),
                edits: Edits::Eager(vec![(s("nameof "), p)]),
                hint_styles: vec![],
            }]
        );
        assert_eq!(
            render(err),
            (
                4482,
                s(
                    "Using `::class` in this position will trigger an implicit runtime conversion to string, please use `nameof `"
                ),
                vec![],
            )
        );
        // classname/new_needs_consistent_construct.php
        assert_eq!(
            render(string_to_class_pointer(Pos::NONE, "\\C", Pos::NONE)),
            (
                4482,
                s(
                    "It is no longer allowed to use a `classname<C>` in this position. Please use a `class<C>` instead."
                ),
                strings(&["Definition is here"]),
            )
        );
    }
}
