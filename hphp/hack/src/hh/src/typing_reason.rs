// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_reason.ml`: the reason a type was inferred, and how it is
//! turned into the `(position, text)` lines of an error message.
//!
//! `oxidized::typing_reason::T_` only has the constructors of the *decl* phase
//! (the OCaml type is a GADT, and the locl constructors are
//! `[@@oxidize.exclude]`d). The reason type of the typechecker, with every
//! constructor, is therefore defined here as [`T_`] (shared as [`T`]); the oxidized
//! one is [`DeclT`] and [`localize`] converts it, as in OCaml. Everything that
//! is not phase dependent (`WitnessDecl`, `PrjSymm`, `FlowKind`, `Blame`, ...)
//! is the oxidized definition, re-exported.
//!
//! Not ported: the JSON form of reasons (`to_json`, `to_json_full` and the
//! `*_to_json` functions). `pp_t_` and `pp_witness_*` are in
//! `crate::typing_show`; the `Derivation` module and `explain`,
//! `debug_reason`, `debug_derivation` are in a submodule of this one.

use std::collections::BTreeMap;
use std::rc::Rc;
use std::sync::LazyLock;

use naming_special_names_rust as sn;
use oxidized::ast_defs::FunKind;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
pub use oxidized::typing_reason::ArgPosition;
pub use oxidized::typing_reason::Axiom;
pub use oxidized::typing_reason::Blame;
pub use oxidized::typing_reason::BlameSource;
pub use oxidized::typing_reason::CstrVariance;
pub use oxidized::typing_reason::CtorKind;
pub use oxidized::typing_reason::ExprDepTypeReason;
pub use oxidized::typing_reason::FieldKind;
pub use oxidized::typing_reason::FlowKind;
pub use oxidized::typing_reason::PessimiseReason;
pub use oxidized::typing_reason::PosId;
pub use oxidized::typing_reason::PrjAsymm;
pub use oxidized::typing_reason::PrjSymm;
pub use oxidized::typing_reason::Ureason;
pub use oxidized::typing_reason::VarianceDir;
pub use oxidized::typing_reason::WitnessDecl;

/// `Tvid.t`
pub type Tvid = oxidized::ident::Ident;

/// `Expression_id.t`
pub type ExpressionId = oxidized::ident::Ident;

/// `decl_t`: the reason of a decl type.
pub type DeclT = oxidized::typing_reason::T_;

/// `t`: the reason of a locl type.
///
/// As in OCaml, where a reason is a pointer to an immutable value, a reason is
/// a shared handle: cloning one (or a type that holds one) only increments a
/// reference count, and a reason that wraps others (`Flow`, `Instantiate`,
/// ...) shares them, since the recursive fields of [`T_`] are the same
/// `Rc<T_>`. Build reasons with the constructor functions of this module
/// (or `T_::Variant(..).into()`), and match on them with `match &**r`.
/// Equality and `Debug` are those of [`T_`], to which `Rc` delegates them.
/// An `Rc`, not an `Arc` (no atomic operations): reasons never leave the
/// thread that typechecks the file (the diagnostics that cross threads hold
/// positions and strings, not reasons); the compiler checks it (`Rc` is not
/// `Send`).
pub type T = Rc<T_>;

// ~~ helpers ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
//
// Copies of functions of other modules: `typing_reason` is compiled without
// the `port` feature too, where `crate::utils`, `crate::markdown_lite`,
// `crate::hh_autoimport` and `crate::expression_id` are not.

/// `Markdown_lite.md_codify`
pub(crate) fn md_codify(s: &str) -> String {
    format!("`{}`", s)
}

/// `Utils.strip_ns`: `\A\B\C` -> `A\B\C`
pub(crate) fn utils_strip_ns(s: &str) -> &str {
    s.strip_prefix('\\').unwrap_or(s)
}

/// `Utils.strip_all_ns`: `\A\B\C` -> `C`
pub(crate) fn utils_strip_all_ns(s: &str) -> &str {
    match s.rfind('\\') {
        Some(i) => &s[i + 1..],
        None => s,
    }
}

/// `Hh_autoimport.is_hh_autoimport`.
///
/// The list of the `hh_autoimport_rust` crate has one name that the OCaml list
/// (`hh_autoimport.ml`) does not have, `class_or_classname`, and the expected
/// outputs depend on the difference (`HH\class_or_classname<C>` keeps its
/// namespace when printed).
pub(crate) fn is_hh_autoimport(s: &str) -> bool {
    hh_autoimport::is_hh_autoimport(s) && s != "class_or_classname"
}

/// `Hh_autoimport.strip_HH_namespace_if_autoimport`
pub(crate) fn strip_hh_namespace_if_autoimport(id: &str) -> &str {
    match id.strip_prefix("HH\\") {
        Some(stripped_id) if is_hh_autoimport(stripped_id) => stripped_id,
        _ => id,
    }
}

/// `strip_ns` of `typing_reason.ml` (and of `typing_print.ml`):
/// `Utils.strip_ns` then `Hh_autoimport.strip_HH_namespace_if_autoimport`.
pub(crate) fn strip_ns(id: &str) -> &str {
    strip_hh_namespace_if_autoimport(utils_strip_ns(id))
}

/// `Expression_id.display`
pub(crate) fn expression_id_display(id: ExpressionId) -> String {
    format!("<expr#{}>", id)
}

/// A `string Lazy.t`: the reasons that mention a printed type (`Typeconst`,
/// `Type_access`) delay the printing until the reason is rendered.
#[derive(Clone)]
pub struct LazyString(std::sync::Arc<LazyLock<String, Box<dyn FnOnce() -> String + Send + Sync>>>);

impl LazyString {
    /// `lazy (f ())`
    pub fn new(f: impl FnOnce() -> String + Send + Sync + 'static) -> Self {
        Self(std::sync::Arc::new(LazyLock::new(Box::new(f))))
    }

    /// `Lazy.from_val`
    pub fn from_val(s: String) -> Self {
        Self::new(move || s)
    }

    /// `Lazy.force`
    pub fn force(&self) -> &str {
        LazyLock::force(&self.0).as_str()
    }
}

/// Lazy values are only ever compared physically (OCaml's structural
/// equality would force them, or fail on the closure): two are equal when they
/// are the same suspension.
impl PartialEq for LazyString {
    fn eq(&self, other: &Self) -> bool {
        std::sync::Arc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for LazyString {}

impl From<String> for LazyString {
    fn from(s: String) -> Self {
        Self::from_val(s)
    }
}

impl From<&str> for LazyString {
    fn from(s: &str) -> Self {
        Self::from_val(s.to_string())
    }
}

impl std::fmt::Debug for LazyString {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.force())
    }
}

// ~~ arg_position ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn arg_pos_str(ap: ArgPosition) -> &'static str {
    match ap {
        ArgPosition::Aonly => "only",
        ArgPosition::Afirst => "first",
        ArgPosition::Asecond => "second",
    }
}

// ~~ expr_dep_type_reason ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn expr_dep_type_reason_string(e: &ExprDepTypeReason) -> String {
    match e {
        ExprDepTypeReason::ERexpr(id) => format!(
            "where {} is a reference to this expression",
            md_codify(&expression_id_display(*id))
        ),
        ExprDepTypeReason::ERstatic => {
            "where `<static>` refers to the late bound type of the enclosing class".to_string()
        }
        ExprDepTypeReason::ERclass(c) => format!(
            "where the class {} was referenced here",
            md_codify(strip_ns(c))
        ),
        ExprDepTypeReason::ERparent(p) => format!(
            "where the class {} (the parent of the enclosing) class was referenced here",
            md_codify(strip_ns(p))
        ),
        ExprDepTypeReason::ERself(c) => format!(
            "where the class {} was referenced here via the keyword `self`",
            md_codify(strip_ns(c))
        ),
        ExprDepTypeReason::ERpu(s) => format!(
            "where {} is a type projected from this expression",
            md_codify(s)
        ),
    }
}

// ~~ Witnesses ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// Witness the reason for a type during typing using the position of a hint or
/// expression
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WitnessLocl {
    Witness(Pos),
    IdxVector(Pos),
    IdxString(Pos),
    Foreach(Pos),
    Asyncforeach(Pos),
    Arith(Pos),
    ArithRet(Pos),
    ArithRetInt(Pos),
    ArithDynamic(Pos),
    BitwiseDynamic(Pos),
    IncdecDynamic(Pos),
    Comp(Pos),
    ConcatRet(Pos),
    Condition(Pos),
    LogicRet(Pos),
    Bitwise(Pos),
    BitwiseRet(Pos),
    NoReturn(Pos),
    NoReturnAsync(Pos),
    RetFunKind(Pos, FunKind),
    Throw(Pos),
    Placeholder(Pos),
    RetDiv(Pos),
    YieldGen(Pos),
    YieldAsyncgen(Pos),
    YieldAsyncnull(Pos),
    YieldSend(Pos),
    UnknownClass(Pos),
    VarParam(Pos),
    UnpackParam(Pos, PosOrDecl, isize),
    NullsafeOp(Pos),
    NullsafePipeOp(Pos),
    Predicated(Pos, String),
    IsRefinement(Pos),
    AsRefinement(Pos),
    Equal(Pos),
    Using(Pos),
    DynamicProp(Pos),
    DynamicCall(Pos),
    DynamicConstruct(Pos),
    IdxDict(Pos),
    IdxSetElement(Pos),
    UnsetField(Pos, String),
    Regex(Pos),
    TypeVariable(Pos, Tvid),
    TypeVariableGenerics(Pos, String, String, Tvid),
    TypeVariableError(Pos, Tvid),
    Shape(Pos, String),
    ShapeLiteral(Pos),
    Destructure(Pos),
    ShapeOrTupleDestructure(Pos),
    KeyValueCollectionKey(Pos),
    Splice(Pos),
    EtBoolean(Pos),
    ConcatOperand(Pos),
    InterpOperand(Pos),
    MissingClass(Pos),
    CapturedLike(Pos),
    UnsafeCast(Pos),
    Pattern(Pos),
    JoinPoint(Pos),
    StaticPropertyAccess(Pos),
    ClassConstantAccess(Pos),
}

fn witness_locl_pos(w: &WitnessLocl) -> &Pos {
    use WitnessLocl::*;
    match w {
        Witness(pos)
        | IdxVector(pos)
        | IdxString(pos)
        | Foreach(pos)
        | Asyncforeach(pos)
        | Arith(pos)
        | ArithRet(pos)
        | ArithRetInt(pos)
        | ArithDynamic(pos)
        | BitwiseDynamic(pos)
        | IncdecDynamic(pos)
        | Comp(pos)
        | ConcatRet(pos)
        | Condition(pos)
        | LogicRet(pos)
        | Bitwise(pos)
        | BitwiseRet(pos)
        | NoReturn(pos)
        | NoReturnAsync(pos)
        | RetFunKind(pos, _)
        | Throw(pos)
        | Placeholder(pos)
        | RetDiv(pos)
        | YieldGen(pos)
        | YieldAsyncgen(pos)
        | YieldAsyncnull(pos)
        | YieldSend(pos)
        | UnknownClass(pos)
        | VarParam(pos)
        | UnpackParam(pos, _, _)
        | NullsafeOp(pos)
        | NullsafePipeOp(pos)
        | Predicated(pos, _)
        | IsRefinement(pos)
        | AsRefinement(pos)
        | Equal(pos)
        | Using(pos)
        | DynamicProp(pos)
        | DynamicCall(pos)
        | DynamicConstruct(pos)
        | IdxDict(pos)
        | IdxSetElement(pos)
        | UnsetField(pos, _)
        | Regex(pos)
        | TypeVariable(pos, _)
        | TypeVariableGenerics(pos, _, _, _)
        | TypeVariableError(pos, _)
        | Shape(pos, _)
        | ShapeLiteral(pos)
        | Destructure(pos)
        | ShapeOrTupleDestructure(pos)
        | KeyValueCollectionKey(pos)
        | Splice(pos)
        | EtBoolean(pos)
        | ConcatOperand(pos)
        | InterpOperand(pos)
        | MissingClass(pos)
        | CapturedLike(pos)
        | UnsafeCast(pos)
        | Pattern(pos)
        | JoinPoint(pos)
        | StaticPropertyAccess(pos)
        | ClassConstantAccess(pos) => pos,
    }
}

pub fn witness_locl_to_raw_pos(w: &WitnessLocl) -> PosOrDecl {
    // Pos_or_decl.of_raw_pos
    witness_locl_pos(w).clone()
}

pub fn get_pri_witness_locl(w: &WitnessLocl) -> isize {
    match w {
        WitnessLocl::Foreach(_) => 1,
        WitnessLocl::Witness(_) => 3,
        _ => 2,
    }
}

pub fn map_pos_witness_locl(
    pos: &dyn Fn(&Pos) -> Pos,
    pos_or_decl: &dyn Fn(&PosOrDecl) -> PosOrDecl,
    w: &WitnessLocl,
) -> WitnessLocl {
    let mut w = w.clone();
    {
        use WitnessLocl::*;
        match &mut w {
            UnpackParam(p1, p2, _) => {
                *p1 = pos(p1);
                *p2 = pos_or_decl(p2);
            }
            Witness(p)
            | IdxVector(p)
            | IdxString(p)
            | Foreach(p)
            | Asyncforeach(p)
            | Arith(p)
            | ArithRet(p)
            | ArithRetInt(p)
            | ArithDynamic(p)
            | BitwiseDynamic(p)
            | IncdecDynamic(p)
            | Comp(p)
            | ConcatRet(p)
            | Condition(p)
            | LogicRet(p)
            | Bitwise(p)
            | BitwiseRet(p)
            | NoReturn(p)
            | NoReturnAsync(p)
            | RetFunKind(p, _)
            | Throw(p)
            | Placeholder(p)
            | RetDiv(p)
            | YieldGen(p)
            | YieldAsyncgen(p)
            | YieldAsyncnull(p)
            | YieldSend(p)
            | UnknownClass(p)
            | VarParam(p)
            | NullsafeOp(p)
            | NullsafePipeOp(p)
            | Predicated(p, _)
            | IsRefinement(p)
            | AsRefinement(p)
            | Equal(p)
            | Using(p)
            | DynamicProp(p)
            | DynamicCall(p)
            | DynamicConstruct(p)
            | IdxDict(p)
            | IdxSetElement(p)
            | UnsetField(p, _)
            | Regex(p)
            | TypeVariable(p, _)
            | TypeVariableGenerics(p, _, _, _)
            | TypeVariableError(p, _)
            | Shape(p, _)
            | ShapeLiteral(p)
            | Destructure(p)
            | ShapeOrTupleDestructure(p)
            | KeyValueCollectionKey(p)
            | Splice(p)
            | EtBoolean(p)
            | ConcatOperand(p)
            | InterpOperand(p)
            | MissingClass(p)
            | CapturedLike(p)
            | UnsafeCast(p)
            | Pattern(p)
            | JoinPoint(p)
            | StaticPropertyAccess(p)
            | ClassConstantAccess(p) => *p = pos(p),
        }
    }
    w
}

pub fn constructor_string_of_witness_locl(w: &WitnessLocl) -> &'static str {
    use WitnessLocl::*;
    match w {
        Witness(_) => "Rwitness",
        IdxVector(_) => "Ridx_vector",
        IdxString(_) => "Ridx_string",
        Foreach(_) => "Rforeach",
        Asyncforeach(_) => "Rasyncforeach",
        Arith(_) => "Rarith",
        ArithRet(_) => "Rarith_ret",
        ArithRetInt(_) => "Rarith_ret_int",
        ArithDynamic(_) => "Rarith_dynamic",
        BitwiseDynamic(_) => "Rbitwise_dynamic",
        IncdecDynamic(_) => "Rincdec_dynamic",
        Comp(_) => "Rcomp",
        ConcatRet(_) => "Rconcat_ret",
        Condition(_) => "Rcondition",
        LogicRet(_) => "Rlogic_ret",
        Bitwise(_) => "Rbitwise",
        BitwiseRet(_) => "Rbitwise_ret",
        NoReturn(_) => "Rno_return",
        NoReturnAsync(_) => "Rno_return_async",
        RetFunKind(..) => "Rret_fun_kind",
        Throw(_) => "Rthrow",
        Placeholder(_) => "Rplaceholder",
        RetDiv(_) => "Rret_div",
        YieldGen(_) => "Ryield_gen",
        YieldAsyncgen(_) => "Ryield_asyncgen",
        YieldAsyncnull(_) => "Ryield_asyncnull",
        YieldSend(_) => "Ryield_send",
        UnknownClass(_) => "Runknown_class",
        VarParam(_) => "Rvar_param",
        UnpackParam(..) => "Runpack_param",
        NullsafeOp(_) => "Rnullsafe_op",
        NullsafePipeOp(_) => "Rnullsafe_pipe_op",
        Predicated(..) => "Rpredicated",
        IsRefinement(_) => "Ris_refinement",
        AsRefinement(_) => "Ras_refinement",
        Equal(_) => "Requal",
        Using(_) => "Rusing",
        DynamicProp(_) => "Rdynamic_prop",
        DynamicCall(_) => "Rdynamic_call",
        DynamicConstruct(_) => "Rdynamic_construct",
        IdxDict(_) => "Ridx_dict",
        IdxSetElement(_) => "Ridx_set_element",
        UnsetField(..) => "Runset_field",
        Regex(_) => "Rregex",
        TypeVariable(..) => "Rtype_variable",
        TypeVariableGenerics(..) => "Rtype_variable_generics",
        TypeVariableError(..) => "Rtype_variable_error",
        Shape(..) => "Rshape",
        ShapeLiteral(_) => "Rshape_literal",
        Destructure(_) => "Rdestructure",
        ShapeOrTupleDestructure(_) => "Rshape_or_tuple_destructure",
        KeyValueCollectionKey(_) => "Rkey_value_collection_key",
        Splice(_) => "Rsplice",
        EtBoolean(_) => "Ret_boolean",
        ConcatOperand(_) => "Rconcat_operand",
        InterpOperand(_) => "Rinterp_operand",
        MissingClass(_) => "Rmissing_class",
        CapturedLike(_) => "Rcaptured_like",
        UnsafeCast(_) => "Runsafe_cast",
        Pattern(_) => "Rpattern",
        JoinPoint(_) => "Rjoin_point",
        StaticPropertyAccess(_) => "Rstatic_property_access",
        ClassConstantAccess(_) => "Rclass_constant_access",
    }
}

/// The text of the `yield`/`async` results, shared by `Ret_fun_kind` and
/// `Ret_fun_kind_from_decl`.
fn ret_fun_kind_to_string(prefix: &str, kind: &FunKind) -> String {
    match kind {
        FunKind::FAsyncGenerator => {
            format!("{} (result of `async function` containing a `yield`)", prefix)
        }
        FunKind::FGenerator => format!("{} (result of function containing a `yield`)", prefix),
        FunKind::FAsync => format!("{} (result of an `async` function)", prefix),
        FunKind::FSync => prefix.to_string(),
    }
}

pub fn witness_locl_to_string(prefix: &str, witness: &WitnessLocl) -> (PosOrDecl, String) {
    use WitnessLocl::*;
    let text = match witness {
        Witness(_) => prefix.to_string(),
        IdxVector(_) => {
            format!(
                "{} because only `int` can be used to index into a `Vector` or `vec`.",
                prefix
            )
        }
        IdxString(_) => {
            format!(
                "{} because only `int` can be used to index into a `string`.",
                prefix
            )
        }
        Foreach(_) => format!("{} because this is used in a `foreach` statement", prefix),
        Asyncforeach(_) => format!(
            "{} because this is used in a `foreach` statement with `await as`",
            prefix
        ),
        Arith(_) => format!("{} because this is used in an arithmetic operation", prefix),
        ArithRet(_) => format!(
            "{} because this is the result of an arithmetic operation",
            prefix
        ),
        ArithRetInt(_) => format!(
            "{} because this is the result of an integer arithmetic operation",
            prefix
        ),
        ArithDynamic(_) => format!(
            "{} because this is the result of an arithmetic operation with two arguments typed `dynamic`",
            prefix
        ),
        BitwiseDynamic(_) => format!(
            "{} because this is the result of a bitwise operation with all arguments typed `dynamic`",
            prefix
        ),
        IncdecDynamic(_) => format!(
            "{} because this is the result of an increment/decrement of an argument typed `dynamic`",
            prefix
        ),
        Comp(_) => format!("{} because this is the result of a comparison", prefix),
        ConcatRet(_) => format!("{} because this is the result of a concatenation", prefix),
        Condition(_) => format!("{} because this is used as a condition", prefix),
        LogicRet(_) => format!(
            "{} because this is the result of a logical operation",
            prefix
        ),
        Bitwise(_) => format!("{} because this is used in a bitwise operation", prefix),
        BitwiseRet(_) => format!(
            "{} because this is the result of a bitwise operation",
            prefix
        ),
        NoReturn(_) => format!(
            "{} because this function does not always return a value",
            prefix
        ),
        NoReturnAsync(_) => format!(
            "{} because this function does not always return a value",
            prefix
        ),
        RetFunKind(_, kind) => ret_fun_kind_to_string(prefix, kind),
        Throw(_) => format!("{} because it is used as an exception", prefix),
        Placeholder(_) => format!(
            "{} (`$_` is a placeholder variable not meant to be used)",
            prefix
        ),
        RetDiv(_) => format!("{} because it is the result of a division `/`", prefix),
        YieldGen(_) => format!("{} (result of function with `yield` in the body)", prefix),
        YieldAsyncgen(_) => format!(
            "{} (result of `async function` with `yield` in the body)",
            prefix
        ),
        YieldAsyncnull(_) => format!(
            "{} because `yield x` is equivalent to `yield null => x` in an `async` function",
            prefix
        ),
        YieldSend(_) => format!(
            "{} (`$generator->send()` can always send a `null` back to a `yield`)",
            prefix
        ),
        UnknownClass(_) => format!("{}; this class name is unknown to Hack", prefix),
        VarParam(_) => format!("{} (variadic argument)", prefix),
        UnpackParam(..) => format!("{} (it is unpacked with `...`)", prefix),
        NullsafeOp(_) => format!("{} (use of `?->` operator)", prefix),
        NullsafePipeOp(_) => format!("{} (use of `|?>` operator)", prefix),
        Predicated(_, f) => format!("{} from the argument to this {} test", prefix, f),
        IsRefinement(_) => format!("{} from this `is` expression test", prefix),
        AsRefinement(_) => format!("{} from this \"as\" assertion", prefix),
        Equal(_) => format!("{} from this equality test", prefix),
        Using(_) => format!("{} because it was assigned in a `using` clause", prefix),
        DynamicProp(_) => format!(
            "{}, the result of accessing a property of a `dynamic` type",
            prefix
        ),
        DynamicCall(_) => format!(
            "{}, the result of calling a `dynamic` type as a function",
            prefix
        ),
        DynamicConstruct(_) => format!(
            "{}, the result of constructing an object with a `dynamic` type",
            prefix
        ),
        IdxDict(_) => format!(
            "{} because only array keys can be used to index into a `Map`, `dict`, `darray`, `Set`, or `keyset`",
            prefix
        ),
        IdxSetElement(_) => format!(
            "{} because only array keys can be used as elements of `keyset` or `Set`",
            prefix
        ),
        UnsetField(_, name) => format!(
            "{} because the field {} was unset here",
            prefix,
            md_codify(name)
        ),
        Regex(_) => format!("{} resulting from this regex pattern", prefix),
        TypeVariable(..) => format!("{} because a type could not be determined here", prefix),
        TypeVariableGenerics(_, tp_name, s, _) => format!(
            "{} because type parameter {} of {} could not be determined. Please add explicit type parameters to the invocation of {}",
            prefix,
            md_codify(tp_name),
            md_codify(s),
            md_codify(s)
        ),
        TypeVariableError(..) => format!("{} because there was another error", prefix),
        Shape(_, fun_name) => format!(
            "{} because {} expects a shape",
            prefix,
            md_codify(fun_name)
        ),
        ShapeLiteral(_) => prefix.to_string(),
        Destructure(_) => format!(
            "{} resulting from a list destructuring assignment or a splat",
            prefix
        ),
        ShapeOrTupleDestructure(_) => format!(
            "{} resulting from a shape or tuple destructuring pattern",
            prefix
        ),
        KeyValueCollectionKey(_) => {
            "This is a key-value collection, which requires `arraykey`-typed keys".to_string()
        }
        Splice(_) => format!(
            "{} because this is being spliced into another Expression Tree",
            prefix
        ),
        EtBoolean(_) => format!(
            "{} because Expression Trees do not allow coercion of truthy values",
            prefix
        ),
        ConcatOperand(_) => "Expected `string` or `int`".to_string(),
        InterpOperand(_) => "Expected `string` or `int`".to_string(),
        MissingClass(_) => format!("{} because class was missing", prefix),
        CapturedLike(_) => format!(
            "{} because this is the type of a local that was captured in a closure",
            prefix
        ),
        UnsafeCast(_) => {
            let unsafe_cast = md_codify(utils_strip_ns(sn::pseudo_functions::UNSAFE_CAST));
            format!(
                "{} because the expression went through a {}. The type might be a lie!",
                prefix, unsafe_cast
            )
        }
        Pattern(_) => format!("{} because of this pattern", prefix),
        JoinPoint(_) => format!("{} because of this statement", prefix),
        StaticPropertyAccess(_) => format!("{} because of this static property access", prefix),
        ClassConstantAccess(_) => format!("{} because of this class constant access", prefix),
    };
    (witness_locl_to_raw_pos(witness), text)
}

pub fn witness_decl_to_raw_pos(w: &WitnessDecl) -> PosOrDecl {
    use WitnessDecl::*;
    match w {
        WitnessFromDecl(pos_or_decl)
        | IdxVectorFromDecl(pos_or_decl)
        | IdxStringFromDecl(pos_or_decl)
        | RetFunKindFromDecl(pos_or_decl, _)
        | Hint(pos_or_decl)
        | ClassClass(pos_or_decl, _)
        | VarParamFromDecl(pos_or_decl)
        | TupleFromSplat(pos_or_decl)
        | InoutParam(pos_or_decl)
        | TconstNoCstr((pos_or_decl, _))
        | VarrayOrDarrayKey(pos_or_decl)
        | VecOrDictKey(pos_or_decl)
        | MissingOptionalField(pos_or_decl, _)
        | ImplicitUpperBound(pos_or_decl, _)
        | PessimisedThis(pos_or_decl)
        | GlobalTypeVariableGenerics(pos_or_decl, _, _)
        | SolveFail(pos_or_decl)
        | CstrOnGenerics(pos_or_decl, _)
        | Enforceable(pos_or_decl)
        | GlobalClassProp(pos_or_decl)
        | GlobalFunParam(pos_or_decl)
        | GlobalFunRet(pos_or_decl)
        | DefaultCapability(pos_or_decl)
        | SupportDynamicType(pos_or_decl)
        | PessimisedInout(pos_or_decl)
        | PessimisedReturn(pos_or_decl, _)
        | PessimisedProp(pos_or_decl, _)
        | IllegalRecursiveType(pos_or_decl, _)
        | SupportDynamicTypeAssume(pos_or_decl)
        | PolymorphicTypeParam(pos_or_decl, _, _, _)
        | EnforcedType(pos_or_decl) => pos_or_decl.clone(),
    }
}

pub fn map_pos_witness_decl(
    pos_or_decl: &dyn Fn(&PosOrDecl) -> PosOrDecl,
    witness: &WitnessDecl,
) -> WitnessDecl {
    let mut w = witness.clone();
    {
        use WitnessDecl::*;
        match &mut w {
            CstrOnGenerics(p, (p2, _)) => {
                *p = pos_or_decl(p);
                *p2 = pos_or_decl(p2);
            }
            WitnessFromDecl(p)
            | IdxVectorFromDecl(p)
            | IdxStringFromDecl(p)
            | RetFunKindFromDecl(p, _)
            | Hint(p)
            | ClassClass(p, _)
            | VarParamFromDecl(p)
            | TupleFromSplat(p)
            | InoutParam(p)
            | TconstNoCstr((p, _))
            | VarrayOrDarrayKey(p)
            | VecOrDictKey(p)
            | MissingOptionalField(p, _)
            | ImplicitUpperBound(p, _)
            | PessimisedThis(p)
            | GlobalTypeVariableGenerics(p, _, _)
            | SolveFail(p)
            | Enforceable(p)
            | GlobalClassProp(p)
            | GlobalFunParam(p)
            | GlobalFunRet(p)
            | DefaultCapability(p)
            | SupportDynamicType(p)
            | PessimisedInout(p)
            | PessimisedReturn(p, _)
            | PessimisedProp(p, _)
            | IllegalRecursiveType(p, _)
            | SupportDynamicTypeAssume(p)
            | PolymorphicTypeParam(p, _, _, _)
            | EnforcedType(p) => *p = pos_or_decl(p),
        }
    }
    w
}

pub fn string_of_pessimise_reason(pr: PessimiseReason) -> &'static str {
    use PessimiseReason::*;
    match pr {
        PRabstract => "abstract",
        PRgenericParam => "generic_param",
        PRgenericApply => "generic_apply",
        PRtypeconst => "typeconst",
        PRtupleOrShape => "tuple_or_shape",
        PRcase => "case",
        PRenum => "enum",
        PRthis => "this",
        PRopaque => "opaque",
        PRdynamic => "dynamic",
        PRfun => "function",
        PRclassptr => "classptr",
        PRvoidOrNoreturn => "void_or_noreturn",
        PRrefinement => "type_refinement",
        PRunionOrIntersection => "union_or_intersection",
        PRxhp => "xhp",
    }
}

pub fn constructor_string_of_witness_decl(w: &WitnessDecl) -> String {
    use WitnessDecl::*;
    match w {
        WitnessFromDecl(_) => "Rwitness_from_decl".to_string(),
        IdxVectorFromDecl(_) => "Ridx_vector_from_decl".to_string(),
        IdxStringFromDecl(_) => "Ridx_string_from_decl".to_string(),
        RetFunKindFromDecl(..) => "Rret_fun_kind_from_decl".to_string(),
        Hint(_) => "Rhint".to_string(),
        ClassClass(..) => "Rclass_class".to_string(),
        VarParamFromDecl(_) => "Rvar_param_from_decl".to_string(),
        TupleFromSplat(_) => "Rtuple_from_splat".to_string(),
        InoutParam(_) => "Rinout_param".to_string(),
        TconstNoCstr(_) => "Rtconst_no_cstr".to_string(),
        VarrayOrDarrayKey(_) => "Rvarray_or_darray_key".to_string(),
        VecOrDictKey(_) => "Rvec_or_dict_key".to_string(),
        MissingOptionalField(..) => "Rmissing_optional_field".to_string(),
        ImplicitUpperBound(..) => "Rimplicit_upper_bound".to_string(),
        GlobalTypeVariableGenerics(..) => "Rglobal_type_variable_generics".to_string(),
        SolveFail(_) => "Rsolve_fail".to_string(),
        CstrOnGenerics(..) => "Rcstr_on_generics".to_string(),
        Enforceable(_) => "Renforceable".to_string(),
        GlobalClassProp(_) => "Rglobal_class_prop".to_string(),
        GlobalFunParam(_) => "Rglobal_fun_param".to_string(),
        GlobalFunRet(_) => "Rglobal_fun_ret".to_string(),
        DefaultCapability(_) => "Rdefault_capability".to_string(),
        SupportDynamicType(_) => "Rsupport_dynamic_type".to_string(),
        PessimisedInout(_) => "Rpessimised_inout".to_string(),
        PessimisedReturn(_, pr) => {
            format!("Rpessimised_return_{}", string_of_pessimise_reason(*pr))
        }
        PessimisedProp(_, pr) => format!("Rpessimised_prop_{}", string_of_pessimise_reason(*pr)),
        PessimisedThis(_) => "Rpessimised_this".to_string(),
        IllegalRecursiveType(..) => "Rillegal_recursive_type".to_string(),
        SupportDynamicTypeAssume(_) => "Rsupport_dynamic_type_assume".to_string(),
        PolymorphicTypeParam(..) => "Rpolymorphic_type_param".to_string(),
        EnforcedType(_) => "Renforced_type".to_string(),
    }
}

pub fn pessimise_reason_to_string(pr: PessimiseReason) -> &'static str {
    use PessimiseReason::*;
    match pr {
        PRabstract => "unknown enforcement for abstract method",
        PRgenericParam => "unenforced generic parameter",
        PRgenericApply => "unenforced generic type arguments",
        PRtypeconst => "unenforced type constant",
        PRtupleOrShape => "unenforced tuple or shape",
        PRcase => "unenforced case type",
        PRenum => "enum enforced only at base type",
        PRthis => "unenforced this",
        PRopaque => "opaque type",
        PRdynamic => "unenforced dynamic",
        PRfun => "unenforced function type",
        PRclassptr => "unenforced class pointer type",
        PRvoidOrNoreturn => "unenforced void or noreturn type",
        PRrefinement => "unenforced type refinement",
        PRunionOrIntersection => "unenforced union or intersection",
        PRxhp => "unenforced XHP attribute",
    }
}

pub fn witness_decl_to_string(prefix: &str, witness: &WitnessDecl) -> (PosOrDecl, String) {
    use WitnessDecl::*;
    let text = match witness {
        WitnessFromDecl(_) => prefix.to_string(),
        PolymorphicTypeParam(_, new_name, orig_name, rank) => {
            let new_name = format!("`{}`", new_name);
            if prefix.ends_with(new_name.as_str()) {
                format!(
                    "{} which corresponds to the rank-{} type parameter `{}` in the polymorphic function",
                    prefix,
                    rank + 1,
                    orig_name
                )
            } else {
                format!(
                    "{} where {} corresponds to the rank-{} type parameter `{}` in the polymorphic function",
                    prefix,
                    new_name,
                    rank + 1,
                    orig_name
                )
            }
        }
        IdxVectorFromDecl(_) => format!(
            "{} because only `int` can be used to index into a `Vector` or `vec`.",
            prefix
        ),
        IdxStringFromDecl(_) => format!(
            "{} because only `int` can be used to index into a `string`.",
            prefix
        ),
        RetFunKindFromDecl(_, kind) => ret_fun_kind_to_string(prefix, kind),
        Hint(_) => prefix.to_string(),
        ClassClass(_, s) => format!(
            "{}; implicitly defined constant `::class` is a reference to class {}",
            prefix,
            md_codify(strip_ns(s))
        ),
        VarParamFromDecl(_) => format!("{} (variadic argument)", prefix),
        TupleFromSplat(_) => format!("{} (tuple from parameters)", prefix),
        InoutParam(_) => format!("{} (`inout` parameter)", prefix),
        TconstNoCstr((_, n)) => format!(
            "{} because the type constant {} lacks a constraint",
            prefix, n
        ),
        VarrayOrDarrayKey(_) => "This is varray_or_darray, which requires arraykey-typed keys when used with an array (used like a hashtable)".to_string(),
        VecOrDictKey(_) => {
            "This is vec_or_dict, which requires keys that have type arraykey".to_string()
        }
        MissingOptionalField(_, name) => format!(
            "{} because the field {} may be set to any type in this shape",
            prefix,
            md_codify(name)
        ),
        ImplicitUpperBound(_, cstr) => format!(
            "{} arising from an implicit {} constraint on this type",
            prefix,
            md_codify(&format!("as {}", cstr))
        ),
        GlobalTypeVariableGenerics(_, tp_name, s) => format!(
            "{} because type parameter {} of {} could not be determined. Please add explicit type parameters to the invocation of {}",
            prefix,
            md_codify(tp_name),
            md_codify(s),
            md_codify(s)
        ),
        SolveFail(_) => format!("{} because a type could not be determined here", prefix),
        CstrOnGenerics(..) => prefix.to_string(),
        Enforceable(_) => format!("{} because it is an unenforceable type", prefix),
        GlobalClassProp(_) => prefix.to_string(),
        GlobalFunParam(_) => prefix.to_string(),
        GlobalFunRet(_) => prefix.to_string(),
        DefaultCapability(_) => format!(
            "{} because the function did not have an explicit context",
            prefix
        ),
        SupportDynamicType(_) => format!(
            "{} because method or function was called on dynamic or like-type",
            prefix
        ),
        SupportDynamicTypeAssume(_) => format!(
            "{} because method must be callable in a dynamic context",
            prefix
        ),
        PessimisedInout(_) => format!(
            "{} because the type of this inout parameter is implicitly a like-type",
            prefix
        ),
        PessimisedReturn(_, pr) => format!(
            "{} because the type of this return is implicitly a like-type due to {}",
            prefix,
            pessimise_reason_to_string(*pr)
        ),
        PessimisedProp(_, pr) => format!(
            "{} because the type of this property is implicitly a like-type due to {}",
            prefix,
            pessimise_reason_to_string(*pr)
        ),
        PessimisedThis(_) => format!(
            "{} from \"as this\" or \"is this\" in a class whose generic parameters (or those of a subclass) are erased at runtime",
            prefix
        ),
        IllegalRecursiveType(_, name) => {
            let name = strip_ns(name);
            format!(
                "{}. Using `mixed` instead of {} because this is an illegal recursive use of {} in the definition of {}",
                prefix, name, name, name
            )
        }
        EnforcedType(_) => prefix.to_string(),
    };
    (witness_decl_to_raw_pos(witness), text)
}

// ~~ Reasons ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// The reason why something is expected to have a certain type (`_ t_`, both
/// phases: a decl reason is a [`DeclT`] and becomes a `T_` with [`localize`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum T_ {
    /// Lift a decl-time witness into a reason
    FromWitnessDecl(WitnessDecl),
    /// Used when applying substitutions { var -> type_ }
    Instantiate {
        type_: Rc<T_>,
        var_name: String,
        var: Rc<T_>,
    },
    NoReason,
    /// Lift a typing-time witness into a reason
    FromWitnessLocl(WitnessLocl),
    /// Records that a type with reason [bound] acted as a lower bound for the
    /// type with reason [of_]
    LowerBound { bound: Rc<T_>, of_: Rc<T_> },
    /// Records the flow of a type from an expression or hint into an
    /// expression during typing
    Flow {
        from: Rc<T_>,
        kind: FlowKind,
        into: Rc<T_>,
    },
    /// Represents the projection of the sub- and supertype during subtype
    /// constraints simplifiction. [sub_prj] is the subtype resulting from the
    /// projection whilst [sub] and [super] are the reasons for the parent
    /// types
    PrjBoth {
        sub_prj: Rc<T_>,
        prj: PrjSymm,
        sub: Rc<T_>,
        super_: Rc<T_>,
    },
    /// Represents the projection of the sub- or supertype during subtype
    /// constraints simplifiction. [part] is the sub/supertype resulting from
    /// the projection whilst [whole] is the reason for the parent type.
    PrjOne {
        part: Rc<T_>,
        whole: Rc<T_>,
        prj: PrjAsymm,
    },
    /// Represents the use of a user-defined axiom about either the subtype or
    /// supertype during subtype constraints simplifiction. [next] is the
    /// sub/supertype resulting from the application of the axiom whilst
    /// [prev] is reason for original type.
    Axiom {
        next: Rc<T_>,
        prev: Rc<T_>,
        axiom: Axiom,
    },
    /// Records the definition site of type alongside the reason recording its
    /// use.
    Def(PosOrDecl, Rc<T_>),
    Solved {
        solution: Rc<T_>,
        of_: Tvid,
        in_: Rc<T_>,
    },
    Invalid,
    MissingField,
    /// Used as an index into a vector-like array or string. Position of
    /// indexing, reason for the indexed type
    Idx(Pos, Rc<T_>),
    /// pos, arg float typing reason, arg position
    ArithRetFloat(Pos, Rc<T_>, ArgPosition),
    /// pos, arg num typing reason, arg position
    ArithRetNum(Pos, Rc<T_>, ArgPosition),
    LostInfo(String, Rc<T_>, Blame),
    Format(Pos, String, Rc<T_>),
    Typeconst(Rc<T_>, (PosOrDecl, String), LazyString, Rc<T_>),
    TypeAccess(Rc<T_>, Vec<(T, LazyString)>),
    ExprDepType(Rc<T_>, PosOrDecl, ExprDepTypeReason),
    LambdaParam(Pos, Rc<T_>),
    DynamicCoercion(Rc<T_>),
    DynamicPartialEnforcement(PosOrDecl, String, Rc<T_>),
    RigidTvarEscape(Pos, String, String, Rc<T_>),
    OpaqueTypeFromModule(PosOrDecl, String, Rc<T_>),
    SDTCall(PosOrDecl, Rc<T_>),
    LikeCall(PosOrDecl, Rc<T_>),
}

impl Default for T_ {
    fn default() -> Self {
        T_::NoReason
    }
}

pub fn to_raw_pos(r: &T_) -> PosOrDecl {
    use T_::*;
    match r {
        NoReason | Invalid | MissingField => Pos::NONE,
        FromWitnessLocl(witness_locl) => witness_locl_to_raw_pos(witness_locl),
        FromWitnessDecl(witness_decl) => witness_decl_to_raw_pos(witness_decl),
        // Deal with legacy reasons which are witness-like but contain other reasons
        Idx(pos, _)
        | ArithRetFloat(pos, _, _)
        | ArithRetNum(pos, _, _)
        | Format(pos, _, _)
        | LambdaParam(pos, _)
        | RigidTvarEscape(pos, _, _, _) => pos.clone(),
        DynamicPartialEnforcement(pos_or_decl, _, _)
        | LikeCall(pos_or_decl, _)
        | SDTCall(pos_or_decl, _) => pos_or_decl.clone(),
        Typeconst(t, (pos_or_decl, _), _, _) if matches!(**t, NoReason) => pos_or_decl.clone(),
        OpaqueTypeFromModule(pos_or_decl, _, _) => pos_or_decl.clone(),
        // When fetching a position of a generic instantiation, report the type
        // application rather than the definition
        Instantiate { type_: t, .. } => to_raw_pos(t),
        // Recurse into flow-like reasons to find the position of the leftmost witness
        Flow { from: t, .. }
        | LowerBound { bound: t, .. }
        | T_::Axiom { next: t, .. }
        | PrjBoth { sub_prj: t, .. }
        | PrjOne { part: t, .. }
        | Solved { solution: t, .. }
        | Def(_, t)
        | LostInfo(_, t, _)
        | TypeAccess(t, _)
        | DynamicCoercion(t) => to_raw_pos(t),
        ExprDepType(t, _, _) => to_raw_pos(t),
        Typeconst(t, _, _, _) => to_raw_pos(t),
    }
}

pub fn get_pri(r: &T_) -> isize {
    match r {
        T_::NoReason => 0,
        T_::FromWitnessLocl(witness) => get_pri_witness_locl(witness),
        T_::FromWitnessDecl(_) => 2,
        T_::LostInfo(..) => 5,
        _ => 2,
    }
}

pub fn compare(r1: &T_, r2: &T_) -> isize {
    let d = get_pri(r2) - get_pri(r1);
    if d != 0 {
        d
    } else {
        match to_raw_pos(r1).cmp(&to_raw_pos(r2)) {
            std::cmp::Ordering::Less => -1,
            std::cmp::Ordering::Equal => 0,
            std::cmp::Ordering::Greater => 1,
        }
    }
}

pub fn map_pos(
    pos: &dyn Fn(&Pos) -> Pos,
    pos_or_decl: &dyn Fn(&PosOrDecl) -> PosOrDecl,
    r: &T_,
) -> T {
    use T_::*;
    let m = |r: &Rc<T_>| map_pos(pos, pos_or_decl, r);
    Rc::new(match r {
        NoReason => NoReason,
        MissingField => MissingField,
        FromWitnessLocl(witness) => {
            FromWitnessLocl(map_pos_witness_locl(pos, pos_or_decl, witness))
        }
        FromWitnessDecl(witness) => FromWitnessDecl(map_pos_witness_decl(pos_or_decl, witness)),
        Idx(p, r) => Idx(pos(p), m(r)),
        LostInfo(s, r1, Blame::Blame(p2, l)) => LostInfo(s.clone(), m(r1), Blame::Blame(pos(p2), *l)),
        Format(p1, s, r) => Format(pos(p1), s.clone(), m(r)),
        Instantiate {
            type_,
            var_name,
            var,
        } => Instantiate {
            type_: m(type_),
            var_name: var_name.clone(),
            var: m(var),
        },
        Typeconst(r1, (p, s1), s2, r2) => {
            Typeconst(m(r1), (pos_or_decl(p), s1.clone()), s2.clone(), m(r2))
        }
        TypeAccess(r1, ls) => TypeAccess(
            m(r1),
            ls.iter()
                .map(|(r, s)| (m(r), s.clone()))
                .collect(),
        ),
        ExprDepType(r, p, n) => ExprDepType(m(r), pos_or_decl(p), n.clone()),
        LambdaParam(p, r) => LambdaParam(pos(p), m(r)),
        ArithRetFloat(p, r, s) => ArithRetFloat(pos(p), m(r), *s),
        ArithRetNum(p, r, s) => ArithRetNum(pos(p), m(r), *s),
        DynamicCoercion(r) => DynamicCoercion(m(r)),
        DynamicPartialEnforcement(p, cn, r) => {
            DynamicPartialEnforcement(pos_or_decl(p), cn.clone(), m(r))
        }
        RigidTvarEscape(p, v, w, r) => RigidTvarEscape(pos(p), v.clone(), w.clone(), m(r)),
        OpaqueTypeFromModule(p, md, r) => OpaqueTypeFromModule(pos_or_decl(p), md.clone(), m(r)),
        SDTCall(p, r) => SDTCall(pos_or_decl(p), m(r)),
        LikeCall(p, r) => LikeCall(pos_or_decl(p), m(r)),
        Invalid => Invalid,
        LowerBound { bound, of_ } => LowerBound {
            bound: m(bound),
            of_: m(of_),
        },
        T_::Axiom { prev, axiom, next } => T_::Axiom {
            prev: m(prev),
            next: m(next),
            axiom: axiom.clone(),
        },
        Flow { from, kind, into } => Flow {
            from: m(from),
            kind: kind.clone(),
            into: m(into),
        },
        PrjBoth {
            sub_prj,
            prj,
            sub,
            super_,
        } => PrjBoth {
            sub_prj: m(sub_prj),
            prj: prj.clone(),
            sub: m(sub),
            super_: m(super_),
        },
        PrjOne { whole, prj, part } => PrjOne {
            whole: m(whole),
            prj: *prj,
            part: m(part),
        },
        Def(def, of_) => Def(pos_or_decl(def), m(of_)),
        Solved { solution, of_, in_ } => Solved {
            solution: m(solution),
            of_: *of_,
            in_: m(in_),
        },
    })
}

pub fn to_constructor_string(r: &T_) -> String {
    use T_::*;
    match r {
        NoReason => "Rnone".to_string(),
        Invalid => "Rinvalid".to_string(),
        MissingField => "Rmissing_field".to_string(),
        FromWitnessLocl(witness) => constructor_string_of_witness_locl(witness).to_string(),
        FromWitnessDecl(witness) => constructor_string_of_witness_decl(witness),
        T_::Axiom { .. } => "Raxiom".to_string(),
        LowerBound { .. } => "Rlower_bound".to_string(),
        Flow { .. } => "Rflow".to_string(),
        PrjBoth { .. } => "Rprj_both".to_string(),
        PrjOne { .. } => "Rprj_one".to_string(),
        Def(..) => "Rdef".to_string(),
        Solved { .. } => "Rsolved".to_string(),
        Idx(..) => "Ridx".to_string(),
        ArithRetFloat(..) => "Rarith_ret_float".to_string(),
        ArithRetNum(..) => "Rarith_ret_num".to_string(),
        LostInfo(..) => "Rlost_info".to_string(),
        Format(..) => "Rformat".to_string(),
        Instantiate { .. } => "Rinstantiate".to_string(),
        Typeconst(..) => "Rtypeconst".to_string(),
        TypeAccess(..) => "Rtype_access".to_string(),
        ExprDepType(..) => "Rexpr_dep_type".to_string(),
        DynamicCoercion(_) => "Rdynamic_coercion".to_string(),
        DynamicPartialEnforcement(..) => "Rdynamic_partial_enforcement".to_string(),
        RigidTvarEscape(..) => "Rrigid_tvar_escape".to_string(),
        OpaqueTypeFromModule(..) => "Ropaque_type_from_module".to_string(),
        SDTCall(..) => "RSDT_call".to_string(),
        LikeCall(..) => "Rlike_call".to_string(),
        LambdaParam(..) => "Rlambda_param".to_string(),
    }
}

pub fn to_pos(r: &T_) -> PosOrDecl {
    to_raw_pos(r)
}

/// The type variable of a `Type_variable` or `Type_variable_generics` witness.
fn tyvar_of_witness(r: &T_) -> Option<Tvid> {
    match r {
        T_::FromWitnessLocl(
            WitnessLocl::TypeVariableGenerics(_, _, _, tvid) | WitnessLocl::TypeVariable(_, tvid),
        ) => Some(*tvid),
        _ => None,
    }
}

fn flow_contains_tyvar(r: &T_) -> bool {
    match r {
        T_::Flow { from, .. } if tyvar_of_witness(from).is_some() => true,
        r if tyvar_of_witness(r).is_some() => true,
        T_::Flow { into, .. } => flow_contains_tyvar(into),
        _ => false,
    }
}

pub fn reverse_flow(t: &T) -> T {
    // The OCaml is in continuation passing style: the flows are rebuilt from
    // the innermost `into` outwards.
    let mut flows = vec![];
    let mut t = t;
    while let T_::Flow { from, into, kind } = &**t {
        flows.push((from, kind));
        t = into;
    }
    // `t` is the last `into`, which is not a flow.
    let mut acc = t.clone();
    for (from, kind) in flows.into_iter().rev() {
        acc = Rc::new(T_::Flow {
            from: acc,
            into: from.clone(),
            kind: kind.clone(),
        });
    }
    acc
}

type Solutions = BTreeMap<Tvid, Rc<T_>>;

/// Translate a reason to a (pos, string) list, suitable for error_l. This
/// previously returned a string, however the need to return multiple lines with
/// multiple locations meant that it needed to more than convert to a string
fn to_string_help(prefix: &str, solutions: &Solutions, r: &T_) -> Vec<(PosOrDecl, String)> {
    use T_::*;
    let p = to_pos(r);
    let contravariant = |class_name: &str| {
        format!(
            "This type argument to {} only allows supertypes (it is contravariant)",
            md_codify(strip_ns(class_name))
        )
    };
    let invariant = |class_name: &str| {
        format!(
            "This type argument to {} must match exactly (it is invariant)",
            md_codify(strip_ns(class_name))
        )
    };
    // `Prj_symm_ctor (_, class_name, _, Dir Contra)` and
    // `Prj_symm_ctor (_, class_name, _, Inv _)`: the note about the variance
    // of the type argument, if this is such a projection.
    let variance_note = |prj: &PrjSymm| match prj {
        PrjSymm::PrjSymmCtor(_, class_name, _, CstrVariance::Dir(VarianceDir::Contra)) => {
            Some(contravariant(class_name))
        }
        PrjSymm::PrjSymmCtor(_, class_name, _, CstrVariance::Inv(_)) => {
            Some(invariant(class_name))
        }
        _ => None,
    };
    match r {
        NoReason => vec![(p, prefix.to_string())],
        MissingField => vec![(p, prefix.to_string())],
        Invalid => vec![(p, prefix.to_string())],
        FromWitnessLocl(witness) => match tyvar_of_witness(r) {
            Some(tvid) if solutions.contains_key(&tvid) => {
                let r = solutions[&tvid].clone();
                let mut solutions = solutions.clone();
                solutions.remove(&tvid);
                to_string_help(prefix, &solutions, &r)
            }
            _ => vec![witness_locl_to_string(prefix, witness)],
        },
        FromWitnessDecl(witness) => vec![witness_decl_to_string(prefix, witness)],
        T_::Axiom {
            next,
            prev,
            axiom: self::Axiom::UpperBound(name),
        } => to_string_help_upper_bound(prefix, solutions, next, prev, name),
        T_::Axiom { next: r1, .. } | Def(_, r1) | PrjOne { part: r1, .. } => {
            to_string_help(prefix, solutions, r1)
        }
        // If we don't have a solution for a type variable use the origin of the flow
        Flow { from, into, kind } if solutions.is_empty() || !flow_contains_tyvar(r) => {
            match kind {
                FlowKind::FlowArrayGet => {
                    let mut res = to_string_help(prefix, solutions, into);
                    res.extend(to_string_help("  from this definition", solutions, from));
                    res
                }
                _ => to_string_help(prefix, solutions, from),
            }
        }
        // otherwise, follow the flow until we reach the type variable
        Flow { from, into, kind } => match tyvar_of_witness(from) {
            Some(tvid) if solutions.contains_key(&tvid) => {
                let r = solutions[&tvid].clone();
                let mut solutions = solutions.clone();
                solutions.remove(&tvid);
                match kind {
                    FlowKind::FlowArrayGet => {
                        let mut res = to_string_help(prefix, &solutions, into);
                        res.extend(to_string_help("  from this definition", &solutions, &r));
                        res
                    }
                    _ => to_string_help(prefix, &solutions, &r),
                }
            }
            _ => to_string_help(prefix, solutions, into),
        },
        Solved {
            solution,
            of_,
            in_: r,
        } => {
            let mut solutions = solutions.clone();
            solutions.insert(*of_, solution.clone());
            to_string_help(prefix, &solutions, r)
        }
        LowerBound { bound: r, of_ } => {
            let note = match &**of_ {
                PrjBoth { prj, .. } => variance_note(prj),
                _ => None,
            };
            let mut res = to_string_help(prefix, solutions, r);
            if let Some(note) = note {
                res.push((p, note));
            }
            res
        }
        PrjBoth { sub_prj, prj, .. } => {
            let mut res = to_string_help(prefix, solutions, sub_prj);
            if let Some(note) = variance_note(prj) {
                res.push((p, note));
            }
            res
        }
        Idx(_, r2) => {
            let p2 = match &**r2 {
                NoReason => p.clone(),
                _ => to_pos(r2),
            };
            vec![
                (p, prefix.to_string()),
                (p2, "This can only be indexed with integers".to_string()),
            ]
        }
        ArithRetFloat(_, r, s) => {
            fn find_last(reason: &T_) -> &T_ {
                match reason {
                    Flow { from: r, .. } | ArithRetFloat(_, r, _) => find_last(r),
                    r => r,
                }
            }
            let r_last = find_last(r);
            let mut res = vec![(
                p,
                format!(
                    "{} because this is the result of an arithmetic operation with a `float` as the {} argument.",
                    prefix,
                    arg_pos_str(*s)
                ),
            )];
            res.extend(to_string_help(
                "Here is why I think the argument is a `float`: this is a `float`",
                solutions,
                r_last,
            ));
            res
        }
        ArithRetNum(_, r, s) => {
            fn find_last(reason: &T_) -> &T_ {
                match reason {
                    Flow { from: r, .. } | ArithRetNum(_, r, _) => find_last(r),
                    r => r,
                }
            }
            let r_last = find_last(r);
            let mut res = vec![(
                p,
                format!(
                    "{} because this is the result of an arithmetic operation with a `num` as the {} argument, and no `float`s.",
                    prefix,
                    arg_pos_str(*s)
                ),
            )];
            res.extend(to_string_help(
                "Here is why I think the argument is a `num`: this is a `num`",
                solutions,
                r_last,
            ));
            res
        }
        LostInfo(s, r1, Blame::Blame(p2, source_of_loss)) => {
            let s = strip_ns(s);
            let cause = match source_of_loss {
                BlameSource::BSlambda => "by this lambda function",
                BlameSource::BScall => "during this call",
                BlameSource::BSassignment => "by this assignment",
                BlameSource::BSoutOfScope => "because of scope change",
            };
            let mut res = to_string_help(prefix, solutions, r1);
            res.push((
                p2.clone(),
                format!(
                    "All the local information about {} has been invalidated {}.\nThis is a limitation of the type-checker; use a local if that's the problem.",
                    md_codify(s),
                    cause
                ),
            ));
            res
        }
        Format(_, s, t) => {
            let s = format!(
                "{} because of the {} format specifier",
                prefix,
                md_codify(s)
            );
            let el = to_string_help("", solutions, t);
            match el.as_slice() {
                [(_, empty)] if empty.is_empty() => vec![(p, s)],
                _ => {
                    let mut res = vec![(p, s)];
                    res.extend(el);
                    res
                }
            }
        }
        Instantiate {
            type_,
            var_name,
            var,
        } => {
            let mut res = to_string_help(prefix, solutions, type_);
            res.extend(to_string_help(
                &format!("  via this generic {}", md_codify(var_name)),
                solutions,
                var,
            ));
            res
        }
        Typeconst(r_orig, (pos, tconst), ty_str, r_root) if matches!(**r_orig, NoReason) => {
            let prefix = if prefix.is_empty() {
                String::new()
            } else {
                format!("{}\n  ", prefix)
            };
            let mut res = vec![(
                pos.clone(),
                format!(
                    "{}by accessing the type constant {}",
                    prefix,
                    md_codify(tconst)
                ),
            )];
            res.extend(to_string_help(
                &format!("on {}", ty_str.force()),
                solutions,
                r_root,
            ));
            res
        }
        Typeconst(r_orig, (pos, tconst), ty_str, r_root) => {
            let mut res = to_string_help(prefix, solutions, r_orig);
            res.push((
                pos.clone(),
                format!(
                    "  resulting from accessing the type constant '{}'",
                    tconst
                ),
            ));
            res.extend(to_string_help(
                &format!("  on {}", ty_str.force()),
                solutions,
                r_root,
            ));
            res
        }
        TypeAccess(r0, l) => match (&**r0, l.as_slice()) {
            (Typeconst(r1, _, _, _), [(r, _), l @ ..]) if matches!(**r1, NoReason) => {
                to_string_help(
                    prefix,
                    solutions,
                    &TypeAccess(r.clone(), l.to_vec()),
                )
            }
            (Typeconst(r, _, _, _), x) => {
                to_string_help(prefix, solutions, &TypeAccess(r.clone(), x.to_vec()))
            }
            (TypeAccess(r, expand2), expand1) => {
                let mut expand = expand1.to_vec();
                expand.extend(expand2.iter().cloned());
                to_string_help(prefix, solutions, &TypeAccess(r.clone(), expand))
            }
            (r, []) => to_string_help(prefix, solutions, r),
            (r, [(r_hd, tconst), tail @ ..]) => {
                let mut res = to_string_help(prefix, solutions, r);
                res.extend(to_string_help(
                    &format!(
                        "  resulting from expanding the type constant {}",
                        md_codify(tconst.force())
                    ),
                    solutions,
                    r_hd,
                ));
                for (r, s) in tail {
                    res.extend(to_string_help(
                        &format!(
                            "  then expanding the type constant {}",
                            md_codify(s.force())
                        ),
                        solutions,
                        r,
                    ));
                }
                res
            }
        },
        ExprDepType(r, p, e) => {
            let mut res = to_string_help(prefix, solutions, r);
            res.push((p.clone(), format!("  {}", expr_dep_type_reason_string(e))));
            res
        }
        // If type originated with an unannotated lambda parameter with type variable type,
        // suggested annotating the lambda parameter. Otherwise defer to original reason.
        LambdaParam(_, r_orig) => match tyvar_of_witness(r_orig) {
            Some(tvid) if solutions.contains_key(&tvid) => {
                let r = solutions[&tvid].clone();
                let mut solutions = solutions.clone();
                solutions.remove(&tvid);
                to_string_help(prefix, &solutions, &r)
            }
            tyvar => {
                if tyvar.is_some()
                    || matches!(**r_orig, FromWitnessDecl(WitnessDecl::SolveFail(_)))
                {
                    vec![(
                        p,
                        format!(
                            "{} because the type of the lambda parameter could not be determined. Please add a type hint to the parameter",
                            prefix
                        ),
                    )]
                } else {
                    to_string_help(prefix, solutions, r_orig)
                }
            }
        },
        DynamicCoercion(r) => to_string_help(prefix, solutions, r),
        DynamicPartialEnforcement(p, cn, r_orig) => {
            let mut res = to_string_help(prefix, solutions, r_orig);
            res.push((
                p.clone(),
                format!(
                    "while allowing dynamic to flow into {}",
                    utils_strip_all_ns(cn)
                ),
            ));
            res
        }
        RigidTvarEscape(p, what, tvar, r_orig) => {
            let tvar = md_codify(tvar);
            let mut res = vec![(
                p.clone(),
                format!("{} because {} escaped from {}", prefix, tvar, what),
            )];
            res.extend(to_string_help(
                &format!("  where {} originates from", tvar),
                solutions,
                r_orig,
            ));
            res
        }
        SDTCall(p, r_orig) => {
            let mut res = vec![(
                p.clone(),
                format!(
                    "{} because this dynamic or like type value passed through a function that supports dynamic calling",
                    prefix
                ),
            )];
            res.extend(to_string_help(
                "The type originated from here",
                solutions,
                r_orig,
            ));
            res
        }
        LikeCall(p, r_orig) => {
            let mut res = vec![(
                p.clone(),
                format!(
                    "{} because this dynamic or like type value was used as a receiver in a method call",
                    prefix
                ),
            )];
            res.extend(to_string_help(
                "The type originated from here",
                solutions,
                r_orig,
            ));
            res
        }
        OpaqueTypeFromModule(p, module_, r_orig) => {
            let mut res = vec![(
                p.clone(),
                format!(
                    "{} because this is an internal symbol from module {}, which is opaque outside of the module.",
                    prefix, module_
                ),
            )];
            res.extend(to_string_help(
                "The type originated from here",
                solutions,
                r_orig,
            ));
            res
        }
    }
}

fn to_string_help_upper_bound(
    prefix: &str,
    solutions: &Solutions,
    next: &T_,
    prev: &T_,
    name: &str,
) -> Vec<(PosOrDecl, String)> {
    // Don't report definitions on internal generated types
    let internal = |c: char| matches!(c, '#' | '$' | ':');
    let bound = if name.chars().any(internal)
        || name == sn::typehints::THIS
        || name == sn::classes::SUPPORT_DYN
    {
        vec![]
    } else {
        to_string_help(
            &format!("  by the definition of {}", md_codify(strip_ns(name))),
            solutions,
            next,
        )
    };
    let mut res = to_string_help(prefix, solutions, prev);
    res.extend(bound);
    res
}

/// The lines of an error message that explain a type: `prefix` (for instance
/// "Expected `int`") with the suffix the reason adds to it, at the position of
/// the reason, followed by any further lines the reason gives.
///
/// For a [`DeclT`], call [`localize`] first.
pub fn to_string(prefix: &str, r: &T_) -> Vec<(PosOrDecl, String)> {
    to_string_help(prefix, &Solutions::new(), r)
}

// -- Constructors ----------------------------------------------------------

/// The reasons without a payload are built once per thread and shared. In
/// OCaml the constant constructors (`No_reason`, `Invalid`, `Missing_field`
/// of `typing_reason.ml`, `Constructors`) are immediates and cost nothing;
/// here an `Rc::new` per call would allocate for every `Reason.none`, which
/// is the reason of many types. Cloning the shared `Rc` only bumps a count,
/// and two `none()` stay physically equal, as in OCaml.
macro_rules! shared_constant_reason {
    ($name:ident, $variant:ident) => {
        pub fn $name() -> T {
            thread_local! {
                static R: T = Rc::new(T_::$variant);
            }
            R.with(T::clone)
        }
    };
}

shared_constant_reason!(none, NoReason);

pub fn from_witness_locl(witness: WitnessLocl) -> T {
    Rc::new(T_::FromWitnessLocl(witness))
}

pub fn from_witness_decl(witness: WitnessDecl) -> T {
    Rc::new(T_::FromWitnessDecl(witness))
}

/// Constructors whose only argument is the position of a locl witness.
macro_rules! witness_locl_constructors {
    ($($name:ident => $variant:ident,)*) => {
        $(
            pub fn $name(p: Pos) -> T {
                from_witness_locl(WitnessLocl::$variant(p))
            }
        )*
    };
}

/// Constructors whose only argument is the position of a decl witness.
macro_rules! witness_decl_constructors {
    ($($name:ident => $variant:ident,)*) => {
        $(
            pub fn $name(p: PosOrDecl) -> T {
                from_witness_decl(WitnessDecl::$variant(p))
            }
        )*
    };
}

witness_locl_constructors! {
    witness => Witness,
    idx_vector => IdxVector,
    idx_string => IdxString,
    foreach => Foreach,
    asyncforeach => Asyncforeach,
    arith => Arith,
    arith_ret => ArithRet,
    arith_ret_int => ArithRetInt,
    arith_dynamic => ArithDynamic,
    bitwise_dynamic => BitwiseDynamic,
    incdec_dynamic => IncdecDynamic,
    comp => Comp,
    concat_ret => ConcatRet,
    condition => Condition,
    logic_ret => LogicRet,
    bitwise => Bitwise,
    bitwise_ret => BitwiseRet,
    no_return => NoReturn,
    no_return_async => NoReturnAsync,
    static_prop_access => StaticPropertyAccess,
    class_const_access => ClassConstantAccess,
    throw => Throw,
    placeholder => Placeholder,
    ret_div => RetDiv,
    yield_gen => YieldGen,
    yield_asyncgen => YieldAsyncgen,
    yield_asyncnull => YieldAsyncnull,
    yield_send => YieldSend,
    unknown_class => UnknownClass,
    var_param => VarParam,
    nullsafe_op => NullsafeOp,
    nullsafe_pipe_op => NullsafePipeOp,
    is_refinement => IsRefinement,
    as_refinement => AsRefinement,
    equal => Equal,
    using => Using,
    dynamic_prop => DynamicProp,
    dynamic_call => DynamicCall,
    dynamic_construct => DynamicConstruct,
    idx_dict => IdxDict,
    idx_set_element => IdxSetElement,
    regex => Regex,
    shape_literal => ShapeLiteral,
    // Reason for types arising from [list()] destructuring or splat unpacking.
    destructure => Destructure,
    // Reason for types arising from shape or tuple destructuring patterns. Used
    // for fresh tyvars and nullable wrapping in {!Typing_destructure}.
    shape_or_tuple_destructure => ShapeOrTupleDestructure,
    key_value_collection_key => KeyValueCollectionKey,
    splice => Splice,
    et_boolean => EtBoolean,
    concat_operand => ConcatOperand,
    interp_operand => InterpOperand,
    missing_class => MissingClass,
    captured_like => CapturedLike,
    unsafe_cast => UnsafeCast,
    pattern => Pattern,
    join_point => JoinPoint,
}

witness_decl_constructors! {
    witness_from_decl => WitnessFromDecl,
    idx_vector_from_decl => IdxVectorFromDecl,
    idx_string_from_decl => IdxStringFromDecl,
    hint => Hint,
    var_param_from_decl => VarParamFromDecl,
    tuple_from_splat => TupleFromSplat,
    inout_param => InoutParam,
    varray_or_darray_key => VarrayOrDarrayKey,
    vec_or_dict_key => VecOrDictKey,
    solve_fail => SolveFail,
    enforceable => Enforceable,
    global_class_prop => GlobalClassProp,
    global_fun_param => GlobalFunParam,
    global_fun_ret => GlobalFunRet,
    default_capability => DefaultCapability,
    support_dynamic_type => SupportDynamicType,
    support_dynamic_type_assume => SupportDynamicTypeAssume,
    pessimised_inout => PessimisedInout,
    pessimised_this => PessimisedThis,
    enforced_type => EnforcedType,
}

pub fn idx((p, r): (Pos, T)) -> T {
    Rc::new(T_::Idx(p, r))
}

pub fn arith_ret_float((p, r, a): (Pos, T, ArgPosition)) -> T {
    Rc::new(T_::ArithRetFloat(p, r, a))
}

pub fn arith_ret_num((p, r, a): (Pos, T, ArgPosition)) -> T {
    Rc::new(T_::ArithRetNum(p, r, a))
}

pub fn ret_fun_kind((p, k): (Pos, FunKind)) -> T {
    from_witness_locl(WitnessLocl::RetFunKind(p, k))
}

pub fn ret_fun_kind_from_decl((p, k): (PosOrDecl, FunKind)) -> T {
    from_witness_decl(WitnessDecl::RetFunKindFromDecl(p, k))
}

pub fn polymorphic_type_param(
    (p, new_name, orig_name, rank): (PosOrDecl, String, String, isize),
) -> T {
    from_witness_decl(WitnessDecl::PolymorphicTypeParam(
        p, new_name, orig_name, rank,
    ))
}

pub fn lost_info((s, r, b): (String, T, Blame)) -> T {
    Rc::new(T_::LostInfo(s, r, b))
}

pub fn format((p, s, r): (Pos, String, T)) -> T {
    Rc::new(T_::Format(p, s, r))
}

pub fn class_class((p, s): (PosOrDecl, String)) -> T {
    from_witness_decl(WitnessDecl::ClassClass(p, s))
}

pub fn unpack_param((p1, p2, n): (Pos, PosOrDecl, isize)) -> T {
    from_witness_locl(WitnessLocl::UnpackParam(p1, p2, n))
}

pub fn instantiate(type_: T, var_name: String, var: T) -> T {
    Rc::new(T_::Instantiate {
        type_,
        var_name,
        var,
    })
}

pub fn typeconst((r, p, s, r2): (T, (PosOrDecl, String), LazyString, T)) -> T {
    Rc::new(T_::Typeconst(r, p, s, r2))
}

pub fn type_access((r, l): (T, Vec<(T, LazyString)>)) -> T {
    Rc::new(T_::TypeAccess(r, l))
}

pub fn expr_dep_type((r, p, d): (T, PosOrDecl, ExprDepTypeReason)) -> T {
    Rc::new(T_::ExprDepType(r, p, d))
}

pub fn tconst_no_cstr(id: PosId) -> T {
    from_witness_decl(WitnessDecl::TconstNoCstr(id))
}

pub fn predicated((p, s): (Pos, String)) -> T {
    from_witness_locl(WitnessLocl::Predicated(p, s))
}

pub fn missing_optional_field((p, s): (PosOrDecl, String)) -> T {
    from_witness_decl(WitnessDecl::MissingOptionalField(p, s))
}

pub fn unset_field((p, s): (Pos, String)) -> T {
    from_witness_locl(WitnessLocl::UnsetField(p, s))
}

pub fn implicit_upper_bound((p, s): (PosOrDecl, String)) -> T {
    from_witness_decl(WitnessDecl::ImplicitUpperBound(p, s))
}

pub fn type_variable(p: Pos, tvid: Tvid) -> T {
    from_witness_locl(WitnessLocl::TypeVariable(p, tvid))
}

pub fn type_variable_generics((p, n1, n2): (Pos, String, String), tvid: Tvid) -> T {
    from_witness_locl(WitnessLocl::TypeVariableGenerics(p, n1, n2, tvid))
}

pub fn type_variable_error(p: Pos, tvid: Tvid) -> T {
    from_witness_locl(WitnessLocl::TypeVariableError(p, tvid))
}

pub fn global_type_variable_generics((p, n1, n2): (PosOrDecl, String, String)) -> T {
    from_witness_decl(WitnessDecl::GlobalTypeVariableGenerics(p, n1, n2))
}

pub fn cstr_on_generics((p, id): (PosOrDecl, PosId)) -> T {
    from_witness_decl(WitnessDecl::CstrOnGenerics(p, id))
}

pub fn lambda_param((p, r): (Pos, T)) -> T {
    Rc::new(T_::LambdaParam(p, r))
}

pub fn shape((p, s): (Pos, String)) -> T {
    from_witness_locl(WitnessLocl::Shape(p, s))
}

pub fn dynamic_coercion(r: T) -> T {
    Rc::new(T_::DynamicCoercion(r))
}

pub fn dynamic_partial_enforcement((p, s, r): (PosOrDecl, String, T)) -> T {
    Rc::new(T_::DynamicPartialEnforcement(p, s, r))
}

pub fn rigid_tvar_escape((p, n1, n2, r): (Pos, String, String, T)) -> T {
    Rc::new(T_::RigidTvarEscape(p, n1, n2, r))
}

pub fn opaque_type_from_module((p, s, r): (PosOrDecl, String, T)) -> T {
    Rc::new(T_::OpaqueTypeFromModule(p, s, r))
}

pub fn support_dynamic_type_call((p, r): (PosOrDecl, T)) -> T {
    Rc::new(T_::SDTCall(p, r))
}

pub fn like_call((p, r): (PosOrDecl, T)) -> T {
    Rc::new(T_::LikeCall(p, r))
}

shared_constant_reason!(invalid, Invalid);

pub fn pessimised_return(p: PosOrDecl, r: PessimiseReason) -> T {
    from_witness_decl(WitnessDecl::PessimisedReturn(p, r))
}

pub fn pessimised_prop(p: PosOrDecl, r: PessimiseReason) -> T {
    from_witness_decl(WitnessDecl::PessimisedProp(p, r))
}

fn flow(from: T, into: T, kind: FlowKind) -> T {
    match &*from {
        T_::Flow {
            from,
            into: into_l,
            kind: kind_l,
        } => Rc::new(T_::Flow {
            from: from.clone(),
            into: flow(into_l.clone(), into, kind),
            kind: kind_l.clone(),
        }),
        _ => Rc::new(T_::Flow { from, kind, into }),
    }
}

pub fn flow_array_get(def: T, access: T) -> T {
    flow(def, access, FlowKind::FlowArrayGet)
}

pub fn flow_assign(rhs: T, lval: T) -> T {
    flow(rhs, lval, FlowKind::FlowAssign)
}

pub fn flow_local(def: T, use_: T) -> T {
    flow(def, use_, FlowKind::FlowLocal)
}

pub fn flow_call(def: T, use_: T) -> T {
    flow(def, use_, FlowKind::FlowCall)
}

pub fn flow_prop_access(def: T, use_: T) -> T {
    flow(def, use_, FlowKind::FlowPropAccess)
}

pub fn flow_const_access(def: T, use_: T) -> T {
    flow(def, use_, FlowKind::FlowConstAccess)
}

pub fn flow_return_expr(expr: T, ret: T) -> T {
    flow(expr, ret, FlowKind::FlowReturnExpr)
}

pub fn flow_return_hint(hint: T, use_: T) -> T {
    flow(hint, use_, FlowKind::FlowFunReturn)
}

pub fn flow_param_hint(hint: T, param: T) -> T {
    flow(hint, param, FlowKind::FlowParamHint)
}

pub fn solved(of_: Tvid, solution: T, in_: T) -> T {
    Rc::new(T_::Solved {
        solution,
        of_,
        in_,
    })
}

pub fn axiom_extends(child: T, ancestor: T) -> T {
    Rc::new(T_::Axiom {
        axiom: Axiom::Extends,
        prev: child,
        next: ancestor,
    })
}

pub fn axiom_upper_bound(bound: T, of_: T, name: String) -> T {
    Rc::new(T_::Axiom {
        axiom: Axiom::UpperBound(name),
        prev: of_,
        next: bound,
    })
}

pub fn axiom_lower_bound(bound: T, of_: T) -> T {
    Rc::new(T_::Axiom {
        axiom: Axiom::LowerBound,
        prev: of_,
        next: bound,
    })
}

pub fn trans_lower_bound(bound: T, of_: T) -> T {
    Rc::new(T_::LowerBound {
        bound,
        of_,
    })
}

pub fn definition(def: PosOrDecl, of_: T) -> T {
    Rc::new(T_::Def(def, of_))
}

// -- Symmetric projections --

fn prj_symm_co(sub: T, sub_prj: T, super_: T, prj: PrjSymm) -> T {
    Rc::new(T_::PrjBoth {
        sub_prj,
        prj,
        sub,
        super_,
    })
}

fn prj_symm_contra(sub: T, super_: T, super_prj: T, prj: PrjSymm) -> T {
    Rc::new(T_::PrjBoth {
        sub_prj: super_prj,
        prj,
        sub,
        super_,
    })
}

/// Record the decomposition of a covariant type parameter when simplifying a
/// subtype constraint between two type constructors
pub fn prj_ctor_co(
    sub: T,
    sub_prj: T,
    super_: T,
    ctor_kind: CtorKind,
    nm: String,
    idx: isize,
    is_invariant: bool,
) -> T {
    let var = if is_invariant {
        CstrVariance::Inv(VarianceDir::Co)
    } else {
        CstrVariance::Dir(VarianceDir::Co)
    };
    let prj = PrjSymm::PrjSymmCtor(ctor_kind, nm, idx, var);
    prj_symm_co(sub, sub_prj, super_, prj)
}

/// Record the decomposition of a contravariant type parameter when simplifying
/// a subtype constraint between two classes
pub fn prj_ctor_contra(
    sub: T,
    super_: T,
    super_prj: T,
    ctor_kind: CtorKind,
    nm: String,
    idx: isize,
    is_invariant: bool,
) -> T {
    let var = if is_invariant {
        CstrVariance::Inv(VarianceDir::Contra)
    } else {
        CstrVariance::Dir(VarianceDir::Contra)
    };
    let prj = PrjSymm::PrjSymmCtor(ctor_kind, nm, idx, var);
    prj_symm_contra(sub, super_, super_prj, prj)
}

/// Record the decomposition of a subtype contraint between two negated types
/// into a constraint between the two inner types
pub fn prj_neg(sub: T, sub_prj: T, super_: T) -> T {
    prj_symm_co(sub, sub_prj, super_, PrjSymm::PrjSymmNeg)
}

/// Record the decomposition of a subtype contraint between two supportdyn types
/// into a constraint between the two non-dynamic types
pub fn prj_supportdyn(sub: T, sub_prj: T, super_: T) -> T {
    prj_symm_co(sub, sub_prj, super_, PrjSymm::PrjSymmSupportdyn)
}

/// Record the decomposition of a subtype contraint between two nullable types
/// into a constraint between the two inner non-null types
pub fn prj_nullable(sub: T, sub_prj: T, super_: T) -> T {
    prj_symm_co(sub, sub_prj, super_, PrjSymm::PrjSymmNullable)
}

/// Record the decomposition of a subtype contraint between two tuple types into
/// a constraint between the two types at index [idx]
pub fn prj_tuple(sub: T, sub_prj: T, super_: T, idx: isize) -> T {
    let prj = PrjSymm::PrjSymmTuple(idx);
    prj_symm_co(sub, sub_prj, super_, prj)
}

/// Record the decomposition of a subtype contraint between two shape types into
/// a constraint between the two types for a given field [lbl]; since the
/// subtype relationship may depend on the field 'kind' in the sub- and
/// supertype, we also record this information
pub fn prj_shape(
    sub: T,
    sub_prj: T,
    super_: T,
    lbl: String,
    kind_sub: FieldKind,
    kind_super: FieldKind,
) -> T {
    let prj = PrjSymm::PrjSymmShape(lbl, kind_sub, kind_super);
    prj_symm_co(sub, sub_prj, super_, prj)
}

/// Record the decomposition of a subtype contraint between two function types
/// into a constraint between the types of a given parameter; when the function
/// has variadic arguments the indices may differ so we explicitly record the
/// index in both sub- and supertype
pub fn prj_fn_param(sub: T, super_: T, super_prj: T, idx_sub: isize, idx_super: isize) -> T {
    let prj = PrjSymm::PrjSymmFnParam(idx_super, idx_sub);
    prj_symm_contra(sub, super_, super_prj, prj)
}

/// Record the decomposition of a subtype contraint between two function types
/// into a constraint between the types of a given inout parameter treated as
/// covariant
pub fn prj_fn_param_inout_co(
    sub: T,
    sub_prj: T,
    super_: T,
    idx_sub: isize,
    idx_super: isize,
) -> T {
    let prj = PrjSymm::PrjSymmFnParamInout(idx_sub, idx_super, VarianceDir::Co);
    prj_symm_co(sub, sub_prj, super_, prj)
}

/// Record the decomposition of a subtype contraint between two function types
/// into a constraint between the types of a given inout parameter treated as
/// contravariant
pub fn prj_fn_param_inout_contra(
    sub: T,
    super_: T,
    super_prj: T,
    idx_sub: isize,
    idx_super: isize,
) -> T {
    let prj = PrjSymm::PrjSymmFnParamInout(idx_super, idx_sub, VarianceDir::Contra);
    prj_symm_contra(sub, super_, super_prj, prj)
}

/// Record the decomposition of a subtype contraint between two function types
/// into a constraint between the return types
pub fn prj_fn_ret(sub: T, sub_prj: T, super_: T) -> T {
    let prj = PrjSymm::PrjSymmFnRet;
    prj_symm_co(sub, sub_prj, super_, prj)
}

// -- Asymmetric projections --

fn prj_asymm_sub(sub: T, sub_prj: T, prj: PrjAsymm) -> T {
    Rc::new(T_::PrjOne {
        part: sub_prj,
        prj,
        whole: sub,
    })
}

fn prj_asymm_super(super_: T, super_prj: T, prj: PrjAsymm) -> T {
    Rc::new(T_::PrjOne {
        part: super_prj,
        prj,
        whole: super_,
    })
}

/// Record the decomposition of a subtype constraint between an aggregate type
/// in subtype position and some other type into another contraint between some
/// type contained in the aggregate and the other type
pub fn prj_contains_sub(sub: T, sub_prj: T) -> T {
    prj_asymm_sub(sub, sub_prj, PrjAsymm::PrjAsymmContains)
}

/// Record the decomposition of a subtype constraint between an aggregate type
/// in supertype position and some other type into another contraint between
/// some type contained in the aggregate and the other type
pub fn prj_contains_super(super_: T, super_prj: T) -> T {
    prj_asymm_super(super_, super_prj, PrjAsymm::PrjAsymmContains)
}

/// Record the decomposition of a subtype constraint between a union type in
/// subtype position and some other type into another contraint between some
/// member of the union and the other type
pub fn prj_union_sub(sub: T, sub_prj: T) -> T {
    prj_asymm_sub(sub, sub_prj, PrjAsymm::PrjAsymmUnion)
}

/// Record the decomposition of a subtype constraint between a union type in
/// supertype position and some other type into another contraint between some
/// member of the union and the other type
pub fn prj_union_super(super_: T, super_prj: T) -> T {
    prj_asymm_super(super_, super_prj, PrjAsymm::PrjAsymmUnion)
}

/// Record the decomposition of a subtype constraint between a intersection type
/// in subtype position and some other type into another contraint between some
/// member of the union and the other type
pub fn prj_inter_sub(sub: T, sub_prj: T) -> T {
    prj_asymm_sub(sub, sub_prj, PrjAsymm::PrjAsymmInter)
}

/// Record the decomposition of a subtype constraint between a intersection type
/// in supertype position and some other type into another contraint between
/// some member of the union and the other type
pub fn prj_inter_super(super_: T, super_prj: T) -> T {
    prj_asymm_super(super_, super_prj, PrjAsymm::PrjAsymmInter)
}

/// Record the decomposition of a subtype constraint between a negated type in
/// subtype position and some other type into another contraint between some
/// member of the union and the other type
pub fn prj_neg_sub(sub: T, sub_prj: T) -> T {
    prj_asymm_sub(sub, sub_prj, PrjAsymm::PrjAsymmNeg)
}

/// Record the decomposition of a subtype constraint between a negated type in
/// supertype position and some other type into another contraint between some
/// member of the union and the other type
pub fn prj_neg_super(super_: T, super_prj: T) -> T {
    prj_asymm_super(super_, super_prj, PrjAsymm::PrjAsymmNeg)
}

/// Record the decomposition of a subtype constraint between a nullable type in
/// subtype position and some other type into another contraint between either
/// the null or non-null part of the nullable type and the other type
pub fn prj_nullable_sub(sub: T, sub_prj: T) -> T {
    prj_asymm_sub(sub, sub_prj, PrjAsymm::PrjAsymmNullable)
}

/// Record the decomposition of a subtype constraint between a nullable type in
/// supertype position and some other type into another contraint between either
/// the null or non-null part of the nullable type and the other type
pub fn prj_nullable_super(super_: T, super_prj: T) -> T {
    prj_asymm_super(super_, super_prj, PrjAsymm::PrjAsymmNullable)
}

/// Record the decomposition of a subtype constraint between a num type in
/// subtype position and some other type into another contraint between either
/// the int or float part of the num type and the other type
pub fn prj_num_sub(sub: T, sub_prj: T) -> T {
    prj_asymm_sub(sub, sub_prj, PrjAsymm::PrjAsymmNum)
}

/// Record the decomposition of a subtype constraint between a num type in
/// supertype position and some other type into another contraint between either
/// the int or float part of the num type and the other type
pub fn prj_num_super(super_: T, super_prj: T) -> T {
    prj_asymm_super(super_, super_prj, PrjAsymm::PrjAsymmNum)
}

/// Record the decomposition of a subtype constraint between an arraykey type in
/// subtype position and some other type into another contraint between either
/// the int or string part of the arraykey type and the other type
pub fn prj_arraykey_sub(sub: T, sub_prj: T) -> T {
    prj_asymm_sub(sub, sub_prj, PrjAsymm::PrjAsymmArraykey)
}

/// Record the decomposition of a subtype constraint between an arraykey type in
/// supertype position and some other type into another contraint between either
/// the int or string part of the arraykey type and the other type
pub fn prj_arraykey_super(super_: T, super_prj: T) -> T {
    prj_asymm_super(super_, super_prj, PrjAsymm::PrjAsymmArraykey)
}

shared_constant_reason!(missing_field, MissingField);

pub fn illegal_recursive_type(p: PosOrDecl, name: String) -> T {
    from_witness_decl(WitnessDecl::IllegalRecursiveType(p, name))
}

pub fn flow_elab(from: T, into: T) -> T {
    flow(from, into, FlowKind::FlowElab)
}

// -- Visitor ---------------------------------------------------------------

/// Reasons hold their lazy strings behind a shared pointer, so forcing them in
/// place is all `Visitor.map` with `on_lazy` overridden amounts to.
pub fn force_lazy_values(r: &T) -> T {
    fn force(r: &T_) {
        use T_::*;
        match r {
            TypeAccess(r, l) => {
                force(r);
                for (r, x) in l {
                    force(r);
                    x.force();
                }
            }
            Typeconst(r1, _, s, r2) => {
                force(r1);
                s.force();
                force(r2);
            }
            ArithRetFloat(_, r, _)
            | ArithRetNum(_, r, _)
            | LostInfo(_, r, _)
            | Format(_, _, r)
            | ExprDepType(r, _, _)
            | LambdaParam(_, r)
            | DynamicCoercion(r)
            | DynamicPartialEnforcement(_, _, r)
            | RigidTvarEscape(_, _, _, r)
            | OpaqueTypeFromModule(_, _, r)
            | SDTCall(_, r)
            | LikeCall(_, r)
            | Def(_, r) => force(r),
            Instantiate { type_, var, .. } => {
                force(type_);
                force(var);
            }
            NoReason | Invalid | MissingField | FromWitnessLocl(_) | FromWitnessDecl(_) => {}
            // The OCaml visitor does not go into the reason of an index.
            Idx(_, _) => {}
            Flow { from, into, .. } => {
                force(from);
                force(into);
            }
            T_::Axiom { prev, next, .. } => {
                force(prev);
                force(next);
            }
            LowerBound { bound, of_ } => {
                force(bound);
                force(of_);
            }
            Solved { solution, in_, .. } => {
                force(solution);
                force(in_);
            }
            PrjBoth {
                sub_prj,
                sub,
                super_,
                ..
            } => {
                force(sub_prj);
                force(sub);
                force(super_);
            }
            PrjOne { part, whole, .. } => {
                force(part);
                force(whole);
            }
        }
    }
    force(r);
    r.clone()
}

// -- Predicates ------------------------------------------------------------

pub mod predicates {
    use super::*;

    fn on_outermost<A>(t: &T_, f: impl Fn(&T_) -> A) -> A {
        fn aux<A>(t: &T_, solutions: &Solutions, f: &dyn Fn(&T_) -> A) -> A {
            use T_::*;
            match t {
                Solved {
                    solution,
                    of_,
                    in_: t,
                } => {
                    let mut solutions = solutions.clone();
                    solutions.insert(*of_, solution.clone());
                    aux(t, &solutions, f)
                }
                Flow { from: t, .. }
                | LowerBound { bound: t, .. }
                | T_::Axiom { next: t, .. }
                | PrjBoth { sub_prj: t, .. }
                | PrjOne { part: t, .. }
                | Def(_, t) => aux(t, solutions, f),
                _ => match tyvar_of_witness(t) {
                    Some(tvid) if solutions.contains_key(&tvid) => {
                        let t = solutions[&tvid].clone();
                        let mut solutions = solutions.clone();
                        solutions.remove(&tvid);
                        aux(&t, &solutions, f)
                    }
                    _ => f(t),
                },
            }
        }
        aux(t, &Solutions::new(), &f)
    }

    pub fn is_opaque_type_from_module(r: &T_) -> bool {
        on_outermost(r, |r| matches!(r, T_::OpaqueTypeFromModule(..)))
    }

    pub fn is_none(r: &T_) -> bool {
        on_outermost(r, |r| matches!(r, T_::NoReason))
    }

    pub fn is_instantiate(r: &T_) -> bool {
        on_outermost(r, |r| matches!(r, T_::Instantiate { .. }))
    }

    pub fn is_enforced_type(r: &T_) -> bool {
        on_outermost(r, |r| {
            matches!(r, T_::FromWitnessDecl(WitnessDecl::EnforcedType(_)))
        })
    }

    pub fn is_captured_like(r: &T_) -> bool {
        on_outermost(r, |r| {
            matches!(r, T_::FromWitnessLocl(WitnessLocl::CapturedLike(_)))
        })
    }

    /// Should be used only for diagnostics
    pub fn outer_constructor_string(r: &T_) -> String {
        on_outermost(r, to_constructor_string)
    }

    pub fn is_hint(r: &T_) -> bool {
        on_outermost(r, |r| matches!(r, T_::FromWitnessDecl(WitnessDecl::Hint(_))))
    }

    pub fn unpack_expr_dep_type_opt(r: &T_) -> Option<(T, PosOrDecl, ExprDepTypeReason)> {
        on_outermost(r, |r| match r {
            T_::ExprDepType(r, p, e) => Some((r.clone(), p.clone(), e.clone())),
            _ => None,
        })
    }

    pub fn unpack_unpack_param_opt(r: &T_) -> Option<(Pos, PosOrDecl, isize)> {
        on_outermost(r, |r| match r {
            T_::FromWitnessLocl(WitnessLocl::UnpackParam(p, p2, i)) => {
                Some((p.clone(), p2.clone(), *i))
            }
            _ => None,
        })
    }

    pub fn unpack_cstr_on_generics_opt(r: &T_) -> Option<(PosOrDecl, PosId)> {
        on_outermost(r, |r| match r {
            T_::FromWitnessDecl(WitnessDecl::CstrOnGenerics(p, sid)) => {
                Some((p.clone(), sid.clone()))
            }
            _ => None,
        })
    }

    pub fn unpack_shape_literal_opt(r: &T_) -> Option<Pos> {
        on_outermost(r, |r| match r {
            T_::FromWitnessLocl(WitnessLocl::ShapeLiteral(p)) => Some(p.clone()),
            _ => None,
        })
    }
}

// ~~ Aliases ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn localize(r: &DeclT) -> T {
    use oxidized::typing_reason::T_ as D;
    match r {
        D::NoReason => none(),
        D::Invalid => invalid(),
        _ => Rc::new(localize_(r)),
    }
}

fn localize_(r: &DeclT) -> T_ {
    use oxidized::typing_reason::T_ as D;
    match r {
        D::NoReason => T_::NoReason,
        D::Invalid => T_::Invalid,
        D::Typeconst(r1, p, q, r2) => T_::Typeconst(
            localize(r1),
            p.clone(),
            LazyString::from_val(q.0.clone()),
            localize(r2),
        ),
        D::Instantiate {
            type__,
            var_name,
            var,
        } => T_::Instantiate {
            type_: localize(type__),
            var_name: var_name.clone(),
            var: localize(var),
        },
        D::ExprDepType(r, s, t) => T_::ExprDepType(localize(r), s.clone(), t.clone()),
        D::FromWitnessDecl(witness) => T_::FromWitnessDecl(witness.clone()),
    }
}

// -- ureason ---------------------------------------------------------------

pub fn index_array() -> Ureason {
    Ureason::URindex("array".to_string())
}

pub fn index_tuple() -> Ureason {
    Ureason::URindex("tuple".to_string())
}

pub fn index_shape() -> Ureason {
    Ureason::URindex("shape".to_string())
}

pub fn index_class(s: &str) -> Ureason {
    Ureason::URindex(strip_ns(s).to_string())
}

pub fn set_element(s: &str) -> Ureason {
    Ureason::URelement(strip_ns(s).to_string())
}

pub fn string_of_ureason(r: &Ureason) -> String {
    use Ureason::*;
    match r {
        URnone => "Typing error".to_string(),
        URreturn => "Invalid return type".to_string(),
        URhint => "Wrong type hint".to_string(),
        URassign => "Invalid assignment".to_string(),
        URassignInout => "Invalid assignment to an `inout` parameter".to_string(),
        URforeach => "Invalid `foreach`".to_string(),
        URthrow => "Invalid exception".to_string(),
        URvector => "Some elements in this collection are incompatible".to_string(),
        URkey(s) => format!("The keys of this `{}` are incompatible", strip_ns(s)),
        URvalue(s) => format!("The values of this `{}` are incompatible", strip_ns(s)),
        URawait => "`await` can only operate on an `Awaitable`".to_string(),
        URdelay => "`delay` can only operate on an `Awaitable`".to_string(),
        URyield => "Invalid `yield`".to_string(),
        URxhp(cls, attr) => format!(
            "Invalid xhp value for attribute {} in {}",
            md_codify(attr),
            md_codify(strip_ns(cls))
        ),
        URxhpSpread => "The attribute spread operator cannot be called on non-XHP".to_string(),
        URindex(s) => format!("Invalid index type for this {}", strip_ns(s)),
        URelement(s) => format!("Invalid element type for this {}", strip_ns(s)),
        URparam => "Invalid argument".to_string(),
        URparamInout => "Invalid argument to an `inout` parameter".to_string(),
        URarrayValue => "Incompatible field values".to_string(),
        URpairValue => "Incompatible pair values".to_string(),
        URtupleAccess => "Tuple elements can only be accessed with an integer literal".to_string(),
        URtupleOOB => "Tuple accessed with an index out of bounds".to_string(),
        URpairAccess => "Pair elements can only be accessed with an integer literal".to_string(),
        URnewtypeCstr => "Invalid constraint on `newtype`".to_string(),
        URclassReq => "Unable to satisfy trait/interface requirement".to_string(),
        URenum => "Constant does not match the type of the enum it is in".to_string(),
        URenumInclude => "Inclusion of enum of incompatible type".to_string(),
        URenumCstr => "Invalid constraint on enum".to_string(),
        URenumUnderlying => "Invalid underlying type for enum".to_string(),
        URenumIncompatibleCstr => {
            "Underlying type for enum is incompatible with constraint".to_string()
        }
        URtypeconstCstr => "Unable to satisfy constraint on this type constant".to_string(),
        URsubsumeTconstCstr => {
            "The constraint on this type constant is inconsistent with its parent".to_string()
        }
        URsubsumeTconstAssign => {
            "The assigned type of this type constant is inconsistent with its parent".to_string()
        }
        URclone => "Clone cannot be called on non-object".to_string(),
        URusing => "Using cannot be used on non-disposable expression".to_string(),
        URstrConcat => {
            "String concatenation can only be performed on string and int arguments".to_string()
        }
        URstrInterp => "Only string and int values can be used in string interpolation".to_string(),
        URdynamicProp => "Dynamic access of property".to_string(),
        URlabel => "This label is not a valid reference to a member of the given enum class"
            .to_string(),
        URcondition => {
            "Only bool values can be used as a condition. Use a type-specific test instead."
                .to_string()
        }
    }
}

/// Get the topmost function parameter projection, in the case that the reason
/// contains a function subtyping
pub fn get_top_fun_param_prj_idx(r: &T_) -> Option<isize> {
    use T_::*;
    match r {
        PrjBoth {
            prj: PrjSymm::PrjSymmFnParam(i, _),
            sub,
            ..
        } => match get_top_fun_param_prj_idx(sub) {
            None => Some(*i),
            Some(i) => Some(i),
        },
        PrjBoth { sub, .. } => get_top_fun_param_prj_idx(sub),
        LowerBound { bound, .. } => get_top_fun_param_prj_idx(bound),
        T_::Axiom { prev, .. } => get_top_fun_param_prj_idx(prev),
        Solved { in_, .. } => get_top_fun_param_prj_idx(in_),
        _ => None,
    }
}

// ~~ Extended reasons rendering ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
//
// `Derivation` (the explanation of a subtyping error as the path the types
// took through the program) is in a submodule. Mind that `Typing_error_utils`
// builds the explanation of every
// subtyping error, whatever the options are (`explain ~complexity:1` when
// `--extended-reasons` is not given), and forces it when it makes the
// diagnostic; only the "extended" error format prints it.

/// The explanation of why `sub` is not a subtype of `super_`.
pub fn explain(
    sub: &T_,
    super_: &T_,
    complexity: isize,
) -> oxidized::explanation::Explanation<PosOrDecl> {
    explain::explain(sub, super_, complexity)
}

pub fn debug_reason(sub: &T_, super_: &T_) -> oxidized::explanation::Explanation<PosOrDecl> {
    explain::debug_reason(sub, super_)
}

pub fn debug_derivation(
    sub: &T_,
    super_: &T_,
) -> oxidized::explanation::Explanation<PosOrDecl> {
    explain::debug_derivation(sub, super_)
}

mod explain;

#[cfg(test)]
mod tests;
