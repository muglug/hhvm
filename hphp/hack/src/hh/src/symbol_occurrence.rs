// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/symbol_occurrence.ml`. See `hh/PORTING.md`.
//!
//! The types were ported by the client-connection assignment (D1):
//! `Server_command_types` carries them over the socket, so they are `serde`.
//! The functions are F1's. The derived `compare` of `'a t` is [`compare`]
//! (the derived `compare` of the other types is their `Ord`, which orders
//! constructors and fields as `ppx_deriving` does); the derived `show` and
//! `pp` are not ported (only Glean's `write_symbol_info` uses them).
//!
//! `'a Pos.pos` is the type parameter `P`: `oxidized::pos::Pos`
//! (`Relative_path.t Pos.pos`) or `crate::pos::Absolute` (`string Pos.pos`).

use std::cmp::Ordering;

use naming_special_names_rust as sn;
use oxidized::aast_defs::Tprim;
use serde::Deserialize;
use serde::Serialize;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct OverrideInfo {
    pub class_name: String,
    pub method_name: String,
    pub is_static: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum ClassIdType {
    ClassId,
    ExpressionTreeVisitor,
    Other,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum ReceiverClass {
    ClassName(String),
    /// invoked dynamically
    UnknownClass,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum KeywordWithHoverDocs {
    Class,
    Interface,
    Trait,
    Enum,
    EnumClass,
    Type,
    Newtype,
    FinalOnClass,
    FinalOnMethod,
    AbstractOnClass,
    AbstractOnMethod,
    ExtendsOnClass,
    ExtendsOnInterface,
    ReadonlyOnMethod,
    ReadonlyOnParameter,
    ReadonlyOnReturnType,
    ReadonlyOnExpression,
    XhpAttribute,
    XhpChildren,
    ConstGlobal,
    ConstOnClass,
    ConstType,
    StaticOnMethod,
    StaticOnProperty,
    Use,
    FunctionGlobal,
    FunctionOnMethod,
    Async,
    AsyncBlock,
    Await,
    Concurrent,
    Public,
    Protected,
    Private,
    Internal,
    ModuleInModuleDeclaration,
    ModuleInModuleMembershipDeclaration,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum BuiltInTypeHint {
    BIprimitive(Tprim),
    BIstring,
    BImixed,
    BIdynamic,
    BInothing,
    BInonnull,
    BIshape,
    BIthis,
    BIoption,
    BIclassPtr,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum Receiver {
    FunctionReceiver(String),
    MethodReceiver {
        cls_name: String,
        meth_name: String,
        is_static: bool,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum Kind {
    Class(ClassIdType),
    BuiltInType(BuiltInTypeHint),
    Function,
    Method(ReceiverClass, String),
    LocalVar,
    TypeVar,
    Property(ReceiverClass, String),
    /// XhpLiteralAttr is only used for attributes in XHP literals.
    /// i.e.
    ///     <foo:bar my-attribute={} />
    /// For all other cases, Property is used.
    /// i.e.
    ///     $x->:my-attribute
    ///     or attributes in class definitions
    XhpLiteralAttr(String, String),
    ClassConst(ReceiverClass, String),
    Typeconst(String, String),
    GConst,
    Attribute(Option<OverrideInfo>),
    EnumClassLabel(String, String),
    Keyword(KeywordWithHoverDocs),
    PureFunctionContext,
    BestEffortArgument(Receiver, isize),
    HhFixme,
    HhIgnore,
    Module,
}

/// `'a t`
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct T<P> {
    pub name: String,
    pub type_: Kind,
    /// If this is a declaration, the span of the full declaration, or None otherwise
    pub is_declaration: Option<P>,
    /// Span of the symbol name itself
    pub pos: P,
    /// Whether this symbol occurrence affects the production build.  Currently
    /// symbols inside __RequirePackage("intern") scopes, nameof expressions,
    /// attributes, and class pointers are marked as not affecting the prod build.
    pub affects_prod_build: bool,
}

/// The derived `compare` of `'a t`: `compare poly_a` compares the files of
/// the positions with `poly_a` (`Pos.compare_pos`).
pub fn compare<P: crate::pos::APos>(
    poly_a: impl Fn(&P::File, &P::File) -> Ordering,
    x: &T<P>,
    y: &T<P>,
) -> Ordering {
    let cmp_pos = |a: &P, b: &P| crate::pos::compare_pos(&poly_a, a, b);
    x.name
        .cmp(&y.name)
        .then_with(|| x.type_.cmp(&y.type_))
        .then_with(|| match (&x.is_declaration, &y.is_declaration) {
            (None, None) => Ordering::Equal,
            (None, Some(_)) => Ordering::Less,
            (Some(_), None) => Ordering::Greater,
            (Some(a), Some(b)) => cmp_pos(a, b),
        })
        .then_with(|| cmp_pos(&x.pos, &y.pos))
        .then_with(|| x.affects_prod_build.cmp(&y.affects_prod_build))
}

pub fn to_absolute(x: &T<crate::pos::Pos>) -> T<crate::pos::Absolute> {
    T {
        name: x.name.clone(),
        type_: x.type_.clone(),
        is_declaration: x.is_declaration.as_ref().map(crate::pos::to_absolute),
        pos: crate::pos::to_absolute(&x.pos),
        affects_prod_build: x.affects_prod_build,
    }
}

pub fn kind_to_string(k: &Kind) -> &'static str {
    match k {
        Kind::Class(_) => "class",
        Kind::BuiltInType(_) => "built_in_type",
        Kind::Method(..) => "method",
        Kind::Function => "function",
        Kind::LocalVar => "local",
        Kind::Property(..) => "property",
        Kind::XhpLiteralAttr(..) => "xhp_literal_attribute",
        Kind::ClassConst(..) => "member_const",
        Kind::Typeconst(..) => "typeconst",
        Kind::GConst => "global_const",
        Kind::TypeVar => "generic_type_var",
        Kind::Attribute(_) => "attribute",
        Kind::EnumClassLabel(..) => "enum_class_label",
        Kind::Keyword(_) => "keyword",
        Kind::PureFunctionContext => "context_braces",
        Kind::BestEffortArgument(..) => "argument",
        Kind::HhFixme => "hh_fixme",
        Kind::HhIgnore => "hh_ignore",
        Kind::Module => "module",
    }
}

pub fn is_top_level_definition<P>(x: &T<P>) -> bool {
    x.is_declaration.is_some()
        && match &x.type_ {
            Kind::Class(_) | Kind::Function | Kind::GConst | Kind::Module => true,
            Kind::BuiltInType(_)
            | Kind::Method(..)
            | Kind::LocalVar
            | Kind::Property(..)
            | Kind::XhpLiteralAttr(..)
            | Kind::ClassConst(..)
            | Kind::Typeconst(..)
            | Kind::TypeVar
            | Kind::Attribute(_)
            | Kind::EnumClassLabel(..)
            | Kind::Keyword(_)
            | Kind::PureFunctionContext
            | Kind::BestEffortArgument(..)
            | Kind::HhFixme
            | Kind::HhIgnore => false,
        }
}

pub fn enclosing_class<P>(occurrence: &T<P>) -> Option<String> {
    match &occurrence.type_ {
        Kind::Method(ReceiverClass::ClassName(c), _)
        | Kind::Property(ReceiverClass::ClassName(c), _)
        | Kind::XhpLiteralAttr(c, _)
        | Kind::ClassConst(ReceiverClass::ClassName(c), _)
        | Kind::Typeconst(c, _)
        | Kind::EnumClassLabel(c, _) => Some(c.clone()),
        _ => None,
    }
}

pub fn get_class_name<P>(occurrence: &T<P>) -> Option<String> {
    match enclosing_class(occurrence) {
        Some(res) => Some(res),
        None => match &occurrence.type_ {
            Kind::Class(_) | Kind::Attribute(_) => Some(occurrence.name.clone()),
            _ => None,
        },
    }
}

pub fn is_constructor<P>(occurrence: &T<P>) -> bool {
    match &occurrence.type_ {
        Kind::Method(_, name) if name == sn::members::__CONSTRUCT => true,
        _ => false,
    }
}

pub fn is_class<P>(occurrence: &T<P>) -> bool {
    matches!(occurrence.type_, Kind::Class(_))
}

pub fn is_xhp_literal_attr<P>(occurrence: &T<P>) -> bool {
    matches!(occurrence.type_, Kind::XhpLiteralAttr(..))
}

pub fn built_in_type_hover(bt: &BuiltInTypeHint) -> String {
    match bt {
        BuiltInTypeHint::BIprimitive(prim) => match prim {
            Tprim::Tnull => "The value `null`. The opposite of `nonnull`.".to_string(),
            Tprim::Tvoid => "A `void` return type indicates a function that never returns a value. `void` functions usually have side effects.".to_string(),
            Tprim::Tint => "A 64-bit integer.".to_string(),
            Tprim::Tbool => "A boolean value, `true` or `false`.".to_string(),
            Tprim::Tfloat => "A 64-bit floating-point number.".to_string(),
            Tprim::Tresource => {
                "An external resource, such as a file handle or database connection.".to_string()
            }
            Tprim::Tnum => "An `int` or a `float`.".to_string(),
            Tprim::Tarraykey => {
                "An `int` or a `string`. `arraykey` is a common key type for `dict`s.".to_string()
            }
            Tprim::Tnoreturn => {
                "A `noreturn` function always errors or loops forever.".to_string()
            }
        },
        BuiltInTypeHint::BIstring => "A sequence of characters.".to_string(),
        BuiltInTypeHint::BImixed => {
            "Any value at all. It's usually better to use a more specific type, or a generic."
                .to_string()
        }
        BuiltInTypeHint::BIdynamic => {
            "Any value at all. Unlike `mixed`, the type checker allows any operation on a `dynamic` value, even if e.g. a method doesn't actually exist.\n\n".to_string()
                + "All operations on a `dynamic` value return another `dynamic` value. Prefer more specific types so the type checker can help you.\n\n"
                + "To convert a `generic` value to something specific, use `$foo as SomeSpecificType`. This will check the type at runtime and the "
                + "type checker will verify types after this point."
        }
        BuiltInTypeHint::BInothing => {
            "The `nothing` type has no values, it's the empty type.\n\nA function returning `nothing` either loops forever or throws an exception. A `vec<nothing>` is always empty.".to_string()
        }
        BuiltInTypeHint::BInonnull => "Any value except `null`.".to_string(),
        BuiltInTypeHint::BIshape => {
            "A shape is a key-value data structure where the keys are known.".to_string()
                + " Shapes are value types, just like `dict` and `vec`.\n\n"
                + " A closed shape, such as `shape('x' => int)`, has a fixed number of keys. "
                + " An open shape, such as `shape('x' => int, ...)`, may have additional keys."
        }
        BuiltInTypeHint::BIthis => {
            "`this` represents the current class.\n\n".to_string()
                + "`this` refers to the type of the current instance at runtime. In a child class, `this` refers to the child class, even if the method is defined in the parent."
        }
        BuiltInTypeHint::BIoption => "The type `?Foo` allows either `Foo` or `null`.".to_string(),
        BuiltInTypeHint::BIclassPtr => {
            "For any class C, C::class creates a class<C>. This value is used for\nexpressions like `new $c()` and `$c::foo()`.".to_string()
        }
    }
}
