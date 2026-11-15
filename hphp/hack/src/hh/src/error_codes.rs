// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `diagnostics/error_codes.ml`. See `hh/PORTING.md`.
//!
//! The enums (`Error_codes.Parsing.t`, ...) are those of
//! `oxidized::error_codes`, re-exported here; each OCaml submodule is a Rust
//! module of the same name in snake case (`Error_codes.NastCheck` is
//! [`nast_check`]), where `T` is its `t` and the functions are those that
//! `[@@deriving enum, show]` (and `ord`, for `Warning`) and the module itself
//! define.
//!
//! The codes of `oxidized` are the `[@value]`s of the OCaml, constructor for
//! constructor and in the same order; two constructors are spelled
//! differently (`Naming.StartWith_T` is `StartWithT`,
//! `NastCheck.Soft_internal_without_internal` is
//! `SoftInternalWithoutInternal`), and `show` gives the OCaml spelling.
//!
//! There is no `Init` module: the OCaml has none (8xxx "had been used for
//! forward/back-compat; no longer").

pub use oxidized::error_codes::*;

/// `Error_codes.Parsing`
pub mod parsing {
    /// `Error_codes.Parsing.t` (its constructors are `oxidized::error_codes::Parsing`'s)
    pub use oxidized::error_codes::Parsing as T;

    /// `to_enum` (`[@@deriving enum]`): the code of an error.
    pub fn to_enum(t: T) -> isize {
        // The discriminants of `oxidized::error_codes::Parsing` are the
        // `[@value]`s of the OCaml.
        t as isize
    }

    /// `of_enum` (`[@@deriving enum]`): the error that has this code.
    pub fn of_enum(i: isize) -> Option<T> {
        Some(match i {
            1001 => T::FixmeFormat,
            1002 => T::ParsingError,
            1007 => T::XhpParsingError,
            1008 => T::HhIgnoreComment,
            1009 => T::PackageConfigError,
            _ => return None,
        })
    }

    /// `min` (`[@@deriving enum]`): the smallest code.
    pub const MIN: isize = 1001;

    /// `max` (`[@@deriving enum]`): the largest code.
    pub const MAX: isize = 1009;

    /// `show` (`[@@deriving show { with_path = false }]`): the name of the
    /// OCaml constructor.
    pub fn show(t: T) -> String {
        match t {
            T::FixmeFormat => "FixmeFormat",
            T::ParsingError => "ParsingError",
            T::XhpParsingError => "XhpParsingError",
            T::HhIgnoreComment => "HhIgnoreComment",
            T::PackageConfigError => "PackageConfigError",
        }
        .to_string()
    }

    /// `pp` (`[@@deriving show { with_path = false }]`)
    pub fn pp(fmt: &mut dyn std::fmt::Write, t: T) -> std::fmt::Result {
        fmt.write_str(&show(t))
    }

    pub fn err_code(t: T) -> isize {
        to_enum(t)
    }
}

/// `Error_codes.Naming`
pub mod naming {
    /// `Error_codes.Naming.t` (its constructors are `oxidized::error_codes::Naming`'s)
    pub use oxidized::error_codes::Naming as T;

    /// `to_enum` (`[@@deriving enum]`): the code of an error.
    pub fn to_enum(t: T) -> isize {
        // The discriminants of `oxidized::error_codes::Naming` are the
        // `[@value]`s of the OCaml.
        t as isize
    }

    /// `of_enum` (`[@@deriving enum]`): the error that has this code.
    pub fn of_enum(i: isize) -> Option<T> {
        Some(match i {
            2001 => T::AddATypehint,
            2004 => T::PrimitiveInvalidAlias,
            2006 => T::DidYouMeanNaming,
            2008 => T::DisallowedXhpType,
            2012 => T::ErrorNameAlreadyBound,
            2013 => T::ExpectedCollection,
            2014 => T::ExpectedVariable,
            2015 => T::FdNameAlreadyBound,
            2021 => T::IllegalClass,
            2022 => T::IllegalClassMeth,
            2023 => T::IllegalConstant,
            2026 => T::IllegalMethCaller,
            2029 => T::InvalidReqExtends,
            2030 => T::InvalidReqImplements,
            2033 => T::MethodNameAlreadyBound,
            2034 => T::MissingArrow,
            2035 => T::MissingTypehint,
            2036 => T::NameAlreadyBound,
            2037 => T::NamingTooFewArguments,
            2038 => T::NamingTooManyArguments,
            2039 => T::PrimitiveToplevel,
            2041 => T::ShadowedTypeParam,
            2042 => T::StartWithT,
            2043 => T::ThisMustBeReturn,
            2044 => T::ThisNoArgument,
            2045 => T::ThisHintOutsideClass,
            2046 => T::ThisReserved,
            2047 => T::HigherKindedTypesUnsupportedFeature,
            2049 => T::UnboundName,
            2050 => T::Undefined,
            2051 => T::UnexpectedArrow,
            2052 => T::UnexpectedTypedef,
            2053 => T::UsingInternalClass,
            2055 => T::ObjectCast,
            2058 => T::IllegalTrait,
            2060 => T::DynamicNewInStrictMode,
            2061 => T::InvalidTypeAccessRoot,
            2062 => T::DuplicateUserAttribute,
            2063 => T::ReturnOnlyTypehint,
            2064 => T::UnexpectedTypeArguments,
            2065 => T::TooManyTypeArguments,
            2066 => T::ClassnameParam,
            2068 => T::NameIsReserved,
            2069 => T::DollardollarUnused,
            2070 => T::IllegalMemberVariableClass,
            2071 => T::TooFewTypeArguments,
            2077 => T::ThisAsLexicalVariable,
            2078 => T::DynamicClassNameInStrictMode,
            2079 => T::XhpOptionalRequiredAttr,
            2084 => T::WildcardHintDisallowed,
            2086 => T::MethodNeedsVisibility,
            2094 => T::NonstaticPropertyWithLSB,
            2105 => T::InvalidFunPointer,
            2106 => T::IllegalUseOfDynamicallyCallable,
            2111 => T::ClassMethNonFinalSelf,
            2112 => T::ParentInFunctionPointer,
            2113 => T::SelfInNonFinalFunctionPointer,
            2114 => T::ClassMethNonFinalCLASS,
            2115 => T::WildcardTypeParamDisallowed,
            2117 => T::InvalidWildcardContext,
            2118 => T::ExplicitConsistentConstructor,
            2119 => T::InvalidReqClass,
            2120 => T::ModuleDeclarationOutsideAllowedFiles,
            2121 => T::DynamicMethodAccess,
            2123 => T::InvalidBuiltinType,
            2124 => T::InvalidMemoizeLabel,
            2125 => T::DynamicHintDisallowed,
            2126 => T::IllegalTypedLocal,
            2127 => T::InternalModuleLevelTrait,
            2128 => T::ToplevelStatement,
            2129 => T::InvalidTypeAccessInWhere,
            2130 => T::AttributeOutsideAllowedFiles,
            2131 => T::HhiAttributeRestriction,
            2132 => T::TypedOpenShapeDisallowed,
            2133 => T::NamedVariadicTypeDisallowed,
            2134 => T::VariadicNamedParameterDisallowed,
            2135 => T::ImplicitPackageFileDirectlyUnderPath,
            2136 => T::ImplicitPackageInvalidMemberDir,
            2137 => T::TraitSelfShapeKey,
            _ => return None,
        })
    }

    /// `min` (`[@@deriving enum]`): the smallest code.
    pub const MIN: isize = 2001;

    /// `max` (`[@@deriving enum]`): the largest code.
    pub const MAX: isize = 2137;

    /// `show` (`[@@deriving show { with_path = false }]`): the name of the
    /// OCaml constructor.
    pub fn show(t: T) -> String {
        match t {
            T::AddATypehint => "AddATypehint",
            T::PrimitiveInvalidAlias => "PrimitiveInvalidAlias",
            T::DidYouMeanNaming => "DidYouMeanNaming",
            T::DisallowedXhpType => "DisallowedXhpType",
            T::ErrorNameAlreadyBound => "ErrorNameAlreadyBound",
            T::ExpectedCollection => "ExpectedCollection",
            T::ExpectedVariable => "ExpectedVariable",
            T::FdNameAlreadyBound => "FdNameAlreadyBound",
            T::IllegalClass => "IllegalClass",
            T::IllegalClassMeth => "IllegalClassMeth",
            T::IllegalConstant => "IllegalConstant",
            T::IllegalMethCaller => "IllegalMethCaller",
            T::InvalidReqExtends => "InvalidReqExtends",
            T::InvalidReqImplements => "InvalidReqImplements",
            T::MethodNameAlreadyBound => "MethodNameAlreadyBound",
            T::MissingArrow => "MissingArrow",
            T::MissingTypehint => "MissingTypehint",
            T::NameAlreadyBound => "NameAlreadyBound",
            T::NamingTooFewArguments => "NamingTooFewArguments",
            T::NamingTooManyArguments => "NamingTooManyArguments",
            T::PrimitiveToplevel => "PrimitiveToplevel",
            T::ShadowedTypeParam => "ShadowedTypeParam",
            T::StartWithT => "StartWith_T",
            T::ThisMustBeReturn => "ThisMustBeReturn",
            T::ThisNoArgument => "ThisNoArgument",
            T::ThisHintOutsideClass => "ThisHintOutsideClass",
            T::ThisReserved => "ThisReserved",
            T::HigherKindedTypesUnsupportedFeature => "HigherKindedTypesUnsupportedFeature",
            T::UnboundName => "UnboundName",
            T::Undefined => "Undefined",
            T::UnexpectedArrow => "UnexpectedArrow",
            T::UnexpectedTypedef => "UnexpectedTypedef",
            T::UsingInternalClass => "UsingInternalClass",
            T::ObjectCast => "ObjectCast",
            T::IllegalTrait => "IllegalTrait",
            T::DynamicNewInStrictMode => "DynamicNewInStrictMode",
            T::InvalidTypeAccessRoot => "InvalidTypeAccessRoot",
            T::DuplicateUserAttribute => "DuplicateUserAttribute",
            T::ReturnOnlyTypehint => "ReturnOnlyTypehint",
            T::UnexpectedTypeArguments => "UnexpectedTypeArguments",
            T::TooManyTypeArguments => "TooManyTypeArguments",
            T::ClassnameParam => "ClassnameParam",
            T::NameIsReserved => "NameIsReserved",
            T::DollardollarUnused => "DollardollarUnused",
            T::IllegalMemberVariableClass => "IllegalMemberVariableClass",
            T::TooFewTypeArguments => "TooFewTypeArguments",
            T::ThisAsLexicalVariable => "ThisAsLexicalVariable",
            T::DynamicClassNameInStrictMode => "DynamicClassNameInStrictMode",
            T::XhpOptionalRequiredAttr => "XhpOptionalRequiredAttr",
            T::WildcardHintDisallowed => "WildcardHintDisallowed",
            T::MethodNeedsVisibility => "MethodNeedsVisibility",
            T::NonstaticPropertyWithLSB => "NonstaticPropertyWithLSB",
            T::InvalidFunPointer => "InvalidFunPointer",
            T::IllegalUseOfDynamicallyCallable => "IllegalUseOfDynamicallyCallable",
            T::ClassMethNonFinalSelf => "ClassMethNonFinalSelf",
            T::ParentInFunctionPointer => "ParentInFunctionPointer",
            T::SelfInNonFinalFunctionPointer => "SelfInNonFinalFunctionPointer",
            T::ClassMethNonFinalCLASS => "ClassMethNonFinalCLASS",
            T::WildcardTypeParamDisallowed => "WildcardTypeParamDisallowed",
            T::InvalidWildcardContext => "InvalidWildcardContext",
            T::ExplicitConsistentConstructor => "ExplicitConsistentConstructor",
            T::InvalidReqClass => "InvalidReqClass",
            T::ModuleDeclarationOutsideAllowedFiles => "ModuleDeclarationOutsideAllowedFiles",
            T::DynamicMethodAccess => "DynamicMethodAccess",
            T::InvalidBuiltinType => "InvalidBuiltinType",
            T::InvalidMemoizeLabel => "InvalidMemoizeLabel",
            T::DynamicHintDisallowed => "DynamicHintDisallowed",
            T::IllegalTypedLocal => "IllegalTypedLocal",
            T::InternalModuleLevelTrait => "InternalModuleLevelTrait",
            T::ToplevelStatement => "ToplevelStatement",
            T::InvalidTypeAccessInWhere => "InvalidTypeAccessInWhere",
            T::AttributeOutsideAllowedFiles => "AttributeOutsideAllowedFiles",
            T::HhiAttributeRestriction => "HhiAttributeRestriction",
            T::TypedOpenShapeDisallowed => "TypedOpenShapeDisallowed",
            T::NamedVariadicTypeDisallowed => "NamedVariadicTypeDisallowed",
            T::VariadicNamedParameterDisallowed => "VariadicNamedParameterDisallowed",
            T::ImplicitPackageFileDirectlyUnderPath => "ImplicitPackageFileDirectlyUnderPath",
            T::ImplicitPackageInvalidMemberDir => "ImplicitPackageInvalidMemberDir",
            T::TraitSelfShapeKey => "TraitSelfShapeKey",
        }
        .to_string()
    }

    /// `pp` (`[@@deriving show { with_path = false }]`)
    pub fn pp(fmt: &mut dyn std::fmt::Write, t: T) -> std::fmt::Result {
        fmt.write_str(&show(t))
    }

    pub fn err_code(t: T) -> isize {
        to_enum(t)
    }
}

/// `Error_codes.NastCheck`
pub mod nast_check {
    /// `Error_codes.NastCheck.t` (its constructors are `oxidized::error_codes::NastCheck`'s)
    pub use oxidized::error_codes::NastCheck as T;

    /// `to_enum` (`[@@deriving enum]`): the code of an error.
    pub fn to_enum(t: T) -> isize {
        // The discriminants of `oxidized::error_codes::NastCheck` are the
        // `[@value]`s of the OCaml.
        t as isize
    }

    /// `of_enum` (`[@@deriving enum]`): the error that has this code.
    pub fn of_enum(i: isize) -> Option<T> {
        Some(match i {
            3001 => T::AbstractBody,
            3002 => T::AbstractWithBody,
            3003 => T::AwaitInSyncFunction,
            3004 => T::CallBeforeInit,
            3005 => T::CaseFallthrough,
            3006 => T::ContinueInSwitch,
            3008 => T::DefaultFallthrough,
            3009 => T::InterfaceWithMemberVariable,
            3010 => T::InterfaceWithStaticMemberVariable,
            3011 => T::Magic,
            3012 => T::NoConstructParent,
            3013 => T::NonInterface,
            3015 => T::NotInitialized,
            3017 => T::RequiresNonClass,
            3018 => T::ReturnInFinally,
            3020 => T::ToStringReturnsString,
            3021 => T::ToStringVisibility,
            3022 => T::ToplevelBreak,
            3023 => T::ToplevelContinue,
            3024 => T::UsesNonTrait,
            3025 => T::IllegalFunctionName,
            3026 => T::NotAbstractWithoutTypeconst,
            3027 => T::TypeconstDependsOnExternalTparam,
            3030 => T::ConstructorRequired,
            3031 => T::InterfaceWithPartialTypeconst,
            3032 => T::MultipleXhpCategory,
            3043 => T::InoutParamsSpecial,
            3045 => T::InoutParamsMemoize,
            3047 => T::ReadingFromAppend,
            3056 => T::IllegalDestructor,
            3072 => T::RequiresFinalClass,
            3073 => T::InterfaceUsesTrait,
            3074 => T::NonstaticMethodInAbstractFinalClass,
            3083 => T::RepeatedRecordFieldName,
            3084 => T::PhpLambdaDisallowed,
            3085 => T::EntryPointArguments,
            3086 => T::VariadicMemoize,
            3087 => T::AbstractMethodMemoize,
            3088 => T::InstancePropertyInAbstractFinalClass,
            3089 => T::DynamicallyCallableReified,
            3090 => T::IllegalContext,
            3092 => T::ListRvalue,
            3093 => T::PartiallyAbstractTypeconstDefinition,
            3094 => T::EntryPointGenerics,
            3095 => T::InternalProtectedOrPrivate,
            3096 => T::InoutInTransformedPsuedofunction,
            3097 => T::PrivateAndFinal,
            3099 => T::InternalMemberInsidePublicTrait,
            3100 => T::AttributeConflictingMemoize,
            3101 => T::RefinementInTypeStruct,
            3102 => T::SoftInternalWithoutInternal,
            3104 => T::CloneReturnType,
            3106 => T::NamedInTransformedPseudofunction,
            3107 => T::RequirePackageStrictInclusion,
            3108 => T::ClassSealedWithTrait,
            3109 => T::PackageExpressionStrictInclusion,
            3110 => T::ObservationNotAllowedForPackage,
            3111 => T::PackageOverrideTargetNotIncluded,
            3112 => T::RedundantPackageOverride,
            3114 => T::OverrideNotAllowedForPackage,
            3115 => T::PlaceholderRead,
            3116 => T::PlaceholderInoutWrite,
            _ => return None,
        })
    }

    /// `min` (`[@@deriving enum]`): the smallest code.
    pub const MIN: isize = 3001;

    /// `max` (`[@@deriving enum]`): the largest code.
    pub const MAX: isize = 3116;

    /// `show` (`[@@deriving show { with_path = false }]`): the name of the
    /// OCaml constructor.
    pub fn show(t: T) -> String {
        match t {
            T::AbstractBody => "AbstractBody",
            T::AbstractWithBody => "AbstractWithBody",
            T::AwaitInSyncFunction => "AwaitInSyncFunction",
            T::CallBeforeInit => "CallBeforeInit",
            T::CaseFallthrough => "CaseFallthrough",
            T::ContinueInSwitch => "ContinueInSwitch",
            T::DefaultFallthrough => "DefaultFallthrough",
            T::InterfaceWithMemberVariable => "InterfaceWithMemberVariable",
            T::InterfaceWithStaticMemberVariable => "InterfaceWithStaticMemberVariable",
            T::Magic => "Magic",
            T::NoConstructParent => "NoConstructParent",
            T::NonInterface => "NonInterface",
            T::NotInitialized => "NotInitialized",
            T::RequiresNonClass => "RequiresNonClass",
            T::ReturnInFinally => "ReturnInFinally",
            T::ToStringReturnsString => "ToStringReturnsString",
            T::ToStringVisibility => "ToStringVisibility",
            T::ToplevelBreak => "ToplevelBreak",
            T::ToplevelContinue => "ToplevelContinue",
            T::UsesNonTrait => "UsesNonTrait",
            T::IllegalFunctionName => "IllegalFunctionName",
            T::NotAbstractWithoutTypeconst => "NotAbstractWithoutTypeconst",
            T::TypeconstDependsOnExternalTparam => "TypeconstDependsOnExternalTparam",
            T::ConstructorRequired => "ConstructorRequired",
            T::InterfaceWithPartialTypeconst => "InterfaceWithPartialTypeconst",
            T::MultipleXhpCategory => "MultipleXhpCategory",
            T::InoutParamsSpecial => "InoutParamsSpecial",
            T::InoutParamsMemoize => "InoutParamsMemoize",
            T::ReadingFromAppend => "ReadingFromAppend",
            T::IllegalDestructor => "IllegalDestructor",
            T::RequiresFinalClass => "RequiresFinalClass",
            T::InterfaceUsesTrait => "InterfaceUsesTrait",
            T::NonstaticMethodInAbstractFinalClass => "NonstaticMethodInAbstractFinalClass",
            T::RepeatedRecordFieldName => "RepeatedRecordFieldName",
            T::PhpLambdaDisallowed => "PhpLambdaDisallowed",
            T::EntryPointArguments => "EntryPointArguments",
            T::VariadicMemoize => "VariadicMemoize",
            T::AbstractMethodMemoize => "AbstractMethodMemoize",
            T::InstancePropertyInAbstractFinalClass => "InstancePropertyInAbstractFinalClass",
            T::DynamicallyCallableReified => "DynamicallyCallableReified",
            T::IllegalContext => "IllegalContext",
            T::ListRvalue => "ListRvalue",
            T::PartiallyAbstractTypeconstDefinition => "PartiallyAbstractTypeconstDefinition",
            T::EntryPointGenerics => "EntryPointGenerics",
            T::InternalProtectedOrPrivate => "InternalProtectedOrPrivate",
            T::InoutInTransformedPsuedofunction => "InoutInTransformedPsuedofunction",
            T::PrivateAndFinal => "PrivateAndFinal",
            T::InternalMemberInsidePublicTrait => "InternalMemberInsidePublicTrait",
            T::AttributeConflictingMemoize => "AttributeConflictingMemoize",
            T::RefinementInTypeStruct => "RefinementInTypeStruct",
            T::SoftInternalWithoutInternal => "Soft_internal_without_internal",
            T::CloneReturnType => "CloneReturnType",
            T::NamedInTransformedPseudofunction => "NamedInTransformedPseudofunction",
            T::RequirePackageStrictInclusion => "RequirePackageStrictInclusion",
            T::ClassSealedWithTrait => "ClassSealedWithTrait",
            T::PackageExpressionStrictInclusion => "PackageExpressionStrictInclusion",
            T::ObservationNotAllowedForPackage => "ObservationNotAllowedForPackage",
            T::PackageOverrideTargetNotIncluded => "PackageOverrideTargetNotIncluded",
            T::RedundantPackageOverride => "RedundantPackageOverride",
            T::OverrideNotAllowedForPackage => "OverrideNotAllowedForPackage",
            T::PlaceholderRead => "PlaceholderRead",
            T::PlaceholderInoutWrite => "PlaceholderInoutWrite",
        }
        .to_string()
    }

    /// `pp` (`[@@deriving show { with_path = false }]`)
    pub fn pp(fmt: &mut dyn std::fmt::Write, t: T) -> std::fmt::Result {
        fmt.write_str(&show(t))
    }

    pub fn err_code(t: T) -> isize {
        to_enum(t)
    }
}

/// `Error_codes.Typing`
pub mod typing {
    /// `Error_codes.Typing.t` (its constructors are `oxidized::error_codes::Typing`'s)
    pub use oxidized::error_codes::Typing as T;

    /// `to_enum` (`[@@deriving enum]`): the code of an error.
    pub fn to_enum(t: T) -> isize {
        // The discriminants of `oxidized::error_codes::Typing` are the
        // `[@value]`s of the OCaml.
        t as isize
    }

    /// `of_enum` (`[@@deriving enum]`): the error that has this code.
    pub fn of_enum(i: isize) -> Option<T> {
        Some(match i {
            0 => T::InternalError,
            4002 => T::UninstantiableClass,
            4005 => T::ArrayAccessRead,
            4006 => T::ArrayAppend,
            4007 => T::ArrayCast,
            4008 => T::ArrayGetArity,
            4009 => T::BadCall,
            4011 => T::ConstMutation,
            4012 => T::ConstructorNoArgs,
            4013 => T::CyclicClassDef,
            4014 => T::CyclicTypedef,
            4015 => T::DiscardedAwaitable,
            4016 => T::IssetEmptyInStrict,
            4018 => T::EnumConstantTypeBad,
            4019 => T::EnumSwitchNonexhaustive,
            4020 => T::EnumSwitchNotConst,
            4021 => T::EnumSwitchRedundant,
            4022 => T::EnumSwitchRedundantDefault,
            4023 => T::EnumSwitchWrongClass,
            4024 => T::EnumTypeBad,
            4026 => T::ExpectedClass,
            4027 => T::ExpectedLiteralFormatString,
            4029 => T::ExpectedTparam,
            4030 => T::ExpectingReturnTypeHint,
            4032 => T::ExpectingTypeHint,
            4033 => T::ExpectingTypeHintVariadic,
            4035 => T::ExtendFinal,
            4036 => T::FieldKinds,
            4038 => T::FormatString,
            4040 => T::FunTooFewArgs,
            4041 => T::FunTooManyArgs,
            4042 => T::FunUnexpectedNonvariadic,
            4043 => T::FunVariadicityHhVsPhp56,
            4046 => T::GenericStatic,
            4047 => T::ImplementAbstract,
            4049 => T::InvalidShapeFieldConst,
            4050 => T::InvalidShapeFieldLiteral,
            4051 => T::InvalidShapeFieldName,
            4052 => T::InvalidShapeFieldType,
            4053 => T::MemberNotFound,
            4054 => T::MemberNotImplemented,
            4055 => T::MissingAssign,
            4056 => T::MissingConstructor,
            4057 => T::MissingField,
            4059 => T::SelfOutsideClass,
            4060 => T::NewStaticInconsistent,
            4061 => T::StaticOutsideClass,
            4062 => T::NonObjectMemberRead,
            4063 => T::NullContainer,
            4064 => T::NullMemberRead,
            4066 => T::OptionReturnOnlyTypehint,
            4067 => T::ObjectString,
            4070 => T::OverrideFinal,
            4071 => T::OverridePerTrait,
            4073 => T::AbstractCall,
            4074 => T::ParentInTrait,
            4075 => T::ParentOutsideClass,
            4076 => T::ParentUndefined,
            4077 => T::PreviousDefault,
            4083 => T::ReadBeforeWrite,
            4084 => T::ReturnInVoid,
            4085 => T::ShapeFieldClassMismatch,
            4086 => T::ShapeFieldTypeMismatch,
            4087 => T::ShouldNotBeOverride,
            4090 => T::SmemberNotFound,
            4091 => T::StaticDynamic,
            4095 => T::ThisVarOutsideClass,
            4100 => T::TupleSyntax,
            4101 => T::TypeArityMismatch,
            4104 => T::TypingTooFewArgs,
            4105 => T::TypingTooManyArgs,
            4106 => T::UnboundGlobal,
            4107 => T::UnboundNameTyping,
            4108 => T::UndefinedField,
            4110 => T::UnifyError,
            4111 => T::UnsatisfiedReq,
            4112 => T::Visibility,
            4113 => T::VisibilityExtends,
            4115 => T::WrongExtendKind,
            4116 => T::GenericUnify,
            4118 => T::TrivialStrictEq,
            4119 => T::VoidUsage,
            4120 => T::DeclaredCovariant,
            4121 => T::DeclaredContravariant,
            4124 => T::ErasedGenericAtRuntime,
            4126 => T::AttributeTooManyArguments,
            4127 => T::AttributeParamType,
            4128 => T::DeprecatedUse,
            4129 => T::AbstractConstUsage,
            4130 => T::CannotDeclareConstant,
            4131 => T::CyclicTypeconst,
            4132 => T::NullsafePropertyWriteContext,
            4133 => T::NoreturnUsage,
            4135 => T::UnsetNonidxInStrict,
            4136 => T::InvalidShapeFieldNameEmpty,
            4138 => T::ShapeFieldsUnknown,
            4139 => T::InvalidShapeRemoveKey,
            4142 => T::AbstractConcreteOverride,
            4143 => T::LocalVariableModifedAndUsed,
            4144 => T::LocalVariableModifedTwice,
            4145 => T::AssignDuringCase,
            4146 => T::CyclicEnumConstraint,
            4147 => T::UnpackingDisallowed,
            4148 => T::InvalidClassname,
            4149 => T::InvalidMemoizedParam,
            4150 => T::IllegalTypeStructure,
            4151 => T::NotNullableCompareNullTrivial,
            4153 => T::AttributeTooFewArguments,
            4155 => T::UnificationCycle,
            4156 => T::KeysetSet,
            4157 => T::EqIncompatibleTypes,
            4158 => T::ContravariantThis,
            4163 => T::RequiredFieldIsOptional,
            4165 => T::ArrayGetWithOptionalField,
            4167 => T::NullableCast,
            4178 => T::DuplicateUsingVar,
            4179 => T::IllegalDisposable,
            4180 => T::EscapingDisposable,
            4182 => T::InoutAnnotationMissing,
            4183 => T::InoutAnnotationUnexpected,
            4184 => T::InoutnessMismatch,
            4185 => T::StaticSyntheticMethod,
            4186 => T::TraitReuse,
            4187 => T::InvalidNewDisposable,
            4188 => T::EscapingDisposableParameter,
            4189 => T::AcceptDisposableInvariant,
            4190 => T::InvalidDisposableHint,
            4191 => T::XhpRequired,
            4192 => T::EscapingThis,
            4193 => T::IllegalXhpChild,
            4194 => T::MustExtendDisposable,
            4195 => T::InvalidIsAsExpressionHint,
            4196 => T::AssigningToConst,
            4197 => T::SelfConstParentNot,
            4204 => T::OverridingPropConstMismatch,
            4205 => T::InvalidReturnDisposable,
            4206 => T::InvalidDisposableReturnHint,
            4207 => T::ReturnDisposableMismatch,
            4208 => T::InoutArgumentBadType,
            4219 => T::EnumTypeTypedefNonnull,
            4222 => T::AmbiguousLambda,
            4231 => T::WrongExpressionKindAttribute,
            4238 => T::ExtendSealed,
            4240 => T::ComparisonInvalidTypes,
            4249 => T::ShapesKeyExistsAlwaysTrue,
            4250 => T::ShapesKeyExistsAlwaysFalse,
            4251 => T::ShapesMethodAccessWithNonExistentField,
            4252 => T::NonClassMember,
            4256 => T::AmbiguousObjectAccess,
            4274 => T::RePrefixedNonString,
            4275 => T::BadRegexPattern,
            4277 => T::LateInitWithDefault,
            4279 => T::ClassVarTypeGenericParam,
            4281 => T::StringCast,
            4282 => T::BadLateInitOverride,
            4284 => T::OverrideLSB,
            4285 => T::MultipleConcreteDefs,
            4291 => T::UnexpectedTy,
            4296 => T::UnknownObjectMember,
            4297 => T::UnknownType,
            4301 => T::RedeclaringMissingMethod,
            4302 => T::InvalidEnforceableTypeArgument,
            4303 => T::RequireArgsReify,
            4304 => T::TypecheckerTimeout,
            4305 => T::InvalidReifiedArgument,
            4306 => T::GenericsNotAllowed,
            4307 => T::InvalidNewableTypeArgument,
            4308 => T::InvalidNewableTypeParamConstraints,
            4309 => T::NewWithoutNewable,
            4310 => T::NewClassReified,
            4311 => T::MemoizeReified,
            4312 => T::ConsistentConstructReified,
            4313 => T::MethodVariance,
            4314 => T::MissingXhpRequiredAttr,
            4315 => T::BadXhpAttrRequiredOverride,
            4317 => T::UnresolvedTypeVariable,
            4318 => T::InvalidSubString,
            4319 => T::InvalidArrayKeyConstraint,
            4320 => T::OverrideNoDefaultTypeconst,
            4321 => T::ShapeAccessWithNonExistentField,
            4322 => T::DisallowPHPArraysAttr,
            4323 => T::TypeConstraintViolation,
            4324 => T::IndexTypeMismatch,
            4325 => T::ExpectedStringlike,
            4326 => T::TypeConstantMismatch,
            4328 => T::ConstantDoesNotMatchEnumType,
            4329 => T::EnumConstraintMustBeArraykey,
            4330 => T::EnumSubtypeMustHaveCompatibleConstraint,
            4331 => T::ParameterDefaultValueWrongType,
            4332 => T::NewtypeAliasMustSatisfyConstraint,
            4336 => T::MissingReturnInNonVoidFunction,
            4337 => T::InoutReturnTypeMismatch,
            4338 => T::ClassConstantValueDoesNotMatchHint,
            4339 => T::ClassPropertyInitializerTypeDoesNotMatchHint,
            4340 => T::BadDeclOverride,
            4341 => T::BadMethodOverride,
            4342 => T::BadEnumExtends,
            4343 => T::XhpAttributeValueDoesNotMatchHint,
            4344 => T::TraitPropConstClass,
            4345 => T::EnumUnderlyingTypeMustBeArraykey,
            4346 => T::ClassGetReified,
            4347 => T::RequireGenericExplicit,
            4348 => T::ClassConstantTypeMismatch,
            4352 => T::AbstractTconstNotAllowed,
            4357 => T::InvalidDestructure,
            4358 => T::StaticMethWithClassReifiedGeneric,
            4359 => T::SplatArrayRequired,
            4361 => T::ExceptionOccurred,
            4362 => T::InvalidReifiedFunctionPointer,
            4363 => T::BadFunctionPointerConstruction,
            4365 => T::TraitReuseInsideClass,
            4366 => T::RedundantGeneric,
            4370 => T::ArrayAccessWrite,
            4371 => T::InvalidArrayKeyWrite,
            4372 => T::NullMemberWrite,
            4373 => T::NonObjectMemberWrite,
            4374 => T::ConcreteConstInterfaceOverride,
            4375 => T::MethCallerTrait,
            4377 => T::DuplicateInterface,
            4381 => T::ReifiedFunctionReference,
            4383 => T::KindMismatch,
            4388 => T::IncompatibleEnumInclusion,
            4389 => T::RedeclaringClassishConstant,
            4390 => T::CallCoeffects,
            4391 => T::AbstractFunctionPointer,
            4392 => T::UnnecessaryAttribute,
            4393 => T::InheritedMethodCaseDiffers,
            4394 => T::EnumClassLabelUnknown,
            4396 => T::EnumClassLabelAsExpression,
            4401 => T::OpCoeffects,
            4402 => T::ImplementsDynamic,
            4403 => T::SubtypeCoeffects,
            4404 => T::ImmutableLocal,
            4406 => T::NonsenseMemberSelection,
            4407 => T::ConsiderMethCaller,
            4409 => T::ReadonlyValueModified,
            4411 => T::ReadonlyMismatch,
            4412 => T::ExplicitReadonlyCast,
            4413 => T::ReadonlyMethodCall,
            4414 => T::StrictStrConcatTypeMismatch,
            4415 => T::StrictStrInterpTypeMismatch,
            4416 => T::InvalidMethCallerCallingConvention,
            4418 => T::ReadonlyException,
            4419 => T::InvalidTypeHint,
            4420 => T::ExperimentalExpressionTrees,
            4421 => T::ReturnsWithAndWithoutValue,
            4422 => T::NonVoidAnnotationOnReturnVoidFun,
            4423 => T::BitwiseMathInvalidArgument,
            4424 => T::CyclicClassConstant,
            4425 => T::PrivateDynamicRead,
            4426 => T::PrivateDynamicWrite,
            4427 => T::IncDecInvalidArgument,
            4428 => T::ReadonlyClosureCall,
            4429 => T::MathInvalidArgument,
            4430 => T::TypeconstConcreteConcreteOverride,
            4431 => T::PrivateMethCaller,
            4432 => T::ProtectedMethCaller,
            4433 => T::BadConditionalSupportDynamic,
            4434 => T::ReadonlyInvalidAsMut,
            4435 => T::InvalidKeysetValue,
            4436 => T::UnresolvedTypeVariableProjection,
            4438 => T::InvalidEchoArgument,
            4439 => T::DiamondTraitMethod,
            4440 => T::ReifiedStaticMethodInExprTree,
            4441 => T::InvariantViolated,
            4442 => T::RigidTVarEscape,
            4443 => T::StrictEqValueIncompatibleTypes,
            4444 => T::ModuleError,
            4446 => T::ModuleHintError,
            4447 => T::MemoizeObjectWithoutGlobals,
            4448 => T::ExpressionTreeNonPublicProperty,
            4449 => T::CovariantIndexTypeMismatch,
            4450 => T::InoutInPseudofunction,
            4451 => T::TraitParentConstructInconsistent,
            4452 => T::HHExpectEquivalentFailure,
            4453 => T::HHExpectFailure,
            4454 => T::CallLvalue,
            4455 => T::UnsafeCastAwait,
            4457 => T::ThisFinal,
            4462 => T::DiamondTraitProperty,
            4463 => T::ConstructNotInstanceMethod,
            4464 => T::InvalidMethCallerReadonlyReturn,
            4465 => T::AbstractMemberInConcreteClass,
            4466 => T::TraitNotUsed,
            4467 => T::OverrideAsync,
            4468 => T::InexactTConstAccess,
            4469 => T::UnsupportedRefinement,
            4470 => T::InvalidClassRefinement,
            4471 => T::InvalidRefinedConstKind,
            4472 => T::InvalidCrossPackage,
            4473 => T::InvalidCrossPackageSoft,
            4474 => T::AttributeNoAutoDynamic,
            4475 => T::IllegalCaseTypeVariants,
            4476 => T::StaticCallOnTraitRequireClass,
            4477 => T::WrongUseKind,
            4478 => T::MatchNotExhaustive,
            4479 => T::MatchOnUnsupportedType,
            4480 => T::MultipleInstantiationInheritence,
            4481 => T::InternalMethCaller,
            4482 => T::ClassPointerToString,
            4483 => T::InvalidXhpAttributeValue,
            4484 => T::OptionalParameterNotSupported,
            4485 => T::InvalidRecursiveType,
            4486 => T::StaticCallOnTraitRequireThisAs,
            4488 => T::StringToClassPointer,
            4489 => T::SwitchNeedsDefault,
            4493 => T::SimpliHackRunPrompt,
            4495 => T::SimpliHackEvalError,
            4496 => T::ProtectedInternalMethCaller,
            4497 => T::StaticPropOnTrait,
            4498 => T::RecursiveCaseType,
            4499 => T::MissingNamedArgs,
            4500 => T::UnexpectedNamedArgs,
            4501 => T::DuplicateNamedArgs,
            4503 => T::OverrideSealed,
            4504 => T::ExpectBoolForCondition,
            4505 => T::NeedsConcreteInFinalClass,
            4506 => T::NeedsConcreteOnInstanceMethod,
            4507 => T::NeedsConcreteOnConstructor,
            4508 => T::ConsistentConstructAbstractExtendsNonAbstract,
            4509 => T::GatedByFeatureFlag,
            4510 => T::DestructureMissingEllipsis,
            4511 => T::DestructureMissingRequiredField,
            4512 => T::DestructureUnknownField,
            4513 => T::DestructureTupleArityMismatch,
            4514 => T::TestsBypassVisibilityOverride,
            4515 => T::TestsBypassVisibilityOnMemberWithoutClass,
            4516 => T::TestsBypassVisibilityAbstractMissingAttr,
            4517 => T::ThisAsFunctionPointerParam,
            4518 => T::StrictIsolationExcludedPathAccess,
            4519 => T::EnumDuplicateValue,
            4520 => T::EnumUncheckableValue,
            4522 => T::SplatMayRequireFields,
            4523 => T::SplatFieldNotKnown,
            4524 => T::RedeclaringPromotedProperty,
            4525 => T::RequireDynamicObjGet,
            4526 => T::NeedsConcreteOverride,
            4527 => T::InvalidMethCallerNamedParameter,
            4528 => T::CallNeedsConcrete,
            4529 => T::AbstractAccessViaStatic,
            4530 => T::UninstantiableClassViaStatic,
            4531 => T::RedundantShapeSplat,
            4532 => T::UnsupportedCyclicShapeSplatBounds,
            4533 => T::ShapeKeyClassConstMissingAttribute,
            4534 => T::ShapeKeyClassConstValueUnresolvable,
            4535 => T::ShapeKeyClassConstIsAbstract,
            4536 => T::ThisRefinementInGenericClass,
            4537 => T::PrivateMemberVariance,
            4538 => T::MemoizeErasedGenericReturn,
            _ => return None,
        })
    }

    /// `min` (`[@@deriving enum]`): the smallest code.
    pub const MIN: isize = 0;

    /// `max` (`[@@deriving enum]`): the largest code.
    pub const MAX: isize = 4538;

    /// `show` (`[@@deriving show { with_path = false }]`): the name of the
    /// OCaml constructor.
    pub fn show(t: T) -> String {
        match t {
            T::InternalError => "InternalError",
            T::UninstantiableClass => "UninstantiableClass",
            T::ArrayAccessRead => "ArrayAccessRead",
            T::ArrayAppend => "ArrayAppend",
            T::ArrayCast => "ArrayCast",
            T::ArrayGetArity => "ArrayGetArity",
            T::BadCall => "BadCall",
            T::ConstMutation => "ConstMutation",
            T::ConstructorNoArgs => "ConstructorNoArgs",
            T::CyclicClassDef => "CyclicClassDef",
            T::CyclicTypedef => "CyclicTypedef",
            T::DiscardedAwaitable => "DiscardedAwaitable",
            T::IssetEmptyInStrict => "IssetEmptyInStrict",
            T::EnumConstantTypeBad => "EnumConstantTypeBad",
            T::EnumSwitchNonexhaustive => "EnumSwitchNonexhaustive",
            T::EnumSwitchNotConst => "EnumSwitchNotConst",
            T::EnumSwitchRedundant => "EnumSwitchRedundant",
            T::EnumSwitchRedundantDefault => "EnumSwitchRedundantDefault",
            T::EnumSwitchWrongClass => "EnumSwitchWrongClass",
            T::EnumTypeBad => "EnumTypeBad",
            T::ExpectedClass => "ExpectedClass",
            T::ExpectedLiteralFormatString => "ExpectedLiteralFormatString",
            T::ExpectedTparam => "ExpectedTparam",
            T::ExpectingReturnTypeHint => "ExpectingReturnTypeHint",
            T::ExpectingTypeHint => "ExpectingTypeHint",
            T::ExpectingTypeHintVariadic => "ExpectingTypeHintVariadic",
            T::ExtendFinal => "ExtendFinal",
            T::FieldKinds => "FieldKinds",
            T::FormatString => "FormatString",
            T::FunTooFewArgs => "FunTooFewArgs",
            T::FunTooManyArgs => "FunTooManyArgs",
            T::FunUnexpectedNonvariadic => "FunUnexpectedNonvariadic",
            T::FunVariadicityHhVsPhp56 => "FunVariadicityHhVsPhp56",
            T::GenericStatic => "GenericStatic",
            T::ImplementAbstract => "ImplementAbstract",
            T::InvalidShapeFieldConst => "InvalidShapeFieldConst",
            T::InvalidShapeFieldLiteral => "InvalidShapeFieldLiteral",
            T::InvalidShapeFieldName => "InvalidShapeFieldName",
            T::InvalidShapeFieldType => "InvalidShapeFieldType",
            T::MemberNotFound => "MemberNotFound",
            T::MemberNotImplemented => "MemberNotImplemented",
            T::MissingAssign => "MissingAssign",
            T::MissingConstructor => "MissingConstructor",
            T::MissingField => "MissingField",
            T::SelfOutsideClass => "SelfOutsideClass",
            T::NewStaticInconsistent => "NewStaticInconsistent",
            T::StaticOutsideClass => "StaticOutsideClass",
            T::NonObjectMemberRead => "NonObjectMemberRead",
            T::NullContainer => "NullContainer",
            T::NullMemberRead => "NullMemberRead",
            T::OptionReturnOnlyTypehint => "OptionReturnOnlyTypehint",
            T::ObjectString => "ObjectString",
            T::OverrideFinal => "OverrideFinal",
            T::OverridePerTrait => "OverridePerTrait",
            T::AbstractCall => "AbstractCall",
            T::ParentInTrait => "ParentInTrait",
            T::ParentOutsideClass => "ParentOutsideClass",
            T::ParentUndefined => "ParentUndefined",
            T::PreviousDefault => "PreviousDefault",
            T::ReadBeforeWrite => "ReadBeforeWrite",
            T::ReturnInVoid => "ReturnInVoid",
            T::ShapeFieldClassMismatch => "ShapeFieldClassMismatch",
            T::ShapeFieldTypeMismatch => "ShapeFieldTypeMismatch",
            T::ShouldNotBeOverride => "ShouldNotBeOverride",
            T::SmemberNotFound => "SmemberNotFound",
            T::StaticDynamic => "StaticDynamic",
            T::ThisVarOutsideClass => "ThisVarOutsideClass",
            T::TupleSyntax => "TupleSyntax",
            T::TypeArityMismatch => "TypeArityMismatch",
            T::TypingTooFewArgs => "TypingTooFewArgs",
            T::TypingTooManyArgs => "TypingTooManyArgs",
            T::UnboundGlobal => "UnboundGlobal",
            T::UnboundNameTyping => "UnboundNameTyping",
            T::UndefinedField => "UndefinedField",
            T::UnifyError => "UnifyError",
            T::UnsatisfiedReq => "UnsatisfiedReq",
            T::Visibility => "Visibility",
            T::VisibilityExtends => "VisibilityExtends",
            T::WrongExtendKind => "WrongExtendKind",
            T::GenericUnify => "GenericUnify",
            T::TrivialStrictEq => "TrivialStrictEq",
            T::VoidUsage => "VoidUsage",
            T::DeclaredCovariant => "DeclaredCovariant",
            T::DeclaredContravariant => "DeclaredContravariant",
            T::ErasedGenericAtRuntime => "ErasedGenericAtRuntime",
            T::AttributeTooManyArguments => "AttributeTooManyArguments",
            T::AttributeParamType => "AttributeParamType",
            T::DeprecatedUse => "DeprecatedUse",
            T::AbstractConstUsage => "AbstractConstUsage",
            T::CannotDeclareConstant => "CannotDeclareConstant",
            T::CyclicTypeconst => "CyclicTypeconst",
            T::NullsafePropertyWriteContext => "NullsafePropertyWriteContext",
            T::NoreturnUsage => "NoreturnUsage",
            T::UnsetNonidxInStrict => "UnsetNonidxInStrict",
            T::InvalidShapeFieldNameEmpty => "InvalidShapeFieldNameEmpty",
            T::ShapeFieldsUnknown => "ShapeFieldsUnknown",
            T::InvalidShapeRemoveKey => "InvalidShapeRemoveKey",
            T::AbstractConcreteOverride => "AbstractConcreteOverride",
            T::LocalVariableModifedAndUsed => "LocalVariableModifedAndUsed",
            T::LocalVariableModifedTwice => "LocalVariableModifedTwice",
            T::AssignDuringCase => "AssignDuringCase",
            T::CyclicEnumConstraint => "CyclicEnumConstraint",
            T::UnpackingDisallowed => "UnpackingDisallowed",
            T::InvalidClassname => "InvalidClassname",
            T::InvalidMemoizedParam => "InvalidMemoizedParam",
            T::IllegalTypeStructure => "IllegalTypeStructure",
            T::NotNullableCompareNullTrivial => "NotNullableCompareNullTrivial",
            T::AttributeTooFewArguments => "AttributeTooFewArguments",
            T::UnificationCycle => "UnificationCycle",
            T::KeysetSet => "KeysetSet",
            T::EqIncompatibleTypes => "EqIncompatibleTypes",
            T::ContravariantThis => "ContravariantThis",
            T::RequiredFieldIsOptional => "RequiredFieldIsOptional",
            T::ArrayGetWithOptionalField => "ArrayGetWithOptionalField",
            T::NullableCast => "NullableCast",
            T::DuplicateUsingVar => "DuplicateUsingVar",
            T::IllegalDisposable => "IllegalDisposable",
            T::EscapingDisposable => "EscapingDisposable",
            T::InoutAnnotationMissing => "InoutAnnotationMissing",
            T::InoutAnnotationUnexpected => "InoutAnnotationUnexpected",
            T::InoutnessMismatch => "InoutnessMismatch",
            T::StaticSyntheticMethod => "StaticSyntheticMethod",
            T::TraitReuse => "TraitReuse",
            T::InvalidNewDisposable => "InvalidNewDisposable",
            T::EscapingDisposableParameter => "EscapingDisposableParameter",
            T::AcceptDisposableInvariant => "AcceptDisposableInvariant",
            T::InvalidDisposableHint => "InvalidDisposableHint",
            T::XhpRequired => "XhpRequired",
            T::EscapingThis => "EscapingThis",
            T::IllegalXhpChild => "IllegalXhpChild",
            T::MustExtendDisposable => "MustExtendDisposable",
            T::InvalidIsAsExpressionHint => "InvalidIsAsExpressionHint",
            T::AssigningToConst => "AssigningToConst",
            T::SelfConstParentNot => "SelfConstParentNot",
            T::OverridingPropConstMismatch => "OverridingPropConstMismatch",
            T::InvalidReturnDisposable => "InvalidReturnDisposable",
            T::InvalidDisposableReturnHint => "InvalidDisposableReturnHint",
            T::ReturnDisposableMismatch => "ReturnDisposableMismatch",
            T::InoutArgumentBadType => "InoutArgumentBadType",
            T::EnumTypeTypedefNonnull => "EnumTypeTypedefNonnull",
            T::AmbiguousLambda => "AmbiguousLambda",
            T::WrongExpressionKindAttribute => "WrongExpressionKindAttribute",
            T::ExtendSealed => "ExtendSealed",
            T::ComparisonInvalidTypes => "ComparisonInvalidTypes",
            T::ShapesKeyExistsAlwaysTrue => "ShapesKeyExistsAlwaysTrue",
            T::ShapesKeyExistsAlwaysFalse => "ShapesKeyExistsAlwaysFalse",
            T::ShapesMethodAccessWithNonExistentField => "ShapesMethodAccessWithNonExistentField",
            T::NonClassMember => "NonClassMember",
            T::AmbiguousObjectAccess => "AmbiguousObjectAccess",
            T::RePrefixedNonString => "RePrefixedNonString",
            T::BadRegexPattern => "BadRegexPattern",
            T::LateInitWithDefault => "LateInitWithDefault",
            T::ClassVarTypeGenericParam => "ClassVarTypeGenericParam",
            T::StringCast => "StringCast",
            T::BadLateInitOverride => "BadLateInitOverride",
            T::OverrideLSB => "OverrideLSB",
            T::MultipleConcreteDefs => "MultipleConcreteDefs",
            T::UnexpectedTy => "UnexpectedTy",
            T::UnknownObjectMember => "UnknownObjectMember",
            T::UnknownType => "UnknownType",
            T::RedeclaringMissingMethod => "RedeclaringMissingMethod",
            T::InvalidEnforceableTypeArgument => "InvalidEnforceableTypeArgument",
            T::RequireArgsReify => "RequireArgsReify",
            T::TypecheckerTimeout => "TypecheckerTimeout",
            T::InvalidReifiedArgument => "InvalidReifiedArgument",
            T::GenericsNotAllowed => "GenericsNotAllowed",
            T::InvalidNewableTypeArgument => "InvalidNewableTypeArgument",
            T::InvalidNewableTypeParamConstraints => "InvalidNewableTypeParamConstraints",
            T::NewWithoutNewable => "NewWithoutNewable",
            T::NewClassReified => "NewClassReified",
            T::MemoizeReified => "MemoizeReified",
            T::ConsistentConstructReified => "ConsistentConstructReified",
            T::MethodVariance => "MethodVariance",
            T::MissingXhpRequiredAttr => "MissingXhpRequiredAttr",
            T::BadXhpAttrRequiredOverride => "BadXhpAttrRequiredOverride",
            T::UnresolvedTypeVariable => "UnresolvedTypeVariable",
            T::InvalidSubString => "InvalidSubString",
            T::InvalidArrayKeyConstraint => "InvalidArrayKeyConstraint",
            T::OverrideNoDefaultTypeconst => "OverrideNoDefaultTypeconst",
            T::ShapeAccessWithNonExistentField => "ShapeAccessWithNonExistentField",
            T::DisallowPHPArraysAttr => "DisallowPHPArraysAttr",
            T::TypeConstraintViolation => "TypeConstraintViolation",
            T::IndexTypeMismatch => "IndexTypeMismatch",
            T::ExpectedStringlike => "ExpectedStringlike",
            T::TypeConstantMismatch => "TypeConstantMismatch",
            T::ConstantDoesNotMatchEnumType => "ConstantDoesNotMatchEnumType",
            T::EnumConstraintMustBeArraykey => "EnumConstraintMustBeArraykey",
            T::EnumSubtypeMustHaveCompatibleConstraint => "EnumSubtypeMustHaveCompatibleConstraint",
            T::ParameterDefaultValueWrongType => "ParameterDefaultValueWrongType",
            T::NewtypeAliasMustSatisfyConstraint => "NewtypeAliasMustSatisfyConstraint",
            T::MissingReturnInNonVoidFunction => "MissingReturnInNonVoidFunction",
            T::InoutReturnTypeMismatch => "InoutReturnTypeMismatch",
            T::ClassConstantValueDoesNotMatchHint => "ClassConstantValueDoesNotMatchHint",
            T::ClassPropertyInitializerTypeDoesNotMatchHint => {
                "ClassPropertyInitializerTypeDoesNotMatchHint"
            }
            T::BadDeclOverride => "BadDeclOverride",
            T::BadMethodOverride => "BadMethodOverride",
            T::BadEnumExtends => "BadEnumExtends",
            T::XhpAttributeValueDoesNotMatchHint => "XhpAttributeValueDoesNotMatchHint",
            T::TraitPropConstClass => "TraitPropConstClass",
            T::EnumUnderlyingTypeMustBeArraykey => "EnumUnderlyingTypeMustBeArraykey",
            T::ClassGetReified => "ClassGetReified",
            T::RequireGenericExplicit => "RequireGenericExplicit",
            T::ClassConstantTypeMismatch => "ClassConstantTypeMismatch",
            T::AbstractTconstNotAllowed => "AbstractTconstNotAllowed",
            T::InvalidDestructure => "InvalidDestructure",
            T::StaticMethWithClassReifiedGeneric => "StaticMethWithClassReifiedGeneric",
            T::SplatArrayRequired => "SplatArrayRequired",
            T::ExceptionOccurred => "ExceptionOccurred",
            T::InvalidReifiedFunctionPointer => "InvalidReifiedFunctionPointer",
            T::BadFunctionPointerConstruction => "BadFunctionPointerConstruction",
            T::TraitReuseInsideClass => "TraitReuseInsideClass",
            T::RedundantGeneric => "RedundantGeneric",
            T::ArrayAccessWrite => "ArrayAccessWrite",
            T::InvalidArrayKeyWrite => "InvalidArrayKeyWrite",
            T::NullMemberWrite => "NullMemberWrite",
            T::NonObjectMemberWrite => "NonObjectMemberWrite",
            T::ConcreteConstInterfaceOverride => "ConcreteConstInterfaceOverride",
            T::MethCallerTrait => "MethCallerTrait",
            T::DuplicateInterface => "DuplicateInterface",
            T::ReifiedFunctionReference => "ReifiedFunctionReference",
            T::KindMismatch => "KindMismatch",
            T::IncompatibleEnumInclusion => "IncompatibleEnumInclusion",
            T::RedeclaringClassishConstant => "RedeclaringClassishConstant",
            T::CallCoeffects => "CallCoeffects",
            T::AbstractFunctionPointer => "AbstractFunctionPointer",
            T::UnnecessaryAttribute => "UnnecessaryAttribute",
            T::InheritedMethodCaseDiffers => "InheritedMethodCaseDiffers",
            T::EnumClassLabelUnknown => "EnumClassLabelUnknown",
            T::EnumClassLabelAsExpression => "EnumClassLabelAsExpression",
            T::OpCoeffects => "OpCoeffects",
            T::ImplementsDynamic => "ImplementsDynamic",
            T::SubtypeCoeffects => "SubtypeCoeffects",
            T::ImmutableLocal => "ImmutableLocal",
            T::NonsenseMemberSelection => "NonsenseMemberSelection",
            T::ConsiderMethCaller => "ConsiderMethCaller",
            T::ReadonlyValueModified => "ReadonlyValueModified",
            T::ReadonlyMismatch => "ReadonlyMismatch",
            T::ExplicitReadonlyCast => "ExplicitReadonlyCast",
            T::ReadonlyMethodCall => "ReadonlyMethodCall",
            T::StrictStrConcatTypeMismatch => "StrictStrConcatTypeMismatch",
            T::StrictStrInterpTypeMismatch => "StrictStrInterpTypeMismatch",
            T::InvalidMethCallerCallingConvention => "InvalidMethCallerCallingConvention",
            T::ReadonlyException => "ReadonlyException",
            T::InvalidTypeHint => "InvalidTypeHint",
            T::ExperimentalExpressionTrees => "ExperimentalExpressionTrees",
            T::ReturnsWithAndWithoutValue => "ReturnsWithAndWithoutValue",
            T::NonVoidAnnotationOnReturnVoidFun => "NonVoidAnnotationOnReturnVoidFun",
            T::BitwiseMathInvalidArgument => "BitwiseMathInvalidArgument",
            T::CyclicClassConstant => "CyclicClassConstant",
            T::PrivateDynamicRead => "PrivateDynamicRead",
            T::PrivateDynamicWrite => "PrivateDynamicWrite",
            T::IncDecInvalidArgument => "IncDecInvalidArgument",
            T::ReadonlyClosureCall => "ReadonlyClosureCall",
            T::MathInvalidArgument => "MathInvalidArgument",
            T::TypeconstConcreteConcreteOverride => "TypeconstConcreteConcreteOverride",
            T::PrivateMethCaller => "PrivateMethCaller",
            T::ProtectedMethCaller => "ProtectedMethCaller",
            T::BadConditionalSupportDynamic => "BadConditionalSupportDynamic",
            T::ReadonlyInvalidAsMut => "ReadonlyInvalidAsMut",
            T::InvalidKeysetValue => "InvalidKeysetValue",
            T::UnresolvedTypeVariableProjection => "UnresolvedTypeVariableProjection",
            T::InvalidEchoArgument => "InvalidEchoArgument",
            T::DiamondTraitMethod => "DiamondTraitMethod",
            T::ReifiedStaticMethodInExprTree => "ReifiedStaticMethodInExprTree",
            T::InvariantViolated => "InvariantViolated",
            T::RigidTVarEscape => "RigidTVarEscape",
            T::StrictEqValueIncompatibleTypes => "StrictEqValueIncompatibleTypes",
            T::ModuleError => "ModuleError",
            T::ModuleHintError => "ModuleHintError",
            T::MemoizeObjectWithoutGlobals => "MemoizeObjectWithoutGlobals",
            T::ExpressionTreeNonPublicProperty => "ExpressionTreeNonPublicProperty",
            T::CovariantIndexTypeMismatch => "CovariantIndexTypeMismatch",
            T::InoutInPseudofunction => "InoutInPseudofunction",
            T::TraitParentConstructInconsistent => "TraitParentConstructInconsistent",
            T::HHExpectEquivalentFailure => "HHExpectEquivalentFailure",
            T::HHExpectFailure => "HHExpectFailure",
            T::CallLvalue => "CallLvalue",
            T::UnsafeCastAwait => "UnsafeCastAwait",
            T::ThisFinal => "ThisFinal",
            T::DiamondTraitProperty => "DiamondTraitProperty",
            T::ConstructNotInstanceMethod => "ConstructNotInstanceMethod",
            T::InvalidMethCallerReadonlyReturn => "InvalidMethCallerReadonlyReturn",
            T::AbstractMemberInConcreteClass => "AbstractMemberInConcreteClass",
            T::TraitNotUsed => "TraitNotUsed",
            T::OverrideAsync => "OverrideAsync",
            T::InexactTConstAccess => "InexactTConstAccess",
            T::UnsupportedRefinement => "UnsupportedRefinement",
            T::InvalidClassRefinement => "InvalidClassRefinement",
            T::InvalidRefinedConstKind => "InvalidRefinedConstKind",
            T::InvalidCrossPackage => "InvalidCrossPackage",
            T::InvalidCrossPackageSoft => "InvalidCrossPackageSoft",
            T::AttributeNoAutoDynamic => "AttributeNoAutoDynamic",
            T::IllegalCaseTypeVariants => "IllegalCaseTypeVariants",
            T::StaticCallOnTraitRequireClass => "StaticCallOnTraitRequireClass",
            T::WrongUseKind => "WrongUseKind",
            T::MatchNotExhaustive => "MatchNotExhaustive",
            T::MatchOnUnsupportedType => "MatchOnUnsupportedType",
            T::MultipleInstantiationInheritence => "MultipleInstantiationInheritence",
            T::InternalMethCaller => "InternalMethCaller",
            T::ClassPointerToString => "ClassPointerToString",
            T::InvalidXhpAttributeValue => "InvalidXhpAttributeValue",
            T::OptionalParameterNotSupported => "OptionalParameterNotSupported",
            T::InvalidRecursiveType => "InvalidRecursiveType",
            T::StaticCallOnTraitRequireThisAs => "StaticCallOnTraitRequireThisAs",
            T::StringToClassPointer => "StringToClassPointer",
            T::SwitchNeedsDefault => "SwitchNeedsDefault",
            T::SimpliHackRunPrompt => "SimpliHackRunPrompt",
            T::SimpliHackEvalError => "SimpliHackEvalError",
            T::ProtectedInternalMethCaller => "ProtectedInternalMethCaller",
            T::StaticPropOnTrait => "StaticPropOnTrait",
            T::RecursiveCaseType => "RecursiveCaseType",
            T::MissingNamedArgs => "MissingNamedArgs",
            T::UnexpectedNamedArgs => "UnexpectedNamedArgs",
            T::DuplicateNamedArgs => "DuplicateNamedArgs",
            T::OverrideSealed => "OverrideSealed",
            T::ExpectBoolForCondition => "ExpectBoolForCondition",
            T::NeedsConcreteInFinalClass => "NeedsConcreteInFinalClass",
            T::NeedsConcreteOnInstanceMethod => "NeedsConcreteOnInstanceMethod",
            T::NeedsConcreteOnConstructor => "NeedsConcreteOnConstructor",
            T::ConsistentConstructAbstractExtendsNonAbstract => {
                "ConsistentConstructAbstractExtendsNonAbstract"
            }
            T::GatedByFeatureFlag => "GatedByFeatureFlag",
            T::DestructureMissingEllipsis => "DestructureMissingEllipsis",
            T::DestructureMissingRequiredField => "DestructureMissingRequiredField",
            T::DestructureUnknownField => "DestructureUnknownField",
            T::DestructureTupleArityMismatch => "DestructureTupleArityMismatch",
            T::TestsBypassVisibilityOverride => "TestsBypassVisibilityOverride",
            T::TestsBypassVisibilityOnMemberWithoutClass => {
                "TestsBypassVisibilityOnMemberWithoutClass"
            }
            T::TestsBypassVisibilityAbstractMissingAttr => {
                "TestsBypassVisibilityAbstractMissingAttr"
            }
            T::ThisAsFunctionPointerParam => "ThisAsFunctionPointerParam",
            T::StrictIsolationExcludedPathAccess => "StrictIsolationExcludedPathAccess",
            T::EnumDuplicateValue => "EnumDuplicateValue",
            T::EnumUncheckableValue => "EnumUncheckableValue",
            T::SplatMayRequireFields => "SplatMayRequireFields",
            T::SplatFieldNotKnown => "SplatFieldNotKnown",
            T::RedeclaringPromotedProperty => "RedeclaringPromotedProperty",
            T::RequireDynamicObjGet => "RequireDynamicObjGet",
            T::NeedsConcreteOverride => "NeedsConcreteOverride",
            T::InvalidMethCallerNamedParameter => "InvalidMethCallerNamedParameter",
            T::CallNeedsConcrete => "CallNeedsConcrete",
            T::AbstractAccessViaStatic => "AbstractAccessViaStatic",
            T::UninstantiableClassViaStatic => "UninstantiableClassViaStatic",
            T::RedundantShapeSplat => "RedundantShapeSplat",
            T::UnsupportedCyclicShapeSplatBounds => "UnsupportedCyclicShapeSplatBounds",
            T::ShapeKeyClassConstMissingAttribute => "ShapeKeyClassConstMissingAttribute",
            T::ShapeKeyClassConstValueUnresolvable => "ShapeKeyClassConstValueUnresolvable",
            T::ShapeKeyClassConstIsAbstract => "ShapeKeyClassConstIsAbstract",
            T::ThisRefinementInGenericClass => "ThisRefinementInGenericClass",
            T::PrivateMemberVariance => "PrivateMemberVariance",
            T::MemoizeErasedGenericReturn => "MemoizeErasedGenericReturn",
        }
        .to_string()
    }

    /// `pp` (`[@@deriving show { with_path = false }]`)
    pub fn pp(fmt: &mut dyn std::fmt::Write, t: T) -> std::fmt::Result {
        fmt.write_str(&show(t))
    }

    pub fn err_code(t: T) -> isize {
        to_enum(t)
    }
}

/// `Error_codes.Warning`
pub mod warning {
    /// `Error_codes.Warning.t` (its constructors are `oxidized::error_codes::Warning`'s)
    pub use oxidized::error_codes::Warning as T;

    /// `to_enum` (`[@@deriving enum]`): the code of an error.
    pub fn to_enum(t: T) -> isize {
        // The discriminants of `oxidized::error_codes::Warning` are the
        // `[@value]`s of the OCaml.
        t as isize
    }

    /// `of_enum` (`[@@deriving enum]`): the error that has this code.
    pub fn of_enum(i: isize) -> Option<T> {
        Some(match i {
            12001 => T::SketchyEquality,
            12004 => T::NonDisjointCheck,
            12005 => T::CastNonPrimitive,
            12006 => T::TruthinessTest,
            12007 => T::EqualityCheck,
            12008 => T::DuplicateProperties,
            12009 => T::IsIsAlwaysTrue,
            12010 => T::IsIsAlwaysFalse,
            12011 => T::AsAlwaysSucceeds,
            12012 => T::AsAlwaysFails,
            12013 => T::ClassPointerToString,
            12017 => T::NoDisjointUnion,
            12018 => T::SafeAbstractConstAccess,
            12019 => T::SwitchRedundancy,
            12020 => T::StaticCallOnTrait,
            12021 => T::StaticPropertyOverride,
            12022 => T::StringToClassPointer,
            12023 => T::NullCoalesceAlways,
            12024 => T::CallNeedsConcrete,
            12028 => T::ExpectBoolForCondition,
            12029 => T::RedundantNullsafeMemberSelect,
            12030 => T::NullsafeMemberSelectOnNull,
            12031 => T::RedundantNullsafePipe,
            12032 => T::NullsafePipeOnNull,
            12033 => T::UnboundNameWarning,
            12034 => T::SetOrKeysetArrayGet,
            12035 => T::SealedNotSubtype,
            12036 => T::TanyFound,
            12037 => T::ConsistentConstructAbstractFinal,
            12038 => T::DynamicMethodCall,
            12039 => T::DynamicFunctionCall,
            12040 => T::DynamicArrayAccess,
            12041 => T::SealedNotOverride,
            12042 => T::DynamicPropertyAccess,
            12043 => T::RedundantRequireThisAs,
            12044 => T::DynamicReturn,
            12045 => T::ReadonlyPropertyOverride,
            12048 => T::RedundantConcurrent,
            _ => return None,
        })
    }

    /// `min` (`[@@deriving enum]`): the smallest code.
    pub const MIN: isize = 12001;

    /// `max` (`[@@deriving enum]`): the largest code.
    pub const MAX: isize = 12048;

    /// `show` (`[@@deriving show { with_path = false }]`): the name of the
    /// OCaml constructor.
    pub fn show(t: T) -> String {
        match t {
            T::SketchyEquality => "SketchyEquality",
            T::NonDisjointCheck => "NonDisjointCheck",
            T::CastNonPrimitive => "CastNonPrimitive",
            T::TruthinessTest => "TruthinessTest",
            T::EqualityCheck => "EqualityCheck",
            T::DuplicateProperties => "DuplicateProperties",
            T::IsIsAlwaysTrue => "IsIsAlwaysTrue",
            T::IsIsAlwaysFalse => "IsIsAlwaysFalse",
            T::AsAlwaysSucceeds => "AsAlwaysSucceeds",
            T::AsAlwaysFails => "AsAlwaysFails",
            T::ClassPointerToString => "ClassPointerToString",
            T::NoDisjointUnion => "NoDisjointUnion",
            T::SafeAbstractConstAccess => "SafeAbstractConstAccess",
            T::SwitchRedundancy => "SwitchRedundancy",
            T::StaticCallOnTrait => "StaticCallOnTrait",
            T::StaticPropertyOverride => "StaticPropertyOverride",
            T::StringToClassPointer => "StringToClassPointer",
            T::NullCoalesceAlways => "NullCoalesceAlways",
            T::CallNeedsConcrete => "CallNeedsConcrete",
            T::ExpectBoolForCondition => "ExpectBoolForCondition",
            T::RedundantNullsafeMemberSelect => "RedundantNullsafeMemberSelect",
            T::NullsafeMemberSelectOnNull => "NullsafeMemberSelectOnNull",
            T::RedundantNullsafePipe => "RedundantNullsafePipe",
            T::NullsafePipeOnNull => "NullsafePipeOnNull",
            T::UnboundNameWarning => "UnboundNameWarning",
            T::SetOrKeysetArrayGet => "SetOrKeysetArrayGet",
            T::SealedNotSubtype => "SealedNotSubtype",
            T::TanyFound => "TanyFound",
            T::ConsistentConstructAbstractFinal => "ConsistentConstructAbstractFinal",
            T::DynamicMethodCall => "DynamicMethodCall",
            T::DynamicFunctionCall => "DynamicFunctionCall",
            T::DynamicArrayAccess => "DynamicArrayAccess",
            T::SealedNotOverride => "SealedNotOverride",
            T::DynamicPropertyAccess => "DynamicPropertyAccess",
            T::RedundantRequireThisAs => "RedundantRequireThisAs",
            T::DynamicReturn => "DynamicReturn",
            T::ReadonlyPropertyOverride => "ReadonlyPropertyOverride",
            T::RedundantConcurrent => "RedundantConcurrent",
        }
        .to_string()
    }

    /// `pp` (`[@@deriving show { with_path = false }]`)
    pub fn pp(fmt: &mut dyn std::fmt::Write, t: T) -> std::fmt::Result {
        fmt.write_str(&show(t))
    }

    /// `compare` (`[@@deriving ord]`): by the order of the constructors,
    /// which is the order of the codes.
    pub fn compare(x: T, y: T) -> std::cmp::Ordering {
        to_enum(x).cmp(&to_enum(y))
    }
}

/// `Error_codes.GlobalAccessCheck`
pub mod global_access_check {
    /// `Error_codes.GlobalAccessCheck.t` (its constructors are `oxidized::error_codes::GlobalAccessCheck`'s)
    pub use oxidized::error_codes::GlobalAccessCheck as T;

    /// `to_enum` (`[@@deriving enum]`): the code of an error.
    pub fn to_enum(t: T) -> isize {
        // The discriminants of `oxidized::error_codes::GlobalAccessCheck` are the
        // `[@value]`s of the OCaml.
        t as isize
    }

    /// `of_enum` (`[@@deriving enum]`): the error that has this code.
    pub fn of_enum(i: isize) -> Option<T> {
        Some(match i {
            11001 => T::DefiniteGlobalWrite,
            11002 => T::PossibleGlobalWriteViaReference,
            11003 => T::PossibleGlobalWriteViaFunctionCall,
            11004 => T::DefiniteGlobalRead,
            _ => return None,
        })
    }

    /// `min` (`[@@deriving enum]`): the smallest code.
    pub const MIN: isize = 11001;

    /// `max` (`[@@deriving enum]`): the largest code.
    pub const MAX: isize = 11004;

    /// `show` (`[@@deriving show { with_path = false }]`): the name of the
    /// OCaml constructor.
    pub fn show(t: T) -> String {
        match t {
            T::DefiniteGlobalWrite => "DefiniteGlobalWrite",
            T::PossibleGlobalWriteViaReference => "PossibleGlobalWriteViaReference",
            T::PossibleGlobalWriteViaFunctionCall => "PossibleGlobalWriteViaFunctionCall",
            T::DefiniteGlobalRead => "DefiniteGlobalRead",
        }
        .to_string()
    }

    /// `pp` (`[@@deriving show { with_path = false }]`)
    pub fn pp(fmt: &mut dyn std::fmt::Write, t: T) -> std::fmt::Result {
        fmt.write_str(&show(t))
    }

    pub fn err_code(t: T) -> isize {
        to_enum(t)
    }
}

/// `module Warning_set = Stdlib.Set.Make (Warning)`
pub mod warning_set {
    /// `Warning_set.t`, ordered as `Warning.compare` orders the codes.
    pub type T = std::collections::BTreeSet<super::Warning>;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn to_enum_of_enum_round_trip() {
        for i in -1..13000 {
            if let Some(t) = parsing::of_enum(i) {
                assert_eq!(parsing::to_enum(t), i);
            }
            if let Some(t) = naming::of_enum(i) {
                assert_eq!(naming::to_enum(t), i);
            }
            if let Some(t) = nast_check::of_enum(i) {
                assert_eq!(nast_check::to_enum(t), i);
            }
            if let Some(t) = typing::of_enum(i) {
                assert_eq!(typing::to_enum(t), i);
            }
            if let Some(t) = warning::of_enum(i) {
                assert_eq!(warning::to_enum(t), i);
            }
            if let Some(t) = global_access_check::of_enum(i) {
                assert_eq!(global_access_check::to_enum(t), i);
            }
        }
    }

    #[test]
    fn codes() {
        assert_eq!(typing::of_enum(0), Some(Typing::InternalError));
        assert_eq!(typing::of_enum(4001), None);
        assert_eq!(typing::err_code(Typing::UninstantiableClass), 4002);
        assert_eq!(naming::of_enum(2042), Some(Naming::StartWithT));
        assert_eq!(naming::show(Naming::StartWithT), "StartWith_T");
        assert_eq!(parsing::MIN, 1001);
        assert_eq!(parsing::MAX, 1009);
        assert_eq!(typing::MIN, 0);
        assert_eq!(warning::of_enum(12002), None);
        assert_eq!(
            warning::compare(Warning::SketchyEquality, Warning::NonDisjointCheck),
            std::cmp::Ordering::Less
        );
        assert_eq!(
            global_access_check::err_code(GlobalAccessCheck::DefiniteGlobalRead),
            11004
        );
    }
}
