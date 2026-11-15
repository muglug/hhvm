// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `Naming_special_names.UserAttributes.as_map`
//! (`naming/naming_special_names.ml`) with all its fields (`contexts`,
//! `doc`, `autocomplete`): the `naming_special_names_rust` crate does not
//! have it, and `typing_attributes.rs` has only the contexts. Used by
//! autocomplete (`Autocomplete_service.autocomplete_builtin_attribute`) and
//! hover (`Ide_hover`).
//!
//! Transcribed from the `.ml` (the test below checks every name against the
//! `.ml`); the contexts are the `AttributeKinds` strings.

/// `attr_info`, with the key of the map.
#[derive(Clone, Copy, Debug)]
pub struct AttrInfo {
    pub name: &'static str,
    pub contexts: &'static [&'static str],
    pub doc: &'static str,
    pub autocomplete: bool,
}

/// `as_map`, in the order of its keys (`S_map.elements`, `S_map.iter`).
pub static AS_MAP: &[AttrInfo] = &[
    AttrInfo { name: "__AcceptDisposable", contexts: &["\\HH\\ParameterAttribute"], doc: "Allows passing values that implement `IDisposable` or `IAsyncDisposable`. Normally these values cannot be passed to functions.\n\nYou cannot save references to `__AcceptDisposable` parameters, to ensure they are disposed at the end of their using block.", autocomplete: true },
    AttrInfo { name: "__AllowUncheckedEnumValues", contexts: &["\\HH\\EnumAttribute"], doc: "Opts this enum out of the enum-value check, allowing members to share a value or to have values that cannot be statically checked.", autocomplete: true },
    AttrInfo { name: "__AsioLowPri", contexts: &["\\HH\\FunctionAttribute", "\\HH\\MethodAttribute"], doc: "Marks the function as low priority. Will suspend eager execution into a low priority awaitable.", autocomplete: false },
    AttrInfo { name: "__ConsistentConstruct", contexts: &["\\HH\\ClassAttribute"], doc: "Requires all child classes to have the same constructor signature.  This allows `new static(...)` and `new $the_class_name(...)`.", autocomplete: true },
    AttrInfo { name: "__Const", contexts: &["\\HH\\ClassAttribute", "\\HH\\InstancePropertyAttribute", "\\HH\\ParameterAttribute", "\\HH\\StaticPropertyAttribute"], doc: "Marks a class or property as immutable. When applied to a class, all the properties are considered `__Const`. `__Const` properties can only be set in the constructor.", autocomplete: false },
    AttrInfo { name: "__Deprecated", contexts: &["\\HH\\FunctionAttribute", "\\HH\\MethodAttribute"], doc: "Mark a function/method as deprecated.  The type checker will show an error at call sites, and a runtime notice is raised if this function/method is called.\n\nThe optional second argument specifies a sampling rate for raising notices at runtime. If the sampling rate is 100, a notice is only raised every 1/100 calls. If omitted, the default sampling rate is 1 (i.e. all calls raise notices). To disable runtime notices, use a sampling rate of 0.", autocomplete: true },
    AttrInfo { name: "__DisableTypecheckerInternal", contexts: &["\\HH\\FunctionAttribute", "\\HH\\MethodAttribute"], doc: "Disables type checking of a function body or method. This is only useful for debugging typechecker performance. The typechecker will discard the body and immediately report an internal error.", autocomplete: false },
    AttrInfo { name: "__Docs", contexts: &["\\HH\\ClassAttribute", "\\HH\\EnumAttribute", "\\HH\\EnumClassAttribute", "\\HH\\TypeAliasAttribute"], doc: "Shows the linked URL when hovering over this type.", autocomplete: true },
    AttrInfo { name: "__DynamicallyCallable", contexts: &["\\HH\\FunctionAttribute", "\\HH\\MethodAttribute"], doc: "Allows this function/method to be called dynamically, based on a string of its name.  HHVM will warn or error (depending on settings) on dynamic calls to functions without this attribute.\n\nSee also `HH\\dynamic_fun()` and `HH\\dynamic_class_meth()`.", autocomplete: true },
    AttrInfo { name: "__DynamicallyConstructible", contexts: &["\\HH\\ClassAttribute"], doc: "Allows this class to be instantiated dynamically, based on a string of its name. HHVM will warn or error (depending on settings) on dynamic instantiations without this attribute.", autocomplete: true },
    AttrInfo { name: "__DynamicallyReferenced", contexts: &["\\HH\\ClassAttribute"], doc: "Allows a user to get a pointer to this class from a string using `HH\\classname_to_class()`. HHVM will raise a notice if this attribute is not present. For migration, this can also be set to soft logging by passing an integer sample rate (1 of N) as an argument.", autocomplete: true },
    AttrInfo { name: "__EnableMethodTraitDiamond", contexts: &["\\HH\\ClassAttribute"], doc: "Allows a trait to be `use`d more than once. This is useful in large class hierarchies, where you can end up using the same trait on via multiple paths, producing 'diamond inheritance'.\n\nThis requires methods to unambiguous: each method definition must occur in exactly one trait.", autocomplete: true },
    AttrInfo { name: "__EnableUnstableFeatures", contexts: &["\\HH\\FileAttribute"], doc: "Enables unstable or preview features of Hack.\n\nUnstable features can only run when HHVM has `Hack.Lang.AllowUnstableFeatures` set. This allows local experimentation without using the feature in production.\n\nWhen a feature enters preview, `__EnableUnstableFeatures` is still required but HHVM will allow the code to run.", autocomplete: true },
    AttrInfo { name: "__Enforceable", contexts: &["\\HH\\TypeConstantAttribute", "\\HH\\TypeParameterAttribute"], doc: "Ensures that this type is enforceable. Enforceable types can be used with `is` and `as`. This forbids usage of function types and erased (not reified) generics.", autocomplete: true },
    AttrInfo { name: "__EntryPoint", contexts: &["\\HH\\FunctionAttribute"], doc: "Execution of the program will start here. This only applies in the first file executed, `__EntryPoint` in required or autoloaded files has no effect.", autocomplete: true },
    AttrInfo { name: "__EnumClass", contexts: &["\\HH\\ClassAttribute", "\\HH\\EnumClassAttribute"], doc: "Allows initializing class constants with class instances (not just constant expressions). Used when desugaring `enum class`.", autocomplete: false },
    AttrInfo { name: "__Explicit", contexts: &["\\HH\\TypeParameterAttribute"], doc: "Requires callers to explicitly specify this type.\n\nNormally Hack allows generics to be inferred at the call site.", autocomplete: true },
    AttrInfo { name: "__GatedByFeatureFlag", contexts: &["\\HH\\ClassAttribute", "\\HH\\TypeAliasAttribute", "\\HH\\FunctionAttribute"], doc: "Gates this declaration behind an unstable feature flag. Users must enable the feature to reference this declaration.", autocomplete: false },
    AttrInfo { name: "__HasReifiedParent", contexts: &[], doc: "Marks a class as extending a class that uses reified generics. This is an internal attribute used for byte compilation, and is banned in user code.", autocomplete: false },
    AttrInfo { name: "__IgnoreReadonlyError", contexts: &["\\HH\\ParameterAttribute"], doc: "Allows passing function values that are non-readonly even if a readonly function is expected.", autocomplete: false },
    AttrInfo { name: "__ImplementedBy", contexts: &["\\HH\\MethodAttribute"], doc: "Specifies that this method is implemented by a specific top-level function. Only valid in .hhi files.", autocomplete: true },
    AttrInfo { name: "__LSB", contexts: &["\\HH\\StaticPropertyAttribute"], doc: "Marks this property as implicitly redeclared on all subclasses. This ensures each subclass has its own value for the property.", autocomplete: true },
    AttrInfo { name: "__LateInit", contexts: &["\\HH\\InstancePropertyAttribute", "\\HH\\StaticPropertyAttribute"], doc: "Marks a property as late initialized. Normally properties are required to be initialized in the constructor.", autocomplete: true },
    AttrInfo { name: "__Memoize", contexts: &["\\HH\\FunctionAttribute", "\\HH\\MethodAttribute"], doc: "Cache the return values from this function/method. Calls with the same arguments will return the cached value.\n\nCaching is per-request and shared between subclasses (see also `__MemoizeLSB`).", autocomplete: true },
    AttrInfo { name: "__MemoizeLSB", contexts: &["\\HH\\MethodAttribute"], doc: "Cache the return values from this method. Calls with the same arguments will return the cached value.\n\nCaching is per-request and has Late Static Binding, so subclasses do not share the cache.", autocomplete: true },
    AttrInfo { name: "__MockClass", contexts: &["\\HH\\ClassAttribute"], doc: "Allows subclasses of final classes and overriding of final methods. This is useful for writing mock classes.\n\nYou cannot use this to subclass `vec`, `keyset`, `dict`, `Vector`, `Map` or `Set`.", autocomplete: false },
    AttrInfo { name: "__ModuleLevelTrait", contexts: &["\\HH\\ClassAttribute"], doc: "Consider the trait to belong to the module where it is defined, rather than to the module of the class that uses it.", autocomplete: false },
    AttrInfo { name: "__NEVER_INLINE", contexts: &["\\HH\\FunctionAttribute", "\\HH\\MethodAttribute"], doc: "Instructs HHVM to never inline this function. Only used for testing HHVM.\n\nSee also `__ALWAYS_INLINE`.", autocomplete: false },
    AttrInfo { name: "__NativeData", contexts: &["\\HH\\ClassAttribute"], doc: "Associates this class with a native data type (usually a C++ class). When instantiating this class, the corresponding native object will also be allocated.", autocomplete: false },
    AttrInfo { name: "__NeedsConcrete", contexts: &["\\HH\\MethodAttribute"], doc: "Indicates that the method can only be called on concrete classes. Inside the method, `static` refers to a concrete class.", autocomplete: false },
    AttrInfo { name: "__Newable", contexts: &["\\HH\\TypeParameterAttribute"], doc: "Ensures the class can be constructed.\n\nThis forbids abstract classes, and ensures that the constructor has a consistent signature. Classes must use `__ConsistentConstruct` or be final.", autocomplete: true },
    AttrInfo { name: "__NoAutoBound", contexts: &["\\HH\\TypeParameterAttribute"], doc: "Locally disable addition of supportdyn<mixed> bound.", autocomplete: false },
    AttrInfo { name: "__NoAutoDynamic", contexts: &["\\HH\\FunctionAttribute", "\\HH\\ClassAttribute", "\\HH\\MethodAttribute", "\\HH\\TypeAliasAttribute"], doc: "Locally disable implicit pessimisation.", autocomplete: false },
    AttrInfo { name: "__NoAutoLikes", contexts: &["\\HH\\FunctionAttribute", "\\HH\\MethodAttribute", "\\HH\\StaticPropertyAttribute", "\\HH\\InstancePropertyAttribute", "\\HH\\ParameterAttribute", "\\HH\\LambdaAttribute"], doc: "Locally disable addition of ~ types.", autocomplete: false },
    AttrInfo { name: "__NoDisjointUnion", contexts: &["\\HH\\TypeParameterAttribute"], doc: "Requires this type parameter to NOT have a union type where the types in the union are disjoint from each other, e.g., `(int | string)`. This prevents Hack from inferring completely unrelated types.", autocomplete: true },
    AttrInfo { name: "__NoFlatten", contexts: &[], doc: "Instructs hhbbc to never inline this trait into classes that use it. Used for testing hhbbc optimizations.", autocomplete: false },
    AttrInfo { name: "__NoSupportDynamicType", contexts: &["\\HH\\FunctionAttribute", "\\HH\\ClassAttribute", "\\HH\\MethodAttribute", "\\HH\\LambdaAttribute", "\\HH\\EnumClassAttribute"], doc: "Disable implicit SupportDynamicType for this declaration", autocomplete: false },
    AttrInfo { name: "__NonDisjoint", contexts: &["\\HH\\TypeParameterAttribute"], doc: "Requires this type parameter to have some overlap with the other `<<__NonDisjoint>>` type parameters.\n\nThis prevents Hack inferring completely unrelated types. For example, this allows the typechecker to warn on `C\\contains(vec[1], \"foo\")`.", autocomplete: true },
    AttrInfo { name: "__Overlapping", contexts: &["\\HH\\FunctionAttribute", "\\HH\\MethodAttribute"], doc: "Requires these type parameters to have some overlap with each other.\n\nThis prevents Hack inferring completely unrelated types. For example, this allows the typechecker to warn on `C\\contains(vec[1], \"foo\")`.", autocomplete: true },
    AttrInfo { name: "__Override", contexts: &["\\HH\\MethodAttribute"], doc: "Ensures there's a parent method being overridden.", autocomplete: true },
    AttrInfo { name: "__PHPStdLib", contexts: &["\\HH\\ClassAttribute", "\\HH\\FunctionAttribute", "\\HH\\MethodAttribute"], doc: "Ignore this built-in function or class, so the type checker errors if code uses it. This only applies to code in .hhi files by default, but can apply everywhere with `deregister_php_stdlib`.", autocomplete: false },
    AttrInfo { name: "__PackageOverride", contexts: &["\\HH\\FileAttribute"], doc: "Overrides the PACKAGES.toml declaration, grouping the file into the specified package.", autocomplete: true },
    AttrInfo { name: "__ProvenanceSkipFrame", contexts: &["\\HH\\FunctionAttribute", "\\HH\\MethodAttribute", "\\HH\\LambdaAttribute"], doc: "Don't track Hack arrays created by this function. This is useful when migrating code from PHP arrays to Hack arrays.", autocomplete: false },
    AttrInfo { name: "__Reifiable", contexts: &["\\HH\\TypeConstantAttribute"], doc: "Requires this type to be reifiable. This bans PHP arrays (varray and darray).", autocomplete: true },
    AttrInfo { name: "__Reified", contexts: &[], doc: "Marks a function as taking reified generics. This is an internal attribute used for byte compilation, and is banned in user code.", autocomplete: false },
    AttrInfo { name: "__RequireDynamic", contexts: &["\\HH\\TypeParameterAttribute"], doc: "Marks this type parameter as required to be `dynamic`.", autocomplete: false },
    AttrInfo { name: "__RequirePackage", contexts: &["\\HH\\FunctionAttribute", "\\HH\\MethodAttribute"], doc: "This function will only execute if the target package is loaded in the current deployment (invariant_violation otherwise). Hack will enforce this constraint on callers by raising an error unless the caller has this package.", autocomplete: true },
    AttrInfo { name: "__ReturnDisposable", contexts: &["\\HH\\FunctionAttribute", "\\HH\\MethodAttribute", "\\HH\\LambdaAttribute"], doc: "Allows a function/method to return a value that implements `IDisposable` or `IAsyncDisposable`. The function must return a fresh disposable value by either instantiating a class or  returning a value from another method/function marked `__ReturnDisposable`.", autocomplete: true },
    AttrInfo { name: "__SafeForGlobalAccessCheck", contexts: &["\\HH\\StaticPropertyAttribute"], doc: "Marks this global variable as safe from mutation. This ensures the global_access_check does NOT raise errors/warnings from writing to this global variable.", autocomplete: false },
    AttrInfo { name: "__Sealed", contexts: &["\\HH\\ClassAttribute", "\\HH\\EnumClassAttribute", "\\HH\\EnumAttribute", "\\HH\\MethodAttribute"], doc: "Only the named classes can extend this class or interface, or override this method. Child classes may still be extended unless they are marked `final`.", autocomplete: true },
    AttrInfo { name: "__SimpliHack", contexts: &["\\HH\\ClassAttribute", "\\HH\\ClassConstantAttribute", "\\HH\\EnumAttribute", "\\HH\\EnumClassAttribute", "\\HH\\FileAttribute", "\\HH\\FunctionAttribute", "\\HH\\InstancePropertyAttribute", "\\HH\\LambdaAttribute", "\\HH\\MethodAttribute", "\\HH\\ModuleAttribute", "\\HH\\ParameterAttribute", "\\HH\\StaticPropertyAttribute", "\\HH\\TypeAliasAttribute", "\\HH\\TypeConstantAttribute", "\\HH\\TypeParameterAttribute"], doc: "Demo for SimpliHack", autocomplete: false },
    AttrInfo { name: "__Soft", contexts: &["\\HH\\InstancePropertyAttribute", "\\HH\\ParameterAttribute", "\\HH\\StaticPropertyAttribute", "\\HH\\TypeParameterAttribute"], doc: "A runtime type mismatch on this parameter/property will not throw a TypeError/Error. This is useful for migrating partial code where you're unsure about the type.\n\nThe type checker will ignore this attribute, so your code will still get type checked. If the type is wrong at runtime, a warning will be logged and code execution will continue.", autocomplete: true },
    AttrInfo { name: "__SoftInternal", contexts: &["\\HH\\FunctionAttribute", "\\HH\\ClassAttribute", "\\HH\\MethodAttribute", "\\HH\\InstancePropertyAttribute", "\\HH\\StaticPropertyAttribute", "\\HH\\ParameterAttribute", "\\HH\\EnumAttribute", "\\HH\\EnumClassAttribute"], doc: "Instead of throwing an exception upon a module boundary violation at this symbol, logs a warning instead.", autocomplete: false },
    AttrInfo { name: "__SoftRequirePackage", contexts: &["\\HH\\FunctionAttribute", "\\HH\\MethodAttribute"], doc: "Migration attribute for `__RequirePackage`. Raises a notice with optional sample rate if the target package is not loaded. Does not allow this function to call other functions from the target package.", autocomplete: true },
    AttrInfo { name: "__StrictSwitch", contexts: &["\\HH\\FunctionAttribute", "\\HH\\MethodAttribute"], doc: "Enables strict switch checking for all switches in function or method.", autocomplete: true },
    AttrInfo { name: "__SupportDynamicType", contexts: &["\\HH\\FunctionAttribute", "\\HH\\ClassAttribute", "\\HH\\MethodAttribute", "\\HH\\LambdaAttribute", "\\HH\\EnumClassAttribute"], doc: "Marks methods and functions that can be called on a receiver of type `dynamic` with `dynamic` arguments.", autocomplete: false },
    AttrInfo { name: "__TestsBypassVisibility", contexts: &["\\HH\\ClassAttribute", "\\HH\\MethodAttribute", "\\HH\\InstancePropertyAttribute", "\\HH\\StaticPropertyAttribute"], doc: "Allows this member to be accessed as public from test contexts. When applied to an internal class, the class becomes visible from test contexts.", autocomplete: true },
    AttrInfo { name: "__UNSAFE_AllowMultipleInstantiations", contexts: &["\\HH\\ClassAttribute"], doc: "CLOWNY. Allows implementing this interface with multiple instantiations, e.g. `implements I<int>, I<string>`.", autocomplete: true },
    AttrInfo { name: "__Warn", contexts: &["\\HH\\TypeParameterAttribute"], doc: "Ensures that incorrect reified types are a warning rather than error.\n\nThis is intended to help gradually migrate code to reified types.", autocomplete: true },
];

/// `S_map.find_opt name as_map`
pub fn find(name: &str) -> Option<&'static AttrInfo> {
    AS_MAP
        .binary_search_by(|a| a.name.as_bytes().cmp(name.as_bytes()))
        .ok()
        .map(|i| &AS_MAP[i])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sorted_and_complete() {
        assert_eq!(AS_MAP.len(), 59);
        for w in AS_MAP.windows(2) {
            assert!(w[0].name.as_bytes() < w[1].name.as_bytes());
        }
        let ml = include_str!("../../naming/naming_special_names.ml");
        for a in AS_MAP {
            assert!(ml.contains(&format!("\"{}\"", a.name)), "{}", a.name);
        }
        assert_eq!(
            find("__Override").map(|a| a.doc),
            Some("Ensures there's a parent method being overridden.")
        );
        assert!(find("__Nope").is_none());
    }
}
