// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_defs_flags.ml`. See `hh/PORTING.md`.
//!
//! The flag types are those of `oxidized::typing_defs_flags`, re-exported
//! here: `Fun.t` is [`FunTypeFlags`], `FunParam.t` is [`FunParamFlags`] and
//! `ClassElt.t` is [`ClassEltFlags`] (the same bits as the OCaml masks). The
//! three OCaml modules are [`fun`], [`fun_param`] and [`class_elt`], with the
//! functions of the `.mli` on those types; flags are `Copy` and are passed by
//! value.
//!
//! `[@@deriving eq, ord]` are `equal` and `compare` (and `==`, `Ord`: the
//! order of the bits as an integer, as in OCaml); `[@@deriving hash]` is
//! `Hash`.
//!
//! The `pp` functions take a `Format.formatter` and are not here (see
//! `crate::typing_defs_core::pp`).

pub use oxidized::typing_defs_flags::*;

pub mod fun {
    use oxidized::ast_defs;
    pub use oxidized::typing_defs_flags::fun::Fun;

    use super::FunTypeFlags;

    /// `Typing_defs_flags.Fun.t`
    pub type T = FunTypeFlags;

    /// `[@@deriving eq]`
    pub fn equal(a: T, b: T) -> bool {
        a == b
    }

    /// `[@@deriving ord]`
    pub fn compare(a: T, b: T) -> std::cmp::Ordering {
        a.cmp(&b)
    }

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub struct Record {
        pub return_disposable: bool,
        pub async_: bool,
        pub generator: bool,
        pub fun_kind: ast_defs::FunKind,
        pub is_function_pointer: bool,
        pub returns_readonly: bool,
        pub readonly_this: bool,
        pub support_dynamic_type: bool,
        pub is_memoized: bool,
        pub variadic: bool,
        pub named_variadic: bool,
    }

    /// `is_set mask`
    fn is_set(bit: T, flags: T) -> bool {
        flags.intersects(bit)
    }

    /// `set_bit mask`
    fn set_bit(bit: T, value: bool, mut flags: T) -> T {
        flags.set(bit, value);
        flags
    }

    pub fn return_disposable(t: T) -> bool {
        is_set(T::RETURN_DISPOSABLE, t)
    }

    pub fn set_return_disposable(value: bool, t: T) -> T {
        set_bit(T::RETURN_DISPOSABLE, value, t)
    }

    pub fn async_(t: T) -> bool {
        is_set(T::ASYNC, t)
    }

    pub fn set_async(value: bool, t: T) -> T {
        set_bit(T::ASYNC, value, t)
    }

    pub fn generator(t: T) -> bool {
        is_set(T::GENERATOR, t)
    }

    pub fn set_generator(value: bool, t: T) -> T {
        set_bit(T::GENERATOR, value, t)
    }

    fn fun_kind_to_flags(kind: ast_defs::FunKind) -> T {
        match kind {
            ast_defs::FunKind::FSync => T::empty(),
            ast_defs::FunKind::FAsync => T::ASYNC,
            ast_defs::FunKind::FGenerator => T::GENERATOR,
            ast_defs::FunKind::FAsyncGenerator => T::ASYNC | T::GENERATOR,
        }
    }

    pub fn fun_kind(t: T) -> ast_defs::FunKind {
        match (async_(t), generator(t)) {
            (false, false) => ast_defs::FunKind::FSync,
            (true, false) => ast_defs::FunKind::FAsync,
            (false, true) => ast_defs::FunKind::FGenerator,
            (true, true) => ast_defs::FunKind::FAsyncGenerator,
        }
    }

    pub fn is_function_pointer(t: T) -> bool {
        is_set(T::IS_FUNCTION_POINTER, t)
    }

    pub fn set_is_function_pointer(value: bool, t: T) -> T {
        set_bit(T::IS_FUNCTION_POINTER, value, t)
    }

    pub fn returns_readonly(t: T) -> bool {
        is_set(T::RETURNS_READONLY, t)
    }

    pub fn set_returns_readonly(value: bool, t: T) -> T {
        set_bit(T::RETURNS_READONLY, value, t)
    }

    /// Does function captures only readonly values?
    /// For methods: is the this parameter readonly?
    pub fn readonly_this(t: T) -> bool {
        is_set(T::READONLY_THIS, t)
    }

    /// Mark the function type as capturing only readonly values,
    /// or for method definitions, the this parameter is readonly
    pub fn set_readonly_this(value: bool, t: T) -> T {
        set_bit(T::READONLY_THIS, value, t)
    }

    pub fn support_dynamic_type(t: T) -> bool {
        is_set(T::SUPPORT_DYNAMIC_TYPE, t)
    }

    pub fn set_support_dynamic_type(value: bool, t: T) -> T {
        set_bit(T::SUPPORT_DYNAMIC_TYPE, value, t)
    }

    pub fn is_memoized(t: T) -> bool {
        is_set(T::IS_MEMOIZED, t)
    }

    pub fn set_is_memoized(value: bool, t: T) -> T {
        set_bit(T::IS_MEMOIZED, value, t)
    }

    pub fn variadic(t: T) -> bool {
        is_set(T::VARIADIC, t)
    }

    pub fn set_variadic(value: bool, t: T) -> T {
        set_bit(T::VARIADIC, value, t)
    }

    pub fn named_variadic(t: T) -> bool {
        is_set(T::NAMED_VARIADIC, t)
    }

    pub fn set_named_variadic(value: bool, t: T) -> T {
        set_bit(T::NAMED_VARIADIC, value, t)
    }

    pub fn make(
        kind: ast_defs::FunKind,
        return_disposable: bool,
        returns_readonly: bool,
        readonly_this: bool,
        support_dynamic_type: bool,
        is_memoized: bool,
        variadic: bool,
        named_variadic: bool,
    ) -> T {
        let t = fun_kind_to_flags(kind);
        let t = set_return_disposable(return_disposable, t);
        let t = set_returns_readonly(returns_readonly, t);
        let t = set_readonly_this(readonly_this, t);
        let t = set_support_dynamic_type(support_dynamic_type, t);
        let t = set_is_memoized(is_memoized, t);
        let t = set_variadic(variadic, t);
        set_named_variadic(named_variadic, t)
    }

    pub fn default() -> T {
        T::empty()
    }

    pub fn as_record(t: T) -> Record {
        Record {
            return_disposable: return_disposable(t),
            async_: async_(t),
            generator: generator(t),
            fun_kind: fun_kind(t),
            is_function_pointer: is_function_pointer(t),
            returns_readonly: returns_readonly(t),
            readonly_this: readonly_this(t),
            support_dynamic_type: support_dynamic_type(t),
            is_memoized: is_memoized(t),
            variadic: variadic(t),
            named_variadic: named_variadic(t),
        }
    }

    /// `pp_record` (`[@@deriving show]` of the record) on `as_record t`.
    pub fn show(_t: T) -> String {
        todo!(
            "Typing_defs_flags.Fun.show: needs a port of OCaml's Format (boxes and break hints)"
        )
    }
}

pub mod fun_param {
    pub use oxidized::typing_defs_flags::fun_param::FunParam;

    use super::FunParamFlags;

    /// `Typing_defs_flags.FunParam.t`
    pub type T = FunParamFlags;

    /// `[@@deriving eq]`
    pub fn equal(a: T, b: T) -> bool {
        a == b
    }

    /// `[@@deriving ord]`
    pub fn compare(a: T, b: T) -> std::cmp::Ordering {
        a.cmp(&b)
    }

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub struct Record {
        pub accept_disposable: bool,
        pub inout: bool,
        /// Parameter is marked optional in function type
        pub is_optional: bool,
        /// Parameter is marked readonly in function type
        pub readonly: bool,
        pub ignore_readonly_error: bool,
        pub splat: bool,
        /// Parameter is marked named in function type
        pub named: bool,
    }

    /// `is_set mask`
    fn is_set(bit: T, flags: T) -> bool {
        flags.intersects(bit)
    }

    /// `set_bit mask`
    fn set_bit(bit: T, value: bool, mut flags: T) -> T {
        flags.set(bit, value);
        flags
    }

    pub fn accept_disposable(t: T) -> bool {
        is_set(T::ACCEPT_DISPOSABLE, t)
    }

    pub fn inout(t: T) -> bool {
        is_set(T::INOUT, t)
    }

    pub fn is_optional(t: T) -> bool {
        is_set(T::IS_OPTIONAL, t)
    }

    pub fn readonly(t: T) -> bool {
        is_set(T::READONLY, t)
    }

    pub fn ignore_readonly_error(t: T) -> bool {
        is_set(T::IGNORE_READONLY_ERROR, t)
    }

    pub fn splat(t: T) -> bool {
        is_set(T::SPLAT, t)
    }

    pub fn named(t: T) -> bool {
        is_set(T::NAMED, t)
    }

    pub fn set_accept_disposable(value: bool, t: T) -> T {
        set_bit(T::ACCEPT_DISPOSABLE, value, t)
    }

    pub fn set_inout(value: bool, t: T) -> T {
        set_bit(T::INOUT, value, t)
    }

    pub fn set_is_optional(value: bool, t: T) -> T {
        set_bit(T::IS_OPTIONAL, value, t)
    }

    pub fn set_readonly(value: bool, t: T) -> T {
        set_bit(T::READONLY, value, t)
    }

    pub fn set_ignore_readonly_error(value: bool, t: T) -> T {
        set_bit(T::IGNORE_READONLY_ERROR, value, t)
    }

    pub fn set_splat(value: bool, t: T) -> T {
        set_bit(T::SPLAT, value, t)
    }

    pub fn set_named(value: bool, t: T) -> T {
        set_bit(T::NAMED, value, t)
    }

    pub fn make(
        inout: bool,
        accept_disposable: bool,
        is_optional: bool,
        readonly: bool,
        ignore_readonly_error: bool,
        splat: bool,
        named: bool,
    ) -> T {
        let t = T::empty();
        let t = set_inout(inout, t);
        let t = set_accept_disposable(accept_disposable, t);
        let t = set_is_optional(is_optional, t);
        let t = set_readonly(readonly, t);
        let t = set_ignore_readonly_error(ignore_readonly_error, t);
        let t = set_splat(splat, t);
        set_named(named, t)
    }

    pub fn as_record(t: T) -> Record {
        Record {
            accept_disposable: accept_disposable(t),
            inout: inout(t),
            is_optional: is_optional(t),
            readonly: readonly(t),
            ignore_readonly_error: ignore_readonly_error(t),
            splat: splat(t),
            named: named(t),
        }
    }

    pub fn default() -> T {
        T::empty()
    }

    /// `pp_record` (`[@@deriving show]` of the record) on `as_record t`.
    pub fn show(_t: T) -> String {
        todo!(
            "Typing_defs_flags.FunParam.show: needs a port of OCaml's Format (boxes and break hints)"
        )
    }
}

pub mod class_elt {
    use oxidized::s_map::SMap;
    pub use oxidized::typing_defs_flags::class_elt::ClassElt;
    use oxidized::xhp_attribute;
    use oxidized::xhp_attribute::XhpAttribute;

    use super::ClassEltFlags;

    /// `Typing_defs_flags.ClassElt.t`
    pub type T = ClassEltFlags;

    /// `ClassElt.Field`: a field is its bit mask (`to_bit_mask`), a constant
    /// of [`ClassEltFlags`] (`Field.Abstract` is `ClassEltFlags::ABSTRACT`).
    mod field {
        use super::ClassEltFlags;
        use super::XhpAttribute;
        use super::xhp_attribute;

        pub type T = ClassEltFlags;

        /// The fields in the order of their definition, with what
        /// `[@@deriving show { with_path = false }]` prints.
        pub const ALL: [(T, &str); 17] = [
            (T::ABSTRACT, "Abstract"),
            (T::FINAL, "Final"),
            (T::SUPERFLUOUS_OVERRIDE, "SuperfluousOverride"),
            (T::LSB, "Lsb"),
            (T::SYNTHESIZED, "Synthesized"),
            (T::CONST, "Const"),
            (T::LATEINIT, "Lateinit"),
            (T::DYNAMICALLYCALLABLE, "Dynamicallycallable"),
            (T::SUPPORT_DYNAMIC_TYPE, "SupportDynamicType"),
            (T::XA_HAS_DEFAULT, "XaHasDefault"),
            (T::XA_TAG_REQUIRED, "XaTagRequired"),
            (T::XA_TAG_LATEINIT, "XaTagLateinit"),
            (T::READONLY_PROP_OR_NEEDS_CONCRETE, "ReadonlyPropOrNeedsConcrete"),
            (T::NEEDS_INIT, "NeedsInit"),
            (T::SAFE_GLOBAL_VARIABLE, "SafeGlobalVariable"),
            (T::NO_AUTO_LIKES, "NoAutoLikes"),
            (T::TESTS_BYPASS_VISIBILITY, "TestsBypassVisibility"),
        ];

        pub fn list_to_bit_mask(fields: &[T]) -> T {
            fields.iter().fold(T::empty(), |acc, field| acc | *field)
        }

        // The three XA bits are used to encode optional XHP attr.
        // Set 1<<10 (0x400) if xa_has_default=true
        // Then encode xa_tag as follows:
        //   Some Required: 1<<11 (0x0800)
        //   Some lateinit: 1<<12 (0x1000)
        //   None:          1<<11 | 1<<12 (0x1800)
        // If attr is not present at all, then masking with 0x1800 will produce zero.

        pub const XHP_ATTR_FIELDS: [T; 3] =
            [T::XA_HAS_DEFAULT, T::XA_TAG_LATEINIT, T::XA_TAG_REQUIRED];

        pub fn of_xhp_tag(tag: xhp_attribute::Tag) -> T {
            match tag {
                xhp_attribute::Tag::Required => T::XA_TAG_REQUIRED,
                xhp_attribute::Tag::LateInit => T::XA_TAG_LATEINIT,
            }
        }

        pub fn to_xhp_tag(field: T) -> xhp_attribute::Tag {
            if field == T::XA_TAG_REQUIRED {
                xhp_attribute::Tag::Required
            } else if field == T::XA_TAG_LATEINIT {
                xhp_attribute::Tag::LateInit
            } else {
                panic!("cannot convert field to xhp attribute tag")
            }
        }

        pub fn equal_xhp_tag(field: T, tag: xhp_attribute::Tag) -> bool {
            match tag {
                xhp_attribute::Tag::Required => field == T::XA_TAG_REQUIRED,
                xhp_attribute::Tag::LateInit => field == T::XA_TAG_LATEINIT,
            }
        }

        pub fn of_xhp_attr(xa: Option<XhpAttribute>) -> Vec<T> {
            match xa {
                None => vec![],
                Some(XhpAttribute {
                    has_default: xa_has_default,
                    tag: xa_tag,
                }) => {
                    let mut tag_fields = match xa_tag {
                        None => vec![T::XA_TAG_REQUIRED, T::XA_TAG_LATEINIT],
                        Some(tag) => vec![of_xhp_tag(tag)],
                    };
                    if xa_has_default {
                        tag_fields.insert(0, T::XA_HAS_DEFAULT);
                        tag_fields
                    } else {
                        tag_fields
                    }
                }
            }
        }

        pub fn to_xhp_attr(fields: &[T]) -> Option<XhpAttribute> {
            if fields.is_empty() {
                None
            } else {
                // Xhp_attribute.init
                let mut xa = XhpAttribute {
                    tag: None,
                    has_default: false,
                };
                for &field in fields {
                    let update_tag = |field: T, tag: Option<xhp_attribute::Tag>| match tag {
                        None => Some(to_xhp_tag(field)),
                        Some(tag) => {
                            if equal_xhp_tag(field, tag) {
                                Some(tag)
                            } else {
                                // If both XaTagRequired and XaTagLateinit bits are set, then that's
                                // code for xa_tag = None.
                                None
                            }
                        }
                    };
                    if field == T::XA_HAS_DEFAULT {
                        xa.has_default = true;
                    } else if field == T::XA_TAG_REQUIRED || field == T::XA_TAG_LATEINIT {
                        // Xhp_attribute.map_tag xa ~f:(update_tag field)
                        xa.tag = update_tag(field, xa.tag);
                    }
                }
                Some(xa)
            }
        }
    }

    fn is_set(field: field::T, flags: T) -> bool {
        flags.intersects(field)
    }

    fn set(field: field::T, value: bool, mut flags: T) -> T {
        flags.set(field, value);
        flags
    }

    pub fn is_abstract(flags: T) -> bool {
        is_set(T::ABSTRACT, flags)
    }

    pub fn is_final(flags: T) -> bool {
        is_set(T::FINAL, flags)
    }

    pub fn has_superfluous_override(flags: T) -> bool {
        is_set(T::SUPERFLUOUS_OVERRIDE, flags)
    }

    pub fn has_lsb(flags: T) -> bool {
        is_set(T::LSB, flags)
    }

    /// Whether a class element comes from a `require extends`.
    pub fn is_synthesized(flags: T) -> bool {
        is_set(T::SYNTHESIZED, flags)
    }

    pub fn is_const(flags: T) -> bool {
        is_set(T::CONST, flags)
    }

    pub fn has_lateinit(flags: T) -> bool {
        is_set(T::LATEINIT, flags)
    }

    pub fn is_dynamicallycallable(flags: T) -> bool {
        is_set(T::DYNAMICALLYCALLABLE, flags)
    }

    pub fn supports_dynamic_type(flags: T) -> bool {
        is_set(T::SUPPORT_DYNAMIC_TYPE, flags)
    }

    pub fn is_readonly_prop_or_needs_concrete(flags: T) -> bool {
        is_set(T::READONLY_PROP_OR_NEEDS_CONCRETE, flags)
    }

    pub fn needs_init(flags: T) -> bool {
        is_set(T::NEEDS_INIT, flags)
    }

    pub fn is_safe_global_variable(flags: T) -> bool {
        is_set(T::SAFE_GLOBAL_VARIABLE, flags)
    }

    pub fn is_no_auto_likes(flags: T) -> bool {
        is_set(T::NO_AUTO_LIKES, flags)
    }

    pub fn is_tests_bypass_visibility(flags: T) -> bool {
        is_set(T::TESTS_BYPASS_VISIBILITY, flags)
    }

    pub fn get_xhp_attr(flags: T) -> Option<XhpAttribute> {
        let fields: Vec<field::T> = field::XHP_ATTR_FIELDS
            .iter()
            .copied()
            .filter(|field| is_set(*field, flags))
            .collect();
        field::to_xhp_attr(&fields)
    }

    fn set_xhp_attr(xa: Option<XhpAttribute>, flags: T) -> T {
        let xhp_attr_as_flags = field::list_to_bit_mask(&field::of_xhp_attr(xa));
        let reset_xhp_attr = |flags: T| {
            let xhp_attr_mask = field::list_to_bit_mask(&field::XHP_ATTR_FIELDS);
            flags.difference(xhp_attr_mask)
        };
        reset_xhp_attr(flags) | xhp_attr_as_flags
    }

    fn to_string_map(flags: T) -> SMap<bool> {
        field::ALL
            .iter()
            .map(|(field, name)| (name.to_string(), is_set(*field, flags)))
            .collect()
    }

    /// `S_map.show Bool.pp` of the fields by name. The map is printed in a
    /// `Format` box `@[<hv 2>{ ... }@]` that never fits on a line (there are
    /// 17 bindings and the margin is 80), so every binding is on its own
    /// line, indented by 2.
    pub fn show(flags: T) -> String {
        let bindings: Vec<String> = to_string_map(flags)
            .iter()
            // The key is printed with `%S`: the names need no escaping.
            .map(|(key, data)| format!("\"{}\" -> {}", key, data))
            .collect();
        format!("{{ {} }}", bindings.join(";\n  "))
    }

    pub fn make(
        xhp_attr: Option<XhpAttribute>,
        abstract_: bool,
        final_: bool,
        superfluous_override: bool,
        lsb: bool,
        synthesized: bool,
        const_: bool,
        lateinit: bool,
        dynamicallycallable: bool,
        readonly_prop_or_needs_concrete: bool,
        support_dynamic_type: bool,
        needs_init: bool,
        safe_global_variable: bool,
        no_auto_likes: bool,
        tests_bypass_visibility: bool,
    ) -> T {
        let flags = T::empty();
        let flags = set(T::ABSTRACT, abstract_, flags);
        let flags = set(T::FINAL, final_, flags);
        let flags = set(T::SUPERFLUOUS_OVERRIDE, superfluous_override, flags);
        let flags = set(T::LSB, lsb, flags);
        let flags = set(T::SYNTHESIZED, synthesized, flags);
        let flags = set(T::CONST, const_, flags);
        let flags = set(T::LATEINIT, lateinit, flags);
        let flags = set(T::DYNAMICALLYCALLABLE, dynamicallycallable, flags);
        let flags = set_xhp_attr(xhp_attr, flags);
        let flags = set(
            T::READONLY_PROP_OR_NEEDS_CONCRETE,
            readonly_prop_or_needs_concrete,
            flags,
        );
        let flags = set(T::SUPPORT_DYNAMIC_TYPE, support_dynamic_type, flags);
        let flags = set(T::NEEDS_INIT, needs_init, flags);
        let flags = set(T::SAFE_GLOBAL_VARIABLE, safe_global_variable, flags);
        let flags = set(T::NO_AUTO_LIKES, no_auto_likes, flags);
        let flags = set(T::TESTS_BYPASS_VISIBILITY, tests_bypass_visibility, flags);
        flags
    }

    pub fn set_synthesized(flags: T) -> T {
        set(T::SYNTHESIZED, true, flags)
    }

    pub fn reset_superfluous_override(flags: T) -> T {
        set(T::SUPERFLUOUS_OVERRIDE, false, flags)
    }
}

#[cfg(test)]
mod tests {
    use oxidized::ast_defs::FunKind;
    use oxidized::xhp_attribute::Tag;
    use oxidized::xhp_attribute::XhpAttribute;

    use super::*;

    #[test]
    fn fun_bits_are_the_ocaml_masks() {
        let all = fun::make(FunKind::FAsyncGenerator, true, true, true, true, true, true, true);
        assert_eq!(
            all.bits(),
            (1 << 0) | (1 << 4) | (1 << 5) | (1 << 10) | (1 << 11) | (1 << 12) | (1 << 13)
                | (1 << 14)
                | (1 << 15)
        );
        assert_eq!(fun::set_is_function_pointer(true, fun::default()).bits(), 1 << 9);
        assert_eq!(fun::set_return_disposable(true, fun::default()).bits(), 1 << 0);
        assert_eq!(fun::set_async(true, fun::default()).bits(), 1 << 4);
        assert_eq!(fun::set_generator(true, fun::default()).bits(), 1 << 5);
        assert_eq!(fun::set_returns_readonly(true, fun::default()).bits(), 1 << 10);
        assert_eq!(fun::set_readonly_this(true, fun::default()).bits(), 1 << 11);
        assert_eq!(fun::set_support_dynamic_type(true, fun::default()).bits(), 1 << 12);
        assert_eq!(fun::set_is_memoized(true, fun::default()).bits(), 1 << 13);
        assert_eq!(fun::set_variadic(true, fun::default()).bits(), 1 << 14);
        assert_eq!(fun::set_named_variadic(true, fun::default()).bits(), 1 << 15);
        assert_eq!(fun::default().bits(), 0);
    }

    #[test]
    fn fun_accessors() {
        for kind in [
            FunKind::FSync,
            FunKind::FAsync,
            FunKind::FGenerator,
            FunKind::FAsyncGenerator,
        ] {
            let t = fun::make(kind, false, true, false, true, false, true, false);
            assert_eq!(fun::fun_kind(t), kind);
            let r = fun::as_record(t);
            assert_eq!(
                r,
                fun::Record {
                    return_disposable: false,
                    async_: matches!(kind, FunKind::FAsync | FunKind::FAsyncGenerator),
                    generator: matches!(kind, FunKind::FGenerator | FunKind::FAsyncGenerator),
                    fun_kind: kind,
                    is_function_pointer: false,
                    returns_readonly: true,
                    readonly_this: false,
                    support_dynamic_type: true,
                    is_memoized: false,
                    variadic: true,
                    named_variadic: false,
                }
            );
            assert_eq!(fun::async_(t), r.async_);
            assert_eq!(fun::generator(t), r.generator);
        }
        let t = fun::make(FunKind::FSync, true, false, true, false, true, false, true);
        assert!(fun::return_disposable(t));
        assert!(!fun::returns_readonly(t));
        assert!(fun::readonly_this(t));
        assert!(!fun::support_dynamic_type(t));
        assert!(fun::is_memoized(t));
        assert!(!fun::variadic(t));
        assert!(fun::named_variadic(t));
        assert!(!fun::is_function_pointer(t));
        // Setting and clearing a bit leaves the others alone.
        let t2 = fun::set_is_function_pointer(true, t);
        assert!(fun::is_function_pointer(t2));
        assert!(!fun::equal(t, t2));
        assert!(fun::equal(fun::set_is_function_pointer(false, t2), t));
        assert_eq!(fun::set_readonly_this(false, t).bits(), t.bits() & !(1 << 11));
        // The order is the order of the integers.
        assert_eq!(fun::compare(fun::default(), t), std::cmp::Ordering::Less);
        assert_eq!(fun::compare(t2, t), t2.bits().cmp(&t.bits()));
    }

    #[test]
    fn fun_param() {
        let all = fun_param::make(true, true, true, true, true, true, true);
        assert_eq!(
            all.bits(),
            (1 << 0) | (1 << 1) | (1 << 2) | (1 << 8) | (1 << 3) | (1 << 9) | (1 << 4)
        );
        assert_eq!(fun_param::default().bits(), 0);
        let t = fun_param::default();
        assert_eq!(fun_param::set_accept_disposable(true, t).bits(), 1 << 0);
        assert_eq!(fun_param::set_inout(true, t).bits(), 1 << 1);
        assert_eq!(fun_param::set_is_optional(true, t).bits(), 1 << 2);
        assert_eq!(fun_param::set_readonly(true, t).bits(), 1 << 8);
        assert_eq!(fun_param::set_ignore_readonly_error(true, t).bits(), 1 << 3);
        assert_eq!(fun_param::set_splat(true, t).bits(), 1 << 9);
        assert_eq!(fun_param::set_named(true, t).bits(), 1 << 4);
        // make ~inout ~accept_disposable ~is_optional ~readonly
        //   ~ignore_readonly_error ~splat ~named
        let t = fun_param::make(true, false, false, true, false, true, false);
        assert_eq!(
            fun_param::as_record(t),
            fun_param::Record {
                accept_disposable: false,
                inout: true,
                is_optional: false,
                readonly: true,
                ignore_readonly_error: false,
                splat: true,
                named: false,
            }
        );
        assert!(fun_param::inout(t));
        assert!(!fun_param::accept_disposable(t));
        assert!(!fun_param::is_optional(t));
        assert!(fun_param::readonly(t));
        assert!(!fun_param::ignore_readonly_error(t));
        assert!(fun_param::splat(t));
        assert!(!fun_param::named(t));
        assert!(fun_param::equal(fun_param::set_inout(false, fun_param::set_inout(true, all)), fun_param::set_inout(false, all)));
        assert_eq!(
            fun_param::compare(fun_param::default(), all),
            std::cmp::Ordering::Less
        );
    }

    fn class_elt_with(xhp_attr: Option<XhpAttribute>, b: bool) -> ClassEltFlags {
        class_elt::make(xhp_attr, b, b, b, b, b, b, b, b, b, b, b, b, b, b)
    }

    #[test]
    fn class_elt_bits_and_accessors() {
        assert_eq!(class_elt_with(None, false).bits(), 0);
        let all = class_elt_with(None, true);
        // Every bit from 0 to 16, except the three of the XHP attribute.
        assert_eq!(all.bits(), 0x1ffff & !((1 << 9) | (1 << 10) | (1 << 11)));
        assert!(class_elt::is_abstract(all));
        assert!(class_elt::is_final(all));
        assert!(class_elt::has_superfluous_override(all));
        assert!(class_elt::has_lsb(all));
        assert!(class_elt::is_synthesized(all));
        assert!(class_elt::is_const(all));
        assert!(class_elt::has_lateinit(all));
        assert!(class_elt::is_dynamicallycallable(all));
        assert!(class_elt::supports_dynamic_type(all));
        assert!(class_elt::is_readonly_prop_or_needs_concrete(all));
        assert!(class_elt::needs_init(all));
        assert!(class_elt::is_safe_global_variable(all));
        assert!(class_elt::is_no_auto_likes(all));
        assert!(class_elt::is_tests_bypass_visibility(all));
        assert_eq!(class_elt::get_xhp_attr(all), None);

        // One argument at a time, in the order of `make`.
        let one = |i: usize| {
            let b = |j: usize| i == j;
            class_elt::make(
                None,
                b(0),
                b(1),
                b(2),
                b(3),
                b(4),
                b(5),
                b(6),
                b(7),
                b(8),
                b(9),
                b(10),
                b(11),
                b(12),
                b(13),
            )
            .bits()
        };
        // abstract, final, superfluous_override, lsb, synthesized, const,
        // lateinit, dynamicallycallable, readonly_prop_or_needs_concrete,
        // support_dynamic_type, needs_init, safe_global_variable,
        // no_auto_likes, tests_bypass_visibility
        let expected: [u32; 14] = [0, 1, 2, 3, 4, 5, 6, 7, 12, 8, 13, 14, 15, 16];
        for (i, bit) in expected.iter().enumerate() {
            assert_eq!(one(i), 1 << bit, "argument {}", i);
        }

        let none = class_elt_with(None, false);
        assert_eq!(class_elt::set_synthesized(none).bits(), 1 << 4);
        assert_eq!(
            class_elt::reset_superfluous_override(all).bits(),
            all.bits() & !(1 << 2)
        );
        assert_eq!(class_elt::reset_superfluous_override(none), none);
    }

    #[test]
    fn class_elt_xhp_attr() {
        let cases = [
            (None, 0),
            (
                Some(XhpAttribute {
                    tag: None,
                    has_default: false,
                }),
                (1 << 10) | (1 << 11),
            ),
            (
                Some(XhpAttribute {
                    tag: None,
                    has_default: true,
                }),
                (1 << 9) | (1 << 10) | (1 << 11),
            ),
            (
                Some(XhpAttribute {
                    tag: Some(Tag::Required),
                    has_default: false,
                }),
                1 << 10,
            ),
            (
                Some(XhpAttribute {
                    tag: Some(Tag::Required),
                    has_default: true,
                }),
                (1 << 9) | (1 << 10),
            ),
            (
                Some(XhpAttribute {
                    tag: Some(Tag::LateInit),
                    has_default: false,
                }),
                1 << 11,
            ),
            (
                Some(XhpAttribute {
                    tag: Some(Tag::LateInit),
                    has_default: true,
                }),
                (1 << 9) | (1 << 11),
            ),
        ];
        for (xa, bits) in cases {
            for b in [false, true] {
                let flags = class_elt_with(xa, b);
                assert_eq!(flags.bits() & ((1 << 9) | (1 << 10) | (1 << 11)), bits);
                assert_eq!(class_elt::get_xhp_attr(flags), xa);
                // The same flags and the same attribute as `oxidized`'s
                // constructor and accessor.
                let oxidized_flags = ClassEltFlags::new(ClassEltFlagsArgs {
                    xhp_attr: xa,
                    is_abstract: b,
                    is_final: b,
                    is_superfluous_override: b,
                    is_lsb: b,
                    is_synthesized: b,
                    is_const: b,
                    is_lateinit: b,
                    is_dynamicallycallable: b,
                    is_readonly_prop_or_needs_concrete: b,
                    supports_dynamic_type: b,
                    needs_init: b,
                    safe_global_variable: b,
                    no_auto_likes: b,
                    is_tests_bypass_visibility: b,
                });
                assert_eq!(flags, oxidized_flags);
                assert_eq!(oxidized_flags.get_xhp_attr(), xa);
            }
        }
    }

    #[test]
    fn class_elt_show() {
        let flags = class_elt::make(
            Some(XhpAttribute {
                tag: Some(Tag::Required),
                has_default: false,
            }),
            true,
            false,
            false,
            false,
            false,
            true,
            false,
            false,
            false,
            false,
            false,
            false,
            false,
            true,
        );
        assert_eq!(class_elt::show(flags), OCAML_CLASS_ELT_SHOW);
    }

    /// What OCaml prints (`S_map.show Bool.pp`, that is `Wrapped_map.make_pp`
    /// with keys printed by `%S`) for the map of `class_elt_show`.
    const OCAML_CLASS_ELT_SHOW: &str = "{ \"Abstract\" -> true;\n  \"Const\" -> true;\n  \"Dynamicallycallable\" -> false;\n  \"Final\" -> false;\n  \"Lateinit\" -> false;\n  \"Lsb\" -> false;\n  \"NeedsInit\" -> false;\n  \"NoAutoLikes\" -> false;\n  \"ReadonlyPropOrNeedsConcrete\" -> false;\n  \"SafeGlobalVariable\" -> false;\n  \"SuperfluousOverride\" -> false;\n  \"SupportDynamicType\" -> false;\n  \"Synthesized\" -> false;\n  \"TestsBypassVisibility\" -> true;\n  \"XaHasDefault\" -> false;\n  \"XaTagLateinit\" -> false;\n  \"XaTagRequired\" -> true }";
}
