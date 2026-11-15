// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/xhp_attribute.ml`. See `hh/PORTING.md`.
//!
//! The types (`tag` and `t`) are those of `oxidized::xhp_attribute`,
//! re-exported here: `t` is [`XhpAttribute`] (also [`T`]), whose fields are
//! `tag` (`xa_tag`) and `has_default` (`xa_has_default`). Both types are
//! `Copy`.

pub use oxidized::xhp_attribute::*;

/// `Xhp_attribute.t`
pub type T = XhpAttribute;

/// `show_tag` (`[@@deriving show { with_path = false }]`)
pub fn show_tag(tag: &Tag) -> String {
    match tag {
        Tag::Required => "Required".to_string(),
        Tag::LateInit => "LateInit".to_string(),
    }
}

/// `show` (`[@@deriving show { with_path = false }]`)
pub fn show(attr: &T) -> String {
    let tag = match &attr.tag {
        None => "None".to_string(),
        Some(tag) => format!("(Some {})", show_tag(tag)),
    };
    format!(
        "{{ xa_tag = {}; xa_has_default = {} }}",
        tag, attr.has_default
    )
}

/// `equal_tag`
pub fn equal_tag(t1: &Tag, t2: &Tag) -> bool {
    t1 == t2
}

/// `equal`
pub fn equal(t1: &T, t2: &T) -> bool {
    t1 == t2
}

pub fn init() -> T {
    XhpAttribute {
        tag: None,
        has_default: false,
    }
}

pub fn map_tag(attr: T, f: impl FnOnce(Option<Tag>) -> Option<Tag>) -> T {
    XhpAttribute {
        tag: f(attr.tag),
        ..attr
    }
}

pub fn is_required(attr: &T) -> bool {
    match attr.tag {
        None | Some(Tag::LateInit) => false,
        Some(Tag::Required) => true,
    }
}

/// The attribute is taken by value (it is `Copy`), as the callers that
/// already exist pass it.
pub fn opt_is_required(attr: Option<T>) -> bool {
    match attr {
        None => false,
        Some(attr) => is_required(&attr),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn required() {
        assert!(!opt_is_required(None));
        assert!(!opt_is_required(Some(init())));
        let req = map_tag(init(), |_| Some(Tag::Required));
        assert!(opt_is_required(Some(req)));
        let late = map_tag(init(), |_| Some(Tag::LateInit));
        assert!(!is_required(&late));
        assert_eq!(
            show(&req),
            "{ xa_tag = (Some Required); xa_has_default = false }"
        );
    }
}
