// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_class_types.ml`, except for `inherited_members`, which
//! nothing uses.

use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;
use std::sync::Arc;
use std::sync::Mutex;

use oxidized::typing_defs_core::ConsistentKind;
use ty::decl::FoldedClass;

use crate::ctx::R;
use crate::folded_class::*;

pub struct EagerMembers {
    pub props: Mutex<HashMap<String, ClassElt>>,
    pub static_props: Mutex<HashMap<String, ClassElt>>,
    pub methods: Mutex<HashMap<String, ClassElt>>,
    pub static_methods: Mutex<HashMap<String, ClassElt>>,
    pub construct: Mutex<Option<(Option<ClassElt>, ConsistentKind)>>,
}

pub fn create_eager_members() -> EagerMembers {
    EagerMembers {
        methods: Mutex::new(HashMap::new()),
        static_methods: Mutex::new(HashMap::new()),
        props: Mutex::new(HashMap::new()),
        static_props: Mutex::new(HashMap::new()),
        construct: Mutex::new(None),
    }
}

/// class_t:
/// This type is an abstraction layer over the way folded decls are stored, and
/// provides a view of classes which includes all inherited members and their types.
///
/// This view is constructed by merging a single heap entry for the folded class
/// with many entries for the types of each of its members (those member entries are
/// looked up lazily, as needed).
///
/// `Decl_defs.decl_class_type * eager_members`. The members are shared by
/// the clones of a `ClassT`, as they are by the copies of the OCaml pair.
///
/// A `ClassT` lives in the class cache of one thread
/// (`Decl_provider.get_class`), which hands out a copy at every lookup:
/// the handles are `Rc`s so that copying one does not write the reference
/// count of the folded class, which all the threads share.
#[derive(Clone)]
pub struct ClassT(pub Rc<Arc<FoldedClass<R>>>, pub Rc<EagerMembers>);

impl fmt::Debug for ClassT {
    // `[@@deriving show]`, with `eager_members` opaque.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("")
            .field(&self.0)
            .field(&format_args!("<opaque>"))
            .finish()
    }
}

pub fn make_class_t(decl: Arc<FoldedClass<R>>) -> ClassT {
    ClassT(Rc::new(decl), Rc::new(create_eager_members()))
}
