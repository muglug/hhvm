// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_go_to_definition.ml`. See
//! `hh/PORTING.md`.
//!
//! Behind `server`: its result type is in
//! `Server_command_types`.

use std::sync::Arc;

use crate::file_content;
use crate::provider_context;
use crate::server_command_types::go_to_definition;
use crate::symbol_definition;
use crate::symbol_occurrence;

/// `` [ `None | `Single of string | `Multiple ] ``
enum Cls {
    None,
    Single(String),
    Multiple,
}

/// Returns the definition of the symbol at the given position in the document.
///
/// This function is for interactive use only, as it may return multiple definitions
/// for the user's convenience. For example, when hovering over a constructor call,
/// it may return both the definition for the class being constructed, and the
/// `__construct` method of the class. Tooling should use
/// [ServerCommandTypes.IDENTIFY_FUNCTION] instead.
pub fn go_quarantined(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    pos: &file_content::position::T,
) -> go_to_definition::Result {
    let results = crate::server_identify_function::go_quarantined(ctx, entry, pos);
    let results: Vec<_> = results
        .into_iter()
        .filter_map(|(occ, def)| def.map(|def| (occ, def)))
        .collect();
    // What's it like when we return multiple definitions? For instance, if you ask
    // for the definition of "new C()" then we've now got the definition of the
    // class "\C" and also of the constructor "\\C::__construct". I think that
    // users would be happier to only have the definition of the constructor, so
    // as to jump straight to it without the fuss of clicking to select which one.
    // That indeed is what Typescript does -- it only gives the constructor.
    // (VSCode displays multiple definitions with a peek view of them all;
    // Atom displays them with a small popup showing just title+file+line of each).
    // There's one subtlety. If you declare a base class "B" with a constructor,
    // and a derived class "C" without a constructor, and click on "new C()", then
    // Typescript and VS Code will pop up a little window with both options. This
    // seems like a reasonable compromise, so Hack should do the same.
    let mut cls = Cls::None;
    for (occ, _) in &results {
        cls = match (cls, symbol_occurrence::enclosing_class(occ)) {
            (Cls::None, Some(c)) => Cls::Single(c),
            (Cls::Single(c), Some(c2)) if c == c2 => Cls::Single(c),
            (Cls::Single(_), Some(_)) => {
                // Symbol occurrences for methods/properties that only exist in a base
                // class still have the derived class as their enclosing class, even
                // though it doesn't explicitly override that member. Because of that, if
                // we hit this case then we know that we're dealing with a union type. In
                // that case, it's not really possible to do the rest of this filtration,
                // since it would have to be decided on a per-class basis.
                Cls::Multiple
            }
            (class_opt, _) => class_opt,
        }
    }
    let results = match cls {
        Cls::None | Cls::Multiple => results,
        Cls::Single(_) => {
            let explicitly_defined: Vec<_> = results
                .iter()
                .filter(|(occ, def)| match symbol_occurrence::get_class_name(occ) {
                    None => false,
                    Some(cls) => symbol_definition::full_name(def)
                        .starts_with(crate::utils::strip_ns(&cls)),
                })
                .collect();
            let is_result_constructor =
                |(occ, _): &&(symbol_occurrence::T<_>, _)| symbol_occurrence::is_constructor(occ);
            let has_explicit_constructor = explicitly_defined.iter().any(is_result_constructor);
            let has_constructor = results.iter().any(|r| is_result_constructor(&r));
            let has_class = results.iter().any(|(occ, _)| symbol_occurrence::is_class(occ));
            // If we have a constructor but it's derived, then we'd like to show both
            // the class and the constructor. If the constructor is explicitly
            // defined, though, we'd like to filter the class out and only show the
            // constructor.
            if has_constructor && has_class && has_explicit_constructor {
                results
                    .into_iter()
                    .filter(|r| is_result_constructor(&r))
                    .collect()
            } else {
                results
            }
        }
    };
    results
        .into_iter()
        .map(|(occurrence, definition)| {
            let occurrence = symbol_occurrence::to_absolute(&occurrence);
            let definition = symbol_definition::to_absolute(&definition);
            (occurrence, definition)
        })
        .collect()
}
