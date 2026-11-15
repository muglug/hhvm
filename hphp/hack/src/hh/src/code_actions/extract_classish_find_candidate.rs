// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of
//! `client/ide_service/code_actions_services/refactors/extract_classish/extract_classish_find_candidate.ml`.

use std::sync::Arc;

use oxidized::aast;
use oxidized::ast_defs;

use super::extract_classish_types::Candidate;
use crate::pos::Pos;
use crate::provider_context;
use crate::tast;
use crate::tast_provider;

pub(crate) fn class_kind_supports_extraction(kind: &ast_defs::ClassishKind) -> bool {
    use ast_defs::Abstraction;
    use ast_defs::ClassishKind;
    match kind {
        ClassishKind::Cclass(Abstraction::Concrete) => true,
        // could handle with more logic
        ClassishKind::Cclass(Abstraction::Abstract) => false,
        ClassishKind::Cinterface | ClassishKind::Ctrait | ClassishKind::Cenum | ClassishKind::CenumClass(_) => false,
    }
}

pub(crate) fn find_candidate(selection: &Pos, entry: &Arc<provider_context::Entry>, ctx: &provider_context::T) -> Option<Candidate> {
    let tast_provider::ComputeTast { tast, .. } = tast_provider::compute_tast_quarantined(ctx, entry);

    tast.under_normal_assumptions.iter().find_map(|def| match def {
        aast::Def::Class(class_)
            if crate::pos::contains(&class_.span, selection) && class_kind_supports_extraction(&class_.kind) =>
        {
            let selected_methods: Vec<tast::Method_> = class_
                .methods
                .iter()
                .filter(|meth| crate::pos::contains(selection, &meth.span))
                .cloned()
                .collect();
            if selected_methods.is_empty() {
                None
            } else {
                Some(Candidate {
                    class_: (**class_).clone(),
                    selected_methods,
                })
            }
        }
        _ => None,
    })
}
