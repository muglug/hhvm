// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `simplihack/simplihack_prompt_context_provider.ml`. See
//! `hh/PORTING.md`.
//!
//! The functor `Make (LangService)` becomes the functions of `class`, generic
//! over the provider (`L`). They return the provider's error where the
//! provider raises.

/// `Make (LangService).Class`
pub mod class {
    use oxidized::aast;
    use oxidized::pos::Pos;

    use crate::folded_class::ClassElt;
    use crate::format;
    use crate::simplihack_intf::LanguageServiceProvider;
    use crate::symbol_occurrence;
    use crate::tast_env;
    use crate::typing_defs::CeVisibility;
    use crate::utils;

    // Helper functions to reduce code duplication

    /// Create a symbol occurrence for a method or constructor
    pub fn create_symbol_occurrence(
        class_name: &str,
        method_name: &str,
    ) -> symbol_occurrence::T<Pos> {
        let dummy_pos = Pos::NONE;
        symbol_occurrence::T {
            name: method_name.to_string(),
            type_: symbol_occurrence::Kind::Method(
                symbol_occurrence::ReceiverClass::ClassName(class_name.to_string()),
                method_name.to_string(),
            ),
            is_declaration: None,
            pos: dummy_pos,
            affects_prod_build: true,
        }
    }

    /// Format a method or constructor description directly from class_elt
    pub fn format_member_description(
        env: &tast_env::Env,
        class_name: &str,
        ce: &ClassElt,
        method_name: &str,
        kind: &str,
    ) -> String {
        // Get visibility as string
        let visibility = match &ce.ce_visibility {
            CeVisibility::Vpublic => "public",
            CeVisibility::Vprivate(_) => "private",
            CeVisibility::Vprotected(_) => "protected",
            CeVisibility::Vinternal(_) => "internal",
            CeVisibility::VprotectedInternal { .. } => "protected internal",
        };

        // Force evaluation of the lazy type
        let ce_type = &*ce.ce_type;

        // Create a symbol occurrence for the method/constructor
        let occurrence = create_symbol_occurrence(class_name, method_name);

        // Get a string representation of the type
        let type_str = tast_env::print_decl_ty_with_identity(env, ce_type, &occurrence, None);

        // Format the description
        let description = format::asprintf(|ppf| {
            format::pp_open_vbox(ppf, 0);
            format::pp_print_string(ppf, visibility);
            format::pp_print_char(ppf, ' ');
            format::pp_print_string(ppf, kind);
            format::pp_print_string(ppf, " defined in ");
            format::pp_print_string(ppf, utils::strip_ns(&ce.ce_origin));
            format::pp_print_string(ppf, ": ");
            format::pp_print_string(ppf, &type_str);
            format::pp_close_box(ppf);
        });

        // Add deprecation warning if applicable
        match &ce.ce_deprecated {
            Some(msg) => format::asprintf(|ppf| {
                format::pp_print_string(ppf, &description);
                format::pp_print_cut(ppf);
                format::pp_print_cut(ppf);
                format::pp_print_string(ppf, "WARNING: This method is deprecated: ");
                format::pp_print_string(ppf, msg);
            }),
            None => description,
        }
    }

    pub fn constructor<L: LanguageServiceProvider>(
        ctx: &L,
        name: &aast::ClassName,
    ) -> Result<String, L::Error> {
        let cls = ctx.class_find(name)?;
        let env = ctx.env();
        let constructor = L::class_constructor(&cls);
        Ok(match constructor {
            None => format::asprintf(|ppf| {
                format::pp_open_vbox(ppf, 0);
                format::pp_print_string(ppf, "This class does not have an explicit constructor.");
                format::pp_print_cut(ppf);
                format::pp_print_string(ppf, "It uses the default constructor.");
                format::pp_print_cut(ppf);
                format::pp_print_string(
                    ppf,
                    "Default constructors are public and do not have any parameters.",
                );
                format::pp_close_box(ppf);
            }),
            Some(ce) => {
                // Get class name as string
                let class_name = &name.1;

                // Format the constructor description
                format_member_description(env, class_name, &ce, "__construct", "constructor")
            }
        })
    }

    /// Helper function to format class members (methods, fields, etc.)
    pub fn format_class_members<L: LanguageServiceProvider>(
        ctx: &L,
        name: &aast::ClassName,
        get_members: impl FnOnce(&L::Class) -> Vec<(String, ClassElt)>,
        member_type: &str,
    ) -> Result<String, L::Error> {
        let cls = ctx.class_find(name)?;
        let env = ctx.env();
        let class_name = &name.1;

        // Get all members from the class using the provided function
        let members = get_members(&cls);

        Ok(if members.is_empty() {
            format!(
                "The class {} does not have any {}s.",
                utils::strip_ns(class_name),
                member_type
            )
        } else {
            // Format each member with its signature and visibility
            let member_entries: Vec<String> = members
                .iter()
                .map(|(member_name, ce)| {
                    // Format the member description
                    format_member_description(
                        env,
                        class_name,
                        ce,
                        member_name,
                        &format!("{} {}", member_type, member_name),
                    )
                })
                .collect();

            // Convert member entries list to a formatted string using fold
            let formatted_members = member_entries.into_iter().fold(String::new(), |acc, entry| {
                if acc.is_empty() {
                    entry
                } else {
                    format::asprintf(|ppf| {
                        format::pp_print_string(ppf, &acc);
                        format::pp_print_cut(ppf);
                        format::pp_print_string(ppf, &entry);
                    })
                }
            });
            format::asprintf(|ppf| {
                format::pp_open_vbox(ppf, 0);
                format::pp_print_string(ppf, &formatted_members);
                format::pp_close_box(ppf);
            })
        })
    }

    pub fn methods<L: LanguageServiceProvider>(
        ctx: &L,
        name: &aast::ClassName,
    ) -> Result<String, L::Error> {
        format_class_members(ctx, name, L::class_methods, "instance method")
    }

    pub fn static_methods<L: LanguageServiceProvider>(
        ctx: &L,
        name: &aast::ClassName,
    ) -> Result<String, L::Error> {
        format_class_members(ctx, name, L::class_static_methods, "static method")
    }

    pub fn fields<L: LanguageServiceProvider>(
        ctx: &L,
        name: &aast::ClassName,
    ) -> Result<String, L::Error> {
        format_class_members(ctx, name, L::class_fields, "instance field")
    }

    pub fn static_fields<L: LanguageServiceProvider>(
        ctx: &L,
        name: &aast::ClassName,
    ) -> Result<String, L::Error> {
        format_class_members(ctx, name, L::class_static_fields, "static field")
    }
}
