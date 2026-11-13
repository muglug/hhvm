// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `refactors/inline_method/inline_method_rewrite_block.ml`. See
//! `hh/PORTING.md`.

use parser_core_types::positioned_syntax::PositionedSyntax;
use parser_core_types::syntax::SyntaxVariant;

use super::code_actions_utils as cu;
use super::inline_method_rename;
use crate::full_fidelity_source_text as source_text;
use crate::relative_path::RelativePath;

fn apply_patches_to_string(old_content: &str, patches: Vec<cu::Patch>) -> String {
    cu::to_string(cu::apply_patches_to_string(old_content.as_bytes(), patches).into())
}

/// given the source text of a block, apply `f` to source text wrapped such that it's
/// a valid Hack program (with `<?hh` and all).
/// Then strip off the wrapping (`<?hh` and all).
fn with_wrapped_source_text<A>(block_source_text: &str, f: impl FnOnce(&str) -> (A, String)) -> (A, String) {
    let unwrap = |wrapped_source_text: &str| -> String {
        // drop "<?hh" and "function foo ..."
        let mut lines: Vec<&str> = wrapped_source_text.lines().skip(2).collect();
        // we wrapped s.t. the string is guaranteed to have a last line
        lines.pop().expect("List.drop_last_exn");
        lines.join("\n")
    };
    let wrapped = format!("<?hh\nfunction foo(): void {{\n{}\n}}", block_source_text);
    let (res, rewritten_block_wrapped) = f(&wrapped);
    let rewritten_block = unwrap(&rewritten_block_wrapped);
    (res, rewritten_block)
}

/// `String.make n ' '`
fn string_make(n: isize) -> String {
    if n < 0 {
        panic!("Invalid_argument(\"String.make\")")
    }
    " ".repeat(n as usize)
}

/// Apply libhackfmt to a string corresponding to a block (one or multiple statements).
/// `start_indent_amount` is the amount the beginning of the text is *already* indented
///
/// Re the `start_indent` param:
/// We remember `start_indent` so we can restore it after formatting.
/// In the following, `start_indent` is `2`:
///
/// ```text
/// if (1 < 2) {
///   // start
///   $x = 3;
///   //end
/// }
/// ```
pub fn format_block(path: &RelativePath, block_source_text: &str, start_indent_amount: isize) -> String {
    let add_indent = |text: &str| -> String {
        let indent = string_make(start_indent_amount);
        // adjusted because the autoformatter already indents once, due to our
        // trick of wrapping the code-to-format in a function
        let inner_indent = string_make(start_indent_amount - hackfmt::Env::default().indent_width);
        let text = text
            .lines()
            .map(|line| format!("{}{}", inner_indent, line))
            .collect::<Vec<_>>()
            .join("\n");
        format!("{}\n{}", text, indent)
    };
    let ((), formatted) = with_wrapped_source_text(block_source_text, |wrapped_source_text| {
        // `Libhackfmt.format_tree @@ tree_of_text path wrapped_source_text`
        let tree = hackfmt::parse(
            wrapped_source_text.as_bytes(),
            &crate::relative_path::suffix(path),
            false,
            false,
        );
        ((), cu::to_string(hackfmt::format_tree(None, &tree).into()))
    });
    add_indent(&formatted)
}

/// `Ff_rewriter.aggregating_rewrite_post fold root acc` with a `fold` that
/// keeps every node: the children from the first to the last, then the node.
fn fold_post<'a>(node: &'a PositionedSyntax, f: &mut impl FnMut(&'a PositionedSyntax)) {
    for child in node.iter_children() {
        fold_post(child, f)
    }
    f(node)
}

/// rename variables and replace `return` with a variable assignment
pub fn rewrite_block(
    r: &mut inline_method_rename::T,
    path: &RelativePath,
    block_source_text: &str,
    return_var_raw_name: &str,
) -> String {
    let ((), rewritten) = with_wrapped_source_text(block_source_text, |wrapped_source_text| {
        // `tree_of_text path wrapped_source_text |> PositionedTree.root`
        let st = source_text::make(path, wrapped_source_text.as_bytes());
        let (root, _errors, _state) = positioned_parser::parse_script(
            &source_text::source_text(&st),
            parser_core_types::parser_env::ParserEnv::default(),
        );
        // `Syn.position_exclusive path node` (always `Some`)
        let position_exclusive = |node: &PositionedSyntax| {
            source_text::relative_pos(path, &st, cu::start_offset(node), cu::end_offset(node) + 1)
        };
        // (`patch :: patches`: the last patch first.)
        let mut patches: Vec<cu::Patch> = vec![];
        fold_post(&root, &mut |node| match &node.syntax {
            SyntaxVariant::VariableExpression(x) => {
                let var = cu::text(&st, &x.variable_expression);
                let pos = position_exclusive(node);
                let var = inline_method_rename::rename(r, &var);
                patches.push(cu::Patch::Replace { pos, text: var });
            }
            SyntaxVariant::ReturnStatement(x) => {
                let pos = position_exclusive(&x.return_keyword);
                let return_var = inline_method_rename::rename(r, return_var_raw_name);
                let text = format!("{} = ", return_var);
                patches.push(cu::Patch::Replace { pos, text });
            }
            _ => {}
        });
        patches.reverse();
        let rewritten = apply_patches_to_string(wrapped_source_text, patches);
        ((), rewritten)
    });
    rewritten
}
