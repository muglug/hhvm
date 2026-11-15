// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! hackfmt_debug.ml: the output of `hackfmt --debug`.

use crate::chunk::ChunkGroup;
use crate::doc::Doc;
use crate::format_env::Env;
use crate::interval;
use crate::interval::Interval;
use crate::line_splitter;

#[derive(Clone, Debug, Default)]
pub struct DebugConfig {
    pub print_doc: bool,
    pub print_nesting_graph: bool,
    pub print_rule_dependencies: bool,
    pub chunk_ids: Option<Vec<isize>>,
}

fn debug_nesting(out: &mut Vec<u8>, chunk_group: &ChunkGroup<'_>) {
    for (i, c) in chunk_group.chunks.iter().enumerate() {
        let nesting_list = chunk_group.get_self_and_parent_list(c.nesting);
        let list_string: Vec<String> = nesting_list.iter().map(|n| n.to_string()).collect();
        out.extend_from_slice(format!("Chunk {} - [ {} ]\n", i, list_string.join(", ")).as_bytes());
    }
}

fn debug_rule_deps(out: &mut Vec<u8>, chunk_group: &ChunkGroup<'_>) {
    out.extend_from_slice(format!("{}\n", chunk_group.dependency_map_to_string()).as_bytes());
}

fn debug_chunk_groups(
    out: &mut Vec<u8>,
    config: &DebugConfig,
    env: &Env,
    range: Interval,
    source_text: &[u8],
    chunk_groups: &[ChunkGroup<'_>],
) {
    for (i, cg) in chunk_groups.iter().enumerate() {
        if let Some(ids) = &config.chunk_ids {
            if !ids.iter().any(|x| *x == i as isize) {
                continue;
            }
        }
        if !interval::intervals_overlap(range, cg.get_char_range()) {
            continue;
        }
        out.extend_from_slice(format!("Group Id: {}\n", i).as_bytes());
        out.extend_from_slice(format!("Indentation: {}\n", cg.block_indentation).as_bytes());
        out.extend_from_slice(format!("Chunk count: {}\n", cg.chunks.len()).as_bytes());
        for (i, c) in cg.chunks.iter().enumerate() {
            out.extend_from_slice(
                format!("{:8} rule_id:{} [{},{})\t", i, c.rule, c.start_char, c.end_char).as_bytes(),
            );
            out.extend_from_slice(&c.text());
            out.push(b'\n');
        }
        out.extend_from_slice(format!("Rule count {}\n", cg.get_rule_count()).as_bytes());
        for (k, v) in cg.rule_map.iter().enumerate() {
            out.extend_from_slice(format!("{:8} - {} - {}\n", k, k, v.to_debug_string()).as_bytes());
        }
        if config.print_rule_dependencies {
            debug_rule_deps(out, cg);
        }
        if config.print_nesting_graph {
            debug_nesting(out, cg);
        }
        out.extend_from_slice(&line_splitter::solve(
            env,
            Some(range),
            true,
            true,
            Some(source_text),
            std::slice::from_ref(cg),
        ));
        out.push(b'\n');
    }
}

/// `Hackfmt_debug.debug`: returns what goes to stdout; the Doc dump (with
/// `--doc`) is returned separately since it goes to stderr.
pub fn debug(
    config: &DebugConfig,
    env: &Env,
    range: Option<Interval>,
    source_text: &[u8],
    doc: &Doc<'_>,
    chunk_groups: &[ChunkGroup<'_>],
) -> (Vec<u8>, Vec<u8>) {
    let stderr = if config.print_doc { doc.dump() } else { vec![] };
    let range = range.unwrap_or((0, source_text.len() as isize));
    let mut out = vec![];
    debug_chunk_groups(&mut out, config, env, range, source_text, chunk_groups);
    (out, stderr)
}
