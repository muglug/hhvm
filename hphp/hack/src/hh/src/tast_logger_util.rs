// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/tast_check/tast_logger_util.ml`. See `hh/PORTING.md`.

use oxidized::pos::Pos;

/// `module Generated_file_utils`
pub mod generated_file_utils {
    use std::cell::RefCell;

    use bstr::ByteSlice;
    use oxidized::pos::Pos;
    use relative_path::RelativePath;

    /// A manual (non-generated) section within a partially-generated file.
    /// `start_offset` is inclusive, `end_offset` is exclusive.
    /// This matches `Pos.t` conventions (see pos.mli).
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct ManualSection {
        /// 0-indexed, inclusive
        pub start_offset: usize,
        /// 0-indexed, exclusive
        pub end_offset: usize,
    }

    /// Classification of a file's generated status.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum FileGeneratedKind {
        NotGenerated,
        FullyGenerated,
        /// The manual sections are the non-generated regions of the file.
        PartiallyGenerated(Vec<ManualSection>),
    }

    pub const BEGIN_MANUAL_SECTION_PREFIX: &str = "/* BEGIN MANUAL SECTION";

    pub const END_MANUAL_SECTION_TAG: &str = "/* END MANUAL SECTION */";

    /// `String.substr_index contents ~pos ~pattern`: the index (in all of
    /// `contents`) of the first occurrence of `pattern` at or after `pos`.
    fn substr_index(contents: &[u8], pos: usize, pattern: &str) -> Option<usize> {
        contents[pos..].find(pattern).map(|i| pos + i)
    }

    /// Find manual sections in partially-generated files
    pub fn parse_manual_sections(contents: &[u8]) -> Vec<ManualSection> {
        let len = contents.len();
        let mut acc = vec![];
        let mut search_from = 0;
        // `let rec find_sections acc search_from`
        loop {
            match substr_index(contents, search_from, BEGIN_MANUAL_SECTION_PREFIX) {
                None => return acc,
                Some(begin_start) => {
                    // Find the closing */ of the BEGIN comment.
                    // Start searching 2 bytes in to skip past the opening "/*".
                    match substr_index(contents, begin_start + 2, "*/") {
                        // malformed, stop
                        None => return acc,
                        Some(close_star) => {
                            let start_offset = close_star + 2;
                            // Find the matching END MANUAL SECTION
                            match substr_index(contents, start_offset, END_MANUAL_SECTION_TAG) {
                                None => {
                                    // Unclosed section, skip and keep searching
                                    search_from = std::cmp::min(len, start_offset)
                                }
                                Some(end_offset) => {
                                    let section = ManualSection {
                                        start_offset,
                                        end_offset,
                                    };
                                    let after_end = end_offset + END_MANUAL_SECTION_TAG.len();
                                    acc.push(section);
                                    search_from = std::cmp::min(len, after_end)
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    pub fn classify_contents(contents: &[u8]) -> FileGeneratedKind {
        let partially_generated_tag = "@".to_string() + "partially-generated";
        if contents.contains_str(&partially_generated_tag) {
            FileGeneratedKind::PartiallyGenerated(parse_manual_sections(contents))
        } else {
            let generated_tag = "@".to_string() + "generated";
            if contents.contains_str(&generated_tag) {
                FileGeneratedKind::FullyGenerated
            } else {
                FileGeneratedKind::NotGenerated
            }
        }
    }

    pub fn is_within_manual_section(manual_sections: &[ManualSection], pos: &Pos) -> bool {
        let pos_start = pos.start_offset();
        let pos_end = pos.end_offset();
        manual_sections
            .iter()
            .any(|section| pos_start >= section.start_offset && pos_end <= section.end_offset)
    }

    thread_local! {
        /// A single-entry cache, since each process checks one file at a time
        /// (here: each thread).
        pub static CACHE: RefCell<Option<(RelativePath, FileGeneratedKind)>> =
            const { RefCell::new(None) };
    }

    /// Not in the OCaml (whose worker starts each job afresh): forget the
    /// cache, the contents of its file may have changed (see
    /// `crate::rt::decl_epoch`).
    pub fn forget_thread_memos() {
        CACHE.with(|c| *c.borrow_mut() = None)
    }

    pub fn classify_file(file: &RelativePath) -> Option<FileGeneratedKind> {
        let cached = CACHE.with(|c| match &*c.borrow() {
            Some((cached_file, kind)) if cached_file == file => Some(kind.clone()),
            _ => None,
        });
        match cached {
            Some(kind) => Some(kind),
            None => match crate::file_provider::get_contents(None, file) {
                None => None,
                Some(contents) => {
                    let kind = classify_contents(&contents);
                    CACHE.with(|c| *c.borrow_mut() = Some((file.clone(), kind.clone())));
                    Some(kind)
                }
            },
        }
    }

    pub fn is_generated(pos: &Pos) -> bool {
        let file = pos.filename();
        match classify_file(file) {
            None => false,
            Some(FileGeneratedKind::NotGenerated) => false,
            Some(FileGeneratedKind::FullyGenerated) => true,
            Some(FileGeneratedKind::PartiallyGenerated(manual_sections)) => {
                !is_within_manual_section(&manual_sections, pos)
            }
        }
    }
}

/// Returns true if the position is in a generated file.
/// In partially-generated files, returns false iff in a MANUAL section.
/// Cheap to call for many positions in the same file.
pub fn is_generated(pos: &Pos) -> bool {
    generated_file_utils::is_generated(pos)
}

#[cfg(test)]
mod tests {
    use super::generated_file_utils::*;

    #[test]
    fn manual_sections() {
        // The tags are split, as in the OCaml, so that this file is not
        // taken for a generated one.
        let contents = format!(
            "<?hh // @{}\n\
            /* BEGIN MANUAL SECTION a */xyz/* END MANUAL SECTION */\n\
            /* BEGIN MANUAL SECTION b */unclosed",
            "partially-generated"
        );
        let contents = contents.as_bytes();
        let begin_a = contents.windows(2).position(|w| w == b"*/").unwrap();
        let start_offset = begin_a + 2;
        let end_offset = start_offset + 3;
        assert_eq!(
            classify_contents(contents),
            FileGeneratedKind::PartiallyGenerated(vec![ManualSection {
                start_offset,
                end_offset
            }])
        );
        assert_eq!(
            classify_contents(format!("<?hh // @{}", "generated").as_bytes()),
            FileGeneratedKind::FullyGenerated
        );
        assert_eq!(classify_contents(b"<?hh"), FileGeneratedKind::NotGenerated);
        // A BEGIN comment without its closing `*/`.
        assert_eq!(parse_manual_sections(b"/* BEGIN MANUAL SECTION"), vec![]);
    }
}
