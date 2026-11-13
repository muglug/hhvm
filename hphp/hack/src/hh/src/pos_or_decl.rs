// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Pos_or_decl` (`decl/pos/pos_or_decl.ml`). See `hh/PORTING.md`.
//!
//! The types are those of `oxidized::pos_or_decl`, re-exported here:
//! `PosOrDecl` is `Pos`, as `Pos_or_decl.t` is `Pos.t`, and `Ctx` is
//! `Pos_or_decl.ctx`.
//!
//! Not here: `set_from_reason` (`oxidized::pos::Pos` has no way to make a
//! `Pos_from_reason`) and `to_span` (a `unit Pos.pos`).

#![allow(non_upper_case_globals)]

pub use oxidized::pos_or_decl::*;
use oxidized::decl_reference::DeclReference;
use oxidized::pos::Pos;

use crate::relative_path::RelativePath;
use crate::yojson::safe as yojson;

pub type T = PosOrDecl;

/// `Pos.Map`
pub mod map {
    pub use crate::pos::map::*;
}

/// `Pos.Set`
pub mod set {
    pub use crate::pos::set::*;
}

pub const none: T = Pos::NONE;

/// `[@@deriving show]` of `type t = Pos.t`: `Pos.pp`.
pub fn pp(fmt: &mut dyn std::fmt::Write, p: &T) -> std::fmt::Result {
    crate::pos::pp(fmt, p)
}

/// `[@@deriving eq]` of `type t = Pos.t`: `Pos.equal`.
pub fn equal(p1: &T, p2: &T) -> bool {
    crate::pos::equal(p1, p2)
}

/// `[@@deriving ord]` of `type t = Pos.t`: `Pos.compare`.
pub fn compare(p1: &T, p2: &T) -> std::cmp::Ordering {
    crate::pos::compare(p1, p2)
}

/// Fill in the gap "between" first position and second position.
/// Not valid if from different files or second position precedes first
pub fn btw(x1: &T, x2: &T) -> T {
    crate::pos::btw(x1, x2)
}

/// Essentially an upcast.
pub fn of_raw_pos(p: Pos) -> T {
    p
}

/// Compress a position to be stored in the decl heap.
pub fn make_decl_pos(p: &Pos, _decl: DeclReference) -> T {
    // TODO
    of_raw_pos(p.clone())
}

/// Compress a position to be stored in the decl heap.
/// If no decl reference is given, the position is not compressed but
/// simply converted.
pub fn make_decl_pos_of_option(p: &Pos, _decl: Option<DeclReference>) -> T {
    // TODO
    of_raw_pos(p.clone())
}

pub fn is_hhi(p: &T) -> bool {
    crate::pos::is_hhi(p)
}

/// This may become unsafe in the future as we change the implementation
/// of positions in the decl heap. Avoid using in new code.
/// Use a position from an AST instead of from a decl or type.
pub fn unsafe_to_raw_pos(p: T) -> Pos {
    p
}

pub fn filename(p: &T) -> RelativePath {
    crate::pos::filename(p)
}

/// For spans over just one line, return the line number, start column and
/// end column. This returns a closed interval.
/// Undefined for multi-line spans.
pub fn line_start_end_columns(p: &T) -> (isize, isize, isize) {
    crate::pos::info_pos(p)
}

pub fn json(p: &T) -> yojson::T {
    crate::pos::json(&crate::pos::to_absolute(p))
}

pub fn show_as_absolute_file_line_characters(p: &T) -> String {
    crate::pos::string(&crate::pos::to_absolute(p))
}

/// Replace the decl reference part of the position with a filename.
pub fn fill_in_filename(_filename: &RelativePath, p: T) -> Pos {
    p
}

/// Check that the position is in the current decl and if it is, resolve
/// it with the current file.
pub fn fill_in_filename_if_in_current_decl(current_decl_and_file: &Ctx, p: &T) -> Option<Pos> {
    let Ctx {
        file: current_file,
        decl: _current_decl,
    } = current_decl_and_file;
    // TODO use current_decl
    if p.filename() == current_file {
        Some(p.clone())
    } else {
        None
    }
}

/// ``[> `Raw of Pos.t | `Decl_ref of Decl_reference.t ]``
#[allow(non_camel_case_types)]
#[derive(Clone, Debug)]
pub enum RawPosOrDeclReference {
    Raw(Pos),
    Decl_ref(DeclReference),
}

/// Returns either a raw position equivalent to this position or the decl
/// that this position belongs to.
pub fn get_raw_pos_or_decl_reference(p: T) -> RawPosOrDeclReference {
    RawPosOrDeclReference::Raw(p)
}

pub fn merge(p1: &T, p2: &T) -> T {
    crate::pos::merge(p1, p2)
}

#[cfg(test)]
mod tests {
    use crate::relative_path::Prefix;

    use super::*;

    fn pos(file: &str) -> Pos {
        crate::pos::make_from_lnum_bol_offset(
            RelativePath::make(Prefix::Root, file.into()),
            (3, 20, 25),
            (3, 20, 30),
        )
    }

    #[test]
    fn current_decl() {
        let p = pos("a.php");
        let ctx = |file: &str| Ctx {
            decl: None,
            file: RelativePath::make(Prefix::Root, file.into()),
        };
        assert_eq!(
            fill_in_filename_if_in_current_decl(&ctx("a.php"), &p),
            Some(p.clone())
        );
        assert_eq!(fill_in_filename_if_in_current_decl(&ctx("b.php"), &p), None);
        // The prefix is part of the file.
        let hhi = Ctx {
            decl: None,
            file: RelativePath::make(Prefix::Hhi, "a.php".into()),
        };
        assert_eq!(fill_in_filename_if_in_current_decl(&hhi, &p), None);
    }

    #[test]
    fn conversions() {
        crate::relative_path::set_prefixes_for_tests();
        let p = pos("a.php");
        assert_eq!(of_raw_pos(p.clone()), p);
        assert_eq!(unsafe_to_raw_pos(p.clone()), p);
        assert_eq!(make_decl_pos_of_option(&p, None), p);
        assert_eq!(make_decl_pos(&p, DeclReference::Function("\\f".into())), p);
        assert_eq!(line_start_end_columns(&p), (3, 6, 10));
        assert_eq!(
            show_as_absolute_file_line_characters(&p),
            r#"File "/data/www/a.php", line 3, characters 6-10:"#
        );
        assert_eq!(
            yojson::to_string(&json(&p)),
            r#"{"filename":"/data/www/a.php","line":3,"char_start":6,"char_end":10}"#
        );
        assert!(!is_hhi(&p));
        assert!(none.is_none());
        let mut shown = String::new();
        pp(&mut shown, &p).unwrap();
        assert_eq!(shown, "[3:6-11]");
        assert!(equal(&p, &p.clone()) && !equal(&p, &none));
        // By file first (`Dummy` is after `Root`), then by offsets (the dummy
        // span is first in its file).
        assert_eq!(compare(&none, &p), std::cmp::Ordering::Greater);
        let start_of_file = crate::pos::make_from(filename(&p));
        assert_eq!(compare(&start_of_file, &p), std::cmp::Ordering::Less);
        assert_eq!(filename(&p), RelativePath::make(Prefix::Root, "a.php".into()));
    }
}
