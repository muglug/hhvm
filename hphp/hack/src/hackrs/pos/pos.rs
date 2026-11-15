// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

#![feature(box_patterns)]
use std::fmt;
use std::hash::Hash;

use eq_modulo_pos::EqModuloPos;
use ocamlrep::FromOcamlRep;
use ocamlrep::ToOcamlRep;
use oxidized::file_pos_small::FilePosSmall;
use oxidized::pos_span_raw::PosSpanRaw;
use oxidized::pos_span_tiny::PosSpanTiny;
use serde::Deserialize;
use serde::Serialize;
use serde::de::DeserializeOwned;

mod relative_path;
mod symbol;
mod to_oxidized;
pub use oxidized::file_pos_large::FilePosLarge;
pub use symbol::*;
pub use to_oxidized::ToOxidized;

pub use crate::relative_path::*;

pub trait Pos:
    Eq
    + Hash
    + Clone
    + std::fmt::Debug
    + Serialize
    + DeserializeOwned
    + for<'a> From<oxidized::pos::Pos>
    + for<'a> From<&'a oxidized::pos::Pos>
    + for<'a> ToOxidized<Output = oxidized::pos::Pos>
    + ToOcamlRep
    + FromOcamlRep
    + EqModuloPos
    + 'static
{
    /// Make a new instance. If the implementing Pos is stateful,
    /// it will call cons() to obtain interned values to construct the instance.
    fn mk(cons: impl FnOnce() -> (RelativePath, FilePosLarge, FilePosLarge)) -> Self;

    fn none() -> Self;

    fn from_ast(pos: &oxidized::pos::Pos) -> Self {
        Self::mk(|| {
            let PosSpanRaw { start, end } = pos.to_raw_span();
            (pos.filename().into(), start, end)
        })
    }

    fn from_decl(pos: oxidized::pos::Pos) -> Self {
        Self::mk(|| {
            let PosSpanRaw { start, end } = pos.to_raw_span();
            (pos.filename().into(), start, end)
        })
    }

    fn is_hhi(&self) -> bool;
}

/// Represents a closed-ended range [start, end] in a file.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[derive(ToOcamlRep, FromOcamlRep)]
enum PosImpl {
    Small {
        prefix: Prefix,
        suffix: Bytes,
        span: Box<(FilePosSmall, FilePosSmall)>,
    },
    Large {
        prefix: Prefix,
        suffix: Bytes,
        span: Box<(FilePosLarge, FilePosLarge)>,
    },
    Tiny {
        prefix: Prefix,
        suffix: Bytes,
        span: PosSpanTiny,
    },
}

static_assertions::assert_eq_size!(PosImpl, u128);

#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct BPos(PosImpl);

impl Pos for BPos {
    fn mk(cons: impl FnOnce() -> (RelativePath, FilePosLarge, FilePosLarge)) -> Self {
        let (file, start, end) = cons();
        Self::new(file, start, end)
    }

    fn none() -> Self {
        BPos::none()
    }

    fn from_ast(pos: &oxidized::pos::Pos) -> Self {
        bpos_of_oxidized(pos)
    }

    fn from_decl(pos: oxidized::pos::Pos) -> Self {
        bpos_of_oxidized(&pos)
    }

    fn is_hhi(&self) -> bool {
        let BPos(pos_impl) = self;
        let prefix = match *pos_impl {
            PosImpl::Small { prefix, .. } => prefix,
            PosImpl::Large { prefix, .. } => prefix,
            PosImpl::Tiny { prefix, .. } => prefix,
        };
        prefix == Prefix::Hhi
    }
}

impl BPos {
    pub fn new(file: RelativePath, start: FilePosLarge, end: FilePosLarge) -> Self {
        let prefix = file.prefix();
        let suffix = file.suffix();
        if let Some(span) = PosSpanTiny::make(&start, &end) {
            return BPos(PosImpl::Tiny {
                prefix,
                suffix,
                span,
            });
        }
        let (lnum, bol, offset) = start.line_beg_offset();
        if let Some(start) = FilePosSmall::from_lnum_bol_offset(lnum, bol, offset) {
            let (lnum, bol, offset) = end.line_beg_offset();
            if let Some(end) = FilePosSmall::from_lnum_bol_offset(lnum, bol, offset) {
                let span = Box::new((start, end));
                return BPos(PosImpl::Small {
                    prefix,
                    suffix,
                    span,
                });
            }
        }
        let span = Box::new((start, end));
        BPos(PosImpl::Large {
            prefix,
            suffix,
            span,
        })
    }

    pub const fn none() -> Self {
        let file = RelativePath::empty();
        Self(PosImpl::Tiny {
            prefix: file.prefix(),
            suffix: file.suffix(),
            span: PosSpanTiny::make_dummy(),
        })
    }

    pub fn is_none(&self) -> bool {
        match self {
            BPos(PosImpl::Tiny { span, .. }) => span.is_dummy() && self.file().is_empty(),
            _ => false,
        }
    }

    pub const fn file(&self) -> RelativePath {
        match self.0 {
            PosImpl::Small { prefix, suffix, .. }
            | PosImpl::Large { prefix, suffix, .. }
            | PosImpl::Tiny { prefix, suffix, .. } => RelativePath::from_bytes(prefix, suffix),
        }
    }
}

impl fmt::Debug for BPos {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut do_fmt = |start_line, start_col, end_line, end_col| {
            if start_line == end_line {
                write!(
                    f,
                    "Pos({:?}, {}:{}-{})",
                    &self.file(),
                    &start_line,
                    &(start_col + 1),
                    &(end_col + 1),
                )
            } else {
                write!(
                    f,
                    "Pos({:?}, {}:{}-{}:{})",
                    &self.file(),
                    &start_line,
                    &(start_col + 1),
                    &end_line,
                    &(end_col + 1),
                )
            }
        };
        if self.is_none() {
            return write!(f, "Pos(None)");
        }
        match &self.0 {
            PosImpl::Small { span, .. } => {
                let (start, end) = &**span;
                do_fmt(start.line(), start.column(), end.line(), end.column())
            }
            PosImpl::Large { span, .. } => {
                let (start, end) = &**span;
                do_fmt(start.line(), start.column(), end.line(), end.column())
            }
            PosImpl::Tiny { span, .. } => {
                let span = span.to_raw_span();
                do_fmt(
                    span.start.line(),
                    span.start.column(),
                    span.end.line(),
                    span.end.column(),
                )
            }
        }
    }
}

impl EqModuloPos for BPos {
    fn eq_modulo_pos(&self, _rhs: &Self) -> bool {
        true
    }
    fn eq_modulo_pos_and_reason(&self, _rhs: &Self) -> bool {
        true
    }
}

/// The interned path of the `oxidized` positions converted from positions in
/// `file`. Interning looks the path up in a global table (after building an
/// `oxidized` path to look up), and the positions of declarations are
/// converted at each use: each thread remembers the interned paths of the
/// files it converted last (in a direct-mapped table).
fn oxidized_file(file: RelativePath) -> oxidized::pos::InternedPath {
    use std::cell::RefCell;
    use std::hash::Hash;
    use std::hash::Hasher;
    const SLOTS: usize = 1024;
    type Slot = Option<(RelativePath, oxidized::pos::InternedPath)>;
    thread_local! {
        static FILES: RefCell<[Slot; SLOTS]> = const { RefCell::new([None; SLOTS]) };
    }
    struct SlotHasher(u64);
    impl Hasher for SlotHasher {
        fn finish(&self) -> u64 {
            self.0
        }
        fn write(&mut self, bytes: &[u8]) {
            for b in bytes {
                self.0 = (self.0.rotate_left(5) ^ *b as u64).wrapping_mul(0x517cc1b727220a95);
            }
        }
        fn write_u32(&mut self, i: u32) {
            self.0 = (self.0.rotate_left(5) ^ i as u64).wrapping_mul(0x517cc1b727220a95);
        }
        fn write_u64(&mut self, i: u64) {
            self.0 = (self.0.rotate_left(5) ^ i).wrapping_mul(0x517cc1b727220a95);
        }
        fn write_usize(&mut self, i: usize) {
            self.write_u64(i as u64)
        }
        fn write_isize(&mut self, i: isize) {
            self.write_u64(i as u64)
        }
    }
    let mut hasher = SlotHasher(0);
    file.hash(&mut hasher);
    let slot = (hasher.finish() >> 32) as usize % SLOTS;
    FILES.with_borrow_mut(|files| match files[slot] {
        Some((f, interned)) if f == file => interned,
        _ => {
            let interned = oxidized::pos::InternedPath::new(&file.into());
            files[slot] = Some((file, interned));
            interned
        }
    })
}

/// `Pos::from_ast` for `BPos`: `BPos::new` of the file and the raw span, with
/// the file taken from a per-thread table by the address of the interned path
/// (interning the path's bytes again looks them up in a global table), and a
/// tiny span kept as it is (the raw span of a tiny span makes it again).
fn bpos_of_oxidized(pos: &oxidized::pos::Pos) -> BPos {
    use std::cell::RefCell;
    const SLOTS: usize = 256;
    thread_local! {
        static FILES: RefCell<[(usize, RelativePath); SLOTS]> =
            const { RefCell::new([(0, RelativePath::empty()); SLOTS]) };
    }
    let interned = pos.interned_filename();
    // (Interned paths are never freed: the address identifies the path.)
    let addr = interned.get() as *const ::relative_path::RelativePath as usize;
    let slot = (addr >> 4 ^ addr >> 12) % SLOTS;
    let file = FILES
        .try_with(|files| {
            let mut files = files.borrow_mut();
            match files[slot] {
                (a, f) if a == addr => f,
                _ => {
                    let f = RelativePath::from(interned.get());
                    files[slot] = (addr, f);
                    f
                }
            }
        })
        .unwrap_or_else(|_| RelativePath::from(interned.get()));
    if let Some(span) = pos.as_tiny_span() {
        return BPos(PosImpl::Tiny {
            prefix: file.prefix(),
            suffix: file.suffix(),
            span,
        });
    }
    let PosSpanRaw { start, end } = pos.to_raw_span();
    BPos::new(file, start, end)
}

impl From<BPos> for oxidized::pos::Pos {
    fn from(pos: BPos) -> Self {
        let file = oxidized_file(pos.file());
        if let PosImpl::Tiny { span, .. } = pos.0 {
            return Self::from_tiny_span_interned(file, span);
        }
        Self::from_raw_span_interned(
            file,
            match &pos.0 {
                PosImpl::Small { span, .. } => {
                    let (start, end) = **span;
                    PosSpanRaw {
                        start: start.into(),
                        end: end.into(),
                    }
                }
                PosImpl::Large { span, .. } => {
                    let (start, end) = **span;
                    PosSpanRaw { start, end }
                }
                PosImpl::Tiny { span, .. } => span.to_raw_span(),
            },
        )
    }
}

impl From<oxidized::pos::Pos> for BPos {
    fn from(pos: oxidized::pos::Pos) -> Self {
        Self::from_ast(&pos)
    }
}

impl<'a> From<&'a oxidized::pos::Pos> for BPos {
    fn from(pos: &'a oxidized::pos::Pos) -> Self {
        Self::from_ast(pos)
    }
}

impl ToOxidized for BPos {
    type Output = oxidized::pos::Pos;

    fn to_oxidized(self) -> Self::Output {
        let file = oxidized_file(self.file());
        match self.0 {
            PosImpl::Small { box span, .. } => {
                let (start, end) = span;
                oxidized::pos::Pos::from_raw_span_interned(
                    file,
                    PosSpanRaw {
                        start: start.into(),
                        end: end.into(),
                    },
                )
            }
            PosImpl::Large { box span, .. } => {
                let (start, end) = span;
                oxidized::pos::Pos::from_raw_span_interned(file, PosSpanRaw { start, end })
            }
            PosImpl::Tiny { span, .. } => oxidized::pos::Pos::from_tiny_span_interned(file, span),
        }
    }
}

impl ToOcamlRep for BPos {
    fn to_ocamlrep<'a, A: ocamlrep::Allocator>(&'a self, alloc: &'a A) -> ocamlrep::Value<'a> {
        let file = match &self.0 {
            PosImpl::Small { prefix, suffix, .. }
            | PosImpl::Large { prefix, suffix, .. }
            | PosImpl::Tiny { prefix, suffix, .. } => {
                let mut file = alloc.block_with_size(2);
                alloc.set_field(&mut file, 0, prefix.to_ocamlrep(alloc));
                alloc.set_field(&mut file, 1, suffix.to_ocamlrep(alloc));
                file.build()
            }
        };
        match &self.0 {
            PosImpl::Small { span, .. } => {
                let (start, end) = &**span;
                let mut pos = alloc.block_with_size_and_tag(3usize, 0u8);
                alloc.set_field(&mut pos, 0, file);
                alloc.set_field(&mut pos, 1, start.to_ocamlrep(alloc));
                alloc.set_field(&mut pos, 2, end.to_ocamlrep(alloc));
                pos.build()
            }
            PosImpl::Large { span, .. } => {
                let (start, end) = &**span;
                let mut pos = alloc.block_with_size_and_tag(3usize, 1u8);
                alloc.set_field(&mut pos, 0, file);
                alloc.set_field(&mut pos, 1, start.to_ocamlrep(alloc));
                alloc.set_field(&mut pos, 2, end.to_ocamlrep(alloc));
                pos.build()
            }
            PosImpl::Tiny { span, .. } => {
                let mut pos = alloc.block_with_size_and_tag(2usize, 2u8);
                alloc.set_field(&mut pos, 0, file);
                alloc.set_field(&mut pos, 1, span.to_ocamlrep(alloc));
                pos.build()
            }
        }
    }
}

impl FromOcamlRep for BPos {
    fn from_ocamlrep(value: ocamlrep::Value<'_>) -> Result<Self, ocamlrep::FromError> {
        let block = ocamlrep::from::expect_block(value)?;
        match block.tag() {
            0u8 /* Pos_small */ => {
                ocamlrep::from::expect_block_size(block, 3usize)?;
                let path = ocamlrep::from::expect_tuple(block[0], 2)?;
                let (prefix, suffix) = (
                    Prefix::from_ocamlrep(path[0])?,
                    Bytes::from_ocamlrep(path[1])?
                );
                let span = Box::new((
                    FilePosSmall::from_ocamlrep(block[1])?,
                    FilePosSmall::from_ocamlrep(block[2])?
                ));

                Ok(BPos(PosImpl::Small{prefix, suffix, span}))
            },
            1u8 /* Pos_large */ => {
                ocamlrep::from::expect_block_size(block, 3usize)?;
                let path = ocamlrep::from::expect_tuple(block[0], 2)?;
                let (prefix, suffix) = (
                    Prefix::from_ocamlrep(path[0])?,
                    Bytes::from_ocamlrep(path[1])?
                );
                let span = Box::new((
                    FilePosLarge::from_ocamlrep(block[1])?,
                    FilePosLarge::from_ocamlrep(block[2])?
                ));

                Ok(BPos(PosImpl::Large{prefix, suffix, span}))
            },
            2u8 /* Pos_tiny */ => {
                ocamlrep::from::expect_block_size(block, 2usize)?;
                let path = ocamlrep::from::expect_tuple(block[0], 2)?;
                let (prefix, suffix) = (
                    Prefix::from_ocamlrep(path[0])?,
                    Bytes::from_ocamlrep(path[1])?
                );
                let span = PosSpanTiny::from_ocamlrep(block[1])?;

                Ok(BPos(PosImpl::Tiny{prefix, suffix, span}))
            },
            tag /* Pos_from_reason */ => {
                Err(ocamlrep::FromError::BlockTagOutOfRange{max:2u8, actual:tag})
            }
        }
    }
}

/// A stateless sentinel Pos.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct NPos;

impl Pos for NPos {
    fn mk(_cons: impl FnOnce() -> (RelativePath, FilePosLarge, FilePosLarge)) -> Self {
        NPos
    }

    fn none() -> Self {
        NPos
    }

    fn is_hhi(&self) -> bool {
        false // See T81321312.
        // Note(SF, 2022-03-23): Jake advises "This definition will lead to a
        // small behavior difference between `NPos` and `BPos`: when
        // typechecking in posisition-free mode we'll register depedencies on
        // hhi files but in positioned mode we won't. If this turns out to be
        // problematic, one solution is to make `NPos` store a `u8` rather than
        // being zero-sized and in that we can store a bit for whether the
        // position is in a hhi file."
    }
}

impl EqModuloPos for NPos {
    fn eq_modulo_pos(&self, _rhs: &Self) -> bool {
        true
    }
    fn eq_modulo_pos_and_reason(&self, _rhs: &Self) -> bool {
        true
    }
}

impl From<oxidized::pos::Pos> for NPos {
    fn from(pos: oxidized::pos::Pos) -> Self {
        Self::from_ast(&pos)
    }
}

impl<'a> From<&'a oxidized::pos::Pos> for NPos {
    fn from(pos: &'a oxidized::pos::Pos) -> Self {
        Self::from_ast(pos)
    }
}

impl ToOxidized for NPos {
    type Output = oxidized::pos::Pos;

    fn to_oxidized(self) -> Self::Output {
        oxidized::pos::Pos::NONE
    }
}

impl ToOcamlRep for NPos {
    fn to_ocamlrep<'a, A: ocamlrep::Allocator>(&'a self, alloc: &'a A) -> ocamlrep::Value<'a> {
        oxidized::pos::Pos::NONE.to_ocamlrep(alloc)
    }
}

impl FromOcamlRep for NPos {
    fn from_ocamlrep(_value: ocamlrep::Value<'_>) -> Result<Self, ocamlrep::FromError> {
        Ok(Self)
    }
}

#[derive(Clone, PartialEq, Eq, EqModuloPos, Hash)]
#[derive(Serialize, Deserialize)]
#[derive(ToOcamlRep, FromOcamlRep)]
pub struct Positioned<S, P> {
    // Caution: field order matters because we derive
    // `ToOcamlRep`/`FromOcamlRep` for this type.
    pos: P,
    id: S,
}

impl<S: fmt::Debug, P: fmt::Debug> fmt::Debug for Positioned<S, P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if std::mem::size_of::<P>() == 0 {
            write!(f, "{:?}", &self.id)
        } else {
            f.debug_tuple("").field(&self.pos).field(&self.id).finish()
        }
    }
}

impl<S, P> Positioned<S, P> {
    pub fn new(pos: P, id: S) -> Self {
        Self { pos, id }
    }

    pub fn pos(&self) -> &P {
        &self.pos
    }

    pub fn into_pos(self) -> P {
        self.pos
    }

    pub fn id_ref(&self) -> &S {
        &self.id
    }
}

impl<S: Copy, P> Positioned<S, P> {
    pub fn id(&self) -> S {
        self.id
    }
}

impl<S: From<String>, P: Pos> From<oxidized::ast_defs::Id> for Positioned<S, P> {
    fn from(pos_id: oxidized::ast_defs::Id) -> Self {
        let oxidized::ast_defs::Id(pos, id) = pos_id;
        Self::new(Pos::from_ast(&pos), S::from(id))
    }
}

impl<'a, S: From<&'a str>, P: Pos> From<&'a oxidized::ast_defs::Id> for Positioned<S, P> {
    fn from(pos_id: &'a oxidized::ast_defs::Id) -> Self {
        let oxidized::ast_defs::Id(pos, id) = pos_id;
        Self::new(Pos::from_ast(pos), S::from(id))
    }
}

impl<S: From<String>, P: Pos> From<oxidized::typing_defs::PosId> for Positioned<S, P> {
    fn from(pos_id: oxidized::typing_defs::PosId) -> Self {
        let (pos, id) = pos_id;
        Self::new(Pos::from_ast(&pos), S::from(id))
    }
}

impl<S: ToOxidized<Output = String>, P: Pos> ToOxidized for Positioned<S, P> {
    type Output = oxidized::typing_reason::PosId;

    fn to_oxidized(self) -> Self::Output {
        (self.pos.to_oxidized(), self.id.to_oxidized())
    }
}
