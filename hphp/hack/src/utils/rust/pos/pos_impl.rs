// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

use std::borrow::Cow;
use std::cmp::Ordering;
use std::ops::Range;
use std::sync::Arc;
use std::sync::OnceLock;

use eq_modulo_pos::EqModuloPos;
use relative_path::RelativePath;
use relative_path::RelativePathCtx;
use serde::Deserialize;
use serde::Serialize;

use crate::file_pos::FilePos;
use crate::file_pos_large::FilePosLarge;
use crate::file_pos_small::FilePosSmall;
use crate::pos_span_raw::PosSpanRaw;
use crate::pos_span_tiny::PosSpanTiny;
use crate::with_erased_lines::WithErasedLines;

/// The file of a position: an interned path. Equal paths are one value, made
/// once and never freed (in OCaml a position's file is a shared immutable
/// string), so a position holds a plain reference: copying a position is a
/// bit copy, dropping it is nothing, and two positions in one file compare
/// their paths by address. The path lives in an `Arc` that is never released
/// (`into_raw`), so `filename_rc` can still hand out an `Arc` of it.
/// Hashing, comparing, printing and serialising go through the path, exactly
/// as for the `Arc<RelativePath>` that positions used to hold.
#[derive(Clone, Copy)]
pub struct InternedPath(&'static RelativePath);

impl InternedPath {
    /// The interned copy of `path` (a lookup in the global table).
    pub fn new(path: &RelativePath) -> Self {
        Self(intern::by_value(path))
    }

    /// The interned copy of `*path`: consecutive calls nearly always pass
    /// the same `Arc`, which each thread remembers.
    #[inline]
    pub fn of_arc(path: &Arc<RelativePath>) -> Self {
        Self(intern::by_arc(path))
    }

    #[inline]
    pub fn get(self) -> &'static RelativePath {
        self.0
    }

    /// An `Arc` of the interned path (an increment of its reference count).
    pub fn to_arc(self) -> Arc<RelativePath> {
        let p: *const RelativePath = self.0;
        // SAFETY: every `InternedPath` points into an `Arc` leaked by
        // `intern::leak` (`Arc::into_raw`), whose count is never decremented
        // to zero: the allocation is alive and owned by an `Arc`.
        unsafe {
            Arc::increment_strong_count(p);
            Arc::from_raw(p)
        }
    }

    #[inline]
    pub fn ptr_eq(self, other: Self) -> bool {
        std::ptr::eq(self.0, other.0)
    }
}

impl std::ops::Deref for InternedPath {
    type Target = RelativePath;
    #[inline]
    fn deref(&self) -> &RelativePath {
        self.0
    }
}

impl std::hash::Hash for InternedPath {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // As `Arc<RelativePath>`: by value.
        self.0.hash(state)
    }
}

impl Serialize for InternedPath {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.0.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for InternedPath {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        Ok(Self::new(&RelativePath::deserialize(deserializer)?))
    }
}

impl std::fmt::Debug for InternedPath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

mod intern {
    use std::cell::RefCell;
    use std::collections::HashSet;
    use std::sync::Arc;
    use std::sync::OnceLock;
    use std::sync::RwLock;

    use relative_path::RelativePath;

    use crate::file_pos_large::FilePosLarge;

    fn leak(path: RelativePath) -> &'static RelativePath {
        // SAFETY: the `Arc` is never released, so the pointee lives forever.
        unsafe { &*Arc::into_raw(Arc::new(path)) }
    }

    fn table() -> &'static RwLock<HashSet<&'static RelativePath>> {
        static TABLE: OnceLock<RwLock<HashSet<&'static RelativePath>>> = OnceLock::new();
        TABLE.get_or_init(Default::default)
    }

    pub(super) fn by_value(path: &RelativePath) -> &'static RelativePath {
        if let Some(p) = table().read().unwrap().get(path) {
            return p;
        }
        let mut table = table().write().unwrap();
        if let Some(p) = table.get(path) {
            return p;
        }
        let p = leak(path.clone());
        table.insert(p);
        p
    }

    const SLOTS: usize = 64;
    type Slot = Option<(Arc<RelativePath>, &'static RelativePath)>;
    thread_local! {
        /// Direct-mapped by the address of the `Arc`. A slot keeps its `Arc`
        /// alive, so the address cannot be reused for another path while the
        /// slot holds it.
        static RECENT: RefCell<[Slot; SLOTS]> = const { RefCell::new([const { None }; SLOTS]) };
    }

    #[inline]
    pub(super) fn by_arc(path: &Arc<RelativePath>) -> &'static RelativePath {
        let addr = Arc::as_ptr(path) as usize;
        let slot = (addr >> 4 ^ addr >> 10) % SLOTS;
        RECENT
            .try_with(|recent| {
                let mut recent = recent.borrow_mut();
                match &recent[slot] {
                    Some((arc, p)) if Arc::ptr_eq(arc, path) => *p,
                    _ => {
                        let p = by_value(path);
                        recent[slot] = Some((Arc::clone(path), p));
                        p
                    }
                }
            })
            // (While the thread's locals are destroyed.)
            .unwrap_or_else(|_| by_value(path))
    }

    /// The spans of `Large` positions (a column past 511, rare: a few dozen
    /// lines in thousands of files), interned like paths so that a position
    /// holds no box.
    pub(super) fn large(span: (FilePosLarge, FilePosLarge)) -> &'static (FilePosLarge, FilePosLarge) {
        static TABLE: OnceLock<RwLock<HashSet<&'static (FilePosLarge, FilePosLarge)>>> =
            OnceLock::new();
        let table = TABLE.get_or_init(Default::default);
        if let Some(p) = table.read().unwrap().get(&span) {
            return p;
        }
        let mut table = table.write().unwrap();
        if let Some(p) = table.get(&span) {
            return p;
        }
        let p: &'static _ = Box::leak(Box::new(span));
        table.insert(p);
        p
    }
}

#[derive(Clone, Copy, Hash)]
enum PosImpl {
    Small {
        file: InternedPath,
        start: FilePosSmall,
        end: FilePosSmall,
    },
    Large {
        file: InternedPath,
        /// Interned (`intern::large`); hashes as the two boxes it replaces.
        span: &'static (FilePosLarge, FilePosLarge),
    },
    Tiny {
        /// Representation invariant: `RelativePath::EMPTY` is always encoded as
        /// `None`. This allows us to construct `Pos` in `const` contexts.
        file: Option<InternedPath>,
        span: PosSpanTiny,
    },
    // `FromReason(Box<PosImpl>)` was never constructed: removed (it was the
    // last variant, so the others keep their serialised indices).
}

/// The serialised form of `PosImpl`: the derived one of the representation
/// with `Arc<RelativePath>` files and boxed large positions.
#[derive(Serialize)]
#[serde(rename = "PosImpl")]
enum PosImplSer<'a> {
    Small {
        file: &'a RelativePath,
        start: FilePosSmall,
        end: FilePosSmall,
    },
    Large {
        file: &'a RelativePath,
        start: &'a FilePosLarge,
        end: &'a FilePosLarge,
    },
    Tiny {
        file: Option<&'a RelativePath>,
        span: PosSpanTiny,
    },
}

#[derive(Deserialize)]
#[serde(rename = "PosImpl")]
enum PosImplDe {
    Small {
        file: InternedPath,
        start: FilePosSmall,
        end: FilePosSmall,
    },
    Large {
        file: InternedPath,
        start: Box<FilePosLarge>,
        end: Box<FilePosLarge>,
    },
    Tiny {
        file: Option<InternedPath>,
        span: PosSpanTiny,
    },
}

impl Serialize for PosImpl {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self {
            PosImpl::Small { file, start, end } => PosImplSer::Small {
                file: file.get(),
                start: *start,
                end: *end,
            },
            PosImpl::Large { file, span } => PosImplSer::Large {
                file: file.get(),
                start: &span.0,
                end: &span.1,
            },
            PosImpl::Tiny { file, span } => PosImplSer::Tiny {
                file: file.map(InternedPath::get),
                span: *span,
            },
        }
        .serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for PosImpl {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        Ok(match PosImplDe::deserialize(deserializer)? {
            PosImplDe::Small { file, start, end } => PosImpl::Small { file, start, end },
            PosImplDe::Large { file, start, end } => PosImpl::Large {
                file,
                span: intern::large((*start, *end)),
            },
            PosImplDe::Tiny { file, span } => PosImpl::Tiny { file, span },
        })
    }
}

/// A position: what `PosImpl` says, packed in three words (24 bytes, where
/// the enum takes 32). `file` is `None` only for a `Tiny` position in the
/// empty path. `b` is the end of a `Small` position (a `FilePosSmall`, whose
/// top bit is clear unless it is the dummy, all ones), or a tag: `TAG_TINY`
/// (`a` is the span) or `TAG_LARGE` (`a` is the interned span).
#[derive(Clone, Copy)]
pub struct Pos {
    file: Option<InternedPath>,
    a: Word,
    b: u64,
}

#[derive(Clone, Copy)]
union Word {
    bits: u64,
    large: &'static (FilePosLarge, FilePosLarge),
}

const TAG_TINY: u64 = 1 << 63;
const TAG_LARGE: u64 = (1 << 63) | 1;

impl Pos {
    #[inline]
    fn pack(p: PosImpl) -> Self {
        match p {
            PosImpl::Small { file, start, end } => {
                debug_assert!(end.to_bits() != TAG_TINY && end.to_bits() != TAG_LARGE);
                Pos {
                    file: Some(file),
                    a: Word {
                        bits: start.to_bits(),
                    },
                    b: end.to_bits(),
                }
            }
            PosImpl::Large { file, span } => Pos {
                file: Some(file),
                a: Word { large: span },
                b: TAG_LARGE,
            },
            PosImpl::Tiny { file, span } => Pos {
                file,
                a: Word {
                    bits: span.to_bits(),
                },
                b: TAG_TINY,
            },
        }
    }

    #[inline]
    fn imp(&self) -> PosImpl {
        // SAFETY: `pack` stores the field of `a` that the tag in `b` says,
        // and a file for `Small` and `Large`.
        unsafe {
            match self.b {
                TAG_TINY => PosImpl::Tiny {
                    file: self.file,
                    span: PosSpanTiny::from_bits(self.a.bits),
                },
                TAG_LARGE => PosImpl::Large {
                    file: self.file.unwrap_unchecked(),
                    span: self.a.large,
                },
                _ => PosImpl::Small {
                    file: self.file.unwrap_unchecked(),
                    start: FilePosSmall::from_bits(self.a.bits),
                    end: FilePosSmall::from_bits(self.b),
                },
            }
        }
    }
}

/// Serialised as before: the newtype `Pos(PosImpl)`.
#[derive(Serialize, Deserialize)]
#[serde(rename = "Pos")]
struct PosSer(PosImpl);

impl Serialize for Pos {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        PosSer(self.imp()).serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for Pos {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let PosSer(p) = PosSer::deserialize(deserializer)?;
        if let PosImpl::Small { end, .. } = p {
            let end = end.to_bits();
            if end == TAG_TINY || end == TAG_LARGE {
                return Err(serde::de::Error::custom("invalid FilePosSmall"));
            }
        }
        Ok(Pos::pack(p))
    }
}

pub type PosR<'a> = &'a Pos;

static EMPTY_PATH: RelativePath = RelativePath::EMPTY;

impl Pos {
    pub const NONE: Self = Pos {
        file: None,
        a: Word {
            bits: PosSpanTiny::make_dummy().to_bits(),
        },
        b: TAG_TINY,
    };
    pub fn is_none(&self) -> bool {
        match self.imp() {
            PosImpl::Tiny { file, span } => span.is_dummy() && file.is_none(),
            _ => false,
        }
    }

    // Validness based on HHVM's definition
    pub fn is_valid(&self) -> bool {
        let (line0, line1, char0, char1) = self.info_pos_extended();
        line0 != 1 || char0 != 1 || line1 != 1 || char1 != 1
    }

    pub fn from_raw_span(file: Arc<RelativePath>, span: PosSpanRaw) -> Self {
        Self::from_raw_span_interned(InternedPath::of_arc(&file), span)
    }

    /// `from_raw_span` with an interned file (no lookup).
    pub fn from_raw_span_interned(file: InternedPath, span: PosSpanRaw) -> Self {
        if let Some(span) = PosSpanTiny::make(&span.start, &span.end) {
            return Pos::pack(PosImpl::Tiny {
                file: if file.is_empty() { None } else { Some(file) },
                span,
            });
        }
        let (lnum, bol, offset) = span.start.line_beg_offset();
        if let Some(start) = FilePosSmall::from_lnum_bol_offset(lnum, bol, offset) {
            let (lnum, bol, offset) = span.end.line_beg_offset();
            if let Some(end) = FilePosSmall::from_lnum_bol_offset(lnum, bol, offset) {
                return Pos::pack(PosImpl::Small { file, start, end });
            }
        }
        Pos::pack(PosImpl::Large {
            file,
            span: intern::large((span.start, span.end)),
        })
    }

    /// `from_raw_span_interned(file, span.to_raw_span())` for a tiny span,
    /// without the round trip through the raw span (making a tiny span of
    /// the raw span of a tiny span gives it back).
    #[inline]
    pub fn from_tiny_span_interned(file: InternedPath, span: PosSpanTiny) -> Self {
        Pos::pack(PosImpl::Tiny {
            file: if file.is_empty() { None } else { Some(file) },
            span,
        })
    }

    /// The span of a `Tiny` position.
    #[inline]
    pub fn as_tiny_span(&self) -> Option<PosSpanTiny> {
        match self.imp() {
            PosImpl::Tiny { span, .. } => Some(span),
            _ => None,
        }
    }

    /// A position in the file of `self` with the given span.
    pub fn with_raw_span(&self, span: PosSpanRaw) -> Self {
        Self::from_raw_span_interned(self.interned_filename(), span)
    }

    /// The interned file of the position.
    pub fn interned_filename(&self) -> InternedPath {
        match self.file() {
            Some(file) => file,
            None => {
                static EMPTY: OnceLock<InternedPath> = OnceLock::new();
                *EMPTY.get_or_init(|| InternedPath::new(&RelativePath::EMPTY))
            }
        }
    }

    pub fn to_raw_span(&self) -> PosSpanRaw {
        match &self.imp() {
            PosImpl::Tiny { span, .. } => span.to_raw_span(),
            PosImpl::Small { start, end, .. } => PosSpanRaw {
                start: (*start).into(),
                end: (*end).into(),
            },
            PosImpl::Large { span, .. } => PosSpanRaw {
                start: span.0,
                end: span.1,
            },
        }
    }

    /// The file of the position, if it has one (`Tiny` positions in the
    /// empty path have none).
    #[inline]
    fn file(&self) -> Option<InternedPath> {
        self.file
    }

    pub fn filename(&self) -> &'static RelativePath {
        match self.file() {
            Some(file) => file.get(),
            None => &EMPTY_PATH,
        }
    }

    pub fn filename_rc(&self) -> Arc<RelativePath> {
        self.interned_filename().to_arc()
    }

    /// Returns a closed interval that's incorrect for multi-line spans.
    pub fn info_pos(&self) -> (usize, usize, usize) {
        fn compute<P: FilePos>(pos_start: &P, pos_end: &P) -> (usize, usize, usize) {
            let (line, start_minus1, bol) = pos_start.line_column_beg();
            let start = start_minus1.wrapping_add(1);
            let end_offset = pos_end.offset();
            let mut end = end_offset - bol;
            // To represent the empty interval, pos_start and pos_end are equal because
            // end_offset is exclusive. Here, it's best for error messages to the user if
            // we print characters N to N (highlighting a single character) rather than characters
            // N to (N-1), which is very unintuitive.
            if end == start_minus1 {
                end = start
            }
            (line, start, end)
        }
        match &self.imp() {
            PosImpl::Small { start, end, .. } => compute(start, end),
            PosImpl::Large { span, .. } => compute(&span.0, &span.1),
            PosImpl::Tiny { span, .. } => {
                let PosSpanRaw { start, end } = span.to_raw_span();
                compute(&start, &end)
            }
        }
    }

    /// Returns (start_line, end_line, start_col, end_col) for multi-line spans.
    pub fn info_pos_extended(&self) -> (usize, usize, usize, usize) {
        let (line_begin, start, end) = self.info_pos();
        let line_end = match &self.imp() {
            PosImpl::Small { end, .. } => end.line_column_beg(),
            PosImpl::Large { span, .. } => span.1.line_column_beg(),
            PosImpl::Tiny { span, .. } => span.to_raw_span().end.line_column_beg(),
        }
        .0;
        (line_begin, line_end, start, end)
    }

    pub fn info_raw(&self) -> (usize, usize) {
        (self.start_offset(), self.end_offset())
    }

    pub fn line(&self) -> usize {
        match &self.imp() {
            PosImpl::Small { start, .. } => start.line(),
            PosImpl::Large { span, .. } => span.0.line(),
            PosImpl::Tiny { span, .. } => span.start_line_number(),
        }
    }

    pub fn from_lnum_bol_offset(
        file: Arc<RelativePath>,
        start: (usize, usize, usize),
        end: (usize, usize, usize),
    ) -> Self {
        let (start_line, start_bol, start_offset) = start;
        let (end_line, end_bol, end_offset) = end;
        let start = FilePosLarge::from_lnum_bol_offset(start_line, start_bol, start_offset);
        let end = FilePosLarge::from_lnum_bol_offset(end_line, end_bol, end_offset);
        Self::from_raw_span(file, PosSpanRaw { start, end })
    }

    pub fn to_start_and_end_lnum_bol_offset(
        &self,
    ) -> ((usize, usize, usize), (usize, usize, usize)) {
        match &self.imp() {
            PosImpl::Small { start, end, .. } => (start.line_beg_offset(), end.line_beg_offset()),
            PosImpl::Large { span, .. } => (span.0.line_beg_offset(), span.1.line_beg_offset()),
            PosImpl::Tiny { span, .. } => {
                let PosSpanRaw { start, end } = span.to_raw_span();
                (start.line_beg_offset(), end.line_beg_offset())
            }
        }
    }

    /// For single-line spans only.
    pub fn from_line_cols_offset(
        file: Arc<RelativePath>,
        line: usize,
        cols: Range<usize>,
        start_offset: usize,
    ) -> Self {
        let start = FilePosLarge::from_line_column_offset(line, cols.start, start_offset);
        let end = FilePosLarge::from_line_column_offset(
            line,
            cols.end,
            start_offset + (cols.end - cols.start),
        );
        Self::from_raw_span(file, PosSpanRaw { start, end })
    }

    pub fn btw_nocheck(x1: Self, x2: Self) -> Self {
        let start = x1.to_raw_span().start;
        let end = x2.to_raw_span().end;
        x1.with_raw_span(PosSpanRaw { start, end })
    }

    pub fn btw(x1: &Self, x2: &Self) -> Result<Self, String> {
        if x1.filename() != x2.filename() {
            // using string concatenation instead of format!,
            // it is not stable see T52404885
            Err(String::from("Position in separate files ")
                + &x1.filename().to_string()
                + " and "
                + &x2.filename().to_string())
        } else if x1.end_offset() > x2.end_offset() {
            Err(String::from("btw: invalid positions")
                + &x1.end_offset().to_string()
                + "and"
                + &x2.end_offset().to_string())
        } else {
            Ok(Self::btw_nocheck(x1.clone(), x2.clone()))
        }
    }

    pub fn merge(x1: &Self, x2: &Self) -> Result<Self, String> {
        if x1.filename() != x2.filename() {
            // see comment above (T52404885)
            return Err(String::from("Position in separate files ")
                + &x1.filename().to_string()
                + " and "
                + &x2.filename().to_string());
        }

        let span1 = x1.to_raw_span();
        let span2 = x2.to_raw_span();

        let start = if span1.start.is_dummy() {
            span2.start
        } else if span2.start.is_dummy() || span1.start.offset() < span2.start.offset() {
            span1.start
        } else {
            span2.start
        };

        let end = if span1.end.is_dummy() {
            span2.end
        } else if span2.end.is_dummy() || span1.end.offset() >= span2.end.offset() {
            span1.end
        } else {
            span2.end
        };

        Ok(x1.with_raw_span(PosSpanRaw { start, end }))
    }

    /// Return the smallest position containing both given positions (if they
    /// are both in the same file). The returned position will have the
    /// filename of the first Pos argument.
    ///
    /// For merging positions that may not occur within the same file, use
    /// `Pos::merge`.
    pub fn merge_without_checking_filename(x1: &Self, x2: &Self) -> Self {
        let span1 = x1.to_raw_span();
        let span2 = x2.to_raw_span();

        let start = if span1.start.is_dummy() {
            span2.start
        } else if span2.start.is_dummy() || span1.start.offset() < span2.start.offset() {
            span1.start
        } else {
            span2.start
        };

        let end = if span1.end.is_dummy() {
            span2.end
        } else if span2.end.is_dummy() {
            span1.end
        } else if span1.end.offset() < span2.end.offset() {
            span2.end
        } else {
            span1.end
        };

        x1.with_raw_span(PosSpanRaw { start, end })
    }

    pub fn last_char(&self) -> Cow<'_, Self> {
        if self.is_none() {
            Cow::Borrowed(self)
        } else {
            let end = self.to_raw_span().end;
            Cow::Owned(self.with_raw_span(PosSpanRaw { start: end, end }))
        }
    }

    pub fn first_char_of_line(&self) -> Cow<'_, Self> {
        if self.is_none() {
            Cow::Borrowed(self)
        } else {
            let start = self.to_raw_span().start.with_column(0);
            Cow::Owned(self.with_raw_span(PosSpanRaw { start, end: start }))
        }
    }

    pub fn end_offset(&self) -> usize {
        match &self.imp() {
            PosImpl::Small { end, .. } => end.offset(),
            PosImpl::Large { span, .. } => span.1.offset(),
            PosImpl::Tiny { span, .. } => span.end_offset(),
        }
    }

    pub fn start_offset(&self) -> usize {
        match &self.imp() {
            PosImpl::Small { start, .. } => start.offset(),
            PosImpl::Large { span, .. } => span.0.offset(),
            PosImpl::Tiny { span, .. } => span.start_offset(),
        }
    }
}

impl std::fmt::Display for Pos {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn do_fmt<P: FilePos>(
            f: &mut std::fmt::Formatter<'_>,
            file: &RelativePath,
            start: &P,
            end: &P,
        ) -> std::fmt::Result {
            write!(f, "{}", file)?;
            let (start_line, start_col, _) = start.line_column_beg();
            let (end_line, end_col, _) = end.line_column_beg();
            // Use a format string rather than Formatter::debug_tuple to prevent
            // adding line breaks. Positions occur very frequently in ASTs and
            // types, so the Debug implementation of those data structures is
            // more readable if we minimize the vertical space taken up by
            // positions. Depends upon RelativePath's implementation of Display
            // also being single-line.
            if start_line == end_line {
                write!(f, "({}:{}-{})", start_line, start_col, end_col)
            } else {
                write!(f, "({}:{}-{}:{})", start_line, start_col, end_line, end_col)
            }
        }
        match &self.imp() {
            PosImpl::Small {
                file, start, end, ..
            } => do_fmt(f, file, start, end),
            PosImpl::Large { file, span } => do_fmt(f, file, &span.0, &span.1),
            PosImpl::Tiny { span, .. } => {
                if self.is_none() {
                    return write!(f, "Pos::NONE");
                }
                let PosSpanRaw { start, end } = span.to_raw_span();
                do_fmt(f, self.filename(), &start, &end)
            }
        }
    }
}

impl std::fmt::Debug for Pos {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use PosImpl::*;
        fn do_fmt<P: FilePos>(
            f: &mut std::fmt::Formatter<'_>,
            file: &RelativePath,
            start: &P,
            end: &P,
        ) -> std::fmt::Result {
            let (start_line, start_col, _) = start.line_column_beg();
            let (end_line, end_col, _) = end.line_column_beg();
            // Use a format string rather than Formatter::debug_tuple to prevent
            // adding line breaks. Positions occur very frequently in ASTs and
            // types, so the Debug implementation of those data structures is
            // more readable if we minimize the vertical space taken up by
            // positions. Depends upon RelativePath's implementation of Display
            // also being single-line.
            if start_line == end_line {
                write!(f, "{}({}:{}-{})", &file, &start_line, &start_col, &end_col,)
            } else {
                write!(
                    f,
                    "{}({}:{}-{}:{})",
                    &file, &start_line, &start_col, &end_line, &end_col,
                )
            }
        }
        match &self.imp() {
            Small { file, start, end } => do_fmt(f, file, start, end),
            Large { file, span } => do_fmt(f, file, &span.0, &span.1),
            Tiny { file, span } => {
                if self.is_none() {
                    return write!(f, "Pos::NONE");
                }
                let file = file.as_deref().unwrap_or(&EMPTY_PATH);
                let PosSpanRaw { start, end } = span.to_raw_span();
                do_fmt(f, file, &start, &end)
            }
        }
    }
}

impl Default for Pos {
    fn default() -> Self {
        Self::NONE
    }
}

impl Ord for Pos {
    // Intended to match the implementation of `Pos.compare` in OCaml.
    fn cmp(&self, other: &Pos) -> Ordering {
        // Paths are interned: two positions in one file share the path, which
        // is then equal without comparing it.
        let same_file = match (self.file(), other.file()) {
            (Some(f1), Some(f2)) => f1.ptr_eq(f2),
            _ => false,
        };
        (if same_file {
            Ordering::Equal
        } else {
            self.filename().cmp(other.filename())
        })
        .then_with(|| self.start_offset().cmp(&other.start_offset()))
            .then(self.end_offset().cmp(&other.end_offset()))
    }
}

impl PartialOrd for Pos {
    fn partial_cmp(&self, other: &Pos) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for Pos {
    fn eq(&self, other: &Self) -> bool {
        // `cmp` is `Equal` when the paths and both offsets are. Interned paths
        // are equal exactly when they are the same path (a `Tiny` position in
        // the empty path has none: compare those by value).
        match (self.file(), other.file()) {
            (Some(f1), Some(f2)) => {
                f1.ptr_eq(f2)
                    && self.start_offset() == other.start_offset()
                    && self.end_offset() == other.end_offset()
            }
            _ => self.cmp(other) == Ordering::Equal,
        }
    }
}

impl Eq for Pos {}

// non-derived impl Hash because PartialEq and Eq are non-derived
impl std::hash::Hash for Pos {
    fn hash<H: std::hash::Hasher>(&self, hasher: &mut H) {
        // As the derived `Hash` of the enum the position was.
        self.imp().hash(hasher)
    }
}

impl EqModuloPos for Pos {
    fn eq_modulo_pos(&self, _rhs: &Self) -> bool {
        true
    }
    fn eq_modulo_pos_and_reason(&self, _rhs: &Self) -> bool {
        true
    }
}

impl Pos {
    /// Returns a struct implementing Display which produces the same format as
    /// `Pos.string` in OCaml.
    pub fn string(&self) -> PosString<'_> {
        PosString(self, None)
    }

    pub fn absolute<'a>(&'a self, ctx: &'a RelativePathCtx) -> PosString<'a> {
        PosString(self, Some(ctx))
    }
}

/// This struct has an impl of Display which produces the same format as
/// `Pos.string` in OCaml.
pub struct PosString<'a>(&'a Pos, Option<&'a RelativePathCtx>);

impl std::fmt::Display for PosString<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self(pos, ctx) = self;
        let path = match ctx {
            Some(ctx) => pos.filename().to_absolute(ctx),
            None => pos.filename().path().to_owned(),
        };
        let (line, start, end) = pos.info_pos();
        write!(
            f,
            "File {:?}, line {}, characters {}-{}:",
            path.display(),
            line,
            start,
            end
        )
    }
}

// NoPosHash is meant to be position-insensitive, so don't do anything!
impl no_pos_hash::NoPosHash for Pos {
    fn hash<H: std::hash::Hasher>(&self, _state: &mut H) {}
}

impl WithErasedLines for Pos {
    fn with_erased_lines(self) -> Self {
        let span = self.to_raw_span().with_erased_lines();
        self.with_raw_span(span)
    }
}
pub mod map {
    pub type Map<T> = std::collections::BTreeMap<super::Pos, T>;
}

impl From<parser_core_types::indexed_source_text::Pos> for Pos {
    fn from(pos: parser_core_types::indexed_source_text::Pos) -> Self {
        Self::from_lnum_bol_offset(pos.path, pos.start, pos.end)
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use pretty_assertions::assert_eq;
    use relative_path::Prefix;

    use super::*;

    fn make_pos(name: &str, start: (usize, usize, usize), end: (usize, usize, usize)) -> Pos {
        Pos::from_lnum_bol_offset(
            Arc::new(RelativePath::make(Prefix::Dummy, PathBuf::from(name))),
            start,
            end,
        )
    }

    #[test]
    fn test_pos() {
        assert!(Pos::NONE.is_none());
        assert!(
            !Pos::from_lnum_bol_offset(
                Arc::new(RelativePath::make(Prefix::Dummy, PathBuf::from("a"))),
                (0, 0, 0),
                (0, 0, 0)
            )
            .is_none(),
        );
        assert!(
            !Pos::from_lnum_bol_offset(
                Arc::new(RelativePath::make(Prefix::Dummy, PathBuf::from(""))),
                (1, 0, 0),
                (0, 0, 0)
            )
            .is_none(),
        );
    }

    #[test]
    fn test_pos_absolute() {
        let ctx = RelativePathCtx {
            dummy: PathBuf::from("dummy"),
            ..Default::default()
        };
        assert_eq!(
            Pos::NONE.absolute(&ctx).to_string(),
            r#"File "dummy/", line 0, characters 0-0:"#
        );
        let path = Arc::new(RelativePath::make(Prefix::Dummy, PathBuf::from("a.php")));
        assert_eq!(
            Pos::from_lnum_bol_offset(path, (5, 100, 117), (5, 100, 142))
                .absolute(&ctx)
                .to_string(),
            r#"File "dummy/a.php", line 5, characters 18-42:"#
        );
    }

    #[test]
    fn test_pos_string() {
        assert_eq!(
            Pos::NONE.string().to_string(),
            r#"File "", line 0, characters 0-0:"#
        );
        let path = Arc::new(RelativePath::make(Prefix::Dummy, PathBuf::from("a.php")));
        assert_eq!(
            Pos::from_lnum_bol_offset(path, (5, 100, 117), (5, 100, 142))
                .string()
                .to_string(),
            r#"File "a.php", line 5, characters 18-42:"#
        );
    }

    #[test]
    fn test_pos_merge() {
        let test = |name, (exp_start, exp_end), ((fst_start, fst_end), (snd_start, snd_end))| {
            assert_eq!(
                Ok(make_pos("a", exp_start, exp_end)),
                Pos::merge(
                    &make_pos("a", fst_start, fst_end),
                    &make_pos("a", snd_start, snd_end)
                ),
                "{}",
                name
            );

            // Run this again because we want to test that we get the same
            // result regardless of order.
            assert_eq!(
                Ok(make_pos("a", exp_start, exp_end)),
                Pos::merge(
                    &make_pos("a", snd_start, snd_end),
                    &make_pos("a", fst_start, fst_end),
                ),
                "{} (reversed)",
                name
            );
        };

        test(
            "basic test",
            ((0, 0, 0), (0, 0, 5)),
            (((0, 0, 0), (0, 0, 2)), ((0, 0, 2), (0, 0, 5))),
        );

        test(
            "merge should work with gaps",
            ((0, 0, 0), (0, 0, 15)),
            (((0, 0, 0), (0, 0, 5)), ((0, 0, 10), (0, 0, 15))),
        );

        test(
            "merge should work with overlaps",
            ((0, 0, 0), (0, 0, 15)),
            (((0, 0, 0), (0, 0, 12)), ((0, 0, 7), (0, 0, 15))),
        );

        test(
            "merge should work between lines",
            ((0, 0, 0), (2, 20, 25)),
            (((0, 0, 0), (1, 10, 15)), ((1, 10, 20), (2, 20, 25))),
        );

        assert_eq!(
            Err("Position in separate files |a and |b".to_string()),
            Pos::merge(
                &make_pos("a", (0, 0, 0), (0, 0, 0)),
                &make_pos("b", (0, 0, 0), (0, 0, 0))
            ),
            "should reject merges with different filenames"
        );
    }
}

// ---- OCaml interop (feature "ocamlrep") ----
#[cfg(feature = "ocamlrep")]
mod ocamlrep_impls {
    use ocamlrep::FromOcamlRep;
    use ocamlrep::ToOcamlRep;

    use super::*;

    impl ToOcamlRep for InternedPath {
        fn to_ocamlrep<'a, A: ocamlrep::Allocator>(&'a self, alloc: &'a A) -> ocamlrep::Value<'a> {
            // Memoized by the address of the interned path, as the `Arc` that
            // positions used to hold was: the positions of a file share one
            // OCaml path instead of copying it each.
            let path: &'static RelativePath = self.0;
            alloc.memoized(
                path as *const RelativePath as usize,
                std::mem::size_of::<RelativePath>(),
                |alloc| alloc.add(path),
            )
        }
    }

    impl FromOcamlRep for InternedPath {
        fn from_ocamlrep(value: ocamlrep::Value<'_>) -> Result<Self, ocamlrep::FromError> {
            Ok(InternedPath::new(&RelativePath::from_ocamlrep(value)?))
        }
    }

    /// The OCaml value of a position is that of `PosImpl` (in OCaml, `Pos.t`).
    impl ToOcamlRep for Pos {
        fn to_ocamlrep<'a, A: ocamlrep::Allocator>(&'a self, alloc: &'a A) -> ocamlrep::Value<'a> {
            match self.imp() {
                PosImpl::Small { file, start, end } => {
                    let mut block = alloc.block_with_size_and_tag(3, 0);
                    alloc.set_field(&mut block, 0, alloc.add_copy(file));
                    alloc.set_field(&mut block, 1, alloc.add_copy(start));
                    alloc.set_field(&mut block, 2, alloc.add_copy(end));
                    block.build()
                }
                PosImpl::Large { file, span } => {
                    let mut block = alloc.block_with_size_and_tag(3, 1);
                    alloc.set_field(&mut block, 0, alloc.add_copy(file));
                    alloc.set_field(&mut block, 1, alloc.add(&span.0));
                    alloc.set_field(&mut block, 2, alloc.add(&span.1));
                    block.build()
                }
                PosImpl::Tiny { file, span } => {
                    let file = match file {
                        Some(file) => alloc.add_copy(file),
                        None => alloc.add(&RelativePath::EMPTY),
                    };
                    let mut block = alloc.block_with_size_and_tag(2, 2);
                    alloc.set_field(&mut block, 0, file);
                    alloc.set_field(&mut block, 1, alloc.add_copy(span));
                    block.build()
                }
            }
        }
    }

    impl FromOcamlRep for Pos {
        fn from_ocamlrep(value: ocamlrep::Value<'_>) -> Result<Self, ocamlrep::FromError> {
            use ocamlrep::from;
            let block = from::expect_block(value)?;
            match block.tag() {
                0 => {
                    from::expect_block_size(block, 3)?;
                    Ok(Pos::pack(PosImpl::Small {
                        file: from::field(block, 0)?,
                        start: from::field(block, 1)?,
                        end: from::field(block, 2)?,
                    }))
                }
                1 => {
                    from::expect_block_size(block, 3)?;
                    let start: FilePosLarge = from::field(block, 1)?;
                    let end: FilePosLarge = from::field(block, 2)?;
                    Ok(Pos::pack(PosImpl::Large {
                        file: from::field(block, 0)?,
                        span: intern::large((start, end)),
                    }))
                }
                2 => {
                    from::expect_block_size(block, 2)?;
                    let file: RelativePath = from::field(block, 0)?;
                    Ok(Pos::pack(PosImpl::Tiny {
                        file: if file.is_empty() {
                            None
                        } else {
                            Some(InternedPath::new(&file))
                        },
                        span: from::field(block, 1)?,
                    }))
                }
                // Tag 3 was `Pos_from_reason`, which is never constructed.
                tag => Err(ocamlrep::FromError::BlockTagOutOfRange {
                    max: 2,
                    actual: tag,
                }),
            }
        }
    }

    #[cfg(test)]
    mod tests {
        use std::path::PathBuf;

        use relative_path::Prefix;

        use super::*;

        #[test]
        fn test_tiny_positions_share_their_path_in_ocaml() {
            let path = Arc::new(RelativePath::make(Prefix::Root, PathBuf::from("a.php")));
            let first = Pos::from_lnum_bol_offset(Arc::clone(&path), (1, 0, 0), (1, 0, 5));
            let second = Pos::from_lnum_bol_offset(path, (2, 6, 6), (2, 6, 9));
            assert!(
                matches!(first.imp(), PosImpl::Tiny { file: Some(_), .. }),
                "a short span with a path should be Tiny"
            );
            let pair = (first, second);
            let arena = ocamlrep::Arena::new();
            let positions = arena.add_root(&pair);
            let path_of = |index| {
                positions
                    .field(index)
                    .and_then(|pos| pos.field(0))
                    .expect("a Tiny position block should have its path as field 0")
                    .to_bits()
            };
            assert_eq!(
                path_of(0),
                path_of(1),
                "both positions should point at one OCaml path"
            );
            let first_back = Pos::from_ocamlrep(positions.field(0).unwrap()).unwrap();
            assert_eq!(first_back, first);
        }
    }
}
