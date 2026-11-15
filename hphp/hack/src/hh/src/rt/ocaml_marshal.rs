// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of OCaml's `Marshal` (`runtime/extern.c`, `runtime/intern.c` of OCaml
//! 5, the version of the OCaml `hh_server`), for the values that files shared
//! with the OCaml binaries hold: `errors.bin` (`Server_progress.ErrorsFile`),
//! the saved state's `B.err`/`B.warn` and the naming table's
//! `NAMING_LOCAL_CHANGES`.
//!
//! # The value model
//!
//! A [`Value`] is an OCaml value: an immediate integer, or a pointer to an
//! [`Obj`] (a block with a tag and fields, a string, a boxed float, a float
//! array). Pointers are `Rc`s, and **an `Rc` shared between two places is a
//! physically shared OCaml object**: [`to_bytes`] writes the second
//! occurrence as a shared reference (`CODE_SHARED*`), exactly as `extern.c`
//! does for a block it has already written, and [`from_bytes`] returns the
//! same `Rc` for every reference to one object. So decoding then encoding
//! gives back the same bytes, and a writer that wants OCaml's bytes for a
//! value must share where the OCaml program shares (and nowhere else).
//! Blocks of size 0 (atoms) are never shared, as in OCaml.
//!
//! What is written is what `Marshal.to_bytes v []` writes on a 64-bit
//! little-endian machine: the 20-byte small header (or the 32-byte big one
//! when a size passes 2^32), then the data, in the order of `extern_rec`
//! (a block's header, then its fields from the first to the last). The
//! flags `No_sharing` and `Compat_32` are supported; `Closures` is not
//! (there are no closures in these files). On read, every code of
//! `intern.c` is accepted except code pointers and custom blocks other than
//! `Int64.t` ([`Obj::Int64`], which the naming table's local changes hold;
//! these files contain no other).
//!
//! # Typed values
//!
//! [`ToOcaml`] and [`FromOcaml`] convert Rust values to and from their
//! OCaml representation: `int` and `bool` are immediates, `string` a string,
//! `float` a boxed float, `'a option` `None` = 0 or a block of tag 0, `'a
//! list` the cons cells (`[]` = 0, `x :: l` a block of tag 0 `[x; l]`),
//! tuples blocks of tag 0. Variants and records are built with
//! [`Value::block`] and [`Value::int`]: constant constructors are the
//! integers 0, 1... in their order, non-constant ones blocks tagged 0, 1...
//! in theirs; a record (or an inline record) is a block of tag 0 (the
//! constructor's tag) with its fields in order; a polymorphic variant is
//! [`hash_variant`] of its name, or a block `[hash; argument]` of tag 0.
//! `Map.Make` maps and `Set.Make` sets are AVL trees whose shape depends on
//! how they were built: [`ocaml_map`] and [`ocaml_set`] build them as the
//! stdlib does (`add`, `filter`) and read them in key order.

use std::collections::HashMap;
use std::rc::Rc;

/// An OCaml value.
#[derive(Clone)]
pub enum Value {
    /// An immediate integer (`int`, `bool`, `char`, constant constructors).
    Int(i64),
    /// A pointer to a heap object. Sharing the `Rc` shares the object.
    Ptr(Rc<Obj>),
}

/// An object of the OCaml heap.
#[derive(Clone, Debug, PartialEq)]
pub enum Obj {
    /// A structured block (tag below `No_scan_tag`, 251).
    Block { tag: u8, fields: Vec<Value> },
    /// A string (`String_tag`, 252).
    String(Vec<u8>),
    /// A boxed float (`Double_tag`, 253).
    Double(f64),
    /// A float array or an all-float record (`Double_array_tag`, 254).
    DoubleArray(Vec<f64>),
    /// A boxed `Int64.t` (a custom block of `caml_int64_ops`, identifier
    /// `_j`: what `Marshal` writes with `CODE_CUSTOM_FIXED`). The only custom
    /// blocks supported (for the `NAMING_LOCAL_CHANGES` blob, whose decl
    /// hashes are `Int64.t option`).
    Int64(i64),
}

/// Without this, dropping a long list (a chain of `Rc`s) would recurse once
/// per element and overflow the stack: the fields of the blocks that
/// nothing else holds are dropped from a work list instead.
impl Drop for Obj {
    fn drop(&mut self) {
        if let Obj::Block { fields, .. } = self {
            if fields.is_empty() {
                return;
            }
            let mut work: Vec<Value> = std::mem::take(fields);
            while let Some(v) = work.pop() {
                if let Value::Ptr(rc) = v {
                    if let Ok(mut obj) = Rc::try_unwrap(rc) {
                        if let Obj::Block { fields, .. } = &mut obj {
                            work.append(fields);
                        }
                    }
                }
            }
        }
    }
}

pub const DOUBLE_ARRAY_TAG: u8 = 254;
pub const DOUBLE_TAG: u8 = 253;
pub const STRING_TAG: u8 = 252;
pub const NO_SCAN_TAG: u8 = 251;

impl Value {
    /// An immediate integer.
    pub fn int(n: i64) -> Value {
        Value::Int(n)
    }

    pub fn bool(b: bool) -> Value {
        Value::Int(b as i64)
    }

    /// A new block (not shared with any other).
    pub fn block(tag: u8, fields: Vec<Value>) -> Value {
        Value::Ptr(Rc::new(Obj::Block { tag, fields }))
    }

    /// A new string.
    pub fn string(bytes: impl Into<Vec<u8>>) -> Value {
        Value::Ptr(Rc::new(Obj::String(bytes.into())))
    }

    /// A new boxed float.
    pub fn double(f: f64) -> Value {
        Value::Ptr(Rc::new(Obj::Double(f)))
    }

    /// A new boxed `Int64.t`.
    pub fn int64(n: i64) -> Value {
        Value::Ptr(Rc::new(Obj::Int64(n)))
    }

    /// The integer 0, i.e. `()`, `[]`, `None`, `false` and the first
    /// constant constructor.
    pub fn unit() -> Value {
        Value::Int(0)
    }

    /// `Some v`
    pub fn some(v: Value) -> Value {
        Value::block(0, vec![v])
    }

    /// The OCaml list of `items` (head first).
    pub fn list(items: impl IntoIterator<Item = Value, IntoIter: DoubleEndedIterator>) -> Value {
        let mut l = Value::Int(0);
        for x in items.into_iter().rev() {
            l = Value::block(0, vec![x, l]);
        }
        l
    }

    /// A polymorphic variant: `` `Name `` (no argument) or `` `Name arg ``.
    pub fn poly_variant(name: &str, arg: Option<Value>) -> Value {
        let hash = Value::Int(hash_variant(name));
        match arg {
            None => hash,
            Some(arg) => Value::block(0, vec![hash, arg]),
        }
    }

    pub fn as_int(&self) -> Result<i64, ConvError> {
        match self {
            Value::Int(n) => Ok(*n),
            Value::Ptr(_) => Err(ConvError::expected("an integer", self)),
        }
    }

    /// The tag and fields of a block (of any size, so atoms too).
    pub fn as_block(&self) -> Result<(u8, &[Value]), ConvError> {
        match self {
            Value::Ptr(obj) => match &**obj {
                Obj::Block { tag, fields } => Ok((*tag, fields)),
                _ => Err(ConvError::expected("a block", self)),
            },
            Value::Int(_) => Err(ConvError::expected("a block", self)),
        }
    }

    /// The fields of a block of tag `tag` and size `size`.
    pub fn fields(&self, tag: u8, size: usize) -> Result<&[Value], ConvError> {
        let (t, fields) = self.as_block()?;
        if t != tag || fields.len() != size {
            return Err(ConvError(format!(
                "expected a block of tag {} and size {}, got {}",
                tag,
                size,
                describe(self, 3)
            )));
        }
        Ok(fields)
    }

    pub fn as_bytes(&self) -> Result<&[u8], ConvError> {
        match self {
            Value::Ptr(obj) => match &**obj {
                Obj::String(s) => Ok(s),
                _ => Err(ConvError::expected("a string", self)),
            },
            Value::Int(_) => Err(ConvError::expected("a string", self)),
        }
    }

    pub fn as_int64(&self) -> Result<i64, ConvError> {
        match self {
            Value::Ptr(obj) => match &**obj {
                Obj::Int64(n) => Ok(*n),
                _ => Err(ConvError::expected("an Int64.t", self)),
            },
            Value::Int(_) => Err(ConvError::expected("an Int64.t", self)),
        }
    }

    pub fn as_double(&self) -> Result<f64, ConvError> {
        match self {
            Value::Ptr(obj) => match &**obj {
                Obj::Double(f) => Ok(*f),
                _ => Err(ConvError::expected("a float", self)),
            },
            Value::Int(_) => Err(ConvError::expected("a float", self)),
        }
    }

    /// The elements of an OCaml list.
    pub fn list_items(&self) -> Result<Vec<&Value>, ConvError> {
        let mut items = vec![];
        let mut l = self;
        loop {
            match l {
                Value::Int(0) => return Ok(items),
                _ => {
                    let cell = l.fields(0, 2)?;
                    items.push(&cell[0]);
                    l = &cell[1];
                }
            }
        }
    }

    /// A copy in which no object is shared (what a program that never
    /// reuses a value would have built).
    pub fn unshare(&self) -> Value {
        match self {
            Value::Int(n) => Value::Int(*n),
            Value::Ptr(obj) => Value::Ptr(Rc::new(match &**obj {
                Obj::Block { tag, fields } => Obj::Block {
                    tag: *tag,
                    fields: fields.iter().map(|f| f.unshare()).collect(),
                },
                other => other.clone(),
            })),
        }
    }

    /// Whether two values are the same object (or equal immediates): OCaml's
    /// `==`.
    pub fn phys_equal(&self, other: &Value) -> bool {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => a == b,
            (Value::Ptr(a), Value::Ptr(b)) => Rc::ptr_eq(a, b),
            _ => false,
        }
    }
}

/// Structural equality (OCaml's `=`, ignoring sharing).
impl PartialEq for Value {
    fn eq(&self, other: &Value) -> bool {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => a == b,
            (Value::Ptr(a), Value::Ptr(b)) => Rc::ptr_eq(a, b) || **a == **b,
            _ => false,
        }
    }
}

impl std::fmt::Debug for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Int(n) => write!(f, "{}", n),
            Value::Ptr(obj) => match &**obj {
                Obj::Block { tag, fields } => {
                    write!(f, "<{}>", tag)?;
                    f.debug_list().entries(fields.iter()).finish()
                }
                Obj::String(s) => write!(f, "{:?}", bstr::BStr::new(s)),
                Obj::Double(d) => write!(f, "{:?}", d),
                Obj::DoubleArray(a) => write!(f, "[|{:?}|]", a),
                Obj::Int64(n) => write!(f, "{}L", n),
            },
        }
    }
}

/// `caml_hash_variant`: the integer that stands for the polymorphic variant
/// `` `name ``.
pub fn hash_variant(name: &str) -> i64 {
    let mut accu: i64 = 0;
    for b in name.bytes() {
        accu = accu.wrapping_mul(223).wrapping_add(b as i64);
    }
    // accu = accu & Val_long(0x7FFFFFFFL); return (int32_t) accu
    let accu = accu & 0x7FFF_FFFF;
    if accu >= 1 << 30 { accu - (1 << 31) } else { accu }
}

// ~~ Writing (extern.c) ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

const INTEXT_MAGIC_NUMBER_SMALL: u32 = 0x8495A6BE;
const INTEXT_MAGIC_NUMBER_BIG: u32 = 0x8495A6BF;
const INTEXT_MAGIC_NUMBER_COMPRESSED: u32 = 0x8495A6BD;

const PREFIX_SMALL_BLOCK: u8 = 0x80;
const PREFIX_SMALL_INT: u8 = 0x40;
const PREFIX_SMALL_STRING: u8 = 0x20;
const CODE_INT8: u8 = 0x0;
const CODE_INT16: u8 = 0x1;
const CODE_INT32: u8 = 0x2;
const CODE_INT64: u8 = 0x3;
const CODE_SHARED8: u8 = 0x4;
const CODE_SHARED16: u8 = 0x5;
const CODE_SHARED32: u8 = 0x6;
const CODE_SHARED64: u8 = 0x14;
const CODE_BLOCK32: u8 = 0x8;
const CODE_BLOCK64: u8 = 0x13;
const CODE_STRING8: u8 = 0x9;
const CODE_STRING32: u8 = 0xA;
const CODE_STRING64: u8 = 0x15;
const CODE_DOUBLE_BIG: u8 = 0xB;
const CODE_DOUBLE_LITTLE: u8 = 0xC;
const CODE_DOUBLE_ARRAY8_BIG: u8 = 0xD;
const CODE_DOUBLE_ARRAY8_LITTLE: u8 = 0xE;
const CODE_DOUBLE_ARRAY32_BIG: u8 = 0xF;
const CODE_DOUBLE_ARRAY32_LITTLE: u8 = 0x7;
const CODE_DOUBLE_ARRAY64_BIG: u8 = 0x16;
const CODE_DOUBLE_ARRAY64_LITTLE: u8 = 0x17;
const CODE_CODEPOINTER: u8 = 0x10;
const CODE_INFIXPOINTER: u8 = 0x11;
const CODE_CUSTOM: u8 = 0x12;
const CODE_CUSTOM_LEN: u8 = 0x18;
const CODE_CUSTOM_FIXED: u8 = 0x19;

/// The colour bits of the headers that `extern_header` writes in OCaml 5
/// (`NOT_MARKABLE`).
const NOT_MARKABLE: u64 = 3 << 8;

/// `Marshal.extern_flags`
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExternFlag {
    NoSharing,
    Compat32,
}

/// `Marshal.header_size`
pub const HEADER_SIZE: usize = 20;

struct Writer {
    out: Vec<u8>,
    no_sharing: bool,
    compat_32: bool,
    obj_counter: u64,
    size_32: u64,
    size_64: u64,
    /// The objects written so far, by address, with their numbers.
    seen: HashMap<*const Obj, u64>,
}

impl Writer {
    fn write(&mut self, c: u8) {
        self.out.push(c)
    }

    fn writecode8(&mut self, code: u8, val: i64) {
        self.out.push(code);
        self.out.push(val as u8);
    }

    fn writecode16(&mut self, code: u8, val: i64) {
        self.out.push(code);
        self.out.extend_from_slice(&(val as u16).to_be_bytes());
    }

    fn writecode32(&mut self, code: u8, val: i64) {
        self.out.push(code);
        self.out.extend_from_slice(&(val as u32).to_be_bytes());
    }

    fn writecode64(&mut self, code: u8, val: i64) {
        self.out.push(code);
        self.out.extend_from_slice(&(val as u64).to_be_bytes());
    }

    fn extern_int(&mut self, n: i64) -> Result<(), MarshalError> {
        if (0..0x40).contains(&n) {
            self.write(PREFIX_SMALL_INT + n as u8);
        } else if (-(1 << 7)..(1 << 7)).contains(&n) {
            self.writecode8(CODE_INT8, n);
        } else if (-(1 << 15)..(1 << 15)).contains(&n) {
            self.writecode16(CODE_INT16, n);
        } else if !(-(1 << 30)..(1 << 30)).contains(&n) {
            if self.compat_32 {
                return Err(MarshalError(
                    "output_value: integer cannot be read back on 32-bit platform".to_string(),
                ));
            }
            self.writecode64(CODE_INT64, n);
        } else {
            self.writecode32(CODE_INT32, n);
        }
        Ok(())
    }

    fn extern_shared_reference(&mut self, d: u64) {
        if d < 0x100 {
            self.writecode8(CODE_SHARED8, d as i64);
        } else if d < 0x10000 {
            self.writecode16(CODE_SHARED16, d as i64);
        } else if d >= 1 << 32 {
            self.writecode64(CODE_SHARED64, d as i64);
        } else {
            self.writecode32(CODE_SHARED32, d as i64);
        }
    }

    fn extern_header(&mut self, sz: usize, tag: u8) -> Result<(), MarshalError> {
        if tag < 16 && sz < 8 {
            self.write(PREFIX_SMALL_BLOCK + tag + ((sz as u8) << 4));
        } else {
            let hd: u64 = ((sz as u64) << 10) | NOT_MARKABLE | tag as u64;
            if sz > 0x3FFFFF && self.compat_32 {
                return Err(MarshalError(
                    "output_value: array cannot be read back on 32-bit platform".to_string(),
                ));
            }
            if hd < 1 << 32 {
                self.writecode32(CODE_BLOCK32, hd as i64);
            } else {
                self.writecode64(CODE_BLOCK64, hd as i64);
            }
        }
        Ok(())
    }

    fn extern_string(&mut self, bytes: &[u8]) -> Result<(), MarshalError> {
        let len = bytes.len();
        if len < 0x20 {
            self.write(PREFIX_SMALL_STRING + len as u8);
        } else if len < 0x100 {
            self.writecode8(CODE_STRING8, len as i64);
        } else {
            if len > 0xFFFFFB && self.compat_32 {
                return Err(MarshalError(
                    "output_value: string cannot be read back on 32-bit platform".to_string(),
                ));
            }
            if (len as u64) < 1 << 32 {
                self.writecode32(CODE_STRING32, len as i64);
            } else {
                self.writecode64(CODE_STRING64, len as i64);
            }
        }
        self.out.extend_from_slice(bytes);
        Ok(())
    }

    fn extern_double_array(&mut self, a: &[f64]) -> Result<(), MarshalError> {
        let nfloats = a.len();
        if nfloats < 0x100 {
            self.writecode8(CODE_DOUBLE_ARRAY8_LITTLE, nfloats as i64);
        } else {
            if nfloats > 0x1FFFFF && self.compat_32 {
                return Err(MarshalError(
                    "output_value: float array cannot be read back on 32-bit platform".to_string(),
                ));
            }
            if (nfloats as u64) < 1 << 32 {
                self.writecode32(CODE_DOUBLE_ARRAY32_LITTLE, nfloats as i64);
            } else {
                self.writecode64(CODE_DOUBLE_ARRAY64_LITTLE, nfloats as i64);
            }
        }
        for f in a {
            self.out.extend_from_slice(&f.to_le_bytes());
        }
        Ok(())
    }

    /// `extern_rec`: the value, then (with an explicit stack, so that long
    /// lists do not overflow) the fields still to write, first to last.
    fn extern_rec(&mut self, v: &Value) -> Result<(), MarshalError> {
        let mut stack: Vec<std::slice::Iter<'_, Value>> = vec![];
        let mut v = v;
        loop {
            match v {
                Value::Int(n) => self.extern_int(*n)?,
                Value::Ptr(obj) => {
                    let sz = match &**obj {
                        Obj::Block { fields, .. } => fields.len(),
                        _ => 1,
                    };
                    if sz == 0 {
                        // Atoms are not shared nor counted.
                        let tag = match &**obj {
                            Obj::Block { tag, .. } => *tag,
                            _ => unreachable!(),
                        };
                        self.extern_header(0, tag)?;
                    } else {
                        let key = Rc::as_ptr(obj);
                        let seen = if self.no_sharing {
                            None
                        } else {
                            self.seen.get(&key).copied()
                        };
                        match seen {
                            Some(pos) => self.extern_shared_reference(self.obj_counter - pos),
                            None => {
                                // record_location (which `No_sharing` skips,
                                // so that the header then counts no object)
                                if !self.no_sharing {
                                    self.seen.insert(key, self.obj_counter);
                                    self.obj_counter += 1;
                                }
                                match &**obj {
                                    Obj::String(s) => {
                                        let len = s.len() as u64;
                                        self.extern_string(s)?;
                                        self.size_32 += 1 + (len + 4) / 4;
                                        self.size_64 += 1 + (len + 8) / 8;
                                    }
                                    Obj::Double(f) => {
                                        self.write(CODE_DOUBLE_LITTLE);
                                        self.out.extend_from_slice(&f.to_le_bytes());
                                        self.size_32 += 1 + 2;
                                        self.size_64 += 1 + 1;
                                    }
                                    Obj::Int64(n) => {
                                        // `extern_custom`: the identifier
                                        // with its NUL, then
                                        // `caml_serialize_int_8` (big-endian);
                                        // 8 bytes of data on both sizes.
                                        self.write(CODE_CUSTOM_FIXED);
                                        self.out.extend_from_slice(b"_j\0");
                                        self.out.extend_from_slice(&n.to_be_bytes());
                                        self.size_32 += 2 + (8 + 3) / 4;
                                        self.size_64 += 2 + (8 + 7) / 8;
                                    }
                                    Obj::DoubleArray(a) => {
                                        if a.is_empty() {
                                            // An empty float array is an atom.
                                            self.extern_header(0, DOUBLE_ARRAY_TAG)?;
                                        } else {
                                            self.extern_double_array(a)?;
                                            let n = a.len() as u64;
                                            self.size_32 += 1 + n * 2;
                                            self.size_64 += 1 + n;
                                        }
                                    }
                                    Obj::Block { tag, fields } => {
                                        if *tag >= NO_SCAN_TAG {
                                            return Err(MarshalError(format!(
                                                "output_value: a block of tag {} is not supported",
                                                tag
                                            )));
                                        }
                                        self.extern_header(sz, *tag)?;
                                        self.size_32 += 1 + sz as u64;
                                        self.size_64 += 1 + sz as u64;
                                        let mut it = fields.iter();
                                        let first = it.next().unwrap();
                                        if it.len() > 0 {
                                            stack.push(it);
                                        }
                                        v = first;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            // next_item
            loop {
                match stack.last_mut() {
                    None => return Ok(()),
                    Some(it) => match it.next() {
                        Some(next) => {
                            if it.len() == 0 {
                                stack.pop();
                            }
                            v = next;
                            break;
                        }
                        None => {
                            stack.pop();
                        }
                    },
                }
            }
        }
    }
}

/// `Marshal.to_bytes v flags`: the header and the data.
pub fn to_bytes(v: &Value, flags: &[ExternFlag]) -> Result<Vec<u8>, MarshalError> {
    let mut w = Writer {
        out: vec![],
        no_sharing: flags.contains(&ExternFlag::NoSharing),
        compat_32: flags.contains(&ExternFlag::Compat32),
        obj_counter: 0,
        size_32: 0,
        size_64: 0,
        seen: HashMap::new(),
    };
    w.extern_rec(v)?;
    let res_len = w.out.len() as u64;
    let mut header = Vec::with_capacity(32);
    if res_len >= 1 << 32 || w.size_32 >= 1 << 32 || w.size_64 >= 1 << 32 {
        // The object is too big for the small header format.
        if w.compat_32 {
            return Err(MarshalError(
                "output_value: object too big to be read back on 32-bit platform".to_string(),
            ));
        }
        header.extend_from_slice(&INTEXT_MAGIC_NUMBER_BIG.to_be_bytes());
        header.extend_from_slice(&0u32.to_be_bytes());
        header.extend_from_slice(&res_len.to_be_bytes());
        header.extend_from_slice(&w.obj_counter.to_be_bytes());
        header.extend_from_slice(&w.size_64.to_be_bytes());
    } else {
        header.extend_from_slice(&INTEXT_MAGIC_NUMBER_SMALL.to_be_bytes());
        header.extend_from_slice(&(res_len as u32).to_be_bytes());
        header.extend_from_slice(&(w.obj_counter as u32).to_be_bytes());
        header.extend_from_slice(&(w.size_32 as u32).to_be_bytes());
        header.extend_from_slice(&(w.size_64 as u32).to_be_bytes());
    }
    header.extend_from_slice(&w.out);
    Ok(header)
}

// ~~ Reading (intern.c) ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// A failure of `Marshal.from_bytes` (OCaml raises `Failure` with this
/// message, or `Invalid_argument "Marshal.from_bytes"`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MarshalError(pub String);

impl std::fmt::Display for MarshalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for MarshalError {}

fn bad_object() -> MarshalError {
    MarshalError("input_value: bad object".to_string())
}

fn truncated() -> MarshalError {
    MarshalError("input_value: truncated object".to_string())
}

/// The header of a marshalled value: `(header_size, data_len,
/// num_objects)`.
fn parse_header(buf: &[u8]) -> Result<(usize, u64, u64), MarshalError> {
    let be32 = |i: usize| -> Result<u32, MarshalError> {
        buf.get(i..i + 4)
            .map(|b| u32::from_be_bytes([b[0], b[1], b[2], b[3]]))
            .ok_or_else(|| MarshalError("Marshal.from_bytes".to_string()))
    };
    let be64 = |i: usize| -> Result<u64, MarshalError> {
        buf.get(i..i + 8)
            .map(|b| u64::from_be_bytes(b.try_into().unwrap()))
            .ok_or_else(|| MarshalError("Marshal.from_bytes".to_string()))
    };
    match be32(0)? {
        INTEXT_MAGIC_NUMBER_SMALL => Ok((20, be32(4)? as u64, be32(8)? as u64)),
        INTEXT_MAGIC_NUMBER_BIG => Ok((32, be64(8)?, be64(16)?)),
        INTEXT_MAGIC_NUMBER_COMPRESSED => Err(MarshalError(
            "input_value: compressed object, cannot decompress".to_string(),
        )),
        _ => Err(bad_object()),
    }
}

/// `Marshal.data_size buff ofs` (the header at `ofs` must be complete).
pub fn data_size(buf: &[u8], ofs: usize) -> Result<usize, MarshalError> {
    let (_, len, _) = parse_header(buf.get(ofs..).unwrap_or(&[]))?;
    Ok(len as usize)
}

/// `Marshal.total_size buff ofs`
pub fn total_size(buf: &[u8], ofs: usize) -> Result<usize, MarshalError> {
    let (hlen, len, _) = parse_header(buf.get(ofs..).unwrap_or(&[]))?;
    Ok(hlen + len as usize)
}

struct Reader<'a> {
    buf: &'a [u8],
    pos: usize,
}

impl Reader<'_> {
    fn bytes(&mut self, n: usize) -> Result<&[u8], MarshalError> {
        let end = self.pos.checked_add(n).ok_or_else(truncated)?;
        let s = self.buf.get(self.pos..end).ok_or_else(truncated)?;
        self.pos = end;
        Ok(s)
    }

    fn u8(&mut self) -> Result<u8, MarshalError> {
        Ok(self.bytes(1)?[0])
    }

    fn i8(&mut self) -> Result<i64, MarshalError> {
        Ok(self.u8()? as i8 as i64)
    }

    fn u16(&mut self) -> Result<u64, MarshalError> {
        let b = self.bytes(2)?;
        Ok(u16::from_be_bytes([b[0], b[1]]) as u64)
    }

    fn i16(&mut self) -> Result<i64, MarshalError> {
        Ok(self.u16()? as u16 as i16 as i64)
    }

    fn u32(&mut self) -> Result<u64, MarshalError> {
        let b = self.bytes(4)?;
        Ok(u32::from_be_bytes([b[0], b[1], b[2], b[3]]) as u64)
    }

    fn i32(&mut self) -> Result<i64, MarshalError> {
        Ok(self.u32()? as u32 as i32 as i64)
    }

    fn u64(&mut self) -> Result<u64, MarshalError> {
        Ok(u64::from_be_bytes(self.bytes(8)?.try_into().unwrap()))
    }

    fn double(&mut self, little: bool) -> Result<f64, MarshalError> {
        let b: [u8; 8] = self.bytes(8)?.try_into().unwrap();
        Ok(if little {
            f64::from_le_bytes(b)
        } else {
            f64::from_be_bytes(b)
        })
    }
}

/// A block being read: its tag, its number in the object table, the fields
/// read so far and how many it has.
struct Frame {
    tag: u8,
    obj: Option<usize>,
    fields: Vec<Value>,
    size: usize,
}

/// `Marshal.from_bytes buff ofs`: the value marshalled at `ofs`.
pub fn from_bytes(buf: &[u8], ofs: usize) -> Result<Value, MarshalError> {
    let invalid = || MarshalError("Marshal.from_bytes".to_string());
    if ofs > buf.len() || buf.len() - ofs < HEADER_SIZE {
        return Err(invalid());
    }
    let (hlen, len, num_objects) = parse_header(&buf[ofs..])?;
    let start = ofs + hlen;
    let end = start.checked_add(len as usize).ok_or_else(invalid)?;
    if end > buf.len() {
        return Err(invalid());
    }
    let mut r = Reader {
        buf: &buf[start..end],
        pos: 0,
    };
    // The object table: `None` while the block is being read.
    let mut objs: Vec<Option<Value>> = Vec::with_capacity(num_objects.min(1 << 20) as usize);
    let mut stack: Vec<Frame> = vec![];
    loop {
        let code = r.u8()?;
        // A value read in full, or a block whose fields come next.
        let v: Option<Value> = if code >= PREFIX_SMALL_INT {
            if code >= PREFIX_SMALL_BLOCK {
                let tag = code & 0xF;
                let size = ((code >> 4) & 0x7) as usize;
                start_block(&mut objs, &mut stack, tag, size)
            } else {
                Some(Value::Int((code & 0x3F) as i64))
            }
        } else if code >= PREFIX_SMALL_STRING {
            let len = (code & 0x1F) as usize;
            Some(record(&mut objs, Obj::String(r.bytes(len)?.to_vec())))
        } else {
            match code {
                CODE_INT8 => Some(Value::Int(r.i8()?)),
                CODE_INT16 => Some(Value::Int(r.i16()?)),
                CODE_INT32 => Some(Value::Int(r.i32()?)),
                CODE_INT64 => Some(Value::Int(r.u64()? as i64)),
                CODE_SHARED8 | CODE_SHARED16 | CODE_SHARED32 | CODE_SHARED64 => {
                    let ofs = match code {
                        CODE_SHARED8 => r.u8()? as u64,
                        CODE_SHARED16 => r.u16()?,
                        CODE_SHARED32 => r.u32()?,
                        _ => r.u64()?,
                    } as usize;
                    let i = objs.len().checked_sub(ofs).ok_or_else(bad_object)?;
                    match objs.get(i) {
                        Some(Some(v)) => Some(v.clone()),
                        // A reference to a block still being read: a cyclic
                        // value, which these files never hold.
                        Some(None) => {
                            return Err(MarshalError(
                                "input_value: cyclic values are not supported".to_string(),
                            ));
                        }
                        None => return Err(bad_object()),
                    }
                }
                CODE_BLOCK32 | CODE_BLOCK64 => {
                    let header = if code == CODE_BLOCK32 {
                        r.u32()?
                    } else {
                        r.u64()?
                    };
                    let tag = (header & 0xFF) as u8;
                    let size = (header >> 10) as usize;
                    if tag >= NO_SCAN_TAG && size > 0 {
                        return Err(bad_object());
                    }
                    start_block(&mut objs, &mut stack, tag, size)
                }
                CODE_STRING8 | CODE_STRING32 | CODE_STRING64 => {
                    let len = match code {
                        CODE_STRING8 => r.u8()? as u64,
                        CODE_STRING32 => r.u32()?,
                        _ => r.u64()?,
                    } as usize;
                    Some(record(&mut objs, Obj::String(r.bytes(len)?.to_vec())))
                }
                CODE_DOUBLE_LITTLE | CODE_DOUBLE_BIG => {
                    let f = r.double(code == CODE_DOUBLE_LITTLE)?;
                    Some(record(&mut objs, Obj::Double(f)))
                }
                CODE_DOUBLE_ARRAY8_LITTLE
                | CODE_DOUBLE_ARRAY8_BIG
                | CODE_DOUBLE_ARRAY32_LITTLE
                | CODE_DOUBLE_ARRAY32_BIG
                | CODE_DOUBLE_ARRAY64_LITTLE
                | CODE_DOUBLE_ARRAY64_BIG => {
                    let n = match code {
                        CODE_DOUBLE_ARRAY8_LITTLE | CODE_DOUBLE_ARRAY8_BIG => r.u8()? as u64,
                        CODE_DOUBLE_ARRAY32_LITTLE | CODE_DOUBLE_ARRAY32_BIG => r.u32()?,
                        _ => r.u64()?,
                    } as usize;
                    let little = matches!(
                        code,
                        CODE_DOUBLE_ARRAY8_LITTLE
                            | CODE_DOUBLE_ARRAY32_LITTLE
                            | CODE_DOUBLE_ARRAY64_LITTLE
                    );
                    let mut a = Vec::with_capacity(n.min(1 << 20));
                    for _ in 0..n {
                        a.push(r.double(little)?);
                    }
                    Some(record(&mut objs, Obj::DoubleArray(a)))
                }
                CODE_CODEPOINTER | CODE_INFIXPOINTER => {
                    return Err(MarshalError(
                        "input_value: code pointers are not supported".to_string(),
                    ));
                }
                CODE_CUSTOM | CODE_CUSTOM_LEN | CODE_CUSTOM_FIXED => {
                    // The identifier, up to its NUL.
                    let start = r.pos;
                    loop {
                        if r.u8()? == 0 {
                            break;
                        }
                    }
                    let ident = &r.buf[start..r.pos - 1];
                    if code == CODE_CUSTOM_LEN {
                        // (`size_32`, `size_64`)
                        let _ = r.u32()?;
                        let _ = r.u64()?;
                    }
                    match ident {
                        b"_j" => {
                            let n = r.u64()? as i64;
                            Some(record(&mut objs, Obj::Int64(n)))
                        }
                        _ => {
                            return Err(MarshalError(format!(
                                "input_value: unknown custom block identifier {}",
                                String::from_utf8_lossy(ident)
                            )));
                        }
                    }
                }
                _ => return Err(bad_object()),
            }
        };
        // Give the value to the block it is a field of, completing blocks
        // as their last field arrives.
        let mut v = match v {
            Some(v) => v,
            None => continue,
        };
        loop {
            match stack.last_mut() {
                None => {
                    if r.pos != r.buf.len() {
                        return Err(bad_object());
                    }
                    return Ok(v);
                }
                Some(frame) => {
                    frame.fields.push(v);
                    if frame.fields.len() < frame.size {
                        break;
                    }
                    let frame = stack.pop().unwrap();
                    let block = Value::block(frame.tag, frame.fields);
                    if let Some(i) = frame.obj {
                        objs[i] = Some(block.clone());
                    }
                    v = block;
                }
            }
        }
    }
}

/// Puts a read object in the table.
fn record(objs: &mut Vec<Option<Value>>, obj: Obj) -> Value {
    let v = Value::Ptr(Rc::new(obj));
    objs.push(Some(v.clone()));
    v
}

/// A block header: an atom is complete (and not in the table); any other
/// block gets its number and waits for its fields.
fn start_block(
    objs: &mut Vec<Option<Value>>,
    stack: &mut Vec<Frame>,
    tag: u8,
    size: usize,
) -> Option<Value> {
    if size == 0 {
        Some(Value::block(tag, vec![]))
    } else {
        objs.push(None);
        stack.push(Frame {
            tag,
            obj: Some(objs.len() - 1),
            fields: Vec::with_capacity(size.min(1 << 16)),
            size,
        });
        None
    }
}

// ~~ Typed values ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// A value that is not the OCaml representation of the expected type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConvError(pub String);

impl ConvError {
    fn expected(what: &str, v: &Value) -> ConvError {
        ConvError(format!("expected {}, got {}", what, describe(v, 3)))
    }
}

/// A short description of a value: `depth` levels of blocks, a few fields
/// each.
fn describe(v: &Value, depth: usize) -> String {
    match v {
        Value::Int(n) => n.to_string(),
        Value::Ptr(obj) => match &**obj {
            Obj::Block { tag, fields } if depth == 0 => format!("<{}>[{} fields]", tag, fields.len()),
            Obj::Block { tag, fields } => {
                let mut parts: Vec<String> =
                    fields.iter().take(6).map(|f| describe(f, depth - 1)).collect();
                if fields.len() > 6 {
                    parts.push("...".to_string());
                }
                format!("<{}>[{}]", tag, parts.join(", "))
            }
            Obj::String(s) => {
                let mut d = format!("{:?}", bstr::BStr::new(&s[..s.len().min(60)]));
                if s.len() > 60 {
                    d.push_str("...");
                }
                d
            }
            Obj::Double(d) => format!("{:?}", d),
            Obj::DoubleArray(a) => format!("[|{} floats|]", a.len()),
            Obj::Int64(n) => format!("{}L", n),
        },
    }
}

impl std::fmt::Display for ConvError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for ConvError {}

/// The OCaml representation of a Rust value.
pub trait ToOcaml {
    fn to_ocaml(&self) -> Value;
}

/// A Rust value from its OCaml representation.
pub trait FromOcaml: Sized {
    fn from_ocaml(v: &Value) -> Result<Self, ConvError>;
}

impl ToOcaml for Value {
    fn to_ocaml(&self) -> Value {
        self.clone()
    }
}

impl FromOcaml for Value {
    fn from_ocaml(v: &Value) -> Result<Self, ConvError> {
        Ok(v.clone())
    }
}

impl ToOcaml for isize {
    fn to_ocaml(&self) -> Value {
        Value::Int(*self as i64)
    }
}

impl FromOcaml for isize {
    fn from_ocaml(v: &Value) -> Result<Self, ConvError> {
        Ok(v.as_int()? as isize)
    }
}

impl ToOcaml for i64 {
    fn to_ocaml(&self) -> Value {
        Value::Int(*self)
    }
}

impl FromOcaml for i64 {
    fn from_ocaml(v: &Value) -> Result<Self, ConvError> {
        v.as_int()
    }
}

impl ToOcaml for bool {
    fn to_ocaml(&self) -> Value {
        Value::bool(*self)
    }
}

impl FromOcaml for bool {
    fn from_ocaml(v: &Value) -> Result<Self, ConvError> {
        match v.as_int()? {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err(ConvError::expected("a bool", v)),
        }
    }
}

impl ToOcaml for () {
    fn to_ocaml(&self) -> Value {
        Value::unit()
    }
}

impl FromOcaml for () {
    fn from_ocaml(v: &Value) -> Result<Self, ConvError> {
        match v.as_int()? {
            0 => Ok(()),
            _ => Err(ConvError::expected("()", v)),
        }
    }
}

/// A float is boxed (`Double_tag`).
impl ToOcaml for f64 {
    fn to_ocaml(&self) -> Value {
        Value::double(*self)
    }
}

impl FromOcaml for f64 {
    fn from_ocaml(v: &Value) -> Result<Self, ConvError> {
        v.as_double()
    }
}

impl ToOcaml for str {
    fn to_ocaml(&self) -> Value {
        Value::string(self.as_bytes())
    }
}

impl ToOcaml for String {
    fn to_ocaml(&self) -> Value {
        Value::string(self.as_bytes())
    }
}

/// An OCaml string holds any bytes: bytes that are not UTF-8 become
/// U+FFFD.
impl FromOcaml for String {
    fn from_ocaml(v: &Value) -> Result<Self, ConvError> {
        Ok(String::from_utf8_lossy(v.as_bytes()?).into_owned())
    }
}

impl ToOcaml for bstr::BString {
    fn to_ocaml(&self) -> Value {
        Value::string(self.to_vec())
    }
}

impl FromOcaml for bstr::BString {
    fn from_ocaml(v: &Value) -> Result<Self, ConvError> {
        Ok(bstr::BString::from(v.as_bytes()?.to_vec()))
    }
}

impl<T: ToOcaml + ?Sized> ToOcaml for &T {
    fn to_ocaml(&self) -> Value {
        (**self).to_ocaml()
    }
}

impl<T: ToOcaml> ToOcaml for Box<T> {
    fn to_ocaml(&self) -> Value {
        (**self).to_ocaml()
    }
}

impl<T: FromOcaml> FromOcaml for Box<T> {
    fn from_ocaml(v: &Value) -> Result<Self, ConvError> {
        Ok(Box::new(T::from_ocaml(v)?))
    }
}

impl<T: ToOcaml> ToOcaml for Option<T> {
    fn to_ocaml(&self) -> Value {
        match self {
            None => Value::unit(),
            Some(x) => Value::some(x.to_ocaml()),
        }
    }
}

impl<T: FromOcaml> FromOcaml for Option<T> {
    fn from_ocaml(v: &Value) -> Result<Self, ConvError> {
        match v {
            Value::Int(0) => Ok(None),
            _ => Ok(Some(T::from_ocaml(&v.fields(0, 1)?[0])?)),
        }
    }
}

/// A `Vec` is an OCaml list (element 0 the head).
impl<T: ToOcaml> ToOcaml for Vec<T> {
    fn to_ocaml(&self) -> Value {
        Value::list(self.iter().map(|x| x.to_ocaml()).collect::<Vec<_>>())
    }
}

impl<T: FromOcaml> FromOcaml for Vec<T> {
    fn from_ocaml(v: &Value) -> Result<Self, ConvError> {
        v.list_items()?.into_iter().map(T::from_ocaml).collect()
    }
}

impl<A: ToOcaml, B: ToOcaml> ToOcaml for (A, B) {
    fn to_ocaml(&self) -> Value {
        Value::block(0, vec![self.0.to_ocaml(), self.1.to_ocaml()])
    }
}

impl<A: FromOcaml, B: FromOcaml> FromOcaml for (A, B) {
    fn from_ocaml(v: &Value) -> Result<Self, ConvError> {
        let f = v.fields(0, 2)?;
        Ok((A::from_ocaml(&f[0])?, B::from_ocaml(&f[1])?))
    }
}

impl<A: ToOcaml, B: ToOcaml, C: ToOcaml> ToOcaml for (A, B, C) {
    fn to_ocaml(&self) -> Value {
        Value::block(
            0,
            vec![self.0.to_ocaml(), self.1.to_ocaml(), self.2.to_ocaml()],
        )
    }
}

impl<A: FromOcaml, B: FromOcaml, C: FromOcaml> FromOcaml for (A, B, C) {
    fn from_ocaml(v: &Value) -> Result<Self, ConvError> {
        let f = v.fields(0, 3)?;
        Ok((
            A::from_ocaml(&f[0])?,
            B::from_ocaml(&f[1])?,
            C::from_ocaml(&f[2])?,
        ))
    }
}

/// The stdlib's `Map.Make(Ord)`: `type 'a t = Empty | Node of {l: 'a t; v:
/// key; d: 'a; r: 'a t; h: int}`. The functions are the stdlib's, so that
/// a map built here by the same calls as in OCaml has the same shape (and
/// so the same bytes).
pub mod ocaml_map {
    use std::cmp::Ordering;
    use std::rc::Rc;

    use super::ConvError;
    use super::Value;

    #[derive(Debug)]
    pub enum T<K, V> {
        Empty,
        Node(Rc<Node<K, V>>),
    }

    #[derive(Debug)]
    pub struct Node<K, V> {
        pub l: T<K, V>,
        pub v: K,
        pub d: V,
        pub r: T<K, V>,
        pub h: i64,
    }

    impl<K, V> Clone for T<K, V> {
        fn clone(&self) -> Self {
            match self {
                T::Empty => T::Empty,
                T::Node(n) => T::Node(n.clone()),
            }
        }
    }

    fn phys_equal<K, V>(a: &T<K, V>, b: &T<K, V>) -> bool {
        match (a, b) {
            (T::Empty, T::Empty) => true,
            (T::Node(a), T::Node(b)) => Rc::ptr_eq(a, b),
            _ => false,
        }
    }

    pub fn empty<K, V>() -> T<K, V> {
        T::Empty
    }

    pub fn height<K, V>(t: &T<K, V>) -> i64 {
        match t {
            T::Empty => 0,
            T::Node(n) => n.h,
        }
    }

    fn create<K, V>(l: T<K, V>, v: K, d: V, r: T<K, V>) -> T<K, V> {
        let hl = height(&l);
        let hr = height(&r);
        let h = if hl >= hr { hl + 1 } else { hr + 1 };
        T::Node(Rc::new(Node { l, v, d, r, h }))
    }

    pub fn singleton<K, V>(x: K, d: V) -> T<K, V> {
        T::Node(Rc::new(Node {
            l: T::Empty,
            v: x,
            d,
            r: T::Empty,
            h: 1,
        }))
    }

    fn node<K, V>(t: &T<K, V>) -> &Node<K, V> {
        match t {
            T::Node(n) => n,
            T::Empty => panic!("Map.bal"),
        }
    }

    fn bal<K: Clone, V: Clone>(l: T<K, V>, x: K, d: V, r: T<K, V>) -> T<K, V> {
        let hl = height(&l);
        let hr = height(&r);
        if hl > hr + 2 {
            let ln = node(&l);
            if height(&ln.l) >= height(&ln.r) {
                create(
                    ln.l.clone(),
                    ln.v.clone(),
                    ln.d.clone(),
                    create(ln.r.clone(), x, d, r),
                )
            } else {
                let lrn = node(&ln.r);
                create(
                    create(ln.l.clone(), ln.v.clone(), ln.d.clone(), lrn.l.clone()),
                    lrn.v.clone(),
                    lrn.d.clone(),
                    create(lrn.r.clone(), x, d, r),
                )
            }
        } else if hr > hl + 2 {
            let rn = node(&r);
            if height(&rn.r) >= height(&rn.l) {
                create(
                    create(l, x, d, rn.l.clone()),
                    rn.v.clone(),
                    rn.d.clone(),
                    rn.r.clone(),
                )
            } else {
                let rln = node(&rn.l);
                create(
                    create(l, x, d, rln.l.clone()),
                    rln.v.clone(),
                    rln.d.clone(),
                    create(rln.r.clone(), rn.v.clone(), rn.d.clone(), rn.r.clone()),
                )
            }
        } else {
            let h = if hl >= hr { hl + 1 } else { hr + 1 };
            T::Node(Rc::new(Node { l, v: x, d, r, h }))
        }
    }

    /// `add x data m` (`compare` is `Ord.compare`). As OCaml, a binding
    /// whose key is already there replaces it (OCaml keeps the node when the
    /// data is physically equal: `same_data` says so).
    pub fn add<K: Clone, V: Clone>(
        x: K,
        data: V,
        m: &T<K, V>,
        compare: &impl Fn(&K, &K) -> Ordering,
        same_data: &impl Fn(&V, &V) -> bool,
    ) -> T<K, V> {
        match m {
            T::Empty => singleton(x, data),
            T::Node(n) => match compare(&x, &n.v) {
                Ordering::Equal => {
                    if same_data(&n.d, &data) {
                        m.clone()
                    } else {
                        T::Node(Rc::new(Node {
                            l: n.l.clone(),
                            v: x,
                            d: data,
                            r: n.r.clone(),
                            h: n.h,
                        }))
                    }
                }
                Ordering::Less => {
                    let ll = add(x, data, &n.l, compare, same_data);
                    if phys_equal(&n.l, &ll) {
                        m.clone()
                    } else {
                        bal(ll, n.v.clone(), n.d.clone(), n.r.clone())
                    }
                }
                Ordering::Greater => {
                    let rr = add(x, data, &n.r, compare, same_data);
                    if phys_equal(&n.r, &rr) {
                        m.clone()
                    } else {
                        bal(n.l.clone(), n.v.clone(), n.d.clone(), rr)
                    }
                }
            },
        }
    }

    fn min_binding<K: Clone, V: Clone>(t: &T<K, V>) -> (K, V) {
        match t {
            T::Empty => panic!("Not_found"),
            T::Node(n) => match &n.l {
                T::Empty => (n.v.clone(), n.d.clone()),
                l => min_binding(l),
            },
        }
    }

    fn remove_min_binding<K: Clone, V: Clone>(t: &T<K, V>) -> T<K, V> {
        match t {
            T::Empty => panic!("Map.remove_min_elt"),
            T::Node(n) => match &n.l {
                T::Empty => n.r.clone(),
                l => bal(remove_min_binding(l), n.v.clone(), n.d.clone(), n.r.clone()),
            },
        }
    }

    fn add_min_binding<K: Clone, V: Clone>(k: K, x: V, t: &T<K, V>) -> T<K, V> {
        match t {
            T::Empty => singleton(k, x),
            T::Node(n) => bal(add_min_binding(k, x, &n.l), n.v.clone(), n.d.clone(), n.r.clone()),
        }
    }

    fn add_max_binding<K: Clone, V: Clone>(k: K, x: V, t: &T<K, V>) -> T<K, V> {
        match t {
            T::Empty => singleton(k, x),
            T::Node(n) => bal(n.l.clone(), n.v.clone(), n.d.clone(), add_max_binding(k, x, &n.r)),
        }
    }

    fn join<K: Clone, V: Clone>(l: &T<K, V>, v: K, d: V, r: &T<K, V>) -> T<K, V> {
        match (l, r) {
            (T::Empty, _) => add_min_binding(v, d, r),
            (_, T::Empty) => add_max_binding(v, d, l),
            (T::Node(ln), T::Node(rn)) => {
                if ln.h > rn.h + 2 {
                    bal(ln.l.clone(), ln.v.clone(), ln.d.clone(), join(&ln.r, v, d, r))
                } else if rn.h > ln.h + 2 {
                    bal(join(l, v, d, &rn.l), rn.v.clone(), rn.d.clone(), rn.r.clone())
                } else {
                    create(l.clone(), v, d, r.clone())
                }
            }
        }
    }

    fn concat<K: Clone, V: Clone>(t1: &T<K, V>, t2: &T<K, V>) -> T<K, V> {
        match (t1, t2) {
            (T::Empty, t) => t.clone(),
            (t, T::Empty) => t.clone(),
            _ => {
                let (x, d) = min_binding(t2);
                join(t1, x, d, &remove_min_binding(t2))
            }
        }
    }

    /// `filter p m` (`p` called in key order, as OCaml does).
    pub fn filter<K: Clone, V: Clone>(p: &mut impl FnMut(&K, &V) -> bool, m: &T<K, V>) -> T<K, V> {
        match m {
            T::Empty => T::Empty,
            T::Node(n) => {
                let l2 = filter(p, &n.l);
                let pvd = p(&n.v, &n.d);
                let r2 = filter(p, &n.r);
                if pvd {
                    if phys_equal(&n.l, &l2) && phys_equal(&n.r, &r2) {
                        m.clone()
                    } else {
                        join(&l2, n.v.clone(), n.d.clone(), &r2)
                    }
                } else {
                    concat(&l2, &r2)
                }
            }
        }
    }

    /// `map f m`: the same shape.
    pub fn map<K: Clone, V, W>(f: &mut impl FnMut(&V) -> W, m: &T<K, V>) -> T<K, W> {
        match m {
            T::Empty => T::Empty,
            T::Node(n) => {
                let l = map(f, &n.l);
                let d = f(&n.d);
                let r = map(f, &n.r);
                T::Node(Rc::new(Node {
                    l,
                    v: n.v.clone(),
                    d,
                    r,
                    h: n.h,
                }))
            }
        }
    }

    /// The map that adding the bindings one by one, in this order, to the
    /// empty map makes (as `fold ... ~init:empty ~f:add` over a map does).
    pub fn of_iter<K: Clone, V: Clone>(
        bindings: impl IntoIterator<Item = (K, V)>,
        compare: &impl Fn(&K, &K) -> Ordering,
    ) -> T<K, V> {
        let mut m = T::Empty;
        for (k, v) in bindings {
            m = add(k, v, &m, compare, &|_, _| false);
        }
        m
    }

    /// The bindings in key order.
    pub fn bindings<K: Clone, V: Clone>(m: &T<K, V>) -> Vec<(K, V)> {
        fn go<K: Clone, V: Clone>(m: &T<K, V>, acc: &mut Vec<(K, V)>) {
            if let T::Node(n) = m {
                go(&n.l, acc);
                acc.push((n.v.clone(), n.d.clone()));
                go(&n.r, acc);
            }
        }
        let mut acc = vec![];
        go(m, &mut acc);
        acc
    }

    /// The OCaml value of the map.
    pub fn to_ocaml<K, V>(
        m: &T<K, V>,
        key: &mut impl FnMut(&K) -> Value,
        data: &mut impl FnMut(&V) -> Value,
    ) -> Value {
        match m {
            T::Empty => Value::Int(0),
            T::Node(n) => {
                let l = to_ocaml(&n.l, key, data);
                let v = key(&n.v);
                let d = data(&n.d);
                let r = to_ocaml(&n.r, key, data);
                Value::block(0, vec![l, v, d, r, Value::Int(n.h)])
            }
        }
    }

    /// The bindings of the OCaml value of a map, in key order (as `fold`
    /// visits them).
    pub fn bindings_of_ocaml(v: &Value) -> Result<Vec<(&Value, &Value)>, ConvError> {
        fn go<'a>(v: &'a Value, acc: &mut Vec<(&'a Value, &'a Value)>) -> Result<(), ConvError> {
            match v {
                Value::Int(0) => Ok(()),
                _ => {
                    let f = v.fields(0, 5)?;
                    go(&f[0], acc)?;
                    acc.push((&f[1], &f[2]));
                    go(&f[3], acc)
                }
            }
        }
        let mut acc = vec![];
        go(v, &mut acc)?;
        Ok(acc)
    }
}

/// The stdlib's `Set.Make(Ord)`: `type t = Empty | Node of {l: t; v: elt;
/// r: t; h: int}`, built as the stdlib's `add` does.
pub mod ocaml_set {
    use std::cmp::Ordering;

    use super::ConvError;
    use super::Value;
    use super::ocaml_map;

    /// A set is a map to `()` here; only its OCaml value differs (no `d`).
    pub type T<K> = ocaml_map::T<K, ()>;

    /// `add x s`
    pub fn add<K: Clone>(x: K, s: &T<K>, compare: &impl Fn(&K, &K) -> Ordering) -> T<K> {
        // Set.add and Map.add rebalance identically; Set.add keeps the set
        // when the element is there, as Map.add does for the same data.
        ocaml_map::add(x, (), s, compare, &|_, _| true)
    }

    /// The set that adding the elements one by one, in this order, makes.
    pub fn of_iter<K: Clone>(
        elts: impl IntoIterator<Item = K>,
        compare: &impl Fn(&K, &K) -> Ordering,
    ) -> T<K> {
        let mut s = ocaml_map::empty();
        for x in elts {
            s = add(x, &s, compare);
        }
        s
    }

    pub fn to_ocaml<K>(s: &T<K>, elt: &mut impl FnMut(&K) -> Value) -> Value {
        match s {
            ocaml_map::T::Empty => Value::Int(0),
            ocaml_map::T::Node(n) => {
                let l = to_ocaml(&n.l, elt);
                let v = elt(&n.v);
                let r = to_ocaml(&n.r, elt);
                Value::block(0, vec![l, v, r, Value::Int(n.h)])
            }
        }
    }

    /// The elements of the OCaml value of a set, in order.
    pub fn elements_of_ocaml(v: &Value) -> Result<Vec<&Value>, ConvError> {
        fn go<'a>(v: &'a Value, acc: &mut Vec<&'a Value>) -> Result<(), ConvError> {
            match v {
                Value::Int(0) => Ok(()),
                _ => {
                    let f = v.fields(0, 4)?;
                    go(&f[0], acc)?;
                    acc.push(&f[1]);
                    go(&f[2], acc)
                }
            }
        }
        let mut acc = vec![];
        go(v, &mut acc)?;
        Ok(acc)
    }
}

#[cfg(test)]
pub(crate) mod tests;
