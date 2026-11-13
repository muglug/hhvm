// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_deps.ml`. See `hh/PORTING.md`.
//!
//! How the OCaml state maps onto this crate:
//!
//! - OCaml checks files in worker *processes*; here one file is checked on
//!   one *thread*. State that every OCaml worker has a private copy of
//!   (`worker_id`, the batch of discovered edges, the batch of filtered edges,
//!   the output channels of `SaveToDiskMode`) is thread-local here. A thread
//!   hands its edges over with `flush_ideps_batch`, exactly as an OCaml worker
//!   does at the end of its job, and the results are combined with
//!   `merge_dep_edges` and stored with `register_discovered_dep_edges`.
//! - State of the OCaml master process (`trace`, the dependency callbacks,
//!   the loaded dependency graph and its in-memory delta) is global here.
//! - The `external`s of the OCaml (`hh_custom_dep_graph_*`, `hh_dep_set_*`,
//!   ...) were implemented in Rust by `deps_rust/typing_deps.rs`,
//!   `deps_rust/dep_graph_with_delta.rs` and `deps_rust/deps_rust_ffi.rs`;
//!   their logic is here, over the crates `dep_graph_delta` (the delta) and
//!   `depgraph_reader` (the saved-state graph).
//! - `Dep.dependent Dep.variant` and `Dep.dependency Dep.variant` are both
//!   `dep::Variant`: the phantom parameter of the OCaml GADT only restricts
//!   which constructors may be used as a dependent.
//! - `raise (Depgraph_unavailable e)` is
//!   `std::panic::panic_any(DepgraphUnavailable(e))`: the exception crosses
//!   all of typing (it can be raised by `add_idep`) and is only caught at the
//!   top of a job, by downcasting the payload of the panic.

#![allow(non_upper_case_globals)]

use std::cell::Cell;
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::VecDeque;
use std::io::ErrorKind;
use std::io::Write;
use std::sync::Arc;
use std::sync::LazyLock;
use std::sync::RwLock;
use std::sync::RwLockReadGuard;
use std::sync::RwLockWriteGuard;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;

use dep_graph_delta::DepGraphDelta;
use dep_graph_delta::HashSetDelta;
use depgraph_reader::BaseDepgraphTrait;
use depgraph_reader::DepGraph;
use hash::HashSet;
use oxidized::file_info::FileInfo;
pub use oxidized::typing_deps_types::DepgraphLoadError;
use typing_deps_hash::DepType;

/// `module Mode = Typing_deps_mode`.
pub use crate::typing_deps_mode as mode;

use mode::T::InMemoryMode;
use mode::T::SaveToDiskMode;

thread_local! {
    /// `worker_id : int option ref`. In OCaml every worker process sets its
    /// own; here every thread that checks files does
    /// (`typing_deps::worker_id.set(Some(n))`).
    pub static worker_id: Cell<Option<isize>> = const { Cell::new(None) };
}

/// `Worker_utils.is_worker_process ()`. `hh` has no worker processes (files
/// are checked on threads of the one process), so the assertions of the
/// OCaml that a function runs in the master process always hold.
fn is_worker_process() -> bool {
    false
}

/// `Utils.strip_ns`
fn strip_ns(s: &str) -> &str {
    s.strip_prefix('\\').unwrap_or(s)
}

/// `Printf`'s `%S`: the string, quoted and escaped as an OCaml literal.
fn ocaml_string_literal(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for &b in s.as_bytes() {
        match b {
            b'"' => out.push_str("\\\""),
            b'\\' => out.push_str("\\\\"),
            b'\n' => out.push_str("\\n"),
            b'\t' => out.push_str("\\t"),
            b'\r' => out.push_str("\\r"),
            0x08 => out.push_str("\\b"),
            b' '..=b'~' => out.push(b as char),
            _ => out.push_str(&format!("\\{:03}", b)),
        }
    }
    out.push('"');
    out
}

/// `int_of_string`, giving the 63-bit OCaml integer as a sign-extended `i64`.
fn int_of_string(s: &str) -> i64 {
    fn fail() -> ! {
        panic!("int_of_string")
    }
    fn digit(c: u8) -> Option<u64> {
        match c {
            b'0'..=b'9' => Some((c - b'0') as u64),
            b'A'..=b'F' => Some((c - b'A' + 10) as u64),
            b'a'..=b'f' => Some((c - b'a' + 10) as u64),
            _ => None,
        }
    }
    let b = s.as_bytes();
    let mut i = 0;
    let mut negative = false;
    match b.first() {
        Some(b'-') => {
            negative = true;
            i = 1;
        }
        Some(b'+') => i = 1,
        _ => {}
    }
    let (base, signed): (u64, bool) = match (b.get(i), b.get(i + 1)) {
        (Some(b'0'), Some(b'x' | b'X')) => (16, false),
        (Some(b'0'), Some(b'o' | b'O')) => (8, false),
        (Some(b'0'), Some(b'b' | b'B')) => (2, false),
        (Some(b'0'), Some(b'u' | b'U')) => (10, false),
        _ => (10, true),
    };
    if !(base == 10 && signed) {
        i += 2;
    }
    let threshold = u64::MAX / base;
    let mut res = match b.get(i).and_then(|&c| digit(c)) {
        Some(d) if d < base => d,
        _ => fail(),
    };
    i += 1;
    while i < b.len() {
        let c = b[i];
        if c == b'_' {
            i += 1;
            continue;
        }
        let d = match digit(c) {
            Some(d) if d < base => d,
            _ => break,
        };
        if res > threshold {
            fail();
        }
        res = res.wrapping_mul(base).wrapping_add(d);
        // Detect overflow in the addition.
        if res < d {
            fail();
        }
        i += 1;
    }
    if i != b.len() {
        fail();
    }
    // An OCaml `int` has 63 bits.
    if signed {
        if negative {
            if res > 1 << 62 {
                fail();
            }
        } else if res >= 1 << 62 {
            fail();
        }
    } else if res >= 1 << 63 {
        fail();
    }
    let res = if negative {
        (res as i64).wrapping_neg()
    } else {
        res as i64
    };
    // `Val_long`: keep 63 bits, sign-extended.
    (res << 1) >> 1
}

/******************************************/
/* Handling dependencies and their hashes */
/******************************************/
pub mod dep {
    use std::cmp::Ordering;

    use oxidized::decl_reference::DeclReference;
    use relative_path::RelativePath;
    use typing_deps_hash::DepType;

    use super::strip_ns;

    /// A type of dependency.
    ///
    /// The OCaml type is a GADT `_ variant` whose parameter is `dependent` (a
    /// node that must be rechecked when its dependencies change) or
    /// `dependency` (a node that, when changed, must recheck all of its
    /// dependents). Only `GConst`, `Fun`, `Type`, `GConstName`, `Module` and
    /// `Declares` can be dependents.
    ///
    /// NOTE: keep in sync with `typing_deps_hash.rs`.
    #[derive(Clone, Debug, PartialEq, Eq, Hash)]
    pub enum Variant {
        /// Represents a global constant depending on something, or something
        /// depending on a global constant.
        GConst(String),
        /// Represents either a global function depending on something, or
        /// something depending on a global function.
        Fun(String),
        /// Represents either a class/typedef/recorddef/trait/interface
        /// depending on something, or something depending on one.
        Type(String),
        /// Represents another class depending on a class via an
        /// inheritance-like mechanism (`extends`, `implements`, `use`,
        /// `require extends`, `require implements`, etc.)
        Extends(String),
        /// Whenever we use the fact that 'A is not a subtype of X' to conclude
        /// that a def F typechecks, we add an edge from `NotSubtype A` to the
        /// variant for F.
        NotSubtype(String),
        /// Represents something depending on a class constant.
        Const(String, String),
        /// Represents something depending on a class constructor.
        Constructor(String),
        /// Represents something depending on a class's instance property.
        Prop(String, String),
        /// Represents something depending on a class's static property.
        SProp(String, String),
        /// Represents something depending on a class's instance method.
        Method(String, String),
        /// Represents something depending on a class's static method.
        SMethod(String, String),
        /// Represents something depending on all members of a class.
        AllMembers(String),
        /// Like `GConst`, but used only in conservative redecl.
        GConstName(String),
        /// Represents a toplevel symbol being defined as a member of this
        /// module.
        Module(String),
        /// An edge `Method(c, m) -> Declares` means that class c declares m.
        Declares,
        /// Represents a dependency on the contents of a file.
        File(RelativePath),
    }

    pub fn dependency_of_variant(v: &Variant) -> Variant {
        use Variant::*;
        match v {
            GConst(s) => GConst(s.clone()),
            GConstName(s) => GConstName(s.clone()),
            Type(s) => Type(s.clone()),
            Fun(s) => Fun(s.clone()),
            Module(m) => Module(m.clone()),
            Const(cls, s) => Const(cls.clone(), s.clone()),
            Prop(cls, s) => Prop(cls.clone(), s.clone()),
            SProp(cls, s) => SProp(cls.clone(), s.clone()),
            Method(cls, s) => Method(cls.clone(), s.clone()),
            SMethod(cls, s) => SMethod(cls.clone(), s.clone()),
            Constructor(s) => Constructor(s.clone()),
            AllMembers(s) => AllMembers(s.clone()),
            Extends(s) => Extends(s.clone()),
            NotSubtype(s) => NotSubtype(s.clone()),
            Declares => Declares,
            File(path) => File(path.clone()),
        }
    }

    /// NOTE: keep in sync with `typing_deps_hash.rs`.
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
    #[repr(u8)]
    pub enum DepKind {
        KGConst = 0,
        KFun = 1,
        KType = 2,
        KExtends = 3,
        KConst = 5,
        KConstructor = 6,
        KProp = 7,
        KSProp = 8,
        KMethod = 9,
        KSMethod = 10,
        KAllMembers = 11,
        KGConstName = 12,
        KModule = 13,
        KDeclares = 14,
        KNotSubtype = 15,
        KFile = 16,
    }

    pub const min_dep_kind: isize = 0;

    pub const max_dep_kind: isize = 16;

    pub fn dep_kind_to_enum(k: DepKind) -> isize {
        k as u8 as isize
    }

    pub fn dep_kind_of_enum(i: isize) -> Option<DepKind> {
        use DepKind::*;
        match i {
            0 => Some(KGConst),
            1 => Some(KFun),
            2 => Some(KType),
            3 => Some(KExtends),
            5 => Some(KConst),
            6 => Some(KConstructor),
            7 => Some(KProp),
            8 => Some(KSProp),
            9 => Some(KMethod),
            10 => Some(KSMethod),
            11 => Some(KAllMembers),
            12 => Some(KGConstName),
            13 => Some(KModule),
            14 => Some(KDeclares),
            15 => Some(KNotSubtype),
            16 => Some(KFile),
            _ => None,
        }
    }

    /// The `DepType` of the crate `typing_deps_hash` with the same tag.
    pub(super) fn dep_type_of_dep_kind(k: DepKind) -> DepType {
        match DepType::from_u8(k as u8) {
            Some(dep_type) => dep_type,
            None => panic!("Invalid dep type: {:?}", k as u8),
        }
    }

    pub mod member {
        use super::DepKind;
        use crate::typing_deps::ocaml_string_literal;

        #[derive(Clone, Debug, PartialEq, Eq, Hash)]
        pub enum T {
            Method(String),
            SMethod(String),
            Prop(String),
            SProp(String),
            Constructor,
            Const(String),
            All,
        }

        pub fn pp(fmt: &mut dyn std::fmt::Write, x: &T) -> std::fmt::Result {
            let with_arg = |fmt: &mut dyn std::fmt::Write, constr: &str, name: &str| {
                write!(
                    fmt,
                    "(Typing_deps.Dep.Member.{} {})",
                    constr,
                    ocaml_string_literal(name)
                )
            };
            match x {
                T::Method(a0) => with_arg(fmt, "Method", a0),
                T::SMethod(a0) => with_arg(fmt, "SMethod", a0),
                T::Prop(a0) => with_arg(fmt, "Prop", a0),
                T::SProp(a0) => with_arg(fmt, "SProp", a0),
                T::Constructor => fmt.write_str("Typing_deps.Dep.Member.Constructor"),
                T::Const(a0) => with_arg(fmt, "Const", a0),
                T::All => fmt.write_str("Typing_deps.Dep.Member.All"),
            }
        }

        pub fn show(x: &T) -> String {
            let mut s = String::new();
            pp(&mut s, x).unwrap();
            s
        }

        pub fn method_(name: &str) -> T {
            T::Method(name.to_string())
        }

        pub fn smethod(name: &str) -> T {
            T::SMethod(name.to_string())
        }

        pub fn prop(name: &str) -> T {
            T::Prop(name.to_string())
        }

        pub fn sprop(name: &str) -> T {
            T::SProp(name.to_string())
        }

        pub const constructor: T = T::Constructor;

        pub fn const_(name: &str) -> T {
            T::Const(name.to_string())
        }

        pub const all: T = T::All;

        pub(in crate::typing_deps) fn to_dep_kind_and_name(member: &T) -> (DepKind, &str) {
            let default_name = "";
            match member {
                T::Const(name) => (DepKind::KConst, name),
                T::Constructor => (DepKind::KConstructor, default_name),
                T::Prop(name) => (DepKind::KProp, name),
                T::SProp(name) => (DepKind::KSProp, name),
                T::Method(name) => (DepKind::KMethod, name),
                T::SMethod(name) => (DepKind::KSMethod, name),
                T::All => (DepKind::KAllMembers, default_name),
            }
        }
    }

    /// `external hash1 : int -> string -> int = "hash1_ocaml"`
    fn hash1(dep_kind: DepKind, name1: &str) -> T {
        T(typing_deps_hash::hash1(
            dep_type_of_dep_kind(dep_kind),
            name1.as_bytes(),
        ))
    }

    /// `external hash2 : int -> int -> string -> int = "hash2_ocaml"`
    fn hash2(dep_kind: DepKind, type_hash: T, name2: &str) -> T {
        T(typing_deps_hash::hash2(
            dep_type_of_dep_kind(dep_kind),
            type_hash.0,
            name2.as_bytes(),
        ))
    }

    /// A 63bit hash.
    ///
    /// In OCaml this is an `int`: the 63 bits of the hash, of which the
    /// topmost is the sign. It is kept here as the unsigned 63-bit number
    /// (what `to_int64` gives, and what the crates `dep`, `depgraph_reader`
    /// and the saved-state files hold); `Ord` is OCaml's `Int.compare`, so
    /// that ordered sets and maps of hashes iterate in the OCaml order.
    #[derive(Clone, Copy, PartialEq, Eq, Hash)]
    pub struct T(u64);

    impl T {
        /// The OCaml `int`, sign-extended.
        fn ocaml_int(self) -> i64 {
            ((self.0 << 1) as i64) >> 1
        }
    }

    impl Ord for T {
        fn cmp(&self, other: &Self) -> Ordering {
            self.ocaml_int().cmp(&other.ocaml_int())
        }
    }

    impl PartialOrd for T {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            Some(self.cmp(other))
        }
    }

    impl std::fmt::Debug for T {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.write_str(&to_hex_string(*self))
        }
    }

    impl From<depgraph_dep::Dep> for T {
        fn from(dep: depgraph_dep::Dep) -> Self {
            T(u64::from(dep) & !(1 << 63))
        }
    }

    impl From<T> for depgraph_dep::Dep {
        fn from(dep: T) -> Self {
            depgraph_dep::Dep::new(dep.0)
        }
    }

    /// A 64bit representation of the 63bit hash.
    pub fn to_int64(t: T) -> i64 {
        // The top bit is reset to 0: whereas the OCaml int might render this
        // bit-pattern as a negative number, the Int64 is always positive.
        t.0 as i64
    }

    pub fn to_int(hash: T) -> isize {
        hash.ocaml_int() as isize
    }

    fn ordinal_variant(v: &Variant) -> isize {
        use Variant::*;
        match v {
            GConst(_) => 0,
            Fun(_) => 1,
            Type(_) => 2,
            Extends(_) => 3,
            NotSubtype(_) => 15,
            Const(..) => 5,
            Constructor(_) => 6,
            Prop(..) => 7,
            SProp(..) => 8,
            Method(..) => 9,
            SMethod(..) => 10,
            AllMembers(_) => 11,
            GConstName(_) => 12,
            Module(_) => 13,
            Declares => 14,
            File(_) => 16,
        }
    }

    pub fn compare_variant(v1: &Variant, v2: &Variant) -> Ordering {
        use Variant::*;
        match (v1, v2) {
            (GConst(x1), GConst(x2))
            | (Fun(x1), Fun(x2))
            | (Type(x1), Type(x2))
            | (Extends(x1), Extends(x2))
            | (NotSubtype(x1), NotSubtype(x2))
            | (Constructor(x1), Constructor(x2))
            | (AllMembers(x1), AllMembers(x2))
            | (GConstName(x1), GConstName(x2)) => x1.as_bytes().cmp(x2.as_bytes()),
            (Prop(c1, m1), Prop(c2, m2))
            | (SProp(c1, m1), SProp(c2, m2))
            | (Method(c1, m1), Method(c2, m2))
            | (SMethod(c1, m1), SMethod(c2, m2))
            | (Const(c1, m1), Const(c2, m2)) => {
                let res = c1.as_bytes().cmp(c2.as_bytes());
                if res != Ordering::Equal {
                    res
                } else {
                    m1.as_bytes().cmp(m2.as_bytes())
                }
            }
            (File(p1), File(p2)) => p1.cmp(p2),
            (Declares, Declares) => Ordering::Equal,
            // As in the OCaml, two `Module`s land here, and compare equal
            // whatever their names.
            (_, _) => ordinal_variant(v1).cmp(&ordinal_variant(v2)),
        }
    }

    pub fn dep_kind_of_variant(v: &Variant) -> DepKind {
        use DepKind::*;
        use Variant::*;
        match v {
            GConst(_) => KGConst,
            GConstName(_) => KGConstName,
            Const(..) => KConst,
            Type(_) => KType,
            Fun(_) => KFun,
            Prop(..) => KProp,
            SProp(..) => KSProp,
            Method(..) => KMethod,
            SMethod(..) => KSMethod,
            Constructor(_) => KConstructor,
            AllMembers(_) => KAllMembers,
            Extends(_) => KExtends,
            NotSubtype(_) => KNotSubtype,
            Module(_) => KModule,
            Declares => KDeclares,
            File(_) => KFile,
        }
    }

    pub fn make_member_dep_from_type_dep(type_dep: T, member: &member::T) -> T {
        let (dep_kind, member_name) = member::to_dep_kind_and_name(member);
        hash2(dep_kind, type_dep, member_name)
    }

    /// Return the 'NotSubtype' dep for a class from its 'Type' dep
    fn not_subtype_of_class(class_dep: T) -> T {
        hash2(DepKind::KNotSubtype, class_dep, "")
    }

    /// `Relative_path.storage_to_string`
    fn storage_to_string(path: &RelativePath) -> String {
        use relative_path::Prefix;
        let string_of_prefix = match path.prefix() {
            Prefix::Root => "root",
            Prefix::Hhi => "hhi",
            Prefix::Tmp => "tmp",
            Prefix::Dummy => "",
        };
        format!("{}|{}", string_of_prefix, path.path().display())
    }

    /* Keep in sync with the tags for `DepType` in `typing_deps_hash.rs`. */
    pub fn make(v: &Variant) -> T {
        use DepKind::*;
        use Variant::*;
        match v {
            /* Deps on defs */
            GConst(name1) => hash1(KGConst, name1),
            Fun(name1) => hash1(KFun, name1),
            GConstName(name1) => hash1(KGConstName, name1),
            Module(mname) => hash1(KModule, mname),
            Type(name1) => hash1(KType, name1),
            Extends(name1) => hash1(KExtends, name1),
            NotSubtype(name1) => not_subtype_of_class(hash1(KType, name1)),
            /* Deps on members */
            Constructor(name1) => {
                make_member_dep_from_type_dep(hash1(KType, name1), &member::T::Constructor)
            }
            Const(name1, name2) => hash2(KConst, hash1(KType, name1), name2),
            Prop(name1, name2) => hash2(KProp, hash1(KType, name1), name2),
            SProp(name1, name2) => hash2(KSProp, hash1(KType, name1), name2),
            Method(name1, name2) => hash2(KMethod, hash1(KType, name1), name2),
            SMethod(name1, name2) => hash2(KSMethod, hash1(KType, name1), name2),
            AllMembers(name1) => {
                make_member_dep_from_type_dep(hash1(KType, name1), &member::T::All)
            }
            Declares => hash1(KDeclares, ""),
            File(path) => hash1(KFile, &storage_to_string(path)),
        }
    }

    pub fn is_class(x: T) -> bool {
        x.0 & 1 == 1
    }

    pub fn compare(a: T, b: T) -> Ordering {
        a.cmp(&b)
    }

    pub fn extract_name(v: &Variant) -> String {
        use Variant::*;
        match v {
            Const(cls, s) | Prop(cls, s) | SProp(cls, s) | Method(cls, s) | SMethod(cls, s) => {
                format!("{}::{}", strip_ns(cls), s)
            }
            GConst(s) | GConstName(s) | Type(s) | Fun(s) | Constructor(s) | AllMembers(s)
            | Extends(s) | NotSubtype(s) => strip_ns(s).to_string(),
            Module(m) => m.clone(),
            Declares => "__declares__".to_string(),
            File(path) => storage_to_string(path),
        }
    }

    /// `strip_namespace` defaults to `true`.
    pub fn extract_root_name(strip_namespace: Option<bool>, variant: &Variant) -> String {
        use Variant::*;
        let strip_namespace = strip_namespace.unwrap_or(true);
        match variant {
            GConst(s)
            | GConstName(s)
            | Constructor(s)
            | AllMembers(s)
            | Extends(s)
            | NotSubtype(s)
            | Module(s)
            | Type(s)
            | Fun(s)
            | Prop(s, _)
            | SProp(s, _)
            | Method(s, _)
            | SMethod(s, _)
            | Const(s, _) => {
                if strip_namespace {
                    strip_ns(s).to_string()
                } else {
                    s.clone()
                }
            }
            Declares => "__declares__".to_string(),
            File(p) => storage_to_string(p),
        }
    }

    pub fn extract_member_name(v: &Variant) -> Option<String> {
        use Variant::*;
        match v {
            GConst(_) | GConstName(_) | Constructor(_) | AllMembers(_) | Extends(_)
            | NotSubtype(_) | Module(_) | Type(_) | Fun(_) | File(_) | Declares => None,
            Const(_cls, s)
            | Prop(_cls, s)
            | SProp(_cls, s)
            | Method(_cls, s)
            | SMethod(_cls, s) => Some(s.clone()),
        }
    }

    pub fn to_decl_reference(v: &Variant) -> DeclReference {
        use Variant::*;
        match v {
            Type(s)
            | Const(s, _)
            | Extends(s)
            | NotSubtype(s)
            | AllMembers(s)
            | Constructor(s)
            | Prop(s, _)
            | SProp(s, _)
            | Method(s, _)
            | SMethod(s, _) => DeclReference::Type(s.clone()),
            GConst(s) | GConstName(s) => DeclReference::GlobalConstant(s.clone()),
            Fun(s) => DeclReference::Function(s.clone()),
            Module(m) => DeclReference::Module(m.clone()),
            Declares => panic!("No Decl_reference.t for Declares Dep.variant"),
            File(_) => panic!("No Decl_reference.t for File Dep.variant"),
        }
    }

    pub fn to_debug_string(dep: T) -> String {
        dep.ocaml_int().to_string()
    }

    pub fn of_debug_string(s: &str) -> T {
        T(super::int_of_string(s) as u64 & !(1 << 63))
    }

    pub fn to_hex_string(dep: T) -> String {
        format!("0x{:016x}", dep.0)
    }

    pub(super) fn pp(fmt: &mut dyn std::fmt::Write, dep: T) -> std::fmt::Result {
        fmt.write_str(&to_hex_string(dep))
    }

    pub fn of_hex_string(s: &str) -> T {
        T(super::int_of_string(s) as u64 & !(1 << 63))
    }

    pub fn variant_to_string(dep: &Variant) -> String {
        use Variant::*;
        let prefix = match dep {
            GConst(_) => "GConst",
            GConstName(_) => "GConstName",
            Const(..) => "Const",
            Type(_) => "Type",
            Fun(_) => "Fun",
            Prop(..) => "Prop",
            SProp(..) => "SProp",
            Method(..) => "Method",
            SMethod(..) => "SMethod",
            Constructor(_) => "Constructor",
            AllMembers(_) => "AllMembers",
            Extends(_) => "Extends",
            NotSubtype(_) => "NotSubtype",
            Module(_) => "Module",
            Declares => "Declares",
            File(_) => "File",
        };
        match dep {
            Declares => prefix.to_string(),
            _ => format!("{} {}", prefix, extract_name(dep)),
        }
    }

    pub fn pp_variant(fmt: &mut dyn std::fmt::Write, variant: &Variant) -> std::fmt::Result {
        fmt.write_str(&variant_to_string(variant))
    }
}

/// `Wrapped_map.Make (Dep)`: a map ordered by `Dep.compare`. Use the methods
/// of `im::OrdMap` for what `Wrapped_map_sig.S` offers.
pub mod dep_map {
    use super::dep;

    pub type T<A> = im::OrdMap<dep::T, A>;

    /// `Wrapped_map.make_pp Dep.pp pp_data`.
    ///
    /// `pp_data` gives the text of a value. The layout is the one `Format`
    /// computes at its default margin when that text holds no break hint, and
    /// the map is printed from the start of a line.
    pub fn pp<A>(
        pp_data: impl Fn(&mut dyn std::fmt::Write, &A) -> std::fmt::Result,
        fmt: &mut dyn std::fmt::Write,
        x: &T<A>,
    ) -> std::fmt::Result {
        // "@[<hv 2>{" [" "] ("@[" key " ->@ " data "@]") sep by ";@ " [" "] "}@]"
        const MARGIN: usize = 78;
        let mut bindings: Vec<(String, String)> = Vec::with_capacity(x.len());
        for (key, data) in x.iter() {
            let mut k = String::new();
            dep::pp(&mut k, *key)?;
            let mut d = String::new();
            pp_data(&mut d, data)?;
            bindings.push((k, d));
        }
        if bindings.is_empty() {
            return fmt.write_str("{}");
        }
        let width = |s: &str| s.chars().count();
        let flat: usize = 4
            + bindings
                .iter()
                .map(|(k, d)| width(k) + 4 + width(d))
                .sum::<usize>()
            + 2 * (bindings.len() - 1);
        // In a "hv" box either no break hint breaks, or all do.
        let breaks = flat > MARGIN;
        fmt.write_str("{ ")?;
        // The column of the current output, and the one the "hv" box
        // indents to.
        let mut column = 2;
        let indent = 2;
        for (i, (k, d)) in bindings.iter().enumerate() {
            if i > 0 {
                fmt.write_char(';')?;
                if breaks {
                    fmt.write_char('\n')?;
                    fmt.write_str(&" ".repeat(indent))?;
                    column = indent;
                } else {
                    fmt.write_char(' ')?;
                    column += 2;
                }
            }
            let box_column = column;
            fmt.write_str(k)?;
            fmt.write_str(" ->")?;
            column += width(k) + 3;
            // The break of the inner box: a new line when what follows, up
            // to the end of that box, does not fit.
            let following = 1 + width(d);
            if column + following > MARGIN {
                fmt.write_char('\n')?;
                fmt.write_str(&" ".repeat(box_column))?;
                column = box_column;
            } else {
                fmt.write_char(' ')?;
                column += 1;
            }
            fmt.write_str(d)?;
            column += width(d);
        }
        fmt.write_str(" }")
    }

    pub fn show<A>(
        pp_data: impl Fn(&mut dyn std::fmt::Write, &A) -> std::fmt::Result,
        x: &T<A>,
    ) -> String {
        let mut s = String::new();
        pp(pp_data, &mut s, x).unwrap();
        s
    }
}

/***********************************************/
/* Dependency tracing                          */
/***********************************************/

/// Whether or not to trace new dependency edges.
///
/// The OCaml starts with `ref true` and its entry points turn tracing off
/// when nobody reads the edges (`Server_env_build`: `trace := not
/// check_mode`). `hh` only has such entry points today, so the flag starts
/// `false`, and recording then costs nothing; a driver that wants the edges
/// does `typing_deps::trace.store(true, Ordering::Relaxed)` first.
pub static trace: AtomicBool = AtomicBool::new(false);

type DependencyCallback = Arc<dyn Fn(&dep::Variant, &dep::Variant) + Send + Sync>;

/// List of callbacks, called when discovering dependency edges
static dependency_callbacks: RwLock<BTreeMap<String, DependencyCallback>> =
    RwLock::new(BTreeMap::new());

/// The number of `dependency_callbacks`, so that `add_idep` does not take
/// the lock when there are none.
static dependency_callbacks_length: AtomicUsize = AtomicUsize::new(0);

pub fn add_dependency_callback(
    name: &str,
    cb: impl Fn(&dep::Variant, &dep::Variant) + Send + Sync + 'static,
) {
    let mut callbacks = dependency_callbacks
        .write()
        .unwrap_or_else(|e| e.into_inner());
    callbacks.insert(name.to_string(), Arc::new(cb));
    dependency_callbacks_length.store(callbacks.len(), Ordering::Release);
}

/// `Stdlib.Hashtbl.iter (fun _ f -> f dependent dependency) dependency_callbacks`
fn call_dependency_callbacks(dependent: &dep::Variant, dependency: &dep::Variant) {
    if dependency_callbacks_length.load(Ordering::Acquire) == 0 {
        return;
    }
    // The callbacks run without the lock: one may register another.
    let callbacks: Vec<DependencyCallback> = dependency_callbacks
        .read()
        .unwrap_or_else(|e| e.into_inner())
        .values()
        .cloned()
        .collect();
    for f in callbacks {
        f(dependent, dependency)
    }
}

/// Set of dependencies used for the custom system.
///
/// The OCaml type is a persistent Rust set behind a pointer; its elements
/// come in no particular order. Here they come in the order of
/// `Dep.compare`.
pub mod dep_set {
    use super::dep;

    pub type T = im::OrdSet<dep::T>;

    pub type Elt = dep::T;

    pub fn make() -> T {
        T::new()
    }

    pub fn singleton(elt: Elt) -> T {
        T::unit(elt)
    }

    pub fn add(s: &T, elt: Elt) -> T {
        s.update(elt)
    }

    pub fn union(s1: &T, s2: &T) -> T {
        // Loop over the smaller set: the sizes of the arguments are expected
        // to be very skewed.
        let (bigger, smaller) = if s1.len() > s2.len() {
            (s1, s2)
        } else {
            (s2, s1)
        };
        let mut bigger = bigger.clone();
        for dep in smaller.iter() {
            bigger.insert(*dep);
        }
        bigger
    }

    pub fn inter(s1: &T, s2: &T) -> T {
        let (bigger, smaller) = if s1.len() > s2.len() {
            (s1, s2)
        } else {
            (s2, s1)
        };
        let mut result = T::new();
        for dep in smaller.iter() {
            if bigger.contains(dep) {
                result.insert(*dep);
            }
        }
        result
    }

    pub fn diff(s1: &T, s2: &T) -> T {
        let mut result = s1.clone();
        if s1.len() < s2.len() {
            for dep in s1.iter() {
                if s2.contains(dep) {
                    result.remove(dep);
                }
            }
        } else {
            for dep in s2.iter() {
                result.remove(dep);
            }
        }
        result
    }

    pub fn mem(s: &T, elt: Elt) -> bool {
        s.contains(&elt)
    }

    pub fn elements(s: &T) -> Vec<Elt> {
        s.iter().copied().collect()
    }

    pub fn cardinal(s: &T) -> isize {
        s.len() as isize
    }

    pub fn is_empty(s: &T) -> bool {
        s.is_empty()
    }

    pub fn of_list(xs: &[Elt]) -> T {
        xs.iter().copied().collect()
    }

    pub fn iter(s: &T, mut f: impl FnMut(Elt)) {
        for x in elements(s) {
            f(x)
        }
    }

    pub fn fold<A>(s: &T, init: A, mut f: impl FnMut(Elt, A) -> A) -> A {
        let l = elements(s);
        l.into_iter().fold(init, |acc, x| f(x, acc))
    }

    pub fn fold_result<A, E>(
        s: &T,
        init: A,
        mut f: impl FnMut(Elt, A) -> Result<A, E>,
    ) -> Result<A, E> {
        let l = elements(s);
        let mut acc = init;
        for x in l {
            acc = f(x, acc)?;
        }
        Ok(acc)
    }

    pub fn pp(fmt: &mut dyn std::fmt::Write, s: &T) -> std::fmt::Result {
        fmt.write_str("{ ")?;
        for x in elements(s) {
            write!(fmt, "{:x}; ", dep::to_int64(x))?;
        }
        fmt.write_str("}")
    }

    pub fn show(s: &T) -> String {
        let mut out = String::new();
        pp(&mut out, s).unwrap();
        out
    }
}

pub mod dep_hash_key {
    use std::cmp::Ordering;

    use super::dep;

    pub type T = dep::T;

    pub fn compare(a: T, b: T) -> Ordering {
        a.cmp(&b)
    }

    pub fn to_string(t: T) -> String {
        dep::to_debug_string(t)
    }
}

pub mod visited_set {
    use hash::HashSet;

    /// The set of the hashes that a traversal has visited; `get_extend_deps`
    /// adds to it.
    #[derive(Debug, Default)]
    pub struct T(pub(super) HashSet<depgraph_dep::Dep>);

    pub fn make() -> T {
        T(HashSet::default())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DepEdge {
    /// The node depending on the dependency
    idependent: dep::T,
    /// The node the dependent depends upon
    idependency: dep::T,
}

/// `exception Depgraph_unavailable of depgraph_load_error`: the payload of
/// the panic that the functions below raise when the dependency graph cannot
/// be read.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DepgraphUnavailable(pub DepgraphLoadError);

pub fn depgraph_load_error_to_string(error: &DepgraphLoadError) -> String {
    match error {
        DepgraphLoadError::DepgraphNotFound(path) => {
            format!("dependency graph not found: {}", path)
        }
        DepgraphLoadError::DepgraphOpenError(message) => {
            format!("could not open dependency graph: {}", message)
        }
        DepgraphLoadError::DepgraphInvalidMode(message) => {
            format!("invalid dependency graph mode: {}", message)
        }
        DepgraphLoadError::DepgraphNotLoaded => "dependency graph was not loaded".to_string(),
    }
}

/// The printer that the OCaml registers for the exception.
impl std::fmt::Display for DepgraphUnavailable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Typing_deps.Depgraph_unavailable({})",
            depgraph_load_error_to_string(&self.0)
        )
    }
}

impl std::error::Error for DepgraphUnavailable {}

/// `raise (Depgraph_unavailable error)`
fn raise_depgraph_unavailable(error: DepgraphLoadError) -> ! {
    std::panic::panic_any(DepgraphUnavailable(error))
}

/// `DepEdgeSet`: ordered by dependent, then by dependency.
type DepEdgeSet = BTreeSet<DepEdge>;

enum BaseDepGraph<B> {
    Uninitialized,
    Loaded(Option<B>),
}

/// The dependency graph of the saved state (if any) and the delta of the
/// edges added and removed since. (`deps_rust/dep_graph_with_delta.rs`)
struct DepGraphWithDelta<B: BaseDepgraphTrait> {
    /// A structure wrapping the memory-mapped dependency graph.
    ///
    /// `Loaded(None)` means that custom mode is enabled without an existing
    /// saved state, while `Uninitialized` means no load has been attempted.
    base: BaseDepGraph<B>,
    /// The dependency graph delta.
    delta: DepGraphDelta,
}

impl<B: BaseDepgraphTrait> Default for DepGraphWithDelta<B> {
    fn default() -> Self {
        Self {
            base: BaseDepGraph::Uninitialized,
            delta: DepGraphDelta::default(),
        }
    }
}

impl<B: BaseDepgraphTrait> DepGraphWithDelta<B> {
    #[cfg(test)]
    fn new(base: Option<B>, delta: DepGraphDelta) -> Self {
        Self {
            base: BaseDepGraph::Loaded(base),
            delta,
        }
    }

    fn base(&self) -> Option<&B> {
        match &self.base {
            BaseDepGraph::Uninitialized => None,
            BaseDepGraph::Loaded(base) => base.as_ref(),
        }
    }

    fn is_base_loaded(&self) -> bool {
        matches!(self.base, BaseDepGraph::Loaded(_))
    }

    /// Iterates over all dependents of a dependency, with possibly duplicate
    /// dependents.
    fn iter_dependents_with_duplicates<F, R>(&self, dep: depgraph_dep::Dep, mut f: F) -> R
    where
        F: FnMut(&mut dyn Iterator<Item = depgraph_dep::Dep>) -> R,
    {
        let Self { delta, .. } = self;
        let base = self.base();
        let HashSetDelta { added, removed } = delta.get(dep);
        let mut added_iter = added.into_iter().flat_map(|s| s.iter().copied());
        let is_removed = |d: &depgraph_dep::Dep| removed.is_some_and(|removed| removed.contains(d));
        match base {
            None => f(&mut added_iter),
            Some(base) => {
                let base_iter = base.iter_dependents(dep);
                f(&mut added_iter.chain(base_iter.filter(|d| !is_removed(d))))
            }
        }
    }

    fn has_edge(&self, dependent: depgraph_dep::Dep, dependency: depgraph_dep::Dep) -> bool {
        let Self { delta, .. } = self;
        let base = self.base();
        let HashSetDelta { added, removed } = delta.get(dependency);
        added.is_some_and(|added| added.contains(&dependent))
            || (base
                .as_ref()
                .is_some_and(|g| g.dependent_dependency_edge_exists(dependent, dependency))
                && !removed.is_some_and(|removed| removed.contains(&dependent)))
    }

    /// Returns the recursive 'extends' dependents of a dep.
    /// Does not include the dep itself.
    fn get_extend_deps(
        &self,
        visited: &mut HashSet<depgraph_dep::Dep>,
        source_class: depgraph_dep::Dep,
        acc: &mut dep_set::T,
    ) {
        let mut queue = VecDeque::new();
        self.get_extend_deps_visit(visited, &mut queue, source_class, acc);
        while let Some(source_class) = queue.pop_front() {
            self.get_extend_deps_visit(visited, &mut queue, source_class, acc);
        }
    }

    /// Helper function to recursively get extend deps
    fn get_extend_deps_visit(
        &self,
        visited: &mut HashSet<depgraph_dep::Dep>,
        queue: &mut VecDeque<depgraph_dep::Dep>,
        source_class: depgraph_dep::Dep,
        acc: &mut dep_set::T,
    ) {
        if !visited.insert(source_class) {
            return;
        }
        if source_class.is_class() {
            let extends_hash = source_class.class_to_extends().unwrap();
            self.iter_dependents_with_duplicates(extends_hash, |iter| {
                iter.for_each(|dep: depgraph_dep::Dep| {
                    if dep.is_class() {
                        let elt = dep::T::from(dep);
                        if !acc.contains(&elt) {
                            acc.insert(elt);
                            queue.push_back(dep);
                        }
                    }
                })
            });
        }
    }

    /// Returns the union of the provided dep set and their recursive
    /// 'extends' dependents.
    fn add_extend_deps(&self, acc: &mut dep_set::T) {
        let mut visited = HashSet::default();
        let mut queue = VecDeque::new();
        for source_class in acc.iter() {
            queue.push_back(depgraph_dep::Dep::from(*source_class));
        }
        while let Some(source_class) = queue.pop_front() {
            self.get_extend_deps_visit(&mut visited, &mut queue, source_class, acc);
        }
    }

    /// The fanout of a member `m` in type `A` contains:
    /// - the members `m` in descendants of `A` down to the first members `m`
    ///   which are declared.
    /// - the dependents of those members `m` in descendants,
    ///   but excluding dependents of declared members.
    ///
    /// We also include `A::m` itself in the result.
    /// The computed fanout is added to the provided fanout accumulator.
    fn get_member_fanout(
        &self,
        class_dep: depgraph_dep::Dep,
        member_type: DepType,
        member_name: &str,
        fanout_acc: &mut dep_set::T,
    ) {
        let mut queue = VecDeque::new();
        let mut visited = HashSet::default();

        self.visit_class_dep_for_member_fanout(
            class_dep,
            member_type,
            member_name,
            &mut visited,
            &mut queue,
            fanout_acc,
            false,
        );

        while let Some(class_dep) = queue.pop_front() {
            self.visit_class_dep_for_member_fanout(
                class_dep,
                member_type,
                member_name,
                &mut visited,
                &mut queue,
                fanout_acc,
                true,
            );
        }
    }

    fn visit_class_dep_for_member_fanout(
        &self,
        class_dep: depgraph_dep::Dep,
        member_type: DepType,
        member_name: &str,
        visited: &mut HashSet<depgraph_dep::Dep>,
        queue: &mut VecDeque<depgraph_dep::Dep>,
        fanout_acc: &mut dep_set::T,
        stop_if_declared: bool,
    ) {
        if !visited.insert(class_dep) {
            return;
        }
        fanout_acc.insert(dep::T::from(class_dep));
        let member_dep = class_dep.member(member_type, member_name);
        let mut member_is_declared = false;
        let mut member_deps = HashSet::default();
        self.iter_dependents_with_duplicates(member_dep, |deps| {
            for dep in deps {
                if dep.is_declares() {
                    member_is_declared = true;
                    if stop_if_declared {
                        break;
                    }
                } else {
                    member_deps.insert(dep);
                }
            }
        });
        if !(stop_if_declared && member_is_declared) {
            member_deps.into_iter().for_each(|dep| {
                fanout_acc.insert(dep::T::from(dep));
            });
            let extends_dep_for_class = class_dep.class_to_extends().unwrap();
            self.iter_dependents_with_duplicates(extends_dep_for_class, |iter| {
                iter.for_each(|dep| queue.push_back(dep));
            });
        }
    }

    /// Follow any NotSubtype edge from provided deps and add these edges'
    /// ends to the fanout.
    fn get_not_subtype_fanout(&self, deps: &dep_set::T, fanout_acc: &mut dep_set::T) {
        for class_dep in deps.iter() {
            let not_subtype_dep = depgraph_dep::Dep::from(*class_dep).class_to_not_subtype();
            self.iter_dependents_with_duplicates(not_subtype_dep, |deps| {
                for dep in deps {
                    fanout_acc.insert(dep::T::from(dep));
                }
            });
        }
    }
}

impl DepGraphWithDelta<DepGraph> {
    /// Load the graph using the given mode.
    ///
    /// The mode is only used on the first call, to establish some global
    /// state, and then ignored for future calls.
    fn load_base(&mut self, mode: &mode::T) -> Result<(), DepgraphLoadError> {
        if !self.is_base_loaded() {
            self.base = BaseDepGraph::Loaded(Self::base_dep_graph_from_mode(mode)?);
        }
        Ok(())
    }

    /// Override the loaded dep graph.
    fn replace_dep_graph(&mut self, mode: &mode::T) -> Result<(), DepgraphLoadError> {
        self.base = BaseDepGraph::Loaded(Self::base_dep_graph_from_mode(mode)?);
        Ok(())
    }

    fn base_dep_graph_from_mode(mode: &mode::T) -> Result<Option<DepGraph>, DepgraphLoadError> {
        match mode {
            InMemoryMode(None)
            | SaveToDiskMode {
                graph: None,
                new_edges_dir: _,
                human_readable_dep_map_dir: _,
            } => {
                // Enabled, but we don't have a saved-state, so we can't open it
                Ok(None)
            }
            InMemoryMode(Some(depgraph_fn))
            | SaveToDiskMode {
                graph: Some(depgraph_fn),
                new_edges_dir: _,
                human_readable_dep_map_dir: _,
            } => {
                let depgraph = DepGraph::from_path(depgraph_fn).map_err(|error| {
                    if error.kind() == ErrorKind::NotFound {
                        DepgraphLoadError::DepgraphNotFound(depgraph_fn.clone())
                    } else {
                        DepgraphLoadError::DepgraphOpenError(format!(
                            "could not open dep graph file {depgraph_fn:?}: {error}"
                        ))
                    }
                })?;
                Ok(Some(depgraph))
            }
        }
    }
}

/// Graph management in the new system with custom file format.
mod custom_graph {
    use super::*;

    /// The memory-mapped dependency graph and the delta, of the process.
    ///
    /// The base is `Loaded(None)` when custom mode is enabled without an
    /// existing saved-state.
    static DEP_GRAPH: LazyLock<RwLock<DepGraphWithDelta<DepGraph>>> =
        LazyLock::new(|| RwLock::new(DepGraphWithDelta::default()));

    fn read() -> RwLockReadGuard<'static, DepGraphWithDelta<DepGraph>> {
        DEP_GRAPH.read().unwrap_or_else(|e| e.into_inner())
    }

    fn write() -> RwLockWriteGuard<'static, DepGraphWithDelta<DepGraph>> {
        DEP_GRAPH.write().unwrap_or_else(|e| e.into_inner())
    }

    /// Locks the depgraph for reading, loading it first if need be.
    fn read_mode(
        mode: &mode::T,
    ) -> Result<RwLockReadGuard<'static, DepGraphWithDelta<DepGraph>>, DepgraphLoadError> {
        load_ffi(mode)?;
        Ok(read())
    }

    static allow_reads_ref: AtomicBool = AtomicBool::new(false);

    pub(super) fn allow_dependency_table_reads(flag: bool) -> bool {
        assert!(!is_worker_process());
        allow_reads_ref.swap(flag, Ordering::SeqCst)
    }

    fn get_or_raise<A>(result: Result<A, DepgraphLoadError>) -> A {
        match result {
            Ok(value) => value,
            Err(error) => raise_depgraph_unavailable(error),
        }
    }

    /// `hh_custom_dep_graph_load`
    fn load_ffi(mode: &mode::T) -> Result<(), DepgraphLoadError> {
        // The mode is only used on the first call.
        if read().is_base_loaded() {
            return Ok(());
        }
        write().load_base(mode)
    }

    /// `hh_custom_dep_graph_replace`
    fn replace_ffi(mode: &mode::T) -> Result<(), DepgraphLoadError> {
        write().replace_dep_graph(mode)
    }

    enum DepgraphHasEdgeResult {
        EdgeAbsent,
        EdgePresent,
        EdgeNotLoaded,
        EdgeInternalError,
    }

    /// `hh_depgraph_has_edge`
    fn depgraph_has_edge_ffi(dependent: dep::T, dependency: dep::T) -> DepgraphHasEdgeResult {
        match std::panic::catch_unwind(|| {
            let graph = read();
            if !graph.is_base_loaded() {
                return DepgraphHasEdgeResult::EdgeNotLoaded;
            }
            if graph.has_edge(dependent.into(), dependency.into()) {
                DepgraphHasEdgeResult::EdgePresent
            } else {
                DepgraphHasEdgeResult::EdgeAbsent
            }
        }) {
            Ok(status) => status,
            Err(_) => DepgraphHasEdgeResult::EdgeInternalError,
        }
    }

    pub(super) fn ensure_loaded(mode: &mode::T) {
        get_or_raise(load_ffi(mode))
    }

    pub(super) fn replace(mode: &mode::T) {
        get_or_raise(replace_ffi(mode))
    }

    #[allow(dead_code)] // (Its callers lock the graph once: `depgraph_retain_absent_edges`.)
    pub(super) fn depgraph_has_edge(dependent: dep::T, dependency: dep::T) -> bool {
        match depgraph_has_edge_ffi(dependent, dependency) {
            DepgraphHasEdgeResult::EdgeAbsent => false,
            DepgraphHasEdgeResult::EdgePresent => true,
            DepgraphHasEdgeResult::EdgeNotLoaded => {
                raise_depgraph_unavailable(DepgraphLoadError::DepgraphNotLoaded)
            }
            DepgraphHasEdgeResult::EdgeInternalError => {
                raise_depgraph_unavailable(DepgraphLoadError::DepgraphOpenError(
                    "internal error while reading the loaded dependency graph".to_string(),
                ))
            }
        }
    }

    /// `hh_custom_dep_graph_get_ideps_from_hash`
    fn get_ideps_from_hash_ffi(
        mode: &mode::T,
        dep: dep::T,
    ) -> Result<dep_set::T, DepgraphLoadError> {
        let deps = read_mode(mode)?.iter_dependents_with_duplicates(dep.into(), |iter_dep| {
            iter_dep.map(dep::T::from).collect::<dep_set::T>()
        });
        Ok(deps)
    }

    pub(super) fn get_ideps_from_hash(mode: &mode::T, dep: dep::T) -> dep_set::T {
        get_or_raise(get_ideps_from_hash_ffi(mode, dep))
    }

    /// `hh_custom_dep_graph_add_typing_deps`: the union of the provided dep
    /// set and their direct typing dependents.
    fn add_typing_deps_ffi(
        mode: &mode::T,
        query: &dep_set::T,
    ) -> Result<dep_set::T, DepgraphLoadError> {
        let mut acc = query.clone();
        let graph = read_mode(mode)?;
        for dependency in query.iter() {
            graph.iter_dependents_with_duplicates((*dependency).into(), |iter| {
                iter.for_each(|dependent| {
                    acc.insert(dep::T::from(dependent));
                })
            })
        }
        Ok(acc)
    }

    pub(super) fn add_typing_deps(mode: &mode::T, deps: &dep_set::T) -> dep_set::T {
        get_or_raise(add_typing_deps_ffi(mode, deps))
    }

    /// `hh_custom_dep_graph_add_extend_deps`: the union of the provided dep
    /// set and their recursive 'extends' dependents.
    fn add_extend_deps_ffi(
        mode: &mode::T,
        query: &dep_set::T,
    ) -> Result<dep_set::T, DepgraphLoadError> {
        let mut acc = query.clone();
        read_mode(mode)?.add_extend_deps(&mut acc);
        Ok(acc)
    }

    pub(super) fn add_extend_deps(mode: &mode::T, deps: &dep_set::T) -> dep_set::T {
        get_or_raise(add_extend_deps_ffi(mode, deps))
    }

    /// `hh_custom_dep_graph_get_extend_deps`: the recursive 'extends'
    /// dependents of a dep.
    fn get_extend_deps_ffi(
        mode: &mode::T,
        visited: &mut visited_set::T,
        source_class: dep::T,
        acc: &dep_set::T,
    ) -> Result<dep_set::T, DepgraphLoadError> {
        let mut acc = acc.clone();
        read_mode(mode)?.get_extend_deps(&mut visited.0, source_class.into(), &mut acc);
        Ok(acc)
    }

    pub(super) fn get_extend_deps(
        mode: &mode::T,
        visited: &mut visited_set::T,
        source_class: dep::T,
        acc: &dep_set::T,
    ) -> dep_set::T {
        get_or_raise(get_extend_deps_ffi(mode, visited, source_class, acc))
    }

    /// `hh_get_member_fanout`
    fn get_member_fanout_ffi(
        mode: &mode::T,
        class_dep: dep::T,
        member_type: dep::DepKind,
        member_name: &str,
        fanout_acc: &dep_set::T,
    ) -> Result<dep_set::T, DepgraphLoadError> {
        let mut fanout_acc = fanout_acc.clone();
        read_mode(mode)?.get_member_fanout(
            class_dep.into(),
            dep::dep_type_of_dep_kind(member_type),
            member_name,
            &mut fanout_acc,
        );
        Ok(fanout_acc)
    }

    pub(super) fn get_member_fanout(
        mode: &mode::T,
        class_dep: dep::T,
        member_type: dep::DepKind,
        member_name: &str,
        fanout_acc: &dep_set::T,
    ) -> dep_set::T {
        get_or_raise(get_member_fanout_ffi(
            mode,
            class_dep,
            member_type,
            member_name,
            fanout_acc,
        ))
    }

    /// `hh_get_not_subtype_fanout`
    fn get_not_subtype_fanout_ffi(
        mode: &mode::T,
        deps: &dep_set::T,
        fanout_acc: &dep_set::T,
    ) -> Result<dep_set::T, DepgraphLoadError> {
        let mut fanout_acc = fanout_acc.clone();
        read_mode(mode)?.get_not_subtype_fanout(deps, &mut fanout_acc);
        Ok(fanout_acc)
    }

    pub(super) fn get_not_subtype_fanout(
        mode: &mode::T,
        deps: &dep_set::T,
        fanout_acc: &dep_set::T,
    ) -> dep_set::T {
        get_or_raise(get_not_subtype_fanout_ffi(mode, deps, fanout_acc))
    }

    /// `hh_custom_dep_graph_register_discovered_dep_edge`: add edge into the
    /// in-memory depgraph delta
    #[allow(dead_code)] // (`register_discovered_dep_edges` locks the graph once.)
    fn register_discovered_dep_edge(dependent: dep::T, dependency: dep::T) {
        write().delta.insert(dependent.into(), dependency.into());
    }

    /// `hh_custom_dep_graph_remove_edge`
    fn remove_edge(dependent: dep::T, dependency: dep::T) {
        write().delta.remove(dependent.into(), dependency.into());
    }

    /// `hh_custom_dep_graph_dep_graph_delta_num_edges`
    pub(super) fn dep_graph_delta_num_edges() -> isize {
        read().delta.added_edges_count() as isize
    }

    /// `hh_custom_dep_graph_save_delta`
    pub(super) fn save_delta(dest: &str, reset_state_after_saving: bool) -> isize {
        let f = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(dest)
            .unwrap();
        let mut w = std::io::BufWriter::new(f);
        let mut graph = write();
        let hashes_added = graph.delta.write_added_edges_to(&mut w).unwrap();
        w.into_inner().unwrap();

        if reset_state_after_saving {
            graph.delta.clear();
        }
        hashes_added as isize
    }

    pub(super) fn add_all_deps(mode: &mode::T, x: &dep_set::T) -> dep_set::T {
        add_typing_deps(mode, &add_extend_deps(mode, x))
    }

    thread_local! {
        /// A batch of discovered dependency edges, of which some might
        /// already be in the dependency graph!
        static discovered_deps_batch: RefCell<HashSet<DepEdge>> =
            RefCell::new(HashSet::default());

        /// A batch of dependency edges that are not yet in the dependency
        /// graph.
        pub(super) static filtered_deps_batch: RefCell<DepEdgeSet> =
            const { RefCell::new(DepEdgeSet::new()) };
    }

    /// Filter out the discovered dep edges which are already in the dep
    /// graph. Get `filtered_deps_batch` to obtain the result.
    pub(super) fn filter_discovered_deps_batch(mode: &mode::T) {
        // Empty discovered_deps_bach by checking for each edge whether it's
        // already in the dependency graph. If it is not, add it to the
        // filtered deps batch.
        discovered_deps_batch.with(|batch| {
            let mut batch = batch.borrow_mut();
            if !batch.is_empty() {
                ensure_loaded(mode);
            }
            filtered_deps_batch.with(|s| {
                let mut s = s.borrow_mut();
                // (`depgraph_has_edge` of each edge, with the graph locked
                // once for the batch.)
                depgraph_retain_absent_edges(batch.iter(), |edge| {
                    s.insert(*edge);
                });
            });
            batch.clear();
        })
    }

    /// `depgraph_has_edge` of each of `edges`, with the graph locked once:
    /// `absent` is called with those that are not in the graph.
    pub(super) fn depgraph_retain_absent_edges<'e>(
        edges: impl Iterator<Item = &'e DepEdge>,
        mut absent: impl FnMut(&'e DepEdge),
    ) {
        let mut edges = edges.peekable();
        if edges.peek().is_none() {
            return;
        }
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let graph = read();
            if !graph.is_base_loaded() {
                return Err(DepgraphHasEdgeResult::EdgeNotLoaded);
            }
            let mut absents = vec![];
            for edge in edges {
                if !graph.has_edge(edge.idependent.into(), edge.idependency.into()) {
                    absents.push(edge);
                }
            }
            Ok(absents)
        }));
        match result {
            Ok(Ok(absents)) => absents.into_iter().for_each(&mut absent),
            Ok(Err(_)) => raise_depgraph_unavailable(DepgraphLoadError::DepgraphNotLoaded),
            Err(_) => raise_depgraph_unavailable(DepgraphLoadError::DepgraphOpenError(
                "internal error while reading the loaded dependency graph".to_string(),
            )),
        }
    }

    pub(super) fn register_discovered_dep_edges(s: &DepEdgeSet) {
        assert!(!is_worker_process());
        // (`register_discovered_dep_edge` of each edge, with the graph
        // locked once.)
        let mut graph = write();
        for DepEdge {
            idependent,
            idependency,
        } in s
        {
            graph.delta.insert((*idependent).into(), (*idependency).into());
        }
    }

    pub(super) fn remove_edges(s: &DepEdgeSet) {
        assert!(!is_worker_process());
        for DepEdge {
            idependent,
            idependency,
        } in s
        {
            remove_edge(*idependent, *idependency)
        }
    }

    /// Not in the OCaml: whether `add_idep` has no effect (nothing traces,
    /// no callbacks).
    pub(super) fn add_idep_is_noop() -> bool {
        !trace.load(Ordering::Relaxed) && dependency_callbacks_length.load(Ordering::Acquire) == 0
    }

    pub(super) fn add_idep(mode: &mode::T, dependent: &dep::Variant, dependency: &dep::Variant) {
        // Not in the OCaml: when nothing below can have an effect, do not
        // even compute the hashes.
        if add_idep_is_noop() {
            return;
        }
        let tracing = trace.load(Ordering::Relaxed);
        let idependent = dep::make(dependent);
        let idependency = dep::make(dependency);
        if idependent == idependency {
        } else {
            call_dependency_callbacks(dependent, dependency);
            if tracing {
                let length = discovered_deps_batch.with(|batch| {
                    let mut batch = batch.borrow_mut();
                    batch.insert(DepEdge {
                        idependent,
                        idependency,
                    });
                    batch.len()
                });
                if length >= 1000 {
                    filter_discovered_deps_batch(mode)
                }
            }
        }
    }

    pub(super) fn dump_current_edge_buffer(deps_to_symbol_map: Option<&dep_map::T<dep::Variant>>) {
        let hash_to_string = |dep: dep::T| match deps_to_symbol_map {
            None => dep::to_hex_string(dep),
            Some(map) => match map.get(&dep) {
                None => dep::to_hex_string(dep),
                Some(symbol) => dep::variant_to_string(symbol),
            },
        };
        // The OCaml prints the edges in the order of its hash table; here
        // they are sorted.
        let edges: DepEdgeSet =
            discovered_deps_batch.with(|batch| batch.borrow().iter().copied().collect());
        for DepEdge {
            idependent,
            idependency,
        } in edges
        {
            println!(
                "{} -> {}",
                hash_to_string(idependency),
                hash_to_string(idependent)
            );
        }
    }
}

/// `Out_channel.create ~append:true ~perm:0o600`
fn out_channel_create_append(filepath: &std::path::Path) -> std::io::BufWriter<std::fs::File> {
    use std::os::unix::fs::OpenOptionsExt;
    let file = std::fs::OpenOptions::new()
        .write(true)
        .create(true)
        .append(true)
        .mode(0o600)
        .open(filepath)
        .unwrap_or_else(|e| panic!("{}: {}", filepath.display(), e));
    std::io::BufWriter::new(file)
}

mod save_human_readable_dep_map {
    use super::*;

    fn should_save(mode: &mode::T) -> bool {
        matches!(
            mode,
            SaveToDiskMode {
                human_readable_dep_map_dir: Some(_),
                ..
            }
        )
    }

    const set_max_size: usize = 20000;

    thread_local! {
        static human_readable_dep_map_channel_ref:
            RefCell<Option<std::io::BufWriter<std::fs::File>>> = const { RefCell::new(None) };

        /// The set of the seen (hashcode, dependency name)s, per worker.
        /// Use the name as well as the hashcode in case of hashcode
        /// conflicts.
        static seen_set_ref: RefCell<BTreeSet<(dep::T, String)>> =
            const { RefCell::new(BTreeSet::new()) };
    }

    fn with_human_readable_dep_map_channel<A>(
        mode: &mode::T,
        f: impl FnOnce(&mut std::io::BufWriter<std::fs::File>) -> A,
    ) -> A {
        human_readable_dep_map_channel_ref.with(|channel| {
            let mut channel = channel.borrow_mut();
            if channel.is_none() {
                let directory = match mode {
                    SaveToDiskMode {
                        human_readable_dep_map_dir: Some(d),
                        ..
                    } => d,
                    _ => panic!("programming error: no human_readable_dep_map_dir"),
                };
                let directory = std::path::Path::new(directory);
                if !directory.is_dir() {
                    std::fs::create_dir_all(directory)
                        .unwrap_or_else(|e| panic!("{}: {}", directory.display(), e));
                }
                let worker_id_ = worker_id.get().expect("Option.value_exn None");
                // To avoid multiple workers interleaving writes to the same
                // file, rely on unique worker id's to have each one write to
                // separate files. Appending lets a new worker write to the
                // previously created logs if they happened to share the same
                // id.
                let filepath = directory.join(format!("human-readable-dep-map-{}.txt", worker_id_));
                *channel = Some(out_channel_create_append(&filepath));
            }
            f(channel.as_mut().unwrap())
        })
    }

    /// Take the current set of human readable deps and writes them to disk.
    /// Reset the set of human readable deps to be empty.
    /// If `flush` (default `false`), flush the channel after the write.
    pub(super) fn export_to_disk(flush: Option<bool>, mode: &mode::T) {
        let flush = flush.unwrap_or(false);
        if should_save(mode) {
            let ss = seen_set_ref.with(|ss| std::mem::take(&mut *ss.borrow_mut()));
            with_human_readable_dep_map_channel(mode, |out_channel| {
                for (hash, name) in ss {
                    writeln!(out_channel, "{} {}", dep::to_int64(hash), name).unwrap();
                }
                if flush {
                    out_channel.flush().unwrap()
                }
            })
        }
    }

    /// Add a dep to the current set of human readable deps.
    pub(super) fn add(mode: &mode::T, (dep, hash): (&dep::Variant, dep::T)) {
        if should_save(mode) {
            let name = dep::variant_to_string(dep);
            let length = seen_set_ref.with(|ss| {
                let mut ss = ss.borrow_mut();
                ss.insert((hash, name));
                ss.len()
            });
            if length >= set_max_size {
                export_to_disk(None, mode)
            }
        }
    }

    /// Whether `add` does anything in this mode.
    pub(super) fn is_saving(mode: &mode::T) -> bool {
        should_save(mode)
    }
}

mod save_custom_graph {
    use super::*;

    thread_local! {
        static discovered_deps_batch: RefCell<HashSet<DepEdge>> =
            RefCell::new(HashSet::default());

        static destination_file_handle_ref:
            RefCell<Option<std::io::BufWriter<std::fs::File>>> = const { RefCell::new(None) };
    }

    fn destination_filepath(mode: &mode::T) -> std::path::PathBuf {
        match mode {
            SaveToDiskMode { new_edges_dir, .. } => {
                let worker_id_ = worker_id.get().expect("Option.value_exn None");
                std::path::Path::new(new_edges_dir)
                    .join(format!("new-edges-worker-{}.bin", worker_id_))
            }
            _ => panic!("programming error: wrong mode"),
        }
    }

    fn with_destination_file_handle<A>(
        mode: &mode::T,
        f: impl FnOnce(&mut std::io::BufWriter<std::fs::File>) -> A,
    ) -> A {
        destination_file_handle_ref.with(|handle| {
            let mut handle = handle.borrow_mut();
            if handle.is_none() {
                let filepath = destination_filepath(mode);
                *handle = Some(out_channel_create_append(&filepath));
            }
            f(handle.as_mut().unwrap())
        })
    }

    /// Write to disk the dep edges which are not already in the depgraph.
    pub(super) fn filter_discovered_deps_batch(flush: bool, mode: &mode::T) {
        with_destination_file_handle(mode, |handle| {
            discovered_deps_batch.with(|batch| {
                let mut batch = batch.borrow_mut();
                if !batch.is_empty() {
                    custom_graph::ensure_loaded(mode);
                }
                // (`depgraph_has_edge` of each edge, with the graph locked
                // once for the batch.)
                custom_graph::depgraph_retain_absent_edges(
                    batch.iter(),
                    |DepEdge {
                         idependent,
                         idependency,
                     }| {
                        /* To be kept in sync with `DepGraphDelta::write_added_edges_to`! */

                        /* Write dependency, with a tag bit set to indicate
                         * this is a dependency. */
                        let idependency = dep::to_int64(*idependency) as u64 | 1 << 63;
                        handle.write_all(&idependency.to_le_bytes()).unwrap();

                        /* Write dependent. */
                        let idependent = dep::to_int64(*idependent) as u64;
                        handle.write_all(&idependent.to_le_bytes()).unwrap();
                    },
                );
                if flush {
                    handle.flush().unwrap()
                }
                batch.clear()
            })
        })
    }

    /// Not in the OCaml: whether `add_idep` has no effect (nothing traces,
    /// no callbacks, nothing saved).
    pub(super) fn add_idep_is_noop(mode: &mode::T) -> bool {
        !trace.load(Ordering::Relaxed)
            && dependency_callbacks_length.load(Ordering::Acquire) == 0
            && !save_human_readable_dep_map::is_saving(mode)
    }

    pub(super) fn add_idep(mode: &mode::T, dependent: &dep::Variant, dependency: &dep::Variant) {
        // Not in the OCaml: when nothing below can have an effect, do not
        // even compute the hashes.
        if add_idep_is_noop(mode) {
            return;
        }
        let tracing = trace.load(Ordering::Relaxed);
        let idependent = dep::make(dependent);
        let idependency = dep::make(dependency);
        if idependent == idependency {
        } else {
            call_dependency_callbacks(dependent, dependency);
            if tracing {
                let length = discovered_deps_batch.with(|batch| {
                    let mut batch = batch.borrow_mut();
                    batch.insert(DepEdge {
                        idependent,
                        idependency,
                    });
                    batch.len()
                });
                if length >= 1000 {
                    filter_discovered_deps_batch(false, mode)
                }
            }
            save_human_readable_dep_map::add(mode, (dependent, idependent));
            save_human_readable_dep_map::add(mode, (dependency, idependency))
        }
    }
}

pub fn deps_of_file_info(file_info: &FileInfo) -> Vec<dep::T> {
    let FileInfo {
        ids:
            oxidized::file_info::Ids {
                funs,
                classes,
                typedefs,
                consts,
                modules,
            },
        comments: _,
        file_mode: _,
        position_free_decl_hash: _,
    } = file_info;
    // Every fold of the OCaml conses onto the list.
    let mut defs = vec![];
    for id in consts {
        defs.push(dep::make(&dep::Variant::GConst(id.name.clone())));
    }
    for id in funs {
        defs.push(dep::make(&dep::Variant::Fun(id.name.clone())));
    }
    for id in classes {
        defs.push(dep::make(&dep::Variant::Type(id.name.clone())));
    }
    for id in typedefs {
        defs.push(dep::make(&dep::Variant::Type(id.name.clone())));
    }
    for id in modules {
        defs.push(dep::make(&dep::Variant::Module(id.name.clone())));
    }
    defs.reverse();
    defs
}

pub mod telemetry {
    use super::custom_graph;
    use super::mode;

    pub fn depgraph_delta_num_edges(mode: &mode::T) -> Option<isize> {
        match mode {
            mode::T::InMemoryMode(_) => Some(custom_graph::dep_graph_delta_num_edges()),
            mode::T::SaveToDiskMode { .. } => None,
        }
    }
}

/// The edges a worker discovered, or `None` when they went to disk instead.
pub type DepEdges = Option<BTreeSet<DepEdge>>;

/// As part of few optimizations (prechecked files, interruptible
/// typechecking), we allow the dependency table to get out of date (in order
/// to be able to prioritize other work, like reporting errors in currently
/// open file). This flag is there to avoid accidental reads of this stale
/// data - anyone attempting to do so would either acknowledge that they
/// don't care about accuracy (by setting this flag themselves), or plug in
/// to a hh_server mechanic that will delay executing such command until
/// dependency table is back up to date.
///
/// Return the previous value of the flag.
pub fn allow_dependency_table_reads(mode: &mode::T, flag: bool) -> bool {
    match mode {
        InMemoryMode(_) | SaveToDiskMode { .. } => custom_graph::allow_dependency_table_reads(flag),
    }
}

/// Not in the OCaml: whether `add_idep` in this mode has no effect (nothing
/// traces the edges, no callbacks, nothing saved: a batch check), so that
/// callers can skip building the dependencies they would pass it.
pub fn add_idep_is_noop(mode: &mode::T) -> bool {
    match mode {
        InMemoryMode(_) => custom_graph::add_idep_is_noop(),
        SaveToDiskMode { .. } => save_custom_graph::add_idep_is_noop(mode),
    }
}

pub fn add_idep(mode: &mode::T, dependent: &dep::Variant, dependency: &dep::Variant) {
    match mode {
        InMemoryMode(_) => custom_graph::add_idep(mode, dependent, dependency),
        SaveToDiskMode { .. } => save_custom_graph::add_idep(mode, dependent, dependency),
    }
}

pub fn replace(mode: &mode::T) {
    match mode {
        InMemoryMode(_) => custom_graph::replace(mode),
        _ => {}
    }
}

pub fn dep_edges_make() -> DepEdges {
    Some(DepEdgeSet::new())
}

/// Depending on `mode`, either return discovered edges which are not already
/// in the dep graph or write those edges to disk.
///
/// The edges are those that the calling thread discovered.
pub fn flush_ideps_batch(mode: &mode::T) -> DepEdges {
    match mode {
        InMemoryMode(_) => {
            /* Make sure we don't miss any dependencies! */
            custom_graph::filter_discovered_deps_batch(mode);
            let old_batch =
                custom_graph::filtered_deps_batch.with(|s| std::mem::take(&mut *s.borrow_mut()));
            Some(old_batch)
        }
        SaveToDiskMode { .. } => {
            save_custom_graph::filter_discovered_deps_batch(true, mode);
            save_human_readable_dep_map::export_to_disk(Some(true), mode);
            None
        }
    }
}

pub fn merge_dep_edges(x: DepEdges, y: DepEdges) -> DepEdges {
    match (x, y) {
        (Some(x), Some(y)) => {
            let (mut bigger, smaller) = if x.len() >= y.len() { (x, y) } else { (y, x) };
            bigger.extend(smaller);
            Some(bigger)
        }
        _ => None,
    }
}

/// Register the provided dep edges in the dep table delta.
pub fn register_discovered_dep_edges(edges: &DepEdges) {
    match edges {
        None => {}
        Some(batch) => custom_graph::register_discovered_dep_edges(batch),
    }
}

/// Depending on mode, flush deps to disk or to in-memory depgraph delta
pub fn flush_deps(mode: &mode::T) {
    register_discovered_dep_edges(&flush_ideps_batch(mode))
}

fn remove_edges(mode: &mode::T, edges: &DepEdgeSet) {
    match mode {
        InMemoryMode(_) | SaveToDiskMode { .. } => custom_graph::remove_edges(edges),
    }
}

/// Remove edges `dep -> Declares` for each `dep` in provided dep set
pub fn remove_declared_tags(mode: &mode::T, deps: &dep_set::T) {
    let edges = dep_set::fold(deps, DepEdgeSet::new(), |dep, mut edges_acc| {
        let edge = DepEdge {
            idependency: dep,
            idependent: dep::make(&dep::Variant::Declares),
        };
        edges_acc.insert(edge);
        edges_acc
    });
    remove_edges(mode, &edges)
}

/// Save discovered edges to a binary file.
///
/// - If mode is `InMemoryMode`, the dep table delta is saved.
/// - If mode is `SaveToDiskMode`, an exception is raised.
///
/// Setting `reset_state_after_saving` will empty the dep table delta.
pub fn save_discovered_edges(mode: &mode::T, dest: &str, reset_state_after_saving: bool) -> isize {
    match mode {
        InMemoryMode(_) => custom_graph::save_delta(dest, reset_state_after_saving),
        SaveToDiskMode { .. } => {
            panic!("save_discovered_edges not supported for SaveToDiskMode")
        }
    }
}

pub fn get_ideps_from_hash(mode: &mode::T, hash: dep::T) -> dep_set::T {
    match mode {
        InMemoryMode(_) | SaveToDiskMode { .. } => custom_graph::get_ideps_from_hash(mode, hash),
    }
}

pub fn get_ideps(mode: &mode::T, dependency: &dep::Variant) -> dep_set::T {
    get_ideps_from_hash(mode, dep::make(dependency))
}

/// Add to accumulator all extend dependencies of source_class. Visited is
/// used to avoid processing nodes reachable in multiple ways more than once.
/// In other words: use DFS to find all nodes reachable by "extends" edges
/// starting from source class
pub fn get_extend_deps(
    mode: &mode::T,
    visited: &mut visited_set::T,
    source_class: dep::T,
    acc: &dep_set::T,
) -> dep_set::T {
    custom_graph::get_extend_deps(mode, visited, source_class, acc)
}

/// Grow input set by adding all its extend dependencies (including recursive)
pub fn add_extend_deps(mode: &mode::T, acc: &dep_set::T) -> dep_set::T {
    custom_graph::add_extend_deps(mode, acc)
}

/// Grow input set by adding all its typing dependencies (direct only)
pub fn add_typing_deps(mode: &mode::T, acc: &dep_set::T) -> dep_set::T {
    custom_graph::add_typing_deps(mode, acc)
}

/// add_extend_deps and add_typing_deps chained together
pub fn add_all_deps(mode: &mode::T, acc: &dep_set::T) -> dep_set::T {
    custom_graph::add_all_deps(mode, acc)
}

/// The fanout of a member `m` in type `A` contains:
/// - the members `m` in descendants of `A` down to the first members `m`
///   which are declared.
/// - the dependents of those members `m` in descendants,
///   but excluding dependents of declared members.
///
/// We also include `A::m` itself in the result.
/// The computed fanout is added to the provided DepSet accumulator.
pub fn get_member_fanout(
    mode: &mode::T,
    class_dep: dep::T,
    member: &dep::member::T,
    fanout_acc: &dep_set::T,
) -> dep_set::T {
    let (member_dep_kind, member_name) = dep::member::to_dep_kind_and_name(member);
    custom_graph::get_member_fanout(mode, class_dep, member_dep_kind, member_name, fanout_acc)
}

pub fn get_not_subtype_fanout(
    mode: &mode::T,
    descendant_deps: &dep_set::T,
    fanout_acc: &dep_set::T,
) -> dep_set::T {
    custom_graph::get_not_subtype_fanout(mode, descendant_deps, fanout_acc)
}

/// Print the edges that the calling thread discovered and has not yet
/// filtered.
pub fn dump_current_edge_buffer_in_memory_mode(
    deps_to_symbol_map: Option<&dep_map::T<dep::Variant>>,
) {
    custom_graph::dump_current_edge_buffer(deps_to_symbol_map)
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;
    use std::sync::Mutex;
    use std::sync::MutexGuard;

    use super::dep::Variant;
    use super::dep::Variant::*;
    use super::*;

    fn s(x: &str) -> String {
        x.to_string()
    }

    /// The tests that turn tracing on or use the graph of the process run one
    /// at a time.
    fn global_state() -> MutexGuard<'static, ()> {
        static LOCK: Mutex<()> = Mutex::new(());
        LOCK.lock().unwrap_or_else(|e| e.into_inner())
    }

    /// Tracing is on while this lives.
    struct Tracing;

    impl Tracing {
        fn on() -> Self {
            trace.store(true, Ordering::SeqCst);
            Tracing
        }
    }

    impl Drop for Tracing {
        fn drop(&mut self) {
            trace.store(false, Ordering::SeqCst);
        }
    }

    fn temp_dir(name: &str) -> std::path::PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "hh_typing_deps_test_{}_{}_{}",
            name,
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir_all(&dir).unwrap();
        dir
    }

    fn u(dep: dep::T) -> u64 {
        dep::to_int64(dep) as u64
    }

    // FNV-1a, written out: what `hash1_ocaml` and `hash2_ocaml` computed.
    fn fnv1a(bytes: &[u8]) -> u64 {
        let mut h: u64 = 0xcbf29ce484222325;
        for b in bytes {
            h ^= *b as u64;
            h = h.wrapping_mul(0x100000001b3);
        }
        h
    }

    fn by_hand_hash1(tag: u8, name: &str) -> u64 {
        // `Extends` hashes with the tag of `Type`.
        let key = if tag == 3 { 2 } else { tag };
        let mut bytes = vec![key];
        bytes.extend_from_slice(name.as_bytes());
        let h = fnv1a(&bytes);
        let h = if tag == 2 { (h << 1) | 1 } else { h << 1 };
        h & !(1 << 63)
    }

    fn by_hand_hash2(tag: u8, type_hash: u64, name: &str) -> u64 {
        let mut bytes = vec![tag];
        bytes.extend_from_slice(&type_hash.to_ne_bytes());
        bytes.extend_from_slice(name.as_bytes());
        (fnv1a(&bytes) << 1) & !(1 << 63)
    }

    #[test]
    fn hashes_are_those_of_typing_deps_hash() {
        use typing_deps_hash::hash1;
        use typing_deps_hash::hash2;
        for (cls, member) in [
            ("\\Foo", "bar"),
            ("\\HH\\Lib\\Vec\\C", "__construct"),
            (
                "\\EntReasonablyLongClassNameSinceSomeClassNamesAreLong",
                "TSomeTypeConstant",
            ),
            ("", ""),
            ("\\Ünïcödé", "ω"),
        ] {
            let b = cls.as_bytes();
            let m = member.as_bytes();
            let ty = hash1(DepType::KType, b);
            let cases: Vec<(Variant, u64, u64)> = vec![
                (
                    GConst(s(cls)),
                    hash1(DepType::KGConst, b),
                    by_hand_hash1(0, cls),
                ),
                (Fun(s(cls)), hash1(DepType::KFun, b), by_hand_hash1(1, cls)),
                (Type(s(cls)), ty, by_hand_hash1(2, cls)),
                (
                    Extends(s(cls)),
                    hash1(DepType::KExtends, b),
                    by_hand_hash1(3, cls),
                ),
                (
                    NotSubtype(s(cls)),
                    hash2(DepType::KNotSubtype, ty, b""),
                    by_hand_hash2(15, ty, ""),
                ),
                (
                    Const(s(cls), s(member)),
                    hash2(DepType::KConst, ty, m),
                    by_hand_hash2(5, ty, member),
                ),
                (
                    Constructor(s(cls)),
                    hash2(DepType::KConstructor, ty, b""),
                    by_hand_hash2(6, ty, ""),
                ),
                (
                    Prop(s(cls), s(member)),
                    hash2(DepType::KProp, ty, m),
                    by_hand_hash2(7, ty, member),
                ),
                (
                    SProp(s(cls), s(member)),
                    hash2(DepType::KSProp, ty, m),
                    by_hand_hash2(8, ty, member),
                ),
                (
                    Method(s(cls), s(member)),
                    hash2(DepType::KMethod, ty, m),
                    by_hand_hash2(9, ty, member),
                ),
                (
                    SMethod(s(cls), s(member)),
                    hash2(DepType::KSMethod, ty, m),
                    by_hand_hash2(10, ty, member),
                ),
                (
                    AllMembers(s(cls)),
                    hash2(DepType::KAllMembers, ty, b""),
                    by_hand_hash2(11, ty, ""),
                ),
                (
                    GConstName(s(cls)),
                    hash1(DepType::KGConstName, b),
                    by_hand_hash1(12, cls),
                ),
                (
                    Module(s(cls)),
                    hash1(DepType::KModule, b),
                    by_hand_hash1(13, cls),
                ),
            ];
            for (variant, from_crate, by_hand) in cases {
                let hash = u(dep::make(&variant));
                assert_eq!(hash, from_crate, "{:?}", variant);
                assert_eq!(hash, by_hand, "{:?}", variant);
                // 63 bits.
                assert_eq!(hash >> 63, 0);
                // Only classes have the lowest bit set.
                assert_eq!(
                    dep::is_class(dep::make(&variant)),
                    matches!(variant, Type(_)),
                    "{:?}",
                    variant
                );
            }

            // The relations that the crate `dep` relies on.
            let ty_dep = depgraph_dep::Dep::new(ty);
            assert_eq!(
                depgraph_dep::Dep::from(dep::make(&Extends(s(cls)))),
                ty_dep.class_to_extends().unwrap()
            );
            assert_eq!(
                depgraph_dep::Dep::from(dep::make(&NotSubtype(s(cls)))),
                ty_dep.class_to_not_subtype()
            );
            assert_eq!(
                depgraph_dep::Dep::from(dep::make(&Method(s(cls), s(member)))),
                ty_dep.member(DepType::KMethod, member)
            );
            for (m, variant) in [
                (dep::member::method_(member), Method(s(cls), s(member))),
                (dep::member::smethod(member), SMethod(s(cls), s(member))),
                (dep::member::prop(member), Prop(s(cls), s(member))),
                (dep::member::sprop(member), SProp(s(cls), s(member))),
                (dep::member::const_(member), Const(s(cls), s(member))),
                (dep::member::constructor, Constructor(s(cls))),
                (dep::member::all, AllMembers(s(cls))),
            ] {
                assert_eq!(
                    dep::make_member_dep_from_type_dep(dep::make(&Type(s(cls))), &m),
                    dep::make(&variant)
                );
            }
        }

        assert_eq!(u(dep::make(&Declares)), typing_deps_hash::declares_hash());
        assert_eq!(u(dep::make(&Declares)), by_hand_hash1(14, ""));
        assert!(depgraph_dep::Dep::from(dep::make(&Declares)).is_declares());

        let path = relative_path::RelativePath::make(
            relative_path::Prefix::Root,
            std::path::PathBuf::from("a/b.php"),
        );
        assert_eq!(
            u(dep::make(&File(path.clone()))),
            typing_deps_hash::hash1(DepType::KFile, b"root|a/b.php")
        );
        assert_eq!(u(dep::make(&File(path))), by_hand_hash1(16, "root|a/b.php"));
        let hhi = relative_path::RelativePath::make(
            relative_path::Prefix::Hhi,
            std::path::PathBuf::from("x.hhi"),
        );
        assert_eq!(dep::extract_name(&File(hhi)), "hhi|x.hhi");

        // Values computed outside of Rust (FNV-1a over the tag and the name,
        // shifted, with the class bit), so that a change of the algorithm
        // does not go unnoticed: saved states hold these numbers.
        assert_eq!(
            dep::to_hex_string(dep::make(&Type(s("\\Foo")))),
            "0x4cd17f7c3d7b6feb"
        );
        assert_eq!(
            dep::to_hex_string(dep::make(&Extends(s("\\Foo")))),
            "0x4cd17f7c3d7b6fea"
        );
        assert_eq!(
            dep::to_hex_string(dep::make(&Fun(s("\\foo")))),
            "0x6a49c7ca1caae890"
        );
        assert_eq!(
            dep::to_hex_string(dep::make(&Method(s("\\Foo"), s("bar")))),
            "0x606421a8bb56f41e"
        );
        assert_eq!(
            dep::to_hex_string(dep::make(&Declares)),
            "0x5ec786990c038422"
        );
        // The same hashes as OCaml shows them (`Dep.to_debug_string`).
        assert_eq!(
            dep::to_debug_string(dep::make(&Type(s("\\Foo")))),
            "-3688026448255553557"
        );
        assert_eq!(
            dep::to_debug_string(dep::make(&Declares)),
            "-2393796685034453982"
        );
    }

    #[test]
    fn dep_kinds() {
        use dep::DepKind::*;
        for kind in [
            KGConst,
            KFun,
            KType,
            KExtends,
            KConst,
            KConstructor,
            KProp,
            KSProp,
            KMethod,
            KSMethod,
            KAllMembers,
            KGConstName,
            KModule,
            KDeclares,
            KNotSubtype,
            KFile,
        ] {
            let tag = dep::dep_kind_to_enum(kind);
            assert_eq!(dep::dep_kind_of_enum(tag), Some(kind));
            assert_eq!(dep::dep_type_of_dep_kind(kind).as_u8() as isize, tag);
            assert!(dep::min_dep_kind <= tag && tag <= dep::max_dep_kind);
        }
        assert_eq!(dep::dep_kind_of_enum(4), None);
        assert_eq!(dep::dep_kind_of_enum(17), None);
        assert_eq!(dep::dep_kind_of_variant(&NotSubtype(s("\\C"))), KNotSubtype);
        assert_eq!(dep::dep_kind_to_enum(KNotSubtype), 15);
    }

    /// `Dep.t` is an OCaml `int`: 63 bits, the topmost being the sign.
    #[test]
    fn hashes_as_ocaml_ints() {
        let small = dep::of_hex_string("0x0000000000000003");
        let big = dep::of_hex_string("0x4000000000000001");
        assert_eq!(dep::to_int(small), 3);
        assert_eq!(dep::to_int64(small), 3);
        assert_eq!(dep::to_int(big), -(1 << 62) + 1);
        assert_eq!(dep::to_int64(big), (1 << 62) + 1);
        assert_eq!(dep::to_debug_string(big), "-4611686018427387903");
        assert_eq!(dep::to_hex_string(big), "0x4000000000000001");
        assert_eq!(dep::to_hex_string(small), "0x0000000000000003");
        assert_eq!(dep::of_debug_string("-4611686018427387903"), big);
        assert_eq!(dep::of_debug_string(&dep::to_debug_string(small)), small);
        assert_eq!(dep_hash_key::to_string(big), "-4611686018427387903");
        // `Int.compare`: the hash with the top bit is negative.
        assert_eq!(dep::compare(big, small), std::cmp::Ordering::Less);
        assert_eq!(
            dep_hash_key::compare(small, big),
            std::cmp::Ordering::Greater
        );
        let set = dep_set::of_list(&[small, big]);
        assert_eq!(dep_set::elements(&set), vec![big, small]);
        assert_eq!(dep_set::show(&set), "{ 4000000000000001; 3; }");
        // The conversions to and from the crate `dep`.
        assert_eq!(u64::from(depgraph_dep::Dep::from(big)), (1 << 62) + 1);
        assert_eq!(dep::T::from(depgraph_dep::Dep::new((1 << 62) + 1)), big);
        // Every hash goes there and back.
        for variant in [Type(s("\\A")), Fun(s("\\f")), Method(s("\\A"), s("m"))] {
            let dep = dep::make(&variant);
            assert_eq!(dep::of_debug_string(&dep::to_debug_string(dep)), dep);
            assert_eq!(dep::of_hex_string(&dep::to_hex_string(dep)), dep);
            assert_eq!(dep::T::from(depgraph_dep::Dep::from(dep)), dep);
        }
    }

    #[test]
    fn int_of_string_as_in_ocaml() {
        assert_eq!(int_of_string("42"), 42);
        assert_eq!(int_of_string("-42"), -42);
        assert_eq!(int_of_string("+1_000"), 1000);
        assert_eq!(int_of_string("0x10"), 16);
        assert_eq!(int_of_string("0o17"), 15);
        assert_eq!(int_of_string("0b101"), 5);
        assert_eq!(int_of_string("0u7"), 7);
        assert_eq!(int_of_string("4611686018427387903"), (1 << 62) - 1);
        assert_eq!(int_of_string("-4611686018427387904"), -(1 << 62));
        assert_eq!(int_of_string("0x7fffffffffffffff"), -1);
        for bad in [
            "",
            "-",
            "0x",
            "12a",
            "4611686018427387904",
            "0x8000000000000000",
            "_1",
        ] {
            let result = std::panic::catch_unwind(|| int_of_string(bad));
            assert!(result.is_err(), "{:?}", bad);
        }
    }

    #[test]
    fn variants() {
        use std::cmp::Ordering::*;
        let cmp = dep::compare_variant;
        assert_eq!(cmp(&Type(s("\\A")), &Type(s("\\B"))), Less);
        assert_eq!(cmp(&Type(s("\\B")), &Type(s("\\A"))), Greater);
        assert_eq!(cmp(&Type(s("\\A")), &Type(s("\\A"))), Equal);
        assert_eq!(
            cmp(&Method(s("\\A"), s("m")), &Method(s("\\A"), s("n"))),
            Less
        );
        assert_eq!(
            cmp(&Method(s("\\B"), s("a")), &Method(s("\\A"), s("z"))),
            Greater
        );
        assert_eq!(cmp(&Declares, &Declares), Equal);
        // By ordinal otherwise: `NotSubtype` is 15, `Const` is 5.
        assert_eq!(cmp(&GConst(s("z")), &Fun(s("a"))), Less);
        assert_eq!(
            cmp(&NotSubtype(s("\\A")), &Const(s("\\A"), s("c"))),
            Greater
        );
        assert_eq!(
            cmp(&Declares, &File(relative_path::RelativePath::EMPTY)),
            Less
        );
        // As in the OCaml, two modules compare equal.
        assert_eq!(cmp(&Module(s("a")), &Module(s("b"))), Equal);

        assert_eq!(dep::extract_name(&Method(s("\\A\\B"), s("m"))), "A\\B::m");
        assert_eq!(dep::extract_name(&Type(s("\\A\\B"))), "A\\B");
        assert_eq!(dep::extract_name(&Module(s("\\m"))), "\\m");
        assert_eq!(dep::extract_name(&Declares), "__declares__");
        assert_eq!(dep::extract_root_name(None, &Prop(s("\\A"), s("p"))), "A");
        assert_eq!(
            dep::extract_root_name(Some(false), &Prop(s("\\A"), s("p"))),
            "\\A"
        );
        assert_eq!(dep::extract_root_name(Some(true), &Module(s("\\m"))), "m");
        assert_eq!(
            dep::extract_member_name(&SProp(s("\\A"), s("p"))),
            Some(s("p"))
        );
        assert_eq!(dep::extract_member_name(&Constructor(s("\\A"))), None);
        assert_eq!(
            dep::variant_to_string(&SMethod(s("\\A"), s("m"))),
            "SMethod A::m"
        );
        assert_eq!(dep::variant_to_string(&Declares), "Declares");
        assert_eq!(
            dep::variant_to_string(&GConstName(s("\\C"))),
            "GConstName C"
        );
        let mut out = String::new();
        dep::pp_variant(&mut out, &Extends(s("\\A"))).unwrap();
        assert_eq!(out, "Extends A");

        use oxidized::decl_reference::DeclReference;
        assert_eq!(
            dep::to_decl_reference(&Method(s("\\A"), s("m"))),
            DeclReference::Type(s("\\A"))
        );
        assert_eq!(
            dep::to_decl_reference(&GConstName(s("\\C"))),
            DeclReference::GlobalConstant(s("\\C"))
        );
        assert_eq!(
            dep::to_decl_reference(&Fun(s("\\f"))),
            DeclReference::Function(s("\\f"))
        );
        assert_eq!(
            dep::to_decl_reference(&Module(s("m"))),
            DeclReference::Module(s("m"))
        );
        assert!(std::panic::catch_unwind(|| dep::to_decl_reference(&Declares)).is_err());

        let v = Const(s("\\A"), s("c"));
        assert_eq!(dep::dependency_of_variant(&v), v);

        assert_eq!(
            dep::member::show(&dep::member::method_("a\"b")),
            "(Typing_deps.Dep.Member.Method \"a\\\"b\")"
        );
        assert_eq!(
            dep::member::show(&dep::member::constructor),
            "Typing_deps.Dep.Member.Constructor"
        );
    }

    #[test]
    fn dep_sets_and_maps() {
        let d = |n: u64| dep::T::from(depgraph_dep::Dep::new(n));
        let set = |xs: &[u64]| dep_set::of_list(&xs.iter().map(|&x| d(x)).collect::<Vec<_>>());
        assert_eq!(
            dep_set::union(&set(&[4, 7]), &set(&[1, 4, 3])),
            set(&[1, 4, 3, 7])
        );
        assert_eq!(
            dep_set::union(&set(&[1, 4, 3]), &set(&[4, 7])),
            set(&[1, 4, 3, 7])
        );
        assert_eq!(dep_set::inter(&set(&[4, 7]), &set(&[1, 4, 3])), set(&[4]));
        assert_eq!(dep_set::inter(&set(&[1, 4, 3]), &set(&[4, 7])), set(&[4]));
        assert_eq!(
            dep_set::diff(&set(&[4, 7]), &set(&[1, 4, 3, 9, 8, 10])),
            set(&[7])
        );
        assert_eq!(
            dep_set::diff(&set(&[1, 4, 3, 9, 8, 10]), &set(&[4, 11])),
            set(&[1, 3, 9, 8, 10])
        );
        let one = dep_set::singleton(d(5));
        let two = dep_set::add(&one, d(6));
        assert_eq!(dep_set::cardinal(&one), 1);
        assert_eq!(dep_set::cardinal(&two), 2);
        assert!(dep_set::mem(&two, d(6)) && !dep_set::mem(&one, d(6)));
        assert!(dep_set::is_empty(&dep_set::make()) && !dep_set::is_empty(&one));
        assert_eq!(dep_set::fold(&two, 0, |x, acc| acc + u(x)), 11);
        let mut seen = vec![];
        dep_set::iter(&two, |x| seen.push(u(x)));
        assert_eq!(seen, vec![5, 6]);
        assert_eq!(
            dep_set::fold_result(&two, 0, |x, acc| if u(x) == 6 {
                Err(acc)
            } else {
                Ok(acc + 1)
            }),
            Err(1)
        );
        assert_eq!(dep_set::show(&dep_set::make()), "{ }");

        // `DepMap.show`, on one line and broken.
        let pp_variant = |fmt: &mut dyn std::fmt::Write, v: &Variant| dep::pp_variant(fmt, v);
        let mut map: dep_map::T<Variant> = dep_map::T::new();
        assert_eq!(dep_map::show(pp_variant, &map), "{}");
        map.insert(d(1), Type(s("\\A")));
        map.insert(d(2), Fun(s("\\f")));
        assert_eq!(
            dep_map::show(pp_variant, &map),
            "{ 0x0000000000000001 -> Type A; 0x0000000000000002 -> Fun f }"
        );
        map.insert(d(3), Method(s("\\A"), s("m")));
        assert_eq!(
            dep_map::show(pp_variant, &map),
            "{ 0x0000000000000001 -> Type A;\n  0x0000000000000002 -> Fun f;\n  0x0000000000000003 -> Method A::m }"
        );
        let long = "x".repeat(70);
        let mut map: dep_map::T<Variant> = dep_map::T::new();
        map.insert(d(1), Type(long.clone()));
        assert_eq!(
            dep_map::show(pp_variant, &map),
            format!("{{ 0x0000000000000001 ->\n  Type {} }}", long)
        );
    }

    #[test]
    fn deps_of_file_info_order() {
        use oxidized::file_info;
        let id = |name: &str| file_info::Id {
            pos: file_info::Pos::File(
                file_info::NameType::Fun,
                Arc::new(relative_path::RelativePath::EMPTY),
            ),
            name: s(name),
            decl_hash: None,
        };
        let info = FileInfo {
            position_free_decl_hash: file_info::HashType(None),
            file_mode: None,
            ids: file_info::Ids {
                funs: vec![id("\\f"), id("\\g")],
                classes: vec![id("\\C")],
                typedefs: vec![id("\\T")],
                consts: vec![id("\\K")],
                modules: vec![id("m")],
            },
            comments: None,
        };
        assert_eq!(
            deps_of_file_info(&info),
            vec![
                dep::make(&Module(s("m"))),
                dep::make(&Type(s("\\T"))),
                dep::make(&Type(s("\\C"))),
                dep::make(&Fun(s("\\g"))),
                dep::make(&Fun(s("\\f"))),
                dep::make(&GConst(s("\\K"))),
            ]
        );
    }

    #[test]
    fn modes_and_errors() {
        assert_eq!(
            crate::yojson::safe::to_string(&mode::to_opaque_json(&InMemoryMode(Some(s("/x"))))),
            r#"{"mode":"InMemoryMode","props":{"base":"<opaque>"}}"#
        );
        assert_eq!(
            crate::yojson::safe::to_string(&mode::to_opaque_json(&SaveToDiskMode {
                graph: None,
                new_edges_dir: s("/e"),
                human_readable_dep_map_dir: Some(s("/h")),
            })),
            r#"{"mode":"SaveToDiskMode","props":{"graph":null,"human_readable_dep_map_dir":"<opaque>"}}"#
        );
        let missing = s("/nonexistent/hh_typing_deps_test.hhdg");
        let error =
            match DepGraphWithDelta::base_dep_graph_from_mode(&InMemoryMode(Some(missing.clone())))
            {
                Err(error) => error,
                Ok(_) => panic!("loading a missing dependency graph should fail"),
            };
        assert_eq!(error, DepgraphLoadError::DepgraphNotFound(missing.clone()));
        assert_eq!(
            DepgraphUnavailable(error).to_string(),
            format!(
                "Typing_deps.Depgraph_unavailable(dependency graph not found: {})",
                missing
            )
        );
        assert_eq!(
            depgraph_load_error_to_string(&DepgraphLoadError::DepgraphNotLoaded),
            "dependency graph was not loaded"
        );
        assert!(matches!(
            DepGraphWithDelta::base_dep_graph_from_mode(&SaveToDiskMode {
                graph: None,
                new_edges_dir: s("/e"),
                human_readable_dep_map_dir: None,
            }),
            Ok(None)
        ));
    }

    // The tests of `deps_rust/dep_graph_with_delta.rs`.

    struct SimpleDepGraph {
        graph: HashMap<depgraph_dep::Dep, std::collections::HashSet<depgraph_dep::Dep>>,
    }

    impl<const N: usize> From<[(depgraph_dep::Dep, Vec<depgraph_dep::Dep>); N]> for SimpleDepGraph {
        fn from(arr: [(depgraph_dep::Dep, Vec<depgraph_dep::Dep>); N]) -> Self {
            Self {
                graph: arr
                    .into_iter()
                    .map(|(k, v)| (k, v.into_iter().collect()))
                    .collect(),
            }
        }
    }

    impl BaseDepgraphTrait for SimpleDepGraph {
        fn iter_dependents(
            &self,
            dep: depgraph_dep::Dep,
        ) -> Box<dyn Iterator<Item = depgraph_dep::Dep> + '_> {
            match self.graph.get(&dep) {
                None => Box::new(std::iter::empty()),
                Some(set) => Box::new(set.iter().copied()),
            }
        }

        fn dependent_dependency_edge_exists(
            &self,
            dependent: depgraph_dep::Dep,
            dependency: depgraph_dep::Dep,
        ) -> bool {
            self.graph
                .get(&dependency)
                .is_some_and(|set| set.contains(&dependent))
        }
    }

    fn dependents<B: BaseDepgraphTrait>(dg: &DepGraphWithDelta<B>, dep: u64) -> Vec<u64> {
        let mut v: Vec<u64> = dg
            .iter_dependents_with_duplicates(depgraph_dep::Dep::new(dep), |iter| {
                iter.map(u64::from).collect()
            });
        v.sort();
        v.dedup();
        v
    }

    fn sorted(set: &dep_set::T) -> Vec<u64> {
        let mut v: Vec<u64> = set.iter().map(|d| u(*d)).collect();
        v.sort();
        v
    }

    #[test]
    fn graph_with_base_and_delta() {
        let d = depgraph_dep::Dep::new;
        let base = SimpleDepGraph::from([(d(0), vec![d(1), d(2)]), (d(3), vec![d(2)])]);
        let mut delta = DepGraphDelta::default();
        delta.insert(d(4), d(3));
        delta.insert(d(3), d(0));
        delta.insert(d(4), d(0));
        delta.remove(d(2), d(0));
        delta.remove(d(4), d(0));
        let dg = DepGraphWithDelta::new(Some(base), delta);

        assert_eq!(dependents(&dg, 0), vec![1, 3]);
        assert_eq!(dependents(&dg, 3), vec![2, 4]);
        assert!(dg.has_edge(d(1), d(0)));
        assert!(!dg.has_edge(d(2), d(0)));
        assert!(dg.has_edge(d(2), d(3)));
        assert!(dg.has_edge(d(4), d(3)));
        assert!(dg.has_edge(d(3), d(0)));
        assert!(!dg.has_edge(d(4), d(0)));
        assert!(!dg.has_edge(d(10), d(11)));

        let mut delta = DepGraphDelta::default();
        delta.insert(d(4), d(3));
        delta.insert(d(3), d(0));
        delta.remove(d(2), d(0));
        let dg = DepGraphWithDelta::<SimpleDepGraph>::new(None, delta);
        assert_eq!(dependents(&dg, 0), vec![3]);
        assert_eq!(dependents(&dg, 3), vec![4]);
        assert!(dg.has_edge(d(4), d(3)));
        assert!(dg.has_edge(d(3), d(0)));
        assert!(!dg.has_edge(d(2), d(0)));
        assert!(!dg.has_edge(d(2), d(3)));
    }

    fn class_dep(n: u64) -> depgraph_dep::Dep {
        depgraph_dep::Dep::new((n << 1) + 1)
    }

    fn extends(c: depgraph_dep::Dep) -> depgraph_dep::Dep {
        c.class_to_extends().unwrap()
    }

    #[test]
    fn graph_extend_deps() {
        let c: Vec<depgraph_dep::Dep> = (0..18).map(class_dep).collect();
        let dg = DepGraphWithDelta::new(
            Some(SimpleDepGraph::from([
                // 'Extends' edges
                (extends(c[0]), vec![c[1], c[2]]),
                (extends(c[1]), vec![c[3]]),
                (extends(c[2]), vec![c[4], c[5]]),
                (extends(c[5]), vec![c[6], c[7]]),
                (extends(c[8]), vec![c[9], c[5]]),
                (extends(c[15]), vec![c[16], c[17]]),
                (extends(c[17]), vec![c[2], c[8]]),
                // Regular edges
                (c[0], vec![c[10]]),
                (c[2], vec![c[11], c[12]]),
                (c[8], vec![c[13]]),
                (c[9], vec![c[14]]),
            ])),
            DepGraphDelta::default(),
        );
        let ids = |cs: &[usize]| {
            let mut v: Vec<u64> = cs.iter().map(|&i| u64::from(c[i])).collect();
            v.sort();
            v
        };

        let mut visited = HashSet::default();
        let mut acc = dep_set::make();
        dg.get_extend_deps(&mut visited, c[0], &mut acc);
        assert_eq!(sorted(&acc), ids(&[1, 2, 3, 4, 5, 6, 7]));
        let mut visited: Vec<u64> = visited.into_iter().map(u64::from).collect();
        visited.sort();
        assert_eq!(visited, ids(&[0, 1, 2, 3, 4, 5, 6, 7]));

        let mut acc = dep_set::of_list(&[c[0].into(), c[8].into()]);
        dg.add_extend_deps(&mut acc);
        assert_eq!(sorted(&acc), ids(&[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]));
    }

    #[test]
    fn graph_member_fanout() {
        let c: Vec<depgraph_dep::Dep> = (0..10).map(class_dep).collect();
        let m = |i: usize| c[i].member(DepType::KMethod, "m");
        let d = |n: u64| depgraph_dep::Dep::new(100 + n);
        let declares = depgraph_dep::Dep::declares();
        let dg = DepGraphWithDelta::new(
            Some(SimpleDepGraph::from([
                // 'Extends' edges
                (extends(c[0]), vec![c[1]]),
                (extends(c[1]), vec![c[2], c[5], c[9]]),
                (extends(c[2]), vec![c[3], c[6], c[8]]),
                (extends(c[3]), vec![c[4]]),
                (extends(c[6]), vec![c[7]]),
                // makes the graph a DAG instead of just a tree
                (extends(c[8]), vec![c[5]]),
                // Let's introduce a cycle
                (extends(c[9]), vec![c[1]]),
                // member deps
                (m(0), vec![d(0)]),
                (m(1), vec![declares, d(1)]),
                (m(2), vec![d(2)]),
                (m(3), vec![d(3), declares, d(8)]),
                (m(4), vec![d(4), d(10)]),
                (m(5), vec![d(5), declares]),
                (m(6), vec![d(6), d(11)]),
                (m(7), vec![d(7), declares, d(9)]),
                // I::m and J::m does not appear in the graph
                // Other class deps
                (c[0], vec![d(12)]),
                (c[1], vec![d(13)]),
                (c[2], vec![d(14)]),
                (c[3], vec![d(15)]),
                (c[4], vec![d(16)]),
                (c[5], vec![d(17)]),
                (c[6], vec![d(18)]),
                (c[7], vec![d(19)]),
                (c[8], vec![d(20)]),
            ])),
            DepGraphDelta::default(),
        );
        let mut fanout = dep_set::make();
        dg.get_member_fanout(c[1], DepType::KMethod, "m", &mut fanout);
        let mut expected: Vec<u64> = [
            c[1],
            c[2],
            c[3],
            c[5],
            c[6],
            c[7],
            c[8],
            c[9],
            d(1),
            d(2),
            d(6),
            d(11),
        ]
        .into_iter()
        .map(u64::from)
        .collect();
        expected.sort();
        assert_eq!(sorted(&fanout), expected);

        let not_subtype = c[2].class_to_not_subtype();
        let dg = DepGraphWithDelta::new(
            Some(SimpleDepGraph::from([(not_subtype, vec![d(1), d(2)])])),
            DepGraphDelta::default(),
        );
        let mut fanout = dep_set::make();
        dg.get_not_subtype_fanout(&dep_set::of_list(&[c[2].into(), c[3].into()]), &mut fanout);
        assert_eq!(sorted(&fanout), vec![101, 102]);
    }

    /// Recording is off unless asked for, and then costs nothing.
    #[test]
    fn nothing_is_recorded_when_not_tracing() {
        let _lock = global_state();
        assert!(!trace.load(Ordering::SeqCst));
        let mode = InMemoryMode(None);
        std::thread::spawn(move || {
            for i in 0..3000 {
                add_idep(
                    &mode,
                    &Fun(format!("\\test_not_tracing_f{}", i)),
                    &Type(s("\\TestNotTracing")),
                );
            }
            assert_eq!(flush_ideps_batch(&mode), Some(BTreeSet::new()));
        })
        .join()
        .unwrap();
        assert!(dep_set::is_empty(&get_ideps(
            &InMemoryMode(None),
            &Type(s("\\TestNotTracing"))
        )));
    }

    #[test]
    fn edges_are_recorded_from_several_threads() {
        let _lock = global_state();
        let _tracing = Tracing::on();
        let mode = InMemoryMode(None);
        const THREADS: usize = 8;
        const EDGES: usize = 2500;
        const SHARED: usize = 100;

        let callback_calls = Arc::new(AtomicUsize::new(0));
        {
            let callback_calls = Arc::clone(&callback_calls);
            add_dependency_callback(
                "edges_are_recorded_from_several_threads",
                move |dependent, _| {
                    if dep::extract_name(dependent).starts_with("test_threads_") {
                        callback_calls.fetch_add(1, Ordering::Relaxed);
                    }
                },
            );
        }

        let record = |t: usize, edges: usize| {
            let mode = InMemoryMode(None);
            for i in 0..edges {
                add_idep(
                    &mode,
                    &Fun(format!("\\test_threads_f_{}_{}", t, i)),
                    &Method(s("\\TestThreadsC"), format!("m{}", i % 50)),
                );
            }
            for j in 0..SHARED {
                add_idep(
                    &mode,
                    &Fun(format!("\\test_threads_shared_{}", j)),
                    &Type(s("\\TestThreadsShared")),
                );
            }
            // Not an edge: both ends are the same node.
            add_idep(
                &mode,
                &Type(s("\\TestThreadsShared")),
                &Type(s("\\TestThreadsShared")),
            );
        };

        // Every thread hands over its own edges, as an OCaml worker does.
        let handles: Vec<_> = (0..THREADS)
            .map(|t| {
                std::thread::spawn(move || {
                    record(t, EDGES);
                    let edges = flush_ideps_batch(&InMemoryMode(None));
                    // Nothing is left behind.
                    assert_eq!(
                        flush_ideps_batch(&InMemoryMode(None)),
                        Some(BTreeSet::new())
                    );
                    edges
                })
            })
            .collect();
        let mut all = dep_edges_make();
        for handle in handles {
            let edges = handle.join().unwrap();
            assert_eq!(edges.as_ref().unwrap().len(), EDGES + SHARED);
            all = merge_dep_edges(all, edges);
        }
        assert_eq!(all.as_ref().unwrap().len(), THREADS * EDGES + SHARED);
        assert_eq!(
            callback_calls.load(Ordering::Relaxed),
            THREADS * (EDGES + SHARED)
        );
        assert_eq!(merge_dep_edges(all.clone(), None), None);

        // The main thread recorded nothing.
        assert_eq!(flush_ideps_batch(&mode), Some(BTreeSet::new()));

        let before = telemetry::depgraph_delta_num_edges(&mode).unwrap();
        register_discovered_dep_edges(&all);
        let after = telemetry::depgraph_delta_num_edges(&mode).unwrap();
        assert_eq!((after - before) as usize, THREADS * EDGES + SHARED);
        assert_eq!(
            telemetry::depgraph_delta_num_edges(&SaveToDiskMode {
                graph: None,
                new_edges_dir: s("/e"),
                human_readable_dep_map_dir: None,
            }),
            None
        );

        let shared = get_ideps(&mode, &Type(s("\\TestThreadsShared")));
        assert_eq!(dep_set::cardinal(&shared) as usize, SHARED);
        assert!(dep_set::mem(
            &shared,
            dep::make(&Fun(s("\\test_threads_shared_7")))
        ));
        let m0 = get_ideps(&mode, &Method(s("\\TestThreadsC"), s("m0")));
        assert_eq!(dep_set::cardinal(&m0) as usize, THREADS * EDGES / 50);
        assert_eq!(
            get_ideps_from_hash(&mode, dep::make(&Method(s("\\TestThreadsC"), s("m0")))),
            m0
        );

        // Edges that are in the graph already are filtered out.
        let again = std::thread::spawn(move || {
            record(0, 1500);
            add_idep(
                &InMemoryMode(None),
                &Fun(s("\\test_threads_new")),
                &Type(s("\\TestThreadsShared")),
            );
            flush_ideps_batch(&InMemoryMode(None))
        })
        .join()
        .unwrap();
        assert_eq!(
            again,
            Some(BTreeSet::from([DepEdge {
                idependent: dep::make(&Fun(s("\\test_threads_new"))),
                idependency: dep::make(&Type(s("\\TestThreadsShared"))),
            }]))
        );

        // `flush_deps` stores what the calling thread recorded.
        add_idep(
            &mode,
            &Fun(s("\\test_threads_flush_deps")),
            &Type(s("\\TestThreadsShared")),
        );
        flush_deps(&mode);
        assert_eq!(
            dep_set::cardinal(&get_ideps(&mode, &Type(s("\\TestThreadsShared")))) as usize,
            SHARED + 1
        );

        // The delta is saved in the format of `DepGraphDelta`.
        let dir = temp_dir("save_discovered_edges");
        let dest = dir.join("edges.bin");
        let saved = save_discovered_edges(&mode, dest.to_str().unwrap(), false);
        assert_eq!(saved, telemetry::depgraph_delta_num_edges(&mode).unwrap());
        let mut read_back = DepGraphDelta::default();
        let read = read_back
            .read_added_edges_from(std::fs::File::open(&dest).unwrap(), |_, _| true)
            .unwrap();
        assert_eq!(read as isize, saved);
        assert!(
            read_back
                .get(dep::make(&Type(s("\\TestThreadsShared"))).into())
                .added
                .unwrap()
                .contains(&dep::make(&Fun(s("\\test_threads_shared_3"))).into())
        );
        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn queries_over_the_delta() {
        let _lock = global_state();
        let mode = InMemoryMode(None);
        let ty = |name: &str| Type(format!("\\TestQueries{}", name));
        let d = |v: &Variant| dep::make(v);
        let edge = |dependent: &Variant, dependency: &Variant| DepEdge {
            idependent: d(dependent),
            idependency: d(dependency),
        };
        let ext = |name: &str| Extends(format!("\\TestQueries{}", name));
        let method = |name: &str| Method(format!("\\TestQueries{}", name), s("m"));
        let f = |name: &str| Fun(format!("\\test_queries_{}", name));
        // B and C extend A, D extends B; f uses A, g uses B::m, h uses D::m;
        // B and D declare m.
        let edges: DepEdges = Some(BTreeSet::from([
            edge(&ty("B"), &ext("A")),
            edge(&ty("C"), &ext("A")),
            edge(&ty("D"), &ext("B")),
            edge(&f("f"), &ty("A")),
            edge(&f("g"), &method("B")),
            edge(&f("h"), &method("D")),
            edge(&f("i"), &method("A")),
            edge(&f("j"), &method("C")),
            edge(&Declares, &method("B")),
            edge(&Declares, &method("D")),
            edge(&f("k"), &NotSubtype(s("\\TestQueriesC"))),
        ]));
        register_discovered_dep_edges(&edges);

        let set = |vs: &[&Variant]| dep_set::of_list(&vs.iter().map(|v| d(v)).collect::<Vec<_>>());
        assert_eq!(get_ideps(&mode, &ty("A")), set(&[&f("f")]));
        assert_eq!(get_ideps(&mode, &ext("A")), set(&[&ty("B"), &ty("C")]));

        let a = set(&[&ty("A")]);
        assert_eq!(
            add_extend_deps(&mode, &a),
            set(&[&ty("A"), &ty("B"), &ty("C"), &ty("D")])
        );
        assert_eq!(add_typing_deps(&mode, &a), set(&[&ty("A"), &f("f")]));
        assert_eq!(
            add_all_deps(&mode, &a),
            set(&[&ty("A"), &ty("B"), &ty("C"), &ty("D"), &f("f")])
        );
        let mut visited = visited_set::make();
        let acc = get_extend_deps(&mode, &mut visited, d(&ty("A")), &dep_set::make());
        assert_eq!(acc, set(&[&ty("B"), &ty("C"), &ty("D")]));
        // Visited nodes are not visited again.
        assert_eq!(
            get_extend_deps(&mode, &mut visited, d(&ty("A")), &dep_set::make()),
            dep_set::make()
        );

        // The fanout of A::m: A, and its descendants down to those that
        // declare m (B does, so D is not reached), with the dependents of
        // their m that is not declared.
        assert_eq!(
            get_member_fanout(
                &mode,
                d(&ty("A")),
                &dep::member::method_("m"),
                &dep_set::make()
            ),
            set(&[&ty("A"), &ty("B"), &ty("C"), &f("i"), &f("j")])
        );
        assert_eq!(
            get_not_subtype_fanout(&mode, &set(&[&ty("C"), &ty("D")]), &dep_set::make()),
            set(&[&f("k")])
        );

        // Without the edge that says B declares m, the fanout goes on to D.
        remove_declared_tags(&mode, &set(&[&method("B")]));
        assert_eq!(
            get_member_fanout(
                &mode,
                d(&ty("A")),
                &dep::member::method_("m"),
                &dep_set::make()
            ),
            set(&[
                &ty("A"),
                &ty("B"),
                &ty("C"),
                &ty("D"),
                &f("g"),
                &f("i"),
                &f("j")
            ])
        );

        assert!(!allow_dependency_table_reads(&mode, true));
        assert!(allow_dependency_table_reads(&mode, false));
    }

    /// A dependency graph file with the edges `dependency -> dependents`,
    /// in the format that `depgraph_reader` reads.
    fn write_depgraph(path: &std::path::Path, dependency: dep::T, dependents: &[dep::T]) {
        use depgraph_reader::compress::UncompressedHeader;
        // Physical order: the dependency, then its dependents.
        let mut deps: Vec<u64> = vec![u(dependency)];
        deps.extend(dependents.iter().map(|d| u(*d)));
        let n = deps.len();
        let mut order: Vec<u32> = (0..n as u32).collect();
        order.sort_by_key(|&i| deps[i as usize]);
        let mut bytes = vec![];
        bytes.extend_from_slice(&UncompressedHeader::MAGIC);
        bytes.extend_from_slice(&UncompressedHeader::LATEST_VERSION.to_ne_bytes());
        bytes.extend_from_slice(&(n as u64).to_ne_bytes());
        bytes.push(0);
        bytes.extend_from_slice(&[0; 7]);
        for dep in &deps {
            bytes.extend_from_slice(&dep.to_ne_bytes());
        }
        for i in &order {
            bytes.extend_from_slice(&i.to_ne_bytes());
        }
        // The empty list is at offset 0, the list of the dependency at 2.
        bytes.extend_from_slice(&2u32.to_ne_bytes());
        for _ in dependents {
            bytes.extend_from_slice(&0u32.to_ne_bytes());
        }
        // A list: the number of blocks and of indices (one-byte `vint64`s),
        // then the blocks (the first index and the length of a run).
        let vint = |v: usize| ((v << 1) | 1) as u8;
        bytes.extend_from_slice(&[vint(0), vint(0)]);
        bytes.extend_from_slice(&[vint(1), vint(dependents.len())]);
        bytes.extend_from_slice(&1u32.to_ne_bytes());
        bytes.push(dependents.len() as u8);
        std::fs::write(path, bytes).unwrap();
    }

    #[test]
    fn queries_over_a_saved_dependency_graph() {
        let _lock = global_state();
        let dir = temp_dir("saved_graph");
        let path = dir.join("graph.hhdg");
        let dependency = Type(s("\\TestSavedGraphC"));
        let dependents = [
            Fun(s("\\test_saved_graph_f")),
            Fun(s("\\test_saved_graph_g")),
        ];
        write_depgraph(
            &path,
            dep::make(&dependency),
            &[dep::make(&dependents[0]), dep::make(&dependents[1])],
        );
        let mode = InMemoryMode(Some(path.to_str().unwrap().to_string()));
        replace(&mode);

        assert_eq!(
            get_ideps(&mode, &dependency),
            dep_set::of_list(&[dep::make(&dependents[0]), dep::make(&dependents[1])])
        );
        assert!(dep_set::is_empty(&get_ideps(&mode, &dependents[0])));

        // An edge of the saved graph is not a new edge; another one is.
        let _tracing = Tracing::on();
        let new = Fun(s("\\test_saved_graph_h"));
        add_idep(&mode, &dependents[0], &dependency);
        add_idep(&mode, &new, &dependency);
        let edges = flush_ideps_batch(&mode);
        assert_eq!(
            edges,
            Some(BTreeSet::from([DepEdge {
                idependent: dep::make(&new),
                idependency: dep::make(&dependency),
            }]))
        );
        register_discovered_dep_edges(&edges);
        assert_eq!(dep_set::cardinal(&get_ideps(&mode, &dependency)), 3);

        // Back to no saved graph: only the delta is left.
        replace(&InMemoryMode(None));
        assert_eq!(
            get_ideps(&InMemoryMode(None), &dependency),
            dep_set::singleton(dep::make(&new))
        );

        // A graph that cannot be loaded is an exception.
        let missing = InMemoryMode(Some(dir.join("missing.hhdg").to_str().unwrap().to_string()));
        let payload = std::panic::catch_unwind(|| replace(&missing)).unwrap_err();
        match payload.downcast_ref::<DepgraphUnavailable>() {
            Some(DepgraphUnavailable(DepgraphLoadError::DepgraphNotFound(_))) => {}
            _ => panic!("expected Depgraph_unavailable"),
        }
        // (The base of before stays.)
        assert_eq!(
            get_ideps(&InMemoryMode(None), &dependency),
            dep_set::singleton(dep::make(&new))
        );
        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn edges_are_saved_to_disk() {
        let _lock = global_state();
        let _tracing = Tracing::on();
        let dir = temp_dir("save_to_disk");
        let human = dir.join("human");
        let mode = SaveToDiskMode {
            graph: None,
            new_edges_dir: dir.to_str().unwrap().to_string(),
            human_readable_dep_map_dir: Some(human.to_str().unwrap().to_string()),
        };
        let dependency = Type(s("\\TestSaveToDiskC"));
        let handles: Vec<_> = (0..2)
            .map(|t: isize| {
                let mode = mode.clone();
                let dependency = dependency.clone();
                std::thread::spawn(move || {
                    worker_id.set(Some(t));
                    for i in 0..1200 {
                        add_idep(
                            &mode,
                            &Fun(format!("\\test_save_to_disk_f_{}_{}", t, i)),
                            &dependency,
                        );
                    }
                    assert_eq!(flush_ideps_batch(&mode), None);
                })
            })
            .collect();
        for handle in handles {
            handle.join().unwrap();
        }

        for t in 0..2 {
            let file = dir.join(format!("new-edges-worker-{}.bin", t));
            let bytes = std::fs::read(&file).unwrap();
            // A dependency (tagged with the top bit) and a dependent per edge.
            assert_eq!(bytes.len(), 1200 * 16);
            let tagged = (u(dep::make(&dependency)) | 1 << 63).to_le_bytes();
            assert_eq!(&bytes[0..8], &tagged[..]);
            let mut delta = DepGraphDelta::default();
            let read = delta
                .read_added_edges_from(&bytes[..], |_, _| true)
                .unwrap();
            assert_eq!(read, 1200);
            let added = delta.get(dep::make(&dependency).into()).added.unwrap();
            assert_eq!(added.len(), 1200);
            for i in [0, 7, 1199] {
                let dependent = Fun(format!("\\test_save_to_disk_f_{}_{}", t, i));
                assert!(added.contains(&dep::make(&dependent).into()));
            }

            let text =
                std::fs::read_to_string(human.join(format!("human-readable-dep-map-{}.txt", t)))
                    .unwrap();
            let lines: Vec<&str> = text.lines().collect();
            assert_eq!(lines.len(), 1201);
            assert!(
                lines.contains(
                    &format!("{} Type TestSaveToDiskC", u(dep::make(&dependency))).as_str()
                )
            );
            let dependent = Fun(format!("\\test_save_to_disk_f_{}_3", t));
            assert!(
                lines.contains(
                    &format!(
                        "{} Fun test_save_to_disk_f_{}_3",
                        u(dep::make(&dependent)),
                        t
                    )
                    .as_str()
                )
            );
        }
        let result = std::panic::catch_unwind(|| save_discovered_edges(&mode, "/dev/null", false));
        assert!(result.is_err());
        std::fs::remove_dir_all(&dir).unwrap();
    }
}
