// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! No OCaml counterpart: persistent ordered maps and sets shaped like OCaml's
//! `Map` and `Set`: a balanced binary tree (the heights of the children differ
//! by at most 2, as in `map.ml`) of reference-counted nodes. No OCaml module corresponds to
//! this one; it is the representation of the OCaml maps whose copies must
//! cost nothing (the locals, the continuations, the type variables of the
//! typing environment).
//!
//! Why not `im::OrdMap`: its B-tree nodes hold up to 64 entries, so an update
//! of a shared map copies whole nodes, that is clones up to 64 keys and
//! values per level (the whole map, for the small maps of the typing
//! environment), and its `Arc`s pay atomic operations. Here, as in OCaml, an
//! update allocates the O(log n) nodes on the path to the key, and every
//! entry is shared between the versions: a node holds its entry `(key,
//! value)` behind an `Rc`, so path copying never clones a key or a value.
//! An update of a map that shares nothing (the reference counts are 1)
//! changes the nodes in place.
//!
//! The methods are the subset of the `im::OrdMap` / `im::OrdSet` API that the
//! callers use, with the same meaning, so that a map can change from one to
//! the other by changing its type. The order of iteration is the order of the
//! keys. The type is not `Send`: use it only for what lives inside the
//! typing of one file.
//!
//! The methods and their OCaml `Map.S` / `Set.S` names:
//!
//! ```text
//! Map / Set method             OCaml
//! new, default                 empty
//! is_empty                     is_empty
//! len                          cardinal
//! get                          find_opt
//! get_key_value                find_opt, with the key of the binding
//! get_entry                    find_opt, giving the shared binding
//! contains_key, contains       mem
//! insert, insert_entry         add (on the map in place)
//! insert_replacing             add, giving back the value it replaces
//! update                       add (a new map)
//! remove, remove_key           remove (on the map in place)
//! without                      remove (a new map)
//! get_mut, get_or_insert_with  update (on the map in place)
//! unit                         singleton
//! iter, for_each               bindings / elements, iter
//! keys, values, entries        bindings (increasing order of the keys)
//! into_entries                 bindings
//! get_min, get_max             min_binding_opt, max_binding_opt
//!                              (Set: min_elt_opt, max_elt_opt)
//! union                        union (fun _ v1 _ -> Some v1)
//! is_subset                    subset
//! ptr_eq                       == (physical equality)
//! FromIterator                 of_list (the last binding of a key wins)
//! ```
//!
//! (Unlike `Wrapped_map.keys`/`values`/`elements`, which are in decreasing
//! order: see `crate::wrapped_map`.)

use std::borrow::Borrow;
use std::cmp::Ordering;
use std::fmt;
use std::hash::Hash;
use std::hash::Hasher;
use std::rc::Rc;

/// The keys of the maps. `prefix` summarises a key in a word that orders
/// like it (`a < b` implies `prefix a <= prefix b`): the nodes keep the
/// prefix of their key, so that a search compares words and reaches the
/// entry (another allocation) only when the prefixes are equal, and not even
/// then if they are `EXACT` (equal prefixes mean equal keys). A type and the
/// types it borrows as (`String` and `str`) must have the same prefixes.
pub trait Key: Ord {
    fn prefix(&self) -> u64;
    const EXACT: bool = false;
}

macro_rules! signed_key {
    ($($t:ty),*) => {$(
        impl Key for $t {
            #[inline]
            fn prefix(&self) -> u64 {
                (*self as i64 as u64) ^ (1 << 63)
            }
            const EXACT: bool = true;
        }
    )*};
}
signed_key!(isize, i64, i32);

/// The first `N` bytes, big-endian, padded with zeros: byte strings order
/// lexicographically.
#[inline]
fn bytes_prefix<const N: usize>(s: &[u8]) -> u64 {
    let mut buf = [0u8; 8];
    let n = s.len().min(N);
    buf[8 - N..8 - N + n].copy_from_slice(&s[..n]);
    u64::from_be_bytes(buf)
}

impl Key for str {
    #[inline]
    fn prefix(&self) -> u64 {
        bytes_prefix::<8>(self.as_bytes())
    }
}

impl Key for String {
    #[inline]
    fn prefix(&self) -> u64 {
        self.as_str().prefix()
    }
}

/// `Local_id.t`: the number in the high half, the first bytes of the name in
/// the low half. A number out of `0..u32::MAX` is clamped and gets no bytes
/// of the name (two of them then have equal prefixes), so that the prefix
/// stays monotone.
impl Key for (isize, String) {
    #[inline]
    fn prefix(&self) -> u64 {
        let (i, name) = self;
        if *i < 0 {
            0
        } else if *i >= u32::MAX as isize {
            (u32::MAX as u64) << 32
        } else {
            ((*i as u64) << 32) | bytes_prefix::<4>(name.as_bytes())
        }
    }
}

struct Node<K, V> {
    l: Tree<K, V>,
    r: Tree<K, V>,
    h: u32,
    /// `kv.0.prefix()`
    p: u64,
    kv: Rc<(K, V)>,
}

impl<K, V> Clone for Node<K, V> {
    fn clone(&self) -> Self {
        Node {
            l: self.l.clone(),
            r: self.r.clone(),
            h: self.h,
            p: self.p,
            kv: self.kv.clone(),
        }
    }
}

type Tree<K, V> = Option<Rc<Node<K, V>>>;

/// A binding `(key, value)`, which the versions of a map share.
pub type Entry<K, V> = Rc<(K, V)>;

#[inline]
fn height<K, V>(t: &Tree<K, V>) -> u32 {
    match t {
        None => 0,
        Some(n) => n.h,
    }
}

#[inline]
fn fix_height<K, V>(n: &mut Node<K, V>) {
    let hl = height(&n.l);
    let hr = height(&n.r);
    n.h = if hl >= hr { hl + 1 } else { hr + 1 };
}

fn leaf<K, V>(kv: Rc<(K, V)>, p: u64) -> Rc<Node<K, V>> {
    Rc::new(Node {
        l: None,
        r: None,
        h: 1,
        p,
        kv,
    })
}

/// `key` (of prefix `p`) compared with the key of `n`.
#[inline(always)]
fn cmp_node<K, V, Q>(key: &Q, p: u64, n: &Node<K, V>) -> Ordering
where
    K: Borrow<Q>,
    Q: Key + ?Sized,
{
    match p.cmp(&n.p) {
        Ordering::Equal if !Q::EXACT => key.cmp(n.kv.0.borrow()),
        o => o,
    }
}

/// `Node (Node (ll, lv, lr), v, r)` becomes `Node (ll, lv, Node (lr, v, r))`.
fn rotate_right<K, V>(t: &mut Tree<K, V>) {
    let mut root = t.take().expect("pmap: rotate_right of an empty tree");
    let n = Rc::make_mut(&mut root);
    let mut l = n.l.take().expect("pmap: rotate_right without a left child");
    let ln = Rc::make_mut(&mut l);
    n.l = ln.r.take();
    fix_height(n);
    ln.r = Some(root);
    fix_height(ln);
    *t = Some(l);
}

/// `Node (l, v, Node (rl, rv, rr))` becomes `Node (Node (l, v, rl), rv, rr)`.
fn rotate_left<K, V>(t: &mut Tree<K, V>) {
    let mut root = t.take().expect("pmap: rotate_left of an empty tree");
    let n = Rc::make_mut(&mut root);
    let mut r = n.r.take().expect("pmap: rotate_left without a right child");
    let rn = Rc::make_mut(&mut r);
    n.r = rn.l.take();
    fix_height(n);
    rn.l = Some(root);
    fix_height(rn);
    *t = Some(r);
}

/// `bal` of `map.ml`, in place: the children of `t` are balanced and their
/// heights differ by at most 3; one step of rebalancing (a single or double
/// rotation) restores the invariant. The root of `t` must not be shared.
fn bal<K, V>(t: &mut Tree<K, V>) {
    let n = Rc::get_mut(t.as_mut().expect("pmap: bal of an empty tree"))
        .expect("pmap: bal of a shared node");
    let hl = height(&n.l);
    let hr = height(&n.r);
    if hl > hr + 2 {
        let l = n.l.as_ref().unwrap();
        if height(&l.l) < height(&l.r) {
            rotate_left(&mut n.l);
        }
        rotate_right(t);
    } else if hr > hl + 2 {
        let r = n.r.as_ref().unwrap();
        if height(&r.r) < height(&r.l) {
            rotate_right(&mut n.r);
        }
        rotate_left(t);
    } else {
        n.h = if hl >= hr { hl + 1 } else { hr + 1 };
    }
}

fn find<'a, K, V, Q>(mut t: &'a Tree<K, V>, key: &Q) -> Option<&'a Rc<(K, V)>>
where
    K: Borrow<Q>,
    Q: Key + ?Sized,
{
    let p = key.prefix();
    while let Some(n) = t {
        match cmp_node(key, p, n) {
            Ordering::Equal => return Some(&n.kv),
            Ordering::Less => t = &n.l,
            Ordering::Greater => t = &n.r,
        }
    }
    None
}

/// Adds or replaces the entry of `kv.0`; returns the entry it replaces.
fn insert<K: Key, V>(t: &mut Tree<K, V>, kv: Rc<(K, V)>, p: u64) -> Option<Rc<(K, V)>> {
    match t {
        None => {
            *t = Some(leaf(kv, p));
            None
        }
        Some(rc) => {
            let n = Rc::make_mut(rc);
            let old = match cmp_node(&kv.0, p, n) {
                Ordering::Equal => return Some(std::mem::replace(&mut n.kv, kv)),
                Ordering::Less => insert(&mut n.l, kv, p),
                Ordering::Greater => insert(&mut n.r, kv, p),
            };
            if old.is_none() {
                bal(t);
            }
            old
        }
    }
}

/// Removes the smallest entry of a non-empty tree and returns it, with its
/// prefix.
fn remove_min<K, V>(t: &mut Tree<K, V>) -> (Rc<(K, V)>, u64) {
    let n = Rc::make_mut(t.as_mut().expect("pmap: remove_min of an empty tree"));
    if n.l.is_none() {
        let r = n.r.take();
        let p = n.p;
        let node = t.take().unwrap();
        *t = r;
        (unwrap_node(node), p)
    } else {
        let kv = remove_min(&mut n.l);
        bal(t);
        kv
    }
}

/// Removes the entry of `key`, which the tree must have, and returns it.
fn remove_present<K, V, Q>(t: &mut Tree<K, V>, key: &Q, p: u64) -> Rc<(K, V)>
where
    K: Borrow<Q>,
    Q: Key + ?Sized,
{
    let n = Rc::make_mut(t.as_mut().expect("pmap: the key to remove is missing"));
    match cmp_node(key, p, n) {
        Ordering::Less => {
            let kv = remove_present(&mut n.l, key, p);
            bal(t);
            kv
        }
        Ordering::Greater => {
            let kv = remove_present(&mut n.r, key, p);
            bal(t);
            kv
        }
        Ordering::Equal => {
            if n.l.is_none() {
                let r = n.r.take();
                let node = t.take().unwrap();
                *t = r;
                unwrap_node(node)
            } else if n.r.is_none() {
                let l = n.l.take();
                let node = t.take().unwrap();
                *t = l;
                unwrap_node(node)
            } else {
                let (min, min_p) = remove_min(&mut n.r);
                n.p = min_p;
                let kv = std::mem::replace(&mut n.kv, min);
                bal(t);
                kv
            }
        }
    }
}

fn unwrap_node<K, V>(node: Rc<Node<K, V>>) -> Rc<(K, V)> {
    match Rc::try_unwrap(node) {
        Ok(node) => node.kv,
        Err(node) => node.kv.clone(),
    }
}

fn unwrap_entry<K: Clone, V: Clone>(kv: Rc<(K, V)>) -> (K, V) {
    Rc::try_unwrap(kv).unwrap_or_else(|kv| (*kv).clone())
}

fn for_each_entry<'a, K, V>(t: &'a Tree<K, V>, f: &mut impl FnMut(&'a Rc<(K, V)>)) {
    if let Some(n) = t {
        for_each_entry(&n.l, f);
        f(&n.kv);
        for_each_entry(&n.r, f);
    }
}

fn ptr_eq_tree<K, V>(a: &Tree<K, V>, b: &Tree<K, V>) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(a), Some(b)) => Rc::ptr_eq(a, b),
        _ => false,
    }
}

/// A persistent ordered map (see the module documentation).
pub struct Map<K, V> {
    root: Tree<K, V>,
    size: usize,
}

impl<K, V> Clone for Map<K, V> {
    #[inline]
    fn clone(&self) -> Self {
        Map {
            root: self.root.clone(),
            size: self.size,
        }
    }
}

impl<K, V> Default for Map<K, V> {
    #[inline]
    fn default() -> Self {
        Map {
            root: None,
            size: 0,
        }
    }
}

impl<K, V> Map<K, V> {
    /// The empty map (no allocation).
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.size
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    /// Whether the two maps are the same tree (OCaml's `==`): then they have
    /// the same entries.
    #[inline]
    pub fn ptr_eq(&self, other: &Self) -> bool {
        ptr_eq_tree(&self.root, &other.root)
    }

    /// The address of the root node (0 for the empty map): the identity of
    /// the tree, as long as the map is alive.
    pub fn root_addr(&self) -> usize {
        match &self.root {
            None => 0,
            Some(n) => Rc::as_ptr(n) as usize,
        }
    }

    pub fn iter(&self) -> Iter<'_, K, V> {
        let mut front = Vec::with_capacity(height(&self.root) as usize);
        push_left(&mut front, &self.root);
        Iter {
            front,
            back: Vec::new(),
            back_started: false,
            root: &self.root,
            remaining: self.size,
        }
    }

    pub fn entries(&self) -> Entries<'_, K, V> {
        Entries(self.iter())
    }

    pub fn keys(&self) -> Keys<'_, K, V> {
        Keys(self.iter())
    }

    pub fn values(&self) -> Values<'_, K, V> {
        Values(self.iter())
    }

    /// Calls `f` on every entry, in increasing order of the keys (without the
    /// allocation of an iterator).
    pub fn for_each<'a>(&'a self, mut f: impl FnMut(&'a K, &'a V)) {
        for_each_entry(&self.root, &mut |kv| f(&kv.0, &kv.1))
    }

    pub fn get_min(&self) -> Option<&(K, V)> {
        let mut t = self.root.as_ref()?;
        while let Some(l) = &t.l {
            t = l;
        }
        Some(&t.kv)
    }

    pub fn get_max(&self) -> Option<&(K, V)> {
        let mut t = self.root.as_ref()?;
        while let Some(r) = &t.r {
            t = r;
        }
        Some(&t.kv)
    }
}

impl<K: Key, V> Map<K, V> {
    #[inline]
    pub fn unit(k: K, v: V) -> Self {
        Map {
            root: Some({
                let p = k.prefix();
                leaf(Rc::new((k, v)), p)
            }),
            size: 1,
        }
    }

    #[inline]
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Key + ?Sized,
    {
        find(&self.root, key).map(|kv| &kv.1)
    }

    #[inline]
    pub fn get_key_value<Q>(&self, key: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q>,
        Q: Key + ?Sized,
    {
        find(&self.root, key).map(|kv| (&kv.0, &kv.1))
    }

    /// The entry of `key`, to share with another map.
    #[inline]
    pub fn get_entry<Q>(&self, key: &Q) -> Option<&Entry<K, V>>
    where
        K: Borrow<Q>,
        Q: Key + ?Sized,
    {
        find(&self.root, key)
    }

    #[inline]
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Key + ?Sized,
    {
        find(&self.root, key).is_some()
    }

    /// `Map.add`: adds the binding, replacing the one of an equal key (key
    /// and value). Unlike `im`, does not return the previous value (which
    /// would have to be cloned out of an entry that other versions share);
    /// see [`Map::insert_replacing`].
    #[inline]
    pub fn insert(&mut self, k: K, v: V) {
        let p = k.prefix();
        if insert(&mut self.root, Rc::new((k, v)), p).is_none() {
            self.size += 1;
        }
    }

    /// `insert` of an entry of another version of the map (see
    /// [`for_each_difference`]), which the two then share.
    #[inline]
    pub fn insert_entry(&mut self, entry: Entry<K, V>) {
        let p = entry.0.prefix();
        if insert(&mut self.root, entry, p).is_none() {
            self.size += 1;
        }
    }

    /// `insert`, returning the value it replaces (as `im::OrdMap::insert`).
    pub fn insert_replacing(&mut self, k: K, v: V) -> Option<V>
    where
        K: Clone,
        V: Clone,
    {
        let p = k.prefix();
        match insert(&mut self.root, Rc::new((k, v)), p) {
            None => {
                self.size += 1;
                None
            }
            Some(old) => Some(unwrap_entry(old).1),
        }
    }

    /// The map with the binding added (`Map.add` on a persistent map).
    pub fn update(&self, k: K, v: V) -> Self {
        let mut m = self.clone();
        m.insert(k, v);
        m
    }

    /// Removes the binding of `key` and returns its value.
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q> + Clone,
        V: Clone,
        Q: Key + ?Sized,
    {
        self.remove_entry(key).map(|kv| unwrap_entry(kv).1)
    }

    /// Removes the binding of `key`; says whether there was one.
    pub fn remove_key<Q>(&mut self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Key + ?Sized,
    {
        self.remove_entry(key).is_some()
    }

    fn remove_entry<Q>(&mut self, key: &Q) -> Option<Rc<(K, V)>>
    where
        K: Borrow<Q>,
        Q: Key + ?Sized,
    {
        // Look first, so that removing a missing key copies no node.
        find(&self.root, key)?;
        self.size -= 1;
        Some(remove_present(&mut self.root, key, key.prefix()))
    }

    /// The map without the binding of `key` (`Map.remove`).
    pub fn without<Q>(&self, key: &Q) -> Self
    where
        K: Borrow<Q>,
        Q: Key + ?Sized,
    {
        let mut m = self.clone();
        m.remove_key(key);
        m
    }

    /// The value of `key`, to change in place. The nodes on the path to it,
    /// and the entry, are copied first if other versions share them.
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q> + Clone,
        V: Clone,
        Q: Key + ?Sized,
    {
        find(&self.root, key)?;
        let p = key.prefix();
        let mut t = &mut self.root;
        loop {
            let n = Rc::make_mut(t.as_mut().unwrap());
            match cmp_node(key, p, n) {
                Ordering::Equal => return Some(&mut Rc::make_mut(&mut n.kv).1),
                Ordering::Less => t = &mut n.l,
                Ordering::Greater => t = &mut n.r,
            }
        }
    }

    /// The value of `key`, added with `default` if missing, to change in
    /// place (as `im`'s `entry(key).or_insert_with(default)`).
    pub fn get_or_insert_with(&mut self, key: K, default: impl FnOnce() -> V) -> &mut V
    where
        K: Clone,
        V: Clone,
    {
        if !self.contains_key(&key) {
            self.insert(key.clone(), default());
        }
        self.get_mut(&key).unwrap()
    }
}

enum WalkItem<'a, K, V> {
    Tree(&'a Rc<Node<K, V>>),
    Entry(&'a Rc<(K, V)>),
}

fn min_node<K, V>(mut n: &Rc<Node<K, V>>) -> &Rc<Node<K, V>> {
    while let Some(l) = &n.l {
        n = l;
    }
    n
}

fn walk_push<'a, K, V>(stack: &mut Vec<WalkItem<'a, K, V>>, t: &'a Tree<K, V>) {
    if let Some(n) = t {
        stack.push(WalkItem::Tree(n))
    }
}

/// Replaces the subtree on top of the stack by its left subtree, its entry
/// and its right subtree.
fn walk_expand<K, V>(stack: &mut Vec<WalkItem<'_, K, V>>) {
    match stack.pop() {
        Some(WalkItem::Tree(n)) => {
            walk_push(stack, &n.r);
            stack.push(WalkItem::Entry(&n.kv));
            walk_push(stack, &n.l);
        }
        _ => panic!("pmap: walk_expand of an entry"),
    }
}

/// Calls `f(entry of m2, value in m1)`, in increasing order of the keys,
/// for each binding of `m2` that is not also a binding of `m1` (where
/// "also" is physical: the same entry, shared by the two versions). The
/// subtrees that the maps share are skipped without being visited, so the
/// cost is proportional to what differs between two versions of a map, not
/// to their sizes. A binding of `m2` that has an equal key and value in `m1`
/// but not the same entry is passed to `f` too.
///
/// Callers use it in place of a full `Map.merge`/`union` of the OCaml: they
/// must apply the OCaml's combine to every binding passed here, and may skip
/// only the shared ones, on which the combine gives back the binding with no
/// effect.
pub fn for_each_difference<'a, K: Ord, V>(
    m1: &'a Map<K, V>,
    m2: &'a Map<K, V>,
    mut f: impl FnMut(&'a Entry<K, V>, Option<&'a V>),
) {
    let mut s1: Vec<WalkItem<'a, K, V>> = Vec::new();
    let mut s2: Vec<WalkItem<'a, K, V>> = Vec::new();
    walk_push(&mut s1, &m1.root);
    walk_push(&mut s2, &m2.root);
    loop {
        match (s1.last(), s2.last()) {
            (_, None) => break,
            (None, Some(WalkItem::Tree(_))) => walk_expand(&mut s2),
            (None, Some(WalkItem::Entry(e2))) => {
                let e2: &'a Rc<(K, V)> = *e2;
                f(e2, None);
                s2.pop();
            }
            (Some(WalkItem::Tree(a)), Some(WalkItem::Tree(b))) => {
                if Rc::ptr_eq(a, b) {
                    s1.pop();
                    s2.pop();
                } else if a.h >= b.h {
                    walk_expand(&mut s1)
                } else {
                    walk_expand(&mut s2)
                }
            }
            // A subtree is expanded only when the entry on the other side is
            // not before all its keys: otherwise the subtree could still meet
            // the same subtree of the other map.
            (Some(WalkItem::Tree(a)), Some(WalkItem::Entry(e2))) => {
                let e2: &'a Rc<(K, V)> = *e2;
                if e2.0 < min_node(a).kv.0 {
                    f(e2, None);
                    s2.pop();
                } else {
                    walk_expand(&mut s1)
                }
            }
            (Some(WalkItem::Entry(e1)), Some(WalkItem::Tree(b))) => {
                if e1.0 < min_node(b).kv.0 {
                    s1.pop();
                } else {
                    walk_expand(&mut s2)
                }
            }
            (Some(WalkItem::Entry(e1)), Some(WalkItem::Entry(e2))) => {
                let e1: &'a Rc<(K, V)> = *e1;
                let e2: &'a Rc<(K, V)> = *e2;
                match e1.0.cmp(&e2.0) {
                    Ordering::Less => {
                        s1.pop();
                    }
                    Ordering::Greater => {
                        f(e2, None);
                        s2.pop();
                    }
                    Ordering::Equal => {
                        if !Rc::ptr_eq(e1, e2) {
                            f(e2, Some(&e1.1));
                        }
                        s1.pop();
                        s2.pop();
                    }
                }
            }
        }
    }
}

impl<K: Key, V> Map<K, V> {
    /// The bindings of both maps; for a key that both have, the binding of
    /// `self` (`im::OrdMap::union`, and OCaml's `union` with a `combine` that
    /// keeps the first value). The entries are shared with the two maps.
    pub fn union(self, other: Self) -> Self {
        if other.is_empty() || self.ptr_eq(&other) {
            return self;
        }
        if self.is_empty() {
            return other;
        }
        if self.len() >= other.len() {
            let mut res = self;
            for_each_entry(&other.root, &mut |kv| {
                if !res.contains_key(&kv.0) {
                    res.insert_entry(Rc::clone(kv))
                }
            });
            res
        } else {
            let mut res = other;
            for_each_entry(&self.root, &mut |kv| res.insert_entry(Rc::clone(kv)));
            res
        }
    }
}

impl<K: Key + Clone, V: Clone> Map<K, V> {
    /// The entries, cloned, in increasing order of the keys.
    pub fn into_entries(self) -> Vec<(K, V)> {
        let mut v = Vec::with_capacity(self.size);
        for_each_entry(&self.root, &mut |kv| v.push((kv.0.clone(), kv.1.clone())));
        v
    }
}

fn push_left<'a, K, V>(stack: &mut Vec<&'a Node<K, V>>, mut t: &'a Tree<K, V>) {
    while let Some(n) = t {
        stack.push(n);
        t = &n.l;
    }
}

fn push_right<'a, K, V>(stack: &mut Vec<&'a Node<K, V>>, mut t: &'a Tree<K, V>) {
    while let Some(n) = t {
        stack.push(n);
        t = &n.r;
    }
}

/// The entries of a [`Map`] in increasing order of the keys (and in
/// decreasing order from the back).
pub struct Iter<'a, K, V> {
    front: Vec<&'a Node<K, V>>,
    back: Vec<&'a Node<K, V>>,
    back_started: bool,
    root: &'a Tree<K, V>,
    remaining: usize,
}

impl<'a, K, V> Iter<'a, K, V> {
    #[inline]
    fn next_entry(&mut self) -> Option<&'a Entry<K, V>> {
        if self.remaining == 0 {
            return None;
        }
        let n = self.front.pop()?;
        push_left(&mut self.front, &n.r);
        self.remaining -= 1;
        Some(&n.kv)
    }

    fn next_back_entry(&mut self) -> Option<&'a Entry<K, V>> {
        if self.remaining == 0 {
            return None;
        }
        if !self.back_started {
            self.back_started = true;
            self.back.reserve(height(self.root) as usize);
            push_right(&mut self.back, self.root);
        }
        let n = self.back.pop()?;
        push_right(&mut self.back, &n.l);
        self.remaining -= 1;
        Some(&n.kv)
    }
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.next_entry().map(|kv| (&kv.0, &kv.1))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl<K, V> DoubleEndedIterator for Iter<'_, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.next_back_entry().map(|kv| (&kv.0, &kv.1))
    }
}

impl<K, V> ExactSizeIterator for Iter<'_, K, V> {}

/// The entries themselves (to share them with another map, see
/// [`Map::insert_entry`]), in increasing order of the keys.
pub struct Entries<'a, K, V>(Iter<'a, K, V>);

impl<'a, K, V> Iterator for Entries<'a, K, V> {
    type Item = &'a Entry<K, V>;
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next_entry()
    }
}

impl<K, V> DoubleEndedIterator for Entries<'_, K, V> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back_entry()
    }
}

pub struct Keys<'a, K, V>(Iter<'a, K, V>);

impl<'a, K, V> Iterator for Keys<'a, K, V> {
    type Item = &'a K;
    #[inline]
    fn next(&mut self) -> Option<&'a K> {
        self.0.next().map(|(k, _)| k)
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<K, V> DoubleEndedIterator for Keys<'_, K, V> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back().map(|(k, _)| k)
    }
}

impl<K, V> ExactSizeIterator for Keys<'_, K, V> {}

pub struct Values<'a, K, V>(Iter<'a, K, V>);

impl<'a, K, V> Iterator for Values<'a, K, V> {
    type Item = &'a V;
    #[inline]
    fn next(&mut self) -> Option<&'a V> {
        self.0.next().map(|(_, v)| v)
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<K, V> DoubleEndedIterator for Values<'_, K, V> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back().map(|(_, v)| v)
    }
}

impl<K, V> ExactSizeIterator for Values<'_, K, V> {}

impl<'a, K, V> IntoIterator for &'a Map<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// Owned iteration clones the entries that other versions share (as `im`).
impl<K: Key + Clone, V: Clone> IntoIterator for Map<K, V> {
    type Item = (K, V);
    type IntoIter = std::vec::IntoIter<(K, V)>;
    fn into_iter(self) -> Self::IntoIter {
        self.into_entries().into_iter()
    }
}

impl<K: Key, V> FromIterator<(K, V)> for Map<K, V> {
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        let mut m = Map::new();
        for (k, v) in iter {
            m.insert(k, v);
        }
        m
    }
}

impl<K: Key, V> Extend<(K, V)> for Map<K, V> {
    fn extend<I: IntoIterator<Item = (K, V)>>(&mut self, iter: I) {
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

impl<K: PartialEq, V: PartialEq> PartialEq for Map<K, V> {
    fn eq(&self, other: &Self) -> bool {
        if ptr_eq_tree(&self.root, &other.root) {
            return true;
        }
        self.size == other.size
            && self
                .iter()
                .zip(other.iter())
                .all(|((k1, v1), (k2, v2))| k1 == k2 && v1 == v2)
    }
}

impl<K: Eq, V: Eq> Eq for Map<K, V> {}

impl<K: PartialOrd, V: PartialOrd> PartialOrd for Map<K, V> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<K: Ord, V: Ord> Ord for Map<K, V> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other.iter())
    }
}

impl<K: Hash, V: Hash> Hash for Map<K, V> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        for entry in self.iter() {
            entry.hash(state);
        }
    }
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for Map<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

/// A persistent ordered set: a [`Map`] to `()`.
pub struct Set<A>(Map<A, ()>);

impl<A> Clone for Set<A> {
    #[inline]
    fn clone(&self) -> Self {
        Set(self.0.clone())
    }
}

impl<A> Default for Set<A> {
    #[inline]
    fn default() -> Self {
        Set(Map::new())
    }
}

impl<A> Set<A> {
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    #[inline]
    pub fn ptr_eq(&self, other: &Self) -> bool {
        self.0.ptr_eq(&other.0)
    }

    pub fn iter(&self) -> Keys<'_, A, ()> {
        self.0.keys()
    }

    pub fn get_min(&self) -> Option<&A> {
        self.0.get_min().map(|(k, ())| k)
    }

    pub fn get_max(&self) -> Option<&A> {
        self.0.get_max().map(|(k, ())| k)
    }
}

impl<A: Key> Set<A> {
    #[inline]
    pub fn unit(a: A) -> Self {
        Set(Map::unit(a, ()))
    }

    #[inline]
    pub fn contains<Q>(&self, a: &Q) -> bool
    where
        A: Borrow<Q>,
        Q: Key + ?Sized,
    {
        self.0.contains_key(a)
    }

    /// `Set.add`. The element replaces an equal one (as `im::OrdSet`).
    #[inline]
    pub fn insert(&mut self, a: A) {
        self.0.insert(a, ())
    }

    #[inline]
    pub fn remove<Q>(&mut self, a: &Q) -> bool
    where
        A: Borrow<Q>,
        Q: Key + ?Sized,
    {
        self.0.remove_key(a)
    }

    pub fn update(&self, a: A) -> Self {
        Set(self.0.update(a, ()))
    }

    pub fn without<Q>(&self, a: &Q) -> Self
    where
        A: Borrow<Q>,
        Q: Key + ?Sized,
    {
        Set(self.0.without(a))
    }

    pub fn is_subset(&self, other: &Self) -> bool {
        self.len() <= other.len() && self.iter().all(|a| other.contains(a))
    }
}

impl<'a, A> IntoIterator for &'a Set<A> {
    type Item = &'a A;
    type IntoIter = Keys<'a, A, ()>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<A: Key + Clone> IntoIterator for Set<A> {
    type Item = A;
    type IntoIter = std::iter::Map<std::vec::IntoIter<(A, ())>, fn((A, ())) -> A>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter().map(|(a, ())| a)
    }
}

impl<A: Key> FromIterator<A> for Set<A> {
    fn from_iter<I: IntoIterator<Item = A>>(iter: I) -> Self {
        Set(iter.into_iter().map(|a| (a, ())).collect())
    }
}

impl<A: Key> Extend<A> for Set<A> {
    fn extend<I: IntoIterator<Item = A>>(&mut self, iter: I) {
        for a in iter {
            self.insert(a);
        }
    }
}

impl<A: PartialEq> PartialEq for Set<A> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<A: Eq> Eq for Set<A> {}

impl<A: PartialOrd> PartialOrd for Set<A> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<A: Ord> Ord for Set<A> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other.iter())
    }
}

impl<A: Hash> Hash for Set<A> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        for a in self.iter() {
            a.hash(state);
        }
    }
}

impl<A: fmt::Debug> fmt::Debug for Set<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

// ---------------------------------------------------------------------------
// IntMap

/// A persistent map from small non-negative integers (type variables, which
/// are numbered densely from 0 in each definition): a trie of 16-way nodes
/// indexed by the digits of the key in base 16. Same sharing as [`Map`]: the
/// entries `Rc<(key, value)>` are shared between the versions, an update of
/// a shared map copies the nodes on the path to the key (4 of them for 60,000
/// keys, against about 17 for a balanced binary tree; 16-way nodes measured
/// better than 32-way ones, whose copies touch twice as many entries), and an
/// unshared map is updated in place. The methods are those of [`Map`] that the callers use.
/// OCaml keeps these maps in `Tvid.Map` (an AVL tree); made the
/// representation of the inference environment's tvenv and tyvar-occurrence
/// maps (32-way then), this took the sample from 109.8G to 107.0G
/// instructions.
pub struct IntMap<V> {
    root: Option<Rc<INode<V>>>,
    /// The number of levels below and including the root (0 when empty):
    /// the keys are below `16^levels`.
    levels: u32,
    len: usize,
}

const IBITS: u32 = 4;
const IWIDTH: usize = 1 << IBITS;
const IMASK: usize = IWIDTH - 1;
/// Enough levels for any `usize`.
const IMAX_LEVELS: u32 = usize::BITS.div_ceil(IBITS);

enum INode<V> {
    Branch([Option<Rc<INode<V>>>; IWIDTH]),
    Leaf([Option<Entry<isize, V>>; IWIDTH]),
}

impl<V> Clone for INode<V> {
    fn clone(&self) -> Self {
        match self {
            INode::Branch(a) => INode::Branch(a.clone()),
            INode::Leaf(a) => INode::Leaf(a.clone()),
        }
    }
}

impl<V> INode<V> {
    fn new(leaf: bool) -> Self {
        if leaf {
            INode::Leaf(std::array::from_fn(|_| None))
        } else {
            INode::Branch(std::array::from_fn(|_| None))
        }
    }

    fn entries<'a>(&'a self, acc: &mut Vec<&'a Entry<isize, V>>) {
        match self {
            INode::Branch(a) => {
                for n in a.iter().flatten() {
                    n.entries(acc)
                }
            }
            INode::Leaf(a) => acc.extend(a.iter().flatten()),
        }
    }
}

#[inline]
fn idigit(k: usize, level: u32) -> usize {
    // `level` 0 is the leaves.
    (k >> (IBITS * level)) & IMASK
}

#[inline]
fn ifits(k: usize, levels: u32) -> bool {
    levels >= IMAX_LEVELS || k >> (IBITS * levels) == 0
}

impl<V> Clone for IntMap<V> {
    fn clone(&self) -> Self {
        IntMap {
            root: self.root.clone(),
            levels: self.levels,
            len: self.len,
        }
    }
}

impl<V> Default for IntMap<V> {
    fn default() -> Self {
        IntMap::new()
    }
}

impl<V> IntMap<V> {
    pub fn new() -> Self {
        IntMap {
            root: None,
            levels: 0,
            len: 0,
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// The two maps are the same version (one is a copy of the other, and
    /// neither changed since).
    pub fn ptr_eq(&self, other: &Self) -> bool {
        match (&self.root, &other.root) {
            (None, None) => true,
            (Some(a), Some(b)) => Rc::ptr_eq(a, b) && self.levels == other.levels,
            _ => false,
        }
    }

    pub fn root_addr(&self) -> usize {
        match &self.root {
            None => 0,
            Some(n) => Rc::as_ptr(n) as usize,
        }
    }

    pub fn get_entry(&self, k: &isize) -> Option<&Entry<isize, V>> {
        let k = *k as usize;
        if !ifits(k, self.levels) {
            return None;
        }
        let mut node = self.root.as_deref()?;
        let mut level = self.levels - 1;
        loop {
            match node {
                INode::Branch(a) => {
                    node = a[idigit(k, level)].as_deref()?;
                    level -= 1;
                }
                INode::Leaf(a) => return a[idigit(k, 0)].as_ref(),
            }
        }
    }

    pub fn get(&self, k: &isize) -> Option<&V> {
        self.get_entry(k).map(|e| &e.1)
    }

    pub fn contains_key(&self, k: &isize) -> bool {
        self.get_entry(k).is_some()
    }

    /// The bindings, in increasing order of the keys.
    pub fn entries(&self) -> Vec<&Entry<isize, V>> {
        let mut acc = Vec::with_capacity(self.len);
        if let Some(n) = &self.root {
            n.entries(&mut acc)
        }
        acc
    }

    pub fn iter(&self) -> IntIter<'_, V> {
        IntIter(self.entries().into_iter())
    }

    pub fn keys(&self) -> impl DoubleEndedIterator<Item = &isize> + '_ {
        self.iter().map(|(k, _)| k)
    }

    pub fn values(&self) -> impl DoubleEndedIterator<Item = &V> + '_ {
        self.iter().map(|(_, v)| v)
    }

    /// The leaf slot of `k`, made unshared, creating the nodes on the way.
    fn slot_mut(&mut self, k: usize) -> &mut Option<Entry<isize, V>> {
        if self.root.is_none() {
            self.levels = 1;
            while !ifits(k, self.levels) {
                self.levels += 1;
            }
            self.root = Some(Rc::new(INode::new(self.levels == 1)));
        }
        while !ifits(k, self.levels) {
            let mut branch = INode::new(false);
            if let INode::Branch(a) = &mut branch {
                a[0] = self.root.take();
            }
            self.root = Some(Rc::new(branch));
            self.levels += 1;
        }
        let mut level = self.levels - 1;
        let mut node = Rc::make_mut(self.root.as_mut().unwrap());
        loop {
            match node {
                INode::Branch(a) => {
                    let child = a[idigit(k, level)]
                        .get_or_insert_with(|| Rc::new(INode::new(level == 1)));
                    node = Rc::make_mut(child);
                    level -= 1;
                }
                INode::Leaf(a) => return &mut a[idigit(k, 0)],
            }
        }
    }

    pub fn insert_entry(&mut self, entry: Entry<isize, V>) {
        let slot = self.slot_mut(entry.0 as usize);
        let added = slot.is_none();
        *slot = Some(entry);
        if added {
            self.len += 1;
        }
    }

    pub fn insert(&mut self, k: isize, v: V) {
        self.insert_entry(Rc::new((k, v)))
    }

    /// Removes the binding of `k`; whether there was one.
    pub fn remove_key(&mut self, k: &isize) -> bool {
        if !self.contains_key(k) {
            return false;
        }
        *self.slot_mut(*k as usize) = None;
        self.len -= 1;
        if self.len == 0 {
            self.root = None;
            self.levels = 0;
        }
        true
    }
}

impl<V: Clone> IntMap<V> {
    /// The value of `k`, to change in place. The nodes on the path to it,
    /// and the entry, are copied first if other versions share them.
    pub fn get_mut(&mut self, k: &isize) -> Option<&mut V> {
        if !self.contains_key(k) {
            return None;
        }
        let slot = self.slot_mut(*k as usize);
        Some(&mut Rc::make_mut(slot.as_mut().unwrap()).1)
    }

    /// The value of `k`, added with `default` if missing, to change in place.
    pub fn get_or_insert_with(&mut self, k: isize, default: impl FnOnce() -> V) -> &mut V {
        if !self.contains_key(&k) {
            self.len += 1;
        }
        let slot = self.slot_mut(k as usize);
        let entry = slot.get_or_insert_with(|| Rc::new((k, default())));
        &mut Rc::make_mut(entry).1
    }
}

pub struct IntIter<'a, V>(std::vec::IntoIter<&'a Entry<isize, V>>);

impl<'a, V> Iterator for IntIter<'a, V> {
    type Item = (&'a isize, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|e| (&e.0, &e.1))
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<V> DoubleEndedIterator for IntIter<'_, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back().map(|e| (&e.0, &e.1))
    }
}

impl<V> ExactSizeIterator for IntIter<'_, V> {}

impl<'a, V> IntoIterator for &'a IntMap<V> {
    type Item = (&'a isize, &'a V);
    type IntoIter = IntIter<'a, V>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<V: fmt::Debug> fmt::Debug for IntMap<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

/// [`for_each_difference`] for [`IntMap`]: `f(entry of m2, value in m1)`, in
/// increasing order of the keys, for each binding of `m2` that is not the
/// same entry in `m1`; the subtrees the two maps share are skipped.
pub fn for_each_difference_int<'a, V>(
    m1: &'a IntMap<V>,
    m2: &'a IntMap<V>,
    mut f: impl FnMut(&'a Entry<isize, V>, Option<&'a V>),
) {
    fn all<'a, V>(n: &'a INode<V>, f: &mut impl FnMut(&'a Entry<isize, V>, Option<&'a V>)) {
        match n {
            INode::Branch(a) => {
                for c in a.iter().flatten() {
                    all(c, f)
                }
            }
            INode::Leaf(a) => {
                for e in a.iter().flatten() {
                    f(e, None)
                }
            }
        }
    }
    // Nodes at the same level.
    fn same<'a, V>(
        n1: &'a Rc<INode<V>>,
        n2: &'a Rc<INode<V>>,
        f: &mut impl FnMut(&'a Entry<isize, V>, Option<&'a V>),
    ) {
        if Rc::ptr_eq(n1, n2) {
            return;
        }
        match (&**n1, &**n2) {
            (INode::Branch(a1), INode::Branch(a2)) => {
                for (c1, c2) in a1.iter().zip(a2.iter()) {
                    match (c1, c2) {
                        (_, None) => {}
                        (None, Some(c2)) => all(c2, f),
                        (Some(c1), Some(c2)) => same(c1, c2, f),
                    }
                }
            }
            (INode::Leaf(a1), INode::Leaf(a2)) => {
                for (e1, e2) in a1.iter().zip(a2.iter()) {
                    match (e1, e2) {
                        (_, None) => {}
                        (None, Some(e2)) => f(e2, None),
                        (Some(e1), Some(e2)) => {
                            if !Rc::ptr_eq(e1, e2) {
                                f(e2, Some(&e1.1))
                            }
                        }
                    }
                }
            }
            _ => panic!("pmap: IntMap nodes of different kinds at one level"),
        }
    }
    // `n1` has `l1` levels, `n2` has `l2`.
    fn diff<'a, V>(
        n1: Option<&'a Rc<INode<V>>>,
        l1: u32,
        n2: &'a Rc<INode<V>>,
        l2: u32,
        f: &mut impl FnMut(&'a Entry<isize, V>, Option<&'a V>),
    ) {
        match n1 {
            None => all(n2, f),
            Some(n1) if l1 == l2 => same(n1, n2, f),
            Some(n1) if l1 > l2 => {
                // The keys of `m2` are all under the first child of `n1`.
                let c1 = match &**n1 {
                    INode::Branch(a) => a[0].as_ref(),
                    INode::Leaf(_) => unreachable!(),
                };
                diff(c1, l1 - 1, n2, l2, f)
            }
            Some(n1) => match &**n2 {
                INode::Branch(a) => {
                    for (i, c2) in a.iter().enumerate() {
                        if let Some(c2) = c2 {
                            if i == 0 {
                                diff(Some(n1), l1, c2, l2 - 1, f)
                            } else {
                                all(c2, f)
                            }
                        }
                    }
                }
                INode::Leaf(_) => unreachable!(),
            },
        }
    }
    if let Some(n2) = &m2.root {
        diff(m1.root.as_ref(), m1.levels, n2, m2.levels, &mut f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check<K: Key, V>(t: &Tree<K, V>) -> (u32, usize) {
        match t {
            None => (0, 0),
            Some(n) => {
                let (hl, sl) = check(&n.l);
                let (hr, sr) = check(&n.r);
                assert!(hl <= hr + 2 && hr <= hl + 2, "unbalanced");
                assert_eq!(n.h, hl.max(hr) + 1, "wrong height");
                assert_eq!(n.p, n.kv.0.prefix(), "wrong prefix");
                if let Some(l) = &n.l {
                    assert!(l.kv.0 < n.kv.0);
                }
                if let Some(r) = &n.r {
                    assert!(r.kv.0 > n.kv.0);
                }
                (n.h, sl + sr + 1)
            }
        }
    }

    fn invariants<K: Key, V>(m: &Map<K, V>) {
        let (_, size) = check(&m.root);
        assert_eq!(size, m.len());
    }

    #[test]
    fn against_btreemap() {
        let mut m: Map<i64, i64> = Map::new();
        let mut b = std::collections::BTreeMap::new();
        let mut versions = vec![];
        let mut x: i64 = 7;
        for i in 0..4000 {
            x = (x * 1103515245 + 12345) % 2147483648;
            let k = x % 300;
            if x % 3 == 0 {
                assert_eq!(m.remove(&k), b.remove(&k));
            } else {
                assert_eq!(m.insert_replacing(k, i), b.insert(k, i));
            }
            if i % 97 == 0 {
                versions.push((m.clone(), b.clone()));
            }
            if i % 13 == 0 {
                if let Some(v) = m.get_mut(&(k + 1)) {
                    *v += 1;
                    *b.get_mut(&(k + 1)).unwrap() += 1;
                }
            }
            invariants(&m);
        }
        for (m, b) in versions {
            invariants(&m);
            assert!(m.iter().map(|(k, v)| (*k, *v)).eq(b.iter().map(|(k, v)| (*k, *v))));
            assert!(
                m.iter()
                    .rev()
                    .map(|(k, v)| (*k, *v))
                    .eq(b.iter().rev().map(|(k, v)| (*k, *v)))
            );
            assert_eq!(m.get_min().map(|kv| kv.0), b.keys().next().copied());
            assert_eq!(m.get_max().map(|kv| kv.0), b.keys().next_back().copied());
        }
    }

    #[test]
    fn difference_walk() {
        let mut x: i64 = 11;
        let mut base: Map<i64, i64> = Map::new();
        for i in 0..500 {
            x = (x * 1103515245 + 12345) % 2147483648;
            base.insert(x % 1000, i);
        }
        for round in 0..50 {
            let mut m1 = base.clone();
            let mut m2 = base.clone();
            for j in 0..round {
                x = (x * 1103515245 + 12345) % 2147483648;
                match x % 4 {
                    0 => m1.insert(x % 1000, j),
                    1 => m2.insert(x % 1000, j),
                    2 => {
                        m2.remove_key(&(x % 1000));
                    }
                    _ => {
                        m1.remove_key(&(x % 1000));
                    }
                }
            }
            let mut got = vec![];
            for_each_difference(&m1, &m2, |e2, v1| got.push((e2.0, v1.copied(), e2.1)));
            // Naively: the bindings of m2 that m1 does not have (as the same
            // entry).
            let mut expected = vec![];
            for (k, v2) in m2.iter() {
                match m1.get(k) {
                    Some(v1) if std::ptr::eq(v1, v2) => {}
                    v1 => expected.push((*k, v1.copied(), *v2)),
                }
            }
            assert_eq!(got, expected);
        }
    }

    #[test]
    fn double_ended_meets_in_the_middle() {
        let m: Map<i32, ()> = (0..10).map(|i| (i, ())).collect();
        let mut it = m.keys();
        let mut seen = vec![];
        while let Some(a) = it.next() {
            seen.push(*a);
            if let Some(b) = it.next_back() {
                seen.push(*b);
            }
        }
        seen.sort();
        assert_eq!(seen, (0..10).collect::<Vec<_>>());
    }

    #[test]
    fn prefixes_are_monotone() {
        let ids: Vec<(isize, String)> = [-3isize, -1, 0, 1, 5, u32::MAX as isize - 1, u32::MAX as isize, 1 << 40]
            .iter()
            .flat_map(|i| ["", "$a", "$ab", "$abcde", "$b", "z"].iter().map(move |n| (*i, n.to_string())))
            .collect();
        for a in &ids {
            for b in &ids {
                if a < b {
                    assert!(a.prefix() <= b.prefix(), "{:?} {:?}", a, b);
                }
            }
        }
        let strs = ["", "a", "a\0", "a\u{1}", "ab", "abcdefgh", "abcdefghi", "abcdefgi", "b"];
        for a in strs {
            for b in strs {
                if a < b {
                    assert!(a.prefix() <= b.prefix(), "{:?} {:?}", a, b);
                }
            }
        }
        assert!((-1isize).prefix() < 0isize.prefix() && 0isize.prefix() < isize::MAX.prefix());
        // Lookups by `str` in a map with `String` keys.
        let m: Map<String, usize> = strs.iter().map(|s| (s.to_string(), s.len())).collect();
        for s in strs {
            assert_eq!(m.get(s), Some(&s.len()));
        }
    }

    #[test]
    fn versions_share_and_stay_valid() {
        let a: Map<String, i32> = [("x".to_string(), 1), ("y".to_string(), 2)]
            .into_iter()
            .collect();
        let mut b = a.clone();
        b.insert("z".to_string(), 3);
        *b.get_mut("x").unwrap() = 10;
        assert_eq!(a.get("x"), Some(&1));
        assert_eq!(b.get("x"), Some(&10));
        assert!(!a.contains_key("z"));
        assert_eq!(b.len(), 3);
        // The entry of "y" is shared.
        assert!(std::ptr::eq(a.get("y").unwrap(), b.get("y").unwrap()));
        let s: Set<i32> = [3, 1, 2].into_iter().collect();
        assert_eq!(s.iter().copied().collect::<Vec<_>>(), vec![1, 2, 3]);
        assert!(s.without(&2).is_subset(&s));
    }

    #[test]
    fn int_map() {
        let mut a: IntMap<usize> = IntMap::new();
        for k in [5isize, 0, 31, 32, 1000, 40000, 3] {
            a.insert(k, k as usize * 2);
        }
        let b = a.clone();
        a.insert(7, 14);
        assert!(a.remove_key(&1000));
        assert!(!a.remove_key(&1001));
        assert_eq!(b.get(&1000), Some(&2000));
        assert_eq!(a.get(&1000), None);
        assert_eq!(a.len(), 7);
        assert_eq!(
            a.keys().copied().collect::<Vec<_>>(),
            vec![0, 3, 5, 7, 31, 32, 40000]
        );
        let mut d = vec![];
        for_each_difference_int(&b, &a, |e, old| d.push((e.0, old.copied())));
        assert_eq!(d, vec![(7, None)]);
        let mut d = vec![];
        for_each_difference_int(&IntMap::new(), &b, |e, old| d.push((e.0, old.copied())));
        assert_eq!(d.len(), b.len());
        let small: IntMap<usize> = {
            let mut m = IntMap::new();
            m.insert(1, 1);
            m
        };
        let mut d = vec![];
        for_each_difference_int(&small, &b, |e, old| d.push((e.0, old.copied())));
        assert_eq!(d.len(), b.len());
        let mut d = vec![];
        for_each_difference_int(&b, &small, |e, old| d.push((e.0, old.copied())));
        assert_eq!(d, vec![(1, None)]);
    }
}
