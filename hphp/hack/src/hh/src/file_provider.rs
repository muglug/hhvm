// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `providers/file_provider.ml`. See `hh/PORTING.md`.
//!
//! Shared memory heap containing the contents of files.
//! Acts as a sort of caching facade which is filled on-demand
//! as contents are needed - The "cache" is filled by loading from
//! the file system.
//!
//! Every function of the OCaml matches on the backend of the process
//! (`Provider_backend.get ()`). In this crate a backend is that of a `Ctx`,
//! and there is no backend of the process: these functions, which are not
//! given a context, are `todo!`. The `Shared_memory` behaviour (`FileHeap`,
//! else the file on disk, a missing file reading as `""`) is that of the
//! files of a `Ctx` (`Ctx::files`, whose overlay stands for `FileHeap`):
//! [`rust_provider_backend::file`], which a caller that has a context uses
//! (as `crate::ast_provider` does). [`file_heap`] is kept for its stacks of
//! local changes, which the OCaml pushes and pops with every backend.

use bstr::BString;
use relative_path::RelativePath;

/// `exception File_provider_stale`: the payload of the panic that raises it
/// (it is caught far from where it is raised).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FileProviderStale;

impl std::fmt::Display for FileProviderStale {
    /// `Printexc.to_string File_provider_stale`
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("File_provider.File_provider_stale")
    }
}

impl std::error::Error for FileProviderStale {}

/// `module FileHeap`: `Shared_mem.Heap (Shared_mem.ImmediateBackend
/// (Shared_mem.Evictable)) (Relative_path.S)` of `string` (description
/// `"File"`), with `replace_nonatomic`.
///
/// The contents themselves are read from `Ctx::files` (see the module doc),
/// but `local_changes_push_sharedmem_stack` and
/// `local_changes_pop_sharedmem_stack` push and pop its stack of local
/// changes with every backend (`Typing_check_service` does around each
/// batch). The stack is a global `ref` of each worker process in OCaml, and
/// a worker is a thread here: the heap (made of
/// `crate::ast_provider::shared_mem::Heap`) is that of the thread.
pub mod file_heap {
    use std::cell::RefCell;

    use bstr::BString;
    use relative_path::RelativePath;

    use crate::ast_provider::shared_mem::Heap;

    thread_local! {
        static FILE_HEAP: RefCell<Heap<BString>> = RefCell::new(Heap::new());
    }

    pub fn add(x: RelativePath, y: BString) {
        FILE_HEAP.with_borrow_mut(|heap| heap.add(x, y))
    }

    pub fn get(x: &RelativePath) -> Option<BString> {
        FILE_HEAP.with_borrow(|heap| heap.get(x))
    }

    pub fn mem(x: &RelativePath) -> bool {
        FILE_HEAP.with_borrow(|heap| heap.mem(x))
    }

    pub fn remove(x: &RelativePath) {
        FILE_HEAP.with_borrow_mut(|heap| heap.remove(x))
    }

    /// `KeySet.iter remove xs`
    pub fn remove_batch(xs: &crate::relative_path::set::T) {
        for x in xs {
            remove(x)
        }
    }

    pub fn replace_nonatomic(key: RelativePath, value: BString) {
        if mem(&key) {
            remove(&key)
        };
        add(key, value)
    }

    /// Not in the OCaml: the heap of this thread stands for the one in
    /// shared memory; every file is removed from it when files may have
    /// changed (see `crate::rt::decl_epoch`), its stack keeps its depth.
    pub fn forget_thread_heap() {
        FILE_HEAP.with_borrow_mut(|heap| heap.clear_keeping_stacks())
    }

    /// `FileHeap.LocalChanges`
    pub mod local_changes {
        use super::FILE_HEAP;

        pub fn push_stack() {
            FILE_HEAP.with_borrow_mut(|heap| heap.push_stack())
        }

        pub fn pop_stack() {
            FILE_HEAP.with_borrow_mut(|heap| heap.pop_stack())
        }
    }
}

pub fn get_contents(force_read_disk: Option<bool>, fn_: &RelativePath) -> Option<BString> {
    let force_read_disk = force_read_disk.unwrap_or(false);
    let _ = (force_read_disk, fn_);
    todo!(
        "File_provider.get_contents: Provider_backend.get () (the backend of the process) has no counterpart: the files are those of a Ctx (see rust_provider_backend::file::get_contents)"
    )
}

pub fn provide_file_for_tests(fn_: &RelativePath, contents: BString) {
    let _ = (fn_, contents);
    todo!(
        "File_provider.provide_file_for_tests: Provider_backend.get () (the backend of the process) has no counterpart: the files are those of a Ctx (see rust_provider_backend::file::provide_file_for_tests)"
    )
}

pub fn remove_batch(paths: &crate::relative_path::set::T) {
    let _ = paths;
    todo!(
        "File_provider.remove_batch: Provider_backend.get () (the backend of the process) has no counterpart: the files are those of a Ctx"
    )
}

pub fn local_changes_push_sharedmem_stack() {
    file_heap::local_changes::push_stack()
}

pub fn local_changes_pop_sharedmem_stack() {
    file_heap::local_changes::pop_stack()
}

/// The functions of `File_provider` for the files of a `Ctx`, with the
/// behaviour of the `Shared_memory` branches (see the module doc); they are
/// written in the shape of `Rust_provider_backend.File`
/// (`providers/rust_provider_backend.ml`), over `Ctx::files`.
pub mod rust_provider_backend {
    pub mod file {
        use ::file_provider::FileProvider;
        use bstr::BString;
        use relative_path::RelativePath;

        use crate::provider_context::T as Ctx;

        /// `backend.file_provider().get(path).ok()`. The file provider of
        /// hh_server's Rust backend (`FileProviderWithChanges` in
        /// `hackrs_provider_backend.rs`) reads a file that does not exist as
        /// `""` (`Err(e) if e.kind() == NotFound => Ok("")`), as the
        /// `Shared_memory` branch of `get_contents` does
        /// (`Option.value (read_file_contents_from_disk fn) ~default:""`);
        /// `Ctx::files` fails then, so that is done here.
        pub fn get_contents(backend: &Ctx, fn_: &RelativePath) -> Option<BString> {
            match backend.files.get(pos::RelativePath::from(fn_)) {
                Ok(contents) => Some(contents),
                Err(err) => match err.downcast_ref::<std::io::Error>() {
                    Some(err) if err.kind() == std::io::ErrorKind::NotFound => {
                        Some(BString::from(""))
                    }
                    _ => None,
                },
            }
        }

        /// `backend.file_provider_provide_file_for_tests(path, contents)`
        pub fn provide_file_for_tests(backend: &Ctx, fn_: &RelativePath, contents: BString) {
            backend.files.set(pos::RelativePath::from(fn_), contents)
        }

        pub fn remove_batch(backend: &Ctx, paths: &crate::relative_path::set::T) {
            let _ = (backend, paths);
            todo!(
                "File_provider.remove_batch: the files of a Ctx (Ctx::files) cannot be removed"
            )
        }
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;
    use std::sync::Arc;

    use oxidized::typechecker_options::TypecheckerOptions;
    use relative_path::Prefix;

    use super::*;

    #[test]
    fn files_of_a_context() {
        let ctx = Arc::new(crate::ctx::Ctx::new(Path::new("/nonexistent"), TypecheckerOptions::default()).unwrap());
        let path = RelativePath::make(Prefix::Root, "a.php".into());
        // A file that does not exist reads as "".
        assert_eq!(
            rust_provider_backend::file::get_contents(&ctx, &path),
            Some(BString::from(""))
        );
        rust_provider_backend::file::provide_file_for_tests(&ctx, &path, BString::from("<?hh"));
        assert_eq!(
            rust_provider_backend::file::get_contents(&ctx, &path),
            Some(BString::from("<?hh"))
        );
        assert_eq!(FileProviderStale.to_string(), "File_provider.File_provider_stale");
    }

    #[test]
    fn file_heap_local_changes() {
        let path = RelativePath::make(Prefix::Root, "heap.php".into());
        file_heap::add(path.clone(), BString::from("a"));
        local_changes_push_sharedmem_stack();
        file_heap::replace_nonatomic(path.clone(), BString::from("b"));
        assert_eq!(file_heap::get(&path), Some(BString::from("b")));
        local_changes_pop_sharedmem_stack();
        assert_eq!(file_heap::get(&path), Some(BString::from("a")));
        file_heap::remove_batch(&std::iter::once(path.clone()).collect());
        assert!(!file_heap::mem(&path));
        assert!(std::panic::catch_unwind(local_changes_pop_sharedmem_stack).is_err());
    }
}
