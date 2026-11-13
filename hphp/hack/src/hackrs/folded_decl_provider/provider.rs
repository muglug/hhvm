// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

use std::collections::VecDeque;
use std::sync::Arc;

use datastore::Store;
use hash::IndexSet;
use oxidized::decl_fold_options::DeclFoldOptions;
use oxidized::naming_types::KindOfType;
use pos::Positioned;
use pos::TypeName;
use shallow_decl_provider::ShallowDeclProvider;
use ty::decl::FoldedClass;
use ty::decl::ShallowClass;
use ty::decl::Ty;
use ty::decl::Ty_;
use ty::decl_error::DeclError;
use ty::reason::Reason;

use super::Error;
use super::Result;
use super::TypeDecl;
use super::fold::DeclFolder;
use super::fold::Parents;

// note(sf, 2022-02-03): c.f. hphp/hack/src/decl/decl_folded_class.ml

/// A `FoldedDeclProvider` which, if the requested class name is not present in
/// its store, recursively computes the folded decl for that class by requesting
/// the shallow decls of that class and its ancestors from its
/// `ShallowDeclProvider`.
#[derive(Debug)]
pub struct LazyFoldedDeclProvider<R: Reason> {
    opts: Arc<DeclFoldOptions>,
    store: Arc<dyn Store<TypeName, Arc<FoldedClass<R>>>>,
    shallow_decl_provider: Arc<dyn ShallowDeclProvider<R>>,
}

impl<R: Reason> LazyFoldedDeclProvider<R> {
    pub fn new(
        opts: Arc<DeclFoldOptions>,
        store: Arc<dyn Store<TypeName, Arc<FoldedClass<R>>>>,
        shallow_decl_provider: Arc<dyn ShallowDeclProvider<R>>,
    ) -> Self {
        Self {
            opts,
            store,
            shallow_decl_provider,
        }
    }
}

impl<R: Reason> super::FoldedDeclProvider<R> for LazyFoldedDeclProvider<R> {
    fn get_type(&self, name: TypeName) -> Result<Option<TypeDecl<R>>> {
        match self.shallow_decl_provider.get_type_kind(name)? {
            None => Ok(None),
            Some(KindOfType::TTypedef) => Ok(self
                .shallow_decl_provider
                .get_typedef(name)?
                .map(TypeDecl::Typedef)),
            Some(KindOfType::TClass) => {
                // `Decl_folded_class.class_decl_if_missing ~sh ctx name`,
                // which declares the class with an empty stack.
                Ok(self
                    .class_decl_if_missing(&IndexSet::default(), name)?
                    .map(TypeDecl::Class))
            }
        }
    }
}

impl<R: Reason> LazyFoldedDeclProvider<R> {
    // note(sf, 2022-03-02): c.f. Decl_folded_class.check_if_cyclic
    //
    // `class_env.stack` is `stack`.
    fn check_if_cyclic(
        stack: &IndexSet<TypeName>,
        pos_id: &Positioned<TypeName, R::Pos>,
    ) -> Option<DeclError<R::Pos>> {
        let is_cyclic = stack.contains(&pos_id.id());
        if is_cyclic {
            // (`stack` is an `S_set.t`: its elements in increasing order.)
            let mut stack: Vec<TypeName> = stack.iter().copied().collect();
            stack.sort_by(|x, y| x.as_str().cmp(y.as_str()));
            // `Pos_or_decl.unsafe_to_raw_pos pos`
            Some(DeclError::CyclicClassDef(pos_id.pos().clone(), stack))
        } else {
            None
        }
    }

    fn parent_error(sc: &ShallowClass<R>, parent_name: TypeName, err: Error) -> Error {
        // We tried to produce a decl of the parent of the given class but
        // failed. We capture this chain of events as a `Parent` error. The has
        // the effect of explaining that "we couldn't decl 'class' because we
        // couldn't decl 'parent' because ... x" ( where 'x' is the underlying
        // error like, the parent's php file is missing).
        match err {
            Error::Parent {
                class: _,
                mut parents,
                error,
            } => {
                parents.push(parent_name);
                Error::Parent {
                    class: sc.name.id(),
                    parents,
                    error,
                }
            }
            _ => Error::Parent {
                class: sc.name.id(),
                parents: vec![parent_name],
                error: Box::new(err),
            },
        }
    }

    // note(sf, 2022-03-02): c.f. Decl_folded_class.declare_class_and_parents
    //
    // The OCaml also returns the members of the class for the member heaps,
    // which do not exist here.
    fn declare_class_and_parents(
        &self,
        stack: &IndexSet<TypeName>,
        shallow_class: &ShallowClass<R>,
    ) -> Result<Arc<FoldedClass<R>>> {
        let name = shallow_class.name.id();
        let mut stack = stack.clone();
        stack.insert(name);
        let (parents, errors) = self.class_parents_decl(&stack, shallow_class)?;
        // `class_decl` declares `StringishObject` with an empty stack.
        let mut class_decl_if_missing = |class_name: TypeName| {
            self.class_decl_if_missing(&IndexSet::default(), class_name)
                .map_err(|err| Self::parent_error(shallow_class, class_name, err))
        };
        DeclFolder::decl_class(
            &self.opts,
            shallow_class,
            &parents,
            errors,
            &mut class_decl_if_missing,
        )
    }

    // note(sf, 2022-03-02): c.f. Decl_folded_class.class_parents_decl
    //
    // The errors are in the order of the OCaml list (the last one first).
    fn class_parents_decl(
        &self,
        stack: &IndexSet<TypeName>,
        c: &ShallowClass<R>,
    ) -> Result<(Parents<R>, Vec<DeclError<R::Pos>>)> {
        let class_type_decl = |(mut parents, mut errs): (Parents<R>, VecDeque<_>),
                               class_ty: &Ty<R>|
         -> Result<(Parents<R>, VecDeque<_>)> {
            match class_ty.node_ref() {
                Ty_::Tapply(id_and_args) => {
                    let (pos_id, _) = &**id_and_args;
                    let class_name = pos_id.id();
                    match Self::check_if_cyclic(stack, pos_id) {
                        Some(err) => {
                            errs.push_front(err);
                            Ok((parents, errs))
                        }
                        None => match self
                            .class_decl_if_missing(stack, class_name)
                            .map_err(|err| Self::parent_error(c, class_name, err))?
                        {
                            None => Ok((parents, errs)),
                            Some(decls) => {
                                parents.insert(class_name, decls);
                                Ok((parents, errs))
                            }
                        },
                    }
                }
                _ => Ok((parents, errs)),
            }
        };
        let acc = (Parents::default(), VecDeque::new());
        let acc = (c.extends.iter()).try_fold(acc, class_type_decl)?;
        let acc = (c.implements.iter()).try_fold(acc, class_type_decl)?;
        let acc = (c.uses.iter()).try_fold(acc, class_type_decl)?;
        let acc = (c.xhp_attr_uses.iter()).try_fold(acc, class_type_decl)?;
        let acc = (c.req_extends.iter()).try_fold(acc, class_type_decl)?;
        let acc = (c.req_implements.iter()).try_fold(acc, class_type_decl)?;
        // Aast.enum_includes_map ~f:(fun et -> et.te_includes) c.sc_enum_type
        let enum_includes: &[Ty<R>] = match &c.enum_type {
            None => &[],
            Some(et) => &et.includes,
        };
        let (parents, errs) = (enum_includes.iter()).try_fold(acc, class_type_decl)?;
        Ok((parents, errs.into()))
    }

    // note(sf, 2022-03-02): c.f. Decl_folded_class.class_decl_if_missing
    //
    // `self.store` is the store of folded classes (`Decl_store`), whose
    // member heaps do not exist here.
    fn class_decl_if_missing(
        &self,
        stack: &IndexSet<TypeName>,
        class_name: TypeName,
    ) -> Result<Option<Arc<FoldedClass<R>>>> {
        match self.store.get(class_name).map_err(Error::Store)? {
            Some(decl) => Ok(Some(decl)),
            None => match self.shallow_decl_provider.get_class(class_name)? {
                None => Ok(None),
                Some(shallow_class) => {
                    let class_ = self.declare_class_and_parents(stack, &shallow_class)?;
                    self.store
                        .insert(class_name, Arc::clone(&class_))
                        .map_err(Error::Store)?;
                    Ok(Some(class_))
                }
            },
        }
    }
}
