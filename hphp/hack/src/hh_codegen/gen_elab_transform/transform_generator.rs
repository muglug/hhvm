// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

#![allow(unused)]

use proc_macro2::TokenStream;
use quote::quote;

use super::Context;
use super::Direction;
use super::contains_transform_attr;
use crate::common::to_snake;

pub fn r#gen(ctx: &Context) -> TokenStream {
    let manual_impls = gen_manual_impls();
    let impls: Vec<_> = ctx
        .type_structures()
        .map(|s| gen_transform_and_traverse(ctx, s))
        .collect();

    quote! {
        #![allow(unused_variables)]
        #![allow(unused_braces)]
        #![allow(clippy::match_single_binding)]

        use std::ops::ControlFlow::Break;

        use oxidized::nast::*;

        use crate::env::Env;
        use crate::Pass;

        pub trait Transform {
            #[inline(always)]
            fn transform(
                &mut self,
                env: &Env,
                pass: &mut (impl Pass + Clone),
            ) {
                stack_limit::maybe_grow(|| self.traverse(env, pass));
            }
            #[inline(always)]
            fn traverse(
                &mut self,
                env: &Env,
                pass: &mut (impl Pass + Clone),
            ) {}
            // `self.transform(env, &mut pass.clone())`: a child that has
            // siblings after it gets its own copy of the passes (the
            // last child is given the copy of its parent, which is not
            // used after it). The leaves make no copy.
            #[inline(always)]
            fn transform_copy(
                &mut self,
                env: &Env,
                pass: &mut (impl Pass + Clone),
            ) {
                self.transform(env, &mut pass.clone())
            }
        }

        // The leaves: nothing to visit, and no stack check
        // (`stack_limit::maybe_grow`) for them.
        impl Transform for () {
            #[inline(always)]
            fn transform(&mut self, env: &Env, pass: &mut (impl Pass + Clone)) {}
            #[inline(always)]
            fn transform_copy(&mut self, env: &Env, pass: &mut (impl Pass + Clone)) {}
        }
        impl Transform for bool {
            #[inline(always)]
            fn transform(&mut self, env: &Env, pass: &mut (impl Pass + Clone)) {}
            #[inline(always)]
            fn transform_copy(&mut self, env: &Env, pass: &mut (impl Pass + Clone)) {}
        }
        impl Transform for isize {
            #[inline(always)]
            fn transform(&mut self, env: &Env, pass: &mut (impl Pass + Clone)) {}
            #[inline(always)]
            fn transform_copy(&mut self, env: &Env, pass: &mut (impl Pass + Clone)) {}
        }
        impl Transform for String {
            #[inline(always)]
            fn transform(&mut self, env: &Env, pass: &mut (impl Pass + Clone)) {}
            #[inline(always)]
            fn transform_copy(&mut self, env: &Env, pass: &mut (impl Pass + Clone)) {}
        }
        impl Transform for bstr::BString {
            #[inline(always)]
            fn transform(&mut self, env: &Env, pass: &mut (impl Pass + Clone)) {}
            #[inline(always)]
            fn transform_copy(&mut self, env: &Env, pass: &mut (impl Pass + Clone)) {}
        }
        impl Transform for oxidized::pos::Pos {
            #[inline(always)]
            fn transform(&mut self, env: &Env, pass: &mut (impl Pass + Clone)) {}
            #[inline(always)]
            fn transform_copy(&mut self, env: &Env, pass: &mut (impl Pass + Clone)) {}
        }
        impl Transform for oxidized::file_info::Mode {
            #[inline(always)]
            fn transform(&mut self, env: &Env, pass: &mut (impl Pass + Clone)) {}
            #[inline(always)]
            fn transform_copy(&mut self, env: &Env, pass: &mut (impl Pass + Clone)) {}
        }
        impl Transform for oxidized::namespace_env::Env {
            #[inline(always)]
            fn transform(&mut self, env: &Env, pass: &mut (impl Pass + Clone)) {}
            #[inline(always)]
            fn transform_copy(&mut self, env: &Env, pass: &mut (impl Pass + Clone)) {}
        }

        #(#manual_impls)*

        #(#impls)*
    }
}

fn gen_transform_and_traverse(ctx: &Context, mut s: synstructure::Structure<'_>) -> TokenStream {
    // By default, if you are deriving an impl of trait Foo for generic type
    // X<T>, synstructure will add Foo as a bound not only for the type
    // parameter T, but also for every type which appears as a field in X. This
    // is not necessary for our use case--we can just require that the type
    // parameters implement our trait.
    s.add_bounds(synstructure::AddBounds::Generics);

    // We are mutating the AST and need &mut references to fields.
    s.bind_with(|_bi| synstructure::BindStyle::RefMut);

    // Cleaner generated syntax for `gen impl` hygiene. Not supported by Rust
    // versions before 1.37. We don't really need the hygiene at all (the quote
    // we pass to `gen_impl` doesn't define any items other than the trait
    // impl), but I don't think there's a way to turn it off.
    s.underscore_const(true);

    // If the type is marked opaque, generate a no-op Transform impl.
    if contains_transform_attr(&s.ast().attrs, "opaque") {
        return s.gen_impl(quote! {
            gen impl Transform for @Self {}
        });
    }

    // Don't visit fields or variants marked opaque.
    s.filter(|bi| !contains_transform_attr(&bi.ast().attrs, "opaque"));
    s.filter_variants(|v| !contains_transform_attr(v.ast().attrs, "opaque"));

    let ty_name = s.ast().ident.to_string();
    let transform_body = gen_transform_body(
        &super::gen_pass_method_name(&ty_name, Direction::TopDown),
        &super::gen_pass_method_name(&ty_name, Direction::BottomUp),
        quote!(self),
        quote!(stack_limit::maybe_grow(|| self.traverse(env, pass))),
    );
    let traverse_body = gen_traverse_body(&ty_name, &s);
    let ty_name = quote::format_ident!("{}", ty_name);

    quote! {
        impl Transform for #ty_name {
            fn transform(
                &mut self,
                env: &Env,
                pass: &mut (impl Pass + Clone),
            ) {
                #transform_body
            }

            fn traverse(
                &mut self,
                env: &Env,
                pass: &mut (impl Pass + Clone),
            ) {
                match *self { #traverse_body }
            }
        }
    }
}

fn gen_traverse_body(ty_name: &str, s: &synstructure::Structure<'_>) -> TokenStream {
    s.variants()
        .iter()
        .map(|v| gen_variant_traverse(ty_name, v))
        .chain(std::iter::once(if s.omitted_variants() {
            quote!(_ => {})
        } else {
            quote!()
        }))
        .collect()
}

fn gen_variant_traverse(ty_name: &str, v: &synstructure::VariantInfo<'_>) -> TokenStream {
    if !contains_transform_attr(v.ast().attrs, "explicit") {
        // (`v.each`, with the last binding told apart.)
        let pat = v.pat();
        let n = v.bindings().len();
        let fields = v
            .bindings()
            .iter()
            .enumerate()
            .map(|(i, bi)| gen_fld_traverse(ty_name, bi, i + 1 == n));
        return quote! { #pat => { #({ #fields })* } };
    }
    let pass_method_td =
        super::gen_pass_ctor_method_name(ty_name, v.ast().ident.to_string(), Direction::TopDown);
    let pass_method_bu =
        super::gen_pass_ctor_method_name(ty_name, v.ast().ident.to_string(), Direction::BottomUp);
    if v.ast().fields.len() != 1 {
        panic!("transform.explicit only supports variants with 1 field")
    }
    v.each(|bi| {
        gen_transform_body_explicit(
            &pass_method_td,
            &pass_method_bu,
            quote!(#bi),
            quote! { #bi.transform(env, &mut td_pass) },
        )
    })
}

/// The visit of the field `bi`; `last`: no field is visited after it, so it
/// is given the passes of the parent (no longer used) instead of a copy.
fn gen_fld_traverse(ty_name: &str, bi: &synstructure::BindingInfo<'_>, last: bool) -> TokenStream {
    if !contains_transform_attr(&bi.ast().attrs, "explicit") {
        return if last {
            quote! { #bi.transform(env, pass) }
        } else {
            quote! { #bi.transform_copy(env, pass) }
        };
    }
    // (In the block of `gen_transform_body_explicit`, `pass` is a copy that
    // is not used after the field.)
    let transform_bi = quote! { #bi.transform(env, pass) };
    // Since Transform is a trait, we can't have special implementations
    // of Transform::transform for fields. Instead, we inline the
    // transform_fld function here (in the Transform::traverse body).
    let pass_method_td = super::gen_pass_fld_method_name(
        ty_name,
        (bi.ast().ident.as_ref())
            .map(|i| i.to_string())
            .unwrap_or_default(),
        Direction::TopDown,
    );
    let pass_method_bu = super::gen_pass_fld_method_name(
        ty_name,
        (bi.ast().ident.as_ref())
            .map(|i| i.to_string())
            .unwrap_or_default(),
        Direction::BottomUp,
    );
    gen_transform_body_explicit(&pass_method_td, &pass_method_bu, quote!(#bi), transform_bi)
}

fn gen_transform_body(
    pass_method_td: &syn::Ident,
    pass_method_bu: &syn::Ident,
    elem: TokenStream,
    recurse: TokenStream,
) -> TokenStream {
    quote! {
        let mut in_pass = pass.clone();
        if let Break(..) = pass.#pass_method_td(env, #elem) {
            return;
        }
        #recurse;
        let _ = in_pass.#pass_method_bu(env, #elem);
    }
}

fn gen_transform_body_explicit(
    pass_method_td: &syn::Ident,
    pass_method_bu: &syn::Ident,
    elem: TokenStream,
    recurse: TokenStream,
) -> TokenStream {
    let body = gen_transform_body(pass_method_td, pass_method_bu, elem, recurse);
    quote! {
        {
            let pass = &mut pass.clone();
            #body
        }
    }
}

fn gen_manual_impls() -> Vec<TokenStream> {
    // A child among others gets its own copy of the passes; the last one
    // (or the only one) gets the passes of its parent, not used after it.
    let transform = quote!(transform(env, pass));
    let transform_copy = quote!(transform_copy(env, pass));

    // The wrappers of one value have no pass method of their own: they
    // give the value what they are given (no copy, no stack check).
    #[rustfmt::skip]
    let wrappers = vec![
        (vec!["T"], quote!(&mut T), quote!((**self)), None),
        (vec!["T"], quote!(Box<T>), quote!((**self)), None),
        (vec!["T"], quote!(oxidized::lazy::Lazy<T>), quote!(self.0), None),
        (vec!["T"], quote!(Option<T>), quote!(x), Some(quote!(Some(x) = self))),
        (vec!["T"], quote!(std::sync::Arc<T>), quote!(x),
         Some(quote!(Some(x) = std::sync::Arc::get_mut(self)))),
        (vec!["T"], quote!(std::rc::Rc<T>), quote!(x),
         Some(quote!(Some(x) = std::rc::Rc::get_mut(self)))),
    ];

    #[rustfmt::skip]
    let manual_impls = vec![
        (vec!["T"], quote!(Vec<T>), quote! {
            if let Some((last, init)) = self.split_last_mut() {
                for x in init {
                    x.#transform_copy;
                }
                last.#transform;
            }
        }, Some(quote!(self.is_empty()))),
        (vec!["K", "V"], quote!(std::collections::BTreeMap<K, V>), quote! {
            let mut values = self.values_mut().peekable();
            while let Some(x) = values.next() {
                if values.peek().is_some() {
                    x.#transform_copy;
                } else {
                    x.#transform;
                }
            }
        }, Some(quote!(self.is_empty()))),
        (vec!["T1", "T2"], quote!((T1, T2)), quote! {
            self.0.#transform_copy;
            self.1.#transform;
        }, None),
        (vec!["T1", "T2", "T3"], quote!((T1, T2, T3)), quote! {
            self.0.#transform_copy;
            self.1.#transform_copy;
            self.2.#transform;
        }, None),
        (vec!["T1", "T2", "T3", "T4"], quote!((T1, T2, T3, T4)), quote! {
            self.0.#transform_copy;
            self.1.#transform_copy;
            self.2.#transform_copy;
            self.3.#transform;
        }, None),
        (vec!["T1", "T2", "T3", "T4", "T5"], quote!((T1, T2, T3, T4, T5)), quote! {
            self.0.#transform_copy;
            self.1.#transform_copy;
            self.2.#transform_copy;
            self.3.#transform_copy;
            self.4.#transform;
        }, None),
    ];

    let either = quote! {
        impl<L, R> Transform for itertools::Either<L, R>
        where
            L: Transform,
            R: Transform,
        {
            #[inline(always)]
            fn transform(&mut self, env: &Env, pass: &mut (impl Pass + Clone)) {
                self.traverse(env, pass)
            }
            fn traverse(&mut self, env: &Env, pass: &mut (impl Pass + Clone)) {
                match self {
                    Self::Left(x) => x.#transform,
                    Self::Right(x) => x.#transform,
                }
            }
            #[inline(always)]
            fn transform_copy(&mut self, env: &Env, pass: &mut (impl Pass + Clone)) {
                match self {
                    Self::Left(x) => x.#transform_copy,
                    Self::Right(x) => x.#transform_copy,
                }
            }
        }
    };

    wrappers
        .into_iter()
        .map(|(tp, ty, inner, binding)| gen_wrapper_impl(tp, ty, inner, binding))
        .chain(std::iter::once(either))
        .chain(
            manual_impls
                .into_iter()
                .map(|(tp, ty, body, empty)| gen_manual_impl(tp, ty, body, empty)),
        )
        .collect()
}

/// A wrapper of `inner` (bound by `if let #binding`, when given).
fn gen_wrapper_impl(
    typarams: Vec<&'static str>,
    ty: TokenStream,
    inner: TokenStream,
    binding: Option<TokenStream>,
) -> TokenStream {
    let typarams: Vec<_> = typarams
        .into_iter()
        .map(|tp| quote::format_ident!("{}", tp))
        .collect();
    let call = |method: TokenStream| match &binding {
        None => quote!(#inner.#method(env, pass)),
        Some(binding) => quote! {
            if let #binding {
                #inner.#method(env, pass)
            }
        },
    };
    let transform = call(quote!(transform));
    let transform_copy = call(quote!(transform_copy));
    quote! {
        impl<#(#typarams,)*> Transform for #ty
        where
            #(#typarams: Transform,)*
        {
            #[inline(always)]
            fn transform(&mut self, env: &Env, pass: &mut (impl Pass + Clone)) {
                #transform
            }
            fn traverse(&mut self, env: &Env, pass: &mut (impl Pass + Clone)) {
                #transform
            }
            #[inline(always)]
            fn transform_copy(&mut self, env: &Env, pass: &mut (impl Pass + Clone)) {
                #transform_copy
            }
        }
    }
}

/// `empty`: when it holds, the value has nothing to visit (no copy of the
/// passes for it).
fn gen_manual_impl(
    typarams: Vec<&'static str>,
    ty: TokenStream,
    traverse_body: TokenStream,
    empty: Option<TokenStream>,
) -> TokenStream {
    let transform_copy = empty.map(|empty| {
        quote! {
            #[inline(always)]
            fn transform_copy(&mut self, env: &Env, pass: &mut (impl Pass + Clone)) {
                if !#empty {
                    self.transform(env, &mut pass.clone())
                }
            }
        }
    });
    let typarams: Vec<_> = typarams
        .into_iter()
        .map(|tp| quote::format_ident!("{}", tp))
        .collect();
    quote! {
        impl<#(#typarams,)*> Transform for #ty
        where
            #(#typarams: Transform,)*
        {
            fn traverse(
                &mut self,
                env: &Env,
                pass: &mut (impl Pass + Clone),
            ) {
                #traverse_body
            }
            #transform_copy
        }
    }
}
