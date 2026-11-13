// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/ide_service/ide_hover.ml`.
//!
//! Owned by **F2** (plan §7.3).

use std::sync::Arc;

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::pos_or_decl::PosOrDecl;

use crate::ctx::R;
use crate::decl_entry;
use crate::decl_provider;
use crate::derive_type_instantiation;
use crate::file_content::position;
use crate::folded_class;
use crate::hover_service;
use crate::hover_service::HoverInfo;
use crate::lsp::MarkedString;
use crate::markdown_lite;
use crate::pos;
use crate::pos::Pos;
use crate::pos_or_decl;
use crate::provider_context;
use crate::server_docblock_at;
use crate::server_identify_function;
use crate::server_infer_type;
use crate::symbol_definition as sd;
use crate::symbol_occurrence as so;
use crate::tast;
use crate::tast_env;
use crate::tast_provider;
use crate::typing_defs;
use crate::utils;

mod attr_docs;

type Occ = so::T<Pos>;
type Def = sd::T<Pos>;

/// `ty::decl::Ty`, the decl types of the folded decls.
type DeclTy = ty::decl::Ty<R>;

/// `Typing_defs.decl_tparam`
type DeclTparam = ty::decl::Tparam<R, DeclTy>;

/// When we get a Class occurrence and a Method occurrence, that means that the
/// user is hovering over an invocation of the constructor, and would therefore only
/// want to see information about the constructor, rather than getting both the
/// class and constructor back in the hover.
fn filter_class_and_constructor(results: Vec<(Occ, HoverInfo)>) -> Vec<HoverInfo> {
    let has_class = results.iter().any(|r| so::is_class(&r.0));
    let has_constructor = results.iter().any(|r| so::is_constructor(&r.0));
    if has_class && has_constructor {
        results
            .into_iter()
            .filter(|r| so::is_constructor(&r.0))
            .map(|r| r.1)
            .collect()
    } else {
        results.into_iter().map(|r| r.1).collect()
    }
}

fn docs_url_markdown(name: &str, url: &str) -> String {
    format!(
        "See the [documentation for {}]({}).",
        markdown_lite::md_codify(utils::strip_ns(name)),
        url
    )
}

fn typedef_docs_url(ctx: &provider_context::T, name: &str) -> Option<String> {
    let qualified_name = format!("\\{}", name);
    let decl = decl_entry::to_option(decl_provider::get_typedef(None, ctx, &qualified_name))?;
    let url = decl.docs_url.as_ref()?;
    Some(docs_url_markdown(name, url))
}

/// If [classish_name] (or any of its parents) has a documentation URL,
/// return the docs of the closest type.
fn classish_docs_url(ctx: &provider_context::T, classish_name: &str) -> Option<String> {
    let docs_url = |name: &str| match decl_provider::get_class(None, ctx, name) {
        decl_entry::T::Found(decl) => folded_class::get_docs_url(&decl),
        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => None,
    };
    let qualified_name = format!("\\{}", classish_name);
    let ancestors = match decl_provider::get_class(None, ctx, &qualified_name) {
        decl_entry::T::Found(decl) => folded_class::all_ancestor_names(&decl),
        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => vec![],
    };
    std::iter::once(qualified_name)
        .chain(ancestors)
        .find_map(|ancestor| docs_url(&ancestor).map(|url| docs_url_markdown(&ancestor, &url)))
}

fn docs_url(ctx: &provider_context::T, def: &Def) -> Option<String> {
    match &def.kind {
        sd::Kind::Classish { .. } => classish_docs_url(ctx, &def.name),
        sd::Kind::Typedef => typedef_docs_url(ctx, &def.name),
        sd::Kind::Function
        | sd::Kind::Member { .. }
        | sd::Kind::GlobalConst
        | sd::Kind::LocalVar
        | sd::Kind::TypeVar
        | sd::Kind::Param
        | sd::Kind::Module => None,
    }
}

fn make_hover_doc_block(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    occurrence: &Occ,
    def_opt: Option<&Def>,
) -> Vec<String> {
    match def_opt {
        Some(def) if occurrence.is_declaration.is_none() => {
            // The docblock is useful at the call site, but it's redundant at
            // the definition site.
            let base_class_name = so::enclosing_class(occurrence);
            let doc_block_hover: Vec<String> =
                server_docblock_at::go_comments_for_symbol_ctx(ctx, entry, def, base_class_name.as_deref())
                    .into_iter()
                    .collect();
            match docs_url(ctx, def) {
                Some(info) => std::iter::once(info).chain(doc_block_hover).collect(),
                None => doc_block_hover,
            }
        }
        None | Some(_) => vec![],
    }
}

/// Given a function/method call receiver, find the position of the
/// definition site.
fn callee_def_pos(ctx: &provider_context::T, recv: &so::Receiver) -> Option<PosOrDecl> {
    match recv {
        so::Receiver::FunctionReceiver(fun_name) => {
            let f = decl_entry::to_option(decl_provider::get_fun(None, ctx, fun_name));
            f.map(|fe| PosOrDecl::from(fe.pos.clone()))
        }
        so::Receiver::MethodReceiver { cls_name, .. } => {
            let c = decl_entry::to_option(decl_provider::get_class(None, ctx, cls_name));
            c.map(|c| folded_class::pos(&c))
        }
    }
}

/// Return the name of the [n]th parameter in [params], handling
/// variadics and splat parameters correctly.
/// For splat parameters, we suffix [i] on the parameter name to indicate
/// that it's the i'th element of the splat tuple.
fn nth_param_name(params: &[tast::FunParam], n: isize) -> Option<String> {
    let len = params.len() as isize;
    let param = if n >= len {
        match params.last() {
            Some(param)
                if crate::aast_utils::is_param_variadic(param)
                    || crate::aast_utils::is_param_splat(param) =>
            {
                Some(param)
            }
            _ => None,
        }
    } else if n < 0 {
        // `List.nth` of a negative index
        None
    } else {
        params.get(n as usize)
    };
    param.map(|param| {
        if crate::aast_utils::is_param_variadic(param) {
            format!("...{}", param.name)
        } else if crate::aast_utils::is_param_splat(param) {
            format!("{}[{}]", param.name, n - len + 1)
        } else {
            param.name.clone()
        }
    })
}

/// Return the name of the [n]th parameter of function [fun_name].
fn nth_fun_param(tast: &[tast::Def], fun_name: &str, n: isize) -> Option<String> {
    tast.iter().find_map(|def| match def {
        aast::Def::Fun(fd) => {
            if fun_name == fd.name.1 {
                nth_param_name(&fd.fun.params, n)
            } else {
                None
            }
        }
        _ => None,
    })
}

/// Return the name of the [n]th parameter of this method.
fn nth_meth_param(tast: &[tast::Def], cls_name: &str, meth_name: &str, is_static: bool, arg_n: isize) -> Option<String> {
    let class_methods: &[tast::Method_] = tast
        .iter()
        .find_map(|def| match def {
            aast::Def::Class(c) => {
                if cls_name == c.name.1 {
                    Some(c.methods.as_slice())
                } else {
                    None
                }
            }
            _ => None,
        })
        .unwrap_or(&[]);
    let class_method = class_methods
        .iter()
        .find(|m| meth_name == m.name.1 && is_static == m.static_);
    match class_method {
        Some(m) => nth_param_name(&m.params, arg_n),
        None => None,
    }
}

fn nth_param(ctx: &provider_context::T, recv: &so::Receiver, i: isize) -> Option<String> {
    match callee_def_pos(ctx, recv) {
        Some(pos) => {
            let path = pos_or_decl::filename(&pos);
            let (ctx, entry) = provider_context::add_entry_if_missing(ctx, path);
            let tast_provider::ComputeTastResult { tast, .. } =
                tast_provider::compute_tast_quarantined(&ctx, &entry);
            let tast = &tast.under_normal_assumptions;
            match recv {
                so::Receiver::FunctionReceiver(fun_name) => nth_fun_param(tast, fun_name, i),
                so::Receiver::MethodReceiver {
                    cls_name,
                    meth_name,
                    is_static,
                } => nth_meth_param(tast, cls_name, meth_name, *is_static, i),
            }
        }
        None => None,
    }
}

fn make_hover_const_definition(entry: &provider_context::Entry, def_opt: Option<&Def>) -> Option<String> {
    def_opt.map(|def| {
        let content = provider_context::read_file_contents_exn(entry);
        pos::get_text_from_pos(&String::from_utf8_lossy(&content), &def.span)
    })
}

/// Return a markdown description of built-in Hack attributes.
fn make_hover_attr_docs(name: &str) -> Vec<String> {
    let find = |map: &[(&str, &'static str)]| {
        map.iter().find(|(k, _)| *k == name).map(|(_, doc)| doc.to_string())
    };
    find(attr_docs::AS_MAP)
        .or_else(|| find(attr_docs::SYSTEMLIB_MAP))
        .into_iter()
        .collect()
}

const PURE_CONTEXT_INFO: &str = "This function has an empty context list, so it has no capabilities.\nIt may only read properties, access constants, or call other pure functions.";

const HH_FIXME_INFO: &str = "`HH_FIXME[N]` disables type checker error N on the next line. It does
not change runtime behavior.

**`HH_FIXME` is almost always a bad idea**. You might get an
exception, or you might get an unexpected value. Even scarier, you
might cause an exception in a totally different part of the codebase.

```
/* HH_FIXME[4110] My reason here */
takes_num(\"x\") + takes_num(\"y\");
```

In this example, the type checker will accept the code, but the code
will still crash when you run it (`TypeHintViolationException` when
calling `takes_num`).

Note that `HH_FIXME` applies to all occurrences of the error on the
next line.

## You can fix it!

It is always possible to write code without `HH_FIXME`. This usually
requires changing type signatures and some refactoring. Your code will
be more reliable, the type checker can help you, and future changes
will be less scary.

See also `HH\\FIXME\\UNSAFE_CAST()`, which is still bad, but much more
precise.";

const HH_IGNORE_INFO: &str = "`HH_IGNORE[N]` silences type checker warning N on the next line. It does
not change runtime behavior.

Note that `HH_IGNORE` applies to all occurrences of the warning on the
next line.";

fn keyword_info(khi: &so::KeywordWithHoverDocs) -> String {
    const AWAIT_EXPLANATION: &str = concat!(
        "\n\nThis does not give you threads. Only one function is running at any point in time.",
        " Instead, the runtime may switch to another function at an `await` expression, and come back to this function later.",
        "\n\nThis allows data fetching (e.g. database requests) to happen in parallel."
    );
    use so::KeywordWithHoverDocs as K;
    match khi {
        K::Class => ["A `class` contains methods, properties and constants that together solve a problem."].concat(),
        K::Interface => ["An `interface` defines signatures for methods that classes must implement."].concat(),
        K::Trait => ["A `trait` provides methods and properties that can be `use`d in classes.", "\n\nTraits are often used to provide default implementations for methods declared in an `interface`.", "\n\nWhen in doubt, use a class rather than a trait. You only need a trait when you want the same method in multiple classes that don't inherit from each other."].concat(),
        K::Enum => ["An `enum` is a fixed set of string or integer values.", "\n\nYou can use `switch` with an `enum` and the type checker will ensure you handle every possible value."].concat(),
        K::EnumClass => ["An `enum class` is a fixed set of values that can be used as typed constants.", "\n\nEnum classes enable you to write generic getter and setter methods.", "\n\n```
enum class PersonFields: BaseField {
  Field<string> name = Field::string();
  Field<string> email = Field::string();
  Field<int> age = Field::int();
}
```", "\n\nYou can refer to items within an enum class by name (using the `#` syntax), and Hack knows the exact type.", "\n\n```
function person_get(
  Person $p,
  HH\\EnumClass\\Label<PersonFields, Field<T>> $field_name
  ): T {
  // ... implementation here ...
}

person_get($a_person, #email); // string
```", "\n\nSee also `HH\\EnumClass\\Label` and `HH\\MemberOf`."].concat(),
        K::Type => ["A `type` is an alias for another type.", "\n\n`type` aliases are transparent, so you can use the original type and its alias interchangeably.", "\n\nSee also `newtype` for opaque type aliases."].concat(),
        K::Newtype => ["A `newtype` is a type alias that is opaque.", "\n\nInside the current file, code can see the underlying type. In all other files, code cannot see the underlying type.", " This enables you to hide implementation details.", "\n\nSee also `type` for transparent type aliases."].concat(),
        K::FinalOnClass => ["A `final` class cannot be extended by other classes.\n\nTo restrict which classes can extend this, use `<<__Sealed()>>`."].concat(),
        K::FinalOnMethod => ["A `final` method cannot be overridden in child classes."].concat(),
        K::AbstractOnClass => ["An `abstract` class can only contain `static` methods and `abstract` instance methods.\n\n", "`abstract` classes cannot be instantiated directly. You can only use `new` on child classes that aren't `abstract`."].concat(),
        K::AbstractOnMethod => ["An `abstract` method has a signature but no body. Child classes must provide an implementation."].concat(),
        K::ExtendsOnClass => ["Extending a class allows your class to inherit methods from another class.", "\n\nInheritance allows your class to:", "\n * Reuse methods from the parent class", "\n * Call `protected` methods on the parent class", "\n * Be passed as a parameter whenever an instance of the parent class is expected", "\n\nHack does not support multiple inheritance on classes. If you need to share functionality between", " unrelated classes, use traits."].concat(),
        K::ExtendsOnInterface => ["Extending an interface allows your interface to include methods from other interfaces.", "\n\nAn interface can extend multiple interfaces."].concat(),
        K::ReadonlyOnMethod => ["A `readonly` method treats `$this` as `readonly`."].concat(),
        K::ReadonlyOnExpression | K::ReadonlyOnParameter => ["A `readonly` value is a reference that cannot modify the underlying value."].concat(),
        K::ReadonlyOnReturnType => ["This function/method may return a `readonly` value."].concat(),
        K::XhpAttribute => ["`attribute` declares which attributes are permitted on the current XHP class.", "\n\nAttributes are optional unless marked with `@required`."].concat(),
        K::XhpChildren => ["`children` declares which XHP types may be used as children when creating instances of this class.", "\n\nFor example, `children (:p)+` means that users may write `<my-class><p>hello</p><p>world</p></my_class>`.", "\n\n**`children` is not enforced by the type checker**, but an XHP framework can choose to validate it at runtime."].concat(),
        K::ConstGlobal => ["A `const` is a global constant."].concat(),
        K::ConstOnClass => ["A class constant.", "\n\nClass constants have public visibility, so you can access `MyClass::MY_CONST` anywhere."].concat(),
        K::ConstType => ["A `const type` declares a type constant inside a class. You can refer to type constants in signatures with `this::TMyConstType`.", "\n\nType constants are also a form of generics.", "\n\n```", "\nabstract class Pet {", "\n  abstract const type TFood;", "\n}", "\n", "\nclass Cat extends Pet {", "\n  const type TFood = Fish;", "\n}", "\n```", "\n\nType constants are static, not per-instance. All instances of `Cat` have the same value for `TFood`, whereas `MyObject<T>` generics can differ between instances.", "\n\nThis enables type constants to be used outside the class, e.g. `Cat::TFood`."].concat(),
        K::StaticOnMethod => ["A static method can be called without an instance, e.g. `MyClass::my_method()`."].concat(),
        K::StaticOnProperty => ["A static property is shared between all instances of a class. It can be accessed with `MyClass::$myProperty`."].concat(),
        K::Use => ["Include all the items (methods, properties etc) from a trait in this class/trait.", "\n\nIf this class/trait already has an item of the same name, the trait item is not copied."].concat(),
        K::FunctionOnMethod => ["A `function` inside a class declares a method."].concat(),
        K::FunctionGlobal => ["A standalone global function."].concat(),
        K::Async => ["An `async` function can use `await` to get results from other `async` functions. You may still return plain values, e.g. `return 1;` is permitted in an `Awaitable<int>` function.", AWAIT_EXPLANATION].concat(),
        K::AsyncBlock => ["An `async` block is syntactic sugar for an `async` lambda that is immediately called.", "\n\n```", "\n$f = async { return 1; };", "\n// Equivalent to:", "\n$f = (async () ==> { return 1; })();", "\n```", "\n\nThis is useful when building more complex async expressions.", "\n\n```", "\nconcurrent {", "\n  $group_name = await async {", "\n    return $group is null ? '' : await $group->genName();", "\n  };", "\n  await async {", "\n    try {", "\n      await gen_log_request();", "\n    } catch (LogRequestFailed $_) {}", "\n  }", "\n}", "\n```"].concat(),
        K::Await => ["`await` waits for the result of an `Awaitable<_>` value.", AWAIT_EXPLANATION].concat(),
        K::Concurrent => ["`concurrent` allows you to `await` multiple values at once. This is similar to `Vec\\map_async`, but `concurrent` allows awaiting unrelated values of different types."].concat(),
        K::Public => ["A `public` method or property has no restrictions on access. It can be accessed from any part of the codebase.", "\n\nSee also `protected` and `private`."].concat(),
        K::Protected => ["A `protected` method or property can only be accessed from methods defined on the current class, or methods on subclasses.", "\n\nIf the current class `use`s a trait, the trait methods can also access `protected` methods and properties.", "\n\nSee also `public` and `private`."].concat(),
        K::Private => ["A `private` method or property can only be accessed from methods defined on the current class.", "\n\nPrivate items can be accessed on any instance of the current class. ", "For example, if you have a private property `name`, you can access both `$this->name` and `$other_instance->name`.", "\n\nSee also `public` and `protected`."].concat(),
        K::Internal => ["An `internal` symbol can only be accessed from files that belong to the current `module`."].concat(),
        K::ModuleInModuleDeclaration => ["`new module Foo {}` defines a new module but does not associate any code with it.", "\n\nYou must use `module Foo;` to mark all the definitions in a given file as associated with the `Foo` module and enable them to use `internal`."].concat(),
        K::ModuleInModuleMembershipDeclaration => ["`module Foo;` marks all the definitions in the current file as associated with the `Foo` module, and enables them to use `internal`.", "\n\nYou must also define this module with `new module Foo {}` inside or outside this file."].concat(),
    }
}

/// For strings like "preffix::suffix", return "prefix", otherwise
/// return the full string.
fn split_class_name(full_name: &str) -> &str {
    match full_name.split_once(':') {
        Some((class_name, _member)) => class_name,
        None => full_name,
    }
}

fn make_fun_defined_in_section(def_opt: Option<&Def>) -> Option<String> {
    let def = def_opt?;
    let abs_name = format!("\\{}", sd::full_name(def));
    if sn::pseudo_functions::is_pseudo_function(&abs_name) {
        None
    } else {
        match utils::strip_hh_lib_ns(&abs_name).rsplit_once('\\') {
            Some((namespace, _)) if !namespace.is_empty() => {
                Some(format!("Defined in namespace `{}`", namespace))
            }
            _ => None,
        }
    }
}

/// Return the decl type of a class member or function represented by a SymbolDefinition.t.
/// If passed a class member, also return the type parameters of that class
fn get_decl_ty(
    ctx: &provider_context::T,
    def_opt: Option<&Def>,
    occurrence: &so::Kind,
) -> (Option<Vec<DeclTparam>>, Option<DeclTy>) {
    let go = || -> Option<(Option<Vec<DeclTparam>>, Option<DeclTy>)> {
        let def = def_opt?;
        let sd::T {
            name, kind, modifiers, ..
        } = def;
        match kind {
            sd::Kind::Member {
                class_name,
                member_kind,
            } => {
                let cls = decl_entry::to_option(decl_provider::get_class(None, ctx, &utils::add_ns(class_name)))?;
                let is_static = sd::is_static(modifiers);
                let member_ty = match member_kind {
                    sd::MemberKind::Method => folded_class::get_any_method(is_static, &cls, name)
                        .map(|member| (*member.ce_type).clone()),
                    sd::MemberKind::Property => {
                        let property = if is_static {
                            folded_class::get_sprop(&cls, name)
                        } else {
                            folded_class::get_prop(&cls, name)
                        };
                        property.map(|property| (*property.ce_type).clone())
                    }
                    sd::MemberKind::ClassConst => {
                        folded_class::get_const(&cls, name).map(|class_const| class_const.ty.clone())
                    }
                    sd::MemberKind::TypeConst => None,
                };
                Some((Some(folded_class::tparams(&cls)), member_ty))
            }
            sd::Kind::Function => {
                let func = decl_entry::to_option(decl_provider::get_fun(None, ctx, &utils::add_ns(name)))?;
                Some((None, Some(func.ty.clone())))
            }
            sd::Kind::Classish { .. } => match occurrence {
                so::Kind::Method(_, construct_name) if construct_name == sn::members::__CONSTRUCT => {
                    // If the constructor is not explicitly defined, then the SymbolDefinition.t
                    // will be a Classish instead of Method
                    let cls = decl_entry::to_option(decl_provider::get_class(None, ctx, &utils::add_ns(name)))?;
                    let ty = match folded_class::construct(&cls).0 {
                        Some(ce) => (*ce.ce_type).clone(),
                        None => default_construct_decl(),
                    };
                    Some((Some(folded_class::tparams(&cls)), Some(ty)))
                }
                _ => None,
            },
            _ => None,
        }
    };
    go().unwrap_or((None, None))
}

/// `Typing_make_type.default_construct Typing_reason.none` at the decl phase.
fn default_construct_decl() -> DeclTy {
    use ty::decl;
    use ty::reason::Reason as _;
    let r = R::none();
    let ft = decl::FunType {
        tparams: Box::new([]),
        where_constraints: Box::new([]),
        params: Box::new([]),
        implicit_params: decl::ty::FunImplicitParams {
            capability: decl::ty::Capability::CapDefaults(r.pos().clone()),
        },
        // `Typing_defs_flags.Fun.make Ast_defs.FSync` with every flag false
        flags: oxidized::typing_defs_flags::FunTypeFlags::empty(),
        ret: DeclTy::void(r.clone()),
        instantiated: true,
    };
    DeclTy::new(r, decl::Ty_::Tfun(Box::new(ft)))
}

fn make_hack_marked_code(s: String) -> MarkedString {
    MarkedString::MarkedCode("hack".to_string(), s)
}

/// Make the 'instantiation' section of the hover card, something like:
///
/// ```text
/// ---
/// Instantiation:
/// ```
///   T = int;
///   Ta = string;
/// ```
/// ```
fn make_instantiation_section(
    env: &tast_env::Env,
    subst: &derive_type_instantiation::instantiation::T,
) -> Option<Vec<MarkedString>> {
    if derive_type_instantiation::instantiation::is_empty(subst) {
        None
    } else {
        let derive_type_instantiation::instantiation::T { this, subst } = subst;
        let header = MarkedString::MarkedString("Instantiation:".to_string());
        let section = {
            let print_tparam = |tparam: &str, ty: &typing_defs::Ty| {
                format!("  {} = {};", tparam, tast_env::print_ty(env, ty))
            };
            let printed_this = this.as_ref().map(|ty| print_tparam("this", ty));
            // `S_map.elements subst |> List.rev_map ~f:print_tparam`:
            // `elements` is in decreasing order of the keys, so this is
            // increasing.
            let mut printed_tparams: Vec<String> =
                subst.iter().map(|(tparam, ty)| print_tparam(tparam, ty)).collect();
            if let Some(printed_this) = printed_this {
                printed_tparams.insert(0, printed_this);
            }
            make_hack_marked_code(printed_tparams.join("\n"))
        };
        Some(vec![header, section])
    }
}

/// Make the "Defined in" section of the hover card, which indicates where a member
/// is defined
fn make_defined_in_section(def_opt: Option<&Def>, tparams: &[DeclTparam]) -> Option<String> {
    let def = def_opt?;
    let tparams = match tparams {
        [] => String::new(),
        _ => format!(
            "<{}>",
            tparams
                .iter()
                .map(|param| param.name.id_ref().as_str())
                .collect::<Vec<_>>()
                .join(", ")
        ),
    };
    Some(format!(
        "Defined in `{}{}`",
        split_class_name(&sd::full_name(def)),
        tparams
    ))
}

/// Return the hover card section for the uninstantiated signature and the
/// hover card section showing the instantiation.
/// So when hovering on a method call for example, shows something like
///
/// ```text
/// ---
/// public function m<T, Tr>(T $x): Tr;
/// ---
/// Instantiation:
///   T = int;
///   Tr = string;
/// ```
fn show_type_with_instantiation(
    occurrence: &Occ,
    def_opt: Option<&Def>,
    decl_ty: &DeclTy,
    type_info: &server_infer_type::T,
) -> (String, Option<Vec<MarkedString>>) {
    let env = server_infer_type::get_env(type_info);
    let locl_ty = server_infer_type::get_type(type_info);
    let snippet = tast_env::print_decl_ty_with_identity(env, decl_ty, occurrence, def_opt);
    let mut env = env.clone();
    let instantiation = tast_env::derive_instantiation(&mut env, decl_ty, locl_ty);
    let instantiation_section = make_instantiation_section(&env, &instantiation);
    (snippet, instantiation_section)
}

fn make_hover_info(
    under_dynamic_result: &str,
    ctx: &provider_context::T,
    info_opt: Option<&server_infer_type::T>,
    entry: &Arc<provider_context::Entry>,
    occurrence: &Occ,
    def_opt: Option<&Def>,
) -> HoverInfo {
    let print_locl_ty_with_identity = |do_not_strip_dynamic: bool, info: &server_infer_type::T| {
        let env = server_infer_type::get_env(info);
        let ty = server_infer_type::get_type(info).clone();
        let ty = if do_not_strip_dynamic {
            ty
        } else {
            tast_env::strip_dynamic(env, ty)
        };
        tast_env::print_ty_with_identity(env, ty, occurrence, def_opt)
    };
    let so::T { name, type_, .. } = occurrence;
    let member_snippet = |info: &server_infer_type::T| match get_decl_ty(ctx, def_opt, type_) {
        (Some(class_tparams), Some(decl_ty)) => (
            show_type_with_instantiation(occurrence, def_opt, &decl_ty, info),
            class_tparams,
        ),
        _ => ((print_locl_ty_with_identity(false, info), None), vec![]),
    };
    let (defined_in, snippet, instantiation_section) = match (type_, info_opt) {
        (_, None) => (None, utils::strip_hh_lib_ns(name).to_string(), None),
        (so::Kind::BestEffortArgument(recv, i), _) => {
            let param_name = nth_param(ctx, recv, *i);
            (
                None,
                format!("Parameter: {}", param_name.as_deref().unwrap_or("$_")),
                None,
            )
        }
        (so::Kind::ClassConst(..), Some(info)) => {
            let ((snippet, instantiation_section), class_tparams) = member_snippet(info);
            // The type snippet is `const <type> <name>`. Append ` = <value>` from the
            // definition text, like GConst hover. The class-const span is
            // `<name> = <value>` (no `const`/type), so strip the leading name.
            let snippet = match (def_opt, make_hover_const_definition(entry, def_opt)) {
                (Some(def), Some(decl)) => match decl.strip_prefix(def.name.as_str()) {
                    Some(value) if !core_string_strip(value).is_empty() => snippet + value,
                    _ => snippet,
                },
                _ => snippet,
            };
            (
                make_defined_in_section(def_opt, &class_tparams),
                snippet,
                instantiation_section,
            )
        }
        (so::Kind::Method(..), Some(info)) | (so::Kind::Property(..), Some(info)) => {
            let ((snippet, instantiation_section), class_tparams) = member_snippet(info);
            (
                make_defined_in_section(def_opt, &class_tparams),
                snippet,
                instantiation_section,
            )
        }
        (so::Kind::GConst, Some(info)) => (
            None,
            match make_hover_const_definition(entry, def_opt) {
                Some(def_txt) => def_txt,
                None => print_locl_ty_with_identity(false, info),
            },
            None,
        ),
        (so::Kind::Function, Some(info)) => {
            let (snippet, instantiation_section) = match get_decl_ty(ctx, def_opt, type_) {
                (_, Some(decl_ty)) => show_type_with_instantiation(occurrence, def_opt, &decl_ty, info),
                _ => (print_locl_ty_with_identity(true, info), None),
            };
            (
                make_fun_defined_in_section(def_opt),
                snippet,
                instantiation_section,
            )
        }
        (
            so::Kind::Class(_)
            | so::Kind::Module
            | so::Kind::Typeconst(..)
            | so::Kind::Attribute(_)
            | so::Kind::EnumClassLabel(..)
            | so::Kind::Keyword(_)
            | so::Kind::BuiltInType(_)
            | so::Kind::LocalVar
            | so::Kind::TypeVar
            | so::Kind::XhpLiteralAttr(..)
            | so::Kind::HhFixme
            | so::Kind::HhIgnore
            | so::Kind::PureFunctionContext,
            Some(info),
        ) => (
            None,
            print_locl_ty_with_identity(true, info) + under_dynamic_result,
            None,
        ),
    };
    let addendum = match type_ {
        so::Kind::Attribute(_) => {
            let mut l = make_hover_attr_docs(name);
            l.extend(make_hover_doc_block(ctx, entry, occurrence, def_opt));
            l
        }
        so::Kind::Keyword(info) => vec![keyword_info(info)],
        so::Kind::HhFixme => vec![HH_FIXME_INFO.to_string()],
        so::Kind::HhIgnore => vec![HH_IGNORE_INFO.to_string()],
        so::Kind::PureFunctionContext => vec![PURE_CONTEXT_INFO.to_string()],
        so::Kind::BuiltInType(bt) => vec![so::built_in_type_hover(bt)],
        _ => make_hover_doc_block(ctx, entry, occurrence, def_opt),
    };
    let addendum: Vec<MarkedString> = addendum.into_iter().map(MarkedString::MarkedString).collect();
    let mut main_section: Vec<Vec<MarkedString>> = vec![vec![make_hack_marked_code(snippet)]];
    if let Some(instantiation_section) = instantiation_section {
        main_section.push(instantiation_section);
    }
    if let Some(defined_in) = defined_in {
        main_section.insert(0, vec![MarkedString::MarkedString(defined_in)]);
    }
    let mut snippet = vec![];
    for (i, section) in main_section.into_iter().enumerate() {
        if i > 0 {
            snippet.push(MarkedString::MarkedString("---".to_string()));
        }
        snippet.extend(section);
    }
    HoverInfo {
        snippet,
        addendum,
        pos: Some(occurrence.pos.clone()),
    }
}

/// `String.strip` (Core)
fn core_string_strip(s: &str) -> &str {
    s.trim_matches(|c| matches!(c, ' ' | '\t' | '\n' | '\x0b' | '\x0c' | '\r'))
}

struct Identity<'a> {
    ctx: provider_context::T,
    info_opt: Option<&'a server_infer_type::T>,
    entry: Arc<provider_context::Entry>,
    occurrence: Occ,
    def_opt: Option<Def>,
}

fn make_hover_info_with_fallback(under_dynamic_result: &str, results: Vec<Identity<'_>>) -> Vec<(Occ, HoverInfo)> {
    let class_fallback = results.iter().find(|r| so::is_class(&r.occurrence));
    results
        .iter()
        .map(|r| {
            let hover_info = || {
                make_hover_info(
                    under_dynamic_result,
                    &r.ctx,
                    r.info_opt,
                    &r.entry,
                    &r.occurrence,
                    r.def_opt.as_ref(),
                )
            };
            if so::is_constructor(&r.occurrence)
                && make_hover_doc_block(&r.ctx, &r.entry, &r.occurrence, r.def_opt.as_ref()).is_empty()
            {
                // Case where constructor docblock is empty.
                let hover_info = hover_info();
                match class_fallback {
                    Some(c) => {
                        let mut addendum: Vec<MarkedString> =
                            make_hover_doc_block(&c.ctx, &c.entry, &c.occurrence, c.def_opt.as_ref())
                                .into_iter()
                                .map(MarkedString::MarkedString)
                                .collect();
                        addendum.extend(hover_info.addendum);
                        (
                            r.occurrence.clone(),
                            HoverInfo {
                                snippet: hover_info.snippet,
                                addendum,
                                pos: hover_info.pos,
                            },
                        )
                    }
                    None => (r.occurrence.clone(), hover_info),
                }
            } else {
                (r.occurrence.clone(), hover_info())
            }
        })
        .collect()
}

pub fn go_quarantined(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    pos: &position::T,
) -> hover_service::Result {
    let identities: Vec<(Occ, Option<Def>)> = server_identify_function::go_quarantined(ctx, entry, pos);
    let tast_provider::ComputeTastResult { tast, .. } = tast_provider::compute_tast_quarantined(ctx, entry);
    let info_opt = server_infer_type::human_friendly_type_at_pos(false, ctx, &tast, pos);
    let info_dynamic_opt = server_infer_type::human_friendly_type_at_pos(true, ctx, &tast, pos);
    let under_dynamic_result: String = match &info_dynamic_opt {
        Some(info_dynamic) => {
            let ty_dynamic = server_infer_type::get_type(info_dynamic);
            match &info_opt {
                None => String::new(),
                Some(info) => {
                    let ty = server_infer_type::get_type(info);
                    let env = server_infer_type::get_env(info_dynamic);
                    // If under dynamic the type is no worse then don't
                    // bother presenting it. Example: ~int in static mode, dynamic under dynamic mode.
                    if tast_env::is_sub_type(env, ty_dynamic, ty) {
                        String::new()
                    } else {
                        format!(
                            " ({} when called dynamically)",
                            tast_env::print_ty(env, ty_dynamic)
                        )
                    }
                }
            }
        }
        None => String::new(),
    };
    match (identities.as_slice(), &info_opt) {
        ([], Some(info)) => {
            let ty = server_infer_type::get_type(info);
            let env = server_infer_type::get_env(info);
            // There are no identities (named entities) at the cursor, but we
            // know the type of the expression. Just show the type.
            //
            // This can occur if the user hovers over a literal such as `123`.
            let addendum = match typing_defs::get_node(ty) {
                typing_defs::Ty_::Tgeneric(name) if name == sn::typehints::THIS => {
                    let upper_bounds = crate::typing_set::to_list(&tast_env::get_upper_bounds(env, sn::typehints::THIS))
                        .iter()
                        .map(|t| tast_env::print_ty(env, t))
                        .collect::<Vec<_>>()
                        .join(", ");
                    vec![MarkedString::MarkedString(format!(
                        "this has the following upper bounds: {}",
                        upper_bounds
                    ))]
                }
                _ => vec![],
            };
            vec![HoverInfo {
                snippet: vec![make_hack_marked_code(
                    tast_env::print_ty(env, ty) + &under_dynamic_result,
                )],
                addendum,
                pos: None,
            }]
        }
        (
            [
                (
                    so::T {
                        type_: so::Kind::BestEffortArgument(recv, i),
                        ..
                    },
                    _,
                ),
            ],
            _,
        ) => {
            // There are no identities (named entities) at the cursor, but we
            // know the type of the expression and the name of the parameter
            // from the definition site.
            //
            // This can occur if the user hovers over a literal in a call,
            // e.g. `foo(123)`.
            let mut ty_result = match &info_opt {
                Some(info) => {
                    let ty = server_infer_type::get_type(info);
                    vec![HoverInfo {
                        snippet: vec![make_hack_marked_code(
                            tast_env::print_ty(server_infer_type::get_env(info), ty) + &under_dynamic_result,
                        )],
                        addendum: vec![],
                        pos: None,
                    }]
                }
                None => vec![],
            };
            let param_result = match nth_param(ctx, recv, *i) {
                Some(param_name) => vec![HoverInfo {
                    snippet: vec![make_hack_marked_code(format!("Parameter: {}", param_name))],
                    addendum: vec![],
                    pos: None,
                }],
                None => vec![],
            };
            ty_result.extend(param_result);
            ty_result
        }
        _ => {
            // We have a list of named things at the cursor. Show the
            // docblock and type of each thing.
            let results: Vec<Identity<'_>> = identities
                .into_iter()
                .map(|(occurrence, def_opt)| {
                    // If we're hovering over a type hint, we're not interested
                    // in the type of the enclosing expression.
                    let info_opt = match &occurrence.type_ {
                        so::Kind::TypeVar => None,
                        so::Kind::BuiltInType(_) => None,
                        _ => info_opt.as_ref(),
                    };
                    let path = match &def_opt {
                        Some(def) => def.pos.filename().clone(),
                        None => entry.path.clone(),
                    };
                    let (ctx, entry) = provider_context::add_entry_if_missing(ctx, path);
                    Identity {
                        ctx,
                        info_opt,
                        entry,
                        occurrence,
                        def_opt,
                    }
                })
                .collect();
            let results = make_hover_info_with_fallback(&under_dynamic_result, results);
            let mut results = filter_class_and_constructor(results);
            // `List.remove_consecutive_duplicates ~equal:equal_hover_info`
            results.dedup_by(|b, a| hover_service::equal_hover_info(a, b));
            results
        }
    }
}
