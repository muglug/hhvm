// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/aast_names_utils.ml`. See `hh/PORTING.md`.

use oxidized::aast::Expr_;
use oxidized::aast::Stmt_;

pub fn stmt_name<Ex, En>(s: &Stmt_<Ex, En>) -> &'static str {
    match s {
        Stmt_::Fallthrough => "Fallthrough",
        Stmt_::Expr(_) => "Expr",
        Stmt_::Break => "Break",
        Stmt_::Continue => "Continue",
        Stmt_::Throw(_) => "Throw",
        Stmt_::Return(_) => "Return",
        Stmt_::YieldBreak => "Yield_break",
        Stmt_::Awaitall(_) => "Awaitall",
        Stmt_::Concurrent(_) => "Concurrent",
        Stmt_::If(_) => "If",
        Stmt_::Do(_) => "Do",
        Stmt_::While(_) => "While",
        Stmt_::Using(_) => "Using",
        Stmt_::For(_) => "For",
        Stmt_::Switch(_) => "Switch",
        Stmt_::Match(_) => "Match",
        Stmt_::Foreach(_) => "Foreach",
        Stmt_::Try(_) => "Try",
        Stmt_::Noop => "Noop",
        Stmt_::Block(_) => "Block",
        Stmt_::Markup(_) => "Markup",
        // (Not in the OCaml function, whose match is exhaustive there.)
        #[allow(unreachable_patterns)]
        _ => "?",
    }
}

pub fn expr_name<Ex, En>(e: &Expr_<Ex, En>) -> &'static str {
    match e {
        Expr_::Shape(_) => "Shape",
        Expr_::ValCollection(_) => "ValCollection",
        Expr_::KeyValCollection(_) => "KeyValCollection",
        Expr_::Null => "Null",
        Expr_::This => "This",
        Expr_::True => "True",
        Expr_::False => "False",
        Expr_::Omitted => "Omitted",
        Expr_::Id(_) => "Id",
        Expr_::Lvar(_) => "Lvar",
        Expr_::Dollardollar(_) => "Dollardollar",
        Expr_::Clone(_) => "Clone",
        Expr_::ObjGet(_) => "Obj_get",
        Expr_::ArrayGet(_) => "Array_get",
        Expr_::ClassGet(_) => "Class_get",
        Expr_::ClassConst(_) => "Class_const",
        Expr_::Call(_) => "Call",
        Expr_::FunctionPointer(_) => "FunctionPointer",
        Expr_::Int(_) => "Int",
        Expr_::Float(_) => "Float",
        Expr_::String(_) => "String",
        Expr_::String2(_) => "String2",
        Expr_::PrefixedString(_) => "PrefixedString",
        Expr_::Yield(_) => "Yield",
        Expr_::Await(_) => "Await",
        Expr_::Delay(_) => "Delay",
        Expr_::Tuple(_) => "Tuple",
        Expr_::List(_) => "List",
        Expr_::Cast(_) => "Cast",
        Expr_::Unop(_) => "Unop",
        Expr_::Binop(_) => "Binop",
        Expr_::Assign(_) => "Assign",
        Expr_::Pipe(_) => "Pipe",
        Expr_::Eif(_) => "Eif",
        Expr_::Is(_) => "Is",
        Expr_::As(_) => "As",
        Expr_::Upcast(_) => "Upcast",
        Expr_::New(_) => "New",
        Expr_::Efun(_) => "Efun",
        Expr_::Lfun(_) => "Lfun",
        Expr_::Xml(_) => "Xml",
        Expr_::Import(_) => "Import",
        Expr_::Collection(_) => "Collection",
        Expr_::ExpressionTree(_) => "ExpressionTree",
        Expr_::Lplaceholder(_) => "Lplaceholder",
        Expr_::MethodCaller(_) => "Method_caller",
        Expr_::Pair(_) => "Pair",
        Expr_::ETSplice(_) => "ET_splice",
        Expr_::EnumClassLabel(_) => "EnumClassLabel",
        Expr_::ReadonlyExpr(_) => "Readonly",
        Expr_::Hole(_) => "Hole",
        Expr_::Invalid(_) => "Invalid",
        Expr_::Package(_) => "Package",
        Expr_::Nameof(_) => "Nameof",
        Expr_::DestructureShape(_) => "DestructureShape",
        Expr_::DestructureTuple(_) => "DestructureTuple",
        // (Not in the OCaml function, whose match is exhaustive there.)
        #[allow(unreachable_patterns)]
        _ => "?",
    }
}
