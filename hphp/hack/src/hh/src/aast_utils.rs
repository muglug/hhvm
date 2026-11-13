// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Aast_utils` (`annotated_ast/aast_utils.ml`). See `hh/PORTING.md`.
//!
//! The functions of `aast_utils.ml` that the typechecker uses. The ones that
//! return a part of their argument (`arg_to_expr`, `get_param_default`,
//! `get_fun_expr`) return a reference to it.
//!
//! Not here: `get_virtual_expr`, which nothing in scope calls. The functions
//! about expression trees (`find_shape_field`, `get_return_from_fun`,
//! `get_virtual_expr_from_et`, `is_assign`, `get_splices_from_fun`,
//! `get_splices_from_et`) were added for `Identify_symbol_service` (F1); the
//! lists they return are lists of references.

use oxidized::aast::Afield;
use oxidized::aast::Argument;
use oxidized::aast::Expr;
use oxidized::aast::Expr_;
use oxidized::aast::FunParam;
use oxidized::aast::FunParamInfo;
use oxidized::aast::Fun_;
use oxidized::aast::PackageMembership;
use oxidized::pos::Pos;

pub fn can_be_captured<Ex, En>(e: &Expr_<Ex, En>) -> bool {
    match e {
        Expr_::Shape(_)
        | Expr_::ValCollection(_)
        | Expr_::KeyValCollection(_)
        | Expr_::Null
        | Expr_::This
        | Expr_::True
        | Expr_::False
        | Expr_::Omitted
        | Expr_::Id(_)
        | Expr_::Lvar(_)
        | Expr_::Dollardollar(_)
        | Expr_::ArrayGet(_)
        | Expr_::ObjGet(_)
        | Expr_::ClassGet(_)
        | Expr_::ClassConst(_)
        | Expr_::Nameof(_)
        | Expr_::Call(_)
        | Expr_::FunctionPointer(_)
        | Expr_::Int(_)
        | Expr_::Float(_)
        | Expr_::String(_)
        | Expr_::String2(_)
        | Expr_::PrefixedString(_)
        | Expr_::Tuple(_)
        | Expr_::List(_)
        | Expr_::Xml(_)
        | Expr_::Import(_)
        | Expr_::Lplaceholder(_)
        | Expr_::MethodCaller(_)
        | Expr_::EnumClassLabel(_)
        | Expr_::DestructureShape(_)
        | Expr_::DestructureTuple(_) => false,
        Expr_::Yield(_)
        | Expr_::Clone(_)
        | Expr_::Await(_)
        | Expr_::Delay(_)
        | Expr_::ReadonlyExpr(_)
        | Expr_::Cast(_)
        | Expr_::Unop(_)
        | Expr_::Binop(_)
        | Expr_::Assign(_)
        | Expr_::Pipe(_)
        | Expr_::Eif(_)
        | Expr_::Is(_)
        | Expr_::As(_)
        | Expr_::Upcast(_)
        | Expr_::New(_)
        | Expr_::Efun(_)
        | Expr_::Lfun(_)
        | Expr_::Collection(_)
        | Expr_::ExpressionTree(_)
        | Expr_::Pair(_)
        | Expr_::ETSplice(_)
        | Expr_::Package(_) => true,
        Expr_::Invalid(e) => match &**e {
            None => false,
            Some(Expr(_, _, exp)) => can_be_captured(exp),
        },
        Expr_::Hole(hole) => {
            let (Expr(_, _, exp), _, _, _) = &**hole;
            can_be_captured(exp)
        }
    }
}

pub fn get_fun_expr<Ex, En>(expr: &Expr<Ex, En>) -> Option<&Fun_<Ex, En>> {
    match &expr.2 {
        Expr_::Lfun(lfun) => Some(&lfun.0),
        Expr_::Efun(efun) => Some(&efun.fun),
        Expr_::Hole(hole) => get_fun_expr(&hole.0),
        _ => None,
    }
}

pub fn is_const_expr<Ex, En>(expr: &Expr<Ex, En>) -> bool {
    // `Option.fold ~none:true ~some:is_const_expr`
    fn is_const_opt<Ex, En>(e: &Option<Expr<Ex, En>>) -> bool {
        match e {
            None => true,
            Some(e) => is_const_expr(e),
        }
    }
    let Expr(_, _, expr_) = expr;
    match expr_ {
        Expr_::Null
        | Expr_::True
        | Expr_::False
        | Expr_::This
        | Expr_::Omitted
        | Expr_::Id(_)
        | Expr_::Lvar(_)
        | Expr_::Dollardollar(_)
        | Expr_::ClassConst(_)
        | Expr_::FunctionPointer(_)
        | Expr_::Int(_)
        | Expr_::Float(_)
        | Expr_::String(_)
        | Expr_::List(_)
        | Expr_::Efun(_)
        | Expr_::Lfun(_)
        | Expr_::EnumClassLabel(_)
        | Expr_::Lplaceholder(_)
        | Expr_::MethodCaller(_)
        | Expr_::Package(_)
        | Expr_::Nameof(_) => true,
        Expr_::Call(_)
        | Expr_::New(_)
        | Expr_::Await(_)
        | Expr_::Delay(_)
        | Expr_::Assign(_)
        | Expr_::ExpressionTree(_)
        | Expr_::ETSplice(_)
        | Expr_::Xml(_) => false,
        Expr_::Clone(expr) | Expr_::ReadonlyExpr(expr) => is_const_expr(expr),
        Expr_::PrefixedString(e) => is_const_expr(&e.1),
        Expr_::Cast(e) => is_const_expr(&e.1),
        Expr_::Unop(e) => is_const_expr(&e.1),
        Expr_::Is(e) => is_const_expr(&e.0),
        Expr_::As(e) => is_const_expr(&e.expr),
        Expr_::Upcast(e) => is_const_expr(&e.0),
        Expr_::Hole(e) => is_const_expr(&e.0),
        Expr_::Import(e) => is_const_expr(&e.1),
        Expr_::ObjGet(e) => is_const_expr(&e.0) && is_const_expr(&e.1),
        Expr_::Pipe(e) => is_const_expr(&e.1) && is_const_expr(&e.2),
        Expr_::Binop(e) => is_const_expr(&e.lhs) && is_const_expr(&e.rhs),
        Expr_::Pair(e) => is_const_expr(&e.1) && is_const_expr(&e.2),
        Expr_::ValCollection(e) => e.2.iter().all(is_const_expr),
        Expr_::String2(exprs) | Expr_::Tuple(exprs) => exprs.iter().all(is_const_expr),
        Expr_::Shape(shapes) => shapes.iter().all(|(_, e)| is_const_expr(e)),
        Expr_::KeyValCollection(e) => {
            (e.2.iter()).all(|field| is_const_expr(&field.0) && is_const_expr(&field.1))
        }
        Expr_::Invalid(e) => is_const_opt(e),
        Expr_::ArrayGet(e) => is_const_expr(&e.0) && is_const_opt(&e.1),
        Expr_::ClassGet(_) => true,
        Expr_::Yield(afield) => is_const_afield(afield),
        Expr_::Eif(e) => is_const_expr(&e.0) && is_const_opt(&e.1) && is_const_expr(&e.2),
        Expr_::Collection(e) => e.2.iter().all(is_const_afield),
        Expr_::DestructureShape(_) | Expr_::DestructureTuple(_) => false,
    }
}

fn is_const_afield<Ex, En>(afield: &Afield<Ex, En>) -> bool {
    match afield {
        Afield::AFvalue(expr) => is_const_expr(expr),
        Afield::AFkvalue(e1, e2) => is_const_expr(e1) && is_const_expr(e2),
    }
}

pub fn is_param_variadic<Ex, En>(param: &FunParam<Ex, En>) -> bool {
    match &param.info {
        FunParamInfo::ParamVariadic => true,
        FunParamInfo::ParamRequired => false,
        FunParamInfo::ParamOptional(_) => false,
    }
}

pub fn is_param_splat<Ex, En>(param: &FunParam<Ex, En>) -> bool {
    param.splat.is_some()
}

pub fn is_param_optional<Ex, En>(param: &FunParam<Ex, En>) -> bool {
    match &param.info {
        FunParamInfo::ParamVariadic => false,
        FunParamInfo::ParamRequired => false,
        FunParamInfo::ParamOptional(_) => true,
    }
}

pub fn get_param_default<Ex, En>(param: &FunParam<Ex, En>) -> Option<&Expr<Ex, En>> {
    match &param.info {
        FunParamInfo::ParamVariadic => None,
        FunParamInfo::ParamRequired => None,
        FunParamInfo::ParamOptional(e) => e.as_ref(),
    }
}

pub fn get_expr_pos<Ex, En>(e: &Expr<Ex, En>) -> Pos {
    e.1.clone()
}

pub fn get_argument_pos<Ex, En>(a: &Argument<Ex, En>) -> Pos {
    match a {
        Argument::Anormal(e) => get_expr_pos(e),
        Argument::Ainout(_, e) => get_expr_pos(e),
        Argument::Anamed(_, e) => get_expr_pos(e),
    }
}

pub fn arg_to_expr<Ex, En>(arg: &Argument<Ex, En>) -> &Expr<Ex, En> {
    match arg {
        Argument::Anormal(e) => e,
        Argument::Ainout(_, e) => e,
        Argument::Anamed(_, e) => e,
    }
}

/// Convert an an expression to an argument, using the supplied inout
///
/// (Added for `Typing.Expr.call`, the only caller. `Pos.show_absolute` is the
/// printer that `[@@deriving show]` makes, which is not ported: the logger
/// gets the `Debug` form of the same record instead, as in
/// `typing_destructure`. The logger is a stub that ignores it.)
pub fn expr_to_arg<Ex, En>(
    pk: oxidized::ast_defs::ParamKind,
    arg_name: Option<oxidized::aast::Sid>,
    e: Expr<Ex, En>,
) -> Argument<Ex, En> {
    use oxidized::ast_defs::ParamKind;
    match (pk, arg_name) {
        (ParamKind::Pnormal, Some(sid)) => Argument::Anamed(sid, e),
        (ParamKind::Pnormal, None) => Argument::Anormal(e),
        (ParamKind::Pinout(p), Some(oxidized::ast_defs::Id(pos, _))) => {
            crate::hack_event_logger::invariant_violation_bug(
                None,
                Some(&format!("{:?}", crate::pos::to_absolute(&pos))),
                None,
                None,
                None,
                "An argument can't be both named and inout. This should be enforced by the structure of Aast_defs.argument",
            );
            Argument::Ainout(p, e)
        }
        (ParamKind::Pinout(p), None) => Argument::Ainout(p, e),
    }
}

pub fn get_package_name(membership: &PackageMembership) -> String {
    match membership {
        PackageMembership::PackageConfigAssignment(pkg)
        | PackageMembership::PackageOverride(_, pkg) => pkg.clone(),
    }
}

pub fn find_shape_field<'a, Ex, En>(
    name: &str,
    fields: &'a [(oxidized::ast_defs::ShapeFieldName, Expr<Ex, En>)],
) -> Option<&'a (oxidized::ast_defs::ShapeFieldName, Expr<Ex, En>)> {
    fields.iter().find(|(field_name, _e)| match field_name {
        oxidized::ast_defs::ShapeFieldName::SFlitStr((_, n)) => name.as_bytes() == n.as_slice(),
        _ => false,
    })
}

pub fn get_return_from_fun<Ex, En>(e: &Expr<Ex, En>) -> Option<&Expr<Ex, En>> {
    let fb_ast = match &e.2 {
        Expr_::Lfun(f) => &f.0.body.fb_ast,
        Expr_::Efun(ef) => &ef.fun.body.fb_ast,
        _ => return None,
    };
    fb_ast.0.iter().find_map(|s| match &s.1 {
        oxidized::aast::Stmt_::Return(e) => e.as_ref().as_ref(),
        _ => None,
    })
}

pub fn get_virtual_expr_from_et<Ex, En>(
    et: &oxidized::aast::ExpressionTree<Ex, En>,
) -> Option<&Expr<Ex, En>> {
    fn get_body_helper<Ex, En>(e: &Expr<Ex, En>) -> Option<&Expr<Ex, En>> {
        // (_, _, Call { args = _ :: Anormal (_, _, Shape fields) :: _; _ })
        let Expr_::Call(call) = &e.2 else {
            return None;
        };
        let Some(Argument::Anormal(Expr(_, _, Expr_::Shape(fields)))) = call.args.get(1) else {
            return None;
        };
        match find_shape_field("type", fields) {
            Some((_, e)) => get_return_from_fun(e),
            None => None,
        }
    }
    let call = match &et.runtime_expr.2 {
        Expr_::Await(e) => match &e.2 {
            Expr_::Call(call) => Some(call),
            _ => None,
        },
        Expr_::Call(call) => Some(call),
        _ => None,
    };
    match call {
        Some(call) => match get_return_from_fun(&call.func) {
            Some(e) => get_body_helper(e),
            None => get_body_helper(&et.runtime_expr),
        },
        None => get_body_helper(&et.runtime_expr),
    }
}

pub fn is_assign<Ex, En>(s: &oxidized::aast::Stmt<Ex, En>) -> bool {
    match &s.1 {
        oxidized::aast::Stmt_::Expr(e) => matches!(&e.2, Expr_::Assign(a) if a.1.is_none()),
        _ => false,
    }
}

pub fn get_splices_from_fun<Ex, En>(e: &Expr<Ex, En>) -> Vec<&oxidized::aast::Stmt<Ex, En>> {
    let fb_ast = match &e.2 {
        Expr_::Lfun(f) => &f.0.body.fb_ast,
        Expr_::Efun(ef) => &ef.fun.body.fb_ast,
        _ => return vec![],
    };
    fb_ast.0.iter().filter(|s| is_assign(s)).collect()
}

pub fn get_splices_from_et<Ex, En>(
    et: &oxidized::aast::ExpressionTree<Ex, En>,
) -> Vec<&oxidized::aast::Stmt<Ex, En>> {
    match &et.runtime_expr.2 {
        Expr_::Await(e) => match &e.2 {
            Expr_::Call(call) => get_splices_from_fun(&call.func),
            _ => vec![],
        },
        Expr_::Call(call) => get_splices_from_fun(&call.func),
        _ => vec![],
    }
}

#[cfg(test)]
mod tests {
    use oxidized::aast::Binop;
    use oxidized::ast_defs::Bop;
    use oxidized::ast_defs::Id;
    use oxidized::ast_defs::Uop;

    use super::*;

    type E = Expr<(), ()>;

    fn e(e: Expr_<(), ()>) -> E {
        Expr((), Pos::NONE, e)
    }

    fn int(i: &str) -> E {
        e(Expr_::Int(i.to_string()))
    }

    fn call() -> E {
        e(Expr_::Await(Box::new(int("1"))))
    }

    #[test]
    fn const_exprs() {
        assert!(is_const_expr(&int("1")));
        assert!(is_const_expr(&e(Expr_::Null)));
        assert!(!is_const_expr(&call()));
        let binop = |lhs, rhs| {
            e(Expr_::Binop(Box::new(Binop {
                bop: Bop::Plus,
                lhs,
                rhs,
            })))
        };
        assert!(is_const_expr(&binop(int("1"), int("2"))));
        assert!(!is_const_expr(&binop(int("1"), call())));
        assert!(!is_const_expr(&binop(call(), int("2"))));
        assert!(is_const_expr(&e(Expr_::Unop(Box::new((
            Uop::Uminus,
            int("1")
        ))))));
        assert!(!is_const_expr(&e(Expr_::Unop(Box::new((
            Uop::Uminus,
            call()
        ))))));
        assert!(is_const_expr(&e(Expr_::Tuple(vec![int("1"), int("2")]))));
        assert!(!is_const_expr(&e(Expr_::Tuple(vec![int("1"), call()]))));
        // A list is constant whatever is in it, and so is an invalid
        // expression without an expression.
        assert!(is_const_expr(&e(Expr_::List(vec![call()]))));
        assert!(is_const_expr(&e(Expr_::Invalid(Box::new(None)))));
        assert!(!is_const_expr(&e(Expr_::Invalid(Box::new(Some(call()))))));
        assert!(is_const_expr(&e(Expr_::ArrayGet(Box::new((
            int("1"),
            None
        ))))));
        assert!(!is_const_expr(&e(Expr_::ArrayGet(Box::new((
            int("1"),
            Some(call())
        ))))));
        assert!(is_const_expr(&e(Expr_::Eif(Box::new((
            int("1"),
            None,
            int("2")
        ))))));
        assert!(!is_const_expr(&e(Expr_::Yield(Box::new(Afield::AFkvalue(
            int("1"),
            call()
        ))))));
    }

    #[test]
    fn captured() {
        assert!(!can_be_captured(&int("1").2));
        assert!(can_be_captured(&call().2));
        assert!(!can_be_captured::<(), ()>(&Expr_::Invalid(Box::new(None))));
        assert!(can_be_captured(&Expr_::Invalid(Box::new(Some(call())))));
        assert!(!can_be_captured(&Expr_::Invalid(Box::new(Some(int("1"))))));
        assert!(can_be_captured::<(), ()>(&Expr_::Package(Box::new(Id(
            Pos::NONE,
            "p".to_string()
        )))));
    }

    #[test]
    fn arguments() {
        let name = Id(Pos::NONE, "x".to_string());
        for arg in [
            Argument::Anormal(int("1")),
            Argument::Ainout(Pos::NONE, int("1")),
            Argument::Anamed(name, int("1")),
        ] {
            assert_eq!(arg_to_expr(&arg), &int("1"));
            assert_eq!(get_argument_pos(&arg), Pos::NONE);
        }
        assert_eq!(get_expr_pos(&int("1")), Pos::NONE);
        assert_eq!(get_fun_expr(&int("1")), None);
    }

    #[test]
    fn package_names() {
        assert_eq!(
            get_package_name(&PackageMembership::PackageConfigAssignment("a".to_string())),
            "a"
        );
        assert_eq!(
            get_package_name(&PackageMembership::PackageOverride(
                Pos::NONE,
                "b".to_string()
            )),
            "b"
        );
    }
}
