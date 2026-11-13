// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `refactor_sd/`: `refactor_sd_types.ml`, `refactor_sd_options.ml`,
//! `refactor_sd_pretty_printer.ml`, `refactor_sd_env.ml`,
//! `refactor_sd_walker.ml`, `refactor_sd_solver.ml` and `refactor_sd.ml`, one
//! module each. See `hh/PORTING.md`.
//!
//! A `constraint_ list` is a `Vec` in the order of the OCaml list (its head
//! first). `Refactor_sd_exn` is a panic.

/// `refactor_sd_types.ml`
pub mod types {
    use std::collections::BTreeMap;

    use crate::pos::Pos;
    use crate::tast_env;
    use crate::typing_continuations as cont;

    pub type LMap<V> = BTreeMap<oxidized::local_id::LocalId, V>;
    pub type KMap<V> = BTreeMap<cont::T, V>;

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum AnalysisMode {
        FlagTargets,
        DumpConstraints,
        SimplifyConstraints,
        SolveConstraints,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum RefactorMode {
        Class,
        Function,
        Method,
    }

    #[derive(Clone, Copy, Debug)]
    pub struct Options {
        pub analysis_mode: AnalysisMode,
        pub refactor_mode: RefactorMode,
    }

    pub struct ElementInfo {
        pub element_name: String,
    }

    /// `[@@deriving eq, ord]`
    #[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
    pub enum Entity_ {
        Literal(Pos),
        Variable(isize),
    }

    pub type Entity = Option<Entity_>;

    #[derive(Clone, Debug)]
    pub enum Constraint_ {
        Introduction(Pos),
        Upcast(Entity_, Pos),
        Subset(Entity_, Entity_),
        Called(Pos),
    }

    #[derive(Clone, Debug)]
    pub enum RefactorSdResult {
        ExistsUpcast(Pos),
        NoUpcast,
    }

    pub type Lenv = KMap<LMap<Entity>>;

    #[derive(Clone)]
    pub struct Env {
        pub constraints: Vec<Constraint_>,
        pub lenv: Lenv,
        pub tast_env: tast_env::Env,
    }

    /// `raise (Refactor_sd_exn msg)`
    pub fn refactor_sd_exn(msg: String) -> ! {
        panic!("Refactor_sd_types.Refactor_sd_exn({:?})", msg)
    }
}

/// `refactor_sd_options.ml`
pub mod options {
    use super::types::*;

    pub fn parse_analysis_mode(s: &str) -> Option<AnalysisMode> {
        match s {
            "flag" => Some(AnalysisMode::FlagTargets),
            "dump" => Some(AnalysisMode::DumpConstraints),
            "simplify" => Some(AnalysisMode::SimplifyConstraints),
            "solve" => Some(AnalysisMode::SolveConstraints),
            _ => None,
        }
    }

    pub fn parse_refactor_mode(s: &str) -> Option<RefactorMode> {
        match s {
            "Class" => Some(RefactorMode::Class),
            "Function" => Some(RefactorMode::Function),
            _ => None,
        }
    }

    pub fn mk(analysis_mode: AnalysisMode, refactor_mode: RefactorMode) -> Options {
        Options {
            analysis_mode,
            refactor_mode,
        }
    }
}

/// `refactor_sd_pretty_printer.ml`
pub mod pretty_printer {
    use super::types::*;

    fn pp(pos: &crate::pos::Pos) -> String {
        crate::ast_show::show_pos(pos)
    }

    pub fn show_entity(e: &Entity_) -> String {
        match e {
            Entity_::Literal(pos) => pp(pos),
            Entity_::Variable(var) => format!("?{}", var),
        }
    }

    pub fn show_constraint_(c: &Constraint_) -> String {
        match c {
            Constraint_::Introduction(pos) => format!("Introduction at {}", pp(pos)),
            Constraint_::Upcast(ent, _) => format!("Upcast at {}", show_entity(ent)),
            Constraint_::Subset(sub, sup) => format!("{} ⊆ {}", show_entity(sub), show_entity(sup)),
            Constraint_::Called(pos) => format!("Function call at {}", pp(pos)),
        }
    }

    pub fn show_refactor_sd_result(r: &RefactorSdResult) -> String {
        match r {
            RefactorSdResult::ExistsUpcast(pos) => format!("Upcast exists at {}", pp(pos)),
            RefactorSdResult::NoUpcast => "No upcast".to_string(),
        }
    }
}

/// `refactor_sd_env.ml`
pub mod env {
    use std::sync::atomic::AtomicIsize;
    use std::sync::atomic::Ordering;

    use oxidized::local_id::LocalId;

    use super::types::*;
    use crate::tast_env;
    use crate::typing_continuations as cont;

    static VAR_COUNTER: AtomicIsize = AtomicIsize::new(0);

    pub fn fresh_var() -> Entity_ {
        Entity_::Variable(VAR_COUNTER.fetch_add(1, Ordering::SeqCst) + 1)
    }

    /// `WrappedMap.merge_env env s1 s2 ~combine`: the bindings of `s2`, then
    /// those of `s1` that `s2` does not have.
    fn merge_env<K: Ord + Clone, V: Clone, E>(
        env: &mut E,
        s1: &std::collections::BTreeMap<K, V>,
        s2: &std::collections::BTreeMap<K, V>,
        mut combine: impl FnMut(&mut E, &K, Option<&V>, Option<&V>) -> Option<V>,
    ) -> std::collections::BTreeMap<K, V> {
        let mut map = std::collections::BTreeMap::new();
        for (key, v2) in s2 {
            if let Some(v) = combine(env, key, s1.get(key), Some(v2)) {
                map.insert(key.clone(), v);
            }
        }
        for (key, v1) in s1 {
            if !s2.contains_key(key) {
                if let Some(v) = combine(env, key, Some(v1), None) {
                    map.insert(key.clone(), v);
                }
            }
        }
        map
    }

    /// `new @ constraints`
    fn prepend(constraints: &mut Vec<Constraint_>, new: Vec<Constraint_>) {
        constraints.splice(0..0, new);
    }

    fn union_continuation_at_lid(entity1: &Entity, entity2: &Entity) -> (Vec<Constraint_>, Entity) {
        match (entity1, entity2) {
            (Some(entity1_), Some(entity2_)) => {
                let var = fresh_var();
                let constraints = vec![
                    Constraint_::Subset(entity1_.clone(), var.clone()),
                    Constraint_::Subset(entity2_.clone(), var.clone()),
                ];
                (constraints, Some(var))
            }
            (entity, None) | (None, entity) => (vec![], entity.clone()),
        }
    }

    fn union_continuation(
        constraints: &mut Vec<Constraint_>,
        cont1: &LMap<Entity>,
        cont2: &LMap<Entity>,
    ) -> LMap<Entity> {
        merge_env(constraints, cont1, cont2, |constraints, _lid, entity1_opt, entity2_opt| {
            match (entity1_opt, entity2_opt) {
                (Some(entity1), Some(entity2)) => {
                    let (new_constraints, entity) = union_continuation_at_lid(entity1, entity2);
                    prepend(constraints, new_constraints);
                    Some(entity)
                }
                (Some(entity), None) | (None, Some(entity)) => Some(entity.clone()),
                (None, None) => None,
            }
        })
    }

    pub mod lenv {
        use super::*;

        pub fn init(bindings: LMap<Entity>) -> Lenv {
            Lenv::from([(cont::T::Next, bindings)])
        }

        pub fn get_local_in_continuation(lenv: &Lenv, cont: cont::T, lid: &LocalId) -> Entity {
            lenv.get(&cont).and_then(|m| m.get(lid)).cloned().flatten()
        }

        pub fn get_local(lenv: &Lenv, lid: &LocalId) -> Entity {
            get_local_in_continuation(lenv, cont::T::Next, lid)
        }

        pub fn set_local_in_continuation(lenv: &mut Lenv, cont: cont::T, lid: LocalId, entity: Entity) {
            if let Some(lenv_per_cont) = lenv.get_mut(&cont) {
                lenv_per_cont.insert(lid, entity);
            }
        }

        pub fn set_local(lenv: &mut Lenv, lid: LocalId, entity: Entity) {
            set_local_in_continuation(lenv, cont::T::Next, lid, entity)
        }

        pub fn drop_cont(lenv: &mut Lenv, cont: cont::T) {
            lenv.remove(&cont);
        }

        pub fn drop_conts(lenv: &mut Lenv, conts: &[cont::T]) {
            for cont in conts {
                drop_cont(lenv, *cont)
            }
        }

        pub fn replace_cont(lenv: &mut Lenv, cont_key: cont::T, cont_opt: Option<LMap<Entity>>) {
            match cont_opt {
                None => drop_cont(lenv, cont_key),
                Some(cont) => {
                    lenv.insert(cont_key, cont);
                }
            }
        }

        pub fn restore_cont_from(lenv: &mut Lenv, from: &Lenv, cont_key: cont::T) {
            let ctxopt = from.get(&cont_key).cloned();
            replace_cont(lenv, cont_key, ctxopt)
        }

        pub fn restore_conts_from(lenv: &mut Lenv, from: &Lenv, conts: &[cont::T]) {
            for cont in conts {
                restore_cont_from(lenv, from, *cont)
            }
        }

        /// `Cont.Map.union_env [] lenv1 lenv2 ~combine`
        pub fn union(lenv1: &Lenv, lenv2: &Lenv) -> (Vec<Constraint_>, Lenv) {
            let mut constraints = vec![];
            let lenv = merge_env(&mut constraints, lenv1, lenv2, |constraints, _, o1, o2| match (o1, o2) {
                (None, None) => None,
                (Some(v), None) | (None, Some(v)) => Some(v.clone()),
                (Some(cont1), Some(cont2)) => Some(union_continuation(constraints, cont1, cont2)),
            });
            (constraints, lenv)
        }
    }

    pub fn init(tast_env: tast_env::Env, constraints: Vec<Constraint_>, bindings: LMap<Entity>) -> Env {
        Env {
            constraints,
            lenv: lenv::init(bindings),
            tast_env,
        }
    }

    pub fn add_constraint(env: &mut Env, constraint_: Constraint_) {
        env.constraints.insert(0, constraint_)
    }

    pub fn reset_constraints(env: &Env) -> Env {
        Env {
            constraints: vec![],
            ..env.clone()
        }
    }

    pub fn get_local(env: &Env, lid: &LocalId) -> Entity {
        lenv::get_local(&env.lenv, lid)
    }

    pub fn set_local(env: &mut Env, lid: LocalId, entity: Entity) {
        lenv::set_local(&mut env.lenv, lid, entity)
    }

    pub fn union(parent_env: Env, env1: Env, env2: Env) -> Env {
        let (points_to_constraints, lenv) = lenv::union(&env1.lenv, &env2.lenv);
        let mut constraints = points_to_constraints;
        constraints.extend(env1.constraints);
        constraints.extend(env2.constraints);
        constraints.extend(parent_env.constraints);
        Env {
            lenv,
            constraints,
            tast_env: parent_env.tast_env,
        }
    }

    pub fn drop_cont(env: &mut Env, cont: cont::T) {
        lenv::drop_cont(&mut env.lenv, cont)
    }

    pub fn drop_conts(env: &mut Env, conts: &[cont::T]) {
        lenv::drop_conts(&mut env.lenv, conts)
    }

    pub fn replace_cont(env: &mut Env, cont_key: cont::T, cont_opt: Option<LMap<Entity>>) {
        lenv::replace_cont(&mut env.lenv, cont_key, cont_opt)
    }

    pub fn restore_conts_from(env: &mut Env, from: &Lenv, conts: &[cont::T]) {
        lenv::restore_conts_from(&mut env.lenv, from, conts)
    }

    pub fn stash_and_do(env: &mut Env, conts: &[cont::T], f: impl FnOnce(&mut Env)) {
        let parent_locals = env.lenv.clone();
        drop_conts(env, conts);
        f(env);
        restore_conts_from(env, &parent_locals, conts)
    }

    fn union_cont_opt(
        constraints: &mut Vec<Constraint_>,
        cont_opt1: Option<LMap<Entity>>,
        cont_opt2: Option<LMap<Entity>>,
    ) -> Option<LMap<Entity>> {
        match (cont_opt1, cont_opt2) {
            (None, opt) | (opt, None) => opt,
            (Some(cont1), Some(cont2)) => Some(union_continuation(constraints, &cont1, &cont2)),
        }
    }

    /// Union a list of continuations
    fn union_conts(env: &mut Env, lenv: &Lenv, cont_keys: &[cont::T]) -> Option<LMap<Entity>> {
        let mut cont_opt = None;
        for cont_key in cont_keys {
            let cont_opt2 = lenv.get(cont_key).cloned();
            cont_opt = union_cont_opt(&mut env.constraints, cont_opt, cont_opt2);
        }
        cont_opt
    }

    /// Union a list of source continuations and store the result in a
    /// destination continuation.
    fn union_conts_and_update(env: &mut Env, from_conts: &[cont::T], to_cont: cont::T) {
        let lenv = env.lenv.clone();
        let unioned_cont = union_conts(env, &lenv, from_conts);
        replace_cont(env, to_cont, unioned_cont)
    }

    pub fn update_next_from_conts(env: &mut Env, from_conts: &[cont::T]) {
        union_conts_and_update(env, from_conts, cont::T::Next)
    }

    pub fn save_and_merge_next_in_cont(env: &mut Env, to_cont: cont::T) {
        union_conts_and_update(env, &[cont::T::Next, to_cont], to_cont)
    }

    pub fn move_and_merge_next_in_cont(env: &mut Env, cont_key: cont::T) {
        save_and_merge_next_in_cont(env, cont_key);
        drop_cont(env, cont::T::Next)
    }

    pub fn loop_continuation(cont_key: cont::T, env_before_iteration: &Env, mut env_after_iteration: Env) -> Env {
        let cont_before_iteration_opt = env_before_iteration.lenv.get(&cont_key);
        let cont_after_iteration_opt = env_after_iteration.lenv.get(&cont_key);
        let new_constraints = match (cont_before_iteration_opt, cont_after_iteration_opt) {
            (Some(cont_before_iteration), Some(cont_after_iteration)) => {
                let mut constraints = vec![];
                let _: LMap<Entity> = merge_env(
                    &mut constraints,
                    cont_before_iteration,
                    cont_after_iteration,
                    |constraints, _key, entity_before_opt, entity_after_opt| {
                        if let (Some(Some(entity_before)), Some(Some(entity_after))) =
                            (entity_before_opt, entity_after_opt)
                        {
                            prepend(
                                constraints,
                                vec![Constraint_::Subset(entity_after.clone(), entity_before.clone())],
                            )
                        }
                        None
                    },
                );
                constraints
            }
            _ => vec![],
        };
        prepend(&mut env_after_iteration.constraints, new_constraints);
        env_after_iteration
    }
}

/// `refactor_sd_walker.ml`
pub mod walker {
    use std::collections::BTreeMap;

    use naming_special_names_rust as sn;
    use oxidized::aast;
    use oxidized::ast_defs::Bop;
    use oxidized::ast_defs::Uop;

    use super::env;
    use super::types::*;
    use crate::aast_names_utils as utils;
    use crate::pos::Pos;
    use crate::provider_context;
    use crate::tast;
    use crate::tast_env;
    use crate::typing_continuations as cont;
    use crate::typing_defs_core::Ty_;

    fn failwithpos(pos: &Pos, msg: String) -> ! {
        refactor_sd_exn(format!("{}: {}", crate::ast_show::show_pos(pos), msg))
    }

    fn redirect(env: &mut Env, entity_: Entity_) -> Entity_ {
        let var = env::fresh_var();
        env::add_constraint(env, Constraint_::Subset(entity_, var.clone()));
        var
    }

    fn assign(env: &mut Env, lhs: &tast::Expr, rhs: Entity) {
        let aast::Expr(_, pos, lval) = lhs;
        match lval {
            aast::Expr_::Lvar(lid) => env::set_local(env, lid.1.clone(), rhs),
            aast::Expr_::ArrayGet(x) if matches!((x.0).2, aast::Expr_::Lvar(_)) => {
                let aast::Expr(vc_type, _, base) = &x.0;
                let lid = match base {
                    aast::Expr_::Lvar(lid) => lid.1.clone(),
                    _ => unreachable!(),
                };
                let entity = env::get_local(env, &lid);
                let ty = tast_env::expand_type(&mut env.tast_env, vc_type.clone());
                let (_, ty_) = crate::typing_defs_core::deref(&ty);
                let class_name = match &ty_ {
                    Ty_::Tclass(id, _, _) => Some(id.1.as_str()),
                    _ => None,
                };
                match (entity, class_name) {
                    (Some(entity_), Some(x)) if x == sn::collections::VEC || x == sn::collections::DICT => {
                        // Handle copy-on-write by creating a variable indirection
                        let var = redirect(env, entity_);
                        if let Some(rhs) = rhs {
                            env::add_constraint(env, Constraint_::Subset(rhs, var.clone()))
                        }
                        env::set_local(env, lid, Some(var))
                    }
                    (Some(entity_), Some(x)) if x == sn::collections::VECTOR => {
                        if let Some(rhs) = rhs {
                            env::add_constraint(env, Constraint_::Subset(rhs, entity_.clone()))
                        }
                        env::set_local(env, lid, Some(entity_))
                    }
                    (Some(_), _) => failwithpos(pos, format!("Unsupported lvalue: {}", utils::expr_name(lval))),
                    (None, _) => {
                        // We might end up here as a result of deadcode, such as a dictionary
                        // assignment after an unconditional break in a loop. In this
                        // situation, it is not meaningful to report a candidate.
                    }
                }
            }
            _ => failwithpos(pos, format!("Unsupported lvalue: {}", utils::expr_name(lval))),
        }
    }

    /// Create a join point entity. It is pretty much Option.marge except that
    /// that function doesn't allow threading state (`env`) through
    fn join(env: &mut Env, then_entity: Entity, else_entity: Entity) -> Entity {
        match (then_entity, else_entity) {
            (Some(then_entity_), Some(else_entity_)) => {
                let var = env::fresh_var();
                env::add_constraint(env, Constraint_::Subset(then_entity_, var.clone()));
                env::add_constraint(env, Constraint_::Subset(else_entity_, var.clone()));
                Some(var)
            }
            (None, else_entity @ Some(_)) => else_entity,
            (then_entity, _) => then_entity,
        }
    }

    /// Handle copy-on-write by creating a variable indirection
    fn introduction(env: &mut Env, pos: &Pos) -> Entity {
        let entity_ = Entity_::Literal(pos.clone());
        env::add_constraint(env, Constraint_::Introduction(pos.clone()));
        let var = redirect(env, entity_);
        Some(var)
    }

    fn expr_(upcasted_info: &ElementInfo, env: &mut Env, expr: &tast::Expr) -> Entity {
        use aast::Expr_ as E;
        let aast::Expr(_ty, pos, e) = expr;
        let unsupported = || -> ! { failwithpos(pos, format!("Unsupported expression: {}", utils::expr_name(e))) };
        match e {
            E::Int(_) | E::Float(_) | E::String(_) | E::Null | E::True | E::False => None,
            // Until interprocedural analaysis has been implemented, this is all incomplete.
            E::Id(_) => None,
            E::Lvar(lid) => env::get_local(env, &lid.1),
            E::Unop(x)
                if matches!(
                    x.0,
                    Uop::Utild
                        | Uop::Unot
                        | Uop::Uplus
                        | Uop::Uminus
                        | Uop::Uincr
                        | Uop::Udecr
                        | Uop::Upincr
                        | Uop::Updecr
                        | Uop::Usilence
                ) =>
            {
                // unary operations won't return function pointrs, so we discard the entity.
                let _ = expr_(upcasted_info, env, &x.1);
                None
            }
            E::Assign(x) if x.1.is_none() => {
                let (e1, _, e2) = &**x;
                let entity_rhs = expr_(upcasted_info, env, e2);
                assign(env, e1, entity_rhs);
                None
            }
            E::Binop(x) if matches!(x.bop, Bop::QuestionQuestion) => {
                let entity1 = expr_(upcasted_info, env, &x.lhs);
                let entity2 = expr_(upcasted_info, env, &x.rhs);
                join(env, entity1, entity2)
            }
            E::Assign(x) if matches!(x.1, Some(Bop::QuestionQuestion)) => {
                let (e1, _, e2) = &**x;
                let entity1 = expr_(upcasted_info, env, e1);
                let entity2 = expr_(upcasted_info, env, e2);
                let entity_rhs = join(env, entity1, entity2);
                assign(env, e1, entity_rhs);
                None
            }
            E::Binop(x)
                if matches!(
                    x.bop,
                    Bop::Plus
                        | Bop::Minus
                        | Bop::Star
                        | Bop::Slash
                        | Bop::Eqeq
                        | Bop::Eqeqeq
                        | Bop::Starstar
                        | Bop::Diff
                        | Bop::Diff2
                        | Bop::Ampamp
                        | Bop::Barbar
                        | Bop::Lt
                        | Bop::Lte
                        | Bop::Gt
                        | Bop::Gte
                        | Bop::Dot
                        | Bop::Amp
                        | Bop::Bar
                        | Bop::Ltlt
                        | Bop::Gtgt
                        | Bop::Percent
                        | Bop::Xor
                        | Bop::Cmp
                ) =>
            {
                // most binary operations won't return function pointers, so we discard the entity.
                let _ = expr_(upcasted_info, env, &x.lhs);
                let _ = expr_(upcasted_info, env, &x.rhs);
                None
            }
            E::KeyValCollection(x) => match (x.0).1 {
                aast::KvcKind::Dict => {
                    let var = env::fresh_var();
                    for aast::Field(_e_key, e_val) in &x.2 {
                        if let Some(entity_rhs_) = expr_(upcasted_info, env, e_val) {
                            env::add_constraint(env, Constraint_::Subset(entity_rhs_, var.clone()))
                        }
                    }
                    Some(var)
                }
                _ => unsupported(),
            },
            E::ValCollection(x) => match (x.0).1 {
                aast::VcKind::Vector | aast::VcKind::Vec => {
                    let var = env::fresh_var();
                    for e_inner in &x.2 {
                        if let Some(entity_rhs_) = expr_(upcasted_info, env, e_inner) {
                            env::add_constraint(env, Constraint_::Subset(entity_rhs_, var.clone()))
                        }
                    }
                    Some(var)
                }
                _ => unsupported(),
            },
            E::ArrayGet(x) if matches!((x.0).2, E::Lvar(_)) && x.1.is_some() => {
                let (base, ix) = &**x;
                let entity_exp = expr_(upcasted_info, env, base);
                let _entity_ix = expr_(upcasted_info, env, ix.as_ref().unwrap());
                entity_exp
            }
            E::Upcast(x) => {
                let entity = expr_(upcasted_info, env, &x.0);
                if let Some(entity) = &entity {
                    env::add_constraint(env, Constraint_::Upcast(entity.clone(), pos.clone()))
                }
                entity
            }
            E::Call(call) => {
                // Until interprocedural analaysis has been implemented, this is all incomplete.
                let entity = expr_(upcasted_info, env, &call.func);
                for arg in &call.args {
                    let _ = expr_(upcasted_info, env, crate::aast_utils::arg_to_expr(arg));
                }
                if let Some(entity) = entity {
                    let location = Entity_::Literal(pos.clone());
                    env::add_constraint(env, Constraint_::Subset(entity, location));
                    env::add_constraint(env, Constraint_::Called(pos.clone()))
                }
                None
            }
            E::ObjGet(x) => {
                let (e_obj, e_meth, _, _) = &**x;
                let entity_obj = expr_(upcasted_info, env, e_obj);
                let _entity_meth = expr_(upcasted_info, env, e_meth);
                match entity_obj {
                    Some(entity) => {
                        let location = Entity_::Literal(pos.clone());
                        env::add_constraint(env, Constraint_::Subset(entity.clone(), location));
                        env::add_constraint(env, Constraint_::Called(pos.clone()));
                        Some(entity)
                    }
                    None => None,
                }
            }
            E::FunctionPointer(x) if matches!(x.0, aast::FunctionPtrId::FPId(_)) => {
                let id = match &x.0 {
                    aast::FunctionPtrId::FPId(id) => &id.1,
                    _ => unreachable!(),
                };
                if &upcasted_info.element_name == id {
                    introduction(env, pos)
                } else {
                    None
                }
            }
            E::New(x) if matches!((x.0).2, aast::ClassId_::CI(_)) => {
                let (aast::ClassId(_, _, cid), _, arg_list, e, _) = &**x;
                let id = match cid {
                    aast::ClassId_::CI(id) => &id.1,
                    _ => unreachable!(),
                };
                if &upcasted_info.element_name == id {
                    for arg in arg_list {
                        let _entity_rhs = expr_(upcasted_info, env, crate::aast_utils::arg_to_expr(arg));
                    }
                    if let Some(e) = e {
                        let _ = expr_(upcasted_info, env, e);
                    }
                    introduction(env, pos)
                } else {
                    None
                }
            }
            E::ClassConst(x) if matches!((x.0).2, aast::ClassId_::CI(_)) => {
                let (aast::ClassId(_, _, cid), (_, method_id)) = &**x;
                let id = match cid {
                    aast::ClassId_::CI(id) => &id.1,
                    _ => unreachable!(),
                };
                let equals_method_id = method_id == "class";
                if &upcasted_info.element_name == id && equals_method_id {
                    introduction(env, pos)
                } else {
                    None
                }
            }
            // Eventually, we should be able to track method pointers inside a class, i.e.
            // also track the following expression with A.CIexpr (_, _, This).
            E::ClassConst(x) if matches!((x.0).2, aast::ClassId_::CIexpr(_)) => match &(x.0).2 {
                aast::ClassId_::CIexpr(e_obj) => expr_(upcasted_info, env, e_obj),
                _ => unreachable!(),
            },
            E::Eif(x) if x.1.is_some() => {
                let (cond, then_expr, else_expr) = &**x;
                let _cond_entity = expr_(upcasted_info, env, cond);
                let parent_env = env.clone();
                let base_env = env::reset_constraints(&parent_env);
                let mut then_env = base_env.clone();
                let then_entity = expr_(upcasted_info, &mut then_env, then_expr.as_ref().unwrap());
                let mut else_env = base_env;
                let else_entity = expr_(upcasted_info, &mut else_env, else_expr);
                *env = env::union(parent_env, then_env, else_env);
                join(env, then_entity, else_entity)
            }
            E::Eif(x) => {
                let (cond, _, else_expr) = &**x;
                let cond_entity = expr_(upcasted_info, env, cond);
                let else_entity = expr_(upcasted_info, env, else_expr);
                join(env, cond_entity, else_entity)
            }
            E::Await(e) => expr_(upcasted_info, env, e),
            E::As(x) => expr_(upcasted_info, env, &x.expr),
            E::Is(x) => {
                // `is` expressions always evaluate to bools, so we discard the entity.
                let _ = expr_(upcasted_info, env, &x.0);
                None
            }
            _ => unsupported(),
        }
    }

    fn expr(upcasted_info: &ElementInfo, env: &mut Env, e: &tast::Expr) {
        let _ = expr_(upcasted_info, env, e);
    }

    fn switch(
        upcasted_info: &ElementInfo,
        parent_locals: &Lenv,
        env: &mut Env,
        cases: &[aast::Case<tast::Ty, tast::SavedEnv>],
        dfl: &Option<aast::DefaultCase<tast::Ty, tast::SavedEnv>>,
    ) {
        let initialize_next_cont = |env: &mut Env| {
            env::restore_conts_from(env, parent_locals, &[cont::T::Next]);
            env::update_next_from_conts(env, &[cont::T::Next, cont::T::Fallthrough]);
            env::drop_cont(env, cont::T::Fallthrough)
        };
        for aast::Case(e, b) in cases {
            initialize_next_cont(env);
            expr(upcasted_info, env, e);
            block(upcasted_info, env, b)
        }
        if let Some(aast::DefaultCase(_, b)) = dfl {
            initialize_next_cont(env);
            block(upcasted_info, env, b)
        }
    }

    fn stmt(upcasted_info: &ElementInfo, env: &mut Env, s: &tast::Stmt) {
        use aast::Stmt_ as S;
        let aast::Stmt(pos, stmt) = s;
        match stmt {
            S::Expr(e) => expr(upcasted_info, env, e),
            S::Return(e) => {
                if let Some(e) = &**e {
                    let _expr = expr_(upcasted_info, env, e);
                }
            }
            S::If(x) => {
                let (cond, then_bl, else_bl) = &**x;
                expr(upcasted_info, env, cond);
                let parent_env = env.clone();
                let base_env = env::reset_constraints(&parent_env);
                let mut then_env = base_env.clone();
                block(upcasted_info, &mut then_env, then_bl);
                let mut else_env = base_env;
                block(upcasted_info, &mut else_env, else_bl);
                *env = env::union(parent_env, then_env, else_env)
            }
            S::Switch(x) => {
                let (cond, cases, dfl) = &**x;
                expr(upcasted_info, env, cond);
                // NB: A 'continue' inside a 'switch' block is equivalent to a 'break'.
                // See the note in
                // http://php.net/manual/en/control-structures.continue.php
                env::stash_and_do(env, &[cont::T::Continue, cont::T::Break], |env| {
                    let parent_locals = env.lenv.clone();
                    switch(upcasted_info, &parent_locals, env, cases, dfl);
                    env::update_next_from_conts(env, &[cont::T::Continue, cont::T::Break, cont::T::Next])
                })
            }
            S::Fallthrough => env::move_and_merge_next_in_cont(env, cont::T::Fallthrough),
            S::Continue => env::move_and_merge_next_in_cont(env, cont::T::Continue),
            S::Break => env::move_and_merge_next_in_cont(env, cont::T::Break),
            S::While(x) => {
                let (aast::LoopCond(_, _, cond), bl) = &**x;
                env::stash_and_do(env, &[cont::T::Continue, cont::T::Break], |env| {
                    env::save_and_merge_next_in_cont(env, cont::T::Continue);
                    let env_before_iteration = env.clone();
                    let env_after_iteration = {
                        let mut env = env.clone();
                        expr(upcasted_info, &mut env, cond);
                        block(upcasted_info, &mut env, bl);
                        env
                    };
                    *env = env::loop_continuation(cont::T::Next, &env_before_iteration, env_after_iteration);
                    env::update_next_from_conts(env, &[cont::T::Continue, cont::T::Next]);
                    expr(upcasted_info, env, cond);
                    env::update_next_from_conts(env, &[cont::T::Break, cont::T::Next])
                })
            }
            S::Noop | S::Markup(_) => {}
            _ => failwithpos(pos, format!("Unsupported statement: {}", utils::stmt_name(stmt))),
        }
    }

    fn block(upcasted_info: &ElementInfo, env: &mut Env, b: &tast::Block) {
        for s in &b.0 {
            stmt(upcasted_info, env, s)
        }
    }

    fn init_params(_tast_env: &tast_env::Env, _params: &[tast::FunParam]) -> (Vec<Constraint_>, LMap<Entity>) {
        (vec![], LMap::new())
    }

    pub fn callable(
        upcasted_info: &ElementInfo,
        tast_env: &tast_env::Env,
        params: &[tast::FunParam],
        body: &tast::FuncBody,
    ) -> Vec<Constraint_> {
        let (param_constraints, param_env) = init_params(tast_env, params);
        let mut env = env::init(tast_env.clone(), param_constraints, param_env);
        block(upcasted_info, &mut env, &body.fb_ast);
        env.constraints
    }

    /// (`S_map.of_list`: of two bindings of a name, the last one.)
    pub fn program(
        upcasted_info: &ElementInfo,
        ctx: &provider_context::T,
        tast: &[tast::Def],
    ) -> BTreeMap<String, Vec<Constraint_>> {
        let mut map = BTreeMap::new();
        for def in tast {
            let tast_env = tast_env::def_env(ctx, def);
            match def {
                aast::Def::Fun(fd) => {
                    let id = fd.name.1.clone();
                    map.insert(id, callable(upcasted_info, &tast_env, &fd.fun.params, &fd.fun.body));
                }
                aast::Def::Class(c) => {
                    let class_name = &c.name.1;
                    for m in &c.methods {
                        let id = format!("{}::{}", class_name, m.name.1);
                        map.insert(id, callable(upcasted_info, &tast_env, &m.params, &m.body));
                    }
                }
                _ => panic!("Failure(\"A definition is not yet handled\")"),
            }
        }
        map
    }
}

/// `refactor_sd_solver.ml`
pub mod solver {
    use std::collections::BTreeMap;
    use std::collections::BTreeSet;

    use super::types::*;
    use crate::pos::Pos;

    type PointsToSet = BTreeSet<(Entity_, Entity_)>;
    type EntityMap<V> = BTreeMap<Entity_, V>;
    type EntitySet = BTreeSet<Entity_>;

    #[derive(Default)]
    struct Constraints {
        introductions: Vec<Pos>,
        subsets: Vec<(Entity_, Entity_)>,
        upcasts: Vec<(Entity_, Pos)>,
        calleds: Vec<Pos>,
    }

    fn transitive_closure(mut set: PointsToSet) -> PointsToSet {
        loop {
            // `PointsToSet.fold immediate_consequence set set`
            let mut new_set = set.clone();
            for (x, y) in &set {
                // `PointsToSet.fold add set set` (the set as it is then)
                let snapshot = new_set.clone();
                for (y_, z) in &snapshot {
                    if y == y_ {
                        new_set.insert((x.clone(), z.clone()));
                    }
                }
            }
            if new_set.len() == set.len() {
                return set;
            }
            set = new_set
        }
    }

    fn find_pointers(introductions: &[Pos], set: &PointsToSet) -> PointsToSet {
        let mut has_pointer_set = PointsToSet::new();
        for pointer_pos in introductions {
            has_pointer_set.extend(
                set.iter()
                    .filter(|(sub, _)| matches!(sub, Entity_::Literal(pos) if pointer_pos == pos))
                    .cloned(),
            )
        }
        has_pointer_set
    }

    fn find_calls(introductions: &[Pos], set: &PointsToSet) -> PointsToSet {
        let mut called_set = PointsToSet::new();
        for called_pos in introductions {
            called_set.extend(
                set.iter()
                    .filter(|(_, sup)| matches!(sup, Entity_::Literal(pos) if called_pos == pos))
                    .cloned(),
            )
        }
        called_set
    }

    /// (The positions are a list whose head is the last one added.)
    fn remove_duplicates(mut positions: Vec<Pos>, (_entity, pos): (Entity_, Pos)) -> Vec<Pos> {
        if !positions.contains(&pos) {
            positions.insert(0, pos)
        }
        positions
    }

    fn partition_constraint(mut constraints: Constraints, c: &Constraint_) -> Constraints {
        match c {
            Constraint_::Introduction(pos) => constraints.introductions.insert(0, pos.clone()),
            Constraint_::Subset(sub, sup) => constraints.subsets.insert(0, (sub.clone(), sup.clone())),
            Constraint_::Upcast(entity, pos) => constraints.upcasts.insert(0, (entity.clone(), pos.clone())),
            Constraint_::Called(pos) => constraints.calleds.insert(0, pos.clone()),
        }
        constraints
    }

    type Collect = Box<dyn Fn(&(Entity_, Pos)) -> Vec<(Entity_, Pos)>>;

    fn subset_lookups(subsets: &PointsToSet) -> (Collect, Collect) {
        let mut subset_map: EntityMap<EntitySet> = EntityMap::new();
        let mut superset_map: EntityMap<EntitySet> = EntityMap::new();
        for (e, e_) in subsets {
            subset_map.entry(e_.clone()).or_default().insert(e.clone());
            superset_map.entry(e.clone()).or_default().insert(e_.clone());
        }
        // Generate lookup functions. This code is different from shape_analysis.
        fn collect(map: EntityMap<EntitySet>) -> Collect {
            Box::new(move |(entity, pos)| match map.get(entity) {
                Some(entities) => entities.iter().map(|ent| (ent.clone(), pos.clone())).collect(),
                None => vec![],
            })
        }
        (collect(subset_map), collect(superset_map))
    }

    pub fn simplify(constraints: &[Constraint_]) -> Vec<RefactorSdResult> {
        let Constraints {
            introductions,
            upcasts,
            subsets,
            calleds,
        } = constraints.iter().fold(Constraints::default(), partition_constraint);
        let subsets = transitive_closure(subsets.into_iter().collect());
        // Limit upcasts to functions of interest
        let subsets_pointers = find_pointers(&introductions, &subsets);
        let (collect_subsets_to_pointers, _collect_supersets_to_pointers) = subset_lookups(&subsets_pointers);
        let upcasts: Vec<(Entity_, Pos)> = upcasts.iter().flat_map(|u| collect_subsets_to_pointers(u)).collect();
        // Limit upcasts to functions that are later called
        let subsets_calls = find_calls(&calleds, &subsets);
        let (_collect_subsets_to_calls, collect_supersets_to_calls) = subset_lookups(&subsets_calls);
        let upcasts: Vec<(Entity_, Pos)> = upcasts.iter().flat_map(|u| collect_supersets_to_calls(u)).collect();
        // Remove duplicates. Duplicates occur when reassigning variables or using a mutable collection.
        let upcast_pos = upcasts.into_iter().fold(vec![], remove_duplicates);
        // Convert to individual upcast results
        let exists_upcast_results: Vec<RefactorSdResult> =
            upcast_pos.into_iter().map(RefactorSdResult::ExistsUpcast).collect();
        if exists_upcast_results.is_empty() {
            vec![RefactorSdResult::NoUpcast]
        } else {
            exists_upcast_results
        }
    }
}

use types::*;

fn add_ns(name: &str) -> String {
    if name.starts_with('\\') {
        name.to_string()
    } else {
        format!("\\{}", name)
    }
}

/// `do_ upcasted_id options ctx tast`
pub fn do_(upcasted_id: &str, options: &Options, ctx: &crate::provider_context::T, tast: &[crate::tast::Def]) {
    let upcasted_id = add_ns(upcasted_id);
    let upcasted_info = ElementInfo {
        element_name: upcasted_id,
    };
    match options.analysis_mode {
        AnalysisMode::FlagTargets => {}
        AnalysisMode::DumpConstraints => {
            for (id, constraints) in walker::program(&upcasted_info, ctx, tast) {
                println!("Constraints for {}:", id);
                let mut shown: Vec<String> = constraints.iter().map(pretty_printer::show_constraint_).collect();
                shown.sort_by(|a, b| a.as_bytes().cmp(b.as_bytes()));
                for s in shown {
                    println!("{}", s)
                }
                println!()
            }
        }
        AnalysisMode::SimplifyConstraints => {
            for (id, constraints) in walker::program(&upcasted_info, ctx, tast) {
                let results = solver::simplify(&constraints);
                println!("Summary for {}:", id);
                for result in &results {
                    println!("{}", pretty_printer::show_refactor_sd_result(result))
                }
            }
        }
        AnalysisMode::SolveConstraints => {}
    }
}

pub fn contains_upcast(r: &RefactorSdResult) -> bool {
    matches!(r, RefactorSdResult::ExistsUpcast(_))
}
