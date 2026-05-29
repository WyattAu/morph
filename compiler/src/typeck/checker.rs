use std::collections::HashMap;

use crate::ast::{
    self, ActorDecl, ActorMember, BinOp, Capability, ConstDecl, EffectSet as AstEffectSet, Expr,
    FnDecl, ImplBlock, Item, Literal, MatchArm, Node, NodeId, Pattern, Stmt, TraitDecl, Type,
    TypeBody, TypeDecl, UnOp, Visibility,
};
use crate::diagnostic::Diagnostic;
use crate::lexer::token::Span;
use crate::typeck::env::TypeEnv;
use crate::typeck::errors::TypeError;
use crate::typeck::result::TypeCheckResult;
use crate::typeck::types::{
    self, can_coerce_int_literal, float_kind_from_name, int_kind_from_name, EffectSet, FloatKind,
    IntKind, Ty,
};
use crate::typeck::unification::{self, Substitution};

pub struct TypeChecker {
    env: TypeEnv,
    diagnostics: Vec<Diagnostic>,
    type_var_counter: u32,
    type_map: HashMap<NodeId, Ty>,
    effect_map: HashMap<NodeId, EffectSet>,
    current_effects: EffectSet,
    current_actor: Option<String>,
    type_defs: HashMap<String, TypeDefInfo>,
    fn_sigs: HashMap<String, FnSigInfo>,
    return_type: Option<Ty>,
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
struct TypeDefInfo {
    name: String,
    visibility: Visibility,
    body: TypeDefBody,
}

#[derive(Debug, Clone)]
enum TypeDefBody {
    Struct(Vec<(String, Ty)>),
    Enum(Vec<(String, Vec<Ty>)>),
    Alias(()),
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
struct FnSigInfo {
    params: Vec<(String, Ty)>,
    ret: Ty,
    effects: EffectSet,
}

impl Default for TypeChecker {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeChecker {
    pub fn new() -> Self {
        Self {
            env: TypeEnv::new(),
            diagnostics: Vec::new(),
            type_var_counter: 0,
            type_map: HashMap::new(),
            effect_map: HashMap::new(),
            current_effects: EffectSet::empty(),
            current_actor: None,
            type_defs: HashMap::new(),
            fn_sigs: HashMap::new(),
            return_type: None,
        }
    }

    pub fn check_program(items: &[Node<Item>]) -> Result<TypeCheckResult, Vec<Diagnostic>> {
        let mut checker = Self::new();
        checker.collect_items(items);
        for item in items {
            checker.check_item(item);
        }
        if checker
            .diagnostics
            .iter()
            .any(|d| d.level == crate::diagnostic::DiagnosticLevel::Error)
        {
            Err(checker.diagnostics)
        } else {
            Ok(TypeCheckResult::new(
                checker.type_map,
                checker.effect_map,
                checker
                    .diagnostics
                    .into_iter()
                    .filter(|d| d.level == crate::diagnostic::DiagnosticLevel::Warning)
                    .collect(),
            ))
        }
    }

    fn collect_items(&mut self, items: &[Node<Item>]) {
        for item in items {
            match &item.kind {
                Item::FnDecl(f) => {
                    self.collect_fn_sig(f);
                }
                Item::TypeDecl(t) => {
                    self.collect_type_decl(t);
                }
                Item::ActorDecl(a) => {
                    self.collect_actor_decl(a);
                }
                _ => {}
            }
        }
    }

    fn collect_fn_sig(&mut self, decl: &FnDecl) {
        let params: Vec<(String, Ty)> = decl
            .params
            .iter()
            .map(|p| {
                let ty = p
                    .kind
                    .type_ann
                    .as_ref()
                    .map(|t| self.resolve_type(t))
                    .unwrap_or_else(|| Ty::Error);
                (p.kind.name.clone(), ty)
            })
            .collect();
        let ret = decl
            .return_type
            .as_ref()
            .map(|t| self.resolve_type(t))
            .unwrap_or(Ty::Void);
        let effects = decl
            .effects
            .as_ref()
            .map(|e| self.convert_effect_set(e))
            .unwrap_or_else(EffectSet::empty);
        self.fn_sigs.insert(
            decl.name.clone(),
            FnSigInfo {
                params,
                ret,
                effects,
            },
        );
    }

    fn collect_type_decl(&mut self, decl: &TypeDecl) {
        let body = match &decl.body {
            TypeBody::Struct(fields) => {
                let resolved: Vec<(String, Ty)> = fields
                    .iter()
                    .map(|f| (f.kind.name.clone(), self.resolve_type(&f.kind.type_ann)))
                    .collect();
                TypeDefBody::Struct(resolved)
            }
            TypeBody::Enum(variants) => {
                let resolved: Vec<(String, Vec<Ty>)> = variants
                    .iter()
                    .map(|v| {
                        let field_tys: Vec<Ty> =
                            v.kind.fields.iter().map(|t| self.resolve_type(t)).collect();
                        (v.kind.name.clone(), field_tys)
                    })
                    .collect();
                TypeDefBody::Enum(resolved)
            }
            TypeBody::Alias(_) => TypeDefBody::Alias(()),
        };
        self.type_defs.insert(
            decl.name.clone(),
            TypeDefInfo {
                name: decl.name.clone(),
                visibility: decl.visibility,
                body,
            },
        );
    }

    fn collect_actor_decl(&mut self, decl: &ActorDecl) {
        let actor_ty = Ty::Actor(decl.name.clone());
        self.env.insert_var(decl.name.clone(), actor_ty);
    }

    fn convert_effect_set(&self, ast_set: &AstEffectSet) -> EffectSet {
        let effects: Vec<types::Effect> = ast_set
            .effects
            .iter()
            .filter_map(|e| match e {
                ast::Effect::Pure => None,
                ast::Effect::IO => Some(types::Effect::IO),
                ast::Effect::Net => Some(types::Effect::Net),
                ast::Effect::Time => Some(types::Effect::Time),
                ast::Effect::System => Some(types::Effect::System),
            })
            .collect();
        EffectSet::new(effects)
    }

    fn check_item(&mut self, item: &Node<Item>) {
        match &item.kind {
            Item::FnDecl(f) => self.check_fn_decl(f, item.span),
            Item::TypeDecl(t) => self.check_type_decl(t),
            Item::ConstDecl(c) => self.check_const_decl(c),
            Item::UseDecl(_) => {}
            Item::ActorDecl(a) => self.check_actor_decl(a),
            Item::ImplBlock(i) => self.check_impl_block(i),
            Item::TraitDecl(t) => self.check_trait_decl(t),
        }
    }

    fn check_fn_decl(&mut self, decl: &FnDecl, span: Span) {
        let saved_env = self.env.clone();
        let saved_effects = self.current_effects.clone();
        let saved_return = self.return_type.clone();

        let param_tys: Vec<(String, Ty)> = decl
            .params
            .iter()
            .map(|p| {
                let ty = p
                    .kind
                    .type_ann
                    .as_ref()
                    .map(|t| self.resolve_type(t))
                    .unwrap_or_else(|| Ty::Error);
                (p.kind.name.clone(), ty)
            })
            .collect();

        for (name, ty) in &param_tys {
            self.env.insert_var(name.clone(), ty.clone());
        }

        let ret_ty = decl
            .return_type
            .as_ref()
            .map(|t| self.resolve_type(t))
            .unwrap_or(Ty::Void);

        self.return_type = Some(ret_ty.clone());
        self.current_effects = decl
            .effects
            .as_ref()
            .map(|e| self.convert_effect_set(e))
            .unwrap_or_else(EffectSet::empty);

        let body_ty = self.infer_expr(&decl.body);

        if !matches!(body_ty, Ty::Never | Ty::Error) && !matches!(ret_ty, Ty::Void | Ty::Error) {
            let mut subst = Substitution::new();
            if let Err(err) = unification::unify(&body_ty, &ret_ty, &mut subst, decl.body.span) {
                self.emit_type_error(err);
            }
        }

        let _ = span;
        self.env = saved_env;
        self.current_effects = saved_effects;
        self.return_type = saved_return;
    }

    fn check_type_decl(&mut self, _decl: &TypeDecl) {}

    fn check_const_decl(&mut self, decl: &ConstDecl) {
        let expected = self.resolve_type(&decl.type_ann);
        let found = self.infer_expr(&decl.value);
        let mut subst = Substitution::new();
        if let Err(err) = unification::unify(&found, &expected, &mut subst, decl.value.span) {
            self.emit_type_error(err);
        }
        self.env.insert_var(decl.name.clone(), expected);
    }

    fn check_actor_decl(&mut self, decl: &ActorDecl) {
        let saved_actor = self.current_actor.clone();
        let saved_env = self.env.clone();
        self.current_actor = Some(decl.name.clone());

        for member in &decl.members {
            match &member.kind {
                ActorMember::State {
                    name,
                    type_ann,
                    init,
                } => {
                    let ty = self.resolve_type(type_ann);
                    if let Some(init_expr) = init {
                        let init_ty = self.infer_expr(init_expr);
                        let mut subst = Substitution::new();
                        if let Err(err) =
                            unification::unify(&init_ty, &ty, &mut subst, init_expr.span)
                        {
                            self.emit_type_error(err);
                        }
                    }
                    self.env.insert_var(name.clone(), ty);
                }
                ActorMember::Event { name, params } => {
                    let param_tys: Vec<Ty> = params
                        .iter()
                        .map(|p| {
                            p.kind
                                .type_ann
                                .as_ref()
                                .map(|t| self.resolve_type(t))
                                .unwrap_or(Ty::Error)
                        })
                        .collect();
                    let event_ty = Ty::Tuple(param_tys);
                    self.env.insert_var(name.clone(), event_ty);
                }
                ActorMember::OnHandler { body, .. } => {
                    let _body_ty = self.infer_expr(body);
                }
                ActorMember::FnMember(f) => {
                    self.check_fn_decl(f, member.span);
                }
            }
        }

        self.current_actor = saved_actor;
        self.env = saved_env;
    }

    fn check_impl_block(&mut self, block: &ImplBlock) {
        for method in &block.methods {
            self.check_fn_decl(&method.kind, method.span);
        }
    }

    fn check_trait_decl(&mut self, _decl: &TraitDecl) {}

    fn infer_expr(&mut self, expr: &Node<Expr>) -> Ty {
        let ty = match &expr.kind {
            Expr::Literal(lit) => self.infer_literal(lit, None),

            Expr::Var(name) => {
                if self.env.is_consumed(name) {
                    self.emit_error(
                        "E002",
                        format!("use after move: variable {} was consumed", name),
                        expr.span,
                    );
                    Ty::Error
                } else if let Some(ty) = self.env.lookup(name) {
                    ty.clone()
                } else {
                    self.emit_error("E001", format!("undefined variable: {}", name), expr.span);
                    Ty::Error
                }
            }

            Expr::BinaryOp { op, lhs, rhs } => self.infer_binop(*op, lhs, rhs, expr.span),

            Expr::UnaryOp { op, operand } => self.infer_unop(*op, operand),

            Expr::Call { callee, args } => self.infer_call(callee, args, expr.span),

            Expr::FieldAccess { object, field } => {
                self.infer_field_access(object, field, expr.span)
            }

            Expr::Index { object, index } => self.infer_index(object, index, expr.span),

            Expr::Lambda { params, body } => self.infer_lambda(params, body),

            Expr::If {
                condition,
                then_branch,
                else_branch,
            } => self.infer_if(condition, then_branch, else_branch, expr.span),

            Expr::Match { scrutinee, arms } => self.infer_match(scrutinee, arms, expr.span),

            Expr::Block { stmts, expr: tail } => self.infer_block(stmts, tail),

            Expr::Pipe { lhs, rhs } => self.infer_pipe(lhs, rhs),

            Expr::ErrorPropagate { expr: inner } => self.infer_error_propagate(inner, expr.span),

            Expr::NullCoalesce { lhs, rhs } => self.infer_null_coalesce(lhs, rhs),

            Expr::Async { expr: inner } => self.infer_expr(inner),

            Expr::Spawn { expr: inner } => {
                let inner_ty = self.infer_expr(inner);
                if self.current_actor.is_some() && !inner_ty.is_sendable() {
                    self.emit_error(
                        "E004",
                        format!("cannot send {} across actor boundary", inner_ty),
                        expr.span,
                    );
                }
                inner_ty
            }

            Expr::StructInit { name, fields } => self.infer_struct_init(name, fields, expr.span),

            Expr::Walrus {
                name,
                value,
                type_ann,
            } => self.infer_walrus(name, value, type_ann),
        };

        self.type_map.insert(expr.id, ty.clone());
        ty
    }

    #[allow(dead_code)]
    fn check_expr(&mut self, expr: &Node<Expr>, expected: &Ty) -> Ty {
        let inferred = match &expr.kind {
            Expr::Literal(lit) => self.infer_literal(lit, Some(expected)),
            _ => self.infer_expr(expr),
        };

        let mut subst = Substitution::new();
        if let Err(err) = unification::unify(&inferred, expected, &mut subst, expr.span) {
            self.emit_type_error(err);
            return inferred;
        }

        let resolved = unification::apply_subst(&subst, &inferred);
        self.type_map.insert(expr.id, resolved.clone());
        resolved
    }

    fn check_stmt(&mut self, stmt: &Node<Stmt>) {
        match &stmt.kind {
            Stmt::ExprStmt(expr) => {
                self.infer_expr(expr);
            }
            Stmt::VarDecl {
                name,
                type_ann,
                value,
            } => {
                let value_ty = self.infer_expr(value);
                let ty = if let Some(ann) = type_ann {
                    let expected = self.resolve_type(ann);
                    let mut subst = Substitution::new();
                    if let Err(err) =
                        unification::unify(&value_ty, &expected, &mut subst, value.span)
                    {
                        self.emit_type_error(err);
                    }
                    unification::apply_subst(&subst, &expected)
                } else {
                    value_ty
                };
                self.env.insert_var(name.clone(), ty);
            }
            Stmt::Assign { target, value } => {
                let target_ty = self.infer_expr(target);
                let value_ty = self.infer_expr(value);
                let mut subst = Substitution::new();
                if let Err(err) = unification::unify(&value_ty, &target_ty, &mut subst, target.span)
                {
                    self.emit_type_error(err);
                }
            }
            Stmt::Return(expr) => {
                if let Some(ret_expr) = expr {
                    let ret_ty = self.infer_expr(ret_expr);
                    if let Some(ref expected) = self.return_type {
                        let mut subst = Substitution::new();
                        if let Err(err) =
                            unification::unify(&ret_ty, expected, &mut subst, ret_expr.span)
                        {
                            self.emit_type_error(err);
                        }
                    }
                }
            }
            Stmt::Defer(expr) => {
                self.infer_expr(expr);
            }
            Stmt::Break | Stmt::Continue | Stmt::Nop => {}
            Stmt::While { condition, body } => {
                let cond_ty = self.infer_expr(condition);
                let mut subst = Substitution::new();
                if let Err(err) =
                    unification::unify(&cond_ty, &Ty::Bool, &mut subst, condition.span)
                {
                    self.emit_type_error(err);
                }
                for s in body {
                    self.check_stmt(s);
                }
            }
        }
    }

    fn infer_literal(&self, lit: &Literal, expected: Option<&Ty>) -> Ty {
        match lit {
            Literal::Bool(_) => Ty::Bool,
            Literal::Int(val) => {
                if let Some(expected) = expected {
                    match expected {
                        Ty::Int(kind) => {
                            if can_coerce_int_literal(*kind, *val) {
                                Ty::Int(*kind)
                            } else {
                                Ty::Int(IntKind::I64)
                            }
                        }
                        Ty::TypeVar(_) => Ty::Int(IntKind::I64),
                        Ty::Float(kind) => {
                            let fv = *val as f64;
                            match kind {
                                FloatKind::F32 => {
                                    if (fv as f32) as f64 == fv {
                                        Ty::Float(FloatKind::F32)
                                    } else {
                                        Ty::Float(FloatKind::F64)
                                    }
                                }
                                FloatKind::F64 => Ty::Float(FloatKind::F64),
                            }
                        }
                        _ => Ty::Int(IntKind::I64),
                    }
                } else {
                    Ty::Int(IntKind::I64)
                }
            }
            Literal::Float(_) => {
                if let Some(expected) = expected {
                    match expected {
                        Ty::Float(kind) => Ty::Float(*kind),
                        _ => Ty::Float(FloatKind::F64),
                    }
                } else {
                    Ty::Float(FloatKind::F64)
                }
            }
            Literal::String(_) => Ty::Str,
            Literal::Null => {
                if let Some(expected) = expected {
                    expected.clone()
                } else {
                    Ty::Optional(Box::new(Ty::Error))
                }
            }
        }
    }

    fn infer_binop(&mut self, op: BinOp, lhs: &Node<Expr>, rhs: &Node<Expr>, span: Span) -> Ty {
        let lt = self.infer_expr(lhs);
        let rt = self.infer_expr(rhs);

        match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => {
                if lt.is_numeric() && rt.is_numeric() {
                    let mut subst = Substitution::new();
                    if unification::unify(&lt, &rt, &mut subst, span).is_ok() {
                        unification::apply_subst(&subst, &lt)
                    } else {
                        Ty::Error
                    }
                } else {
                    self.emit_error(
                        "E003",
                        format!("type mismatch: expected numeric, found {} and {}", lt, rt),
                        span,
                    );
                    Ty::Error
                }
            }
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
                let mut subst = Substitution::new();
                if unification::unify(&lt, &rt, &mut subst, span).is_err() {
                    self.emit_error(
                        "E003",
                        format!("comparison of incompatible types {} and {}", lt, rt),
                        span,
                    );
                }
                Ty::Bool
            }
            BinOp::And | BinOp::Or => {
                let mut subst = Substitution::new();
                if let Err(err) = unification::unify(&lt, &Ty::Bool, &mut subst, lhs.span) {
                    self.emit_type_error(err);
                }
                if let Err(err) = unification::unify(&rt, &Ty::Bool, &mut subst, rhs.span) {
                    self.emit_type_error(err);
                }
                Ty::Bool
            }
            BinOp::Is | BinOp::As => Ty::Bool,
        }
    }

    fn infer_unop(&mut self, op: UnOp, operand: &Node<Expr>) -> Ty {
        let ty = self.infer_expr(operand);
        match op {
            UnOp::Neg => {
                if ty.is_numeric() {
                    ty
                } else {
                    self.emit_error(
                        "E003",
                        format!("cannot negate non-numeric type {}", ty),
                        operand.span,
                    );
                    Ty::Error
                }
            }
            UnOp::Not => {
                if matches!(ty, Ty::Bool) {
                    Ty::Bool
                } else {
                    self.emit_error(
                        "E003",
                        format!("cannot apply ! to type {}", ty),
                        operand.span,
                    );
                    Ty::Error
                }
            }
            UnOp::Ref => Ty::Ref {
                cap: types::Capability::Ref,
                inner: Box::new(ty),
            },
        }
    }

    fn infer_call(&mut self, callee: &Node<Expr>, args: &[Node<Expr>], span: Span) -> Ty {
        let callee_ty = self.infer_expr(callee);

        match &callee_ty {
            Ty::Fn {
                params,
                ret,
                effects,
            } => {
                if args.len() != params.len() {
                    self.emit_error(
                        "E010",
                        format!(
                            "wrong number of arguments: expected {}, found {}",
                            params.len(),
                            args.len()
                        ),
                        span,
                    );
                    return ret.as_ref().clone();
                }
                for (arg, param_ty) in args.iter().zip(params.iter()) {
                    let arg_ty = self.infer_expr(arg);
                    let mut subst = Substitution::new();
                    if let Err(err) = unification::unify(&arg_ty, param_ty, &mut subst, arg.span) {
                        self.emit_type_error(err);
                    }
                }
                if !effects.is_pure() {
                    if self.current_effects.is_pure() {
                        for eff in effects.iter() {
                            self.emit_error(
                                "E006",
                                format!("pure function cannot perform {:?}", eff),
                                span,
                            );
                        }
                    } else {
                        for eff in effects.iter() {
                            self.current_effects.insert(eff);
                        }
                    }
                }
                ret.as_ref().clone()
            }
            Ty::Error => Ty::Error,
            _ => {
                self.emit_error("E011", format!("not a function: {}", callee_ty), span);
                Ty::Error
            }
        }
    }

    fn infer_field_access(&mut self, object: &Node<Expr>, field: &str, span: Span) -> Ty {
        let obj_ty = self.infer_expr(object);

        match &obj_ty {
            Ty::Named { name, .. } => {
                if let Some(type_def) = self.type_defs.get(name) {
                    if let TypeDefBody::Struct(fields) = &type_def.body {
                        for (fname, fty) in fields {
                            if fname == field {
                                return fty.clone();
                            }
                        }
                    }
                }
                self.emit_error(
                    "E012",
                    format!("field not found: {} on type {}", field, obj_ty),
                    span,
                );
                Ty::Error
            }
            Ty::Tuple(elements) => {
                if let Ok(idx) = field.parse::<usize>() {
                    if idx < elements.len() {
                        return elements[idx].clone();
                    }
                }
                self.emit_error(
                    "E012",
                    format!("field not found: {} on type {}", field, obj_ty),
                    span,
                );
                Ty::Error
            }
            Ty::Error => Ty::Error,
            _ => {
                self.emit_error(
                    "E012",
                    format!("field not found: {} on type {}", field, obj_ty),
                    span,
                );
                Ty::Error
            }
        }
    }

    fn infer_index(&mut self, object: &Node<Expr>, index: &Node<Expr>, span: Span) -> Ty {
        let obj_ty = self.infer_expr(object);
        let idx_ty = self.infer_expr(index);

        match &obj_ty {
            Ty::Array(inner) => {
                let mut subst = Substitution::new();
                if let Err(err) =
                    unification::unify(&idx_ty, &Ty::Int(IntKind::USize), &mut subst, span)
                {
                    self.emit_type_error(err);
                }
                inner.as_ref().clone()
            }
            Ty::Error => Ty::Error,
            _ => {
                self.emit_error("E003", format!("cannot index into type {}", obj_ty), span);
                Ty::Error
            }
        }
    }

    fn infer_lambda(&mut self, params: &[Node<ast::Param>], body: &Node<Expr>) -> Ty {
        let saved_env = self.env.clone();
        let mut param_tys = Vec::new();

        for p in params {
            let ty = p
                .kind
                .type_ann
                .as_ref()
                .map(|t| self.resolve_type(t))
                .unwrap_or_else(|| self.fresh_var());
            self.env.insert_var(p.kind.name.clone(), ty.clone());
            param_tys.push(ty);
        }

        let body_ty = self.infer_expr(body);
        self.env = saved_env;

        Ty::Fn {
            params: param_tys,
            ret: Box::new(body_ty),
            effects: self.current_effects.clone(),
        }
    }

    fn infer_if(
        &mut self,
        condition: &Node<Expr>,
        then_branch: &Node<Expr>,
        else_branch: &Option<Box<Node<Expr>>>,
        span: Span,
    ) -> Ty {
        let cond_ty = self.infer_expr(condition);
        let mut subst = Substitution::new();
        if let Err(err) = unification::unify(&cond_ty, &Ty::Bool, &mut subst, condition.span) {
            self.emit_type_error(err);
        }

        let then_ty = self.infer_expr(then_branch);

        if let Some(else_br) = else_branch {
            let else_ty = self.infer_expr(else_br);
            let mut subst2 = Substitution::new();
            if let Err(err) = unification::unify(&then_ty, &else_ty, &mut subst2, span) {
                self.emit_type_error(err);
            }
            unification::apply_subst(&subst2, &then_ty)
        } else {
            Ty::Void
        }
    }

    fn infer_match(&mut self, scrutinee: &Node<Expr>, arms: &[Node<MatchArm>], span: Span) -> Ty {
        let scrut_ty = self.infer_expr(scrutinee);

        if arms.is_empty() {
            self.emit_error(
                "E008",
                "non-exhaustive match: missing patterns".to_string(),
                span,
            );
            return Ty::Error;
        }

        let mut result_ty: Option<Ty> = None;
        for arm in arms {
            self.check_pattern(&arm.kind.pattern, &scrut_ty);
            if let Some(guard) = &arm.kind.guard {
                let guard_ty = self.infer_expr(guard);
                let mut subst = Substitution::new();
                if let Err(err) = unification::unify(&guard_ty, &Ty::Bool, &mut subst, guard.span) {
                    self.emit_type_error(err);
                }
            }
            let arm_ty = self.infer_expr(&arm.kind.body);
            if let Some(ref prev) = result_ty {
                let mut subst = Substitution::new();
                if let Err(err) = unification::unify(prev, &arm_ty, &mut subst, arm.span) {
                    self.emit_type_error(err);
                }
                result_ty = Some(unification::apply_subst(&subst, prev));
            } else {
                result_ty = Some(arm_ty);
            }
        }

        result_ty.unwrap_or(Ty::Error)
    }

    fn check_pattern(&mut self, pattern: &Node<Pattern>, expected: &Ty) {
        match &pattern.kind {
            Pattern::Wildcard => {}
            Pattern::Var(name) => {
                self.env.insert_var(name.clone(), expected.clone());
            }
            Pattern::Literal(lit) => {
                let lit_ty = self.infer_literal(lit, Some(expected));
                let mut subst = Substitution::new();
                if let Err(err) = unification::unify(&lit_ty, expected, &mut subst, pattern.span) {
                    self.emit_type_error(err);
                }
            }
            Pattern::Constructor { name, fields } => {
                if let Some(type_def) = self.type_defs.get(name) {
                    if let TypeDefBody::Enum(_variants) = &type_def.body {
                        // Check constructor pattern against enum
                    }
                }
                let _ = fields;
            }
            Pattern::Tuple(elements) => {
                if let Ty::Tuple(tys) = expected {
                    if elements.len() != tys.len() {
                        self.emit_error(
                            "E008",
                            "non-exhaustive match: missing patterns".to_string(),
                            pattern.span,
                        );
                    }
                    for (elem, ty) in elements.iter().zip(tys.iter()) {
                        self.check_pattern(elem, ty);
                    }
                }
            }
            Pattern::Or(alternatives) => {
                for alt in alternatives {
                    self.check_pattern(alt, expected);
                }
            }
            Pattern::Range { start, end } => {
                self.check_pattern(start, expected);
                self.check_pattern(end, expected);
            }
            Pattern::Rest(_) => {}
        }
    }

    fn infer_block(&mut self, stmts: &[Node<Stmt>], tail: &Option<Box<Node<Expr>>>) -> Ty {
        let saved_env = self.env.clone();
        for stmt in stmts {
            self.check_stmt(stmt);
        }
        let result = if let Some(expr) = tail {
            self.infer_expr(expr)
        } else {
            Ty::Void
        };
        self.env = saved_env;
        result
    }

    fn infer_pipe(&mut self, lhs: &Node<Expr>, rhs: &Node<Expr>) -> Ty {
        let lhs_ty = self.infer_expr(lhs);
        match &rhs.kind {
            Expr::Lambda { params, body: _ } => {
                if !params.is_empty() {
                    let param_ty = params[0]
                        .kind
                        .type_ann
                        .as_ref()
                        .map(|t| self.resolve_type(t))
                        .unwrap_or_else(|| self.fresh_var());
                    let mut subst = Substitution::new();
                    if let Err(err) = unification::unify(&lhs_ty, &param_ty, &mut subst, lhs.span) {
                        self.emit_type_error(err);
                    }
                }
                self.infer_expr(rhs)
            }
            Expr::Var(name) => {
                if let Some(sig) = self.fn_sigs.get(name).cloned() {
                    if sig.params.len() == 1 {
                        let mut subst = Substitution::new();
                        if let Err(err) =
                            unification::unify(&lhs_ty, &sig.params[0].1, &mut subst, lhs.span)
                        {
                            self.emit_type_error(err);
                        }
                        sig.ret
                    } else {
                        self.emit_error(
                            "E010",
                            format!(
                                "piped function {} expects {} arguments",
                                name,
                                sig.params.len()
                            ),
                            rhs.span,
                        );
                        Ty::Error
                    }
                } else {
                    self.infer_expr(rhs)
                }
            }
            _ => {
                self.env.insert_var("_pipe_arg".to_string(), lhs_ty);
                self.infer_expr(rhs)
            }
        }
    }

    fn infer_error_propagate(&mut self, inner: &Node<Expr>, span: Span) -> Ty {
        let inner_ty = self.infer_expr(inner);
        match &inner_ty {
            Ty::Result { ok, .. } => ok.as_ref().clone(),
            Ty::Optional(inner) => inner.as_ref().clone(),
            Ty::Error => Ty::Error,
            _ => {
                self.emit_error(
                    "E003",
                    format!("? operator requires Result or Optional, found {}", inner_ty),
                    span,
                );
                Ty::Error
            }
        }
    }

    fn infer_null_coalesce(&mut self, lhs: &Node<Expr>, rhs: &Node<Expr>) -> Ty {
        let lhs_ty = self.infer_expr(lhs);
        let rhs_ty = self.infer_expr(rhs);

        let inner = match &lhs_ty {
            Ty::Optional(inner) => inner.as_ref().clone(),
            _ => lhs_ty.clone(),
        };

        let mut subst = Substitution::new();
        if let Err(err) = unification::unify(&inner, &rhs_ty, &mut subst, lhs.span) {
            self.emit_type_error(err);
        }

        unification::apply_subst(&subst, &inner)
    }

    fn infer_struct_init(&mut self, name: &str, fields: &[(String, Node<Expr>)], span: Span) -> Ty {
        let struct_fields = self.type_defs.get(name).and_then(|td| match &td.body {
            TypeDefBody::Struct(fields) => Some(fields.clone()),
            _ => None,
        });

        if let Some(struct_fields) = struct_fields {
            for (fname, fexpr) in fields {
                let expected = struct_fields
                    .iter()
                    .find(|(n, _)| n == fname)
                    .map(|(_, t)| t.clone());
                match expected {
                    Some(exp) => {
                        let found = self.infer_expr(fexpr);
                        let mut subst = Substitution::new();
                        if let Err(err) = unification::unify(&found, &exp, &mut subst, fexpr.span) {
                            self.emit_type_error(err);
                        }
                    }
                    None => {
                        self.emit_error(
                            "E012",
                            format!("field not found: {} on type {}", fname, name),
                            span,
                        );
                    }
                }
            }

            let provided: Vec<&str> = fields.iter().map(|(n, _)| n.as_str()).collect();
            for (fname, _) in &struct_fields {
                if !provided.contains(&fname.as_str()) {
                    self.emit_error(
                        "E012",
                        format!("missing field: {} in struct {}", fname, name),
                        span,
                    );
                }
            }

            return Ty::Named {
                name: name.to_string(),
                args: vec![],
            };
        }

        Ty::Named {
            name: name.to_string(),
            args: vec![],
        }
    }

    fn infer_walrus(
        &mut self,
        name: &str,
        value: &Node<Expr>,
        type_ann: &Option<Node<Type>>,
    ) -> Ty {
        let value_ty = self.infer_expr(value);
        let ty = if let Some(ann) = type_ann {
            let expected = self.resolve_type(ann);
            let mut subst = Substitution::new();
            if let Err(err) = unification::unify(&value_ty, &expected, &mut subst, value.span) {
                self.emit_type_error(err);
            }
            unification::apply_subst(&subst, &expected)
        } else {
            value_ty
        };
        self.env.shadow(name.to_string(), ty.clone());
        ty
    }

    fn resolve_type(&self, ty: &Node<Type>) -> Ty {
        match &ty.kind {
            Type::Named(name) => {
                if let Some(kind) = int_kind_from_name(name) {
                    Ty::Int(kind)
                } else if let Some(kind) = float_kind_from_name(name) {
                    Ty::Float(kind)
                } else if name == "bool" {
                    Ty::Bool
                } else if name == "str" {
                    Ty::Str
                } else if name == "void" {
                    Ty::Void
                } else {
                    Ty::Named {
                        name: name.clone(),
                        args: vec![],
                    }
                }
            }
            Type::Generic { name, args } => {
                if name == "Result" && args.len() == 2 {
                    let ok = self.resolve_type(&args[0]);
                    let err = self.resolve_type(&args[1]);
                    Ty::Result {
                        ok: Box::new(ok),
                        err: Box::new(err),
                    }
                } else if name == "Option" && args.len() == 1 {
                    let inner = self.resolve_type(&args[0]);
                    Ty::Optional(Box::new(inner))
                } else {
                    let resolved_args: Vec<Ty> =
                        args.iter().map(|a| self.resolve_type(a)).collect();
                    Ty::Named {
                        name: name.clone(),
                        args: resolved_args,
                    }
                }
            }
            Type::Tuple(elements) => {
                Ty::Tuple(elements.iter().map(|e| self.resolve_type(e)).collect())
            }
            Type::Array(inner) => Ty::Array(Box::new(self.resolve_type(inner))),
            Type::Optional(inner) => Ty::Optional(Box::new(self.resolve_type(inner))),
            Type::Reference { cap, inner } => {
                let resolved_inner = self.resolve_type(inner);
                let converted_cap = match cap {
                    Capability::Iso => types::Capability::Iso,
                    Capability::Val => types::Capability::Val,
                    Capability::Ref => types::Capability::Ref,
                };
                Ty::Ref {
                    cap: converted_cap,
                    inner: Box::new(resolved_inner),
                }
            }
            Type::Function { params, ret } => Ty::Fn {
                params: params.iter().map(|p| self.resolve_type(p)).collect(),
                ret: Box::new(self.resolve_type(ret)),
                effects: EffectSet::empty(),
            },
            Type::Never => Ty::Never,
            Type::Wildcard => Ty::TypeVar(0),
        }
    }

    fn fresh_var(&mut self) -> Ty {
        let v = self.type_var_counter;
        self.type_var_counter += 1;
        Ty::TypeVar(v)
    }

    pub fn check_sendable(&mut self, ty: &Ty, span: Span) -> bool {
        if ty.is_sendable() {
            true
        } else {
            self.emit_error(
                "E004",
                format!("cannot send {} across actor boundary", ty),
                span,
            );
            false
        }
    }

    pub fn check_capability_transition(
        &mut self,
        from: types::Capability,
        to: types::Capability,
        span: Span,
    ) -> bool {
        let valid = matches!(
            (from, to),
            (types::Capability::Iso, types::Capability::Iso)
                | (types::Capability::Iso, types::Capability::Val)
                | (types::Capability::Iso, types::Capability::Ref)
                | (types::Capability::Val, types::Capability::Val)
                | (types::Capability::Ref, types::Capability::Ref)
        );
        if !valid {
            self.emit_error(
                "E005",
                format!(
                    "capability violation: cannot transition {:?} to {:?}",
                    from, to
                ),
                span,
            );
        }
        valid
    }

    pub fn check_effects(&mut self, caller: &EffectSet, callee: &EffectSet, span: Span) {
        if caller.is_pure() && !callee.is_pure() {
            for eff in callee.iter() {
                self.emit_error(
                    "E006",
                    format!("pure function cannot perform {:?}", eff),
                    span,
                );
            }
        } else if !callee.is_subset_of(caller) {
            for eff in callee.iter() {
                if !caller.contains(eff) {
                    self.emit_error(
                        "E006",
                        format!("effect violation: calling {:?} from {:?}", callee, caller),
                        span,
                    );
                }
            }
        }
    }

    fn emit_error(&mut self, code: &str, message: String, span: Span) {
        self.diagnostics
            .push(Diagnostic::error(code, message, span));
    }

    fn emit_type_error(&mut self, err: TypeError) {
        let span = match &err {
            TypeError::Mismatch { span, .. } => *span,
            TypeError::UndefinedVar { span, .. } => *span,
            TypeError::UseAfterMove { span, .. } => *span,
            TypeError::NotSendable { span, .. } => *span,
            TypeError::CapabilityViolation { span, .. } => *span,
            TypeError::EffectViolation { span, .. } => *span,
            TypeError::OccursCheck { span, .. } => *span,
            TypeError::NonExhaustiveMatch { span } => *span,
            TypeError::DuplicateDef { span, .. } => *span,
            TypeError::UndefinedType { span, .. } => *span,
            TypeError::ArgCount { span, .. } => *span,
            TypeError::NotAFunction { span, .. } => *span,
            TypeError::FieldNotFound { span, .. } => *span,
            TypeError::NullNotAllowed { span, .. } => *span,
            TypeError::PureViolation { span, .. } => *span,
        };
        self.diagnostics
            .push(Diagnostic::error("T001", err.to_string(), span));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::typeck::types::FloatKind;

    fn dummy_span() -> Span {
        Span::dummy()
    }

    fn make_lit_int(val: i64) -> Node<Expr> {
        Node::new(Expr::Literal(Literal::Int(val)), dummy_span())
    }

    fn make_lit_bool(val: bool) -> Node<Expr> {
        Node::new(Expr::Literal(Literal::Bool(val)), dummy_span())
    }

    fn make_lit_float(val: &str) -> Node<Expr> {
        Node::new(Expr::Literal(Literal::Float(val.to_string())), dummy_span())
    }

    fn make_var(name: &str) -> Node<Expr> {
        Node::new(Expr::Var(name.to_string()), dummy_span())
    }

    fn make_binop(op: BinOp, lhs: Node<Expr>, rhs: Node<Expr>) -> Node<Expr> {
        Node::new(
            Expr::BinaryOp {
                op,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            },
            dummy_span(),
        )
    }

    fn make_walrus(name: &str, value: Node<Expr>) -> Node<Expr> {
        Node::new(
            Expr::Walrus {
                name: name.to_string(),
                value: Box::new(value),
                type_ann: None,
            },
            dummy_span(),
        )
    }

    fn make_block(stmts: Vec<Node<Stmt>>, expr: Option<Node<Expr>>) -> Node<Expr> {
        Node::new(
            Expr::Block {
                stmts,
                expr: expr.map(Box::new),
            },
            dummy_span(),
        )
    }

    fn make_named_type(name: &str) -> Node<Type> {
        Node::new(Type::Named(name.to_string()), dummy_span())
    }

    fn make_fn_item(
        name: &str,
        params: Vec<Node<ast::Param>>,
        ret: Option<Node<Type>>,
        body: Node<Expr>,
    ) -> Node<Item> {
        Node::new(
            Item::FnDecl(FnDecl {
                visibility: Visibility::Private,
                name: name.to_string(),
                generic_params: vec![],
                params,
                return_type: ret,
                body,
                effects: None,
            }),
            dummy_span(),
        )
    }

    fn make_param(name: &str, type_name: &str) -> Node<ast::Param> {
        Node::new(
            ast::Param {
                name: name.to_string(),
                type_ann: Some(make_named_type(type_name)),
            },
            dummy_span(),
        )
    }

    #[test]
    fn test_infer_int_literal() {
        let mut checker = TypeChecker::new();
        let expr = make_lit_int(42);
        let ty = checker.infer_expr(&expr);
        assert_eq!(ty, Ty::Int(IntKind::I64));
    }

    #[test]
    fn test_infer_bool_literal() {
        let mut checker = TypeChecker::new();
        let expr = make_lit_bool(true);
        let ty = checker.infer_expr(&expr);
        assert_eq!(ty, Ty::Bool);
    }

    #[test]
    fn test_infer_float_literal() {
        let mut checker = TypeChecker::new();
        let expr = make_lit_float("3.14");
        let ty = checker.infer_expr(&expr);
        assert_eq!(ty, Ty::Float(FloatKind::F64));
    }

    #[test]
    fn test_infer_binary_add() {
        let mut checker = TypeChecker::new();
        let lhs = make_lit_int(1);
        let rhs = make_lit_int(2);
        let expr = make_binop(BinOp::Add, lhs, rhs);
        let ty = checker.infer_expr(&expr);
        assert_eq!(ty, Ty::Int(IntKind::I64));
    }

    #[test]
    fn test_infer_binary_compare() {
        let mut checker = TypeChecker::new();
        let lhs = make_lit_int(1);
        let rhs = make_lit_int(2);
        let expr = make_binop(BinOp::Lt, lhs, rhs);
        let ty = checker.infer_expr(&expr);
        assert_eq!(ty, Ty::Bool);
    }

    #[test]
    fn test_infer_undefined_var() {
        let mut checker = TypeChecker::new();
        let expr = make_var("undefined_var");
        let ty = checker.infer_expr(&expr);
        assert_eq!(ty, Ty::Error);
        assert!(!checker.diagnostics.is_empty());
    }

    #[test]
    fn test_infer_walrus() {
        let mut checker = TypeChecker::new();
        let value = make_lit_int(42);
        let expr = make_walrus("x", value);
        let ty = checker.infer_expr(&expr);
        assert_eq!(ty, Ty::Int(IntKind::I64));
        assert_eq!(checker.env.lookup("x"), Some(&Ty::Int(IntKind::I64)));
    }

    #[test]
    fn test_check_program_simple_fn() {
        let body = make_block(vec![], Some(make_lit_bool(true)));
        let item = make_fn_item("foo", vec![], Some(make_named_type("bool")), body);
        let result = TypeChecker::check_program(&[item]);
        assert!(result.is_ok());
    }

    #[test]
    fn test_check_program_type_mismatch_fn() {
        let body = make_block(vec![], Some(make_lit_bool(true)));
        let item = make_fn_item("foo", vec![], Some(make_named_type("i32")), body);
        let result = TypeChecker::check_program(&[item]);
        assert!(result.is_err());
    }

    #[test]
    fn test_literal_coercion() {
        let checker = TypeChecker::new();
        let ty = checker.infer_literal(&Literal::Int(10), Some(&Ty::Int(IntKind::U8)));
        assert_eq!(ty, Ty::Int(IntKind::U8));
    }

    #[test]
    fn test_literal_coercion_out_of_range() {
        let checker = TypeChecker::new();
        let ty = checker.infer_literal(&Literal::Int(300), Some(&Ty::Int(IntKind::U8)));
        assert_eq!(ty, Ty::Int(IntKind::I64));
    }

    #[test]
    fn test_capability_transition_iso_to_val() {
        let mut checker = TypeChecker::new();
        assert!(checker.check_capability_transition(
            types::Capability::Iso,
            types::Capability::Val,
            dummy_span()
        ));
    }

    #[test]
    fn test_capability_transition_val_to_iso() {
        let mut checker = TypeChecker::new();
        assert!(!checker.check_capability_transition(
            types::Capability::Val,
            types::Capability::Iso,
            dummy_span()
        ));
    }

    #[test]
    fn test_sendable_int() {
        let mut checker = TypeChecker::new();
        assert!(checker.check_sendable(&Ty::Int(IntKind::I32), dummy_span()));
    }

    #[test]
    fn test_not_sendable_ref() {
        let mut checker = TypeChecker::new();
        assert!(!checker.check_sendable(
            &Ty::Ref {
                cap: types::Capability::Ref,
                inner: Box::new(Ty::Int(IntKind::I32)),
            },
            dummy_span()
        ));
    }

    #[test]
    fn test_effect_violation_pure_calling_io() {
        let mut checker = TypeChecker::new();
        let caller = EffectSet::empty();
        let callee = EffectSet::new(vec![types::Effect::IO]);
        checker.check_effects(&caller, &callee, dummy_span());
        assert!(!checker.diagnostics.is_empty());
    }

    #[test]
    fn test_effect_compatible_io_calling_io() {
        let mut checker = TypeChecker::new();
        let caller = EffectSet::new(vec![types::Effect::IO, types::Effect::Net]);
        let callee = EffectSet::new(vec![types::Effect::IO]);
        checker.check_effects(&caller, &callee, dummy_span());
        assert!(checker.diagnostics.is_empty());
    }

    #[test]
    fn test_error_propagate_result() {
        let mut checker = TypeChecker::new();
        checker.env.insert_var(
            "x".to_string(),
            Ty::Result {
                ok: Box::new(Ty::Int(IntKind::I32)),
                err: Box::new(Ty::Named {
                    name: "Error".to_string(),
                    args: vec![],
                }),
            },
        );

        let expr = Node::new(
            Expr::ErrorPropagate {
                expr: Box::new(make_var("x")),
            },
            dummy_span(),
        );
        let ty = checker.infer_expr(&expr);
        assert_eq!(ty, Ty::Int(IntKind::I32));
    }

    #[test]
    fn test_resolve_types() {
        let checker = TypeChecker::new();
        assert_eq!(
            checker.resolve_type(&make_named_type("i32")),
            Ty::Int(IntKind::I32)
        );
        assert_eq!(
            checker.resolve_type(&make_named_type("u8")),
            Ty::Int(IntKind::U8)
        );
        assert_eq!(
            checker.resolve_type(&make_named_type("f64")),
            Ty::Float(FloatKind::F64)
        );
        assert_eq!(checker.resolve_type(&make_named_type("bool")), Ty::Bool);
        assert_eq!(checker.resolve_type(&make_named_type("str")), Ty::Str);
        assert_eq!(checker.resolve_type(&make_named_type("void")), Ty::Void);
    }

    #[test]
    fn test_int_literal_default_is_i64() {
        let checker = TypeChecker::new();
        let ty = checker.infer_literal(&Literal::Int(42), None);
        assert_eq!(ty, Ty::Int(IntKind::I64));
    }

    #[test]
    fn test_check_program_fn_with_params() {
        let body = make_block(
            vec![],
            Some(make_binop(BinOp::Add, make_var("a"), make_var("b"))),
        );
        let item = make_fn_item(
            "add",
            vec![make_param("a", "i32"), make_param("b", "i32")],
            Some(make_named_type("i32")),
            body,
        );
        let result = TypeChecker::check_program(&[item]);
        assert!(result.is_ok());
    }

    #[test]
    fn test_sendable_iso_ref() {
        let mut checker = TypeChecker::new();
        assert!(checker.check_sendable(
            &Ty::Ref {
                cap: types::Capability::Iso,
                inner: Box::new(Ty::Int(IntKind::I32)),
            },
            dummy_span()
        ));
    }

    #[test]
    fn test_capability_ref_to_val() {
        let mut checker = TypeChecker::new();
        assert!(!checker.check_capability_transition(
            types::Capability::Ref,
            types::Capability::Val,
            dummy_span()
        ));
    }

    #[test]
    fn test_capability_iso_to_ref() {
        let mut checker = TypeChecker::new();
        assert!(checker.check_capability_transition(
            types::Capability::Iso,
            types::Capability::Ref,
            dummy_span()
        ));
    }
}
