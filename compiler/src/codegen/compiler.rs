use std::collections::HashMap;

use crate::ast::{
    self, ActorDecl, BinOp, Expr, FnDecl, Item, Literal, Stmt, TypeBody, UnOp,
};
use crate::lexer::token::Span;
use crate::typeck::types::{Capability, Effect, EffectSet, Ty};

use super::errors::CodeGenError;
use super::layout::{self, TypeRegistry};
use super::morph_ir::{
    CompiledFunction, Instruction, MorphIRModule, ParamInfo, TypeInfo, TypeInfoKind,
};

type CompileResult<T = ()> = Result<T, CodeGenError>;

struct LocalScope {
    vars: HashMap<String, u32>,
    next_slot: u32,
}

impl LocalScope {
    fn new() -> Self {
        Self {
            vars: HashMap::new(),
            next_slot: 0,
        }
    }

    fn alloc(&mut self, name: String) -> u32 {
        let slot = self.next_slot;
        self.next_slot += 1;
        self.vars.insert(name, slot);
        slot
    }

    fn lookup(&self, name: &str) -> Option<u32> {
        self.vars.get(name).copied()
    }
}

pub struct CodeGen {
    module: MorphIRModule,
    type_map: HashMap<crate::ast::NodeId, Ty>,
    effect_map: HashMap<crate::ast::NodeId, EffectSet>,
    current_function: Option<CompiledFunction>,
    scope_stack: Vec<LocalScope>,
    string_table: HashMap<String, u32>,
    loop_depth: u32,
    registry: TypeRegistry,
    fn_sigs: HashMap<String, FnSig>,
}

#[derive(Debug, Clone)]
struct FnSig {
    param_count: usize,
    return_ty: Ty,
    effects: EffectSet,
}

impl CodeGen {
    pub fn new(type_map: HashMap<crate::ast::NodeId, Ty>) -> Self {
        Self {
            module: MorphIRModule::new("main".to_string()),
            type_map,
            effect_map: HashMap::new(),
            current_function: None,
            scope_stack: Vec::new(),
            string_table: HashMap::new(),
            loop_depth: 0,
            registry: TypeRegistry::new(),
            fn_sigs: HashMap::new(),
        }
    }

    pub fn with_effects(
        type_map: HashMap<crate::ast::NodeId, Ty>,
        effect_map: HashMap<crate::ast::NodeId, EffectSet>,
    ) -> Self {
        let mut cg = Self::new(type_map);
        cg.effect_map = effect_map;
        cg
    }

    pub fn compile(
        items: &[crate::ast::Node<Item>],
        type_map: HashMap<crate::ast::NodeId, Ty>,
    ) -> Result<MorphIRModule, Vec<CodeGenError>> {
        let mut cg = Self::new(type_map);
        let mut errors = Vec::new();

        cg.collect_types(items);
        cg.collect_fn_sigs(items);

        for item in items {
            if let Err(e) = cg.compile_item(item) {
                errors.push(e);
            }
        }

        if errors.is_empty() {
            Ok(cg.module)
        } else {
            Err(errors)
        }
    }

    pub fn compile_with_effects(
        items: &[crate::ast::Node<Item>],
        type_map: HashMap<crate::ast::NodeId, Ty>,
        effect_map: HashMap<crate::ast::NodeId, EffectSet>,
    ) -> Result<MorphIRModule, Vec<CodeGenError>> {
        let mut cg = Self::with_effects(type_map, effect_map);
        let mut errors = Vec::new();

        cg.collect_types(items);
        cg.collect_fn_sigs(items);

        for item in items {
            if let Err(e) = cg.compile_item(item) {
                errors.push(e);
            }
        }

        if errors.is_empty() {
            Ok(cg.module)
        } else {
            Err(errors)
        }
    }

    fn collect_types(&mut self, items: &[crate::ast::Node<Item>]) {
        for item in items {
            if let Item::TypeDecl(decl) = &item.kind {
                match &decl.body {
                    TypeBody::Struct(fields) => {
                        let field_tys: Vec<(String, Ty)> = fields
                            .iter()
                            .map(|f| {
                                let ty = self.resolve_ast_type_or_error(&f.kind.type_ann);
                                (f.kind.name.clone(), ty)
                            })
                            .collect();
                        self.registry.register_struct(decl.name.clone(), field_tys);
                    }
                    TypeBody::Enum(variants) => {
                        let variant_tys: Vec<(String, Vec<Ty>)> = variants
                            .iter()
                            .map(|v| {
                                let field_tys: Vec<Ty> = v
                                    .kind
                                    .fields
                                    .iter()
                                    .map(|t| self.resolve_ast_type_or_error(t))
                                    .collect();
                                (v.kind.name.clone(), field_tys)
                            })
                            .collect();
                        self.registry.register_enum(decl.name.clone(), variant_tys);
                    }
                    TypeBody::Alias(_) => {}
                }
            }
        }
    }

    fn collect_fn_sigs(&mut self, items: &[crate::ast::Node<Item>]) {
        for item in items {
            if let Item::FnDecl(decl) = &item.kind {
                let param_count = decl.params.len();
                let return_ty = decl
                    .return_type
                    .as_ref()
                    .map(|t| self.resolve_ast_type_or_error(t))
                    .unwrap_or(Ty::Void);
                let effects = decl
                    .effects
                    .as_ref()
                    .map(|e| self.convert_ast_effects(e))
                    .unwrap_or_else(EffectSet::empty);
                self.fn_sigs.insert(
                    decl.name.clone(),
                    FnSig {
                        param_count,
                        return_ty,
                        effects,
                    },
                );
            }
        }
    }

    fn resolve_ast_type_or_error(&self, ty: &crate::ast::Node<ast::Type>) -> Ty {
        resolve_ast_type(ty)
    }

    fn convert_ast_effects(&self, ast_set: &ast::EffectSet) -> EffectSet {
        let effects: Vec<Effect> = ast_set
            .effects
            .iter()
            .filter_map(|e| match e {
                ast::Effect::Pure => None,
                ast::Effect::IO => Some(Effect::IO),
                ast::Effect::Net => Some(Effect::Net),
                ast::Effect::Time => Some(Effect::Time),
                ast::Effect::System => Some(Effect::System),
            })
            .collect();
        EffectSet::new(effects)
    }

    fn compile_item(&mut self, item: &crate::ast::Node<Item>) -> CompileResult {
        match &item.kind {
            Item::FnDecl(decl) => self.compile_fn_decl(decl, item.span),
            Item::TypeDecl(decl) => {
                self.compile_type_decl(decl, item.span);
                Ok(())
            }
            Item::ActorDecl(decl) => self.compile_actor_decl(decl, item.span),
            Item::ConstDecl(decl) => {
                let mut func = CompiledFunction::new(format!("const_{}", decl.name));
                self.current_function = Some(func);
                self.push_scope();
                self.compile_expr(&decl.value)?;
                self.emit(Instruction::Ret, decl.value.span);
                self.pop_scope();
                self.finish_function();
                Ok(())
            }
            Item::UseDecl(_) => Ok(()),
            Item::ImplBlock(block) => {
                for method in &block.methods {
                    self.compile_fn_decl(&method.kind, method.span)?;
                }
                Ok(())
            }
            Item::TraitDecl(_) => Ok(()),
        }
    }

    fn compile_fn_decl(&mut self, decl: &FnDecl, span: Span) -> CompileResult {
        let mut func = CompiledFunction::new(decl.name.clone());

        self.push_scope();

        let return_ty = decl
            .return_type
            .as_ref()
            .map(|t| resolve_ast_type(t))
            .unwrap_or(Ty::Void);
        func.return_type = Some(return_ty);

        for param in &decl.params {
            let slot = self.scope_stack.last_mut().map(|s| s.alloc(param.kind.name.clone()));
            if let Some(slot) = slot {
                let ty = param
                    .kind
                    .type_ann
                    .as_ref()
                    .map(|t| resolve_ast_type(t))
                    .unwrap_or(Ty::Error);
                func.params.push(ParamInfo {
                    name: param.kind.name.clone(),
                    ty,
                    slot,
                });
            }
        }

        self.current_function = Some(func);

        let effects = decl
            .effects
            .as_ref()
            .map(|e| self.convert_ast_effects(e))
            .unwrap_or_else(EffectSet::empty);
        let has_io = effects.contains(Effect::IO) || effects.contains(Effect::Net);
        if has_io {
            self.emit_yield_checkpoint(decl.body.span);
        } else {
            self.emit_yield_checkpoint(decl.body.span);
        }

        self.compile_expr(&decl.body)?;

        self.emit(Instruction::Ret, span);

        self.pop_scope();
        self.finish_function();

        Ok(())
    }

    fn compile_type_decl(&mut self, decl: &ast::TypeDecl, _span: Span) {
        match &decl.body {
            TypeBody::Struct(fields) => {
                let field_tys: Vec<(String, Ty)> = fields
                    .iter()
                    .map(|f| (f.kind.name.clone(), resolve_ast_type(&f.kind.type_ann)))
                    .collect();
                let (size, align, field_infos) =
                    layout::compute_struct_layout(&field_tys, &self.registry);
                self.module.type_info.push(TypeInfo {
                    name: decl.name.clone(),
                    size,
                    alignment: align,
                    kind: TypeInfoKind::Struct { fields: field_infos },
                });
            }
            TypeBody::Enum(variants) => {
                let variant_tys: Vec<(String, Vec<Ty>)> = variants
                    .iter()
                    .map(|v| {
                        let field_tys: Vec<Ty> = v
                            .kind
                            .fields
                            .iter()
                            .map(|t| resolve_ast_type(t))
                            .collect();
                        (v.kind.name.clone(), field_tys)
                    })
                    .collect();
                let (size, align, variant_infos) =
                    layout::compute_enum_layout_from_types(&variant_tys, &self.registry);
                self.module.type_info.push(TypeInfo {
                    name: decl.name.clone(),
                    size,
                    alignment: align,
                    kind: TypeInfoKind::Enum {
                        variants: variant_infos,
                    },
                });
            }
            TypeBody::Alias(_) => {}
        }
    }

    fn compile_actor_decl(&mut self, decl: &ActorDecl, span: Span) -> CompileResult {
        for member in &decl.members {
            if let ast::ActorMember::FnMember(f) = &member.kind {
                self.compile_fn_decl(f, member.span)?;
            }
        }
        let _ = span;
        Ok(())
    }

    fn compile_expr(&mut self, expr: &crate::ast::Node<Expr>) -> CompileResult {
        match &expr.kind {
            Expr::Literal(lit) => self.compile_literal(lit, expr.span),
            Expr::Var(name) => self.compile_var(name, expr.span),
            Expr::BinaryOp { op, lhs, rhs } => self.compile_binop(*op, lhs, rhs, expr.span),
            Expr::UnaryOp { op, operand } => self.compile_unop(*op, operand, expr.span),
            Expr::Call { callee, args } => self.compile_call(callee, args, expr.span),
            Expr::FieldAccess { object, field } => {
                self.compile_field_access(object, field, expr.span)
            }
            Expr::Index { object, index } => self.compile_index(object, index, expr.span),
            Expr::Lambda { params, body } => self.compile_lambda(params, body, expr.span),
            Expr::If {
                condition,
                then_branch,
                else_branch,
            } => self.compile_if(condition, then_branch, else_branch, expr.span),
            Expr::Match { scrutinee, arms } => self.compile_match(scrutinee, arms, expr.span),
            Expr::Block { stmts, expr: tail } => self.compile_block(stmts, tail, expr.span),
            Expr::Pipe { lhs, rhs } => self.compile_pipe(lhs, rhs, expr.span),
            Expr::ErrorPropagate { expr: inner } => self.compile_error_propagate(inner, expr.span),
            Expr::NullCoalesce { lhs, rhs } => self.compile_null_coalesce(lhs, rhs, expr.span),
            Expr::Async { expr: inner } => {
                self.emit(Instruction::SpawnFiber, expr.span);
                self.compile_expr(inner)
            }
            Expr::Spawn { expr: inner } => {
                self.compile_expr(inner)?;
                self.emit(Instruction::SpawnFiber, expr.span);
                Ok(())
            }
            Expr::StructInit { name, fields } => {
                self.compile_struct_init(name, fields, expr.span)
            }
            Expr::Walrus {
                name,
                value,
                type_ann: _,
            } => self.compile_walrus(name, value, expr.span),
        }
    }

    fn compile_literal(&mut self, lit: &Literal, span: Span) -> CompileResult {
        match lit {
            Literal::Int(v) => {
                self.emit(Instruction::PushInt(*v), span);
            }
            Literal::Float(v) => {
                let val: f64 = v.parse().unwrap_or(0.0);
                self.emit(Instruction::PushFloat(val), span);
            }
            Literal::Bool(v) => {
                self.emit(Instruction::PushBool(*v), span);
            }
            Literal::String(v) => {
                let idx = self.intern_string(v);
                self.emit(Instruction::PushStr(idx), span);
            }
            Literal::Null => {
                self.emit(Instruction::PushNull, span);
            }
        }
        Ok(())
    }

    fn compile_var(&mut self, name: &str, span: Span) -> CompileResult {
        for scope in self.scope_stack.iter().rev() {
            if let Some(slot) = scope.lookup(name) {
                self.emit(Instruction::LoadLocal(slot), span);
                return Ok(());
            }
        }
        Err(CodeGenError::UndefinedVariable {
            name: name.to_string(),
            span,
        })
    }

    fn compile_binop(
        &mut self,
        op: BinOp,
        lhs: &crate::ast::Node<Expr>,
        rhs: &crate::ast::Node<Expr>,
        span: Span,
    ) -> CompileResult {
        if op == BinOp::And || op == BinOp::Or {
            self.compile_expr(lhs)?;
            let lhs_end = self.current_instruction_count();
            // placeholder for JumpIf/JumpIfNot
            self.emit(Instruction::JumpIfNot(0), span);
            self.compile_expr(rhs)?;
            let rhs_end = self.current_instruction_count();
            self.patch_jump(lhs_end, (rhs_end - lhs_end) as i32);
            return Ok(());
        }

        self.compile_expr(lhs)?;
        self.compile_expr(rhs)?;

        let instr = match op {
            BinOp::Add => Instruction::Add,
            BinOp::Sub => Instruction::Sub,
            BinOp::Mul => Instruction::Mul,
            BinOp::Div => Instruction::Div,
            BinOp::Mod => Instruction::Mod,
            BinOp::Eq => Instruction::Eq,
            BinOp::Ne => Instruction::Ne,
            BinOp::Lt => Instruction::Lt,
            BinOp::Gt => Instruction::Gt,
            BinOp::Le => Instruction::Le,
            BinOp::Ge => Instruction::Ge,
            BinOp::And | BinOp::Or => unreachable!(),
            BinOp::Is => Instruction::Eq,
            BinOp::As => {
                let ty = self.type_map.get(&lhs.id);
                if let Some(Ty::Ref { cap, .. }) = ty {
                    match cap {
                        Capability::Iso => {
                            self.emit(Instruction::FreezeCap, span);
                            return Ok(());
                        }
                        Capability::Ref => {
                            self.emit(Instruction::BorrowCap, span);
                            return Ok(());
                        }
                        Capability::Val => {
                            return Ok(());
                        }
                    }
                }
                return Ok(());
            }
        };
        self.emit(instr, span);
        Ok(())
    }

    fn compile_unop(
        &mut self,
        op: UnOp,
        operand: &crate::ast::Node<Expr>,
        span: Span,
    ) -> CompileResult {
        self.compile_expr(operand)?;
        match op {
            UnOp::Neg => {
                self.emit(Instruction::Neg, span);
            }
            UnOp::Not => {
                self.emit(Instruction::Not, span);
            }
            UnOp::Ref => {
                let ty = self.type_map.get(&operand.id);
                if let Some(Ty::Ref { cap, .. }) = ty {
                    match cap {
                        Capability::Val => {
                            self.emit(Instruction::ArcRetain, span);
                        }
                        Capability::Ref => {
                            self.emit(Instruction::BorrowCap, span);
                        }
                        Capability::Iso => {}
                    }
                }
            }
        }
        Ok(())
    }

    fn compile_call(
        &mut self,
        callee: &crate::ast::Node<Expr>,
        args: &[crate::ast::Node<Expr>],
        span: Span,
    ) -> CompileResult {
        for arg in args {
            self.compile_expr(arg)?;
        }
        self.compile_expr(callee)?;

        let arg_count = args.len() as u32;
        self.emit(Instruction::Call(arg_count), span);

        if let Some(ty) = self.type_map.get(&callee.id) {
            if let Ty::Ref {
                cap: Capability::Val,
                ..
            } = ty
            {
                self.emit(Instruction::ArcRelease, span);
            }
        }

        Ok(())
    }

    fn compile_field_access(
        &mut self,
        object: &crate::ast::Node<Expr>,
        field: &str,
        span: Span,
    ) -> CompileResult {
        self.compile_expr(object)?;

        let obj_ty = self.type_map.get(&object.id);
        if let Some(Ty::Named { name, .. }) = obj_ty {
            if let Some(fields) = self.registry.lookup_struct(name) {
                for (idx, (fname, _)) in fields.iter().enumerate() {
                    if fname == field {
                        self.emit(Instruction::GetField(idx as u32), span);
                        return Ok(());
                    }
                }
            }
        }

        if let Ok(idx) = field.parse::<u32>() {
            self.emit(Instruction::GetField(idx), span);
            return Ok(());
        }

        self.emit(Instruction::GetField(0), span);
        Ok(())
    }

    fn compile_index(
        &mut self,
        object: &crate::ast::Node<Expr>,
        index: &crate::ast::Node<Expr>,
        span: Span,
    ) -> CompileResult {
        self.compile_expr(object)?;
        self.compile_expr(index)?;
        let _ = span;
        Ok(())
    }

    fn compile_lambda(
        &mut self,
        params: &[crate::ast::Node<ast::Param>],
        body: &crate::ast::Node<Expr>,
        span: Span,
    ) -> CompileResult {
        self.push_scope();
        for param in params {
            if let Some(scope) = self.scope_stack.last_mut() {
                scope.alloc(param.kind.name.clone());
            }
        }
        self.compile_expr(body)?;
        self.emit(Instruction::Ret, span);
        self.pop_scope();
        Ok(())
    }

    fn compile_if(
        &mut self,
        condition: &crate::ast::Node<Expr>,
        then_branch: &crate::ast::Node<Expr>,
        else_branch: &Option<Box<crate::ast::Node<Expr>>>,
        span: Span,
    ) -> CompileResult {
        self.compile_expr(condition)?;

        let jump_not_idx = self.current_instruction_count();
        self.emit(Instruction::JumpIfNot(0), span);

        self.compile_expr(then_branch)?;

        if let Some(else_br) = else_branch {
            let jump_end_idx = self.current_instruction_count();
            self.emit(Instruction::Jump(0), span);

            let else_start = self.current_instruction_count();
            self.patch_jump(jump_not_idx, (else_start - jump_not_idx) as i32);

            self.compile_expr(else_br)?;

            let end_idx = self.current_instruction_count();
            self.patch_jump(jump_end_idx, (end_idx - jump_end_idx) as i32);
        } else {
            let end_idx = self.current_instruction_count();
            self.patch_jump(jump_not_idx, (end_idx - jump_not_idx) as i32);
        }

        Ok(())
    }

    fn compile_match(
        &mut self,
        scrutinee: &crate::ast::Node<Expr>,
        arms: &[crate::ast::Node<ast::MatchArm>],
        span: Span,
    ) -> CompileResult {
        self.compile_expr(scrutinee)?;

        let arm_count = arms.len() as u32;
        self.emit(Instruction::Match(arm_count), span);

        let mut arm_end_jumps = Vec::with_capacity(arms.len());

        for arm in arms {
            self.push_scope();
            self.compile_pattern_bindings(&arm.kind.pattern, scrutinee.id)?;

            if let Some(guard) = &arm.kind.guard {
                self.compile_expr(guard)?;
                let guard_jump_idx = self.current_instruction_count();
                self.emit(Instruction::JumpIfNot(0), arm.span);
                self.compile_expr(&arm.kind.body)?;
                let body_end = self.current_instruction_count();
                self.patch_jump(guard_jump_idx, (body_end - guard_jump_idx) as i32);
            } else {
                self.compile_expr(&arm.kind.body)?;
            }

            let jump_end_idx = self.current_instruction_count();
            self.emit(Instruction::Jump(0), arm.span);
            arm_end_jumps.push(jump_end_idx);

            self.emit(Instruction::DropMatch, arm.span);
            self.pop_scope();
        }

        let match_end = self.current_instruction_count();
        for jump_idx in arm_end_jumps {
            self.patch_jump(jump_idx, (match_end - jump_idx) as i32);
        }

        Ok(())
    }

    fn compile_pattern_bindings(
        &mut self,
        pattern: &crate::ast::Node<ast::Pattern>,
        _scrutinee_id: crate::ast::NodeId,
    ) -> CompileResult {
        match &pattern.kind {
            ast::Pattern::Var(name) => {
                if let Some(scope) = self.scope_stack.last_mut() {
                    let slot = scope.alloc(name.clone());
                    self.emit(Instruction::StoreLocal(slot), pattern.span);
                }
            }
            ast::Pattern::Wildcard | ast::Pattern::Literal(_) => {}
            ast::Pattern::Constructor { name, fields } => {
                let _ = name;
                for (fname, fpat) in fields {
                    let _ = fname;
                    self.compile_pattern_bindings(fpat, _scrutinee_id)?;
                }
            }
            ast::Pattern::Tuple(elements) => {
                for elem in elements {
                    self.compile_pattern_bindings(elem, _scrutinee_id)?;
                }
            }
            ast::Pattern::Or(alternatives) => {
                if let Some(first) = alternatives.first() {
                    self.compile_pattern_bindings(first, _scrutinee_id)?;
                }
            }
            ast::Pattern::Range { .. } => {}
            ast::Pattern::Rest(_) => {}
        }
        Ok(())
    }

    fn compile_block(
        &mut self,
        stmts: &[crate::ast::Node<Stmt>],
        tail: &Option<Box<crate::ast::Node<Expr>>>,
        span: Span,
    ) -> CompileResult {
        self.push_scope();
        for stmt in stmts {
            self.compile_stmt(stmt)?;
        }
        if let Some(expr) = tail {
            self.compile_expr(expr)?;
        } else {
            self.emit(Instruction::PushUnit, span);
        }
        self.pop_scope();
        Ok(())
    }

    fn compile_stmt(&mut self, stmt: &crate::ast::Node<Stmt>) -> CompileResult {
        match &stmt.kind {
            Stmt::ExprStmt(expr) => {
                self.compile_expr(expr)?;
                let ty = self.type_map.get(&expr.id);
                if !matches!(ty, Some(Ty::Void)) {
                    // result of expression statement is discarded
                }
            }
            Stmt::VarDecl {
                name,
                type_ann: _,
                value,
            } => {
                self.compile_expr(value)?;
                if let Some(scope) = self.scope_stack.last_mut() {
                    let slot = scope.alloc(name.clone());
                    self.emit(Instruction::StoreLocal(slot), stmt.span);
                }
            }
            Stmt::Assign { target, value } => {
                self.compile_expr(value)?;
                if let Expr::Var(name) = &target.kind {
                    for scope in self.scope_stack.iter().rev() {
                        if let Some(slot) = scope.lookup(name) {
                            self.emit(Instruction::StoreLocal(slot), target.span);
                            return Ok(());
                        }
                    }
                    return Err(CodeGenError::UndefinedVariable {
                        name: name.clone(),
                        span: target.span,
                    });
                }
                if let Expr::FieldAccess { object, field } = &target.kind {
                    self.compile_expr(object)?;
                    let obj_ty = self.type_map.get(&object.id);
                    if let Some(Ty::Named { name: type_name, .. }) = obj_ty {
                        if let Some(fields) = self.registry.lookup_struct(type_name) {
                            for (idx, (fname, _)) in fields.iter().enumerate() {
                                if fname == field {
                                    self.emit(Instruction::SetField(idx as u32), target.span);
                                    return Ok(());
                                }
                            }
                        }
                    }
                    self.emit(Instruction::SetField(0), target.span);
                    return Ok(());
                }
            }
            Stmt::Return(expr) => {
                if let Some(ret_expr) = expr {
                    self.compile_expr(ret_expr)?;
                } else {
                    self.emit(Instruction::PushUnit, stmt.span);
                }
                self.emit(Instruction::Ret, stmt.span);
            }
            Stmt::Defer(expr) => {
                self.compile_expr(expr)?;
            }
            Stmt::Break | Stmt::Continue => {}
            Stmt::While { condition, body } => {
                self.loop_depth += 1;

                let loop_start = self.current_instruction_count();
                self.emit_yield_checkpoint(condition.span);

                self.compile_expr(condition)?;
                let exit_jump_idx = self.current_instruction_count();
                self.emit(Instruction::JumpIfNot(0), condition.span);

                self.push_scope();
                for s in body {
                    self.compile_stmt(s)?;
                }
                self.pop_scope();

                let current = self.current_instruction_count();
                self.emit(
                    Instruction::Jump(-(current as i32 - loop_start as i32)),
                    condition.span,
                );

                let loop_end = self.current_instruction_count();
                self.patch_jump(exit_jump_idx, (loop_end - exit_jump_idx) as i32);

                self.emit(Instruction::PushUnit, condition.span);

                self.loop_depth -= 1;
            }
            Stmt::Nop => {}
        }
        Ok(())
    }

    fn compile_pipe(
        &mut self,
        lhs: &crate::ast::Node<Expr>,
        rhs: &crate::ast::Node<Expr>,
        span: Span,
    ) -> CompileResult {
        self.compile_expr(lhs)?;
        match &rhs.kind {
            Expr::Call { callee, args } => {
                for arg in args {
                    self.compile_expr(arg)?;
                }
                self.compile_expr(callee)?;
                let total_args = args.len() as u32 + 1;
                self.emit(Instruction::Call(total_args), span);
            }
            Expr::Var(name) => {
                if let Some(sig) = self.fn_sigs.get(name) {
                    self.emit(Instruction::Call(sig.param_count as u32), span);
                } else {
                    self.emit(Instruction::Call(1), span);
                }
            }
            _ => {
                self.compile_expr(rhs)?;
                self.emit(Instruction::Call(1), span);
            }
        }
        Ok(())
    }

    fn compile_error_propagate(
        &mut self,
        inner: &crate::ast::Node<Expr>,
        span: Span,
    ) -> CompileResult {
        let catch_jump_idx = self.current_instruction_count();
        self.emit(Instruction::TryBegin(0), span);

        self.compile_expr(inner)?;

        let ok_jump_idx = self.current_instruction_count();
        self.emit(Instruction::Jump(0), span);
        self.emit(Instruction::TryEnd, span);

        let catch_start = self.current_instruction_count();
        self.patch_jump(catch_jump_idx, (catch_start - catch_jump_idx) as i32);

        self.emit(Instruction::Throw, span);

        let after = self.current_instruction_count();
        self.patch_jump(ok_jump_idx, (after - ok_jump_idx) as i32);

        Ok(())
    }

    fn compile_null_coalesce(
        &mut self,
        lhs: &crate::ast::Node<Expr>,
        rhs: &crate::ast::Node<Expr>,
        span: Span,
    ) -> CompileResult {
        self.compile_expr(lhs)?;

        self.emit(Instruction::IsNull, span);

        let jump_idx = self.current_instruction_count();
        self.emit(Instruction::JumpIfNot(0), span);

        self.compile_expr(rhs)?;

        let end_idx = self.current_instruction_count();
        self.patch_jump(jump_idx, (end_idx - jump_idx) as i32);

        Ok(())
    }

    fn compile_struct_init(
        &mut self,
        name: &str,
        fields: &[(String, crate::ast::Node<Expr>)],
        span: Span,
    ) -> CompileResult {
        let ordered_fields = if let Some(struct_fields) = self.registry.lookup_struct(name) {
            let mut result = Vec::with_capacity(fields.len());
            for (sname, _) in struct_fields {
                if let Some((_, expr)) = fields.iter().find(|(n, _)| n == sname) {
                    result.push(expr);
                }
            }
            result
        } else {
            fields.iter().map(|(_, e)| e).collect()
        };

        for field_expr in &ordered_fields {
            self.compile_expr(field_expr)?;
        }

        let field_count = fields.len() as u32;
        self.emit(Instruction::MakeStruct(field_count), span);

        for (_, fexpr) in fields {
            if let Some(t) = self.type_map.get(&fexpr.id) {
                if let Ty::Ref {
                    cap: Capability::Val,
                    ..
                } = t
                {
                    self.emit(Instruction::ArcRetain, span);
                }
            }
        }

        Ok(())
    }

    fn compile_walrus(
        &mut self,
        name: &str,
        value: &crate::ast::Node<Expr>,
        span: Span,
    ) -> CompileResult {
        self.compile_expr(value)?;
        if let Some(scope) = self.scope_stack.last_mut() {
            let slot = scope.alloc(name.to_string());
            self.emit(Instruction::StoreLocal(slot), span);
            self.emit(Instruction::LoadLocal(slot), span);
        }
        Ok(())
    }

    fn push_scope(&mut self) {
        self.scope_stack.push(LocalScope::new());
    }

    fn pop_scope(&mut self) {
        self.scope_stack.pop();
    }

    fn emit(&mut self, instr: Instruction, span: Span) {
        if let Some(func) = &mut self.current_function {
            let idx = func.instructions.len() as u32;
            func.instructions.push(instr);
            func.span_map.push((idx, span));
        }
    }

    fn emit_yield_checkpoint(&mut self, span: Span) {
        self.emit(Instruction::YieldFiber, span);
    }

    fn intern_string(&mut self, s: &str) -> u32 {
        if let Some(&idx) = self.string_table.get(s) {
            return idx;
        }
        let idx = self.module.strings.len() as u32;
        self.module.strings.push(s.to_string());
        self.string_table.insert(s.to_string(), idx);
        idx
    }

    fn current_instruction_count(&mut self) -> usize {
        self.current_function
            .as_ref()
            .map(|f| f.instructions.len())
            .unwrap_or(0)
    }

    fn patch_jump(&mut self, instr_idx: usize, offset: i32) {
        if let Some(func) = &mut self.current_function {
            if instr_idx < func.instructions.len() {
                match &mut func.instructions[instr_idx] {
                    Instruction::Jump(ref mut o) => *o = offset,
                    Instruction::JumpIf(ref mut o) => *o = offset,
                    Instruction::JumpIfNot(ref mut o) => *o = offset,
                    Instruction::TryBegin(ref mut o) => *o = offset,
                    _ => {}
                }
            }
        }
    }

    fn finish_function(&mut self) {
        if let Some(mut func) = self.current_function.take() {
            func.locals = self
                .scope_stack
                .last()
                .map(|s| s.next_slot)
                .unwrap_or(0);
            self.module.functions.push(func);
        }
    }

    pub fn into_module(self) -> MorphIRModule {
        self.module
    }

    pub fn registry(&self) -> &TypeRegistry {
        &self.registry
    }
}

fn resolve_ast_type(ty: &crate::ast::Node<ast::Type>) -> Ty {
    match &ty.kind {
        ast::Type::Named(name) => {
            use crate::typeck::types::{float_kind_from_name, int_kind_from_name};
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
        ast::Type::Generic { name, args } => {
            if name == "Result" && args.len() == 2 {
                Ty::Result {
                    ok: Box::new(resolve_ast_type(&args[0])),
                    err: Box::new(resolve_ast_type(&args[1])),
                }
            } else if name == "Option" && args.len() == 1 {
                Ty::Optional(Box::new(resolve_ast_type(&args[0])))
            } else {
                Ty::Named {
                    name: name.clone(),
                    args: args.iter().map(resolve_ast_type).collect(),
                }
            }
        }
        ast::Type::Tuple(elements) => Ty::Tuple(elements.iter().map(resolve_ast_type).collect()),
        ast::Type::Array(inner) => Ty::Array(Box::new(resolve_ast_type(inner))),
        ast::Type::Optional(inner) => Ty::Optional(Box::new(resolve_ast_type(inner))),
        ast::Type::Reference { cap, inner } => {
            let resolved_cap = match cap {
                ast::Capability::Iso => Capability::Iso,
                ast::Capability::Val => Capability::Val,
                ast::Capability::Ref => Capability::Ref,
            };
            Ty::Ref {
                cap: resolved_cap,
                inner: Box::new(resolve_ast_type(inner)),
            }
        }
        ast::Type::Function { params, ret } => Ty::Fn {
            params: params.iter().map(resolve_ast_type).collect(),
            ret: Box::new(resolve_ast_type(ret)),
            effects: EffectSet::empty(),
        },
        ast::Type::Never => Ty::Never,
        ast::Type::Wildcard => Ty::TypeVar(0),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{
        BinOp, Expr as AstExpr, FnDecl, Item as AstItem, Literal, Node, Stmt as AstStmt,
        Type as AstType, Visibility,
    };
    use crate::lexer::token::Span;
    use crate::typeck::types::{FloatKind, IntKind};

    fn dummy_span() -> Span {
        Span::dummy()
    }

    fn make_lit_int(val: i64) -> Node<AstExpr> {
        Node::new(AstExpr::Literal(Literal::Int(val)), dummy_span())
    }

    fn make_lit_bool(val: bool) -> Node<AstExpr> {
        Node::new(AstExpr::Literal(Literal::Bool(val)), dummy_span())
    }

    fn make_lit_float(val: &str) -> Node<AstExpr> {
        Node::new(
            AstExpr::Literal(Literal::Float(val.to_string())),
            dummy_span(),
        )
    }

    fn make_var(name: &str) -> Node<AstExpr> {
        Node::new(AstExpr::Var(name.to_string()), dummy_span())
    }

    fn make_binop(op: BinOp, lhs: Node<AstExpr>, rhs: Node<AstExpr>) -> Node<AstExpr> {
        Node::new(
            AstExpr::BinaryOp {
                op,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            },
            dummy_span(),
        )
    }

    fn make_block(stmts: Vec<Node<AstStmt>>, expr: Option<Node<AstExpr>>) -> Node<AstExpr> {
        Node::new(
            AstExpr::Block {
                stmts,
                expr: expr.map(Box::new),
            },
            dummy_span(),
        )
    }

    fn make_fn_item(
        name: &str,
        params: Vec<Node<crate::ast::Param>>,
        ret: Option<Node<AstType>>,
        body: Node<AstExpr>,
    ) -> Node<AstItem> {
        Node::new(
            AstItem::FnDecl(FnDecl {
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

    fn make_param(name: &str, type_name: &str) -> Node<crate::ast::Param> {
        Node::new(
            crate::ast::Param {
                name: name.to_string(),
                type_ann: Some(Node::new(AstType::Named(type_name.to_string()), dummy_span())),
            },
            dummy_span(),
        )
    }

    fn make_named_type(name: &str) -> Node<AstType> {
        Node::new(AstType::Named(name.to_string()), dummy_span())
    }

    fn make_stmt_expr(expr: Node<AstExpr>) -> Node<AstStmt> {
        Node::new(AstStmt::ExprStmt(expr), dummy_span())
    }

    fn make_return_stmt(expr: Node<AstExpr>) -> Node<AstStmt> {
        Node::new(AstStmt::Return(Some(expr)), dummy_span())
    }

    #[test]
    fn test_simple_fn_compilation() {
        let body = make_block(vec![], Some(make_lit_int(42)));
        let item = make_fn_item("foo", vec![], Some(make_named_type("i64")), body);
        let result = CodeGen::compile(&[item], HashMap::new());
        assert!(result.is_ok());
        let module = result.unwrap();
        assert_eq!(module.functions.len(), 1);
        assert_eq!(module.functions[0].name, "foo");
    }

    #[test]
    fn test_binary_op_compilation() {
        let expr = make_binop(BinOp::Add, make_lit_int(1), make_lit_int(2));
        let body = make_block(vec![], Some(expr));
        let item = make_fn_item("add_test", vec![], Some(make_named_type("i64")), body);
        let result = CodeGen::compile(&[item], HashMap::new());
        assert!(result.is_ok());
        let module = result.unwrap();
        let func = &module.functions[0];
        assert!(func
            .instructions
            .iter()
            .any(|i| matches!(i, Instruction::Add)));
    }

    #[test]
    fn test_variable_decl_and_use() {
        let val_expr = make_lit_int(10);
        let walrus = Node::new(
            AstExpr::Walrus {
                name: "x".to_string(),
                value: Box::new(val_expr),
                type_ann: None,
            },
            dummy_span(),
        );
        let body = make_block(vec![], Some(walrus));
        let item = make_fn_item("var_test", vec![], Some(make_named_type("i64")), body);
        let result = CodeGen::compile(&[item], HashMap::new());
        assert!(result.is_ok());
        let module = result.unwrap();
        let func = &module.functions[0];
        assert!(func
            .instructions
            .iter()
            .any(|i| matches!(i, Instruction::StoreLocal(_))));
        assert!(func
            .instructions
            .iter()
            .any(|i| matches!(i, Instruction::LoadLocal(_))));
    }

    #[test]
    fn test_if_else_compilation() {
        let cond = make_lit_bool(true);
        let then_br = make_lit_int(1);
        let else_br = make_lit_int(2);
        let if_expr = Node::new(
            AstExpr::If {
                condition: Box::new(cond),
                then_branch: Box::new(then_br),
                else_branch: Some(Box::new(else_br)),
            },
            dummy_span(),
        );
        let body = make_block(vec![], Some(if_expr));
        let item = make_fn_item("if_test", vec![], Some(make_named_type("i64")), body);
        let result = CodeGen::compile(&[item], HashMap::new());
        assert!(result.is_ok());
        let module = result.unwrap();
        let func = &module.functions[0];
        assert!(func
            .instructions
            .iter()
            .any(|i| matches!(i, Instruction::JumpIfNot(_))));
        assert!(func
            .instructions
            .iter()
            .any(|i| matches!(i, Instruction::Jump(_))));
    }

    #[test]
    fn test_function_with_params() {
        let var_x = make_var("x");
        let var_y = make_var("y");
        let add = make_binop(BinOp::Add, var_x, var_y);
        let body = make_block(vec![make_return_stmt(add)], None);
        let item = make_fn_item(
            "add",
            vec![make_param("x", "i64"), make_param("y", "i64")],
            Some(make_named_type("i64")),
            body,
        );
        let result = CodeGen::compile(&[item], HashMap::new());
        assert!(result.is_ok());
        let module = result.unwrap();
        let func = &module.functions[0];
        assert_eq!(func.params.len(), 2);
        assert_eq!(func.params[0].name, "x");
        assert_eq!(func.params[1].name, "y");
    }

    #[test]
    fn test_yield_checkpoint_at_fn_entry() {
        let body = make_block(vec![], Some(make_lit_int(42)));
        let item = make_fn_item("with_yield", vec![], Some(make_named_type("i64")), body);
        let result = CodeGen::compile(&[item], HashMap::new());
        assert!(result.is_ok());
        let module = result.unwrap();
        let func = &module.functions[0];
        assert!(func
            .instructions
            .first()
            .map_or(false, |i| matches!(i, Instruction::YieldFiber)));
    }

    #[test]
    fn test_string_interning() {
        let mut cg = CodeGen::new(HashMap::new());
        assert_eq!(cg.intern_string("hello"), 0);
        assert_eq!(cg.intern_string("world"), 1);
        assert_eq!(cg.intern_string("hello"), 0);
        assert_eq!(cg.module.strings.len(), 2);
    }

    #[test]
    fn test_error_propagation() {
        let inner = make_lit_int(42);
        let prop = Node::new(
            AstExpr::ErrorPropagate {
                expr: Box::new(inner),
            },
            dummy_span(),
        );
        let body = make_block(vec![], Some(prop));
        let item = make_fn_item("err_prop", vec![], None, body);
        let result = CodeGen::compile(&[item], HashMap::new());
        assert!(result.is_ok());
        let module = result.unwrap();
        let func = &module.functions[0];
        assert!(func
            .instructions
            .iter()
            .any(|i| matches!(i, Instruction::TryBegin(_))));
        assert!(func
            .instructions
            .iter()
            .any(|i| matches!(i, Instruction::TryEnd)));
        assert!(func
            .instructions
            .iter()
            .any(|i| matches!(i, Instruction::Throw)));
    }

    #[test]
    fn test_null_coalesce_compilation() {
        let lhs = Node::new(AstExpr::Literal(Literal::Null), dummy_span());
        let rhs = make_lit_int(0);
        let coalesce = Node::new(
            AstExpr::NullCoalesce {
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            },
            dummy_span(),
        );
        let body = make_block(vec![], Some(coalesce));
        let item = make_fn_item("null_coalesce_test", vec![], None, body);
        let result = CodeGen::compile(&[item], HashMap::new());
        assert!(result.is_ok());
        let module = result.unwrap();
        let func = &module.functions[0];
        assert!(func
            .instructions
            .iter()
            .any(|i| matches!(i, Instruction::IsNull)));
    }

    #[test]
    fn test_multiple_functions() {
        let body1 = make_block(vec![], Some(make_lit_int(1)));
        let item1 = make_fn_item("fn1", vec![], Some(make_named_type("i64")), body1);
        let body2 = make_block(vec![], Some(make_lit_int(2)));
        let item2 = make_fn_item("fn2", vec![], Some(make_named_type("i64")), body2);
        let result = CodeGen::compile(&[item1, item2], HashMap::new());
        assert!(result.is_ok());
        let module = result.unwrap();
        assert_eq!(module.functions.len(), 2);
    }

    #[test]
    fn test_comparison_compilation() {
        let expr = make_binop(BinOp::Lt, make_lit_int(1), make_lit_int(2));
        let body = make_block(vec![], Some(expr));
        let item = make_fn_item("cmp_test", vec![], Some(make_named_type("bool")), body);
        let result = CodeGen::compile(&[item], HashMap::new());
        assert!(result.is_ok());
        let module = result.unwrap();
        let func = &module.functions[0];
        assert!(func
            .instructions
            .iter()
            .any(|i| matches!(i, Instruction::Lt)));
    }

    #[test]
    fn test_local_scope_allocation() {
        let mut scope = LocalScope::new();
        let s0 = scope.alloc("x".to_string());
        let s1 = scope.alloc("y".to_string());
        assert_eq!(s0, 0);
        assert_eq!(s1, 1);
        assert_eq!(scope.lookup("x"), Some(0));
        assert_eq!(scope.lookup("y"), Some(1));
        assert_eq!(scope.lookup("z"), None);
    }
}
