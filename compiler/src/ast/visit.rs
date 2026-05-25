use crate::ast::*;

pub trait Visitor {
    fn visit_expr(&mut self, node: &Node<Expr>) {
        walk_expr(self, node)
    }
    fn visit_stmt(&mut self, node: &Node<Stmt>) {
        walk_stmt(self, node)
    }
    fn visit_item(&mut self, node: &Node<Item>) {
        walk_item(self, node)
    }
    fn visit_type(&mut self, node: &Node<Type>) {
        walk_type(self, node)
    }
    fn visit_pattern(&mut self, node: &Node<Pattern>) {
        walk_pattern(self, node)
    }
    fn visit_param(&mut self, node: &Node<Param>) {
        walk_param(self, node)
    }
}

pub fn walk_expr<V: Visitor + ?Sized>(v: &mut V, node: &Node<Expr>) {
    match &node.kind {
        Expr::Literal(_) => {}
        Expr::Var(_) => {}
        Expr::BinaryOp { lhs, rhs, .. } => {
            v.visit_expr(lhs);
            v.visit_expr(rhs);
        }
        Expr::UnaryOp { operand, .. } => {
            v.visit_expr(operand);
        }
        Expr::Call { callee, args } => {
            v.visit_expr(callee);
            for arg in args {
                v.visit_expr(arg);
            }
        }
        Expr::FieldAccess { object, .. } => {
            v.visit_expr(object);
        }
        Expr::Index { object, index } => {
            v.visit_expr(object);
            v.visit_expr(index);
        }
        Expr::Lambda { params, body } => {
            for p in params {
                v.visit_param(p);
            }
            v.visit_expr(body);
        }
        Expr::If {
            condition,
            then_branch,
            else_branch,
        } => {
            v.visit_expr(condition);
            v.visit_expr(then_branch);
            if let Some(e) = else_branch {
                v.visit_expr(e);
            }
        }
        Expr::Match { scrutinee, arms } => {
            v.visit_expr(scrutinee);
            for arm in arms {
                v.visit_pattern(&arm.kind.pattern);
                if let Some(guard) = &arm.kind.guard {
                    v.visit_expr(guard);
                }
                v.visit_expr(&arm.kind.body);
            }
        }
        Expr::Block { stmts, expr } => {
            for s in stmts {
                v.visit_stmt(s);
            }
            if let Some(e) = expr {
                v.visit_expr(e);
            }
        }
        Expr::Pipe { lhs, rhs } => {
            v.visit_expr(lhs);
            v.visit_expr(rhs);
        }
        Expr::ErrorPropagate { expr } => {
            v.visit_expr(expr);
        }
        Expr::NullCoalesce { lhs, rhs } => {
            v.visit_expr(lhs);
            v.visit_expr(rhs);
        }
        Expr::Async { expr } => {
            v.visit_expr(expr);
        }
        Expr::Spawn { expr } => {
            v.visit_expr(expr);
        }
        Expr::StructInit { fields, .. } => {
            for (_, val) in fields {
                v.visit_expr(val);
            }
        }
        Expr::Walrus {
            value, type_ann, ..
        } => {
            v.visit_expr(value);
            if let Some(t) = type_ann {
                v.visit_type(t);
            }
        }
    }
}

pub fn walk_stmt<V: Visitor + ?Sized>(v: &mut V, node: &Node<Stmt>) {
    match &node.kind {
        Stmt::ExprStmt(expr) => {
            v.visit_expr(expr);
        }
        Stmt::VarDecl {
            type_ann, value, ..
        } => {
            if let Some(t) = type_ann {
                v.visit_type(t);
            }
            v.visit_expr(value);
        }
        Stmt::Assign { target, value } => {
            v.visit_expr(target);
            v.visit_expr(value);
        }
        Stmt::Return(expr) => {
            if let Some(e) = expr {
                v.visit_expr(e);
            }
        }
        Stmt::Defer(expr) => {
            v.visit_expr(expr);
        }
        Stmt::Break | Stmt::Continue | Stmt::Nop => {}
        Stmt::While { condition, body } => {
            v.visit_expr(condition);
            for s in body {
                v.visit_stmt(s);
            }
        }
    }
}

pub fn walk_item<V: Visitor + ?Sized>(v: &mut V, node: &Node<Item>) {
    match &node.kind {
        Item::FnDecl(f) => {
            walk_fn_decl(v, f);
        }
        Item::TypeDecl(t) => {
            walk_type_decl(v, t);
        }
        Item::ConstDecl(c) => {
            v.visit_type(&c.type_ann);
            v.visit_expr(&c.value);
        }
        Item::UseDecl(_) => {}
        Item::ActorDecl(a) => {
            walk_actor_decl(v, a);
        }
        Item::ImplBlock(i) => {
            for method in &i.methods {
                walk_fn_decl(v, &method.kind);
            }
        }
        Item::TraitDecl(t) => {
            for method in &t.methods {
                for p in &method.kind.params {
                    v.visit_param(p);
                }
                if let Some(ret) = &method.kind.return_type {
                    v.visit_type(ret);
                }
            }
        }
    }
}

pub fn walk_fn_decl<V: Visitor + ?Sized>(v: &mut V, f: &FnDecl) {
    for p in &f.params {
        v.visit_param(p);
    }
    if let Some(ret) = &f.return_type {
        v.visit_type(ret);
    }
    v.visit_expr(&f.body);
}

pub fn walk_type_decl<V: Visitor + ?Sized>(v: &mut V, t: &TypeDecl) {
    match &t.body {
        TypeBody::Struct(fields) => {
            for f in fields {
                v.visit_type(&f.kind.type_ann);
            }
        }
        TypeBody::Enum(variants) => {
            for variant in variants {
                for field_type in &variant.kind.fields {
                    v.visit_type(field_type);
                }
                if let Some(data) = &variant.kind.data {
                    v.visit_type(data);
                }
            }
        }
        TypeBody::Alias(ty) => {
            v.visit_type(ty);
        }
    }
}

pub fn walk_actor_decl<V: Visitor + ?Sized>(v: &mut V, a: &ActorDecl) {
    for member in &a.members {
        match &member.kind {
            ActorMember::State { type_ann, init, .. } => {
                v.visit_type(type_ann);
                if let Some(init_expr) = init {
                    v.visit_expr(init_expr);
                }
            }
            ActorMember::Event { params, .. } => {
                for p in params {
                    v.visit_param(p);
                }
            }
            ActorMember::OnHandler { body, .. } => {
                v.visit_expr(body);
            }
            ActorMember::FnMember(f) => {
                walk_fn_decl(v, f);
            }
        }
    }
}

pub fn walk_type<V: Visitor + ?Sized>(v: &mut V, node: &Node<Type>) {
    match &node.kind {
        Type::Named(_) | Type::Never | Type::Wildcard => {}
        Type::Generic { args, .. } => {
            for arg in args {
                v.visit_type(arg);
            }
        }
        Type::Tuple(elements) => {
            for elem in elements {
                v.visit_type(elem);
            }
        }
        Type::Array(inner) => {
            v.visit_type(inner);
        }
        Type::Optional(inner) => {
            v.visit_type(inner);
        }
        Type::Reference { inner, .. } => {
            v.visit_type(inner);
        }
        Type::Function { params, ret } => {
            for p in params {
                v.visit_type(p);
            }
            v.visit_type(ret);
        }
    }
}

pub fn walk_pattern<V: Visitor + ?Sized>(v: &mut V, node: &Node<Pattern>) {
    match &node.kind {
        Pattern::Wildcard | Pattern::Var(_) | Pattern::Literal(_) | Pattern::Rest(_) => {}
        Pattern::Constructor { fields, .. } => {
            for (_, pat) in fields {
                v.visit_pattern(pat);
            }
        }
        Pattern::Tuple(elements) => {
            for elem in elements {
                v.visit_pattern(elem);
            }
        }
        Pattern::Or(alternatives) => {
            for alt in alternatives {
                v.visit_pattern(alt);
            }
        }
        Pattern::Range { start, end } => {
            v.visit_pattern(start);
            v.visit_pattern(end);
        }
    }
}

pub fn walk_param<V: Visitor + ?Sized>(v: &mut V, node: &Node<Param>) {
    if let Some(t) = &node.kind.type_ann {
        v.visit_type(t);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::token::Span;

    struct ExprCollector {
        count: usize,
    }

    impl Visitor for ExprCollector {
        fn visit_expr(&mut self, node: &Node<Expr>) {
            self.count += 1;
            walk_expr(self, node);
        }
    }

    #[test]
    fn test_walk_literal() {
        let expr = Node::new(
            Expr::Literal(Literal::Int(42)),
            Span::dummy(),
        );
        let mut collector = ExprCollector { count: 0 };
        collector.visit_expr(&expr);
        assert_eq!(collector.count, 1);
    }

    #[test]
    fn test_walk_binary_op() {
        let lhs = Node::new(Expr::Literal(Literal::Int(1)), Span::dummy());
        let rhs = Node::new(Expr::Literal(Literal::Int(2)), Span::dummy());
        let expr = Node::new(
            Expr::BinaryOp {
                op: BinOp::Add,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            },
            Span::dummy(),
        );
        let mut collector = ExprCollector { count: 0 };
        collector.visit_expr(&expr);
        assert_eq!(collector.count, 3);
    }

    #[test]
    fn test_walk_block() {
        let stmt1 = Node::new(
            Stmt::ExprStmt(Node::new(Expr::Literal(Literal::Int(1)), Span::dummy())),
            Span::dummy(),
        );
        let expr = Node::new(
            Expr::Block {
                stmts: vec![stmt1],
                expr: Some(Box::new(Node::new(
                    Expr::Literal(Literal::Int(2)),
                    Span::dummy(),
                ))),
            },
            Span::dummy(),
        );
        let mut collector = ExprCollector { count: 0 };
        collector.visit_expr(&expr);
        assert_eq!(collector.count, 3);
    }

    #[test]
    fn test_walk_if() {
        let cond = Node::new(Expr::Literal(Literal::Bool(true)), Span::dummy());
        let then = Node::new(Expr::Literal(Literal::Int(1)), Span::dummy());
        let else_ = Node::new(Expr::Literal(Literal::Int(2)), Span::dummy());
        let expr = Node::new(
            Expr::If {
                condition: Box::new(cond),
                then_branch: Box::new(then),
                else_branch: Some(Box::new(else_)),
            },
            Span::dummy(),
        );
        let mut collector = ExprCollector { count: 0 };
        collector.visit_expr(&expr);
        assert_eq!(collector.count, 4);
    }
}
