use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::{lox::{LoxError, LoxErrorType}, parser::{Expression, Statement}, scanner::Token};

// Scope needs to be borrowed mutably by peek in a way
// that can't be done with &mut borrows, at least not
// without a little more effort than I want to put in
// right now
type Scope = Rc<RefCell<HashMap<String, bool>>>;
type Scopes = Vec<Scope>;

fn new_scope() -> Scope {
    Rc::new(RefCell::new(HashMap::new()))
}

fn peek(scopes: &Scopes) -> Option<Scope> {
    scopes
        .get(scopes.len() - 1)
        .map(|sc| sc.clone())
}

pub trait Resolver {
    fn resolve(&mut self, scopes: &mut Scopes) -> Result<(), LoxError>;

    fn resolve_statements(&self, scopes: &mut Scopes, statements: &mut Vec<Statement>) -> Result<(), LoxError> {
        for statement in statements {
            statement.resolve(scopes)?
        }
        Ok(())
    }

    fn resolve_local(&self, scopes: &mut Scopes, expr: &mut Expression, name: &Token) {
        let mut i = scopes.len();
        for scope in scopes.iter().rev() {
            i -= 1;
            if scope.borrow().contains_key(&name.lexeme) {
                expr.resolve_at(i);
            }
        }
    }

    fn begin_scope(&mut self, scopes: &mut Scopes) {
        scopes.push(new_scope());
    }

    fn end_scope(&self, scopes: &mut Scopes) {
        scopes.pop();
    }

    fn declare(&self, scopes: &mut Scopes, name: &Token) {
        if let Some(scope) = peek(scopes) {
            scope.borrow_mut().insert(name.lexeme.to_string(), false);
        }
    }

    fn define(&self, scopes: &mut Scopes, name: &Token) {
        if let Some(scope) = peek(scopes) {
            scope.borrow_mut().insert(name.lexeme.to_string(), true);
        }
    }

    fn resolve_function(&mut self, scopes: &mut Scopes, statement: &mut Statement) -> Result<(), LoxError> {
        if let Statement::Function(_name, params, body) = statement {
            self.begin_scope(scopes);
            for param in params {
                self.declare(scopes, param);
                self.define(scopes, param);
            }
            self.resolve_statements(scopes, body)?;
            self.end_scope(scopes);
        }
        Ok(())
    }
}

impl Resolver for Expression {
    fn resolve(&mut self, scopes: &mut Scopes) -> Result<(), LoxError> {
        match self.clone() {
            Expression::Assignment(_, name, value) => {
                self.resolve(scopes)?;
                self.resolve_local(scopes, &mut (*value), &name)
            }
            Expression::Binary(_, left, _op, right) => {
                left.resolve(scopes)?;
                right.resolve(scopes)?;
            }
            Expression::Grouping(_, expr) => {
                expr.resolve(scopes)?;
            }
            Expression::Literal(_, _) => (),
            Expression::Logical(_, left, _op, right) => {
                left.resolve(scopes)?;
                right.resolve(scopes)?;
            }
            Expression::Unary(_, _op, target) => {
                target.resolve(scopes)?;
            }
            Expression::Call(_, callee, _paren, params) => {
                callee.resolve(scopes)?;
                for param in params {
                    param.resolve(scopes)?;
                }
            }
            Expression::Variable(_, name) => {
                if let Some(scope) = peek(scopes) {
                    if scope.borrow().contains_key(&name.lexeme) && !scope.borrow().get(&name.lexeme).unwrap() {
                        return Err(crate::lox::parse_error(
                            name.clone(),
                            LoxErrorType::InitializationError,
                            "can't read local variable in its own initializer"
                        ))
                    }
                }
                self.resolve_local(scopes, self, &name)
            }
        }
        Ok(())
    }
}

impl Resolver for Statement {
    fn resolve(&mut self, scopes: &mut Scopes) -> Result<(), LoxError> {
        match self {
            Statement::Print(expr) => {
                expr.resolve(scopes)?;
            }
            Statement::Expression(expr) => {
                expr.resolve(scopes)?;
            }
            Statement::Block(statements) => {
                self.begin_scope(scopes);
                self.resolve_statements(scopes, statements)?;
                self.end_scope(scopes);
            }
            Statement::Var(name, value) => {
                self.declare(scopes, name);
                if let Some(val) = value {
                    val.resolve(scopes)?;
                }
                self.define(scopes, name);
            }
            Statement::If(cond, if_stmt, else_stmt) => {
                cond.resolve(scopes)?;
                if_stmt.resolve(scopes)?;
                if let Some(stmt) = else_stmt {
                    stmt.resolve(scopes)?;
                }
            }
            Statement::Function(name, _, _) => {
                self.declare(scopes, name);
                self.define(scopes, name);
                self.resolve_function(scopes, self)?;
            }
            Statement::While(cond, stmt) => {
                cond.resolve(scopes)?;
                stmt.resolve(scopes)?;
            }
            Statement::Return(_keywd, expr) => {
                expr.resolve(scopes)?;
            }
            Statement::None => ()
        }
        Ok(())
    }
}