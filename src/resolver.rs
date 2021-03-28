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
    fn resolve(&self, scopes: &mut Scopes) -> Result<(), LoxError>;

    fn resolve_statements(&self, scopes: &mut Scopes, statements: &Vec<Statement>) -> Result<(), LoxError> {
        for statement in statements {
            statement.resolve(scopes)?
        }
        Ok(())
    }

    fn resolve_local(&self, scopes: &mut Scopes, expr: &Expression, name: &Token) {
        let mut i = scopes.len();
        for scope in scopes.iter().rev() {
            i -= 1;
            if scope.borrow().contains_key(&name.lexeme) {
                expr.resolve_at(i);
            }
        }
    }

    fn begin_scope(&self, scopes: &mut Scopes) {
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

    fn resolve_function(&self, scopes: &mut Scopes, statement: &Statement) -> Result<(), LoxError> {
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
    fn resolve(&self, scopes: &mut Scopes) -> Result<(), LoxError> {
        match self {
            Expression::Assignment(name, value) => {
                self.resolve(scopes)?;
                self.resolve_local(scopes, value, name)
            }
            Expression::Binary(_, _, _) => {}
            Expression::Grouping(_) => {}
            Expression::Literal(_) => {}
            Expression::Logical(_, _, _) => {}
            Expression::Unary(_, _) => {}
            Expression::Call(_, _, _) => {}
            Expression::Variable(name) => {
                if let Some(scope) = peek(scopes) {
                    if scope.borrow().contains_key(&name.lexeme) && !scope.borrow().get(&name.lexeme).unwrap() {
                        return Err(crate::lox::parse_error(
                            name.clone(),
                            LoxErrorType::InitializationError,
                            "can't read local variable in its own initializer"
                        ))
                    }
                }
                self.resolve_local(scopes, self, name)
            }
        }
        Ok(())
    }
}

impl Resolver for Statement {
    fn resolve(&self, scopes: &mut Scopes) -> Result<(), LoxError> {
        match self {
            Statement::Print(_) => {}
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
            Statement::If(_, _, _) => {}
            Statement::Function(name, _, _) => {
                self.declare(scopes, name);
                self.define(scopes, name);
                self.resolve_function(scopes, self)?;
            }
            Statement::While(_, _) => {}
            Statement::Return(_, _) => {}
            Statement::None => {}
        }
        Ok(())
    }
}