#![allow(dead_code)]

use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::{
    interpreter::Interpreter,
    lox::{LoxError, LoxErrorType},
    parser::{Expression, Statement},
    scanner::Token,
};

/*******************************************************************************
********************************************************************************
                                RESOLVER
********************************************************************************

The resolver walks the parse tree just like the interpreter, but instead of
tracking an environment and evaluating expressions, it only takes action on
variable or assignment expressions. The resolver adds each of these
expressions to a map by a unique id, which is held by the expression itself.
The map of expressions contains the number of "jumps" that are needed to
reach the variable in question in the environment.

The resolver uses private types to track all of this state, Scope and Scopes,
so that the internals can be changed without affecting the rest of the
interpreter.

*******************************************************************************/

// Scope needs to be borrowed mutably by peek in a way
// that can't be done with &mut borrows, at least not
// without a little more effort than I want to put in
// right now
type Scope = Rc<RefCell<HashMap<String, bool>>>;
type Scopes = Vec<Scope>;

fn new_scope() -> Scope {
    Rc::new(RefCell::new(HashMap::new()))
}

pub struct Resolver {
    interpreter: Interpreter,
    scopes: Scopes,
    current_function: FunctionType,
}

type FunctionType = Option<()>;

fn is_function(ft: FunctionType) -> bool {
    ft.is_some()
}

impl Resolver {
    pub fn new(interpreter: Interpreter) -> Resolver {
        Resolver {
            interpreter,
            scopes: vec![new_scope()],
            current_function: None,
        }
    }

    pub fn destruct(self) -> Interpreter {
        self.interpreter
    }

    fn resolve_statements(&mut self, statements: &Vec<Statement>) -> Result<(), LoxError> {
        for statement in statements {
            self.resolve_statement(statement)?
        }
        Ok(())
    }

    fn resolve_local(&mut self, expr: &Expression, name: &Token) {
        // Not sure what's going on here, I must have reversed something
        // by not reading the code closely, idk. This works so I guess
        // it's fine for now
        // let mut i = self.scopes.len() as u16;
        let mut i = 0;
        crate::lox::trace(format!(
            ">>> Resolving local variable expr={:?}, scopes={:?}",
            name.lexeme, self.scopes,
        ));
        for scope in self.scopes.iter().rev() {
            i += 1;
            if scope.borrow().contains_key(&name.lexeme) {
                crate::lox::trace(format!(">>> Found at {}", i));
                self.interpreter.resolve(expr.clone(), i);
                return;
            }
        }
    }

    fn begin_scope(&mut self) {
        self.scopes.push(new_scope());
    }

    fn end_scope(&mut self) {
        self.scopes.pop();
    }

    fn peek(&self) -> Option<Scope> {
        self.scopes.get(self.scopes.len() - 1).map(|sc| sc.clone())
    }

    fn declare(&mut self, name: &Token) -> Result<(), LoxError> {
        if let Some(scope) = self.peek() {
            if scope.borrow().contains_key(&name.lexeme) {
                return Err(crate::lox::parse_error(
                    name.clone(),
                    LoxErrorType::DefinitionError,
                    "already a variable with this name in scope",
                ));
            }
            scope.borrow_mut().insert(name.lexeme.to_string(), false);
        }
        Ok(())
    }

    fn define(&self, name: &Token) {
        if let Some(scope) = self.peek() {
            scope.borrow_mut().insert(name.lexeme.to_string(), true);
        }
    }

    fn resolve_function(
        &mut self,
        statement: &Statement,
        function_type: FunctionType,
    ) -> Result<(), LoxError> {
        let mut enclosing_function = std::mem::replace(&mut self.current_function, function_type);
        if let Statement::Function(definition) = statement {
            self.begin_scope();
            for param in definition.params.iter() {
                self.declare(&param)?;
                self.define(&param);
            }
            self.resolve_statements(&definition.body)?;
            self.end_scope();
        }
        std::mem::swap(&mut enclosing_function, &mut self.current_function);
        Ok(())
    }

    fn resolve_expression(&mut self, expression: &Expression) -> Result<(), LoxError> {
        match expression {
            Expression::Assignment(_, name, value) => {
                self.resolve_expression(&value)?;
                self.resolve_local(expression, &name)
            }
            Expression::Binary(left, _op, right) => {
                self.resolve_expression(left)?;
                self.resolve_expression(&right)?;
            }
            Expression::Grouping(expr) => {
                self.resolve_expression(&expr)?;
            }
            Expression::Literal(_) => (),
            Expression::Logical(left, _op, right) => {
                self.resolve_expression(&left)?;
                self.resolve_expression(&right)?;
            }
            Expression::Unary(_op, target) => {
                self.resolve_expression(&target)?;
            }
            Expression::Call(callee, _paren, params) => {
                self.resolve_expression(&callee)?;
                for param in params {
                    self.resolve_expression(param)?;
                }
            }
            Expression::Set(object, _name, value) => {
                self.resolve_expression(value)?;
                self.resolve_expression(object)?;
            }
            Expression::Get(object, _name) => {
                self.resolve_expression(object)?;
            }
            Expression::Variable(_, name) => {
                if let Some(scope) = self.peek() {
                    if scope.borrow().contains_key(&name.lexeme)
                        && !scope.borrow().get(&name.lexeme).unwrap()
                    {
                        return Err(crate::lox::parse_error(
                            name.clone(),
                            LoxErrorType::InitializationError,
                            "can't read local variable in its own initializer",
                        ));
                    }
                }
                self.resolve_local(&expression, &name)
            }
        }
        Ok(())
    }

    pub fn resolve_statement(&mut self, statement: &Statement) -> Result<(), LoxError> {
        match statement {
            Statement::Print(expr) => {
                self.resolve_expression(expr)?;
            }
            Statement::Expression(expr) => {
                self.resolve_expression(expr)?;
            }
            Statement::Block(statements) => {
                crate::lox::trace(format!(
                    ">>> Resolving block statement stmt={:?}",
                    statement
                ));
                self.begin_scope();
                self.resolve_statements(&statements)?;
                self.end_scope();
            }
            Statement::Var(name, value) => {
                self.declare(&name)?;
                if let Some(val) = value {
                    self.resolve_expression(val)?;
                }
                self.define(&name);
            }
            Statement::If(cond, if_stmt, else_stmt) => {
                self.resolve_expression(cond)?;
                self.resolve_statement(&if_stmt)?;
                if let Some(stmt) = else_stmt {
                    self.resolve_statement(&stmt)?;
                }
            }
            Statement::Function(definition) => {
                self.declare(&definition.name)?;
                self.define(&definition.name);
                self.resolve_function(&statement, Some(()))?;
            }
            Statement::While(cond, stmt) => {
                crate::lox::trace(format!(
                    ">>> Resolving while statement stmt={:?}",
                    statement
                ));
                self.resolve_expression(cond)?;
                self.resolve_statement(&stmt)?;
            }
            Statement::Return(keyword, expr) => {
                if !is_function(self.current_function) {
                    return Err(crate::lox::parse_error(
                        keyword.clone(),
                        LoxErrorType::FunctionCallError,
                        "",
                    ));
                }
                self.resolve_expression(expr)?;
            }
            Statement::None => (),
            Statement::Class(name, _functions) => {
                self.declare(name)?;
                self.define(name);
            }
        }
        Ok(())
    }
}
