#![allow(dead_code)]

use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::{
    interpreter::Interpreter,
    lox::{LoxError, LoxErrorType},
    parser::{ClassDefinition, Expression, FunctionDefinition, Statement},
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
    current_class: ClassType,
}

enum FunctionType {
    Function,
    Method,
    Initializer,
    None,
}

enum ClassType {
    Class,
    None,
}

impl FunctionType {
    fn is_none(&self) -> bool {
        match self {
            &FunctionType::None => true,
            _ => false,
        }
    }

    fn is_initializer(&self) -> bool {
        match self {
            &FunctionType::Initializer => true,
            _ => false,
        }
    }
}

impl ClassType {
    fn is_none(&self) -> bool {
        match self {
            ClassType::None => true,
            _ => false,
        }
    }
}

impl Resolver {
    pub fn new(interpreter: Interpreter) -> Resolver {
        Resolver {
            interpreter,
            scopes: vec![new_scope()],
            current_function: FunctionType::None,
            current_class: ClassType::None,
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
        definition: &FunctionDefinition,
        function_type: FunctionType,
    ) -> Result<(), LoxError> {
        let mut enclosing_function = std::mem::replace(&mut self.current_function, function_type);
        self.begin_scope();
        for param in definition.params.iter() {
            self.declare(&param)?;
            self.define(&param);
        }
        self.resolve_statements(&definition.body)?;
        self.end_scope();
        std::mem::swap(&mut enclosing_function, &mut self.current_function);
        Ok(())
    }

    fn resolve_expression(&mut self, expression: &Expression) -> Result<(), LoxError> {
        match expression {
            Expression::Assignment { name, value, .. } => {
                self.resolve_expression(&value)?;
                self.resolve_local(expression, &name)
            }
            Expression::Binary { left, right, .. } => {
                self.resolve_expression(left)?;
                self.resolve_expression(&right)?;
            }
            Expression::Grouping { expression } => {
                self.resolve_expression(&expression)?;
            }
            Expression::Literal { .. } => (),
            Expression::Logical { left, right, .. } => {
                self.resolve_expression(&left)?;
                self.resolve_expression(&right)?;
            }
            Expression::Unary { value, .. } => {
                self.resolve_expression(&value)?;
            }
            Expression::Call { callee, args, .. } => {
                self.resolve_expression(&callee)?;
                for arg in args {
                    self.resolve_expression(arg)?;
                }
            }
            Expression::This { keyword, .. } => {
                if self.current_class.is_none() {
                    return Err(crate::lox::parse_error(
                        keyword.clone(),
                        LoxErrorType::ReferenceError,
                        "can't use 'this' outside of class",
                    ));
                }
                self.resolve_local(expression, keyword);
            }
            Expression::Super { keyword, .. } => {
                self.resolve_local(expression, keyword);
            }
            Expression::Set { object, value, .. } => {
                self.resolve_expression(value)?;
                self.resolve_expression(object)?;
            }
            Expression::Get { object, .. } => {
                self.resolve_expression(object)?;
            }
            Expression::Variable { name, .. } => {
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
            Statement::Print { expression } => {
                self.resolve_expression(expression)?;
            }
            Statement::Expression { expression } => {
                self.resolve_expression(expression)?;
            }
            Statement::Block { statements, .. } => {
                crate::lox::trace(format!(
                    ">>> Resolving block statement stmt={:?}",
                    statement
                ));
                self.begin_scope();
                self.resolve_statements(&statements)?;
                self.end_scope();
            }
            Statement::Var { name, initializer } => {
                self.declare(&name)?;
                if let Some(val) = initializer {
                    self.resolve_expression(val)?;
                }
                self.define(&name);
            }
            Statement::If {
                condition,
                then_statement,
                else_statement,
            } => {
                self.resolve_expression(condition)?;
                self.resolve_statement(&then_statement)?;
                if let Some(stmt) = else_statement {
                    self.resolve_statement(&stmt)?;
                }
            }
            Statement::Function { definition } => {
                self.declare(&definition.name)?;
                self.define(&definition.name);
                self.resolve_function(&definition, FunctionType::Function)?;
            }
            Statement::While { condition, body } => {
                crate::lox::trace(format!(
                    ">>> Resolving while statement stmt={:?}",
                    statement
                ));
                self.resolve_expression(condition)?;
                self.resolve_statement(&body)?;
            }
            Statement::Return { keyword, value } => {
                if self.current_function.is_initializer() && value.is_nil() {
                    return Err(crate::lox::parse_error(
                        keyword.clone(),
                        LoxErrorType::FunctionCallError,
                        "cannot return a value from an initializer",
                    ));
                }
                if self.current_function.is_none() {
                    return Err(crate::lox::parse_error(
                        keyword.clone(),
                        LoxErrorType::FunctionCallError,
                        "cannot return outside a function or method",
                    ));
                }
                self.resolve_expression(value)?;
            }
            Statement::None => (),
            Statement::Class {
                definition:
                    ClassDefinition {
                        name,
                        methods,
                        superclass,
                    },
            } => {
                let mut enclosing = std::mem::replace(&mut self.current_class, ClassType::Class);

                self.declare(name)?;
                self.define(name);

                if let Some(Expression::Variable {
                    name: super_name, ..
                }) = superclass
                {
                    if name.lexeme == super_name.lexeme {
                        return Err(crate::lox::parse_error(
                            super_name.clone(),
                            LoxErrorType::ClassError,
                            "class cannot inherit from itself",
                        ));
                    }
                } else if let Some(_expression) = superclass {
                    return Err(crate::lox::parse_error(
                        name.clone(),
                        LoxErrorType::ClassError,
                        &format!("cannot inherit from non-class"),
                    ));
                }

                if let Some(superclass) = superclass {
                    self.resolve_expression(superclass)?;
                    self.begin_scope();
                    self.peek().unwrap().borrow_mut().insert("super".to_string(), true);
                }

                self.begin_scope();
                self.peek()
                    .unwrap()
                    .borrow_mut()
                    .insert("this".to_string(), true);

                for method in methods {
                    let function_type = if method.name.lexeme == "init" {
                        FunctionType::Initializer
                    } else {
                        FunctionType::Method
                    };
                    self.resolve_function(method, function_type)?;
                }

                self.end_scope();

                if let Some(_superclass) = superclass {
                    self.end_scope();
                }

                std::mem::swap(&mut enclosing, &mut self.current_class);
            }
        }
        Ok(())
    }
}
