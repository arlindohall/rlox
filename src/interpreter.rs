// Ignore while building
#![ allow( dead_code, unused_imports, unused_variables, unused_must_use ) ]

use std::{borrow::Borrow, collections::HashMap};

use crate::lox::{Lox, LoxError, LoxErrorType, LoxNumber};
use crate::parser::{Expression, LoxObject, Statement};
use crate::scanner::{Token, TokenType};

/*******************************************************************************
********************************************************************************
                                INTERPRETER
********************************************************************************

This is the final division of the interpreter, which does the actual
interpreting of expressions. In the book this is done using a visitor pattern
because the initial implementation is done in Java. However, since I've used
Rust, some functional approaches make more sense, and so I've used the
pattern the book describes as "too hard to maintain for large code bases,"
and I just sort of am resolved to having to refactor in the future if I ever
change that.

It's not a huge deal since this is a side project, but in my opinion, this
way of doing things is easier to understand for the Lox language, while the
visitor pattern splits all the behavior necessary to the language up into
different files and classes when it really ought to live next to the trait or
struct (or in Java the class) where it is actually used.

The interpreter's job is to produce a value for each expression.

*******************************************************************************/

pub trait AstPrinter {
    fn to_string(&self) -> String;
}

/*
The Interpreter consumes the expression completely because it pulls the
components out to evaluate them. If you need to re-use the whole expression,
you should clone it first.

TODO: The environment in the book is a property of the Interpreter class, but
we implement enterpreter for both expression and statement, and it looks like
the environment is setting up to be not only mutable but movable, so I'm going
to pass in a parameter for now until I've got more details. Clean this up
later.
*/
pub trait Interpreter {
    fn interpret(self, lox: &mut Lox, environment: &mut Environment)
        -> Result<LoxObject, LoxError>;
}

impl AstPrinter for Expression {
    fn to_string(&self) -> String {
        match self {
            Expression::Assignment(n, v) => format!("(assign {} {})", n.lexeme, v.to_string()),
            Expression::Binary(l, t, r) => {
                format!("({} {} {})", t.lexeme, l.to_string(), r.to_string())
            }
            Expression::Grouping(e) => format!("{}", e.to_string()),
            Expression::Literal(l) => l.to_string(),
            Expression::Logical(l, op, r) => {
                format!("({} {} {})", op.lexeme, l.to_string(), r.to_string())
            }
            Expression::Unary(t, e) => format!("({} {})", t.lexeme, e.to_string()),
            Expression::Call(callee, _, args) => {
                let args: Vec<String> = args.iter().map(|arg| arg.to_string()).collect();
                format!("({} {})", callee.to_string(), args.join(" "))
            }
            Expression::Variable(t) => format!("{}", t.lexeme),
        }
    }
}

impl AstPrinter for Statement {
    fn to_string(&self) -> String {
        match self {
            Statement::Block(statements) => {
                let printed: Vec<String> = statements.iter().map(|s| s.to_string()).collect();
                format!("(do {})", printed.join(" "))
            }
            Statement::Print(expr) => format!("(print {})", expr.to_string()),
            Statement::Expression(expr) => format!("({})", expr.to_string()),
            Statement::Var(name, Some(value)) => {
                format!("(define {} {})", name.lexeme, value.to_string())
            }
            Statement::Var(name, None) => format!("(define {} nil)", name.lexeme),
            Statement::If(condition, then_st, Some(else_st)) => format!(
                "(if ({}) ({}) ({}))",
                condition.to_string(),
                then_st.to_string(),
                else_st.to_string()
            ),
            Statement::If(condition, then_st, None) => {
                format!("(if ({}) ({}))", condition.to_string(), then_st.to_string())
            }
            Statement::While(condition, do_st) => format!(
                "(do-while ({}) ({})",
                condition.to_string(),
                do_st.to_string()
            ),
            Statement::None => "()".to_owned(),
        }
    }
}

impl Interpreter for Expression {
    fn interpret(
        self,
        lox: &mut Lox,
        environment: &mut Environment,
    ) -> Result<LoxObject, LoxError> {
        match self.clone() {
            Expression::Grouping(expr) => expr.interpret(lox, environment),
            Expression::Literal(obj) => Ok(obj),
            Expression::Unary(op, value) => {
                let obj = value.clone().interpret(lox, environment)?;
                match op.token_type {
                    TokenType::Minus => {
                        if let LoxObject::Number(n) = obj {
                            Ok(LoxObject::Number(-n))
                        } else {
                            Err(lox.runtime_error(
                                self,
                                LoxErrorType::TypeError,
                                &format!(
                                    "cannot negate `{}` — expected Number, found {}",
                                    obj.to_string(),
                                    obj.get_type()
                                ),
                            ))
                        }
                    }
                    TokenType::Bang => {
                        if Self::is_truthy(obj) {
                            Ok(LoxObject::Boolean(false))
                        } else {
                            Ok(LoxObject::Boolean(true))
                        }
                    }
                    _ => Err(lox.runtime_error(
                        self,
                        LoxErrorType::UnknownOperator,
                        &format!("'{:?}'", op.token_type),
                    )),
                }
            }
            Expression::Binary(left, op, right) => {
                let robj = right.clone().interpret(lox, environment)?;
                let lobj = left.clone().interpret(lox, environment)?;

                match op.token_type {
                    TokenType::Minus => match (lobj, robj) {
                        (LoxObject::Number(l), LoxObject::Number(r)) => {
                            Ok(LoxObject::Number(l - r))
                        }
                        _ => Err(lox.runtime_error(
                            self,
                            LoxErrorType::TypeError,
                            "cannot subtract non-numbers",
                        )),
                    },
                    TokenType::Slash => match (lobj, robj) {
                        (LoxObject::Number(l), LoxObject::Number(r)) => {
                            if r == 0.0 {
                                Err(lox.runtime_error(
                                    self,
                                    LoxErrorType::DivideByZeroError,
                                    "divide by zero",
                                ))
                            } else {
                                Ok(LoxObject::Number(l / r))
                            }
                        }
                        _ => Err(lox.runtime_error(
                            self,
                            LoxErrorType::TypeError,
                            "cannot divide non-numbers",
                        )),
                    },
                    TokenType::Star => match (lobj, robj) {
                        (LoxObject::Number(l), LoxObject::Number(r)) => {
                            Ok(LoxObject::Number(l * r))
                        }
                        _ => Err(lox.runtime_error(
                            self,
                            LoxErrorType::TypeError,
                            "cannot multiply non-numbers",
                        )),
                    },
                    TokenType::Plus => match (lobj, robj) {
                        (LoxObject::Number(l), LoxObject::Number(r)) => {
                            Ok(LoxObject::Number(l + r))
                        }
                        (LoxObject::String(l), LoxObject::String(r)) => {
                            Ok(LoxObject::String(l.clone() + &r))
                        }
                        _ => Err(lox.runtime_error(
                            self,
                            LoxErrorType::TypeError,
                            "addition is defined for numbers and strings",
                        )),
                    },
                    TokenType::Greater
                    | TokenType::GreaterEqual
                    | TokenType::Less
                    | TokenType::LessEqual => self.apply_compare(lox, op.token_type, lobj, robj),
                    TokenType::EqualEqual => Ok(LoxObject::Boolean(lobj == robj)),
                    TokenType::BangEqual => Ok(LoxObject::Boolean(lobj != robj)),
                    _ => panic!("unimplemented binary operator"),
                }
            }
            Expression::Variable(token) => Ok(environment.get(lox, self, token)?.clone()),
            Expression::Assignment(name, value) => {
                // TODO: This clone could be super expensive, if the whole program is one assignment
                crate::lox::trace(format!(
                    ">>> Modifying environment={}",
                    environment.to_string()
                ));
                let result = value.clone().interpret(lox, environment)?;
                environment.assign(lox, *value, name, result.clone());
                crate::lox::trace(format!(
                    ">>> Done modifying environment={}",
                    environment.to_string()
                ));

                Ok(result)
            }
            Expression::Logical(l, op, r) => {
                let left = l.interpret(lox, environment)?;

                if op.token_type == TokenType::Or && Self::is_truthy(left.clone()) {
                    Ok(left)
                } else if op.token_type == TokenType::And && !Self::is_truthy(left.clone()) {
                    Ok(left)
                } else {
                    r.interpret(lox, environment)
                }
            }
            Expression::Call(callee, paren, args) => {
                let callee_obj = callee.clone().interpret(lox, environment)?;

                let mut arguments = Vec::new();
                for arg in args {
                    arguments.push(arg.interpret(lox, environment)?);
                }

                let mut func: LoxCallable = LoxCallable::try_from(lox, callee_obj)?;
                if func.arity() as usize != arguments.len() {
                    Err(lox.runtime_error(
                        *callee,
                        LoxErrorType::FunctionCallError,
                        &format!(
                            "expected {} arguments but got {}.",
                            func.arity(),
                            arguments.len()
                        ),
                    ))
                } else {
                    func.call_lox_func(lox, arguments)
                }
            }
        }
    }
}

impl Interpreter for Statement {
    fn interpret(
        self,
        lox: &mut Lox,
        environment: &mut Environment,
    ) -> Result<LoxObject, LoxError> {
        crate::lox::trace(format!(
            ">>> Interpreting at statement={} env={}",
            self.to_string(),
            environment.to_string()
        ));
        match self {
            Statement::Print(expr) => {
                let obj = expr.interpret(lox, environment)?;
                println!("{}", obj.to_string());
                Ok(obj)
            }
            Statement::Expression(expr) => expr.interpret(lox, environment),
            Statement::Var(token, expr) => {
                let value = match expr {
                    Some(expr) => expr.interpret(lox, environment),
                    None => Ok(LoxObject::Nil),
                }?;
                crate::lox::trace(format!(
                    ">>> Defining new variable={} value={}",
                    token.lexeme,
                    value.to_string()
                ));
                environment.define(token.lexeme, value.clone());
                crate::lox::trace(format!(
                    ">>> After definition env={}",
                    environment.to_string()
                ));
                Ok(value)
            }
            Statement::Block(statements) => {
                let parent = std::mem::replace(environment, Environment::new());
                let mut block = Environment::extend(parent);

                let mut last = LoxObject::Nil;
                for statement in statements {
                    last = statement.interpret(lox, &mut block)?;
                }

                std::mem::replace(environment, *block.enclosing.unwrap());
                Ok(last)
            }
            Statement::If(cond, then_st, else_st) => {
                if Expression::is_truthy(cond.interpret(lox, environment)?) {
                    then_st.interpret(lox, environment)
                } else {
                    match else_st {
                        Some(st) => st.interpret(lox, environment),
                        None => Ok(LoxObject::Nil),
                    }
                }
            }
            Statement::While(cond, do_st) => {
                // TODO: This is expensive, maybe don't consume on interpret?
                while Expression::is_truthy(cond.clone().interpret(lox, environment)?) {
                    do_st.clone().interpret(lox, environment)?;
                }

                Ok(LoxObject::Nil)
            }
            Statement::None => Ok(LoxObject::Nil),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Environment {
    values: HashMap<String, LoxObject>,
    enclosing: Option<Box<Environment>>,
}

impl Environment {
    pub fn new() -> Environment {
        Environment {
            values: HashMap::new(),
            enclosing: None,
        }
    }

    pub fn extend(environment: Environment) -> Environment {
        Environment {
            values: HashMap::new(),
            enclosing: Some(Box::new(environment)),
        }
    }

    fn define(&mut self, name: String, value: LoxObject) {
        crate::lox::trace(format!(
            ">>> Inserted into environment name={} val={}",
            name,
            value.to_string()
        ));
        self.values.insert(name, value);
        crate::lox::trace(format!(
            ">>> Raw environment contents map={:?}",
            self.values
        ));
    }

    fn define_global(&mut self, name: String, value: LoxObject) {
        match &mut self.enclosing {
            Some(env) => env.define_global(name, value),
            None => {
                self.values.insert(name, value);
            }
        }
    }

    fn get(
        &self,
        lox: &mut Lox,
        expression: Expression,
        name: Token,
    ) -> Result<LoxObject, LoxError> {
        crate::lox::trace(format!(
            ">>> Debugging get at expression={}, token={:?}, environment={}",
            expression.to_string(),
            name,
            self.to_string(),
        ));
        if let Some(value) = self.values.get(&name.lexeme) {
            Ok(value.clone())
        } else if self.enclosing.is_some() {
            Ok(self
                .enclosing
                .as_ref()
                .unwrap()
                .get(lox, expression, name)?
                .clone())
        } else {
            Err(lox.runtime_error(
                expression,
                LoxErrorType::AssignmentError,
                &format!("undefined variable {}", name.lexeme),
            ))
        }
    }

    fn assign(
        &mut self,
        lox: &mut Lox,
        expression: Expression,
        name: Token,
        value: LoxObject,
    ) -> Result<(), LoxError> {
        if self.values.contains_key(&name.lexeme) {
            self.values.insert(name.lexeme, value);
            Ok(())
        } else if let Some(environ) = &mut self.enclosing {
            environ.assign(lox, expression, name, value);
            Ok(())
        } else {
            Err(lox.runtime_error(
                expression,
                LoxErrorType::AssignmentError,
                &format!("undefined variable {}", name.lexeme),
            ))
        }
    }
}

impl AstPrinter for Environment {
    fn to_string(&self) -> String {
        let values: Vec<String> = self
            .values
            .iter()
            .map(|(k, v)| format!("(var {} {:?})", k, v))
            .collect();
        let values = values.join(" ");
        match &self.enclosing {
            Some(enc) => format!("(({}) (enclosing {}))", values, enc.to_string()),
            None => format!("(({}))", values),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct LoxCallable {
    arity: u8,
    env: Environment,
    block: Box<Statement>,
}

impl LoxCallable {
    fn try_from(lox: &mut Lox, object: LoxObject) -> Result<LoxCallable, LoxError> {
        fn err(lox: &mut Lox, object: LoxObject) -> Result<LoxCallable, LoxError> {
            Err(lox.runtime_error(
                Expression::Literal(object),
                LoxErrorType::FunctionCallError,
                &format!(""),
            ))
        };
        match &object {
            // TODO: This is a total guess but I have a feeling we're heading somewhere like this
            LoxObject::Function(f) => Ok(f.clone()),
            LoxObject::Object(vals) => {
                match vals.get("__call") {
                    Some(obj) => Self::try_from(lox, *(obj.clone())),
                    None => err(lox, object),
                }
            }
            _ => err(lox, object),
        }
    }

    fn arity(&self) -> u8 {
        self.arity
    }

    fn call_lox_func(
        &mut self,
        lox: &mut Lox,
        args: Vec<LoxObject>,
    ) -> Result<LoxObject, LoxError> {
        // TODO: make new environment with args
        self.block.clone().interpret(lox, &mut self.env)
    }
}
