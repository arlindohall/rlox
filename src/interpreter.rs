// Ignore while building
#![ allow( dead_code, unused_imports, unused_variables, unused_must_use ) ]

use std::collections::HashMap;

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
            Expression::Assignment(n, v) => format!("(define {} {})", n.lexeme, v.to_string()),
            Expression::Binary(l, t, r) => {
                format!("({} {} {})", t.lexeme, l.to_string(), r.to_string())
            }
            Expression::Grouping(e) => format!("{}", e.to_string()),
            Expression::Literal(l) => l.to_string(),
            Expression::Unary(t, e) => format!("({} {})", t.lexeme, e.to_string()),
            Expression::Variable(t) => format!("{}", t.lexeme),
        }
    }
}

// TODO: AstPrinter for Statement

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
            Expression::Variable(token) => Ok(environment.get(&token).clone()),
            Expression::Assignment(token, value) => todo!(),
        }
    }
}

impl Interpreter for Statement {
    fn interpret(
        self,
        lox: &mut Lox,
        environment: &mut Environment,
    ) -> Result<LoxObject, LoxError> {
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
                environment.define(token.lexeme, value);
                Ok(LoxObject::Nil)
            }
            _ => todo!(),
        }
    }
}

pub struct Environment {
    values: HashMap<String, LoxObject>,
}

impl Environment {
    pub fn new() -> Environment {
        Environment {
            values: HashMap::new(),
        }
    }

    fn define(&mut self, name: String, value: LoxObject) {
        self.values.insert(name, value);
    }

    /*
     * The book throws an error when a value doesn't exist, but
     * this is (1) more similar to Lua which I enjoy and (2)
     * something that I feel more languages should have, especially
     * dyanamic languages.
     *
     * One result of this decision to part from Lox's definition in
     * the text is that we could, like Lua, delete values any time
     * their name is set to `Nil`
     */
    fn get<'a, 'b>(&'a self, name: &'b Token) -> &'a LoxObject {
        if let Some(value) = self.values.get(&name.lexeme) {
            value
        } else {
            &LoxObject::Nil
        }
    }
}
