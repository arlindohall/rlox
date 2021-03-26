
use std::{collections::HashMap};

use crate::lox::{LoxError, LoxErrorType};
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
    fn interpret(self, environment: &mut Environment)
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
            Statement::Function(name, params, body) => format!(
                "(define ({} {}) ({}))",
                name.lexeme,
                params
                    .iter()
                    .map(|p| p.lexeme.to_owned())
                    .collect::<Vec<String>>()
                    .join(" "),
                body.iter()
                    .map(|s| s.clone().to_string())
                    .collect::<Vec<String>>()
                    .join(" "),
            ),
            Statement::None => "()".to_owned(),
        }
    }
}

impl Interpreter for Expression {
    fn interpret(
        self,
        environment: &mut Environment,
    ) -> Result<LoxObject, LoxError> {
        match self.clone() {
            Expression::Grouping(expr) => expr.interpret(environment),
            Expression::Literal(obj) => Ok(obj),
            Expression::Unary(op, value) => {
                let obj = value.clone().interpret(environment)?;
                match op.token_type {
                    TokenType::Minus => {
                        if let LoxObject::Number(n) = obj {
                            Ok(LoxObject::Number(-n))
                        } else {
                            Err(crate::lox::runtime_error(
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
                    _ => Err(crate::lox::runtime_error(
                        self,
                        LoxErrorType::UnknownOperator,
                        &format!("'{:?}'", op.token_type),
                    )),
                }
            }
            Expression::Binary(left, op, right) => {
                let robj = right.clone().interpret(environment)?;
                let lobj = left.clone().interpret(environment)?;

                match op.token_type {
                    TokenType::Minus => match (lobj, robj) {
                        (LoxObject::Number(l), LoxObject::Number(r)) => {
                            Ok(LoxObject::Number(l - r))
                        }
                        _ => Err(crate::lox::runtime_error(
                            self,
                            LoxErrorType::TypeError,
                            "cannot subtract non-numbers",
                        )),
                    },
                    TokenType::Slash => match (lobj, robj) {
                        (LoxObject::Number(l), LoxObject::Number(r)) => {
                            if r == 0.0 {
                                Err(crate::lox::runtime_error(
                                    self,
                                    LoxErrorType::DivideByZeroError,
                                    "divide by zero",
                                ))
                            } else {
                                Ok(LoxObject::Number(l / r))
                            }
                        }
                        _ => Err(crate::lox::runtime_error(
                            self,
                            LoxErrorType::TypeError,
                            "cannot divide non-numbers",
                        )),
                    },
                    TokenType::Star => match (lobj, robj) {
                        (LoxObject::Number(l), LoxObject::Number(r)) => {
                            Ok(LoxObject::Number(l * r))
                        }
                        _ => Err(crate::lox::runtime_error(
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
                        _ => Err(crate::lox::runtime_error(
                            self,
                            LoxErrorType::TypeError,
                            "addition is defined for numbers and strings",
                        )),
                    },
                    TokenType::Greater
                    | TokenType::GreaterEqual
                    | TokenType::Less
                    | TokenType::LessEqual => self.apply_compare(op.token_type, lobj, robj),
                    TokenType::EqualEqual => Ok(LoxObject::Boolean(lobj == robj)),
                    TokenType::BangEqual => Ok(LoxObject::Boolean(lobj != robj)),
                    _ => panic!("unimplemented binary operator"),
                }
            }
            Expression::Variable(token) => Ok(environment.get(self, token)?.clone()),
            Expression::Assignment(name, value) => {
                // TODO: This clone could be super expensive, if the whole program is one assignment
                crate::lox::trace(format!(
                    ">>> Modifying environment={}",
                    environment.to_string()
                ));
                let result = value.clone().interpret(environment)?;
                environment.assign(*value, name, result.clone())?;
                crate::lox::trace(format!(
                    ">>> Done modifying environment={}",
                    environment.to_string()
                ));

                Ok(result)
            }
            Expression::Logical(l, op, r) => {
                let left = l.interpret(environment)?;

                if op.token_type == TokenType::Or && Self::is_truthy(left.clone()) {
                    Ok(left)
                } else if op.token_type == TokenType::And && !Self::is_truthy(left.clone()) {
                    Ok(left)
                } else {
                    r.interpret(environment)
                }
            }
            Expression::Call(callee, _paren, args) => {
                crate::lox::trace(format!(
                    ">>> Calling function with environment={}",
                    environment.to_string()
                ));
                let callee_obj = callee.clone().interpret(environment)?;

                let mut arguments = Vec::new();
                for arg in args {
                    arguments.push(arg.interpret(environment)?);
                }

                let mut func: LoxCallable = LoxCallable::try_from(callee_obj)?;
                if func.arity() as usize != arguments.len() {
                    Err(crate::lox::runtime_error(
                        *callee,
                        LoxErrorType::FunctionCallError,
                        &format!(
                            "expected {} arguments but got {}.",
                            func.arity(),
                            arguments.len()
                        ),
                    ))
                } else {
                    func.call_lox_func(arguments, environment)
                }
            }
        }
    }
}

impl Interpreter for Statement {
    fn interpret(
        self,
        environment: &mut Environment,
    ) -> Result<LoxObject, LoxError> {
        crate::lox::trace(format!(
            ">>> Interpreting at statement={} env={}",
            self.to_string(),
            environment.to_string()
        ));
        match self {
            Statement::Print(expr) => {
                let obj = expr.interpret(environment)?;
                println!("{}", obj.to_string());
                Ok(obj)
            }
            Statement::Expression(expr) => expr.interpret(environment),
            Statement::Var(token, expr) => {
                let value = match expr {
                    Some(expr) => expr.interpret(environment),
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
                    last = statement.interpret(&mut block)?;
                }

                *environment = *block.enclosing.unwrap();
                Ok(last)
            }
            Statement::If(cond, then_st, else_st) => {
                if Expression::is_truthy(cond.interpret(environment)?) {
                    then_st.interpret(environment)
                } else {
                    match else_st {
                        Some(st) => st.interpret(environment),
                        None => Ok(LoxObject::Nil),
                    }
                }
            }
            Statement::While(cond, do_st) => {
                // TODO: This is expensive, maybe don't consume on interpret?
                while Expression::is_truthy(cond.clone().interpret(environment)?) {
                    do_st.clone().interpret(environment)?;
                }

                Ok(LoxObject::Nil)
            }
            Statement::Function(name, params, body) => {
                let params = params.iter().map(|param| param.lexeme.to_owned()).collect();
                // TODO: when creating closures will have to do some unsafe wizardry
                // in order for function environments to point back to the functions
                let func =
                    LoxObject::Function(LoxCallable::interpreted(name.lexeme.clone(), params, body));
                environment.define(name.lexeme, func);
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

    pub fn define(&mut self, name: String, value: LoxObject) {
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

    fn _define_global(&mut self, name: String, value: LoxObject) {
        match &mut self.enclosing {
            Some(env) => env._define_global(name, value),
            None => {
                self.values.insert(name, value);
            }
        }
    }

    fn get(
        &self,
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
                .get(expression, name)?
                .clone())
        } else {
            Err(crate::lox::runtime_error(
                expression,
                LoxErrorType::AssignmentError,
                &format!("undefined variable {}", name.lexeme),
            ))
        }
    }

    fn assign(
        &mut self,
        expression: Expression,
        name: Token,
        value: LoxObject,
    ) -> Result<(), LoxError> {
        if self.values.contains_key(&name.lexeme) {
            self.values.insert(name.lexeme, value);
            Ok(())
        } else if let Some(environ) = &mut self.enclosing {
            environ.assign(expression, name, value)?;
            Ok(())
        } else {
            Err(crate::lox::runtime_error(
                expression,
                LoxErrorType::AssignmentError,
                &format!("undefined variable {}", name.lexeme),
            ))
        }
    }

    fn global(&self) -> &Environment {
        match &self.enclosing {
            None => self,
            Some(env) => env.global(),
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

/*
 * For now, I'm using dynamic scope because it's possible to implement it and
 * I have no way to extend a scope with two parents. The lox implementation of
 * the book extends the global variables with a new scope containing only the
 * funciton arguments, but I'm not sure how the function names for recursive
 * definitions work in that case?? Whatever... I'm not worried about it. I can
 * come back to it later.
 */
#[derive(Clone)]
pub struct LoxCallable {
    arity: u8,
    // TODO: Add environment to make true closures
    // env: Environment,
    exec: Executable,
    name: String,
}

impl std::fmt::Debug for LoxCallable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

// TODO: we could theoretically give each function some ID to track,
// and compare equal if the ids are equal even though the two would be clones
impl PartialEq for LoxCallable {
    fn eq(&self, _other: &Self) -> bool {
        false
    }
}

#[derive(Clone)]
enum Executable {
    Interpreted(Vec<Statement>, Vec<String>),
    Native(fn(Vec<LoxObject>) -> Result<LoxObject, LoxError>),
}

impl LoxCallable {
    pub fn native(
        name: String,
        arity: u8,
        f: fn(Vec<LoxObject>) -> Result<LoxObject, LoxError>,
    ) -> LoxCallable {
        LoxCallable {
            arity,
            name,
            exec: Executable::Native(f),
        }
    }

    pub fn to_string(&self) -> String {
        format!("<fn {}(arity={})>", self.name, self.arity)
    }

    pub fn interpreted(name: String, params: Vec<String>, body: Vec<Statement>) -> LoxCallable {
        LoxCallable {
            name,
            arity: params.len() as u8,
            exec: Executable::Interpreted(body, params),
        }
    }

    fn try_from(object: LoxObject) -> Result<LoxCallable, LoxError> {
        fn err(object: LoxObject) -> Result<LoxCallable, LoxError> {
            Err(crate::lox::runtime_error(
                Expression::Literal(object),
                LoxErrorType::FunctionCallError,
                &format!(""),
            ))
        };
        match &object {
            // TODO: This is a total guess but I have a feeling we're heading somewhere like this
            LoxObject::Function(f) => Ok(f.clone()),
            LoxObject::Object(vals) => match vals.get("__call") {
                Some(obj) => Self::try_from(*(obj.clone())),
                None => err(object),
            },
            _ => err(object),
        }
    }

    fn arity(&self) -> u8 {
        self.arity
    }

    fn call_lox_func(
        &mut self,
        args: Vec<LoxObject>,
        env: &mut Environment,
    ) -> Result<LoxObject, LoxError> {
        match &self.exec {
            Executable::Interpreted(body, names) => {
                let caller = std::mem::replace(env, Environment::new());
                let mut wrapper = Environment::extend(caller.global().clone());

                names.iter().enumerate().for_each(|(i, x)| {
                    // Here we guard against calling with different length args and
                    // expected args (names). We throw an error in the interpreter if
                    // we reach this state, but still would like to ensure nobody can
                    // abuse this method to cause a panic
                    let name = x.to_owned();
                    let value = match args.get(i) {
                        Some(val) => val.clone(),
                        None => LoxObject::Nil,
                    };
                    wrapper.define(name, value);
                });

                let mut result = LoxObject::Nil;
                for statement in body {
                    result = statement.clone().interpret(&mut wrapper)?;
                }

                *env = caller;

                Ok(result)
            }
            Executable::Native(f) => f(args),
        }
    }
}
