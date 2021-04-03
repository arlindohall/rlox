use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::{lox::{LoxError, LoxErrorType}, parser::ExpressionId};
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
pub struct Interpreter {
    pub environment: SharedEnvironment,
    locals: Locals,
    globals: SharedEnvironment,
}

type Locals = HashMap<ExpressionId, u16>;

fn take_parent(env: &SharedEnvironment) -> SharedEnvironment {
    env.clone().borrow().enclosing.clone().unwrap()
}

impl AstPrinter for Expression {
    fn to_string(&self) -> String {
        match self {
            Expression::Assignment(_, n, v) => format!("(assign {} {})", n.lexeme, v.to_string()),
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
            Expression::Variable(_, t) => format!("{}", t.lexeme),
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
            Statement::Return(_keyword, value) => format!("(return {})", value.to_string()),
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

impl Interpreter {
    pub fn with_env(environment: SharedEnvironment) -> Interpreter {
        Interpreter {
            globals: environment.clone(),
            environment,
            locals: HashMap::new(),
        }
    }

    pub fn resolve(&mut self, expression: Expression, i: u16) {
        crate::lox::trace(format!(">>> Resolving level={}, expr={:?}", i, expression));
        self.locals.insert(expression.get_id(), i);
    }

    fn lookup_variable(&self, name: Token, expression: Expression) -> Result<LoxObject, LoxError> {
        let distance = self.locals.get(&expression.get_id());
        crate::lox::trace(format!(
            ">>> Looking for variable name={}, dist={:?}, env={}",
            name.lexeme,
            &distance,
            self.environment.borrow().to_string(),
        ));
        match distance {
            Some(dist) => self.get_at(*dist, name),
            None => Ok(self.globals.borrow().values.get(&name.lexeme).unwrap().clone()),
        }
    }

    fn get_at(&self, distance: u16, name: Token) -> Result<LoxObject, LoxError> {
        crate::lox::trace(format!(
            ">>> Getting name={}, distance={}, env={:?}",
            name.lexeme,
            &distance,
            self.environment,
        ));
        let value = self.ancestor(distance)
            .borrow()
            .values
            .get(&name.lexeme)
            .unwrap()
            .clone();
        Ok(value)
    }

    fn assign_at(&self, distance: u16, name: Token, value: LoxObject) -> Result<(), LoxError> {
        crate::lox::trace(format!(
            ">>> Assigning name={}, distance={}, value={:?}, env={}",
            name.lexeme,
            &distance,
            value,
            self.environment.borrow().to_string(),
        ));
        Ok(self.ancestor(distance).borrow_mut().define(name.lexeme, value))
    }

    fn ancestor(&self, distance: u16) -> SharedEnvironment {
        let mut distance = distance.clone();
        let mut env = self.environment.clone();
        crate::lox::trace(format!(
            ">>> Getting ancestor at distance={}, env={:?}",
            distance,
            env,
        ));
        while distance > 1 {
            crate::lox::trace(format!("  ... pulling from environment {}", distance));
            env = take_parent(&env);
            distance -= 1;
        }
        env
    }

    fn interpret_expression(&mut self, expression: Expression) -> Result<LoxObject, LoxError> {
        match expression.clone() {
            Expression::Grouping(expr) => self.interpret_expression(*expr),
            Expression::Literal(obj) => Ok(obj.clone()),
            Expression::Unary(op, value) => {
                let obj = self.interpret_expression(*value.clone())?;
                match op.token_type {
                    TokenType::Minus => {
                        if let LoxObject::Number(n) = obj {
                            Ok(LoxObject::Number(-n))
                        } else {
                            Err(crate::lox::runtime_error(
                                *value,
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
                        if Expression::is_truthy(obj) {
                            Ok(LoxObject::Boolean(false))
                        } else {
                            Ok(LoxObject::Boolean(true))
                        }
                    }
                    _ => Err(crate::lox::runtime_error(
                        expression,
                        LoxErrorType::UnknownOperator,
                        &format!("'{:?}'", op.token_type),
                    )),
                }
            }
            Expression::Binary(left, op, right) => {
                let robj = self.interpret_expression(*right)?;
                let lobj = self.interpret_expression(*left)?;

                match op.token_type {
                    TokenType::Minus => match (lobj, robj) {
                        (LoxObject::Number(l), LoxObject::Number(r)) => {
                            Ok(LoxObject::Number(l - r))
                        }
                        _ => Err(crate::lox::runtime_error(
                            expression.clone(),
                            LoxErrorType::TypeError,
                            "cannot subtract non-numbers",
                        )),
                    },
                    TokenType::Slash => match (lobj, robj) {
                        (LoxObject::Number(l), LoxObject::Number(r)) => {
                            if r == 0.0 {
                                Err(crate::lox::runtime_error(
                                    expression.clone(),
                                    LoxErrorType::DivideByZeroError,
                                    "divide by zero",
                                ))
                            } else {
                                Ok(LoxObject::Number(l / r))
                            }
                        }
                        _ => Err(crate::lox::runtime_error(
                            expression.clone(),
                            LoxErrorType::TypeError,
                            "cannot divide non-numbers",
                        )),
                    },
                    TokenType::Star => match (lobj, robj) {
                        (LoxObject::Number(l), LoxObject::Number(r)) => {
                            Ok(LoxObject::Number(l * r))
                        }
                        _ => Err(crate::lox::runtime_error(
                            expression.clone(),
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
                            expression.clone(),
                            LoxErrorType::TypeError,
                            "addition is defined for numbers and strings",
                        )),
                    },
                    TokenType::Greater
                    | TokenType::GreaterEqual
                    | TokenType::Less
                    | TokenType::LessEqual => expression.apply_compare(op.token_type, lobj, robj),
                    TokenType::EqualEqual => Ok(LoxObject::Boolean(lobj == robj)),
                    TokenType::BangEqual => Ok(LoxObject::Boolean(lobj != robj)),
                    _ => panic!("unimplemented binary operator"),
                }
            }
            Expression::Variable(_, token) => self.lookup_variable(token, expression),
            Expression::Assignment(_, name, value) => {
                // TODO: This clone could be super expensive, if the whole program is one assignment
                crate::lox::trace(format!(
                    ">>> Modifying environment={}",
                    self.environment.borrow().to_string(),
                ));
                let value = self.interpret_expression(*value.clone())?;
                let distance = self.locals.get(&expression.get_id());
                match distance {
                    Some(dist) => self.assign_at(*dist, name, value.clone()),
                    None => Ok(self.globals.borrow_mut().define(name.lexeme, value.clone())),
                }?;
                crate::lox::trace(format!(
                    ">>> Done modifying environment={}",
                    self.environment.borrow().to_string()
                ));

                Ok(value)
            }
            Expression::Logical(l, op, r) => {
                let left = self.interpret_expression(*l)?;

                if op.token_type == TokenType::Or && Expression::is_truthy(left.clone()) {
                    Ok(left)
                } else if op.token_type == TokenType::And && !Expression::is_truthy(left.clone()) {
                    Ok(left)
                } else {
                    self.interpret_expression(*r)
                }
            }
            Expression::Call(callee, _paren, args) => {
                crate::lox::trace(format!(
                    ">>> Calling function with environment={}",
                    self.environment.borrow().to_string()
                ));
                let callee_obj = self.interpret_expression(*callee.clone())?;

                let mut arguments = Vec::new();
                for arg in args {
                    arguments.push(self.interpret_expression(arg)?);
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
                    func.call(self, arguments)
                }
            }
        }
    }

    pub fn interpret_statement(&mut self, statement: Statement) -> Result<LoxObject, LoxError> {
        crate::lox::trace(format!(
            ">>> Interpreting at statement={} env={}",
            statement.to_string(),
            self.environment.borrow().to_string()
        ));
        match statement.clone() {
            Statement::Print(expr) => {
                let obj = self.interpret_expression(expr)?;
                println!("{}", obj.to_string());
                Ok(obj)
            }
            Statement::Expression(expr) => self.interpret_expression(expr),
            Statement::Var(token, expr) => {
                let value = match expr {
                    Some(expr) => self.interpret_expression(expr),
                    None => Ok(LoxObject::Nil),
                }?;
                crate::lox::trace(format!(
                    ">>> Defining new variable={} value={}",
                    token.lexeme,
                    value.to_string()
                ));
                self.environment
                    .borrow_mut()
                    .define(token.lexeme, value.clone());
                crate::lox::trace(format!(
                    ">>> After definition env={}",
                    self.environment.borrow().to_string()
                ));
                Ok(value)
            }
            Statement::Block(statements) => {
                self.environment = Environment::extend(self.environment.clone());

                let mut last = LoxObject::Nil;
                for statement in statements {
                    last = self.interpret_statement(statement)?;
                }

                self.environment = take_parent(&self.environment);
                Ok(last)
            }
            Statement::If(cond, then_st, else_st) => {
                if Expression::is_truthy(self.interpret_expression(cond)?) {
                    self.interpret_statement(*then_st)
                } else {
                    match else_st {
                        Some(st) => self.interpret_statement(*st),
                        None => Ok(LoxObject::Nil),
                    }
                }
            }
            Statement::While(cond, do_st) => {
                // TODO: This is expensive, maybe don't consume on interpret?
                while Expression::is_truthy(self.interpret_expression(cond.clone())?) {
                    self.interpret_statement(*do_st.clone())?;
                }

                Ok(LoxObject::Nil)
            }
            Statement::Return(_keyword, expression) => {
                let value = self.interpret_expression(expression)?;
                Err(LoxError::ReturnPseudoError { value })
            }
            Statement::Function(name, params, body) => {
                let params = params.iter().map(|param| param.lexeme.to_owned()).collect();
                // TODO: when creating closures will have to do some unsafe wizardry
                // in order for function environments to point back to the functions
                let func = LoxObject::Function(LoxCallable::interpreted(
                    name.lexeme.clone(),
                    params,
                    body,
                    self.environment.clone(),
                ));
                self.environment.borrow_mut().define(name.lexeme, func);
                Ok(LoxObject::Nil)
            }
            Statement::None => Ok(LoxObject::Nil),
        }
    }
}

type SharedEnvironment = Rc<RefCell<Environment>>;

#[derive(Debug, Clone, PartialEq)]
pub struct Environment {
    values: HashMap<String, LoxObject>,
    enclosing: Option<SharedEnvironment>,
}

impl Environment {
    pub fn new() -> SharedEnvironment {
        Rc::new(RefCell::new(Environment {
            values: HashMap::new(),
            enclosing: None,
        }))
    }

    pub fn extend(environment: SharedEnvironment) -> SharedEnvironment {
        Rc::new(RefCell::new(Environment {
            values: HashMap::new(),
            enclosing: Some(environment),
        }))
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
            Some(enc) => format!("(({}) (enclosing {}))", values, enc.borrow().to_string()),
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
    closure: SharedEnvironment,
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
        global: SharedEnvironment,
        f: fn(Vec<LoxObject>) -> Result<LoxObject, LoxError>,
    ) -> LoxCallable {
        LoxCallable {
            arity,
            name,
            closure: global,
            exec: Executable::Native(f),
        }
    }

    pub fn to_string(&self) -> String {
        format!("<fn {}(arity={})>", self.name, self.arity)
    }

    pub fn interpreted(
        name: String,
        params: Vec<String>,
        body: Vec<Statement>,
        closure: SharedEnvironment,
    ) -> LoxCallable {
        LoxCallable {
            name,
            arity: params.len() as u8,
            closure,
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

    fn call(
        &mut self,
        interpreter: &mut Interpreter,
        args: Vec<LoxObject>,
    ) -> Result<LoxObject, LoxError> {
        match self.exec.clone() {
            Executable::Interpreted(body, names) => {
                let old = interpreter.environment.clone();
                interpreter.environment = Environment::extend(self.closure.clone());

                for (i, x) in names.iter().enumerate() {
                    // Here we guard against calling with different length args and
                    // expected args (names). We throw an error in the interpreter if
                    // we reach this state, but still would like to ensure nobody can
                    // abuse this method to cause a panic
                    let name = x.to_owned();
                    let value = match args.get(i) {
                        Some(val) => val.clone(),
                        None => LoxObject::Nil,
                    };
                    interpreter.environment.borrow_mut().define(name, value);
                }

                let mut result = Ok(LoxObject::Nil);
                for statement in body {
                    result = match interpreter.interpret_statement(statement) {
                        Ok(obj) => Ok(obj),
                        Err(LoxError::ReturnPseudoError { value }) => {
                            interpreter.environment = old;
                            return Ok(value.clone());
                        }
                        Err(_) => {
                            interpreter.environment = old;
                            return result;
                        }
                    }
                }

                interpreter.environment = old;
                result
            }
            Executable::Native(f) => f(args),
        }
    }
}
