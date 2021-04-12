use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::{
    builtins,
    lox::{LoxError, LoxErrorType, LoxNumber},
    parser::{
        ClassDefinition, Expression, ExpressionId, FunctionDefinition, LoxLiteral, Statement,
    },
    scanner::{Token, TokenType},
};

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

pub struct Interpreter {
    pub environment: SharedEnvironment,
    locals: Locals,
    globals: SharedEnvironment,
}

type Locals = HashMap<ExpressionId, u16>;
pub type SharedEnvironment = Rc<RefCell<Environment>>;
pub type ObjectRef = Rc<RefCell<Object>>;
pub type FunctionRef = Rc<RefCell<LoxFunction>>;

// TODO maybe don't have values exposed, just have a getter, no setter??
#[derive(Debug, Clone, PartialEq)]
pub struct Environment {
    pub values: HashMap<String, ObjectRef>,
    enclosing: Option<SharedEnvironment>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Object {
    // This exists solely to keep the `value` field private
    value: ObjectType,
}

// Maybe revisit this, but it's only public so builtins can implement it
#[derive(Debug, Clone, PartialEq)]
pub struct LoxClass {
    name: String,
    methods: HashMap<String, FunctionRef>,
    superclass: Option<ObjectRef>,
}

#[derive(Debug, Clone, PartialEq)]
enum ObjectType {
    Primitive(PrimitiveObject),
    Instance(Instance),
}

#[derive(Debug, Clone, PartialEq)]
struct Instance {
    class: LoxClass,
    fields: HashMap<String, ObjectRef>,
}

#[derive(Debug, Clone, PartialEq)]
enum PrimitiveObject {
    Boolean(bool),
    Number(LoxNumber),
    String(String),
    Function(FunctionRef),
    Class(LoxClass),
    Nil,
}

#[derive(Clone)]
pub struct LoxFunction {
    arity: u8,
    closure: SharedEnvironment,
    exec: Executable,
    is_initializer: bool,
    name: String,
}

#[derive(Clone)]
enum Executable {
    Constructor(LoxClass),
    Interpreted(Vec<Statement>, Vec<String>),
    Native(fn(Vec<ObjectRef>, SharedEnvironment, Expression) -> Result<ObjectRef, LoxError>),
}

pub trait AstPrinter {
    fn to_string_indent(&self, indent: u8) -> String;

    fn to_string(&self) -> String {
        self.to_string_indent(0)
    }
}

pub trait Bindable {
    fn bind(&mut self, obj: ObjectRef) -> LoxFunction;
}

fn take_parent(env: &SharedEnvironment) -> SharedEnvironment {
    env.clone().borrow().enclosing.clone().unwrap()
}

impl AstPrinter for Expression {
    fn to_string_indent(&self, _indent: u8) -> String {
        match self {
            Expression::Assignment { name, value, .. } => {
                format!("{} = {}", name.lexeme, value.to_string())
            }
            Expression::Logical { left, op, right } | Expression::Binary { left, op, right } => {
                format!("{} {} {}", left.to_string(), op.lexeme, right.to_string())
            }
            Expression::Grouping { expression } => format!("({})", expression.to_string()),
            Expression::Literal { value } => value.to_string(),
            Expression::Unary { op, value } => format!("{}{}", op.lexeme, value.to_string()),
            Expression::Call { callee, args, .. } => {
                let args: Vec<String> = args.iter().map(|arg| arg.to_string()).collect();
                format!("{}({})", callee.to_string(), args.join(" "))
            }
            Expression::This { .. } => "this".to_string(),
            Expression::Set {
                object,
                name,
                value,
            } => format!(
                "{}.{} = {}",
                object.to_string(),
                name.lexeme,
                value.to_string()
            ),
            Expression::Get { object, name } => format!("{}.{}", object.to_string(), name.lexeme),
            Expression::Variable { name, .. } => format!("{}", name.lexeme),
        }
    }
}

impl AstPrinter for Statement {
    fn to_string_indent(&self, indent: u8) -> String {
        let prefix_whitespace: Vec<String> = std::iter::repeat("    ".to_string())
            .take(indent.into())
            .collect();
        let prefix_whitespace = prefix_whitespace.join("");
        match self {
            Statement::Block { statements } => {
                let printed: Vec<String> = statements
                    .iter()
                    .map(|s| s.to_string_indent(indent + 1))
                    .collect();
                format!(
                    "{}{{\n{}\n{}}}",
                    prefix_whitespace,
                    printed.join("\n"),
                    prefix_whitespace
                )
            }
            Statement::Print { expression } => {
                format!("{}print {};", prefix_whitespace, expression.to_string())
            }
            Statement::Expression { expression } => {
                format!("{}{};", prefix_whitespace, expression.to_string())
            }
            Statement::Var {
                name,
                initializer: Some(value),
            } => format!(
                "{}var {} = {};",
                prefix_whitespace,
                name.lexeme,
                value.to_string()
            ),
            Statement::Var {
                name,
                initializer: None,
            } => format!("{}var {};", prefix_whitespace, name.lexeme),
            Statement::If {
                condition,
                then_statement,
                else_statement: Some(else_st),
            } => format!(
                "{}if ({}) \n{}\n{}\n",
                prefix_whitespace,
                condition.to_string(),
                then_statement.to_string_indent(indent + 1),
                else_st.to_string_indent(indent + 1)
            ),
            Statement::If {
                condition,
                then_statement,
                else_statement: None,
            } => format!(
                "{}if ({}) \n{}\n",
                prefix_whitespace,
                condition.to_string(),
                then_statement.to_string_indent(indent + 1),
            ),
            Statement::While { condition, body } => format!(
                "{}while ({}) \n{}\n",
                prefix_whitespace,
                condition.to_string(),
                body.to_string_indent(indent + 1)
            ),
            Statement::Return { value, .. } => format!("return {};\n", value.to_string()),
            Statement::Function { definition } => format!(
                // "{}fun {}({}) \n{}",
                "{}fun {}({}) {{\n{}\n{}}}",
                prefix_whitespace,
                definition.name.lexeme,
                definition
                    .params
                    .iter()
                    .map(|p| p.lexeme.to_owned())
                    .collect::<Vec<String>>()
                    .join(", "),
                definition
                    .body
                    .clone()
                    .iter()
                    .map(|statement| statement.to_string_indent(indent + 1))
                    .collect::<Vec<String>>()
                    .join("\n"),
                prefix_whitespace,
            ),
            Statement::None => "\n".to_owned(),
            Statement::Class {
                definition: ClassDefinition { name, methods, .. },
            } => format!(
                "{}class {} {{\n{}\n{}}}",
                prefix_whitespace,
                name.lexeme,
                methods
                    .iter()
                    .map(|f| Statement::Function {
                        definition: f.clone()
                    }
                    .to_string_indent(indent + 1))
                    .collect::<Vec<String>>()
                    .join("\n"),
                prefix_whitespace,
            ),
        }
    }
}

impl LoxClass {
    pub fn find_method(&self, name: &str) -> Option<FunctionRef> {
        self.methods.get(name).map(|m| m.clone())
    }

    pub fn new(name: String, methods: HashMap<String, FunctionRef>) -> LoxClass {
        LoxClass { name, methods, superclass: None }
    }
}

impl PrimitiveObject {
    fn get_class(&self) -> LoxClass {
        match self {
            PrimitiveObject::Boolean(_) => builtins::boolean(),
            PrimitiveObject::Number(_) => builtins::number(),
            PrimitiveObject::String(_) => builtins::string(),
            PrimitiveObject::Function(_) => builtins::function(),
            PrimitiveObject::Class(_) => builtins::meta_class(),
            PrimitiveObject::Nil => builtins::nil(),
        }
    }
}

impl std::convert::From<LoxLiteral> for PrimitiveObject {
    fn from(literal: LoxLiteral) -> Self {
        match literal {
            LoxLiteral::Boolean(b) => PrimitiveObject::Boolean(b),
            LoxLiteral::String(s) => PrimitiveObject::String(s),
            LoxLiteral::Number(n) => PrimitiveObject::Number(n),
            LoxLiteral::Nil => PrimitiveObject::Nil,
        }
    }
}

impl std::convert::From<LoxLiteral> for Object {
    fn from(literal: LoxLiteral) -> Self {
        Object {
            value: ObjectType::Primitive(PrimitiveObject::from(literal)),
        }
    }
}

impl Object {
    pub fn wrap(self) -> ObjectRef {
        Rc::new(RefCell::new(self))
    }

    pub fn to_string(&self) -> String {
        self.value.to_string()
    }

    pub fn nil() -> ObjectRef {
        Object {
            value: ObjectType::Primitive(PrimitiveObject::Nil),
        }
        .wrap()
    }

    pub fn number(f: LoxNumber) -> ObjectRef {
        Object {
            value: ObjectType::Primitive(PrimitiveObject::Number(f)),
        }
        .wrap()
    }

    pub fn boolean(b: bool) -> ObjectRef {
        Object {
            value: ObjectType::Primitive(PrimitiveObject::Boolean(b)),
        }
        .wrap()
    }

    pub fn string(s: String) -> ObjectRef {
        Object {
            value: ObjectType::Primitive(PrimitiveObject::String(s)),
        }
        .wrap()
    }

    pub fn function(f: FunctionRef) -> ObjectRef {
        Object {
            value: ObjectType::Primitive(PrimitiveObject::Function(f)),
        }
        .wrap()
    }

    // Classes and instances are private to the interpreter
    fn class(c: LoxClass) -> ObjectRef {
        Object {
            value: ObjectType::Primitive(PrimitiveObject::Class(c)),
        }
        .wrap()
    }

    fn instance(i: Instance) -> ObjectRef {
        Object {
            value: ObjectType::Instance(i),
        }
        .wrap()
    }
}

impl ObjectType {
    pub fn is_instance(&self) -> bool {
        match self {
            Self::Instance(_) => true,
            _ => false,
        }
    }

    pub fn is_nil(&self) -> bool {
        match self {
            Self::Primitive(PrimitiveObject::Nil) => true,
            _ => false,
        }
    }

    fn is_truthy(&self) -> bool {
        match self {
            Self::Primitive(PrimitiveObject::Nil) => false,
            Self::Primitive(PrimitiveObject::Boolean(b)) => b.clone(),
            _ => true,
        }
    }

    pub fn to_string(&self) -> String {
        match self {
            Self::Primitive(primitive) => match primitive {
                PrimitiveObject::Boolean(b) => format!("{}", b),
                PrimitiveObject::String(s) => s.clone(),
                PrimitiveObject::Number(n) => format!("{}", n),
                PrimitiveObject::Function(callable) => callable.borrow().to_string(),
                PrimitiveObject::Class(class) => class.name.clone(),
                PrimitiveObject::Nil => String::from("nil"),
            },
            // TODO: maybe actually print objects
            Self::Instance(object) => format!("<{}>", object.class.name),
        }
    }

    pub fn get_type(&self) -> String {
        match self {
            Self::Primitive(primitive) => primitive.get_class().name,
            Self::Instance(Instance { class, .. }) => class.name.to_string(),
        }
    }

    pub fn set(&mut self, name: String, value: ObjectRef) {
        match self {
            Self::Instance(Instance { fields, .. }) => {
                fields.insert(name, value);
            }
            _ => panic!(format!("cannot set property on {}", self.get_type())),
        }
    }

    pub fn get(
        &self,
        this: ObjectRef,
        expression: Expression,
        name: &str,
    ) -> Result<ObjectRef, LoxError> {
        if let Self::Instance(Instance { class, fields }) = self {
            if let Some(field) = fields.get(name) {
                return Ok(field.clone());
            } else if let Some(method) = class.find_method(name) {
                return Ok(Object::function(method.clone().borrow_mut().bind(this)));
            }
        } else if let Self::Primitive(primitive) = self {
            let class = primitive.get_class();
            if let Some(method) = class.find_method(name) {
                return Ok(Object::function(method.clone().borrow_mut().bind(this)));
            }
        }
        Err(crate::lox::runtime_error(
            expression,
            LoxErrorType::PropertyError,
            &format!("undefined property {}", name),
        ))
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

    fn lookup_variable(&self, name: Token, expression: Expression) -> Result<ObjectRef, LoxError> {
        let distance = self.locals.get(&expression.get_id());
        crate::lox::trace(format!(
            ">>> Looking for variable name={}, dist={:?}, env={}",
            name.lexeme,
            &distance,
            self.environment.borrow().to_string(),
        ));
        match distance {
            Some(dist) => self.get_at(*dist, name),
            None => Ok(self
                .globals
                .borrow()
                .values
                .get(&name.lexeme)
                .unwrap()
                .clone()),
        }
    }

    fn get_at(&self, distance: u16, name: Token) -> Result<ObjectRef, LoxError> {
        crate::lox::trace(format!(
            ">>> Getting name={}, distance={}, env={:?}",
            name.lexeme, &distance, self.environment,
        ));
        let value = self
            .ancestor(distance)
            .borrow()
            .values
            .get(&name.lexeme)
            .unwrap()
            .clone();
        Ok(value)
    }

    fn assign_at(&self, distance: u16, name: Token, value: ObjectRef) -> Result<(), LoxError> {
        crate::lox::trace(format!(
            ">>> Assigning name={}, distance={}, value={:?}, env={}",
            name.lexeme,
            &distance,
            value,
            self.environment.borrow().to_string(),
        ));
        Ok(self
            .ancestor(distance)
            .borrow_mut()
            .define(name.lexeme, value))
    }

    fn ancestor(&self, distance: u16) -> SharedEnvironment {
        let mut distance = distance.clone();
        let mut env = self.environment.clone();
        crate::lox::trace(format!(
            ">>> Getting ancestor at distance={}, env={:?}",
            distance, env,
        ));
        while distance > 1 {
            crate::lox::trace(format!("  ... pulling from environment {}", distance));
            env = take_parent(&env);
            distance -= 1;
        }
        env
    }

    fn interpret_expression(&mut self, expression: Expression) -> Result<ObjectRef, LoxError> {
        match expression.clone() {
            Expression::Grouping { expression } => self.interpret_expression(*expression),
            Expression::Literal { value } => Ok(Object::from(value.clone()).wrap()),
            Expression::Unary { op, value } => {
                let obj = self.interpret_expression(*value.clone())?;
                match op.token_type {
                    TokenType::Minus => {
                        if let ObjectType::Primitive(PrimitiveObject::Number(n)) =
                            obj.borrow().value
                        {
                            Ok(Object::number(-n))
                        } else {
                            Err(crate::lox::runtime_error(
                                *value,
                                LoxErrorType::TypeError,
                                &format!(
                                    "cannot negate `{}` — expected Number, found {}",
                                    obj.borrow().value.to_string(),
                                    obj.borrow().value.get_type()
                                ),
                            ))
                        }
                    }
                    TokenType::Bang => {
                        if obj.borrow_mut().value.is_truthy() {
                            Ok(Object::boolean(false))
                        } else {
                            Ok(Object::boolean(true))
                        }
                    }
                    _ => Err(crate::lox::runtime_error(
                        expression,
                        LoxErrorType::UnknownOperator,
                        &format!("'{:?}'", op.token_type),
                    )),
                }
            }
            Expression::Binary { left, op, right } => {
                let right = self.interpret_expression(*right)?;
                let left = self.interpret_expression(*left)?;

                match op.token_type {
                    TokenType::Minus => match (&left.borrow().value, &right.borrow().value) {
                        (
                            ObjectType::Primitive(PrimitiveObject::Number(l)),
                            ObjectType::Primitive(PrimitiveObject::Number(r)),
                        ) => Ok(Object::number(l - r)),
                        _ => Err(crate::lox::runtime_error(
                            expression.clone(),
                            LoxErrorType::TypeError,
                            "cannot subtract non-numbers",
                        )),
                    },
                    TokenType::Slash => match (&left.borrow().value, &right.borrow().value) {
                        (
                            ObjectType::Primitive(PrimitiveObject::Number(l)),
                            ObjectType::Primitive(PrimitiveObject::Number(r)),
                        ) => {
                            if *r == 0.0 {
                                Err(crate::lox::runtime_error(
                                    expression.clone(),
                                    LoxErrorType::DivideByZeroError,
                                    "divide by zero",
                                ))
                            } else {
                                Ok(Object::number(l / r))
                            }
                        }
                        _ => Err(crate::lox::runtime_error(
                            expression.clone(),
                            LoxErrorType::TypeError,
                            "cannot divide non-numbers",
                        )),
                    },
                    TokenType::Star => match (&left.borrow().value, &right.borrow().value) {
                        (
                            ObjectType::Primitive(PrimitiveObject::Number(l)),
                            ObjectType::Primitive(PrimitiveObject::Number(r)),
                        ) => Ok(Object::number(l * r)),
                        _ => Err(crate::lox::runtime_error(
                            expression.clone(),
                            LoxErrorType::TypeError,
                            "cannot multiply non-numbers",
                        )),
                    },
                    TokenType::Plus => match (&left.borrow().value, &right.borrow().value) {
                        (
                            ObjectType::Primitive(PrimitiveObject::Number(l)),
                            ObjectType::Primitive(PrimitiveObject::Number(r)),
                        ) => Ok(Object::number(l + r)),
                        (
                            ObjectType::Primitive(PrimitiveObject::String(l)),
                            ObjectType::Primitive(PrimitiveObject::String(r)),
                        ) => Ok(Object::string(l.clone() + &r)),
                        _ => Err(crate::lox::runtime_error(
                            expression.clone(),
                            LoxErrorType::TypeError,
                            "addition is defined for numbers and strings",
                        )),
                    },
                    TokenType::Greater
                    | TokenType::GreaterEqual
                    | TokenType::Less
                    | TokenType::LessEqual => Ok(self.apply_compare(
                        op.token_type,
                        &*left.borrow(),
                        &*right.borrow(),
                        expression,
                    )?),
                    TokenType::EqualEqual => Ok(Object::boolean(left == right)),
                    TokenType::BangEqual => Ok(Object::boolean(left != right)),
                    _ => panic!("unimplemented binary operator"),
                }
            }
            Expression::Variable { name, .. } => self.lookup_variable(name, expression),
            Expression::Assignment { name, value, .. } => {
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
            Expression::Logical { left, op, right } => {
                let left = self.interpret_expression(*left)?;

                if op.token_type == TokenType::Or && left.borrow().value.is_truthy() {
                    Ok(left)
                } else if op.token_type == TokenType::And && !left.borrow().value.is_truthy() {
                    Ok(left)
                } else {
                    self.interpret_expression(*right)
                }
            }
            Expression::Call { callee, args, .. } => {
                crate::lox::trace(format!(
                    ">>> Calling function with environment={}",
                    self.environment.borrow().to_string()
                ));
                let callee_obj = self.interpret_expression(*callee.clone())?;

                let mut arguments = Vec::new();
                for arg in args {
                    arguments.push(self.interpret_expression(arg)?);
                }

                let func = LoxFunction::try_from(callee_obj, &expression)?;
                if func.borrow().arity as usize != arguments.len() {
                    Err(crate::lox::runtime_error(
                        *callee,
                        LoxErrorType::FunctionCallError,
                        &format!(
                            "expected {} arguments but got {}.",
                            func.borrow().arity,
                            arguments.len()
                        ),
                    ))
                } else {
                    func.borrow().call(self, arguments, expression)
                }
            }
            Expression::This { keyword, .. } => self.lookup_variable(keyword, expression),
            Expression::Set {
                object,
                name,
                value,
            } => {
                let object = self.interpret_expression(*object)?;

                if object.borrow().value.is_instance() {
                    let value = self.interpret_expression(*value)?;
                    object
                        .clone()
                        .borrow_mut()
                        .value
                        .set(name.lexeme, value.clone());
                    // TODO, and this will probably be far-reaching, object fields need to be Rc references.
                    // this will appear as a bug where object state changes aren't persisted
                    Ok(value)
                } else {
                    Err(crate::lox::runtime_error(
                        expression,
                        LoxErrorType::PropertyError,
                        "only instances have fields",
                    ))
                }
            }
            Expression::Get { object, name } => {
                let object = self.interpret_expression(*object)?;
                if object.borrow().value.is_instance() {
                    object
                        .borrow()
                        .value
                        .get(object.clone(), expression, &name.lexeme)
                } else if object.borrow().value.is_nil() {
                    Err(crate::lox::runtime_error(
                        expression,
                        LoxErrorType::TypeError,
                        &format!(
                            "cannot access property {} on value nil, nil has no properties",
                            name.lexeme
                        ),
                    ))
                } else {
                    // Method retrieval on builtin classes is just property lookup
                    // Adding properties to builtins later would happen here
                    object
                        .borrow()
                        .value
                        .get(object.clone(), expression, &name.lexeme)
                }
            }
        }
    }

    pub fn interpret_statement(&mut self, statement: Statement) -> Result<ObjectRef, LoxError> {
        crate::lox::trace(format!(
            ">>> Interpreting at statement={} env={}",
            statement.to_string(),
            self.environment.borrow().to_string()
        ));
        match statement.clone() {
            Statement::Print { expression } => {
                let obj = self.interpret_expression(expression)?;
                println!("{}", obj.borrow().value.to_string());
                Ok(obj)
            }
            Statement::Expression { expression } => self.interpret_expression(expression),
            Statement::Var { name, initializer } => {
                let value = match initializer {
                    Some(expr) => self.interpret_expression(expr),
                    None => Ok(Object::nil()),
                }?;
                crate::lox::trace(format!(
                    ">>> Defining new variable={} value={}",
                    name.lexeme,
                    value.borrow().value.to_string()
                ));
                self.environment
                    .borrow_mut()
                    .define(name.lexeme, value.clone());
                crate::lox::trace(format!(
                    ">>> After definition env={}",
                    self.environment.borrow().to_string()
                ));
                Ok(value)
            }
            Statement::Block { statements } => {
                self.environment = Environment::extend(self.environment.clone());

                let mut last = Object::nil();
                for statement in statements {
                    last = self.interpret_statement(statement)?;
                }

                self.environment = take_parent(&self.environment);
                Ok(last)
            }
            Statement::If {
                condition,
                then_statement,
                else_statement,
            } => {
                if self
                    .interpret_expression(condition)?
                    .borrow()
                    .value
                    .is_truthy()
                {
                    self.interpret_statement(*then_statement)
                } else {
                    match else_statement {
                        Some(statement) => self.interpret_statement(*statement),
                        None => Ok(Object::nil()),
                    }
                }
            }
            Statement::While { condition, body } => {
                while self
                    .interpret_expression(condition.clone())?
                    .borrow()
                    .value
                    .is_truthy()
                {
                    self.interpret_statement(*body.clone())?;
                }

                Ok(Object::nil())
            }
            Statement::Return { value, .. } => {
                let value = self.interpret_expression(value)?;
                Err(LoxError::ReturnPseudoError { value })
            }
            Statement::Function { definition } => {
                let params = definition
                    .params
                    .iter()
                    .map(|param| param.lexeme.to_owned())
                    .collect();
                // TODO: when creating closures will have to do some unsafe wizardry
                // in order for function environments to point back to the functions
                let func = Object::function(LoxFunction::interpreted(
                    definition.name.lexeme.clone(),
                    params,
                    definition.body,
                    self.environment.clone(),
                ));
                self.environment
                    .borrow_mut()
                    .define(definition.name.lexeme, func);
                Ok(Object::nil())
            }
            Statement::None => Ok(Object::nil()),
            Statement::Class {
                definition: ClassDefinition { name, methods, superclass },
            } => {
                self.environment
                    .borrow_mut()
                    .define(name.lexeme.clone(), Object::nil());

                let superclass = if let Some(sc) = superclass {
                    // We don't check explicitly if sc is a class here because
                    // we already statically determined it was a class in the resolver
                    Some(self.interpret_expression(sc)?)
                } else {
                    None
                };

                let methods: HashMap<String, FunctionRef> = methods
                    .iter()
                    .map(|FunctionDefinition { name, params, body }| {
                        let params = params.iter().map(|token| token.lexeme.clone()).collect();
                        (
                            name.lexeme.clone(),
                            LoxFunction::interpreted(
                                name.lexeme.clone(),
                                params,
                                body.clone(),
                                self.environment.clone(),
                            ),
                        )
                    })
                    .collect();
                let class = Object::class(LoxClass {
                    name: name.lexeme.clone(),
                    superclass,
                    methods,
                });

                // TODO um, the book uses `assign` here, but I deleted that and can't remember why
                self.environment
                    .borrow_mut()
                    .define(name.lexeme.clone(), class.clone());
                Ok(class)
            }
        }
    }

    pub fn apply_compare(
        &self,
        op: TokenType,
        left: &Object,
        right: &Object,
        expression: Expression,
    ) -> Result<ObjectRef, LoxError> {
        if let (
            ObjectType::Primitive(PrimitiveObject::Number(l)),
            ObjectType::Primitive(PrimitiveObject::Number(r)),
        ) = (&left.value, &right.value)
        {
            let result = match op {
                TokenType::Greater => Ok(l > r),
                TokenType::GreaterEqual => Ok(l >= r),
                TokenType::Less => Ok(l < r),
                TokenType::LessEqual => Ok(l <= r),
                _ => Err(crate::lox::runtime_error(
                    expression,
                    LoxErrorType::UnknownOperator,
                    &format!("unable to apply {:?} as a comparison operator", op),
                )),
            };
            result.map(|b| Object::boolean(b))
        } else {
            Err(crate::lox::runtime_error(
                expression,
                LoxErrorType::TypeError,
                &format!("cannot apply operation {:?} to non-numeric types", op),
            ))
        }
    }
}

/**
 * Environment section
 * These are all of the procedures for modifying and retrieving values from an environment
 */

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

    pub fn define(&mut self, name: String, value: ObjectRef) {
        crate::lox::trace(format!(
            ">>> Inserted into environment name={} val={}",
            name,
            value.borrow().value.to_string()
        ));
        self.values.insert(name, value);
        crate::lox::trace(format!(
            ">>> Raw environment contents map={:?}",
            self.values
        ));
    }

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

/**
 * Function section
 * These are all the procedures for creating, executing, and modifying functions, methods,
 * and constructors.
 */

// Implemented so that object class can be debugged
impl std::fmt::Debug for LoxFunction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

// TODO: we could theoretically give each function some ID to track,
// and compare equal if the ids are equal even though the two would be clones
impl PartialEq for LoxFunction {
    fn eq(&self, _other: &Self) -> bool {
        false
    }
}

impl LoxFunction {
    pub fn to_string(&self) -> String {
        format!("<fn {}(arity={})>", self.name, self.arity)
    }

    fn wrap(self) -> FunctionRef {
        Rc::new(RefCell::new(self))
    }

    pub fn native(
        name: String,
        arity: u8,
        global: SharedEnvironment,
        f: fn(Vec<ObjectRef>, SharedEnvironment, Expression) -> Result<ObjectRef, LoxError>,
    ) -> FunctionRef {
        LoxFunction {
            arity,
            name,
            closure: global,
            is_initializer: false,
            exec: Executable::Native(f),
        }
        .wrap()
    }

    pub fn interpreted(
        name: String,
        params: Vec<String>,
        body: Vec<Statement>,
        closure: SharedEnvironment,
    ) -> FunctionRef {
        LoxFunction {
            name,
            arity: params.len() as u8,
            closure,
            is_initializer: false,
            exec: Executable::Interpreted(body, params),
        }
        .wrap()
    }

    fn try_from(object: ObjectRef, expression: &Expression) -> Result<FunctionRef, LoxError> {
        fn err(expression: &Expression) -> Result<FunctionRef, LoxError> {
            Err(crate::lox::runtime_error(
                expression.clone(),
                LoxErrorType::FunctionCallError,
                &format!("exception trying to call non-function"),
            ))
        };
        match &object.borrow().value {
            ObjectType::Primitive(PrimitiveObject::Function(f)) => Ok(f.clone()),
            ObjectType::Instance(Instance { fields, .. }) => match fields.get("__call") {
                Some(obj) => Self::try_from(obj.clone(), expression),
                None => err(expression),
            },
            ObjectType::Primitive(PrimitiveObject::Class(class)) => {
                let arity = if let Some(init) = class.find_method("init") {
                    init.borrow().arity
                } else {
                    0
                };
                let callable = LoxFunction {
                    arity,
                    exec: Executable::Constructor(class.clone()),
                    closure: Environment::new(),
                    is_initializer: true,
                    name: class.name.clone(),
                };
                Ok(callable.wrap())
            }
            _ => err(expression),
        }
    }

    fn bind(&mut self, obj: ObjectRef) -> FunctionRef {
        let env = Environment::extend(self.closure.clone());
        env.borrow_mut().define("this".to_string(), obj);
        LoxFunction {
            closure: env,
            is_initializer: self.is_initializer,
            arity: self.arity,
            exec: self.exec.clone(),
            name: self.name.clone(),
        }
        .wrap()
    }

    fn call(
        &self,
        interpreter: &mut Interpreter,
        args: Vec<ObjectRef>,
        expression: Expression,
    ) -> Result<ObjectRef, LoxError> {
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
                        None => Object::nil(),
                    };
                    interpreter.environment.borrow_mut().define(name, value);
                }

                let mut result = Ok(Object::nil());
                for statement in body {
                    result = match interpreter.interpret_statement(statement) {
                        Ok(obj) => Ok(obj),
                        Err(LoxError::ReturnPseudoError { value }) => {
                            if self.is_initializer {
                                let this =
                                    self.closure.borrow().values.get("this").unwrap().clone();
                                interpreter.environment = old;
                                return Ok(this);
                            } else {
                                interpreter.environment = old;
                                return Ok(value.clone());
                            }
                        }
                        Err(_) => {
                            interpreter.environment = old;
                            return result;
                        }
                    }
                }

                if self.is_initializer {
                    let this = self.closure.borrow().values.get("this").unwrap().clone();
                    interpreter.environment = old;
                    return Ok(this);
                }

                interpreter.environment = old;
                result
            }
            Executable::Native(f) => f(args, self.closure.clone(), expression),
            Executable::Constructor(class) => {
                let initializer = class.find_method("init");
                let instance = Object::instance(Instance {
                    class,
                    fields: HashMap::new(),
                });

                if let Some(init) = initializer {
                    init.borrow_mut().bind(instance.clone()).borrow().call(
                        interpreter,
                        args,
                        expression,
                    )?;
                }

                Ok(instance)
            }
        }
    }
}
