use std::{
    cell::RefCell,
    collections::HashMap,
    rc::Rc,
    time::{SystemTime, UNIX_EPOCH},
};

use crate::{
    interpreter::{
        Environment, FunctionRef, LoxClass, LoxFunction, Object, ObjectRef, SharedEnvironment,
    },
    lox::{LoxError, LoxErrorType},
    parser::Expression,
};

/*
 * Built-in clock function. We deviate from lox and show milliseconds.
 */
fn clock_impl(
    _args: Vec<ObjectRef>,
    _environment: SharedEnvironment,
    expression: Expression,
) -> Result<ObjectRef, LoxError> {
    match SystemTime::now().duration_since(UNIX_EPOCH) {
        Ok(time) => Ok(Object::number(time.as_millis() as f64)),
        Err(_err) => Err(crate::lox::runtime_error(
            expression,
            LoxErrorType::SystemError,
            "error getting system time",
        )),
    }
}

pub fn clock(global: Rc<RefCell<Environment>>) -> ObjectRef {
    Object::function(LoxFunction::native(
        "clock".to_string(),
        0,
        global,
        clock_impl,
    ))
}

/*
 * Built-in classes.
 */
struct Builtins {
    boolean: Option<LoxClass>,
    number: Option<LoxClass>,
    string: Option<LoxClass>,
    function: Option<LoxClass>,
    meta_class: Option<LoxClass>,
    nil: Option<LoxClass>,
}

static mut BUILTINS: Builtins = Builtins {
    boolean: None,
    number: None,
    string: None,
    function: None,
    meta_class: None,
    nil: None,
};

pub fn boolean() -> LoxClass {
    unsafe {
        if let None = BUILTINS.boolean {
            BUILTINS.boolean = Some(
                LoxClass::new("Boolean".to_string(), builtin_methods())
            );
        }
        BUILTINS.boolean.clone().unwrap()
    }
}

pub fn number() -> LoxClass {
    unsafe {
        if let None = BUILTINS.number {
            BUILTINS.number = Some(
                LoxClass::new("Number".to_string(), builtin_methods())
            );
        }
        BUILTINS.number.clone().unwrap()
    }
}

pub fn string() -> LoxClass {
    unsafe {
        if let None = BUILTINS.string {
            let mut shared = builtin_methods();
            shared.insert("to_number".to_string(), to_number());
            BUILTINS.string = Some(
                LoxClass::new("String".to_string(), shared)
            );
        }
        BUILTINS.string.clone().unwrap()
    }
}

pub fn function() -> LoxClass {
    unsafe {
        if let None = BUILTINS.function {
            BUILTINS.function = Some(
                LoxClass::new("Function".to_string(), builtin_methods())
            );
        }
        BUILTINS.function.clone().unwrap()
    }
}

pub fn meta_class() -> LoxClass {
    unsafe {
        if let None = BUILTINS.meta_class {
            BUILTINS.meta_class = Some(
                LoxClass::new("Class".to_string(), builtin_methods())
            );
        }
        BUILTINS.meta_class.clone().unwrap()
    }
}

pub fn nil() -> LoxClass {
    unsafe {
        if let None = BUILTINS.nil {
            BUILTINS.nil = Some(
                LoxClass::new("Nil".to_string(), builtin_methods())
            );
        }
        BUILTINS.nil.clone().unwrap()
    }
}

/*
 * Shared built-in methods.
 */
fn builtin_methods() -> HashMap<String, FunctionRef> {
    let mut methods = HashMap::new();
    methods.insert("to_string".to_string(), to_string());

    methods
}

fn to_string_impl(
    _args: Vec<ObjectRef>,
    environment: SharedEnvironment,
    expression: Expression,
) -> Result<ObjectRef, LoxError> {
    if let Some(this) = environment.borrow_mut().values.get("this") {
        Ok(Object::string(this.borrow_mut().to_string()))
    } else {
        Err(crate::lox::runtime_error(
            expression,
            LoxErrorType::TypeError,
            "called 'to_string' on non-object",
        ))
    }
}

fn to_string() -> FunctionRef {
    LoxFunction::native("to_string".to_string(), 0, Environment::new(), to_string_impl)
}

/*
 * String builtins
 */
fn to_number_impl(_args: Vec<ObjectRef>, environment: SharedEnvironment, expression: Expression) -> Result<ObjectRef, LoxError> {
    if let Some(this) = environment.borrow_mut().values.get("this") {
        let string = this.borrow().to_string();
        match string.parse() {
            Ok(num) => Ok(Object::number(num)),
            Err(_) => Err(crate::lox::runtime_error(
                expression,
                LoxErrorType::TypeError,
                &format!("cannot convert {} to number", string)
            ))
        }
    } else {
        Err(crate::lox::runtime_error(
            expression,
            LoxErrorType::TypeError,
            "called 'to_number' on non-string",
        ))
    }
}

fn to_number() -> FunctionRef {
    LoxFunction::native("to_number".to_string(), 0, Environment::new(), to_number_impl)
}