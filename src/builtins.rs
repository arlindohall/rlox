use std::{cell::RefCell, collections::HashMap, rc::Rc, time::{SystemTime, UNIX_EPOCH}};

use crate::{interpreter::{Environment, FunctionRef, LoxClass, LoxFunction, Object, ObjectRef, SharedEnvironment}, lox::{LoxError, LoxErrorType}, parser::Expression};

/*
 * Built-in clock function. We deviate from lox and show milliseconds.
 */
fn clock_impl(_args: Vec<ObjectRef>, _environment: SharedEnvironment, expression: Expression) -> Result<ObjectRef, LoxError> {
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
pub fn boolean(environment: SharedEnvironment) -> LoxClass {
    LoxClass::new(
        "Boolean".to_string(),
        builtin_methods(environment)
    )
}

pub fn number(environment: SharedEnvironment) -> LoxClass {
    LoxClass::new(
        "Number".to_string(),
        builtin_methods(environment)
    )
}

pub fn string(environment: SharedEnvironment) -> LoxClass {
    LoxClass::new(
        "String".to_string(),
        builtin_methods(environment)
    )
}

pub fn function(environment: SharedEnvironment) -> LoxClass {
    LoxClass::new(
        "Function".to_string(),
        builtin_methods(environment)
    )
}

pub fn meta_class(environment: SharedEnvironment) -> LoxClass {
    LoxClass::new(
        "Class".to_string(),
        builtin_methods(environment)
    )
}

pub fn nil(environment: SharedEnvironment) -> LoxClass {
    LoxClass::new(
        "Nil".to_string(),
        builtin_methods(environment)
    )
}

/*
 * Shared built-in methods.
 */
fn builtin_methods(environment: SharedEnvironment) -> HashMap<String, FunctionRef> {
    let mut methods = HashMap::new();
    methods.insert("to_string".to_string(), to_string(environment));

    methods
}

fn to_string_impl(_args: Vec<ObjectRef>, environment: SharedEnvironment, expression: Expression) -> Result<ObjectRef, LoxError> {
    if let Some(this) = environment.borrow_mut().values.get("this") {
        Ok(Object::string(this.borrow_mut().to_string()))
    } else {
        Err(crate::lox::runtime_error(
            expression,
            LoxErrorType::TypeError,
            "called 'to_string' on non-object"
        ))
    }
}

fn to_string(environment: SharedEnvironment) -> FunctionRef {
    LoxFunction::native("to_string".to_string(), 0, environment, to_string_impl)
}