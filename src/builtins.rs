use std::{
    cell::RefCell,
    rc::Rc,
    time::{SystemTime, UNIX_EPOCH},
};

use crate::{
    interpreter::{Environment, LoxFunction, Object, ObjectRef},
    lox::{LoxError, LoxErrorType},
    parser::Expression,
};

/*
 * Built-in clock function. We deviate from lox and show miliseconds.
 */
fn clock_impl(_args: Vec<ObjectRef>, expression: Expression) -> Result<ObjectRef, LoxError> {
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
