use std::{
    cell::RefCell,
    rc::Rc,
    time::{SystemTime, UNIX_EPOCH},
};

use crate::{
    interpreter::{Environment, LoxCallable},
    lox::{LoxError, LoxErrorType},
    parser::{Expression, LoxObject},
};

/*
 * Built-in clock function. We deviate from lox and show miliseconds.
 */
fn clock_impl(_args: Vec<LoxObject>) -> Result<LoxObject, LoxError> {
    match SystemTime::now().duration_since(UNIX_EPOCH) {
        Ok(time) => Ok(LoxObject::Number(time.as_millis() as f64)),
        Err(_err) => Err(crate::lox::runtime_error(
            Expression::Literal(LoxObject::Nil),
            LoxErrorType::SystemError,
            "error getting system time",
        )),
    }
}

pub fn clock(global: Rc<RefCell<Environment>>) -> LoxObject {
    LoxObject::Function(LoxCallable::native(
        "clock".to_string(),
        0,
        global,
        clock_impl,
    ))
}
