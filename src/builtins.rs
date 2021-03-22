use std::time::{SystemTime, UNIX_EPOCH};

use crate::{
    interpreter::LoxCallable,
    lox::{Lox, LoxError, LoxErrorType},
    parser::{Expression, LoxObject},
};

/*
 * Built-in clock function. We deviate from lox and show miliseconds.
 */
fn clock_impl(lox: &mut Lox, _args: Vec<LoxObject>) -> Result<LoxObject, LoxError> {
    match SystemTime::now().duration_since(UNIX_EPOCH) {
        Ok(time) => Ok(LoxObject::Number(time.as_millis() as f64)),
        Err(_err) => Err(lox.runtime_error(
            Expression::Literal(LoxObject::Nil),
            LoxErrorType::SystemError,
            "error getting system time",
        )),
    }
}

pub fn clock() -> LoxObject {
    LoxObject::Function(LoxCallable::native(0, clock_impl))
}
