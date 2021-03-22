
use std::time::{SystemTime, UNIX_EPOCH};

use crate::{interpreter::{LoxCallable}, lox::LoxError, parser::LoxObject};

/*
 * Built-in clock function. We deviate from lox and show miliseconds.
 */
fn clock_impl(_args: Vec<LoxObject>) -> Result<LoxObject, LoxError> {
    match SystemTime::now().duration_since(UNIX_EPOCH) {
        Ok(time) => Ok(LoxObject::Number(time.as_millis() as f64)),
        Err(_err) => todo!(), // TODO: how to handle legit system time error?
    }
}

pub fn clock() -> LoxObject {
    LoxObject::Function(
        LoxCallable::native(0, clock_impl)
    )
}