use crate::{interpreter::{LoxCallable}, lox::LoxError, parser::LoxObject};



/*
 * Built-in clock function
 */
fn clock_impl(args: Vec<LoxObject>) -> Result<LoxObject, LoxError> {
    Ok(LoxObject::Number(0.0))
}

pub fn clock() -> LoxObject {
    LoxObject::Function(
        LoxCallable::native(0, clock_impl)
    )
}