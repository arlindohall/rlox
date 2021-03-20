// Ignore while building
#![ allow( dead_code, unused_imports, unused_variables, unused_must_use ) ]

use std::cmp::PartialEq;
use std::collections::HashMap;

use crate::interpreter::{AstPrinter, Environment, Interpreter};
use crate::parser::{Expression, Parser};
use crate::scanner::{Literal, Scanner, Token, TokenType};

pub type LineNumber = u16; // 64K lines
pub type FileLocation = usize; // 4G chars
pub type LoxNumber = f64; // Numbers are floats, can be improved

#[derive(Debug)]
pub enum LoxError {
    ScanError {
        line: LineNumber,
        message: String,
        err_type: LoxErrorType,
    },
    ParseError {
        cause: Token,
        message: String,
        err_type: LoxErrorType,
    },
    RuntimeError {
        cause: Expression,
        message: String,
        err_type: LoxErrorType,
    },
}

impl LoxError {
    fn to_string(&self) -> String {
        let err_type = match self {
            LoxError::ScanError { err_type, .. } => err_type,
            LoxError::ParseError { err_type, .. } => err_type,
            LoxError::RuntimeError { err_type, .. } => err_type,
        };
        let message = match self {
            LoxError::ScanError { message, .. } => message,
            LoxError::ParseError { message, .. } => message,
            LoxError::RuntimeError { message, .. } => message,
        };
        format!("({:?}) --- {}", err_type, message)
    }
}

#[derive(Debug)]
pub enum LoxErrorType {
    // Scan errors
    UnexpectedCharacter,
    UnterminatedString,

    // Parse errors
    ExpressionError,
    IncompleteExpression,

    // Runtime errors
    TypeError,
    UnknownOperator,
    DivideByZeroError,
    AssignmentError,
}

pub struct Lox {
    pub had_error: bool,
    pub had_runtime_error: bool,
    pub reserved_words: HashMap<String, TokenType>,
}

impl Lox {
    pub fn new() -> Lox {
        let mut lox = Lox {
            had_error: false,
            had_runtime_error: false,
            reserved_words: HashMap::new(),
        };

        lox.reserved_words.insert("and".to_owned(), TokenType::And);
        lox.reserved_words
            .insert("class".to_owned(), TokenType::Class);
        lox.reserved_words
            .insert("else".to_owned(), TokenType::Else);
        lox.reserved_words
            .insert("false".to_owned(), TokenType::False);
        lox.reserved_words.insert("for".to_owned(), TokenType::For);
        lox.reserved_words.insert("fun".to_owned(), TokenType::Fun);
        lox.reserved_words.insert("if".to_owned(), TokenType::If);
        lox.reserved_words.insert("nil".to_owned(), TokenType::Nil);
        lox.reserved_words.insert("or".to_owned(), TokenType::Or);
        lox.reserved_words
            .insert("print".to_owned(), TokenType::Print);
        lox.reserved_words
            .insert("return".to_owned(), TokenType::Return);
        lox.reserved_words
            .insert("super".to_owned(), TokenType::Super);
        lox.reserved_words
            .insert("this".to_owned(), TokenType::This);
        lox.reserved_words
            .insert("true".to_owned(), TokenType::True);
        lox.reserved_words.insert("var".to_owned(), TokenType::Var);
        lox.reserved_words
            .insert("while".to_owned(), TokenType::While);

        lox
    }

    pub fn scan_error(
        &mut self,
        line: LineNumber,
        err_type: LoxErrorType,
        message: &str,
    ) -> LoxError {
        println!("[line={}] ScanError ({:?}): {}", line, err_type, message);
        self.had_error = true;

        LoxError::ScanError {
            message: String::from(message),
            err_type,
            line,
        }
    }

    pub fn parse_error(&mut self, token: Token, err_type: LoxErrorType, message: &str) -> LoxError {
        if token.token_type == TokenType::Eof {
            println!(
                "[line={}] ParseError ({:?} at end): {}",
                token.line, err_type, message
            );
        } else {
            println!(
                "[line={}] ParseError ({:?} at `{}`): {}",
                token.line, err_type, token.lexeme, message
            );
        }
        self.had_error = true;

        LoxError::ParseError {
            message: String::from(message),
            cause: token,
            err_type,
        }
    }

    pub fn runtime_error(
        &mut self,
        expression: Expression,
        err_type: LoxErrorType,
        message: &str,
    ) -> LoxError {
        println!(
            "RuntimeError ({:?} at `{}`): {}",
            err_type,
            expression.to_string(),
            message
        );
        self.had_runtime_error = true;

        LoxError::RuntimeError {
            message: String::from(message),
            cause: expression,
            err_type,
        }
    }

    pub fn run(&mut self, snippet: String) -> Result<(), LoxError> {
        let mut scanner = Scanner::new(snippet);
        let tokens = scanner.scan_tokens(self)?;
        let mut parser = Parser::new(tokens);
        let statements = parser.parse(self)?;

        // TODO: maybe this should be structured so Lox doesn't need
        // to know what an environment is?
        let environment = &mut Environment::new();

        for statement in statements {
            statement.interpret(self, environment);
        }

        Ok(())
    }
}
