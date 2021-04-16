use crate::{
    builtins::clock,
    interpreter::ObjectRef,
    parser::{Expression, Parser},
};
use crate::{
    builtins::list,
    interpreter::SharedEnvironment,
    scanner::{Scanner, Token, TokenType},
};
use crate::{
    interpreter::{AstPrinter, Environment, Interpreter},
    resolver::Resolver,
};

pub type LineNumber = u16; // 64K lines
pub type FileLocation = usize; // 4G chars
pub type LoxNumber = f64; // Numbers are floats, can be improved

type ReservedWord = (&'static str, TokenType);

pub static TRACE: bool = false;

static mut HAD_ERROR: bool = false;
static mut HAD_RUNTIME_ERROR: bool = false;

static RESERVED_WORDS: &[ReservedWord] = &[
    ("and", TokenType::And),
    ("class", TokenType::Class),
    ("else", TokenType::Else),
    ("false", TokenType::False),
    ("for", TokenType::For),
    ("fun", TokenType::Fun),
    ("if", TokenType::If),
    ("nil", TokenType::Nil),
    ("or", TokenType::Or),
    ("print", TokenType::Print),
    ("return", TokenType::Return),
    ("super", TokenType::Super),
    ("this", TokenType::This),
    ("true", TokenType::True),
    ("var", TokenType::Var),
    ("while", TokenType::While),
];

/*
 * Gross gross gross gross gross gross gross
 */
pub fn clear_errors() {
    unsafe {
        HAD_ERROR = false;
        HAD_RUNTIME_ERROR = false;
    }
}

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
    LoxErrorList {
        errors: Vec<LoxError>,
    },
    ReturnPseudoError {
        value: ObjectRef,
    },
}

impl LoxError {
    pub fn to_string(&self) -> String {
        let err_type = match self {
            LoxError::ScanError { err_type, .. } => format!("{:?}", err_type),
            LoxError::ParseError { err_type, .. } => format!("{:?}", err_type),
            LoxError::RuntimeError { err_type, .. } => format!("{:?}", err_type),
            LoxError::LoxErrorList { .. } => format!("ErrorList"),
            LoxError::ReturnPseudoError { value: _ } => "return".to_string(),
        };
        let message = match self {
            LoxError::ScanError { message, .. } => message.to_string(),
            LoxError::ParseError { message, .. } => message.to_string(),
            LoxError::RuntimeError { message, .. } => message.to_string(),
            LoxError::LoxErrorList { errors } => errors
                .iter()
                .map(|e| e.to_string())
                .collect::<Vec<String>>()
                .join(", "),
            LoxError::ReturnPseudoError { value } => value.borrow().to_string(),
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
    DefinitionError,
    InitializationError,
    ReferenceError,
    ClassError,

    // Runtime errors
    TypeError,
    UnknownOperator,
    DivideByZeroError,
    AssignmentError,
    FunctionCallError,
    PropertyError,

    SystemError,
}

pub fn had_error() -> bool {
    unsafe { HAD_ERROR }
}

pub fn had_runtime_error() -> bool {
    unsafe { HAD_RUNTIME_ERROR }
}

pub fn scan_error(line: LineNumber, err_type: LoxErrorType, message: &str) -> LoxError {
    println!("[line={}] ScanError ({:?}): {}", line, err_type, message);
    unsafe {
        HAD_ERROR = true;
    }

    LoxError::ScanError {
        message: String::from(message),
        err_type,
        line,
    }
}

pub fn parse_error(token: Token, err_type: LoxErrorType, message: &str) -> LoxError {
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
    unsafe {
        HAD_ERROR = true;
    }

    LoxError::ParseError {
        message: String::from(message),
        cause: token,
        err_type,
    }
}

pub fn runtime_error(expression: Expression, err_type: LoxErrorType, message: &str) -> LoxError {
    println!(
        "RuntimeError ({:?} at `{}`): {}",
        err_type,
        expression.to_string(),
        message
    );
    unsafe {
        HAD_RUNTIME_ERROR = true;
    }

    LoxError::RuntimeError {
        message: String::from(message),
        cause: expression,
        err_type,
    }
}

pub fn reserved(name: &str) -> Option<TokenType> {
    for word in RESERVED_WORDS.iter() {
        if word.0 == name {
            return Some(word.1.clone());
        }
    }
    None
}

pub struct Lox {
    environment: SharedEnvironment,
}

impl Lox {
    pub fn new() -> Lox {
        let environment = Environment::new();
        Lox { environment }
    }

    pub fn run(&mut self, snippet: String) -> Result<(), LoxError> {
        let mut scanner = Scanner::new(snippet);
        let tokens = scanner.scan_tokens()?;
        let mut parser = Parser::new(tokens);
        let statements = parser.parse()?;

        let clock = clock(self.environment.clone());
        self.environment
            .borrow_mut()
            .define("clock".to_owned(), clock);
        let list = list(self.environment.clone());
        self.environment
            .borrow_mut()
            .define("list".to_owned(), list);

        let interpreter = Interpreter::with_env(self.environment.clone());
        let mut resolver = Resolver::new(interpreter);

        let mut errors = Vec::new();
        for statement in &statements {
            let result = resolver.resolve_statement(statement);
            if let Err(e) = result {
                errors.push(e);
            }
        }

        if errors.len() > 0 {
            return Err(LoxError::LoxErrorList { errors });
        }

        let mut interpreter = resolver.destruct();
        for statement in statements {
            interpreter.interpret_statement(statement)?;
        }

        Ok(())
    }
}
