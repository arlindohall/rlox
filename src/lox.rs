use std::error::Error;
use std::fs::File;
use std::io::{BufRead, Read};

type LineNumber = u16;

pub struct Lox {
    had_error: bool,
}

impl Lox {
    pub fn new() -> Lox {
        return Lox { had_error: false };
    }

    pub fn run_file(&self, name: &str) -> Result<(), Box<dyn Error>> {
        let mut contents = String::new();
        File::open(name)?.read_to_string(&mut contents)?;

        self.run(contents);
        if self.had_error {
            std::process::exit(65);
        } else {
            return Ok(());
        }
    }

    pub fn run_prompt(&mut self) -> Result<(), Box<dyn Error>> {
        println!("Getting input");
        let stdin = std::io::stdin();
        let lock = stdin.lock();

        for line in lock.lines() {
            self.run(line?);
            self.had_error = false;
        }

        return Ok(());
    }

    pub fn error(&mut self, line: LineNumber, message: &str) {
        println!("[line={}] Error: {}", line, message);
        self.had_error = true;
    }

    fn run(&self, snippet: String) {
        let scanner = Scanner::new(snippet);
        let tokens = scanner.scan_tokens(self);

        for token in tokens {
            println!("{}", token);
        }
    }
}

pub struct Scanner {
    text: String,
}

impl Scanner {
    pub fn scan_tokens(&self, lox: &Lox) -> Vec<String> {
        let mut tokens = Vec::new();
        for item in self.text.split(" ") {
            tokens.push(String::from(item));
        }
        return tokens;
    }

    pub fn new(snippet: String) -> Scanner {
        Scanner { text: snippet }
    }
}

#[derive(Debug)]
enum TokenType {
    // Single-character tokens.
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    Comma,
    Dot,
    Minus,
    Plus,
    Semicolon,
    Slash,
    Star,

    // One or two character tokens.
    Bang,
    BangEqual,
    Equal,
    EqualEqual,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,

    // Literals.
    Identifier,
    LoxString, // String is a Rust type
    Number,

    // Keywords.
    And,
    Class,
    Else,
    False,
    Fun,
    For,
    If,
    Nil,
    Or,
    Print,
    Return,
    Super,
    This,
    True,
    Var,
    While,

    Eof,
}

struct Token<T: std::fmt::Display> {
    token_type: TokenType,
    lexeme: String,
    literal: T,
    line: LineNumber,
}

impl<T: std::fmt::Display> Token<T> {
    fn to_string(&self) {
        format!(
            "Token(token_type={:?}, lexeme={}, literal={})",
            self.token_type, self.lexeme, self.literal
        );
    }
}
