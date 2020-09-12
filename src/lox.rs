extern crate unicode_segmentation;

use std::error::Error;
use std::fs::File;
use std::io::{BufRead, Read};
use std::str::FromStr;

use unicode_segmentation::UnicodeSegmentation;

type LineNumber = u16; // 64K lines
type FileLocation = usize; // 4G chars

pub struct Lox {
    had_error: bool,
}

impl Lox {
    pub fn new() -> Lox {
        Lox { had_error: false }
    }

    pub fn run_file(&mut self, name: &str) -> Result<(), Box<dyn Error>> {
        let mut contents = String::new();
        File::open(name)?.read_to_string(&mut contents)?;

        self.run(contents);
        if self.had_error {
            std::process::exit(65);
        } else {
            Ok(())
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

        Ok(())
    }

    pub fn error(&mut self, line: LineNumber, message: &str) {
        println!("[line={}] Error: {}", line, message);
        self.had_error = true;
    }

    fn run(&mut self, snippet: String) {
        let mut scanner = Scanner::new(snippet);
        let tokens = scanner.scan_tokens(self);

        for token in tokens {
            println!("{}", token.to_string());
        }
    }
}

pub enum Literal {
    LoxString(String),
    LoxNumber(f64),
    None,
}

impl Literal {
    fn get_number(&self) -> Option<&f64> {
        if let Literal::LoxNumber(f) = self {
            Some(f)
        } else {
            None
        }
    }

    fn get_string(&self) -> Option<&str> {
        if let Literal::LoxString(s) = self {
            Some(s)
        } else {
            None
        }
    }

    fn repr(&self) -> String {
        match self {
            Literal::LoxString(s) => format!("Literal(string={})", s),
            Literal::LoxNumber(n) => format!("Literal(number={})", n),
            Literal::None => format!("None"),
        }
    }
}

pub struct Scanner {
    graphemes: Vec<String>,
    start: FileLocation,
    next: FileLocation,
    line: LineNumber,
}

impl Scanner {
    pub fn new(snippet: String) -> Scanner {
        Scanner {
            graphemes: UnicodeSegmentation::graphemes(&snippet[..], true)
                .map(|grph| String::from(grph))
                .collect::<Vec<String>>(),
            start: 0,
            next: 0,
            line: 1,
        }
    }

    // TODO: remove passing lox in here, make some shared error handler
    pub fn scan_tokens(&mut self, lox: &mut Lox) -> Vec<Token> {
        let mut tokens = Vec::new();
        while !self.is_at_end() {
            self.start = self.next;
            match self.scan_token(lox) {
                Ok(token) => tokens.push(token),
                Err(()) => (),
            }
        }

        tokens.push(Token {
            token_type: TokenType::Eof,
            line: self.line,
            literal: Literal::None,
            lexeme: "".to_owned(),
        });

        tokens
    }

    // TODO: I don't like passing lox in, I'd rather find a better way to
    // implement what Bob calls separation of the code that reports errors
    // from the code that handles errors
    fn scan_token(&mut self, lox: &mut Lox) -> Result<Token, ()> {
        let c = self.advance();
        let token = match c {
            "(" => self.new_token(TokenType::LeftParen),
            ")" => self.new_token(TokenType::RightParen),
            "{" => self.new_token(TokenType::LeftBrace),
            "}" => self.new_token(TokenType::RightBrace),
            "," => self.new_token(TokenType::Comma),
            "." => self.new_token(TokenType::Dot),
            "-" => self.new_token(TokenType::Minus),
            "+" => self.new_token(TokenType::Plus),
            ";" => self.new_token(TokenType::Semicolon),
            "*" => self.new_token(TokenType::Star),
            "!" => {
                let token = if self.is_match("=") {
                    TokenType::BangEqual
                } else {
                    TokenType::Bang
                };
                self.new_token(token)
            }
            "=" => {
                let token = if self.is_match("=") {
                    TokenType::EqualEqual
                } else {
                    TokenType::Equal
                };
                self.new_token(token)
            }
            "<" => {
                let token = if self.is_match("=") {
                    TokenType::LessEqual
                } else {
                    TokenType::Less
                };
                self.new_token(token)
            }
            ">" => {
                let token = if self.is_match("=") {
                    TokenType::GreaterEqual
                } else {
                    TokenType::Greater
                };
                self.new_token(token)
            }
            "/" => {
                if self.is_match("/") {
                    loop {
                        if self.is_at_end() || self.advance() == "\n" {
                            break;
                        }
                    }
                    self.line += 1;
                    return Err(()); // No token
                } else {
                    self.new_token(TokenType::Slash)
                }
            }
            " " => return Err(()),
            "\r" => return Err(()),
            "\t" => return Err(()),
            "\n" => {
                self.line += 1;
                return Err(());
            }
            // TODO: remove passing lox in here, make some shared error handler
            "\"" => self.string(lox),
            _ => {
                // Borrow c again as immutable to avoid reference error
                let c = self.peek();
                if self.is_digit(&c) {
                    self.number(lox)
                } else {
                let message = format!("Unexpected character '{}'", c);
                lox.error(self.line, &message);
                return Err(());
            }
            }
        };

        Ok(token)
    }

    fn advance(&mut self) -> &str {
        let current = &self.graphemes[self.next];
        self.next += 1;
        current
    }

    fn peek(&self) -> &str {
        &self.graphemes[self.next]
    }

    fn peek_next(&self) -> &str {
        if self.next + 1 >= self.graphemes.len() {
            "\0"
        } else {
            &self.graphemes[self.next + 1]
        }
    }

    fn is_at_end(&self) -> bool {
        self.next >= self.graphemes.len()
    }

    fn is_match(&mut self, against: &str) -> bool {
        if self.is_at_end() {
            return false;
        };
        if self.peek() != against {
            // is_match doesn't consume characters that don't match, for example
            // is_match on the character after '=' when it's just an equals sign
            false
        } else {
            self.advance();
            true
        }
    }

    fn is_digit(&self, c: &str) -> bool {
        match c {
            "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" => true,
            _ => false,
        }
    }

    // TODO: remove passing lox in here, make some shared error handler
    fn string(&mut self, lox: &mut Lox) -> Token {
        loop {
            if self.is_at_end() {
                break;
            };
            let c = self.advance();
            if c == "\"" {
                break;
            }
            if c == "\n" {
                self.line += 1;
                break;
            }
        }

        if self.is_at_end() {
            lox.error(self.line, "Unterminated string");
        }

        let mut lexeme = String::new();
        for i in self.start + 1..self.next - 1 {
            lexeme.push_str(&self.graphemes[i]);
        }

        Token {
            token_type: TokenType::LoxString,
            line: self.line,
            literal: Literal::LoxString(lexeme.clone()), // TODO is this dumb?
            lexeme: lexeme,
        }
    }

    fn number(&mut self, _lox: &mut Lox) -> Token {
        loop {
            let c = self.peek();
            if self.is_digit(c) {
                self.advance();
            } else {
                break;
            }
        }

        if self.peek() == "." && self.is_digit(self.peek_next()) {
            self.advance();
            loop {
                let c = self.peek();
                if self.is_digit(c) {
                    self.advance();
                } else {
                    break;
                }
            }
        }

        // Panic if we can't parse the thing we already checked was a number
        let d = f64::from_str(&self.lexeme()).unwrap();
        Token {
            token_type: TokenType::Number,
            line: self.line,
            literal: Literal::LoxNumber(d),
            lexeme: self.lexeme(),
        }
    }

    fn new_token(&mut self, token_type: TokenType) -> Token {
        Token {
            token_type: token_type,
            line: self.line,
            literal: Literal::None,
            lexeme: self.lexeme(),
        }
    }

    fn lexeme(&self) -> String {
        let mut lexeme = String::new();
        for i in self.start..self.next {
            lexeme.push_str(&self.graphemes[i]);
        }
        lexeme
    }
}

#[derive(Debug)]
pub enum TokenType {
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

pub struct Token {
    token_type: TokenType,
    lexeme: String,
    literal: Literal,
    line: LineNumber,
}

impl Token {
    fn to_string(&self) -> String {
        format!(
            "Token(token_type={:?}, lexeme=\"{}\", literal={})",
            self.token_type,
            self.lexeme,
            self.literal.repr(),
        )
    }
}
