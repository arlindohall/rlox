// Ignore while building
#![ allow( dead_code, unused_imports, unused_variables, unused_must_use ) ]

extern crate unicode_segmentation;

use std::str::FromStr;

use unicode_segmentation::UnicodeSegmentation;

use crate::lox::{FileLocation, LineNumber, Lox, LoxError, LoxErrorType, LoxNumber};

/*******************************************************************************
********************************************************************************
                                SCANNER
********************************************************************************

This section contains the first logical division of the interpreter: the
scanner. It takes the input, which has already been grouped into graphemes
(utf-8 character clusters, useful so we can act on what users think of as
characters), and converts each string into tokens. The tokens can then be
passed off to the parser to be turned into data structures that can be
interpreted.

*******************************************************************************/

/*
This is super simple, a helper enum and accessor methods, plus a stringify
method `repr` for debugging.
*/
#[derive(Debug, Clone, PartialEq)]
pub enum Literal {
    Boolean(bool),
    String(String),
    Number(LoxNumber),
    None,
}

impl Literal {
    pub fn repr(&self) -> String {
        match self {
            Literal::String(s) => format!("\"{}\"", s),
            Literal::Number(n) => format!("{}", n),
            Literal::Boolean(b) => format!("{}", b),
            Literal::None => format!("None"),
        }
    }

    pub fn get_string(self) -> Option<String> {
        if let Literal::String(s) = self {
            Some(s)
        } else {
            None
        }
    }

    pub fn get_number(self) -> Option<LoxNumber> {
        if let Literal::Number(n) = self {
            Some(n)
        } else {
            None
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
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

#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub token_type: TokenType,
    pub lexeme: String,
    pub literal: Literal,
    pub line: LineNumber,
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

enum ScanResult {
    Empty,
    Error(LoxError),
    Token(Token),
}

/*
The first stage in the intepreter pipeline, transforms a string which could
be multiple lines into a list of graphemes. The list of graphemes will go
into the parser.
*/
pub struct Scanner {
    graphemes: Vec<String>,
    start: FileLocation,
    next: FileLocation,
    line: LineNumber,
    col: LineNumber,
}

impl Scanner {
    pub fn new(snippet: String) -> Scanner {
        let graphemes = UnicodeSegmentation::graphemes(&snippet[..], true)
            .map(|grph| String::from(grph))
            .collect::<Vec<String>>();
        Scanner {
            start: 0,
            next: 0,
            col: 1,
            line: 1,
            graphemes,
        }
    }

    pub fn scan_tokens(&mut self) -> Result<Vec<Token>, LoxError> {
        let mut tokens = Vec::new();
        while !self.is_at_end() {
            self.start = self.next;
            let result = self.scan_token();

            if let ScanResult::Token(token) = result {
                tokens.push(token);
            } else if let ScanResult::Error(error) = result {
                return Err(error);
            }
        }

        tokens.push(Token {
            token_type: TokenType::Eof,
            line: self.line,
            literal: Literal::None,
            lexeme: "".to_owned(),
        });

        Ok(tokens)
    }

    // TODO: I don't like passing lox in, I'd rather find a better way to
    // implement what Bob calls separation of the code that reports errors from
    // the code that handles errors
    fn scan_token(&mut self) -> ScanResult {
        self.col += 1;
        let c = self.advance();
        // println!("Scanning token starting at c={}", c);
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
                    return ScanResult::Empty;
                } else {
                    self.new_token(TokenType::Slash)
                }
            }
            " " => return ScanResult::Empty,
            "\r" => return ScanResult::Empty,
            "\t" => return ScanResult::Empty,
            "\n" => {
                self.line += 1;
                self.col = 1;
                return ScanResult::Empty;
            }
            "\"" => self.string(),
            _ => {
                // Borrow c again as immutable to avoid reference error
                let c = self.prev();
                if self.is_digit(&c) {
                    self.number()
                } else if self.is_alpha(&c) {
                    self.identifier()
                } else {
                    let message = format!("unexpected character '{}' at [col={}]", c, self.col);
                    let err =
                        crate::lox::scan_error(self.line, LoxErrorType::UnexpectedCharacter, &message);
                    // ScanResult::Error(err)
                    return ScanResult::Empty;
                }
            }
        };

        // println!("Scanned token={}", token.to_string());
        ScanResult::Token(token)
    }

    fn advance(&mut self) -> &str {
        let current = &self.graphemes[self.next];
        self.next += 1;
        current
    }

    // TODO: Enforce calling only after one call of advance
    fn prev(&self) -> &str {
        &self.graphemes[self.next - 1]
    }

    /*
    Basically for both peek and peek_next, we're checking for what the next
    or character after next contains. If we call `peek` during the match
    statement of the scan_token (main block of scanning logic) then we're
    actually looking at the next character, but if we call it before then,
    we're looking at the character currently being scanned (about to be
    scanned).

    What this means is that both peek and peek_next can look into the future,
    and can go over the length of the `graphemes` vector. If that happens,
    we'll panic and quit the whole program. But wait, that's bad! So instead
    we just guard and return `\0` as a way to pretend the rest of memory
    after the end of the vec is all zeros, which as far as the interpreter is
    concerned, makes sense.
    */
    fn peek(&self) -> &str {
        if self.next >= self.graphemes.len() {
            "\0"
        } else {
            &self.graphemes[self.next]
        }
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

    fn is_alpha(&self, c: &str) -> bool {
        match c {
            "a" | "b" | "c" | "d" | "e" | "f" | "g" | "h" | "i" | "j" | "k" | "l" | "m" | "n"
            | "o" | "p" | "q" | "r" | "s" | "t" | "u" | "v" | "w" | "x" | "y" | "z" | "A" | "B"
            | "C" | "D" | "E" | "F" | "G" | "H" | "I" | "J" | "K" | "L" | "M" | "N" | "O" | "P"
            | "Q" | "R" | "S" | "T" | "U" | "V" | "W" | "X" | "Y" | "Z" | "_" => true,
            _ => false,
        }
    }

    fn is_alpha_numeric(&self, c: &str) -> bool {
        return self.is_digit(c) || self.is_alpha(c);
    }

    fn string(&mut self) -> Token {
        // println!("Scanning string starting at c={}{}", self.prev(), self.peek());
        loop {
            if self.is_at_end() {
                break;
            };
            let c = self.advance();
            // println!("Scanning character c={}", c);
            if c == "\"" {
                break;
            }
            if c == "\n" {
                self.line += 1;
                break;
            }
        }

        // If we're at the end, but we've advanced and the last character is a
        // quotation, that's actually okay. We're probably in the interactive
        // mode and didn't have another character after the end of the string,
        // i.e. > "a"
        if self.is_at_end() && !(self.prev() == "\"" && self.next > self.start) {
            crate::lox::scan_error(
                self.line,
                LoxErrorType::UnterminatedString,
                "unterminated string",
            );
        }

        let mut lexeme = String::new();
        for i in self.start + 1..self.next - 1 {
            lexeme.push_str(&self.graphemes[i]);
        }

        Token {
            token_type: TokenType::LoxString,
            line: self.line,
            literal: Literal::String(lexeme.clone()),
            lexeme: lexeme,
        }
    }

    fn number(&mut self) -> Token {
        loop {
            let c = self.peek();
            // println!("Looking for number c={}", c);
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
            literal: Literal::Number(d),
            lexeme: self.lexeme(),
        }
    }

    fn identifier(&mut self) -> Token {
        loop {
            if self.is_alpha_numeric(self.peek()) {
                self.advance();
            } else {
                break;
            }
        }

        let lexeme = self.lexeme();
        if let Some(token_type) = crate::lox::reserved(&lexeme) {
            let token_type = token_type.to_owned();
            Token {
                token_type,
                line: self.line,
                literal: Literal::None,
                lexeme: self.lexeme(),
            }
        } else {
            Token {
                token_type: TokenType::Identifier,
                line: self.line,
                literal: Literal::None,
                lexeme: self.lexeme(),
            }
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
