extern crate unicode_segmentation;

use std::collections::HashMap;
use std::str::FromStr;

use unicode_segmentation::UnicodeSegmentation;

type LineNumber = u16; // 64K lines
type FileLocation = usize; // 4G chars

pub struct Lox {
    pub had_error: bool,
    reserved_words: HashMap<String, TokenType>,
}

impl Lox {
    pub fn new() -> Lox {
        let mut lox = Lox {
            had_error: false,
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

    pub fn error(&mut self, line: LineNumber, message: &str) {
        println!("[line={}] Error: {}", line, message);
        self.had_error = true;
    }

    pub fn run(&mut self, snippet: String) {
        let mut scanner = Scanner::new(snippet);
        let tokens = scanner.scan_tokens(self);

        for token in tokens {
            println!("{}", token.to_string());
        }
    }
}

/*
This is super simple, a helper enum and accessor methods, plus
a stringify method `repr` for debugging.
*/
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

/*
The first stage in the intepreter pipeline, transforms a string
which could be multiple lines into a list of graphemes. The list
of graphemes will go into the parser.
*/
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
                } else if self.is_alpha(&c) {
                    self.identifier(lox)
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

    fn identifier(&mut self, lox: &mut Lox) -> Token {
        loop {
            if self.is_alpha_numeric(self.peek()) {
                self.advance();
            } else {
                break;
            }
        }

        let lexeme = self.lexeme();
        if let Some(token_type) = lox.reserved_words.get(&lexeme) {
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

/*
This section of the code corresponds to the section of the
book that uses metaprogramming and the visitor pattern to easily
create Java classes to represent nested expressions. The thing
is, in my opinion, Rust is usable enough for this kind of task
that I feel fine creating this code by hand. I might revisit
this using metaprogramming or macros later when I feel better
about Rust 🙂

The ultimate goal here is to show how you can implement N behaviors
for each of M data types, but with Rust that's just `impl`.

So, for example, the book says to create an `AstPrinter` class
which implements visitors for each type, binary/grouping/literal/
unary, which each in turn produce a string. This is logically
equivalent to `ExpressionPrinter` trait which each expression
implements.
*/
pub enum Expression {
    Binary(Box<Expression>, Token, Box<Expression>),
    Grouping(Box<Expression>),
    Literal(Literal),
    Unary(Token, Box<Expression>),
}

impl Expression {
    fn binary(l: Expression, t: Token, r: Expression) -> Expression {
        Expression::Binary(Box::new(l), t, Box::new(r))
    }

    fn grouping(e: Expression) -> Expression {
        Expression::Grouping(Box::new(e))
    }

    fn literal(l: Literal) -> Expression {
        Expression::Literal(l)
    }

    fn unary(t: Token, e: Expression) -> Expression {
        Expression::Unary(t, Box::new(e))
    }
}

trait Printer {
    fn print(&self) -> String;
}

impl Printer for Expression {
    fn print(&self) -> String {
        match self {
            Expression::Binary(l, t, r) => format!("({} {} {})", t.lexeme, l.print(), r.print()),
            Expression::Grouping(e) => format!("({} {})", "group", e.print()),
            Expression::Literal(Literal::None) => format!("nil"),
            Expression::Literal(Literal::LoxString(s)) => format!("{}", s),
            Expression::Literal(Literal::LoxNumber(n)) => format!("{}", n),
            Expression::Unary(t, e) => format!("({} {})", t.lexeme, e.print()),
        }
    }
}

#[derive(Debug, Clone)]
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
