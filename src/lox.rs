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

    pub fn scan_error(&mut self, line: LineNumber, message: &str) {
        println!("[line={}] ScanError: {}", line, message);
        self.had_error = true;
    }

    pub fn parse_error(&mut self, token: Token, message: &str) {
        if token.token_type == TokenType::Eof {
            println!("[line={}] ParseError at end: {}", token.line, message);
        } else {
            println!(
                "[line={}] ParseError (at '{}'): {}",
                token.line, token.lexeme, message
            );
        }
        self.had_error = true;
    }

    pub fn run(&mut self, snippet: String) {
        let mut scanner = Scanner::new(snippet);
        let tokens = scanner.scan_tokens(self);
        let mut parser = Parser::new(tokens);
        match parser.parse(self) {
            Ok(expr) => println!("{}", expr.print()),
            Err(e) => println!("ParseError: "),
        }
    }
}

/*
This is super simple, a helper enum and accessor methods, plus
a stringify method `repr` for debugging.
*/
#[derive(Clone)]
pub enum Literal {
    // TODO: Object(),
    Boolean(bool),
    String(String),
    Number(f64),
    None,
}

impl Literal {
    fn repr(&self) -> String {
        match self {
            Literal::String(s) => format!("\"{}\"", s),
            Literal::Number(n) => format!("{}", n),
            Literal::Boolean(b) => format!("{}", b),
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
                self.col = 1;
                return Err(());
            }
            // TODO: remove passing lox in here, make some shared error handler
            "\"" => self.string(lox),
            _ => {
                // Borrow c again as immutable to avoid reference error
                let c = self.prev();
                if self.is_digit(&c) {
                    self.number(lox)
                } else if self.is_alpha(&c) {
                    self.identifier(lox)
                } else {
                    let message = format!("Unexpected character '{}' at [col={}]", c, self.col);
                    lox.scan_error(self.line, &message);
                    return Err(());
                }
            }
        };

        // println!("Scanned token={}", token.to_string());
        Ok(token)
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
    or character after next contains. If we call `peek` during the match statement
    of the scan_token (main block of scanning logic) then we're actually looking
    at the next character, but if we call it before then, we're looking at the
    character currently being scanned (about to be scanned).

    What this means is that both peek and peek_next can look into the future, and
    can go over the length of the `graphemes` vector. If that happens, we'll panic
    and quit the whole program. But wait, that's bad! So instead we just guard and
    return `\0` as a way to pretend the rest of memory after the end of the vec
    is all zeros, which as far as the interpreter is concerned, makes sense.
    */
    fn peek(&self) -> &str {
        if self.next + 1 >= self.graphemes.len() {
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
            lox.scan_error(self.line, "Unterminated string");
        }

        let mut lexeme = String::new();
        for i in self.start + 1..self.next - 1 {
            lexeme.push_str(&self.graphemes[i]);
        }

        Token {
            token_type: TokenType::LoxString,
            line: self.line,
            literal: Literal::String(lexeme.clone()), // TODO is this dumb?
            lexeme: lexeme,
        }
    }

    fn number(&mut self, _lox: &mut Lox) -> Token {
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

#[derive(Debug, Clone, std::cmp::PartialEq)]
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

#[derive(Clone)]
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

struct Parser {
    tokens: Vec<Token>,
    current: FileLocation,
}

impl Parser {
    fn new(tokens: Vec<Token>) -> Parser {
        Parser { current: 0, tokens }
    }

    fn parse(&mut self, lox: &mut Lox) -> Result<Expression, ()> {
        match self.expression(lox) {
            Ok(e) => Ok(e),
            // Book does `return null` here and says we will revisit
            // When we revisit we'll update this branch
            Err(e) => Err(()),
        }
    }

    fn synchronize(&mut self) -> () {
        self.advance();

        while !self.is_at_end() {
            if self.previous().token_type == TokenType::Semicolon {
                break;
            }

            let found = match self.peek().token_type {
                TokenType::Class => true,
                TokenType::Fun => true,
                TokenType::Var => true,
                TokenType::For => true,
                TokenType::If => true,
                TokenType::While => true,
                TokenType::Print => true,
                TokenType::Return => true,
                _ => false,
            };

            if found {
                break;
            } else {
                self.advance();
            }
        }
    }

    fn expression(&mut self, lox: &mut Lox) -> Result<Expression, ParseError> {
        self.equality(lox)
    }

    fn equality(&mut self, lox: &mut Lox) -> Result<Expression, ParseError> {
        let mut expr = self.comparison(lox)?;

        while self.match_tokens(vec![TokenType::BangEqual, TokenType::EqualEqual]) {
            let operator = self.previous();
            let right = self.comparison(lox)?;
            expr = Expression::binary(expr, operator, right);
        }

        Ok(expr)
    }

    fn comparison(&mut self, lox: &mut Lox) -> Result<Expression, ParseError> {
        let mut expr = self.terminal(lox)?;

        while self.match_tokens(vec![
            TokenType::Greater,
            TokenType::GreaterEqual,
            TokenType::Less,
            TokenType::LessEqual,
        ]) {
            let operator = self.previous();
            let right = self.terminal(lox)?;
            expr = Expression::binary(expr, operator, right);
        }

        Ok(expr)
    }

    fn terminal(&mut self, lox: &mut Lox) -> Result<Expression, ParseError> {
        let mut expr = self.factor(lox)?;

        while self.match_tokens(vec![TokenType::Minus, TokenType::Plus]) {
            let operator = self.previous();
            let right = self.factor(lox)?;
            expr = Expression::binary(expr, operator, right);
        }

        Ok(expr)
    }

    fn factor(&mut self, lox: &mut Lox) -> Result<Expression, ParseError> {
        let mut expr = self.unary(lox)?;

        while self.match_tokens(vec![TokenType::Star, TokenType::Slash]) {
            let operator = self.previous();
            let right = self.unary(lox)?;
            expr = Expression::binary(expr, operator, right);
        }

        Ok(expr)
    }

    fn unary(&mut self, lox: &mut Lox) -> Result<Expression, ParseError> {
        if self.match_tokens(vec![TokenType::Bang, TokenType::Minus]) {
            let operator = self.previous();
            let right = self.unary(lox)?;
            Ok(Expression::unary(operator, right))
        } else {
            self.primary(lox)
        }
    }

    fn primary(&mut self, lox: &mut Lox) -> Result<Expression, ParseError> {
        if self.match_token(TokenType::False) {
            Ok(Expression::literal(Literal::Boolean(false)))
        } else if self.match_token(TokenType::True) {
            Ok(Expression::literal(Literal::Boolean(true)))
        } else if self.match_tokens(vec![
            TokenType::Nil,
            TokenType::Number,
            TokenType::LoxString,
        ]) {
            Ok(Expression::literal(self.previous().literal))
        } else if self.match_token(TokenType::LeftParen) {
            let expr = self.expression(lox)?;
            self.consume(TokenType::RightParen, "Expect ')' after expression")?;
            Ok(Expression::grouping(expr))
        } else {
            let cause = self.peek();
            let message = "Expected expression";
            lox.parse_error(cause.clone(), message);
            Err(ParseError {
                message: String::from(message),
                cause,
            })
        }
    }

    fn consume(&mut self, token_type: TokenType, message: &str) -> Result<Token, ParseError> {
        if self.check(token_type) {
            Ok(self.advance())
        } else {
            Err(ParseError {
                cause: self.peek(),
                message: String::from(message),
            })
        }
    }

    fn match_tokens(&mut self, tokens: Vec<TokenType>) -> bool {
        let mut tokens = tokens.into_iter();
        while let Some(next) = tokens.next() {
            if self.match_token(next) {
                return true;
            }
        }

        false
    }

    fn match_token(&mut self, token: TokenType) -> bool {
        if self.check(token) {
            self.advance();
            true
        } else {
            false
        }
    }

    fn check(&self, token_type: TokenType) -> bool {
        if self.is_at_end() {
            false
        } else {
            self.peek().token_type == token_type
        }
    }

    fn advance(&mut self) -> Token {
        if !self.is_at_end() {
            self.current += 1;
        }

        self.previous()
    }

    fn previous(&self) -> Token {
        // TODO: need an invariant that we will not call this until advancing at least once, would panic
        self.tokens[self.current - 1].clone()
    }

    fn peek(&self) -> Token {
        // TODO: is it an invariant that we will always stop advancing at the end?
        self.tokens[self.current].clone()
    }

    fn is_at_end(&self) -> bool {
        self.peek().token_type == TokenType::Eof
    }
}

struct ParseError {
    cause: Token,
    message: String,
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
#[derive(Clone)]
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

    fn unbox(expr: Box<Expression>) -> Expression {
        match *expr {
            Expression::Binary(left, token, right) => Expression::Binary(left, token, right),
            Expression::Unary(token, expr) => Expression::Unary(token, expr),
            Expression::Literal(lit) => Expression::Literal(lit),
            Expression::Grouping(expr) => Expression::Grouping(expr),
        }
    }
}

trait AstPrinter {
    fn print(&self) -> String;
}

/*
The Interpreter consumes the expression completely because it pulls the
components out to evaluate them. If you need to re-use the whole
expression, you should clone it first.
*/
trait Interpreter {
    fn interpret(self) -> Result<LoxObject, LoxError>;
}

impl AstPrinter for Expression {
    fn print(&self) -> String {
        match self {
            Expression::Binary(l, t, r) => format!("({} {} {})", t.lexeme, l.print(), r.print()),
            Expression::Grouping(e) => format!("{}", e.print()),
            Expression::Literal(l) => l.repr(),
            Expression::Unary(t, e) => format!("({} {})", t.lexeme, e.print()),
        }
    }
}

impl Interpreter for Expression {
    fn interpret(self) -> Result<LoxObject, LoxError> {
        match self {
            Expression::Grouping(expr) => expr.interpret(),
            Expression::Literal(lit) => match lit {
                Literal::Boolean(b) => Ok(LoxObject::Boolean(b)),
                Literal::String(s) => Ok(LoxObject::String(s)),
                Literal::Number(n) => Ok(LoxObject::Number(n)),
                Literal::None => Ok(LoxObject::Nil),
            },
            Expression::Unary(op, value) => {
                let value = Expression::unbox(value);
                let obj = value.clone().interpret()?;
                match op.token_type {
                    TokenType::Minus => {
                        if let LoxObject::Number(n) = obj {
                            Ok(LoxObject::Number(-n))
                        } else {
                            Err(LoxError {
                                cause: value,
                                message: format!(
                                    "cannot negate {} — expected Number, found {}",
                                    obj.print(),
                                    obj.get_type()
                                ),
                                err_type: LoxErrorType::TypeError,
                            })
                        }
                    },
                    TokenType::Bang => {
                        if let LoxObject::Boolean(b) = obj {
                            Ok(LoxObject::Boolean(!b))
                        } else {
                            Err(LoxError {
                                cause: value,
                                message: format!(
                                    "cannot take logical inverse of {} — expected Boolean, found {}",
                                    obj.print(),
                                    obj.get_type()
                                ),
                                err_type: LoxErrorType::TypeError,
                            })
                        }
                    },
                    _ => Err(LoxError {
                        cause: value,
                        message: format!("'{:?}'", op.token_type),
                        err_type: LoxErrorType::UnknownOperator,
                    }),
                }
            }
            Expression::Binary(left, op, right) => panic!("unimplemented"),
        }
    }
}

enum LoxErrorType {
    TypeError,
    UnknownOperator,
}

struct LoxError {
    cause: Expression,
    message: String,
    err_type: LoxErrorType,
}

enum LoxObject {
    Boolean(bool),
    String(String),
    Number(f64),
    Object(HashMap<String, Box<LoxObject>>),
    Nil,
}

impl LoxObject {
    fn print(&self) -> String {
        match self {
            LoxObject::Boolean(b) => format!("{}", b),
            LoxObject::String(s) => s.clone(),
            LoxObject::Number(n) => format!("{}", n),
            LoxObject::Object(o) => String::from("<Object>"),
            LoxObject::Nil => String::from("nil"),
        }
    }

    fn get_type(&self) -> String {
        let s = match self {
            LoxObject::Boolean(_) => "Boolean",
            LoxObject::String(_) => "String",
            LoxObject::Number(_) => "Number",
            LoxObject::Object(_) => "Object",
            LoxObject::Nil => "Nil",
        };

        String::from(s)
    }
}
