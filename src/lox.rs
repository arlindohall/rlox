// Ignore while building
#![ allow( dead_code, unused_imports, unused_variables, unused_must_use ) ]

extern crate unicode_segmentation;

use std::cmp::PartialEq;
use std::collections::HashMap;
use std::str::FromStr;

use unicode_segmentation::UnicodeSegmentation;

type LineNumber = u16; // 64K lines
type FileLocation = usize; // 4G chars
type LoxNumberLiteral = f64; // Numbers are floats, can be improved

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
}

pub struct Lox {
    pub had_error: bool,
    pub had_runtime_error: bool,
    reserved_words: HashMap<String, TokenType>,
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

        for statement in statements {
            statement.interpret(self);
        }

        Ok(())
    }
}

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
#[derive(Debug, Clone)]
pub enum Literal {
    Boolean(bool),
    String(String),
    Number(LoxNumberLiteral),
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

#[derive(Debug, Clone)]
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

    pub fn scan_tokens(&mut self, lox: &mut Lox) -> Result<Vec<Token>, LoxError> {
        let mut tokens = Vec::new();
        while !self.is_at_end() {
            self.start = self.next;
            let result = self.scan_token(lox);

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
    fn scan_token(&mut self, lox: &mut Lox) -> ScanResult {
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
            "\"" => self.string(lox),
            _ => {
                // Borrow c again as immutable to avoid reference error
                let c = self.prev();
                if self.is_digit(&c) {
                    self.number(lox)
                } else if self.is_alpha(&c) {
                    self.identifier(lox)
                } else {
                    let message = format!("unexpected character '{}' at [col={}]", c, self.col);
                    let err =
                        lox.scan_error(self.line, LoxErrorType::UnexpectedCharacter, &message);
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

    fn string(&mut self, lox: &mut Lox) -> Token {
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
            lox.scan_error(
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

/*******************************************************************************
********************************************************************************
                                PARSER
********************************************************************************

This section contains the second logical division of interpreter logic. It
receives a flat vector of tokens which we can then build into expressions and
statement data structures which can be directly interpreted.

*******************************************************************************/

/*
This section of the code corresponds to the section of the book that uses
metaprogramming and the visitor pattern to easily create Java classes to
represent nested expressions. The thing is, in my opinion, Rust is usable
enough for this kind of task that I feel fine creating this code by hand. I
might revisit this using metaprogramming or macros later when I feel better
about Rust 🙂

The ultimate goal here is to show how you can implement N behaviors for each
of M data types, but with Rust that's just `impl`.

So, for example, the book says to create an `AstPrinter` class which
implements visitors for each type, binary/grouping/literal/ unary, which each
in turn produce a string. This is logically equivalent to `ExpressionPrinter`
trait which each expression implements.
*/
#[derive(Debug, Clone)]
pub enum Expression {
    Binary(Box<Expression>, Token, Box<Expression>),
    Grouping(Box<Expression>),
    Literal(Literal),
    Unary(Token, Box<Expression>),
    Variable(Token),
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
            Expression::Variable(var) => Expression::Variable(var),
        }
    }

    fn is_truthy(obj: LoxObject) -> bool {
        match obj {
            LoxObject::Nil => false,
            LoxObject::Boolean(b) => b,
            _ => true,
        }
    }

    fn apply_compare(
        self,
        lox: &mut Lox,
        op: TokenType,
        left: LoxObject,
        right: LoxObject,
    ) -> Result<LoxObject, LoxError> {
        if let (LoxObject::Number(l), LoxObject::Number(r)) = (left, right) {
            let result = match op {
                TokenType::Greater => Ok(l > r),
                TokenType::GreaterEqual => Ok(l >= r),
                TokenType::Less => Ok(l < r),
                TokenType::LessEqual => Ok(l <= r),
                _ => Err(lox.runtime_error(
                    self,
                    LoxErrorType::UnknownOperator,
                    &format!("unable to apply {:?} as a comparison operator", op),
                )),
            };
            result.map(|b| LoxObject::Boolean(b))
        } else {
            Err(lox.runtime_error(
                self,
                LoxErrorType::TypeError,
                &format!("cannot apply operation {:?} to non-numeric types", op),
            ))
        }
    }
}

enum Statement {
    Print(Expression),
    Expression(Expression),
    Var(Token, Option<Expression>),
    None,
}

struct Parser {
    tokens: Vec<Token>,
    current: FileLocation,
}

impl Parser {
    fn new(tokens: Vec<Token>) -> Parser {
        Parser { current: 0, tokens }
    }

    fn parse(&mut self, lox: &mut Lox) -> Result<Vec<Statement>, LoxError> {
        let mut statements = Vec::new();
        while !self.is_at_end() {
            statements.push(self.declaration(lox)?)
        }

        Ok(statements)
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

    fn declaration(&mut self, lox: &mut Lox) -> Result<Statement, LoxError> {
        let declr = if self.match_token(TokenType::Var) {
            self.var_declaration(lox)
        } else {
            self.statement(lox)
        };

        match declr {
            Ok(s) => Ok(s),
            Err(e) => {
                self.synchronize();
                Err(e)
            },
        }
    }

    fn var_declaration(&mut self, lox: &mut Lox) -> Result<Statement, LoxError> {
        let name = self.consume(lox, TokenType::Identifier, "Expect variable name.")?;

        let initializer = if self.match_token(TokenType::Equal) {
            Some(self.expression(lox)?)
        } else {
            None
        };

        Ok(Statement::Var(name, initializer))
    }

    fn handle_declaration_err(&mut self, result: Result<Statement, LoxError>) -> Result<Statement, LoxError> {
        match result {
            Ok(stmt) => Ok(stmt),
            Err(err) => {
                self.synchronize();
                Ok(Statement::None)
            }
        }
    }

    fn statement(&mut self, lox: &mut Lox) -> Result<Statement, LoxError> {
        if self.match_token(TokenType::Print) {
            return Ok(self.print_statement(lox)?);
        }

        Ok(self.expression_statement(lox)?)
    }

    fn print_statement(&mut self, lox: &mut Lox) -> Result<Statement, LoxError> {
        let value = self.expression(lox)?;
        self.consume(lox, TokenType::Semicolon, "expect ';' after value");
        Ok(Statement::Print(value))
    }

    fn expression_statement(&mut self, lox: &mut Lox) -> Result<Statement, LoxError> {
        let expr = self.expression(lox)?;
        self.consume(lox, TokenType::Semicolon, "expect ';' after statement");
        Ok(Statement::Expression(expr))
    }

    fn expression(&mut self, lox: &mut Lox) -> Result<Expression, LoxError> {
        self.equality(lox)
    }

    fn equality(&mut self, lox: &mut Lox) -> Result<Expression, LoxError> {
        let mut expr = self.comparison(lox)?;

        while self.match_tokens(vec![TokenType::BangEqual, TokenType::EqualEqual]) {
            let operator = self.previous();
            let right = self.comparison(lox)?;
            expr = Expression::binary(expr, operator, right);
        }

        Ok(expr)
    }

    fn comparison(&mut self, lox: &mut Lox) -> Result<Expression, LoxError> {
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

    fn terminal(&mut self, lox: &mut Lox) -> Result<Expression, LoxError> {
        let mut expr = self.factor(lox)?;

        while self.match_tokens(vec![TokenType::Minus, TokenType::Plus]) {
            let operator = self.previous();
            let right = self.factor(lox)?;
            expr = Expression::binary(expr, operator, right);
        }

        Ok(expr)
    }

    fn factor(&mut self, lox: &mut Lox) -> Result<Expression, LoxError> {
        let mut expr = self.unary(lox)?;

        while self.match_tokens(vec![TokenType::Star, TokenType::Slash]) {
            let operator = self.previous();
            let right = self.unary(lox)?;
            expr = Expression::binary(expr, operator, right);
        }

        Ok(expr)
    }

    fn unary(&mut self, lox: &mut Lox) -> Result<Expression, LoxError> {
        if self.match_tokens(vec![TokenType::Bang, TokenType::Minus]) {
            let operator = self.previous();
            let right = self.unary(lox)?;
            Ok(Expression::unary(operator, right))
        } else {
            self.primary(lox)
        }
    }

    fn primary(&mut self, lox: &mut Lox) -> Result<Expression, LoxError> {
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
        } else if self.match_token(TokenType::Identifier) {
            Ok(Expression::Variable(self.previous()))
        } else if self.match_token(TokenType::LeftParen) {
            let expr = self.expression(lox)?;
            self.consume(lox, TokenType::RightParen, "Expect ')' after expression")?;
            Ok(Expression::grouping(expr))
        } else {
            let cause = self.peek();
            let message = "expected expression";
            Err(lox.parse_error(cause, LoxErrorType::ExpressionError, message))
        }
    }

    fn consume(
        &mut self,
        lox: &mut Lox,
        token_type: TokenType,
        message: &str,
    ) -> Result<Token, LoxError> {
        if self.check(token_type) {
            Ok(self.advance())
        } else {
            Err(lox.parse_error(self.peek(), LoxErrorType::IncompleteExpression, message))
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
        // TODO: need an invariant that we will not call this until advancing at
        // least once, would panic
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

/*******************************************************************************
********************************************************************************
                                INTERPRETER
********************************************************************************

This is the final division of the interpreter, which does the actual
interpreting of expressions. In the book this is done using a visitor pattern
because the initial implementation is done in Java. However, since I've used
Rust, some functional approaches make more sense, and so I've used the
pattern the book describes as "too hard to maintain for large code bases,"
and I just sort of am resolved to having to refactor in the future if I ever
change that.

It's not a huge deal since this is a side project, but in my opinion, this
way of doing things is easier to understand for the Lox language, while the
visitor pattern splits all the behavior necessary to the language up into
different files and classes when it really ought to live next to the trait or
struct (or in Java the class) where it is actually used.

The interpreter's job is to produce a value for each expression.

*******************************************************************************/

trait AstPrinter {
    fn to_string(&self) -> String;
}

/*
The Interpreter consumes the expression completely because it pulls the
components out to evaluate them. If you need to re-use the whole expression,
you should clone it first.
*/
trait Interpreter {
    fn interpret(self, lox: &mut Lox) -> Result<LoxObject, LoxError>;
}

#[derive(PartialEq)]
enum LoxObject {
    Boolean(bool),
    String(String),
    Number(LoxNumberLiteral),
    Object(HashMap<String, Box<LoxObject>>),
    Nil,
}

impl LoxObject {
    fn to_string(&self) -> String {
        match self {
            LoxObject::Boolean(b) => format!("{}", b),
            LoxObject::String(s) => s.clone(),
            LoxObject::Number(n) => format!("{}", n),
            // TODO: maybe actually print objects
            LoxObject::Object(_) => String::from("<Object>"),
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

impl AstPrinter for Expression {
    fn to_string(&self) -> String {
        match self {
            Expression::Binary(l, t, r) => {
                format!("({} {} {})", t.lexeme, l.to_string(), r.to_string())
            }
            Expression::Grouping(e) => format!("{}", e.to_string()),
            Expression::Literal(l) => l.repr(),
            Expression::Unary(t, e) => format!("({} {})", t.lexeme, e.to_string()),
            Expression::Variable(t) => format!("{}", t.lexeme)
        }
    }
}

impl Interpreter for Expression {
    fn interpret(self, lox: &mut Lox) -> Result<LoxObject, LoxError> {
        match self.clone() {
            Expression::Grouping(expr) => expr.interpret(lox),
            Expression::Literal(lit) => match lit {
                Literal::Boolean(b) => Ok(LoxObject::Boolean(b)),
                Literal::String(s) => Ok(LoxObject::String(s)),
                Literal::Number(n) => Ok(LoxObject::Number(n)),
                Literal::None => Ok(LoxObject::Nil),
            },
            Expression::Unary(op, value) => {
                let value = Expression::unbox(value);
                let obj = value.clone().interpret(lox)?;
                match op.token_type {
                    TokenType::Minus => {
                        if let LoxObject::Number(n) = obj {
                            Ok(LoxObject::Number(-n))
                        } else {
                            Err(lox.runtime_error(
                                self,
                                LoxErrorType::TypeError,
                                &format!(
                                    "cannot negate `{}` — expected Number, found {}",
                                    obj.to_string(),
                                    obj.get_type()
                                ),
                            ))
                        }
                    }
                    TokenType::Bang => {
                        if Self::is_truthy(obj) {
                            Ok(LoxObject::Boolean(false))
                        } else {
                            Ok(LoxObject::Boolean(true))
                        }
                    }
                    _ => Err(lox.runtime_error(
                        self,
                        LoxErrorType::UnknownOperator,
                        &format!("'{:?}'", op.token_type),
                    )),
                }
            }
            Expression::Binary(left, op, right) => {
                let rval = Expression::unbox(right);
                let lval = Expression::unbox(left);

                let robj = rval.clone().interpret(lox)?;
                let lobj = lval.clone().interpret(lox)?;

                match op.token_type {
                    TokenType::Minus => match (lobj, robj) {
                        (LoxObject::Number(l), LoxObject::Number(r)) => {
                            Ok(LoxObject::Number(l - r))
                        }
                        _ => Err(lox.runtime_error(
                            self,
                            LoxErrorType::TypeError,
                            "cannot subtract non-numbers",
                        )),
                    },
                    TokenType::Slash => match (lobj, robj) {
                        (LoxObject::Number(l), LoxObject::Number(r)) => {
                            if r == 0.0 {
                                Err(lox.runtime_error(
                                    self,
                                    LoxErrorType::DivideByZeroError,
                                    "divide by zero",
                                ))
                            } else {
                                Ok(LoxObject::Number(l / r))
                            }
                        }
                        _ => Err(lox.runtime_error(
                            self,
                            LoxErrorType::TypeError,
                            "cannot divide non-numbers",
                        )),
                    },
                    TokenType::Star => match (lobj, robj) {
                        (LoxObject::Number(l), LoxObject::Number(r)) => {
                            Ok(LoxObject::Number(l * r))
                        }
                        _ => Err(lox.runtime_error(
                            self,
                            LoxErrorType::TypeError,
                            "cannot multiply non-numbers",
                        )),
                    },
                    TokenType::Plus => match (lobj, robj) {
                        (LoxObject::Number(l), LoxObject::Number(r)) => {
                            Ok(LoxObject::Number(l + r))
                        }
                        (LoxObject::String(l), LoxObject::String(r)) => {
                            Ok(LoxObject::String(l.clone() + &r))
                        }
                        _ => Err(lox.runtime_error(
                            self,
                            LoxErrorType::TypeError,
                            "addition is defined for numbers and strings",
                        )),
                    },
                    TokenType::Greater
                    | TokenType::GreaterEqual
                    | TokenType::Less
                    | TokenType::LessEqual => self.apply_compare(lox, op.token_type, lobj, robj),
                    TokenType::EqualEqual => Ok(LoxObject::Boolean(lobj == robj)),
                    TokenType::BangEqual => Ok(LoxObject::Boolean(lobj != robj)),
                    _ => panic!("unimplemented binary operator"),
                }
            },
            Expression::Variable(_) => todo!(),
        }
    }
}

impl Interpreter for Statement {
    fn interpret(self, lox: &mut Lox) -> Result<LoxObject, LoxError> {
        match self {
            Statement::Print(expr) => {
                let obj = expr.interpret(lox)?;
                println!("{}", obj.to_string());
                Ok(obj)
            }
            Statement::Expression(expr) => expr.interpret(lox),
            Statement::Var(token, expr) => todo!(),
            _ => todo!(),
        }
    }
}
