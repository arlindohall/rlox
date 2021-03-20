// Ignore while building
#![ allow( dead_code, unused_imports, unused_variables, unused_must_use ) ]

use std::collections::HashMap;

use crate::lox::{FileLocation, Lox, LoxError, LoxErrorType, LoxNumber};
use crate::scanner::{Literal, Token, TokenType};

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
// TODO make these struct-style enums since I already wrote wrapper methods
#[derive(Debug, Clone)]
pub enum Expression {
    Assignment(Token, Box<Expression>),
    Binary(Box<Expression>, Token, Box<Expression>),
    Grouping(Box<Expression>),
    Literal(LoxObject),
    Unary(Token, Box<Expression>),
    Variable(Token),
}

impl Expression {
    fn assignment(name: Token, value: Expression) -> Expression {
        Expression::Assignment(name, Box::new(value))
    }

    fn binary(l: Expression, t: Token, r: Expression) -> Expression {
        Expression::Binary(Box::new(l), t, Box::new(r))
    }

    fn grouping(e: Expression) -> Expression {
        Expression::Grouping(Box::new(e))
    }

    fn literal(l: LoxObject) -> Expression {
        Expression::Literal(l)
    }

    fn unary(t: Token, e: Expression) -> Expression {
        Expression::Unary(t, Box::new(e))
    }

    pub fn is_truthy(obj: LoxObject) -> bool {
        match obj {
            LoxObject::Nil => false,
            LoxObject::Boolean(b) => b,
            _ => true,
        }
    }

    pub fn apply_compare(
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
#[derive(Debug, Clone, PartialEq)]
pub enum LoxObject {
    Boolean(bool),
    String(String),
    Number(LoxNumber),
    Object(HashMap<String, Box<LoxObject>>),
    Nil,
}

impl LoxObject {
    pub fn to_string(&self) -> String {
        match self {
            LoxObject::Boolean(b) => format!("{}", b),
            LoxObject::String(s) => s.clone(),
            LoxObject::Number(n) => format!("{}", n),
            // TODO: maybe actually print objects
            LoxObject::Object(_) => String::from("<Object>"),
            LoxObject::Nil => String::from("nil"),
        }
    }

    pub fn get_type(&self) -> String {
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

pub enum Statement {
    Print(Expression),
    Expression(Expression),
    Var(Token, Option<Expression>),
    None,
}

pub struct Parser {
    tokens: Vec<Token>,
    current: FileLocation,
}

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Parser {
        Parser { current: 0, tokens }
    }

    pub fn parse(&mut self, lox: &mut Lox) -> Result<Vec<Statement>, LoxError> {
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
            }
        }
    }

    fn var_declaration(&mut self, lox: &mut Lox) -> Result<Statement, LoxError> {
        let name = self.consume(lox, TokenType::Identifier, "expect variable name.")?;

        let initializer = if self.match_token(TokenType::Equal) {
            Some(self.expression(lox)?)
        } else {
            None
        };

        self.consume(
            lox,
            TokenType::Semicolon,
            "expected semicolon after variable declaration",
        );
        Ok(Statement::Var(name, initializer))
    }

    fn handle_declaration_err(
        &mut self,
        result: Result<Statement, LoxError>,
    ) -> Result<Statement, LoxError> {
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
        self.assignment(lox)
    }

    fn assignment(&mut self, lox: &mut Lox) -> Result<Expression, LoxError> {
        let expr = self.equality(lox);

        // If this is an assignment, parse the RHS as a normal expression
        if self.match_token(TokenType::Equal) {
            let equals = self.previous();
            let value = self.assignment(lox)?;

            // If the left hand side is a valid assignment target, make the assignment
            // According to the book, we'll revisit this
            if let Ok(Expression::Variable(token)) = expr {
                return Ok(Expression::assignment(token, value));
            } else {
                // If it's not valid, report and continue
                lox.runtime_error(
                    value,
                    LoxErrorType::AssignmentError,
                    "invalid assignment target",
                );
            }
        }

        // If it turned out not to be an assignment or was invalid, return the
        // LHS as an expression only
        expr
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
            Ok(Expression::literal(LoxObject::Boolean(false)))
        } else if self.match_token(TokenType::True) {
            Ok(Expression::literal(LoxObject::Boolean(true)))
        } else if self.match_token(TokenType::Nil) {
            Ok(Expression::literal(LoxObject::Nil))
        } else if self.match_token(TokenType::Number) {
            Ok(Expression::literal(LoxObject::Number(
                self.previous().literal.get_number().unwrap(),
            )))
        } else if self.match_token(TokenType::LoxString) {
            Ok(Expression::literal(LoxObject::String(
                self.previous().literal.get_string().unwrap(),
            )))
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
