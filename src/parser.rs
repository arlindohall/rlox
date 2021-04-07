use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::{
    interpreter::LoxCallable,
    lox::{FileLocation, LoxError, LoxErrorType, LoxNumber},
};
use crate::{
    interpreter::ObjectRef,
    scanner::{Token, TokenType},
};
use uuid::Uuid;

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

// Hey, dummy, start working here when you start again. This is where you
// need to create expression IDs for each expression that can be used as a
// hash for the side table. The ID needs to be created with the expression
// in the parser, and then it can be used to track the expression throughout
// the program. Also, you can get rid of the hashes for all the other types.
#[derive(Debug, Clone, PartialEq)]
pub enum Expression {
    Assignment(ExpressionId, Token, Box<Expression>),
    Binary(Box<Expression>, Token, Box<Expression>),
    Grouping(Box<Expression>),
    Literal(ObjectRef),
    Logical(Box<Expression>, Token, Box<Expression>),
    Unary(Token, Box<Expression>),
    Call(Box<Expression>, Token, Vec<Expression>),
    Set(Box<Expression>, Token, Box<Expression>),
    Get(Box<Expression>, Token),
    Variable(ExpressionId, Token),
}

pub type ExpressionId = u128;

impl Expression {
    fn assignment(name: Token, value: Expression) -> Expression {
        Expression::Assignment(Uuid::new_v4().as_u128(), name, Box::new(value))
    }

    fn binary(l: Expression, t: Token, r: Expression) -> Expression {
        Expression::Binary(Box::new(l), t, Box::new(r))
    }

    fn grouping(e: Expression) -> Expression {
        Expression::Grouping(Box::new(e))
    }

    fn literal(l: ObjectRef) -> Expression {
        Expression::Literal(l)
    }

    fn logical(l: Expression, op: Token, r: Expression) -> Expression {
        Expression::Logical(Box::new(l), op, Box::new(r))
    }

    fn unary(t: Token, e: Expression) -> Expression {
        Expression::Unary(t, Box::new(e))
    }

    fn variable(t: Token) -> Expression {
        Expression::Variable(Uuid::new_v4().as_u128(), t)
    }

    fn call(callee: Expression, paren: Token, params: Vec<Expression>) -> Expression {
        Expression::Call(Box::new(callee), paren, params)
    }

    fn get(object: Expression, name: Token) -> Expression {
        Expression::Get(Box::new(object), name)
    }

    fn set(object: Expression, name: Token, value: Expression) -> Expression {
        Expression::Set(Box::new(object), name, Box::new(value))
    }

    pub fn get_id(&self) -> ExpressionId {
        match self {
            Expression::Variable(id, _) | Expression::Assignment(id, _, _) => *id,
            _ => panic!(format!(
                "Unrecoverable lox error to get expression id for expression {:?}",
                self
            )),
        }
    }

    pub fn is_truthy(obj: ObjectRef) -> bool {
        match *obj.borrow() {
            LoxObject::Nil => false,
            LoxObject::Boolean(b) => b.clone(),
            _ => true,
        }
    }

    pub fn apply_compare(
        self,
        op: TokenType,
        left: ObjectRef,
        right: ObjectRef,
    ) -> Result<LoxObject, LoxError> {
        if let (LoxObject::Number(l), LoxObject::Number(r)) = (&*left.borrow(), &*right.borrow()) {
            let result = match op {
                TokenType::Greater => Ok(l > r),
                TokenType::GreaterEqual => Ok(l >= r),
                TokenType::Less => Ok(l < r),
                TokenType::LessEqual => Ok(l <= r),
                _ => Err(crate::lox::runtime_error(
                    self,
                    LoxErrorType::UnknownOperator,
                    &format!("unable to apply {:?} as a comparison operator", op),
                )),
            };
            result.map(|b| LoxObject::Boolean(b))
        } else {
            Err(crate::lox::runtime_error(
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
    Class(LoxClass),
    Object(LoxClass, ObjectValues),
    Function(LoxCallable),
    Nil,
}

type ObjectValues = HashMap<String, ObjectRef>;

#[derive(Debug, Clone, PartialEq)]
pub struct LoxClass {
    pub name: String,
    pub methods: HashMap<String, ObjectRef>,
}

impl LoxClass {
    fn find_method(&self, name: &str) -> Option<ObjectRef> {
        self.methods.get(name).map(|m| m.clone())
    }
}

impl LoxObject {
    pub fn to_string(&self) -> String {
        match self {
            LoxObject::Boolean(b) => format!("{}", b),
            LoxObject::String(s) => s.clone(),
            LoxObject::Number(n) => format!("{}", n),
            // TODO: maybe actually print objects
            LoxObject::Function(callable) => callable.to_string(),
            LoxObject::Class(class) => class.name.clone(),
            LoxObject::Object(class, _) => format!("<{}>", class.name),
            LoxObject::Nil => String::from("nil"),
        }
    }

    pub fn get_type(&self) -> String {
        let s = match self {
            LoxObject::Boolean(_) => "Boolean",
            LoxObject::String(_) => "String",
            LoxObject::Number(_) => "Number",
            LoxObject::Function(_) => "Function",
            LoxObject::Class(_) => "Class",
            LoxObject::Object(_, _) => "Object", // TODO: maybe this should be instances to match the text
            LoxObject::Nil => "Nil",
        };

        String::from(s)
    }

    pub fn wrap(self) -> ObjectRef {
        Rc::new(RefCell::new(self))
    }

    pub fn set(&mut self, name: String, value: ObjectRef) {
        match self {
            LoxObject::Object(_, fields) => {
                fields.insert(name, value);
            }
            _ => panic!(format!("cannot set property on {}", self.get_type())),
        }
    }

    pub fn get(&self, expression: Expression, name: &str) -> Result<ObjectRef, LoxError> {
        if let LoxObject::Object(class, fields) = self {
            if let Some(field) = fields.get(name) {
                return Ok(field.clone());
            } else if let Some(method) = class.find_method(name) {
                return Ok(method.clone());
            }
        }
        Err(crate::lox::runtime_error(
            expression,
            LoxErrorType::PropertyError,
            &format!("undefined property {}", name),
        ))
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Statement {
    Print(Expression),
    Expression(Expression),
    Block(Vec<Statement>),
    Class(Token, Vec<FunctionDefinition>),
    Var(Token, Option<Expression>),
    If(Expression, Box<Statement>, Option<Box<Statement>>),
    Function(FunctionDefinition),
    While(Expression, Box<Statement>),
    Return(Token, Expression),
    None,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunctionDefinition {
    pub name: Token,
    pub params: Vec<Token>,
    pub body: Vec<Statement>,
}

pub struct Parser {
    tokens: Vec<Token>,
    current: FileLocation,
}

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Parser {
        Parser { current: 0, tokens }
    }

    pub fn parse(&mut self) -> Result<Vec<Statement>, LoxError> {
        let mut statements = Vec::new();
        while !self.is_at_end() {
            statements.push(self.declaration()?)
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

    fn declaration(&mut self) -> Result<Statement, LoxError> {
        let declr = if self.match_token(TokenType::Class) {
            self.class_declaration()
        } else if self.match_token(TokenType::Fun) {
            self.function("function")
        } else if self.match_token(TokenType::Var) {
            self.var_declaration()
        } else {
            self.statement()
        };

        match declr {
            Ok(s) => Ok(s),
            Err(e) => {
                self.synchronize();
                Err(e)
            }
        }
    }

    fn class_declaration(&mut self) -> Result<Statement, LoxError> {
        let name = self.consume(TokenType::Identifier, "expect class name")?;
        self.consume(TokenType::LeftBrace, "expect '{' before class body")?;

        let mut methods = Vec::new();
        while !self.check(TokenType::RightBrace) && !self.is_at_end() {
            methods.push(self.function_definition("method")?);
        }

        self.consume(TokenType::RightBrace, "expect '}' after class body")?;
        Ok(Statement::Class(name, methods))
    }

    fn function(&mut self, kind: &str) -> Result<Statement, LoxError> {
        Ok(Statement::Function(self.function_definition(kind)?))
    }

    fn function_definition(&mut self, kind: &str) -> Result<FunctionDefinition, LoxError> {
        let name = self.consume(TokenType::Identifier, &format!("expect {} name", kind))?;
        self.consume(
            TokenType::LeftParen,
            &format!("expect '(' after {} name", kind),
        )?;
        let mut params = Vec::new();
        if !self.check(TokenType::RightParen) {
            loop {
                if params.len() >= 255 {
                    return Err(crate::lox::parse_error(
                        name,
                        LoxErrorType::DefinitionError,
                        &format!("{} cannot have more than 255 parameters", kind),
                    ));
                } else {
                    params.push(self.consume(TokenType::Identifier, "expected parameter name")?)
                }
                if !self.match_token(TokenType::Comma) {
                    break;
                }
            }
        }
        self.consume(
            TokenType::RightParen,
            &format!("expected ')' after {} parameters", kind),
        )?;

        self.consume(
            TokenType::LeftBrace,
            &format!("expect '{{' before {} body", kind),
        )?;
        let body = self.block()?;
        Ok(FunctionDefinition { name, params, body })
    }

    fn var_declaration(&mut self) -> Result<Statement, LoxError> {
        let name = self.consume(TokenType::Identifier, "expect variable name.")?;

        let initializer = if self.match_token(TokenType::Equal) {
            Some(self.expression()?)
        } else {
            None
        };

        self.consume(
            TokenType::Semicolon,
            "expected semicolon after variable declaration",
        )?;
        Ok(Statement::Var(name, initializer))
    }

    fn _handle_declaration_err(
        &mut self,
        result: Result<Statement, LoxError>,
    ) -> Result<Statement, LoxError> {
        match result {
            Ok(stmt) => Ok(stmt),
            Err(_err) => {
                self.synchronize();
                Ok(Statement::None)
            }
        }
    }

    fn statement(&mut self) -> Result<Statement, LoxError> {
        if self.match_token(TokenType::For) {
            self.for_statement()
        } else if self.match_token(TokenType::If) {
            self.if_statement()
        } else if self.match_token(TokenType::Print) {
            self.print_statement()
        } else if self.match_token(TokenType::Return) {
            self.return_statement()
        } else if self.match_token(TokenType::While) {
            self.while_statement()
        } else if self.match_token(TokenType::LeftBrace) {
            self.block().map(|statements| Statement::Block(statements))
        } else {
            self.expression_statement()
        }
    }

    fn for_statement(&mut self) -> Result<Statement, LoxError> {
        self.consume(TokenType::LeftParen, "expect '(' after 'for'")?;

        let initializer = if self.match_token(TokenType::Semicolon) {
            Statement::None
        } else if self.match_token(TokenType::Var) {
            self.var_declaration()?
        } else {
            self.expression_statement()?
        };

        let condition = if self.match_token(TokenType::Semicolon) {
            None
        } else {
            let cond = self.expression()?;
            self.consume(TokenType::Semicolon, "expect ';' after for condition")?;
            Some(cond)
        };

        let increment = if self.match_token(TokenType::RightParen) {
            None
        } else {
            let inc = self.expression()?;
            self.consume(
                TokenType::RightParen,
                "expect ')' after for increment clause",
            )?;
            Some(inc)
        };

        let mut body = self.statement()?;

        body = match increment {
            Some(inc) => Statement::Block(vec![body, Statement::Expression(inc)]),
            None => body,
        };

        body = match condition {
            Some(cond) => Statement::While(cond, Box::new(body)),
            None => Statement::While(
                Expression::Literal(LoxObject::Boolean(true).wrap()),
                Box::new(body),
            ),
        };

        body = match initializer {
            Statement::None => body,
            _ => Statement::Block(vec![initializer, body]),
        };

        Ok(body)
    }

    fn while_statement(&mut self) -> Result<Statement, LoxError> {
        self.consume(TokenType::LeftParen, "expect '(' after 'while'")?;
        let condition = self.expression()?;
        self.consume(TokenType::RightParen, "expect ')' after while condition")?;
        let body = self.statement()?;

        Ok(Statement::While(condition, Box::new(body)))
    }

    fn if_statement(&mut self) -> Result<Statement, LoxError> {
        self.consume(TokenType::LeftParen, "expect '(' after 'if'")?;
        let condition = self.expression()?;
        self.consume(TokenType::RightParen, "expect ')' after if condition")?;

        let then_statement = Box::new(self.statement()?);
        let else_statement = if self.match_token(TokenType::Else) {
            Some(Box::new(self.statement()?))
        } else {
            None
        };

        Ok(Statement::If(condition, then_statement, else_statement))
    }

    fn print_statement(&mut self) -> Result<Statement, LoxError> {
        let value = self.expression()?;
        self.consume(TokenType::Semicolon, "expect ';' after value")?;
        Ok(Statement::Print(value))
    }

    fn return_statement(&mut self) -> Result<Statement, LoxError> {
        let keyword = self.previous();
        let value = if self.check(TokenType::Semicolon) {
            Expression::Literal(LoxObject::Nil.wrap())
        } else {
            self.expression()?
        };

        self.consume(TokenType::Semicolon, "expect ';' after return statement")?;
        Ok(Statement::Return(keyword, value))
    }

    fn block(&mut self) -> Result<Vec<Statement>, LoxError> {
        let mut statements = Vec::new();

        while !self.check(TokenType::RightBrace) && !self.is_at_end() {
            statements.push(self.declaration()?);
        }

        self.consume(TokenType::RightBrace, "expect '}' after block")?;
        Ok(statements)
    }

    fn expression_statement(&mut self) -> Result<Statement, LoxError> {
        let expr = self.expression()?;
        self.consume(TokenType::Semicolon, "expect ';' after statement")?;
        Ok(Statement::Expression(expr))
    }

    fn expression(&mut self) -> Result<Expression, LoxError> {
        self.assignment()
    }

    fn assignment(&mut self) -> Result<Expression, LoxError> {
        let expr = self.or()?;

        // If this is an assignment, parse the RHS as a normal expression
        if self.match_token(TokenType::Equal) {
            let _equals = self.previous();
            let value = self.assignment()?;

            if let Expression::Variable(_, token) = expr {
                return Ok(Expression::assignment(token, value));
            } else if let Expression::Get(object, name) = expr {
                return Ok(Expression::set(*object, name, value));
            } else {
                // If it's not valid, report and continue
                crate::lox::runtime_error(
                    value,
                    LoxErrorType::AssignmentError,
                    "invalid assignment target",
                );
            }
        }

        // If it turned out not to be an assignment or was invalid, return the
        // LHS as an expression only
        Ok(expr)
    }

    fn or(&mut self) -> Result<Expression, LoxError> {
        let mut left = self.and()?;

        while self.match_token(TokenType::Or) {
            let op = self.previous();
            let right = self.and()?;
            left = Expression::logical(left, op, right);
        }

        Ok(left)
    }

    fn and(&mut self) -> Result<Expression, LoxError> {
        let mut left = self.equality()?;

        while self.match_token(TokenType::And) {
            let op = self.previous();
            let right = self.and()?;
            left = Expression::logical(left, op, right);
        }

        Ok(left)
    }

    fn equality(&mut self) -> Result<Expression, LoxError> {
        let mut expr = self.comparison()?;

        while self.match_tokens(vec![TokenType::BangEqual, TokenType::EqualEqual]) {
            let operator = self.previous();
            let right = self.comparison()?;
            expr = Expression::binary(expr, operator, right);
        }

        Ok(expr)
    }

    fn comparison(&mut self) -> Result<Expression, LoxError> {
        let mut expr = self.terminal()?;

        while self.match_tokens(vec![
            TokenType::Greater,
            TokenType::GreaterEqual,
            TokenType::Less,
            TokenType::LessEqual,
        ]) {
            let operator = self.previous();
            let right = self.terminal()?;
            expr = Expression::binary(expr, operator, right);
        }

        Ok(expr)
    }

    fn terminal(&mut self) -> Result<Expression, LoxError> {
        let mut expr = self.factor()?;

        while self.match_tokens(vec![TokenType::Minus, TokenType::Plus]) {
            let operator = self.previous();
            let right = self.factor()?;
            expr = Expression::binary(expr, operator, right);
        }

        Ok(expr)
    }

    fn factor(&mut self) -> Result<Expression, LoxError> {
        let mut expr = self.unary()?;

        while self.match_tokens(vec![TokenType::Star, TokenType::Slash]) {
            let operator = self.previous();
            let right = self.unary()?;
            expr = Expression::binary(expr, operator, right);
        }

        Ok(expr)
    }

    fn unary(&mut self) -> Result<Expression, LoxError> {
        if self.match_tokens(vec![TokenType::Bang, TokenType::Minus]) {
            let operator = self.previous();
            let right = self.unary()?;
            Ok(Expression::unary(operator, right))
        } else {
            self.call()
        }
    }

    fn call(&mut self) -> Result<Expression, LoxError> {
        let mut expr = self.primary()?;

        loop {
            if self.match_token(TokenType::LeftParen) {
                expr = self.finish_call(expr)?;
            } else if self.match_token(TokenType::Dot) {
                let name = self.consume(TokenType::Identifier, "expect property name after '.'")?;
                expr = Expression::get(expr, name);
            } else {
                break;
            }
        }

        Ok(expr)
    }

    fn finish_call(&mut self, expr: Expression) -> Result<Expression, LoxError> {
        let mut arguments = Vec::new();

        if !self.check(TokenType::RightParen) {
            loop {
                if arguments.len() >= 255 {
                    return Err(crate::lox::runtime_error(
                        expr,
                        LoxErrorType::FunctionCallError,
                        "can't have more than 255 arguments",
                    ));
                } else {
                    arguments.push(self.expression()?);
                }
                if !self.match_token(TokenType::Comma) {
                    break;
                }
            }
        }

        let paren = self.consume(
            TokenType::RightParen,
            "expect ')' after funnction arguments",
        )?;

        Ok(Expression::call(expr, paren, arguments))
    }

    fn primary(&mut self) -> Result<Expression, LoxError> {
        if self.match_token(TokenType::False) {
            Ok(Expression::literal(LoxObject::Boolean(false).wrap()))
        } else if self.match_token(TokenType::True) {
            Ok(Expression::literal(LoxObject::Boolean(true).wrap()))
        } else if self.match_token(TokenType::Nil) {
            Ok(Expression::literal(LoxObject::Nil.wrap()))
        } else if self.match_token(TokenType::Number) {
            Ok(Expression::literal(
                LoxObject::Number(self.previous().literal.get_number().unwrap()).wrap(),
            ))
        } else if self.match_token(TokenType::LoxString) {
            Ok(Expression::literal(
                LoxObject::String(self.previous().literal.get_string().unwrap()).wrap(),
            ))
        } else if self.match_token(TokenType::Identifier) {
            Ok(Expression::variable(self.previous()))
        } else if self.match_token(TokenType::LeftParen) {
            let expr = self.expression()?;
            self.consume(TokenType::RightParen, "Expect ')' after expression")?;
            Ok(Expression::grouping(expr))
        } else {
            let cause = self.peek();
            let message = "expected expression";
            Err(crate::lox::parse_error(
                cause,
                LoxErrorType::ExpressionError,
                message,
            ))
        }
    }

    fn consume(&mut self, token_type: TokenType, message: &str) -> Result<Token, LoxError> {
        if self.check(token_type) {
            Ok(self.advance())
        } else {
            Err(crate::lox::parse_error(
                self.peek(),
                LoxErrorType::IncompleteExpression,
                message,
            ))
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
