use crate::lox::{FileLocation, LoxError, LoxErrorType, LoxNumber};
use crate::scanner::{Token, TokenType};
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
meta-programming and the visitor pattern to easily create Java classes to
represent nested expressions. The thing is, in my opinion, Rust is usable
enough for this kind of task that I feel fine creating this code by hand. I
might revisit this using meta-programming or macros later when I feel better
about Rust 🙂

The ultimate goal here is to show how you can implement N behaviors for each
of M data types, but with Rust that's just `impl`.

So, for example, the book says to create an `AstPrinter` class which
implements visitors for each type, binary/grouping/literal/ unary, which each
in turn produce a string. This is logically equivalent to `ExpressionPrinter`
trait which each expression implements.
*/

pub struct Parser {
    tokens: Vec<Token>,
    current: FileLocation,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expression {
    Assignment {
        id: ExpressionId,
        name: Token,
        value: Box<Expression>,
    },
    Binary {
        left: Box<Expression>,
        op: Token,
        right: Box<Expression>,
    },
    Grouping {
        expression: Box<Expression>,
    },
    Literal {
        value: LoxLiteral,
    },
    Logical {
        left: Box<Expression>,
        op: Token,
        right: Box<Expression>,
    },
    Unary {
        op: Token,
        value: Box<Expression>,
    },
    Call {
        callee: Box<Expression>,
        paren: Token,
        args: Vec<Expression>,
    },
    This {
        id: ExpressionId,
        keyword: Token,
    },
    Set {
        object: Box<Expression>,
        name: Token,
        value: Box<Expression>,
    },
    Get {
        object: Box<Expression>,
        name: Token,
    },
    Variable {
        id: ExpressionId,
        name: Token,
    },
}
#[derive(Debug, Clone, PartialEq)]
pub enum Statement {
    Print {
        expression: Expression,
    },
    Expression {
        expression: Expression,
    },
    Block {
        statements: Vec<Statement>,
    },
    Class {
        name: Token,
        methods: Vec<FunctionDefinition>,
    },
    Var {
        name: Token,
        initializer: Option<Expression>,
    },
    If {
        condition: Expression,
        then_statement: Box<Statement>,
        else_statement: Option<Box<Statement>>,
    },
    Function {
        definition: FunctionDefinition,
    },
    While {
        condition: Expression,
        body: Box<Statement>,
    },
    Return {
        keyword: Token,
        value: Expression,
    },
    None,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunctionDefinition {
    pub name: Token,
    pub params: Vec<Token>,
    pub body: Vec<Statement>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum LoxLiteral {
    Boolean(bool),
    String(String),
    Number(LoxNumber),
    Nil,
}

pub type ExpressionId = u128;

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
        let declaration = if self.match_token(TokenType::Class) {
            self.class_declaration()
        } else if self.match_token(TokenType::Fun) {
            self.function("function")
        } else if self.match_token(TokenType::Var) {
            self.var_declaration()
        } else {
            self.statement()
        };

        match declaration {
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
        Ok(Statement::Class { name, methods })
    }

    fn function(&mut self, kind: &str) -> Result<Statement, LoxError> {
        Ok(Statement::Function {
            definition: self.function_definition(kind)?,
        })
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
        Ok(Statement::Var { name, initializer })
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
            self.block()
                .map(|statements| Statement::Block { statements })
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
            let condition = self.expression()?;
            self.consume(TokenType::Semicolon, "expect ';' after for condition")?;
            Some(condition)
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
            Some(expression) => Statement::Block {
                statements: vec![body, Statement::Expression { expression }],
            },
            None => body,
        };

        body = match condition {
            Some(condition) => Statement::While {
                condition,
                body: Box::new(body),
            },
            None => Statement::While {
                condition: Expression::Literal {
                    value: LoxLiteral::Boolean(true),
                },
                body: Box::new(body),
            },
        };

        body = match initializer {
            Statement::None => body,
            _ => Statement::Block {
                statements: vec![initializer, body],
            },
        };

        Ok(body)
    }

    fn while_statement(&mut self) -> Result<Statement, LoxError> {
        self.consume(TokenType::LeftParen, "expect '(' after 'while'")?;
        let condition = self.expression()?;
        self.consume(TokenType::RightParen, "expect ')' after while condition")?;
        let body = Box::new(self.statement()?);

        Ok(Statement::While { condition, body })
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

        Ok(Statement::If {
            condition,
            then_statement,
            else_statement,
        })
    }

    fn print_statement(&mut self) -> Result<Statement, LoxError> {
        let expression = self.expression()?;
        self.consume(TokenType::Semicolon, "expect ';' after value")?;
        Ok(Statement::Print { expression })
    }

    fn return_statement(&mut self) -> Result<Statement, LoxError> {
        let keyword = self.previous();
        let value = if self.check(TokenType::Semicolon) {
            Expression::Literal {
                value: LoxLiteral::Nil,
            }
        } else {
            self.expression()?
        };

        self.consume(TokenType::Semicolon, "expect ';' after return statement")?;
        Ok(Statement::Return { keyword, value })
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
        let expression = self.expression()?;
        self.consume(TokenType::Semicolon, "expect ';' after statement")?;
        Ok(Statement::Expression { expression })
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

            if let Expression::Variable { name, .. } = expr {
                return Ok(Expression::assignment(name, value));
            } else if let Expression::Get { object, name } = expr {
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

        let paren = self.consume(TokenType::RightParen, "expect ')' after function arguments")?;

        Ok(Expression::call(expr, paren, arguments))
    }

    fn primary(&mut self) -> Result<Expression, LoxError> {
        if self.match_token(TokenType::False) {
            Ok(Expression::literal(LoxLiteral::Boolean(false)))
        } else if self.match_token(TokenType::True) {
            Ok(Expression::literal(LoxLiteral::Boolean(true)))
        } else if self.match_token(TokenType::Nil) {
            Ok(Expression::literal(LoxLiteral::Nil))
        } else if self.match_token(TokenType::Number) {
            Ok(Expression::literal(LoxLiteral::Number(
                self.previous().literal.get_number().unwrap(),
            )))
        } else if self.match_token(TokenType::LoxString) {
            Ok(Expression::literal(LoxLiteral::String(
                self.previous().literal.get_string().unwrap(),
            )))
        } else if self.match_token(TokenType::This) {
            Ok(Expression::this(self.previous()))
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

impl Expression {
    fn assignment(name: Token, value: Expression) -> Expression {
        let value = Box::new(value);
        Expression::Assignment {
            id: Uuid::new_v4().as_u128(),
            value,
            name,
        }
    }

    fn binary(l: Expression, op: Token, r: Expression) -> Expression {
        let left = Box::new(l);
        let right = Box::new(r);
        Expression::Binary { left, right, op }
    }

    fn grouping(e: Expression) -> Expression {
        Expression::Grouping {
            expression: Box::new(e),
        }
    }

    fn literal(l: LoxLiteral) -> Expression {
        Expression::Literal { value: l }
    }

    fn logical(l: Expression, op: Token, r: Expression) -> Expression {
        let left = Box::new(l);
        let right = Box::new(r);
        Expression::Logical { left, right, op }
    }

    fn unary(op: Token, value: Expression) -> Expression {
        let value = Box::new(value);
        Expression::Unary { op, value }
    }

    fn variable(name: Token) -> Expression {
        Expression::Variable {
            id: Uuid::new_v4().as_u128(),
            name,
        }
    }

    fn call(callee: Expression, paren: Token, args: Vec<Expression>) -> Expression {
        let callee = Box::new(callee);
        Expression::Call {
            callee,
            paren,
            args,
        }
    }

    fn this(keyword: Token) -> Expression {
        Expression::This {
            id: Uuid::new_v4().as_u128(),
            keyword,
        }
    }

    fn get(object: Expression, name: Token) -> Expression {
        let object = Box::new(object);
        Expression::Get { object, name }
    }

    fn set(object: Expression, name: Token, value: Expression) -> Expression {
        let object = Box::new(object);
        let value = Box::new(value);
        Expression::Set {
            object,
            name,
            value,
        }
    }

    pub fn get_id(&self) -> ExpressionId {
        match self {
            Expression::Variable { id, .. }
            | Expression::Assignment { id, .. }
            | Expression::This { id, .. } => *id,
            _ => panic!(format!(
                "Unrecoverable lox error to get expression id for expression {:?}",
                self
            )),
        }
    }

    pub fn is_nil(&self) -> bool {
        match self {
            Expression::Literal { value } => value.is_nil(),
            _ => false,
        }
    }
}

impl LoxLiteral {
    fn is_nil(&self) -> bool {
        if let LoxLiteral::Nil = self {
            true
        } else {
            false
        }
    }

    pub fn to_string(&self) -> String {
        match self {
            LoxLiteral::Boolean(b) => b.to_string(),
            LoxLiteral::String(s) => format!("\"{}\"", s),
            LoxLiteral::Number(n) => n.to_string(),
            LoxLiteral::Nil => "nil".to_string(),
        }
    }
}
