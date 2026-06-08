#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    LParen,
    RParen,
    Symbol(String),
    Keyword(String),
    Int(i64),
    Real(f64),
    BitVec(u64, usize),
    String(String),
}

pub struct Lexer<'a> {
    chars: std::iter::Peekable<std::str::Chars<'a>>,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str) -> Self {
        Self {
            chars: input.chars().peekable(),
        }
    }

    pub fn next_token(&mut self) -> Option<Token> {
        self.skip_whitespace();
        let c = self.chars.next()?;

        match c {
            '(' => Some(Token::LParen),
            ')' => Some(Token::RParen),
            ':' => {
                let mut s = String::new();
                s.push(':');
                while let Some(&next) = self.chars.peek() {
                    if next.is_whitespace() || next == '(' || next == ')' { break; }
                    s.push(self.chars.next().unwrap());
                }
                Some(Token::Keyword(s))
            }
            '"' => {
                let mut s = String::new();
                for next in self.chars.by_ref() {
                    if next == '"' { break; }
                    s.push(next);
                }
                Some(Token::String(s))
            }
            '#' => {
                let base = self.chars.next()?;
                if base != 'b' {
                    return self.next_token();
                }
                let mut value = 0u64;
                let mut width = 0usize;
                while let Some(&next) = self.chars.peek() {
                    match next {
                        '0' | '1' => {
                            value = (value << 1) | u64::from(next == '1');
                            width += 1;
                            self.chars.next();
                        }
                        _ => break,
                    }
                }
                if width == 0 { self.next_token() } else { Some(Token::BitVec(value, width)) }
            }
            c if c.is_ascii_digit() || (c == '-' && self.chars.peek().is_some_and(|&n| n.is_ascii_digit())) => {
                let mut s = String::new();
                s.push(c);
                while let Some(&next) = self.chars.peek() {
                    if next.is_ascii_digit() || next == '.' {
                        s.push(self.chars.next().unwrap());
                    } else {
                        break;
                    }
                }
                if s.contains('.') {
                    Some(Token::Real(s.parse().unwrap_or(0.0)))
                } else {
                    Some(Token::Int(s.parse().unwrap_or(0)))
                }
            }
            c if is_symbol_char(c) => {
                let mut s = String::new();
                s.push(c);
                while let Some(&next) = self.chars.peek() {
                    if is_symbol_char(next) || next.is_ascii_digit() {
                        s.push(self.chars.next().unwrap());
                    } else {
                        break;
                    }
                }
                Some(Token::Symbol(s))
            }
            _ => self.next_token(), // Skip unknown chars
        }
    }

    fn skip_whitespace(&mut self) {
        while let Some(&c) = self.chars.peek() {
            if c.is_whitespace() {
                self.chars.next();
            } else if c == ';' {
                for next in self.chars.by_ref() {
                    if next == '\n' { break; }
                }
            } else {
                break;
            }
        }
    }
}

fn is_symbol_char(c: char) -> bool {
    c.is_alphabetic() || "~!@$%^&*_-+=<>.?/".contains(c)
}

use crate::ast::{fp::FloatSort, Expr, Type};

#[derive(Debug, Clone, PartialEq)]
pub enum Command {
    SetLogic(String),
    SetOption(String, String),
    DeclareFun(String, Vec<Type>, Type),
    DefineFun(String, Vec<(String, Type)>, Type, Expr),
    Assert(Expr),
    CheckSat,
    GetModel,
    Exit,
    SetInfo(String, String),
}

pub struct Parser<'a> {
    lexer: Lexer<'a>,
    peeked: Option<Token>,
}

impl<'a> Parser<'a> {
    pub fn new(input: &'a str) -> Self {
        Self {
            lexer: Lexer::new(input),
            peeked: None,
        }
    }

    fn next_token(&mut self) -> Option<Token> {
        self.peeked.take().or_else(|| self.lexer.next_token())
    }

    fn peek_token(&mut self) -> Option<&Token> {
        if self.peeked.is_none() {
            self.peeked = self.lexer.next_token();
        }
        self.peeked.as_ref()
    }

    pub fn parse_type(&mut self) -> Option<Type> {
        let token = self.next_token()?;
        match token {
            Token::Symbol(s) => match s.as_str() {
                "Bool" => Some(Type::Bool),
                "Int" => Some(Type::Int),
                "Real" => Some(Type::Real),
                _ => None,
            },
            Token::LParen => {
                let head = self.next_token()?;
                if let Token::Symbol(s) = head {
                    if s == "_" {
                        let op = self.next_token()?;
                        if let Token::Symbol(op_s) = op {
                            if op_s == "BitVec" {
                                if let Some(Token::Int(w)) = self.next_token() {
                                    self.next_token(); // RParen
                                    self.next_token(); // RParen
                                    return Some(Type::BitVec(w as usize));
                                }
                            } else if op_s == "FloatingPoint" {
                                if let (Some(Token::Int(ebits)), Some(Token::Int(sbits))) =
                                    (self.next_token(), self.next_token())
                                {
                                    self.next_token(); // RParen
                                    self.next_token(); // RParen
                                    return Some(Type::Float(FloatSort {
                                        exponent_bits: ebits as u16,
                                        significand_bits: sbits as u16,
                                    }));
                                }
                            }
                        }
                    }
                }
                None
            }
            _ => None,
        }
    }

    pub fn parse_command(&mut self) -> Option<Command> {
        let token = self.next_token()?;
        if token != Token::LParen { return None; }
        
        let op = match self.next_token()? {
            Token::Symbol(s) => s,
            _ => return None,
        };

        let cmd = match op.as_str() {
            "set-logic" => {
                let logic = match self.next_token()? {
                    Token::Symbol(s) => s,
                    _ => return None,
                };
                self.next_token(); // RParen
                Command::SetLogic(logic)
            }
            "set-option" => {
                let key = match self.next_token()? {
                    Token::Keyword(s) => s,
                    _ => return None,
                };
                let value = match self.next_token()? {
                    Token::Symbol(s) => s,
                    Token::Int(i) => i.to_string(),
                    Token::Real(f) => f.to_string(),
                    Token::BitVec(v, w) => format!("#b{:0width$b}", v, width = w),
                    Token::String(s) => s,
                    _ => return None,
                };
                self.next_token(); // RParen
                Command::SetOption(key, value)
            }
            "get-value" => {
                if self.next_token() != Some(Token::LParen) { return None; }
                let mut exprs = Vec::new();
                while self.peek_token() != Some(&Token::RParen) {
                    if let Some(e) = self.parse_expr() {
                        exprs.push(e);
                    }
                }
                self.next_token(); // RParen (expr list)
                self.next_token(); // RParen (command)
                // Note: Command::GetModel is reused or we should add GetValue
                Command::GetModel 
            }
            "push" => {
                let n = if let Some(Token::Int(i)) = self.peek_token() {
                    let val = *i;
                    self.next_token();
                    val as usize
                } else { 1 };
                self.next_token(); // RParen
                Command::SetOption(":push".to_string(), n.to_string())
            }
            "pop" => {
                let n = if let Some(Token::Int(i)) = self.peek_token() {
                    let val = *i;
                    self.next_token();
                    val as usize
                } else { 1 };
                self.next_token(); // RParen
                Command::SetOption(":pop".to_string(), n.to_string())
            }
            "set-info" => {
                let key = match self.next_token()? {
                    Token::Keyword(s) => s,
                    _ => return None,
                };
                let value = match self.next_token()? {
                    Token::Symbol(s) => s,
                    Token::Int(i) => i.to_string(),
                    Token::String(s) => s,
                    Token::Real(f) => f.to_string(),
                    Token::BitVec(v, w) => format!("#b{:0width$b}", v, width = w),
                    _ => return None,
                };
                self.next_token(); // RParen
                Command::SetInfo(key, value)
            }
            "declare-fun" => {
                let name = match self.next_token()? {
                    Token::Symbol(s) => s,
                    _ => return None,
                };
                
                // Parse params: ((name Type) ...)
                let mut params = Vec::new();
                if self.next_token() == Some(Token::LParen) {
                    while self.peek_token() != Some(&Token::RParen) {
                        if self.next_token() == Some(Token::LParen) {
                            let _param_name = self.next_token()?; // Ignore name for now
                            let param_type = self.parse_type()?;
                            self.next_token(); // RParen
                            params.push(param_type);
                        }
                    }
                    self.next_token(); // RParen
                }
                
                let return_type = self.parse_type()?;
                self.next_token(); // RParen
                Command::DeclareFun(name, params, return_type)
            }
            "define-fun" => {
                let name = match self.next_token()? {
                    Token::Symbol(s) => s,
                    _ => return None,
                };
                
                // Parse params: ((name Type) ...)
                let mut params = Vec::new();
                if self.next_token() == Some(Token::LParen) {
                    while self.peek_token() != Some(&Token::RParen) {
                        if self.next_token() == Some(Token::LParen) {
                            let param_name = match self.next_token()? {
                                Token::Symbol(s) => s,
                                _ => return None,
                            };
                            let param_type = self.parse_type()?;
                            self.next_token(); // RParen
                            params.push((param_name, param_type));
                        }
                    }
                    self.next_token(); // RParen
                }
                
                let return_type = self.parse_type()?;
                let body = self.parse_expr()?;
                self.next_token(); // RParen
                Command::DefineFun(name, params, return_type, body)
            }
            "assert" => {
                let expr = self.parse_expr()?;
                self.next_token(); // RParen
                Command::Assert(expr)
            }
            "check-sat" => {
                self.next_token(); // RParen
                Command::CheckSat
            }
            "get-model" => {
                self.next_token(); // RParen
                Command::GetModel
            }
            _ => return None,
        };
        Some(cmd)
    }

    pub fn parse_expr(&mut self) -> Option<Expr> {
        let token = self.next_token()?;
        match token {
            Token::Int(i) => Some(Expr::Int(i)),
            Token::BitVec(value, width) => Some(Expr::BvConst(value, width)),
            Token::Real(f) => {
                let s = f.to_string();
                if let Some(pos) = s.find('.') {
                    let decimal_places = s.len() - pos - 1;
                    let val = (f * 10f64.powi(decimal_places as i32)).round() as i64;
                    Some(Expr::Real(val, decimal_places as u32))
                } else {
                    Some(Expr::Real(f as i64, 0))
                }
            }
            Token::Symbol(s) => {
                match s.as_str() {
                    "true" => Some(Expr::Bool(true)),
                    "false" => Some(Expr::Bool(false)),
                    _ => Some(Expr::Var(s, Type::Real)), // Default to Real
                }
            }
            Token::LParen => {
                let head = self.next_token()?;
                let op = match head {
                    Token::Symbol(s) => s,
                    _ => return None,
                };
                
                let mut args = Vec::new();
                while self.peek_token() != Some(&Token::RParen) {
                    if let Some(arg) = self.parse_expr() {
                        args.push(arg);
                    } else {
                        break;
                    }
                }
                self.next_token(); // Consume RParen
                
                match op.as_str() {
                    "and" => Some(Expr::And(args)),
                    "or" => Some(Expr::Or(args)),
                    "not" => Some(Expr::Not(Box::new(args.into_iter().next()?))),
                    "+" => Some(Expr::Add(args)),
                    "*" => Some(Expr::Mul(args)),
                    "<=" => Some(Expr::Le(Box::new(args[0].clone()), Box::new(args[1].clone()))),
                    ">=" => Some(Expr::Ge(Box::new(args[0].clone()), Box::new(args[1].clone()))),
                    "<" => Some(Expr::Lt(Box::new(args[0].clone()), Box::new(args[1].clone()))),
                    ">" => Some(Expr::Gt(Box::new(args[0].clone()), Box::new(args[1].clone()))),
                    "=" => Some(Expr::Eq(Box::new(args[0].clone()), Box::new(args[1].clone()))),
                    "ite" => Some(Expr::Ite(
                        Box::new(args[0].clone()),
                        Box::new(args[1].clone()),
                        Box::new(args[2].clone()),
                    )),
                    _ => Some(Expr::App(op, args)),
                }
            }
            _ => None,
        }
    }
}
