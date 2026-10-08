//! SMT-LIB 2.6 front end.
//!
//! Design rule (RZ3 soundness audit, 2026-10): the front end never weakens a
//! formula silently. Anything it cannot translate faithfully is recorded in
//! [`Parser::error`] instead of being dropped, truncated or turned into an
//! uninterpreted symbol. `let` and `define-fun` are expanded here, so the
//! solver only ever sees the fully interpreted formula.

use std::collections::{BTreeMap, VecDeque};

#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    LParen,
    RParen,
    Symbol(String),
    Keyword(String),
    Int(i64),
    Real(i64, u32),
    /// Numeral or decimal that does not fit the machine representations: exact digits
    /// (`123..` or `12.5..`), converted to a rational by the parser.
    BigNum(String),
    BitVec(u64, usize),
    String(String),
}

pub struct Lexer<'a> {
    chars: std::iter::Peekable<std::str::Chars<'a>>,
    error: Option<String>,
}

/// Widest bit-vector literal/sort the front end accepts: values are carried in `u64`.
pub const MAX_PARSED_BV_WIDTH: usize = 64;

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str) -> Self {
        Self {
            chars: input.chars().peekable(),
            error: None,
        }
    }

    /// First lexical error seen so far, if any.
    pub fn error(&self) -> Option<&str> {
        self.error.as_deref()
    }

    fn fail(&mut self, msg: impl Into<String>) {
        if self.error.is_none() {
            self.error = Some(msg.into());
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
                    if next.is_whitespace() || next == '(' || next == ')' {
                        break;
                    }
                    let Some(consumed) = self.chars.next() else {
                        break;
                    };
                    s.push(consumed);
                }
                Some(Token::Keyword(s))
            }
            '"' => {
                let mut s = String::new();
                loop {
                    match self.chars.next() {
                        Some('"') => {
                            if self.chars.peek() == Some(&'"') {
                                self.chars.next();
                                s.push('"');
                            } else {
                                return Some(Token::String(s));
                            }
                        }
                        Some(ch) => s.push(ch),
                        None => {
                            self.fail("unterminated string literal");
                            return None;
                        }
                    }
                }
            }
            '|' => {
                let mut s = String::new();
                loop {
                    match self.chars.next() {
                        Some('|') => return Some(Token::Symbol(s)),
                        Some(ch) => s.push(ch),
                        None => {
                            self.fail("unterminated quoted symbol");
                            return None;
                        }
                    }
                }
            }
            '#' => match self.chars.next() {
                Some('b') => {
                    let mut value = 0u64;
                    let mut width = 0usize;
                    while let Some(&next) = self.chars.peek() {
                        match next {
                            '0' | '1' => {
                                if width >= MAX_PARSED_BV_WIDTH {
                                    self.fail(
                                        "bit-vector literal wider than 64 bits is unsupported",
                                    );
                                    return None;
                                }
                                value = (value << 1) | u64::from(next == '1');
                                width += 1;
                                self.chars.next();
                            }
                            _ => break,
                        }
                    }
                    if width == 0 {
                        self.fail("empty #b literal");
                        None
                    } else {
                        Some(Token::BitVec(value, width))
                    }
                }
                Some('x') => {
                    let mut value = 0u64;
                    let mut digits = 0usize;
                    while let Some(&next) = self.chars.peek() {
                        let Some(d) = next.to_digit(16) else { break };
                        if digits >= MAX_PARSED_BV_WIDTH / 4 {
                            self.fail("bit-vector literal wider than 64 bits is unsupported");
                            return None;
                        }
                        value = (value << 4) | u64::from(d);
                        digits += 1;
                        self.chars.next();
                    }
                    if digits == 0 {
                        self.fail("empty #x literal");
                        None
                    } else {
                        Some(Token::BitVec(value, digits * 4))
                    }
                }
                _ => {
                    self.fail("unsupported '#' literal");
                    None
                }
            },
            c if c.is_ascii_digit()
                || (c == '-' && self.chars.peek().is_some_and(|&n| n.is_ascii_digit())) =>
            {
                let mut s = String::new();
                s.push(c);
                while let Some(&next) = self.chars.peek() {
                    if next.is_ascii_digit() || next == '.' {
                        let Some(consumed) = self.chars.next() else {
                            break;
                        };
                        s.push(consumed);
                    } else {
                        break;
                    }
                }
                if s.contains('.') {
                    match parse_decimal_token(&s) {
                        Some((mantissa, scale)) => Some(Token::Real(mantissa, scale)),
                        // Too many digits for i64: keep them exactly instead of rejecting.
                        None if s.trim_start_matches('-').split_once('.').is_some_and(
                            |(w, f)| {
                                (!w.is_empty() || !f.is_empty())
                                    && w.chars().chain(f.chars()).all(|c| c.is_ascii_digit())
                            },
                        ) =>
                        {
                            Some(Token::BigNum(s))
                        }
                        None => {
                            self.fail(format!("malformed decimal '{s}'"));
                            None
                        }
                    }
                } else {
                    match s.parse() {
                        Ok(v) => Some(Token::Int(v)),
                        Err(_) => Some(Token::BigNum(s)),
                    }
                }
            }
            c if is_symbol_char(c) => {
                let mut s = String::new();
                s.push(c);
                while let Some(&next) = self.chars.peek() {
                    if is_symbol_char(next) || next.is_ascii_digit() {
                        let Some(consumed) = self.chars.next() else {
                            break;
                        };
                        s.push(consumed);
                    } else {
                        break;
                    }
                }
                Some(Token::Symbol(s))
            }
            other => {
                self.fail(format!("unexpected character {other:?}"));
                self.next_token()
            }
        }
    }

    fn skip_whitespace(&mut self) {
        while let Some(&c) = self.chars.peek() {
            if c.is_whitespace() {
                self.chars.next();
            } else if c == ';' {
                for next in self.chars.by_ref() {
                    if next == '\n' {
                        break;
                    }
                }
            } else {
                break;
            }
        }
    }
}

use crate::ast::{fp::FloatSort, Expr, Type};

#[derive(Debug, Clone, PartialEq)]
pub enum Command {
    SetLogic(String),
    SetOption(String, String),
    DeclareFun(String, Vec<Type>, Type),
    /// `(declare-sort name 0)`: a new uninterpreted sort.
    DeclareSort(String),
    /// The body is already expanded by the parser wherever the function is used;
    /// consumers must NOT also declare it as an uninterpreted function.
    DefineFun(String, Vec<(String, Type)>, Type, Expr),
    Assert(Expr),
    CheckSat,
    GetModel,
    GetValue(Vec<Expr>),
    Push(usize),
    Pop(usize),
    Exit,
    SetInfo(String, String),
    /// A harmless query command (`get-info`, `echo`, ...) that was parsed and ignored.
    Skipped(String),
}

#[derive(Clone)]
struct Macro {
    params: Vec<(String, Type)>,
    body: Vec<Token>,
}

pub struct Parser<'a> {
    lexer: Lexer<'a>,
    peeked: Option<Token>,
    strict: bool,
    error: Option<String>,
    consts: BTreeMap<String, Type>,
    /// Declared sorts: `None` = uninterpreted, `Some(t)` = alias created by `define-sort`.
    sorts: BTreeMap<String, Option<Type>>,
    funs: BTreeMap<String, usize>,
    macros: BTreeMap<String, Macro>,
    env: Vec<BTreeMap<String, Expr>>,
    injected: Vec<VecDeque<Token>>,
    recording: Option<Vec<Token>>,
}

impl<'a> Parser<'a> {
    /// Lenient parser: undeclared symbols default to `Real` and unknown operators
    /// become uninterpreted applications. Meant for programmatic use and tests;
    /// the CLI uses [`Parser::strict`].
    pub fn new(input: &'a str) -> Self {
        Self {
            lexer: Lexer::new(input),
            peeked: None,
            strict: false,
            error: None,
            consts: BTreeMap::new(),
            sorts: BTreeMap::new(),
            funs: BTreeMap::new(),
            macros: BTreeMap::new(),
            env: Vec::new(),
            injected: Vec::new(),
            recording: None,
        }
    }

    /// Strict parser: undeclared symbols and operators that are neither interpreted
    /// nor declared are errors, never silently-uninterpreted terms.
    pub fn strict(input: &'a str) -> Self {
        let mut p = Self::new(input);
        p.strict = true;
        p
    }

    /// First parse error, if any. A `None` from `parse_command` with no error
    /// means a clean end of input.
    pub fn error(&self) -> Option<&str> {
        self.error.as_deref()
    }

    fn set_error(&mut self, msg: impl Into<String>) {
        if self.error.is_none() {
            self.error = Some(msg.into());
        }
    }

    fn fail<T>(&mut self, msg: impl Into<String>) -> Option<T> {
        self.set_error(msg);
        None
    }

    fn fetch(&mut self) -> Option<Token> {
        if let Some(queue) = self.injected.last_mut() {
            return queue.pop_front();
        }
        let token = self.lexer.next_token();
        if let Some(e) = self.lexer.error() {
            let e = e.to_string();
            self.set_error(e);
        }
        if let (Some(rec), Some(tok)) = (self.recording.as_mut(), token.as_ref()) {
            rec.push(tok.clone());
        }
        token
    }

    fn next_token(&mut self) -> Option<Token> {
        match self.peeked.take() {
            Some(t) => Some(t),
            None => self.fetch(),
        }
    }

    fn peek_token(&mut self) -> Option<&Token> {
        if self.peeked.is_none() {
            self.peeked = self.fetch();
        }
        self.peeked.as_ref()
    }

    fn expect_rparen(&mut self) -> Option<()> {
        match self.next_token() {
            Some(Token::RParen) => Some(()),
            _ => self.fail("expected ')'"),
        }
    }

    fn expect_lparen(&mut self) -> Option<()> {
        match self.next_token() {
            Some(Token::LParen) => Some(()),
            _ => self.fail("expected '('"),
        }
    }

    fn expect_symbol(&mut self, what: &str) -> Option<String> {
        match self.next_token() {
            Some(Token::Symbol(s)) => Some(s),
            _ => self.fail(format!("expected {what}")),
        }
    }

    /// Skip the rest of the current list (the opening paren is already consumed).
    fn skip_to_rparen(&mut self) -> Option<()> {
        let mut depth = 1usize;
        while depth > 0 {
            match self.next_token() {
                Some(Token::LParen) => depth += 1,
                Some(Token::RParen) => depth -= 1,
                Some(_) => {}
                None => return self.fail("unexpected end of input"),
            }
        }
        Some(())
    }

    pub fn parse_type(&mut self) -> Option<Type> {
        match self.next_token() {
            Some(Token::Symbol(s)) => match s.as_str() {
                "Bool" => Some(Type::Bool),
                "Int" => Some(Type::Int),
                "Real" => Some(Type::Real),
                other => match self.sorts.get(other) {
                    Some(None) => Some(Type::Sort(other.to_string())),
                    Some(Some(alias)) => Some(alias.clone()),
                    None => self.fail(format!("unsupported sort '{other}'")),
                },
            },
            Some(Token::LParen) => {
                if self.peek_token() == Some(&Token::Symbol("Array".to_string())) {
                    self.next_token();
                    let index = self.parse_type()?;
                    let element = self.parse_type()?;
                    self.expect_rparen()?;
                    return Some(Type::Array(Box::new(index), Box::new(element)));
                }
                self.parse_indexed_type()
            }
            _ => self.fail("expected a sort"),
        }
    }

    /// Parses `_ BitVec w)` / `_ FloatingPoint e s)` once `(` has been consumed.
    fn parse_indexed_type(&mut self) -> Option<Type> {
        if self.expect_symbol("'_'")? != "_" {
            return self.fail("unsupported parametric sort");
        }
        let name = self.expect_symbol("sort name")?;
        match name.as_str() {
            "BitVec" => {
                let Some(Token::Int(w)) = self.next_token() else {
                    return self.fail("expected a bit-vector width");
                };
                if !(1..=MAX_PARSED_BV_WIDTH as i64).contains(&w) {
                    return self.fail(format!("bit-vector width {w} is unsupported (1..=64)"));
                }
                self.expect_rparen()?;
                Some(Type::BitVec(w as usize))
            }
            "FloatingPoint" => {
                let (Some(Token::Int(e)), Some(Token::Int(s))) =
                    (self.next_token(), self.next_token())
                else {
                    return self.fail("expected floating-point sort indices");
                };
                if !(2..=u16::MAX as i64).contains(&e) || !(2..=u16::MAX as i64).contains(&s) {
                    return self.fail("floating-point sort indices out of range");
                }
                self.expect_rparen()?;
                Some(Type::Float(FloatSort {
                    exponent_bits: e as u16,
                    significand_bits: s as u16,
                }))
            }
            other => self.fail(format!("unsupported sort '{other}'")),
        }
    }

    fn parse_attribute_value(&mut self) -> Option<String> {
        Some(match self.next_token() {
            Some(Token::Symbol(s)) => s,
            Some(Token::Int(i)) => i.to_string(),
            Some(Token::Real(i, s)) => format_real_token(i, s),
            Some(Token::BigNum(t)) => t,
            Some(Token::BitVec(v, w)) => format!("#b{:0width$b}", v, width = w),
            Some(Token::String(s)) => s,
            _ => return self.fail("unsupported attribute value"),
        })
    }

    fn register_const(&mut self, name: &str, ty: &Type) -> Option<()> {
        if self.funs.contains_key(name) || self.macros.contains_key(name) {
            return self.fail(format!("'{name}' is already declared"));
        }
        match self.consts.get(name) {
            Some(old) if old != ty => self.fail(format!("'{name}' redeclared with another sort")),
            _ => {
                self.consts.insert(name.to_string(), ty.clone());
                Some(())
            }
        }
    }

    pub fn parse_command(&mut self) -> Option<Command> {
        if self.error.is_some() {
            return None;
        }
        let token = self.next_token()?;
        if token != Token::LParen {
            return self.fail("expected '(' at the start of a command");
        }
        let op = self.expect_symbol("a command name")?;

        let cmd = match op.as_str() {
            "set-logic" => {
                let logic = self.expect_symbol("a logic name")?;
                self.expect_rparen()?;
                Command::SetLogic(logic)
            }
            "set-option" | "set-info" => {
                let key = match self.next_token() {
                    Some(Token::Keyword(s)) => s,
                    _ => return self.fail("expected an attribute keyword"),
                };
                let value = if self.peek_token() == Some(&Token::RParen) {
                    String::new()
                } else {
                    self.parse_attribute_value()?
                };
                self.expect_rparen()?;
                if op == "set-option" {
                    Command::SetOption(key, value)
                } else {
                    Command::SetInfo(key, value)
                }
            }
            "get-value" => {
                self.expect_lparen()?;
                let mut exprs = Vec::new();
                loop {
                    match self.peek_token() {
                        Some(Token::RParen) => {
                            self.next_token();
                            break;
                        }
                        None => return self.fail("unexpected end of input"),
                        _ => exprs.push(self.parse_expr()?),
                    }
                }
                self.expect_rparen()?;
                Command::GetValue(exprs)
            }
            "push" | "pop" => {
                let n = if let Some(Token::Int(i)) = self.peek_token() {
                    let val = *i;
                    self.next_token();
                    if val < 0 {
                        return self.fail("negative push/pop count");
                    }
                    val as usize
                } else {
                    1
                };
                self.expect_rparen()?;
                if op == "push" {
                    Command::Push(n)
                } else {
                    Command::Pop(n)
                }
            }
            "declare-sort" => {
                let name = self.expect_symbol("a sort name")?;
                match self.next_token() {
                    Some(Token::Int(0)) => {}
                    Some(Token::RParen) => {
                        // `(declare-sort S)` without arity is accepted as arity 0.
                        self.sorts.insert(name.clone(), None);
                        return Some(Command::DeclareSort(name));
                    }
                    _ => return self.fail("parametric sorts are unsupported"),
                }
                self.expect_rparen()?;
                if self.sorts.contains_key(&name) {
                    return self.fail(format!("sort '{name}' is already declared"));
                }
                self.sorts.insert(name.clone(), None);
                Command::DeclareSort(name)
            }
            "define-sort" => {
                let name = self.expect_symbol("a sort name")?;
                self.expect_lparen()?;
                if self.peek_token() != Some(&Token::RParen) {
                    return self.fail("parametric sort definitions are unsupported");
                }
                self.next_token();
                let ty = self.parse_type()?;
                self.expect_rparen()?;
                self.sorts.insert(name.clone(), Some(ty));
                Command::Skipped(format!("define-sort {name}"))
            }
            "declare-const" => {
                let name = self.expect_symbol("a constant name")?;
                let ty = self.parse_type()?;
                self.expect_rparen()?;
                self.register_const(&name, &ty)?;
                Command::DeclareFun(name, Vec::new(), ty)
            }
            "declare-fun" => {
                let name = self.expect_symbol("a function name")?;
                self.expect_lparen()?;
                let mut params = Vec::new();
                loop {
                    match self.next_token() {
                        Some(Token::RParen) => break,
                        // `(_ BitVec 8)` is a sort; `(x Real)` is a named parameter.
                        Some(Token::LParen) => {
                            if self.peek_token() == Some(&Token::Symbol("_".to_string())) {
                                params.push(self.parse_indexed_type()?);
                            } else {
                                self.expect_symbol("a parameter name")?;
                                params.push(self.parse_type()?);
                                self.expect_rparen()?;
                            }
                        }
                        Some(Token::Symbol(s)) => {
                            self.peeked = Some(Token::Symbol(s));
                            params.push(self.parse_type()?);
                        }
                        _ => return self.fail("malformed parameter sort list"),
                    }
                }
                let ret = self.parse_type()?;
                self.expect_rparen()?;
                if params.is_empty() {
                    self.register_const(&name, &ret)?;
                } else {
                    if self.consts.contains_key(&name) || self.macros.contains_key(&name) {
                        return self.fail(format!("'{name}' is already declared"));
                    }
                    self.funs.insert(name.clone(), params.len());
                }
                Command::DeclareFun(name, params, ret)
            }
            "define-fun" => {
                let name = self.expect_symbol("a function name")?;
                self.expect_lparen()?;
                let mut params: Vec<(String, Type)> = Vec::new();
                loop {
                    match self.next_token() {
                        Some(Token::RParen) => break,
                        Some(Token::LParen) => {
                            let pname = self.expect_symbol("a parameter name")?;
                            let pty = self.parse_type()?;
                            self.expect_rparen()?;
                            params.push((pname, pty));
                        }
                        _ => return self.fail("malformed parameter list"),
                    }
                }
                let ret = self.parse_type()?;
                if self.consts.contains_key(&name)
                    || self.funs.contains_key(&name)
                    || self.macros.contains_key(&name)
                {
                    return self.fail(format!("'{name}' is already declared"));
                }
                let mut recorded = Vec::new();
                if let Some(t) = &self.peeked {
                    recorded.push(t.clone());
                }
                self.recording = Some(recorded);
                let scope: BTreeMap<String, Expr> = params
                    .iter()
                    .map(|(n, t)| (n.clone(), Expr::Var(n.clone(), t.clone())))
                    .collect();
                let saved_env = std::mem::replace(&mut self.env, vec![scope]);
                let body = self.parse_expr();
                self.env = saved_env;
                let tokens = self.recording.take().unwrap_or_default();
                let body = body?;
                self.expect_rparen()?;
                let body_tokens = first_expression(&tokens);
                self.macros.insert(
                    name.clone(),
                    Macro {
                        params: params.clone(),
                        body: body_tokens,
                    },
                );
                Command::DefineFun(name, params, ret, body)
            }
            "assert" => {
                let expr = self.parse_expr()?;
                self.expect_rparen()?;
                Command::Assert(expr)
            }
            "check-sat" => {
                self.expect_rparen()?;
                Command::CheckSat
            }
            "get-model" => {
                self.expect_rparen()?;
                Command::GetModel
            }
            "exit" => {
                self.expect_rparen()?;
                Command::Exit
            }
            "get-info"
            | "get-option"
            | "echo"
            | "get-assertions"
            | "get-assignment"
            | "get-proof"
            | "get-unsat-core"
            | "get-unsat-assumptions" => {
                self.skip_to_rparen()?;
                Command::Skipped(op)
            }
            other => return self.fail(format!("unsupported command '{other}'")),
        };
        Some(cmd)
    }

    fn lookup_local(&self, name: &str) -> Option<Expr> {
        self.env
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).cloned())
    }

    fn parse_symbol(&mut self, s: String) -> Option<Expr> {
        match s.as_str() {
            "true" => return Some(Expr::Bool(true)),
            "false" => return Some(Expr::Bool(false)),
            _ => {}
        }
        if let Some(e) = self.lookup_local(&s) {
            return Some(e);
        }
        if let Some(ty) = self.consts.get(&s) {
            return Some(Expr::Var(s, ty.clone()));
        }
        if self.macros.get(&s).is_some_and(|m| m.params.is_empty()) {
            return self.expand_macro(&s, Vec::new());
        }
        if self.strict {
            return self.fail(format!("undeclared symbol '{s}'"));
        }
        Some(Expr::Var(s, Type::Real))
    }

    fn expand_macro(&mut self, name: &str, args: Vec<Expr>) -> Option<Expr> {
        let Some(m) = self.macros.get(name).cloned() else {
            return self.fail(format!("unknown function '{name}'"));
        };
        if m.params.len() != args.len() {
            return self.fail(format!(
                "'{name}' expects {} argument(s), got {}",
                m.params.len(),
                args.len()
            ));
        }
        let scope: BTreeMap<String, Expr> =
            m.params.iter().map(|(p, _)| p.clone()).zip(args).collect();
        let saved_env = std::mem::replace(&mut self.env, vec![scope]);
        let saved_peek = self.peeked.take();
        let saved_rec = self.recording.take();
        self.injected.push(m.body.iter().cloned().collect());
        let result = self.parse_expr();
        let leftover = self.injected.pop().is_some_and(|q| !q.is_empty());
        self.env = saved_env;
        self.peeked = saved_peek;
        self.recording = saved_rec;
        if leftover {
            return self.fail(format!("internal error expanding '{name}'"));
        }
        result
    }

    /// Parses expressions up to and including the closing `)`.
    fn parse_args(&mut self) -> Option<Vec<Expr>> {
        let mut args = Vec::new();
        loop {
            match self.peek_token() {
                Some(Token::RParen) => {
                    self.next_token();
                    return Some(args);
                }
                None => return self.fail("unexpected end of input"),
                _ => args.push(self.parse_expr()?),
            }
        }
    }

    pub fn parse_expr(&mut self) -> Option<Expr> {
        match self.next_token() {
            Some(Token::Int(i)) => Some(Expr::Int(i)),
            Some(Token::BitVec(value, width)) => Some(Expr::BvConst(value, width)),
            Some(Token::Real(i, s)) => Some(Expr::Real(i, s)),
            Some(Token::BigNum(text)) => match big_number(&text) {
                Some(r) => Some(Expr::from_rational(&r)),
                None => self.fail(format!("malformed numeral '{text}'")),
            },
            Some(Token::Symbol(s)) => self.parse_symbol(s),
            Some(Token::LParen) => self.parse_list(),
            Some(Token::String(_)) => self.fail("string literals are unsupported"),
            _ => self.fail("expected an expression"),
        }
    }

    fn parse_list(&mut self) -> Option<Expr> {
        let head = self.next_token();
        match head {
            Some(Token::Symbol(op)) => match op.as_str() {
                "let" => self.parse_let(),
                "forall" | "exists" => self.parse_quantifier(op == "forall"),
                "!" => {
                    let inner = self.parse_expr()?;
                    self.skip_to_rparen()?;
                    Some(inner)
                }
                "_" => {
                    let name = self.expect_symbol("an indexed identifier")?;
                    let Some(digits) = name.strip_prefix("bv") else {
                        return self.fail(format!("unsupported indexed identifier '{name}'"));
                    };
                    let (Ok(value), Some(Token::Int(width))) =
                        (digits.parse::<u64>(), self.next_token())
                    else {
                        return self.fail("malformed (_ bvN w) literal");
                    };
                    if !(1..=MAX_PARSED_BV_WIDTH as i64).contains(&width)
                        || (width < 64 && value >> width != 0)
                    {
                        return self.fail("bit-vector literal out of range");
                    }
                    self.expect_rparen()?;
                    Some(Expr::BvConst(value, width as usize))
                }
                _ => {
                    let args = self.parse_args()?;
                    self.build_app(&op, args)
                }
            },
            Some(Token::LParen) => {
                if self.peek_token() == Some(&Token::Symbol("as".to_string())) {
                    self.next_token();
                    let what = self.expect_symbol("'const'")?;
                    if what != "const" {
                        return self.fail("unsupported 'as' qualification");
                    }
                    let ty = self.parse_type()?;
                    self.expect_rparen()?;
                    let mut args = self.parse_args()?;
                    if args.len() != 1 || !matches!(ty, Type::Array(_, _)) {
                        return self.fail("malformed constant array");
                    }
                    return Some(Expr::ConstArray(ty, Box::new(args.remove(0))));
                }
                if self.expect_symbol("'_'")? != "_" {
                    return self.fail("unsupported expression head");
                }
                let name = self.expect_symbol("an indexed operator")?;
                let mut indices = Vec::new();
                loop {
                    match self.next_token() {
                        Some(Token::Int(i)) => indices.push(i),
                        Some(Token::RParen) => break,
                        _ => return self.fail("malformed indexed operator"),
                    }
                }
                let args = self.parse_args()?;
                match (name.as_str(), indices.as_slice(), args.len()) {
                    ("extract", [h, l], 1)
                        if *l >= 0 && h >= l && *h < MAX_PARSED_BV_WIDTH as i64 =>
                    {
                        let arg = args.into_iter().next()?;
                        Some(Expr::BvExtract(*h as usize, *l as usize, Box::new(arg)))
                    }
                    _ => self.fail(format!("unsupported indexed operator '{name}'")),
                }
            }
            _ => self.fail("expected an operator"),
        }
    }

    fn parse_let(&mut self) -> Option<Expr> {
        self.expect_lparen()?;
        let mut scope = BTreeMap::new();
        loop {
            match self.next_token() {
                Some(Token::RParen) => break,
                Some(Token::LParen) => {
                    let name = self.expect_symbol("a let-bound name")?;
                    let value = self.parse_expr()?;
                    self.expect_rparen()?;
                    scope.insert(name, value);
                }
                _ => return self.fail("malformed let bindings"),
            }
        }
        self.env.push(scope);
        let body = self.parse_expr();
        self.env.pop();
        let body = body?;
        self.expect_rparen()?;
        Some(body)
    }

    fn parse_quantifier(&mut self, universal: bool) -> Option<Expr> {
        self.expect_lparen()?;
        let mut vars: Vec<(String, Type)> = Vec::new();
        loop {
            match self.next_token() {
                Some(Token::RParen) => break,
                Some(Token::LParen) => {
                    let name = self.expect_symbol("a bound variable")?;
                    let ty = self.parse_type()?;
                    self.expect_rparen()?;
                    vars.push((name, ty));
                }
                _ => return self.fail("malformed quantifier binders"),
            }
        }
        let scope: BTreeMap<String, Expr> = vars
            .iter()
            .map(|(n, t)| (n.clone(), Expr::Var(n.clone(), t.clone())))
            .collect();
        self.env.push(scope);
        let body = self.parse_expr();
        self.env.pop();
        let body = Box::new(body?);
        self.expect_rparen()?;
        Some(if universal {
            Expr::ForAll(vars, body)
        } else {
            Expr::Exists(vars, body)
        })
    }

    fn arity(&mut self, op: &str, args: &[Expr], min: usize, max: Option<usize>) -> Option<()> {
        if args.len() < min || max.is_some_and(|m| args.len() > m) {
            return self.fail(format!("wrong number of arguments to '{op}'"));
        }
        Some(())
    }

    fn chain(args: Vec<Expr>, mk: fn(Box<Expr>, Box<Expr>) -> Expr) -> Expr {
        let mut pairs: Vec<Expr> = args
            .windows(2)
            .map(|w| mk(Box::new(w[0].clone()), Box::new(w[1].clone())))
            .collect();
        if pairs.len() == 1 {
            pairs.remove(0)
        } else {
            Expr::And(pairs)
        }
    }

    fn fold_left(args: Vec<Expr>, mk: fn(Box<Expr>, Box<Expr>) -> Expr) -> Option<Expr> {
        let mut it = args.into_iter();
        let first = it.next()?;
        Some(it.fold(first, |acc, x| mk(Box::new(acc), Box::new(x))))
    }

    fn build_app(&mut self, op: &str, args: Vec<Expr>) -> Option<Expr> {
        // User-defined names shadow nothing: interpreted symbols cannot be redeclared
        // by the front end, so check macros/functions only for non-reserved heads.
        match op {
            "and" => Some(if args.is_empty() {
                Expr::Bool(true)
            } else {
                Expr::And(args)
            }),
            "or" => Some(if args.is_empty() {
                Expr::Bool(false)
            } else {
                Expr::Or(args)
            }),
            "not" => {
                self.arity(op, &args, 1, Some(1))?;
                Some(Expr::Not(Box::new(args.into_iter().next()?)))
            }
            "=>" => {
                self.arity(op, &args, 2, None)?;
                let mut it = args.into_iter().rev();
                let last = it.next()?;
                Some(it.fold(last, |acc, a| Expr::Implies(Box::new(a), Box::new(acc))))
            }
            "xor" => {
                self.arity(op, &args, 2, None)?;
                Self::fold_left(args, |a, b| Expr::Not(Box::new(Expr::Eq(a, b))))
            }
            "ite" => {
                self.arity(op, &args, 3, Some(3))?;
                let mut it = args.into_iter();
                let (c, t, e) = (it.next()?, it.next()?, it.next()?);
                Some(Expr::Ite(Box::new(c), Box::new(t), Box::new(e)))
            }
            "=" => {
                self.arity(op, &args, 2, None)?;
                Some(Self::chain(args, Expr::Eq))
            }
            "distinct" => {
                self.arity(op, &args, 2, None)?;
                let mut pairs = Vec::new();
                for i in 0..args.len() {
                    for j in (i + 1)..args.len() {
                        pairs.push(Expr::Not(Box::new(Expr::Eq(
                            Box::new(args[i].clone()),
                            Box::new(args[j].clone()),
                        ))));
                    }
                }
                Some(if pairs.len() == 1 {
                    pairs.remove(0)
                } else {
                    Expr::And(pairs)
                })
            }
            "<=" => {
                self.arity(op, &args, 2, None)?;
                Some(Self::chain(args, Expr::Le))
            }
            ">=" => {
                self.arity(op, &args, 2, None)?;
                Some(Self::chain(args, Expr::Ge))
            }
            "<" => {
                self.arity(op, &args, 2, None)?;
                Some(Self::chain(args, Expr::Lt))
            }
            ">" => {
                self.arity(op, &args, 2, None)?;
                Some(Self::chain(args, Expr::Gt))
            }
            "+" => {
                self.arity(op, &args, 1, None)?;
                Some(if args.len() == 1 {
                    args.into_iter().next()?
                } else {
                    Expr::Add(args)
                })
            }
            "-" => {
                self.arity(op, &args, 1, None)?;
                if args.len() == 1 {
                    Some(Expr::Sub(vec![Expr::Int(0), args.into_iter().next()?]))
                } else {
                    Some(Expr::Sub(args))
                }
            }
            "*" => {
                self.arity(op, &args, 1, None)?;
                Some(if args.len() == 1 {
                    args.into_iter().next()?
                } else {
                    Expr::Mul(args)
                })
            }
            "/" => {
                self.arity(op, &args, 2, None)?;
                Self::fold_left(args, Expr::Div)
            }
            "div" | "mod" => {
                self.arity(op, &args, 2, if op == "mod" { Some(2) } else { None })?;
                let mk: fn(Box<Expr>, Box<Expr>) -> Expr = if op == "div" {
                    Expr::IntDiv
                } else {
                    Expr::IntMod
                };
                Self::fold_left(args, mk)
            }
            "abs" => {
                self.arity(op, &args, 1, Some(1))?;
                let x = args.into_iter().next()?;
                Some(Expr::Ite(
                    Box::new(Expr::Ge(Box::new(x.clone()), Box::new(Expr::Int(0)))),
                    Box::new(x.clone()),
                    Box::new(Expr::Sub(vec![Expr::Int(0), x])),
                ))
            }
            "select" => {
                self.arity(op, &args, 2, Some(2))?;
                let mut it = args.into_iter();
                Some(Expr::Select(Box::new(it.next()?), Box::new(it.next()?)))
            }
            "store" => {
                self.arity(op, &args, 3, Some(3))?;
                let mut it = args.into_iter();
                Some(Expr::Store(
                    Box::new(it.next()?),
                    Box::new(it.next()?),
                    Box::new(it.next()?),
                ))
            }
            "to_real" => {
                self.arity(op, &args, 1, Some(1))?;
                args.into_iter().next()
            }
            "to_int" => {
                self.arity(op, &args, 1, Some(1))?;
                Some(Expr::ToInt(Box::new(args.into_iter().next()?)))
            }
            "is_int" => {
                self.arity(op, &args, 1, Some(1))?;
                Some(Expr::IsInt(Box::new(args.into_iter().next()?)))
            }
            "bvadd" => {
                self.arity(op, &args, 2, None)?;
                Self::fold_left(args, Expr::BvAdd)
            }
            "bvsub" => {
                self.arity(op, &args, 2, None)?;
                Self::fold_left(args, Expr::BvSub)
            }
            "bvmul" => {
                self.arity(op, &args, 2, None)?;
                Self::fold_left(args, Expr::BvMul)
            }
            "bvand" => {
                self.arity(op, &args, 2, None)?;
                Self::fold_left(args, Expr::BvAnd)
            }
            "bvor" => {
                self.arity(op, &args, 2, None)?;
                Self::fold_left(args, Expr::BvOr)
            }
            "bvxor" => {
                self.arity(op, &args, 2, None)?;
                Self::fold_left(args, Expr::BvXor)
            }
            "bvnot" => {
                self.arity(op, &args, 1, Some(1))?;
                Some(Expr::BvNot(Box::new(args.into_iter().next()?)))
            }
            "bvshl" | "bvlshr" | "bvashr" | "bvule" | "bvult" | "bvsle" | "bvslt" | "bvuge"
            | "bvugt" | "bvsge" | "bvsgt" | "concat" => {
                self.arity(op, &args, 2, Some(2))?;
                let mut it = args.into_iter();
                let (a, b) = (Box::new(it.next()?), Box::new(it.next()?));
                Some(match op {
                    "bvshl" => Expr::BvShl(a, b),
                    "bvlshr" => Expr::BvLshr(a, b),
                    "bvashr" => Expr::BvAshr(a, b),
                    "bvule" => Expr::BvUle(a, b),
                    "bvult" => Expr::BvUlt(a, b),
                    "bvsle" => Expr::BvSle(a, b),
                    "bvslt" => Expr::BvSlt(a, b),
                    "bvuge" => Expr::BvUle(b, a),
                    "bvugt" => Expr::BvUlt(b, a),
                    "bvsge" => Expr::BvSle(b, a),
                    "bvsgt" => Expr::BvSlt(b, a),
                    _ => Expr::BvConcat(a, b),
                })
            }
            _ => {
                if self.macros.contains_key(op) {
                    return self.expand_macro(op, args);
                }
                if let Some(&arity) = self.funs.get(op) {
                    if arity != args.len() {
                        return self.fail(format!(
                            "'{op}' expects {arity} argument(s), got {}",
                            args.len()
                        ));
                    }
                    return Some(Expr::App(op.to_string(), args));
                }
                // Floating-point operators are interpreted by the FP theory solver.
                if op == "fp" || op.starts_with("fp.") {
                    return Some(Expr::App(op.to_string(), args));
                }
                if self.strict {
                    return self.fail(format!("unsupported or undeclared operator '{op}'"));
                }
                Some(Expr::App(op.to_string(), args))
            }
        }
    }
}

/// The first complete expression in `tokens` (balanced parentheses).
fn first_expression(tokens: &[Token]) -> Vec<Token> {
    let mut out = Vec::new();
    let mut depth = 0usize;
    for t in tokens {
        out.push(t.clone());
        match t {
            Token::LParen => depth += 1,
            Token::RParen => depth = depth.saturating_sub(1),
            _ => {}
        }
        if depth == 0 {
            break;
        }
    }
    out
}

fn is_symbol_char(c: char) -> bool {
    c.is_alphabetic() || "~!@$%^&*_-+=<>.?/".contains(c)
}

/// Exact value of an arbitrarily long numeral or decimal (`-123`, `0.000...01`).
fn big_number(text: &str) -> Option<num_rational::BigRational> {
    use num_bigint::BigInt;
    use std::str::FromStr;
    let negative = text.starts_with('-');
    let body = text.trim_start_matches('-');
    let (whole, frac) = body.split_once('.').unwrap_or((body, ""));
    let digits = format!("{}{}", if whole.is_empty() { "0" } else { whole }, frac);
    let mut numer = BigInt::from_str(&digits).ok()?;
    if negative {
        numer = -numer;
    }
    let scale = u32::try_from(frac.len()).ok()?;
    Some(num_rational::BigRational::new(
        numer,
        BigInt::from(10u8).pow(scale),
    ))
}

fn parse_decimal_token(s: &str) -> Option<(i64, u32)> {
    let negative = s.starts_with('-');
    let body = if negative { &s[1..] } else { s };
    let (whole, frac) = body.split_once('.')?;
    if whole.is_empty() && frac.is_empty() {
        return None;
    }
    let mut digits = String::new();
    digits.push_str(if whole.is_empty() { "0" } else { whole });
    digits.push_str(frac);
    let mut mantissa = digits.parse::<i64>().ok()?;
    if negative {
        mantissa = -mantissa;
    }
    Some((mantissa, frac.len() as u32))
}

fn format_real_token(mantissa: i64, scale: u32) -> String {
    if scale == 0 {
        return mantissa.to_string();
    }
    let negative = mantissa < 0;
    let digits = mantissa.abs().to_string();
    let scale_usize = scale as usize;
    let out = if digits.len() <= scale_usize {
        let zeros = "0".repeat(scale_usize - digits.len());
        format!("0.{}{}", zeros, digits)
    } else {
        let split = digits.len() - scale_usize;
        format!("{}.{}", &digits[..split], &digits[split..])
    };
    if negative {
        format!("-{}", out)
    } else {
        out
    }
}
