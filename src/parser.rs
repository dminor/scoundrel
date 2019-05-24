use crate::lexer;
use std::collections::LinkedList;
use std::error::Error;
use std::fmt;

/*
expression     -> "let" ( IDENTIFIER ":=" expression )* in expression end
                  | conditional
conditional    -> "if" equality "then" equality ("elsif" equality "then" equality)* ("else" equality)? "end"
                  | equality
equality       -> comparison ( ( "!=" | "==" ) comparison )*
comparison     -> addition ( ( ">" | ">=" | "<" | "<=" ) addition )*
addition       -> multiplication ( ( "+" | "-" | "or" ) multiplication )*
multiplication -> unary ( ( "/" | "*" | "mod" | "and" ) unary )*
unary          -> ( "!" | "-" ) unary | call
call           -> value ( "(" ( value ,? )* ")" )?
value          -> IDENTIFIER | NUMBER | STR | "false" | "true"
                  | "(" expression ")" | "[" ( expression )* "]"
                  | "fn" "(" ( IDENTIFIER ,? ) * ")" in expression end
*/

pub enum Ast {
    BinaryOp(lexer::LexedToken, Box<Ast>, Box<Ast>),
    Function(Vec<lexer::LexedToken>, Box<Ast>),
    FunctionCall(Box<Ast>, Vec<Ast>),
    If(Vec<(Ast, Ast)>, Box<Ast>),
    Let(Vec<(lexer::LexedToken, Ast)>, Box<Ast>),
    List(Vec<Ast>),
    UnaryOp(lexer::LexedToken, Box<Ast>),
    Value(lexer::LexedToken),
}

#[derive(Debug)]
pub struct ParserError {
    pub err: String,
    pub line: usize,
    pub pos: usize,
}

impl fmt::Display for ParserError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ParserError [Line {}]: {}", self.line, self.err)
    }
}

impl Error for ParserError {}

macro_rules! expect {
    ($tokens:expr, $token:tt, $err:expr) => {{
        match $tokens.pop_front() {
            Some(token) => match token.token {
                lexer::Token::$token => {}
                _ => {
                    return Err(ParserError {
                        err: $err,
                        line: token.line,
                        pos: token.pos,
                    });
                }
            },
            None => {
                return Err(ParserError {
                    err: "Unexpected end of input.".to_string(),
                    line: 0,
                    pos: 0,
                });
            }
        }
    };};
}

fn expression(tokens: &mut LinkedList<lexer::LexedToken>) -> Result<Ast, ParserError> {
    match tokens.front() {
        Some(peek) => match peek.token {
            lexer::Token::Let => {
                tokens.pop_front();
                let mut variables = Vec::<(lexer::LexedToken, Ast)>::new();
                loop {
                    match tokens.pop_front() {
                        Some(token) => match token.token {
                            lexer::Token::Identifier(s) => {
                                let var = lexer::LexedToken {
                                    token: lexer::Token::Identifier(s),
                                    line: token.line,
                                    pos: token.pos,
                                };
                                expect!(tokens, ColonEqual, "Expected :=.".to_string());
                                match expression(tokens) {
                                    Ok(value) => {
                                        variables.push((var, value));
                                    }
                                    Err(e) => {
                                        return Err(e);
                                    }
                                }
                            }
                            lexer::Token::In => {
                                break;
                            }
                            _ => {
                                return Err(ParserError {
                                    err: "Expected identifier.".to_string(),
                                    line: token.line,
                                    pos: token.pos,
                                });
                            }
                        },
                        None => {
                            return Err(ParserError {
                                err: "Unexpected end of input.".to_string(),
                                line: 0,
                                pos: 0,
                            });
                        }
                    }
                }
                match expression(tokens) {
                    Ok(body) => {
                        expect!(tokens, End, "Expected end.".to_string());
                        return Ok(Ast::Let(variables, Box::new(body)));
                    }
                    Err(e) => Err(e),
                }
            }
            _ => conditional(tokens),
        },
        None => {
            return Err(ParserError {
                err: "Unexpected end of input.".to_string(),
                line: 0,
                pos: 0,
            });
        }
    }
}

fn conditional(tokens: &mut LinkedList<lexer::LexedToken>) -> Result<Ast, ParserError> {
    match tokens.front() {
        Some(peek) => match peek.token {
            lexer::Token::If => {
                tokens.pop_front();
                let mut conds = Vec::<(Ast, Ast)>::new();
                loop {
                    match expression(tokens) {
                        Ok(cond) => {
                            expect!(tokens, Then, "Expected then.".to_string());
                            match equality(tokens) {
                                Ok(then) => {
                                    conds.push((cond, then));
                                }
                                Err(e) => {
                                    return Err(e);
                                }
                            }
                        }
                        Err(e) => {
                            return Err(e);
                        }
                    }
                    match tokens.pop_front() {
                        Some(token) => match token.token {
                            lexer::Token::Elsif => {
                                continue;
                            }
                            lexer::Token::Else => match expression(tokens) {
                                Ok(then) => {
                                    expect!(tokens, End, "Expected end.".to_string());
                                    return Ok(Ast::If(conds, Box::new(then)));
                                }
                                Err(e) => {
                                    return Err(e);
                                }
                            },
                            _ => {
                                return Err(ParserError {
                                    err: "Expected else.".to_string(),
                                    line: token.line,
                                    pos: token.pos,
                                });
                            }
                        },
                        None => {
                            return Err(ParserError {
                                err: "Unexpected end of input.".to_string(),
                                line: 0,
                                pos: 0,
                            });
                        }
                    }
                }
            }
            _ => equality(tokens),
        },
        None => {
            return Err(ParserError {
                err: "Unexpected end of input.".to_string(),
                line: 0,
                pos: 0,
            });
        }
    }
}

fn equality(tokens: &mut LinkedList<lexer::LexedToken>) -> Result<Ast, ParserError> {
    let lhs = comparison(tokens);
    match lhs {
        Ok(mut lhs) => {
            loop {
                match tokens.front() {
                    Some(peek) => match peek.token {
                        lexer::Token::EqualEqual | lexer::Token::NotEqual => {
                            if let Some(token) = tokens.pop_front() {
                                let rhs = comparison(tokens);
                                match rhs {
                                    Ok(rhs) => {
                                        lhs = Ast::BinaryOp(token, Box::new(lhs), Box::new(rhs));
                                    }
                                    Err(e) => {
                                        return Err(e);
                                    }
                                }
                            }
                        }
                        _ => {
                            break;
                        }
                    },
                    None => {
                        break;
                    }
                }
            }
            Ok(lhs)
        }
        Err(e) => Err(e),
    }
}

fn comparison(tokens: &mut LinkedList<lexer::LexedToken>) -> Result<Ast, ParserError> {
    let lhs = addition(tokens);
    match lhs {
        Ok(mut lhs) => {
            loop {
                match tokens.front() {
                    Some(peek) => match peek.token {
                        lexer::Token::Greater
                        | lexer::Token::GreaterEqual
                        | lexer::Token::Less
                        | lexer::Token::LessEqual => {
                            if let Some(token) = tokens.pop_front() {
                                let rhs = addition(tokens);
                                match rhs {
                                    Ok(rhs) => {
                                        lhs = Ast::BinaryOp(token, Box::new(lhs), Box::new(rhs));
                                    }
                                    Err(e) => {
                                        return Err(e);
                                    }
                                }
                            }
                        }
                        _ => {
                            break;
                        }
                    },
                    None => {
                        break;
                    }
                }
            }
            Ok(lhs)
        }
        Err(e) => Err(e),
    }
}

fn addition(tokens: &mut LinkedList<lexer::LexedToken>) -> Result<Ast, ParserError> {
    let lhs = multiplication(tokens);
    match lhs {
        Ok(mut lhs) => {
            loop {
                match tokens.front() {
                    Some(peek) => match peek.token {
                        lexer::Token::Plus | lexer::Token::Minus | lexer::Token::Or => {
                            if let Some(token) = tokens.pop_front() {
                                let rhs = multiplication(tokens);
                                match rhs {
                                    Ok(rhs) => {
                                        lhs = Ast::BinaryOp(token, Box::new(lhs), Box::new(rhs));
                                    }
                                    Err(e) => {
                                        return Err(e);
                                    }
                                }
                            }
                        }
                        _ => {
                            break;
                        }
                    },
                    None => {
                        break;
                    }
                }
            }
            Ok(lhs)
        }
        Err(e) => Err(e),
    }
}

fn multiplication(tokens: &mut LinkedList<lexer::LexedToken>) -> Result<Ast, ParserError> {
    let lhs = unary(tokens);
    match lhs {
        Ok(mut lhs) => {
            loop {
                match tokens.front() {
                    Some(peek) => match peek.token {
                        lexer::Token::Slash
                        | lexer::Token::Star
                        | lexer::Token::Mod
                        | lexer::Token::And => {
                            if let Some(token) = tokens.pop_front() {
                                let rhs = unary(tokens);
                                match rhs {
                                    Ok(rhs) => {
                                        lhs = Ast::BinaryOp(token, Box::new(lhs), Box::new(rhs));
                                    }
                                    Err(e) => {
                                        return Err(e);
                                    }
                                }
                            }
                        }
                        _ => {
                            break;
                        }
                    },
                    None => {
                        break;
                    }
                }
            }
            Ok(lhs)
        }
        Err(e) => Err(e),
    }
}

fn unary(tokens: &mut LinkedList<lexer::LexedToken>) -> Result<Ast, ParserError> {
    match tokens.front() {
        Some(peek) => {
            match peek.token {
                lexer::Token::Minus | lexer::Token::Not => {
                    if let Some(token) = tokens.pop_front() {
                        match call(tokens) {
                            Ok(n) => Ok(Ast::UnaryOp(token, Box::new(n))),
                            Err(e) => Err(e),
                        }
                    } else {
                        // Unreachable
                        return Err(ParserError {
                            err: "Unexpected end of input.".to_string(),
                            line: 0,
                            pos: 0,
                        });
                    }
                }
                _ => call(tokens),
            }
        }
        None => {
            return Err(ParserError {
                err: "Unexpected end of input.".to_string(),
                line: 0,
                pos: 0,
            });
        }
    }
}

fn call(tokens: &mut LinkedList<lexer::LexedToken>) -> Result<Ast, ParserError> {
    let v = value(tokens);

    match v {
        Ok(ast) => match tokens.front() {
            Some(peek) => match peek.token {
                lexer::Token::LeftParen => {
                    tokens.pop_front();
                    let mut args = Vec::<Ast>::new();
                    loop {
                        match tokens.front() {
                            Some(peek) => match peek.token {
                                lexer::Token::Comma => {
                                    tokens.pop_front();
                                }
                                lexer::Token::RightParen => {
                                    tokens.pop_front();
                                    break;
                                }
                                _ => {}
                            },
                            None => {
                                return Err(ParserError {
                                    err: "Unexpected end of input in function call.".to_string(),
                                    line: 0,
                                    pos: 0,
                                });
                            }
                        }
                        match expression(tokens) {
                            Ok(ast) => args.push(ast),
                            Err(err) => return Err(err),
                        }
                    }
                    Ok(Ast::FunctionCall(Box::new(ast), args))
                }
                _ => Ok(ast),
            },
            None => Ok(ast),
        },
        Err(e) => Err(e),
    }
}

fn value(tokens: &mut LinkedList<lexer::LexedToken>) -> Result<Ast, ParserError> {
    match tokens.pop_front() {
        Some(token) => match token.token {
            lexer::Token::False => Ok(Ast::Value(token)),
            lexer::Token::Function => {
                let mut variables = Vec::<lexer::LexedToken>::new();
                expect!(tokens, LeftParen, "Expected (.".to_string());
                loop {
                    match tokens.pop_front() {
                        Some(token) => match token.token {
                            lexer::Token::Identifier(s) => {
                                variables.push(lexer::LexedToken {
                                    token: lexer::Token::Identifier(s),
                                    line: token.line,
                                    pos: token.pos,
                                });
                            }
                            lexer::Token::Comma => {}
                            lexer::Token::RightParen => {
                                break;
                            }
                            _ => {
                                return Err(ParserError {
                                    err: "Expected identifier.".to_string(),
                                    line: token.line,
                                    pos: token.pos,
                                });
                            }
                        },
                        None => {
                            return Err(ParserError {
                                err: "Unexpected end of input.".to_string(),
                                line: 0,
                                pos: 0,
                            });
                        }
                    }
                }
                match expression(tokens) {
                    Ok(body) => {
                        expect!(tokens, End, "Expected end.".to_string());
                        return Ok(Ast::Function(variables, Box::new(body)));
                    }
                    Err(e) => Err(e),
                }
            }
            lexer::Token::Identifier(s) => Ok(Ast::Value(lexer::LexedToken {
                token: lexer::Token::Identifier(s),
                line: token.line,
                pos: token.pos,
            })),
            lexer::Token::True => Ok(Ast::Value(token)),
            lexer::Token::Number(_) => Ok(Ast::Value(token)),
            lexer::Token::Str(_) => Ok(Ast::Value(token)),
            lexer::Token::LeftBracket => {
                let mut items = Vec::<Ast>::new();
                loop {
                    match tokens.front() {
                        Some(peek) => {
                            if let lexer::Token::RightBracket = peek.token {
                                tokens.pop_front();
                                break;
                            }
                            if let Ok(item) = expression(tokens) {
                                items.push(item);
                            }
                        }
                        None => {
                            return Err(ParserError {
                                err: "Unexpected end of input when looking for ].".to_string(),
                                line: token.line,
                                pos: token.pos,
                            });
                        }
                    }
                }
                Ok(Ast::List(items))
            }
            lexer::Token::LeftParen => match expression(tokens) {
                Ok(result) => match tokens.pop_front() {
                    Some(next) => {
                        match next.token {
                            lexer::Token::RightParen => {}
                            _ => {
                                return Err(ParserError {
                                    err: "Unexpected token when looking for ).".to_string(),
                                    line: next.line,
                                    pos: next.pos,
                                });
                            }
                        }
                        Ok(result)
                    }
                    None => {
                        return Err(ParserError {
                            err: "Unexpected end of input when looking for ].".to_string(),
                            line: token.line,
                            pos: token.pos,
                        });
                    }
                },
                Err(e) => Err(e),
            },
            _ => {
                let mut err = "Expected value, found ".to_string();
                err.push_str(&token.token.to_string());
                err.push('.');
                Err(ParserError {
                    err: err,
                    line: token.line,
                    pos: token.pos,
                })
            }
        },
        None => {
            return Err(ParserError {
                err: "Unexpected end of input.".to_string(),
                line: 0,
                pos: 0,
            });
        }
    }
}

pub fn parse(tokens: &mut LinkedList<lexer::LexedToken>) -> Result<Ast, ParserError> {
    expression(tokens)
}

#[cfg(test)]
mod tests {
    use crate::lexer;
    use crate::parser;

    macro_rules! parse {
        ($input:expr, $len:expr, parser::Ast::Value, $value:expr) => {{
            match lexer::scan($input) {
                Ok(mut tokens) => {
                    assert_eq!(tokens.len(), $len);
                    match parser::parse(&mut tokens) {
                        Ok(parser::Ast::Value(t)) => {
                            assert_eq!(t.token, $value);
                        }
                        _ => assert!(false),
                    }
                }
                _ => assert!(false),
            }
        }};
        ($input:expr, $len:expr, parser::Ast::UnaryOp, $op:expr, $value:expr) => {{
            match lexer::scan($input) {
                Ok(mut tokens) => {
                    assert_eq!(tokens.len(), $len);
                    match parser::parse(&mut tokens) {
                        Ok(parser::Ast::UnaryOp(op, t)) => {
                            assert_eq!(op.token, $op);
                            match *t {
                                parser::Ast::Value(t) => {
                                    assert_eq!(t.token, $value);
                                }
                                _ => assert!(false),
                            }
                        }
                        _ => assert!(false),
                    }
                }
                _ => assert!(false),
            }
        }};
        ($input:expr, $len:expr, parser::Ast::BinaryOp, $op:expr, $lhs:expr, $rhs:expr) => {{
            match lexer::scan($input) {
                Ok(mut tokens) => {
                    assert_eq!(tokens.len(), $len);
                    match parser::parse(&mut tokens) {
                        Ok(parser::Ast::BinaryOp(op, lhs, rhs)) => {
                            assert_eq!(op.token, $op);
                            match *lhs {
                                parser::Ast::Value(t) => {
                                    assert_eq!(t.token, $lhs);
                                }
                                _ => assert!(false),
                            }
                            match *rhs {
                                parser::Ast::Value(t) => {
                                    assert_eq!(t.token, $rhs);
                                }
                                _ => assert!(false),
                            }
                        }
                        _ => assert!(false),
                    }
                }
                _ => assert!(false),
            }
        }};
    }

    macro_rules! parsefails {
        ($input:expr, $len:expr, $err:tt) => {{
            match lexer::scan($input) {
                Ok(mut tokens) => {
                    assert_eq!(tokens.len(), $len);
                    match parser::parse(&mut tokens) {
                        Ok(_) => assert!(false),
                        Err(e) => assert!(e.err.starts_with($err)),
                    }
                }
                _ => assert!(false),
            }
        }};
    }

    #[test]
    fn parsing() {
        parse!("2", 1, parser::Ast::Value, lexer::Token::Number(2.0));
        parse!("(2)", 3, parser::Ast::Value, lexer::Token::Number(2.0));
        parse!("false", 1, parser::Ast::Value, lexer::Token::False);
        parse!("true", 1, parser::Ast::Value, lexer::Token::True);
        parse!(
            "x",
            1,
            parser::Ast::Value,
            lexer::Token::Identifier("x".to_string())
        );
        parse!(
            "-2",
            2,
            parser::Ast::UnaryOp,
            lexer::Token::Minus,
            lexer::Token::Number(2.0)
        );
        parse!(
            "not true",
            2,
            parser::Ast::UnaryOp,
            lexer::Token::Not,
            lexer::Token::True
        );

        match lexer::scan("2*2/5") {
            Ok(mut tokens) => {
                assert_eq!(tokens.len(), 5);
                match parser::parse(&mut tokens) {
                    Ok(ast) => match ast {
                        parser::Ast::BinaryOp(op, lhs, rhs) => {
                            assert_eq!(op.token, lexer::Token::Slash);
                            match *lhs {
                                parser::Ast::BinaryOp(op, lhs, rhs) => {
                                    assert_eq!(op.token, lexer::Token::Star);
                                    match *lhs {
                                        parser::Ast::Value(t) => {
                                            assert_eq!(t.token, lexer::Token::Number(2.0));
                                        }
                                        _ => assert!(false),
                                    }
                                    match *rhs {
                                        parser::Ast::Value(t) => {
                                            assert_eq!(t.token, lexer::Token::Number(2.0));
                                        }
                                        _ => assert!(false),
                                    }
                                }
                                _ => assert!(false),
                            }
                            match *rhs {
                                parser::Ast::Value(t) => {
                                    assert_eq!(t.token, lexer::Token::Number(5.0));
                                }
                                _ => assert!(false),
                            }
                        }
                        _ => assert!(false),
                    },
                    _ => assert!(false),
                }
            }
            _ => assert!(false),
        }

        match lexer::scan("2+5/2") {
            Ok(mut tokens) => {
                assert_eq!(tokens.len(), 5);
                match parser::parse(&mut tokens) {
                    Ok(ast) => match ast {
                        parser::Ast::BinaryOp(op, lhs, rhs) => {
                            assert_eq!(op.token, lexer::Token::Plus);
                            match *lhs {
                                parser::Ast::Value(t) => {
                                    assert_eq!(t.token, lexer::Token::Number(2.0));
                                }
                                _ => assert!(false),
                            }
                            match *rhs {
                                parser::Ast::BinaryOp(op, lhs, rhs) => {
                                    assert_eq!(op.token, lexer::Token::Slash);
                                    match *lhs {
                                        parser::Ast::Value(t) => {
                                            assert_eq!(t.token, lexer::Token::Number(5.0));
                                        }
                                        _ => assert!(false),
                                    }
                                    match *rhs {
                                        parser::Ast::Value(t) => {
                                            assert_eq!(t.token, lexer::Token::Number(2.0));
                                        }
                                        _ => assert!(false),
                                    }
                                }
                                _ => assert!(false),
                            }
                        }
                        _ => assert!(false),
                    },
                    _ => assert!(false),
                }
            }
            _ => assert!(false),
        }

        parse!(
            "2<=3",
            3,
            parser::Ast::BinaryOp,
            lexer::Token::LessEqual,
            lexer::Token::Number(2.0),
            lexer::Token::Number(3.0)
        );

        parse!(
            "true or false",
            3,
            parser::Ast::BinaryOp,
            lexer::Token::Or,
            lexer::Token::True,
            lexer::Token::False
        );

        match lexer::scan("x and y or false") {
            Ok(mut tokens) => {
                assert_eq!(tokens.len(), 5);
                match parser::parse(&mut tokens) {
                    Ok(ast) => match ast {
                        parser::Ast::BinaryOp(op, lhs, rhs) => {
                            assert_eq!(op.token, lexer::Token::Or);
                            match *lhs {
                                parser::Ast::BinaryOp(op, lhs, rhs) => {
                                    assert_eq!(op.token, lexer::Token::And);
                                    match *lhs {
                                        parser::Ast::Value(t) => {
                                            assert_eq!(
                                                t.token,
                                                lexer::Token::Identifier("x".to_string())
                                            );
                                        }
                                        _ => assert!(false),
                                    }
                                    match *rhs {
                                        parser::Ast::Value(t) => {
                                            assert_eq!(
                                                t.token,
                                                lexer::Token::Identifier("y".to_string())
                                            );
                                        }
                                        _ => assert!(false),
                                    }
                                }
                                _ => assert!(false),
                            }
                            match *rhs {
                                parser::Ast::Value(t) => {
                                    assert_eq!(t.token, lexer::Token::False);
                                }
                                _ => assert!(false),
                            }
                        }
                        _ => assert!(false),
                    },
                    _ => assert!(false),
                }
            }
            _ => assert!(false),
        }

        match lexer::scan("x == y <> false") {
            Ok(mut tokens) => {
                assert_eq!(tokens.len(), 5);
                match parser::parse(&mut tokens) {
                    Ok(ast) => match ast {
                        parser::Ast::BinaryOp(op, lhs, rhs) => {
                            assert_eq!(op.token, lexer::Token::NotEqual);
                            match *lhs {
                                parser::Ast::BinaryOp(op, lhs, rhs) => {
                                    assert_eq!(op.token, lexer::Token::EqualEqual);
                                    match *lhs {
                                        parser::Ast::Value(t) => {
                                            assert_eq!(
                                                t.token,
                                                lexer::Token::Identifier("x".to_string())
                                            );
                                        }
                                        _ => assert!(false),
                                    }
                                    match *rhs {
                                        parser::Ast::Value(t) => {
                                            assert_eq!(
                                                t.token,
                                                lexer::Token::Identifier("y".to_string())
                                            );
                                        }
                                        _ => assert!(false),
                                    }
                                }
                                _ => assert!(false),
                            }
                            match *rhs {
                                parser::Ast::Value(t) => {
                                    assert_eq!(t.token, lexer::Token::False);
                                }
                                _ => assert!(false),
                            }
                        }
                        _ => assert!(false),
                    },
                    _ => assert!(false),
                }
            }
            _ => assert!(false),
        }

        match lexer::scan("[]") {
            Ok(mut tokens) => {
                assert_eq!(tokens.len(), 2);
                match parser::parse(&mut tokens) {
                    Ok(ast) => match ast {
                        parser::Ast::List(l) => {
                            assert_eq!(l.len(), 0);
                        }
                        _ => assert!(false),
                    },
                    _ => assert!(false),
                }
            }
            _ => assert!(false),
        }

        match lexer::scan("[2]") {
            Ok(mut tokens) => {
                assert_eq!(tokens.len(), 3);
                match parser::parse(&mut tokens) {
                    Ok(ast) => match ast {
                        parser::Ast::List(l) => {
                            assert_eq!(l.len(), 1);
                            match &l[0] {
                                parser::Ast::Value(t) => {
                                    assert_eq!(t.token, lexer::Token::Number(2.0));
                                }
                                _ => assert!(false),
                            }
                        }
                        _ => assert!(false),
                    },
                    _ => assert!(false),
                }
            }
            _ => assert!(false),
        }

        match lexer::scan("[1 2 3]") {
            Ok(mut tokens) => {
                assert_eq!(tokens.len(), 5);
                match parser::parse(&mut tokens) {
                    Ok(ast) => match ast {
                        parser::Ast::List(l) => {
                            assert_eq!(l.len(), 3);
                            match &l[0] {
                                parser::Ast::Value(t) => {
                                    assert_eq!(t.token, lexer::Token::Number(1.0));
                                }
                                _ => assert!(false),
                            }
                            match &l[1] {
                                parser::Ast::Value(t) => {
                                    assert_eq!(t.token, lexer::Token::Number(2.0));
                                }
                                _ => assert!(false),
                            }
                            match &l[2] {
                                parser::Ast::Value(t) => {
                                    assert_eq!(t.token, lexer::Token::Number(3.0));
                                }
                                _ => assert!(false),
                            }
                        }
                        _ => assert!(false),
                    },
                    _ => assert!(false),
                }
            }
            _ => assert!(false),
        }

        parsefails!("", 0, "Unexpected end of input.");
        parsefails!("[", 1, "Unexpected end of input when looking for ].");
        parsefails!("(", 1, "Unexpected end of input.");
        parsefails!("(2]", 3, "Unexpected token when looking for ).");
        parsefails!("true or", 2, "Unexpected end of input.");

        match lexer::scan("if true then 1 elsif false then 2 else 3 end") {
            Ok(mut tokens) => {
                assert_eq!(tokens.len(), 11);
                match parser::parse(&mut tokens) {
                    Ok(ast) => match ast {
                        parser::Ast::If(conds, then) => {
                            assert_eq!(conds.len(), 2);
                            match &conds[0] {
                                (parser::Ast::Value(cond), parser::Ast::Value(then)) => {
                                    assert_eq!(cond.token, lexer::Token::True);
                                    assert_eq!(then.token, lexer::Token::Number(1.0));
                                }
                                _ => assert!(false),
                            }
                            match &conds[1] {
                                (parser::Ast::Value(cond), parser::Ast::Value(then)) => {
                                    assert_eq!(cond.token, lexer::Token::False);
                                    assert_eq!(then.token, lexer::Token::Number(2.0));
                                }
                                _ => assert!(false),
                            }
                            match *then {
                                parser::Ast::Value(t) => {
                                    assert_eq!(t.token, lexer::Token::Number(3.0));
                                }
                                _ => assert!(false),
                            }
                        }
                        _ => assert!(false),
                    },
                    _ => assert!(false),
                }
            }
            _ => assert!(false),
        }

        match lexer::scan("let x := 1 in x end") {
            Ok(mut tokens) => {
                assert_eq!(tokens.len(), 7);
                match parser::parse(&mut tokens) {
                    Ok(ast) => match ast {
                        parser::Ast::Let(vars, expr) => {
                            assert_eq!(vars.len(), 1);
                            assert_eq!(vars[0].0.token, lexer::Token::Identifier("x".to_string()));
                            match &vars[0].1 {
                                parser::Ast::Value(t) => {
                                    assert_eq!(t.token, lexer::Token::Number(1.0));
                                }
                                _ => assert!(false),
                            }
                            match *expr {
                                parser::Ast::Value(t) => {
                                    assert_eq!(t.token, lexer::Token::Identifier("x".to_string()));
                                }
                                _ => assert!(false),
                            }
                        }
                        _ => assert!(false),
                    },
                    _ => assert!(false),
                }
            }
            _ => assert!(false),
        }

        match lexer::scan("fn (x, y) x + y end") {
            Ok(mut tokens) => {
                assert_eq!(tokens.len(), 10);
                match parser::parse(&mut tokens) {
                    Ok(ast) => match ast {
                        parser::Ast::Function(args, body) => {
                            assert_eq!(args.len(), 2);
                            assert_eq!(args[0].token, lexer::Token::Identifier("x".to_string()));
                            assert_eq!(args[1].token, lexer::Token::Identifier("y".to_string()));
                            match *body {
                                parser::Ast::BinaryOp(op, lhs, rhs) => {
                                    assert_eq!(op.token, lexer::Token::Plus);
                                    match *lhs {
                                        parser::Ast::Value(t) => {
                                            assert_eq!(
                                                t.token,
                                                lexer::Token::Identifier("x".to_string())
                                            );
                                        }
                                        _ => assert!(false),
                                    }
                                    match *rhs {
                                        parser::Ast::Value(t) => {
                                            assert_eq!(
                                                t.token,
                                                lexer::Token::Identifier("y".to_string())
                                            );
                                        }
                                        _ => assert!(false),
                                    }
                                }
                                _ => assert!(false),
                            }
                        }
                        _ => assert!(false),
                    },
                    _ => assert!(false),
                }
            }
            _ => assert!(false),
        }
        match lexer::scan("fn (x, y) x + y end (2, 3)") {
            Ok(mut tokens) => {
                assert_eq!(tokens.len(), 15);
                match parser::parse(&mut tokens) {
                    Ok(ast) => match ast {
                        parser::Ast::FunctionCall(func, args) => {
                            match *func {
                                parser::Ast::Function(args, body) => {
                                    assert_eq!(args.len(), 2);
                                    assert_eq!(
                                        args[0].token,
                                        lexer::Token::Identifier("x".to_string())
                                    );
                                    assert_eq!(
                                        args[1].token,
                                        lexer::Token::Identifier("y".to_string())
                                    );
                                    match *body {
                                        parser::Ast::BinaryOp(op, lhs, rhs) => {
                                            assert_eq!(op.token, lexer::Token::Plus);
                                            match *lhs {
                                                parser::Ast::Value(t) => {
                                                    assert_eq!(
                                                        t.token,
                                                        lexer::Token::Identifier("x".to_string())
                                                    );
                                                }
                                                _ => assert!(false),
                                            }
                                            match *rhs {
                                                parser::Ast::Value(t) => {
                                                    assert_eq!(
                                                        t.token,
                                                        lexer::Token::Identifier("y".to_string())
                                                    );
                                                }
                                                _ => assert!(false),
                                            }
                                        }
                                        _ => assert!(false),
                                    }
                                }
                                _ => assert!(false),
                            }
                            assert_eq!(args.len(), 2);
                            match &args[0] {
                                parser::Ast::Value(t) => {
                                    assert_eq!(t.token, lexer::Token::Number(2.0));
                                }
                                _ => assert!(false),
                            }
                            match &args[1] {
                                parser::Ast::Value(t) => {
                                    assert_eq!(t.token, lexer::Token::Number(3.0));
                                }
                                _ => assert!(false),
                            }
                        }
                        _ => assert!(false),
                    },
                    _ => assert!(false),
                }
            }
            _ => assert!(false),
        }
    }
}
