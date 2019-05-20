use crate::lexer;
use std::error::Error;
use std::fmt;

/*
expression     -> equality
equality       -> comparison ( ( "!=" | "==" ) comparison )*
comparison     -> addition ( ( ">" | ">=" | "<" | "<=" ) addition )*
addition       -> multiplication ( ( "+" | "-" ) multiplication )*
multiplication -> unary ( ( "/" | "*" ) unary )*
unary          -> ( "!" | "-" ) unary | value
value          -> NUMBER | STR | "false" | "true" |
                  "(" expression ")" | "[" ( expression )* "]"
*/

pub enum Ast {
    BinaryOp(lexer::LexedToken, Box<Ast>, Box<Ast>),
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

fn expression(tokens: &mut Vec<lexer::LexedToken>) -> Result<Ast, ParserError> {
    equality(tokens)
}

fn equality(tokens: &mut Vec<lexer::LexedToken>) -> Result<Ast, ParserError> {
    let lhs = comparison(tokens);
    match lhs {
        Ok(mut lhs) => {
            while tokens.len() > 0 {
                let peek = &tokens[0];
                match peek.token {
                    lexer::Token::EqualEqual | lexer::Token::NotEqual => {
                        let token = tokens.remove(0);
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
                    _ => {
                        break;
                    }
                }
            }
            Ok(lhs)
        }
        Err(e) => Err(e),
    }
}

fn comparison(tokens: &mut Vec<lexer::LexedToken>) -> Result<Ast, ParserError> {
    let lhs = addition(tokens);
    match lhs {
        Ok(mut lhs) => {
            while tokens.len() > 0 {
                let peek = &tokens[0];
                match peek.token {
                    lexer::Token::Greater
                    | lexer::Token::GreaterEqual
                    | lexer::Token::Less
                    | lexer::Token::LessEqual => {
                        let token = tokens.remove(0);
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
                    _ => {
                        break;
                    }
                }
            }
            Ok(lhs)
        }
        Err(e) => Err(e),
    }
}

fn addition(tokens: &mut Vec<lexer::LexedToken>) -> Result<Ast, ParserError> {
    let lhs = multiplication(tokens);
    match lhs {
        Ok(mut lhs) => {
            while tokens.len() > 0 {
                let peek = &tokens[0];
                match peek.token {
                    lexer::Token::Plus | lexer::Token::Minus => {
                        let token = tokens.remove(0);
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
                    _ => {
                        break;
                    }
                }
            }

            Ok(lhs)
        }
        Err(e) => Err(e),
    }
}

fn multiplication(tokens: &mut Vec<lexer::LexedToken>) -> Result<Ast, ParserError> {
    let lhs = unary(tokens);
    match lhs {
        Ok(mut lhs) => {
            while tokens.len() > 0 {
                let peek = &tokens[0];
                match peek.token {
                    lexer::Token::Slash | lexer::Token::Star => {
                        let token = tokens.remove(0);
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
                    _ => {
                        break;
                    }
                }
            }
            Ok(lhs)
        }
        Err(e) => Err(e),
    }
}

fn unary(tokens: &mut Vec<lexer::LexedToken>) -> Result<Ast, ParserError> {
    if tokens.len() == 0 {
        return Err(ParserError {
            err: "Unexpected end of input.".to_string(),
            line: 0,
            pos: 0,
        });
    }

    let peek = &tokens[0];
    match peek.token {
        lexer::Token::Minus | lexer::Token::Not => {
            let token = tokens.remove(0);
            match value(tokens) {
                Ok(n) => Ok(Ast::UnaryOp(token, Box::new(n))),
                Err(e) => Err(e),
            }
        }
        _ => value(tokens),
    }
}

fn value(tokens: &mut Vec<lexer::LexedToken>) -> Result<Ast, ParserError> {
    if tokens.len() == 0 {
        return Err(ParserError {
            err: "Unexpected end of input.".to_string(),
            line: 0,
            pos: 0,
        });
    }

    let token = tokens.remove(0);
    match token.token {
        lexer::Token::False => Ok(Ast::Value(token)),
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
                if tokens.len() == 0 {
                    return Err(ParserError {
                        err: "Unexpected end of input when looking for ].".to_string(),
                        line: token.line,
                        pos: token.pos,
                    });
                }
                let peek = &tokens[0];
                if let lexer::Token::RightBracket = peek.token {
                    tokens.remove(0);
                    break;
                }
                if let Ok(item) = expression(tokens) {
                    items.push(item);
                }
            }
            Ok(Ast::List(items))
        }
        lexer::Token::LeftParen => match expression(tokens) {
            Ok(result) => {
                if tokens.len() == 0 {
                    return Err(ParserError {
                        err: "Unexpected end of input when looking for ].".to_string(),
                        line: token.line,
                        pos: token.pos,
                    });
                }

                let next = tokens.remove(0);
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
            Err(e) => Err(e),
        },
        _ => Err(ParserError {
            err: "Expected value.".to_string(),
            line: token.line,
            pos: token.pos,
        }),
    }
}

pub fn parse(tokens: &mut Vec<lexer::LexedToken>) -> Result<Ast, ParserError> {
    expression(tokens)
}

#[cfg(test)]
mod tests {
    use crate::lexer;
    use crate::parser;

    macro_rules! scan {
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

    macro_rules! scanfails {
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
        scan!("2", 1, parser::Ast::Value, lexer::Token::Number(2.0));
        scan!("(2)", 3, parser::Ast::Value, lexer::Token::Number(2.0));
        scan!("false", 1, parser::Ast::Value, lexer::Token::False);
        scan!("true", 1, parser::Ast::Value, lexer::Token::True);
        scan!(
            "x",
            1,
            parser::Ast::Value,
            lexer::Token::Identifier("x".to_string())
        );
        scan!(
            "-2",
            2,
            parser::Ast::UnaryOp,
            lexer::Token::Minus,
            lexer::Token::Number(2.0)
        );
        scan!(
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

        scan!(
            "2<=3",
            3,
            parser::Ast::BinaryOp,
            lexer::Token::LessEqual,
            lexer::Token::Number(2.0),
            lexer::Token::Number(3.0)
        );

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

        scanfails!("", 0, "Unexpected end of input.");
        scanfails!("[", 1, "Unexpected end of input when looking for ].");
        scanfails!("(", 1, "Unexpected end of input.");
        scanfails!("(2]", 3, "Unexpected token when looking for ).");
    }
}
