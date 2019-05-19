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
                  "(" expression ")"
*/

pub enum Ast {
    BinaryOp(lexer::LexedToken, Box<Ast>, Box<Ast>),
    List(Vec<Ast>),
    UnaryOp(lexer::LexedToken, Box<Ast>),
    Value(lexer::LexedToken),
    None,
}

#[derive(Debug)]
pub struct ParserError {
    pub err: String,
    pub line: usize,
    pub pos: usize,
}

impl fmt::Display for ParserError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ParserError: line {} msg {}", self.line, self.err)
    }
}

impl Error for ParserError {}

fn expression(tokens: &mut Vec<lexer::LexedToken>) -> Ast {
    equality(tokens)
}

fn equality(tokens: &mut Vec<lexer::LexedToken>) -> Ast {
    let mut lhs = comparison(tokens);
    while tokens.len() > 0 {
        let peek = &tokens[0];
        match peek.token {
            lexer::Token::EqualEqual | lexer::Token::NotEqual => {
                let token = tokens.remove(0);
                let rhs = comparison(tokens);
                lhs = Ast::BinaryOp(token, Box::new(lhs), Box::new(rhs));
            }
            _ => {
                break;
            }
        }
    }

    lhs
}

fn comparison(tokens: &mut Vec<lexer::LexedToken>) -> Ast {
    let mut lhs = addition(tokens);
    while tokens.len() > 0 {
        let peek = &tokens[0];
        match peek.token {
            lexer::Token::Greater
            | lexer::Token::GreaterEqual
            | lexer::Token::Less
            | lexer::Token::LessEqual => {
                let token = tokens.remove(0);
                let rhs = addition(tokens);
                lhs = Ast::BinaryOp(token, Box::new(lhs), Box::new(rhs));
            }
            _ => {
                break;
            }
        }
    }

    lhs
}

fn addition(tokens: &mut Vec<lexer::LexedToken>) -> Ast {
    let mut lhs = multiplication(tokens);
    while tokens.len() > 0 {
        let peek = &tokens[0];
        match peek.token {
            lexer::Token::Plus | lexer::Token::Minus => {
                let token = tokens.remove(0);
                let rhs = multiplication(tokens);
                lhs = Ast::BinaryOp(token, Box::new(lhs), Box::new(rhs));
            }
            _ => {
                break;
            }
        }
    }

    lhs
}

fn multiplication(tokens: &mut Vec<lexer::LexedToken>) -> Ast {
    let mut lhs = unary(tokens);
    while tokens.len() > 0 {
        let peek = &tokens[0];
        match peek.token {
            lexer::Token::Slash | lexer::Token::Star => {
                let token = tokens.remove(0);
                let rhs = unary(tokens);
                lhs = Ast::BinaryOp(token, Box::new(lhs), Box::new(rhs));
            }
            _ => {
                break;
            }
        }
    }

    lhs
}

fn unary(tokens: &mut Vec<lexer::LexedToken>) -> Ast {
    let peek = &tokens[0];
    match peek.token {
        lexer::Token::Minus => {
            let token = tokens.remove(0);
            Ast::UnaryOp(token, Box::new(value(tokens)))
        }
        lexer::Token::Not => {
            let token = tokens.remove(0);
            Ast::UnaryOp(token, Box::new(value(tokens)))
        }
        _ => value(tokens),
    }
}

fn value(tokens: &mut Vec<lexer::LexedToken>) -> Ast {
    let token = tokens.remove(0);
    match token.token {
        lexer::Token::False => Ast::Value(token),
        lexer::Token::Identifier(s) => Ast::Value(lexer::LexedToken {
            token: lexer::Token::Identifier(s),
            line: token.line,
            pos: token.pos,
        }),
        lexer::Token::True => Ast::Value(token),
        lexer::Token::Number(_) => Ast::Value(token),
        lexer::Token::Str(_) => Ast::Value(token),
        lexer::Token::LeftParen => {
            let result = expression(tokens);
            let next = tokens.remove(0);
            match next.token {
                lexer::Token::RightParen => {}
                _ => {} // TODO: signal error
            }
            result
        }
        _ => Ast::None // TODO: signal error,
    }
}

pub fn parse(tokens: &mut Vec<lexer::LexedToken>) -> Ast {
    expression(tokens)
}

#[cfg(test)]
mod tests {
    use crate::lexer;
    use crate::parser;

    #[test]
    fn parsing() {
        let (mut tokens, errors) = lexer::scan("2");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 1);
        let ast = parser::parse(&mut tokens);
        match ast {
            parser::Ast::Value(t) => {
                assert_eq!(t.token, lexer::Token::Number(2.0));
            }
            _ => {
                assert!(false);
            }
        }

        let (mut tokens, errors) = lexer::scan("(2)");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 3);
        let ast = parser::parse(&mut tokens);
        match ast {
            parser::Ast::Value(t) => {
                assert_eq!(t.token, lexer::Token::Number(2.0));
            }
            _ => {
                assert!(false);
            }
        }

        let (mut tokens, errors) = lexer::scan("false");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 1);
        let ast = parser::parse(&mut tokens);
        match ast {
            parser::Ast::Value(t) => {
                assert_eq!(t.token, lexer::Token::False);
            }
            _ => {
                assert!(false);
            }
        }

        let (mut tokens, errors) = lexer::scan("true");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 1);
        let ast = parser::parse(&mut tokens);
        match ast {
            parser::Ast::Value(t) => {
                assert_eq!(t.token, lexer::Token::True);
            }
            _ => {
                assert!(false);
            }
        }

        let (mut tokens, errors) = lexer::scan("x");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 1);
        let ast = parser::parse(&mut tokens);
        match ast {
            parser::Ast::Value(t) => {
                assert_eq!(t.token, lexer::Token::Identifier("x".to_string()));
            }
            _ => {
                assert!(false);
            }
        }

        let (mut tokens, errors) = lexer::scan("-2");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 2);
        let ast = parser::parse(&mut tokens);
        match ast {
            parser::Ast::UnaryOp(op, t) => {
                assert_eq!(op.token, lexer::Token::Minus);
                match *t {
                    parser::Ast::Value(t) => {
                        assert_eq!(t.token, lexer::Token::Number(2.0));
                    }
                    _ => {
                        assert!(false);
                    }
                }
            }
            _ => {
                assert!(false);
            }
        }

        let (mut tokens, errors) = lexer::scan("!true");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 2);
        let ast = parser::parse(&mut tokens);
        match ast {
            parser::Ast::UnaryOp(op, t) => {
                assert_eq!(op.token, lexer::Token::Not);
                match *t {
                    parser::Ast::Value(t) => {
                        assert_eq!(t.token, lexer::Token::True);
                    }
                    _ => {
                        assert!(false);
                    }
                }
            }
            _ => {
                assert!(false);
            }
        }

        let (mut tokens, errors) = lexer::scan("2*2/5");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 5);
        let ast = parser::parse(&mut tokens);
        match ast {
            parser::Ast::BinaryOp(op, lhs, rhs) => {
                assert_eq!(op.token, lexer::Token::Slash);
                match *lhs {
                    parser::Ast::BinaryOp(op, lhs, rhs) => {
                        assert_eq!(op.token, lexer::Token::Star);
                        match *lhs {
                            parser::Ast::Value(t) => {
                                assert_eq!(t.token, lexer::Token::Number(2.0));
                            }
                            _ => {
                                assert!(false);
                            }
                        }
                        match *rhs {
                            parser::Ast::Value(t) => {
                                assert_eq!(t.token, lexer::Token::Number(2.0));
                            }
                            _ => {
                                assert!(false);
                            }
                        }
                    }
                    _ => {
                        assert!(false);
                    }
                }
                match *rhs {
                    parser::Ast::Value(t) => {
                        assert_eq!(t.token, lexer::Token::Number(5.0));
                    }
                    _ => {
                        assert!(false);
                    }
                }
            }
            _ => {
                assert!(false);
            }
        }

        let (mut tokens, errors) = lexer::scan("2+5/2");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 5);
        let ast = parser::parse(&mut tokens);
        match ast {
            parser::Ast::BinaryOp(op, lhs, rhs) => {
                assert_eq!(op.token, lexer::Token::Plus);
                match *lhs {
                    parser::Ast::Value(t) => {
                        assert_eq!(t.token, lexer::Token::Number(2.0));
                    }
                    _ => {
                        assert!(false);
                    }
                }
                match *rhs {
                    parser::Ast::BinaryOp(op, lhs, rhs) => {
                        assert_eq!(op.token, lexer::Token::Slash);
                        match *lhs {
                            parser::Ast::Value(t) => {
                                assert_eq!(t.token, lexer::Token::Number(5.0));
                            }
                            _ => {
                                assert!(false);
                            }
                        }
                        match *rhs {
                            parser::Ast::Value(t) => {
                                assert_eq!(t.token, lexer::Token::Number(2.0));
                            }
                            _ => {
                                assert!(false);
                            }
                        }
                    }
                    _ => {
                        assert!(false);
                    }
                }
            }
            _ => {
                assert!(false);
            }
        }

        let (mut tokens, errors) = lexer::scan("2<=3");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 3);
        let ast = parser::parse(&mut tokens);
        match ast {
            parser::Ast::BinaryOp(op, lhs, rhs) => {
                assert_eq!(op.token, lexer::Token::LessEqual);
                match *lhs {
                    parser::Ast::Value(t) => {
                        assert_eq!(t.token, lexer::Token::Number(2.0));
                    }
                    _ => {
                        assert!(false);
                    }
                }
                match *rhs {
                    parser::Ast::Value(t) => {
                        assert_eq!(t.token, lexer::Token::Number(3.0));
                    }
                    _ => {
                        assert!(false);
                    }
                }
            }
            _ => {
                assert!(false);
            }
        }

        let (mut tokens, errors) = lexer::scan("x == y != false");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 5);
        let ast = parser::parse(&mut tokens);
        match ast {
            parser::Ast::BinaryOp(op, lhs, rhs) => {
                assert_eq!(op.token, lexer::Token::NotEqual);
                match *lhs {
                    parser::Ast::BinaryOp(op, lhs, rhs) => {
                        assert_eq!(op.token, lexer::Token::EqualEqual);
                        match *lhs {
                            parser::Ast::Value(t) => {
                                assert_eq!(t.token, lexer::Token::Identifier("x".to_string()));
                            }
                            _ => {
                                assert!(false);
                            }
                        }
                        match *rhs {
                            parser::Ast::Value(t) => {
                                assert_eq!(t.token, lexer::Token::Identifier("y".to_string()));
                            }
                            _ => {
                                assert!(false);
                            }
                        }
                    }
                    _ => {
                        assert!(false);
                    }
                }
                match *rhs {
                    parser::Ast::Value(t) => {
                        assert_eq!(t.token, lexer::Token::False);
                    }
                    _ => {
                        assert!(false);
                    }
                }
            }
            _ => {
                assert!(false);
            }
        }
    }
}
