use crate::lexer;
use crate::parser;
use std::error::Error;
use std::fmt;

pub enum Value {
    Boolean(bool),
    Number(f64),
    Str(String),
    Nil,
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::Boolean(b) => write!(f, "{}", b),
            Value::Number(n) => write!(f, "{}", n),
            Value::Str(s) => write!(f, "{}", s),
            Value::Nil => write!(f, "(nil)"),
        }
    }
}

macro_rules! apply_binaryop {
    (Value::Number, Value::Number, $r:ident, $lhs:ident, $rhs:ident, $op:tt) => (
        if let Value::Number(x) = $lhs {
            if let Value::Number(y) = $rhs {
                $r = Value::Number(x $op y);
            }
        }
    );
    (Value::Number, Value::Boolean, $r:ident, $lhs:ident, $rhs:ident, $op:tt) => (
        if let Value::Number(x) = $lhs {
            if let Value::Number(y) = $rhs {
                $r = Value::Boolean(x $op y);
            }
        }
    );
    (Value::Boolean, Value::Boolean, $r:ident, $lhs:ident, $rhs:ident, $op:tt) => (
        if let Value::Boolean(x) = $lhs {
            if let Value::Boolean(y) = $rhs {
                $r = Value::Boolean(x $op y);
            }
        }
    )
}

fn binaryop(op: &lexer::LexedToken, lhs: &parser::Ast, rhs: &parser::Ast) -> Value {
    let lhs = eval(lhs);
    let rhs = eval(rhs);
    let mut result = Value::Nil;
    match &op.token {
        lexer::Token::Plus => {
            apply_binaryop!(Value::Number, Value::Number, result, lhs, rhs, +);
        }
        lexer::Token::Minus => {
            apply_binaryop!(Value::Number, Value::Number, result, lhs, rhs, -);
        }
        lexer::Token::Star => {
            apply_binaryop!(Value::Number, Value::Number, result, lhs, rhs, *);
        }
        lexer::Token::Slash => {
            apply_binaryop!(Value::Number, Value::Number, result, lhs, rhs, /);
        }
        lexer::Token::EqualEqual => {
            apply_binaryop!(Value::Number, Value::Boolean, result, lhs, rhs, ==);
        }
        lexer::Token::Greater => {
            apply_binaryop!(Value::Number, Value::Boolean, result, lhs, rhs, >);
        }
        lexer::Token::GreaterEqual => {
            apply_binaryop!(Value::Number, Value::Boolean, result, lhs, rhs, >=);
        }
        lexer::Token::Less => {
            apply_binaryop!(Value::Number, Value::Boolean, result, lhs, rhs, <);
        }
        lexer::Token::LessEqual => {
            apply_binaryop!(Value::Number, Value::Boolean, result, lhs, rhs, <=);
        }
        _ => {}
    }

    result
}

fn value(token: &lexer::LexedToken) -> Value {
    match &token.token {
        lexer::Token::False => Value::Boolean(false),
        lexer::Token::True => Value::Boolean(true),
        lexer::Token::Number(n) => Value::Number(*n),
        lexer::Token::Str(s) => Value::Str(s.to_string()),
        _ => Value::Nil,
    }
}

pub fn eval(ast: &parser::Ast) -> Value {
    match ast {
        parser::Ast::BinaryOp(op, lhs, rhs) => binaryop(op, lhs, rhs),
        parser::Ast::Value(t) => value(t),
        _ => Value::Nil,
    }
}

#[cfg(test)]
mod tests {
    use crate::interpreter;
    use crate::lexer;
    use crate::parser;

    #[test]
    fn evaling() {
        let (mut tokens, errors) = lexer::scan("2");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 1);
        let ast = parser::parse(&mut tokens);
        match interpreter::eval(&ast) {
            interpreter::Value::Number(t) => {
                assert_eq!(t, 2.0);
            }
            _ => {
                assert!(false);
            }
        }

        let (mut tokens, errors) = lexer::scan("2+2");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 3);
        let ast = parser::parse(&mut tokens);
        match interpreter::eval(&ast) {
            interpreter::Value::Number(t) => {
                assert_eq!(t, 4.0);
            }
            _ => {
                assert!(false);
            }
        }

        let (mut tokens, errors) = lexer::scan("2.2+2*5");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 5);
        let ast = parser::parse(&mut tokens);
        match interpreter::eval(&ast) {
            interpreter::Value::Number(t) => {
                assert_eq!(t, 12.2);
            }
            _ => {
                assert!(false);
            }
        }

        let (mut tokens, errors) = lexer::scan("2+2<=5");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 5);
        let ast = parser::parse(&mut tokens);
        match interpreter::eval(&ast) {
            interpreter::Value::Boolean(b) => {
                assert!(b);
            }
            _ => {
                assert!(false);
            }
        }

        let (mut tokens, errors) = lexer::scan("2+2>5");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 5);
        let ast = parser::parse(&mut tokens);
        match interpreter::eval(&ast) {
            interpreter::Value::Boolean(b) => {
                assert!(!b);
            }
            _ => {
                assert!(false);
            }
        }
    }
}
