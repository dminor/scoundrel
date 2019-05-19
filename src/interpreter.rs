use crate::lexer;
use crate::parser;
use std::error::Error;
use std::fmt;

pub enum Value {
    Boolean(bool),
    List(Vec<Value>),
    Number(f64),
    Str(String),
    Nil,
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::Boolean(b) => write!(f, "{}", b),
            Value::List(list) => {
                write!(f, "[")?;
                for item in list {
                    write!(f, " {}", item)?;
                }
                write!(f, " ]")
            }
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

fn truthy(value: Value) -> bool {
    match value {
        Value::Boolean(b) => b,
        Value::List(list) => {
            if list.len() == 0 {
                false
            } else {
                true
            }
        }
        Value::Number(n) => {
            if n == 0.0 {
                false
            } else {
                true
            }
        }
        Value::Str(s) => {
            if s.len() == 0 {
                false
            } else {
                true
            }
        }
        Value::Nil => false,
    }
}

fn unaryop(op: &lexer::LexedToken, value: &parser::Ast) -> Value {
    let value = eval(value);
    let mut result = Value::Nil;
    match &op.token {
        lexer::Token::Not => {
            result = Value::Boolean(!truthy(value));
        }
        lexer::Token::Minus => {
            if let Value::Number(n) = value {
                result = Value::Number(-n);
            } else {
                // TODO: signal error
            }
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
        parser::Ast::List(list) => {
            let mut result = Vec::<Value>::new();
            for item in list {
                result.push(eval(item));
            }
            Value::List(result)
        }
        parser::Ast::UnaryOp(op, v) => unaryop(op, v),
        parser::Ast::Value(t) => value(t),
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
        match parser::parse(&mut tokens) {
            Ok(ast) => match interpreter::eval(&ast) {
                interpreter::Value::Number(t) => {
                    assert_eq!(t, 2.0);
                }
                _ => assert!(false),
            },
            _ => assert!(false),
        }

        let (mut tokens, errors) = lexer::scan("-2");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 2);
        match parser::parse(&mut tokens) {
            Ok(ast) => match interpreter::eval(&ast) {
                interpreter::Value::Number(t) => {
                    assert_eq!(t, -2.0);
                }
                _ => assert!(false),
            },
            _ => assert!(false),
        }

        let (mut tokens, errors) = lexer::scan("!true");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 2);
        match parser::parse(&mut tokens) {
            Ok(ast) => match interpreter::eval(&ast) {
                interpreter::Value::Boolean(t) => {
                    assert!(!t);
                }
                _ => assert!(false),
            },
            _ => assert!(false),
        }

        let (mut tokens, errors) = lexer::scan("2+2");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 3);
        match parser::parse(&mut tokens) {
            Ok(ast) => match interpreter::eval(&ast) {
                interpreter::Value::Number(t) => {
                    assert_eq!(t, 4.0);
                }
                _ => assert!(false),
            },
            _ => assert!(false),
        }

        let (mut tokens, errors) = lexer::scan("2.2+2*5");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 5);
        match parser::parse(&mut tokens) {
            Ok(ast) => match interpreter::eval(&ast) {
                interpreter::Value::Number(t) => {
                    assert_eq!(t, 12.2);
                }
                _ => assert!(false),
            },
            _ => assert!(false),
        }

        let (mut tokens, errors) = lexer::scan("2+2<=5");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 5);
        match parser::parse(&mut tokens) {
            Ok(ast) => match interpreter::eval(&ast) {
                interpreter::Value::Boolean(b) => {
                    assert!(b);
                }
                _ => assert!(false),
            },
            _ => assert!(false),
        }

        let (mut tokens, errors) = lexer::scan("2+2>5");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 5);
        match parser::parse(&mut tokens) {
            Ok(ast) => match interpreter::eval(&ast) {
                interpreter::Value::Boolean(b) => {
                    assert!(!b);
                }
                _ => assert!(false),
            },
            _ => assert!(false),
        }

        let (mut tokens, errors) = lexer::scan("[2 2>5 3*4]");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 9);
        match parser::parse(&mut tokens) {
            Ok(ast) => match interpreter::eval(&ast) {
                interpreter::Value::List(list) => {
                    match list[0] {
                        interpreter::Value::Number(t) => {
                            assert_eq!(t, 2.0);
                        }
                        _ => assert!(false),
                    }
                    match list[1] {
                        interpreter::Value::Boolean(b) => {
                            assert!(!b);
                        }
                        _ => assert!(false),
                    }
                    match list[2] {
                        interpreter::Value::Number(t) => {
                            assert_eq!(t, 12.0);
                        }
                        _ => assert!(false),
                    }
                }
                _ => assert!(false),
            },
            _ => assert!(false),
        }
    }
}
