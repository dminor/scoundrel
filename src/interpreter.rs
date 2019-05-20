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

#[derive(Debug)]
pub struct RuntimeError {
    pub err: String,
    pub line: usize,
    pub pos: usize,
}

impl fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "RuntimeError [Line {}]: {}", self.line, self.err)
    }
}

impl Error for RuntimeError {}

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

fn binaryop(
    op: &lexer::LexedToken,
    lhs: &parser::Ast,
    rhs: &parser::Ast,
) -> Result<Value, RuntimeError> {
    match eval(lhs) {
        Ok(lhs) => match eval(rhs) {
            Ok(rhs) => {
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
                    _ => {
                        return Err(RuntimeError {
                            err: "Internal error: invalid binary operation.".to_string(),
                            line: op.line,
                            pos: op.pos,
                        });
                    }
                }
                Ok(result)
            }
            Err(e) => Err(e),
        },
        Err(e) => Err(e),
    }
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

fn unaryop(op: &lexer::LexedToken, value: &parser::Ast) -> Result<Value, RuntimeError> {
    match eval(value) {
        Ok(value) => {
            let mut result = Value::Nil;
            match &op.token {
                lexer::Token::Not => Ok(Value::Boolean(!truthy(value))),
                lexer::Token::Minus => {
                    if let Value::Number(n) = value {
                        result = Value::Number(-n);
                    } else {
                        // TODO: signal error
                    }
                    Ok(result)
                }
                _ => Err(RuntimeError {
                    err: "Internal error: token has no value.".to_string(),
                    line: op.line,
                    pos: op.pos,
                }),
            }
        }
        Err(e) => Err(e),
    }
}

fn value(token: &lexer::LexedToken) -> Result<Value, RuntimeError> {
    match &token.token {
        lexer::Token::False => Ok(Value::Boolean(false)),
        lexer::Token::True => Ok(Value::Boolean(true)),
        lexer::Token::Number(n) => Ok(Value::Number(*n)),
        lexer::Token::Str(s) => Ok(Value::Str(s.to_string())),
        _ => Err(RuntimeError {
            err: "Internal error: token has no value.".to_string(),
            line: token.line,
            pos: token.pos,
        }),
    }
}

pub fn eval(ast: &parser::Ast) -> Result<Value, RuntimeError> {
    match ast {
        parser::Ast::BinaryOp(op, lhs, rhs) => binaryop(op, lhs, rhs),
        parser::Ast::List(list) => {
            let mut result = Vec::<Value>::new();
            for item in list {
                match eval(item) {
                    Ok(v) => result.push(v),
                    Err(e) => {
                        return Err(e);
                    }
                }
            }
            Ok(Value::List(result))
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

    macro_rules! testeval {
        ($input:expr, $type:tt, $value:expr) => {{
            match lexer::scan($input) {
                Ok(mut tokens) => match parser::parse(&mut tokens) {
                    Ok(ast) => match interpreter::eval(&ast) {
                        Ok(v) => match v {
                            interpreter::Value::$type(t) => {
                                assert_eq!(t, $value);
                            }
                            _ => assert!(false),
                        },
                        _ => assert!(false),
                    },
                    _ => assert!(false),
                },
                _ => assert!(false),
            }
        }};
    }

    #[test]
    fn evaling() {
        testeval!("2", Number, 2.0);
        testeval!("-2", Number, -2.0);
        testeval!("!true", Boolean, false);
        testeval!("2+2", Number, 4.0);
        testeval!("2.2+2*5", Number, 12.2);
        testeval!("2+2<=5", Boolean, true);
        testeval!("2+2>5", Boolean, false);

        match lexer::scan("[2 2>5 3*4]") {
            Ok(mut tokens) => {
                assert_eq!(tokens.len(), 9);
                match parser::parse(&mut tokens) {
                    Ok(ast) => match interpreter::eval(&ast) {
                        Ok(v) => match v {
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
                    },
                    _ => assert!(false),
                }
            }
            _ => assert!(false),
        }
    }
}
