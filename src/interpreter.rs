use crate::lexer;
use crate::parser;
use std::collections::LinkedList;
use std::error::Error;
use std::fmt;

#[derive(Clone)]
pub enum Value {
    Boolean(bool),
    List(LinkedList<Value>),
    Number(f64),
    Str(String),
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
        }
    }
}

macro_rules! maybe_apply_op {
    ($in:tt, $out:tt, $r:ident, $lhs:ident, $rhs:ident, $rustop:tt, $err:expr, $op:ident) => (
        if let Value::$in(x) = $lhs {
            if let Value::$in(y) = $rhs {
                return Ok(Value::$out(x $rustop y));
            } else {
                let mut err = "Type mismatch, expected ".to_string();
                err.push_str($err);
                err.push('.');
                return Err(RuntimeError {
                    err: err,
                    line: $op.line,
                    pos: $op.pos,
                });
            }
        }
    );
}

fn binaryop(
    op: &lexer::LexedToken,
    lhs: &parser::Ast,
    rhs: &parser::Ast,
) -> Result<Value, RuntimeError> {
    match eval(lhs) {
        Ok(lhs) => match &op.token {
            lexer::Token::And => {
                if truthy(lhs) {
                    match eval(rhs) {
                        Ok(rhs) => {
                            return Ok(Value::Boolean(truthy(rhs)));
                        }
                        Err(e) => Err(e),
                    }
                } else {
                    return Ok(Value::Boolean(false));
                }
            }
            lexer::Token::Or => {
                if truthy(lhs) {
                    return Ok(Value::Boolean(true));
                } else {
                    match eval(rhs) {
                        Ok(rhs) => {
                            return Ok(Value::Boolean(truthy(rhs)));
                        }
                        Err(e) => Err(e),
                    }
                }
            }
            _ => match eval(rhs) {
                Ok(rhs) => {
                    match &op.token {
                        lexer::Token::Plus => {
                            if let Value::List(x) = lhs {
                                if let Value::List(y) = rhs {
                                    let mut l = LinkedList::<Value>::new();
                                    l.extend(x.clone());
                                    l.extend(y.clone());
                                    return Ok(Value::List(l));
                                } else {
                                    return Err(RuntimeError {
                                        err: "Type mismatch, expected list.".to_string(),
                                        line: op.line,
                                        pos: op.pos,
                                    });
                                }
                            }
                            maybe_apply_op!(Number, Number, result, lhs, rhs, +, "number", op);
                            if let Value::Str(x) = lhs {
                                if let Value::Str(y) = rhs {
                                    return Ok(Value::Str(x + &y));
                                } else {
                                    return Err(RuntimeError {
                                        err: "Type mismatch, expected string.".to_string(),
                                        line: op.line,
                                        pos: op.pos,
                                    });
                                }
                            }
                        }
                        lexer::Token::Minus => {
                            maybe_apply_op!(Number, Number, result, lhs, rhs, -, "number", op);
                        }
                        lexer::Token::Star => {
                            maybe_apply_op!(Number, Number, result, lhs, rhs, *, "number", op);
                        }
                        lexer::Token::Slash => {
                            maybe_apply_op!(Number, Number, result, lhs, rhs, /, "number", op);
                        }
                        lexer::Token::EqualEqual => {
                            maybe_apply_op!(Boolean, Boolean, result, lhs, rhs, ==, "boolean", op);
                            maybe_apply_op!(Number, Boolean, result, lhs, rhs, ==, "number", op);
                            maybe_apply_op!(Str, Boolean, result, lhs, rhs, ==, "string", op);
                        }
                        lexer::Token::NotEqual => {
                            maybe_apply_op!(Boolean, Boolean, result, lhs, rhs, !=, "boolean", op);
                            maybe_apply_op!(Number, Boolean, result, lhs, rhs, !=, "number", op);
                            maybe_apply_op!(Str, Boolean, result, lhs, rhs, !=, "string", op);
                        }
                        lexer::Token::Greater => {
                            maybe_apply_op!(Number, Boolean, result, lhs, rhs, >, "number", op);
                        }
                        lexer::Token::GreaterEqual => {
                            maybe_apply_op!(Number, Boolean, result, lhs, rhs, >=, "number", op);
                        }
                        lexer::Token::Less => {
                            maybe_apply_op!(Number, Boolean, result, lhs, rhs, <, "number", op);
                        }
                        lexer::Token::LessEqual => {
                            maybe_apply_op!(Number, Boolean, result, lhs, rhs, <=, "number", op);
                        }
                        _ => {
                            return Err(RuntimeError {
                                err: "Internal error: invalid binary operation.".to_string(),
                                line: op.line,
                                pos: op.pos,
                            });
                        }
                    }
                    let mut err = "Invalid arguments to ".to_string();
                    err.push_str(&op.token.to_string());
                    err.push('.');
                    return Err(RuntimeError {
                        err: err,
                        line: op.line,
                        pos: op.pos,
                    });
                }
                Err(e) => Err(e),
            },
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
    }
}

fn unaryop(op: &lexer::LexedToken, value: &parser::Ast) -> Result<Value, RuntimeError> {
    match eval(value) {
        Ok(value) => match &op.token {
            lexer::Token::Not => Ok(Value::Boolean(!truthy(value))),
            lexer::Token::Minus => match value {
                Value::Number(n) => Ok(Value::Number(-n)),
                _ => Err(RuntimeError {
                    err: "Type mismatch, expected number.".to_string(),
                    line: op.line,
                    pos: op.pos,
                }),
            },
            _ => Err(RuntimeError {
                err: "Internal error: invalid unary operator.".to_string(),
                line: op.line,
                pos: op.pos,
            }),
        },
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
        parser::Ast::If(conds, then) => {
            for (cond, then) in conds.iter() {
                match eval(cond) {
                    Ok(v) => {
                        if truthy(v) {
                            match eval(then) {
                                Ok(v) => return Ok(v),
                                Err(e) => {
                                    return Err(e);
                                }
                            }
                        }
                    }
                    Err(e) => {
                        return Err(e);
                    }
                }
            }
            match eval(then) {
                Ok(v) => return Ok(v),
                Err(e) => {
                    return Err(e);
                }
            }
        }
        parser::Ast::List(list) => {
            let mut result = LinkedList::<Value>::new();
            for item in list {
                match eval(item) {
                    Ok(v) => result.push_back(v),
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

    macro_rules! eval {
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

    macro_rules! evalfails {
        ($input:expr, $err:tt) => {{
            match lexer::scan($input) {
                Ok(mut tokens) => match parser::parse(&mut tokens) {
                    Ok(ast) => match interpreter::eval(&ast) {
                        Ok(_) => assert!(false),
                        Err(e) => assert_eq!(e.err, $err),
                    },
                    _ => assert!(false),
                },
                _ => assert!(false),
            }
        }};
    }

    #[test]
    fn evals() {
        eval!("2", Number, 2.0);
        eval!("-2", Number, -2.0);
        eval!("not true", Boolean, false);
        eval!("2+2", Number, 4.0);
        eval!("2.2+2*5", Number, 12.2);
        eval!("2+2<=5", Boolean, true);
        eval!("2+2>5", Boolean, false);
        eval!("2<>5", Boolean, true);
        eval!("true or false", Boolean, true);
        eval!("true or ''", Boolean, true);
        eval!("[1] and 0.0", Boolean, false);
        eval!("true or undefined", Boolean, true);
        eval!("false and undefined", Boolean, false);
        eval!("'a'=='a'", Boolean, true);
        eval!("'hello ' + 'world'", Str, "hello world");
        eval!("if 1 then 2 else 3 end", Number, 2.0);
        eval!("if false then 1 elsif true then 2 else 3 end", Number, 2.0);
        eval!("if false then 1 elsif false then 2 else 3 end", Number, 3.0);
        eval!("if 1 then 2 else undefined end", Number, 2.0);
        evalfails!("2+true", "Type mismatch, expected number.");
        evalfails!("-true", "Type mismatch, expected number.");
        evalfails!("'a'+2", "Type mismatch, expected string.");
        evalfails!("true+true", "Invalid arguments to +.");
        evalfails!("[1]+2", "Type mismatch, expected list.");

        match lexer::scan("[2 2>5 3*4]") {
            Ok(mut tokens) => {
                assert_eq!(tokens.len(), 9);
                match parser::parse(&mut tokens) {
                    Ok(ast) => match interpreter::eval(&ast) {
                        Ok(v) => match v {
                            interpreter::Value::List(mut list) => {
                                match list.pop_front() {
                                    Some(interpreter::Value::Number(t)) => {
                                        assert_eq!(t, 2.0);
                                    }
                                    _ => assert!(false),
                                }
                                match list.pop_front() {
                                    Some(interpreter::Value::Boolean(b)) => {
                                        assert!(!b);
                                    }
                                    _ => assert!(false),
                                }
                                match list.pop_front() {
                                    Some(interpreter::Value::Number(t)) => {
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

        match lexer::scan("[1] + [2 3] + [4 5 6]") {
            Ok(mut tokens) => {
                assert_eq!(tokens.len(), 14);
                match parser::parse(&mut tokens) {
                    Ok(ast) => match interpreter::eval(&ast) {
                        Ok(v) => match v {
                            interpreter::Value::List(list) => {
                                let mut expected = 1.0;
                                for item in list {
                                    match item {
                                        interpreter::Value::Number(t) => {
                                            assert_eq!(t, expected);
                                        }
                                        _ => assert!(false),
                                    }
                                    expected += 1.0;
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
