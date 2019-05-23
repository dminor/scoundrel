use crate::lexer;
use crate::parser;
use std::collections::HashMap;
use std::collections::LinkedList;
use std::error::Error;
use std::fmt;

#[derive(Clone)]
pub enum Value<'a> {
    Boolean(bool),
    Function(HashMap<String, Value<'a>>, Vec<String>, &'a parser::Ast),
    List(LinkedList<Value<'a>>),
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
    fn fmt<'a>(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "RuntimeError [Line {}]: {}", self.line, self.err)
    }
}

impl Error for RuntimeError {}

impl<'a> fmt::Display for Value<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::Boolean(b) => write!(f, "{}", b),
            Value::Function(_, _, _) => write!(f, "<lambda expression>"),
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

fn binaryop<'a>(
    env: &HashMap<String, Value<'a>>,
    op: &lexer::LexedToken,
    lhs: &'a parser::Ast,
    rhs: &'a parser::Ast,
) -> Result<Value<'a>, RuntimeError> {
    match eval(env, lhs) {
        Ok(lhs) => match &op.token {
            lexer::Token::And => {
                if truthy(lhs) {
                    match eval(env, rhs) {
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
                    match eval(env, rhs) {
                        Ok(rhs) => {
                            return Ok(Value::Boolean(truthy(rhs)));
                        }
                        Err(e) => Err(e),
                    }
                }
            }
            _ => match eval(env, rhs) {
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
        Value::Function(_, _, _) => true,
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

fn unaryop<'a>(
    env: &HashMap<String, Value>,
    op: &lexer::LexedToken,
    value: &parser::Ast,
) -> Result<Value<'a>, RuntimeError> {
    match eval(env, value) {
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

fn value<'a>(
    env: &HashMap<String, Value<'a>>,
    token: &lexer::LexedToken,
) -> Result<Value<'a>, RuntimeError> {
    match &token.token {
        lexer::Token::False => Ok(Value::Boolean(false)),
        lexer::Token::True => Ok(Value::Boolean(true)),
        lexer::Token::Number(n) => Ok(Value::Number(*n)),
        lexer::Token::Str(s) => Ok(Value::Str(s.to_string())),
        lexer::Token::Identifier(s) => match env.get(s) {
            Some(v) => Ok(v.clone()),
            None => {
                let mut err = "Undefined variable: ".to_string();
                err.push_str(s);
                err.push('.');
                Err(RuntimeError {
                    err: err,
                    line: token.line,
                    pos: token.pos,
                })
            }
        },
        _ => Err(RuntimeError {
            err: "Internal error: token has no value.".to_string(),
            line: token.line,
            pos: token.pos,
        }),
    }
}

pub fn eval<'a>(
    env: &HashMap<String, Value<'a>>,
    ast: &'a parser::Ast,
) -> Result<Value<'a>, RuntimeError> {
    match ast {
        parser::Ast::BinaryOp(op, lhs, rhs) => binaryop(env, op, lhs, rhs),
        parser::Ast::Function(args, body) => {
            let fn_env = env.clone();
            let mut variables = Vec::<String>::new();
            for arg in args {
                match &arg.token {
                    lexer::Token::Identifier(s) => {
                        variables.push(s.to_string());
                    }
                    _ => {
                        return Err(RuntimeError {
                            err: "Expected identifier.".to_string(),
                            line: arg.line,
                            pos: arg.pos,
                        });
                    }
                }
            }
            Ok(Value::Function(fn_env, variables, body))
        }
        parser::Ast::Let(variables, expr) => {
            // TODO: maintaining a stack of environments would
            // likely be more efficient than copying here.
            let mut let_env = env.clone();
            for (var, var_expr) in variables {
                match &var.token {
                    lexer::Token::Identifier(s) => match eval(&let_env, var_expr) {
                        Ok(v) => {
                            let_env.insert(s.to_string(), v);
                        }
                        Err(e) => {
                            return Err(e);
                        }
                    },
                    _ => {
                        return Err(RuntimeError {
                            err: "Expected identifier.".to_string(),
                            line: var.line,
                            pos: var.pos,
                        });
                    }
                }
            }
            eval(&let_env, expr)
        }
        parser::Ast::List(list) => {
            let mut result = LinkedList::<Value>::new();
            for item in list {
                match eval(env, item) {
                    Ok(v) => result.push_back(v),
                    Err(e) => {
                        return Err(e);
                    }
                }
            }
            Ok(Value::List(result))
        }
        parser::Ast::If(conds, then) => {
            for (cond, then) in conds.iter() {
                match eval(env, cond) {
                    Ok(v) => {
                        if truthy(v) {
                            match eval(env, then) {
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
            match eval(env, then) {
                Ok(v) => return Ok(v),
                Err(e) => {
                    return Err(e);
                }
            }
        }
        parser::Ast::UnaryOp(op, v) => unaryop(env, op, v),
        parser::Ast::Value(t) => value(env, t),
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::interpreter;
    use crate::lexer;
    use crate::parser;

    macro_rules! eval {
        ($input:expr, $type:tt, $value:expr) => {{
            let env = HashMap::new();
            match lexer::scan($input) {
                Ok(mut tokens) => match parser::parse(&mut tokens) {
                    Ok(ast) => match interpreter::eval(&env, &ast) {
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
            let env = HashMap::new();
            match lexer::scan($input) {
                Ok(mut tokens) => match parser::parse(&mut tokens) {
                    Ok(ast) => match interpreter::eval(&env, &ast) {
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
        eval!(
            "let x := 1 y := x + 1 z := x + 2 in x + y + z end",
            Number,
            6.0
        );
        eval!("let x := true in x or undefined end", Boolean, true);
        eval!("let x := fn (a) a*2 end in 2 end", Number, 2.0);
        evalfails!("2+true", "Type mismatch, expected number.");
        evalfails!("-true", "Type mismatch, expected number.");
        evalfails!("'a'+2", "Type mismatch, expected string.");
        evalfails!("true+true", "Invalid arguments to +.");
        evalfails!("[1]+2", "Type mismatch, expected list.");
        evalfails!("z", "Undefined variable: z.");

        match lexer::scan("[2 2>5 3*4]") {
            Ok(mut tokens) => {
                assert_eq!(tokens.len(), 9);
                let env = HashMap::new();
                match parser::parse(&mut tokens) {
                    Ok(ast) => match interpreter::eval(&env, &ast) {
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
                let env = HashMap::new();
                match parser::parse(&mut tokens) {
                    Ok(ast) => match interpreter::eval(&env, &ast) {
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
