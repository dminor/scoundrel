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
    Recur(Vec<Value<'a>>),
    RustFunction(fn(usize, Vec<Value>) -> Result<Value, RuntimeError>),
    Str(String),
}

#[derive(Debug)]
pub struct RuntimeError {
    pub err: String,
    pub line: usize,
}

impl fmt::Display for RuntimeError {
    fn fmt<'a>(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "RuntimeError: {}", self.err)
    }
}

impl Error for RuntimeError {}

impl<'a> fmt::Display for Value<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::Boolean(b) => write!(f, "{}", b),
            Value::Function(_, _, _) => write!(f, "<lambda>"),
            Value::List(list) => {
                write!(f, "[")?;
                for item in list {
                    write!(f, " {}", item)?;
                }
                write!(f, " ]")
            }
            Value::Number(n) => write!(f, "{}", n),
            Value::Recur(_) => write!(f, "<recur>"),
            Value::RustFunction(_) => write!(f, "<lambda>"),
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
                        lexer::Token::Divides => {
                            if let Value::Number(x) = lhs {
                                if let Value::Number(y) = rhs {
                                    return Ok(Value::Boolean(y % x == 0.0));
                                } else {
                                    let err = "Type mismatch, expected number".to_string();
                                    return Err(RuntimeError {
                                        err: err,
                                        line: op.line,
                                    });
                                }
                            }
                        }
                        lexer::Token::Mod => {
                            maybe_apply_op!(Number, Number, result, lhs, rhs, %, "number", op);
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
                            });
                        }
                    }
                    let mut err = "Invalid arguments to ".to_string();
                    err.push_str(&op.token.to_string());
                    err.push('.');
                    return Err(RuntimeError {
                        err: err,
                        line: op.line,
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
        Value::Recur(_) => true,
        Value::RustFunction(_) => true,
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
                }),
            },
            _ => Err(RuntimeError {
                err: "Internal error: invalid unary operator.".to_string(),
                line: op.line,
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
                })
            }
        },
        _ => Err(RuntimeError {
            err: "Internal error: token has no value.".to_string(),
            line: token.line,
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
                        });
                    }
                }
            }
            Ok(Value::Function(fn_env, variables, body))
        }
        parser::Ast::FunctionCall(line, function, args) => match eval(&env, function) {
            Ok(Value::Function(fn_env, variables, body)) => {
                let mut call_env = env.clone();
                for kv in fn_env.iter() {
                    call_env.insert(kv.0.to_string(), kv.1.clone());
                }

                if variables.len() != args.len() {
                    let mut err =
                        "Wrong number of arguments in function call, expected ".to_string();
                    err.push_str(&variables.len().to_string());
                    err.push_str(" received ");
                    err.push_str(&args.len().to_string());
                    err.push('.');
                    return Err(RuntimeError {
                        err: err,
                        line: *line,
                    });
                }

                for i in 0..variables.len() {
                    match eval(&env, &args[i]) {
                        Ok(v) => {
                            call_env.insert(variables[i].clone(), v);
                        }
                        Err(e) => {
                            return Err(e);
                        }
                    }
                }
                loop {
                    let result = eval(&call_env, body);
                    match result {
                        Ok(Value::Recur(args)) => {
                            if variables.len() != args.len() {
                                let mut err =
                                    "Wrong number of arguments in recur, expected ".to_string();
                                err.push_str(&variables.len().to_string());
                                err.push_str(" received ");
                                err.push_str(&args.len().to_string());
                                err.push('.');
                                return Err(RuntimeError {
                                    err: err,
                                    line: *line,
                                });
                            }

                            for i in 0..variables.len() {
                                call_env.insert(variables[i].clone(), args[i].clone());
                            }
                        }
                        _ => return result,
                    }
                }
            }
            Ok(Value::RustFunction(func)) => {
                let mut func_args = Vec::new();
                for i in 0..args.len() {
                    match eval(&env, &args[i]) {
                        Ok(v) => {
                            func_args.push(v);
                        }
                        Err(e) => {
                            return Err(e);
                        }
                    }
                }
                func(*line, func_args)
            }
            Err(e) => Err(e),
            _ => {
                return Err(RuntimeError {
                    err: "Attempt to call non-function.".to_string(),
                    line: *line,
                });
            }
        },
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
        parser::Ast::Recur(args) => {
            let mut result = Vec::<Value>::new();
            for arg in args {
                match eval(env, arg) {
                    Ok(v) => result.push(v),
                    Err(e) => {
                        return Err(e);
                    }
                }
            }
            Ok(Value::Recur(result))
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
        eval!("3 | 6", Boolean, true);
        eval!("3 | 7", Boolean, false);
        eval!("24 mod 5", Number, 4.0);
        eval!("27.5 mod 4", Number, 3.5);
        eval!("5 mod -3", Number, 2.0);
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
        eval!("let f := fn (a) a*2 end in 2 end", Number, 2.0);
        eval!("fn() 1 end ()", Number, 1.0);
        eval!("fn(x, y) x + y end (2, 3)", Number, 5.0);
        eval!("let f := fn(a) a*2 end in f(2) end", Number, 4.0);
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

        eval!(
            "
            let f := fn(n, sum)
                    if n == 1000 then
                        sum
                    else
                        if (n mod 3 == 0) or (n mod 5 == 0) then
                            $(n + 1, sum + n)
                        else
                            $(n + 1, sum)
                        end
                    end
                end
            in
                f(1, 0)
            end",
            Number,
            233168.0
        );

        evalfails!(
            "fn() 1 end (2)",
            "Wrong number of arguments in function call, expected 0 received 1."
        );

        eval!(
            "
            let f := fn(n)
                    let iter := fn(d, largest)
                            if d | largest then
                                if d == n then
                                    largest
                                else
                                    $(d + 1, largest)
                                end
                            else
                                $(2, largest + 1)
                            end
                        end
                    in
                        iter(2, n)
                    end
                end
            in
                f(10)
            end",
            Number,
            2520.0
        );
    }
}
