use crate::interpreter;
use std::collections::HashMap;

fn car(
    line: usize,
    arguments: Vec<interpreter::Value>,
) -> Result<interpreter::Value, interpreter::RuntimeError> {
    if arguments.len() != 1 {
        return Err(interpreter::RuntimeError {
            err: "car takes one argument.".to_string(),
            line: line,
        });
    }

    match &arguments[0] {
        interpreter::Value::List(list) => match list.front() {
            Some(v) => Ok(v.clone()),
            _ => Err(interpreter::RuntimeError {
                err: "car called on empty list.".to_string(),
                line: line,
            }),
        },
        _ => Err(interpreter::RuntimeError {
            err: "Type mismatch, car expects list.".to_string(),
            line: line,
        }),
    }
}

fn cdr(
    line: usize,
    arguments: Vec<interpreter::Value>,
) -> Result<interpreter::Value, interpreter::RuntimeError> {
    if arguments.len() != 1 {
        return Err(interpreter::RuntimeError {
            err: "car takes one argument.".to_string(),
            line: line,
        });
    }

    match &arguments[0] {
        interpreter::Value::List(list) => {
            let mut result = list.clone();
            match result.pop_front() {
                Some(_) => Ok(interpreter::Value::List(result)),
                _ => Err(interpreter::RuntimeError {
                    err: "cdr called on empty list.".to_string(),
                    line: line,
                }),
            }
        }
        _ => Err(interpreter::RuntimeError {
            err: "Type mismatch, cdr expects list.".to_string(),
            line: line,
        }),
    }
}

fn len(
    line: usize,
    arguments: Vec<interpreter::Value>,
) -> Result<interpreter::Value, interpreter::RuntimeError> {
    if arguments.len() != 1 {
        return Err(interpreter::RuntimeError {
            err: "len takes one argument.".to_string(),
            line: line,
        });
    }

    match &arguments[0] {
        interpreter::Value::Str(s) => Ok(interpreter::Value::Number(s.len() as f64)),
        interpreter::Value::List(v) => Ok(interpreter::Value::Number(v.len() as f64)),
        _ => Err(interpreter::RuntimeError {
            err: "Type mismatch, len expects string or list.".to_string(),
            line: line,
        }),
    }
}

pub fn register(env: &mut HashMap<String, interpreter::Value>) {
    env.insert("car".to_string(), interpreter::Value::RustFunction(car));
    env.insert("cdr".to_string(), interpreter::Value::RustFunction(cdr));
    env.insert("len".to_string(), interpreter::Value::RustFunction(len));
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::interpreter;
    use crate::lexer;
    use crate::parser;
    use crate::stdlib;

    macro_rules! eval {
        ($input:expr, $type:tt, $value:expr) => {{
            let mut env = HashMap::new();
            stdlib::register(&mut env);
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
            let mut env = HashMap::new();
            stdlib::register(&mut env);
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
        eval!("car([1])", Number, 1.0);
        evalfails!("car([])", "car called on empty list.");
        evalfails!("car('hello world')", "Type mismatch, car expects list.");
        evalfails!("cdr([])", "cdr called on empty list.");

        match lexer::scan("cdr([42])") {
            Ok(mut tokens) => {
                assert_eq!(tokens.len(), 6);
                let mut env = HashMap::new();
                stdlib::register(&mut env);
                match parser::parse(&mut tokens) {
                    Ok(ast) => match interpreter::eval(&env, &ast) {
                        Ok(v) => match v {
                            interpreter::Value::List(list) => {
                                assert_eq!(list.len(), 0);
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

        match lexer::scan("cdr([0 1 2 3 4])") {
            Ok(mut tokens) => {
                assert_eq!(tokens.len(), 10);
                let mut env = HashMap::new();
                stdlib::register(&mut env);
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

        eval!("len('')", Number, 0.0);
        eval!("len('hello world')", Number, 11.0);
        eval!("len([])", Number, 0.0);
        eval!("len([1 2 3])", Number, 3.0);
        evalfails!("len(42)", "Type mismatch, len expects string or list.");

        eval!(
            "
            let f := fn (list, len)
                    if not list then
                        len
                    else
                        $(cdr(list), len + 1)
                    end
                end
            in
                f([1, 2, 3], 0)
            end",
            Number,
            3.0
        );
    }
}
