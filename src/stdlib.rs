use crate::interpreter;
use std::collections::HashMap;
use std::collections::LinkedList;

fn car(
    line: usize,
    arguments: Vec<interpreter::Value>,
) -> Result<interpreter::Value, interpreter::RuntimeError> {
    if arguments.len() != 1 {
        return Err(interpreter::RuntimeError {
            err: "car takes one argument.".to_string(),
            line,
        });
    }

    match &arguments[0] {
        interpreter::Value::List(list) => match list.front() {
            Some(v) => Ok(v.clone()),
            _ => Err(interpreter::RuntimeError {
                err: "car called on empty list.".to_string(),
                line,
            }),
        },
        interpreter::Value::Str(s) => match s.chars().nth(0) {
            Some(v) => Ok(interpreter::Value::Str(v.to_string())),
            _ => Err(interpreter::RuntimeError {
                err: "car called on empty string.".to_string(),
                line,
            }),
        },
        _ => Err(interpreter::RuntimeError {
            err: "Type mismatch, car expects list or string.".to_string(),
            line,
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
            line,
        });
    }

    match &arguments[0] {
        interpreter::Value::List(list) => {
            let mut result = list.clone();
            match result.pop_front() {
                Some(_) => Ok(interpreter::Value::List(result)),
                _ => Err(interpreter::RuntimeError {
                    err: "cdr called on empty list.".to_string(),
                    line,
                }),
            }
        }
        interpreter::Value::Str(s) => {
            if !s.is_empty() {
                let mut substr = s.chars();
                substr.next();
                Ok(interpreter::Value::Str(substr.collect()))
            } else {
                Err(interpreter::RuntimeError {
                    err: "cdr called on empty string.".to_string(),
                    line,
                })
            }
        }
        _ => Err(interpreter::RuntimeError {
            err: "Type mismatch, cdr expects list or string.".to_string(),
            line,
        }),
    }
}

#[allow(clippy::float_cmp)]
fn is_prime(
    line: usize,
    arguments: Vec<interpreter::Value>,
) -> Result<interpreter::Value, interpreter::RuntimeError> {
    if arguments.len() != 1 {
        return Err(interpreter::RuntimeError {
            err: "prime? takes one argument.".to_string(),
            line,
        });
    }

    match &arguments[0] {
        interpreter::Value::Number(n) => {
            if *n == 1.0 || *n == 2.0 {
                Ok(interpreter::Value::Boolean(true))
            } else if *n % 2.0 == 0.0 {
                Ok(interpreter::Value::Boolean(false))
            } else {
                // TODO: Consider Miller-Rabin instead, this is super slow
                let mut i = 3.0;
                while i <= n.sqrt().ceil() {
                    if *n % i == 0.0 {
                        return Ok(interpreter::Value::Boolean(false));
                    }
                    i += 2.0;
                }
                Ok(interpreter::Value::Boolean(true))
            }
        }
        _ => Err(interpreter::RuntimeError {
            err: "Type mismatch, prime? expects number.".to_string(),
            line,
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
            line,
        });
    }

    match &arguments[0] {
        interpreter::Value::List(v) => Ok(interpreter::Value::Number(v.len() as f64)),
        interpreter::Value::Str(s) => Ok(interpreter::Value::Number(s.len() as f64)),
        _ => Err(interpreter::RuntimeError {
            err: "Type mismatch, len expects string or list.".to_string(),
            line,
        }),
    }
}

fn map(
    line: usize,
    arguments: Vec<interpreter::Value>,
) -> Result<interpreter::Value, interpreter::RuntimeError> {
    if arguments.len() != 2 {
        return Err(interpreter::RuntimeError {
            err: "map takes two arguments.".to_string(),
            line,
        });
    }

    match &arguments[0] {
        interpreter::Value::Function(env, params, body) => {
            if params.len() != 1 {
                return Err(interpreter::RuntimeError {
                    err: "Function passed to map should take one argument.".to_string(),
                    line,
                });
            }
            match &arguments[1] {
                interpreter::Value::List(list) => {
                    let mut result = LinkedList::new();
                    for item in list {
                        let mut env = env.clone();
                        env.insert(params[0].clone(), item.clone());
                        match interpreter::eval(&env, body) {
                            Ok(v) => result.push_back(v),
                            Err(e) => {
                                return Err(e);
                            }
                        }
                    }
                    Ok(interpreter::Value::List(result))
                }
                _ => Err(interpreter::RuntimeError {
                    err: "Type mismatch, map expects list as second argument.".to_string(),
                    line,
                }),
            }
        }
        interpreter::Value::RustFunction(func) => match &arguments[1] {
            interpreter::Value::List(list) => {
                let mut result = LinkedList::new();
                for item in list {
                    match func(line, vec![item.clone()]) {
                        Ok(v) => result.push_back(v),
                        Err(e) => {
                            return Err(e);
                        }
                    }
                }
                Ok(interpreter::Value::List(result))
            }
            _ => Err(interpreter::RuntimeError {
                err: "Type mismatch, map expects list as second argument.".to_string(),
                line,
            }),
        },
        _ => Err(interpreter::RuntimeError {
            err: "Type mismatch, map expects function as first argument.".to_string(),
            line,
        }),
    }
}

fn nth(
    line: usize,
    arguments: Vec<interpreter::Value>,
) -> Result<interpreter::Value, interpreter::RuntimeError> {
    if arguments.len() != 2 {
        return Err(interpreter::RuntimeError {
            err: "nth takes two arguments.".to_string(),
            line,
        });
    }

    match &arguments[0] {
        interpreter::Value::Number(n) => {
            if *n < 0.0 {
                return Err(interpreter::RuntimeError {
                    err: "list index must be non-negative.".to_string(),
                    line,
                });
            }

            let index = *n as usize;
            match &arguments[1] {
                interpreter::Value::List(list) => match list.iter().nth(index) {
                    Some(v) => Ok(v.clone()),
                    _ => {
                        let mut err = "index ".to_string();
                        err.push_str(&index.to_string());
                        err.push_str(" must be less than list length ");
                        err.push_str(&list.len().to_string());
                        err.push('.');
                        Err(interpreter::RuntimeError { err, line })
                    }
                },
                _ => Err(interpreter::RuntimeError {
                    err: "Type mismatch, nth expects list as second argument.".to_string(),
                    line,
                }),
            }
        }
        _ => Err(interpreter::RuntimeError {
            err: "Type mismatch, map expects number as first argument.".to_string(),
            line,
        }),
    }
}

fn num(
    line: usize,
    arguments: Vec<interpreter::Value>,
) -> Result<interpreter::Value, interpreter::RuntimeError> {
    if arguments.len() != 1 {
        return Err(interpreter::RuntimeError {
            err: "num takes one argument.".to_string(),
            line,
        });
    }

    match &arguments[0] {
        interpreter::Value::Str(s) => match s.parse::<f64>() {
            Ok(n) => Ok(interpreter::Value::Number(n)),
            _ => Err(interpreter::RuntimeError {
                err: "Could not convert string to number.".to_string(),
                line,
            }),
        },
        _ => Err(interpreter::RuntimeError {
            err: "Type mismatch, num expects string.".to_string(),
            line,
        }),
    }
}

fn reduce(
    line: usize,
    arguments: Vec<interpreter::Value>,
) -> Result<interpreter::Value, interpreter::RuntimeError> {
    if arguments.len() != 2 {
        return Err(interpreter::RuntimeError {
            err: "reduce takes two arguments.".to_string(),
            line,
        });
    }

    match &arguments[0] {
        interpreter::Value::Function(env, params, body) => {
            if params.len() != 2 {
                return Err(interpreter::RuntimeError {
                    err: "Function passed to reduce should take two arguments.".to_string(),
                    line,
                });
            }
            match &arguments[1] {
                interpreter::Value::List(list) => {
                    let mut iter = list.iter();
                    match iter.next() {
                        Some(v) => {
                            let mut result = v.clone();
                            for item in iter {
                                let mut env = env.clone();
                                env.insert(params[0].clone(), result);
                                env.insert(params[1].clone(), item.clone());
                                match interpreter::eval(&env, body) {
                                    Ok(v) => result = v,
                                    Err(e) => {
                                        return Err(e);
                                    }
                                }
                            }
                            Ok(result)
                        }
                        _ => Err(interpreter::RuntimeError {
                            err: "reduce applied to empty list.".to_string(),
                            line,
                        }),
                    }
                }
                _ => Err(interpreter::RuntimeError {
                    err: "Type mismatch, reduce expects list as second argument.".to_string(),
                    line,
                }),
            }
        }
        interpreter::Value::RustFunction(func) => match &arguments[1] {
            interpreter::Value::List(list) => {
                let mut iter = list.iter();
                match iter.next() {
                    Some(v) => {
                        let mut result = v.clone();
                        for item in iter {
                            match func(line, vec![result, item.clone()]) {
                                Ok(v) => result = v,
                                Err(e) => {
                                    return Err(e);
                                }
                            }
                        }
                        Ok(result)
                    }
                    _ => Err(interpreter::RuntimeError {
                        err: "reduce applied to empty list.".to_string(),
                        line,
                    }),
                }
            }
            _ => Err(interpreter::RuntimeError {
                err: "Type mismatch, reduce expects list as second argument.".to_string(),
                line,
            }),
        },
        _ => Err(interpreter::RuntimeError {
            err: "Type mismatch, reduce expects function as first argument.".to_string(),
            line,
        }),
    }
}

fn sqrt(
    line: usize,
    arguments: Vec<interpreter::Value>,
) -> Result<interpreter::Value, interpreter::RuntimeError> {
    if arguments.len() != 1 {
        return Err(interpreter::RuntimeError {
            err: "sqrt takes one argument.".to_string(),
            line,
        });
    }

    match &arguments[0] {
        interpreter::Value::Number(n) => Ok(interpreter::Value::Number(n.sqrt())),
        _ => Err(interpreter::RuntimeError {
            err: "Type mismatch, sqrt expects number.".to_string(),
            line,
        }),
    }
}

fn to_str(
    line: usize,
    arguments: Vec<interpreter::Value>,
) -> Result<interpreter::Value, interpreter::RuntimeError> {
    if arguments.len() != 1 {
        return Err(interpreter::RuntimeError {
            err: "str takes one argument.".to_string(),
            line,
        });
    }

    Ok(interpreter::Value::Str(arguments[0].to_string()))
}

pub fn register(env: &mut HashMap<String, interpreter::Value>) {
    env.insert("car".to_string(), interpreter::Value::RustFunction(car));
    env.insert("cdr".to_string(), interpreter::Value::RustFunction(cdr));
    env.insert(
        "prime?".to_string(),
        interpreter::Value::RustFunction(is_prime),
    );
    env.insert("len".to_string(), interpreter::Value::RustFunction(len));
    env.insert("map".to_string(), interpreter::Value::RustFunction(map));
    env.insert("nth".to_string(), interpreter::Value::RustFunction(nth));
    env.insert("num".to_string(), interpreter::Value::RustFunction(num));
    env.insert(
        "reduce".to_string(),
        interpreter::Value::RustFunction(reduce),
    );
    env.insert("sqrt".to_string(), interpreter::Value::RustFunction(sqrt));
    env.insert("str".to_string(), interpreter::Value::RustFunction(to_str));
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

    fn add(
        line: usize,
        arguments: Vec<interpreter::Value>,
    ) -> Result<interpreter::Value, interpreter::RuntimeError> {
        if let interpreter::Value::Number(n1) = &arguments[0] {
            if let interpreter::Value::Number(n2) = &arguments[1] {
                return Ok(interpreter::Value::Number(n1 + n2));
            }
        }
        return Err(interpreter::RuntimeError {
            err: "Type mismatch, sqrt expects number.".to_string(),
            line,
        });
    }

    #[test]
    fn evals() {
        eval!("car([1])", Number, 1.0);
        evalfails!("car([])", "car called on empty list.");
        eval!("car('hello world')", Str, "h".to_string());
        evalfails!("car(42)", "Type mismatch, car expects list or string.");
        eval!("cdr('hello world')", Str, "ello world".to_string());
        evalfails!("cdr([])", "cdr called on empty list.");
        evalfails!("cdr('')", "cdr called on empty string.");

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

        eval!("sqrt(4)", Number, 2.0);
        eval!("prime?(1)", Boolean, true);
        eval!("prime?(2)", Boolean, true);
        eval!("prime?(4)", Boolean, false);
        eval!("prime?(15)", Boolean, false);
        eval!("str(42)", Str, "42".to_string());
        eval!("str(false)", Str, "false".to_string());

        eval!(
            "
            let square := fn(x)
                    x*x
                end
                sum := fn(x, y)
                    x + y
                end
            in
                reduce(sum, map(square, [1, 2, 3, 4, 5]))
            end",
            Number,
            55.0
        );

        evalfails!(
            "map(fn() 1 end, [1 2 3])",
            "Function passed to map should take one argument."
        );
        evalfails!(
            "reduce(fn(x) 1 end, [1 2 3])",
            "Function passed to reduce should take two arguments."
        );
        evalfails!(
            "reduce(fn(x, y) x + y end, [])",
            "reduce applied to empty list."
        );
        eval!("reduce(fn(x, y) x + y end, [1])", Number, 1.0);

        match lexer::scan("map(fn(x) x end, [])") {
            Ok(mut tokens) => {
                assert_eq!(tokens.len(), 12);
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

        eval!("num('42')", Number, 42.0);
        evalfails!("num('forty two')", "Could not convert string to number.");

        eval!(
            "reduce(fn(x,y) x*y end, map(num, ['1', '2', '3']))",
            Number,
            6.0
        );

        match lexer::scan("reduce(add, [1, 2, 3, 4, 5])") {
            Ok(mut tokens) => {
                assert_eq!(tokens.len(), 16);
                let mut env = HashMap::new();
                stdlib::register(&mut env);
                env.insert("add".to_string(), interpreter::Value::RustFunction(add));
                match parser::parse(&mut tokens) {
                    Ok(ast) => match interpreter::eval(&env, &ast) {
                        Ok(v) => match v {
                            interpreter::Value::Number(n) => {
                                assert_eq!(n, 15.0);
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

        eval!("nth(3, [1, 2, 3, 4, 5])", Number, 4.0);
        evalfails!("nth(-1, [1, 2, 3])", "list index must be non-negative.");
        evalfails!("nth(0, [])", "index 0 must be less than list length 0.");
    }
}
