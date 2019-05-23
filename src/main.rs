use std::collections::HashMap;

mod interpreter;
mod lexer;
mod parser;

use std::io::{self, BufRead, Write};

fn main() -> io::Result<()> {
    let stdin = io::stdin();
    let mut stdout = io::stdout();
    println!("Welcome to Scoundrel!");
    print!("> ");
    stdout.flush()?;

    let env = HashMap::new();
    for line in stdin.lock().lines() {
        match line {
            Ok(s) => match lexer::scan(&s) {
                Ok(mut tokens) => match parser::parse(&mut tokens) {
                    Ok(ast) => match interpreter::eval(&env, &ast) {
                        Ok(v) => {
                            println!("{}", v);
                        }
                        Err(err) => {
                            println!("{}", err);
                        }
                    },
                    Err(err) => {
                        println!("{}", err);
                    }
                },
                Err(err) => {
                    println!("{}", err);
                }
            },
            _ => break,
        }
        print!("> ");
        stdout.flush()?;
    }

    Ok(())
}
