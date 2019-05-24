use std::collections::HashMap;
use std::env;
use std::fs::File;
use std::io::prelude::*;

mod interpreter;
mod lexer;
mod parser;

use std::io::{self, BufRead, Write};

fn eval(s: String) {
    let env = HashMap::new();
    match lexer::scan(&s) {
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
    }
}

fn main() -> io::Result<()> {
    let args: Vec<String> = env::args().collect();
    if args.len() > 1 {
        let mut file = File::open(args[1].to_string())?;
        let mut program = String::new();
        file.read_to_string(&mut program)?;
        eval(program);
        return Ok(());
    }

    let stdin = io::stdin();
    let mut stdout = io::stdout();
    println!("Welcome to Scoundrel!");
    print!("> ");
    stdout.flush()?;

    for line in stdin.lock().lines() {
        match line {
            Ok(s) => {
                eval(s);
            }
            _ => break,
        }
        print!("> ");
        stdout.flush()?;
    }

    Ok(())
}
