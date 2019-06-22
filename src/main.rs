use std::cmp::min;
use std::collections::HashMap;
use std::env;
use std::fs::File;
use std::io::prelude::*;

mod interpreter;
mod lexer;
mod parser;
mod stdlib;

use std::io::{self, BufRead, Write};

fn eval(filename: &str, src: &str) {
    let mut env = HashMap::new();
    stdlib::register(&mut env);

    let lines: Vec<&str> = src.split('\n').collect();
    match lexer::scan(&src) {
        Ok(mut tokens) => match parser::parse(&mut tokens) {
            Ok(ast) => match interpreter::eval(&env, &ast) {
                Ok(v) => {
                    println!("{}", v);
                }
                Err(err) => {
                    let line = min(lines.len(), err.line);
                    let width = line.to_string().len() + 2;
                    println!("{}", err);
                    println!("{s:>width$}|", s = " ", width = width);
                    println!(" {} | {}", line, lines[line - 1]);
                    println!("{s:>width$}|", s = " ", width = width);
                    println!("--> {}:{}", filename, line);
                }
            },
            Err(err) => {
                let line = min(lines.len(), err.line);
                let width = line.to_string().len() + 2;
                println!("{}", err);
                println!("{s:>width$}|", s = " ", width = width);
                println!(" {} | {}", line, lines[line - 1]);
                println!("{s:>width$}|", s = " ", width = width);
                println!("--> {}:{}", filename, line);
            }
        },
        Err(err) => {
            let line = min(lines.len(), err.line);
            let width = line.to_string().len() + 2;
            println!("{}", err);
            println!("{s:>width$}|", s = " ", width = width);
            println!(" {} | {}", line, lines[line - 1]);
            println!("{s:>width$}|", s = " ", width = width);
            println!("--> {}:{}", filename, line);
        }
    }
}

fn main() -> io::Result<()> {
    let args: Vec<String> = env::args().collect();
    if args.len() > 1 {
        let filename = &args[1];
        let mut file = File::open(&filename)?;
        let mut program = String::new();
        file.read_to_string(&mut program)?;
        eval(&filename, &program);
        return Ok(());
    }

    let stdin = io::stdin();
    let mut stdout = io::stdout();
    println!("Welcome to Scoundrel!");
    print!("> ");
    stdout.flush()?;

    for line in stdin.lock().lines() {
        match line {
            Ok(src) => {
                eval("<stdin>", &src);
            }
            _ => break,
        }
        print!("> ");
        stdout.flush()?;
    }

    Ok(())
}
