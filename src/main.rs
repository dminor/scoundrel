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
    for line in stdin.lock().lines() {
        match line {
            Ok(s) => {
                let (mut tokens, _) = lexer::scan(&s);
                match parser::parse(&mut tokens) {
                    Ok(ast) => println!("{}", interpreter::eval(&ast)),
                    Err(err) => {
                        println!("{}", err);
                    }
                }
            }
            _ => break,
        }
        print!("> ");
        stdout.flush()?;
    }

    Ok(())
}
