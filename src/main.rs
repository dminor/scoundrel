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
                let ast = parser::parse(&mut tokens);
                println!("{}", interpreter::eval(&ast));
            }
            _ => break,
        }
        print!("> ");
        stdout.flush()?;
    }

    Ok(())
}
