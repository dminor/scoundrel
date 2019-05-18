mod lexer;
mod parser;

fn main() {
    let (tokens, _) = lexer::scan("'hello world!'");
    for token in tokens {
        println!("{}", token.token);
    }
}
