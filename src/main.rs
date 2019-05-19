mod interpreter;
mod lexer;
mod parser;

fn main() {
    let (mut tokens, _) = lexer::scan("'hello world!'");
    let ast = parser::parse(&mut tokens);
    println!("{}", interpreter::eval(&ast));
}
