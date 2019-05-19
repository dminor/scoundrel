use std::error::Error;
use std::fmt;

#[derive(Debug, PartialEq)]
pub enum Token {
    LeftParen,
    RightParen,
    ColonEqual,
    Comma,
    Minus,
    Plus,
    Slash,
    Star,
    Not,
    NotEqual,
    EqualEqual,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,

    // Literals
    Identifier(String),
    Str(String),
    Number(f64),

    // Keywords
    And,
    Break,
    Continue,
    Do,
    Else,
    Elsif,
    End,
    False,
    Function,
    If,
    Let,
    Or,
    Return,
    Then,
    True,
    While,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Token::LeftParen => write!(f, "("),
            Token::RightParen => write!(f, ")"),
            Token::ColonEqual => write!(f, ":="),
            Token::Comma => write!(f, ","),
            Token::Minus => write!(f, "-"),
            Token::Plus => write!(f, "+"),
            Token::Slash => write!(f, "/"),
            Token::Star => write!(f, "*"),
            Token::Not => write!(f, "!"),
            Token::NotEqual => write!(f, "!="),
            Token::EqualEqual => write!(f, "=="),
            Token::Greater => write!(f, ">"),
            Token::GreaterEqual => write!(f, ">="),
            Token::Less => write!(f, "<"),
            Token::LessEqual => write!(f, "<="),
            Token::Identifier(s) => write!(f, "{}", s),
            Token::Str(s) => write!(f, "{}", s),
            Token::Number(n) => write!(f, "{}", n),
            Token::And => write!(f, "and"),
            Token::Break => write!(f, "break"),
            Token::Continue => write!(f, "continue"),
            Token::Do => write!(f, "do"),
            Token::Else => write!(f, "else"),
            Token::Elsif => write!(f, "elsif"),
            Token::End => write!(f, "end"),
            Token::False => write!(f, "false"),
            Token::Function => write!(f, "fn"),
            Token::If => write!(f, "if"),
            Token::Let => write!(f, "let"),
            Token::Or => write!(f, "or"),
            Token::Return => write!(f, "return"),
            Token::Then => write!(f, "then"),
            Token::True => write!(f, "true"),
            Token::While => write!(f, "while"),
        }
    }
}

#[derive(Debug)]
pub struct LexerError {
    pub err: String,
    pub line: usize,
    pub pos: usize,
}

impl fmt::Display for LexerError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "LexerError: line {} msg {}", self.line, self.err)
    }
}

impl Error for LexerError {}

pub struct LexedToken {
    pub token: Token,
    pub line: usize,
    pub pos: usize,
}

macro_rules! push_token {
    ($T:expr, $tokens:ident, $line:ident, $pos:ident) => (
        $tokens.push({
            LexedToken {
                token: $T,
                line: $line,
                pos: $pos,
            }
        });
    )
}

pub fn scan(src: &str) -> (Vec<LexedToken>, Vec<LexerError>) {
    let mut line = 0;
    let mut tokens = Vec::<LexedToken>::new();
    let mut errors = Vec::<LexerError>::new();
    let mut chars = src.char_indices().peekable();
    loop {
        match chars.next() {
            Some((pos, c)) => match c {
                '(' => {
                    push_token!(Token::LeftParen, tokens, line, pos);
                }
                ')' => {
                    push_token!(Token::RightParen, tokens, line, pos);
                }
                ':' => match chars.next() {
                    Some((pos, c)) => {
                        if c == '=' {
                            push_token!(Token::ColonEqual, tokens, line, pos);
                        } else {
                            errors.push({
                                LexerError {
                                    err: "unexpected token while parsing :=".to_string(),
                                    line: line,
                                    pos: pos,
                                }
                            });
                        }
                    }
                    _ => {
                        errors.push({
                            LexerError {
                                err: "unexpected end of input while parsing :=".to_string(),
                                line: line,
                                pos: pos,
                            }
                        });
                    }
                },
                ',' => {
                    push_token!(Token::Comma, tokens, line, pos);
                }
                '-' => {
                    push_token!(Token::Minus, tokens, line, pos);
                }
                '+' => {
                    push_token!(Token::Plus, tokens, line, pos);
                }
                '/' => {
                    push_token!(Token::Slash, tokens, line, pos);
                }
                '*' => {
                    push_token!(Token::Star, tokens, line, pos);
                }
                '!' => match chars.peek() {
                    Some((_, c)) => {
                        if *c == '=' {
                            push_token!(Token::NotEqual, tokens, line, pos);
                            chars.next();
                        } else {
                            push_token!(Token::Not, tokens, line, pos);
                        }
                    }
                    None => {
                        push_token!(Token::Not, tokens, line, pos);
                    }
                },
                '=' => match chars.peek() {
                    Some((_, c)) => {
                        if *c == '=' {
                            push_token!(Token::EqualEqual, tokens, line, pos);
                            chars.next();
                        } else {
                            errors.push({
                                LexerError {
                                    err: "unexpected end of input while parsing ==".to_string(),
                                    line: line,
                                    pos: pos,
                                }
                            });
                        }
                    }
                    None => {}
                },
                '>' => match chars.peek() {
                    Some((_, c)) => {
                        if *c == '=' {
                            push_token!(Token::GreaterEqual, tokens, line, pos);
                            chars.next();
                        } else {
                            push_token!(Token::Greater, tokens, line, pos);
                        }
                    }
                    None => {
                        push_token!(Token::Greater, tokens, line, pos);
                    }
                },
                '<' => match chars.peek() {
                    Some((_, c)) => {
                        if *c == '=' {
                            push_token!(Token::LessEqual, tokens, line, pos);
                            chars.next();
                        } else {
                            push_token!(Token::Less, tokens, line, pos);
                        }
                    }
                    None => {
                        push_token!(Token::Less, tokens, line, pos);
                    }
                },
                '\'' => {
                    let mut v = Vec::<char>::new();
                    loop {
                        match chars.next() {
                            Some((_, c)) => match c {
                                '\'' => {
                                    push_token!(Token::Str(v.into_iter().collect()), tokens, line, pos);
                                    break;
                                }
                                '\n' => {
                                    errors.push({
                                        LexerError {
                                            err: "unexpected end of line while lexing string"
                                                .to_string(),
                                            line: line,
                                            pos: pos,
                                        }
                                    });
                                    break;
                                }
                                _ => v.push(c),
                            },
                            None => {
                                errors.push({
                                    LexerError {
                                        err: "unexpected end of input while lexing string"
                                            .to_string(),
                                        line: line,
                                        pos: pos,
                                    }
                                });
                                break;
                            }
                        }
                    }
                }
                '\n' => {
                    line += 1;
                    continue;
                }
                ' ' => {}
                _ => {
                    let mut v = vec![c];
                    loop {
                        match chars.peek() {
                            Some((_, c)) => {
                                if c.is_alphanumeric() || *c == '.' {
                                    v.push(*c);
                                    chars.next();
                                } else {
                                    break;
                                }
                            }
                            None => {
                                break;
                            }
                        }
                    }
                    let s: String = v.into_iter().collect();
                    match &s[..] {
                        "and" => {
                            push_token!(Token::And, tokens, line, pos);
                        }
                        "break" => {
                            push_token!(Token::Break, tokens, line, pos);
                        }
                        "continue" => {
                            push_token!(Token::Continue, tokens, line, pos);
                        }
                        "do" => {
                            push_token!(Token::Do, tokens, line, pos);
                        }
                        "else" => {
                            push_token!(Token::Else, tokens, line, pos);
                        }
                        "elsif" => {
                            push_token!(Token::Elsif, tokens, line, pos);
                        }
                        "end" => {
                            push_token!(Token::End, tokens, line, pos);
                        }
                        "false" => {
                            push_token!(Token::False, tokens, line, pos);
                        }
                        "fn" => {
                            push_token!(Token::Function, tokens, line, pos);
                        }
                        "if" => {
                            push_token!(Token::If, tokens, line, pos);
                        }
                        "let" => {
                            push_token!(Token::Let, tokens, line, pos);
                        }
                        "or" => {
                            push_token!(Token::Or, tokens, line, pos);
                        }
                        "return" => {
                            push_token!(Token::Return, tokens, line, pos);
                        }
                        "then" => {
                            push_token!(Token::Then, tokens, line, pos);
                        }
                        "true" => {
                            push_token!(Token::True, tokens, line, pos);
                        }
                        "while" => {
                            push_token!(Token::While, tokens, line, pos);
                        }
                        _ => match s.parse::<f64>() {
                            Ok(n) => {
                                push_token!(Token::Number(n), tokens, line, pos);
                            }
                            _ => {
                                push_token!(Token::Identifier(s.to_string()), tokens, line, pos);
                            }
                        },
                    }
                }
            },
            None => {
                break;
            }
        }
    }

    (tokens, errors)
}

#[cfg(test)]
mod tests {
    use crate::lexer;

    #[test]
    fn scanning() {
        let (tokens, errors) = lexer::scan("(())");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 4);
        assert_eq!(tokens[0].token, lexer::Token::LeftParen);
        assert_eq!(tokens[1].token, lexer::Token::LeftParen);
        assert_eq!(tokens[2].token, lexer::Token::RightParen);
        assert_eq!(tokens[3].token, lexer::Token::RightParen);
        assert_eq!(tokens[3].line, 0);
        assert_eq!(tokens[3].pos, 3);

        let (tokens, errors) = lexer::scan(":=");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 1);
        assert_eq!(tokens[0].token, lexer::Token::ColonEqual);

        let (tokens, errors) = lexer::scan("::");
        assert_eq!(errors.len(), 1);
        assert_eq!(tokens.len(), 0);

        let (tokens, errors) = lexer::scan(":");
        assert_eq!(errors.len(), 1);
        assert_eq!(tokens.len(), 0);

        let (tokens, errors) = lexer::scan(",");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 1);
        assert_eq!(tokens[0].token, lexer::Token::Comma);

        let (tokens, errors) = lexer::scan("-");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 1);
        assert_eq!(tokens[0].token, lexer::Token::Minus);

        let (tokens, errors) = lexer::scan("+");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 1);
        assert_eq!(tokens[0].token, lexer::Token::Plus);

        let (tokens, errors) = lexer::scan("/");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 1);
        assert_eq!(tokens[0].token, lexer::Token::Slash);

        let (tokens, errors) = lexer::scan("*");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 1);
        assert_eq!(tokens[0].token, lexer::Token::Star);

        let (tokens, errors) = lexer::scan("!!");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 2);
        assert_eq!(tokens[0].token, lexer::Token::Not);
        assert_eq!(tokens[1].token, lexer::Token::Not);

        let (tokens, errors) = lexer::scan("!=");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 1);
        assert_eq!(tokens[0].token, lexer::Token::NotEqual);

        let (tokens, errors) = lexer::scan("==");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 1);
        assert_eq!(tokens[0].token, lexer::Token::EqualEqual);

        let (tokens, errors) = lexer::scan("<<");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 2);
        assert_eq!(tokens[0].token, lexer::Token::Less);
        assert_eq!(tokens[1].token, lexer::Token::Less);

        let (tokens, errors) = lexer::scan("<=");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 1);
        assert_eq!(tokens[0].token, lexer::Token::LessEqual);

        let (tokens, errors) = lexer::scan(">>");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 2);
        assert_eq!(tokens[0].token, lexer::Token::Greater);
        assert_eq!(tokens[1].token, lexer::Token::Greater);

        let (tokens, errors) = lexer::scan(">=");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 1);
        assert_eq!(tokens[0].token, lexer::Token::GreaterEqual);

        let (tokens, errors) = lexer::scan(" +\n\n   +  \n");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 2);
        assert_eq!(tokens[0].token, lexer::Token::Plus);
        assert_eq!(tokens[0].line, 0);
        assert_eq!(tokens[0].pos, 1);
        assert_eq!(tokens[1].token, lexer::Token::Plus);
        assert_eq!(tokens[1].line, 2);
        assert_eq!(tokens[1].pos, 7);

        let (tokens, errors) = lexer::scan("'blahblah blah");
        assert_eq!(errors.len(), 1);
        assert_eq!(tokens.len(), 0);

        let (tokens, errors) = lexer::scan("'blahblah blah'");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 1);
        assert_eq!(
            tokens[0].token,
            lexer::Token::Str("blahblah blah".to_string())
        );

        let (tokens, errors) = lexer::scan("4");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 1);
        assert_eq!(tokens[0].token, lexer::Token::Number(4.0));

        let (tokens, errors) = lexer::scan("42");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 1);
        assert_eq!(tokens[0].token, lexer::Token::Number(42.0));

        let (tokens, errors) = lexer::scan("42 ");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 1);
        assert_eq!(tokens[0].token, lexer::Token::Number(42.0));

        let (tokens, errors) = lexer::scan("4.2");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 1);
        assert_eq!(tokens[0].token, lexer::Token::Number(4.2));

        let (tokens, errors) = lexer::scan("4+2");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 3);
        assert_eq!(tokens[0].token, lexer::Token::Number(4.0));
        assert_eq!(tokens[1].token, lexer::Token::Plus);
        assert_eq!(tokens[2].token, lexer::Token::Number(2.0));

        let (tokens, errors) = lexer::scan("4 + 2");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 3);
        assert_eq!(tokens[0].token, lexer::Token::Number(4.0));
        assert_eq!(tokens[1].token, lexer::Token::Plus);
        assert_eq!(tokens[2].token, lexer::Token::Number(2.0));

        let (tokens, errors) = lexer::scan("4 2");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 2);
        assert_eq!(tokens[0].token, lexer::Token::Number(4.0));
        assert_eq!(tokens[1].token, lexer::Token::Number(2.0));

        let (tokens, errors) = lexer::scan("let y := x + 1");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 6);
        assert_eq!(tokens[0].token, lexer::Token::Let);
        assert_eq!(tokens[1].token, lexer::Token::Identifier("y".to_string()));
        assert_eq!(tokens[2].token, lexer::Token::ColonEqual);
        assert_eq!(tokens[3].token, lexer::Token::Identifier("x".to_string()));
        assert_eq!(tokens[4].token, lexer::Token::Plus);
        assert_eq!(tokens[5].token, lexer::Token::Number(1.0));

        let (tokens, errors) = lexer::scan("xs");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 1);
        assert_eq!(tokens[0].token, lexer::Token::Identifier("xs".to_string()));

        let (tokens, errors) = lexer::scan("man and !mortal == false");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 6);
        assert_eq!(tokens[0].token, lexer::Token::Identifier("man".to_string()));
        assert_eq!(tokens[1].token, lexer::Token::And);
        assert_eq!(tokens[2].token, lexer::Token::Not);
        assert_eq!(
            tokens[3].token,
            lexer::Token::Identifier("mortal".to_string())
        );
        assert_eq!(tokens[4].token, lexer::Token::EqualEqual);
        assert_eq!(tokens[5].token, lexer::Token::False);

        let (tokens, errors) = lexer::scan("fn x(arg)\n    return arg*2\nend");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 10);
        assert_eq!(tokens[0].token, lexer::Token::Function);
        assert_eq!(tokens[1].token, lexer::Token::Identifier("x".to_string()));
        assert_eq!(tokens[2].token, lexer::Token::LeftParen);
        assert_eq!(tokens[3].token, lexer::Token::Identifier("arg".to_string()));
        assert_eq!(tokens[4].token, lexer::Token::RightParen);
        assert_eq!(tokens[5].token, lexer::Token::Return);
        assert_eq!(tokens[6].token, lexer::Token::Identifier("arg".to_string()));
        assert_eq!(tokens[7].token, lexer::Token::Star);
        assert_eq!(tokens[8].token, lexer::Token::Number(2.0));
        assert_eq!(tokens[9].token, lexer::Token::End);

        let (tokens, errors) =
            lexer::scan("if x then\n    1\nelsif y then\n    2\nelse\n    3\nend");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 11);
        assert_eq!(tokens[0].token, lexer::Token::If);
        assert_eq!(tokens[1].token, lexer::Token::Identifier("x".to_string()));
        assert_eq!(tokens[2].token, lexer::Token::Then);
        assert_eq!(tokens[3].token, lexer::Token::Number(1.0));
        assert_eq!(tokens[4].token, lexer::Token::Elsif);
        assert_eq!(tokens[5].token, lexer::Token::Identifier("y".to_string()));
        assert_eq!(tokens[6].token, lexer::Token::Then);
        assert_eq!(tokens[7].token, lexer::Token::Number(2.0));
        assert_eq!(tokens[8].token, lexer::Token::Else);
        assert_eq!(tokens[9].token, lexer::Token::Number(3.0));
        assert_eq!(tokens[10].token, lexer::Token::End);

        let (tokens, errors) =
            lexer::scan("while true or false do\n    i := i + 1\n    break\nend");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 12);
        assert_eq!(tokens[0].token, lexer::Token::While);
        assert_eq!(tokens[1].token, lexer::Token::True);
        assert_eq!(tokens[2].token, lexer::Token::Or);
        assert_eq!(tokens[3].token, lexer::Token::False);
        assert_eq!(tokens[4].token, lexer::Token::Do);
        assert_eq!(tokens[5].token, lexer::Token::Identifier("i".to_string()));
        assert_eq!(tokens[6].token, lexer::Token::ColonEqual);
        assert_eq!(tokens[7].token, lexer::Token::Identifier("i".to_string()));
        assert_eq!(tokens[8].token, lexer::Token::Plus);
        assert_eq!(tokens[9].token, lexer::Token::Number(1.0));
        assert_eq!(tokens[10].token, lexer::Token::Break);
        assert_eq!(tokens[11].token, lexer::Token::End);

        let (tokens, errors) = lexer::scan("continue");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 1);
        assert_eq!(tokens[0].token, lexer::Token::Continue);

        let (tokens, errors) = lexer::scan("Ὦ := 'φῶς'");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 3);
        assert_eq!(tokens[0].token, lexer::Token::Identifier("Ὦ".to_string()));
        assert_eq!(tokens[1].token, lexer::Token::ColonEqual);
        assert_eq!(tokens[2].token, lexer::Token::Str("φῶς".to_string()));

        let (tokens, errors) = lexer::scan("abd(def)");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 4);
        assert_eq!(tokens[0].token, lexer::Token::Identifier("abd".to_string()));
        assert_eq!(tokens[1].token, lexer::Token::LeftParen);
        assert_eq!(tokens[2].token, lexer::Token::Identifier("def".to_string()));
        assert_eq!(tokens[3].token, lexer::Token::RightParen);

        let (tokens, errors) = lexer::scan("&$123");
        assert_eq!(errors.len(), 0);
        assert_eq!(tokens.len(), 2);
        assert_eq!(tokens[0].token, lexer::Token::Identifier("&".to_string()));
        assert_eq!(
            tokens[1].token,
            lexer::Token::Identifier("$123".to_string())
        );
    }
}
