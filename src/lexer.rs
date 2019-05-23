use std::collections::LinkedList;
use std::error::Error;
use std::fmt;

#[derive(Debug, PartialEq)]
pub enum Token {
    LeftBracket,
    RightBracket,
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
    In,
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
            Token::LeftBracket => write!(f, "["),
            Token::RightBracket => write!(f, "]"),
            Token::LeftParen => write!(f, "("),
            Token::RightParen => write!(f, ")"),
            Token::ColonEqual => write!(f, ":="),
            Token::Comma => write!(f, ","),
            Token::Minus => write!(f, "-"),
            Token::Plus => write!(f, "+"),
            Token::Slash => write!(f, "/"),
            Token::Star => write!(f, "*"),
            Token::NotEqual => write!(f, "<>"),
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
            Token::In => write!(f, "in"),
            Token::Let => write!(f, "let"),
            Token::Not => write!(f, "not"),
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
        write!(f, "LexerError: [Line {}] {}", self.line, self.err)
    }
}

impl Error for LexerError {}

pub struct LexedToken {
    pub token: Token,
    pub line: usize,
    pub pos: usize,
}

macro_rules! push_token {
    ($T:expr, $tokens:ident, $line:ident, $pos:ident) => {
        $tokens.push_back({
            LexedToken {
                token: $T,
                line: $line,
                pos: $pos,
            }
        });
    };
}

pub fn scan(src: &str) -> Result<LinkedList<LexedToken>, LexerError> {
    let mut line = 0;
    let mut tokens = LinkedList::<LexedToken>::new();
    let mut chars = src.char_indices().peekable();
    loop {
        match chars.next() {
            Some((pos, c)) => match c {
                '[' => {
                    push_token!(Token::LeftBracket, tokens, line, pos);
                }
                ']' => {
                    push_token!(Token::RightBracket, tokens, line, pos);
                }
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
                            return Err(LexerError {
                                err: "Unexpected token while parsing :=".to_string(),
                                line: line,
                                pos: pos,
                            });
                        }
                    }
                    _ => {
                        return Err(LexerError {
                            err: "Unexpected end of input while parsing :=".to_string(),
                            line: line,
                            pos: pos,
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
                '=' => match chars.peek() {
                    Some((_, c)) => {
                        if *c == '=' {
                            push_token!(Token::EqualEqual, tokens, line, pos);
                            chars.next();
                        } else {
                            return Err(LexerError {
                                err: "Unexpected end of input while parsing ==".to_string(),
                                line: line,
                                pos: pos,
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
                        } else if *c == '>' {
                            push_token!(Token::NotEqual, tokens, line, pos);
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
                                    push_token!(
                                        Token::Str(v.into_iter().collect()),
                                        tokens,
                                        line,
                                        pos
                                    );
                                    break;
                                }
                                '\n' => {
                                    return Err(LexerError {
                                        err: "Unexpected end of line while lexing string"
                                            .to_string(),
                                        line: line,
                                        pos: pos,
                                    });
                                }
                                _ => v.push(c),
                            },
                            None => {
                                return Err(LexerError {
                                    err: "Unexpected end of input while lexing string".to_string(),
                                    line: line,
                                    pos: pos,
                                });
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
                        "in" => {
                            push_token!(Token::In, tokens, line, pos);
                        }
                        "let" => {
                            push_token!(Token::Let, tokens, line, pos);
                        }
                        "not" => {
                            push_token!(Token::Not, tokens, line, pos);
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

    Ok(tokens)
}

#[cfg(test)]
mod tests {
    use crate::lexer;

    macro_rules! scan {
        ($input:expr, $( $value:expr),* ) => {{
            match lexer::scan($input) {
                Ok(mut tokens) => {
                    $(
                        match tokens.pop_front() {
                            Some(t) => {
                                assert_eq!(t.token, $value);
                            }
                            None => {}
                        }
                    )*
                    assert_eq!(tokens.len(), 0);
                }
                _ => assert!(false),
            }
        }};
    }

    macro_rules! scanfails {
        ($input:expr, $err:tt) => {{
            match lexer::scan($input) {
                Ok(_) => assert!(false),
                Err(e) => assert!(e.err.starts_with($err)),
            }
        }};
    }

    #[test]
    fn scanning() {
        scan!(
            "[1 2 3]",
            lexer::Token::LeftBracket,
            lexer::Token::Number(1.0),
            lexer::Token::Number(2.0),
            lexer::Token::Number(3.0),
            lexer::Token::RightBracket
        );
        scan!(
            "[1 2 3]",
            lexer::Token::LeftBracket,
            lexer::Token::Number(1.0),
            lexer::Token::Number(2.0),
            lexer::Token::Number(3.0),
            lexer::Token::RightBracket
        );
        scan!(
            "(())",
            lexer::Token::LeftParen,
            lexer::Token::LeftParen,
            lexer::Token::RightParen,
            lexer::Token::RightParen
        );
        scan!(":=", lexer::Token::ColonEqual);
        scanfails!("::", "Unexpected token");
        scanfails!(":", "Unexpected end");
        scan!(",", lexer::Token::Comma);
        scan!("-", lexer::Token::Minus);
        scan!("+", lexer::Token::Plus);
        scan!("/", lexer::Token::Slash);
        scan!("*", lexer::Token::Star);
        scan!("not not", lexer::Token::Not, lexer::Token::Not);
        scan!("<>", lexer::Token::NotEqual);
        scan!("==", lexer::Token::EqualEqual);
        scan!("<<", lexer::Token::Less, lexer::Token::Less);
        scan!("<=", lexer::Token::LessEqual);
        scan!(">>", lexer::Token::Greater, lexer::Token::Greater);
        scan!(">=", lexer::Token::GreaterEqual);
        scanfails!("'blah blah blah", "Unexpected end");
        scan!(
            "'blah blah blah'",
            lexer::Token::Str("blah blah blah".to_string())
        );
        scan!("4", lexer::Token::Number(4.0));
        scan!("42", lexer::Token::Number(42.0));
        scan!("42 ", lexer::Token::Number(42.0));
        scan!("4.2 ", lexer::Token::Number(4.2));
        scan!(
            "4+2",
            lexer::Token::Number(4.0),
            lexer::Token::Plus,
            lexer::Token::Number(2.0)
        );
        scan!("4 2", lexer::Token::Number(4.0), lexer::Token::Number(2.0));
        scan!(
            "let y := x + 1 in 2 * y end",
            lexer::Token::Let,
            lexer::Token::Identifier("y".to_string()),
            lexer::Token::ColonEqual,
            lexer::Token::Identifier("x".to_string()),
            lexer::Token::Plus,
            lexer::Token::Number(1.0),
            lexer::Token::In,
            lexer::Token::Number(2.0),
            lexer::Token::Star,
            lexer::Token::Identifier("y".to_string()),
            lexer::Token::End
        );
        scan!(
            "man and not mortal == false",
            lexer::Token::Identifier("man".to_string()),
            lexer::Token::And,
            lexer::Token::Not,
            lexer::Token::Identifier("mortal".to_string()),
            lexer::Token::EqualEqual,
            lexer::Token::False
        );
        scan!(
            "fn x(arg)\n    return arg*2\nend",
            lexer::Token::Function,
            lexer::Token::Identifier("x".to_string()),
            lexer::Token::LeftParen,
            lexer::Token::Identifier("arg".to_string()),
            lexer::Token::RightParen,
            lexer::Token::Return,
            lexer::Token::Identifier("arg".to_string()),
            lexer::Token::Star,
            lexer::Token::Number(2.0),
            lexer::Token::End
        );
        scan!(
            "if x then\n    1\nelsif y then\n    2\nelse\n    3\nend",
            lexer::Token::If,
            lexer::Token::Identifier("x".to_string()),
            lexer::Token::Then,
            lexer::Token::Number(1.0),
            lexer::Token::Elsif,
            lexer::Token::Identifier("y".to_string()),
            lexer::Token::Then,
            lexer::Token::Number(2.0),
            lexer::Token::Else,
            lexer::Token::Number(3.0),
            lexer::Token::End
        );
        scan!(
            "while true or false do\n    i := i + 1\n    break\nend",
            lexer::Token::While,
            lexer::Token::True,
            lexer::Token::Or,
            lexer::Token::False,
            lexer::Token::Do,
            lexer::Token::Identifier("i".to_string()),
            lexer::Token::ColonEqual,
            lexer::Token::Identifier("i".to_string()),
            lexer::Token::Plus,
            lexer::Token::Number(1.0),
            lexer::Token::Break,
            lexer::Token::End
        );
        scan!("continue", lexer::Token::Continue);
        scan!(
            "Ὦ := 'φῶς'",
            lexer::Token::Identifier("Ὦ".to_string()),
            lexer::Token::ColonEqual,
            lexer::Token::Str("φῶς".to_string())
        );
        scan!(
            "abd(def)",
            lexer::Token::Identifier("abd".to_string()),
            lexer::Token::LeftParen,
            lexer::Token::Identifier("def".to_string()),
            lexer::Token::RightParen
        );
        scan!(
            "&$123",
            lexer::Token::Identifier("&".to_string()),
            lexer::Token::Identifier("$123".to_string())
        );
    }
}
