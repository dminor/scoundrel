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
    Divides,
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
    Else,
    Elsif,
    End,
    False,
    Function,
    If,
    In,
    Let,
    Mod,
    Or,
    Recur,
    Then,
    True,
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
            Token::Divides => write!(f, "|"),
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
            Token::Else => write!(f, "else"),
            Token::Elsif => write!(f, "elsif"),
            Token::End => write!(f, "end"),
            Token::False => write!(f, "false"),
            Token::Function => write!(f, "fn"),
            Token::If => write!(f, "if"),
            Token::In => write!(f, "in"),
            Token::Let => write!(f, "let"),
            Token::Mod => write!(f, "mod"),
            Token::Not => write!(f, "not"),
            Token::Or => write!(f, "or"),
            Token::Recur => write!(f, "$"),
            Token::Then => write!(f, "then"),
            Token::True => write!(f, "true"),
        }
    }
}

#[derive(Debug)]
pub struct LexerError {
    pub err: String,
    pub line: usize,
}

impl fmt::Display for LexerError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "LexerError: {}", self.err)
    }
}

impl Error for LexerError {}

pub struct LexedToken {
    pub token: Token,
    pub line: usize,
}

macro_rules! push_token {
    ($T:expr, $tokens:ident, $line:ident) => {
        $tokens.push_back({
            LexedToken {
                token: $T,
                line: $line,
            }
        });
    };
}

pub fn scan(src: &str) -> Result<LinkedList<LexedToken>, LexerError> {
    let mut line = 1;
    let mut tokens = LinkedList::<LexedToken>::new();
    let mut chars = src.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '[' => {
                push_token!(Token::LeftBracket, tokens, line);
            }
            ']' => {
                push_token!(Token::RightBracket, tokens, line);
            }
            '(' => match chars.peek() {
                Some(c) => {
                    if *c == '*' {
                        loop {
                            match chars.next() {
                                Some(c) => match c {
                                    '*' => {
                                        if let Some(')') = chars.peek() {
                                            chars.next();
                                            break;
                                        }
                                    }
                                    '\n' => {
                                        line += 1;
                                    }
                                    _ => {}
                                },
                                None => {
                                    return Err(LexerError {
                                        err: "Unexpected end of input while scanning comment"
                                            .to_string(),
                                        line,
                                    });
                                }
                            }
                        }
                    } else {
                        push_token!(Token::LeftParen, tokens, line);
                    }
                }
                None => {
                    push_token!(Token::LeftParen, tokens, line);
                }
            },
            ')' => {
                push_token!(Token::RightParen, tokens, line);
            }
            ':' => match chars.next() {
                Some(c) => {
                    if c == '=' {
                        push_token!(Token::ColonEqual, tokens, line);
                    } else {
                        return Err(LexerError {
                            err: "Unexpected token while parsing :=".to_string(),
                            line,
                        });
                    }
                }
                _ => {
                    return Err(LexerError {
                        err: "Unexpected end of input while parsing :=".to_string(),
                        line,
                    });
                }
            },
            ',' => {
                push_token!(Token::Comma, tokens, line);
            }
            '-' => {
                push_token!(Token::Minus, tokens, line);
            }
            '+' => {
                push_token!(Token::Plus, tokens, line);
            }
            '/' => {
                push_token!(Token::Slash, tokens, line);
            }
            '*' => {
                push_token!(Token::Star, tokens, line);
            }
            '|' => {
                push_token!(Token::Divides, tokens, line);
            }
            '=' => {
                if let Some(c) = chars.peek() {
                    if *c == '=' {
                        push_token!(Token::EqualEqual, tokens, line);
                        chars.next();
                    } else {
                        return Err(LexerError {
                            err: "Unexpected end of input while parsing ==".to_string(),
                            line,
                        });
                    }
                }
            }
            '>' => match chars.peek() {
                Some(c) => {
                    if *c == '=' {
                        push_token!(Token::GreaterEqual, tokens, line);
                        chars.next();
                    } else {
                        push_token!(Token::Greater, tokens, line);
                    }
                }
                None => {
                    push_token!(Token::Greater, tokens, line);
                }
            },
            '<' => match chars.peek() {
                Some(c) => {
                    if *c == '=' {
                        push_token!(Token::LessEqual, tokens, line);
                        chars.next();
                    } else if *c == '>' {
                        push_token!(Token::NotEqual, tokens, line);
                        chars.next();
                    } else {
                        push_token!(Token::Less, tokens, line);
                    }
                }
                None => {
                    push_token!(Token::Less, tokens, line);
                }
            },
            '\'' => {
                let mut v = Vec::<char>::new();
                loop {
                    match chars.next() {
                        Some(c) => match c {
                            '\'' => {
                                push_token!(Token::Str(v.into_iter().collect()), tokens, line);
                                break;
                            }
                            '\n' => {
                                return Err(LexerError {
                                    err: "Unexpected end of line while scanning string".to_string(),
                                    line,
                                });
                            }
                            _ => v.push(c),
                        },
                        None => {
                            return Err(LexerError {
                                err: "Unexpected end of input while scanning string".to_string(),
                                line,
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
                while let Some(c) = chars.peek() {
                    if c.is_alphanumeric() || *c == '.' || *c == '?' {
                        v.push(*c);
                        chars.next();
                    } else {
                        break;
                    }
                }
                let s: String = v.into_iter().collect();
                match &s[..] {
                    "and" => {
                        push_token!(Token::And, tokens, line);
                    }
                    "else" => {
                        push_token!(Token::Else, tokens, line);
                    }
                    "elsif" => {
                        push_token!(Token::Elsif, tokens, line);
                    }
                    "end" => {
                        push_token!(Token::End, tokens, line);
                    }
                    "false" => {
                        push_token!(Token::False, tokens, line);
                    }
                    "fn" => {
                        push_token!(Token::Function, tokens, line);
                    }
                    "if" => {
                        push_token!(Token::If, tokens, line);
                    }
                    "in" => {
                        push_token!(Token::In, tokens, line);
                    }
                    "let" => {
                        push_token!(Token::Let, tokens, line);
                    }
                    "mod" => {
                        push_token!(Token::Mod, tokens, line);
                    }
                    "not" => {
                        push_token!(Token::Not, tokens, line);
                    }
                    "or" => {
                        push_token!(Token::Or, tokens, line);
                    }
                    "$" => {
                        push_token!(Token::Recur, tokens, line);
                    }
                    "then" => {
                        push_token!(Token::Then, tokens, line);
                    }
                    "true" => {
                        push_token!(Token::True, tokens, line);
                    }
                    _ => match s.parse::<f64>() {
                        Ok(n) => {
                            push_token!(Token::Number(n), tokens, line);
                        }
                        _ => {
                            push_token!(Token::Identifier(s.to_string()), tokens, line);
                        }
                    },
                }
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
        ($input:expr, $err:tt, $line:expr) => {{
            match lexer::scan($input) {
                Ok(_) => assert!(false),
                Err(e) => {
                    assert_eq!(e.err, $err);
                    assert_eq!(e.line, $line);
                }
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
        scanfails!("::", "Unexpected token while parsing :=", 1);
        scanfails!(":", "Unexpected end of input while parsing :=", 1);
        scan!(",", lexer::Token::Comma);
        scan!("-", lexer::Token::Minus);
        scan!("+", lexer::Token::Plus);
        scan!("/", lexer::Token::Slash);
        scan!("*", lexer::Token::Star);
        scan!("|", lexer::Token::Divides);
        scan!("not not", lexer::Token::Not, lexer::Token::Not);
        scan!("<>", lexer::Token::NotEqual);
        scan!("==", lexer::Token::EqualEqual);
        scan!("<<", lexer::Token::Less, lexer::Token::Less);
        scan!("<=", lexer::Token::LessEqual);
        scan!(">>", lexer::Token::Greater, lexer::Token::Greater);
        scan!(">=", lexer::Token::GreaterEqual);
        scanfails!(
            "(* blah\nblah\nblah",
            "Unexpected end of input while scanning comment",
            3
        );
        scanfails!(
            "'blah blah blah",
            "Unexpected end of input while scanning string",
            1
        );
        scanfails!(
            "'blah blah\nblah",
            "Unexpected end of line while scanning string",
            1
        );
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
            "fn x(param)\n    param*2\nend",
            lexer::Token::Function,
            lexer::Token::Identifier("x".to_string()),
            lexer::Token::LeftParen,
            lexer::Token::Identifier("param".to_string()),
            lexer::Token::RightParen,
            lexer::Token::Identifier("param".to_string()),
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
        scan!(
            "(* this is\na comment (* )\n*) 42",
            lexer::Token::Number(42.0)
        );
        scan!(
            "23 mod 4",
            lexer::Token::Number(23.0),
            lexer::Token::Mod,
            lexer::Token::Number(4.0)
        );
        scan!(
            "$(1 2)",
            lexer::Token::Recur,
            lexer::Token::LeftParen,
            lexer::Token::Number(1.0),
            lexer::Token::Number(2.0),
            lexer::Token::RightParen
        );
    }
}
