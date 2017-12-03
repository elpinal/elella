//! A lexer for the Elella format.
//!
//! ```
//! use elella::lexer::*;
//!
//! let mut l = Lexer::new("[:a 1]".as_bytes());
//! assert_eq!(l.lex().ok(), Some(Token::LBrack));
//! assert_eq!(l.lex().ok(), Some(Token::Lit(Lit::Keyword(String::from("a")))));
//! assert_eq!(l.lex().ok(), Some(Token::Lit(Lit::Int(1))));
//! assert_eq!(l.lex().ok(), Some(Token::RBrack));
//! assert_eq!(l.lex().unwrap_err().is_eof(), true);
//! ```

use std::error::Error;
use std::fmt;
use std::io;
use std::io::Read;
use std::iter::Peekable;
use std::num::ParseIntError;
use std::string::FromUtf8Error;

/// A literal.
#[derive(Debug, PartialEq)]
pub enum Lit {
    Keyword(String),
    Var(String),
    Int(isize),
    Str(String),
    Bool(bool),
}

/// A token.
#[derive(Debug, PartialEq)]
pub enum Token {
    /// '('.
    LParen,
    /// ')'.
    RParen,
    /// '['.
    LBrack,
    /// ']'.
    RBrack,
    /// '{'.
    LBrace,
    /// '}'.
    RBrace,
    Semicolon,
    Lit(Lit),
    If,
    Def,
    Nil,
}

/// A lexer.
pub struct Lexer<R: Read + Sized> {
    bytes: Peekable<io::Bytes<R>>,
}

impl<R> Lexer<R>
where
    R: Read,
{
    /// Creates a new lexer.
    pub fn new(r: R) -> Lexer<R> {
        Lexer { bytes: r.bytes().peekable() }
    }

    fn next(&mut self) -> Result<u8, LexError> {
        self.bytes
            .next()
            .map(|r| r.map_err(|e| LexError::from(e)))
            .unwrap_or(Err(LexError::EOF))
    }

    /// Lexes a token from inner bytes.
    pub fn lex(&mut self) -> Result<Token, LexError> {
        let b = self.next()?;
        match b {
            b' ' | b',' => self.lex(),
            b'(' => Ok(Token::LParen),
            b')' => Ok(Token::RParen),
            b'[' => Ok(Token::LBrack),
            b']' => Ok(Token::RBrack),
            b'{' => Ok(Token::LBrace),
            b'}' => Ok(Token::RBrace),
            b';' => Ok(Token::Semicolon),
            b'1'...b'9' => self.number(b),
            b':' => self.keyword(),
            b'"' => self.string(),
            _ if is_symbol(b) => self.ident(b),
            _ => Err(LexError::Illegal),
        }
    }

    fn read<P>(&mut self, vec: &mut Vec<u8>, p: P) -> Result<(), LexError>
    where
        P: Fn(u8) -> bool,
    {
        loop {
            match self.bytes.peek() {
                None => return Ok(()),
                Some(k) => {
                    if let &Ok(b) = k {
                        if !p(b) {
                            return Ok(());
                        }
                        vec.push(b);
                    }
                }
            }
            self.bytes.next().unwrap()?;
        }
    }

    fn number(&mut self, start: u8) -> Result<Token, LexError> {
        let mut vec = vec![start];
        self.read(&mut vec, is_digit)?;
        Ok(Token::Lit(Lit::Int(String::from_utf8(vec)?.parse()?)))
    }

    fn keyword(&mut self) -> Result<Token, LexError> {
        let mut vec = Vec::new();
        self.read(&mut vec, is_symbol)?;
        if vec.is_empty() {
            return Err(LexError::Illegal);
        }
        Ok(Token::Lit(Lit::Keyword(String::from_utf8(vec)?)))
    }

    fn ident(&mut self, start: u8) -> Result<Token, LexError> {
        let mut vec = vec![start];
        self.read(&mut vec, is_symbol)?;
        let s = String::from_utf8(vec)?;
        match s {
            _ if s == "true" => Ok(Token::Lit(Lit::Bool(true))),
            _ if s == "false" => Ok(Token::Lit(Lit::Bool(false))),
            _ => Ok(Token::Lit(Lit::Var(s))),
        }
    }

    fn string(&mut self) -> Result<Token, LexError> {
        let mut vec = Vec::new();
        self.read(&mut vec, |b| b != b'"')?;
        if self.bytes.next().is_none() {
            return Err(LexError::Terminate);
        }
        Ok(Token::Lit(Lit::Str(String::from_utf8(vec)?)))
    }
}

fn is_digit(b: u8) -> bool {
    match b {
        b'0'...b'9' => true,
        _ => false,
    }
}

fn is_symbol(b: u8) -> bool {
    match b {
        b'a'...b'z' | b'A'...b'Z' | b'-' | b'*' | b'\'' => true,
        _ => false,
    }
}

/// An error while lexing.
#[derive(Debug)]
pub enum LexError {
    /// Error on IO.
    IO(io::Error),
    /// Invalid integer literal.
    ParseInt(ParseIntError),
    /// Invalid UTF-8 error.
    Utf8(FromUtf8Error),
    /// An error that indicates "string literal is not terminated."
    Terminate,
    /// EOF.
    EOF,
    /// Illegal byte.
    Illegal,
}

impl From<io::Error> for LexError {
    fn from(e: io::Error) -> LexError {
        LexError::IO(e)
    }
}

impl From<ParseIntError> for LexError {
    fn from(e: ParseIntError) -> LexError {
        LexError::ParseInt(e)
    }
}

impl From<FromUtf8Error> for LexError {
    fn from(e: FromUtf8Error) -> LexError {
        LexError::Utf8(e)
    }
}

impl LexError {
    fn is_terminate(&self) -> bool {
        match self {
            &LexError::Terminate => true,
            _ => false,
        }
    }

    /// Test an error is caused by EOF.
    pub fn is_eof(&self) -> bool {
        match self {
            &LexError::EOF => true,
            _ => false,
        }
    }

    fn is_illegal(&self) -> bool {
        match self {
            &LexError::Illegal => true,
            _ => false,
        }
    }
}

impl fmt::Display for LexError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &LexError::IO(ref e) => e.fmt(f),
            &LexError::ParseInt(ref e) => e.fmt(f),
            &LexError::Utf8(ref e) => e.fmt(f),
            &LexError::Terminate => write!(f, "EOF while string literal not terminated"),
            &LexError::EOF => write!(f, "EOF"),
            &LexError::Illegal => write!(f, "Illegal byte"),
        }
    }
}

impl Error for LexError {
    fn description(&self) -> &str {
        match self {
            &LexError::IO(ref e) => e.description(),
            &LexError::ParseInt(ref e) => e.description(),
            &LexError::Utf8(ref e) => e.description(),
            &LexError::Terminate => "EOF while string literal not terminated",
            &LexError::EOF => "EOF",
            &LexError::Illegal => "Illegal byte",
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! lex_test {
        ( $s:expr, $( $x:expr ),* ) => {
            {
                let mut l = Lexer::new($s.as_bytes());
                $(
                    assert_eq!(l.lex().ok(), Some($x));
                )*
                assert_eq!(l.lex().err().map(|e| e.is_eof()), Some(true));
            }
        };
    }

    #[test]
    fn test_lexer() {
        lex_test!("( )", Token::LParen, Token::RParen);
        lex_test!("(,)", Token::LParen, Token::RParen);
    }

    #[test]
    fn test_lex_number() {
        lex_test!("123)", Token::Lit(Lit::Int(123)), Token::RParen);

        lex_test!("10", Token::Lit(Lit::Int(10)));
    }

    #[test]
    fn test_lex_keyword() {
        let mut l = Lexer::new(":".as_bytes());
        assert_eq!(l.lex().err().map(|e| e.is_illegal()), Some(true));

        lex_test!(":abc", Token::Lit(Lit::Keyword(String::from("abc"))));

        lex_test!(
            ":aA*Z-]",
            Token::Lit(Lit::Keyword(String::from("aA*Z-"))),
            Token::RBrack
        );
    }

    #[test]
    fn test_lex_var() {
        lex_test!("abc", (Token::Lit(Lit::Var(String::from("abc")))));

        lex_test!(
            "aA*Z-:***",
            (Token::Lit(Lit::Var(String::from("aA*Z-")))),
            (Token::Lit(Lit::Keyword(String::from("***"))))
        );
    }

    #[test]
    fn test_lex_reserved() {
        lex_test!("true", (Token::Lit(Lit::Bool(true))));

        lex_test!("false", (Token::Lit(Lit::Bool(false))));

        lex_test!("tru", (Token::Lit(Lit::Var(String::from("tru")))));

        lex_test!("truE", (Token::Lit(Lit::Var(String::from("truE")))));

        lex_test!("trues", (Token::Lit(Lit::Var(String::from("trues")))));
    }

    #[test]
    fn test_lex_string() {
        lex_test!(r#""""#, (Token::Lit(Lit::Str(String::from("")))));

        lex_test!(r#""abc""#, (Token::Lit(Lit::Str(String::from("abc")))));

        lex_test!(
            r#""aA* Z-:***":a"#,
            (Token::Lit(Lit::Str(String::from("aA* Z-:***")))),
            (Token::Lit(Lit::Keyword(String::from("a"))))
        );

        let mut l = Lexer::new(r#""abc"#.as_bytes());
        assert_eq!(l.lex().err().map(|e| e.is_terminate()), Some(true));
    }
}
