//! The Elella format.
#![warn(missing_docs)]

use std::collections::HashMap;
use std::error::Error;
use std::fmt;
use std::io;
use std::io::Read;
use std::iter::Peekable;
use std::num::ParseIntError;
use std::string::FromUtf8Error;

#[derive(Debug, PartialEq)]
enum Lit {
    Keyword(String),
    Var(String),
    Int(isize),
    Str(String),
    Bool(bool),
}

enum Expr {
    App(Box<Expr>, Vec<Expr>),
    Lit(Lit),
    List(Vec<Expr>),
    Vec(Vec<Expr>),
    Map(HashMap<String, Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
}

#[derive(Debug, PartialEq)]
enum Token {
    LParen,
    RParen,
    LBrack,
    RBrack,
    LBrace,
    RBrace,
    Semicolon,
    Lit(Lit),
    If,
    Def,
    Nil,
}

struct Lexer<R: Read + Sized> {
    bytes: Peekable<io::Bytes<R>>,
}

impl<R> Lexer<R>
where
    R: Read,
{
    fn new(r: R) -> Lexer<R> {
        Lexer { bytes: r.bytes().peekable() }
    }

    fn peek(&mut self) -> Result<&Result<u8, io::Error>, LexError> {
        match self.bytes.peek() {
            Some(r) => Ok(r),
            None => Err(LexError::EOF),
        }
    }

    fn next(&mut self) -> Result<u8, LexError> {
        self.bytes
            .next()
            .map(|r| r.map_err(|e| LexError::from(e)))
            .unwrap_or(Err(LexError::EOF))
    }

    fn lex(&mut self) -> Result<Token, LexError> {
        let b = self.next()?;
        match b {
            b' ' => self.lex(),
            b'(' => Ok(Token::LParen),
            b')' => Ok(Token::RParen),
            b'[' => Ok(Token::LBrack),
            b']' => Ok(Token::RBrack),
            b'{' => Ok(Token::LBrace),
            b'}' => Ok(Token::RBrace),
            b';' => Ok(Token::Semicolon),
            b'1'...b'9' => self.number(b),
            b':' => self.keyword(),
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
        self.read_number(&mut vec)?;
        Ok(Token::Lit(Lit::Int(String::from_utf8(vec)?.parse()?)))
    }

    fn read_number(&mut self, vec: &mut Vec<u8>) -> Result<(), LexError> {
        self.read(vec, is_digit)
    }

    fn keyword(&mut self) -> Result<Token, LexError> {
        let mut vec = Vec::new();
        self.read_keyword(&mut vec)?;
        Ok(Token::Lit(Lit::Keyword(String::from_utf8(vec)?)))
    }

    fn read_keyword(&mut self, vec: &mut Vec<u8>) -> Result<(), LexError> {
        self.read(vec, is_symbol)
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

#[derive(Debug)]
enum LexError {
    IO(io::Error),
    ParseInt(ParseIntError),
    Utf8(FromUtf8Error),
    EOF,
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
    fn is_eof(&self) -> bool {
        match self {
            &LexError::EOF => true,
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
            &LexError::EOF => "EOF",
            &LexError::Illegal => "Illegal byte",
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lexer() {
        let mut l = Lexer::new(&[b'(', b' ', b')'][..]);
        assert_eq!(l.lex().ok(), Some(Token::LParen));
        assert_eq!(l.lex().ok(), Some(Token::RParen));
        assert_eq!(l.lex().err().map(|e| e.is_eof()), Some(true));
    }

    #[test]
    fn test_lex_number() {
        let mut l = Lexer::new("123)".as_bytes());
        assert_eq!(l.lex().ok(), Some(Token::Lit(Lit::Int(123))));
        assert_eq!(l.lex().ok(), Some(Token::RParen));
        assert_eq!(l.lex().err().map(|e| e.is_eof()), Some(true));

        let mut l = Lexer::new("10".as_bytes());
        assert_eq!(l.lex().ok(), Some(Token::Lit(Lit::Int(10))));
        assert_eq!(l.lex().err().map(|e| e.is_eof()), Some(true));
    }

    #[test]
    fn test_lex_keyword() {
        let mut l = Lexer::new(":abc".as_bytes());
        assert_eq!(
            l.lex().ok(),
            Some(Token::Lit(Lit::Keyword(String::from("abc"))))
        );
        assert_eq!(l.lex().err().map(|e| e.is_eof()), Some(true));

        let mut l = Lexer::new(":aA*Z-]".as_bytes());
        assert_eq!(
            l.lex().ok(),
            Some(Token::Lit(Lit::Keyword(String::from("aA*Z-"))))
        );
        assert_eq!(l.lex().ok(), Some(Token::RBrack));
        assert_eq!(l.lex().err().map(|e| e.is_eof()), Some(true));
    }
}
