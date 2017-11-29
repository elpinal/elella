//! The Elella format.
#![warn(missing_docs)]

use std::collections::HashMap;
use std::error::Error;
use std::fmt;
use std::io;
use std::io::Read;

#[derive(Debug, PartialEq)]
enum Lit {
    Symbol(String),
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
    Lit(Lit),
}

struct Lexer<R: Read + Sized> {
    bytes: io::Bytes<R>,
}

impl<R> Lexer<R>
where
    R: Read,
{
    fn new(r: R) -> Lexer<R> {
        Lexer { bytes: r.bytes() }
    }

    fn next(&mut self) -> Result<Token, LexError> {
        let b = self.bytes
            .next()
            .map(|r| r.map_err(|e| LexError::from(e)))
            .unwrap_or(Err(LexError::EOF))?;
        match b {
            b' ' => self.next(),
            b'(' => Ok(Token::LParen),
            b')' => Ok(Token::RParen),
            b'[' => Ok(Token::LBrack),
            b']' => Ok(Token::RBrack),
            b'{' => Ok(Token::LBrace),
            b'}' => Ok(Token::RBrace),
            _ => Err(LexError::Illegal),
        }
    }
}

#[derive(Debug)]
enum LexError {
    IOError(io::Error),
    EOF,
    Illegal,
}

impl From<io::Error> for LexError {
    fn from(e: io::Error) -> LexError {
        LexError::IOError(e)
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
            &LexError::IOError(ref e) => e.fmt(f),
            &LexError::EOF => write!(f, "EOF"),
            &LexError::Illegal => write!(f, "Illegal byte"),
        }
    }
}

impl Error for LexError {
    fn description(&self) -> &str {
        match self {
            &LexError::IOError(ref e) => e.description(),
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
        assert_eq!(l.next().ok(), Some(Token::LParen));
        assert_eq!(l.next().ok(), Some(Token::RParen));
        assert_eq!(l.next().err().map(|e| e.is_eof()), Some(true));
    }
}
