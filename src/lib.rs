//! The Elella format.
#![warn(missing_docs)]

use std::collections::HashMap;
use std::error::Error;
use std::fmt;
use std::io;
use std::io::Read;
use std::iter::Peekable;
use std::num::ParseIntError;

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
    Lit(Lit),
    If,
    Def,
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
            b'1'...b'9' => self.number(b),
            b':' => self.keyword(),
            _ => Err(LexError::Illegal),
        }
    }

    fn number(&mut self, start: u8) -> Result<Token, LexError> {
        let mut vec = vec![start];
        loop {
            let b = match self.peek()? {
                &Ok(b) => b,
                &Err(_) => self.next()?,
            };
            match b {
                b'0'...b'9' => vec.push(b),
                _ => break,
            }
            self.next()?;
        }
        let s = String::from_utf8_lossy(&vec);
        let n: isize = s.parse()?;
        Ok(Token::Lit(Lit::Int(n)))
    }

    fn keyword(&mut self) -> Result<Token, LexError> {
        let mut vec = Vec::new();
        loop {
            let j = self.bytes.peek();
            if j.is_none() {
                break;
            }
            let b = match j.unwrap() {
                &Ok(b) => b,
                &Err(_) => self.next()?,
            };
            match b {
                b'a'...b'z' | b'A'...b'Z' => vec.push(b),
                _ => break,
            }
            self.next()?;
        }
        let s = String::from_utf8_lossy(&vec);
        Ok(Token::Lit(Lit::Keyword(String::from(s))))
    }
}

#[derive(Debug)]
enum LexError {
    IOError(io::Error),
    ParseInt(ParseIntError),
    EOF,
    Illegal,
}

impl From<io::Error> for LexError {
    fn from(e: io::Error) -> LexError {
        LexError::IOError(e)
    }
}

impl From<ParseIntError> for LexError {
    fn from(e: ParseIntError) -> LexError {
        LexError::ParseInt(e)
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
            &LexError::ParseInt(ref e) => e.fmt(f),
            &LexError::EOF => write!(f, "EOF"),
            &LexError::Illegal => write!(f, "Illegal byte"),
        }
    }
}

impl Error for LexError {
    fn description(&self) -> &str {
        match self {
            &LexError::IOError(ref e) => e.description(),
            &LexError::ParseInt(ref e) => e.description(),
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
    }

    #[test]
    fn test_lex_keyword() {
        let mut l = Lexer::new(":abc".as_bytes());
        assert_eq!(
            l.lex().ok(),
            Some(Token::Lit(Lit::Keyword(String::from("abc"))))
        );
        assert_eq!(l.lex().err().map(|e| e.is_eof()), Some(true));
    }
}
