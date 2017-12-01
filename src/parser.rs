//! A parser for the Elella format.
//!
//! ```
//! use elella::parser::*;
//!
//! let mut p = Parser::new(r#"[:a "x"]"#.as_bytes());
//! assert_eq!(
//!     p.parse().ok(),
//!     Some(Expr::Vec(vec![
//!         Expr::Lit(Lit::Keyword(String::from("a"))),
//!         Expr::Lit(Lit::Str(String::from("x")))
//!     ])));
//! ```

use std::collections::HashMap;
use std::io::Read;

use lexer::*;

pub use lexer::Lit;

#[derive(Debug, PartialEq)]
pub enum Expr {
    App(Box<Expr>, Vec<Expr>),
    Lit(Lit),
    List(Vec<Expr>),
    Vec(Vec<Expr>),
    Map(HashMap<String, Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
}

pub struct Parser<R: Read> {
    l: Lexer<R>,
}

impl<R: Read> Parser<R> {
    pub fn new(r: R) -> Parser<R> {
        Parser { l: Lexer::new(r) }
    }

    pub fn parse(&mut self) -> Result<Expr, ParseError> {
        match self.l.lex()? {
            Token::LBrack => self.vector(),
            Token::LBrace => self.map(),
            _ => unimplemented!(),
        }
    }

    fn vector(&mut self) -> Result<Expr, ParseError> {
        let mut vec = Vec::new();
        loop {
            match self.l.lex()? {
                Token::RBrack => return Ok(Expr::Vec(vec)),
                Token::Lit(l) => vec.push(Expr::Lit(l)),
                _ => unimplemented!(),
            }
        }
    }

    fn map(&mut self) -> Result<Expr, ParseError> {
        let mut m = HashMap::new();
        loop {
            let k;
            match self.l.lex()? {
                Token::RBrace => return Ok(Expr::Map(m)),
                Token::Lit(Lit::Keyword(s)) => k = s,
                _ => unimplemented!(),
            }
            match self.l.lex()? {
                Token::RBrace => panic!("not even map"),
                Token::Lit(l) => {
                    if m.insert(k.clone(), Expr::Lit(l)).is_some() {
                        return Err(ParseError::DupKeys(k));
                    }
                }
                _ => unimplemented!(),
            }
        }
    }
}

pub enum ParseError {
    Lex(LexError),
    DupKeys(String),
}

impl From<LexError> for ParseError {
    fn from(e: LexError) -> ParseError {
        ParseError::Lex(e)
    }
}

impl ParseError {
    fn is_dupkeys(&self) -> bool {
        if let &ParseError::DupKeys(_) = self {
            true
        } else {
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! parse_test {
        ( $s:expr, $( $x:expr ),* ) => {
            {
                let mut l = Parser::new($s.as_bytes());
                $(
                    assert_eq!(l.parse().ok(), Some($x));
                )*
            }
        };
    }

    #[test]
    fn test_parse_vector() {
        parse_test!("[]", Expr::Vec(Vec::new()));
        parse_test!("[1]", Expr::Vec(vec![Expr::Lit(Lit::Int(1))]));
        parse_test!(
            "[:a x]",
            Expr::Vec(vec![
                Expr::Lit(Lit::Keyword(String::from("a"))),
                Expr::Lit(Lit::Var(String::from("x"))),
            ])
        );
        parse_test!(
            "[:a, x]",
            Expr::Vec(vec![
                Expr::Lit(Lit::Keyword(String::from("a"))),
                Expr::Lit(Lit::Var(String::from("x"))),
            ])
        );
    }

    #[test]
    fn test_parse_map() {
        parse_test!("{}", Expr::Map(HashMap::new()));

        let mut m = HashMap::new();
        m.insert(String::from("a"), Expr::Lit(Lit::Int(1)));
        parse_test!("{:a 1}", Expr::Map(m));

        let mut m = HashMap::new();
        m.insert(String::from("a"), Expr::Lit(Lit::Int(1)));
        m.insert(
            String::from("b"),
            Expr::Lit(Lit::Keyword(String::from("c"))),
        );
        parse_test!("{:a 1, :b :c}", Expr::Map(m));
    }

    #[test]
    fn test_parse_map_fail() {
        let mut p = Parser::new("{:a 1, :a :c}".as_bytes());
        assert!(p.parse().unwrap_err().is_dupkeys());
    }
}
