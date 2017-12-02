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

/// An expression.
#[derive(Debug, PartialEq)]
pub enum Expr {
    /// A function application which contains a functions and its arguments.
    App(Box<Expr>, Vec<Expr>),
    /// A literal expression.
    Lit(Lit),
    /// A list.
    List(Vec<Expr>),
    /// A vector.
    Vec(Vec<Expr>),
    Map(HashMap<String, Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
}

/// A parser which contaiins its reader.
pub struct Parser<R: Read> {
    l: Lexer<R>,
}

impl<R: Read> Parser<R> {
    /// Creates a new parser with a input reader.
    ///
    /// ```
    /// use elella::parser::Parser;
    ///
    /// let p = Parser::new("abcd".as_bytes());
    /// ```
    pub fn new(r: R) -> Parser<R> {
        Parser { l: Lexer::new(r) }
    }

    /// Parses an expression from the inner reader.
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
                Token::RBrace => return Err(ParseError::OddMap),
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

/// Errors which represents some errors on parsing.
pub enum ParseError {
    /// Lexing error.
    Lex(LexError),
    /// Duplicate keys in map literals.
    DupKeys(String),
    /// An odd number of entries in map literals.
    OddMap,
}

impl From<LexError> for ParseError {
    fn from(e: LexError) -> ParseError {
        ParseError::Lex(e)
    }
}

impl ParseError {
    fn is_dupkeys(&self) -> bool {
        match self {
            &ParseError::DupKeys(_) => true,
            _ => false,
        }
    }

    fn is_oddmap(&self) -> bool {
        match self {
            &ParseError::OddMap => true,
            _ => false,
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

        let mut p = Parser::new("{:a 1, :b}".as_bytes());
        assert!(p.parse().unwrap_err().is_oddmap());
    }
}
