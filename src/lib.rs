//! The Elella format.
#![warn(missing_docs)]

use std::collections::HashMap;

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

enum Token {
    LParen,
    RParen,
    LBrack,
    RBrack,
    LBrace,
    RBrace,
    Lit(Lit),
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
