//! The Elella format.
#![warn(missing_docs)]

pub mod lexer;

use std::collections::HashMap;

enum Expr {
    App(Box<Expr>, Vec<Expr>),
    Lit(lexer::Lit),
    List(Vec<Expr>),
    Vec(Vec<Expr>),
    Map(HashMap<String, Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
}
