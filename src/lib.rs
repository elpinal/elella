//! The Elella format.
#![warn(missing_docs)]

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
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
