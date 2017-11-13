//! The Elella format.
#![warn(missing_docs)]

enum Term {
    Symbol(String),
    Var(String),
    Int(isize),
    Str(String),
    Bool(bool),
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
