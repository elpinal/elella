//! The Elella format.
#![warn(missing_docs)]

enum Term {
    Symbol(String),
    Int(isize),
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}