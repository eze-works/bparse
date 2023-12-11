use std::cell::Cell;
mod byte_pattern;
mod pattern_repetition;

use byte_pattern::BytePattern;
use pattern_repetition::PatternRepetition;

/// Rexports of the parts of the crate commonly used together
pub mod prelude {
    pub use crate::b;
    pub use crate::byte_pattern::BytePattern;
    pub use crate::pattern_repetition::PatternRepetition;
}

/// A short-hand constructor for building a `&[u8]`
///
/// This `b("hello")` is slightly less verbose than this `&["hello"][..]`
pub fn b<S: AsRef<[u8]> + ?Sized>(s: &S) -> &[u8] {
    s.as_ref()
}

/// Returns a parser that will try to match `pattern`  
///
/// If the pattern matches, the parser will return the part of the input that matched and the rest
/// of the input bundled in a tuple
///
/// Look to the [`BytePattern`] `impl`s for what can be used as `pattern`
///
/// # Examples
///
pub fn parse(pattern: impl BytePattern) -> impl Fn(&[u8]) -> Option<(&[u8], &[u8])> {
    move |input: &[u8]| {
        let m = pattern.try_match(input)?;
        Some((m, &input[m.len()..]))
    }
}

#[cfg(test)]
mod tests {
    use super::parse;
    use super::prelude::*;

    #[test]
    fn test_accept() {}

    #[test]
    fn test_parse() {}
}

#[doc = include_str!("../README.md")]
#[cfg(doctest)]
pub struct ReadmeDocTests {}
