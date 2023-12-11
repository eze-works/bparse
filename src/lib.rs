mod byte_pattern;
mod pattern_repetition;

use byte_pattern::BytePattern;
use pattern_repetition::PatternRepetition;

/// Rexports of the parts of the crate commonly used together
pub mod prelude {
    pub use crate::byte_pattern::BytePattern;
    pub use crate::pattern_repetition::PatternRepetition;
    pub use crate::{b, parse};
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
pub fn parse(
    pattern: impl BytePattern,
    count: impl PatternRepetition,
) -> impl Fn(&[u8]) -> Option<(&[u8], &[u8])> {
    move |input: &[u8]| {
        let mut counter = 0;
        let mut offset = 0;
        let lower_bound = count.lower_bound();
        if let Some(upper_bound) = count.upper_bound() {
            assert!(
                upper_bound >= lower_bound,
                "upper bound should be greater than or equal to the lower bound"
            );
        };

        loop {
            // We hit the upper bound of pattern repetition
            if let Some(upper_bound) = count.upper_bound() {
                if counter == upper_bound {
                    return Some((&input[..offset], &input[offset..]));
                }
            };

            let Some(v) = pattern.try_match(&input[offset..]) else {
                if counter < lower_bound {
                    return None;
                }
                return Some((&input[..offset], &input[offset..]));
            };

            counter += 1;
            offset += v.len();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::prelude::*;

    fn do_test<P: BytePattern, C: PatternRepetition>(
        pattern: P,
        count: C,
        input: &'static [u8],
        result: Option<(&'static [u8], &'static [u8])>,
    ) {
        let out = parse(pattern, count)(input);
        assert_eq!(result, out);
    }

    #[test]
    fn test_parse_patterns() {
        // Parsing string slices
        do_test("", 1, b"a1b2", Some((b"", b"a1b2")));

        // Parsing using string slices
        do_test("a", 1, b"a1b2", Some((b"a", b"1b2")));

        // Parsing using byte ranges
        do_test(97, 1, b"a1b2", Some((b"a", b"1b2")));
        do_test(97.., 1, b"a1b2", Some((b"a", b"1b2")));
        do_test(..=97, 1, b"a1b2", Some((b"a", b"1b2")));
        do_test(96..=98, 1, b"a1b2", Some((b"a", b"1b2")));

        // Parsing using char ranges
        do_test("١", 1, b"\xd9\xa1", Some((b"\xd9\xa1", &[])));
        do_test('٠'..='٩', 1, b"\xd9\xa1", Some((b"\xd9\xa1", &[])));
        do_test(..='٩', 1, b"\xd9\xa1", Some((b"\xd9\xa1", &[])));
        do_test('٠'.., 1, b"\xd9\xa1", Some((b"\xd9\xa1", &[])));
    }

    #[test]
    fn test_parse_repetition() {
        // Bounded on both ends
        do_test("a", 0..=0, b"aabb", Some((b"", b"aabb")));
        do_test("a", 1..=1, b"aabb", Some((b"a", b"abb")));
        do_test("a", 1..=2, b"aabb", Some((b"aa", b"bb")));
        do_test("a", 1..=10, b"aabb", Some((b"aa", b"bb")));

        // Lower bound
        do_test("a", 0.., b"aaaab", Some((b"aaaa", b"b")));
        do_test("a", 4.., b"aaaab", Some((b"aaaa", b"b")));
        do_test("a", 5.., b"aaaab", None);

        // Upper bound
        do_test("a", ..=3, b"bb", Some((b"", b"bb")));
        do_test("a", ..=0, b"aaabb", Some((b"", b"aaabb")));
        do_test("a", ..=1, b"aaabb", Some((b"a", b"aabb")));
        do_test("a", ..=10, b"aaabb", Some((b"aaa", b"bb")));
    }
}

#[doc = include_str!("../README.md")]
#[cfg(doctest)]
pub struct ReadmeDocTests {}
