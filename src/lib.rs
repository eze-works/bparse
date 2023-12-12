mod byte_pattern;
mod pattern_repetition;

use byte_pattern::BytePattern;

/// Rexports of the parts of the crate commonly used together
pub mod prelude {
    pub use crate::byte_pattern::BytePattern;
    pub use crate::parse;
    pub use crate::pattern_repetition::PatternRepetition;
}

/// Returns a parser that will try to match `pattern`  
///
/// If the pattern matches, the parser will return a tuple made up of the slice of input that
/// matched, and the rest of the input
///
/// Look to the [`BytePattern`] `impl`s for what can be used as `pattern`
pub fn parse(pattern: impl BytePattern) -> impl Fn(&[u8]) -> Option<(&[u8], &[u8])> {
    move |input: &[u8]| {
        let out = pattern.try_match(input)?;

        Some((out, &input[out.len()..]))
    }
}

#[cfg(test)]
mod tests {
    use super::prelude::*;

    fn do_test<P: BytePattern>(
        pattern: P,
        input: &'static [u8],
        result: Option<(&'static [u8], &'static [u8])>,
    ) {
        let out = parse(pattern)(input);
        assert_eq!(result, out);
    }

    #[test]
    fn test_parse_patterns() {
        // Parsing using string slices
        do_test("", b"a1b2", Some((b"", b"a1b2")));
        do_test("a", b"a1b2", Some((b"a", b"1b2")));
        do_test("١", b"\xd9\xa1", Some((b"\xd9\xa1", &[])));

        // Parsing using bytes
        do_test(97, b"a1b2", Some((b"a", b"1b2")));

        // Parsing using byte ranges and their references
        do_test(97.., b"a1b2", Some((b"a", b"1b2")));
        do_test(&(97..), b"a1b2", Some((b"a", b"1b2")));
        do_test(..=97, b"a1b2", Some((b"a", b"1b2")));
        do_test(&(..=97), b"a1b2", Some((b"a", b"1b2")));
        do_test(96..=98, b"a1b2", Some((b"a", b"1b2")));
        do_test(&(96..=98), b"a1b2", Some((b"a", b"1b2")));

        // Parsing using char ranges and their references
        do_test('٠'..='٩', b"\xd9\xa1", Some((b"\xd9\xa1", &[])));
        do_test(&('٠'..='٩'), b"\xd9\xa1", Some((b"\xd9\xa1", &[])));
        do_test(..='٩', b"\xd9\xa1", Some((b"\xd9\xa1", &[])));
        do_test(&(..='٩'), b"\xd9\xa1", Some((b"\xd9\xa1", &[])));
        do_test('٠'.., b"\xd9\xa1", Some((b"\xd9\xa1", &[])));
        do_test(&('٠'..), b"\xd9\xa1", Some((b"\xd9\xa1", &[])));

        // Parsing using alternatives
        do_test("b".or(97), b"a1b2", Some((b"a", b"1b2")));
        do_test(&("b".or(97)), b"a1b2", Some((b"a", b"1b2")));

        // Parsing in sequence
        do_test("9".then("7").then("8"), b"978", Some((b"978", b"")));
        do_test(&("9".then("7").then("8")), b"978", Some((b"978", b"")));
    }

    #[test]
    fn test_parse_repetition() {
        // Bounded on both ends
        do_test("a".repeats(0..=0), b"aabb", Some((b"", b"aabb")));
        do_test("a".repeats(1..=1), b"aabb", Some((b"a", b"abb")));
        do_test("a".repeats(1..=2), b"aabb", Some((b"aa", b"bb")));
        do_test("a".repeats(1..=10), b"aabb", Some((b"aa", b"bb")));

        // Lower bound
        do_test("a".repeats(0..), b"aaaab", Some((b"aaaa", b"b")));
        do_test("a".repeats(4..), b"aaaab", Some((b"aaaa", b"b")));
        do_test("a".repeats(5..), b"aaaab", None);

        // Upper bound
        do_test("a".repeats(..=3), b"bb", Some((b"", b"bb")));
        do_test("a".repeats(..=0), b"aaabb", Some((b"", b"aaabb")));
        do_test("a".repeats(..=1), b"aaabb", Some((b"a", b"aabb")));
        do_test("a".repeats(..=10), b"aaabb", Some((b"aaa", b"bb")));

        // References to bounds also work
        do_test("a".repeats(&(0..=0)), b"aabb", Some((b"", b"aabb")));
        do_test("a".repeats(&(0..)), b"aaaab", Some((b"aaaa", b"b")));
        do_test("a".repeats(&(..=3)), b"bb", Some((b"", b"bb")));
    }
}

#[doc = include_str!("../README.md")]
#[cfg(doctest)]
pub struct ReadmeDocTests {}
