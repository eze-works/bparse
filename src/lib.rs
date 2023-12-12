use crate::pattern_repetition::PatternRepetition;
use bstr::ByteSlice;
use std::ops::{RangeFrom, RangeInclusive, RangeToInclusive};

mod pattern_repetition;
/// Rexports of the parts of the crate commonly used together
pub mod prelude {
    pub use crate::end;
    pub use crate::pattern_repetition::*;
    pub use crate::BytePattern;
}

/// Expresses that the implementing type can be used as a condition for matching a byte slice
pub trait BytePattern {
    fn test<'i>(&self, input: &'i [u8]) -> Option<(&'i [u8], &'i [u8])>;

    fn or<A>(self, next: A) -> Or<Self, A>
    where
        Self: Sized,
    {
        Or {
            pattern1: self,
            pattern2: next,
        }
    }

    fn then<P>(self, next: P) -> Then<Self, P>
    where
        Self: Sized,
    {
        Then {
            pattern1: self,
            pattern2: next,
        }
    }

    fn repeats<R: PatternRepetition>(self, count: R) -> Repeat<Self, R>
    where
        Self: Sized,
    {
        Repeat {
            pattern: self,
            count,
        }
    }
}

/// See [`BytePattern::or`]
#[derive(Clone, Copy, Debug)]
pub struct Or<C1, C2> {
    pattern1: C1,
    pattern2: C2,
}

/// See [`BytePattern::then`]
#[derive(Clone, Copy, Debug)]
pub struct Then<C1, C2> {
    pattern1: C1,
    pattern2: C2,
}

/// See [`BytePattern::repeats`]
#[derive(Clone, Copy, Debug)]
pub struct Repeat<P, R> {
    pattern: P,
    count: R,
}

/// A pattern that only matches the input if it is empty
pub fn end(input: &[u8]) -> Option<(&[u8], &[u8])> {
    if input.is_empty() {
        Some((&[], input))
    } else {
        None
    }
}

impl<C1: BytePattern, C2: BytePattern> BytePattern for Or<C1, C2> {
    fn test<'i>(&self, input: &'i [u8]) -> Option<(&'i [u8], &'i [u8])> {
        self.pattern1
            .test(input)
            .or_else(|| self.pattern2.test(input))
    }
}

impl<C1: BytePattern, C2: BytePattern> BytePattern for Then<C1, C2> {
    fn test<'i>(&self, input: &'i [u8]) -> Option<(&'i [u8], &'i [u8])> {
        let mut offset = 0;
        let Some((value, rest)) = self.pattern1.test(input) else {
            return None;
        };

        offset += value.len();

        let Some((value, rest)) = self.pattern2.test(rest) else {
            return None;
        };

        offset += value.len();

        Some((&input[..offset], rest))
    }
}

impl<P: BytePattern, R: PatternRepetition> BytePattern for Repeat<P, R> {
    fn test<'i>(&self, input: &'i [u8]) -> Option<(&'i [u8], &'i [u8])> {
        let mut counter = 0;
        let mut offset = 0;
        let lower_bound = self.count.lower_bound();
        if let Some(upper_bound) = self.count.upper_bound() {
            assert!(
                upper_bound >= lower_bound,
                "upper bound should be greater than or equal to the lower bound"
            );
        };

        loop {
            // We hit the upper bound of pattern repetition
            if let Some(upper_bound) = self.count.upper_bound() {
                if counter == upper_bound {
                    return Some((&input[..offset], &input[offset..]));
                }
            };

            let Some((value, _)) = self.pattern.test(&input[offset..]) else {
                if counter < lower_bound {
                    return None;
                }
                return Some((&input[..offset], &input[offset..]));
            };

            counter += 1;
            offset += value.len();
        }
    }
}

impl<F> BytePattern for F
where
    F: Fn(&[u8]) -> Option<(&[u8], &[u8])>,
{
    fn test<'i>(&self, input: &'i [u8]) -> Option<(&'i [u8], &'i [u8])> {
        (self)(input)
    }
}

impl BytePattern for &str {
    fn test<'i>(&self, input: &'i [u8]) -> Option<(&'i [u8], &'i [u8])> {
        let bytes = self.as_bytes();
        let Some(_) = input.strip_prefix(bytes) else {
            return None;
        };

        Some((&input[..self.len()], &input[self.len()..]))
    }
}

impl BytePattern for RangeFrom<u8> {
    fn test<'i>(&self, input: &'i [u8]) -> Option<(&'i [u8], &'i [u8])> {
        let first = *input.get(0)?;
        (first >= self.start).then_some((&input[0..1], &input[1..]))
    }
}

impl BytePattern for RangeFrom<char> {
    fn test<'i>(&self, input: &'i [u8]) -> Option<(&'i [u8], &'i [u8])> {
        let mut iter = input.char_indices();
        let (_, end, c) = iter.next()?;

        let c = c as u32;

        (c >= self.start as u32).then_some((&input[..end], &input[end..]))
    }
}

impl BytePattern for RangeToInclusive<u8> {
    fn test<'i>(&self, input: &'i [u8]) -> Option<(&'i [u8], &'i [u8])> {
        let first = *input.get(0)?;
        (first <= self.end).then_some((&input[0..1], &input[1..]))
    }
}

impl BytePattern for RangeToInclusive<char> {
    fn test<'i>(&self, input: &'i [u8]) -> Option<(&'i [u8], &'i [u8])> {
        let mut iter = input.char_indices();
        let (_, end, c) = iter.next()?;

        let c = c as u32;

        (c <= self.end as u32).then_some((&input[..end], &input[end..]))
    }
}

impl BytePattern for RangeInclusive<u8> {
    fn test<'i>(&self, input: &'i [u8]) -> Option<(&'i [u8], &'i [u8])> {
        let first = input.get(0)?;
        (first >= self.start() && first <= self.end()).then_some((&input[0..1], &input[1..]))
    }
}

impl BytePattern for RangeInclusive<char> {
    fn test<'i>(&self, input: &'i [u8]) -> Option<(&'i [u8], &'i [u8])> {
        let mut iter = input.char_indices();
        let (_, end, c) = iter.next()?;

        let c = c as u32;

        (c >= *self.start() as u32 && c <= *self.end() as u32)
            .then_some((&input[..end], &input[end..]))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn do_test(
        pattern: impl BytePattern,
        input: &'static [u8],
        result: Option<(&'static [u8], &'static [u8])>,
    ) {
        let out = pattern.test(input);
        assert_eq!(result, out);
    }

    #[test]
    fn test_parse_patterns() {
        // Parsing using string slices
        do_test("", b"a1b2", Some((b"", b"a1b2")));
        do_test("a", b"a1b2", Some((b"a", b"1b2")));
        do_test("١", b"\xd9\xa1", Some((b"\xd9\xa1", &[])));

        // Parsing using byte ranges
        do_test(97.., b"a1b2", Some((b"a", b"1b2")));
        do_test(..=97, b"a1b2", Some((b"a", b"1b2")));
        do_test(96..=98, b"a1b2", Some((b"a", b"1b2")));

        // Parsing using char ranges
        do_test('٠'..='٩', b"\xd9\xa1", Some((b"\xd9\xa1", &[])));
        do_test(..='٩', b"\xd9\xa1", Some((b"\xd9\xa1", &[])));
        do_test('٠'.., b"\xd9\xa1", Some((b"\xd9\xa1", &[])));

        // Parsing using alternatives
        do_test("b".or(97..), b"a1b2", Some((b"a", b"1b2")));

        // Parsing in sequence
        do_test("9".then("7").then("8"), b"978", Some((b"978", b"")));

        // Parsing using functions
        fn parse_a(input: &[u8]) -> Option<(&[u8], &[u8])> {
            let first = input.get(0)?;

            (*first == b'a').then_some((&input[0..1], &input[1..]))
        }

        fn parse_1(input: &[u8]) -> Option<(&[u8], &[u8])> {
            let first = input.get(0)?;

            (*first == b'1').then_some((&input[0..1], &input[1..]))
        }

        do_test(parse_a.then(parse_1), b"a1b2", Some((b"a1", b"b2")))
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
    }
}

#[doc = include_str!("../README.md")]
#[cfg(doctest)]
pub struct ReadmeDocTests {}
