#![warn(missing_docs)]

//! A library for matching patterns in byte slices

use bstr::ByteSlice;
use std::ops::{RangeFrom, RangeInclusive, RangeToInclusive};

pub mod pattern;

/// Expresses that the implementing type can be used to match a byte slice
pub trait Pattern {
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

    fn repeats<R: Repetition>(self, count: R) -> Repeat<Self, R>
    where
        Self: Sized,
    {
        Repeat {
            pattern: self,
            count,
        }
    }

    fn peek(self) -> Peek<Self>
    where
        Self: Sized,
    {
        Peek { pattern: self }
    }

    fn optional(self) -> Optional<Self>
    where
        Self: Sized,
    {
        Optional { pattern: self }
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

/// See [`BytePattern::peek`]
#[derive(Clone, Copy, Debug)]
pub struct Peek<P> {
    pattern: P,
}

/// See [`BytePattern::optional`]
#[derive(Clone, Copy, Debug)]
pub struct Optional<P> {
    pattern: P,
}

impl<C1: Pattern, C2: Pattern> Pattern for Or<C1, C2> {
    fn test<'i>(&self, input: &'i [u8]) -> Option<(&'i [u8], &'i [u8])> {
        self.pattern1
            .test(input)
            .or_else(|| self.pattern2.test(input))
    }
}

impl<C1: Pattern, C2: Pattern> Pattern for Then<C1, C2> {
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

impl<P: Pattern, R: Repetition> Pattern for Repeat<P, R> {
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

impl<P> Pattern for Peek<P>
where
    P: Pattern,
{
    fn test<'i>(&self, input: &'i [u8]) -> Option<(&'i [u8], &'i [u8])> {
        let Some((value, _)) = self.pattern.test(input) else {
            return None;
        };

        Some((value, input))
    }
}

impl<P> Pattern for Optional<P>
where
    P: Pattern,
{
    fn test<'i>(&self, input: &'i [u8]) -> Option<(&'i [u8], &'i [u8])> {
        self.pattern.test(input).or(Some((b"", input)))
    }
}

impl<F> Pattern for F
where
    F: Fn(&[u8]) -> Option<(&[u8], &[u8])>,
{
    fn test<'i>(&self, input: &'i [u8]) -> Option<(&'i [u8], &'i [u8])> {
        (self)(input)
    }
}

impl Pattern for &str {
    fn test<'i>(&self, input: &'i [u8]) -> Option<(&'i [u8], &'i [u8])> {
        let bytes = self.as_bytes();
        let Some(_) = input.strip_prefix(bytes) else {
            return None;
        };

        Some((&input[..self.len()], &input[self.len()..]))
    }
}

impl Pattern for RangeFrom<u8> {
    fn test<'i>(&self, input: &'i [u8]) -> Option<(&'i [u8], &'i [u8])> {
        let first = *input.get(0)?;
        (first >= self.start).then_some((&input[0..1], &input[1..]))
    }
}

impl Pattern for RangeFrom<char> {
    fn test<'i>(&self, input: &'i [u8]) -> Option<(&'i [u8], &'i [u8])> {
        let mut iter = input.char_indices();
        let (_, end, c) = iter.next()?;

        let c = c as u32;

        (c >= self.start as u32).then_some((&input[..end], &input[end..]))
    }
}

impl Pattern for RangeToInclusive<u8> {
    fn test<'i>(&self, input: &'i [u8]) -> Option<(&'i [u8], &'i [u8])> {
        let first = *input.get(0)?;
        (first <= self.end).then_some((&input[0..1], &input[1..]))
    }
}

impl Pattern for RangeToInclusive<char> {
    fn test<'i>(&self, input: &'i [u8]) -> Option<(&'i [u8], &'i [u8])> {
        let mut iter = input.char_indices();
        let (_, end, c) = iter.next()?;

        let c = c as u32;

        (c <= self.end as u32).then_some((&input[..end], &input[end..]))
    }
}

impl Pattern for RangeInclusive<u8> {
    fn test<'i>(&self, input: &'i [u8]) -> Option<(&'i [u8], &'i [u8])> {
        let first = input.get(0)?;
        (first >= self.start() && first <= self.end()).then_some((&input[0..1], &input[1..]))
    }
}

impl Pattern for RangeInclusive<char> {
    fn test<'i>(&self, input: &'i [u8]) -> Option<(&'i [u8], &'i [u8])> {
        let mut iter = input.char_indices();
        let (_, end, c) = iter.next()?;

        let c = c as u32;

        (c >= *self.start() as u32 && c <= *self.end() as u32)
            .then_some((&input[..end], &input[end..]))
    }
}

/// Trait used to specify start and end bounds for pattern repetitions
///
/// Unlike the standard library's [`std::ops::RangeBounds`],
///
/// 1. this trait cannot express an unbounded lower bound
/// 2. this trait's bounds are always inclusive
///
/// # Examples
///
/// ```
/// use bparse::Repetition;
///
/// assert_eq!(3.lower_bound(), 3);
/// assert_eq!(3.upper_bound(), Some(3));
///
/// assert_eq!((2..=4).lower_bound(), 2);
/// assert_eq!((2..=4).upper_bound(), Some(4));
///
/// assert_eq!((..=10).lower_bound(), 0);
/// assert_eq!((..=10).upper_bound(), Some(10));
///
/// assert_eq!((3..).lower_bound(), 3);
/// assert_eq!((3..).upper_bound(), None);
/// ```
pub trait Repetition {
    /// The minimum amount of times a pattern should repeat
    fn lower_bound(&self) -> usize;

    /// The maxiumum amount of times a pattern should repeat, possibly unbounded.
    fn upper_bound(&self) -> Option<usize>;
}

impl Repetition for usize {
    fn lower_bound(&self) -> usize {
        *self
    }
    fn upper_bound(&self) -> Option<usize> {
        Some(*self)
    }
}

impl Repetition for RangeInclusive<usize> {
    fn lower_bound(&self) -> usize {
        *self.start()
    }
    fn upper_bound(&self) -> Option<usize> {
        Some(*self.end())
    }
}

impl Repetition for RangeToInclusive<usize> {
    fn lower_bound(&self) -> usize {
        0
    }
    fn upper_bound(&self) -> Option<usize> {
        Some(self.end)
    }
}

impl Repetition for RangeFrom<usize> {
    fn lower_bound(&self) -> usize {
        self.start
    }
    fn upper_bound(&self) -> Option<usize> {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn do_test(
        pattern: impl Pattern,
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

        // Peeking ahead
        do_test(('a'..='b').peek(), b"a1b2", Some((b"a", b"a1b2")));

        // Optional
        do_test(" ".optional().then("a"), b"a1b2", Some((b"a", b"1b2")));
        do_test(" ".optional().then("a"), b" a1b2", Some((b" a", b"1b2")));

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
    fn test_builtin_patterns() {
        do_test(
            pattern::digit.repeats(0..),
            b"0123456789",
            Some((b"0123456789", b"")),
        );

        do_test(
            pattern::alpha.repeats(0..),
            b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ",
            Some((b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ", b"")),
        );

        do_test(
            pattern::hex.repeats(0..),
            b"abcdefABCDEF0123456789",
            Some((b"abcdefABCDEF0123456789", b"")),
        );
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
