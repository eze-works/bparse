#![warn(missing_docs)]

//! A library for matching patterns in byte slices

use bstr::ByteSlice;
use std::ops::{RangeFrom, RangeInclusive, RangeToInclusive};

pub mod pattern;

/// Expresses that the implementing type can be used to match a byte slice
pub trait BytePattern {
    /// Tests the pattern against the input slice. If the pattern matches, the matching part is
    /// returned along with what is left of the input. Returns `None` if the pattern does not match
    fn test<'i>(&self, input: &'i [u8]) -> Option<(&'i [u8], &'i [u8])>;

    /// Expresses an alternate pattern.
    ///
    /// Returns a new pattern that will match an input slice if either `self` or `other` match it.
    ///
    /// # Example
    ///
    /// ```
    /// use bparse::BytePattern;
    ///
    /// let input = b"b";
    /// let pattern = "a".or("b");
    ///
    /// assert_eq!(b"b", pattern.test(input).unwrap().0);
    /// ```
    fn or<P>(self, other: P) -> Or<Self, P>
    where
        Self: Sized,
    {
        Or {
            pattern1: self,
            pattern2: other,
        }
    }

    /// Expreses a sequence of patterns
    ///
    /// Returns a new pattern that will match an input slice if `self` matches it, and `other`
    /// matches the rest.
    ///
    /// # Example
    ///
    /// ```
    /// use bparse::BytePattern;
    ///
    /// let input = b"abc";
    /// let pattern = "a".then("b").then("c");
    ///
    /// assert_eq!(b"abc", pattern.test(input).unwrap().0);
    /// ```
    fn then<P>(self, next: P) -> Then<Self, P>
    where
        Self: Sized,
    {
        Then {
            pattern1: self,
            pattern2: next,
        }
    }

    /// Expresses pattern repetition
    ///
    /// Returns a new pattern that will match an input slice if `self` can match `count` times
    ///
    /// See [`Repetition`] for more examples of types that implement it.
    ///
    /// ```
    /// use bparse::BytePattern;
    ///
    /// let input = b"ababab";
    /// let pattern = "a".then("b").repeats(1..=2);
    ///
    /// assert_eq!(b"abab", pattern.test(input).unwrap().0);
    /// ```
    fn repeats<R: Repetition>(self, count: R) -> Repeat<Self, R>
    where
        Self: Sized,
    {
        Repeat {
            pattern: self,
            count,
        }
    }

    /// Expresses pattern negation
    ///
    /// Returns a new pattern that will match only if `self` does not match
    ///
    /// # Example
    ///
    /// Say you want to match a string of multiple 'a's and 'b's, except the string must not end in
    /// a 'b':
    /// ```
    /// use bparse::BytePattern;
    /// use bparse::pattern::end;
    ///
    /// let input1 = b"aabaaaa";
    /// let input2 = b"aaaab";
    ///
    /// // a pattern of either a's or b's that do not occur at the input
    /// let pattern = "a".or("b".then(end.not())).repeats(0..);
    ///
    /// assert_eq!(b"aabaaaa", pattern.test(input1).unwrap().0);
    /// assert_eq!(b"aaaa", pattern.test(input2).unwrap().0);
    ///
    ///
    /// ```
    fn not(self) -> Not<Self>
    where
        Self: Sized,
    {
        Not { pattern: self }
    }

    /// Expresses an optional pattern
    ///
    /// Returns a new pattern that will always match the input regardless of the outcome of
    /// matching `self`
    ///
    /// # Example
    ///
    /// ```
    /// use bparse::BytePattern;
    ///
    /// let input1 = b"aab";
    /// let input2 = b"aa";
    ///
    /// let pattern = "aa".then("b".optional());
    ///
    /// assert_eq!(b"aab", pattern.test(input1).unwrap().0);
    /// assert_eq!(b"aa", pattern.test(input2).unwrap().0);
    /// ```
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

/// See [`BytePattern::not`]
#[derive(Clone, Copy, Debug)]
pub struct Not<P> {
    pattern: P,
}

/// See [`BytePattern::optional`]
#[derive(Clone, Copy, Debug)]
pub struct Optional<P> {
    pattern: P,
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

impl<P: BytePattern, R: Repetition> BytePattern for Repeat<P, R> {
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

impl<P> BytePattern for Not<P>
where
    P: BytePattern,
{
    fn test<'i>(&self, input: &'i [u8]) -> Option<(&'i [u8], &'i [u8])> {
        if self.pattern.test(input).is_some() {
            return None;
        };

        Some((b"", input))
    }
}

impl<P> BytePattern for Optional<P>
where
    P: BytePattern,
{
    fn test<'i>(&self, input: &'i [u8]) -> Option<(&'i [u8], &'i [u8])> {
        self.pattern.test(input).or(Some((b"", input)))
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

        // Negating a pattern
        do_test(('0'..='9').not(), b"a1b2", Some((b"", b"a1b2")));

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

        do_test(
            pattern::byteset("&@*%#!?").repeats(0..),
            b"#!q",
            Some((b"#!", b"q")),
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
