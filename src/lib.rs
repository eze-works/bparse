#![warn(missing_docs)]

//! This crate provides utilites for parsing byte slices. The API borrows some concepts from other
//! parser-combinator crates but heavily simplifies things by eschewing error management and
//! focusing exclusively on parsing byte slices.
//!
//! ## Overview
//!
//! The core of the crate is the [`Pattern`] trait. Patterns can be combined using combinatorial
//! logic to express more complex rules about what a byte (or sequence of bytes) should look like.
//!
//! The other part of the crate is the [`Parser`] struct. It provides a simpler way to parse a
//! slice of bytes by continuously matching patterns against it.
//!
//!
//! ## Examples
//!
//! __HTTP request line__
//!
//! Say you want to parse the request line of an HTTP message. There are three important parts to
//! extract: the method, the request target and the protocol version.
//!
//! ```text
//! GET /hello?value=world HTTP/1.1\r\n
//! ```
//!
//! Here is how you would do it:
//!
//! _Note: The rules for parsing http are a bit more nuanced than this_
//!
//! ```
//! use bparse::{Pattern, Parser};
//!
//! # fn main() {
//! #   do_test().unwrap();
//! # }
//! # fn do_test() -> Option<()> {
//! // This input would probably come from a TcpStream
//! let input = b"GET /hello?value=world HTTP/1.1\r\n";
//!
//! let mut parser = Parser::new(input);
//!
//! // A method is an alphabetic string with at least one character
//! let method_pattern = bparse::range(b'a', b'z')
//!     .or(bparse::range(b'A', b'Z'))
//!     .repeats(1..);
//!
//!
//! // A request url must start with a `/` and contains a mix of alphabetic and special characters
//! let request_target_pattern = "/"
//!     .and(
//!         bparse::range(b'a', b'z')
//!         .or(bparse::range(b'A', b'Z'))
//!         .or(bparse::oneof("?=/"))
//!         .repeats(0..)
//!     );
//!
//! // We want to match the version exactly
//! let version_pattern = "HTTP/1.1";
//!
//! let method = parser.try_match(method_pattern)?;
//! parser.try_match(" ")?;
//! let request_target = parser.try_match(request_target_pattern)?;
//! parser.try_match(" ")?;
//! let version = parser.try_match(version_pattern)?;
//! parser.try_match("\r\n".and(bparse::end))?;
//!
//! assert_eq!(method, b"GET");
//! assert_eq!(request_target, b"/hello?value=world");
//! assert_eq!(version, b"HTTP/1.1");
//!
//! # Some(())
//! # }
//! ```
//!
//! __Hexadecimal color parser:__
//!
//! ```rust
//! use bparse::{Pattern, Parser, range, end};
//! use std::str::from_utf8;
//!
//! #[derive(Debug, PartialEq)]
//! pub struct Color {
//!   pub red: u8,
//!   pub green: u8,
//!   pub blue: u8,
//! }
//!
//! fn main() {
//!   assert_eq!(hex_color("#2F14DF"), Some(Color {
//!     red: 47,
//!     green: 20,
//!     blue: 223,
//!   }));
//! }
//!
//! fn hex_color(input: &str) -> Option<Color> {
//!   let hexbyte = range(b'0', b'9').or(range(b'A', b'F')).or(range(b'a', b'f')).repeats(2);
//!
//!   let mut parser = Parser::new(input.as_bytes());
//!
//!   parser.try_match("#")?;
//!   let red = parser.try_match(hexbyte)?;
//!   let green = parser.try_match(hexbyte)?;
//!   let blue = parser.try_match(hexbyte)?;
//!   parser.try_match(end)?;
//!
//!   Some(Color {
//!     red: u8::from_str_radix(from_utf8(red).unwrap(), 16).unwrap(),
//!     green: u8::from_str_radix(from_utf8(green).unwrap(), 16).unwrap(),
//!     blue: u8::from_str_radix(from_utf8(blue).unwrap(), 16).unwrap()
//!   })
//! }
//! ```

use std::cmp;
use std::ops::{RangeFrom, RangeInclusive, RangeToInclusive};

/// An interval with a lower and (potentially unbounded) upper bound
///
/// Both bounds are inclusive
#[derive(Copy, Clone, Debug)]
pub struct Interval<T>(T, Option<T>);

impl From<usize> for Interval<usize> {
    fn from(value: usize) -> Self {
        Interval(value, Some(value))
    }
}

impl From<RangeInclusive<usize>> for Interval<usize> {
    fn from(value: RangeInclusive<usize>) -> Self {
        Interval(*value.start(), Some(*value.end()))
    }
}

impl From<RangeFrom<usize>> for Interval<usize> {
    fn from(value: RangeFrom<usize>) -> Self {
        Interval(value.start, None)
    }
}

impl From<RangeToInclusive<usize>> for Interval<usize> {
    fn from(value: RangeToInclusive<usize>) -> Self {
        Interval(0, Some(value.end))
    }
}

/// Expresses that the implementing type can be used to match a byte slice
pub trait Pattern {
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
    /// use bparse::Pattern;
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
    /// Returns a new pattern that will test an input slice against `self` and `other` in sequence,
    /// feeding the remainder from the first match as the input to the second.
    ///
    /// # Example
    ///
    /// ```
    /// use bparse::Pattern;
    ///
    /// let input = b"abc";
    /// let pattern = "a".and("b").and("c");
    ///
    /// assert_eq!(b"abc", pattern.test(input).unwrap().0);
    /// ```
    fn and<P>(self, next: P) -> And<Self, P>
    where
        Self: Sized,
    {
        And {
            pattern1: self,
            pattern2: next,
        }
    }

    /// Expresses pattern repetition
    ///
    /// Returns a new pattern that will match an input slice if `self` can match `count` times
    ///
    /// Anything that can be safely converted to an [`Interval`] can be used as an argument .
    ///
    /// ```
    /// use bparse::{Pattern};
    ///
    /// let input = b"ababab";
    /// let pattern = "a".and("b").repeats(1..=2);
    ///
    /// assert_eq!(b"abab", pattern.test(input).unwrap().0);
    /// ```
    fn repeats<I: Into<Interval<usize>>>(self, count: I) -> Repeat<Self>
    where
        Self: Sized,
    {
        Repeat {
            pattern: self,
            count: count.into(),
        }
    }
}

/// See [`Pattern::or`]
#[derive(Clone, Copy, Debug)]
pub struct Or<C1, C2> {
    pattern1: C1,
    pattern2: C2,
}

/// See [`Pattern::and`]
#[derive(Clone, Copy, Debug)]
pub struct And<C1, C2> {
    pattern1: C1,
    pattern2: C2,
}

/// See [`Pattern::repeats`]
#[derive(Clone, Copy, Debug)]
pub struct Repeat<P> {
    pattern: P,
    count: Interval<usize>,
}

/// See [`not`]
#[derive(Clone, Copy, Debug)]
pub struct Not<P> {
    pattern: P,
}

/// See [`optional`]
#[derive(Clone, Copy, Debug)]
pub struct Optional<P> {
    pattern: P,
}

impl<C1: Pattern, C2: Pattern> Pattern for Or<C1, C2> {
    #[inline]
    fn test<'i>(&self, input: &'i [u8]) -> Option<(&'i [u8], &'i [u8])> {
        self.pattern1
            .test(input)
            .or_else(|| self.pattern2.test(input))
    }
}

impl<C1: Pattern, C2: Pattern> Pattern for And<C1, C2> {
    #[inline]
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

impl<P: Pattern> Pattern for Repeat<P> {
    #[inline]
    fn test<'i>(&self, input: &'i [u8]) -> Option<(&'i [u8], &'i [u8])> {
        let mut counter = 0;
        let mut offset = 0;
        let lower_bound = self.count.0;
        if let Some(upper_bound) = self.count.1 {
            assert!(
                upper_bound >= lower_bound,
                "upper bound should be greater than or equal to the lower bound"
            );
        };

        loop {
            // We hit the upper bound of pattern repetition
            if let Some(upper_bound) = self.count.1 {
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

impl<P> Pattern for Not<P>
where
    P: Pattern,
{
    #[inline]
    fn test<'i>(&self, input: &'i [u8]) -> Option<(&'i [u8], &'i [u8])> {
        if self.pattern.test(input).is_some() {
            return None;
        };

        Some((b"", input))
    }
}

impl<P> Pattern for Optional<P>
where
    P: Pattern,
{
    #[inline]
    fn test<'i>(&self, input: &'i [u8]) -> Option<(&'i [u8], &'i [u8])> {
        self.pattern.test(input).or(Some((b"", input)))
    }
}

impl<F> Pattern for F
where
    F: Fn(&[u8]) -> Option<(&[u8], &[u8])>,
{
    #[inline]
    fn test<'i>(&self, input: &'i [u8]) -> Option<(&'i [u8], &'i [u8])> {
        (self)(input)
    }
}

impl Pattern for &str {
    #[inline]
    fn test<'i>(&self, input: &'i [u8]) -> Option<(&'i [u8], &'i [u8])> {
        let bytes = self.as_bytes();

        if bytes.len() > input.len() {
            return None;
        }

        for (i, byte) in bytes.iter().enumerate() {
            if &input[i] != byte {
                return None;
            }
        }

        Some((&input[..self.len()], &input[self.len()..]))
    }
}

/// A pattern that fails if the input is not empty
///
/// # Example
///
/// ```
/// use bparse::{Pattern, end};
///
/// assert_eq!(end.test(b"abc"), None);
/// assert_eq!(end.test(b"").unwrap().0, b"");
/// ```
pub fn end(input: &[u8]) -> Option<(&[u8], &[u8])> {
    if input.is_empty() {
        Some((&[], input))
    } else {
        None
    }
}

/// A pattern that fails if the byte at the start of the input is not an ascii digit
///
/// # Example
///
/// ```
/// use bparse::{Pattern, digit};
/// assert_eq!(digit.test(b"1").unwrap().0, b"1");
/// assert_eq!(digit.test(b"a"), None);
/// ```
pub fn digit(input: &[u8]) -> Option<(&[u8], &[u8])> {
    range(b'0', b'9').test(input)
}

/// A pattern that fails if the byte at the start of the input is not an ascii alphabetic character
///
/// # Example
///
/// ```
/// use bparse::{Pattern, alpha};
/// assert_eq!(alpha.test(b"a").unwrap().0, b"a");
/// assert_eq!(alpha.test(b"1"), None);
/// ```
pub fn alpha(input: &[u8]) -> Option<(&[u8], &[u8])> {
    range(b'a', b'z').or(range(b'A', b'Z')).test(input)
}

/// A pattern that fails if the byte at the start of the input is not a hexadecimal character
///
/// # Example
///
/// ```
/// use bparse::{Pattern, hex};
/// assert_eq!(hex.test(b"a").unwrap().0, b"a");
/// assert_eq!(hex.test(b"1").unwrap().0, b"1");
/// assert_eq!(hex.test(b"g"), None);
/// ```
pub fn hex(input: &[u8]) -> Option<(&[u8], &[u8])> {
    range(b'a', b'f')
        .or(range(b'A', b'F'))
        .or(digit)
        .test(input)
}

/// Returns a pattern that will match any one of the bytes in `alternatives`
///
/// This is a useful alternative to a long `Pattern::or()` chain when you have many single-byte
/// alternatives.
///
/// # Example
///
/// ```
/// use bparse::{Pattern, oneof};
///
/// let punctuation = oneof(".,\"'-?:!;");
/// assert_eq!(punctuation.test(b"!").unwrap().0, b"!");
/// assert_eq!(punctuation.test(b",").unwrap().0, b",");
/// assert_eq!(punctuation.test(b"a"), None);
/// ```
///
/// This function is callable in const contexts. Additionally, the compile-time generated lookup
/// table can be accessed from the [`OneOf`] struct
///
/// ```
/// use bparse::oneof;
/// const lookup: [bool; 256] = oneof("abc").0;
/// assert!(lookup[b'a' as usize] == true);
/// assert!(lookup[b'b' as usize] == true);
/// assert!(lookup[b'c' as usize] == true);
/// assert!(lookup[b'd' as usize] == false);
/// ```
///
pub const fn oneof(alternatives: &str) -> OneOf {
    let bytes = alternatives.as_bytes();
    let mut set: [bool; 256] = [false; 256];

    let mut i = 0;
    while i < bytes.len() {
        set[bytes[i] as usize] = true;
        i += 1;
    }

    OneOf(set)
}

/// Inverse of [`oneof`]
///
/// # Example
///
/// ```
/// use bparse::{Pattern, noneof};
///
/// let nondigits = noneof("0123456789");
///
/// assert_eq!(nondigits.test(b"A").unwrap().0, b"A");
/// assert_eq!(nondigits.test(b"3"), None);
/// ```
///
/// This function is callable in const contexts. Additionally, the compile-time generated lookup
/// table can be accessed from the [`NoneOf`] struct
///
/// ```
/// use bparse::noneof;
/// const lookup: [bool; 256] = noneof("abc").0;
///
/// assert!(lookup[b'a' as usize] == false);
/// assert!(lookup[b'b' as usize] == false);
/// assert!(lookup[b'c' as usize] == false);
/// assert!(lookup[b'd' as usize] == true);
/// ```
pub const fn noneof(exclusions: &str) -> NoneOf {
    let bytes = exclusions.as_bytes();
    let mut set: [bool; 256] = [true; 256];

    let mut i = 0;
    while i < bytes.len() {
        set[bytes[i] as usize] = false;
        i += 1;
    }

    NoneOf(set)
}

/// Expresses pattern negation
///
/// Returns a new pattern that will match only if `pattern` does not match
///
///
/// # Example
///
/// Say you want to match a string of multiple 'a's and 'b's, except the string must not end in
/// a 'b':
/// ```
/// use bparse::{Pattern, not, end};
///
/// let input1 = b"aabaaaa";
/// let input2 = b"aaaab";
///
/// // a pattern of either a's or b's that do not occur at the input
/// let pattern = "a".or("b".and(not(end))).repeats(0..);
///
/// assert_eq!(b"aabaaaa", pattern.test(input1).unwrap().0);
/// assert_eq!(b"aaaa", pattern.test(input2).unwrap().0);
/// ```
///
/// Note: This will always return `Some((&[], _))` (i.e. an empty slice) in the successful case..
///
/// # Example
///
/// ```
/// use bparse::{Pattern, not};
///
/// let input = b"b";
/// let pattern = not("a");
///
/// assert!(matches!(pattern.test(input), Some((&[], _))));
/// ```
pub fn not<P: Pattern>(pattern: P) -> Not<P> {
    Not { pattern }
}

/// Expresses an optional pattern
///
/// Returns a new pattern that will always match the input regardless of the outcome of
/// matching `self`
///
/// # Example
///
/// ```
/// use bparse::{Pattern, optional};
///
/// let input1 = b"aab";
/// let input2 = b"aa";
///
/// let pattern = "aa".and(optional("b"));
///
/// assert_eq!(b"aab", pattern.test(input1).unwrap().0);
/// assert_eq!(b"aa", pattern.test(input2).unwrap().0);
/// ```
pub fn optional<P: Pattern>(pattern: P) -> Optional<P> {
    Optional { pattern }
}

/// See [`oneof()`]
#[derive(Debug, Clone, Copy)]
pub struct OneOf(pub [bool; 256]);

impl Pattern for OneOf {
    #[inline]
    fn test<'i>(&self, input: &'i [u8]) -> Option<(&'i [u8], &'i [u8])> {
        let first = *input.first()?;
        self.0[first as usize].then_some((&input[0..1], &input[1..]))
    }
}

/// See [`noneof()`]
pub struct NoneOf(pub [bool; 256]);

impl Pattern for NoneOf {
    #[inline]
    fn test<'i>(&self, input: &'i [u8]) -> Option<(&'i [u8], &'i [u8])> {
        let first = *input.first()?;
        self.0[first as usize].then_some((&input[0..1], &input[1..]))
    }
}

/// Returns a pattern that will match any byte in the closed interval `[lo, hi]`
///
/// # Example
///
/// ```
/// use bparse::{Pattern, range};
///
/// let digit = range(b'0', b'9');
///
/// assert_eq!(digit.test(b"1").unwrap().0, b"1");
/// assert_eq!(digit.test(b"a"), None);
/// ```
pub fn range(lo: u8, hi: u8) -> ByteRange {
    ByteRange(lo, hi)
}

/// See [`range()`]
#[derive(Debug, Clone, Copy)]
pub struct ByteRange(u8, u8);

impl Pattern for ByteRange {
    #[inline]
    fn test<'i>(&self, input: &'i [u8]) -> Option<(&'i [u8], &'i [u8])> {
        let first = *input.first()?;

        if first < self.0 {
            return None;
        }

        if first > self.1 {
            return None;
        }

        Some((&input[0..1], &input[1..]))
    }
}

/// A byte parser that recognizes [`Pattern`]s
pub struct Parser<'input> {
    input: &'input [u8],
    /// The parser's current position within the input
    pub pos: usize,
}

impl<'i> Parser<'i> {
    /// Returns a new instance of [`Parser`] that will operate on `input`
    pub fn new(input: &'i [u8]) -> Self {
        Parser { input, pos: 0 }
    }

    /// Advances the parser by `step`. Does nothing if the parser is at the end of the input
    #[inline]
    pub fn advance(&mut self, step: usize) {
        // This guarantees that `cursor` never goes past the end of the input, which makes it such
        // that calling `.remaining()` always gives you something (even if it is an empty slice)
        let step = cmp::min(self.input.len() - self.pos, step);
        self.pos += step;
    }

    /// Returns `true` if the parser reached the end of its input. Returns `false` otherwise
    #[inline]
    pub fn eof(&self) -> bool {
        self.input.len() == self.pos
    }

    /// Returns the part of the input that is yet to be consumed
    #[inline]
    pub fn remaining(&self) -> &'i [u8] {
        &self.input[self.pos..]
    }

    /// Tests `pattern` against the remaining input. If the pattern matches, the matching portion
    /// is returned and the parser is advanced by the length of the matched slice.
    ///
    /// Returns `None` if the pattern does not match.
    #[inline]
    pub fn try_match(&mut self, pattern: impl Pattern) -> Option<&'i [u8]> {
        let (matched, _) = pattern.test(self.remaining())?;
        self.advance(matched.len());
        Some(matched)
    }

    /// Tests `pattern` against the remaining input but does not advance the parser. The matching
    /// portion is returned.
    ///
    /// You can use [`Parser::assert`] later to advance the parser with the same pattern.
    #[inline]
    pub fn peek_match(&self, pattern: impl Pattern) -> Option<&'i [u8]> {
        let (matched, _) = pattern.test(self.remaining())?;
        Some(matched)
    }

    /// Similar to [`Parser::try_match`], but panics if the pattern does not match.
    ///
    /// This could be useful when you have previously peeked at the input (perhaps by using
    /// [`Pattern::test`] or [`Parser::peek_match`]) and later want to advance the parser
    #[inline]
    pub fn assert(&mut self, pattern: impl Pattern) -> &'i [u8] {
        let (matched, _) = pattern
            .test(self.remaining())
            .expect("pattern assertion should not fail");
        self.advance(matched.len());
        matched
    }
}
#[cfg(test)]
mod tests {
    use super::*;

    #[track_caller]
    fn do_test(
        pattern: impl Pattern,
        input: &'static [u8],
        result: Option<(&'static [u8], &'static [u8])>,
    ) {
        let out = pattern.test(input);
        assert_eq!(out, result);
    }

    #[test]
    fn test_parse_patterns() {
        // Parsing using string slices
        do_test("", b"a1b2", Some((b"", b"a1b2")));
        do_test("a", b"a1b2", Some((b"a", b"1b2")));
        do_test("١", b"\xd9\xa1", Some((b"\xd9\xa1", &[])));

        // Parsing using alternatives
        do_test("b".or("a"), b"a1b2", Some((b"a", b"1b2")));

        // Parsing in sequence
        do_test("9".and("7").and("8"), b"978", Some((b"978", b"")));

        // Negating a pattern
        do_test(not(range(b'0', b'9')), b"a1b2", Some((b"", b"a1b2")));

        // Optional
        do_test(optional(" ").and("a"), b"a1b2", Some((b"a", b"1b2")));
        do_test(optional(" ").and("a"), b" a1b2", Some((b" a", b"1b2")));

        // Parsing using functions
        fn parse_a(input: &[u8]) -> Option<(&[u8], &[u8])> {
            "a".test(input)
        }

        fn parse_1(input: &[u8]) -> Option<(&[u8], &[u8])> {
            "1".test(input)
        }
        let huh = parse_a.and(parse_1);

        do_test(huh, b"a1b2", Some((b"a1", b"b2")));
        do_test(huh, b"a1b2", Some((b"a1", b"b2")));
    }

    #[test]
    fn test_builtin_patterns() {
        do_test(
            digit.repeats(0..),
            b"0123456789",
            Some((b"0123456789", b"")),
        );

        do_test(
            alpha.repeats(0..),
            b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ",
            Some((b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ", b"")),
        );

        do_test(
            hex.repeats(0..),
            b"abcdefABCDEF0123456789",
            Some((b"abcdefABCDEF0123456789", b"")),
        );

        do_test(oneof("&@*%#!?").repeats(0..), b"#!q", Some((b"#!", b"q")));
        do_test(noneof("ABC").repeats(0..), b"123C", Some((b"123", b"C")));

        do_test(range(b'`', b'b'), b"a1b2", Some((b"a", b"1b2")));
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

    #[test]
    fn test_parser() {
        let input = b"aa bbcc";
        let mut parser = Parser::new(input);

        let peeked_a = parser.peek_match("a".repeats(2));
        let a = parser.try_match("a".repeats(2));
        let _ = parser.try_match(optional(" "));
        let b = parser.try_match("b".repeats(2));
        let _ = parser.try_match(optional(" "));
        let c = parser.try_match("c".repeats(2));
        let huh = parser.try_match("d");
        parser.assert(end);

        assert!(matches!(peeked_a, Some(b"aa")));
        assert!(matches!(a, Some(b"aa")));
        assert!(matches!(b, Some(b"bb")));
        assert!(matches!(c, Some(b"cc")));
        assert!(matches!(huh, None));
    }
}

#[doc = include_str!("../README.md")]
#[cfg(doctest)]
pub struct ReadmeDocTests {}
