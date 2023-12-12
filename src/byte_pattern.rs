//! Condition traits
//!

use bstr::ByteSlice;
use std::ops::{RangeFrom, RangeInclusive, RangeToInclusive};

/// Expresses that the implementing type can be used as a condition for matching a byte slice
pub trait BytePattern {
    /// Returns the slice of the input that is recognized, if any
    fn try_match<'i>(&self, input: &'i [u8]) -> Option<&'i [u8]>;

    /// Patterns can be chained with `or` to express alternatives
    ///
    /// Each pattern is evaluated in sequence on the same input until one succeeds. If no pattern
    /// matches, the entire alternative chain fails.
    ///
    /// # Example
    /// ```
    /// use bparse::prelude::*;
    ///
    /// assert_eq!(Some(b("9")), "0".or("7").or("9").try_match(b("978")));
    /// ```
    fn or<A>(self, next: A) -> Or<Self, A>
    where
        Self: Sized,
    {
        Or {
            condition1: self,
            condition2: next,
        }
    }

    /// Patterns can be chained with `then` to express an ordered sequence
    ///
    /// Each pattern is evaluated in sequence with remainder from the previous pattern until they
    /// all succeed. If any pattern fails to match, the entire chain fails.
    ///
    /// # Example
    ///
    /// ```
    /// use bparse::prelude::*;
    ///
    /// assert_eq!(Some(b("978")), "9".then("7").then("8").try_match(b("978")));
    /// ```
    fn then<P>(self, next: P) -> Then<Self, P>
    where
        Self: Sized,
    {
        Then {
            condition1: self,
            condition2: next,
        }
    }
}

/// See [`BytePattern::or`]
#[derive(Clone, Copy, Debug)]
pub struct Or<C1, C2> {
    condition1: C1,
    condition2: C2,
}

/// See [`BytePattern::then`]
#[derive(Clone, Copy, Debug)]
pub struct Then<C1, C2> {
    condition1: C1,
    condition2: C2,
}

impl<C1: BytePattern, C2: BytePattern> BytePattern for Or<C1, C2> {
    fn try_match<'i>(&self, input: &'i [u8]) -> Option<&'i [u8]> {
        self.condition1
            .try_match(input)
            .or_else(|| self.condition2.try_match(input))
    }
}

impl<C1: BytePattern, C2: BytePattern> BytePattern for Then<C1, C2> {
    fn try_match<'i>(&self, input: &'i [u8]) -> Option<&'i [u8]> {
        let mut offset = 0;
        let Some(out) = self.condition1.try_match(input) else {
            return None;
        };

        offset += out.len();

        let Some(out) = self.condition2.try_match(&input[out.len()..]) else {
            return None;
        };

        offset += out.len();

        Some(&input[..offset])
    }
}

impl<T: BytePattern> BytePattern for &T {
    fn try_match<'i>(&self, input: &'i [u8]) -> Option<&'i [u8]> {
        (*self).try_match(input)
    }
}

/// [`BytePattern`] implementation for string slices.
///
/// Matches unicode scalar values in the byte input.
///
/// # Example
///
/// ```
/// use bparse::prelude::*;
///
/// assert_eq!(Some(b("🙂")), "🙂".try_match(b("🙂")));
///
/// ```
impl BytePattern for &str {
    fn try_match<'i>(&self, input: &'i [u8]) -> Option<&'i [u8]> {
        let bytes = self.as_bytes();
        let Some(_) = input.strip_prefix(bytes) else {
            return None;
        };

        Some(&input[..self.len()])
    }
}

/// [`BytePattern`] implementation for a byte
///
///
/// # Example
///
/// ```
/// use bparse::prelude::*;
///
/// assert_eq!(Some(b(&[123])), 123.try_match(&[123]));
/// ```
impl BytePattern for u8 {
    fn try_match<'i>(&self, input: &'i [u8]) -> Option<&'i [u8]> {
        input.starts_with(&[*self]).then_some(&input[0..1])
    }
}

/// [`BytePattern`] implementation for ranges of the form `0..`
///
/// # Example
///
/// ```
/// use bparse::prelude::*;
///
/// assert_eq!(Some(b(&[123])), (0..).try_match(&[123]));
/// ```
impl BytePattern for RangeFrom<u8> {
    fn try_match<'i>(&self, input: &'i [u8]) -> Option<&'i [u8]> {
        let first = *input.get(0)?;
        (first >= self.start).then_some(&input[0..1])
    }
}

/// [`BytePattern`] implementattion for ranges of the form `'a'..`
///
/// Matches a range of unicode scalar values in the byte input.
///
/// # Example
///
/// ```
/// use bparse::prelude::*;
///
/// assert_eq!(Some(b("┦")), ('\u{2520}'..).try_match(b"\xE2\x94\xA6"));
/// ```
impl BytePattern for RangeFrom<char> {
    fn try_match<'i>(&self, input: &'i [u8]) -> Option<&'i [u8]> {
        let mut iter = input.char_indices();
        let (_, end, c) = iter.next()?;

        let c = c as u32;

        (c >= self.start as u32).then_some(&input[..end])
    }
}

/// [`BytePattern`] implementation for ranges of the form `..=10`
///
/// # Example
///
/// ```
/// use bparse::prelude::*;
///
/// assert_eq!(Some(b(&[10])), (..=10).try_match(&[10]));
/// ```
impl BytePattern for RangeToInclusive<u8> {
    fn try_match<'i>(&self, input: &'i [u8]) -> Option<&'i [u8]> {
        let first = *input.get(0)?;
        (first <= self.end).then_some(&input[0..1])
    }
}

/// [`BytePattern`] implementation for ranges of the form `..='Z'`
///
/// # Example
///
/// ```
/// use bparse::prelude::*;
///
/// assert_eq!(Some(b("Y")), (..='Z').try_match(b"Y"));
///
/// ```
impl BytePattern for RangeToInclusive<char> {
    fn try_match<'i>(&self, input: &'i [u8]) -> Option<&'i [u8]> {
        let mut iter = input.char_indices();
        let (_, end, c) = iter.next()?;

        let c = c as u32;

        (c <= self.end as u32).then_some(&input[..end])
    }
}

/// [`BytePattern`] implementation for ranges of the form `0..=9`
///
/// # Example
///
/// ```
/// use bparse::prelude::*;
///
/// assert_eq!(Some(b("7")), (0x30..=0x39).try_match(b"7"));
/// ```
impl BytePattern for RangeInclusive<u8> {
    fn try_match<'i>(&self, input: &'i [u8]) -> Option<&'i [u8]> {
        let first = input.get(0)?;
        (first >= self.start() && first <= self.end()).then_some(&input[0..1])
    }
}

/// [`BytePattern`] implementation for ranges of the form `'a'..='z'`
///
/// # Example
/// ```
/// use bparse::prelude::*;
///
/// assert_eq!(Some(b("d")), (0x61..=0x7A).try_match(b"d"));
/// ```
impl BytePattern for RangeInclusive<char> {
    fn try_match<'i>(&self, input: &'i [u8]) -> Option<&'i [u8]> {
        let mut iter = input.char_indices();
        let (_, end, c) = iter.next()?;

        let c = c as u32;

        (c >= *self.start() as u32 && c <= *self.end() as u32).then_some(&input[..end])
    }
}
