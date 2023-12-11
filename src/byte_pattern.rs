//! Condition traits
//!

use bstr::ByteSlice;
use std::ops::{RangeFrom, RangeInclusive, RangeToInclusive};

/// Expresses that the implementing type can be used as a condition for advancing
/// [`BParse`](crate::BParse)
pub trait BytePattern {
    /// Returns the slice of the input that is recognized, if any
    fn matches<'i>(&self, input: &'i [u8]) -> Option<&'i [u8]>;

    /// Patterns can be chained with `or` to express alternatives
    ///
    /// Each pattern is evaluated in sequence on the same input until one succeeds. If no pattern
    /// matches, the entire alternative chain fails, and the parser does not advance
    ///
    /// # Example
    /// ```
    /// use bparse::prelude::*;
    ///
    /// let input = b("978");
    /// let parser = BParse::new(input);
    ///
    /// assert_eq!(Some(b("9")), parser.accept("0".or("7").or("9")));
    /// assert_eq!(Some(b("7")), parser.accept("0".or("7").or("9")));
    /// assert_eq!(None, parser.accept("0".or("7").or("9")));
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
    /// all succeed. If any pattern fails to match, the entire chain fails and the parser does not
    /// advance
    ///
    /// # Example
    ///
    /// ```
    /// use bparse::prelude::*;
    ///
    /// let input = b("978");
    /// let parser = BParse::new(input);
    ///
    /// assert_eq!(Some(b("978")), parser.accept("9".then("7").then("8")));
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
pub struct Or<C1, C2> {
    condition1: C1,
    condition2: C2,
}

/// See [`BytePattern::then`]
pub struct Then<C1, C2> {
    condition1: C1,
    condition2: C2,
}

impl<C1: BytePattern, C2: BytePattern> BytePattern for Or<C1, C2> {
    fn matches<'i>(&self, input: &'i [u8]) -> Option<&'i [u8]> {
        self.condition1
            .matches(input)
            .or_else(|| self.condition2.matches(input))
    }
}

impl<C1: BytePattern, C2: BytePattern> BytePattern for Then<C1, C2> {
    fn matches<'i>(&self, input: &'i [u8]) -> Option<&'i [u8]> {
        let mut offset = 0;
        let Some(out) = self.condition1.matches(input) else {
            return None;
        };

        offset += out.len();

        let Some(out) = self.condition2.matches(&input[out.len()..]) else {
            return None;
        };

        offset += out.len();

        Some(&input[..offset])
    }
}

impl BytePattern for &str {
    fn matches<'i>(&self, input: &'i [u8]) -> Option<&'i [u8]> {
        let bytes = self.as_bytes();
        let Some(_) = input.strip_prefix(bytes) else {
            return None;
        };

        Some(&input[..self.len()])
    }
}

impl BytePattern for &[u8] {
    fn matches<'i>(&self, input: &'i [u8]) -> Option<&'i [u8]> {
        let Some(_) = input.strip_prefix(*self) else {
            return None;
        };

        Some(&input[..self.len()])
    }
}

impl BytePattern for u8 {
    fn matches<'i>(&self, input: &'i [u8]) -> Option<&'i [u8]> {
        input.starts_with(&[*self]).then_some(&input[0..1])
    }
}

impl BytePattern for RangeFrom<u8> {
    fn matches<'i>(&self, input: &'i [u8]) -> Option<&'i [u8]> {
        let first = *input.get(0)?;
        (first >= self.start).then_some(&input[0..1])
    }
}

impl BytePattern for RangeFrom<u32> {
    fn matches<'i>(&self, input: &'i [u8]) -> Option<&'i [u8]> {
        let mut iter = input.char_indices();
        let (_, end, c) = iter.next()?;

        let c = c as u32;

        (c >= self.start).then_some(&input[..end])
    }
}

impl BytePattern for RangeToInclusive<u8> {
    fn matches<'i>(&self, input: &'i [u8]) -> Option<&'i [u8]> {
        let first = *input.get(0)?;
        (first <= self.end).then_some(&input[0..1])
    }
}

impl BytePattern for RangeToInclusive<u32> {
    fn matches<'i>(&self, input: &'i [u8]) -> Option<&'i [u8]> {
        let mut iter = input.char_indices();
        let (_, end, c) = iter.next()?;

        let c = c as u32;

        (c <= self.end).then_some(&input[..end])
    }
}

impl BytePattern for RangeInclusive<u8> {
    fn matches<'i>(&self, input: &'i [u8]) -> Option<&'i [u8]> {
        let first = input.get(0)?;
        (first >= self.start() && first <= self.end()).then_some(&input[0..1])
    }
}

impl BytePattern for RangeInclusive<u32> {
    fn matches<'i>(&self, input: &'i [u8]) -> Option<&'i [u8]> {
        let mut iter = input.char_indices();
        let (_, end, c) = iter.next()?;

        let c = c as u32;

        (c >= *self.start() && c <= *self.end()).then_some(&input[..end])
    }
}
