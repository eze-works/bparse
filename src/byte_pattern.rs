//! Condition traits
//!

use crate::pattern_repetition::PatternRepetition;
use bstr::ByteSlice;
use std::ops::{RangeFrom, RangeInclusive, RangeToInclusive};

/// Expresses that the implementing type can be used as a condition for matching a byte slice
pub trait BytePattern {
    /// Returns the slice of the input that is recognized, if any
    fn try_match<'i>(&self, input: &'i [u8]) -> Option<&'i [u8]>;

    /// Chain patterns with `.or()` to express alternatives
    ///
    /// Each pattern is evaluated in sequence on the same input until one succeeds. If no pattern
    /// matches, the entire alternative chain fails.
    ///
    /// # Example
    /// ```
    /// use bparse::prelude::*;
    ///
    /// assert_eq!(Some(&b"9"[..]), "0".or("7").or("9").try_match(b"978"));
    /// ```
    fn or<A>(self, next: A) -> Or<Self, A>
    where
        Self: Sized,
    {
        Or {
            pattern1: self,
            pattern2: next,
        }
    }

    /// Chain patterns with `.then()` to express an ordered sequence
    ///
    /// Each pattern is evaluated in sequence with remainder from the previous pattern until they
    /// all succeed. If any pattern fails to match, the entire chain fails.
    ///
    /// # Example
    ///
    /// ```
    /// use bparse::prelude::*;
    ///
    /// assert_eq!(Some(&b"978"[..]), "9".then("7").then("8").try_match(b"978"));
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

    /// Chain patterns with `.repeats()` to express ... uhh... repetition
    ///
    /// # Example
    ///
    /// ```
    /// use bparse::prelude::*;
    ///
    /// assert_eq!(Some(&[9,9,9][..]), 9.repeats(3).try_match(&[9, 9, 9]));
    /// ```
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

impl<C1: BytePattern, C2: BytePattern> BytePattern for Or<C1, C2> {
    fn try_match<'i>(&self, input: &'i [u8]) -> Option<&'i [u8]> {
        self.pattern1
            .try_match(input)
            .or_else(|| self.pattern2.try_match(input))
    }
}

impl<C1: BytePattern, C2: BytePattern> BytePattern for Then<C1, C2> {
    fn try_match<'i>(&self, input: &'i [u8]) -> Option<&'i [u8]> {
        let mut offset = 0;
        let Some(out) = self.pattern1.try_match(input) else {
            return None;
        };

        offset += out.len();

        let Some(out) = self.pattern2.try_match(&input[out.len()..]) else {
            return None;
        };

        offset += out.len();

        Some(&input[..offset])
    }
}

impl<P: BytePattern, R: PatternRepetition> BytePattern for Repeat<P, R> {
    fn try_match<'i>(&self, input: &'i [u8]) -> Option<&'i [u8]> {
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
                    return Some(&input[..offset]);
                }
            };

            let Some(v) = self.pattern.try_match(&input[offset..]) else {
                if counter < lower_bound {
                    return None;
                }
                return Some(&input[..offset]);
            };

            counter += 1;
            offset += v.len();
        }
    }
}

impl<T: BytePattern> BytePattern for &T {
    fn try_match<'i>(&self, input: &'i [u8]) -> Option<&'i [u8]> {
        (*self).try_match(input)
    }
}

impl BytePattern for &str {
    fn try_match<'i>(&self, input: &'i [u8]) -> Option<&'i [u8]> {
        let bytes = self.as_bytes();
        let Some(_) = input.strip_prefix(bytes) else {
            return None;
        };

        Some(&input[..self.len()])
    }
}

impl BytePattern for u8 {
    fn try_match<'i>(&self, input: &'i [u8]) -> Option<&'i [u8]> {
        input.starts_with(&[*self]).then_some(&input[0..1])
    }
}

impl BytePattern for RangeFrom<u8> {
    fn try_match<'i>(&self, input: &'i [u8]) -> Option<&'i [u8]> {
        let first = *input.get(0)?;
        (first >= self.start).then_some(&input[0..1])
    }
}

impl BytePattern for RangeFrom<char> {
    fn try_match<'i>(&self, input: &'i [u8]) -> Option<&'i [u8]> {
        let mut iter = input.char_indices();
        let (_, end, c) = iter.next()?;

        let c = c as u32;

        (c >= self.start as u32).then_some(&input[..end])
    }
}

impl BytePattern for RangeToInclusive<u8> {
    fn try_match<'i>(&self, input: &'i [u8]) -> Option<&'i [u8]> {
        let first = *input.get(0)?;
        (first <= self.end).then_some(&input[0..1])
    }
}

impl BytePattern for RangeToInclusive<char> {
    fn try_match<'i>(&self, input: &'i [u8]) -> Option<&'i [u8]> {
        let mut iter = input.char_indices();
        let (_, end, c) = iter.next()?;

        let c = c as u32;

        (c <= self.end as u32).then_some(&input[..end])
    }
}

impl BytePattern for RangeInclusive<u8> {
    fn try_match<'i>(&self, input: &'i [u8]) -> Option<&'i [u8]> {
        let first = input.get(0)?;
        (first >= self.start() && first <= self.end()).then_some(&input[0..1])
    }
}

impl BytePattern for RangeInclusive<char> {
    fn try_match<'i>(&self, input: &'i [u8]) -> Option<&'i [u8]> {
        let mut iter = input.char_indices();
        let (_, end, c) = iter.next()?;

        let c = c as u32;

        (c >= *self.start() as u32 && c <= *self.end() as u32).then_some(&input[..end])
    }
}
