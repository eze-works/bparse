//! Condition traits
//!

use bstr::ByteSlice;
use std::ops::{RangeFrom, RangeInclusive, RangeToInclusive};

/// Expresses that the implementing type can be used as a condition for advancing
/// [`BParse`](crate::BParse)
pub trait Accept {
    /// Returns a value indicating if the [`BParse`](crate::BParse) should advance, and if
    /// so, by how many bytes
    fn matches(&self, input: &[u8]) -> Option<usize>;
}

impl Accept for &str {
    fn matches(&self, input: &[u8]) -> Option<usize> {
        let bytes = self.as_bytes();
        let Some(_) = input.strip_prefix(bytes) else {
            return None;
        };

        Some(self.len())
    }
}

impl Accept for &[u8] {
    fn matches(&self, input: &[u8]) -> Option<usize> {
        let Some(_) = input.strip_prefix(*self) else {
            return None;
        };

        Some(self.len())
    }
}

impl Accept for u8 {
    fn matches(&self, input: &[u8]) -> Option<usize> {
        input.starts_with(&[*self]).then_some(1)
    }
}

impl Accept for RangeFrom<u8> {
    fn matches(&self, input: &[u8]) -> Option<usize> {
        let first = *input.get(0)?;
        (first >= self.start).then_some(1)
    }
}

impl Accept for RangeFrom<u32> {
    fn matches(&self, input: &[u8]) -> Option<usize> {
        let mut iter = input.char_indices();
        let (start, end, c) = iter.next()?;

        let c = c as u32;

        (c >= self.start).then_some(end - start)
    }
}

impl Accept for RangeToInclusive<u8> {
    fn matches(&self, input: &[u8]) -> Option<usize> {
        let first = *input.get(0)?;
        (first <= self.end).then_some(1)
    }
}

impl Accept for RangeToInclusive<u32> {
    fn matches(&self, input: &[u8]) -> Option<usize> {
        let mut iter = input.char_indices();
        let (start, end, c) = iter.next()?;

        let c = c as u32;

        (c <= self.end).then_some(end - start)
    }
}

impl Accept for RangeInclusive<u8> {
    fn matches(&self, input: &[u8]) -> Option<usize> {
        let first = input.get(0)?;
        (first >= self.start() && first <= self.end()).then_some(1)
    }
}

impl Accept for RangeInclusive<u32> {
    fn matches(&self, input: &[u8]) -> Option<usize> {
        let mut iter = input.char_indices();
        let (start, end, c) = iter.next()?;

        let c = c as u32;

        (c >= *self.start() && c <= *self.end()).then_some(end - start)
    }
}

macro_rules! impl_tuple {
    ($($condition_type:ident, $condition:ident),+) => {
        /// A tuple of members implementing `Accept` also implements `Accept` such that the
        /// resulting condition is true if any of the tuple conditions evaluates to `true`. This is
        /// implemented for up to 10 tuple members
        impl <$( $condition_type,)+> Accept for ($( $condition_type, )+)
        where $( $condition_type : Accept,)+
        {
            fn matches(&self, input: &[u8]) -> Option<usize> {
                let ($($condition,)+) = self;
                $(
                    if let Some(offset) = $condition.matches(input) {
                        return Some(offset);
                    }
                )+
                return None;
            }
        }
    }
}

impl_tuple!(C0, c0);
impl_tuple!(C0, c0, C1, c1);
impl_tuple!(C0, c0, C1, c1, C2, c2);
impl_tuple!(C0, c0, C1, c1, C2, c2, C3, c3);
impl_tuple!(C0, c0, C1, c1, C2, c2, C3, c3, C4, c4);
impl_tuple!(C0, c0, C1, c1, C2, c2, C3, c3, C4, c4, C5, c5);
impl_tuple!(C0, c0, C1, c1, C2, c2, C3, c3, C4, c4, C5, c5, C6, c6);
impl_tuple!(C0, c0, C1, c1, C2, c2, C3, c3, C4, c4, C5, c5, C6, c6, C7, c7);
impl_tuple!(C0, c0, C1, c1, C2, c2, C3, c3, C4, c4, C5, c5, C6, c6, C7, c7, C8, c8);
impl_tuple!(C0, c0, C1, c1, C2, c2, C3, c3, C4, c4, C5, c5, C6, c6, C7, c7, C8, c8, C9, c9);
