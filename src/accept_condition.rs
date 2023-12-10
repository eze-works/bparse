use bstr::ByteSlice;
use std::ops::{RangeFrom, RangeInclusive, RangeToInclusive};

/// Expresses that the implementing type can be used as a condition for advancing
/// [`BParse`](crate::BParse)
pub trait AcceptCondition {
    /// Returns a value indicating if the [`BParse`](crate::BParse) should advance, and if
    /// so, by how many bytes
    fn advance(&self, input: &[u8]) -> Option<usize>;
}

/// # String slice implementation
impl AcceptCondition for &str {
    fn advance(&self, input: &[u8]) -> Option<usize> {
        let bytes = self.as_bytes();
        let Some(_) = input.strip_prefix(bytes) else {
            return None;
        };

        Some(self.len())
    }
}

/// # Slice implementation
impl AcceptCondition for &[u8] {
    fn advance(&self, input: &[u8]) -> Option<usize> {
        let Some(_) = input.strip_prefix(*self) else {
            return None;
        };

        Some(self.len())
    }
}

/// # Byte implementation
impl AcceptCondition for u8 {
    fn advance(&self, input: &[u8]) -> Option<usize> {
        input.starts_with(&[*self]).then_some(1)
    }
}

impl AcceptCondition for RangeFrom<u8> {
    fn advance(&self, input: &[u8]) -> Option<usize> {
        let first = *input.get(0)?;
        (first >= self.start).then_some(1)
    }
}

impl AcceptCondition for RangeFrom<u32> {
    fn advance(&self, input: &[u8]) -> Option<usize> {
        let mut iter = input.char_indices();
        let (start, end, c) = iter.next()?;

        let c = c as u32;

        (c >= self.start).then_some(end - start)
    }
}

impl AcceptCondition for RangeToInclusive<u8> {
    fn advance(&self, input: &[u8]) -> Option<usize> {
        let first = *input.get(0)?;
        (first <= self.end).then_some(1)
    }
}

impl AcceptCondition for RangeToInclusive<u32> {
    fn advance(&self, input: &[u8]) -> Option<usize> {
        let mut iter = input.char_indices();
        let (start, end, c) = iter.next()?;

        let c = c as u32;

        (c <= self.end).then_some(end - start)
    }
}

impl AcceptCondition for RangeInclusive<u8> {
    fn advance(&self, input: &[u8]) -> Option<usize> {
        let first = input.get(0)?;
        (first >= self.start() && first <= self.end()).then_some(1)
    }
}

impl AcceptCondition for RangeInclusive<u32> {
    fn advance(&self, input: &[u8]) -> Option<usize> {
        let mut iter = input.char_indices();
        let (start, end, c) = iter.next()?;

        let c = c as u32;

        (c >= *self.start() && c <= *self.end()).then_some(end - start)
    }
}
