//! Implementations of the [`Pattern`] trait for recognizing common patterns

use crate::{Matches, Pattern};

/// A pattern that fails if the input is not empty
///
/// # Example
///
/// ```
/// use bparse::{Pattern, end};
///
/// assert_eq!(end.test(b"abc"), None);
/// assert_eq!(end.test(b"").unwrap().value(), b"");
/// ```
pub fn end(input: &[u8]) -> Option<Matches<1>> {
    if input.is_empty() {
        Some(Matches([&[]], input))
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
/// assert_eq!(digit.test(b"1").unwrap().value(), b"1");
/// assert_eq!(digit.test(b"a"), None);
/// ```
pub fn digit(input: &[u8]) -> Option<Matches<1>> {
    range(b'0', b'9').test(input)
}

/// A pattern that fails if the byte at the start of the input is not an ascii alphabetic character
///
/// # Example
///
/// ```
/// use bparse::{Pattern, alpha};
/// assert_eq!(alpha.test(b"a").unwrap().value(), b"a");
/// assert_eq!(alpha.test(b"1"), None);
/// ```
pub fn alpha(input: &[u8]) -> Option<Matches<1>> {
    range(b'a', b'z').or(range(b'A', b'Z')).test(input)
}

/// A pattern that fails if the byte at the start of the input is not a hexadecimal character
///
/// # Example
///
/// ```
/// use bparse::{Pattern, hex};
/// assert_eq!(hex.test(b"a").unwrap().value(), b"a");
/// assert_eq!(hex.test(b"1").unwrap().value(), b"1");
/// assert_eq!(hex.test(b"g"), None);
/// ```
pub fn hex(input: &[u8]) -> Option<Matches<1>> {
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
/// use bparse::{Pattern, byteset};
///
/// let punctuation = byteset(".,\"'-?:!;");
/// assert_eq!(punctuation.test(b"!").unwrap().value(), b"!");
/// assert_eq!(punctuation.test(b",").unwrap().value(), b",");
/// assert_eq!(punctuation.test(b"a"), None);
/// ```
pub fn byteset(alternatives: &str) -> ByteSet {
    let mut set: [bool; 256] = [false; 256];

    for &byte in alternatives.as_bytes() {
        set[byte as usize] = true;
    }

    ByteSet(set)
}

/// See [`byteset()`]
#[derive(Debug, Clone, Copy)]
pub struct ByteSet([bool; 256]);

impl Pattern for ByteSet {
    fn test<'i>(&self, input: &'i [u8]) -> Option<Matches<'i, 1>> {
        let first = *input.first()?;
        self.0[first as usize].then_some(Matches([&input[0..1]], &input[1..]))
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
/// assert_eq!(digit.test(b"1").unwrap().value(), b"1");
/// assert_eq!(digit.test(b"a"), None);
/// ```
pub fn range(lo: u8, hi: u8) -> ByteRange {
    ByteRange(lo, hi)
}

/// See [`range()`]
#[derive(Debug, Clone, Copy)]
pub struct ByteRange(u8, u8);

impl Pattern for ByteRange {
    fn test<'i>(&self, input: &'i [u8]) -> Option<Matches<'i, 1>> {
        let first = *input.first()?;

        if first < self.0 {
            return None;
        }

        if first > self.1 {
            return None;
        }

        Some(Matches([&input[0..1]], &input[1..]))
    }
}
