//! Implementations of the [`BytePattern`] trait for recognizing common patterns

use crate::BytePattern;

/// Returns `None` if the input is not empty
///
/// # Example
///
/// ```
/// use bparse::{BytePattern, pattern};
///
/// assert_eq!(pattern::end.test(b"abc"), None);
/// assert_eq!(pattern::end.test(b""), Some((&[][..], &[][..])));
/// ```
pub fn end(input: &[u8]) -> Option<(&[u8], &[u8])> {
    if input.is_empty() {
        Some((&[], input))
    } else {
        None
    }
}

/// Returns `None` if the byte at the start of the input is not an ascii digit
///
/// # Example
///
/// ```
/// use bparse::{BytePattern, pattern};
/// assert_eq!(pattern::digit.test(b"1"), Some((&b"1"[..], &[][..])));
/// assert_eq!(pattern::digit.test(b"a"), None);
/// ```
pub fn digit(input: &[u8]) -> Option<(&[u8], &[u8])> {
    (0x30..=0x39).test(input)
}

/// Returns `None` if the byte at the start of the input is not an ascii alphabetic character
///
/// # Example
///
/// ```
/// use bparse::{BytePattern, pattern};
/// assert_eq!(pattern::alpha.test(b"a"), Some((&b"a"[..], &[][..])));
/// assert_eq!(pattern::alpha.test(b"1"), None);
/// ```
pub fn alpha(input: &[u8]) -> Option<(&[u8], &[u8])> {
    ('a'..='z').or('A'..='Z').test(input)
}

/// Returns `None` if the byte at the start of the input is not a hexadecimal character
///
/// # Example
///
/// ```
/// use bparse::{BytePattern, pattern};
/// assert_eq!(pattern::hex.test(b"a"), Some((&b"a"[..], &[][..])));
/// assert_eq!(pattern::hex.test(b"1"), Some((&b"1"[..], &[][..])));
/// assert_eq!(pattern::hex.test(b"g"), None);
/// ```
pub fn hex(input: &[u8]) -> Option<(&[u8], &[u8])> {
    ('a'..='f').or('A'..='F').or(digit).test(input)
}

/// Returns a pattern that will match any one of the bytes in `alternatives`
///
/// This is a useful alternative to a long `BytePattern::or()` chain when you have many
/// alternatives.
///
/// # Example
///
/// ```
/// use bparse::{BytePattern, pattern};
///
/// let punctuation = pattern::byteset(".,\"'-?:!;");
/// assert_eq!(punctuation.test(b"!"), Some((&b"!"[..], &[][..])));
/// assert_eq!(punctuation.test(b","), Some((&b","[..], &[][..])));
/// assert_eq!(punctuation.test(b"a"), None);
/// ```
pub fn byteset(alternatives: &str) -> impl Fn(&[u8]) -> Option<(&[u8], &[u8])> {
    let mut set: [bool; 256] = [false; 256];

    for &byte in alternatives.as_bytes() {
        set[byte as usize] = true;
    }

    move |input: &[u8]| {
        let first = *input.get(0)?;
        (set[first as usize] == true).then_some((&input[0..1], &input[1..]))
    }
}
