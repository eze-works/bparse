//! Implementations of the [`Pattern`] trait for recognizing common patterns

use crate::{Match, Pattern};

/// Returns `None` if the input is not empty
///
/// # Example
///
/// ```
/// use bparse::{Pattern, end};
///
/// assert_eq!(end.test(b"abc"), None);
/// assert_eq!(end.test(b"").unwrap().value(), b"");
/// ```
pub fn end(input: &[u8]) -> Option<Match<1>> {
    if input.is_empty() {
        Some(Match([&[]], input))
    } else {
        None
    }
}

/// Returns `None` if the byte at the start of the input is not an ascii digit
///
/// # Example
///
/// ```
/// use bparse::{Pattern, digit};
/// assert_eq!(digit.test(b"1").unwrap().value(), b"1");
/// assert_eq!(digit.test(b"a"), None);
/// ```
pub fn digit(input: &[u8]) -> Option<Match<1>> {
    (0x30..=0x39).test(input)
}

/// Returns `None` if the byte at the start of the input is not an ascii alphabetic character
///
/// # Example
///
/// ```
/// use bparse::{Pattern, alpha};
/// assert_eq!(alpha.test(b"a").unwrap().value(), b"a");
/// assert_eq!(alpha.test(b"1"), None);
/// ```
pub fn alpha(input: &[u8]) -> Option<Match<1>> {
    ('a'..='z').or('A'..='Z').test(input)
}

/// Returns `None` if the byte at the start of the input is not a hexadecimal character
///
/// # Example
///
/// ```
/// use bparse::{Pattern, hex};
/// assert_eq!(hex.test(b"a").unwrap().value(), b"a");
/// assert_eq!(hex.test(b"1").unwrap().value(), b"1");
/// assert_eq!(hex.test(b"g"), None);
/// ```
pub fn hex(input: &[u8]) -> Option<Match<1>> {
    ('a'..='f').or('A'..='F').or(digit).test(input)
}

/// Returns a pattern that will match any one of the bytes in `alternatives`
///
/// This is a useful alternative to a long `Pattern::or()` chain when you have many
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
pub fn byteset(alternatives: &str) -> impl Fn(&[u8]) -> Option<Match<1>> {
    let mut set: [bool; 256] = [false; 256];

    for &byte in alternatives.as_bytes() {
        set[byte as usize] = true;
    }

    move |input: &[u8]| {
        let first = *input.get(0)?;
        (set[first as usize] == true).then_some(Match([&input[0..1]], &input[1..]))
    }
}
