use std::cell::Cell;
pub mod byte_pattern;

use byte_pattern::BytePattern;

/// Rexports of the parts of the crate commonly used together
pub mod prelude {
    pub use crate::byte_pattern::BytePattern;
    pub use crate::{b, BParse};
}

/// A short-hand constructor for building a `&[u8]`
///
/// This `b("hello")` is slightly less verbose than this `&["hello"][..]`
pub fn b<S: AsRef<[u8]> + ?Sized>(s: &S) -> &[u8] {
    s.as_ref()
}

/// A parser for byte slices
pub struct BParse<'input> {
    input: &'input [u8],
    // The API allows returning immutable references to `input`.
    // I want this to be valid:
    //
    // ```
    //  let p = BParse::new(b("hello world"));
    //  let hello = p.accept("hello");
    //  let sp = p.accept(" ");
    //  println!("{:#?}", hello);
    // ```
    //
    // To do this properly, the calls that modify the position can't take a mutable reference to
    // `self` since that would mean the lifetime of the returned value would be mutable.
    pos: Cell<usize>,
}

impl<'i> BParse<'i> {
    /// Returns a new instance of [`BParse`]
    pub fn new(bytes: &'i [u8]) -> Self {
        Self {
            input: bytes,
            pos: Cell::new(0),
        }
    }

    /// Advances the parser if the input matches `pattern` at the current position
    ///
    /// If the pattern matches at the parser's current position, this method returns a slice of the
    /// parser's input.
    ///
    /// Look to the [`BytePattern`] `impl`s for what can be used as `pattern`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bparse::prelude::*;
    ///
    /// let raw = "hello_world1👻٩".as_ref();
    /// let parser = BParse::new(raw);
    /// assert_eq!(Some(b("hello")), parser.accept("hello"));
    /// assert_eq!(Some(b("_")), parser.accept(b'_'));
    /// assert_eq!(Some(b("world")), parser.accept(&b"world"[..]));
    /// assert_eq!(Some(b("1")), parser.accept(0x30..=0x39u8));
    /// assert_eq!(Some(b("👻")), parser.accept("👻"));
    /// assert_eq!(
    ///     Some(b("٩")),
    ///     parser.accept('\u{669}'..='\u{700}')
    /// );
    /// ```
    pub fn accept(&self, pattern: impl BytePattern) -> Option<&[u8]> {
        let current_pos = self.pos.get();
        let s = pattern.matches(&self.input[current_pos..])?;
        let new_pos = current_pos + s.len();
        self.pos.replace(new_pos);
        return Some(&self.input[current_pos..new_pos]);
    }
}

#[cfg(test)]
mod tests {
    use super::prelude::*;

    #[test]
    fn test_accept() {
        // Can accept nothing
        assert_eq!(Some(b("")), BParse::new(b("")).accept(b(""))); // using byte slice
        assert_eq!(Some(b("")), BParse::new(b("a")).accept(b("")));
        assert_eq!(Some(b("")), BParse::new(b("")).accept("")); // using &str
        assert_eq!(Some(b("")), BParse::new(b("a")).accept(""));

        // Regular usage
        assert_eq!(Some(b("a")), BParse::new(b("a")).accept("a"));
        assert_eq!(Some(b("a")), BParse::new(b("a")).accept(b("a")));
        assert_eq!(Some(b("a")), BParse::new(b("a")).accept(0x61));
        assert_eq!(Some(b("a")), BParse::new(b("a")).accept(0x61..));
        assert_eq!(None, BParse::new(b("a")).accept(0x62..));
        assert_eq!(Some(b("a")), BParse::new(b("a")).accept(..=0x61));
        assert_eq!(None, BParse::new(b("a")).accept(..=0x60));
        assert_eq!(Some(b("a")), BParse::new(b("a")).accept(0x61..=0x62));
        assert_eq!(None, BParse::new(b("a")).accept(0x62..=0x63));
        assert_eq!(Some(b("٩")), BParse::new(b("٩")).accept("\u{669}"));
        assert_eq!(Some(b("٩")), BParse::new(b("٩")).accept('\u{669}'..));
        assert_eq!(None, BParse::new(b("٩")).accept('\u{700}'..));
        assert_eq!(Some(b("٩")), BParse::new(b("٩")).accept(..='\u{669}'));
        assert_eq!(None, BParse::new(b("٩")).accept(..='\u{668}'));
        assert_eq!(
            Some(b("٩")),
            BParse::new(b("٩")).accept('\u{668}'..='\u{669}')
        );
        assert_eq!(None, BParse::new(b("٩")).accept('\u{667}'..='\u{668}'));
        assert_eq!(
            Some(b("7")),
            BParse::new(b("7")).accept("0".or("1").or("7"))
        );

        // Edge cases

        // Trying to accept more input than is available
        assert_eq!(None, BParse::new(b("a")).accept("ab"));
        assert_eq!(None, BParse::new(b("a")).accept(b("ab")));
    }

    #[test]
    fn huh() {}
}

#[doc = include_str!("../README.md")]
#[cfg(doctest)]
pub struct ReadmeDocTests {}
