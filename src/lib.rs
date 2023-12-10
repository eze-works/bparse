mod accept_condition;
pub use accept_condition::AcceptCondition;

/// A short-hand constructor for building a `&[u8]`
pub fn b<S: AsRef<[u8]> + ?Sized>(s: &S) -> &[u8] {
    s.as_ref()
}

/// A parser for byte slices
pub struct BParse<'input> {
    input: &'input [u8],
    pos: usize,
}

impl<'i> BParse<'i> {
    /// Returns a new instance of [`BParse`]
    pub fn new(bytes: &'i [u8]) -> Self {
        Self {
            input: bytes,
            pos: 0,
        }
    }

    /// Advances the parser if the input matches `condition` at the current position
    ///
    /// `condition` can be a [`&str`](crate::AcceptCondition#string-slice-implementation),
    /// [`u8`](crate::AcceptCondition#byte-implementation),
    /// [`&[u8]`](crate::AcceptCondition#slice-implementation), or a range.
    ///
    /// For ranges, use `u8` bounds to recognize individual bytes. Use `u32` bounds to
    /// recognize utf8 scalar values.
    ///
    /// [`AcceptCondition`] is implemented for [`std::ops::RangeFrom`] (e.g. `8..`),
    /// [`std::ops::RangeInclusive`] (e.g. `..=89`) and [`std::ops::RangeToInclusive`] (e.g.
    /// `32..=34`)
    ///
    /// # Examples
    ///
    /// ```
    /// use bparse::{BParse, b};
    ///
    /// let raw = "hello_world1👻٩".as_ref();
    /// let mut parser = BParse::new(raw);
    /// assert_eq!(Some(b("hello")), parser.accept("hello"));
    /// assert_eq!(Some(b("_")), parser.accept(b'_'));
    /// assert_eq!(Some(b("world")), parser.accept(&b"world"[..]));
    /// assert_eq!(Some(b("1")), parser.accept(0x30..=0x39u8));
    /// assert_eq!(Some(b("👻")), parser.accept("👻"));
    /// assert_eq!(
    ///     Some(b("٩")),
    ///     parser.accept('\u{669}' as u32..='\u{700}' as u32)
    /// );
    /// ```
    /// parser.accept(Condition::
    pub fn accept(&mut self, condition: impl AcceptCondition) -> Option<&[u8]> {
        let offset = condition.matches(&self.input[self.pos..])?;
        let old_pos = self.pos;
        self.pos += offset;
        return Some(&self.input[old_pos..self.pos]);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
        assert_eq!(Some(b("a")), BParse::new(b("a")).accept(0x61u8..));
        assert_eq!(None, BParse::new(b("a")).accept(0x62u8..));
        assert_eq!(Some(b("a")), BParse::new(b("a")).accept(..=0x61u8));
        assert_eq!(None, BParse::new(b("a")).accept(..=0x60u8));
        assert_eq!(Some(b("a")), BParse::new(b("a")).accept(0x61..=0x62u8));
        assert_eq!(None, BParse::new(b("a")).accept(0x62..=0x63u8));
        assert_eq!(Some(b("٩")), BParse::new(b("٩")).accept("\u{669}"));
        assert_eq!(Some(b("٩")), BParse::new(b("٩")).accept('\u{669}' as u32..));
        assert_eq!(None, BParse::new(b("٩")).accept('\u{700}' as u32..));
        assert_eq!(
            Some(b("٩")),
            BParse::new(b("٩")).accept(..='\u{669}' as u32)
        );
        assert_eq!(None, BParse::new(b("٩")).accept(..='\u{668}' as u32));
        assert_eq!(
            Some(b("٩")),
            BParse::new(b("٩")).accept('\u{668}' as u32..='\u{669}' as u32)
        );
        assert_eq!(
            None,
            BParse::new(b("٩")).accept('\u{667}' as u32..='\u{668}' as u32)
        );

        // Edge cases

        // Trying to accept more input than is available
        assert_eq!(None, BParse::new(b("a")).accept("ab"));
        assert_eq!(None, BParse::new(b("a")).accept(b("ab")));
    }
}
