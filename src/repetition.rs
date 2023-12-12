use std::ops::{RangeFrom, RangeInclusive, RangeToInclusive};

/// Trait used to specify start and end bounds for pattern repetitions
///
/// Unlike the standard library's [`std::ops::RangeBounds`],
///
/// 1. this trait cannot express an unbounded lower bound
/// 2. this trait's bounds are always inclusive
///
/// # Examples
///
/// ```
/// use bparse::repetition::Repetition;
///
/// assert_eq!(3.lower_bound(), 3);
/// assert_eq!(3.upper_bound(), Some(3));
///
/// assert_eq!((2..=4).lower_bound(), 2);
/// assert_eq!((2..=4).upper_bound(), Some(4));
///
/// assert_eq!((..=10).lower_bound(), 0);
/// assert_eq!((..=10).upper_bound(), Some(10));
///
/// assert_eq!((3..).lower_bound(), 3);
/// assert_eq!((3..).upper_bound(), None);
/// ```
pub trait Repetition {
    /// The minimum amount of times a pattern should repeat
    fn lower_bound(&self) -> usize;

    /// The maxiumum amount of times a pattern should repeat, possibly unbounded.
    fn upper_bound(&self) -> Option<usize>;
}

impl Repetition for usize {
    fn lower_bound(&self) -> usize {
        *self
    }
    fn upper_bound(&self) -> Option<usize> {
        Some(*self)
    }
}

impl Repetition for RangeInclusive<usize> {
    fn lower_bound(&self) -> usize {
        *self.start()
    }
    fn upper_bound(&self) -> Option<usize> {
        Some(*self.end())
    }
}

impl Repetition for RangeToInclusive<usize> {
    fn lower_bound(&self) -> usize {
        0
    }
    fn upper_bound(&self) -> Option<usize> {
        Some(self.end)
    }
}

impl Repetition for RangeFrom<usize> {
    fn lower_bound(&self) -> usize {
        self.start
    }
    fn upper_bound(&self) -> Option<usize> {
        None
    }
}
