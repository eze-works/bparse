use std::ops::{RangeFrom, RangeInclusive, RangeToInclusive};

/// Trait used to specify start and end bounds
pub trait PatternRepetition {
    fn lower_bound(&self) -> usize;
    fn upper_bound(&self) -> Option<usize>;
}

impl PatternRepetition for usize {
    fn lower_bound(&self) -> usize {
        *self
    }
    fn upper_bound(&self) -> Option<usize> {
        Some(*self)
    }
}

impl PatternRepetition for RangeInclusive<usize> {
    fn lower_bound(&self) -> usize {
        *self.start()
    }
    fn upper_bound(&self) -> Option<usize> {
        Some(*self.end())
    }
}

impl PatternRepetition for RangeToInclusive<usize> {
    fn lower_bound(&self) -> usize {
        0
    }
    fn upper_bound(&self) -> Option<usize> {
        Some(self.end)
    }
}

impl PatternRepetition for RangeFrom<usize> {
    fn lower_bound(&self) -> usize {
        self.start
    }
    fn upper_bound(&self) -> Option<usize> {
        None
    }
}
