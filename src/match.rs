use crate::Pattern;

/// A container of matched slices. Also stores the remaining input
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Matches<'i, const N: usize>(
    /// A list of all the matched slices.
    pub [&'i [u8]; N],
    /// What is left of the input
    pub &'i [u8],
);

impl<'i> Matches<'i, 0> {
    /// Returns a new `Matches` struct with 0 matches
    ///
    /// This is useful for starting a chain of pattern tests against `input`
    pub fn new(input: &[u8]) -> Matches<0> {
        Matches([], input)
    }
}

impl<'i, const N: usize> Matches<'i, N> {
    /// Tests the pattern `p` against the remaining input in `self` and returns a new
    /// `Match` struct if `p` matches.
    ///
    /// The array of matched slices in the returned struct is identical to that in `self`.
    /// This has the effect of ignoring the value matched by `p`
    pub fn ignore(self, p: impl Pattern) -> Option<Matches<'i, N>> {
        let (_, rest) = p.test(self.1)?;
        Some(Matches(self.0, rest))
    }
}

macro_rules! impl_match {
    ($n:literal => $m:literal) => {
        impl<'i> Matches<'i, $n> {
            /// Tests the pattern `p` against the remaining input in `self` and returns a new
            /// `Match` struct if `p` matches.
            ///
            /// The array of matched slices in the returned struct will have an additional element
            /// corresponding to the value matched by `p`
            ///
            /// This method is implemented for up to 20 elements
            pub fn pattern(self, p: impl Pattern) -> Option<Matches<'i, $m>> {
                let (value, rest) = p.test(self.1)?;
                let mut result: [&[u8]; $m] = [&[]; $m];
                let (existing_matches, new_match) = result.split_at_mut(self.0.len());
                existing_matches.copy_from_slice(&self.0);
                new_match.copy_from_slice(&[value]);

                Some(Matches(result, rest))
            }
        }
    };
}

impl_match!(0 => 1);
impl_match!(1 => 2);
impl_match!(2 => 3);
impl_match!(3 => 4);
impl_match!(4 => 5);
impl_match!(5 => 6);
impl_match!(6 => 7);
impl_match!(7 => 8);
impl_match!(8 => 9);
impl_match!(9 => 10);
impl_match!(10 => 11);
impl_match!(11 => 12);
impl_match!(12 => 13);
impl_match!(13 => 14);
impl_match!(14 => 15);
impl_match!(15 => 16);
impl_match!(16 => 17);
impl_match!(17 => 18);
impl_match!(18 => 19);
impl_match!(19 => 20);

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_matches() {
        let input = b"aa bbcc";
        let Matches([a, b, c], _) = Matches::new(input)
            .pattern("a".repeats(2))
            .unwrap()
            .ignore(" ".optional())
            .unwrap()
            .pattern("b".repeats(2))
            .unwrap()
            .ignore(" ".optional())
            .unwrap()
            .pattern("c".repeats(2))
            .unwrap();

        println!("{:#?}", a);
        println!("{:#?}", b);
        println!("{:#?}", c);
    }
}
