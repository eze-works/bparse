use crate::Pattern;

pub fn end(input: &[u8]) -> Option<(&[u8], &[u8])> {
    if input.is_empty() {
        Some((&[], input))
    } else {
        None
    }
}

pub fn digit(input: &[u8]) -> Option<(&[u8], &[u8])> {
    (0x30..=0x39).test(input)
}

pub fn alpha(input: &[u8]) -> Option<(&[u8], &[u8])> {
    ('a'..='z').or('A'..='Z').test(input)
}

pub fn hex(input: &[u8]) -> Option<(&[u8], &[u8])> {
    ('a'..='f').or('A'..='F').or(digit).test(input)
}
