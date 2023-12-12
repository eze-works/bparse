# bparse

A library for recognizing patterns in byte slices. 

## Example

Hexadecimal color parser:

```rust
use bparse::{BytePattern, pattern};
use std::str::from_utf8;

#[derive(Debug, PartialEq)]
pub struct Color {
  pub red: u8,
  pub green: u8,
  pub blue: u8,
}

fn main() {
  assert_eq!(hex_color("#2F14DF"), Some(Color {
    red: 47,
    green: 20,
    blue: 223,
  }));
}

fn hex_color(input: &str) -> Option<Color> {
  let hexbyte = ('0'..='9').or('a'..='f').or('A'..='F').repeats(2);

  let (_, rest) = "#".test(input.as_bytes())?;

  let (red, rest) = hexbyte.test(rest)?;
  let (green, rest) = hexbyte.test(rest)?;
  let (blue, _) = hexbyte.then(pattern::end).test(rest)?;

  Some(Color {
    red: u8::from_str_radix(from_utf8(red).unwrap(), 16).unwrap(),
    green: u8::from_str_radix(from_utf8(green).unwrap(), 16).unwrap(),
    blue: u8::from_str_radix(from_utf8(blue).unwrap(), 16).unwrap() 
  })
}

```
