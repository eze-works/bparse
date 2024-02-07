# bparse

This crate provides utilites for parsing byte slices. The API borrows some
concepts from other parser-combinator crates but heavily simplifies things by
eschewing error management and focusing exclusively on parsing byte slices.

[Documentation](https://docs.rs/bparse)

# Example

The classic [nom example](https://crates.io/crates/nom); a hexadecimal color
parser:

```rust
use bparse::{Pattern, Parser, range, end};
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
  let hexbyte = range(b'0', b'9').or(range(b'A', b'F')).or(range(b'a', b'f')).repeats(2);

  let mut parser = Parser::new(input.as_bytes());

  parser.try_match("#")?;
  let red = parser.try_match(hexbyte)?;
  let green = parser.try_match(hexbyte)?;
  let blue = parser.try_match(hexbyte)?;
  parser.try_match(end)?;

  Some(Color {
    red: u8::from_str_radix(from_utf8(red).unwrap(), 16).unwrap(),
    green: u8::from_str_radix(from_utf8(green).unwrap(), 16).unwrap(),
    blue: u8::from_str_radix(from_utf8(blue).unwrap(), 16).unwrap()
  })
}
```
