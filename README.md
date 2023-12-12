# bparse

A library for parsing bytes 


## Example

Hexadecimal color parser:

```rust
use bparse::prelude::*;
use std::str::from_utf8;

#[derive(Debug, PartialEq)]
pub struct Color {
  pub red: u8,
  pub green: u8,
  pub blue: u8,
}

fn hex_color(input: &str) -> Option<Color> {
  let hexdigit = ('0'..='9').or('a'..='f').or('A'..='F');

  let (_, rest) = parse("#", 1)(input.as_bytes())?;
  let (red, rest) = parse(&hexdigit, 2)(rest)?;
  let (green, rest) = parse(&hexdigit, 2)(rest)?;
  let (blue, rest) = parse(&hexdigit, 2)(rest)?;

  Some(Color {
    red: u8::from_str_radix(from_utf8(red).unwrap(), 16).unwrap(),
    green: u8::from_str_radix(from_utf8(green).unwrap(), 16).unwrap(),
    blue: u8::from_str_radix(from_utf8(blue).unwrap(), 16).unwrap() 
  })
}

fn main() {
  assert_eq!(hex_color("#2F14DF"), Some(Color {
    red: 47,
    green: 20,
    blue: 223,
  }));
}
```
