//! Memory-efficient data structures based on patricia tree (a.k.a, radix tree).
//!
//! A common prefixes of the keys in a patricia tree are represented by a shared path.
//! So if the prefixes of the key set is highly redundant,
//! the memory usage of the resulting patricia tree will be drastically less than
//! more generic data structures (e.g., `BTreeMap`).
//!
//! See [Radix tree](https://en.wikipedia.org/wiki/Radix_tree) for more details.
//!
//! # Examples
//!
//! ```
//! use patricia_tree::PatriciaMap;
//!
//! let mut map = PatriciaMap::new();
//! map.insert("foo", 1);
//! map.insert("bar", 2);
//! map.insert("baz", 3);
//! assert_eq!(map.len(), 3);
//!
//! assert_eq!(map.get("foo"), Some(&1));
//! assert_eq!(map.get("bar"), Some(&2));
//! assert_eq!(map.get("baz"), Some(&3));
//! ```
#![warn(missing_docs)]
#![allow(clippy::cast_ptr_alignment, clippy::cast_ref_to_mut)]

#[macro_use]
extern crate bitflags;
#[cfg(feature = "binary-format")]
#[macro_use]
extern crate bytecodec;
#[cfg(test)]
extern crate rand;
#[cfg(feature = "binary-format")]
#[macro_use]
extern crate trackable;

pub use map::PatriciaMap;
pub use set::PatriciaSet;

pub mod map;
pub mod node;
pub mod set;

#[cfg(feature = "binary-format")]
mod codec;
#[cfg(feature = "serde")]
mod serialization;
mod tree;

#[allow(missing_docs)]
pub trait Unit {
    fn is_unit_boundary(key: &[u8], i: usize) -> bool;
}

#[allow(missing_docs)]
pub struct Byte;

impl Unit for Byte {
    fn is_unit_boundary(_: &[u8], _: usize) -> bool {
        true
    }
}

#[allow(missing_docs)]
pub struct Char;

impl Unit for Char {
    fn is_unit_boundary(key: &[u8], i: usize) -> bool {
        std::str::from_utf8(key).map_or(false, |s| s.is_char_boundary(i))
    }
}
