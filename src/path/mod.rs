//! Patricia trees with [Path] keys, with the restriction that only UTF8 paths are allowed except on
//! unix and WASI.
pub mod map;