//! `cargo run --example encode --features binary-format < INPUT_FILE > OUTPUT_FILE`
extern crate bytecodec;
extern crate patricia_tree;

use bytecodec::Encode;
use bytecodec::io::IoEncodeExt;
use bytecodec::null::NullEncoder;
use patricia_tree::{PatriciaSet, node::NodeEncoder};
use std::io::BufRead;

fn main() {
    let mut set = PatriciaSet::new();
    let stdin = std::io::stdin();
    for line in stdin.lock().lines() {
        let line = line.unwrap();
        set.insert(line);
    }

    let mut encoder = NodeEncoder::new(NullEncoder);
    encoder.start_encoding(set.into()).unwrap();
    encoder.encode_all(std::io::stdout()).unwrap();
}
