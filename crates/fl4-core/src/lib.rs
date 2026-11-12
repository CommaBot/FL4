//! FL4 kernel logic. Every kernel decision lives here. The crate must stay
//! inside the Rust subset that Charon and Aeneas translate (DESIGN.md §6):
//! no unsafe, no alloc, no closures stored in data, no `dyn`, explicit
//! checked or wrapping arithmetic, loops bounded by kernel-controlled data.
#![no_std]
#![forbid(unsafe_code)]

pub mod msginfo;
