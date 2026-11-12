//! FL4's ABI: numbering generated from `interfaces/` plus the fixed
//! constants of FL4's libsel4. Everything user space can observe about the
//! encoding of a system call is defined here or in libsel4, never in
//! `fl4-core` itself.
#![no_std]
#![forbid(unsafe_code)]

include!(concat!(env!("OUT_DIR"), "/generated.rs"));

#[allow(non_upper_case_globals)]
pub mod consts;
