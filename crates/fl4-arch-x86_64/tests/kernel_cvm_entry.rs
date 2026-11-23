//! Audit (TDX r5, fix 1): in two places the kernel runs in ring 0 on the
//! user's RSP (entry.S): from `fl4_syscall_entry` until it loads the entry
//! stack, and on the SYSRET path from loading the user's RSP through
//! SYSRETQ. A thread that points RSP into an IST and single-steps a SYSCALL
//! (IRETQ with TF set onto it) gets a #DB at the entry's first instruction
//! with that RSP; a VMM can inject an NMI anywhere in either window. The
//! confidential guest's IST check (entry.rs `fl4_cvm_kernel_entry_stack`)
//! took that RSP for an overwritten kernel frame and ended the guest. It now
//! exempts exactly those entries (cvm_entry.rs) and nothing else.
#![cfg(target_arch = "x86_64")]

#[allow(dead_code)]
#[path = "../../fl4-kernel/src/cvm_entry.rs"]
mod cvm_entry;

use cvm_entry::{invalid_entry, user_rsp_window};

const ENTRY_S: &str = include_str!("../../fl4-kernel/src/entry.S");
const ENTRY_RS: &str = include_str!("../../fl4-kernel/src/entry.rs");

/// An IST of the entry area and a user RSP pointing into it.
const IST: core::ops::Range<u64> = 0xffff_ff80_0010_0000..0xffff_ff80_0010_1000;
const RSP_IN_IST: u64 = IST.start + 0x800;
const RSP_OUTSIDE: u64 = 0x7fff_ffff_e000;
/// fl4_syscall_entry's four user-RSP instructions, and the SYSRET path's
/// five from after POP %rsp through SYSRETQ.
const SYSCALL: core::ops::Range<u64> = 0xffff_ffff_8010_a010..0xffff_ffff_8010_a028;
const SYSRET: core::ops::Range<u64> = 0xffff_ffff_8010_a59c..0xffff_ffff_8010_a5bf;
const IF: u64 = 1 << 9;

fn overlap(vector: u64, rip: u64, rsp: u64) -> bool {
    invalid_entry(vector, rip, rsp, IF, IST, SYSCALL, SYSRET).0
}

#[test]
fn a_single_stepped_syscall_into_an_ist_rsp_is_no_overwritten_frame() {
    assert!(user_rsp_window(1, SYSCALL.start, SYSCALL, SYSRET));
    assert_eq!(invalid_entry(1, SYSCALL.start, RSP_IN_IST, 0x2, IST, SYSCALL, SYSRET), (false, false));
    // Elsewhere a #DB in kernel mode with RSP in its IST did overwrite one.
    for rip in [SYSCALL.start + 1, SYSCALL.start + 3, SYSCALL.end - 1, SYSCALL.end, SYSCALL.start - 1, SYSRET.start, SYSRET.end - 1, SYSRET.end] {
        assert!(!user_rsp_window(1, rip, SYSCALL, SYSRET), "{rip:#x}");
        assert!(overlap(1, rip, RSP_IN_IST), "{rip:#x}");
    }
}

#[test]
fn an_nmi_or_mce_anywhere_in_either_window_is_exempt() {
    for vector in [2, 18] {
        for rip in SYSCALL.chain(SYSRET) {
            assert!(user_rsp_window(vector, rip, SYSCALL, SYSRET), "{vector} {rip:#x}");
            assert_eq!(invalid_entry(vector, rip, RSP_IN_IST, 0x2, IST, SYSCALL, SYSRET), (false, false), "{vector} {rip:#x}");
        }
        for rip in [SYSCALL.start - 1, SYSCALL.end, SYSRET.start - 1, SYSRET.end, 0xffff_ffff_8010_0000, 0x40_0000] {
            assert!(!user_rsp_window(vector, rip, SYSCALL, SYSRET), "{vector} {rip:#x}");
            assert!(overlap(vector, rip, RSP_IN_IST), "{vector} {rip:#x}");
        }
    }
}

#[test]
fn no_other_vector_is_exempt_even_in_the_windows() {
    for vector in [0, 3, 6, 8, 13, 14, 20, 29, 32, 0x30, 0xec, 0xfe, 0xff] {
        for rip in [SYSCALL.start, SYSCALL.start + 1, SYSRET.start, SYSRET.end - 1] {
            assert!(!user_rsp_window(vector, rip, SYSCALL, SYSRET), "{vector:#x} {rip:#x}");
            assert!(overlap(vector, rip, RSP_IN_IST), "{vector:#x} {rip:#x}");
        }
    }
    // An IRQ there is also one taken with IF clear.
    for vector in [32, 0xff] {
        assert_eq!(invalid_entry(vector, SYSCALL.start, RSP_IN_IST, 0x2, IST, SYSCALL, SYSRET), (true, true));
        assert_eq!(invalid_entry(vector, SYSRET.start, RSP_OUTSIDE, 0x2, IST, SYSCALL, SYSRET), (false, true));
        assert_eq!(invalid_entry(vector, SYSRET.start, RSP_OUTSIDE, IF | 0x2, IST, SYSCALL, SYSRET), (false, false));
    }
    // Exceptions are never IRQs, whatever IF says.
    assert_eq!(invalid_entry(13, 0x1000, RSP_OUTSIDE, 0x2, IST, SYSCALL, SYSRET), (false, false));
}

#[test]
fn an_rsp_outside_the_ist_is_never_an_overlap() {
    for vector in [1, 2, 8, 13, 18, 20, 32] {
        for rip in [SYSCALL.start, SYSCALL.end, SYSRET.start, 0x1000] {
            for rsp in [RSP_OUTSIDE, IST.start - 8, IST.end, 0] {
                assert!(!overlap(vector, rip, rsp), "{vector} {rip:#x} {rsp:#x}");
            }
        }
    }
    assert!(overlap(2, 0x1000, IST.start) && overlap(2, 0x1000, IST.end - 1));
}

#[test]
fn an_empty_window_exempts_nothing() {
    let at = SYSCALL.start;
    let empty = at..at;
    for vector in [1, 2, 18] {
        assert!(!user_rsp_window(vector, at, empty.clone(), empty.clone()), "{vector}");
        assert!(invalid_entry(vector, at, RSP_IN_IST, IF, IST, empty.clone(), empty.clone()).0, "{vector}");
    }
    // One empty window leaves the other as it was.
    assert!(!user_rsp_window(1, at, empty.clone(), SYSRET));
    assert!(user_rsp_window(2, SYSRET.start, empty.clone(), SYSRET));
    assert!(!user_rsp_window(2, SYSRET.end, empty, SYSRET));
}

/// The kernel takes the windows from entry.S's symbols and decides only
/// through `invalid_entry`; the instructions in each window are checked on
/// the linked kernel (xtask/scripts/check_vm_asm.py). A #DB let through at
/// the SYSCALL entry is the deferred user #DB fl4_entry hands back
/// (`deferred_user_debug`: [fl4_vectors, fl4_common_entry) holds the
/// SYSCALL entry).
#[test]
fn the_kernel_checks_entries_with_the_windows_entry_s_marks() {
    let label = |l: &str| ENTRY_S.find(&format!("\n{l}:\n")).unwrap_or_else(|| panic!("{l}"));
    assert!(label("fl4_vectors") < label("fl4_syscall_entry"));
    assert!(label("fl4_syscall_entry") < label("fl4_syscall_on_stack"));
    assert!(label("fl4_syscall_on_stack") < label("fl4_common_entry"));
    assert!(label("fl4_sysret_user_rsp") < label("fl4_sysret_end"));

    let check = &ENTRY_RS[ENTRY_RS.find("extern \"C\" fn fl4_cvm_kernel_entry_stack(").expect("IST check")..];
    let check = &check[..check.find("\n}\n").unwrap()];
    assert!(check.contains(
        "let syscall = fl4_syscall_entry as *const () as u64..core::ptr::addr_of!(fl4_syscall_on_stack) as u64;"
    ));
    assert!(check.contains(
        "let sysret = core::ptr::addr_of!(fl4_sysret_user_rsp) as u64..core::ptr::addr_of!(fl4_sysret_end) as u64;"
    ));
    assert!(check.contains(
        "let (ist_overlap, if_clear) = crate::cvm_entry::invalid_entry(f.vector, f.rip, f.rsp, f.rflags, stack, syscall, sysret);"
    ));
    assert!(!check.contains("stack.contains("), "only through invalid_entry");
    assert!(ENTRY_RS.contains("f.vector == 1 && (start..end).contains(&f.rip)"));
}
