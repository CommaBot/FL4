//! The TDX AP trampoline (fl4-kernel ap.S). It runs with no IDT on a page
//! that leaves the address space once `fl4_ap_main` loads the kernel's
//! tables, so the order of its steps is what keeps it from a triple fault.
#![cfg(target_arch = "x86_64")]

const AP: &str = include_str!("../../fl4-kernel/src/ap.S");
const BOOT: &str = include_str!("../../fl4-kernel/src/boot.S");
const SMP: &str = include_str!("../../fl4-kernel/src/smp.rs");

/// The trampoline's instructions, comments and blank lines removed.
fn trampoline() -> Vec<&'static str> {
    let at = AP.find("fl4_tdx_ap_trampoline:").expect("trampoline");
    let end = at + AP[at..].find("fl4_tdx_ap_trampoline_end:").unwrap();
    let mut comment = false;
    let mut out = Vec::new();
    for line in AP[at..end].lines() {
        let mut l = line.trim();
        if comment {
            match l.find("*/") {
                Some(i) => {
                    l = l[i + 2..].trim();
                    comment = false;
                }
                None => continue,
            }
        }
        if let Some(i) = l.find("/*") {
            comment = !l[i..].contains("*/");
            l = l[..i].trim();
        }
        if !l.is_empty() {
            out.push(l);
        }
    }
    out
}

fn pos(t: &[&str], what: &str) -> usize {
    t.iter().position(|l| l.starts_with(what)).unwrap_or_else(|| panic!("{what} missing"))
}

/// Audit: GDTR must not name the trampoline's page when the kernel's tables
/// unmap it (`fl4_ap_main`), or the first exception there is a triple fault.
#[test]
fn the_ap_runs_on_the_images_gdt_before_it_leaves_the_boot_tables() {
    let t = trampoline();
    let stack = pos(&t, "movq tdx_ap_stack(%rip), %rsp");
    let gdt = pos(&t, "movabsq $fl4_efi_gdt, %rax");
    let load = stack + t[stack..].iter().position(|l| *l == "lgdt 6(%rsp)").expect("lgdt");
    let lret = pos(&t, "lretq");
    assert!(stack < gdt && gdt < load && load < lret, "{t:?}");
    assert!(t[lret..].iter().all(|l| !l.starts_with("lgdt")), "no other GDT before fl4_ap_main");
}

/// The image's GDT is read-only under the kernel's tables and the page's
/// may be under firmware's: a load must not have to set an accessed bit.
#[test]
fn every_gdt_an_ap_loads_needs_no_write() {
    let efi = &BOOT[BOOT.find("fl4_efi_gdt:").expect("fl4_efi_gdt")..];
    assert!(efi.contains(".quad 0, 0, 0x00af9b000000ffff, 0x00cf93000000ffff"));
    let t = trampoline();
    let gdt = pos(&t, "fl4_tdx_ap_gdt:");
    assert_eq!(&t[gdt + 1..gdt + 5], [".quad 0", ".quad 0x00cf9b000000ffff", ".quad 0x00af9b000000ffff", ".quad 0x00cf93000000ffff"]);
}

/// PGE, PCIDE and CET go off before either way to the new CR3: it drops
/// firmware's global and PCID TLB entries, and clearing CR0.PG needs it.
#[test]
fn firmware_tlb_entries_and_cet_go_before_the_new_tables() {
    let t = trampoline();
    let clear = pos(&t, "andq $~((1 << 7) | (1 << 17) | (1 << 23)), %rax");
    assert_eq!(t[clear + 1], "movq %rax, %cr4");
    let la57 = pos(&t, "btq $12, %rax");
    let first_cr3 = pos(&t, "movq %rax, %cr3");
    let compat = pos(&t, "ljmpl *tdx_ap_to_compat(%rip)");
    let paging_off = pos(&t, "andl $0x7fffffff, %eax");
    assert!(clear < la57 && la57 < first_cr3 && first_cr3 < compat && compat < paging_off);
}

/// `fl4_ap_main` loads the boot IDT before the kernel's tables.
#[test]
fn the_ap_has_an_idt_before_the_kernels_tables() {
    let at = SMP.find("extern \"C\" fn fl4_ap_main(").expect("fl4_ap_main");
    let m = &SMP[at..];
    assert!(m.find("gdt::load_boot_idt()").unwrap() < m.find("cpu::write_cr3(paging::root_paddr())").unwrap());
}
