//! The TDX AP trampoline (fl4-kernel ap.S). It runs with no IDT on a page
//! that leaves the address space once `fl4_ap_main` loads the kernel's
//! tables, so the order of its steps is what keeps it from a triple fault.
#![cfg(target_arch = "x86_64")]

const AP: &str = include_str!("../../fl4-kernel/src/ap.S");
const BOOT: &str = include_str!("../../fl4-kernel/src/boot.S");
const SMP: &str = include_str!("../../fl4-kernel/src/smp.rs");
const GDT: &str = include_str!("../../fl4-kernel/src/gdt.rs");
const TDX: &str = include_str!("../../fl4-kernel/src/tdx.rs");
const LIB: &str = include_str!("../../fl4-kernel/src/lib.rs");

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

/// IA32_CSTAR takes #VE in a TD (TDX Module 1.5 `msr_config_lookup`), and
/// every core writes the SYSCALL MSRs in `gdt::init_core` before it can
/// handle one usefully: seen on a real GCP C3 TD.
#[test]
fn a_td_does_not_write_cstar() {
    let write = GDT.find("wrmsr(msr::CSTAR,").expect("CSTAR write");
    let guard = GDT[..write].rfind("if !fl4_arch_x86_64::tdx::active() {").expect("TDX guard");
    assert!(!GDT[guard..write].contains('}'), "the write is inside the guard");
    assert_eq!(GDT.matches("msr::CSTAR").count(), 1);
}

/// The console is the VMM's. A fatal detail in the kernel's entry and #VE
/// code names vectors, reasons and flags, never a frame's registers.
#[test]
fn fatal_details_in_the_entry_paths_name_no_registers() {
    for src in [include_str!("../../fl4-kernel/src/entry.rs"), include_str!("../../fl4-kernel/src/tdx.rs")] {
        for (at, _) in src.match_indices("terminate_with(") {
            let call = &src[at..at + src[at..].find('\n').unwrap()];
            for field in ["f.rip", "f.rsp", "f.rax", "f.rbx", "f.rcx", "f.rdx", "f.rsi", "f.rdi", "f.rbp", "f.r8", "f.r9", "f.r1", "info.gpa", "info.gla"] {
                assert!(!call.contains(field), "{field} in {call}");
            }
        }
    }
    let entry = include_str!("../../fl4-kernel/src/entry.rs");
    assert!(entry.contains("kprintln!(\"FL4: unhandled user TDX #VE (exit_reason {})\", info.exit_reason);"));
}

/// Audit (TDX r1, fix 1): a vCPU takes its core index, once, before it
/// touches that core's stack, and none may once the boot core is done. The
/// claim is on the boot table (the wakeup page may be read-only before it),
/// by the kernel statics' absolute addresses (this code runs from a copy),
/// and the index passed on is the one claimed.
#[test]
fn an_ap_claims_its_index_once_before_it_takes_a_stack() {
    let t = trampoline();
    let tables = pos(&t, ".Ltdx_ap_tables:");
    let closed = pos(&t, "movabsq $FL4_TDX_AP_CLOSED, %rax");
    let cpu = pos(&t, "movq tdx_ap_cpu(%rip), %r12");
    let claimed = pos(&t, "movabsq $FL4_TDX_AP_CLAIMED, %rax");
    let bts = pos(&t, "lock btsq %r12, (%rax)");
    let stack = pos(&t, "movq tdx_ap_stack(%rip), %rsp");
    assert!(tables < closed && closed < cpu && cpu < claimed && claimed < bts && bts < stack, "{t:?}");
    assert_eq!(&t[closed + 1..closed + 3], ["cmpb $0, (%rax)", "jne .Ltdx_ap_reject"]);
    assert_eq!(&t[cpu + 1..claimed], ["testq %r12, %r12", "jz .Ltdx_ap_reject", "cmpq $64, %r12", "jae .Ltdx_ap_reject"]);
    assert_eq!(t[bts + 1], "jc .Ltdx_ap_reject");
    // Nothing between the boot table and the claim writes memory or uses
    // the stack.
    for l in &t[tables..bts] {
        let dst = l.rsplit(", ").next().unwrap();
        assert!(!l.starts_with("push") && !l.contains("%rsp") && !(l.starts_with("mov") && dst.contains('(')), "{l}");
    }
    // No RIP-relative kernel statics: the copy is not where they are.
    assert!(t.iter().all(|l| !l.contains("FL4_TDX_AP_CLOSED(%rip)") && !l.contains("FL4_TDX_AP_CLAIMED(%rip)") && !l.contains("FL4_CVM_POISONED(%rip)")));
    // The index claimed is the one passed on, not one re-read from the page.
    let jmp = pos(&t, "jmp *%rax");
    assert_eq!(t[jmp - 2], "movq %r12, %rdi");
    assert!(!t.contains(&"movq tdx_ap_cpu(%rip), %rdi"));
    assert_eq!(t.iter().filter(|l| l.starts_with("movq tdx_ap_cpu(%rip)")).count(), 1);
}

/// A rejected vCPU has no stack and no IDT: it poisons the guest, reports
/// with a TDCALL (no #VE), and spins without HLT or a GDT of its own.
#[test]
fn a_rejected_ap_poisons_reports_and_spins() {
    let t = trampoline();
    let jmp = pos(&t, "jmp *%rax");
    let reject = pos(&t, ".Ltdx_ap_reject:");
    let gdt = pos(&t, "fl4_tdx_ap_gdt:");
    assert!(jmp < reject && reject < gdt);
    let r = &t[reject + 1..gdt];
    assert_eq!(r[0], "cli");
    assert_eq!(&r[1..3], ["movabsq $FL4_CVM_POISONED, %rax", "movb $1, (%rax)"]);
    let call = r.iter().position(|l| *l == ".byte 0x66, 0x0f, 0x01, 0xcc").expect("TDCALL");
    for want in ["xorl %eax, %eax", "movl $((1 << 10) | (1 << 11) | (1 << 12) | (1 << 13)), %ecx", "xorl %r10d, %r10d", "movl $0x10003, %r11d", "movl $11, %r12d", "xorl %r13d, %r13d"] {
        let at = r.iter().position(|l| *l == want).unwrap_or_else(|| panic!("{want} missing"));
        assert!(at < call, "{want}");
    }
    assert_eq!(&r[call + 1..], ["1:", "pause", "jmp 1b", ".align 8", ".global fl4_tdx_ap_gdt"]);
    assert!(r.iter().all(|l| !l.starts_with("hlt") && !l.starts_with("lgdt") && !l.contains("%rsp") && !l.starts_with("push") && !l.starts_with("call")));
}

/// Audit (TDX r2, R1-2): once the cores are up the trampoline is closed,
/// and its page is never written again: a late vCPU may be fetching from
/// it (no cross-modifying code), and the code there rejects it. The boot
/// core gives up on a poisoned guest wherever it waits for firmware.
#[test]
fn the_wakeup_page_is_closed_and_left_as_it_is() {
    let f = &TDX[TDX.find("pub fn finish_wakeup(").unwrap()..];
    let f = &f[..f.find("\n}\n").unwrap()];
    assert!(f.starts_with("pub fn finish_wakeup() {"), "no page to write");
    assert!(f.contains("FL4_TDX_AP_CLOSED.store(true, Ordering::Release);"));
    assert!(f.contains("fence(Ordering::SeqCst);"));
    for write in ["write_bytes", "from_raw_parts_mut", "pptr(", "poison"] {
        assert!(!f.contains(write), "{write}");
    }
    assert!(!TDX.contains("poison_wakeup_page") && !TDX.contains("PARKED_STUB"));
    let p = &TDX[TDX.find("pub fn prepare_wakeup(").unwrap()..];
    assert!(p[..p.find("\n}\n").unwrap()].contains("FL4_TDX_AP_CLAIMED.load(Ordering::Acquire) != 1"));
    assert!(TDX.contains("pub static FL4_TDX_AP_CLAIMED: AtomicU64 = AtomicU64::new(1);"));
    let s = &TDX[TDX.find("pub fn start_ap(").unwrap()..];
    let s = &s[..s.find("\n}\n").unwrap()];
    let w = &s[s.find("let wait_idle = || {").unwrap()..];
    let w = &w[..w.find("\n    };").unwrap()];
    let lines: Vec<&str> = w.lines().map(str::trim).collect();
    assert_eq!(lines[1], "cvm::halt_if_poisoned();", "on the way in");
    assert_eq!(lines[lines.len() - 1], "cvm::halt_if_poisoned();", "on the way out");
    assert!(lines[2].starts_with("while command.load(Ordering::Acquire) != 0 {"));
    assert_eq!(lines[3], "cvm::halt_if_poisoned();", "while waiting");
    let write = s.find("((mb + 4) as *mut u32).write_volatile(id);").unwrap();
    assert!(s[..write].trim_end().trim_end_matches("unsafe {").trim_end().ends_with("cvm::halt_if_poisoned();"), "before the mailbox is written");
}

/// The wakeup page is never handed out again: not RAM (so not free, DMA or
/// a load target), not device memory, and private if anything maps it.
#[test]
fn the_wakeup_page_is_kept_from_user_space() {
    let ram = LIB.find("ram.remove(page, page + PAGE);").expect("out of RAM");
    assert!(ram < LIB.find("let mut free = ram;").unwrap());
    assert!(ram < LIB.find("let load = match ram.find(").unwrap());
    let dev = LIB.find("let mut dev = bootmem::device(").unwrap();
    let removed = LIB[dev..].find("dev.remove(page, page + PAGE);").expect("out of device memory");
    assert!(dev + removed < LIB.find("bootmem::device_regions(").unwrap());
    assert!(LIB.contains("if let (Some(page), true) = (mb.tdx_ap_page, cvm::active()) {\n        st.private_devices.add(page, page + PAGE);"));
}

/// Audit (TDX r1, fix 2): a multi-vCPU TD without a usable wakeup mailbox
/// does not boot on one core, leaving the others in firmware.
#[test]
fn a_multi_vcpu_td_without_a_mailbox_does_not_boot() {
    let at = LIB.find("if td.is_some() && tdx_wakeup.is_none() {").unwrap();
    let b = &LIB[at..];
    let b = &b[..b.find("\n    }\n").unwrap()];
    let check = b.find("if td.is_some_and(|t| t.num_vcpus > 1) {").expect("check");
    assert!(b[check..].contains("fail(\"no usable TDX AP wakeup mailbox for multi-vCPU TD\")"));
    assert!(LIB.find("if td.is_some() && tdx_wakeup.is_none() {").unwrap() < LIB.find("let ncpus = smp::start_aps(").unwrap());
}

/// Audit (TDX r1, fix 3): a kernel #VE answers CPUID from the VMM only for
/// the whitelisted leaves.
#[test]
fn a_kernel_cpuid_ve_is_whitelisted() {
    let ve = &TDX[TDX.find("pub fn ve(").unwrap()..TDX.find("fn translate(").unwrap()];
    assert!(ve.contains("(td::EXIT_CPUID, [0x0f, 0xa2]) if td::virtual_cpuid(f.rax as u32) => {"));
    assert_eq!(ve.matches("td::EXIT_CPUID").count(), 1);
}

/// Audit (TDX r1, fix 5): in a confidential guest a kernel panic says only
/// that it happened on the VMM's console: no message, location or trace.
#[test]
fn a_cvm_panic_prints_nothing_but_that_it_happened() {
    let p = &LIB[LIB.find("#[panic_handler]").unwrap()..];
    let p = &p[..p.find("\n}\n").unwrap()];
    let hardened = p.find("if cvm::hardened() {").expect("hardened branch");
    let branch = &p[hardened..hardened + p[hardened..].find("\n    }\n").unwrap()];
    assert!(branch.contains("kprintln!(\"FL4: kernel panic\");"));
    assert!(branch.contains("cvm::terminate(0);"));
    assert!(!branch.contains("info") && !branch.contains("dump_trace"));
    // The detailed lines come only after it.
    assert!(hardened < p.find("kprintln!(\"FL4 panic: {}\", info);").unwrap());
    assert!(hardened < p.find("entry::dump_trace();").unwrap());
}

/// Audit (TDX r2, R1-4): the kernel uses the MADT's mailbox only if the
/// memory map says ACPI NVS and, from fl4-efi, it is the page the loader
/// checked against `EfiACPIMemoryNVS`.
#[test]
fn the_kernel_uses_only_the_mailbox_the_loader_checked() {
    let at = LIB.find("let mailbox = acpi.mp_wakeup_mailbox.filter(|&m| {").expect("mailbox");
    let m = &LIB[at..at + LIB[at..].find("});").unwrap()];
    assert!(m.contains("bootmem::mailbox_ok(m, window_top,"));
    assert!(m.contains("&& (mb.tdx_ap_page.is_none() || mb.tdx_mailbox == Some(m))"));
}

/// The boot modules and logs reach the root task only as device memory:
/// a device list too full for them stops the boot.
#[test]
fn boot_modules_must_fit_the_device_ranges() {
    let at = LIB.find("    dev.add(image.p_end, log_end);\n").expect("dev.add");
    assert!(LIB[at..].starts_with("    dev.add(image.p_end, log_end);\n    // The modules and logs reach the root task only as device memory.\n    if log_end > image.p_end && !dev.contains(image.p_end, log_end) {\n        fail(\"boot modules or event logs exceed the boot device range limit\");"));
}

/// Audit (TDX r2, R1-3): in a confidential guest the kernel reads ACPI
/// tables only from RAM, ACPI reclaim or NVS memory of the memory map.
#[test]
fn a_cvm_reads_acpi_only_from_firmware_memory() {
    let at = LIB.find("let acpi_readable = |p: u64, len: u64| {").expect("readable");
    let r = &LIB[at..at + LIB[at..].find("};").unwrap()];
    assert!(r.contains("!cvm::hardened() ||"));
    assert!(r.contains("matches!(e.ty, 1 | 3 | 4) && e.base <= p && end <= e.base.saturating_add(e.len)"));
    assert!(LIB.contains("acpi::init(mb.rsdp, window_top, &acpi_readable)"));
}

/// Audit (TDX r2, R1-7): the loader stops without HLT (#VE in a TD) or
/// CPUID (#VC under SEV-ES and SNP, a forged leaf 21H), and reports to a
/// VMM only in a TD that TDG.VP.INFO confirmed; so does its panic handler.
#[test]
fn the_loader_halts_without_hlt_or_cpuid() {
    let x86 = include_str!("../../fl4-efi/src/x86.rs");
    let h = &x86[x86.find("pub(super) fn halt_forever() -> ! {").expect("halt_forever")..];
    let h = &h[..h.find("\n}\n").unwrap()];
    assert!(h.contains("asm!(\"cli\""));
    assert!(!h.contains("hlt") && !h.contains("cpuid"));
    assert!(h.contains("if TDX_CONFIRMED.load(core::sync::atomic::Ordering::Acquire) {"));
    assert!(h.trim_end().ends_with("loop {\n        core::hint::spin_loop();\n    }"));
    // Set only once TDG.VP.INFO answered with a valid width.
    assert_eq!(x86.matches("TDX_CONFIRMED.store(").count(), 1);
    let m = &x86[x86.find("fn tdx_shared_mask() -> u64 {").unwrap()..];
    let m = &m[..m.find("\n}\n").unwrap()];
    let valid = m.find("fail(\"invalid TDX guest information\");").unwrap();
    assert!(valid < m.find("TDX_CONFIRMED.store(true, core::sync::atomic::Ordering::Release);").unwrap());
    let fail = include_str!("../../fl4-efi/src/lib.rs");
    assert!(fail.contains("pub fn halt() -> ! {\n    x86::halt_forever()\n}"));
    let bin = include_str!("../../fl4-efi/src/bin/fl4-efi.rs");
    assert!(bin.contains("fn panic(_: &core::panic::PanicInfo) -> ! {\n    fl4_efi::halt()\n}"));
    assert!(!bin.contains("hlt"));
}

/// Audit (TDX r3, R2-2): firmware's write-back reserved memory has a type
/// of its own: in a confidential guest it stays out of device memory and
/// inside the private boundaries, as ACPI NVS does, but ACPI tables are not
/// read from it and no mailbox may be there.
#[test]
fn private_reserved_memory_is_kept_private_but_not_read() {
    let hardened = LIB.find("if matches!(e.ty, 1 | 4 | bootmem::PRIVATE_RESERVED) {").expect("out of device memory");
    assert!(LIB[..hardened].rfind("if cvm::hardened() {").is_some());
    assert!(LIB.contains("if e.len != 0 && matches!(e.ty, 1 | 3 | 4 | bootmem::PRIVATE_RESERVED) {"), "private boundary");
    let at = LIB.find("let acpi_readable = |p: u64, len: u64| {").unwrap();
    assert!(!LIB[at..at + LIB[at..].find("};").unwrap()].contains("PRIVATE_RESERVED"));
    let bootmem = include_str!("../../fl4-kernel/src/bootmem.rs");
    assert!(bootmem.contains("pub const PRIVATE_RESERVED: u32 = 0x464c_3411;"));
    assert!(bootmem.contains("ty == 4 && base <= mailbox"));
}
