//! An AP loads the boot core's CR4 (fl4-kernel smp.rs `fl4_ap_main`)
//! before its IDT is in: a bit this core cannot set faults with nothing to
//! catch it (a triple fault, not a rejected AP). So it loads only bits it
//! has checked: PCIDE (tlb::core_supported) and SMEP, SMAP and FSGSBASE
//! (cpu::cr4_supported); OSXSAVE and VMXE wait for `fpu::init` and
//! `vm::init`, which check this core's XSAVE and VMX first.
#![cfg(target_arch = "x86_64")]

use fl4_arch_x86_64::cpu;

const SMP: &str = include_str!("../../fl4-kernel/src/smp.rs");
const LIB: &str = include_str!("../../fl4-kernel/src/lib.rs");

/// The statements of `fl4_ap_main`, trimmed.
fn ap_main() -> Vec<&'static str> {
    let at = SMP.find("extern \"C\" fn fl4_ap_main(").expect("fl4_ap_main");
    let end = at + SMP[at..].find("\n}\n").unwrap();
    SMP[at..end].lines().map(str::trim).filter(|l| !l.is_empty() && !l.starts_with("//")).collect()
}

#[test]
fn ap_checks_every_cr4_bit_before_loading_it_without_an_idt() {
    let call = LIB.find("smp::start_aps(").expect("start_aps call");
    let line = &LIB[call..call + LIB[call..].find('\n').unwrap()];
    assert!(line.contains("cr4: cpu::ap_boot_cr4(cpu::read_cr4())"), "{line}");
    let m = ap_main();
    let pos = |s: &str| m.iter().position(|l| *l == s).unwrap_or_else(|| panic!("{s} missing"));
    let write = pos("cpu::write_cr4(f.cr4);");
    let idt = pos("gdt::init_core(c as usize, stack_top);");
    // Natively before the write; on SNP (CR4 from the VMSA, CPUID by #VC)
    // once the core's own IDT is in, like the PCID check.
    assert_eq!(m[write - 2], "if !snp::active() && !fl4_arch_x86_64::tlb::core_supported() { reject_ap(REJECT_TLB); }");
    assert_eq!(m[write - 1], "if !snp::active() && !cpu::core_cr4_supported(f.cr4) { reject_ap(REJECT_CR4); }");
    assert_eq!(m[idt + 1], "if snp::active() && !fl4_arch_x86_64::tlb::core_supported() { reject_ap(REJECT_TLB); }");
    assert_eq!(m[idt + 2], "if snp::active() && !cpu::core_cr4_supported(f.cr4) { reject_ap(REJECT_CR4); }");
    assert!(SMP.contains("REJECT_CR4 => "), "the rejection is reported");
}

#[test]
fn ap_cr4_leaves_osxsave_and_vmxe_to_the_cores_own_checks() {
    let all = u64::MAX;
    assert_eq!(cpu::ap_boot_cr4(all), all & !(1 << 18) & !(1 << 13));
    // SMEP, SMAP, FSGSBASE, PCIDE, OSXSAVE, VMXE, OSFXSR, PGE, PAE.
    assert_eq!(cpu::ap_boot_cr4(0x37_26a0), 0x33_06a0);
}

#[test]
fn cr4_bits_need_their_cpuid_bits() {
    let (fsgsbase, smep, smap) = (1u64 << 16, 1u64 << 20, 1u64 << 21);
    let (f_fsgsbase, f_smep, f_smap) = (1u32 << 0, 1u32 << 7, 1u32 << 20);
    // Bits FL4 does not check against CPUID leaf 7 pass: PAE, PGE,
    // OSFXSR, OSXMMEXCPT, PCIDE (tlb::core_supported).
    assert!(cpu::cr4_supported((1 << 5) | (1 << 7) | (1 << 9) | (1 << 10) | (1 << 17), 0));
    for set in 0..8u32 {
        let cr4 = [fsgsbase, smep, smap].iter().enumerate().filter(|(i, _)| set & (1 << i) != 0).fold(0, |a, (_, b)| a | b);
        for have in 0..8u32 {
            let ebx = [f_fsgsbase, f_smep, f_smap].iter().enumerate().filter(|(i, _)| have & (1 << i) != 0).fold(0, |a, (_, b)| a | b);
            assert_eq!(cpu::cr4_supported(cr4, ebx), set & !have == 0, "cr4 {cr4:#x} ebx {ebx:#x}");
        }
    }
}
