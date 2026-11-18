//! Exercise the kernel's actual ACPI parser with host-allocated firmware tables.
//! Only the physical-to-virtual address translation is replaced for this test.
extern crate self as fl4_core;

pub mod layout {
    pub fn pptr(p: u64) -> u64 {
        p
    }
}

#[path = "../../crates/fl4-kernel/src/acpi.rs"]
mod acpi;

fn checksum(table: &mut [u8], offset: usize) {
    table[offset] = 0;
    table[offset] = table.iter().fold(0u8, |sum, byte| sum.wrapping_add(*byte)).wrapping_neg();
}

fn parse(entries: &[u8]) -> acpi::Info {
    let mut madt = vec![0; 44];
    madt.extend_from_slice(entries);
    let len = madt.len() as u32;
    madt[..4].copy_from_slice(b"APIC");
    madt[4..8].copy_from_slice(&len.to_le_bytes());
    madt[8] = 6;
    checksum(&mut madt, 9);

    let mut xsdt = [0u8; 44];
    xsdt[..4].copy_from_slice(b"XSDT");
    xsdt[4..8].copy_from_slice(&44u32.to_le_bytes());
    xsdt[8] = 1;
    xsdt[36..44].copy_from_slice(&(madt.as_ptr() as u64).to_le_bytes());
    checksum(&mut xsdt, 9);

    let mut rsdp = [0u8; 36];
    rsdp[..8].copy_from_slice(b"RSD PTR ");
    rsdp[15] = 2;
    rsdp[20..24].copy_from_slice(&36u32.to_le_bytes());
    rsdp[24..32].copy_from_slice(&(xsdt.as_ptr() as u64).to_le_bytes());
    checksum(&mut rsdp[..20], 8);
    checksum(&mut rsdp, 32);

    acpi::init(Some(rsdp.as_ptr() as u64)).expect("valid RSDP")
}

fn lapic(id: u8, flags: u32) -> [u8; 8] {
    let mut entry = [0u8; 8];
    entry[1] = 8;
    entry[2] = id;
    entry[3] = id;
    entry[4..8].copy_from_slice(&flags.to_le_bytes());
    entry
}

fn x2apic(id: u32, flags: u32) -> [u8; 16] {
    let mut entry = [0u8; 16];
    entry[0] = 9;
    entry[1] = 16;
    entry[4..8].copy_from_slice(&id.to_le_bytes());
    entry[8..12].copy_from_slice(&flags.to_le_bytes());
    entry[12..16].copy_from_slice(&id.to_le_bytes());
    entry
}

#[test]
fn only_enabled_lapic_and_x2apic_entries_are_boot_cpus() {
    let mut entries = Vec::new();
    // Unusable, online-capable only, enabled, and enabled with a reserved bit.
    for flags in [0, 2, 1, 3] {
        entries.extend_from_slice(&lapic(flags as u8, flags));
        entries.extend_from_slice(&x2apic(0x100 + flags, flags));
    }
    let mut ioapic = [1, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    ioapic[4..8].copy_from_slice(&0xfec0_0000u32.to_le_bytes());
    entries.extend_from_slice(&ioapic);

    let info = parse(&entries);
    assert_eq!(&info.cpus[..info.n_cpus], &[1, 0x101, 3, 0x103]);
    assert_eq!(&info.ioapics[..info.n_ioapics], &[0xfec0_0000]);
}

#[test]
fn hotplug_slots_do_not_consume_boot_cpu_capacity() {
    let mut entries = Vec::new();
    for id in 0..acpi::MAX_CPUS as u32 {
        entries.extend_from_slice(&lapic(id as u8, 2));
        entries.extend_from_slice(&x2apic(0x100 + id, 2));
    }
    entries.extend_from_slice(&lapic(0x80, 1));
    entries.extend_from_slice(&x2apic(0x180, 1));

    let info = parse(&entries);
    assert_eq!(&info.cpus[..info.n_cpus], &[0x80, 0x180]);
}

fn ioapic(addr: u32, len: u8) -> Vec<u8> {
    let mut e = vec![0u8; len as usize];
    e[0] = 1;
    e[1] = len;
    if len >= 8 {
        e[4..8].copy_from_slice(&addr.to_le_bytes());
    }
    e
}

#[test]
fn every_ioapic_is_recorded_past_the_ones_the_kernel_drives() {
    // Their registers must stay out of user space's device memory.
    let mut entries = Vec::new();
    for i in 0..10u32 {
        entries.extend_from_slice(&ioapic(0xfec0_0000 + i * 0x1000, 12));
    }
    let info = parse(&entries);
    assert_eq!(info.n_ioapics, 10);
    assert!(!info.ioapics_lost);
    assert_eq!(info.ioapics[9], 0xfec0_9000);
}

#[test]
fn madt_entries_too_short_for_their_fields_are_skipped() {
    let mut entries = Vec::new();
    let mut short_lapic = lapic(7, 1);
    short_lapic[1] = 6;
    entries.extend_from_slice(&short_lapic[..6]);
    entries.extend_from_slice(&ioapic(0xfec0_0000, 8));
    let mut short_x2 = x2apic(0x200, 1);
    short_x2[1] = 12;
    entries.extend_from_slice(&short_x2[..12]);
    entries.extend_from_slice(&lapic(1, 1));
    entries.extend_from_slice(&ioapic(0xfec1_0000, 12));
    let info = parse(&entries);
    assert_eq!(&info.cpus[..info.n_cpus], &[1]);
    assert_eq!(&info.ioapics[..info.n_ioapics], &[0xfec1_0000]);
}

#[test]
fn a_madt_entry_past_the_table_ends_the_walk() {
    let mut entries = lapic(1, 1).to_vec();
    // Claims 16 bytes; the table has 12 left, then lies other memory.
    let mut cut = x2apic(0x300, 1).to_vec();
    cut.truncate(12);
    entries.extend_from_slice(&cut);
    let info = parse(&entries);
    assert_eq!(&info.cpus[..info.n_cpus], &[1]);
}

/// Memory below 4 GiB, which an RSDT can point at.
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn low_memory(len: usize) -> &'static mut [u8] {
    extern "C" {
        fn mmap(addr: *mut u8, len: usize, prot: i32, flags: i32, fd: i32, off: i64) -> *mut u8;
    }
    // PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, with a hint
    // below 4 GiB (MAP_32BIT is not honoured everywhere).
    for hint in (1u64..64).map(|i| i << 26) {
        let p = unsafe { mmap(hint as *mut u8, len, 3, 0x02 | 0x20, -1, 0) };
        if p as isize != -1 && (p as u64) < 1 << 32 {
            return unsafe { core::slice::from_raw_parts_mut(p, len) };
        }
    }
    panic!("no memory below 4 GiB for the RSDT test")
}

/// ACPI 1.0: a 20-byte RSDP (whatever follows it) and an RSDT.
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[test]
fn an_acpi_1_rsdp_uses_the_rsdt_and_only_its_20_bytes() {
    let low = low_memory(4096);
    let (rsdt, madt) = low.split_at_mut(64);
    let mut entries = vec![0; 44];
    entries.extend_from_slice(&lapic(3, 1));
    let madt = &mut madt[..entries.len()];
    madt.copy_from_slice(&entries);
    let len = madt.len() as u32;
    madt[..4].copy_from_slice(b"APIC");
    madt[4..8].copy_from_slice(&len.to_le_bytes());
    checksum(madt, 9);
    let rsdt = &mut rsdt[..40];
    rsdt[..4].copy_from_slice(b"RSDT");
    rsdt[4..8].copy_from_slice(&40u32.to_le_bytes());
    rsdt[36..40].copy_from_slice(&(madt.as_ptr() as u64 as u32).to_le_bytes());
    checksum(rsdt, 9);
    // Revision 0; the bytes after the 20 are not ACPI 2.0 fields.
    let mut rsdp = [0xeeu8; 36];
    rsdp[..8].copy_from_slice(b"RSD PTR ");
    rsdp[15] = 0;
    rsdp[16..20].copy_from_slice(&(rsdt.as_ptr() as u64 as u32).to_le_bytes());
    checksum(&mut rsdp[..20], 8);
    let info = acpi::init(Some(rsdp.as_ptr() as u64)).expect("valid RSDP");
    assert_eq!(&info.cpus[..info.n_cpus], &[3]);
    assert_eq!(&info.rsdp[..20], &rsdp[..20]);
    assert!(info.rsdp[20..].iter().all(|&b| b == 0));
}

#[test]
fn a_root_table_shorter_than_its_header_gives_no_tables() {
    let mut xsdt = [0u8; 44];
    xsdt[..4].copy_from_slice(b"XSDT");
    xsdt[4..8].copy_from_slice(&20u32.to_le_bytes());
    let mut rsdp = [0u8; 36];
    rsdp[..8].copy_from_slice(b"RSD PTR ");
    rsdp[15] = 2;
    rsdp[20..24].copy_from_slice(&36u32.to_le_bytes());
    rsdp[24..32].copy_from_slice(&(xsdt.as_ptr() as u64).to_le_bytes());
    checksum(&mut rsdp[..20], 8);
    checksum(&mut rsdp, 32);
    assert!(acpi::init(Some(rsdp.as_ptr() as u64)).is_none());
}
