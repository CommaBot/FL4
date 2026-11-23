//! The x86_64 loader's memory map (x86.rs `memory_map`): the firmware's EFI
//! memory descriptors as Multiboot2 regions, adjacent ones of the same kind
//! merged. Plain functions, so host tests run them (xtask/tests/efi_snp.rs).

use super::snp_map;

const PAGE: u64 = 4096;

fn rd32(b: &[u8], o: usize) -> u32 {
    u32::from_le_bytes(b[o..o + 4].try_into().unwrap())
}

fn rd64(b: &[u8], o: usize) -> u64 {
    u64::from_le_bytes(b[o..o + 8].try_into().unwrap())
}

/// FL4's Multiboot 2 memory type for `EfiUnacceptedMemoryType` (15, UEFI
/// 2.10 table 7.10; 14 is `EfiPersistentMemory`, 16 `EfiMaxMemoryType`): RAM a
/// confidential guest must accept before touching it. Neither usable RAM
/// nor reserved memory, which the kernel would hand out as device memory.
pub const UNACCEPTED: u32 = 0x464c_3410;

/// FL4's Multiboot 2 memory type for `EfiReservedMemoryType` that is
/// write-back memory: firmware's private memory, which the kernel keeps
/// private and out of device memory in a confidential guest, but no
/// firmware data it reads (UEFI calls the type not usable).
pub const PRIVATE_RESERVED: u32 = 0x464c_3411;

/// EFI memory types (UEFI 2.10 table 7.10) the loader looks at by number.
pub const EFI_ACPI_RECLAIM: u32 = 9;
pub const EFI_ACPI_NVS: u32 = 10;
pub const EFI_UNACCEPTED: u32 = 15;

/// Conventional and reclaimable boot-services pages are free. Keep
/// firmware RAM distinguishable from device apertures for encrypted guests.
/// Runtime services, ACPI NVS and persistent memory (5, 6, 10, 14) become
/// ACPI NVS, write-back reserved memory `PRIVATE_RESERVED`; types from
/// `EfiMaxMemoryType` (16) on, unknown, reserved.
pub fn kind(ty: u32, attributes: u64) -> u32 {
    match ty {
        1..=4 | 7 => 1,
        EFI_ACPI_RECLAIM => 3,
        5 | 6 | EFI_ACPI_NVS | 14 => 4,
        0 if attributes & 8 != 0 => PRIVATE_RESERVED,
        EFI_UNACCEPTED => UNACCEPTED,
        _ => 2,
    }
}

/// Whether the loader may read firmware data (ACPI tables) from memory of
/// this EFI type: loader, boot services and conventional memory (1 to 4,
/// 7), ACPI reclaim (9) or ACPI NVS (10). Never reserved memory (0, with
/// or without write-back), runtime services (5, 6), unusable memory, MMIO
/// (11, 12), persistent memory, nor unaccepted memory, which a TD faults
/// on.
pub fn readable(ty: u32) -> bool {
    matches!(ty, 1..=4 | 7 | EFI_ACPI_RECLAIM | EFI_ACPI_NVS)
}

/// The descriptors of `map` (`stride` bytes apart) as (base, bytes, EFI
/// type, attributes), leaving out any `extent` refuses.
pub fn descriptors(map: &[u8], stride: usize) -> impl Iterator<Item = (u64, u64, u32, u64)> + Clone + '_ {
    map.chunks_exact(stride.max(DESCRIPTOR_MIN))
        .filter_map(|d| extent(d).map(|(base, bytes)| (base, bytes, rd32(d, 0), rd64(d, 32))))
}

/// Whether `[addr, addr + len)` (non-empty, not wrapping) lies whole in one
/// of `regions`, given as (base, bytes, whether that region will do).
pub fn within(addr: u64, len: u64, regions: impl IntoIterator<Item = (u64, u64, bool)>) -> bool {
    let Some(end) = addr.checked_add(len) else { return false };
    len != 0 && regions.into_iter().any(|(base, bytes, ok)| ok && base <= addr && base.checked_add(bytes).is_some_and(|e| end <= e))
}

/// EFI_MEMORY_DESCRIPTOR up to its attributes: type at 0, physical start
/// at 8, pages at 24, attributes at 32.
pub const DESCRIPTOR_MIN: usize = 40;

/// The buffer the second GetMemoryMap call gets: the size the sizing call
/// gave and room for 16 more descriptors of at least 48 bytes (a stride
/// the sizing call gives need not be the one that follows). None if that
/// does not fit in a usize.
pub fn capacity(size: usize, stride: usize) -> Option<usize> {
    size.checked_add(stride.max(48).checked_mul(16)?)
}

/// Whether the map GetMemoryMap returned, `size` bytes of descriptors
/// `stride` apart, is whole descriptors inside the `capacity` byte buffer.
pub fn layout_ok(size: usize, stride: usize, capacity: usize) -> bool {
    size <= capacity && stride >= DESCRIPTOR_MIN && size % stride == 0
}

/// A descriptor's physical start and length in bytes. None for a start
/// off a page boundary (EFI requires 4 KiB alignment, and the kernel rounds
/// regions outwards) or a length or end that does not fit in 64 bits.
fn extent(d: &[u8]) -> Option<(u64, u64)> {
    let base = rd64(d, 8);
    let bytes = rd64(d, 24).checked_mul(PAGE)?;
    base.checked_add(bytes)?;
    (base % PAGE == 0).then_some((base, bytes))
}

/// The regions of `map` (descriptors `stride` bytes apart), each passed to
/// `emit` as (base, bytes, kind), adjacent ones of one kind merged. The
/// SEV-SNP CPUID and secrets pages (0 without SNP) must lie whole in a
/// descriptor, and every descriptor holding one gets `PRIVATE_RESERVED`,
/// which a confidential guest's kernel keeps private and out of every
/// capability, and reads no ACPI tables from. The kernel hands out
/// what the map leaves out as device memory, so every descriptor must fit:
/// a length or end past 2^64 is an error, not a wrap (two descriptors
/// whose merge wrapped once added up to a region of 0 bytes).
pub fn regions(
    map: &[u8],
    stride: usize,
    cpuid: u64,
    secrets: u64,
    mut emit: impl FnMut((u64, u64, u32)) -> Result<(), &'static str>,
) -> Result<(), &'static str> {
    if stride < DESCRIPTOR_MIN || map.len() % stride != 0 {
        return Err("invalid EFI memory map");
    }
    let descriptors = map.chunks_exact(stride).map(extent);
    if descriptors.clone().any(|d| d.is_none()) {
        return Err("EFI memory descriptor off a page boundary or past 2^64");
    }
    // The kernel keeps these pages out of user space by the type their
    // descriptors get below: neither may lie in a hole of the map.
    if !snp_map::all_held(descriptors.flatten(), &[cpuid, secrets]) {
        return Err("SEV-SNP CPUID or secrets page is not in the EFI memory map");
    }
    let mut previous: Option<(u64, u64, u32)> = None;
    for d in map.chunks_exact(stride) {
        let (base, bytes) = extent(d).ok_or("invalid EFI memory map")?;
        // Any overlap with either page, not only a whole page.
        let sensitive = [cpuid, secrets]
            .into_iter()
            .any(|page| page != 0 && base < page.saturating_add(PAGE) && page < base + bytes);
        let kind = if sensitive { PRIVATE_RESERVED } else { kind(rd32(d, 0), rd64(d, 32)) };
        if let Some((start, len, ty)) = previous {
            // `start + len` is the end of a descriptor, which fits; so is
            // the merged region's.
            if start.checked_add(len) == Some(base) && ty == kind {
                previous = Some((start, len.checked_add(bytes).ok_or("invalid EFI memory map")?, ty));
                continue;
            }
            emit((start, len, ty))?;
        }
        previous = Some((base, bytes, kind));
    }
    if let Some(last) = previous {
        emit(last)?;
    }
    Ok(())
}
