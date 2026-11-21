//! Pure AArch64 Stage-2 IPA geometry and 8-bit VMID table management.
//!
//! No hardware register access, so host tests (`xtask/tests/aarch64_boot.rs`)
//! include and exercise this module directly.
use core::sync::atomic::{AtomicU64, Ordering};

/// Stage-2 IPA width supported for a given physical address width (40, 44, or 48).
pub fn s2_ipa_bits_for_pa(pa_bits: u64) -> u64 {
    if pa_bits <= 42 {
        40
    } else if pa_bits == 44 {
        44
    } else {
        48
    }
}

/// Mask a hardware VGIC LR bitmap (`GICH_EISR0` / `GICH_ELRSR0`) to the
/// ABI-exposed LR count (`lrs <= 16`).
pub fn mask_lr_bitmap(raw: u64, lrs: u64) -> u64 {
    if lrs >= 64 {
        raw
    } else {
        raw & ((1u64 << lrs) - 1)
    }
}

/// 8-bit hardware VMID table (slots 1..=255; slot 0 is reserved for the empty root).
///
/// Each slot holds `(gen << 16) | (asid & 0xffff)` when active in generation `gen`,
/// or 0 when free. Single-ASID revocation releases only that ASID's slot without
/// bumping `gen`; `gen` increments ONLY when the 255-slot allocator wraps around.
pub struct VmidTable {
    gen: AtomicU64,
    slots: [AtomicU64; 256],
    next: AtomicU64,
}

impl VmidTable {
    pub const fn new() -> Self {
        Self {
            gen: AtomicU64::new(1),
            slots: [const { AtomicU64::new(0) }; 256],
            next: AtomicU64::new(1),
        }
    }

    /// Current generation counter.
    pub fn generation(&self) -> u64 {
        self.gen.load(Ordering::SeqCst)
    }

    /// Non-allocating lookup of the 8-bit hardware VMID currently assigned to `asid`.
    pub fn lookup(&self, asid: u64) -> Option<u64> {
        if asid == 0 {
            return Some(0);
        }
        let gen = self.gen.load(Ordering::SeqCst);
        let tag = (gen << 16) | (asid & 0xffff);
        for (v, slot) in self.slots.iter().enumerate().skip(1) {
            if slot.load(Ordering::Acquire) == tag {
                return Some(v as u64);
            }
        }
        None
    }

    /// Reserve the next 8-bit VMID slot for `asid` (caller must hold the serial gate
    /// and have already checked `lookup(asid)` returned `None`).
    ///
    /// Returns `(slot, wrapped)`:
    /// - When `wrapped == false`: `slot` is immediately installed in the current generation.
    /// - When `wrapped == true`: `slot == 1` and the caller MUST bump generation, retire all
    ///   cores, broadcast `TLBI ALLE1IS`, and only then call `install_slot(slot, new_gen, asid)`.
    pub fn alloc_step(&self, asid: u64) -> (u64, bool) {
        let gen = self.gen.load(Ordering::SeqCst);
        let next = self.next.fetch_add(1, Ordering::AcqRel);
        let slot = ((next - 1) % 255) + 1;
        if next > 255 && slot == 1 {
            return (slot, true);
        }
        self.install_slot(slot, gen, asid);
        (slot, false)
    }

    /// Increment and return the new generation counter (only on 8-bit VMID wrap-around).
    pub fn bump_gen(&self) -> u64 {
        self.gen.fetch_add(1, Ordering::SeqCst) + 1
    }

    /// Install `(gen, asid)` into `slot` (1..=255).
    pub fn install_slot(&self, slot: u64, gen: u64, asid: u64) {
        if (1..256).contains(&slot) {
            let tag = (gen << 16) | (asid & 0xffff);
            self.slots[slot as usize].store(tag, Ordering::Release);
        }
    }

    /// Release a single 8-bit VMID slot (1..=255) after its ASID has been retired and flushed.
    pub fn release_slot(&self, slot: u64) {
        if (1..256).contains(&slot) {
            self.slots[slot as usize].store(0, Ordering::Release);
        }
    }
}
