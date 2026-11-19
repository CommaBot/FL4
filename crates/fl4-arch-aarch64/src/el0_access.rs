//! What EL0 may reach of the per-core system registers that the kernel
//! never context-switches. No hardware access, so the host tests run it
//! (xtask/tests/aarch64_boot.rs).

/// MDSCR_EL1: no debug events, EL0 debug communications channel access
/// (DBGDTR_EL0, DBGDTRRX_EL0, DBGDTRTX_EL0, MDCCSR_EL0) trapped
/// (TDCC, bit 12). The kernel saves none of them, so an untrapped DCC
/// register would be a channel between threads time-sliced on a core.
pub const MDSCR_EL1: u64 = 1 << 12;

/// CPACR_EL1.TTA (bit 28): EL0 and EL1 System register accesses to the
/// trace unit trap. The kernel uses no trace register.
pub const CPACR_TTA: u64 = 1 << 28;
/// CPACR_EL1 for a thread that does not own the FP/SIMD registers: FPEN
/// traps EL0 (not EL1).
pub const CPACR_FP_EL0_TRAP: u64 = CPACR_TTA | (1 << 20);
/// CPACR_EL1 for the thread that owns them: FPEN traps nothing.
pub const CPACR_FP_NONE: u64 = CPACR_TTA | (3 << 20);

/// Whether the core has an EL0-accessible PMU (ID_AA64DFR0_EL1.PMUVer:
/// neither absent nor IMPLEMENTATION DEFINED), so PMUSERENR_EL0 exists.
pub fn has_pmu(dfr0: u64) -> bool {
    let v = (dfr0 >> 8) & 0xf;
    v != 0 && v != 0xf
}

// AMUSERENR_EL0 is left alone: its EN bit resets to 0, and EL1 access to
// it traps to EL3 where firmware keeps the activity monitors for itself
// (CPTR_EL3.TAM, TF-A's default), which EL0 access then does too.
