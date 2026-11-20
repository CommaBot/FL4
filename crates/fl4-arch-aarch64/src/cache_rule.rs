//! When user cache maintenance (seL4 `doFlush`) must wait for the serial
//! gate. No hardware access, so the host tests run it
//! (xtask/tests/aarch64_boot.rs).

/// Largest cache maintenance done inside a transaction (bytes), as
/// fl4-store's `MAX_TX_CLEAR`. Larger ranges (a 2 MiB or 1 GiB block) run
/// under the serial gate: a failed commit would otherwise repeat them on
/// every retry, each time with this core counted as active, which holds
/// off every core waiting for the gate.
pub const MAX_TX_CACHE: u64 = 8192;

/// Whether a cache operation inside a transaction must rerun under the
/// serial gate: an invalidation (discarding data cannot be repeated or
/// undone if the transaction fails), anything on memory outside the
/// kernel window (`in_window` false), and anything longer than
/// `MAX_TX_CACHE`. Outside the window it goes through the user mapping
/// itself, with TTBR0 on the transaction's view of the address space:
/// which another core may since have unmapped, or whose tables and ASID
/// it may have freed and given to another address space. A walk of them
/// would fault in the kernel or fill this core's TLB with translations the
/// ASID's next owner then uses. Under the gate the view is current and no
/// invalidation runs alongside.
pub fn needs_gate(invalidate: bool, in_window: bool, len: u64) -> bool {
    invalidate || !in_window || len > MAX_TX_CACHE
}

/// What a cache operation does inside a transaction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InTx {
    /// Clean (or unify) through the kernel window now.
    Run,
    /// The transaction is doomed: its reads since the conflict were 0, so
    /// the range may be made up, and the entry runs again anyway.
    Skip,
    /// Rerun the entry under the serial gate (`needs_gate`).
    Serial,
}

pub fn in_tx(doomed: bool, invalidate: bool, in_window: bool, len: u64) -> InTx {
    if doomed {
        InTx::Skip
    } else if needs_gate(invalidate, in_window, len) {
        InTx::Serial
    } else {
        InTx::Run
    }
}
