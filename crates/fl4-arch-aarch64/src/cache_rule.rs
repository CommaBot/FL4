//! When user cache maintenance (seL4 `doFlush`) must wait for the serial
//! gate. No hardware access, so the host tests run it
//! (xtask/tests/aarch64_boot.rs).

/// Whether a cache operation inside a transaction must rerun under the
/// serial gate: an invalidation (discarding data cannot be repeated or
/// undone if the transaction fails), and anything on memory outside the
/// kernel window (`in_window` false). That goes through the user mapping
/// itself, with TTBR0 on the transaction's view of the address space:
/// which another core may since have unmapped, or whose tables and ASID
/// it may have freed and given to another address space. A walk of them
/// would fault in the kernel or fill this core's TLB with translations the
/// ASID's next owner then uses. Under the gate the view is current and no
/// invalidation runs alongside.
pub fn needs_gate(invalidate: bool, in_window: bool) -> bool {
    invalidate || !in_window
}
