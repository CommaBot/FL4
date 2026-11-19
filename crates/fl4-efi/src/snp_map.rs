//! Which EFI memory descriptors hold the SEV-SNP CPUID and secrets pages
//! (x86.rs `memory_map`). Plain functions, so host tests run them.

/// Whether the descriptor at `base`, `bytes` long, holds the page at `page`.
pub fn holds(base: u64, bytes: u64, page: u64) -> bool {
    page != 0 && base <= page && page - base < bytes
}

/// Whether every nonzero page of `pages` lies in one of `descriptors`
/// (base, bytes). The kernel keeps a page out of user space only through
/// the type its descriptor gets: one in a hole of the map would be handed
/// out as device memory.
pub fn all_held<I: Iterator<Item = (u64, u64)> + Clone>(descriptors: I, pages: &[u64]) -> bool {
    pages.iter().all(|&p| p == 0 || descriptors.clone().any(|(base, bytes)| holds(base, bytes, p)))
}
