//! Which EFI memory descriptors hold the SEV-SNP CPUID and secrets pages
//! (x86_mmap.rs `regions`). Plain functions, so host tests run them.

const PAGE: u64 = 4096;

/// Whether the descriptor at `base`, `bytes` long, holds all of the page at
/// `page`. Nothing ending past 2^64 holds a page.
pub fn holds(base: u64, bytes: u64, page: u64) -> bool {
    let (Some(end), Some(page_end)) = (base.checked_add(bytes), page.checked_add(PAGE)) else {
        return false;
    };
    page != 0 && base <= page && page_end <= end
}

/// Whether every nonzero page of `pages` lies in one of `descriptors`
/// (base, bytes). The kernel keeps a page out of user space only through
/// the type its descriptor gets: one in a hole of the map would be handed
/// out as device memory.
pub fn all_held<I: Iterator<Item = (u64, u64)> + Clone>(descriptors: I, pages: &[u64]) -> bool {
    pages.iter().all(|&p| p == 0 || descriptors.clone().any(|(base, bytes)| holds(base, bytes, p)))
}
