//! AMD SEV-SNP: the validated CPUID table, RMP transitions and GHCB. The
//! guest memory view both AMD SEV and Intel TDX use is in `crate::cvm`.

pub mod snp;
