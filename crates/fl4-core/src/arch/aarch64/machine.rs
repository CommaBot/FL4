macro_rules! arch_machine_methods {
    () => {
        /// AArch64 cache maintenance (seL4 `doFlush`): operation `op`
        /// (`vspace::CACHE_*`) over `len` bytes at `vaddr` in the address space
        /// `root` with ASID `asid`, physically at `paddr`.
        fn cache_op(&mut self, op: u64, root: u64, asid: u64, vaddr: u64, len: u64, paddr: u64);
        /// AArch64: hardware sets access flags (TCR_EL1.HA), so a cleared flag
        /// does not fault.
        fn hw_access_flag(&self) -> bool;
        /// AArch64: the largest SPI the interrupt controller has.
        fn max_spi(&self) -> u64;
        /// AArch64: configure interrupt `irq` as edge (true) or level triggered
        /// and, for an SPI, route it to `core`.
        fn configure_irq(&mut self, irq: u64, edge: bool, core: u64);
    };
}
