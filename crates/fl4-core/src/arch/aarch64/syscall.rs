macro_rules! syscall_insn_len {
    () => {
        4
    };
}

macro_rules! trapped_syscall_number {
    ($s:expr, $t:expr, $number:expr) => {
        $t.reg($s, reg::X8)
    };
}

macro_rules! instruction_fault {
    ($code:expr) => {
        ($code >> 26) & 0x3f == 0x20
    };
}
