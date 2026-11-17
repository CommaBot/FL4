/// AArch64 `syscallMessage`.
pub const SYSCALL_MESSAGE: [u64; 12] = [
    reg::X0,
    reg::X1,
    reg::X2,
    reg::X3,
    reg::X4,
    reg::X5,
    reg::X6,
    reg::X7,
    reg::FAULT_IP,
    reg::SP_EL0,
    reg::ELR_EL1,
    reg::SPSR_EL1,
];

/// AArch64 `exceptionMessage`.
pub const EXCEPTION_MESSAGE: [u64; 3] = [reg::FAULT_IP, reg::SP_EL0, reg::SPSR_EL1];

/// AArch64 `timeoutReplyMessage`.
pub const TIMEOUT_REPLY_MESSAGE: [u64; 34] = [
    reg::FAULT_IP,
    reg::SP_EL0,
    reg::SPSR_EL1,
    reg::X0,
    reg::X1,
    reg::X2,
    reg::X3,
    reg::X4,
    reg::X5,
    reg::X6,
    reg::X7,
    reg::X8,
    reg::X16,
    reg::X17,
    reg::X18,
    reg::X29,
    reg::X30,
    reg::X9,
    reg::X10,
    reg::X11,
    reg::X12,
    reg::X13,
    reg::X14,
    reg::X15,
    reg::X19,
    reg::X20,
    reg::X21,
    reg::X22,
    reg::X23,
    reg::X24,
    reg::X25,
    reg::X26,
    reg::X27,
    reg::X28,
];

macro_rules! unknown_syscall_number_mr {
    () => {
        12
    };
}
