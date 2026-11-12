//! Kernel exceptions: seL4's `exception_t` together with the global
//! `current_syscall_error`, `current_fault` and `current_lookup_fault`,
//! carried as values instead.

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum LookupFault {
    InvalidRoot,
    MissingCapability { bits_left: u64 },
    DepthMismatch { bits_found: u64, bits_left: u64 },
    GuardMismatch { guard_found: u64, bits_left: u64, guard_size: u64 },
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SysError {
    InvalidArgument { arg: u64 },
    InvalidCapability { arg: u64 },
    IllegalOperation,
    RangeError { min: u64, max: u64 },
    AlignmentError,
    FailedLookup { source: bool, lf: LookupFault },
    TruncatedMessage,
    DeleteFirst,
    RevokeFirst,
    NotEnoughMemory { bytes: u64 },
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Fault {
    Null,
    Cap { addr: u64, in_recv: bool, lf: LookupFault },
    UnknownSyscall { number: u64 },
    UserException { number: u64, code: u64 },
    Debug { reason: u64, addr: u64, bp: u64 },
    Timeout { badge: u64 },
    VmFault { addr: u64, fsr: u64, instruction: bool },
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Exc {
    Fault(Fault),
    Lookup(LookupFault),
    Sys(SysError),
    Preempted,
}

pub type KResult<T> = Result<T, Exc>;

pub fn sys<T>(e: SysError) -> KResult<T> {
    Err(Exc::Sys(e))
}

pub fn illegal<T>() -> KResult<T> {
    Err(Exc::Sys(SysError::IllegalOperation))
}

pub fn truncated<T>() -> KResult<T> {
    Err(Exc::Sys(SysError::TruncatedMessage))
}

pub fn invalid_arg<T>(arg: u64) -> KResult<T> {
    Err(Exc::Sys(SysError::InvalidArgument { arg }))
}

pub fn invalid_cap<T>(arg: u64) -> KResult<T> {
    Err(Exc::Sys(SysError::InvalidCapability { arg }))
}

pub fn range<T>(min: u64, max: u64) -> KResult<T> {
    Err(Exc::Sys(SysError::RangeError { min, max }))
}

impl SysError {
    /// `seL4_Error` code.
    pub fn code(self) -> u64 {
        use fl4_abi::consts::error as e;
        match self {
            SysError::InvalidArgument { .. } => e::InvalidArgument,
            SysError::InvalidCapability { .. } => e::InvalidCapability,
            SysError::IllegalOperation => e::IllegalOperation,
            SysError::RangeError { .. } => e::RangeError,
            SysError::AlignmentError => e::AlignmentError,
            SysError::FailedLookup { .. } => e::FailedLookup,
            SysError::TruncatedMessage => e::TruncatedMessage,
            SysError::DeleteFirst => e::DeleteFirst,
            SysError::RevokeFirst => e::RevokeFirst,
            SysError::NotEnoughMemory { .. } => e::NotEnoughMemory,
        }
    }
}

impl LookupFault {
    pub fn type_code(self) -> u64 {
        use fl4_abi::consts::lookup as l;
        match self {
            LookupFault::InvalidRoot => l::InvalidRoot,
            LookupFault::MissingCapability { .. } => l::MissingCapability,
            LookupFault::DepthMismatch { .. } => l::DepthMismatch,
            LookupFault::GuardMismatch { .. } => l::GuardMismatch,
        }
    }

    pub fn encode(self) -> (u64, u64, u64) {
        match self {
            LookupFault::InvalidRoot => (1, 0, 0),
            LookupFault::MissingCapability { bits_left } => (2, bits_left, 0),
            LookupFault::DepthMismatch { bits_found, bits_left } => (3, bits_found, bits_left),
            LookupFault::GuardMismatch { guard_found, bits_left, guard_size } => {
                (4, guard_found, (bits_left << 8) | guard_size)
            }
        }
    }

    pub fn decode(t: u64, w0: u64, w1: u64) -> LookupFault {
        if t == 2 {
            LookupFault::MissingCapability { bits_left: w0 }
        } else if t == 3 {
            LookupFault::DepthMismatch { bits_found: w0, bits_left: w1 }
        } else if t == 4 {
            LookupFault::GuardMismatch { guard_found: w0, bits_left: w1 >> 8, guard_size: w1 & 0xff }
        } else {
            LookupFault::InvalidRoot
        }
    }
}
