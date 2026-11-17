/// The message registers R10, R8, R9 and R15: register `i` for i < 4. A
/// function rather than an array, so P0 proofs need no u64-to-usize step.
pub fn msg_register(i: u64) -> u64 {
    if i == 0 {
        reg::R10
    } else if i == 1 {
        reg::R8
    } else if i == 2 {
        reg::R9
    } else {
        reg::R15
    }
}
