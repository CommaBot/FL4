/// AArch64: X2-X5.
pub fn msg_register(i: u64) -> u64 {
    if i == 0 {
        reg::X2
    } else if i == 1 {
        reg::X3
    } else if i == 2 {
        reg::X4
    } else {
        reg::X5
    }
}
