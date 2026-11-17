const N_FRAME: u64 = 17;

const N_GP: u64 = 19;

/// AArch64 always restores every register: nothing to do.
fn post_modify_registers<S: Store>(s: &mut S, t: Tcb) {
    let _ = (s, t);
}
