const N_FRAME: u64 = 18;

const N_GP: u64 = 2;

/// seL4 x86_64 `Mode_postModifyRegisters`: force a full (iret) restore.
fn post_modify_registers<S: Store>(s: &mut S, t: Tcb) {
    if t != sched::cur_thread(s) {
        t.set_reg(s, reg::ERROR, 0);
    }
}
