const N_FRAME: u64 = 17;

const N_GP: u64 = 19;

/// AArch64 always restores every register: nothing to do.
fn post_modify_registers<S: Store>(s: &mut S, t: Tcb) {
    let _ = (s, t);
}

/// FL4 AArch64 TCB invocations: `TCBSetPACKeys` and `TCBSetHighVSpace`.
fn decode_arch<S: Store, A: Arch>(s: &mut S, a: &mut A, lbl: u64, target: Tcb, c: &Ctx) -> KResult<()> {
    if lbl == label::TCBSetPACKeys {
        decode_set_pac_keys(s, a, target, c)
    } else {
        decode_set_high_vspace(s, a, target, c)
    }
}

/// `TCBSetPACKeys(flags, the ten key words)`: the thread's pointer
/// authentication enables and keys. A new key generation makes every core
/// that holds the thread's old keys load the new ones the next time it
/// runs the thread (also this core, if the thread is the caller).
fn decode_set_pac_keys<S: Store, A: Arch>(s: &mut S, a: &mut A, target: Tcb, c: &Ctx) -> KResult<()> {
    if c.length < 11 {
        return truncated();
    }
    let flags = arg(s, c, 0);
    if flags & !fl4_abi::consts::pac_flag::MASK != 0 {
        return invalid_arg(0);
    }
    if flags != 0 && !a.has_pauth() {
        return illegal();
    }
    restart_caller(s);
    let mut i = 0;
    while i < 10 {
        let k = arg(s, c, i + 1);
        s.write(target.0.wrapping_add(tl::PAC_KEYS).wrapping_add(i * 8), k);
        i += 1;
    }
    s.write(target.0.wrapping_add(tl::PAC_FLAGS), flags);
    let epoch = a.next_pac_epoch();
    s.write(target.0.wrapping_add(tl::PAC_EPOCH), epoch);
    Ok(())
}

/// `TCBSetHighVSpace(high_vspace)`: bind a copy of an assigned
/// `ArmHighVSpace` cap (whose ASID still names it) to the thread, or with a
/// null cap unbind it. The
/// thread runs on it from its next address-space switch (the kernel exit,
/// if it is the caller).
fn decode_set_high_vspace<S: Store, A: Arch>(s: &mut S, a: &mut A, target: Tcb, c: &Ctx) -> KResult<()> {
    let src = match extra(c, 0) {
        Some(x) => x,
        None => return truncated(),
    };
    let cap = src.cap(s);
    let new_cap = match cap {
        Cap::Null => Cap::Null,
        Cap::HighVSpace { ptr, mapped: true, asid } => {
            // A copy kept after its ASID pool (or ASID) was deleted names
            // no window: refuse it before the old binding is touched.
            match vspace::find_high_asid(s, asid) {
                Ok(r) if r == ptr => crate::objects::derive_cap(s, src, cap)?,
                _ => return invalid_cap(1),
            }
        }
        _ => return invalid_cap(1),
    };
    restart_caller(s);
    install_tcb_cap(s, a, target, c.slot, tl::SLOT_HIGH_VSPACE, new_cap, src)
}
