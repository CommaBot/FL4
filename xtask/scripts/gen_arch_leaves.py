#!/usr/bin/env python3
"""Emit the Arch-call leaf trees `AR.<m>` with their `interp` equations (part of P2/ProgGenBase.lean)."""
# method: (arg types, result kind, AV ctor)   kind: V (value only), A (state only), VA (value, state)
ARCH = [
 ("private_device_frame", ["U64"], "V", "b", "Bool"),
 ("dma_ram", ["U64", "U64"], "V", "b", "Bool"),
 ("dma_frame", ["U64", "U64", "Bool"], "A", None, None),
 ("virtualization", [], "V", "u", "U64"),
 ("vcpu_capability", ["U64"], "V", "u", "U64"),
 ("vcpu_barrier", [], "A", None, None),
 ("vcpu_release", ["U64"], "A", None, None),
 ("invalidate_ept", ["U64", "U64"], "A", None, None),
 ("tdx_active", [], "V", "b", "Bool"),
 ("tdx_report", ["U64"] * 9, "VA", "u", "U64"),
 ("tdx_extend_rtmr", ["U64"] * 7, "VA", "u", "U64"),
 ("tdx_get_quote", ["U64", "U64"], "VA", "u", "U64"),
 ("now", [], "VA", "u", "U64"),
 ("set_deadline", ["U64"], "A", None, None),
 ("us_to_ticks", ["U64"], "V", "u", "U64"),
 ("ticks_to_us", ["U64"], "V", "u", "U64"),
 ("max_us", [], "V", "u", "U64"),
 ("kernel_wcet_ticks", [], "V", "u", "U64"),
 ("irq_pending", [], "VA", "b", "Bool"),
 ("take_pending_irq", [], "VA", "u", "U64"),
 ("mask_irq", ["U64", "Bool"], "A", None, None),
 ("ack_irq", ["U64"], "A", None, None),
 ("irq_free", ["U64"], "A", None, None),
 ("set_vspace", ["U64", "U64"], "A", None, None),
 ("invalidate_page", ["U64", "U64"], "A", None, None),
 ("invalidate_asid", ["U64"], "A", None, None),
 ("invalidate_page_structures", ["U64"], "A", None, None),
 ("ioapic_map", ["U64"] * 5, "VA", "b", "Bool"),
 ("ioapic_map_remapped", ["U64"] * 6, "VA", "b", "Bool"),
 ("num_ioapics", [], "V", "u", "U64"),
 ("ioapic_pins", ["U64"], "V", "u", "U64"),
 ("port_in", ["U64", "U64"], "VA", "u", "U64"),
 ("port_out", ["U64", "U64", "U64"], "A", None, None),
 ("fpu_flush", ["U64"], "A", None, None),
 ("fpu_sanitise", ["U64"], "A", None, None),
 ("fpu_reload", ["U64"], "A", None, None),
 ("fpu_release", ["U64"], "A", None, None),
 ("remote_stall", ["U64"], "A", None, None),
 ("send_reschedule", ["U64"], "A", None, None),
 ("putc", ["U64"], "A", None, None),
 ("get_char", [], "VA", "u", "U64"),
 ("halt", [], "A", None, None),
]
KIND = {m: k for (m, _, k, _, _) in ARCH}

# The AArch64 extraction's `machine.Arch` (Fl4CoreA64/Types.lean): the same methods, `send_reschedule`
# taking a 128-bit core mask, and the AArch64 ones (cache, GIC, stage-2, VCPU, PAC, high VSpace).
ARCH_A64 = [e if e[0] != "send_reschedule" else ("send_reschedule", ["U128"], "A", None, None)
            for e in ARCH[:-3]] + [
 ("cache_op", ["U64"] * 6, "A", None, None),
 ("hw_access_flag", [], "V", "b", "Bool"),
 ("max_spi", [], "V", "u", "U64"),
 ("configure_irq", ["U64", "Bool", "U64"], "A", None, None),
 ("msi_map", ["U64"] * 4, "VA", "u", "U64"),
 ("s2_ipa_bits", [], "V", "u", "U64"),
 ("set_stage2_vspace", ["U64", "U64"], "A", None, None),
 ("invalidate_stage2_page", ["U64", "U64"], "A", None, None),
 ("invalidate_stage2_vmid", ["U64"], "A", None, None),
 ("vcpu_flush", ["U64"], "A", None, None),
 ("vcpu_flush_state", ["U64", "U64"], "A", None, None),
 ("vcpu_vgic_vtr", [], "V", "u", "U64"),
 ("vcpu_gic_version", [], "V", "u", "U64"),
 ("vcpu_midr", [], "V", "u", "U64"),
 ("has_pauth", [], "V", "b", "Bool"),
 ("next_pac_epoch", [], "VA", "u", "U64"),
 ("kernel_ttbr1_entry", ["U64", "U64"], "V", "u", "U64"),
 ("set_high_vspace", ["U64", "U64"], "A", None, None),
 ("invalidate_high_page", ["U64"], "A", None, None),
 ("invalidate_high_vspace", ["U64"], "A", None, None),
] + ARCH[-3:]
assert [e[0] for e in ARCH[-3:]] == ["putc", "get_char", "halt"]

def emit(arch=None):
    out = []
    for (m, tys, kind, ctor, vty) in (ARCH if arch is None else arch):
        xs = [f"x{i}" for i in range(len(tys))]
        binders = " ".join(f"({x} : {t})" for x, t in zip(xs, tys))
        args = " ".join(xs)
        op = f"(.{m} {args})" if xs else f".{m}"
        if kind == "A":
            out.append(f"def AR.{m} {binders} : SProg Unit := .arch {op} fun _ => .ret ()")
            rhs = f"ar.{m} a {args} >>= fun a' => ok ((), s, a')"
        else:
            out.append(f"def AR.{m} {binders} : SProg {vty} := .arch {op} fun v =>\n"
                       f"  match v with\n  | .{ctor} x => .ret x\n  | _ => .err .panic")
            if kind == "V":
                rhs = f"ar.{m} a {args} >>= fun v => ok (v, s, a)"
            else:
                rhs = f"ar.{m} a {args} >>= fun r => ok (r.1, s, r.2)"
        call = f"ar.{m} a {args}".rstrip()
        out.append(f"@[reif_simps] theorem AR.{m}_eq {binders} (s : S) (a : A) :\n"
                   f"    interp st ar (AR.{m} {args}) s a = ({rhs.replace(f'ar.{m} a {args}', call, 1)}) := by\n"
                   f"  rcases result_trichotomy ({call}) with {'⟨⟨r, r2⟩, e⟩' if kind == 'VA' else '⟨r, e⟩'} | ⟨er, e⟩ | e <;>\n"
                   f"    simp [AR.{m}, interp, callArch, e]")
        out.append(f"@[reif_nz] theorem AR.{m}_nz {binders} : NoZero (AR.{m} {args}) := by\n"
                   f"  intro v; {'trivial' if kind == 'A' else 'cases v <;> trivial'}")
        out.append("")
    return "\n".join(out)

if __name__ == "__main__":
    import sys
    print(emit(ARCH_A64 if sys.argv[1:] == ["--arch", "aarch64"] else None))
