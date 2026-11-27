/-
P1 (aarch64): **`ARMVCPUSetTCB`** over the corrected placements (QueueUnbindB), and the VCPU family's `DecGap` with
`Run` the only label left.

* **[P] `VcpuObjA`**: at every `Fr0 ∧ BXI` state of a decode of an invoked `.Vcpu vc` cap (from a `P3Ok` entry),
  `vc` is a VCPU object (`VcObj`: its words in `Ω \ Sg`, its `TCB` / `RUN_CALLER` words `0` or threads). The
  shape of [P] `VcpuW` (words) and [P] `VcpuStA.tcb` (the `TCB` word, at the decode start) stated along the decode,
  plus the `RUN_CALLER` word; source as QueueUnbindB's `VcPl.vcb` (vcpu.rs: `TCB` written by `decode_set_tcb`
  388 with a thread cap's TCB and by `unbind` 306 / `init` with 0; `RUN_CALLER` by `decode_run` 861 with the
  current thread and by `cancel_run` / `complete_run` / `unbind` with 0).
* **`vcpu.decode_set_tcb.dec`**: the restart, `unbind vc` (`vcpu.unbind.ub`, from `VcpuObjA`), `unbind` of the
  target's old VCPU (`VcPl.vcb`), the stall, `vc + TCB := target` (a word of `Ω \ Sg`), `set_bound target vc`
  (`UbF.bnd0`), the VM-root reload (no store write).
* `VcpuGapsC` (`run` only), **`decGap_vcpuC`** (seven labels proved; [P] `VcpuW`, [P] `VcpuStA`, [P] `VcpuObjA`,
  and `B.DelPlace`'s [P] `vc` for the unbinds).

Named premises: **[P] `VcpuObjA`** (new); [P] `VcPl` (QueueUnbindB) through `W7.R.A5.B.DelPlace`.
No existing statement changed.
-/
import Fl4ProofsA64.P1.QueueDecTcbB
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}
variable {A : Type _} {ar : machine.Arch A}

/-- **[P] (a64) The invoked VCPU is a VCPU object along its decode** (module docstring). -/
def VcpuObjA (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop) : Prop :=
  ∀ (Ac Ac' : Set U64) (s0 s : S) (vc : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize),
    EntAt st P3Ok s0 → DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s0 (.Vcpu vc) extra →
    Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s → VcObj st T Ω Sg s vc

set_option hygiene false in
/-- An error leaf with the state unchanged. -/
local macro "errS" : tactic => `(tactic| first
  | exact (WP.spec_ok _).2 (D.err _)
  | (simp only [bind_ok, bind_tc_ok, lift, error.illegal, error.truncated, error.range, error.invalid_arg,
      error.invalid_cap]
     first | exact D.err _ | exact (WP.spec_ok _).2 (D.err _)))

set_option maxHeartbeats 4000000 in
/-- **`ARMVCPUSetTCB`** keeps the invariants (module docstring). -/
theorem vcpu.decode_set_tcb.dec (hA : P0.ArchTotal ar) {s : S} {vc : U64} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Vcpu vc) extra) (Pl : VcPl st T Cs Ω H Sg Rp Scs Nt Z s)
    (hV : ∀ (Ac' : Set U64) (s' : S), Fr0 st T Cs Ω H Sg Scs Z s s' → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s' →
      VcObj st T Ω Sg s' vc) (a : A) :
    vcpu.decode_set_tcb st ar s a vc extra ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vcpu.decode_set_tcb vcpu.set_bound
  rw [eq_of_spec_fd P0.Consts.layout.tcb.VCPU.spec]
  have hl0 : (0#usize).val < extra.val.length := by rw [extra.property]; simp
  refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec extra 0#usize hl0) fun sl hsl => ?_
  simp only [obj.Slot.is_null, bind_ok]
  refine spec_ite (fun _ => by errS) (fun h0 => ?_)
  have hmem : sl ∈ extra.val := hsl ▸ List.getElem_mem hl0
  have hne : sl ≠ 0#u64 := by simpa using h0
  refine WP.spec_bind (D.extra s (WritesIn.refl _ _) sl hmem hne) fun c hc => ?_
  cases c
  all_goals try errS
  rename_i ptr
  have hp : ptr ∈ T := hc.2.1 ptr rfl
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e
  have vU : ∀ s' : S, Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s s' → VcObj st T Ω Sg s' vc := fun s' h' => by
    obtain ⟨Ac', hb'⟩ := h'.bxi; exact hV Ac' s' h'.fr hb'
  refine WP.spec_bind (Cur0.restart D) fun s1 h1 => ?_
  refine WP.spec_bind (vcpu.unbind.ub hA Pl h1 a vc (fun s' h' _ => vU s' h')) ?_
  rintro ⟨s2, a1⟩ F2
  try simp only [uncurry_apply_pair, WP.uncurry'_pair]
  step with vcpu.bound.spec as ⟨ov, eov⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => UbF st T Cs Ω H Sg Rp Scs Nt Z Ac s s2 r.1) ?_ ?_
  · split
    · rename_i hov
      have hov0 : ov ≠ 0#u64 := by simpa using hov
      refine WP.spec_mono (vcpu.unbind.ub hA Pl F2.cur a1 ov fun s' h' b' => ?_) fun r hr => hr
      obtain ⟨Ac', hb'⟩ := h'.bxi
      have e' : L.mem s' (core.num.U64.wrapping_add ptr 3664#u64) = ov := by rw [b' ptr hp, eov]
      have := Pl.vcb Ac' s' ptr h'.fr hb' hp (by rw [e']; exact hov0)
      rw [e'] at this; exact this
    · exact (WP.spec_ok _).2 (UbF.refl F2.cur)
  rintro ⟨s3, a2⟩ F3
  try simp only [uncurry_apply_pair, WP.uncurry'_pair]
  refine WP.spec_bind (smp.remote_tcb_stall.ub hA F3.cur a2 ptr) ?_
  rintro ⟨s4, a3⟩ ⟨F4, -, -⟩
  try simp only [uncurry_apply_pair, WP.uncurry'_pair]
  simp only [lift, bind_ok, L.write_eq]
  have hw := (vU s4 F4.cur).1
  have hx0 := hw vcpu.TCB (by simp [vcpu.TCB]) (by simp [vcpu.TCB])
  obtain ⟨F5, -, -⟩ := UbF.omega (v := ptr) F4.cur hx0.1 hx0.2.1 hx0.2.2
  obtain ⟨F6, -⟩ := UbF.bnd0 (v := vc) F5.cur hp
  refine WP.spec_bind (sched.cur_thread.spec _) fun t _ => ?_
  refine WP.spec_bind (tcb_eq.blk ptr t) fun b _ => ?_
  split
  · refine WP.spec_bind (spec_eq' (P0.vspace.set_vm_root.p0 st ar _ a3 ptr L.total hA)) fun r hr => ?_
    obtain ⟨s8, a4⟩ := r
    have e8 : s8 = _ := set_vm_root_ok_s ar hr.1
    try simp only [WP.uncurry'_pair, uncurry_apply_pair]
    subst e8
    exact (WP.spec_ok _).2 F6.cur.post
  · exact (WP.spec_ok _).2 F6.cur.post

/-- **The VCPU label not yet proved**: `Run`. -/
structure VcpuGapsC (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop) :
    Prop where
  run : ∀ (Ac : Set U64) (s : S) (a : A) (vc len : U64) (call : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize),
    EntAt st P3Ok s → DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Vcpu vc) extra →
    vcpu.decode_run st ar s a vc len call buf ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄

/-- **InvGaps' `vcpu` from `Run` alone**: the other seven labels proved (SetTCB over `B.DelPlace`'s [P] `vc`
and [P] `VcpuObjA`). -/
theorem decGap_vcpuC (hA : P0.ArchTotal ar) {V : U64 → Prop}
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (G : VcpuGapsC st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (W : VcpuW st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (Pl : VcpuStA st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (VO : VcpuObjA st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (Pd : W7.R.A5.B.DelPlace st T Cs Ω H Sg Rp Scs Nt Z V P3Ok) :
    DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .vcpu := by
  intro Ac s a lbl len slot cap blk call don fp buf extra hf D _hslot hE
  cases cap <;> simp [capFam] at hf
  rename_i vc
  have hw : VcWords Ω Sg vc := W Ac s vc extra hE D
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec as ⟨ct, _⟩
  try dsimp only
  unfold vcpu.decode
  split
  · exact vcpu.decode_set_tcb.dec hA D (Pd s hE).vc (fun Ac' s' f b => VO Ac Ac' s s' vc extra hE D f b) a
  split
  · exact vcpu.decode_inject_irq.dec hA D a vc len buf hw
  split
  · exact vcpu.decode_read_reg.dec hA E D hE a vc len call buf
  split
  · exact vcpu.decode_write_reg.dec hA D a vc len buf hw
  split
  · exact vcpu.decode_ack_vppi.dec hA D a vc len buf hw
  split
  · exact vcpu.decode_state_transfer.dec hA Pl D hE hw a len buf true
  split
  · exact vcpu.decode_state_transfer.dec hA Pl D hE hw a len buf false
  split
  · exact G.run Ac s a vc len call buf extra hE D
  · simp only [error.illegal, bind_ok]; exact (WP.spec_ok _).2 (D.err _)

end

end Fl4ProofsA64.P1
