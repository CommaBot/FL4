/-
P1 (aarch64, gen 28 audit): **the slot-read field `cap` of every `DelPlaceAt` / `DelGapsAt` (every generation) is
contradictory with any `BXI` state**, so every `DelPlace` / `DelGaps` premise holds of no `P3Ok` with a decode
start, and so does every entry-gap record carrying one (`InvGaps3` … `InvGaps10`). Nothing here is a premise of
anything; these are refutations (as x86's P1/EntryVacuous), kept so that the bundles are not used as if they held.

The field is stated at **every** state `s` with `Fr0 s0 s ∧ BXI s` — not at the states a decode reaches. `Fr0`
allows every cap-slot word (`CapW`, `Cur0W`'s third disjunct) to change, and `BXI` reads no cap slot
(`blk_capw_wr`), so from any `BXI` state `s0` the state with the first cap slot of a TCB of `T` (`t + 0`, a
`TLow` slot) rewritten to the words `(8 << 59, w1)` is an `Fr0 ∧ BXI` state whose slot decodes to
`IrqHandler w1` (`irqH_state`, `decode_irqH`). With `w1 = 2^63` this violates the IRQ bound of every `DelCapOK`
form (`< 128`, and the widened `< 5376` of `W7.R.A5.I.DelCapOK`). Gen 27's post-retype counterexample (handoff
§31) is a special case: no retype, and no reachable state, is needed.

Consequences, machine-checked:
* `DelPlaceAt.cap_false` (QueueDelFin's), `DelGapsAt.cap_false` (QueueDecDel's), and the same for `W7.`,
  `W7.R.`, `W7.R.A5.`, `W7.R.A5.B.`, `W7.R.A5.B.V.` forms: no `DelPlaceAt s0` / `DelGapsAt s0` with `BXI s0`.
* `W7.R.A5.B.V.DelPlaceAt.dec_false`: none at any decode start (`DecPre`, any invoked cap): **gen 27's proposed
  repair (state `DelPlace` only at decode starts whose invoked cap is not an Untyped cap) is false too**, and so
  is the repair "relative to the heap tuple current at the state" (`irqH_state` is uniform in the set tuple, and
  the IRQ bound reads no set).
* `InvGaps3.del_false`, `InvGaps4/5/6/7/7B/8/9/10.place_false`: no record and a `BXI` `EntAt` state together.
* `VcpuObjA.false_at`: [P] `VcpuObjA` (QueueDecVcpuB, `InvGaps7B…10.vcpuObj`) is false at every VCPU decode start
  where [P] `VcpuW` holds, by the same argument (the VCPU's `TCB` word is a `CapW` word: `Ω \ Sg`).

Even an `s0`-only restatement (`∀ x, SlotW x → Slot.cap x s0 ⦃ DelCapOK ⦄`) is false on reachable states while
`SlotW` is the word class `CapW`: [P] `VcpuW` puts a VCPU's words in `Ω \ Sg`, and `ARMVCPUWriteRegisters`
(vcpu.rs:475–512, `reg_set` at `vc + 0x40 + 8·field`, unsanitised for `TTBR0` / `TTBR1`, fields 3 / 4) stores
user words there, so two invocations leave `(8 << 59, 2^63)` at `vc + 0x58` (not mechanised; P1 has no
reachability). The repair needs the slot typing carried along the deletion as a state invariant over the
object-level slots (CNode / TCB slot arrays), not a premise at arbitrary `Fr0 ∧ BXI` states.

No premise; no existing statement changed.
-/
import Fl4ProofsA64.P1.QueueEntryGaps10
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64} {V : U64 → Prop}

namespace DPF

theorem spec_tot {α : Type _} {m : Result α} (h : m ⦃ _ => True ⦄) : ∃ y, m = ok y := by
  revert h; cases m <;> simp [WP.spec_vis, WP.spec_div, WP.spec_ok]

theorem shr_eq (x : U64) (k : I32) (h0 : 0 ≤ k.val) (h : k.val < 64) : x >>> k = ok ⟨x.bv >>> k.toNat⟩ := by
  have hk : k.toNat < 64 := by scalar_tac
  simp only [HShiftRight.hShiftRight, UScalar.shiftRight_IScalar, h0, UScalar.shiftRight, ite_true]
  simp [hk, BitVec.ushiftRight_eq]

/-- The first word of an IRQ-handler cap: tag 8 in bits 59–63. -/
abbrev irqW0 : U64 := 4611686018427387904#u64

/-- An IRQ number no `DelCapOK` form admits (`2^63`). -/
abbrev bigIrq : U64 := 9223372036854775808#u64

/-- `Cap::decode (8 << 59, w1)` is `IrqHandler w1` (capability.rs:160–213, tag 8). -/
theorem decode_irqH (w1 : U64) : capability.Cap.decode irqW0 w1 = ok (.IrqHandler w1) := by
  obtain ⟨p, hp⟩ := spec_tot (Fl4ProofsA64.P0.capability.unpack_ptr.p0 irqW0)
  have ht : irqW0.bv >>> 59 = 8#64 := by first | rfl | decide
  unfold capability.Cap.decode
  simp only [shr_eq _ 59#i32 (by decide) (by decide), hp, bind_ok]
  first
  | rfl
  | (split <;> rename_i heq <;> first
      | rfl
      | (exfalso; have := congrArg UScalar.bv heq; simp [ht] at this; done)
      | (exfalso; simp_all))

/-- A cap slot read: `Cap::decode` of its two words. -/
theorem slot_cap_dec (s : S) (a : U64) :
    obj.Slot.cap st a s = capability.Cap.decode (L.mem s a) (L.mem s (core.num.U64.wrapping_add a 8#u64)) := by
  unfold obj.Slot.cap
  rw [L.read_pair_eq]
  first | rfl | (simp only [bind_ok]; done) | (simp only [bind_ok]; rfl) | simp

theorem wadd0 (x : U64) : core.num.U64.wrapping_add x 0#u64 = x := by
  apply UScalar.eq_of_val_eq; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]

/-- **From any `BXI` state, an `Fr0 ∧ BXI` state with an `IrqHandler w1` cap in a TCB cap slot**: the first cap
slot of a thread of `T` rewritten (two `CapW` words; `BXI` reads no cap slot). -/
theorem irqH_state {s0 : S} (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (w1 : U64) :
    ∃ s x, Fr0 st T Cs Ω H Sg Scs Z s0 s ∧ BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s ∧
      Fl4ProofsA64.P1.SlotW T Ω Sg x ∧ obj.Slot.cap st x s = ok (.IrqHandler w1) := by
  obtain ⟨Q, R, h0⟩ := h.1
  obtain ⟨t, ht⟩ : ∃ t, t ∈ T := ⟨_, h0.curT⟩
  have hpl := h0.tcbs _ ht
  have ha0 : Aligned t := by
    have := field_aligned (K := 0#u64) hpl (by simp) (by simp)
    rwa [wadd0] at this
  have ha8 : Aligned (core.num.U64.wrapping_add t 8#u64) := field_aligned hpl (by simp) (by simp)
  have hx : Fl4ProofsA64.P1.SlotW T Ω Sg t := ⟨ha0, fun o h1 _ => Or.inl ⟨t, ht, o, by omega, rfl⟩⟩
  have c0 : Fl4ProofsA64.P1.CapW T Ω Sg t := by
    have := hx.2 0#u64 (by simp) (by simp)
    rwa [wadd0] at this
  have c8 : Fl4ProofsA64.P1.CapW T Ω Sg (core.num.U64.wrapping_add t 8#u64) := hx.2 8#u64 (by simp) (by simp)
  have hne : (core.num.U64.wrapping_add t 8#u64).val ≠ t.val := by
    have := hpl.fits
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  refine ⟨L.wr (L.wr s0 t irqW0) (core.num.U64.wrapping_add t 8#u64) w1, t, ?_, ?_, hx, ?_⟩
  · refine ((writesIn_wr ha0).trans (writesIn_wr ha8)).mono fun b hb => ?_
    rcases hb with rfl | rfl
    · exact Or.inr (Or.inr (Or.inl c0))
    · exact Or.inr (Or.inr (Or.inl c8))
  · exact (blk_capw_wr (blk_capw_wr h.blk ha0 c0) ha8 c8).bxi
  · rw [slot_cap_dec, L.mem_wr_same ha8, L.mem_wr_ne ha8 ha0 hne, L.mem_wr_same ha0]
    exact decode_irqH w1

theorem bigIrq_ge : ¬ bigIrq.val < 5376 := by
  first | decide | simp | (show ¬ (9223372036854775808 : Nat) < 5376; omega)

theorem bigIrq_ge128 : ¬ bigIrq.val < 128 := fun h => bigIrq_ge (by omega)

/-- The read of an `IrqHandler bigIrq` slot under a spec giving the 128 bound is impossible. -/
theorem irq_read_false {s' : S} {x' : U64} {P : capability.Cap → Prop}
    (hc : obj.Slot.cap st x' s' = ok (.IrqHandler bigIrq)) (h : obj.Slot.cap st x' s' ⦃ c => P c ⦄)
    (hP : ∀ i, P (.IrqHandler i) → i.val < 5376) : False := by
  rw [hc, WP.spec_ok] at h
  exact bigIrq_ge (hP _ h)

end DPF

open DPF

/-! ## The `cap` fields, every generation -/

/-- **QueueDelFin's `DelPlaceAt` holds at no `BXI` decode start** (its `cap`). -/
theorem DelPlaceAt.cap_false {s0 : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨s, x, hf, hb, hx, hc⟩ := irqH_state h bigIrq
  exact irq_read_false hc (P.cap Ac s x hf hb hx)
    fun i hi => Nat.lt_trans (hi.1.2.1 i rfl) (by omega)

/-- **QueueDecDel's `DelGapsAt` holds at no `BXI` decode start** (its `cap`). -/
theorem DelGapsAt.cap_false {A : Type _} {ar : machine.Arch A} {s0 : S}
    (P : DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨s, x, hf, hb, hx, hc⟩ := irqH_state h bigIrq
  exact irq_read_false hc (P.cap Ac s x hf hb hx)
    fun i hi => Nat.lt_trans (hi.1.2.1 i rfl) (by omega)

theorem W7.DelPlaceAt.cap_false {s0 : S} (P : W7.DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨s, x, hf, hb, hx, hc⟩ := irqH_state h bigIrq
  exact irq_read_false hc (P.cap Ac s x hf hb (W7.slotW_to7 hx))
    fun i hi => Nat.lt_trans (hi.1.2.1 i rfl) (by omega)

theorem W7.DelGapsAt.cap_false {A : Type _} {ar : machine.Arch A} {s0 : S}
    (P : W7.DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨s, x, hf, hb, hx, hc⟩ := irqH_state h bigIrq
  exact irq_read_false hc (P.cap Ac s x hf hb (W7.slotW_to7 hx))
    fun i hi => Nat.lt_trans (hi.1.2.1 i rfl) (by omega)

theorem W7.R.DelPlaceAt.cap_false {s0 : S} (P : W7.R.DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨s, x, hf, hb, hx, hc⟩ := irqH_state h bigIrq
  exact irq_read_false hc (P.cap Ac s x hf hb (W7.slotW_to7 hx))
    fun i hi => Nat.lt_trans (hi.1.2.1 i rfl) (by omega)

theorem W7.R.DelGapsAt.cap_false {A : Type _} {ar : machine.Arch A} {s0 : S}
    (P : W7.R.DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨s, x, hf, hb, hx, hc⟩ := irqH_state h bigIrq
  exact irq_read_false hc (P.cap Ac s x hf hb (W7.slotW_to7 hx))
    fun i hi => Nat.lt_trans (hi.1.2.1 i rfl) (by omega)

theorem W7.R.A5.DelPlaceAt.cap_false {s0 : S} (P : W7.R.A5.DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨s, x, hf, hb, hx, hc⟩ := irqH_state h bigIrq
  exact irq_read_false hc (P.cap Ac s x hf hb (W7.slotW_to7 hx))
    fun i hi => Nat.lt_trans (hi.1.2.1 i rfl) (by omega)

theorem W7.R.A5.DelGapsAt.cap_false {A : Type _} {ar : machine.Arch A} {s0 : S}
    (P : W7.R.A5.DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨s, x, hf, hb, hx, hc⟩ := irqH_state h bigIrq
  exact irq_read_false hc (P.cap Ac s x hf hb (W7.slotW_to7 hx))
    fun i hi => Nat.lt_trans (hi.1.2.1 i rfl) (by omega)

theorem W7.R.A5.B.DelPlaceAt.cap_false {s0 : S} (P : W7.R.A5.B.DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨s, x, hf, hb, hx, hc⟩ := irqH_state h bigIrq
  exact irq_read_false hc (P.cap Ac s x hf hb (W7.slotW_to7 hx))
    fun i hi => Nat.lt_trans (hi.1.2.1 i rfl) (by omega)

theorem W7.R.A5.B.DelGapsAt.cap_false {A : Type _} {ar : machine.Arch A} {s0 : S}
    (P : W7.R.A5.B.DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) :
    False := by
  obtain ⟨s, x, hf, hb, hx, hc⟩ := irqH_state h bigIrq
  exact irq_read_false hc (P.cap Ac s x hf hb (W7.slotW_to7 hx))
    fun i hi => Nat.lt_trans (hi.1.2.1 i rfl) (by omega)

/-- **`V.DelPlaceAt` (the newest form, `InvGaps10.place`) holds at no `BXI` state.** -/
theorem W7.R.A5.B.V.DelPlaceAt.cap_false {s0 : S} (P : W7.R.A5.B.V.DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False :=
  W7.R.A5.B.DelPlaceAt.cap_false P.toDelPlaceAt h

theorem W7.R.A5.B.V.DelGapsAt.cap_false {A : Type _} {ar : machine.Arch A} {s0 : S}
    (P : W7.R.A5.B.V.DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) :
    False := by
  obtain ⟨s, x, hf, hb, hx, hc⟩ := irqH_state h bigIrq
  exact irq_read_false hc (P.cap Ac s x hf hb (W7.slotW_to7 hx))
    fun i hi => Nat.lt_trans (hi.1.2.1 i rfl) (by omega)

/-- **Gen 27's proposed repair is false**: `V.DelPlaceAt` at a decode start of *any* invoked cap (an Untyped cap
or not) is contradictory with that decode's `DecPre`. -/
theorem W7.R.A5.B.V.DelPlaceAt.dec_false {s0 : S} {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (P : W7.R.A5.B.V.DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s0 cap extra) : False :=
  P.cap_false D.bxi

/-- `V.DelPlace` holds of no `P3Ok` with a `BXI` `EntAt` state. -/
theorem W7.R.A5.B.V.DelPlace.entAt_false {s0 : S} (P : W7.R.A5.B.V.DelPlace st T Cs Ω H Sg Rp Scs Nt Z V P3Ok)
    (hE : EntAt st P3Ok s0) (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False :=
  (P s0 hE).cap_false h

/-! ## The entry-gap records -/

theorem InvGaps3.del_false {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} {s0 : S}
    (G : InvGaps3 st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (hE : EntAt st P3Ok s0)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False :=
  (G.del s0 hE).cap_false h

theorem InvGaps4.place_false {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} {s0 : S}
    (G : InvGaps4 st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (hE : EntAt st P3Ok s0)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨V, Pd, -⟩ := G.place
  exact (Pd s0 hE).cap_false h

theorem InvGaps5.place_false {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} {s0 : S}
    (G : InvGaps5 st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (hE : EntAt st P3Ok s0)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨V, Pd, -⟩ := G.place
  exact (Pd s0 hE).cap_false h

theorem InvGaps6.place_false {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} {s0 : S}
    (G : InvGaps6 st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (hE : EntAt st P3Ok s0)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨V, Pd, -⟩ := G.place
  exact (Pd s0 hE).cap_false h

theorem InvGaps7.place_false {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} {s0 : S}
    (G : InvGaps7 st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (hE : EntAt st P3Ok s0)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨V, Pd, -⟩ := G.place
  exact (Pd s0 hE).cap_false h

theorem InvGaps7B.place_false {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} {s0 : S}
    (G : InvGaps7B st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (hE : EntAt st P3Ok s0)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨V, Pd, -⟩ := G.place
  exact (Pd s0 hE).cap_false h

theorem InvGaps8.place_false {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} {s0 : S}
    (G : InvGaps8 st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (hE : EntAt st P3Ok s0)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨V, Pd, -⟩ := G.place
  exact (Pd s0 hE).cap_false h

theorem InvGaps9.place_false {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} {s0 : S}
    (G : InvGaps9 st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (hE : EntAt st P3Ok s0)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨V, Pd, -⟩ := G.place
  exact (Pd s0 hE).cap_false h

/-- **`InvGaps10` (gen 27's newest record) holds of no `P3Ok` with a `BXI` `EntAt` state**, so `InvGaps10.gaps`
gives no decode gap (each `DecGap` instance takes `DecPre` and `EntAt`). -/
theorem InvGaps10.place_false {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} {s0 : S}
    (G : InvGaps10 st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (hE : EntAt st P3Ok s0)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨V, Pd, -⟩ := G.place
  exact (Pd s0 hE).cap_false h

/-! ## `VcpuObjA` -/

/-- **[P] `VcpuObjA` is false at every VCPU decode start where [P] `VcpuW` holds**: the VCPU's `TCB` word (an
`Ω \ Sg` word, so `CapW`) rewritten to `1` (no thread: TCBs are 4096-aligned) gives an `Fr0 ∧ BXI` state where
`VcObj` fails. -/
theorem VcpuObjA.false_at (O : VcpuObjA st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (W : VcpuW st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) {s0 : S} {vc : U64}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (hE : EntAt st P3Ok s0)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s0 (.Vcpu vc) extra) : False := by
  obtain ⟨ha, hΩ, hS⟩ := W Ac s0 vc extra hE D 0#u64 (by simp) (by simp)
  have c : Fl4ProofsA64.P1.CapW T Ω Sg (core.num.U64.wrapping_add vc 0#u64) := Or.inr ⟨hΩ, hS⟩
  have hf : Fr0 st T Cs Ω H Sg Scs Z s0 (L.wr s0 (core.num.U64.wrapping_add vc 0#u64) 1#u64) :=
    (writesIn_wr ha).mono fun b e => by subst e; exact Or.inr (Or.inr (Or.inl c))
  have hb : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s0 (core.num.U64.wrapping_add vc 0#u64) 1#u64) :=
    (blk_capw_wr D.bxi.blk ha c).bxi
  obtain ⟨-, hT, -⟩ := O Ac Ac s0 _ vc extra hE D hf hb
  have eT : vcpu.TCB = 0#u64 := by first | rfl | simp [vcpu.TCB] | (unfold vcpu.TCB; rfl)
  rw [eT, L.mem_wr_same ha] at hT
  obtain ⟨Q, R, h0⟩ := D.bxi.1
  rcases hT with e | e
  · exact absurd e (by decide)
  · have := (h0.tcbs _ e).align
    revert this; first | decide | simp | omega

end

end Fl4ProofsA64.P1
