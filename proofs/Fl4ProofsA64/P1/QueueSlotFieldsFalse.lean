/-
P1 (aarch64, gen 29 audit): **the other `Fr0 ∧ BXI`-quantified slot / TCB-word fields refuted**, by gen 28's
argument (QueueDelPlaceFalse): each is stated at **every** `s` with `Fr0 s0 s ∧ BXI s`, and reads a word that
`Fr0` lets change while no `BXI` conjunct reads it. From any `BXI` state one write gives an `Fr0 ∧ BXI` state
where the field fails. Nothing here is a premise; these are refutations.

* `next` / `prev` (every `DelPlaceAt` generation; `next` of every `DelGapsAt` generation): the `NEXT` / `PREV`
  word of a TCB's first cap slot (`t + 24` / `t + 16`, `TLow`, so `CapW`) rewritten to `1`; the read returns `1`
  (`sext48 1 = 1`), neither `0` nor aligned, so no `SlotW` (`next_state`, `prev_state`).
* `irq` (every `DelPlaceAt` generation): the first word of IRQ 0's handler slot (`ks + 43232`, in `Ω` by
  `SgOK.ksΩ`, outside `Sg`: `CapW`, `irq_slotW`) rewritten to `7 << 59`, which decodes to `IrqControl`, neither
  `Null` nor a notification cap (`irq_state`).
* `frm` (`W7.R.A5.DelPlaceAt`, `W7.R.A5.B.DelPlaceAt`, and the `frm` of `A5.` / `B.` / `V.DelGapsAt`): a TCB
  cap slot rewritten to `(13 << 59 | 1 << 53, 2^48 + 2^47)`, which decodes to a mapped Stage-1 frame cap with
  ASID 1 at `0xffff_8000_0000_0000` (sign-extended), neither a user address nor in the high window: not
  `FrMapOK` (`frm_state`).
* `vco` (`W7.R.A5.B.V.DelPlaceAt`): a TCB cap slot's first word rewritten to `22 << 59 | 1`, which decodes to
  `Vcpu 1`; `VcCap` at that same state asks `VcObj _ 1`, whose `VcWords` asks `1` aligned (`vco_state`).
* `VcPl.vcb` / `VcPl.rcv` (QueueUnbindB, `B.DelPlaceAt.vc`) and `TcbPlace8.rcv` / `TcbPlace9.rcv`: a thread's
  `BOUND_VCPU` (`t + 3664`) / `RUN_VCPU` (`t + 3672`) word — a `KW` word (TCB field, offset ≥ 192), so `Cur0W`;
  `blk_vf`: no `BXI` conjunct reads it — rewritten to `1`, nonzero and not aligned, so neither `VcObj 1` nor
  `VcWords 1` (`vf_state`). The two `TcbPlace` forms are stated at `EntAt` decode starts `s0`, so they are
  refuted together with any `BXI` `EntAt` state.

So every record built on them (`InvGaps3` … `InvGaps10`, through `place` / `del` / `tcb8` / `tcb9`) was already
refuted (QueueDelPlaceFalse); these add, per field, that no single one of these fields is true as stated, so no
repair that keeps any of them at every `Fr0 ∧ BXI` state is sound.

Checked to be true, not refuted: none of the listed fields. `VsDelAt.ptw` / `elw` / `ptslot` ([J],
QueueDelVs5) are not mechanised here: their walks start at roots read from the ASID table (kernel-state words
`ks + …`, `CapW` by `SgOK.ksΩ`) and pools / page-table words (`Ω \ Sg`, `CapW`), so they are false by the same
argument once a walk's root or entry is rewritten to a table outside `V` (`VsOK V` puts `V ⊆ Ω \ Sg`, so the
entry can point into a TCB); the mechanisation needs a run of `find_asid_raw` and the walk loop on a concrete
store and is left (handoff §33).

No premise; no existing statement changed.
-/
import Fl4ProofsA64.P1.QueueDelPlaceFalse
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64} {V : U64 → Prop}

namespace SFF

/-! ## Concrete words -/

theorem unpack_vcpu1 : capability.unpack_ptr 12682136550675316737#u64 = ok 1#u64 := by
  first
  | rfl
  | (unfold capability.unpack_ptr; simp only [lift, bind_ok, capability.PTR_MASK]; rfl)
  | (unfold capability.unpack_ptr; simp only [lift, bind_ok, capability.PTR_MASK]; decide)

theorem sext48_one : obj.sext48 1#u64 = ok 1#u64 := by
  first
  | rfl
  | (unfold obj.sext48; simp only [lift, bind_ok, obj.MDB_PTR_MASK]; rfl)
  | (unfold obj.sext48; simp only [lift, bind_ok, obj.MDB_PTR_MASK]; decide)

/-- `Cap::decode (22 << 59 | 1, w1)` is `Vcpu 1` (capability.rs:160–213, tag 22). -/
theorem decode_vcpu1 (w1 : U64) : capability.Cap.decode 12682136550675316737#u64 w1 = ok (.Vcpu 1#u64) := by
  have ht : (12682136550675316737#u64 : U64).bv >>> 59 = 22#64 := by first | rfl | decide
  unfold capability.Cap.decode
  simp only [DPF.shr_eq _ 59#i32 (by decide) (by decide), unpack_vcpu1, bind_ok]
  first
  | rfl
  | (split <;> rename_i heq <;> first
      | rfl
      | (exfalso; have := congrArg UScalar.bv heq; simp [ht] at this; done)
      | (exfalso; simp_all))

/-- `Cap::decode (7 << 59, w1)` is `IrqControl` (tag 7). -/
theorem decode_ictl (w1 : U64) : capability.Cap.decode 4035225266123964416#u64 w1 = ok .IrqControl := by
  obtain ⟨p, hp⟩ := DPF.spec_tot (Fl4ProofsA64.P0.capability.unpack_ptr.p0 4035225266123964416#u64)
  have ht : (4035225266123964416#u64 : U64).bv >>> 59 = 7#64 := by first | rfl | decide
  unfold capability.Cap.decode
  simp only [DPF.shr_eq _ 59#i32 (by decide) (by decide), hp, bind_ok]
  first
  | rfl
  | (split <;> rename_i heq <;> first
      | rfl
      | (exfalso; have := congrArg UScalar.bv heq; simp [ht] at this; done)
      | (exfalso; simp_all))

/-- The frame address `0xffff_8000_0000_0000`. -/
abbrev badVa : U64 := 18446603336221196288#u64

theorem shr_u64_eq (x i : U64) (h : i.val < 64) : x >>> i = ok ⟨x.bv >>> i.val⟩ := by
  simp only [HShiftRight.hShiftRight, UScalar.shiftRight_UScalar, UScalar.shiftRight]
  simp [h, BitVec.ushiftRight_eq]

theorem shl_eq (x : U64) (k : I32) (h0 : 0 ≤ k.val) (h : k.val < 64) : x <<< k = ok ⟨x.bv <<< k.toNat⟩ := by
  have hk : k.toNat < 64 := by scalar_tac
  simp only [HShiftLeft.hShiftLeft, UScalar.shiftLeft_IScalar, h0, UScalar.shiftLeft, ite_true]
  simp [hk, BitVec.shiftLeft_eq]

theorem up0 : capability.unpack_ptr 7502996979199246336#u64 = ok 0#u64 := by
  unfold capability.unpack_ptr; simp only [lift, bind_ok, capability.PTR_MASK]; rfl

theorem upW1 : capability.unpack_ptr 422212465065984#u64 = ok 18446603336221196288#u64 := by
  unfold capability.unpack_ptr; simp only [lift, bind_ok, capability.PTR_MASK]; rfl

theorem bitT (n : U64) (b : Bool) (hn : (n &&& 63#u64).val < 64) (w : U64)
    (hb : ((⟨w.bv >>> (n &&& 63#u64).val⟩ : U64) &&& 1#u64 != 0#u64) = b) : capability.bit w n = ok b := by
  unfold capability.bit
  simp only [lift, bind_ok]
  rw [shr_u64_eq _ _ hn]
  simp only [bind_ok, hb]

theorem bit53 : capability.bit 7502996979199246336#u64 53#u64 = ok true := bitT _ _ (by first | decide | rfl) _ (by rfl)
theorem bit52 : capability.bit 7502996979199246336#u64 52#u64 = ok false := bitT _ _ (by first | decide | rfl) _ (by rfl)
theorem bit58 : capability.bit 7502996979199246336#u64 58#u64 = ok false := bitT _ _ (by first | decide | rfl) _ (by rfl)

theorem asid1 : capability.unpack_asid 7502996979199246336#u64 54#u64 422212465065984#u64 = ok 1#u64 := by
  unfold capability.unpack_asid
  simp only [lift, bind_ok]
  rw [shr_u64_eq _ _ (by decide)]
  simp only [bind_ok, shl_eq _ 16#i32 (by decide) (by decide), DPF.shr_eq _ 48#i32 (by decide) (by decide)]
  rfl

theorem fc_small (c : U64) (h1 : c ≠ 1#u64) (h2 : c ≠ 2#u64) : capability.FrameSize.from_code c = ok .Small := by
  unfold capability.FrameSize.from_code; simp [h1, h2]

/-- `Cap::decode (13 << 59 | 1 << 53, 2^48 + 2^47)`: a mapped (bit 53), non-EPT (bit 58 clear), non-device
small frame cap, ASID `(w1 >> 48) = 1`, address `unpack_ptr w1 = 0xffff_8000_0000_0000` (tag 13). -/
theorem decode_frm : capability.Cap.decode 7502996979199246336#u64 422212465065984#u64 =
    ok (.Frame 0#u64 .Small 0#u64 false true false 1#u64 badVa) := by
  have ht : (7502996979199246336#u64 : U64).bv >>> 59 = 13#64 := by first | rfl | decide
  unfold capability.Cap.decode
  simp only [DPF.shr_eq _ 59#i32 (by decide) (by decide), up0, bind_ok]
  split <;> rename_i heq
  all_goals first
    | (exfalso; have := congrArg UScalar.bv heq; simp [ht] at this; done)
    | (simp only [DPF.shr_eq _ 48#i32 (by decide) (by decide),
        DPF.shr_eq _ 50#i32 (by decide) (by decide), lift, bind_ok, bit52, bit53, bit58, asid1,
        upW1, Bool.false_eq_true, ↓reduceIte]
       rw [fc_small _ (by first | decide | (intro h; cases h)) (by first | decide | (intro h; cases h))]
       simp only [bind_ok]
       rfl)
    | (exfalso; simp_all)

theorem badVa_not : ¬ HiOK badVa := by
  unfold HiOK InWin
  first
  | decide
  | simp [fl4_abi.consts.HIGH_VSPACE_BASE]
  | (simp only [fl4_abi.consts.HIGH_VSPACE_BASE]; omega)

theorem one_not_aligned : ¬ Aligned 1#u64 := by
  unfold Aligned; first | decide | simp

theorem wadd0' (x : U64) : core.num.U64.wrapping_add x 0#u64 = x := DPF.wadd0 x

/-! ## One-write states -/

/-- **From any `BXI` state, one aligned `CapW` write gives an `Fr0 ∧ BXI` state.** -/
theorem capw_state {s0 : S} (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) {b : U64} (ha : Aligned b)
    (hc : CapW T Ω Sg b) (v : U64) :
    Fr0 st T Cs Ω H Sg Scs Z s0 (L.wr s0 b v) ∧ BXI st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s0 b v) :=
  ⟨(writesIn_wr ha).mono fun b' e => by subst e; exact Or.inr (Or.inr (Or.inl hc)),
    (blk_capw_wr h.blk ha hc).bxi⟩

/-- A thread of `T`, its first cap slot (`SlotW`), and its low words (`TLow`, so `CapW`). -/
theorem tcb_slot {s0 : S} (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) :
    ∃ t ∈ T, TcbAddr t ∧ Aligned t ∧ SlotW T Ω Sg t ∧
      ∀ K : U64, K.val < 192 → K.val % 8 = 0 →
        Aligned (core.num.U64.wrapping_add t K) ∧ CapW T Ω Sg (core.num.U64.wrapping_add t K) := by
  obtain ⟨Q, R, h0⟩ := h.1
  obtain ⟨t, ht⟩ : ∃ t, t ∈ T := ⟨_, h0.curT⟩
  have hpl := h0.tcbs _ ht
  have ha0 : Aligned t := by
    have := field_aligned (K := 0#u64) hpl (by simp) (by simp)
    rwa [wadd0'] at this
  refine ⟨t, ht, hpl, ha0, ⟨ha0, fun o h1 _ => Or.inl ⟨t, ht, o, by omega, rfl⟩⟩, fun K h1 h2 =>
    ⟨field_aligned hpl (by omega) h2, Or.inl ⟨t, ht, K, h1, rfl⟩⟩⟩

theorem tcb_wval {t K : U64} (hpl : TcbAddr t) (hK : K.val < 4096) :
    (core.num.U64.wrapping_add t K).val = t.val + K.val := by
  have := hpl.fits
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega

/-- **`next_state`**: a cap slot whose `NEXT` read returns `1`. -/
theorem next_state {s0 : S} (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) :
    ∃ s x, Fr0 st T Cs Ω H Sg Scs Z s0 s ∧ BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s ∧ SlotW T Ω Sg x ∧
      obj.Slot.next st x s = ok 1#u64 := by
  obtain ⟨t, ht, hpl, ha0, hx, hw⟩ := tcb_slot h
  obtain ⟨ha, hc⟩ := hw 24#u64 (by simp) (by simp)
  obtain ⟨hf, hb⟩ := capw_state h ha hc 1#u64
  refine ⟨_, t, hf, hb, hx, ?_⟩
  unfold obj.Slot.next obj.Slot.next_word
  simp only [lift, bind_ok, cte_next, L.read_eq, L.mem_wr_same ha, sext48_one]

/-- **`prev_state`**: a cap slot whose `PREV` read returns `1`. -/
theorem prev_state {s0 : S} (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) :
    ∃ s x, Fr0 st T Cs Ω H Sg Scs Z s0 s ∧ BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s ∧ SlotW T Ω Sg x ∧
      obj.Slot.prev st x s = ok 1#u64 := by
  obtain ⟨t, ht, hpl, ha0, hx, hw⟩ := tcb_slot h
  obtain ⟨ha, hc⟩ := hw 16#u64 (by simp) (by simp)
  obtain ⟨hf, hb⟩ := capw_state h ha hc 1#u64
  refine ⟨_, t, hf, hb, hx, ?_⟩
  unfold obj.Slot.prev
  simp only [lift, bind_ok, cte_prev, L.read_eq, L.mem_wr_same ha]

/-- **`vco_state`**: a cap slot holding `Vcpu 1`. -/
theorem vco_state {s0 : S} (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) :
    ∃ s x, Fr0 st T Cs Ω H Sg Scs Z s0 s ∧ BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s ∧ SlotW T Ω Sg x ∧
      obj.Slot.cap st x s = ok (.Vcpu 1#u64) := by
  obtain ⟨t, ht, hpl, ha0, hx, hw⟩ := tcb_slot h
  have hc : CapW T Ω Sg t := by have := (hw 0#u64 (by simp) (by simp)).2; rwa [wadd0'] at this
  obtain ⟨hf, hb⟩ := capw_state h ha0 hc 12682136550675316737#u64
  refine ⟨_, t, hf, hb, hx, ?_⟩
  have ha8 := (hw 8#u64 (by simp) (by simp)).1
  rw [DPF.slot_cap_dec, L.mem_wr_same ha0]
  exact decode_vcpu1 _

/-- **`frm_state`**: a cap slot holding a mapped frame cap at a non-user, non-window address. -/
theorem frm_state {s0 : S} (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) :
    ∃ s x, Fr0 st T Cs Ω H Sg Scs Z s0 s ∧ BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s ∧ SlotW T Ω Sg x ∧
      obj.Slot.cap st x s = ok (.Frame 0#u64 .Small 0#u64 false true false 1#u64 badVa) := by
  obtain ⟨t, ht, hpl, ha0, hx, hw⟩ := tcb_slot h
  have hc : CapW T Ω Sg t := by have := (hw 0#u64 (by simp) (by simp)).2; rwa [wadd0'] at this
  obtain ⟨ha8, hc8⟩ := hw 8#u64 (by simp) (by simp)
  obtain ⟨hf1, hb1⟩ := capw_state h ha0 hc 7502996979199246336#u64
  obtain ⟨hf2, hb2⟩ := capw_state hb1 ha8 hc8 422212465065984#u64
  have hne : (core.num.U64.wrapping_add t 8#u64).val ≠ t.val := by
    rw [tcb_wval hpl (by simp)]; simp
  refine ⟨_, t, (hf1.trans hf2).mono fun b hb => hb.elim id (Cur0W.ksb hf1.1), hb2, hx, ?_⟩
  rw [DPF.slot_cap_dec, L.mem_wr_same ha8, L.mem_wr_ne ha8 ha0 hne, L.mem_wr_same ha0]
  exact decode_frm

/-- **`irq_state`**: IRQ 0's handler slot holding `IrqControl`. -/
theorem irq_state {s0 : S} (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) :
    ∃ s, Fr0 st T Cs Ω H Sg Scs Z s0 s ∧ BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s ∧
      obj.Slot.cap st (irqSlotA (L.ksb s) 0#u64) s = ok .IrqControl := by
  have hW := irq_slotW h (i := 0#u64) (by simp)
  have hc : CapW T Ω Sg (irqSlotA (L.ksb s0) 0#u64) := by
    have := hW.2 0#u64 (by simp) (by simp); rwa [wadd0'] at this
  obtain ⟨hf, hb⟩ := capw_state h hW.1 hc 4035225266123964416#u64
  refine ⟨_, hf, hb, ?_⟩
  rw [L.ksb_wr, DPF.slot_cap_dec, L.mem_wr_same hW.1]
  exact decode_ictl _

/-- **`vf_state`**: a thread's `BOUND_VCPU` (`K = 3664`) or `RUN_VCPU` (`K = 3672`) word rewritten to `1`. -/
theorem vf_state {s0 : S} (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) {K : U64} (hK : K.val = 3664 ∨ K.val = 3672) :
    ∃ s t, t ∈ T ∧ Fr0 st T Cs Ω H Sg Scs Z s0 s ∧ BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s ∧
      L.mem s (core.num.U64.wrapping_add t K) = 1#u64 := by
  obtain ⟨Q, R, h0⟩ := h.1
  obtain ⟨t, ht⟩ : ∃ t, t ∈ T := ⟨_, h0.curT⟩
  have hpl := h0.tcbs _ ht
  have ha := field_aligned (K := K) hpl (by omega) (by omega)
  refine ⟨_, t, ht, (writesIn_wr ha).mono fun b e => ?_, (blk_vf (v := 1#u64) h.blk ht hK).bxi,
    L.mem_wr_same ha⟩
  subst e
  exact Or.inl (kw_field ht (by omega) (by omega) ⟨by omega, by omega⟩)

end SFF

open SFF

/-! ## `next` / `prev` -/

private theorem one_bad {P : U64 → Prop} (hP : ∀ n, P n → Aligned n) : ¬ (1#u64 = 0#u64 ∨ P 1#u64) := by
  rintro (e | e)
  · exact absurd e (by decide)
  · exact one_not_aligned (hP _ e)

theorem DelPlaceAt.next_false {s0 : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨s, x, hf, hb, hx, he⟩ := next_state h
  have := P.next Ac s x hf hb hx
  rw [he, WP.spec_ok] at this
  exact one_bad (fun _ e => e.1) this

theorem DelPlaceAt.prev_false {s0 : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨s, x, hf, hb, hx, he⟩ := prev_state h
  have := P.prev Ac s x hf hb hx
  rw [he, WP.spec_ok] at this
  exact one_bad (fun _ e => e.1) this

theorem DelGapsAt.next_false {A : Type _} {ar : machine.Arch A} {s0 : S}
    (P : DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨s, x, hf, hb, hx, he⟩ := next_state h
  have := P.next Ac s x hf hb hx
  rw [he, WP.spec_ok] at this
  exact one_bad (fun _ e => e.1) this

/-- The W7 forms: `next` / `prev` over `W7.SlotW`. -/
theorem W7.DelPlaceAt.next_false {s0 : S} (P : W7.DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨s, x, hf, hb, hx, he⟩ := next_state h
  have := P.next Ac s x hf hb (W7.slotW_to7 hx)
  rw [he, WP.spec_ok] at this
  exact one_bad (fun _ e => e.1) this

theorem W7.DelPlaceAt.prev_false {s0 : S} (P : W7.DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨s, x, hf, hb, hx, he⟩ := prev_state h
  have := P.prev Ac s x hf hb (W7.slotW_to7 hx)
  rw [he, WP.spec_ok] at this
  exact one_bad (fun _ e => e.1) this

theorem W7.DelGapsAt.next_false {A : Type _} {ar : machine.Arch A} {s0 : S}
    (P : W7.DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨s, x, hf, hb, hx, he⟩ := next_state h
  have := P.next Ac s x hf hb (W7.slotW_to7 hx)
  rw [he, WP.spec_ok] at this
  exact one_bad (fun _ e => e.1) this

theorem W7.R.DelPlaceAt.next_false {s0 : S} (P : W7.R.DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨s, x, hf, hb, hx, he⟩ := next_state h
  have := P.next Ac s x hf hb (W7.slotW_to7 hx)
  rw [he, WP.spec_ok] at this
  exact one_bad (fun _ e => e.1) this

theorem W7.R.DelPlaceAt.prev_false {s0 : S} (P : W7.R.DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨s, x, hf, hb, hx, he⟩ := prev_state h
  have := P.prev Ac s x hf hb (W7.slotW_to7 hx)
  rw [he, WP.spec_ok] at this
  exact one_bad (fun _ e => e.1) this

theorem W7.R.DelGapsAt.next_false {A : Type _} {ar : machine.Arch A} {s0 : S}
    (P : W7.R.DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨s, x, hf, hb, hx, he⟩ := next_state h
  have := P.next Ac s x hf hb (W7.slotW_to7 hx)
  rw [he, WP.spec_ok] at this
  exact one_bad (fun _ e => e.1) this

theorem W7.R.A5.DelPlaceAt.next_false {s0 : S} (P : W7.R.A5.DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨s, x, hf, hb, hx, he⟩ := next_state h
  have := P.next Ac s x hf hb (W7.slotW_to7 hx)
  rw [he, WP.spec_ok] at this
  exact one_bad (fun _ e => e.1) this

theorem W7.R.A5.DelPlaceAt.prev_false {s0 : S} (P : W7.R.A5.DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨s, x, hf, hb, hx, he⟩ := prev_state h
  have := P.prev Ac s x hf hb (W7.slotW_to7 hx)
  rw [he, WP.spec_ok] at this
  exact one_bad (fun _ e => e.1) this

theorem W7.R.A5.DelGapsAt.next_false {A : Type _} {ar : machine.Arch A} {s0 : S}
    (P : W7.R.A5.DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) :
    False := by
  obtain ⟨s, x, hf, hb, hx, he⟩ := next_state h
  have := P.next Ac s x hf hb (W7.slotW_to7 hx)
  rw [he, WP.spec_ok] at this
  exact one_bad (fun _ e => e.1) this

theorem W7.R.A5.B.DelPlaceAt.next_false {s0 : S} (P : W7.R.A5.B.DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨s, x, hf, hb, hx, he⟩ := next_state h
  have := P.next Ac s x hf hb (W7.slotW_to7 hx)
  rw [he, WP.spec_ok] at this
  exact one_bad (fun _ e => e.1) this

theorem W7.R.A5.B.DelPlaceAt.prev_false {s0 : S} (P : W7.R.A5.B.DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨s, x, hf, hb, hx, he⟩ := prev_state h
  have := P.prev Ac s x hf hb (W7.slotW_to7 hx)
  rw [he, WP.spec_ok] at this
  exact one_bad (fun _ e => e.1) this

theorem W7.R.A5.B.DelGapsAt.next_false {A : Type _} {ar : machine.Arch A} {s0 : S}
    (P : W7.R.A5.B.DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) :
    False := by
  obtain ⟨s, x, hf, hb, hx, he⟩ := next_state h
  have := P.next Ac s x hf hb (W7.slotW_to7 hx)
  rw [he, WP.spec_ok] at this
  exact one_bad (fun _ e => e.1) this

theorem W7.R.A5.B.V.DelGapsAt.next_false {A : Type _} {ar : machine.Arch A} {s0 : S}
    (P : W7.R.A5.B.V.DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) :
    False := by
  obtain ⟨s, x, hf, hb, hx, he⟩ := next_state h
  have := P.next Ac s x hf hb (W7.slotW_to7 hx)
  rw [he, WP.spec_ok] at this
  exact one_bad (fun _ e => e.1) this

/-! ## `irq` -/

private theorem ictl_bad : ¬ (capability.Cap.IrqControl = .Null ∨
    ∃ n b0 b1 b2, capability.Cap.IrqControl = .Notification n b0 b1 b2) := by
  rintro (e | ⟨_, _, _, _, e⟩) <;> cases e

theorem DelPlaceAt.irq_false {s0 : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨s, hf, hb, he⟩ := irq_state h
  have := P.irq Ac s 0#u64 hf hb (by simp)
  rw [he, WP.spec_ok] at this
  first | exact ictl_bad this | (revert this; simp)

theorem W7.DelPlaceAt.irq_false {s0 : S} (P : W7.DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨s, hf, hb, he⟩ := irq_state h
  have := P.irq Ac s 0#u64 hf hb (by simp)
  rw [he, WP.spec_ok] at this
  first | exact ictl_bad this | (revert this; simp)

theorem W7.R.DelPlaceAt.irq_false {s0 : S} (P : W7.R.DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨s, hf, hb, he⟩ := irq_state h
  have := P.irq Ac s 0#u64 hf hb (by simp)
  rw [he, WP.spec_ok] at this
  first | exact ictl_bad this | (revert this; simp)

theorem W7.R.A5.DelPlaceAt.irq_false {s0 : S} (P : W7.R.A5.DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨s, hf, hb, he⟩ := irq_state h
  have := P.irq Ac s 0#u64 hf hb (by simp)
  rw [he, WP.spec_ok] at this
  first | exact ictl_bad this | (revert this; simp)

theorem W7.R.A5.B.DelPlaceAt.irq_false {s0 : S} (P : W7.R.A5.B.DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨s, hf, hb, he⟩ := irq_state h
  have := P.irq Ac s 0#u64 hf hb (by simp)
  rw [he, WP.spec_ok] at this
  first | exact ictl_bad this | (revert this; simp)

/-! ## `frm` -/

private theorem frm_bad : ¬ FrMapOK (.Frame 0#u64 .Small 0#u64 false true false 1#u64 badVa) := fun h =>
  badVa_not (h _ _ _ _ _ _ rfl (by decide))

theorem W7.R.A5.DelPlaceAt.frm_false {s0 : S} (P : W7.R.A5.DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨s, x, hf, hb, hx, he⟩ := frm_state h
  have := P.frm Ac s x hf hb (W7.slotW_to7 hx)
  rw [he, WP.spec_ok] at this
  exact frm_bad this

theorem W7.R.A5.B.DelPlaceAt.frm_false {s0 : S} (P : W7.R.A5.B.DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨s, x, hf, hb, hx, he⟩ := frm_state h
  have := P.frm Ac s x hf hb (W7.slotW_to7 hx)
  rw [he, WP.spec_ok] at this
  exact frm_bad this

theorem W7.R.A5.DelGapsAt.frm_false {A : Type _} {ar : machine.Arch A} {s0 : S}
    (P : W7.R.A5.DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) :
    False := by
  obtain ⟨s, x, hf, hb, hx, he⟩ := frm_state h
  have := P.frm Ac s x hf hb (W7.slotW_to7 hx)
  rw [he, WP.spec_ok] at this
  exact frm_bad this

theorem W7.R.A5.B.DelGapsAt.frm_false {A : Type _} {ar : machine.Arch A} {s0 : S}
    (P : W7.R.A5.B.DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) :
    False := by
  obtain ⟨s, x, hf, hb, hx, he⟩ := frm_state h
  have := P.frm Ac s x hf hb (W7.slotW_to7 hx)
  rw [he, WP.spec_ok] at this
  exact frm_bad this

theorem W7.R.A5.B.V.DelGapsAt.frm_false {A : Type _} {ar : machine.Arch A} {s0 : S}
    (P : W7.R.A5.B.V.DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) :
    False := by
  obtain ⟨s, x, hf, hb, hx, he⟩ := frm_state h
  have := P.frm Ac s x hf hb (W7.slotW_to7 hx)
  rw [he, WP.spec_ok] at this
  exact frm_bad this.1

/-! ## `vco` -/

/-- **[P] `vco` (`V.DelPlaceAt`) holds at no `BXI` state.** -/
theorem W7.R.A5.B.V.DelPlaceAt.vco_false {s0 : S} (P : W7.R.A5.B.V.DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨s, x, hf, hb, hx, he⟩ := vco_state h
  have := P.vco Ac s x hf hb (W7.slotW_to7 hx)
  rw [he, WP.spec_ok] at this
  have hv := (this 1#u64 rfl Ac s hf hb).1 0#u64 (by simp) (by simp)
  rw [wadd0'] at hv
  exact one_not_aligned hv.1

/-! ## `VcPl.vcb` / `.rcv`, `TcbPlace8.rcv` / `TcbPlace9.rcv` -/

/-- **[P] `VcPl.vcb` holds at no `BXI` state.** -/
theorem VcPl.vcb_false {s0 : S} (Pl : VcPl st T Cs Ω H Sg Rp Scs Nt Z s0)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨s, t, ht, hf, hb, he⟩ := vf_state h (K := 3664#u64) (Or.inl (by simp))
  have := Pl.vcb Ac s t hf hb ht (by rw [he]; decide)
  rw [he] at this
  have hv := this.1 0#u64 (by simp) (by simp)
  rw [wadd0'] at hv
  exact one_not_aligned hv.1

/-- **[P] `VcPl.rcv` holds at no `BXI` state.** -/
theorem VcPl.rcv_false {s0 : S} (Pl : VcPl st T Cs Ω H Sg Rp Scs Nt Z s0)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨s, t, ht, hf, hb, he⟩ := vf_state h (K := 3672#u64) (Or.inr (by simp))
  have he' : L.mem s (runVcpuA t) = 1#u64 := he
  have := Pl.rcv Ac s t hf hb ht (by rw [he']; decide)
  rw [he'] at this
  have hv := this 0#u64 (by simp) (by simp)
  rw [wadd0'] at hv
  exact one_not_aligned hv.1

/-- `B.DelPlaceAt.vc` (the `VcPl` field) is refuted on its own. -/
theorem W7.R.A5.B.DelPlaceAt.vc_false {s0 : S} (P : W7.R.A5.B.DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False :=
  P.vc.vcb_false h

/-- **[P] `TcbPlace9.rcv` holds together with no `BXI` `EntAt` state.** -/
theorem TcbPlace9.rcv_false (P : TcbPlace9 st T Cs Ω H Sg Rp Scs Nt Z P3Ok) {s0 : S} (hE : EntAt st P3Ok s0)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False := by
  obtain ⟨s, t, ht, hf, hb, he⟩ := vf_state h (K := 3672#u64) (Or.inr (by simp))
  have he' : L.mem s (runVcpuA t) = 1#u64 := he
  have := P.rcv Ac s0 s t hE hf hb ht (by rw [he']; decide)
  rw [he'] at this
  have hv := this 0#u64 (by simp) (by simp)
  rw [wadd0'] at hv
  exact one_not_aligned hv.1

/-- **[P] `TcbPlace8.rcv`** likewise (`TcbPlace9.of8`). -/
theorem TcbPlace8.rcv_false (P : TcbPlace8 st T Cs Ω H Sg Rp Scs Nt Z P3Ok) {s0 : S} (hE : EntAt st P3Ok s0)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0) : False :=
  (TcbPlace9.of8 P).rcv_false hE h

end

end Fl4ProofsA64.P1
