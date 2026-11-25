/-
P1 (p1g, audit): **the premise bundles of the P1 kernel-entry tops are
contradictory**, so `kernel_entry.entry`, `entry_of` .. `entry_of10` (and
`entryXG`, `finish.entry` with `EntryHyps0`) are vacuous: each asks one of these bundles
together with an `EntryInv` state. Nothing here is a premise of anything; these are refutations, kept
so that the bundles are not used as if they held of the kernel.

Machine-checked:

* `EntryHyps0.blkU` / `tmoOK` and `P3Place.blkU` / `tmoOK` claim `CanBlock` of
  the current thread at every `BXI` (and `XG`) state; `BXI` is kept when the idle
  thread is made current, and `CanBlock.ni` says the current thread is not the
  idle thread (`EntryHyps0.not_bxi`, `EntryHyps0.tmoOK_false`; p2j4's finding).
* `P3Place.tmoAny` claims the timeout-handler cap of every thread typed
  (`CapTyped`) at every `BXI` state; `BXI` reads no cap slot, so a reply cap
  naming the null address can be written there (`P3Place.tmoAny_false`).
* `irqcap` the same, at the IRQ slots, under the `XG` guard: `XG` allows every
  cap-slot word to be rewritten (`Cur0W`'s `CapW`) (`irqcap_false`).
* `InvHyps.cur` claims the scheduler action resume at every `EntAt` `BXI`
  state; `EntAt` allows every word of the current node to be rewritten (`EntW`)
  (`InvHyps.not_bxi`).

* `XferHyps.buf` the same way (`XferHyps.buf_false`), **conditional on `hF`**: that a
  frame cap over the thread's page is encodable (true of every canonical address,
  `P3.decode_encode`; the witness for an arbitrary second word is pending).

The refutations are not vacuous themselves: their premises are exactly the entry
states the P1 tops take (`EntryInv s` with `P3Ok s`; `EntryInv.bxi` gives `BXI`,
`entAt_self` gives `EntAt` and `EntAt.xg` gives `XG`), and such states exist:
P3's `JAtZ.entryInv` (P3/XTopJointEntryInv29) proves `EntryInv` at every joint
state with the action resume, so at every kernel entry `kernel_entry_reachU29` reaches.

By the same argument, not checked here: `XferHyps.extra` / `slot` / `ins`, the cap part of `recvOK` (they read cap slots at `XG` states), the
idle part of `InvHyps.slotcap` (`EntW` allows the idle-thread word),
`DecErrG` / `postG` (no invariant guard at all).
Not affected: `act` (a theorem, `EntryHyps.of`), and the per-state premises
`RRPreAt*`, `FaultEntAt`, `RRSumAt`, `CnOffAt`, `AsidOff` (stated at one state).

The repair is not a guard on `blkU` / `tmoOK` alone: every cap-reading field
needs the caps' typing carried from the entry state across each step (P3's
relation), which is what P3's joint tops do. The entry theorem to use is
`P3.SInvR.G5.kernel_entry_entryInvU29` (P3/XTopJointEntryInv29), from U29: the
same conclusion (`EntryInv` at the exit) from P3's reachable states.
-/
import Fl4Proofs.P1.QueueEntryGaps4
import Fl4Proofs.P3.Encode
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}
variable {P3Ok : S → Prop} {A : Type _} {ar : machine.Arch A}

/-! ## The idle thread current -/

/-- From any `BXI` state there is one whose current thread is the idle thread,
one kernel-word write away (so an `XG` state if the first one is). -/
theorem BXI.idle_cur {s : S} (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    ∃ s', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ L.curW s' = L.idleW s' ∧ Foot st T Cs Sg Scs Z (EH H) s s' := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hSg, hS⟩ := h
  have hN := h0.nodes _ h0.cur
  have hsp := WP.spec_and (WP.spec_and
    (sched.set_cur_thread.sch s (L.idleW s) Q R h0 hB hSg h0.idleT (fun _ => hB.idle) (fun _ => hB.idleA h0.idleT))
    (sched.set_cur_thread.kw (T := T) (Cs := Cs) (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s (L.idleW s) hN h0.cur))
    (sched.set_cur_thread.spec s (L.idleW s))
  obtain ⟨s', hs'⟩ : ∃ s', sched.set_cur_thread st s (L.idleW s) = ok s' :=
    ⟨_, ib_eq_of_spec (sched.set_cur_thread.spec s (L.idleW s))⟩
  rw [hs'] at hsp
  obtain ⟨⟨⟨P, ec, -⟩, f⟩, e⟩ := (WP.spec_ok _).1 hsp
  refine ⟨s', ⟨P.inv, P.bnd, hX.fr P.fr, hSg.fr P.fr, hS.fr P.fr⟩, ?_, f⟩
  rw [ec, e]
  unfold LawfulStore.idleW
  exact (rd_cur_node h0 (by rw [curth0]; omega) (by rw [curth0]) (by rw [idle8]; omega) (by rw [idle8])
    (by rw [curth0, idle8]; omega)).symm

/-- **`blkU` is contradictory with any `BXI` state.** -/
theorem blkU_false
    (hb : ∀ (Ac : Set U64) (s : S), BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
      CanBlock st T Ac s (L.curW s) ∧ UserOK st T Cs Ω H U s) {s : S}
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) : False := by
  obtain ⟨s', h', e, -⟩ := h.idle_cur
  exact (hb Ac s' h').1.ni e.symm

/-- **`EntryHyps0` is contradictory with any `BXI` state** (so with any
`EntryInv` state, `EntryInv.bxi`). -/
theorem EntryHyps0.not_bxi (E : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) {s : S}
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) : False := blkU_false E.blkU h

/-- **`P3Place` is contradictory with any `BXI` state** (`blkU`). -/
theorem P3Place.not_bxi (P : P3Place st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) {s : S}
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) : False := blkU_false P.blkU h

/-- `tmoOK`'s `CanBlock` alone (guarded by `XG`) is contradictory with any `XG` `BXI` state. -/
theorem tmoOK_false
    (hT : ∀ (Ac : Set U64) (s : S), XG st T Cs Ω H Sg Scs Z P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
      CanBlock st T Ac s (L.curW s)) {s : S} (hG : XG st T Cs Ω H Sg Scs Z P3Ok s)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) : False := by
  obtain ⟨s', h', e, f⟩ := h.idle_cur
  exact (hT Ac s' (hG.foot f) h').ni e.symm

/-- **The top bundle `Hyps4` is contradictory with any `EntryInv` state** over its sets. -/
theorem Hyps4.not_entryInv {Adm : PSets → Prop} (G : Hyps4 st ar Adm Cs U P3Ok ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩) {s : S}
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) : False := G.1.not_bxi h.bxi

/-! ## The caps rewritten -/

/-- A `BXI` state stays one when a cap-slot word is written. -/
theorem BXI.capw {s : S} {a v : U64} (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ha : Aligned a) (hc : CapW T Ω Sg a) :
    BXI st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s a v) := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hSg, hS⟩ := h
  obtain ⟨h1, hB1, hX1, hS1, hSg1, -⟩ := capw_bx h0 hB hX hS hSg (writesIn_wr (v := v) ha) (fun b e => e ▸ hc)
  exact ⟨⟨Q, R, h1⟩, hB1, hX1, hSg1, hS1⟩

theorem XG.capw {s : S} {a v : U64} (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) (ha : Aligned a) (hc : CapW T Ω Sg a) :
    XG st T Cs Ω H Sg Scs Z P3Ok (L.wr s a v) :=
  hG.of_fr ((writesIn_wr (v := v) ha).mono fun _ e => Or.inr (Or.inr (Or.inl (e ▸ hc))))

theorem spec_total {α : Type _} {m : Result α} (h : m ⦃ _ => True ⦄) : ∃ y, m = ok y := by
  revert h; cases m <;> simp [WP.spec_vis, WP.spec_div, WP.spec_ok]

/-- A cap slot read: `Cap::decode` of its two words. -/
theorem slot_cap_dec (s : S) (a : U64) :
    obj.Slot.cap st a s = capability.Cap.decode (L.mem s a) (L.mem s (core.num.U64.wrapping_add a 8#u64)) := by
  unfold obj.Slot.cap
  rw [L.read_pair_eq]
  first | rfl | (simp only [bind_ok]; done) | (simp only [bind_ok]; rfl) | simp

/-- The first cap word of a reply cap naming the null address. -/
theorem decodeF_reply0 (w1 : BitVec 64) :
    P3.decodeF (2305843009213693952#u64 : U64).bv w1 = .Reply 0#u64 false := by
  have e : ((2305843009213693952#u64 : U64).bv >>> 59).toNat = 4 := by first | rfl | decide
  have hu : P3.unpackF (2305843009213693952#u64 : U64).bv = 0#64 := by
    first | rfl | decide | (unfold P3.unpackF P3.M48; decide)
  first
  | rfl
  | (simp only [P3.decodeF, e, hu]; done)
  | (simp only [P3.decodeF, e, hu]; rfl)
  | (simp only [P3.decodeF, e]; congr 1 <;> first | rfl | decide | (rw [hu]; rfl))

/-- The first cap word of a notification cap naming the null address. -/
theorem decodeF_ntfn0 (w1 : BitVec 64) :
    P3.decodeF (1729382256910270464#u64 : U64).bv w1 = .Notification 0#u64 ⟨w1⟩ false false := by
  have e : ((1729382256910270464#u64 : U64).bv >>> 59).toNat = 3 := by first | rfl | decide
  have hu : P3.unpackF (1729382256910270464#u64 : U64).bv = 0#64 := by
    first | rfl | decide | (unfold P3.unpackF P3.M48; decide)
  first
  | rfl
  | (simp only [P3.decodeF, e, hu]; done)
  | (simp only [P3.decodeF, e, hu]; rfl)
  | (simp only [P3.decodeF, e]; congr 1 <;> first | rfl | decide | (rw [hu]; rfl))

theorem mul_slot {i v : U64} (h : i.val * 32 = v.val) (hi : i.val < 8) :
    core.num.U64.wrapping_mul i layout.cte.SIZE = v := by
  apply UScalar.eq_of_val_eq
  have hs : UScalar.size UScalarTy.U64 = 2 ^ 64 := by simp [U64.size_def, U64.numBits]
  rw [core.num.U64.wrapping_mul_val_eq, show layout.cte.SIZE.val = 32 by simp [layout.cte.SIZE], h, hs]
  have : v.val < 256 := by omega
  exact Nat.mod_eq_of_lt (by omega)

/-- An entry state is reached from itself by the entry prefix: every `P3Ok`
state is an `EntAt` state, hence an `XG` state (`EntAt.xg`). -/
theorem entAt_self {s : S} (hP : P3Ok s) : EntAt st P3Ok s := ⟨s, hP, WritesIn.refl s _⟩


/-- **`tmoAny` is contradictory with any `BXI` state** (no guard, and `BXI`
reads no cap slot). -/
theorem P3Place.tmoAny_false
    (hT : ∀ (Ac : Set U64) (s : S) (t : U64), BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → t ∈ T →
      obj.Tcb.slot t layout.tcb.SLOT_TIMEOUT_HANDLER ⦃ sl => obj.Slot.cap st sl s ⦃ c => CapTyped H Rp Nt c ⦄ ⦄)
    {s : S} (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) : False := by
  have ht := h.1.choose_spec.choose_spec.curT
  have hpl := h.1.choose_spec.choose_spec.tcbs _ ht
  have ha : Aligned (core.num.U64.wrapping_add (L.curW s) 128#u64) := field_aligned hpl (by simp) (by simp)
  have h' := h.capw (v := 2305843009213693952#u64) ha (Or.inl (tlow_slots _ ht 128#u64 (by simp)))
  have := hT Ac _ (L.curW s) h' ht
  have hsl : obj.Tcb.slot (L.curW s) layout.tcb.SLOT_TIMEOUT_HANDLER =
      ok (core.num.U64.wrapping_add (L.curW s) 128#u64) := by
    have e : core.num.U64.wrapping_mul layout.tcb.SLOT_TIMEOUT_HANDLER layout.cte.SIZE = 128#u64 :=
      mul_slot (by simp [layout.tcb.SLOT_TIMEOUT_HANDLER]) (by simp [layout.tcb.SLOT_TIMEOUT_HANDLER])
    simp [obj.Tcb.slot, lift, e]
  rw [hsl, WP.spec_ok, slot_cap_dec, L.mem_wr _ _ _ _ ha ha, if_pos rfl, P3.decode_eq, decodeF_reply0,
    WP.spec_ok] at this
  exact h.2.2.1.1.rp0 _ (this.2.2 _ _ rfl) rfl

/-- **`irqcap` is contradictory with any `XG` `BXI` state** (`XG` allows every
cap-slot word to be rewritten). -/
theorem irqcap_false
    (hI : ∀ (Ac : Set U64) (s : S), XG st T Cs Ω H Sg Scs Z P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
      ∀ i : U64, i.val < 128 →
      obj.Slot.cap st (irqSlotA (L.ksb s) i) s ⦃ c => ∀ ptr b0 b1 b2, c = .Notification ptr b0 b1 b2 → ptr ∈ Nt ⦄)
    {s : S} (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) : False := by
  have h0 := h.1.choose_spec.choose_spec
  have hN := h0.nodes _ h0.cur
  have hSg := h.2.2.2.1
  have ea : irqSlotA (L.ksb s) 0#u64 = core.num.U64.wrapping_add (L.ksb s) 1248#u64 := by
    unfold irqSlotA
    apply UScalar.eq_of_val_eq
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
  have hm : irqSlotA (L.ksb s) 0#u64 ∈ Ω := ea ▸ hSg.ksΩ 1248#u64 (by simp) (by simp)
  have ha : Aligned (irqSlotA (L.ksb s) 0#u64) := (h0.omega _ hm).1
  have hv : (irqSlotA (L.ksb s) 0#u64).val = (L.ksb s).val + 1248 := by
    have hf := hN.fits
    have hb : (L.ksb s).val + 1248 < 2 ^ 64 := by simp only [LawfulStore.nodeBase] at hf; omega
    rw [ea]
    simp only [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
    exact Nat.mod_eq_of_lt (by simpa [U64.size_def, U64.numBits] using hb)
  have hc : CapW T Ω Sg (irqSlotA (L.ksb s) 0#u64) := Or.inr ⟨hm, fun hs => by
    rcases hSg.ks _ hs with e | e <;> rw [hv] at e <;> omega⟩
  have := hI Ac _ (hG.capw (v := 1729382256910270464#u64) ha hc) (h.capw (v := 1729382256910270464#u64) ha hc) 0#u64
    (by simp)
  rw [L.ksb_wr] at this
  rw [slot_cap_dec, L.mem_wr _ _ _ _ ha ha, if_pos rfl, P3.decode_eq, decodeF_ntfn0, WP.spec_ok] at this
  exact h.2.2.1.1.nt0 0#u64 (this 0#u64 _ false false rfl) rfl

/-- **`XferHyps.buf` is contradictory with any `XG` state** of the transfer
invariants (`XG` allows the IPC-buffer cap slot to be rewritten), given only that a frame
cap over the current thread's page is encodable (`hF`: its address is
canonical, as every kernel object's). -/
theorem XferHyps.buf_false (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) {X : Set U64}
    {Q : U64 → U64 → List U64} {R : U64 → List U64} {s : S} (hG : XG st T Cs Ω H Sg Scs Z P3Ok s)
    (h : XI st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s) {t : U64} (ht : t ∈ T)
    (hF : ∃ w0, ∀ w1, ∃ b c d e, capability.Cap.decode w0 w1 =
      ok (.Frame t .Small capability.VM_READ_WRITE false b c d e)) : False := by
  obtain ⟨w0, hF⟩ := hF
  have hpl := h.1.tcbs _ ht
  have es : sbWordA t = core.num.U64.wrapping_add t 64#u64 := by
    have e : core.num.U64.wrapping_mul layout.tcb.SLOT_BUFFER layout.cte.SIZE = 64#u64 :=
      mul_slot (by simp [layout.tcb.SLOT_BUFFER]) (by simp [layout.tcb.SLOT_BUFFER])
    rw [sbWordA, e]
  have ha : Aligned (sbWordA t) := es ▸ field_aligned hpl (by simp) (by simp)
  have hc : CapW T Ω Sg (sbWordA t) := es ▸ Or.inl (tlow_slots _ ht 64#u64 (by simp))
  have h1 := XS.capw (XS.start h) (writesIn_wr (st := st) (s := s) (v := w0) ha) (fun b e => e ▸ hc)
  have hb := E.buf _ _ _ _ _ t (hG.capw (v := w0) ha hc) h1.1 ht
  have hU := h1.1.2.2.2.2.2
  unfold msg.lookup_ipc_buffer at hb
  rw [ipc_buffer_word] at hb
  have hs : obj.Tcb.slot t layout.tcb.SLOT_BUFFER = ok (sbWordA t) := by simp [obj.Tcb.slot, lift, sbWordA]
  rw [hs] at hb
  simp only [bind_ok] at hb
  rw [slot_cap_dec, L.mem_wr _ _ _ _ ha ha, if_pos rfl] at hb
  obtain ⟨b, c, d, e, hd⟩ := hF (L.mem (L.wr s (sbWordA t) w0) (core.num.U64.wrapping_add (sbWordA t) 8#u64))
  have e12 : (1#u64 <<< (12#u64 &&& 63#u64) : Result U64) = ok 4096#u64 := by rfl
  simp only [bind_ok, hd, capability.FrameSize.bits, lift, Bool.false_eq_true, if_false, if_true, e12,
    WP.spec_ok] at hb
  generalize hm : (L.mem (L.wr s (sbWordA t) w0) (ibWordA t) &&& core.num.U64.wrapping_sub 4096#u64 1#u64 : U64) = m at hb
  have hmv : m.val < 4096 := by
    have e' : core.num.U64.wrapping_sub 4096#u64 1#u64 = 4095#u64 := by rfl
    rw [← hm, e']
    simp only [UScalar.val_and]
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by simp)
  have hf := hpl.fits
  have hv : (core.num.U64.wrapping_add t m).val = t.val + m.val := by
    have hs : UScalar.size UScalarTy.U64 = 2 ^ 64 := by simp [U64.size_def, U64.numBits]
    rw [core.num.U64.wrapping_add_val_eq, hs]
    exact Nat.mod_eq_of_lt (by omega)
  have hb0 := hb (fun e => by
    have := congrArg UScalar.val e
    rw [hv] at this
    have := hpl.ne0
    simp at *; omega) 0#u64 (by simp)
  have e0 : core.num.U64.wrapping_add (core.num.U64.wrapping_add t m) (core.num.U64.wrapping_mul 0#u64 8#u64) =
      core.num.U64.wrapping_add t m := by
    apply UScalar.eq_of_val_eq
    have := (core.num.U64.wrapping_add t m).hBounds
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
  rw [e0] at hb0
  have ho := (hU _ hb0).1.2.1 t ht
  rw [hv] at ho
  omega

/-! ## The entry's current-node words -/

/-- **`InvHyps` (its `cur`) is contradictory with any `EntAt` `BXI` state**:
`EntAt` allows the current node's scheduler action to be rewritten. -/
theorem InvHyps.not_bxi (I : InvHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok) {s : S} (he : EntAt st P3Ok s)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) : False := by
  have hact := (I.cur Ac s he h).2
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hSg, hS⟩ := h
  have hN := h0.nodes _ h0.cur
  have hsp := WP.spec_and (sched.reschedule_required.sch s Q R h0 hB hSg) (sched.reschedule_required.resume s hact)
  obtain ⟨s', hs'⟩ : ∃ s', sched.reschedule_required st s = ok s' :=
    ⟨_, ib_eq_of_spec (sched.reschedule_required.resume s hact)⟩
  rw [hs'] at hsp
  obtain ⟨⟨⟨hi, hB1, f1⟩, e1, -⟩, e⟩ := (WP.spec_ok _).1 hsp
  have he' : EntAt st P3Ok s' := by
    obtain ⟨e0, hP, w⟩ := he
    refine ⟨e0, hP, ?_⟩
    subst e
    refine (WritesIn.trans w (writesIn_wr (nodeAt_aligned hN (by simp [layout.node.SCHED_ACTION])
      (by simp [layout.node.SCHED_ACTION])))).mono fun b hb => hb.elim id fun hb => Or.inr ?_
    exact ⟨layout.node.SCHED_ACTION, trivial, by simp [layout.node.SCHED_ACTION], by simp [layout.node.SCHED_ACTION],
      by rw [hb, ← w.2.1, nodeAt_of_ksb w.1]⟩
  have h2 := (I.cur Ac s' he' ⟨hi, hB1, hX.fr f1, hSg.fr f1, hS.fr f1⟩).2
  rw [e1] at h2
  exact absurd h2 (by decide)

end

end Fl4Proofs.P1
