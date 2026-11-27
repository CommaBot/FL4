/-
P1 (aarch64): **the seventh TCB cap slot** (`W7`).

AArch64 TCBs have seven cap slots (`layout::tcb::NUM_SLOTS` 7; slot 6 is `SLOT_HIGH_VSPACE`, TCB offsets
192–223, the registers start at 256). The x86_64-shaped `TLow` / `CapW` / `SlotW` (QueueFinal / QueueDecDel) cover
offsets below 192 only (six slots), so slot 6 is no cap slot there: neither the HighVSpace slot's install nor the
7-slot Zombie remainder of a TCB (`.Zombie p ZOMBIE_TCB 7`) is typed for deletion.

This module re-states the cap-slot vocabulary and the deletion chain in the namespace `W7`, with the TCB low
words below 224 (all seven slots), **new definitions only, no existing statement changed**:
* `W7.TLow` (< 224), `W7.CapW`, `W7.SlotW`, `W7.DelCapOK`; bridges `tlow_to7`, `capw_to7`, `slotW_to7`,
  `delCapOK_to7` (old ⇒ W7), `delCapOK_of7` (W7 ⇒ old for caps that are no CNode / Zombie).
* `W7.blk_of_capw` (QueueSlots' text with 224: no invariant reads a TCB word below 224), `capw_cur0w`
  (a W7 cap-slot word is a `Cur0W` word: below 192 a `CapW` word, 192–223 a `KW` TCB word), so `Cur0` / `Fr0`
  are unchanged and `Cur0.capw7` / `Cur0.cw7` keep `Cur0` across W7 cap-slot writes.
* The deletion chain over the W7 forms (QueueDecDel / QueueDelFin text): `DelGapsAt`, `DelGaps`,
  `cdt.finalise_slot_immediate.cur0`, `cdt.delete.cur0`, `cdt.revoke.cur0`, `cnode_del`, `cnode_rev`,
  `cnode.decode.dec2` (old `CdtHyps2`, its slot bridged by `slotW_to7`), `decGap_cnode2`, `FinGap`, `FinGapAt`,
  `DelPlaceAt`, `DelPlace`, `fin_vs`, `FinKindsAt`, `fin_all`, the slot writes, `post_cap_deletion`,
  `empty_slot`, `cdt.swap`, `cap_swap_for_delete`, `finalise_slot_deferred`, `delete_deferred`, `delGaps_of`.
* `W7.DelPlaceAt` has the fields of `DelPlaceAt` (its [J] `rv` included) and one more, **[P] `rcw`**: a thread's
  run VCPU's `RUN_CALLER` word is a user word (`UserW`), the kind and shape of VcpuCheckInv's [P] `hpw`. It is used
  by QueueFinThr7's thread kind (`vcpu::cancel_run` of a thread in an `ARMVCPURun`).

Named premises: [J] `W7.DelPlaceAt.rv` (as `DelPlaceAt.rv`), [P] `W7.DelPlaceAt.rcw` (new field).
-/
import Fl4ProofsA64.P1.QueueFinIo
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}

namespace W7

/-- The low words of the TCBs, below offset 224: the seven AArch64 cap slots (x86_64 `TLow`: below 192). -/
def TLow (T : Set U64) (b : U64) : Prop := ∃ t ∈ T, ∃ K : U64, K.val < 224 ∧ b = core.num.U64.wrapping_add t K

/-- Capability-slot words with the seven AArch64 TCB slots. -/
def CapW (T Ω Sg : Set U64) (b : U64) : Prop := TLow T b ∨ (b ∈ Ω ∧ b ∉ Sg)

/-- The four words of a cap slot are (W7) cap-slot words. -/
def SlotW (T Ω Sg : Set U64) (x : U64) : Prop :=
  Aligned x ∧ ∀ o : U64, o.val < 32 → o.val % 8 = 0 → CapW T Ω Sg (core.num.U64.wrapping_add x o)

theorem tlow_to7 {b : U64} (h : Fl4ProofsA64.P1.TLow T b) : TLow T b := by
  obtain ⟨t, ht, K, hK, e⟩ := h; exact ⟨t, ht, K, by omega, e⟩

theorem capw_to7 {b : U64} (h : Fl4ProofsA64.P1.CapW T Ω Sg b) : CapW T Ω Sg b :=
  h.elim (fun h' => Or.inl (tlow_to7 h')) Or.inr

theorem slotW_to7 {x : U64} (h : Fl4ProofsA64.P1.SlotW T Ω Sg x) : SlotW T Ω Sg x :=
  ⟨h.1, fun o h1 h2 => capw_to7 (h.2 o h1 h2)⟩

/-- Every word below offset 224 of a TCB (its seven cap slots, a64) is a `TLow`
word (the Sc side's `TLowSlots`). -/
theorem tlow_slots : ∀ t ∈ T, ∀ K : U64, K.val < 224 → TLow T (core.num.U64.wrapping_add t K) :=
  fun t ht K hK => ⟨t, ht, K, hK, rfl⟩

theorem tlow_ne_field {y K b : U64} (hT : TcbPlaced T) (hy : y ∈ T) (hK0 : 224 ≤ K.val) (hK : K.val < 4096)
    (hb : TLow T b) : b ≠ core.num.U64.wrapping_add y K := by
  obtain ⟨t, ht, K', hK', rfl⟩ := hb
  exact field_ne (hT t ht) (hT y hy) (by omega) hK (fun _ => by omega)

theorem tlow_ne_node {s : S} {c o b : U64} (hT : TcbPlaced T) (hN : NodePlaced st T s c) (ho : o.val < 4288)
    (hb : TLow T b) : L.nodeAt s c o ≠ b := by
  obtain ⟨t, ht, K', hK', rfl⟩ := hb
  exact node_ne_field hN ho ht (hT t ht) (by omega)

theorem tlow_ne_out {s : S} {a : U64} (hT : TcbPlaced T) (ha : OutsideObjs st T Cs s a) (hb : TLow T a) : False := by
  obtain ⟨t, ht, K', hK', e⟩ := hb
  exact out_ne_field (K := K') ha ht (hT t ht) (by omega) (by rw [e])

theorem inv_of_capw {Cs X : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) {B : U64 → Prop} (hw : WritesIn st s s' B)
    (hBw : ∀ b, B b → L.Free s Ω Cs b ∨ TLow T b) :
    SchedQueuesInvX st T Cs Ω H X s' Q R := by
  have hT := h.tcbs
  have fld : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      224 ≤ K.val → L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
    intro y hy K hK hK8 hK0
    refine hw.mem_eq (field_aligned (hT y hy) hK hK8) fun hb => ?_
    rcases hBw _ hb with (hm | ⟨c, hc, o, ho, e⟩) | hl
    rotate_right
    · exact tlow_ne_field hT hy hK0 hK hl rfl
    · exact out_ne_field (h.omega _ hm) hy (hT y hy) hK rfl
    · exact node_ne_field (h.nodes c hc) (by simp only [LowFree] at ho; omega) hy (hT y hy) hK e.symm
  have nod : ∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → ¬ LowFree o.val →
      L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o) := by
    intro c hc o ho h8 hro
    refine hw.mem_eq (nodeAt_aligned (h.nodes c hc) ho h8) fun hb => ?_
    rcases hBw _ hb with (hm | ⟨c', hc', o', ho', e⟩) | hl
    rotate_right
    · exact tlow_ne_node hT (h.nodes c hc) ho hl rfl
    · exact out_ne_node (h.omega _ hm) hc (h.nodes c hc) ho rfl
    · by_cases hcc : c' = c
      · subst hcc
        simp only [LowFree] at ho' hro
        have := congrArg UScalar.val e
        rw [nodeAt_val (h.nodes c' hc) ho, nodeAt_val (h.nodes c' hc) (by omega : o'.val < 4288)] at this
        omega
      · simp only [LowFree] at ho'
        exact nodeAt_ne_cpu (h.nodes c hc) (h.nodes c' hc') ho (by omega : o'.val < 4288) (Ne.symm hcc) e
  have hsb : ∀ y ∈ T, L.mem s' (stA y) = L.mem s (stA y) ∧ L.mem s' (blockA y) = L.mem s (blockA y) :=
    fun y hy => ⟨by rw [stA_eq]; exact fld y hy _ (by simp) (by simp) (by simp),
      by rw [blockA_eq]; exact fld y hy _ (by simp) (by simp) (by simp)⟩
  have hact : L.actionW s' = L.actionW s := by
    unfold LawfulStore.actionW
    rw [hw.2.1, nodeAt_of_ksb hw.1]
    exact nod _ h.cur _ (by rw [act_val]; omega) (by rw [act_val]) (by rw [act_val]; simp [LowFree])
  refine inv_of_agree h hw.1 hw.2.1 (fun y hy => ⟨?_, ?_⟩)
    (fun c hc o h1 h2 h3 => nod c hc o h1 h2 (by simp only [LowFree]; omega))
    (fun y hy => fld y hy _ (by simp) (by simp) (by simp)) (fun y hy => fld y hy _ (by simp) (by simp) (by simp))
    (fun y hy => Or.inl (fld y hy _ (by simp) (by simp) (by simp))) (by rw [hact]; exact h.action) hsb
    (by rw [hact]; intro haT; rw [(hsb _ haT).1]; exact h.actOK haT) ?_
    (by rw [hw.2.1, nodeAt_of_ksb hw.1, nod _ h.cur _ (by rw [curth0]; omega) (by rw [curth0])
          (by rw [curth0]; simp [LowFree])]; exact h.curT)
    (by rw [hw.2.1, nodeAt_of_ksb hw.1, nod _ h.cur _ (by rw [idle8]; omega) (by rw [idle8])
          (by rw [idle8]; simp [LowFree])]; exact h.idleT)
  · rw [nextA_eq']; exact fld y hy _ (by simp [nextOff]) (by simp [nextOff]) (by simp [nextOff])
  · rw [prevA_eq']; exact fld y hy _ (by simp [prevOff]) (by simp [prevOff]) (by simp [prevOff])
  obtain ⟨E, EQ, w1, w2, w5, w3, w4, w6⟩ := h.eps
  have hnb : ∀ c, L.nodeBase s' c = L.nodeBase s c := fun c => by simp [LawfulStore.nodeBase, hw.1]
  have ewg : ∀ e ∈ E, ∀ a, (a = epHeadA e ∨ a = epTSA e) → L.mem s' a = L.mem s a := by
    intro e he a ha
    obtain ⟨hE, hEN, hq⟩ := w1 e he
    obtain ⟨a1, a2⟩ := ep_aligned hE
    have hal : Aligned a := by rcases ha with rfl | rfl <;> assumption
    have hav : a.val = e.val ∨ a.val = e.val + 8 := by
      rcases ha with rfl | rfl
      · exact Or.inl epHeadA_val
      · exact Or.inr (epTSA_val hE)
    refine hw.mem_eq hal fun hb => ?_
    rcases hBw _ hb with (hm | ⟨c, hc, o, ho, e2⟩) | hl
    rotate_right
    · exact tlow_ne_out hT (by rcases ha with rfl | rfl; exacts [(ep_out hE hEN).1, (ep_out hE hEN).2]) hl
    · have := w5 e he a hm; omega
    · have := congrArg UScalar.val e2
      rw [nodeAt_val (h.nodes c hc) (by simp only [LowFree] at ho; omega)] at this
      have := hEN.1 c hc; simp only [LowFree] at ho; omega
  refine ⟨E, EQ, fun e he => ?_, w2, w5, fun e he y hy => ?_, fun y hy hyX hb => ?_,
    w6.agree (fun y hy => Or.inl hy) (fun y hy _ _ => hsb y hy) (fun _ _ _ hy => hy)
      (fun e he y hy => (hsb y ((w1 e he).2.2.mem y hy)).1)
      (fun e he _ => by simp only [LawfulStore.epState, ewg e he _ (Or.inr rfl)])
      (fun e he h0 => Or.inl ⟨h0, by simp only [LawfulStore.epState, ewg e he _ (Or.inr rfl)]⟩)⟩
  · obtain ⟨hE, hEN, hq⟩ := w1 e he
    obtain ⟨a1, a2⟩ := ep_aligned hE
    have ew : ∀ a, (a = epHeadA e ∨ a = epTSA e) → L.mem s' a = L.mem s a := by
      intro a ha
      have hal : Aligned a := by rcases ha with rfl | rfl <;> assumption
      have hav : a.val = e.val ∨ a.val = e.val + 8 := by
        rcases ha with rfl | rfl
        · exact Or.inl epHeadA_val
        · exact Or.inr (epTSA_val hE)
      refine hw.mem_eq hal fun hb => ?_
      rcases hBw _ hb with (hm | ⟨c, hc, o, ho, e2⟩) | hl
      rotate_right
      · exact tlow_ne_out hT (by rcases ha with rfl | rfl; exacts [(ep_out hE hEN).1, (ep_out hE hEN).2]) hl
      · have := w5 e he a hm; omega
      · have := congrArg UScalar.val e2
        rw [nodeAt_val (h.nodes c hc) (by simp only [LowFree] at ho; omega)] at this
        have := hEN.1 c hc; simp only [LowFree] at ho; omega
    have eq : L.epQ s' e = L.epQ s e := by
      simp only [LawfulStore.epQ, ew _ (Or.inl rfl), ew _ (Or.inr rfl)]
    refine ⟨hE, ⟨fun c hc => by rw [hnb]; exact hEN.1 c hc, by rw [hw.1]; exact hEN.2⟩, ?_⟩
    rw [eq]
    exact ⟨hq.nodup, hq.mem, hq.head, hq.last, hq.seg.congr fun y hy =>
      ⟨by rw [prevA_eq']; exact fld y (hq.mem y hy) _ (by simp [prevOff]) (by simp [prevOff]) (by simp [prevOff]),
       by rw [nextA_eq']; exact fld y (hq.mem y hy) _ (by simp [nextOff]) (by simp [nextOff]) (by simp [nextOff])⟩⟩
  · have hyT := (w1 e he).2.2.mem y hy
    rw [(hsb y hyT).1, (hsb y hyT).2]; exact w3 e he y hy
  · rw [(hsb y hy).1] at hb
    rw [(hsb y hy).2]; exact w4 y hy hyX hb

variable {X : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}

theorem BoundInv.capw {Ω : Set U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T Ac s)
    {B : U64 → Prop} (hw : WritesIn st s s' B)
    (hBw : ∀ b, B b → L.Free s Ω Cs b ∨ TLow T b) : BoundInv st T Ac s' := by
  have hT := h.tcbs
  have fld : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      224 ≤ K.val → L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
    intro y hy K hK hK8 hK0
    refine hw.mem_eq (field_aligned (hT y hy) hK hK8) fun hb => ?_
    rcases hBw _ hb with (hm | ⟨c, hc, o, ho, e⟩) | hl
    rotate_right
    · exact tlow_ne_field hT hy hK0 hK hl rfl
    · exact out_ne_field (h.omega _ hm) hy (hT y hy) hK rfl
    · exact node_ne_field (h.nodes c hc) (by simp only [LowFree] at ho; omega) hy (hT y hy) hK e.symm
  have nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → ¬ LowFree o.val →
      L.mem s' (L.nodeAt s' (L.cpu s') o) = L.mem s (L.nodeAt s (L.cpu s) o) := by
    intro o ho h8 hro
    rw [hw.2.1, nodeAt_of_ksb hw.1]
    refine hw.mem_eq (nodeAt_aligned (h.nodes _ h.cur) ho h8) fun hb => ?_
    rcases hBw _ hb with (hm | ⟨c', hc', o', ho', e⟩) | hl
    rotate_right
    · exact tlow_ne_node hT (h.nodes _ h.cur) ho hl rfl
    · exact out_ne_node (h.omega _ hm) h.cur (h.nodes _ h.cur) ho rfl
    · by_cases ec : L.cpu s = c'
      · subst ec
        have := congrArg UScalar.val e
        rw [nodeAt_val (h.nodes _ h.cur) ho, nodeAt_val (h.nodes _ h.cur) (by simp only [LowFree] at ho'; omega)] at this
        exact hro (by have : o.val = o'.val := by omega
                      rw [this]; exact ho')
      · exact nodeAt_ne_cpu (h.nodes _ h.cur) (h.nodes _ hc') ho (by simp only [LowFree] at ho'; omega) ec e
  have hsc : ∀ y ∈ T, L.mem s' (scA y) = L.mem s (scA y) := fun y hy => by
    rw [scA_eq]; exact fld y hy _ (by simp) (by simp) (by simp)
  have hinq : ∀ y ∈ T, L.mem s' (inqA y) = L.mem s (inqA y) := fun y hy => by
    rw [inqA_eq]; exact fld y hy _ (by simp) (by simp) (by simp)
  have ea : L.actionW s' = L.actionW s := by
    unfold LawfulStore.actionW; exact nd _ (by rw [act_val]; omega) (by rw [act_val]) (by simp [act_val, LowFree])
  have ec : L.curW s' = L.curW s := by
    unfold LawfulStore.curW; exact nd _ (by rw [curth0]; omega) (by rw [curth0]) (by simp [curth0, LowFree])
  have ei : L.idleW s' = L.idleW s := by
    unfold LawfulStore.idleW; exact nd _ (by rw [idle8]; omega) (by rw [idle8]) (by simp [idle8, LowFree])
  refine hB.mk' hsc (fun y hy hf => Or.inl (by rw [← hinq y hy]; exact hf))
    (fun y hy hf => Or.inr (Or.inl (by rw [← hinq y hy]; exact hf))) (fun haT => ?_) ?_ (fun h0 => ?_)
    (hB.nb ei (by rw [stA_eq]; exact fld _ h.idleT _ (by simp) (by simp) (by simp)))
    (fun y hy hS _ => Or.inl (Sch.of_eq (fun hf => by rwa [hinq y hy] at hf) (fun hf => by rwa [hinq y hy] at hf)
      ea ei ec (by rw [stA_eq]; exact fld _ hy _ (by simp) (by simp) (by simp)) hS))
  · rw [ea] at haT ⊢; exact ⟨haT, hB.act haT⟩
  · rw [ei]; exact ⟨h.idleT, hB.idle⟩
  · rw [ea] at h0; rw [ec]; exact ⟨h.curT, hB.resume h0⟩

/-- **Writes confined to cap-slot words keep `BlkOK`**, with every TCB field
from offset 224, every node word of the cores and every frame word `Sg`
unchanged (so `PFr`, the current and idle threads, the current SC and the
scheduler action hold). -/
theorem blk_of_capw {s s' : S} {B : U64 → Prop} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hw : WritesIn st s s' B) (hB : ∀ b, B b → CapW T Ω Sg b) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ PFr st T Sg s s' ∧
      L.curW s' = L.curW s ∧ L.cscW s' = L.cscW s ∧ L.actionW s' = L.actionW s ∧
      (∀ y ∈ T, ∀ K : U64, 224 ≤ K.val → K.val < 4096 → K.val % 8 = 0 →
        L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o)) ∧
      (∀ b ∈ Sg, L.mem s' b = L.mem s b) := by
  obtain ⟨⟨Q, R, h0⟩, hBd, hX, hS, hSg⟩ := h
  have hT := h0.tcbs
  have hO := hX.1
  have hBw : ∀ b, B b → L.Free s Ω Cs b ∨ TLow T b := fun b hb =>
    (hB b hb).elim Or.inr fun h' => Or.inl (Or.inl h'.1)
  have fld : ∀ y ∈ T, ∀ K : U64, 224 ≤ K.val → K.val < 4096 → K.val % 8 = 0 →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
    intro y hy K hK0 hK hK8
    refine hw.mem_eq (field_aligned (hT y hy) hK hK8) fun hb => ?_
    rcases hB _ hb with hl | ⟨hm, -⟩
    · exact tlow_ne_field hT hy hK0 hK hl rfl
    · exact out_ne_field (h0.omega _ hm) hy (hT y hy) hK rfl
  have nod : ∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o) := by
    intro c hc o ho h8
    refine hw.mem_eq (nodeAt_aligned (h0.nodes c hc) ho h8) fun hb => ?_
    rcases hB _ hb with hl | ⟨hm, -⟩
    · exact tlow_ne_node hT (h0.nodes c hc) ho hl rfl
    · exact out_ne_node (h0.omega _ hm) hc (h0.nodes c hc) ho rfl
  have sig : ∀ b ∈ Sg, L.mem s' b = L.mem s b := by
    intro b hb
    have ho := h0.omega _ (hSg.sub b hb)
    refine hw.mem_eq ho.1 fun hb' => ?_
    rcases hB _ hb' with hl | ⟨-, hn⟩
    · exact tlow_ne_out hT ho hl
    · exact hn hb
  have cur : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem s' (L.nodeAt s' (L.cpu s') o) = L.mem s (L.nodeAt s (L.cpu s) o) := fun o ho h8 => by
    rw [hw.2.1, nodeAt_of_ksb hw.1]; exact nod _ h0.cur o ho h8
  have hsc : ∀ y ∈ T, L.mem s' (scA y) = L.mem s (scA y) := fun y hy => by
    rw [scA_eq]; exact fld y hy _ (by simp) (by simp) (by simp)
  have hst : ∀ y ∈ T, L.mem s' (stA y) = L.mem s (stA y) := fun y hy => by
    rw [stA_eq]; exact fld y hy _ (by simp) (by simp) (by simp)
  have ecs : L.cscW s' = L.cscW s := by
    unfold LawfulStore.cscW LawfulStore.nodeA
    exact cur _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have ei : L.idleW s' = L.idleW s := by
    unfold LawfulStore.idleW; exact cur _ (by rw [idle8]; omega) (by rw [idle8])
  have ea : L.actionW s' = L.actionW s := by
    unfold LawfulStore.actionW; exact cur _ (by rw [act_val]; omega) (by rw [act_val])
  have ec : L.curW s' = L.curW s := by
    unfold LawfulStore.curW; exact cur _ (by rw [curth0]; omega) (by rw [curth0])
  have htm : TmFr st T Cs Nt s s' := TmFr.of_writes hT h0.nodes hO hw fun b hb => by
    rcases hB b hb with hl | ⟨hm, hn⟩
    · rintro (⟨y, hy, K, h1, h2, h3, e⟩ | ⟨c, hc, o, ho, e⟩ | ⟨n, hn', e⟩)
      · exact tlow_ne_field hT hy (by omega) (by omega) hl e
      · exact tlow_ne_node hT (h0.nodes c hc) (by omega) hl e.symm
      · exact tlow_ne_out hT (h0.omega _ (hSg.sub _ (hO.ntB n hn').2)) (by rw [← e]; exact hl)
    · rintro (⟨y, hy, K, h1, h2, h3, e⟩ | ⟨c, hc, o, ho, e⟩ | ⟨n, hn', e⟩)
      · exact out_ne_field (h0.omega _ hm) hy (hT y hy) (by omega) (congrArg UScalar.val e).symm
      · exact out_ne_node (h0.omega _ hm) hc (h0.nodes c hc) (by omega) (congrArg UScalar.val e).symm
      · exact hn (by rw [e]; exact (hO.ntB n hn').2)
  have hX' : XInv st T Cs Ω Sg Rp Scs Nt Z s' :=
    hX.keep (fun r hr => ⟨sig _ (hX.1.tcbW hr), sig _ (hX.1.prevW hr), sig _ (hX.1.nextW hr)⟩)
      (fun c hc => ⟨sig _ (hX.1.fixW c hc).1, sig _ (hX.1.fixW c hc).2⟩) hsc
      (fun y hy => fld y hy _ (by simp) (by simp) (by simp)) hst
      (by rw [ecs]; exact hX.2.2.cur) (fun c hc => sig _ (hX.1.repW c hc))
      (fun y hy => fld y hy _ (by simp) (by simp) (by simp))
      (fun n hn => sig _ (hX.1.ntW n hn)) (hX.tn htm)
      (fun c hc => sig _ (hX.1.snW c hc)) (fun y hy => fld y hy _ (by simp) (by simp) (by simp))
      (fun c hc => sig _ (hX.1.syW c hc))
      (fun c hc => sig _ (hX.1.mxW c hc)) ei
      (fun y hy => fld y hy _ (by simp) (by simp) (by simp))
  have hS' : SCsOK st T Ω Sg Scs Z Ac s' := by
    refine ⟨hS.sub, fun b hb => by rw [hw.1]; exact hS.ks b hb, fun o h1 h2 => by rw [hw.1]; exact hS.ksΩ o h1 h2,
      fun t ht hb hne => ?_, fun c hc => (hS.all c hc).agree sig,
      fun c hc => by rw [show L.rmax s' c = L.rmax s c from sig _ (hS.all c hc).2.1]; exact hS.act c hc,
      fun c hc h1 => hS.spor c hc (by rw [← sig _ (hS.spSg c hc)]; exact h1), hS.spSg,
      fun c hc h1 => hS.rep c hc (by rw [← sig _ (hS.repSg c hc)]; exact h1), hS.repSg, fun c hc => by rw [hw.1]; exact hS.scKs c hc⟩
    rw [hsc t ht] at hb hne ⊢; rw [ecs] at hne ⊢; exact hS.disj t ht hb hne
  exact ⟨⟨⟨Q, R, inv_of_capw h0 hw hBw⟩, BoundInv.capw h0 hBd hw hBw, hX', hS',
      ⟨hSg.sub, fun b hb => by rw [hw.1]; exact hSg.ks b hb, fun o h1 h2 => by rw [hw.1]; exact hSg.ksΩ o h1 h2⟩⟩,
    ⟨hsc, hst, sig, ei, Or.inl ea⟩, ec, ecs, ea, fld, nod, sig⟩

/-- One write of a cap-slot word. -/
theorem blk_capw_wr {s : S} {b v : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ha : Aligned b)
    (hb : CapW T Ω Sg b) : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s b v) :=
  (blk_of_capw h (writesIn_wr ha) fun b' e => by subst e; exact hb).1

/-- The current-thread conditions of the later steps (`set_priority`'s, say)
carry across cap-slot writes. -/
theorem capw_cur {s s' : S} {B : U64 → Prop} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hw : WritesIn st s s' B) (hB : ∀ b, B b → CapW T Ω Sg b) (t : U64) (ht : t ∈ T) :
    L.mem s' (inqA t) = L.mem s (inqA t) ∧ L.mem s' (scA t) = L.mem s (scA t) ∧ L.mem s' (stA t) = L.mem s (stA t) := by
  obtain ⟨-, -, -, -, -, fld, -, -⟩ := blk_of_capw h hw hB
  exact ⟨by rw [inqA_eq]; exact fld t ht _ (by simp) (by simp) (by simp),
    by rw [scA_eq]; exact fld t ht _ (by simp) (by simp) (by simp),
    by rw [stA_eq]; exact fld t ht _ (by simp) (by simp) (by simp)⟩


/-- A W7 cap-slot word is a `Cur0W` word: below 192 a `CapW` word, from 192 a `KW` TCB word. -/
theorem capw_cur0w {s0 : S} {b : U64} (h : CapW T Ω Sg b) : Cur0W st T Cs Ω H Sg Scs Z s0 b := by
  rcases h with ⟨t, ht, K, hK, rfl⟩ | h
  · by_cases hl : K.val < 192
    · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨t, ht, K, hl, rfl⟩)))
    · exact Or.inl (Or.inl ⟨t, ht, K, by omega, by omega, by omega, by omega, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl (Or.inr h)))

/-- W7 cap-slot writes keep `Cur0`. -/
theorem _root_.Fl4ProofsA64.P1.Cur0.capw7 {s0 s s' : S} {B : U64 → Prop}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hw : WritesIn st s s' B) (hB : ∀ b, B b → W7.CapW T Ω Sg b) :
    Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' := by
  have h0 := h
  obtain ⟨-, Ac', h1, -, -, -, -, -⟩ := h0
  have hct : L.curW s ∈ T := h1.1.choose_spec.choose_spec.curT
  obtain ⟨b, -, ec, ecs, ea, fld, -, -⟩ := W7.blk_of_capw h1.blk hw hB
  refine Cur0.mk h (BlkOK.bxi b) ec ecs (Or.inl ?_) (Or.inl ea) (Or.inl ?_)
    (hw.mono fun b hb => W7.capw_cur0w (hB b hb))
  · rw [scA_eq]; exact fld _ hct _ (by simp) (by simp) (by simp)
  · rw [stA_eq]; exact fld _ hct _ (by simp) (by simp) (by simp)

theorem _root_.Fl4ProofsA64.P1.Cur0.cw7 {s0 s : S} {m : Result S} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (hm : m ⦃ s' => WritesIn st s s' (W7.CapW T Ω Sg) ⦄) : m ⦃ s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ :=
  WP.spec_mono hm fun _ w => h.capw7 w fun _ hb => hb

/-- `set_cap` of a cap slot. -/
theorem obj.Slot.set_cap.capw {s : S} {x : U64} {c : capability.Cap} (hx' : SlotW T Ω Sg x) :
    obj.Slot.set_cap st x s c ⦃ s' => WritesIn st s s' (CapW T Ω Sg) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  obtain ⟨ha, hx⟩ := hx'
  unfold obj.Slot.set_cap
  refine WP.spec_bind (P0.capability.Cap.encode.p0 c) ?_
  rintro ⟨w0, w1⟩ -
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (LawfulStore.write_spec s x w0) fun s1 e1 => ?_
  subst e1
  simp only [lift, bind_ok]
  refine WP.spec_mono (LawfulStore.write_spec _ _ w1) fun s2 e2 => ?_
  subst e2
  have h0 : core.num.U64.wrapping_add x 0#u64 = x := by
    apply UScalar.eq_of_val_eq; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
  have c0 : CapW T Ω Sg x := h0 ▸ hx 0#u64 (by simp) (by simp)
  have c8 := hx 8#u64 (by simp) (by simp)
  have a8 : Aligned (core.num.U64.wrapping_add x 8#u64) := by
    unfold Aligned at ha ⊢; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  exact ((writesIn_wr ha).trans (writesIn_wr a8)).mono fun b hb => by
    rcases hb with e | e
    · exact e ▸ c0
    · exact e ▸ c8

/-- A cap's typing for its deletion (P3's `valid_cap`): `CapTyped`; IRQ
handler caps name IRQs below 128; I/O-port caps name ranges of 16-bit ports;
CNode and zombie caps name arrays of cap slots; thread caps name TCBs. -/
def DelCapOK (T Ω Sg : Set U64) (H : Heap) (Rp Nt : Set U64) (c : capability.Cap) : Prop :=
  CapTyped H Rp Nt c ∧ (∀ i, c = .IrqHandler i → i.val < 128) ∧
  (∀ f l o, c = .IoPort f l o → f.val ≤ l.val ∧ l.val < 65536) ∧
  (∀ p r g b, c = .CNode p r g b → SlotW T Ω Sg p ∧ ∀ i : U64, i.val < 2 ^ (r.val % 64) → SlotW T Ω Sg (slotIdx p i)) ∧
  (∀ p t n, c = .Zombie p t n → SlotW T Ω Sg p ∧ ∀ i : U64, i.val < n.val → SlotW T Ω Sg (slotIdx p i)) ∧
  (∀ p, c = .Thread p → p ∈ T)

theorem DelCapOK.null : DelCapOK T Ω Sg H Rp Nt .Null := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all

/-- The finalisation steps (P3's), each `Cur0` in and `Cur0` out: the caps
in cap slots are typed for deletion (`DelCapOK`); each typed cap's
finalisation, with typed remainder and cleanup caps; the deferred delete of
a cap slot; emptying a cap slot with its CDT unlinking and the typed cleanup
cap's `post_cap_deletion`; and the CDT's `NEXT` links of cap slots name cap
slots.  QueueDelFin proves this from placement (`DelPlace`) and the named
per-kind finalisations (`FinGaps`). -/
structure DelGapsAt (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (s0 : S) : Prop where
  cap : ∀ (Ac : Set U64) (s : S) (x : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    SlotW T Ω Sg x → obj.Slot.cap st x s ⦃ c => DelCapOK T Ω Sg H Rp Nt c ∧ FinPl st Scs s c ⦄
  fin : ∀ (Ac : Set U64) (s : S) (a : A) (c : capability.Cap) (fin : Bool),
    Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s → DelCapOK T Ω Sg H Rp Nt c → FinPl st Scs s c →
    objects.finalise_cap st ar s a c fin false ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧
      DelCapOK T Ω Sg H Rp Nt r.1.1 ∧ DelCapOK T Ω Sg H Rp Nt r.1.2 ⦄
  deferred : ∀ (Ac : Set U64) (s : S) (a : A) (x : U64), Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s →
    SlotW T Ω Sg x → cdt.delete_deferred st ar s a x ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄
  empty : ∀ (Ac : Set U64) (s : S) (a : A) (x : U64) (c : capability.Cap),
    Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s → SlotW T Ω Sg x → DelCapOK T Ω Sg H Rp Nt c →
    cdt.empty_slot st ar s a x c ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ⦄
  next : ∀ (Ac : Set U64) (s : S) (x : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    SlotW T Ω Sg x → obj.Slot.next st x s ⦃ n => n = 0#u64 ∨ SlotW T Ω Sg n ⦄

/-- The deletion gaps at every decode start reached from a `P3Ok` entry. -/
def DelGaps (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (P3Ok : S → Prop) : Prop :=
  ∀ s0, EntAt st P3Ok s0 → DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0
theorem zombie_last {T Ω Sg : Set U64} {H : Heap} {Rp Nt : Set U64} {p t n : U64}
    (hc : DelCapOK T Ω Sg H Rp Nt (.Zombie p t n)) (hn : n ≠ 0#u64) :
    SlotW T Ω Sg (slotIdx p (core.num.U64.wrapping_sub n 1#u64)) := by
  refine (hc.2.2.2.2.1 p t n rfl).2 _ ?_
  have : n.val ≠ 0 := fun e => hn (UScalar.eq_of_val_eq (by simpa using e))
  simp [core.num.U64.wrapping_sub_val_eq, U64.size_def, U64.numBits]; omega

set_option hygiene false in
/-- The preemption-point tail of a loop round (`Cur0` at `s2`). -/
local macro "pptail" : tactic => `(tactic| (
  refine WP.spec_bind (sched.preemption_point.cur0 hA h2) ?_
  rintro ⟨rr, s3, a3⟩ h3
  try simp only [WP.uncurry'_pair] at h3 ⊢
  try simp only [uncurry_apply_pair] at h3 ⊢
  rcases rr with _ | ee
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok]
    refine (WP.spec_ok _).2 ⟨h3, ?_⟩
    show fuel1.val < fuel.val
    omega
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    first | exact (WP.spec_ok _).2 h3 | exact h3 | exact (WP.spec_ok _).2 ⟨h3, by intro v hv; simp_all⟩ |
      exact ⟨h3, by intro v hv; simp_all⟩))

set_option maxHeartbeats 4000000 in
theorem cdt.finalise_slot_immediate.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {s0 s : S} (G : DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) {a : A} {x : U64}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : SlotW T Ω Sg x) :
    cdt.finalise_slot_immediate st ar s a x ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧
      ∀ v, r.1 = .Ok v → DelCapOK T Ω Sg H Rp Nt v.cleanup ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.finalise_slot_immediate cdt.finalise_slot_immediate_loop
  apply loop.spec_decr_nat (measure := fun y => y.2.2.val)
    (inv := fun y => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 y.1)
  · rintro ⟨s1, a1, fuel⟩ h1
    simp only at h1
    dsimp only
    unfold cdt.finalise_slot_immediate_loop.body
    split
    swap
    · exact (WP.spec_ok _).2 ⟨h1, by intro v hv; simp_all⟩
    rename_i hf
    step as ⟨fuel1, hf1⟩
    obtain ⟨Acx, hbx⟩ := h1.bxi
    refine WP.spec_bind (G.cap Acx s1 x h1.fr hbx hx) fun c ⟨hc, hpl⟩ => ?_
    refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h1, fun v hv => by cases hv; exact DelCapOK.null⟩
    refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s1 x c hS) fun fin _ => ?_
    refine WP.spec_bind (G.fin Ac s1 a1 c fin h1 hc hpl) ?_
    rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨h2', hrem, hcl⟩
    try simp only [uncurry_apply_pair, WP.uncurry'_pair]
    refine WP.spec_bind (cdt.cap_removable.zombie rem x) fun br hbr => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h2', fun v hv => by cases hv; exact hcl⟩
    rename_i hbr0
    have hbr' := hbr (by simpa using hbr0)
    refine WP.spec_bind (obj.Slot.set_cap.capw (c := rem) (s := s2) hx) fun s2' w2 => ?_
    have h2 := h2'.capw7 w2 fun _ hb => hb
    have hf' : 0 < fuel.val := by simpa using hf
    split
    all_goals try pptail
    -- the zombie: the deferred delete of its last slot, then the count
    simp only [lift, bind_ok]
    rename_i zp zt zn
    have hen := zombie_last hrem (hbr' zp zt zn rfl)
    unfold obj.Slot.index
    simp only [lift, bind_ok, cte_size]
    refine WP.spec_bind (G.deferred Ac s2' a2 _ h2 hen) ?_
    rintro ⟨r, s3, a3⟩ h3
    try simp only [uncurry_apply_pair] at h3 ⊢
    rcases r with _ | e
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      refine WP.spec_bind (P0.obj.Slot.cap.p0 st x s3 hS) fun c _ => ?_
      have SC : ∀ c', obj.Slot.set_cap st x s3 c' ⦃ s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := fun c' =>
        WP.spec_mono (obj.Slot.set_cap.capw hx) fun s' w => h3.capw7 w fun _ hb => hb
      refine WP.spec_bind (Pₘ := fun r : S × A => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1) ?_ ?_
      · split
        all_goals try exact (WP.spec_ok _).2 h3
        split
        · split
          · refine WP.spec_bind (Pₘ := fun s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s') ?_
              fun s' h' => (WP.spec_ok _).2 h'
            split
            · try simp only [lift, bind_ok]
              exact SC _
            · exact (WP.spec_ok _).2 h3
          · exact (WP.spec_ok _).2 h3
        · exact (WP.spec_ok _).2 h3
      · rintro ⟨s4, a4⟩ h2
        try simp only [uncurry_apply_pair] at h2 ⊢
        pptail
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      exact (WP.spec_ok _).2 ⟨h3, by intro v hv; simp_all⟩
  · exact h

/-- `cdt.delete` (exposed) of a cap slot. -/
theorem cdt.delete.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {s0 s : S} (G : DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) {a : A} {x : U64}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : SlotW T Ω Sg x) :
    cdt.delete st ar s a x true ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄ := by
  unfold cdt.delete
  simp only [↓reduceIte]
  refine WP.spec_bind (cdt.finalise_slot_immediate.cur0 hA G h hx) ?_
  rintro ⟨r, s1, a1⟩ ⟨h1, hv1⟩
  try simp only [uncurry_apply_pair] at h1 hv1 ⊢
  rcases r with v | e
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    refine WP.spec_bind (G.empty Ac s1 a1 x _ h1 hx (hv1 v rfl)) ?_
    rintro ⟨s2, a2⟩ h2
    try simp only [uncurry_apply_pair] at h2 ⊢
    exact (WP.spec_ok _).2 h2
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 h1

set_option maxHeartbeats 2000000 in
/-- `cdt.revoke` of a cap slot. -/
theorem cdt.revoke.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {s0 s : S} (G : DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) {a : A} {x : U64}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : SlotW T Ω Sg x) :
    cdt.revoke st ar s a x ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.revoke cdt.revoke_loop
  apply loop.spec_decr_nat (measure := fun y => y.2.2.val)
    (inv := fun y => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 y.1)
  · rintro ⟨s1, a1, fuel⟩ h1
    simp only at h1
    dsimp only
    unfold cdt.revoke_loop.body
    split
    swap
    · exact (WP.spec_ok _).2 h1
    rename_i hf
    have hf' : 0 < fuel.val := by simpa using hf
    step as ⟨fuel1, hf1⟩
    have h1' := h1
    obtain ⟨-, Acx, hbx, -, -, -, -, -⟩ := h1'
    refine WP.spec_bind (G.next Acx s1 x h1.fr hbx hx) fun nx hnx => ?_
    simp only [obj.Slot.is_null, bind_ok]
    split
    · exact (WP.spec_ok _).2 h1
    rename_i hn0
    have hnW : SlotW T Ω Sg nx := hnx.resolve_left (by simpa using hn0)
    refine WP.spec_bind (P0.cdt.is_mdb_parent_of.p0 st s1 x nx hS) fun bp _ => ?_
    split
    · refine WP.spec_bind (cdt.delete.cur0 hA G h1 hnW) ?_
      rintro ⟨r, s2', a2⟩ h2
      try simp only [uncurry_apply_pair] at h2 ⊢
      rcases r with _ | e
      · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        refine WP.spec_bind (sched.preemption_point.cur0 hA h2) ?_
        rintro ⟨rr, s3, a3⟩ h3
        try simp only [uncurry_apply_pair] at h3 ⊢
        rcases rr with _ | ee
        · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok]
          refine (WP.spec_ok _).2 ⟨h3, ?_⟩
          show fuel1.val < fuel.val
          omega
        · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
            bind_tc_ok]
          exact (WP.spec_ok _).2 h3
      · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
          bind_tc_ok]
        exact (WP.spec_ok _).2 h2
    · exact (WP.spec_ok _).2 h1
  · exact h

/-- **CNode `Delete`** from `DelGaps`. -/
theorem cnode_del {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {s : S} (G : DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s) {a : A} {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {x : U64}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hx : SlotW T Ω Sg x) :
    (do
      let s1 ← sched.set_thread_state st s (L.curW s) sched.TS_RESTART
      cdt.delete st ar s1 a x true) ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ :=
  WP.spec_bind (Cur0.restart D) fun s1 h1 => WP.spec_mono (cdt.delete.cur0 hA G h1 hx) fun r hr => by
    obtain ⟨r', s', a'⟩ := r; exact hr.post

/-- **CNode `Revoke`** from `DelGaps`. -/
theorem cnode_rev {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {s : S} (G : DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s) {a : A} {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {x : U64}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hx : SlotW T Ω Sg x) :
    (do
      let s1 ← sched.set_thread_state st s (L.curW s) sched.TS_RESTART
      cdt.revoke st ar s1 a x) ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ :=
  WP.spec_bind (Cur0.restart D) fun s1 h1 => WP.spec_mono (cdt.revoke.cur0 hA G h1 hx) fun r hr => by
    obtain ⟨r', s', a'⟩ := r; exact hr.post

set_option hygiene false in
local macro "errleaf2" : tactic => `(tactic| first
  | exact D.err _
  | exact (WP.spec_ok _).2 (D.err _)
  | (simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, error.illegal, error.truncated, cnode.missing_source]
     first | exact D.err _ | exact (WP.spec_ok _).2 (D.err _)))

set_option maxHeartbeats 4000000 in
/-- **`cnode.decode`**, Delete and Revoke included. -/
theorem cnode.decode.dec2 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (C : CdtHyps2 st T Cs Ω H Sg Rp Scs Nt Z P3Ok) {s : S} (G : DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s)
    {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) (lbl len buf : U64)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hE : EntAt st P3Ok s) (c : capability.Cap) :
    cnode.decode st ar s a lbl len c buf extra ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cnode.decode
  simp only [error.illegal, error.truncated, bind_ok]
  split
  · errleaf2
  split
  · errleaf2
  split
  · errleaf2
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun idx _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun dep _ => ?_
  refine WP.spec_bind (WP.spec_and (C.tgt Ac s c idx dep hE D.bxi) (C.tgtW Ac s c idx dep hE D.bxi)) fun r hr => ?_
  rcases r with v | e
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    errleaf2
  have hv := hr.1 v rfl
  have hvW := slotW_to7 (hr.2 v rfl)
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  repeat' (first
    | exact (WP.spec_ok _).2 (D.err _)
    | exact lift2 (cnode.decode_copy.dec C.toCdtHyps lbl len buf v D hE hv)
    | exact lift2 (cnode.decode_cancel_badged_sends.dec C.toCdtHyps v D hE hv)
    | exact lift2 (cnode.decode_rotate.dec C.toCdtHyps len buf v D hE hv)
    | exact cnode_del hA G D hvW
    | exact cnode_rev hA G D hvW
    | split)

/-- **InvGaps' `cnode`, discharged** from `CdtHyps2` and `DelGaps`. -/
theorem decGap_cnode2 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (C : CdtHyps2 st T Cs Ω H Sg Rp Scs Nt Z P3Ok) (G : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) :
    DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .cnode := by
  intro Ac s a lbl len slot cap blk call don fp buf extra hf D _hslot hE
  cases cap <;> simp [capFam] at hf
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec as ⟨ct, _⟩
  try dsimp only
  split
  · exact (WP.spec_ok _).2 (DecPost.keep D.bxi (by simp))
  · exact cnode.decode.dec2 hA C (G s hE) a lbl len buf D hE _



theorem delCapOK_to7 {c : capability.Cap} (h : Fl4ProofsA64.P1.DelCapOK T Ω Sg H Rp Nt c) :
    DelCapOK T Ω Sg H Rp Nt c :=
  ⟨h.1, h.2.1, h.2.2.1,
    fun p r g b e => ⟨slotW_to7 (h.2.2.2.1 p r g b e).1, fun i hi => slotW_to7 ((h.2.2.2.1 p r g b e).2 i hi)⟩,
    fun p t n e => ⟨slotW_to7 (h.2.2.2.2.1 p t n e).1, fun i hi => slotW_to7 ((h.2.2.2.2.1 p t n e).2 i hi)⟩,
    h.2.2.2.2.2⟩

/-- A W7-typed cap that is no CNode and no Zombie is typed in the x86_64 sense. -/
theorem delCapOK_of7 {c : capability.Cap} (h : DelCapOK T Ω Sg H Rp Nt c)
    (hc : ∀ p r g b, c ≠ .CNode p r g b) (hz : ∀ p t n, c ≠ .Zombie p t n) :
    Fl4ProofsA64.P1.DelCapOK T Ω Sg H Rp Nt c :=
  ⟨h.1, h.2.1, h.2.2.1, fun p r g b e => absurd e (hc p r g b), fun p t n e => absurd e (hz p t n), h.2.2.2.2.2⟩

/-- **The finalisation shape**: `finalise_cap` of a typed cap with `P`, from
`Cur0` to `Cur0`, with typed remainder and cleanup caps. -/
def FinGap (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A) (T Cs Ω : Set U64)
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (P : capability.Cap → Prop) : Prop :=
  ∀ (Ac : Set U64) (s0 s : S) (a : A) (c : capability.Cap) (fin : Bool),
    Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s → DelCapOK T Ω Sg H Rp Nt c → FinPl st Scs s c → P c →
    objects.finalise_cap st ar s a c fin false ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧
      DelCapOK T Ω Sg H Rp Nt r.1.1 ∧ DelCapOK T Ω Sg H Rp Nt r.1.2 ⦄

/-- `FinGap` from one decode start `s0`. -/
def FinGapAt (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A) (T Cs Ω : Set U64)
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (P : capability.Cap → Prop) (s0 : S) : Prop :=
  ∀ (Ac : Set U64) (s : S) (a : A) (c : capability.Cap) (fin : Bool),
    Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s → DelCapOK T Ω Sg H Rp Nt c → FinPl st Scs s c → P c →
    objects.finalise_cap st ar s a c fin false ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧
      DelCapOK T Ω Sg H Rp Nt r.1.1 ∧ DelCapOK T Ω Sg H Rp Nt r.1.2 ⦄

theorem FinGap.at {A : Type _} {ar : machine.Arch A} {P : capability.Cap → Prop}
    (g : FinGap st ar T Cs Ω H Sg Rp Scs Nt Z P) (s0 : S) : FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z P s0 :=
  fun Ac s a c fin => g Ac s0 s a c fin

theorem fin_noop {A : Type _} {ar : machine.Arch A} {s0 s : S} {a : A} {c : capability.Cap} {fin : Bool}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (hc : c = .Null ∨ (∃ x y z w, c = .Untyped x y z w) ∨ c = .IrqControl ∨ c = .Domain ∨
      (∃ x, c = .SchedControl x) ∨ c = .AsidControl ∨ c = .IoPortControl ∨ c = .TdxControl) :
    objects.finalise_cap st ar s a c fin false ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧
      DelCapOK T Ω Sg H Rp Nt r.1.1 ∧ DelCapOK T Ω Sg H Rp Nt r.1.2 ⦄ := by
  rcases hc with rfl | ⟨_, _, _, _, rfl⟩ | rfl | rfl | ⟨_, rfl⟩ | rfl | rfl | rfl <;>
    simp [objects.finalise_cap, objects.finalise_cap_object, h, DelCapOK.null]

theorem fin_cnode {A : Type _} {ar : machine.Arch A} {s0 s : S} {a : A} {p r g b : U64} {fin : Bool}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hc : DelCapOK T Ω Sg H Rp Nt (.CNode p r g b)) :
    objects.finalise_cap st ar s a (.CNode p r g b) fin false ⦃ x => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 x.2.1 ∧
      DelCapOK T Ω Sg H Rp Nt x.1.1 ∧ DelCapOK T Ω Sg H Rp Nt x.1.2 ⦄ := by
  obtain ⟨hp, hi⟩ := hc.2.2.2.1 p r g b rfl
  simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok]
  split
  · simp only [lift, bind_ok]
    step as ⟨n, hn⟩
    refine ⟨h, ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, DelCapOK.null⟩ <;> try (intros; simp_all; done)
    intro p' t' n' e
    simp only [capability.Cap.Zombie.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    refine ⟨hp, fun i hlt => hi i ?_⟩
    have : (r &&& 63#u64).val = r.val % 64 := by
      simp [UScalar.val_and]; exact Nat.and_two_pow_sub_one_eq_mod r.val 6
    rw [hn, this] at hlt; exact hlt
  · exact (WP.spec_ok _).2 ⟨h, DelCapOK.null, DelCapOK.null⟩

theorem fin_zombie {A : Type _} {ar : machine.Arch A} {s0 s : S} {a : A} {p t n : U64} {fin : Bool}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hc : DelCapOK T Ω Sg H Rp Nt (.Zombie p t n)) :
    objects.finalise_cap st ar s a (.Zombie p t n) fin false ⦃ x => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 x.2.1 ∧
      DelCapOK T Ω Sg H Rp Nt x.1.1 ∧ DelCapOK T Ω Sg H Rp Nt x.1.2 ⦄ := by
  simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok]
  exact (WP.spec_ok _).2 ⟨h, hc, DelCapOK.null⟩

/-- The placement facts of a deletion (P3's): the caps in cap slots are typed
for their deletion (`DelCapOK`); the CDT links of a cap slot are cap slots
or null; the VSpace lookups of the unmaps name VSpace words `V` (aligned
words of the other objects outside `Sg`), and so do the ASID tables. -/
structure DelPlaceAt (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (V : U64 → Prop) (s0 : S) : Prop where
  vs : VsOK Ω Sg V
  cap : ∀ (Ac : Set U64) (s : S) (x : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → SlotW T Ω Sg x →
    obj.Slot.cap st x s ⦃ c => DelCapOK T Ω Sg H Rp Nt c ∧ FinPl st Scs s c ⦄
  next : ∀ (Ac : Set U64) (s : S) (x : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → SlotW T Ω Sg x →
    obj.Slot.next st x s ⦃ n => n = 0#u64 ∨ SlotW T Ω Sg n ⦄
  prev : ∀ (Ac : Set U64) (s : S) (x : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → SlotW T Ω Sg x →
    obj.Slot.prev st x s ⦃ n => n = 0#u64 ∨ SlotW T Ω Sg n ⦄
  /-- a64: the slot the TTBR0/TTBR1 walk of `unmap_page_table` finds is a VSpace word. -/
  ptw : ∀ (Ac : Set U64) (s : S) (v pt table shift level : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s →
    BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    vspace.unmap_page_table_loop st s v pt table shift level ⦃ r => ∀ x, r = some x → V x ⦄
  /-- a64: the slot the Stage-2 walk (`ept.unmap_table_loop`) finds is a VSpace word. -/
  elw : ∀ (Ac : Set U64) (s : S) (v pt table shift mask rem : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s →
    BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    ept.unmap_table_loop st s v pt table shift mask rem ⦃ r => ∀ x, r = some x → V x ⦄
  /-- a64: `lookup_pt_slot`'s slot (`unmap_page`) is a VSpace word. -/
  ptslot : ∀ (Ac : Set U64) (s : S) (root v : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s →
    BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → vspace.lookup_pt_slot st s root v ⦃ lu => V lu.slot ⦄
  pool : ∀ (Ac : Set U64) (s : S) (asid i : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    vspace.asid_table st s i ⦃ pool => pool ≠ 0#u64 →
      V (core.num.U64.wrapping_add pool (core.num.U64.wrapping_mul (asid &&& 511#u64) 8#u64)) ⦄
  aset : ∀ (Ac : Set U64) (s : S) (hi : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    vspace.set_asid_table st s hi 0#u64 ⦃ s1 => WritesIn st s s1 V ⦄
  /-- **[J] (a64) `RunVcpuInv` along the deletion** (`EntryHyps0A.rvAt`'s kind): the AArch64 reply
  finalisation's donation needs the replier to run no VCPU (QueueFinCur `finGap_reply`). -/
  rv : ∀ (Ac : Set U64) (s : S), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    RunVcpuInv st T s
  /-- **[P] (a64) `rcw`**: a thread's run VCPU's `RUN_CALLER` word is a user word (`UserW`; the kind and shape
  of VcpuCheckInv's [P] `hpw`), so `vcpu::cancel_run` of a finalised thread in an `ARMVCPURun` writes no
  kernel-object word (QueueFinThr7 `finGap_thread`). -/
  rcw : ∀ (Ac : Set U64) (s : S) (p : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    p ∈ T → L.mem s (runVcpuA p) ≠ 0#u64 →
    UserW st T Cs Ω H s (core.num.U64.wrapping_add (L.mem s (runVcpuA p)) vcpu.RUN_CALLER)
  /-- An IRQ's handler slot holds no cap or a notification cap
  (`deleting_irq_handler`). -/
  irq : ∀ (Ac : Set U64) (s : S) (i : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → i.val < 128 →
    obj.Slot.cap st (irqSlotA (L.ksb s) i) s ⦃ c => c = .Null ∨ ∃ n b0 b1 b2, c = .Notification n b0 b1 b2 ⦄

/-- **The deletion placement facts** (P3's), at every decode start reached
from a `P3Ok` entry, along the decode's frame (`Fr0`). -/
def DelPlace (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (V : U64 → Prop) (P3Ok : S → Prop) : Prop :=
  ∀ s0, EntAt st P3Ok s0 → DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0

set_option maxHeartbeats 2000000 in
/-- The VSpace kinds QueueVsFin covers. a64: PageDirectory / Pdpt are `unmap_page_table` on AArch64, and
`HighVSpace` is `delete_asid` of the tagged root. -/
theorem fin_vs {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 s : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) {a : A} {c : capability.Cap} {fin : Bool}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (hc : (∃ x y z w, c = .PageTable x y z w) ∨ (∃ x y z w m asid vaddr, c = .Frame x y z w m false asid vaddr) ∨
      (∃ x y z, c = .Pml4 x y z) ∨ (∃ x y, c = .AsidPool x y) ∨ (∃ x y z w, c = .PageDirectory x y z w) ∨
      (∃ x y z w, c = .Pdpt x y z w) ∨ (∃ x y z, c = .HighVSpace x y z)) :
    objects.finalise_cap st ar s a c fin false ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧
      DelCapOK T Ω Sg H Rp Nt r.1.1 ∧ DelCapOK T Ω Sg H Rp Nt r.1.2 ⦄ := by
  have hb := h.bxi
  obtain ⟨Ac', hb⟩ := hb
  have W : ∀ (m : Result (S × A)), m ⦃ r => WritesIn st s r.1 V ⦄ →
      (do let (s1, a1) ← m; ok ((capability.Cap.Null, capability.Cap.Null), s1, a1)) ⦃ r =>
        Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧ DelCapOK T Ω Sg H Rp Nt r.1.1 ∧
        DelCapOK T Ω Sg H Rp Nt r.1.2 ⦄ := fun m hm =>
    WP.spec_bind hm fun r hr => by
      obtain ⟨s1, a1⟩ := r
      exact (WP.spec_ok _).2 ⟨h.vs P.vs hr, DelCapOK.null, DelCapOK.null⟩
  have K : (ok ((capability.Cap.Null, capability.Cap.Null), s, a) : Result _) ⦃ r =>
      Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧ DelCapOK T Ω Sg H Rp Nt r.1.1 ∧
      DelCapOK T Ω Sg H Rp Nt r.1.2 ⦄ := (WP.spec_ok _).2 ⟨h, DelCapOK.null, DelCapOK.null⟩
  have UPT : ∀ asid vaddr pt, vspace.unmap_page_table st ar s a asid vaddr pt ⦃ r => WritesIn st s r.1 V ⦄ :=
    fun asid vaddr pt => vspace.unmap_page_table.vs hA s a asid vaddr pt P.vs
      (fun table shift level => P.ptw Ac' s vaddr pt table shift level h.fr hb)
      (fun table shift mask rem => P.elw Ac' s vaddr pt table shift mask rem h.fr hb)
  rcases hc with ⟨x, y, z, w, rfl⟩ | ⟨x, y, z, w, m, asid, vaddr, rfl⟩ | ⟨x, y, z, rfl⟩ | ⟨x, y, rfl⟩ |
    ⟨x, y, z, w, rfl⟩ | ⟨x, y, z, w, rfl⟩ | ⟨x, y, z, rfl⟩
  · simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok]
    split
    · split
      · exact W _ (UPT z w x)
      · exact K
    · exact K
  · simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok, Bool.false_eq_true, ↓reduceIte]
    apply WP.spec_bind (Pₘ := fun r => WritesIn st s r.1 V)
    · split
      · split
        · exact vspace.unmap_page.vs hA s a y asid vaddr x P.vs (fun root => P.ptslot Ac' s root vaddr h.fr hb)
        · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
      · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
    · rintro ⟨s1, a1⟩ hw
      cases fin <;> cases w <;> simp only [↓reduceIte, Bool.false_eq_true, uncurry_apply_pair]
      all_goals first
        | exact (WP.spec_ok _).2 ⟨h.vs P.vs hw, DelCapOK.null, DelCapOK.null⟩
        | exact WP.spec_bind (P0.objects.retire_dma_frame.p0 st ar s1 a1 x y L.total hA) fun _ _ =>
            (WP.spec_ok _).2 ⟨h.vs P.vs hw, DelCapOK.null, DelCapOK.null⟩
  · simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok]
    split
    · split
      · exact W _ (vspace.delete_asid.vs hA s a z x P.vs fun i => P.pool Ac' s z i h.fr hb)
      · exact K
    · exact K
  · simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok]
    split
    · exact W _ (vspace.delete_asid_pool.vs hA s a y x fun hi => P.aset Ac' s hi h.fr hb)
    · exact K
  · simp only [objects.finalise_cap, objects.finalise_cap_object, vspace.unmap_page_directory, bind_ok]
    split
    · split
      · exact W _ (UPT z w x)
      · exact K
    · exact K
  · simp only [objects.finalise_cap, objects.finalise_cap_object, vspace.unmap_pdpt, bind_ok]
    split
    · split
      · exact W _ (UPT z w x)
      · exact K
    · exact K
  · simp only [objects.finalise_cap, objects.finalise_cap_object, lift, bind_ok]
    split
    · split
      · exact W _ (vspace.delete_asid.vs hA s a z _ P.vs fun i => P.pool Ac' s z i h.fr hb)
      · exact K
    · exact K

/-- The finalisations of the kinds this file does not prove, one shape
(`FinGap`): the endpoint, notification, reply, SC, thread and IRQ handler
kinds (QueueFinCur proves the endpoint, notification, reply and IRQ handler
ones), and the VCPU/EPT/I/O-port kinds (with EPT frames). -/
structure FinKindsAt (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (s0 : S) : Prop where
  ep : FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (fun c => ∃ x1 x2 x3 x4 x5 x6, c = .Endpoint x1 x2 x3 x4 x5 x6) s0
  ntfn : FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (fun c => ∃ x1 x2 x3 x4, c = .Notification x1 x2 x3 x4) s0
  reply : FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (fun c => ∃ x1 x2, c = .Reply x1 x2) s0
  sc : FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (fun c => ∃ x1 x2, c = .SchedContext x1 x2) s0
  thread : FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (fun c => ∃ x1, c = .Thread x1) s0
  irq : FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (fun c => ∃ x1, c = .IrqHandler x1) s0
  ioPort : FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (fun c => ∃ x1 x2 x3, c = .IoPort x1 x2 x3) s0
  /-- The VT-x kinds: VCPUs, EPTs and EPT frames. -/
  arch : FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (fun c => (∃ x1, c = .Vcpu x1) ∨
    (∃ x1 x2 x3 x4 x5, c = .Ept x1 x2 x3 x4 x5) ∨
    (∃ x1 x2 x3 x4 x5 x6 x7, c = .Frame x1 x2 x3 x4 x5 true x6 x7)) s0

/-- **Every cap kind's finalisation**, from `FinKinds`. -/
theorem fin_all {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (G : FinKindsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) :
    FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (fun _ => True) s0 := by
  intro Ac s a c fin h hc hpl _
  cases c with
  | Null => exact fin_noop h (Or.inl rfl)
  | Untyped => exact fin_noop h (Or.inr (Or.inl ⟨_, _, _, _, rfl⟩))
  | IrqControl => exact fin_noop h (Or.inr (Or.inr (Or.inl rfl)))
  | Domain => exact fin_noop h (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | SchedControl => exact fin_noop h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩)))))
  | AsidControl => exact fin_noop h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  | IoPortControl => exact fin_noop h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  | TdxControl => exact fin_noop h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))
  | CNode => exact fin_cnode h hc
  | Zombie => exact fin_zombie h hc
  | PageTable => exact fin_vs hA P h (Or.inl ⟨_, _, _, _, rfl⟩)
  | HighVSpace => exact fin_vs hA P h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, _, rfl⟩))))))  -- a64
  | Pml4 => exact fin_vs hA P h (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl⟩)))
  | AsidPool => exact fin_vs hA P h (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))))
  | Frame x1 x2 x3 x4 x5 e x6 x7 =>
    cases e
    · exact fin_vs hA P h (Or.inr (Or.inl ⟨_, _, _, _, _, _, _, rfl⟩))
    · exact G.arch _ _ _ _ _ h hc hpl (Or.inr (Or.inr ⟨_, _, _, _, _, _, _, rfl⟩))
  | Endpoint => exact G.ep _ _ _ _ _ h hc hpl ⟨_, _, _, _, _, _, rfl⟩
  | Notification => exact G.ntfn _ _ _ _ _ h hc hpl ⟨_, _, _, _, rfl⟩
  | Reply => exact G.reply _ _ _ _ _ h hc hpl ⟨_, _, rfl⟩
  | SchedContext => exact G.sc _ _ _ _ _ h hc hpl ⟨_, _, rfl⟩
  | Thread => exact G.thread _ _ _ _ _ h hc hpl ⟨_, rfl⟩
  | IrqHandler => exact G.irq _ _ _ _ _ h hc hpl ⟨_, rfl⟩
  | PageDirectory => exact fin_vs hA P h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl⟩)))))
  | Pdpt => exact fin_vs hA P h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl⟩))))))  -- a64
  | Vcpu => exact G.arch _ _ _ _ _ h hc hpl (Or.inl ⟨_, rfl⟩)
  | Ept => exact G.arch _ _ _ _ _ h hc hpl (Or.inr (Or.inl ⟨_, _, _, _, _, rfl⟩))
  | IoPort => exact G.ioPort _ _ _ _ _ h hc hpl ⟨_, _, _, rfl⟩
theorem slot_wr {s : S} {x o v : U64} (hx : SlotW T Ω Sg x) (ho : o.val < 32) (h8 : o.val % 8 = 0) :
    st.write s (core.num.U64.wrapping_add x o) v ⦃ s' => WritesIn st s s' (CapW T Ω Sg) ⦄ := by
  refine WP.spec_mono (LawfulStore.write_spec _ _ _) fun s' e => ?_
  subst e
  have ha : Aligned (core.num.U64.wrapping_add x o) := by
    have := hx.1
    unfold Aligned at this ⊢; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  exact (writesIn_wr ha).mono fun b e => e ▸ hx.2 o ho h8

theorem slot_wr0 {s : S} {x v : U64} (hx : SlotW T Ω Sg x) :
    st.write s x v ⦃ s' => WritesIn st s s' (CapW T Ω Sg) ⦄ := by
  have h0 : core.num.U64.wrapping_add x 0#u64 = x := by
    apply UScalar.eq_of_val_eq; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
  have := slot_wr (st := st) (s := s) (v := v) (o := 0#u64) hx (by simp) (by simp)
  rwa [h0] at this

theorem obj.Slot.set_next.capw {s : S} {x n : U64} (hx : SlotW T Ω Sg x) :
    obj.Slot.set_next st x s n ⦃ s' => WritesIn st s s' (CapW T Ω Sg) ⦄ := by
  unfold obj.Slot.set_next obj.Slot.next_word
  simp only [lift, bind_ok, cte_next]
  refine WP.spec_bind (LawfulStore.read_spec _ _) fun w _ => ?_
  exact slot_wr hx (by simp) (by simp)

theorem obj.Slot.set_prev.capw {s : S} {x n : U64} (hx : SlotW T Ω Sg x) :
    obj.Slot.set_prev st x s n ⦃ s' => WritesIn st s s' (CapW T Ω Sg) ⦄ := by
  unfold obj.Slot.set_prev
  simp only [lift, bind_ok, cte_prev]
  exact slot_wr hx (by simp) (by simp)

theorem obj.Slot.set_first_badged.capw {s : S} {x : U64} {v : Bool} (hx : SlotW T Ω Sg x) :
    obj.Slot.set_first_badged st x s v ⦃ s' => WritesIn st s s' (CapW T Ω Sg) ⦄ := by
  unfold obj.Slot.set_first_badged obj.Slot.next_word
  simp only [lift, bind_ok, cte_next]
  refine WP.spec_bind (LawfulStore.read_spec _ _) fun w _ => ?_
  refine WP.spec_bind P0.Consts.obj.MDB_FIRST_BADGED.spec fun i1 _ => ?_
  split <;> exact slot_wr hx (by simp) (by simp)

theorem obj.Slot.set_revocable.capw {s : S} {x : U64} {v : Bool} (hx : SlotW T Ω Sg x) :
    obj.Slot.set_revocable st x s v ⦃ s' => WritesIn st s s' (CapW T Ω Sg) ⦄ := by
  unfold obj.Slot.set_revocable obj.Slot.next_word
  simp only [lift, bind_ok, cte_next]
  refine WP.spec_bind (LawfulStore.read_spec _ _) fun w _ => ?_
  refine WP.spec_bind P0.Consts.obj.MDB_REVOCABLE.spec fun i1 _ => ?_
  split <;> exact slot_wr hx (by simp) (by simp)

theorem obj.Slot.set_next_flags.capw {s : S} {x n : U64} {r f : Bool} (hx : SlotW T Ω Sg x) :
    obj.Slot.set_next_flags st x s n r f ⦃ s' => WritesIn st s s' (CapW T Ω Sg) ⦄ := by
  unfold obj.Slot.set_next_flags obj.Slot.next_word
  simp only [lift, bind_ok, cte_next]
  refine WP.spec_bind (LawfulStore.read_spec _ _) fun w _ => ?_
  refine WP.spec_bind P0.Consts.obj.MDB_REVOCABLE.spec fun i1 _ => ?_
  refine WP.spec_bind P0.Consts.obj.MDB_FIRST_BADGED.spec fun i3 _ => ?_
  refine WP.spec_bind (Pₘ := fun _ => True) (by split <;> exact (WP.spec_ok _).2 trivial) fun _ _ => ?_
  refine WP.spec_bind (Pₘ := fun _ => True) (by split <;> exact (WP.spec_ok _).2 trivial) fun _ _ => ?_
  exact slot_wr hx (by simp) (by simp)

theorem obj.Slot.clear.capw {s : S} {x : U64} (hx : SlotW T Ω Sg x) :
    obj.Slot.clear st x s ⦃ s' => WritesIn st s s' (CapW T Ω Sg) ⦄ := by
  unfold obj.Slot.clear
  simp only [lift, bind_ok]
  refine WP.spec_bind (slot_wr0 hx) fun s1 w1 => ?_
  refine WP.spec_bind (slot_wr hx (o := 8#u64) (by simp) (by simp)) fun s2 w2 => ?_
  refine WP.spec_bind (slot_wr hx (o := 16#u64) (by simp) (by simp)) fun s3 w3 => ?_
  exact WP.spec_mono (slot_wr hx (o := 24#u64) (by simp) (by simp)) fun s4 w4 =>
    ((w1.trans1 w2).trans1 w3).trans1 w4
theorem objects.post_cap_deletion.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s0 s : S} {a : A}
    {c : capability.Cap} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hc : DelCapOK T Ω Sg H Rp Nt c) :
    objects.post_cap_deletion st ar s a c ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ⦄ := by
  unfold objects.post_cap_deletion
  cases c
  all_goals try exact (WP.spec_ok _).2 h
  · rename_i irq
    have hi := hc.2.1 irq rfl
    unfold interrupt.deleted_irq_handler
    refine WP.spec_bind (Pₘ := fun r : S × A => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1) ?_ ?_
    · unfold interrupt.set_irq_state interrupt.state_off
      simp only [lift, bind_ok]
      refine WP.spec_bind (Pₘ := fun o : U64 => o.val = 224 + 8 * irq.val) ?_ fun o ho => ?_
      · refine WP.spec_bind P0.Consts.layout.ks.IRQ_STATE.spec fun b eb => ?_
        subst eb
        refine (WP.spec_ok _).2 ?_
        simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]; omega
      refine WP.spec_bind (h.ks (v := interrupt.IRQ_INACTIVE) (by omega) (by omega)) fun s1 h1 => ?_
      exact WP.spec_bind (hA.mask_irq a irq _) fun a1 _ => (WP.spec_ok _).2 h1
    rintro ⟨s1, a1⟩ h1
    exact WP.spec_bind (hA.irq_free a1 irq) fun a2 _ => (WP.spec_ok _).2 h1
  · rename_i f l o
    obtain ⟨hfl, hl⟩ := hc.2.2.1 f l o rfl
    unfold ioport.free_ioports
    exact WP.spec_bind (ioport.set_mask.cur0 h hl hfl) fun s1 h1 => (WP.spec_ok _).2 h1

set_option maxHeartbeats 1000000 in
/-- **`empty_slot`** of a cap slot, its cleanup cap typed. -/
theorem cdt.empty_slot.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 s : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) {a : A} {x : U64} {c : capability.Cap}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : SlotW T Ω Sg x) (hc : DelCapOK T Ω Sg H Rp Nt c) :
    cdt.empty_slot st ar s a x c ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  obtain ⟨Ac', hb⟩ := h.bxi
  unfold cdt.empty_slot
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st x s hS) fun c0 _ => ?_
  refine WP.spec_bind (P0.capability.Cap.is_null.p0 c0) fun bn _ => ?_
  split
  · exact (WP.spec_ok _).2 h
  refine WP.spec_bind (P.prev Ac' s x h.fr hb hx) fun pv hpv => ?_
  refine WP.spec_bind (P.next Ac' s x h.fr hb hx) fun nx hnx => ?_
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st x s hS) fun fb _ => ?_
  simp only [obj.Slot.is_null, bind_ok]
  refine WP.spec_bind (Pₘ := fun s1 => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s1) ?_ fun s1 h1 => ?_
  · split
    · exact (WP.spec_ok _).2 h
    · rename_i hp0
      exact WP.spec_mono (obj.Slot.set_next.capw (hpv.resolve_left (by simpa using hp0))) fun s' w =>
        h.capw7 w fun _ hb => hb
  refine WP.spec_bind (Pₘ := fun s2 => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s2) ?_ fun s2 h2 => ?_
  · split
    · exact (WP.spec_ok _).2 h1
    · rename_i hn0
      have hnW := hnx.resolve_left (by simpa using hn0)
      refine WP.spec_bind (obj.Slot.set_prev.capw hnW) fun s3 w3 => ?_
      have h3 := h1.capw7 w3 fun _ hb => hb
      refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st nx s3 hS) fun nfb _ => ?_
      split <;> exact WP.spec_mono (obj.Slot.set_first_badged.capw hnW) fun s' w => h3.capw7 w fun _ hb => hb
  refine WP.spec_bind (obj.Slot.clear.capw hx) fun s3 w3 => ?_
  exact objects.post_cap_deletion.cur0 hA (h2.capw7 w3 fun _ hb => hb) hc
set_option maxHeartbeats 2000000 in
/-- **`cdt.swap`** of two cap slots. -/
theorem cdt.swap.cur0 {V : U64 → Prop} {s0 s : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0)
    {c1 c2 : capability.Cap} {x1 x2 : U64} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (h1 : SlotW T Ω Sg x1) (h2 : SlotW T Ω Sg x2) :
    cdt.swap st s c1 x1 c2 x2 ⦃ s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.swap
  refine WP.spec_bind (h.cw7 (obj.Slot.set_cap.capw h1)) fun sa ha => ?_
  refine WP.spec_bind (ha.cw7 (obj.Slot.set_cap.capw h2)) fun sb hb => ?_
  obtain ⟨Acb, hbb⟩ := hb.bxi
  refine WP.spec_bind (P.prev Acb sb x1 hb.fr hbb h1) fun p1 hp1 => ?_
  refine WP.spec_bind (P.next Acb sb x1 hb.fr hbb h1) fun n1 hn1 => ?_
  refine WP.spec_bind (P0.obj.Slot.revocable.p0 st x1 sb hS) fun r1 _ => ?_
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st x1 sb hS) fun f1 _ => ?_
  simp only [obj.Slot.is_null, bind_ok]
  refine WP.spec_bind (Pₘ := fun s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s') ?_ fun sc hc => ?_
  · split
    · exact (WP.spec_ok _).2 hb
    · rename_i e; exact hb.cw7 (obj.Slot.set_next.capw (hp1.resolve_left (by simpa using e)))
  refine WP.spec_bind (Pₘ := fun s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s') ?_ fun sd hd => ?_
  · split
    · exact (WP.spec_ok _).2 hc
    · rename_i e; exact hc.cw7 (obj.Slot.set_prev.capw (hn1.resolve_left (by simpa using e)))
  obtain ⟨Acd, hbd⟩ := hd.bxi
  refine WP.spec_bind (P.prev Acd sd x2 hd.fr hbd h2) fun p2 hp2 => ?_
  refine WP.spec_bind (P.next Acd sd x2 hd.fr hbd h2) fun n2 hn2 => ?_
  refine WP.spec_bind (P0.obj.Slot.revocable.p0 st x2 sd hS) fun r2 _ => ?_
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st x2 sd hS) fun f2 _ => ?_
  refine WP.spec_bind (hd.cw7 (obj.Slot.set_prev.capw h1)) fun s5 h5 => ?_
  refine WP.spec_bind (h5.cw7 (obj.Slot.set_next_flags.capw h1)) fun s6 h6 => ?_
  refine WP.spec_bind (h6.cw7 (obj.Slot.set_prev.capw h2)) fun s7 h7 => ?_
  refine WP.spec_bind (h7.cw7 (obj.Slot.set_next_flags.capw h2)) fun s12 h12 => ?_
  refine WP.spec_bind (Pₘ := fun s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s') ?_ fun s13 h13 => ?_
  · split
    · exact (WP.spec_ok _).2 h12
    · rename_i e; exact h12.cw7 (obj.Slot.set_next.capw (hp2.resolve_left (by simpa using e)))
  split
  · exact (WP.spec_ok _).2 h13
  · rename_i e; exact h13.cw7 (obj.Slot.set_prev.capw (hn2.resolve_left (by simpa using e)))

theorem cdt.cap_swap_for_delete.cur0 {V : U64 → Prop} {s0 s : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0)
    {x1 x2 : U64} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (h1 : SlotW T Ω Sg x1) (h2 : SlotW T Ω Sg x2) :
    cdt.cap_swap_for_delete st s x1 x2 ⦃ s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.cap_swap_for_delete obj.Slot.Insts.CoreCmpPartialEqSlot.eq
  simp only [bind_ok]
  split
  · exact (WP.spec_ok _).2 h
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st x1 s hS) fun c1 _ => ?_
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st x2 s hS) fun c2 _ => ?_
  exact cdt.swap.cur0 P h h1 h2

set_option hygiene false in
/-- The preemption-point tail of a deferred round (`Cur0` at `s3`). -/
local macro "dtail" : tactic => `(tactic| (
  refine WP.spec_bind (sched.preemption_point.cur0 hA h3) ?_
  rintro ⟨rr, s4, a4⟩ h4
  try simp only [uncurry_apply_pair] at h4 ⊢
  rcases rr with _ | ee
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok]
    refine (WP.spec_ok _).2 ⟨h4, ?_⟩
    show fuel1.val < fuel.val
    omega
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 ⟨h4, fun v hv => by cases hv⟩))

set_option maxHeartbeats 4000000 in
/-- **`finalise_slot_deferred`** of a cap slot: `Cur0`, the cleanup cap typed. -/
theorem cdt.finalise_slot_deferred.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 s : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (F : FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (fun _ => True) s0)
    {a : A} {x : U64} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : SlotW T Ω Sg x) :
    cdt.finalise_slot_deferred st ar s a x ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧
      ∀ v, r.1 = .Ok v → DelCapOK T Ω Sg H Rp Nt v.cleanup ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.finalise_slot_deferred cdt.finalise_slot_deferred_loop
  apply loop.spec_decr_nat (measure := fun y => y.2.2.val)
    (inv := fun y => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 y.1)
  · rintro ⟨s1, a1, fuel⟩ h1
    simp only at h1
    dsimp only
    unfold cdt.finalise_slot_deferred_loop.body
    split
    swap
    · exact (WP.spec_ok _).2 ⟨h1, fun v hv => by cases hv⟩
    rename_i hf
    have hf' : 0 < fuel.val := by simpa using hf
    step as ⟨fuel1, hf1⟩
    obtain ⟨Acx, hbx⟩ := h1.bxi
    refine WP.spec_bind (P.cap Acx s1 x h1.fr hbx hx) fun c ⟨hc, hpl⟩ => ?_
    refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h1, fun v hv => by cases hv; exact DelCapOK.null⟩
    refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s1 x c hS) fun fin _ => ?_
    refine WP.spec_bind (F Ac s1 a1 c fin h1 hc hpl trivial) ?_
    rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨h2', hrem, hcl⟩
    try simp only [uncurry_apply_pair]
    refine WP.spec_bind (P0.cdt.cap_removable.p0 rem x) fun br _ => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h2', fun v hv => by cases hv; exact hcl⟩
    refine WP.spec_bind (h2'.cw7 (obj.Slot.set_cap.capw (c := rem) hx)) fun s2 h2 => ?_
    refine WP.spec_bind (P0.cdt.cap_cyclic_zombie.p0 rem x) fun bz _ => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h2, fun v hv => by cases hv; exact hcl⟩
    refine WP.spec_bind (Pₘ := fun s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s') ?_ fun s3 h3 => ?_
    · split
      all_goals try exact (WP.spec_ok _).2 h2
      rename_i zp zt zn
      exact cdt.cap_swap_for_delete.cur0 P h2 (hrem.2.2.2.2.1 zp zt zn rfl).1 hx
    dtail
  · exact h

/-- **`delete_deferred`** of a cap slot. -/
theorem cdt.delete_deferred.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 s : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (F : FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (fun _ => True) s0)
    {a : A} {x : U64} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : SlotW T Ω Sg x) :
    cdt.delete_deferred st ar s a x ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄ := by
  unfold cdt.delete_deferred
  refine WP.spec_bind (cdt.finalise_slot_deferred.cur0 hA P F h hx) ?_
  rintro ⟨r, s1, a1⟩ ⟨h1, hv1⟩
  try simp only [uncurry_apply_pair] at h1 hv1 ⊢
  rcases r with v | e
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    split
    · refine WP.spec_bind (cdt.empty_slot.cur0 hA P h1 hx (hv1 v rfl)) ?_
      rintro ⟨s2, a2⟩ h2
      exact (WP.spec_ok _).2 h2
    · exact (WP.spec_ok _).2 h1
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 h1

/-- **`DelGaps`, discharged** from placement and the named finalisations. -/
theorem delGaps_of {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (G : FinKindsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) :
    DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0 where
  cap := P.cap
  fin Ac s a c fin h hc hpl := fin_all hA P G Ac s a c fin h hc hpl trivial
  deferred _ _ _ _ h hx := cdt.delete_deferred.cur0 hA P (fin_all hA P G) h hx
  empty _ _ _ _ _ h hx hc := cdt.empty_slot.cur0 hA P h hx hc
  next := P.next


end W7

end

end Fl4ProofsA64.P1
