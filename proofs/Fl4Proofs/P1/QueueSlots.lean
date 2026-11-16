/-
P1: writes to capability slots keep `BlkOK`.

The cap slots are words the invariants do not read: the low words of the
TCBs (below offset 192, the TCB's own slots) and, in the CNodes, words of
the other objects `Ω` outside the kernel-object words `Sg` (`CapW`).  A
change confined to such words keeps `BlkOK` (`blk_of_capw`), with every TCB
field from offset 192, every node word and every `Sg` word unchanged; so
the scheduler words of the current thread and the frames `PFr`/`Fr` hold
across it.  The P3 side gets `BlkOK` across `cdt::insert`, `empty_slot` and
the slot writes of a delete from its slot frames (`SlotFrame`) and the fact
that slot words are `CapW`.
-/
import Fl4Proofs.P1.QueueInvoke
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- The low words of the TCBs (below offset 192, where the TCB's cap slots
lie): no invariant reads them. -/
def TLow (T : Set U64) (b : U64) : Prop := ∃ t ∈ T, ∃ K : U64, K.val < 192 ∧ b = core.num.U64.wrapping_add t K

/-- Capability-slot words as the invariants see them: TCB low words, or
words of `Ω` outside `Sg`. -/
def CapW (T Ω Sg : Set U64) (b : U64) : Prop := TLow T b ∨ (b ∈ Ω ∧ b ∉ Sg)

/-- Every word below offset 192 of a TCB (its six cap slots) is a `TLow`
word (the Sc side's `TLowSlots`). -/
theorem tlow_slots : ∀ t ∈ T, ∀ K : U64, K.val < 192 → TLow T (core.num.U64.wrapping_add t K) :=
  fun t ht K hK => ⟨t, ht, K, hK, rfl⟩

theorem tlow_ne_field {y K b : U64} (hT : TcbPlaced T) (hy : y ∈ T) (hK0 : 192 ≤ K.val) (hK : K.val < 4096)
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
      192 ≤ K.val → L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
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
      192 ≤ K.val → L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
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
from offset 192, every node word of the cores and every frame word `Sg`
unchanged (so `PFr`, the current and idle threads, the current SC and the
scheduler action hold). -/
theorem blk_of_capw {s s' : S} {B : U64 → Prop} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hw : WritesIn st s s' B) (hB : ∀ b, B b → CapW T Ω Sg b) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ PFr st T Sg s s' ∧
      L.curW s' = L.curW s ∧ L.cscW s' = L.cscW s ∧ L.actionW s' = L.actionW s ∧
      (∀ y ∈ T, ∀ K : U64, 192 ≤ K.val → K.val < 4096 → K.val % 8 = 0 →
        L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o)) ∧
      (∀ b ∈ Sg, L.mem s' b = L.mem s b) := by
  obtain ⟨⟨Q, R, h0⟩, hBd, hX, hS, hSg⟩ := h
  have hT := h0.tcbs
  have hO := hX.1
  have hBw : ∀ b, B b → L.Free s Ω Cs b ∨ TLow T b := fun b hb =>
    (hB b hb).elim Or.inr fun h' => Or.inl (Or.inl h'.1)
  have fld : ∀ y ∈ T, ∀ K : U64, 192 ≤ K.val → K.val < 4096 → K.val % 8 = 0 →
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
  have hS' : SCsOK st T Ω Sg Scs Z Ac s' := by
    refine ⟨hS.sub, fun b hb => by rw [hw.1]; exact hS.ks b hb, fun o h1 h2 => by rw [hw.1]; exact hS.ksΩ o h1 h2,
      fun t ht hb hne => ?_, fun c hc => (hS.all c hc).agree sig,
      fun c hc => by rw [show L.rmax s' c = L.rmax s c from sig _ (hS.all c hc).2.1]; exact hS.act c hc,
      fun c hc h1 => hS.spor c hc (by rw [← sig _ (hS.spSg c hc)]; exact h1), hS.spSg,
      fun c hc h1 => hS.rep c hc (by rw [← sig _ (hS.repSg c hc)]; exact h1), hS.repSg⟩
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

/-! ## The footprint words are no slot words (P3's `KWOut`) -/

/-- No word of the footprint `KW` lies in the 8 bytes of a cap-slot word. -/
theorem capw_not_kw {s : S} {w b : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hw : CapW T Ω Sg w)
    (hwa : Aligned w) (h1 : w.val ≤ b.val) (h2 : b.val < w.val + 8)
    (hk : KW st T Cs Sg Scs Z (EH H) s b) : False := by
  obtain ⟨⟨Q, R, h0⟩, -, hX, hS, hSg⟩ := h
  have hT := h0.tcbs
  have hO := hX.1
  unfold Aligned at hwa
  have same : Aligned b → b = w := fun hb => by
    unfold Aligned at hb; exact UScalar.eq_of_val_eq (by omega)
  have notSg : ∀ x, CapW T Ω Sg x → x ∈ Sg → False := fun x hx hs =>
    hx.elim (fun hl => tlow_ne_out hT (h0.omega _ (hSg.sub _ hs)) hl) (fun h' => h'.2 hs)
  rcases hk with ⟨y, hy, K, hK1, hK2, -, -, rfl⟩ | ⟨c, hc, o, ho, -, rfl⟩ | hs | ⟨c, hc, hin⟩ | ⟨e, he, he'⟩
  · have hyv := field_val (hT y hy) hK2
    have ya : y.val % 4096 = 0 := (hT y hy).align
    rcases hw with ⟨t, ht, K', hK', rfl⟩ | ⟨hm, -⟩
    · have tv := field_val (hT t ht) (by omega : K'.val < 4096)
      have ta : t.val % 4096 = 0 := (hT t ht).align
      omega
    · have := (h0.omega _ hm).2.1 y hy
      have e12 : (2 : Nat) ^ 12 = 4096 := rfl
      omega
  · have hN := h0.nodes c hc
    have nv := nodeAt_val hN ho
    have na := hN.align
    rcases hw with ⟨t, ht, K', hK', rfl⟩ | ⟨hm, -⟩
    · have tv := field_val (hT t ht) (by omega : K'.val < 4096)
      have := hN.disj t ht
      have e12 : (2 : Nat) ^ 12 = 4096 := rfl
      omega
    · have := (h0.omega _ hm).2.2 c hc
      omega
  · have := same (h0.omega _ (hSg.sub b hs)).1
    subst this
    exact notSg b hw hs
  · obtain ⟨hP, hz⟩ := hO.sc c hc
    have := sc_lo hP hz
    have hwin : InSC c (Z c) w := by unfold InSC at hin ⊢; omega
    exact notSg w hw ((hS.all c hc).2.2 w hwa hwin)
  · obtain ⟨E, EQ, w1, -, w5, -, -, ty⟩ := h0.eps
    have heE : e ∈ E := (ty.2.2.1 e).2 he
    obtain ⟨hE, hEN, -⟩ := w1 e heE
    obtain ⟨a1, a2⟩ := ep_aligned hE
    obtain ⟨o1, o2⟩ := ep_out hE hEN
    rcases he' with rfl | rfl
    · have := same a1; subst this
      rcases hw with hl | ⟨hm, -⟩
      · exact tlow_ne_out hT o1 hl
      · have := w5 e heE _ hm; rw [epHeadA_val] at this; omega
    · have := same a2; subst this
      rcases hw with hl | ⟨hm, -⟩
      · exact tlow_ne_out hT o2 hl
      · have := w5 e heE _ hm; rw [epTSA_val hE] at this; omega

theorem slot_word_val {a o : U64} (hfit : a.val + 32 ≤ 2 ^ 64) (ho : o.val < 32) :
    (core.num.U64.wrapping_add a o).val = a.val + o.val := by
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega

/-- **The footprint words lie outside a slot whose four words are cap-slot
words** (P3's `KWOut` for that slot). -/
theorem kw_out_slot {s : S} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) {a : U64} (ha : Aligned a)
    (hfit : a.val + 32 ≤ 2 ^ 64)
    (hcw : ∀ o : U64, o.val < 32 → o.val % 8 = 0 → CapW T Ω Sg (core.num.U64.wrapping_add a o)) :
    ∀ b, KW st T Cs Sg Scs Z (EH H) s b → ¬ (a.val ≤ b.val ∧ b.val < a.val + 32) := by
  rintro b hk ⟨h1, h2⟩
  unfold Aligned at ha
  have key : ∀ o : U64, o.val < 32 → o.val % 8 = 0 → a.val + o.val ≤ b.val → b.val < a.val + o.val + 8 → False :=
    fun o ho h8 l1 l2 => by
      have hv := slot_word_val hfit ho
      exact capw_not_kw h (hcw o ho h8) (by unfold Aligned; rw [hv]; omega) (by rw [hv]; exact l1)
        (by rw [hv]; exact l2) hk
  by_cases e0 : b.val < a.val + 8
  · exact key 0#u64 (by simp) (by simp) (by simp; omega) (by simp; omega)
  by_cases e1 : b.val < a.val + 16
  · exact key 8#u64 (by simp) (by simp) (by simp; omega) (by simp; omega)
  by_cases e2 : b.val < a.val + 24
  · exact key 16#u64 (by simp) (by simp) (by simp; omega) (by simp; omega)
  · exact key 24#u64 (by simp) (by simp) (by simp; omega) (by simp; omega)

end

end Fl4Proofs.P1
