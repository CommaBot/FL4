/-
P3 (DESIGN.md §9): **the joint placement invariant** linking P3's typed
heap `th` (CNodes, TCBs, other objects; `Placed th`) to P1's typed heap `H`
(`HeapOK H`, with P1's object sets taken from it: `(Heap.tcbs H)`, `(Heap.omega H)`,
`(Heap.frame H)`, `(Heap.replies H)`, `(Heap.scs H)`, `(Heap.ntfns H)`, `(Heap.scBits H)`).

* `JPlaced th H Tr C s σ`: both heaps placed; a TCB of `th` is a TCB of `H`
  and conversely, a CNode of radix `r` is an object of `2 ^ (r + 5)` bytes of
  `H`; the TCBs are among the scheduler relation's `Tr`, the spec's SCs
  among `C` and `H`'s SCs; every cap in a slot names objects of the right
  kind (P1's `CapTyped`), and the fault-handler slots hold the null or an
  endpoint cap (l4v `valid_fault_handler`).
* Derived: `hTh`/`hTr` (`JPlaced.tcbT`, `JPlaced.tcbTr`), `ScSetsHyp`
  (`JPlaced.scSets`), `FhSlotHyp` (`JPlaced.fhSlot`), `KWOut`
  (`JPlaced.kwOut`, with the nodes and `Ω` facts of P1's `BlkOK`),
  `SlotCapW` (`JPlaced.slotCapW`, given P1's TCB low words cover the six
  TCB slots, `TLowSlots`), and the CSpace side's `NtfnP1Hyp`/`ReplyP1Hyp`
  from the invariant at every related state (`JointInv`).
-/
import Fl4Proofs.P3.ScInstPost
import Fl4Proofs.P3.DelObjK
import Fl4Proofs.P1.QueueHeap
import Fl4Proofs.P1.QueueRecv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P3 Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **The joint placement invariant** (module docstring). -/
structure JPlaced (th : TypedHeap) (H : Heap) (Tr C : Set U64) (s : S) (σ : Fl4Spec.State Unit) : Prop where
  heap : HeapOK H
  pl : Placed th
  tcb : ∀ t, th t = some .tcb ↔ H t = some .tcb
  cnode : ∀ p r, th p = some (.cnode r) → H p = some (.other (r + 5))
  tr : ∀ t, th t = some .tcb → t ∈ Tr
  sc : ∀ (c : U64) y n, c ≠ 0#u64 → σ.kheap c.bv = some (.schedContext y n) → c ∈ C ∧ ∃ z, H c = some (.sc z)
  typed : ∀ a, IsSlot th a → CapTyped H (Heap.replies H) (Heap.ntfns H) (capV (L.mem s) a)
  fh : ∀ t, th t = some .tcb → capV (L.mem s) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 3)) = .Null ∨
    ∃ ep b0 b1 b2 b3 b4, capV (L.mem s) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 3)) = .Endpoint ep b0 b1 b2 b3 b4

variable {th : TypedHeap} {H : Heap} {Tr C : Set U64} {s : S} {σ : Fl4Spec.State Unit}

/-! ### The one-line consequences -/

theorem JPlaced.tcbT (h : JPlaced (L := L) th H Tr C s σ) : ∀ t, th t = some .tcb → t ∈ (Heap.tcbs H) :=
  fun t ht => (h.tcb t).1 ht

theorem JPlaced.tcbTr (h : JPlaced (L := L) th H Tr C s σ) : ∀ t, th t = some .tcb → t ∈ Tr := h.tr

theorem JPlaced.scSets (h : JPlaced (L := L) th H Tr C s σ) : ScSetsHyp C (Heap.scs H) σ :=
  fun c y n hc hk => ⟨(h.sc c y n hc hk).1, (h.sc c y n hc hk).2⟩

theorem JPlaced.fhSlot (h : JPlaced (L := L) th H Tr C s σ) : FhSlotHyp (L := L) th H s := by
  intro t ht
  have hs : IsSlot th (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 3)) :=
    AbsSlot.isSlot ⟨t, rfl, Or.inr ⟨ht, 3, by decide, rfl⟩⟩
  rcases h.fh t ht with e | ⟨ep, b0, b1, b2, b3, b4, e⟩
  · exact Or.inl e
  · exact Or.inr ⟨ep, b0, b1, b2, b3, b4, e, (h.typed _ hs).1 ep b0 b1 b2 b3 b4 e⟩

/-! ### Slots inside their objects -/

/-- The `H` object of a slot's object, and the slot inside it (a TCB's slots
in its first 192 bytes). -/
theorem JPlaced.slot_in (h : JPlaced (L := L) th H Tr C s σ) {a : U64} (ha : IsSlot th a) :
    ∃ q k, H q = some k ∧ q.val ≤ a.val ∧ a.val + 32 ≤ q.val + 2 ^ k.bits ∧
      (k = .tcb → a.val + 32 ≤ q.val + 192) ∧ (k = .tcb ∨ ∃ z, k = .other z) := by
  obtain ⟨q, i, hqi, rfl⟩ := ha
  have hv := hqi.val h.pl
  rcases hqi with ⟨r, hq, hi⟩ | ⟨hq, hi⟩
  · refine ⟨q, _, h.cnode q r hq, by rw [hv]; omega, ?_, fun e => (by cases e), Or.inr ⟨_, rfl⟩⟩
    rw [hv]
    simp only [HKind.bits]
    have : 2 ^ (r + 5) = 32 * 2 ^ r := by rw [pow_add]; ring
    rw [this]
    have : i + 1 ≤ 2 ^ r := hi
    nlinarith
  · refine ⟨q, _, (h.tcb q).1 hq, by rw [hv]; omega, ?_, fun _ => ?_, Or.inl rfl⟩
    · rw [hv]; simp only [HKind.bits, tcbSlots] at hi ⊢; omega
    · rw [hv]; simp only [tcbSlots] at hi; omega

/-- A word of another `H` object is in no slot. -/
theorem JPlaced.not_slot (h : JPlaced (L := L) th H Tr C s σ) {a : U64} (ha : IsSlot th a) {p : U64} {k : HKind}
    (hp : H p = some k) (hk : k ≠ .tcb ∧ ∀ z, k ≠ .other z) {b : U64} (hb : InObj p k b) :
    ¬ (a.val ≤ b.val ∧ b.val < a.val + 32) := by
  rintro ⟨h1, h2⟩
  obtain ⟨q, kq, hq, e1, e2, -, hkq⟩ := h.slot_in ha
  have hpq : p ≠ q := by
    rintro rfl; rw [hp] at hq; cases hq
    rcases hkq with e | ⟨z, e⟩
    · exact hk.1 e
    · exact hk.2 z e
  obtain ⟨b1, b2⟩ := hb
  rcases h.heap.disj p k q kq hp hq hpq with e | e <;> omega

/-! ### `KWOut` -/

/-- **`KWOut` from `JPlaced`**, for P1's sets drawn from `H` (`T` its
TCBs, `Sg` its frame words, `Scs` its SCs with `Z` their sizes, the
endpoints and notifications `EH H`), given the core nodes `Cs` placed and
`Ω`'s words (the CNodes') outside the nodes, as P1's `BlkOK` has them. -/
theorem JPlaced.kwOut (h : JPlaced (L := L) th H Tr C s σ) {T Cs Sg Scs : Set U64} {Z : U64 → Nat}
    (hT : T = (Heap.tcbs H)) (hSg : Sg ⊆ (Heap.frame H)) (hScs : ∀ c ∈ Scs, ∃ z, H c = some (.sc z) ∧ Z c = z)
    (hN : ∀ c ∈ Cs, NodePlaced st T s c) (hΩ : ∀ a ∈ (Heap.omega H), OutsideObjs st T Cs s a) :
    KWOut (st := st) th T Cs Sg Scs Z (EH H) s := by
  intro a ha b hb hin
  obtain ⟨q, kq, hq, e1, e2, e3, hkq⟩ := h.slot_in ha
  have hdiff : ∀ p k, H p = some k → (k ≠ .tcb ∧ ∀ z, k ≠ .other z) → InObj p k b → False :=
    fun p k hp hk hb' => h.not_slot ha hp hk hb' hin
  rcases hb with ⟨y, hy, K, hK1, hK2, -, -, rfl⟩ | ⟨c, hc, o, ho, -, rfl⟩ | hsg | ⟨c, hc, hb'⟩ | ⟨e, he, hb'⟩
  · -- a TCB field
    rw [hT] at hy
    have hya := h.heap.align y _ hy
    have hyf := h.heap.fits y _ hy
    simp only [HKind.bits] at hya hyf
    have hv : (core.num.U64.wrapping_add y K).val = y.val + K.val := by
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    rw [hv] at hin
    by_cases hyq : y = q
    · subst hyq; rw [hy] at hq; cases hq
      have := e3 rfl; omega
    · have e' := h.heap.disj y _ q kq hy hq hyq
      rw [show (2 : ℕ) ^ HKind.tcb.bits = 4096 from rfl] at e'
      omega
  · -- a node word
    have hNc := hN c hc
    rw [nodeAt_val hNc ho] at hin
    rcases hkq with rfl | ⟨z, rfl⟩
    · have hqT : q ∈ T := by rw [hT]; exact hq
      have := hNc.disj q hqT; simp only [HKind.bits] at e2; omega
    · -- the CNode's words are outside the node
      have hal : a.val % 32 = 0 := by
        obtain ⟨q', i, hqi, rfl⟩ := ha
        exact hqi.aligned h.pl
      have hbase := hNc.align
      have hfit := hNc.fits
      have hw : ∀ w : U64, w.val % 8 = 0 → q.val ≤ w.val → w.val < a.val + 32 →
          w.val < L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ w.val := fun w h8 hq1 hq2 =>
        (hΩ w ⟨h8, q, _, hq, Or.inr (Or.inr (Or.inl ⟨z, rfl⟩)), hq1, by omega⟩).2.2 c hc
      by_cases hab : L.nodeBase s c ≤ a.val
      · rcases hw a (by omega) e1 (by omega) with e | e <;> omega
      · have hlt : L.nodeBase s c < 2 ^ 64 := by omega
        obtain ⟨w, hwv⟩ : ∃ w : U64, w.val = L.nodeBase s c :=
          ⟨⟨BitVec.ofNat 64 (L.nodeBase s c)⟩, by
            show (BitVec.ofNat 64 (L.nodeBase s c)).toNat = _; simp; omega⟩
        rcases hw w (by rw [hwv]; exact hbase) (by rw [hwv]; omega) (by rw [hwv]; omega) with e | e <;>
          rw [hwv] at e <;> omega
  · -- a frame word
    obtain ⟨-, p, k, hp, hk, hb'⟩ := hSg hsg
    refine hdiff p k hp ⟨fun e => ?_, fun z e => ?_⟩ hb' <;> subst e <;>
      rcases hk with h' | ⟨z', h'⟩ | ⟨h', -⟩ <;> cases h'
  · -- an SC word
    obtain ⟨z, hz, hZ⟩ := hScs c hc
    rw [hZ] at hb'
    exact hdiff c _ hz ⟨fun e => (by cases e), fun _ e => (by cases e)⟩ hb'
  · -- an endpoint or notification word
    have hfits : e.val + 2 ^ 4 ≤ 2 ^ 64 ∧ ∃ k, H e = some k ∧ 4 ≤ k.bits ∧ k ≠ .tcb ∧ ∀ z, k ≠ .other z := by
      rcases he with he | he
      · exact ⟨by have := h.heap.fits e _ he; simpa [HKind.bits] using this, _, he, by simp [HKind.bits],
          fun e => (by cases e), fun _ e => (by cases e)⟩
      · exact ⟨by have := h.heap.fits e _ he; simp [HKind.bits] at this; omega, _, he, by simp [HKind.bits],
          fun e => (by cases e), fun _ e => (by cases e)⟩
    obtain ⟨hf, k, hk, hk4, hk1, hk2⟩ := hfits
    have hfk := h.heap.fits e k hk
    have h4 : 2 ^ 4 ≤ 2 ^ k.bits := Nat.pow_le_pow_right (by norm_num) hk4
    rcases hb' with rfl | rfl
    · have hv : (epHeadA e).val = e.val := by
        unfold epHeadA; have : layout.ep.HEAD.val = 0 := by unfold layout.ep.HEAD; rfl
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, this]
        try omega
      exact hdiff e k hk ⟨hk1, hk2⟩ ⟨by rw [hv], by rw [hv]; omega⟩
    · have hv : (epTSA e).val = e.val + 8 := by
        unfold epTSA; have : layout.ep.TAIL_STATE.val = 8 := by unfold layout.ep.TAIL_STATE; rfl
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, this]
        try omega
      exact hdiff e k hk ⟨hk1, hk2⟩ ⟨by rw [hv]; omega, by rw [hv]; omega⟩

/-! ### `SlotCapW` -/

/-- **P1's TCB low words cover the six TCB cap slots** (the first 192 bytes;
P1's `TLow` stops at 160, the five slots before the EPT slot). -/
def TLowSlots (T : Set U64) : Prop := ∀ t ∈ T, ∀ K : U64, K.val < 192 → TLow T (core.num.U64.wrapping_add t K)

/-- **`SlotCapW` from `JPlaced`**: a TCB slot word is a TCB low word
(`TLowSlots`), a CNode slot word is an `Ω` word (P1's other objects) and no
frame word (those are in replies, SCs and notifications). -/
theorem JPlaced.slotCapW (h : JPlaced (L := L) th H Tr C s σ) (hTL : TLowSlots (Heap.tcbs H)) :
    SlotCapW th (Heap.tcbs H) (Heap.omega H) (Heap.frame H) := by
  rintro b ⟨a, ha, k, hk, rfl⟩
  have hv := slot_word_val h.pl ha hk
  have hkl := hk.lt
  obtain ⟨q, kq, hq, e1, e2, e3, hkq⟩ := h.slot_in ha
  rcases hkq with rfl | ⟨z, rfl⟩
  · -- a TCB slot word
    left
    have hqf := h.heap.fits q _ hq
    simp only [HKind.bits] at hqf
    have hK : (wordOf a k).val - q.val < 192 := by have := e3 rfl; omega
    obtain ⟨K, hKv⟩ : ∃ K : U64, K.val = (wordOf a k).val - q.val := by
      generalize (wordOf a k).val - q.val = n at hK ⊢
      exact ⟨⟨BitVec.ofNat 64 n⟩, by show (BitVec.ofNat 64 n).toNat = n; simp; omega⟩
    have e : wordOf a k = core.num.U64.wrapping_add q K := by
      apply UScalar.eq_of_val_eq
      have hKv' : K.val = a.val + k.val - q.val := by rw [hKv, hv]
      have hw : (core.num.U64.wrapping_add q K).val = q.val + K.val := by
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      rw [hv, hw]; omega
    rw [e]
    exact hTL q hq K (by omega)
  · -- a CNode slot word
    right
    have hal := slot_word_aligned h.pl ha hk
    refine ⟨⟨hal, q, _, hq, Or.inr (Or.inr (Or.inl ⟨z, rfl⟩)), by omega, by omega⟩, ?_⟩
    rintro ⟨-, p, k', hp, hk', hb'⟩
    have hpq : p ≠ q := by
      rintro rfl; rw [hp] at hq; cases hq
      rcases hk' with h' | ⟨z', h'⟩ | ⟨h', -⟩ <;> cases h'
    obtain ⟨b1, b2⟩ := hb'
    rcases h.heap.disj p k' q _ hp hq hpq with e | e <;> omega

/-! ### With P1's invariant -/

/-- **`KWOut` from `JPlaced` and P1's `BlkOK`** over `H`'s sets. -/
theorem JPlaced.kwOutBlk (h : JPlaced (L := L) th H Tr C s σ) {Cs Ac : Set U64}
    (hb : BlkOK st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
      (Heap.scBits H) Ac s) :
    KWOut (st := st) th (Heap.tcbs H) Cs (Heap.frame H) (Heap.scs H) (Heap.scBits H) (EH H) s := by
  obtain ⟨⟨Q, R, h0⟩, -⟩ := hb
  exact h.kwOut rfl (fun _ h => h) (fun c ⟨z, hz⟩ => ⟨z, hz, Heap.scBits_eq hz⟩) h0.nodes h0.omega

/-- **The joint invariant at every related state**: P1's `BlkOK` over the
sets of some heap `H` with `JPlaced`. -/
def JointInv (th : TypedHeap) : Prop :=
  ∀ (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost), DState (L := L) th s σ G →
    ∃ (H : Heap) (Cs Ac Tr C : Set U64),
      BlkOK st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
        (Heap.scBits H) Ac s ∧ JPlaced (L := L) th H Tr C s σ

/-- **The CSpace side's `NtfnP1Hyp`.** -/
theorem ntfnP1Hyp_of (hJ : JointInv (L := L) th) (hTL : ∀ T, TLowSlots T) : NtfnP1Hyp (L := L) th := by
  intro s σ G sl n b0 b1 b2 hDS hA hc
  obtain ⟨H, Cs, Ac, Tr, C, hb, hj⟩ := hJ s σ G hDS
  have hty := hj.typed _ hA.isSlot
  rw [capV_of_capAt hc] at hty
  exact ⟨_, Cs, _, H, _, _, _, _, _, Ac, hb, hj.slotCapW (hTL _), hty.2.1 n b0 b1 b2 rfl⟩

/-- **The CSpace side's `ReplyP1Hyp`.** -/
theorem replyP1Hyp_of (hJ : JointInv (L := L) th) (hTL : ∀ T, TLowSlots T) : ReplyP1Hyp (L := L) th := by
  intro s σ G sl p x hDS hA hc
  obtain ⟨H, Cs, Ac, Tr, C, hb, hj⟩ := hJ s σ G hDS
  have hty := hj.typed _ hA.isSlot
  rw [capV_of_capAt hc] at hty
  exact ⟨_, Cs, _, H, _, _, _, _, _, Ac, hb, hj.slotCapW (hTL _), hty.2.2 p x rfl⟩

/-- **The placement hypotheses of `tcb_set_sched_params_refines_disch`** at
P1's sets drawn from `H`: `hTh`, `hK`, `hSC`, `hFh`, `hTr`, `hG`. -/
theorem JPlaced.ssp (h : JPlaced (L := L) th H Tr C s σ) {Cs Ac : Set U64}
    (hb : BlkOK st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
      (Heap.scBits H) Ac s) (hTL : TLowSlots (Heap.tcbs H)) :
    (∀ t, th t = some .tcb → t ∈ Heap.tcbs H) ∧
    KWOut (st := st) th (Heap.tcbs H) Cs (Heap.frame H) (Heap.scs H) (Heap.scBits H) (EH H) s ∧
    SlotCapW th (Heap.tcbs H) (Heap.omega H) (Heap.frame H) ∧ FhSlotHyp (L := L) th H s ∧
    (∀ t, th t = some .tcb → t ∈ Tr) ∧ ScSetsHyp C (Heap.scs H) σ :=
  ⟨h.tcbT, h.kwOutBlk hb, h.slotCapW hTL, h.fhSlot, h.tcbTr, h.scSets⟩

/-! ### Keeping `JPlaced` -/

theorem capTyped_of_chgZ {H : Heap} {Rp Nt : Set U64} {m m' : U64 → U64} {y : U64}
    (h : CapTyped H Rp Nt (capV m y)) (hz : ChgZ m m' y) : CapTyped H Rp Nt (capV m' y) := by
  rcases hz with e | e | e
  · rw [e]; exact h
  · rw [e]; exact ⟨fun _ _ _ _ _ _ h => (by cases h), fun _ _ _ _ h => (by cases h), fun _ _ h => (by cases h)⟩
  · obtain ⟨p, zt, k, hc⟩ : ∃ p zt k, capV m' y = .Zombie p zt k := by
      generalize capV m' y = c at e ⊢; cases c <;> simp [isZb] at e; exact ⟨_, _, _, rfl⟩
    rw [hc]; exact ⟨fun _ _ _ _ _ _ h => (by cases h), fun _ _ _ _ h => (by cases h), fun _ _ h => (by cases h)⟩

/-- **`JPlaced` across a step** keeping the typed heaps: every slot's cap kept,
emptied or made a zombie except those in `X`, whose new caps are typed
(`hX`); each fault-handler slot kept, emptied or in `X` with a null or
endpoint cap (`hF`); the spec's SC
objects at nonzero addresses were SCs before (`hsc`). -/
theorem JPlaced.step (h : JPlaced (L := L) th H Tr C s σ) {s' : S} {σ' : Fl4Spec.State Unit} (X : U64 → Prop)
    (hZ : ∀ y, IsSlot th y → ¬ X y → ChgZ (L.mem s) (L.mem s') y)
    (hX : ∀ y, IsSlot th y → X y → CapTyped H (Heap.replies H) (Heap.ntfns H) (capV (L.mem s') y))
    (hF : ∀ t, th t = some .tcb →
      capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 3)) =
        capV (L.mem s) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 3)) ∨
      capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 3)) = .Null ∨
      ∃ ep b0 b1 b2 b3 b4, capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 3)) = .Endpoint ep b0 b1 b2 b3 b4)
    (hsc : ∀ (c : U64) y n, c ≠ 0#u64 → σ'.kheap c.bv = some (.schedContext y n) →
      ∃ y0 n0, σ.kheap c.bv = some (.schedContext y0 n0)) :
    JPlaced (L := L) th H Tr C s' σ' := by
  refine ⟨h.heap, h.pl, h.tcb, h.cnode, h.tr, fun c y n hc hk => ?_, fun a ha => ?_, fun t ht => ?_⟩
  · obtain ⟨y0, n0, hk0⟩ := hsc c y n hc hk
    exact h.sc c y0 n0 hc hk0
  · by_cases hx : X a
    · exact hX a ha hx
    · exact capTyped_of_chgZ (h.typed a ha) (hZ a ha hx)
  · rcases hF t ht with e | e
    · rw [e]; exact h.fh t ht
    · exact e

/-- **`JPlaced` across a step keeping every slot** (the scheduler-side TCB
invocations: `set_priority`, `set_mcpriority`, the SC bind and unbind, the
notification bind and unbind) and the spec's SC objects. -/
theorem JPlaced.same (h : JPlaced (L := L) th H Tr C s σ) {s' : S} {σ' : Fl4Spec.State Unit}
    (hS : SlotsSame th (L.mem s) (L.mem s'))
    (hsc : ∀ (c : U64) y n, c ≠ 0#u64 → σ'.kheap c.bv = some (.schedContext y n) →
      ∃ y0 n0, σ.kheap c.bv = some (.schedContext y0 n0)) :
    JPlaced (L := L) th H Tr C s' σ' := by
  refine ⟨h.heap, h.pl, h.tcb, h.cnode, h.tr, fun c y n hc hk => ?_, fun a ha => ?_, fun t ht => ?_⟩
  · obtain ⟨y0, n0, hk0⟩ := hsc c y n hc hk
    exact h.sc c y0 n0 hc hk0
  · rw [hS.capV ha]; exact h.typed a ha
  · have hs : IsSlot th (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 3)) :=
      AbsSlot.isSlot ⟨t, rfl, Or.inr ⟨ht, 3, by decide, rfl⟩⟩
    rw [hS.capV hs]; exact h.fh t ht

end

end

end Fl4Proofs.P3.Sched
