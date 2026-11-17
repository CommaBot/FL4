/-
P3 (DESIGN.md §9): **the joint placement invariant** linking P3's typed
heap `th` (CNodes, TCBs, other objects; `Placed th`) to P1's typed heap `H`
(`HeapOK H`, with P1's object sets taken from it: `(Heap.tcbs H)`, `(Heap.omega H)`,
`(Heap.frame H)`, `(Heap.replies H)`, `(Heap.scs H)`, `(Heap.ntfns H)`, `(Heap.scBits H)`).

* `JPlaced th H Tr C s σ`: both heaps placed; a TCB of `th` is a TCB of `H`
  and conversely, a CNode of radix `r` is an object of `2 ^ (r + 5)` bytes of
  `H`; the TCBs are among the scheduler relation's `Tr`, the spec's SCs
  among `C` and `H`'s SCs; every cap in a slot names objects of the right
  kind (P1's `CapTyped`), the IRQ handler slots too, the fault-handler
  slots hold the null or an endpoint cap (l4v `valid_fault_handler`), and
  `H`'s objects lie outside the kernel-global area.
* Derived: `hTh`/`hTr` (`JPlaced.tcbT`, `JPlaced.tcbTr`), `ScSetsHyp`
  (`JPlaced.scSets`), `FhSlotHyp` (`JPlaced.fhSlot`), `KWOut`
  (`JPlaced.kwOut`, with the nodes and `Ω` facts of P1's `BlkOK`),
  `SlotCapW` (`JPlaced.slotCapW`, given P1's TCB low words cover the six
  TCB slots, `TLowSlots`), and the CSpace side's `NtfnP1Hyp`/`ReplyP1Hyp`/`EpP1Hyp` (`capTypedP1Hyp_of`)
  from the invariant at every related state (`JointInv`); the CSpace side's
  `ThreadP1Hyp`/`ScP1Hyp` (`threadP1Hyp_of`, `scP1Hyp_of`) from it with the
  state facts `JState` (`JointInvS`).
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
  sc : ∀ (c : U64) y n, c ≠ 0#u64 → σ.kheap c.bv = some (.schedContext y n) →
    c ∈ C ∧ H c = some (.sc (n + Fl4Spec.minSchedContextBits))
  /-- `H`'s objects lie outside the kernel-global area. -/
  ks : ∀ p k, H p = some k → p.val + 2 ^ k.bits ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ p.val
  typed : ∀ a, IsSlot th a → CapTyped H (Heap.replies H) (Heap.ntfns H) (capV (L.mem s) a)
  /-- The IRQ handler slots (the kernel-global IRQ node) hold typed caps too. -/
  irq : ∀ i : U64, i.val < 128 → CapTyped H (Heap.replies H) (Heap.ntfns H) (capV (L.mem s) (nodeA (L.ksb s) i))
  fh : ∀ t, th t = some .tcb → capV (L.mem s) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 3)) = .Null ∨
    ∃ ep b0 b1 b2 b3 b4, capV (L.mem s) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 3)) = .Endpoint ep b0 b1 b2 b3 b4

variable {th : TypedHeap} {H : Heap} {Tr C : Set U64} {s : S} {σ : Fl4Spec.State Unit}

/-! ### The one-line consequences -/

theorem JPlaced.tcbT (h : JPlaced (L := L) th H Tr C s σ) : ∀ t, th t = some .tcb → t ∈ (Heap.tcbs H) :=
  fun t ht => (h.tcb t).1 ht

theorem JPlaced.tcbTr (h : JPlaced (L := L) th H Tr C s σ) : ∀ t, th t = some .tcb → t ∈ Tr := h.tr

theorem JPlaced.scSets (h : JPlaced (L := L) th H Tr C s σ) : ScSetsHyp C (Heap.scs H) σ :=
  fun c y n hc hk => ⟨(h.sc c y n hc hk).1, _, (h.sc c y n hc hk).2⟩

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

/-- **The spec's objects in `H`**, the part of the spec-to-FL4 object
coverage (`Sched.ObjCover`) that the CSpace relation does not give: the
spec's notifications, endpoints and replies are `H`'s, and no SC sits at
address 0 (TCBs: `KTyped` and `JPlaced.tcb`; nonzero SCs: `JPlaced.sc`); the
arch objects are `H`'s page-sized (or larger) `other` objects. -/
structure SpecCover (H : Heap) (σ : Fl4Spec.State Unit) : Prop where
  ntfn : ∀ o x, σ.kheap o = some (.notification x) → H ⟨o⟩ = some .ntfn
  ep : ∀ o x, σ.kheap o = some (.endpoint x) → H ⟨o⟩ = some .ep
  reply : ∀ o x, σ.kheap o = some (.reply x) → H ⟨o⟩ = some .reply
  sc0 : ∀ y k, σ.kheap (0#u64 : U64).bv ≠ some (.schedContext y k)
  /-- The spec's arch objects (page tables, pools, frames) are `H`'s `other`
  objects of at least a page ([W] producer: retype). -/
  arch : ∀ o ao, σ.kheap o = some (.archObj ao) → ∃ n, 12 ≤ n ∧ H ⟨o⟩ = some (.other n)

/-- **No spec object in an untyped cap's free part** (l4v `valid_untyped`):
every object of the spec's heap that meets the range of an untyped cap of
the MDB lies in it, below its free index. -/
def SpecFree (mem : U64 → U64) (G : MdbGhost) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ x ∈ G.chains.flatten, ∀ p sb fi d, capV mem x = .Untyped p sb fi d →
    ∀ o ko, σ.kheap o = some ko →
      (o.toNat + 2 ^ Fl4Spec.objBits ko ≤ p.val ∨ p.val + 2 ^ sb.val ≤ o.toNat) ∨
      (p.val ≤ o.toNat ∧ o.toNat + 2 ^ Fl4Spec.objBits ko ≤ p.val + fi.val)

/-- **The joint invariant at every related state**: P1's `BlkOK` over the
sets of some heap `H` with `JPlaced`, the spec's objects in `H`
(`SpecCover`), and none in an untyped cap's free part (`SpecFree`). -/
def JointInv (th : TypedHeap) : Prop :=
  ∀ (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost), DState (L := L) th s σ G →
    ∃ (H : Heap) (Cs Ac Tr C : Set U64),
      BlkOK st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
        (Heap.scBits H) Ac s ∧ JPlaced (L := L) th H Tr C s σ ∧ SpecCover H σ ∧ SpecFree (L.mem s) G σ

/-- **P1's invariant at a cap, with the cap typed** (`CapTyped`), from the
joint invariant: the uniform shape of the CSpace side's couplings. -/
theorem capTypedP1Hyp_of (hJ : JointInv (L := L) th) (hTL : ∀ T, TLowSlots T) :
    P1CapHyp (L := L) th (fun c X _ => CapTyped X.H X.Rp X.Nt c) := by
  intro s σ G sl c hDS hA hc _
  obtain ⟨H, Cs, Ac, Tr, C, hb, hj, -⟩ := hJ s σ G hDS
  have hty := hj.typed _ hA.isSlot
  rw [capV_of_capAt hc] at hty
  exact ⟨⟨_, Cs, _, H, _, _, _, _, _, Ac⟩, hb, hj.slotCapW (hTL _), hty⟩

/-- **The CSpace side's `NtfnP1Hyp`.** -/
theorem ntfnP1Hyp_of (hJ : JointInv (L := L) th) (hTL : ∀ T, TLowSlots T) : NtfnP1Hyp (L := L) th := by
  intro s σ G sl c hDS hA hc hk
  obtain ⟨X, hb, hS, hty⟩ := capTypedP1Hyp_of hJ hTL s σ G sl c hDS hA hc hk
  exact ⟨X, hb, hS, hty.2.1⟩

/-- **The CSpace side's `ReplyP1Hyp`.** -/
theorem replyP1Hyp_of (hJ : JointInv (L := L) th) (hTL : ∀ T, TLowSlots T) : ReplyP1Hyp (L := L) th := by
  intro s σ G sl c hDS hA hc hk
  obtain ⟨X, hb, hS, hty⟩ := capTypedP1Hyp_of hJ hTL s σ G sl c hDS hA hc hk
  exact ⟨X, hb, hS, hty.2.2⟩

/-- **The CSpace side's `EpP1Hyp`.** -/
theorem epP1Hyp_of (hJ : JointInv (L := L) th) (hTL : ∀ T, TLowSlots T) : EpP1Hyp (L := L) th := by
  intro s σ G sl c hDS hA hc hk
  obtain ⟨X, hb, hS, hty⟩ := capTypedP1Hyp_of hJ hTL s σ G sl c hDS hA hc hk
  exact ⟨X, hb, hS, hty.1⟩

/-- P1's TCB low words cover the six TCB slots (P1's `tlow_slots`). -/
theorem tLowSlots_all (T : Set U64) : TLowSlots T := fun t ht K hK => P1.tlow_slots t ht K hK

/-- **The state facts of the joint invariant** that P1's thread and SC
finalisations need: the scheduler action is resume or choose-new; no thread
cap names the idle thread; an SC cap names a nonzero SC of `H` whose TCB,
if any, is a TCB of `H` and not the idle thread (l4v `valid_global_refs`,
`valid_sched_action` at kernel entry); the threads are native (their VCPU
link word, at offset 3664, is zero). -/
structure JState (th : TypedHeap) (H : Heap) (s : S) : Prop where
  act : L.actionW s = 0#u64 ∨ L.actionW s = 1#u64
  noIdle : ∀ a, IsSlot th a → ∀ p, capV (L.mem s) a = .Thread p → p ≠ L.idleW s
  sc : ∀ a, IsSlot th a → ∀ p x, capV (L.mem s) a = .SchedContext p x → p ≠ 0#u64 ∧ (∃ z, H p = some (.sc z)) ∧
    (L.mem s (P1.scTcbA p) ≠ 0#u64 → L.mem s (P1.scTcbA p) ∈ Heap.tcbs H ∧ L.mem s (P1.scTcbA p) ≠ L.idleW s)
  vcpu : ∀ t, th t = some .tcb → L.mem s (core.num.U64.wrapping_add t 3664#u64) = 0#u64

/-- **The joint invariant with its state facts** at every related state. -/
def JointInvS (th : TypedHeap) : Prop :=
  ∀ (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost), DState (L := L) th s σ G →
    ∃ (H : Heap) (Cs Ac Tr C : Set U64),
      BlkOK st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
        (Heap.scBits H) Ac s ∧ JPlaced (L := L) th H Tr C s σ ∧ JState (L := L) th H s ∧ SpecCover H σ ∧
        SpecFree (L.mem s) G σ

theorem JointInvS.toJ (h : JointInvS (L := L) th) : JointInv (L := L) th := fun s σ G hDS => by
  obtain ⟨H, Cs, Ac, Tr, C, hb, hj, -, hc, hf⟩ := h s σ G hDS
  exact ⟨H, Cs, Ac, Tr, C, hb, hj, hc, hf⟩

/-- The scheduler action, resume or choose-new, is no TCB. -/
theorem JState.act_ne {H : Heap} {s : S} (h : JState (L := L) th H s) {T : Set U64} (hT : TcbPlaced T) {p : U64}
    (hp : p ∈ T) : L.actionW s ≠ p := by
  intro e
  rcases h.act with e' | e' <;> rw [e'] at e <;> subst e <;> exact notT_small hT (by decide) hp

/-- **The CSpace side's `ThreadP1Hyp`.** -/
theorem threadP1Hyp_of (hJ : JointInvS (L := L) th) : ThreadP1Hyp (L := L) th := by
  intro s σ G sl c hDS hA hc _
  obtain ⟨H, Cs, Ac, Tr, C, hb, hj, hs, -⟩ := hJ s σ G hDS
  refine ⟨⟨_, Cs, _, H, _, _, _, _, _, Ac⟩, hb, hj.slotCapW (tLowSlots_all _), fun p e => ?_⟩
  have hcv : capV (L.mem s) (cslotAddr sl) = .Thread p := by rw [capV_of_capAt hc, e]
  have hth : th p = some .tcb := by
    have := hDS.1.2.1.abs hA hc
    rw [e] at this; exact this
  have hT := hb.1.choose_spec.choose_spec.tcbs
  have hpT : p ∈ Heap.tcbs H := hj.tcbT p hth
  exact ⟨hpT, hs.act_ne hT hpT, (hs.noIdle _ hA.isSlot p hcv).symm, hs.vcpu p hth⟩

/-- **The CSpace side's `ScP1Hyp`.** -/
theorem scP1Hyp_of (hJ : JointInvS (L := L) th) : ScP1Hyp (L := L) th := by
  intro s σ G sl c hDS hA hc _
  obtain ⟨H, Cs, Ac, Tr, C, hb, hj, hs, -⟩ := hJ s σ G hDS
  refine ⟨⟨_, Cs, _, H, _, _, _, _, _, Ac⟩, hb, hj.slotCapW (tLowSlots_all _), fun p x e => ?_⟩
  have hcv : capV (L.mem s) (cslotAddr sl) = .SchedContext p x := by rw [capV_of_capAt hc, e]
  obtain ⟨h0, hz, ht⟩ := hs.sc _ hA.isSlot p x hcv
  have hT := hb.1.choose_spec.choose_spec.tcbs
  exact ⟨hz, h0, fun hn => hs.act_ne hT (ht hn).1, fun hn => (ht hn).2.symm⟩

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

/-- **P1's cap typedness at the slots it reads** (`EntryHyps.tmoOK`'s and
`irqcap`'s, restricted to the typed heap's slots and the IRQ handler slots). -/
theorem JPlaced.slotCapTyped (h : JPlaced (L := L) th H Tr C s σ) {sl : U64}
    (hsl : IsSlot th sl ∨ ∃ i : U64, i.val < 128 ∧ sl = nodeA (L.ksb s) i) :
    obj.Slot.cap st sl s ⦃ c => CapTyped H (Heap.replies H) (Heap.ntfns H) c ⦄ := by
  rw [slot_cap_eq, capAt_capV, WP.spec_ok]
  rcases hsl with hs | ⟨i, hi, rfl⟩
  · exact h.typed sl hs
  · exact h.irq i hi

theorem JPlaced.slotNtfn (h : JPlaced (L := L) th H Tr C s σ) {sl : U64}
    (hsl : IsSlot th sl ∨ ∃ i : U64, i.val < 128 ∧ sl = nodeA (L.ksb s) i) :
    obj.Slot.cap st sl s ⦃ c => ∀ ptr b0 b1 b2, c = .Notification ptr b0 b1 b2 → ptr ∈ Heap.ntfns H ⦄ :=
  WP.spec_mono (h.slotCapTyped hsl) fun c hc ptr b0 b1 b2 e => (hc.2.1 ptr b0 b1 b2 e).1

/-! ### Keeping `JPlaced` -/

theorem capTyped_of_chgZ {H : Heap} {Rp Nt : Set U64} {m m' : U64 → U64} {y : U64}
    (h : CapTyped H Rp Nt (capV m y)) (hz : ChgZ m m' y) : CapTyped H Rp Nt (capV m' y) := by
  rcases hz with e | e | e
  · rw [e]; exact h
  · rw [e]; exact ⟨fun _ _ _ _ _ _ h => (by cases h), fun _ _ _ _ h => (by cases h), fun _ _ h => (by cases h)⟩
  · obtain ⟨zt, k, hc⟩ := e
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
      ∃ y0, σ.kheap c.bv = some (.schedContext y0 n))
    (hk : L.ksb s' = L.ksb s) (hI : ∀ i : U64, i.val < 128 → ChgZ (L.mem s) (L.mem s') (nodeA (L.ksb s) i)) :
    JPlaced (L := L) th H Tr C s' σ' := by
  refine ⟨h.heap, h.pl, h.tcb, h.cnode, h.tr, fun c y n hc hk => ?_, by rw [hk]; exact h.ks, fun a ha => ?_,
    fun i hi => by rw [hk]; exact capTyped_of_chgZ (h.irq i hi) (hI i hi), fun t ht => ?_⟩
  · obtain ⟨y0, hk0⟩ := hsc c y n hc hk
    exact h.sc c y0 n hc hk0
  · by_cases hx : X a
    · exact hX a ha hx
    · exact capTyped_of_chgZ (h.typed a ha) (hZ a ha hx)
  · rcases hF t ht with e | e
    · rw [e]; exact h.fh t ht
    · exact e

/-- **`JPlaced` across a step keeping every slot** (the scheduler-side TCB
invocations: `set_priority`, `set_mcpriority`, the SC bind and unbind, the
notification bind and unbind) and the spec's SC objects, with the IRQ
handler slots kept. -/
theorem JPlaced.same (h : JPlaced (L := L) th H Tr C s σ) {s' : S} {σ' : Fl4Spec.State Unit}
    (hS : SlotsSame th (L.mem s) (L.mem s'))
    (hsc : ∀ (c : U64) y n, c ≠ 0#u64 → σ'.kheap c.bv = some (.schedContext y n) →
      ∃ y0, σ.kheap c.bv = some (.schedContext y0 n))
    (hk : L.ksb s' = L.ksb s)
    (hI : ∀ i : U64, i.val < 128 → capV (L.mem s') (nodeA (L.ksb s) i) = capV (L.mem s) (nodeA (L.ksb s) i)) :
    JPlaced (L := L) th H Tr C s' σ' := by
  refine ⟨h.heap, h.pl, h.tcb, h.cnode, h.tr, fun c y n hc hk => ?_, by rw [hk]; exact h.ks, fun a ha => ?_,
    fun i hi => by rw [hk, hI i hi]; exact h.irq i hi, fun t ht => ?_⟩
  · obtain ⟨y0, hk0⟩ := hsc c y n hc hk
    exact h.sc c y0 n hc hk0
  · rw [hS.capV ha]; exact h.typed a ha
  · have hs : IsSlot th (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 3)) :=
      AbsSlot.isSlot ⟨t, rfl, Or.inr ⟨ht, 3, by decide, rfl⟩⟩
    rw [hS.capV hs]; exact h.fh t ht

end

end

end Fl4Proofs.P3.Sched
