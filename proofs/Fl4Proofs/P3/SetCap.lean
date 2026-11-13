/-
P3 (DESIGN.md §9), CSpace: writing a slot. FL4's `Slot::set_cap` refines
l4v `set_cap` (CSpaceAcc_A), and preserves the state relation.
-/
import Fl4Proofs.P3.Layout
import Fl4Proofs.P3.Encode
import Fl4Proofs.P3.Lookup
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-! ## Slot indices: bit lists and numbers -/

theorem blVal_add (a : Nat) (l : List Bool) : blVal a l = a * 2 ^ l.length + blVal 0 l := by
  induction l generalizing a with
  | nil => simp [blVal]
  | cons b l ih =>
    simp only [blVal, List.foldl_cons, List.length_cons] at ih ⊢
    rw [ih, ih (2 * 0 + _)]
    cases b <;> simp [Nat.pow_succ] <;> ring

theorem blVal_lt (l : List Bool) : blVal 0 l < 2 ^ l.length := by
  induction l with
  | nil => simp [blVal]
  | cons b l ih =>
    have e : blVal 0 (b :: l) = (if b then 1 else 0) * 2 ^ l.length + blVal 0 l := by
      rw [show blVal 0 (b :: l) = blVal (2 * 0 + if b then 1 else 0) l from rfl, blVal_add]; simp
    rw [e, List.length_cons, Nat.pow_succ]
    cases b <;> simp <;> omega

theorem bitsOf_blVal (l : List Bool) : bitsOf (blVal 0 l) l.length = l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have e : blVal 0 (b :: l) = 2 ^ l.length * (if b then 1 else 0) + blVal 0 l := by
      rw [show blVal 0 (b :: l) = blVal (2 * 0 + if b then 1 else 0) l from rfl, blVal_add]
      simp [Nat.mul_comm]
    rw [e, List.length_cons, bitsOf_succ, Nat.testBit_two_pow_mul_add _ (blVal_lt l)]
    simp only [Nat.lt_irrefl, ↓reduceIte, Nat.sub_self]
    congr 1
    · cases b <;> simp
    · rw [← bitsOf_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt (blVal_lt l)]; exact ih

theorem ofBl_eq (idx : List Bool) :
    (Fl4Spec.ofBl idx : BitVec 64) = BitVec.ofNat 64 (blVal 0 idx) := by
  apply BitVec.eq_of_toNat_eq
  unfold Fl4Spec.ofBl
  rw [ofBl_foldl_toNat, BitVec.toNat_ofNat]; rfl

/-- Abstract slot index `idx` of a CNode is concrete slot number `blVal 0 idx`. -/
theorem slotAddr_ofBl (p : U64) (idx : List Bool) : slotAddr p.bv (Fl4Spec.ofBl idx) = slotOf p (blVal 0 idx) := by
  rw [ofBl_eq]

theorem idx_inj {idx idx' : List Bool} (hl : idx.length = idx'.length) (h : blVal 0 idx = blVal 0 idx') :
    idx = idx' := by
  rw [← bitsOf_blVal idx, ← bitsOf_blVal idx', h, hl]

/-! ## The spec's `set_cap` on a CNode slot -/

section Spec
open Fl4Spec
variable {Z : Type}

/-- The abstract state after writing `a` into slot `idx` of the CNode at `p`. -/
def setCnodeSlot (σ : State Z) (p : ObjRef) (r : Nat) (cs : CnodeContents) (idx : List Bool) (a : Cap) : State Z :=
  { σ with kheap := Function.update σ.kheap p (some (.cnode r (Function.update cs idx (some a)))) }

theorem wf_update {r : Nat} {cs : CnodeContents} {idx : List Bool} (a : Cap) (hwf : wellFormedCnodeN r cs)
    (hidx : idx.length = r) : wellFormedCnodeN r (Function.update cs idx (some a)) := by
  unfold wellFormedCnodeN dom at *
  ext x
  have := congrArg (x ∈ ·) hwf
  simp only [Set.mem_setOf_eq] at this ⊢
  by_cases hx : x = idx
  · subst hx; simp [hidx]
  · simp [Function.update_apply, hx, this]

theorem setCap_cnode {σ : State Z} {p : ObjRef} {r : Nat} {cs : CnodeContents} {idx : List Bool} (a : Cap)
    (hk : σ.kheap p = some (.cnode r cs)) (hwf : wellFormedCnodeN r cs) (hidx : idx.length = r) :
    setCap (Z := Z) a (p, idx) σ = ({((), setCnodeSlot σ p r cs idx a)}, False) := by
  have hobj : getObject (Z := Z) p σ = ({(.cnode r cs, σ)}, False) := by
    simp [getObject, NonDet.getsThe, readObject, hk, NonDet.assertOpt]; rfl
  have hdom : idx ∈ dom cs := by
    rw [show dom cs = _ from hwf]; exact hidx
  have hty : aType (.cnode r cs) = aType (.cnode r (Function.update cs idx (some a))) := by
    simp [aType, hwf, wf_update a hwf hidx]
  unfold setCap
  show (getObject p >>= _) σ = _
  rw [nd_bind_single hobj]
  simp only [hdom, hwf, and_self, ↓reduceIte]
  show ((pure _ : NonDet (State Z) KernelObject) >>= _) σ = _
  rw [nd_pure_bind]
  unfold setObject
  show (getObject p >>= _) σ = _
  rw [nd_bind_single hobj]
  have ha : NonDet.assert (σ := State Z) (aType (.cnode r cs) = aType (.cnode r (Function.update cs idx (some a)))) σ =
      ({((), σ)}, False) := by simp [NonDet.assert, hty]
  show (NonDet.assert _ >>= _) σ = _
  rw [nd_bind_single ha]
  show (NonDet.get >>= _) σ = _
  rw [nd_bind_single (show (NonDet.get : NonDet (State Z) (State Z)) σ = ({(σ, σ)}, False) from rfl)]
  rfl

end Spec

/-! ## The store after `Slot::set_cap` -/

section Store
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem set_cap_spec (sl : obj.Slot) (s : S) (c : capability.Cap) :
    obj.Slot.set_cap st sl s c ⦃ s' =>
      s' = L.wr (L.wr s sl ⟨(encodeF c).1⟩) (core.num.U64.wrapping_add sl 8#u64) ⟨(encodeF c).2⟩ ⦄ := by
  unfold obj.Slot.set_cap
  simp [encode_eq, L.write_eq, lift]

theorem wa8_val {a : U64} (h : a.val + 8 < 2 ^ 64) : (core.num.U64.wrapping_add a 8#u64).val = a.val + 8 := by
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega

theorem mem_wr2 (s : S) (a a8 w0 w1 b : U64) (ha : P1.Aligned a) (ha8 : P1.Aligned a8) (hb : P1.Aligned b) :
    L.mem (L.wr (L.wr s a w0) a8 w1) b = if a8.val = b.val then w1 else if a.val = b.val then w0 else L.mem s b := by
  rw [P1.LawfulStore.mem_wr_val ha8 hb, P1.LawfulStore.mem_wr_val ha hb]

/-- A slot whose words are not the written ones keeps its cap. -/
theorem capAt_wr2 (s : S) (a a8 w0 w1 x : U64) (ha : P1.Aligned a) (ha8 : P1.Aligned a8)
    (hx : P1.Aligned x) (hx8 : P1.Aligned (core.num.U64.wrapping_add x 8#u64))
    (h1 : x.val ≠ a.val) (h2 : x.val ≠ a8.val)
    (h3 : (core.num.U64.wrapping_add x 8#u64).val ≠ a.val) (h4 : (core.num.U64.wrapping_add x 8#u64).val ≠ a8.val) :
    capAt (L.mem (L.wr (L.wr s a w0) a8 w1)) x = capAt (L.mem s) x := by
  unfold capAt
  rw [mem_wr2 s a a8 w0 w1 x ha ha8 hx, mem_wr2 s a a8 w0 w1 _ ha ha8 hx8]
  simp only [Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, ↓reduceIte]

/-- The written slot holds the written cap. -/
theorem capAt_wr2_self (s : S) (a : U64) (c : capability.Cap) (hc : EncWf c) (ha : P1.Aligned a)
    (ha8 : P1.Aligned (core.num.U64.wrapping_add a 8#u64))
    (hne : (core.num.U64.wrapping_add a 8#u64).val ≠ a.val) :
    capAt (L.mem (L.wr (L.wr s a ⟨(encodeF c).1⟩) (core.num.U64.wrapping_add a 8#u64) ⟨(encodeF c).2⟩)) a = ok c := by
  unfold capAt
  rw [mem_wr2 _ _ _ _ _ a ha ha8 ha, mem_wr2 _ _ _ _ _ _ ha ha8 ha8]
  simp only [hne, ↓reduceIte]
  rw [decode_eq]; exact congrArg ok (decodeF_encodeF c hc)

end Store

/-! ## `Slot::set_cap` on a CNode slot -/

section SetCap
variable {Z : Type} {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem IsSlotAt.fit {th : TypedHeap} (hP : Placed th) {p : U64} {i : Nat} (h : IsSlotAt th p i) :
    (slotOf p i).val + 32 ≤ 2 ^ 64 := by
  obtain ⟨k, hk, hs⟩ := h.size
  rw [h.val hP]; have := hP.fits p k hk; omega

theorem IsSlotAt.al {th : TypedHeap} (hP : Placed th) {p : U64} {i : Nat} (h : IsSlotAt th p i) :
    P1.Aligned (slotOf p i) := by
  have := h.aligned hP; unfold P1.Aligned; omega

theorem IsSlotAt.al8 {th : TypedHeap} (hP : Placed th) {p : U64} {i : Nat} (h : IsSlotAt th p i) :
    P1.Aligned (core.num.U64.wrapping_add (slotOf p i) 8#u64) := by
  have := h.aligned hP; have := h.fit hP
  unfold P1.Aligned; rw [wa8_val (by omega)]; omega

/-- After writing slot `(p, i)`, every other slot keeps its cap. -/
theorem capAt_other_slot {th : TypedHeap} (hP : Placed th) (s : S) {p q : U64} {i j : Nat}
    (hp : IsSlotAt th p i) (hq : IsSlotAt th q j) (hne : ¬ (q = p ∧ j = i)) (w0 w1 : U64) :
    capAt (L.mem (L.wr (L.wr s (slotOf p i) w0) (core.num.U64.wrapping_add (slotOf p i) 8#u64) w1)) (slotOf q j) =
      capAt (L.mem s) (slotOf q j) := by
  have hap := hq.apart hP hp hne
  have f1 := hp.fit hP; have f2 := hq.fit hP
  apply capAt_wr2 _ _ _ _ _ _ (hp.al hP) (hp.al8 hP) (hq.al hP) (hq.al8 hP)
  all_goals (try simp only [wa8_val (show (slotOf p i).val + 8 < 2 ^ 64 by omega),
      wa8_val (show (slotOf q j).val + 8 < 2 ^ 64 by omega)])
  all_goals omega

theorem bv_inj {p q : U64} (h : p.bv = q.bv) : p = q := (UScalar.eq_equiv_bv_eq p q).2 h

/-- The state relation after writing a related cap into a CNode slot. -/
theorem StateRel.set_cnode_slot {th : TypedHeap} {s : S} {σ : Fl4Spec.State Z}
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    {p : U64} {r : Nat} {cs : Fl4Spec.CnodeContents} (hp : th p = some (.cnode r))
    (hk : σ.kheap p.bv = some (.cnode r cs)) (hwf : Fl4Spec.wellFormedCnodeN r cs)
    {idx : List Bool} (hidx : idx.length = r) {c : capability.Cap} {a : Fl4Spec.Cap}
    (hca : CapRel c a) (hcv : CapValid th c) (he : EncWf c) :
    let a0 := slotOf p (blVal 0 idx)
    let s' := L.wr (L.wr s a0 ⟨(encodeF c).1⟩) (core.num.U64.wrapping_add a0 8#u64) ⟨(encodeF c).2⟩
    StateRel th (L.mem s') (setCnodeSlot σ p.bv r cs idx a) ∧ SlotsValid th (L.mem s') := by
  intro a0 s'
  have hsp : IsSlotAt th p (blVal 0 idx) := Or.inl ⟨r, hp, hidx ▸ blVal_lt idx⟩
  have hself : capAt (L.mem s') a0 = ok c := by
    have f := hsp.fit hP
    apply capAt_wr2_self _ _ _ he (hsp.al hP) (hsp.al8 hP)
    rw [wa8_val (by omega)]; omega
  -- every other slot is unchanged
  have hother : ∀ q j, IsSlotAt th q j → ¬ (q = p ∧ j = blVal 0 idx) → capAt (L.mem s') (slotOf q j) = capAt (L.mem s) (slotOf q j) :=
    fun q j hq hne => capAt_other_slot hP s hsp hq hne _ _
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro q r' hq
    have hsq : ∀ idx' : List Bool, idx'.length = r' → IsSlotAt th q (blVal 0 idx') :=
      fun idx' h => Or.inl ⟨r', hq, h ▸ blVal_lt idx'⟩
    by_cases hqp : q = p
    · subst hqp
      rw [hp] at hq; cases hq
      refine ⟨Function.update cs idx (some a), by simp [setCnodeSlot], wf_update a hwf hidx, ?_⟩
      intro idx' hl
      rw [slotAddr_ofBl]
      by_cases hi : idx' = idx
      · subst hi; exact ⟨c, a, hself, by simp, hca⟩
      · have hne : ¬ (q = q ∧ blVal 0 idx' = blVal 0 idx) := fun ⟨_, h⟩ => hi (idx_inj (by rw [hl, hidx]) h)
        unfold SlotRel
        rw [hother _ _ (hsq idx' hl) hne, Function.update_of_ne hi, ← slotAddr_ofBl]
        obtain ⟨cs0, hk0, -, hs0⟩ := hR.cnode q _ hp
        rw [hk] at hk0; cases hk0
        exact hs0 idx' hl
    · obtain ⟨cs', hk', hwf', hs'⟩ := hR.cnode q r' hq
      have hb : q.bv ≠ p.bv := fun h => hqp (bv_inj h)
      refine ⟨cs', by simp [setCnodeSlot, Function.update_of_ne hb, hk'], hwf', ?_⟩
      intro idx' hl
      unfold SlotRel
      rw [slotAddr_ofBl, hother _ _ (hsq idx' hl) (fun h => hqp h.1), ← slotAddr_ofBl]
      exact hs' idx' hl
  · intro t ht
    obtain ⟨tcb, hk', hs'⟩ := hR.tcb t ht
    have htp : t ≠ p := by rintro rfl; rw [hp] at ht; cases ht
    have hb : t.bv ≠ p.bv := fun h => htp (bv_inj h)
    refine ⟨tcb, by simp [setCnodeSlot, Function.update_of_ne hb, hk'], ?_⟩
    intro i hi
    show SlotRel _ (slotOf t i) _
    rw [SlotRel, hother _ _ (Or.inr ⟨ht, hi⟩) (fun h => htp h.1)]
    exact hs' i hi
  · intro q r' hq i hi c' hc'
    by_cases hqi : q = p ∧ i = blVal 0 idx
    · obtain ⟨rfl, rfl⟩ := hqi
      have : capAt (L.mem s') (slotOf q (blVal 0 idx)) = ok c := hself
      change capAt _ (slotOf q (blVal 0 idx)) = _ at hc'
      rw [this] at hc'; have e : c = c' := by simpa using hc'
      subst e; exact hcv
    · change capAt _ (slotOf q i) = _ at hc'
      rw [hother _ _ (Or.inl ⟨r', hq, hi⟩) hqi] at hc'
      exact hV.cnode q r' hq i hi c' hc'
  · intro t ht i hi c' hc'
    have htp : t ≠ p := by rintro rfl; rw [hp] at ht; cases ht
    change capAt _ (slotOf t i) = _ at hc'
    rw [hother _ _ (Or.inr ⟨ht, hi⟩) (fun h => htp h.1)] at hc'
    exact hV.tcb t ht i hi c' hc'

/-- **FL4's `Slot::set_cap` refines l4v `set_cap`** on a slot of a CNode of
the typed heap: the spec has the single outcome `setCnodeSlot` (it does not
fail), and the new states are related again (`StateRel`, `SlotsValid`).
Only the two cap words of the slot change, so the CDT links of every slot
and the spec's `cdt` and `is_original_cap` are unchanged. -/
theorem set_cap_refines (th : TypedHeap) (s : S) (σ : Fl4Spec.State Z)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    {p : U64} {r : Nat} (hp : th p = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    (c : capability.Cap) (a : Fl4Spec.Cap) (hca : CapRel c a) (hcv : CapValid th c) (he : EncWf c) :
    obj.Slot.set_cap st (cslotAddr (p.bv, idx)) s c ⦃ s' =>
      ∃ σ', Fl4Spec.setCap (Z := Z) a (p.bv, idx) σ = ({((), σ')}, False) ∧
        StateRel th (L.mem s') σ' ∧ SlotsValid th (L.mem s') ∧
        σ'.cdt = σ.cdt ∧ σ'.isOriginalCap = σ.isOriginalCap ∧ σ'.exst = σ.exst ∧
        ∀ b, P1.Aligned b → b.val ≠ (cslotAddr (p.bv, idx)).val → b.val ≠ (cslotAddr (p.bv, idx)).val + 8 →
          L.mem s' b = L.mem s b ⦄ := by
  obtain ⟨cs, hk, hwf, -⟩ := hR.cnode p r hp
  have ha0 : cslotAddr (p.bv, idx) = slotOf p (blVal 0 idx) := slotAddr_ofBl p idx
  rw [ha0]
  have hsp : IsSlotAt th p (blVal 0 idx) := Or.inl ⟨r, hp, hidx ▸ blVal_lt idx⟩
  apply WP.spec_mono (set_cap_spec _ s c)
  rintro s' rfl
  obtain ⟨h1, h2⟩ := StateRel.set_cnode_slot hR hV hP hp hk hwf hidx hca hcv he
  refine ⟨_, setCap_cnode a hk hwf hidx, h1, h2, rfl, rfl, rfl, ?_⟩
  intro b hb hb1 hb2
  have f := hsp.fit hP
  rw [mem_wr2 _ _ _ _ _ b (hsp.al hP) (hsp.al8 hP) hb, wa8_val (by omega)]
  simp only [Ne.symm hb2, Ne.symm hb1, ↓reduceIte]

/-- The state relation only depends on the caps in the slots. -/
theorem StateRel.of_caps {th : TypedHeap} {mem mem' : U64 → U64} {σ : Fl4Spec.State Z}
    (hR : StateRel th mem σ) (hcap : ∀ x, IsSlot th x → capAt mem' x = capAt mem x) : StateRel th mem' σ := by
  refine ⟨fun p r hp => ?_, fun t ht => ?_⟩
  · obtain ⟨cs, hk, hwf, hs⟩ := hR.cnode p r hp
    refine ⟨cs, hk, hwf, fun idx hl => ?_⟩
    unfold SlotRel
    rw [slotAddr_ofBl, hcap _ ⟨p, _, Or.inl ⟨r, hp, hl ▸ blVal_lt idx⟩, rfl⟩, ← slotAddr_ofBl]
    exact hs idx hl
  · obtain ⟨tcb, hk, hs⟩ := hR.tcb t ht
    refine ⟨tcb, hk, fun i hi => ?_⟩
    unfold SlotRel
    show (∃ c ac, capAt mem' (slotOf t i) = _ ∧ _) 
    rw [hcap _ ⟨t, i, Or.inr ⟨ht, hi⟩, rfl⟩]
    exact hs i hi

theorem SlotsValid.of_caps {th : TypedHeap} {mem mem' : U64 → U64} (hV : SlotsValid th mem)
    (hcap : ∀ x, IsSlot th x → capAt mem' x = capAt mem x) : SlotsValid th mem' := by
  refine ⟨fun p r hp i hi c hc => ?_, fun t ht i hi c hc => ?_⟩
  · change capAt _ (slotOf p i) = _ at hc
    rw [hcap _ ⟨p, i, Or.inl ⟨r, hp, hi⟩, rfl⟩] at hc
    exact hV.cnode p r hp i hi c hc
  · change capAt _ (slotOf t i) = _ at hc
    rw [hcap _ ⟨t, i, Or.inr ⟨ht, hi⟩, rfl⟩] at hc
    exact hV.tcb t ht i hi c hc

/-- The state relation after a CNode slot gets a related cap, given only how
the caps change. -/
theorem StateRel.update_cnode_slot {th : TypedHeap} {mem mem' : U64 → U64} {σ : Fl4Spec.State Z}
    (hR : StateRel th mem σ) (hV : SlotsValid th mem) (hP : Placed th)
    {p : U64} {r : Nat} {cs : Fl4Spec.CnodeContents} (hp : th p = some (.cnode r))
    (hk : σ.kheap p.bv = some (.cnode r cs)) (hwf : Fl4Spec.wellFormedCnodeN r cs)
    {idx : List Bool} (hidx : idx.length = r) {c : capability.Cap} {a : Fl4Spec.Cap}
    (hca : CapRel c a) (hcv : CapValid th c)
    (hcap : ∀ x, IsSlot th x → capAt mem' x = if x = slotOf p (blVal 0 idx) then ok c else capAt mem x) :
    StateRel th mem' (setCnodeSlot σ p.bv r cs idx a) ∧ SlotsValid th mem' := by
  have hsp : IsSlotAt th p (blVal 0 idx) := Or.inl ⟨r, hp, hidx ▸ blVal_lt idx⟩
  have hself : capAt mem' (slotOf p (blVal 0 idx)) = ok c := by rw [hcap _ ⟨_, _, hsp, rfl⟩]; simp
  have hother : ∀ q j, IsSlotAt th q j → ¬ (q = p ∧ j = blVal 0 idx) →
      capAt mem' (slotOf q j) = capAt mem (slotOf q j) := by
    intro q j hq hne
    rw [hcap _ ⟨_, _, hq, rfl⟩, if_neg]
    intro h
    rcases hq.apart hP hsp hne with h' | h' <;> rw [h] at h' <;> omega
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro q r' hq
    have hsq : ∀ idx' : List Bool, idx'.length = r' → IsSlotAt th q (blVal 0 idx') :=
      fun idx' h => Or.inl ⟨r', hq, h ▸ blVal_lt idx'⟩
    by_cases hqp : q = p
    · subst hqp
      rw [hp] at hq; cases hq
      refine ⟨Function.update cs idx (some a), by simp [setCnodeSlot], wf_update a hwf hidx, ?_⟩
      intro idx' hl
      rw [slotAddr_ofBl]
      by_cases hi : idx' = idx
      · subst hi; exact ⟨c, a, hself, by simp, hca⟩
      · have hne : ¬ (q = q ∧ blVal 0 idx' = blVal 0 idx) := fun ⟨_, h⟩ => hi (idx_inj (by rw [hl, hidx]) h)
        unfold SlotRel
        rw [hother _ _ (hsq idx' hl) hne, Function.update_of_ne hi, ← slotAddr_ofBl]
        obtain ⟨cs0, hk0, -, hs0⟩ := hR.cnode q _ hp
        rw [hk] at hk0; cases hk0
        exact hs0 idx' hl
    · obtain ⟨cs', hk', hwf', hs'⟩ := hR.cnode q r' hq
      have hb : q.bv ≠ p.bv := fun h => hqp (bv_inj h)
      refine ⟨cs', by simp [setCnodeSlot, Function.update_of_ne hb, hk'], hwf', ?_⟩
      intro idx' hl
      unfold SlotRel
      rw [slotAddr_ofBl, hother _ _ (hsq idx' hl) (fun h => hqp h.1), ← slotAddr_ofBl]
      exact hs' idx' hl
  · intro t ht
    obtain ⟨tcb, hk', hs'⟩ := hR.tcb t ht
    have htp : t ≠ p := by rintro rfl; rw [hp] at ht; cases ht
    have hb : t.bv ≠ p.bv := fun h => htp (bv_inj h)
    refine ⟨tcb, by simp [setCnodeSlot, Function.update_of_ne hb, hk'], ?_⟩
    intro i hi
    show SlotRel _ (slotOf t i) _
    rw [SlotRel, hother _ _ (Or.inr ⟨ht, hi⟩) (fun h => htp h.1)]
    exact hs' i hi
  · intro q r' hq i hi c' hc'
    by_cases hqi : q = p ∧ i = blVal 0 idx
    · obtain ⟨rfl, rfl⟩ := hqi
      change capAt _ (slotOf q (blVal 0 idx)) = _ at hc'
      rw [hself] at hc'; have e : c = c' := by simpa using hc'
      subst e; exact hcv
    · change capAt _ (slotOf q i) = _ at hc'
      rw [hother _ _ (Or.inl ⟨r', hq, hi⟩) hqi] at hc'
      exact hV.cnode q r' hq i hi c' hc'
  · intro t ht i hi c' hc'
    have htp : t ≠ p := by rintro rfl; rw [hp] at ht; cases ht
    change capAt _ (slotOf t i) = _ at hc'
    rw [hother _ _ (Or.inr ⟨ht, hi⟩) (fun h => htp h.1)] at hc'
    exact hV.tcb t ht i hi c' hc'

end SetCap

end

end Fl4Proofs.P3
