/-
P3 (DESIGN.md §9), untyped: **the object-creation loop of `Retype`**
(`objects::create_new_objects`) against l4v `retype_region` and
`mapM_x create_cap` (`invoke_untyped`), for the non-arch object types but
the TCB.

* the new caps' ranges (`newCap_range`);
* the spec's `retype_region` evaluated (`retypeRegionWith_eq`);
* the typed heap and the relations after `retype_region` (`extend_rel`):
  new CNodes are added to the ghost typed heap and are related to
  `empty_cnode` because their memory is zero (`ZeroRegion`, the "free region
  is zero" hypothesis);
* the loop (`create_loop_rel`): each `insert_new_cap` is `insert_new_full`,
  the range hypotheses of the next one carried as a loop invariant.
-/
import Fl4Proofs.P3.UntypedMdb
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section
set_option linter.unusedSimpArgs false

/-! ## The new caps -/

theorem ptrF_of {c : capability.Cap} {v : U64} (h : capability.Cap.ptr c = ok v) : ptrF c = v :=
  ok_inj ((ptr_eq c).symm.trans h)
theorem sizeF_of {c : capability.Cap} {v : U64} (h : objects.cap_size_bits c = ok v) : sizeF c = v :=
  ok_inj ((size_eq c).symm.trans h)
theorem physF_of {c : capability.Cap} {v : Bool} (h : objects.cap_is_physical c = ok v) : physF c = v :=
  ok_inj ((phys_eq c).symm.trans h)

theorem sizeF_newCap {n : Nat} (hn : n = 0 ∨ (2 ≤ n ∧ n ≤ 6)) (base us : U64) (dev : Bool) (hus : us.val < 64) :
    (sizeF (newCapOf n base us dev)).val = zOf n us.val := by
  rcases hn with rfl | ⟨h1, h2⟩
  · rw [show newCapOf 0 base us dev = .Untyped base us 0#u64 dev from rfl, sizeF_ut]; simp [zOf]
  · interval_cases n <;> simp only [newCapOf, show ¬ (2 : Nat) = 3 by decide, show ¬ (3 : Nat) = 2 by decide] <;>
      simp <;> rw [sizeF_of rfl] <;> simp [fl4_abi.consts.bits.ENDPOINT,
        fl4_abi.consts.bits.NOTIFICATION, fl4_abi.consts.bits.SLOT, fl4_abi.consts.bits.REPLY, zOf]
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega

theorem ptrF_newCap (n : Nat) (base us : U64) (dev : Bool) : ptrF (newCapOf n base us dev) = base := by
  unfold newCapOf
  split_ifs <;> exact ptrF_of rfl

theorem physF_newCap (n : Nat) (base us : U64) (dev : Bool) : physF (newCapOf n base us dev) = true := by
  unfold newCapOf
  split_ifs <;> exact physF_of rfl

theorem newKind_newCap (n : Nat) (base us : U64) (dev : Bool) : NewKind (newCapOf n base us dev) := by
  unfold newCapOf; split_ifs <;> trivial

/-- **The range of a new cap** is its object: `2^z` bytes from `base`. -/
theorem newCap_range {n : Nat} (hn : n = 0 ∨ (2 ≤ n ∧ n ≤ 6)) (base us : U64) (dev : Bool) (hus : us.val < 64)
    (hz : zOf n us.val < 64) (hb : base.val + 2 ^ zOf n us.val ≤ 2 ^ 64) :
    baseF (newCapOf n base us dev) = base.val ∧
      topF (newCapOf n base us dev) = base.val + 2 ^ zOf n us.val - 1 := by
  refine ⟨by unfold baseF; rw [ptrF_newCap], ?_⟩
  unfold topF
  rw [ptrF_newCap]
  have hs := sizeF_newCap hn base us dev hus
  have hm := maskF_val (b := sizeF (newCapOf n base us dev)) (by rw [hs]; exact hz)
  rw [hs] at hm
  have h1 : 1 ≤ 2 ^ zOf n us.val := Nat.one_le_two_pow
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits, hm]
  omega

/-! ## The spec's `retype_region` -/

/-- The objects `retype_region` creates. -/
def regionPtrs (ptr : Fl4Spec.ObjRef) (n k : Nat) : List Fl4Spec.ObjRef :=
  (List.range n).map fun p => Fl4Spec.ptrAdd ptr (p * k)

/-- The heap after `retype_region`. -/
def regionHeap (σ : Fl4Spec.State Unit) (ptrs : List Fl4Spec.ObjRef) (ko : Fl4Spec.KernelObject) :
    Fl4Spec.State Unit :=
  { σ with kheap := ptrs.foldr (fun p kh => Function.update kh p (some ko)) σ.kheap }

theorem retypeRegionWith_eq (bitsApi : Fl4Spec.ApiObjectType → Nat → Nat) (ptr : Fl4Spec.ObjRef) (n oBits : Nat)
    (t : Fl4Spec.ApiObjectType) (dev : Bool) (σ : Fl4Spec.State Unit) :
    Fl4Spec.retypeRegionWith (Z := Unit) bitsApi ptr n oBits t dev σ =
      ({(regionPtrs ptr n (2 ^ bitsApi t oBits),
        if t ≠ .untyped then regionHeap σ (regionPtrs ptr n (2 ^ bitsApi t oBits))
          (Fl4Spec.defaultObject t dev oBits σ.curDomain) else σ)}, False) := by
  unfold Fl4Spec.retypeRegionWith
  show ((pure _ : Fl4Spec.NonDet (Fl4Spec.State Unit) Nat) >>= _) σ = _
  rw [nd_pure_bind]
  show ((pure _ : Fl4Spec.NonDet (Fl4Spec.State Unit) (List Fl4Spec.ObjRef)) >>= _) σ = _
  rw [nd_pure_bind]
  by_cases ht : t ≠ .untyped
  · simp only [Fl4Spec.NonDet.when]
    rw [if_pos ht, if_pos ht]
    rw [nd_bind_one (m := (do
          let kh ← Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.kheap
          let cd ← Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curDomain
          let kh' ← pure (List.foldr (fun p kh => Function.update kh p (some (Fl4Spec.defaultObject t dev oBits cd))) kh
            (List.map (fun p => Fl4Spec.ptrAdd ptr (p * 2 ^ bitsApi t oBits)) (List.range n)))
          Fl4Spec.NonDet.modify fun s : Fl4Spec.State Unit => { s with kheap := kh' } : Fl4Spec.NonDet _ Unit))
      (s' := regionHeap σ (regionPtrs ptr n (2 ^ bitsApi t oBits)) (Fl4Spec.defaultObject t dev oBits σ.curDomain))
      (a := ())]
    · rfl
    · rw [nd_bind_single (gets_eq _ σ), nd_bind_single (gets_eq _ σ), nd_pure_bind]
      rfl
  · simp only [Fl4Spec.NonDet.when, ht, ↓reduceIte]
    rw [nd_bind_one (show (Fl4Spec.NonDet.pure () : Fl4Spec.NonDet (Fl4Spec.State Unit) Unit) σ = ({((), σ)}, False)
      from rfl)]
    rfl

theorem foldr_update_apply {α β : Type} [DecidableEq α] (ps : List α) (v : β) (f : α → β) (q : α) :
    (ps.foldr (fun p kh => Function.update kh p v) f) q = if q ∈ ps then v else f q := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldr_cons, List.mem_cons]
    by_cases h : q = p
    · subst h; simp
    · rw [Function.update_of_ne h, ih]; simp [h]

/-! ## The typed heap after `retype_region` -/

theorem slot_word_val_of {a : U64} {v : Nat} (hv : a.val = v) {k : U64} (hk : Off k) (h : v + 32 ≤ 2 ^ 64) :
    (wordOf a k).val = v + k.val := by
  rw [wordOf_val (by have := hk.lt; omega), hv]


/-- Hypothesis on the concrete state (**the free region is zero**): every
word of `lo .. hi` reads 0. FL4's `create_object` does not clear memory;
FL4 clears untyped memory when it resets an untyped cap and at boot. -/
def ZeroRegion (mem : U64 → U64) (lo hi : Nat) : Prop :=
  ∀ a : U64, P1.Aligned a → lo ≤ a.val → a.val < hi → mem a = 0#u64

/-- `q` is one of the new objects. -/
def NewP (A k n : Nat) (q : U64) : Prop := ∃ i, i < n ∧ q.val = A + i * k

theorem mem_regionPtrs (ptr : Fl4Spec.ObjRef) (A k n : Nat) (hA : ptr.toNat = A) (hk : 1 ≤ k)
    (hfit : A + n * k ≤ 2 ^ 64) (q : U64) : q.bv ∈ regionPtrs ptr n k ↔ NewP A k n q := by
  unfold regionPtrs NewP
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, he⟩
    refine ⟨i, hi, ?_⟩
    have h1 : i * k < n * k := Nat.mul_lt_mul_of_pos_right hi (by omega)
    have := congrArg BitVec.toNat he
    simp only [Fl4Spec.ptrAdd, BitVec.toNat_add, BitVec.toNat_ofNat, hA] at this
    rw [Nat.mod_eq_of_lt (a := i * k) (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact this.symm
  · rintro ⟨i, hi, he⟩
    refine ⟨i, hi, ?_⟩
    have h1 : i * k < n * k := Nat.mul_lt_mul_of_pos_right hi (by omega)
    apply BitVec.eq_of_toNat_eq
    simp only [Fl4Spec.ptrAdd, BitVec.toNat_add, BitVec.toNat_ofNat, hA]
    rw [Nat.mod_eq_of_lt (a := i * k) (by omega), Nat.mod_eq_of_lt (by omega)]
    exact he.symm

theorem not_newP {th : TypedHeap} {A k n : Nat} (hk : 1 ≤ k) (hfree : RegionFree th A (A + n * k)) {p : U64}
    {kd : ObjKind} (hp : th p = some kd) (hs : 1 ≤ objSize kd) : ¬ NewP A k n p := by
  rintro ⟨i, hi, he⟩
  have h1 : (i + 1) * k ≤ n * k := Nat.mul_le_mul_right _ hi
  rw [Nat.add_mul, Nat.one_mul] at h1
  rcases hfree p kd hp with h | h <;> omega

theorem objSize_pos_cnode (r : Nat) : 1 ≤ objSize (.cnode r) := by
  have := Nat.one_le_two_pow (n := r); simp [objSize]; omega

theorem objSize_pos_tcb : 1 ≤ objSize .tcb := by simp [objSize]

theorem extendTh_of_old {th : TypedHeap} {A k n : Nat} {kd' : ObjKind} (hk : 1 ≤ k) (hfree : RegionFree th A (A + n * k))
    {p : U64} {kd : ObjKind} (hp : th p = some kd) (hs : 1 ≤ objSize kd) : extendTh th A k n kd' p = th p :=
  extendTh_old (not_newP hk hfree hp hs)

/-- The ghost typed heap and the new heap agree on the old CNodes and TCBs. -/
theorem IsSlotAt.extend {th : TypedHeap} {A k n : Nat} {kd' : ObjKind} (hk : 1 ≤ k) (hfree : RegionFree th A (A + n * k))
    {p : U64} {i : Nat} (h : IsSlotAt th p i) : IsSlotAt (extendTh th A k n kd') p i := by
  rcases h with ⟨r, hr, hi⟩ | ⟨ht, hi⟩
  · exact Or.inl ⟨r, by rw [extendTh_of_old hk hfree hr (objSize_pos_cnode r)]; exact hr, hi⟩
  · exact Or.inr ⟨by rw [extendTh_of_old hk hfree ht objSize_pos_tcb]; exact ht, hi⟩

theorem IsSlot.extend {th : TypedHeap} {A k n : Nat} {kd' : ObjKind} (hk : 1 ≤ k) (hfree : RegionFree th A (A + n * k))
    {a : U64} (h : IsSlot th a) : IsSlot (extendTh th A k n kd') a := by
  obtain ⟨p, i, hi, rfl⟩ := h; exact ⟨p, i, hi.extend hk hfree, rfl⟩

theorem AbsSlot.extend {th : TypedHeap} {A k n : Nat} {kd' : ObjKind} (hk : 1 ≤ k) (hfree : RegionFree th A (A + n * k))
    {sl : Fl4Spec.CslotPtr} (h : AbsSlot th sl) : AbsSlot (extendTh th A k n kd') sl := by
  obtain ⟨p, h1, h2 | ⟨ht, hi⟩⟩ := h
  · exact ⟨p, h1, Or.inl (by rw [extendTh_of_old hk hfree h2 (objSize_pos_cnode _)]; exact h2)⟩
  · exact ⟨p, h1, Or.inr ⟨by rw [extendTh_of_old hk hfree ht objSize_pos_tcb]; exact ht, hi⟩⟩

theorem CapValid.extend {th : TypedHeap} {A k n : Nat} {kd' : ObjKind} (hk : 1 ≤ k) (hfree : RegionFree th A (A + n * k))
    {c : capability.Cap} (h : CapValid th c) : CapValid (extendTh th A k n kd') c := by
  cases c <;> simp only [CapValid] at h ⊢
  · exact ⟨by rw [extendTh_of_old hk hfree h.1 (objSize_pos_cnode _)]; exact h.1, h.2⟩
  · rw [extendTh_of_old hk hfree h objSize_pos_tcb]; exact h

/-- A slot of the grown heap is old or a slot of a new CNode. -/
theorem IsSlotAt.of_extend {th : TypedHeap} {A k n r0 : Nat} {p : U64} {i : Nat}
    (h : IsSlotAt (extendTh th A k n (.cnode r0)) p i) :
    IsSlotAt th p i ∨ (NewP A k n p ∧ i < 2 ^ r0) := by
  by_cases hp : NewP A k n p
  · rcases h with ⟨r, hr, hi⟩ | ⟨ht, -⟩
    · rw [extendTh_new hp] at hr; cases hr; exact Or.inr ⟨hp, hi⟩
    · rw [extendTh_new hp] at ht; cases ht
  · left
    rcases h with ⟨r, hr, hi⟩ | ⟨ht, hi⟩
    · rw [extendTh_old hp] at hr; exact Or.inl ⟨r, hr, hi⟩
    · rw [extendTh_old hp] at ht; exact Or.inr ⟨ht, hi⟩

theorem AbsSlot.of_extend {th : TypedHeap} {A k n r0 : Nat} {sl : Fl4Spec.CslotPtr}
    (h : AbsSlot (extendTh th A k n (.cnode r0)) sl) (hn : ¬ AbsSlot th sl) :
    ∃ p, NewP A k n p ∧ sl.1 = p.bv ∧ sl.2.length = r0 := by
  obtain ⟨p, h1, h2 | ⟨ht, hi⟩⟩ := h
  · by_cases hp : NewP A k n p
    · rw [extendTh_new hp] at h2; cases h2; exact ⟨p, hp, h1, rfl⟩
    · rw [extendTh_old hp] at h2; exact absurd ⟨p, h1, Or.inl h2⟩ hn
  · by_cases hp : NewP A k n p
    · rw [extendTh_new hp] at ht; cases ht
    · rw [extendTh_old hp] at ht; exact absurd ⟨p, h1, Or.inr ⟨ht, hi⟩⟩ hn

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **After `retype_region` of `n` CNodes of radix `us`** from `A` (a free,
zeroed region): the ghost typed heap grown by the new CNodes is `Placed`,
and the state relations hold for it against the spec's grown heap, where
the new CNodes are `empty_cnode`. `horig` (spec-state hypothesis): only
existing slots are original. -/
theorem extend_cnode_rel (th : TypedHeap) (mem : U64 → U64) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th mem σ) (hV : SlotsValid th mem) (hP : Placed th)
    (hM : MdbLinks th mem G) (hC : CdtRel th mem σ G)
    (horig : ∀ sl, σ.isOriginalCap sl = true → AbsSlot th sl)
    (ptr : Fl4Spec.ObjRef) (A n us : Nat) (hA : ptr.toNat = A)
    (hfit : A + n * (32 * 2 ^ us) ≤ 2 ^ 64) (hhigh : 2 ^ 64 - 2 ^ 47 ≤ A) (hal : A % 32 = 0)
    (hfree : RegionFree th A (A + n * (32 * 2 ^ us))) (hzero : ZeroRegion mem A (A + n * (32 * 2 ^ us))) :
    Placed (extendTh th A (32 * 2 ^ us) n (.cnode us)) ∧
    StateRel (extendTh th A (32 * 2 ^ us) n (.cnode us)) mem
      (regionHeap σ (regionPtrs ptr n (32 * 2 ^ us)) (.cnode us (Fl4Spec.emptyCnode us))) ∧
    SlotsValid (extendTh th A (32 * 2 ^ us) n (.cnode us)) mem ∧
    MdbLinks (extendTh th A (32 * 2 ^ us) n (.cnode us)) mem G ∧
    CdtRel (extendTh th A (32 * 2 ^ us) n (.cnode us)) mem
      (regionHeap σ (regionPtrs ptr n (32 * 2 ^ us)) (.cnode us (Fl4Spec.emptyCnode us))) G := by
  set k := 32 * 2 ^ us with hkdef
  have hk1 : 1 ≤ k := by have := Nat.one_le_two_pow (n := us); omega
  have hP' : Placed (extendTh th A k n (.cnode us)) := Placed.extend hP hfree (le_refl _) (le_refl _) hfit hhigh hal (by omega) (by simp [objSize, k])
  have hmemP := mem_regionPtrs ptr A k n hA hk1 hfit
  -- the words of a new CNode are zero
  have hnewz : ∀ p, NewP A k n p → ∀ i, i < 2 ^ us → ∀ off : Nat, off < 32 → off % 8 = 0 →
      ∀ a : U64, a.val = p.val + 32 * i + off → mem a = 0#u64 := by
    rintro p ⟨j, hj, hpj⟩ i hi off hoff ho8 a ha
    have h1 : (j + 1) * k ≤ n * k := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at h1
    have h2 : 32 * (i + 1) ≤ k := by rw [hkdef]; omega
    have h3 : j * k = 32 * (j * 2 ^ us) := by rw [hkdef]; ring
    apply hzero a (by show a.val % 8 = 0; omega) <;> omega
  have hslotv : ∀ p, NewP A k n p → ∀ i, i < 2 ^ us → (slotOf p i).val = p.val + 32 * i := by
    rintro p ⟨j, hj, hpj⟩ i hi
    have h1 : (j + 1) * k ≤ n * k := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at h1
    have h2 : 32 * (i + 1) ≤ k := by rw [hkdef]; omega
    exact slotOf_val (by omega)
  have hbnd : ∀ p, NewP A k n p → ∀ i, i < 2 ^ us → p.val + 32 * i + 32 ≤ 2 ^ 64 := by
    rintro p ⟨j, hj, hpj⟩ i hi
    have h1 : (j + 1) * k ≤ n * k := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at h1
    have h2 : 32 * (i + 1) ≤ k := by rw [hkdef]; omega
    omega
  have hnull : ∀ p, NewP A k n p → ∀ i, i < 2 ^ us → capAt mem (slotOf p i) = ok .Null := by
    intro p hp i hi
    have hv := hslotv p hp i hi
    have hb := hbnd p hp i hi
    rw [capAt_words, hnewz p hp i hi 0 (by decide) (by decide) _ (by rw [wordOf_zero, hv]; rfl),
      hnewz p hp i hi 8 (by decide) (by decide) _ (by rw [slot_word_val_of hv off8 (by omega)]; rfl)]
    exact decode_encode_null.2
  have hrevz : ∀ p, NewP A k n p → ∀ i, i < 2 ^ us → revOf mem (slotOf p i) = false := by
    intro p hp i hi
    have hb := hbnd p hp i hi
    unfold revOf
    rw [hnewz p hp i hi 24 (by decide) (by decide) _ (by rw [slot_word_val_of (hslotv p hp i hi) off24 (by omega)]; rfl)]
    rfl
  have hkh : ∀ q : U64, (regionHeap σ (regionPtrs ptr n k) (.cnode us (Fl4Spec.emptyCnode us))).kheap q.bv =
      if NewP A k n q then some (.cnode us (Fl4Spec.emptyCnode us)) else σ.kheap q.bv := by
    intro q
    simp only [regionHeap]
    rw [foldr_update_apply]
    by_cases h : NewP A k n q
    · rw [if_pos ((hmemP q).2 h), if_pos h]
    · rw [if_neg (fun e => h ((hmemP q).1 e)), if_neg h]
  refine ⟨hP', ?_, ?_, ?_, ?_⟩
  · refine ⟨fun p r hp => ?_, fun t ht => ?_⟩
    · by_cases hn : NewP A k n p
      · rw [extendTh_new hn] at hp; cases hp
        refine ⟨Fl4Spec.emptyCnode us, by rw [hkh, if_pos hn], ?_, fun idx hl => ?_⟩
        · unfold Fl4Spec.wellFormedCnodeN Fl4Spec.dom Fl4Spec.emptyCnode
          ext x; simp
        · refine ⟨.Null, .nullCap, ?_, by simp [Fl4Spec.emptyCnode, hl], ⟨trivial, rfl⟩⟩
          rw [slotAddr_ofBl]; exact hnull p hn _ (hl ▸ blVal_lt idx)
      · rw [extendTh_old hn] at hp
        rw [hkh, if_neg hn]; exact hR.cnode p r hp
    · by_cases hn : NewP A k n t
      · rw [extendTh_new hn] at ht; cases ht
      · rw [extendTh_old hn] at ht
        rw [hkh, if_neg hn]; exact hR.tcb t ht
  · refine ⟨fun p r hp i hi c hc => ?_, fun t ht i hi c hc => ?_⟩
    · by_cases hn : NewP A k n p
      · rw [extendTh_new hn] at hp; cases hp
        change capAt mem (slotOf p i) = _ at hc
        rw [hnull p hn i hi] at hc
        rw [← eq_of_ok_eq hc]; trivial
      · rw [extendTh_old hn] at hp
        exact (hV.cnode p r hp i hi c hc).extend hk1 hfree
    · by_cases hn : NewP A k n t
      · rw [extendTh_new hn] at ht; cases ht
      · rw [extendTh_old hn] at ht
        exact (hV.tcb t ht i hi c hc).extend hk1 hfree
  · refine ⟨hM.tree, hM.ne_nil, hM.chain, hM.head, hM.last, fun a => ?_⟩
    rw [hM.members a]
    constructor
    · rintro ⟨ha, hc⟩; exact ⟨ha.extend hk1 hfree, hc⟩
    · rintro ⟨⟨p, i, hi, rfl⟩, c, hc, hcn⟩
      rcases hi.of_extend with hi | ⟨hn, hi⟩
      · exact ⟨⟨p, i, hi, rfl⟩, c, hc, hcn⟩
      · rw [hnull p hn i hi] at hc; exact absurd (eq_of_ok_eq hc).symm hcn
  · have hnew : ∀ sl, AbsSlot (extendTh th A k n (.cnode us)) sl → ¬ AbsSlot th sl →
        ∃ p, NewP A k n p ∧ sl.1 = p.bv ∧ cslotAddr sl = slotOf p (blVal 0 sl.2) ∧ blVal 0 sl.2 < 2 ^ us := by
      intro sl h1 h2
      obtain ⟨p, hp, e1, e2⟩ := h1.of_extend h2
      refine ⟨p, hp, e1, ?_, e2 ▸ blVal_lt _⟩
      obtain ⟨a, b⟩ := sl; simp only at e1 ⊢; subst e1; exact slotAddr_ofBl _ _
    refine ⟨fun sl hsl => ?_, fun sl q hq => ?_, fun sl hsl => ?_, fun a b hab => ?_⟩
    · by_cases ho : AbsSlot th sl
      · exact hC.cdt sl ho
      · show (σ.cdt sl).map cslotAddr = _
        have h1 : σ.cdt sl = none := by
          cases e : σ.cdt sl with
          | none => rfl
          | some q => exact absurd (hC.cdt_slot sl q e).1 ho
        have h2 : G.par (cslotAddr sl) = none := by
          cases e : G.par (cslotAddr sl) with
          | none => rfl
          | some b =>
            obtain ⟨sl0, h0, he⟩ := hC.par_slot _ b e
            exact absurd (cslotAddr_inj hP' (h0.extend hk1 hfree) hsl he ▸ h0) ho
        rw [h1, h2]; rfl
    · obtain ⟨h1, h2⟩ := hC.cdt_slot sl q hq
      exact ⟨h1.extend hk1 hfree, h2.extend hk1 hfree⟩
    · by_cases ho : AbsSlot th sl
      · exact hC.orig sl ho
      · obtain ⟨p, hp, -, he, hi⟩ := hnew sl hsl ho
        show σ.isOriginalCap sl = _
        rw [he, hrevz p hp _ hi]
        cases e : σ.isOriginalCap sl
        · rfl
        · exact absurd (horig sl e) ho
    · obtain ⟨sl, h1, h2⟩ := hC.par_slot a b hab
      exact ⟨sl, h1.extend hk1 hfree, h2⟩

end
theorem CdtRel.of_cdt {Z : Type} {th : TypedHeap} {mem : U64 → U64} {σ σ' : Fl4Spec.State Z} {G : MdbGhost}
    (h : CdtRel th mem σ G) (h1 : σ'.cdt = σ.cdt) (h2 : σ'.isOriginalCap = σ.isOriginalCap) : CdtRel th mem σ' G :=
  ⟨fun sl hs => by rw [h1]; exact h.cdt sl hs, fun sl q hq => h.cdt_slot sl q (by rw [← h1]; exact hq),
    fun sl hs => by rw [h2]; exact h.orig sl hs, h.par_slot⟩

/-- **After `retype_region` of objects other than CNodes and TCBs** in a free
region: the typed heap does not change, and the state relations still
hold. -/
theorem extend_other_rel (th : TypedHeap) (mem : U64 → U64) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th mem σ) (hC : CdtRel th mem σ G)
    (ptr : Fl4Spec.ObjRef) (A n k : Nat) (hA : ptr.toNat = A) (hk1 : 1 ≤ k) (hfit : A + n * k ≤ 2 ^ 64)
    (hfree : RegionFree th A (A + n * k)) (ko : Fl4Spec.KernelObject) :
    StateRel th mem (regionHeap σ (regionPtrs ptr n k) ko) ∧ CdtRel th mem (regionHeap σ (regionPtrs ptr n k) ko) G := by
  have hmemP := mem_regionPtrs ptr A k n hA hk1 hfit
  have hkh : ∀ q : U64, (∃ kd, th q = some kd ∧ 1 ≤ objSize kd) →
      (regionHeap σ (regionPtrs ptr n k) ko).kheap q.bv = σ.kheap q.bv := by
    rintro q ⟨kd, hq, hs⟩
    simp only [regionHeap]
    rw [foldr_update_apply, if_neg (fun e => not_newP hk1 hfree hq hs ((hmemP q).1 e))]
  refine ⟨⟨fun p r hp => ?_, fun t ht => ?_⟩, hC.of_cdt rfl rfl⟩
  · rw [hkh p ⟨_, hp, objSize_pos_cnode r⟩]; exact hR.cnode p r hp
  · rw [hkh t ⟨_, ht, objSize_pos_tcb⟩]; exact hR.tcb t ht

/-! ## The loop -/

/-- `c`'s range misses `lo .. hi`. -/
def DisjR (c : capability.Cap) (lo hi : Nat) : Prop := topF c < lo ∨ hi ≤ baseF c

theorem desc_insG_true {th : TypedHeap} {mem : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G)
    {src dest : U64} (hdest : dest ∉ G.chains.flatten) (hsd : src ≠ dest) (y x : U64) :
    Mdb.Desc (insG G src dest true).par y x ↔
      Mdb.Desc G.par y x ∨ (y = dest ∧ (x = src ∨ Mdb.Desc G.par src x)) := by
  have hpd : ∀ z, G.par z ≠ some dest := fun z e => hdest (hM.tree.par_mem z dest e).2
  have hdn : G.par dest = none := by
    cases e : G.par dest with
    | none => rfl
    | some p => exact absurd (hM.tree.par_mem dest p e).1 hdest
  have hnp : (if true then some src else G.par src) ≠ some dest := by simp [hsd]
  show Mdb.Desc (Function.update G.par dest _) y x ↔ _
  rw [Mdb.desc_update_iff hpd hdn hnp, np_desc_iff]
  simp

theorem mapMx_cons_one {σ α β : Type} {f : α → Fl4Spec.NonDet σ β} {x : α} {xs : List α} {s s' : σ} {b : β}
    (h : f x s = ({(b, s')}, False)) : Fl4Spec.NonDet.mapMx f (x :: xs) s = Fl4Spec.NonDet.mapMx f xs s' := by
  show Fl4Spec.NonDet.bind (f x) (fun _ => Fl4Spec.NonDet.mapMx f xs) s = _
  have := nd_bind_one h (fun _ => Fl4Spec.NonDet.mapMx f xs)
  exact this

theorem mapMx_nil {σ α β : Type} (f : α → Fl4Spec.NonDet σ β) (s : σ) :
    Fl4Spec.NonDet.mapMx f [] s = ({((), s)}, False) := rfl

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- The invariant of `create_new_objects`' loop after `i` objects. -/
def LoopInv (th' : TypedHeap) (srcSl : Fl4Spec.CslotPtr) (srcC : capability.Cap) (σ1 : Fl4Spec.State Unit)
    (f : Fl4Spec.CslotPtr × Fl4Spec.ObjRef → Fl4Spec.NonDet (Fl4Spec.State Unit) Unit)
    (pairs : List (Fl4Spec.CslotPtr × Fl4Spec.ObjRef)) (A k win : Nat) (dslot : Nat → U64) (zlo zhi : Nat)
    (s : S) (i : Nat) : Prop :=
  ∃ σi Gi, (∀ σf, Fl4Spec.NonDet.mapMx f (pairs.drop i) σi = ({((), σf)}, False) →
      Fl4Spec.NonDet.mapMx f pairs σ1 = ({((), σf)}, False)) ∧
    StateRel th' (L.mem s) σi ∧ SlotsValid th' (L.mem s) ∧ MdbLinks th' (L.mem s) Gi ∧
    CdtRel th' (L.mem s) σi Gi ∧ MdbInv (L.mem s) Gi ∧
    capAt (L.mem s) (cslotAddr srcSl) = ok srcC ∧
    (∀ j, i ≤ j → j < win → capAt (L.mem s) (dslot j) = ok .Null) ∧
    (∀ x ∈ Gi.chains.flatten, physF (capV (L.mem s) x) = true →
      baseF (capV (L.mem s) x) ≤ topF (capV (L.mem s) x) ∧
      (DisjR (capV (L.mem s) x) (A + i * k) (A + win * k) ∨
        (isUt (capV (L.mem s) x) = true ∧ Within srcC (capV (L.mem s) x)))) ∧
    (∀ y, Mdb.Desc Gi.par y (cslotAddr srcSl) → DisjR (capV (L.mem s) y) (A + i * k) (A + win * k)) ∧
    ZeroRegion (L.mem s) zlo zhi

end
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem newCap_encWf {n : Nat} (hn : n = 0 ∨ (2 ≤ n ∧ n ≤ 6)) (base us : U64) (dev : Bool) (hus : us.val < 64)
    (hb : Canonical base) : EncWf (newCapOf n base us dev) := by
  unfold newCapOf
  rcases hn with rfl | ⟨h1, h2⟩
  · exact ⟨hb, hus⟩
  · interval_cases n <;> simp [EncWf] <;> first | exact hb | exact ⟨hb, hus⟩ | (refine ⟨hb, hus, ?_⟩; decide)

theorem isUt_newCap {n : Nat} {base us : U64} {dev : Bool} (h : isUt (newCapOf n base us dev) = true) :
    n = 0 ∧ newCapOf n base us dev = .Untyped base us 0#u64 dev := by
  unfold newCapOf at h ⊢
  by_cases h0 : n = 0
  · subst h0; simp
  · split_ifs at h ⊢ <;> simp_all [isUt]

theorem topF_ut (p sb f : U64) (d : Bool) (hsb : sb.val < 64) (hfit : p.val + 2 ^ sb.val ≤ 2 ^ 64) :
    baseF (.Untyped p sb f d) = p.val ∧ topF (.Untyped p sb f d) = p.val + 2 ^ sb.val - 1 := by
  refine ⟨by unfold baseF; rw [ptrF_ut], ?_⟩
  unfold topF
  rw [ptrF_ut, sizeF_ut]
  have hm := maskF_val (b := sb) hsb
  have h1 : 1 ≤ 2 ^ sb.val := Nat.one_le_two_pow
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits, hm]
  omega

/-- **One step of the loop**: inserting the `i`-th new cap keeps the
invariant. -/
theorem loop_step (th' : TypedHeap) (hP' : Placed th') {pp : U64} {rs : Nat} (hpp : th' pp = some (.cnode rs))
    {idx : List Bool} (hidx : idx.length = rs) {p sb fi : U64} {d : Bool}
    (hsb : sb.val < 64) (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64)
    (σ1 : Fl4Spec.State Unit) {dest : U64} {r : Nat} (hdest : th' dest = some (.cnode r)) (hr : r ≤ 64)
    (nt us : U64) (dev : Bool) (t : Fl4Spec.ApiObjectType) (ht : objTypeOf nt.val = some t)
    (hn : nt.val = 0 ∨ (2 ≤ nt.val ∧ nt.val ≤ 6)) (hus : us.val < 64) (hz : zOf nt.val us.val < 64)
    (hsc : nt.val = 5 → 7 ≤ us.val)
    (off win A : Nat) (hwin : off + win ≤ 2 ^ r)
    (hfit : A + win * 2 ^ zOf nt.val us.val ≤ 2 ^ 64) (hhigh : 2 ^ 64 - 2 ^ 47 ≤ A)
    (hpA : p.val ≤ A) (hAp : A + win * 2 ^ zOf nt.val us.val ≤ p.val + 2 ^ sb.val)
    (hnewcv : ∀ i, i < win →
      CapValid th' (newCapOf nt.val ⟨BitVec.ofNat 64 (A + i * 2 ^ zOf nt.val us.val)⟩ us dev))
    (zlo zhi : Nat) (hzs : ∀ a, IsSlot th' a → a.val + 32 ≤ zlo ∨ zhi ≤ a.val)
    (s : S) (i : Nat) (hi : i < win)
    (hinv : LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t us.val (pp.bv, idx) dev)
      ((windowSlots dest r off win).zip (regionPtrs (BitVec.ofNat 64 A) win (2 ^ zOf nt.val us.val)))
      A (2 ^ zOf nt.val us.val) win (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off + j))) zlo zhi s i) :
    cdt.insert_new_cap st s (cslotAddr (pp.bv, idx)) (slotAddr dest.bv (BitVec.ofNat 64 (off + i)))
      (newCapOf nt.val ⟨BitVec.ofNat 64 (A + i * 2 ^ zOf nt.val us.val)⟩ us dev) ⦃ s' =>
    LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t us.val (pp.bv, idx) dev)
      ((windowSlots dest r off win).zip (regionPtrs (BitVec.ofNat 64 A) win (2 ^ zOf nt.val us.val)))
      A (2 ^ zOf nt.val us.val) win (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off + j))) zlo zhi s' (i + 1) ⦄ := by
  obtain ⟨σi, Gi, hchain, hR, hV, hM, hC, hI, hsrc, hnull, hno, hdd, hzr⟩ := hinv
  set k := 2 ^ zOf nt.val us.val with hkdef
  have hk1 : 1 ≤ k := Nat.one_le_two_pow
  have hik : (i + 1) * k ≤ win * k := Nat.mul_le_mul_right _ hi
  rw [Nat.add_mul, Nat.one_mul] at hik
  set bi : U64 := ⟨BitVec.ofNat 64 (A + i * k)⟩ with hbi
  have hbiv : bi.val = A + i * k := by
    show (BitVec.ofNat 64 (A + i * k)).toNat = _; simp; omega
  set c := newCapOf nt.val bi us dev with hcdef
  obtain ⟨hcb, hct⟩ := newCap_range hn bi us dev hus hz (by rw [hbiv]; omega)
  rw [hbiv] at hcb hct
  -- the destination slot
  have hoff : off + i < 2 ^ r := by omega
  have hdsl : slotAddr dest.bv (BitVec.ofNat 64 (off + i)) = cslotAddr (dest.bv, Fl4Spec.natToCref r (off + i)) :=
    (cslotAddr_natToCref _ _ _ hr hoff).symm
  rw [hdsl]
  obtain ⟨hsb', hst'⟩ := topF_ut p sb fi d hsb hpfit
  have hsrcC := hsrc
  have hut : isUt (capability.Cap.Untyped p sb fi d) = true := rfl
  have hdnull := hnull i (le_refl _) hi
  simp only at hdnull
  rw [hdsl] at hdnull
  have hno' : ∀ x ∈ Gi.chains.flatten, physF (capV (L.mem s) x) = true →
      Disj (capV (L.mem s) x) c ∨ (isUt (capV (L.mem s) x) = true ∧ Within (.Untyped p sb fi d) (capV (L.mem s) x)) := by
    intro x hx hp
    rcases (hno x hx hp).2 with h | h
    · left; unfold DisjR at h; unfold Disj; rw [hcb, hct]; omega
    · exact Or.inr h
  have hdd' : ∀ y, Mdb.Desc Gi.par y (cslotAddr (pp.bv, idx)) → Disj (capV (L.mem s) y) c := by
    intro y hy
    have h := hdd y hy
    unfold DisjR at h; unfold Disj; rw [hcb, hct]; omega
  have hcin : Within c (.Untyped p sb fi d) := by
    unfold Within; rw [hcb, hct, hsb', hst']; omega
  have hsame : isUt c = true → Within (.Untyped p sb fi d) c → shape c = shape (.Untyped p sb fi d) := by
    intro hu hw
    obtain ⟨hn0, hce⟩ := isUt_newCap hu
    have hce' : c = .Untyped bi us 0#u64 dev := hce
    unfold Within at hw hcin
    rw [hce'] at hw hcin ⊢
    have hzu : zOf nt.val us.val = us.val := by simp [zOf, hn0]
    rw [hzu] at hkdef
    obtain ⟨hb1, ht1⟩ := topF_ut bi us 0#u64 dev hus (by rw [hbiv]; omega)
    rw [hb1, ht1, hsb', hst'] at hw
    rw [hb1, ht1, hsb', hst'] at hcin
    have e1 : bi = p := UScalar.eq_of_val_eq (by omega)
    have e2 : 2 ^ us.val = 2 ^ sb.val := by
      have := Nat.one_le_two_pow (n := us.val); have := Nat.one_le_two_pow (n := sb.val); omega
    have e3 : us = sb := UScalar.eq_of_val_eq (Nat.pow_right_injective (le_refl 2) e2)
    rw [e1, e3]; rfl
  have hreg : ∀ x ∈ Gi.chains.flatten, physF (capV (L.mem s) x) = true →
      baseF (capV (L.mem s) x) ≤ topF (capV (L.mem s) x) := fun x hx hp => (hno x hx hp).1
  have hca := newCap_rel ht hn bi us dev hus hsc
  have he : EncWf c := newCap_encWf hn bi us dev hus (canonical_of_high (by rw [hbiv]; omega))
  have hAd0 : AbsSlot th' (dest.bv, Fl4Spec.natToCref r (off + i)) :=
    ⟨dest, rfl, Or.inl (by rw [natToCref_length _ _ hr]; exact hdest)⟩
  have hAs0 : AbsSlot th' (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hnx0 : nextOf (L.mem s) (cslotAddr (pp.bv, idx)) = 0#u64 ∨ IsSlot th' (nextOf (L.mem s) (cslotAddr (pp.bv, idx))) := by
    have hsm : cslotAddr (pp.bv, idx) ∈ Gi.chains.flatten := (hM.members _).2 ⟨hAs0.isSlot, _, hsrcC, by simp⟩
    rcases hM.next_mem hsm with h | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr ((hM.members _).1 h).1
  obtain ⟨s', hs', hfull⟩ := spec_exists (insert_new_full th' s σi Gi hR hV hP' hM hC hI hpp hdest hidx
    (natToCref_length _ _ hr) hsrcC hut hdnull c _ hca (hnewcv i hi) he (newKind_newCap _ _ _ _)
    (physF_newCap _ _ _ _) (by rw [hcb, hct]; omega) hcin hreg hno' hdd' hsame)
  obtain ⟨s'', hs'', hfr⟩ := spec_exists (insert_new_frame (L := L) hP' s c _ _ hAs0.isSlot hAd0.isSlot hnx0)
  rw [hs'] at hs''; have := eq_of_ok_eq hs''; subst this
  rw [hs', WP.spec_ok]
  obtain ⟨σ', h1, hR', hV', hM', hC', hI', hW⟩ := hfull
  set src := cslotAddr (pp.bv, idx)
  set dsl := cslotAddr (dest.bv, Fl4Spec.natToCref r (off + i))
  have hAd : AbsSlot th' (dest.bv, Fl4Spec.natToCref r (off + i)) :=
    ⟨dest, rfl, Or.inl (by rw [natToCref_length _ _ hr]; exact hdest)⟩
  have hd : IsSlot th' dsl := hAd.isSlot
  have hAs : AbsSlot th' (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hs : IsSlot th' src := hAs.isSlot
  have hsd : src ≠ dsl := by
    intro e; rw [e, hdnull] at hsrcC; cases eq_of_ok_eq hsrcC
  have hdestm : dsl ∉ Gi.chains.flatten := by
    intro h; obtain ⟨-, c0, h0, hn0⟩ := (hM.members dsl).1 h
    rw [hdnull] at h0; exact hn0 (eq_of_ok_eq h0).symm
  have hcapW : ∀ x, IsSlot th' x → capAt (L.mem s') x = if x = dsl then ok c else capAt (L.mem s) x :=
    fun x hx => hW.capAt' hx he
  have hcapV : ∀ x, IsSlot th' x → x ≠ dsl → capV (L.mem s') x = capV (L.mem s) x := by
    intro x hx hne
    have := hcapW x hx; rw [if_neg hne, capAt_capV, capAt_capV] at this; exact eq_of_ok_eq this
  have hcapD : capV (L.mem s') dsl = c := by
    have := hcapW dsl hd; rw [if_pos rfl, capAt_capV] at this; exact eq_of_ok_eq this
  have hslot : ∀ x, x ∈ Gi.chains.flatten → IsSlot th' x := fun x h => ((hM.members x).1 h).1
  refine ⟨σ', insG Gi src dsl true, ?_, hR', hV', hM', hC', hI', ?_, ?_, ?_, ?_, ?_⟩
  · -- the spec's loop
    intro σf hf
    apply hchain σf
    have hlen : i < ((windowSlots dest r off win).zip (regionPtrs (BitVec.ofNat 64 A) win k)).length := by
      simp [windowSlots, regionPtrs]; exact hi
    rw [List.drop_eq_getElem_cons hlen]
    have hget : ((windowSlots dest r off win).zip (regionPtrs (BitVec.ofNat 64 A) win k))[i] =
        ((dest.bv, Fl4Spec.natToCref r (off + i)), bi.bv) := by
      simp only [List.getElem_zip, windowSlots, regionPtrs, List.getElem_map, List.getElem_range,
        List.getElem_range']
      congr 1
      · simp
      show Fl4Spec.ptrAdd (BitVec.ofNat 64 A) (i * k) = BitVec.ofNat 64 (A + i * k)
      simp [Fl4Spec.ptrAdd, BitVec.ofNat_add]
    rw [hget, mapMx_cons_one (createCap_eq t us.val (pp.bv, idx) _ dev bi.bv σi σ' h1)]
    exact hf
  · have := hcapW src hs; rw [if_neg hsd] at this; rw [this]; exact hsrcC
  · intro j hj1 hj2
    have hj : off + j < 2 ^ r := by omega
    have hdj : slotAddr dest.bv (BitVec.ofNat 64 (off + j)) = cslotAddr (dest.bv, Fl4Spec.natToCref r (off + j)) :=
      (cslotAddr_natToCref _ _ _ hr hj).symm
    have hAj : AbsSlot th' (dest.bv, Fl4Spec.natToCref r (off + j)) :=
      ⟨dest, rfl, Or.inl (by rw [natToCref_length _ _ hr]; exact hdest)⟩
    have hne : cslotAddr (dest.bv, Fl4Spec.natToCref r (off + j)) ≠ dsl := by
      intro e
      have := cslotAddr_inj hP' hAj hAd e
      simp only [Prod.mk.injEq, true_and] at this
      have h2 := congrArg (fun l => Fl4Spec.ofBl (w := 64) l) this
      rw [natToCref_eq _ _ hr, natToCref_eq _ _ hr, ofBl_bitsOf_eq, ofBl_bitsOf_eq] at h2
      have h3 := congrArg BitVec.toNat h2
      simp at h3
      have hrr : 2 ^ r ≤ 18446744073709551616 := by
        have := Nat.pow_le_pow_right (show 0 < 2 by decide) hr; simpa using this
      have hj64 : off + j < 18446744073709551616 := by omega
      have hi64 : off + i < 18446744073709551616 := by omega
      simp only [Nat.mod_eq_of_lt hj64, Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hoff] at h3
      omega
    show capAt _ (slotAddr dest.bv (BitVec.ofNat 64 (off + j))) = _
    rw [hdj, hcapW _ hAj.isSlot, if_neg hne]
    have := hnull j (by omega) hj2; simp only at this; rw [hdj] at this; exact this
  · intro x hx hp
    have hsrcm : src ∈ Gi.chains.flatten := (hM.members src).2 ⟨hs, _, hsrcC, by simp⟩
    rcases (mem_flatten_ins (dest := dsl) hsrcm).1 hx with hxd | hx'
    · subst hxd
      rw [hcapD] at hp ⊢
      refine ⟨by rw [hcb, hct]; omega, Or.inl (Or.inl (by rw [hct, Nat.add_mul, Nat.one_mul]; omega))⟩
    · have hxs := hslot x hx'
      have hxd : x ≠ dsl := fun e => hdestm (e ▸ hx')
      rw [hcapV x hxs hxd] at hp ⊢
      obtain ⟨h1', h2'⟩ := hno x hx' hp
      refine ⟨h1', ?_⟩
      rcases h2' with h | h
      · left; unfold DisjR at h ⊢; rw [Nat.add_mul, Nat.one_mul]; omega
      · exact Or.inr h
  · intro y hy
    rcases (desc_insG_true hM hdestm hsd y src).1 hy with hy | ⟨rfl, -⟩
    · have hym := (desc_mem hM hy).1
      rw [hcapV y (hslot y hym) (fun e => hdestm (e ▸ hym))]
      have := hdd y hy
      unfold DisjR at this ⊢; rw [Nat.add_mul, Nat.one_mul]; omega
    · rw [hcapD]; unfold DisjR; left; rw [hct, Nat.add_mul, Nat.one_mul]; omega
  · intro w hw h1 h2
    have hout : ∀ a, (a = src ∨ a = dsl ∨ (nextOf (L.mem s) src ≠ 0#u64 ∧ a = nextOf (L.mem s) src)) →
        ¬ (a.val ≤ w.val ∧ w.val < a.val + 32) := by
      rintro a (rfl | rfl | ⟨hz, rfl⟩)
      · have := hzs _ hs; omega
      · have := hzs _ hd; omega
      · have := hzs _ (hnx0.resolve_left hz); omega
    rw [hfr w hw hout]; exact hzr w hw h1 h2

end
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`create_new_objects`** (types 0, 2..6): from the loop invariant at 0,
the invariant at `win` (all new caps inserted), the arch state unchanged. -/
theorem create_loop_rel {A' : Type} (arI : machine.Arch A') (ar : A') (th' : TypedHeap) (hP' : Placed th')
    {pp : U64} {rs : Nat} (hpp : th' pp = some (.cnode rs))
    {idx : List Bool} (hidx : idx.length = rs) {p sb fi : U64} {d : Bool}
    (hsb : sb.val < 64) (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64)
    (σ1 : Fl4Spec.State Unit) {dest : U64} {r : Nat} (hdest : th' dest = some (.cnode r)) (hr : r ≤ 64)
    (nt us : U64) (dev : Bool) (t : Fl4Spec.ApiObjectType) (ht : objTypeOf nt.val = some t)
    (hn : nt.val = 0 ∨ (2 ≤ nt.val ∧ nt.val ≤ 6)) (hus : us.val < 64) (hz : zOf nt.val us.val < 64)
    (hsc : nt.val = 5 → 7 ≤ us.val)
    (off win base : U64) (hwin : off.val + win.val ≤ 2 ^ r)
    (hfit : base.val + win.val * 2 ^ zOf nt.val us.val ≤ 2 ^ 64) (hhigh : 2 ^ 64 - 2 ^ 47 ≤ base.val)
    (hpA : p.val ≤ base.val) (hAp : base.val + win.val * 2 ^ zOf nt.val us.val ≤ p.val + 2 ^ sb.val)
    (hnewcv : ∀ i, i < win.val →
      CapValid th' (newCapOf nt.val ⟨BitVec.ofNat 64 (base.val + i * 2 ^ zOf nt.val us.val)⟩ us dev))
    (zlo zhi : Nat) (hzs : ∀ a, IsSlot th' a → a.val + 32 ≤ zlo ∨ zhi ≤ a.val)
    (s : S)
    (hinv : LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 base.val) win.val (2 ^ zOf nt.val us.val)))
      base.val (2 ^ zOf nt.val us.val) win.val (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) zlo zhi s 0) :
    objects.create_new_objects st arI s ar nt (cslotAddr (pp.bv, idx)) dest off win base us dev ⦃ res =>
      res.2 = ar ∧ LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 base.val) win.val (2 ^ zOf nt.val us.val)))
      base.val (2 ^ zOf nt.val us.val) win.val (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) zlo zhi res.1
        win.val ⦄ := by
  have hn14 : nt.val < 14 := by omega
  unfold objects.create_new_objects
  rw [object_size_eq nt us hn14 hus]
  simp only [bind_ok]
  unfold objects.create_new_objects_loop
  have hk1 : 1 ≤ 2 ^ zOf nt.val us.val := Nat.one_le_two_pow
  have h63 : ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64).val = zOf nt.val us.val := by
    have : ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64).val =
        (⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64).val % 64 := by
      simp only [UScalar.val_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 6
    rw [this]
    show (BitVec.ofNat 64 (zOf nt.val us.val)).toNat % 64 = _
    simp; omega
  refine loop.spec_decr_nat (measure := fun x => win.val - x.2.2.val)
    (inv := fun x => x.2.1 = ar ∧ x.2.2.val ≤ win.val ∧ LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 base.val) win.val (2 ^ zOf nt.val us.val)))
      base.val (2 ^ zOf nt.val us.val) win.val (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) zlo zhi x.1
        x.2.2.val) _ _ _ ?_ ?_
  · rintro ⟨s1, a1, i⟩ ⟨ha, hiw, hI⟩
    simp only at ha hiw hI ⊢
    subst ha
    unfold objects.create_new_objects_loop.body
    by_cases hit : i < win
    · rw [if_pos hit]
      have hit' : i.val < win.val := hit
      simp only [lift, bind_ok]
      have hik : (i.val + 1) * 2 ^ zOf nt.val us.val ≤ win.val * 2 ^ zOf nt.val us.val :=
        Nat.mul_le_mul_right _ hit'
      rw [Nat.add_mul, Nat.one_mul] at hik
      obtain ⟨i2, hi2, hv2, -⟩ := spec_exists (UScalar.ShiftLeft_spec i
        ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64) _
        (by rw [h63]; simp [UScalarTy.U64_numBits_eq]; omega) rfl)
      rw [hi2]; simp only [bind_ok]
      have hi2v : i2.val = i.val * 2 ^ zOf nt.val us.val := by
        rw [hv2, h63, Nat.shiftLeft_eq]
        simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
      have hi3 : core.num.U64.wrapping_add base i2 =
          ⟨BitVec.ofNat 64 (base.val + i.val * 2 ^ zOf nt.val us.val)⟩ := by
        apply u64_ofNat_eq
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits, hi2v]; omega
      rw [hi3, create_object_eq arI s1 a1 nt _ us dev (by omega)]
      simp only [bind_ok, uncurry_apply_pair]
      have hi4 : (core.num.U64.wrapping_add off i).bv = BitVec.ofNat 64 (off.val + i.val) := by
        rw [bv_eq_ofNat]; congr 1
        have : off.val + i.val < 2 ^ 64 := by
          have := Nat.pow_le_pow_right (show 0 < 2 by decide) hr; omega
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
      rw [show obj.Slot.index dest (core.num.U64.wrapping_add off i) =
        ok (slotAddr dest.bv (BitVec.ofNat 64 (off.val + i.val))) by
          rw [spec_eq_ok (slot_index_spec dest _), hi4]]
      simp only [bind_ok]
      step with loop_step th' hP' hpp hidx hsb hpfit σ1 hdest hr nt us dev t ht hn hus hz hsc off.val win.val
        base.val hwin hfit hhigh hpA hAp hnewcv zlo zhi hzs s1 i.val hit' hI as ⟨s3, hs3⟩
      step as ⟨i5, hi5⟩
      refine ⟨by omega, by rw [hi5]; exact hs3, by omega⟩
    · rw [if_neg hit, WP.spec_ok]
      have : i.val = win.val := by have : ¬ i.val < win.val := hit; omega
      rw [this] at hI
      exact ⟨rfl, hI⟩
  · exact ⟨rfl, by simp, hinv⟩

end
end
end Fl4Proofs.P3
