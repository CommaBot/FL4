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

(mmuAD gen 42b17) **`create_new_objects_loopI`**: the loop skeleton of `create_new_objects` for any per-object step
(`create_object`'s result in a predicate `Q`, then `insert_new_cap` back to the invariant `I` at `i + 1`); the native
`create_loop_rel` is its instance (proof only, statement unchanged); VirtRetypeLoop's VCPU loop and EptRetype's EPT
loop are the other instances.
-/
import Fl4Proofs.P3.UntypedMdb
import Fl4Proofs.P3.RetypeFresh
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

theorem sizeF_newCap {n : Nat} (hn : n ≤ 13) (base us : U64) (dev : Bool) (hus : us.val < 64) :
    (sizeF (newCapOf n base us dev)).val = zOf n us.val := by
  interval_cases n
  · rw [show newCapOf 0 base us dev = .Untyped base us 0#u64 dev from rfl, sizeF_ut]; simp [zOf]
  all_goals simp only [newCapOf, show ¬ (2 : Nat) = 3 by decide, show ¬ (3 : Nat) = 2 by decide] <;>
      simp <;> rw [sizeF_of rfl] <;> simp [fl4_abi.consts.bits.ENDPOINT, fl4_abi.consts.bits.TCB,
        fl4_abi.consts.bits.NOTIFICATION, fl4_abi.consts.bits.SLOT, fl4_abi.consts.bits.REPLY, zOf]
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega

theorem ptrF_newCap (n : Nat) (base us : U64) (dev : Bool) : ptrF (newCapOf n base us dev) = base := by
  apply newCapOf_ind (fun c => ptrF c = base) <;> intros <;> exact ptrF_of rfl

theorem physF_newCap (n : Nat) (base us : U64) (dev : Bool) : physF (newCapOf n base us dev) = true := by
  apply newCapOf_ind (fun c => physF c = true) <;> intros <;> exact physF_of rfl

theorem newKind_newCap (n : Nat) (base us : U64) (dev : Bool) : NewKind (newCapOf n base us dev) := by
  apply newCapOf_ind NewKind <;> intros <;> trivial

/-- **The range of a new cap** is its object: `2^z` bytes from `base`. -/
theorem newCap_range {n : Nat} (hn : n ≤ 13) (base us : U64) (dev : Bool) (hus : us.val < 64)
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
  all_goals first
    | exact h
    | exact ⟨by rw [extendTh_of_old hk hfree h.1 (objSize_pos_cnode _)]; exact h.1, h.2⟩
    | (rw [extendTh_of_old hk hfree h objSize_pos_tcb]; exact h)

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

/-- **`KTyped` for the new objects**: the spec's heap grown by `ko` at the new
pointers, against a typed heap that keeps the old objects and has the new
CNodes and TCBs `ko` makes. -/
theorem ktyped_region {th th' : TypedHeap} {σ : Fl4Spec.State Unit} (hK : KTyped th σ)
    (ptr : Fl4Spec.ObjRef) (A n k : Nat) (hA : ptr.toNat = A) (hk1 : 1 ≤ k) (hfit : A + n * k ≤ 2 ^ 64)
    (hfree : RegionFree th A (A + n * k)) (hold : ∀ q kd, th q = some kd → 1 ≤ objSize kd → th' q = th q)
    (ko : Fl4Spec.KernelObject)
    (hnew : ∀ q : U64, NewP A k n q → (∀ r cs, ko = .cnode r cs → Fl4Spec.wellFormedCnodeN r cs →
      th' q = some (.cnode r)) ∧ (∀ t, ko = .tcb t → th' q = some .tcb)) :
    KTyped th' (regionHeap σ (regionPtrs ptr n k) ko) := by
  have hmemP := mem_regionPtrs ptr A k n hA hk1 hfit
  intro o
  have hkh : (regionHeap σ (regionPtrs ptr n k) ko).kheap o = if o ∈ regionPtrs ptr n k then some ko else σ.kheap o := by
    simp only [regionHeap]; rw [foldr_update_apply]
  rw [hkh]
  by_cases hm : o ∈ regionPtrs ptr n k
  · rw [if_pos hm]
    have hn := hnew ⟨o⟩ ((hmemP ⟨o⟩).1 hm)
    exact ⟨fun r cs h hw => hn.1 r cs (Option.some.inj h) hw, fun t h => hn.2 t (Option.some.inj h)⟩
  · rw [if_neg hm]
    refine ⟨fun r cs h hw => ?_, fun t h => ?_⟩
    · have e := (hK o).1 r cs h hw; rw [hold _ _ e (objSize_pos_cnode r)]; exact e
    · have e := (hK o).2 t h; rw [hold _ _ e objSize_pos_tcb]; exact e

/-! ## The loop -/


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

/-- **The empty slots after were empty before, with the same link words**
(the retype writes no link word of a slot it leaves empty; feeds `DelInv.nc`
across a retype, `RetExp.nkeep`). -/
def NullKeep (th : TypedHeap) (m m' : U64 → U64) : Prop :=
  ∀ y, IsSlot th y → capV m' y = .Null → capV m y = .Null ∧ prevOf m' y = prevOf m y ∧ nextOf m' y = nextOf m y

theorem NullKeep.refl (th : TypedHeap) (m : U64 → U64) : NullKeep th m m := fun _ _ h => ⟨h, rfl, rfl⟩

theorem NullKeep.trans {th : TypedHeap} {m1 m2 m3 : U64 → U64} (h1 : NullKeep th m1 m2) (h2 : NullKeep th m2 m3) :
    NullKeep th m1 m3 := fun y hy h => by
  obtain ⟨e2, p2, n2⟩ := h2 y hy h
  obtain ⟨e1, p1, n1⟩ := h1 y hy e2
  exact ⟨e1, p2.trans p1, n2.trans n1⟩

theorem NullKeep.of_same {th : TypedHeap} {m m' : U64 → U64} (h : SlotsSame th m m') : NullKeep th m m' :=
  fun y hy e => ⟨by rw [← h.capV hy]; exact e, h.prevOf hy, h.nextOf hy⟩

/-- **The empty slots have clear links** (`DelInv.nc`'s statement on its own,
carried across a retype by `RetExp.nclr`). -/
def NullClr (th : TypedHeap) (m : U64 → U64) : Prop :=
  ∀ y, IsSlot th y → capV m y = .Null → prevOf m y = 0#u64 ∧ nextOf m y = 0#u64

/-- The link words (`+16`, `+24`) of every slot kept. -/
def LinksKeep (th : TypedHeap) (m m' : U64 → U64) : Prop :=
  ∀ y, IsSlot th y → m' (wordOf y 16#u64) = m (wordOf y 16#u64) ∧ m' (wordOf y 24#u64) = m (wordOf y 24#u64)

theorem LinksKeep.refl (th : TypedHeap) (m : U64 → U64) : LinksKeep th m m := fun _ _ => ⟨rfl, rfl⟩

theorem LinksKeep.trans {th : TypedHeap} {m1 m2 m3 : U64 → U64} (h1 : LinksKeep th m1 m2)
    (h2 : LinksKeep th m2 m3) : LinksKeep th m1 m3 := fun y hy =>
  ⟨(h2 y hy).1.trans (h1 y hy).1, (h2 y hy).2.trans (h1 y hy).2⟩

theorem LinksKeep.of_same {th : TypedHeap} {m m' : U64 → U64} (h : SlotsSame th m m') : LinksKeep th m m' :=
  fun y hy => ⟨(h y hy).2.2.1, (h y hy).2.2.2⟩

/-- `NullClr` kept when the links are and no slot becomes empty. -/
theorem NullClr.keep {th : TypedHeap} {m m' : U64 → U64} (hN : NullClr th m) (hL : LinksKeep th m m')
    (hc : ∀ y, IsSlot th y → capV m' y = .Null → capV m y = .Null) : NullClr th m' := fun y hy e => by
  obtain ⟨h1, h2⟩ := hN y hy (hc y hy e)
  refine ⟨?_, ?_⟩
  · unfold prevOf at h1 ⊢; rw [(hL y hy).1]; exact h1
  · unfold nextOf at h2 ⊢; rw [(hL y hy).2]; exact h2

theorem NullClr.of_same {th : TypedHeap} {m m' : U64 → U64} (hN : NullClr th m) (h : SlotsSame th m m') :
    NullClr th m' := hN.keep (LinksKeep.of_same h) (fun y hy e => by rw [← h.capV hy]; exact e)

/-- `NullClr` across the steps of a `NullKeep`. -/
theorem NullClr.of_keep {th : TypedHeap} {m m' : U64 → U64} (hN : NullClr th m) (h : NullKeep th m m') :
    NullClr th m' := fun y hy e => by
  obtain ⟨e0, hp, hn⟩ := h y hy e
  rw [hp, hn]; exact hN y hy e0

/-- **`NullClr` for a grown typed heap** whose new slots lie in a zero region. -/
theorem NullClr.grow {th th' : TypedHeap} (hP' : Placed th') {m : U64 → U64} (hN : NullClr th m) {lo hi : Nat}
    (hZ : ZeroRegion m lo hi) (hnew : ∀ y, IsSlot th' y → ¬ IsSlot th y → lo ≤ y.val ∧ y.val + 32 ≤ hi) :
    NullClr th' m := fun y hy e => by
  by_cases ho : IsSlot th y
  · exact hN y ho e
  · obtain ⟨h1, h2⟩ := hnew y hy ho
    have hz : ∀ k : U64, Off k → m (wordOf y k) = 0#u64 := fun k hk => by
      have hv := slot_word_val hP' hy hk
      have := hk.lt
      exact hZ _ (slot_word_aligned hP' hy hk) (by omega) (by omega)
    refine ⟨hz _ off16, ?_⟩
    unfold nextOf; rw [hz _ off24]
    exact congrArg (fun b => (⟨b⟩ : U64)) (sextF_canonical _ canonical_zero)

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`insert_new_cap` of a non-null cap into an empty slot keeps `NullKeep`**:
it writes the destination's words, the source's next link and the old next's
previous link, all of non-empty slots after. -/
theorem NullKeep.ins {th : TypedHeap} (hP : Placed th) {s s' : S} {G : MdbGhost} (hM : MdbLinks th (L.mem s) G)
    {c : capability.Cap} {src dest : U64} (hW : InsNWords (L := L) th s s' c src dest)
    (hsrc : src ∈ G.chains.flatten) (hd : IsSlot th dest) (hdest : dest ∉ G.chains.flatten)
    (hcn : c ≠ .Null) (he : EncWf c) : NullKeep th (L.mem s) (L.mem s') := by
  have hslot : ∀ x, x ∈ G.chains.flatten → IsSlot th x := fun x h => ((hM.members x).1 h).1
  have hs := hslot src hsrc
  have hne : src ≠ dest := fun e => hdest (e ▸ hsrc)
  have hnm : ∀ y, capV (L.mem s) y = .Null → y ∉ G.chains.flatten := fun y h hm => by
    obtain ⟨-, c0, h0, hn0⟩ := (hM.members y).1 hm
    rw [capAt_capV, h] at h0; exact hn0 (by simpa using h0.symm)
  have hNs : nextOf (L.mem s) src ≠ src := by
    rcases hM.next_mem hsrc with h | ⟨-, h⟩
    · rw [h]; exact (hs.ne_zero hP).symm
    · exact h
  have hNc : Canonical (nextOf (L.mem s) src) := by
    rcases hM.next_mem hsrc with h | ⟨h, -⟩
    · rw [h]; exact canonical_zero
    · exact (hslot _ h).canonical hP
  intro y hy h
  have hcap := hW.capAt' hy he
  have hyd : y ≠ dest := fun e => by
    subst e; rw [if_pos rfl, capAt_capV, h] at hcap; exact hcn (eq_of_ok_eq hcap).symm
  rw [if_neg hyd, capAt_capV, capAt_capV, h] at hcap
  have h0 : capV (L.mem s) y = .Null := (eq_of_ok_eq hcap).symm
  have hym := hnm y h0
  have hys : y ≠ src := fun e => hym (e ▸ hsrc)
  have hyn : ¬ (nextOf (L.mem s) src ≠ 0#u64 ∧ y = nextOf (L.mem s) src) := by
    rintro ⟨h0', rfl⟩
    rcases hM.next_mem hsrc with h1 | ⟨h1, -⟩
    · exact h0' h1
    · exact hym h1
  refine ⟨h0, ?_, ?_⟩
  · rw [hW.prevOf' hy hNs, if_neg hyd, if_neg hyn]
  · rw [hW.nextOf' hP hy hd hNc, if_neg hyd, if_neg hys]

/-- **`NullClr` for the typed heap grown by new objects over a zero window.** -/
theorem NullClr.extend {th : TypedHeap} {A k n : Nat} {kd : ObjKind} (hP' : Placed (extendTh th A k n kd))
    {m : U64 → U64} (hN : NullClr th m) (hsz : objSize kd ≤ k) (hZ : ZeroRegion m A (A + n * k)) :
    NullClr (extendTh th A k n kd) m := by
  refine hN.grow hP' hZ (fun y hy ho => ?_)
  obtain ⟨q, j, hj, rfl⟩ := hy
  have hv := hj.val hP'
  obtain ⟨k', hk', hjk⟩ := hj.size
  by_cases hq : ∃ i, i < n ∧ q.val = A + i * k
  · rw [extendTh_new hq] at hk'
    cases hk'
    obtain ⟨i, hi, hqi⟩ := hq
    have h1 : (i + 1) * k ≤ n * k := Nat.mul_le_mul_right _ hi
    rw [Nat.add_mul, Nat.one_mul] at h1
    rw [hv]; constructor <;> omega
  · refine absurd ⟨q, j, ?_, rfl⟩ ho
    have e := extendTh_old (th := th) (kd := kd) hq
    rcases hj with ⟨r, hr, hjr⟩ | ⟨ht, hjt⟩
    · exact Or.inl ⟨r, by rw [← e]; exact hr, hjr⟩
    · exact Or.inr ⟨by rw [← e]; exact ht, hjt⟩

/-- The invariant of `create_new_objects`' loop after `i` objects. -/
def LoopInv (th' : TypedHeap) (srcSl : Fl4Spec.CslotPtr) (srcC : capability.Cap) (σ1 : Fl4Spec.State Unit)
    (f : Fl4Spec.CslotPtr × Fl4Spec.ObjRef → Fl4Spec.NonDet (Fl4Spec.State Unit) Unit)
    (pairs : List (Fl4Spec.CslotPtr × Fl4Spec.ObjRef)) (A k win : Nat) (dslot : Nat → U64) (zlo zhi : Nat)
    (G0 : MdbGhost) (m0 : U64 → U64) (cj : Nat → capability.Cap) (s : S) (i : Nat) : Prop :=
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
    ZeroRegion (L.mem s) zlo zhi ∧
    (∀ x ∈ Gi.chains.flatten, x ∈ G0.chains.flatten ∨ ∃ j, j < i ∧ x = dslot j) ∧
    (∀ x ∈ G0.chains.flatten, x ∈ Gi.chains.flatten) ∧
    (∀ j, j < i → capV (L.mem s) (dslot j) = cj j) ∧
    (∀ x ∈ G0.chains.flatten, capV (L.mem s) x = capV m0 x) ∧
    (∀ y x, Mdb.Desc Gi.par y x ↔ Mdb.Desc G0.par y x ∨
      ∃ j, j < i ∧ y = dslot j ∧ (x = cslotAddr srcSl ∨ Mdb.Desc G0.par (cslotAddr srcSl) x)) ∧
    (FinM m0 G0 → FinM (L.mem s) Gi) ∧
    (∀ ch ∈ G0.chains, ∃ ch' ∈ Gi.chains, ∀ z ∈ ch, z ∈ ch') ∧
    (∀ x ∈ G0.chains.flatten, revOf (L.mem s) x = revOf m0 x) ∧
    NullKeep th' m0 (L.mem s)

/-- The caps a loop over `newCapOf` inserts. -/
def cjOf (n : Nat) (us : U64) (dev : Bool) (A k : Nat) : Nat → capability.Cap :=
  fun j => newCapOf n ⟨BitVec.ofNat 64 (A + j * k)⟩ us dev

end
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **A pointer range in one canonical half with a nonzero base**: `[lo, hi)`
below `2^47` or at or above `2^64 - 2^47`, and `0 < lo`. A RAM untyped's range
is in the kernel half (`CanonR.of_high`); a device untyped's range may lie in
the lower half (its pointer wrapped past `2^64`), DevJ's `DevApart`. -/
def CanonR (lo hi : Nat) : Prop := 0 < lo ∧ (hi ≤ 2 ^ 47 ∨ 2 ^ 64 - 2 ^ 47 ≤ lo)

theorem CanonR.of_high {lo hi : Nat} (h : 2 ^ 64 - 2 ^ 47 ≤ lo) : CanonR lo hi := ⟨by omega, Or.inr h⟩

theorem CanonR.sub {lo hi lo' hi' : Nat} (h : CanonR lo hi) (h1 : lo ≤ lo') (h2 : hi' ≤ hi) : CanonR lo' hi' :=
  ⟨by have := h.1; omega, h.2.imp (fun h => by omega) (fun h => by omega)⟩

theorem canonical_of_low {a : U64} (h : a.val < 2 ^ 47) : Canonical a := by
  left
  intro j hj hj'
  rw [← BitVec.getLsbD_eq_getElem]
  show a.val.testBit j = false
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) hj'))

theorem CanonR.canonical {lo hi : Nat} (h : CanonR lo hi) {a : U64} (h1 : lo ≤ a.val) (h2 : a.val < hi) :
    Canonical a := by
  rcases h.2 with h' | h'
  · exact canonical_of_low (by omega)
  · exact canonical_of_high (by omega)

theorem newCap_encWf {n : Nat} (hn : n ≤ 13) (base us : U64) (dev : Bool) (hus : us.val < 64)
    (hb : Canonical base) : EncWf (newCapOf n base us dev) := by
  unfold newCapOf
  interval_cases n <;> simp [EncWf] <;> first | exact hb | exact ⟨hb, hus⟩ | (refine ⟨hb, hus, ?_⟩; decide)

theorem isUt_newCap {n : Nat} {base us : U64} {dev : Bool} (h : isUt (newCapOf n base us dev) = true) :
    n = 0 ∧ newCapOf n base us dev = .Untyped base us 0#u64 dev := by
  revert h
  apply newCapOf_ind (fun c => isUt c = true → n = 0 ∧ c = .Untyped base us 0#u64 dev) <;> intros <;>
    first | exact ⟨by assumption, rfl⟩ | (simp [isUt] at *)

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
    (hn : nt.val ≤ 13) (hus : us.val < 64) (hz : zOf nt.val us.val < 64)
    (hsc : nt.val = 5 → 7 ≤ us.val)
    (off win A : Nat) (hwin : off + win ≤ 2 ^ r)
    (hfit : A + win * 2 ^ zOf nt.val us.val ≤ 2 ^ 64) (hcan : CanonR A (A + win * 2 ^ zOf nt.val us.val))
    (hpA : p.val ≤ A) (hAp : A + win * 2 ^ zOf nt.val us.val ≤ p.val + 2 ^ sb.val)
    (hnewcv : ∀ i, i < win →
      CapValid th' (newCapOf nt.val ⟨BitVec.ofNat 64 (A + i * 2 ^ zOf nt.val us.val)⟩ us dev))
    (zlo zhi : Nat) (hzs : ∀ a, IsSlot th' a → a.val + 32 ≤ zlo ∨ zhi ≤ a.val)
    (G0 : MdbGhost) (m0 : U64 → U64)
    (hsrcd : ∀ j, j < win → cslotAddr (pp.bv, idx) ≠ slotAddr dest.bv (BitVec.ofNat 64 (off + j)))
    (s : S) (i : Nat) (hi : i < win)
    (hinv : LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t us.val (pp.bv, idx) dev)
      ((windowSlots dest r off win).zip (regionPtrs (BitVec.ofNat 64 A) win (2 ^ zOf nt.val us.val)))
      A (2 ^ zOf nt.val us.val) win (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off + j))) zlo zhi G0 m0
      (cjOf nt.val us dev A (2 ^ zOf nt.val us.val)) s i) :
    cdt.insert_new_cap st s (cslotAddr (pp.bv, idx)) (slotAddr dest.bv (BitVec.ofNat 64 (off + i)))
      (newCapOf nt.val ⟨BitVec.ofNat 64 (A + i * 2 ^ zOf nt.val us.val)⟩ us dev) ⦃ s' =>
    LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t us.val (pp.bv, idx) dev)
      ((windowSlots dest r off win).zip (regionPtrs (BitVec.ofNat 64 A) win (2 ^ zOf nt.val us.val)))
      A (2 ^ zOf nt.val us.val) win (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off + j))) zlo zhi G0 m0
      (cjOf nt.val us dev A (2 ^ zOf nt.val us.val)) s' (i + 1) ⦄ := by
  obtain ⟨σi, Gi, hchain, hR, hV, hM, hC, hI, hsrc, hnull, hno, hdd, hzr, hT1, hT1b, hT2a, hT2b, hT3, hFM,
    hCh, hRv, hNK⟩ := hinv
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
  have he : EncWf c := newCap_encWf hn bi us dev hus (hcan.canonical (by rw [hbiv]; omega) (by rw [hbiv]; omega))
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
  have hNK' : NullKeep th' m0 (L.mem s') :=
    hNK.trans (NullKeep.ins hP' hM hW ((hM.members src).2 ⟨hs, _, hsrcC, by simp⟩) hd hdestm
      (newCap_ne_null _ _ _ _) he)
  refine ⟨σ', insG Gi src dsl true, ?_, hR', hV', hM', hC', hI', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun ch hch => ?_, fun x hx => ?_, hNK'⟩
  rotate_right
  · -- the revocable bits of the old slots
    have hx' := hT1b x hx
    rw [hW.revOf' (hslot x hx'), if_neg (fun (e : x = dsl) => hdestm (e ▸ hx'))]; exact hRv x hx
  rotate_right
  · -- the chains grow
    obtain ⟨ch1, hch1, hs1⟩ := hCh ch hch
    obtain ⟨ch2, hch2, hs2⟩ := insG_chains_sub Gi src dsl true ch1 hch1
    exact ⟨ch2, hch2, fun z hz => hs2 z (hs1 z hz)⟩
  rotate_right
  · -- finality: the new cap is fresh
    intro h0
    have hsrcm : src ∈ Gi.chains.flatten := (hM.members src).2 ⟨hs, _, hsrcC, by simp⟩
    refine (hFM h0).fresh_ins hsrcm hdestm true hM'.tree.nodup
      (fun z hz => hcapV z (hslot z hz) (fun e => hdestm (e ▸ hz))) (fun w hw => ?_)
    rw [hcapD, hcapV w (hslot w hw) (fun e => hdestm (e ▸ hw))]
    exact fresh_new (newKind_newCap _ _ _ _) (by rw [hcb, hct]; omega)
      (fun hp => ⟨hreg w hw hp, (hno' w hw hp).imp id (·.1)⟩)
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
  · have hsrcm : src ∈ Gi.chains.flatten := (hM.members src).2 ⟨hs, _, hsrcC, by simp⟩
    intro x hx
    rcases (mem_flatten_ins (dest := dsl) hsrcm).1 hx with hxd | hx'
    · exact Or.inr ⟨i, by omega, by rw [hxd]; exact hdsl.symm⟩
    · rcases hT1 x hx' with h | ⟨j, hj, he⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, by omega, he⟩
  · have hsrcm : src ∈ Gi.chains.flatten := (hM.members src).2 ⟨hs, _, hsrcC, by simp⟩
    intro x hx
    exact (mem_flatten_ins (dest := dsl) hsrcm).2 (Or.inr (hT1b x hx))
  · intro j hj
    by_cases hji : j = i
    · subst hji; show capV _ (slotAddr dest.bv (BitVec.ofNat 64 (off + j))) = _
      rw [hdsl, hcapD]; rfl
    · have hj' : j < i := by omega
      have hdj : IsSlot th' (slotAddr dest.bv (BitVec.ofNat 64 (off + j))) :=
        ⟨dest, off + j, Or.inl ⟨r, hdest, by omega⟩, rfl⟩
      have hne : slotAddr dest.bv (BitVec.ofNat 64 (off + j)) ≠ dsl := by
        intro e
        have hc := hT2a j hj'
        simp only at hc
        rw [e] at hc
        have := hcapW dsl hd
        rw [if_pos rfl, capAt_capV] at this
        have hdn := hdnull
        rw [capAt_capV] at hdn
        have h1 := eq_of_ok_eq hdn
        rw [h1] at hc
        unfold cjOf at hc
        exact newCap_ne_null _ _ _ _ hc.symm
      show capV _ (slotAddr dest.bv (BitVec.ofNat 64 (off + j))) = _
      rw [hcapV _ hdj hne]; exact hT2a j hj'
  · intro x hx
    have hx' := hT1b x hx
    rw [hcapV x (hslot x hx') (fun e => hdestm (e ▸ hx'))]; exact hT2b x hx
  · intro y x
    rw [desc_insG_true hM hdestm hsd y x, hT3 y x]
    have hsx : ∀ x, Mdb.Desc Gi.par src x ↔ Mdb.Desc G0.par src x := by
      intro x; rw [hT3]
      constructor
      · rintro (h | ⟨j, hj, he, -⟩)
        · exact h
        · exact absurd he (hsrcd j (by omega))
      · exact Or.inl
    rw [hsx x]
    constructor
    · rintro ((h | ⟨j, hj, hy1, hy2⟩) | ⟨hy1, hy2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨j, by omega, hy1, hy2⟩
      · exact Or.inr ⟨i, by omega, by rw [hy1]; exact hdsl.symm, hy2⟩
    · rintro (h | ⟨j, hj, hy1, hy2⟩)
      · exact Or.inl (Or.inl h)
      · by_cases hji : j = i
        · subst hji; exact Or.inr ⟨by rw [hy1]; exact hdsl, hy2⟩
        · exact Or.inl (Or.inr ⟨j, by omega, hy1, hy2⟩)

end
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`create_new_objects`' loop for any per-object step** (mmuAD gen 42b17): the loop skeleton every retype shares
(native types, VCPUs, EPT tables). From `I s 0`: if `create_object` of the `i`-th object (at `base + i·2^z`) keeps
the arch state and lands in `Q` (state after, the returned cap, `i`), and `insert_new_cap` of that cap into the `i`-th
window slot goes from `Q` to `I … (i + 1)`, the loop ends with the arch state unchanged and `I res win`. The
per-object footprint and the cap family live entirely in `I` / `Q` / `hco` / `hins`. -/
theorem create_new_objects_loopI {A' : Type} (arI : machine.Arch A') (ar : A') (s : S)
    (nt parent dest off win base us : U64) (dev : Bool) (zU : U64) (z : Nat) (hzU : zU.val = z)
    (hsz : objects.object_size nt us = ok (some zU)) (hz : z < 64)
    (hfit : base.val + win.val * 2 ^ z ≤ 2 ^ 64)
    (I : S → Nat → Prop) (Q : S → capability.Cap → Nat → Prop)
    (hco : ∀ (s1 : S) (i : Nat), i < win.val → I s1 i →
      objects.create_object st arI s1 ar nt ⟨BitVec.ofNat 64 (base.val + i * 2 ^ z)⟩ us dev ⦃ r =>
        r.2.2 = ar ∧ Q r.2.1 r.1 i ⦄)
    (hins : ∀ (s2 : S) (c : capability.Cap) (iw : U64), iw.val < win.val → Q s2 c iw.val →
      cdt.insert_new_cap st s2 parent (slotAddr dest.bv (core.num.U64.wrapping_add off iw).bv) c ⦃ s3 =>
        I s3 (iw.val + 1) ⦄)
    (h0 : I s 0) :
    objects.create_new_objects st arI s ar nt parent dest off win base us dev ⦃ res =>
      res.2 = ar ∧ I res.1 win.val ⦄ := by
  unfold objects.create_new_objects
  rw [hsz]
  simp only [bind_ok]
  unfold objects.create_new_objects_loop
  have hk1 : 1 ≤ 2 ^ z := Nat.one_le_two_pow
  have h63 : (zU &&& 63#u64).val = z := by
    have : (zU &&& 63#u64).val = zU.val % 64 := by
      simp only [UScalar.val_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 6
    rw [this, hzU]; omega
  refine loop.spec_decr_nat (measure := fun x => win.val - x.2.2.val)
    (inv := fun x => x.2.1 = ar ∧ x.2.2.val ≤ win.val ∧ I x.1 x.2.2.val) _ _ _ ?_ ⟨rfl, by simp, h0⟩
  rintro ⟨s1, a1, i⟩ ⟨ha, hiw, hI⟩
  simp only at ha hiw hI ⊢
  subst ha
  unfold objects.create_new_objects_loop.body
  by_cases hit : i < win
  · rw [if_pos hit]
    have hit' : i.val < win.val := hit
    simp only [lift, bind_ok]
    have hik : (i.val + 1) * 2 ^ z ≤ win.val * 2 ^ z := Nat.mul_le_mul_right _ hit'
    rw [Nat.add_mul, Nat.one_mul] at hik
    obtain ⟨i2, hi2, hv2, -⟩ := spec_exists (UScalar.ShiftLeft_spec i (zU &&& 63#u64) _
      (by rw [h63]; simp [UScalarTy.U64_numBits_eq]; omega) rfl)
    rw [hi2]; simp only [bind_ok]
    have hi2v : i2.val = i.val * 2 ^ z := by
      rw [hv2, h63, Nat.shiftLeft_eq]
      simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
    have hi3 : core.num.U64.wrapping_add base i2 = ⟨BitVec.ofNat 64 (base.val + i.val * 2 ^ z)⟩ := by
      apply u64_ofNat_eq
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits, hi2v]; omega
    rw [hi3]
    refine WP.spec_bind (hco s1 i.val hit' hI) fun r hr => ?_
    obtain ⟨c, s2, a2⟩ := r
    obtain ⟨e2, hQ⟩ := hr
    simp only at e2 hQ ⊢
    subst e2
    obtain ⟨sl, hsl, hsle⟩ := spec_exists (slot_index_spec dest (core.num.U64.wrapping_add off i))
    rw [hsl]; simp only [bind_ok]
    subst hsle
    refine WP.spec_bind (hins s2 c i hit' hQ) fun s3 h3 => ?_
    step as ⟨i5, hi5⟩
    have hi5' : i5.val = i.val + 1 := by omega
    refine ⟨by omega, ?_, by omega⟩
    rw [hi5']
    exact h3
  · rw [if_neg hit, WP.spec_ok]
    have : i.val = win.val := by have : ¬ i.val < win.val := hit; omega
    rw [this] at hI
    exact ⟨rfl, hI⟩

/-- **`create_new_objects`** (types 0, 2..6): from the loop invariant at 0,
the invariant at `win` (all new caps inserted), the arch state unchanged. -/
theorem create_loop_rel {A' : Type} (arI : machine.Arch A') (ar : A') (th' : TypedHeap) (hP' : Placed th')
    {pp : U64} {rs : Nat} (hpp : th' pp = some (.cnode rs))
    {idx : List Bool} (hidx : idx.length = rs) {p sb fi : U64} {d : Bool}
    (hsb : sb.val < 64) (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64)
    (σ1 : Fl4Spec.State Unit) {dest : U64} {r : Nat} (hdest : th' dest = some (.cnode r)) (hr : r ≤ 64)
    (nt us : U64) (dev : Bool) (t : Fl4Spec.ApiObjectType) (ht : objTypeOf nt.val = some t)
    (hn : nt.val = 0 ∨ (2 ≤ nt.val ∧ nt.val ≤ 13 ∧ nt.val ≠ 8)) (hus : us.val < 64) (hz : zOf nt.val us.val < 64)
    (hsc : nt.val = 5 → 7 ≤ us.val)
    (off win base : U64) (hwin : off.val + win.val ≤ 2 ^ r)
    (hfit : base.val + win.val * 2 ^ zOf nt.val us.val ≤ 2 ^ 64) (hhigh : 2 ^ 64 - 2 ^ 47 ≤ base.val)
    (hpA : p.val ≤ base.val) (hAp : base.val + win.val * 2 ^ zOf nt.val us.val ≤ p.val + 2 ^ sb.val)
    (hnewcv : ∀ i, i < win.val →
      CapValid th' (newCapOf nt.val ⟨BitVec.ofNat 64 (base.val + i * 2 ^ zOf nt.val us.val)⟩ us dev))
    (zlo zhi : Nat) (hzs : ∀ a, IsSlot th' a → a.val + 32 ≤ zlo ∨ zhi ≤ a.val)
    (G0 : MdbGhost) (m0 : U64 → U64)
    (hsrcd : ∀ j, j < win.val → cslotAddr (pp.bv, idx) ≠ slotAddr dest.bv (BitVec.ofNat 64 (off.val + j)))
    (s : S)
    (hinv : LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 base.val) win.val (2 ^ zOf nt.val us.val)))
      base.val (2 ^ zOf nt.val us.val) win.val (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) zlo zhi G0 m0
      (cjOf nt.val us dev base.val (2 ^ zOf nt.val us.val)) s 0) :
    objects.create_new_objects st arI s ar nt (cslotAddr (pp.bv, idx)) dest off win base us dev ⦃ res =>
      res.2 = ar ∧ LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 base.val) win.val (2 ^ zOf nt.val us.val)))
      base.val (2 ^ zOf nt.val us.val) win.val (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) zlo zhi G0 m0
      (cjOf nt.val us dev base.val (2 ^ zOf nt.val us.val)) res.1
        win.val ⦄ := by
  have hn14 : nt.val < 14 := by omega
  have hrr : 2 ^ r ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hr
  refine create_new_objects_loopI arI ar s nt _ dest off win base us dev _ (zOf nt.val us.val)
    (by show (BitVec.ofNat 64 (zOf nt.val us.val)).toNat = _; simp; omega) (object_size_eq nt us hn14 hus) hz hfit
    (fun s1 i => LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 base.val) win.val (2 ^ zOf nt.val us.val)))
      base.val (2 ^ zOf nt.val us.val) win.val (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) zlo zhi G0 m0
      (cjOf nt.val us dev base.val (2 ^ zOf nt.val us.val)) s1 i)
    (fun s2 c i => c = newCapOf nt.val ⟨BitVec.ofNat 64 (base.val + i * 2 ^ zOf nt.val us.val)⟩ us dev ∧
      LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 base.val) win.val (2 ^ zOf nt.val us.val)))
      base.val (2 ^ zOf nt.val us.val) win.val (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) zlo zhi G0 m0
      (cjOf nt.val us dev base.val (2 ^ zOf nt.val us.val)) s2 i)
    (fun s1 i _ hI => by
      rw [create_object_eq arI s1 ar nt _ us dev hn]; exact (WP.spec_ok _).2 ⟨rfl, rfl, hI⟩)
    (fun s2 c iw hi ⟨hc, hI⟩ => by
      subst hc
      have hi4 : (core.num.U64.wrapping_add off iw).bv = BitVec.ofNat 64 (off.val + iw.val) := by
        rw [bv_eq_ofNat]; congr 1
        have : off.val + iw.val < 2 ^ 64 := by omega
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
      rw [hi4]
      exact loop_step th' hP' hpp hidx hsb hpfit σ1 hdest hr nt us dev t ht (by omega) hus hz
        hsc off.val win.val base.val hwin hfit (CanonR.of_high hhigh) hpA hAp hnewcv zlo zhi hzs G0 m0 hsrcd s2 iw.val
        hi hI)
    hinv

end
end

/-- **Retype's new caps placed for the VSpace invariant** (`MdbStep.retype`'s
`hvc`): the objects inside a placed untyped region (`UtW`: so their
physical addresses are below `2^47`), each aligned to its size; a PML4 only
from a RAM untyped (`hdn`: a device untyped makes no PML4), so at or above
`PPTR_BASE`. -/
theorem cjOf_vplaced {n : Nat} {us : U64} {dev : Bool} {A k w : Nat} {p sb fi : U64} (hk : k = 2 ^ zOf n us.val)
    (hA : A % k = 0) (hpA : p.val ≤ A) (hfit : A + w * k ≤ 2 ^ 64) (hin : A + w * k ≤ p.val + 2 ^ sb.val)
    (hdn : dev = true → n ≠ 8)
    (hpb : UtW (.Untyped p sb fi dev)) :
    ∀ j, j < w → NewVPlaced (cjOf n us dev A k j) := by
  intro j hj
  have hm : (j + 1) * k ≤ w * k := Nat.mul_le_mul_right k hj
  rw [Nat.add_mul, Nat.one_mul] at hm
  have hk1 : 1 ≤ k := by rw [hk]; exact Nat.one_le_two_pow
  have hbv : (⟨BitVec.ofNat 64 (A + j * k)⟩ : U64).val = A + j * k := by
    show (BitVec.ofNat 64 (A + j * k)).toNat = _; simp; omega
  have hal : (A + j * k) % k = 0 := by rw [Nat.add_mul_mod_self_right, hA]
  have hph : paddrN (⟨BitVec.ofNat 64 (A + j * k)⟩ : U64) < 2 ^ 47 :=
    paddrN_within hpb (by rw [hbv]; omega) (by rw [hbv]; omega)
  have hpml : n = 8 → layout.PPTR_BASE.val ≤ A + j * k := fun hn => by
    cases dev
    · have := utW_ram hpb; omega
    · exact absurd hn (hdn rfl)
  unfold cjOf
  apply newCapOf_ind
  all_goals first
    | (intros; exact True.intro)
    | (intro hn; subst hn; simp only [NewVPlaced]; done)
    | (intro hn; subst hn; exact ⟨rfl, by rw [hbv]; exact hpml rfl⟩)
    | (intro hn; subst hn; simp only [zOf] at hk; norm_num at hk; subst hk
       refine ⟨rfl, hph, ?_⟩
       rw [hbv]; try simp only [frameBitsN]
       omega)

/-- Retype's new untyped caps carry the parent's device flag. -/
theorem cjOf_dev {n : Nat} {us : U64} {dev : Bool} {A k j : Nat} {q us' f : U64} {d : Bool}
    (h : cjOf n us dev A k j = .Untyped q us' f d) : d = dev := by
  have hu : isUt (cjOf n us dev A k j) = true := by rw [h]; rfl
  unfold cjOf at h hu
  rw [(isUt_newCap hu).2] at h
  injection h with _ _ _ e
  exact e.symm

end Fl4Proofs.P3
