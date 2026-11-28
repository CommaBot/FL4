/-
P3 (line mmuAD, gen 42b22): **the EPT create loop below the untyped retype body** — the pieces of FL4's
`create_new_objects` over EPT tables (type numbers 15-18) moved here unchanged so that UntypedSuccess's
`retype_fullC` (the retype for the native types and the EPT types, one body) can use them; and the retype's
window caps **`capsOf`**.

* Moved byte-identical: from P3/VirtLoopFrame `SlotW`, `loop_stepC_frame` (proof: `spec_and2` → `WP.spec_and`,
  as VirtRetypeInit's `spec_and2` sits downstream); from P3/EptStep1 `physF_ept`, `ptrF_ept`; from P3/EptRetype
  `eptLvl`, `create_object_ept`, `newCap_rel_ept`, `eptLvl_lt`, `object_size_ept`, `ejOf`, `sizeF_ept12`, `ejOf_val`,
  `ejOf_base`, `ejOf_top`, `create_new_objects_ept`.
* **`capsOf n us dev A k`**: the caps a retype of type number `n` inserts at `A`, `k` bytes apart — `cjOf` (UntypedLoop,
  `newCapOf`) for every type but 14..18, the `Vcpu` caps for 14, `ejOf n A` (unmapped `Ept` caps of the type's level)
  for 15..18; **`capsOf_native`**: `capsOf = cjOf` off 14..18.

No named premise. No `sorry`; only the three standard axioms.
-/
import Fl4Proofs.P3.VirtLoopC
import Fl4Proofs.P3.VirtInsCpu
import Fl4Proofs.P3.UntypedFrameBase
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtLoopFrame
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.VirtInsCpu

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- An aligned word inside a slot of `th`. -/
def SlotW (th : TypedHeap) (b : U64) : Prop := P1.Aligned b ∧ ∃ y, IsSlot th y ∧ y.val ≤ b.val ∧ b.val < y.val + 32

/-- **`loop_stepC` with `insert_new_cap`'s footprint** (module docstring). -/
theorem loop_stepC_frame (th' : TypedHeap) (hP' : Placed th') {pp : U64} {rs : Nat}
    (hpp : th' pp = some (.cnode rs))
    {idx : List Bool} (hidx : idx.length = rs) {p sb fi : U64} {d : Bool}
    (hsb : sb.val < 64) (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64)
    (σ1 : Fl4Spec.State Unit) {dest : U64} {r : Nat} (hdest : th' dest = some (.cnode r)) (hr : r ≤ 64)
    (t : Fl4Spec.ApiObjectType) (bits : Nat) (dev : Bool) (cj : Nat → capability.Cap)
    (off win A k : Nat) (hk1 : 1 ≤ k) (hwin : off + win ≤ 2 ^ r)
    (hfit : A + win * k ≤ 2 ^ 64)
    (hpA : p.val ≤ A) (hAp : A + win * k ≤ p.val + 2 ^ sb.val)
    (hcbF : ∀ i, i < win → baseF (cj i) = A + i * k) (hctF : ∀ i, i < win → topF (cj i) = A + i * k + k - 1)
    (hcuF : ∀ i, i < win → isUt (cj i) = false)
    (hcaF : ∀ i, i < win → CapRel (cj i) (Fl4Spec.defaultCap t (BitVec.ofNat 64 (A + i * k)) bits dev))
    (hceF : ∀ i, i < win → EncWf (cj i)) (hcnF : ∀ i, i < win → NewKindV (cj i))
    (hcpF : ∀ i, i < win → physF (cj i) = true)
    (hnewcv : ∀ i, i < win → CapValid th' (cj i))
    (zlo zhi : Nat) (hzs : ∀ a, IsSlot th' a → a.val + 32 ≤ zlo ∨ zhi ≤ a.val)
    (G0 : MdbGhost) (m0 : U64 → U64)
    (hsrcd : ∀ j, j < win → cslotAddr (pp.bv, idx) ≠ slotAddr dest.bv (BitVec.ofNat 64 (off + j)))
    (s : S) (i : Nat) (hi : i < win)
    (hinv : LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t bits (pp.bv, idx) dev)
      ((windowSlots dest r off win).zip (regionPtrs (BitVec.ofNat 64 A) win k))
      A k win (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off + j))) zlo zhi G0 m0 cj s i) :
    cdt.insert_new_cap st s (cslotAddr (pp.bv, idx)) (slotAddr dest.bv (BitVec.ofNat 64 (off + i))) (cj i) ⦃ s' =>
    LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t bits (pp.bv, idx) dev)
      ((windowSlots dest r off win).zip (regionPtrs (BitVec.ofNat 64 A) win k))
      A k win (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off + j))) zlo zhi G0 m0 cj s' (i + 1) ∧
    P1.WritesIn st s s' (SlotW th') ⦄ := by
  have hAs : AbsSlot th' (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hs : IsSlot th' (cslotAddr (pp.bv, idx)) := hAs.isSlot
  have hd : IsSlot th' (slotAddr dest.bv (BitVec.ofNat 64 (off + i))) := ⟨dest, off + i, Or.inl ⟨r, hdest, by omega⟩, rfl⟩
  have hnx0 : nextOf (L.mem s) (cslotAddr (pp.bv, idx)) = 0#u64 ∨
      IsSlot th' (nextOf (L.mem s) (cslotAddr (pp.bv, idx))) := by
    obtain ⟨σi, Gi, -, -, -, hM, -, -, hsrc, -⟩ := hinv
    have hsm : cslotAddr (pp.bv, idx) ∈ Gi.chains.flatten := (hM.members _).2 ⟨hs, _, hsrc, by simp⟩
    rcases hM.next_mem hsm with h | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr ((hM.members _).1 h).1
  refine WP.spec_mono (WP.spec_and (WP.spec_and (loop_stepC th' hP' hpp hidx hsb hpfit σ1 hdest hr t bits dev cj off win
    A k hk1 hwin hfit hpA hAp hcbF hctF hcuF hcaF hceF hcnF hcpF hnewcv zlo zhi hzs G0 m0 hsrcd s i hi hinv)
    (insert_new_frame hP' s (cj i) _ _ hs hd hnx0))
    (WP.spec_and (insert_new_cap_ksb s _ _ _) (insert_new_cap_cpu s _ _ _))) ?_
  rintro s' ⟨⟨h1, hfr⟩, hk, hc⟩
  refine ⟨h1, hk, hc, fun b hb hn => hfr b hb fun a ha hin => hn ⟨hb, a, ?_, hin⟩⟩
  rcases ha with rfl | rfl | ⟨hz, rfl⟩
  · exact hs
  · exact hd
  · exact hnx0.resolve_left hz

end

end

end Fl4Proofs.P3.VirtLoopFrame

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

theorem physF_ept (p l a v : U64) (m : Bool) : physF (.Ept p l m a v) = true := ok_inj (phys_eq _).symm

theorem ptrF_ept (p l a v : U64) (m : Bool) : ptrF (.Ept p l m a v) = p := ok_inj (ptr_eq _).symm

/-- The level FL4 gives a new EPT table of type number `n` (x86_64/objects.rs l. 47). -/
def eptLvl (n : Nat) : U64 :=
  if n = 15 then 0#u64 else if n = 16 then 39#u64 else if n = 17 then 30#u64 else 21#u64

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`create_object` for an EPT type** (15-18) writes nothing and returns the unmapped `Ept` cap. -/
theorem create_object_ept {A : Type} (arI : machine.Arch A) (s : S) (ar : A) (nt base us : U64) (dev : Bool)
    (h1 : 15 ≤ nt.val) (h2 : nt.val ≤ 18) :
    objects.create_object st arI s ar nt base us dev =
      ok (.Ept base (eptLvl nt.val) false 0#u64 0#u64, s, ar) := by
  have h14 : nt ≠ 14#u64 := by scalar_tac
  have h15 : nt ≥ 15#u64 := by scalar_tac
  have h18 : nt ≤ 18#u64 := by scalar_tac
  unfold objects.create_object objects.create_arch_object
  simp only [fl4_abi.consts.object.X86Vcpu, fl4_abi.consts.object.X86EptPml4, fl4_abi.consts.object.X86EptPt,
    h14, h15, h18, ↓reduceIte]
  simp only [fl4_abi.consts.object.Tcb, fl4_abi.consts.object.Endpoint, fl4_abi.consts.object.Notification,
    fl4_abi.consts.object.CapTable, fl4_abi.consts.object.Untyped, fl4_abi.consts.object.SchedContext,
    fl4_abi.consts.object.Reply, fl4_abi.consts.object.X86EptPdpt, fl4_abi.consts.object.X86EptPd, u64_eq_iff]
  unfold eptLvl
  generalize hv : nt.val = n at *
  interval_cases n <;> simp_all

end

/-- **The new EPT cap relates to the spec's default cap.** -/
theorem newCap_rel_ept {n : Nat} {t : Fl4Spec.ApiObjectType} (ht : objTypeOf n = some t) (h1 : 15 ≤ n)
    (h2 : n ≤ 18) (base : U64) (us : Nat) (dev : Bool) :
    CapRel (.Ept base (eptLvl n) false 0#u64 0#u64) (Fl4Spec.defaultCap t base.bv us dev) := by
  unfold objTypeOf Fl4Spec.archDataToObjType at ht
  interval_cases n <;> simp at ht <;> subst ht <;>
    exact ⟨trivial, by simp [absCap, eptLvl, Fl4Spec.defaultCap, Fl4Spec.archDefaultCap]⟩

theorem eptLvl_lt (n : Nat) : (eptLvl n).val < 64 := by
  unfold eptLvl
  by_cases h1 : n = 15
  · rw [if_pos h1]; decide
  rw [if_neg h1]
  by_cases h2 : n = 16
  · rw [if_pos h2]; decide
  rw [if_neg h2]
  by_cases h3 : n = 17
  · rw [if_pos h3]; decide
  rw [if_neg h3]; decide

/-- **`object_size` of an EPT type** (15-18) is 12 (objects.rs `object_size`). -/
theorem object_size_ept (nt us : U64) (h1 : 15 ≤ nt.val) (h2 : nt.val ≤ 18) :
    objects.object_size nt us = ok (some 12#u64) := by
  have h14 : nt ≠ 14#u64 := by scalar_tac
  have h15 : nt ≥ 15#u64 := by scalar_tac
  have h18 : nt ≤ 18#u64 := by scalar_tac
  unfold objects.object_size
  simp only [fl4_abi.consts.object.X86Vcpu, fl4_abi.consts.object.X86EptPml4, fl4_abi.consts.object.X86EptPt,
    h14, h15, h18, ↓reduceIte]

/-- The caps an EPT retype of type number `n` at `A` inserts: unmapped tables of the type's level. -/
def ejOf (n A : Nat) : Nat → capability.Cap := fun j => .Ept ⟨BitVec.ofNat 64 (A + j * 4096)⟩ (eptLvl n) false 0#u64 0#u64

theorem sizeF_ept12 (q l a v : U64) (m : Bool) : sizeF (.Ept q l m a v) = 12#u64 :=
  sizeF_of (by unfold objects.cap_size_bits; rfl)

theorem ejOf_val {A j : Nat} (h : A + j * 4096 < 2 ^ 64) :
    (⟨BitVec.ofNat 64 (A + j * 4096)⟩ : U64).val = A + j * 4096 := by
  show (BitVec.ofNat 64 (A + j * 4096)).toNat = _
  simp; omega

theorem ejOf_base {n A j : Nat} (h : A + j * 4096 < 2 ^ 64) : baseF (ejOf n A j) = A + j * 4096 := by
  unfold ejOf baseF; rw [ptrF_ept, ejOf_val h]

theorem ejOf_top {n A j : Nat} (h : A + j * 4096 + 4096 ≤ 2 ^ 64) :
    topF (ejOf n A j) = A + j * 4096 + 4096 - 1 := by
  unfold ejOf topF
  rw [ptrF_ept, sizeF_ept12]
  have hm := maskF_val (b := 12#u64) (by decide)
  have hv := ejOf_val (A := A) (j := j) (by omega)
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits, hm, hv]
  omega

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
open VirtLoopFrame

set_option maxHeartbeats 4000000 in
/-- **`create_new_objects` over EPT tables** (type numbers 15-18): UntypedLoop's `create_new_objects_loopI` with
`create_object_ept` (no write) as the object step and VirtLoopFrame's `loop_stepC_frame` over the caps `ejOf` as the
cap step. From `LoopInv … (ejOf nt base) s 0`: the arch state unchanged, all `win` unmapped `Ept` caps inserted
(`LoopInv … res win`), and FL4's writes only slot words of `th'`. The hypotheses are `create_loop_rel`'s placement
facts (window inside the untyped, canonical, the source slot not a window slot). -/
theorem create_new_objects_ept {A' : Type} (arI : machine.Arch A') (ar : A') (th' : TypedHeap) (hP' : Placed th')
    {pp : U64} {rs : Nat} (hpp : th' pp = some (.cnode rs))
    {idx : List Bool} (hidx : idx.length = rs) {p sb fi : U64} {d : Bool}
    (hsb : sb.val < 64) (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64)
    (σ1 : Fl4Spec.State Unit) {dest : U64} {r : Nat} (hdest : th' dest = some (.cnode r)) (hr : r ≤ 64)
    (nt us : U64) (dev : Bool) (t : Fl4Spec.ApiObjectType) (ht : objTypeOf nt.val = some t)
    (h15 : 15 ≤ nt.val) (h18 : nt.val ≤ 18)
    (off win base : U64) (hwin : off.val + win.val ≤ 2 ^ r)
    (hfit : base.val + win.val * 4096 ≤ 2 ^ 64) (hcan : CanonR base.val (base.val + win.val * 4096))
    (hpA : p.val ≤ base.val) (hAp : base.val + win.val * 4096 ≤ p.val + 2 ^ sb.val)
    (zlo zhi : Nat) (hzs : ∀ a, IsSlot th' a → a.val + 32 ≤ zlo ∨ zhi ≤ a.val)
    (G0 : MdbGhost) (m0 : U64 → U64)
    (hsrcd : ∀ j, j < win.val → cslotAddr (pp.bv, idx) ≠ slotAddr dest.bv (BitVec.ofNat 64 (off.val + j)))
    (s : S)
    (hinv : LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 base.val) win.val 4096))
      base.val 4096 win.val (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) zlo zhi G0 m0
      (ejOf nt.val base.val) s 0) :
    objects.create_new_objects st arI s ar nt (cslotAddr (pp.bv, idx)) dest off win base us dev ⦃ res =>
      res.2 = ar ∧ LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 base.val) win.val 4096))
      base.val 4096 win.val (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) zlo zhi G0 m0
      (ejOf nt.val base.val) res.1 win.val ∧ P1.WritesIn st s res.1 (SlotW th') ⦄ := by
  have hrr : 2 ^ r ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hr
  have hfit' : base.val + win.val * 2 ^ 12 ≤ 2 ^ 64 := by norm_num; omega
  refine WP.spec_mono (create_new_objects_loopI arI ar s nt _ dest off win base us dev 12#u64 12 rfl
    (object_size_ept nt us h15 h18) (by norm_num) hfit'
    (fun s1 i => LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 base.val) win.val 4096))
      base.val 4096 win.val (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) zlo zhi G0 m0
      (ejOf nt.val base.val) s1 i ∧ P1.WritesIn st s s1 (SlotW th'))
    (fun s2 c i => c = ejOf nt.val base.val i ∧ LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 base.val) win.val 4096))
      base.val 4096 win.val (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) zlo zhi G0 m0
      (ejOf nt.val base.val) s2 i ∧ P1.WritesIn st s s2 (SlotW th'))
    (fun s1 i _ hI => by
      rw [create_object_ept arI s1 ar nt _ us dev h15 h18]
      refine (WP.spec_ok _).2 ⟨rfl, ?_, hI⟩
      unfold ejOf; norm_num)
    (fun s2 c iw hi ⟨hc, hI, hW⟩ => by
      subst hc
      have hi4 : (core.num.U64.wrapping_add off iw).bv = BitVec.ofNat 64 (off.val + iw.val) := by
        rw [bv_eq_ofNat]; congr 1
        have : off.val + iw.val < 2 ^ 64 := by omega
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
      rw [hi4]
      have hstep := loop_stepC_frame (L := L) th' hP' hpp hidx hsb hpfit σ1 hdest hr t us.val dev
        (ejOf nt.val base.val) off.val win.val base.val 4096 (by norm_num) hwin hfit hpA hAp
        (fun j hj => ejOf_base (by have : (j + 1) * 4096 ≤ win.val * 4096 := Nat.mul_le_mul_right _ hj; omega))
        (fun j hj => ejOf_top (by have : (j + 1) * 4096 ≤ win.val * 4096 := Nat.mul_le_mul_right _ hj; omega))
        (fun j _ => rfl) (fun j _ => newCap_rel_ept ht h15 h18 ⟨BitVec.ofNat 64 (base.val + j * 4096)⟩ us.val dev)
        (fun j hj => by
          have : (j + 1) * 4096 ≤ win.val * 4096 := Nat.mul_le_mul_right _ hj
          have e := ejOf_val (A := base.val) (j := j) (by omega)
          show Canonical (⟨BitVec.ofNat 64 (base.val + j * 4096)⟩ : U64) ∧ (eptLvl nt.val).val < 64 ∧
            (0#u64 : U64).val < 2 ^ 20 ∧ (0#u64 : U64).val < 2 ^ 48
          exact ⟨hcan.canonical (by rw [e]; omega) (by rw [e]; omega), eptLvl_lt _, by decide, by decide⟩)
        (fun j _ => NewKindV.ept _ _ _ _ _) (fun j _ => physF_ept _ _ _ _ _) (fun j _ => trivial)
        zlo zhi hzs G0 m0 hsrcd s2 iw.val hi hI
      exact WP.spec_mono hstep fun s3 ⟨h1, h2⟩ => ⟨h1, (hW.trans h2).mono fun b h => h.elim id id⟩)
    ⟨hinv, P1.WritesIn.refl s _⟩) ?_
  rintro res ⟨h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end

/-- **The caps a retype of type number `n` inserts** at `A`, `k` bytes apart (module docstring): `cjOf` but for
the VT-x types — `Vcpu` caps for 14, unmapped `Ept` caps of the type's level (`ejOf`) for 15..18. -/
def capsOf (n : Nat) (us : U64) (dev : Bool) (A k : Nat) : Nat → capability.Cap :=
  if n = 14 then fun j => .Vcpu ⟨BitVec.ofNat 64 (A + j * k)⟩
  else if 15 ≤ n ∧ n ≤ 18 then ejOf n A else cjOf n us dev A k

/-- The size of an EPT table (types 15..18) is `2^12`. -/
theorem zOf_ept {n : Nat} (h1 : 15 ≤ n) (h2 : n ≤ 18) (us : Nat) : zOf n us = 12 := by
  unfold zOf
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- `capsOf` is `cjOf` off the VT-x types. -/
theorem capsOf_native {n : Nat} (h : n < 14 ∨ 18 < n) (us : U64) (dev : Bool) (A k : Nat) :
    capsOf n us dev A k = cjOf n us dev A k := by
  unfold capsOf; rw [if_neg (by omega), if_neg (by omega)]

/-- `capsOf` on the EPT types is `ejOf`. -/
theorem capsOf_ept {n : Nat} (h1 : 15 ≤ n) (h2 : n ≤ 18) (us : U64) (dev : Bool) (A k : Nat) :
    capsOf n us dev A k = ejOf n A := by
  unfold capsOf; rw [if_neg (by omega), if_pos ⟨h1, h2⟩]

end

end Fl4Proofs.P3
