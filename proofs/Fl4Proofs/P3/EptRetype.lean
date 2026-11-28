/-
P3 (line mmuAD, gen 42b5): **the retype of an EPT table, one object** — the per-object pieces of goal "EPT retype"
(42b2's plan): FL4's `create_object` for the four EPT types, the spec's default cap and object, and `EptCore` across
adding the fresh table with `UnmappedEmpty` established from the RAM-untyped zero invariant.

* **`create_object_ept`**: for the type numbers 15-18 (`X86EptPml4` … `X86EptPt`, fl4-abi), FL4's
  `objects.create_object` writes nothing and returns `Ept base (eptLvl n) false 0 0` (x86_64/objects.rs l. 46-50:
  levels 0 / 39 / 30 / 21, `create_object`'s arch fall-through, objects.rs l. 446 "The memory is already zero").
* **`newCap_rel_ept`** / **`default_ept`**: `objTypeOf 15..18` is `archDataToObjType 8..11` = `eptPml4Obj` …
  `eptPtObj` (Decode l. 471-474); the new cap relates to the spec's `defaultCap` (`archDefaultCap`, Structs
  l. 455-458) and the spec's new object is `.ept (eptLvl n).val 0` (`defaultArchObject`, Structs l. 472-475): the
  level `EptCore.capL` needs is the cap's.
* **`ept_zero_of_region`**, **`UtCapP3.ept_zero`**: a table lying in the free part `[p + fi, p + 2^sb)` of a RAM
  untyped cap (`NotDev`: untyped.rs l. 66 refuses non-frame objects from device untypeds) has its 512 words zero —
  P3's `UtCapP3.zero` (ScUtRetype l. 239, established by `reset_untyped`'s `clear_free`, untyped.rs l. 238-246, and
  at boot).
* **`EptCore.growZ`**: P3/EptStep2's `EptCore.grow` with its `hz` (the fresh table's words zero after the step)
  discharged from the words zero before (e.g. `UtCapP3.ept_zero`) and the step's writes missing the table: so
  `UnmappedEmpty` (i)-(ii) for the fresh `Ept t l false` cap comes from the zero invariant; (iii) is `huq` (one cap
  per new object, `create_new_objects`), (iv) `t ∉ X`. **`EptCore.growSZ`**: the same for a set `T` of new tables
  (P3/EptStep2's `EptCore.growS`, gen 42b5: `grow` generalised in place), the shape the create loop needs.

Gen 42b10: `growZ` / `growSZ` take `EptNamed` after the step as their last hypothesis (`hnm`, `EptCore.named`).

No named premise; the spec is not touched. No `sorry`; only the three standard axioms.

(mmuAD gen 42b17) **`create_new_objects_ept`**: FL4's create loop over EPT tables (type numbers 15-18) as an instance
of UntypedLoop's `create_new_objects_loopI` — `create_object_ept` (no write) as the object step, VirtLoopFrame's
`loop_stepC_frame` over the caps `ejOf nt base` (`Ept (base + j·4096) (eptLvl nt) false 0 0`) as the cap step: from
`LoopInv … 0`, the arch state kept, `LoopInv … win` (all caps inserted, related to `createCap`'s spec loop), FL4's
writes inside slot words. Pieces: `object_size_ept`, `eptLvl_lt`, `ejOf`, `sizeF_ept12` (P3/EptStep1's `ptrF_ept` / `physF_ept` reused),
`ejOf_val`, `ejOf_base`, `ejOf_top`. No named premise.
-/
import Fl4Proofs.P3.EptStep2
import Fl4Proofs.P3.EptStep1
import Fl4Proofs.P3.ScUtRetype
import Fl4Proofs.P3.UntypedRetype
import Fl4Proofs.P3.CnodeCopy
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

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

/-- **The spec's new EPT object** is the empty table at the cap's level. -/
theorem default_ept {n : Nat} {a : Fl4Spec.AObjectType} (ht : objTypeOf n = some (.archObject a)) (h1 : 15 ≤ n)
    (h2 : n ≤ 18) (dev : Bool) (k : Nat) :
    Fl4Spec.defaultArchObject a dev k = .ept (eptLvl n).val (fun _ => 0) := by
  unfold objTypeOf Fl4Spec.archDataToObjType at ht
  interval_cases n <;> simp at ht <;> subst ht <;> simp [eptLvl, Fl4Spec.defaultArchObject]

/-- A 4 KiB table inside a zero region has its 512 words zero. -/
theorem ept_zero_of_region {m : U64 → U64} {lo hi : Nat} (hZ : ZeroRegion m lo hi) {t : U64}
    (hal : t.val % 4096 = 0) (hlo : lo ≤ t.val) (hhi : t.val + 4096 ≤ hi) (hfit : t.val + 4096 ≤ 2 ^ 64) :
    ∀ i : BitVec 9, m (eptA t i) = 0#u64 := by
  intro i
  have e := eptA_val hfit i
  have hi9 := i.isLt
  exact hZ _ (by unfold P1.Aligned; rw [e]; omega) (by rw [e]; omega) (by rw [e]; omega)

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **A table in the free part of a RAM untyped cap is zero** (`UtCapP3.zero`). -/
theorem UtCapP3.ept_zero {A' : Type} {arI : machine.Arch A'} {th : TypedHeap} {s : S} {σ : Fl4Spec.State Unit}
    {G : MdbGhost} {sl : Fl4Spec.CslotPtr} {p sb fi : U64} (hU : Sched.UtCapP3 (L := L) arI th s σ G sl p sb fi)
    (hnd : Sched.NotDev (L.mem s) (cslotAddr sl) p sb fi) {t : U64} (hal : t.val % 4096 = 0)
    (hlo : p.val + fi.val ≤ t.val) (hhi : t.val + 4096 ≤ p.val + 2 ^ sb.val) :
    ∀ i : BitVec 9, L.mem s (eptA t i) = 0#u64 :=
  ept_zero_of_region (hU.zero hnd) hal hlo hhi (le_trans hhi hU.pfit)

variable {X : Set U64} {XL : U64 → Nat} {th : TypedHeap} {s : S} {σ : Fl4Spec.State Unit}

/-- **`EptCore` across the retype of a guest table `t`, its words zero before** (`EptCore.grow` with `hz` from
the words zero at `s` and the step's writes missing `t`'s 4 KiB). -/
theorem EptCore.growZ (C : EptCore (L := L) X XL th s σ) {t : U64} (htX : t ∉ X) (l : Nat)
    {th' : TypedHeap} {s' : S} {σ' : Fl4Spec.State Unit} {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hW : ∀ b, W b → ∀ u ∈ X, b.val < u.val ∨ u.val + 4096 ≤ b.val)
    (hWt : ∀ b, W b → b.val < t.val ∨ t.val + 4096 ≤ b.val)
    (hpl : t.val % 4096 = 0 ∧ t.val + 4096 ≤ 2 ^ 64)
    (hz0 : ∀ i : BitVec 9, L.mem s (eptA t i) = 0#u64)
    (hσt : σ'.kheap t.bv = some (.archObj (.ept l (fun _ => 0))))
    (hxk : ∀ u ∈ X, σ'.kheap u.bv = σ.kheap u.bv)
    (hne : ∀ r l' es, σ'.kheap r = some (.archObj (.ept l' es)) →
      r = t.bv ∨ ∃ l'' es', σ.kheap r = some (.archObj (.ept l'' es')))
    (hcap : ∀ y, IsSlot th' y → ∀ p l' a v (mm : Bool), capV (L.mem s') y = .Ept p l' mm a v →
      (p = t ∧ l'.val = l) ∨ (IsSlot th y ∧ capV (L.mem s) y = .Ept p l' mm a v))
    (huq : ∀ y y', IsSlot th' y → IsSlot th' y' → ∀ l1 l2 a1 a2 v1 v2 (m1 m2 : Bool),
      capV (L.mem s') y = .Ept t l1 m1 a1 v1 → capV (L.mem s') y' = .Ept t l2 m2 a2 v2 → y = y')
    (hX' : JExtEpt (L := L) (insert t X) th' s')
    (hge : ∀ e, GuestEntry σ' e → GuestEntry σ e)
    (hks : t.val + 4096 ≤ (L.ksb s').val ∨ (L.ksb s').val + 304384 ≤ t.val)
    (hsep : ∀ u ∈ insert t X, ∀ o ko, σ'.kheap o = some ko → o ≠ u.bv → EptApart u o ko)
    (h5 : EptSlotStep th th' (L.mem s) (L.mem s')) (hnm : EptNamed th' (L.mem s') σ')
    (htb : (l = 0 ∨ l = 39 ∨ l = 30 ∨ l = 21) ∧ Vs.PaM t 4503599627366400#u64) :
    EptCore (L := L) (insert t X) (Function.update XL t l) th' s' σ' := by
  refine C.grow htX l hw hW hpl (fun i => ?_) hσt hxk hne hcap huq hX' hge hks hsep h5 hnm htb
  have e := eptA_val hpl.2 i
  have hi9 := i.isLt
  rw [hw.mem_eq (b := eptA t i) (by unfold P1.Aligned; rw [e]; omega)
    (fun hb => by rcases hWt _ hb with h | h <;> omega)]
  exact hz0 i


/-- **`EptCore` across the retype of a set `T` of guest tables, their words zero before** (`EptCore.growS` with `hz`
from the words zero at `s` — `UtCapP3.ept_zero` per table — and the step's writes missing every table of `T`). -/
theorem EptCore.growSZ (C : EptCore (L := L) X XL th s σ) {T : Set U64} (hTX : ∀ t ∈ T, t ∉ X) (XL' : U64 → Nat)
    (hXL : ∀ u ∈ X, XL' u = XL u)
    {th' : TypedHeap} {s' : S} {σ' : Fl4Spec.State Unit} {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hW : ∀ b, W b → ∀ u ∈ X, b.val < u.val ∨ u.val + 4096 ≤ b.val)
    (hWT : ∀ b, W b → ∀ t ∈ T, b.val < t.val ∨ t.val + 4096 ≤ b.val)
    (hpl : ∀ t ∈ T, t.val % 4096 = 0 ∧ t.val + 4096 ≤ 2 ^ 64)
    (hz0 : ∀ t ∈ T, ∀ i : BitVec 9, L.mem s (eptA t i) = 0#u64)
    (hσt : ∀ t ∈ T, σ'.kheap t.bv = some (.archObj (.ept (XL' t) (fun _ => 0))))
    (hxk : ∀ u ∈ X, σ'.kheap u.bv = σ.kheap u.bv)
    (hne : ∀ r l' es, σ'.kheap r = some (.archObj (.ept l' es)) →
      (∃ t ∈ T, r = t.bv) ∨ ∃ l'' es', σ.kheap r = some (.archObj (.ept l'' es')))
    (hcap : ∀ y, IsSlot th' y → ∀ p l' a v (mm : Bool), capV (L.mem s') y = .Ept p l' mm a v →
      (p ∈ T ∧ l'.val = XL' p) ∨ (IsSlot th y ∧ capV (L.mem s) y = .Ept p l' mm a v))
    (huq : ∀ t ∈ T, ∀ y y', IsSlot th' y → IsSlot th' y' → ∀ l1 l2 a1 a2 v1 v2 (m1 m2 : Bool),
      capV (L.mem s') y = .Ept t l1 m1 a1 v1 → capV (L.mem s') y' = .Ept t l2 m2 a2 v2 → y = y')
    (hX' : JExtEpt (L := L) (T ∪ X) th' s')
    (hge : ∀ e, GuestEntry σ' e → GuestEntry σ e)
    (hks : ∀ t ∈ T, t.val + 4096 ≤ (L.ksb s').val ∨ (L.ksb s').val + 304384 ≤ t.val)
    (hsep : ∀ u ∈ T ∪ X, ∀ o ko, σ'.kheap o = some ko → o ≠ u.bv → EptApart u o ko)
    (h5 : EptSlotStep th th' (L.mem s) (L.mem s')) (hnm : EptNamed th' (L.mem s') σ')
    (htb : ∀ t ∈ T, (XL' t = 0 ∨ XL' t = 39 ∨ XL' t = 30 ∨ XL' t = 21) ∧ Vs.PaM t 4503599627366400#u64) :
    EptCore (L := L) (T ∪ X) XL' th' s' σ' := by
  refine C.growS hTX XL' hXL hw hW hpl (fun t ht i => ?_) hσt hxk hne hcap huq hX' hge hks hsep h5 hnm htb
  have e := eptA_val (hpl t ht).2 i
  have hi9 := i.isLt
  rw [hw.mem_eq (b := eptA t i) (by unfold P1.Aligned; rw [e]; have := (hpl t ht).1; omega)
    (fun hb => by rcases hWT _ hb t ht with h | h <;> omega)]
  exact hz0 t ht i

end


/-! ## The create loop over EPT tables (mmuAD gen 42b17) -/

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

end

end Fl4Proofs.P3
