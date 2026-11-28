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
import Fl4Proofs.P3.CreateLoopE
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

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


end

end Fl4Proofs.P3
