/-
P3 (losfair/FL4#34), untyped: **no spec object in a device untyped cap's free
part** (`DevFree`, l4v `valid_untyped` for device caps), under an explicit
apartness hypothesis on the cap's range.

`Sched.SpecFree` (ScPlace) is asked of RAM untypeds only: since #34 a device
untyped's pointer `paddr + PPTR_BASE` may lie in the kernel image (physical
[510, 512) GiB), where the spec's IRQ-node CNodes and idle TCBs are, so the
fact is false of such a cap (handoff/devretype.md, "dj1 line"). Either fix
under discussion (a kernel change excluding that range, or keeping the kernel
and leaving the aliasing caps outside the J proof) gives a predicate `Ap` on
the cap's range (`p`, `sb`) saying it misses the kernel image and every
object of the typed heap. `DevFree Ap` asks `SpecFree`'s conclusion of the
device caps whose range satisfies `Ap`; `Ap` is a parameter, fixed across
steps.

* `SpecFreeP P`: `SpecFree`'s conclusion for every untyped cap of the MDB
  whose pointer, size and device flag satisfy `P`. `SpecFree` is
  `SpecFreeP RamP` (`specFreeP_ram_iff`), `DevFree Ap` is `SpecFreeP (DevP Ap)`.
* `SpecFreeP.frame`: across a step that keeps the objects' types (`KSz`) and
  whose untyped caps each have one before over the same region, of the same
  device flag, with a free index no larger (every step but the retype; the
  drop of the reset's region keeps the caps and only removes objects:
  `SpecFreeP.shrink`).
* `SpecFreeP.retype`: across `invoke_untyped` (with or without the reset,
  whose `delete_objects` removes the source's objects), from any source cap
  satisfying `P` (`hPs`): as SpecFreeRetJ's `SpecFree.retype`, whose only use
  of the RAM flag is the source's `SpecFree` fact.
-/
import Fl4Proofs.P3.SpecFreeRetJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-- **`SpecFree`'s conclusion for the untyped caps satisfying `P`** (of their
pointer, size bits and device flag). -/
def SpecFreeP (P : U64 → U64 → Bool → Prop) (mem : U64 → U64) (G : MdbGhost) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ x ∈ G.chains.flatten, ∀ p sb fi d, capV mem x = .Untyped p sb fi d → P p sb d →
    ∀ o ko, σ.kheap o = some ko →
      (o.toNat + 2 ^ Fl4Spec.objBits ko ≤ p.val ∨ p.val + 2 ^ sb.val ≤ o.toNat) ∨
      (p.val ≤ o.toNat ∧ o.toNat + 2 ^ Fl4Spec.objBits ko ≤ p.val + fi.val)

/-- The RAM caps. -/
def RamP : U64 → U64 → Bool → Prop := fun _ _ d => d = false

/-- The device caps whose range satisfies `Ap`. -/
def DevP (Ap : U64 → U64 → Prop) : U64 → U64 → Bool → Prop := fun p sb d => d = true ∧ Ap p sb

/-- **[J] candidate, l4v `valid_untyped` for device caps**: no spec object in
the free part of a device untyped cap whose range satisfies `Ap` (the cap
misses the kernel image and the typed heap's objects). -/
abbrev DevFree (Ap : U64 → U64 → Prop) (mem : U64 → U64) (G : MdbGhost) (σ : Fl4Spec.State Unit) : Prop :=
  SpecFreeP (DevP Ap) mem G σ

theorem specFreeP_ram_iff {mem : U64 → U64} {G : MdbGhost} {σ : Fl4Spec.State Unit} :
    SpecFreeP RamP mem G σ ↔ Sched.SpecFree mem G σ := by
  constructor
  · intro h x hx p sb fi hc o ko ho
    exact h x hx p sb fi false hc rfl o ko ho
  · intro h x hx p sb fi d hc hd o ko ho
    have hd' : d = false := hd
    subst hd'
    exact h x hx p sb fi hc o ko ho

/-- **`SpecFreeP` across a step that keeps the objects' types** (`KSz`) and
whose untyped caps each have one before over the same region, with the same
device flag and a free index no larger. -/
theorem SpecFreeP.frame {P : U64 → U64 → Bool → Prop} {m m' : U64 → U64} {G G' : MdbGhost}
    {σ σ' : Fl4Spec.State Unit}
    (h : SpecFreeP P m G σ)
    (hu : ∀ x' ∈ G'.chains.flatten, ∀ p sb fi' d, capV m' x' = .Untyped p sb fi' d →
      ∃ x ∈ G.chains.flatten, ∃ fi, capV m x = .Untyped p sb fi d ∧ fi.val ≤ fi'.val)
    (hk : KSz σ σ') : SpecFreeP P m' G' σ' := by
  intro x' hx' p sb fi' d hc hP o ko' ho
  obtain ⟨x, hx, fi, hc0, hfi⟩ := hu x' hx' p sb fi' d hc
  obtain ⟨ko, hko, hty⟩ := hk o ko' ho
  rw [← objBits_of_aType hty]
  rcases h x hx p sb fi d hc0 hP o ko hko with e | e
  · exact Or.inl e
  · right; omega

/-- **`SpecFreeP` across a step that only removes spec objects** (the drop of
a reset's region) and keeps the untyped caps. -/
theorem SpecFreeP.shrink {P : U64 → U64 → Bool → Prop} {m m' : U64 → U64} {G G' : MdbGhost}
    {σ σ' : Fl4Spec.State Unit}
    (h : SpecFreeP P m G σ)
    (hu : ∀ x' ∈ G'.chains.flatten, ∀ p sb fi' d, capV m' x' = .Untyped p sb fi' d →
      ∃ x ∈ G.chains.flatten, ∃ fi, capV m x = .Untyped p sb fi d ∧ fi.val ≤ fi'.val)
    (hk : ∀ o ko, σ'.kheap o = some ko → σ.kheap o = some ko) : SpecFreeP P m' G' σ' :=
  h.frame hu (fun o ko h => ⟨ko, hk o ko h, rfl⟩)

/-- **`SpecFreeP` across retype** (SpecFreeRetJ's `SpecFree.retype` for any
`P`): from the state before `set_thread_state` (`KSz` to `σ1`) and one
outcome of `invoke_untyped` from `σ1` whose heap is `σ'`'s, with FL4's
`RetExp` for the source slot and its window, the new caps untyped only for an
untyped retype, `default_object` no larger than the window's slices, and the
source cap satisfying `P` (`hPs`). For a device source, `P = DevP Ap` and
`hPs` is the source's apartness; a RAM source with `P = RamP` is
`SpecFree.retype`. -/
theorem SpecFreeP.retype {P : U64 → U64 → Bool → Prop} {th th' : TypedHeap} {m m' : U64 → U64}
    {G G' : MdbGhost}
    {σ σ1 σ' : Fl4Spec.State Unit} {bitsApi : Fl4Spec.ApiObjectType → Nat → Nat} {sl : Fl4Spec.CslotPtr}
    {rs : Bool} {pb rb : Fl4Spec.ObjRef} {t : Fl4Spec.ApiObjectType} {us : Nat} {slots : List Fl4Spec.CslotPtr}
    {dev : Bool} {A k w : Nat} {dslot : Nat → U64} {cj : Nat → capability.Cap} {p sb fi : U64} {d : Bool}
    (hSF : SpecFreeP P m G σ) (hU : UtInv m G) (hst : KSz σ σ1)
    (hcs : capV m (cslotAddr sl) = .Untyped p sb fi d) (hPs : P p sb d)
    (hg : Fl4Spec.getCap (Z := Unit) sl σ1 = ({(.untypedCap d p.bv sb.val fi.val, σ1)}, False))
    (hbelow : rs = false → p.val + fi.val ≤ rb.toNat)
    {y : Except Unit Unit × Fl4Spec.State Unit}
    (hy : y ∈ ((Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype sl rs pb rb t us slots dev)).run σ1).1)
    (hK : y.2.kheap = σ'.kheap)
    (hU' : UtInv m' G') (hI' : MdbInv m' G')
    (hE : RetExp th th' m m' G G' A k w dslot cj (cslotAddr sl))
    (hok : y.1 = .ok () → A = rb.toNat ∧ k = 2 ^ bitsApi t us ∧ w = slots.length ∧
      ∀ j, j < w → isUt (cj j) = true → t = .untyped)
    (hob : ∀ cd, Fl4Spec.objBits (Fl4Spec.defaultObject t dev us cd) ≤ bitsApi t us) :
    SpecFreeP P m' G' σ' := by
  intro x' hx' p' sb' fi' d' hcx' hP' o ko' ho
  rw [← hK] at ho
  obtain ⟨hxG, p0, sb0, fi0, fi1, d0, e0, e1, hpA, hAf1, hAs, -, hoth⟩ := hE.usrc
  rw [hcs] at e0; cases e0
  have hsb : sb.val < 64 := capV_ut_sb hcs
  have hfitS : p.val + 2 ^ sb.val ≤ 2 ^ 64 := by
    have hreg := hU.reg _ hxG (by rw [hcs]; exact physF_ut _ _ _ _)
    rw [hcs] at hreg
    exact (ut_range hsb hreg).2.2
  have hfiS : fi.val ≤ 2 ^ sb.val := hU.fib _ hxG p sb fi d hcs
  have hk1 := hE.k1
  obtain ⟨hrs, hkh⟩ := invokeUntyped_kheap bitsApi sl rs pb rb t us slots dev σ1 hg y hy
  rcases hkh o ko' ho with ⟨ko1, h1, e1', hR⟩ | ⟨ht, hm, cd, ecd⟩
  · -- an old object
    obtain ⟨ko0, h0, e0'⟩ := hst o ko1 h1
    rw [← objBits_of_aType (e0'.trans e1')]
    have hb1 := Nat.one_le_two_pow (n := Fl4Spec.objBits ko0)
    -- against the source: outside its range, or below the window
    have hOW : (o.toNat + 2 ^ Fl4Spec.objBits ko0 ≤ p.val ∨ p.val + 2 ^ sb.val ≤ o.toNat) ∨
        (p.val ≤ o.toNat ∧ o.toNat + 2 ^ Fl4Spec.objBits ko0 ≤ A) := by
      rcases hSF _ hxG p sb fi d hcs hPs o ko0 h0 with e | ⟨l1, l2⟩
      · exact Or.inl e
      · by_cases hc : rs = true ∧ fi.val ≠ 0
        · rw [if_pos hc] at hR
          have := (regionSet_iff p ⟨o⟩ sb.val hsb hfitS).not.1 hR
          exact absurd ⟨l1, by show o.toNat < _; omega⟩ this
        · rcases Bool.eq_false_or_eq_true rs with hr | hr
          · have hz : fi.val = 0 := by by_contra hz; exact hc ⟨hr, hz⟩
            omega
          · have := hbelow hr
            have hy1 : y.1 = .ok () := by rcases hrs with h | h; exact h; rw [hr] at h; cases h
            have := (hok hy1).1
            right; omega
    rcases hE.gmem x' hx' with hxG' | ⟨j, hj, rfl⟩
    · have hut : isUt (capV m x') = true := by
        by_contra hn
        have := (hE.keep x' hxG' (by simpa using hn)).2
        rw [hcx'] at this; rw [← this] at hn; exact hn rfl
      by_cases hxs : x' = cslotAddr sl
      · subst hxs
        rw [e1] at hcx'; cases hcx'
        rcases hOW with e | ⟨l1, l2⟩
        · exact Or.inl e
        · right; omega
      · rw [hoth x' hxG' hut hxs] at hcx'
        exact hSF x' hxG' p' sb' fi' d' hcx' hP' o ko0 h0
    · -- a new cap: in the window
      have hc := hE.newc j hj
      rw [hcx'] at hc
      have hb := hE.cbase j hj
      have ht := hE.ctop j hj
      rw [← hc] at hb ht
      have hsb' := capV_ut_sb hcx'
      have hreg := hU'.reg _ hx' (by rw [hcx']; exact physF_ut _ _ _ _)
      rw [hcx'] at hreg
      obtain ⟨b1, t1, -⟩ := ut_range hsb' hreg
      have hjk : j * k + k ≤ w * k := by
        have := Nat.mul_le_mul_right k (show j + 1 ≤ w by omega); rw [Nat.add_mul, Nat.one_mul] at this; exact this
      have hp2 := Nat.one_le_two_pow (n := sb'.val)
      left
      rcases hOW with e | ⟨l1, l2⟩ <;> omega
  · -- a new object, in the range of its non-untyped cap
    by_cases hy1 : y.1 = .ok ()
    swap
    · rw [if_neg hy1] at hm; simp [regionPtrs] at hm
    rw [if_pos hy1] at hm
    obtain ⟨hA, hk, hw, hcu⟩ := hok hy1
    rw [← hk] at hm
    obtain ⟨j, hj, rfl⟩ := regionPtrs_mem hm
    rw [← hw] at hj
    have hjk : j * k + k ≤ w * k := by
      have := Nat.mul_le_mul_right k (show j + 1 ≤ w by omega); rw [Nat.add_mul, Nat.one_mul] at this; exact this
    have hov : (Fl4Spec.ptrAdd rb (j * k)).toNat = A + j * k := by
      rw [hA]; exact ptrAdd_toNat (by omega)
    rw [hov]
    have hob' : 2 ^ Fl4Spec.objBits ko' ≤ k := by
      rw [hk, objBits_of_aType ecd]; exact Nat.pow_le_pow_right (show 0 < 2 by decide) (hob cd)
    have hdm := hE.newm j hj
    have hdc := hE.newc j hj
    have hdp := hE.cphys j hj
    have hdb := hE.cbase j hj
    have hdt := hE.ctop j hj
    have hnu : isUt (cj j) = false := by
      cases e : isUt (cj j)
      · rfl
      · exact absurd (hcu j hj e) ht
    have hsb' := capV_ut_sb hcx'
    have hreg := hU'.reg _ hx' (by rw [hcx']; exact physF_ut _ _ _ _)
    rw [hcx'] at hreg
    obtain ⟨b1, t1, -⟩ := ut_range hsb' hreg
    have hp2 := Nat.one_le_two_pow (n := sb'.val)
    have hb0 := Nat.one_le_two_pow (n := Fl4Spec.objBits ko')
    have hne : dslot j ≠ x' := by
      rintro rfl; rw [hdc] at hcx'; rw [hcx'] at hnu; cases hnu
    by_cases hdj : Disj (capV m' (dslot j)) (capV m' x')
    · unfold Disj at hdj
      rw [hdc, hcx', b1, t1, hdt, hdb] at hdj
      left; omega
    · rcases hU'.drange x' hx' p' sb' fi' d' hcx' (dslot j) hdm hne (by rw [hdc]; exact hdp) hdj with h | h
      · obtain ⟨-, i1, i2⟩ := hU'.inc x' hx' p' sb' fi' d' hcx' (dslot j) h
        rw [hdc, hdb] at i1; rw [hdc, hdt] at i2
        right; omega
      · have := hI'.anc_ut h (by rw [hcx']; rfl)
        rw [hdc, hnu] at this; cases this

/-- **`DevFree` across retype from an apart device cap** (`SpecFreeP.retype`
at `DevP Ap`). -/
theorem DevFree.retype {Ap : U64 → U64 → Prop} {th th' : TypedHeap} {m m' : U64 → U64}
    {G G' : MdbGhost}
    {σ σ1 σ' : Fl4Spec.State Unit} {bitsApi : Fl4Spec.ApiObjectType → Nat → Nat} {sl : Fl4Spec.CslotPtr}
    {rs : Bool} {pb rb : Fl4Spec.ObjRef} {t : Fl4Spec.ApiObjectType} {us : Nat} {slots : List Fl4Spec.CslotPtr}
    {dev : Bool} {A k w : Nat} {dslot : Nat → U64} {cj : Nat → capability.Cap} {p sb fi : U64}
    (hSF : DevFree Ap m G σ) (hU : UtInv m G) (hst : KSz σ σ1)
    (hcs : capV m (cslotAddr sl) = .Untyped p sb fi true) (hAp : Ap p sb)
    (hg : Fl4Spec.getCap (Z := Unit) sl σ1 = ({(.untypedCap true p.bv sb.val fi.val, σ1)}, False))
    (hbelow : rs = false → p.val + fi.val ≤ rb.toNat)
    {y : Except Unit Unit × Fl4Spec.State Unit}
    (hy : y ∈ ((Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype sl rs pb rb t us slots dev)).run σ1).1)
    (hK : y.2.kheap = σ'.kheap)
    (hU' : UtInv m' G') (hI' : MdbInv m' G')
    (hE : RetExp th th' m m' G G' A k w dslot cj (cslotAddr sl))
    (hok : y.1 = .ok () → A = rb.toNat ∧ k = 2 ^ bitsApi t us ∧ w = slots.length ∧
      ∀ j, j < w → isUt (cj j) = true → t = .untyped)
    (hob : ∀ cd, Fl4Spec.objBits (Fl4Spec.defaultObject t dev us cd) ≤ bitsApi t us) :
    DevFree Ap m' G' σ' :=
  SpecFreeP.retype hSF hU hst hcs ⟨rfl, hAp⟩ hg hbelow hy hK hU' hI' hE hok hob

/-- **`SpecFree` (RAM caps) across retype from a device source with an apart
range**: the RAM caps' facts after a device retype, from `SpecFree` and the
source's `DevFree` fact (`SpecFreeP.retype` at `fun p sb d => RamP p sb d ∨
DevP Ap p sb d`). -/
theorem SpecFree.retype_dev {Ap : U64 → U64 → Prop} {th th' : TypedHeap} {m m' : U64 → U64}
    {G G' : MdbGhost}
    {σ σ1 σ' : Fl4Spec.State Unit} {bitsApi : Fl4Spec.ApiObjectType → Nat → Nat} {sl : Fl4Spec.CslotPtr}
    {rs : Bool} {pb rb : Fl4Spec.ObjRef} {t : Fl4Spec.ApiObjectType} {us : Nat} {slots : List Fl4Spec.CslotPtr}
    {dev : Bool} {A k w : Nat} {dslot : Nat → U64} {cj : Nat → capability.Cap} {p sb fi : U64}
    (hSF : Sched.SpecFree m G σ) (hDF : DevFree Ap m G σ) (hU : UtInv m G) (hst : KSz σ σ1)
    (hcs : capV m (cslotAddr sl) = .Untyped p sb fi true) (hAp : Ap p sb)
    (hg : Fl4Spec.getCap (Z := Unit) sl σ1 = ({(.untypedCap true p.bv sb.val fi.val, σ1)}, False))
    (hbelow : rs = false → p.val + fi.val ≤ rb.toNat)
    {y : Except Unit Unit × Fl4Spec.State Unit}
    (hy : y ∈ ((Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype sl rs pb rb t us slots dev)).run σ1).1)
    (hK : y.2.kheap = σ'.kheap)
    (hU' : UtInv m' G') (hI' : MdbInv m' G')
    (hE : RetExp th th' m m' G G' A k w dslot cj (cslotAddr sl))
    (hok : y.1 = .ok () → A = rb.toNat ∧ k = 2 ^ bitsApi t us ∧ w = slots.length ∧
      ∀ j, j < w → isUt (cj j) = true → t = .untyped)
    (hob : ∀ cd, Fl4Spec.objBits (Fl4Spec.defaultObject t dev us cd) ≤ bitsApi t us) :
    Sched.SpecFree m' G' σ' := by
  have hB : SpecFreeP (fun p sb d => RamP p sb d ∨ DevP Ap p sb d) m G σ := by
    intro x hx p sb fi d hc hP o ko ho
    rcases hP with hP | hP
    · exact (specFreeP_ram_iff.2 hSF) x hx p sb fi d hc hP o ko ho
    · exact hDF x hx p sb fi d hc hP o ko ho
  have hA := SpecFreeP.retype hB hU hst hcs (Or.inr ⟨rfl, hAp⟩) hg hbelow hy hK hU' hI' hE hok hob
  exact specFreeP_ram_iff.1 fun x hx p sb fi d hc hP o ko ho => hA x hx p sb fi d hc (Or.inl hP) o ko ho

end

end Fl4Proofs.P3
