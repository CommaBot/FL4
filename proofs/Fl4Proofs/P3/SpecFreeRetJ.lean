/-
P3: **`SpecFree` across retype** (l4v `valid_untyped` kept by
`invoke_untyped`).

The spec's objects after (`invokeUntyped_kheap`) are old objects or new
ones; FL4's untyped caps after (`RetExp`) are the old ones, the source with
its free index past the window (`RetExp.usrc`), or new caps over the
window's slices.

* An old object met the source's range only below its free index; it is
  below the window unless the invocation resets a used cap, which deletes
  it (`reset_avoid`). So it stays valid for every untyped cap: unchanged
  ones by `SpecFree` before, the source since its new free index is past
  the window, new caps since they lie in the window.
* A new object lies in the range of its non-untyped cap, so in the range
  of an untyped cap after it lies below the free index (`UtInv.inc`) or
  misses it (`UtInv.drange`, `MdbInv.anc_ut`).
-/
import Fl4Proofs.P3.SpecFreeRet
import Fl4Proofs.P3.UntypedExp
import Fl4Proofs.P3.UntypedUtOps
import Fl4Proofs.P3.UntypedRetypeReset
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

theorem regionPtrs_mem {rb o : Fl4Spec.ObjRef} {n K : Nat} (h : o ∈ regionPtrs rb n K) :
    ∃ j, j < n ∧ o = Fl4Spec.ptrAdd rb (j * K) := by
  unfold regionPtrs at h
  obtain ⟨j, hj, e⟩ := List.mem_map.1 h
  exact ⟨j, List.mem_range.1 hj, e.symm⟩

theorem ptrAdd_toNat {rb : Fl4Spec.ObjRef} {n : Nat} (h : rb.toNat + n < 2 ^ 64) :
    (Fl4Spec.ptrAdd rb n).toNat = rb.toNat + n := by
  unfold Fl4Spec.ptrAdd
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have : n < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt h]

/-- **An old object after `invoke_untyped`, against the source cap**: outside
its range, or (without a reset) below the window. A used source cap that is
reset loses its objects (`hR`), an unused one has none. -/
theorem old_window {m : U64 → U64} {G : MdbGhost} {σ : Fl4Spec.State Unit} {x : U64} {p sb fi : U64} {d : Bool}
    {A : Nat} {rs : Bool} {o : Fl4Spec.ObjRef} {ko : Fl4Spec.KernelObject}
    (hSF : Sched.SpecFree m G σ) (hU : UtInv m G) (hxG : x ∈ G.chains.flatten)
    (hcs : capV m x = .Untyped p sb fi d) (hd : d = false) (h0 : σ.kheap o = some ko)
    (hR : o ∉ (if rs = true ∧ fi.val ≠ 0 then regionSet p.bv sb.val else ∅))
    (hbelow : rs = false → p.val + fi.val ≤ A) :
    (o.toNat + 2 ^ Fl4Spec.objBits ko ≤ p.val ∨ p.val + 2 ^ sb.val ≤ o.toNat) ∨
      (rs = false ∧ p.val ≤ o.toNat ∧ o.toNat + 2 ^ Fl4Spec.objBits ko ≤ A) := by
  have hsb : sb.val < 64 := capV_ut_sb hcs
  have hfitS : p.val + 2 ^ sb.val ≤ 2 ^ 64 := by
    have hreg := hU.reg _ hxG (by rw [hcs]; exact physF_ut _ _ _ _)
    rw [hcs] at hreg
    exact (ut_range hsb hreg).2.2
  have hfiS : fi.val ≤ 2 ^ sb.val := hU.fib _ hxG p sb fi d hcs
  have hb1 := Nat.one_le_two_pow (n := Fl4Spec.objBits ko)
  rcases hSF _ hxG p sb fi (by rw [hcs, hd]) o ko h0 with e | ⟨l1, l2⟩
  · exact Or.inl e
  · by_cases hc : rs = true ∧ fi.val ≠ 0
    · rw [if_pos hc] at hR
      have := (regionSet_iff p ⟨o⟩ sb.val hsb hfitS).not.1 hR
      exact absurd ⟨l1, by show o.toNat < _; omega⟩ this
    · rcases Bool.eq_false_or_eq_true rs with hr | hr
      · have hz : fi.val = 0 := by by_contra hz; exact hc ⟨hr, hz⟩
        omega
      · have := hbelow hr; right; exact ⟨hr, l1, by omega⟩

theorem emptyCnode_wf (n : Nat) : Fl4Spec.wellFormedCnodeN n (Fl4Spec.emptyCnode n) := by
  unfold Fl4Spec.wellFormedCnodeN Fl4Spec.dom Fl4Spec.emptyCnode
  ext x; simp only [Set.mem_setOf_eq, ne_eq, ite_eq_right_iff, reduceCtorEq, imp_false, not_not]

/-- An object of an SC's type is an SC of the same size, or a malformed CNode. -/
theorem sc_of_aType {ko : Fl4Spec.KernelObject} {y : Fl4Spec.SchedContext} {n : Nat}
    (h : Fl4Spec.aType ko = Fl4Spec.aType (.schedContext y n)) :
    (∃ y0, ko = .schedContext y0 n) ∨ ∃ sz cs, ko = .cnode sz cs ∧ ¬ Fl4Spec.wellFormedCnodeN sz cs := by
  cases ko with
  | cnode sz cs =>
    by_cases hw : Fl4Spec.wellFormedCnodeN sz cs
    · simp only [Fl4Spec.aType, if_pos hw] at h; split_ifs at h
    · exact Or.inr ⟨sz, cs, rfl, hw⟩
  | schedContext y0 n0 =>
    simp only [Fl4Spec.aType] at h
    split_ifs at h with h1 h2 h2 <;> simp_all [Fl4Spec.minSchedContextBits]
  | archObj ao => simp only [Fl4Spec.aType] at h; split_ifs at h
  | _ => simp only [Fl4Spec.aType] at h; split_ifs at h <;> cases h

/-- A default object of an SC's type is a default SC (of size `us - 7`). -/
theorem sc_of_default {t : Fl4Spec.ApiObjectType} {dev : Bool} {us : Nat} {cd : Fl4Spec.Domain}
    {y : Fl4Spec.SchedContext} {n : Nat}
    (h : Fl4Spec.aType (.schedContext y n) = Fl4Spec.aType (Fl4Spec.defaultObject t dev us cd)) (ht : t ≠ .untyped) :
    t = .schedContextObject ∧ n = us - Fl4Spec.minSchedContextBits := by
  cases t with
  | untyped => exact absurd rfl ht
  | capTableObject =>
    simp only [Fl4Spec.defaultObject, Fl4Spec.aType, if_pos (emptyCnode_wf us)] at h; split_ifs at h
  | schedContextObject =>
    refine ⟨rfl, ?_⟩
    simp only [Fl4Spec.defaultObject, Fl4Spec.aType] at h
    split_ifs at h <;> simp_all [Fl4Spec.minSchedContextBits]
  | archObject a => simp only [Fl4Spec.defaultObject, Fl4Spec.aType] at h; split_ifs at h
  | _ => simp only [Fl4Spec.defaultObject, Fl4Spec.aType] at h; split_ifs at h <;> cases h

/-- **`SpecFree` across retype**: from the state before `set_thread_state`
(`KSz` to `σ1`) and one outcome of `invoke_untyped` from `σ1` whose heap is
`σ'`'s, with FL4's `RetExp` for the source slot and its window, the new
caps untyped only for an untyped retype, and `default_object` no larger
than the window's slices. `hbelow`: without a reset the window starts at
or past the source's free index (decode's `alignUp`). -/
theorem SpecFree.retype {th th' : TypedHeap} {m m' : U64 → U64} {G G' : MdbGhost}
    {σ σ1 σ' : Fl4Spec.State Unit} {bitsApi : Fl4Spec.ApiObjectType → Nat → Nat} {sl : Fl4Spec.CslotPtr}
    {rs : Bool} {pb rb : Fl4Spec.ObjRef} {t : Fl4Spec.ApiObjectType} {us : Nat} {slots : List Fl4Spec.CslotPtr}
    {dev : Bool} {A k w : Nat} {dslot : Nat → U64} {cj : Nat → capability.Cap} {p sb fi : U64} {d : Bool}
    (hSF : Sched.SpecFree m G σ) (hU : UtInv m G) (hst : KSz σ σ1)
    (hcs : capV m (cslotAddr sl) = .Untyped p sb fi d) (hd : d = false)
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
    Sched.SpecFree m' G' σ' := by
  intro x' hx' p' sb' fi' hcx' o ko' ho
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
      rcases hSF _ hxG p sb fi (by rw [hcs, hd]) o ko0 h0 with e | ⟨l1, l2⟩
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
        exact hSF x' hxG' p' sb' fi' hcx' o ko0 h0
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
    · rcases hU'.drange x' hx' p' sb' fi' false hcx' (dslot j) hdm hne (by rw [hdc]; exact hdp) hdj with h | h
      · obtain ⟨-, i1, i2⟩ := hU'.inc x' hx' p' sb' fi' false hcx' (dslot j) h
        rw [hdc, hdb] at i1; rw [hdc, hdt] at i2
        right; omega
      · have := hI'.anc_ut h (by rw [hcx']; rfl)
        rw [hdc, hnu] at this; cases this

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- `RetPostN` with `SpecFree` after. -/
def RetPostNF {A' : Type} (th : TypedHeap) (m : U64 → U64) (G : MdbGhost) (σ : Fl4Spec.State Unit)
    (arI : machine.Arch A') (ar : A') (s0 : S)
    (bitsApi : Fl4Spec.ApiObjectType → Nat → Nat) (ks : U64)
    (inv : Fl4Spec.UntypedInvocation) (res : core.result.Result Unit error.Exc × S × A') : Prop :=
  ∃ σ1, Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
    NSat (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi inv).run σ1 (fun _ => True) ∧
    ∃ e σ' G' th', ((res.1 = .Ok () ∧ e = .ok ()) ∨ (res.1 = .Err .Preempted ∧ e = .error ())) ∧
      NHas (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi inv).run σ1 (fun y => y.1 = e ∧ KSame σ' y.2) ∧
      Placed th' ∧ StateRel th' (L.mem res.2.1) σ' ∧ SlotsValid th' (L.mem res.2.1) ∧
      MdbLinks th' (L.mem res.2.1) G' ∧ CdtRel th' (L.mem res.2.1) σ' G' ∧ MdbInv (L.mem res.2.1) G' ∧
      UtInv (L.mem res.2.1) G' ∧ Sched.SpecFree (L.mem res.2.1) G' σ' ∧ MdbStep m G (L.mem res.2.1) G' ∧
      (FinInv th m σ G → FinInv th' (L.mem res.2.1) σ' G') ∧ L.ksb res.2.1 = ks ∧
      ∃ A k w dslot cj, RetExp th th' m (L.mem res.2.1) G G' A k w dslot cj (invSrc inv) ∧
        RetFrameI (L := L) arI ar th G s0 bitsApi inv A k w dslot cj th' res

theorem RetPostNF.toN {A' : Type} {th : TypedHeap} {m : U64 → U64} {G : MdbGhost} {σ : Fl4Spec.State Unit}
    {arI : machine.Arch A'} {ar : A'} {s0 : S} {bitsApi : Fl4Spec.ApiObjectType → Nat → Nat} {ks : U64}
    {inv : Fl4Spec.UntypedInvocation} {res : core.result.Result Unit error.Exc × S × A'}
    (h : RetPostNF (L := L) th m G σ arI ar s0 bitsApi ks inv res) :
    RetPostN (L := L) th m G σ arI ar s0 bitsApi ks inv res := by
  obtain ⟨σ1, h1, h2, e, σ', G', th', h3, h4, h5, h6, h7, h8, h9, h10, h11, -, h12⟩ := h
  exact ⟨σ1, h1, h2, e, σ', G', th', h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

/-- **An untyped invocation keeps `SpecFree`** (`SpecFree.retype` on the
outcome `RetPostN` names). Premises from decode: the source cap (FL4's and,
after `set_thread_state`, the spec's), the window at or past its free index
without a reset, and `default_object`'s size. -/
theorem RetPostN.specFree {A' : Type} {th : TypedHeap} {G : MdbGhost} {σ : Fl4Spec.State Unit}
    {arI : machine.Arch A'} {ar : A'} {s : S} {bitsApi : Fl4Spec.ApiObjectType → Nat → Nat} {ks : U64}
    {sl : Fl4Spec.CslotPtr} {rs : Bool} {pb rb : Fl4Spec.ObjRef} {t : Fl4Spec.ApiObjectType} {us : Nat}
    {slots : List Fl4Spec.CslotPtr} {dev : Bool} {res : core.result.Result Unit error.Exc × S × A'}
    {p sb fi : U64} {d : Bool}
    (hRP : RetPostN (L := L) th (L.mem s) G σ arI ar s bitsApi ks (.retype sl rs pb rb t us slots dev) res)
    (hSF : Sched.SpecFree (L.mem s) G σ) (hU : UtInv (L.mem s) G)
    (hcs : capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi d) (hd : d = false)
    (hg : ∀ σ1, Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
      Fl4Spec.getCap (Z := Unit) sl σ1 = ({(.untypedCap d p.bv sb.val fi.val, σ1)}, False))
    (hbelow : rs = false → p.val + fi.val ≤ rb.toNat)
    (hob : ∀ cd, Fl4Spec.objBits (Fl4Spec.defaultObject t dev us cd) ≤ bitsApi t us) :
    RetPostNF (L := L) th (L.mem s) G σ arI ar s bitsApi ks (.retype sl rs pb rb t us slots dev) res := by
  obtain ⟨σ1, hst, hNS, e, σ', G', th', he, hhas, h5, h6, h7, h8, h9, hI', hU', h11, h12, h13, A, k, w, dslot, cj,
    hE, hF⟩ := hRP
  obtain ⟨y, hy, hy1, hK⟩ := hhas
  refine ⟨σ1, hst, hNS, e, σ', G', th', he, ⟨y, hy, hy1, hK⟩, h5, h6, h7, h8, h9, hI', hU', ?_, h11, h12, h13,
    A, k, w, dslot, cj, hE, hF⟩
  refine SpecFree.retype hSF hU (ksz_of_eq (nkz_setThreadState _ _) hst) hcs hd (hg σ1 hst) hbelow hy hK.1 hU' hI' hE
    (fun hok => ?_) hob
  have hr : res.1 = .Ok () := by
    rcases he with ⟨h, -⟩ | ⟨-, h⟩
    · exact h
    · rw [← hy1, hok] at h; cases h
  obtain ⟨⟨ct, s0, -, -, hbr⟩, hcu⟩ := hF
  rcases hbr with ⟨h, -⟩ | ⟨-, ⟨eA, ek, ew, -⟩, -⟩
  · rw [hr] at h; cases h
  · exact ⟨eA, ek, ew, hcu hr⟩

end

end

end Fl4Proofs.P3
