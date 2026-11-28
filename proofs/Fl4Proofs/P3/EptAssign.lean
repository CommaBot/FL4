/-
P3 (line mmuAD, gen 42b4): **`EptCore` across the ASID-pool assign of an EPT root** — the guest-table half of the
nested `X86ASIDPoolAssign` (vspace.rs l. 1227, 1246-1250) at the footprint P3/EptAssignRel's `assign_rel_ept`
returns.

* `archKept_of`: with `AssignFE`'s `ArchKeepBut` and `KFoot` (`Vs`), every spec arch object other than the written
  pool is the old one.
* **`EptCore.assignE`**: from `EptCore X XL th s σ`, the assigned slot `x` holding the unmapped level-0 `Ept r` (r
  even, as every table of `X`), FL4's writes `W` missing the tables of `X`, `SlotFoot` at `x`, `AssignFE` and
  `KFoot` (all from `assign_rel_ept`), and `JExtEpt X` after: `EptCore X XL th s' σ'` — P3/EptStep2's
  `EptCore.frameT` with its cap, table, kind, tag and size hypotheses discharged from the footprint (the new tagged
  entry is `r ||| 1`, whose root `(r ||| 1) &&& ~~~1` is `r`).

Gen 42b10: `assignE` proves `EptCore.named` (the new tagged entry names the zero root `r`, which no tagged entry
named before, so `PoolInj` holds after; the only rewritten cap is level 0, outside `EptNamed`), statement unchanged.

No named premise; the spec is not touched. No `sorry`; only the three standard axioms.
-/
import Fl4Proofs.P3.EptAssignRel
import Fl4Proofs.P3.EptStep2
import Fl4Proofs.P3.VsNamedPost
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-- Every spec arch object but the written pool is kept (`AssignFE` + `KFoot`). -/
theorem archKept_of {σ σ' : Fl4Spec.State Unit} {pool : U64} (hA : Vs.ArchKeepBut pool σ σ') (hK : Vs.KFoot σ σ')
    {o : Fl4Spec.ObjRef} (ho : o ≠ pool.bv) {ao : Fl4Spec.ArchKernelObj}
    (h' : σ'.kheap o = some (.archObj ao)) : σ.kheap o = some (.archObj ao) := by
  by_cases e : σ'.kheap o = σ.kheap o
  · rw [← e]; exact h'
  rcases hK.2.2.1 o e with ⟨a0, a1, h0, -⟩ | ⟨r, cs, cs', -, -, h1⟩ | ⟨t, t', -, h1⟩
  · exact absurd (hA ⟨o⟩ ⟨a0, h0⟩ (fun h => ho (by rw [← h]))) e
  · rw [h1] at h'; cases h'
  · rw [h1] at h'; cases h'

/-- The root of a tagged entry `r ||| 1`, `r` even. -/
theorem asidEntryRoot_or1 (r : U64) (hr : r.val % 2 = 0) :
    Fl4Spec.asidEntryRoot (r.bv ||| 1) = r.bv := by
  have h := congrArg UScalar.bv (Sched.or1_and_not1 r hr)
  simp only [UScalar.bv_and, UScalar.bv_or, UScalar.bv_not] at h
  exact h

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {X : Set U64} {XL : U64 → Nat} {th : TypedHeap} {s : S} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 4000000 in
/-- **`EptCore` across the EPT pool assign** (module docstring). -/
theorem EptCore.assignE (C : EptCore (L := L) X XL th s σ) {s' : S} {σ' : Fl4Spec.State Unit}
    {x r a0 v0 : U64} (hx : IsSlot th x) (hcx : capV (L.mem s) x = .Ept r 0#u64 false a0 v0)
    (hev : r.val % 2 = 0)
    {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hW : ∀ b, W b → ∀ t ∈ X, b.val < t.val ∨ t.val + 4096 ≤ b.val)
    (hF : Vs.SlotFoot th (L.mem s) (L.mem s') x) (hA : Vs.AssignFE (L.mem s') x r σ σ') (hK : Vs.KFoot σ σ')
    (hX' : JExtEpt (L := L) X th s') :
    EptCore (L := L) X XL th s' σ' := by
  obtain ⟨asid, pool, hi, lo, f, hcv, -, htab, -, -, -, -, hkp, hkp', hAK, htab'⟩ := hA
  refine C.frameT hx hcx hw hW ?_ hX' ?_ ?_ ?_ ?_ ?_ ?_
  · intro y hy p l a v mm hc
    by_cases e : y = x
    · subst e
      rw [hcv] at hc
      injection hc with h1 h2 h3
      exact Or.inl ⟨rfl, h1.symm, h2.symm, h3.symm⟩
    · exact Or.inr ⟨e, hy, by rw [← Vs.capV_of_foot hF y hy e]; exact hc⟩
  · intro t ht
    obtain ⟨es, hk, -⟩ := C.rel.obj t ht
    have htp : t ≠ pool := fun h => by subst h; rw [hk] at hkp; cases hkp
    exact hAK t ⟨_, hk⟩ htp
  · intro o l es hk
    have hop : o ≠ pool.bv := fun h => by subst h; rw [hk] at hkp'; cases hkp'
    exact ⟨l, es, archKept_of hAK hK hop hk⟩
  · rintro e ⟨hi', p, g, lo', ht', hkg, hge⟩ h1
    rw [htab'] at ht'
    by_cases hpp : p = pool.bv
    · subst hpp
      rw [hkp'] at hkg
      injection hkg with hkg; injection hkg with hkg; injection hkg with hkg; subst hkg
      by_cases hl : lo' = Fl4Spec.ucast 9 lo.bv
      · subst hl
        rw [Function.update_self] at hge
        injection hge with hge; subst hge
        exact Or.inr (asidEntryRoot_or1 r hev)
      · rw [Function.update_of_ne hl] at hge
        exact Or.inl ⟨hi', pool.bv, f, lo', ht', hkp, hge⟩
    · exact Or.inl ⟨hi', p, g, lo', ht', archKept_of hAK hK hpp hkg, hge⟩
  · intro o ko' hk'
    by_cases e : σ'.kheap o = σ.kheap o
    · exact ⟨ko', by rw [← e]; exact hk', rfl⟩
    rcases hK.2.2.1 o e with ⟨a1, a2, h0, h1⟩ | ⟨rr, cs, cs', h0, -, h1⟩ | ⟨t, t', h0, h1⟩
    · by_cases hop : o = pool.bv
      · subst hop
        rw [hkp'] at hk'; cases hk'
        exact ⟨_, hkp, rfl⟩
      · exact absurd (hAK ⟨o⟩ ⟨a1, h0⟩ (fun h => hop (by rw [← h]))) e
    · rw [h1] at hk'; cases hk'; exact ⟨_, h0, rfl⟩
    · rw [h1] at hk'; cases hk'; exact ⟨_, h0, rfl⟩
  · -- `SLOT_EPT`: `x` held an unmapped cap, so it is no TCB's `SLOT_EPT` (`EptCore.eslot`); the others are kept
    intro t ht
    by_cases e : cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 5) = x
    · exfalso
      rcases C.eslot t ht with h | ⟨p, a, v, h⟩ <;> rw [e, hcx] at h <;> cases h
    · exact Or.inr (Or.inr ⟨ht, Vs.capV_of_foot hF _ (isSlot_eptSlot ht) e⟩)
  · -- `EptNamed` (gen 42b10): the new tagged entry names the zero root `r`, unnamed before (`ue`); the only cap
    -- rewritten is `x`'s level-0 one
    have hr : r ∈ X := by have h := C.exte.cap x hx; rw [hcx] at h; exact h
    have hrz : σ'.kheap r.bv = some (.archObj (.ept (XL r) fun _ => 0)) := by
      obtain ⟨es, hk, -⟩ := C.rel.obj r hr
      have hrp : r ≠ pool := fun h => by subst h; rw [hk] at hkp; cases hkp
      rw [hAK r ⟨_, hk⟩ hrp]; exact (C.ue x hx r 0#u64 a0 v0 hcx).2.1
    have cls : ∀ hi' lo' e, PoolAt σ' hi' lo' e → PoolAt σ hi' lo' e ∨
        (σ.archState.x64AsidTable hi' = some pool.bv ∧ lo' = Fl4Spec.ucast 9 lo.bv ∧ e = r.bv ||| 1) := by
      rintro hi' lo' e ⟨p, g, ht', hkg, hge⟩
      rw [htab'] at ht'
      by_cases hpp : p = pool.bv
      · subst hpp
        rw [hkp'] at hkg
        injection hkg with hkg; injection hkg with hkg; injection hkg with hkg; subst hkg
        by_cases hl : lo' = Fl4Spec.ucast 9 lo.bv
        · subst hl
          rw [Function.update_self] at hge
          injection hge with hge
          exact Or.inr ⟨ht', rfl, hge.symm⟩
        · rw [Function.update_of_ne hl] at hge
          exact Or.inl ⟨pool.bv, f, ht', hkp, hge⟩
      · exact Or.inl ⟨p, g, ht', archKept_of hAK hK hpp hkg, hge⟩
    have hobj : ∀ o l es, σ'.kheap o = some (.archObj (.ept l es)) → σ.kheap o = some (.archObj (.ept l es)) := by
      intro o l es hk
      have hop : o ≠ pool.bv := fun h => by subst h; rw [hk] at hkp'; cases hkp'
      exact archKept_of hAK hK hop hk
    refine C.named.keep (GPath.mono' (fun hi' lo' e hp h1 => (cls hi' lo' e hp).imp id fun hn =>
        ⟨XL r, by rw [hn.2.2, asidEntryRoot_or1 r hev]; exact hrz⟩) (fun o l es hk => Or.inl (hobj o l es hk)))
      ⟨fun h1 h2 p g1 g2 => C.named.inj.tab h1 h2 p (by rw [← htab']; exact g1) (by rw [← htab']; exact g2), ?_⟩
      (fun y p lv a v hy hc _ => ?_) (fun y p lv mm a v hy hc => ?_)
    · intro h1 l1 h2 l2 e e' hp hp' t1 t2 hre
      have hne : ∀ e'', GuestEntry σ e'' → e'' &&& 1 = 1 → Fl4Spec.asidEntryRoot e'' ≠ r.bv :=
        (C.ue x hx r 0#u64 a0 v0 hcx).2.2.2
      rcases cls h1 l1 e hp with g | ⟨g1, g2, ge⟩ <;> rcases cls h2 l2 e' hp' with g' | ⟨g1', g2', ge'⟩
      · exact C.named.inj.root h1 l1 h2 l2 e e' g g' t1 t2 hre
      · exact absurd (by rw [hre, ge', asidEntryRoot_or1 r hev]) (hne e g.guest t1)
      · exact absurd (by rw [← hre, ge, asidEntryRoot_or1 r hev]) (hne e' g'.guest t2)
      · exact ⟨C.named.inj.tab h1 h2 pool.bv g1 g1', g2.trans g2'.symm⟩
    · by_cases e : y = x
      · subst e; rw [hcx] at hc; exact absurd (capability.Cap.Ept.inj hc).2.2.1 Bool.false_ne_true
      · exact ⟨y, hy, by rw [Vs.capV_of_foot hF y hy e]; exact hc⟩
    · by_cases e : y = x
      · subst e; rw [hcv] at hc
        obtain ⟨rfl, -, -, -, -⟩ := capability.Cap.Ept.inj hc
        exact Or.inr ⟨y, 0#u64, a0, v0, hy, hcx⟩
      · exact Or.inl ⟨y, hy, by rw [← Vs.capV_of_foot hF y hy e]; exact hc⟩

end

end

end Fl4Proofs.P3
