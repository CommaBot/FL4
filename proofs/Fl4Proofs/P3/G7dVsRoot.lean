/-
P3 (DESIGN.md §9), scheduler, g7d (KENTRY-PLAN g7c-2 1.): **`VsRootOK` from
the joint state** (no new premise).

* `vsRootOK_of`: from `StateRel` (a TCB's vtable is the abstraction of FL4's
  slot-1 cap, `tcbCnodeMap_one`), `VsRel` (every ASID-table entry is FL4's
  table word, nonzero ones in `P`, every member of `P` a spec ASID pool) and
  the nonzero ASID of every mapped PML4 cap in a TCB's slot 1.
* `JAtZ.vsRootOK` / `JAtZR.vsRootOK`: the latter from `vsc` (`VsSlotsW`), as
  `vtAsid_ofR` (XTopJointKEntry31).
-/
import Fl4Proofs.P3.G7dVsDef
import Fl4Proofs.P3.XTopJointJAtZR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Sched

noncomputable section

theorem vsRootOK_of {th : TypedHeap} {P T : Set U64} {mem : U64 → U64} {ksb : U64} {σ : Fl4Spec.State Unit}
    (hSt : StateRel th mem σ) (hR : VsRel P mem ksb σ)
    (hT : ∀ t ∈ T, th t = some .tcb ∧ ∀ p asid, capAt mem (slotOf t 1) = ok (.Pml4 p true asid) → asid ≠ 0#u64) :
    VsRootOK T σ := by
  refine ⟨fun t ht x hx p a hv => ?_, fun i p hi => ?_⟩
  · obtain ⟨hth, has⟩ := hT t ht
    obtain ⟨x', hkx, hsl⟩ := hSt.tcb t hth
    rw [hx] at hkx; cases hkx
    obtain ⟨c, ac, hc, hac, hca⟩ := hsl 1 (by decide)
    rw [tcbCnodeMap_one] at hac
    have hv' : x.tcbVtable = absCap c := by injection hac with h; rw [h, hca.2]
    have hc' : capAt mem (slotOf t 1) = ok c := hc
    rw [hv'] at hv
    cases c with
    | Pml4 q b a' =>
      cases b with
      | false => simp [absCap] at hv
      | true =>
        have e : absCap (.Pml4 q true a') = .archObjectCap (.pml4Cap q.bv (some a'.bv)) := rfl
        rw [e] at hv
        cases hv
        intro h0
        exact has q a' hc' (P1.eq_of_bv (by rw [h0]; rfl))
    | _ => simp [absCap] at hv
  · have hi11 : i.toNat < 2048 := lt_of_lt_of_eq i.isLt (by norm_num [Fl4Spec.asidHighLen])
    let hiU : U64 := ⟨i.setWidth 64⟩
    have hlt : hiU.val < 2048 := by
      show (i.setWidth 64).toNat < 2048
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
      exact hi11
    have hix : Fl4Spec.ucast 11 hiU.bv = i := by
      apply BitVec.eq_of_toNat_eq
      show ((i.setWidth 64).setWidth 11).toNat = i.toNat
      rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have ht := hR.table hiU hlt
    rw [hix, hi] at ht
    obtain ⟨hne, hbv⟩ := Notif.optRef_some ht.symm
    obtain ⟨f, hf, -⟩ := hR.pool _ (hR.tmem hiU hlt hne)
    exact ⟨f, by rw [← hbv]; exact hf⟩

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
  {AR : A → Fl4Spec.Cr3 → Prop}

/-- **`VsRootOK` at a `JAtZ` state** (module docstring). -/
theorem JAtZ.vsRootOK {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    VsRootOK Z.T σ := by
  refine vsRootOK_of J.xtop.rel.2.1.1 J.xtop.fin.2.1 fun t ht => ?_
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hth : Z.th t = some .tcb := (hJ.tcb t).2 (J.zH.1 t ht)
  refine ⟨hth, fun p asid hc => ?_⟩
  have hx : IsSlot Z.th (slotOf t 1) := ⟨t, 1, Or.inr ⟨hth, by decide⟩, rfl⟩
  have h := J.vsc _ hx
  rw [capV_of_capAt hc] at h
  have h' : p ∈ _ ∧ p ≠ 0#u64 ∧ (true = true → asid ≠ 0#u64 ∧ asid.val < 2 ^ 20) := h
  exact (h'.2.2 rfl).1

/-- **`VsRootOK` at a `JAtZR` state** (module docstring). -/
theorem JAtZR.vsRootOK {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    VsRootOK Z.T σ := by
  refine vsRootOK_of J.xtop.rel.2.1.1 J.xtop.fin.2.1 fun t ht => ?_
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hth : Z.th t = some .tcb := (hJ.tcb t).2 (J.zH.1 t ht)
  refine ⟨hth, fun p asid hc => ?_⟩
  have hx : IsSlot Z.th (slotOf t 1) := ⟨t, 1, Or.inr ⟨hth, by decide⟩, rfl⟩
  have h := J.vsc _ hx
  rw [capV_of_capAt hc] at h
  have h' : p ∈ _ ∧ p ≠ 0#u64 ∧ (true = true → asid ≠ 0#u64 ∧ asid.val < 2 ^ 20) := h
  exact (h'.2.2 rfl).1

end

end

end Fl4Proofs.P3
