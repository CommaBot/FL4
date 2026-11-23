/-
P3 (issue #16, FL4 #71), VSpace FrameBatch (KENTRY-PLAN fb3l), spec side:
**`cap_delete` of a frame-cap slot keeps `FbKeep`**.

* `fbUF`: XTopJointFinVsSpec's `archF` with the IRQ fields, the domain list,
  the ASID table and the ASID pools; `fbu_unmapPage`: `unmap_page` keeps it
  (its stores hit page tables, directories and PDPTs only).
* `FbKeep.of_fbUF`, `FbKeep.of_cnK` (an `empty_slot`'s CNode-only step).
* `fbKeep_capDelete_frame`: SpecFbX's `capDelete_subX` (one round of
  `rec_del` on a frame: `arch_finalise_cap` then `empty_slot … Null`).
-/
import Fl4Proofs.P3.XTopJointFbDefs
import Fl4Proofs.P3.SpecFbX
import Fl4Proofs.P3.XTopJointFinVsSpec
import Fl4Proofs.P3.DelW
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open Classical Fl4Proofs.P3.Ipc

noncomputable section

section Spec
open Fl4Spec

/-- The ASID pools' contents. -/
def poolV (σ : State Unit) (p : ObjRef) : Option (AsidLowIndex → Option ObjRef) :=
  match σ.kheap p with
  | some (.archObj (.asidPool f)) => some f
  | _ => none

/-- **The fields `unmap_page` keeps** (module docstring). -/
def fbUF (σ : State Unit) :=
  (archF σ, σ.interruptIrqNode, σ.interruptStates, σ.domainList, σ.domainIndex, σ.domainStartIndex,
    σ.archState.x64AsidTable, poolV σ, σ.machineState.underlyingMemory)

theorem fbu_setObject (p : ObjRef) (a : ArchKernelObj) (hn : aaType a ≠ .aASIDPool) :
    Vs.FK fbUF (setObject (Z := Unit) p (.archObj a)) := by
  intro σ x hx
  obtain ⟨k, hk, hty, e⟩ := MaxK.mk_setObject_mem hx
  rw [e]
  cases k with
  | archObj a0 =>
    have ht : aaType a0 = aaType a := by simpa [aType] using hty
    unfold fbUF
    rw [archF_upd hk ht]
    have hp : poolV { σ with kheap := Function.update σ.kheap p (some (.archObj a)) } = poolV σ := by
      funext q
      unfold poolV
      by_cases eq : q = p
      · subst eq
        rw [Function.update_self, hk]
        cases a <;> cases a0 <;> simp_all [aaType]
      · simp only [Function.update_of_ne eq]
    rw [hp]
  | cnode r cs => simp only [aType] at hty; split at hty <;> cases hty
  | schedContext y n => simp only [aType] at hty; split at hty <;> cases hty
  | _ => simp [aType] at hty

theorem fbu_setObject_pt (p : ObjRef) (pt : BitVec 9 → PTE) :
    Vs.FK fbUF (setObject (Z := Unit) p (.archObj (.pageTable pt))) := fbu_setObject p _ (by decide)
theorem fbu_setObject_pd (p : ObjRef) (pd : BitVec 9 → PDE) :
    Vs.FK fbUF (setObject (Z := Unit) p (.archObj (.pageDirectory pd))) := fbu_setObject p _ (by decide)
theorem fbu_setObject_pdpt (p : ObjRef) (pd : BitVec 9 → PDPTE) :
    Vs.FK fbUF (setObject (Z := Unit) p (.archObj (.pdPointerTable pd))) := fbu_setObject p _ (by decide)

/-- A machine operation keeping the underlying memory. -/
def UKM {α : Type} (m : NonDet MachineState α) : Prop :=
  ∀ ms x, x ∈ (m ms).1 → x.2.underlyingMemory = ms.underlyingMemory

theorem ukm_machineOpLift (f : MachineRestMonad Unit) : UKM (machineOpLift f) := by
  unfold machineOpLift machineRestLift
  intro ms x hx
  obtain ⟨⟨mr, ms1⟩, h1, ⟨⟨r, mr'⟩, ms2⟩, h2, ⟨u, ms3⟩, h3, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 h1] at h2
  obtain ⟨-, e2⟩ := h2
  simp only [Prod.mk.injEq] at e2
  obtain ⟨-, rfl⟩ := e2
  rw [Set.mem_singleton_iff.1 h3] at hx
  rw [Set.mem_singleton_iff.1 hx]

theorem fbu_doMachineOp {α : Type} {mop : NonDet MachineState α} (hm : UKM mop) :
    Vs.FK fbUF (doMachineOp (Z := Unit) mop) := by
  intro σ x hx
  unfold doMachineOp at hx
  obtain ⟨⟨ms0, s1⟩, h1, ⟨⟨r, ms'⟩, s2⟩, h2, ⟨u, s3⟩, h3, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 h1] at h2
  obtain ⟨hm2, e2⟩ := h2
  simp only [Prod.mk.injEq] at e2 h3
  obtain ⟨-, rfl⟩ := e2
  rw [Set.mem_singleton_iff.1 h3] at hx
  rw [Set.mem_singleton_iff.1 hx]
  have e := hm _ _ hm2
  simp only at e
  simp only [fbUF, archF, poolV, e]

theorem fbu_invTSA (v a : Word) :
    Vs.FK fbUF (doMachineOp (Z := Unit) (invalidateTranslationSingleASID v a)) :=
  fbu_doMachineOp (ukm_machineOpLift _)

set_option maxHeartbeats 8000000 in
/-- **`unmap_page` keeps `fbUF`.** -/
theorem fbu_unmapPage (sz : VMPageSize) (a : Asid) (v : VSpaceRef) (p : ObjRef) :
    Vs.FK fbUF (unmapPage (Z := Unit) sz a v p) := by
  unfold unmapPage
  repeat' (first | exact fbu_setObject_pt _ _ | exact fbu_setObject_pd _ _ | exact fbu_setObject_pdpt _ _ |
    exact fk_getCapG _ _ | exact fbu_invTSA _ _ | dk_step0 | fk_unf | sched_unf | vs_unf)

theorem eraseA_eq_none {o : Option KernelObject} (h : eraseA o = none) : o = none ∨ ∃ a, o = some (.archObj a) := by
  rcases o with _ | o
  · exact Or.inl rfl
  · cases o <;> first | exact Or.inr ⟨_, rfl⟩ | (simp [eraseA] at h)

theorem eraseA_some {o : Option KernelObject} {k : KernelObject} (h : eraseA o = some k) : o = some k := by
  rcases o with _ | o
  · simp [eraseA] at h
  · cases o <;> simp_all [eraseA]

/-- **`FbKeep` from `fbUF`.** -/
theorem FbKeep.of_fbUF {σ σ' : State Unit} (h : fbUF σ' = fbUF σ) : FbKeep σ σ' := by
  simp only [fbUF, archF, Prod.mk.injEq] at h
  obtain ⟨⟨he, ht, -, -, hct, hid, hcons, htime, hcsc, hrep, hact, hdt, hrq, hrel, hgp, hcd, hisc⟩,
    hin, his, hdl, hdi, hdsi, hat, hpool, -⟩ := h
  refine ⟨fun p => ?_, hct, hid, hcons, htime, hcsc, hisc, hrep, hact, hdl, hdi, hdsi, hcd, hdt, hrq, hrel, hin, his,
    hat, hgp⟩
  have e1 := congrFun he p
  have e2 := congrFun ht p
  have e3 := congrFun hpool p
  simp only at e1 e2
  cases hk : σ.kheap p with
  | none =>
    rw [hk] at e1 e2
    left
    rcases eraseA_eq_none e1 with h0 | ⟨a, ha⟩
    · exact h0
    · rw [ha] at e2; cases e2
  | some o =>
    rw [hk] at e1 e2 e3
    cases o with
    | archObj a =>
      rcases eraseA_eq_none e1 with h0 | ⟨a', ha'⟩
      · rw [h0] at e2; cases e2
      · rw [ha'] at e2
        have e2' : aaType a' = aaType a := by simpa [aType] using e2
        by_cases hpa : aaType a = .aASIDPool
        · cases a <;> simp [aaType] at hpa
          cases a' <;> simp [aaType] at e2'
          unfold poolV at e3
          rw [hk, ha'] at e3
          simp only [Option.some.injEq] at e3
          subst e3
          left; exact ha'
        · right; left
          exact ⟨a, a', rfl, ha', e2', hpa⟩
    | _ =>
      left
      exact eraseA_some e1

/-- **`FbKeep` across a CNode-only step** (`CnK`: the CNodes' and TCBs' caps, the CDT and the
original bits). -/
theorem FbKeep.of_cnK {σ σ' : State Unit} (h : CnK σ σ') : FbKeep σ σ' := by
  obtain ⟨ha, hk⟩ := h
  have f : ∀ {β : Type} (g : AbstractState → β), g (abs0 σ') = g (abs0 σ) := fun g => congrArg g ha
  refine ⟨fun p => ?_, f (·.curThread), f (·.idleThread), f (·.consumedTime), f (·.curTime), f (·.curSc),
    f (·.idleSc), f (·.reprogramTimer), f (·.schedulerAction), f (·.domainList), f (·.domainIndex),
    f (·.domainStartIndex), f (·.curDomain), f (·.domainTime), f (·.readyQueues), f (·.releaseQueue),
    f (·.interruptIrqNode), f (·.interruptStates), f (·.archState.x64AsidTable), f (·.archState.x64GlobalPml4)⟩
  rcases hk p with e | ⟨r, cs, cs', h1, h2⟩ | ⟨x, y, h1, h2, hxy⟩
  · exact Or.inl e
  · exact Or.inr (Or.inr (Or.inl ⟨r, cs, cs', h1, h2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨x, y, h1, h2, hxy⟩))

/-- **`cap_delete` of a frame-cap slot keeps `FbKeep`** and the underlying memory (module docstring). -/
theorem fbKeep_capDelete_frame {sl : CslotPtr} {σ τ : State Unit} {dev : Bool} {p : ObjRef} {R : CapRights}
    {mt : VMMapType} {sz : VMPageSize} {m : Option (Asid × VSpaceRef)}
    (hc : SInvU.capAt σ sl = some (.archObjectCap (.pageCap dev p R mt sz m)))
    (h : (.ok (), τ) ∈ ((capDelete (Z := Unit) sl).run σ).1) :
    FbKeep σ τ ∧ τ.machineState.underlyingMemory = σ.machineState.underlyingMemory := by
  have hx := SInv.capDelete_subX hc _ h
  unfold SInv.fbDelX NonDetE.liftE at hx
  rw [ExceptT.run_lift] at hx
  obtain ⟨⟨u, τ'⟩, hu, he⟩ := hx
  have e : τ' = τ := (congrArg Prod.snd (Set.mem_singleton_iff.1 he)).symm
  subst e
  obtain ⟨⟨c, σ1⟩, h1, h2⟩ := hu
  have e1 := fk_getCapG (fun t => t) sl σ _ h1
  simp only at e1
  subst e1
  cases c with
  | archObjectCap ac =>
    cases ac with
    | pageCap dev' p' R' mt' sz' m' =>
      obtain ⟨⟨fin, σ2⟩, h3, h4⟩ := h2
      have e2 : σ2 = σ1 := (congrArg Prod.snd (Set.mem_singleton_iff.1 h3))
      subst e2
      obtain ⟨⟨cc, σ3⟩, h5, h6⟩ := h4
      have hU : fbUF σ3 = fbUF σ2 := by
        rcases m' with _ | ⟨a, v⟩ <;> cases fin <;> simp only [archFinaliseCap] at h5
        all_goals first
          | (rw [(congrArg Prod.snd (Set.mem_singleton_iff.1 h5))])
          | (obtain ⟨y, hy, h5⟩ := h5
             rw [(congrArg Prod.snd (Set.mem_singleton_iff.1 h5))]
             exact fbu_unmapPage _ _ _ _ σ2 y hy)
      have hC := emptySlot_null_nkn sl σ3 _ h6
      refine ⟨(FbKeep.of_fbUF hU).trans (FbKeep.of_cnK hC), ?_⟩
      have u1 : σ3.machineState.underlyingMemory = σ2.machineState.underlyingMemory :=
        congrArg (fun t => t.2.2.2.2.2.2.2.2) hU
      exact (congrArg (fun t : AbstractState => t.machineState.underlyingMemory) hC.1).trans u1
    | _ => simp [NonDet.fail] at h2
  | _ => simp [NonDet.fail] at h2

end Spec

end

end Fl4Proofs.P3
