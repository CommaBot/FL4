/-
P3 (DESIGN.md §9), TCB invocations: **SetPriority's leaf at `XTop`**
(XTopTcbSched's `SetPrioXLeaf`), from `set_priority_irel` (IpcSetPrio).

* `SetPrioOK`: what `set_priority_irel` needs beyond `IRel` at the state
  after the caller's restart (l4v `valid_sched` and `valid_objs`): the current
  thread in no release queue, `SchedValid`, `Inv`, `ObjCover`, the endpoint
  and notification queues sorted.
* `setPrioXLeaf_of`: the caller's restart (`XTopAt.restart`), `IRel` by
  `XTopAt.irelK`, `set_priority_irel`, back by `IRel.xtop`.
-/
import Fl4Proofs.P3.IpcSetPrio
import Fl4Proofs.P3.XTopTcbSched
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-- **What SetPriority's scheduler step needs beyond `IRel`** [J] (l4v
`valid_sched`: `ct_not_in_release_q`, `valid_queues`; `sym_refs`; the queues
ordered by priority): for the target `p`. -/
def SetPrioOK (st : machine.Store S) [L : P1.LawfulStore st] (Z : XSets) (p : U64) (s : S)
    (σ : Fl4Spec.State Unit) : Prop :=
  (σ.curThread = p.bv → p.bv ∉ σ.releaseQueue) ∧ SchedValid σ ∧ Inv σ ∧ ObjCover Z.N Z.T Z.E Z.R Z.C σ ∧
    QSorted st Z.T Z.E s ∧ QSorted st Z.T Z.N s

set_option maxHeartbeats 4000000 in
/-- **`SetPrioXLeaf`** (module docstring). Named, at every `Z` the entry's
`XTopAt` holds at: `KsApart`, the IPC placement, the target among the TCBs,
`ActReady` on `IRel` [J], `SetPrioOK` on `IRel`; `BufWordRel` at `XTopAt`
(as XTopTcbSched's `hBT`); the caller runnable (`CurRun`) [J]. -/
theorem setPrioXLeaf_of {AR : A → Fl4Spec.Cr3 → Prop} {s : S} {ar : A} {σ σ1 : Fl4Spec.State Unit} {p v : U64}
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False)) (hv : v.val < 256)
    (hC : CurRun σ)
    (hZ : ∀ Z : XSets, XTopAt (L := L) AR Z s ar σ → KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s) ∧
      IPlaced Z.N Z.T Z.E Z.R Z.B ∧ p ∈ Z.T ∧
      (∀ s' σ', IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ' → Notif.ActReady σ') ∧
      (∀ s' σ', IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ' → SetPrioOK st Z p s' σ'))
    (hBW : ∀ (Z : XSets) s' a' σ', XTopAt (L := L) AR Z s' a' σ' → BufWordRel Z.T (L.mem s') σ') :
    SetPrioXLeaf (L := L) AR s ar σ σ1 p v := by
  rintro ⟨Z, hX⟩
  obtain ⟨hKA, hP0, hpT, hAct, hOK⟩ := hZ Z hX
  have hSch := hX.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hSch.lists
  set ct := L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) with hctd
  have hcur : σ.curThread = ct.bv := by rw [hs.curThread, hctd, hc.cur]; rfl
  obtain ⟨-, x, hk⟩ := hX.curTcb hcur
  have hrun : Fl4Spec.runnable x.tcbState = true := hC x (by rw [hcur]; exact hk)
  have hσ1 : σ1 = Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv := by
    rw [hcur, Notif.setThreadState_eq .restart hk] at hst
    have := congrArg (fun q => ((), σ1) ∈ q.1) hst
    simp only [Set.mem_singleton_iff, Prod.mk.injEq, true_and] at this
    exact of_eq_true this
  subst hσ1
  have hcr : (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv).archState.x64CurrentCr3 =
      σ.archState.x64CurrentCr3 := by
    unfold Notif.stsAct; split <;> rfl
  have hAR : AR ar σ.archState.x64CurrentCr3 := hX.fin.1.1.2.2.2.2.2.2
  unfold tcb.restart_caller
  step with P1.sched.cur_thread.spec as ⟨ct', hct'⟩
  subst hct'
  refine WP.spec_bind (XTopAt.restart hX hcur hk hrun) ?_
  rintro s1 ⟨hX1, -, hks1⟩
  have hI1 := hX1.irelK (by rw [hks1]; exact hKA) (hBW _ _ _ _ hX1)
  rw [hcr] at hI1
  obtain ⟨hRel, hSV, hInv, hOC, hSE, hSN⟩ := hOK _ _ hI1
  refine WP.spec_bind (set_priority_irel hP0 hI1 hpT v hv hAct hRel hSV hInv hOC hSE hSN) ?_
  rintro s2 ⟨σ2, hm, hI2⟩
  simp only [WP.spec_ok]
  obtain ⟨⟨Z', -, -, -, -, -, -, -, -, hZ'⟩, -⟩ := IRel.xtop (L := L) (AR := AR) (a := ar) hI2 hAR
  exact ⟨trivial, ((), σ2), by rw [hm]; exact Set.mem_singleton _, (SRT.relTop hI2).1, Z', hZ'⟩

end

end

end Fl4Proofs.P3
