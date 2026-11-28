/-
P3 (DESIGN.md §9), CSpace: **`WJL` across the caller's restart** and the CNode
Delete and Revoke labels with the deletion at `WJL` (XTopJointWJLDel's
`JDelHypL`), so that they need no `LiveJHyp`.

* `LiveDN th H Cs G s σ`: `LiveJ`, `DbgWF` and `NullOrig` at a state (the
  three facts `WJL` adds to `WJR`; the entry fact `JEntryAt.live`).
* `WJL.restart`: the caller's restart keeps `WJL` from `JAtZ`, `LiveDN`,
  `SpecGlob` and `PPR0` at the start: the slots, the original bits and the
  debug words kept (P1's `set_thread_state.restart_ok` footprint,
  `Foot.dbgKeep`), the TCB zombies' TCBs dead after (XTopJointRest's
  `jowes_restartD` at the dead set grown by `ZTcb`, `JAtZ.addDeadSet`: a dead TCB is
  `TS_INACTIVE`, the restarted current thread runnable, so it is no TCB
  zombie's TCB), then XTopJointWJLFin's `wjl_keep`. `EJL.restart`: with
  `DelE` (`delE_restart`).
* `cn_del_topJL`, `decode_invocation_cnode_{revoke,delete}JL`,
  `decode_invocation_cnodeJ_stepsL`: XTopJointCnDel's `cn_del_topJ`,
  `decode_invocation_cnode_{revoke,delete}J` and
  the former `decode_invocation_cnodeJ_steps` with the deletion at `EJL` (`DelE ∧ WJL`,
  `JDelHypL`; the preemption point by `rppHyp_fullW` of `jPreemptHypL`), from
  `LiveDN` at the invocation's start.
-/
import Fl4Proofs.P3.XTopJointWJLDel
import Fl4Proofs.P3.XTopJointIrqDel
import Fl4Proofs.P3.ZNoBlkJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- **The caller's restart keeps `WJL`** (module docstring). -/
theorem WJL.restart {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hsg : SpecGlob σ) (hP0 : PPR0 σ)
    (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ) {ct : U64} (hct : sched.cur_thread st s = ok ct) :
    ∀ s1 σ1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
      WJL (L := L) arI AR Z H Cs (L.ksb s) s1 ar σ1 Z.G := by
  intro s1 σ1 hs1 hst
  have hsg1 : SpecGlob σ1 := SpecGlob.sts (mem_of_single hst) hsg
  obtain ⟨hcur, x, hk, hrun⟩ := J.curRunnable hni hct
  have htcb : Z.th ct = some .tcb := (J.xtop.curTcb hcur).1
  have e : σ1 = Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv := by
    rw [hcur, Notif.setThreadState_eq .restart hk] at hst
    have := congrArg (fun q => ((), σ1) ∈ q.1) hst
    simp only [Set.mem_singleton_iff, Prod.mk.injEq, true_and] at this
    exact of_eq_true this
  subst e
  obtain ⟨hL, hDW, hN⟩ := hLv
  have h := XTopAt.restart J.xtop hcur hk hrun
  rw [hs1, WP.spec_ok] at h
  obtain ⟨hX1, hSS, hk1⟩ := h
  obtain ⟨Ac1, Lst', J1⟩ := J.restartSJ (jStepHyps arI) hcur hk htcb hrun hs1
  have hns1 : Vs.NoSwitch (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) := by
    intro u e
    unfold Notif.stsAct at e
    split_ifs at e
    all_goals first
      | (have e2 : σ.schedulerAction = .switchThread u := e
         rw [hni.2] at e2; cases e2)
      | cases e
  -- the debug words: P1's footprint of the restart
  have hT : ct ∈ Z.T := J.thT ct htcb
  have hK : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s1 := by
    obtain ⟨x', hk', hRt⟩ := J.xtop.ipc.tcb ct hT
    rw [hk] at hk'; cases hk'
    have hnbr : ¬ P1.BlockedR (L.mem s (P1.stA ct)) := fun hb => by
      have hq := Sched.blockedR_queued hRt.st hb
      cases hx : x.tcbState <;> simp_all [Fl4Spec.runnable, Fl4Spec.ipcQueuedThreadState]
    have hTe : Z.T = P1.Heap.tcbs H := by
      obtain ⟨Tr, Cq, hJ⟩ := J.jpl
      exact Set.ext fun t => ⟨fun h => J.zH.1 t h, fun h => J.thT t ((hJ.tcb t).2 h)⟩
    rw [hTe] at hT
    exact P1.Foot.dbgKeep J.blk (Set.empty_subset _)
      (P1.sched.set_thread_state.restart_ok (Es := ∅) J.blk hT (fun h => hnbr (Or.inl h))
        (fun h => hnbr (Or.inr h)) hs1).2.1
  have hDS : DState (L := L) Z.th s σ Z.G := ⟨J.xtop.rel.2.1, J.del, J.xtop.rel.2.2.1⟩
  have hDS1 : DState (L := L) Z.th s1 (Notif.stsAct (Notif.updK σ ct.bv
      (.tcb { x with tcbState := .restart })) ct.bv) Z.G := ⟨J1.xtop.rel.2.1, J1.del, J1.xtop.rel.2.2.1⟩
  obtain ⟨hL1, hDW1, hN1⟩ := wjl_keep arI (Z := Z) (G := Z.G) (V := Z.vs) (V1 := Z.vs) J hDS hL hDW hN J1 J.zD hSS hDS1 hK (by unfold Notif.stsAct; split <;> rfl)
  exact ⟨⟨Z.vs, Ac1, Lst', D, J1, hk1, hns1, hsg1, hP0.of_ppk (PPK.restart hk .restart (Or.inl hcur.symm))⟩, hL1, hDW1, hN1⟩

/-- **`DelE` and `WJL`** (the deletion's invariant at `WJL`, `JDelHypL`). -/
abbrev EJL (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (K : Nat) (s : S)
    (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) : Prop :=
  DelE (L := L) Z.th K s σ ∧ WJL (L := L) arI AR Z H Cs kb s a σ G

/-- **The caller's restart keeps `EJL`** (module docstring). -/
theorem EJL.restart {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hsg : SpecGlob σ) (hP0 : PPR0 σ)
    (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ) {K : Nat} (hDE : DelE (L := L) Z.th K s σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) :
    ∀ s1 σ1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 → SlotsSame Z.th (L.mem s) (L.mem s1) →
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
      EJL (L := L) arI AR Z H Cs (L.ksb s) K s1 ar σ1 Z.G :=
  fun s1 σ1 hs1 hS hst => ⟨delE_restart hDE hS (ksub_of_eq (setThreadState_nks _ _) hst),
    WJL.restart arI J hni hsg hP0 hLv hct s1 σ1 hs1 hst⟩

/-- **A CNode cap at an FL4 label other than Revoke and Delete** decodes to
no invocation with a preemption point (`specDec_cnode_noPre`). -/
theorem cnode_noPre_of {slbl : Fl4Spec.Data} {lbl : U64}
    (hlbl : Fl4Spec.genInvocationType slbl = cnodeLabelOf lbl) (h : lbl.val ≠ 25 ∧ lbl.val ≠ 26)
    {fp : Bool} {args : List Fl4Spec.Data} {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr}
    {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {buffer : Option Fl4Spec.ObjRef} {σ : Fl4Spec.State Unit}
    {p r gs g : U64} :
    ∀ inv, DecOut (specDec fp slbl args ci sl (.CNode p r gs g) excaps buffer) σ inv → ¬ NoPre.PreInv inv := by
  refine specDec_cnode_noPre ?_ ?_ <;> rw [hlbl] <;> unfold cnodeLabelOf <;> intro e <;> split_ifs at e <;>
    first | omega | cases e

end

end

end Fl4Proofs.P3
