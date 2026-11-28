/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN budtr): **`kernel_entryJ8B`:
`kernel_entryJ8` with the budget premise `KBudget.tmo` (false in reachable
states: a receiver waiting on the current thread's timeout-handler endpoint
satisfies neither disjunct) replaced by `ct_not_in_q`.**

* `KBudgetB`: `KBudget` (XTopJointKEntry) with `tmo : NoTmoSend σ0 ∨ (∀ d p,
  σ0.curThread ∉ σ0.readyQueues d p)` [J] (l4v `ct_not_in_q`: the current
  thread is not queued while `scheduler_action = resume_cur_thread`, which
  `Entered` gives; the same fact as `JEntryAt.ctnq` one step later). The old
  second disjunct's other conjuncts are derived: Running/Restart from
  `JAtZ.curRun` (`CurRunM.run` under `Entered`) and `NativeScope` (the top's
  existing [S] `hNSR` at the entry's `JAtZR`); the endpoint handler and the
  non-round-robin SC from `¬ NoTmoSend`; the handler endpoint's state is
  free: idle/sending by `JAtZ.budgetOkT`, receiving by XTopJointBudgetTR's
  `JAtZ.budgetOkTR`. `KBudget.toB`: the old premise implies the new.
* `JAtZ.budgetOkB`: `budget_ok` at an entry state under `KBudgetB`, both
  outcomes (the `hBud` block of `kernel_entryJ8`, every case).
* `kernel_entryJ8B` = `kernel_entryJ8` with `hB : … → KBudgetB …`.
-/
import Fl4Proofs.P3.XTopJointKEntry8
import Fl4Proofs.P3.XTopJointBudgetTR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The budget-check premises at the entry state after the `FaultIP`
write, the timeout case unrestricted** (module docstring): the clock [P]
`NowAgree`, `CurInv` and `OffReady` [J] as `KBudget`; `tmo` [J] l4v
`ct_not_in_q` unless no timeout-fault send is possible. -/
structure KBudgetB (a : A) (σ0 : Fl4Spec.State Unit) : Prop where
  now : NowAgree arI a σ0
  cur : CurInv σ0
  off : OffReady σ0
  tmo : NoTmoSend σ0 ∨ ∀ d p, σ0.curThread ∉ σ0.readyQueues d p

variable {arI}

theorem KBudget.toB {a : A} {σ0 : Fl4Spec.State Unit} (h : KBudget arI a σ0) : KBudgetB arI a σ0 :=
  ⟨h.now, h.cur, h.off, h.tmo.imp id fun h' => h'.1⟩

variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 16000000 in
/-- **`budget_ok` at an entry state under `KBudgetB`** (module docstring):
`kernel_entryJ8`'s `hBud` for every timeout-handler case. -/
theorem JAtZ.budgetOkB {s : S} {a : A} {σ0 : Fl4Spec.State Unit}
    (J0 : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ0) [VxE Z] (hni0 : Entered σ0) (hBu : KBudgetB arI a σ0)
    (hNS0 : NativeScope σ0) (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.budget_ok st arI s a ⦃ r =>
      (r.1 = true → ∃ σ', (Fl4Spec.updateTimeStamp (Z := Unit) >>= fun _ => Fl4Spec.checkBudgetRestart) σ0 =
          ({(true, σ')}, False) ∧
        σ'.kheap = σ0.kheap ∧ σ'.curThread = σ0.curThread ∧ σ'.curSc = σ0.curSc ∧
        σ'.schedulerAction = σ0.schedulerAction ∧ σ'.idleThread = σ0.idleThread ∧
        CurInv σ' ∧ OffReady σ' ∧ ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' r.2.1 r.2.2 σ') ∧
      (r.1 = false → ∃ z ∈ (specBudget σ0).1, z.1 = false ∧
        ∃ (Z' : XSets) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JAtZ (L := L) arI AR Z' H Cs Ac' Lst' D' r.2.1 r.2.2 z.2 ∧ VxE Z') ⦄ := by
  have hF : ∀ hnt : NoTmoSend σ0, syscall.budget_ok st arI s a ⦃ r =>
      (r.1 = true → ∃ σ', (Fl4Spec.updateTimeStamp (Z := Unit) >>= fun _ => Fl4Spec.checkBudgetRestart) σ0 =
          ({(true, σ')}, False) ∧
        σ'.kheap = σ0.kheap ∧ σ'.curThread = σ0.curThread ∧ σ'.curSc = σ0.curSc ∧
        σ'.schedulerAction = σ0.schedulerAction ∧ σ'.idleThread = σ0.idleThread ∧
        CurInv σ' ∧ OffReady σ' ∧ ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' r.2.1 r.2.2 σ') ∧
      (r.1 = false → ∃ z ∈ (specBudget σ0).1, z.1 = false ∧
        ∃ (Z' : XSets) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JAtZ (L := L) arI AR Z' H Cs Ac' Lst' D' r.2.1 r.2.2 z.2 ∧ VxE Z') ⦄ := fun hnt =>
    WP.spec_mono (WP.spec_and (J0.budgetOkJ hAK hA hnd hBu.now hBu.cur hBu.off hmb)
        (J0.budgetOkF hAK hA hnd hBu.now hni0 hBu.cur hmrt hmb hnt)) fun r ⟨h1, h2⟩ => ⟨h1, fun hf => by
          obtain ⟨σ', he, Ac', Lst', D', J'⟩ := h2 hf
          refine ⟨(false, σ'), ?_, rfl, _, Ac', Lst', D', J', inferInstance⟩
          unfold specBudget
          rw [he]; exact Set.mem_singleton _⟩
  rcases hBu.tmo with hnt | hnq
  · exact hF hnt
  by_cases hnt : NoTmoSend σ0
  · exact hF hnt
  -- an endpoint timeout handler and a non-round-robin SC
  unfold NoTmoSend at hnt
  push_neg at hnt
  obtain ⟨⟨xt, hkt, hep⟩, ⟨y, m, hky, hy⟩⟩ := hnt
  have hper : ∀ x n, σ0.kheap σ0.curSc = some (.schedContext x n) → x.scPeriod ≠ 0 := fun x n h => by
    rw [hky] at h; cases h; exact hy
  obtain ⟨p, bd, rr, hth⟩ : ∃ p bd rr, xt.tcbTimeoutHandler = .endpointCap p bd rr := by
    revert hep; cases xt.tcbTimeoutHandler <;> simp [Fl4Spec.isEpCap]
  have hrr : xt.tcbState = .running ∨ xt.tcbState = .restart := by
    have hrun := J0.curRun.run hni0 xt hkt
    have hvm := hNS0 _ xt hkt
    revert hrun hvm; cases xt.tcbState <;> simp [Fl4Spec.runnable]
  by_cases hkl : ∃ l, σ0.kheap p = some (.endpoint (.recvEP l))
  · exact WP.spec_mono (WP.spec_and (J0.budgetOkJ hAK hA hnd hBu.now hBu.cur hBu.off hmb)
        (J0.budgetOkTR hAK hA hnd hBu.now hni0 hBu.cur hmrt hmb hmax htu hnq hkt hrr hth hper hkl))
      fun r ⟨h1, h2⟩ => ⟨h1, fun hf => by
            obtain ⟨z, hz, hz1, V, Ac', Lst', D', J'⟩ := h2 hf
            exact ⟨z, hz, hz1, _, Ac', Lst', D', J', inferInstance⟩⟩
  · have hcb : ∀ xe, σ0.kheap p = some (.endpoint xe) → Endp.CanBlock false xe := fun xe h => by
      cases xe with
      | idleEP => trivial
      | sendEP q => rfl
      | recvEP q => exact absurd ⟨q, h⟩ hkl
    exact WP.spec_mono (WP.spec_and (J0.budgetOkJ hAK hA hnd hBu.now hBu.cur hBu.off hmb)
        (J0.budgetOkT hAK hA hnd hBu.now hni0 hBu.cur hmrt hmb hnq hkt hrr hth hper hcb))
      fun r ⟨h1, h2⟩ => ⟨h1, fun hf => by
            obtain ⟨z, hz, hz1, V, Ac', Lst', D', J'⟩ := h2 hf
            exact ⟨z, hz, hz1, _, Ac', Lst', D', J', inferInstance⟩⟩

end

end

end Fl4Proofs.P3
