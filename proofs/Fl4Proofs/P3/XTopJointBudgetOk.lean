/-
P3 (DESIGN.md §9), kernel entry: **`budget_ok` at `J` when it lets the
system call run** (KENTRY-PLAN item 10, the true branch).

* `check_budgetT` / `check_budget_restartT` (SchedRel level): when FL4's
  `check_budget(_restart)` returns `true` the state and the arch state are
  unchanged and the spec's `getScRefillSufficient` of the current SC for the
  consumed time is `true` (FL4 has one domain: `is_cur_domain_expired` is
  `false`, so `true` is exactly `sufficient`); the other branch (the charge
  with `can_timeout_fault = true`, or the restart) only by P0 totality, the
  post asking nothing there.
* `checkBudgetRestart_suff` (spec): a sufficient current SC makes l4v's
  `check_budget_restart` return `true` without a state change.
* `JAtZ.budgetOkJ`: from `JAtZ` with `CurInv` and `OffReady` at kernel entry
  (ScEntryRd's `budget_ok_offReady` premises), when FL4's `budget_ok`
  returns `true`, l4v's `update_time_stamp; check_budget_restart` returns
  `true` and `JAtZ` holds after (XTopJointPP's `JAtZ.timestampJ`, its `OffOK`
  from `OffReady` and the sufficient head, `CurOwnW` from `CurInv`), with
  `CurInv`, `OffReady` (hence `JEntryAt.rd0`, `OffReady.rd0`) and `Entered`
  carried. The false branch (the current thread's timeout fault inside
  `charge_budget`) is not covered: its post is vacuous.
-/
import Fl4Proofs.P3.XTopJointPP
import Fl4Proofs.P3.ScCharge7
import Fl4Proofs.P3.ScEntryRd
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-- **A sufficient current SC: `check_budget_restart` returns `true` and
changes nothing** (one domain). -/
theorem checkBudgetRestart_suff {σ : State Unit} (hnd : numDomains = 1)
    (hb : getScRefillSufficient (Z := Unit) σ.curSc σ.consumedTime σ = ({(true, σ)}, False))
    {xt : Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xt)) :
    checkBudgetRestart (Z := Unit) σ = ({(true, σ)}, False) := by
  have h1 : checkBudget (Z := Unit) σ = ({(true, σ)}, False) := by
    unfold checkBudget
    rw [nd_gets_bind, nd_gets_bind, nd_bind_one hb]
    have e : isCurDomainExpired σ = false := by simp [isCurDomainExpired, hnd]
    show (do let domExp ← NonDet.gets isCurDomainExpired; return !domExp) σ = _
    rw [nd_gets_bind, e]; rfl
  unfold checkBudgetRestart
  rw [nd_bind_one h1, nd_gets_bind, nd_bind_one (getThreadState_eq hkt)]
  unfold NonDet.when
  rw [if_neg (by simp), nd_bind_one (rfl : NonDet.pure () σ = ({((), σ)}, False))]
  rfl

end Spec

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- **`check_budget` returning `true`**: nothing changed, and the current SC
sufficient for the consumed time (module docstring). -/
theorem check_budgetT {N T C : Set U64} {c : U64} (hA : P0.ArchTotal ar) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hscC : nodeW st s c layout.node.CUR_SC ∈ C)
    (hact : (nodeW st s c layout.node.CUR_SC).bv ≠ σ.idleSc → ∀ x n,
      σ.kheap (nodeW st s c layout.node.CUR_SC).bv = some (.schedContext x n) → Fl4Spec.scActive x = true)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) :
    sched.check_budget st ar s a ⦃ r => r.1 = true → r.2 = (s, a) ∧
      Fl4Spec.getScRefillSufficient (Z := Unit) σ.curSc σ.consumedTime σ = ({(true, σ)}, False) ∧
      ∀ y n, σ.kheap σ.curSc = some (.schedContext y n) →
        Fl4Spec.refillSufficient σ.consumedTime (Fl4Spec.refillHd y) = true ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x, n, hk, hx⟩ := hs.scs _ hscC
  unfold sched.check_budget
  step with sched.cur_sc.spec' as ⟨sc', hsc'⟩
  step with sched.consumed.spec' as ⟨cn, hcn⟩
  rw [hc.cur] at hsc' hcn
  subst hsc' hcn
  have hax : Fl4Spec.scActive x = true := by
    by_cases hi : (nodeW st s c layout.node.CUR_SC).bv = σ.idleSc
    · exact hx.active_of_rmax (hx.idle hi)
    · exact hact hi x n hk
  refine WP.spec_bind (sufficient_refines s a σ hS hscC hk hax _ hmb) ?_
  intro b hb
  by_cases hbt : b = true
  · rw [if_pos hbt, is_cur_domain_expired_eq]
    simp only [bind_ok]
    refine (WP.spec_ok _).2 fun _ => ?_
    have hb' : Fl4Spec.getScRefillSufficient (Z := Unit) σ.curSc σ.consumedTime σ = ({(true, σ)}, False) := by
      rw [hs.curSc, hs.consumed, ← hbt]; exact hb
    refine ⟨rfl, hb', fun y m hy => ?_⟩
    rw [hs.curSc, hk] at hy; cases hy
    rw [getScRefillSufficient_eq hk (by rw [(hx.strong hax).refills]; exact refills_ne (hx.strong hax).wf)] at hb
    have eb := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hb))).1
    rw [hs.consumed]; exact eb.trans hbt
  · rw [if_neg hbt]
    refine WP.spec_bind (Pₘ := fun _ => True) (P0.sched.charge_budget.p0 st ar s a _ true L.total hA) ?_
    rintro ⟨s1, a1⟩ -
    refine (WP.spec_ok _).2 ?_
    intro h; exact absurd h (by simp)

/-- **`check_budget_restart` returning `true`** (`check_budgetT`; the
restart only on `false`). -/
theorem check_budget_restartT {N T C : Set U64} {c : U64} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hS : SchedRel st N T C c s σ) (hscC : nodeW st s c layout.node.CUR_SC ∈ C)
    (hact : (nodeW st s c layout.node.CUR_SC).bv ≠ σ.idleSc → ∀ x n,
      σ.kheap (nodeW st s c layout.node.CUR_SC).bv = some (.schedContext x n) → Fl4Spec.scActive x = true)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) :
    sched.check_budget_restart st ar s a ⦃ r => r.1 = true → r.2 = (s, a) ∧
      Fl4Spec.getScRefillSufficient (Z := Unit) σ.curSc σ.consumedTime σ = ({(true, σ)}, False) ∧
      ∀ y n, σ.kheap σ.curSc = some (.schedContext y n) →
        Fl4Spec.refillSufficient σ.consumedTime (Fl4Spec.refillHd y) = true ⦄ := by
  unfold sched.check_budget_restart
  refine WP.spec_bind (check_budgetT hA s a σ hS hscC hact hmb) ?_
  rintro ⟨r, s1, a1⟩ hB
  step with sched.cur_thread.spec' as ⟨ct, _⟩
  by_cases hr : r = true
  · subst hr
    rw [if_pos rfl]
    exact (WP.spec_ok _).2 hB
  · have hr' : r = false := by simpa using hr
    subst hr'
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_bind (Pₘ := fun _ => True) (P0.sched.is_runnable.p0 st s1 ct L.total) ?_
    intro b _
    split
    · refine WP.spec_bind (Pₘ := fun _ => True) (P0.sched.set_thread_state.p0 st s1 ct _ L.total) ?_
      intro s2 _
      refine (WP.spec_ok _).2 ?_
      intro h; exact absurd h (by simp)
    · refine (WP.spec_ok _).2 ?_
      intro h; exact absurd h (by simp)

end

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 8000000 in
/-- **`budget_ok` at `J`, when it lets the system call run** (KENTRY-PLAN item
10, true branch; module docstring): the clock [P] (`NowAgree`), one domain,
the platform's `MIN_BUDGET` [P] (`hmb`), and at kernel entry `CurInv` and
`OffReady` (as ScEntryRd's `budget_ok_offReady`). -/
theorem JAtZ.budgetOkJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hAK : ARKeep arI AR)
    (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hnow : NowAgree arI a σ) (hC : CurInv σ)
    (hOR : OffReady σ) (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) :
    syscall.budget_ok st arI s a ⦃ r => r.1 = true → ∃ σ',
      (Fl4Spec.updateTimeStamp (Z := Unit) >>= fun _ => Fl4Spec.checkBudgetRestart) σ = ({(true, σ')}, False) ∧
      σ'.kheap = σ.kheap ∧ σ'.curThread = σ.curThread ∧ σ'.curSc = σ.curSc ∧
      σ'.schedulerAction = σ.schedulerAction ∧ σ'.idleThread = σ.idleThread ∧
      CurInv σ' ∧ OffReady σ' ∧
      ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' r.2.1 r.2.2 σ' ⦄ := by
  have hS := J.xtop.fin.1.1.1
  have hR := J.xtop.fin.1.1.2.2.1
  have hnow' : arI.now a ⦃ r => ∃ ms, Fl4Spec.doMachineOp (Z := Unit) Fl4Spec.getCurrentTime σ =
      ({(r.1.bv, { σ with machineState := ms })}, False) ∧ σ.curTime ≤ r.1.bv ⦄ :=
    WP.spec_mono hnow fun _ ⟨ms, h1, h2, _⟩ => ⟨ms, h1, h2⟩
  obtain ⟨r0, -, hr0⟩ := spec_exists hnow
  obtain ⟨ms, hm, -, -⟩ := hr0
  have hE := Sched.updateTimeStamp_eq' hnd hm
  unfold syscall.budget_ok
  refine WP.spec_bind (WP.spec_and (J.timestampJ arI hAK hA hnd hnow)
    (update_timestamp_refines s a σ hS hR J.nsc hnd hnow')) ?_
  rintro ⟨s1, a1⟩ ⟨⟨σ1, h1, hk1, hcs1, -, hct1, -, hum1, hO1, hJ1⟩, ⟨σ1', h1', hS1, -, -, hI1, hC1, hact1, -⟩⟩
  have e1 : σ1 = σ1' := by
    have e1 := (Prod.mk.inj (h1.symm.trans h1')).1
    exact congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 e1)
  subst e1
  have hσ1 : σ1 = _ := congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 (Prod.mk.inj (h1.symm.trans hE)).1)
  have hid1 : σ1.idleThread = σ.idleThread := by rw [hσ1]
  have hI1 := hI1 J.inv
  have hC1 := hC1 hC
  obtain ⟨hscC, -, -, -, hact, -, -⟩ := CurInv.facts hS1 hI1 hC1
  refine WP.spec_mono (check_budget_restartT hA s1 a1 σ1 hS1 hscC hact (hmb a1)) ?_
  rintro ⟨r, s2, a2⟩ hB hr
  obtain ⟨e, hb, hsuf⟩ := hB hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  have hr' : r = true := hr
  subst hr'
  obtain ⟨xt, hkt, -, -⟩ := hC1.tcb
  have hOR1 : OffReady σ1 := hO1 hOR
  have hOK : OffOK σ1 := hOR1.ok hsuf
  have hOw : CurOwnW Z.T Z.C σ1 := Or.inl (curOwn_of_curInv hS1 hI1 hC1)
  obtain ⟨-, hJ⟩ := hJ1 σ1.machineState _ hum1 id
  obtain ⟨Ac', Lst', D', J'⟩ := hJ hOK hOw
  refine ⟨σ1, ?_, hk1, hct1, hcs1, hact1, hid1, hC1, hOR1, Ac', Lst', D', J'⟩
  rw [nd_bind_one h1]
  exact checkBudgetRestart_suff hnd hb hkt

end

end

end Fl4Proofs.P3
