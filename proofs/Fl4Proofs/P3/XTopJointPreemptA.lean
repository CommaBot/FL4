/-
P3 (DESIGN.md §9): **the preemption path's charging branch with an endpoint
timeout handler, a reschedule pending or not** (KENTRY-PLAN kp15 (A)/(B)):
`JPreemptRestHypE` [W] split into what is proved, a [J] fact and a narrower
[W] rest.

* `JHole.mcsPPJA`: `mcs_preemption_point` at a hole with `CurInv`, a
  non-idle schedulable `Running`/`Restart` current thread in no ready queue,
  the action `ResumeCurThread` or `ChooseNewThread`, an insufficient head, a
  non-round-robin current SC and an endpoint timeout handler whose endpoint
  is idle or sending: ScChargeTA's `JHole.checkBudgetTA` (the FL4 `true`
  outcome is excluded by the insufficient head, `check_budgetT`); `JAt`
  after.
* `JHoleCtNQHyp` [J] (l4v `ct_not_queued`, the precondition of MCS
  `check_budget` / `charge_budget … True` in `preemption_point`): at a hole
  with `CurInv` and a schedulable current thread, the current thread is in
  no ready queue. At the invocation it is `JEntryAt.ctnq` (l4v `ct_not_in_q`
  under `resume_cur_thread`); the spec steps that enqueue the current thread
  (`set_priority` / `set_domain` / `yield_to` / `sched_context_bind_tcb` on
  it, `end_timeslice`'s append) are in no preemptible invocation, and the
  other enqueues (`possible_switch_to`, `reschedule_required`'s switch
  target) name woken or switched-to threads, never the running current one.
  Needed because a queued current thread blocked by its timeout fault would
  break `Inv.rq` (the spec does not dequeue it).
* `JPreemptRestHypC` [W]: `JPreemptRestHypE` narrowed to the timeout
  handler's endpoint with waiting receivers (`recvEP`), the current thread
  `Running`/`Restart` and unqueued, a non-round-robin SC (kp5 (i): the
  timeout fault's transfer to a receiver for the current thread from a
  `JTH`). `jPreemptRestHypE_ofC`: E from `JHoleCtNQHyp`, C and the platform
  facts; `dispatch_invokeJPZA` / `dispatch_invokeJEPZA` (new top).
-/
import Fl4Proofs.P3.ScChargeTA
import Fl4Proofs.P3.XTopJointPreemptE
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 16000000 in
/-- **`mcs_preemption_point` charging the current thread with an endpoint
timeout handler on an idle or sending endpoint, a reschedule pending or
not** (module docstring). -/
theorem JHole.mcsPPJA {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hAT : P0.ArchTotal arI)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hC : CurInv σ) (hni : σ.curThread ≠ σ.idleThread)
    (hres : σ.schedulerAction = .resumeCurThread ∨ σ.schedulerAction = .chooseNewThread)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p) (hsch : Fl4Spec.schedulable σ.curThread σ = true)
    (hnsuf : ¬ (∀ y n, σ.kheap σ.curSc = some (.schedContext y n) →
      Fl4Spec.refillSufficient σ.consumedTime (Fl4Spec.refillHd y) = true))
    {xt : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xt))
    (hrr : xt.tcbState = .running ∨ xt.tcbState = .restart)
    {p bd : Fl4Spec.Word} {r : Fl4Spec.CapRights} (hth : xt.tcbTimeoutHandler = .endpointCap p bd r)
    (hper : ∀ x n, σ.kheap σ.curSc = some (.schedContext x n) → x.scPeriod ≠ 0)
    (hcb : ∀ xe, σ.kheap p = some (.endpoint xe) → Endp.CanBlock false xe) :
    syscall.mcs_preemption_point st arI s a ⦃ r => ∃ σ',
      (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 → y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
      ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
      JAt (L := L) arI AR r.1 r.2 σ' ⦄ := by
  have hS := Hh.xtop.fin.1.1.1
  have hR := Hh.xtop.fin.1.1.2.2.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨hscC, -, -, -, hact, -, -⟩ := CurInv.facts hS Hh.inv hC
  unfold syscall.mcs_preemption_point
  step with sched.cur_thread.spec' as ⟨ct, hct'⟩
  step with Sched.sched.is_schedulable.spec' as ⟨b, hb⟩
  rw [hc.cur] at hct'
  subst hct'
  rw [schedulable_eq hR hS hc.curT] at hb
  have ect : σ.curThread = (nodeW st s Z.c layout.node.CUR_THREAD).bv := hs.curThread
  subst hb
  rw [← ect, hsch]
  simp only [↓reduceIte]
  refine WP.spec_bind (WP.spec_and (check_budgetT hAT s a σ hS hscC hact hmb)
    (Hh.checkBudgetTA hAT hC hni hres hnq hmrt hmb hkt hrr hth hper hcb)) ?_
  rintro ⟨r, s', a'⟩ ⟨hT, hF⟩
  refine (WP.spec_ok _).2 ?_
  cases r
  · obtain ⟨z, hz, -, V, Ac', Lst', D', J'⟩ := hF rfl
    exact ⟨z.2, fun y hy => mem_pp_sched hsch hz hy, fun hy => fail_pp_sched hsch hz hy,
      Z.mv Z.G V, H, Cs, Ac', Lst', D', J'⟩
  · exact absurd (hT rfl).2.2 hnsuf

variable (arI) in
/-- **[J] The current thread in no ready queue at a hole where it is
schedulable** (l4v `ct_not_queued`; module docstring). -/
def JHoleCtNQHyp (AR : A → Fl4Spec.Cr3 → Prop) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → CurInv σ →
    Fl4Spec.schedulable σ.curThread σ = true → ∀ d p, σ.curThread ∉ σ.readyQueues d p

variable (arI) in
/-- **The preemption path's charge with the current thread's timeout fault
sent to a waiting receiver** [W] (kp15: `JPreemptRestHypE` with the idle or
sending handler endpoint proved by `JHole.mcsPPJA` for either action, a
queued current thread excluded by `JHoleCtNQHyp`). Left: kp5 (i), l4v
`check_budget`'s `charge_budget … True` → `end_timeslice` → `handle_timeout`
→ `send_fault_ipc` → `send_ipc` to a receiver waiting on the handler's
endpoint, for the current thread inside `charge_budget` (a `JTH` state). -/
def JPreemptRestHypC (AR : A → Fl4Spec.Cr3 → Prop) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ →
    σ.curThread ≠ σ.idleThread → Vs.NoSwitch σ → CurScFree σ → CtOK σ → Chg σ →
    CurInv σ → Fl4Spec.schedulable σ.curThread σ = true →
    ¬ (∀ y n, σ.kheap σ.curSc = some (.schedContext y n) →
      Fl4Spec.refillSufficient σ.consumedTime (Fl4Spec.refillHd y) = true) →
    (∀ d p, σ.curThread ∉ σ.readyQueues d p) →
    (∀ x n, σ.kheap σ.curSc = some (.schedContext x n) → x.scPeriod ≠ 0) →
    ∀ (xt : Fl4Spec.Tcb) (p bd : Fl4Spec.Word) (r : Fl4Spec.CapRights) (q : List Fl4Spec.ObjRef),
      σ.kheap σ.curThread = some (.tcb xt) → (xt.tcbState = .running ∨ xt.tcbState = .restart) →
      xt.tcbTimeoutHandler = .endpointCap p bd r → σ.kheap p = some (.endpoint (.recvEP q)) →
    syscall.after_invocation st arI s a (.Err .Preempted) ⦃ r => PPQ (L := L) arI AR σ (r.2.1, r.2.2) ⦄

set_option maxHeartbeats 4000000 in
/-- **`JPreemptRestHypE` from `JHoleCtNQHyp` [J] and `JPreemptRestHypC` [W]**
(module docstring): outside `PPCov`, `NoTmoSend` fails (`CurInv`, non-idle,
no switch pending), so the handler is an endpoint cap and the SC not
round-robin; `NativeScope` makes the runnable thread `Running`/`Restart`;
`NoSwitch` leaves `ResumeCurThread` or `ChooseNewThread`; an idle or sending
endpoint is `JHole.mcsPPJA`, a receiving one `JPreemptRestHypC`. -/
theorem jPreemptRestHypE_ofC (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hNQ : JHoleCtNQHyp (L := L) arI AR) (hRC : JPreemptRestHypC (L := L) arI AR) :
    JPreemptRestHypE (L := L) arI AR := by
  intro s a σ hJ hn hi hs hf hc hg hC hsc hnsuf hcov
  have hnq := hNQ s a σ hJ hC hsc
  obtain ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh⟩ := hJ
  have hIrq := jIrqHypZ_of hARI hA hIP hP.minBudget hNS
  have hnt : ¬ NoTmoSend σ := fun h => hcov (Or.inl ⟨hC, hi, hs σ.curThread, h⟩)
  unfold NoTmoSend at hnt
  simp only [not_or, not_forall] at hnt
  obtain ⟨⟨xt, hkt, hep⟩, ⟨x0, n0, hk0, hp0⟩⟩ := hnt
  have hper : ∀ x n, σ.kheap σ.curSc = some (.schedContext x n) → x.scPeriod ≠ 0 := by
    intro x n hk; rw [hk0] at hk; cases hk; exact hp0
  obtain ⟨p, bd, r, hth⟩ : ∃ p bd r, xt.tcbTimeoutHandler = .endpointCap p bd r := by
    revert hep; cases xt.tcbTimeoutHandler <;> simp [Fl4Spec.isEpCap]
  have hrr : xt.tcbState = .running ∨ xt.tcbState = .restart := by
    obtain ⟨x1, -, -, -, hk1, -, hr1, -, -, -⟩ := schedulable_inv hsc
    rw [hkt] at hk1; cases hk1
    have hvm := hn _ _ hkt
    revert hr1 hvm; cases xt.tcbState <;> simp [Fl4Spec.runnable]
  have hres : σ.schedulerAction = .resumeCurThread ∨ σ.schedulerAction = .chooseNewThread := by
    rcases e : σ.schedulerAction with _ | u | _
    · exact Or.inl rfl
    · exact absurd e (hs u)
    · exact Or.inr rfl
  by_cases hcb : ∀ xe, σ.kheap p = some (.endpoint xe) → Endp.CanBlock false xe
  · exact WP.spec_mono (afterInv_of_mcs (Hh.mcsPPJA hA (hmrt a) (hP.minBudget a) hC hi hres hnq hsc hnsuf hkt
      hrr hth hper hcb) hIP hIrq _) fun _ h => h.2.toPPQ
  · simp only [not_forall] at hcb
    obtain ⟨xe, hke, hncb⟩ := hcb
    obtain ⟨q, rfl⟩ : ∃ q, xe = .recvEP q := by
      revert hncb; cases xe <;> simp [Endp.CanBlock]
    exact hRC s a σ ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh⟩ hn hi hs hf hc hg hC hsc hnsuf hnq hper xt p bd r q
      hkt hrr hth hke

set_option maxHeartbeats 4000000 in
/-- **`dispatch_invokeJPZE` with `JHoleCtNQHyp` [J] and `JPreemptRestHypC`
[W]** (kp15). -/
theorem dispatch_invokeJPZA [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (call bl don : Bool)
    (hn : InvSys number call bl don)
    (hG : JEntryGlob (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z s ar σ)
    (hP : JPathAt (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hNQ : JHoleCtNQHyp (L := L) arI AR) (hRC : JPreemptRestHypC (L := L) arI AR) :
    syscall.dispatch_syscall st arI s ar number ⦃ r =>
      DispPost (L := L) arI AR (PPQ (L := L) arI AR) (DispInv call bl don) σ r ⦄ :=
  dispatch_invokeJPZE s ar σ J ct hct number call bl don hn hG hE hP hARI hA hnd hPP hmrt hIP hNS
    (jPreemptRestHypE_ofC hARI hA hPP hmrt hIP hNS hNQ hRC)

set_option maxHeartbeats 4000000 in
/-- **`dispatch_invokeJEPZE` with `JHoleCtNQHyp` [J] and `JPreemptRestHypC`
[W]** (kp15; against `fl4HandleEvent true`'s branch). -/
theorem dispatch_invokeJEPZA [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (call bl don : Bool)
    (hn : InvSys number call bl don)
    (hG : JEntryGlob (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z s ar σ)
    (hP : JPathAt (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hNQ : JHoleCtNQHyp (L := L) arI AR) (hRC : JPreemptRestHypC (L := L) arI AR) :
    syscall.dispatch_syscall st arI s ar number ⦃ r =>
      DispPost (L := L) arI AR (PPQ (L := L) arI AR) (Fl4Spec.fl4HandleSyscall true (invSysOf call bl)) σ r ⦄ :=
  dispatch_invokeJEPZE s ar σ J ct hct number call bl don hn hG hE hP hARI hA hnd hPP hmrt hIP hNS
    (jPreemptRestHypE_ofC hARI hA hPP hmrt hIP hNS hNQ hRC)

end

end

end Fl4Proofs.P3
