/-
P3 (DESIGN.md §9), invariant line G1 (ctq19): **`call_kernel` of every
event carries the ready-queue bundle to the exit** (spec side only, outside
the JAtZ cone; KENTRY-PLAN ctq17 handoff 1).

* The fault events (unknownSyscall, userLevelFault, vmFaultEvent,
  hypervisorEvent): `update_time_stamp` keeps SpecInvCqN3's `EvP`
  (`evp_auto`); `check_budget_restart` without restart gives `EB false`
  (ctq8's `eb_checkBudgetRestart_p`), with restart leaves the state; then the
  handler on the current thread `C`: `handle_fault` by ctq8's
  `eb_handleFault_p` (`NPQ C` from `EB true`, `NQ [C]`), `handle_vm_fault`
  keeps `EB true ∧ NQ [C] ∧ ct = C` to its error (`eb_auto` / `nq_auto` /
  `ct_auto`) and the catch runs `handle_fault`; the hypervisor fault is a
  no-op on x64 (`eb_faultArm`, `eb_handleEvent_fault`).
* The interrupt: `update_time_stamp` (`EvP`), `check_budget` (ctq8's
  `eb_checkBudget_p`, nq's `nq_checkBudget`, vi's `vi_checkBudget`), then
  ctq8's `ebx_maybeHandleInterrupt` (`NtfnQB` from `NQ []`, `IdS` from `VI`);
  the current thread may be idle here (`eb_handleEvent_irq`).
* `ok_other`: the non-syscall events are `withoutPreemption` (no error
  outcome), so the preemption handler never runs; **`ebx_handleE_other`**:
  every outcome `EBX N S false` (NQ: nq3's `nq_fl4HandleEvent_other`; VI:
  vi3's `vi_handleEvent_fault` for an active current thread,
  `vi_handleEvent_irq` for the interrupt).
* **`kcall_tq_other`** (ctq6's `rb_tail`) and **`kcall_tq`**: every event,
  with ctq17's `kcall_tq_sys` for the syscalls; the activeness premise is
  vi3's `kcall_validIdle_of` form (`activeSt ∨ ev = .interrupt`).
-/
import Fl4Proofs.P3.SpecInvCqN4
open Classical

namespace Fl4Proofs.P3.SInvQ.P19
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL
  Fl4Proofs.P3.SInvQ.P17

noncomputable section

set_option maxHeartbeats 2000000

section E
variable {C N S : ObjRef} {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef} {σe : State Unit}

theorem evp_updateTimeStamp : IK (EvP C N S I d Nq σe) (updateTimeStamp (Z := Unit)) := by
  evp_auto

/-- `handle_fault` on the current thread from `EvP`'s `EB true` and `NQ [C]`. -/
theorem eb_handleFault_c (ex : Fault) (s : State Unit) (hE : EB true s) (hN : NQ [C] s) (hc : s.curThread = C) :
    ∀ z ∈ (handleFault (Z := Unit) C ex s).1, EB false z.2 := fun z hz =>
  eb_weak (eb_handleFault_p (k := true) (K := [C]) C ex s (by rw [← hc]; exact npq_ct hE) hN
    (by rw [hc]; exact List.mem_singleton_self _) hE z hz)

/-- **A fault event's body**: `update_time_stamp`, `check_budget_restart`, the
handler `F` on the current thread. -/
theorem eb_faultArm (F : ObjRef → SMonad Unit Unit)
    (hF : ∀ s, EvP C N S I d Nq σe s → ∀ z ∈ (F C s).1, EB false z.2) (σ : State Unit)
    (hσ : EvP C N S I d Nq σe σ) :
    ∀ y ∈ ((do
        updateTimeStamp (Z := Unit)
        let restart ← checkBudgetRestart (Z := Unit)
        NonDet.when restart <| do
          let thread ← NonDet.gets fun s : State Unit => s.curThread
          F thread) σ).1, EB false y.2 := by
  intro y ⟨y1, h1, hy⟩
  have hσ1 : EvP C N S I d Nq σe y1.2 := evp_updateTimeStamp σ hσ y1 h1
  obtain ⟨y2, h2, hy⟩ := hy
  (try dsimp only at hy)
  unfold NonDet.when at hy
  split at hy
  · rename_i hr
    have e2 : y2.2 = y1.2 := SInv.checkBudgetRestart_true h2 hr
    obtain ⟨y3, h3, hy⟩ := hy
    rw [mem_gets h3] at hy
    (try dsimp only at hy)
    rw [e2, hσ1.1.1.2.1] at hy
    exact hF _ hσ1 y hy
  · rename_i hr
    rw [Set.mem_singleton_iff.1 hy]
    have h := eb_checkBudgetRestart_p y1.2 (hb_of_evp hσ1) (nq_weak_nil _ hσ1.1.1.2.2.2) hσ1.1.1.1 y2 h2
    cases hw : y2.1
    · rw [hw] at h; exact h
    · exact absurd hw hr

/-- `handle_vm_fault` keeps `EB true`, `NQ [C]` and the current thread. -/
theorem fv_handleVmFault (ft : VMFaultType) :
    IKE (fun s => EB true s ∧ NQ [C] s ∧ s.curThread = C) (handleVmFault (Z := Unit) C ft) :=
  fun σ h y hy => ⟨(show EBKE true (handleVmFault (Z := Unit) C ft) by eb_auto) σ h.1 y hy,
    (show NQKE [C] (handleVmFault (Z := Unit) C ft) by nq_auto) σ h.2.1 y hy,
    (show CTKE C (handleVmFault (Z := Unit) C ft) by ct_auto) σ h.2.2 y hy⟩

set_option maxHeartbeats 8000000 in
/-- **The fault events**: every outcome `EB false`. -/
theorem eb_handleEvent_fault (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) (hi : ev ≠ .interrupt)
    (σ : State Unit) (hσ : EvP C N S I d Nq σe σ) :
    ∀ y ∈ ((handleEvent (Z := Unit) ev).run σ).1, EB false y.2 := by
  have hHF : ∀ ex s, EvP C N S I d Nq σe s → ∀ z ∈ (handleFault (Z := Unit) C ex s).1, EB false z.2 :=
    fun ex s hs => eb_handleFault_c ex s hs.1.1.1 hs.1.1.2.2.2 hs.1.1.2.1
  cases ev with
  | syscallEvent c => exact absurd rfl (h c)
  | interrupt => exact absurd rfl hi
  | unknownSyscall n =>
    simp only [handleEvent, withoutPreemption]
    exact hk_liftE (eb_faultArm _ (hHF _))  σ hσ
  | userLevelFault w1 w2 =>
    simp only [handleEvent, withoutPreemption]
    exact hk_liftE (eb_faultArm _ (hHF _)) σ hσ
  | vmFaultEvent ft =>
    simp only [handleEvent, withoutPreemption]
    refine hk_liftE (eb_faultArm _ ?_) σ hσ
    intro s hs z hz
    exact hk_catch (I := fun s => EB true s ∧ NQ [C] s ∧ s.curThread = C) (Q0 := EB false)
      (hkr_of_ike (fv_handleVmFault ft) fun _ h => eb_weak h.1)
      (fun e s' hs' z' hz' => eb_handleFault_c e s' hs'.1 hs'.2.1 hs'.2.2 z' hz')
      s ⟨hs.1.1.1, hs.1.1.2.2.2, hs.1.1.2.1⟩ z hz
  | hypervisorEvent ht =>
    simp only [handleEvent, withoutPreemption]
    refine hk_liftE (eb_faultArm _ ?_) σ hσ
    intro s hs z hz
    cases ht
    exact eb_weak ((ik_pure (P := EB true) ()) s hs.1.1.1 z hz)

/-- **The interrupt**: every outcome `EBX N S false` (the current thread may be idle). -/
theorem ebx_handleEvent_irq (σ : State Unit) (hσ : EvP C N S I d Nq σe σ) :
    ∀ y ∈ ((handleEvent (Z := Unit) .interrupt).run σ).1, EBX N S false y.2 := by
  simp only [handleEvent, withoutPreemption]
  refine hk_liftE ?_ σ hσ
  intro σ hσ y ⟨y1, h1, hy⟩
  have hσ1 : EvP C N S I d Nq σe y1.2 := evp_updateTimeStamp σ hσ y1 h1
  obtain ⟨y2, h2, hy⟩ := hy
  have hE2 := eb_checkBudget_p y1.2 (hb_of_evp hσ1) (nq_weak_nil _ hσ1.1.1.2.2.2) hσ1.1.1.1 y2 h2
  have hN2 : NQ [] y2.2 := nq_checkBudget y1.2 hσ1.1.1.2.2.2 y2 h2
  have hV2 : SInvI.VI N S false y2.2 := SInvI.vi_checkBudget y1.2 hσ1.1.2.2.1 y2 h2
  exact ebx_maybeHandleInterrupt N S false false y2.2 ⟨eb_weak hE2, hN2, hV2⟩ y hy

end E

/-! ## The event with its preemption handler -/

/-- The non-syscall events have no error outcome (`withoutPreemption`). -/
theorem ok_other (rep : Bool) (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) (σ : State Unit) :
    ∀ z ∈ ((fl4HandleEvent (Z := Unit) rep ev).run σ).1, ∃ a, z.1 = .ok a := by
  intro z hz
  rw [fl4HandleEvent_other rep ev h] at hz
  cases ev with
  | syscallEvent c => exact absurd rfl (h c)
  | _ =>
    simp only [handleEvent, withoutPreemption] at hz
    obtain ⟨x, -, rfl⟩ := ft_mem_liftE hz
    exact ⟨_, rfl⟩

section K
variable {C N S : ObjRef} {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}

set_option maxHeartbeats 4000000 in
/-- **A non-syscall event and its preemption handler**: every outcome `EBX N S false`
(`hV`: `VI N S true` unless the event is the interrupt). -/
theorem ebx_handleE_other (rep : Bool) (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) {σ : State Unit}
    (hσ : EvP C N S I d Nq σ σ) (hV : ev ≠ .interrupt → SInvI.VI N S true σ) :
    ∀ y ∈ (ExceptT.run (NonDetE.handleE (fl4HandleEvent (Z := Unit) rep ev)
      (fun _ => withoutPreemption preemptionPath)) σ).1, EBX N S false y.2 := by
  intro y hy
  unfold NonDetE.handleE at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨a, ha⟩ := ok_other rep ev h σ z hz
  obtain ⟨r, s⟩ := z
  simp only at ha; subst ha
  have hP : EBX N S false s := by
    by_cases hi : ev = .interrupt
    · subst hi
      rw [fl4HandleEvent_other rep _ h] at hz
      exact ebx_handleEvent_irq σ hσ _ hz
    · have hz' := hz
      rw [fl4HandleEvent_other rep _ h] at hz'
      exact ⟨eb_handleEvent_fault ev h hi σ hσ _ hz',
        nq_fl4HandleEvent_other C rep ev h σ ⟨hσ.2.2.1.1, hσ.2.2.1.2.1⟩ _ hz,
        vi_false_of_true (SInvI.vi_handleEvent_fault ev h hi σ (hV hi) _ hz')⟩
  first
    | (obtain rfl := Set.mem_singleton_iff.1 hy; exact hP)
    | (dsimp only at hy; obtain rfl := Set.mem_singleton_iff.1 hy; exact hP)

end K

/-! ## The tops -/

set_option maxHeartbeats 4000000 in
/-- **The ready-queue bundle across `call_kernel` of a non-syscall event.** -/
theorem kcall_tq_other (rep : Bool) (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) {σ : State Unit}
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (hX : EX σ) (hR : RB σ) (h4 : T4 σ) (hV : SInvI.ValidIdle σ) (hEO : SInvB.EntryOK σ)
    (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState ∨ ev = .interrupt)
    (hIu : Iu σ.curThread σ) (hIL : IL [σ.curThread] σ) (hJ : Js I σ.curThread d Nq σ σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, EX y.2 ∧ RB y.2 := by
  intro y hy
  unfold fl4CallKernel at hy
  obtain ⟨y1, h1, hy⟩ := hy
  have hσ := evp_start (I := I) (d := d) (Nq := Nq) hX hR h4 hV hEO hCX hIu hIL hJ
  have hx : EBX σ.idleThread σ.idleSc false y1.2 :=
    ebx_handleE_other rep ev h hσ (fun hi => SInvI.vi_true_of_active hV fun x hx => (ha x hx).resolve_right hi)
      y1 h1
  obtain ⟨hE1, hN1, hV2⟩ := hx
  exact rb_tail y1.2 ⟨hE1.1, SInvI.validIdle_of (σ := σ) hV2, hN1, hE1.2⟩ y hy

set_option maxHeartbeats 4000000 in
/-- **The ready-queue bundle across `call_kernel` of every event**: from the
carried entry facts, every outcome has ctq5's `EX` and ctq6's `RB` (`hct` is
vi3's `CtSc` [J] for the pinned syscalls; `hnd` SpecInvQDom's [P]). -/
theorem kcall_tq (hnd : numDomains = 1) (rep : Bool) (ev : Event) {σ : State Unit}
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (hX : EX σ) (hR : RB σ) (h4 : T4 σ) (hV : SInvI.ValidIdle σ) (hEO : SInvB.EntryOK σ)
    (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState ∨ ev = .interrupt)
    (hIu : Iu σ.curThread σ) (hIL : IL [σ.curThread] σ) (hJ : Js I σ.curThread d Nq σ σ)
    (hE : EF Nq σ) (hI2 : I.2 = σ.idleSc) (hI1 : IrqOutV (fun _ => I.1) (uV σ))
    (hO : SInvG.IdleOutV σ) (hI : SInvI.IdleScOutV σ)
    (hct : ∀ c, ev = .syscallEvent c → SInvI.Pinned c → SInvI.CtSc σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, EX y.2 ∧ RB y.2 := by
  by_cases hs : ∃ c, ev = .syscallEvent c
  · obtain ⟨c, rfl⟩ := hs
    exact kcall_tq_sys hnd rep c hX hR h4 hV hEO hCX
      (fun x hx => (ha x hx).resolve_right fun e => by cases e) hIu hIL hJ hE hI2 hI1 hO hI (hct c rfl)
  · exact kcall_tq_other rep ev (fun c e => hs ⟨c, e⟩) hX hR h4 hV hEO hCX ha hIu hIL hJ

end

end Fl4Proofs.P3.SInvQ.P19
