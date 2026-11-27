/-
P3 (iolay gen 4): **YieldScope at every reachable joint state** — a thread with `tcbYieldTo ≠ none` is not
`blockedOnReceive`, and the current thread does not yield — carried beside `kernel_entry_reachU29`'s reachability
without changing it.

`YieldScopeS` / `CurYieldNone` are not fields of `SInvX` (nor derivable from it: iolay gen 3 checked SInvX, SInvA,
SchedValid, ValidIdle, ScYield, P1). They are a separate spec invariant (SpecInvYieldScopeT/F1..F4/H): every spec step
keeps `YieldScopeS`, and every kernel exit (`activate_thread`) gives `CurYieldNone`. This module adds the pair to
the reachable states:

* **`JReachY s a σ := JReachU17 s a σ ∧ YieldScopeS σ ∧ CurYieldNone σ`** (a new predicate; `JReachU17` unchanged).
* `SInvX.ftEntry`: ft3's entry facts `FaultTcbsS ∧ NQB` and `CtEntry` from `SInvX σ` and `ct ≠ idle`
  (`SInvA.fts` / `nqb`, `SInvB.entryJ`, `ctEntry_of_J`), the hypotheses of `kentry_yieldScope`.
* `evOut_yieldScope`: an `EvOut` outcome of a non-syscall event keeps the pair.
* **`kernel_entry_yieldScopeU29`**: same premises as `kernel_entry_reachU29`; at a `JReachY` state,
  `kernel_entry_reachU29`'s `JAtZ` with `SInvX σ`, `YieldScopeS σ`, `CurYieldNone σ`, and at the exit of each of the
  six entry kinds `RJ ∧ JReachY` at the exit state. The exits are `kernel_entry_reachU29`'s, whose spec outcome
  (`fl4KernelEntrySyscall` membership, `EvOut`) the spec tops of SpecInvYieldScopeH carry the pair across.
* `boot_yieldScope'`: the pair at `initASt`.

No new premise ([J]/[P]/[W]): every theorem's premises are those of `kernel_entry_reachU29`. No existing statement
changed.
-/
import Fl4Proofs.P3.JNativeScope
import Fl4Proofs.P3.SpecInvYieldScopeH
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

/-- ft3's entry facts at a state carrying `SInvX` whose current thread is not idle. -/
theorem SInvX.ftEntry {σ : Fl4Spec.State Unit} (hX : SInvX σ) (hct : σ.curThread ≠ σ.idleThread) :
    (SInv.FaultTcbsS σ ∧ SInv.NQB σ) ∧ SInv.CtEntry σ :=
  ⟨⟨hX.1.a.fts, hX.1.a.nqb⟩, SInvAll.ctEntry_of_J (SInvAll.SInvB.entryJ hX.1.sb hct) hX.1.a.nq⟩

/-- An `EvOut` outcome of a non-syscall event keeps YieldScope and gives the exit's `CurYieldNone`. -/
theorem evOut_yieldScope {fip : Bool} {ev : Fl4Spec.Event} {σ σ' : Fl4Spec.State Unit}
    (hev : ∀ c, ev ≠ .syscallEvent c) (hY : SInv.YieldScopeS σ) (h : EvOut fip ev σ σ') :
    SInv.YieldScopeS σ' ∧ SInv.CurYieldNone σ' := by
  cases fip
  · exact SInv.kcall_yieldScope true ev hev hY _ h
  · obtain ⟨w, hw, h⟩ := h
    exact SInv.kcallF_yieldScope true ev hev hY w hw _ h

/-- The pair at boot. -/
theorem boot_yieldScope' : SInv.YieldScopeS (Fl4Spec.initASt (Z := Unit)) ∧
    SInv.CurYieldNone (Fl4Spec.initASt (Z := Unit)) :=
  ⟨SInv.boot_yieldScope, SInv.boot_curYieldNone⟩

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **A receive-blocked thread's `YIELD_TO` word is 0** at a joint state carrying YieldScope (`TcbRel.st`:
its state word codes `blockedOnReceive`; `YieldRel.tcb`: the word is its `tcbYieldTo`). -/
theorem JAtZ.yield0_recv (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hY : SInv.YieldScopeS σ) {d : U64}
    (hd : d ∈ Z.T) (hs : (L.mem s (tStA d)).val = 3) : L.mem s (Fl4Proofs.P1.yieldA d) = 0#u64 := by
  obtain ⟨x, hk, hr⟩ := J.xtop.ipc.tcb d hd
  obtain ⟨e, r, dd, hst⟩ := tsCode_three (hr.st.symm.trans hs)
  have hn : x.tcbYieldTo = none := by
    by_contra hne
    have := hY _ x hk hne
    rw [hst] at this
    exact this
  obtain ⟨x', hk', hy⟩ := J.yld.tcb d hd
  rw [hk] at hk'
  cases hk'
  rw [hn] at hy
  unfold optRef at hy
  by_contra h0
  rw [if_neg h0] at hy
  cases hy

/-- **The head of a receive queue has `YIELD_TO = 0`** at a joint state carrying YieldScope (`EpObjRel` of the
endpoint: state 2 is `recvEP`, whose queue's threads have state word 3). -/
theorem JAtZ.yield0_recvHead (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hY : SInv.YieldScopeS σ)
    {ptr : U64} (hE : ptr ∈ Z.E) (hst : L.epState s ptr = 2#u64) :
    L.mem s (Fl4Proofs.P1.yieldA (L.mem s (Fl4Proofs.P1.epHeadA ptr))) = 0#u64 := by
  obtain ⟨x, -, hrel⟩ := J.xtop.ipc.ep ptr hE
  rw [epState_eq] at hst
  cases x with
  | idleEP => rw [hrel.1] at hst; exact absurd hst (by decide)
  | sendEP q => rw [hrel.1] at hst; exact absurd hst (by decide)
  | recvEP q =>
    obtain ⟨-, xs, hne, -, hQ, hon⟩ := hrel
    obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hne
    have hh : L.mem s (Fl4Proofs.P1.epHeadA ptr) = y := hQ.head
    rw [hh]
    exact JAtZ.yield0_recv J hY (hQ.mem y (List.mem_cons_self ..)) (hon y (List.mem_cons_self ..)).1

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **The reachable joint states with YieldScope** (module docstring). -/
abbrev JReachY (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  JReachU17 (L := L) arI AR MR s a σ ∧ SInv.YieldScopeS σ ∧ SInv.CurYieldNone σ

set_option maxHeartbeats 4000000 in
/-- **YieldScope at every reachable joint state and every kernel exit** (module docstring). Same premises as
`kernel_entry_reachU29`. -/
theorem kernel_entry_yieldScopeU29 [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachY (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ SInvX σ ∧ SInv.YieldScopeS σ ∧ SInv.CurYieldNone σ ∧
      (∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c →
        (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
          ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            KDispHypsKVU29 (L := L) arI AR (Z.mv Z.G V') H Cs D' s' a' σb n c) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            ∀ ct', sched.cur_thread st s' = ok ct' →
              JDecMRLK (L := L) arI VtxK AR MR (Z.mv Z.G V') H Cs D' s' a' σb ct') →
        (∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
          (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
            JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
            KFinAtR13 (L := L) arI AR Z' H' Cs' s' a' x.2) →
        syscall.handle_syscall st arI s a n ⦃ r => ∃ σ', RJ (L := L) arI AR r.1 r.2 σ' ∧
          JReachY (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
        KFinEv13 (L := L) arI AR .interrupt (KFrontI (st := st) arI s a1 w) σ →
        syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∃ σ', RJ (L := L) arI AR r.1 r.2 σ' ∧
          JReachY (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
        KFinEv13 (L := L) arI AR (.userLevelFault n.bv c.bv) (KFrontF2 (st := st) arI (brU (st := st) arI n c) s a) σ →
        syscall.handle_user_exception st arI s a n c ⦃ r => ∃ σ', RJ (L := L) arI AR r.1 r.2 σ' ∧
          JReachY (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (ad c : U64) (ft : Fl4Spec.VMFaultType), σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
        KFinEv13 (L := L) arI AR (.vmFaultEvent ft) (KFrontF2 (st := st) arI (brV (st := st) arI ad c) s a) σ →
        syscall.handle_vm_fault st arI s a ad c ⦃ r => ∃ σ', RJ (L := L) arI AR r.1 r.2 σ' ∧
          JReachY (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (v : U64), σ.curThread ≠ σ.idleThread → v.val < 256 →
        (∀ ev, KEvSpec (.trap v) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontTrap (st := st) arI s a) w.2) →
        syscall.handle_trap_syscall st arI s a v ⦃ r => ∃ σ', RJ (L := L) arI AR r.1 r.2 σ' ∧
          JReachY (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n : I64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
        (∀ ev, KEvSpec (.sysU n) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontSysU (st := st) arI n s a) w.2) →
        syscall.handle_syscall st arI s a n ⦃ r => ∃ σ', RJ (L := L) arI AR r.1 r.2 σ' ∧
          JReachY (L := L) arI AR MR r.1 r.2 σ' ⦄) := by
  obtain ⟨hJ, hY, hC⟩ := hJ
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, -, -, -, -, -, -, hSys, hIrq, hUs, hVm, hTr, hSU⟩ :=
    kernel_entry_reachU29 arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
  have hirq : ∀ c, (Fl4Spec.Event.interrupt) ≠ .syscallEvent c := by intro c h; cases h
  have huf : ∀ (w1 w2 : Fl4Spec.Word) c, (Fl4Spec.Event.userLevelFault w1 w2) ≠ .syscallEvent c := by
    intro _ _ c h; cases h
  have hvf : ∀ (ft : Fl4Spec.VMFaultType) c, (Fl4Spec.Event.vmFaultEvent ft) ≠ .syscallEvent c := by
    intro _ c h; cases h
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, hY, hC, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n c hct hn hfl hK hDL hFin
    refine WP.spec_mono (hSys n c hct hn hfl hK hDL hFin) ?_
    rintro r ⟨σ', hm, hRJ, -, -, -, -, -, -, hJR⟩
    obtain ⟨hF, hE⟩ := SInvX.ftEntry hX hct
    exact ⟨σ', hRJ, hJR, SInv.kentry_yieldScope true c hY hC hF hE _ hm⟩
  · intro w a1 hIh hE
    refine WP.spec_mono (hIrq w a1 hIh hE) ?_
    rintro r ⟨σ', hEv, hRJ, -, -, -, -, -, hJR⟩
    exact ⟨σ', hRJ, hJR, evOut_yieldScope hirq hY hEv⟩
  · intro n c hct hU hE
    refine WP.spec_mono (hUs n c hct hU hE) ?_
    rintro r ⟨σ', hEv, hRJ, -, -, -, -, -, hJR⟩
    exact ⟨σ', hRJ, hJR, evOut_yieldScope (huf _ _) hY hEv⟩
  · intro ad c ft hct hV hE
    refine WP.spec_mono (hVm ad c ft hct hV hE) ?_
    rintro r ⟨σ', hEv, hRJ, -, -, -, -, -, hJR⟩
    exact ⟨σ', hRJ, hJR, evOut_yieldScope (hvf _) hY hEv⟩
  · intro v hct hv hE
    refine WP.spec_mono (hTr v hct hv hE) ?_
    rintro r ⟨ev, σ', hK, hEv, hRJ, -, -, -, -, -, hJR⟩
    exact ⟨σ', hRJ, hJR, evOut_yieldScope hK.not_sys hY hEv⟩
  · intro n hct hU hND hE
    refine WP.spec_mono (hSU n hct hU hND hE) ?_
    rintro r ⟨ev, σ', hK, hEv, hRJ, -, -, -, -, -, hJR⟩
    exact ⟨σ', hRJ, hJR, evOut_yieldScope hK.not_sys hY hEv⟩

end

end

end Fl4Proofs.P3.SInvR.G5
