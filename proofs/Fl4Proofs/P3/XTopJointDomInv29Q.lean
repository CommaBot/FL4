/-
P3 (tmofr gen 2): **`kernel_entry_domInvU29` with two `SInvX` facts at the
same joint state**, and their FL4 words.

* **`kernel_entry_domInvU29Q`**: `kernel_entry_domInvU29` (left as it was)
  whose conclusion also exports, at the same `J`, the spec facts
  `SInvX.ctQ` (the current thread is in no ready queue, l4v `ct_not_in_q`)
  and `SInvCQ.idleSt` (the idle thread is in `IdleThreadState`, l4v
  `valid_idle`). Same premises; derived from `kernel_entry_reachU29` as
  `kernel_entry_domInvU29` is.
* `JAtZ.curQ0`: at a `JAtZ` state, a current thread in no spec ready queue has
  its `Q_QUEUED` bit clear (`SchedCore.queued`, `SchedSpec.rq`; the first half
  of `JAtZ.curBits` without the release-queue fact).
* `JAtZ.idleTS`: at a `JAtZ` state, an idle thread in `IdleThreadState` has
  state word `TS_IDLE` (7, `TcbRel1.st`); `JAtZ.idleNR`: so it is not
  `Runnable`.

No premise beyond U29's. No existing statement changed.
-/
import Fl4Proofs.P3.XTopJointDomInv29
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **The current thread's `Q_QUEUED` bit is clear** when the spec's current
thread is in no ready queue. -/
theorem JAtZ.curQ0 (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hq : ∀ d p, σ.curThread ∉ σ.readyQueues d p) :
    (L.mem s (P1.inqA (L.curW s)) &&& sched.Q_QUEUED) = 0#u64 := by
  obtain ⟨Q, R, hc, hs⟩ := J.xtop.fin.1.1.1.lists
  have ecw : L.curW s = nodeW st s Z.c layout.node.CUR_THREAD := by
    unfold P1.LawfulStore.curW nodeW; rw [hc.cur]
  rw [ecw]
  refine Classical.byContradiction fun h => ?_
  have hm := (hc.queued _ hc.curT).1 h
  apply hq 0 (specPrio (L.mem s (P1.prioA (nodeW st s Z.c layout.node.CUR_THREAD))))
  rw [hs.rq _ (hc.prio _ hc.curT), hs.curThread]
  exact List.mem_map_of_mem hm

/-- **The idle thread's state word is `TS_IDLE`** when the spec's idle thread
is in `IdleThreadState`. -/
theorem JAtZ.idleTS (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hi : ∀ x, σ.kheap σ.idleThread = some (.tcb x) → x.tcbState = .idleThreadState) :
    L.mem s (P1.stA (L.idleW s)) = sched.TS_IDLE := by
  obtain ⟨Q, R, hc, hs⟩ := J.xtop.fin.1.1.1.lists
  have eiw : L.idleW s = nodeW st s Z.c layout.node.IDLE_THREAD := by
    unfold P1.LawfulStore.idleW nodeW; rw [hc.cur]
  have hI := J.xtop.irelK J.ks J.buf
  have hR := hI.1.toE
  obtain ⟨x, hkx, -⟩ := hI.1.tcb _ hc.idleT
  have hxt := hR.at_tcb hc.idleT hkx
  have hst := hi x (by rw [hs.idleTh]; exact hkx)
  have h7 : (L.mem s (tStA (nodeW st s Z.c layout.node.IDLE_THREAD))).val = 7 := by
    rw [hxt.st, hst]; rfl
  rw [eiw]
  apply UScalar.eq_of_val_eq
  rw [Fl4Proofs.P0.Consts.sched.TS_IDLE.val_eq]
  exact h7

/-- **The idle thread's state word is not runnable** (`JAtZ.idleTS`). -/
theorem JAtZ.idleNR (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hi : ∀ x, σ.kheap σ.idleThread = some (.tcb x) → x.tcbState = .idleThreadState) :
    ¬ P1.Runnable (L.mem s (P1.stA (L.idleW s))) := by
  rw [J.idleTS hi]
  unfold P1.Runnable sched.TS_IDLE sched.TS_RUNNING sched.TS_RESTART sched.TS_RUNNING_VM; decide

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

set_option maxHeartbeats 8000000 in
/-- **`kernel_entry_domInvU29` with `ct_not_in_q` and `valid_idle` at the same
joint state** (module docstring): the conclusion of `kernel_entry_domInvU29`
with, after `EntryDomInv`, the spec facts `SInvX.ctQ` (the current thread is
in no ready queue) and `SInvCQ.idleSt` (the idle thread is in
`IdleThreadState`) of the `J` it returns. Same premises as
`kernel_entry_domInvU29`. -/
theorem kernel_entry_domInvU29Q [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧
      P1.EntryDomInv st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H) (P1.Heap.scs H)
        (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s ∧
      (∀ d p, σ.curThread ∉ σ.readyQueues d p) ∧
      (∀ x, σ.kheap σ.idleThread = some (.tcb x) → x.tcbState = .idleThreadState) ∧
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
        syscall.handle_syscall st arI s a n ⦃ r => EntDomAt st r.1 ⦄) ∧
      (∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
        KFinEv13 (L := L) arI AR .interrupt (KFrontI (st := st) arI s a1 w) σ →
        syscall.handle_interrupt_entry st arI s a1 w ⦃ r => EntDomAt st r.1 ⦄) ∧
      (∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
        KFinEv13 (L := L) arI AR (.userLevelFault n.bv c.bv) (KFrontF2 (st := st) arI (brU (st := st) arI n c) s a) σ →
        syscall.handle_user_exception st arI s a n c ⦃ r => EntDomAt st r.1 ⦄) ∧
      (∀ (ad c : U64) (ft : Fl4Spec.VMFaultType), σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
        KFinEv13 (L := L) arI AR (.vmFaultEvent ft) (KFrontF2 (st := st) arI (brV (st := st) arI ad c) s a) σ →
        syscall.handle_vm_fault st arI s a ad c ⦃ r => EntDomAt st r.1 ⦄) ∧
      (∀ (v : U64), σ.curThread ≠ σ.idleThread → v.val < 256 →
        (∀ ev, KEvSpec (.trap v) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontTrap (st := st) arI s a) w.2) →
        syscall.handle_trap_syscall st arI s a v ⦃ r => EntDomAt st r.1 ⦄) ∧
      (∀ (n : I64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
        (∀ ev, KEvSpec (.sysU n) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontSysU (st := st) arI n s a) w.2) →
        syscall.handle_syscall st arI s a n ⦃ r => EntDomAt st r.1 ⦄) := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, -, -, -, -, -, -, hSys, hIrq, hUs, hVm, hTr, hSU⟩ :=
    kernel_entry_reachU29 arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
  refine ⟨Z, H, Cs, Ac, Lst, D, J, ⟨J.entryInv hX.cr.2, J.domInv⟩, hX.ctQ, hX.cq.idleSt, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n c hct hn hfl hK hDL hFin
    refine WP.spec_mono (hSys n c hct hn hfl hK hDL hFin) ?_
    rintro r ⟨σ', -, hRJ, hX', -⟩
    exact JAt.entDomAt hRJ.2 hX'
  · intro w a1 hIh hE
    refine WP.spec_mono (hIrq w a1 hIh hE) ?_
    rintro r ⟨σ', -, hRJ, hX', -⟩
    exact JAt.entDomAt hRJ.2 hX'
  · intro n c hct hU hE
    refine WP.spec_mono (hUs n c hct hU hE) ?_
    rintro r ⟨σ', -, hRJ, hX', -⟩
    exact JAt.entDomAt hRJ.2 hX'
  · intro ad c ft hct hV hE
    refine WP.spec_mono (hVm ad c ft hct hV hE) ?_
    rintro r ⟨σ', -, hRJ, hX', -⟩
    exact JAt.entDomAt hRJ.2 hX'
  · intro v hct hv hE
    refine WP.spec_mono (hTr v hct hv hE) ?_
    rintro r ⟨ev, σ', -, -, hRJ, hX', -⟩
    exact JAt.entDomAt hRJ.2 hX'
  · intro n hct hU hND hE
    refine WP.spec_mono (hSU n hct hU hND hE) ?_
    rintro r ⟨ev, σ', -, -, hRJ, hX', -⟩
    exact JAt.entDomAt hRJ.2 hX'

end

end

end Fl4Proofs.P3.SInvR.G5
