/-
P3 (iolay gen 5): **YieldBlock at every reachable joint state** — a thread with `tcbYieldTo ≠ none` is not blocked
at all (SpecInvYieldBlockT/F1..F4/H), with `CurYieldNone` — carried beside `kernel_entry_reachU29`'s reachability
(as JYieldScope does for gen 4's weaker YieldScope; gen 4's modules unchanged).

* **`JReachYB s a σ := JReachU17 s a σ ∧ YieldBlockS σ ∧ CurYieldNone σ`**; `JReachYB.toY` (gives gen 4's `JReachY`).
* **`kernel_entry_yieldScope2U29`**: same premises as `kernel_entry_reachU29`; at a `JReachYB` state the `JAtZ` with
  `SInvX`, `YieldBlockS`, `CurYieldNone`, and at the exit of each of the six entry kinds `RJ ∧ JReachYB`.
* `JAtZ.yield0_blk`: a TCB of `Z.T` whose state word codes a blocked state (3 receive, 4 send, 5 reply,
  6 notification) has `YIELD_TO = 0` under YieldBlock (`TcbRel.st`, `YieldRel.tcb`).
* `KEvSpec.true_not_irq`, `boot_yieldBlock'`.

No new premise ([J]/[P]/[W]); no existing statement changed.
-/
import Fl4Proofs.P3.JYieldScope
import Fl4Proofs.P3.SpecInvYieldBlockH
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

theorem KEvSpec.true_not_irq {e : KEv} {ev : Fl4Spec.Event} (h : KEvSpec e true ev) : ev ≠ .interrupt := by
  cases h <;> intro h' <;> cases h'

theorem boot_yieldBlock' : SInv.YieldBlockS (Fl4Spec.initASt (Z := Unit)) ∧
    SInv.CurYieldNone (Fl4Spec.initASt (Z := Unit)) :=
  ⟨SInv.boot_yieldBlock, SInv.boot_curYieldNone⟩

theorem blk_of_code {ts : Fl4Spec.ThreadState} (h : tsCode ts = 3 ∨ tsCode ts = 4 ∨ tsCode ts = 5 ∨ tsCode ts = 6) :
    ¬ SInv.notBlkSt ts := by
  cases ts <;> simp_all [tsCode, SInv.notBlkSt]

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **A blocked thread's `YIELD_TO` word is 0** at a joint state carrying YieldBlock. -/
theorem JAtZ.yield0_blk (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hY : SInv.YieldBlockS σ) {d : U64}
    (hd : d ∈ Z.T) (hs : (L.mem s (tStA d)).val = 3 ∨ (L.mem s (tStA d)).val = 4 ∨ (L.mem s (tStA d)).val = 5 ∨
      (L.mem s (tStA d)).val = 6) : L.mem s (Fl4Proofs.P1.yieldA d) = 0#u64 := by
  obtain ⟨x, hk, hr⟩ := J.xtop.ipc.tcb d hd
  rw [hr.st] at hs
  have hb := blk_of_code hs
  have hn : x.tcbYieldTo = none := by
    by_contra hne
    exact hb (hY _ x hk hne)
  obtain ⟨x', hk', hy⟩ := J.yld.tcb d hd
  rw [hk] at hk'
  cases hk'
  rw [hn] at hy
  unfold optRef at hy
  by_contra h0
  rw [if_neg h0] at hy
  cases hy

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **The reachable joint states with YieldBlock** (module docstring). -/
abbrev JReachYB (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  JReachU17 (L := L) arI AR MR s a σ ∧ SInv.YieldBlockS σ ∧ SInv.CurYieldNone σ

variable {arI AR MR} in
theorem JReachYB.toY {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : JReachYB (L := L) arI AR MR s a σ) :
    JReachY (L := L) arI AR MR s a σ :=
  ⟨h.1, h.2.1.scope, h.2.2⟩

set_option maxHeartbeats 4000000 in
/-- **YieldBlock at every reachable joint state and every kernel exit** (module docstring). Same premises as
`kernel_entry_reachU29`. -/
theorem kernel_entry_yieldScope2U29 [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachYB (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ SInvX σ ∧ SInv.YieldBlockS σ ∧ SInv.CurYieldNone σ ∧
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
          JReachYB (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
        KFinEv13 (L := L) arI AR .interrupt (KFrontI (st := st) arI s a1 w) σ →
        syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∃ σ', RJ (L := L) arI AR r.1 r.2 σ' ∧
          JReachYB (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
        KFinEv13 (L := L) arI AR (.userLevelFault n.bv c.bv) (KFrontF2 (st := st) arI (brU (st := st) arI n c) s a) σ →
        syscall.handle_user_exception st arI s a n c ⦃ r => ∃ σ', RJ (L := L) arI AR r.1 r.2 σ' ∧
          JReachYB (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (ad c : U64) (ft : Fl4Spec.VMFaultType), σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
        KFinEv13 (L := L) arI AR (.vmFaultEvent ft) (KFrontF2 (st := st) arI (brV (st := st) arI ad c) s a) σ →
        syscall.handle_vm_fault st arI s a ad c ⦃ r => ∃ σ', RJ (L := L) arI AR r.1 r.2 σ' ∧
          JReachYB (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (v : U64), σ.curThread ≠ σ.idleThread → v.val < 256 →
        (∀ ev, KEvSpec (.trap v) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontTrap (st := st) arI s a) w.2) →
        syscall.handle_trap_syscall st arI s a v ⦃ r => ∃ σ', RJ (L := L) arI AR r.1 r.2 σ' ∧
          JReachYB (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n : I64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
        (∀ ev, KEvSpec (.sysU n) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontSysU (st := st) arI n s a) w.2) →
        syscall.handle_syscall st arI s a n ⦃ r => ∃ σ', RJ (L := L) arI AR r.1 r.2 σ' ∧
          JReachYB (L := L) arI AR MR r.1 r.2 σ' ⦄) := by
  obtain ⟨hJ, hY, hC⟩ := hJ
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, -, -, -, -, -, -, hSys, hIrq, hUs, hVm, hTr, hSU⟩ :=
    kernel_entry_reachU29 arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
  have huf : ∀ (w1 w2 : Fl4Spec.Word), (Fl4Spec.Event.userLevelFault w1 w2) ≠ .interrupt := by intro _ _ h; cases h
  have hvf : ∀ (ft : Fl4Spec.VMFaultType), (Fl4Spec.Event.vmFaultEvent ft) ≠ .interrupt := by intro _ h; cases h
  have hus : ∀ (w1 w2 : Fl4Spec.Word) c, (Fl4Spec.Event.userLevelFault w1 w2) ≠ .syscallEvent c := by
    intro _ _ c h; cases h
  have hvs : ∀ (ft : Fl4Spec.VMFaultType) c, (Fl4Spec.Event.vmFaultEvent ft) ≠ .syscallEvent c := by
    intro _ c h; cases h
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, hY, hC, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n c hct hn hfl hK hDL hFin
    refine WP.spec_mono (hSys n c hct hn hfl hK hDL hFin) ?_
    rintro r ⟨σ', hm, hRJ, -, -, -, -, -, -, hJR⟩
    obtain ⟨hF, hE⟩ := SInvX.ftEntry hX hct
    exact ⟨σ', hRJ, hJR, SInv.kentry_yieldBlock true c hY hC hF hE _ hm⟩
  · intro w a1 hIh hE
    refine WP.spec_mono (hIrq w a1 hIh hE) ?_
    rintro r ⟨σ', hEv, hRJ, -, -, -, -, -, hJR⟩
    exact ⟨σ', hRJ, hJR, SInv.kirq_yieldBlock true hY hC _ hEv⟩
  · intro n c hct hU hE
    refine WP.spec_mono (hUs n c hct hU hE) ?_
    rintro r ⟨σ', hEv, hRJ, -, -, -, -, -, hJR⟩
    obtain ⟨hF, hE⟩ := SInvX.ftEntry hX hct
    exact ⟨σ', hRJ, hJR, SInv.kcall_yieldBlock true _ (huf _ _) (hus _ _) hY hC hF hE _ hEv⟩
  · intro ad c ft hct hV hE
    refine WP.spec_mono (hVm ad c ft hct hV hE) ?_
    rintro r ⟨σ', hEv, hRJ, -, -, -, -, -, hJR⟩
    obtain ⟨hF, hE⟩ := SInvX.ftEntry hX hct
    exact ⟨σ', hRJ, hJR, SInv.kcall_yieldBlock true _ (hvf _) (hvs _) hY hC hF hE _ hEv⟩
  · intro v hct hv hE
    refine WP.spec_mono (hTr v hct hv hE) ?_
    rintro r ⟨ev, σ', hK, ⟨w, hw, hEv⟩, hRJ, -, -, -, -, -, hJR⟩
    obtain ⟨hF, hE⟩ := SInvX.ftEntry hX hct
    exact ⟨σ', hRJ, hJR, SInv.kcallF_yieldBlock true ev (KEvSpec.true_not_irq hK) hK.not_sys hY hC hF hE w hw _ hEv⟩
  · intro n hct hU hND hE
    refine WP.spec_mono (hSU n hct hU hND hE) ?_
    rintro r ⟨ev, σ', hK, ⟨w, hw, hEv⟩, hRJ, -, -, -, -, -, hJR⟩
    obtain ⟨hF, hE⟩ := SInvX.ftEntry hX hct
    exact ⟨σ', hRJ, hJR, SInv.kcallF_yieldBlock true ev (KEvSpec.true_not_irq hK) hK.not_sys hY hC hF hE w hw _ hEv⟩

end

end

end Fl4Proofs.P3.SInvR.G5
