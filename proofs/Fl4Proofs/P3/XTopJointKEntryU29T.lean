/-
P3 (FL4 #94 / #97, KENTRY-PLAN lt1): **the local timer entries beside the serial gate**:
`kernel_entry_reachU29T` (accepted) and `kernel_entry_reachU29TD` (declined).

fl4-sync's `local_set_timer` runs `localtimer.handle_set_timer_local … number target` with the
`target` its locked lookup of the caller's `CAP` register found (`lookup_slot_locked`, one
`localtimer.cspace_step` per level); `local_timer_irq` runs `localtimer.handle_timer_irq_local …
irq p` with the plan `plan_timer_irq` returned.

* **Accepted `TCB_SetTimer`** (P1 `set_timer_local_same`): the general entry
  `handle_syscall … SysCall` from the same state. Inputs of the clause: U29's syscall clause's own,
  and **fl4-sync's contract** that the general CSpace lookup of the `CAP` register, at the entry
  state, finds a slot holding `Thread target` (fl4-sync's walk is that lookup, level by level, with
  the slots it reads locked; the contract is an input of the entry like lcv's plan and lcs's
  `found`, not a state premise). `target ∈ T` is derived (`JAtZ.threadCapT`: the cap is in a slot
  of `Z.th`, `SlotsValid` types it).
* **Accepted timer interrupt** (P1 `irq_local_same`): `handle_interrupt_entry` from the same
  state, for any plan (the plan only narrows when it runs). Inputs: U29's interrupt clause's own.
* **Declined** (`kernel_entry_reachU29TD`): lcd's `kernel_entry_reachU29D` (its five entries,
  unchanged) and the two new entries. `TCB_SetTimer` declines as the other syscall-type entries
  (`set_timer_local_decline`: entry state or `LocalPre` with `RoT`), so `DeclSysU29` (`declSys_of`).
  The interrupt entry declines at the entry state (U29's interrupt clause at `(s, a, σ)` for the
  run from `(s, a1)`) or after one `update_timestamp` (`irq_local_decline`); then the general
  entry runs as from the entry state with the Arch value the update left (`irq_pre_same`), and
  the clause holds at the reachable joint state `(s, a0, tick σ)` (`arI.now a = ok (n0, a0)`,
  `jreachU17_tick`) for the run from `(s, a')` (`DeclIrqU29`). As in U29 the clause takes the
  hardware fact `IrqHw` of the entry as an input, here at `tick σ` (the interrupt's line read and
  the one extra clock reading, in the spec's order: `tick` first).

Premises added to either top: none (U29's verbatim). No existing top statement changed.
-/
import Fl4Proofs.P3.XTopJointKEntryU29D
import Fl4Proofs.P3.XTopJointKEntryRRF
import Fl4Proofs.P1.LocalTimer
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **A thread cap the current thread's lookup finds names a TCB of `H`** (`SlotsValid` at the
found slot of `Z.th`). -/
theorem JAtZ.threadCapT {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t c p : U64} {r : cspace.Resolved} (et : sched.cur_thread st s = ok t)
    (h : cspace.lookup_slot st s t c = ok (core.result.Result.Ok r))
    (hc : obj.Slot.cap st r.slot s = ok (capability.Cap.Thread p)) : p ∈ P1.Heap.tcbs H := by
  have htcb := J.curW_tcb et
  have hR := J.xtop.rel.2.1.1
  have hV := J.xtop.rel.2.1.2.1
  have HL := lookup_slot_refines Z.th s σ hR hV t htcb c
  rw [h, WP.spec_ok] at HL
  obtain ⟨e, -, hrel, hok⟩ := HL
  cases e with
  | ok v =>
    obtain ⟨sl, rest⟩ := v
    obtain ⟨hsl, -⟩ := hrel
    obtain ⟨pp, hp, hth, -⟩ := hok
    have hca : capAt (L.mem s) (cslotAddr sl) = ok (capability.Cap.Thread p) := by
      rw [← hsl, ← slot_cap_eq]; exact hc
    have hv : Z.th p = some .tcb := hV.abs ⟨pp, hp, Or.inl hth⟩ hca
    exact J.zH.1 p (J.thT p hv)
  | error _ => exact hrel.elim

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

/-- **fl4-sync's `TCB_SetTimer` contract** (an input of the entry): at the entry state the general
CSpace lookup of the current thread's `CAP` register finds a slot holding `Thread target`. -/
def SetTimerFound (s : S) (target : U64) : Prop :=
  ∀ t, sched.cur_thread st s = ok t → ∃ r : cspace.Resolved,
    cspace.lookup_slot st s t (L.mem s (regA t layout.reg.CAP)) = ok (core.result.Result.Ok r) ∧
    obj.Slot.cap st r.slot s = ok (capability.Cap.Thread target)

/-- **U29's interrupt clause** (its text) at `(s, a, σ)` for the line `w`, the Arch value `a1` the
interrupt was taken at, and the run `R`. -/
def IrqClU29 (s : S) (a : A) (σ : Fl4Spec.State Unit) (w : U64) (a1 : A) (R : Result (S × A)) : Prop :=
  IrqHw AR MR a a1 σ w → KFinEv13 (L := L) arI AR .interrupt (KFrontI (st := st) arI s a1 w) σ →
    R ⦃ r => ∃ σ', EvOut false .interrupt σ σ' ∧
      RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
      SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU17 (L := L) arI AR MR r.1 r.2 σ' ⦄

/-- **A declined timer-interrupt entry ending at `(s', a')`** (taken at `a1`): declined before any
write, U29's interrupt clause at `(s, a, σ)` for the general run from `(s', a') = (s, a1)`; or after
its clock reading, the clause at the reachable `(s, a0, tick σ)` (`arI.now a = ok (n0, a0)`) for
the general run from `(s', a')`. -/
def DeclIrqU29 (s : S) (a : A) (σ : Fl4Spec.State Unit) (w : U64) (a1 : A) (s' : S) (a' : A) : Prop :=
  (s' = s ∧ a' = a1 ∧
    IrqClU29 (L := L) arI AR MR s a σ w a1 (syscall.handle_interrupt_entry st arI s' a' w)) ∨
  (∃ n0 a0, arI.now a = ok (n0, a0) ∧
    IrqClU29 (L := L) arI AR MR s a0 (Fl4Spec.fl4ClockTick σ) w a' (syscall.handle_interrupt_entry st arI s' a' w))

set_option maxHeartbeats 8000000 in
/-- **The local timer entries beside the serial gate, accepted** (module docstring):
`kernel_entry_reachU29`'s syscall clause for `handle_set_timer_local … n target` (with fl4-sync's
`SetTimerFound` contract) and its interrupt clause for `handle_timer_irq_local … w p` (any plan),
on the runs that return `true`. U29's premises verbatim. -/
theorem kernel_entry_reachU29T [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
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
      (∀ (n : I64) (c : Fl4Spec.Syscall) (target : U64), σ.curThread ≠ σ.idleThread → NativeSys n c →
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
        SetTimerFound (L := L) s target →
        localtimer.handle_set_timer_local st arI s a n target ⦃ r => r.1 = true →
          ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
            RJ (L := L) arI AR r.2.1 r.2.2 σ' ∧ SInvX σ' ∧ MR r.2.2 σ'.machineState ∧
            SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ SInvUZ.UtPgR σ' ∧
            JReachU17 (L := L) arI AR MR r.2.1 r.2.2 σ' ⦄) ∧
      (∀ (w : U64) (a1 : A) (p : localtimer.TimerIrqPlan), IrqHw AR MR a a1 σ w →
        KFinEv13 (L := L) arI AR .interrupt (KFrontI (st := st) arI s a1 w) σ →
        localtimer.handle_timer_irq_local st arI s a1 w p ⦃ r => r.1 = true → ∃ σ', EvOut false .interrupt σ σ' ∧
          RJ (L := L) arI AR r.2.1 r.2.2 σ' ∧ SInvX σ' ∧ MR r.2.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU17 (L := L) arI AR MR r.2.1 r.2.2 σ' ⦄) := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, -, -, -, -, -, -, -, hSys, hIrq, -⟩ :=
    kernel_entry_reachU29 arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
  refine ⟨Z, H, Cs, Ac, Lst, D, J, fun n c target hct hn hflag hK hDL hFin hF => ?_,
    fun w a1 p hw hfin => ?_⟩
  · have htg : target ∈ P1.Heap.tcbs H := by
      have et := cur_thread_curW (L := L) (st := st) s
      obtain ⟨r, er, ecr⟩ := hF _ et
      exact J.threadCapT et er ecr
    exact P1.set_timer_local_triple arI hA J.bxi (fun _ et => J.cnOff et) hflag hF htg
      (hSys n c hct hn hflag hK hDL hFin)
  · exact P1.irq_local_triple arI hA (hIrq w a1 hw hfin)

set_option maxHeartbeats 8000000 in
/-- **A declined timer-interrupt entry** (the entry state, or one `update_timestamp`): `DeclIrqU29`. -/
theorem declIrq_of [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ)
    {w : U64} {a1 : A} {s' : S} {a' : A}
    (hd : (s' = s ∧ a' = a1) ∨ sched.update_timestamp st arI s a1 = ok (s', a')) :
    DeclIrqU29 (L := L) arI AR MR s a σ w a1 s' a' := by
  rcases hd with ⟨rfl, rfl⟩ | hu
  · obtain ⟨_, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hIrq, -⟩ :=
      kernel_entry_reachU29 arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
    exact Or.inl ⟨rfl, rfl, fun hw hfin => hIrq w _ hw hfin⟩
  · obtain ⟨Z0, H0, Cs0, Ac0, Lst0, D0, J0, -⟩ := jreach_invU3 hnd hJ.1
    obtain ⟨-, hN, -⟩ := P1.BXI.tcbNode J0.bxi
    obtain ⟨⟨n0, a0⟩, hn, -⟩ := P1.spec_ex_fd (hA.now a)
    have hJ' := jreachU17_tick hnd hARI hM hJ hn
    obtain ⟨_, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hIrq, -⟩ :=
      kernel_entry_reachU29 arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ'
    have e := P1.irq_pre_same arI hSX hA hN hu w
    dsimp only at e
    refine Or.inr ⟨n0, a0, hn, fun hw hfin => ?_⟩
    rw [e]; exact hIrq w a' hw hfin

set_option maxHeartbeats 8000000 in
/-- **`kernel_entry_reachU29D` with the local timer entries** (module docstring): lcd's five
declined entries (`kernel_entry_reachU29D`, unchanged), a declined `handle_set_timer_local`
(`DeclSysU29`, as the other syscall-type entries) and a declined `handle_timer_irq_local`
(`DeclIrqU29`). U29's premises verbatim, nothing added. -/
theorem kernel_entry_reachU29TD [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ) :
    (∀ (ad c : U64), syscall.handle_vm_fault_local st arI s a ad c ⦃ r =>
      r.1 = false → DeclVmU29 (L := L) arI AR MR s a σ ad c r.2.1 r.2.2 ⦄) ∧
    (∀ (n : I64) (found : U64 × U64), syscall.handle_syscall_local st arI s a n found ⦃ r =>
      r.1 = false → DeclSysU29 (L := L) arI AR MR s a σ n r.2.1 r.2.2 ⦄) ∧
    (∀ (found : U64 × U64), syscall.handle_reply_recv_vm_local st arI s a found ⦃ r =>
      r.1 = false → DeclSysU29 (L := L) arI AR MR s a σ fl4_abi.syscall.SysReplyRecv r.2.1 r.2.2 ⦄) ∧
    (∀ (n : I64), syscall.handle_ioport_local st arI s a n ⦃ r =>
      r.1 = false → DeclSysU29 (L := L) arI AR MR s a σ n r.2.1 r.2.2 ⦄) ∧
    (∀ (n : I64) (p : localinv.Plan), syscall.handle_invocation_local st arI s a n p ⦃ r =>
      r.1 = false → DeclSysU29 (L := L) arI AR MR s a σ n r.2.1 r.2.2 ⦄) ∧
    (∀ (n : I64) (target : U64), localtimer.handle_set_timer_local st arI s a n target ⦃ r =>
      r.1 = false → DeclSysU29 (L := L) arI AR MR s a σ n r.2.1 r.2.2 ⦄) ∧
    (∀ (w : U64) (a1 : A) (p : localtimer.TimerIrqPlan), localtimer.handle_timer_irq_local st arI s a1 w p ⦃ r =>
      r.1 = false → DeclIrqU29 (L := L) arI AR MR s a σ w a1 r.2.1 r.2.2 ⦄) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    kernel_entry_reachU29D arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
  refine ⟨h1, h2, h3, h4, h5, fun n target => ?_, fun w a1 p => ?_⟩
  · obtain ⟨⟨b, s', a'⟩, e, -⟩ :=
      P1.spec_ex_fd (P0.localtimer.handle_set_timer_local.p0 st arI s a n target L.total hA)
    rw [e, WP.spec_ok]
    intro hb
    simp only at hb
    subst hb
    exact declSys_of arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
      (P1.set_timer_local_decline arI e)
  · obtain ⟨⟨b, s', a'⟩, e, -⟩ :=
      P1.spec_ex_fd (P0.localtimer.handle_timer_irq_local.p0 st arI s a1 w p L.total hA)
    rw [e, WP.spec_ok]
    intro hb
    simp only at hb
    subst hb
    exact declIrq_of arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
      (P1.irq_local_decline arI e)

end

end

end Fl4Proofs.P3.SInvR.G5
