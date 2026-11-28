/-
P3 (p3J gen 49): **`DispStabFootLzw.midSpec` (`MidSpecAt`) proved; top `kernel_entry_runMcWKR_sysLzx` with
`DispStabFootLzx` [J] = {midRecvSw}**.

`MidSpecAt σ` (P3JMidCls) asks, at every dispatch state `σb` of the entry (`BudgetAt σ σb true`) with `CKI`, for
every cap pointer, `MidStF` at every `ok` outcome `y` of the spec's first phase
`fl4HandleInvocationR true false false true true cptr`. Its six fields, each from an existing proof:
* the first phase's queue / action fact (`CQ ct`: ct current, runnable without a fault, in no ready queue, no
  switch to it pending) at `y.2`: XTopJointMidRunQ's **`midRunQ_shell`** from `CQ ∧ NQ` at `σb` and
  `JMidPerfHypQ` [W] at `σb`, which is XTopJointPerfI's **`jMidPerfHypQ_of2`** from `JPerfRegHyp` and
  `JPerfIrqSlotHyp` (the IRQ handler set / clear of the first phase included), both XTopJointKEntry27b's
  **`jPerfRegHyp_27b`** / **`jPerfIrqSlotHyp_27b`** from `SInvB σ` (the non-stable chain's discharge,
  KEntry27b; StPostRRTop uses it the same way). This gives `nq`, `nsw`, `run` (`CurRun`: the current thread is
  `ct` with its TCB runnable).
* `CQ ∧ NQ` at `σb`: **`midEntry_disp`** (new) — `MidEntry σ` by XTopJointMidRunS's `JAtZ.midEntry` at the entry
  state (`Entered σ` by `SInvX.entered`, the no-fault fact by `SInvAll.sinvB_disp` at `σ` itself), moved to `σb`
  through the `FaultIP` register write (`BudgetAt.shape27`: `σb`'s heap is `σ`'s with ct's TCB register-updated;
  ready queues, current thread unchanged), the no-fault fact at `σb` by `sinvB_disp`, the action by
  `BudgetAt.entered`.
* `ni`: `y.2.curThread = σb.curThread` (`CQ`), `y.2.idleThread = σb.idleThread` (SpecInvSgI6's
  `idk_fl4HandleInvocationR`), `Entered σb`.
* `vfh`: XTopJointKEntry27b's **`jMidVfhHyp_27b`** (`JMidVfhHyp` [J] discharged there from `SInvB σ`).
* `cki`: P3JCkS's **`ck_handleInvocationR`**.

* **`midSpecAt_of`**: `MidSpecAt σ` from `JAtZ … s a σ`, `SInvX σ`, `σ.curThread ≠ σ.idleThread`.
* **`DispStabFootLzx` [J]** {midRecvSw — `DispStabFootLzw`'s, verbatim}; **`dispStabFootLzw_of_Lzx`**
  (`midSpec` by `midSpecAt_of`, `SInvX` from `RunMcWKR` by `jreach_invU3`), **`dispStabFootLzx_of_Lzw`**
  (unconditional); top **`kernel_entry_runMcWKR_sysLzx`** (globals verbatim as `_sysLzw`, `KNo88` [S] as there:
  transitional, over-wide [S]; the proper native scope, via `LookAt`, excludes only entries whose invoked slot
  holds a Thread cap with label = 88).

Premise honesty: `DispStabFootLzx` is `DispStabFootLzw` without `midSpec` (implied by it); with the globals
(`hnd`) it implies it. Nothing weakened.

Named premises: `DispStabFootLzx` [J], `KNo88` [S] (P3JEptScope); globals as `_sysLzw`. No sorry. New module; no
existing statement changed.

(p3J gen 58) P3JEptScope removed with `KNo88` / `DispStabFootLzw` / `_sysLzw`; its three declarations still
used by the `_sysLzz` chain (`thHard20_ept`, `decThEptMidSt`, `midDecStWL29`: P3JLookFlat `invDecFlat` /
`midDecRestLn_of`) moved here verbatim, with P3JEptScope's import.
-/
import Fl4Proofs.P3.P3JSspSt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

/-- (p3J gen 48) **The Thread labels left after SetSchedParams are exactly `TCBSetEPTRoot`** (module docstring). -/
theorem thHard20_ept {l : U64} (h : ThHard20 l) : l = fl4_abi.label.TCBSetEPTRoot := by
  obtain ⟨h, n8⟩ := h
  obtain ⟨h, nI⟩ := h
  obtain ⟨h, n11⟩ := h
  obtain ⟨h, n22⟩ := h
  obtain ⟨h, n2⟩ := h
  obtain ⟨h, n17⟩ := h
  obtain ⟨h, n4⟩ := h
  obtain ⟨h, n3⟩ := h
  obtain ⟨h, n24⟩ := h
  obtain ⟨h, n13⟩ := h
  obtain ⟨h, n12⟩ := h
  obtain ⟨h, n6⟩ := h
  obtain ⟨h, n23⟩ := h
  obtain ⟨h, n21⟩ := h
  obtain ⟨h, n19⟩ := h
  obtain ⟨h, n14⟩ := h
  obtain ⟨h, nB⟩ := h
  obtain ⟨h, n7⟩ := h
  obtain ⟨h, nT⟩ := h
  rcases h with hr | he
  · exfalso
    have v : ∀ k : U64, l ≠ k → l.val ≠ k.val := fun k hk hv => hk (UScalar.eq_of_val_eq hv)
    have a8 := v _ n8
    have a9 := v _ (fun e => nI (Or.inl e))
    have a10 := v _ (fun e => nI (Or.inr (Or.inl e)))
    have a5 := v _ (fun e => nI (Or.inr (Or.inr e)))
    have a11 := v _ n11
    have a22 := v _ n22
    have a2 := v _ n2
    have a17 := v _ n17
    have a4 := v _ n4
    have a3 := v _ n3
    have a24 := v _ n24
    have a13 := v _ n13
    have a12 := v _ n12
    have a6 := v _ n6
    have a23 := v _ n23
    have a21 := v _ n21
    have a19 := v _ n19
    have a14 := v _ n14
    have a16 := v _ (fun e => nB (Or.inl e))
    have a18 := v _ (fun e => nB (Or.inr e))
    have a7 := v _ n7
    have a15 := v _ (fun e => nT (Or.inl e))
    have a20 := v _ (fun e => nT (Or.inr e))
    simp [fl4_abi.label.TCBSetSchedParams, fl4_abi.label.TCBSetTimeoutEndpoint, fl4_abi.label.TCBSetIPCBuffer,
      fl4_abi.label.TCBConfigure, fl4_abi.label.TCBSetSpace, fl4_abi.label.TCBWriteFPU,
      fl4_abi.label.TCBReadRegisters, fl4_abi.label.TCBGetBreakpoint, fl4_abi.label.TCBCopyRegisters,
      fl4_abi.label.TCBWriteRegisters, fl4_abi.label.TCBSetTimer, fl4_abi.label.TCBResume,
      fl4_abi.label.TCBSuspend, fl4_abi.label.TCBSetPriority, fl4_abi.label.TCBReadFPU,
      fl4_abi.label.TCBSetFlags, fl4_abi.label.TCBConfigureSingleStepping,
      fl4_abi.label.TCBBindNotification, fl4_abi.label.TCBSetBreakpoint, fl4_abi.label.TCBUnsetBreakpoint,
      fl4_abi.label.TCBSetMCPriority, fl4_abi.label.TCBUnbindNotification, fl4_abi.label.TCBSetTLSBase]
      at a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    omega
  · exact he

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 48) **The Thread cap's first-phase decode at a dispatch state at `TCBSetEPTRoot`** (module docstring):
FL4 and the spec both return `InvalidCapability 0`, the state unchanged (P3JThIll's `decThIllSt`, first-phase
branch). -/
theorem decThEptMidSt [VxE Z] {V' : XVs} {Ac' : Set U64} {Lst' : U64 → List U64}
    {D' : Set U64} {s' : S} {a' : A} {σb : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb)
    (hMb : MR a' σb.machineState) {ct : U64} (hct : sched.cur_thread st s' = ok ct)
    {info : msginfo.MessageInfo} {mi : Fl4Spec.MessageInfo} {buf : U64} {buffer : Option Fl4Spec.ObjRef}
    {r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault}
    {er : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr))}
    (hinfo : msg.msg_info st s' ct = ok info)
    (hmi : Fl4Spec.getMessageInfo (Z := Unit) ct.bv σb = ({(mi, σb)}, False))
    (hbuf : msg.lookup_ipc_buffer st s' false ct = ok buf)
    (hbuffer : Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σb = ({(buffer, σb)}, False))
    (hr2 : ipc.lookup_extra_caps st s' ct buf info = ok r2)
    (her : (Fl4Spec.lookupExtraCaps (Z := Unit) ct.bv buffer mi).run σb = ({(er, σb)}, False))
    (sl : Fl4Spec.CslotPtr) {p : U64}
    (e : Aeneas.Std.Array obj.Slot 3#usize) (exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hl : info.label = fl4_abi.label.TCBSetEPTRoot) (args : List Fl4Spec.Data) (bl call don : Bool)
    (ci : Fl4Spec.CapRef) :
    XCapP (L := L) arI (MidX (L := L) arI AR MR Z H Cs s') (MidXP (L := L) arI AR MR Z H Cs s') s' a' σb
      info.label (msgLen info buf) (cslotAddr sl) (.Thread p) bl call don true buf e mi.miLabel
      args ci sl exs buffer ct := by
  have h88 : info.label.val = 88 := by rw [hl]; exact lbl_ept_val
  have hX0 : (JStab (L := L) arI AR (Z.mv Z.G V') H Cs s' a' σb ∧
      P1.WritesIn st s' s' (Mc.ProjW (L := L) H Cs s')) ∧ MR a' σb.machineState :=
    ⟨⟨J.stab, P1.WritesIn.refl _ _⟩, hMb⟩
  refine XCapP.monoX (X := fun s1 a1 σ1 => (JStab (L := L) arI AR (Z.mv Z.G V') H Cs s1 a1 σ1 ∧
      P1.WritesIn st s' s1 (Mc.ProjW (L := L) H Cs s')) ∧ MR a1 σ1.machineState) ?_
    fun _ _ _ ⟨⟨hJ, hw⟩, hm⟩ => ⟨JStab.mv hJ, hm, hw⟩
  obtain ⟨hLb, -⟩ := J.frontJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hr2 her
  rw [← hLb]
  obtain ⟨sl', hlbl, -, hd⟩ := tcb_canon info.label
  refine XCapP.lbl_congr arI (specDec_thread p hd) ?_
  have hl5 : info.label.val ≠ 5 ∧ info.label.val ≠ 8 ∧ info.label.val ≠ 9 ∧ info.label.val ≠ 10 ∧
      info.label.val ≠ 11 := ⟨by omega, by omega, by omega, by omega, by omega⟩
  refine XCap.toPN arI ?_ (thread_noPre_of hlbl hl5)
  left
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  simp only [↓reduceIte]
  rw [WP.spec_ok]
  exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, hX0⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 48) **`MidDecStWL` at `KW ∧ IsRestCap29`, proved** (module docstring: the mid class at Thread @ 88
is a first-phase error on both sides). -/
theorem midDecStWL29 [VxE Z] {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall} :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap29 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  obtain ⟨-, hW⟩ := hW
  cases cp
  case Thread p => exact decThEptMidSt J hMb hct a1 a2 a3 a4 a5 a6 sl e exs (thHard20_ept hW) _ _ _ _ _
  all_goals exact False.elim hW

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 49) **`CQ ∧ NQ` of the current thread at a dispatch state, from the entry state** (module
docstring). -/
theorem midEntry_disp (hnd : Fl4Spec.numDomains = 1) {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ σb : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hX : SInvX σ) (hct : σ.curThread ≠ σ.idleThread)
    (hBA : BudgetAt σ σb true) :
    Entered σb ∧ MidRun.CQ σb.curThread σb ∧ MidRun.NQ σb.curThread σb := by
  have hS := hX.sb
  have hni : Entered σ := hX.entered hct
  obtain ⟨x0, hk0, -⟩ := hS.1.2
  obtain ⟨-, ek, ect, -, -, eq0⟩ := BudgetAt.shape27 hnd hk0 hBA
  have ek' : σb.kheap = Function.update σ.kheap σ.curThread
      (some (.tcb (Notif.setReg x0 .faultIP (x0.tcbArch.tcbContext.userRegs .nextIP - 2)))) := ek
  obtain ⟨-, hnfb⟩ := SInvAll.sinvB_disp (x' := Notif.setReg x0 .faultIP (x0.tcbArch.tcbContext.userRegs .nextIP - 2))
    hS hct hk0 rfl rfl ek' ect
  have ek0 : σ.kheap = Function.update σ.kheap σ.curThread (some (.tcb x0)) := by
    rw [← hk0]; exact (Function.update_eq_self _ _).symm
  obtain ⟨-, hnf0⟩ := SInvAll.sinvB_disp (σb := σ) (x' := x0) hS hct hk0 rfl rfl ek0 rfl
  have hME := J.midEntry hni hnf0
  have hnib : Entered σb := BudgetAt.entered hnd hk0 hni hBA
  have hxb : ∀ x, σb.kheap σb.curThread = some (.tcb x) →
      x = Notif.setReg x0 .faultIP (x0.tcbArch.tcbContext.userRegs .nextIP - 2) := by
    intro x hx
    rw [ek', ect, Function.update_self] at hx
    simp only [Option.some.injEq, Fl4Spec.KernelObject.tcb.injEq] at hx
    exact hx.symm
  refine ⟨hnib, ⟨⟨rfl, fun x hx => ⟨?_, hnfb x hx⟩⟩, ?_, ?_⟩, ?_⟩
  · obtain rfl := hxb x hx
    exact hME.run x0 hk0
  · rw [ect, eq0]; exact hX.ctQ
  · rw [hnib.2]; intro e; cases e
  · intro p n q hp hq
    by_cases e : p = σ.curThread
    · subst e
      rw [ek', Function.update_self] at hp
      simp at hp
    · rw [ek', Function.update_of_ne e] at hp
      rw [ect]
      exact hME.nq p n q hp hq

set_option maxHeartbeats 4000000 in
/-- (p3J gen 49) **`MidSpecAt` proved** (module docstring): from the entry state's `JAtZ`, `SInvX` and a
non-idle current thread. -/
theorem midSpecAt_of (hnd : Fl4Spec.numDomains = 1) {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hX : SInvX σ) (hct : σ.curThread ≠ σ.idleThread) :
    MidSpecAt σ := by
  intro σb hBA hCb cptr y hy hok
  have hS := hX.sb
  obtain ⟨hnib, hcq, hnqb⟩ := midEntry_disp hnd J hX hct hBA
  have hPQ : MidRun.JMidPerfHypQ true cptr σb :=
    MidRun.jMidPerfHypQ_of2 hcq hnqb (jPerfRegHyp_27b hnd hS hct hBA cptr) (jPerfIrqSlotHyp_27b hnd hS hBA cptr)
  obtain ⟨⟨hcy, hrs⟩, hrq, hsw⟩ := MidRun.midRunQ_shell true true cptr σb hcq hnqb hPQ y hy
  have hid : y.2.idleThread = σb.idleThread :=
    SInvG.idk_fl4HandleInvocationR (N := σb.idleThread) true false false true true cptr σb rfl y hy
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcy, hid]; exact hnib.1
  · rw [hcy]; exact hrq
  · exact jMidVfhHyp_27b hnd hS hBA cptr y hy hok
  · exact SInvCk.ck_handleInvocationR true false false true true cptr σb hCb y hy
  · intro x hx
    rw [hcy] at hx
    exact (hrs x hx).1
  · rw [hcy]; exact hsw

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- (p3J gen 49) **`DispStabFootLzx` [J]**: `DispStabFootLzw` without `midSpec` (module docstring). -/
structure DispStabFootLzx (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- `DispStabFootLzw.midRecvSw`, verbatim. -/
  midRecvSw : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidRecvSw (L := L) arI AR MR Z H Cs s a σ n c

variable {arI AR MR}

end

end

end Fl4Proofs.P3.Mc
