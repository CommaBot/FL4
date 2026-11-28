/-
P3 (p3J gen 35): **the invoking class (Send / NBSend / Call) of the syscall clause reduced to its per-cap decode
leaf** (the stable invoke skeleton with footprint, gen 32/33's mid skeleton for `handle_invocation call bl don
false` on the CAP register, then `after_invocation`).

* **`InvDecSt` [J]**: at every dispatch state of the entry (as `DispStabFootAt`) and every number `n` of the class
  with its flags (`InvSys n call bl don`), for the front reads and every slot / cap the lookup can find (P3JMidInv's
  `MidDecSt` binder chain), the decode leaf `XCapP (MidX …) (MidXP …)` of the cap at `blocking = bl`,
  `is_call = call`, `can_donate = don`, `first_phase = false` (P3JMidInv's `MidX` / `MidXP`: `JStab Z H Cs`, `MR`,
  footprint `ProjW H Cs s'`; the preempted half through `after_invocation`).
* **`invInvHI`**: the invocation at `MidX` / `MidXP` by XTopJointEntry's `handle_invocation_refinesMXP` in gen 33's
  `refine … ?_` shape. Leaves: the front reads (`JAtZ.frontEx`), the extra caps (`JAtZ.extraJ`) and the lookup
  fault (`capFaultCorr_lookup`) — with `blocking` these run `handle_fault`: StPostFault's `JAtZ.faultHypJZGSt`
  (stable), `MKD.faults_handle_fault` (`MR`), P3JMcFlt's `faultProjW` (footprint; the dispatch state is `Entered`,
  its current thread in no ready queue, its fault handler valid: `BudgetAt.entered`, `BudgetAt.shape27`,
  `SInvX.ctQ`, `sinvB_disp`); the success tail (StPostIoLeaf's `JAtZ.flTailJSt`, `MKD.fl_tail`, P3JInvFt's
  `flTailProjWc`); the error reply (StPostIoLeaf's `replyFailJSt`, `MKD.reply_err_tail`, P3JInvFt's
  `replyErrProjW` with `NoBufCap` by `noBufCap_cki`); the current thread kept (P3JMidInv's `midPK`); the decode by
  `InvDecSt`.
* `inv_afterSt`, `dispatch_invSt`, **`dispInv_stFt`**: `after_invocation` and the if-chain (XTopJointDispatch's
  `invoke_afterJ` / `dispatch_invokeJ` shape; `JStabR` by `JAtZ.toR`): the inv class of `DispStabFootAt` from
  `InvDecSt`.
* **`DispStabFootLi` [J]** {invDec, midDecRest, midSpec, midRecvSw}: P3JMidEp's `DispStabFootLn` with `inv`
  replaced by `invDec`; **`dispStabFootLn_of_Li`**, top **`kernel_entry_runMcWKR_sysLi`** (globals as `_sysLn`).

Premise honesty: `invDec` (`InvDecSt`) speaks of a sub-call of `inv`'s call (the decode and perform of the looked-up
cap inside `handle_invocation`); it implies `inv` (`dispInv_stFt`) and is **not implied by it**, exactly as gen 33's
`midDec` against `midInv`. Justification that it is not false on reachable states: it is `inv` with the proved
skeleton removed; the decode leaves are where the non-stable chain's per-cap premises sit (XTopJointKEntry23P's
`decOK_JMU`, every arm ending at `Z.mv G' V'` with the entry's `H` / `Cs` but the untyped retype, which `CKI`
excludes: no untyped cap is in any slot); the preempted arms are `MidXP` (the non-stable `JAtPreMV`); the footprint
of every non-retype decode lies in `ProjW` (P1's per-family footprints are `KW` / `IpcW` words of `H`'s objects).
Removed from the [J] content: the front reads, the lookup and its fault, the extra caps and their fault, the success
tail, the error reply and `after_invocation` of the invoking class.

Named premises: `InvDecSt` [J], `DispStabFootLi` [J]. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JInvFt
import Fl4Proofs.P3.P3JMidEp
import Fl4Proofs.P3.StPostIoLeaf
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 35) **The invocation and `after_invocation` at a dispatch state** (`invoke_afterJ`'s shape). -/
theorem inv_afterSt {V' : XVs} {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} {s' : S} {a' : A}
    {σb : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb) [VxE Z] {ct : U64}
    (hct : sched.cur_thread st s' = ok ct) {n : I64} {call bl don : Bool} (hn : InvSys n call bl don)
    (hInv : syscall.handle_invocation st arI s' a' call bl don false (L.mem s' (Endp.regA ct layout.reg.CAP)) ⦃ res =>
      HIPostMXP (L := L) (MidX (L := L) arI AR MR Z H Cs s') (MidXP (L := L) arI AR MR Z H Cs s') true σb
        call bl don false (Fl4Spec.toBl (L.mem s' (Endp.regA ct layout.reg.CAP)).bv) res ⦄) :
    (do
      let (r, s1, a1) ← syscall.handle_invocation st arI s' a' call bl don false (L.mem s' (Endp.regA ct layout.reg.CAP))
      let (_, s2, a2) ← syscall.after_invocation st arI s1 a1 r
      ok (s2, a2)) ⦃ r => SInvR.G5.DispPostSt (L := L) arI AR MR Z H Cs (invSysOf call bl) σb s' r ⦄ := by
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨-, xs, hks⟩ := J.xtop.curTcb hcur
  have hctT : ct ∈ (Z.mv Z.G V').T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hxs := (J.xtop.irelK J.ks J.buf).1.toE.at_tcb hctT hks
  have hcp : Fl4Spec.dataToCptr (xs.tcbArch.tcbContext.userRegs Fl4Spec.cap_register) =
      Fl4Spec.toBl (L.mem s' (Endp.regA ct layout.reg.CAP)).bv := by
    rw [← regIdx_cap, hxs.regs]; rfl
  have hk' : σb.kheap σb.curThread = some (.tcb xs) := by rw [hcur]; exact hks
  have hreg := mem_getCapReg hk' Fl4Spec.cap_register
  rw [hcp] at hreg
  have top : ∀ y, y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) true call bl don false
      (Fl4Spec.toBl (L.mem s' (Endp.regA ct layout.reg.CAP)).bv)).run σb).1 →
      y ∈ ((Fl4Spec.fl4HandleSyscall (Z := Unit) true (invSysOf call bl)).run σb).1 := fun y hy => by
    rw [fl4HandleSyscall_inv hn]; exact mem_bindE_ok (mem_liftE (ε := Unit) hreg) hy
  have hok : ∀ {α : Type} {x : α} {P : α → Prop}, P x → ok x ⦃ P ⦄ := fun h => by rw [WP.spec_ok]; exact h
  refine WP.spec_bind hInv ?_
  rintro ⟨r, s1, a1⟩ ⟨y, hy, hres, -, hXr⟩
  rcases hres with ⟨h1, hy1⟩ | ⟨h1, hy1⟩
  · dsimp only at h1 hXr; subst h1
    rw [if_neg (fun h => by cases h)] at hXr
    obtain ⟨⟨G1, V1, Ac1, Lst1, D1, J1⟩, hMm, hW1⟩ := hXr
    show (do
      let (_, s2, a2) ← syscall.after_invocation st arI s1 a1 (.Ok ())
      ok (s2, a2)) ⦃ _ ⦄
    rw [show syscall.after_invocation st arI s1 a1 (.Ok ()) = ok (true, s1, a1) by
      unfold syscall.after_invocation; rfl, bind_ok]
    exact hok ⟨⟨y, top y hy, Or.inl ⟨hy1, ⟨G1, V1, Ac1, Lst1, D1, J1.toR⟩, hMm⟩⟩, hW1⟩
  · dsimp only at h1 hXr; subst h1
    rw [if_pos rfl] at hXr
    obtain ⟨-, hAI⟩ := hXr
    refine WP.spec_bind hAI ?_
    rintro ⟨b, s2, a2⟩ ⟨-, ⟨z, hz, hJz, hMz⟩, hW2⟩
    exact hok ⟨⟨y, top y hy, Or.inr ⟨hy1, z, hz, hJz, hMz⟩⟩, hW2⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 35) **`dispatch_syscall` for the invoking class at a dispatch state** (`dispatch_invokeJ`'s
if-chain). -/
theorem dispatch_invSt {V' : XVs} {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} {s' : S} {a' : A}
    {σb : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb) [VxE Z] {ct : U64}
    (hct : sched.cur_thread st s' = ok ct) {number : I64} {call bl don : Bool} (hn : InvSys number call bl don)
    (hInv : syscall.handle_invocation st arI s' a' call bl don false (L.mem s' (Endp.regA ct layout.reg.CAP)) ⦃ res =>
      HIPostMXP (L := L) (MidX (L := L) arI AR MR Z H Cs s') (MidXP (L := L) arI AR MR Z H Cs s') true σb
        call bl don false (Fl4Spec.toBl (L.mem s' (Endp.regA ct layout.reg.CAP)).bv) res ⦄) :
    syscall.dispatch_syscall st arI s' a' number ⦃ r =>
      SInvR.G5.DispPostSt (L := L) arI AR MR Z H Cs (invSysOf call bl) σb s' r ⦄ := by
  have h := inv_afterSt J hct hn hInv
  unfold syscall.dispatch_syscall
  rw [hct]; simp only [bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s' ct layout.reg.CAP) ?_
  rintro c0 rfl
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s' ct layout.reg.REPLY) ?_
  rintro c1 -
  have n65 : fl4_abi.syscall.SysNBSend ≠ fl4_abi.syscall.SysSend := by
    unfold fl4_abi.syscall.SysNBSend fl4_abi.syscall.SysSend; decide
  have n15 : fl4_abi.syscall.SysCall ≠ fl4_abi.syscall.SysSend := by
    unfold fl4_abi.syscall.SysCall fl4_abi.syscall.SysSend; decide
  have n16 : fl4_abi.syscall.SysCall ≠ fl4_abi.syscall.SysNBSend := by
    unfold fl4_abi.syscall.SysCall fl4_abi.syscall.SysNBSend; decide
  rcases hn with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · rw [if_pos rfl]; exact h
  · rw [if_neg n65, if_pos rfl]; exact h
  · rw [if_neg n15, if_neg n16, if_pos rfl]; exact h

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ
open Fl4Proofs.P3.SInvR.G4

end Fl4Proofs.P3.Mc
