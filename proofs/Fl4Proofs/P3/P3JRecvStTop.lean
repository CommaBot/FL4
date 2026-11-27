/-
P3 (p3J gen 31): **the native syscall clause with the endpoint receive's stable post proved** — gen 30's
`DispStabFootLv` [J] restated with its `recvIpc` field (`RecvIpcStFt`, stable post ∧ footprint) replaced by the
footprint alone (P3JRecvSt's `RecvIpcFt`).

* **`DispStabFootLf` [J]** (structure): `inv`, `mid` verbatim from `DispStabFootLv`; `recvFt`: `RecvIpcFt` at every
  dispatch state of the entry (where `DispStabFootLv.recvIpc` asks `RecvIpcStFt`).
* **`dispStabFootLv_of_Lf`**: `DispStabFootLf → DispStabFootLv` (P3JRecvSt's `recvIpcStFt_of`, with `VxE Z` from
  the field's own hypothesis and JEntryGlob's `maxTU` / `tu`, already globals of the clause).
* **`kernel_entry_runMcWKR_sysLf`**: the native syscall clause, `RunMcWKR` → `RunMcWKR`, with `DispStabFootLf`
  only (+ the globals of P3JRecvCls's `kernel_entry_runMcWKR_sysLv`).

Narrowing honesty: `inv` / `mid` are `DispStabFootLv`'s fields unchanged; `recvFt` is implied by `recvIpc` (its
footprint conjunct) and not conversely. The remaining [J] content: the invoking class, the mid class, and the
footprint of the endpoint receive (`RecvIpcFt`).

Named premises: `DispStabFootLf` [J] (above; `RecvIpcFt` [J] is P3JRecvSt's). No sorry. New module; no existing
statement changed.
-/
import Fl4Proofs.P3.P3JRecvSt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ
open Fl4Proofs.P3.SInvR.G4

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- (p3J gen 31) **`DispStabFootLf` [J]**: `DispStabFootLv` with the endpoint receive's footprint only (module
docstring). -/
structure DispStabFootLf (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- The invoking class (`SysSend`, `SysNBSend`, `SysCall`). -/
  inv : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (call bl don : Bool),
        σ.curThread ≠ σ.idleThread → InvSys n call bl don → SysFlag (L := L) s →
        SysK6 (L := L) arI AR Z H Cs s a σ n (invSysOf call bl) →
        DispStabFootAt (L := L) arI AR MR Z H Cs s a σ n (invSysOf call bl)
  /-- The mid class (`SysReplyRecv`, `SysNBSendRecv`, `SysNBSendWait`). -/
  mid : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        DispStabFootAt (L := L) arI AR MR Z H Cs s a σ n c
  /-- The endpoint receive's footprint at every dispatch state of the entry (`RecvIpcFt`). -/
  recvFt : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → σ.curThread ≠ σ.idleThread → SysFlag (L := L) s →
      ∀ σb, BudgetAt σ σb true → ∀ (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        RecvIpcFt (L := L) arI AR Z H Cs s' a' σb

variable {arI AR MR}

/-- (p3J gen 31) **`DispStabFootLf → DispStabFootLv`** (module docstring). -/
theorem dispStabFootLv_of_Lf (hA : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) {s : S} {a : A}
    {σ : Fl4Spec.State Unit} (h : DispStabFootLf (L := L) arI AR MR s a σ) :
    DispStabFootLv (L := L) arI AR MR s a σ where
  inv := h.inv
  mid := h.mid
  recvIpc := fun hR Z H Cs Ac Lst D J hV hct hfl σb hB s' a' hK => by
    haveI := hV
    exact recvIpcStFt_of hA hmax htu (h.recvFt hR Z H Cs Ac Lst D J hV hct hfl σb hB s' a' hK)

set_option maxHeartbeats 4000000 in
/-- (p3J gen 31) **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with `DispStabFootLf` only** (`hLf` [J];
module docstring). -/
theorem kernel_entry_runMcWKR_sysLf [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hLf : DispStabFootLf (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLv hARI hA hnd hM hIp hKD hPAi hT hmax htu hRef hSX hDR hFpu hFW hR
    (dispStabFootLv_of_Lf hA hmax htu hLf)

end

end Fl4Proofs.P3.Mc
