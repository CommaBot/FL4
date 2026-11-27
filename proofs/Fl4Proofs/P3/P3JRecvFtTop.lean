/-
P3 (p3J gen 31): **`RecvIpcFt` [J] discharged; the native syscall clause with only the invoking and mid classes**.

* **`recvIpcFt_holds`**: P3JRecvSt's `RecvIpcFt` holds at every state (no premise beyond `P0.ArchTotal`): at a
  dispatch state `JAtZ (Z.mv Z.G V) H Cs` with `Entered`, the current thread in no ready queue and `CKI`, the current
  thread can block (`JAtZ.canBlockCur`), P1's invariants hold over `H`'s sets (`J.blk`), the held endpoint cap's
  object is an `H` endpoint and a held reply cap's an `H` reply (`JPlaced.typed`), and no TCB of `H` has a frame cap
  in its IPC-buffer slot (P3JMcFlt's `noBufCap_cki`, `bufApart_blk`); then P3JRecvFtW's `recvIpcProjW` from
  `BufK.refl`.
* **`DispStabFootLw` [J]** (structure): `inv`, `mid` verbatim from P3JRecvStTop's `DispStabFootLf` (and gen 30's
  `DispStabFootLv`). **`dispStabFootLf_of_Lw`**: the `recvFt` field by `recvIpcFt_holds`.
* **`kernel_entry_runMcWKR_sysLw`**: the native syscall clause, `RunMcWKR` → `RunMcWKR`, with `DispStabFootLw` only
  (+ the globals of P3JRecvCls's `kernel_entry_runMcWKR_sysLv`, unchanged).

Narrowing honesty: `DispStabFootLw` is `DispStabFootLv` without its `recvIpc` field (implied by it). The remaining
[J] content of the syscall clause is exactly the invoking class and the mid class.

Named premise: `DispStabFootLw` [J] (above). No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JRecvStTop
import Fl4Proofs.P3.P3JRecvFtW
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ
open Fl4Proofs.P3.SInvR.G4

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 31) **`RecvIpcFt` holds** (module docstring). -/
theorem recvIpcFt_holds (hA : P0.ArchTotal arI) {Z : XSets} {H : P1.Heap} {Cs : Set U64} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} : RecvIpcFt (L := L) arI AR Z H Cs s a σ := by
  intro V Ac Lst D J hni hnq hC hRR ct hct blocking p b sd g gr rc rc' hpE hrc hHd hHr
  obtain ⟨hcur, x, hk, hrn⟩ := J.curRunnable hni hct
  have hctT : ct ∈ (Z.mv Z.G V).T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hcb := J.canBlockCur hctT hcur hk hrn hni hnq
  obtain ⟨⟨Q0, R0, h0⟩, hB0, hX0, hS0, hSg0⟩ := J.blk
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  obtain ⟨y, hy, hcv⟩ := hHd
  have hHe : H p = some .ep := (hJ.typed _ hy).1 p b sd true g gr hcv
  have hcap : ∀ q g', rc = .Reply q g' → q ∈ P1.Heap.replies H := by
    intro q g' e
    obtain ⟨y', hy', hcv'⟩ := hHr q g' e
    rw [e] at hcv'
    exact (hJ.typed _ hy').2.2 q g' hcv'
  refine WP.spec_mono (recvIpcProjW hA J.kern.heap (noBufCap_cki J hC) (bufApart_blk J.blk) s a ct _ blocking rc p
    Q0 R0 h0 hB0 hX0 hS0 hSg0 hcb rfl hHe hcap (fun n hn => hn) (P1.BufK.refl s)) ?_
  rintro ⟨s', a'⟩ hW
  simpa only [WP.uncurry'_pair] using hW

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- (p3J gen 31) **`DispStabFootLw` [J]**: the invoking and mid classes of the dispatch (module docstring). -/
structure DispStabFootLw (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
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

variable {arI AR MR}

/-- (p3J gen 31) **`DispStabFootLw → DispStabFootLf`** (module docstring). -/
theorem dispStabFootLf_of_Lw (hA : P0.ArchTotal arI) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : DispStabFootLw (L := L) arI AR MR s a σ) : DispStabFootLf (L := L) arI AR MR s a σ where
  inv := h.inv
  mid := h.mid
  recvFt := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => recvIpcFt_holds hA

set_option maxHeartbeats 4000000 in
/-- (p3J gen 31) **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with `DispStabFootLw` only** (`hLw` [J];
module docstring). -/
theorem kernel_entry_runMcWKR_sysLw [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hLw : DispStabFootLw (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLf hARI hA hnd hM hIp hKD hPAi hT hmax htu hRef hSX hDR hFpu hFW hR
    (dispStabFootLf_of_Lw hA hLw)

end

end Fl4Proofs.P3.Mc
