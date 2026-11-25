/-
# P2 (line stpost, generation 4): the accepted ReplyRecv fast path keeps the chain's stable ghosts

SlJStPost's `jreachSt_sysUStK` for the other arm of `handle_syscall_local`: the ReplyRecv fast
path (trap flag clear, `SysReplyRecv`, `fastpath.reply_recv_found` with fl4-sync's `found`).

* **`jreachSt_rrSt`**: from every `JReachSt` state, an accepted
  `handle_syscall_local … SysReplyRecv found` has an outcome `σ'` of
  `fl4KernelEntrySyscall true .sysReplyRecv` with `JReachSt` at `(s', a', σ')` through a `LocSt`
  step: P3's `kernel_entry_rr_localSt17` (StPostRRReach) at the chain's own ghosts gives
  `JReachU17` and `JStab Z H Cs` at the same outcome; the kernel-state base by `ksbEq_of_irqNode`
  with P3 `SInvU.nk_fl4KernelEntrySyscall` (no spec entry writes the IRQ node).

Inputs: U29S's syscall clause at `SysReplyRecv` that the route reads (`hflag`, `hFin`, `hfd`);
no premise beyond U29S's.
-/
import Fl4Proofs.P2.SlJStPost
import Fl4Proofs.P3.StPostRRReach
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap
open Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P3.Vs Fl4Proofs.P3.SInvR.G4 Fl4Proofs.P3.SInvR.G5

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 8000000 in
/-- (stpost) **The accepted ReplyRecv fast path from a `JReachSt` state** (module docstring). -/
theorem jreachSt_rrSt [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {Loc : S → A → Fl4Spec.State Unit → S → A → Fl4Spec.State Unit → Prop}
    {th : TypedHeap} {B : Set (U64 × Fl4Spec.Word)} {H : Heap} {Cs : Set U64} {k : U64}
    (hK : LocKeepSt (L := L) arI AR Loc th B H Cs)
    (hsub : ∀ s a σ s' a' σ', LocSt (L := L) arI AR (LocSys (st := st) arI) th B H Cs s a σ s' a' σ' →
      Loc s a σ s' a' σ')
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachSt (L := L) arI AR MR Loc th B H Cs k s a σ)
    (found : U64 × U64) (hct : σ.curThread ≠ σ.idleThread)
    (hn : NativeSys fl4_abi.syscall.SysReplyRecv .sysReplyRecv)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hFin : ∀ x ∈ (specFront .sysReplyRecv σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64)
      (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
        KFrontF (L := L) arI fl4_abi.syscall.SysReplyRecv s a s' a' →
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR13 (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hfd : ∀ t f, sched.cur_thread st s = ok t → obj.Tcb.flags st t s = ok f →
      (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 → fl4_abi.syscall.SysReplyRecv = fl4_abi.syscall.SysReplyRecv →
      fastpath.reply_caps st s t = ok (some found))
    {s' : S} {a' : A}
    (hrun : syscall.handle_syscall_local st arI s a fl4_abi.syscall.SysReplyRecv found = ok (true, s', a')) :
    ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true .sysReplyRecv σ).1 ∧
      JReachSt (L := L) arI AR MR Loc th B H Cs k s' a' σ' := by
  obtain ⟨Z, Ac, Lst, D, hth, hB, -, J, hvx⟩ := hJ.atSt' hK
  have := hvx
  have hT' := kernel_entry_rr_localSt17 hARI hA hnd hM hKD hPA hT hmax htu hRef hSX hDR hJ.reach J found hct hn
    hflag hFin hfd
  rw [hrun, WP.spec_ok] at hT'
  obtain ⟨σ', hy, hR', G, V, Ac', Lst', D', J'⟩ := hT' rfl
  have hks : L.ksb s' = L.ksb s :=
    ksbEq_of_irqNode J J' (SInvU.nk_fl4KernelEntrySyscall (N := σ.interruptIrqNode) true .sysReplyRecv σ rfl _ hy)
  refine ⟨σ', hy, .loc hJ (hsub _ _ _ _ _ _ ⟨⟨_, found, hrun, Or.inl ⟨.sysReplyRecv, hn, hy⟩⟩, hks,
    Z.mv G V, Ac', Lst', D', hth, hB, J', ⟨hvx.eq⟩⟩) hR'⟩

end

end Fl4Proofs.P2.PathObl
