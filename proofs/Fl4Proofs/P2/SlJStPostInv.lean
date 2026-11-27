/-
# P2 (line stpost, generations 8–9): the accepted frame-cap invocation keeps the chain's stable ghosts

SlJStPostTm's `jreachSt_tmSt` for the local frame-cap invocation `handle_invocation_local … n p`
(fl4-sync's `local_invocation`, U29V's entry), at every label the plan accepts (`CNodeCopy`, `CNodeMint`,
`X86PageMap`, and since gen 9 `CNodeDelete`).

* `LocInv`: the accepted runs with their spec outcomes (U29V's syscall clause: a native number `n`, its
  spec syscall `c`, fl4-sync's plan `localinv.plan s n = some p` at the entry state, an outcome of
  `fl4KernelEntrySyscall true c`; gen 8's temporary run restriction "label not `CNodeDelete`" is gone).
* **`jreachSt_invSt`**: from every `JReachSt` state, such a run has an outcome `σ'` with `JReachSt` at
  `(s', a', σ')` through a `LocSt` step: P3's `kernel_entry_inv_localSt17` (StPostInvTop) at the chain's
  own ghosts; the kernel-state base by `ksbEq_of_irqNode` with `SInvU.nk_fl4KernelEntrySyscall`.

Inputs: U29V's syscall-clause inputs that the route reads (`hct`, `hn`, `hflag`, `hFin`, `hp`; not `hK` /
`hDL`); platform premises a subset of U29's. No new premise.
-/
import Fl4Proofs.P2.SlJStPostIo
import Fl4Proofs.P3.StPostInvTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap
open Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P3.Vs Fl4Proofs.P3.SInvR.G4 Fl4Proofs.P3.SInvR.G5

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- (stpost) **The accepted frame-cap invocations** with their spec outcomes (module docstring). -/
def LocInv (s : S) (a : A) (σ : Fl4Spec.State Unit) (s' : S) (a' : A) (σ' : Fl4Spec.State Unit) : Prop :=
  ∃ (n : I64) (c : Fl4Spec.Syscall) (p : localinv.Plan), NativeSys n c ∧
    localinv.plan st s n = ok (some p) ∧
    syscall.handle_invocation_local st arI s a n p = ok (true, s', a') ∧
    ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1

end

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 8000000 in
/-- (stpost) **The accepted frame-cap invocation from a `JReachSt` state** (module docstring). -/
theorem jreachSt_invSt [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR)
    (hPA : PPPlatA arI AR) (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hDR : SetDlDetR (A := A) MR)
    {Loc : S → A → Fl4Spec.State Unit → S → A → Fl4Spec.State Unit → Prop}
    {th : TypedHeap} {B : Set (U64 × Fl4Spec.Word)} {H : Heap} {Cs : Set U64} {k : U64}
    (hK : LocKeepSt (L := L) arI AR Loc th B H Cs)
    (hsub : ∀ s a σ s' a' σ', LocSt (L := L) arI AR (LocInv (st := st) arI) th B H Cs s a σ s' a' σ' →
      Loc s a σ s' a' σ')
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachSt (L := L) arI AR MR Loc th B H Cs k s a σ)
    (n : I64) (c : Fl4Spec.Syscall) (p : localinv.Plan) (hct : σ.curThread ≠ σ.idleThread) (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64)
      (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
        KFrontF (L := L) arI n s a s' a' →
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR13 (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hp : localinv.plan st s n = ok (some p))
    {s' : S} {a' : A} (hrun : syscall.handle_invocation_local st arI s a n p = ok (true, s', a')) :
    ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
      JReachSt (L := L) arI AR MR Loc th B H Cs k s' a' σ' := by
  obtain ⟨Z, Ac, Lst, D, hth, hB, -, J, hvx⟩ := hJ.atSt' hK
  have := hvx
  have hT' := kernel_entry_inv_localSt17 hARI hA hnd hM hKD hPA hT hmax htu hRef hDR hJ.reach J n c p hct hn
    hflag hFin hp
  rw [hrun, WP.spec_ok] at hT'
  obtain ⟨σ', hy, hR', G, V, Ac', Lst', D', J'⟩ := hT' rfl
  have hks : L.ksb s' = L.ksb s :=
    ksbEq_of_irqNode J J' (SInvU.nk_fl4KernelEntrySyscall (N := σ.interruptIrqNode) true c σ rfl _ hy)
  refine ⟨σ', hy, .loc hJ (hsub _ _ _ _ _ _ ⟨⟨n, c, p, hn, hp, hrun, hy⟩, hks,
    Z.mv G V, Ac', Lst', D', hth, hB, J', ⟨hvx.eq⟩⟩) hR'⟩

end

end Fl4Proofs.P2.PathObl
