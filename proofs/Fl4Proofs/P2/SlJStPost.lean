/-
# P2 (line stpost): the accepted trapped syscall (trap arm) keeps the chain's stable ghosts

Lines lstab / locmv reduced the syscall local path's layout gap to `LocKeepSt Loc th B H Cs`
for the local steps between two serial entries. For an *accepted* local entry the spec side is
nondeterministic (an accepted run relates to *some* outcome of the spec entry), so a step
relation that names an arbitrary spec outcome (`LocSys`) cannot keep the ghosts: the ghosts
are tied to the run's own outcome. The step relation used here records that outcome:

* `LocSt Loc th B H Cs`: a `Loc` step whose end state keeps the kernel-state base and has
  `JAtZ` at ghosts with the chain's `th`, `B`, `H`, `Cs` (and `VxE`). `locKeepSt_st`:
  `LocKeepSt` holds for it by construction; `LocKeepSt.or` combines it with the other steps.
* **`jreachSt_sysUSt`** (the per-entry content): from every `JReachSt` state, an accepted
  `handle_syscall_local` of a `TRAP_SYSCALLS` thread (the trap arm, `fastpath.fault`; U29S's
  unknown-syscall clause, inputs verbatim) has a spec outcome `σ'` with `JReachSt` at
  `(s', a', σ')` through a `LocSt` step: P3's `kernel_entry_sysU_localSt` at the chain's own
  ghosts (`JReachSt.atSt'`) gives `JReachU17` and `JStab Z H Cs` at the same outcome.

`jreachSt_sysUSt` takes `hks : L.ksb s' = L.ksb s` for the run as a premise; **`jreachSt_sysUStK`**
(line stpost, generation 2) is the same theorem without it: the kernel-state base is read off
the spec's IRQ node (`ksbEq_of_irqNode`: `JAtZ`'s `IrqRel.node` pins
`σ.interruptIrqNode 0 = nodeA (L.ksb s) 0`), and no spec event writes the IRQ node
(`evOut_irqNode`, from P3 `SInvU.nk_fl4SyscallFaultIP` / `nk_fl4CallKernel`). So any two joint
states related by a kernel event share `L.ksb`, whatever their ghosts; no new premise.

The other arm of `handle_syscall_local`, the ReplyRecv fast path, is SlJStPostRR's `jreachSt_rrSt`
(line stpost, generation 4); SlJStTop's `sl_pathsK_startAt_loc` composes both arms with lstab /
locmv's `StartAt` (no `LocKeepSt` premise left).
-/
import Fl4Proofs.P2.SlJLocMv
import Fl4Proofs.P3.StPostTop
import Fl4Proofs.P3.SpecInvUtNK6
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap
open Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P3.Vs Fl4Proofs.P3.SInvR.G4 Fl4Proofs.P3.SInvR.G5

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **A step that keeps the chain's stable ghosts** (module docstring). -/
def LocSt (Loc : S → A → Fl4Spec.State Unit → S → A → Fl4Spec.State Unit → Prop)
    (th : TypedHeap) (B : Set (U64 × Fl4Spec.Word)) (H : Heap) (Cs : Set U64)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (s' : S) (a' : A) (σ' : Fl4Spec.State Unit) : Prop :=
  Loc s a σ s' a' σ' ∧ L.ksb s' = L.ksb s ∧
    ∃ (Z : XSets) (Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      Z.th = th ∧ Z.B = B ∧ JAtZ (L := L) arI AR Z H Cs Ac Lst D s' a' σ' ∧ VxE Z

variable {arI AR MR}

/-- `LocKeepSt` of a `LocSt` step (by construction). -/
theorem locKeepSt_st (Loc : S → A → Fl4Spec.State Unit → S → A → Fl4Spec.State Unit → Prop)
    (th : TypedHeap) (B : Set (U64 × Fl4Spec.Word)) (H : Heap) (Cs : Set U64) :
    LocKeepSt (L := L) arI AR (LocSt (L := L) arI AR Loc th B H Cs) th B H Cs := by
  intro k s a σ s' a' σ' ⟨_, _, _, _, _, _, hk, _, _⟩ ⟨_, hks, Z, Ac, Lst, D, hth, hB, J, hvx⟩
  exact ⟨Z, Ac, Lst, D, hth, hB, hks.trans hk, J, hvx⟩

set_option maxHeartbeats 8000000 in
/-- **The accepted trapped syscall from a `JReachSt` state** (module docstring): a spec
outcome `σ'` of the unknown-syscall event and `JReachSt` at `(s', a', σ')` by a `LocSt` step.
`hK`: `LocKeepSt` of the chain's whole step relation (gives `JAtSt` at the start). -/
theorem jreachSt_sysUSt [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
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
    (n : I64) (found : U64 × U64) (hct : σ.curThread ≠ σ.idleThread) (hU : UnkSys (L := L) n s)
    (hND : NoDbgSys (L := L) arI n s a)
    (hFin : ∀ ev, KEvSpec (.sysU n) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      KFinEv13 (L := L) arI AR ev (KFrontSysU (st := st) arI n s a) w.2)
    {s' : S} {a' : A} (hrun : syscall.handle_syscall_local st arI s a n found = ok (true, s', a'))
    (hks : L.ksb s' = L.ksb s) :
    ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
      JReachSt (L := L) arI AR MR Loc th B H Cs k s' a' σ' := by
  obtain ⟨Z, Ac, Lst, D, hth, hB, -, J, hvx⟩ := hJ.atSt' hK
  have := hvx
  have hT' := kernel_entry_sysU_localSt hARI hA hnd hM hKD hPA hT hmax htu hRef hSX hDR hJ.reach J n found hct hU
    hND hFin
  rw [hrun, WP.spec_ok] at hT'
  obtain ⟨ev, σ', hev, hO, hR', G, V, Ac', Lst', D', J'⟩ := hT' rfl
  refine ⟨ev, σ', hev, hO, .loc hJ (hsub _ _ _ _ _ _ ⟨⟨n, found, hrun, Or.inr ⟨ev, hev, hO⟩⟩, hks,
    Z.mv G V, Ac', Lst', D', hth, hB, J', ⟨hvx.eq⟩⟩) hR'⟩

/-- **The kernel-state base is read off the spec's IRQ node.** `JAtZ`'s `IrqRel` (in `XTopAt`)
pins `σ.interruptIrqNode 0` to the address `nodeA (L.ksb s) 0`; so two joint states whose spec
states share the IRQ node share the kernel-state base (whatever their ghosts). -/
theorem ksbEq_of_irqNode {Z Z' : XSets} {H H' : Heap} {Cs Cs' Ac Ac' : Set U64} {Lst Lst' : U64 → List U64}
    {D D' : Set U64} {s s' : S} {a a' : A} {σ σ' : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (J' : JAtZ (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' σ')
    (hn : σ'.interruptIrqNode = σ.interruptIrqNode) : L.ksb s' = L.ksb s := by
  have h1 := J.xtop.fin.1.1.2.2.2.1.node 0#u64 (by decide)
  have h2 := J'.xtop.fin.1.1.2.2.2.1.node 0#u64 (by decide)
  rw [hn, h1] at h2
  have h3 : (nodeA (L.ksb s) 0#u64).val = (nodeA (L.ksb s') 0#u64).val := congrArg BitVec.toNat h2
  unfold nodeA at h3
  simp only [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq] at h3
  simp [U64.size, U64.numBits] at h3
  have b1 := (L.ksb s).hBounds
  have b2 := (L.ksb s').hBounds
  apply UScalar.eq_of_val_eq
  simp [U64.size, U64.numBits] at b1 b2
  omega

end

/-- **A kernel event keeps the IRQ node** (P3 `SInvU.nk_fl4SyscallFaultIP` /
`nk_fl4CallKernel`: no spec step writes it). -/
theorem evOut_irqNode {fip : Bool} {ev : Fl4Spec.Event} {σ σ' : Fl4Spec.State Unit} (h : EvOut fip ev σ σ') :
    σ'.interruptIrqNode = σ.interruptIrqNode := by
  cases fip
  · exact SInvU.nk_fl4CallKernel (N := σ.interruptIrqNode) true ev σ rfl _ h
  · obtain ⟨w, hw, hy⟩ := h
    exact SInvU.nk_fl4CallKernel (N := σ.interruptIrqNode) true ev w.2
      (SInvU.nk_fl4SyscallFaultIP (N := σ.interruptIrqNode) σ.curThread σ rfl w hw) _ hy

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 8000000 in
/-- **`jreachSt_sysUSt` without `hks`**: the kernel-state base kept by the run is derived
(`ksbEq_of_irqNode` at the start and end joint states, `evOut_irqNode` for the outcome). -/
theorem jreachSt_sysUStK [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
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
    (n : I64) (found : U64 × U64) (hct : σ.curThread ≠ σ.idleThread) (hU : UnkSys (L := L) n s)
    (hND : NoDbgSys (L := L) arI n s a)
    (hFin : ∀ ev, KEvSpec (.sysU n) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      KFinEv13 (L := L) arI AR ev (KFrontSysU (st := st) arI n s a) w.2)
    {s' : S} {a' : A} (hrun : syscall.handle_syscall_local st arI s a n found = ok (true, s', a')) :
    ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
      JReachSt (L := L) arI AR MR Loc th B H Cs k s' a' σ' := by
  obtain ⟨Z, Ac, Lst, D, hth, hB, -, J, hvx⟩ := hJ.atSt' hK
  have := hvx
  have hT' := kernel_entry_sysU_localSt hARI hA hnd hM hKD hPA hT hmax htu hRef hSX hDR hJ.reach J n found hct hU
    hND hFin
  rw [hrun, WP.spec_ok] at hT'
  obtain ⟨ev, σ', hev, hO, hR', G, V, Ac', Lst', D', J'⟩ := hT' rfl
  have hks : L.ksb s' = L.ksb s := ksbEq_of_irqNode J J' (evOut_irqNode hO)
  refine ⟨ev, σ', hev, hO, .loc hJ (hsub _ _ _ _ _ _ ⟨⟨n, found, hrun, Or.inr ⟨ev, hev, hO⟩⟩, hks,
    Z.mv G V, Ac', Lst', D', hth, hB, J', ⟨hvx.eq⟩⟩) hR'⟩

end

end Fl4Proofs.P2.PathObl
