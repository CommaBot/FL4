/-
# P2 (line stpost): the accepted trapped syscall keeps the chain's stable ghosts

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

Premise added beside U29's: `hks : L.ksb s' = L.ksb s` for the run [J] (the kernel-state base
is a store constant: `LawfulStore.ksb_wr`/`ksb_zr`; P2's `sl_trap_foot` gives it as part of
`WritesIn` under the path's P1 preconditions; not derived from `JAtZ` here).

The ReplyRecv arm is not covered (handoff workspace/handoff/stpost.md).
-/
import Fl4Proofs.P2.SlJLocMv
import Fl4Proofs.P3.StPostTop
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
  haveI := hvx
  have hT' := kernel_entry_sysU_localSt hARI hA hnd hM hKD hPA hT hmax htu hRef hSX hDR hJ.reach J n found hct hU
    hND hFin
  rw [hrun, WP.spec_ok] at hT'
  obtain ⟨ev, σ', hev, hO, hR', G, V, Ac', Lst', D', J'⟩ := hT' rfl
  refine ⟨ev, σ', hev, hO, .loc hJ (hsub _ _ _ _ _ _ ⟨⟨n, found, hrun, Or.inr ⟨ev, hev, hO⟩⟩, hks,
    Z.mv G V, Ac', Lst', D', hth, hB, J', ⟨hvx.eq⟩⟩) hR'⟩

end

end Fl4Proofs.P2.PathObl
