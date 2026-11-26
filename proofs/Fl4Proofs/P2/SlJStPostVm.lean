/-
# P2 (line stpost, generation 9): the accepted VM fault keeps the chain's stable ghosts

SlJStPostIrq's `jreachSt_irqSt` for the local page-fault entry `handle_vm_fault_local … ad c`
(fl4-sync's local VM-fault entry, U29Vm's first clause).

* `LocVmf`: the accepted VM-fault runs (any address `ad`, error code `c`, spec fault kind `ft`) with
  their spec outcomes (`EvOut false (.vmFaultEvent ft)`). The hardware fact `VmfHw` is an input of the
  step lemma, not part of the relation (as `IrqHw` for `LocIrq`).
* **`jreachSt_vmfSt`**: from every `JReachSt` state, an accepted `handle_vm_fault_local … ad c` (with
  `VmfHw ad c ft σ`) has an `EvOut false (.vmFaultEvent ft)` outcome `σ'` with `JReachSt` at
  `(s', a', σ')` through a `LocSt` step: P3's `kernel_entry_vmf_localSt17` (StPostVmTop) at the chain's
  own ghosts; the kernel-state base by `ksbEq_of_irqNode` with `evOut_irqNode`.

Inputs: U29Vm's VM-fault clause inputs (`hct`, `hV : VmfHw` [P], `hFin : KFinEv13`); platform premises a
subset of U29's. No new premise. So `LocKeepSt (LocSt LocVmf …)` holds by `locKeepSt_st`.
-/
import Fl4Proofs.P2.SlJStPostInv
import Fl4Proofs.P3.StPostVmTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap
open Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P3.Vs Fl4Proofs.P3.SInvR.G4 Fl4Proofs.P3.SInvR.G5

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- (stpost) **The accepted VM-fault runs** with their spec outcomes (module docstring). -/
def LocVmf (s : S) (a : A) (σ : Fl4Spec.State Unit) (s' : S) (a' : A) (σ' : Fl4Spec.State Unit) : Prop :=
  ∃ (ad c : U64) (ft : Fl4Spec.VMFaultType),
    syscall.handle_vm_fault_local st arI s a ad c = ok (true, s', a') ∧
    Fl4Proofs.P3.EvOut false (.vmFaultEvent ft) σ σ'

end

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 8000000 in
/-- (stpost) **The accepted VM fault from a `JReachSt` state** (module docstring). -/
theorem jreachSt_vmfSt [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR)
    (hPA : PPPlatA arI AR) (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {Loc : S → A → Fl4Spec.State Unit → S → A → Fl4Spec.State Unit → Prop}
    {th : TypedHeap} {B : Set (U64 × Fl4Spec.Word)} {H : Heap} {Cs : Set U64} {k : U64}
    (hK : LocKeepSt (L := L) arI AR Loc th B H Cs)
    (hsub : ∀ s a σ s' a' σ', LocSt (L := L) arI AR (LocVmf (st := st) arI) th B H Cs s a σ s' a' σ' →
      Loc s a σ s' a' σ')
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachSt (L := L) arI AR MR Loc th B H Cs k s a σ)
    (ad c : U64) (ft : Fl4Spec.VMFaultType) (hct : σ.curThread ≠ σ.idleThread) (hV : VmfHw ad c ft σ)
    (hFin : KFinEv13 (L := L) arI AR (.vmFaultEvent ft) (KFrontF2 (st := st) arI (brV (st := st) arI ad c) s a) σ)
    {s' : S} {a' : A} (hrun : syscall.handle_vm_fault_local st arI s a ad c = ok (true, s', a')) :
    ∃ σ', Fl4Proofs.P3.EvOut false (.vmFaultEvent ft) σ σ' ∧
      JReachSt (L := L) arI AR MR Loc th B H Cs k s' a' σ' := by
  obtain ⟨Z, Ac, Lst, D, hth, hB, -, J, hvx⟩ := hJ.atSt' hK
  have := hvx
  have hT' := kernel_entry_vmf_localSt17 hARI hA hnd hM hKD hPA hT hmax htu hRef hSX hDR hJ.reach J ad c ft hct hV
    hFin
  rw [hrun, WP.spec_ok] at hT'
  obtain ⟨σ', hO, hR', G, V, Ac', Lst', D', J'⟩ := hT' rfl
  have hks : L.ksb s' = L.ksb s := ksbEq_of_irqNode J J' (evOut_irqNode hO)
  refine ⟨σ', hO, .loc hJ (hsub _ _ _ _ _ _ ⟨⟨ad, c, ft, hrun, hO⟩, hks,
    Z.mv G V, Ac', Lst', D', hth, hB, J', ⟨hvx.eq⟩⟩) hR'⟩

end

end Fl4Proofs.P2.PathObl
