/-
# P2 (line slj2): the syscall entry's bundle `SlJAt` at every reachable entry state

`kernel_entry_reachU17V` (P3/XTopJointKEntryU17.lean) gives, at every `JReachU17` state `s`
(the state each kernel entry starts from, reached by the U17 chain of serial entries), `JAtZ`
at some ghosts `Zx H Cs Ac Lst D` and `SInvX σ`, whose `cr` makes the scheduler action resume;
`JKern.csN` numbers `Cs` from 0. So `SlJAt.of_JAtZ` (P2/SlJEnt.lean) gives `SlJAt K s` for the
layout read off that state, `K = layoutJ Zx H (L.ksb s) n`:

* `slJAt_of_JAtZ`: from `JAtZ` and the action resume (any entry state);
* `slJAt_of_reachU17`: at every `JReachU17` state, under `kernel_entry_reachU17V`'s premises
  only (no new premise).

What this does not give (the fixed-layout caveat): `sl_localPathJ` asks `SlJAt K s` for one
`K` at every state of its `P`. `K` is read off the state, and the ghosts are existential per
state, so a fixed `K` across the states of `P` needs `H`, `Zx.th`, `Zx.B`, `L.ksb` and the core
count to be the same ghosts at each of them (true between serial entries that keep the typed
heap: `Serial.no_overlap`'s local paths write no object or slot layout, P2/SerExit.lean,
P2/OwnLayout.lean), which P3 does not state: its reachability chain re-chooses the ghosts at each
exit.
-/
import Fl4Proofs.P2.SlJEnt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap
open Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P3.Vs Fl4Proofs.P3.SInvR.G4 Fl4Proofs.P3.SInvR.G5

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **`SlJAt` at a joint-invariant state with the action resume**, for the layout read off
it (`JKern.csN` gives the core count). -/
theorem slJAt_of_JAtZ {A' : Type} {arI : machine.Arch A'} {AR : A' → Fl4Spec.Cr3 → Prop}
    {Zx : XSets} {H : Heap} {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64} {s : S} {a' : A'}
    {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Zx H Cx Ax Lst D s a' σ)
    (hres : σ.schedulerAction = .resumeCurThread) :
    ∃ n : Nat, SlJAt (L := L) (layoutJ Zx H (L.ksb s) n) s := by
  obtain ⟨n, hn⟩ := J.kern.csN
  exact ⟨n, SlJAt.of_JAtZ J hres hn⟩

set_option maxHeartbeats 4000000 in
/-- **`SlJAt` at every reachable entry state** (module docstring): `kernel_entry_reachU17V`'s
premises, no other. -/
theorem slJAt_of_reachU17 {A : Type} (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop)
    (MR : A → Fl4Spec.MachineState → Prop) [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR)
    (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ) :
    ∃ (Zx : XSets) (H : Heap) (n : Nat), SlJAt (L := L) (layoutJ Zx H (L.ksb s) n) s := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, -, J, hX, -⟩ :=
    kernel_entry_reachU17V arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
  obtain ⟨n, h⟩ := slJAt_of_JAtZ J hX.cr.2
  exact ⟨Z, H, n, h⟩

end

end Fl4Proofs.P2.PathObl
