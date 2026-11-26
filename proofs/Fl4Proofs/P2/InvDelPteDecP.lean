/-
# P2 (line invj, generation 7): `dec_alt` of the Delete PTE-arm path under rule 8 (`invDecPP`)

**`invDecPP`**: a run declining at a `PreP` entry `s` declines at every alternative of `InvRSP s`, on the decline
guard `(⊤, IoDS s)` and on the `mguard` store for `StepOK (ownP K)` — `inv_dec_altR` at `Alt.anti` (`IoRSR s ⊆
IoRSP s ⊆ InvRSP s`: `ioRSR_P`, `ioRSP_inv`), the `mguard` run lifted from `own` to `ownP` over the program tree
(`hp` [P], as `invMovePP`) by `interp_mguard_mono` with `stepOKP_of_stepOKV ∘ stepOKV_of_own`.

No new premise. New module; no existing statement changes.
-/
import Fl4Proofs.P2.InvDelPteMoveP
import Fl4Proofs.P2.InvDelPteDecR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV

section dec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- (invj gen 7) **`dec_alt` of the PTE-arm path under rule 8** (module docstring). -/
theorem invDecPP {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} {number : I64} {p : localinv.Plan} {K : KLayoutP} {m : U64 → U64}
    (hKP : RegionOKP K) (nv : K.vcpus = ∅) {q : SProg Bool}
    (hp : IsProgOn (fun m s a => syscall.handle_invocation_local m ar s a number p) ar st
      (AltOf st (PreP st Cs Ω Sg Ac Locks p K m) (InvRSP st K Locks) (OwnMap.cls K.toKLayout)
        (OwnMap.ko K.toKLayout m) (· ∈ K.user)) q)
    {s s' : S} {a : A} {r r' : Bool × S × A} (hE : PreP st Cs Ω Sg Ac Locks p K m s)
    (h : syscall.handle_invocation_local st ar s a number p = ok r) (hr : r.1 ≠ true)
    (Al : Alt st (InvRSP st K Locks s) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) s s')
    (h' : syscall.handle_invocation_local st ar s' a number p = ok r') :
    r'.1 ≠ true ∧
      syscall.handle_invocation_local (guard st (fun _ => True) (IoDS (st := st) s)) ar s' a number p = ok r' ∧
      syscall.handle_invocation_local (mguard st (fun x y => PathObl.StepOK (ownP K) (OwnMap.cls K.toKLayout)
        (OwnMap.ko K.toKLayout m) (· ∈ K.user) (L.cpu s) (Locks s) (L.mem x) (L.mem y))) ar s' a number p =
        ok r' := by
  have hks := ksNoE_conv hE.2.2.choose_spec.1
  obtain ⟨h1, h2, h3⟩ := inv_dec_altR hA hE.1.regionOK hE.1.ioLayA hE.2.1.1.1.1 (invSeenR_of hE.1 hE.2.1) h hr
    (Al.anti (fun x hx => ioRSP_inv (ioRSR_P hKP hks hx))) h'
  refine ⟨h1, h2, ?_⟩
  rw [inv_hp hp (Narrow.mguard _ _) ⟨s, hE, Al⟩ a] at h3 ⊢
  exact interp_mguard_mono (fun x y hs => stepOKP_of_stepOKV (stepOKV_of_own nv hs)) q s' a _ h3

end dec

end Fl4Proofs.P2.E2EP
