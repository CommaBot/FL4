/-
P2 (line invj, gen 2): **`serializable_fl4_localWI`: W9's top with the frame-cap invocation local path as a new
slot** (new definitions only; no existing statement changes).

## Where the path goes

`fl4LocP3W6` (P2/E2EVFl4W6.lean) has seven slots (`Fl4Loc`: vmF, vmR, io, st, irq, sl, and the `ownV`-native
family `vq`); none of them is the frame-cap invocation path (`syscall.handle_invocation_local`, CNodeDelete arm),
so it is a **new slot**, not a replacement. `Fl4Loc`'s seven fields are fixed, but `vq` is an arbitrary `PathsV ν`
family: the new family puts the path beside W6's `vq` (`fl4LQP3W5`, vx ⊕ vt) through `PathsV.sum`, so the generic
top `serializable_fl4_localG` (any `Fl4Loc`) applies unchanged.

* `avoidV_nv`: a path stated for `own` meets `AvoidV` at a layout with no VCPU, from its own `PathObl.acc` /
  `dec_alt` / `isProg` (the cut read set `rsV K RS` is `RS`; the declining run at an alternative goes from the
  guard `(⊤, DS)` to `(¬ VData, ⊤)` by `interp_mono`), given `NoZero` of its tree;
* `InvArg` (syscall number, plan, P1's sets, locks), `InvPremW` (no VCPU; a bundle state at the index's core and
  active-SC sets, which gives `Cs` below 64 as for io's `IoPremW9`; [P] `lk`: the locks are kept by a user write),
  **`invSlotW`** (`SlotC` at `inv_pathsKFU4`, P2/InvURoTr.lean: the uncut CNodeDelete path, no [W]);
* **`fl4LocP3WI`**: `fl4LocP3W6` with `vq := PathsV.sum fl4LQP3W5 invSlotW.lift`; **`StartP3WI`** (W9's start facts,
  and for the new index the slot's record and `GlueAt` [P] with the entry fact `InvQF` at the start state, as
  every other slot's); **`startAt_P3WI`**; **`serializable_fl4_localWI`** (W9's statement over the new family).

Premises of `serializable_fl4_localWI`: W9's (`P : LocPlat`, `hIoa` [P], `h0`, `hA0`, `hB`, `nv0`, `hM0`, the
execution `h : ExecW …` and `hq`); the new slot adds only what its `StartP3WI` record asks (`InvPremW.lk` [P],
`GlueAt` [P] with `InvQF` at the start, as the other slots' entry facts).
-/
import Fl4Proofs.P2.InvURoTr
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
open Fl4Proofs.P2.OwnMap (fld oAFFINITY region TcbSlot InW InNode)
open Fl4Proofs.P2.E2E (StartAt SP LocalPath SerStep)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg)

noncomputable section
open Classical

/-! ## `AvoidV` with no VCPU -/

section av
variable {K : KLayoutV} {cls : U64 → U64 → U64} {ko : U64 → ClsOwner U64} {User : U64 → Prop}

/-- **`AvoidV` at a layout with no VCPU** (module docstring). -/
theorem avoidV_nv (nv : K.vcpus = ∅) (P : LocalPath (OwnMap.own K.toKLayout) cls ko User) (hz : NoZero P.p) :
    AvoidV K P := by
  have hV : ∀ x, ¬ VData K x := fun x ⟨v, ⟨hv, _⟩, _⟩ => by rw [nv] at hv; exact hv
  have hrs : rsV K P.RS = P.RS :=
    funext fun s => funext fun x => propext ⟨fun h => h.1, fun h => ⟨h, hV x⟩⟩
  letI := P.L
  refine ⟨?_, ?_, ?_⟩
  · intro s a r hs h hacc
    rw [hrs]
    exact P.obl.acc s a r hs h hacc
  · intro s a r hs h hd s' r' Al h'
    obtain ⟨-, hg, -⟩ := P.obl.dec_alt s a r hs h hd s' r' Al h'
    rw [P.isProg _ (Narrow.guard _ _ _) s' ⟨s, hs, Al⟩ a] at hg ⊢
    exact interp_mono (fun q _ => hV q) (fun _ _ => trivial) _ hz s' a _ hg
  · rw [hrs]; exact P.isProg

/-- The chosen tree of a program premise `∃ q, _ ∧ NoZero q ∧ _` has no `zero`. -/
theorem nz_choose {X : Type} {P Q : SProg X → Prop} (h : ∃ q, P q ∧ NoZero q ∧ Q q) : NoZero h.choose :=
  h.choose_spec.2.1

end av

/-! ## The slot -/

/-- The frame-cap invocation path's index: the syscall number, the plan, P1's sets and the locks. -/
structure InvArg (S : Type) : Type where
  number : I64
  p : localinv.Plan
  Cs : Set U64
  Ω : Set U64
  Sg : Set U64
  Ac : Set U64
  Locks : S → U64 → Prop

section slot
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)

/-- **The frame-cap invocation slot's premises at `(K, m)`** (module docstring). -/
structure InvPremW (i : InvArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- No VCPU in the layout (P3's scope, as `ioSlotP3W`). -/
  nv : K.vcpus = ∅
  /-- Some bundle state of the layout with the index's core / active-SC sets as its ghosts (as `IoPremW9.bunS`). -/
  bunS : ∃ σ : S, SlJAtS (L := L) K.toKLayout i.Cs i.Ac σ
  /-- [P] The locks are kept by an aligned user-word write at a bundle state (`hufQF_of2`'s `hlk`). -/
  lk : ∀ (K' : OwnMap.KLayout) (s : S) (b v : U64), SlJAt (L := L) K' s → b ∈ K'.user → Aligned b →
    i.Locks (L.wr s b v) = i.Locks s

theorem InvPremW.hCs {i : InvArg S} {K : KLayoutV} {m : U64 → U64} (h : InvPremW st i K m) :
    ∀ c ∈ i.Cs, c.val < 64 := by
  obtain ⟨σ, A', arI, AR, Zx, Lst, D, a', τ, B⟩ := h.bunS
  exact fun c hc => B.j.kern.csLt c hc

variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- **The frame-cap invocation slot** (route C, at `inv_pathsKFU4`; `AvoidV` by `avoidV_nv`). -/
def invSlotW : SlotC (InvArg S) where
  Prem i K m := InvPremW st i K m
  path i K m hK hU h :=
    inv_pathsKFU4 (Cs := i.Cs) (Ω := i.Ω) (Sg := i.Sg) (Ac := i.Ac) (Locks := i.Locks) ar hA i.number i.p hm
      (h.hCs st) h.lk () K.toKLayout m hK.base hU.base
  Av i K m hK hU h := avoidV_nv h.nv _ (by
    dsimp only [inv_pathsKFU4, inv_pathsKFU3, inv_pathsKFU2, inv_pathsKFU8, inv_pathsKDelU, inv_localPathU]
    exact nz_choose _)

end slot

/-! ## The family -/

section fam
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)

end fam

/-! ## The start fact and the top -/

section start
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st] {A : Type}
  (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)

variable {arI AR MR}

end start

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

end top

end
end Fl4Proofs.P2.E2EV
