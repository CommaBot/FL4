/-
# P2 (line pte, generation 15): `blk` discharged — the PageMap slot with `PmObl5` (no `blk`)

* **`pm_blkG`**: gen 13's [W] `PmBlkUW2` at `PmPreG`, proved at every layout with `RegionOKP K` (InvPmBlkD's
  `pmAccG` and InvPmBlkE's `pmFinG` at the store `guard st (PmRSU s) (PmWSU s)`: `IoRS (ptU K) ⊆ PmRSU`
  (`pmRSU_ioRS`), `IoWS (ptU K) ⊆ PmWSU` (`pmWSU_ioWS`), aligned user words and the leaf's `PmRS` / `PmWS` are
  `PmRSU` / `PmWSU` words by definition);
* `PmObl5` = `PmObl4` without `blk`: [W] `mv`, [W] `roA`, [P] `cs`, [P] `lk`; `pmPathsI` (gen 13's `pmPathsG` with
  `acc` from `pm_blkG`; `RegionOKP K` is the family's layout hypothesis), `StartPmI` (= gen 14's `StartPmH`),
  `pm_hSFQI`, **`serializable_fl4_localW11PRIPmI`**.

Premises of `serializable_fl4_localW11PRIPmI` beyond `serializable_fl4_localW11PR`'s (`B : PmObl5`): [W] `mv`,
[W] `roA`, [P] `cs`, [P] `lk`. (Not named `…Pm3`: it still has [W] fields.)

No new named premise. New module; no existing statement changes.
-/
import Fl4Proofs.P2.InvPmBlkE
import Fl4Proofs.P2.InvPmRoot
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (Once ReadOnce StartAt SP)
open Fl4Proofs.P2.Serial (Cfg Init ArmInv NoLoc RunAll)

noncomputable section

section blk
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {μ : U64 → U64}
variable {A : Type} {ar : machine.Arch A}

/-- **`blk` at `PmPreG`** (gen 13's [W] `PmBlkUW2`, proved; module docstring). -/
theorem pm_blkG (hA : P0.ArchTotal ar) (hK : RegionOKP K) :
    PmBlkUW2 st ar p K Locks (PmPreG st Cs Ω Sg Ac Locks p K μ) := by
  intro s a info nx s1 s2 a1 buf length cap hE emi C _ hcap y hy
  have hG := hE.1.2.2
  have P := hE.1.2.1.1.1.1.ptU hG
  have hW : IoWr st (PmWSU st K Locks s) K.heap.scBits s :=
    (P.ioWr (Locks := Locks)).mono (fun _ hy => pmWSU_ioWS hK hy)
  obtain ⟨hdec, hrep⟩ := pmAccG (R := PmRSU st K Locks s) (W := PmWSU st K Locks s)
    (gS := guard st (PmRSU st K Locks s) (PmWSU st K Locks s)) hA hE (fun _ h => pmRSU_ioRS hG h)
    (fun b hb => ⟨hb.1, Or.inl hb.2⟩) (fun b hb => ⟨hb.1, Or.inr hb⟩) hW (fun _ h => pmWSU_ioWS hK h)
    (fun b hb => ⟨hb.1, Or.inl hb.2⟩) (fun b hb => ⟨hb.1, Or.inr hb⟩) emi C hcap hy
  refine ⟨hdec, fun z hz => ⟨hrep z hz, ?_⟩⟩
  have hsw : SWr (guard st (PmRSU st K Locks s) (PmWSU st K Locks s)) st (L.curW s) sched.TS_RUNNING :=
    SWr.of_W (pmWSU_ioWS hK (P.stw (Locks := Locks)).2)
  haveI : GRd (guard st (PmRSU st K Locks s) (PmWSU st K Locks s)) st (IoRS (st := st) K.ptU Locks s) :=
    grd_sub (fun _ hy => pmRSU_ioRS hG hy)
  exact pmFinG hA hE hW hsw emi C hcap hy hz

end blk

section slot
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- **What is left of the PageMap slot's obligations** (`PmObl4` without `blk`; module docstring). -/
structure PmObl5 (Cs Ω Sg Ac : Set U64) (Locks : S → U64 → Prop) : Prop where
  /-- [W] `move`. -/
  mv : ∀ (j : I64 × localinv.Plan) K m, PmMoveW st ar j.1 j.2 K Locks m (PmPreG st Cs Ω Sg Ac Locks j.2 K m)
  /-- [W] `ReadOnce` of accepting runs (the buffer word read once before its write). -/
  roA : ∀ (j : I64 × localinv.Plan) K m,
    PmRoAccW st ar j.1 j.2 K Locks m (R.invBodyPmG j.1 j.2) (PmPreG st Cs Ω Sg Ac Locks j.2 K m)
  /-- [P] the core set is below 64. -/
  cs : ∀ c ∈ Cs, c.val < 64
  /-- [P] the locks survive a user write. -/
  lk : PmLk st Locks

variable {st ar}

variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

end slot

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

end top

end
end Fl4Proofs.P2.E2EP
