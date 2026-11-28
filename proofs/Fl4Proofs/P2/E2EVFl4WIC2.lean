/-
P2 (line slhuf, gen 14): **`serializable_fl4_localWIC2`: `serializable_fl4_localWIC` without the [J] `nul`**
(new definitions only; no existing statement changes).

With fl4-core's raw-zero Copy / Mint target (`plan_with` requires the target's first word `0`; commit "fl4-core:
localinv Copy/Mint requires raw-zero dest"), the slot is at `inv_pathsKCM7` (P2/InvCMPathZ.lean), whose premises are
[P] only, and its record is invj's `InvPremW` (no VCPU, a bundle state, [P] `lk`): `cmSlotW2`, `fl4LocP3WIC2`,
`StartP3WIC2` (the Copy / Mint index asks `InvPremW` and `GlueAt` [P] with `InvQCMW` at the start state),
`startAt_P3WIC2`, **`serializable_fl4_localWIC2`** (W9's statement and premises), **`cmStartW_sat2`** (the record and
the entry fact at every chain state with a planned CNodeCopy / CNodeMint, no premise beyond `invStartW_sat`'s).
-/
import Fl4Proofs.P2.E2EVFl4WIC
import Fl4Proofs.P2.InvCMPathZ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
open Fl4Proofs.P2.OwnMap (fld oAFFINITY region TcbSlot InW InNode)
open Fl4Proofs.P2.E2E (StartAt SP LocalPath SerStep)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg)

noncomputable section
open Classical

section slot
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)

variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- **The Copy / Mint slot** (slhuf gen 14; at `inv_pathsKCM7`, no [J]; `AvoidV` by `avoidV_nv`). -/
def cmSlotW2 : SlotC (InvArg S) where
  Prem i K m := InvPremW st i K m
  path i K m hK hU h :=
    inv_pathsKCM7 (Cs := i.Cs) (Ω := i.Ω) (Sg := i.Sg) (Ac := i.Ac) (Locks := i.Locks) ar hA i.number i.p hm
      (h.hCs st) h.lk () K.toKLayout m hK.base hU.base
  Av i K m hK hU h := avoidV_nv h.nv _ (by
    dsimp only [inv_pathsKCM7, inv_pathsKCM6, inv_pathsKCM2, inv_pathsKCM, inv_localPathCM]
    exact nz_choose _)

end slot

section fam
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)

end fam

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

section sat
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- (slhuf gen 14) **The Copy / Mint slot's record and entry fact hold at every chain state with a non-idle current
thread whose CNodeCopy / CNodeMint invocation is planned** (module docstring; as invj's `invStartW_sat`; no [J]). -/
theorem cmStartW_sat2 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) {σe : S}
    {K : KLayoutV} {Ch : S → Prop} (hC : ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (nv : K.vcpus = ∅)
    {s : S} (hs : Ch s) (hct : NonIdle st arI AR MR s) {n : I64} {p : localinv.Plan}
    (hp : localinv.plan st s n = ok (some p)) (harm : InvCMArm st s) :
    ∃ Ac : Set U64, ∀ j : InvArg S, j.Cs = {c : U64 | c.val < K.ncores} → j.Ω = K.heap.omega →
      j.Sg = K.heap.frame → j.Ac = Ac → j.p = p → j.Locks = planLocks p →
      InvPremW st j K (L.mem s) ∧ InvQCMW st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K.toKLayout (L.mem s) s := by
  obtain ⟨Ac, BI⟩ := bunIx_of (L := L) (ChainOf.bun hC s hs)
  refine ⟨Ac, fun j e1 e2 e3 e4 e5 e6 => ?_⟩
  have hrun := chain_run P hIoa hC hs hct
  let i : IoArg S := ⟨n, j.Cs, j.Ω, j.Sg, j.Ac, j.Locks, fun _ _ _ => True⟩
  have BI' : BunIx (L := L) K.toKLayout K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns
      K.heap.scBits i.Ac s := by
    show BunIx (L := L) K.toKLayout K.heap.tcbs j.Cs j.Ω K.heap j.Sg K.heap.replies K.heap.scs K.heap.ntfns
      K.heap.scBits j.Ac s
    rw [e1, e2, e3, e4]; exact BI
  have hP := (IoEntJ7.of_bun st BI' hrun).toJ.pre
  refine ⟨⟨nv, ⟨s, BI'.ac⟩, fun _ _ _ _ _ _ _ => by rw [e6]; rfl⟩, ?_⟩
  rw [e5, e6]
  exact invQCMW_of_plan hP (fun _ _ => rfl) hp harm (fun k x hk hx => ⟨k, hk, hx⟩)

end sat

end
end Fl4Proofs.P2.E2EV
