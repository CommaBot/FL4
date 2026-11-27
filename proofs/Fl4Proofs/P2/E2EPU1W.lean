/-
# P2 (line unify, gen 1): every slot in one family — `serializable_fl4_localU1W` (two [W]: PTE avoidance)

`serializable_fl4_localU1G` (P2/E2EPU1.lean) at `LQ := (delPteSlot ⊕ invSlotP) ⊕ cmSlotP`: the eight W11 slots of
PJ12 (with `yb`), the mapped-frame Delete slot (invj gen 8, native `ownP`), and the two `ownV` invocation slots
CNodeDelete without a PTE lock (invj `invSlotW`, WI) and Copy / Mint (slhuf `cmSlotW2`, WIC2), each restricted to
`QPs` states, PTE-cut and lifted to `ownP` exactly as `fl4LocW11JA` does for the eight W11 slots.

**Why two [W] premises.** A path stated for `ownV` enters an `ownP` family only through `LocalPath.cutLiftP`, which
needs `AvoidP K P` (P2/E2EPCut.lean: the accepted run on `guard (IoRS s ∖ ptes) (WS s)`, the declining runs from
every alternative reading no PTE word, the program premise on the cut set's alternatives). Under `ownV` a leaf PTE
word is region `.none`, so `own` gives it to the gate and `IoRS` *contains* it (`RPerm` = held ∨ `GateOnly`); the
WI / WIC2 proofs bound reads by `IoRS` only, so they say nothing about PTE words. Each of the eight W11 slots has its
own avoidance proof (`allA`: `vmF/vmR/vt_avoidPJ_pathA`, `io/stm/irq/sl/vx_avoidPJ`); WI and WIC2 have none. So:

* `AvInvW` [W] — PTE avoidance of the CNodeDelete (no PTE lock) path at `QPs` states;
* `AvCMW` [W] — PTE avoidance of the Copy / Mint path at `QPs` states.

They are new proof obligations, not conventions: no existing statement of invj / slhuf implies them. What a proof
needs (handoff `unify.md`): declines are covered by `inv_dec_guardRS` at `userP K` (`ioPre_userP`, `alt_userP`;
`hSeen` slot words are no PTE by `RegionOKP.none`); the accepted runs need the acc chain at a read set without leaf
PTEs — `IoRSR`-scripted copies (invj gen 7) of the CNodeDelete chain (whose decode walks the page tables for a
stale-mapped frame cap: `VsRdG (VsW ∧ ¬ ptes)`, `SlJAtZ.vsRdX`) and of the Copy / Mint chain (no walk).

With them as hypotheses everything else is proved here: `invSlotP` / `cmSlotP` (the cut lifts, `LocalPath.void`
where the record fails), `InvStartU` / `CMStartU` (record + `GlueAt` [P] with `InvQF` / `InvQCMW`, armed program
`cutP` of the `ownV` program, as every W11 slot's), `invStartU_at` / `cmStartU_at` (`StartAt` from the chain and the
epoch data: `QPs` by `qPs_of_convR`), `StartInvU`, **`serializable_fl4_localU1W`**, and the satisfiability lemmas
`invStartU_sat` / `cmStartU_sat` (from `invStartW_sat` / `cmStartW_sat2`, `m := L.mem s`).
-/
import Fl4Proofs.P2.E2EPU1
import Fl4Proofs.P2.E2EVFl4WIC2
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld)
open Fl4Proofs.P2.E2E (StartAt SP SerStep)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg)

noncomputable section
open Classical

section slot
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- **The CNodeDelete slot's start fact** [P]: the record and `GlueAt` with `InvQF` (as `StartP3WI`), the armed
program the cut of the `ownV` program. -/
def InvStartU (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (q : SP) (j : InvArg S) : Prop :=
  ∃ q0, (∃ h : InvPremW st j K.toKLayoutV m,
      GlueAt ((invSlotW st ar hA hm).liftAt j K.toKLayoutV m hK.base hU.base h)
        (fun σ : S => Ch σ ∧ InvQF st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K.toKLayout m σ) c hs m q0) ∧
    q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c q0 ∅

/-- **The Copy / Mint slot's start fact** [P]: the record and `GlueAt` with `InvQCMW` (as `StartP3WIC2`). -/
def CMStartU (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (q : SP) (j : InvArg S) : Prop :=
  ∃ q0, (∃ h : InvPremW st j K.toKLayoutV m,
      GlueAt ((cmSlotW2 st ar hA hm).liftAt j K.toKLayoutV m hK.base hU.base h)
        (fun σ : S => Ch σ ∧ InvQCMW st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K.toKLayout m σ) c hs m q0) ∧
    q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c q0 ∅

variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

end slot

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

end top

section sat
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st] {A : Type}
  (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **The CNodeDelete slot's start fact holds at every chain state planning a CNodeDelete with no PTE lock**
(`invStartW_sat`'s record and entry at `m := L.mem s`; no core-count assumption). -/
theorem invStartU_sat (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) {σe : S}
    {K : KLayoutP} {Ch : S → Prop} (hC : ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (nv : K.vcpus = ∅)
    (hK : RegionOKP K) (hU : UserOKP K)
    {s : S} (hs : Ch s) (hct : NonIdle st arI AR MR s) {n : I64} {p : localinv.Plan}
    (hp : localinv.plan st s n = ok (some p)) (harm : InvArm st p s) (a : A) :
    ∃ Ac : Set U64, ∀ j : InvArg S, j.Cs = {c : U64 | c.val < K.ncores} → j.Ω = K.heap.omega →
      j.Sg = K.heap.frame → j.Ac = Ac → j.p = p → j.Locks = planLocks p →
      ∃ q, InvStartU st ar hA hm Ch K (L.mem s) hK hU (L.cpu s) (j.Locks s) q j := by
  obtain ⟨Ac, H⟩ := invStartW_sat (K := K.toKLayoutV) st P hIoa hC nv hs hct hp harm
  refine ⟨Ac, fun j e1 e2 e3 e4 e5 e6 => ?_⟩
  obtain ⟨h, hQ⟩ := H j e1 e2 e3 e4 e5 e6
  exact ⟨_, _, ⟨h, s, a, ⟨hs, hQ⟩, rfl, rfl, fun _ _ _ => rfl, rfl⟩, rfl⟩

/-- **The Copy / Mint slot's start fact holds at every chain state planning a CNodeCopy / CNodeMint**
(`cmStartW_sat2`'s record and entry at `m := L.mem s`). -/
theorem cmStartU_sat (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) {σe : S}
    {K : KLayoutP} {Ch : S → Prop} (hC : ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (nv : K.vcpus = ∅)
    (hK : RegionOKP K) (hU : UserOKP K)
    {s : S} (hs : Ch s) (hct : NonIdle st arI AR MR s) {n : I64} {p : localinv.Plan}
    (hp : localinv.plan st s n = ok (some p)) (harm : InvCMArm st s) (a : A) :
    ∃ Ac : Set U64, ∀ j : InvArg S, j.Cs = {c : U64 | c.val < K.ncores} → j.Ω = K.heap.omega →
      j.Sg = K.heap.frame → j.Ac = Ac → j.p = p → j.Locks = planLocks p →
      ∃ q, CMStartU st ar hA hm Ch K (L.mem s) hK hU (L.cpu s) (j.Locks s) q j := by
  obtain ⟨Ac, H⟩ := cmStartW_sat2 (K := K.toKLayoutV) st P hIoa hC nv hs hct hp harm
  refine ⟨Ac, fun j e1 e2 e3 e4 e5 e6 => ?_⟩
  obtain ⟨h, hQ⟩ := H j e1 e2 e3 e4 e5 e6
  exact ⟨_, _, ⟨h, s, a, ⟨hs, hQ⟩, rfl, rfl, fun _ _ _ => rfl, rfl⟩, rfl⟩

end sat

end
end Fl4Proofs.P2.E2EP
