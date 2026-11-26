/-
# P2 (line invj, generation 8): the Delete PTE-arm slot on the invocation-index family (`serializable_fl4_localW11PRID`)

The CNodeDelete path for a target holding a live-mapped small frame cap (the plan's PTE arm, `InvQFP`) as an `ownP`
slot of pte's invocation-index family (P2/E2EPW11RI.lean), and the end-to-end theorem over it:

* `DelPtePrem` (the slot's record: no VCPU, a bundle state at the index's core / active-SC sets — `Cs` below 64 —,
  and [P] `lk`, the locks kept by an aligned user write, as invj's `InvPremW`);
* **`delPteSlot : PathsP (InvArg S)`**: `inv_localPathPP` (P2/InvDelPteOnceP.lean) where the record holds, a
  never-starting path (`LocalPath.void`) elsewhere;
* **`DelPteStart`** (the slot's start fact: the record and `GlueAt` [P] with the entry fact `InvQFP` at the start
  state, as every other slot's) and **`delPteStart_at`**: `StartAt` of the slot from it, given the chain and the
  epoch data of `execP_of_WPRI` — `PreP`'s `CvP` is the epoch start's memory (`K.ptes = ptesR K s1.mem`, and the
  start state agrees with it on the gate words: the glue's memory link and `gateW_of_region`);
* **`serializable_fl4_localW11PRID`**: `serializable_fl4_localW11PRI` at `LQ := delPteSlot`, `SFQ := DelPteStart`;
* **`delPteStart_sat`** (satisfiability): at every chain state with a non-idle current thread whose syscall is
  planned as a CNodeDelete of a target holding a mapped small frame cap with a non-zero ASID and a live (non-zero)
  page-table entry (`invArmP_of`, P2/InvDelPtePlanLt.lean), and a PTE set by the reachability convention at a
  memory agreeing with the state on the gate words (`CvP`, what an epoch start gives), the record and the entry
  `PreP` hold for the canonical index (the plan's locks, `planLocks`) — on any layout with no VCPU; no assumption on
  the number of cores. The slot is not vacuous.

**The TCB `AFFINITY` agreement** (`hmA` of `invMovePP`) is part of `PreP` itself (`InvQFP` → `IoQ`, second half),
discharged pointwise from the entry state (`h.2.1.1.1.2`), kept by user writes (`ioQ_wr`) and supplied at the start
by `GlueAt`'s memory `m` (at `delPteStart_sat`: `m := L.mem s`, `rfl`). It is no ∀-`Pre` record field.

Premises of `serializable_fl4_localW11PRID`: `serializable_fl4_localW11PR`'s (`P`, `hIoa` [P], `h0`, `hA0`, `hB`,
`hc0`, `hM0`, the execution `h`, `hq`); the new slot's start obligation is `DelPteStart` (`DelPtePrem.lk` [P],
`GlueAt` [P] with `InvQFP`). No new [J] / [W]; no existing statement or file changed.
-/
import Fl4Proofs.P2.E2EPW11RI
import Fl4Proofs.P2.InvDelPteOnceP
import Fl4Proofs.P2.InvDelPtePlanLt
import Fl4Proofs.P2.E2EVFl4WIS
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

/-- **The Delete PTE-arm slot's premises at `K`** (module docstring). -/
structure DelPtePrem (i : InvArg S) (K : KLayoutP) : Prop where
  /-- No VCPU in the layout (P3's scope). -/
  nv : K.vcpus = ∅
  /-- Some bundle state of the layout with the index's core / active-SC sets as its ghosts (as `InvPremW.bunS`). -/
  bunS : ∃ σ : S, SlJAtS (L := L) K.toKLayout i.Cs i.Ac σ
  /-- [P] The locks are kept by an aligned user-word write at a bundle state (as `InvPremW.lk`). -/
  lk : ∀ (K' : OwnMap.KLayout) (s : S) (b v : U64), SlJAt (L := L) K' s → b ∈ K'.user → Aligned b →
    i.Locks (L.wr s b v) = i.Locks s

theorem DelPtePrem.hCs {i : InvArg S} {K : KLayoutP} (h : DelPtePrem st i K) : ∀ c ∈ i.Cs, c.val < 64 := by
  obtain ⟨σ, A', arI, AR, Zx, Lst, D, a', τ, B⟩ := h.bunS
  exact fun c hc => B.j.kern.csLt c hc

variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- The slot's path where its premises hold. -/
noncomputable def delPtePath (i : InvArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : DelPtePrem st i K) :
    E2E.LocalPath (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) :=
  inv_localPathPP (Cs := i.Cs) (Ω := i.Ω) (Sg := i.Sg) (Ac := i.Ac) (Locks := i.Locks) ar hA i.number i.p hm
    (h.hCs st) h.lk K m hK hU h.nv

/-- **The Delete PTE-arm slot** (module docstring). -/
noncomputable def delPteSlot : PathsP (InvArg S) :=
  fun i K m hK hU => if h : DelPtePrem st i K then delPtePath st ar hA hm i K m hK hU h
    else E2EV.LocalPath.void (fl4Dflt st ar hm)
      (fun x hx => Fl4Proofs.P2.ko_aligned hK.base.base hU.base.base x hx)

theorem delPteSlot_pos {i : InvArg S} {K : KLayoutP} {m : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K}
    (h : DelPtePrem st i K) : delPteSlot st ar hA hm i K m hK hU = delPtePath st ar hA hm i K m hK hU h :=
  dif_pos h

/-- **The slot's start fact** (module docstring): the record and `GlueAt` [P] with the entry fact `InvQFP`. -/
def DelPteStart (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (q : SP) (j : InvArg S) : Prop :=
  ∃ h : DelPtePrem st j K, GlueAt (delPtePath st ar hA hm j K m hK hU h)
    (fun σ : S => Ch σ ∧ InvQFP st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K.toKLayout m σ) c hs m q

variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **`StartAt` of the slot from its start fact**, given the chain and the epoch data (module docstring). -/
theorem delPteStart_at [Fl4Proofs.P1.PlainStore st] {Ch : S → Prop} {K : KLayoutP} {m : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K}
    {c : U64} {hs : U64 → Prop} {q : SP} {j : InvArg S}
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch)
    (hEp : ∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → m x = s1.mem x)
    (h : DelPteStart st ar hA hm Ch K m hK hU c hs q j) :
    StartAt (delPteSlot st ar hA hm j K m hK hU) c hs m q := by
  obtain ⟨σe, hC⟩ := hC
  have hCh := ChainOf.bun hC
  obtain ⟨s1, ⟨nv, hc⟩, hk⟩ := hEp
  obtain ⟨h, hG⟩ := h
  rw [delPteSlot_pos st ar hA hm h]
  refine hG.startAt fun σ he hμ => ⟨hCh σ he.1, he.2, s1.mem, hc, fun w hr hp hu ha => ?_⟩
  exact (hμ w ha hu).trans (hk w (gateW_of_region hr (by rw [hc]; exact hp) nv))

end slot

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- (invj gen 8) **FL4 end to end over the invocation-index family with the Delete PTE-arm slot** (module
docstring): `serializable_fl4_localW11PRI` at `LQ := delPteSlot`, `SFQ := DelPteStart`. -/
theorem serializable_fl4_localW11PRID (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPR (PathsP.sum (fl4LocW11J st ar hA hm hSt a0) (delPteSlot st ar hA hm))
      (StartW11RI st ar hA hm hSt a0 arI AR MR (DelPteStart st ar hA hm)) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_fl4_localW11PRI st ar hA hm hSt a0 P hIoa (delPteSlot st ar hA hm)
    (fun _ _ _ _ _ _ _ _ _ hC hEp hS => delPteStart_at st ar hA hm hC hEp hS) h0 hA0 hB hc0 hM0 h hq

end top

section sat
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- (invj gen 8) **The slot's record and entry hold at every chain state planning a Delete of a live-mapped frame
cap** (module docstring). Inputs: `nv` (no VCPU, as every P3 slot), `hIoa` [P] / `P` (as `chain_run`), `hct` [P]
(non-idle current thread), `hp` (the plan), `hlbl` / `hmap` (the Delete of a live-mapped small frame cap), the
convention `hc` / `hag` at a memory `m1` (an epoch start's). -/
theorem delPteStart_sat (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) {σe : S}
    {K : KLayoutP} {Ch : S → Prop} (hC : ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (nv : K.vcpus = ∅)
    {s : S} (hs : Ch s) (hct : NonIdle st arI AR MR s) {n : I64} {p : localinv.Plan}
    (hp : localinv.plan st s n = ok (some p))
    (hlbl : ∀ t info, sched.cur_thread st s = ok t → msg.msg_info st s t = ok info →
      info.label = fl4_abi.label.CNodeDelete)
    (hmap : ∀ cp cr cg cgb dest, obj.Slot.cap st p.slot s = ok (.CNode cp cr cg cgb) →
      cspace.lookup_target_slot st s (.CNode cp cr cg cgb) (L.mem s (regA (L.curW s) layout.reg.R10))
        (L.mem s (regA (L.curW s) layout.reg.R8)) = ok (.Ok dest) →
      ∃ fp rt asid va e, obj.Slot.cap st dest s = ok (.Frame fp .Small rt false true false asid va) ∧
        asid ≠ 0#u64 ∧ localinv.small_page_entry st s asid va = ok (some e) ∧ e ≠ 0#u64)
    {m1 : U64 → U64} (hc : K.ptes = ptesR K m1) (hag : GateAg st K m1 s) :
    ∃ Ac : Set U64, ∀ j : InvArg S, j.Cs = {c : U64 | c.val < K.ncores} → j.Ω = K.heap.omega →
      j.Sg = K.heap.frame → j.Ac = Ac → j.p = p → j.Locks = planLocks p →
      DelPtePrem st j K ∧ PreP st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K (L.mem s) s := by
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
  refine ⟨⟨nv, ⟨s, BI'.ac⟩, fun _ _ _ _ _ _ _ => by rw [e6]; rfl⟩, ChainOf.bun hC s hs, ?_, m1, hc, hag⟩
  rw [e5, e6]
  exact ⟨⟨⟨hP, fun _ _ => rfl⟩, planD_of_plan hp, invArmP_of hp hlbl hmap, fun k x hk hx => ⟨k, hk, hx⟩⟩,
    invLk_of_plan hp⟩

end sat

end
end Fl4Proofs.P2.E2EP
