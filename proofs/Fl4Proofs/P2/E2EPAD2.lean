/-
# P2 (line mmuAD, gen 17): **one A/D top with PageMap in both epochs** — `serializable_fl4_localAD2`

`serializable_fl4_localAD` (P2/E2EPAD.lean) runs every U1 slot in native and VM epochs and PageMap in native epochs
only. FL4 also runs PageMap in VM epochs (fl4-sync `local_invocation`, lib.rs l. 538, plans a frame-cap invocation
with no VCPU condition) and stores a present PTE there (vspace.rs `write_mapping` l. 446). This module adds that
case:

* **`famAD2`** = `famAD` ⊕ E2EPAD2D's **`pmSlotVX`** (the PageMap path at `PmPreGX`: `InvLX` in place of P3's
  `SlJAt`, `PmGX` in place of the native epoch data `GateEp`; every path obligation proved in E2EPAD2A–D);
* **`StartAD2`** = `StartAD` ⊕ **`PmStartX`** (E2EPAD2D: `K.vcpus ≠ ∅`, the record `PmPremX`, VX9's [S] record
  `InvEntV9` at `G := PmEntG`, `GlueAt` data [P]); **`ad2_startAt`** (`ad_startAt` ⊕ `pmStartX_at`);
* **`serializable_fl4_localAD2`**: `serializable_VXD_of` with `famAD`'s `hIns` cases (copied from
  `serializable_fl4_localAD`) and, for the new slot, E2EPAD2E's **`insAP_pmX`** (gen 11–12's walk at the VM layout,
  restricted by `TabKU`; the present store is deferred as natively, `InsAP`'s done set).

## Premise diff vs `serializable_fl4_localAD`
* Theorem premises: identical (`P`, [P] `hIoa`, `B : PmObl7`, `h0`, `hA0`, `hB`, `hc0`, `hM0`, the execution over
  `ExecVX4d` — [P] `MmuAD`, [S] `VmPweT` at VM serial exits — and `hq`). No [W], no [J].
* The execution's start facts get one more case, the VM-epoch PageMap start `PmStartX`. Its [S] content is VX9's
  record `InvEntV9` (`hz`, `ent`, `qps`, as for CNodeDelete / delPte) at the entry part `PmEntG` = U1P's PageMap
  entry facts `PmQF ∧ PmEx ∧ PmRoot` (natively from the glue's plan and P3's ASID map), vmscope gen 10's walk fact
  `WalkP` (as for delPte) and **`ne0`** (no walk answers the null entry address; natively `SlJAtZ.spe_ne0`; PT
  objects are retyped from untyped memory, never physical page 0). Justification: E2EPAD2D's module docstring. Its
  [P]s are `PmPremX.lk` (= VX8's `InvPremX.lk`) and the `GlueAt` data, as every VM-epoch slot.

No sorry / admit / native_decide / bv_decide. New module; no existing statement changes.
-/
import Fl4Proofs.P2.E2EPAD2E
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg HwWr allowed_of_sinv
  InsA InsAP insAP_of_insA ARunD aRunD_inv serializable_safeD IgnG)
open Fl4Proofs.P2.MmuAD (MmuAD ADEq NotPresent adEq_equiv adEq_trans adOr_adEq)

noncomputable section
open Classical

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **The union family with PageMap in VM epochs**: `famAD` ⊕ `pmSlotVX`. -/
abbrev famAD2 {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl7 st Cs Ω Sg Ac Locks) :=
  PathsP.sum (famAD st ar hA a0 B) (pmSlotVX st ar hA (masksWr_plain st))

/-- Its start facts: `StartAD` ⊕ `PmStartX`. -/
abbrev StartAD2 {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl7 st Cs Ω Sg Ac Locks) :=
  fun (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
      (hs : U64 → Prop) (q : SP) =>
    Sum.elim (StartAD st ar hA a0 B (arI := arI) (AR := AR) (MR := MR) Ch K m hK hU c hs q)
      (PmStartX st ar hA (masksWr_plain st) K m hK hU c hs q)

/-- **The start case split** (`ad_startAt` ⊕ `pmStartX_at`). -/
theorem ad2_startAt (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl7 st Cs Ω Sg Ac Locks) :
    ∀ (Ch : S → Prop) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) c hs q i,
      (K.vcpus = ∅ → NatEp P K Ch s) → (K.vcpus ≠ ∅ → VtxBundle4 st L K) →
      StartAD2 st ar hA a0 B (arI := arI) (AR := AR) (MR := MR) Ch K s.mem hK hU c hs q i →
      StartAt (famAD2 st ar hA a0 B i K s.mem hK hU) c hs s.mem q := by
  intro Ch K s hK hU c hs q i hN hV hsf
  rcases i with i | j
  · exact ad_startAt st ar hA a0 P hIoa B Ch K s hK hU c hs q i hN hV hsf
  · have hsf' : PmStartX st ar hA (masksWr_plain st) K s.mem hK hU c hs q j := hsf
    exact pmStartX_at (hV hsf'.1) hsf'

/-- **FL4 end to end with the host walker's A/D writes, every U1 slot and PageMap in native and VM epochs**
(module docstring). Premises: `serializable_fl4_localAD`'s (`P`, [P] `hIoa`, `B` = [P] `cs` / [P] `lk`, `h0`,
`hA0`, `hB`, `hc0`, `hM0`, the execution, `hq`), with the execution's start facts extended by `PmStartX` ([S]
`InvEntV9` at `PmEntG`). No [W]. -/
theorem serializable_fl4_localAD2 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl7 st Cs Ω Sg Ac Locks)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecVX4d (famAD2 st ar hA a0 B) (StartAD2 st ar hA a0 B (arI := arI) (AR := AR) (MR := MR))
      P s0 K0 Ch0 s K Ch E)
    (hq : NoLoc s) :
    ∃ ℓ : List SP, ℓ.Perm s.log ∧ RunAll ℓ s0.mem s.mem := by
  refine serializable_VXD_of P (ad2_startAt st ar hA a0 P hIoa B) ?_ h0 hA0 hB hc0 hM0 h hq
  intro Ch K E s hK hU c hs q i hX hV hW J hM hsf hP
  rcases i with i | j
  swap
  · have hsf' : PmStartX st ar hA (masksWr_plain st) K s.mem hK hU c hs q j := hsf
    exact insAP_pmX hA (masksWr_plain st) K E s hK hU c hs q j (hW hsf'.1) J hM hP
  rcases i with ((((((((((i | j) | j) | j) | j) | j) | j) | j) | j) | j) | j) | j
  · have hsf' : K.vcpus = ∅ ∧ StartU1P st ar hA a0 B (arI := arI) (AR := AR) (MR := MR) Ch K s.mem hK hU c hs
        q i := hsf
    have nv := hsf'.1
    have J' := J.toJ nv
    have hb : ∃ σe, SlJAt (L := L) K.toKLayout σe := by
      obtain ⟨σe, hC'⟩ := (hX nv).chainOf
      have hσe : Ch σe := by
        obtain ⟨_, _, _, _, _, _, _, _, h'⟩ := hC'
        exact h'
      exact ⟨σe, ChainOf.bun hC' σe hσe⟩
    rcases i with i | (((j | j) | j) | j)
    · exact insAP_of_insA (insA_w11 st ar hA (masksWr_plain st) L.total a0 i (hK := hK) (hU := hU) hb J' hM hP)
    · exact insAP_of_insA (insA_delR st ar hA (masksWr_plain st) j (hK := hK) (hU := hU) hb J' hM hP)
    · exact insAP_of_insA (insA_invR st ar hA (masksWr_plain st) j (hK := hK) (hU := hU) hb J' hM hP)
    · exact insAP_of_insA (insA_cm st ar hA (masksWr_plain st) j (hK := hK) (hU := hU) hb J' hM hP)
    · exact insAP_pmR hA (masksWr_plain st) B (pmAccIns st ar hA (masksWr_plain st) B) K E s hK hU c hs q j
        hb J' hM hP
  · have hsf' : VxStartV2 st ar hA (masksWr_plain st) K s.mem hK hU c hs q j := hsf
    have hne := vxStartV2_ne hsf'
    exact insAP_of_insA (insAW_vx st ar hA (masksWr_plain st) K E s hK hU c hs q j hne (hV hne) (hW hne).toVmPwe
      J hM hP)
  · have hsf' : VtStartV4 st ar hA (masksWr_plain st) K s.mem hK hU c hs q j := hsf
    exact insAP_of_insA (insAW_vt st ar hA (masksWr_plain st) K E s hK hU c hs q j hsf'.1 (hV hsf'.1)
      (hW hsf'.1).toVmPwe J hM hP)
  · have hsf' : IoStartX5 st ar hA (masksWr_plain st) K s.mem hK hU c hs q j := hsf
    exact insAP_of_insA (insAW_io st ar hA (masksWr_plain st) K E s hK hU c hs q j hsf'.1 (hV hsf'.1)
      (hW hsf'.1).toVmPwe J hM hP)
  · have hsf' : StStartX st ar hA (masksWr_plain st) K s.mem hK hU c hs q j := hsf
    exact insAP_of_insA (insAW_st st ar hA (masksWr_plain st) K E s hK hU c hs q j hsf'.1 (hV hsf'.1)
      (hW hsf'.1).toVmPwe J hM hP)
  · have hsf' : IrqStartX st ar hA (masksWr_plain st) K s.mem hK hU c hs q j := hsf
    exact insAP_of_insA (insAW_irq st ar hA (masksWr_plain st) K E s hK hU c hs q j hsf'.1 (hV hsf'.1)
      (hW hsf'.1).toVmPwe J hM hP)
  · have hsf' : SlStartX st ar hA (masksWr_plain st) L.total a0 K s.mem hK hU c hs q j := hsf
    exact insAP_of_insA (insAW_sl st ar hA (masksWr_plain st) L.total a0 K E s hK hU c hs q j hsf'.1 (hV hsf'.1)
      (hW hsf'.1).toVmPwe J hM hP)
  · have hsf' : InvStartX9 st ar hA (masksWr_plain st) K s.mem hK hU c hs q j := hsf
    exact insAP_of_insA (insAW_inv st ar hA (masksWr_plain st) K E s hK hU c hs q j hsf'.1 (hV hsf'.1)
      (hW hsf'.1) J hM hP)
  · have hsf' : CMStartX9 st ar hA (masksWr_plain st) K s.mem hK hU c hs q j := hsf
    exact insAP_of_insA (insAW_cm st ar hA (masksWr_plain st) K E s hK hU c hs q j hsf'.1 (hV hsf'.1)
      (hW hsf'.1).toVmPwe J hM hP)
  · have hsf' : DelPteStartX st ar hA (masksWr_plain st) K s.mem hK hU c hs q j := hsf
    exact insAP_of_insA (insAW_del st ar hA (masksWr_plain st) K E s hK hU c hs q j hsf'.1 (hV hsf'.1)
      (hW hsf'.1) J hM hP)
  · have hsf' : VmFStartY st ar hA (masksWr_plain st) K s.mem hK hU c hs q j := hsf
    exact insAP_of_insA (insAW_vmF st ar hA (masksWr_plain st) K E s hK hU c hs q j hsf'.1 (hV hsf'.1)
      (hW hsf'.1).toVmPwe J hM hP)
  · have hsf' : VmRStartY st ar hA (masksWr_plain st) K s.mem hK hU c hs q j := hsf
    exact insAP_of_insA (insAW_vmR st ar hA (masksWr_plain st) K E s hK hU c hs q j hsf'.1 (hV hsf'.1)
      (hW hsf'.1).toVmPwe J hM hP)

end top

end
end Fl4Proofs.P2.E2EP
