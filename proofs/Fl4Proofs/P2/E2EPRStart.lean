/-
# P2 (line pte, gen 8): the reachability convention at the starts of an epoch

The glue's choice at every epoch start `s1` (the execution's start, or a serial step's target) is
**`PteConvR K s1`**: `K.ptes = ptesR K s1.mem` and no VCPU (`P2/PteReach.lean`). It is always available (a definition
of the memory) and, by `ptesR`'s filters, gives the serial step's `RegionOKP` / `UserOKP` from `RegionOKV` /
`UserOKV` (`pteConvR_ok`). No memory link at the serial exit is needed.

At a state `s` of an `ExecP` whose epoch start chose the convention, a store state `σ` that is a bundle state of
`K.toKLayout` and agrees with `s.mem` on the aligned non-user words (a start state: `StartAt`'s memory link and the
chain's `ChainLay.bun`) agrees with the epoch start's memory on the gate words (`exec_epoch`): **`gateAg_at`**. So:
* **`qPs_at_startR`**: `QPs K st σ` (the start fact `StartQP`'s `QPs` half, `E2EPW11`);
* **`ptesR_at_run`**: the entry a writing PageMap run writes from `σ` is in `K.ptes` (`PtePlanLocked`'s [J] half,
  weakened to the runs that write: `find_vspace_for_asid` found the root, `lookup_pt_slot` the entry).

No named premise; no existing statement changed; new file only.
-/
import Fl4Proofs.P2.PteReach
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (StartAt SP SerStep)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll Step)
open Fl4Proofs.P3.Vs (UserV)

section start
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **The reachability convention at an epoch start** (module docstring). -/
def PteConvR (K : KLayoutP) (s1 : Cfg U64 U64 U64 U64) : Prop := K.ptes = ptesR K s1.mem ∧ K.vcpus = ∅

/-- The convention gives the serial step's PTE facts. -/
theorem pteConvR_ok {K : KLayoutP} {s1 : Cfg U64 U64 U64 U64} (h : PteConvR K s1) (hK : RegionOKV K.toKLayoutV)
    (hU : UserOKV K.toKLayoutV) : RegionOKP K ∧ UserOKP K :=
  ⟨regionOKP_R hK h.1, userOKP_R hU h.1⟩

/-- **A start state agrees with its epoch start on the gate words.** -/
theorem gateAg_at {ι : Type} {LP : PathsP ι} {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP}
    (h0 : Init s0) (hA0 : ArmInv s0) (hK0 : RegionOKP K0) (hU0 : UserOKP K0) (hM0 : MapsP K0 s0)
    (h : ExecP LP s0 K0 s K) (hEp : ∀ s1, EpochStart LP s0 K0 s1 K → PteConvR K s1) {σ : S}
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = s.mem x) :
    ∃ s1 : Cfg U64 U64 U64 U64, PteConvR K s1 ∧ GateAg st K s1.mem σ := by
  obtain ⟨s1, hS1, hkeep⟩ := exec_epoch h0 hA0 hK0 hU0 hM0 h
  obtain ⟨he, nv⟩ := hEp s1 hS1
  refine ⟨s1, ⟨he, nv⟩, fun w hr hp hu ha => ?_⟩
  rw [hμ w ha hu]
  exact hkeep w (gateW_of_region hr (by rw [he]; exact hp) nv)

/-- **`QPs` at every start of an epoch under the convention.** -/
theorem qPs_at_startR {ι : Type} {LP : PathsP ι} {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP}
    (h0 : Init s0) (hA0 : ArmInv s0) (hK0 : RegionOKP K0) (hU0 : UserOKP K0) (hM0 : MapsP K0 s0)
    (h : ExecP LP s0 K0 s K) (hEp : ∀ s1, EpochStart LP s0 K0 s1 K → PteConvR K s1) {σ : S}
    (hJ : SlJAt (L := L) K.toKLayout σ) (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = s.mem x) :
    QPs K st σ := by
  obtain ⟨s1, ⟨he, nv⟩, hag⟩ := gateAg_at h0 hA0 hK0 hU0 hM0 h hEp hμ
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', τ, B⟩ := hJ
  exact qPs_R B hag he nv

/-- **`PtePlanLocked`'s [J] half for a writing run from a start state, under the convention.** -/
theorem ptesR_at_run {ι : Type} {LP : PathsP ι} {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP}
    (h0 : Init s0) (hA0 : ArmInv s0) (hK0 : RegionOKP K0) (hU0 : UserOKP K0) (hM0 : MapsP K0 s0)
    (h : ExecP LP s0 K0 s K) (hEp : ∀ s1, EpochStart LP s0 K0 s1 K → PteConvR K s1) {σ : S}
    (hJ : SlJAt (L := L) K.toKLayout σ) (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = s.mem x)
    {asid r v e : U64} (hf : vspace.find_vspace_for_asid st σ asid = ok (.Ok r)) (hv : UserV v)
    (hl : vspace.lookup_pt_slot st σ r v = ok (.Ok e)) : e ∈ K.ptes := by
  obtain ⟨s1, ⟨he, nv⟩, hag⟩ := gateAg_at h0 hA0 hK0 hU0 hM0 h hEp hμ
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', τ, B⟩ := hJ
  rw [he]
  exact ptesR_of_run B hag nv hf hv hl

end start

end Fl4Proofs.P2.E2EP
