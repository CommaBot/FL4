/-
# P2 (line p3mc, gen 44): the CoreView PageMap slot over `pmPathsK` — `PmObl4`'s three [W]s gone from the top

Gen 43's authoritative PageMap top `serializable_fl4_V15_pmV` carried `B : PmObl4` ([W] `blk`, `mv`, `roA`; [P] `cs`,
`lk`). The mmuAD line (merged in int26) discharged the three [W]s at `PmPreG` for every `K` with `RegionOKP K`
(`UserOKP K` for `mv`): `pm_blkG` (P2/InvPmBlkF.lean), `pm_mvG` (P2/InvPmMvC.lean), `pm_roAG` (P2/InvPmRoE.lean), and
built the slot family `pmPathsK B7` (P2/InvPmRoE.lean) over `B7 : PmObl7` = [P] `cs`, [P] `lk` only. Since the view
precondition *is* `PmPreG` (`pmPreV_eq`, P2/E2EPV15PmV.lean) and `PathsP` is memory-parametric, the swap is a family
change only:

* **`fl4LocV13PmK B7`** = `fl4LocV13 ⊕ pmPathsK B7`; start fact **`StartV13PmK`**: V13's on `.inl`, InvPmRoE's own
  `StartPmK` [P] (at the view's memory; no `PmRoot`, no `GateEp`: both are derived, `pmRoot_of_qf` and
  `gateEp_viewStart`) on `.inr`; **`ExecCfg.nativePmK B7`** (`VcpuOK := vcpus = ∅`, `AdStep := False`).
* **`pmStartK_at`** (`sf` at PageMap), **`PmFhK B7`** [J] (gen 42's `PmFhV` restated over `pmPathsK` / `StartPmK`),
  **`slotOblV13PmK`**, `nativePmK_noAd`, `nativePmK_vcpuNone`.
* **`serializable_fl4_V15_pmK`** — premises `P`, `hIoa`, `B7 : PmObl7` ([P] `cs`, `lk`), `PmFhK B7` [J], `h0`, `hA0`,
  `hB`, `hc0`, `hM0`, `ExecV15 (ExecCfg.nativePmK B7)`, `hq` ⇒ `RunAll s.log s0.mem s.mem` (exact). **No `PmObl4` /
  `PmObl4V`.**
* Old from new: **`pmObl7_of4`** (`PmObl4 → PmObl7`), **`pmPathsG_eq_K`** (`pmPathsG B = pmPathsK (pmObl7_of4 B)`,
  `rfl`: the two families differ only in proof arguments), **`pmFhK_of_V`** (`PmFhV B → PmFhK (pmObl7_of4 B)`),
  **`serializable_fl4_V15_pmVofK`**: gen 43's `serializable_fl4_V15_pmV` statement from the new top;
  **`serializable_fl4_localV13ofV15PmK`**: V13 from the new top.

Premise diff against `serializable_fl4_V15_pmV`: `B : PmObl4` ([W] `blk`, [W] `mv`, [W] `roA`, [P] `cs`, [P] `lk`)
becomes `B7 : PmObl7` ([P] `cs`, [P] `lk`); [J] `PmFhV B` becomes [J] `PmFhK B7` (same content over the same paths up to
proof arguments); start records `StartPmV0` [P] become `StartPmK` [P] (one conjunct less). No premise on any existing
top. New module; no existing statement changed except the root import list.

Gen 56 (handoff p3mc §61) retired, with `ExecWPRV10–12` and the V15 stepping stones: `slotOblV13PmK`,
`nativePmK_noAd`, `nativePmK_vcpuNone`, `serializable_fl4_V15_pmK`, `pmFhK_of_V`, `serializable_fl4_V15_pmVofK`,
`serializable_fl4_localV13ofV15PmK`.
-/
import Fl4Proofs.P2.E2EPV15PmV
import Fl4Proofs.P2.InvPmRoE
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath tr masksOf)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg NextH VEq Safe narrowSP)

noncomputable section
open Classical

section pmK
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}

/-- **The family with mmuAD's PageMap slot** (`pmPathsK`: `blk`, `mv`, `roA` proved per `K`). -/
abbrev fl4LocV13PmK (B : PmObl7 st Cs Ω Sg Ac Locks) : PathsP (IxV13Pm S) :=
  PathsP.sum (fl4LocV13 st ar hA a0) (pmPathsK hA (masksWr_plain st) B)

/-- The start facts: V13's, and InvPmRoE's `StartPmK` [P] at the view's memory. -/
def StartV13PmK (B : PmObl7 st Cs Ω Sg Ac Locks) (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64)
    (hK : RegionOKP K) (hU : UserOKP K) (c : U64) (hs : U64 → Prop) (q : SP) : IxV13Pm S → Prop
  | .inl i => StartV13 st ar hA a0 arI AR MR Ch K m hK hU c hs q i
  | .inr j => StartPmK hA (masksWr_plain st) B Ch K m hK hU c hs q j

/-- **The native configuration over `pmPathsK`.** -/
def ExecCfg.nativePmK (B : PmObl7 st Cs Ω Sg Ac Locks) : ExecCfg S (IxV13Pm S) where
  Fam := fl4LocV13PmK st ar hA a0 B
  NoV := NoVPm (S := S)
  SF := StartV13PmK st ar hA a0 arI AR MR B
  VcpuOK := fun K _ => K.vcpus = ∅
  AdStep := fun _ _ _ _ _ => False

variable {arI AR MR}

/-- **[J] The PageMap `VSafe9` content on CoreView over `pmPathsK`** (gen 42's `PmFhV`, P2/E2EPV15Pm.lean, with
the start record `StartPmK`): the re-annotated body is `Safe` at the physical memory at every PageMap view start. -/
def PmFhK (B : PmObl7 st Cs Ω Sg Ac Locks) : Prop :=
  ∀ (Ch : S → Prop) (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (hK : RegionOKP K) (hU : UserOKP K) (c : U64) (k : SP)
    (ρ : U64 → U64) (j : I64 × localinv.Plan),
    (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) → EpochPteN K (CoreView.view K.toKLayout c ρ) →
    StartPmK hA (masksWr_plain st) B Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k j →
    MapsP K s → VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem →
    Safe s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k)

/-- **The PageMap start gives `StartAt`** at a view start (`PmRoot` by `pmRoot_of_qf`, `GateEp` by
`gateEp_viewStart`). -/
theorem pmStartK_at (B : PmObl7 st Cs Ω Sg Ac Locks) {Ch : S → Prop} {K : KLayoutP} {m : U64 → U64}
    {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {hs : U64 → Prop} {q : SP} {j : I64 × localinv.Plan}
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (hE : EpochPteN K m)
    (h : StartPmK hA (masksWr_plain st) B Ch K m hK hU c hs q j) :
    StartAt (pmPathsK hA (masksWr_plain st) B j K m hK hU) c hs m q := by
  obtain ⟨σe, Z, H, Cx, nc, -, -, -, hCL, -⟩ := hC
  obtain ⟨σ, a, hCh, hQ, hEx, hc, hl, hμ, rfl⟩ := h
  exact ⟨σ, a, ⟨⟨hCL.bun σ hCh, hQ, gateEp_viewStart (hCL.bun σ hCh) hE hμ⟩, hEx, pmRoot_of_qf hQ⟩, hc, hl, hμ,
    rfl⟩

set_option maxHeartbeats 4000000 in
/-- **`slotOblV13PmK` on the re-based platform** (gen 54, in place: `P : LocPlatCR` for `P : LocPlat` / `hIoa`). -/
theorem slotOblV13PmK_C (P : LocPlatCR st arI AR MR)
    (B : PmObl7 st Cs Ω Sg Ac Locks) (hPm : PmFhK st ar hA (arI := arI) (AR := AR) (MR := MR) B) :
    SlotOblV15 (L := L) arI AR MR (ExecCfg.nativePmK st ar hA a0 arI AR MR B) where
  sf := by
    intro Ch K s hK hU c hs q i hC hE hsf
    rcases i with i | j
    · exact (slotOblV13_C st ar hA a0 P).sf Ch K s hK hU c hs q i hC hE hsf
    · exact pmStartK_at st ar hA B hC hE hsf
  vs := by
    intro s K hK hU c k ρ i hM hV hn
    rcases i with i | j
    · exact (slotOblV13_C st ar hA a0 P).vs s K hK hU c k ρ i hM hV hn
    · exact absurd trivial hn
  fh := by
    intro Ch s K hK hU c k ρ i hC hE hsf hM hV hn
    rcases i with i | j
    · exact (slotOblV13_C st ar hA a0 P).fh Ch s K hK hU c k ρ i hC hE hsf hM hV hn
    · exact hPm Ch s K hK hU c k ρ j hC hE hsf hM hV

/-! ## The gen-43 top from the new one -/

/-- `PmObl4`'s [P] fields. -/
theorem pmObl7_of4 (B : PmObl4 st ar Cs Ω Sg Ac Locks) : PmObl7 st Cs Ω Sg Ac Locks := ⟨B.cs, B.lk⟩

/-- **The two PageMap families coincide** (they differ only in proof arguments). -/
theorem pmPathsG_eq_K (B : PmObl4 st ar Cs Ω Sg Ac Locks) :
    pmPathsG hA (masksWr_plain st) B = pmPathsK hA (masksWr_plain st) (pmObl7_of4 st ar B) := rfl

end pmK

end
end Fl4Proofs.P2.E2EP
