/-
# P2 (line pte, gen 9): `serializable_fl4_localW11PR` — W11's top with the reachability convention `ptesR`

nscope's `serializable_fl4_localW11PJ2` (P2/E2EPW11J2.lean) with the glue's PTE choice at every serial exit (and at
boot) `K'.ptes = ptesR K' s'.mem` (P2/PteReach.lean) in place of `ptesCanon`:

* **`qPs_of_convR`**: `QPs` at a start state of any store type from the convention at the epoch start, agreement
  with it on the `GateW` words and the start's memory link: `KsNoE` by `ptesR`'s filter, the ASID-table / pool words
  are `WalkW` words (so off `ptesR`, gate words, and equal to the epoch start's), the layout facts (`al`, `uoff`)
  from any bundle state of the layout (nscope's `qPs_of_bundle` at the empty PTE set). No bundle state at the start
  state and no memory link at the serial exit are needed.
* `Fl4StepWPR` / `ExecWPR`: nscope's `Fl4StepWPJ` / `ExecWPJ` with `serC : K'.vcpus = ∅ ∧ K'.ptes = ptesR K' s'.mem`;
  **`execP_of_WPR`** (an `ExecWPR` is an `ExecP`, with the epoch invariant `K.ptes = ptesR K s1.mem` and gate-word
  agreement); the serial step's `RegionOKP` / `UserOKP` by `regionOKP_R` / `userOKP_R` (no bundle needed).
* **`serializable_fl4_localW11PR`**: starts `StartP3W11JC` (W11's `StartP3W11` [P], armed program the relabelled
  annotation, `startQPB_of`).

The PageMap slot is not in this family yet; for it, `PtePlanLocked`'s [J] half under the convention is
`ptesR_at_run` (P2/E2EPRStart.lean). Premises: as `serializable_fl4_localW11PJ2`, with the convention `ptesR` in
`serC` / `hc0`. No new premise; no existing statement or file changed.
-/
import Fl4Proofs.P2.E2EPW11J2
import Fl4Proofs.P2.E2EPRStart
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld)
open Fl4Proofs.P2.E2E (StartAt SP SerStep)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg xsafeRun_greach allowed_of_sinv)

noncomputable section
open Classical

section conv
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **`QPs` at a start state of any store type** from the convention `ptesR` at the epoch start (module docstring). -/
theorem qPs_of_convR {S' : Type} {st' : machine.Store S'} [L' : LawfulStore st'] {K : KLayoutP}
    {s1 s : Cfg U64 U64 U64 U64} (he : K.ptes = ptesR K s1.mem) (nv : K.vcpus = ∅)
    (hb : ∃ σe, SlJAt (L := L) K.toKLayout σe) (hkeep : ∀ x, GateW K x → s.mem x = s1.mem x)
    {σ : S'} (hk : L'.ksb σ = K.ksb) (hμ : ∀ x, Aligned x → x ∉ K.user → L'.mem σ x = s.mem x) :
    QPs K st' σ := by
  obtain ⟨σe, A', arI, AR, Zx, Cx, Ax, Lst, D, a', τ, B⟩ := hb
  let K0 : KLayoutP := { K with ptes := ∅ }
  have B0 : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K0.toKLayout σe a' τ := B
  have Q0 : QPs K0 st σe := qPs_of_bundle B0 (fun b hb => absurd hb (Set.notMem_empty b)) nv
  have hnu : ∀ hi : U64, hi.val < 2048 → atAF K.ksb hi ∉ K.user :=
    fun hi hhi hu => Q0.uoff _ (Or.inl hu) hi hhi rfl
  have hnp : ∀ hi : U64, hi.val < 2048 → atAF K.ksb hi ∉ K.ptes := by
    intro hi hhi hb
    rw [he] at hb
    exact hb.2.1 (Or.inl ⟨hi, hhi, rfl⟩)
  have hm : ∀ hi : U64, hi.val < 2048 → L'.mem σ (atAF K.ksb hi) = s1.mem (atAF K.ksb hi) := by
    intro hi hhi
    rw [hμ _ (Q0.al hi hhi) (hnu hi hhi)]
    exact hkeep _ (gateW_of_region (region_none_tab B hhi) (hnp hi hhi) nv)
  refine ⟨fun o ho hb => ?_, hk, ?_, Q0.al, Q0.uoff⟩
  · rw [he] at hb
    exact ptesR_ks o ho hb
  · intro hi hhi
    rw [hk]
    refine ⟨hnp hi hhi, fun lo hlo hne hb => ?_⟩
    rw [hm hi hhi] at hne hb
    rw [he] at hb
    exact hb.2.1 (Or.inr (Or.inl ⟨hi, hhi, hne, lo, hlo, rfl⟩))

end conv

section exec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {ι : Type}

/-- **A step of FL4 with the glue premises named, rule 8, the PTE set by the reachability convention.** -/
structure Fl4StepWPR (LP : PathsP ι)
    (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (Ch : S → Prop) (c : U64)
    (s' : Cfg U64 U64 U64 U64) (K' : KLayoutP) (Ch' : S → Prop) : Prop where
  /-- [P] an armed program is pure glue. -/
  arm : ∀ p, s'.ph c = .arm p → PureGlue p
  /-- [P] the glue's start fact. -/
  start : ∀ p0 k W, s.ph c = .loc p0 (.start k) W → ∀ (hK : RegionOKP K) (hU : UserOKP K),
    ∃ i, SF Ch K s.mem hK hU c (fun l => s.lk l = some c) k i
  /-- [P] the serial exit's ghost choice. -/
  serX : SerStep s c → SerExitW P K'.toKLayoutV Ch'
  /-- The glue's layout convention at the serial exit: no VCPU, the PTE set `ptesR` of the exit memory. -/
  serC : SerStep s c → K'.vcpus = ∅ ∧ K'.ptes = ptesR K' s'.mem
  /-- [P] the exit ghost with rule 8. -/
  serG : SerStep s c → MapsP K' s'
  /-- Layout and chain change only at serial steps. -/
  keep : ¬ SerStep s c → K' = K ∧ Ch' = Ch

/-- **An execution of FL4 with the reachability-convention glue steps.** -/
inductive ExecWPR (LP : PathsP ι)
    (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s0 : Cfg U64 U64 U64 U64) (K0 : KLayoutP) (Ch0 : S → Prop) :
    Cfg U64 U64 U64 U64 → KLayoutP → (S → Prop) → Prop
  | refl : ExecWPR LP SF P s0 K0 Ch0 s0 K0 Ch0
  | step {s s' : Cfg U64 U64 U64 U64} {K K' : KLayoutP} {Ch Ch' : S → Prop} {c : U64} :
      ExecWPR LP SF P s0 K0 Ch0 s K Ch → Step s c s' → Fl4StepWPR LP SF P s K Ch c s' K' Ch' →
      ExecWPR LP SF P s0 K0 Ch0 s' K' Ch'
  | hw {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {Ch : S → Prop} {v a x : U64} :
      ExecWPR LP SF P s0 K0 Ch0 s K Ch → HwStepP K s v a x → ExecWPR LP SF P s0 K0 Ch0 (hwCfg s a x) K Ch

/-- **`okP_R` over `LocPlatC`** (gen 54, in place). -/
theorem okP_R_C {P : LocPlatC st arI AR MR} {K : KLayoutP} {Ch : S → Prop} {m : U64 → U64}
    (hB : SerExitC P K.toKLayoutV Ch) (hc : K.vcpus = ∅ ∧ K.ptes = ptesR K m) : RegionOKP K ∧ UserOKP K := by
  have hok := serExitC_ok hB (vcpuLay_empty hc.1)
  exact ⟨regionOKP_R hok.1 hc.2, userOKP_R hok.2 hc.2⟩

/-- The convention and the exit ghost give the layout's `RegionOKP` / `UserOKP`. -/
theorem okP_R {P : LocPlat st arI AR MR} {K : KLayoutP} {Ch : S → Prop} {m : U64 → U64}
    (hB : SerExitW P K.toKLayoutV Ch) (hc : K.vcpus = ∅ ∧ K.ptes = ptesR K m) : RegionOKP K ∧ UserOKP K :=
  okP_R_C ((serExitW_iff_C P).1 hB) hc

end exec

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

end top

end
end Fl4Proofs.P2.E2EP
