/-
P2 (line nscope, gen 4): **the carry argument for `QPs`** — the glue start fact of `E2EPJW` / `E2EPJW5`, reduced
to one serial-exit premise, family-agnostic (any `PathsP`).

* **`GateW K x`**: `x` is the gate's under `ownP K` at every memory. `gateW_of_region`: a word of region `.none`,
  off the PTE set, at a layout without VCPUs (P3 scope) is `GateW` (`own`'s `.none` case; `ownV` / `ownP` fall
  through).
* **`step_gate_keep`** (Serial ownership): a non-serial core step allowed by `Allowed` (the ownership discipline
  every `ExecP` step has, `exec_safeRunP` → `xsafeRun_greach` → `SInv` → `allowed_of_sinv`) leaves every `GateW`
  word's value: a local write needs `Held` of its word's owner, and no core holds the gate; no other non-serial
  step writes memory. **`hw_gate_keep`**: a hardware step writes a word that is lock-owned (`HwWr.own`), so no
  `GateW` word.
* **`EpochStart LP s0 K0 s1 K`**: `s1` begins an epoch of layout `K` — the start (`s1 = s0`, `K = K0`) or the target
  of a serial step whose `Fl4StepP` chose `K`. **`exec_epoch`**: every `ExecP` state `s` at layout `K` has an epoch
  start `s1` (reached by an `ExecP`) with `s.mem x = s1.mem x` for every `GateW K` word (induction on `ExecP`: a
  serial step starts a new epoch; a non-serial step keeps `K`, `Fl4StepP.keep`, and the `GateW` words).
* **`tabNoE_of_agree`**: `TabNoE` reads only the 2048 ASID-table words (and the kernel base), so it carries to any
  state agreeing with them.
* **`SerExitPte st K s1`** [P] (the glue's serial-exit choice, stated precisely): at the epoch start `s1` there is a
  bundle state `σe` (`SlJAtZ` with ghost `Zx`, layout `K.toKLayout`) agreeing with `s1.mem` on the aligned non-user
  words, with `K.ptes ⊆ ptesJ Zx` and `K.vcpus = ∅`. This is the only new premise; it is the choice of the PTE set
  (`K.ptes := {b | PtW Zx.L1 b}`, the leaf entries, is one, `ptesL1_sub`) plus the bundle link the existing
  serial-exit glue already makes for `K.toKLayout` (`SerExitW`: `K.toKLayout` and the chain are read off a P3 exit
  state).
* **`qPs_at_start`**: in any `ExecP` from an `Init` start, at any state `s` of layout `K`, a store state `σ` with
  `K`'s kernel base agreeing with `s.mem` on aligned non-user words (what `StartAt` / `GlueAt` give at a start)
  satisfies `QPs K st σ`, given `SerExitPte` at epoch starts. So `E2EPJW`'s start obligation reduces to
  `SerExitPte` plus `L.ksb σ = K.ksb` at the start state (true at every bundle / chain start: `SlJAtZ.ksb`).

`PtePlanLocked`'s [J] half (the planned leaf entry is in `K.ptes`) does **not** fall out here: it needs the walk
(`lookup_pt_slot`) at the start state to land where it lands at `σe`. The ingredient is in place — every word the walk
reads above the leaf (ASID-table words, pool entries, PML4/PDPT/PD entries) is region `.none` (P3 arch objects are
`H`'s `.other` objects, which `region` does not cover) and off `K.ptes` when `K.ptes` holds the leaf entries only, so
`GateW` by `gateW_of_region`, hence unchanged in the epoch by `exec_epoch` — but the PageMap path and the
`lookup_pt_slot` read-set lemma do not exist yet (pte gap 2).

No existing statement changed; no file of another line edited.
-/
import Fl4Proofs.P2.E2EPJW
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (StartAt SP SerStep)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll Step Allowed Held HwWr hwCfg XSafeRun
  xsafeRun_greach allowed_of_sinv)

noncomputable section
open Classical

/-! ## Gate words and the Serial ownership discipline -/

/-- `x` is the gate's under `ownP K` at every memory. -/
def GateW (K : KLayoutP) (x : U64) : Prop := ∀ m, ownP K m x = .gate

/-- **A region-`.none` word off the PTE set is `GateW`** at a layout without VCPUs. -/
theorem gateW_of_region {K : KLayoutP} {x : U64} (hr : OwnMap.region K.toKLayout x = .none) (hp : x ∉ K.ptes)
    (nv : K.vcpus = ∅) : GateW K x := by
  intro m
  unfold ownP
  rw [if_neg hp]
  unfold ownV
  rw [dif_neg (by rintro ⟨v, hv⟩; exact not_inVcpu_empty nv hv)]
  unfold OwnMap.own
  rw [hr]

/-- **A non-serial allowed core step keeps every `GateW` word.** -/
theorem step_gate_keep {K : KLayoutP} {s s' : Cfg U64 U64 U64 U64} {c : U64} (hM : MapsP K s) (hal : Allowed s c)
    (hst : Step s c s') (hn : ¬ SerStep s c) {x : U64} (hx : GateW K x) : s'.mem x = s.mem x := by
  cases hst with
  | serial _ _ _ _ hh hg _ _ => exact absurd ⟨hg, hh⟩ hn
  | @wr p0 a v k W hc =>
    simp only [Allowed, hc] at hal
    have hax : x ≠ a := by
      rintro rfl
      have h1 := hal.1
      rw [hM.own, hx] at h1
      exact h1
    exact Function.update_of_ne hax _ _
  | _ => rfl

/-- **A hardware step keeps every `GateW` word.** -/
theorem hw_gate_keep {K : KLayoutP} {s : Cfg U64 U64 U64 U64} {v a y : U64} (hK : RegionOKP K) (hM : MapsP K s)
    (h : HwStepP K s v a y) {x : U64} (hx : GateW K x) : (hwCfg s a y).mem x = s.mem x := by
  have hw := h.hwWr hK hM
  have hax : x ≠ a := by
    rintro rfl
    have h1 := hw.own
    rw [hM.own, hx] at h1
    cases h1
  exact Function.update_of_ne hax _ _

/-! ## Epochs -/

/-- **`s1` starts an epoch of layout `K`**: the execution's start, or the target of a serial step that chose `K`. -/
def EpochStart {ι : Type} (LP : PathsP ι) (s0 : Cfg U64 U64 U64 U64) (K0 : KLayoutP) (s1 : Cfg U64 U64 U64 U64)
    (K : KLayoutP) : Prop :=
  (s1 = s0 ∧ K = K0) ∨ ∃ (sp : Cfg U64 U64 U64 U64) (Kp : KLayoutP) (c : U64),
    ExecP LP s0 K0 sp Kp ∧ Step sp c s1 ∧ SerStep sp c ∧ Fl4StepP LP sp Kp c s1 K

/-- **Every `ExecP` state lies in an epoch whose start it agrees with on the `GateW` words** (module docstring). -/
theorem exec_epoch {ι : Type} {LP : PathsP ι} {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP}
    (h0 : Init s0) (hA0 : ArmInv s0) (hK0 : RegionOKP K0) (hU0 : UserOKP K0) (hM0 : MapsP K0 s0)
    (h : ExecP LP s0 K0 s K) :
    ∃ s1, EpochStart LP s0 K0 s1 K ∧ ∀ x, GateW K x → s.mem x = s1.mem x := by
  induction h with
  | refl => exact ⟨s0, Or.inl ⟨rfl, rfl⟩, fun _ _ => rfl⟩
  | @step s s' K K' c hE hst hF ih =>
    by_cases hs : SerStep s c
    · exact ⟨s', Or.inr ⟨s, K, c, hE, hst, hs, hF⟩, fun _ _ => rfl⟩
    · have eK : K' = K := hF.keep hs
      subst eK
      obtain ⟨s1, hS1, hk⟩ := ih
      obtain ⟨hr, -, -, hM⟩ := exec_safeRunP h0 hA0 hK0 hU0 hM0 hE
      obtain ⟨-, hSI, -⟩ := xsafeRun_greach h0 hA0 hr
      refine ⟨s1, hS1, fun x hx => ?_⟩
      rw [← hk x hx]
      exact step_gate_keep hM (allowed_of_sinv hSI c) hst hs hx
  | @hw s K v a y hE hh ih =>
    obtain ⟨s1, hS1, hk⟩ := ih
    obtain ⟨-, hK, -, hM⟩ := exec_safeRunP h0 hA0 hK0 hU0 hM0 hE
    refine ⟨s1, hS1, fun x hx => ?_⟩
    rw [← hk x hx]
    exact hw_gate_keep hK hM hh hx

/-! ## The carry -/

section carry
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **`TabNoE` carries to a state agreeing on the ASID-table words.** -/
theorem tabNoE_of_agree {K : KLayoutP} {σ σe : S} (hk : L.ksb σ = L.ksb σe)
    (hT : TabNoE (L := L) (· ∈ K.ptes) σe)
    (hm : ∀ hi : U64, hi.val < 2048 → L.mem σ (atAF (L.ksb σ) hi) = L.mem σe (atAF (L.ksb σe) hi)) :
    TabNoE (L := L) (· ∈ K.ptes) σ := by
  intro hi hhi
  obtain ⟨t1, t2⟩ := hT hi hhi
  refine ⟨by rw [hk]; exact t1, fun lo hlo hne => ?_⟩
  rw [hm hi hhi] at hne ⊢
  exact t2 lo hlo hne

/-- **The leaf entries are page-table words** (the PTE set rule 8 means: leaf entries only). -/
theorem ptesL1_sub (Zx : Fl4Proofs.P3.XSets) : {b | Fl4Proofs.P3.Vs.PtW Zx.L1 b} ⊆ ptesJ Zx :=
  fun _ hb => Fl4Proofs.P3.Vs.ptWA hb

variable (st) in
/-- **The serial-exit PTE choice** [P] (module docstring): at the epoch start `s1`, a bundle state `σe` of
`K.toKLayout` agreeing with `s1.mem` on the aligned non-user words, whose ghost's page-table words contain
`K.ptes`, at a layout without VCPUs. -/
def SerExitPte (K : KLayoutP) (s1 : Cfg U64 U64 U64 U64) : Prop :=
  ∃ (σe : S) (A' : Type) (arI : machine.Arch A') (AR : A' → Fl4Spec.Cr3 → Prop) (Zx : Fl4Proofs.P3.XSets)
    (Cx Ax : Set U64) (Lst : U64 → List U64) (D : Set U64) (a' : A') (τ : Fl4Spec.State Unit),
    SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K.toKLayout σe a' τ ∧ K.ptes ⊆ ptesJ Zx ∧ K.vcpus = ∅ ∧
    ∀ x, Aligned x → x ∉ K.user → L.mem σe x = s1.mem x

/-- **`QPs` at every start of an epoch** (module docstring): from `SerExitPte` [P] at the epoch starts, a store
state with `K`'s kernel base agreeing with the current memory on the aligned non-user words satisfies `QPs`. -/
theorem qPs_at_start {ι : Type} {LP : PathsP ι} {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP}
    (h0 : Init s0) (hA0 : ArmInv s0) (hK0 : RegionOKP K0) (hU0 : UserOKP K0) (hM0 : MapsP K0 s0)
    (h : ExecP LP s0 K0 s K) (hEp : ∀ s1, EpochStart LP s0 K0 s1 K → SerExitPte st K s1)
    {σ : S} (hk : L.ksb σ = K.ksb) (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = s.mem x) :
    QPs K st σ := by
  obtain ⟨s1, hS1, hkeep⟩ := exec_epoch h0 hA0 hK0 hU0 hM0 h
  obtain ⟨σe, A', arI, AR, Zx, Cx, Ax, Lst, D, a', τ, B, hsub, nv, hag⟩ := hEp s1 hS1
  have Q : QPs K st σe := qPs_of_bundle B hsub nv
  have hX := B.regionOKX
  have hnu : ∀ hi : U64, hi.val < 2048 → atAF K.ksb hi ∉ K.user :=
    fun hi hhi hu => Q.uoff _ (Or.inl hu) hi hhi rfl
  have hg : ∀ hi : U64, hi.val < 2048 → GateW K (atAF K.ksb hi) := by
    intro hi hhi
    have hp : atAF K.ksb hi ∉ K.ptes := by
      have := (Q.tab hi hhi).1
      rw [Q.ksb] at this
      exact this
    exact gateW_of_region (hX.asidT hi hhi).1 hp nv
  refine ⟨Q.ks, hk, ?_, Q.al, Q.uoff⟩
  refine tabNoE_of_agree (hk.trans Q.ksb.symm) Q.tab fun hi hhi => ?_
  rw [hk, Q.ksb]
  rw [hμ _ (Q.al hi hhi) (hnu hi hhi), hkeep _ (hg hi hhi), hag _ (Q.al hi hhi) (hnu hi hhi)]

end carry

end

end Fl4Proofs.P2.E2EP
