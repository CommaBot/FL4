/-
# P2 (line p3mc, gen 43): the CoreView PageMap slot without `GateEp` in its start fact — and `GateEp` proved at every view start

Gen 42 put `GateEp st K σ` into the PageMap start record `StartPmV` and reported that it "can fail at a view start"
(the view rewrites a gate-owned TCB word, offset 3520 of another core's thread). **That analysis was wrong**: `GateEp`
asks for *some* memory `m1` with `K.ptes = ptesR K m1` that agrees with `σ` on the gate words, not for the epoch
memory. Taking `m1 := L.mem σ` it reduces to `K.ptes = ptesR K (L.mem σ)`, which holds at every bundle state agreeing
with the epoch on the region-`.none` words (`GateAg`):

* **`walkW_agree`**: at a bundle state `σ` with `GateAg st K m σ`, every word a walk of `m` reads (`WalkW K.ksb m`:
  ASID table, named pools, the three upper levels of every walk from a named root) has the same value at `σ` and in
  `m` (the existing `gateAg_tab`, `gateAg_pool`, `named_L4`, `gateAg_up`, and the table facts of `walk_agree`'s proof);
* **`ptesR_congr`** (combinatorial, any `K`, `m`, `m'`): `ptesR K m' = ptesR K m` when `m'` agrees with `m` on the words
  `WalkW K.ksb m` (the convention reads nothing else);
* **`gateEp_of_ag`**: `SlJAt K σ`, `GateAg st K m σ`, `K.vcpus = ∅`, `K.ptes = ptesR K m` ⇒ **`GateEp st K σ`**;
* **`gateAg_of_epochN`**: at a state agreeing with `m` off user words, `EpochPteN K m` gives such an `m1` (the epoch
  memory) — so **`gateEp_viewStart`**: `GateEp` holds at every start state of a view (`SlJAt` + agreement with the view +
  the view's `EpochPteN`, which is exactly what the CoreView obligation `sf` / `fh` receives).

So no counterexample exists (goal 2: the claimed failure is refuted, not mechanised). The gen-42 top did not rest on a
false premise; still, its start record asked more than needed. Here, the clean form:

* **`PmPreV`** = `SlJAt ∧ PmQF ∧ (vcpus = ∅ ∧ ∃ m1, ptes = ptesR K m1 ∧ GateAg st K m1 σ) ∧ PmEx ∧ PmRoot` (the epoch
  clause on `GateAg`, as the PTE-arm Delete slot's `CvP`), **`pmPreV_eq`**: `PmPreV = PmPreG` (both directions:
  `gateEp_of_ag`, and `gateW_of_region` for the converse); **`PmObl4V`** (the [W] fields `blk`, `mv`, `roA` at
  `PmPreV`, the [P] `cs`, `lk`), **`pmObl4V_of`** / **`pmObl4_of_V`** (both directions, by `pmPreV_eq`).
* **`StartPmV0`** [P]: `StartPmG` on the view, **without** `GateEp`; **`startPmV_of_V0`** (at every view start the
  gen-42 record follows), `startPmV0_of` (and conversely, forgetting `GateEp`).
* **`ExecCfg.nativePmV B`**, **`slotOblV13PmV`** (from `slotOblV13`, `startPmV_of_V0`, `pmStartV_at` and `PmFhV`),
  **`serializable_fl4_V15_pmV`** (exact; premises `B : PmObl4`, `PmFhV B` [J], start records `StartPmV0` [P]) —
  **authoritative**; **`serializable_fl4_V15_pmV'`** (the same with `PmObl4V`); **`serializable_fl4_V15_pmOfV`**: the
  gen-42 top's statement from the new one (every gen-42 execution is a new one: `ExecV15.map` with `startPmV0_of`);
  **`serializable_fl4_localV13ofV15PmV`**: V13 from the new top.

No premise on any existing top. No existing statement changed except the root import list.

Gen 56 (handoff p3mc §61) retired, with `ExecWPRV10–12` and the V15 stepping stones: `pmObl4_of_V`, `StartPmV0`,
`StartV13PmV`, `nativePmV`, `startPmV0_of`, `startPmV_of_V0`, `slotOblV13PmV`, `nativePmV_noAd`, `nativePmV_vcpuNone`,
`serializable_fl4_V15_pmV`, `serializable_fl4_V15_pmV'`, `serializable_fl4_V15_pmOfV`,
`serializable_fl4_localV13ofV15PmV`.
-/
import Fl4Proofs.P2.E2EPV15Pm
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P3.Vs (PtW PtWAll peA atA PtRel PtPlaced UserV VsWrite)
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath tr masksOf)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg NextH VEq Safe narrowSP)

noncomputable section
open Classical

/-! ## The convention reads only the walk words -/

section congr
variable {K : KLayoutP} {m m' : U64 → U64}

theorem named_congr (h : ∀ b, WalkW K.ksb m b → m' b = m b) {r : U64} :
    NamedM m' K.ksb r ↔ NamedM m K.ksb r := by
  have hA : ∀ hi : U64, hi.val < 2048 → m' (atA K.ksb hi) = m (atA K.ksb hi) :=
    fun hi hhi => h _ (Or.inl ⟨hi, hhi, rfl⟩)
  have hP : ∀ hi : U64, hi.val < 2048 → m (atA K.ksb hi) ≠ 0#u64 → ∀ lo : U64, lo.val < 512 →
      m' (peA (m (atA K.ksb hi)) lo) = m (peA (m (atA K.ksb hi)) lo) :=
    fun hi hhi hne lo hlo => h _ (Or.inr (Or.inl ⟨hi, hhi, hne, lo, hlo, rfl⟩))
  constructor
  · rintro ⟨hi, hhi, hne, lo, hlo, e, h0, h1⟩
    rw [hA hi hhi] at hne e
    rw [hP hi hhi hne lo hlo] at e
    exact ⟨hi, hhi, hne, lo, hlo, e, h0, h1⟩
  · rintro ⟨hi, hhi, hne, lo, hlo, e, h0, h1⟩
    refine ⟨hi, hhi, by rw [hA hi hhi]; exact hne, lo, hlo, ?_, h0, h1⟩
    rw [hA hi hhi, hP hi hhi hne lo hlo]; exact e

theorem walks_congr (h : ∀ b, WalkW K.ksb m b → m' b = m b) {r v : U64} (hr : NamedM m K.ksb r) (hv : UserV v) :
    walk1 m' r v = walk1 m r v ∧ walk2 m' r v = walk2 m r v ∧ walk3 m' r v = walk3 m r v := by
  have h1 : walk1 m' r v = walk1 m r v := by
    unfold walk1
    rw [h _ (Or.inr (Or.inr ⟨r, hr, v, hv, Or.inl rfl⟩))]
  have h2 : walk2 m' r v = walk2 m r v := by
    unfold walk2
    rw [h1]
    cases hx : walk1 m r v with
    | none => rfl
    | some x =>
      simp only [walkStep]
      rw [h x (Or.inr (Or.inr ⟨r, hr, v, hv, Or.inr (Or.inl hx)⟩))]
  have h3 : walk3 m' r v = walk3 m r v := by
    unfold walk3
    rw [h2]
    cases hx : walk2 m r v with
    | none => rfl
    | some x =>
      simp only [walkStep]
      rw [h x (Or.inr (Or.inr ⟨r, hr, v, hv, Or.inr (Or.inr hx)⟩))]
  exact ⟨h1, h2, h3⟩

theorem walkW_congr (h : ∀ b, WalkW K.ksb m b → m' b = m b) {b : U64} : WalkW K.ksb m' b ↔ WalkW K.ksb m b := by
  have hA : ∀ hi : U64, hi.val < 2048 → m' (atA K.ksb hi) = m (atA K.ksb hi) :=
    fun hi hhi => h _ (Or.inl ⟨hi, hhi, rfl⟩)
  constructor
  · rintro (h0 | ⟨hi, hhi, hne, lo, hlo, e⟩ | ⟨r, hr, v, hv, hw⟩)
    · exact Or.inl h0
    · rw [hA hi hhi] at hne e
      exact Or.inr (Or.inl ⟨hi, hhi, hne, lo, hlo, e⟩)
    · have hr' := (named_congr h).1 hr
      obtain ⟨e1, e2, -⟩ := walks_congr h hr' hv
      rw [e1, e2] at hw
      exact Or.inr (Or.inr ⟨r, hr', v, hv, hw⟩)
  · rintro (h0 | ⟨hi, hhi, hne, lo, hlo, e⟩ | ⟨r, hr, v, hv, hw⟩)
    · exact Or.inl h0
    · exact Or.inr (Or.inl ⟨hi, hhi, by rw [hA hi hhi]; exact hne, lo, hlo, by rw [hA hi hhi]; exact e⟩)
    · obtain ⟨e1, e2, -⟩ := walks_congr h hr hv
      refine Or.inr (Or.inr ⟨r, (named_congr h).2 hr, v, hv, ?_⟩)
      rw [e1, e2]; exact hw

/-- **The reachability convention reads only the walk words** (module docstring). -/
theorem ptesR_congr (h : ∀ b, WalkW K.ksb m b → m' b = m b) : ptesR K m' = ptesR K m := by
  ext e
  constructor
  · rintro ⟨⟨r, hr, v, hv, hw⟩, hnw, rest⟩
    have hr' := (named_congr h).1 hr
    obtain ⟨-, -, e3⟩ := walks_congr h hr' hv
    exact ⟨⟨r, hr', v, hv, by rw [← e3]; exact hw⟩, fun hW => hnw ((walkW_congr h).2 hW), rest⟩
  · rintro ⟨⟨r, hr, v, hv, hw⟩, hnw, rest⟩
    obtain ⟨-, -, e3⟩ := walks_congr h hr hv
    exact ⟨⟨r, (named_congr h).2 hr, v, hv, by rw [e3]; exact hw⟩, fun hW => hnw ((walkW_congr h).1 hW), rest⟩

end congr

/-! ## Every walk word agrees at a `GateAg` bundle state -/

section bundle
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A' : Type} {arI : machine.Arch A'}
  {AR : A' → Fl4Spec.Cr3 → Prop} {Zx : Fl4Proofs.P3.XSets} {Cx Ax : Set U64} {Lst : U64 → List U64}
  {D : Set U64} {σ : S} {a' : A'} {τ : Fl4Spec.State Unit} {K : KLayoutP} {m : U64 → U64}

/-- **Every word a walk of `m` reads agrees at `σ`** (module docstring). -/
theorem walkW_agree (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K.toKLayout σ a' τ) (hag : GateAg st K m σ) :
    ∀ b, WalkW K.ksb m b → L.mem σ b = m b := by
  have hPR := B.j.xtop.fin.2.2.1
  have hTP := B.j.xtop.fin.1.2
  rintro b (⟨hi, hhi, rfl⟩ | ⟨hi, hhi, hne, lo, hlo, rfl⟩ | ⟨r, hr, v, hv, hw⟩)
  · exact gateAg_tab B hag hhi
  · exact (gateAg_pool B hag hhi hne).2 lo hlo
  · obtain ⟨hr4, -⟩ := named_L4 B hag hr
    obtain ⟨e1, e2, -⟩ := walk_agree B hag hr hv
    rcases hw with rfl | h1 | h2
    · exact gateAg_up B hag (Or.inl hr4) (Fl4Proofs.P3.Vs.vIdx_lt v 39)
        (Or.inr (Or.inr ⟨r, hr, v, hv, Or.inl rfl⟩))
    · have hx : walk1 (L.mem σ) r v = some b := e1.trans h1
      obtain ⟨rr, hrr, -, hsl, -⟩ := spec_ex_fd (Fl4Proofs.P3.Vs.lookup_pdpt_slot_rel σ τ hPR hTP.pt hr4 v hv)
      rw [lookup_pdpt_slot_res] at hrr
      have := ok_inj_ff hrr
      subst this
      obtain ⟨q, hq, rfl⟩ := hsl b (res1_ok.2 hx)
      exact gateAg_up B hag (Or.inr (Or.inl hq)) (Fl4Proofs.P3.Vs.vIdx_lt v 30)
        (Or.inr (Or.inr ⟨r, hr, v, hv, Or.inr (Or.inl h1)⟩))
    · have hx : walk2 (L.mem σ) r v = some b := e2.trans h2
      obtain ⟨rr, hrr, -, hsl, -⟩ := spec_ex_fd (Fl4Proofs.P3.Vs.lookup_pd_slot_rel σ τ hPR hTP.pt hr4 v hv)
      rw [lookup_pd_slot_res] at hrr
      have := ok_inj_ff hrr
      subst this
      obtain ⟨q, hq, rfl⟩ := hsl b (res2_ok.2 hx)
      exact gateAg_up B hag (Or.inr (Or.inr hq)) (Fl4Proofs.P3.Vs.vIdx_lt v 21)
        (Or.inr (Or.inr ⟨r, hr, v, hv, Or.inr (Or.inr h2)⟩))

end bundle

section ep
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayoutP} {σ : S}

/-- **`GateEp` at a `GateAg` bundle state** (module docstring; `m1 := L.mem σ`). -/
theorem gateEp_of_ag (hJ : SlJAt (L := L) K.toKLayout σ) {m : U64 → U64} (hag : GateAg st K m σ)
    (nv : K.vcpus = ∅) (he : K.ptes = ptesR K m) : GateEp st K σ := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', τ, B⟩ := hJ
  exact ⟨L.mem σ, ⟨nv, he.trans (ptesR_congr (walkW_agree B hag)).symm⟩, fun _ _ _ _ => rfl⟩

/-- **`EpochPteN` of a memory `σ` agrees with gives `GateAg` for the epoch memory.** -/
theorem gateAg_of_epochN {m : U64 → U64} (hE : EpochPteN K m)
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = m x) :
    ∃ m1 : U64 → U64, K.vcpus = ∅ ∧ K.ptes = ptesR K m1 ∧ GateAg st K m1 σ := by
  obtain ⟨s1, ⟨nv, hc⟩, hk⟩ := hE
  refine ⟨s1.mem, nv, hc, fun w hr hn hu ha => ?_⟩
  rw [hμ w ha hu]
  exact hk w hr (by rw [hc]; exact hn)

/-- **`GateEp` at every view start** (module docstring). -/
theorem gateEp_viewStart (hJ : SlJAt (L := L) K.toKLayout σ) {m : U64 → U64} (hE : EpochPteN K m)
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = m x) : GateEp st K σ := by
  obtain ⟨m1, nv, he, hag⟩ := gateAg_of_epochN (st := st) hE hμ
  exact gateEp_of_ag hJ hag nv he

/-- `GateEp` gives the `GateAg` form. -/
theorem ag_of_gateEp (h : GateEp st K σ) :
    K.vcpus = ∅ ∧ ∃ m1 : U64 → U64, K.ptes = ptesR K m1 ∧ GateAg st K m1 σ := by
  obtain ⟨m1, ⟨nv, hp⟩, hg⟩ := h
  exact ⟨nv, m1, hp, fun w hr hn hu ha => hg w (gateW_of_region hr (by rw [hp]; exact hn) nv) ha hu⟩

end ep

/-! ## The view precondition and the obligations at it -/

section pre
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}

/-- **PageMap's precondition on the view** (module docstring): `PmPreF`'s epoch clause on `GateAg`. -/
def PmPreV (Cs Ω Sg Ac : Set U64) (Locks : S → U64 → Prop) (p : localinv.Plan) (K : KLayoutP) (m : U64 → U64)
    (s : S) : Prop :=
  SlJAt (L := L) K.toKLayout s ∧ PmQF st Cs Ω Sg Ac Locks p K m s ∧
    (K.vcpus = ∅ ∧ ∃ m1 : U64 → U64, K.ptes = ptesR K m1 ∧ GateAg st K m1 s) ∧ PmEx st p s ∧ PmRoot st p s

/-- **`PmPreV` is `PmPreG`** (both directions). -/
theorem pmPreV_eq (p : localinv.Plan) (K : KLayoutP) (m : U64 → U64) :
    PmPreV st Cs Ω Sg Ac Locks p K m = PmPreG st Cs Ω Sg Ac Locks p K m := by
  funext s
  apply propext
  constructor
  · rintro ⟨hJ, hQ, ⟨nv, m1, he, hag⟩, hEx, hRt⟩
    exact ⟨⟨hJ, hQ, gateEp_of_ag hJ hag nv he⟩, hEx, hRt⟩
  · rintro ⟨⟨hJ, hQ, hG⟩, hEx, hRt⟩
    exact ⟨hJ, hQ, ag_of_gateEp hG, hEx, hRt⟩

/-- **PageMap's remaining obligations at the view precondition** ([W] `blk`, `mv`, `roA`; [P] `cs`, `lk`). -/
structure PmObl4V (Cs Ω Sg Ac : Set U64) (Locks : S → U64 → Prop) : Prop where
  /-- [W] the decode block. -/
  blk : ∀ (j : I64 × localinv.Plan) K m, PmBlkUW2 st ar j.2 K Locks (PmPreV st Cs Ω Sg Ac Locks j.2 K m)
  /-- [W] `move`. -/
  mv : ∀ (j : I64 × localinv.Plan) K m, PmMoveW st ar j.1 j.2 K Locks m (PmPreV st Cs Ω Sg Ac Locks j.2 K m)
  /-- [W] `ReadOnce` of accepting runs. -/
  roA : ∀ (j : I64 × localinv.Plan) K m,
    PmRoAccW st ar j.1 j.2 K Locks m (R.invBodyPmG j.1 j.2) (PmPreV st Cs Ω Sg Ac Locks j.2 K m)
  /-- [P] the core set is below 64. -/
  cs : ∀ c ∈ Cs, c.val < 64
  /-- [P] the locks survive a user write. -/
  lk : PmLk st Locks

theorem pmObl4V_of (B : PmObl4 st ar Cs Ω Sg Ac Locks) : PmObl4V st ar Cs Ω Sg Ac Locks where
  blk j K m := by rw [pmPreV_eq]; exact B.blk j K m
  mv j K m := by rw [pmPreV_eq]; exact B.mv j K m
  roA j K m := by rw [pmPreV_eq]; exact B.roA j K m
  cs := B.cs
  lk := B.lk

end pre

/-! ## The start fact without `GateEp` and the top -/

section pm
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}

variable {arI AR MR}

end pm

end
end Fl4Proofs.P2.E2EP
