/-
# P2 (line mmuAD, gen 1): page-walker A/D writes in the execution — `serializable_fl4_localU3`

`serializable_fl4_localU2` (P2/E2EPU2P.lean) is about executions whose memory changes only by core steps and the
VCPU hardware step (`HwStepP`, vacuous at `vcpus = ∅`). The x86 MMU also writes kernel words: it ORs the accessed
/ dirty bits into paging-structure entries (`MmuAD.MmuAD` [P], P2/MmuADWalk.lean, with its SDM basis). This module
puts those writes into the execution, for the class the existing serial machinery absorbs exactly:

* **`MmuLeaf K s a x`**: an A/D write (`MmuAD` [P] over the leaf set `K.ptes`) to a leaf PTE `a` whose word lock
  no core holds (`s.lk a = none`).
* **`MmuLeaf.hwWr`**: such a write is a `Serial.HwWr` with lock `a` (under `ownP` a leaf is `.lock a`,
  `ownP_pte`; it decides no owner, `pte_nondec`; its class is untracked, `ko_pte`). So it is an environment
  action that commutes with every in-progress local path (`Serial.sinv_hw`: it is `Foreign` to each) and is
  logged as its own entry `.wr a x .done`: the serial order explains it.
* `ExecPA` (`ExecP` + `mmu`), `exec_safeRunPA`, **`serializable_e2ePA`**; `ExecU3` (`ExecWPR` + `mmu`),
  **`execPA_of_U3G`** (`execP_of_WPRG` with A/D steps: they keep the epoch's gate words, `mmu_gate_keep`, since
  a leaf is never a `GateW` word, so `ptesR`'s upper levels and every start fact's chain data are unchanged),
  `execU3_of_WPR` (every U2 execution is a U3 one).
* **`serializable_fl4_localU3`**: U2's statement over `ExecU3`: where an execution with core steps, VCPU hardware
  steps and leaf A/D writes reaches `NoLoc`, memory is the serial run of the completed entries, A/D writes
  included as entries, in completion order. Premises: exactly U2's, plus `MmuAD` [P] inside the `mmu` steps
  (which only *adds* behaviours: the premise is the hardware semantics the steps are allowed to have).
  The start facts' `GlueAt` (real store = model memory on kernel words) now holds with the A/D bits of free
  leaves *in* the model memory — this closes p2P's finding 3 for that class.

## What `ExecU3` still excludes (stated, not hidden) — `ExecU3H` is the full hardware relation
`ExecU3H` has an `mmu` step for every `MmuAD (PW K)` write, any present paging word, any time. Not yet covered:
1. **A bits of non-leaf entries** (PML4E / PDPTE / PDE: `make_user_table` creates them with A = 0, so the walker
   sets A once per entry, at any time). These words are `GateW` (gate-owned) under `ownP`; local paths read them
   lock-free (`localinv::plan_with`'s walk, CNodeDelete's `unmap_page` re-walk). `HwWr` needs a lock owner, so
   the write is not an environment action of `Serial`. What it needs is that every in-progress local path's
   continuation at a read of such a word is the same tree for `v` and `v ||| A` (`ADIns`, plan in the handoff).
   The sequential half is proved: `lookup_pdpt_slot_ad` / `lookup_pd_slot_ad` / `lookup_pt_slot_ad`
   (P2/MmuADWalk.lean) — the walks' results are equal on `ADEqM` stores.
2. **A/D writes to a leaf while a local path holds its lock** (Delete of a mapped frame, PageMap remapping a present
   entry). The holder's accesses are: read `e` (decisions on `& P_PRESENT`, `& P_PS`, `frame_base`; rights /
   frame masks in `write_mapping`: none touches bits 5, 6, `MmuADWalk.kP`…`kXD`) and one plain store (`0` or the
   new entry). A plain store is linearizable against the walker's locked RMW: a write before it is overwritten
   (log it before the path), a write after it hits `0` (not present: no write) or the new entry (log it after the
   path's `leave`). Needs `Serial` with a deferred-entry rule; not done.
3. **Inside serial bodies** P2 does not interpret the body (`Step.serial` takes any `Run p s.mem m'`), so an A/D
   write in the middle of a body is the body's P3 refinement question. One body is **not** linearizable against it:
   `decode_test_and_clear_accessed` (vspace.rs l. 906-908, plain `read` then `write(old & !P_ACCESSED)`) loses a
   concurrent A or D write — see the handoff (race report and the one-line fix, an atomic fetch-and).

No [W]; no new [J]; the only new [P] is `MmuAD` (P2/MmuADWalk.lean). No existing statement or file changed.
-/
import Fl4Proofs.P2.E2EPU2P
import Fl4Proofs.P2.MmuADWalk
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld)
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg HwWr XSafeRun xsafeRun_greach
  allowed_of_sinv serializable_safeX)
open Fl4Proofs.P2.MmuAD (MmuAD)

noncomputable section
open Classical

/-! ## A/D writes to a free leaf are hardware writes of `Serial` -/

section leaf
variable {K : KLayoutP}

/-- **An A/D write to a leaf PTE no core has locked**: `MmuAD` [P] over the leaf set `K.ptes`, and the word's
lock is free. -/
structure MmuLeaf (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (a x : U64) : Prop where
  hw : MmuAD (· ∈ K.ptes) s.mem a x
  free : s.lk a = none

/-- **A free-leaf A/D write is a `Serial.HwWr`** with lock `a`. -/
theorem MmuLeaf.hwWr (hK : RegionOKP K) {s : Cfg U64 U64 U64 U64} {a x : U64} (h : MmuLeaf K s a x)
    (hM : MapsP K s) : HwWr s a x a where
  own := by rw [hM.own]; exact ownP_pte h.hw.pw
  free := h.free
  keep := by rw [hM.own]; exact ownP_upd_nondec hK (pte_nondec hK h.hw.pw) _ _
  ko := by rw [hM.ko]; exact ko_pte hK h.hw.pw _

/-- A free-leaf A/D write keeps the ghost maps. -/
theorem maps_mmu (hK : RegionOKP K) {s : Cfg U64 U64 U64 U64} {a x : U64} (hM : MapsP K s)
    (h : MmuLeaf K s a x) : MapsP K (hwCfg s a x) := by
  refine ⟨hM.own, hM.cls, ?_⟩
  show s.ko = OwnMap.ko K.toKLayout (Function.update s.mem a x)
  rw [ko_updP hK (m := s.mem) (by rw [ownP_pte h.hw.pw]; intro e; cases e)]
  exact hM.ko

/-- A free-leaf A/D write changes no gate word. -/
theorem mmu_gate_keep {s : Cfg U64 U64 U64 U64} {a y : U64} (h : MmuLeaf K s a y) {x : U64} (hx : GateW K x) :
    (hwCfg s a y).mem x = s.mem x := by
  have hax : x ≠ a := by
    rintro rfl
    have h1 := hx s.mem
    rw [ownP_pte h.hw.pw] at h1
    cases h1
  exact Function.update_of_ne hax _ _

end leaf

/-! ## Executions with A/D writes -/

/-- **An execution of FL4 with rules 7 and 8, the VCPU hardware and free-leaf A/D writes.** -/
inductive ExecPA {ι : Type} (LP : PathsP ι) (s0 : Cfg U64 U64 U64 U64) (K0 : KLayoutP) :
    Cfg U64 U64 U64 U64 → KLayoutP → Prop
  | refl : ExecPA LP s0 K0 s0 K0
  | step {s s' : Cfg U64 U64 U64 U64} {K K' : KLayoutP} {c : U64} :
      ExecPA LP s0 K0 s K → Step s c s' → Fl4StepP LP s K c s' K' → ExecPA LP s0 K0 s' K'
  | hw {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {v a x : U64} :
      ExecPA LP s0 K0 s K → HwStepP K s v a x → ExecPA LP s0 K0 (hwCfg s a x) K
  | mmu {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {a x : U64} :
      ExecPA LP s0 K0 s K → MmuLeaf K s a x → ExecPA LP s0 K0 (hwCfg s a x) K

theorem exec_safeRunPA {ι : Type} {LP : PathsP ι} {s0 s : Cfg U64 U64 U64 U64}
    {K0 K : KLayoutP} (h0 : Init s0) (hA0 : ArmInv s0) (hK0 : RegionOKP K0)
    (hU0 : UserOKP K0) (hM0 : MapsP K0 s0) (h : ExecPA LP s0 K0 s K) :
    XSafeRun s0 s ∧ RegionOKP K ∧ UserOKP K ∧ MapsP K s := by
  induction h with
  | refl => exact ⟨.refl, hK0, hU0, hM0⟩
  | @step s s' K K' c _ hst hF ih =>
    obtain ⟨hr, hK, hU, hM⟩ := ih
    obtain ⟨_, hS, _⟩ := xsafeRun_greach h0 hA0 hr
    refine ⟨.step hr hst ⟨hF.arm, fun p0 k W hph => ?_⟩, ?_⟩
    · obtain ⟨i, hP⟩ := hF.start p0 k W hph hK hU
      rw [hM.own, hM.cls, hM.ko]
      exact (LP i K s.mem hK hU).safe (moveHeldP hK) (ownDepP hK hU) hP
    · by_cases hs : SerStep s c
      · exact hF.ser hs
      · rw [hF.keep hs]
        exact ⟨hK, hU, maps_stepP hK hM (allowed_of_sinv hS c) hst hs⟩
  | hw _ hh ih =>
    obtain ⟨hr, hK, hU, hM⟩ := ih
    exact ⟨.hw hr (hh.hwWr hK hM), hK, hU, maps_hwP hK hM hh⟩
  | mmu _ hh ih =>
    obtain ⟨hr, hK, hU, hM⟩ := ih
    exact ⟨.hw hr (hh.hwWr hK hM), hK, hU, maps_mmu hK hM hh⟩

/-- **End to end with free-leaf A/D writes** (`serializable_e2eP` over `ExecPA`): the A/D writes are entries of
the serial order. -/
theorem serializable_e2ePA {ι : Type} (LP : PathsP ι) {s0 s : Cfg U64 U64 U64 U64}
    {K0 K : KLayoutP} (h0 : Init s0) (hA0 : ArmInv s0) (hK0 : RegionOKP K0)
    (hU0 : UserOKP K0) (hM0 : MapsP K0 s0) (h : ExecPA LP s0 K0 s K) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_safeX h0 hA0 (exec_safeRunPA h0 hA0 hK0 hU0 hM0 h).1 hq

section exec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {ι : Type}

/-- **An execution of FL4 with the U2 glue, the VCPU hardware and free-leaf A/D writes.** -/
inductive ExecU3 (LP : PathsP ι)
    (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s0 : Cfg U64 U64 U64 U64) (K0 : KLayoutP) (Ch0 : S → Prop) :
    Cfg U64 U64 U64 U64 → KLayoutP → (S → Prop) → Prop
  | refl : ExecU3 LP SF P s0 K0 Ch0 s0 K0 Ch0
  | step {s s' : Cfg U64 U64 U64 U64} {K K' : KLayoutP} {Ch Ch' : S → Prop} {c : U64} :
      ExecU3 LP SF P s0 K0 Ch0 s K Ch → Step s c s' → Fl4StepWPR LP SF P s K Ch c s' K' Ch' →
      ExecU3 LP SF P s0 K0 Ch0 s' K' Ch'
  | hw {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {Ch : S → Prop} {v a x : U64} :
      ExecU3 LP SF P s0 K0 Ch0 s K Ch → HwStepP K s v a x → ExecU3 LP SF P s0 K0 Ch0 (hwCfg s a x) K Ch
  | mmu {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {Ch : S → Prop} {a x : U64} :
      ExecU3 LP SF P s0 K0 Ch0 s K Ch → MmuLeaf K s a x → ExecU3 LP SF P s0 K0 Ch0 (hwCfg s a x) K Ch

/-- **The full hardware relation** (module docstring, the target): an `mmu` step for every `MmuAD` [P] write to a
paging word of `PW K` (any present paging-structure entry, any lock state, any time). `ExecU3` is its sub-relation
with the leaf / free-lock restriction; `serializable_fl4_localU3` is proved for `ExecU3` only. -/
inductive ExecU3H (LP : PathsP ι)
    (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (PW : KLayoutP → U64 → Prop) (s0 : Cfg U64 U64 U64 U64) (K0 : KLayoutP)
    (Ch0 : S → Prop) : Cfg U64 U64 U64 U64 → KLayoutP → (S → Prop) → Prop
  | refl : ExecU3H LP SF P PW s0 K0 Ch0 s0 K0 Ch0
  | step {s s' : Cfg U64 U64 U64 U64} {K K' : KLayoutP} {Ch Ch' : S → Prop} {c : U64} :
      ExecU3H LP SF P PW s0 K0 Ch0 s K Ch → Step s c s' → Fl4StepWPR LP SF P s K Ch c s' K' Ch' →
      ExecU3H LP SF P PW s0 K0 Ch0 s' K' Ch'
  | hw {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {Ch : S → Prop} {v a x : U64} :
      ExecU3H LP SF P PW s0 K0 Ch0 s K Ch → HwStepP K s v a x → ExecU3H LP SF P PW s0 K0 Ch0 (hwCfg s a x) K Ch
  | mmu {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {Ch : S → Prop} {a x : U64} :
      ExecU3H LP SF P PW s0 K0 Ch0 s K Ch → MmuAD (PW K) s.mem a x →
      ExecU3H LP SF P PW s0 K0 Ch0 (hwCfg s a x) K Ch

/-- **`ExecU3` is the part of `ExecU3H` whose A/D writes hit free leaves** (for any `PW` containing the leaves). -/
theorem execU3H_of_U3 {LP : PathsP ι}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    {P : LocPlat st arI AR MR} {PW : KLayoutP → U64 → Prop} (hPW : ∀ K x, x ∈ K.ptes → PW K x)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop}
    (h : ExecU3 LP SF P s0 K0 Ch0 s K Ch) : ExecU3H LP SF P PW s0 K0 Ch0 s K Ch := by
  induction h with
  | refl => exact .refl
  | step _ hS g ih => exact .step ih hS g
  | hw _ hH ih => exact .hw ih hH
  | @mmu s K Ch a x _ hH ih =>
    exact .mmu ih ⟨hPW K a hH.hw.pw, hH.hw.present, hH.hw.ad, hH.hw.chg⟩

/-- **Every U2 execution is a U3 one** (no A/D write). -/
theorem execU3_of_WPR {LP : PathsP ι}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    {P : LocPlat st arI AR MR} {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop}
    (h : ExecWPR LP SF P s0 K0 Ch0 s K Ch) : ExecU3 LP SF P s0 K0 Ch0 s K Ch := by
  induction h with
  | refl => exact .refl
  | step _ hS g ih => exact .step ih hS g
  | hw _ hH ih => exact .hw ih hH

/-- **An `ExecU3` is an `ExecPA`, with the epoch invariant** (`execP_of_WPRG` with A/D steps). -/
theorem execPA_of_U3G {LP : PathsP ι}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    (hSF : ∀ (Ch : S → Prop) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) c hs q i,
      (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) →
      (∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → s.mem x = s1.mem x) →
      SF Ch K s.mem hK hU c hs q i → StartAt (LP i K s.mem hK hU) c hs s.mem q)
    (P : LocPlat st arI AR MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecU3 LP SF P s0 K0 Ch0 s K Ch) :
    ExecPA LP s0 K0 s K ∧ SerExitW P K.toKLayoutV Ch ∧
      ∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → s.mem x = s1.mem x := by
  obtain ⟨hK0, hU0⟩ := okP_R hB hc0
  induction h with
  | refl => exact ⟨.refl, hB, s0, hc0, fun _ _ => rfl⟩
  | @step s1 s1' K1 K1' Ch1 Ch1' c1 _ hS g ih =>
    obtain ⟨hE, hX, e1, hCe, hk1⟩ := ih
    have hst : Fl4StepP LP s1 K1 c1 s1' K1' := by
      refine ⟨g.arm, fun p0 k W hph hK hU => ?_, fun hs => ?_, fun hn => (g.keep hn).1⟩
      · obtain ⟨i, hi⟩ := g.start p0 k W hph hK hU
        exact ⟨i, hSF _ _ s1 _ _ _ _ _ i hX.chainOf ⟨e1, hCe, hk1⟩ hi⟩
      · have hP := okP_R (g.serX hs) (g.serC hs)
        exact ⟨hP.1, hP.2, g.serG hs⟩
    refine ⟨.step hE hS hst, ?_, ?_⟩
    · by_cases hs : SerStep s1 c1
      · exact g.serX hs
      · obtain ⟨e1, e2⟩ := g.keep hs
        rw [e1, e2]; exact hX
    · by_cases hs : SerStep s1 c1
      · exact ⟨s1', g.serC hs, fun _ _ => rfl⟩
      · obtain ⟨eK, -⟩ := g.keep hs
        subst eK
        obtain ⟨hr, -, -, hM⟩ := exec_safeRunPA h0 hA0 hK0 hU0 hM0 hE
        obtain ⟨-, hSI, -⟩ := xsafeRun_greach h0 hA0 hr
        refine ⟨e1, hCe, fun x hx => ?_⟩
        rw [← hk1 x hx]
        exact step_gate_keep hM (allowed_of_sinv hSI c1) hS hs hx
  | @hw s1 K1 Ch1 v a y _ hH ih =>
    obtain ⟨hE, hX, e1, hCe, hk1⟩ := ih
    obtain ⟨-, hK, -, hM⟩ := exec_safeRunPA h0 hA0 hK0 hU0 hM0 hE
    refine ⟨.hw hE hH, hX, e1, hCe, fun x hx => ?_⟩
    rw [← hk1 x hx]
    exact hw_gate_keep hK hM hH hx
  | @mmu s1 K1 Ch1 a y _ hH ih =>
    obtain ⟨hE, hX, e1, hCe, hk1⟩ := ih
    refine ⟨.mmu hE hH, hX, e1, hCe, fun x hx => ?_⟩
    rw [← hk1 x hx]
    exact mmu_gate_keep hH hx

end exec

/-! ## The top -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **FL4 end to end with every slot and the page walker's A/D writes to free leaves** (module docstring):
`serializable_fl4_localU2`'s premises, over `ExecU3` (core steps, VCPU hardware steps, `MmuLeaf` A/D writes, each
an `MmuAD` [P] write); the A/D writes are entries of the serial order. -/
theorem serializable_fl4_localU3 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecU3 (PathsP.sum (fl4LocW11JA st ar hA (masksWr_plain st) L.total a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
          (cmSlotU st ar hA (masksWr_plain st))))
      (StartV2 st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  obtain ⟨hK0, hU0⟩ := okP_R hB hc0
  refine serializable_e2ePA _ h0 hA0 hK0 hU0 hM0 (execPA_of_U3G ?_ P h0 hA0 hB hc0 hM0 h).1 hq
  intro Ch K s hK hU c hs q i hC hE hsf
  have nv : K.vcpus = ∅ := by
    obtain ⟨_, ⟨nv, _⟩, _⟩ := hE
    exact nv
  rcases i with i | ((j | j) | j)
  · exact startAt_U st ar hA (masksWr_plain st) L.total a0 P hIoa hC hE (startU_of_U2 st ar hA a0 hC nv hsf)
  · exact delPteStart_at st ar hA (masksWr_plain st) hC hE (hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v)
  · exact invStartU2_at st ar hA (masksWr_plain st) hC hE (hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v)
  · exact cmStartU2_at st ar hA (masksWr_plain st) hC hE (hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v)

/-- U3 contains U2: `serializable_fl4_localU2` is U3 at executions without A/D writes. -/
theorem serializable_fl4_localU2_viaU3 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPR (PathsP.sum (fl4LocW11JA st ar hA (masksWr_plain st) L.total a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
          (cmSlotU st ar hA (masksWr_plain st))))
      (StartV2 st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_fl4_localU3 st ar hA a0 P hIoa h0 hA0 hB hc0 hM0 (execU3_of_WPR h) hq

end top

end
end Fl4Proofs.P2.E2EP
