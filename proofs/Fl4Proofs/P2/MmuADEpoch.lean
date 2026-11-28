/-
# P2 (line mmuAD, gen 3): the epoch under upper-level A/D writes — `ptesR` is A/D-blind, `ExecU3b`

`serializable_fl4_localU3` (P2/E2EPU3.lean) admits A/D writes to free leaves only. Its epoch invariant (every start
state's gate words agree with a memory `s1` with `K.ptes = ptesR K s1.mem`, the form every slot's start fact
consumes) used that a leaf is never a gate word. A bits on the upper paging levels *are* gate words. This module
proves that the epoch survives them, and states the execution relation with them:

* **Walks are A/D-blind**: `walk1_adEq` / `walkStep_adEq` / `walk2_adEq` / `walk3_adEq` (equal on `ADEqM`
  memories: they test only bits 0 and 7 and the address bits, `eP_adEq` / `eS_adEq` / `eT_adEq`).
* `AsidW` (the ASID-table and named-pool words, read raw by `NamedM`), `UpW` (the upper-level entries a walk from
  a named root reads), `walkW_iff` (`WalkW` is their union). `AgA ksb m m'`: `ADEqM m m'` and equality on the
  `AsidW` words of `m`. **`ptesR_agA`**: `ptesR K m = ptesR K m'` under `AgA` (`namedM_agA`, `asidW_agA`,
  `upW_agA`, `walkW_agA`).
* **`PWE K E`**, the paging words of an epoch with memory `E`: the leaves `K.ptes`, and the upper-level entries
  `UpW K.ksb E` that are not `AsidW` words, lie in `own`'s `.none` region, and are neither user words nor in the
  kernel-state block (the filters `ptesR` itself applies to leaves; FL4's paging tables are untyped-retyped `.other`
  objects, so every real upper-level entry passes them). `pwe_asid`: no `AsidW` word is in `PWE`.
* `adWr_pwe`: every `MmuAD (PWE K E)` [P] write is a `Serial.ADWr (PWE K E) ADEq NotPresent` (whatever its lock
  state), and `maps_pwe`: it keeps the rule-8 ghost maps (`ko_upd_none`).
* **`EpochJ K E s`**: no VCPU, `K.ptes = ptesR K E`, and every gate word of `s` is `ADEq` to `E` on `PWE`, equal
  off it. `epochJ_ser` (a serial exit starts one), `epochJ_keep` (steps keeping the gate words: every non-serial
  allowed core step, `step_gate_keep`, and every VCPU hardware step, `hw_gate_keep`), **`epochJ_mmu`** (an A/D
  write), **`epoch_start`**: an `EpochJ` state gives the start facts' epoch premise exactly (`s1` := the gate words
  of `s`, `E` elsewhere; `ptesR_agA`).
* **`ExecU3b`**: `ExecU3H`'s steps with the word set `PWE K E` of the current epoch (`E` = the memory at the last
  serial exit, an index of the relation), and `execU3b_of_U3` (every `ExecU3` execution is one).

## Why `serializable_fl4_localU3b` is not proved here (reported, not narrowed)
Gen 2's plan reduced the per-path obligation to `SADIns (PWE K E) ADEq NotPresent User P.p` of each slot's explicit
tree. **That is false for every slot of the U2 family**: the predicate quantifies over every branch of the tree,
and the trees chase pointers read from memory. Concrete case, shared by delPte, CNodeDelete and Copy/Mint
(`InvProgSrc.invBodyG`, Rust `localinv.rs` l. 172-173) and by the syscall-entry W11 paths: `sched.cur_thread` reads
the node word `CUR_THREAD` (value `t`), then `msg.msg_info` reads `t + REGS + 8·RSI` and decodes
`length := w &&& 0x7f` (`msginfo.rs` l. 19), which contains bits 5 and 6. On the branch where the `CUR_THREAD` word
holds `x - (REGS + 8·RSI)` for an upper-level entry `x ∈ PWE K E`, the tree reads `x` and its continuation for `v`
and `v ||| 32` differ (length 0 vs 32). `sadIns_rd_sens` is the formal shape: such a node is not `SADIns`. The
branch is never taken in a real execution (`t` is a TCB, `Pre`), so the obligation that holds is *along the
execution*, not over the tree: see the handoff (gen 4 plan: a run-relative `ADIns` in `Serial`, discharged per slot
by an `AvoidE`-style "reads no upper-level entry" fact, or masked reads for the walks of Delete).

No [W], no new [J]; the only [P] is `MmuAD` (P2/MmuADWalk.lean). No existing statement or file changed.
-/
import Fl4Proofs.P2.E2EPU3b
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (SP SerStep)
open Fl4Proofs.P2.Serial (Cfg Step hwCfg ADWr)
open Fl4Proofs.P3.Vs (peA atA UserV eP eS eT eA)
open Fl4Proofs.P2.MmuAD (MmuAD ADEq ADEqM adBits adKeep and_eq_of_adEq kP kPS adOr_adEq adEq_trans NotPresent
  SADIns)

noncomputable section
open Classical

/-! ## 1. The walks read only bits other than A and D -/

section walk

theorem kEA : (4503599627366400#u64 : U64) &&& adBits = 0#u64 := by decide

theorem eP_adEq {v w : U64} (h : ADEq v w) : eP v ↔ eP w := by
  unfold eP; rw [and_eq_of_adEq h kP]

theorem eS_adEq {v w : U64} (h : ADEq v w) : eS v ↔ eS w := by
  unfold eS; rw [and_eq_of_adEq h kPS]

theorem eT_adEq {v w : U64} (h : ADEq v w) : eT v = eT w := by
  unfold eT eA; rw [and_eq_of_adEq h kEA]

variable {m m' : U64 → U64}

theorem walk1_adEq (h : ADEqM m m') (r v : U64) : walk1 m r v = walk1 m' r v := by
  unfold walk1
  have hp := eP_adEq (h (peA r (Fl4Proofs.P3.Vs.vIdx v 39)))
  by_cases h1 : eP (m (peA r (Fl4Proofs.P3.Vs.vIdx v 39)))
  · rw [if_pos h1, if_pos (hp.mp h1), eT_adEq (h _)]
  · rw [if_neg h1, if_neg (fun h2 => h1 (hp.mpr h2))]

theorem walkStep_adEq (h : ADEqM m m') (v : U64) (sh : Nat) (o : Option U64) :
    walkStep m v sh o = walkStep m' v sh o := by
  cases o with
  | none => rfl
  | some x =>
    have hc : (eP (m x) ∧ ¬ eS (m x)) ↔ (eP (m' x) ∧ ¬ eS (m' x)) := by
      rw [eP_adEq (h x), eS_adEq (h x)]
    simp only [walkStep]
    by_cases h1 : eP (m x) ∧ ¬ eS (m x)
    · rw [if_pos h1, if_pos (hc.mp h1), eT_adEq (h x)]
    · rw [if_neg h1, if_neg (fun h2 => h1 (hc.mpr h2))]

theorem walk2_adEq (h : ADEqM m m') (r v : U64) : walk2 m r v = walk2 m' r v := by
  unfold walk2; rw [walk1_adEq h, walkStep_adEq h]

theorem walk3_adEq (h : ADEqM m m') (r v : U64) : walk3 m r v = walk3 m' r v := by
  unfold walk3; rw [walk2_adEq h, walkStep_adEq h]

end walk

/-! ## 2. `ptesR` is A/D-blind when the ASID words are unchanged -/

section conv

/-- The ASID-table words and the named pools' words (read raw by `NamedM`): `WalkW`'s first two parts. -/
def AsidW (ksb : U64) (m : U64 → U64) (b : U64) : Prop :=
  (∃ hi : U64, hi.val < 2048 ∧ b = atA ksb hi) ∨
  (∃ hi : U64, hi.val < 2048 ∧ m (atA ksb hi) ≠ 0#u64 ∧ ∃ lo : U64, lo.val < 512 ∧ b = peA (m (atA ksb hi)) lo)

/-- The upper-level entries a walk from a named root reads: `WalkW`'s third part. -/
def UpW (ksb : U64) (m : U64 → U64) (b : U64) : Prop :=
  ∃ r, NamedM m ksb r ∧ ∃ v, UserV v ∧
    (b = peA r (Fl4Proofs.P3.Vs.vIdx v 39) ∨ walk1 m r v = some b ∨ walk2 m r v = some b)

theorem walkW_iff {ksb : U64} {m : U64 → U64} {b : U64} : WalkW ksb m b ↔ AsidW ksb m b ∨ UpW ksb m b := by
  unfold WalkW AsidW UpW; exact or_assoc.symm

/-- Two memories `ADEq` everywhere and equal on the ASID words of the first. -/
def AgA (ksb : U64) (m m' : U64 → U64) : Prop := ADEqM m m' ∧ ∀ b, AsidW ksb m b → m b = m' b

variable {ksb : U64} {m m' : U64 → U64}

theorem tab_agA (h : AgA ksb m m') {hi : U64} (hh : hi.val < 2048) : m (atA ksb hi) = m' (atA ksb hi) :=
  h.2 _ (Or.inl ⟨hi, hh, rfl⟩)

theorem pool_agA (h : AgA ksb m m') {hi lo : U64} (hh : hi.val < 2048) (h0 : m (atA ksb hi) ≠ 0#u64)
    (hl : lo.val < 512) : m (peA (m (atA ksb hi)) lo) = m' (peA (m' (atA ksb hi)) lo) := by
  have e := h.2 _ (Or.inr ⟨hi, hh, h0, lo, hl, rfl⟩)
  rw [← tab_agA h hh]; exact e

theorem namedM_agA (h : AgA ksb m m') (r : U64) : NamedM m ksb r ↔ NamedM m' ksb r := by
  constructor
  · rintro ⟨hi, hh, h0, lo, hl, hr, hr0, hr1⟩
    refine ⟨hi, hh, by rw [← tab_agA h hh]; exact h0, lo, hl, ?_, hr0, hr1⟩
    rw [hr]; exact pool_agA h hh h0 hl
  · rintro ⟨hi, hh, h0, lo, hl, hr, hr0, hr1⟩
    have h0' : m (atA ksb hi) ≠ 0#u64 := by rw [tab_agA h hh]; exact h0
    refine ⟨hi, hh, h0', lo, hl, ?_, hr0, hr1⟩
    rw [hr]; exact (pool_agA h hh h0' hl).symm

theorem asidW_agA (h : AgA ksb m m') (b : U64) : AsidW ksb m b ↔ AsidW ksb m' b := by
  unfold AsidW
  constructor
  · rintro (⟨hi, hh, rfl⟩ | ⟨hi, hh, h0, lo, hl, rfl⟩)
    · exact Or.inl ⟨hi, hh, rfl⟩
    · exact Or.inr ⟨hi, hh, by rw [← tab_agA h hh]; exact h0, lo, hl, by rw [tab_agA h hh]⟩
  · rintro (⟨hi, hh, rfl⟩ | ⟨hi, hh, h0, lo, hl, rfl⟩)
    · exact Or.inl ⟨hi, hh, rfl⟩
    · exact Or.inr ⟨hi, hh, by rw [tab_agA h hh]; exact h0, lo, hl, by rw [tab_agA h hh]⟩

theorem upW_agA (h : AgA ksb m m') (b : U64) : UpW ksb m b ↔ UpW ksb m' b := by
  unfold UpW
  simp only [namedM_agA h, walk1_adEq h.1, walk2_adEq h.1]

theorem walkW_agA (h : AgA ksb m m') (b : U64) : WalkW ksb m b ↔ WalkW ksb m' b := by
  rw [walkW_iff, walkW_iff, asidW_agA h, upW_agA h]

/-- **The reachability convention is A/D-blind** (module docstring). -/
theorem ptesR_agA {K : KLayoutP} (h : AgA K.ksb m m') : ptesR K m = ptesR K m' := by
  ext e
  unfold ptesR
  simp only [Set.mem_setOf_eq, namedM_agA h, walk3_adEq h.1, walkW_agA h]

end conv

/-! ## 3. The paging words of an epoch -/

section pwe
variable {K : KLayoutP}

/-- **The paging words of the epoch with memory `E`** (module docstring). -/
def PWE (K : KLayoutP) (E : U64 → U64) (b : U64) : Prop :=
  b ∈ K.ptes ∨ (UpW K.ksb E b ∧ ¬ AsidW K.ksb E b ∧ OwnMap.region K.toKLayout b = .none ∧ b ∉ K.user ∧
    ∀ o : U64, o.val < 13568 → b ≠ core.num.U64.wrapping_add K.ksb o)

/-- No ASID word is a paging word of the epoch. -/
theorem pwe_asid {E : U64 → U64} (hc : K.ptes = ptesR K E) {b : U64} (ha : AsidW K.ksb E b) : ¬ PWE K E b := by
  rintro (hp | ⟨-, hn, -⟩)
  · rw [hc] at hp; exact hp.2.1 (walkW_iff.mpr (Or.inl ha))
  · exact hn ha

theorem pwe_region (hK : RegionOKP K) {E : U64 → U64} {b : U64} (h : PWE K E b) :
    OwnMap.region K.toKLayout b = .none := by
  rcases h with hp | h
  · exact hK.none b hp
  · exact h.2.2.1

open OwnMap in
/-- A write to a `.none`-region word keeps `ko`. -/
theorem ko_upd_none (hK : RegionOKP K) {m : U64 → U64} {a v : U64} (ha : region K.toKLayout a = .none) :
    ko K.toKLayout (Function.update m a v) = ko K.toKLayout m := by
  funext b
  unfold ko
  cases hr : region K.toKLayout b with
  | tcb t =>
    have ht := hK.base.base.tcbOf t b hr
    have hne : fld t oAFFINITY ≠ a := by
      intro e
      have h1 := (hK.base.base.tcb t ht oAFFINITY (Or.inl rfl)).1
      rw [e, ha] at h1; cases h1
    simp only [Function.update_of_ne hne]
  | _ => rfl

/-- **Every A/D write to a paging word of the epoch is an `ADWr`**, any lock state. -/
theorem adWr_pwe (hK : RegionOKP K) {E : U64 → U64} {s : Cfg U64 U64 U64 U64} {a x : U64} (hM : MapsP K s)
    (h : MmuAD (PWE K E) s.mem a x) : ADWr (PWE K E) ADEq NotPresent s a x :=
  MmuAD.MmuAD.adWr_none hK hM (pwe_region hK h.pw) h

/-- An A/D write to a paging word keeps the rule-8 ghost maps. -/
theorem maps_pwe (hK : RegionOKP K) {E : U64 → U64} {s : Cfg U64 U64 U64 U64} {a x : U64} (hM : MapsP K s)
    (h : MmuAD (PWE K E) s.mem a x) : MapsP K (hwCfg s a x) := by
  refine ⟨hM.own, hM.cls, ?_⟩
  show s.ko = OwnMap.ko K.toKLayout (Function.update s.mem a x)
  rw [ko_upd_none hK (pwe_region hK h.pw)]
  exact hM.ko

end pwe

/-! ## 4. The epoch invariant -/

section epoch
variable {K : KLayoutP} {E : U64 → U64}

/-- **The epoch invariant with A/D writes** (module docstring). -/
structure EpochJ (K : KLayoutP) (E : U64 → U64) (s : Cfg U64 U64 U64 U64) : Prop where
  nv : K.vcpus = ∅
  conv : K.ptes = ptesR K E
  pw : ∀ x, GateW K x → PWE K E x → ADEq (s.mem x) (E x)
  eq : ∀ x, GateW K x → ¬ PWE K E x → s.mem x = E x

/-- A serial exit with the convention starts an epoch. -/
theorem epochJ_ser {s : Cfg U64 U64 U64 U64} (hc : K.vcpus = ∅ ∧ K.ptes = ptesR K s.mem) : EpochJ K s.mem s :=
  ⟨hc.1, hc.2, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

/-- A step keeping every gate word keeps the epoch. -/
theorem epochJ_keep {s s' : Cfg U64 U64 U64 U64} (J : EpochJ K E s) (hk : ∀ x, GateW K x → s'.mem x = s.mem x) :
    EpochJ K E s' :=
  ⟨J.nv, J.conv, fun x hg hp => by rw [hk x hg]; exact J.pw x hg hp,
    fun x hg hp => by rw [hk x hg]; exact J.eq x hg hp⟩

/-- **An A/D write to a paging word of the epoch keeps the epoch.** -/
theorem epochJ_mmu {s : Cfg U64 U64 U64 U64} {a y : U64} (J : EpochJ K E s) (h : MmuAD (PWE K E) s.mem a y) :
    EpochJ K E (hwCfg s a y) := by
  refine ⟨J.nv, J.conv, fun x hg hp => ?_, fun x hg hp => ?_⟩
  · show ADEq (Function.update s.mem a y x) (E x)
    by_cases hx : x = a
    · subst hx; rw [Function.update_self]; exact adEq_trans (adOr_adEq h.ad) (J.pw x hg hp)
    · rw [Function.update_of_ne hx]; exact J.pw x hg hp
  · show Function.update s.mem a y x = E x
    have hx : x ≠ a := fun e => hp (e ▸ h.pw)
    rw [Function.update_of_ne hx]; exact J.eq x hg hp

/-- **An epoch state gives the start facts' epoch premise** (module docstring). -/
theorem epoch_start {s : Cfg U64 U64 U64 U64} (J : EpochJ K E s) :
    ∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → s.mem x = s1.mem x := by
  let f : U64 → U64 := fun x => if GateW K x then s.mem x else E x
  have key : ∀ x, ADEq (E x) (f x) := by
    intro x
    unfold ADEq
    by_cases hg : GateW K x
    · show _ = (if GateW K x then s.mem x else E x) &&& _
      rw [if_pos hg]
      by_cases hp : PWE K E x
      · exact Eq.symm (J.pw x hg hp)
      · rw [J.eq x hg hp]
    · show _ = (if GateW K x then s.mem x else E x) &&& _
      rw [if_neg hg]
  have hA : AgA K.ksb E f := by
    refine ⟨key, fun b hb => ?_⟩
    show E b = if GateW K b then s.mem b else E b
    by_cases hg : GateW K b
    · rw [if_pos hg, J.eq b hg (pwe_asid J.conv hb)]
    · rw [if_neg hg]
  refine ⟨{ s with mem := f }, ⟨J.nv, ?_⟩, fun x hx => ?_⟩
  · show K.ptes = ptesR K f
    rw [J.conv]; exact ptesR_agA hA
  · show s.mem x = if GateW K x then s.mem x else E x
    rw [if_pos hx]

end epoch

/-! ## 5. Executions with A/D writes to every paging word of the epoch -/

section exec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {ι : Type}

/-- **An execution of FL4 with the U2 glue, the VCPU hardware and A/D writes to the epoch's paging words**
(module docstring); the last index is the epoch memory (the memory at the last serial exit). The `mmu` step is
`MmuAD` [P] over `PWE K E`: leaves in any lock state and the upper-level entries. -/
inductive ExecU3b (LP : PathsP ι)
    (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s0 : Cfg U64 U64 U64 U64) (K0 : KLayoutP) (Ch0 : S → Prop) :
    Cfg U64 U64 U64 U64 → KLayoutP → (S → Prop) → (U64 → U64) → Prop
  | refl : ExecU3b LP SF P s0 K0 Ch0 s0 K0 Ch0 s0.mem
  | step {s s' : Cfg U64 U64 U64 U64} {K K' : KLayoutP} {Ch Ch' : S → Prop} {c : U64} {E : U64 → U64} :
      ExecU3b LP SF P s0 K0 Ch0 s K Ch E → Step s c s' → Fl4StepWPR LP SF P s K Ch c s' K' Ch' →
      ExecU3b LP SF P s0 K0 Ch0 s' K' Ch' (if SerStep s c then s'.mem else E)
  | hw {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {Ch : S → Prop} {E : U64 → U64} {v a x : U64} :
      ExecU3b LP SF P s0 K0 Ch0 s K Ch E → HwStepP K s v a x → ExecU3b LP SF P s0 K0 Ch0 (hwCfg s a x) K Ch E
  | mmu {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {Ch : S → Prop} {E : U64 → U64} {a x : U64} :
      ExecU3b LP SF P s0 K0 Ch0 s K Ch E → MmuAD (PWE K E) s.mem a x →
      ExecU3b LP SF P s0 K0 Ch0 (hwCfg s a x) K Ch E

end exec

end
end Fl4Proofs.P2.E2EP

namespace Fl4Proofs.P2.MmuAD

/-- **The formal shape of the gen-3 counterexample** (`MmuADEpoch` module docstring): a read of a `G` word whose
continuation tells two `Q`-equivalent values apart is not `SADIns`. -/
theorem sadIns_rd_sens {G : U64 → Prop} {Q : U64 → U64 → Prop} {NP User : U64 → Prop} {X : Type} {q : U64}
    {k : U64 → Fl4Proofs.P2.PathObl.SProg X} (hg : G q) {u w : U64} (hq : Q u w) (hne : k u ≠ k w) :
    ¬ SADIns G Q NP User (.rd q k) := by
  intro h
  cases h with
  | rd h1 _ => exact hne (h1 hg u w hq)

end Fl4Proofs.P2.MmuAD
