/-
P2: **`serializable_e2e`'s hypotheses are satisfiable, with entries running**.

For the empty layout (no objects, no slots, no user words) and no local paths,
from any memory `m0` and for any serial body `p` with a run to `m'`, an execution
of FL4 (`E2E.Exec`) takes the gate (ticket, scan of its own core, drain), runs
`p` and opens the gate again, and a core then runs a local attempt that is pure
glue (arms `.done`, enters, leaves). Every premise of `serializable_e2e` holds on
it, so its conclusion is about this execution: memory `m'`, log `[p, .done]`.

No premises.
-/
import Fl4Proofs.P2.OwnLayout
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EWitness
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.E2E Fl4Proofs.P2.Serial Fl4Proofs.P2.OwnMap

noncomputable section
open Classical

/-- The empty layout. -/
def K0 : KLayout := ⟨fun _ => none, 0#u64, 0, ∅, ∅⟩

theorem layP0 : LayP K0 where
  heap := ⟨fun _ _ h => (by simp [K0] at h), fun _ _ h => (by simp [K0] at h),
    fun _ _ h => (by simp [K0] at h), fun _ _ h => (by simp [K0] at h),
    fun _ _ _ _ h => (by simp [K0] at h)⟩
  node _ _ _ _ h := by simp [K0] at h
  slot _ h := by simp [K0] at h
  user _ h := by simp [K0] at h
  userSlot _ h := by simp [K0] at h

theorem rk0 : RegionOK K0 := regionOK_of layP0
theorem uk0 : UserOK K0 := userOK_of layP0

/-- No local paths. -/
def LP0 : Paths Empty := fun i => i.elim

/-- The start: every core idle, gate open, the maps the empty layout's. -/
def s0 (m0 : U64 → U64) : Cfg U64 U64 U64 U64 where
  mem := m0
  gate := .opn
  holder := none
  seen := ∅
  lk := fun _ => none
  ph := fun _ => .idle
  own := own K0
  cls := cls K0
  ko := ko K0 m0
  log := []

theorem not_ser_opn {s : Cfg U64 U64 U64 U64} {c : U64} (h : s.gate ≠ .closed) : ¬ SerStep s c :=
  fun hs => h hs.1

/-- A step that is no serial body, arms nothing and starts nothing, keeping `K0`. -/
theorem fstep {s s' : Cfg U64 U64 U64 U64} {c : U64} (hg : s.gate ≠ .closed)
    (ha : ∀ p, s'.ph c = .arm p → PureGlue p)
    (hst : ∀ p0 k W, s.ph c ≠ .loc p0 (.start k) W) : Fl4Step LP0 s K0 c s' K0 where
  arm := ha
  start p0 k W h := absurd h (hst p0 k W)
  ser h := absurd h (not_ser_opn hg)
  keep _ := rfl

/-- **The witness.** -/
theorem witness (m0 m' : U64 → U64) (p : Prog U64 U64 U64) (hp : Run p m0 m') :
    ∃ s, Exec LP0 (s0 m0) K0 s K0 ∧ Init (s0 m0) ∧ ArmInv (s0 m0) ∧ Maps K0 (s0 m0) ∧
      NoLoc s ∧ s.log = [p, .done] ∧ s.mem = m' := by
  let c : U64 := 0#u64
  -- take
  have t1 : Step (s0 m0) c
        { s0 m0 with holder := some c, seen := ∅, ph := Function.update (s0 m0).ph c (.ser p), gate := if (s0 m0).gate = .opn then .draining else (s0 m0).gate } :=
    Step.take p rfl rfl
  generalize hs1 :
        ({ s0 m0 with holder := some c, seen := ∅, ph := Function.update (s0 m0).ph c (.ser p), gate := if (s0 m0).gate = .opn then .draining else (s0 m0).gate } : Cfg U64 U64 U64 U64) = s1
    at t1
  have g1 : s1.gate = .draining := by rw [← hs1]; rfl
  have h1 : s1.holder = some c := by rw [← hs1]
  have p1 : s1.ph = Function.update (fun _ => .idle) c (.ser p) := by rw [← hs1]; rfl
  have m1 : s1.mem = m0 := by rw [← hs1]; rfl
  have e1 : Exec LP0 (s0 m0) K0 s1 K0 :=
    .step .refl t1 (fstep (by intro h; cases h) (by
      intro q hq; rw [p1, Function.update_self] at hq; cases hq) (by
      intro p0 k W h; cases h))
  -- scan its own core
  have t2 : Step s1 c { s1 with seen := insert c s1.seen } :=
    Step.scan c h1 g1 (by rw [p1, Function.update_self]; exact fun h => h)
  generalize hs2 : ({ s1 with seen := insert c s1.seen } : Cfg U64 U64 U64 U64) = s2 at t2
  have e2 : Exec LP0 (s0 m0) K0 s2 K0 :=
    .step e1 t2 (fstep (by rw [g1]; intro h; cases h) (by
      intro q hq; rw [← hs2] at hq; simp only [p1, Function.update_self] at hq; cases hq) (by
      intro p0 k W h; rw [p1, Function.update_self] at h; cases h))
  have g2 : s2.gate = .draining := by rw [← hs2]; exact g1
  have h2 : s2.holder = some c := by rw [← hs2]; exact h1
  have p2 : s2.ph = s1.ph := by rw [← hs2]
  -- drain
  have hall : ∀ d, d ∈ s2.seen ∨ s2.ph d = .idle := by
    intro d
    by_cases hd : d = c
    · left; rw [← hs2, hd]; exact Set.mem_insert _ _
    · right; rw [p2, p1, Function.update_of_ne hd]
  have t3 : Step s2 c { s2 with gate := .closed } := Step.drain h2 g2 hall
  generalize hs3 : ({ s2 with gate := .closed } : Cfg U64 U64 U64 U64) = s3 at t3
  have e3 : Exec LP0 (s0 m0) K0 s3 K0 :=
    .step e2 t3 (fstep (by rw [g2]; intro h; cases h) (by
      intro q hq; rw [← hs3] at hq; simp only [p2, p1, Function.update_self] at hq; cases hq) (by
      intro p0 k W h; rw [p2, p1, Function.update_self] at h; cases h))
  have g3 : s3.gate = .closed := by rw [← hs3]
  have h3 : s3.holder = some c := by rw [← hs3]; exact h2
  have p3 : s3.ph = s1.ph := by rw [← hs3]; exact p2
  have m3 : s3.mem = m0 := by rw [← hs3, ← hs2]; exact m1
  have l3 : s3.log = [] := by rw [← hs3, ← hs2, ← hs1]; rfl
  -- the serial body, opening the gate
  have t4 : Step s3 c
        { s3 with mem := m', holder := none, ph := Function.update s3.ph c .idle, gate := if false then .closed else .opn, log := s3.log ++ [p], own := own K0, cls := cls K0, ko := ko K0 m' } :=
    Step.serial false (own K0) (cls K0) (ko K0 m') h3 g3 (by rw [p3, p1, Function.update_self])
      (by rw [m3]; exact hp)
  generalize hs4 :
        ({ s3 with mem := m', holder := none, ph := Function.update s3.ph c .idle, gate := if false then .closed else .opn, log := s3.log ++ [p], own := own K0, cls := cls K0, ko := ko K0 m' } : Cfg U64 U64 U64 U64) = s4 at t4
  have p4 : s4.ph = fun _ => .idle := by
    rw [← hs4]; funext d
    show Function.update s3.ph c .idle d = .idle
    by_cases hd : d = c
    · rw [hd, Function.update_self]
    · rw [Function.update_of_ne hd, p3, p1, Function.update_of_ne hd]
  have e4 : Exec LP0 (s0 m0) K0 s4 K0 := by
    refine .step e3 t4 ⟨?_, ?_, fun _ => ⟨rk0, uk0, ?_⟩, fun h => absurd ⟨g3, h3⟩ h⟩
    · intro q hq; rw [p4] at hq; cases hq
    · intro p0 k W h; rw [p3, p1, Function.update_self] at h; cases h
    · rw [← hs4]; exact ⟨rfl, rfl, rfl⟩
  have g4 : s4.gate = .opn := by rw [← hs4]; rfl
  have m4 : s4.mem = m' := by rw [← hs4]
  have l4 : s4.log = [p] := by rw [← hs4]; show s3.log ++ [p] = [p]; rw [l3]; rfl
  have lk4 : s4.lk = fun _ => none := by rw [← hs4, ← hs3, ← hs2, ← hs1]; rfl
  -- a local attempt of pure glue: arm `.done`, enter, leave
  have t5 : Step s4 c { s4 with ph := Function.update s4.ph c (.arm .done) } :=
    Step.arm .done (by rw [p4])
  generalize hs5 : ({ s4 with ph := Function.update s4.ph c (.arm .done) } :
    Cfg U64 U64 U64 U64) = s5 at t5
  have p5 : s5.ph = Function.update (fun _ => .idle) c (.arm .done) := by rw [← hs5, p4]
  have e5 : Exec LP0 (s0 m0) K0 s5 K0 :=
    .step e4 t5 (fstep (by rw [g4]; intro h; cases h) (by
      intro q hq; rw [p5, Function.update_self] at hq; cases hq; exact .done) (by
      intro p0 k W h; rw [p4] at h; cases h))
  have g5 : s5.gate = .opn := by rw [← hs5]; exact g4
  have t6 : Step s5 c { s5 with ph := Function.update s5.ph c (.loc .done .done ∅) } :=
    Step.enter (by rw [p5, Function.update_self]) g5
  generalize hs6 : ({ s5 with ph := Function.update s5.ph c (.loc .done .done ∅) } :
    Cfg U64 U64 U64 U64) = s6 at t6
  have p6 : s6.ph = Function.update (fun _ => .idle) c (.loc .done .done ∅) := by
    rw [← hs6, p5, Function.update_idem]
  have e6 : Exec LP0 (s0 m0) K0 s6 K0 :=
    .step e5 t6 (fstep (by rw [g5]; intro h; cases h) (by
      intro q hq; rw [p6, Function.update_self] at hq; cases hq) (by
      intro p0 k W h; rw [p5, Function.update_self] at h; cases h))
  have g6 : s6.gate = .opn := by rw [← hs6]; exact g5
  have t7 : Step s6 c
        { s6 with lk := release s6.lk c, ph := Function.update s6.ph c .idle, log := s6.log ++ [.done] } := Step.leave (by rw [p6, Function.update_self])
  generalize hs7 :
        ({ s6 with lk := release s6.lk c, ph := Function.update s6.ph c .idle, log := s6.log ++ [.done] } : Cfg U64 U64 U64 U64) = s7 at t7
  have p7 : s7.ph = fun _ => .idle := by
    rw [← hs7, p6, Function.update_idem]; funext d
    show Function.update (fun _ => Phase.idle) c Phase.idle d = Phase.idle
    by_cases hd : d = c
    · rw [hd, Function.update_self]
    · rw [Function.update_of_ne hd]
  have e7 : Exec LP0 (s0 m0) K0 s7 K0 :=
    .step e6 t7 (fstep (by rw [g6]; intro h; cases h) (by
      intro q hq; rw [p7] at hq; cases hq) (by
      intro p0 k W h; rw [p6, Function.update_self] at h; cases h))
  refine ⟨s7, e7, ⟨rfl, fun d h => h⟩, fun d q h => (by cases h), ⟨rfl, rfl, rfl⟩,
    fun d => by rw [p7]; exact Phase.idle_not_loc, ?_, ?_⟩
  · rw [← hs7, ← hs6, ← hs5]; show s4.log ++ [.done] = _; rw [l4]; rfl
  · rw [← hs7, ← hs6, ← hs5]; exact m4

/-- `serializable_e2e` on the witness: its conclusion holds there. -/
theorem witness_e2e (m0 m' : U64 → U64) (p : Prog U64 U64 U64) (hp : Run p m0 m') :
    ∃ s K, Exec LP0 (s0 m0) K0 s K ∧ NoLoc s ∧ s.log = [p, .done] ∧
      RunAll s.log (s0 m0).mem s.mem := by
  obtain ⟨s, e, h0, hA, hM, hq, hl, -⟩ := witness m0 m' p hp
  exact ⟨s, K0, e, hq, hl, serializable_e2e LP0 h0 hA rk0 uk0 hM e hq⟩

end
end Fl4Proofs.P2.E2EWitness
