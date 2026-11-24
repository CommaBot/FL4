/-
P2 (DESIGN.md §9): **the footprint premise of `Serial` from per-path safety**.

`Serial.serializable_reach` assumes `FootprintOK` [W]: every local-path step of
every execution is `Allowed`. This module derives it from properties of each
local path taken one at a time, at the moment its body starts, so that the
per-path obligations of `PathObl.lean` can discharge it.

A local path's program is the fl4-sync glue (speculative reads and lock
attempts: `Glue`), then a `start` marker, then the extracted body. The glue
needs no ownership. The body must be `Safe` from this core's view when it
starts: every read it makes is of a word the core holds (its core, its locks)
or the gate owns, or is speculative; every write is of a word it holds and
moves owners only between owners it holds. `Safe` is a property of the body's
*sequential* run from the memory at its start, with the core's locks fixed
(the body takes no locks).

The point is stability (`Safe.foreign`): another core's write, which `Allowed`
restricts to words that core holds and to owner moves between its own owners,
keeps a running body `Safe` from the new memory. This needs `Deciders` [W] of
the ownership map: a word's owner changes only through a write to a word with
the same owner or the gate's (the map's deciding words, e.g. a thread's
`STATE` for its queue links, lie in the group they decide).

Theorems:
* `footprintOK_of_safe`: `ArmGlue`, `BodyOK`, `DecidersOK` give `FootprintOK`.
* `serializable_safe`: hence `Serial.serializable_reach` without the
  `FootprintOK` premise: every execution that reaches a state with no local
  path in progress equals running its completed entries one after another.
  As there: in that serial order a speculative read may return **any** value,
  not the value memory held at that point; that the result is a real serial
  run of the entry is the per-path refinement obligation (`PathObl.lean`).

Premises (all named, nothing else):
* `ArmGlue s0` [W]: every program a core arms is glue (`Glue`) up to `start`.
  True of the model of fl4-sync's `run_syscall` / `run_vm_fault` /
  `run_timer_irq` local attempts; stated, not derived from the Rust.
* `BodyOK s0` [W]: when a body starts, it is `Safe` from the current memory and
  the core's locks. To be discharged from `PathObl` + `IsProg` per path (the
  bridge), with the glue's guarantee that it starts a body only in a state
  satisfying the body's `Pre` [P] (fl4-sync, trusted).
* `DecidersOK s0` [W]: every ownership map of the execution satisfies
  `Deciders` (for `OwnMap.own`, to be proved from P1's typed-heap disjointness).

## Remaining plan: discharging `BodyOK` (handoff; not yet written)

Goal: `BodyOK` from, per local path, `PathObl` v3 (`PathObl.lean`) for every
Arch instance, `IsProg` [P], `DecOnce` [W], and the glue's `Pre` [P]. Steps:

1. **Choice node.** Add `Serial.Prog.ch (k : Option (V ⊕ Bool) → Prog)` (Arch
   results; `PathObl.AV` maps `u x ↦ some (inl x)`, `b x ↦ some (inr x)`,
   `none ↦ none`); `Run.ch` (any value), `Step.ch` (any value), `Allowed` True,
   `inv_ch` as `inv_rds`, `Within.ch`, `Safe.ch` (∀ values), `Glue` unchanged,
   `Safe.foreign`/`sinv_step`/`allowed_of_sinv` cases as for `rds`.
2. **Translation** `tr : SProg X → Serial.Prog U64 U64 U64` (new module, e.g.
   `P2/E2E.lean`), parameters fixed at body start: `R` (= `ReadSet s`), `User`,
   `ko`, `cls`, the core `c`, `ksb`, `masks`; carries the set `Wd` of words the
   body has written and a cache of pure Arch queries since the last
   state-changing call. A read of `a`: `rd` if `R a ∧ ¬ User a` or `a ∈ Wd`;
   else `rdc a (fun u w => cls a u = cls a w)` if `¬ User a` and `ko a` is
   gate or `core c`; else `rds`. `rdp` as two reads (`a`, `a + 8` wrapping).
   `wr`: dropped for a user word, else `wr` (and add to `Wd`). `zero` / `clr`:
   `wr 0` on each aligned word of the range. `ksb`/`cpu`/`masks`: the
   constants. `arch op k`: a pure query (`Self → Result _` methods) already in
   the cache reuses its value; otherwise `ch`, updating the cache (a
   state-changing call empties it). `ret`/`err`: `done`.
3. **Realizability.** For each branch of `tr p` (values at `rds`/`rdc`/`ch`
   nodes): an alternative entry state `s*` = `s` with each racy word set to
   its branch value (via `LawfulStore.wr`; `DecOnce` and the `Wd` rule make each
   racy word read once, before any write of it), and an oracle Arch instance
   (state: a list of per-segment answer functions `ArchCall → AV`; a pure query
   answers from the head, a state-changing call answers from the head and pops)
   whose `interp` run follows the branch.
4. **Safety of every branch.** Let `R0` be the run from `(s, oracle)`. If it
   accepts, `acc` (instance: the oracle) makes all its reads `ReadSet`, so the
   branch has no racy nodes and is `R0`: `Within` gives `rd` permission
   (`read_own`), `wr` holding (`write_own`), `StepOK` (`move`) gives `MoveV` and
   the class condition. If it declines, `dec_alt` at `s*` gives: the branch
   declines, writes only `DecSet s` (held, `write_own`), and `StepOK` at every
   write. Along the run, `PO`/held sets stay those of the entry (`MoveV`
   preserves them), and `μ` tracks `L.mem` on kernel words (`aligned` +
   `LawfulStore.mem_wr`).
5. Store hypotheses to name: `MasksWr` [P] (`frame_masks` unchanged by `wr`;
   true of `PlainStore`, where it is constant) for `Alt.masks` of `s*`;
   `OwnUserFree` [W] (`own`, `cls`, `ko` do not depend on user words; true of
   `OwnMap`, whose regions are kernel objects) since `μ` is stale on user words.
-/
import Fl4Proofs.P2.Serial

namespace Fl4Proofs.P2.Serial

noncomputable section

variable {A V C L : Type} [DecidableEq A] [DecidableEq C] [DecidableEq L]

/-- Owners a core holding the locks `hs` holds. -/
def HeldV (c : C) (hs : L → Prop) : Owner C L → Prop
  | .core d => d = c
  | .lock l => hs l
  | .gate => False

/-- Owners whose words the core may read: held, or the gate. -/
def PO (c : C) (hs : L → Prop) (o : Owner C L) : Prop := HeldV c hs o ∨ o = .gate

/-- A write from `μ` to `μ'` moves owners only between owners the core holds. -/
def MoveV (own : (A → V) → A → Owner C L) (c : C) (hs : L → Prop) (μ μ' : A → V) : Prop :=
  ∀ x, own μ' x ≠ own μ x → HeldV c hs (own μ x) ∧ HeldV c hs (own μ' x)

/-- **A body safe from core `c`'s view** with locks `hs`, from memory `μ`: its
sequential run reads held or gate-owned words (or reads speculatively) and
writes held words, moving owners only between held owners. -/
inductive Safe (own : (A → V) → A → Owner C L) (cls : A → V → V) (ko : A → ClsOwner C)
    (c : C) (hs : L → Prop) : (A → V) → Prog A V L → Prop
  | done {μ : A → V} : Safe own cls ko c hs μ .done
  | rd {μ : A → V} {a : A} {k : V → Prog A V L} :
      PO c hs (own μ a) → Safe own cls ko c hs μ (k (μ a)) → Safe own cls ko c hs μ (.rd a k)
  | rds {μ : A → V} {a : A} {k : V → Prog A V L} :
      (∀ v, Safe own cls ko c hs μ (k v)) → Safe own cls ko c hs μ (.rds a k)
  | rdc {μ : A → V} {a : A} {K : V → V → Prop} {k : V → Prog A V L} :
      (ko a = .gate ∨ ko a = .core c) → (∀ u w, cls a u = cls a w → K u w) →
      (∀ v, cls a v = cls a (μ a) → Safe own cls ko c hs μ (k v)) →
      Safe own cls ko c hs μ (.rdc a K k)
  | wr {μ : A → V} {a : A} {v : V} {k : Prog A V L} :
      HeldV c hs (own μ a) → MoveV own c hs μ (Function.update μ a v) →
      (cls a v = cls a (μ a) ∨ ko a = .core c ∨ ko a = .free) →
      Safe own cls ko c hs (Function.update μ a v) k → Safe own cls ko c hs μ (.wr a v k)

/-- The fl4-sync glue: speculative reads and lock attempts, up to `start`. -/
inductive Glue (cls : A → V → V) (ko : A → ClsOwner C) (c : C) : Prog A V L → Prop
  | done : Glue cls ko c .done
  | rds {a : A} {k : V → Prog A V L} : (∀ v, Glue cls ko c (k v)) → Glue cls ko c (.rds a k)
  | rdc {a : A} {K : V → V → Prop} {k : V → Prog A V L} :
      (ko a = .gate ∨ ko a = .core c) → (∀ u w, cls a u = cls a w → K u w) →
      (∀ v, Glue cls ko c (k v)) → Glue cls ko c (.rdc a K k)
  | lock {l : L} {k : Bool → Prog A V L} : (∀ b, Glue cls ko c (k b)) → Glue cls ko c (.lock l k)
  | start (k : Prog A V L) : Glue cls ko c (.start k)

/-- **`Deciders`**: a word's owner changes only through a write to a word with
the same owner, or the gate's. -/
def Deciders (own : (A → V) → A → Owner C L) : Prop :=
  ∀ (m : A → V) (b : A) (v : V) (x : A),
    own (Function.update m b v) x ≠ own m x → own m b = own m x ∨ own m b = .gate

/-! ## Basic facts -/

theorem heldV_congr {c : C} {hs hs' : L → Prop} (h : ∀ l, hs l ↔ hs' l) (o : Owner C L) :
    HeldV c hs o ↔ HeldV c hs' o := by
  cases o with
  | core d => exact Iff.rfl
  | lock l => exact h l
  | gate => exact Iff.rfl

theorem held_of_heldV {lk : L → Option C} {c : C} {o : Owner C L}
    (h : HeldV c (fun l => lk l = some c) o) : Held lk c o := by
  cases o <;> exact h

theorem heldV_of_held {lk : L → Option C} {c : C} {o : Owner C L}
    (h : Held lk c o) : HeldV c (fun l => lk l = some c) o := by
  cases o <;> exact h

theorem heldV_ne_gate {c : C} {hs : L → Prop} {o : Owner C L} (h : HeldV c hs o) : o ≠ .gate := by
  rintro rfl; exact h

/-- Another core's held owners are not this core's readable owners. -/
theorem not_PO_of_held {lk : L → Option C} {e d : C} (hed : e ≠ d) {o : Owner C L}
    (h : Held lk e o) : ¬ PO d (fun l => lk l = some d) o := by
  rintro (hd | hg)
  · cases o with
    | core f =>
      have h1 : f = e := h
      have h2 : f = d := hd
      exact hed (h1.symm.trans h2)
    | lock l =>
      have h1 : lk l = some e := h
      have h2 : lk l = some d := hd
      exact hed (Option.some.inj (h1.symm.trans h2))
    | gate => exact h
  · subst hg; exact h

theorem Safe.congr {own : (A → V) → A → Owner C L} {cls : A → V → V} {ko : A → ClsOwner C}
    {c : C} {hs hs' : L → Prop}
    (h : ∀ l, hs l ↔ hs' l) {μ : A → V} {q : Prog A V L} (hS : Safe own cls ko c hs μ q) :
    Safe own cls ko c hs' μ q := by
  induction hS with
  | done => exact .done
  | rd hp _ ih => exact .rd (hp.imp_left (heldV_congr h _).mp) ih
  | rds _ ih => exact .rds ih
  | rdc hko hK _ ih => exact .rdc hko hK ih
  | wr ha hm hcl _ ih =>
    exact .wr ((heldV_congr h _).mp ha)
      (fun x hx => ⟨(heldV_congr h _).mp (hm x hx).1, (heldV_congr h _).mp (hm x hx).2⟩) hcl ih

/-! ## Stability under another core's write -/

/-- What another core's write `b := v` looks like from core `c`: `b` is not a
word `c` may read, and every owner it changes is, before and after, one `c`
may not read. -/
def Foreign (own : (A → V) → A → Owner C L) (cls : A → V → V) (ko : A → ClsOwner C) (c : C)
    (hs : L → Prop) (μ : A → V) (b : A) (v : V) : Prop :=
  ¬ PO c hs (own μ b) ∧ (∀ x, own (Function.update μ b v) x ≠ own μ x →
    ¬ PO c hs (own μ x) ∧ ¬ PO c hs (own (Function.update μ b v) x)) ∧
  (cls b v = cls b (μ b) ∨ (ko b ≠ .gate ∧ ko b ≠ .core c))

theorem Foreign.perm {own : (A → V) → A → Owner C L} {cls : A → V → V} {ko : A → ClsOwner C}
    {c : C} {hs : L → Prop} {μ : A → V}
    {b : A} {v : V} (hF : Foreign own cls ko c hs μ b v) {x : A} (hx : PO c hs (own μ x)) :
    own (Function.update μ b v) x = own μ x ∧ Function.update μ b v x = μ x := by
  refine ⟨?_, ?_⟩
  · by_contra hne; exact (hF.2.1 x hne).1 hx
  · have hxb : x ≠ b := by rintro rfl; exact hF.1 hx
    exact Function.update_of_ne hxb _ _

/-- **Stability**: a body `Safe` from `μ` stays `Safe` after another core's
write that is `Foreign` to it. -/
theorem Safe.foreign {own : (A → V) → A → Owner C L} {cls : A → V → V}
    {ko : A → ClsOwner C} (hD : Deciders own) {c : C}
    {hs : L → Prop} {μ : A → V} {q : Prog A V L} (hS : Safe own cls ko c hs μ q) :
    ∀ {b : A} {v : V}, Foreign own cls ko c hs μ b v →
      Safe own cls ko c hs (Function.update μ b v) q := by
  induction hS with
  | done => intro _ _ _; exact .done
  | @rd μ a k hp _ ih =>
    intro b v hF
    obtain ⟨ho, hv⟩ := hF.perm hp
    refine .rd ?_ ?_
    · rw [ho]; exact hp
    · rw [hv]; exact ih hF
  | rds _ ih => intro b v hF; exact .rds (fun w => ih w hF)
  | @rdc μ a K k hko hK _ ih =>
    intro b v hF
    have hca : cls a (Function.update μ b v a) = cls a (μ a) := by
      by_cases hab : a = b
      · subst hab
        rw [Function.update_self]
        rcases hF.2.2 with h | ⟨h1, h2⟩
        · exact h
        · rcases hko with h | h
          · exact absurd h h1
          · exact absurd h h2
      · rw [Function.update_of_ne hab]
    exact .rdc hko hK (fun w hw => ih w (hw.trans hca) hF)
  | @wr μ a w k ha hm hcl _ ih =>
    intro b v hF
    have hpa : PO c hs (own μ a) := Or.inl ha
    have hab : a ≠ b := by rintro rfl; exact hF.1 hpa
    have hoa : own (Function.update μ b v) a = own μ a := (hF.perm hpa).1
    have hnb : ¬ PO c hs (own μ b) := hF.1
    have hbg : own μ b ≠ .gate := fun h => hnb (Or.inr h)
    -- `c`'s write does not move `b`'s owner.
    have hob : own (Function.update μ a w) b = own μ b := by
      by_contra hne; exact hnb (Or.inl (hm b hne).1)
    -- Words whose owner `c` may not read keep `μ`'s owner across `c`'s write.
    have hstay : ∀ x, ¬ PO c hs (own (Function.update μ a w) x) →
        own (Function.update μ a w) x = own μ x := by
      intro x hx
      by_contra hne; exact hx (Or.inl (hm x hne).2)
    -- The foreign write seen after `c`'s write.
    have hF' : Foreign own cls ko c hs (Function.update μ a w) b v := by
      refine ⟨by rw [hob]; exact hnb, fun x hx => ?_, ?_⟩
      swap
      · rw [Function.update_of_ne (Ne.symm hab)]; exact hF.2.2
      have hdec := hD (Function.update μ a w) b v x hx
      rw [hob] at hdec
      have hxo : own (Function.update μ a w) x = own μ b := by
        rcases hdec with h | h
        · exact h.symm
        · exact absurd h hbg
      have hn1 : ¬ PO c hs (own (Function.update μ a w) x) := by rw [hxo]; exact hnb
      refine ⟨hn1, fun hP => ?_⟩
      -- `own μ x` is not readable by `c`.
      have hμx : own μ x = own μ b := by rw [← hstay x hn1, hxo]
      -- after the foreign write alone, `x`'s owner is not readable either
      have hn2 : ¬ PO c hs (own (Function.update μ b v) x) := by
        by_cases he : own (Function.update μ b v) x = own μ x
        · rw [he, hμx]; exact hnb
        · exact (hF.2.1 x he).2
      rw [Function.update_comm hab] at hP
      by_cases he2 : own (Function.update (Function.update μ b v) a w) x =
          own (Function.update μ b v) x
      · rw [he2] at hP; exact hn2 hP
      · have hd2 := hD (Function.update μ b v) a w x he2
        rw [hoa] at hd2
        rcases hd2 with h | h
        · exact hn2 (by rw [← h]; exact hpa)
        · exact heldV_ne_gate ha h
    refine .wr ?_ ?_ ?_ ?_
    · rw [hoa]; exact ha
    · intro x hx
      have hd1 := hD (Function.update μ b v) a w x hx
      rw [hoa] at hd1
      have hx1 : own (Function.update μ b v) x = own μ a := by
        rcases hd1 with h | h
        · exact h.symm
        · exact absurd h (heldV_ne_gate ha)
      refine ⟨by rw [hx1]; exact ha, ?_⟩
      -- `x`'s owner under `μ`, then under `c`'s write, is held
      have hμx : own μ x = own μ a := by
        by_cases he : own (Function.update μ b v) x = own μ x
        · rw [← he, hx1]
        · exact absurd (by rw [hx1]; exact hpa) (hF.2.1 x he).2
      have hνx : HeldV c hs (own (Function.update μ a w) x) := by
        by_cases he : own (Function.update μ a w) x = own μ x
        · rw [he, hμx]; exact ha
        · exact (hm x he).2
      rw [← Function.update_comm hab]
      by_cases he : own (Function.update (Function.update μ a w) b v) x =
          own (Function.update μ a w) x
      · rw [he]; exact hνx
      · exact absurd (Or.inl hνx) (hF'.2.1 x he).1
    · rw [Function.update_of_ne hab]; exact hcl
    · rw [← Function.update_comm hab]; exact ih hF'

/-! ## The invariant -/

/-- Every local path in progress is in its glue, or in a body `Safe` from the
current memory with its current locks. -/
def SInv (s : Cfg A V C L) : Prop :=
  ∀ d p0 q W, s.ph d = .loc p0 q W →
    Glue s.cls s.ko d q ∨ Safe s.own s.cls s.ko d (fun l => s.lk l = some d) s.mem q

/-- **Premise** [W]: every program a core arms is glue up to its body. -/
def ArmGlue (s0 : Cfg A V C L) : Prop :=
  ∀ s, GReach s0 s → ∀ c p, s.ph c = .arm p → Glue s.cls s.ko c p

/-- **Premise** [W]: a body is `Safe` from the memory and locks when it starts
(per path, from `PathObl` and the glue's `Pre` [P]). -/
def BodyOK (s0 : Cfg A V C L) : Prop :=
  ∀ s, GReach s0 s → ∀ c p0 k W, s.ph c = .loc p0 (.start k) W →
    Safe s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem k

/-- **Premise** [W]: every ownership map of the execution satisfies `Deciders`. -/
def DecidersOK (s0 : Cfg A V C L) : Prop := ∀ s, GReach s0 s → Deciders s.own

theorem allowed_of_sinv {s : Cfg A V C L} (I : SInv s) (c : C) : Allowed s c := by
  cases hph : s.ph c with
  | idle => simp only [Allowed, hph]
  | arm p => simp only [Allowed, hph]
  | ser p => simp only [Allowed, hph]
  | loc p0 q W =>
    have hI := I c p0 q W hph
    cases q with
    | rd a k =>
      simp only [Allowed, hph]
      rcases hI with hg | hS
      · cases hg
      · cases hS with
        | rd hp _ => exact hp.imp_left held_of_heldV
    | wr a v k =>
      simp only [Allowed, hph]
      rcases hI with hg | hS
      · cases hg
      · cases hS with
        | wr ha hm hcl _ =>
          exact ⟨held_of_heldV ha,
            fun x hx => ⟨held_of_heldV (hm x hx).1, held_of_heldV (hm x hx).2⟩, hcl⟩
    | rdc a K k =>
      simp only [Allowed, hph]
      rcases hI with hg | hS
      · cases hg with
        | rdc hko hK _ => exact ⟨hko, hK⟩
      · cases hS with
        | rdc hko hK _ => exact ⟨hko, hK⟩
    | done => simp only [Allowed, hph]
    | rds a k => simp only [Allowed, hph]
    | lock l k => simp only [Allowed, hph]
    | start k => simp only [Allowed, hph]

/-- A core's lock view is unchanged when another core takes or releases locks. -/
theorem sinv_keep {s : Cfg A V C L} {d : C} {own' : (A → V) → A → Owner C L}
    {mem' : A → V} {lk' : L → Option C} (hown : own' = s.own) (hmem : mem' = s.mem)
    (hlk : ∀ l, lk' l = some d ↔ s.lk l = some d) {q : Prog A V L}
    {cls' : A → V → V} {ko' : A → ClsOwner C} (hcl : cls' = s.cls) (hko : ko' = s.ko)
    (h : Glue s.cls s.ko d q ∨ Safe s.own s.cls s.ko d (fun l => s.lk l = some d) s.mem q) :
    Glue cls' ko' d q ∨ Safe own' cls' ko' d (fun l => lk' l = some d) mem' q := by
  subst hown hmem hcl hko
  exact h.imp id (Safe.congr (fun l => (hlk l).symm))

theorem sinv_step {s0 s s' : Cfg A V C L} {c : C} (h0 : Init s0) (hr : GReach s0 s)
    (hA : ArmGlue s0) (hB : BodyOK s0) (hD : Deciders s.own) (I : SInv s)
    (hal : Allowed s c) (hst : Step s c s') : SInv s' := by
  intro d p0 q W hd
  cases hst with
  | arm p hc =>
    have hd' : Function.update s.ph c (.arm p) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
    · rw [Function.update_of_ne hdc] at hd'; exact I d p0 q W hd'
  | back hc _ =>
    have hd' : Function.update s.ph c .idle d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
    · rw [Function.update_of_ne hdc] at hd'; exact I d p0 q W hd'
  | @enter p hc _ =>
    have hd' : Function.update s.ph c (.loc p p ∅) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
      exact Or.inl (hA s hr d _ hc)
    · rw [Function.update_of_ne hdc] at hd'; exact I d p0 q W hd'
  | @rd p1 a k W1 hc =>
    have hd' : Function.update s.ph c (.loc p1 (k (s.mem a)) W1) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
      rcases I d _ _ _ hc with hg | hS
      · cases hg
      · cases hS with
        | rd _ hk => exact Or.inr hk
    · rw [Function.update_of_ne hdc] at hd'; exact I d p0 q W hd'
  | @rds p1 a k W1 hc =>
    have hd' : Function.update s.ph c (.loc p1 (k (s.mem a)) W1) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
      rcases I d _ _ _ hc with hg | hS
      · cases hg with
        | rds hk => exact Or.inl (hk _)
      · cases hS with
        | rds hk => exact Or.inr (hk _)
    · rw [Function.update_of_ne hdc] at hd'; exact I d p0 q W hd'
  | @rdc p1 a K k W1 hc =>
    have hd' : Function.update s.ph c (.loc p1 (k (s.mem a)) W1) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
      rcases I d _ _ _ hc with hg | hS
      · cases hg with
        | rdc _ _ hk => exact Or.inl (hk _)
      · cases hS with
        | rdc _ _ hk => exact Or.inr (hk _ rfl)
    · rw [Function.update_of_ne hdc] at hd'; exact I d p0 q W hd'
  | @start p1 k W1 hc =>
    have hd' : Function.update s.ph c (.loc p1 k W1) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
      exact Or.inr (hB s hr d _ _ _ hc)
    · rw [Function.update_of_ne hdc] at hd'; exact I d p0 q W hd'
  | @wr p1 a v k W1 hc =>
    have hd' : Function.update s.ph c (.loc p1 k (insert a W1)) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
      rcases I d _ _ _ hc with hg | hS
      · cases hg
      · cases hS with
        | wr _ _ _ hk => exact Or.inr hk
    · rw [Function.update_of_ne hdc] at hd'
      rcases I d p0 q W hd' with hg | hS
      · exact Or.inl hg
      · right
        simp only [Allowed, hc] at hal
        obtain ⟨hb, hmv, hcl⟩ := hal
        have hcd : c ≠ d := Ne.symm hdc
        refine Safe.foreign hD hS
          ⟨not_PO_of_held hcd hb, fun x hx =>
            ⟨not_PO_of_held hcd (hmv x hx).1, not_PO_of_held hcd (hmv x hx).2⟩, ?_⟩
        rcases hcl with h | h | h
        · exact Or.inl h
        · refine Or.inr ⟨?_, ?_⟩
          · rw [h]; intro e; cases e
          · rw [h]; intro e; exact hcd (ClsOwner.core.inj e)
        · refine Or.inr ⟨?_, ?_⟩
          · rw [h]; intro e; cases e
          · rw [h]; intro e; cases e
  | @lock p1 l k W1 b hc hb =>
    have hd' : Function.update s.ph c (.loc p1 (k b) W1) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
      rcases I d _ _ _ hc with hg | hS
      · cases hg with
        | lock hk => exact Or.inl (hk b)
      · cases hS
    · rw [Function.update_of_ne hdc] at hd'
      refine sinv_keep (s := s) (lk' := if b then Function.update s.lk l (some c) else s.lk)
        rfl rfl (fun l' => ?_) rfl rfl (I d p0 q W hd')
      cases b with
      | false => rw [if_neg (by decide)]
      | true =>
        rw [if_pos rfl]
        by_cases hl : l' = l
        · subst hl
          rw [Function.update_self, hb rfl]
          exact ⟨fun h => absurd (Option.some.inj h) (Ne.symm hdc), fun h => by cases h⟩
        · rw [Function.update_of_ne hl]
  | @leave p1 W1 hc =>
    have hd' : Function.update s.ph c .idle d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
    · rw [Function.update_of_ne hdc] at hd'
      refine sinv_keep (s := s) (lk' := release s.lk c) rfl rfl (fun l' => ?_) rfl rfl
        (I d p0 q W hd')
      show (if s.lk l' = some c then none else s.lk l') = some d ↔ s.lk l' = some d
      by_cases hl : s.lk l' = some c
      · rw [if_pos hl, hl]
        exact ⟨(fun h => by cases h), fun h => absurd (Option.some.inj h) (Ne.symm hdc)⟩
      · rw [if_neg hl]
  | take p hc _ =>
    have hd' : Function.update s.ph c (.ser p) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
    · rw [Function.update_of_ne hdc] at hd'; exact I d p0 q W hd'
  | scan e _ _ _ => exact I d p0 q W hd
  | drain _ _ _ => exact I d p0 q W hd
  | serial keep own' cls' ko' _ hg _ _ =>
    have hd' : Function.update s.ph c .idle d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
    · rw [Function.update_of_ne hdc] at hd'
      exact absurd (by rw [hd']; trivial) (no_overlap h0 hr hg d)

theorem sinv_greach {s0 s : Cfg A V C L} (h0 : Init s0) (hA : ArmGlue s0) (hB : BodyOK s0)
    (hD : DecidersOK s0) (h : GReach s0 s) : SInv s := by
  induction h with
  | refl => intro d p0 q W hd; exact absurd (by rw [hd]; trivial) (h0.2 d)
  | step hr hal hst ih => exact sinv_step h0 hr hA hB (hD _ hr) ih hal hst

/-- **The footprint premise from per-path safety.** -/
theorem footprintOK_of_safe {s0 : Cfg A V C L} (h0 : Init s0) (hA : ArmGlue s0)
    (hB : BodyOK s0) (hD : DecidersOK s0) : FootprintOK s0 :=
  fun _ hs c => allowed_of_sinv (sinv_greach h0 hA hB hD hs) c

/-- **Every execution is a serial one**, from per-path safety (`ArmGlue`,
`BodyOK`, `DecidersOK`, all [W]) instead of `FootprintOK`: in every reachable
state with no local path in progress, memory is what running the completed
entries one after another, in completion order, produces from the initial
memory. **In that serial order a speculative read may return any value**, not
the value memory held at that point: this theorem alone does not say each
entry's run is one of its real serial runs; that is the per-path refinement
obligation (P2 (2), `PathObl.lean`), which must hold for every value of those
reads. -/
theorem serializable_safe {s0 s : Cfg A V C L} (h0 : Init s0) (hA : ArmGlue s0)
    (hB : BodyOK s0) (hD : DecidersOK s0) (h : Reach s0 s) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_reach h0 (footprintOK_of_safe h0 hA hB hD) h hq

end

end Fl4Proofs.P2.Serial
