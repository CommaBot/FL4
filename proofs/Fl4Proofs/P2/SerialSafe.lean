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
inductive Safe (own : (A → V) → A → Owner C L) (c : C) (hs : L → Prop) :
    (A → V) → Prog A V L → Prop
  | done {μ : A → V} : Safe own c hs μ .done
  | rd {μ : A → V} {a : A} {k : V → Prog A V L} :
      PO c hs (own μ a) → Safe own c hs μ (k (μ a)) → Safe own c hs μ (.rd a k)
  | rds {μ : A → V} {a : A} {k : V → Prog A V L} :
      (∀ v, Safe own c hs μ (k v)) → Safe own c hs μ (.rds a k)
  | wr {μ : A → V} {a : A} {v : V} {k : Prog A V L} :
      HeldV c hs (own μ a) → MoveV own c hs μ (Function.update μ a v) →
      Safe own c hs (Function.update μ a v) k → Safe own c hs μ (.wr a v k)

/-- The fl4-sync glue: speculative reads and lock attempts, up to `start`. -/
inductive Glue : Prog A V L → Prop
  | done : Glue .done
  | rds {a : A} {k : V → Prog A V L} : (∀ v, Glue (k v)) → Glue (.rds a k)
  | lock {l : L} {k : Bool → Prog A V L} : (∀ b, Glue (k b)) → Glue (.lock l k)
  | start (k : Prog A V L) : Glue (.start k)

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

theorem Safe.congr {own : (A → V) → A → Owner C L} {c : C} {hs hs' : L → Prop}
    (h : ∀ l, hs l ↔ hs' l) {μ : A → V} {q : Prog A V L} (hS : Safe own c hs μ q) :
    Safe own c hs' μ q := by
  induction hS with
  | done => exact .done
  | rd hp _ ih => exact .rd (hp.imp_left (heldV_congr h _).mp) ih
  | rds _ ih => exact .rds ih
  | wr ha hm _ ih =>
    exact .wr ((heldV_congr h _).mp ha)
      (fun x hx => ⟨(heldV_congr h _).mp (hm x hx).1, (heldV_congr h _).mp (hm x hx).2⟩) ih

/-! ## Stability under another core's write -/

/-- What another core's write `b := v` looks like from core `c`: `b` is not a
word `c` may read, and every owner it changes is, before and after, one `c`
may not read. -/
def Foreign (own : (A → V) → A → Owner C L) (c : C) (hs : L → Prop) (μ : A → V) (b : A)
    (v : V) : Prop :=
  ¬ PO c hs (own μ b) ∧ ∀ x, own (Function.update μ b v) x ≠ own μ x →
    ¬ PO c hs (own μ x) ∧ ¬ PO c hs (own (Function.update μ b v) x)

theorem Foreign.perm {own : (A → V) → A → Owner C L} {c : C} {hs : L → Prop} {μ : A → V}
    {b : A} {v : V} (hF : Foreign own c hs μ b v) {x : A} (hx : PO c hs (own μ x)) :
    own (Function.update μ b v) x = own μ x ∧ Function.update μ b v x = μ x := by
  refine ⟨?_, ?_⟩
  · by_contra hne; exact (hF.2 x hne).1 hx
  · have hxb : x ≠ b := by rintro rfl; exact hF.1 hx
    exact Function.update_of_ne hxb _ _

/-- **Stability**: a body `Safe` from `μ` stays `Safe` after another core's
write that is `Foreign` to it. -/
theorem Safe.foreign {own : (A → V) → A → Owner C L} (hD : Deciders own) {c : C}
    {hs : L → Prop} {μ : A → V} {q : Prog A V L} (hS : Safe own c hs μ q) :
    ∀ {b : A} {v : V}, Foreign own c hs μ b v → Safe own c hs (Function.update μ b v) q := by
  induction hS with
  | done => intro _ _ _; exact .done
  | @rd μ a k hp _ ih =>
    intro b v hF
    obtain ⟨ho, hv⟩ := hF.perm hp
    refine .rd ?_ ?_
    · rw [ho]; exact hp
    · rw [hv]; exact ih hF
  | rds _ ih => intro b v hF; exact .rds (fun w => ih w hF)
  | @wr μ a w k ha hm _ ih =>
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
    have hF' : Foreign own c hs (Function.update μ a w) b v := by
      refine ⟨by rw [hob]; exact hnb, fun x hx => ?_⟩
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
        · exact (hF.2 x he).2
      rw [Function.update_comm hab] at hP
      by_cases he2 : own (Function.update (Function.update μ b v) a w) x =
          own (Function.update μ b v) x
      · rw [he2] at hP; exact hn2 hP
      · have hd2 := hD (Function.update μ b v) a w x he2
        rw [hoa] at hd2
        rcases hd2 with h | h
        · exact hn2 (by rw [← h]; exact hpa)
        · exact heldV_ne_gate ha h
    refine .wr ?_ ?_ ?_
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
        · exact absurd (by rw [hx1]; exact hpa) (hF.2 x he).2
      have hνx : HeldV c hs (own (Function.update μ a w) x) := by
        by_cases he : own (Function.update μ a w) x = own μ x
        · rw [he, hμx]; exact ha
        · exact (hm x he).2
      rw [← Function.update_comm hab]
      by_cases he : own (Function.update (Function.update μ a w) b v) x =
          own (Function.update μ a w) x
      · rw [he]; exact hνx
      · exact absurd (Or.inl hνx) (hF'.2 x he).1
    · rw [← Function.update_comm hab]; exact ih hF'

/-! ## The invariant -/

/-- Every local path in progress is in its glue, or in a body `Safe` from the
current memory with its current locks. -/
def SInv (s : Cfg A V C L) : Prop :=
  ∀ d p0 q W, s.ph d = .loc p0 q W →
    Glue q ∨ Safe s.own d (fun l => s.lk l = some d) s.mem q

/-- **Premise** [W]: every program a core arms is glue up to its body. -/
def ArmGlue (s0 : Cfg A V C L) : Prop :=
  ∀ s, GReach s0 s → ∀ c p, s.ph c = .arm p → Glue p

/-- **Premise** [W]: a body is `Safe` from the memory and locks when it starts
(per path, from `PathObl` and the glue's `Pre` [P]). -/
def BodyOK (s0 : Cfg A V C L) : Prop :=
  ∀ s, GReach s0 s → ∀ c p0 k W, s.ph c = .loc p0 (.start k) W →
    Safe s.own c (fun l => s.lk l = some c) s.mem k

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
        | wr ha hm _ =>
          exact ⟨held_of_heldV ha, fun x hx => ⟨held_of_heldV (hm x hx).1, held_of_heldV (hm x hx).2⟩⟩
    | done => simp only [Allowed, hph]
    | rds a k => simp only [Allowed, hph]
    | lock l k => simp only [Allowed, hph]
    | start k => simp only [Allowed, hph]

/-- A core's lock view is unchanged when another core takes or releases locks. -/
theorem sinv_keep {s : Cfg A V C L} {d : C} {own' : (A → V) → A → Owner C L}
    {mem' : A → V} {lk' : L → Option C} (hown : own' = s.own) (hmem : mem' = s.mem)
    (hlk : ∀ l, lk' l = some d ↔ s.lk l = some d) {q : Prog A V L}
    (h : Glue q ∨ Safe s.own d (fun l => s.lk l = some d) s.mem q) :
    Glue q ∨ Safe own' d (fun l => lk' l = some d) mem' q := by
  subst hown hmem
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
        | wr _ _ hk => exact Or.inr hk
    · rw [Function.update_of_ne hdc] at hd'
      rcases I d p0 q W hd' with hg | hS
      · exact Or.inl hg
      · right
        simp only [Allowed, hc] at hal
        obtain ⟨hb, hmv⟩ := hal
        have hcd : c ≠ d := Ne.symm hdc
        exact Safe.foreign hD hS
          ⟨not_PO_of_held hcd hb, fun x hx =>
            ⟨not_PO_of_held hcd (hmv x hx).1, not_PO_of_held hcd (hmv x hx).2⟩⟩
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
        rfl rfl (fun l' => ?_) (I d p0 q W hd')
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
      refine sinv_keep (s := s) (lk' := release s.lk c) rfl rfl (fun l' => ?_) (I d p0 q W hd')
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
  | serial keep own' _ hg _ _ =>
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
