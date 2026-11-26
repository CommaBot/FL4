/-
# P2 (line mmuAD, gen 4): **run-relative insensitivity** — `SerialAD` with `ADIns` asked only along the run

`P2/SerialAD.lean` serializes the page walker's accessed / dirty writes (`ADWr`) given that every started body is
`ADIns G Q NP`: a property of the *whole* program tree. Gen 3 (`MmuADEpoch.sadIns_rd_sens`) showed that this is
false for every FL4 slot: the trees chase pointers read from memory, and on branches no real run takes (a
`CUR_THREAD` word pointing next to a paging entry) a read of a paging word decodes bits 5, 6. What `SerialAD`'s
proofs use is only the insensitivity *at the values the run reads*: `InvA.step` at `k (s.mem a)`, `safe_ad` at the
values of the memories other cores reach. This module states the obligation that way, modelled on
`SerialSafe.Safe`:

* `ADStep G Q NP own ko μ b v`: an `ADWr`-shaped write (a `G` word, not `NP`, `Q`-equivalent value, owners kept,
  class untracked), as any core sees it.
* **`FReachA`**: memories reached from `μ` by other cores' `Foreign` writes and by `ADStep`s.
* **`InsA G Q NP own cls ko c hs μ p`**: at every `FReachA`-reached memory `μ'`, a read of a `G` word `a` has the
  same continuation for every value `Q`-equivalent to `μ' a`, and the rest is `InsA` from `μ'` at the value `μ' a`;
  a store into a `G` word stores an `NP` value. No `lock` / `start` (bodies take no locks, as for `Safe`).
  `InsA.pre` / `InsA.reach` / `InsA.foreign` / `InsA.adstep` (stable by construction), `insA_congr` (lock view).
* `IInv s`: every in-progress local path is in its glue or `InsA` from the current memory with its locks;
  **`iinv_stepX`** (every core step keeps it, given that started bodies are `InsA`), `iinv_hw`, `iinv_ad`.
* **`InvR`** = `InvA` without its tree-level `ins` field: `InvR.step` (all 14 `Step` kinds, using `IInv` at the
  value read), `InvR.hw`, **`InvR.ad`**, `InvR.of_noLoc`.
* **`safe_adR`** / **`sinv_adR`**: `SInv` across an `ADWr`, from `InsA` (`SerialAD.freach_ad` reused).
* **`ARunR`** (core steps are `SafeStep`s whose started bodies are `InsA` at the start memory, `HwWr`, `ADWr`,
  `regate`), `aRunR_inv`, **`serializable_safeR`**: where an `ARunR` reaches a state with no local path in
  progress, memory is the serial run of the completed entries, each environment write logged at its time.
  `insA_of_adIns`: the tree-level `ADIns` of a body with no `lock` / `start` (`NoLk`) implies `InsA` at every
  memory.

No premise: everything here is proved. `SerialAD`'s statements are untouched (its `freach_ad`, `SimA`,
`SimA.mono`, `InvH.hist_perm`, `ADWr` are reused).
-/
import Fl4Proofs.P2.SerialAD

namespace Fl4Proofs.P2.Serial

noncomputable section

variable {A V C L : Type} [DecidableEq A] [DecidableEq C] [DecidableEq L]

/-! ## Reachability with environment writes, and the run-relative predicate -/

/-- An `ADWr`-shaped write of `b := v` from `μ`, as any core sees it. -/
def ADStep (G : A → Prop) (Q : V → V → Prop) (NP : V → Prop) (own : (A → V) → A → Owner C L)
    (ko : A → ClsOwner C) (μ : A → V) (b : A) (v : V) : Prop :=
  G b ∧ ¬ NP (μ b) ∧ Q (μ b) v ∧ (∀ m, own (Function.update m b v) = own m) ∧ ko b = .free

/-- **Memories reached from `μ`** by other cores' `Foreign` writes and environment `ADStep`s. -/
inductive FReachA (G : A → Prop) (Q : V → V → Prop) (NP : V → Prop) (own : (A → V) → A → Owner C L)
    (cls : A → V → V) (ko : A → ClsOwner C) (c : C) (hs : L → Prop) : (A → V) → (A → V) → Prop
  | refl (μ : A → V) : FReachA G Q NP own cls ko c hs μ μ
  | step {μ μ' : A → V} {b : A} {v : V} : Foreign own cls ko c hs μ b v →
      FReachA G Q NP own cls ko c hs (Function.update μ b v) μ' → FReachA G Q NP own cls ko c hs μ μ'
  | ad {μ μ' : A → V} {b : A} {v : V} : ADStep G Q NP own ko μ b v →
      FReachA G Q NP own cls ko c hs (Function.update μ b v) μ' → FReachA G Q NP own cls ko c hs μ μ'

/-- **Run-relative insensitivity** (module docstring). -/
inductive InsA (G : A → Prop) (Q : V → V → Prop) (NP : V → Prop) (own : (A → V) → A → Owner C L)
    (cls : A → V → V) (ko : A → ClsOwner C) (c : C) (hs : L → Prop) : (A → V) → Prog A V L → Prop
  | done {μ : A → V} : InsA G Q NP own cls ko c hs μ .done
  | rd {μ : A → V} {a : A} {k : V → Prog A V L} :
      (G a → ∀ μ', FReachA G Q NP own cls ko c hs μ μ' → ∀ u, Q u (μ' a) → k u = k (μ' a)) →
      (∀ μ', FReachA G Q NP own cls ko c hs μ μ' → InsA G Q NP own cls ko c hs μ' (k (μ' a))) →
      InsA G Q NP own cls ko c hs μ (.rd a k)
  | rds {μ : A → V} {a : A} {k : V → Prog A V L} :
      (G a → ∀ μ', FReachA G Q NP own cls ko c hs μ μ' → ∀ u, Q u (μ' a) → k u = k (μ' a)) →
      (∀ μ', FReachA G Q NP own cls ko c hs μ μ' → InsA G Q NP own cls ko c hs μ' (k (μ' a))) →
      InsA G Q NP own cls ko c hs μ (.rds a k)
  | rdc {μ : A → V} {a : A} {K : V → V → Prop} {k : V → Prog A V L} :
      (G a → ∀ μ', FReachA G Q NP own cls ko c hs μ μ' → ∀ u, Q u (μ' a) → k u = k (μ' a)) →
      (∀ μ', FReachA G Q NP own cls ko c hs μ μ' → InsA G Q NP own cls ko c hs μ' (k (μ' a))) →
      InsA G Q NP own cls ko c hs μ (.rdc a K k)
  | wr {μ : A → V} {a : A} {v : V} {k : Prog A V L} : (G a → NP v) →
      (∀ μ', FReachA G Q NP own cls ko c hs μ μ' →
        InsA G Q NP own cls ko c hs (Function.update μ' a v) k) →
      InsA G Q NP own cls ko c hs μ (.wr a v k)

section ins
variable {G : A → Prop} {Q : V → V → Prop} {NP : V → Prop} {own : (A → V) → A → Owner C L}
  {cls : A → V → V} {ko : A → ClsOwner C} {c : C} {hs : L → Prop}

theorem FReachA.trans {μ μ1 μ2 : A → V} (h1 : FReachA G Q NP own cls ko c hs μ μ1)
    (h2 : FReachA G Q NP own cls ko c hs μ1 μ2) : FReachA G Q NP own cls ko c hs μ μ2 := by
  induction h1 with
  | refl => exact h2
  | step hF _ ih => exact .step hF (ih h2)
  | ad hA _ ih => exact .ad hA (ih h2)

theorem FReachA.of_freach {μ μ' : A → V} (h : FReach own cls ko c hs μ μ') :
    FReachA G Q NP own cls ko c hs μ μ' := by
  induction h with
  | refl => exact .refl _
  | step hF _ ih => exact .step hF ih

/-- `InsA` passes to a memory whose reached memories are reached from the old one. -/
theorem InsA.pre {μ μ1 : A → V} {p : Prog A V L}
    (h : ∀ μ', FReachA G Q NP own cls ko c hs μ1 μ' → FReachA G Q NP own cls ko c hs μ μ')
    (hI : InsA G Q NP own cls ko c hs μ p) : InsA G Q NP own cls ko c hs μ1 p := by
  cases hI with
  | done => exact .done
  | rd h1 h2 => exact .rd (fun hg μ' hR => h1 hg μ' (h μ' hR)) (fun μ' hR => h2 μ' (h μ' hR))
  | rds h1 h2 => exact .rds (fun hg μ' hR => h1 hg μ' (h μ' hR)) (fun μ' hR => h2 μ' (h μ' hR))
  | rdc h1 h2 => exact .rdc (fun hg μ' hR => h1 hg μ' (h μ' hR)) (fun μ' hR => h2 μ' (h μ' hR))
  | wr h1 h2 => exact .wr h1 (fun μ' hR => h2 μ' (h μ' hR))

theorem InsA.reach {μ μ1 : A → V} {p : Prog A V L} (hR : FReachA G Q NP own cls ko c hs μ μ1)
    (hI : InsA G Q NP own cls ko c hs μ p) : InsA G Q NP own cls ko c hs μ1 p :=
  hI.pre fun _ h => hR.trans h

theorem InsA.foreign {μ : A → V} {b : A} {v : V} {p : Prog A V L} (hF : Foreign own cls ko c hs μ b v)
    (hI : InsA G Q NP own cls ko c hs μ p) : InsA G Q NP own cls ko c hs (Function.update μ b v) p :=
  hI.pre fun _ h => .step hF h

theorem InsA.adstep {μ : A → V} {b : A} {v : V} {p : Prog A V L} (hA : ADStep G Q NP own ko μ b v)
    (hI : InsA G Q NP own cls ko c hs μ p) : InsA G Q NP own cls ko c hs (Function.update μ b v) p :=
  hI.pre fun _ h => .ad hA h

theorem insA_congr {hs' : L → Prop} (h : ∀ l, hs l ↔ hs' l) {μ : A → V} {p : Prog A V L}
    (hI : InsA G Q NP own cls ko c hs μ p) : InsA G Q NP own cls ko c hs' μ p := by
  have e : hs = hs' := funext fun l => propext (h l)
  subst e; exact hI

/-- The value read at the current memory: the reflexive instance of the read clause. -/
theorem InsA.rd_ins {μ : A → V} {a : A} {k : V → Prog A V L}
    (hI : InsA G Q NP own cls ko c hs μ (.rd a k)) :
    (G a → ∀ u, Q u (μ a) → k u = k (μ a)) ∧ InsA G Q NP own cls ko c hs μ (k (μ a)) := by
  cases hI with
  | rd h1 h2 => exact ⟨fun hg => h1 hg μ (.refl _), h2 μ (.refl _)⟩

end ins

/-! ## The per-path invariant -/

/-- Every in-progress local path is in its glue or run-relatively insensitive. -/
def IInv (G : A → Prop) (Q : V → V → Prop) (NP : V → Prop) (s : Cfg A V C L) : Prop :=
  ∀ d p0 q W, s.ph d = .loc p0 q W →
    Glue s.cls s.ko d q ∨ InsA G Q NP s.own s.cls s.ko d (fun l => s.lk l = some d) s.mem q

section iinv
variable {G : A → Prop} {Q : V → V → Prop} {NP : V → Prop}

theorem iinv_keep {s : Cfg A V C L} {d : C} {lk' : L → Option C}
    (hlk : ∀ l, lk' l = some d ↔ s.lk l = some d) {q : Prog A V L}
    (h : Glue s.cls s.ko d q ∨ InsA G Q NP s.own s.cls s.ko d (fun l => s.lk l = some d) s.mem q) :
    Glue s.cls s.ko d q ∨ InsA G Q NP s.own s.cls s.ko d (fun l => lk' l = some d) s.mem q :=
  h.imp id (insA_congr fun l => (hlk l).symm)

/-- **`IInv` is kept by every core step** (`SerialHw.sinv_stepX` with `InsA` for `Safe`). -/
theorem iinv_stepX {s s' : Cfg A V C L} {c : C} (hno : s.gate = .closed → NoLoc s)
    (hA : ArmInv s) (hB : ∀ p0 k W, s.ph c = .loc p0 (.start k) W →
      InsA G Q NP s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem k) (I : IInv G Q NP s)
    (hal : Allowed s c) (hst : Step s c s') : IInv G Q NP s' := by
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
      exact Or.inl ((hA d _ hc).glue _ _ _)
    · rw [Function.update_of_ne hdc] at hd'; exact I d p0 q W hd'
  | @rd p1 a k W1 hc =>
    have hd' : Function.update s.ph c (.loc p1 (k (s.mem a)) W1) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
      rcases I d _ _ _ hc with hg | hS
      · cases hg
      · cases hS with
        | rd _ h => exact Or.inr (h _ (.refl _))
    · rw [Function.update_of_ne hdc] at hd'; exact I d p0 q W hd'
  | @rds p1 a k W1 hc =>
    have hd' : Function.update s.ph c (.loc p1 (k (s.mem a)) W1) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
      rcases I d _ _ _ hc with hg | hS
      · cases hg with
        | rds hk => exact Or.inl (hk _)
      · cases hS with
        | rds _ h => exact Or.inr (h _ (.refl _))
    · rw [Function.update_of_ne hdc] at hd'; exact I d p0 q W hd'
  | @rdc p1 a K k W1 hc =>
    have hd' : Function.update s.ph c (.loc p1 (k (s.mem a)) W1) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
      rcases I d _ _ _ hc with hg | hS
      · cases hg with
        | rdc _ _ hk => exact Or.inl (hk _)
      · cases hS with
        | rdc _ h => exact Or.inr (h _ (.refl _))
    · rw [Function.update_of_ne hdc] at hd'; exact I d p0 q W hd'
  | @start p1 k W1 hc =>
    have hd' : Function.update s.ph c (.loc p1 k W1) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
      exact Or.inr (hB _ _ _ hc)
    · rw [Function.update_of_ne hdc] at hd'; exact I d p0 q W hd'
  | @wr p1 a v k W1 hc =>
    have hd' : Function.update s.ph c (.loc p1 k (insert a W1)) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
      rcases I d _ _ _ hc with hg | hS
      · cases hg
      · cases hS with
        | wr _ h => exact Or.inr (h _ (.refl _))
    · rw [Function.update_of_ne hdc] at hd'
      rcases I d p0 q W hd' with hg | hS
      · exact Or.inl hg
      · right
        simp only [Allowed, hc] at hal
        obtain ⟨hb, hmv, hcl⟩ := hal
        have hcd : c ≠ d := Ne.symm hdc
        have hF : Foreign s.own s.cls s.ko d (fun l => s.lk l = some d) s.mem a v := by
          refine ⟨not_PO_of_held hcd hb, fun x hx =>
            ⟨not_PO_of_held hcd (hmv x hx).1, not_PO_of_held hcd (hmv x hx).2⟩, ?_⟩
          rcases hcl with h | h | h
          · exact Or.inl h
          · refine Or.inr ⟨?_, ?_⟩
            · rw [h]; intro e; cases e
            · rw [h]; intro e; exact hcd (ClsOwner.core.inj e)
          · refine Or.inr ⟨?_, ?_⟩
            · rw [h]; intro e; cases e
            · rw [h]; intro e; cases e
        exact hS.foreign hF
  | @lock p1 l k W1 b hc hb =>
    have hd' : Function.update s.ph c (.loc p1 (k b) W1) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
      rcases I d _ _ _ hc with hg | hS
      · cases hg with
        | lock hk => exact Or.inl (hk b)
      · cases hS
    · rw [Function.update_of_ne hdc] at hd'
      refine iinv_keep (s := s) (lk' := if b then Function.update s.lk l (some c) else s.lk)
        (fun l' => ?_) (I d p0 q W hd')
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
      refine iinv_keep (s := s) (lk' := release s.lk c) (fun l' => ?_) (I d p0 q W hd')
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
      exact absurd (by rw [hd']; trivial) (hno hg d)

/-- **`IInv` is kept by a hardware write** (to every path it is `Foreign`, as in `sinv_hw`). -/
theorem iinv_hw {s : Cfg A V C L} (I : IInv G Q NP s) {a : A} {x : V} {l : L} (h : HwWr s a x l) :
    IInv G Q NP (hwCfg s a x) := by
  intro d p0 q W hd
  rcases I d p0 q W hd with hg | hS
  · exact Or.inl hg
  · right
    have hF : Foreign s.own s.cls s.ko d (fun l => s.lk l = some d) s.mem a x := by
      refine ⟨?_, fun y hy => absurd (by rw [h.keep]) hy, ?_⟩
      · rw [h.own]; rintro (hl | hl)
        · change s.lk l = some d at hl; rw [h.free] at hl; cases hl
        · cases hl
      · right; rw [h.ko]; exact ⟨(fun e => by cases e), (fun e => by cases e)⟩
    exact hS.foreign hF

theorem ADWr.adStep {s : Cfg A V C L} {x : A} {y : V} (h : ADWr G Q NP s x y) :
    ADStep G Q NP s.own s.ko s.mem x y :=
  ⟨h.g, h.np, h.q, h.keep, h.ko⟩

/-- **`IInv` is kept by an `ADWr`**: it is an `ADStep` of every path's reachability. -/
theorem iinv_ad {s : Cfg A V C L} (I : IInv G Q NP s) {x : A} {y : V} (h : ADWr G Q NP s x y) :
    IInv G Q NP (hwCfg s x y) := by
  intro d p0 q W hd
  exact (I d p0 q W hd).imp id fun hS => hS.adstep h.adStep

end iinv

/-! ## The serialization invariant without the tree-level field -/

/-- `SerialAD.InvA` without `ins` (the insensitivity is `IInv`, carried beside it). -/
structure InvR (G : A → Prop) (Q : V → V → Prop) (NP : V → Prop) (m0 : A → V) (s : Cfg A V C L)
    (H : A → V) : Prop where
  inv : InvH m0 s H
  sim : ∀ d p0 p W, s.ph d = .loc p0 p W → SimA G Q s H d p0 p W
  np : ∀ d p0 p W, s.ph d = .loc p0 p W → ∀ x ∈ W, G x → NP (s.mem x)

section invr
variable {G : A → Prop} {Q : V → V → Prop} {NP : V → Prop}

theorem InvR.locstep {m0 : A → V} {s s' : Cfg A V C L} {H : A → V} {c : C} {p0 p p' : Prog A V L}
    {W W' : Set A} (I : InvR G Q NP m0 s H) (I' : InvH m0 s' H)
    (hc : s.ph c = .loc p0 p W) (hph : s'.ph = Function.update s.ph c (.loc p0 p' W'))
    (hperm : ∀ d, d ≠ c → ∀ x, Perm s d x → Perm s' d x)
    (hmemd : ∀ d, d ≠ c → ∀ q0 q U, s.ph d = .loc q0 q U → ∀ x ∈ U, s'.mem x = s.mem x)
    (hko : s'.ko = s.ko) (hcl : s'.cls = s.cls)
    (hsim : SimA G Q s' H c p0 p' W')
    (hnp : ∀ x ∈ W', G x → NP (s'.mem x)) : InvR G Q NP m0 s' H where
  inv := I'
  sim d q0 q U hd := by
    rw [hph] at hd
    rcases upd_loc hd with ⟨rfl, he⟩ | ⟨hdc, hd⟩
    · cases he; exact hsim
    · exact (I.sim d q0 q U hd).mono (hperm d hdc) (fun _ _ => rfl) (hmemd d hdc q0 q U hd) hko hcl
        (fun _ _ => rfl)
  np d q0 q U hd x hx hg := by
    rw [hph] at hd
    rcases upd_loc hd with ⟨rfl, he⟩ | ⟨hdc, hd⟩
    · cases he; exact hnp x hx hg
    · rw [hmemd d hdc q0 q U hd x hx]; exact I.np d q0 q U hd x hx hg

theorem InvR.frame {m0 : A → V} {s s' : Cfg A V C L} {H : A → V} (I : InvR G Q NP m0 s H)
    (I' : InvH m0 s' H) (hmem : s'.mem = s.mem) (hlk : s'.lk = s.lk) (hown : s'.own = s.own)
    (hko : s'.ko = s.ko) (hcl : s'.cls = s.cls)
    (hl : ∀ d q0 q U, s'.ph d = .loc q0 q U → s.ph d = .loc q0 q U) : InvR G Q NP m0 s' H where
  inv := I'
  sim d q0 q U hd := (I.sim d q0 q U (hl d q0 q U hd)).mono
    (fun x h => by unfold Perm; rw [hlk, hmem, hown]; exact h) (fun _ _ => rfl)
    (fun x _ => by rw [hmem]) hko hcl (fun _ _ => rfl)
  np d q0 q U hd x hx hg := by rw [hmem]; exact I.np d q0 q U (hl d q0 q U hd) x hx hg

theorem InvR.of_noLoc {G' : A → Prop} {m0 : A → V} {s : Cfg A V C L} {H : A → V} (I : InvH m0 s H)
    (hq : NoLoc s) : InvR G' Q NP m0 s H where
  inv := I
  sim d _ _ _ hd := absurd (by rw [hd]; trivial) (hq d)
  np d _ _ _ hd := absurd (by rw [hd]; trivial) (hq d)

theorem InvR.regate (G' : A → Prop) {m0 : A → V} {s : Cfg A V C L} {H : A → V} (I : InvR G Q NP m0 s H)
    (hg : s.gate = .closed) : InvR G' Q NP m0 s H :=
  InvR.of_noLoc I.inv (I.inv.clo hg)

/-- **Every core step keeps `InvR`**, the insensitivity used only at the value read (`IInv`). -/
theorem InvR.step {m0 : A → V} {s s' : Cfg A V C L} {H : A → V} {c : C} (I : InvR G Q NP m0 s H)
    (J : IInv G Q NP s) (hal : Allowed s c) (hst : Step s c s') :
    ∃ H', InvR G Q NP m0 s' H' := by
  cases hst with
  | arm p hc =>
    have hc' : ¬ (s.ph c).IsLoc := by rw [hc]; exact Phase.idle_not_loc
    exact ⟨H, I.frame (inv_phase I.inv (Phase.arm_not_loc p) hc') rfl rfl rfl rfl rfl
      (fun d q0 q U h => (upd_nonloc (Phase.arm_not_loc p) hc' d q0 q U).mp h)⟩
  | back hc _ =>
    have hc' : ¬ (s.ph c).IsLoc := by rw [hc]; exact Phase.arm_not_loc _
    exact ⟨H, I.frame (inv_phase I.inv Phase.idle_not_loc hc') rfl rfl rfl rfl rfl
      (fun d q0 q U h => (upd_nonloc Phase.idle_not_loc hc' d q0 q U).mp h)⟩
  | @enter p hc hg =>
    refine ⟨H, inv_enter I.inv hc hg, ?_, ?_⟩
    · intro d q0 q U hd
      rcases upd_loc hd with ⟨rfl, he⟩ | ⟨hdc, hd⟩
      · cases he
        intro n n' _ _ _ hr
        rw [mix_empty] at hr; exact hr
      · exact (I.sim d q0 q U hd).mono (fun _ h => h) (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl
          (fun _ _ => rfl)
    · intro d q0 q U hd x hx hg
      rcases upd_loc hd with ⟨rfl, he⟩ | ⟨_, hd⟩
      · cases he; exact absurd hx (Set.notMem_empty x)
      · exact I.np d q0 q U hd x hx hg
  | @rd p0 a k W hc =>
    simp only [Allowed, hc] at hal
    refine ⟨H, I.locstep (inv_rd I.inv hc hal) hc rfl (fun _ _ _ h => h) (fun _ _ _ _ _ _ _ _ => rfl)
      rfl rfl ?_ (fun x hx hg => I.np c p0 _ W hc x hx hg)⟩
    intro n n' hG hN hcn hr
    refine I.sim c p0 _ W hc n n' hG hN hcn (Run.rd ?_)
    have hval : k (mix W s.mem n a) = k (s.mem a) := by
      by_cases haW : a ∈ W
      · rw [mix_mem haW]
      · rw [mix_nmem haW]
        have hHa := I.inv.hist_perm hc hal haW
        by_cases hg : G a
        · have hq := hG a hal hg
          rw [hHa] at hq
          rcases J c p0 _ W hc with hgl | hAD
          · cases hgl
          · exact (hAD.rd_ins).1 hg _ hq
        · rw [hN a hal hg, hHa]
    rw [hval]; exact hr
  | @rds p0 a k W hc =>
    exact ⟨H, I.locstep (inv_rds I.inv hc) hc rfl (fun _ _ _ h => h) (fun _ _ _ _ _ _ _ _ => rfl)
      rfl rfl (fun n n' hG hN hcn hr => I.sim c p0 _ W hc n n' hG hN hcn (Run.rds _ hr))
      (fun x hx hg => I.np c p0 _ W hc x hx hg)⟩
  | @rdc p0 a K k W hc =>
    simp only [Allowed, hc] at hal
    obtain ⟨hko, hK⟩ := hal
    have hcl : ∀ n : A → V, (∀ x, (s.ko x = .gate ∨ s.ko x = .core c) →
        s.cls x (n x) = s.cls x (H x)) → s.cls a (mix W s.mem n a) = s.cls a (s.mem a) := by
      intro n hn
      by_cases haW : a ∈ W
      · rw [mix_mem haW]
      · rw [mix_nmem haW, hn a hko]
        rcases I.inv.clsinv a with h | ⟨e, q0, q, U, he, hx, hk⟩
        · exact h.symm
        · exfalso
          rcases hko with hg | hco
          · rcases hk with h | h <;> rw [hg] at h <;> cases h
          · rcases hk with h | h
            · rw [hco] at h
              obtain rfl : c = e := ClsOwner.core.inj h
              rw [hc] at he; cases he; exact haW hx
            · rw [hco] at h; cases h
    exact ⟨H, I.locstep (inv_rdc I.inv hc hko hK) hc rfl (fun _ _ _ h => h)
      (fun _ _ _ _ _ _ _ _ => rfl) rfl rfl
      (fun n n' hG hN hcn hr => I.sim c p0 _ W hc n n' hG hN hcn (Run.rdc _ (hK _ _ (hcl n hcn)) hr))
      (fun x hx hg => I.np c p0 _ W hc x hx hg)⟩
  | @start p0 k W hc =>
    exact ⟨H, I.locstep (inv_start I.inv hc) hc rfl (fun _ _ _ h => h) (fun _ _ _ _ _ _ _ _ => rfl)
      rfl rfl (fun n n' hG hN hcn hr => I.sim c p0 _ W hc n n' hG hN hcn (Run.start hr))
      (fun x hx hg => I.np c p0 _ W hc x hx hg)⟩
  | @lock p0 l k W b hc hb =>
    exact ⟨H, I.locstep (inv_lock I.inv hc b hb) hc rfl (fun _ _ _ h => Or.imp (held_lock hb) id h)
      (fun _ _ _ _ _ _ _ _ => rfl) rfl rfl
      (fun n n' hG hN hcn hr => I.sim c p0 _ W hc n n'
        (fun x hx hg => hG x (Or.imp (held_lock hb) id hx) hg)
        (fun x hx hg => hN x (Or.imp (held_lock hb) id hx) hg) hcn (Run.lock b hr))
      (fun x hx hg => I.np c p0 _ W hc x hx hg)⟩
  | @wr p0 a v k W hc =>
    simp only [Allowed, hc] at hal
    obtain ⟨ha, hmv, hcls⟩ := hal
    have hsame : ∀ d, d ≠ c → ∀ x, (Held s.lk d (s.own s.mem x) ∨ s.own s.mem x = .gate) →
        s.own (Function.update s.mem a v) x = s.own s.mem x := by
      intro d hdc x h
      by_contra hne
      exact held_disj (Ne.symm hdc) (hmv x hne).1 h
    have hnpv : G a → NP v := by
      rcases J c p0 _ W hc with hgl | hAD
      · cases hgl
      · cases hAD with
        | wr h1 _ => exact h1
    refine ⟨H, I.locstep (inv_wr I.inv hc ha hmv hcls) hc rfl ?_ ?_ rfl rfl ?_ ?_⟩
    · intro d hdc x h
      show Held s.lk d (s.own (Function.update s.mem a v) x) ∨
        s.own (Function.update s.mem a v) x = .gate
      rw [hsame d hdc x h]; exact h
    · intro d hdc q0 q U hd x hx
      have hxa : x ≠ a := by
        rintro rfl
        exact held_disj (Ne.symm hdc) ha (Or.inl ((I.inv.loc d q0 q U hd).held x hx))
      exact Function.update_of_ne hxa _ _
    · intro n n' hG hN hcn hr
      have hp : ∀ x, Perm s c x →
          Held s.lk c (s.own (Function.update s.mem a v) x) ∨
            s.own (Function.update s.mem a v) x = .gate := by
        intro x hx
        by_cases he : s.own (Function.update s.mem a v) x = s.own s.mem x
        · rw [he]; exact hx
        · exact Or.inl (hmv x he).2
      exact I.sim c p0 _ W hc n n' (fun x hx hg => hG x (hp x hx) hg) (fun x hx hg => hN x (hp x hx) hg)
        hcn (Run.wr (by rw [mix_upd]; exact hr))
    · intro x hx hg
      show NP (Function.update s.mem a v x)
      by_cases hxa : x = a
      · subst hxa; rw [Function.update_self]; exact hnpv hg
      · rw [Function.update_of_ne hxa]
        exact I.np c p0 _ W hc x ((Set.mem_insert_iff.mp hx).resolve_left hxa) hg
  | @leave p0 W hc =>
    have Ic := I.inv.loc c p0 _ W hc
    refine ⟨_, inv_leave I.inv hc, ?_, ?_⟩
    · intro d q0 q U hd
      rcases upd_loc hd with ⟨_, he⟩ | ⟨hdc, hd⟩
      · cases he
      · refine (I.sim d q0 q U hd).mono (fun x h => Or.imp (held_release hdc) id h)
          (fun x hp => mix_nmem (fun hxW => held_disj (Ne.symm hdc) (Ic.held x hxW) hp))
          (fun _ _ => rfl) rfl rfl (fun x hx => ?_)
        by_cases hxW : x ∈ W
        · rw [mix_mem hxW]
          rcases I.inv.clsinv x with h | ⟨e, q0', q', U', he, hxU, hk⟩
          · exact h
          · exfalso
            have hec : e = c := by
              by_contra hne
              exact held_disj hne ((I.inv.loc e q0' q' U' he).held x hxU) (Or.inl (Ic.held x hxW))
            subst hec
            rcases hx with h1 | h1 <;> rcases hk with h2 | h2 <;> rw [h1] at h2 <;>
              first | exact hdc (ClsOwner.core.inj h2) | exact hdc (ClsOwner.core.inj h2).symm | cases h2
        · rw [mix_nmem hxW]
    · intro d q0 q U hd x hx hg
      rcases upd_loc hd with ⟨_, he⟩ | ⟨_, hd⟩
      · cases he
      · exact I.np d q0 q U hd x hx hg
  | take p hc _ =>
    have hX : ¬ (Phase.ser p : Phase A V L).IsLoc := Phase.ser_not_loc p
    have hc' : ¬ (s.ph c).IsLoc := by rw [hc]; exact Phase.idle_not_loc
    exact ⟨H, I.frame (inv_take I.inv p hc) rfl rfl rfl rfl rfl
      (fun d q0 q U h => (upd_nonloc hX hc' d q0 q U).mp h)⟩
  | scan d _ _ hd => exact ⟨H, I.frame (inv_scan I.inv d hd) rfl rfl rfl rfl rfl (fun _ _ _ _ h => h)⟩
  | drain _ hg hall =>
    exact ⟨H, I.frame (inv_drain I.inv hg hall) rfl rfl rfl rfl rfl (fun _ _ _ _ h => h)⟩
  | serial keep own' cls' ko' _ hg _ hr =>
    have nl := I.inv.clo hg
    exact ⟨_, InvR.of_noLoc (inv_serial I.inv keep own' cls' ko' hg hr)
      (fun d hd => nl d (upd_isLoc Phase.idle_not_loc hd).2)⟩

/-- **`InvR` is kept by a `HwWr`** (the history taking the same write). -/
theorem InvR.hw {m0 : A → V} {s : Cfg A V C L} {H : A → V} (I : InvR G Q NP m0 s H) {a : A} {x : V}
    {l : L} (h : HwWr s a x l) : InvR G Q NP m0 (hwCfg s a x) (Function.update H a x) where
  inv := inv_hw I.inv h
  sim d p0 p W hd := by
    have L0 := I.inv.loc d p0 p W hd
    refine (I.sim d p0 p W hd).mono (s' := hwCfg s a x) (fun y hy => ?_) (fun y hy => ?_)
      (fun y hy => ?_) rfl rfl (fun y hy => ?_)
    · show Held s.lk d (s.own (Function.update s.mem a x) y) ∨ s.own (Function.update s.mem a x) y = .gate
      rw [h.keep]; exact hy
    · exact Function.update_of_ne (h.ne_of_perm hy) _ _
    · exact Function.update_of_ne (h.ne_of_held (L0.held y hy)) _ _
    · have hya : y ≠ a := by
        rintro rfl; rw [h.ko] at hy; rcases hy with hy | hy <;> cases hy
      rw [Function.update_of_ne hya]
  np d p0 p W hd y hy hg := by
    show NP (Function.update s.mem a x y)
    rw [Function.update_of_ne (h.ne_of_held ((I.inv.loc d p0 p W hd).held y hy))]
    exact I.np d p0 p W hd y hy hg

theorem InvR.ad_nmem {m0 : A → V} {s : Cfg A V C L} {H : A → V} (I : InvR G Q NP m0 s H) {x : A} {y : V}
    (h : ADWr G Q NP s x y) {d : C} {p0 p : Prog A V L} {W : Set A} (hd : s.ph d = .loc p0 p W) : x ∉ W :=
  fun hx => h.np (I.np d p0 p W hd x hx h.g)

/-- **`InvR` is kept by an `ADWr`**, the history taking the same write (`Q` an equivalence). -/
theorem InvR.ad (hQ : Equivalence Q) {m0 : A → V} {s : Cfg A V C L} {H : A → V} (I : InvR G Q NP m0 s H)
    {x : A} {y : V} (h : ADWr G Q NP s x y) :
    InvR G Q NP m0 (hwCfg s x y) (Function.update H x y) := by
  have hHx : H x = s.mem x :=
    (I.inv.agree x (fun d q0 q U hd hx => I.ad_nmem h hd hx)).symm
  have hperm : ∀ d z, Perm (hwCfg s x y) d z ↔ Perm s d z := by
    intro d z
    show (Held s.lk d (s.own (Function.update s.mem x y) z) ∨ s.own (Function.update s.mem x y) z = .gate) ↔ _
    rw [h.keep]; rfl
  have hmix : ∀ (W : Set A) (n : A → V), x ∉ W → mix W (Function.update s.mem x y) n = mix W s.mem n := by
    intro W n hxW
    funext z
    by_cases hz : z ∈ W
    · rw [mix_mem hz, mix_mem hz, Function.update_of_ne (fun e => hxW (by rw [← e]; exact hz))]
    · rw [mix_nmem hz, mix_nmem hz]
  have hcx : ∀ d, ¬ (s.ko x = .gate ∨ s.ko x = .core d) := by
    intro d hx; rw [h.ko] at hx; rcases hx with hx | hx <;> cases hx
  have key : ∀ d p0 p W, s.ph d = .loc p0 p W → ∀ n n' : A → V,
      (∀ z, Perm s d z → G z → Q (n z) (Function.update H x y z)) →
      (∀ z, Perm s d z → ¬ G z → n z = Function.update H x y z) →
      (∀ z, (s.ko z = .gate ∨ s.ko z = .core d) → s.cls z (n z) = s.cls z (Function.update H x y z)) →
      Run p (mix W (Function.update s.mem x y) n) n' → Run p0 n n' := by
    intro d p0 p W hd n n' hG hN hcn hr
    refine I.sim d p0 p W hd n n' (fun z hz hg => ?_) (fun z hz hg => ?_) (fun z hz => ?_)
      (by rw [← hmix W n (I.ad_nmem h hd)]; exact hr)
    · have h1 := hG z hz hg
      by_cases hzx : z = x
      · subst hzx
        rw [Function.update_self] at h1
        rw [hHx]; exact hQ.trans h1 (hQ.symm h.q)
      · rw [Function.update_of_ne hzx] at h1; exact h1
    · have hzx : z ≠ x := fun e => hg (e ▸ h.g)
      rw [hN z hz hg, Function.update_of_ne hzx]
    · have hzx : z ≠ x := fun e => hcx d (e ▸ hz)
      rw [hcn z hz, Function.update_of_ne hzx]
  refine ⟨⟨RunAll.snoc I.inv.hist (.wr (.done _)), I.inv.clo, I.inv.drn, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro z hz
    show Function.update s.mem x y z = Function.update H x y z
    by_cases hzx : z = x
    · subst hzx; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hzx, Function.update_of_ne hzx]; exact I.inv.agree z hz
  · intro d p0 p W hd
    have L0 := I.inv.loc d p0 p W hd
    refine ⟨fun z hz => ?_, fun n n' hn hcn hr => ?_⟩
    · show Held s.lk d (s.own (Function.update s.mem x y) z); rw [h.keep]; exact L0.held z hz
    · exact key d p0 p W hd n n' (fun z hz _ => by rw [hn z ((hperm d z).mpr hz)]; exact hQ.refl _)
        (fun z hz _ => hn z ((hperm d z).mpr hz)) hcn hr
  · intro z
    show s.cls z (Function.update s.mem x y z) = s.cls z (Function.update H x y z) ∨
      ∃ e p0 p W, s.ph e = .loc p0 p W ∧ z ∈ W ∧ (s.ko z = .core e ∨ s.ko z = .free)
    by_cases hzx : z = x
    · subst hzx; left; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hzx, Function.update_of_ne hzx]; exact I.inv.clsinv z
  · intro d p0 p W hd n n' hG hN hcn hr
    exact key d p0 p W hd n n' (fun z hz hg => hG z ((hperm d z).mpr hz) hg)
      (fun z hz hg => hN z ((hperm d z).mpr hz) hg) hcn hr
  · intro d p0 p W hd z hz hg
    show NP (Function.update s.mem x y z)
    rw [Function.update_of_ne (fun e => I.ad_nmem h hd (by rw [← e]; exact hz))]
    exact I.np d p0 p W hd z hz hg

end invr

/-! ## `Safe` across an environment write, from run-relative insensitivity -/

section safe
variable {G : A → Prop} {Q : V → V → Prop} {NP : V → Prop}
variable {own : (A → V) → A → Owner C L} {cls : A → V → V} {ko : A → ClsOwner C} {d : C} {hs : L → Prop}

/-- **`Safe` transfers across the write** for a run-relatively insensitive body that may read the word
(`SerialAD.safe_ad` with `InsA` for `ADIns`). -/
theorem safe_adR (hQs : ∀ u w, Q u w → Q w u) {x : A} {y : V} (hGx : G x)
    (hkeep : ∀ m, own (Function.update m x y) = own m) (hko : ko x = .free) {ν : A → V} {q : Prog A V L}
    (hS : Safe own cls ko d hs ν q) :
    InsA G Q NP own cls ko d hs ν q → PO d hs (own ν x) → Q (ν x) y →
      Safe own cls ko d hs (Function.update ν x y) q := by
  induction hS with
  | done => intro _ _ _; exact .done
  | @rd μ a k h1 _ ih =>
    intro hA hpo hq
    refine .rd (fun μ'' hR => ?_) (fun μ'' hR => ?_)
    · obtain ⟨ν', hR', rfl, _, _⟩ := freach_ad hkeep hR hpo
      rw [hkeep]; exact h1 ν' hR'
    · obtain ⟨ν', hR', rfl, hx, hpo'⟩ := freach_ad hkeep hR hpo
      obtain ⟨hA1, hA2⟩ := (hA.reach (.of_freach hR')).rd_ins
      have e : k (Function.update ν' x y a) = k (ν' a) := by
        by_cases hax : a = x
        · subst hax; rw [Function.update_self]
          exact hA1 hGx _ (hQs _ _ (by rw [hx]; exact hq))
        · rw [Function.update_of_ne hax]
      rw [e]; exact ih ν' hR' hA2 hpo' (by rw [hx]; exact hq)
  | @rds μ a k _ ih =>
    intro hA hpo hq
    refine .rds (fun μ'' hR => ?_)
    obtain ⟨ν', hR', rfl, hx, hpo'⟩ := freach_ad hkeep hR hpo
    have hA' := hA.reach (.of_freach hR')
    obtain ⟨hA1, hA2⟩ : (G a → ∀ u, Q u (ν' a) → k u = k (ν' a)) ∧
        InsA G Q NP own cls ko d hs ν' (k (ν' a)) := by
      cases hA' with
      | rds h1 h2 => exact ⟨fun hg => h1 hg ν' (.refl _), h2 ν' (.refl _)⟩
    have e : k (Function.update ν' x y a) = k (ν' a) := by
      by_cases hax : a = x
      · subst hax; rw [Function.update_self]
        exact hA1 hGx _ (hQs _ _ (by rw [hx]; exact hq))
      · rw [Function.update_of_ne hax]
    rw [e]; exact ih ν' hR' hA2 hpo' (by rw [hx]; exact hq)
  | @rdc μ a K k hko' hK _ ih =>
    intro hA hpo hq
    refine .rdc hko' hK (fun μ'' hR => ?_)
    obtain ⟨ν', hR', rfl, hx, hpo'⟩ := freach_ad hkeep hR hpo
    have hA' := hA.reach (.of_freach hR')
    obtain ⟨hA1, hA2⟩ : (G a → ∀ u, Q u (ν' a) → k u = k (ν' a)) ∧
        InsA G Q NP own cls ko d hs ν' (k (ν' a)) := by
      cases hA' with
      | rdc h1 h2 => exact ⟨fun hg => h1 hg ν' (.refl _), h2 ν' (.refl _)⟩
    have e : k (Function.update ν' x y a) = k (ν' a) := by
      by_cases hax : a = x
      · subst hax; rw [Function.update_self]
        exact hA1 hGx _ (hQs _ _ (by rw [hx]; exact hq))
      · rw [Function.update_of_ne hax]
    rw [e]; exact ih ν' hR' hA2 hpo' (by rw [hx]; exact hq)
  | @wr μ a v k h1 h2 h3 h4 ih =>
    intro hA hpo hq
    have hown : ∀ ν' : A → V,
        own (Function.update (Function.update ν' x y) a v) = own (Function.update ν' a v) := by
      intro ν'
      by_cases hax : a = x
      · subst hax; rw [Function.update_idem]
      · rw [Function.update_comm (Ne.symm hax) y v ν', hkeep]
    refine .wr (fun μ'' hR => ?_) (fun μ'' hR => ?_) (fun μ'' hR => ?_) (fun μ'' hR => ?_)
    · obtain ⟨ν', hR', rfl, _, _⟩ := freach_ad hkeep hR hpo
      rw [hkeep]; exact h1 ν' hR'
    · obtain ⟨ν', hR', rfl, _, _⟩ := freach_ad hkeep hR hpo
      intro z hz
      rw [hown, hkeep] at hz ⊢
      exact h2 ν' hR' z hz
    · obtain ⟨ν', hR', rfl, _, _⟩ := freach_ad hkeep hR hpo
      by_cases hax : a = x
      · subst hax; exact Or.inr (Or.inr hko)
      · rw [Function.update_of_ne hax]; exact h3 ν' hR'
    · obtain ⟨ν', hR', rfl, hx, hpo'⟩ := freach_ad hkeep hR hpo
      by_cases hax : a = x
      · subst hax; rw [Function.update_idem]; exact h4 ν' hR'
      · rw [Function.update_comm (Ne.symm hax) y v ν']
        have hpo1 : PO d hs (own (Function.update ν' a v) x) := by
          by_cases he : own (Function.update ν' a v) x = own ν' x
          · rw [he]; exact hpo'
          · exact Or.inl (h2 ν' hR' x he).2
        have hAk : InsA G Q NP own cls ko d hs (Function.update ν' a v) k := by
          cases hA.reach (.of_freach hR') with
          | wr _ h => exact h ν' (.refl _)
        refine ih ν' hR' hAk hpo1 ?_
        rw [Function.update_of_ne (Ne.symm hax), hx]; exact hq

end safe

/-- **`SInv` is kept by an `ADWr`** to whose readers it is run-relatively insensitive. -/
theorem sinv_adR {G : A → Prop} {Q : V → V → Prop} {NP : V → Prop} (hQs : ∀ u w, Q u w → Q w u)
    {s : Cfg A V C L} (I : SInv s) (J : IInv G Q NP s) {x : A} {y : V} (h : ADWr G Q NP s x y) :
    SInv (hwCfg s x y) := by
  intro d p0 q W hd
  rcases I d p0 q W hd with hg | hS
  · exact Or.inl hg
  · by_cases hpo : PO d (fun l => s.lk l = some d) (s.own s.mem x)
    · rcases J d p0 q W hd with hg | hA
      · exact Or.inl hg
      · exact Or.inr (safe_adR hQs h.g h.keep h.ko hS hA hpo h.q)
    · right
      have hF : Foreign s.own s.cls s.ko d (fun l => s.lk l = some d) s.mem x y := by
        refine ⟨hpo, fun z hz => absurd (by rw [h.keep]) hz, ?_⟩
        right; rw [h.ko]; exact ⟨(fun e => by cases e), (fun e => by cases e)⟩
      exact Safe.foreign hS hF

/-! ## Executions -/

/-- **Executions with environment writes the readers are run-relatively insensitive to**: as `SerialAD.ARun`,
a started body asked to be `InsA` from the memory and locks at its start. -/
inductive ARunR (Q : V → V → Prop) (NP : V → Prop) (s0 : Cfg A V C L) : Cfg A V C L → (A → Prop) → Prop
  | refl (G : A → Prop) : ARunR Q NP s0 s0 G
  | step {s s' : Cfg A V C L} {c : C} {G : A → Prop} :
      ARunR Q NP s0 s G → Step s c s' → SafeStep s c s' →
      (∀ p0 k W, s.ph c = .loc p0 (.start k) W →
        InsA G Q NP s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem k) → ARunR Q NP s0 s' G
  | hw {s : Cfg A V C L} {a : A} {x : V} {l : L} {G : A → Prop} :
      ARunR Q NP s0 s G → HwWr s a x l → ARunR Q NP s0 (hwCfg s a x) G
  | ad {s : Cfg A V C L} {x : A} {y : V} {G : A → Prop} :
      ARunR Q NP s0 s G → ADWr G Q NP s x y → ARunR Q NP s0 (hwCfg s x y) G
  | regate {s : Cfg A V C L} {G : A → Prop} (G' : A → Prop) :
      ARunR Q NP s0 s G → s.gate = .closed → ARunR Q NP s0 s G'

theorem aRunR_inv {Q : V → V → Prop} {NP : V → Prop} (hQ : Equivalence Q) {s0 s : Cfg A V C L}
    {G : A → Prop} (h0 : Init s0) (hA0 : ArmInv s0) (h : ARunR Q NP s0 s G) :
    (∃ H, InvR G Q NP s0.mem s H) ∧ IInv G Q NP s ∧ SInv s ∧ ArmInv s := by
  induction h with
  | refl G => exact ⟨⟨_, InvR.of_noLoc (inv_init h0) h0.2⟩,
      fun d p0 q W hd => absurd (by rw [hd]; trivial) (h0.2 d),
      fun d p0 q W hd => absurd (by rw [hd]; trivial) (h0.2 d), hA0⟩
  | @step s s' c G _ hst hok hB ih =>
    obtain ⟨⟨H, I⟩, J, hS, hA⟩ := ih
    have hal := allowed_of_sinv hS c
    exact ⟨I.step J hal hst, iinv_stepX I.inv.clo hA hB J hal hst,
      sinv_stepX I.inv.clo hA hok.start hS hal hst, armInv_step hA hst hok⟩
  | hw _ hh ih =>
    obtain ⟨⟨H, I⟩, J, hS, hA⟩ := ih
    exact ⟨⟨_, I.hw hh⟩, iinv_hw J hh, sinv_hw hS hh, hA⟩
  | ad _ hh ih =>
    obtain ⟨⟨H, I⟩, J, hS, hA⟩ := ih
    exact ⟨⟨_, I.ad hQ hh⟩, iinv_ad J hh, sinv_adR (fun u w h => hQ.symm h) hS J hh, hA⟩
  | regate G' _ hg ih =>
    obtain ⟨⟨H, I⟩, -, hS, hA⟩ := ih
    exact ⟨⟨H, I.regate G' hg⟩, fun d p0 q W hd => absurd (by rw [hd]; trivial) (I.inv.clo hg d), hS, hA⟩

/-- **Every `ARunR` is a serial one**: where it reaches a state with no local path in progress, memory is the
serial run of the completed entries, the environment writes logged as entries at their time. -/
theorem serializable_safeR {Q : V → V → Prop} {NP : V → Prop} (hQ : Equivalence Q) {s0 s : Cfg A V C L}
    {G : A → Prop} (h0 : Init s0) (hA0 : ArmInv s0) (h : ARunR Q NP s0 s G) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  obtain ⟨⟨H, I⟩, -, -, -⟩ := aRunR_inv hQ h0 hA0 h
  have : s.mem = H := funext fun x =>
    I.inv.agree x (fun d q0 q U hd => absurd (by rw [hd]; trivial) (hq d))
  rw [this]; exact I.inv.hist

/-! ## The tree-level predicate implies the run-relative one -/

/-- No `lock` and no `start` (the shape of a body). -/
inductive NoLk : Prog A V L → Prop
  | done : NoLk .done
  | rd {a : A} {k : V → Prog A V L} : (∀ v, NoLk (k v)) → NoLk (.rd a k)
  | rds {a : A} {k : V → Prog A V L} : (∀ v, NoLk (k v)) → NoLk (.rds a k)
  | rdc {a : A} {K : V → V → Prop} {k : V → Prog A V L} : (∀ v, NoLk (k v)) → NoLk (.rdc a K k)
  | wr {a : A} {v : V} {k : Prog A V L} : NoLk k → NoLk (.wr a v k)

theorem insA_of_adIns {G : A → Prop} {Q : V → V → Prop} {NP : V → Prop}
    {own : (A → V) → A → Owner C L} {cls : A → V → V} {ko : A → ClsOwner C} {c : C} {hs : L → Prop}
    {p : Prog A V L} (hN : NoLk p) (hA : ADIns G Q NP p) :
    ∀ μ, InsA G Q NP own cls ko c hs μ p := by
  induction hN with
  | done => intro _; exact .done
  | rd _ ih =>
    cases hA with
    | rd h1 h2 => intro μ; exact .rd (fun hg μ' _ u hu => h1 hg _ _ hu) (fun μ' _ => ih _ (h2 _) μ')
  | rds _ ih =>
    cases hA with
    | rds h1 h2 => intro μ; exact .rds (fun hg μ' _ u hu => h1 hg _ _ hu) (fun μ' _ => ih _ (h2 _) μ')
  | rdc _ ih =>
    cases hA with
    | rdc h1 h2 => intro μ; exact .rdc (fun hg μ' _ u hu => h1 hg _ _ hu) (fun μ' _ => ih _ (h2 _) μ')
  | wr _ ih =>
    cases hA with
    | wr h1 h2 => intro μ; exact .wr h1 (fun μ' _ => ih h2 _)

end

end Fl4Proofs.P2.Serial
