/-
# P2 (line mmuAD, gen 8): bodies that **store a present value** into a walker-written word — `InsAP`

`SerialADR.InsA` asks every store into a `G` word (a paging word the walker writes) to store an `NP`
(not-present) value: then the walker never writes a word a local path has written, and every A/D write can be
logged at its time. PageMap (`pmPathsK`) stores a *present* leaf entry under the leaf's lock. Once that store
is in memory the walker may set A/D in it while PageMap still holds the lock (the lock is software; the walker
ignores it). Such a write can only be serialised *after* PageMap's entry (its log entry stores the value without
the bits), so it is deferred (`SerialADD`). That is sound only if the holder does not touch the word's value
again in a way that loses or depends on the bits:

* **`InsAP G Q NP own cls ko c hs D μ p`**: `InsA` with a set `D` of *done* words. A store of a non-`NP` value
  into a `G` word adds it to `D` (and needs `ko = .free`); a store into a `D` word is not allowed; reads are as in
  `InsA` (a read of a `D` word must be `Q`-insensitive, like every `G` read). `InsAP.pre` / `reach` / `foreign` /
  `adstep`, `insAP_congr`, **`insAP_of_insA`** (`InsA` is `InsAP` with `D = ∅`).
* `IInvP G Q NP D s`: every in-progress path is in its glue with `D d = ∅`, or `InsAP` with its own `D d`;
  **`iinvP_stepX`** (every core step, `D` updated at a present store and emptied at `leave`), `iinvP_hw`,
  `iinvP_ad`.
* **`safe_adP`** / **`sinv_adP`**: `SInv` across an `ADWr` (deferred or not), from `InsAP`.

No premise: everything here is proved.
-/
import Fl4Proofs.P2.SerialADR

namespace Fl4Proofs.P2.Serial

noncomputable section
open Classical

variable {A V C L : Type} [DecidableEq A] [DecidableEq C] [DecidableEq L]

/-- The done set after a store `a := v`: `a` joins it when it is a `G` word and `v` is not `NP`. -/
def dU (G : A → Prop) (NP : V → Prop) (D : Set A) (a : A) (v : V) : Set A :=
  {z | z ∈ D ∨ (z = a ∧ G a ∧ ¬ NP v)}

theorem dU_empty {G : A → Prop} {NP : V → Prop} {a : A} {v : V} (h : G a → NP v) :
    dU G NP (∅ : Set A) a v = ∅ := by
  ext z
  constructor
  · rintro (hz | ⟨_, hg, hn⟩)
    · exact hz
    · exact absurd (h hg) hn
  · intro hz; exact absurd hz (Set.notMem_empty _)

/-- **Run-relative insensitivity with present stores** (module docstring). -/
inductive InsAP (G : A → Prop) (Q : V → V → Prop) (NP : V → Prop) (own : (A → V) → A → Owner C L)
    (cls : A → V → V) (ko : A → ClsOwner C) (c : C) (hs : L → Prop) : Set A → (A → V) → Prog A V L → Prop
  | done {D : Set A} {μ : A → V} : InsAP G Q NP own cls ko c hs D μ .done
  | rd {D : Set A} {μ : A → V} {a : A} {k : V → Prog A V L} :
      (G a → ∀ μ', FReachA G Q NP own cls ko c hs μ μ' → ∀ u, Q u (μ' a) → k u = k (μ' a)) →
      (∀ μ', FReachA G Q NP own cls ko c hs μ μ' → InsAP G Q NP own cls ko c hs D μ' (k (μ' a))) →
      InsAP G Q NP own cls ko c hs D μ (.rd a k)
  | rds {D : Set A} {μ : A → V} {a : A} {k : V → Prog A V L} :
      (G a → ∀ μ', FReachA G Q NP own cls ko c hs μ μ' → ∀ u, Q u (μ' a) → k u = k (μ' a)) →
      (∀ μ', FReachA G Q NP own cls ko c hs μ μ' → InsAP G Q NP own cls ko c hs D μ' (k (μ' a))) →
      InsAP G Q NP own cls ko c hs D μ (.rds a k)
  | rdc {D : Set A} {μ : A → V} {a : A} {K : V → V → Prop} {k : V → Prog A V L} :
      (G a → ∀ μ', FReachA G Q NP own cls ko c hs μ μ' → ∀ u, Q u (μ' a) → k u = k (μ' a)) →
      (∀ μ', FReachA G Q NP own cls ko c hs μ μ' → InsAP G Q NP own cls ko c hs D μ' (k (μ' a))) →
      InsAP G Q NP own cls ko c hs D μ (.rdc a K k)
  | wr {D : Set A} {μ : A → V} {a : A} {v : V} {k : Prog A V L} : a ∉ D → (G a → ¬ NP v → ko a = .free) →
      (∀ μ', FReachA G Q NP own cls ko c hs μ μ' →
        InsAP G Q NP own cls ko c hs (dU G NP D a v) (Function.update μ' a v) k) →
      InsAP G Q NP own cls ko c hs D μ (.wr a v k)

section ins
variable {G : A → Prop} {Q : V → V → Prop} {NP : V → Prop} {own : (A → V) → A → Owner C L}
  {cls : A → V → V} {ko : A → ClsOwner C} {c : C} {hs : L → Prop}

theorem InsAP.pre {D : Set A} {μ μ1 : A → V} {p : Prog A V L}
    (h : ∀ μ', FReachA G Q NP own cls ko c hs μ1 μ' → FReachA G Q NP own cls ko c hs μ μ')
    (hI : InsAP G Q NP own cls ko c hs D μ p) : InsAP G Q NP own cls ko c hs D μ1 p := by
  cases hI with
  | done => exact .done
  | rd h1 h2 => exact .rd (fun hg μ' hR => h1 hg μ' (h μ' hR)) (fun μ' hR => h2 μ' (h μ' hR))
  | rds h1 h2 => exact .rds (fun hg μ' hR => h1 hg μ' (h μ' hR)) (fun μ' hR => h2 μ' (h μ' hR))
  | rdc h1 h2 => exact .rdc (fun hg μ' hR => h1 hg μ' (h μ' hR)) (fun μ' hR => h2 μ' (h μ' hR))
  | wr h0 h1 h2 => exact .wr h0 h1 (fun μ' hR => h2 μ' (h μ' hR))

theorem InsAP.reach {D : Set A} {μ μ1 : A → V} {p : Prog A V L} (hR : FReachA G Q NP own cls ko c hs μ μ1)
    (hI : InsAP G Q NP own cls ko c hs D μ p) : InsAP G Q NP own cls ko c hs D μ1 p :=
  hI.pre fun _ h => hR.trans h

theorem InsAP.foreign {D : Set A} {μ : A → V} {b : A} {v : V} {p : Prog A V L}
    (hF : Foreign own cls ko c hs μ b v)
    (hI : InsAP G Q NP own cls ko c hs D μ p) : InsAP G Q NP own cls ko c hs D (Function.update μ b v) p :=
  hI.pre fun _ h => .step hF h

theorem InsAP.adstep {D : Set A} {μ : A → V} {b : A} {v : V} {p : Prog A V L}
    (hA : ADStep G Q NP own ko μ b v)
    (hI : InsAP G Q NP own cls ko c hs D μ p) : InsAP G Q NP own cls ko c hs D (Function.update μ b v) p :=
  hI.pre fun _ h => .ad hA h

theorem insAP_congr {hs' : L → Prop} (h : ∀ l, hs l ↔ hs' l) {D : Set A} {μ : A → V} {p : Prog A V L}
    (hI : InsAP G Q NP own cls ko c hs D μ p) : InsAP G Q NP own cls ko c hs' D μ p := by
  have e : hs = hs' := funext fun l => propext (h l)
  subst e; exact hI

/-- **`InsA` is `InsAP` with nothing done** (its stores into `G` words are `NP`). -/
theorem insAP_of_insA {μ : A → V} {p : Prog A V L} (h : InsA G Q NP own cls ko c hs μ p) :
    InsAP G Q NP own cls ko c hs ∅ μ p := by
  induction h with
  | done => exact .done
  | rd h1 _ ih => exact .rd h1 ih
  | rds h1 _ ih => exact .rds h1 ih
  | rdc h1 _ ih => exact .rdc h1 ih
  | wr h1 _ ih =>
    refine .wr (Set.notMem_empty _) (fun hg hn => absurd (h1 hg) hn) (fun μ' hR => ?_)
    rw [dU_empty h1]; exact ih μ' hR

end ins

/-! ## The per-path invariant -/

/-- Every in-progress local path is in its glue (nothing done) or `InsAP` with its done set. -/
def IInvP (G : A → Prop) (Q : V → V → Prop) (NP : V → Prop) (D : C → Set A) (s : Cfg A V C L) : Prop :=
  ∀ d p0 q W, s.ph d = .loc p0 q W →
    (Glue s.cls s.ko d q ∧ D d = ∅) ∨
      InsAP G Q NP s.own s.cls s.ko d (fun l => s.lk l = some d) (D d) s.mem q

/-- The done sets after a step of core `c` from `s` to `s'`: `c`'s after a store, emptied at `leave`, others
(and every step that changes no phase) unchanged. -/
def DNext (G : A → Prop) (NP : V → Prop) (s s' : Cfg A V C L) (c : C) (D : C → Set A) : C → Set A :=
  fun d => if d = c ∧ s'.ph ≠ s.ph then
    (match s.ph c with
      | .loc _ (.wr a v _) _ => dU G NP (D c) a v
      | .loc _ .done _ => ∅
      | _ => D c)
    else D d

theorem dNext_ne {G : A → Prop} {NP : V → Prop} {s s' : Cfg A V C L} {c d : C} {D : C → Set A} (h : d ≠ c) :
    DNext G NP s s' c D d = D d := by
  simp only [DNext]; rw [if_neg (fun h' => h h'.1)]

theorem dNext_same {G : A → Prop} {NP : V → Prop} {s s' : Cfg A V C L} {c d : C} {D : C → Set A}
    (h : s'.ph = s.ph) : DNext G NP s s' c D d = D d := by
  simp only [DNext]; rw [if_neg (fun h' => h'.2 h)]

theorem dNext_self {G : A → Prop} {NP : V → Prop} {s s' : Cfg A V C L} {c : C} {D : C → Set A}
    (h : (match s.ph c with
      | .loc _ (.wr a v _) _ => dU G NP (D c) a v
      | .loc _ .done _ => ∅
      | _ => D c) = D c) : DNext G NP s s' c D c = D c := by
  simp only [DNext]
  by_cases h' : s'.ph ≠ s.ph
  · rw [if_pos (And.intro trivial h')]; exact h
  · rw [if_neg (fun h'' => h' h''.2)]

theorem dNext_wr {G : A → Prop} {NP : V → Prop} {s s' : Cfg A V C L} {c : C} {D : C → Set A}
    {p0 : Prog A V L} {a : A} {v : V} {k : Prog A V L} {W : Set A} (hc : s.ph c = .loc p0 (.wr a v k) W)
    (hne : s'.ph ≠ s.ph) : DNext G NP s s' c D c = dU G NP (D c) a v := by
  simp only [DNext]; rw [if_pos (And.intro trivial hne), hc]

theorem prog_wr_ne {a : A} {v : V} {k : Prog A V L} : Prog.wr a v k ≠ k := by
  intro h
  have := congrArg sizeOf h
  simp only [Prog.wr.sizeOf_spec] at this
  omega

section iinv
variable {G : A → Prop} {Q : V → V → Prop} {NP : V → Prop}

theorem insAP_keep {s : Cfg A V C L} {d : C} {lk' : L → Option C}
    (hlk : ∀ l, lk' l = some d ↔ s.lk l = some d) {D : Set A} {q : Prog A V L}
    (h : InsAP G Q NP s.own s.cls s.ko d (fun l => s.lk l = some d) D s.mem q) :
    InsAP G Q NP s.own s.cls s.ko d (fun l => lk' l = some d) D s.mem q :=
  insAP_congr (fun l => (hlk l).symm) h

/-- **`IInvP` is kept by every core step** (`iinv_stepX` with `InsAP`, the done sets by `DNext`). -/
theorem iinvP_stepX {s s' : Cfg A V C L} {c : C} {D : C → Set A} (hno : s.gate = .closed → NoLoc s)
    (hA : ArmInv s) (hB : ∀ p0 k W, s.ph c = .loc p0 (.start k) W →
      InsAP G Q NP s.own s.cls s.ko c (fun l => s.lk l = some c) (D c) s.mem k) (I : IInvP G Q NP D s)
    (hD0 : ∀ d, ¬ (s.ph d).IsLoc → D d = ∅)
    (hal : Allowed s c) (hst : Step s c s') : IInvP G Q NP (DNext G NP s s' c D) s' := by
  intro d p0 q W hd
  cases hst with
  | arm p hc =>
    have hd' : Function.update s.ph c (.arm p) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
    · rw [Function.update_of_ne hdc] at hd'; rw [dNext_ne hdc]; exact I d p0 q W hd'
  | back hc _ =>
    have hd' : Function.update s.ph c .idle d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
    · rw [Function.update_of_ne hdc] at hd'; rw [dNext_ne hdc]; exact I d p0 q W hd'
  | @enter p hc _ =>
    have hd' : Function.update s.ph c (.loc p p ∅) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
      left
      refine ⟨(hA d _ hc).glue _ _ _, ?_⟩
      rw [dNext_self (G := G) (NP := NP) (s := s) (c := d) (D := D) (by simp only [hc])]
      exact hD0 d (by rw [hc]; exact Phase.arm_not_loc _)
    · rw [Function.update_of_ne hdc] at hd'; rw [dNext_ne hdc]; exact I d p0 q W hd'
  | @rd p1 a k W1 hc =>
    have hd' : Function.update s.ph c (.loc p1 (k (s.mem a)) W1) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
      rw [dNext_self (G := G) (NP := NP) (s := s) (c := d) (D := D) (by simp only [hc])]
      rcases I d _ _ _ hc with ⟨hg, _⟩ | hS
      · cases hg
      · cases hS with
        | rd _ h => exact Or.inr (h _ (.refl _))
    · rw [Function.update_of_ne hdc] at hd'; rw [dNext_ne hdc]; exact I d p0 q W hd'
  | @rds p1 a k W1 hc =>
    have hd' : Function.update s.ph c (.loc p1 (k (s.mem a)) W1) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
      rw [dNext_self (G := G) (NP := NP) (s := s) (c := d) (D := D) (by simp only [hc])]
      rcases I d _ _ _ hc with ⟨hg, h0⟩ | hS
      · cases hg with
        | rds hk => exact Or.inl ⟨hk _, h0⟩
      · cases hS with
        | rds _ h => exact Or.inr (h _ (.refl _))
    · rw [Function.update_of_ne hdc] at hd'; rw [dNext_ne hdc]; exact I d p0 q W hd'
  | @rdc p1 a K k W1 hc =>
    have hd' : Function.update s.ph c (.loc p1 (k (s.mem a)) W1) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
      rw [dNext_self (G := G) (NP := NP) (s := s) (c := d) (D := D) (by simp only [hc])]
      rcases I d _ _ _ hc with ⟨hg, h0⟩ | hS
      · cases hg with
        | rdc _ _ hk => exact Or.inl ⟨hk _, h0⟩
      · cases hS with
        | rdc _ h => exact Or.inr (h _ (.refl _))
    · rw [Function.update_of_ne hdc] at hd'; rw [dNext_ne hdc]; exact I d p0 q W hd'
  | @start p1 k W1 hc =>
    have hd' : Function.update s.ph c (.loc p1 k W1) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
      rw [dNext_self (G := G) (NP := NP) (s := s) (c := d) (D := D) (by simp only [hc])]
      exact Or.inr (hB _ _ _ hc)
    · rw [Function.update_of_ne hdc] at hd'; rw [dNext_ne hdc]; exact I d p0 q W hd'
  | @wr p1 a v k W1 hc =>
    have hd' : Function.update s.ph c (.loc p1 k (insert a W1)) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
      have hne : Function.update s.ph d (.loc p0 q (insert a W1)) ≠ s.ph := by
        intro h
        have h1 := congrFun h d
        rw [Function.update_self, hc] at h1
        obtain ⟨-, h2, -⟩ := Phase.loc.inj h1
        exact prog_wr_ne h2.symm
      have e1 := dNext_wr (G := G) (NP := NP) (D := D) (s' := { s with mem := Function.update s.mem a v, ph := Function.update s.ph d (.loc p0 q (insert a W1)) }) hc hne
      rw [e1]
      rcases I d _ _ _ hc with ⟨hg, _⟩ | hS
      · cases hg
      · cases hS with
        | wr _ _ h => exact Or.inr (h _ (.refl _))
    · rw [Function.update_of_ne hdc] at hd'
      rw [dNext_ne hdc]
      rcases I d p0 q W hd' with ⟨hg, h0⟩ | hS
      · exact Or.inl ⟨hg, h0⟩
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
      rw [dNext_self (G := G) (NP := NP) (s := s) (c := d) (D := D) (by simp only [hc])]
      rcases I d _ _ _ hc with ⟨hg, h0⟩ | hS
      · cases hg with
        | lock hk => exact Or.inl ⟨hk b, h0⟩
      · cases hS
    · rw [Function.update_of_ne hdc] at hd'
      rw [dNext_ne hdc]
      have hlk : ∀ l', (if b then Function.update s.lk l (some c) else s.lk) l' = some d ↔
          s.lk l' = some d := by
        intro l'
        cases b with
        | false => rw [if_neg (by decide)]
        | true =>
          rw [if_pos rfl]
          by_cases hl : l' = l
          · subst hl
            rw [Function.update_self, hb rfl]
            exact ⟨fun h => absurd (Option.some.inj h) (Ne.symm hdc), fun h => by cases h⟩
          · rw [Function.update_of_ne hl]
      rcases I d p0 q W hd' with ⟨hg, h0⟩ | hS
      · exact Or.inl ⟨hg, h0⟩
      · exact Or.inr (insAP_keep (s := s) hlk hS)
  | @leave p1 W1 hc =>
    have hd' : Function.update s.ph c .idle d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
    · rw [Function.update_of_ne hdc] at hd'
      rw [dNext_ne hdc]
      have hlk : ∀ l', release s.lk c l' = some d ↔ s.lk l' = some d := by
        intro l'
        show (if s.lk l' = some c then none else s.lk l') = some d ↔ s.lk l' = some d
        by_cases hl : s.lk l' = some c
        · rw [if_pos hl, hl]
          exact ⟨(fun h => by cases h), fun h => absurd (Option.some.inj h) (Ne.symm hdc)⟩
        · rw [if_neg hl]
      rcases I d p0 q W hd' with ⟨hg, h0⟩ | hS
      · exact Or.inl ⟨hg, h0⟩
      · exact Or.inr (insAP_keep (s := s) hlk hS)
  | take p hc _ =>
    have hd' : Function.update s.ph c (.ser p) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
    · rw [Function.update_of_ne hdc] at hd'; rw [dNext_ne hdc]; exact I d p0 q W hd'
  | scan e _ _ _ =>
    rw [show DNext G NP s { s with seen := insert e s.seen } c D d = D d from dNext_same rfl]
    exact I d p0 q W hd
  | drain _ _ _ =>
    rw [show DNext G NP s { s with gate := .closed } c D d = D d from dNext_same rfl]
    exact I d p0 q W hd
  | serial keep own' cls' ko' _ hg _ _ =>
    have hd' : Function.update s.ph c .idle d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
    · rw [Function.update_of_ne hdc] at hd'
      exact absurd (by rw [hd']; trivial) (hno hg d)

/-- **`IInvP` is kept by a hardware write** (`Foreign` to every path). -/
theorem iinvP_hw {s : Cfg A V C L} {D : C → Set A} (I : IInvP G Q NP D s) {a : A} {x : V} {l : L}
    (h : HwWr s a x l) : IInvP G Q NP D (hwCfg s a x) := by
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

/-- **`IInvP` is kept by an `ADWr`** (an `ADStep` of every path's reachability). -/
theorem iinvP_ad {s : Cfg A V C L} {D : C → Set A} (I : IInvP G Q NP D s) {x : A} {y : V}
    (h : ADWr G Q NP s x y) : IInvP G Q NP D (hwCfg s x y) := by
  intro d p0 q W hd
  exact (I d p0 q W hd).imp id fun hS => hS.adstep h.adStep

end iinv

/-! ## `Safe` across an environment write, from `InsAP` -/

section safe
variable {G : A → Prop} {Q : V → V → Prop} {NP : V → Prop}
variable {own : (A → V) → A → Owner C L} {cls : A → V → V} {ko : A → ClsOwner C} {d : C} {hs : L → Prop}

/-- **`Safe` transfers across the write** for an `InsAP` body that may read the word (`safe_adR` with
`InsAP`). -/
theorem safe_adP (hQs : ∀ u w, Q u w → Q w u) {x : A} {y : V} (hGx : G x)
    (hkeep : ∀ m, own (Function.update m x y) = own m) (hko : ko x = .free) {ν : A → V} {q : Prog A V L}
    (hS : Safe own cls ko d hs ν q) :
    ∀ {D : Set A}, InsAP G Q NP own cls ko d hs D ν q → PO d hs (own ν x) → Q (ν x) y →
      Safe own cls ko d hs (Function.update ν x y) q := by
  induction hS with
  | done => intro _ _ _ _; exact .done
  | @rd μ a k h1 _ ih =>
    intro D hA hpo hq
    refine .rd (fun μ'' hR => ?_) (fun μ'' hR => ?_)
    · obtain ⟨ν', hR', rfl, _, _⟩ := freach_ad hkeep hR hpo
      rw [hkeep]; exact h1 ν' hR'
    · obtain ⟨ν', hR', rfl, hx, hpo'⟩ := freach_ad hkeep hR hpo
      have hA' := hA.reach (.of_freach hR')
      obtain ⟨hA1, hA2⟩ : (G a → ∀ u, Q u (ν' a) → k u = k (ν' a)) ∧
          InsAP G Q NP own cls ko d hs D ν' (k (ν' a)) := by
        cases hA' with
        | rd h1 h2 => exact ⟨fun hg => h1 hg ν' (.refl _), h2 ν' (.refl _)⟩
      have e : k (Function.update ν' x y a) = k (ν' a) := by
        by_cases hax : a = x
        · subst hax; rw [Function.update_self]
          exact hA1 hGx _ (hQs _ _ (by rw [hx]; exact hq))
        · rw [Function.update_of_ne hax]
      rw [e]; exact ih ν' hR' hA2 hpo' (by rw [hx]; exact hq)
  | @rds μ a k _ ih =>
    intro D hA hpo hq
    refine .rds (fun μ'' hR => ?_)
    obtain ⟨ν', hR', rfl, hx, hpo'⟩ := freach_ad hkeep hR hpo
    have hA' := hA.reach (.of_freach hR')
    obtain ⟨hA1, hA2⟩ : (G a → ∀ u, Q u (ν' a) → k u = k (ν' a)) ∧
        InsAP G Q NP own cls ko d hs D ν' (k (ν' a)) := by
      cases hA' with
      | rds h1 h2 => exact ⟨fun hg => h1 hg ν' (.refl _), h2 ν' (.refl _)⟩
    have e : k (Function.update ν' x y a) = k (ν' a) := by
      by_cases hax : a = x
      · subst hax; rw [Function.update_self]
        exact hA1 hGx _ (hQs _ _ (by rw [hx]; exact hq))
      · rw [Function.update_of_ne hax]
    rw [e]; exact ih ν' hR' hA2 hpo' (by rw [hx]; exact hq)
  | @rdc μ a K k hko' hK _ ih =>
    intro D hA hpo hq
    refine .rdc hko' hK (fun μ'' hR => ?_)
    obtain ⟨ν', hR', rfl, hx, hpo'⟩ := freach_ad hkeep hR hpo
    have hA' := hA.reach (.of_freach hR')
    obtain ⟨hA1, hA2⟩ : (G a → ∀ u, Q u (ν' a) → k u = k (ν' a)) ∧
        InsAP G Q NP own cls ko d hs D ν' (k (ν' a)) := by
      cases hA' with
      | rdc h1 h2 => exact ⟨fun hg => h1 hg ν' (.refl _), h2 ν' (.refl _)⟩
    have e : k (Function.update ν' x y a) = k (ν' a) := by
      by_cases hax : a = x
      · subst hax; rw [Function.update_self]
        exact hA1 hGx _ (hQs _ _ (by rw [hx]; exact hq))
      · rw [Function.update_of_ne hax]
    rw [e]; exact ih ν' hR' hA2 hpo' (by rw [hx]; exact hq)
  | @wr μ a v k h1 h2 h3 h4 ih =>
    intro D hA hpo hq
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
        have hAk : InsAP G Q NP own cls ko d hs (dU G NP D a v) (Function.update ν' a v) k := by
          cases hA.reach (.of_freach hR') with
          | wr _ _ h => exact h ν' (.refl _)
        refine ih ν' hR' hAk hpo1 ?_
        rw [Function.update_of_ne (Ne.symm hax), hx]; exact hq

end safe

/-- **`SInv` is kept by an `ADWr`** to whose readers it is run-relatively insensitive (`InsAP`). -/
theorem sinv_adP {G : A → Prop} {Q : V → V → Prop} {NP : V → Prop} (hQs : ∀ u w, Q u w → Q w u)
    {s : Cfg A V C L} {D : C → Set A} (I : SInv s) (J : IInvP G Q NP D s) {x : A} {y : V}
    (h : ADWr G Q NP s x y) : SInv (hwCfg s x y) := by
  intro d p0 q W hd
  rcases I d p0 q W hd with hg | hS
  · exact Or.inl hg
  · by_cases hpo : PO d (fun l => s.lk l = some d) (s.own s.mem x)
    · rcases J d p0 q W hd with ⟨hg, _⟩ | hA
      · exact Or.inl hg
      · exact Or.inr (safe_adP hQs h.g h.keep h.ko hS hA hpo h.q)
    · right
      have hF : Foreign s.own s.cls s.ko d (fun l => s.lk l = some d) s.mem x y := by
        refine ⟨hpo, fun z hz => absurd (by rw [h.keep]) hz, ?_⟩
        right; rw [h.ko]; exact ⟨(fun e => by cases e), (fun e => by cases e)⟩
      exact Safe.foreign hS hF

end

end Fl4Proofs.P2.Serial
