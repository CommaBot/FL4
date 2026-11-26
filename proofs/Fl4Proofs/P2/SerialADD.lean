/-
# P2 (line mmuAD, gen 8): **deferred A/D writes** — serialising the walker against a local path that stored a
present paging entry

`SerialADR.serializable_safeR` logs every A/D write (`ADWr`) at its time. That is impossible for a write to a word a
local path has already stored a present value into and still holds (PageMap's leaf, between `write_mapping`'s
store and `leave`): the path's log entry is logged at `leave` and stores the value *without* the bits, so the bits
have to come after it in the serial order. This module proves that ordering correct:

* **The shadow.** Beside the real configuration `s` we carry a ghost log `ℓ`, a ghost memory `σ` (the memory with
  the deferred bits not yet applied), a done set `D d` per core (the words core `d` stored a present value into),
  and the deferred writes `pd` (core, word, value), in order. `shd s σ ℓ` is `s` with memory `σ` and log `ℓ`.
* **`InvD`**: `SerialADR.InvR` of the shadow at the word set `GD G D` (`G` minus every done word), `s.mem = apl pd σ`
  (the deferred writes on top of `σ`), done words are in their core's write set, `G` words, not `NP` in `σ`,
  class-free; each deferred value is `Q`-equivalent to `σ`'s; owners ignore `G` while a path runs; and
  **`ℓ ++ pd` is a permutation of the real log `s.log`**.
* `InvD.step` (all 14 `Step` kinds; at `leave`, the leaving core's deferred writes are appended to `ℓ` right after
  its entry, each an `ADWr` of the shadow, `flushR`), `InvD.hw`, **`InvD.ad`** (a write to a done word is deferred,
  any other is logged at its time as in `InvR.ad`), `InvD.regate`.
* **`ARunD`** (as `ARunR`, started bodies `InsAP` with nothing done, every core step's owner map ignoring `G`),
  `aRunD_inv`, **`serializable_safeD`**: at a state with no local path in progress there is a log `ℓ`, a
  permutation of `s.log` (the A/D entries written during a holder's tenure moved right after the holder's entry),
  whose serial run from the initial memory is the memory: `RunAll ℓ s0.mem s.mem`.

No premise: everything here is proved.
-/
import Fl4Proofs.P2.SerialADP

namespace Fl4Proofs.P2.Serial

noncomputable section
open Classical

variable {A V C L : Type} [DecidableEq A] [DecidableEq C] [DecidableEq L]

/-! ## Deferred writes -/

/-- The deferred writes applied in order. -/
def apl : List (C × A × V) → (A → V) → (A → V)
  | [], m => m
  | e :: l, m => apl l (Function.update m e.2.1 e.2.2)

/-- A deferred write as a log entry. -/
def pwr (e : C × A × V) : Prog A V L := .wr e.2.1 e.2.2 .done

/-- The shadow configuration. -/
def shd (s : Cfg A V C L) (σ : A → V) (ℓ : List (Prog A V L)) : Cfg A V C L := { s with mem := σ, log := ℓ }

/-- Every done word. -/
def DUn (D : C → Set A) : Set A := {x | ∃ d, x ∈ D d}

/-- The word set of the shadow: `G` without the done words. -/
def GD (G : A → Prop) (D : C → Set A) : A → Prop := fun x => G x ∧ x ∉ DUn D

/-- The owner map ignores `G` words. -/
def IgnG (G : A → Prop) (own : (A → V) → A → Owner C L) : Prop :=
  ∀ m m' : A → V, (∀ z, ¬ G z → m z = m' z) → own m = own m'

theorem apl_nmem {l : List (C × A × V)} {m : A → V} {x : A} (h : ∀ e ∈ l, e.2.1 ≠ x) : apl l m x = m x := by
  induction l generalizing m with
  | nil => rfl
  | cons e l ih =>
    show apl l (Function.update m e.2.1 e.2.2) x = m x
    rw [ih (fun e' he' => h e' (List.mem_cons_of_mem _ he')),
      Function.update_of_ne (Ne.symm (h e List.mem_cons_self))]

theorem apl_upd {l : List (C × A × V)} {m : A → V} {a : A} {v : V} (h : ∀ e ∈ l, e.2.1 ≠ a) :
    apl l (Function.update m a v) = Function.update (apl l m) a v := by
  induction l generalizing m with
  | nil => rfl
  | cons e l ih =>
    show apl l (Function.update (Function.update m a v) e.2.1 e.2.2) =
      Function.update (apl l (Function.update m e.2.1 e.2.2)) a v
    rw [Function.update_comm (h e List.mem_cons_self).symm v e.2.2 m]
    exact ih (fun e' he' => h e' (List.mem_cons_of_mem _ he'))

theorem apl_append {l l' : List (C × A × V)} {m : A → V} : apl (l ++ l') m = apl l' (apl l m) := by
  induction l generalizing m with
  | nil => rfl
  | cons e l ih => exact ih

theorem apl_cases {l : List (C × A × V)} {m : A → V} (x : A) :
    apl l m x = m x ∨ ∃ e ∈ l, e.2.1 = x ∧ apl l m x = e.2.2 := by
  induction l generalizing m with
  | nil => exact Or.inl rfl
  | cons e l ih =>
    show apl l (Function.update m e.2.1 e.2.2) x = m x ∨
      ∃ e' ∈ e :: l, e'.2.1 = x ∧ apl l (Function.update m e.2.1 e.2.2) x = e'.2.2
    rcases ih (m := Function.update m e.2.1 e.2.2) with h | ⟨e', he', h1, h2⟩
    · by_cases hx : x = e.2.1
      · subst hx; rw [Function.update_self] at h
        exact Or.inr ⟨e, List.mem_cons_self, rfl, h⟩
      · rw [Function.update_of_ne hx] at h; exact Or.inl h
    · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', h1, h2⟩

theorem apl_split (p : C × A × V → Bool) {l : List (C × A × V)} {m : A → V}
    (h : ∀ e1 ∈ l, ∀ e2 ∈ l, p e1 = true → p e2 = false → e1.2.1 ≠ e2.2.1) :
    apl l m = apl (l.filter (fun e => !p e)) (apl (l.filter p) m) := by
  induction l generalizing m with
  | nil => rfl
  | cons e l ih =>
    have h' : ∀ e1 ∈ l, ∀ e2 ∈ l, p e1 = true → p e2 = false → e1.2.1 ≠ e2.2.1 :=
      fun e1 h1 e2 h2 => h e1 (List.mem_cons_of_mem _ h1) e2 (List.mem_cons_of_mem _ h2)
    cases hp : p e with
    | true =>
      have e1 : (e :: l).filter p = e :: l.filter p := by simp [List.filter_cons, hp]
      have e2 : (e :: l).filter (fun e => !p e) = l.filter (fun e => !p e) := by simp [List.filter_cons, hp]
      rw [e1, e2]
      exact ih h'
    | false =>
      have e1 : (e :: l).filter p = l.filter p := by simp [List.filter_cons, hp]
      have e2 : (e :: l).filter (fun e => !p e) = e :: l.filter (fun e => !p e) := by
        simp [List.filter_cons, hp]
      rw [e1, e2]
      show apl l (Function.update m e.2.1 e.2.2) =
        apl (l.filter (fun e => !p e)) (Function.update (apl (l.filter p) m) e.2.1 e.2.2)
      rw [ih h', apl_upd]
      intro e1 he1
      rw [List.mem_filter] at he1
      exact h e1 (List.mem_cons_of_mem _ he1.1) e List.mem_cons_self he1.2 hp

theorem perm_snoc_mid {α : Type _} {ℓ t l L : List α} (h : (ℓ ++ l).Perm L) : ((ℓ ++ t) ++ l).Perm (L ++ t) := by
  have h1 : ((ℓ ++ t) ++ l).Perm ((ℓ ++ l) ++ t) := by
    rw [List.append_assoc, List.append_assoc]; exact List.perm_append_comm.append_left ℓ
  exact h1.trans (h.append_right t)

/-! ## The invariant -/

/-- **The deferral invariant** (module docstring). -/
structure InvD (G : A → Prop) (Q : V → V → Prop) (NP : V → Prop) (m0 : A → V) (s : Cfg A V C L)
    (ℓ : List (Prog A V L)) (σ : A → V) (D : C → Set A) (pd : List (C × A × V)) (H : A → V) : Prop where
  r : InvR (GD G D) Q NP m0 (shd s σ ℓ) H
  mem : s.mem = apl pd σ
  dloc : ∀ d x, x ∈ D d → ∃ p0 p W, s.ph d = .loc p0 p W ∧ x ∈ W
  dG : ∀ d x, x ∈ D d → G x ∧ ¬ NP (σ x) ∧ s.ko x = .free
  pdD : ∀ e ∈ pd, e.2.1 ∈ D e.1
  pdQ : ∀ e ∈ pd, Q (σ e.2.1) e.2.2
  ig : (∃ d, (s.ph d).IsLoc) → IgnG G s.own
  perm : (ℓ ++ pd.map pwr).Perm s.log

section invd
variable {G : A → Prop} {Q : V → V → Prop} {NP : V → Prop} {m0 : A → V} {s : Cfg A V C L}
  {ℓ : List (Prog A V L)} {σ : A → V} {D : C → Set A} {pd : List (C × A × V)} {H : A → V}

theorem InvD.offDU (I : InvD G Q NP m0 s ℓ σ D pd H) {x : A} (hx : x ∉ DUn D) : σ x = s.mem x := by
  rw [I.mem]
  exact (apl_nmem (fun e he h => hx ⟨e.1, h ▸ I.pdD e he⟩)).symm

theorem InvD.qmem (hQ : Equivalence Q) (I : InvD G Q NP m0 s ℓ σ D pd H) (x : A) : Q (σ x) (s.mem x) := by
  rw [I.mem]
  rcases apl_cases (l := pd) (m := σ) x with h | ⟨e, he, h1, h2⟩
  · rw [h]; exact hQ.refl _
  · rw [h2, ← h1]; exact I.pdQ e he

theorem InvD.ownE (I : InvD G Q NP m0 s ℓ σ D pd H) {m m' : A → V} (h : ∀ z, z ∉ DUn D → m z = m' z) :
    s.own m = s.own m' := by
  by_cases hl : ∃ d, (s.ph d).IsLoc
  · exact I.ig hl m m' (fun z hz => h z (fun ⟨d, hd⟩ => hz (I.dG d z hd).1))
  · have e : m = m' := funext fun z => h z (fun ⟨d, hd⟩ => hl (by
      obtain ⟨p0, p, W, hph, _⟩ := I.dloc d z hd
      exact ⟨d, by rw [hph]; trivial⟩))
    rw [e]

theorem InvD.ownσ (I : InvD G Q NP m0 s ℓ σ D pd H) : s.own σ = s.own s.mem :=
  I.ownE (fun _ hz => I.offDU hz)

theorem InvD.ownσu (I : InvD G Q NP m0 s ℓ σ D pd H) (a : A) (v : V) :
    s.own (Function.update σ a v) = s.own (Function.update s.mem a v) := by
  refine I.ownE (fun z hz => ?_)
  by_cases hza : z = a
  · subst hza; rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hza, Function.update_of_ne hza]; exact I.offDU hz

theorem InvD.perm_iff (I : InvD G Q NP m0 s ℓ σ D pd H) (d : C) (x : A) :
    Perm (shd s σ ℓ) d x ↔ Perm s d x := by
  show (Held s.lk d (s.own σ x) ∨ s.own σ x = .gate) ↔ _
  rw [I.ownσ]; rfl

theorem InvD.held (I : InvD G Q NP m0 s ℓ σ D pd H) {d : C} {x : A} (hx : x ∈ D d) :
    Held s.lk d (s.own s.mem x) := by
  obtain ⟨p0, p, W, hph, hxW⟩ := I.dloc d x hx
  have h := (I.r.inv.loc d p0 p W hph).held x hxW
  change Held s.lk d (s.own σ x) at h
  rw [I.ownσ] at h; exact h

theorem InvD.ddisj (I : InvD G Q NP m0 s ℓ σ D pd H) {d e : C} {x : A} (h1 : x ∈ D d) (h2 : x ∈ D e) :
    d = e := by
  by_contra hne
  exact held_disj hne (I.held h1) (Or.inl (I.held h2))

theorem InvD.d_empty (I : InvD G Q NP m0 s ℓ σ D pd H) {d : C} (hd : ¬ (s.ph d).IsLoc) : D d = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  obtain ⟨p0, p, W, hph, _⟩ := I.dloc d x hx
  exact hd (by rw [hph]; trivial)

theorem InvD.noLoc (I : InvD G Q NP m0 s ℓ σ D pd H) (hq : NoLoc s) :
    (∀ d, D d = ∅) ∧ pd = [] ∧ σ = s.mem := by
  have hD : ∀ d, D d = ∅ := fun d => I.d_empty (hq d)
  have hp : pd = [] := by
    cases hpd : pd with
    | nil => rfl
    | cons e l =>
      have := I.pdD e (by rw [hpd]; exact List.mem_cons_self)
      rw [hD] at this; exact absurd this (Set.notMem_empty _)
  refine ⟨hD, hp, ?_⟩
  have := I.mem; rw [hp] at this; exact this.symm

end invd

/-! ## `InvR` and the word set -/

section ws
variable {G : A → Prop} {Q : V → V → Prop} {NP : V → Prop} {m0 : A → V} {s : Cfg A V C L} {H : A → V}

theorem InvR.shrink (hQ : Equivalence Q) {G' : A → Prop} (I : InvR G Q NP m0 s H) (h : ∀ x, G' x → G x) :
    InvR G' Q NP m0 s H where
  inv := I.inv
  sim d p0 p W hd n n' hG hN hcn hr := by
    refine I.sim d p0 p W hd n n' (fun x hx hg => ?_) (fun x hx hg => hN x hx (fun h' => hg (h x h'))) hcn hr
    by_cases hg' : G' x
    · exact hG x hx hg'
    · rw [hN x hx hg']; exact hQ.refl _
  np d p0 p W hd x hx hg := I.np d p0 p W hd x hx (h x hg)

theorem InvR.grow {G' : A → Prop} (I : InvR G Q NP m0 s H) (h : ∀ x, G x → G' x)
    (hn : ∀ x, G' x → ¬ G x → ∀ d p0 p W, s.ph d = .loc p0 p W → ¬ Perm s d x ∧ x ∉ W) :
    InvR G' Q NP m0 s H where
  inv := I.inv
  sim d p0 p W hd n n' hG hN hcn hr := by
    refine I.sim d p0 p W hd n n' (fun x hx hg => hG x hx (h x hg)) (fun x hx hg => ?_) hcn hr
    by_cases hg' : G' x
    · exact absurd hx (hn x hg' hg d p0 p W hd).1
    · exact hN x hx hg'
  np d p0 p W hd x hx hg := by
    by_cases hg0 : G x
    · exact I.np d p0 p W hd x hx hg0
    · exact absurd hx (hn x hg hg0 d p0 p W hd).2

/-- The shadow after appending deferred writes to memory and log. -/
def flc (t : Cfg A V C L) (l : List (C × A × V)) : Cfg A V C L :=
  { t with mem := apl l t.mem, log := t.log ++ l.map pwr }

/-- **The flush**: deferred writes, each an `ADWr` of the shadow, appended one after another. -/
theorem flushR (hQ : Equivalence Q) (hQN : ∀ u w, Q u w → (NP u ↔ NP w)) :
    ∀ (l : List (C × A × V)) (t : Cfg A V C L) (H : A → V), InvR G Q NP m0 t H →
      (∀ e ∈ l, G e.2.1 ∧ ¬ NP (t.mem e.2.1) ∧ Q (t.mem e.2.1) e.2.2 ∧
        (∀ m, t.own (Function.update m e.2.1 e.2.2) = t.own m) ∧ t.ko e.2.1 = .free) →
      ∃ H', InvR G Q NP m0 (flc t l) H'
  | [], t, H, I, _ => ⟨H, by
      have e : flc t [] = t := by cases t; simp [flc, apl]
      rw [e]; exact I⟩
  | e :: l, t, H, I, h => by
    obtain ⟨hg, hnp, hq, hk, hko⟩ := h e List.mem_cons_self
    have I1 := I.ad hQ ⟨hg, hnp, hq, hk, hko⟩
    obtain ⟨H', I'⟩ := flushR hQ hQN l (hwCfg t e.2.1 e.2.2) _ I1 (by
      intro e' he'
      obtain ⟨hg', hnp', hq', hk', hko'⟩ := h e' (List.mem_cons_of_mem _ he')
      refine ⟨hg', ?_, ?_, hk', hko'⟩
      · show ¬ NP (Function.update t.mem e.2.1 e.2.2 e'.2.1)
        by_cases hx : e'.2.1 = e.2.1
        · rw [hx, Function.update_self]; rw [hx] at hnp'
          exact fun h' => hnp ((hQN _ _ hq).mpr h')
        · rw [Function.update_of_ne hx]; exact hnp'
      · show Q (Function.update t.mem e.2.1 e.2.2 e'.2.1) e'.2.2
        by_cases hx : e'.2.1 = e.2.1
        · rw [hx, Function.update_self]; rw [hx] at hq'
          exact hQ.trans (hQ.symm hq) hq'
        · rw [Function.update_of_ne hx]; exact hq')
    refine ⟨H', ?_⟩
    have e1 : flc (hwCfg t e.2.1 e.2.2) l = flc t (e :: l) := by
      cases t; simp [flc, hwCfg, apl, pwr]
    rw [← e1]; exact I'

end ws

/-! ## Steps -/

section steps
variable {G : A → Prop} {Q : V → V → Prop} {NP : V → Prop} {m0 : A → V}

theorem inv_rdsV {s : Cfg A V C L} {H : A → V} (I : InvH m0 s H) {c : C}
    {p0 : Prog A V L} {a : A} {k : V → Prog A V L} {W : Set A}
    (hc : s.ph c = .loc p0 (.rds a k) W) (v : V) :
    InvH m0 { s with ph := Function.update s.ph c (.loc p0 (k v) W) } H := by
  have Ic := I.loc c p0 _ W hc
  exact I.locstep (p' := k v) (W' := W) hc rfl rfl rfl rfl (subset_refl _)
    (fun _ _ => rfl) (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ _ _ _ _ _ => rfl)
    rfl rfl (I.clsW hc)
    { held := Ic.held
      sim := fun n n' hn hcn hr => Ic.sim n n' hn hcn (Run.rds _ hr) }

theorem held_of_release {lk : L → Option C} {c d : C} {o : Owner C L} (h : Held (release lk c) d o) :
    Held lk d o := by
  cases o with
  | core e => exact h
  | lock l =>
    have h' : (if lk l = some c then none else lk l) = some d := h
    show lk l = some d
    by_cases hl : lk l = some c
    · rw [if_pos hl] at h'; cases h'
    · rw [if_neg hl] at h'; exact h'
  | gate => exact h

theorem dNext_id {s s' : Cfg A V C L} {c : C} {D : C → Set A}
    (h : (match s.ph c with
      | .loc _ (.wr a v _) _ => dU G NP (D c) a v
      | .loc _ .done _ => ∅
      | _ => D c) = D c) : DNext G NP s s' c D = D := by
  funext d
  by_cases hd : d = c
  · subst hd; exact dNext_self h
  · exact dNext_ne hd

variable {s : Cfg A V C L} {ℓ : List (Prog A V L)} {σ : A → V} {D : C → Set A} {pd : List (C × A × V)}
  {H : A → V}

/-- Steps keeping memory, owners, classes and log, and every in-progress path's write set. -/
theorem InvD.keepLoc (I : InvD G Q NP m0 s ℓ σ D pd H) {s' : Cfg A V C L}
    (hph : ∀ d p0 p W, s.ph d = .loc p0 p W → ∃ p0' p' W', s'.ph d = .loc p0' p' W' ∧ W ⊆ W')
    (hmem : s'.mem = s.mem) (hko : s'.ko = s.ko) (hlog : s'.log = s.log)
    (r : InvR (GD G D) Q NP m0 (shd s' σ ℓ) H) (hig : IgnG G s'.own) :
    InvD G Q NP m0 s' ℓ σ D pd H where
  r := r
  mem := by rw [hmem]; exact I.mem
  dloc d x hx := by
    obtain ⟨p0, p, W, h1, h2⟩ := I.dloc d x hx
    obtain ⟨p0', p', W', h3, h4⟩ := hph d p0 p W h1
    exact ⟨p0', p', W', h3, h4 h2⟩
  dG d x hx := by rw [hko]; exact I.dG d x hx
  pdD := I.pdD
  pdQ := I.pdQ
  ig _ := hig
  perm := by rw [hlog]; exact I.perm

/-- The stepping core's phase changes in place (same write set). -/
theorem keep_c {s : Cfg A V C L} {c : C} {p0 p p' : Prog A V L} {W : Set A} (hc : s.ph c = .loc p0 p W) :
    ∀ d q0 q U, s.ph d = .loc q0 q U →
      ∃ q0' q' U', Function.update s.ph c (.loc p0 p' W) d = .loc q0' q' U' ∧ U ⊆ U' := by
  intro d q0 q U hd
  by_cases hdc : d = c
  · subst hdc; rw [hc] at hd; cases hd
    exact ⟨_, _, _, Function.update_self .., subset_refl _⟩
  · exact ⟨_, _, _, by rw [Function.update_of_ne hdc]; exact hd, subset_refl _⟩

theorem keep_nonloc {s : Cfg A V C L} {c : C} {X : Phase A V L} (hc : ¬ (s.ph c).IsLoc) :
    ∀ d q0 q U, s.ph d = .loc q0 q U →
      ∃ q0' q' U', Function.update s.ph c X d = .loc q0' q' U' ∧ U ⊆ U' := by
  intro d q0 q U hd
  have hdc : d ≠ c := by rintro rfl; rw [hd] at hc; exact hc trivial
  exact ⟨_, _, _, by rw [Function.update_of_ne hdc]; exact hd, subset_refl _⟩

/-- **Every core step keeps `InvD`** (module docstring). -/
theorem InvD.step (hQ : Equivalence Q) (hQN : ∀ u w, Q u w → (NP u ↔ NP w))
    (I : InvD G Q NP m0 s ℓ σ D pd H) (J : IInvP G Q NP D s) {c : C} {s' : Cfg A V C L}
    (hal : Allowed s c) (hst : Step s c s') (hig : IgnG G s'.own) :
    ∃ ℓ' σ' pd' H', InvD G Q NP m0 s' ℓ' σ' (DNext G NP s s' c D) pd' H' := by
  cases hst with
  | arm p hc =>
    have hc' : ¬ (s.ph c).IsLoc := by rw [hc]; exact Phase.idle_not_loc
    rw [dNext_id (G := G) (NP := NP) (s := s) (c := c) (D := D) (by simp only [hc])]
    exact ⟨ℓ, σ, pd, H, I.keepLoc (keep_nonloc hc') rfl rfl rfl
      (I.r.frame (inv_phase I.r.inv (Phase.arm_not_loc p) hc') rfl rfl rfl rfl rfl
        (fun d q0 q U h => (upd_nonloc (Phase.arm_not_loc p) hc' d q0 q U).mp h)) hig⟩
  | back hc _ =>
    have hc' : ¬ (s.ph c).IsLoc := by rw [hc]; exact Phase.arm_not_loc _
    rw [dNext_id (G := G) (NP := NP) (s := s) (c := c) (D := D) (by simp only [hc])]
    exact ⟨ℓ, σ, pd, H, I.keepLoc (keep_nonloc hc') rfl rfl rfl
      (I.r.frame (inv_phase I.r.inv Phase.idle_not_loc hc') rfl rfl rfl rfl rfl
        (fun d q0 q U h => (upd_nonloc Phase.idle_not_loc hc' d q0 q U).mp h)) hig⟩
  | @enter p hc hg =>
    have hc' : ¬ (s.ph c).IsLoc := by rw [hc]; exact Phase.arm_not_loc _
    rw [dNext_id (G := G) (NP := NP) (s := s) (c := c) (D := D) (by simp only [hc])]
    refine ⟨ℓ, σ, pd, H, I.keepLoc (keep_nonloc hc') rfl rfl rfl ⟨inv_enter I.r.inv hc hg, ?_, ?_⟩ hig⟩
    · intro d q0 q U hd
      rcases upd_loc hd with ⟨rfl, he⟩ | ⟨hdc, hd⟩
      · cases he
        intro n n' _ _ _ hr
        rw [mix_empty] at hr; exact hr
      · exact (I.r.sim d q0 q U hd).mono (fun _ h => h) (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl
          (fun _ _ => rfl)
    · intro d q0 q U hd x hx hg
      rcases upd_loc hd with ⟨rfl, he⟩ | ⟨_, hd⟩
      · cases he; exact absurd hx (Set.notMem_empty x)
      · exact I.r.np d q0 q U hd x hx hg
  | @rd p0 a k W hc =>
    simp only [Allowed, hc] at hal
    rw [dNext_id (G := G) (NP := NP) (s := s) (c := c) (D := D) (by simp only [hc])]
    have hp' : Perm (shd s σ ℓ) c a := (I.perm_iff c a).mpr hal
    obtain ⟨h1, -⟩ : (G a → ∀ μ', FReachA G Q NP s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem μ' →
        ∀ u, Q u (μ' a) → k u = k (μ' a)) ∧ True := by
      rcases J c p0 _ W hc with ⟨hgl, _⟩ | hS
      · cases hgl
      · cases hS with
        | rd h1 _ => exact ⟨h1, trivial⟩
    have hk : k (σ a) = k (s.mem a) := by
      by_cases ha : a ∈ DUn D
      · obtain ⟨d, hd⟩ := ha
        have hdc : d = c := by
          by_contra hne; exact held_disj hne (I.held hd) hal
        subst hdc
        exact h1 (I.dG d a hd).1 s.mem (.refl _) (σ a) (I.qmem hQ a)
      · rw [I.offDU ha]
    have hI' : InvH m0 (shd { s with ph := Function.update s.ph c (.loc p0 (k (s.mem a)) W) } σ ℓ) H := by
      have h0 := inv_rd I.r.inv (c := c) hc hp'
      have hk' : k ((shd s σ ℓ).mem a) = k (s.mem a) := hk
      rw [hk'] at h0; exact h0
    refine ⟨ℓ, σ, pd, H, I.keepLoc (keep_c hc) rfl rfl rfl ?_ hig⟩
    refine I.r.locstep hI' hc rfl (fun _ _ _ h => h) (fun _ _ _ _ _ _ _ _ => rfl) rfl rfl ?_
      (fun x hx hg => I.r.np c p0 _ W hc x hx hg)
    intro n n' hG hN hcn hr
    refine I.r.sim c p0 _ W hc n n' hG hN hcn (Run.rd ?_)
    have hval : k (mix W σ n a) = k (s.mem a) := by
      by_cases haW : a ∈ W
      · rw [mix_mem haW]; exact hk
      · rw [mix_nmem haW]
        have hHa := I.r.inv.hist_perm hc hp' haW
        by_cases hg : GD G D a
        · have hq := hG a hp' hg
          rw [hHa] at hq
          change Q (n a) (σ a) at hq
          rw [I.offDU hg.2] at hq
          exact h1 hg.1 s.mem (.refl _) (n a) hq
        · rw [hN a hp' hg, hHa]; exact hk
    change Run (k (mix W σ n a)) (mix W σ n) n'
    rw [hval]; exact hr
  | @rds p0 a k W hc =>
    rw [dNext_id (G := G) (NP := NP) (s := s) (c := c) (D := D) (by simp only [hc])]
    refine ⟨ℓ, σ, pd, H, I.keepLoc (keep_c hc) rfl rfl rfl ?_ hig⟩
    exact I.r.locstep (inv_rdsV I.r.inv hc (s.mem a)) hc rfl (fun _ _ _ h => h)
      (fun _ _ _ _ _ _ _ _ => rfl) rfl rfl
      (fun n n' hG hN hcn hr => I.r.sim c p0 _ W hc n n' hG hN hcn (Run.rds _ hr))
      (fun x hx hg => I.r.np c p0 _ W hc x hx hg)
  | @rdc p0 a K k W hc =>
    simp only [Allowed, hc] at hal
    obtain ⟨hko, hK⟩ := hal
    rw [dNext_id (G := G) (NP := NP) (s := s) (c := c) (D := D) (by simp only [hc])]
    have ha : a ∉ DUn D := by
      rintro ⟨d, hd⟩
      rw [(I.dG d a hd).2.2] at hko
      rcases hko with h | h <;> cases h
    have e : (shd s σ ℓ).mem a = s.mem a := I.offDU ha
    have hI' : InvH m0 (shd { s with ph := Function.update s.ph c (.loc p0 (k (s.mem a)) W) } σ ℓ) H := by
      have h0 := inv_rdc I.r.inv (c := c) hc hko hK
      rw [e] at h0; exact h0
    have hcl : ∀ n : A → V, (∀ x, (s.ko x = .gate ∨ s.ko x = .core c) →
        s.cls x (n x) = s.cls x (H x)) → s.cls a (mix W σ n a) = s.cls a (s.mem a) := by
      intro n hn
      rw [← e]
      by_cases haW : a ∈ W
      · exact congrArg (s.cls a) (mix_mem haW)
      · rw [mix_nmem haW, hn a hko]
        rcases I.r.inv.clsinv a with h | ⟨e', q0, q, U, he, hx, hk⟩
        · exact h.symm
        · exfalso
          rcases hko with hg | hco
          · rcases hk with h | h <;> change s.ko a = _ at h <;> rw [hg] at h <;> cases h
          · rcases hk with h | h
            · change s.ko a = _ at h
              rw [hco] at h
              obtain rfl : c = e' := ClsOwner.core.inj h
              change s.ph c = _ at he
              rw [hc] at he; cases he; exact haW hx
            · change s.ko a = _ at h
              rw [hco] at h; cases h
    refine ⟨ℓ, σ, pd, H, I.keepLoc (keep_c hc) rfl rfl rfl ?_ hig⟩
    exact I.r.locstep hI' hc rfl (fun _ _ _ h => h)
      (fun _ _ _ _ _ _ _ _ => rfl) rfl rfl
      (fun n n' hG hN hcn hr => I.r.sim c p0 _ W hc n n' hG hN hcn (Run.rdc _ (hK _ _ (hcl n hcn)) hr))
      (fun x hx hg => I.r.np c p0 _ W hc x hx hg)
  | @start p0 k W hc =>
    rw [dNext_id (G := G) (NP := NP) (s := s) (c := c) (D := D) (by simp only [hc])]
    refine ⟨ℓ, σ, pd, H, I.keepLoc (keep_c hc) rfl rfl rfl ?_ hig⟩
    exact I.r.locstep (inv_start I.r.inv hc) hc rfl (fun _ _ _ h => h) (fun _ _ _ _ _ _ _ _ => rfl)
      rfl rfl (fun n n' hG hN hcn hr => I.r.sim c p0 _ W hc n n' hG hN hcn (Run.start hr))
      (fun x hx hg => I.r.np c p0 _ W hc x hx hg)
  | @lock p0 l k W b hc hb =>
    rw [dNext_id (G := G) (NP := NP) (s := s) (c := c) (D := D) (by simp only [hc])]
    refine ⟨ℓ, σ, pd, H, I.keepLoc (keep_c hc) rfl rfl rfl ?_ hig⟩
    exact I.r.locstep (inv_lock I.r.inv hc b hb) hc rfl (fun _ _ _ h => Or.imp (held_lock hb) id h)
      (fun _ _ _ _ _ _ _ _ => rfl) rfl rfl
      (fun n n' hG hN hcn hr => I.r.sim c p0 _ W hc n n'
        (fun x hx hg => hG x (Or.imp (held_lock hb) id hx) hg)
        (fun x hx hg => hN x (Or.imp (held_lock hb) id hx) hg) hcn (Run.lock b hr))
      (fun x hx hg => I.r.np c p0 _ W hc x hx hg)
  | @wr p0 a v k W hc =>
    simp only [Allowed, hc] at hal
    obtain ⟨ha, hmv, hcls⟩ := hal
    obtain ⟨h0, hko0⟩ : a ∉ D c ∧ (G a → ¬ NP v → s.ko a = .free) := by
      rcases J c p0 _ W hc with ⟨hgl, _⟩ | hS
      · cases hgl
      · cases hS with
        | wr h0 h1 _ => exact ⟨h0, h1⟩
    have haD : a ∉ DUn D := by
      rintro ⟨d, hd⟩
      by_cases hdc : d = c
      · subst hdc; exact h0 hd
      · exact held_disj hdc (I.held hd) (Or.inl ha)
    -- the new done sets
    let D1 : C → Set A := Function.update D c (dU G NP (D c) a v)
    have hne : (Function.update s.ph c (.loc p0 k (insert a W))) ≠ s.ph := by
      intro h
      have h1 := congrFun h c
      rw [Function.update_self, hc] at h1
      obtain ⟨-, h2, -⟩ := Phase.loc.inj h1
      exact prog_wr_ne h2.symm
    have eDc := dNext_wr (G := G) (NP := NP) (D := D) (s' := { s with mem := Function.update s.mem a v, ph := Function.update s.ph c (.loc p0 k (insert a W)) }) hc hne
    have eD : DNext G NP s { s with mem := Function.update s.mem a v, ph := Function.update s.ph c (.loc p0 k (insert a W)) } c D = D1 := by
      funext d
      by_cases hdc : d = c
      · rw [hdc, eDc]; exact (Function.update_self c (dU G NP (D c) a v) D).symm
      · rw [dNext_ne hdc]; exact (Function.update_of_ne hdc _ D).symm
    rw [eD]
    have hD1 : ∀ d x, x ∈ D d → x ∈ D1 d := by
      intro d x hx
      by_cases hdc : d = c
      · subst hdc; show x ∈ Function.update D d _ d; rw [Function.update_self]; exact Or.inl hx
      · show x ∈ Function.update D c _ d; rw [Function.update_of_ne hdc]; exact hx
    have hD1' : ∀ d x, x ∈ D1 d → x ∈ D d ∨ (d = c ∧ x = a ∧ G a ∧ ¬ NP v) := by
      intro d x hx
      by_cases hdc : d = c
      · subst hdc
        change x ∈ Function.update D d _ d at hx
        rw [Function.update_self] at hx
        rcases hx with hx | ⟨rfl, hg, hn⟩
        · exact Or.inl hx
        · exact Or.inr ⟨rfl, rfl, hg, hn⟩
      · change x ∈ Function.update D c _ d at hx
        rw [Function.update_of_ne hdc] at hx; exact Or.inl hx
    have Ir := I.r.shrink hQ (G' := GD G D1) (fun x hx => ⟨hx.1, fun ⟨d, hd⟩ => hx.2 ⟨d, hD1 d x hd⟩⟩)
    have hnpv : GD G D1 a → NP v := by
      intro hg
      by_contra hn
      exact hg.2 ⟨c, by show a ∈ Function.update D c _ c; rw [Function.update_self]; exact Or.inr ⟨rfl, hg.1, hn⟩⟩
    have hσa : σ a = s.mem a := I.offDU haD
    -- the shadow's write
    have ha' : Held s.lk c (s.own σ a) := by rw [I.ownσ]; exact ha
    have hmv' : ∀ x, s.own (Function.update σ a v) x ≠ s.own σ x →
        Held s.lk c (s.own σ x) ∧ Held s.lk c (s.own (Function.update σ a v) x) := by
      intro x hx
      rw [I.ownσ, I.ownσu] at hx ⊢
      exact hmv x hx
    have hcls' : s.cls a v = s.cls a (σ a) ∨ s.ko a = .core c ∨ s.ko a = .free := by rw [hσa]; exact hcls
    have hI' := inv_wr Ir.inv (c := c) hc ha' hmv' hcls'
    have hsame : ∀ d, d ≠ c → ∀ x, (Held s.lk d (s.own σ x) ∨ s.own σ x = .gate) →
        s.own (Function.update σ a v) x = s.own σ x := by
      intro d hdc x h
      by_contra hne
      exact held_disj (Ne.symm hdc) (hmv' x hne).1 h
    have hpa : ∀ e ∈ pd, e.2.1 ≠ a := fun e he h => haD ⟨e.1, h ▸ I.pdD e he⟩
    refine ⟨ℓ, Function.update σ a v, pd, H, ⟨?_, ?_, ?_, ?_, ?_, ?_, fun _ => hig, I.perm⟩⟩
    · refine Ir.locstep hI' hc rfl ?_ ?_ rfl rfl ?_ ?_
      · intro d hdc x h
        show Held s.lk d (s.own (Function.update σ a v) x) ∨ s.own (Function.update σ a v) x = .gate
        rw [hsame d hdc x h]; exact h
      · intro d hdc q0 q U hd x hx
        have hxa : x ≠ a := by
          rintro rfl
          exact held_disj (Ne.symm hdc) ha' (Or.inl ((Ir.inv.loc d q0 q U hd).held x hx))
        exact Function.update_of_ne hxa _ _
      · intro n n' hG hN hcn hr
        have hp : ∀ x, Perm (shd s σ ℓ) c x →
            Held s.lk c (s.own (Function.update σ a v) x) ∨
              s.own (Function.update σ a v) x = .gate := by
          intro x hx
          by_cases he : s.own (Function.update σ a v) x = s.own σ x
          · rw [he]; exact hx
          · exact Or.inl (hmv' x he).2
        exact Ir.sim c p0 _ W hc n n' (fun x hx hg => hG x (hp x hx) hg) (fun x hx hg => hN x (hp x hx) hg)
          hcn (Run.wr (by rw [mix_upd]; exact hr))
      · intro x hx hg
        show NP (Function.update σ a v x)
        by_cases hxa : x = a
        · subst hxa; rw [Function.update_self]; exact hnpv hg
        · rw [Function.update_of_ne hxa]
          exact Ir.np c p0 _ W hc x ((Set.mem_insert_iff.mp hx).resolve_left hxa) hg
    · show Function.update s.mem a v = apl pd (Function.update σ a v)
      rw [apl_upd hpa, I.mem]
    · intro d x hx
      rcases hD1' d x hx with hx | ⟨rfl, rfl, _, _⟩
      · obtain ⟨q0, q, U, hph, hxU⟩ := I.dloc d x hx
        by_cases hdc : d = c
        · subst hdc; rw [hc] at hph; cases hph
          exact ⟨_, _, _, Function.update_self .., Set.mem_insert_of_mem _ hxU⟩
        · exact ⟨_, _, _, by show Function.update s.ph c _ d = _; rw [Function.update_of_ne hdc]; exact hph,
            hxU⟩
      · exact ⟨_, _, _, Function.update_self .., Set.mem_insert _ _⟩
    · intro d x hx
      rcases hD1' d x hx with hx | ⟨rfl, rfl, hg, hn⟩
      · have hxa : x ≠ a := fun e => haD ⟨d, e ▸ hx⟩
        rw [Function.update_of_ne hxa]; exact I.dG d x hx
      · rw [Function.update_self]; exact ⟨hg, hn, hko0 hg hn⟩
    · intro e he; exact hD1 _ _ (I.pdD e he)
    · intro e he
      rw [Function.update_of_ne (hpa e he)]; exact I.pdQ e he
  | @leave p0 W hc =>
    have Ic := I.r.inv.loc c p0 _ W hc
    let D0 : C → Set A := Function.update D c ∅
    have hne : Function.update s.ph c (.idle : Phase A V L) ≠ s.ph := by
      intro h; have h1 := congrFun h c; rw [Function.update_self, hc] at h1; cases h1
    have eDc : DNext G NP s { s with lk := release s.lk c, ph := Function.update s.ph c .idle, log := s.log ++ [p0] } c D c = ∅ := by
      simp only [DNext]; rw [if_pos (And.intro trivial hne), hc]
    have eD : DNext G NP s { s with lk := release s.lk c, ph := Function.update s.ph c .idle, log := s.log ++ [p0] } c D = D0 := by
      funext d
      by_cases hdc : d = c
      · rw [hdc, eDc]; exact (Function.update_self c (∅ : Set A) D).symm
      · rw [dNext_ne hdc]; exact (Function.update_of_ne hdc _ D).symm
    rw [eD]
    have hDc : ∀ d x, x ∈ D d → d ≠ c → x ∈ D0 d := by
      intro d x hx hdc; show x ∈ Function.update D c ∅ d; rw [Function.update_of_ne hdc]; exact hx
    have hD0' : ∀ d x, x ∈ D0 d → x ∈ D d ∧ d ≠ c := by
      intro d x hx
      change x ∈ Function.update D c ∅ d at hx
      by_cases hdc : d = c
      · subst hdc; rw [Function.update_self] at hx; exact absurd hx (Set.notMem_empty _)
      · rw [Function.update_of_ne hdc] at hx; exact ⟨hx, hdc⟩
    -- the shadow's `leave` (`InvR.step`'s case)
    have Ir1 : InvR (GD G D) Q NP m0 (shd { s with lk := release s.lk c, ph := Function.update s.ph c .idle, log := s.log ++ [p0] } σ (ℓ ++ [p0])) (mix W σ H) := by
      refine ⟨inv_leave I.r.inv hc, ?_, ?_⟩
      · intro d q0 q U hd
        rcases upd_loc hd with ⟨_, he⟩ | ⟨hdc, hd⟩
        · cases he
        · refine (I.r.sim d q0 q U hd).mono (fun x h => Or.imp (held_release hdc) id h)
            (fun x hp => mix_nmem (fun hxW => held_disj (Ne.symm hdc) (Ic.held x hxW) hp))
            (fun _ _ => rfl) rfl rfl (fun x hx => ?_)
          by_cases hxW : x ∈ W
          · rw [mix_mem hxW]
            rcases I.r.inv.clsinv x with h | ⟨e, q0', q', U', he, hxU, hk⟩
            · exact h
            · exfalso
              have hec : e = c := by
                by_contra hne
                exact held_disj hne ((I.r.inv.loc e q0' q' U' he).held x hxU) (Or.inl (Ic.held x hxW))
              subst hec
              rcases hx with h1 | h1 <;> rcases hk with h2 | h2 <;> change s.ko x = _ at h1 h2 <;>
                rw [h1] at h2 <;>
                first | exact hdc (ClsOwner.core.inj h2) | exact hdc (ClsOwner.core.inj h2).symm | cases h2
          · rw [mix_nmem hxW]
      · intro d q0 q U hd x hx hg
        rcases upd_loc hd with ⟨_, he⟩ | ⟨_, hd⟩
        · cases he
        · exact I.r.np d q0 q U hd x hx hg
    -- grow to the word set without `c`'s done words
    have Ir2 := Ir1.grow (G' := GD G D0)
      (fun x hx => ⟨hx.1, fun ⟨d, hd⟩ => hx.2 ⟨d, (hD0' d x hd).1⟩⟩) (by
        intro x hx hn d q0 q U hd
        have hxc : x ∈ D c := by
          by_contra hxc
          refine hn ⟨hx.1, fun ⟨e, he⟩ => ?_⟩
          by_cases hec : e = c
          · subst hec; exact hxc he
          · exact hx.2 ⟨e, hDc e x he hec⟩
        have hdc : d ≠ c := by
          intro e; rw [e] at hd
          change Function.update s.ph c _ c = _ at hd; rw [Function.update_self] at hd; cases hd
        have hcx := I.held hxc
        refine ⟨fun hp => ?_, fun hxU => ?_⟩
        · change Held (release s.lk c) d (s.own σ x) ∨ s.own σ x = .gate at hp
          rw [I.ownσ] at hp
          exact held_disj (Ne.symm hdc) hcx (hp.imp_left held_of_release)
        · have h1 := (Ir1.inv.loc d q0 q U hd).held x hxU
          change Held (release s.lk c) d (s.own σ x) at h1
          rw [I.ownσ] at h1
          exact held_disj (Ne.symm hdc) hcx (Or.inl (held_of_release h1)))
    -- the flush
    let pc : C × A × V → Bool := fun e => decide (e.1 = c)
    have hcloc : ∃ d, (s.ph d).IsLoc := ⟨c, by rw [hc]; trivial⟩
    have hpc : ∀ e ∈ pd.filter pc, e ∈ pd ∧ e.1 = c := by
      intro e he; rw [List.mem_filter] at he; exact ⟨he.1, of_decide_eq_true he.2⟩
    obtain ⟨H', Ir3⟩ := flushR hQ hQN (pd.filter pc) _ _ Ir2 (by
      intro e he
      obtain ⟨hep, hec⟩ := hpc e he
      have hx : e.2.1 ∈ D c := by have h' := I.pdD e hep; rw [hec] at h'; exact h'
      obtain ⟨hg, hn, hko⟩ := I.dG c e.2.1 hx
      refine ⟨⟨hg, fun ⟨d, hd⟩ => ?_⟩, hn, I.pdQ e hep, fun m => ?_, hko⟩
      · obtain ⟨hd1, hdc⟩ := hD0' d _ hd
        exact hdc (I.ddisj hd1 hx)
      · refine I.ig hcloc _ _ (fun z hz => ?_)
        have hzx : z ≠ e.2.1 := fun h => hz (h ▸ hg)
        exact Function.update_of_ne hzx _ _)
    have hwc : ∀ e ∈ pd.filter pc, ∀ x, (∀ d, x ∈ D d → d ≠ c) → e.2.1 ≠ x := by
      intro e he x hx h
      obtain ⟨hep, hec⟩ := hpc e he
      have h' := I.pdD e hep
      rw [hec, h] at h'
      exact hx c h' rfl
    refine ⟨(ℓ ++ [p0]) ++ (pd.filter pc).map pwr, apl (pd.filter pc) σ, pd.filter (fun e => !pc e), H',
      ⟨Ir3, ?_, ?_, ?_, ?_, ?_, fun _ => hig, ?_⟩⟩
    · show s.mem = _
      rw [I.mem]
      refine apl_split pc (fun e1 h1 e2 h2 hp1 hp2 => ?_)
      have hx1 : e1.2.1 ∈ D c := by
        have h' := I.pdD e1 h1; rw [of_decide_eq_true hp1] at h'; exact h'
      have hn2 : e2.1 ≠ c := fun h => by simp [pc, h] at hp2
      intro he
      rw [he] at hx1
      exact hn2 (I.ddisj (I.pdD e2 h2) hx1)
    · intro d x hx
      obtain ⟨hx, hdc⟩ := hD0' d x hx
      obtain ⟨q0, q, U, hph, hxU⟩ := I.dloc d x hx
      exact ⟨q0, q, U, by show Function.update s.ph c _ d = _; rw [Function.update_of_ne hdc]; exact hph, hxU⟩
    · intro d x hx
      obtain ⟨hx, hdc⟩ := hD0' d x hx
      rw [apl_nmem (fun e he h => hwc e he x (fun d' hd' h' => hdc ((I.ddisj hd' hx).symm.trans h')) h)]
      exact I.dG d x hx
    · intro e he
      rw [List.mem_filter] at he
      have hn : e.1 ≠ c := fun h => by simp [pc, h] at he
      exact hDc _ _ (I.pdD e he.1) hn
    · intro e he
      rw [List.mem_filter] at he
      have hn : e.1 ≠ c := fun h => by simp [pc, h] at he
      have hx := I.pdD e he.1
      rw [apl_nmem (fun e' he' h => hwc e' he' e.2.1 (fun d' hd' h' => hn ((I.ddisj hd' hx).symm.trans h')) h)]
      exact I.pdQ e he.1
    · have h1 : (pd.filter pc ++ pd.filter (fun e => !pc e)).Perm pd := List.filter_append_perm _ _
      show (((ℓ ++ [p0]) ++ (pd.filter pc).map pwr) ++ (pd.filter (fun e => !pc e)).map pwr).Perm
        (s.log ++ [p0])
      rw [List.append_assoc (ℓ ++ [p0]), ← List.map_append]
      exact ((h1.map pwr).append_left (ℓ ++ [p0])).trans (perm_snoc_mid I.perm)
  | take p hc _ =>
    have hX : ¬ (Phase.ser p : Phase A V L).IsLoc := Phase.ser_not_loc p
    have hc' : ¬ (s.ph c).IsLoc := by rw [hc]; exact Phase.idle_not_loc
    rw [dNext_id (G := G) (NP := NP) (s := s) (c := c) (D := D) (by simp only [hc])]
    exact ⟨ℓ, σ, pd, H, I.keepLoc (keep_nonloc hc') rfl rfl rfl
      (I.r.frame (inv_take I.r.inv p hc) rfl rfl rfl rfl rfl
        (fun d q0 q U h => (upd_nonloc hX hc' d q0 q U).mp h)) hig⟩
  | scan d _ _ hd =>
    rw [show DNext G NP s { s with seen := insert d s.seen } c D = D from funext fun _ => dNext_same rfl]
    exact ⟨ℓ, σ, pd, H, I.keepLoc (fun d q0 q U h => ⟨q0, q, U, h, subset_refl _⟩) rfl rfl rfl
      (I.r.frame (inv_scan I.r.inv d hd) rfl rfl rfl rfl rfl (fun _ _ _ _ h => h)) hig⟩
  | drain _ hg hall =>
    rw [show DNext G NP s { s with gate := .closed } c D = D from funext fun _ => dNext_same rfl]
    exact ⟨ℓ, σ, pd, H, I.keepLoc (fun d q0 q U h => ⟨q0, q, U, h, subset_refl _⟩) rfl rfl rfl
      (I.r.frame (inv_drain I.r.inv hg hall) rfl rfl rfl rfl rfl (fun _ _ _ _ h => h)) hig⟩
  | @serial p m' keep own' cls' ko' _ hg hc hr =>
    rw [dNext_id (G := G) (NP := NP) (s := s) (c := c) (D := D) (by simp only [hc])]
    have nl : NoLoc s := I.r.inv.clo hg
    obtain ⟨hD, hpd, hσ⟩ := I.noLoc nl
    have hr' : Run p (shd s σ ℓ).mem m' := by show Run p σ m'; rw [hσ]; exact hr
    refine ⟨ℓ ++ [p], m', [], m', ⟨InvR.of_noLoc (inv_serial I.r.inv keep own' cls' ko' hg hr')
      (fun d hd => nl d (upd_isLoc Phase.idle_not_loc hd).2), rfl, ?_, ?_, ?_, ?_, fun _ => hig, ?_⟩⟩
    · intro d x hx; rw [hD] at hx; exact absurd hx (Set.notMem_empty _)
    · intro d x hx; rw [hD] at hx; exact absurd hx (Set.notMem_empty _)
    · intro e he; cases he
    · intro e he; cases he
    · have h1 := I.perm
      rw [hpd] at h1
      simp only [List.map_nil, List.append_nil] at h1 ⊢
      exact h1.append_right [p]

/-- **A hardware write keeps `InvD`** (the shadow takes it, `InvR.hw`). -/
theorem InvD.hw (I : InvD G Q NP m0 s ℓ σ D pd H) {a : A} {x : V} {l : L} (h : HwWr s a x l) :
    ∃ ℓ' σ' pd' H', InvD G Q NP m0 (hwCfg s a x) ℓ' σ' D pd' H' := by
  have haD : a ∉ DUn D := by
    rintro ⟨d, hd⟩
    have h1 := I.held hd
    rw [h.own] at h1
    change s.lk l = some d at h1
    rw [h.free] at h1; cases h1
  have hsh : HwWr (shd s σ ℓ) a x l := by
    refine ⟨?_, h.free, ?_, h.ko⟩
    · show s.own σ a = _; rw [I.ownσ]; exact h.own
    · show s.own (Function.update σ a x) = s.own σ
      rw [I.ownσu, h.keep, I.ownσ]
  have hpa : ∀ e ∈ pd, e.2.1 ≠ a := fun e he h' => haD ⟨e.1, h' ▸ I.pdD e he⟩
  refine ⟨ℓ ++ [(Prog.wr a x .done : Prog A V L)], Function.update σ a x, pd, _, ⟨I.r.hw hsh, ?_, I.dloc, ?_, I.pdD, ?_, I.ig, ?_⟩⟩
  · show Function.update s.mem a x = _; rw [apl_upd hpa, I.mem]
  · intro d y hy
    have hya : y ≠ a := fun e => haD ⟨d, e ▸ hy⟩
    rw [Function.update_of_ne hya]; exact I.dG d y hy
  · intro e he; rw [Function.update_of_ne (hpa e he)]; exact I.pdQ e he
  · show ((ℓ ++ [(Prog.wr a x .done : Prog A V L)]) ++ pd.map pwr).Perm (s.log ++ [(Prog.wr a x .done : Prog A V L)])
    exact perm_snoc_mid I.perm

/-- **An A/D write keeps `InvD`**: to a done word it is deferred, to any other it is logged at its time. -/
theorem InvD.ad (hQ : Equivalence Q) (I : InvD G Q NP m0 s ℓ σ D pd H) {x : A} {y : V}
    (h : ADWr G Q NP s x y) : ∃ ℓ' σ' pd' H', InvD G Q NP m0 (hwCfg s x y) ℓ' σ' D pd' H' := by
  by_cases hx : x ∈ DUn D
  · obtain ⟨d, hd⟩ := hx
    refine ⟨ℓ, σ, pd ++ [(d, x, y)], H, ⟨I.r, ?_, I.dloc, I.dG, ?_, ?_, I.ig, ?_⟩⟩
    · show Function.update s.mem x y = apl (pd ++ [(d, x, y)]) σ
      rw [apl_append]
      show _ = Function.update (apl pd σ) x y
      rw [← I.mem]
    · intro e he
      rcases List.mem_append.mp he with he | he
      · exact I.pdD e he
      · rw [List.mem_singleton] at he; subst he; exact hd
    · intro e he
      rcases List.mem_append.mp he with he | he
      · exact I.pdQ e he
      · rw [List.mem_singleton] at he; subst he; exact hQ.trans (I.qmem hQ x) h.q
    · show (ℓ ++ (pd ++ [(d, x, y)]).map pwr).Perm (s.log ++ [(Prog.wr x y .done : Prog A V L)])
      rw [List.map_append, ← List.append_assoc]
      exact I.perm.append_right _
  · have hσx : σ x = s.mem x := I.offDU hx
    have hsh : ADWr (GD G D) Q NP (shd s σ ℓ) x y :=
      ⟨⟨h.g, hx⟩, by show ¬ NP (σ x); rw [hσx]; exact h.np, by show Q (σ x) y; rw [hσx]; exact h.q,
        h.keep, h.ko⟩
    have hpa : ∀ e ∈ pd, e.2.1 ≠ x := fun e he h' => hx ⟨e.1, h' ▸ I.pdD e he⟩
    refine ⟨ℓ ++ [(Prog.wr x y .done : Prog A V L)], Function.update σ x y, pd, _,
      ⟨I.r.ad hQ hsh, ?_, I.dloc, ?_, I.pdD, ?_, I.ig, ?_⟩⟩
    · show Function.update s.mem x y = _; rw [apl_upd hpa, I.mem]
    · intro d z hz
      have hzx : z ≠ x := fun e => hx ⟨d, e ▸ hz⟩
      rw [Function.update_of_ne hzx]; exact I.dG d z hz
    · intro e he; rw [Function.update_of_ne (hpa e he)]; exact I.pdQ e he
    · show ((ℓ ++ [(Prog.wr x y .done : Prog A V L)]) ++ pd.map pwr).Perm (s.log ++ [(Prog.wr x y .done : Prog A V L)])
      exact perm_snoc_mid I.perm

/-- **The word set may change under a closed gate.** -/
theorem InvD.regate (G' : A → Prop) (I : InvD G Q NP m0 s ℓ σ D pd H) (hg : s.gate = .closed) :
    InvD G' Q NP m0 s ℓ σ D pd H := by
  have nl : NoLoc s := I.r.inv.clo hg
  obtain ⟨hD, hpd, _⟩ := I.noLoc nl
  refine ⟨I.r.regate (GD G' D) hg, I.mem, I.dloc, ?_, I.pdD, ?_, ?_, I.perm⟩
  · intro d x hx; rw [hD] at hx; exact absurd hx (Set.notMem_empty _)
  · intro e he; rw [hpd] at he; cases he
  · rintro ⟨d, hd⟩; exact absurd hd (nl d)

end steps

/-! ## Executions -/

/-- **Executions with deferrable A/D writes**: as `ARunR`, a started body `InsAP` with nothing done, and the
owner map after every core step ignoring `G` (`IgnG`). -/
inductive ARunD (Q : V → V → Prop) (NP : V → Prop) (s0 : Cfg A V C L) : Cfg A V C L → (A → Prop) → Prop
  | refl (G : A → Prop) : ARunD Q NP s0 s0 G
  | step {s s' : Cfg A V C L} {c : C} {G : A → Prop} :
      ARunD Q NP s0 s G → Step s c s' → SafeStep s c s' →
      (∀ p0 k W, s.ph c = .loc p0 (.start k) W →
        InsAP G Q NP s.own s.cls s.ko c (fun l => s.lk l = some c) ∅ s.mem k) →
      IgnG G s'.own → ARunD Q NP s0 s' G
  | hw {s : Cfg A V C L} {a : A} {x : V} {l : L} {G : A → Prop} :
      ARunD Q NP s0 s G → HwWr s a x l → ARunD Q NP s0 (hwCfg s a x) G
  | ad {s : Cfg A V C L} {x : A} {y : V} {G : A → Prop} :
      ARunD Q NP s0 s G → ADWr G Q NP s x y → ARunD Q NP s0 (hwCfg s x y) G
  | regate {s : Cfg A V C L} {G : A → Prop} (G' : A → Prop) :
      ARunD Q NP s0 s G → s.gate = .closed → ARunD Q NP s0 s G'

theorem aRunD_inv {Q : V → V → Prop} {NP : V → Prop} (hQ : Equivalence Q) (hQN : ∀ u w, Q u w → (NP u ↔ NP w))
    {s0 s : Cfg A V C L} {G : A → Prop} (h0 : Init s0) (hA0 : ArmInv s0) (h : ARunD Q NP s0 s G) :
    (∃ ℓ σ D pd H, InvD G Q NP s0.mem s ℓ σ D pd H ∧ IInvP G Q NP D s) ∧ SInv s ∧ ArmInv s := by
  induction h with
  | refl G =>
    refine ⟨⟨s0.log, s0.mem, fun _ => ∅, [], s0.mem, ⟨InvR.of_noLoc (inv_init h0) h0.2, rfl, ?_, ?_, ?_, ?_,
      ?_, ?_⟩, ?_⟩, fun d p0 q W hd => absurd (by rw [hd]; trivial) (h0.2 d), hA0⟩
    · intro d x hx; exact absurd hx (Set.notMem_empty _)
    · intro d x hx; exact absurd hx (Set.notMem_empty _)
    · intro e he; cases he
    · intro e he; cases he
    · rintro ⟨d, hd⟩; exact absurd hd (h0.2 d)
    · simp only [List.map_nil, List.append_nil]; exact List.Perm.refl _
    · intro d p0 q W hd; exact absurd (by rw [hd]; trivial) (h0.2 d)
  | @step s s' c G _ hst hok hB hig ih =>
    obtain ⟨⟨ℓ, σ, D, pd, H, I, J⟩, hS, hA⟩ := ih
    have hal := allowed_of_sinv hS c
    have hno : s.gate = .closed → NoLoc s := I.r.inv.clo
    obtain ⟨ℓ', σ', pd', H', I'⟩ := I.step hQ hQN J hal hst hig
    refine ⟨⟨ℓ', σ', _, pd', H', I', iinvP_stepX hno hA (fun p0 k W hph => ?_) J
      (fun d hd => I.d_empty hd) hal hst⟩, sinv_stepX hno hA hok.start hS hal hst, armInv_step hA hst hok⟩
    rcases J c p0 _ W hph with ⟨_, h0⟩ | hS'
    · rw [h0]; exact hB p0 k W hph
    · cases hS'
  | hw _ hh ih =>
    obtain ⟨⟨ℓ, σ, D, pd, H, I, J⟩, hS, hA⟩ := ih
    obtain ⟨ℓ', σ', pd', H', I'⟩ := I.hw hh
    exact ⟨⟨ℓ', σ', D, pd', H', I', iinvP_hw J hh⟩, sinv_hw hS hh, hA⟩
  | ad _ hh ih =>
    obtain ⟨⟨ℓ, σ, D, pd, H, I, J⟩, hS, hA⟩ := ih
    obtain ⟨ℓ', σ', pd', H', I'⟩ := I.ad hQ hh
    exact ⟨⟨ℓ', σ', D, pd', H', I', iinvP_ad J hh⟩, sinv_adP (fun u w h => hQ.symm h) hS J hh, hA⟩
  | @regate s G G' _ hg ih =>
    obtain ⟨⟨ℓ, σ, D, pd, H, I, -⟩, hS, hA⟩ := ih
    exact ⟨⟨ℓ, σ, D, pd, H, I.regate G' hg,
      fun d p0 q W hd => absurd (by change (s.ph d).IsLoc; rw [hd]; trivial) (I.r.inv.clo hg d)⟩, hS, hA⟩

/-- **Every `ARunD` is a serial one, up to moving deferred A/D entries later**: where it reaches a state with no
local path in progress, some permutation `ℓ` of the log runs serially from the initial memory to the memory. -/
theorem serializable_safeD {Q : V → V → Prop} {NP : V → Prop} (hQ : Equivalence Q)
    (hQN : ∀ u w, Q u w → (NP u ↔ NP w)) {s0 s : Cfg A V C L}
    {G : A → Prop} (h0 : Init s0) (hA0 : ArmInv s0) (h : ARunD Q NP s0 s G) (hq : NoLoc s) :
    ∃ ℓ : List (Prog A V L), ℓ.Perm s.log ∧ RunAll ℓ s0.mem s.mem := by
  obtain ⟨⟨ℓ, σ, D, pd, H, I, -⟩, -, -⟩ := aRunD_inv hQ hQN h0 hA0 h
  obtain ⟨-, hpd, hσ⟩ := I.noLoc hq
  have hH : σ = H := funext fun x =>
    I.r.inv.agree x (fun d q0 q U hd => absurd (by change s.ph d = _ at hd; rw [hd]; trivial) (hq d))
  refine ⟨ℓ, ?_, ?_⟩
  · have h1 := I.perm; rw [hpd] at h1; simpa using h1
  · rw [← hσ, hH]; exact I.r.inv.hist

end

end Fl4Proofs.P2.Serial
