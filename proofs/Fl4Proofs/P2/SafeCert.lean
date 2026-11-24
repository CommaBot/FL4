/-
P2: **`Safe` from sequential-run certificates** (step 4 of `SerialSafe`'s
plan, at the level of `Serial.Prog`; the bridge from `PathObl` builds the
certificates).

A body `q` (on core `c` with locks `hs`) is checked against the
*deterministic* sequential run that reads a memory `ν` (`AltRun`): every `rd`
is of a word in `Rp`, every write of a word in `Hp` and passes `WrOK` (`MoveV`
and the class condition) at `ν`; racy reads (`rds`, `rdc`) are allowed only
when `racy`, each word at most once (the set `P` of words already read
racily: `DecOnce`'s form here), `rdc` with its class conditions.

* `safe_of_acc` (accepted runs): if the run from the real memory `σ` passes
  with no racy read, `q` is `Safe` from `σ`.
* `safe_of_dec` (declined runs): if the run from **every** memory `ν`
  admissible for `μ` (`Adm`: equal to `μ` on the words `c` may read,
  of the same class on the class-tracked words) passes, `q` is `Safe` from `μ`.

Both need, at the start, `Rp` words readable and `Hp` words held (`RInv`),
and the ownership map's `Deciders` and `MoveLocal`. The invariant behind
them: along the real interleaving (another core's `Foreign` writes and the
body's own `MoveV` writes), the words `c` may read keep their owners up to
moves between held owners, and those it may not read stay unreadable
(`freach_po`, `write_po`); the real memory and the certificate's memory differ
only on unreadable words, where `moveV_transfer` carries each write's check
over. In the declined case the certificate's memory is the current one with
each racy word at the value it was read (`pick`); a racy read pins its word
(`DInv`).

No premises (everything is a hypothesis of the theorems).
-/
import Fl4Proofs.P2.SerialSafe

namespace Fl4Proofs.P2.Serial

noncomputable section

variable {A V C L : Type} [DecidableEq A] [DecidableEq C] [DecidableEq L]

/-- A write's per-step check at memory `ν`: owner moves and value class. -/
def WrOK (own : (A → V) → A → Owner C L) (cls : A → V → V) (ko : A → ClsOwner C) (c : C)
    (hs : L → Prop) (ν : A → V) (a : A) (v : V) : Prop :=
  MoveV own c hs ν (Function.update ν a v) ∧ (cls a v = cls a (ν a) ∨ ko a = .core c ∨ ko a = .free)

/-- **The deterministic run of `q` reading `ν`** passes: `rd` words in `Rp`,
written words in `Hp` passing `WrOK`, racy reads only if `racy` and each word
(outside `rd`) at most once (`P`: the words already read racily). Bodies take
no locks and have no `start`. -/
def AltRun (own : (A → V) → A → Owner C L) (cls : A → V → V) (ko : A → ClsOwner C) (c : C)
    (hs : L → Prop) (Rp Hp : A → Prop) (racy : Prop) : Set A → Prog A V L → (A → V) → Prop
  | _, .done, _ => True
  | P, .rd a k, ν => Rp a ∧ AltRun own cls ko c hs Rp Hp racy P (k (ν a)) ν
  | P, .rds a k, ν => racy ∧ a ∉ P ∧ AltRun own cls ko c hs Rp Hp racy (insert a P) (k (ν a)) ν
  | P, .rdc a K k, ν => racy ∧ a ∉ P ∧ (ko a = .gate ∨ ko a = .core c) ∧
      (∀ u w, cls a u = cls a w → K u w) ∧
      AltRun own cls ko c hs Rp Hp racy (insert a P) (k (ν a)) ν
  | P, .wr a v k, ν => Hp a ∧ WrOK own cls ko c hs ν a v ∧
      AltRun own cls ko c hs Rp Hp racy P k (Function.update ν a v)
  | _, .lock _ _, _ => False
  | _, .start _, _ => False

/-- `ν` is admissible for the real memory `μ` with pinned racy values `π`:
equal to `μ` where `c` may read, equal to the pins, and of `μ`'s class on
class-tracked words. -/
def Adm (own : (A → V) → A → Owner C L) (cls : A → V → V) (ko : A → ClsOwner C) (c : C)
    (hs : L → Prop) (μ : A → V) (π : A → Option V) (ν : A → V) : Prop :=
  (∀ y, PO c hs (own μ y) → ν y = μ y) ∧ (∀ y u, π y = some u → ν y = u) ∧
    (∀ y, (ko y = .gate ∨ ko y = .core c) → cls y (ν y) = cls y (μ y))

/-- The real memory with each pinned word at its pin. -/
def pick (μ : A → V) (π : A → Option V) : A → V := fun y => (π y).getD (μ y)

variable {own : (A → V) → A → Owner C L} {cls : A → V → V} {ko : A → ClsOwner C} {c : C}
  {hs : L → Prop}

/-! ## The invariant along the real interleaving -/

/-- Along `Foreign` writes: readable words keep owner and value, unreadable
ones stay unreadable, class-tracked words keep their class. -/
theorem freach_po {μ μ' : A → V} (hR : FReach own cls ko c hs μ μ') :
    (∀ x, PO c hs (own μ x) → own μ' x = own μ x ∧ μ' x = μ x) ∧
    (∀ x, PO c hs (own μ' x) → PO c hs (own μ x)) ∧
    (∀ x, (ko x = .gate ∨ ko x = .core c) → cls x (μ' x) = cls x (μ x)) := by
  induction hR with
  | refl => exact ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ h => h, fun _ _ => rfl⟩
  | @step μ μ1 b v hF _ ih =>
    obtain ⟨i1, i2, i3⟩ := ih
    refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
    · obtain ⟨e1, e2⟩ := hF.perm hx
      have hx' : PO c hs (own (Function.update μ b v) x) := by rw [e1]; exact hx
      obtain ⟨f1, f2⟩ := i1 x hx'
      exact ⟨f1.trans e1, f2.trans e2⟩
    · have h1 := i2 x hx
      by_contra hn
      by_cases he : own (Function.update μ b v) x = own μ x
      · rw [he] at h1; exact hn h1
      · exact (hF.2.1 x he).2 h1
    · rw [i3 x hx]
      by_cases hxb : x = b
      · subst hxb
        rw [Function.update_self]
        rcases hF.2.2 with h | ⟨h1, h2⟩
        · exact h
        · rcases hx with h | h
          · exact absurd h h1
          · exact absurd h h2
      · rw [Function.update_of_ne hxb]

/-- Along an own write passing `MoveV`: readable words stay readable, held
ones held, unreadable ones keep their owner. -/
theorem write_po {μ : A → V} {a : A} {v : V}
    (hM : MoveV own c hs μ (Function.update μ a v)) :
    (∀ x, PO c hs (own μ x) → PO c hs (own (Function.update μ a v) x)) ∧
    (∀ x, PO c hs (own (Function.update μ a v) x) → PO c hs (own μ x)) ∧
    (∀ x, HeldV c hs (own μ x) → HeldV c hs (own (Function.update μ a v) x)) ∧
    (∀ x, ¬ PO c hs (own μ x) → own (Function.update μ a v) x = own μ x) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · by_cases he : own (Function.update μ a v) x = own μ x
    · rw [he]; exact hx
    · exact Or.inl (hM x he).2
  · by_cases he : own (Function.update μ a v) x = own μ x
    · rw [← he]; exact hx
    · exact Or.inl (hM x he).1
  · by_cases he : own (Function.update μ a v) x = own μ x
    · rw [he]; exact hx
    · exact (hM x he).2
  · by_contra he
    exact hx (Or.inl (hM x he).1)

/-- `Rp` words readable, `Hp` words held. -/
def RInv (own : (A → V) → A → Owner C L) (c : C) (hs : L → Prop) (Rp Hp : A → Prop)
    (μ : A → V) : Prop :=
  (∀ x, Hp x → HeldV c hs (own μ x)) ∧ (∀ x, Rp x → PO c hs (own μ x))

theorem RInv.freach {Rp Hp : A → Prop} {μ μ' : A → V} (I : RInv own c hs Rp Hp μ)
    (hR : FReach own cls ko c hs μ μ') : RInv own c hs Rp Hp μ' := by
  have h1 := (freach_po hR).1
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rw [(h1 x (Or.inl (I.1 x hx))).1]; exact I.1 x hx
  · rw [(h1 x (I.2 x hx)).1]; exact I.2 x hx

theorem RInv.write {Rp Hp : A → Prop} {μ : A → V} {a : A} {v : V} (I : RInv own c hs Rp Hp μ)
    (hM : MoveV own c hs μ (Function.update μ a v)) :
    RInv own c hs Rp Hp (Function.update μ a v) :=
  ⟨fun x hx => (write_po hM).2.2.1 x (I.1 x hx), fun x hx => (write_po hM).1 x (I.2 x hx)⟩

/-- The certificate's memory differs from the real one only on unreadable words. -/
def Diff (own : (A → V) → A → Owner C L) (c : C) (hs : L → Prop) (μ ν : A → V) : Prop :=
  ∀ y, ν y ≠ μ y → ¬ PO c hs (own μ y)

theorem Diff.freach {μ μ' ν : A → V} (hd : Diff own c hs μ ν)
    (hR : FReach own cls ko c hs μ μ') : Diff own c hs μ' ν := by
  intro y hy hpo
  have hpo0 := (freach_po hR).2.1 y hpo
  have e := ((freach_po hR).1 y hpo0).2
  rw [e] at hy
  exact hd y hy hpo0

theorem Diff.write {μ ν : A → V} {a : A} {v : V} (hd : Diff own c hs μ ν)
    (hM : MoveV own c hs μ (Function.update μ a v)) :
    Diff own c hs (Function.update μ a v) (Function.update ν a v) := by
  intro y hy hpo
  have hya : y ≠ a := by rintro rfl; simp at hy
  rw [Function.update_of_ne hya, Function.update_of_ne hya] at hy
  exact hd y hy ((write_po hM).2.1 y hpo)

/-- A held word's value agrees across `Diff`. -/
theorem Diff.eq_of_po {μ ν : A → V} (hd : Diff own c hs μ ν) {y : A}
    (h : PO c hs (own μ y)) : ν y = μ y := by
  by_contra hne; exact hd y hne h

/-! ## Accepted runs -/

/-- **`Safe` from an accepted run**: the run reading the certificate memory
`σ` (the real memory up to unreadable words) passes with no racy read. -/
theorem safe_of_acc (hD : Deciders own) (hL : MoveLocal own) {Rp Hp : A → Prop}
    (q : Prog A V L) :
    ∀ (P : Set A) (σ μ : A → V), AltRun own cls ko c hs Rp Hp False P q σ →
      Diff own c hs μ σ → RInv own c hs Rp Hp μ → Safe own cls ko c hs μ q := by
  induction q with
  | done => intros; exact .done
  | lock l k _ => intro _ _ _ h; simp only [AltRun] at h
  | start k _ => intro _ _ _ h; simp only [AltRun] at h
  | rds a k _ => intro _ _ _ h; simp only [AltRun, false_and] at h
  | rdc a K k _ => intro _ _ _ h; simp only [AltRun, false_and] at h
  | rd a k ih =>
    intro P σ μ h hd I
    simp only [AltRun] at h
    refine .rd (fun μ' hR => (I.freach hR).2 a h.1) (fun μ' hR => ?_)
    have hd' := hd.freach hR
    have I' := I.freach hR
    have e : σ a = μ' a := hd'.eq_of_po (I'.2 a h.1)
    rw [← e]
    exact ih (σ a) P σ μ' h.2 hd' I'
  | wr a v k ih =>
    intro P σ μ h hd I
    simp only [AltRun] at h
    obtain ⟨hHp, ⟨hM, hcl⟩, hk⟩ := h
    have go : ∀ μ', FReach own cls ko c hs μ μ' →
        HeldV c hs (own μ' a) ∧ MoveV own c hs μ' (Function.update μ' a v) ∧
          (cls a v = cls a (μ' a) ∨ ko a = .core c ∨ ko a = .free) := by
      intro μ' hR
      have hd' := hd.freach hR
      have I' := I.freach hR
      have ha := I'.1 a hHp
      have ea : σ a = μ' a := hd'.eq_of_po (Or.inl ha)
      refine ⟨ha, moveV_transfer hD hL hd' ha hM, ?_⟩
      rw [← ea]; exact hcl
    refine .wr (fun μ' hR => (go μ' hR).1) (fun μ' hR => (go μ' hR).2.1)
      (fun μ' hR => (go μ' hR).2.2) (fun μ' hR => ?_)
    have hM' := (go μ' hR).2.1
    exact ih P (Function.update σ a v) (Function.update μ' a v) hk
      ((hd.freach hR).write hM') ((I.freach hR).write hM')

/-! ## Declined runs -/

/-- The declined-run invariant at real memory `μ` with pins `π` and the racy
words `P` read so far. -/
structure DInv (own : (A → V) → A → Owner C L) (cls : A → V → V) (ko : A → ClsOwner C) (c : C)
    (hs : L → Prop) (Rp Hp : A → Prop) (P : Set A) (q : Prog A V L) (μ : A → V)
    (π : A → Option V) : Prop where
  run : ∀ ν, Adm own cls ko c hs μ π ν → AltRun own cls ko c hs Rp Hp True P q ν
  pin : ∀ y u, π y = some u → y ∈ P
  pinPO : ∀ y u, π y = some u → PO c hs (own μ y) → μ y = u
  pinCls : ∀ y u, π y = some u → (ko y = .gate ∨ ko y = .core c) → cls y u = cls y (μ y)
  rinv : RInv own c hs Rp Hp μ

theorem adm_pick {Rp Hp : A → Prop} {P : Set A} {q : Prog A V L} {μ : A → V}
    {π : A → Option V} (I : DInv own cls ko c hs Rp Hp P q μ π) :
    Adm own cls ko c hs μ π (pick μ π) := by
  refine ⟨fun y hy => ?_, fun y u hu => ?_, fun y hy => ?_⟩
  · unfold pick
    cases hπ : π y with
    | none => rfl
    | some u => exact (I.pinPO y u hπ hy).symm
  · unfold pick; rw [hu]; rfl
  · unfold pick
    cases hπ : π y with
    | none => rfl
    | some u => exact I.pinCls y u hπ hy

theorem pick_diff {Rp Hp : A → Prop} {P : Set A} {q : Prog A V L} {μ : A → V}
    {π : A → Option V} (I : DInv own cls ko c hs Rp Hp P q μ π) :
    Diff own c hs μ (pick μ π) := by
  intro y hy hpo
  exact hy ((adm_pick I).1 y hpo)

theorem DInv.freach {Rp Hp : A → Prop} {P : Set A} {q : Prog A V L} {μ μ' : A → V}
    {π : A → Option V} (I : DInv own cls ko c hs Rp Hp P q μ π)
    (hR : FReach own cls ko c hs μ μ') : DInv own cls ko c hs Rp Hp P q μ' π := by
  obtain ⟨f1, f2, f3⟩ := freach_po hR
  refine ⟨fun ν hν => I.run ν ⟨fun y hy => ?_, hν.2.1, fun y hy => ?_⟩, I.pin,
    fun y u hu hy => ?_, fun y u hu hy => ?_, I.rinv.freach hR⟩
  · rw [hν.1 y ((f1 y hy).1 ▸ hy), (f1 y hy).2]
  · rw [hν.2.2 y hy, f3 y hy]
  · rw [(f1 y (f2 y hy)).2]; exact I.pinPO y u hu (f2 y hy)
  · rw [f3 y hy]; exact I.pinCls y u hu hy

/-- A racy read of `b` at the real memory: pin `b` to the value read. -/
theorem DInv.read {Rp Hp : A → Prop} {P : Set A} {μ : A → V} {π : A → Option V} {b : A}
    {k : V → Prog A V L} {q : Prog A V L}
    (hq : ∀ ν, AltRun own cls ko c hs Rp Hp True P q ν →
      b ∉ P ∧ AltRun own cls ko c hs Rp Hp True (insert b P) (k (ν b)) ν)
    (I : DInv own cls ko c hs Rp Hp P q μ π) :
    DInv own cls ko c hs Rp Hp (insert b P) (k (μ b)) μ (Function.update π b (some (μ b))) := by
  have hbP : b ∉ P := (hq _ (I.run _ (adm_pick I))).1
  have hπb : π b = none := by
    cases h : π b with
    | none => rfl
    | some u => exact absurd (I.pin b u h) hbP
  have ext : ∀ y u, π y = some u → Function.update π b (some (μ b)) y = some u := by
    intro y u hu
    have hyb : y ≠ b := by rintro rfl; rw [hπb] at hu; cases hu
    rw [Function.update_of_ne hyb]; exact hu
  refine ⟨fun ν hν => ?_, fun y u hu => ?_, fun y u hu hy => ?_, fun y u hu hy => ?_, I.rinv⟩
  · have hν0 : Adm own cls ko c hs μ π ν :=
      ⟨hν.1, fun y u hu => hν.2.1 y u (ext y u hu), hν.2.2⟩
    have e : ν b = μ b := hν.2.1 b (μ b) (by rw [Function.update_self])
    have h := (hq ν (I.run ν hν0)).2
    rw [e] at h; exact h
  · by_cases hyb : y = b
    · subst hyb; exact Set.mem_insert _ _
    · rw [Function.update_of_ne hyb] at hu; exact Set.mem_insert_of_mem _ (I.pin y u hu)
  · by_cases hyb : y = b
    · subst hyb; rw [Function.update_self] at hu; exact Option.some.inj hu
    · rw [Function.update_of_ne hyb] at hu; exact I.pinPO y u hu hy
  · by_cases hyb : y = b
    · subst hyb; rw [Function.update_self] at hu; rw [← Option.some.inj hu]
    · rw [Function.update_of_ne hyb] at hu; exact I.pinCls y u hu hy

/-- **`Safe` from a declined run**: the run reading every admissible memory passes. -/
theorem safe_of_dec (hD : Deciders own) (hL : MoveLocal own) {Rp Hp : A → Prop}
    (q : Prog A V L) :
    ∀ (P : Set A) (μ : A → V) (π : A → Option V), DInv own cls ko c hs Rp Hp P q μ π →
      Safe own cls ko c hs μ q := by
  induction q with
  | done => intros; exact .done
  | lock l k _ =>
    intro _ _ _ I; have h := I.run _ (adm_pick I); simp only [AltRun] at h
  | start k _ =>
    intro _ _ _ I; have h := I.run _ (adm_pick I); simp only [AltRun] at h
  | rd a k ih =>
    intro P μ π I
    have hRp : Rp a := by have h := I.run _ (adm_pick I); simp only [AltRun] at h; exact h.1
    refine .rd (fun μ' hR => (I.freach hR).rinv.2 a hRp) (fun μ' hR => ?_)
    have I' := I.freach hR
    have hpo := I'.rinv.2 a hRp
    refine ih (μ' a) P μ' π ⟨fun ν hν => ?_, I'.pin, I'.pinPO, I'.pinCls, I'.rinv⟩
    have h := I'.run ν hν
    simp only [AltRun] at h
    have h := h.2
    rw [hν.1 a hpo] at h; exact h
  | rds b k ih =>
    intro P μ π I
    refine .rds fun μ' hR => ?_
    exact ih _ _ _ _ ((I.freach hR).read (fun ν h => by simp only [AltRun] at h; exact ⟨h.2.1, h.2.2⟩))
  | rdc b K k ih =>
    intro P μ π I
    have h0 := I.run _ (adm_pick I)
    simp only [AltRun] at h0
    refine .rdc h0.2.2.1 h0.2.2.2.1 fun μ' hR => ?_
    exact ih _ _ _ _ ((I.freach hR).read (fun ν h => by simp only [AltRun] at h; exact ⟨h.2.1, h.2.2.2.2⟩))
  | wr a v k ih =>
    intro P μ π I
    have go : ∀ μ', FReach own cls ko c hs μ μ' →
        HeldV c hs (own μ' a) ∧ MoveV own c hs μ' (Function.update μ' a v) ∧
          (cls a v = cls a (μ' a) ∨ ko a = .core c ∨ ko a = .free) := by
      intro μ' hR
      have I' := I.freach hR
      have h0 := I'.run _ (adm_pick I')
      simp only [AltRun] at h0
      obtain ⟨hHp, ⟨hM, hcl⟩, _⟩ := h0
      have ha := I'.rinv.1 a hHp
      have ea : pick μ' π a = μ' a := (pick_diff I').eq_of_po (Or.inl ha)
      refine ⟨ha, moveV_transfer hD hL (pick_diff I') ha hM, ?_⟩
      rw [← ea]; exact hcl
    refine .wr (fun μ' hR => (go μ' hR).1) (fun μ' hR => (go μ' hR).2.1)
      (fun μ' hR => (go μ' hR).2.2) (fun μ' hR => ?_)
    have I' := I.freach hR
    obtain ⟨ha, hM, _⟩ := go μ' hR
    obtain ⟨w1, w2, w3, _⟩ := write_po hM
    have hpoa : PO c hs (own μ' a) := Or.inl ha
    have hpoa' : PO c hs (own (Function.update μ' a v) a) := Or.inl (w3 a ha)
    refine ih P (Function.update μ' a v) (Function.update π a none)
      ⟨fun ν'' hν => ?_, fun y u hu => ?_, fun y u hu hy => ?_, fun y u hu hy => ?_,
        I'.rinv.write hM⟩
    · -- the certificate memory before the write
      let ν := Function.update ν'' a (μ' a)
      have hadm : Adm own cls ko c hs μ' π ν := by
        refine ⟨fun y hy => ?_, fun y u hu => ?_, fun y hy => ?_⟩
        · by_cases hya : y = a
          · subst hya; simp [ν]
          · simp only [ν, Function.update_of_ne hya]
            rw [hν.1 y (w1 y hy), Function.update_of_ne hya]
        · by_cases hya : y = a
          · subst hya; simp only [ν, Function.update_self]; exact I'.pinPO y u hu hpoa
          · simp only [ν, Function.update_of_ne hya]
            exact hν.2.1 y u (by rw [Function.update_of_ne hya]; exact hu)
        · by_cases hya : y = a
          · subst hya; simp [ν]
          · simp only [ν, Function.update_of_ne hya]
            rw [hν.2.2 y hy, Function.update_of_ne hya]
      have h := I'.run ν hadm
      simp only [AltRun] at h
      have h := h.2.2
      have e : Function.update ν a v = ν'' := by
        simp only [ν, Function.update_idem]
        have : ν'' a = v := by rw [hν.1 a hpoa', Function.update_self]
        rw [← this, Function.update_eq_self]
      rw [e] at h; exact h
    · by_cases hya : y = a
      · subst hya; rw [Function.update_self] at hu; cases hu
      · rw [Function.update_of_ne hya] at hu; exact I'.pin y u hu
    · by_cases hya : y = a
      · subst hya; rw [Function.update_self] at hu; cases hu
      · rw [Function.update_of_ne hya] at hu
        rw [Function.update_of_ne hya]; exact I'.pinPO y u hu (w2 y hy)
    · by_cases hya : y = a
      · subst hya; rw [Function.update_self] at hu; cases hu
      · rw [Function.update_of_ne hya] at hu
        rw [Function.update_of_ne hya]; exact I'.pinCls y u hu hy

end

end Fl4Proofs.P2.Serial
