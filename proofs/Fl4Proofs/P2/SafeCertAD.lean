/-
# P2 (line mmuAD, gen 4): **`InsA` from sequential-run certificates that touch no `G` word**

`SerialADR.InsA` asks, at every memory reached by other cores' `Foreign` writes and environment `ADStep`s, that a
read of a `G` word be insensitive. A body whose runs never touch a `G` word satisfies it vacuously, but "never"
must hold at the reached memories, not only at the start. This module derives it, in the way `SafeCert.safe_of_runs`
derives `Safe`, from the deterministic sequential runs on admissible memories:

* `NoGRun G q ν`: the run of `q` reading `ν` reads and writes no `G` word.
* `altRun_congrG`: an `AltRun` (with `NoGRun`) is unchanged when `ν` and the check memory `κ` change on `G` words
  only, given that owners ignore `G` words (`hGo`).
* **`DInvG`** = `SafeCert.DInv` with `NoGRun` in the run certificate and no pin on a `G` word. `DInvG.freach`, **`DInvG.adstep`**
  (an `ADStep` changes only a `G` word: the certificate of the memory before the write, transferred by
  `altRun_congrG`), `DInvG.freachA`, `DInvG.read`.
* **`insA_of_runs`**: `DInvG` at `μ` gives `InsA G Q NP own cls ko c hs μ q`, for any `Q`, `NP` (every `G` clause is
  vacuous: the reads and writes of the run are not `G` words).

No premise: everything is a hypothesis of the theorems.
-/
import Fl4Proofs.P2.SafeCert
import Fl4Proofs.P2.SerialADR

namespace Fl4Proofs.P2.Serial

noncomputable section

variable {A V C L : Type} [DecidableEq A] [DecidableEq C] [DecidableEq L]

/-- The run of `q` reading `ν` touches no `G` word. -/
def NoGRun (G : A → Prop) : Prog A V L → (A → V) → Prop
  | .done, _ => True
  | .rd a k, ν => ¬ G a ∧ NoGRun G (k (ν a)) ν
  | .rds a k, ν => ¬ G a ∧ NoGRun G (k (ν a)) ν
  | .rdc a _ k, ν => ¬ G a ∧ NoGRun G (k (ν a)) ν
  | .wr a v k, ν => ¬ G a ∧ NoGRun G k (Function.update ν a v)
  | .lock _ _, _ => True
  | .start _, _ => True

variable {G : A → Prop} {own : (A → V) → A → Owner C L} {cls : A → V → V} {ko : A → ClsOwner C} {c : C}
  {hs : L → Prop}

theorem agree_upd {m m' : A → V} (h : ∀ x, ¬ G x → m x = m' x) (a : A) (v : V) :
    ∀ x, ¬ G x → Function.update m a v x = Function.update m' a v x := by
  intro x hx
  by_cases hxa : x = a
  · subst hxa; rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hxa, Function.update_of_ne hxa]; exact h x hx

/-- **An `AltRun` touching no `G` word ignores the `G` words of `ν` and `κ`** (owners ignoring them). -/
theorem altRun_congrG (hGo : ∀ m m' : A → V, (∀ x, ¬ G x → m x = m' x) → own m = own m') {Rp Hp : A → Prop}
    (q : Prog A V L) : ∀ (P : Set A) (ν κ ν' κ' : A → V),
      AltRun own cls ko c hs Rp Hp P q ν κ → NoGRun G q ν →
      (∀ x, ¬ G x → ν' x = ν x) → (∀ x, ¬ G x → κ' x = κ x) →
      AltRun own cls ko c hs Rp Hp P q ν' κ' ∧ NoGRun G q ν' := by
  induction q with
  | done => intros; exact ⟨trivial, trivial⟩
  | lock l k _ => intro _ _ _ _ _ h; simp only [AltRun] at h
  | start k _ => intro _ _ _ _ _ h; simp only [AltRun] at h
  | rd a k ih =>
    intro P ν κ ν' κ' h hn hν hκ
    simp only [AltRun, NoGRun] at h hn ⊢
    rw [hν a hn.1]
    obtain ⟨h1, h2⟩ := ih (ν a) P ν κ ν' κ' h.2 hn.2 hν hκ
    exact ⟨⟨h.1, h1⟩, hn.1, h2⟩
  | rds a k ih =>
    intro P ν κ ν' κ' h hn hν hκ
    simp only [AltRun, NoGRun] at h hn ⊢
    rw [hν a hn.1]
    obtain ⟨h1, h2⟩ := ih (ν a) _ ν κ ν' κ' h.2 hn.2 hν hκ
    exact ⟨⟨h.1, h1⟩, hn.1, h2⟩
  | rdc a K k ih =>
    intro P ν κ ν' κ' h hn hν hκ
    simp only [AltRun, NoGRun] at h hn ⊢
    rw [hν a hn.1]
    obtain ⟨h1, h2⟩ := ih (ν a) _ ν κ ν' κ' h.2.2.2 hn.2 hν hκ
    exact ⟨⟨h.1, h.2.1, h.2.2.1, h1⟩, hn.1, h2⟩
  | wr a v k ih =>
    intro P ν κ ν' κ' h hn hν hκ
    simp only [AltRun, NoGRun] at h hn ⊢
    obtain ⟨hHp, ⟨hM, hcl⟩, hk⟩ := h
    have e1 : own κ' = own κ := hGo _ _ hκ
    have e2 : own (Function.update κ' a v) = own (Function.update κ a v) := hGo _ _ (agree_upd hκ a v)
    obtain ⟨h1, h2⟩ := ih P _ _ _ _ hk hn.2 (agree_upd hν a v) (agree_upd hκ a v)
    refine ⟨⟨hHp, ⟨?_, ?_⟩, h1⟩, hn.1, h2⟩
    · intro x hx; rw [e1, e2] at hx ⊢; exact hM x hx
    · rw [hκ a hn.1]; exact hcl

/-- **`SafeCert.DInv` for runs touching no `G` word** (module docstring). -/
structure DInvG (G : A → Prop) (own : (A → V) → A → Owner C L) (cls : A → V → V) (ko : A → ClsOwner C) (c : C)
    (hs : L → Prop) (Rp Hp : A → Prop) (P : Set A) (q : Prog A V L) (μ : A → V)
    (π : A → Option V) : Prop where
  run : ∀ ν, Adm own cls ko c hs μ π ν →
    ∃ κ, Diff own c hs μ κ ∧ AltRun own cls ko c hs Rp Hp P q ν κ ∧ NoGRun G q ν
  pin : ∀ y u, π y = some u → y ∈ P
  pinPO : ∀ y u, π y = some u → PO c hs (own μ y) → μ y = u
  pinCls : ∀ y u, π y = some u → (ko y = .gate ∨ ko y = .core c) → cls y u = cls y (μ y)
  rinv : RInv own c hs Rp Hp μ
  pinG : ∀ y u, π y = some u → ¬ G y

section dinv
variable {Rp Hp : A → Prop} {P : Set A} {q : Prog A V L} {μ : A → V} {π : A → Option V}

theorem DInvG.toDInv (I : DInvG G own cls ko c hs Rp Hp P q μ π) : DInv own cls ko c hs Rp Hp P q μ π :=
  ⟨fun ν hν => (I.run ν hν).imp fun _ h => ⟨h.1, h.2.1⟩, I.pin, I.pinPO, I.pinCls, I.rinv⟩

theorem DInvG.freach {μ' : A → V} (I : DInvG G own cls ko c hs Rp Hp P q μ π)
    (hR : FReach own cls ko c hs μ μ') : DInvG G own cls ko c hs Rp Hp P q μ' π := by
  obtain ⟨f1, f2, f3⟩ := freach_po hR
  have D := I.toDInv.freach hR
  refine ⟨fun ν hν => ?_, D.pin, D.pinPO, D.pinCls, D.rinv, I.pinG⟩
  obtain ⟨κ, hd, h⟩ := I.run ν ⟨fun y hy => by rw [hν.1 y ((f1 y hy).1 ▸ hy), (f1 y hy).2],
    hν.2.1, fun y hy => by rw [hν.2.2 y hy, f3 y hy]⟩
  exact ⟨κ, hd.freach hR, h⟩

/-- **An environment `ADStep` keeps `DInvG`**: it changes a `G` word only, which no certified run touches. -/
theorem DInvG.adstep {Q : V → V → Prop} {NP : V → Prop}
    (hGo : ∀ m m' : A → V, (∀ x, ¬ G x → m x = m' x) → own m = own m') {x : A} {y : V}
    (I : DInvG G own cls ko c hs Rp Hp P q μ π) (hA : ADStep G Q NP own ko μ x y) :
    DInvG G own cls ko c hs Rp Hp P q (Function.update μ x y) π := by
  obtain ⟨hgx, -, -, hkeep, hkox⟩ := hA
  have hpx : ∀ z u, π z = some u → z ≠ x := fun z u hu e => I.pinG z u hu (by rw [e]; exact hgx)
  refine ⟨fun ν hν => ?_, I.pin, fun z u hu hz => ?_, fun z u hu hz => ?_, ?_, I.pinG⟩
  · let ν0 := Function.update ν x (μ x)
    have hadm : Adm own cls ko c hs μ π ν0 := by
      refine ⟨fun z hz => ?_, fun z u hu => ?_, fun z hz => ?_⟩
      · by_cases hzx : z = x
        · subst hzx; simp [ν0]
        · simp only [ν0, Function.update_of_ne hzx]
          rw [hν.1 z (by rw [hkeep]; exact hz), Function.update_of_ne hzx]
      · simp only [ν0, Function.update_of_ne (hpx z u hu)]; exact hν.2.1 z u hu
      · by_cases hzx : z = x
        · subst hzx; rw [hkox] at hz; rcases hz with h | h <;> cases h
        · simp only [ν0, Function.update_of_ne hzx]
          rw [hν.2.2 z hz, Function.update_of_ne hzx]
    obtain ⟨κ, hd, h, hn⟩ := I.run ν0 hadm
    have hνν : ∀ z, ¬ G z → ν z = ν0 z := by
      intro z hz
      have hzx : z ≠ x := fun e => hz (by rw [e]; exact hgx)
      simp only [ν0, Function.update_of_ne hzx]
    have hκκ : ∀ z, ¬ G z → Function.update κ x y z = κ z := by
      intro z hz
      exact Function.update_of_ne (fun e => hz (by rw [e]; exact hgx)) _ _
    obtain ⟨h1, h2⟩ := altRun_congrG hGo q P ν0 κ ν _ h hn hνν hκκ
    refine ⟨_, fun z hz => ?_, h1, h2⟩
    rw [hkeep]
    by_cases hzx : z = x
    · subst hzx; rw [Function.update_self, Function.update_self] at hz; exact absurd rfl hz
    · rw [Function.update_of_ne hzx, Function.update_of_ne hzx] at hz; exact hd z hz
  · rw [hkeep] at hz
    rw [Function.update_of_ne (hpx z u hu)]; exact I.pinPO z u hu hz
  · rw [Function.update_of_ne (hpx z u hu)]; exact I.pinCls z u hu hz
  · have r := I.rinv
    refine ⟨fun z hz => ?_, fun z hz => ?_⟩ <;> rw [hkeep]
    · exact r.1 z hz
    · exact r.2 z hz

theorem DInvG.freachA {Q : V → V → Prop} {NP : V → Prop}
    (hGo : ∀ m m' : A → V, (∀ x, ¬ G x → m x = m' x) → own m = own m') {μ' : A → V}
    (I : DInvG G own cls ko c hs Rp Hp P q μ π) (hR : FReachA G Q NP own cls ko c hs μ μ') :
    DInvG G own cls ko c hs Rp Hp P q μ' π := by
  induction hR with
  | refl => exact I
  | step hF _ ih => exact ih (I.freach (.step hF (.refl _)))
  | ad hA _ ih => exact ih (I.adstep hGo hA)

/-- A racy read of `b` at the real memory: pin `b` to the value read (`SafeCert.DInv.read`). -/
theorem DInvG.read {b : A} {k : V → Prog A V L} (hbG : ¬ G b)
    (hq : ∀ ν κ, AltRun own cls ko c hs Rp Hp P q ν κ →
      b ∉ P ∧ AltRun own cls ko c hs Rp Hp (insert b P) (k (ν b)) ν κ)
    (hqn : ∀ ν, NoGRun G q ν → NoGRun G (k (ν b)) ν)
    (I : DInvG G own cls ko c hs Rp Hp P q μ π) :
    DInvG G own cls ko c hs Rp Hp (insert b P) (k (μ b)) μ (Function.update π b (some (μ b))) := by
  have D := I.toDInv.read hq
  have hbP : b ∉ P := by
    obtain ⟨κ, -, h⟩ := I.toDInv.run _ (adm_pick I.toDInv)
    exact (hq _ _ h).1
  have hπb : π b = none := by
    cases h : π b with
    | none => rfl
    | some u => exact absurd (I.pin b u h) hbP
  have ext : ∀ y u, π y = some u → Function.update π b (some (μ b)) y = some u := by
    intro y u hu
    have hyb : y ≠ b := by rintro rfl; rw [hπb] at hu; cases hu
    rw [Function.update_of_ne hyb]; exact hu
  refine ⟨fun ν hν => ?_, D.pin, D.pinPO, D.pinCls, D.rinv, fun y u hu => ?_⟩
  · have hν0 : Adm own cls ko c hs μ π ν :=
      ⟨hν.1, fun y u hu => hν.2.1 y u (ext y u hu), hν.2.2⟩
    have e : ν b = μ b := hν.2.1 b (μ b) (by rw [Function.update_self])
    obtain ⟨κ, hd, h, hn⟩ := I.run ν hν0
    have h := (hq ν κ h).2
    have hn := hqn ν hn
    rw [e] at h hn; exact ⟨κ, hd, h, hn⟩
  · by_cases hyb : y = b
    · subst hyb; exact hbG
    · rw [Function.update_of_ne hyb] at hu; exact I.pinG y u hu

end dinv

/-- **`InsA` from sequential runs touching no `G` word** (module docstring). -/
theorem insA_of_runs {Q : V → V → Prop} {NP : V → Prop} (hL : MoveHeld own)
    (hGo : ∀ m m' : A → V, (∀ x, ¬ G x → m x = m' x) → own m = own m') {Rp Hp : A → Prop}
    (q : Prog A V L) :
    ∀ (P : Set A) (μ : A → V) (π : A → Option V), DInvG G own cls ko c hs Rp Hp P q μ π →
      InsA G Q NP own cls ko c hs μ q := by
  induction q with
  | done => intros; exact .done
  | lock l k _ =>
    intro _ _ _ I; obtain ⟨κ, -, h, -⟩ := I.run _ (adm_pick I.toDInv); simp only [AltRun] at h
  | start k _ =>
    intro _ _ _ I; obtain ⟨κ, -, h, -⟩ := I.run _ (adm_pick I.toDInv); simp only [AltRun] at h
  | rd a k ih =>
    intro P μ π I
    obtain ⟨κ, -, h0, hn0⟩ := I.run _ (adm_pick I.toDInv)
    simp only [AltRun, NoGRun] at h0 hn0
    have hRp := h0.1
    refine .rd (fun hg => absurd hg hn0.1) (fun μ' hR => ?_)
    have I' := I.freachA hGo hR
    have hpo := I'.rinv.2 a hRp
    refine ih (μ' a) P μ' π ⟨fun ν hν => ?_, I'.pin, I'.pinPO, I'.pinCls, I'.rinv, I'.pinG⟩
    obtain ⟨κ, hd, h, hn⟩ := I'.run ν hν
    simp only [AltRun, NoGRun] at h hn
    have h := h.2
    have hn := hn.2
    rw [hν.1 a hpo] at h hn; exact ⟨κ, hd, h, hn⟩
  | rds b k ih =>
    intro P μ π I
    obtain ⟨κ, -, -, hn0⟩ := I.run _ (adm_pick I.toDInv)
    simp only [NoGRun] at hn0
    refine .rds (fun hg => absurd hg hn0.1) fun μ' hR => ?_
    exact ih _ _ _ _ ((I.freachA hGo hR).read hn0.1 (fun ν κ h => by simp only [AltRun] at h; exact h)
      (fun ν h => by simp only [NoGRun] at h; exact h.2))
  | rdc b K k ih =>
    intro P μ π I
    obtain ⟨κ, -, -, hn0⟩ := I.run _ (adm_pick I.toDInv)
    simp only [NoGRun] at hn0
    refine .rdc (fun hg => absurd hg hn0.1) fun μ' hR => ?_
    exact ih _ _ _ _ ((I.freachA hGo hR).read hn0.1
      (fun ν κ h => by simp only [AltRun] at h; exact ⟨h.1, h.2.2.2⟩)
      (fun ν h => by simp only [NoGRun] at h; exact h.2))
  | wr a v k ih =>
    intro P μ π I
    obtain ⟨κ0, -, -, hn0⟩ := I.run _ (adm_pick I.toDInv)
    simp only [NoGRun] at hn0
    refine .wr (fun hg => absurd hg hn0.1) (fun μ' hR => ?_)
    have I' := I.freachA hGo hR
    obtain ⟨κ, hd, h0, -⟩ := I'.run _ (adm_pick I'.toDInv)
    simp only [AltRun] at h0
    obtain ⟨hHp, ⟨hM0, -⟩, _⟩ := h0
    have ha := I'.rinv.1 a hHp
    have hM := moveV_transfer hL hd ha hM0
    obtain ⟨w1, w2, w3, _⟩ := write_po hM
    have hpoa : PO c hs (own μ' a) := Or.inl ha
    have hpoa' : PO c hs (own (Function.update μ' a v) a) := Or.inl (w3 a ha)
    refine ih P (Function.update μ' a v) (Function.update π a none)
      ⟨fun ν'' hν => ?_, fun y u hu => ?_, fun y u hu hy => ?_, fun y u hu hy => ?_,
        I'.rinv.write hM, fun y u hu => ?_⟩
    · let ν := Function.update ν'' a (μ' a)
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
      obtain ⟨κ1, hd1, h, hn⟩ := I'.run ν hadm
      simp only [AltRun, NoGRun] at h hn
      have h := h.2.2
      have hn := hn.2
      have e : Function.update ν a v = ν'' := by
        simp only [ν, Function.update_idem]
        have : ν'' a = v := by rw [hν.1 a hpoa', Function.update_self]
        rw [← this, Function.update_eq_self]
      rw [e] at h hn; exact ⟨_, hd1.write hM, h, hn⟩
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
    · by_cases hya : y = a
      · subst hya; rw [Function.update_self] at hu; cases hu
      · rw [Function.update_of_ne hya] at hu; exact I'.pinG y u hu

end

end Fl4Proofs.P2.Serial
