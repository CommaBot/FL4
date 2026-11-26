/-
# P2 (line mmuAD, gen 9): **the masked bridge with a done set** — `InsAP` from sequential runs

`SafeCertADQ` with `SerialADP`'s done set: a run may store a present (non-`NP`) value into a `G` word, which
joins the done set `D`; a done word is never stored again (PageMap's leaf). Statements are `SafeCertADQ`'s with
`InsRun` → `InsRunP D`, `DInvQ` → `DInvQP D`, `InsA` → `InsAP D`:

* `InsRunP G Q NP D q ν` (reads as `InsRun`; a store `a := v` needs `a ∉ D` and continues at `dU G NP D a v`).
* `altRun_congrQP`, `DInvQP` (+ `toDInv` / `freach` / `adstep` / `freachA` / `read`), **`insAP_of_runsQP`**:
  `DInvQP D` at `μ` gives `InsAP G Q NP own cls ko c hs D μ q` (`Q` an equivalence, `G` words class-free).

No premise. New module; no existing statement changed.
-/
import Fl4Proofs.P2.SafeCertADQ
import Fl4Proofs.P2.SerialADP

namespace Fl4Proofs.P2.Serial

noncomputable section
open Classical

variable {A V C L : Type} [DecidableEq A] [DecidableEq C] [DecidableEq L]

/-- The run of `q` reading `ν` reads `G` words only `Q`-insensitively (by `rd`); a store needs its word outside
the done set `D` and continues at `dU G NP D a v`. -/
def InsRunP (G : A → Prop) (Q : V → V → Prop) (NP : V → Prop) : Set A → Prog A V L → (A → V) → Prop
  | _, .done, _ => True
  | D, .rd a k, ν => (G a → ∀ u, Q u (ν a) → k u = k (ν a)) ∧ InsRunP G Q NP D (k (ν a)) ν
  | D, .rds a k, ν => ¬ G a ∧ InsRunP G Q NP D (k (ν a)) ν
  | D, .rdc a _ k, ν => ¬ G a ∧ InsRunP G Q NP D (k (ν a)) ν
  | D, .wr a v k, ν => a ∉ D ∧ InsRunP G Q NP (dU G NP D a v) k (Function.update ν a v)
  | _, .lock _ _, _ => True
  | _, .start _, _ => True

variable {G : A → Prop} {Q : V → V → Prop} {NP : V → Prop} {own : (A → V) → A → Owner C L} {cls : A → V → V}
  {ko : A → ClsOwner C} {c : C} {hs : L → Prop}

/-- **An `AltRun` reading `G` words insensitively ignores `Q`-changes of them** (SafeCertADQ's, with the done set). -/
theorem altRun_congrQP (hQ : Equivalence Q)
    (hGo : ∀ m m' : A → V, (∀ x, ¬ G x → m x = m' x) → own m = own m') (hGko : ∀ x, G x → ko x = .free)
    {Rp Hp : A → Prop} (q : Prog A V L) : ∀ (D P : Set A) (ν κ ν' κ' : A → V),
      AltRun own cls ko c hs Rp Hp P q ν κ → InsRunP G Q NP D q ν →
      (∀ x, ¬ G x → ν' x = ν x) → (∀ x, G x → Rp x → Q (ν' x) (ν x)) → (∀ x, ¬ G x → κ' x = κ x) →
      AltRun own cls ko c hs Rp Hp P q ν' κ' ∧ InsRunP G Q NP D q ν' := by
  induction q with
  | done => intros; exact ⟨trivial, trivial⟩
  | lock l k _ => intro _ _ _ _ _ _ h; simp only [AltRun] at h
  | start k _ => intro _ _ _ _ _ _ h; simp only [AltRun] at h
  | rd a k ih =>
    intro D P ν κ ν' κ' h hn hν hνQ hκ
    simp only [AltRun, InsRunP] at h hn ⊢
    have e : k (ν' a) = k (ν a) := by
      by_cases hg : G a
      · exact hn.1 hg _ (hνQ a hg h.1)
      · rw [hν a hg]
    rw [e]
    obtain ⟨h1, h2⟩ := ih (ν a) D P ν κ ν' κ' h.2 hn.2 hν hνQ hκ
    refine ⟨⟨h.1, h1⟩, fun hg u hu => ?_, h2⟩
    exact hn.1 hg u (hQ.trans hu (hνQ a hg h.1))
  | rds a k ih =>
    intro D P ν κ ν' κ' h hn hν hνQ hκ
    simp only [AltRun, InsRunP] at h hn ⊢
    rw [hν a hn.1]
    obtain ⟨h1, h2⟩ := ih (ν a) D _ ν κ ν' κ' h.2 hn.2 hν hνQ hκ
    exact ⟨⟨h.1, h1⟩, hn.1, h2⟩
  | rdc a K k ih =>
    intro D P ν κ ν' κ' h hn hν hνQ hκ
    simp only [AltRun, InsRunP] at h hn ⊢
    rw [hν a hn.1]
    obtain ⟨h1, h2⟩ := ih (ν a) D _ ν κ ν' κ' h.2.2.2 hn.2 hν hνQ hκ
    exact ⟨⟨h.1, h.2.1, h.2.2.1, h1⟩, hn.1, h2⟩
  | wr a v k ih =>
    intro D P ν κ ν' κ' h hn hν hνQ hκ
    simp only [AltRun, InsRunP] at h hn ⊢
    obtain ⟨hHp, ⟨hM, hcl⟩, hk⟩ := h
    have e1 : own κ' = own κ := hGo _ _ hκ
    have e2 : own (Function.update κ' a v) = own (Function.update κ a v) := hGo _ _ (agree_upd hκ a v)
    obtain ⟨h1, h2⟩ := ih _ P _ _ _ _ hk hn.2 (agree_upd hν a v) (agreeQ_upd hQ hνQ a v) (agree_upd hκ a v)
    refine ⟨⟨hHp, ⟨?_, ?_⟩, h1⟩, hn.1, h2⟩
    · intro x hx; rw [e1, e2] at hx ⊢; exact hM x hx
    · by_cases hg : G a
      · exact Or.inr (Or.inr (hGko a hg))
      · rw [hκ a hg]; exact hcl

/-- **`SafeCert.DInv` for runs reading `G` words insensitively** (SafeCertADQ's, with the done set). -/
structure DInvQP (G : A → Prop) (Q : V → V → Prop) (NP : V → Prop) (D : Set A) (own : (A → V) → A → Owner C L)
    (cls : A → V → V) (ko : A → ClsOwner C) (c : C)
    (hs : L → Prop) (Rp Hp : A → Prop) (P : Set A) (q : Prog A V L) (μ : A → V)
    (π : A → Option V) : Prop where
  run : ∀ ν, Adm own cls ko c hs μ π ν →
    ∃ κ, Diff own c hs μ κ ∧ AltRun own cls ko c hs Rp Hp P q ν κ ∧ InsRunP G Q NP D q ν
  pin : ∀ y u, π y = some u → y ∈ P
  pinPO : ∀ y u, π y = some u → PO c hs (own μ y) → μ y = u
  pinCls : ∀ y u, π y = some u → (ko y = .gate ∨ ko y = .core c) → cls y u = cls y (μ y)
  rinv : RInv own c hs Rp Hp μ
  pinG : ∀ y u, π y = some u → ¬ G y

section dinv
variable {Rp Hp : A → Prop} {P : Set A} {q : Prog A V L} {μ : A → V} {π : A → Option V} {D : Set A}

theorem DInvQP.toDInv (I : DInvQP G Q NP D own cls ko c hs Rp Hp P q μ π) : DInv own cls ko c hs Rp Hp P q μ π :=
  ⟨fun ν hν => (I.run ν hν).imp fun _ h => ⟨h.1, h.2.1⟩, I.pin, I.pinPO, I.pinCls, I.rinv⟩

theorem DInvQP.freach {μ' : A → V} (I : DInvQP G Q NP D own cls ko c hs Rp Hp P q μ π)
    (hR : FReach own cls ko c hs μ μ') : DInvQP G Q NP D own cls ko c hs Rp Hp P q μ' π := by
  obtain ⟨f1, f2, f3⟩ := freach_po hR
  have D := I.toDInv.freach hR
  refine ⟨fun ν hν => ?_, D.pin, D.pinPO, D.pinCls, D.rinv, I.pinG⟩
  obtain ⟨κ, hd, h⟩ := I.run ν ⟨fun y hy => by rw [hν.1 y ((f1 y hy).1 ▸ hy), (f1 y hy).2],
    hν.2.1, fun y hy => by rw [hν.2.2 y hy, f3 y hy]⟩
  exact ⟨κ, hd.freach hR, h⟩

/-- **An environment `ADStep` keeps `DInvQP`** (SafeCertADQ's, with the done set). -/
theorem DInvQP.adstep (hQ : Equivalence Q)
    (hGo : ∀ m m' : A → V, (∀ x, ¬ G x → m x = m' x) → own m = own m') (hGko : ∀ x, G x → ko x = .free)
    {x : A} {y : V}
    (I : DInvQP G Q NP D own cls ko c hs Rp Hp P q μ π) (hA : ADStep G Q NP own ko μ x y) :
    DInvQP G Q NP D own cls ko c hs Rp Hp P q (Function.update μ x y) π := by
  obtain ⟨hgx, -, hqx, hkeep, hkox⟩ := hA
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
    have hνQ : ∀ z, G z → Rp z → Q (ν z) (ν0 z) := by
      intro z _ hr
      by_cases hzx : z = x
      · subst hzx
        simp only [ν0, Function.update_self]
        have hpo : PO c hs (own (Function.update μ z y) z) := by rw [hkeep]; exact I.rinv.2 z hr
        rw [hν.1 z hpo, Function.update_self]
        exact hQ.symm hqx
      · simp only [ν0, Function.update_of_ne hzx]; exact hQ.refl _
    have hκκ : ∀ z, ¬ G z → Function.update κ x y z = κ z := by
      intro z hz
      exact Function.update_of_ne (fun e => hz (by rw [e]; exact hgx)) _ _
    obtain ⟨h1, h2⟩ := altRun_congrQP hQ hGo hGko q D P ν0 κ ν _ h hn hνν hνQ hκκ
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

theorem DInvQP.freachA (hQ : Equivalence Q)
    (hGo : ∀ m m' : A → V, (∀ x, ¬ G x → m x = m' x) → own m = own m') (hGko : ∀ x, G x → ko x = .free)
    {μ' : A → V}
    (I : DInvQP G Q NP D own cls ko c hs Rp Hp P q μ π) (hR : FReachA G Q NP own cls ko c hs μ μ') :
    DInvQP G Q NP D own cls ko c hs Rp Hp P q μ' π := by
  induction hR with
  | refl => exact I
  | step hF _ ih => exact ih (I.freach (.step hF (.refl _)))
  | ad hA _ ih => exact ih (I.adstep hQ hGo hGko hA)

/-- A racy read of a non-`G` word `b` at the real memory: pin `b` to the value read. -/
theorem DInvQP.read {b : A} {k : V → Prog A V L} (hbG : ¬ G b)
    (hq : ∀ ν κ, AltRun own cls ko c hs Rp Hp P q ν κ →
      b ∉ P ∧ AltRun own cls ko c hs Rp Hp (insert b P) (k (ν b)) ν κ)
    (hqn : ∀ ν, InsRunP G Q NP D q ν → InsRunP G Q NP D (k (ν b)) ν)
    (I : DInvQP G Q NP D own cls ko c hs Rp Hp P q μ π) :
    DInvQP G Q NP D own cls ko c hs Rp Hp (insert b P) (k (μ b)) μ (Function.update π b (some (μ b))) := by
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

/-- **`InsA` from sequential runs reading `G` words insensitively** (SafeCertADQ's, with the done set). -/
theorem insAP_of_runsQP (hQ : Equivalence Q) (hL : MoveHeld own)
    (hGo : ∀ m m' : A → V, (∀ x, ¬ G x → m x = m' x) → own m = own m') (hGko : ∀ x, G x → ko x = .free)
    {Rp Hp : A → Prop} (q : Prog A V L) :
    ∀ (D P : Set A) (μ : A → V) (π : A → Option V), DInvQP G Q NP D own cls ko c hs Rp Hp P q μ π →
      InsAP G Q NP own cls ko c hs D μ q := by
  induction q with
  | done => intros; exact .done
  | lock l k _ =>
    intro _ _ _ _ I; obtain ⟨κ, -, h, -⟩ := I.run _ (adm_pick I.toDInv); simp only [AltRun] at h
  | start k _ =>
    intro _ _ _ _ I; obtain ⟨κ, -, h, -⟩ := I.run _ (adm_pick I.toDInv); simp only [AltRun] at h
  | rd a k ih =>
    intro D P μ π I
    obtain ⟨κ, -, h0, -⟩ := I.run _ (adm_pick I.toDInv)
    simp only [AltRun] at h0
    have hRp := h0.1
    refine .rd (fun hg μ' hR u hu => ?_) (fun μ' hR => ?_)
    · have I' := I.freachA hQ hGo hGko hR
      obtain ⟨κ, -, -, hn⟩ := I'.run _ (adm_pick I'.toDInv)
      simp only [InsRunP] at hn
      have e : pick μ' π a = μ' a := (adm_pick I'.toDInv).1 a (I'.rinv.2 a hRp)
      rw [e] at hn
      exact hn.1 hg u hu
    have I' := I.freachA hQ hGo hGko hR
    have hpo := I'.rinv.2 a hRp
    refine ih (μ' a) D P μ' π ⟨fun ν hν => ?_, I'.pin, I'.pinPO, I'.pinCls, I'.rinv, I'.pinG⟩
    obtain ⟨κ, hd, h, hn⟩ := I'.run ν hν
    simp only [AltRun, InsRunP] at h hn
    have h := h.2
    have hn := hn.2
    rw [hν.1 a hpo] at h hn; exact ⟨κ, hd, h, hn⟩
  | rds b k ih =>
    intro D P μ π I
    obtain ⟨κ, -, -, hn0⟩ := I.run _ (adm_pick I.toDInv)
    simp only [InsRunP] at hn0
    refine .rds (fun hg => absurd hg hn0.1) fun μ' hR => ?_
    exact ih _ _ _ _ _ ((I.freachA hQ hGo hGko hR).read hn0.1
      (fun ν κ h => by simp only [AltRun] at h; exact h)
      (fun ν h => by simp only [InsRunP] at h; exact h.2))
  | rdc b K k ih =>
    intro D P μ π I
    obtain ⟨κ, -, -, hn0⟩ := I.run _ (adm_pick I.toDInv)
    simp only [InsRunP] at hn0
    refine .rdc (fun hg => absurd hg hn0.1) fun μ' hR => ?_
    exact ih _ _ _ _ _ ((I.freachA hQ hGo hGko hR).read hn0.1
      (fun ν κ h => by simp only [AltRun] at h; exact ⟨h.1, h.2.2.2⟩)
      (fun ν h => by simp only [InsRunP] at h; exact h.2))
  | wr a v k ih =>
    intro D P μ π I
    obtain ⟨κ0, -, -, hn0⟩ := I.run _ (adm_pick I.toDInv)
    simp only [InsRunP] at hn0
    refine .wr hn0.1 (fun hg _ => hGko a hg) (fun μ' hR => ?_)
    have I' := I.freachA hQ hGo hGko hR
    obtain ⟨κ, hd, h0, -⟩ := I'.run _ (adm_pick I'.toDInv)
    simp only [AltRun] at h0
    obtain ⟨hHp, ⟨hM0, -⟩, _⟩ := h0
    have ha := I'.rinv.1 a hHp
    have hM := moveV_transfer hL hd ha hM0
    obtain ⟨w1, w2, w3, _⟩ := write_po hM
    have hpoa : PO c hs (own μ' a) := Or.inl ha
    have hpoa' : PO c hs (own (Function.update μ' a v) a) := Or.inl (w3 a ha)
    refine ih (dU G NP D a v) P (Function.update μ' a v) (Function.update π a none)
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
      simp only [AltRun, InsRunP] at h hn
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
