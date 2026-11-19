/-
P3 (DESIGN.md §9), untyped: **the typed heap grown by a retype** (`ThX`:
the window's new CNodes or TCBs), for the no-reset retype of CNodes and
TCBs at `J` (handoff/utj.md "uttypes (line ut24-)").

An object of the grown heap `th'` is one of `th`'s or lies in the window
`[A, A + w * k)` (`ThX.cases`), and `th`'s objects stay (`ThX.mono`). So a
placement fact about `th'` (a word outside its objects, not a slot word, an
IPC or SC word apart from its slots) follows from `th`'s and the word
outside the window: `VObj.thX`, `IsSlot.thX`, `SlotW.thX`, and from these
`TopPlaced.grow`, `IpcApart.grow`, `ScApart.grow`, `CurOK.grow`.
-/
import Fl4Proofs.P3.UtPmRet
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section Grow
variable {th th' : TypedHeap} {A k w n us : Nat}

/-- **An object of the grown heap** is one of `th`'s or a new one inside
the window. -/
theorem ThX.cases (hT : ThX th th' A k w n us) (hks : ∀ kd, thKindN n us = some kd → objSize kd ≤ k)
    {q : U64} {kd : ObjKind} (h : th' q = some kd) :
    th q = some kd ∨ (A ≤ q.val ∧ q.val + objSize kd ≤ A + w * k ∧ thKindN n us = some kd) := by
  rw [hT.1 q] at h
  split_ifs at h with hc
  · obtain ⟨⟨i, hi, hq⟩, -⟩ := hc
    have hsz := hks kd h
    have : (i + 1) * k ≤ w * k := Nat.mul_le_mul_right _ hi
    rw [Nat.add_mul, Nat.one_mul] at this
    exact Or.inr ⟨by omega, by omega, h⟩
  · exact Or.inl h

/-- **`th`'s objects stay** (the window is free in `th`; its objects have a
positive size). -/
theorem ThX.mono (hT : ThX th th' A k w n us) (hk : 0 < k) (hpos : ∀ q kd, th q = some kd → 0 < objSize kd)
    {q : U64} {kd : ObjKind} (h : th q = some kd) : th' q = some kd := by
  rw [hT.1 q]
  split_ifs with hc
  · exfalso
    obtain ⟨⟨i, hi, hq⟩, -⟩ := hc
    have h0 := hpos q kd h
    have hik : i * k < w * k := Nat.mul_lt_mul_of_pos_right hi hk
    rcases hT.2 q kd h with e | e <;> omega
  · exact h

theorem IsSlot.thMono (hT : ThX th th' A k w n us) (hk : 0 < k) (hpos : ∀ q kd, th q = some kd → 0 < objSize kd)
    {x : U64} (h : IsSlot th x) : IsSlot th' x := by
  obtain ⟨p, i, hi, rfl⟩ := h
  refine ⟨p, i, ?_, rfl⟩
  rcases hi with ⟨r, hp, hr⟩ | ⟨hp, ht⟩
  · exact Or.inl ⟨r, hT.mono hk hpos hp, hr⟩
  · exact Or.inr ⟨hT.mono hk hpos hp, ht⟩

/-- **A slot of the grown heap** is one of `th`'s or lies in the window. -/
theorem IsSlot.thX (hT : ThX th th' A k w n us) (hks : ∀ kd, thKindN n us = some kd → objSize kd ≤ k)
    (hP' : Placed th') {x : U64} (h : IsSlot th' x) :
    IsSlot th x ∨ (A ≤ x.val ∧ x.val + 32 ≤ A + w * k) := by
  obtain ⟨p, i, hi, rfl⟩ := h
  have hv := hi.val hP'
  obtain ⟨kd, hkd, hsz⟩ := hi.size
  rcases hT.cases hks hkd with ho | ⟨h1, h2, -⟩
  · left
    refine ⟨p, i, ?_, rfl⟩
    rcases hi with ⟨r, hp, hr⟩ | ⟨hp, ht⟩
    · rw [hp] at hkd; cases hkd; exact Or.inl ⟨r, ho, hr⟩
    · rw [hp] at hkd; cases hkd; exact Or.inr ⟨ho, ht⟩
  · right; rw [hv]; constructor <;> omega

/-- **A `VObj` word of the grown heap** is one of `th`'s or in the window. -/
theorem VObj.thX (hT : ThX th th' A k w n us) (hks : ∀ kd, thKindN n us = some kd → objSize kd ≤ k)
    {P L4 L3 L2 L1 : Set U64} {kb b : U64} (h : VObj th' P L4 L3 L2 L1 kb b) :
    VObj th P L4 L3 L2 L1 kb b ∨ (A ≤ b.val ∧ b.val < A + w * k) := by
  rcases h with ⟨q, r, hq, h1, h2⟩ | ⟨t, ht, h1, h2⟩ | h | h
  · rcases hT.cases hks hq with ho | ⟨g1, g2, -⟩
    · exact Or.inl (Or.inl ⟨q, r, ho, h1, h2⟩)
    · simp only [objSize] at g2; right; constructor <;> omega
  · rcases hT.cases hks ht with ho | ⟨g1, g2, -⟩
    · exact Or.inl (Or.inr (Or.inl ⟨t, ho, h1, h2⟩))
    · simp only [objSize] at g2; right; constructor <;> omega
  · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr h)))

/-- A word outside `th`'s objects and the window is outside `th'`'s. -/
theorem OutsideObjects.grow (hT : ThX th th' A k w n us) (hks : ∀ kd, thKindN n us = some kd → objSize kd ≤ k)
    {b : U64} (h : OutsideObjects th b) (hb : ¬ (A ≤ b.val ∧ b.val < A + w * k)) : OutsideObjects th' b := by
  refine ⟨h.1, fun q kd hq hin => ?_⟩
  rcases hT.cases hks hq with ho | ⟨g1, g2, -⟩
  · exact h.2 q kd ho hin
  · exact hb ⟨by omega, by omega⟩

/-- **A slot word of the grown heap** is one of `th`'s or in the window
(the window within the address space). -/
theorem SlotW.thX (hT : ThX th th' A k w n us) (hks : ∀ kd, thKindN n us = some kd → objSize kd ≤ k)
    (hP' : Placed th') {b : U64} (h : SlotW th' b) :
    SlotW th b ∨ (A ≤ b.val ∧ b.val < A + w * k) := by
  obtain ⟨x, hx, hb⟩ := h
  have hfit := hx.fit hP'
  rcases IsSlot.thX hT hks hP' hx with ho | ⟨g1, g2⟩
  · exact Or.inl ⟨x, ho, hb⟩
  · right
    rcases hb with rfl | rfl
    · constructor <;> omega
    · rw [wa8_val (by omega)]; constructor <;> omega

end Grow

section Place
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {th th' : TypedHeap} {A k w n us : Nat}
variable {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- **`TopPlaced` at the grown heap**: the window's words are none the
relations read (`¬ OObj`), none of the VSpace's or `th`'s objects
(`¬ VObj`), and miss the kernel-state block. -/
theorem TopPlaced.grow {s : S} {σ : Fl4Spec.State Unit}
    (hP : TopPlaced st th P L4 L3 L2 L1 N T C E R B c s σ) (hT : ThX th th' A k w n us)
    (hks : ∀ kd, thKindN n us = some kd → objSize kd ≤ k) (hP' : Placed th')
    (hWo : ∀ b : U64, A ≤ b.val → b.val < A + w * k → ¬ OObj st N T C E R B c s σ b)
    (hWv : ∀ b : U64, A ≤ b.val → b.val < A + w * k → ¬ VObj th P L4 L3 L2 L1 (L.ksb s) b)
    (hWk : A + w * k ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ A) :
    TopPlaced st th' P L4 L3 L2 L1 N T C E R B c s σ := by
  have hPtW : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ (A ≤ b.val ∧ b.val < A + w * k) := by
    rintro b ⟨q, hq, i, hi, rfl⟩ ⟨g1, g2⟩
    exact hWv _ g1 g2 (table_vobj hP.pt hq hi _)
  have hVsW : ∀ b, VsWrite P (L.ksb s) b → ¬ (A ≤ b.val ∧ b.val < A + w * k) := by
    rintro b hb ⟨g1, g2⟩
    exact hWv _ g1 g2 (vsWrite_vobj hP.vs hb)
  refine ⟨hP.ep, hP.vs, hP.pt, hP', fun a ha hv => ?_, hP.nodeE, fun b hb => ?_, fun b hb hs => ?_, hP.pv,
    fun b hb => ?_, fun b hb hs => ?_, fun t ht => ?_⟩
  · rcases VObj.thX hT hks hv with h | ⟨g1, g2⟩
    · exact hP.disj a ha h
    · exact hWo a g1 g2 ha
  · exact OutsideObjects.grow hT hks (hP.po b hb) (hPtW b hb)
  · rcases SlotW.thX hT hks hP' hs with h | h
    · exact hP.ps b hb h
    · exact hPtW b hb h
  · exact OutsideObjects.grow hT hks (hP.vo b hb) (hVsW b hb)
  · rcases SlotW.thX hT hks hP' hs with h | h
    · exact hP.sd b hb h
    · exact hVsW b hb h
  · rcases hT.cases hks ht with h | ⟨g1, g2, -⟩
    · exact hP.tko t h
    · simp only [objSize] at g2; omega

/-- **`IpcApart` at the grown heap**: the IPC words are relation words
(`OObj`), so none lies in the window; the core's node and the
kernel-state block miss it. -/
theorem IpcApart.grow {s : S} {σ : Fl4Spec.State Unit} (h : IpcApart th N T E R B (L.ksb s) c)
    (hT : ThX th th' A k w n us) (hks : ∀ kd, thKindN n us = some kd → objSize kd ≤ k) (hP' : Placed th')
    (hWo : ∀ b : U64, A ≤ b.val → b.val < A + w * k → ¬ OObj st N T C E R B c s σ b)
    (hWk : A + w * k ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ A) :
    IpcApart th' N T E R B (L.ksb s) c := by
  refine ⟨fun a ha x hx hin => ?_, fun a h1 h2 x hx hin => ?_, h.dom, fun a h1 h2 h0 x hx hin => ?_, h.kfit, h.kal⟩
  · rcases IsSlot.thX hT hks hP' hx with ho | ⟨g1, g2⟩
    · exact h.slot a ha x ho hin
    · refine hWo a (by omega) (by omega) ?_
      rcases ha with h | h | h | ⟨n, hn, h1, h2⟩ | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, h1, by omega⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
  · rcases IsSlot.thX hT hks hP' hx with ho | ⟨g1, g2⟩
    · exact h.node a h1 h2 x ho hin
    · refine hWo a (by omega) (by omega) (Or.inl ?_)
      simp only [P1.LawfulStore.nodeBase]; constructor <;> omega
  · rcases IsSlot.thX hT hks hP' hx with ho | ⟨g1, g2⟩
    · exact h.ks a h1 h2 h0 x ho hin
    · omega

/-- **`ScApart` at the grown heap**: an SC word is a relation word. -/
theorem ScApart.grow {s : S} {σ : Fl4Spec.State Unit} (h : ScApart th C σ)
    (hT : ThX th th' A k w n us) (hks : ∀ kd, thKindN n us = some kd → objSize kd ≤ k) (hP' : Placed th')
    (hWo : ∀ b : U64, A ≤ b.val → b.val < A + w * k → ¬ OObj st N T C E R B c s σ b) :
    ScApart th' C σ := by
  intro sc hsc x m hk a ha y hy hin
  rcases IsSlot.thX hT hks hP' hy with ho | ⟨g1, g2⟩
  · exact h sc hsc x m hk a ha y ho hin
  · exact hWo a (by omega) (by omega)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨sc, hsc, x, m, hk, ha⟩)))))))

/-- **`CurOK` at the grown heap** (the current TCB stays). -/
theorem CurOK.grow {s : S} {σ : Fl4Spec.State Unit} (h : CurOK st th s σ) (hT : ThX th th' A k w n us)
    (hk : 0 < k) (hpos : ∀ q kd, th q = some kd → 0 < objSize kd) : CurOK st th' s σ := by
  obtain ⟨t, h1, h2, h3⟩ := h
  exact ⟨t, h1, hT.mono hk hpos h2, h3⟩

end Place

end

end Fl4Proofs.P3
