/-
P2 (line glue, gen 1): **a started body is `Safe` from the history** (`body_safeH`, `LocalPath.safeH`).

`E2E.body_safe` with the store state linked to a memory `ρ` (Serial's serial-prefix memory, `SerialH`) rather
than to the physical memory `μ` at which `Safe` is asked, given `VEq ρ μ` (what the core may read agrees between
the two, in owner, value and class). The proof is `body_safe`'s: the permissions `PathObl` gives at `own ρ` carry to
`own μ` by `VEq`'s first clause; the accepted run's check memory is `ρ` on kernel words (`μ` elsewhere), which
differs from `μ` only on words the core may not read (second clause); the declined run's class conditions carry by
the third. No premise.
-/
import Fl4Proofs.P2.E2E
import Fl4Proofs.P2.SerialH
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2E
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.Serial (Owner ClsOwner Prog HeldV PO MoveV Safe MoveHeld AltRun Adm
  Diff RInv WrOK VEq)

noncomputable section
open Classical

section body
variable {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
  {ko : U64 → ClsOwner U64} {User : U64 → Prop}
  {S A X : Type} {st : machine.Store S} [L : LawfulStore st] {ar : machine.Arch A}
  {F : ∀ {A : Type}, machine.Arch A → machine.Store S → S → A → Result (X × S × A)}
  {p : SProg X} {Acc : X → Prop} {Locks : S → U64 → Prop} {Pre : S → Prop}
  {RS WS DS : S → U64 → Prop}

/-- **A body is `Safe` when it starts, from the history** (`body_safe` with the store link split): the store
state `σ` satisfies `Pre` and agrees with `ρ` (the serial-prefix memory) on aligned kernel words, and core
`L.cpu σ`'s view of `ρ` and of the real memory `μ` agrees (`VEq`). `Safe` is at `μ`. -/
theorem body_safeH (hL : MoveHeld own) (hO : OwnDep own User)
    (hp : IsProgOn (F ar) ar st (AltOf st Pre RS cls ko User) p)
    (O : PathObl st (F ar) Acc own cls ko User Locks Pre RS WS DS)
    (Sd : PathSide st (F ar) cls ko User Locks Pre RS WS DS)
    (hN : ReadOnce st ar p cls ko User Pre RS) (hT : ∀ s a, ∃ r, F ar st s a = ok r)
    (hmk : MasksWr st) {σ : S} {a : A} (hpre : Pre σ) {ρ μ : U64 → U64}
    (hρ : ∀ x, Aligned x → ¬ User x → L.mem σ x = ρ x)
    (hV : VEq own cls ko (L.cpu σ) (Locks σ) ρ μ) :
    Safe own cls ko (L.cpu σ) (Locks σ) μ
      (tr (RS σ) User cls ko (L.cpu σ) (L.ksb σ) (masksOf st σ) ar p ∅ a) := by
  have e0 : own (L.mem σ) = own ρ := hO _ _ hρ
  let Hp : U64 → Prop := fun x => ¬ User x ∧ (WS σ x ∨ DS σ x)
  have hRI : RInv own (L.cpu σ) (Locks σ) (RpOf (RS σ) User Hp) Hp μ := by
    have hH : ∀ x, Hp x → HeldV (L.cpu σ) (Locks σ) (own μ x) := by
      intro x hx
      have h : HeldV (L.cpu σ) (Locks σ) (own ρ x) := by
        rw [← e0]; exact heldBy_iff.mp (O.write_own σ x hpre hx.2 hx.1)
      rw [hV.1 x (Or.inl h)]; exact h
    refine ⟨hH, fun x hx => ?_⟩
    rcases hx with ⟨hu, hr⟩ | hx
    · rcases O.read_own σ x hpre hr hu with h | h
      · have h' : HeldV (L.cpu σ) (Locks σ) (own ρ x) := by rw [← e0]; exact heldBy_iff.mp h
        rw [hV.1 x (Or.inl h')]; exact Or.inl h'
      · have h' : own ρ x = .gate := by rw [← e0]; exact h
        rw [hV.1 x (Or.inr h')]; exact Or.inr h'
    · exact Or.inl (hH x hx)
  refine Fl4Proofs.P2.Serial.safe_of_runs hL (Rp := RpOf (RS σ) User Hp) (Hp := Hp) _ ∅ μ
    (fun _ => none) ⟨fun ν hν => ?_, fun y u hu => (by cases hu), fun y u hu => (by cases hu),
      fun y u hu => (by cases hu), hRI⟩
  have hνR : ∀ x, ¬ User x → RS σ x → ν x = μ x := fun x hu hr => hν.1 x (hRI.2 x (Or.inl ⟨hu, hr⟩))
  have hρR : ∀ x, ¬ User x → RS σ x → ρ x = μ x := fun x hu hr => hV.2.1 x (hRI.2 x (Or.inl ⟨hu, hr⟩))
  generalize hq : tr (RS σ) User cls ko (L.cpu σ) (L.ksb σ) (masksOf st σ) ar p ∅ a = q
  let rl := (reads q ν).filter (fun x => decide (Aligned x))
  let ul := rl.filter (fun x => decide (User x))
  let kl := rl.filter (fun x => decide (¬ User x))
  have hul : ∀ x, x ∈ ul ↔ (x ∈ reads q ν ∧ Aligned x) ∧ User x := by
    intro x; simp only [ul, rl, List.mem_filter, decide_eq_true_eq]
  have hkl : ∀ x, x ∈ kl ↔ (x ∈ reads q ν ∧ Aligned x) ∧ ¬ User x := by
    intro x; simp only [kl, rl, List.mem_filter, decide_eq_true_eq]
  obtain ⟨σu, hσu⟩ : ∃ s, s = wrs st ν ul σ := ⟨_, rfl⟩
  obtain ⟨σν, hσν⟩ : ∃ s, s = wrs st ν kl σu := ⟨_, rfl⟩
  obtain ⟨uP, uL, uR, uW, uD⟩ := wrs_user st Sd (ν := ν) ul σ
    (fun x hx => ⟨((hul x).mp hx).2, ((hul x).mp hx).1.2⟩) hpre
  obtain ⟨uc, ub, um⟩ := wrs_const st (ν := ν) hmk ul σ
  have uM := wrs_mem st (ν := ν) ul σ (fun x hx => ((hul x).mp hx).1.2)
  rw [← hσu] at uP uL uR uW uD uc ub um uM
  obtain ⟨kc, kb, km⟩ := wrs_const st (ν := ν) hmk kl σu
  have kM := wrs_mem st (ν := ν) kl σu (fun x hx => ((hkl x).mp hx).1.2)
  rw [← hσν] at kc kb km kM
  have hmσ := masksOf_eq st σ
  have uMk : ∀ x, Aligned x → ¬ User x → L.mem σu x = ρ x := by
    intro x hx hu
    rw [uM x hx, if_neg (fun h => hu ((hul x).mp h).2)]; exact hρ x hx hu
  obtain ⟨ru, hru⟩ := hT σu a
  by_cases hacc : Acc ru.1
  · -- accepted at `σu`
    refine ⟨fun x => if Aligned x ∧ ¬ User x then ρ x else μ x, fun y hy hpo => hy ?_, ?_⟩
    · show (if Aligned y ∧ ¬ User y then ρ y else μ y) = μ y
      split_ifs
      · exact hV.2.1 y hpo
      · rfl
    have gu : AltOf st Pre RS cls ko User σu := AltOf.pre uP
    have hW := O.acc σu a ru uP hru hacc
    rw [hp _ (Narrow.guard _ _ _) σu gu a] at hW
    have hW := (interp_guard p σu a ru hW).2
    have hA := Sd.read_aligned σu σu a ru uP (Alt.refl σu) hru
    rw [hp _ (Narrow.guard _ _ _) σu gu a] at hA
    have hA := (interp_guard p σu a ru hA).2
    have hM := O.move_steps hp uP gu hru
    have hO1 := hN σu σu a ru uP (Alt.refl σu) (by rw [← hp _ (Narrow.self st) σu gu a]; exact hru)
    rw [uR] at hW hO1; rw [uW] at hW; rw [uc, uL] at hM
    rw [← hq]
    refine sim (L := L) hO hmk (Rr := RS σ) (Wr := fun x => True ∧ WS σ x) ?_ p σu a ∅ ∅ ∅ ν
      (fun x => if Aligned x ∧ ¬ User x then ρ x else μ x)
      (within_and p σu a hA hW) hM hO1 (fun x hx => absurd hx (Set.notMem_empty x)) subset_rfl
      (um.trans hmσ) ub uc (fun x hx hu => by
        show (if Aligned x ∧ ¬ User x then ρ x else μ x) = _
        rw [if_pos ⟨hx, hu⟩]; exact (uMk x hx hu).symm) ?_
    · intro x hx
      exact ⟨O.aligned σ x hpre (Or.inl hx.2), fun hu => ⟨hu, Or.inl hx.2⟩⟩
    · rw [hq]
      intro x hx hxa hxr _
      by_cases hu : User x
      · rw [uM x hxa, if_pos ((hul x).mpr ⟨⟨hx, hxa⟩, hu⟩)]
      · rw [uMk x hxa hu, hνR x hu hxr]; exact hρR x hu hxr
  · -- declined at `σu`
    have hAlt : Alt st (RS σu) cls ko User σu σν := by
      refine ⟨kc, kb, km, fun x hx => ?_, fun x hx hu hko => ?_⟩
      · have hxa := Sd.rs_aligned σu x uP hx
        rw [uR] at hx
        rw [kM x hxa]
        split_ifs with h
        · have hu := ((hkl x).mp h).2
          rw [hνR x hu hx, uMk x hxa hu]; exact (hρR x hu hx).symm
        · rfl
      · have hxa : Aligned x := Sd.ko_aligned x (by rcases hko with h | h <;> rw [h] <;> simp)
        rw [kM x hxa]
        split_ifs with h
        · rw [uc] at hko
          rw [hν.2.2 x hko, uMk x hxa hu]; exact (hV.2.2 x hko).symm
        · rfl
    obtain ⟨rν, hrν⟩ := hT σν a
    have gν : AltOf st Pre RS cls ko User σν := ⟨σu, uP, hAlt⟩
    obtain ⟨-, hW, hM⟩ := O.dec_alt σu a ru uP hru hacc σν rν hAlt hrν
    rw [hp _ (Narrow.guard _ _ _) σν gν a] at hW
    rw [hp _ (Narrow.mguard _ _) σν gν a] at hM
    have hW := (interp_guard p σν a rν hW).2
    have hM := (interp_mguard p σν a rν hM).2
    have hA := Sd.read_aligned σu σν a rν uP hAlt hrν
    rw [hp _ (Narrow.guard _ _ _) σν gν a] at hA
    have hA := (interp_guard p σν a rν hA).2
    have hO1 := hN σu σν a rν uP hAlt (by rw [← hp _ (Narrow.self st) σν gν a]; exact hrν)
    rw [uR] at hO1; rw [uD] at hW; rw [uc, uL] at hM
    refine ⟨fun x => if Aligned x ∧ ¬ User x then L.mem σν x else μ x, fun y hy hpo => ?_, ?_⟩
    · apply hy
      beta_reduce
      split_ifs with h
      · rw [kM y h.1, uMk y h.1 h.2]
        split_ifs
        · exact hν.1 y hpo
        · exact hV.2.1 y hpo
      · rfl
    · rw [← hq]
      refine sim (L := L) hO hmk (Rr := fun _ => True) (Wr := fun x => True ∧ DS σ x) ?_ p σν a
        ∅ ∅ ∅ ν _ (within_and p σν a hA hW) hM hO1 (fun x hx => absurd hx (Set.notMem_empty x))
        subset_rfl (km.trans (um.trans hmσ)) (kb.trans ub) (kc.trans uc)
        (fun x hx hu => if_pos ⟨hx, hu⟩) ?_
      · intro x hx
        exact ⟨O.aligned σ x hpre (Or.inr hx.2), fun hu => ⟨hu, Or.inr hx.2⟩⟩
      · rw [hq]
        intro x hx hxa _ _
        rw [kM x hxa]
        by_cases hu : User x
        · rw [if_neg (fun h => ((hkl x).mp h).2 hu), uM x hxa,
            if_pos ((hul x).mpr ⟨⟨hx, hxa⟩, hu⟩)]
        · rw [if_pos ((hkl x).mpr ⟨⟨hx, hxa⟩, hu⟩)]

end body

/-- **`LocalPath.safe` from the history**: a start at `ρ` gives `Safe` at every `μ` the core sees as `ρ`. -/
theorem LocalPath.safeH {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
    {ko : U64 → ClsOwner U64} {User : U64 → Prop} (P : LocalPath own cls ko User) (hL : MoveHeld own)
    (hO : OwnDep own User) {c : U64} {hs : U64 → Prop} {ρ μ : U64 → U64} {q : SP}
    (h : StartAt P c hs ρ q) (hV : VEq own cls ko c hs ρ μ) : Safe own cls ko c hs μ q := by
  obtain ⟨σ, a, hpre, rfl, rfl, hρ, rfl⟩ := h
  let _ := P.L
  exact body_safeH hL hO P.isProg P.obl P.side P.once P.total P.masks hpre hρ hV

end

end Fl4Proofs.P2.E2E
