/-
# P2 (line p3mc, gen 8): `Safe` of a translated body from runs at real-valued store states (`safe_tr_of_states`)

`body_safeV` (`P2/ViewSafeGen.lean`) certifies a body started at a view state by runs from that state's alternatives:
its check memory may differ from the store's only where the view does, so a run reading a word the view rewrites
(the vmF / sl fault handler's `AFFINITY` when it is homed elsewhere) cannot be followed (handoff p3mc §9/§10: the
"decline split"). Here the certificate runs at a store state whose aligned words carry **the admissible memory's own
values** (`ν` on the words the run reads, any values elsewhere where `c` cannot read them), so no rewritten word is in
the way:

* **`safe_tr_of_states`**: `tr R … kt p ∅ a` (read set `R`, class owner `kt` the target's) is `Safe` at `μ` if `R`'s
  kernel words are readable at `μ`, the written words `Hp` held, and every admissible `ν` has a store state `s` with
  `c`'s constants whose run of `p` reads aligned words, writes `Hp` words, passes `StepOK` at each write, reads each
  racy word once (`Once` with `R`), and whose memory is `ν` on the words read and `μ` on every other aligned kernel
  word `c` can read. (`simN` with `N = Kc = True` and no check-memory exception, then `Serial.safe_of_runs`.)
* `exists_mem_state`: a store state with given constants and any given values on all aligned words (finitely many
  writes: `U64` is finite).

No premise. No existing statement changed.
-/
import Fl4Proofs.P2.ViewSafeGen
import Fl4Proofs.P2.E2EVCut
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2E
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.Serial (Owner ClsOwner Prog HeldV PO Safe MoveHeld AltRun Adm Diff RInv)

noncomputable section
open Classical

section
variable {S A X : Type} {st : machine.Store S} [L : LawfulStore st] {ar : machine.Arch A}

/-- **A store state with `σ`'s constants and the values `f` on every aligned word.** -/
theorem exists_mem_state (hmk : MasksWr st) (σ : S) (f : U64 → U64) :
    ∃ s, L.cpu s = L.cpu σ ∧ L.ksb s = L.ksb σ ∧ st.frame_masks s = st.frame_masks σ ∧
      ∀ x, Aligned x → L.mem s x = f x := by
  have hfin : Set.Finite {x : U64 | Aligned x} := Set.toFinite _
  obtain ⟨c1, c2, c3⟩ := wrs_const st (ν := f) hmk hfin.toFinset.toList σ
  refine ⟨wrs st f hfin.toFinset.toList σ, c1, c2, c3, fun x hx => ?_⟩
  have hl : ∀ y ∈ hfin.toFinset.toList, Aligned y := fun y hy => by
    rw [Finset.mem_toList, Set.Finite.mem_toFinset] at hy; exact hy
  rw [wrs_mem st (ν := f) _ σ hl x hx, if_pos (by rw [Finset.mem_toList, Set.Finite.mem_toFinset]; exact hx)]

variable {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
  {kt : U64 → ClsOwner U64} {User : U64 → Prop}

/-- **`Safe` of a translated body from runs at real-valued states** (module docstring). -/
theorem safe_tr_of_states (hL : MoveHeld own) (hO : OwnDep own User) (hmk : MasksWr st)
    {c : U64} {hs : U64 → Prop} {kb : U64} {mk : U64 × U64} {R Hp : U64 → Prop} (p : SProg X) (a : A)
    {μ : U64 → U64}
    (hH : ∀ x, Hp x → HeldV c hs (own μ x)) (hR : ∀ x, ¬ User x → R x → PO c hs (own μ x))
    (hrun : ∀ ν, Adm own cls kt c hs μ (fun _ => none) ν → ∃ (s : S) (Wr : U64 → Prop),
      L.cpu s = c ∧ L.ksb s = kb ∧ st.frame_masks s = ok mk ∧
      Within st ar Aligned Wr p s a ∧
      WithinM st ar (fun x y => StepOK own cls kt User c hs (L.mem x) (L.mem y)) p s a ∧
      Once st ar R User ∅ ∅ p s a ∧ (∀ x, Wr x → Aligned x ∧ (¬ User x → Hp x)) ∧
      (∀ x ∈ reads (tr R User cls kt c kb mk ar p ∅ a) ν, Aligned x → L.mem s x = ν x) ∧
      (∀ x, Aligned x → ¬ User x → L.mem s x ≠ μ x → ¬ PO c hs (own μ x))) :
    Safe own cls kt c hs μ (tr R User cls kt c kb mk ar p ∅ a) := by
  have hRI : RInv own c hs (RpOf (fun x => R x ∧ True) User Hp) Hp μ :=
    ⟨hH, fun x hx => hx.elim (fun h => hR x h.1 h.2.1) (fun h => Or.inl (hH x h))⟩
  refine Fl4Proofs.P2.Serial.safe_of_runs hL (Rp := RpOf (fun x => R x ∧ True) User Hp) (Hp := Hp) _ ∅ μ
    (fun _ => none) ⟨fun ν hν => ?_, fun y u hu => (by cases hu), fun y u hu => (by cases hu),
      fun y u hu => (by cases hu), hRI⟩
  obtain ⟨s, Wr, hc, hk, hm, hW, hM, hN, hWr, hν', hD⟩ := hrun ν hν
  refine ⟨fun x => if Aligned x ∧ ¬ User x then L.mem s x else μ x, fun y hy hpo => ?_, ?_⟩
  · dsimp only at hy
    by_cases h : Aligned y ∧ ¬ User y
    · rw [if_pos h] at hy; exact hD y h.1 h.2 hy hpo
    · rw [if_neg h] at hy; exact hy rfl
  · exact simN (L := L) hmk (N := fun _ => True) (Kc := fun _ => True) (kt := kt) (ko := kt)
      (Rr := fun _ => True) (Wr := Wr) (D := fun _ => False) (DD := fun _ => False)
      (fun x hx => ⟨(hWr x hx).1, (hWr x hx).2, trivial, trivial⟩) (fun x _ => ⟨trivial, Or.inr trivial⟩)
      (fun x _ h => h) (fun x _ => rfl)
      (fun m m' h y _ => congrFun (hO m m' fun x hx hu => h x hx hu id) y)
      (fun q _ m v y hy => hy.elim) p s a ∅ ∅ ∅ ν _
      (Within.mono (fun b hb => ⟨hb, trivial⟩) (fun b hb => hb) p s a hW) hM hN
      (fun x hx => absurd hx (Set.notMem_empty x)) subset_rfl hm hk hc
      (fun x hx hu _ => by
        show (if Aligned x ∧ ¬ User x then L.mem s x else μ x) = _
        rw [if_pos ⟨hx, hu⟩])
      (fun x hx hxa _ _ => hν' x hx hxa)

end

end
end Fl4Proofs.P2.E2E
