/-
# P2 (line p3mc, gen 49): the `InsA` twin of `safe_tr_wr` (groundwork for the four irq slots)

The irq certificates (`irq_fh_annV`, `irq_hn_annV`, `irq_wf_annV`, `irq_wh_annV`; P2/IrqFhAnn … P2/IrqWhAnn) are
`PathObl.safe_tr_wr` (P2/SafeTrWr): a run on `guard st Rd Wd` with `StepOK` per write at every state carrying `ρ` on
the read set `Rd`, `Once` derived from the guard. **`PathObl.insA_narrow_tr_wr`**: the same data, with `Rd` and `Wd`
off `G`, give `InsA` of the re-annotated body — the foreign-handler pattern `insA_narrow_tr_gd` (P2/InsV15Fh) at
`Rc = Rg = Rd`, `Once` by `once_of_guardG` / `once_monoR` as in `safe_tr_wr`.

What each irq slot still needs (handoff §54): its `hgo` split out of the 16M monolith in place, and its read set cut
off `PWE K E` (its ASID table / pool reads are `AsidW` words, off `PWE` by `pwe_asid`, once the view equals `E` there,
`atAF_view`; the other words are region-tagged or kernel-static).

No named premise. New module; no existing statement changed.
-/
import Fl4Proofs.P2.InsV15Fh
import Fl4Proofs.P2.SafeTrWr
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
open Fl4Proofs.P2.E2E (Once tr reads OwnDep MasksWr masksOf)
open Fl4Proofs.P2.Serial (Owner ClsOwner HeldV PO MoveHeld InsA narrowSP)

noncomputable section
open Classical

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **The `InsA` twin of `safe_tr_wr`** (module docstring). -/
theorem insA_narrow_tr_wr {X : Type} {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
    {kt kv : U64 → ClsOwner U64} {User : U64 → Prop} {G : U64 → Prop} {Q : U64 → U64 → Prop} {NP : U64 → Prop}
    (hQ : Equivalence Q) (hL : MoveHeld own) (hO : OwnDep own User) (hmk : MasksWr st)
    (hGo : ∀ m m' : U64 → U64, (∀ x, ¬ G x → m x = m' x) → own m = own m') (hGko : ∀ x, G x → kt x = .free)
    (hGU : ∀ b, G b → ¬ User b)
    {c : U64} {hs : U64 → Prop} {μ ρ : U64 → U64} {σ : S} {a : A} (p : SProg X) (hz : NoZero p)
    (hc : L.cpu σ = c) {R0 Qv Rd Wd : U64 → Prop} (hGQ : ∀ b, G b → Qv b)
    (hal : ∀ b, Rd b → Aligned b) (hR0 : ∀ q, Rd q → (R0 q ∧ Qv q) ∧ ¬ User q)
    (hRdG : ∀ b, Rd b → ¬ G b) (hWdG : ∀ b, Wd b → User b ∨ ¬ G b)
    (hWd : ∀ x, Wd x → Aligned x ∧ (¬ User x → HeldV c hs (own μ x)))
    (hRPO : ∀ x, ¬ User x → (R0 x ∧ Qv x) → PO c hs (own μ x))
    (hρμ : ∀ x, PO c hs (own μ x) → ρ x = μ x)
    (hgo : ∀ s : S, L.cpu s = L.cpu σ → L.ksb s = L.ksb σ → (∀ b, Rd b → L.mem s b = ρ b) →
      ∃ r, interp (guard st Rd Wd) ar p s a = ok r ∧
        WithinM st ar (fun x y => StepOK own cls kt User c hs (L.mem x) (L.mem y)) p s a) :
    InsA G Q NP own cls kt c hs μ
      (narrowSP cls kt c Qv ∅ (tr R0 User cls kv c (L.ksb σ) (masksOf st σ) ar p ∅ a)) := by
  refine insA_narrow_tr_gd ar hQ hL hO hmk hGo hGko hGU p hc hGQ (Rc := Rd) (Rg := Rd) (Wd := Wd) hal hR0 hal hRdG
    hWdG hWd hRPO hρμ ?_
  intro s h1 h2 _ h3
  obtain ⟨r, hg, hWM⟩ := hgo s h1 h2 h3
  have hO1 := once_of_guardG (R := Rd) (W := Wd) (User := User) (fun q hq => (hR0 q hq).2) _ hz ∅ ∅ s a r hg
  exact ⟨r, hg, hWM, once_monoR (R := Rd) (R' := fun x => R0 x ∧ Qv x) (User := User)
    (fun b hb => (hR0 b hb).1) _ ∅ ∅ ∅ s a hO1 (fun _ h => h)⟩

end

end
end Fl4Proofs.P2.PathObl
