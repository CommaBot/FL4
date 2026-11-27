/-
# P2 (line p3mc, gen 22): a certificate at real values for a program that writes held words

Handoff §26c item 3, the generic part. `PathObl.safe_tr_dec` (U20) covers programs that decline writing nothing.
**`PathObl.safe_tr_wr`**: a program is `Safe` at a start `σ` when, at every state carrying `σ`'s constants and `ρ`
on a read set `Rd ⊆ Ro` (∌ user), it runs on `guard st Rd Wd` with every write step passing `StepOK`, and every
non-user word of `Wd` is held at `μ` (`HeldV`). Same proof as `safe_tr_dec` (`safe_tr_of_states` with
`Hp := Wd ∖ user`), the `WithinM` fact supplied by the caller instead of an `mguard` run.

For the irq foreign-`tm` starts: `Rd` the head's words (`VtRd`'s first three classes) and the tail's `IrqRdT` at the
view start, `Wd` the tail's writes (`IrqWr`, the current thread's `STATE`, the clock words), the run by `irq_fh_guard`
+ `irqTail_guardT` at `σ` moved to `s` by `interp_agree` (plan: handoff §27).

No named premises; no existing statement changed.
-/
import Fl4Proofs.P2.E2EPU20
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
open Fl4Proofs.P2.E2E (Once tr reads safe_tr_of_states exists_mem_state OwnDep MasksWr masksOf masksOf_eq)
open Fl4Proofs.P2.Serial (Owner ClsOwner HeldV PO Safe MoveHeld Adm)

noncomputable section
open Classical

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **A program writing held words, run on a guard at every state carrying `ρ` on its reads, is `Safe`**
(module docstring). -/
theorem safe_tr_wr {X : Type} {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
    {kt : U64 → ClsOwner U64} {User : U64 → Prop} (hL : MoveHeld own) (hO : OwnDep own User) (hmk : MasksWr st)
    {c : U64} {hs : U64 → Prop} {μ ρ : U64 → U64} {σ : S} {a : A} (p : SProg X) (hz : NoZero p)
    (hc : L.cpu σ = c) {Ro Rd Wd : U64 → Prop}
    (hal : ∀ b, Rd b → Aligned b) (hR0 : ∀ q, Rd q → Ro q ∧ ¬ User q)
    (hWd : ∀ x, Wd x → Aligned x ∧ (¬ User x → HeldV c hs (own μ x)))
    (hRPO : ∀ x, ¬ User x → Ro x → PO c hs (own μ x))
    (hρμ : ∀ x, PO c hs (own μ x) → ρ x = μ x)
    (hgo : ∀ s : S, L.cpu s = L.cpu σ → L.ksb s = L.ksb σ → (∀ b, Rd b → L.mem s b = ρ b) →
      ∃ r, interp (guard st Rd Wd) ar p s a = ok r ∧
        WithinM st ar (fun x y => StepOK own cls kt User c hs (L.mem x) (L.mem y)) p s a) :
    Safe own cls kt c hs μ (tr Ro User cls kt c (L.ksb σ) (masksOf st σ) ar p ∅ a) := by
  refine safe_tr_of_states hL hO hmk (Hp := fun x => Wd x ∧ ¬ User x) _ a
    (fun x hx => (hWd x hx.1).2 hx.2) hRPO ?_
  intro ν hν
  generalize hq : tr Ro User cls kt c (L.ksb σ) (masksOf st σ) ar p ∅ a = q
  obtain ⟨s, sc, sk, sm, hmem0⟩ := exists_mem_state hmk σ (fun x => if x ∈ reads q ν then ν x else ρ x)
  have hmem : ∀ x, Aligned x → L.mem s x = if x ∈ reads q ν then ν x else ρ x := hmem0
  have eR : ∀ b, Ro b → ¬ User b → (if b ∈ reads q ν then ν b else ρ b) = ρ b := by
    intro b hb hu'
    split_ifs
    · exact (hν.1 b (hRPO b hu' hb)).trans (hρμ b (hRPO b hu' hb)).symm
    · rfl
  have hag : ∀ b, Rd b → L.mem s b = ρ b := fun b hb => by
    rw [hmem b (hal b hb), eR b (hR0 b hb).1 (hR0 b hb).2]
  obtain ⟨r, hg, hWM⟩ := hgo s sc sk hag
  have hW := (interp_guard _ s a r hg).2
  have hO1 := once_of_guardG (R := Rd) (W := Wd) (User := User)
    (fun q hq => (hR0 q hq).2) _ hz ∅ ∅ s a r hg
  have hOnce := once_monoR (R := Rd) (R' := Ro) (User := User)
    (fun b hb => (hR0 b hb).1) _ ∅ ∅ ∅ s a hO1 (fun _ h => h)
  refine ⟨s, Wd, sc.trans hc, sk, sm.trans (masksOf_eq st σ),
    Within.mono (fun b hb => hal b hb) (fun b hb => hb) _ s a hW, hWM, hOnce,
    fun x hx => ⟨(hWd x hx).1, fun hu => ⟨hx, hu⟩⟩, fun x hx hxa => by rw [hmem x hxa, if_pos hx],
    fun x hxa hu' hne hpo => hne ?_⟩
  rw [hmem x hxa]
  split_ifs
  · exact hν.1 x hpo
  · exact hρμ x hpo

end

end
end Fl4Proofs.P2.PathObl
