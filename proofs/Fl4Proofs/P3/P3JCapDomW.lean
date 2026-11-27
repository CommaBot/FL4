/-
P3 (p3J gen 36): **`DispStabFootLo` is implied by `DispStabFootLj`** (the premise-honesty claim of P3JCapDom,
checked).

* `midDecStW_anti` / `invDecStW_anti`: `MidDecStW` / `InvDecStW` are antitone in the cap predicate (the predicate
  is the last antecedent).
* **`dispStabFootLo_of_Lj`**: `DispStabFootLj → DispStabFootLo` (`IsRestCap cp → ¬ Reply ∧ ¬ Easy ∧ ¬ Ep`:
  P3JCapDom's `restCap_not`; the other two fields verbatim). With P3JCapDom's `dispStabFootLj_of_Lo` the two are
  equivalent under the tops' platform facts.

No premise. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JCapDom
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs : Set U64}

/-- (p3J gen 36) `MidDecStW` is antitone in the cap predicate. -/
theorem midDecStW_anti {W W' : capability.Cap → Prop} (hWW : ∀ cp, W' cp → W cp) {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : MidDecStW (L := L) arI AR MR W Z H Cs s a σ n c) : MidDecStW (L := L) arI AR MR W' Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs (hWW cp hW)

/-- (p3J gen 36) `InvDecStW` is antitone in the cap predicate. -/
theorem invDecStW_anti {W W' : capability.Cap → Prop} (hWW : ∀ cp, W' cp → W cp) {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool}
    (h : InvDecStW (L := L) arI AR MR W Z H Cs s a σ n call bl don) :
    InvDecStW (L := L) arI AR MR W' Z H Cs s a σ n call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs (hWW cp hW)

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Proofs.P3

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

theorem restCapW {cp : capability.Cap} (h : SInvCk.KW (absCap cp) ∧ IsRestCap cp) :
    SInvCk.KW (absCap cp) ∧ ¬ IsReplyCap cp ∧ ¬ IsEasyCap cp ∧ ¬ IsEpCap cp :=
  ⟨h.1, restCap_not h.2⟩

/-- (p3J gen 36) **`DispStabFootLj → DispStabFootLo`** (module docstring). -/
theorem dispStabFootLo_of_Lj {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : DispStabFootLj (L := L) arI AR MR s a σ) : DispStabFootLo (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 =>
    invDecStW_anti (fun _ => restCapW) (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 =>
    midDecStW_anti (fun _ => restCapW) (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

end

end Fl4Proofs.P3.Mc
