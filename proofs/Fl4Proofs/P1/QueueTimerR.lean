/-
P1: `timer.remove` with its footprint at both ends (`TF`), downstream of the
red-black proofs (`TimerRBRmv`), so that the full `TInv` at the end of `remove`
can use `timer.remove.rb`.
-/
import Fl4Proofs.P1.TimerRBRmv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}

/-! ## `TInv` with a footprint at both ends

`TF` is `TFB` with the full `TInv`; it holds at the start and at the end of
`timer.remove`, not at its intermediate states (hence `TFB` inside). -/

/-- `TInv`, and a `KW ∅` footprint from `s0`: the timer code writes only TCB
timer fields and node timer-tree words (`TKeep`: the other TCB fields are kept). -/
def TF (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (Ac : Set U64) (s0 s : S) : Prop :=
  TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s ∧ Foot st T Cs Sg Scs Z ∅ s0 s ∧ ANI st s0 s ∧ TKeep st T s0 s ∧
    WritesIn st s0 s (TW st T Cs s0)

theorem TF.start {s : S} (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) : TF st T Cs Ω H Sg Rp Scs Nt Z Ac s s :=
  ⟨h, Foot.refl _, ANI.refl _, TKeep.refl _, WritesIn.refl _ _⟩

theorem TF.tfb {s0 s : S} (h : TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) : TFB st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s :=
  ⟨⟨BlkOK.blkT h.1, h.1.tm⟩, h.2⟩

theorem TFB.tf {s0 s : S} (h : TFB st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hrb : TimerRB st T Cs s) :
    TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s :=
  ⟨h.tinv hrb, h.2⟩

/-- **`timer.remove` with its footprint**: `TInv` kept, only the timer words
written, the other TCB fields kept. -/
theorem timer.remove.tf {s0 : S} (s : S) (t : U64) (h : TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (ht : t ∈ T) : timer.remove st s t ⦃ s' => TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ :=
  WP.spec_mono (WP.spec_and (timer.remove.tfb s t h.tfb ht) (timer.remove.rb s t h.1.tcbs ht h.1.rb h.1.nodes))
    fun _ h' => h'.1.tf h'.2.1

theorem timer.remove.tinv (s : S) (t : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ht : t ∈ T) : timer.remove st s t ⦃ s' => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ :=
  WP.spec_mono (timer.remove.tf (s0 := s) s t (TF.start h) ht) fun _ h' => h'.1

end

end Fl4Proofs.P1
