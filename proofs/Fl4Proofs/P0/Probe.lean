import Fl4Core.Funs
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P0
open fl4_core

/-- The trusted memory never fails (DESIGN.md §9: `fl4-store` is trusted). -/
structure StoreTotal {S : Type _} (st : machine.Store S) : Prop where
  read : ∀ s a, ∃ v, st.read s a = ok v
  write : ∀ s a v, ∃ s', st.write s a v = ok s'
  zero : ∀ s a n, ∃ s', st.zero s a n = ok s'
  ks_base : ∀ s, ∃ v, st.ks_base s = ok v
  cur_cpu : ∀ s, ∃ v, st.cur_cpu s = ok v

example {S : Type _} (st : machine.Store S) (h : StoreTotal st) (s : S) (c : U64) :
    obj.node_base st s c ⦃ _ => True ⦄ := by
  unfold obj.node_base
  obtain ⟨v, hv⟩ := h.ks_base s
  simp [hv]
  step*

end Fl4Proofs.P0
