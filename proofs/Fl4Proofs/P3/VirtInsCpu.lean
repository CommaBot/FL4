/-
P3x for virtualization (line virt, gen 19, item 2, helper): **`insert_new_cap` keeps the core id** —
`set_cap_cpuV`, `insert_new_cap_cpu`, P3/UntypedExp's `set_cap_ksb` / `insert_new_cap_ksb` with `cpu` for `ksb`
(same proof; kept in a module with UntypedExp's imports only, where `step` picks the same spec lemmas). Used by
P3/VirtLoopFrame for `WritesIn` (which fixes `ksb` and `cpu`).

No named premise. New file only; no existing statement changed.
-/
import Fl4Proofs.P3.UntypedExp
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtInsCpu
open fl4_core Classical Fl4Proofs.P3

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem set_cap_cpuV (sl : obj.Slot) (s : S) (c : capability.Cap) :
    obj.Slot.set_cap st sl s c ⦃ s' => L.cpu s' = L.cpu s ⦄ :=
  WP.spec_mono (set_cap_spec (L := L) sl s c) (by rintro _ rfl; simp)

theorem insert_new_cap_cpu (s : S) (src dest : U64) (c : capability.Cap) :
    cdt.insert_new_cap st s src dest c ⦃ s' => L.cpu s' = L.cpu s ⦄ := by
  unfold cdt.insert_new_cap
  step
  obtain ⟨s1, h1, k1⟩ := spec_exists (set_cap_cpuV (L := L) dest s c)
  rw [h1]; simp only [bind_ok]
  step; step
  simp only [obj.Slot.is_null, bind_ok]
  by_cases hz0 : next = 0#u64
  · simp only [hz0, decide_true, ↓reduceIte, bind_ok]
    step*
    subst_vars; simp_all
  · simp only [hz0, decide_false, Bool.false_eq_true, ↓reduceIte, bind_ok]
    step*
    subst_vars; simp_all

end

end Fl4Proofs.P3.VirtInsCpu
