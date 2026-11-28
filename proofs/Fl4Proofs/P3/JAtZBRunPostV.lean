/-
P3 (line mmuAD, gen 29): **`set_thread_state Running` then `postpone` at `JAtZV2`** (gen 28's "Next" item 3,
`runPostJ`).

* **`JAtZB.runPostJV`**: P3/JAtZBRunPost's `JAtZB.runPostJ` (gen 28) with its post extended by three facts its proof
  already has: FL4's writes lie in `TFoot` (`hW7`), the thread's spec TCB is `{x with tcbState := .running}` and
  every other spec object is unchanged (`postpone` keeps the spec heap: `hke`). Proof verbatim otherwise.
* **`JAtZV2.runPostJ`**: the same step at `JAtZV2 V X` for any `V` (`JAtZV2.ofBS`: VCPU objects kept — the
  thread is a TCB, not a VCPU; sizes kept; the only changed TCB is now `running`, so no new `runningVM`).
  Premises exactly `JAtZ.runPostJ`'s.

No named premise. No existing statement changed.

(mmuAD gen 42b18) `JAtZB.runPostJV` moved to P3/XTopJointRunPost as `runPostJ`'s in-place generalisation (statement
unchanged).
-/
import Fl4Proofs.P3.JAtZBRunPost
import Fl4Proofs.P3.JAtZBYield
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

/-- **`Running`, then `postpone`, at `JAtZV2`** (module docstring). -/
theorem JAtZV2.runPostJ (J : JAtZV2 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    (htD : t ∉ D)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hrs : x.tcbState = .inactive)
    (htc : t.bv ≠ σ.curThread) {sc : U64} (hsc : sc ∈ Z.C) (hxsc : x.tcbSchedContext = some sc.bv)
    {y : Fl4Spec.SchedContext} {n : Nat} (hky : σ.kheap sc.bv = some (.schedContext y n))
    (hya : Fl4Spec.scActive y = true)
    (hnrel : ¬ (Fl4Spec.refillReady σ.curTime (Fl4Spec.refillHd y) = true ∧
      Fl4Spec.refillSufficient 0 (Fl4Spec.refillHd y) = true)) :
    sched.set_thread_state st s t sched.TS_RUNNING ⦃ s6 =>
      sched.postpone st s6 sc ⦃ s7 => ∃ σ7, Fl4Spec.postpone (Z := Unit) sc.bv
          (stsAct (updK σ t.bv (.tcb { x with tcbState := .running })) t.bv) = ({((), σ7)}, False) ∧
        ∃ Lst' : U64 → List U64, JAtZV2 (L := L) arI V X AR Z H Cs Ac Lst' D s7 a σ7 ⦄ ⦄ := by
  have B := J.zv.base
  have hS := B.xtop.fin.1.1.1
  refine WP.spec_mono (B.runPostJV ht htD hk hrs htc hsc hxsc hky hya hnrel) fun s6 ⟨_, _, h6⟩ => ?_
  refine WP.spec_mono h6 fun s7 ⟨σ7, he, hW, hk7, hkp7, Lst', B'⟩ => ⟨σ7, he, Lst', ?_⟩
  refine J.ofBS B' hW (fun b hb => tfoot_oobj hS hb) (fun b hb => B.tfoot_nh hb) (VKeep.of_tfoot hS B.thT hW)
    (fun u hu => ?_) (fun o ko' ho => ?_) (fun o x' ho hx => ?_)
  · obtain ⟨vu, hvu⟩ := J.zv.vm.spec u hu
    refine hkp7 _ fun e => ?_
    rw [e, hk] at hvu; cases hvu
  · by_cases e : o = t.bv
    · subst e
      rw [hk7] at ho; cases ho
      exact ⟨_, hk, rfl⟩
    · rw [hkp7 _ e] at ho; exact ⟨ko', ho, rfl⟩
  · by_cases e : o = t.bv
    · subst e
      rw [hk7] at ho; cases ho
      cases hx
    · rw [hkp7 _ e] at ho; exact ⟨x', ho, hx⟩

end

end

end

end Fl4Proofs.P3
