/-
P3 (line famw, gen 6): **the current thread's state word at an `Entered` joint state** (new lemma beside
`JAtZ.curFacts`, P3/ScRestJ.lean, which is left as it was).

* **`JAtZ.curRunR`**: at a `JAtZ` state with `Entered σ` (the current thread is not idle and the action is resume),
  if no thread runs a guest (`Endp.NativeScope σ`), the current thread's state word is `TS_RESTART` or `TS_RUNNING`.
  From `JAtZ.curRunnable` (the spec's current TCB is `runnable`), the relation's `TcbRel1.st` (state word =
  `tsCode` of the spec state) and `NativeScope` (excluding `runningVM`, code 8).

**What P3 does not export**: `NativeScope` at `JAtZ` states. It stays a named premise of the native IPC lemmas
(P3/IpcLeaves.lean: "VT-x: RunningVM branch not yet refined"); no P3 invariant (`JAtZ`, `SInvX`, `JExt`) states
that no TCB is `runningVM` (`JExt.vw` only says every typed-heap TCB's VCPU word is 0). Without it, `JAtZ.curFacts`
gives only P1's `Runnable` (RUNNING, RESTART or RUNNING_VM).
-/
import Fl4Proofs.P3.ScRestJ
import Fl4Proofs.P3.IpcLeaves
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **The current thread is `RESTART` or `RUNNING`** at an `Entered` joint state with no thread running a guest
(module docstring). -/
theorem JAtZ.curRunR (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) (hN : NativeScope σ) :
    L.mem s (P1.stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s (P1.stA (L.curW s)) = sched.TS_RUNNING := by
  have hct : sched.cur_thread st s = ok (L.curW s) := P1.cur_thread_ok (L := L) s
  obtain ⟨-, x, hk, hrun⟩ := J.curRunnable hni hct
  obtain ⟨-, ht, -, -⟩ := J.curFacts hni hct
  have hR := J.xtop.fin.1.1.2.2.1
  have hw := (hR.at_tcb ht hk).st
  have hvm := hN _ _ hk
  rw [stA_tStA]
  have e : ∀ k : U64, (L.mem s (tStA (L.curW s)) = k ↔ (L.mem s (tStA (L.curW s))).val = k.val) :=
    fun k => ⟨fun h => h ▸ rfl, fun h => UScalar.eq_of_val_eq h⟩
  rw [e, e, hw]
  unfold sched.TS_RESTART sched.TS_RUNNING
  cases hx : x.tcbState <;> rw [hx] at hrun hvm <;> simp_all [tsCode, Fl4Spec.runnable]

end
end
end Fl4Proofs.P3
