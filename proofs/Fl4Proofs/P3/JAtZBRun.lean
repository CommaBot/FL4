/-
P3 (line mmuAD, gen 25): **`hRt` of `JAtZV.enter` reduced to spec facts of the exit point.**

`JAtZV.enter` (P3/JAtZBLay) keeps `hRt` [J]: the entering thread's state word is not `BlockedR` (blocked on send,
receive, notification or reply). The word is the `tsCode` of the spec thread's state (`xtop.fin`'s TCB relation,
`.st`), so:

* **`JAtZB.nbr`**: a typed-heap TCB whose spec state is runnable (`running` / `restart` / `runningVM`) or
  `idleThreadState` has a state word that is not `BlockedR`. No premise beyond that spec fact.
* **`JAtZB.nbrCur`**: the current thread, when the scheduler action is `resumeCurThread` and the current thread
  is not the idle thread, satisfies it (`JAtZB.curRun : CurRunM σ`, l4v `ct_running or ct_idle`).
* **`JAtZV.enterR`** = `JAtZV.enter` with `hRt` replaced by the spec fact; **`JAtZV.enterCur`**: for FL4's entering
  thread `t` with `t.bv = σ.curThread`, `σ.schedulerAction = .resumeCurThread`, `σ.curThread ≠ σ.idleThread` —
  the state at FL4's kernel exit, where `vcpu::enter` runs for the current thread after `schedule` /
  `activate_thread` (spec `fl4KernelExitV`: `schedule` leaves `resumeCurThread`). These three are the call site's
  facts, stated where used; `hRt` itself is no longer a premise of `enterCur`.

Named premises: `enterCur`'s `hcur`, `hres`, `hni` [J] (exit-point facts; the idle-thread case is excluded rather
than derived: `JAtZB` has no field fixing the idle TCB's state word). No existing statement changed.
-/
import Fl4Proofs.P3.JAtZBWr
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P0.Consts Fl4Proofs.P3.Notif

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

/-- **Not `BlockedR` from the spec state** (module docstring). -/
theorem JAtZB.nbr (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : Z.th t = some .tcb)
    (hsp : ∀ x, σ.kheap t.bv = some (.tcb x) →
      Fl4Spec.runnable x.tcbState = true ∨ x.tcbState = .idleThreadState) :
    ¬ P1.BlockedR (L.mem s (P1.stA t)) := by
  intro hb
  obtain ⟨x, hk, -⟩ := J.xtop.rel.2.1.1.tcb t ht
  have hw := (J.xtop.fin.1.1.2.2.1.at_tcb (J.thT t ht) hk).st
  have hr := hsp x hk
  rw [Sched.stA_tStA] at hb
  have hv : (L.mem s (tStA t)).val = 3 ∨ (L.mem s (tStA t)).val = 4 ∨ (L.mem s (tStA t)).val = 5 ∨
      (L.mem s (tStA t)).val = 6 := by
    rcases hb with (h | h | h) | h <;> rw [h] <;> simp
  rw [hw] at hv
  cases hx : x.tcbState <;> rw [hx] at hv hr <;> simp_all [tsCode, Fl4Spec.runnable]

/-- **The current thread at a resumed, non-idle exit** (module docstring). -/
theorem JAtZB.nbrCur (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : Z.th t = some .tcb)
    (hcur : t.bv = σ.curThread) (hres : σ.schedulerAction = .resumeCurThread)
    (hni : σ.curThread ≠ σ.idleThread) :
    ¬ P1.BlockedR (L.mem s (P1.stA t)) :=
  J.nbr ht fun x hx => by
    have hW : CurRunW σ := J.curRun.resolve_left fun e => e hres
    rw [hcur] at hx
    exact Or.inl (hW.run hni x hx)

variable {ar : machine.Arch A}

set_option maxHeartbeats 4000000 in
/-- **`JAtZV.enter` with `hRt` from the spec state** (module docstring). -/
theorem JAtZV.enterR (hA : P0.ArchTotal ar) (J : JAtZV (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (a' : A)
    {t : U64} (ht : Z.th t = some .tcb) (hv0 : L.mem s (tVcpuA t) ≠ 0#u64)
    (hsp : ∀ x, σ.kheap t.bv = some (.tcb x) →
      Fl4Spec.runnable x.tcbState = true ∨ x.tcbState = .idleThreadState) :
    vcpu.enter st ar s a' t ⦃ r => JExtV (L := L) V X Z.th r.1 ∧ RunVmB (L := L) Z.th r.1 ⦄ :=
  J.enter hA a' ht hv0 (J.base.nbr ht hsp)

set_option maxHeartbeats 4000000 in
/-- **`vcpu.enter` of the current thread at a VM-epoch kernel exit**; `hcur`, `hres`, `hni` [J] (the exit
point's facts, module docstring). -/
theorem JAtZV.enterCur (hA : P0.ArchTotal ar) (J : JAtZV (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (a' : A)
    {t : U64} (ht : Z.th t = some .tcb) (hv0 : L.mem s (tVcpuA t) ≠ 0#u64)
    (hcur : t.bv = σ.curThread) (hres : σ.schedulerAction = .resumeCurThread)
    (hni : σ.curThread ≠ σ.idleThread) :
    vcpu.enter st ar s a' t ⦃ r => JExtV (L := L) V X Z.th r.1 ∧ RunVmB (L := L) Z.th r.1 ⦄ :=
  J.enter hA a' ht hv0 (J.base.nbrCur ht hcur hres hni)

end

end

end Fl4Proofs.P3
