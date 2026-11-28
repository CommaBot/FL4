/-
P3 (iolay gen 4): **YieldScope at every reachable joint state** — a thread with `tcbYieldTo ≠ none` is not
`blockedOnReceive`, and the current thread does not yield — carried beside `kernel_entry_reachU29`'s reachability
without changing it.

`YieldScopeS` / `CurYieldNone` are not fields of `SInvX` (nor derivable from it: iolay gen 3 checked SInvX, SInvA,
SchedValid, ValidIdle, ScYield, P1). They are a separate spec invariant (SpecInvYieldScopeT/F1..F4/H): every spec step
keeps `YieldScopeS`, and every kernel exit (`activate_thread`) gives `CurYieldNone`. This module adds the pair to
the reachable states:

* **`JReachY s a σ := JReachU17 s a σ ∧ YieldScopeS σ ∧ CurYieldNone σ`** (a new predicate; `JReachU17` unchanged).
* `SInvX.ftEntry`: ft3's entry facts `FaultTcbsS ∧ NQB` and `CtEntry` from `SInvX σ` and `ct ≠ idle`
  (`SInvA.fts` / `nqb`, `SInvB.entryJ`, `ctEntry_of_J`), the hypotheses of `kentry_yieldScope`.
* `evOut_yieldScope`: an `EvOut` outcome of a non-syscall event keeps the pair.
* **`kernel_entry_yieldScopeU29`**: same premises as `kernel_entry_reachU29`; at a `JReachY` state,
  `kernel_entry_reachU29`'s `JAtZ` with `SInvX σ`, `YieldScopeS σ`, `CurYieldNone σ`, and at the exit of each of the
  six entry kinds `RJ ∧ JReachY` at the exit state. The exits are `kernel_entry_reachU29`'s, whose spec outcome
  (`fl4KernelEntrySyscall` membership, `EvOut`) the spec tops of SpecInvYieldScopeH carry the pair across.
* `boot_yieldScope'`: the pair at `initASt`.

No new premise ([J]/[P]/[W]): every theorem's premises are those of `kernel_entry_reachU29`. No existing statement
changed.
-/
import Fl4Proofs.P3.JNativeScope
import Fl4Proofs.P3.SpecInvYieldScopeH
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

/-- ft3's entry facts at a state carrying `SInvX` whose current thread is not idle. -/
theorem SInvX.ftEntry {σ : Fl4Spec.State Unit} (hX : SInvX σ) (hct : σ.curThread ≠ σ.idleThread) :
    (SInv.FaultTcbsS σ ∧ SInv.NQB σ) ∧ SInv.CtEntry σ :=
  ⟨⟨hX.1.a.fts, hX.1.a.nqb⟩, SInvAll.ctEntry_of_J (SInvAll.SInvB.entryJ hX.1.sb hct) hX.1.a.nq⟩

/-- The pair at boot. -/
theorem boot_yieldScope' : SInv.YieldScopeS (Fl4Spec.initASt (Z := Unit)) ∧
    SInv.CurYieldNone (Fl4Spec.initASt (Z := Unit)) :=
  ⟨SInv.boot_yieldScope, SInv.boot_curYieldNone⟩

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **A receive-blocked thread's `YIELD_TO` word is 0** at a joint state carrying YieldScope (`TcbRel.st`:
its state word codes `blockedOnReceive`; `YieldRel.tcb`: the word is its `tcbYieldTo`). -/
theorem JAtZ.yield0_recv (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hY : SInv.YieldScopeS σ) {d : U64}
    (hd : d ∈ Z.T) (hs : (L.mem s (tStA d)).val = 3) : L.mem s (Fl4Proofs.P1.yieldA d) = 0#u64 := by
  obtain ⟨x, hk, hr⟩ := J.xtop.ipc.tcb d hd
  obtain ⟨e, r, dd, hst⟩ := tsCode_three (hr.st.symm.trans hs)
  have hn : x.tcbYieldTo = none := by
    by_contra hne
    have := hY _ x hk hne
    rw [hst] at this
    exact this
  obtain ⟨x', hk', hy⟩ := J.yld.tcb d hd
  rw [hk] at hk'
  cases hk'
  rw [hn] at hy
  unfold optRef at hy
  by_contra h0
  rw [if_neg h0] at hy
  cases hy

/-- **The head of a receive queue has `YIELD_TO = 0`** at a joint state carrying YieldScope (`EpObjRel` of the
endpoint: state 2 is `recvEP`, whose queue's threads have state word 3). -/
theorem JAtZ.yield0_recvHead (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hY : SInv.YieldScopeS σ)
    {ptr : U64} (hE : ptr ∈ Z.E) (hst : L.epState s ptr = 2#u64) :
    L.mem s (Fl4Proofs.P1.yieldA (L.mem s (Fl4Proofs.P1.epHeadA ptr))) = 0#u64 := by
  obtain ⟨x, -, hrel⟩ := J.xtop.ipc.ep ptr hE
  rw [epState_eq] at hst
  cases x with
  | idleEP => rw [hrel.1] at hst; exact absurd hst (by decide)
  | sendEP q => rw [hrel.1] at hst; exact absurd hst (by decide)
  | recvEP q =>
    obtain ⟨-, xs, hne, -, hQ, hon⟩ := hrel
    obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hne
    have hh : L.mem s (Fl4Proofs.P1.epHeadA ptr) = y := hQ.head
    rw [hh]
    exact JAtZ.yield0_recv J hY (hQ.mem y (List.mem_cons_self ..)) (hon y (List.mem_cons_self ..)).1

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **The reachable joint states with YieldScope** (module docstring). -/
abbrev JReachY (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  JReachU17 (L := L) arI AR MR s a σ ∧ SInv.YieldScopeS σ ∧ SInv.CurYieldNone σ

end

end

end Fl4Proofs.P3.SInvR.G5
