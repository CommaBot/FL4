/-
P3 (iolay gen 5): **YieldBlock at every reachable joint state** — a thread with `tcbYieldTo ≠ none` is not blocked
at all (SpecInvYieldBlockT/F1..F4/H), with `CurYieldNone` — carried beside `kernel_entry_reachU29`'s reachability
(as JYieldScope does for gen 4's weaker YieldScope; gen 4's modules unchanged).

* **`JReachYB s a σ := JReachU17 s a σ ∧ YieldBlockS σ ∧ CurYieldNone σ`**; `JReachYB.toY` (gives gen 4's `JReachY`).
* **`kernel_entry_yieldScope2U29`**: same premises as `kernel_entry_reachU29`; at a `JReachYB` state the `JAtZ` with
  `SInvX`, `YieldBlockS`, `CurYieldNone`, and at the exit of each of the six entry kinds `RJ ∧ JReachYB`.
* `JAtZ.yield0_blk`: a TCB of `Z.T` whose state word codes a blocked state (3 receive, 4 send, 5 reply,
  6 notification) has `YIELD_TO = 0` under YieldBlock (`TcbRel.st`, `YieldRel.tcb`).
* `KEvSpec.true_not_irq`, `boot_yieldBlock'`.

No new premise ([J]/[P]/[W]); no existing statement changed.
-/
import Fl4Proofs.P3.JYieldScope
import Fl4Proofs.P3.SpecInvYieldBlockH
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

theorem boot_yieldBlock' : SInv.YieldBlockS (Fl4Spec.initASt (Z := Unit)) ∧
    SInv.CurYieldNone (Fl4Spec.initASt (Z := Unit)) :=
  ⟨SInv.boot_yieldBlock, SInv.boot_curYieldNone⟩

theorem blk_of_code {ts : Fl4Spec.ThreadState} (h : tsCode ts = 3 ∨ tsCode ts = 4 ∨ tsCode ts = 5 ∨ tsCode ts = 6) :
    ¬ SInv.notBlkSt ts := by
  cases ts <;> simp_all [tsCode, SInv.notBlkSt]

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **A blocked thread's `YIELD_TO` word is 0** at a joint state carrying YieldBlock. -/
theorem JAtZ.yield0_blk (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hY : SInv.YieldBlockS σ) {d : U64}
    (hd : d ∈ Z.T) (hs : (L.mem s (tStA d)).val = 3 ∨ (L.mem s (tStA d)).val = 4 ∨ (L.mem s (tStA d)).val = 5 ∨
      (L.mem s (tStA d)).val = 6) : L.mem s (Fl4Proofs.P1.yieldA d) = 0#u64 := by
  obtain ⟨x, hk, hr⟩ := J.xtop.ipc.tcb d hd
  rw [hr.st] at hs
  have hb := blk_of_code hs
  have hn : x.tcbYieldTo = none := by
    by_contra hne
    exact hb (hY _ x hk hne)
  obtain ⟨x', hk', hy⟩ := J.yld.tcb d hd
  rw [hk] at hk'
  cases hk'
  rw [hn] at hy
  unfold optRef at hy
  by_contra h0
  rw [if_neg h0] at hy
  cases hy

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **The reachable joint states with YieldBlock** (module docstring). -/
abbrev JReachYB (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  JReachU17 (L := L) arI AR MR s a σ ∧ SInv.YieldBlockS σ ∧ SInv.CurYieldNone σ

variable {arI AR MR} in
theorem JReachYB.toY {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : JReachYB (L := L) arI AR MR s a σ) :
    JReachY (L := L) arI AR MR s a σ :=
  ⟨h.1, h.2.1.scope, h.2.2⟩

end

end

end Fl4Proofs.P3.SInvR.G5
