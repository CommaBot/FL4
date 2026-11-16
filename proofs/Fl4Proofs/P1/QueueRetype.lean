/-
P1: **retype keeps the invariants, over the heap with the region's dead
objects dropped and the new objects added** — the statement
(`RetypeP1Step`); its proof comes family by family in later rounds
(endpoints, notifications and replies in their zero forms, then SCs, then
TCBs).

* `DeadQ H s q`: the object at `q` is read by nothing P1 tracks (P3's
  `DeadP` is this, `DeadP_iff`).
* the region `[lo, hi)` the retype may overwrite (the new objects' window;
  with a reset, the whole untyped region) and the window `[A, A + w k)`;
* the write frame: the cap-slot words (`CapW`), the region, and the
  debug-list words (`DbgW`, a new TCB is appended);
* the region after: zero, but a new TCB's context, domain, debug-link and
  name words (`TcbInitK`), when the new objects are in the heap
  (`newKind`); the region before: its objects dead;
* the current thread lies off the region.
-/
import Fl4Proofs.P1.QueueFinCap
import Fl4Proofs.P1.QueueHeap
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- **A dead object** for P1 (module docstring). -/
def DeadQ (st : machine.Store S) [L : LawfulStore st] (H : Heap) (s : S) (q : U64) : Prop :=
  (H q = some .tcb → L.mem s (stA q) = sched.TS_INACTIVE ∧
    L.mem s (scA q) = 0#u64 ∧ L.mem s (boundA q) = 0#u64 ∧
    q ≠ L.actionW s ∧ q ≠ L.idleW s) ∧
  (H q = some .ep → L.epState s q = 0#u64) ∧
  (H q = some .ntfn → L.epState s q ≠ 1#u64 ∧ L.mem s (ntfnBtA q) = 0#u64 ∧ L.mem s (ntfnScA q) = 0#u64) ∧
  (H q = some .reply → L.mem s (rTcbA q) = 0#u64) ∧
  (∀ z, H q = some (.sc z) → L.mem s (scTcbA q) = 0#u64 ∧ L.mem s (scReplyA q) = 0#u64 ∧
    L.mem s (scNtfnA q) = 0#u64)

/-- `[lo, hi)` met by `[a, b)`. -/
def MeetsR (lo hi a b : Nat) : Prop := ¬ (b ≤ lo ∨ hi ≤ a)

/-- `q` is the address of the `j`-th new object of the window. -/
def NewAt (A k w : Nat) (q : U64) : Prop := ∃ j, j < w ∧ q.val = A + j * k

/-- The heap kind of the new objects of FL4 type `n` (user size `us`), if
they are heap objects: TCB, endpoint, notification, CNode, SC, reply. -/
def newKind (n us : Nat) : Option HKind :=
  if n = 1 then some .tcb else if n = 2 then some .ep else if n = 3 then some .ntfn else
  if n = 4 then some (.other (us + 5)) else if n = 5 then some (.sc us) else if n = 6 then some .reply else none

/-- The TCB words a new TCB's creation initialises: the context
(registers, debug registers, FPU: below `F`), the domain (`F + 104`), the
debug links (`F + 248`, `F + 256`) and the name (from `F + 272`). -/
def TcbInitK (K : Nat) : Prop := K < 3328 ∨ K = 3432 ∨ K = 3576 ∨ K = 3584 ∨ 3600 ≤ K

/-- **The region after a retype** (module docstring): zero, but the
initialised words of the new TCBs, when the new objects are heap objects. -/
def WinInit (st : machine.Store S) [L : LawfulStore st] (s' : S) (lo hi A k w n us : Nat) : Prop :=
  (newKind n us).isSome → ∀ b : U64, Aligned b → lo ≤ b.val → b.val < hi →
    L.mem s' b = 0#u64 ∨ (n = 1 ∧ ∃ j, j < w ∧ ∃ K, TcbInitK K ∧ b.val = A + j * k + K)

/-- **P1's half of retype** (module docstring): from `BlkOK` over `H`'s
sets, with the region's objects dead, the current thread off the region,
the write frame and the region's contents after, `BlkOK` over a heap `H'`
that keeps `H`'s objects off the region, drops the ones on it, and has the
new objects (of kind `newKind n us`, each within its window slot `k`), with
the dead staying dead. -/
def RetypeP1Step (st : machine.Store S) [L : LawfulStore st] (s s' : S) (H : Heap) (Cs Ac : Set U64)
    (lo hi A k w n us : Nat) : Prop :=
  BlkOK st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
      (Heap.scBits H) Ac s →
    lo ≤ A → A + w * k ≤ hi → (∀ kd, newKind n us = some kd → 2 ^ kd.bits ≤ k) →
    (∀ q kd, H q = some kd → MeetsR lo hi q.val (q.val + 2 ^ kd.bits) → DeadQ st H s q) →
    ¬ (lo ≤ (L.curW s).val ∧ (L.curW s).val < hi) →
    WritesIn st s s' (fun b => CapW (Heap.tcbs H) (Heap.omega H) (Heap.frame H) b ∨ (lo ≤ b.val ∧ b.val < hi) ∨
      DbgW st (Heap.tcbs H) Cs s b) →
    WinInit st s' lo hi A k w n us →
    ∃ (H' : Heap) (Ac' : Set U64),
      BlkOK st (Heap.tcbs H') Cs (Heap.omega H') H' (Heap.frame H') (Heap.replies H') (Heap.scs H') (Heap.ntfns H')
        (Heap.scBits H') Ac' s' ∧
      (∀ q kd, H q = some kd → ¬ MeetsR lo hi q.val (q.val + 2 ^ kd.bits) → H' q = some kd) ∧
      (∀ q kd, H' q = some kd → (H q = some kd ∧ ¬ MeetsR lo hi q.val (q.val + 2 ^ kd.bits)) ∨
        (NewAt A k w q ∧ newKind n us = some kd)) ∧
      (∀ q, NewAt A k w q → ∀ kd, newKind n us = some kd → H' q = some kd) ∧
      (∀ q, H' q = H q → DeadQ st H s q → DeadQ st H' s' q)

end

end Fl4Proofs.P1
