/-
P1: **retype keeps the invariants, over the heap with the region's dead
objects dropped and the new objects added** — the statement
(`RetypeP1Step`); its proof comes family by family in later rounds
(endpoints, notifications and replies in their zero forms, then SCs, then
TCBs).

* `DeadQ H s q`: the object at `q` is read by nothing P1 tracks (P3's
  `DeadP` is this, `DeadP_iff`).
* the reset is a step of its own (`ResetP1Step`): `reset_untyped` keeps
  `BlkOK` over the heap with the untyped region's (dead) objects dropped;
  its writes (the region, the cap's slot, the preemption point's words) are
  P1's to follow, the preemption point by `preemption_point.pp`; it keeps the
  current thread's words (`ResetKeeps`, for a preempted reset);
* after it, the region `[lo, hi)` the object creation may overwrite (the
  free part holding the window `[A, A + w k)`);
* the write frame of the creation: the cap-slot words (`CapW`), the region,
  and the debug-list words (`DbgW`, a new TCB is appended);
* the region after: zero, but a new TCB's context, domain, debug-link and
  name words (`TcbInitK`), when the new objects are in the heap
  (`newKind`); the region before: its objects dead;
* the current thread lies off the region.
-/
import Fl4Proofs.P1.QueueHeapDrop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

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

/-- The objects meeting the region `[lo, hi)` (those a reset or retype drops). -/
def RegionD (H : Heap) (lo hi : Nat) (q : U64) : Prop :=
  MeetsR lo hi q.val (q.val + 2 ^ ((H q).elim 0 HKind.bits))

/-- The region `[lo, hi)` misses the cores' nodes (P3's: kernel memory is
never untyped memory). -/
def RegionOffNodes (st : machine.Store S) [L : LawfulStore st] (Cs : Set U64) (s : S) (lo hi : Nat) : Prop :=
  ∀ c ∈ Cs, L.nodeBase s c + 4288 ≤ lo ∨ hi ≤ L.nodeBase s c

/-- An untyped cap's size and free index (P3's `valid_untyped`/`valid_cap`:
at least x64's `MIN_UNTYPED_BITS` = 4 bits, below 64, the free index within
the size). -/
def UtSize (fi sb : U64) : Prop := fi.val ≤ 2 ^ sb.val ∧ 4 ≤ sb.val ∧ sb.val < 64

/-- **P1's half of retype** (module docstring): from `BlkOK` over `H`'s
sets, with the region's objects droppable (`DropOK`: dead, unreferenced, the
current thread and SC off the region),
the write frame and the region's contents after, `BlkOK` over a heap `H'`
that keeps `H`'s objects off the region, drops the ones on it, and has the
new objects (of kind `newKind n us`, each within its window slot `k`), with
the dead staying dead. -/
def RetypeP1Step (st : machine.Store S) [L : LawfulStore st] (s s' : S) (H : Heap) (Cs Ac : Set U64)
    (lo hi A k w n us : Nat) : Prop :=
  BlkOK st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
      (Heap.scBits H) Ac s →
    lo ≤ A → A + w * k ≤ hi → (∀ kd, newKind n us = some kd → 2 ^ kd.bits ≤ k) →
    DropOK st H (RegionD H lo hi) Cs s → RegionOffNodes st Cs s lo hi →
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

/-- What the reset keeps for the current thread (for a preempted reset's
`DecPost`): the current thread, SC and scheduler action words, and the
current thread's `SC` and state words. -/
def ResetKeeps (st : machine.Store S) [L : LawfulStore st] (s s' : S) : Prop :=
  L.curW s' = L.curW s ∧ L.cscW s' = L.cscW s ∧ L.actionW s' = L.actionW s ∧
    L.mem s' (scA (L.curW s)) = L.mem s (scA (L.curW s)) ∧ L.mem s' (stA (L.curW s)) = L.mem s (stA (L.curW s))

open Classical in
/-- **P1's half of the reset** (module docstring): `reset_untyped` on the
slot `x` (a cap slot, `CapSlotW`) of an untyped cap `Untyped p sb fi dev`
(its size and free index valid, `UtSize`),
from `BlkOK` over `H`'s sets with the objects meeting the region droppable
(`DropOK`), ends in `BlkOK` over `H` with those objects dropped, the dead
staying dead. -/
def ResetP1Step (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A) : Prop :=
  ∀ (H : Heap) (Cs Ac : Set U64) (s : S) (a : A) (x p sb fi : U64) (dev : Bool),
    BlkOK st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
      (Heap.scBits H) Ac s →
    obj.Slot.cap st x s = ok (.Untyped p sb fi dev) →
    CapSlotW (Heap.tcbs H) (Heap.omega H) (Heap.frame H) x →
    p.val % 2 ^ sb.val = 0 → p.val + 2 ^ sb.val ≤ 2 ^ 64 →
    DropOK st H (RegionD H p.val (p.val + 2 ^ sb.val)) Cs s → RegionOffNodes st Cs s p.val (p.val + 2 ^ sb.val) →
    UtSize fi sb →
    untyped.reset_untyped st ar s a x ⦃ res => ∃ (H' : Heap) (Ac' : Set U64),
      BlkOK st (Heap.tcbs H') Cs (Heap.omega H') H' (Heap.frame H') (Heap.replies H') (Heap.scs H')
        (Heap.ntfns H') (Heap.scBits H') Ac' res.2.1 ∧
      (∀ q, H' q = if MeetsR p.val (p.val + 2 ^ sb.val) q.val (q.val + 2 ^ ((H q).elim 0 HKind.bits))
        then none else H q) ∧
      (∀ q, H' q = H q → DeadQ st H s q → DeadQ st H' res.2.1 q) ∧
      ResetKeeps st s res.2.1 ⦄

end

end Fl4Proofs.P1
