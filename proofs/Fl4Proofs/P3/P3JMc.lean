/-
P3 (p3J gen 17): **the multicore joint predicate `JAtMc`, route (a): per-core projection.**

FL4's boot gives every core `c < NUM_NODES` its own idle TCB and idle SC (crates/fl4-core/src/boot.rs l.677-704,
`create_idle_threads` / `create_idle_thread`: state `TS_IDLE`, affinity `c`, the SC's `CORE` = `c`, the node's
`IDLE_THREAD` / `IDLE_SC` words). The ported spec (l4v's abstract spec, single core) has one `idleThread` and
`SInvAll.OnlyIdle` (l4v `only_idle`) admits no other TCB in `IdleThreadState`, so a second idle TCB in the joint
TCB set breaks `SInvX` (JBoot6Find `idle2_not_sinvX`).

**Route (a)** (this module): the joint invariant `JAtZ` is read as the *current core's projection*. `JAtZ`'s core
set `Cs` is all cores (P1's queues, nodes, affinities and `JKern.csN` already range over `Cs`), but the other
cores' idle TCBs and SCs are outside the projection exactly as the kernel-state block is: outside every ghost set,
outside P1's heap `H` and the typed heap, outside the spec state, apart from the kernel-state block, every core's
node and every RAM untyped region (`ForeignIdle`). Nothing of `JAtZ` changes: since they are not `H` objects,
`JPlaced.tcb` / `thT` / `hscC` / `JCovD` say nothing about them, and P1 asks only the *current* core's
`CUR_THREAD` / `IDLE_THREAD` to be TCBs of its set (`SchedQueuesInvX.curT` / `idleT`).
Why not (b), a spec extension with a set of idle threads: there is no Isabelle source for it (l4v has no SMP
abstract spec; seL4's SMP C code keeps one `ksIdleThread` per node in `NODE_STATE`, i.e. a per-node copy of the
single-core state, which is (a)'s reading), and it would change `OnlyIdle`, `schedule`'s idle choice,
`valid_idle` / `idle_thread` users across the whole port and every spec invariant proof built on them (SInvX …),
while (a) keeps every existing statement and proof.

* **`ForeignIdle Z H Cs s σ c`**: the shape FL4's boot writes for core `c`'s idle objects (`TS_IDLE`, affinity /
  SC core `c`, the TCB↔SC links) and their apartness from the projection.
* **`JAtMc arI AR s a σ`**: `JAt`'s ghosts with `JAtZ`, `VxE` and `ForeignIdle` at every core of `Cs` other than
  the current one.
* **`jAtMc_of_one`**: a `JAtZ` state whose cores are all the current one (one core: `Cs = {0}`) is a `JAtMc` state,
  with the same ghosts; **`JAtMc.jAt`**: a `JAtMc` state is a `JAt` state (forget `ForeignIdle`). So on one core
  `JAtMc` and `JAt` coincide and nothing single-core is lost.

Remaining for a multicore top (handoff p3J.md gen 17): the per-entry carry of `ForeignIdle` (an entry's footprint
misses the other cores' idle objects) and the projection switch between cores (`JAtMc` at core `c` ⇒ at core `c'`).

No sorry; no premises. New module; no existing statement changed.
-/
import Fl4Proofs.P3.JointAt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Mc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- Core `c`'s idle TCB (its node's `IDLE_THREAD` word). -/
def idleOf (s : S) (c : U64) : U64 := L.mem s (L.nodeAt s c layout.node.IDLE_THREAD)
/-- Core `c`'s idle SC (its node's `IDLE_SC` word). -/
def idleScOf (s : S) (c : U64) : U64 := L.mem s (L.nodeAt s c layout.node.IDLE_SC)

/-- Two byte ranges `[p, p + n)`, `[q, q + m)` apart. -/
def Apart (p n q m : Nat) : Prop := p + n ≤ q ∨ q + m ≤ p

/-- **Core `c`'s idle objects outside the projection** (module docstring). TCB 4096 bytes, SC 128 (`2 ^ 7`, the
smallest SC FL4's boot gives the idle thread). -/
structure ForeignIdle (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (σ : Fl4Spec.State Unit) (c : U64) :
    Prop where
  /-- `TS_IDLE` (`sched::TS_IDLE` = 7, `create_idle_thread`'s `set_state`). -/
  tSt : L.mem s (P1.stA (idleOf (L := L) s c)) = 7#u64
  /-- Affinity `c` (`set_affinity`). -/
  tAff : L.mem s (P1.affA (idleOf (L := L) s c)) = c
  /-- The TCB's SC word is the idle SC (`configure_sched_context`). -/
  tSc : L.mem s (P1.scA (idleOf (L := L) s c)) = idleScOf (L := L) s c
  /-- The SC's TCB word is the idle TCB. -/
  sTcb : L.mem s (P1.scTcbA (idleScOf (L := L) s c)) = idleOf (L := L) s c
  /-- The SC's core is `c` (`isc.set_cpu`). -/
  sCore : L.mem s (P1.scCoreA (idleScOf (L := L) s c)) = c
  tH : ∀ p k, H p = some k → Apart p.val (2 ^ k.bits) (idleOf (L := L) s c).val 4096
  sH : ∀ p k, H p = some k → Apart p.val (2 ^ k.bits) (idleScOf (L := L) s c).val 128
  tTh : ∀ q k, Z.th q = some k → Apart q.val (max (objSize k) 1) (idleOf (L := L) s c).val 4096
  sTh : ∀ q k, Z.th q = some k → Apart q.val (max (objSize k) 1) (idleScOf (L := L) s c).val 128
  tT : idleOf (L := L) s c ∉ Z.T
  sC : idleScOf (L := L) s c ∉ Z.C
  tK : σ.kheap (idleOf (L := L) s c).bv = none
  sK : σ.kheap (idleScOf (L := L) s c).bv = none
  /-- Apart from the kernel-state block. -/
  tKs : Apart (idleOf (L := L) s c).val 4096 (L.ksb s).val 13568
  sKs : Apart (idleScOf (L := L) s c).val 128 (L.ksb s).val 13568
  /-- Apart from every core's node. -/
  tN : ∀ c' ∈ Cs, Apart (idleOf (L := L) s c).val 4096 (L.nodeBase s c') 4288
  sN : ∀ c' ∈ Cs, Apart (idleScOf (L := L) s c).val 128 (L.nodeBase s c') 4288
  /-- Apart from every RAM untyped region of the MDB (as `JCovD.idleOut` for the current core's). -/
  ut : ∀ x ∈ Z.G.chains.flatten, ∀ p sb fi, capV (L.mem s) x = .Untyped p sb fi false →
    Apart (idleOf (L := L) s c).val 4096 p.val (2 ^ sb.val) ∧ Apart (idleScOf (L := L) s c).val 128 p.val (2 ^ sb.val)

/-- **The multicore joint predicate** (module docstring): the current core's projection `JAtZ` (with `VxE`), and
every other core's idle objects outside it. -/
def JAtMc (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ VxE Z ∧
      ∀ c ∈ Cs, c ≠ L.cpu s → ForeignIdle (L := L) Z H Cs s σ c

variable {arI} {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **One core: `JAtZ` gives `JAtMc`** (no other core, so `ForeignIdle` is vacuous). -/
theorem jAtMc_of_one (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hV : VxE Z)
    (h1 : ∀ c ∈ Cs, c = L.cpu s) : JAtMc (L := L) arI AR s a σ :=
  ⟨Z, H, Cs, Ac, Lst, D, J, hV, fun c hc hne => absurd (h1 c hc) hne⟩

/-- **The boot core alone (`Cs = {0}` or any `Cs ⊆ {0}`)**: `JAtZ` gives `JAtMc` (`JKern.cpuCs` puts the current
core in `Cs`, so it is core 0). -/
theorem jAtMc_of_core0 (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hV : VxE Z)
    (h0 : ∀ c ∈ Cs, c = 0#u64) : JAtMc (L := L) arI AR s a σ :=
  jAtMc_of_one J hV fun c hc => (h0 c hc).trans (h0 _ J.kern.cpuCs).symm

/-- **`JAtMc` gives `JAt`** (forget the other cores). -/
theorem JAtMc.jAt (h : JAtMc (L := L) arI AR s a σ) : JAt (L := L) arI AR s a σ := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hV, -⟩ := h
  exact ⟨Z, H, Cs, Ac, Lst, D, J, hV⟩

end

end Fl4Proofs.P3.Mc
