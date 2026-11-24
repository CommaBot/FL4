/-
P2: **the global ownership map** `own` of `P2/PathObl.lean` (proposal), from
DESIGN §7 "What a local path may write", "Timer ownership" and "Local paths".

`own K m b` gives the owner of kernel word `b` in memory `m`, given `K`, the
data that changes only under the gate: P1's typed heap (`Heap`), the kernel
state base, the number of cores, and the set of capability slots. In order:

1. **Nodes.** A word of core `c`'s node (`ks + 13568 + c * 4288`, size 4288,
   P1's `nodeAt`) is `core c`'s.
2. **Capability slots.** A word of a slot (32 bytes; CNode slots, a TCB's own
   slots, IRQ-node slots) is `lock <slot>`'s: `localtimer::cspace_step` locks
   each slot before reading it, and frame-cap invocations beside the gate write
   slots they lock.
3. **TCBs** (`tcbOwner`, offsets of `arch/x86_64/layout.rs`, `F = 0xd00`).
   The thread's home core is its `AFFINITY` word.
   * Gate-owned (written only under the gate, read by other cores' local
     paths): `AFFINITY`, `DOMAIN`, `MCP`, `PRIO`, `SC`, `BOUND_NTFN`,
     `IPC_BUFFER`, `DEBUG_NEXT` / `DEBUG_PREV`, `VCPU`.
   * Timer fields `TIMER_DEADLINE` … `TIMER_HEIGHT`: armed (deadline ≠ 0), the
     core of its tree, `TIMER_HEIGHT >> 8`; disarmed, the home core (DESIGN
     "Timer ownership").
   * While blocked on an endpoint or notification (`STATE` ∈ {3 recv, 4 send,
     6 ntfn}): `STATE`, `BLOCK_OBJ`, `BLOCK_BADGE`, `BLOCK_FLAGS`, `EP_NEXT`,
     `EP_PREV` are `lock <BLOCK_OBJ>`'s: they change only with the queue's
     object locked (a waker), and a local path on another core reads a queued
     receiver's state under that lock.
   * Everything else of the TCB (registers, FPU image, fault words, reply
     link, scheduler links, flags, …): the home core's.
4. **Endpoints, notifications, reply objects**: `lock <object>`.
5. **Scheduling contexts**: the core in the SC's `CORE` word (offset 16); the
   `CORE` word itself is gate-owned.
6. **Everything else** (the global kernel state, page tables, untyped
   bookkeeping, …): the gate.

Notes for review (by the path lines):

* User memory (IPC buffers, frames) is outside `own`'s domain (`Serial`
  Scope): `K.user` marks it, and `PathObl`'s `read_own` / `write_own` are
  meant for kernel words only (a follow-up generalises them to
  `¬ K.user x → …`).
* `own` depends on `K`, which serial entries change (retype, delete,
  migration, binding): `Serial` fixes `own` for a whole execution; the
  follow-up lets a serial step replace it (sound: no local path is in
  progress then, `no_overlap`).
* Lock owners are indexed by object (slot) address, finer than
  `fl4_store::lock`'s 4,096-entry hash table: sound, since a hash collision
  only makes the real exclusion coarser.
-/
import Fl4Proofs.P1.QueueSchedInv
import Fl4Proofs.P2.PathObl
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.OwnMap
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.Serial (Owner)

noncomputable section
open Classical

/-- What `own` reads besides memory: data serial entries alone change. -/
structure KLayout where
  /-- P1's typed heap. -/
  heap : Heap
  /-- The kernel-state base (`ks_base`). -/
  ksb : U64
  /-- The number of cores (nodes). -/
  ncores : Nat
  /-- The base addresses of every capability slot. -/
  slots : Set U64
  /-- User memory (frames, IPC buffers): outside the ownership discipline. -/
  user : Set U64

/-- `b` lies in `[p, p + n)`. -/
def InW (p : U64) (n : Nat) (b : U64) : Prop := p.val ≤ b.val ∧ b.val < p.val + n

/-- `b` is a word of core `c`'s node. -/
def InNode (K : KLayout) (c b : U64) : Prop :=
  c.val < K.ncores ∧ K.ksb.val + 13568 + c.val * 4288 ≤ b.val ∧
    b.val < K.ksb.val + 13568 + c.val * 4288 + 4288

/-- The word at offset `off` of the object at `p`. -/
def fld (p off : U64) : U64 := core.num.U64.wrapping_add p off

/-- The core whose timer tree a `TIMER_HEIGHT` value names (`>> 8`). -/
def treeCore (v : U64) : U64 := @Classical.epsilon U64 ⟨0#u64⟩ (fun c => c.val = v.val / 256)

/-- TCB offsets (x86_64 `layout::tcb`, `F = 0xd00 = 3328`). -/
def oSTATE : U64 := 3328#u64
def oBLOCK_OBJ : U64 := 3336#u64
def oBLOCK_BADGE : U64 := 3344#u64
def oBLOCK_FLAGS : U64 := 3352#u64
def oBOUND_NTFN : U64 := 3368#u64
def oDOMAIN : U64 := 3432#u64
def oMCP : U64 := 3440#u64
def oPRIO : U64 := 3448#u64
def oSC : U64 := 3464#u64
def oEP_NEXT : U64 := 3496#u64
def oEP_PREV : U64 := 3504#u64
def oIPC_BUFFER : U64 := 3512#u64
def oAFFINITY : U64 := 3520#u64
def oTIMER_DEADLINE : U64 := 3528#u64
def oTIMER_HEIGHT : U64 := 3568#u64
def oDEBUG_NEXT : U64 := 3576#u64
def oDEBUG_PREV : U64 := 3584#u64
def oVCPU : U64 := 3664#u64

/-- Blocked on an endpoint (receive or send) or a notification. -/
def QueuedState (v : U64) : Prop := v.val = 3 ∨ v.val = 4 ∨ v.val = 6

/-- The owner of the word at offset `o` of the TCB at `t`. -/
def tcbOwner (m : U64 → U64) (t : U64) (o : Nat) : Owner U64 U64 :=
  let home : Owner U64 U64 := .core (m (fld t oAFFINITY))
  if o = oAFFINITY.val ∨ o = oDOMAIN.val ∨ o = oMCP.val ∨ o = oPRIO.val ∨ o = oSC.val ∨ o = oBOUND_NTFN.val ∨
      o = oIPC_BUFFER.val ∨ o = oDEBUG_NEXT.val ∨ o = oDEBUG_PREV.val ∨ o = oVCPU.val then .gate
  else if oTIMER_DEADLINE.val ≤ o ∧ o ≤ oTIMER_HEIGHT.val then
    if (m (fld t oTIMER_DEADLINE)).val ≠ 0 then .core (treeCore (m (fld t oTIMER_HEIGHT)))
    else home
  else if (o = oSTATE.val ∨ o = oBLOCK_OBJ.val ∨ o = oBLOCK_BADGE.val ∨ o = oBLOCK_FLAGS.val ∨
      o = oEP_NEXT.val ∨ o = oEP_PREV.val) ∧ QueuedState (m (fld t oSTATE)) then
    .lock (m (fld t oBLOCK_OBJ))
  else home

/-- **The ownership map** (module docstring, rules 1–6). -/
def own (K : KLayout) (m : U64 → U64) (b : U64) : Owner U64 U64 :=
  if h : ∃ c, InNode K c b then .core (Classical.choose h)
  else if h : ∃ p ∈ K.slots, InW p 32 b then .lock (Classical.choose h)
  else if h : ∃ t, K.heap t = some .tcb ∧ InW t (2 ^ 12) b then
    tcbOwner m (Classical.choose h) (b.val - (Classical.choose h).val)
  else if h : ∃ p, (K.heap p = some .ep ∧ InW p (2 ^ 4) b) ∨
      (K.heap p = some .ntfn ∧ InW p (2 ^ 6) b) ∨ (K.heap p = some .reply ∧ InW p (2 ^ 5) b) then
    .lock (Classical.choose h)
  else if h : ∃ p z, K.heap p = some (.sc z) ∧ InW p (2 ^ z) b then
    if b.val = (Classical.choose h).val + 16 then .gate
    else .core (m (fld (Classical.choose h) 16#u64))
  else .gate

/-- Words only the gate writes, for this layout. -/
def GateOnlyK (K : KLayout) (m : U64 → U64) (x : U64) : Prop := PathObl.GateOnly (own K) m x

/-- A word of core `c`'s node is `c`'s (rule 1). -/
theorem own_node {K : KLayout} {m : U64 → U64} {c b : U64} (h : InNode K c b)
    (huniq : ∀ c', InNode K c' b → c' = c) : own K m b = .core c := by
  have hex : ∃ c, InNode K c b := ⟨c, h⟩
  unfold own
  rw [dif_pos hex]
  exact congrArg Owner.core (huniq _ (Classical.choose_spec hex))

end

end Fl4Proofs.P2.OwnMap
