/-
P2: **the global ownership map** `own` of `P2/PathObl.lean` (proposal), from
DESIGN §7 "What a local path may write", "Timer ownership" and "Local paths".

`own K m b` gives the owner of kernel word `b` in memory `m`, given `K`, the
data that changes only under the gate: P1's typed heap (`Heap`), the kernel
state base, the number of cores, and the set of capability slots. In order:

1. **Nodes.** A word of core `c`'s node (`ks + 13568 + c * 4288`, size 4288,
   P1's `nodeAt`) is `core c`'s.
2. **Capability slots** (32 bytes: `CAP0`, `CAP1`, `PREV`, `NEXT`). The CDT
   link words are `lock <slot>`'s (localinv writes the links of a frame cap's
   neighbours, TCB slots included). The cap words of a TCB's own slot are the
   gate's. The cap words of a CNode slot are value-dependent: `lock <slot>`'s
   while `CAP0`'s tag (`w0 >> 59`) is 0 (Null) or 13 (Frame), the gate's
   otherwise; localinv beside the gate writes cap words only of Null/Frame
   slots and leaves them Null/Frame, so the owner changes only under the gate.
3. **TCBs** (`tcbOwner`, offsets of `arch/x86_64/layout.rs`, `F = 0xd00`).
   The thread's home core is its `AFFINITY` word.
   * Gate-owned: `AFFINITY`, `DOMAIN`, `MCP`, `PRIO`, `SC`, `BOUND_NTFN`,
     `IPC_BUFFER`, `DEBUG_NEXT` / `DEBUG_PREV`, `VCPU`.
   * Timer fields `TIMER_DEADLINE` … `TIMER_HEIGHT`: armed (deadline ≠ 0), the
     core of its tree, `TIMER_HEIGHT >> 8`; disarmed, the home core.
   * Blocked on an endpoint or notification (`STATE` ∈ {3, 4, 6}): `STATE`,
     `BLOCK_OBJ`, `BLOCK_BADGE`, `BLOCK_FLAGS`, `REPLY_OBJ`, `EP_NEXT`,
     `EP_PREV`, `IN_QUEUES` are `lock <BLOCK_OBJ>`'s.
   * Blocked on reply (`STATE` = 5): `STATE`, `REPLY_OBJ`, the fault and
     lookup-fault words, `IN_QUEUES` are `lock <REPLY_OBJ>`'s.
   * Everything else of the TCB: the home core's.
4. **Endpoints, reply objects**: `lock <object>`. **Notifications**: bound
   (`BOUND_TCB` ≠ 0), the bound thread's home core (only that core's timer
   path signals it beside the gate); unbound, `lock <object>`; `BOUND_TCB`
   itself is the gate's.
5. **Scheduling contexts**: the core in the SC's `CORE` word (offset 16); the
   `CORE` word itself is gate-owned.
6. **Everything else**: the gate.

`cls K b v`: the value class a racing local path can leave in a word (a CNode
slot's `CAP0`: Null or Frame); not needed by `Serial` (speculative reads), kept
as the statement of p2io's value-benign argument.

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

def oREPLY_OBJ : U64 := 3360#u64
def oFAULT_TYPE : U64 := 3376#u64
def oLF_W1 : U64 := 3424#u64
def oIN_QUEUES : U64 := 3592#u64

/-- Blocked on an endpoint (receive or send) or a notification. -/
def QueuedState (v : U64) : Prop := v.val = 3 ∨ v.val = 4 ∨ v.val = 6

/-- Blocked on reply. -/
def ReplyState (v : U64) : Prop := v.val = 5

/-- The owner of the word at offset `o` of the TCB at `t` (rule 3). -/
def tcbOwner (m : U64 → U64) (t : U64) (o : Nat) : Owner U64 U64 :=
  let home : Owner U64 U64 := .core (m (fld t oAFFINITY))
  let st := m (fld t oSTATE)
  if o = oAFFINITY.val ∨ o = oDOMAIN.val ∨ o = oMCP.val ∨ o = oPRIO.val ∨ o = oSC.val ∨
      o = oBOUND_NTFN.val ∨ o = oIPC_BUFFER.val ∨ o = oDEBUG_NEXT.val ∨ o = oDEBUG_PREV.val ∨
      o = oVCPU.val then .gate
  else if oTIMER_DEADLINE.val ≤ o ∧ o ≤ oTIMER_HEIGHT.val then
    if (m (fld t oTIMER_DEADLINE)).val ≠ 0 then .core (treeCore (m (fld t oTIMER_HEIGHT)))
    else home
  else if (o = oSTATE.val ∨ o = oBLOCK_OBJ.val ∨ o = oBLOCK_BADGE.val ∨ o = oBLOCK_FLAGS.val ∨
      o = oREPLY_OBJ.val ∨ o = oEP_NEXT.val ∨ o = oEP_PREV.val ∨ o = oIN_QUEUES.val) ∧
      QueuedState st then
    .lock (m (fld t oBLOCK_OBJ))
  else if (o = oSTATE.val ∨ o = oREPLY_OBJ.val ∨ (oFAULT_TYPE.val ≤ o ∧ o ≤ oLF_W1.val) ∨
      o = oIN_QUEUES.val) ∧ ReplyState st then
    .lock (m (fld t oREPLY_OBJ))
  else home

/-- A slot word's tag: Null (0) or Frame (13). -/
def NullOrFrame (w : U64) : Prop := w.val / 2 ^ 59 = 0 ∨ w.val / 2 ^ 59 = 13

/-- The slot at `p` is one of a TCB's own slots. -/
def TcbSlot (K : KLayout) (p : U64) : Prop := ∃ t, K.heap t = some .tcb ∧ InW t (2 ^ 12) p

/-- The owner of the word at offset `o` of the slot at `p` (rule 2). -/
def slotOwner (K : KLayout) (m : U64 → U64) (p : U64) (o : Nat) : Owner U64 U64 :=
  if 16 ≤ o then .lock p
  else if TcbSlot K p then .gate
  else if NullOrFrame (m p) then .lock p
  else .gate

/-- The owner of the word at offset `o` of the notification at `p` (rule 4). -/
def ntfnOwner (m : U64 → U64) (p : U64) (o : Nat) : Owner U64 U64 :=
  if o = 24 then .gate
  else if (m (fld p 24#u64)).val ≠ 0 then .core (m (fld (m (fld p 24#u64)) oAFFINITY))
  else .lock p

/-- **The ownership map** (module docstring, rules 1–6). -/
def own (K : KLayout) (m : U64 → U64) (b : U64) : Owner U64 U64 :=
  if h : ∃ c, InNode K c b then .core (Classical.choose h)
  else if h : ∃ p ∈ K.slots, InW p 32 b then
    slotOwner K m (Classical.choose h) (b.val - (Classical.choose h).val)
  else if h : ∃ t, K.heap t = some .tcb ∧ InW t (2 ^ 12) b then
    tcbOwner m (Classical.choose h) (b.val - (Classical.choose h).val)
  else if h : ∃ p, K.heap p = some .ntfn ∧ InW p (2 ^ 6) b then
    ntfnOwner m (Classical.choose h) (b.val - (Classical.choose h).val)
  else if h : ∃ p, (K.heap p = some .ep ∧ InW p (2 ^ 4) b) ∨
      (K.heap p = some .reply ∧ InW p (2 ^ 5) b) then
    .lock (Classical.choose h)
  else if h : ∃ p z, K.heap p = some (.sc z) ∧ InW p (2 ^ z) b then
    if b.val = (Classical.choose h).val + 16 then .gate
    else .core (m (fld (Classical.choose h) 16#u64))
  else .gate

/-- The value class of `Serial`'s class reads (module docstring). -/
def cls (K : KLayout) (b v : U64) : Prop := b ∈ K.slots → ¬ TcbSlot K b → NullOrFrame v

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
