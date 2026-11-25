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
   * The queue links `EP_NEXT`, `EP_PREV` of a thread queued on a receive queue
     or a notification (`STATE` ∈ {3, 6}): `lock <BLOCK_OBJ>`'s; otherwise the
     home core's. State 4 (blocked on send) is not in the list: no local path
     dequeues from or appends to a send queue (`fault` takes an endpoint in
     `EP_RECV` only, ReplyRecv one in `EP_IDLE` only, the timer interrupt's
     `cancel_ipc` runs on a thread in `Recv` only), so beside the gate a
     sender's links are only its home core's.
   * Everything else of the TCB: the home core's, whatever the state: `STATE`,
     `BLOCK_OBJ`, `BLOCK_BADGE`, `BLOCK_FLAGS` of a queued thread too (no local
     path writes them of another core's thread, and an accepted one reads them
     only of its own core's: the queue's owner needs only the links), always
     `REPLY_OBJ`, the fault and lookup-fault words and `IN_QUEUES`. So the timer
     interrupt reads its timer's thread's `STATE` as its own word, whichever
     object that thread may be blocked on. An accepted local path writes or relies on these words only of
     threads of its own core: `fault`/`vm_fault` of the current thread `t`, and
     of `dest` after `schedulable_here(dest)`; ReplyRecv of `t`, and of the
     replied thread `u` after `schedulable_here(u)`; the timer interrupt of the
     current thread and of threads `may_run_here` accepts, or the timer's thread
     `tm` (its `affinity` checked); `TCB_SetTimer` and I/O ports of the caller.
     A path reading them of another core's thread (`dest.REPLY_OBJ`, `u.STATE`,
     `u.FAULT_TYPE`, before the check) declines on the thread's (gate-owned)
     `AFFINITY`. A reply object's lock therefore owns no TCB word: `fault` writes
     `STATE := 5` before `REPLY_OBJ`, which under a lock-of-`REPLY_OBJ` rule
     moved the group to the stale reply object for one write.
4. **Endpoints, reply objects**: `lock <object>`. **Notifications**: bound
   (`BOUND_TCB` ≠ 0), the bound thread's home core (only that core's timer
   path signals it beside the gate); unbound, `lock <object>`; `BOUND_TCB`
   itself is the gate's.
5. **Scheduling contexts**: the core in the SC's `CORE` word (offset 16); the
   `CORE` word itself is gate-owned.
6. **Everything else**: the gate.

`cls K b v`: the value class a racing local path can leave in a word (a CNode
slot's `CAP0`: Null or Frame; every other word its own class), `ko` who may
change it.

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
import Fl4Proofs.P2.SerialSafe
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

/-- Queued on an endpoint's receive queue or a notification. -/
def QueuedState (v : U64) : Prop := v.val = 3 ∨ v.val = 6

/-- TCB words only the gate writes: `AFFINITY`, `DOMAIN`, `MCP`, `PRIO`, `SC`,
`BOUND_NTFN`, `IPC_BUFFER`, `DEBUG_NEXT` / `DEBUG_PREV`, `VCPU`. -/
def GateField (o : Nat) : Prop :=
  o = 3520 ∨ o = 3432 ∨ o = 3440 ∨ o = 3448 ∨ o = 3464 ∨ o = 3368 ∨ o = 3512 ∨ o = 3576 ∨
    o = 3584 ∨ o = 3664

/-- The timer fields `TIMER_DEADLINE` … `TIMER_HEIGHT`. -/
def TimerField (o : Nat) : Prop := 3528 ≤ o ∧ o ≤ 3568

/-- The words `STATE` and `BLOCK_OBJ` decide: the queue links `EP_NEXT` /
`EP_PREV`. -/
def GField (o : Nat) : Prop := o = 3496 ∨ o = 3504

/-- The owner of the queue links. -/
def gOwner (st bo : U64) (home : Owner U64 U64) : Owner U64 U64 :=
  if QueuedState st then .lock bo else home

/-- The owner of the timer group. -/
def tOwner (dl ht : U64) (home : Owner U64 U64) : Owner U64 U64 :=
  if dl.val ≠ 0 then .core (treeCore ht) else home

/-- The owner of the word at offset `o` of the TCB at `t` (rule 3). -/
def tcbOwner (m : U64 → U64) (t : U64) (o : Nat) : Owner U64 U64 :=
  if GateField o then .gate
  else if TimerField o then
    tOwner (m (fld t oTIMER_DEADLINE)) (m (fld t oTIMER_HEIGHT)) (.core (m (fld t oAFFINITY)))
  else if GField o then
    gOwner (m (fld t oSTATE)) (m (fld t oBLOCK_OBJ)) (.core (m (fld t oAFFINITY)))
  else .core (m (fld t oAFFINITY))

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

/-- The owner of the word at offset `o` of the notification at `p` (rule 4):
bound to a TCB, that TCB's home core. -/
def ntfnOwner (K : KLayout) (m : U64 → U64) (p : U64) (o : Nat) : Owner U64 U64 :=
  if o = 24 then .gate
  else if K.heap (m (fld p 24#u64)) = some .tcb then .core (m (fld (m (fld p 24#u64)) oAFFINITY))
  else .lock p

/-- Which object a word lies in (memory-independent). -/
inductive Region where
  | node (c : U64)
  | slot (p : U64)
  | tcb (t : U64)
  | ntfn (p : U64)
  | obj (p : U64)
  | sc (p : U64)
  | none

def region (K : KLayout) (b : U64) : Region :=
  if h : ∃ c, InNode K c b then .node (Classical.choose h)
  else if h : ∃ p ∈ K.slots, InW p 32 b then .slot (Classical.choose h)
  else if h : ∃ t, K.heap t = some .tcb ∧ InW t (2 ^ 12) b then .tcb (Classical.choose h)
  else if h : ∃ p, K.heap p = some .ntfn ∧ InW p (2 ^ 6) b then .ntfn (Classical.choose h)
  else if h : ∃ p, (K.heap p = some .ep ∧ InW p (2 ^ 4) b) ∨
      (K.heap p = some .reply ∧ InW p (2 ^ 5) b) then .obj (Classical.choose h)
  else if h : ∃ p z, K.heap p = some (.sc z) ∧ InW p (2 ^ z) b then .sc (Classical.choose h)
  else .none

/-- **The ownership map** (module docstring, rules 1–6). -/
def own (K : KLayout) (m : U64 → U64) (b : U64) : Owner U64 U64 :=
  match region K b with
  | .node c => .core c
  | .slot p => slotOwner K m p (b.val - p.val)
  | .tcb t => tcbOwner m t (b.val - t.val)
  | .ntfn p => ntfnOwner K m p (b.val - p.val)
  | .obj p => .lock p
  | .sc p => if b.val = p.val + 16 then .gate else .core (m (fld p 16#u64))
  | .none => .gate

/-- Words only the gate writes, for this layout. -/
def GateOnlyK (K : KLayout) (m : U64 → U64) (x : U64) : Prop := PathObl.GateOnly (own K) m x

/-! ## Value classes -/

/-- The class of a CNode slot's `CAP0`: Null/Frame lumped together. Every other
word is its own class (so a TCB's `STATE` and `TIMER_DEADLINE`, whose `ko` is
the thread's home core, are exactly stable for that core). -/
def cls (K : KLayout) (b v : U64) : U64 :=
  match region K b with
  | .slot p => if b = p ∧ ¬ TcbSlot K p ∧ NullOrFrame v then 0#u64 else v
  | _ => v

/-- Who may change a word's class beside the gate: a CNode slot's `CAP0`, the
gate (localinv keeps it Null/Frame); a TCB's `STATE` and `TIMER_DEADLINE`, the
thread's home core (a timer fires beside the gate only on a core that is both
its thread's home and its tree's, and `TCB_SetTimer` needs its target homed
there; another core's tree operations write links only); everything else,
untracked. -/
def ko (K : KLayout) (m : U64 → U64) (b : U64) : Serial.ClsOwner U64 :=
  match region K b with
  | .slot p => if b = p ∧ ¬ TcbSlot K p then .gate else .free
  | .tcb t => if b.val - t.val = 3328 ∨ b.val - t.val = 3528 then .core (m (fld t oAFFINITY))
    else .free
  | _ => .free

/-! ## Where the deciding words lie -/

/-- **Layout facts** [J] (from P1's typed-heap disjointness, `HeapOK`, with the
nodes and capability slots disjoint from the objects and from each other, TCB
slots below offset 192): where the deciding words of an owner lie. -/
structure RegionOK (K : KLayout) : Prop where
  tcb : ∀ t, K.heap t = some .tcb → ∀ off, off = oAFFINITY ∨ off = oSTATE ∨ off = oBLOCK_OBJ ∨
    off = oREPLY_OBJ ∨ off = oTIMER_DEADLINE ∨ off = oTIMER_HEIGHT →
    region K (fld t off) = .tcb t ∧ (fld t off).val - t.val = off.val
  slot : ∀ p ∈ K.slots, region K p = .slot p
  ntfn : ∀ p, K.heap p = some .ntfn →
    region K (fld p 24#u64) = .ntfn p ∧ (fld p 24#u64).val - p.val = 24
  scw : ∀ p b, region K b = .sc p → region K (fld p 16#u64) = .sc p ∧
    (fld p 16#u64).val = p.val + 16
  tcbOf : ∀ t b, region K b = .tcb t → K.heap t = some .tcb
  slotOf : ∀ p b, region K b = .slot p → p ∈ K.slots
  ntfnOf : ∀ p b, region K b = .ntfn p → K.heap p = some .ntfn

theorem oAFF_val : oAFFINITY.val = 3520 := by simp [oAFFINITY]
theorem oSTATE_val : oSTATE.val = 3328 := by simp [oSTATE]
theorem oBOBJ_val : oBLOCK_OBJ.val = 3336 := by simp [oBLOCK_OBJ]
theorem oROBJ_val : oREPLY_OBJ.val = 3360 := by simp [oREPLY_OBJ]
theorem oDL_val : oTIMER_DEADLINE.val = 3528 := by simp [oTIMER_DEADLINE]
theorem oHT_val : oTIMER_HEIGHT.val = 3568 := by simp [oTIMER_HEIGHT]

/-- The owner of a decider word of a TCB, through `region`. -/
theorem own_tcb_at {K : KLayout} (hK : RegionOK K) {t off : U64} (ht : K.heap t = some .tcb)
    (hoff : off = oAFFINITY ∨ off = oSTATE ∨ off = oBLOCK_OBJ ∨ off = oREPLY_OBJ ∨
      off = oTIMER_DEADLINE ∨ off = oTIMER_HEIGHT) (m : U64 → U64) :
    own K m (fld t off) = tcbOwner m t off.val := by
  obtain ⟨hr, ho⟩ := hK.tcb t ht off hoff
  simp only [own, hr, ho]

/-- A TCB's `AFFINITY` word is the gate's. -/
theorem own_aff_gate {K : KLayout} (hK : RegionOK K) {t : U64} (ht : K.heap t = some .tcb)
    (m : U64 → U64) : own K m (fld t oAFFINITY) = .gate := by
  rw [own_tcb_at hK ht (Or.inl rfl), oAFF_val]
  simp [tcbOwner, GateField]

/-- A TCB's `STATE` and `BLOCK_OBJ` are its home core's. -/
theorem own_state_home {K : KLayout} (hK : RegionOK K) {t off : U64} (ht : K.heap t = some .tcb)
    (hoff : off = oSTATE ∨ off = oBLOCK_OBJ) (m : U64 → U64) :
    own K m (fld t off) = .core (m (fld t oAFFINITY)) := by
  have hv : off.val = 3328 ∨ off.val = 3336 := by
    rcases hoff with h | h <;> subst h
    · exact Or.inl oSTATE_val
    · exact Or.inr oBOBJ_val
  rw [own_tcb_at hK ht (by rcases hoff with h | h <;> simp [h])]
  have h1 : ¬ GateField off.val := by simp only [GateField]; omega
  have h2 : ¬ TimerField off.val := by simp only [TimerField]; omega
  have h3 : ¬ GField off.val := by simp only [GField]; omega
  simp only [tcbOwner, if_neg h1, if_neg h2, if_neg h3]

/-- `TIMER_DEADLINE` and `TIMER_HEIGHT` have the timer group's owner. -/
theorem own_timer_at {K : KLayout} (hK : RegionOK K) {t off : U64} (ht : K.heap t = some .tcb)
    (hoff : off = oTIMER_DEADLINE ∨ off = oTIMER_HEIGHT) (m : U64 → U64) {o : Nat}
    (hG : ¬ GateField o) (hT : TimerField o) : own K m (fld t off) = tcbOwner m t o := by
  have hv : off.val = 3528 ∨ off.val = 3568 := by
    rcases hoff with h | h <;> subst h
    · exact Or.inl oDL_val
    · exact Or.inr oHT_val
  rw [own_tcb_at hK ht (by rcases hoff with h | h <;> simp [h])]
  have h1 : ¬ GateField off.val := by simp only [GateField]; omega
  have h2 : TimerField off.val := by simp only [TimerField]; omega
  simp only [tcbOwner, if_neg hG, if_pos hT, if_neg h1, if_pos h2]

/-! ## `MoveHeld` -/

/-- **`MoveHeld` for the ownership map**, from the layout facts: a word that
decides another's owner is the gate's, or whoever holds it may read the words
that decide with it. -/
theorem moveHeld {K : KLayout} (hK : RegionOK K) : Fl4Proofs.P2.Serial.MoveHeld (own K) := by
  intro c hs m m' a v x ha hag hx
  have hna : ∀ {y}, own K m y = .gate → y ≠ a := by
    rintro y hy rfl
    rw [hy] at ha; exact ha
  have hgate : ∀ {y}, own K m y = .gate → m' y = m y := fun hy => hag _ (Or.inr hy)
  have haa : m' a = m a := hag a (Or.inl ha)
  have hupd : ∀ {y}, m' y = m y → Function.update m' a v y = Function.update m a v y := by
    intro y hy
    by_cases hya : y = a
    · subst hya; simp only [Function.update_self]
    · rw [Function.update_of_ne hya, Function.update_of_ne hya, hy]
  cases hR : region K x with
  | node c => simp only [own, hR] at hx; exact absurd rfl hx
  | obj p => simp only [own, hR] at hx; exact absurd rfl hx
  | none => simp only [own, hR] at hx; exact absurd rfl hx
  | slot p =>
    simp only [own, hR] at hx ⊢
    have hap : a = p := by
      by_contra hne
      apply hx
      simp only [slotOwner, Function.update_of_ne (Ne.symm hne)]
    subst hap
    simp only [slotOwner, haa, hupd haa, true_and]
  | sc p =>
    simp only [own, hR] at hx ⊢
    obtain ⟨h16, h16v⟩ := hK.scw p x hR
    have hg : own K m (fld p 16#u64) = .gate := by simp only [own, h16, if_pos h16v]
    simp only [hgate hg, hupd (hgate hg), true_and]
  | ntfn p =>
    exfalso
    simp only [own, hR] at hx
    have hpn := hK.ntfnOf p x hR
    obtain ⟨h24, h24v⟩ := hK.ntfn p hpn
    have hg : own K m (fld p 24#u64) = .gate := by
      simp only [own, h24, h24v, ntfnOwner]; exact if_pos trivial
    simp only [ntfnOwner, Function.update_of_ne (hna hg)] at hx
    by_cases ho : x.val - p.val = 24
    · simp only [if_pos ho] at hx; exact absurd rfl hx
    · simp only [if_neg ho] at hx
      by_cases hB : K.heap (m (fld p 24#u64)) = some .tcb
      · simp only [if_pos hB, Function.update_of_ne (hna (own_aff_gate hK hB m))] at hx
        exact absurd rfl hx
      · simp only [if_neg hB] at hx; exact absurd rfl hx
  | tcb t =>
    have ht := hK.tcbOf t x hR
    have hgA := own_aff_gate hK ht m
    have hA := hgate hgA
    have hA' : Function.update m a v (fld t oAFFINITY) = m (fld t oAFFINITY) :=
      Function.update_of_ne (hna hgA) _ _
    simp only [own, hR] at hx ⊢
    by_cases hG : GateField (x.val - t.val)
    · simp only [tcbOwner, if_pos hG] at hx; exact absurd rfl hx
    by_cases hT : TimerField (x.val - t.val)
    · have hd : a = fld t oTIMER_DEADLINE ∨ a = fld t oTIMER_HEIGHT := by
        by_contra hne
        obtain ⟨h1, h2⟩ := not_or.mp hne
        apply hx
        simp only [tcbOwner, if_neg hG, if_pos hT, hA', Function.update_of_ne (Ne.symm h1),
          Function.update_of_ne (Ne.symm h2)]
      have e : ∀ off, (off = oTIMER_DEADLINE ∨ off = oTIMER_HEIGHT) →
          m' (fld t off) = m (fld t off) := by
        intro off hoff
        apply hag; left
        rw [own_timer_at hK ht hoff m hG hT]
        rcases hd with h | h
        · rw [h, own_timer_at hK ht (Or.inl rfl) m hG hT] at ha; exact ha
        · rw [h, own_timer_at hK ht (Or.inr rfl) m hG hT] at ha; exact ha
      have e1 := e _ (Or.inl rfl)
      have e2 := e _ (Or.inr rfl)
      simp only [tcbOwner, if_neg hG, if_pos hT, hA, e1, e2, hupd hA, hupd e1, hupd e2, true_and]
    by_cases hGF : GField (x.val - t.val)
    · have hd : a = fld t oSTATE ∨ a = fld t oBLOCK_OBJ := by
        by_contra hne
        obtain ⟨h1, h2⟩ := not_or.mp hne
        apply hx
        simp only [tcbOwner, if_neg hG, if_neg hT, if_pos hGF, hA',
          Function.update_of_ne (Ne.symm h1), Function.update_of_ne (Ne.symm h2)]
      have e : ∀ off, (off = oSTATE ∨ off = oBLOCK_OBJ) → m' (fld t off) = m (fld t off) := by
        intro off hoff
        apply hag; left
        rw [own_state_home hK ht hoff m]
        rcases hd with h | h
        · rw [h, own_state_home hK ht (Or.inl rfl) m] at ha; exact ha
        · rw [h, own_state_home hK ht (Or.inr rfl) m] at ha; exact ha
      have e1 := e _ (Or.inl rfl)
      have e2 := e _ (Or.inr rfl)
      simp only [tcbOwner, if_neg hG, if_neg hT, if_pos hGF, hA, e1, e2, hupd hA, hupd e1,
        hupd e2, true_and]
    · simp only [tcbOwner, if_neg hG, if_neg hT, if_neg hGF, hA'] at hx
      exact absurd rfl hx

end

end Fl4Proofs.P2.OwnMap
