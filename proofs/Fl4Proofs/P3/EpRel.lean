/-
P3 (DESIGN.md §9), endpoints: the state relation.

FL4's endpoint (layout.rs `ep`, 16 bytes) is two words: the queue head and
the queue end with the state (`EP_IDLE` 0, `EP_SEND` 1, `EP_RECV` 2) in bits
0-1. The spec's (l4v Structures_A `endpoint`) is `IdleEP | SendEP q |
RecvEP q`.

Ghost state: `T` the TCB addresses, `E` the endpoint addresses, `R` the
reply-object addresses, and `B` the mapped IPC-buffer words: pairs `(w, p)`
of an FL4 kernel word address `w` and the spec's (physical) address `p` of
the same user word. Hypotheses on them (`EPlaced`, a P1 well-typed-heap
invariant to come): TCBs are placed (`TcbPlaced`), endpoints are 16-byte
and replies 32-byte aligned, nonzero, do not wrap; TCBs, endpoints and
replies do not overlap; buffer words are aligned, lie outside every kernel
object, and `w ↦ p` is injective.

The relation (`EpStateRel T E R B m σ`, on memory `m`):

* every `e ∈ E` is an endpoint `x` in the spec's heap with `EpObjRel`:
  idle ↔ state 0 and the queue (P1 `QueueRel`, `Ep` links) is empty;
  `SendEP q` ↔ state 1, the queue holds TCBs `xs ≠ []`, `q = xs`, each with
  state word 4 (`TS_BLOCKED_ON_SEND`) and block object `e`; `RecvEP q` the
  same with state 2 and state word 3 (`TS_BLOCKED_ON_RECV`);
* every `r ∈ R` is a reply object whose `reply_tcb` is the TCB word (0 ↔
  `None`); `reply_sc` is not related here: it is the SC subsystem's call
  stack, related by `CallRel` (ScCall.lean) together with `sc_replies` and
  the replies' next/prev chain;
* every `t ∈ T` is a TCB `x` with `TcbRelE`:
  - the state word codes `tcb_state` (`tsCode`, as for notifications);
  - for `BlockedOnSend e d` / `BlockedOnReceive e r d`, the block-object word
    is `e`; for `BlockedOnSend`, the block-badge word is `sender_badge` and
    the block-flags word is `flagsOf d` (bit 0 canGrant, 1 canGrantReply, 2
    isCall); for `BlockedOnReceive _ r _`, the reply word is `r` (0 ↔ `None`,
    and a reply of `R`); for `BlockedOnReply r`, the reply word is `r`;
  - all 24 registers of the saved user context (`regIdx`: FL4's register
    numbering, layout.rs `reg`);
  - the priority, the fault (`fault_type` 0 ↔ `None`, 5 ↔ a timeout fault)
    and the bound notification (0 ↔ `None`);
* every `(w, p) ∈ B`: the word at `w` is the spec's user word at `p`
  (`loadWordAt`, X64 `loadWord`'s byte order).

The scheduling-context field of a TCB is not related here (it belongs to the
scheduler/SC relation `SR`; SC donation is out of scope).

The relation reads memory only in the footprint `EFoot` and the spec's state
only through `KView`, so it is preserved by any change outside them
(`EpStateRel.frame`).
-/
import Fl4Proofs.P3.Ntfn
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

/-! ## TCB words -/

/-- The block-badge word of the TCB at `t` (layout.rs `tcb::BLOCK_BADGE`). -/
def tBadgeA (t : U64) : U64 := core.num.U64.wrapping_add t 3344#u64
/-- The block-flags word (`tcb::BLOCK_FLAGS`). -/
def tFlagsA (t : U64) : U64 := core.num.U64.wrapping_add t 3352#u64
/-- The reply-object word (`tcb::REPLY_OBJ`). -/
def tReplyA (t : U64) : U64 := core.num.U64.wrapping_add t 3360#u64
/-- The bound-notification word (`tcb::BOUND_NTFN`). -/
def tBoundA (t : U64) : U64 := core.num.U64.wrapping_add t 3368#u64
/-- The fault-type word (`tcb::FAULT_TYPE`). -/
def tFaultA (t : U64) : U64 := core.num.U64.wrapping_add t 3376#u64
/-- The fault words of the TCB at `t` (`tcb::FAULT_W0..2`, `LF_TYPE`,
`LF_W0`, `LF_W1`). -/
def tFw0A (t : U64) : U64 := core.num.U64.wrapping_add t 3384#u64
def tFw1A (t : U64) : U64 := core.num.U64.wrapping_add t 3392#u64
def tFw2A (t : U64) : U64 := core.num.U64.wrapping_add t 3400#u64
def tLfA (t : U64) : U64 := core.num.U64.wrapping_add t 3408#u64
def tLf0A (t : U64) : U64 := core.num.U64.wrapping_add t 3416#u64
def tLf1A (t : U64) : U64 := core.num.U64.wrapping_add t 3424#u64
/-- Register `i` of the saved user context of the TCB at `t`
(`Tcb::reg`/`set_reg`). -/
def regA (t i : U64) : U64 :=
  core.num.U64.wrapping_add (core.num.U64.wrapping_add t layout.tcb.REGS) (core.num.U64.wrapping_mul i 8#u64)
/-- The TCB word of the reply object at `r` (`reply::TCB`). -/
def rTcbA (r : U64) : U64 := core.num.U64.wrapping_add r layout.reply.TCB

theorem regA_val {t i : U64} (ht : TcbAddr t) (hi : i.val < 24) : (regA t i).val = t.val + 256 + 8 * i.val := by
  have := ht.fits
  unfold regA layout.tcb.REGS
  have hs : UScalar.size UScalarTy.U64 = 2 ^ 64 := by simp [U64.size_def, U64.numBits]
  have h1 : (256#u64 : U64).val = 256 := rfl
  have h2 : (8#u64 : U64).val = 8 := rfl
  rw [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq,
    hs, h1, h2]
  have : (i.val * 8) % 2 ^ 64 = i.val * 8 := Nat.mod_eq_of_lt (by omega)
  rw [this]
  have : (t.val + 256) % 2 ^ 64 = t.val + 256 := Nat.mod_eq_of_lt (by omega)
  rw [this, Nat.mod_eq_of_lt (by omega)]
  omega

theorem rTcbA_val (r : U64) : (rTcbA r).val = r.val := by
  unfold rTcbA layout.reply.TCB
  rw [core.num.U64.wrapping_add_val_eq]
  have : (0#u64 : U64).val = 0 := rfl
  rw [this, Nat.add_zero]
  exact Nat.mod_eq_of_lt (by have := r.hBounds; simpa [U64.size_def, U64.numBits] using this)

/-- FL4's register number of a spec register (layout.rs `reg`). -/
def regIdx : Fl4Spec.Register → U64
  | .rdi => 0#u64 | .rsi => 1#u64 | .rax => 2#u64 | .rbx => 3#u64 | .rbp => 4#u64
  | .r12 => 5#u64 | .r13 => 6#u64 | .r14 => 7#u64 | .rdx => 8#u64 | .r10 => 9#u64
  | .r8 => 10#u64 | .r9 => 11#u64 | .r15 => 12#u64 | .flags => 13#u64 | .nextIP => 14#u64
  | .errorRegister => 15#u64 | .rsp => 16#u64 | .faultIP => 17#u64 | .r11 => 18#u64
  | .rcx => 19#u64 | .cs => 20#u64 | .ss => 21#u64 | .fsBase => 22#u64 | .gsBase => 23#u64

/-- The inverse of `regIdx`. -/
def idxReg : Nat → Fl4Spec.Register
  | 0 => .rdi | 1 => .rsi | 2 => .rax | 3 => .rbx | 4 => .rbp | 5 => .r12 | 6 => .r13
  | 7 => .r14 | 8 => .rdx | 9 => .r10 | 10 => .r8 | 11 => .r9 | 12 => .r15 | 13 => .flags
  | 14 => .nextIP | 15 => .errorRegister | 16 => .rsp | 17 => .faultIP | 18 => .r11
  | 19 => .rcx | 20 => .cs | 21 => .ss | 22 => .fsBase | _ => .gsBase

theorem idxReg_regIdx (r : Fl4Spec.Register) : idxReg (regIdx r).val = r := by cases r <;> rfl

theorem regIdx_lt (r : Fl4Spec.Register) : (regIdx r).val < 24 := by cases r <;> decide

theorem regIdx_inj {r r' : Fl4Spec.Register} (h : (regIdx r).val = (regIdx r').val) : r = r' := by
  rw [← idxReg_regIdx r, ← idxReg_regIdx r', h]

theorem regIdx_badge : regIdx Fl4Spec.badge_register = layout.reg.BADGE := by
  unfold layout.reg.BADGE layout.reg.RDI; rfl
theorem regIdx_msgInfo : regIdx Fl4Spec.msg_info_register = layout.reg.MSG_INFO := by
  unfold layout.reg.MSG_INFO layout.reg.RSI; rfl

theorem badgeRegA_eq_regA (t : U64) : badgeRegA t = regA t (regIdx Fl4Spec.badge_register) := by
  rw [regIdx_badge]; rfl

/-! ## Store specs of the field accessors -/

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

@[step] theorem obj.Tcb.block_badge.spec (s : S) (t : obj.Tcb) :
    obj.Tcb.block_badge st t s ⦃ v => v = L.mem s (tBadgeA t) ⦄ := by
  unfold obj.Tcb.block_badge; step*; simp_all [tBadgeA]
@[step] theorem obj.Tcb.set_block_badge.spec (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_block_badge st t s v ⦃ s' => s' = L.wr s (tBadgeA t) v ⦄ := by
  unfold obj.Tcb.set_block_badge; step*; simp_all [tBadgeA]
@[step] theorem obj.Tcb.block_flags.spec (s : S) (t : obj.Tcb) :
    obj.Tcb.block_flags st t s ⦃ v => v = L.mem s (tFlagsA t) ⦄ := by
  unfold obj.Tcb.block_flags; step*; simp_all [tFlagsA]
@[step] theorem obj.Tcb.set_block_flags.spec (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_block_flags st t s v ⦃ s' => s' = L.wr s (tFlagsA t) v ⦄ := by
  unfold obj.Tcb.set_block_flags; step*; simp_all [tFlagsA]
@[step] theorem obj.Tcb.reply_obj.spec (s : S) (t : obj.Tcb) :
    obj.Tcb.reply_obj st t s ⦃ v => v = L.mem s (tReplyA t) ⦄ := by
  unfold obj.Tcb.reply_obj; step*; simp_all [tReplyA]
@[step] theorem obj.Tcb.set_reply_obj.spec (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_reply_obj st t s v ⦃ s' => s' = L.wr s (tReplyA t) v ⦄ := by
  unfold obj.Tcb.set_reply_obj; step*; simp_all [tReplyA]
@[step] theorem obj.Tcb.bound_ntfn.spec (s : S) (t : obj.Tcb) :
    obj.Tcb.bound_ntfn st t s ⦃ v => v = L.mem s (tBoundA t) ⦄ := by
  unfold obj.Tcb.bound_ntfn; step*; simp_all [tBoundA]
@[step] theorem obj.Tcb.fault_type.spec (s : S) (t : obj.Tcb) :
    obj.Tcb.fault_type st t s ⦃ v => v = L.mem s (tFaultA t) ⦄ := by
  unfold obj.Tcb.fault_type; step*; simp_all [tFaultA]
@[step] theorem obj.Tcb.fault_w0.spec (s : S) (t : obj.Tcb) :
    obj.Tcb.fault_w0 st t s ⦃ v => v = L.mem s (tFw0A t) ⦄ := by
  unfold obj.Tcb.fault_w0; step*; simp_all [tFw0A]
@[step] theorem obj.Tcb.fault_w1.spec (s : S) (t : obj.Tcb) :
    obj.Tcb.fault_w1 st t s ⦃ v => v = L.mem s (tFw1A t) ⦄ := by
  unfold obj.Tcb.fault_w1; step*; simp_all [tFw1A]
@[step] theorem obj.Tcb.fault_w2.spec (s : S) (t : obj.Tcb) :
    obj.Tcb.fault_w2 st t s ⦃ v => v = L.mem s (tFw2A t) ⦄ := by
  unfold obj.Tcb.fault_w2; step*; simp_all [tFw2A]
@[step] theorem obj.Tcb.lf_type.spec (s : S) (t : obj.Tcb) :
    obj.Tcb.lf_type st t s ⦃ v => v = L.mem s (tLfA t) ⦄ := by
  unfold obj.Tcb.lf_type; step*; simp_all [tLfA]
@[step] theorem obj.Tcb.lf_w0.spec (s : S) (t : obj.Tcb) :
    obj.Tcb.lf_w0 st t s ⦃ v => v = L.mem s (tLf0A t) ⦄ := by
  unfold obj.Tcb.lf_w0; step*; simp_all [tLf0A]
@[step] theorem obj.Tcb.lf_w1.spec (s : S) (t : obj.Tcb) :
    obj.Tcb.lf_w1 st t s ⦃ v => v = L.mem s (tLf1A t) ⦄ := by
  unfold obj.Tcb.lf_w1; step*; simp_all [tLf1A]
@[step] theorem obj.Tcb.reg.spec (s : S) (t : obj.Tcb) (i : U64) :
    obj.Tcb.reg st t s i ⦃ v => v = L.mem s (regA t i) ⦄ := by
  unfold obj.Tcb.reg; step*; simp_all [regA]
@[step] theorem obj.Tcb.set_reg.spec (s : S) (t : obj.Tcb) (i v : U64) :
    obj.Tcb.set_reg st t s i v ⦃ s' => s' = L.wr s (regA t i) v ⦄ := by
  unfold obj.Tcb.set_reg; step*; simp_all [regA]
@[step] theorem obj.Reply.tcb.spec (s : S) (r : obj.Reply) :
    obj.Reply.tcb st r s ⦃ v => v = L.mem s (rTcbA r) ⦄ := by
  unfold obj.Reply.tcb; step*; simp_all [rTcbA]
@[step] theorem obj.Reply.set_tcb.spec (s : S) (r : obj.Reply) (v : U64) :
    obj.Reply.set_tcb st r s v ⦃ s' => s' = L.wr s (rTcbA r) v ⦄ := by
  unfold obj.Reply.set_tcb; step*; simp_all [rTcbA]

end

/-! ## Placement -/

/-- The words of the TCB at `t` the relation reads, as offsets (all but the
`Ep` links): state, block object, block badge, block flags, reply object,
bound notification, fault type, priority, and the registers. -/
def TOffN (k : Nat) : Prop :=
  k = 3328 ∨ k = 3336 ∨ k = 3344 ∨ k = 3352 ∨ k = 3360 ∨ k = 3368 ∨ k = 3376 ∨ k = 3448 ∨
    (256 ≤ k ∧ k < 448) ∨ k = 3384 ∨ k = 3392 ∨ k = 3400 ∨ k = 3408 ∨ k = 3416 ∨ k = 3424

/-- The words of a TCB the endpoint code writes (not the bound
notification, the fault and the priority). -/
def TWOffN (k : Nat) : Prop :=
  k = 3328 ∨ k = 3336 ∨ k = 3344 ∨ k = 3352 ∨ k = 3360 ∨ (256 ≤ k ∧ k < 448)

/-- A field word (not a link) of the TCB at `t`. -/
def TF (t a : U64) : Prop := t.val ≤ a.val ∧ TOffN (a.val - t.val)
/-- A written field word of the TCB at `t`. -/
def TWF (t a : U64) : Prop := t.val ≤ a.val ∧ TWOffN (a.val - t.val)
/-- An `Ep` link word of the TCB at `t`. -/
def TL (t a : U64) : Prop := a.val = t.val + 3496 ∨ a.val = t.val + 3504

/-- Hypothesis on the ghost sets (see the module docstring). -/
structure EPlaced (T E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) : Prop where
  tcb : TcbPlaced T
  ep : ∀ e ∈ E, e.val % 16 = 0 ∧ e.val ≠ 0 ∧ e.val + 16 ≤ 2 ^ 64
  rep : ∀ r ∈ R, r.val % 32 = 0 ∧ r.val ≠ 0 ∧ r.val + 32 ≤ 2 ^ 64
  et : ∀ e ∈ E, ∀ t ∈ T, t.val + 4096 ≤ e.val ∨ e.val + 16 ≤ t.val
  rt : ∀ r ∈ R, ∀ t ∈ T, t.val + 4096 ≤ r.val ∨ r.val + 32 ≤ t.val
  er : ∀ e ∈ E, ∀ r ∈ R, r.val + 32 ≤ e.val ∨ e.val + 16 ≤ r.val
  balign : ∀ wp ∈ B, wp.1.val % 8 = 0 ∧ wp.2.toNat % 8 = 0
  bt : ∀ wp ∈ B, ∀ t ∈ T, wp.1.val < t.val ∨ t.val + 4096 ≤ wp.1.val
  be : ∀ wp ∈ B, ∀ e ∈ E, wp.1.val < e.val ∨ e.val + 16 ≤ wp.1.val
  br : ∀ wp ∈ B, ∀ r ∈ R, wp.1.val < r.val ∨ r.val + 32 ≤ wp.1.val
  binj : ∀ wp ∈ B, ∀ wq ∈ B, (wp.1 = wq.1 ↔ wp.2 = wq.2)

theorem EPlaced.epPlaced {T E R : Set U64} {B} (hP : EPlaced T E R B) {e : U64} (he : e ∈ E) : EpPlaced T e :=
  ⟨by have := (hP.ep e he).1; omega, (hP.ep e he).2.2, fun t ht => by have := hP.et e he t ht; omega⟩

/-! ## The relation -/

section Rel
open Fl4Spec

/-- The block-flags word for a sender payload (endpoint.rs `FLAG_*`). -/
def flagsOf (d : SenderPayload) : U64 :=
  ((if d.senderCanGrant then 1#u64 else 0#u64) ||| (if d.senderCanGrantReply then 2#u64 else 0#u64)) |||
    (if d.senderIsCall then 4#u64 else 0#u64)

/-- X64 `loadWord` on a byte memory, as a function. -/
def loadWordAt (um : Word → Word8) (p : Word) : Word :=
  wordRcat ((intUpto 0 7).map fun i => um (p + (7 - BitVec.ofInt 64 i)))

/-- A lookup failure, from the lookup-failure words (type, `w0`, `w1`;
error.rs `LookupFault::encode`). -/
def LfRel (lt l0 l1 : U64) : LookupFailure → Prop
  | .invalidRoot => lt = 1#u64
  | .missingCapability n => lt = 2#u64 ∧ l0.val = n
  | .depthMismatch bl bf => lt = 3#u64 ∧ l0.val = bf ∧ l1.val = bl
  | .guardMismatch bl g => lt = 4#u64 ∧ l0.bv = ofBl g ∧ (l1.val >>> 8) = bl ∧ l1.val % 256 = g.length

/-- A fault, from the fault words (type, `w0`, `w1`, `w2`, and the
lookup-failure words; faults.rs `set_fault`). A VM fault's l4v arch data is
`[instruction, fsr]` (`handle_vm_fault`), FL4's `w2` and `w1`. -/
def FaultRel' (ty w0 w1 w2 lt l0 l1 : U64) : Option Fault → Prop
  | none => ty = 0#u64
  | some (.capFault a rp lf) => ty = 1#u64 ∧ w0.bv = a ∧ w1 = (if rp then 1#u64 else 0#u64) ∧ LfRel lt l0 l1 lf
  | some (.unknownSyscallException n) => ty = 2#u64 ∧ w0.bv = n
  | some (.userException e c) => ty = 3#u64 ∧ w0.bv = e ∧ w1.bv = c
  | some (.timeout b) => ty = 5#u64 ∧ w0.bv = b
  | some (.archFault (.vmFault a d)) => ty = 6#u64 ∧ w0.bv = a ∧ d = [w2.bv, w1.bv]

/-- The fault of the TCB at `t`. -/
def FaultRel (m : U64 → U64) (t : U64) (f : Option Fault) : Prop :=
  FaultRel' (m (tFaultA t)) (m (tFw0A t)) (m (tFw1A t)) (m (tFw2A t)) (m (tLfA t)) (m (tLf0A t)) (m (tLf1A t)) f

/-- The TCB at `t` and the spec's TCB `x`. -/
structure TcbRelE (R : Set U64) (m : U64 → U64) (t : U64) (x : Tcb) : Prop where
  st : (m (tStA t)).val = tsCode x.tcbState
  blk : ∀ e, epBlocked x.tcbState = some e → (m (tBlockA t)).bv = e
  send : ∀ e d, x.tcbState = .blockedOnSend e d → (m (tBadgeA t)).bv = d.senderBadge ∧ m (tFlagsA t) = flagsOf d
  recv : ∀ e r d, x.tcbState = .blockedOnReceive e r d → optRef (m (tReplyA t)) = r ∧
    (r ≠ none → m (tReplyA t) ∈ R)
  reply : ∀ r, x.tcbState = .blockedOnReply r → (m (tReplyA t)).bv = r
  regs : ∀ r, (m (regA t (regIdx r))).bv = x.tcbArch.tcbContext.userRegs r
  prio : (m (prioA t)).val = x.tcbPriority.toNat
  fault0 : m (tFaultA t) = 0#u64 ↔ x.tcbFault = none
  faultT : m (tFaultA t) = 5#u64 ↔ ∃ b, x.tcbFault = some (.timeout b)
  bound : x.tcbBoundNotification = optRef (m (tBoundA t))
  faultR : FaultRel m t x.tcbFault

/-- A TCB queued on the endpoint at `e` with state word `k`. -/
def QueuedOn (m : U64 → U64) (e : U64) (k : Nat) (y : U64) : Prop := (m (tStA y)).val = k ∧ m (tBlockA y) = e

/-- The endpoint at `e` in memory `m` and the spec's endpoint `x`. -/
def EpObjRel (m : U64 → U64) (T : Set U64) (e : U64) : Endpoint → Prop
  | .idleEP => stOf m e = 0#u64 ∧ QueueRel m T .Ep (qOf m e) []
  | .sendEP q => stOf m e = 1#u64 ∧ ∃ xs : List U64, xs ≠ [] ∧ q = xs.map UScalar.bv ∧
      QueueRel m T .Ep (qOf m e) xs ∧ ∀ y ∈ xs, QueuedOn m e 4 y
  | .recvEP q => stOf m e = 2#u64 ∧ ∃ xs : List U64, xs ≠ [] ∧ q = xs.map UScalar.bv ∧
      QueueRel m T .Ep (qOf m e) xs ∧ ∀ y ∈ xs, QueuedOn m e 3 y

/-- The endpoint part of the state relation. -/
structure EpStateRel {Z : Type} (T E R : Set U64) (B : Set (U64 × Word)) (m : U64 → U64) (σ : State Z) :
    Prop where
  ep : ∀ e ∈ E, ∃ x, σ.kheap e.bv = some (.endpoint x) ∧ EpObjRel m T e x
  reply : ∀ r ∈ R, ∃ x, σ.kheap r.bv = some (.reply x) ∧ x.replyTcb = optRef (m (rTcbA r))
  tcb : ∀ t ∈ T, ∃ x, σ.kheap t.bv = some (.tcb x) ∧ TcbRelE R m t x
  buf : ∀ wp ∈ B, (m wp.1).bv = loadWordAt σ.machineState.underlyingMemory wp.2

/-- The words the relation reads. -/
def EFoot (T E R : Set U64) (B : Set (U64 × Word)) (a : U64) : Prop :=
  (∃ e ∈ E, a.val = e.val ∨ a.val = e.val + 8) ∨ (∃ r ∈ R, a.val = r.val) ∨
    (∃ t ∈ T, TF t a ∨ TL t a) ∨ (∃ wp ∈ B, a = wp.1)

/-- The words the endpoint code writes. -/
def EWrite (T E R : Set U64) (B : Set (U64 × Word)) (a : U64) : Prop :=
  (∃ e ∈ E, a.val = e.val ∨ a.val = e.val + 8) ∨ (∃ r ∈ R, a.val = r.val) ∨
    (∃ t ∈ T, TWF t a ∨ TL t a) ∨ (∃ wp ∈ B, a = wp.1)

theorem EWrite.foot {T E R : Set U64} {B} {a : U64} (h : EWrite T E R B a) : EFoot T E R B a := by
  rcases h with h | h | ⟨t, ht, h | h⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inl ⟨h.1, ?_⟩⟩))
    have := h.2; unfold TWOffN at this; unfold TOffN; omega
  · exact Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inr h⟩))
  · exact Or.inr (Or.inr (Or.inr h))

/-- What the relation reads of the spec's state: endpoints, the TCB of
replies, TCBs' state, registers, priority, fault and bound notification, and
user memory. -/
def KView {Z : Type} (σ σ' : State Z) : Prop :=
  (∀ p x, σ.kheap p = some (.endpoint x) → σ'.kheap p = some (.endpoint x)) ∧
  (∀ p x, σ.kheap p = some (.reply x) → ∃ y, σ'.kheap p = some (.reply y) ∧ y.replyTcb = x.replyTcb) ∧
  (∀ p x, σ.kheap p = some (.tcb x) → ∃ y, σ'.kheap p = some (.tcb y) ∧
    y.tcbState = x.tcbState ∧ y.tcbArch.tcbContext.userRegs = x.tcbArch.tcbContext.userRegs ∧
    y.tcbPriority = x.tcbPriority ∧ y.tcbFault = x.tcbFault ∧ y.tcbBoundNotification = x.tcbBoundNotification) ∧
  σ'.machineState.underlyingMemory = σ.machineState.underlyingMemory

/-- The abstract state `a` with heap `kh` and user memory `um`. -/
def withKM (a : AbstractState) (kh : ObjRef → Option KernelObject) (um : Word → Word8) : AbstractState :=
  { a with kheap := kh, machineState := { a.machineState with underlyingMemory := um } }

/-- What the endpoint code changes in the spec's state: endpoints, the TCB of
replies, the state and user context of TCBs, and user memory; nothing
else. -/
def EpStep {Z : Type} (σ σ' : State Z) : Prop :=
  σ'.exst = σ.exst ∧
  σ'.toAbstractState = withKM σ.toAbstractState σ'.kheap σ'.machineState.underlyingMemory ∧
  ∀ p, σ'.kheap p = σ.kheap p ∨
    (∃ x y, σ.kheap p = some (.endpoint x) ∧ σ'.kheap p = some (.endpoint y)) ∨
    (∃ x y, σ.kheap p = some (.reply x) ∧ σ'.kheap p = some (.reply y) ∧ y.replySc = x.replySc) ∨
    (∃ x y, σ.kheap p = some (.tcb x) ∧ σ'.kheap p = some (.tcb y) ∧
      y = { x with tcbState := y.tcbState, tcbArch := y.tcbArch })

end Rel

/-! ## Addresses -/

/-- Memory that agrees on the words `P`. -/
def Agree (m m' : U64 → U64) (P : U64 → Prop) : Prop := ∀ a, Aligned a → P a → m' a = m a

theorem Agree.trans {m₁ m₂ m₃ : U64 → U64} {P : U64 → Prop} (h₁ : Agree m₁ m₂ P) (h₂ : Agree m₂ m₃ P) :
    Agree m₁ m₃ P := fun a ha hp => (h₂ a ha hp).trans (h₁ a ha hp)
theorem Agree.mono {m m' : U64 → U64} {P Q : U64 → Prop} (h : Agree m m' P) (hPQ : ∀ a, Q a → P a) :
    Agree m m' Q := fun a ha hq => h a ha (hPQ a hq)
theorem Agree.rfl' {m : U64 → U64} {P : U64 → Prop} : Agree m m P := fun _ _ _ => rfl

theorem tw_val {t K : U64} (ht : TcbAddr t) (hK : K.val < 4096) :
    (core.num.U64.wrapping_add t K).val = t.val + K.val := tfield_val ht hK

/-- A field word at offset `K`: aligned and a field. -/
theorem tf_addr {t K : U64} (ht : TcbAddr t) (hK : TOffN K.val) (h8 : K.val % 8 = 0) :
    Aligned (core.num.U64.wrapping_add t K) ∧ TF t (core.num.U64.wrapping_add t K) := by
  have hK' : K.val < 4096 := by unfold TOffN at hK; omega
  have := ht.align
  refine ⟨?_, ?_, ?_⟩
  · unfold Aligned; rw [tw_val ht hK']; omega
  · rw [tw_val ht hK']; omega
  · rw [tw_val ht hK', Nat.add_sub_cancel_left]; exact hK

theorem regA_tf {t i : U64} (ht : TcbAddr t) (hi : i.val < 24) : Aligned (regA t i) ∧ TF t (regA t i) := by
  have := ht.align
  refine ⟨?_, ?_, ?_⟩
  · unfold Aligned; rw [regA_val ht hi]; omega
  · rw [regA_val ht hi]; omega
  · rw [regA_val ht hi]; unfold TOffN; omega

section
variable {t : U64} (ht : TcbAddr t)
include ht
theorem a_st : Aligned (tStA t) ∧ TF t (tStA t) := by rw [tStA_eq]; exact tf_addr ht (by unfold TOffN; simp) (by simp)
theorem a_blk : Aligned (tBlockA t) ∧ TF t (tBlockA t) := by
  rw [tBlockA_eq]; exact tf_addr ht (by unfold TOffN; simp) (by simp)
theorem a_badge : Aligned (tBadgeA t) ∧ TF t (tBadgeA t) := tf_addr ht (by unfold TOffN; simp) (by simp)
theorem a_flags : Aligned (tFlagsA t) ∧ TF t (tFlagsA t) := tf_addr ht (by unfold TOffN; simp) (by simp)
theorem a_reply : Aligned (tReplyA t) ∧ TF t (tReplyA t) := tf_addr ht (by unfold TOffN; simp) (by simp)
theorem a_bound : Aligned (tBoundA t) ∧ TF t (tBoundA t) := tf_addr ht (by unfold TOffN; simp) (by simp)
theorem a_fault : Aligned (tFaultA t) ∧ TF t (tFaultA t) := tf_addr ht (by unfold TOffN; simp) (by simp)
theorem a_fw0 : Aligned (tFw0A t) ∧ TF t (tFw0A t) := tf_addr ht (by unfold TOffN; simp) (by simp)
theorem a_fw1 : Aligned (tFw1A t) ∧ TF t (tFw1A t) := tf_addr ht (by unfold TOffN; simp) (by simp)
theorem a_fw2 : Aligned (tFw2A t) ∧ TF t (tFw2A t) := tf_addr ht (by unfold TOffN; simp) (by simp)
theorem a_lf : Aligned (tLfA t) ∧ TF t (tLfA t) := tf_addr ht (by unfold TOffN; simp) (by simp)
theorem a_lf0 : Aligned (tLf0A t) ∧ TF t (tLf0A t) := tf_addr ht (by unfold TOffN; simp) (by simp)
theorem a_lf1 : Aligned (tLf1A t) ∧ TF t (tLf1A t) := tf_addr ht (by unfold TOffN; simp) (by simp)
theorem a_prio : Aligned (prioA t) ∧ TF t (prioA t) := by
  rw [prioA_eq']; exact tf_addr ht (by unfold TOffN; simp) (by simp)
theorem a_reg (r : Fl4Spec.Register) : Aligned (regA t (regIdx r)) ∧ TF t (regA t (regIdx r)) :=
  regA_tf ht (regIdx_lt r)
theorem a_next : Aligned (nextA .Ep t) ∧ TL t (nextA .Ep t) :=
  ⟨nextA_aligned ht .Ep, Or.inl (by rw [nextEp_eq, tw_val ht (by simp)]; rfl)⟩
theorem a_prev : Aligned (prevA .Ep t) ∧ TL t (prevA .Ep t) :=
  ⟨prevA_aligned ht .Ep, Or.inr (by rw [prevEp_eq, tw_val ht (by simp)]; rfl)⟩
end

theorem val_st {t : U64} (ht : TcbAddr t) : (tStA t).val = t.val + 3328 := by rw [tStA_eq, tw_val ht (by simp)]; rfl
theorem val_blk {t : U64} (ht : TcbAddr t) : (tBlockA t).val = t.val + 3336 := by
  rw [tBlockA_eq, tw_val ht (by simp)]; rfl
theorem val_badge {t : U64} (ht : TcbAddr t) : (tBadgeA t).val = t.val + 3344 := by
  unfold tBadgeA; rw [tw_val ht (by simp)]; rfl
theorem val_flags {t : U64} (ht : TcbAddr t) : (tFlagsA t).val = t.val + 3352 := by
  unfold tFlagsA; rw [tw_val ht (by simp)]; rfl
theorem val_reply {t : U64} (ht : TcbAddr t) : (tReplyA t).val = t.val + 3360 := by
  unfold tReplyA; rw [tw_val ht (by simp)]; rfl
theorem val_bound {t : U64} (ht : TcbAddr t) : (tBoundA t).val = t.val + 3368 := by
  unfold tBoundA; rw [tw_val ht (by simp)]; rfl
theorem val_fault {t : U64} (ht : TcbAddr t) : (tFaultA t).val = t.val + 3376 := by
  unfold tFaultA; rw [tw_val ht (by simp)]; rfl
theorem val_fw0 {t : U64} (ht : TcbAddr t) : (tFw0A t).val = t.val + 3384 := by
  unfold tFw0A; rw [tw_val ht (by simp)]; rfl
theorem val_fw1 {t : U64} (ht : TcbAddr t) : (tFw1A t).val = t.val + 3392 := by
  unfold tFw1A; rw [tw_val ht (by simp)]; rfl
theorem val_fw2 {t : U64} (ht : TcbAddr t) : (tFw2A t).val = t.val + 3400 := by
  unfold tFw2A; rw [tw_val ht (by simp)]; rfl
theorem val_lf {t : U64} (ht : TcbAddr t) : (tLfA t).val = t.val + 3408 := by
  unfold tLfA; rw [tw_val ht (by simp)]; rfl
theorem val_lf0 {t : U64} (ht : TcbAddr t) : (tLf0A t).val = t.val + 3416 := by
  unfold tLf0A; rw [tw_val ht (by simp)]; rfl
theorem val_lf1 {t : U64} (ht : TcbAddr t) : (tLf1A t).val = t.val + 3424 := by
  unfold tLf1A; rw [tw_val ht (by simp)]; rfl

/-- The fault relation only reads the fault words. -/
theorem FaultRel.congr {m m' : U64 → U64} {t : U64} {f : Option Fl4Spec.Fault} (h : FaultRel m t f)
    (e0 : m' (tFaultA t) = m (tFaultA t)) (e1 : m' (tFw0A t) = m (tFw0A t)) (e2 : m' (tFw1A t) = m (tFw1A t))
    (e3 : m' (tLfA t) = m (tLfA t)) (e4 : m' (tLf0A t) = m (tLf0A t)) (e5 : m' (tLf1A t) = m (tLf1A t))
    (e6 : m' (tFw2A t) = m (tFw2A t)) :
    FaultRel m' t f := by
  unfold FaultRel; rw [e0, e1, e2, e3, e4, e5, e6]; exact h

/-- The fault words agree when memory agrees on the fields `P` reaches. -/
theorem FaultRel.congr' {m m' : U64 → U64} {t : U64} (ht : TcbAddr t) {f : Option Fl4Spec.Fault}
    (h : FaultRel m t f) (P : Nat → Prop) (hA : ∀ a, Aligned a → P a.val → m' a = m a)
    (hP : ∀ k, 3376 ≤ k → k ≤ 3424 → P (t.val + k)) : FaultRel m' t f :=
  h.congr (hA _ (a_fault ht).1 (by rw [val_fault ht]; exact hP _ (by omega) (by omega)))
    (hA _ (a_fw0 ht).1 (by rw [val_fw0 ht]; exact hP _ (by omega) (by omega)))
    (hA _ (a_fw1 ht).1 (by rw [val_fw1 ht]; exact hP _ (by omega) (by omega)))
    (hA _ (a_lf ht).1 (by rw [val_lf ht]; exact hP _ (by omega) (by omega)))
    (hA _ (a_lf0 ht).1 (by rw [val_lf0 ht]; exact hP _ (by omega) (by omega)))
    (hA _ (a_lf1 ht).1 (by rw [val_lf1 ht]; exact hP _ (by omega) (by omega)))
    (hA _ (a_fw2 ht).1 (by rw [val_fw2 ht]; exact hP _ (by omega) (by omega)))

theorem val_prio {t : U64} (ht : TcbAddr t) : (prioA t).val = t.val + 3448 := by
  rw [prioA_eq', tw_val ht (by simp)]; rfl
theorem val_next {t : U64} (ht : TcbAddr t) : (nextA .Ep t).val = t.val + 3496 := by
  rw [nextEp_eq, tw_val ht (by simp)]; rfl
theorem val_prev {t : U64} (ht : TcbAddr t) : (prevA .Ep t).val = t.val + 3504 := by
  rw [prevEp_eq, tw_val ht (by simp)]; rfl

section
variable {T E R : Set U64} {B : Set (U64 × Fl4Spec.Word)}

theorem val_head (e : U64) : (epHeadA e).val = e.val := epHeadA_val
theorem val_ts (hP : EPlaced T E R B) {e : U64} (he : e ∈ E) : (epTSA e).val = e.val + 8 :=
  epTSA_val (hP.epPlaced he)

theorem a_head (hP : EPlaced T E R B) {e : U64} (he : e ∈ E) : Aligned (epHeadA e) ∧ EFoot T E R B (epHeadA e) :=
  ⟨(ep_aligned (hP.epPlaced he)).1, Or.inl ⟨e, he, Or.inl (val_head e)⟩⟩
theorem a_ts (hP : EPlaced T E R B) {e : U64} (he : e ∈ E) : Aligned (epTSA e) ∧ EFoot T E R B (epTSA e) :=
  ⟨(ep_aligned (hP.epPlaced he)).2, Or.inl ⟨e, he, Or.inr (val_ts hP he)⟩⟩
theorem a_rtcb (hP : EPlaced T E R B) {r : U64} (hr : r ∈ R) : Aligned (rTcbA r) ∧ EFoot T E R B (rTcbA r) := by
  refine ⟨?_, Or.inr (Or.inl ⟨r, hr, rTcbA_val r⟩)⟩
  have := (hP.rep r hr).1
  unfold Aligned; rw [rTcbA_val]; omega

end

/-! ## Frames -/

section Frame
open Fl4Spec
variable {Z : Type} {T E R : Set U64} {B : Set (U64 × Word)}

theorem TcbRelE.frame {m m' : U64 → U64} {t : U64} {x : Tcb} (ht : TcbAddr t) (h : TcbRelE R m t x)
    (he : Agree m m' (TF t)) : TcbRelE R m' t x := by
  have e_st := he _ (a_st ht).1 (a_st ht).2
  have e_blk := he _ (a_blk ht).1 (a_blk ht).2
  have e_badge := he _ (a_badge ht).1 (a_badge ht).2
  have e_flags := he _ (a_flags ht).1 (a_flags ht).2
  have e_reply := he _ (a_reply ht).1 (a_reply ht).2
  have e_bound := he _ (a_bound ht).1 (a_bound ht).2
  have e_fault := he _ (a_fault ht).1 (a_fault ht).2
  have e_prio := he _ (a_prio ht).1 (a_prio ht).2
  refine ⟨by rw [e_st]; exact h.st, fun e hb => by rw [e_blk]; exact h.blk e hb,
    fun e d hs => by rw [e_badge, e_flags]; exact h.send e d hs,
    fun e r d hs => by rw [e_reply]; exact h.recv e r d hs, fun r hs => by rw [e_reply]; exact h.reply r hs,
    fun r => by rw [he _ (a_reg ht r).1 (a_reg ht r).2]; exact h.regs r, by rw [e_prio]; exact h.prio,
    by rw [e_fault]; exact h.fault0, by rw [e_fault]; exact h.faultT, by rw [e_bound]; exact h.bound,
    h.faultR.congr e_fault (he _ (a_fw0 ht).1 (a_fw0 ht).2) (he _ (a_fw1 ht).1 (a_fw1 ht).2)
      (he _ (a_lf ht).1 (a_lf ht).2) (he _ (a_lf0 ht).1 (a_lf0 ht).2) (he _ (a_lf1 ht).1 (a_lf1 ht).2)
      (he _ (a_fw2 ht).1 (a_fw2 ht).2)⟩

/-- What an endpoint needs of a member of its queue: state, block object
and links. -/
def MemberEq (m m' : U64 → U64) (y : U64) : Prop :=
  m' (tStA y) = m (tStA y) ∧ m' (tBlockA y) = m (tBlockA y) ∧ TLinksEq m m' y

theorem EpObjRel.frame {m m' : U64 → U64} {e : U64} {o : Endpoint} (h : EpObjRel m T e o)
    (h1 : m' (epHeadA e) = m (epHeadA e)) (h2 : m' (epTSA e) = m (epTSA e))
    (hy : ∀ y ∈ T, y.bv ∈ o.epQueue → MemberEq m m' y) : EpObjRel m' T e o := by
  have hq : qOf m' e = qOf m e := by simp only [qOf, h1, h2]
  have hs : stOf m' e = stOf m e := by simp only [stOf, h2]
  cases o with
  | idleEP =>
    obtain ⟨a, b⟩ := h
    exact ⟨hs ▸ a, hq ▸ queueRel_congr_links b (by simp)⟩
  | sendEP q =>
    obtain ⟨a, xs, hne, rfl, b, c⟩ := h
    have hy' : ∀ y ∈ xs, MemberEq m m' y := fun y hyx =>
      hy y (b.mem y hyx) (by simp only [Endpoint.epQueue]; exact List.mem_map_of_mem hyx)
    refine ⟨hs ▸ a, xs, hne, rfl, hq ▸ queueRel_congr_links b (fun y hyx => (hy' y hyx).2.2), fun y hyx => ?_⟩
    obtain ⟨c1, c2⟩ := c y hyx
    exact ⟨(hy' y hyx).1 ▸ c1, (hy' y hyx).2.1 ▸ c2⟩
  | recvEP q =>
    obtain ⟨a, xs, hne, rfl, b, c⟩ := h
    have hy' : ∀ y ∈ xs, MemberEq m m' y := fun y hyx =>
      hy y (b.mem y hyx) (by simp only [Endpoint.epQueue]; exact List.mem_map_of_mem hyx)
    refine ⟨hs ▸ a, xs, hne, rfl, hq ▸ queueRel_congr_links b (fun y hyx => (hy' y hyx).2.2), fun y hyx => ?_⟩
    obtain ⟨c1, c2⟩ := c y hyx
    exact ⟨(hy' y hyx).1 ▸ c1, (hy' y hyx).2.1 ▸ c2⟩

/-- The queue of a related endpoint, whatever its state. -/
theorem EpObjRel.queue {m : U64 → U64} {e : U64} {o : Endpoint} (h : EpObjRel m T e o) :
    ∃ xs, QueueRel m T .Ep (qOf m e) xs ∧ o.epQueue = xs.map UScalar.bv ∧
      ∀ y ∈ xs, m (tBlockA y) = e ∧ ((m (tStA y)).val = 3 ∨ (m (tStA y)).val = 4) := by
  cases o with
  | idleEP => exact ⟨[], h.2, rfl, by simp⟩
  | sendEP q =>
    obtain ⟨-, xs, -, rfl, h2, h3⟩ := h
    exact ⟨xs, h2, rfl, fun y hy => ⟨(h3 y hy).2, Or.inr (h3 y hy).1⟩⟩
  | recvEP q =>
    obtain ⟨-, xs, -, rfl, h2, h3⟩ := h
    exact ⟨xs, h2, rfl, fun y hy => ⟨(h3 y hy).2, Or.inl (h3 y hy).1⟩⟩

/-- Members of an endpoint queue are TCBs blocked on the endpoint. -/
theorem EpObjRel.blocked {m : U64 → U64} {e : U64} {o : Endpoint} (h : EpObjRel m T e o)
    {y : U64} (hy : y.bv ∈ o.epQueue) : y ∈ T ∧ m (tBlockA y) = e := by
  obtain ⟨xs, h1, h2, h3⟩ := h.queue
  rw [h2, List.mem_map] at hy
  obtain ⟨z, hz, ez⟩ := hy
  have : z = y := eq_of_bv ez
  subst this
  exact ⟨h1.mem z hz, (h3 z hz).1⟩

/-- Memory that agrees on the footprint. -/
def FootEq (T E R : Set U64) (B : Set (U64 × Word)) (m m' : U64 → U64) : Prop := Agree m m' (EFoot T E R B)

theorem loadWordAt_congr {um um' : Word → Word8} (h : um' = um) (p : Word) : loadWordAt um' p = loadWordAt um p := by
  rw [h]

/-- The relation only reads the footprint and `KView`. -/
theorem EpStateRel.frame {m m' : U64 → U64} {σ σ' : State Z} (hR : EpStateRel T E R B m σ)
    (hP : EPlaced T E R B) (hm : FootEq T E R B m m') (hk : KView σ σ') : EpStateRel T E R B m' σ' := by
  refine ⟨fun e he => ?_, fun r hr => ?_, fun t ht => ?_, fun wp hw => ?_⟩
  · obtain ⟨x, hkx, hx⟩ := hR.ep e he
    refine ⟨x, hk.1 _ _ hkx, hx.frame (hm _ (a_head hP he).1 (a_head hP he).2) (hm _ (a_ts hP he).1 (a_ts hP he).2)
      fun y hy _ => ?_⟩
    have hya := hP.tcb y hy
    exact ⟨hm _ (a_st hya).1 (Or.inr (Or.inr (Or.inl ⟨y, hy, Or.inl (a_st hya).2⟩))),
      hm _ (a_blk hya).1 (Or.inr (Or.inr (Or.inl ⟨y, hy, Or.inl (a_blk hya).2⟩))),
      hm _ (a_prev hya).1 (Or.inr (Or.inr (Or.inl ⟨y, hy, Or.inr (a_prev hya).2⟩))),
      hm _ (a_next hya).1 (Or.inr (Or.inr (Or.inl ⟨y, hy, Or.inr (a_next hya).2⟩)))⟩
  · obtain ⟨x, hkx, hx⟩ := hR.reply r hr
    obtain ⟨y, hky, ey⟩ := hk.2.1 _ _ hkx
    exact ⟨y, hky, by rw [ey, hx, hm _ (a_rtcb hP hr).1 (a_rtcb hP hr).2]⟩
  · obtain ⟨x, hkx, hx⟩ := hR.tcb t ht
    obtain ⟨y, hky, e1, e2, e3, e4, e5⟩ := hk.2.2.1 _ _ hkx
    have hta := hP.tcb t ht
    have hx' := hx.frame hta (fun a ha hf => hm a ha (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inl hf⟩))))
    refine ⟨y, hky, ⟨e1 ▸ hx'.st, fun e hb => hx'.blk e (e1 ▸ hb), fun e d hs => hx'.send e d (e1 ▸ hs),
      fun e r d hs => hx'.recv e r d (e1 ▸ hs), fun r hs => hx'.reply r (e1 ▸ hs), fun r => e2 ▸ hx'.regs r,
      e3 ▸ hx'.prio, e4 ▸ hx'.fault0, e4 ▸ hx'.faultT, e5 ▸ hx'.bound, e4 ▸ hx'.faultR⟩⟩
  · have hal : Aligned wp.1 := (hP.balign wp hw).1
    rw [hm _ hal (Or.inr (Or.inr (Or.inr ⟨wp, hw, rfl⟩))), hR.buf wp hw, hk.2.2.2]

theorem KView.refl (σ : State Z) : KView σ σ :=
  ⟨fun _ _ h => h, fun _ x h => ⟨x, h, rfl⟩, fun _ x h => ⟨x, h, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

theorem KView.trans {σ₁ σ₂ σ₃ : State Z} (h₁ : KView σ₁ σ₂) (h₂ : KView σ₂ σ₃) : KView σ₁ σ₃ := by
  refine ⟨fun p x h => h₂.1 p x (h₁.1 p x h), fun p x h => ?_, fun p x h => ?_, h₂.2.2.2.trans h₁.2.2.2⟩
  · obtain ⟨y, hy, e⟩ := h₁.2.1 p x h
    obtain ⟨z, hz, f⟩ := h₂.2.1 p y hy
    exact ⟨z, hz, f.trans e⟩
  · obtain ⟨y, hy, e1, e2, e3, e4, e5⟩ := h₁.2.2.1 p x h
    obtain ⟨z, hz, f1, f2, f3, f4, f5⟩ := h₂.2.2.1 p y hy
    exact ⟨z, hz, f1.trans e1, f2.trans e2, f3.trans e3, f4.trans e4, f5.trans e5⟩

theorem EpStep.refl (σ : State Z) : EpStep σ σ := ⟨rfl, rfl, fun _ => Or.inl rfl⟩

end Frame

end

end Fl4Proofs.P3.Endp
