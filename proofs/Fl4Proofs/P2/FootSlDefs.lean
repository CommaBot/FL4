/-
# P2 (line p2sl): the write footprint of `handle_syscall_local`, definitions

DESIGN.md §7 ("What a local path may write, its footprint"), made concrete
for the syscall entry beside the gate (`syscall.handle_syscall_local`: an
l4h guest's trapped syscall answered by `fastpath.fault`, the handler's
ReplyRecv answered by `fastpath.reply_recv_found`), at the entry state `s`
(fl4-sync's `local_syscall` calls it once it holds its locks), over the TCB
set `T` and the SC sizes `Z` of the P1 invariants:

* `SlNode`: the current core's node words;
* `SlTcb`: the TCB words of the threads on this core (`SlOn`: a TCB of `T`
  whose affinity is this core, or the current thread), except the timer
  fields (`TIMER_DEADLINE ..= TIMER_HEIGHT`, which the path never writes)
  and except the queue links (`EP_NEXT`, `EP_PREV`) of one blocked on an
  endpoint or notification (`SlBlk`);
* `SlBuf`: the IPC-buffer words of the threads on this core (the 128
  words at the buffer `msg.lookup_ipc_buffer` finds);
* `SlSc`: the words of the SCs on this core (the current SC and the SCs of
  the threads on this core), of `2 ^ Z c` bytes;
* `SlLk ep r`: the objects the path locked, the endpoint `ep` (16 bytes)
  and the reply object `r` (32 bytes), as fl4-sync's `observe` sees them
  (`SlLocks`: the fault handler's endpoint and its head's reply object for a
  trapped thread, `found` for a ReplyRecv);
* `SlQ ep`: the queue links of the threads queued on the locked endpoint
  (`SlReach`: from its head along `EP_NEXT`, within `T`).

`FootSl` is their union. Words are the store's aligned 8-byte words (`L.mem`;
`WritesIn` speaks of aligned words only).

The prefix both outcomes share (`sl_pre_foot`): the current thread's
`FAULT_IP`, then `update_timestamp`'s two node words. A declined run wrote
at most these (`sl_decline_foot`, from P1's `syscall_local_decline`).

No premises.
-/
import Fl4Proofs.P2.FootSlTail
import Fl4Proofs.P1.FastLocalDecline
import Fl4Proofs.P1.FastSysLocal
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

section
variable {S : Type _} {A : Type _} {st : machine.Store S} [L : LawfulStore st]

variable (st) in
/-- A word of the current core's node. -/
def SlNode (s : S) (b : U64) : Prop :=
  ∃ o : U64, o.val < 4288 ∧ o.val % 8 = 0 ∧ b = L.nodeAt s (L.cpu s) o

variable (st) in
/-- A thread on this core: a TCB whose affinity is this core, or the current thread. -/
def SlOn (T : Set U64) (s : S) (y : U64) : Prop :=
  y ∈ T ∧ (L.mem s (affA y) = L.cpu s ∨ y = L.curW s)

variable (st) in
/-- Blocked on an endpoint or a notification. -/
def SlBlk (s : S) (y : U64) : Prop :=
  L.mem s (stA y) = sched.TS_BLOCKED_ON_RECV ∨ L.mem s (stA y) = sched.TS_BLOCKED_ON_SEND ∨
    L.mem s (stA y) = sched.TS_BLOCKED_ON_NTFN

variable (st) in
/-- A TCB word of a thread on this core: not a timer field, and not a queue
link while the thread is blocked on an endpoint or notification. -/
def SlTcb (T : Set U64) (s : S) (b : U64) : Prop :=
  ∃ y, SlOn st T s y ∧ ∃ K : U64, K.val < 4096 ∧ b = core.num.U64.wrapping_add y K ∧
    ¬ (3528 ≤ K.val ∧ K.val < 3576) ∧ (SlBlk st s y → K.val ≠ 3496 ∧ K.val ≠ 3504)

variable (st) in
/-- A word of the IPC buffer of a thread on this core. -/
def SlBuf (T : Set U64) (s : S) (b : U64) : Prop :=
  ∃ y, SlOn st T s y ∧ ∃ (w : Bool) (buf : U64), msg.lookup_ipc_buffer st s w y = ok buf ∧ buf ≠ 0#u64 ∧
    ∃ i : U64, i.val < 128 ∧ b = core.num.U64.wrapping_add buf (core.num.U64.wrapping_mul i 8#u64)

variable (st) in
/-- A word of an SC on this core: the current SC or a thread on this core's SC. -/
def SlSc (T : Set U64) (Z : U64 → Nat) (s : S) (b : U64) : Prop :=
  ∃ c, (c = L.cscW s ∨ ∃ y, SlOn st T s y ∧ L.mem s (scA y) = c ∧ c ≠ 0#u64) ∧ InSC c (Z c) b

/-- A word of a locked object: the endpoint (16 bytes) or the reply object (32 bytes). -/
def SlLk (ep r : U64) (b : U64) : Prop :=
  (ep.val ≤ b.val ∧ b.val < ep.val + 16) ∨ (r.val ≤ b.val ∧ b.val < r.val + 32)

/-- The threads queued on the endpoint `ep`: from its head along `EP_NEXT`, within `T`. -/
inductive SlReach (m : U64 → U64) (T : Set U64) (ep : U64) : U64 → Prop
  | head : m (epHeadA ep) ∈ T → SlReach m T ep (m (epHeadA ep))
  | next {y : U64} : SlReach m T ep y → m (nextA .Ep y) ∈ T → SlReach m T ep (m (nextA .Ep y))

variable (st) in
/-- A queue link of a thread queued on the locked endpoint `ep`. -/
def SlQ (T : Set U64) (s : S) (ep : U64) (b : U64) : Prop :=
  ∃ y, SlReach (L.mem s) T ep y ∧ (b = nextA .Ep y ∨ b = prevA .Ep y)

variable (st) in
/-- **The footprint of `handle_syscall_local` at its entry state `s`**, with
the locked endpoint `ep` and reply object `r` (module docstring). -/
def FootSl (T : Set U64) (Z : U64 → Nat) (s : S) (ep r : U64) (b : U64) : Prop :=
  SlNode st s b ∨ SlTcb st T s b ∨ SlBuf st T s b ∨ SlSc st T Z s b ∨ SlLk ep r b ∨ SlQ st T s ep b

variable (st) in
/-- **The objects fl4-sync's `local_syscall` locks** at the entry state `s`:
for a trapped thread, its fault handler's endpoint and the reply object of
the endpoint's head; for a ReplyRecv, `found` (the reply object, the
endpoint). -/
def SlLocks (s : S) (n : I64) (found : U64 × U64) (ep r : U64) : Prop :=
  (∃ f, obj.Tcb.flags st (L.curW s) s = ok f ∧ (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true ∧
    ∃ sl badge x y g gr, obj.Tcb.slot (L.curW s) layout.tcb.SLOT_FAULT_HANDLER = ok sl ∧
      obj.Slot.cap st sl s = ok (capability.Cap.Endpoint ep badge x y g gr) ∧
      r = L.mem s (replyA (L.mem s (epHeadA ep)))) ∨
  (∃ f, obj.Tcb.flags st (L.curW s) s = ok f ∧ ¬ (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true ∧
    n = fl4_abi.syscall.SysReplyRecv ∧ found = (r, ep))

/-! ## Membership -/

variable {T : Set U64} {Z : U64 → Nat} {s : S} {ep r : U64}

theorem FootSl.node {b : U64} (h : SlNode st s b) : FootSl st T Z s ep r b := Or.inl h
theorem FootSl.tcb {b : U64} (h : SlTcb st T s b) : FootSl st T Z s ep r b := Or.inr (Or.inl h)
theorem FootSl.buf {b : U64} (h : SlBuf st T s b) : FootSl st T Z s ep r b := Or.inr (Or.inr (Or.inl h))
theorem FootSl.sc {b : U64} (h : SlSc st T Z s b) : FootSl st T Z s ep r b := Or.inr (Or.inr (Or.inr (Or.inl h)))
theorem FootSl.lk {b : U64} (h : SlLk ep r b) : FootSl st T Z s ep r b :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
theorem FootSl.q {b : U64} (h : SlQ st T s ep b) : FootSl st T Z s ep r b := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

theorem slNode_at {o : U64} (ho : o.val < 4288) (h8 : o.val % 8 = 0) : SlNode st s (L.nodeAt s (L.cpu s) o) :=
  ⟨o, ho, h8, rfl⟩

/-- A field of a thread on this core, other than a timer field and a queue link. -/
theorem slTcb_at {y K : U64} (hy : SlOn st T s y) (hK : K.val < 4096) (hT : ¬ (3528 ≤ K.val ∧ K.val < 3576))
    (hE : K.val ≠ 3496 ∧ K.val ≠ 3504) : SlTcb st T s (core.num.U64.wrapping_add y K) :=
  ⟨y, hy, K, hK, rfl, hT, fun _ => hE⟩

/-- A field of a thread on this core that is not blocked on an endpoint or notification. -/
theorem slTcb_at' {y K : U64} (hy : SlOn st T s y) (hK : K.val < 4096) (hT : ¬ (3528 ≤ K.val ∧ K.val < 3576))
    (hb : ¬ SlBlk st s y) : SlTcb st T s (core.num.U64.wrapping_add y K) :=
  ⟨y, hy, K, hK, rfl, hT, fun h => absurd h hb⟩

theorem slOn_cur (hc : L.curW s ∈ T) : SlOn st T s (L.curW s) := ⟨hc, Or.inr rfl⟩

theorem slOn_aff {y : U64} (hy : y ∈ T) (ha : L.mem s (affA y) = L.cpu s) : SlOn st T s y := ⟨hy, Or.inl ha⟩

/-- The ring words of an SC on this core. -/
theorem slSc_ring {c b : U64} (hc : c = L.cscW s ∨ ∃ y, SlOn st T s y ∧ L.mem s (scA y) = c ∧ c ≠ 0#u64)
    (hb : InRing c (Z c) b) : SlSc st T Z s b := ⟨c, hc, hb.inSC⟩

/-- The endpoint's two words, by value. -/
theorem sl_ep_vals {ep : U64} (hE : EpPlaced T ep) :
    (epHeadA ep).val = ep.val ∧ (epTSA ep).val = ep.val + 8 :=
  ⟨epHeadA_val, epTSA_val hE⟩

/-- The locked endpoint's words. -/
theorem slLk_ep {ep r : U64} (hE : EpPlaced T ep) : SlLk ep r (epHeadA ep) ∧ SlLk ep r (epTSA ep) := by
  obtain ⟨h1, h2⟩ := sl_ep_vals hE
  exact ⟨Or.inl ⟨by omega, by omega⟩, Or.inl ⟨by omega, by omega⟩⟩

/-- The locked reply object's `TCB` word. -/
theorem slLk_rtcb {ep r : U64} : SlLk ep r (rTcbA r) := Or.inr ⟨by rw [rTcbA_val0], by rw [rTcbA_val0]; omega⟩

/-- An endpoint word is no TCB word. -/
theorem sl_ep_ne_field {ep y K : U64} (hE : EpPlaced T ep) (hy : y ∈ T) (hya : TcbAddr y) (hK : K.val < 4096) :
    epHeadA ep ≠ core.num.U64.wrapping_add y K ∧ epTSA ep ≠ core.num.U64.wrapping_add y K := by
  obtain ⟨h1, h2⟩ := sl_ep_vals hE
  have hd := hE.disj y hy
  have hv := field_val hya hK
  constructor <;> intro e <;> have e' := congrArg UScalar.val e <;> omega

/-! ## The prefix and a declined run -/

variable {A : Type _} {ar : machine.Arch A}

/-- The prefix's words: the current thread's `FAULT_IP`, the node. -/
theorem sl_pre_foot (hA : P0.ArchTotal ar) (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s))
    (hcT : L.curW s ∈ T) {a a' : A} {s' : S}
    (hP : LocalPre (st := st) ar s a (s', a')) :
    WritesIn st s s' (fun b => b = regA (L.curW s) layout.reg.FAULT_IP ∨ SlNode st s b) := by
  obtain ⟨t, nx, s1, et, -, es1, eu⟩ := hP
  have et' : t = L.curW s := by rw [cur_thread_ok] at et; exact (ok_inj_ff et).symm
  subst et'
  have ht' := hT _ hcT
  have e1 := set_fip_wr ht' es1
  obtain ⟨KF, hKF, eKF⟩ := regA_eq ht' (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])
  have hKF' : KF.val = 392 := by rw [hKF]; simp [layout.reg.FAULT_IP]
  have aF : Aligned (regA (L.curW s) layout.reg.FAULT_IP) := by rw [eKF]; exact field_aligned ht' (by omega) (by omega)
  have hN1 : NodePlaced st T s1 (L.cpu s1) := by rw [e1, LawfulStore.cpu_wr]; exact hN.wr
  have w2 := sched.update_timestamp.fr hA s1 a hN1
  rw [eu, WP.spec_ok] at w2
  try simp only [WP.uncurry'_pair] at w2
  subst e1
  refine ((writesIn_wr aF).trans w2).mono fun b hb => ?_
  rcases hb with rfl | ⟨o, -, ho, h8, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨o, ho, h8, by rw [L.cpu_wr, nodeAt_of_ksb (L.ksb_wr _ _ _)]⟩

/-- The prefix's words are footprint words. -/
theorem sl_pre_sub (hT : TcbPlaced T) (hcT : L.curW s ∈ T) {b : U64}
    (h : b = regA (L.curW s) layout.reg.FAULT_IP ∨ SlNode st s b) : FootSl st T Z s ep r b := by
  rcases h with rfl | h
  · obtain ⟨KF, hKF, eKF⟩ := regA_eq (hT _ hcT) (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])
    have hKF' : KF.val = 392 := by rw [hKF]; simp [layout.reg.FAULT_IP]
    rw [eKF]; exact FootSl.tcb (slTcb_at (slOn_cur hcT) (by omega) (by omega) (by omega))
  · exact FootSl.node h

/-- **A declined `handle_syscall_local` wrote at most the prefix's words**:
the current thread's `FAULT_IP` and the node (both footprint words). -/
theorem sl_decline_foot (hA : P0.ArchTotal ar) (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s))
    (hcT : L.curW s ∈ T) {a a' : A} {s' : S} {n : I64} {found : U64 × U64}
    (h : syscall.handle_syscall_local st ar s a n found = ok (false, s', a')) :
    WritesIn st s s' (fun b => b = regA (L.curW s) layout.reg.FAULT_IP ∨ SlNode st s b) := by
  rcases syscall_local_decline ar h with ⟨rfl, -⟩ | ⟨hP, -⟩
  · exact WritesIn.refl _ _
  · exact sl_pre_foot hA hT hN hcT hP

end

end Fl4Proofs.P2
