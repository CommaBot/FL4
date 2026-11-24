/-
P2 (local-path ownership): the kernel facts the global ownership map
(`P2/OwnMap.lean`, DESIGN §7 "What a local path may write", "Timer
ownership") needs that **already follow from the P1 invariants**. Numbering
as in the P2 ownership plan:

* (4a) A thread blocked on reply (`STATE` 5) has a reply object `r ≠ 0`
  naming it back (`ReplyInv0.blocked_reply`, from `ReplyInv0.reply`/`back`).
* (4b) A thread blocked on an endpoint or notification (`STATE` 3, 4, 6) is
  in the queue of the object its `BLOCK_OBJ` names, an endpoint for 3/4 and a
  notification for 6 (`SchedQueuesInvX.blocked_obj`, from `EpsWit`).
* (5) A notification has at most one bound TCB, and that TCB's
  `BOUND_NTFN` points back (`BndS.bound_unique`, `XInv.ntfn_bound`).
* (7) An armed thread lies in exactly one core's timer tree, the core
  `TIMER_HEIGHT >> 8` (`TimerRB.owner`, `TimerRB.owner_unique`).

`EntryInv.p2_owner_facts` collects them at a kernel entry. No new premises.
-/
import Fl4Proofs.P1.QueueFire
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-! ## (7) Timer ownership -/

/-- `x >>> 8` is the quotient by 256 (OwnMap's `treeCore` uses `/ 256`). -/
theorem shr8_eq_div (x : Nat) : x >>> 8 = x / 256 := by
  rw [Nat.shiftRight_eq_div_pow]

/-- A node of core `c`'s tree names `c` in its `TIMER_HEIGHT` word. -/
theorem CoreTree.owner_eq {s : S} {c : U64} {t : TRB.RBT} (h : CoreTree st T s c t) {y : U64}
    (hy : y ∈ t.keys) : c.val = (L.mem s (thA y)).val / 256 := by
  rw [← shr8_eq_div]; exact (h.core y hy).symm

/-- **(7)** An armed thread is a node of the tree of the core `TIMER_HEIGHT >> 8`. -/
theorem TimerRB.owner {s : S} (h : TimerRB st T Cs s) {y : U64} (hy : y ∈ T) (hd : L.mem s (tdA y) ≠ 0#u64) :
    ∃ c ∈ Cs, c.val = (L.mem s (thA y)).val / 256 ∧ ∃ t, CoreTree st T s c t ∧ y ∈ t.keys := by
  obtain ⟨c, hc, t, ct, hyt⟩ := h.armed y hy hd
  exact ⟨c, hc, ct.owner_eq hyt, t, ct, hyt⟩

/-- **(7)** A thread is a node of at most one core's tree. -/
theorem TimerRB.owner_unique {s : S} {c c' : U64} {t t' : TRB.RBT} (h : CoreTree st T s c t)
    (h' : CoreTree st T s c' t') {y : U64} (hy : y ∈ t.keys) (hy' : y ∈ t'.keys) : c = c' :=
  UScalar.eq_of_val_eq ((h.owner_eq hy).trans (h'.owner_eq hy').symm)

/-- **(7)** The tree holding an armed thread is the one of the core its
`TIMER_HEIGHT` names, whichever witness is taken. -/
theorem TimerRB.owner_of_mem {s : S} {c : U64} {t : TRB.RBT} (h : CoreTree st T s c t) {y : U64}
    (hy : y ∈ t.keys) : L.mem s (tdA y) ≠ 0#u64 ∧ c.val = (L.mem s (thA y)).val / 256 :=
  ⟨h.armed y hy, h.owner_eq hy⟩

/-! ## (5) Notification binding -/

/-- **(5)** Two TCBs bound to the same notification are equal. -/
theorem BndS.bound_unique {s : S} (h : BndS st T Scs Nt s) {t t' n : U64} (ht : t ∈ T) (ht' : t' ∈ T)
    (hn : n ≠ 0#u64) (e : L.mem s (boundA t) = n) (e' : L.mem s (boundA t') = n) : t = t' := by
  have a := h.tb t ht (by rw [e]; exact hn)
  have b := h.tb t' ht' (by rw [e']; exact hn)
  rw [e] at a; rw [e'] at b
  exact a.symm.trans b

/-- **(5)** A notification's bound TCB (if any) is a TCB whose `BOUND_NTFN`
names the notification, and is the only TCB bound to it. -/
theorem XInv.ntfn_bound {s : S} (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) {n : U64} (hn : n ∈ Nt)
    (hn0 : n ≠ 0#u64) (hb : L.mem s (ntfnBtA n) ≠ 0#u64) :
    L.mem s (ntfnBtA n) ∈ T ∧ L.mem s (boundA (L.mem s (ntfnBtA n))) = n ∧
      ∀ t ∈ T, L.mem s (boundA t) = n → t = L.mem s (ntfnBtA n) := by
  have hT : L.mem s (ntfnBtA n) ∈ T := (hX.2.2.ntb n hn).ne0 hb
  have hback := hX.2.2.bs.nt n hn hb
  exact ⟨hT, hback, fun t ht e => hX.2.2.bs.bound_unique ht hT hn0 e hback⟩

/-- **(5)** A TCB's bound notification names it back. -/
theorem XInv.tcb_bound {s : S} (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) {t : U64} (ht : t ∈ T)
    (hb : L.mem s (boundA t) ≠ 0#u64) :
    L.mem s (boundA t) ∈ Nt ∧ L.mem s (ntfnBtA (L.mem s (boundA t))) = t :=
  ⟨hX.2.2.bnd t ht hb, hX.2.2.bs.tb t ht hb⟩

/-! ## (4) Blocked threads -/

/-- **(4a)** A thread blocked on reply has a reply object, not null, naming it. -/
theorem ReplyInv0.blocked_reply {s : S} (h : ReplyInv0 st T Rp Scs s) (hT : TcbPlaced T) {t : U64} (ht : t ∈ T)
    (hs : L.mem s (stA t) = sched.TS_BLOCKED_ON_REPLY) :
    L.mem s (replyA t) ≠ 0#u64 ∧ L.mem s (replyA t) ∈ Rp ∧ L.mem s (rTcbA (L.mem s (replyA t))) = t := by
  obtain ⟨hr, hb⟩ := h.reply t ht hs
  have ht0 : t ≠ 0#u64 := fun e => (hT t ht).ne0 (by rw [e]; rfl)
  exact ⟨(h.back _ hr (by rw [hb]; exact ht0)).1, hr, hb⟩

/-- **(4b)** A thread blocked on an endpoint or a notification (outside the
exception set) is in the queue of its `BLOCK_OBJ`: an endpoint when blocked on
send or receive, a notification when blocked on a notification. The members
of that queue all name it as their `BLOCK_OBJ`. -/
theorem SchedQueuesInvX.blocked_obj {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) {t : U64} (ht : t ∈ T) (hx : t ∉ X)
    (hb : Blocked (L.mem s (stA t))) :
    ∃ (E : Set U64) (EQ : U64 → List U64), L.mem s (blockA t) ∈ E ∧ t ∈ EQ (L.mem s (blockA t)) ∧
      QueueRel (L.mem s) T .Ep (L.epQ s (L.mem s (blockA t))) (EQ (L.mem s (blockA t))) ∧
      (∀ y ∈ EQ (L.mem s (blockA t)), L.mem s (blockA y) = L.mem s (blockA t)) ∧
      ((L.mem s (stA t) = sched.TS_BLOCKED_ON_SEND ∨ L.mem s (stA t) = sched.TS_BLOCKED_ON_RECV) →
        H (L.mem s (blockA t)) = some .ep) ∧
      (L.mem s (stA t) = sched.TS_BLOCKED_ON_NTFN → H (L.mem s (blockA t)) = some .ntfn) := by
  obtain ⟨E, EQ, hpl, -, -, hin, hmem, k1, k2, -⟩ := h.eps
  obtain ⟨he, hq⟩ := hmem t ht hx hb
  exact ⟨E, EQ, he, hq, (hpl _ he).2.2, fun y hy => (hin _ he y hy).2.1, k1 t ht hx, k2 t ht hx⟩

/-! ## At a kernel entry -/

/-- The P1-implied ownership facts (4), (5), (7) at a kernel entry. -/
theorem EntryInv.p2_owner_facts {s : S} (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    (∀ t ∈ T, L.mem s (stA t) = sched.TS_BLOCKED_ON_REPLY →
      L.mem s (replyA t) ≠ 0#u64 ∧ L.mem s (replyA t) ∈ Rp ∧ L.mem s (rTcbA (L.mem s (replyA t))) = t) ∧
    (∀ t ∈ T, Blocked (L.mem s (stA t)) →
      ∃ (E : Set U64) (EQ : U64 → List U64), L.mem s (blockA t) ∈ E ∧ t ∈ EQ (L.mem s (blockA t)) ∧
        QueueRel (L.mem s) T .Ep (L.epQ s (L.mem s (blockA t))) (EQ (L.mem s (blockA t))) ∧
        (∀ y ∈ EQ (L.mem s (blockA t)), L.mem s (blockA y) = L.mem s (blockA t)) ∧
        ((L.mem s (stA t) = sched.TS_BLOCKED_ON_SEND ∨ L.mem s (stA t) = sched.TS_BLOCKED_ON_RECV) →
          H (L.mem s (blockA t)) = some .ep) ∧
        (L.mem s (stA t) = sched.TS_BLOCKED_ON_NTFN → H (L.mem s (blockA t)) = some .ntfn)) ∧
    (∀ t ∈ T, ∀ t' ∈ T, ∀ n : U64, n ≠ 0#u64 → L.mem s (boundA t) = n → L.mem s (boundA t') = n → t = t') ∧
    (∀ n ∈ Nt, L.mem s (ntfnBtA n) ≠ 0#u64 → L.mem s (boundA (L.mem s (ntfnBtA n))) = n) ∧
    (∀ y ∈ T, L.mem s (tdA y) ≠ 0#u64 →
      ∃ c ∈ Cs, c.val = (L.mem s (thA y)).val / 256 ∧ ∃ t, CoreTree st T s c t ∧ y ∈ t.keys) := by
  obtain ⟨⟨Q, R, hq⟩, -, hX, -⟩ := h
  refine ⟨fun t ht hs => hX.2.1.toReplyInv0.blocked_reply hq.tcbs ht hs,
    fun t ht hb => hq.blocked_obj ht (Set.notMem_empty t) hb,
    fun t ht t' ht' n hn e e' => hX.2.2.bs.bound_unique ht ht' hn e e',
    fun n hn hb => hX.2.2.bs.nt n hn hb,
    fun y hy hd => hX.2.2.rb.owner hy hd⟩

end

end Fl4Proofs.P1
