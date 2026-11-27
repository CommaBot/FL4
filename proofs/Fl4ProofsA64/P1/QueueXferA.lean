/-
P1 (AArch64): the message-transfer hypothesis with the frame AArch64's transfer actually has.

x86's `XferFr` (QueueIpc) promises every TCB field at offset ≥ 3328 of every thread unchanged by
`do_ipc_transfer`. On AArch64 that is false on the trap-syscalls fault path: `faults.set_mrs_fault`'s
`UnknownSyscall` arm ends in `faults.trap_extra_mrs`, which (sender flag `TRAP_SYSCALLS` set, buffer non-null,
13 words so far) writes **the sender's `FAULT_W1` field** (`layout.tcb.FAULT_W1` = F + 64 = 3392) before
copying X8..X31 into the receiver's buffer. So `XferOK` (stated with `XferFr`) is not provable on A64.

This module states the A64 frame and hypothesis and re-proves its consumers:
- `XferFrA st T Rp snd s s'`: `XferFr` minus exactly the sender's `FAULT_W1` word (`y = snd → K ≠ 3392`);
  `XferFr.toA` (the x86 frame implies it) and `XferOK.toA`.
- `XferOKA`: `XferOK` with `XferFrA` for the transfer's sender; `xferOK_ofA` (QueueXfer) proves it.
- `_A` twins (text of the originals, `XferOK` → `XferOKA`, the frame composition `F` taking one more
  `K ≠ 3392` hypothesis, discharged by `simp` at every use: the words read through the frame are `STATE`,
  `REPLY`, the queue links, `SC` and `RUN_VCPU`, none of them `FAULT_W1`):
  `endpoint.receive_from_sender.ipcA`, `endpoint.send_ipc.ipcA`, `endpoint.receive_ipc.ipcA` (QueueIpc),
  `endpoint.receive_ipc.ipc_rvA` (RunVcpuRecv), `syscall.handle_recv.bxiA`, `faults.handle_timeout.bxiA`,
  `faults.handle_fault.bxiA` (QueueRecv), `ep_send.blkA` (QueueInvoke).
No consumer needs the sender's `FAULT_W1` word kept. Named premises: those of the originals, unchanged
(**[J] `hRV`** `RunVcpuInv`, caller-level `hvm` / `hrvc`); nothing new.
-/
import Fl4ProofsA64.P1.QueueRecv
import Fl4ProofsA64.P1.QueueInvoke
import Fl4ProofsA64.P1.RunVcpuRecv
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}

/-- a64: the frame of a message transfer from `snd`: `XferFr` (the scheduler words, the TCB fields from
`STATE`, the reply objects' `TCB` words and the kernel base) except the sender's `FAULT_W1` word (TCB offset
3392), which AArch64's `trap_extra_mrs` sets. -/
def XferFrA (st : machine.Store S) [L : LawfulStore st] (T Rp : Set U64) (snd : U64) (s s' : S) : Prop :=
  L.actionW s' = L.actionW s ∧ L.curW s' = L.curW s ∧ L.idleW s' = L.idleW s ∧ L.cscW s' = L.cscW s ∧
    (∀ y ∈ T, ∀ K : U64, 3328 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → (y = snd → K.val ≠ 3392) →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
    (∀ r ∈ Rp, L.mem s' (rTcbA r) = L.mem s (rTcbA r)) ∧ L.ksb s' = L.ksb s

theorem XferFr.toA {snd : U64} {s s' : S} (h : XferFr st T Rp s s') : XferFrA st T Rp snd s s' :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun y hy K a b c _ => h.2.2.2.2.1 y hy K a b c, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem XferFrA.refl (snd : U64) (s : S) : XferFrA st T Rp snd s s :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ _ _ _ _ _ => rfl, fun _ _ => rfl, rfl⟩

theorem XferFrA.trans {snd : U64} {s1 s2 s3 : S} (h1 : XferFrA st T Rp snd s1 s2) (h2 : XferFrA st T Rp snd s2 s3) :
    XferFrA st T Rp snd s1 s3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
    fun y hy K a b c d => (h2.2.2.2.2.1 y hy K a b c d).trans (h1.2.2.2.2.1 y hy K a b c d),
    fun r hr => (h2.2.2.2.2.2.1 r hr).trans (h1.2.2.2.2.2.1 r hr), h2.2.2.2.2.2.2.trans h1.2.2.2.2.2.2⟩

/-- a64: **the message transfer keeps the invariants within `XferFrA`** (`XferOK` with the A64 frame: the
sender's `FAULT_W1` word may change). `xferOK_ofA` (QueueXfer) proves it from the placement facts. -/
def XferOKA (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (G : S → Prop) : Prop :=
  ∀ (Ac X : Set U64) (Q : U64 → U64 → List U64) (R : U64 → List U64) (s : S) (a : A) (snd ep badge : U64)
    (grant : Bool) (rcv : U64), snd ∈ T → rcv ∈ T →
    SchedQueuesInvX st T Cs Ω H X s Q R → BoundInv st T Ac s → XInv st T Cs Ω Sg Rp Scs Nt Z s →
    SCsOK st T Ω Sg Scs Z Ac s → SgOK st Ω Sg s → UserOK st T Cs Ω H U s → G s →
    ipc.do_ipc_transfer st ar s a snd ep badge grant rcv ⦃ s' =>
      SchedQueuesInvX st T Cs Ω H X s' Q R ∧ BoundInv st T Ac s' ∧ XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧
      SCsOK st T Ω Sg Scs Z Ac s' ∧ SgOK st Ω Sg s' ∧ XferFrA st T Rp snd s s' ∧ G s' ⦄

/-- The x86-shaped hypothesis implies the A64 one. -/
theorem XferOK.toA {A : Type _} {ar : machine.Arch A} {U : Set U64} {G : S → Prop}
    (h : XferOK st ar T Cs Ω H Sg Rp Scs Nt Z U G) : XferOKA st ar T Cs Ω H Sg Rp Scs Nt Z U G :=
  fun Ac X Q R s a snd ep badge grant rcv hs hr h1 h2 h3 h4 h5 h6 h7 =>
    WP.spec_mono (h Ac X Q R s a snd ep badge grant rcv hs hr h1 h2 h3 h4 h5 h6 h7)
      fun _ ⟨a1, a2, a3, a4, a5, a6, a7⟩ => ⟨a1, a2, a3, a4, a5, a6.toA, a7⟩

/-! ## QueueIpc twins -/

-- a64: `_A` twin (`XferOKA`) of the QueueIpc lemma below
/-- seL4 `receiveIPC`'s end on a sending endpoint: the head sender is
dequeued, the message transferred, and the sender either becomes blocked on
the receiver's reply (a call, with the reply bookkeeping and SC donation),
inactive, or running. a64: named premise **[J] `hRV`** (`RunVcpuInv`), with the receiver not in
`TS_RUNNING_VM` (`hvm`): the receiver, to which a call donates its SC, runs no VCPU. -/
theorem endpoint.receive_from_sender.ipcA {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {U : Set U64} {G : S → Prop} (hxf : XferOKA st ar T Cs Ω H Sg Rp Scs Nt Z U G) (s : S) (a : A)
    (thread e reply : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (hG : ∀ s1, H e = some .ep → (L.epState s e = 1#u64 ∨ L.epState s e = 2#u64) →
      endpoint.ep_dequeue st s e (L.epQ s e).head = ok s1 → G s1)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hU : UserOK st T Cs Ω H U s)
    (hc : CanBlock st T Ac s thread)
    (hH : H e = some .ep) (hst : L.epState s e ≠ 0#u64 ∧ L.epState s e ≠ 2#u64)
    (hr : reply ≠ 0#u64 → reply ∈ Rp ∧ (L.mem s (rTcbA reply) = 0#u64 ∨ L.mem s (rTcbA reply) = thread))
    (hRV : RunVcpuInv st T s) (hvm : L.mem s (stA thread) ≠ sched.TS_RUNNING_VM) :
    endpoint.receive_from_sender st ar s a thread e reply ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  have hT := h.tcbs
  have ht := hc.mem
  have hst1 : L.epState s e = 1#u64 := by
    rcases ep_state3 h hH with e0 | e0 | e0
    · exact absurd e0 hst.1
    · exact e0
    · exact absurd e0 hst.2
  obtain ⟨hdT, hbe, hds, -⟩ := ep_head h hH (Or.inl rfl) hst1
  have hds := hds rfl
  set hd := (L.epQ s e).head with hhd
  have hdt : hd ≠ thread := fun e' => hc.nb (by rw [← e', hds]; exact Or.inl rfl)
  have hdi : L.idleW s ≠ hd := fun e' => hB.idleNB (by rw [e', hds]; exact Or.inl (Or.inl rfl))
  -- the reply object is unused
  have hr' : reply ≠ 0#u64 → reply ∈ Rp ∧ L.mem s (rTcbA reply) = 0#u64 := fun h0 => by
    obtain ⟨h1, h2⟩ := hr h0
    refine ⟨h1, h2.resolve_right fun e' => hX.noref (hT _ ht) hc.nrp (fun e2 => hc.nb (Or.inr (Or.inl e2))) _ h1 e'⟩
  unfold endpoint.receive_from_sender
  step with endpoint.get_queue.spec as ⟨q, eq⟩
  subst eq
  have hdq := endpoint.ep_dequeue.inv s hd Q R h hdT (by simp) (Or.inl hds)
  rw [hbe] at hdq
  refine WP.spec_bind (spec_eq' hdq) ?_
  rintro s1 ⟨eq1, h1, f1, o1, n1, k1, c1, nc1⟩
  obtain ⟨hB1, hX1, hS1, hSg1, ea1, ec1, ei1⟩ := frame_bx h hB hX hS hSg f1 o1 n1 k1
    (TmFr.mk0 ⟨k1, fun y hy K a b c => f1 y hy K (by omega) c (by omega) (by omega),
      fun c hc o ho => nc1 c hc o (by omega) (by omega), fun n' hn' => o1 _ (hSg.sub _ (hX.1.ntB n' hn').2)⟩)
  step with obj.Tcb.block_badge.any as ⟨badge, _⟩
  step with obj.Tcb.block_flags.any as ⟨flags, _⟩
  simp only [lift, Aeneas.Std.bind_ok]
  refine WP.spec_bind (hxf _ _ _ _ s1 a hd e badge _ thread hdT ht h1 hB1 hX1 hS1 hSg1 (hU.ksb k1) (hG s1 hH (Or.inl hst1) eq1)) ?_
  rintro s2 ⟨h2, hB2, hX2, hS2, hSg2, ⟨ea2, ec2, ei2, ecs2, f2, o2, -⟩, -⟩
  refine WP.spec_bind (endpoint.unblock_sporadic.all s2 hd h2 hB2 hX2 hS2 hSg2 hdT) ?_
  rintro s3 ⟨h3, hB3, hX3, hS3, hSg3, ea3, ec3, ei3, f3, r3⟩
  step with obj.Tcb.fault_type.any as ⟨ftype, _⟩
  -- facts at `s3`
  have F : ∀ y ∈ T, ∀ K : U64, 3328 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 → K.val ≠ 3392 →
      L.mem s3 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K h0 hK hK8 h1 h2' h9 => (f3 y hy K hK hK8).trans ((f2 y hy K h0 hK hK8 fun _ => h9).trans (f1 y hy K hK hK8 h1 h2'))
  have st3 : ∀ y ∈ T, L.mem s3 (stA y) = L.mem s (stA y) := fun y hy => by
    rw [stA_eq]; exact F y hy _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have iq3 : ∀ y ∈ T, L.mem s3 (inqA y) = L.mem s (inqA y) := fun y hy => by
    rw [inqA_eq]; exact F y hy _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have ea : L.actionW s3 = L.actionW s := ea3.trans (ea2.trans ea1)
  have ei : L.idleW s3 = L.idleW s := ei3.trans (ei2.trans ei1)
  have hds3 : L.mem s3 (stA hd) = sched.TS_BLOCKED_ON_SEND := (st3 hd hdT).trans hds
  have rv3 : L.mem s3 (runVcpuA thread) = 0#u64 :=
    (F thread ht 3672#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).trans (hRV.zero ht hvm)
  obtain ⟨dq, dr, da⟩ := blocked_out h3 hdT (by rw [hds3]; exact blocked_not_runnable (Or.inl rfl))
  have hXc : ExcT {y | y ∈ (∅ : Set U64) ∨ y = hd} hd := fun y hy => by simpa using hy
  have hx3 : hd ∈ {y | y ∈ (∅ : Set U64) ∨ y = hd} := Or.inr rfl
  have rt3 : ∀ r ∈ Rp, L.mem s3 (rTcbA r) = L.mem s (rTcbA r) := fun r hr0 =>
    (r3 r hr0).trans ((o2 r hr0).trans (o1 _ (hSg.sub _ (hX.1.tcbW hr0))))
  have sc3 : L.mem s3 (scA hd) = L.mem s (scA hd) := by
    rw [scA_eq]; exact F hd hdT _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have hdA : L.mem s3 (scA hd) ≠ 0#u64 → L.mem s3 (scA hd) ∈ Ac := fun h0 => by
    rw [sc3] at h0 ⊢
    exact hB.sact hd hdT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [hds]; exact Or.inl rfl)))))))
      h0
  have E1 : ∀ cd : Bool, reply ≠ 0#u64 → ipc.reply_push st ar s3 a hd thread reply cd ⦃ s' _ =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := fun cd h0 =>
    WP.spec_mono (ipc.reply_push.ipc hA s3 a hd thread reply cd Q R h3 hXc (Or.inl hx3) hB3 hX3 hS3 hSg3 hdT dq dr da
      (by rw [ei]; exact hdi) (by rw [hds3]; exact send_ne) (hr' h0).1 h0 (by rw [rt3 _ (hr' h0).1]; exact (hr' h0).2)
      ht (Ne.symm hdt) (by rw [iq3 _ ht]; exact hc.nq) (by rw [iq3 _ ht]; exact hc.nr) (by rw [ea]; exact hc.na)
      (by rw [ei]; exact hc.ni) hdA rv3)
      fun r hh => by obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at hh ⊢; exact hh.1
  have E1' : reply ≠ 0#u64 → (do
      let i3 ← obj.Tcb.sc st hd s3
      let can_donate ← if (i3 != 0#u64) = true then ok (ftype != fl4_abi.consts.fault.Timeout) else ok false
      ipc.reply_push st ar s3 a hd thread reply can_donate) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
    intro h0
    step with obj.Tcb.sc.spec as ⟨i3, _⟩
    split <;> (try simp only [Aeneas.Std.bind_ok]) <;> exact E1 _ h0
  have E2 : (do
      let s4 ← sched.set_thread_state st s3 hd sched.TS_INACTIVE
      ok (s4, a)) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
    refine WP.spec_bind (sts_all s3 hd _ Q R h3 hB3 hX3 hS3 hSg3 hdT not_blocked_inactive inactive_ne
      (Or.inl hx3) (hX3.noref (h3.tcbs _ hdT) (by rw [hds3]; exact send_ne.1) (by rw [hds3]; exact send_ne.2))
      ⟨fun c hc' p hp hm => absurd hm (h3.notQ hdT dq hc' hp),
        fun c hc' hm => absurd hm (h3.notR hdT dr hc'), fun e' => absurd e' da⟩) fun s4 hh => ?_
    obtain ⟨h4, hB4, hX4, hS4, hSg4, -, -⟩ := hh
    exact (WP.spec_ok _).2 ⟨⟨Q, R, h4.congrX empty_congr'⟩, hB4, hX4, hS4, hSg4⟩
  have E3 : (do
      let s4 ← sched.set_thread_state st s3 hd sched.TS_RUNNING
      let s5 ← sched.possible_switch_to st s4 hd
      ok (s5, a)) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
    refine WP.spec_bind (sts_all s3 hd _ Q R h3 hB3 hX3 hS3 hSg3 hdT not_blocked_running running_ne
      (Or.inl hx3) (hX3.noref (h3.tcbs _ hdT) (by rw [hds3]; exact send_ne.1) (by rw [hds3]; exact send_ne.2))
      ⟨fun _ _ _ _ _ => runnable_running, fun _ _ _ => runnable_running,
        fun _ => runnable_running⟩) fun s4 hh => ?_
    obtain ⟨h4, hB4, hX4, hS4, hSg4, e4, k4⟩ := hh
    have h4' := h4.congrX empty_congr'
    refine WP.spec_bind (sched.possible_switch_to.sch s4 hd Q R h4' hB4 hSg4 hdT (by rw [e4]; exact runnable_running)
      (fun h0 => by rw [k4.scf hdT] at h0 ⊢; exact hdA h0))
      fun s5 hh => ?_
    obtain ⟨p5, -, -⟩ := hh
    exact (WP.spec_ok _).2 ⟨p5.inv, p5.bnd, hX4.fr p5.fr, hS4.fr p5.fr, hSg4.fr p5.fr⟩
  repeat' split
  all_goals first
    | exact E2
    | exact E3
    | (rename_i hh; exact E1' (by simpa using hh))

/-! ## `send_ipc` -/

-- a64: `_A` twin (`XferOKA`) of the QueueIpc lemma below
/-- seL4 `sendIPC`: on an idle or sending endpoint the sender blocks (or
returns); on a receiving endpoint the head receiver is dequeued, gets the
message, the reply bookkeeping is done (reply object unlinked from the
receiver, pushed for a call or a fault, with SC donation), and the receiver
runs.  Caller-level preconditions: `t` can block (`CanBlock`: not blocked,
queued, the switch-to candidate or the idle thread), and if it may donate it
is bound (`hdon`): on the syscall path the sender is the current thread,
which has an SC in MCS, and on the fault path FL4 sets `can_donate` to
`t.sc != 0`. a64: named premise **[J] `hRV`** (`RunVcpuInv`): the receiver, blocked on the endpoint, runs
no VCPU, for the donation's `migrate_tcb`. -/
theorem endpoint.send_ipc.ipcA {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {U : Set U64}
    {G : S → Prop} (hxf : XferOKA st ar T Cs Ω H Sg Rp Scs Nt Z U G) (s : S) (a : A) (blocking do_call : Bool)
    (badge : U64) (can_grant can_grant_reply can_donate : Bool) (t e : U64)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (hG : ∀ s1, H e = some .ep → (L.epState s e = 1#u64 ∨ L.epState s e = 2#u64) →
      endpoint.ep_dequeue st s e (L.epQ s e).head = ok s1 → G s1)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hU : UserOK st T Cs Ω H U s)
    (hc : CanBlock st T Ac s t) (hdon : can_donate = true → L.mem s (scA t) ≠ 0#u64)
    (hH : H e = some .ep) (hRV : RunVcpuInv st T s) :
    endpoint.send_ipc st ar s a blocking do_call badge can_grant can_grant_reply can_donate t e
      ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  have hidle := hc.ni
  have hT := h.tcbs
  have ht := hc.mem
  have hta := hT t ht
  rcases ep_state3 h hH with e0 | e0 | e0
  · exact WP.spec_mono (endpoint.send_ipc.block ar s a blocking do_call badge can_grant can_grant_reply can_donate
      t e Q R h hB hX hS hSg (fun _ => hc) hH (Or.inl e0)) fun r hh => by
        obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at hh ⊢; exact ⟨⟨Q, R, hh.1⟩, hh.2⟩
  · exact WP.spec_mono (endpoint.send_ipc.block ar s a blocking do_call badge can_grant can_grant_reply can_donate
      t e Q R h hB hX hS hSg (fun _ => hc) hH (Or.inr e0)) fun r hh => by
        obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at hh ⊢; exact ⟨⟨Q, R, hh.1⟩, hh.2⟩
  -- a receiving endpoint
  obtain ⟨hdT, hbe, -, hds⟩ := ep_head h hH (Or.inr rfl) e0
  have hds := hds rfl
  set hd := (L.epQ s e).head with hhd
  have hdt : hd ≠ t := fun e' => hc.nb (by rw [← e', hds]; exact Or.inr (Or.inl rfl))
  have hdi : L.idleW s ≠ hd := fun e' => hB.idleNB (by rw [e', hds]; exact Or.inl (Or.inr (Or.inl rfl)))
  have hdta := hT hd hdT
  unfold endpoint.send_ipc
  step with obj.Ep.state.spec as ⟨v, hv⟩
  have hv2 : v = 2#u64 := hv.trans e0
  rw [hv2]
  simp only [ep_idle_val, ep_send_val', show ¬ ((2#u64) = 0#u64) from by decide,
    show ¬ ((2#u64) = 1#u64) from by decide, ↓reduceIte]
  have hsub := hSg.sub
  step with endpoint.get_queue.spec as ⟨q, eq⟩
  subst eq
  have hdq := endpoint.ep_dequeue.inv s hd Q R h hdT (by simp) (Or.inr (Or.inl hds))
  rw [hbe] at hdq
  refine WP.spec_bind (spec_eq' hdq) ?_
  rintro s1 ⟨eq1, h1, f1, o1, n1, k1, c1, nc1⟩
  obtain ⟨hB1, hX1, hS1, hSg1, ea1, ec1, ei1⟩ := frame_bx h hB hX hS hSg f1 o1 n1 k1
    (TmFr.mk0 ⟨k1, fun y hy K a b c => f1 y hy K (by omega) c (by omega) (by omega),
      fun c hc o ho => nc1 c hc o (by omega) (by omega), fun n' hn' => o1 _ (hSg.sub _ (hX.1.ntB n' hn').2)⟩)
  refine WP.spec_bind (hxf _ _ _ _ s1 a t e badge can_grant hd ht hdT h1 hB1 hX1 hS1 hSg1 (hU.ksb k1) (hG s1 hH (Or.inr e0) eq1)) ?_
  rintro s2 ⟨h2, hB2, hX2, hS2, hSg2, ⟨ea2, ec2, ei2, ecs2, f2, o2, -⟩, -⟩
  have F : ∀ y ∈ T, ∀ K : U64, 3328 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 → K.val ≠ 3392 →
      L.mem s2 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K h0 hK hK8 h1' h2' h9 => (f2 y hy K h0 hK hK8 fun _ => h9).trans (f1 y hy K hK hK8 h1' h2')
  have Fst : ∀ y ∈ T, L.mem s2 (stA y) = L.mem s (stA y) := fun y hy => by
    rw [stA_eq]; exact F y hy _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have Frp : ∀ y ∈ T, L.mem s2 (replyA y) = L.mem s (replyA y) := fun y hy =>
    F y hy _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have Fiq : ∀ y ∈ T, L.mem s2 (inqA y) = L.mem s (inqA y) := fun y hy => by
    rw [inqA_eq]; exact F y hy _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have Fsc : ∀ y ∈ T, L.mem s2 (scA y) = L.mem s (scA y) := fun y hy => by
    rw [scA_eq]; exact F y hy _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have ea2' : L.actionW s2 = L.actionW s := ea2.trans ea1
  have ei2' : L.idleW s2 = L.idleW s := ei2.trans ei1
  step with obj.Tcb.reply_obj.spec as ⟨i, ei⟩
  have hds2 : L.mem s2 (stA hd) = sched.TS_BLOCKED_ON_RECV := (Fst hd hdT).trans hds
  have rv2 : L.mem s2 (runVcpuA hd) = 0#u64 :=
    (F hd hdT 3672#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).trans
      (hRV.blocked hdT (by rw [hds]; exact Or.inr (Or.inl rfl)))
  -- the reply object leaves the receiver
  refine WP.spec_bind (Pₘ := fun s3 => ∃ X3 : Set U64, SchedQueuesInvX st T Cs Ω H X3 s3 Q R ∧ BoundInv st T Ac s3 ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z s3 ∧ SCsOK st T Ω Sg Scs Z Ac s3 ∧ SgOK st Ω Sg s3 ∧ ExcT X3 hd ∧
      (hd ∈ X3 ∨ ¬ Blocked (L.mem s3 (stA hd))) ∧ ¬ Runnable (L.mem s3 (stA hd)) ∧
      (hd ∈ X3 → L.mem s3 (replyA hd) = 0#u64) ∧ (hd ∉ X3 → L.mem s3 (stA hd) = sched.TS_INACTIVE) ∧
      ((i != 0#u64) = true → hd ∉ X3 ∧ i ∈ Rp ∧ L.mem s3 (rTcbA i) = 0#u64) ∧
      L.mem s3 (stA t) = L.mem s (stA t) ∧ L.mem s3 (inqA t) = L.mem s (inqA t) ∧
      L.mem s3 (scA t) = L.mem s (scA t) ∧ L.actionW s3 ≠ t ∧ L.idleW s3 = L.idleW s ∧
      L.mem s3 (scA hd) = L.mem s (scA hd) ∧ L.mem s3 (runVcpuA hd) = 0#u64) ?_ ?_
  · split
    · rename_i hi
      have hi0 : i ≠ 0#u64 := by simpa using hi
      obtain ⟨hiR, hit⟩ := hX2.2.1.recv hd hdT hds2 (by rw [← ei]; exact hi0)
      rw [← ei] at hiR hit
      refine WP.spec_mono (ipc.reply_unlink.inv s2 i hd Q R h2 hdT hX2.1 hsub hiR hit
        (by rw [hds2]; exact blocked_not_runnable (Or.inr (Or.inl rfl))) (Or.inl (Or.inr rfl))) fun s3 hh => ?_
      obtain ⟨h3, e3, k3, z3⟩ := hh
      have hclr : ∀ r ∈ Rp, L.mem s2 (rTcbA r) = hd → L.mem s3 (rTcbA r) = 0#u64 := by
        intro r hr er
        obtain ⟨-, -, b2, -⟩ := hX2.2.1.back r hr (by rw [er]; exact fun e0 => hdta.ne0 (by rw [e0]; rfl))
        rw [er, ← ei] at b2; rw [← b2]; exact z3
      refine ⟨_, h3, hB2.keepT h2 k3 (by rw [e3]; exact not_blocked_inactive) (by rw [e3]; exact inactive_ne.1),
        hX2.keepT k3 (by rw [e3]; exact inactive_ne) hclr, hS2.keepT hX2 k3,
        ⟨hsub, fun b hb => by rw [k3.ksb]; exact hSg2.ks b hb, fun o h1' h2' => by rw [k3.ksb]; exact hSg2.ksΩ o h1' h2'⟩,
        fun y hy => ?_, Or.inr (by rw [e3]; exact not_blocked_inactive), by rw [e3]; exact not_runnable_inactive,
        fun hm => absurd rfl hm.2, fun _ => e3, fun _ => ⟨fun hm => hm.2 rfl, hiR, z3⟩,
        (k3.stf ht (Ne.symm hdt)).trans (Fst t ht), (k3.inqf ht).trans (Fiq t ht), (k3.scf ht).trans (Fsc t ht),
        ?_, k3.idleW.trans ei2', (k3.scf hdT).trans (Fsc hd hdT),
        (k3.fld hd hdT 3672#u64 (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)).trans rv2⟩
      · obtain ⟨hy1, hy2⟩ := hy
        rcases hy1 with hy1 | hy1
        · exact absurd hy1 (Set.notMem_empty _)
        · exact absurd hy1 hy2
      · rcases k3.act with e' | e'
        · rw [e', ea2']; exact hc.na
        · rw [e']; exact fun e2 => notT_small hT (by simp) (e2 ▸ ht)
    · rename_i hi
      have hi0 : i = 0#u64 := by simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hi; exact hi
      refine (WP.spec_ok _).2 ⟨_, h2, hB2, hX2, hS2, hSg2, fun y hy => by simpa using hy, Or.inl (Or.inr rfl),
        by rw [hds2]; exact blocked_not_runnable (Or.inr (Or.inl rfl)), fun _ => by rw [← ei, hi0],
        fun hm => absurd (Or.inr rfl) hm, fun hi' => absurd hi0 (by simpa using hi'),
        Fst t ht, Fiq t ht, Fsc t ht, by rw [ea2']; exact hc.na, ei2', Fsc hd hdT, rv2⟩
  rintro s3 ⟨X3, h3, hB3, hX3, hS3, hSg3, hXc3, hx3, hnr3, hz3, hin3, hpu3, st3, iq3, sc3, na3, ei3, shd3, rv3⟩
  have hdA3 : L.mem s3 (scA hd) ≠ 0#u64 → L.mem s3 (scA hd) ∈ Ac := fun h0 => by
    rw [shd3] at h0 ⊢
    exact hB.sact hd hdT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [hds]; exact Or.inr (Or.inl rfl))))))))
      h0
  have htA3 : L.mem s3 (scA t) ≠ 0#u64 → L.mem s3 (scA t) ∈ Ac := fun h0 => by
    rw [sc3] at h0 ⊢; exact hc.ac h0
  have htq3 : (L.mem s3 (inqA t) &&& sched.Q_QUEUED) = 0#u64 := by rw [iq3]; exact hc.nq
  have htr3 : (L.mem s3 (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by rw [iq3]; exact hc.nr
  have hnb3 : ¬ Blocked (L.mem s3 (stA t)) := by rw [st3]; exact hc.nb
  have hnrp3 : L.mem s3 (stA t) ≠ sched.TS_BLOCKED_ON_REPLY := by rw [st3]; exact hc.nrp
  have hcold3 : L.mem s3 (stA t) ≠ sched.TS_BLOCKED_ON_REPLY ∧ L.mem s3 (stA t) ≠ sched.TS_BLOCKED_ON_RECV :=
    ⟨hnrp3, fun e' => hnb3 (Or.inr (Or.inl e'))⟩
  obtain ⟨dq, dr, da⟩ := blocked_out h3 hdT hnr3
  have hidle3 : L.idleW s3 ≠ t := by rw [ei3]; exact hidle
  have hnt3 : ∀ r ∈ Rp, L.mem s3 (rTcbA r) ≠ t := hX3.noref hta hcold3.1 hcold3.2
  have hnd3 : ∀ r ∈ Rp, L.mem s3 (rTcbA r) ≠ hd := by
    by_cases hm : hd ∈ X3
    · exact hX3.noref0 hdta (hz3 hm)
    · have e' := hin3 hm
      exact hX3.noref hdta (by rw [e']; exact inactive_ne.1) (by rw [e']; exact inactive_ne.2)
  refine WP.spec_bind (Pₘ := fun r : S × A => ∃ X4 : Set U64, (∃ Q4 R4, SchedQueuesInvX st T Cs Ω H X4 r.1 Q4 R4) ∧
      BoundInv st T Ac r.1 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ SCsOK st T Ω Sg Scs Z Ac r.1 ∧ SgOK st Ω Sg r.1 ∧
      ExcT X4 hd ∧ (hd ∈ X4 ∨ ¬ Blocked (L.mem r.1 (stA hd))) ∧ (∀ r' ∈ Rp, L.mem r.1 (rTcbA r') ≠ hd) ∧
      (L.mem r.1 (scA hd) ≠ 0#u64 → L.mem r.1 (scA hd) ∈ Ac)) ?_ ?_
  rotate_left
  · rintro ⟨s4, a1⟩ ⟨X4, ⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4, hXc4, hx4, hnr4, hdA4⟩
    try simp only [WP.uncurry'_pair]
    exact send_tail s4 a1 hd Q4 R4 h4 hB4 hX4 hS4 hSg4 hdT hXc4 hx4 hnr4 hdA4
  have Ppush : ∀ cd : Bool, (i != 0#u64) = true → ipc.reply_push st ar s3 a t hd i cd ⦃ r => ∃ X4 : Set U64,
      (∃ Q4 R4, SchedQueuesInvX st T Cs Ω H X4 r.1 Q4 R4) ∧
      BoundInv st T Ac r.1 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ SCsOK st T Ω Sg Scs Z Ac r.1 ∧ SgOK st Ω Sg r.1 ∧
      ExcT X4 hd ∧ (hd ∈ X4 ∨ ¬ Blocked (L.mem r.1 (stA hd))) ∧ (∀ r' ∈ Rp, L.mem r.1 (rTcbA r') ≠ hd) ∧
      (L.mem r.1 (scA hd) ≠ 0#u64 → L.mem r.1 (scA hd) ∈ Ac) ⦄ := by
    intro cd hi
    obtain ⟨hdX, hiR, hiz⟩ := hpu3 hi
    have hi0 : i ≠ 0#u64 := by simpa using hi
    refine WP.spec_mono (ipc.reply_push.ipc hA s3 a t hd i cd Q R h3
      (fun y hy => absurd (hXc3 y hy ▸ hy) hdX) (Or.inr hnb3) hB3 hX3 hS3 hSg3 ht htq3 htr3 na3 hidle3 hcold3
      hiR hi0 hiz hdT hdt dq dr da (by rw [ei3]; exact hdi) htA3 rv3) fun r hh => ?_
    obtain ⟨s4, a4⟩ := r
    simp only [WP.uncurry'_pair] at hh
    obtain ⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, st4, sc4⟩ := hh
    have e4 : L.mem s4 (stA hd) = sched.TS_INACTIVE := (st4 hd hdT hdt).trans (hin3 hdX)
    exact ⟨∅, ⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4, fun y hy => absurd hy (Set.notMem_empty _),
      Or.inr (by rw [e4]; exact not_blocked_inactive),
      hX4.noref hdta (by rw [e4]; exact inactive_ne.1) (by rw [e4]; exact inactive_ne.2), fun h0 => by
        rcases sc4 with e | e
        · rw [e] at h0 ⊢; exact hdA3 h0
        · rw [e] at h0 ⊢; exact htA3 h0⟩
  have Pinact : (do
      let s5 ← sched.set_thread_state st s3 t sched.TS_INACTIVE
      ok (s5, a)) ⦃ r => ∃ X4 : Set U64, (∃ Q4 R4, SchedQueuesInvX st T Cs Ω H X4 r.1 Q4 R4) ∧
      BoundInv st T Ac r.1 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ SCsOK st T Ω Sg Scs Z Ac r.1 ∧ SgOK st Ω Sg r.1 ∧
      ExcT X4 hd ∧ (hd ∈ X4 ∨ ¬ Blocked (L.mem r.1 (stA hd))) ∧ (∀ r' ∈ Rp, L.mem r.1 (rTcbA r') ≠ hd) ∧
      (L.mem r.1 (scA hd) ≠ 0#u64 → L.mem r.1 (scA hd) ∈ Ac) ⦄ := by
    refine WP.spec_bind (sts_all s3 t _ Q R h3 hB3 hX3 hS3 hSg3 ht not_blocked_inactive inactive_ne (Or.inr hnb3)
      hnt3 ⟨fun c hc' p hp hm => absurd hm (h3.notQ ht htq3 hc' hp), fun c hc' hm => absurd hm (h3.notR ht htr3 hc'),
        fun e' => absurd e' na3⟩) fun s4 hh => ?_
    obtain ⟨h4, hB4, hX4, hS4, hSg4, -, k4⟩ := hh
    refine (WP.spec_ok _).2 ⟨{y | y ∈ X3 ∧ y ≠ t}, ⟨Q, R, h4⟩, hB4, hX4, hS4, hSg4,
      fun y hy => hXc3 y hy.1, ?_, fun r hr => ?_, fun h0 => by rw [k4.scf hdT] at h0 ⊢; exact hdA3 h0⟩
    · rcases hx3 with hm | hnb
      · exact Or.inl ⟨hm, hdt⟩
      · exact Or.inr (by rw [k4.stf hdT hdt]; exact hnb)
    · rcases k4.rtcb r hr with e' | ⟨-, e'⟩
      · rw [e']; exact hnd3 r hr
      · rw [e']; exact fun e2 => hdta.ne0 (by rw [← e2]; rfl)
  have Pok : (ok (s3, a) : Result (S × A)) ⦃ r => ∃ X4 : Set U64, (∃ Q4 R4, SchedQueuesInvX st T Cs Ω H X4 r.1 Q4 R4) ∧
      BoundInv st T Ac r.1 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ SCsOK st T Ω Sg Scs Z Ac r.1 ∧ SgOK st Ω Sg r.1 ∧
      ExcT X4 hd ∧ (hd ∈ X4 ∨ ¬ Blocked (L.mem r.1 (stA hd))) ∧ (∀ r' ∈ Rp, L.mem r.1 (rTcbA r') ≠ hd) ∧
      (L.mem r.1 (scA hd) ≠ 0#u64 → L.mem r.1 (scA hd) ∈ Ac) ⦄ :=
    (WP.spec_ok _).2 ⟨X3, ⟨Q, R, h3⟩, hB3, hX3, hS3, hSg3, hXc3, hx3, hnd3, hdA3⟩
  have Pdon : can_donate = true → (do
      let i2 ← obj.Tcb.sc st hd s3
      if i2 = 0#u64 then do
          let i3 ← obj.Tcb.sc st t s3
          schedcontext.donate st ar s3 a i3 hd
        else ok (s3, a)) ⦃ r => ∃ X4 : Set U64, (∃ Q4 R4, SchedQueuesInvX st T Cs Ω H X4 r.1 Q4 R4) ∧
      BoundInv st T Ac r.1 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ SCsOK st T Ω Sg Scs Z Ac r.1 ∧ SgOK st Ω Sg r.1 ∧
      ExcT X4 hd ∧ (hd ∈ X4 ∨ ¬ Blocked (L.mem r.1 (stA hd))) ∧ (∀ r' ∈ Rp, L.mem r.1 (rTcbA r') ≠ hd) ∧
      (L.mem r.1 (scA hd) ≠ 0#u64 → L.mem r.1 (scA hd) ∈ Ac) ⦄ := by
    intro hcd
    step with obj.Tcb.sc.spec as ⟨i2, ei2⟩
    split
    · rename_i hi2
      step with obj.Tcb.sc.spec as ⟨i3, ei3'⟩
      refine WP.spec_mono (schedcontext.donate.ipc hA s3 a i3 hd t Q R h3 hB3 hX3 hS3 hSg3 ht ei3'.symm
        (by rw [ei3', sc3]; exact hdon hcd) ⟨htq3, htr3, na3⟩ hidle3 hdT (by rw [← ei2, hi2]) dq dr da hdt
        (by rw [ei3']; exact htA3 (by rw [sc3]; exact hdon hcd)) (by rw [ei3]; exact hdi) rv3)
        fun r hh => ?_
      obtain ⟨s4, a4⟩ := r
      simp only [WP.uncurry'_pair] at hh
      obtain ⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, st4, rp4, sd4⟩ := hh
      refine ⟨X3, ⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4, hXc3, ?_, ?_,
        fun _ => by rw [sd4, ei3']; exact htA3 (by rw [sc3]; exact hdon hcd)⟩
      · rcases hx3 with hm | hnb
        · exact Or.inl hm
        · exact Or.inr (by rw [st4 hd hdT]; exact hnb)
      · by_cases hm : hd ∈ X3
        · exact hX4.noref0 hdta (by rw [rp4 hd hdT]; exact hz3 hm)
        · have e' : L.mem s4 (stA hd) = sched.TS_INACTIVE := (st4 hd hdT).trans (hin3 hm)
          exact hX4.noref hdta (by rw [e']; exact inactive_ne.1) (by rw [e']; exact inactive_ne.2)
    · exact Pok
  split
  · repeat' split
    all_goals first
      | exact Pinact
      | exact Ppush _ (by assumption)
  · step with obj.Tcb.fault_type.any as ⟨i1, _⟩
    repeat' split
    all_goals first
      | exact Pinact
      | exact Ppush _ (by assumption)
      | exact Pdon (by assumption)
      | exact Pok


-- a64: `_A` twin (`XferOKA`) of the QueueIpc lemma below
/-- seL4 `receiveIPC`, all of it: the reply bookkeeping (`take_reply`), the
active bound notification (`complete_signal`), the bound notification's SC
going back (`maybe_return_sched_context`), blocking or polling on an idle or
receiving endpoint, and receiving from a sending endpoint.  Besides the
invariants, only caller-level facts: `t` can block, the cap names a heap
endpoint, a reply cap names a reply object, and `Nt` are heap notifications
(true of the instantiation `Nt := H.ntfns`). a64: named premise **[J] `hRV`**: `RunVcpuInv` at the states
`receive_ipc` reaches before its end on the endpoint (`RecvPre`, after `take_reply` and
`maybe_return_sched_context`), and the caller-level fact `hvm` that the receiver is not in `TS_RUNNING_VM`
(`take_reply` and `maybe_return_sched_context` keep its state, `RecvPre.stt`): the SC donations of a call
(`receive_from_sender`) and of the bound notification (`complete_signal`) go to the receiver, which then runs
no VCPU. Proved through `endpoint.receive_ipc.inv_rp`. -/
theorem endpoint.receive_ipc.ipcA {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {U : Set U64}
    {G : S → Prop} (hxf : XferOKA st ar T Cs Ω H Sg Rp Scs Nt Z U G) (s : S) (a : A) (t : U64)
    (cap : capability.Cap) (blocking : Bool)
    (reply_cap : capability.Cap) (e : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (hG : ∀ s2 s1, RecvPre st ar s a t reply_cap s2 → H e = some .ep →
      (L.epState s2 e = 1#u64 ∨ L.epState s2 e = 2#u64) → endpoint.ep_dequeue st s2 e (L.epQ s2 e).head = ok s1 → G s1)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hU : UserOK st T Cs Ω H U s)
    (hc : CanBlock st T Ac s t)
    (hptr : capability.Cap.ptr cap = ok e) (hH : H e = some .ep)
    (hcap : ∀ p g, reply_cap = .Reply p g → p ∈ Rp)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (hRV : ∀ s2, RecvPre st ar s a t reply_cap s2 → RunVcpuInv st T s2)
    (hvm : L.mem s (stA t) ≠ sched.TS_RUNNING_VM) :
    endpoint.receive_ipc st ar s a t cap blocking reply_cap ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ :=
  endpoint.receive_ipc.inv_rp ar s a t cap blocking reply_cap e Q R h hB hX hS hSg hc hptr hH hcap
    (fun s1 a1 n hok hc1 hn hn0 hst hp1 => by
      obtain ⟨⟨Q1, R1, h1⟩, hB1, hX1, hS1, hSg1⟩ := hok
      subst hn
      obtain ⟨hn1, hn2, hn3⟩ := BoundNtfnOK.of_inv hNt hc1.mem hX1 hS1 hSg1 hn0
      refine notification.complete_signal.ipc hA s1 a1 _ t Q1 R1 h1 hB1 hX1 hS1 hSg1 hc1.mem hc1.nq hc1.nr hc1.na
        hc1.ni hn1 hn2 hn3 (fun _ h0 hS => ?_) (hRV s1 hp1)
        (by rw [RecvPre.stt Q R h hB hX hS hSg hc hcap hp1]; exact hvm)
      exfalso
      rcases hS with e | e | e | e | ⟨e1, e2⟩ | e
      · exact e hc1.nq
      · exact e hc1.nr
      · exact hc1.na e
      · exact hc1.ni e
      · exact hB1.resume e1 (by rw [e2]; exact h0)
      · rcases e with e | e
        · exact hc1.nb e
        · exact hc1.nrp e)
    (fun s2 a2 r hok hc2 hr kb ib hs0 hs2 hp => by
      obtain ⟨⟨Q2, R2, h2⟩, hB2, hX2, hS2, hSg2⟩ := hok
      exact endpoint.receive_from_sender.ipcA hA hxf s2 a2 t e r Q2 R2 (fun s1 => hG s2 s1 hp) h2 hB2 hX2 hS2 hSg2 (hU.ksb kb) hc2 hH
        ⟨hs0, hs2⟩ hr (hRV s2 hp) (by rw [RecvPre.stt Q R h hB hX hS hSg hc hcap hp]; exact hvm))

end

/-! ## RunVcpuRecv twin -/

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

-- a64: `_A` twin (`XferOKA`) of the RunVcpuRecv lemma below
/-- seL4 `receiveIPC` (`endpoint.receive_ipc.ipcA`) with named premise **[J] `hRV`** at the entry state: plain
`RunVcpuInv st T s` (`RecvPre.rvi` carries it to the states `receive_ipc.ipc` asks it at), and the caller-level
`hvm` (the receiver is not in `TS_RUNNING_VM`). -/
theorem endpoint.receive_ipc.ipc_rvA {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {U : Set U64}
    {G : S → Prop} (hxf : XferOKA st ar T Cs Ω H Sg Rp Scs Nt Z U G) (s : S) (a : A) (t : U64)
    (cap : capability.Cap) (blocking : Bool)
    (reply_cap : capability.Cap) (e : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (hG : ∀ s2 s1, RecvPre st ar s a t reply_cap s2 → H e = some .ep →
      (L.epState s2 e = 1#u64 ∨ L.epState s2 e = 2#u64) → endpoint.ep_dequeue st s2 e (L.epQ s2 e).head = ok s1 → G s1)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hU : UserOK st T Cs Ω H U s)
    (hc : CanBlock st T Ac s t)
    (hptr : capability.Cap.ptr cap = ok e) (hH : H e = some .ep)
    (hcap : ∀ p g, reply_cap = .Reply p g → p ∈ Rp)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (hRV : RunVcpuInv st T s)
    (hvm : L.mem s (stA t) ≠ sched.TS_RUNNING_VM) :
    endpoint.receive_ipc st ar s a t cap blocking reply_cap ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ :=
  endpoint.receive_ipc.ipcA hA hxf s a t cap blocking reply_cap e Q R hG h hB hX hS hSg hU hc hptr hH hcap hNt
    (fun _ hp => RecvPre.rvi Q R h hB hX hS hSg hc hcap hRV hp) hvm

end

/-! ## QueueRecv twins -/

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}

-- a64: `_A` twin (`XferOKA`) of the QueueRecv lemma below
/-- seL4 `handleRecv`: the endpoint (or notification) cap and, with a reply
right, the reply cap are looked up; `receive_ipc` / `receive_signal`, or a
cap fault.  From the hypotheses at the call: the looked-up caps are typed
(`CapTyped`), the notification states are the three states, the current
thread can block, the user words are outside the kernel objects (`UserOK`)
and the message transfer writes there (`XferOK`); cap faults are the fault
family `hfault`. -/
theorem syscall.handle_recv.bxiA {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) {U : Set U64} {G : S → Prop} (hxf : XferOKA st ar T Cs Ω H Sg Rp Scs Nt Z U G)
    {Ac : Set U64} (s : S) (a : A) (blk rep : Bool) (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hG : RecvG st ar H Rp G s a)
    (hU : UserOK st T Cs Ω H U s) (hc : CanBlock st T Ac s (L.curW s))
    (hlk : ∀ cptr, cspace.lookup_cap st s (L.curW s) cptr ⦃ r => ∀ c, r = .Ok c → CapTyped H Rp Nt c ⦄)
    (h3 : ∀ n ∈ Nt, L.epState s n ≠ 3#u64)
    (hfault : ∀ (f : error.Fault),
      faults.handle_fault st ar s a (L.curW s) f ⦃ s' _ => ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄)
    (hRV : RunVcpuInv st T s)  -- a64: [J] `RunVcpuInv`
    (hvm : L.mem s (stA (L.curW s)) ≠ sched.TS_RUNNING_VM) :  -- a64: the caller is not in `TS_RUNNING_VM`
    syscall.handle_recv st ar s a blk rep ⦃ s' _ => ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hSg, hS⟩ := h
  have CF : ∀ cptr lf, syscall.cap_fault_recv st ar s a cptr lf ⦃ s' _ =>
      ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄ := fun cptr lf => by
    unfold syscall.cap_fault_recv
    step with sched.cur_thread.spec as ⟨t1, e1⟩
    have e1' : t1 = L.curW s := e1
    subst e1'
    exact hfault _
  have ok0 : (ok (s, a) : Result (S × A)) ⦃ s' _ => ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄ :=
    (WP.spec_ok _).2 ⟨Ac, ⟨Q, R, h0⟩, hB, hX, hSg, hS⟩
  have RI : ∀ (c rc : capability.Cap) (e : U64), capability.Cap.ptr c = ok e → H e = some .ep →
      (∀ p g, rc = .Reply p g → p ∈ Rp) →
      endpoint.receive_ipc st ar s a (L.curW s) c blk rc ⦃ s' _ =>
        ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄ := fun c rc e hp hH hr =>
    WP.spec_mono (endpoint.receive_ipc.ipc_rvA hA hxf s a _ c blk rc e Q R (fun s2 s1 => hG rc e s2 s1 hr) h0 hB hX hS hSg
      hU hc hp hH hr hNt hRV hvm)
      fun r hh => by obtain ⟨s', a'⟩ := r; exact ⟨Ac, BlkOK.bxi (by simpa using hh)⟩
  have RS : ∀ n, n ∈ Nt → H n = some .ntfn → notification.receive_signal st ar s a (L.curW s) n blk ⦃ s' _ =>
      ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄ := fun n hn hH =>
    WP.spec_mono (notification.receive_signal.ipc hA s a _ n blk Q R h0 hB hX hS hSg hc hn hH (h3 n hn)
      (hRV.zero hc.mem hvm))
      fun r hh => by obtain ⟨s', a'⟩ := r; exact ⟨Ac, BlkOK.bxi (by simpa using hh)⟩
  unfold syscall.handle_recv
  step with sched.cur_thread.spec as ⟨t, et⟩
  have et' : t = L.curW s := et
  subst et'
  step with obj.Tcb.reg.spec as ⟨cptr⟩
  refine WP.spec_bind (hlk cptr) fun r hr => ?_
  split
  · rename_i c
    have hct := hr c rfl
    split
    all_goals first | exact CF _ _ | skip
    · -- an endpoint cap
      rename_i p b x rcv z w
      have hpH := hct.1 p b x rcv z w rfl
      split
      · split
        · step with obj.Tcb.reg.spec as ⟨rptr⟩
          refine WP.spec_bind (hlk rptr) fun r1 hr1 => ?_
          split
          · rename_i c1
            have hct1 := hr1 c1 rfl
            split
            all_goals first | exact CF _ _ | skip
            exact RI _ _ p rfl hpH (fun q g e => hct1.2.2 q g e)
          · split
            all_goals first | exact ok0 | exact CF _ _
        · exact RI _ _ p rfl hpH (fun q g e => by cases e)
      · exact CF _ _
    · -- a notification cap
      rename_i p b x rcv
      obtain ⟨hpN, hpH⟩ := hct.2.1 p b x rcv rfl
      refine WP.spec_bind (obj.Ntfn.bound_tcb.val s p) fun bd _ => ?_
      split
      · split
        · split
          · exact CF _ _
          · exact RS p hpN hpH
        · exact RS p hpN hpH
      · exact CF _ _
  · split
    all_goals first | exact ok0 | exact CF _ _

-- a64: `_A` twin (`XferOKA`) of the QueueRecv lemma below
/-- seL4 `handleTimeout`: the fault goes to the thread's timeout handler as a
fault IPC (`send_fault_ipc`, no donation), if the handler cap is an
endpoint.  From the hypotheses at the call: the handler cap is typed, the
thread can block, `UserOK` and `XferOK`. -/
theorem faults.handle_timeout.bxiA {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {U : Set U64}
    {G : S → Prop} (hxf : XferOKA st ar T Cs Ω H Sg Rp Scs Nt Z U G) {Ac : Set U64} (s : S) (a : A) (t : obj.Tcb)
    (f : error.Fault)
    (hG : FaultG st H G s t f)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hU : UserOK st T Cs Ω H U s) (hc : CanBlock st T Ac s t)
    (hcap : obj.Tcb.slot t layout.tcb.SLOT_TIMEOUT_HANDLER ⦃ sl =>
      obj.Slot.cap st sl s ⦃ c => CapTyped H Rp Nt c ⦄ ⦄)
    (hRV : RunVcpuInv st T s) :  -- a64: [J] `RunVcpuInv` (`send_ipc.ipc`)
    faults.handle_timeout st ar s a t f ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  have ht := hc.mem
  unfold faults.handle_timeout
  refine WP.spec_bind hcap fun sl hsl => ?_
  refine WP.spec_bind hsl fun c hct => ?_
  unfold faults.send_fault_ipc
  refine WP.spec_bind (Pₘ := fun r : Bool × S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1) ?_ ?_
  · split
    all_goals first | exact (WP.spec_ok _).2 h | skip
    rename_i p b x y g gr
    have hpH := hct.1 p b x y g gr rfl
    refine WP.spec_bind (spec_eq' (WP.spec_and (faults.set_fault.blk s t f h ht hU hc)
      (faults.set_fault.rv s t f h.1.choose_spec.choose_spec.tcbs ht))) ?_
    rintro s1 ⟨eq1, ⟨h1, hU1, hc1⟩, rv1⟩
    obtain ⟨⟨Q1, R1, q1⟩, hB1, hX1, hS1, hSg1⟩ := h1
    refine WP.spec_bind (endpoint.send_ipc.ipcA hA hxf s1 a true false b g gr false t p Q1 R1 (fun s2 => hG s1 p s2 eq1) q1 hB1 hX1 hS1 hSg1
      hU1 hc1 (fun e => by cases e) hpH (hRV.rvSt rv1)) ?_
    rintro ⟨s2, a1⟩ h2
    exact (WP.spec_ok _).2 (by simpa using h2)
  · rintro ⟨x, s2, a2⟩ h2
    exact (WP.spec_ok _).2 h2


-- a64: `_A` twin (`XferOKA`) of the QueueRecv lemma below
/-- seL4 `handleFault`: a fault IPC to the thread's fault handler when it is
an endpoint cap (donating the thread's SC if it has one), else the thread is
made inactive with no fault stored (seL4 `handleNoFaultHandler`).  From the hypotheses at the call:
the handler cap is typed, the thread can block, `UserOK` and `XferOK`. -/
theorem faults.handle_fault.bxiA {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {U : Set U64}
    {G : S → Prop} (hxf : XferOKA st ar T Cs Ω H Sg Rp Scs Nt Z U G) {Ac : Set U64} (s : S) (a : A) (t : obj.Tcb)
    (f : error.Fault)
    (hG : FaultG st H G s t f)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hU : UserOK st T Cs Ω H U s) (hc : CanBlock st T Ac s t)
    (hcap : obj.Tcb.slot t layout.tcb.SLOT_FAULT_HANDLER ⦃ sl =>
      obj.Slot.cap st sl s ⦃ c => CapTyped H Rp Nt c ⦄ ⦄)
    (hRV : RunVcpuInv st T s) :  -- a64: [J] `RunVcpuInv` (`send_ipc.ipc`)
    faults.handle_fault st ar s a t f ⦃ r => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ⦄ := by
  have ht := hc.mem
  unfold faults.handle_fault
  refine WP.spec_bind hcap fun sl hsl => ?_
  refine WP.spec_bind hsl fun c hct => ?_
  step with obj.Tcb.sc.spec as ⟨i, ei⟩
  unfold faults.send_fault_ipc
  refine WP.spec_bind (Pₘ := fun r : Bool × S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ∧
      (r.1 = false → r.2.1 = s)) ?_ ?_
  · split
    all_goals first | exact (WP.spec_ok _).2 ⟨h, fun _ => rfl⟩ | skip
    rename_i p b x y g gr
    have hpH := hct.1 p b x y g gr rfl
    refine WP.spec_bind (spec_eq' (WP.spec_and (WP.spec_and (faults.set_fault.blk s t f h ht hU hc)
      (faults.set_fault.sc s t f h.1.choose_spec.choose_spec.tcbs ht))
      (faults.set_fault.rv s t f h.1.choose_spec.choose_spec.tcbs ht))) ?_
    rintro s1 ⟨eq1, ⟨⟨h1, hU1, hc1⟩, sc1⟩, rv1⟩
    obtain ⟨⟨Q1, R1, q1⟩, hB1, hX1, hS1, hSg1⟩ := h1
    refine WP.spec_bind (endpoint.send_ipc.ipcA hA hxf s1 a true false b g gr (i != 0#u64) t p Q1 R1
      (fun s2 => hG s1 p s2 eq1) q1 hB1 hX1
      hS1 hSg1 hU1 hc1 (fun e => ?_) hpH (hRV.rvSt rv1)) ?_
    · have hi : i ≠ 0#u64 := by simpa using e
      rw [sc1, ← ei]; exact hi
    rintro ⟨s2, a1⟩ h2
    exact (WP.spec_ok _).2 ⟨by simpa using h2, fun e => by cases e⟩
  · rintro ⟨b, s2, a2⟩ ⟨h2, e2⟩
    try simp only [WP.uncurry'_pair] at e2
    simp only [uncurry_apply_pair]
    split
    · exact (WP.spec_ok _).2 h2
    · rename_i hb
      have e2' : s2 = s := e2 (by simpa using hb)
      subst e2'
      obtain ⟨⟨Q3, R3, q3⟩, hB3, hX3, hS3, hSg3⟩ := h2
      refine WP.spec_bind (sts_all s2 t _ Q3 R3 q3 hB3 hX3 hS3 hSg3 ht not_blocked_inactive inactive_ne
        (Or.inr hc.nb) (hX3.noref (q3.tcbs t ht) hc.nrp (fun e => hc.nb (Or.inr (Or.inl e))))
        ⟨fun c hc' p hp hm => absurd hm (q3.notQ ht hc.nq hc' hp), fun c hc' hm => absurd hm (q3.notR ht hc.nr hc'),
          fun e => absurd e hc.na⟩) ?_
      rintro s4 ⟨h4, hB4, hX4, hS4, hSg4, -, -⟩
      exact (WP.spec_ok _).2 ⟨⟨Q3, R3, h4.congrX empty_congr⟩, hB4, hX4, hS4, hSg4⟩


end

/-! ## QueueInvoke twin -/

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {Es : Set U64}

-- a64: `_A` twin (`XferOKA`) of the QueueInvoke lemma below
/-- **Endpoint send** (`Send`/`Call`/`NBSend` on an endpoint cap): restart,
`send_ipc`.  The caller can block (`CanBlock`, as at a receive), and the user
words are outside the kernel objects. -/
theorem ep_send.blkA {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {U : Set U64}
    {G : S → Prop} (hxf : XferOKA st ar T Cs Ω H Sg Rp Scs Nt Z U G) (s : S) (a : A) (blk call : Bool) (badge : U64)
    (grant grant_reply don : Bool) (ct e : U64)
    (hG : ∀ s1 s2, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 → H e = some .ep →
      (L.epState s1 e = 1#u64 ∨ L.epState s1 e = 2#u64) → endpoint.ep_dequeue st s1 e (L.epQ s1 e).head = ok s2 → G s2)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hU : UserOK st T Cs Ω H U s)
    (hc : CanBlock st T Ac s ct) (hdon : don = true → L.mem s (scA ct) ≠ 0#u64) (hH : H e = some .ep)
    (hRV : RunVcpuInv st T s) (hrvc : L.mem s (runVcpuA ct) = 0#u64) :  -- a64: [J] `RunVcpuInv`; caller-level `hrvc`
    (do
      let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
      let (s2, a1) ← endpoint.send_ipc st ar s1 a blk call badge grant grant_reply don ct e
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1)) ⦃ r s' _ =>
      r = .Ok () ∧ BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  have hT := h.1.choose_spec.choose_spec.tcbs
  refine WP.spec_bind (spec_eq' (sched.set_thread_state.restart_blk (Es := ∅) s ct h hc.mem hc.nb hc.nrp)) ?_
  rintro s1 ⟨eq1, ⟨⟨Q1, R1, h1⟩, hB1, hX1, hS1, hSg1⟩, -, e1, k1⟩
  refine WP.spec_bind (endpoint.send_ipc.ipcA hA hxf s1 a blk call badge grant grant_reply don ct e Q1 R1
    (fun s2 => hG s1 s2 eq1) h1 hB1 hX1
    hS1 hSg1 (hU.ksb k1.ksb) (hc.restart hT k1 e1) (fun hd => by rw [k1.scf hc.mem]; exact hdon hd) hH
    (hRV.restart k1 hrvc)) ?_
  rintro ⟨s2, a1⟩ h2
  try simp only [WP.uncurry'_pair] at h2 ⊢
  exact (WP.spec_ok _).2 ⟨by first | trivial | rfl, h2⟩


end

end Fl4ProofsA64.P1
