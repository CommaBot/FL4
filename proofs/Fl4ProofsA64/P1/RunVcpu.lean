/-
P1 (AArch64 only): the `RUN_VCPU` invariant `RunVcpuInv`.

A thread's `RUN_VCPU` word (`runVcpuA`, TCB + 3672) names the VCPU of the `ARMVCPURun` it has in flight, or
is 0. `RunVcpuInv` says that a thread with a nonzero `RUN_VCPU` is in `TS_RUNNING_VM`. So a thread in any
other state, in particular a blocked one, runs no VCPU, and AArch64's VCPU steps on it write nothing:
`vcpu::cancel_run` in `suspend` and the `RUN_VCPU` branch of `smp::migrate_tcb`.

Named premise:
* **[J] `RunVcpuInv`** (`hRV`): the invariant at the state a lemma starts from. Its preservation by every kernel
  entry is an obligation for when A64 P1 has an `EntryInv`; nothing here proves it.

The theorems below derive the facts the AArch64 proofs need from it:
* `RunVcpuInv.zero` / `.blocked`: a thread not in `TS_RUNNING_VM` (a blocked one) has `RUN_VCPU` 0;
* `sched.suspend.inv_rv` / `sched.suspend.all_rv`: `sched.suspend.inv` / `.all` with their gen-2 [J] `hrv`
  (the suspended thread runs no VCPU) derived from [J] `RunVcpuInv` and the precondition `hvm` that the
  thread is not in `TS_RUNNING_VM`. The original theorems keep their statements;
* `endpoint.take_reply.stt`, `RecvPre.stt`: `receive_ipc`'s prefix keeps the receiver's `STATE` word.
-/
import Fl4ProofsA64.P1.QueueSuspend
import Fl4ProofsA64.P1.QueueBlock
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- **[J]** (AArch64) A thread whose `RUN_VCPU` word is nonzero (an `ARMVCPURun` in flight) is in
`TS_RUNNING_VM`. Its preservation by every kernel entry is an obligation for when A64 P1 has an `EntryInv`. -/
def RunVcpuInv (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s : S) : Prop :=
  ∀ t ∈ T, L.mem s (runVcpuA t) ≠ 0#u64 → L.mem s (stA t) = sched.TS_RUNNING_VM

/-- Under [J] `RunVcpuInv`, a thread not in `TS_RUNNING_VM` runs no VCPU. -/
theorem RunVcpuInv.zero {s : S} {t : U64} (hRV : RunVcpuInv st T s) (ht : t ∈ T)
    (hv : L.mem s (stA t) ≠ sched.TS_RUNNING_VM) : L.mem s (runVcpuA t) = 0#u64 :=
  Classical.byContradiction fun h0 => hv (hRV t ht h0)

theorem blocked_ne_vm {v : U64} (h : Blocked v) : v ≠ sched.TS_RUNNING_VM :=
  fun e => not_runnable_of_blocked h (Or.inr (Or.inr e))

/-- Under [J] `RunVcpuInv`, a thread blocked on an endpoint or notification runs no VCPU. -/
theorem RunVcpuInv.blocked {s : S} {t : U64} (hRV : RunVcpuInv st T s) (ht : t ∈ T)
    (hb : Blocked (L.mem s (stA t))) : L.mem s (runVcpuA t) = 0#u64 :=
  hRV.zero ht (blocked_ne_vm hb)

/-- `RunVcpuInv` moves along a step that keeps every thread's `STATE` and `RUN_VCPU` words. -/
theorem RunVcpuInv.keep {s s' : S} (hRV : RunVcpuInv st T s) (hst : ∀ y ∈ T, L.mem s' (stA y) = L.mem s (stA y))
    (hrv : ∀ y ∈ T, L.mem s' (runVcpuA y) = L.mem s (runVcpuA y)) : RunVcpuInv st T s' := fun y hy h0 => by
  rw [hst y hy]; exact hRV y hy (by rw [← hrv y hy]; exact h0)

/-- `sched.suspend.inv` with its [J] `hrv` derived: from [J] `RunVcpuInv` and `hvm` (`t` is not in
`TS_RUNNING_VM`), `t` runs no VCPU. -/
theorem sched.suspend.inv_rv {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (t : obj.Tcb)
    (hRV : RunVcpuInv st T s) (hvm : L.mem s (stA t) ≠ sched.TS_RUNNING_VM)
    (Q : U64 → U64 → List U64) (R : U64 → List U64) (h : SchedQueuesInv st T Cs Ω H s Q R) (ht : t ∈ T)
    (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (hrecv : L.mem s (stA t) = sched.TS_BLOCKED_ON_RECV → L.mem s (replyA t) ≠ 0#u64 →
      L.mem s (replyA t) ∈ Rp ∧ L.mem s (rTcbA (L.mem s (replyA t))) = t)
    (hreply : L.mem s (stA t) = sched.TS_BLOCKED_ON_REPLY → ReplyT st Rp Scs s t)
    (hna : L.actionW s ≠ t)
    (hyield : L.mem s (yieldA t) ≠ 0#u64 → scYieldFromA (L.mem s (yieldA t)) ∈ Ω)
    (hhd : RHead st Rp s) (hnx : ∀ r ∈ Rp, L.mem s (rNextA r) &&& ~~~1#u64 ≠ 0#u64 →
      headBit (L.mem s (rNextA r)) = true → L.mem s (rNextA r) &&& ~~~1#u64 ∈ Scs) :
    sched.suspend st ar s a t ⦃ s' _ => ∃ Q' R', SchedQueuesInv st T Cs Ω H s' Q' R' ⦄ :=
  sched.suspend.inv s a t (hRV.zero ht hvm) Q R h ht hO hsub hrecv hreply hna hyield hhd hnx

/-- `sched.suspend.all` with its [J] `hrv` derived: from [J] `RunVcpuInv` and `hvm` (`t` is not in
`TS_RUNNING_VM`), `t` runs no VCPU. -/
theorem sched.suspend.all_rv {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (t : obj.Tcb)
    (hRV : RunVcpuInv st T s) (hvm : L.mem s (stA t) ≠ sched.TS_RUNNING_VM)
    (Q : U64 → U64 → List U64) (R : U64 → List U64) (h : SchedQueuesInv st T Cs Ω H s Q R) (ht : t ∈ T)
    (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hSg : SgOK st Ω Sg s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hna : L.actionW s ≠ t)
    (hyield : L.mem s (yieldA t) ≠ 0#u64 → L.mem s (yieldA t) ∈ Scs) :
    sched.suspend st ar s a t ⦃ s' _ => ∃ Q' R', SchedQueuesInv st T Cs Ω H s' Q' R' ∧ BoundInv st T Ac s' ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧ SCsOK st T Ω Sg Scs Z Ac s' ∧ TmFr st T Cs Nt s s' ⦄ :=
  sched.suspend.all s a t (hRV.zero ht hvm) Q R h ht hB hX hSg hS hna hyield

/-- `take_reply` keeps the receiver's `STATE` word: the `cancel_ipc` it may make is of another thread. -/
theorem endpoint.take_reply.stt {A : Type _} (ar : machine.Arch A) (s : S) (a : A) (t : U64)
    (cap : capability.Cap) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hSg : SgOK st Ω Sg s) (hc : CanBlock st T Ac s t)
    (hcap : ∀ p g, cap = .Reply p g → p ∈ Rp) :
    endpoint.take_reply st ar s a t cap ⦃ _ s' _ => L.mem s' (stA t) = L.mem s (stA t) ⦄ := by
  unfold endpoint.take_reply
  split
  case h_5 p g =>
    have hp := hcap p g rfl
    step with obj.Reply.tcb.blk as ⟨i, ei⟩
    step with obj.Tcb.is_null.spec as ⟨b, eb⟩
    split
    · exact (WP.spec_ok _).2 rfl
    rename_i hb
    have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    step with tcb_ne.blk as ⟨b1, eb1⟩
    split
    · rename_i hb1
      have hit : i ≠ t := fun e => (eb1.1 hb1) e
      obtain ⟨-, hiT, -, -⟩ := hX.2.1.back p hp (by rw [← ei]; exact hi0)
      rw [← ei] at hiT
      refine WP.spec_bind (ipc.cancel_ipc.all s a i Q R h hiT hB hX hSg.sub) ?_
      rintro ⟨s1, a1⟩ ⟨-, -, -, -, -, -, k1, -⟩
      try simp only [WP.uncurry'_pair]
      exact (WP.spec_ok _).2 (k1.stf hc.mem (Ne.symm hit))
    · exact (WP.spec_ok _).2 rfl
  all_goals exact (WP.spec_ok _).2 rfl

/-- The states `receive_ipc` reaches before its end on the endpoint (`RecvPre`: after `take_reply` and
`maybe_return_sched_context`) have the receiver's `STATE` word of the entry state. -/
theorem RecvPre.stt {A : Type _} {ar : machine.Arch A} {s : S} {a : A} {t : U64} {reply_cap : capability.Cap}
    {s2 : S} (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hc : CanBlock st T Ac s t)
    (hcap : ∀ p g, reply_cap = .Reply p g → p ∈ Rp) (hp : RecvPre st ar s a t reply_cap s2) :
    L.mem s2 (stA t) = L.mem s (stA t) := by
  obtain ⟨r, s1, a1, e1, h2⟩ := hp
  have k := endpoint.take_reply.stt ar s a t reply_cap Q R h hB hX hSg hc hcap
  have I := endpoint.take_reply.inv ar s a t reply_cap Q R h hB hX hS hSg hc hcap
  rw [e1, WP.spec_ok] at k I
  try simp only [WP.uncurry'_pair] at k I
  obtain ⟨h1, hB1, hX1, hS1, hSg1, hc1, -⟩ := I
  rcases h2 with e2 | ⟨i, e2⟩
  · rw [e2]; exact k
  · have M := notification.maybe_return_sched_context.inv s1 i t Q R h1 hB1 hX1 hS1 hSg1 hc1.mem
      ⟨hc1.nq, hc1.nr, hc1.na⟩ hc1.ni
    rw [e2, WP.spec_ok] at M
    exact M.2.2.2.2.2.2.1.trans k

end

end Fl4ProofsA64.P1
