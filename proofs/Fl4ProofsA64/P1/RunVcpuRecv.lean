/-
P1 (AArch64 only): `RunVcpuInv` across `receive_ipc`'s prefix, so that `receive_ipc` takes the invariant at its
entry state.

* `RunVcpuInv.keep'`: `RunVcpuInv` moves along a step that keeps every `RUN_VCPU` word and changes the `STATE`
  word only of threads with `RUN_VCPU` 0.
* `endpoint.take_reply.rvi`: `take_reply` keeps `RunVcpuInv`. Its `cancel_ipc` is of the reply's thread, which
  is blocked on the reply (or on a receive), so it runs no VCPU; `cancel_ipc` keeps every `RUN_VCPU` word.
* `notification.maybe_return_sched_context.rv` / `.rvi`: it keeps every `RUN_VCPU` word (an SC and a TCB `SC`
  word, then possibly `reschedule_required`, `sched.reschedule_required.fldX`) and every `STATE` word, so it
  keeps `RunVcpuInv`.
* `RecvPre.rvi`: `RunVcpuInv` at the entry gives it at every `RecvPre` state.
* `endpoint.receive_ipc.ipc_rv`: `endpoint.receive_ipc.ipc` (QueueIpc) with its premise `hRV` at the entry
  state, plain `RunVcpuInv st T s`. `receive_ipc.ipc` keeps its statement.

Named premise: **[J] `RunVcpuInv`** (`hRV`, see `RunVcpu`); its preservation by every kernel entry is an
obligation for when A64 P1 has an `EntryInv`. No other premises.
-/
import Fl4ProofsA64.P1.QueueIpc
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- `RunVcpuInv` moves along a step that keeps every `RUN_VCPU` word and changes only the `STATE` words of
threads running no VCPU. -/
theorem RunVcpuInv.keep' {s s' : S} (hRV : RunVcpuInv st T s)
    (hrv : ∀ y ∈ T, L.mem s' (runVcpuA y) = L.mem s (runVcpuA y))
    (hst : ∀ y ∈ T, L.mem s' (stA y) = L.mem s (stA y) ∨ L.mem s (runVcpuA y) = 0#u64) :
    RunVcpuInv st T s' := fun y hy h0 => by
  have h0' : L.mem s (runVcpuA y) ≠ 0#u64 := by rw [← hrv y hy]; exact h0
  rcases hst y hy with e | e
  · rw [e]; exact hRV y hy h0'
  · exact absurd e h0'

/-- `take_reply` keeps [J] `RunVcpuInv`. -/
theorem endpoint.take_reply.rvi {A : Type _} (ar : machine.Arch A) (s : S) (a : A) (t : U64)
    (cap : capability.Cap) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hSg : SgOK st Ω Sg s) (hcap : ∀ p g, cap = .Reply p g → p ∈ Rp) (hRV : RunVcpuInv st T s) :
    endpoint.take_reply st ar s a t cap ⦃ _ s' _ => RunVcpuInv st T s' ⦄ := by
  unfold endpoint.take_reply
  split
  case h_5 p g =>
    have hp := hcap p g rfl
    step with obj.Reply.tcb.blk as ⟨i, ei⟩
    step with obj.Tcb.is_null.spec as ⟨b, eb⟩
    split
    · exact (WP.spec_ok _).2 hRV
    rename_i hb
    have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    step with tcb_ne.blk as ⟨b1, eb1⟩
    split
    · obtain ⟨-, hiT, -, hist⟩ := hX.2.1.back p hp (by rw [← ei]; exact hi0)
      rw [← ei] at hiT hist
      have hiv : L.mem s (runVcpuA i) = 0#u64 := hRV.zero hiT (by
        rcases hist with e | e
        · exact fun hv => runnable_ne_reply (Or.inr (Or.inr hv)) e
        · exact blocked_ne_vm (Or.inr (Or.inl e)))
      refine WP.spec_bind (ipc.cancel_ipc.all s a i Q R h hiT hB hX hSg.sub) ?_
      rintro ⟨s1, a1⟩ ⟨-, -, -, -, -, -, k1, -⟩
      try simp only [WP.uncurry'_pair]
      refine (WP.spec_ok _).2 (hRV.keep' (fun y hy => k1.fld y hy 3672#u64 (by simp) (by simp) (by simp) (by simp)
        (fun _ => ⟨by simp, by simp⟩)) fun y hy => ?_)
      by_cases hyi : y = i
      · subst hyi; exact Or.inr hiv
      · exact Or.inl (k1.stf hy hyi)
    · exact (WP.spec_ok _).2 hRV
  all_goals exact (WP.spec_ok _).2 hRV

/-- `maybe_return_sched_context` keeps every `RUN_VCPU` word: it writes the thread's `SC` word and the SC's
`TCB` word, then maybe `reschedule_required` (`sched.reschedule_required.fldX`). -/
theorem notification.maybe_return_sched_context.rv (s : S) (n t : U64)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T)
    (hout : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64 ∧
      L.actionW s ≠ t)
    (hidle : L.idleW s ≠ t) :
    notification.maybe_return_sched_context st s n t ⦃ s' =>
      ∀ y ∈ T, L.mem s' (runVcpuA y) = L.mem s (runVcpuA y) ⦄ := by
  have hta := h.tcbs t ht
  unfold notification.maybe_return_sched_context
  step with obj.Ntfn.sc.any as ⟨i, _⟩
  step with obj.Sc.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 fun _ _ => rfl
  rename_i hb
  have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
  step with obj.Tcb.sc.spec as ⟨i1, ei1⟩
  split
  · rename_i hii
    have hsc : L.mem s (scA t) = i := by rw [← ei1, hii]
    step with obj.Tcb.set_sc.wr as ⟨s1, e1⟩
    step with obj.Sc.set_tcb.wr as ⟨s2, e2⟩
    have key := unbind_state h hB hX hS hSg ht hout hidle hsc hi0
    rw [← e1, ← e2] at key
    obtain ⟨k1, kB, -, -, -, k5, -⟩ := key
    obtain ⟨hiS, -, -⟩ := hX.2.2.bound t ht (by rw [hsc]; exact hi0)
    rw [hsc] at hiS
    have hm := h.omega _ (hSg.sub _ (hX.1.fixW i hiS).1)
    have rv2 : ∀ y ∈ T, L.mem s2 (runVcpuA y) = L.mem s (runVcpuA y) := fun y hy => by
      have hya := h.tcbs y hy
      rw [e2, e1, show runVcpuA y = core.num.U64.wrapping_add y 3672#u64 from rfl,
        L.mem_wr_ne hm.1 (field_aligned (K := 3672#u64) hya (by simp) (by simp))
          (fun e => out_ne_field (K := 3672#u64) hm hy hya (by simp) e.symm),
        L.mem_wr_ne (scA_aligned hta) (field_aligned (K := 3672#u64) hya (by simp) (by simp))
          (fun e => field_ne (K1 := 3464#u64) (K2 := 3672#u64) hta hya (by simp) (by simp) (fun _ => by simp)
            (by rw [← scA_eq]; exact UScalar.eq_of_val_eq e))]
    step with sched.cur_thread.spec as ⟨t1, et1⟩
    step with tcb_eq.blk as ⟨b1, eb1⟩
    split
    · by_cases ha0 : L.actionW s2 = 0#u64
      · refine WP.spec_mono (sched.reschedule_required.resume s2 ha0) fun s3 e3 => ?_
        subst e3
        intro y hy
        rw [show runVcpuA y = core.num.U64.wrapping_add y 3672#u64 from rfl,
          field_wr_node k1 k1.cur (by rw [act_val]; omega) (by rw [act_val]) hy (by simp) (by simp)]
        exact rv2 y hy
      · have kB2 := kB (fun _ => ha0)
        exact WP.spec_mono (sched.reschedule_required.fldX (K := 3672#u64) s2 Q R k1 kB2 k5 (by simp) (by simp)
          (by simp) (by simp)) fun s3 hh y hy => (hh y hy).trans (rv2 y hy)
    · exact (WP.spec_ok _).2 rv2
  · exact (WP.spec_ok _).2 fun _ _ => rfl

/-- `maybe_return_sched_context` keeps [J] `RunVcpuInv`: it keeps every `STATE` and `RUN_VCPU` word. -/
theorem notification.maybe_return_sched_context.rvi (s : S) (n t : U64)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T)
    (hout : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64 ∧
      L.actionW s ≠ t)
    (hidle : L.idleW s ≠ t) (hRV : RunVcpuInv st T s) :
    notification.maybe_return_sched_context st s n t ⦃ s' => RunVcpuInv st T s' ⦄ :=
  WP.spec_mono (WP.spec_and (notification.maybe_return_sched_context.inv s n t Q R h hB hX hS hSg ht hout hidle)
    (notification.maybe_return_sched_context.rv s n t Q R h hB hX hS hSg ht hout hidle)) fun _ hh =>
    hRV.keep hh.1.2.2.2.2.2.2.2.2.2.2.1 hh.2

/-- [J] `RunVcpuInv` at `receive_ipc`'s entry holds at every `RecvPre` state. -/
theorem RecvPre.rvi {A : Type _} {ar : machine.Arch A} {s : S} {a : A} {t : U64} {reply_cap : capability.Cap}
    {s2 : S} (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hc : CanBlock st T Ac s t)
    (hcap : ∀ p g, reply_cap = .Reply p g → p ∈ Rp) (hRV : RunVcpuInv st T s)
    (hp : RecvPre st ar s a t reply_cap s2) : RunVcpuInv st T s2 := by
  obtain ⟨r, s1, a1, e1, h2⟩ := hp
  have k := endpoint.take_reply.rvi ar s a t reply_cap Q R h hB hX hSg hcap hRV
  have I := endpoint.take_reply.inv ar s a t reply_cap Q R h hB hX hS hSg hc hcap
  rw [e1, WP.spec_ok] at k I
  try simp only [WP.uncurry'_pair] at k I
  obtain ⟨h1, hB1, hX1, hS1, hSg1, hc1, -⟩ := I
  rcases h2 with e2 | ⟨i, e2⟩
  · rw [e2]; exact k
  · have M := notification.maybe_return_sched_context.rvi s1 i t Q R h1 hB1 hX1 hS1 hSg1 hc1.mem
      ⟨hc1.nq, hc1.nr, hc1.na⟩ hc1.ni k
    rw [e2, WP.spec_ok] at M
    exact M

/-- seL4 `receiveIPC` (`endpoint.receive_ipc.ipc`) with named premise **[J] `hRV`** at the entry state: plain
`RunVcpuInv st T s` (`RecvPre.rvi` carries it to the states `receive_ipc.ipc` asks it at), and the caller-level
`hvm` (the receiver is not in `TS_RUNNING_VM`). -/
theorem endpoint.receive_ipc.ipc_rv {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {U : Set U64}
    {G : S → Prop} (hxf : XferOK st ar T Cs Ω H Sg Rp Scs Nt Z U G) (s : S) (a : A) (t : U64)
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
  endpoint.receive_ipc.ipc hA hxf s a t cap blocking reply_cap e Q R hG h hB hX hS hSg hU hc hptr hH hcap hNt
    (fun _ hp => RecvPre.rvi Q R h hB hX hS hSg hc hcap hRV hp) hvm

end

end Fl4ProofsA64.P1
