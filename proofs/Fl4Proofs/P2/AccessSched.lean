/-
# P2: guarded-store lemmas for the scheduler and SC callees of the local paths

Built on `P2/AccessLeaf.lean` (one-word accessors), for the per-path
obligation of `P2/PathObl.lean`: each callee `f` gets `f.guard`, the run on
`guard st R W` is the run on `st`, given that the words it may read are in `R`
and the words it may write are in `W`. Membership hypotheses are stated at the
callee's entry state, with P1's address abbreviations (`ctA`, `regA`, `rtA`,
`headA`, …); a hypothesis may cover a word a given run does not touch (the
caller's `ReadSet` must then hold it too). Shared by every local-path line.

* `bind_guard_congr`: composing along a bind (the continuation only at the
  values the real run produces); `loop_guard_congr`: along a loop (an
  invariant of the real loop states and a decreasing measure);
* registers: `obj.Tcb.reg.guard`, `obj.Tcb.set_reg.guard`;
* timestamps: `sched.update_timestamp.guard` (one domain: the node's
  `CUR_TIME` and `CONSUMED`);
* refills: `obj.Sc.r_time.guard`, `r_amount`, `sporadic.get`, `head`,
  `capacity`, `sufficient` (`RdHead`: the SC's head index and head refill);
* checks: `sched.in_release_queue.guard`, `sched.queued.guard`,
  `sched.is_cur_domain_expired.guard` (one domain: no access),
  `fastpath.schedulable_here.guard`, `sched.highest_prio.guard`,
  `sched.is_highest_prio.guard` (the node's bitmap words),
  `sporadic.cur_time.guard`, `sporadic.ready.guard`;
* `switch_to` helpers: `sched.set_cur_thread.guard`, `sched.set_reprogram.guard`,
  `sporadic.sc_constant_bandwidth.guard`, `sporadic.is_round_robin.guard`,
  `smp.send_pending.guard`, `vspace.kernel_root.guard`,
  `vspace.set_kernel_vm_root.guard`.

No premises.
-/
import Fl4Proofs.P2.AccessLeaf
import Fl4Proofs.P1.FastVmDecline
import Fl4Proofs.P1.FastRRFoot
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts

section
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop}

/-- Composing along a bind: equal first steps, and equal continuations at the
values the (real) first step produces. -/
theorem bind_guard_congr {α β : Type} {m m' : Result α} {k k' : α → Result β} (h : m' = m)
    (hk : ∀ x, m = ok x → k' x = k x) : Std.bind m' k' = Std.bind m k := by
  rw [h]
  cases m with
  | ret x => rw [bind_ok, bind_ok]; exact hk x rfl
  | vis i k0 =>
    rw [bind_vis, bind_vis]; congr 1; funext y; cases i; exact PEmpty.elim y
  | div => rw [bind_div, bind_div]

/-- Composing along a loop: an invariant `I` of the (real) loop states, under
which the guarded body equals the real one, kept by the real body's `cont`
steps with a decreasing measure. -/
theorem loop_guard_congr {α β : Type} {body body' : α → Result (ControlFlow α β)} (I : α → Prop)
    (μ : α → Nat) (hstep : ∀ x, I x → body' x = body x ∧
      ∀ y, body x = ok (ControlFlow.cont y) → I y ∧ μ y < μ x) :
    ∀ x, I x → loop body' x = loop body x := by
  suffices H : ∀ n x, μ x = n → I x → loop body' x = loop body x from fun x hx => H _ x rfl hx
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hn hx
    obtain ⟨he, hc⟩ := hstep x hx
    unfold loop
    rw [he]
    refine bind_guard_congr rfl fun r hr => ?_
    cases r with
    | cont y =>
      obtain ⟨hy, hlt⟩ := hc y hr
      exact ih (μ y) (hn ▸ hlt) y rfl hy
    | done z => rfl

/-! ## Registers -/

theorem obj.Tcb.reg.guard (t : obj.Tcb) (s : S) (r : U64) (h : R (regA t r)) :
    obj.Tcb.reg (guard st R W) t s r = obj.Tcb.reg st t s r := by
  unfold obj.Tcb.reg
  simp only [lift, bind_ok]
  exact guard_read_of h rfl

theorem obj.Tcb.set_reg.guard (t : obj.Tcb) (s : S) (r v : U64) (h : W (regA t r)) :
    obj.Tcb.set_reg (guard st R W) t s r v = obj.Tcb.set_reg st t s r v := by
  unfold obj.Tcb.set_reg
  simp only [lift, bind_ok]
  exact guard_write_of h rfl

/-! ## Refills -/

theorem obj.Sc.r_time.guard (sc : obj.Sc) (s : S) (i : U64) (h : R (rtA sc i)) :
    obj.Sc.r_time (guard st R W) sc s i = obj.Sc.r_time st sc s i := by
  unfold obj.Sc.r_time
  rw [eq_ok_of_spec (obj.Sc.refill_addr.spec sc i)]
  simp only [bind_ok]
  exact guard_read h

theorem obj.Sc.r_amount.guard (sc : obj.Sc) (s : S) (i : U64) (h : R (raA sc i)) :
    obj.Sc.r_amount (guard st R W) sc s i = obj.Sc.r_amount st sc s i := by
  unfold obj.Sc.r_amount
  rw [eq_ok_of_spec (obj.Sc.refill_addr.spec sc i)]
  simp only [lift, bind_ok]
  exact guard_read_of h rfl

theorem sporadic.get.guard (s : S) (sc : obj.Sc) (i : U64) (ht : R (rtA sc i)) (ha : R (raA sc i)) :
    sporadic.get (guard st R W) s sc i = sporadic.get st s sc i := by
  unfold sporadic.get
  rw [obj.Sc.r_time.guard sc s i ht, obj.Sc.r_amount.guard sc s i ha]

section law
variable [L : LawfulStore st]

/-- The words `sporadic.head` reads: the SC's head index and its head refill. -/
def RdHead (R : U64 → Prop) (s : S) (sc : obj.Sc) : Prop :=
  R (headA sc) ∧ R (rtA sc (L.rhead s sc)) ∧ R (raA sc (L.rhead s sc))

theorem sporadic.head.guard (s : S) (sc : obj.Sc) (h : RdHead (L := L) R s sc) :
    sporadic.head (guard st R W) s sc = sporadic.head st s sc := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold sporadic.head
  rw [obj.Sc.refill_head.guard sc s h1, eq_ok_of_spec (obj.Sc.refill_head.spec (L := L) s sc)]
  simp only [bind_ok]
  exact sporadic.get.guard s sc _ h2 h3

theorem sporadic.capacity.guard (s : S) (sc : obj.Sc) (u : U64) (h : RdHead (L := L) R s sc) :
    sporadic.capacity (guard st R W) s sc u = sporadic.capacity st s sc u := by
  unfold sporadic.capacity
  rw [sporadic.head.guard s sc h]

theorem sporadic.sufficient.guard {A : Type} (ar : machine.Arch A) (s : S) (a : A) (sc : obj.Sc) (u : U64)
    (h : RdHead (L := L) R s sc) :
    sporadic.sufficient (guard st R W) ar s a sc u = sporadic.sufficient st ar s a sc u := by
  unfold sporadic.sufficient
  rw [sporadic.capacity.guard s sc u h]

/-! ## Timestamps -/

/-- **`update_timestamp`** (one domain) reads and writes the node's `CUR_TIME`
and `CONSUMED`. -/
theorem sched.update_timestamp.guard {A : Type} (ar : machine.Arch A) (s : S) (a : A)
    (hr1 : R (ctA (L := L) s)) (hw1 : W (ctA (L := L) s)) (hr2 : R (cnA (L := L) s))
    (hw2 : W (cnA (L := L) s)) :
    sched.update_timestamp (guard st R W) ar s a = sched.update_timestamp st ar s a := by
  unfold sched.update_timestamp
  rw [sched.cur_time.guard s hr1]
  refine bind_guard_congr rfl fun prev _ => ?_
  refine bind_guard_congr rfl fun na _ => ?_
  obtain ⟨n, a1⟩ := na
  try simp only [Aeneas.Std.uncurry_apply_pair]
  simp only [guard_cur_cpu, L.cur_cpu_eq, bind_ok]
  rw [obj.node_set.guard s _ _ _ hw1, eq_ok_of_spec (obj.node_set.spec (L := L) s _ _ _)]
  simp only [bind_ok, lift]
  have e : ∀ v, L.nodeAt (L.wr s (L.nodeAt s (L.cpu s) layout.node.CUR_TIME) v)
      (L.cpu (L.wr s (L.nodeAt s (L.cpu s) layout.node.CUR_TIME) v)) layout.node.CONSUMED = cnA (L := L) s := by
    intro v; rw [LawfulStore.cpu_wr, nodeAt_of_ksb (L.ksb_wr _ _ _)]
  rw [sched.consumed.guard _ (by rw [e]; exact hr2)]
  refine bind_guard_congr rfl fun c _ => ?_
  rw [sched.set_consumed.guard _ _ (by rw [e]; exact hw2)]
  simp only [if_neg num_domains_one]

/-! ## Checks -/

theorem sched.in_release_queue.guard (s : S) (t : obj.Tcb) (h : R (inqA t)) :
    sched.in_release_queue (guard st R W) s t = sched.in_release_queue st s t := by
  unfold sched.in_release_queue
  rw [obj.Tcb.in_queues.guard t s h]

theorem sched.queued.guard (s : S) (t : obj.Tcb) (h : R (inqA t)) :
    sched.queued (guard st R W) s t = sched.queued st s t := by
  unfold sched.queued
  rw [obj.Tcb.in_queues.guard t s h]

theorem sched.is_cur_domain_expired.guard (s : S) :
    sched.is_cur_domain_expired (guard st R W) s = sched.is_cur_domain_expired st s := by
  unfold sched.is_cur_domain_expired
  rw [if_neg num_domains_one, if_neg num_domains_one]

theorem sporadic.cur_time.guard (s : S) (h : R (ctA (L := L) s)) :
    sporadic.cur_time (guard st R W) s = sporadic.cur_time st s := by
  unfold sporadic.cur_time
  simp only [guard_cur_cpu, L.cur_cpu_eq, bind_ok]
  exact obj.node_get.guard s _ _ h

theorem sporadic.ready.guard (s : S) (sc : obj.Sc) (h : RdHead (L := L) R s sc) (hct : R (ctA (L := L) s)) :
    sporadic.ready (guard st R W) s sc = sporadic.ready st s sc := by
  unfold sporadic.ready
  rw [sporadic.head.guard s sc h, sporadic.cur_time.guard s hct]

/-- The node's `TIMER_MIN` word. -/
abbrev tmA (s : S) : U64 := L.nodeAt s (L.cpu s) layout.node.TIMER_MIN
/-- The node's `RELEASE_HEAD` word. -/
abbrev rhA (s : S) : U64 := L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD

/-- **`schedulable_here to`** reads the node's `CUR_TIME`, `TIMER_MIN` and
`RELEASE_HEAD`, the timer-min thread's deadline, the release head's SC and its
head refill, the kernel's `DOMAIN_TIME` and `CUR_DOMAIN`, and `to`'s
affinity, domain, SC and queue flags. -/
theorem fastpath.schedulable_here.guard (s : S) (t : obj.Tcb)
    (hct : R (ctA (L := L) s)) (htm : R (tmA (L := L) s)) (hrh : R (rhA (L := L) s))
    (htd : L.mem s (tmA (L := L) s) ≠ 0#u64 →
      R (core.num.U64.wrapping_add (L.mem s (tmA (L := L) s)) 3528#u64))
    (hrs : L.mem s (rhA (L := L) s) ≠ 0#u64 → R (scA (L.mem s (rhA (L := L) s))) ∧
      RdHead (L := L) R s (L.mem s (scA (L.mem s (rhA (L := L) s)))))
    (hdt : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME))
    (hcd : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (haf : R (affA t)) (hdo : R (core.num.U64.wrapping_add t 3432#u64)) (hsc : R (scA t))
    (hiq : R (inqA t)) :
    fastpath.schedulable_here (guard st R W) s t = fastpath.schedulable_here st s t := by
  unfold fastpath.schedulable_here
  simp only [guard_cur_cpu, L.cur_cpu_eq, bind_ok]
  rw [sched.cur_time.guard s hct, obj.node_get.guard s _ _ htm, obj.node_get.guard s _ _ hrh,
    sched.is_cur_domain_expired.guard s, sched.domain_time.guard s hdt, obj.Tcb.affinity.guard t s haf,
    obj.Tcb.domain.guard t s hdo, sched.cur_domain.guard s hcd, obj.Tcb.sc.guard t s hsc,
    sched.in_release_queue.guard s t hiq, sched.queued.guard s t hiq]
  rw [node_get_ok s _ layout.node.TIMER_MIN, node_get_ok s _ layout.node.RELEASE_HEAD]
  simp only [bind_ok, is_null_ok]
  by_cases h0 : L.mem s (tmA (L := L) s) = 0#u64
  · simp only [h0, decide_true, ↓reduceIte]
    by_cases h1 : L.mem s (rhA (L := L) s) = 0#u64
    · simp only [h1, decide_true, ↓reduceIte]
    · obtain ⟨hs1, hs2⟩ := hrs h1
      rw [obj.Tcb.sc.guard _ s hs1, tcb_sc_ok s (L.mem s (rhA (L := L) s))]
      simp only [bind_ok]
      rw [sporadic.ready.guard s _ hs2 hct]
  · rw [obj.Tcb.timer_deadline.guard _ s (htd h0)]
    by_cases h1 : L.mem s (rhA (L := L) s) = 0#u64
    · simp only [h1, decide_true, ↓reduceIte]
    · obtain ⟨hs1, hs2⟩ := hrs h1
      rw [obj.Tcb.sc.guard _ s hs1, tcb_sc_ok s (L.mem s (rhA (L := L) s))]
      simp only [bind_ok]
      rw [sporadic.ready.guard s _ hs2 hct]

/-- The node's scheduler bitmap words (one domain): `L1` and the four `L2` words. -/
def RdBitmap (R : U64 → Prop) (s : S) : Prop :=
  R (L.nodeAt s (L.cpu s) l1Off) ∧ ∀ inv : U64, inv.val < 4 → R (L.nodeAt s (L.cpu s) (w64 (136 + 8 * inv.val)))

theorem sched.highest_prio.guard (s : S) (dom : U64) (h : RdBitmap (L := L) R s) :
    sched.highest_prio (guard st R W) s dom = sched.highest_prio st s dom := by
  obtain ⟨h1, h2⟩ := h
  unfold sched.highest_prio
  simp only [guard_cur_cpu, L.cur_cpu_eq, bind_ok, bitmap_dom_one]
  rw [eq_ok_of_spec l1_off_zero]
  simp only [bind_ok]
  rw [obj.node_get.guard s _ _ h1]
  refine bind_guard_congr rfl fun l1 _ => ?_
  refine bind_guard_congr rfl fun l1i _ => ?_
  simp only [lift, bind_ok]
  refine bind_guard_congr rfl fun inv hinv => ?_
  have hlt : inv.val < 4 := by
    have ha : (l1i &&& 3#u64).val ≤ 3 := by
      simp only [UScalar.val_and]; exact Nat.and_le_right
    obtain ⟨z, hz, hv⟩ := spec_ex_fd (U64.sub_spec (x := 3#u64) (y := l1i &&& 3#u64) (by scalar_tac))
    rw [hz] at hinv
    have := ok_inj_ff hinv
    subst this
    have h3 : (3#u64 : U64).val = 3 := by simp
    omega
  rw [eq_ok_of_spec (l2_off_zero inv hlt)]
  simp only [bind_ok]
  rw [obj.node_get.guard s _ _ (h2 inv hlt)]

theorem sched.is_highest_prio.guard (s : S) (dom p : U64) (h : RdBitmap (L := L) R s) :
    sched.is_highest_prio (guard st R W) s dom p = sched.is_highest_prio st s dom p := by
  unfold sched.is_highest_prio
  simp only [guard_cur_cpu, L.cur_cpu_eq, bind_ok, bitmap_dom_one]
  rw [eq_ok_of_spec l1_off_zero]
  simp only [bind_ok]
  rw [obj.node_get.guard s _ _ h.1]
  refine bind_guard_congr rfl fun l1 _ => ?_
  split
  · rfl
  · rw [sched.highest_prio.guard s dom h]

/-! ## Small node and SC helpers of `switch_to` -/

theorem sched.set_cur_thread.guard (s : S) (t : obj.Tcb)
    (h : W (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD)) :
    sched.set_cur_thread (guard st R W) s t = sched.set_cur_thread st s t := by
  unfold sched.set_cur_thread
  simp only [guard_cur_cpu, L.cur_cpu_eq, bind_ok]
  exact obj.node_set.guard s _ _ _ h

theorem sched.set_reprogram.guard (s : S) (h : W (L.nodeAt s (L.cpu s) layout.node.REPROGRAM)) :
    sched.set_reprogram (guard st R W) s = sched.set_reprogram st s := by
  unfold sched.set_reprogram
  simp only [guard_cur_cpu, L.cur_cpu_eq, bind_ok]
  exact obj.node_set.guard s _ _ _ h

theorem sporadic.sc_constant_bandwidth.guard (s : S) (sc : obj.Sc)
    (h : R (core.num.U64.wrapping_add sc layout.sc.SPORADIC)) :
    sporadic.sc_constant_bandwidth (guard st R W) s sc = sporadic.sc_constant_bandwidth st s sc := by
  unfold sporadic.sc_constant_bandwidth
  rw [obj.Sc.sporadic.guard sc s h]

theorem sporadic.is_round_robin.guard (s : S) (sc : obj.Sc)
    (h : R (core.num.U64.wrapping_add sc layout.sc.PERIOD)) :
    sporadic.is_round_robin (guard st R W) s sc = sporadic.is_round_robin st s sc := by
  unfold sporadic.is_round_robin
  rw [obj.Sc.period.guard sc s h]

/-- `send_pending` reads and clears the node's `IPI_PENDING`. -/
theorem smp.send_pending.guard {A : Type} (ar : machine.Arch A) (s : S) (a : A)
    (hr : R (L.nodeAt s (L.cpu s) layout.node.IPI_PENDING))
    (hw : W (L.nodeAt s (L.cpu s) layout.node.IPI_PENDING)) :
    smp.send_pending (guard st R W) ar s a = smp.send_pending st ar s a := by
  unfold smp.send_pending
  simp only [guard_cur_cpu, L.cur_cpu_eq, bind_ok]
  rw [obj.node_get.guard s _ _ hr, obj.node_set.guard s _ _ _ hw]

theorem vspace.kernel_root.guard (s : S)
    (h : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.KERNEL_ROOT)) :
    vspace.kernel_root (guard st R W) s = vspace.kernel_root st s := by
  unfold vspace.kernel_root
  exact obj.ks_get.guard s _ h

theorem vspace.set_kernel_vm_root.guard {A : Type} (ar : machine.Arch A) (s : S) (a : A)
    (h : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.KERNEL_ROOT)) :
    vspace.set_kernel_vm_root (guard st R W) ar s a = vspace.set_kernel_vm_root st ar s a := by
  unfold vspace.set_kernel_vm_root
  rw [vspace.kernel_root.guard s h]

end law

end

end Fl4Proofs.P2.PathObl
