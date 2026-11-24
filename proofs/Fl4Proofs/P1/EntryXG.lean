/-
P1 (a6x): `XG` reaches `finish` on every native kernel-entry path.

`XG` (QueueEntry: a state reached from an entered state writing only `Cur0W`
words) is what P3's placement facts (`XferHyps.buf`, …) are stated at.  Before
this module `XG` reached `syscall.finish` only on the invocation path
(`EntryHyps.postG`).  Here every other path from the entry state to the
`finish` state keeps it:

* `faults.handle_fault.xg` (the fault IPC by `send_ipc.xg`, the no-handler
  case by `set_thread_state.kw`);
* `syscall.handle_recv.xg`: `receive_ipc.xg` (`take_reply`,
  `maybe_return_sched_context`, `wait_for_sender.kw`, `complete_signal.xg`,
  `receive_from_sender.xg`: the transfer keeps `XG` by `XferOK`'s guard, every
  other step is a `KW` / `FootD` step), `receive_signal.xg` (`ntfn_block.kw`,
  the active case), the cap faults (`handle_fault.xg`);
* `syscall.handle_yield.xg` (`charge_budget.allG` with `G := XG`, the SC's
  `CONSUMED` word);
* `syscall.budget_ok.xg`: `XG` after the entry's budget check whether it
  passes or fails (`check_budget.allG`, the restart's `set_thread_state.kw`);
* `interrupt.handle_interrupt.xg`, from `SigXG` (below);
* the composites `syscall.dispatch_syscall.xg`, `…unknown_syscall_fault_old.xgF`,
  `…set_tls_base_self.xgF`, `…handle_unknown_syscall_old.xgF`,
  `syscall.handle_syscall_old.entryXG`, `syscall.handle_interrupt_entry.entryXG`
  and `kernel_entry.entryXG`: the kernel-entry composites with the `finish`
  call taken as a hypothesis that may use `XG` (and `BXI`) at the `finish`
  state.  `syscall.handle_syscall_old.entry'` re-derives QueueEntry's
  `handle_syscall_old.entry` from `entryXG` (the original is an instance).

`SigXG` (a definition, like `TmoXG`, not a premise of any top): `send_signal`
from an `XG` state ends at an `XG` state.  Since #80/#85 `send_signal` may write
the bound thread's IPC buffer (`vcpu.report`'s full-state completion), so its
footprint is no longer in `KW`; the `send_signal` line proves it (from a
widened footprint inside `IpcW`, `SigXG.of_ipcFoot`).  It is used only by
`handle_interrupt.xg` and the IRQ entry.

No premise is added to any existing top; no existing statement changes.
-/
import Fl4Proofs.P1.QueueInvAll
import Fl4Proofs.P1.QueueIpcFoot
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {P3Ok : S → Prop}
variable {A : Type _} {ar : machine.Arch A} {Ac : Set U64}

/-! ## `XG` and the `IpcW` footprint -/

/-- `XG` is kept by an `IpcW` footprint (user words of `U`, given `UserOK`). -/
theorem XG.ipc {U : Set U64} {s s' : S} (h : XG st T Cs Ω H Sg Scs Z P3Ok s) (hU : UserOK st T Cs Ω H U s)
    (f : IpcFoot st T Cs Ω Sg Scs Z (EH H) U s s') : XG st T Cs Ω H Sg Scs Z P3Ok s' :=
  h.of_fr (WritesIn.mono f fun _ hb => IpcW.cur0w hU hb)

/-! ## Blocking steps -/

/-- The words of a blocking step (`BlkFoot`) are `KW` words. -/
theorem blkfoot_kw {s : S} {t r0 b : U64} {Es : Set U64} (ht : t ∈ T) (hc : L.cpu s ∈ Cs)
    (hr : r0 ≠ 0#u64 → rTcbA r0 ∈ Sg) (hb : BlkFoot st s t r0 b) : KW st T Cs Sg Scs Z Es s b := by
  rcases hb with ⟨K, hK, rfl⟩ | rfl | ⟨h0, rfl⟩
  · exact kw_field ht (by omega) (by omega) (by omega)
  · exact kw_node hc (by rw [act_val]; omega) (by rw [act_val]; omega)
  · exact kw_sg (hr h0)

/-- `ep_append` of a thread being blocked (the only thread of the exception
set) writes `KW` words. -/
theorem ep_append_kw {s : S} {e t state : U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H {y | y ∈ (∅ : Set U64) ∨ y = t} s Q R) (ht : t ∈ T) (hH : H e = some .ep) :
    endpoint.ep_append st s e t state ⦃ s' => Foot st T Cs Sg Scs Z (EH H) s s' ⦄ := by
  obtain ⟨E5, EQ5, hEW5⟩ := h.eps
  have he5 : e ∈ E5 := (hEW5.2.2.2.2.2.2.2.1 e).2 (Or.inl hH)
  obtain ⟨hE5, -, hq5⟩ := hEW5.1 e he5
  have htn : t ∉ EQ5 e := fun hm => (hEW5.2.2.2.1 e he5 t hm).1 (Or.inr rfl)
  refine WP.spec_mono (endpoint.ep_append.foot s e t state (EQ5 e) h.tcbs hE5 hq5 ht htn) fun s' w => ?_
  refine Foot.of w fun b hb => hb.kw ?_ (Or.inl hH)
  intro w hw
  rcases List.mem_cons.1 hw with rfl | hw
  · exact ht
  · exact hq5.mem w hw

/-- `ntfn_append` of a thread being blocked writes `KW` words. -/
theorem ntfn_append_kw {s : S} {n t : U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H {y | y ∈ (∅ : Set U64) ∨ y = t} s Q R) (ht : t ∈ T) (hH : H n = some .ntfn) :
    notification.ntfn_append st s n t ⦃ s' => Foot st T Cs Sg Scs Z (EH H) s s' ⦄ := by
  obtain ⟨E5, EQ5, hEW5⟩ := h.eps
  have he5 : n ∈ E5 := (hEW5.2.2.2.2.2.2.2.1 n).2 (Or.inr hH)
  obtain ⟨hE5, -, hq5⟩ := hEW5.1 n he5
  have htn : t ∉ EQ5 n := fun hm => (hEW5.2.2.2.1 n he5 t hm).1 (Or.inr rfl)
  refine WP.spec_mono (notification.ntfn_append.foot s n t (EQ5 n) h.tcbs hE5 hq5 ht htn) fun s' w => ?_
  refine Foot.of w fun b hb => hb.kw ?_ (Or.inr hH)
  intro w hw
  rcases List.mem_cons.1 hw with rfl | hw
  · exact ht
  · exact hq5.mem w hw

/-- **`wait_for_sender`'s footprint** (the blocking receive on an idle or
receiving endpoint, with the reply object; or the badge clear). -/
theorem endpoint.wait_for_sender.kw (s : S) (t e : U64) (blocking : Bool) (reply : U64)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hSg : SgOK st Ω Sg s)
    (ht : t ∈ T) (hc : blocking = true → CanBlock st T Ac s t) (hH : H e = some .ep)
    (hr : reply ≠ 0#u64 → reply ∈ Rp) :
    endpoint.wait_for_sender st s t e blocking reply ⦃ s' => Foot st T Cs Sg Scs Z (EH H) s s' ⦄ := by
  have hta := h.tcbs t ht
  have hN := h.nodes _ h.cur
  have hrs : reply ≠ 0#u64 → rTcbA reply ∈ Sg := fun h0 => hX.1.tcbW (hr h0)
  unfold endpoint.wait_for_sender
  split
  · have hc := hc ‹_›
    step with obj.Tcb.set_state.spec as ⟨s1, e1⟩
    step with obj.Tcb.set_block_obj.wr as ⟨s2, e2⟩
    step with obj.Tcb.set_reply_obj.wr as ⟨s3, e3⟩
    have h1 : SchedQueuesInvX st T Cs Ω H {y | y ∈ (∅ : Set U64) ∨ y = t} s1 Q R := by
      rw [e1]; exact blk_set_state h hc
    have h2 : SchedQueuesInvX st T Cs Ω H {y | y ∈ (∅ : Set U64) ∨ y = t} s2 Q R := by
      rw [e2]; exact inv_wr_fieldX (K := 3336#u64) h1 ht (Or.inr rfl) (by simp) (by simp) (by simp)
    have h3 : SchedQueuesInvX st T Cs Ω H {y | y ∈ (∅ : Set U64) ∨ y = t} s3 Q R := by
      rw [e3]; exact inv_wr_fieldX (K := 3360#u64) h2 ht (Or.inr rfl) (by simp) (by simp) (by simp)
    rw [stA_eq] at e1
    have w3 : WritesIn st s s3 (BlkFoot st s t reply) := by
      rw [e3, e2, e1]
      exact blk_wr_field (K := 3360#u64) hta (blk_wr_field hta (blk_wr_field hta (WritesIn.refl _ _) (by simp))
        (by simp)) (by simp)
    have v3 : L.mem s3 (stA t) = sched.TS_BLOCKED_ON_RECV := by
      rw [e3, fld_wr_ne' (K := 3360#u64) (a := replyA t) hta rfl (stA_eq t) (by simp) (by simp) (by simp) (by simp) (by simp),
        e2, fld_wr_ne' hta (blockA_eq t) (stA_eq t) (by simp) (by simp) (by simp) (by simp) (by simp), e1, stA_eq]
      exact L.mem_wr_same (field_aligned hta (by simp) (by simp))
    have a3 : L.actionW s3 = L.actionW s := by
      rw [e3, act_wr_field (K := 3360#u64) (a := replyA t) (h2.nodes _ h2.cur) ht hta rfl (by simp) (by simp),
        e2, act_wr_field (h1.nodes _ h1.cur) ht hta (blockA_eq t) (by simp) (by simp),
        e1, act_wr_field hN ht hta rfl (by simp) (by simp)]
    refine WP.spec_bind (sched.schedule_tcb.blk s3 t h3 (by rw [v3]; exact blocked_not_runnable (Or.inr (Or.inl rfl)))) ?_
    rintro s4 ⟨h4, e4, -⟩
    obtain ⟨w4, -, -, -, -, -⟩ := blk_sched h3 ht w3 a3 e4
    have F4 : Foot st T Cs Sg Scs Z (EH H) s s4 := Foot.of w4 fun b hb => blkfoot_kw ht h.cur hrs hb
    split
    · rename_i hne
      have h0 : reply ≠ 0#u64 := by simpa using hne
      have hm : rTcbA reply ∈ Ω := hSg.sub _ (hrs h0)
      step with obj.Reply.set_tcb.spec as ⟨s6, e6⟩
      try simp only [Aeneas.Std.bind_ok]
      obtain ⟨h6, -, -⟩ := omega_wr (v := t) h4 hm
      rw [← e6] at h6
      have F6 : Foot st T Cs Sg Scs Z (EH H) s s6 := by
        rw [e6]; exact Foot.of (blk_wr_reply (h4.omega _ hm).1 h0 w4) fun b hb => blkfoot_kw ht h.cur hrs hb
      exact WP.spec_mono (ep_append_kw h6 ht hH) fun s' f => F6.trans f
    · try simp only [Aeneas.Std.bind_ok]
      exact WP.spec_mono (ep_append_kw h4 ht hH) fun s' f => F4.trans f
  · refine WP.spec_mono (obj.Tcb.set_reg.badge s t 0#u64 hta) fun s' e' => ?_
    subst e'
    exact foot_field (K := 256#u64) h.tcbs ht (by simp) (by simp) (by simp) (by simp)

/-- **The blocking receive on a notification writes `KW` words** (`ntfn_block`'s footprint). -/
theorem ntfn_block.kw (s : S) (a : A) (t n : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hc : CanBlock st T Ac s t) (hidle : L.idleW s ≠ t)
    (hH : H n = some .ntfn) (hst0 : L.epState s n = 0#u64 ∨ L.epState s n = 1#u64) :
    (do
      let s1 ← obj.Tcb.set_state st t s sched.TS_BLOCKED_ON_NTFN
      let s2 ← obj.Tcb.set_block_obj st t s1 n
      let s3 ← sched.schedule_tcb st s2 t
      let s4 ← notification.ntfn_append st s3 n t
      let s5 ← notification.maybe_return_sched_context st s4 n t
      ok (s5, a)) ⦃ s' _ => Foot st T Cs Sg Scs Z (EH H) s s' ⦄ := by
  have ht := hc.mem
  have hta := h.tcbs t ht
  have hN := h.nodes _ h.cur
  step with obj.Tcb.set_state.spec as ⟨s1, e1⟩
  step with obj.Tcb.set_block_obj.wr as ⟨s2, e2⟩
  have h1 : SchedQueuesInvX st T Cs Ω H {y | y ∈ (∅ : Set U64) ∨ y = t} s1 Q R := by
    rw [e1]; exact blk_set_state h hc
  have h2 : SchedQueuesInvX st T Cs Ω H {y | y ∈ (∅ : Set U64) ∨ y = t} s2 Q R := by
    rw [e2]; exact inv_wr_fieldX (K := 3336#u64) h1 ht (Or.inr rfl) (by simp) (by simp) (by simp)
  rw [stA_eq] at e1
  have w2 : WritesIn st s s2 (BlkFoot st s t 0#u64) := by
    rw [e2, e1]; exact blk_wr_field hta (blk_wr_field (K := 3328#u64) hta (WritesIn.refl _ _) (by simp)) (by simp)
  have v2 : L.mem s2 (stA t) = sched.TS_BLOCKED_ON_NTFN := by
    rw [e2, fld_wr_ne' hta (blockA_eq t) (stA_eq t) (by simp) (by simp) (by simp) (by simp) (by simp), e1, stA_eq]
    exact L.mem_wr_same (field_aligned hta (by simp) (by simp))
  have b2 : L.mem s2 (blockA t) = n := by
    rw [e2]; exact L.mem_wr_same (field_aligned hta (by simp) (by simp))
  have a2 : L.actionW s2 = L.actionW s := by
    rw [e2, act_wr_field (h1.nodes _ h1.cur) ht hta (blockA_eq t) (by simp) (by simp),
      e1, act_wr_field hN ht hta rfl (by simp) (by simp)]
  have hbl : Blocked sched.TS_BLOCKED_ON_NTFN := Or.inr (Or.inr rfl)
  refine WP.spec_bind (sched.schedule_tcb.blk s2 t h2 (by rw [v2]; exact blocked_not_runnable hbl)) ?_
  rintro s3 ⟨h3, e3, hc3⟩
  obtain ⟨w3, a3, v3, b3, -, -⟩ := blk_sched h2 ht w2 a2 e3
  rw [v2] at v3; rw [b2] at b3
  have F3 : Foot st T Cs Sg Scs Z (EH H) s s3 := Foot.of w3 fun b hb => blkfoot_kw ht h.cur (fun h0 => absurd rfl h0) hb
  obtain ⟨-, -, r3, -, r6⟩ := ts_vals
  refine WP.spec_bind (WP.spec_and (blk_tail (f := notification.ntfn_append st s3 n t) (r0 := 0#u64) (hidl := hidle)
    h hB hX hS hSg ht
    (Or.inr (Or.inr ⟨rfl, hH, rfl⟩)) hst0 h3 w3 a3 v3 b3 (fun h0 => absurd rfl h0)
    (fun h1 => absurd (v3.symm.trans h1) (by rw [r3, r6]; decide)) hc.old (fun h0 => absurd rfl h0) hc.ac
    (fun xs hE hq hn => WP.spec_mono (WP.spec_and
      (notification.ntfn_append.rel s3 n t xs h3.tcbs hE hq ht hn)
      (notification.ntfn_append.foot s3 n t xs h3.tcbs hE hq ht hn))
      fun s4 hh => ⟨hh.1.1, by rw [hh.1.2, ntfn_wait_val], hh.2⟩))
    (ntfn_append_kw (Sg := Sg) (Scs := Scs) (Z := Z) h3 ht hH)) ?_
  rintro s4 ⟨⟨h4, hB4, hX4, hS4, hSg4, ea4, ec4, v4, ei4⟩, F4⟩
  refine WP.spec_bind (notification.maybe_return_sched_context.kw s4 n t Q R h4 hB4 hX4 hS4 hSg4 ht
    (blocked_out h4 ht (by rw [v4]; exact blocked_not_runnable hbl)) (by rw [ei4]; exact hidle)) ?_
  rintro s5 F5
  simp only [WP.spec_ok, WP.uncurry'_pair]
  exact F3.trans (F4.trans F5)

/-! ## `receive_signal` and `complete_signal` -/

/-- **`receive_signal` keeps `XG`.** -/
theorem notification.receive_signal.xg (hA : P0.ArchTotal ar)
    (s : S) (a : A) (t n : U64) (blocking : Bool) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hc : CanBlock st T Ac s t)
    (hnN : n ∈ Nt) (hn : H n = some .ntfn) (h3 : L.epState s n ≠ 3#u64)
    (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) :
    notification.receive_signal st ar s a t n blocking ⦃ s' _ => XG st T Cs Ω H Sg Scs Z P3Ok s' ⦄ := by
  have ht := hc.mem
  have hT := h.tcbs
  have hta := hT t ht
  by_cases e01 : L.epState s n = 0#u64 ∨ L.epState s n = 1#u64
  · have nb : (do let s1 ← obj.Tcb.set_reg st t s layout.reg.BADGE 0#u64; ok (s1, a)) ⦃ s' _ =>
        XG st T Cs Ω H Sg Scs Z P3Ok s' ⦄ := by
      refine WP.spec_bind (obj.Tcb.set_reg.badge s t 0#u64 hta) ?_
      rintro s1 rfl
      simp only [WP.spec_ok, WP.uncurry'_pair]
      exact hG.foot (foot_field (K := 256#u64) hT ht (by simp) (by simp) (by simp) (by simp))
    have blk' : (do
        let s1 ← obj.Tcb.set_state st t s sched.TS_BLOCKED_ON_NTFN
        let s2 ← obj.Tcb.set_block_obj st t s1 n
        let s3 ← sched.schedule_tcb st s2 t
        let s4 ← notification.ntfn_append st s3 n t
        let s5 ← notification.maybe_return_sched_context st s4 n t
        ok (s5, a)) ⦃ s' _ => XG st T Cs Ω H Sg Scs Z P3Ok s' ⦄ :=
      WP.spec_mono (ntfn_block.kw s a t n Q R h hB hX hS hSg hc hc.ni hn e01) fun r f => by
        obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at f ⊢; exact hG.foot f
    unfold notification.receive_signal
    step with obj.Ntfn.state.spec as ⟨v, hv⟩
    split
    · split
      · exact blk'
      · exact nb
    · split
      · split
        · exact blk'
        · exact nb
      · exfalso
        rename_i h1 h2
        rw [ntfn_idle_val] at h1; rw [ntfn_wait_val'] at h2
        rcases e01 with e0 | e0 <;> rw [← hv] at e0 <;> contradiction
  have hact : L.epState s n = 2#u64 := by
    have := (L.mem s (epTSA n)).val
    push_neg at e01
    simp only [LawfulStore.epState] at e01 h3 ⊢
    apply UScalar.eq_of_val_eq
    have hb : (L.mem s (epTSA n) &&& 3#u64).val < 4 := by
      rw [UScalar.val_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
    have e0 : (L.mem s (epTSA n) &&& 3#u64).val ≠ 0 := fun e => e01.1 (UScalar.eq_of_val_eq e)
    have e1 : (L.mem s (epTSA n) &&& 3#u64).val ≠ 1 := fun e => e01.2 (UScalar.eq_of_val_eq e)
    have e3 : (L.mem s (epTSA n) &&& 3#u64).val ≠ 3 := fun e => h3 (UScalar.eq_of_val_eq e)
    show (L.mem s (epTSA n) &&& 3#u64).val = 2
    omega
  have hta' := hc.na
  have hti := hc.ni
  have htq := hc.nq
  have htr := hc.nr
  have hnΩ : ntfnScA n ∈ Ω := hSg.sub _ (hX.1.ntW n hnN)
  have hns : L.mem s (ntfnScA n) ≠ 0#u64 → L.mem s (ntfnScA n) ∈ Scs ∧
      L.mem s (scCoreA (L.mem s (ntfnScA n))) ∈ Cs := fun h0 => by
    obtain ⟨hc', -⟩ := hX.2.2.nsc n hnN h0
    exact ⟨hc', hX.2.2.core _ hc'⟩
  have hdA : L.mem s (ntfnScA n) ≠ 0#u64 → L.mem s (scA t) = 0#u64 → Sch st s t → L.mem s (ntfnScA n) ∈ Ac := by
    intro _ h0 hS'
    exfalso
    rcases hS' with e | e | e | e | ⟨e1, e2⟩ | e
    · exact e hc.nq
    · exact e hc.nr
    · exact hc.na e
    · exact hc.ni e
    · exact hB.resume e1 (by rw [e2]; exact h0)
    · rcases e with e | e
      · exact hc.nb e
      · exact hc.nrp e
  have hN := h.nodes _ h.cur
  obtain ⟨E, EQ, hEW⟩ := h.eps
  have he : n ∈ E := (hEW.2.2.2.2.2.2.2.1 n).2 (Or.inr hn)
  obtain ⟨hE, -, -⟩ := hEW.1 n he
  unfold notification.receive_signal
  step with obj.Ntfn.state.spec as ⟨v, hv⟩
  rw [if_neg (by rw [hv, hact, ntfn_idle_val]; decide), if_neg (by rw [hv, hact, ntfn_wait_val']; decide)]
  step with obj.Ntfn.badge.any as ⟨b1, _⟩
  refine WP.spec_bind (obj.Tcb.set_reg.badge s t b1 hta) fun s1 e1 => ?_
  subst e1
  have g1 : XG st T Cs Ω H Sg Scs Z P3Ok (L.wr s (core.num.U64.wrapping_add t 256#u64) b1) :=
    hG.foot (foot_field (K := 256#u64) hT ht (by simp) (by simp) (by simp) (by simp))
  obtain ⟨h1, hB1, hX1, hS1, hSg1⟩ := badge_all (v := b1) h hB hX hS hSg ht
  have ha1 : Aligned (core.num.U64.wrapping_add t 256#u64) := field_aligned hta (by simp) (by simp)
  have f1 : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (y = t → K.val ≠ 256) →
      L.mem (L.wr s (core.num.U64.wrapping_add t 256#u64) b1) (core.num.U64.wrapping_add y K) =
        L.mem s (core.num.U64.wrapping_add y K) := fun y hy K hK hK8 hne =>
    L.mem_wr_ne ha1 (field_aligned (hT y hy) hK hK8)
      (fun e => field_ne hta (hT y hy) (by simp) hK (fun e' => by subst e'; exact fun h' => hne rfl h'.symm)
        (UScalar.eq_of_val_eq e))
  have o1 : ∀ x ∈ Ω, L.mem (L.wr s (core.num.U64.wrapping_add t 256#u64) b1) x = L.mem s x := fun x hx =>
    L.mem_wr_ne ha1 (h.omega x hx).1 (fun e => out_ne_field (h.omega x hx) ht hta (by simp) e)
  have ts1 : L.mem (L.wr s (core.num.U64.wrapping_add t 256#u64) b1) (epTSA n) = L.mem s (epTSA n) :=
    L.mem_wr_ne ha1 (ep_aligned hE).2 (by
      rw [field_val hta (by simp), epTSA_val hE]; have := hE.disj t ht; simp; omega)
  have hact1 : L.epState (L.wr s (core.num.U64.wrapping_add t 256#u64) b1) n = 2#u64 := by
    simp only [LawfulStore.epState]; rw [ts1]; exact hact
  have ei1 : L.idleW (L.wr s (core.num.U64.wrapping_add t 256#u64) b1) = L.idleW s := by
    unfold LawfulStore.idleW; rw [LawfulStore.cpu_wr, nodeAt_wr]
    exact L.mem_wr_ne ha1 (nodeAt_aligned hN (by rw [idle8]; omega) (by rw [idle8]))
      (fun e => node_ne_field (K := 256#u64) hN (by rw [idle8]; omega) ht hta (by simp) (UScalar.eq_of_val_eq e).symm)
  set s1 := L.wr s (core.num.U64.wrapping_add t 256#u64) b1 with hs1
  refine WP.spec_bind (obj.Ntfn.set_state.val s1 n _) fun s2 e2 => ?_
  subst e2
  have g2 := g1.foot (foot_wr (Sg := Sg) (Scs := Scs) (Z := Z) (v := (L.mem s1 (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64))
    (ep_aligned hE).2 (kw_ep (Or.inr hn) (Or.inr rfl)))
  obtain ⟨h2, hB2, hX2, hS2, hSg2, f2, o2, ea2, ei2, ec2⟩ := ntfn_idle_all h1 hB1 hX1 hS1 hSg1 hn hact1
  set s2 := L.wr s1 (epTSA n) ((L.mem s1 (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64)) with hs2
  have F : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 → (y = t → K.val ≠ 256) →
      L.mem s2 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K hK hK8 h1' h2' h3' => (f2 y hy K hK hK8 h1' h2').trans (f1 y hy K hK hK8 h3')
  have O : ∀ x ∈ Ω, L.mem s2 x = L.mem s x := fun x hx => (o2 x hx).trans (o1 x hx)
  have iq2 : L.mem s2 (inqA t) = L.mem s (inqA t) := by
    rw [inqA_eq]; exact F t ht _ (by simp) (by simp) (by simp) (by simp) (fun _ => by simp)
  have sc2 : L.mem s2 (scA t) = L.mem s (scA t) := by
    rw [scA_eq]; exact F t ht _ (by simp) (by simp) (by simp) (by simp) (fun _ => by simp)
  have ea2' : L.actionW s2 = L.actionW s := by
    rw [ea2, hs1, act_wr_field hN ht hta rfl (by simp) (by simp)]
  have hc2 : L.mem s2 (ntfnScA n) = L.mem s (ntfnScA n) := O _ hnΩ
  refine WP.spec_bind (notification.maybe_donate_sched_context.tinvF (Es := EH H) hA s2 a t n Q R h2 hB2 hX2 hS2 hSg2 ht
    (by rw [iq2]; exact htq) (by rw [iq2]; exact htr) (by rw [ea2']; exact hta') (by rw [ei2, ei1]; exact hti)
    fun h0 _ _ => ?_) ?_
  · rw [hc2] at h0 ⊢
    obtain ⟨c1, c3⟩ := hns h0
    obtain ⟨-, hcΩ⟩ := objs_omega hX.1 hSg.sub
    refine ⟨c1, by rw [O _ (hcΩ _ c1).2.1]; exact c3, fun hS2t => hdA h0 (by rw [← sc2]; assumption) ?_⟩
    have f21 : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
        L.mem s2 (core.num.U64.wrapping_add t K) = L.mem s1 (core.num.U64.wrapping_add t K) :=
      fun K a1 a2 a3 a4 => f2 t ht K a1 a2 a3 a4
    have hS1t : Sch st s1 t := Sch.of_eq
      (fun hf => by rwa [inqA_eq, f21 _ (by simp) (by simp) (by simp) (by simp)] at hf)
      (fun hf => by rwa [inqA_eq, f21 _ (by simp) (by simp) (by simp) (by simp)] at hf)
      ea2 ei2 ec2 (by rw [stA_eq]; exact f21 _ (by simp) (by simp) (by simp) (by simp)) hS2t
    exact Sch.wr_field h ht (by simp) (by simp) (by simp) ht hS1t
  rintro ⟨s3, a1⟩ ⟨⟨⟨Q3, R3, h3⟩, hB3, hX3, hS3, hSg3⟩, -, F3, -⟩
  try simp only [WP.uncurry'_pair]
  have g3 := g2.footD F3
  have ok3 : (ok (s3, a1) : Result (S × A)) ⦃ s' _ => XG st T Cs Ω H Sg Scs Z P3Ok s' ⦄ :=
    (WP.spec_ok _).2 g3
  step with obj.Tcb.sc.spec as ⟨i1, ei1⟩
  step with sched.cur_sc.spec as ⟨c4, _⟩
  step with sc_ne.spec as ⟨b3⟩
  split
  · step with sporadic.sc_sporadic.spec as ⟨b2, eb2⟩
    split
    · rename_i hb2
      have hi1S : i1 ∈ Scs := (hX3.2.2.bound t ht (by rw [← ei1]; exact (eb2 hb2).1)).1 |> fun h => by
        rw [← ei1] at h; exact h
      refine WP.spec_bind (sporadic.unblock_check.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s3 t i1 h3 hB3 hX3
        hS3 hSg3 ht ei1 (eb2 hb2).1 (hS3.spor i1 hi1S (eb2 hb2).2)) fun s5 F5 => ?_
      exact (WP.spec_ok _).2 (g3.foot F5)
    · exact ok3
  · exact ok3

/-- **`complete_signal` keeps `XG`** (under `complete_signal.ipc`'s hypotheses). -/
theorem notification.complete_signal.xg (hA : P0.ArchTotal ar)
    (s : S) (a : A) (n t : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T)
    (htq : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64) (htr : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64)
    (hta' : L.actionW s ≠ t) (hti : L.idleW s ≠ t) (hn : H n = some .ntfn) (hnΩ : ntfnScA n ∈ Ω)
    (hns : L.mem s (ntfnScA n) ≠ 0#u64 → L.mem s (ntfnScA n) ∈ Scs ∧
      L.mem s (scCoreA (L.mem s (ntfnScA n))) ∈ Cs)
    (hdA : L.mem s (ntfnScA n) ≠ 0#u64 → L.mem s (scA t) = 0#u64 → Sch st s t → L.mem s (ntfnScA n) ∈ Ac)
    (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) :
    notification.complete_signal st ar s a n t ⦃ s' _ => XG st T Cs Ω H Sg Scs Z P3Ok s' ⦄ := by
  have hT := h.tcbs
  have hta := hT t ht
  have hN := h.nodes _ h.cur
  have ok0 : (ok (s, a) : Result (S × A)) ⦃ s' _ => XG st T Cs Ω H Sg Scs Z P3Ok s' ⦄ := (WP.spec_ok _).2 hG
  obtain ⟨E, EQ, hEW⟩ := h.eps
  have he : n ∈ E := (hEW.2.2.2.2.2.2.2.1 n).2 (Or.inr hn)
  obtain ⟨hE, -, -⟩ := hEW.1 n he
  unfold notification.complete_signal
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · exact ok0
  step with obj.Ntfn.state.spec as ⟨i, ei⟩
  split
  · exact ok0
  rename_i hia
  have hact : L.epState s n = 2#u64 := by rw [← ei]; exact ntfn_active_ne hia
  step with obj.Ntfn.badge.any as ⟨b1, _⟩
  refine WP.spec_bind (obj.Tcb.set_reg.badge s t b1 hta) fun s1 e1 => ?_
  subst e1
  have g1 : XG st T Cs Ω H Sg Scs Z P3Ok (L.wr s (core.num.U64.wrapping_add t 256#u64) b1) :=
    hG.foot (foot_field (K := 256#u64) hT ht (by simp) (by simp) (by simp) (by simp))
  obtain ⟨h1, hB1, hX1, hS1, hSg1⟩ := badge_all (v := b1) h hB hX hS hSg ht
  have ha1 : Aligned (core.num.U64.wrapping_add t 256#u64) := field_aligned hta (by simp) (by simp)
  have f1 : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (y = t → K.val ≠ 256) →
      L.mem (L.wr s (core.num.U64.wrapping_add t 256#u64) b1) (core.num.U64.wrapping_add y K) =
        L.mem s (core.num.U64.wrapping_add y K) := fun y hy K hK hK8 hne =>
    L.mem_wr_ne ha1 (field_aligned (hT y hy) hK hK8)
      (fun e => field_ne hta (hT y hy) (by simp) hK (fun e' => by subst e'; exact fun h' => hne rfl h'.symm)
        (UScalar.eq_of_val_eq e))
  have o1 : ∀ x ∈ Ω, L.mem (L.wr s (core.num.U64.wrapping_add t 256#u64) b1) x = L.mem s x := fun x hx =>
    L.mem_wr_ne ha1 (h.omega x hx).1 (fun e => out_ne_field (h.omega x hx) ht hta (by simp) e)
  have ts1 : L.mem (L.wr s (core.num.U64.wrapping_add t 256#u64) b1) (epTSA n) = L.mem s (epTSA n) :=
    L.mem_wr_ne ha1 (ep_aligned hE).2 (by
      rw [field_val hta (by simp), epTSA_val hE]; have := hE.disj t ht; simp; omega)
  have hact1 : L.epState (L.wr s (core.num.U64.wrapping_add t 256#u64) b1) n = 2#u64 := by
    simp only [LawfulStore.epState]; rw [ts1]; exact hact
  have ei1 : L.idleW (L.wr s (core.num.U64.wrapping_add t 256#u64) b1) = L.idleW s := by
    unfold LawfulStore.idleW; rw [LawfulStore.cpu_wr, nodeAt_wr]
    exact L.mem_wr_ne ha1 (nodeAt_aligned hN (by rw [idle8]; omega) (by rw [idle8]))
      (fun e => node_ne_field (K := 256#u64) hN (by rw [idle8]; omega) ht hta (by simp) (UScalar.eq_of_val_eq e).symm)
  set s1 := L.wr s (core.num.U64.wrapping_add t 256#u64) b1 with hs1
  refine WP.spec_bind (obj.Ntfn.set_state.val s1 n _) fun s2 e2 => ?_
  subst e2
  have g2 := g1.foot (foot_wr (Sg := Sg) (Scs := Scs) (Z := Z) (v := (L.mem s1 (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64))
    (ep_aligned hE).2 (kw_ep (Or.inr hn) (Or.inr rfl)))
  obtain ⟨h2, hB2, hX2, hS2, hSg2, f2, o2, ea2, ei2, ec2⟩ := ntfn_idle_all h1 hB1 hX1 hS1 hSg1 hn hact1
  set s2 := L.wr s1 (epTSA n) ((L.mem s1 (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64)) with hs2
  have F : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 → (y = t → K.val ≠ 256) →
      L.mem s2 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K hK hK8 h1' h2' h3' => (f2 y hy K hK hK8 h1' h2').trans (f1 y hy K hK hK8 h3')
  have O : ∀ x ∈ Ω, L.mem s2 x = L.mem s x := fun x hx => (o2 x hx).trans (o1 x hx)
  have iq2 : L.mem s2 (inqA t) = L.mem s (inqA t) := by
    rw [inqA_eq]; exact F t ht _ (by simp) (by simp) (by simp) (by simp) (fun _ => by simp)
  have sc2 : L.mem s2 (scA t) = L.mem s (scA t) := by
    rw [scA_eq]; exact F t ht _ (by simp) (by simp) (by simp) (by simp) (fun _ => by simp)
  have ea2' : L.actionW s2 = L.actionW s := by
    rw [ea2, hs1, act_wr_field hN ht hta rfl (by simp) (by simp)]
  have hc2 : L.mem s2 (ntfnScA n) = L.mem s (ntfnScA n) := O _ hnΩ
  refine WP.spec_bind (notification.maybe_donate_sched_context.tinvF (Es := EH H) hA s2 a t n Q R h2 hB2 hX2 hS2 hSg2 ht
    (by rw [iq2]; exact htq) (by rw [iq2]; exact htr) (by rw [ea2']; exact hta') (by rw [ei2, ei1]; exact hti)
    fun h0 _ _ => ?_) ?_
  · rw [hc2] at h0 ⊢
    obtain ⟨c1, c3⟩ := hns h0
    obtain ⟨-, hcΩ⟩ := objs_omega hX.1 hSg.sub
    refine ⟨c1, by rw [O _ (hcΩ _ c1).2.1]; exact c3, fun hS2t => hdA h0 (by rw [← sc2]; assumption) ?_⟩
    have f21 : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
        L.mem s2 (core.num.U64.wrapping_add t K) = L.mem s1 (core.num.U64.wrapping_add t K) :=
      fun K a1 a2 a3 a4 => f2 t ht K a1 a2 a3 a4
    have hS1t : Sch st s1 t := Sch.of_eq
      (fun hf => by rwa [inqA_eq, f21 _ (by simp) (by simp) (by simp) (by simp)] at hf)
      (fun hf => by rwa [inqA_eq, f21 _ (by simp) (by simp) (by simp) (by simp)] at hf)
      ea2 ei2 ec2 (by rw [stA_eq]; exact f21 _ (by simp) (by simp) (by simp) (by simp)) hS2t
    exact Sch.wr_field h ht (by simp) (by simp) (by simp) ht hS1t
  rintro ⟨s3, a1⟩ ⟨⟨⟨Q3, R3, h3⟩, hB3, hX3, hS3, hSg3⟩, -, F3, -⟩
  try simp only [WP.uncurry'_pair]
  have g3 := g2.footD F3
  have ok3 : (ok (s3, a1) : Result (S × A)) ⦃ s' _ => XG st T Cs Ω H Sg Scs Z P3Ok s' ⦄ :=
    (WP.spec_ok _).2 g3
  step with obj.Tcb.sc.spec as ⟨i1, ei1⟩
  step with sporadic.sc_sporadic.spec as ⟨b2, eb2⟩
  split
  · rename_i hb2
    step with obj.Ntfn.sc.val as ⟨i2, _⟩
    split
    · step with sched.cur_sc.spec as ⟨c4, _⟩
      step with sc_ne.spec as ⟨b3⟩
      split
      · have hi1S : i1 ∈ Scs := (hX3.2.2.bound t ht (by rw [← ei1]; exact (eb2 hb2).1)).1 |> fun h => by
          rw [← ei1] at h; exact h
        refine WP.spec_bind (sporadic.unblock_check.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s3 t i1 h3 hB3
          hX3 hS3 hSg3 ht ei1 (eb2 hb2).1 (hS3.spor i1 hi1S (eb2 hb2).2)) fun s5 F5 => ?_
        exact (WP.spec_ok _).2 (g3.foot F5)
      · exact ok3
    · exact ok3
  · exact ok3

/-! ## `receive_from_sender` and `receive_ipc` -/

set_option maxHeartbeats 4000000 in
/-- **`receive_from_sender` keeps `XG`**: the dequeue is a `KW` step, the
transfer keeps `XG` (`XferOK`'s guard), the sender's wake-up / reply push /
inactivation are `KW` / `FootD` steps. -/
theorem endpoint.receive_from_sender.xg (hA : P0.ArchTotal ar)
    {U : Set U64} (hxf : XferOK st ar T Cs Ω H Sg Rp Scs Nt Z U (XG st T Cs Ω H Sg Scs Z P3Ok)) (s : S) (a : A)
    (thread e reply : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hU : UserOK st T Cs Ω H U s)
    (hc : CanBlock st T Ac s thread)
    (hH : H e = some .ep) (hst : L.epState s e ≠ 0#u64 ∧ L.epState s e ≠ 2#u64)
    (hr : reply ≠ 0#u64 → reply ∈ Rp ∧ (L.mem s (rTcbA reply) = 0#u64 ∨ L.mem s (rTcbA reply) = thread))
    (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) :
    endpoint.receive_from_sender st ar s a thread e reply ⦃ s' _ => XG st T Cs Ω H Sg Scs Z P3Ok s' ⦄ := by
  have hT := h.tcbs
  have ht := hc.mem
  have hst1 : L.epState s e = 1#u64 := by
    rcases ep_state3 h hH with e0 | e0 | e0
    · exact absurd e0 hst.1
    · exact e0
    · exact absurd e0 hst.2
  have F0 := endpoint.ep_dequeue.head_kw (Sg := Sg) (Scs := Scs) (Z := Z) h hH (Or.inl hst1)
  obtain ⟨hdT, hbe, hds, -⟩ := ep_head h hH (Or.inl rfl) hst1
  have hds := hds rfl
  set hd := (L.epQ s e).head with hhd
  have hdt : hd ≠ thread := fun e' => hc.nb (by rw [← e', hds]; exact Or.inl rfl)
  have hdi : L.idleW s ≠ hd := fun e' => hB.idleNB (by rw [e', hds]; exact Or.inl (Or.inl rfl))
  have hr' : reply ≠ 0#u64 → reply ∈ Rp ∧ L.mem s (rTcbA reply) = 0#u64 := fun h0 => by
    obtain ⟨h1, h2⟩ := hr h0
    refine ⟨h1, h2.resolve_right fun e' => hX.noref (hT _ ht) hc.nrp (fun e2 => hc.nb (Or.inr (Or.inl e2))) _ h1 e'⟩
  unfold endpoint.receive_from_sender
  step with endpoint.get_queue.spec as ⟨q, eq⟩
  subst eq
  have hdq := endpoint.ep_dequeue.inv s hd Q R h hdT (by simp) (Or.inl hds)
  rw [hbe] at hdq
  refine WP.spec_bind (WP.spec_and hdq F0) ?_
  rintro s1 ⟨⟨h1, f1, o1, n1, k1, c1, nc1⟩, F1⟩
  have g1 : XG st T Cs Ω H Sg Scs Z P3Ok s1 := hG.foot F1
  obtain ⟨hB1, hX1, hS1, hSg1, ea1, ec1, ei1⟩ := frame_bx h hB hX hS hSg f1 o1 n1 k1
    (TmFr.mk0 ⟨k1, fun y hy K a b c => f1 y hy K (by omega) c (by omega) (by omega),
      fun c hc o ho => nc1 c hc o (by omega) (by omega), fun n' hn' => o1 _ (hSg.sub _ (hX.1.ntB n' hn').2)⟩)
  step with obj.Tcb.block_badge.any as ⟨badge, _⟩
  step with obj.Tcb.block_flags.any as ⟨flags, _⟩
  simp only [lift, Aeneas.Std.bind_ok]
  refine WP.spec_bind (hxf _ _ _ _ s1 a hd e badge _ thread hdT ht h1 hB1 hX1 hS1 hSg1 (hU.ksb k1) g1) ?_
  rintro s2 ⟨h2, hB2, hX2, hS2, hSg2, ⟨ea2, ec2, ei2, ecs2, f2, o2, -⟩, g2⟩
  refine WP.spec_bind (WP.spec_and (endpoint.unblock_sporadic.all s2 hd h2 hB2 hX2 hS2 hSg2 hdT)
    (endpoint.unblock_sporadic.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s2 hd h2 hX2 hS2 hdT)) ?_
  rintro s3 ⟨⟨h3, hB3, hX3, hS3, hSg3, ea3, ec3, ei3, f3, r3⟩, F3⟩
  have g3 : XG st T Cs Ω H Sg Scs Z P3Ok s3 := g2.foot F3
  step with obj.Tcb.fault_type.any as ⟨ftype, _⟩
  have F : ∀ y ∈ T, ∀ K : U64, 3328 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
      L.mem s3 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K h0 hK hK8 h1 h2' => (f3 y hy K hK hK8).trans ((f2 y hy K h0 hK hK8).trans (f1 y hy K hK hK8 h1 h2'))
  have st3 : ∀ y ∈ T, L.mem s3 (stA y) = L.mem s (stA y) := fun y hy => by
    rw [stA_eq]; exact F y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)
  have ea : L.actionW s3 = L.actionW s := ea3.trans (ea2.trans ea1)
  have ei : L.idleW s3 = L.idleW s := ei3.trans (ei2.trans ei1)
  have hds3 : L.mem s3 (stA hd) = sched.TS_BLOCKED_ON_SEND := (st3 hd hdT).trans hds
  obtain ⟨dq, dr, da⟩ := blocked_out h3 hdT (by rw [hds3]; exact blocked_not_runnable (Or.inl rfl))
  have hXc : ExcT {y | y ∈ (∅ : Set U64) ∨ y = hd} hd := fun y hy => by simpa using hy
  have hx3 : hd ∈ {y | y ∈ (∅ : Set U64) ∨ y = hd} := Or.inr rfl
  have rt3 : ∀ r ∈ Rp, L.mem s3 (rTcbA r) = L.mem s (rTcbA r) := fun r hr0 =>
    (r3 r hr0).trans ((o2 r hr0).trans (o1 _ (hSg.sub _ (hX.1.tcbW hr0))))
  have sc3 : L.mem s3 (scA hd) = L.mem s (scA hd) := by
    rw [scA_eq]; exact F hd hdT _ (by simp) (by simp) (by simp) (by simp) (by simp)
  have hdA : L.mem s3 (scA hd) ≠ 0#u64 → L.mem s3 (scA hd) ∈ Ac := fun h0 => by
    rw [sc3] at h0 ⊢
    exact hB.sact hd hdT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [hds]; exact Or.inl rfl)))))))
      h0
  have E1 : ∀ cd : Bool, reply ≠ 0#u64 → ipc.reply_push st ar s3 a hd thread reply cd ⦃ s' _ =>
      XG st T Cs Ω H Sg Scs Z P3Ok s' ⦄ := fun cd h0 =>
    WP.spec_mono (ipc.reply_push.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) hA s3 a hd thread reply cd h3 hXc
      (Or.inl hx3) hB3 hX3 hS3 hSg3 hdT dq dr da
      (by rw [ei]; exact hdi) (by rw [hds3]; exact send_ne) (hr' h0).1 h0 (by rw [rt3 _ (hr' h0).1]; exact (hr' h0).2)
      ht hdA)
      fun r hh => by obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at hh ⊢; exact g3.footD hh
  have E1' : reply ≠ 0#u64 → (do
      let i3 ← obj.Tcb.sc st hd s3
      let can_donate ← if (i3 != 0#u64) = true then ok (ftype != fl4_abi.consts.fault.Timeout) else ok false
      ipc.reply_push st ar s3 a hd thread reply can_donate) ⦃ s' _ => XG st T Cs Ω H Sg Scs Z P3Ok s' ⦄ := by
    intro h0
    step with obj.Tcb.sc.spec as ⟨i3, _⟩
    split <;> (try simp only [Aeneas.Std.bind_ok]) <;> exact E1 _ h0
  have E2 : (do
      let s4 ← sched.set_thread_state st s3 hd sched.TS_INACTIVE
      ok (s4, a)) ⦃ s' _ => XG st T Cs Ω H Sg Scs Z P3Ok s' ⦄ := by
    refine WP.spec_bind (sched.set_thread_state.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s3 hd _ h3 hdT)
      fun s4 f4 => ?_
    exact (WP.spec_ok _).2 (g3.foot f4)
  have E3 : (do
      let s4 ← sched.set_thread_state st s3 hd sched.TS_RUNNING
      let s5 ← sched.possible_switch_to st s4 hd
      ok (s5, a)) ⦃ s' _ => XG st T Cs Ω H Sg Scs Z P3Ok s' ⦄ := by
    refine WP.spec_bind (WP.spec_and (sts_all s3 hd _ Q R h3 hB3 hX3 hS3 hSg3 hdT not_blocked_running running_ne
      (Or.inl hx3) (hX3.noref (h3.tcbs _ hdT) (by rw [hds3]; exact send_ne.1) (by rw [hds3]; exact send_ne.2))
      ⟨fun _ _ _ _ _ => runnable_running, fun _ _ _ => runnable_running,
        fun _ => runnable_running⟩)
      (sched.set_thread_state.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s3 hd _ h3 hdT)) fun s4 hh => ?_
    obtain ⟨⟨h4, -⟩, f4⟩ := hh
    have h4' := h4.congrX empty_congr'
    refine WP.spec_bind (sched.possible_switch_to.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s4 hd h4' hdT)
      fun s5 f5 => ?_
    exact (WP.spec_ok _).2 ((g3.foot f4).foot f5)
  repeat' split
  all_goals first
    | exact E2
    | exact E3
    | (rename_i hh; exact E1' (by simpa using hh))

set_option maxHeartbeats 4000000 in
/-- **`receive_ipc` keeps `XG`** (under `receive_ipc.ipc`'s hypotheses). -/
theorem endpoint.receive_ipc.xg (hA : P0.ArchTotal ar) {U : Set U64}
    (hxf : XferOK st ar T Cs Ω H Sg Rp Scs Nt Z U (XG st T Cs Ω H Sg Scs Z P3Ok)) (s : S) (a : A) (t : U64)
    (cap : capability.Cap) (blocking : Bool)
    (reply_cap : capability.Cap) (e : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hU : UserOK st T Cs Ω H U s)
    (hc : CanBlock st T Ac s t)
    (hptr : capability.Cap.ptr cap = ok e) (hH : H e = some .ep)
    (hcap : ∀ p g, reply_cap = .Reply p g → p ∈ Rp)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) :
    endpoint.receive_ipc st ar s a t cap blocking reply_cap ⦃ s' _ => XG st T Cs Ω H Sg Scs Z P3Ok s' ⦄ := by
  unfold endpoint.receive_ipc
  rw [hptr]
  simp only [Aeneas.Std.bind_ok]
  refine WP.spec_bind (WP.spec_and (endpoint.take_reply.inv ar s a t reply_cap Q R h hB hX hS hSg hc hcap)
    (endpoint.take_reply.kw (Sg := Sg) (Scs := Scs) (Z := Z) ar s a t reply_cap h hX hSg hcap)) ?_
  rintro ⟨reply, s1, a1⟩ ⟨⟨h1, hB1, hX1, hS1, hSg1, hc1, hi1, hr1, kb1, -⟩, F1⟩
  have g1 : XG st T Cs Ω H Sg Scs Z P3Ok s1 := hG.foot F1
  have hidle := hc.ni
  try simp only [WP.uncurry'_pair]
  have ht := hc.mem
  -- the end on the endpoint
  have tail : ∀ (s2 : S) (a2 : A) (Q2 : U64 → U64 → List U64) (R2 : U64 → List U64),
      SchedQueuesInv st T Cs Ω H s2 Q2 R2 → BoundInv st T Ac s2 → XInv st T Cs Ω Sg Rp Scs Nt Z s2 →
      SCsOK st T Ω Sg Scs Z Ac s2 → SgOK st Ω Sg s2 → CanBlock st T Ac s2 t →
      (reply ≠ 0#u64 → reply ∈ Rp ∧ (L.mem s2 (rTcbA reply) = 0#u64 ∨ L.mem s2 (rTcbA reply) = t)) →
      L.ksb s2 = L.ksb s → XG st T Cs Ω H Sg Scs Z P3Ok s2 →
      (do
        let st0 ← obj.Ep.state st e s2
        if st0 = obj.EP_IDLE then do
          let s3 ← endpoint.wait_for_sender st s2 t e blocking reply
          ok (s3, a2)
        else if st0 = obj.EP_RECV then do
          let s3 ← endpoint.wait_for_sender st s2 t e blocking reply
          ok (s3, a2)
        else endpoint.receive_from_sender st ar s2 a2 t e reply) ⦃ s' _ =>
          XG st T Cs Ω H Sg Scs Z P3Ok s' ⦄ := by
    intro s2 a2 Q2 R2 h2 hB2 hX2 hS2 hSg2 hc2 hr2 kb2 g2
    have W : (do
        let s3 ← endpoint.wait_for_sender st s2 t e blocking reply
        ok (s3, a2)) ⦃ s' _ => XG st T Cs Ω H Sg Scs Z P3Ok s' ⦄ :=
      WP.spec_bind (endpoint.wait_for_sender.kw (Ac := Ac) s2 t e blocking reply Q2 R2 h2 hX2 hSg2 ht (fun _ => hc2)
        hH (fun hn => (hr2 hn).1)) fun s3 f3 => (WP.spec_ok _).2 (g2.foot f3)
    step with obj.Ep.state.spec as ⟨v, hv⟩
    split
    · exact W
    · split
      · exact W
      · rename_i h01 h02
        exact endpoint.receive_from_sender.xg hA hxf s2 a2 t e reply Q2 R2 h2 hB2 hX2 hS2 hSg2 (hU.ksb kb2) hc2 hH
          ⟨fun e0 => h01 (by rw [hv, e0, ep_idle_val]), fun e0 => h02 (by rw [hv, e0, ep_recv_val'])⟩ hr2 g2
  -- the bound notification's SC
  have mid : ∀ (i : U64), (if blocking then notification.maybe_return_sched_context st s1 i t else ok s1)
      ⦃ s2 => ∃ Q2 R2, SchedQueuesInv st T Cs Ω H s2 Q2 R2 ∧ BoundInv st T Ac s2 ∧
        XInv st T Cs Ω Sg Rp Scs Nt Z s2 ∧ SCsOK st T Ω Sg Scs Z Ac s2 ∧ SgOK st Ω Sg s2 ∧ CanBlock st T Ac s2 t ∧
        (reply ≠ 0#u64 → reply ∈ Rp ∧ (L.mem s2 (rTcbA reply) = 0#u64 ∨ L.mem s2 (rTcbA reply) = t)) ∧
        L.ksb s2 = L.ksb s ∧ XG st T Cs Ω H Sg Scs Z P3Ok s2 ⦄ := by
    intro i
    split
    · refine WP.spec_mono (WP.spec_and (notification.maybe_return_sched_context.inv s1 i t Q R h1 hB1 hX1 hS1 hSg1 ht
        ⟨hc1.nq, hc1.nr, hc1.na⟩ (by rw [hi1]; exact hidle))
        (notification.maybe_return_sched_context.kw s1 i t Q R h1 hB1 hX1 hS1 hSg1 ht
        ⟨hc1.nq, hc1.nr, hc1.na⟩ (by rw [hi1]; exact hidle))) fun s2 hh' => ?_
      obtain ⟨hh, F2⟩ := hh'
      obtain ⟨⟨Q2, R2, h2⟩, hB2, hX2, hS2, hSg2, q2, st2, na2, ii2, rt2, sa2, ks2, sc2⟩ := hh
      refine ⟨Q2, R2, h2, hB2, hX2, hS2, hSg2, hc1.mrsc q2 st2 na2 ii2 sc2, fun hn => ?_, ks2.trans kb1, g1.foot F2⟩
      obtain ⟨r1, r2⟩ := hr1 hn
      rw [rt2 _ r1]; exact ⟨r1, r2⟩
    · exact (WP.spec_ok _).2 ⟨Q, R, h1, hB1, hX1, hS1, hSg1, hc1, hr1, kb1, g1⟩
  step with obj.Tcb.bound_ntfn.val as ⟨i, ei⟩
  split
  · rename_i hi0
    step with obj.Ntfn.state.spec as ⟨v1, hv1⟩
    split
    · have hn0 : L.mem s1 (boundA t) ≠ 0#u64 := by rw [← ei]; simpa using hi0
      obtain ⟨hn1, hn2, hn3⟩ := BoundNtfnOK.of_inv hNt ht hX1 hS1 hSg1 hn0
      subst ei
      refine notification.complete_signal.xg hA s1 a1 _ t Q R h1 hB1 hX1 hS1 hSg1 ht hc1.nq hc1.nr hc1.na
        hc1.ni hn1 hn2 hn3 (fun _ h0 hS' => ?_) g1
      exfalso
      rcases hS' with e | e | e | e | ⟨e1, e2⟩ | e
      · exact e hc1.nq
      · exact e hc1.nr
      · exact hc1.na e
      · exact hc1.ni e
      · exact hB1.resume e1 (by rw [e2]; exact h0)
      · rcases e with e | e
        · exact hc1.nb e
        · exact hc1.nrp e
    · refine WP.spec_bind (mid i) ?_
      rintro s2 ⟨Q2, R2, h2, hB2, hX2, hS2, hSg2, hc2, hr2, kb2, g2⟩
      exact tail s2 a1 Q2 R2 h2 hB2 hX2 hS2 hSg2 hc2 hr2 kb2 g2
  · try simp only [Aeneas.Std.bind_ok]
    exact tail s1 a1 Q R h1 hB1 hX1 hS1 hSg1 hc1 hr1 kb1 g1

/-! ## `handle_fault` and `handle_recv` -/

/-- **`handle_fault` keeps `XG`** (under `handle_fault.bxi`'s hypotheses, with
`XferOK`'s guard `XG`): the fault IPC by `send_ipc.xg`, the no-handler case
is a `KW` step. -/
theorem faults.handle_fault.xg (hA : P0.ArchTotal ar) {U : Set U64}
    (hxf : XferOK st ar T Cs Ω H Sg Rp Scs Nt Z U (XG st T Cs Ω H Sg Scs Z P3Ok)) (s : S) (a : A) (t : obj.Tcb)
    (f : error.Fault)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hU : UserOK st T Cs Ω H U s) (hc : CanBlock st T Ac s t)
    (hcap : obj.Tcb.slot t layout.tcb.SLOT_FAULT_HANDLER ⦃ sl =>
      obj.Slot.cap st sl s ⦃ c => CapTyped H Rp Nt c ⦄ ⦄) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) :
    faults.handle_fault st ar s a t f ⦃ s' _ => XG st T Cs Ω H Sg Scs Z P3Ok s' ⦄ := by
  have ht := hc.mem
  unfold faults.handle_fault
  refine WP.spec_bind hcap fun sl hsl => ?_
  refine WP.spec_bind hsl fun c hct => ?_
  step with obj.Tcb.sc.spec as ⟨i, ei⟩
  unfold faults.send_fault_ipc
  refine WP.spec_bind (Pₘ := fun r : Bool × S × A => XG st T Cs Ω H Sg Scs Z P3Ok r.2.1 ∧
      (r.1 = false → r.2.1 = s)) ?_ ?_
  · split
    all_goals first | exact (WP.spec_ok _).2 ⟨hG, fun _ => rfl⟩ | skip
    rename_i p b x y g gr
    have hpH := hct.1 p b x y g gr rfl
    refine WP.spec_bind (WP.spec_and (WP.spec_and (faults.set_fault.blk s t f h ht hU hc)
      (faults.set_fault.sc s t f h.1.choose_spec.choose_spec.tcbs ht))
      (faults.set_fault.kw (Cs := Cs) (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s t f
        h.1.choose_spec.choose_spec.tcbs ht)) ?_
    rintro s1 ⟨⟨⟨h1, hU1, hc1⟩, sc1⟩, F1⟩
    obtain ⟨⟨Q1, R1, q1⟩, hB1, hX1, hS1, hSg1⟩ := h1
    refine WP.spec_bind (endpoint.send_ipc.xg hA hxf s1 a true false b g gr (i != 0#u64) t p Q1 R1 q1 hB1 hX1
      hS1 hSg1 hU1 hc1 (fun e => ?_) hpH (hG.foot F1)) ?_
    · have hi : i ≠ 0#u64 := by simpa using e
      rw [sc1, ← ei]; exact hi
    rintro ⟨s2, a1⟩ h2
    exact (WP.spec_ok _).2 ⟨by simpa using h2, fun e => by cases e⟩
  · rintro ⟨b, s2, a2⟩ ⟨g2, e2⟩
    try simp only [WP.uncurry'_pair] at e2
    simp only [uncurry_apply_pair]
    split
    · exact (WP.spec_ok _).2 g2
    · rename_i hb
      have e2' : s2 = s := e2 (by simpa using hb)
      obtain ⟨⟨Q3, R3, q3⟩, -, -, -, -⟩ := h
      rw [e2'] at g2 ⊢
      refine WP.spec_bind (sched.set_thread_state.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s t _ q3 ht) ?_
      intro s4 f4
      exact (WP.spec_ok _).2 (g2.foot f4)

/-- **`handle_recv` keeps `XG`** (under `handle_recv.bxi`'s hypotheses, with
the cap faults keeping `XG`, `hfault`). -/
theorem syscall.handle_recv.xg (hA : P0.ArchTotal ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) {U : Set U64}
    (hxf : XferOK st ar T Cs Ω H Sg Rp Scs Nt Z U (XG st T Cs Ω H Sg Scs Z P3Ok))
    (s : S) (a : A) (blk rep : Bool) (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hU : UserOK st T Cs Ω H U s) (hc : CanBlock st T Ac s (L.curW s))
    (hlk : ∀ cptr, cspace.lookup_cap st s (L.curW s) cptr ⦃ r => ∀ c, r = .Ok c → CapTyped H Rp Nt c ⦄)
    (h3 : ∀ n ∈ Nt, L.epState s n ≠ 3#u64)
    (hfault : ∀ (f : error.Fault),
      faults.handle_fault st ar s a (L.curW s) f ⦃ s' _ => XG st T Cs Ω H Sg Scs Z P3Ok s' ⦄)
    (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) :
    syscall.handle_recv st ar s a blk rep ⦃ s' _ => XG st T Cs Ω H Sg Scs Z P3Ok s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hSg, hS⟩ := h
  have CF : ∀ cptr lf, syscall.cap_fault_recv st ar s a cptr lf ⦃ s' _ =>
      XG st T Cs Ω H Sg Scs Z P3Ok s' ⦄ := fun cptr lf => by
    unfold syscall.cap_fault_recv
    step with sched.cur_thread.spec as ⟨t1, e1⟩
    have e1' : t1 = L.curW s := e1
    subst e1'
    exact hfault _
  have ok0 : (ok (s, a) : Result (S × A)) ⦃ s' _ => XG st T Cs Ω H Sg Scs Z P3Ok s' ⦄ := (WP.spec_ok _).2 hG
  have RI : ∀ (c rc : capability.Cap) (e : U64), capability.Cap.ptr c = ok e → H e = some .ep →
      (∀ p g, rc = .Reply p g → p ∈ Rp) →
      endpoint.receive_ipc st ar s a (L.curW s) c blk rc ⦃ s' _ => XG st T Cs Ω H Sg Scs Z P3Ok s' ⦄ :=
    fun c rc e hp hH hr =>
      endpoint.receive_ipc.xg hA hxf s a _ c blk rc e Q R h0 hB hX hS hSg hU hc hp hH hr hNt hG
  have RS : ∀ n, n ∈ Nt → H n = some .ntfn → notification.receive_signal st ar s a (L.curW s) n blk ⦃ s' _ =>
      XG st T Cs Ω H Sg Scs Z P3Ok s' ⦄ := fun n hn hH =>
    notification.receive_signal.xg hA s a _ n blk Q R h0 hB hX hS hSg hc hn hH (h3 n hn) hG
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

end

end Fl4Proofs.P1
