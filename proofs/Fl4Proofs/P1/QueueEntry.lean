/-
P1: the kernel entries `handle_syscall` and `handle_interrupt_entry` keep
`EntryInv` (established by `schedule`, `sched.schedule.entry`).

Inside an entry, before the final `schedule`, the current SC word is not
switched.  The budget check at the entry (`budget_ok`, `check_budget`) needs
the current SC active and the current thread's (`EntryInv`); after an
invocation the preemption point (`mcs_preemption_point.all`) needs `HCur`:
the current SC is active, or the current thread has no other SC.  `HCur` is
preserved across an invocation (`HCur.step`) given the invocation's
`CurStep` (it keeps the current SC and thread words, and the current
thread's `SC` field is kept or cleared unless the current SC stays active;
an SC deletion takes the current SC out of the active set only with the
current thread unbound from it, `CurStep.del`).

The invocations themselves (`handle_invocation`, `handle_recv`,
`handle_yield`, the fault, timeout and interrupt handlers, the debug
syscalls, `activate_thread`) are the named hypotheses `EntryHyps`, one per
family, stated with the invariants of P1 (`BXI`, with a possibly smaller
active set), for the P3 decode theorems to discharge.
-/
import Fl4Proofs.P1.QueueReplyPop
import Fl4Proofs.P1.QueueFire
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}

/-! ## `hcur` -/

/-- Inside a kernel entry: the current SC is active, or the current thread
has no other SC than it (it may have lost its SC, e.g. when the SC was
deleted). -/
def HCur (st : machine.Store S) [L : LawfulStore st] (Ac : Set U64) (s : S) : Prop :=
  L.cscW s ∈ Ac ∨ L.mem s (scA (L.curW s)) = L.cscW s ∨ L.mem s (scA (L.curW s)) = 0#u64

/-- What an invocation does to the current SC and thread: the current SC and
current thread words are kept (only `schedule` switches them); if the
current SC leaves the active set (`Ac` to `Ac'`, an SC deletion), the
current thread's `SC` field is cleared or is that SC; otherwise the field is
kept or cleared, unless the current SC stays active. -/
structure CurStep (st : machine.Store S) [L : LawfulStore st] (Ac Ac' : Set U64) (s s' : S) : Prop where
  csc : L.cscW s' = L.cscW s
  cur : L.curW s' = L.curW s
  del : L.cscW s ∈ Ac → L.cscW s ∉ Ac' →
    L.mem s' (scA (L.curW s)) = 0#u64 ∨ L.mem s' (scA (L.curW s)) = L.cscW s
  sc : L.mem s' (scA (L.curW s)) = L.mem s (scA (L.curW s)) ∨ L.mem s' (scA (L.curW s)) = 0#u64 ∨
    L.cscW s ∈ Ac'

/-- **`hcur` is preserved across an invocation.** -/
theorem HCur.step {Ac Ac' : Set U64} {s s' : S} (h : HCur st Ac s) (k : CurStep st Ac Ac' s s') :
    HCur st Ac' s' := by
  unfold HCur
  rw [k.csc, k.cur]
  by_cases h1 : L.cscW s ∈ Ac'
  · exact Or.inl h1
  right
  by_cases h2 : L.cscW s ∈ Ac
  · rcases k.del h2 h1 with e | e
    · exact Or.inr e
    · exact Or.inl e
  · rcases h with h | h | h
    · exact absurd h h2
    · rcases k.sc with e | e | e
      · exact Or.inl (e.trans h)
      · exact Or.inr e
      · exact absurd e h1
    · rcases k.sc with e | e | e
      · exact Or.inr (e.trans h)
      · exact Or.inr e
      · exact absurd e h1

theorem HCur.of_mem {Ac : Set U64} {s : S} (h : L.cscW s ∈ Ac) : HCur st Ac s := Or.inl h

theorem CurStep.refl (Ac : Set U64) (s : S) : CurStep st Ac Ac s s :=
  ⟨rfl, rfl, fun h1 h2 => absurd h1 h2, Or.inl rfl⟩

/-- A step that keeps the active set, the current SC and thread words and the
current thread's `SC` field. -/
theorem CurStep.keep {Ac : Set U64} {s s' : S} (hcs : L.cscW s' = L.cscW s) (hcu : L.curW s' = L.curW s)
    (hsc : L.mem s' (scA (L.curW s)) = L.mem s (scA (L.curW s))) : CurStep st Ac Ac s s' :=
  ⟨hcs, hcu, fun h1 h2 => absurd h1 h2, Or.inl hsc⟩

/-- A step that keeps the active set and may clear the current thread's `SC`
field. -/
theorem CurStep.clear {Ac : Set U64} {s s' : S} (hcs : L.cscW s' = L.cscW s) (hcu : L.curW s' = L.curW s)
    (hsc : L.mem s' (scA (L.curW s)) = L.mem s (scA (L.curW s)) ∨ L.mem s' (scA (L.curW s)) = 0#u64) :
    CurStep st Ac Ac s s' :=
  ⟨hcs, hcu, fun h1 h2 => absurd h1 h2, by rcases hsc with e | e; exacts [Or.inl e, Or.inr (Or.inl e)]⟩

/-- An SC deletion (`fin_sc.blk`: the active set loses `p`, the thread bound
to `p` is unbound), when the current thread's SC (if any) is the current SC. -/
theorem CurStep.ofDel {Ac : Set U64} {s s' : S} {p : U64} (hcs : L.cscW s' = L.cscW s)
    (hcu : L.curW s' = L.curW s)
    (hcsc : L.mem s (scA (L.curW s)) ≠ 0#u64 → L.cscW s = L.mem s (scA (L.curW s)))
    (hsc : L.mem s' (scA (L.curW s)) = L.mem s (scA (L.curW s)) ∨
      (L.mem s (scA (L.curW s)) = p ∧ L.mem s' (scA (L.curW s)) = 0#u64)) :
    CurStep st Ac (Ac \ {p}) s s' := by
  refine ⟨hcs, hcu, fun h1 h2 => ?_, ?_⟩
  · rcases hsc with e | ⟨-, e⟩
    · rw [e]
      by_cases h0 : L.mem s (scA (L.curW s)) = 0#u64
      · exact Or.inl h0
      · exact Or.inr (hcsc h0).symm
    · exact Or.inl e
  · rcases hsc with e | ⟨-, e⟩
    · exact Or.inl e
    · exact Or.inr (Or.inl e)

/-! ## Steps that keep the current SC -/

theorem BXI.blk {Ac : Set U64} {s : S} (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2, h.2.2.2.1⟩

theorem BlkOK.bxi {Ac : Set U64} {s : S} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2, h.2.2.2.1⟩

theorem EntryInv.bxi {Ac : Set U64} {s : S} (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1.sg, h.2.2.2.1⟩

/-- A write to a current-node word other than the scheduler's. -/
theorem nodew_bxc {Ac : Set U64} {s : S} {o v : U64} (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ho : LowFree o.val) (h24 : o.val ≠ 24) (hto : o.val ≠ 88 ∧ o.val ≠ 104 ∧ o.val ≠ 112) :
    BXC st T Cs Ω H Sg Rp Scs Nt Z Ac s (L.wr s (L.nodeAt s (L.cpu s) o) v) ∧
      ANI st s (L.wr s (L.nodeAt s (L.cpu s) o) v) ∧
      (∀ y ∈ T, L.mem (L.wr s (L.nodeAt s (L.cpu s) o) v) (scA y) = L.mem s (scA y)) := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hSg, hS⟩ := h
  obtain ⟨h3, hB3, hX3, hSg3, ea, ec, ecs3, f3⟩ := node_bx (o := o) (v := v) h0 hB hX hSg ho h24 hto
  have hN := h0.nodes _ h0.cur
  obtain ⟨-, hc⟩ := objs_omega hX.1 hS.sub
  have ho' := ho
  unfold LowFree at ho'
  refine ⟨⟨⟨⟨Q, R, h3⟩, hB3, hX3, hSg3, SCsOK.wr h0 hS hX (nodeAt_aligned hN (by omega) (by omega))
    (fun y hy => ?_) ?_ (fun c hc' => ?_)
    (fun c hc' => out_ne_node (h0.omega _ (spor_omega hX.1 hc')) h0.cur hN (by omega))
    (fun c hc' e => absurd e (out_ne_node (h0.omega _ (hS.sub _ (hX.1.repW c hc'))) h0.cur hN (by omega)))⟩, ecs3⟩,
    ⟨ea, ?_, ec⟩, fun y hy => (f3 y hy).1⟩
  · rw [scA_eq]; exact fun e => node_ne_field hN (by omega) hy (h0.tcbs y hy) (by simp) (UScalar.eq_of_val_eq e)
  · intro e
    simp only [LawfulStore.nodeA] at e
    rw [nodeAt_val hN (by omega), nodeAt_val hN (by simp [layout.node.CUR_SC])] at e
    simp [layout.node.CUR_SC] at e; omega
  · obtain ⟨-, -, c3, c4, c5⟩ := hc c hc'
    exact ⟨out_ne_node (h0.omega _ c3) h0.cur hN (by omega), out_ne_node (h0.omega _ c4) h0.cur hN (by omega),
      out_ne_node (h0.omega _ c5) h0.cur hN (by omega)⟩
  · unfold LawfulStore.idleW
    exact rd_cur_node h0 (by omega) (by omega) (by rw [idle8]; omega) (by rw [idle8]) (by rw [idle8]; omega)

variable {A : Type _} {ar : machine.Arch A}

/-- seL4 `updateTimestamp`: the current node's time and `CONSUMED` words. -/
theorem sched.update_timestamp.bxc (hA : P0.ArchTotal ar) {Ac : Set U64} (s : S) (a : A)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    sched.update_timestamp st ar s a ⦃ s' _ => BXC st T Cs Ω H Sg Rp Scs Nt Z Ac s s' ∧ ANI st s s' ∧
      ∀ y ∈ T, L.mem s' (scA y) = L.mem s (scA y) ⦄ := by
  unfold sched.update_timestamp
  step with sched.cur_time.spec as ⟨prev⟩
  refine WP.spec_bind (hA.now a) ?_
  rintro ⟨now, a1⟩ -
  try simp only [WP.uncurry'_pair]
  step with LawfulStore.cur_cpu_spec as ⟨c, ec⟩
  step with obj.node_set.spec as ⟨s1, e1⟩
  subst ec e1
  obtain ⟨⟨k1, c1⟩, n1, f1⟩ := nodew_bxc (o := layout.node.CUR_TIME) (v := now) h
    (by simp [layout.node.CUR_TIME, LowFree]) (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
  step as ⟨used, _⟩
  step with sched.consumed.spec as ⟨i⟩
  step as ⟨total, _⟩
  step with sched.set_consumed.spec as ⟨s2, e2⟩
  rw [show ∀ s0 : S, L.nodeA s0 layout.node.CONSUMED = L.nodeAt s0 (L.cpu s0) layout.node.CONSUMED from
    fun _ => rfl] at e2
  subst e2
  obtain ⟨⟨k2, c2⟩, n2, f2⟩ := nodew_bxc (o := layout.node.CONSUMED) (v := total) k1
    (by simp [layout.node.CONSUMED, LowFree]) (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
  simp only [layout.NUM_DOMAINS, fl4_abi.config.NUM_DOMAINS]
  have hnd : ¬ ((1#u64) > (1#u64)) := by simp
  simp only [hnd, ↓reduceIte, WP.spec_ok, WP.uncurry'_pair]
  exact ⟨⟨k2, c2.trans c1⟩, n1.trans n2, fun y hy => (f2 y hy).trans (f1 y hy)⟩

/-- `update_timestamp` at a kernel entry: the facts `check_budget` needs. -/
theorem sched.update_timestamp.entry (hA : P0.ArchTotal ar) {Ac : Set U64} (s : S) (a : A)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    sched.update_timestamp st ar s a ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ L.cscW s' = L.cscW s ∧
      L.cscW s' ∈ Ac ∧ L.actionW s' ≠ L.curW s' ∧
      (L.mem s' (scA (L.curW s')) ≠ 0#u64 → L.cscW s' = L.mem s' (scA (L.curW s'))) ⦄ := by
  have hcT : L.curW s ∈ T := h.1.choose_spec.choose_spec.curT
  have hb := EntryInv.bxi h
  obtain ⟨-, -, -, -, -, hcA, hna, hcsc⟩ := h
  refine WP.spec_mono (sched.update_timestamp.bxc hA s a hb) ?_
  rintro ⟨s1, a1⟩ ⟨⟨k1, c1⟩, n1, f1⟩
  simp only [WP.uncurry'_pair] at *
  refine ⟨k1, c1, by rw [c1]; exact hcA, by rw [n1.1, n1.2.2]; exact hna, ?_⟩
  rw [n1.2.2, f1 _ hcT, c1]; exact hcsc

/-! ## The invocation families -/

/-- The hypotheses of the kernel-entry composites, one per family of kernel
operation not proved in P1, stated with P1's invariants.  An invocation may
shrink the active set (`Ac'`, an SC deletion); `handle_invocation` reports
its `CurStep` (for `HCur.step`) and, when it was preempted, what the
preemption point needs. -/
structure EntryHyps (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A) (T Cs Ω : Set U64)
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) : Prop where
  /-- Timeout faults (`handle_timeout`, from `check_budget`'s `end_timeslice`). -/
  tmo : ∀ (Ac : Set U64) (s : S) (a : A) (t : obj.Tcb) (f : error.Fault) (Q : U64 → U64 → List U64)
    (R : U64 → List U64), SchedQueuesInv st T Cs Ω H s Q R → BoundInv st T Ac s →
    XInv st T Cs Ω Sg Rp Scs Nt Z s → SgOK st Ω Sg s → SCsOK st T Ω Sg Scs Z Ac s →
    faults.handle_timeout st ar s a t f ⦃ s' _ => BXC st T Cs Ω H Sg Rp Scs Nt Z Ac s s' ⦄
  /-- The cap invocations (`handle_invocation`: lookup, decode, perform, reply). -/
  inv : ∀ (Ac : Set U64) (s : S) (a : A) (call blk don fp : Bool) (cptr : U64),
    BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → L.cscW s ∈ Ac →
    syscall.handle_invocation st ar s a call blk don fp cptr ⦃ r s' _ => ∃ Ac',
      BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ∧ CurStep st Ac Ac' s s' ∧
      (∀ e, r = .Err e → L.actionW s' ≠ L.curW s' ∧
        (L.mem s' (scA (L.curW s')) ≠ 0#u64 → L.cscW s' = L.mem s' (scA (L.curW s')))) ⦄
  /-- Receives (`handle_recv`). -/
  recv : ∀ (Ac : Set U64) (s : S) (a : A) (blk rep : Bool), BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    syscall.handle_recv st ar s a blk rep ⦃ s' _ => ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄
  /-- `handle_yield`. -/
  yield : ∀ (Ac : Set U64) (s : S) (a : A), BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → L.cscW s ∈ Ac →
    syscall.handle_yield st ar s a ⦃ s' _ => ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄
  /-- Faults (`handle_fault`). -/
  fault : ∀ (Ac : Set U64) (s : S) (a : A) (t : obj.Tcb) (f : error.Fault), BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    faults.handle_fault st ar s a t f ⦃ s' _ => ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄
  /-- Interrupts (`handle_interrupt`). -/
  irq : ∀ (Ac : Set U64) (s : S) (a : A) (i : U64), BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    interrupt.handle_interrupt st ar s a i ⦃ s' _ => ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄
  /-- The debug syscalls (`debug_syscall`, which return to the thread directly). -/
  debug : ∀ (Ac : Set U64) (s : S) (a : A) (t : obj.Tcb) (n : I64), EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    syscall.debug_syscall st ar s a t n ⦃ _ s' _ => ∃ Ac', EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄
  /-- `activate_thread`, after `schedule`. -/
  act : ∀ (Ac : Set U64) (s : S) (a : A), EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    sched.activate_thread st ar s a ⦃ s' _ => EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄

/-! ## The composites -/

/-- `budget_ok` at a kernel entry keeps the current SC. -/
theorem syscall.budget_ok.bxc (hA : P0.ArchTotal ar) (E : EntryHyps st ar T Cs Ω H Sg Rp Scs Nt Z)
    {Ac : Set U64} (s : S) (a : A) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    syscall.budget_ok st ar s a ⦃ _ s' _ => BXC st T Cs Ω H Sg Rp Scs Nt Z Ac s s' ⦄ := by
  unfold syscall.budget_ok
  refine WP.spec_bind (sched.update_timestamp.entry hA s a h) ?_
  rintro ⟨s1, a1⟩ ⟨⟨⟨Q1, R1, h1⟩, hB1, hX1, hSg1, hS1⟩, c1, hcA, hna, hcsc⟩
  try simp only [WP.uncurry'_pair]
  refine WP.spec_mono (sched.check_budget_restart.all hA s1 a1 Q1 R1 h1 hB1 hX1 hSg1 hS1 hcsc hna hcA
    (E.tmo Ac)) ?_
  rintro ⟨r, s2, a2⟩ ⟨k2, c2⟩
  exact ⟨k2, c2.trans c1⟩

/-- `finish`: `schedule` establishes `EntryInv`, `activate_thread` keeps it. -/
theorem syscall.finish.entry (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (E : EntryHyps st ar T Cs Ω H Sg Rp Scs Nt Z) {Ac : Set U64} (s : S) (a : A)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    syscall.finish st ar s a ⦃ s' _ => ∃ Ac', EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄ := by
  unfold syscall.finish
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hSg, hS⟩ := h
  refine WP.spec_bind (sched.schedule.entry hA hNt s a Q R h0 hB hS hX hSg) ?_
  rintro ⟨s1, a1⟩ h1
  try simp only [WP.uncurry'_pair]
  exact WP.spec_mono (E.act Ac s1 a1 h1) fun r hr => ⟨Ac, hr⟩

/-- `after_invocation`: the preemption point of a preempted invocation, with
`HCur`, then a pending interrupt. -/
theorem syscall.after_invocation.bxi (hA : P0.ArchTotal ar) (E : EntryHyps st ar T Cs Ω H Sg Rp Scs Nt Z)
    {Ac : Set U64} (s : S) (a : A) (r : core.result.Result Unit error.Exc)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hc : HCur st Ac s)
    (herr : ∀ e, r = .Err e → L.actionW s ≠ L.curW s ∧
      (L.mem s (scA (L.curW s)) ≠ 0#u64 → L.cscW s = L.mem s (scA (L.curW s)))) :
    syscall.after_invocation st ar s a r ⦃ _ s' _ => ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄ := by
  unfold syscall.after_invocation
  cases r with
  | Ok _ => exact (WP.spec_ok _).2 ⟨Ac, h⟩
  | Err e =>
    obtain ⟨hna, hcsc⟩ := herr e rfl
    obtain ⟨⟨Q, R, h0⟩, hB, hX, hSg, hS⟩ := h
    dsimp only
    refine WP.spec_bind (syscall.mcs_preemption_point.all hA s a Q R h0 hB hX hSg hS hcsc hna hc (E.tmo Ac)) ?_
    rintro ⟨s1, a1⟩ ⟨h1, -⟩
    try simp only [WP.uncurry'_pair]
    refine WP.spec_bind (hA.take_pending_irq a1) ?_
    rintro ⟨irq, a2⟩ -
    try simp only [WP.uncurry'_pair]
    unfold syscall.check_interrupt
    refine WP.spec_bind (Pₘ := fun r : S × A => ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' r.1) ?_ ?_
    · split
      · exact WP.spec_mono (E.irq Ac s1 a2 irq h1) fun r hr => by
          obtain ⟨s', a'⟩ := r; simpa using hr
      · exact (WP.spec_ok _).2 ⟨Ac, h1⟩
    · rintro ⟨s2, a3⟩ h2
      exact (WP.spec_ok _).2 h2

/-- `dispatch_syscall`, after a successful budget check. -/
theorem syscall.dispatch_syscall.bxi (hA : P0.ArchTotal ar) (E : EntryHyps st ar T Cs Ω H Sg Rp Scs Nt Z)
    {Ac : Set U64} (s : S) (a : A) (number : I64) (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hcA : L.cscW s ∈ Ac) :
    syscall.dispatch_syscall st ar s a number ⦃ s' _ => ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄ := by
  have IA : ∀ (call blk don fp : Bool) (cptr : U64),
      syscall.handle_invocation st ar s a call blk don fp cptr ⦃ r s1 a1 =>
        syscall.after_invocation st ar s1 a1 r ⦃ _ s2 _ => ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s2 ⦄ ⦄ :=
    fun call blk don fp cptr => WP.spec_mono (E.inv Ac s a call blk don fp cptr h hcA) fun r hr => by
      obtain ⟨r', s1, a1⟩ := r
      simp only [WP.uncurry'_pair] at hr ⊢
      obtain ⟨Ac1, h1, k1, e1⟩ := hr
      exact syscall.after_invocation.bxi hA E s1 a1 r' h1 ((HCur.of_mem hcA).step k1) e1
  have IR : ∀ (call blk don fp : Bool) (cptr : U64) (b1 b2 : Bool),
      (do
        let (r, s1, a1) ← syscall.handle_invocation st ar s a call blk don fp cptr
        let (b, s2, a2) ← syscall.after_invocation st ar s1 a1 r
        if b then syscall.handle_recv st ar s2 a2 b1 b2 else ok (s2, a2)) ⦃ s' _ =>
          ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄ := by
    intro call blk don fp cptr b1 b2
    refine WP.spec_bind (IA call blk don fp cptr) ?_
    rintro ⟨r, s1, a1⟩ hh
    simp only [WP.uncurry'_pair] at hh ⊢
    refine WP.spec_bind hh ?_
    rintro ⟨b, s2, a2⟩ ⟨Ac2, h2⟩
    try simp only [WP.uncurry'_pair]
    try simp only [uncurry_apply_pair]
    split
    · exact E.recv Ac2 s2 a2 b1 b2 h2
    · exact (WP.spec_ok _).2 ⟨Ac2, h2⟩
  have IS : ∀ (call blk don fp : Bool) (cptr : U64),
      (do
        let (r, s1, a1) ← syscall.handle_invocation st ar s a call blk don fp cptr
        let (_, s2, a2) ← syscall.after_invocation st ar s1 a1 r
        ok (s2, a2)) ⦃ s' _ => ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄ := by
    intro call blk don fp cptr
    refine WP.spec_bind (IA call blk don fp cptr) ?_
    rintro ⟨r, s1, a1⟩ hh
    simp only [WP.uncurry'_pair] at hh ⊢
    refine WP.spec_bind hh ?_
    rintro ⟨b, s2, a2⟩ ⟨Ac2, h2⟩
    exact (WP.spec_ok _).2 ⟨Ac2, h2⟩
  unfold syscall.dispatch_syscall
  step with sched.cur_thread.spec as ⟨t, et⟩
  step with obj.Tcb.reg.spec as ⟨cptr⟩
  step with obj.Tcb.reg.spec as ⟨reply⟩
  by_cases c1 : number = fl4_abi.syscall.SysSend
  · rw [if_pos c1]; exact IS _ _ _ _ _
  rw [if_neg c1]
  by_cases c2 : number = fl4_abi.syscall.SysNBSend
  · rw [if_pos c2]; exact IS _ _ _ _ _
  rw [if_neg c2]
  by_cases c3 : number = fl4_abi.syscall.SysCall
  · rw [if_pos c3]; exact IS _ _ _ _ _
  rw [if_neg c3]
  by_cases c4 : number = fl4_abi.syscall.SysRecv
  · rw [if_pos c4]; exact E.recv Ac s a _ _ h
  rw [if_neg c4]
  by_cases c5 : number = fl4_abi.syscall.SysNBRecv
  · rw [if_pos c5]; exact E.recv Ac s a _ _ h
  rw [if_neg c5]
  by_cases c6 : number = fl4_abi.syscall.SysWait
  · rw [if_pos c6]; exact E.recv Ac s a _ _ h
  rw [if_neg c6]
  by_cases c7 : number = fl4_abi.syscall.SysNBWait
  · rw [if_pos c7]; exact E.recv Ac s a _ _ h
  rw [if_neg c7]
  by_cases c8 : number = fl4_abi.syscall.SysReplyRecv
  · rw [if_pos c8]; exact IR _ _ _ _ _ _ _
  rw [if_neg c8]
  by_cases c9 : number = fl4_abi.syscall.SysNBSendRecv
  · rw [if_pos c9]
    step with obj.Tcb.reg.spec as ⟨dest⟩
    exact IR _ _ _ _ _ _ _
  rw [if_neg c9]
  by_cases c10 : number = fl4_abi.syscall.SysNBSendWait
  · rw [if_pos c10]; exact IR _ _ _ _ _ _ _
  rw [if_neg c10]
  by_cases c11 : number = fl4_abi.syscall.SysYield
  · rw [if_pos c11]; exact E.yield Ac s a h hcA
  rw [if_neg c11]
  exact (WP.spec_ok _).2 ⟨Ac, h⟩

/-- A register write at a kernel entry keeps `EntryInv`. -/
theorem reg_entry {Ac : Set U64} {s : S} {t r v : U64} (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T)
    (hr : r.val < 384) : obj.Tcb.set_reg st t s r v ⦃ s' => EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, -, hcA, hna, hcsc⟩ := h
  refine WP.spec_mono (obj.Tcb.set_reg.wrK s t r v (h0.tcbs t ht) hr) ?_
  rintro s' ⟨K, hK, rfl⟩
  obtain ⟨⟨⟨Q', R', h'⟩, hB', hX', hS', -⟩, -, n⟩ :=
    regW_all (Ac := Ac) (Sg := Sg) (Z := Z) ⟨⟨Q, R, h0⟩, hB, hX, hS, hS.sg⟩ ht (K := K) (v := v)
      (by omega) (by omega) (by omega)
  have f := fr_field (Sg := Sg) h0 hS.sg ht (K := K) (v := v) (by omega) (by omega)
    ⟨by omega, by omega, by omega, by omega, by omega, Or.inl (by omega)⟩
  refine ⟨⟨Q', R', h'⟩, hB', hX', hS', hX'.2.2.tm, by rw [f.csc]; exact hcA, by rw [n.1, n.2.2]; exact hna, ?_⟩
  rw [n.2.2, f.sc (L.curW s) h0.curT, f.csc]; exact hcsc

/-- seL4 `handleUnknownSyscall`'s fault path (`unknown_syscall_fault`). -/
theorem syscall.unknown_syscall_fault.entry (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (E : EntryHyps st ar T Cs Ω H Sg Rp Scs Nt Z) {Ac : Set U64} (s : S) (a : A) (n : U64)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    syscall.unknown_syscall_fault st ar s a n ⦃ s' _ => ∃ Ac', EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄ := by
  unfold syscall.unknown_syscall_fault
  refine WP.spec_bind (syscall.budget_ok.bxc hA E s a h) ?_
  rintro ⟨b, s1, a1⟩ ⟨h1, -⟩
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (Pₘ := fun r : S × A => ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' r.1) ?_ ?_
  · split
    · step with sched.cur_thread.spec as ⟨t, et⟩
      have htT : t ∈ T := by rw [et]; exact h1.1.choose_spec.choose_spec.curT
      simp only [fl4_abi.config.SET_TLS_BASE_SELF, ↓reduceIte]
      step as ⟨i, _⟩
      split
      · step with obj.Tcb.reg.spec as ⟨base⟩
        step with P0.regs.sanitise.p0 as ⟨i1⟩
        refine WP.spec_bind (regW_spec h1.blk htT (r := layout.reg.TLS_BASE)
          (by simp [layout.reg.TLS_BASE, layout.reg.FS_BASE])) ?_
        rintro s3 ⟨h3, -, -⟩
        exact (WP.spec_ok _).2 ⟨Ac, h3.bxi⟩
      · exact WP.spec_mono (E.fault Ac s1 a1 t _ h1) fun r hr => by
          obtain ⟨s', a'⟩ := r; simpa using hr
    · exact (WP.spec_ok _).2 ⟨Ac, h1⟩
  · rintro ⟨s2, a2⟩ ⟨Ac2, h2⟩
    exact syscall.finish.entry hA hNt E s2 a2 h2

/-- seL4 `handleUnknownSyscall`. -/
theorem syscall.handle_unknown_syscall.entry (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (E : EntryHyps st ar T Cs Ω H Sg Rp Scs Nt Z) {Ac : Set U64} (s : S) (a : A) (number : I64)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    syscall.handle_unknown_syscall st ar s a number ⦃ s' _ =>
      ∃ Ac', EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄ := by
  unfold syscall.handle_unknown_syscall
  step with sched.cur_thread.spec as ⟨t, et⟩
  simp only [fl4_abi.config.PRINTING, fl4_abi.config.DEBUG_BUILD, ↓reduceIte]
  split
  · step with obj.Tcb.reg.spec as ⟨c⟩
    step as ⟨i, _⟩
    refine WP.spec_bind (hA.putc a i) fun a1 _ => ?_
    exact (WP.spec_ok _).2 ⟨Ac, h⟩
  split
  · exact (WP.spec_ok _).2 ⟨Ac, h⟩
  refine WP.spec_bind (E.debug Ac s a t number h) ?_
  rintro ⟨b, s1, a1⟩ ⟨Ac1, h1⟩
  try simp only [WP.uncurry'_pair]
  try simp only [uncurry_apply_pair]
  split
  · exact (WP.spec_ok _).2 ⟨Ac1, h1⟩
  · step as ⟨i, _⟩
    exact syscall.unknown_syscall_fault.entry hA hNt E s1 a1 i h1

/-- **`handle_syscall` keeps `EntryInv`**: the budget check at the entry, the
dispatch (with `HCur` across the invocation, `HCur.step`), then `schedule`. -/
theorem syscall.handle_syscall.entry (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (E : EntryHyps st ar T Cs Ω H Sg Rp Scs Nt Z) {Ac : Set U64} (s : S) (a : A) (number : I64)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    syscall.handle_syscall st ar s a number ⦃ s' _ => ∃ Ac', EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄ := by
  have hcT : L.curW s ∈ T := h.1.choose_spec.choose_spec.curT
  unfold syscall.handle_syscall
  step with sched.cur_thread.spec as ⟨t, et⟩
  have htT : t ∈ T := by rw [et]; exact hcT
  step with obj.Tcb.reg.spec as ⟨nx⟩
  step as ⟨i, _⟩
  refine WP.spec_bind (reg_entry h htT (r := layout.reg.FAULT_IP) (v := i) (by simp [layout.reg.FAULT_IP]))
    fun s1 h1 => ?_
  step with P0.obj.Tcb.flags.p0 st t s1 L.total as ⟨fl⟩
  step as ⟨i2, _⟩
  split
  · step as ⟨i3, _⟩
    exact syscall.unknown_syscall_fault.entry hA hNt E s1 a i3 h1
  split
  · exact syscall.handle_unknown_syscall.entry hA hNt E s1 a number h1
  split
  · exact syscall.handle_unknown_syscall.entry hA hNt E s1 a number h1
  have hcA1 : L.cscW s1 ∈ Ac := h1.2.2.2.2.2.1
  refine WP.spec_bind (syscall.budget_ok.bxc hA E s1 a h1) ?_
  rintro ⟨b, s2, a1⟩ ⟨h2, c2⟩
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (Pₘ := fun r : S × A => ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' r.1) ?_ ?_
  · split
    · exact WP.spec_mono (syscall.dispatch_syscall.bxi hA E s2 a1 number h2 (by rw [c2]; exact hcA1))
        fun r hr => by obtain ⟨s', a'⟩ := r; simpa using hr
    · exact (WP.spec_ok _).2 ⟨Ac, h2⟩
  · rintro ⟨s3, a2⟩ ⟨Ac3, h3⟩
    exact syscall.finish.entry hA hNt E s3 a2 h3

/-- **`handle_interrupt_entry` keeps `EntryInv`.** -/
theorem syscall.handle_interrupt_entry.entry (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (E : EntryHyps st ar T Cs Ω H Sg Rp Scs Nt Z) {Ac : Set U64} (s : S) (a : A) (irq : U64)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    syscall.handle_interrupt_entry st ar s a irq ⦃ s' _ =>
      ∃ Ac', EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄ := by
  unfold syscall.handle_interrupt_entry
  refine WP.spec_bind (sched.update_timestamp.entry hA s a h) ?_
  rintro ⟨s1, a1⟩ ⟨⟨⟨Q1, R1, h1⟩, hB1, hX1, hSg1, hS1⟩, -, hcA, hna, hcsc⟩
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (sched.check_budget.all hA s1 a1 Q1 R1 h1 hB1 hX1 hSg1 hS1 hcsc hna hcA (E.tmo Ac)) ?_
  rintro ⟨r, s2, a2⟩ ⟨h2, -⟩
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (E.irq Ac s2 a2 irq h2) ?_
  rintro ⟨s3, a3⟩ ⟨Ac3, h3⟩
  try simp only [WP.uncurry'_pair]
  exact syscall.finish.entry hA hNt E s3 a3 h3

end

end Fl4Proofs.P1
