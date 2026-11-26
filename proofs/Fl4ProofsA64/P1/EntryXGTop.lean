-- AArch64 port of Fl4Proofs.P1.EntryXGTop (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
/-
P1 (a6x): the kernel-entry composites with `XG` at the `finish` state.

Building on `EntryXG` (the IPC paths keep `XG`): the budget check at the
entry (`syscall.budget_ok.xg`: `XG` whether the check passes or fails),
`handle_yield` (`syscall.handle_yield.xg`), `handle_interrupt`
(`interrupt.handle_interrupt.xg`, from `SigXG`), the fault and receive
families from `EntryHyps0` (`EntryHyps0.faultXG`, `EntryHyps0.recvXG`), and the
composites of QueueEntry restated with the `finish` call as a hypothesis that
may use `XG` at the `finish` state (`…xgF`, `…entryXG`).  QueueEntry's
`syscall.handle_syscall_old.entry` is re-derived from `entryXG`
(`syscall.handle_syscall_old.entry'`).

`SigXG` (a definition, like QueueEntry's `TmoXG`): `send_signal` keeps `XG`
from a `BlkOK` / `UserOK` / `XG` state, given the transfer placement facts
(`XferHyps`).  It is the `send_signal` line's to prove (since #80/#85
`send_signal` may write the bound thread's IPC buffer); `SigXG.of_ipcFoot`
reduces it to an `IpcW` footprint of `send_signal`.  It is used by the IRQ
paths only (`handle_interrupt.xg`, `handle_interrupt_entry.entryXG`,
`kernel_entry.entryXG`).  No premise is added to any existing top.

a64 (AArch64 port): over the A forms (`EntryHyps0A`, `EHsA`, `TmoXGA`, `after_invocation.bxiA`,
`finish.entryA`); `syscall.budget_ok.bxcA` is the `EntryHyps0A` twin of QueueEntry's `budget_ok.bxc`.
A64 has no `SyscallGen`: x86's `*_old` composites are restated over the extraction with `fast := false`
(`unknown_syscall_fault.xgF`, `set_tls_base_self.xgF`, `handle_unknown_syscall.xgF`, `syscall.entryXG`,
`handle_syscall_general.entryXG` / `.entry'`), post on the state component; `handle_interrupt.xg` follows the
A64 `handle_interrupt.bxi` (5376 IRQs, `layout.irq.id`). Named premises: no new kind. The **[J]
`RunVcpuInv`** occurs as the hypothesis `hRV` of `interrupt.handle_interrupt.xg` and inside `SigXG`
(discharged by `sigXG_holds` with `send_signal.tinvF`'s own `hRV`); everywhere else it is taken from
`EntryHyps0A.rvAt` [J] (and the not-`TS_RUNNING_VM` conjunct of `EntryHyps0A.recvOK`).
-/
import Fl4ProofsA64.P1.EntryXG
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

/-- **`send_signal` keeps `XG`** (a definition, discharged by the
`send_signal` line; `SigXG.of_ipcFoot`): from a state with the invariants,
`UserOK` and `XG`, given the transfer placement facts, signalling a heap
notification ends at an `XG` state. -/
def SigXG {S : Type _} (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A) : Prop :=
  ∀ (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop),
    XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok →
    ∀ (Ac : Set U64) (s : S) (a : A) (n badge : U64), XG st T Cs Ω H Sg Scs Z P3Ok s →
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s → UserOK st T Cs Ω H U s → n ∈ Nt → H n = some .ntfn →
      RunVcpuInv st T s →  -- a64: `RunVcpuInv` at the signal (A64 `send_signal.tinvF`'s `hRV`)
      notification.send_signal st ar s a n badge ⦃ s' _ => XG st T Cs Ω H Sg Scs Z P3Ok s' ⦄

/-- `SigXG` from an `IpcW` footprint of `send_signal` (kernel words, the
receiver's user context and the user words `U`, cap-slot and debug words). -/
theorem SigXG.of_ipcFoot {S : Type _} {st : machine.Store S} [L : LawfulStore st] {A : Type _}
    {ar : machine.Arch A}
    (hF : ∀ (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop),
      XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok →
      ∀ (Ac : Set U64) (s : S) (a : A) (n badge : U64), XG st T Cs Ω H Sg Scs Z P3Ok s →
        BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s → UserOK st T Cs Ω H U s → n ∈ Nt → H n = some .ntfn →
        RunVcpuInv st T s →  -- a64
        notification.send_signal st ar s a n badge ⦃ s' _ => IpcFoot st T Cs Ω Sg Scs Z (EH H) U s s' ⦄) :
    SigXG st ar :=
  fun T Cs Ω H Sg Rp Scs Nt Z U P3Ok E Ac s a n badge hG h hU hn hH hRV =>
    WP.spec_mono (hF T Cs Ω H Sg Rp Scs Nt Z U P3Ok E Ac s a n badge hG h hU hn hH hRV) fun r f => by
      obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at f ⊢; exact hG.ipc hU f

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {P3Ok : S → Prop}
variable {A : Type _} {ar : machine.Arch A} {U : Set U64}

/-! ## The budget check, `handle_yield`, `handle_interrupt` -/

-- a64: `_A` twin (`EntryHyps0A`) of QueueEntry's `syscall.budget_ok.bxc` (it reads only `E.tmo`)
/-- `budget_ok` at a kernel entry keeps the current SC. -/
theorem syscall.budget_ok.bxcA (hA : P0.ArchTotal ar) (E : EntryHyps0A st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    {Ac : Set U64} (s : S) (a : A) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) :
    syscall.budget_ok st ar s a ⦃ b s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      (b = true → L.cscW s' ∈ Ac ∧ L.actionW s' ≠ L.curW s' ∧
        (L.mem s' (scA (L.curW s')) ≠ 0#u64 → L.cscW s' = L.mem s' (scA (L.curW s')))) ∧
      (b = true → XG st T Cs Ω H Sg Scs Z P3Ok s') ⦄ := by
  have h0 := h.1.choose_spec.choose_spec
  unfold syscall.budget_ok
  refine WP.spec_bind (WP.spec_and (sched.update_timestamp.entry hA s a h)
    (sched.update_timestamp.fr hA s a (h0.nodes _ h0.cur))) ?_
  rintro ⟨s1, a1⟩ ⟨⟨⟨⟨Q1, R1, h1⟩, hB1, hX1, hSg1, hS1⟩, c1, hcA, hna, hcsc, kk1⟩, w1⟩
  try simp only [WP.uncurry'_pair] at w1 ⊢
  have hG1 : XG st T Cs Ω H Sg Scs Z P3Ok s1 := hG.node h0.cur w1
  refine WP.spec_mono (sched.check_budget_restart.all hA s1 a1 Q1 R1 h1 hB1 hX1 hSg1 hS1 hcsc hna hcA
    (E.tmo hA Ac hG1 h1.cur)) ?_
  rintro ⟨r, s2, a2⟩ ⟨k2, e2⟩
  refine ⟨k2, fun hr => ?_, fun hr => ?_⟩
  · rw [e2 hr]; exact ⟨hcA, hna, hcsc⟩
  · rw [e2 hr]; exact hG1

/-- **The entry's budget check keeps `XG`**, whether it passes or not
(`update_timestamp`: the current node; `check_budget.allG` with `G := XG`;
the restart's `set_thread_state`). -/
theorem syscall.budget_ok.xg (hA : P0.ArchTotal ar) (TX : TmoXGA st ar)
    (E : EntryHyps0A st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) {Ac : Set U64} (s : S) (a : A)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) :
    syscall.budget_ok st ar s a ⦃ _ s' _ => XG st T Cs Ω H Sg Scs Z P3Ok s' ⦄ := by
  have h0 := h.1.choose_spec.choose_spec
  unfold syscall.budget_ok
  refine WP.spec_bind (WP.spec_and (sched.update_timestamp.entry hA s a h)
    (sched.update_timestamp.fr hA s a (h0.nodes _ h0.cur))) ?_
  rintro ⟨s1, a1⟩ ⟨⟨⟨⟨Q1, R1, h1⟩, hB1, hX1, hSg1, hS1⟩, c1, hcA, hna, hcsc, kk1⟩, w1⟩
  try simp only [WP.uncurry'_pair] at w1 ⊢
  have hG1 : XG st T Cs Ω H Sg Scs Z P3Ok s1 := hG.node h0.cur w1
  unfold sched.check_budget_restart
  refine WP.spec_bind (sched.check_budget.allG hA s1 a1 Q1 R1 h1 hB1 hX1 hSg1 hS1 hcsc hna hcA
    (fun _ _ g f => XG.foot g f) hG1 (E.tmoG hA TX Ac)) ?_
  rintro ⟨r, s2, a2⟩ ⟨⟨⟨⟨Q2, R2, h2⟩, hB2, hX2, hSg2, hS2⟩, g2⟩, -⟩
  try simp only [WP.uncurry'_pair]
  step with sched.cur_thread.spec as ⟨ct, ct_post⟩
  have hct : ct ∈ T := by rw [ct_post]; exact h2.curT
  split
  · simp only [WP.spec_ok, WP.uncurry'_pair]; exact g2
  step with sched.is_runnable.spec' as ⟨b, b_post⟩
  split
  · refine WP.spec_bind (sched.set_thread_state.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s2 ct _ h2 hct) ?_
    intro s3 f3
    simp only [WP.spec_ok, WP.uncurry'_pair]; exact g2.foot f3
  · simp only [WP.spec_ok, WP.uncurry'_pair]; exact g2

/-- **`handle_yield` keeps `XG`** (under `handle_yield.bxi`'s hypotheses, with
the timeout faults keeping `XG`, `TmoKG`). -/
theorem syscall.handle_yield.xg (hA : P0.ArchTotal ar) {Ac : Set U64} (s : S) (a : A)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hcA : L.cscW s ∈ Ac) (hna : L.actionW s ≠ L.curW s)
    (hcsc : L.mem s (scA (L.curW s)) ≠ 0#u64 → L.cscW s = L.mem s (scA (L.curW s)))
    (htmo : TmoKG st ar T Cs Ω H Sg Rp Scs Nt Z Ac (XG st T Cs Ω H Sg Scs Z P3Ok))
    (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) :
    syscall.handle_yield st ar s a ⦃ s' _ => XG st T Cs Ω H Sg Scs Z P3Ok s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hSg, hS⟩ := h
  unfold syscall.handle_yield
  step with sched.cur_sc.spec as ⟨csc, ecsc⟩
  have e1 : csc = L.cscW s := ecsc
  subst e1
  step with obj.Sc.consumed.spec as ⟨i⟩
  step with sched.consumed.spec as ⟨i1⟩
  step as ⟨total, _⟩
  step with sporadic.head.spec as ⟨hd, ehd⟩
  refine WP.spec_bind (sched.charge_budget.allG hA s a hd.amount false Q R h0 hB hX hSg hS hcsc hna hcA
    (fun _ _ g f => XG.foot g f) hG htmo) ?_
  rintro ⟨s1, a1⟩ ⟨⟨⟨Q1, R1, h1⟩, hB1, hX1, hSg1, hS1⟩, g1⟩
  try simp only [WP.uncurry'_pair]
  step with obj.Sc.set_consumed.spec as ⟨s2, e2⟩
  subst e2
  have hcS : L.cscW s ∈ Scs := hX.2.2.cur
  obtain ⟨hP, hz⟩ := hX1.1.sc _ hcS
  obtain ⟨h8, h128, -⟩ := sc_lo hP hz
  have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
  have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
  have hal : Aligned (core.num.U64.wrapping_add (L.cscW s) layout.sc.CONSUMED) := by
    unfold Aligned; rw [hv, hcv]; omega
  have hin : InSC (L.cscW s) (Z (L.cscW s)) (core.num.U64.wrapping_add (L.cscW s) layout.sc.CONSUMED) :=
    ⟨by rw [hv]; omega, by rw [hv]; omega⟩
  exact g1.foot (foot_wr (Es := EH H) hal (kw_sc hcS hin))

/-- **`handle_interrupt` keeps `XG`** (under `handle_interrupt.bxi`'s
hypotheses, with `UserOK`, the transfer placement facts and `SigXG`): the
signal by `SigXG`, the timer's node words, the reschedule IPI's `KW` step. -/
theorem interrupt.handle_interrupt.xg (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (XH : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (SX : SigXG st ar)
    {Ac : Set U64} (s : S) (a : A) (irq : U64)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hU : UserOK st T Cs Ω H U s)
    (hirq : ∀ i : U64, i.val < 5376 → obj.Slot.cap st (irqSlotA (L.ksb s) i) s ⦃ c => ∀ ptr b0 b1 b2,
      c = .Notification ptr b0 b1 b2 → ptr ∈ Nt ⦄) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s)
    (hRV : RunVcpuInv st T s) :  -- a64: [J] `RunVcpuInv` (`send_signal`, `SigXG`); 5376 IRQs
    interrupt.handle_interrupt st ar s a irq ⦃ s' _ => XG st T Cs Ω H Sg Scs Z P3Ok s' ⦄ := by
  have hST : P0.StoreTotal st := L.total
  have h0 := h.1.choose_spec.choose_spec
  unfold interrupt.handle_interrupt
  step with layout.irq.MAX.spec as ⟨mx, emx⟩
  split
  · refine WP.spec_bind (hA.mask_irq a irq true) fun a1 _ => ?_
    refine WP.spec_bind (hA.ack_irq a1 irq) fun a2 _ => ?_
    exact (WP.spec_ok _).2 hG
  step with P0.interrupt.irq_state.p0 st s irq hST as ⟨v⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => XG st T Cs Ω H Sg Scs Z P3Ok r.1) ?_ ?_
  · split
    · rename_i hle _
      step with interrupt.irq_slot.val as ⟨sl, esl⟩
      subst esl
      have hirq' : irq.val < 5376 := by
        have : mx.val = 5375 := by rw [emx]; rfl
        simp at hle; omega
      refine WP.spec_bind (hirq irq hirq') fun c hc => ?_
      refine WP.spec_bind (Pₘ := fun r : S × A => XG st T Cs Ω H Sg Scs Z P3Ok r.1) ?_ ?_
      · split
        all_goals try exact (WP.spec_ok _).2 hG
        rename_i ptr badge b x
        split
        · have hn := hc ptr badge b x rfl
          exact WP.spec_mono (SX T Cs Ω H Sg Rp Scs Nt Z U P3Ok XH Ac s a ptr badge hG h.blk hU hn (hNt ptr hn) hRV)
            fun r hr => by obtain ⟨s', a'⟩ := r; simpa using hr
        · exact (WP.spec_ok _).2 hG
      · rintro ⟨s3, a2⟩ h3
        try simp only [WP.uncurry'_pair]
        refine WP.spec_bind (hA.mask_irq a2 irq true) fun a3 _ => ?_
        exact (WP.spec_ok _).2 h3
    split
    · have hN := h0.nodes _ h0.cur
      step with LawfulStore.cur_cpu_spec as ⟨c, ec⟩
      step with obj.node_set.spec as ⟨s2, e2⟩
      subst ec e2
      have g2 := hG.foot (foot_node (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) (v := 1#u64)
        (o := layout.node.REPROGRAM) hN h0.cur (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
        (by simp [layout.node.REPROGRAM]))
      step with obj.node_set.spec as ⟨s3, e3⟩
      subst e3
      have g3 := g2.foot (foot_node (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) (v := 0#u64)
        (o := layout.node.ARMED) (hN.ksb (L.ksb_wr _ _ _)) h0.cur (by simp [layout.node.ARMED])
        (by simp [layout.node.ARMED]) (by simp [layout.node.ARMED]))
      first
        | exact g3
        | exact (WP.spec_ok _).2 g3
        | (simp only [LawfulStore.cpu_wr, nodeAt_wr] at g3 ⊢; first | exact g3 | exact (WP.spec_ok _).2 g3)
    split
    · unfold smp.handle_ipi
      -- a64: the IPI's id (`layout.irq.id`) against `RESCHEDULE_ID`
      refine WP.spec_bind (P0.layout.irq.id.p0 irq) fun ri _ => ?_
      split
      · refine WP.spec_bind (sched.reschedule_required.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s h0)
          fun s1 f1 => ?_
        exact (WP.spec_ok _).2 (hG.foot f1)
      · exact (WP.spec_ok _).2 hG
    · refine WP.spec_bind (Pₘ := fun _ : A => True) ?_ fun t _ => (WP.spec_ok _).2 hG
      split
      · exact WP.spec_mono (hA.mask_irq a irq true) fun _ _ => trivial
      · exact (WP.spec_ok _).2 trivial
  · rintro ⟨s1, a1⟩ h1
    try simp only [WP.uncurry'_pair]
    refine WP.spec_bind (hA.ack_irq a1 irq) fun a2 _ => ?_
    exact (WP.spec_ok _).2 h1

/-! ## The fault and receive families from `EntryHyps0` -/

/-- Faults of the current thread keep `XG` (`handle_fault.xg`, from `tmoOK`
and `xfer`). -/
theorem EntryHyps0A.faultXG (E : EntryHyps0A st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (hA : P0.ArchTotal ar)
    (Ac : Set U64) (s : S) (a : A) (f : error.Fault) (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) :
    faults.handle_fault st ar s a (L.curW s) f ⦃ s' _ => XG st T Cs Ω H Sg Scs Z P3Ok s' ⦄ := by
  obtain ⟨hc, hU, hcap⟩ := E.tmoOK Ac s hG h
  exact faults.handle_fault.xg hA E.xfer s a _ f h.blk hU hc (hcap _ (Or.inr rfl)) hG
    (E.rvAt Ac s hG h)  -- a64: [J] `rvAt`

/-- Receives keep `XG` (`handle_recv.xg`). -/
theorem EntryHyps0A.recvXG (E : EntryHyps0A st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (hA : P0.ArchTotal ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (Ac : Set U64) (s : S) (a : A) (blk rep : Bool)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) :
    syscall.handle_recv st ar s a blk rep ⦃ s' _ => XG st T Cs Ω H Sg Scs Z P3Ok s' ⦄ := by
  obtain ⟨hc, hU⟩ := E.blkU Ac s h
  obtain ⟨hlk, h3, hvm⟩ := E.recvOK Ac s hG h  -- a64: `recvOK`'s not-`TS_RUNNING_VM` conjunct
  exact syscall.handle_recv.xg hA hNt E.xfer s a blk rep h hU hc hlk h3
    (fun f => E.faultXG hA Ac s a f h hG) hG (E.rvAt Ac s hG h) hvm

/-- Faults: the invariants and `XG`. -/
theorem EntryHyps0A.faultB (E : EntryHyps0A st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (hA : P0.ArchTotal ar)
    (Ac : Set U64) (s : S) (a : A) (f : error.Fault) (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) :
    faults.handle_fault st ar s a (L.curW s) f ⦃ s' _ => ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ∧
      XG st T Cs Ω H Sg Scs Z P3Ok s' ⦄ :=
  WP.spec_mono (WP.spec_and (E.fault hA Ac s a f h hG) (E.faultXG hA Ac s a f h hG)) fun r hr => by
    obtain ⟨s', a'⟩ := r
    simp only [WP.uncurry'_pair] at hr ⊢
    obtain ⟨⟨Ac', h'⟩, g'⟩ := hr
    exact ⟨Ac', h', g'⟩

/-- Receives: the invariants and `XG`. -/
theorem EntryHyps0A.recvB (E : EntryHyps0A st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (hA : P0.ArchTotal ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (Ac : Set U64) (s : S) (a : A) (blk rep : Bool)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) :
    syscall.handle_recv st ar s a blk rep ⦃ s' _ => ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ∧
      XG st T Cs Ω H Sg Scs Z P3Ok s' ⦄ :=
  WP.spec_mono (WP.spec_and (E.recv hA hNt Ac s a blk rep h hG) (E.recvXG hA hNt Ac s a blk rep h hG))
    fun r hr => by
      obtain ⟨s', a'⟩ := r
      simp only [WP.uncurry'_pair] at hr ⊢
      obtain ⟨⟨Ac', h'⟩, g'⟩ := hr
      exact ⟨Ac', h', g'⟩

/-! ## The composites -/

/-- **`dispatch_syscall` ends at an `XG` state** (with the invariants, as
`dispatch_syscall.bxi`). -/
theorem syscall.dispatch_syscall.xg (hA : P0.ArchTotal ar) (TX : TmoXGA st ar) {Adm : PSets → Prop}
    (EH : ∀ σ, Adm σ → EHsA st ar Adm Cs U P3Ok σ) (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩)
    {Ac : Set U64} (s : S) (a : A) (number : I64) (he : EntAt st P3Ok s) (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hcA : L.cscW s ∈ Ac) (hna : L.actionW s ≠ L.curW s)
    (hcsc : L.mem s (scA (L.curW s)) ≠ 0#u64 → L.cscW s = L.mem s (scA (L.curW s))) :
    syscall.dispatch_syscall st ar s a number ⦃ s' _ => ∃ σ', Adm σ' ∧ ∃ Ac', BXIs st Cs σ' Ac' s' ∧
      XG st σ'.T Cs σ'.Ω σ'.H σ'.Sg σ'.Scs σ'.Z P3Ok s' ⦄ := by
  obtain ⟨E, hNt⟩ := EH _ hσ
  have IA : ∀ (call blk don fp : Bool) (cptr : U64),
      syscall.handle_invocation st ar s a call blk don fp cptr ⦃ r s1 a1 =>
        syscall.after_invocation st ar s1 a1 r ⦃ _ s2 _ => ∃ σ', Adm σ' ∧ ∃ Ac', BXIs st Cs σ' Ac' s2 ∧
          XG st σ'.T Cs σ'.Ω σ'.H σ'.Sg σ'.Scs σ'.Z P3Ok s2 ⦄ ⦄ :=
    fun call blk don fp cptr => WP.spec_mono (spec_eq' (E.inv Ac s a call blk don fp cptr he h hcA hna hcsc)) (by
      rintro ⟨r', s1, a1⟩ ⟨eqI, hr⟩
      simp only [WP.uncurry'_pair] at hr ⊢
      obtain ⟨σ1, hσ1, Ac1, h1, e1⟩ := hr
      obtain ⟨E1, hNt1⟩ := EH σ1 hσ1
      obtain ⟨G1, G2⟩ := E1.postG s a call blk don fp cptr r' s1 a1 he eqI
      exact WP.spec_mono (spec_eq' (syscall.after_invocation.bxiA hA hNt1 TX E1.toEntryHyps0A s1 a1 r' h1 G1
        (fun e he => (HCur.of_mem hcA).step (e1 e he).1) fun e he => (e1 e he).2)) (by
          rintro ⟨b, s2, a2⟩ ⟨eqA, Ac2, h2⟩
          exact ⟨σ1, hσ1, Ac2, h2, G2 b s2 a2 eqA⟩))
  have IR : ∀ (call blk don fp : Bool) (cptr : U64) (b1 b2 : Bool),
      (do
        let (r, s1, a1) ← syscall.handle_invocation st ar s a call blk don fp cptr
        let (b, s2, a2) ← syscall.after_invocation st ar s1 a1 r
        if b then syscall.handle_recv st ar s2 a2 b1 b2 else ok (s2, a2)) ⦃ s' _ =>
          ∃ σ', Adm σ' ∧ ∃ Ac', BXIs st Cs σ' Ac' s' ∧ XG st σ'.T Cs σ'.Ω σ'.H σ'.Sg σ'.Scs σ'.Z P3Ok s' ⦄ := by
    intro call blk don fp cptr b1 b2
    refine WP.spec_bind (IA call blk don fp cptr) ?_
    rintro ⟨r, s1, a1⟩ hh
    simp only [WP.uncurry'_pair] at hh ⊢
    refine WP.spec_bind hh ?_
    rintro ⟨b, s2, a2⟩ ⟨σ2, hσ2, Ac2, h2, g2⟩
    try simp only [WP.uncurry'_pair]
    try simp only [uncurry_apply_pair]
    obtain ⟨E2, hNt2⟩ := EH σ2 hσ2
    split
    · exact WP.spec_mono (E2.recvB hA hNt2 Ac2 s2 a2 b1 b2 h2 g2) fun r hr => by
        obtain ⟨s', a'⟩ := r
        simp only [WP.uncurry'_pair] at hr ⊢
        obtain ⟨Ac3, h3, g3⟩ := hr
        exact ⟨σ2, hσ2, Ac3, h3, g3⟩
    · exact (WP.spec_ok _).2 ⟨σ2, hσ2, Ac2, h2, g2⟩
  have IS : ∀ (call blk don fp : Bool) (cptr : U64),
      (do
        let (r, s1, a1) ← syscall.handle_invocation st ar s a call blk don fp cptr
        let (_, s2, a2) ← syscall.after_invocation st ar s1 a1 r
        ok (s2, a2)) ⦃ s' _ => ∃ σ', Adm σ' ∧ ∃ Ac', BXIs st Cs σ' Ac' s' ∧
          XG st σ'.T Cs σ'.Ω σ'.H σ'.Sg σ'.Scs σ'.Z P3Ok s' ⦄ := by
    intro call blk don fp cptr
    refine WP.spec_bind (IA call blk don fp cptr) ?_
    rintro ⟨r, s1, a1⟩ hh
    simp only [WP.uncurry'_pair] at hh ⊢
    refine WP.spec_bind hh ?_
    rintro ⟨b, s2, a2⟩ ⟨σ2, hσ2, Ac2, h2, g2⟩
    exact (WP.spec_ok _).2 ⟨σ2, hσ2, Ac2, h2, g2⟩
  have RC : ∀ (b1 b2 : Bool), syscall.handle_recv st ar s a b1 b2 ⦃ s' _ => ∃ σ', Adm σ' ∧ ∃ Ac',
      BXIs st Cs σ' Ac' s' ∧ XG st σ'.T Cs σ'.Ω σ'.H σ'.Sg σ'.Scs σ'.Z P3Ok s' ⦄ := fun b1 b2 =>
    WP.spec_mono (E.recvB hA hNt Ac s a b1 b2 h he.xg) fun r hr => by
      obtain ⟨s', a'⟩ := r
      simp only [WP.uncurry'_pair] at hr ⊢
      obtain ⟨Ac', h', g'⟩ := hr
      exact ⟨_, hσ, Ac', h', g'⟩
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
  · rw [if_pos c4]; exact RC _ _
  rw [if_neg c4]
  by_cases c5 : number = fl4_abi.syscall.SysNBRecv
  · rw [if_pos c5]; exact RC _ _
  rw [if_neg c5]
  by_cases c6 : number = fl4_abi.syscall.SysWait
  · rw [if_pos c6]; exact RC _ _
  rw [if_neg c6]
  by_cases c7 : number = fl4_abi.syscall.SysNBWait
  · rw [if_pos c7]; exact RC _ _
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
  · rw [if_pos c11]
    exact WP.spec_mono (WP.spec_and (syscall.handle_yield.bxi hA s a h hcA hna hcsc
      (E.tmo hA Ac he.xg h.1.choose_spec.choose_spec.cur))
      (syscall.handle_yield.xg hA s a h hcA hna hcsc (E.tmoG hA TX Ac) he.xg)) fun r hr => by
      obtain ⟨s', a'⟩ := r
      simp only [WP.uncurry'_pair] at hr ⊢
      exact ⟨_, hσ, Ac, hr.1, hr.2⟩
  rw [if_neg c11]
  exact (WP.spec_ok _).2 ⟨_, hσ, Ac, h, he.xg⟩

-- a64: A64 has no `SyscallGen` (`*_old`); the composites below are over the real extraction with
-- `fast := false` (`unknown_syscall_fault … false`, `handle_unknown_syscall … false`, `syscall … false`,
-- `handle_syscall_general`), whose bodies call `finish` themselves; the post is on the state component.

/-- seL4 `handleUnknownSyscall`'s fault path, with `finish` given at `BXI ∧ XG`. -/
theorem syscall.unknown_syscall_fault.xgF (hA : P0.ArchTotal ar) (TX : TmoXGA st ar)
    (E : EntryHyps0A st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) {Ac : Set U64} (s : S) (a : A) (n : U64)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) {Post : S → Prop}
    (hfin : ∀ (Ac : Set U64) (s : S) (a : A), BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
      XG st T Cs Ω H Sg Scs Z P3Ok s → syscall.finish st ar s a ⦃ s' _ => Post s' ⦄) :
    syscall.unknown_syscall_fault st ar s a n false ⦃ _ s' _ => Post s' ⦄ := by
  unfold syscall.unknown_syscall_fault
  refine WP.spec_bind (WP.spec_and (syscall.budget_ok.bxcA hA E s a h hG) (syscall.budget_ok.xg hA TX E s a h hG)) ?_
  rintro ⟨b, s1, a1⟩ ⟨⟨h1, -, -⟩, g1⟩
  try simp only [WP.uncurry'_pair] at g1 ⊢
  try simp only [Bool.false_eq_true, ↓reduceIte]
  try simp only [uncurry_apply_pair, Bool.false_eq_true, ↓reduceIte]
  split
  · step with sched.cur_thread.spec as ⟨t, et⟩
    have et' : t = L.curW s1 := et
    subst et'
    refine WP.spec_bind (E.faultB hA Ac s1 a1 _ h1 g1) ?_
    rintro ⟨s2, a2⟩ ⟨Ac2, h2, g2⟩
    refine WP.spec_bind (hfin Ac2 s2 a2 h2 g2) ?_
    rintro ⟨s3, a3⟩ h3
    exact (WP.spec_ok _).2 h3
  · refine WP.spec_bind (hfin Ac s1 a1 h1 g1) ?_
    rintro ⟨s3, a3⟩ h3
    exact (WP.spec_ok _).2 h3

/-- seL4 `handleUnknownSyscall`'s SetTLSBase path, with `finish` given at `BXI ∧ XG`
(a64: the base is read from `layout.reg.CAP`). -/
theorem syscall.set_tls_base_self.xgF (hA : P0.ArchTotal ar) (TX : TmoXGA st ar)
    (E : EntryHyps0A st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) {Ac : Set U64} (s : S) (a : A)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) {Post : S → Prop}
    (hfin : ∀ (Ac : Set U64) (s : S) (a : A), BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
      XG st T Cs Ω H Sg Scs Z P3Ok s → syscall.finish st ar s a ⦃ s' _ => Post s' ⦄) :
    syscall.set_tls_base_self st ar s a ⦃ s' _ => Post s' ⦄ := by
  unfold syscall.set_tls_base_self
  refine WP.spec_bind (WP.spec_and (syscall.budget_ok.bxcA hA E s a h hG) (syscall.budget_ok.xg hA TX E s a h hG)) ?_
  rintro ⟨b, s1, a1⟩ ⟨⟨h1, -⟩, g1⟩
  try simp only [WP.uncurry'_pair] at g1 ⊢
  refine WP.spec_bind (Pₘ := fun s2 : S => ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s2 ∧
      XG st T Cs Ω H Sg Scs Z P3Ok s2) ?_ ?_
  · split
    · step with sched.cur_thread.spec as ⟨t, et⟩
      have htT : t ∈ T := by rw [et]; exact h1.1.choose_spec.choose_spec.curT
      step with obj.Tcb.reg.spec as ⟨base⟩
      step with P0.regs.sanitise.p0 as ⟨i1⟩
      refine WP.spec_mono (regW_spec h1.blk htT (r := layout.reg.TLS_BASE)
        (by simp [layout.reg.TLS_BASE, layout.reg.TPIDR_EL0])) ?_
      rintro s3 ⟨h3, f3, -⟩
      exact ⟨Ac, h3.bxi, g1.foot (WritesIn.mono f3 fun _ hb => KW.mono hb (Set.empty_subset _))⟩
    · exact (WP.spec_ok _).2 ⟨Ac, h1, g1⟩
  · rintro s2 ⟨Ac2, h2, g2⟩
    exact hfin Ac2 s2 a1 h2 g2

/-- Native `handleUnknownSyscall` (excluding VMEnter), with `finish` given at
`BXI ∧ XG` and the direct returns at `EntryInv` (`hpost`). -/
theorem syscall.handle_unknown_syscall.xgF (hA : P0.ArchTotal ar) (TX : TmoXGA st ar)
    (E : EntryHyps0A st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) {Ac : Set U64} (s : S) (a : A) (number : I64)
    (hNative : number ≠ fl4_abi.syscall.SysVMEnter) (he : EntAt st P3Ok s)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) {Post : S → Prop}
    (hfin : ∀ (Ac : Set U64) (s : S) (a : A), BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
      XG st T Cs Ω H Sg Scs Z P3Ok s → syscall.finish st ar s a ⦃ s' _ => Post s' ⦄)
    (hpost : ∀ (Ac : Set U64) (s : S), EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s → Post s) :
    syscall.handle_unknown_syscall st ar s a number false ⦃ _ s' _ => Post s' ⦄ := by
  unfold syscall.handle_unknown_syscall
  step with sched.cur_thread.spec as ⟨t, et⟩
  simp only [fl4_abi.config.PRINTING, fl4_abi.config.DEBUG_BUILD, ↓reduceIte]
  split
  · step with obj.Tcb.reg.spec as ⟨c⟩
    step as ⟨i, _⟩
    refine WP.spec_bind (hA.putc a i) fun a1 _ => ?_
    exact (WP.spec_ok _).2 (hpost Ac s h)
  split
  · exact (WP.spec_ok _).2 (hpost Ac s h)
  have et' : t = L.curW s := et
  subst et'
  refine WP.spec_bind (WP.spec_and (E.debug Ac s a number he h) (syscall.debug_syscall.same hA s a _ number)) ?_
  rintro ⟨b, s1, a1⟩ ⟨⟨Ac1, h1⟩, e1⟩
  try simp only [WP.uncurry'_pair]
  try simp only [uncurry_apply_pair]
  split
  · exact (WP.spec_ok _).2 (hpost Ac1 s1 h1)
  · rename_i hb
    simp only [WP.uncurry'_pair] at e1
    have hG1 : XG st T Cs Ω H Sg Scs Z P3Ok s1 := by rw [e1 (by simpa using hb)]; exact he.xg
    simp only [fl4_abi.config.SET_TLS_BASE_SELF, ↓reduceIte]
    split
    · refine WP.spec_bind (syscall.set_tls_base_self.xgF hA TX E s1 a1 h1 hG1 hfin) ?_
      rintro ⟨s2, a2⟩ h2
      exact (WP.spec_ok _).2 h2
    · try simp only [hNative, ↓reduceIte]  -- a64: the VMEnter branch is excluded (`hNative`)
      step as ⟨i, _⟩
      exact syscall.unknown_syscall_fault.xgF hA TX E s1 a1 i h1 hG1 hfin

/-- **Native `syscall … false` with `XG` at `finish`** (a64: the general path, x86's
`handle_syscall_old.entryXG`), with the `finish` call a hypothesis (`hfin`) that
may use `BXI ∧ XG` at the `finish` state (over the admissible tuple the entry
ends with), and the direct returns at `EntryInv` (`hpost`). -/
theorem syscall.syscall.entryXG (hA : P0.ArchTotal ar) (TX : TmoXGA st ar) {Adm : PSets → Prop}
    (EH : ∀ σ, Adm σ → EHsA st ar Adm Cs U P3Ok σ) (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩)
    {Ac : Set U64} (s : S) (a : A) (number : I64)
    (hNative : number ≠ fl4_abi.syscall.SysVMEnter) (hP : P3Ok s)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) {Post : S → Prop}
    (hfin : ∀ σ, Adm σ → ∀ (Ac : Set U64) (s : S) (a : A), BXIs st Cs σ Ac s →
      XG st σ.T Cs σ.Ω σ.H σ.Sg σ.Scs σ.Z P3Ok s → syscall.finish st ar s a ⦃ s' _ => Post s' ⦄)
    (hpost : ∀ σ, Adm σ → ∀ (Ac : Set U64) (s : S), EntryInvs st Cs σ Ac s → Post s) :
    syscall.syscall st ar s a number false ⦃ _ s' _ => Post s' ⦄ := by
  obtain ⟨E', hNt⟩ := EH _ hσ
  have E := E'.toEntryHyps0A
  have hfin0 := hfin _ hσ
  have hpost0 := hpost _ hσ
  have hcT : L.curW s ∈ T := h.1.choose_spec.choose_spec.curT
  unfold syscall.syscall
  step with sched.cur_thread.spec as ⟨t, et⟩
  have htT : t ∈ T := by rw [et]; exact hcT
  step with obj.Tcb.reg.spec as ⟨nx⟩
  step as ⟨i, _⟩
  refine WP.spec_bind (WP.spec_and (reg_entry h htT (r := layout.reg.FAULT_IP) (v := i) (by simp [layout.reg.FAULT_IP]))
    (obj.Tcb.set_reg.wrK s t layout.reg.FAULT_IP i (h.1.choose_spec.choose_spec.tcbs t htT)
      (by simp [layout.reg.FAULT_IP]))) ?_
  rintro s1 ⟨h1, K, hK, e1⟩
  have et' : t = L.curW s := et
  have hal : Aligned (core.num.U64.wrapping_add (L.curW s) K) := by
    rw [← et']; exact field_aligned (h.1.choose_spec.choose_spec.tcbs t htT)
      (by rw [hK]; simp [layout.reg.FAULT_IP]) (by rw [hK]; simp [layout.reg.FAULT_IP])
  have he1 : EntAt st P3Ok s1 := ⟨s, hP, Ent.prefix hK hal (by rw [e1, et']) (WritesIn.refl _ _)⟩
  step with P0.obj.Tcb.flags.p0 st t s1 L.total as ⟨fl⟩
  step as ⟨i2, _⟩
  split
  · -- a64: the trapped syscall number is read from `X8`
    step with obj.Tcb.reg.spec as ⟨i3⟩
    exact syscall.unknown_syscall_fault.xgF hA TX E s1 a i3 h1 he1.xg hfin0
  split
  · exact syscall.handle_unknown_syscall.xgF hA TX E s1 a number hNative he1 h1 hfin0 hpost0
  split
  · exact syscall.handle_unknown_syscall.xgF hA TX E s1 a number hNative he1 h1 hfin0 hpost0
  have hN1 : NodePlaced st T s1 (L.cpu s1) :=
    (h1.1.choose_spec.choose_spec).nodes _ h1.1.choose_spec.choose_spec.cur
  refine WP.spec_bind (WP.spec_and (WP.spec_and (syscall.budget_ok.bxcA hA E s1 a h1 he1.xg)
    (syscall.budget_ok.fr hA s1 a hN1)) (syscall.budget_ok.xg hA TX E s1 a h1 he1.xg)) ?_
  rintro ⟨b, s2, a1⟩ ⟨⟨⟨h2, k2, -⟩, f2⟩, g2⟩
  try simp only [WP.uncurry'_pair] at g2 ⊢
  try simp only [Bool.false_eq_true, ↓reduceIte]
  try simp only [uncurry_apply_pair, Bool.false_eq_true, ↓reduceIte]
  split
  · rename_i hb
    obtain ⟨hcA2, hna2, hcsc2⟩ := k2 hb
    have he : EntAt st P3Ok s2 := ⟨s, hP, Ent.prefix hK hal (by rw [e1, et']) (f2 hb)⟩
    refine WP.spec_bind (syscall.dispatch_syscall.xg hA TX EH hσ s2 a1 number he h2 hcA2 hna2 hcsc2) ?_
    rintro ⟨s3, a2⟩ ⟨σ3, hσ3, Ac3, h3, g3⟩
    refine WP.spec_bind (hfin σ3 hσ3 Ac3 s3 a2 h3 g3) ?_
    rintro ⟨s4, a3⟩ h4
    exact (WP.spec_ok _).2 h4
  · refine WP.spec_bind (hfin _ hσ Ac s2 a1 h2 g2) ?_
    rintro ⟨s4, a3⟩ h4
    exact (WP.spec_ok _).2 h4

/-- **`handle_syscall_general` with `XG` at `finish`** (`syscall.syscall.entryXG`). -/
theorem syscall.handle_syscall_general.entryXG (hA : P0.ArchTotal ar) (TX : TmoXGA st ar) {Adm : PSets → Prop}
    (EH : ∀ σ, Adm σ → EHsA st ar Adm Cs U P3Ok σ) (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩)
    {Ac : Set U64} (s : S) (a : A) (number : I64)
    (hNative : number ≠ fl4_abi.syscall.SysVMEnter) (hP : P3Ok s)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) {Post : S → Prop}
    (hfin : ∀ σ, Adm σ → ∀ (Ac : Set U64) (s : S) (a : A), BXIs st Cs σ Ac s →
      XG st σ.T Cs σ.Ω σ.H σ.Sg σ.Scs σ.Z P3Ok s → syscall.finish st ar s a ⦃ s' _ => Post s' ⦄)
    (hpost : ∀ σ, Adm σ → ∀ (Ac : Set U64) (s : S), EntryInvs st Cs σ Ac s → Post s) :
    syscall.handle_syscall_general st ar s a number ⦃ s' _ => Post s' ⦄ := by
  unfold syscall.handle_syscall_general
  refine WP.spec_bind (syscall.syscall.entryXG hA TX EH hσ s a number hNative hP h hfin hpost) ?_
  rintro ⟨b, s1, a1⟩ h1
  exact (WP.spec_ok _).2 h1

/-- QueueEntry's `handle_syscall_old.entry`, on A64 over `handle_syscall_general`, is an
instance of `entryXG` (`finish.entryA`, which uses `XG` for the buffer placement). -/
theorem syscall.handle_syscall_general.entry' (hA : P0.ArchTotal ar) (TX : TmoXGA st ar)
    {Adm : PSets → Prop}
    (EH : ∀ σ, Adm σ → EHsA st ar Adm Cs U P3Ok σ) (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩)
    {Ac : Set U64} (s : S) (a : A) (number : I64)
    (hNative : number ≠ fl4_abi.syscall.SysVMEnter) (hP : P3Ok s)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    syscall.handle_syscall_general st ar s a number ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄ :=
  syscall.handle_syscall_general.entryXG hA TX EH hσ s a number hNative hP h
    (fun σ hσ' Ac s a h g => WP.spec_mono (syscall.finish.entryA hA (EH σ hσ').2 (EH σ hσ').1.toEntryHyps0A s a h g)
      fun r hr => by obtain ⟨s', a'⟩ := r; obtain ⟨Ac', h'⟩ := hr; exact ⟨σ, hσ', Ac', h'⟩)
    fun σ hσ' Ac s h => ⟨σ, hσ', Ac, h⟩

/-- **`handle_interrupt_entry` with `XG` at `finish`** (the budget check by
`check_budget.allG` with `G := XG`, the interrupt by `handle_interrupt.xg`,
from `SigXG` and the transfer placement facts). -/
theorem syscall.handle_interrupt_entry.entryXG (hA : P0.ArchTotal ar) (TX : TmoXGA st ar) (SX : SigXG st ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (E : EntryHyps0A st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (XH : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) {Ac : Set U64} (s : S) (a : A) (irq : U64)
    (hP : P3Ok s) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) {Post : S → Prop}
    (hfin : ∀ (Ac : Set U64) (s : S) (a : A), BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
      XG st T Cs Ω H Sg Scs Z P3Ok s → syscall.finish st ar s a ⦃ s' _ => Post s' ⦄) :
    syscall.handle_interrupt_entry st ar s a irq ⦃ s' _ => Post s' ⦄ := by
  have h0 := h.1.choose_spec.choose_spec
  have hG : XG st T Cs Ω H Sg Scs Z P3Ok s := EntAt.xg ⟨s, hP, WritesIn.refl _ _⟩
  unfold syscall.handle_interrupt_entry
  refine WP.spec_bind (WP.spec_and (sched.update_timestamp.entry hA s a h)
    (sched.update_timestamp.fr hA s a (h0.nodes _ h0.cur))) ?_
  rintro ⟨s1, a1⟩ ⟨⟨⟨⟨Q1, R1, h1⟩, hB1, hX1, hSg1, hS1⟩, -, hcA, hna, hcsc, -⟩, w1⟩
  try simp only [WP.uncurry'_pair] at w1 ⊢
  refine WP.spec_bind (sched.check_budget.allG hA s1 a1 Q1 R1 h1 hB1 hX1 hSg1 hS1 hcsc hna hcA
    (fun _ _ g f => XG.foot g f) (hG.node h0.cur w1) (E.tmoG hA TX Ac)) ?_
  rintro ⟨r, s2, a2⟩ ⟨⟨h2, g2⟩, -⟩
  try simp only [WP.uncurry'_pair]
  have hU2 := (E.blkU Ac s2 h2).2
  have hRV2 := E.rvAt Ac s2 g2 h2  -- a64: [J] `rvAt`
  refine WP.spec_bind (WP.spec_and (interrupt.handle_interrupt.bxi hA hNt s2 a2 irq h2 (E.irqcap Ac s2 g2 h2)
      (E.bufAt Ac s2 g2 h2) hRV2)
    (interrupt.handle_interrupt.xg hA hNt XH SX s2 a2 irq h2 hU2 (E.irqcap Ac s2 g2 h2) g2 hRV2)) ?_
  rintro ⟨s3, a3⟩ ⟨h3, g3⟩
  try simp only [WP.uncurry'_pair]
  exact hfin Ac s3 a3 h3 g3

/-- **Native kernel entries with `XG` at `finish`** (`kernel_entry.entry`'s
shape, with the `finish` calls as the hypothesis `hfin` and the direct
returns `hpost`); the IRQ entry uses `SigXG` and the transfer placement facts
of the start tuple. (a64: the syscall entry is `handle_syscall_general`.)
**Vacuous** (p1g): its premise bundles are contradictory with the `EntryInv` premise
(P1/EntryVacuous). Use P3's `kernel_entry_entryInvU29` (P3/XTopJointEntryInv29),
which has this conclusion from U29's premises. -/
theorem kernel_entry.entryXG (hA : P0.ArchTotal ar) (TX : TmoXGA st ar) (SX : SigXG st ar) {Adm : PSets → Prop}
    (EH : ∀ σ, Adm σ → EHsA st ar Adm Cs U P3Ok σ) (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩)
    (XH : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    {Ac : Set U64} (s : S) (a : A) (hP : P3Ok s)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) {Post : S → Prop}
    (hfin : ∀ σ, Adm σ → ∀ (Ac : Set U64) (s : S) (a : A), BXIs st Cs σ Ac s →
      XG st σ.T Cs σ.Ω σ.H σ.Sg σ.Scs σ.Z P3Ok s → syscall.finish st ar s a ⦃ s' _ => Post s' ⦄)
    (hpost : ∀ σ, Adm σ → ∀ (Ac : Set U64) (s : S), EntryInvs st Cs σ Ac s → Post s) :
    (∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter → syscall.handle_syscall_general st ar s a number ⦃ s' _ =>
      Post s' ⦄) ∧
    (∀ irq : U64, syscall.handle_interrupt_entry st ar s a irq ⦃ s' _ => Post s' ⦄) :=
  ⟨fun number hNative => syscall.handle_syscall_general.entryXG hA TX EH hσ s a number hNative hP h hfin hpost,
   fun irq => syscall.handle_interrupt_entry.entryXG hA TX SX (EH _ hσ).2 (EH _ hσ).1.toEntryHyps0A XH s a irq hP h
     (hfin _ hσ)⟩

end

end Fl4ProofsA64.P1
