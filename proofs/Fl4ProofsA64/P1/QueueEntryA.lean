/-
P1 (AArch64): the kernel-entry hypotheses over the A64 message-transfer hypothesis `XferOKA` (QueueXferA).

`EntryHyps0.xfer : XferOK …` (QueueEntry) is not provable on AArch64 (`trap_extra_mrs` writes the sender's
`FAULT_W1`, outside `XferFr`; QueueXferA's docstring). This module is the `_A` twin of QueueEntry's
entry-hypothesis structures and the lemmas that read `xfer`, with `XferOKA` in place of `XferOK` and the
`_A` twins of `handle_timeout.bxi` / `handle_fault.bxi` / `handle_recv.bxi`:
`EntryHyps0A` (fields as `EntryHyps0`, `xfer : XferOKA …`), `EntryHyps0A.vmchk` / `.tmo` / `.tmoG` /
`.fault` / `.recv`, `EntryHypsA`, `EHsA`, `TmoXGA` (`TmoXG` over `XferOKA`), `syscall.finish.entryA`,
`syscall.after_invocation.bxiA`, `syscall.dispatch_syscall.bxiA` (QueueEntry) and `EntryHypsA.of`
(QueueKeeps). Statements and proofs are the originals' text with those names swapped; the existing
statements are unchanged. Downstream A64 modules use the `A` forms.

Named premises: as the originals: **[J] field `rvAt`** (`RunVcpuInv` at `XG` states), **[P] field `vmpl`**
(the run frame `RunBuf` and the run VCPU's `RUN_CALLER` word), and the hypothesis fields of `EntryHyps0`
(`xfer` now `XferOKA`, discharged by `xferOK_ofA` in QueueXfer from `XferHyps`). Nothing new.
-/
import Fl4ProofsA64.P1.QueueKeeps
import Fl4ProofsA64.P1.QueueXferA
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}
variable {A : Type _} {ar : machine.Arch A} {U : Set U64} {P3Ok : S → Prop}

-- a64: `_A` twin (`XferOKA`) of the QueueEntry text below
/-- The hypotheses of the kernel-entry composites, one per family of kernel
operation not proved in P1, stated with P1's invariants.  An invocation may
shrink the active set (`Ac'`, an SC deletion); `handle_invocation` reports
its `CurStep` (for `HCur.step`) and, when it was preempted, what the
preemption point needs (that is `EntryHyps`' `inv`).
**Contradictory** (p1g, P1/EntryVacuous): no `BXI` state satisfies it (`blkU`); not a
specification of the kernel. -/
structure EntryHyps0A (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A) (T Cs Ω : Set U64)
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop) : Prop where
  /-- The message transfer keeps the invariants within `XferFr` (`do_ipc_transfer`;
  `xferOK_of` proves it from `XferHyps`). -/
  xfer : XferOKA st ar T Cs Ω H Sg Rp Scs Nt Z U (XG st T Cs Ω H Sg Scs Z P3Ok)
  /-- At a timeout fault of the current thread (`check_budget`'s
  `end_timeslice`): it can block, the user words are outside the kernel
  objects, and the caps (its timeout-handler slot) are typed. -/
  tmoOK : ∀ (Ac : Set U64) (s : S), XG st T Cs Ω H Sg Scs Z P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    CanBlock st T Ac s (L.curW s) ∧ UserOK st T Cs Ω H U s ∧
    ∀ i, (i = layout.tcb.SLOT_TIMEOUT_HANDLER ∨ i = layout.tcb.SLOT_FAULT_HANDLER) →
      obj.Tcb.slot (L.curW s) i ⦃ sl => obj.Slot.cap st sl s ⦃ c => CapTyped H Rp Nt c ⦄ ⦄
  /-- The current thread can block and the user words are outside the kernel
  objects, at every `BXI` state (unguarded: `handle_invocation.inv` reads it
  after the invocation, over the sets after, and `decGap_reply`). -/
  blkU : ∀ (Ac : Set U64) (s : S), BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    CanBlock st T Ac s (L.curW s) ∧ UserOK st T Cs Ω H U s
  /-- At a receive (`handle_recv`, an `XG` state): the caps the current
  thread looks up are typed, and the notification states are the three
  states. -/
  recvOK : ∀ (Ac : Set U64) (s : S), XG st T Cs Ω H Sg Scs Z P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    (∀ cptr, cspace.lookup_cap st s (L.curW s) cptr ⦃ r => ∀ c, r = .Ok c → CapTyped H Rp Nt c ⦄) ∧
    (∀ n ∈ Nt, L.epState s n ≠ 3#u64) ∧
    -- a64: the current thread at a receive is not in `TS_RUNNING_VM` (A64 `handle_recv.bxi`'s `hvm`)
    L.mem s (stA (L.curW s)) ≠ sched.TS_RUNNING_VM
  /-- At an `XG` state (where `handle_interrupt` runs: after the entry's
  budget check or an invocation's preemption point, both keeping `XG`,
  `check_budget.allG` / `mcs_preemption_point.allG` with `TmoXGA`): the
  notification caps of the IRQ handler slots name heap notifications (P3's
  `CapValid`); `handle_interrupt` itself is proved
  (`interrupt.handle_interrupt.bxi`). -/
  irqcap : ∀ (Ac : Set U64) (s : S), XG st T Cs Ω H Sg Scs Z P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    ∀ i : U64, i.val < 5376 →
    obj.Slot.cap st (irqSlotA (L.ksb s) i) s ⦃ c => ∀ ptr b0 b1 b2, c = .Notification ptr b0 b1 b2 → ptr ∈ Nt ⦄
  /-- The debug syscalls (`debug_syscall`, which return to the thread directly). -/
  debug : ∀ (Ac : Set U64) (s : S) (a : A) (n : I64), EntAt st P3Ok s → EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    syscall.debug_syscall st ar s a (L.curW s) n ⦃ _ s' _ => ∃ Ac', EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄
  /-- (P3, from its post-invocation relation) The states after an invocation
  and after its preemption point are `XG` states: the preemption point's
  timeout and the receive that follows are message transfers. -/
  postG : ∀ (s0 : S) (a0 : A) (call blk don fp : Bool) (cptr : U64) (r : core.result.Result Unit error.Exc)
    (s1 : S) (a1 : A), EntAt st P3Ok s0 → syscall.handle_invocation st ar s0 a0 call blk don fp cptr = ok (r, s1, a1) →
    XG st T Cs Ω H Sg Scs Z P3Ok s1 ∧ ∀ (b : Bool) (s2 : S) (a2 : A),
      syscall.after_invocation st ar s1 a1 r = ok (b, s2, a2) → XG st T Cs Ω H Sg Scs Z P3Ok s2
  /-- `activate_thread`, after `schedule`. -/
  act : ∀ (Ac : Set U64) (s : S) (a : A), EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    sched.activate_thread st ar s a ⦃ s' _ => EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄
  /-- **[P] (vmchk) The placement `finish`'s `vcpu.check` needs** of a
  `TS_RUNNING_VM` current thread at an `EntryInv` state (the completion of its
  VMEnter, `vcpu.check.entry`; off `TS_RUNNING_VM` it does nothing,
  `check_of_ne`): its IPC buffer lies in the user words `U` (`hbuf`, as
  `bufAt`'s, here after `schedule`), and its bound VCPU's `PENDING` word is a
  user-class word (`hpw`, `UsrW`; P2's `VcpuUsr`). Replaces the former
  behavioural field `vmchk` (now the theorem `EntryHyps0A.vmchk`).
  `P3Place.vmpl` [P]. -/
  vmpl : ∀ (Ac : Set U64) (s : S), EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    L.mem s (stA (L.curW s)) = sched.TS_RUNNING_VM →
    -- a64: the run frame (`RunBuf`) and the run VCPU's `RUN_CALLER` word (VcpuCheckInv)
    RunBuf st U s (L.curW s) ∧
    (L.mem s (runVcpuA (L.curW s)) ≠ 0#u64 →
      UsrW st T Cs H Sg Scs Z s (core.num.U64.wrapping_add (L.mem s (runVcpuA (L.curW s))) vcpu.RUN_CALLER))
  /-- (int6; from `P3Place.xfer.buf` and `P3Place.blkU`, `EntryHypsA.of_gaps`)
  At an `XG` state the TCBs' IPC buffers lie in the user words (`BufAt`):
  what `send_signal`'s VMEnter completion (#80 / #85) needs, in
  `handle_interrupt` and `schedule`. -/
  bufAt : ∀ (Ac : Set U64) (s : S), XG st T Cs Ω H Sg Scs Z P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    BufAt st T Cs H Sg Scs Z U s
  /-- **[J] (a64) `RunVcpuInv` at an `XG` state** (as `bufAt`): what AArch64's `schedule`, `send_signal`
  and fault / timeout / receive handlers need (module docstring). -/
  rvAt : ∀ (Ac : Set U64) (s : S), XG st T Cs Ω H Sg Scs Z P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    RunVcpuInv st T s

/-- **(vmchk) `finish`'s `vcpu.check` of a `TS_RUNNING_VM` current thread keeps
`EntryInv`** (the former field `EntryHyps0A.vmchk`), from `vcpu.check.entry`
with the user words `UsrW` (from `blkU`'s `UserOK`) and `vmpl`. -/
theorem EntryHyps0A.vmchk (E : EntryHyps0A st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (hA : P0.ArchTotal ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (Ac : Set U64) (s : S) (a : A)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hv : L.mem s (stA (L.curW s)) = sched.TS_RUNNING_VM) :
    vcpu.check st ar s a (L.curW s) ⦃ s' _ => EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  have hb := EntryInv.bxi h
  have hUs := (E.blkU Ac s hb).2.usrW hb.blk
  obtain ⟨hbuf, hpw⟩ := E.vmpl Ac s h hv
  exact vcpu.check.entry (U := {b | UsrW st T Cs H Sg Scs Z s b}) hA hNt s a h (fun b hb => hb)
    (fun p z r d x1 x2 x3 x4 bi sz e1 e2 e3 e4 e5 e6 e7 e8 i hi =>
      hUs _ (hbuf p z r d x1 x2 x3 x4 bi sz e1 e2 e3 e4 e5 e6 e7 e8 i hi)) hpw

/-- `EntryHyps0A` and the invocations (`inv`), over the admissible sets `Adm`.
**Contradictory** (p1g, P1/EntryVacuous): no `BXI` state satisfies it (`blkU`); not a
specification of the kernel. -/
structure EntryHypsA (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A) (Adm : PSets → Prop)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop) : Prop
    extends EntryHyps0A st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok where
  /-- The cap invocations (`handle_invocation`: lookup, decode, perform, reply);
  a retype may grow the heap, so the post is over some admissible sets. -/
  inv : ∀ (Ac : Set U64) (s : S) (a : A) (call blk don fp : Bool) (cptr : U64), EntAt st P3Ok s →
    BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → L.cscW s ∈ Ac → L.actionW s ≠ L.curW s →
      (L.mem s (scA (L.curW s)) ≠ 0#u64 → L.cscW s = L.mem s (scA (L.curW s))) →
    syscall.handle_invocation st ar s a call blk don fp cptr ⦃ r s' _ => ∃ σ', Adm σ' ∧ ∃ Ac',
      BXI st σ'.T Cs σ'.Ω σ'.H σ'.Sg σ'.Rp σ'.Scs σ'.Nt σ'.Z Ac' s' ∧
      (∀ e, r = .Err e → CurStep st Ac Ac' s s' ∧ L.actionW s' ≠ L.curW s' ∧
        (L.mem s' (scA (L.curW s')) ≠ 0#u64 → L.cscW s' = L.mem s' (scA (L.curW s')))) ⦄

-- a64: `_A` twin (`XferOKA`) of the QueueEntry text below
/-- The entry hypotheses of an admissible set tuple (and its notifications
being the heap's). -/
abbrev EHsA (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A) (Adm : PSets → Prop) (Cs U : Set U64)
    (P3Ok : S → Prop) (σ : PSets) : Prop :=
  EntryHypsA st ar Adm σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z U P3Ok ∧ ∀ n ∈ σ.Nt, σ.H n = some .ntfn

/-- Timeout faults keep the invariants (`faults.handle_timeout.bxiA`). -/
theorem EntryHyps0A.tmo {U : Set U64} (E : EntryHyps0A st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (hA : P0.ArchTotal ar)
    (Ac : Set U64) {s0 : S} (hG0 : XG st T Cs Ω H Sg Scs Z P3Ok s0) (hc0 : L.cpu s0 ∈ Cs) :
    TmoK st ar T Cs Ω H Sg Rp Scs Nt Z Ac s0 :=
  fun s a f Q R h hB hX hSg hS w => by
    have hG := hG0.chg hc0 w
    obtain ⟨hc, hU, hcap⟩ := E.tmoOK Ac s hG ⟨⟨Q, R, h⟩, hB, hX, hSg, hS⟩
    exact WP.spec_mono (faults.handle_timeout.bxiA hA E.xfer s a _ f
      (XG.faultG hG ⟨⟨Q, R, h⟩, hB, hX, hS, hSg⟩ hU hc) ⟨⟨Q, R, h⟩, hB, hX, hS, hSg⟩ hU hc
      (hcap _ (Or.inl rfl)) (E.rvAt Ac s hG ⟨⟨Q, R, h⟩, hB, hX, hSg, hS⟩))
      fun r hr => by obtain ⟨s', a'⟩ := r; exact BlkOK.bxi (by simpa using hr)

/-- **Timeout faults keep `XG`** (a P1 lemma, `tmoXG_holds` in QueueIpcFoot,
downstream of this module: `send_ipc` keeps `XG`, its transfer by `XferOK`'s
guard and its other steps by `KW` footprints). -/
def TmoXGA (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A) : Prop :=
  ∀ (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop),
    XferOKA st ar T Cs Ω H Sg Rp Scs Nt Z U (XG st T Cs Ω H Sg Scs Z P3Ok) →
    ∀ (Ac : Set U64) (s : S) (a : A) (t : obj.Tcb) (f : error.Fault), XG st T Cs Ω H Sg Scs Z P3Ok s →
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s → UserOK st T Cs Ω H U s → CanBlock st T Ac s t →
      obj.Tcb.slot t layout.tcb.SLOT_TIMEOUT_HANDLER ⦃ sl => obj.Slot.cap st sl s ⦃ c => CapTyped H Rp Nt c ⦄ ⦄ →
      RunVcpuInv st T s →  -- a64: [J] `RunVcpuInv` (A64 `handle_timeout.bxi`)
      faults.handle_timeout st ar s a t f ⦃ s' _ => XG st T Cs Ω H Sg Scs Z P3Ok s' ⦄

/-- Timeout faults keep the invariants and `XG` (`faults.handle_timeout.bxiA`, `TmoXGA`). -/
theorem EntryHyps0A.tmoG {U : Set U64} (E : EntryHyps0A st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (hA : P0.ArchTotal ar)
    (TX : TmoXGA st ar) (Ac : Set U64) :
    TmoKG st ar T Cs Ω H Sg Rp Scs Nt Z Ac (XG st T Cs Ω H Sg Scs Z P3Ok) :=
  fun s a f Q R h hB hX hSg hS hG => by
    obtain ⟨hc, hU, hcap⟩ := E.tmoOK Ac s hG ⟨⟨Q, R, h⟩, hB, hX, hSg, hS⟩
    have hRV := E.rvAt Ac s hG ⟨⟨Q, R, h⟩, hB, hX, hSg, hS⟩
    exact WP.spec_mono (WP.spec_and (faults.handle_timeout.bxiA hA E.xfer s a _ f
      (XG.faultG hG ⟨⟨Q, R, h⟩, hB, hX, hS, hSg⟩ hU hc) ⟨⟨Q, R, h⟩, hB, hX, hS, hSg⟩ hU hc
      (hcap _ (Or.inl rfl)) hRV)
      (TX T Cs Ω H Sg Rp Scs Nt Z U P3Ok E.xfer Ac s a _ f hG ⟨⟨Q, R, h⟩, hB, hX, hS, hSg⟩ hU hc
        (hcap _ (Or.inl rfl)) hRV))
      fun r hr => by
        obtain ⟨s', a'⟩ := r
        simp only [WP.uncurry'_pair] at hr ⊢
        exact ⟨BlkOK.bxi hr.1, hr.2⟩

/-- Faults of the current thread keep the invariants (`faults.handle_fault.bxiA`,
from `tmoOK` and `xfer`). -/
theorem EntryHyps0A.fault {U : Set U64} (E : EntryHyps0A st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (hA : P0.ArchTotal ar)
    (Ac : Set U64) (s : S) (a : A) (f : error.Fault) (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) :
    faults.handle_fault st ar s a (L.curW s) f ⦃ s' _ => ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄ := by
  obtain ⟨hc, hU, hcap⟩ := E.tmoOK Ac s hG h
  exact WP.spec_mono (faults.handle_fault.bxiA hA E.xfer s a _ f (XG.faultG hG h.blk hU hc) h.blk hU hc
    (hcap _ (Or.inr rfl)) (E.rvAt Ac s hG h))
    fun r hr => by obtain ⟨s', a'⟩ := r; exact ⟨Ac, BlkOK.bxi (by simpa using hr)⟩

/-- Receives keep the invariants (`syscall.handle_recv.bxiA`). -/
theorem EntryHyps0A.recv {U : Set U64} (E : EntryHyps0A st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (hA : P0.ArchTotal ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (Ac : Set U64) (s : S) (a : A) (blk rep : Bool)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) :
    syscall.handle_recv st ar s a blk rep ⦃ s' _ => ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄ := by
  obtain ⟨hc, hU⟩ := E.blkU Ac s h
  obtain ⟨hlk, h3, hvm⟩ := E.recvOK Ac s hG h
  exact syscall.handle_recv.bxiA hA hNt E.xfer s a blk rep h (XG.recvG hG h hc) hU hc hlk h3
    (fun f => E.fault hA Ac s a f h hG) (E.rvAt Ac s hG h) hvm

-- a64: `_A` twin (`XferOKA`) of the QueueEntry text below
/-- `finish`: `schedule` establishes `EntryInv`, `activate_thread` keeps it. -/
theorem syscall.finish.entryA (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (E : EntryHyps0A st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) {Ac : Set U64} (s : S) (a : A)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) :
    syscall.finish st ar s a ⦃ s' _ => ∃ Ac', EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄ := by
  rw [finish_eq_old]
  refine WP.spec_bind (Pₘ := fun r : S × A => EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac r.1) ?_ ?_
  · unfold syscall.finish_old
    have hBA := E.bufAt Ac s hG h
    have hRV := E.rvAt Ac s hG h
    obtain ⟨⟨Q, R, h0⟩, hB, hX, hSg, hS⟩ := h
    refine WP.spec_bind (sched.schedule.entry_ib hA hNt s a Q R h0 hB hS hX hSg hBA hRV) ?_
    rintro ⟨s1, a1⟩ h1
    try simp only [WP.uncurry'_pair]
    exact WP.spec_mono (E.act Ac s1 a1 h1) fun r hr => by obtain ⟨s', a'⟩ := r; exact hr
  · rintro ⟨s2, a2⟩ h2
    show (do let t ← sched.cur_thread st s2; vcpu.check st ar s2 a2 t) ⦃ _ ⦄
    rw [cur_thread_ok]; simp only [bind_ok]
    by_cases hv : L.mem s2 (stA (L.curW s2)) = sched.TS_RUNNING_VM
    · exact WP.spec_mono (E.vmchk hA hNt Ac s2 a2 h2 hv) fun r hr => by obtain ⟨s', a'⟩ := r; exact ⟨Ac, hr⟩
    · rw [check_of_ne ar s2 a2 _ hv]; exact (WP.spec_ok _).2 ⟨Ac, h2⟩

/-- `after_invocation`: the preemption point of a preempted invocation, with
`HCur`, then a pending interrupt. -/
theorem syscall.after_invocation.bxiA (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (TX : TmoXGA st ar) (E : EntryHyps0A st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    {Ac : Set U64} (s : S) (a : A) (r : core.result.Result Unit error.Exc)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s)
    (hc : ∀ e, r = .Err e → HCur st Ac s)
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
    refine WP.spec_bind (syscall.mcs_preemption_point.allG hA s a Q R h0 hB hX hSg hS hcsc hna (hc e rfl)
      (fun _ _ g f => XG.foot g f) hG (E.tmoG hA TX Ac)) ?_
    rintro ⟨s1, a1⟩ ⟨h1, g1⟩
    try simp only [WP.uncurry'_pair]
    refine WP.spec_bind (hA.take_pending_irq a1) ?_
    rintro ⟨irq, a2⟩ -
    try simp only [WP.uncurry'_pair]
    unfold syscall.check_interrupt
    refine WP.spec_bind (Pₘ := fun r : S × A => ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' r.1) ?_ ?_
    · split
      · exact WP.spec_mono (interrupt.handle_interrupt.bxi hA hNt s1 a2 irq h1 (E.irqcap Ac s1 g1 h1) (E.bufAt Ac s1 g1 h1)
          (E.rvAt Ac s1 g1 h1)) fun r hr => by
          obtain ⟨s', a'⟩ := r; exact ⟨Ac, by simpa using hr⟩
      · exact (WP.spec_ok _).2 ⟨Ac, h1⟩
    · rintro ⟨s2, a3⟩ h2
      exact (WP.spec_ok _).2 h2

/-- `dispatch_syscall`, after a successful budget check. -/
theorem syscall.dispatch_syscall.bxiA (hA : P0.ArchTotal ar) (TX : TmoXGA st ar) {Adm : PSets → Prop}
    (EH : ∀ σ, Adm σ → EHsA st ar Adm Cs U P3Ok σ) (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩)
    {Ac : Set U64} (s : S) (a : A) (number : I64) (he : EntAt st P3Ok s) (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hcA : L.cscW s ∈ Ac) (hna : L.actionW s ≠ L.curW s)
    (hcsc : L.mem s (scA (L.curW s)) ≠ 0#u64 → L.cscW s = L.mem s (scA (L.curW s))) :
    syscall.dispatch_syscall st ar s a number ⦃ s' _ => ∃ σ', Adm σ' ∧ ∃ Ac', BXIs st Cs σ' Ac' s' ⦄ := by
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
          ∃ σ', Adm σ' ∧ ∃ Ac', BXIs st Cs σ' Ac' s' ⦄ := by
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
    · exact WP.spec_mono (E2.recv hA hNt2 Ac2 s2 a2 b1 b2 h2 g2) fun _ ⟨Ac3, h3⟩ => ⟨σ2, hσ2, Ac3, h3⟩
    · exact (WP.spec_ok _).2 ⟨σ2, hσ2, Ac2, h2⟩
  have IS : ∀ (call blk don fp : Bool) (cptr : U64),
      (do
        let (r, s1, a1) ← syscall.handle_invocation st ar s a call blk don fp cptr
        let (_, s2, a2) ← syscall.after_invocation st ar s1 a1 r
        ok (s2, a2)) ⦃ s' _ => ∃ σ', Adm σ' ∧ ∃ Ac', BXIs st Cs σ' Ac' s' ⦄ := by
    intro call blk don fp cptr
    refine WP.spec_bind (IA call blk don fp cptr) ?_
    rintro ⟨r, s1, a1⟩ hh
    simp only [WP.uncurry'_pair] at hh ⊢
    refine WP.spec_bind hh ?_
    rintro ⟨b, s2, a2⟩ ⟨σ2, hσ2, Ac2, h2, -⟩
    exact (WP.spec_ok _).2 ⟨σ2, hσ2, Ac2, h2⟩
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
  · rw [if_pos c4]; exact WP.spec_mono (E.recv hA hNt Ac s a _ _ h he.xg) fun _ ⟨Ac', h'⟩ => ⟨_, hσ, Ac', h'⟩
  rw [if_neg c4]
  by_cases c5 : number = fl4_abi.syscall.SysNBRecv
  · rw [if_pos c5]; exact WP.spec_mono (E.recv hA hNt Ac s a _ _ h he.xg) fun _ ⟨Ac', h'⟩ => ⟨_, hσ, Ac', h'⟩
  rw [if_neg c5]
  by_cases c6 : number = fl4_abi.syscall.SysWait
  · rw [if_pos c6]; exact WP.spec_mono (E.recv hA hNt Ac s a _ _ h he.xg) fun _ ⟨Ac', h'⟩ => ⟨_, hσ, Ac', h'⟩
  rw [if_neg c6]
  by_cases c7 : number = fl4_abi.syscall.SysNBWait
  · rw [if_pos c7]; exact WP.spec_mono (E.recv hA hNt Ac s a _ _ h he.xg) fun _ ⟨Ac', h'⟩ => ⟨_, hσ, Ac', h'⟩
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
  · rw [if_pos c11]; exact WP.spec_mono (syscall.handle_yield.bxi hA s a h hcA hna hcsc
      (E.tmo hA Ac he.xg h.1.choose_spec.choose_spec.cur)) fun r hr => by
      obtain ⟨s', a'⟩ := r; exact ⟨_, hσ, Ac, hr⟩
  rw [if_neg c11]
  exact (WP.spec_ok _).2 ⟨_, hσ, Ac, h⟩

end

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}
variable {A : Type _} {ar : machine.Arch A} {P3Ok : S → Prop}

-- a64: `_A` twin (`XferOKA`) of the QueueKeeps text below
/-- **`EntryHyps` with `act` discharged** (`sched.activate_thread.entry`);
`fault` is no longer a field (`EntryHypsA.fault`, from `tmoOK` and `xfer`). -/
theorem EntryHypsA.of {U : Set U64} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (xfer : XferOKA st ar T Cs Ω H Sg Rp Scs Nt Z U (XG st T Cs Ω H Sg Scs Z P3Ok))
    (tmoOK : ∀ (Ac : Set U64) (s : S), XG st T Cs Ω H Sg Scs Z P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
      CanBlock st T Ac s (L.curW s) ∧ UserOK st T Cs Ω H U s ∧
      ∀ i, (i = layout.tcb.SLOT_TIMEOUT_HANDLER ∨ i = layout.tcb.SLOT_FAULT_HANDLER) →
        obj.Tcb.slot (L.curW s) i ⦃ sl => obj.Slot.cap st sl s ⦃ c => CapTyped H Rp Nt c ⦄ ⦄)
    (inv : ∀ (Ac : Set U64) (s : S) (a : A) (call blk don fp : Bool) (cptr : U64), EntAt st P3Ok s →
      BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → L.cscW s ∈ Ac → L.actionW s ≠ L.curW s →
      (L.mem s (scA (L.curW s)) ≠ 0#u64 → L.cscW s = L.mem s (scA (L.curW s))) →
      syscall.handle_invocation st ar s a call blk don fp cptr ⦃ r s' _ => ∃ σ', Adm σ' ∧ ∃ Ac',
        BXIs st Cs σ' Ac' s' ∧
        (∀ e, r = .Err e → CurStep st Ac Ac' s s' ∧ L.actionW s' ≠ L.curW s' ∧
          (L.mem s' (scA (L.curW s')) ≠ 0#u64 → L.cscW s' = L.mem s' (scA (L.curW s')))) ⦄)
    (blkU : ∀ (Ac : Set U64) (s : S), BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
      CanBlock st T Ac s (L.curW s) ∧ UserOK st T Cs Ω H U s)
    (recvOK : ∀ (Ac : Set U64) (s : S), XG st T Cs Ω H Sg Scs Z P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
      (∀ cptr, cspace.lookup_cap st s (L.curW s) cptr ⦃ r => ∀ c, r = .Ok c → CapTyped H Rp Nt c ⦄) ∧
      (∀ n ∈ Nt, L.epState s n ≠ 3#u64) ∧
      L.mem s (stA (L.curW s)) ≠ sched.TS_RUNNING_VM)  -- a64: `EntryHyps0A.recvOK`'s A64 conjunct
    (irqcap : ∀ (Ac : Set U64) (s : S), XG st T Cs Ω H Sg Scs Z P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
      ∀ i : U64, i.val < 5376 →  -- a64: 5376 IRQs
      obj.Slot.cap st (irqSlotA (L.ksb s) i) s ⦃ c => ∀ ptr b0 b1 b2, c = .Notification ptr b0 b1 b2 → ptr ∈ Nt ⦄)
    (debug : ∀ (Ac : Set U64) (s : S) (a : A) (n : I64), EntAt st P3Ok s → EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s →
      syscall.debug_syscall st ar s a (L.curW s) n ⦃ _ s' _ => ∃ Ac', EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄)
    (postG : ∀ (s0 : S) (a0 : A) (call blk don fp : Bool) (cptr : U64) (r : core.result.Result Unit error.Exc)
      (s1 : S) (a1 : A), EntAt st P3Ok s0 → syscall.handle_invocation st ar s0 a0 call blk don fp cptr = ok (r, s1, a1) →
      XG st T Cs Ω H Sg Scs Z P3Ok s1 ∧ ∀ (b : Bool) (s2 : S) (a2 : A),
        syscall.after_invocation st ar s1 a1 r = ok (b, s2, a2) → XG st T Cs Ω H Sg Scs Z P3Ok s2)
    (vmpl : ∀ (Ac : Set U64) (s : S), EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s →
      L.mem s (stA (L.curW s)) = sched.TS_RUNNING_VM →
      RunBuf st U s (L.curW s) ∧  -- a64: A64 `vmpl` [P] (QueueEntry)
      (L.mem s (runVcpuA (L.curW s)) ≠ 0#u64 →
        UsrW st T Cs H Sg Scs Z s (core.num.U64.wrapping_add (L.mem s (runVcpuA (L.curW s))) vcpu.RUN_CALLER)))
    (bufAt : ∀ (Ac : Set U64) (s : S), XG st T Cs Ω H Sg Scs Z P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
      BufAt st T Cs H Sg Scs Z U s)
    (rvAt : ∀ (Ac : Set U64) (s : S), XG st T Cs Ω H Sg Scs Z P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
      RunVcpuInv st T s) :  -- a64: [J] `EntryHyps0A.rvAt` (QueueEntry)
    EntryHypsA st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok :=
  ⟨⟨xfer, tmoOK, blkU, recvOK, irqcap, debug, postG, fun Ac s a h =>
    WP.spec_mono (sched.activate_thread.entry hA s a h) fun r hr => by obtain ⟨s', a'⟩ := r; simpa using hr,
    vmpl, bufAt, rvAt⟩, inv⟩

end

end Fl4ProofsA64.P1
