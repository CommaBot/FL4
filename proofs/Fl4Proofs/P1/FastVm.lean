/-
# The l4h guest page-fault fast paths (FL4 #71, pf1)

`fastpath_vm.vm_fault` and `fastpath_vm.reply_recv_vm_found` are
`fastpath.fault` / `fastpath.reply_recv_found` with a VM fault in place of an
UnknownSyscall fault. In the extraction:

* `vm_fault` is `fastpath.fault` with `set_fault … (UnknownSyscall n)` read as
  `set_fault … f` and the message label `UnknownSyscall` read as `VMFault`;
* `reply_recv_vm_found` is `reply_recv_found` with the receiver's fault-type
  check `UnknownSyscall` read as `VMFault` (the write part is the same text,
  m64's `rrTail`).

So m58–m66's meeting-point proofs carry over once stated over the fault `f`,
the state `s2` that `set_fault f` writes and the label `ty` (fault half), and
over the fault type the reply answers (ReplyRecv half). Those general forms
live beside the originals, which are now their instances at
`UnknownSyscall` with unchanged statements: FastFault `fastFaultG` /
`fault_accG` / `faultTailG` / `faultTail2G` / `faultTailG_eq` /
`faultTail2G_eq` / `handle_fault_preG` / `FaultReadsG` (`FaultReads` an
abbrev) / `sfG` / `set_fault_vm`, FastFin `FaultOKG` / `fault_sameG`, FastFaultInv
`faultReads_ofG`, FastFinInv `faultOK_ofG`, FastTailFault `faultNvm_tailG`.
Here:

* `vm_fault_acc` (`fault_accG` at `VMFault`);
* **`vm_fault_same`**: an accepted `fastpath_vm.vm_fault` run ends where
  `handle_fault f` + `finish` end, given `FaultOKG … VMFault` and the end-state
  read `VmFaultNvm` (the analogue of `FaultOK` / `FaultNvm`);
* **`vm_local_same`**: an accepted `syscall.handle_vm_fault_local` run ends where
  the general entry `syscall.handle_vm_fault` ends (`budget_ok`, after the same
  timestamp update, passes without writing: `check_budget_restart_suf`);
* **`vm_fault_decline`**, **`reply_recv_vm_found_decline`**: a `false` return
  is the entry state; **`vm_local_decline`**: a declined
  `handle_vm_fault_local` has written at most its `update_timestamp`;
* ReplyRecv: the #56 derivation is stated over the receiver's fault type `ty`
  (FastRR's `RRChecksG`, FastRRSame's `RRR3G` / `RRPreG` / `rr_found_sameG`,
  FastRRSync's `do_reply_transfer_rrG`, the `…G` lemmas of FastRREnt /
  FastRRFoot / FastRRLk / FastTailRR; the #56 names are their instances at
  `UnknownSyscall`); here `reply_recv_vm_found_acc` (the write part is m64's
  `rrTail`), `hfr_vm` (a VM fault's reply restarts the receiver and writes
  nothing; the `HfrRestart` instance at `VMFault`) and **`rr_vm_same`**: an
  accepted `reply_recv_vm_found` run from the dispatch state, with `found`
  what `reply_caps` returns there, ends where `dispatch_syscall …
  SysReplyRecv` + `finish` end, given `RRPreG … VMFault`.
-/
import Fl4Proofs.P1.FastRRSame
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

theorem vm_ne_null : fl4_abi.consts.fault.VMFault ≠ fl4_abi.consts.fault.NullFault := by
  unfold fl4_abi.consts.fault.VMFault fl4_abi.consts.fault.NullFault; decide

/-! ## Declines -/

section
variable {S : Type _} {A : Type _} (st : machine.Store S) (ar : machine.Arch A)

/-- **`fastpath_vm.vm_fault` declines without a trace.** -/
theorem vm_fault_decline {s : S} {a : A} {t : obj.Tcb} {f : error.Fault} {s' : S} {a' : A}
    (h : fastpath_vm.vm_fault st ar s a t f = ok (false, s', a')) : s' = s ∧ a' = a := by
  have h' := spec_of_eq_fd h
  clear h
  unfold fastpath_vm.vm_fault at h'
  revert h'
  repeat' (first
    | (with_reducible_and_instances refine spec_bind_imp (fun _ => ?_)
       try simp only [uncurry_eta_fd])
    | (with_reducible_and_instances refine spec_bind_imp' (fun _ => ?_)
       try simp only [uncurry_eta_fd])
    | (with_reducible refine spec_ite_imp (fun _ => ?_) (fun _ => ?_))
    | split
    | (refine spec_bind_imp (fun _ => ?_)
       try simp only [uncurry_eta_fd]))
  all_goals intro h'
  all_goals rw [WP.spec_ok] at h'
  all_goals first
    | exact ⟨(congrArg (fun r => r.2.1) h').symm, (congrArg (fun r => r.2.2) h').symm⟩
    | simp at h'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`fastpath_vm.reply_recv_vm_found` declines without a trace.** -/
theorem reply_recv_vm_found_decline {s : S} {a : A} {t : obj.Tcb} {rp ep : Std.U64} {s' : S} {a' : A}
    (h : fastpath_vm.reply_recv_vm_found st ar s a t rp ep = ok (false, s', a')) : s' = s ∧ a' = a := by
  have h' := spec_of_eq_fd h
  clear h
  unfold fastpath_vm.reply_recv_vm_found at h'
  revert h'
  repeat' (first
    | (with_reducible_and_instances refine spec_bind_imp (fun _ => ?_)
       try simp only [uncurry_eta_fd])
    | (with_reducible_and_instances refine spec_bind_imp' (fun _ => ?_)
       try simp only [uncurry_eta_fd])
    | (with_reducible refine spec_ite_imp (fun _ => ?_) (fun _ => ?_))
    | split
    | (refine spec_bind_imp (fun _ => ?_)
       try simp only [uncurry_eta_fd]))
  all_goals intro h'
  all_goals rw [WP.spec_ok] at h'
  all_goals first
    | exact ⟨(congrArg (fun r => r.2.1) h').symm, (congrArg (fun r => r.2.2) h').symm⟩
    | simp at h'

end

/-! ## The fault half, generalised over the fault -/

section
variable {S : Type _} {A : Type _} (st : machine.Store S) (ar : machine.Arch A)

/-- **Inversion of an accepted `fastpath_vm.vm_fault`** (`fault_accG`: the
VM fast path is `fastFaultG … f VMFault` by definition). -/
theorem vm_fault_acc {s : S} {a : A} {t : obj.Tcb} {f : error.Fault} {s' : S} {a' : A}
    (h : fastpath_vm.vm_fault st ar s a t f = ok (true, s', a')) :
    ∃ ptr badge dest r, FaultChecks st s t ptr badge dest r ∧
      faultTailG st ar s a t f fl4_abi.consts.fault.VMFault ptr badge dest r = ok (true, s', a') :=
  fault_accG st ar (f := f) (ty := fl4_abi.consts.fault.VMFault) h

end

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A) [L : LawfulStore st]

/-- **(#57) The thread an accepted `vm_fault` switches to is not
`TS_RUNNING_VM`** (m62's `FaultNvm` for the VM fast path). -/
def VmFaultNvm (s : S) (a : A) (t : obj.Tcb) (f : error.Fault) : Prop :=
  ∀ sF aF, fastpath_vm.vm_fault st ar s a t f = ok (true, sF, aF) →
    L.mem sF (stA (L.curW sF)) ≠ sched.TS_RUNNING_VM

/-- **`vm_fault_same`**: an accepted `fastpath_vm.vm_fault` run ends exactly
where the general `handle_fault f` + `finish` ends (under `StoreExt`, as
states; the Arch value the same), given the general path's reads
(`FaultOKG … VMFault`, `VmFaultNvm`). -/
theorem vm_fault_same (hX : StoreExt st) {s : S} {a : A} {t : obj.Tcb} {f : error.Fault} {sF : S} {aF : A}
    (h : fastpath_vm.vm_fault st ar s a t f = ok (true, sF, aF))
    (hR : FaultOKG (L := L) ar s a t f fl4_abi.consts.fault.VMFault)
    (hV : VmFaultNvm (L := L) ar s a t f) :
    (do
      let (s2, a2) ← faults.handle_fault st ar s a t f
      syscall.finish st ar s2 a2) = ok (sF, aF) := by
  obtain ⟨ptr, badge, dest, r, hc, hfast⟩ := vm_fault_acc st ar h
  exact fault_sameG ar hX vm_ne_null hc hfast hR (hV sF aF h)

/-! ## The entry `handle_vm_fault_local` -/

/-- `check_budget_restart` with budget left (one domain: never expired) writes
nothing and passes. -/
theorem check_budget_restart_suf {s : S} {a : A} {csc c : U64}
    (ecsc : sched.cur_sc st s = ok csc) (ec : sched.consumed st s = ok c)
    (eb : sporadic.sufficient st ar s a csc c = ok true) :
    sched.check_budget_restart st ar s a = ok (true, s, a) := by
  unfold sched.check_budget_restart sched.check_budget
  rw [ecsc]; simp only [bind_ok]
  rw [ec]; simp only [bind_ok]
  rw [eb]; simp only [bind_ok, ↓reduceIte]
  unfold sched.is_cur_domain_expired
  simp only [num_domains_one, ↓reduceIte, bind_ok, uncurry_apply_pair]
  rw [cur_thread_ok]
  simp

/-- The general path's reads for `handle_vm_fault s a`: at the state after a
passing `budget_ok`, for the current thread and every VM fault. -/
def VmFaultOK (s : S) (a : A) : Prop :=
  ∀ s1 a1 t addr fsr ins, syscall.budget_ok st ar s a = ok (true, s1, a1) → sched.cur_thread st s1 = ok t →
    FaultOKG (L := L) ar s1 a1 t (error.Fault.VmFault addr fsr ins) fl4_abi.consts.fault.VMFault ∧
      VmFaultNvm (L := L) ar s1 a1 t (error.Fault.VmFault addr fsr ins)

theorem num_domains_ne_one_false : (layout.NUM_DOMAINS != 1#u64) = false := by
  simp [layout.NUM_DOMAINS, fl4_abi.config.NUM_DOMAINS]

/-- **`vm_local_same`: the VM-fault entry beside the serial gate, where its
fast path ran, is the general entry** `syscall.handle_vm_fault` (the same
`update_timestamp`; `budget_ok` then passes without writing, since the local
entry checked `sufficient` at the same state; then `vm_fault_same`). -/
theorem vm_local_same (hX : StoreExt st) {s : S} {a : A} {addr code : U64} {s' : S} {a' : A}
    (hF : VmFaultOK (L := L) ar s a)
    (h : syscall.handle_vm_fault_local st ar s a addr code = ok (true, s', a')) :
    syscall.handle_vm_fault st ar s a addr code = ok (s', a') := by
  unfold syscall.handle_vm_fault_local at h
  rw [num_domains_ne_one_false] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨⟨s1, a1⟩, e1, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨csc, ecsc, h⟩ := bind_eq_ok h
  obtain ⟨c, ec, h⟩ := bind_eq_ok h
  obtain ⟨b, eb, h⟩ := bind_eq_ok h
  cases b
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨t, et, h⟩ := bind_eq_ok h
  obtain ⟨i1, ei1, h⟩ := bind_eq_ok h
  obtain ⟨i2, ei2, h⟩ := bind_eq_ok h
  obtain ⟨f, ef, h⟩ := bind_eq_ok h
  have hb : syscall.budget_ok st ar s a = ok (true, s1, a1) := by
    unfold syscall.budget_ok
    rw [e1]; simp only [bind_ok, uncurry_apply_pair]
    exact check_budget_restart_suf ar ecsc ec eb
  have hf : f = error.Fault.VmFault addr code (i2 != 0#u64) := by
    unfold vspace.vm_fault at ef; exact (ok_inj_ff ef).symm
  subst hf
  obtain ⟨hR, hV⟩ := hF s1 a1 t addr code (i2 != 0#u64) hb et
  have hs := vm_fault_same ar hX h hR hV
  obtain ⟨⟨p1, p2⟩, ehf, hs⟩ := bind_eq_ok hs
  try simp only [uncurry_apply_pair] at hs
  unfold syscall.handle_vm_fault
  rw [hb]; simp only [bind_ok, uncurry_apply_pair, ↓reduceIte]
  rw [et]; simp only [bind_ok]
  rw [ei1]; simp only [bind_ok]
  rw [ei2]; simp only [bind_ok]
  rw [ef]; simp only [bind_ok]
  rw [ehf]; simp only [bind_ok, uncurry_apply_pair]
  exact hs

/-- **A declined `handle_vm_fault_local` has written at most its
`update_timestamp`** (fl4-sync then runs the general entry, whose own
`update_timestamp` follows it). -/
theorem vm_local_decline {s : S} {a : A} {addr code : U64} {s' : S} {a' : A}
    (h : syscall.handle_vm_fault_local st ar s a addr code = ok (false, s', a')) :
    sched.update_timestamp st ar s a = ok (s', a') := by
  unfold syscall.handle_vm_fault_local at h
  rw [num_domains_ne_one_false] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨⟨s1, a1⟩, e1, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨csc, -, h⟩ := bind_eq_ok h
  obtain ⟨c, -, h⟩ := bind_eq_ok h
  obtain ⟨b, -, h⟩ := bind_eq_ok h
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at h
    have e := ok_inj_ff h
    simp only [Prod.mk.injEq, true_and] at e
    obtain ⟨rfl, rfl⟩ := e
    exact e1
  · simp only [↓reduceIte] at h
    obtain ⟨t, -, h⟩ := bind_eq_ok h
    obtain ⟨i1, -, h⟩ := bind_eq_ok h
    obtain ⟨i2, -, h⟩ := bind_eq_ok h
    obtain ⟨f, -, h⟩ := bind_eq_ok h
    obtain ⟨rfl, rfl⟩ := vm_fault_decline st ar h
    exact e1

end

/-! ## The ReplyRecv half for a VM fault -/

section
variable {S : Type _} {A : Type _} (st : machine.Store S) (ar : machine.Arch A)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **Inversion of an accepted `fastpath_vm.reply_recv_vm_found`** (as
`reply_recv_found_acc`): its checks held at the entry state and the run is
m64's `rrTail` from there. -/
theorem reply_recv_vm_found_acc {s : S} {a : A} {t : obj.Tcb} {rptr ep_ptr : Std.U64} {s' : S} {a' : A}
    (h : fastpath_vm.reply_recv_vm_found st ar s a t rptr ep_ptr = ok (true, s', a')) :
    ∃ u usc, RRChecksG st ar fl4_abi.consts.fault.VMFault s a t rptr ep_ptr u usc ∧
      rrTail st ar s a t rptr ep_ptr u usc = ok (true, s', a') := by
  unfold fastpath_vm.reply_recv_vm_found at h
  revert h
  repeat' (first
    | (rr_at_tail; intro h; refine ⟨_, _, ?_, h⟩; clear h)
    | (with_reducible_and_instances refine eq_bind_imp (fun _ _ => ?_))
    | (with_reducible_and_instances refine eq_bind_imp' (fun _ _ => ?_))
    | (with_reducible refine eq_ite_imp (fun _ => ?_) (fun _ => ?_))
    | (intro h; simp at h; done))
  all_goals
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | assumption
    | exact ⟨_, ‹_›, ‹_›⟩
    | exact ⟨_, ‹_›, ‹_›, ‹_›⟩
    | exact Or.inl ⟨_, ‹_›, ‹_›⟩
    | exact Or.inr ⟨_, ‹_›, ‹_›, _, ‹_›, ‹_›⟩
    | exact Or.inr ⟨_, ‹_›, ‹_›, _, ‹_›, ‹_›, _, ‹_›, Or.inl ‹_›⟩
    | exact Or.inr ⟨_, ‹_›, ‹_›, _, ‹_›, ‹_›, _, ‹_›, Or.inr ⟨‹_›, _, ‹_›, ‹_›⟩⟩
    | exact ⟨_, _, _, ‹_›, ‹_›, ‹_›, Or.inl ‹_›⟩
    | exact ⟨_, _, _, ‹_›, ‹_›, ‹_›, Or.inr ⟨‹_›, _, _, _, ‹_›, ‹_›, ‹_›, ‹_›⟩⟩

/-- **R3 / R7 for a VM fault's reply** (faults.rs: "VM faults always restart
the thread"): `handle_fault_reply` restarts the receiver and returns the
state and the Arch value unchanged, whatever the label. -/
theorem hfr_vm {s : S} {a : A} {rcv snd : obj.Tcb} {restart : Bool} {s4 : S} {a4 : A}
    (hty : obj.Tcb.fault_type st rcv s = ok fl4_abi.consts.fault.VMFault)
    (h : faults.handle_fault_reply st ar s a rcv snd = ok (restart, s4, a4)) :
    restart = true ∧ s4 = s ∧ a4 = a := by
  unfold faults.handle_fault_reply at h
  obtain ⟨tag, -, h⟩ := bind_eq_ok h
  try dsimp only at h
  rw [hty] at h
  simp only [bind_ok] at h
  have c1 : ¬ fl4_abi.consts.fault.VMFault = fl4_abi.consts.fault.CapFault := by
    unfold fl4_abi.consts.fault.VMFault fl4_abi.consts.fault.CapFault; decide
  have c2 : ¬ fl4_abi.consts.fault.VMFault = fl4_abi.consts.fault.UnknownSyscall := by
    unfold fl4_abi.consts.fault.VMFault fl4_abi.consts.fault.UnknownSyscall; decide
  have c3 : ¬ fl4_abi.consts.fault.VMFault = fl4_abi.consts.fault.UserException := by
    unfold fl4_abi.consts.fault.VMFault fl4_abi.consts.fault.UserException; decide
  have c4 : ¬ fl4_abi.consts.fault.VMFault = fl4_abi.consts.fault.Timeout := by
    unfold fl4_abi.consts.fault.VMFault fl4_abi.consts.fault.Timeout; decide
  have c5 : ¬ fl4_abi.consts.fault.VMFault = fl4_abi.consts.fault.DebugException := by
    unfold fl4_abi.consts.fault.VMFault fl4_abi.consts.fault.DebugException; decide
  rw [if_neg c1, if_neg c2, if_neg c3, if_neg c4, if_neg c5] at h
  have e := ok_inj_ff h
  simp only [Prod.mk.injEq] at e
  obtain ⟨e1, e2, e3⟩ := e
  exact ⟨e1.symm, e2.symm, e3.symm⟩

instance hfrRestart_vm : HfrRestart st ar fl4_abi.consts.fault.VMFault :=
  ⟨fun hty _ h => ⟨(hfr_vm st ar hty h).1, (hfr_vm st ar hty h).2.2⟩⟩

end

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A) [L : LawfulStore st]

/-- **`rr_vm_same`: the accepted VM-fault ReplyRecv fast path ends where the
general path ends**: from the dispatch state `X0`, with `(rptr, ep)` what
`reply_caps` returns for the current thread there (fl4-sync's `found`), an
accepted `reply_recv_vm_found` ends where `dispatch_syscall … SysReplyRecv`
then `finish` end, given the read bundle `RRPreG … VMFault` (m66's `rr_same`
through `rr_found_sameG`). -/
theorem rr_vm_same {X0 s' : S} {a a' : A} {t rptr ep : U64}
    (hct : sched.cur_thread st X0 = ok t) (hrc : fastpath.reply_caps st X0 t = ok (some (rptr, ep)))
    (hf : fastpath_vm.reply_recv_vm_found st ar X0 a t rptr ep = ok (true, s', a'))
    (hP : RRPreG (L := L) ar fl4_abi.consts.fault.VMFault X0 a) :
    ∃ X a'', syscall.dispatch_syscall st ar X0 a fl4_abi.syscall.SysReplyRecv = ok (X, a'') ∧
      syscall.finish st ar X a'' = ok (s', a') := by
  obtain ⟨u, usc, hC, hT⟩ := reply_recv_vm_found_acc st ar hf
  exact rr_found_sameG ar vm_ne_null hct hrc hC hT hP

end

end Fl4Proofs.P1
