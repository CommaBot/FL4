/-
P3 (line stpost, generation 9): **the accepted VM ReplyRecv entry beside the gate at stable ghosts**
(`syscall.handle_reply_recv_vm_local`, U29Vm's second clause; StPostRRReach's route for the
UnknownSyscall ReplyRecv fast path, at the fault type `VMFault`).

fl4-sync's VM ReplyRecv entry (`local_syscall` with `found = reply_caps` at the entry state) runs
`fastpath_vm.reply_recv_vm_found` after the general entry's prefix; where it returns `true` it ends
where `handle_syscall … SysReplyRecv` ends (P1 `rr_vm_local_same`): there the UnknownSyscall fast path
declines and the general path runs (`dispatch_syscall`'s ReplyRecv arm: the Reply-cap invocation to a
VM-faulted receiver, then the receive). Every P1 fact the gen-4 route reads is already generic in the
fault type (`RRChecksG`, `RRPreG`, `rrPl_lkG`, `rr_x8G`, `do_reply_transfer_rrG`, `rr_ntfnSc8`), so:

* `P1.rr_vm_local_acc`: an accepted `handle_reply_recv_vm_local` reaches, at the general entry's
  dispatch state (after the `FAULT_IP` write and a passing `budget_ok`), a state where the current
  thread's `reply_caps` is `found` and `reply_recv_vm_found` accepts (`rr_vm_local_same`'s walk,
  `rr_prefix_keep`).
* `rrMidVm_of`: StPostRRMid's `rrMid_of` from `reply_recv_vm_found`'s acceptance
  (`reply_recv_vm_found_acc`, `hty0 := vm_ne_null`).
* `kernel_entry_rrVmSt`: StPostRRTop's `kernel_entry_rrSt` with that `hacc`, `hRPd : RRPreAtG VMFault`
  and `rrMidVm_of` (verbatim otherwise: `dispatch_replyRecvJStF` does not read the fault type).
* **`kernel_entry_rrVm_localSt17`**: from `JReachU17` and given `JAtZ Z H Cs` (with `VxE Z`), under
  U29Vm's ReplyRecv clause inputs that the route reads (`hct`, `hn`, `hflag`, `hFin : KFinAtR13`, fl4-sync's
  `found` contract `hfd`; not `hK` / `hDec`), an accepted run ends at a `fl4KernelEntrySyscall true
  .sysReplyRecv` outcome that is `JReachU17` **and** `JStab Z H Cs`. `RRPreAtG VMFault` by
  `JAtZ.rrPreAtG`; `handle_syscall_old` to `handle_syscall` by `FastAcc.of_rrpre` (the UnknownSyscall
  bundle `JAtZ.rrPreAt`, as gen 4), to the local entry by `rr_vm_local_same`; `JReachU17` by
  `JReachU3.step` and the three spec facts, as `kernel_entry_rr_localSt17`.

Premises: a subset of U29's platform facts (`hSX : StoreExt` [P] as U29); no new premise.
-/
import Fl4Proofs.P3.StPostRRReach
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A) [L : LawfulStore st]

set_option maxHeartbeats 1600000 in
/-- (stpost) **An accepted VM ReplyRecv run beside the gate accepts at its dispatch state** (module
docstring; `rr_vm_local_same`'s walk). -/
theorem rr_vm_local_acc (hA : P0.ArchTotal ar) {T Cs Sg : Set U64} {s s' : S} {a a' : A}
    {found : U64 × U64}
    {Ω Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hCn : ∀ t, sched.cur_thread st s = ok t → CnOff (L := L) T Cs Sg s t)
    (hfd : ∀ t, sched.cur_thread st s = ok t → fastpath.reply_caps st s t = ok (some found))
    (h : syscall.handle_reply_recv_vm_local st ar s a found = ok (true, s', a')) :
    ∀ ct nx s2 a2, sched.cur_thread st s = ok ct → obj.Tcb.reg st ct s layout.reg.NEXT_IP = ok nx →
      syscall.budget_ok st ar (L.wr s (regA ct layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64)) a =
        ok (true, s2, a2) → ∃ (t rptr ep : U64) (r : S × A), sched.cur_thread st s2 = ok t ∧
          fastpath.reply_caps st s2 t = ok (some (rptr, ep)) ∧
          fastpath_vm.reply_recv_vm_found st ar s2 a2 t rptr ep = ok (true, r) := by
  intro ct nx0 s2g a2g hct hnx hb2
  obtain ⟨⟨Q, R, hSQ⟩, -, -, -, -⟩ := hI
  have hT : TcbPlaced T := hSQ.tcbs
  have hcC : L.cpu s ∈ Cs := hSQ.cur
  have hN : NodePlaced st T s (L.cpu s) := hSQ.nodes _ hcC
  have hcT : L.curW s ∈ T := hSQ.curT
  obtain ⟨rptr, ep⟩ := found
  unfold syscall.handle_reply_recv_vm_local at h
  try simp only [lift, bind_ok] at h
  obtain ⟨t, et, h⟩ := bind_eq_ok h
  rw [num_domains_ne_one_false] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨i, -, h⟩ := bind_eq_ok h
  by_cases c1 : (i &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true
  · rw [if_pos c1] at h; simp at h
  rw [if_neg c1] at h
  obtain ⟨nx, enx, h⟩ := bind_eq_ok h
  obtain ⟨s1, es1, h⟩ := bind_eq_ok h
  obtain ⟨⟨s2, a1⟩, eu, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨csc, ecsc, h⟩ := bind_eq_ok h
  obtain ⟨c, ec, h⟩ := bind_eq_ok h
  obtain ⟨b, eb, h⟩ := bind_eq_ok h
  cases b
  · simp at h
  simp only [↓reduceIte] at h
  try dsimp only at h
  have hb : syscall.budget_ok st ar s1 a = ok (true, s2, a1) := by
    unfold syscall.budget_ok
    rw [eu]; simp only [bind_ok, uncurry_apply_pair]
    exact check_budget_restart_suf ar ecsc ec eb
  have htT : t ∈ T := by
    rw [cur_thread_ok] at et; rw [← ok_inj_ff et]; exact hcT
  have ht' := hT t htT
  obtain ⟨et2, hrc⟩ := rr_prefix_keep ar hT hN hcC et htT (hCn t et) es1 hb (hfd t et) hA
  have e1 : ct = t := ok_inj_ff (hct.symm.trans et)
  rw [e1] at hb2 hnx
  have e2 : nx0 = nx := ok_inj_ff (hnx.symm.trans enx)
  rw [e2] at hb2
  have hs1 := set_fip_wr ht' es1
  rw [← hs1, hb] at hb2
  have e3 := ok_inj_ff hb2
  simp only [Prod.mk.injEq] at e3
  obtain ⟨-, e4, e5⟩ := e3
  rw [← e4, ← e5]
  exact ⟨t, rptr, ep, (s', a'), et2, hrc, h⟩

end

end Fl4Proofs.P1

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

set_option maxHeartbeats 3200000 in
/-- (stpost) **StPostRecv's `hMid` at a dispatch state where the VM ReplyRecv fast run accepts**
(`rrMid_of` for `fastpath_vm.reply_recv_vm_found`, the fault type `VMFault`; module docstring). -/
theorem rrMidVm_of {T Cs Ω Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {X0 s' : S} {a a' : A} {t rptr ep : U64}
    (hct : sched.cur_thread st X0 = ok t) (hrc : fastpath.reply_caps st X0 t = ok (some (rptr, ep)))
    (h : fastpath_vm.reply_recv_vm_found st arI X0 a t rptr ep = ok (true, s', a'))
    (hP : P1.RRPreG (L := L) arI fl4_abi.consts.fault.VMFault X0 a)
    (hPl : ∀ t rptr ep u usc, sched.cur_thread st X0 = ok t → fastpath.reply_caps st X0 t = ok (some (rptr, ep)) →
      P1.RRChecksG st arI fl4_abi.consts.fault.VMFault X0 a t rptr ep u usc →
        P1.RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X0 t rptr ep u usc)
    (hS : P1.RRSum (L := L) Scs X0) :
    ∃ (t : U64) (X8 : S) (a8 : A) (rptr ep : U64), sched.cur_thread st X0 = ok t ∧
      syscall.handle_invocation st arI X0 a false false true true (L.mem X0 (regA t layout.reg.REPLY)) =
        ok (.Ok (), X8, a8) ∧ RRMidSt (st := st) X8 t rptr ep := by
  obtain ⟨u, usc, hC, hT⟩ := P1.reply_recv_vm_found_acc st arI h
  have hRC := P1.reply_caps_some st hrc
  have Pl := hPl t rptr ep u usc hct hrc hC
  obtain ⟨X1, X2, a1, b9, X3, restart, X4, a2, X5, X6, X7, X8, X9, X10, X11, X12, X13, X14, X15,
    e1, e2, e3s, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16⟩ := P1.rrTail_split st arI hT
  obtain ⟨R3, hR⟩ := hP t rptr ep u usc X1 X2 a1 b9 X3 hct hrc hC e1 e2 e3s e3
  obtain ⟨hrs, -⟩ := P1.HfrRestart.restart (st := st) (ar := arI) R3.ft3 R3.lbl3 e4
  subst hrs
  rw [if_pos rfl] at e6
  have R := hR X4 a2 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  obtain ⟨-, -, K8, -, -, -, -, -, -, -, -, -, hact8, -, -, -, -, -⟩ :=
    P1.rr_x8G arI Pl hC (hS usc Pl.hcS) e1 e2 e3s e3 e4 e5 e6 e7 e8
  obtain ⟨ebd, hnsc⟩ := P1.rr_ntfnSc8 arI Pl hC K8
  have hun : obj.Tcb.is_null u = ok false := by
    obtain ⟨b, hb, hbn⟩ := hC.u0
    rw [Bool.not_eq_true] at hbn; subst hbn; exact hb
  have husc : obj.Sc.is_null usc = ok false := by
    obtain ⟨b, hb, hbn⟩ := hC.sc0
    rw [Bool.not_eq_true] at hbn; subst hbn; exact hb
  obtain ⟨⟨sl, root, hsl, hroot, ⟨i, found, g, hi, hr, hc⟩, -⟩⟩ := hRC
  have hls : cspace.lookup_slot st X0 t i = ok (core.result.Result.Ok found) := by
    unfold cspace.lookup_slot
    rw [hsl]; simp only [bind_ok]
    rw [hroot]; simp only [bind_ok]
    exact hr
  obtain ⟨info, hmi, hex, -⟩ := hC.info
  have hex' : info.extra_caps = 0#u64 := by apply UScalar.eq_of_val_eq; simpa using hex
  obtain ⟨buf, hbuf, -⟩ := P1.spec_ex_fd (P0.msg.lookup_ipc_buffer.p0 st X0 false t L.total)
  have hdrt := P1.do_reply_transfer_rrG st arI (t := t) (g := g) (hty0 := P1.vm_ne_null) R.rt1 hun R.us1 e2
    R.sc2 e3s e3 R3.ft3 e4 e5 e6 R.sch6 R.sc6 husc R.run6 R.rdy6 R.suf6 R.pst
  have hinv := P1.handle_invocation_rr st arI hct hmi hex' hls hc hbuf e1
    (P1.schedule_tcb_sch (L := L) X1 t R.sch1) hdrt R.st7 e8 (P1.schedule_tcb_nr (L := L) X8 t R.act8)
  have hiv : i = L.mem X0 (regA t layout.reg.REPLY) := by
    rw [P1.reg_ok] at hi; exact (P1.ok_inj_ff hi).symm
  subst hiv
  refine ⟨t, X8, a2, rptr, ep, hct, hinv, ?_⟩
  obtain ⟨j, j1, c0, c1, c3, c4, g', hj1, hlk1, hj, hlk2⟩ := R.lk8
  rw [P1.reg_ok] at hj1 hj
  have ej1 := P1.ok_inj_ff hj1
  have ej := P1.ok_inj_ff hj
  subst ej1 ej
  obtain ⟨n, hbn, hnc⟩ := R.ntfn8
  rw [P1.eq_of_spec_fd (P1.obj.Tcb.bound_ntfn.val (L := L) X8 t)] at hbn
  have en := P1.ok_inj_ff hbn
  subst en
  refine ⟨R.ct8, ?_, ?_, ⟨c0, c1, c3, c4, g', hlk1, hlk2⟩, ?_, ?_, ?_⟩
  · have := R.act8; unfold sched.ACTION_RESUME_CURRENT at this; exact this
  · rw [hact8]; have := R.ucn; unfold sched.ACTION_CHOOSE_NEW at this; exact this
  · have := R.rt8
    rw [P1.eq_of_spec_fd (P1.obj.Reply.tcb.blk (L := L) X8 rptr)] at this
    exact P1.ok_inj_ff this
  · have := R.ep8
    rw [P1.eq_of_spec_fd (P1.obj.Ep.state.spec (L := L) X8 ep)] at this
    have e := P1.ok_inj_ff this
    unfold obj.EP_IDLE at e
    exact e
  · rcases hnc with h0 | ⟨h0, i7, h7, hn7, -⟩
    · exact Or.inl h0
    · refine Or.inr ⟨?_, ?_⟩
      · rw [P1.eq_of_spec_fd (P1.obj.Ntfn.state.spec (L := L) X8 _)] at h7
        intro e; apply hn7; rw [← P1.ok_inj_ff h7]; exact e
      · rcases hnsc with h00 | h1
        · exact absurd (ebd.trans h00) h0
        · show L.mem X8 (P1.ntfnScA (L.mem X8 (P1.boundA t))) = 0#u64 ∨
            L.mem X8 (P1.ntfnScA (L.mem X8 (P1.boundA t))) ≠ L.mem X8 (P1.scA t)
          rw [ebd]; exact h1

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 16000000 in
/-- (stpost) **The ReplyRecv entry at stable ghosts where the VM ReplyRecv fast run accepts at the
dispatch state** (`kernel_entry_rrSt` with `hacc` for `fastpath_vm.reply_recv_vm_found`, `hRPd` at
`VMFault`, `hMid` by `rrMidVm_of`; module docstring). -/
theorem kernel_entry_rrVmSt [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hni : Entered σ)
    (hR : MR a σ.machineState) (hVI : ValidIrqMasks σ) (hNS0 : NativeScope σ)
    (hn : NativeSys fl4_abi.syscall.SysReplyRecv .sysReplyRecv)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → KBudgetB arI a (faultIPSt σ σ.curThread x))
    (hS : SInvAll.SInvB σ) (hQ : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hFin : ∀ x ∈ (specFront .sysReplyRecv σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64)
      (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
        KFrontF (L := L) arI fl4_abi.syscall.SysReplyRecv s a s' a' →
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hacc : ∀ ct nx s2 a2, sched.cur_thread st s = ok ct → obj.Tcb.reg st ct s layout.reg.NEXT_IP = ok nx →
      syscall.budget_ok st arI (L.wr s (regA ct layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64)) a =
        ok (true, s2, a2) → ∃ (t rptr ep : U64) (r : S × A), sched.cur_thread st s2 = ok t ∧
          fastpath.reply_caps st s2 t = ok (some (rptr, ep)) ∧
          fastpath_vm.reply_recv_vm_found st arI s2 a2 t rptr ep = ok (true, r))
    (hRPd : P1.RRPreAtG (L := L) arI fl4_abi.consts.fault.VMFault s a)
    (hRV : SInvR.RV σ)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_syscall_old st arI s a fl4_abi.syscall.SysReplyRecv ⦃ r =>
      ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true .sysReplyRecv σ).1 ∧
        RJ (L := L) arI AR r.1 r.2 σ' ∧ MR r.2 σ'.machineState ∧ JStab (L := L) arI AR Z H Cs r.1 r.2 σ' ⦄ := by
  have hct := cur_thread_eq (L := L) s
  generalize L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) = ct at hct
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hI := J.xtop.irelK J.ks J.buf
  obtain ⟨x, hk, hTR⟩ := hI.1.tcb ct hctT
  have hxs := hI.1.toE.at_tcb hctT hk
  have hk' : σ.kheap σ.curThread = some (.tcb x) := by rw [hcur]; exact hk
  -- the FaultIP write
  unfold syscall.handle_syscall_old
  rw [hct]; simp only [bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.NEXT_IP) ?_
  rintro nx hnx
  have hnx' : obj.Tcb.reg st ct s layout.reg.NEXT_IP = ok nx := by rw [P1.reg_ok, hnx]; rfl
  simp only [lift, bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s ct layout.reg.FAULT_IP _) ?_
  rintro s1 rfl
  generalize hv : core.num.U64.wrapping_sub nx 2#u64 = v
  have es1 : obj.Tcb.set_reg st ct s layout.reg.FAULT_IP v = ok (L.wr s (regA ct layout.reg.FAULT_IP) v) :=
    P1.eq_of_spec_fd (Endp.obj.Tcb.set_reg.spec s ct layout.reg.FAULT_IP v)
  have hvb : v.bv = x.tcbArch.tcbContext.userRegs .nextIP - 2 := by
    rw [← hv, core.num.U64.wrapping_sub_bv_eq, hnx, ← hxs.regs .nextIP, regIdx_nextIP]; rfl
  have hX2 := reg_wr_irel J.ip hI hctT hk Fl4Spec.Register.faultIP (by decide) v
  rw [regIdx_faultIP] at hX2
  obtain ⟨V0, J0⟩ := J.regWrJ hctT hk Fl4Spec.Register.faultIP v (by rw [regIdx_faultIP]; exact hX2)
  rw [regIdx_faultIP, hvb] at J0
  rw [← hcur] at J0
  have hF : ((), faultIPSt σ σ.curThread x) ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1 := by
    rw [fl4SyscallFaultIP_eq hk']; exact Set.mem_singleton _
  have hni0 : Entered (faultIPSt σ σ.curThread x) := hni
  have hBu := hB x hk'
  -- the trap flag and the number range
  refine WP.spec_bind (hflag ct v hct) ?_
  rintro f hf
  simp only [hf, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [if_neg hn.range.1, if_neg hn.range.2]
  -- budget_ok
  have hAK := hARI.toARKeep
  have hNSf := SInv.ns_fl4SyscallFaultIP σ.curThread σ hNS0 _ hF
  have hBud := JAtZ.budgetOkB (σ0 := faultIPSt σ σ.curThread x) J0 hni0 hBu hNSf hAK hA hnd hmrt hmb hmax htu
  have hBudS := JAtZ.budgetOkBSt (σ0 := faultIPSt σ σ.curThread x) J0 hni0 hBu hNSf hAK hA hnd hmrt hmb hmax htu
  have hMK := hKD.toK
  refine WP.spec_bind (WP.spec_and (WP.spec_and (spec_and_eq hBud fun _ h => h) hBudS)
    (budget_ok_mr hM hMK hA hR _)) ?_
  rintro ⟨b, s2, a1⟩ ⟨⟨⟨⟨hTr, -⟩, hbeq⟩, hFaS⟩, hMRb⟩
  cases b
  · -- the budget check stops the system call
    obtain ⟨z, hz, hz1, hJS⟩ := hFaS rfl
    obtain ⟨b', σb⟩ := z
    simp only at hz1; subst hz1
    obtain ⟨Gb, Vb, Acb, Lstb, Db, Jb⟩ := hJS
    show (do
      let (s3, a2) ← (if false = true then syscall.dispatch_syscall st arI s2 a1 fl4_abi.syscall.SysReplyRecv
        else ok (s2, a1))
      syscall.finish st arI s3 a2) ⦃ _ ⦄
    rw [if_neg (by decide)]
    simp only [bind_ok]
    have hx : ((.ok (), σb) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront .sysReplyRecv σ).1 :=
      mem_specFront hF (mem_handleE_ok (mem_fl4HandleEvent hz mem_whenE_false))
    have F := hFin _ hx _ H Cs Acb Lstb Db s2 a1
      ⟨ct, v, false, s2, a1, hct, hbeq, Or.inl ⟨rfl, rfl, rfl⟩⟩ Jb.toR
    have hMσb := (budget_mr_at (σ0 := faultIPSt σ σ.curThread x) hM hnd hz hMRb hVI).1
    exact WP.spec_mono (jat_finishJRNMSt s2 a1 σb Jb.toR (SInvN.ns_front true .sysReplyRecv hNS0 _ hx) F.hd hnd
      hA F.vt hmb F.arch F.archNd F.fo F.sni F.send hT F.tail hmax htu hM hKD hMσb)
      fun r ⟨σ', hmem, hRJ, hM', hSt⟩ => ⟨σ', mem_kentry hx hmem, hRJ, hM', hSt.mv⟩
  · -- the system call runs: the accepted ReplyRecv dispatch
    obtain ⟨σb, he, ekh, ect, ecs, eact, eidle, hCb, hOb, Ac', Lst', D', J'⟩ := hTr rfl
    show (do
      let (s3, a2) ← (if true = true then syscall.dispatch_syscall st arI s2 a1 fl4_abi.syscall.SysReplyRecv
        else ok (s2, a1))
      syscall.finish st arI s3 a2) ⦃ _ ⦄
    rw [if_pos rfl]
    have hb : (true, σb) ∈ (specBudget (faultIPSt σ σ.curThread x)).1 := by
      unfold specBudget
      rw [he]; exact Set.mem_singleton _
    have hBA : BudgetAt σ σb true := ⟨_, hF, hb⟩
    obtain ⟨hMRσb, -⟩ := budget_mr_at (σ0 := faultIPSt σ σ.curThread x) hM hnd
      (show (true, σb) ∈ _ by rw [he]; exact Set.mem_singleton _) hMRb hVI
    have hnib : Entered σb := ⟨by rw [ect, eidle]; exact hni0.1, by rw [eact]; exact hni0.2⟩
    have hfr : KFrontB (L := L) arI s a s2 a1 := ⟨ct, v, hct, hbeq⟩
    -- the accepted fast path at the dispatch state
    obtain ⟨t2, rptr2, ep2, ⟨s'', a''⟩, hct2, hrc2, hrr⟩ := hacc ct nx s2 a1 hct hnx' (by rw [hv]; exact hbeq)
    obtain ⟨i, found, g, hi, hls, hcap⟩ := (P1.reply_caps_some st hrc2).replyLookup
    have hiv : i = L.mem s2 (regA t2 layout.reg.REPLY) := by
      rw [P1.reg_ok] at hi; exact (P1.ok_inj_ff hi).symm
    subst hiv
    obtain ⟨t3, X8, a8, rptr, ep, hct3, hinv, hMs⟩ := rrMidVm_of arI hct2 hrc2 hrr
      (hRPd ct nx _ s2 a1 hct hnx' (by rw [hv]; exact es1) hbeq)
      (fun _ _ _ _ _ et hrc hC => P1.rrPl_lkG arI (fun _ h => h) J'.bxi J'.lkTyped et hrc hC)
      (J'.rrSum (rv_faultIP ekh hRV))
    have e23 : t3 = t2 := P1.ok_inj_ff (hct3.symm.trans hct2)
    subst e23
    -- the dispatch state's entry facts (`KDispHypsKV27.to26`, `KDispHypsKV27b.to27`, `KDispHyps28M.to27M`)
    obtain ⟨x0, hk0, -⟩ := hS.1.2
    obtain ⟨-, ek0, ect0, -, -, eq0⟩ := BudgetAt.shape27 hnd hk0 hBA
    have ek0' : σb.kheap = Function.update σ.kheap σ.curThread
        (some (.tcb (setReg x0 .faultIP (x0.tcbArch.tcbContext.userRegs .nextIP - 2)))) := ek0
    obtain ⟨-, hcnf⟩ := SInvAll.sinvB_disp (x' := setReg x0 .faultIP (x0.tcbArch.tcbContext.userRegs .nextIP - 2))
      hS hni.1 hk0 rfl rfl ek0' ect0
    have hqb : ∀ d p, σb.curThread ∉ σb.readyQueues d p := by rw [ect0, eq0]; exact hQ
    have hME := J'.midEntry hnib hcnf
    have hcq : MidRun.CQ σb.curThread σb :=
      ⟨⟨rfl, fun x hx => ⟨hME.run x hx, hME.nf x hx⟩⟩, hqb, by rw [hnib.2]; intro e; cases e⟩
    have hPQ : MidRun.JMidPerfHypQ true (Fl4Spec.toBl (L.mem s2 (regA t3 layout.reg.REPLY)).bv) σb :=
      MidRun.jMidPerfHypQ_of2 hcq hME.nq (jPerfRegHyp_27b hnd hS hni.1 hBA _) (jPerfIrqSlotHyp_27b hnd hS hBA _)
    refine WP.spec_bind (spec_and_eq (dispatch_replyRecvJStF s2 a1 σb J' hnib hcnf hqb hA hmax htu hmb hM hKD
      hMRσb t3 hct2 found hls hcap hPQ ⟨X8, a8, rptr, ep, hinv, hMs⟩) fun _ h => h) ?_
    rintro ⟨s3, a2⟩ ⟨⟨⟨u, σm⟩, hy, hy1, hRm, hJm, hMy⟩, hdeq⟩
    simp only at hy1; subst hy1
    obtain ⟨Gm, Vm, Acm, Lstm, Dm, JmR⟩ := JStabR.mv hJm
    have hx : ((.ok (), σm) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront .sysReplyRecv σ).1 :=
      mem_specFront hF (mem_handleE_ok (mem_fl4HandleEvent hb (mem_whenE_true hy)))
    have F := hFin _ hx _ H Cs Acm Lstm Dm s3 a2
      ⟨ct, v, true, s2, a1, hct, hbeq, Or.inr ⟨rfl, hdeq⟩⟩ JmR
    exact WP.spec_mono (jat_finishJRNMSt s3 a2 σm JmR (SInvN.ns_front true .sysReplyRecv hNS0 _ hx) F.hd hnd hA
      F.vt hmb F.arch F.archNd F.fo F.sni F.send hT F.tail hmax htu hM hKD hMy)
      fun r ⟨σ', hmem, hRJ, hM', hSt⟩ => ⟨σ', mem_kentry hx hmem, hRJ, hM', hSt.mv⟩


end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 8000000 in
/-- (stpost) **The accepted VM ReplyRecv entry at given ghosts, stable** (module docstring). -/
theorem kernel_entry_rrVm_localSt17 [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ)
    {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z]
    (found : U64 × U64) (hct : σ.curThread ≠ σ.idleThread)
    (hn : NativeSys fl4_abi.syscall.SysReplyRecv .sysReplyRecv)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hFin : ∀ x ∈ (specFront .sysReplyRecv σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64)
      (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
        KFrontF (L := L) arI fl4_abi.syscall.SysReplyRecv s a s' a' →
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR13 (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hfd : ∀ t, sched.cur_thread st s = ok t → fastpath.reply_caps st s t = ok (some found)) :
    syscall.handle_reply_recv_vm_local st arI s a found ⦃ r => r.1 = true →
      ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true .sysReplyRecv σ).1 ∧
        JReachU17 (L := L) arI AR MR r.2.1 r.2.2 σ' ∧ JStab (L := L) arI AR Z H Cs r.2.1 r.2.2 σ' ⦄ := by
  obtain ⟨hJ3, hGp, hIv, hDv⟩ := hJ
  obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, hR, -, -, -⟩ := jreach_invU3 hnd hJ3
  have hni := hX.entered hct
  have hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄ := hPA.minBudget
  have hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄ :=
    fun a => hT.mrt a
  have hD : SetDlDet := setDlDet_of arI hM hDR hR
  have hARK := hARI.toARKeep
  have hS := hX.sb
  have hQ := hX.ctQ
  have hU3 := sinvX_ut3 hX
  have hSg : SInvG.SpecGlobS σ := sinvX_sg hX
  have hC : CurInv σ := J.cur.resolve_left (by rw [hni.2]; intro e; cases e)
  have hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → KBudgetB arI a (faultIPSt σ σ.curThread x) :=
    fun x hk => ⟨hM.nowAgree hR hS.1.1.vmt, curInv_faultIPSt hk hC, offReady_faultIPSt hX.offReady, Or.inr hQ⟩
  have hRV := Fl4Proofs.P3.SInvW.rv hX.w
  have hRPd : P1.RRPreAt (L := L) arI s a :=
    J.rrPreAt hni hR hS hQ (fun _ _ => offReady_faultIPSt hX.offReady) hARI hA hnd hM hmrt hmb hmax htu hRV
      (J.rrPre5At hni hR hX.sb hX.ctQ (fun _ _ => offReady_faultIPSt hX.offReady) hARI hA hnd hM hmrt hmb hmax htu
        hRV)
  have hFin' : ∀ x ∈ (specFront .sysReplyRecv σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64)
      (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
        KFrontF (L := L) arI fl4_abi.syscall.SysReplyRecv s a s' a' →
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR (L := L) arI AR Z' H' Cs' s' a' x.2 := fun x hx Z' H' Cs' Ac' Lst' D' s' a' hF J' =>
    ((((hFin x hx Z' H' Cs' Ac' Lst' D' s' a' hF J').to11 J'
      (SInvIV.front_idleVtS σ.curThread true (.syscallEvent .sysReplyRecv) hSg (sinvX_idleOut hX) hU3 hIv x hx)).to8
      (J'.hdOK (dp_specFront hnd .sysReplyRecv (sinvX_dom hX) x hx))).to5 hnd hA hARK hRef hD hT J'
      (fun o e => SInvAll.sinvB_front_fo true .sysReplyRecv hS hct x hx o e)).to31 hA hD |>.to27.toR
      (fun o e => SInvAll.sinvB_front_fo true .sysReplyRecv hS hct x hx o e)
  have hRPdV : P1.RRPreAtG (L := L) arI fl4_abi.consts.fault.VMFault s a :=
    J.rrPreAtG (ty := fl4_abi.consts.fault.VMFault) hni hR hS hQ (fun _ _ => offReady_faultIPSt hX.offReady) hARI hA
      hnd hM hmrt hmb hmax htu hRV
  obtain ⟨⟨b, s', a'⟩, e, -⟩ := P1.spec_ex_fd
    (P0.syscall.handle_reply_recv_vm_local.p0 st arI s a found L.total hA)
  rw [e, WP.spec_ok]
  intro hb
  simp only at hb
  subst hb
  have hs := P1.rr_vm_local_same arI hSX hA hRPdV J.bxi (fun _ et => J.cnOff et) hflag hfd e
  have hacc := P1.rr_vm_local_acc arI hA J.bxi (fun _ et => J.cnOff et) hfd e
  have hG := kernel_entry_rrVmSt s a σ J hni hR hS.1.1.vim hS.1.1.ns hn hflag hB hS hQ hFin' hacc hRPdV hRV hARI hA
    hnd hM hKD hmrt hmb hT hmax htu
  have hG' := P1.FastAgree.spec st arI (P1.FastAgree.of_acc st arI P1.LawfulStore.total hA
    (FastAcc.of_rrpre hSX hflag hn.range rfl hRPd)) hG
  rw [hs, WP.spec_ok] at hG'
  obtain ⟨σ', hy, hRJ, hM', hSt⟩ := hG'
  exact ⟨σ', hy, ⟨JReachU3.step _ _ hJ3 hct hn hs hy ⟨hRJ, hM'⟩,
    SInvGp.kentry_gpmOut .sysReplyRecv hSg hU3 hGp _ hy,
    SInvIV.kentry_idleVtS .sysReplyRecv hSg (sinvX_idleOut hX) hU3 hIv _ hy,
    SInvDV.kentry_devRange .sysReplyRecv hU3 hDv _ hy⟩, hSt⟩


end

end

end Fl4Proofs.P3.SInvR.G5
