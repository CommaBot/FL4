/-
P3 (line stpost, generation 4): **the ReplyRecv kernel entry at stable ghosts, where the fast path
accepts** (KEntryU's `kernel_entryJ13PUGMD4S` restricted to `SysReplyRecv` at a dispatch state
whose `fastpath.reply_recv` accepts).

* `kernel_entry_rrSt`: the general path `handle_syscall_old` from a `JAtZ Z H Cs` entry state with
  the trap flag clear and `SysReplyRecv`, under `kernel_entryJ13PUGMD4S`'s inputs (its `hK`,
  `hFin`, platform premises; no `hDL`: the Reply cap's decode is StPostInv's, not `JDecMRLK`),
  given `hacc` (the passing budget check of this entry reaches a dispatch state where
  `fastpath.reply_recv` accepts), `hRPd : P1.RRPreAt` (`JAtZ.rrPreAt` gives it) and `hRV` (as `JAtZ.rrPreAt`):
  every outcome is a `fl4KernelEntrySyscall true .sysReplyRecv` outcome with `RJ`, `MR` **and**
  `JStab Z H Cs`. The FAULT_IP write as the template; the budget stop by `JAtZ.budgetOkBSt` and
  `jat_finishJRNMSt` (StPostEv); the dispatch by StPostRecv's `dispatch_replyRecvJStF` with the
  Reply cap from `reply_recv_acc` / `reply_caps_some` / `RCaps.replyLookup` and `hMid` from
  StPostRRMid's `rrMid_of` (`RRPl` by `P1.rrPl_lk` at the dispatch `JAtZ`, `RRSum` by
  `JAtZ.rrSum`); no preemption (the Reply-cap invocation is never preempted); the finish by
  `jat_finishJRNMSt`.

Premises: `kernel_entryJ13PUGMD4S`'s (a subset) and `hacc` / `hRPd` / `hRV` above; the receive's
[W] `JMidRecvHypSt` is gone (StPostRecv). `hK`'s mid field supplies JEntryAt's `cnf` / `ctnq` and
`JMidPerfHypQ` [W] as in the template.
-/
import Fl4Proofs.P3.StPostRRMid
import Fl4Proofs.P3.StPostTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A) [L : LawfulStore st]

set_option maxHeartbeats 1600000 in
/-- (stpost) **An accepted ReplyRecv run beside the gate accepts at its dispatch state**: where
`handle_syscall_local … SysReplyRecv` returns `true` and the trap flag is clear, the general
entry's `FAULT_IP` write and passing `budget_ok` reach a state where `fastpath.reply_recv`
accepts (`syscall_local_same`'s ReplyRecv arm; `budget_ok` and the reads deterministic). -/
theorem syscall_local_rr_acc (hA : P0.ArchTotal ar) {T Cs Sg : Set U64} {s s' : S} {a a' : A}
    {found : U64 × U64}
    {Ω Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hCn : ∀ t, sched.cur_thread st s = ok t → CnOff (L := L) T Cs Sg s t)
    (hfd : ∀ t f, sched.cur_thread st s = ok t → obj.Tcb.flags st t s = ok f →
      (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 → fl4_abi.syscall.SysReplyRecv = fl4_abi.syscall.SysReplyRecv →
      fastpath.reply_caps st s t = ok (some found))
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (h : syscall.handle_syscall_local st ar s a fl4_abi.syscall.SysReplyRecv found = ok (true, s', a')) :
    ∀ ct nx s2 a2, sched.cur_thread st s = ok ct → obj.Tcb.reg st ct s layout.reg.NEXT_IP = ok nx →
      syscall.budget_ok st ar (L.wr s (regA ct layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64)) a =
        ok (true, s2, a2) → ∃ r : S × A, fastpath.reply_recv st ar s2 a2 = ok (true, r) := by
  intro ct nx s2 a2 hct hnx hb2
  obtain ⟨⟨Q, R, hSQ⟩, -, -, -, -⟩ := hI
  have hT : TcbPlaced T := hSQ.tcbs
  have hcC : L.cpu s ∈ Cs := hSQ.cur
  have hN : NodePlaced st T s (L.cpu s) := hSQ.nodes _ hcC
  have hcT : L.curW s ∈ T := hSQ.curT
  obtain ⟨rptr, ep⟩ := found
  unfold syscall.handle_syscall_local at h
  try simp only [lift, bind_ok] at h
  obtain ⟨t, et, h⟩ := bind_eq_ok h
  obtain ⟨i, ei, h⟩ := bind_eq_ok h
  try simp only [lift, bind_ok] at h
  rw [num_domains_ne_one_false] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  have htT : t ∈ T := by
    rw [cur_thread_ok] at et; rw [← ok_inj_ff et]; exact hcT
  have ht' := hT t htT
  have hi0 : (i &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 := by
    have hf := hflag t 0#u64 et
    rw [flags_fip ht', ei, WP.spec_ok] at hf
    exact hf
  have c1 : ¬ (i &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true := by simp [hi0]
  rw [if_neg c1] at h
  have c2 : ¬ (fl4_abi.syscall.SysReplyRecv != fl4_abi.syscall.SysReplyRecv) = true := by simp
  rw [if_neg c2] at h
  obtain ⟨nx', enx, h⟩ := bind_eq_ok h
  obtain ⟨s1, es1, h⟩ := bind_eq_ok h
  obtain ⟨⟨s2', a1⟩, eu, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨csc, ecsc, h⟩ := bind_eq_ok h
  obtain ⟨c, ec, h⟩ := bind_eq_ok h
  obtain ⟨b, eb, h⟩ := bind_eq_ok h
  cases b
  · simp at h
  simp only [↓reduceIte, if_neg c1] at h
  try dsimp only at h
  have hb : syscall.budget_ok st ar s1 a = ok (true, s2', a1) := by
    unfold syscall.budget_ok
    rw [eu]; simp only [bind_ok, uncurry_apply_pair]
    exact check_budget_restart_suf ar ecsc ec eb
  obtain ⟨et2, hrcK⟩ := local_prefix_keep ar hT hN hcC et htT (hCn t et) es1 hb hA
  have hrc := hrcK rptr ep (hfd t i et ei hi0 rfl)
  have hrr : fastpath.reply_recv st ar s2' a1 = ok (true, s', a') := by
    unfold fastpath.reply_recv
    rw [et2]; simp only [bind_ok]
    rw [hrc]; simp only [bind_ok]
    exact h
  have e1 : ct = t := ok_inj_ff (hct.symm.trans et)
  subst e1
  have e2 : nx = nx' := ok_inj_ff (hnx.symm.trans enx)
  subst e2
  have hs1 := set_fip_wr ht' es1
  rw [← hs1, hb] at hb2
  have e3 := ok_inj_ff hb2
  simp only [Prod.mk.injEq] at e3
  obtain ⟨-, rfl, rfl⟩ := e3
  exact ⟨(s', a'), hrr⟩

end

end Fl4Proofs.P1

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 16000000 in
/-- (stpost) **The accepted ReplyRecv entry at stable ghosts** (module docstring). -/
theorem kernel_entry_rrSt [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hni : Entered σ)
    (hR : MR a σ.machineState) (hVI : ValidIrqMasks σ) (hNS0 : NativeScope σ)
    (hn : NativeSys fl4_abi.syscall.SysReplyRecv .sysReplyRecv)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → KBudgetB arI a (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        KDispHyps13PU (L := L) arI AR MR (Z.mv Z.G V') H Cs D' s' a' σb fl4_abi.syscall.SysReplyRecv .sysReplyRecv)
    (hFin : ∀ x ∈ (specFront .sysReplyRecv σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64)
      (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
        KFrontF (L := L) arI fl4_abi.syscall.SysReplyRecv s a s' a' →
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hacc : ∀ ct nx s2 a2, sched.cur_thread st s = ok ct → obj.Tcb.reg st ct s layout.reg.NEXT_IP = ok nx →
      syscall.budget_ok st arI (L.wr s (regA ct layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64)) a =
        ok (true, s2, a2) → ∃ r : S × A, fastpath.reply_recv st arI s2 a2 = ok (true, r))
    (hRPd : P1.RRPreAt (L := L) arI s a)
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
    obtain ⟨⟨s'', a''⟩, hrr⟩ := hacc ct nx s2 a1 hct hnx' (by rw [hv]; exact hbeq)
    obtain ⟨t2, rptr2, ep2, hct2, hrc2, -⟩ := P1.reply_recv_acc st arI hrr
    obtain ⟨i, found, g, hi, hls, hcap⟩ := (P1.reply_caps_some st hrc2).replyLookup
    have hiv : i = L.mem s2 (regA t2 layout.reg.REPLY) := by
      rw [P1.reg_ok] at hi; exact (P1.ok_inj_ff hi).symm
    subst hiv
    obtain ⟨t3, X8, a8, rptr, ep, hct3, hinv, hMs⟩ := rrMid_of arI hrr (hRPd ct nx _ s2 a1 hct hnx' (by rw [hv]; exact es1) hbeq)
      (fun _ _ _ _ _ et hrc hC => P1.rrPl_lk arI (fun _ h => h) J'.bxi J'.lkTyped et hrc hC)
      (J'.rrSum (rv_faultIP ekh hRV))
    have e23 : t3 = t2 := P1.ok_inj_ff (hct3.symm.trans hct2)
    subst e23
    obtain ⟨-, hE, -, hPQ, -⟩ := (hK σb hBA V0 Ac' Lst' D' s2 a1 hfr J').mid t3 layout.reg.REPLY
      Fl4Spec.replyRegister true hct2 (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩)
    refine WP.spec_bind (spec_and_eq (dispatch_replyRecvJStF s2 a1 σb J' hnib hE.cnf hE.ctnq hA hmax htu hmb hM hKD
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


set_option maxHeartbeats 4000000 in
/-- (stpost) **The accepted ReplyRecv entry beside the gate, stable ghosts**: `handle_syscall_local`
with the trap flag clear and `SysReplyRecv`, where it returns `true`, ends at a
`fl4KernelEntrySyscall true .sysReplyRecv` outcome with `RJ`, `MR` and `JStab Z H Cs`
(`kernel_entry_rrSt` with `hacc` from `P1.syscall_local_rr_acc`, carried to `handle_syscall` by
`FastAcc.of_rrpre` and to the local entry by `P1.syscall_local_same`). `hfd`: fl4-sync's `found`
contract [P] (as P1 `syscall_local_same`). -/
theorem kernel_entry_rr_localSt [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets}
    {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hni : Entered σ)
    (hR : MR a σ.machineState) (hVI : ValidIrqMasks σ) (hNS0 : NativeScope σ)
    (hn : NativeSys fl4_abi.syscall.SysReplyRecv .sysReplyRecv) (found : U64 × U64)
    (hfd : ∀ t f, sched.cur_thread st s = ok t → obj.Tcb.flags st t s = ok f →
      (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 → fl4_abi.syscall.SysReplyRecv = fl4_abi.syscall.SysReplyRecv →
      fastpath.reply_caps st s t = ok (some found))
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → KBudgetB arI a (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        KDispHyps13PU (L := L) arI AR MR (Z.mv Z.G V') H Cs D' s' a' σb fl4_abi.syscall.SysReplyRecv .sysReplyRecv)
    (hFin : ∀ x ∈ (specFront .sysReplyRecv σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64)
      (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
        KFrontF (L := L) arI fl4_abi.syscall.SysReplyRecv s a s' a' →
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hRPd : P1.RRPreAt (L := L) arI s a) (hRV : SInvR.RV σ) (hSX : P1.StoreExt st)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_syscall_local st arI s a fl4_abi.syscall.SysReplyRecv found ⦃ r => r.1 = true →
      ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true .sysReplyRecv σ).1 ∧
        RJ (L := L) arI AR r.2.1 r.2.2 σ' ∧ MR r.2.2 σ'.machineState ∧
        JStab (L := L) arI AR Z H Cs r.2.1 r.2.2 σ' ⦄ := by
  obtain ⟨⟨b, s', a'⟩, e, -⟩ := P1.spec_ex_fd
    (P0.syscall.handle_syscall_local.p0 st arI s a fl4_abi.syscall.SysReplyRecv found L.total hA)
  rw [e, WP.spec_ok]
  intro hb
  simp only at hb
  subst hb
  have hs := P1.syscall_local_same arI hA J.bxi (fun _ et => J.cnOff et) hfd e
  have hacc := P1.syscall_local_rr_acc arI hA J.bxi (fun _ et => J.cnOff et) hfd hflag e
  have hG := kernel_entry_rrSt s a σ J hni hR hVI hNS0 hn hflag hB hK hFin hacc hRPd hRV hARI hA hnd hM hKD hmrt
    hmb hT hmax htu
  have hG' := P1.FastAgree.spec st arI (P1.FastAgree.of_acc st arI P1.LawfulStore.total hA
    (FastAcc.of_rrpre hSX hflag hn.range rfl hRPd)) hG
  rw [hs, WP.spec_ok] at hG'
  exact hG'

end

end

end Fl4Proofs.P3.SInvR.G5
