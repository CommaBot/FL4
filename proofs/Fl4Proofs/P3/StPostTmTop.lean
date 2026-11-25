/-
P3 (line stpost, generation 6): **the accepted `TCB_SetTimer` entry beside the gate at stable
ghosts** (StPostIoTop's route for `localtimer.handle_set_timer_local`).

`handle_set_timer_local … n target` (fl4-sync's `local_set_timer`) is, where it returns `true`, the
general entry (P1 `set_timer_local_same`): `FAULT_IP`, `budget_ok`, `dispatch_syscall`'s invoking
arm for `SysCall` (`handle_invocation true true true false cptr`, `after_invocation`), `finish`. The
general invocation decodes any cap at any label; the local entry runs only where, at the dispatch
state, the `CAP` register names fl4-sync's `Thread target` slot and the message label is
`TCBSetTimer`. So:

* `P1.set_timer_local_acc`: an accepted run has number `SysCall`, and at the general entry's
  dispatch state (after its `FAULT_IP` write and passing `budget_ok`) the current thread is
  unchanged, the `CAP` lookup finds the slot of fl4-sync's contract (`hL`, carried from the entry
  state by `lookup_slot_keep` / `found_cap_keep`: the prefix misses the CSpace words), the message
  info's label is `TCBSetTimer` (the `MSG_INFO` register is not `FAULT_IP`: the message-info
  register survives the prefix, `reg_keepK`), and `remote_tcb_stall` of the target stalls nothing
  (the target's affinity word is this core's, `stall_none`).
* `handle_invocation_threadTmJSt`: `handle_invocation call true don false cptr` at `J` with the
  found `Thread p` cap and the label `TCBSetTimer`: `refinesMXPF` (StPostInv) at `X := JStabM Z H Cs`,
  `XP := False`; fault by `faultHypJZGSt`, tails by StPostIoLeaf's `flTailJSt` / `replyFailJSt`; the
  decode by `tcb_canon` / `XCapP.lbl_congr` to the canonical label, `xcapP_of_tcb` of StPostTmLeaf's
  `tcb_set_timerJSt` (the truncated error and the timer insert), `MR` by `XCapP.mrG` with
  `MKD.decode_thread_nonins` / `perfF_tcbN`. Never preempted (`thread_noPre_of`).
* `dispatch_threadTmJSt`, `kernel_entry_tmSt` (handle_syscall_old, StPostIoTop's `kernel_entry_ioSt`
  shape) given `htm` (the dispatch-state facts above).
* **`kernel_entry_tm_localSt17`**: from `JReachU17` and given `JAtZ Z H Cs` (with `VxE Z`), under
  U29T's syscall-clause inputs that this route reads (`hct`, `hn : NativeSys n c`, `hflag`,
  `hFin : KFinAtR13`, fl4-sync's contract `SetTimerFound`; not `hK` / `hDL`), an accepted
  `handle_set_timer_local … n target` ends at a `fl4KernelEntrySyscall true c` outcome that is
  `JReachU17` **and** `JStab Z H Cs`.

Files: `P1.set_timer_local_acc` in StPostTmAcc; `handle_invocation_threadTmJSt` /
`dispatch_threadTmJSt` in StPostTmInv; `kernel_entry_tmSt` / `kernel_entry_tm_localSt17` here.

Premises: U29T's (a subset of the platform facts); no new premise.
-/
import Fl4Proofs.P3.StPostTmAcc
import Fl4Proofs.P3.StPostTmInv
import Fl4Proofs.P3.XTopJointKEntryU29T
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 16000000 in
/-- (stpost) **The `TCB_SetTimer` entry at stable ghosts, where the cap in `CAP` is a Thread cap and
the label `TCBSetTimer`** (module docstring; `kernel_entry_ioSt`'s shape). -/
theorem kernel_entry_tmSt [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hni : Entered σ)
    (hR : MR a σ.machineState) (hVI : ValidIrqMasks σ) (hNS0 : NativeScope σ)
    (n : I64) (call don : Bool) (hi : InvSys n call true don)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → KBudgetB arI a (faultIPSt σ σ.curThread x))
    (hS : SInvAll.SInvB σ) (hQ : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hFin : ∀ x ∈ (specFront (invSysOf call true) σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64)
      (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
        KFrontF (L := L) arI n s a s' a' →
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR (L := L) arI AR Z' H' Cs' s' a' x.2)
    (htm : ∀ ct nx s2 a2, sched.cur_thread st s = ok ct → obj.Tcb.reg st ct s layout.reg.NEXT_IP = ok nx →
      syscall.budget_ok st arI (L.wr s (regA ct layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64)) a =
        ok (true, s2, a2) →
      sched.cur_thread st s2 = ok ct ∧ ∃ (found : cspace.Resolved) (p : U64),
        cspace.lookup_slot st s2 ct (L.mem s2 (regA ct layout.reg.CAP)) = ok (.Ok found) ∧
        obj.Slot.cap st found.slot s2 = ok (.Thread p) ∧
        (∀ info, msg.msg_info st s2 ct = ok info → info.label = fl4_abi.label.TCBSetTimer) ∧
        smp.remote_tcb_stall st arI s2 a2 p = ok (s2, a2))
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_syscall_old st arI s a n ⦃ r =>
      ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true (invSysOf call true) σ).1 ∧
        RJ (L := L) arI AR r.1 r.2 σ' ∧ MR r.2 σ'.machineState ∧ JStab (L := L) arI AR Z H Cs r.1 r.2 σ' ⦄ := by
  have hn : NativeSys n (invSysOf call true) := Or.inl ⟨call, true, don, hi, rfl⟩
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
      let (s3, a2) ← (if false = true then syscall.dispatch_syscall st arI s2 a1 n else ok (s2, a1))
      syscall.finish st arI s3 a2) ⦃ _ ⦄
    rw [if_neg (by decide)]
    simp only [bind_ok]
    have hx : ((.ok (), σb) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront (invSysOf call true) σ).1 :=
      mem_specFront hF (mem_handleE_ok (mem_fl4HandleEvent hz mem_whenE_false))
    have F := hFin _ hx _ H Cs Acb Lstb Db s2 a1
      ⟨ct, v, false, s2, a1, hct, hbeq, Or.inl ⟨rfl, rfl, rfl⟩⟩ Jb.toR
    have hMσb := (budget_mr_at (σ0 := faultIPSt σ σ.curThread x) hM hnd hz hMRb hVI).1
    exact WP.spec_mono (jat_finishJRNMSt s2 a1 σb Jb.toR (SInvN.ns_front true (invSysOf call true) hNS0 _ hx) F.hd hnd
      hA F.vt hmb F.arch F.archNd F.fo F.sni F.send hT F.tail hmax htu hM hKD hMσb)
      fun r ⟨σ', hmem, hRJ, hM', hSt⟩ => ⟨σ', mem_kentry hx hmem, hRJ, hM', hSt.mv⟩
  · -- the system call runs: the SetTimer invocation
    obtain ⟨σb, he, ekh, ect, ecs, eact, eidle, hCb, hOb, Ac', Lst', D', J'⟩ := hTr rfl
    show (do
      let (s3, a2) ← (if true = true then syscall.dispatch_syscall st arI s2 a1 n else ok (s2, a1))
      syscall.finish st arI s3 a2) ⦃ _ ⦄
    rw [if_pos rfl]
    have hb : (true, σb) ∈ (specBudget (faultIPSt σ σ.curThread x)).1 := by
      unfold specBudget
      rw [he]; exact Set.mem_singleton _
    have hBA : BudgetAt σ σb true := ⟨_, hF, hb⟩
    obtain ⟨hMRσb, -⟩ := budget_mr_at (σ0 := faultIPSt σ σ.curThread x) hM hnd
      (show (true, σb) ∈ _ by rw [he]; exact Set.mem_singleton _) hMRb hVI
    have hnib : Entered σb := ⟨by rw [ect, eidle]; exact hni0.1, by rw [eact]; exact hni0.2⟩
    -- the Thread cap, the label and the stall at the dispatch state
    obtain ⟨hct2, found, p, hls, hcap, hlab, hstall⟩ := htm ct nx s2 a1 hct hnx' (by rw [hv]; exact hbeq)
    -- the dispatch state's entry facts (`KDispHypsKV27.to26`)
    obtain ⟨x0, hk0, -⟩ := hS.1.2
    obtain ⟨-, ek0, ect0, en0, ei0, eq0⟩ := BudgetAt.shape27 hnd hk0 hBA
    have ek0' : σb.kheap = Function.update σ.kheap σ.curThread
        (some (.tcb (setReg x0 .faultIP (x0.tcbArch.tcbContext.userRegs .nextIP - 2)))) := ek0
    obtain ⟨hvfh, -⟩ := SInvAll.sinvB_disp (x' := setReg x0 .faultIP (x0.tcbArch.tcbContext.userRegs .nextIP - 2))
      hS hni.1 hk0 rfl rfl ek0' ect0
    have hqb : ∀ d p, σb.curThread ∉ σb.readyQueues d p := by rw [ect0, eq0]; exact hQ
    refine WP.spec_bind (spec_and_eq (dispatch_threadTmJSt s2 a1 σb J' hA hM hKD hnib hqb hvfh
      hMRσb ct hct2 n call don hi found hls hcap hlab hstall) fun _ h => h) ?_
    rintro ⟨s3, a2⟩ ⟨⟨⟨u, σm⟩, hy, hy1, hRm, hJm, hMy⟩, hdeq⟩
    simp only at hy1; subst hy1
    obtain ⟨Gm, Vm, Acm, Lstm, Dm, Jm⟩ := hJm
    have hx : ((.ok (), σm) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront (invSysOf call true) σ).1 :=
      mem_specFront hF (mem_handleE_ok (mem_fl4HandleEvent hb (mem_whenE_true hy)))
    have F := hFin _ hx _ H Cs Acm Lstm Dm s3 a2
      ⟨ct, v, true, s2, a1, hct, hbeq, Or.inr ⟨rfl, hdeq⟩⟩ Jm.toR
    exact WP.spec_mono (jat_finishJRNMSt s3 a2 σm Jm.toR (SInvN.ns_front true (invSysOf call true) hNS0 _ hx) F.hd
      hnd hA F.vt hmb F.arch F.archNd F.fo F.sni F.send hT F.tail hmax htu hM hKD hMy)
      fun r ⟨σ', hmem, hRJ, hM', hSt⟩ => ⟨σ', mem_kentry hx hmem, hRJ, hM', hSt.mv⟩

set_option maxHeartbeats 8000000 in
/-- (stpost) **The accepted `TCB_SetTimer` entry beside the gate at given ghosts, stable** (module
docstring). -/
theorem kernel_entry_tm_localSt17 [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop}
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR)
    (hPA : PPPlatA arI AR) (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ)
    {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z]
    (n : I64) (c : Fl4Spec.Syscall) (target : U64) (hct : σ.curThread ≠ σ.idleThread) (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64)
      (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
        KFrontF (L := L) arI n s a s' a' →
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR13 (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hTF : SetTimerFound (L := L) s target) :
    localtimer.handle_set_timer_local st arI s a n target ⦃ r => r.1 = true →
      ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
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
  have hFin' : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64)
      (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
        KFrontF (L := L) arI n s a s' a' →
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR (L := L) arI AR Z' H' Cs' s' a' x.2 := fun x hx Z' H' Cs' Ac' Lst' D' s' a' hF J' =>
    ((((hFin x hx Z' H' Cs' Ac' Lst' D' s' a' hF J').to11 J'
      (SInvIV.front_idleVtS σ.curThread true (.syscallEvent c) hSg (sinvX_idleOut hX) hU3 hIv x hx)).to8
      (J'.hdOK (dp_specFront hnd c (sinvX_dom hX) x hx))).to5 hnd hA hARK hRef hD hT J'
      (fun o e => SInvAll.sinvB_front_fo true c hS hct x hx o e)).to31 hA hD |>.to27.toR
      (fun o e => SInvAll.sinvB_front_fo true c hS hct x hx o e)
  have htg : target ∈ P1.Heap.tcbs H := by
    have et := cur_thread_curW (L := L) (st := st) s
    obtain ⟨r, er, ecr⟩ := hTF _ et
    exact J.threadCapT et er ecr
  obtain ⟨⟨b, s', a'⟩, e, -⟩ := P1.spec_ex_fd
    (P0.localtimer.handle_set_timer_local.p0 st arI s a n target L.total hA)
  rw [e, WP.spec_ok]
  intro hb
  simp only at hb
  subst hb
  have hs := P1.set_timer_local_same arI hA J.bxi (fun _ et => J.cnOff et) hflag hTF htg e
  obtain ⟨hn2, htm⟩ := P1.set_timer_local_acc arI hA J.bxi (fun _ et => J.cnOff et) hTF htg e
  subst hn2
  have hi : InvSys fl4_abi.syscall.SysCall true true true := Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩)
  have hrr : fl4_abi.syscall.SysCall ≠ fl4_abi.syscall.SysReplyRecv := by
    (simp only [fl4_abi.syscall.SysCall, fl4_abi.syscall.SysReplyRecv, ne_eq] <;> decide)
  have hc := nativeSys_invC hn hi
  subst hc
  have hG := kernel_entry_tmSt s a σ J hni hR hS.1.1.vim hS.1.1.ns _ true true hi hflag hB hS hQ hFin'
    (fun ct nx s2 a2 h1 h2 h3 => by
      obtain ⟨e1, f, h⟩ := htm ct nx s2 a2 h1 h2 h3
      exact ⟨e1, f, target, h⟩) hARI hA
    hnd hM hKD hmrt hmb hT hmax htu
  have hG' : syscall.handle_syscall st arI s a fl4_abi.syscall.SysCall ⦃ r =>
      ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true (invSysOf true true) σ).1 ∧
        RJ (L := L) arI AR r.1 r.2 σ' ∧ MR r.2 σ'.machineState ∧ JStab (L := L) arI AR Z H Cs r.1 r.2 σ' ⦄ := by
    rw [handle_syscall_eq_general_of hflag hn.range hrr, P1.handle_syscall_general_eq]; exact hG
  rw [hs, WP.spec_ok] at hG'
  obtain ⟨σ', hy, hRJ, hM', hSt⟩ := hG'
  exact ⟨σ', hy, ⟨JReachU3.step _ _ hJ3 hct hn hs hy ⟨hRJ, hM'⟩,
    SInvGp.kentry_gpmOut (invSysOf true true) hSg hU3 hGp _ hy,
    SInvIV.kentry_idleVtS (invSysOf true true) hSg (sinvX_idleOut hX) hU3 hIv _ hy,
    SInvDV.kentry_devRange (invSysOf true true) hU3 hDv _ hy⟩, hSt⟩

end

end

end Fl4Proofs.P3.SInvR.G5
