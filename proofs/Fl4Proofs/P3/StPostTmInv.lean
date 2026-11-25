/-
P3 (line stpost, generation 6): **the SetTimer invocation of a Thread cap at stable ghosts**
(`handle_invocation_threadTmJSt`, `dispatch_threadTmJSt`; split from StPostTmTop, whose module
docstring describes the route). No premise added.
-/
import Fl4Proofs.P3.StPostTmDec
import Fl4Proofs.P3.StPostIoTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section StTmInv
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 8000000 in
/-- (stpost) **The SetTimer invocation of a Thread cap at `J`, stable ghosts** (module docstring). -/
theorem handle_invocation_threadTmJSt [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (hA : P0.ArchTotal arI) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hni : Entered σ)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hvfh : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler)
    (hR : MR ar σ.machineState)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (is_call can_donate : Bool) (cptr : U64)
    (found : cspace.Resolved) (hls : cspace.lookup_slot st s ct cptr = ok (.Ok found))
    {p : U64} (hcap : obj.Slot.cap st found.slot s = ok (.Thread p))
    (hlab : ∀ info, msg.msg_info st s ct = ok info → info.label = fl4_abi.label.TCBSetTimer)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) :
    syscall.handle_invocation st arI s ar is_call true can_donate false cptr ⦃ res =>
      HIPostMXP (L := L) (JStabM (L := L) arI AR MR Z H Cs) (fun _ _ _ => False) true σ is_call true can_donate
        false (Fl4Spec.toBl cptr.bv) res ⦄ := by
  obtain ⟨info, mi, buf, buffer, r2, er, argsU, hinfo, hmi, hbuf, hbuffer, hr2, her, hmrs⟩ :=
    JAtZ.frontEx arI J J.xferH.1 J.xferH.2.1 hct
  obtain ⟨hcur, -⟩ := J.curEq hct
  have htcb := (J.xtop.curTcb hcur).1
  have hX := J.xtop
  have hF : ∀ {f : error.Fault} {f' : Fl4Spec.Fault}, CapFaultCorr f f' →
      faults.handle_fault st arI s ar ct f ⦃ r => ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv f' σ).1,
        RelTopM (L := L) r.1 z.2 ∧ JStabM (L := L) arI AR MR Z H Cs r.1 r.2 z.2 ⦄ := fun hcf =>
    WP.spec_mono (spec_mrz hM (J.faultHypJZGSt hA hni hct hnq hvfh (FaultCorrG.cap hcf))
      (MKD.faults_handle_fault L.total hA hKD hR)
      (fun z hz => congrArg Prod.fst (MachT.mtk_handleFaultG _ _ σ z hz)))
      fun _ ⟨z, hz, ⟨h1, h2⟩, h3⟩ => ⟨z, hz, h1, h2, h3⟩
  refine handle_invocation_refinesMXPF arI (JStabM (L := L) arI AR MR Z H Cs) (fun _ _ _ => False) true s ar σ
    Z.th Z.G hX.rel.1 hX.rel.2.1 hX.rel.2.2.1 hX.rel.2.2.2.1 hX.rel.2.2.2.2.1 ⟨J.stab, hR⟩ ct hct hcur htcb
    is_call true can_donate false cptr found hls info hinfo mi hmi buf hbuf buffer hbuffer r2 hr2 er her
    ((J.extraJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf
      hbuffer hr2 her).imp id fun ⟨f, f', h1, h2, hcf⟩ => ⟨f, f', h1, h2, fun _ => hF hcf⟩)
    (argsU.map UScalar.bv) hmrs
    (fun s1 a1 σ' _ hXs hc => by
      obtain ⟨⟨_, _, _, _, _, J'⟩, hR'⟩ := hXs
      exact WP.spec_mono (WP.spec_and (J'.flTailJSt hc is_call) (MKD.fl_tail L.total hA hKD hR'))
        fun _ ⟨⟨h1, z, hz, h2, h3⟩, h4⟩ => ⟨h1, z, hz, h2, h3.mv, msF_mr hM h4
          (congrArg Prod.fst (MachT.mtk_specTailG _ _ _ σ' z hz))⟩)
    (fun a1 e e' hX1 he => by
      obtain ⟨⟨_, _, _, _, _, J''⟩, hR'⟩ := hX1
      exact WP.spec_mono (WP.spec_and ((J.archJ J''.xtop.fin.1.1.2.2.2.2.2.2).replyFailJSt hcur is_call e e' he)
        (MKD.reply_err_tail (e := e) (t := ct) (s := s) (is_call := is_call) L.total hA hKD hR'))
        fun _ ⟨⟨h1, z, hz, h2, h3⟩, h4⟩ => ⟨h1, z, hz, h2, h3, msF_mr hM h4
          (congrArg Prod.fst (MachT.mtk_when (MachT.mtk_fl4ReplyFromKernelErrorG _ _ _) σ z hz))⟩)
    (fun inv σ1 y hst hy => by
      rw [perfCurKeep _ _ _ inv σ1 y hy]
      obtain ⟨x, hk⟩ := (J.xtop.curTcb hcur).2
      rw [hcur] at hst
      have hm : ((), σ1) ∈ (Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ).1 := by
        rw [hst]; exact Set.mem_singleton _
      rw [Notif.setThreadState_eq .restart hk] at hm
      have e : σ1 = _ := congrArg Prod.snd (Set.mem_singleton_iff.1 hm)
      rw [e, Sched.stsAct_rec]; exact hcur) ?_
  obtain ⟨hLen, hArgs, -⟩ := J.argsJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hmrs
  obtain ⟨hLb, -⟩ := J.frontJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hr2 her
  have hl : info.label = fl4_abi.label.TCBSetTimer := hlab info hinfo
  intro sl c e exs hsl hfs hc hget _ _
  have hc' : c = .Thread p := by
    rw [slot_cap_eq, hfs, hc] at hcap; exact ok_inj hcap
  subst hc'
  have hAs : AbsSlot Z.th sl := by
    obtain ⟨q, hq, hth⟩ := hsl; exact ⟨q, hq, Or.inl hth⟩
  have hsc : capV (L.mem s) (cslotAddr sl) = .Thread p := capV_of_capAt hc
  rw [← hLb, hl]
  exact decode_threadTmJSt s ar σ J hni hA hM hKD hR ct hct is_call can_donate (msgLen info buf) buf argsU hLen hArgs
    sl hAs hsc hstall e exs buffer (Fl4Spec.toBl cptr.bv)

set_option maxHeartbeats 8000000 in
/-- (stpost) **`dispatch_syscall` for an invoking number with a `Thread` cap in `CAP` at the label
`TCBSetTimer`, stable ghosts** (module docstring; StPostIoTop's `dispatch_ioportJSt`). -/
theorem dispatch_threadTmJSt [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (hA : P0.ArchTotal arI) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hni : Entered σ)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hvfh : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler)
    (hR : MR ar σ.machineState)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (call don : Bool)
    (hn : InvSys number call true don) (found : cspace.Resolved)
    (hls : cspace.lookup_slot st s ct (L.mem s (regA ct layout.reg.CAP)) = ok (.Ok found))
    {p : U64} (hcap : obj.Slot.cap st found.slot s = ok (.Thread p))
    (hlab : ∀ info, msg.msg_info st s ct = ok info → info.label = fl4_abi.label.TCBSetTimer)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) :
    syscall.dispatch_syscall st arI s ar number ⦃ r =>
      ∃ y ∈ ((Fl4Spec.fl4HandleSyscall (Z := Unit) true (invSysOf call true)).run σ).1, y.1 = .ok () ∧
        RelTopM (L := L) r.1 y.2 ∧ JStab (L := L) arI AR Z H Cs r.1 r.2 y.2 ∧ MR r.2 y.2.machineState ⦄ := by
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨-, xs, hks⟩ := J.xtop.curTcb hcur
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hxs := (J.xtop.irelK J.ks J.buf).1.toE.at_tcb hctT hks
  have hcp : Fl4Spec.dataToCptr (xs.tcbArch.tcbContext.userRegs Fl4Spec.cap_register) =
      Fl4Spec.toBl (L.mem s (regA ct layout.reg.CAP)).bv := by
    rw [← regIdx_cap, hxs.regs]; rfl
  have hk' : σ.kheap σ.curThread = some (.tcb xs) := by rw [hcur]; exact hks
  have hreg := mem_getCapReg hk' Fl4Spec.cap_register
  rw [hcp] at hreg
  have hinv : (do
      let (r, s1, a1) ← syscall.handle_invocation st arI s ar call true don false (L.mem s (regA ct layout.reg.CAP))
      let (_, s2, a2) ← syscall.after_invocation st arI s1 a1 r
      ok (s2, a2)) ⦃ r => ∃ y ∈ ((DispInv call true don).run σ).1, y.1 = .ok () ∧
        RelTopM (L := L) r.1 y.2 ∧ JStab (L := L) arI AR Z H Cs r.1 r.2 y.2 ∧ MR r.2 y.2.machineState ⦄ := by
    refine WP.spec_bind (handle_invocation_threadTmJSt s ar σ J hA hM hKD hni hnq hvfh hR ct hct
      call don _ found hls hcap hlab hstall) ?_
    rintro ⟨r, s1, a1⟩ ⟨y, hy, hres, hrel, hX⟩
    rcases hres with ⟨rfl, hy1⟩ | ⟨rfl, hy1⟩
    · show (do
        let (_, s2, a2) ← syscall.after_invocation st arI s1 a1 (.Ok ())
        ok (s2, a2)) ⦃ _ ⦄
      rw [show syscall.after_invocation st arI s1 a1 (.Ok ()) = ok (true, s1, a1) by
        unfold syscall.after_invocation; rfl, bind_ok]
      rw [if_neg (fun h => by cases h)] at hX
      exact (WP.spec_ok _).2 ⟨y, mem_bindE_ok (mem_liftE (ε := Unit) hreg) hy, hy1, hrel, hX.1, hX.2⟩
    · rw [if_pos rfl] at hX; exact hX.elim
  rw [fl4HandleSyscall_inv hn]
  unfold syscall.dispatch_syscall
  rw [hct]; simp only [bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.CAP) ?_
  rintro c0 rfl
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.REPLY) ?_
  rintro c1 -
  have n15 : fl4_abi.syscall.SysCall ≠ fl4_abi.syscall.SysSend := by
    unfold fl4_abi.syscall.SysCall fl4_abi.syscall.SysSend; decide
  have n16 : fl4_abi.syscall.SysCall ≠ fl4_abi.syscall.SysNBSend := by
    unfold fl4_abi.syscall.SysCall fl4_abi.syscall.SysNBSend; decide
  rcases hn with ⟨rfl, rfl, -, rfl⟩ | ⟨-, -, h, -⟩ | ⟨rfl, rfl, -, rfl⟩
  · rw [if_pos rfl]; exact hinv
  · cases h
  · rw [if_neg n15, if_neg n16, if_pos rfl]; exact hinv

end StTmInv

end

end Fl4Proofs.P3
