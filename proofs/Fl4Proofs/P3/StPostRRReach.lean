/-
P3 (line stpost, generation 4): **the accepted ReplyRecv entry beside the gate at given ghosts,
stable, from a `JReachU17` state** (StPostTop's `kernel_entry_sysU_localSt` for U29S's syscall
clause at `SysReplyRecv`).

`kernel_entry_rr_localSt17`: from `JReachU17 s a σ` and any `JAtZ Z H Cs …` (with `VxE Z`) at
`(s, a, σ)`, under U29S's syscall-clause inputs at `SysReplyRecv` that the ReplyRecv route reads
(the trap flag `hflag`, the finish `hFin : KFinAtR13`, fl4-sync's `found` contract `hfd`; not
`hK` / `hDL`: StPostRRTop derives the dispatch facts from `SInvB`, and the Reply cap's decode is
StPostInv's), an accepted `handle_syscall_local … SysReplyRecv found` ends at a
`fl4KernelEntrySyscall true .sysReplyRecv` outcome that is `JReachU17` **and** `JStab Z H Cs`.

* `hFin` to `KFinAtR` along the U chain's conversions (U13 `to11` with `front_idleVtS`, U11 `to8`
  with `dp_specFront`, U8 `to5` with `sinvB_front_fo`, U5 `to31`, KEntryU `to27.toR`);
* `RRPreAt` by `JAtZ.rrPreAt` / `JAtZ.rrPre5At` (as KEntryUH), `RV` by `SInvW.rv`;
* `JReachU17` at the outcome by `JReachU3.step` (the run is `handle_syscall`'s: P1
  `syscall_local_same`) and `kentry_gpmOut` / `kentry_idleVtS` / `kentry_devRange`, as U12 / U13 /
  U17 carry them.

Premises: U29S's (a subset); no new premise.
-/
import Fl4Proofs.P3.StPostRRTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 8000000 in
/-- (stpost) **The accepted ReplyRecv entry at given ghosts, stable** (module docstring). -/
theorem kernel_entry_rr_localSt17 [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
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
    (hfd : ∀ t f, sched.cur_thread st s = ok t → obj.Tcb.flags st t s = ok f →
      (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 → fl4_abi.syscall.SysReplyRecv = fl4_abi.syscall.SysReplyRecv →
      fastpath.reply_caps st s t = ok (some found)) :
    syscall.handle_syscall_local st arI s a fl4_abi.syscall.SysReplyRecv found ⦃ r => r.1 = true →
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
  obtain ⟨⟨b, s', a'⟩, e, -⟩ := P1.spec_ex_fd
    (P0.syscall.handle_syscall_local.p0 st arI s a fl4_abi.syscall.SysReplyRecv found L.total hA)
  rw [e, WP.spec_ok]
  intro hb
  simp only at hb
  subst hb
  have hs := P1.syscall_local_same arI hA J.bxi (fun _ et => J.cnOff et) hfd e
  have hacc := P1.syscall_local_rr_acc arI hA J.bxi (fun _ et => J.cnOff et) hfd hflag e
  have hG := kernel_entry_rrSt s a σ J hni hR hS.1.1.vim hS.1.1.ns hn hflag hB hS hQ hFin' hacc hRPd hRV hARI hA hnd
    hM hKD hmrt hmb hT hmax htu
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
