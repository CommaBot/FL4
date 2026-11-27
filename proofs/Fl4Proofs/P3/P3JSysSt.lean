/-
P3 (p3J gen 29): **the native syscall entry at given ghosts, stable, with its footprint, from one dispatch-level
fact** (stage A; stages Q / K in P3JSysStQ / P3JSysStK, as P3JStTrap).

Gen 28 found that `SysFootWC` cannot be composed from leaf footprints alone: `finFootJ_holds` at the post-dispatch
state needs a `JAtZ` there with the **entry's** `H` / `Cs`, i.e. the stable-ghost (`JStab`) half of the dispatch.
This module states that half and the footprint together, at the dispatch state, and runs the entry around it.

* **`DispPostSt`**: the post of one dispatch run from a dispatch state `s0` (spec state `σb`): an outcome `y` of the
  spec's `fl4HandleSyscall true c` from `σb` with, unpreempted (`y.1 = ok`), `JStabR Z H Cs` and `MR` at `y.2`, or,
  preempted (`y.1 = error`), an outcome `z` of `preemptionPath y.2` with `JStab Z H Cs` and `MR` at `z.2`; **and**
  the run writes only `ProjW H Cs s0`. (`DispPostRM`, XTopJointKEntry36, at stable ghosts, with the footprint.)
* **`DispStabFootAt Z H Cs s a σ n c`**: at every dispatch state of the entry from `(s, a, σ)` (`KFrontB`: the
  `FAULT_IP` write, a passing `budget_ok`; `BudgetAt σ σb true`) where `JAtZ (Z.mv Z.G V') H Cs` holds with `MR`,
  `CKI σb` and `RR σb`, every run of `dispatch_syscall … n` ends in `DispPostSt`. This is the shape of the premise
  P3JSysStTop names `DispStabFoot` [J]; here it is only a hypothesis.
* **`cki_front`**: `CKI` at every outcome of `specFront` (spec only, `hv_auto` as P3JCkS).
* **`kernel_entry_sysStF`**: StPostRRTop's `kernel_entry_rrSt` for **every** native syscall: the general path
  `handle_syscall_old` from a `JAtZ Z H Cs` entry state, the `FAULT_IP` write (`J.regWrJ`; P3JMcFltS's
  `fipProjW`), `budget_ok` (`budgetOkB` / `budgetOkBSt`, `budget_ok_mr`; P3JMcFlt's `budOk_projW_rr`), the
  budget stop by `jat_finishJRNMSt` + `finFootJ_holds`, the dispatch by `hDS`, its unpreempted outcome by
  `jat_finishJRNMSt` + P3JFinR's `finFootJR`, its preempted outcome (as KEntryEv's `kPreFinAtGMS`) by
  `jat_finishJRNMSt` + `finFootJ_holds`: every outcome is an outcome of `fl4KernelEntrySyscall true c` with `RJ`,
  `MR`, `JStab Z H Cs` **and** the run writes only `ProjW H Cs s`.
* **`sys_entryStFU17`**: from `JReachU17` (as StPostRRReach's `kernel_entry_rr_localSt17`): `hFin : KFinAtR13` to
  `KFinAtR` along the U chain; the fast path by P1 `FastAgree` — at `SysReplyRecv` from `FastAcc.of_rrpre` with
  `JAtZ.rrPreAt` / `JAtZ.rrPre5At` (no fast path premise: the accepted ReplyRecv fast path keeps every property of
  the general path's outcomes, `StoreExt` [P] global), elsewhere `handle_syscall_eq_general_of` (FL4 #56); the
  outcome `JReachU17` by `JReachU3.step` and `kentry_gpmOut` / `kentry_idleVtS` / `kentry_devRange`.
* **`sys_entryStFU41`**: the same from `KFinAtR41` (`to13` with `FpuImplDet`), as P3JStTrap's `trap_entryStU41`.

Premises: the stated hypotheses only (`hDS` is a hypothesis; U41's platform globals). No sorry. New module; no
existing statement changed.
-/
import Fl4Proofs.P3.StPostRRReach
import Fl4Proofs.P3.P3JStTrap
import Fl4Proofs.P3.P3JMcFltS
import Fl4Proofs.P3.P3JFinR
import Fl4Proofs.P3.P3JCkS
import Fl4Proofs.P3.P3JRrE
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvCk
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvV Fl4Proofs.P3.SInvDom Fl4Proofs.P3.SInvIo

set_option maxHeartbeats 4000000 in
/-- **`CKI` at every outcome of the syscall front** (spec only). -/
theorem cki_front (c : Syscall) {σ : State Unit} (h : CKI σ) : ∀ x ∈ (specFront c σ).1, CKI x.2 := by
  intro x hx
  have hK : IKH CKI (fl4SyscallFaultIP (Z := Unit) σ.curThread >>= fun _ =>
      ExceptT.run (NonDetE.handleE (fl4HandleEvent (Z := Unit) true (.syscallEvent c))
        (fun _ => withoutPreemption preemptionPath))) := by hv_auto
  exact hK σ h x hx

end Fl4Proofs.P3.SInvCk

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **One dispatch run's stable post with its footprint** (module docstring). -/
def DispPostSt (Z : XSets) (H : P1.Heap) (Cs : Set U64) (c : Fl4Spec.Syscall) (σb : Fl4Spec.State Unit) (s0 : S)
    (r : S × A) : Prop :=
  (∃ y ∈ ((Fl4Spec.fl4HandleSyscall (Z := Unit) true c).run σb).1,
    (y.1 = .ok () ∧ JStabR (L := L) arI AR Z H Cs r.1 r.2 y.2 ∧ MR r.2 y.2.machineState) ∨
    (y.1 = .error () ∧ ∃ z ∈ (Fl4Spec.preemptionPath (Z := Unit) y.2).1,
      JStab (L := L) arI AR Z H Cs r.1 r.2 z.2 ∧ MR r.2 z.2.machineState)) ∧
  P1.WritesIn st s0 r.1 (Mc.ProjW (L := L) H Cs s0)

/-- **The dispatch's stable post with footprint at every dispatch state of the entry** (module docstring). -/
def DispStabFootAt (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64)
    (c : Fl4Spec.Syscall) : Prop :=
  ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
    KFrontB (L := L) arI s a s' a' → JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
    MR a' σb.machineState → SInvCk.CKI σb → SInvRr.RR σb →
    syscall.dispatch_syscall st arI s' a' n ⦃ r => DispPostSt (L := L) arI AR MR Z H Cs c σb s' r ⦄

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 16000000 in
/-- (p3J gen 29) **The general syscall path at stable ghosts, with its footprint** (module docstring). -/
theorem kernel_entry_sysStF [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hni : Entered σ)
    (hR : MR a σ.machineState) (hVI : ValidIrqMasks σ) (hNS0 : NativeScope σ)
    (hC : SInvCk.CKI σ) (hRR : SInvRr.RR σ) (hres : σ.schedulerAction = .resumeCurThread)
    (n : I64) (c : Fl4Spec.Syscall) (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → KBudgetB arI a (faultIPSt σ σ.curThread x))
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64)
      (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
        KFrontF (L := L) arI n s a s' a' →
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hDS : DispStabFootAt (L := L) arI AR MR Z H Cs s a σ n c)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_syscall_old st arI s a n ⦃ r =>
      ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
        RJ (L := L) arI AR r.1 r.2 σ' ∧ MR r.2 σ'.machineState ∧ JStab (L := L) arI AR Z H Cs r.1 r.2 σ' ∧
        P1.WritesIn st s r.1 (Mc.ProjW (L := L) H Cs s) ⦄ := by
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
  simp only [lift, bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s ct layout.reg.FAULT_IP _) ?_
  rintro s1 rfl
  generalize hv : core.num.U64.wrapping_sub nx 2#u64 = v
  have F0 := Mc.fipProjW J hct v
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
  have hC0 : SInvCk.CKI (faultIPSt σ σ.curThread x) :=
    SInvV.hv_fl4SyscallFaultIP (P := SInvCk.CKI) σ.curThread σ hC _ hF
  have hRR0 : SInvRr.RR (faultIPSt σ σ.curThread x) :=
    (SInvRr.rq_fl4SyscallFaultIP σ.curThread σ _ hF).trans hRR
  have hres0 : (faultIPSt σ σ.curThread x).schedulerAction = .resumeCurThread := hres
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
  have hBudF := Mc.budOk_projW_rr hA J0 hres0 hRR0
  have hMK := hKD.toK
  refine WP.spec_bind (WP.spec_and (WP.spec_and (WP.spec_and (spec_and_eq hBud fun _ h => h) hBudS)
    (budget_ok_mr hM hMK hA hR _)) hBudF) ?_
  rintro ⟨b, s2, a1⟩ ⟨⟨⟨⟨⟨hTr, -⟩, hbeq⟩, hFaS⟩, hMRb⟩, F1⟩
  have F01 : P1.WritesIn st s s2 (Mc.ProjW (L := L) H Cs s) := F0.projW_trans F1
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
    have hx : ((.ok (), σb) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront c σ).1 :=
      mem_specFront hF (mem_handleE_ok (mem_fl4HandleEvent hz mem_whenE_false))
    have F := hFin _ hx _ H Cs Acb Lstb Db s2 a1
      ⟨ct, v, false, s2, a1, hct, hbeq, Or.inl ⟨rfl, rfl, rfl⟩⟩ Jb.toR
    have hMσb := (budget_mr_at (σ0 := faultIPSt σ σ.curThread x) hM hnd hz hMRb hVI).1
    have hCb : SInvCk.CKI σb := SInvCk.cki_front c hC _ hx
    refine WP.spec_mono (WP.spec_and (jat_finishJRNMSt s2 a1 σb Jb.toR (SInvN.ns_front true c hNS0 _ hx) F.hd hnd
      hA F.vt hmb F.arch F.archNd F.fo F.sni F.send hT F.tail hmax htu hM hKD hMσb)
      (Mc.finFootJ_holds hA _ H Cs Acb Lstb Db s2 a1 σb Jb inferInstance hCb)) ?_
    rintro r ⟨⟨σ', hmem, hRJ, hM', hSt⟩, F2⟩
    exact ⟨σ', mem_kentry hx hmem, hRJ, hM', hSt.mv, F01.projW_trans F2⟩
  · -- the system call runs: the dispatch
    obtain ⟨σb, he, ekh, ect, ecs, eact, eidle, hCb', hOb, Ac', Lst', D', J'⟩ := hTr rfl
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
    have hfr : KFrontB (L := L) arI s a s2 a1 := ⟨ct, v, hct, hbeq⟩
    have hCb : SInvCk.CKI σb := by
      intro p cref c' hc; rw [ekh] at hc; exact hC0 p cref c' hc
    have hRRb : SInvRr.RR σb := by
      have e : SInvRr.rpV σb = SInvRr.rpV (faultIPSt σ σ.curThread x) := by
        funext o; simp only [SInvRr.rpV, ekh]
      unfold SInvRr.RR at hRR0 ⊢
      rw [e]; exact hRR0
    refine WP.spec_bind (spec_and_eq (hDS σb hBA V0 Ac' Lst' D' s2 a1 hfr J' hMRσb hCb hRRb) fun _ h => h) ?_
    rintro ⟨s3, a2⟩ ⟨⟨⟨y, hy, hcase⟩, F2⟩, hdeq⟩
    rcases hcase with ⟨hy1, hJm, hMy⟩ | ⟨hy1, z, hz, hJz, hMz⟩
    · obtain ⟨u, σm⟩ := y
      simp only at hy1; subst hy1
      obtain ⟨Gm, Vm, Acm, Lstm, Dm, JmR⟩ := hJm
      have hx : ((.ok (), σm) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront c σ).1 :=
        mem_specFront hF (mem_handleE_ok (mem_fl4HandleEvent hb (mem_whenE_true hy)))
      have F := hFin _ hx _ H Cs Acm Lstm Dm s3 a2
        ⟨ct, v, true, s2, a1, hct, hbeq, Or.inr ⟨rfl, hdeq⟩⟩ JmR
      have hCm : SInvCk.CKI σm := SInvCk.cki_front c hC _ hx
      refine WP.spec_mono (WP.spec_and (jat_finishJRNMSt s3 a2 σm JmR (SInvN.ns_front true c hNS0 _ hx) F.hd hnd hA
        F.vt hmb F.arch F.archNd F.fo F.sni F.send hT F.tail hmax htu hM hKD hMy)
        (Mc.finFootJR hA JmR hCm)) ?_
      rintro r ⟨⟨σ', hmem, hRJ, hM', hSt⟩, F3⟩
      exact ⟨σ', mem_kentry hx hmem, hRJ, hM', hSt.mv, (F01.projW_trans F2).projW_trans F3⟩
    · obtain ⟨u, σ1⟩ := y
      simp only at hy1; subst hy1
      obtain ⟨Gz, Vz, Acz, Lstz, Dz, Jz⟩ := hJz
      have hx : ((.ok z.1, z.2) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront c σ).1 :=
        mem_specFront hF (mem_handleE_err (mem_fl4HandleEvent hb (mem_whenE_true hy)) (mem_liftE hz))
      have F := hFin _ hx _ H Cs Acz Lstz Dz s3 a2
        ⟨ct, v, true, s2, a1, hct, hbeq, Or.inr ⟨rfl, hdeq⟩⟩ Jz.toR
      have hCz : SInvCk.CKI z.2 := SInvCk.cki_front c hC _ hx
      refine WP.spec_mono (WP.spec_and (jat_finishJRNMSt s3 a2 z.2 Jz.toR (SInvN.ns_front true c hNS0 _ hx) F.hd hnd
        hA F.vt hmb F.arch F.archNd F.fo F.sni F.send hT F.tail hmax htu hM hKD hMz)
        (Mc.finFootJ_holds hA _ H Cs Acz Lstz Dz s3 a2 z.2 Jz inferInstance hCz)) ?_
      rintro r ⟨⟨σ', hmem, hRJ, hM', hSt⟩, F3⟩
      exact ⟨σ', mem_kentry hx hmem, hRJ, hM', hSt.mv, (F01.projW_trans F2).projW_trans F3⟩

set_option maxHeartbeats 8000000 in
/-- (p3J gen 29) **The native syscall entry at given ghosts, stable, with its footprint, from `JReachU17`**
(module docstring). -/
theorem sys_entryStFU17 [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} (hARI : ARIface arI AR)
    (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ)
    (hC : SInvCk.CKI σ) (hRR : SInvRr.RR σ)
    {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z]
    (n : I64) (c : Fl4Spec.Syscall) (hct : σ.curThread ≠ σ.idleThread) (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64)
      (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
        KFrontF (L := L) arI n s a s' a' →
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR13 (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hDS : DispStabFootAt (L := L) arI AR MR Z H Cs s a σ n c) :
    syscall.handle_syscall st arI s a n ⦃ r =>
      ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
        JReachU17 (L := L) arI AR MR r.1 r.2 σ' ∧ JStab (L := L) arI AR Z H Cs r.1 r.2 σ' ∧
        MR r.2 σ'.machineState ∧ P1.WritesIn st s r.1 (Mc.ProjW (L := L) H Cs s) ⦄ := by
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
  have hCI : CurInv σ := J.cur.resolve_left (by rw [hni.2]; intro e; cases e)
  have hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → KBudgetB arI a (faultIPSt σ σ.curThread x) :=
    fun x hk => ⟨hM.nowAgree hR hS.1.1.vmt, curInv_faultIPSt hk hCI, offReady_faultIPSt hX.offReady, Or.inr hQ⟩
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
  have hG := kernel_entry_sysStF s a σ J hni hR hS.1.1.vim hS.1.1.ns hC hRR hX.cr.2 n c hn hflag hB hFin' hDS
    hARI hA hnd hM hKD hmrt hmb hT hmax htu
  have hG' : syscall.handle_syscall st arI s a n ⦃ r =>
      ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
        RJ (L := L) arI AR r.1 r.2 σ' ∧ MR r.2 σ'.machineState ∧ JStab (L := L) arI AR Z H Cs r.1 r.2 σ' ∧
        P1.WritesIn st s r.1 (Mc.ProjW (L := L) H Cs s) ⦄ := by
    by_cases hrr : n = fl4_abi.syscall.SysReplyRecv
    · have hRV := Fl4Proofs.P3.SInvW.rv hX.w
      have hRPd : P1.RRPreAt (L := L) arI s a :=
        J.rrPreAt hni hR hS hQ (fun _ _ => offReady_faultIPSt hX.offReady) hARI hA hnd hM hmrt hmb hmax htu hRV
          (J.rrPre5At hni hR hX.sb hX.ctQ (fun _ _ => offReady_faultIPSt hX.offReady) hARI hA hnd hM hmrt hmb hmax
            htu hRV)
      exact P1.FastAgree.spec st arI (P1.FastAgree.of_acc st arI P1.LawfulStore.total hA
        (FastAcc.of_rrpre hSX hflag hn.range hrr hRPd)) hG
    · exact P1.FastAgree.spec st arI (P1.FastAgree.of_eq st arI (handle_syscall_eq_general_of hflag hn.range hrr)) hG
  refine WP.spec_mono (spec_and_eq hG' fun _ h => h) ?_
  rintro ⟨s', a'⟩ ⟨⟨σ', hy, hRJ, hM', hSt, hW⟩, hs⟩
  exact ⟨σ', hy, ⟨JReachU3.step _ _ hJ3 hct hn hs hy ⟨hRJ, hM'⟩,
    SInvGp.kentry_gpmOut c hSg hU3 hGp _ hy,
    SInvIV.kentry_idleVtS c hSg (sinvX_idleOut hX) hU3 hIv _ hy,
    SInvDV.kentry_devRange c hU3 hDv _ hy⟩, hSt, hM', hW⟩

set_option maxHeartbeats 8000000 in
/-- (p3J gen 29) **`sys_entryStFU17` on U41's finish record** (`KFinAtR41.to13`, as `trap_entryStU41`). -/
theorem sys_entryStFU41 [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} (hARI : ARIface arI AR)
    (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR) (hFpu : FpuImplDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ)
    (hC : SInvCk.CKI σ) (hRR : SInvRr.RR σ)
    {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z]
    (n : I64) (c : Fl4Spec.Syscall) (hct : σ.curThread ≠ σ.idleThread) (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hFin41 : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64)
      (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
        KFrontF (L := L) arI n s a s' a' →
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR41 (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hDS : DispStabFootAt (L := L) arI AR MR Z H Cs s a σ n c) :
    syscall.handle_syscall st arI s a n ⦃ r =>
      ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
        JReachU17 (L := L) arI AR MR r.1 r.2 σ' ∧ JStab (L := L) arI AR Z H Cs r.1 r.2 σ' ∧
        MR r.2 σ'.machineState ∧ P1.WritesIn st s r.1 (Mc.ProjW (L := L) H Cs s) ⦄ :=
  sys_entryStFU17 hARI hA hnd hM hKD hPA hT hmax htu hRef hSX hDR hJ hC hRR J n c hct hn hflag
    (fun x hx Z' H' Cs' Ac' Lst' D' s' a' hF J' => (hFin41 x hx Z' H' Cs' Ac' Lst' D' s' a' hF J').to13 hFpu) hDS

end

end

end Fl4Proofs.P3.SInvR.G5
