/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN g3b, INV-PLAN §4 G3):
**`kernel_entryJ28` = `kernel_entryJ27` without `hNS` / `hNSR`.** Both were
∀-over-states [S] premises (`NativeScope` at every `JHoleAt` / `JAtZR`
state), false for any instance with a `RunningVM` thread (INV-PLAN §3), so
J27 and every top below it were vacuous there. Each consumer now takes
`NativeScope` at its own state, threaded from `SInvB`'s `SInvA.ns` at the
entry state σ by invA's NSK family (spec only, XTopJointKEntry28S):

* the budget check at the `FaultIP` state: `ns_fl4SyscallFaultIP`;
* the dispatch state σb (σb's heap is the `FaultIP` state's): `ns_of_kheap`;
* the preemption hole of an invocation (the `JAtPreMV` state = the spec's
  error outcome of `fl4HandleInvocationR` from σb): `ns_fl4HandleInvocationR`,
  then `hPre_ofZQIMN` (XTopJointMRHole): at the hole itself, and after the
  MCS part (`mcsPPJ*M` posts now carry `NativeScope σ → NativeScope σ'`, from
  `ns_chargeBudget` / `ns_checkBudget` at their spec endpoints) for the
  interrupt (`afterInv_of_mcsIMN`, `handleIrqJIAN`, `JAtZ.signal_atN`);
* every `finish` (after a stopping budget check, after the dispatch, after
  a preemption) starts at a front-end outcome: `ns_front`, then
  `jat_finishJRN` (`jat_finishJRP` at `P := NativeScope`: the fired timers by
  `ns_fl4Awaken`, the activated thread after `schedule` by `ns_schedule`).

The dispatch layer of `kernel_entryJ13PU` (XTopJointKEntry23P) is restated
here with `NativeScope` at the dispatch state (`…N` names: `invoke_afterJMUN`,
`dispatch_invokeJMUN`, `mid_invRecvJMUN`, `dispatch_midJMUN`,
`dispatch_invokeJAllMUN`, `dispatch_all13PUN`, `kernel_entryJ13PUN`), with
`kPreFinHypJI_ofN` and `jat_finishJRN`. NEW TOP `kernel_entryJ28`: J27's
premises minus `hNS` / `hNSR`; nothing added.
-/
import Fl4Proofs.P3.XTopJointKEntry27
import Fl4Proofs.P3.XTopJointKEntry28S
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop}

set_option maxHeartbeats 4000000 in
/-- **FL4's `finish` from `JAtZR` with `NativeScope` at its own state** (module
docstring): `jat_finishJRP` at `P := NativeScope`: along the fired timers by
`ns_fl4Awaken` (the signal step's `RunningVM` case is then absurd), after
`schedule` by `ns_schedule` (`hvm`). -/
theorem jat_finishJRN {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hN : NativeScope σ)
    (hd : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ)
    (hnd : Fl4Spec.numDomains = 1) (hAT : P0.ArchTotal arI)
    (hVt : ∀ (V1 : XVs) (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (Ac1 : Set U64) (Lst1 : U64 → List U64)
      (D1 : Set U64), JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s1 a1 σ1 → ∀ t ∈ Z.T,
        Z.th t = some .tcb ∧ ∀ p asid, capAt (L.mem s1) (slotOf t 1) = ok (.Pml4 p true asid) → asid ≠ 0#u64)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hA : ArchSwF st arI Z.N Z.T Z.C Z.c) (hAN : ArchNdF st Z.N Z.T Z.C Z.c) (hFO : FpuOwnOK σ)
    (hsni : SniHyp st arI Z.N Z.T Z.C Z.c) (hsend : SendHyp st arI Z.N Z.T Z.C Z.c) (hT : TimeAgree arI)
    (hTail : sched.schedule st arI s a ⦃ r => ∀ (rf : S × A) σ1 σ' (D1 : Set U64), Fires σ σ1 →
      timer.fire st arI s a = ok rf →
      ((∃ (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D2 : Set U64),
        JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D2 rf.1 rf.2 σ1) ∨
       ∃ (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D2 : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D2 rf.1 rf.2 σ1) →
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) →
      P1.WritesIn st rf.1 r.1 (KFootN st Z.T Z.N Z.C Z.c rf.1 σ1) →
      SchedRel st Z.N Z.T Z.C Z.c r.1 σ' → Inv σ' → CurInv σ' → ActIdle σ' →
      SchTailHypsR AR Z H D1 r.1 r.2 σ' ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.finish st arI s a ⦃ r => ∃ (σ1 σ' : Fl4Spec.State Unit), ((), σ1) ∈ (Fl4Spec.fl4Awaken (Z := Unit) σ).1 ∧
      (Fl4Spec.schedule (Z := Unit) >>= fun _ => Fl4Spec.activateThread) σ1 = ({((), σ')}, False) ∧
      ((), σ') ∈ ((Fl4Spec.fl4Awaken (Z := Unit) >>= fun _ => Fl4Spec.schedule >>= fun _ => Fl4Spec.activateThread) σ).1 ∧
      RJ (L := L) arI AR r.1 r.2 σ' ∧ ∃ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' r.1 r.2 σ' ⦄ :=
  jat_finishJRP s a σ J hd hnd hAT hVt (fun σ1 => NativeScope σ1)
    (fun σ1 h => SInv.ns_fl4Awaken σ hN ((), σ1) (mem_fl4Awaken_of h))
    (fun _ _ _ _ _ _ _ _ _ _ _ hP _ _ ⟨_, t, tcb, _, hkt, hvm⟩ => absurd hvm (hP t tcb hkt)) hmb
    hA hAN hFO hsni hsend hT hTail hmax htu
    (fun σ1 σ2 _ _ hF hsc _ x hk =>
      SInv.ns_schedule σ1 (SInv.ns_fl4Awaken σ hN ((), σ1) (mem_fl4Awaken_of hF)) ((), σ2)
        (by rw [hsc]; exact Set.mem_singleton _) _ x hk)

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
theorem invoke_afterJMUN [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (call bl don : Bool)
    (hG : JEntryGlobM (L := L) arI AR MR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAtM (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (hPD : JPreDecHypM (L := L) arI AR MR Z H Cs D s ar σ ct) (hR : MR ar σ.machineState)
    (hVT : ValidMachineTime σ) (hVI : ValidIrqMasks σ) (hN : NativeScope σ)
    (Q : Fl4Spec.State Unit → S × A → Prop)
    (hPre : ∀ (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit), RelTopM (L := L) s1 σ1 →
      JAtPreMV (L := L) arI AR MR s1 a1 σ1 → NativeScope σ1 →
      syscall.after_invocation st arI s1 a1 (.Err .Preempted) ⦃ r => Q σ1 (r.2.1, r.2.2) ⦄) :
    (do
      let (r, s1, a1) ← syscall.handle_invocation st arI s ar call bl don false (L.mem s (regA ct layout.reg.CAP))
      let (_, s2, a2) ← syscall.after_invocation st arI s1 a1 r
      ok (s2, a2)) ⦃ r => DispPost (L := L) arI AR Q (DispInv call bl don) σ r ⦄ := by
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
  have top : ∀ y, y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) true call bl don false
      (Fl4Spec.toBl (L.mem s (regA ct layout.reg.CAP)).bv)).run σ).1 → y ∈ ((DispInv call bl don).run σ).1 :=
    fun y hy => mem_bindE_ok (mem_liftE (ε := Unit) hreg) hy
  have hok : ∀ {α : Type} {x : α} {P : α → Prop}, P x → ok x ⦃ P ⦄ := fun h => by rw [WP.spec_ok]; exact h
  refine WP.spec_bind (handle_invocation_entryJMU arI s ar σ J ct hct call bl don false _ hG hE hP hPD hR hVT hVI hN) ?_
  rintro ⟨r, s1, a1⟩ ⟨y, hy, hres, hrel, hX⟩
  rcases hres with ⟨rfl, hy1⟩ | ⟨rfl, hy1⟩
  · show (do
      let (_, s2, a2) ← syscall.after_invocation st arI s1 a1 (.Ok ())
      ok (s2, a2)) ⦃ _ ⦄
    rw [show syscall.after_invocation st arI s1 a1 (.Ok ()) = ok (true, s1, a1) by
      unfold syscall.after_invocation; rfl, bind_ok]
    refine hok ?_
    exact ⟨y, top y hy, Or.inl ⟨hy1, hrel, ifP_X (fun h => by cases h) hX⟩⟩
  · rw [if_pos rfl] at hX
    refine WP.spec_bind (hPre s1 a1 y.2 hrel hX (SInv.ns_fl4HandleInvocationR true call bl don false _ σ hN y hy)) ?_
    rintro ⟨b, s2, a2⟩ hQ
    refine hok ?_
    exact ⟨y, top y hy, Or.inr ⟨hy1, hQ⟩⟩

set_option maxHeartbeats 4000000 in
theorem dispatch_invokeJMUN [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (call bl don : Bool)
    (hn : InvSys number call bl don)
    (hG : JEntryGlobM (L := L) arI AR MR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAtM (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (hPD : JPreDecHypM (L := L) arI AR MR Z H Cs D s ar σ ct) (hR : MR ar σ.machineState)
    (hVT : ValidMachineTime σ) (hVI : ValidIrqMasks σ) (hN : NativeScope σ)
    (Q : Fl4Spec.State Unit → S × A → Prop)
    (hPre : ∀ (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit), RelTopM (L := L) s1 σ1 →
      JAtPreMV (L := L) arI AR MR s1 a1 σ1 → NativeScope σ1 →
      syscall.after_invocation st arI s1 a1 (.Err .Preempted) ⦃ r => Q σ1 (r.2.1, r.2.2) ⦄) :
    syscall.dispatch_syscall st arI s ar number ⦃ r => DispPost (L := L) arI AR Q (DispInv call bl don) σ r ⦄ := by
  have h := invoke_afterJMUN arI s ar σ J ct hct call bl don hG hE hP hPD hR hVT hVI hN Q hPre
  unfold syscall.dispatch_syscall
  rw [hct]; simp only [bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.CAP) ?_
  rintro c0 rfl
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.REPLY) ?_
  rintro c1 -
  have n65 : fl4_abi.syscall.SysNBSend ≠ fl4_abi.syscall.SysSend := by
    unfold fl4_abi.syscall.SysNBSend fl4_abi.syscall.SysSend; decide
  have n15 : fl4_abi.syscall.SysCall ≠ fl4_abi.syscall.SysSend := by
    unfold fl4_abi.syscall.SysCall fl4_abi.syscall.SysSend; decide
  have n16 : fl4_abi.syscall.SysCall ≠ fl4_abi.syscall.SysNBSend := by
    unfold fl4_abi.syscall.SysCall fl4_abi.syscall.SysNBSend; decide
  rcases hn with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · rw [if_pos rfl]; exact h
  · rw [if_neg n65, if_pos rfl]; exact h
  · rw [if_neg n15, if_neg n16, if_pos rfl]; exact h


end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
theorem mid_invRecvJMUN [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z] (hni : Entered σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (rg : U64) (sr : Fl4Spec.Register) (cr : Bool)
    (hrg : regIdx sr = rg)
    (hG : JEntryGlobM (L := L) arI AR MR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAtM (L := L) arI AR Z H Cs D s ar σ ct false false true true (L.mem s (regA ct rg)))
    (hW : MidRun.JMidPerfHyp true (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ)
    (hR : JMidRecvHyp (L := L) arI AR (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) cr σ)
    (hPD : JPreDecHypM (L := L) arI AR MR Z H Cs D s ar σ ct) (hR0 : MR ar σ.machineState)
    (hVT : ValidMachineTime σ) (hVI : ValidIrqMasks σ) (hN : NativeScope σ)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hMK : MRKeep arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄) :
    (do
      let (r, s1, a1) ← syscall.handle_invocation st arI s ar false false true true (L.mem s (regA ct rg))
      let (b, s2, a2) ← syscall.after_invocation st arI s1 a1 r
      if b then syscall.handle_recv st arI s2 a2 true cr else ok (s2, a2)) ⦃ r =>
      DispPostR (L := L) arI AR (PPQJI (L := L) arI AR) (DispMid sr cr) σ r ⦄ := by
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨-, xs, hks⟩ := J.xtop.curTcb hcur
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hxs := (J.xtop.irelK J.ks J.buf).1.toE.at_tcb hctT hks
  have hcp : Fl4Spec.dataToCptr (xs.tcbArch.tcbContext.userRegs sr) =
      Fl4Spec.toBl (L.mem s (regA ct rg)).bv := by
    rw [← hrg, hxs.regs]; rfl
  have hk' : σ.kheap σ.curThread = some (.tcb xs) := by rw [hcur]; exact hks
  have hreg := mem_getCapReg hk' sr
  rw [hcp] at hreg
  have hok : ∀ {α : Type} {x : α} {P : α → Prop}, P x → ok x ⦃ P ⦄ := fun h => by rw [WP.spec_ok]; exact h
  refine WP.spec_bind (WP.spec_mono (handle_invocation_entryJMU arI s ar σ J ct hct false false true true _ hG hE hP
    hPD hR0 hVT hVI hN)
    fun res h => And.intro (h.toPreMV.mid arI (MidRun.jMidRunHyp_of hW) (J.midEntry hni hE.cnf)) h) ?_
  rintro ⟨r, s1, a1⟩ ⟨⟨⟨y1, σm⟩, hy, ⟨hr1, hy1, hM⟩ | ⟨hr1, hy1, hrel, hX⟩⟩, hMV⟩
  · dsimp only at hr1 hy1 hM
    subst hr1 hy1
    show (do
      let (b, s2, a2) ← syscall.after_invocation st arI s1 a1 (.Ok ())
      if b then syscall.handle_recv st arI s2 a2 true cr else ok (s2, a2)) ⦃ _ ⦄
    rw [show syscall.after_invocation st arI s1 a1 (.Ok ()) = ok (true, s1, a1) by
      unfold syscall.after_invocation; rfl, bind_ok]
    show (if true = true then syscall.handle_recv st arI s1 a1 true cr else ok (s1, a1)) ⦃ _ ⦄
    rw [if_pos rfl]
    refine WP.spec_mono (hR _ hy rfl s1 a1 hM) ?_
    rintro r ⟨z, hz, hrl, hJ⟩
    exact ⟨(.ok z.1, z.2), mem_bindE_ok (mem_liftE (ε := Unit) hreg) (mem_bindE_ok hy (mem_liftE hz)),
      Or.inl ⟨rfl, hrl, hJ⟩⟩
  · dsimp only at hr1
    subst hr1
    obtain ⟨⟨u', σm'⟩, hy', hc', hrel', hX'⟩ := hMV
    have hu' : u' = .error () := by
      rcases hc' with ⟨h1, -⟩ | ⟨-, h2⟩
      · cases h1
      · exact h2
    subst hu'
    rw [if_pos rfl] at hX'
    show (do
      let (b, s2, a2) ← syscall.after_invocation st arI s1 a1 (.Err .Preempted)
      if b then syscall.handle_recv st arI s2 a2 true cr else ok (s2, a2)) ⦃ _ ⦄
    refine WP.spec_bind (hPre_ofZQIMN hARI hA hnd hM hMK hPA hIA hmrt hG.maxTU hG.tu s1 a1 σm' hrel' hX'
      (SInv.ns_fl4HandleInvocationR true false false true true _ σ hN _ hy')) ?_
    rintro ⟨b, s2, a2⟩ ⟨hb, hQ⟩
    dsimp only at hb; subst hb
    show (if false = true then syscall.handle_recv st arI s2 a2 true cr else ok (s2, a2)) ⦃ _ ⦄
    rw [if_neg (by decide)]
    exact hok ⟨_, mem_bindE_ok (mem_liftE (ε := Unit) hreg) (mem_bindE_err hy'), Or.inr ⟨rfl, hQ⟩⟩

set_option maxHeartbeats 4000000 in
theorem dispatch_midJMUN [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z] (hni : Entered σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (c : Fl4Spec.Syscall) (rg : U64)
    (sr : Fl4Spec.Register) (cr : Bool) (hn : MidSysR number c rg sr cr)
    (hG : JEntryGlobM (L := L) arI AR MR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAtM (L := L) arI AR Z H Cs D s ar σ ct false false true true (L.mem s (regA ct rg)))
    (hW : MidRun.JMidPerfHyp true (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ)
    (hR : JMidRecvHyp (L := L) arI AR (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) cr σ)
    (hPD : JPreDecHypM (L := L) arI AR MR Z H Cs D s ar σ ct) (hR0 : MR ar σ.machineState)
    (hVT : ValidMachineTime σ) (hVI : ValidIrqMasks σ) (hN : NativeScope σ)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hMK : MRKeep arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄) :
    syscall.dispatch_syscall st arI s ar number ⦃ r =>
      DispPostR (L := L) arI AR (PPQJI (L := L) arI AR) (Fl4Spec.fl4HandleSyscall true c) σ r ⦄ := by
  have h := mid_invRecvJMUN s ar σ J hni ct hct rg sr cr hn.reg hG hE hP hW hR hPD hR0 hVT hVI hN hARI hA hnd hM hMK hPA hIA hmrt
  rw [fl4HandleSyscall_mid hn]
  unfold syscall.dispatch_syscall
  rw [hct]; simp only [bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.CAP) ?_
  rintro c0 -
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.REPLY) ?_
  rintro c1 rfl
  rcases hn with ⟨rfl, -, rfl, -, rfl⟩ | ⟨rfl, -, rfl, -, rfl⟩ | ⟨rfl, -, rfl, -, rfl⟩
  · rw [if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysSend by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysSend; decide), if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysNBSend by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysNBSend; decide), if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysCall by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysCall; decide), if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysRecv by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysRecv; decide), if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysNBRecv by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysNBRecv; decide), if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysWait by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysWait; decide), if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysNBWait by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysNBWait; decide), if_pos rfl]
    exact h
  · rw [if_neg (show fl4_abi.syscall.SysNBSendRecv ≠ fl4_abi.syscall.SysSend by unfold fl4_abi.syscall.SysNBSendRecv fl4_abi.syscall.SysSend; decide), if_neg (show fl4_abi.syscall.SysNBSendRecv ≠ fl4_abi.syscall.SysNBSend by unfold fl4_abi.syscall.SysNBSendRecv fl4_abi.syscall.SysNBSend; decide), if_neg (show fl4_abi.syscall.SysNBSendRecv ≠ fl4_abi.syscall.SysCall by unfold fl4_abi.syscall.SysNBSendRecv fl4_abi.syscall.SysCall; decide), if_neg (show fl4_abi.syscall.SysNBSendRecv ≠ fl4_abi.syscall.SysRecv by unfold fl4_abi.syscall.SysNBSendRecv fl4_abi.syscall.SysRecv; decide), if_neg (show fl4_abi.syscall.SysNBSendRecv ≠ fl4_abi.syscall.SysNBRecv by unfold fl4_abi.syscall.SysNBSendRecv fl4_abi.syscall.SysNBRecv; decide), if_neg (show fl4_abi.syscall.SysNBSendRecv ≠ fl4_abi.syscall.SysWait by unfold fl4_abi.syscall.SysNBSendRecv fl4_abi.syscall.SysWait; decide), if_neg (show fl4_abi.syscall.SysNBSendRecv ≠ fl4_abi.syscall.SysNBWait by unfold fl4_abi.syscall.SysNBSendRecv fl4_abi.syscall.SysNBWait; decide), if_neg (show fl4_abi.syscall.SysNBSendRecv ≠ fl4_abi.syscall.SysReplyRecv by unfold fl4_abi.syscall.SysNBSendRecv fl4_abi.syscall.SysReplyRecv; decide), if_pos rfl]
    refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.NBSEND_RECV_DEST) ?_
    rintro c2 rfl
    exact h
  · rw [if_neg (show fl4_abi.syscall.SysNBSendWait ≠ fl4_abi.syscall.SysSend by unfold fl4_abi.syscall.SysNBSendWait fl4_abi.syscall.SysSend; decide), if_neg (show fl4_abi.syscall.SysNBSendWait ≠ fl4_abi.syscall.SysNBSend by unfold fl4_abi.syscall.SysNBSendWait fl4_abi.syscall.SysNBSend; decide), if_neg (show fl4_abi.syscall.SysNBSendWait ≠ fl4_abi.syscall.SysCall by unfold fl4_abi.syscall.SysNBSendWait fl4_abi.syscall.SysCall; decide), if_neg (show fl4_abi.syscall.SysNBSendWait ≠ fl4_abi.syscall.SysRecv by unfold fl4_abi.syscall.SysNBSendWait fl4_abi.syscall.SysRecv; decide), if_neg (show fl4_abi.syscall.SysNBSendWait ≠ fl4_abi.syscall.SysNBRecv by unfold fl4_abi.syscall.SysNBSendWait fl4_abi.syscall.SysNBRecv; decide), if_neg (show fl4_abi.syscall.SysNBSendWait ≠ fl4_abi.syscall.SysWait by unfold fl4_abi.syscall.SysNBSendWait fl4_abi.syscall.SysWait; decide), if_neg (show fl4_abi.syscall.SysNBSendWait ≠ fl4_abi.syscall.SysNBWait by unfold fl4_abi.syscall.SysNBSendWait fl4_abi.syscall.SysNBWait; decide), if_neg (show fl4_abi.syscall.SysNBSendWait ≠ fl4_abi.syscall.SysReplyRecv by unfold fl4_abi.syscall.SysNBSendWait fl4_abi.syscall.SysReplyRecv; decide), if_neg (show fl4_abi.syscall.SysNBSendWait ≠ fl4_abi.syscall.SysNBSendRecv by unfold fl4_abi.syscall.SysNBSendWait fl4_abi.syscall.SysNBSendRecv; decide), if_pos rfl]
    exact h

set_option maxHeartbeats 4000000 in
/-- **The invoking dispatches ending in `PPQJI` under `MachPlat`**
(`dispatch_invokeJAll` with mr3's `hPre_ofZQIM`; no `PPPlat`/`IrqPlat`). -/
theorem dispatch_invokeJAllMUN [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (call bl don : Bool)
    (hn : InvSys number call bl don)
    (hG : JEntryGlobM (L := L) arI AR MR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAtM (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (hPD : JPreDecHypM (L := L) arI AR MR Z H Cs D s ar σ ct) (hR : MR ar σ.machineState)
    (hVT : ValidMachineTime σ) (hVI : ValidIrqMasks σ) (hN : NativeScope σ)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hMK : MRKeep arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄) :
    syscall.dispatch_syscall st arI s ar number ⦃ r =>
      DispPost (L := L) arI AR (PPQJI (L := L) arI AR) (Fl4Spec.fl4HandleSyscall true (invSysOf call bl)) σ r ⦄ := by
  rw [fl4HandleSyscall_inv hn]
  exact dispatch_invokeJMUN arI s ar σ J ct hct number call bl don hn hG hE hP hPD hR hVT hVI hN _
    fun s1 a1 σ1 h1 h2 h3 => WP.spec_mono (hPre_ofZQIMN hARI hA hnd hM hMK hPA hIA hmrt hG.maxTU hG.tu s1 a1 σ1 h1 h2 h3)
      fun _ h => h.2

set_option maxHeartbeats 4000000 in
/-- **Every native dispatch at `J` under `MachPlat`** (`dispatch_all9M` with
`KDispHyps13PU`; the mid receive leaves narrowed as `KDispHyps15M.to14M` …
`to9M`). -/
theorem dispatch_all13PUN [Fl4Proofs.P1.PlainStore st] (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hni : Entered σ) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c) (hK : KDispHyps13PU (L := L) arI AR MR Z H Cs D s a σ n c)
    (hR : MR a σ.machineState) (hVI : ValidIrqMasks σ) (hN : NativeScope σ)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hMK : MRKeep arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.dispatch_syscall st arI s a n ⦃ r =>
      DispPostR (L := L) arI AR (PPQJI (L := L) arI AR) (Fl4Spec.fl4HandleSyscall true c) σ r ⦄ := by
  have hct := cur_thread_eq (L := L) s
  rcases hn with ⟨call, bl, don, hi, rfl⟩ | ⟨bl, cr, hr, rfl⟩ | ⟨rfl, rfl⟩ | hm
  · obtain ⟨hG, hE, hP, hPD⟩ := hK.inv _ call bl don hct hi
    exact WP.spec_mono (dispatch_invokeJAllMUN s a σ J _ hct n call bl don hi hG hE hP hPD hR hK.vmt hVI hN hARI
      hA hnd hM hMK hPA hIA hmrt) fun _ h => h.toR
  · obtain ⟨hnq, hvfh⟩ := hK.recv bl cr hr
    exact WP.spec_mono (dispatch_recvJL true hA s a σ J hni hct hnq hvfh n bl cr hr hmax (htu a))
      fun _ ⟨y, hy, h1, h2⟩ => ⟨y, hy, Or.inl ⟨h1, h2.1, h2.2.toRE⟩⟩
  · exact WP.spec_mono (dispatch_yieldJ true hA s a σ J hni hct (hmrt a) (hPA.minBudget a))
      fun _ ⟨y, hy, h1, h2⟩ => ⟨y, hy, Or.inl ⟨h1, h2.1, h2.2.toRE⟩⟩
  · obtain ⟨rg, sr, cr, hm'⟩ := midSysR_of hm
    obtain ⟨hG, hE, hP, hW, hV, hS6, hPD⟩ := hK.mid _ rg sr cr hct hm'
    obtain ⟨hs, hq⟩ := J.midCQ hni hE
    have hS : JMidRecvHypS (L := L) arI AR (Fl4Spec.toBl (L.mem s (regA _ rg)).bv) cr σ :=
      jMidRecvHypS_of hA (jMidLeavesHyp_of2 hA (jMidLeavesHyp_of3 hA (jMidLeavesHyp_of4 hA hmax htu
        (jMidLeavesHyp_of5 hA hmax htu (jMidLeavesHyp_of6 hA hmax htu hS6)))))
    exact dispatch_midJMUN s a σ J hni _ hct n c rg sr cr hm' hG hE hP hW.toP
      (jMidRecvHyp_of hA hG.maxTU hG.tu hs hq hW hV hS) hPD hR hK.vmt hVI hN hARI hA hnd hM hMK hPA hIA hmrt


end

end

end Fl4Proofs.P3
