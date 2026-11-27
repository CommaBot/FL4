/-
P3 (p3J gen 27): **the unknown-syscall and `int $N` entries' footprint** composed along P3's joint chain (stage A;
stage Q and the tops in P3JMcFltQ).

* `fipProjW`: the entry's `FAULT_IP` write (a register word of the current thread, a TCB of `H`) is a `ProjW`
  write.
* `brK_projW`: the unknown-syscall branch by P3JMcFlt's `faultProjW`.
* **`jEvRef_sysUFt`**: StPostEv's `jEvRef_sysUSt` re-run with the footprint as post: the `FAULT_IP` write, then
  P3JMcFlt's `jEvRef_fltFt` at the post-write `JAtZ` (`CKI` and `RR` of the `FaultIP` state by
  `hv_fl4SyscallFaultIP` / `rq_fl4SyscallFaultIP`); P1's `FastFaultOK` by `JAtZ.fastFaultOK` (no premise).
* **`jEvRef_trapFt`**: P3JStTrap's `jEvRef_trapSt` the same way (user branch `brU_projW`, unknown branch
  `brK_projW`).

No premise beyond the stated hypotheses (globals of the clause tops); no sorry. New module; no existing statement
changed.
-/
import Fl4Proofs.P3.P3JMcFlt
import Fl4Proofs.P3.P3JStTrap
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
  {AR : A → Fl4Spec.Cr3 → Prop}
variable {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A}
  {σ : Fl4Spec.State Unit}

/-- **The `FAULT_IP` write of the current thread is a `ProjW` write.** -/
theorem fipProjW (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) (v : U64) :
    P1.WritesIn st s (L.wr s (Fl4Proofs.P3.Endp.regA ct layout.reg.FAULT_IP) v) (ProjW (L := L) H Cs s) := by
  show P1.WritesIn st s (L.wr s (P1.regA ct layout.reg.FAULT_IP) v) _
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hH : H ct = some .tcb := J.zH.1 ct hctT
  have hTa : TcbAddr ct := J.blk.1.choose_spec.choose_spec.tcbs ct hH
  have hr : layout.reg.FAULT_IP.val < 384 := by simp [layout.reg.FAULT_IP]
  obtain ⟨K, hK, e⟩ := P1.regA_eq hTa hr
  have hK' : K.val < 4096 := by rw [hK]; simp [layout.reg.FAULT_IP]
  have hal : Aligned (P1.regA ct layout.reg.FAULT_IP) := by
    rw [e]; exact field_aligned hTa hK' (by rw [hK]; simp [layout.reg.FAULT_IP])
  refine (writesIn_wr hal).mono fun b hb => ?_
  subst hb
  rw [e]; exact obj_projW J.kern.heap (k := .tcb) hH (by simp only [P1.HKind.bits]; omega)

end

end Fl4Proofs.P3.Mc

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4 Fl4Proofs.P3.Mc

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- The unknown-syscall branch writes only `ProjW` at the post-budget `JAtZ` (`faultProjW`). -/
theorem brK_projW (hnd : Fl4Spec.numDomains = 1) (hA : P0.ArchTotal arI) {Z : XSets} {H : P1.Heap}
    {Cs : Set U64} {σ : Fl4Spec.State Unit} (hX : SInvX σ) (hct : σ.curThread ≠ σ.idleThread) (num : U64) :
    ∀ (σb : Fl4Spec.State Unit) (s1 : S) (a1 : A) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
      (true, σb) ∈ (specBudget σ).1 → JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' s1 a1 σb → SInvCk.CKI σb →
      brK (st := st) (arI := arI) num s1 a1 ⦃ r => P1.WritesIn st s1 r.1 (ProjW (L := L) H Cs s1) ⦄ := by
  intro σb s1 a1 Ac' Lst' D' hb J1 hC1
  obtain ⟨hni1, hnq1, -, -, -, -⟩ := budget_true_facts hnd hX hct hb
  obtain ⟨ct, hct1, -⟩ := spec_exists (sched.cur_thread.spec' (L := L) s1)
  show (do let t ← sched.cur_thread st s1; faults.handle_fault st arI s1 a1 t (.UnknownSyscall num)) ⦃ _ ⦄
  rw [hct1, bind_ok]
  exact faultProjW hA J1 hC1 hni1 hnq1 hct1 _

open Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvF in
set_option maxHeartbeats 16000000 in
/-- **The unknown-syscall entry writes only `ProjW`** from a `CKI ∧ RR` `JAtZ` state (module docstring). -/
theorem jEvRef_sysUFt (hnd : Fl4Spec.numDomains = 1) {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} (n : I64)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hX : SInvX σ) (hct0 : σ.curThread ≠ σ.idleThread)
    (hR : MR a σ.machineState) (hC : SInvCk.CKI σ) (hRR : SInvRr.RR σ)
    (hU : UnkSys (L := L) n s) (hD : NoDbgSys (L := L) arI n s a) (hSX : P1.StoreExt st)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_syscall st arI s a n ⦃ r => P1.WritesIn st s r.1 (ProjW (L := L) H Cs s) ⦄ := by
  have hFF := J.fastFaultOK (hX.entered hct0) hR hX.sb hX.ctQ (fun _ _ => offReady_faultIPSt hX.offReady)
    hARI hA hnd hM hmrt hmb hmax htu n
  rw [handle_syscall_unk_eq hA hSX hFF hU]
  have hct := cur_thread_eq (L := L) s
  generalize L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) = ct at hct
  obtain ⟨x, hk', hcur, V0, J0⟩ := fip_pre J hct
  have F0 := fipProjW J hct (core.num.U64.wrapping_sub (L.mem s (regA ct layout.reg.NEXT_IP)) 2#u64)
  generalize hs0 : L.wr s (regA ct layout.reg.FAULT_IP)
    (core.num.U64.wrapping_sub (L.mem s (regA ct layout.reg.NEXT_IP)) 2#u64) = s0 at J0 F0
  have hF : ((), faultIPSt σ σ.curThread x) ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1 := by
    rw [fl4SyscallFaultIP_eq hk']; exact Set.mem_singleton _
  have hX0 : SInvX (faultIPSt σ σ.curThread x) := sinvX_fip hX _ hF
  have hct1 : (faultIPSt σ σ.curThread x).curThread ≠ (faultIPSt σ σ.curThread x).idleThread := hct0
  have hR0 : MR a (faultIPSt σ σ.curThread x).machineState := hR
  have hC0 : SInvCk.CKI (faultIPSt σ σ.curThread x) :=
    SInvV.hv_fl4SyscallFaultIP (P := SInvCk.CKI) σ.curThread σ hC _ hF
  have hRR0 : SInvRr.RR (faultIPSt σ σ.curThread x) :=
    (SInvRr.rq_fl4SyscallFaultIP σ.curThread σ _ hF).trans hRR
  -- the current thread after the FaultIP write
  have hct0' : sched.cur_thread st s0 = ok ct := by
    have h0 := cur_thread_eq (L := L) s0
    generalize L.mem s0 (L.nodeAt s0 (L.cpu s0) layout.node.CUR_THREAD) = ct' at h0
    have e0 : (faultIPSt σ σ.curThread x).curThread = ct'.bv := (J0.curEq h0).1
    have e1 : ct' = ct := UScalar.eq_of_val_eq (by
      show ct'.bv.toNat = ct.bv.toNat
      rw [← e0, ← hcur]; rfl)
    rw [h0, e1]
  -- the general path's fault branch at the FaultIP state
  have hUSF : syscall.unknown_syscall_fault st arI s0 a (IScalar.hcast .U64 n) false ⦃ r =>
      P1.WritesIn st s r.2.1 (ProjW (L := L) H Cs s) ⦄ := by
    have hE := jEvRef_fltFt (ev := .unknownSyscall (IScalar.hcast .U64 n).val)
      (G := brKS (IScalar.hcast .U64 n).val) (B := brK (st := st) (arI := arI) (IScalar.hcast .U64 n))
      rfl (fun _ h => by cases h) (fun h => by cases h) J0 hX0 hct1 hR0 hC0 hRR0
      (jFltHyp_unkSt hnd hM hKD hA hX0 hct1 (IScalar.hcast .U64 n))
      (brK_projW hnd hA hX0 hct1 (IScalar.hcast .U64 n)) hARI hA hnd hM hKD hmrt hmb hmax htu
    refine WP.spec_mono (usf_spec s0 a (IScalar.hcast .U64 n) hE) ?_
    rintro r hr
    exact F0.projW_trans hr
  suffices hG : syscall.syscall st arI s a n false ⦃ r => P1.WritesIn st s r.2.1 (ProjW (L := L) H Cs s) ⦄ by
    unfold syscall.handle_syscall_general
    refine WP.spec_bind hG ?_
    rintro ⟨b, s', a'⟩ h
    first
      | exact (WP.spec_ok _).2 h
      | (simp only [uncurry_apply_pair, WP.spec_ok]; exact h)
  unfold syscall.syscall
  rw [hct, bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.NEXT_IP) ?_
  rintro nx rfl
  simp only [lift, bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s ct layout.reg.FAULT_IP _) ?_
  rintro s1 rfl
  rw [hs0]
  obtain ⟨fl, hfl, -⟩ := spec_exists (Fl4Proofs.P0.obj.Tcb.flags.p0 st ct s0 L.total)
  rw [hfl, bind_ok]
  try simp only [lift, bind_ok]
  by_cases htr : (fl &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true
  · rw [if_pos htr]
    try simp only [lift, bind_ok]
    exact hUSF
  rw [if_neg htr]
  have hrange : n < fl4_abi.syscall.SYSCALL_MIN ∨ n > fl4_abi.syscall.SYSCALL_MAX := by
    rcases hU with hu | hu | hu
    · exact Or.inl hu
    · exact Or.inr hu
    · exfalso
      have h0 := hu ct (core.num.U64.wrapping_sub (L.mem s (regA ct layout.reg.NEXT_IP)) 2#u64) hct
      rw [hs0, hfl, WP.spec_ok] at h0
      exact h0 (by by_contra hne; exact htr (bne_iff_ne.2 hne))
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, dv⟩ := hD
  have hv : n = fl4_abi.syscall.SysVMEnter → arI.virtualization a = ok 0#u64 ∨
      ∀ t, sched.cur_thread st s0 = ok t → vcpu.bound st s0 t = ok 0#u64 := fun hn => by
    rcases dv hn with h0 | h0
    · exact Or.inl h0
    · refine Or.inr fun t ht => ?_
      have e : t = ct := by
        have h1 : sched.cur_thread st s0 ⦃ v => v = ct ⦄ := by rw [hct0']; exact (WP.spec_ok _).2 rfl
        rw [ht, WP.spec_ok] at h1; exact h1
      subst e
      rw [← hs0]; exact h0 t _ hct
  have hH := handle_unknown_syscall_nd arI hA s0 a n false d1 d2 d3 d4 d5 d6 d7 d8 d9 hv
  by_cases hlt : n < fl4_abi.syscall.SYSCALL_MIN
  · rw [if_pos hlt, hH]; exact hUSF
  · rw [if_neg hlt, if_pos (hrange.resolve_left hlt), hH]; exact hUSF

open Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvF in
set_option maxHeartbeats 16000000 in
/-- **The `int $N` entry writes only `ProjW`** from a `CKI ∧ RR` `JAtZ` state (module docstring). -/
theorem jEvRef_trapFt (hnd : Fl4Spec.numDomains = 1) {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} (v : U64) (hv : v.val < 256)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hX : SInvX σ) (hct0 : σ.curThread ≠ σ.idleThread)
    (hR : MR a σ.machineState) (hC : SInvCk.CKI σ) (hRR : SInvRr.RR σ)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_trap_syscall st arI s a v ⦃ r => P1.WritesIn st s r.1 (ProjW (L := L) H Cs s) ⦄ := by
  have hct := cur_thread_eq (L := L) s
  generalize L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) = ct at hct
  obtain ⟨x, hk', hcur, V0, J0⟩ := fip_pre J hct
  have F0 := fipProjW J hct (core.num.U64.wrapping_sub (L.mem s (regA ct layout.reg.NEXT_IP)) 2#u64)
  generalize hs0 : L.wr s (regA ct layout.reg.FAULT_IP)
    (core.num.U64.wrapping_sub (L.mem s (regA ct layout.reg.NEXT_IP)) 2#u64) = s0 at J0 F0
  have hF : ((), faultIPSt σ σ.curThread x) ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1 := by
    rw [fl4SyscallFaultIP_eq hk']; exact Set.mem_singleton _
  have hX0 : SInvX (faultIPSt σ σ.curThread x) := sinvX_fip hX _ hF
  have hct1 : (faultIPSt σ σ.curThread x).curThread ≠ (faultIPSt σ σ.curThread x).idleThread := hct0
  have hR0 : MR a (faultIPSt σ σ.curThread x).machineState := hR
  have hC0 : SInvCk.CKI (faultIPSt σ σ.curThread x) :=
    SInvV.hv_fl4SyscallFaultIP (P := SInvCk.CKI) σ.curThread σ hC _ hF
  have hRR0 : SInvRr.RR (faultIPSt σ σ.curThread x) :=
    (SInvRr.rq_fl4SyscallFaultIP σ.curThread σ _ hF).trans hRR
  unfold syscall.handle_trap_syscall
  rw [hct, bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.NEXT_IP) ?_
  rintro nx rfl
  simp only [lift, bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s ct layout.reg.FAULT_IP _) ?_
  rintro s1 rfl
  rw [hs0]
  obtain ⟨fl, hfl, -⟩ := spec_exists (Fl4Proofs.P0.obj.Tcb.flags.p0 st ct s0 L.total)
  rw [hfl, bind_ok]
  try simp only [lift, bind_ok]
  by_cases htr : (fl &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true
  · rw [if_pos htr, shl_eq v 3#i32 (by decide) (by decide), bind_ok]
    try simp only [lift, bind_ok]
    generalize hcd : ((⟨v.bv <<< (3#i32 : I32).toNat⟩ : U64) ||| 2#u64) = code
    have hcode : code.val < 2 ^ 28 := by
      rw [← hcd, UScalar.val_or]
      exact Nat.or_lt_two_pow (shl3_lt v hv) (by decide)
    have hU : UserHw 13#u64 code := ⟨by decide, hcode⟩
    have hE := jEvRef_fltFt (ev := .userLevelFault (13#u64 : U64).bv code.bv) (G := brUS 13#u64 code)
        (B := brU (st := st) arI 13#u64 code) rfl (fun _ h => by cases h) (fun h => by cases h) J0 hX0 hct1 hR0
        hC0 hRR0 (jFltHyp_userSt hnd hM hKD hA hX0 hct1 _ _ hU) (brU_projW hnd hA hX0 hct1 _ _)
        hARI hA hnd hM hKD hmrt hmb hmax htu
    exact WP.spec_mono hE fun r hr => F0.projW_trans hr
  · rw [if_neg htr]
    refine WP.spec_bind (Endp.obj.Tcb.reg.spec s0 ct layout.reg.RAX) ?_
    rintro eax -
    rw [shl_eq v 24#i32 (by decide) (by decide), bind_ok]
    try simp only [lift, bind_ok]
    generalize hnm : ((⟨v.bv <<< (24#i32 : I32).toNat⟩ : U64) ||| (eax &&& 16777215#u64)) = num
    have hnum : num.val < 2 ^ 32 := by
      rw [← hnm, UScalar.val_or]
      refine Nat.or_lt_two_pow (shl24_lt v hv) ?_
      rw [UScalar.val_and]
      exact lt_of_le_of_lt Nat.and_le_right (by decide)
    rw [handle_unknown_syscall_pos s0 a num hnum, usf_eq s0 a num _ ?hK]
    swap
    · intro _ _ _; rfl
    have hE := jEvRef_fltFt (ev := .unknownSyscall num.val) (G := brKS num.val)
      (B := brK (st := st) (arI := arI) num)
      rfl (fun _ h => by cases h) (fun h => by cases h) J0 hX0 hct1 hR0 hC0 hRR0
      (jFltHyp_unkSt hnd hM hKD hA hX0 hct1 num) (brK_projW hnd hA hX0 hct1 num)
      hARI hA hnd hM hKD hmrt hmb hmax htu
    exact WP.spec_mono hE fun r hr => F0.projW_trans hr

end

end

end Fl4Proofs.P3
