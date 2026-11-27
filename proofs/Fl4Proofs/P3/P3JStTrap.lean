/-
P3 (p3J gen 22): **the `int $N` (trap) entry at given ghosts, stable, on U41's finish record** (stage A; stages
Q / K in P3JStTrapQ / P3JStTrapK, as P3JStEv for the user-exception / VM-fault / unknown-syscall entries).

* **`jEvRef_trapSt`**: XTopJointKEntryEv4's `jEvRef_trap` (same premises) with `JStab Z H Cs` beside `RJM` at the
  same spec outcome. The run is the same: the FaultIP write (`fip_pre`, at `Z.mv Z.G V0`), then under
  `TRAP_SYSCALLS` the #GP user exception (StPostEv's `jEvRef_fltSt` with P3JStEv's `jFltHyp_userSt`), otherwise
  the unknown syscall of a non-negative number (`jEvRef_fltSt` with StPostEv's `jFltHyp_unkSt`). `JStab.mv` drops
  the FaultIP write's VSpace sets.
* **`trap_entryStU41`**: from `JReachU17` and a given `JAtZ Z H Cs` (with `VxE Z`), for a vector below 256 and a
  non-idle current thread, under the per-entry `KFinEv41` at the FaultIP states (+ `FpuImplDet`), every outcome of
  `handle_trap_syscall` is a `KEvSpec (.trap v)` event's `EvOut true` outcome that is `JReachU17` **and**
  `JStab Z H Cs` (P3JStEv's `sysU_entryStU41` with the trap run; `JReachU3.trap`).

Premises: XTopJointKEntryEv4's / StPostEv's platform facts, the clause conditions and the per-entry `KFinEv41`
(discharged at the top, P3JMcTrap, as U43); no new premise. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JStEv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

open Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvF in
set_option maxHeartbeats 16000000 in
/-- (p3J gen 22) **`jEvRef_trap` with the stable ghosts** (module docstring; same premises). -/
theorem jEvRef_trapSt (hnd : Fl4Spec.numDomains = 1) {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} (v : U64) (hv : v.val < 256)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hX : SInvX σ) (hct0 : σ.curThread ≠ σ.idleThread)
    (hR : MR a σ.machineState)
    (hFin : ∀ ev, KEvSpec (.trap v) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      KFinEv (L := L) arI AR ev (KFrontTrap (st := st) arI s a) w.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_trap_syscall st arI s a v ⦃ r => ∃ ev σ', KEvSpec (.trap v) true ev ∧ EvOut true ev σ σ' ∧
      RJM (L := L) arI AR MR r.1 r.2 σ' ∧ JStab (L := L) arI AR Z H Cs r.1 r.2 σ' ⦄ := by
  have hct := cur_thread_eq (L := L) s
  generalize L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) = ct at hct
  obtain ⟨x, hk', hcur, V0, J0⟩ := fip_pre J hct
  generalize hs0 : L.wr s (regA ct layout.reg.FAULT_IP)
    (core.num.U64.wrapping_sub (L.mem s (regA ct layout.reg.NEXT_IP)) 2#u64) = s0 at J0
  have hF : ((), faultIPSt σ σ.curThread x) ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1 := by
    rw [fl4SyscallFaultIP_eq hk']; exact Set.mem_singleton _
  have hX0 : SInvX (faultIPSt σ σ.curThread x) := sinvX_fip hX _ hF
  have hct1 : (faultIPSt σ σ.curThread x).curThread ≠ (faultIPSt σ σ.curThread x).idleThread := hct0
  have hR0 : MR a (faultIPSt σ σ.curThread x).machineState := hR
  have hFin0 := fun ev hev => hFin ev hev _ hF
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
    have hE : syscall.handle_user_exception st arI s0 a 13#u64 code ⦃ r =>
        ∃ σ', EvOut false (.userLevelFault (13#u64 : U64).bv code.bv) (faultIPSt σ σ.curThread x) σ' ∧
          RJM (L := L) arI AR MR r.1 r.2 σ' ∧ JStab (L := L) arI AR (Z.mv Z.G V0) H Cs r.1 r.2 σ' ⦄ :=
      jEvRef_fltSt (ev := .userLevelFault (13#u64 : U64).bv code.bv) (G := brUS 13#u64 code)
        (B := brU (st := st) arI 13#u64 code) rfl (fun _ h => by cases h) (fun h => by cases h) J0 hX0 hct1 hR0
        (jFltHyp_userSt hnd hM hKD hA hX0 hct1 _ _ hU)
        (fun x hx Z' H' Cs' Ac' Lst' D' s' a' hfr J' => hFin0 _ (KEvSpec.trapF v _ _) x hx Z' H' Cs' Ac' Lst' D' s'
          a' ⟨ct, _, hct, Or.inl ⟨13#u64, code, by rw [hs0]; exact hfr⟩⟩ J')
        hARI hA hnd hM hKD hmrt hmb hT hmax htu
    refine WP.spec_mono hE ?_
    rintro r ⟨σ', hO, hRJ, hSt⟩
    exact ⟨_, σ', KEvSpec.trapF v _ _, ⟨((), faultIPSt σ σ.curThread x), hF, hO⟩, hRJ, hSt.mv⟩
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
    have hE := jEvRef_fltSt (ev := .unknownSyscall num.val) (G := brKS num.val)
      (B := brK (st := st) (arI := arI) num)
      rfl (fun _ h => by cases h) (fun h => by cases h) J0 hX0 hct1 hR0 (jFltHyp_unkSt hnd hM hKD hA hX0 hct1 num)
      (fun x hx Z' H' Cs' Ac' Lst' D' s' a' hfr J' => hFin0 _ (KEvSpec.trapU v _) x hx Z' H' Cs' Ac' Lst' D' s' a'
        ⟨ct, _, hct, Or.inr ⟨num, by rw [hs0]; exact hfr⟩⟩ J')
      hARI hA hnd hM hKD hmrt hmb hT hmax htu
    refine WP.spec_mono hE ?_
    rintro r ⟨σ', hO, hRJ, hSt⟩
    exact ⟨_, σ', KEvSpec.trapU v _, ⟨((), faultIPSt σ σ.curThread x), hF, hO⟩, hRJ, hSt.mv⟩

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 8000000 in
/-- (p3J gen 22) **The `int $N` entry at given ghosts, stable** (module docstring). -/
theorem trap_entryStU41 [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hDR : SetDlDetR (A := A) MR) (hFpu : FpuImplDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ)
    {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z]
    (v : U64) (hct : σ.curThread ≠ σ.idleThread) (hv : v.val < 256)
    (hFin41 : ∀ ev, KEvSpec (.trap v) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      KFinEv41 (L := L) arI AR ev (KFrontTrap (st := st) arI s a) w.2) :
    syscall.handle_trap_syscall st arI s a v ⦃ r =>
      ∃ ev σ', KEvSpec (.trap v) true ev ∧ EvOut true ev σ σ' ∧
        JReachU17 (L := L) arI AR MR r.1 r.2 σ' ∧ JStab (L := L) arI AR Z H Cs r.1 r.2 σ' ⦄ := by
  have hFin : ∀ ev, KEvSpec (.trap v) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      KFinEv13 (L := L) arI AR ev (KFrontTrap (st := st) arI s a) w.2 := fun ev he w hw =>
    (hFin41 ev he w hw).to13 hFpu
  obtain ⟨hJ3, hGp, hIv, hDv⟩ := hJ
  obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, hR, -, -, -⟩ := jreach_invU3 hnd hJ3
  have hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄ := hPA.minBudget
  have hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄ :=
    fun a => hT.mrt a
  have hD : SetDlDet := setDlDet_of arI hM hDR hR
  have hARK := hARI.toARKeep
  have hS := hX.sb
  have hU3 := sinvX_ut3 hX
  have hSg : SInvG.SpecGlobS σ := sinvX_sg hX
  have hFin' : ∀ ev, KEvSpec (.trap v) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      KFinEv (L := L) arI AR ev (KFrontTrap (st := st) arI s a) w.2 := fun ev he w hw =>
    ((((hFin ev he w hw).to11 (fun x hx => SInvIV.front_idleVtS σ.curThread true ev hSg (sinvX_idleOut hX) hU3 hIv
        x ⟨w, hw, hx⟩)).to8 hnd
      (SInvDom.dp_of_dl (SInvDom.dl_fl4SyscallFaultIP σ.curThread) σ w (sinvX_dom hX) hw)).to hnd hA hARK hRef hD hT
      (fun x hx o e => SInvF.fpuOwnOK_of_ft
        (SInvF.kcall_fo_fip true _ he.not_sys (by cases he <;> intro e <;> cases e)
          (SInvAll.SInvB.entryJ hS hct).ctAct ⟨hS.1.1.nq, hS.1.1.epq⟩ hS.1.1.ut hS.1.1.live hS.1.1.ft w hw x hx)
        o e)).to hA hD
  have hG := jEvRef_trapSt hnd v hv J hX hct hR hFin' hARI hA hM hKD hmrt hmb hT hmax htu
  refine WP.spec_mono (spec_and_eq hG fun _ h => h) ?_
  rintro ⟨s', a'⟩ ⟨⟨ev, σ', hK, hO, hRJM, hSt⟩, hrun⟩
  have hO' : EvOut true ev σ σ' := hO
  obtain ⟨w, hw, hy⟩ := hO
  exact ⟨ev, σ', hK, hO',
    ⟨JReachU3.trap v ev hJ3 hct hv hK hrun hO' hRJM,
      SInvGp.fipEv_gpmOut true ev hSg hU3 hGp hw _ hy, evOut_idleVtS hX hIv hO',
      SInvDV.fip_kcall_devRange _ true ev hU3 hDv w hw _ hy⟩, hSt⟩

end

end

end Fl4Proofs.P3.SInvR.G5
