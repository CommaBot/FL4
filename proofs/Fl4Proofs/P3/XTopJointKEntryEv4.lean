/-
P3 (DESIGN.md §9), invariant line G4 (g4g, KENTRY-PLAN g4g; g4f's handoff (2)):
**the `int $N` entry at `J`** (`handle_trap_syscall`, no `JEvRef`).

FL4's `handle_trap_syscall v`: the FaultIP write (as the syscall entry's,
`fip_pre`: `reg_wr_irel` + `JAtZ.regWrJ`, the spec's `fl4SyscallFaultIP`),
then under `TRAP_SYSCALLS` the #GP user exception `13, (v << 3) | 2`
(Ev3's `jFltHyp_user`; `UserHw` holds for a vector below 256), otherwise the
unknown syscall `(v << 24) | (rax & 0xffffff)`: a non-negative number, so
none of `handle_unknown_syscall`'s debug / TLS / `SysVMEnter` arms
(seL4's numbers are negative; `handle_unknown_syscall_pos`), and with
`fast = false` no fast path: `unknown_syscall_fault` is `budget_ok`, the
fault, `finish` (`usf_eq`), g4f's `jEvRef_flt` with `jFltHyp_unk`
(FaultCorrN's unknown syscall).

* `jEvRef_trap`: the entry ends related to the spec's event of this run
  (`KEvSpec.trapF` / `trapU`, chosen by FL4's flag and `rax` reads), after
  the spec's FaultIP write.
* `kernel_entry_reachE3T`: `kernel_entry_reachE3` with the `int $N` entry
  clause (premises: the vector below 256 [P], `KFinEv` at the FaultIP
  states; no `JEvRef`).
-/
import Fl4Proofs.P3.XTopJointKEntryEv3
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

/-! ## Scalars -/

theorem hcast_rt (x : U64) : IScalar.hcast .U64 (UScalar.hcast .I64 x) = x := by
  have h : (IScalar.hcast .U64 (UScalar.hcast .I64 x)).bv = x.bv := by
    rw [IScalar.hcast_bv_eq, UScalar.hcast_bv_eq]
    show (x.bv.setWidth 64).signExtend 64 = x.bv
    rw [BitVec.setWidth_eq, BitVec.signExtend_eq]
  exact UScalar.eq_of_val_eq (by show (IScalar.hcast .U64 (UScalar.hcast .I64 x)).bv.toNat = x.bv.toNat; rw [h])

theorem ne_of_hcast_big {num : U64} (hn : num.val < 2 ^ 32) {k : I64} (hk : 2 ^ 32 ≤ (IScalar.hcast .U64 k).val) :
    UScalar.hcast .I64 num ≠ k := by
  intro e
  have h := congrArg (fun i => (IScalar.hcast .U64 i).val) e
  simp only [hcast_rt] at h
  omega

/-! ## FL4's unknown-syscall path for a non-negative number -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- **`handle_unknown_syscall` of a number below `2^32`** (module docstring):
none of the debug / TLS / `SysVMEnter` arms, so `unknown_syscall_fault`. -/
theorem handle_unknown_syscall_pos (s : S) (a : A) (num : U64) (hn : num.val < 2 ^ 32) :
    syscall.handle_unknown_syscall st arI s a (UScalar.hcast .I64 num) false =
      syscall.unknown_syscall_fault st arI s a num false := by
  have n1 := ne_of_hcast_big hn (k := fl4_abi.syscall.SysDebugPutChar) (by unfold fl4_abi.syscall.SysDebugPutChar; decide)
  have n2 := ne_of_hcast_big hn (k := fl4_abi.syscall.SysDebugDumpScheduler)
    (by unfold fl4_abi.syscall.SysDebugDumpScheduler; decide)
  have n3 := ne_of_hcast_big hn (k := fl4_abi.syscall.SysDebugHalt) (by unfold fl4_abi.syscall.SysDebugHalt; decide)
  have n4 := ne_of_hcast_big hn (k := fl4_abi.syscall.SysDebugSnapshot)
    (by unfold fl4_abi.syscall.SysDebugSnapshot; decide)
  have n5 := ne_of_hcast_big hn (k := fl4_abi.syscall.SysDebugCapIdentify)
    (by unfold fl4_abi.syscall.SysDebugCapIdentify; decide)
  have n6 := ne_of_hcast_big hn (k := fl4_abi.syscall.SysDebugNameThread)
    (by unfold fl4_abi.syscall.SysDebugNameThread; decide)
  have n7 := ne_of_hcast_big hn (k := fl4_abi.syscall.SysDebugGetThreadAffinity)
    (by unfold fl4_abi.syscall.SysDebugGetThreadAffinity; decide)
  have n8 := ne_of_hcast_big hn (k := fl4_abi.syscall.SysDebugSendIPI)
    (by unfold fl4_abi.syscall.SysDebugSendIPI; decide)
  have n9 := ne_of_hcast_big hn (k := fl4_abi.syscall.SysSetTLSBase)
    (by unfold fl4_abi.syscall.SysSetTLSBase; decide)
  have n10 := ne_of_hcast_big hn (k := fl4_abi.syscall.SysVMEnter) (by unfold fl4_abi.syscall.SysVMEnter; decide)
  have e1 : fl4_abi.config.PRINTING = true := by unfold fl4_abi.config.PRINTING; rfl
  have e2 : fl4_abi.config.DEBUG_BUILD = true := by unfold fl4_abi.config.DEBUG_BUILD; rfl
  have e3 : fl4_abi.config.SET_TLS_BASE_SELF = true := by unfold fl4_abi.config.SET_TLS_BASE_SELF; rfl
  have e4 : fl4_abi.config.ENABLE_SMP_SUPPORT = true := by unfold fl4_abi.config.ENABLE_SMP_SUPPORT; rfl
  unfold syscall.handle_unknown_syscall syscall.debug_syscall
  simp only [cur_thread_eq (L := L) s, bind_ok, e1, e2, e3, e4, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, ↓reduceIte, lift, hcast_rt]
  rfl

/-- FL4's unknown-syscall fault branch. -/
abbrev brK (num : U64) : S → A → Result (S × A) :=
  fun s1 a1 => do let t ← sched.cur_thread st s1; faults.handle_fault st arI s1 a1 t (.UnknownSyscall num)

/-- **`unknown_syscall_fault` without the fast path** is a fault entry's shape
(`budget_ok`, the branch, `finish`), for any continuation dropping the flag. -/
theorem usf_eq (s0 : S) (a : A) (num : U64) (K : Bool × S × A → Result (S × A))
    (hK : ∀ b s a, K (b, s, a) = ok (s, a)) :
    Std.bind (syscall.unknown_syscall_fault st arI s0 a num false) K =
      Std.bind (syscall.budget_ok st arI s0 a) (uncurry fun b => uncurry fun s1 a1 =>
        Std.bind (if b then brK (st := st) (arI := arI) num s1 a1 else ok (s1, a1))
          (uncurry fun s2 a2 => syscall.finish st arI s2 a2)) := by
  unfold syscall.unknown_syscall_fault
  rw [Std.bind_assoc]
  congr 1
  funext x
  obtain ⟨b, s1, a1⟩ := x
  cases b
  · simp only [uncurry_apply_pair, Bool.false_eq_true, ↓reduceIte, bind_ok, Std.bind_assoc, hK]
    conv_rhs => rw [← Std.bind_pure (syscall.finish st arI s1 a1)]
    congr 1
    funext y
    obtain ⟨s2, a2⟩ := y
    simp only [uncurry_apply_pair, bind_ok, hK]
  · simp only [uncurry_apply_pair, ↓reduceIte, bind_ok, Std.bind_assoc, brK, Bool.false_eq_true, hK]
    congr 1
    funext t
    congr 1
    funext y
    obtain ⟨s2, a2⟩ := y
    simp only [uncurry_apply_pair, bind_ok, Std.bind_assoc, hK]
    conv_rhs => rw [← Std.bind_pure (syscall.finish st arI s2 a2)]
    congr 1
    funext z
    obtain ⟨s3, a3⟩ := z
    simp only [uncurry_apply_pair, bind_ok, hK]

end

/-! ## `JFltHyp` of the unknown-syscall fault -/

/-- The spec's unknown-syscall branch. -/
abbrev brKS (m : Nat) : Fl4Spec.SMonad Unit Unit :=
  do let t ← Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread
     Fl4Spec.handleFault t (.unknownSyscallException (BitVec.ofNat 64 m))

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 8000000 in
/-- **`JFltHyp` of the unknown-syscall fault** (as `jFltHyp_user`). -/
theorem jFltHyp_unk (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR)
    (hA : P0.ArchTotal arI) {Z : XSets} [VxE Z] {H : P1.Heap} {Cs : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hX : SInvX σ) (hct : σ.curThread ≠ σ.idleThread) (num : U64) :
    JFltHyp (L := L) arI AR MR Z H Cs (brK (st := st) (arI := arI) num) (brKS num.val) s a σ := by
  intro σb s1 a1 Ac' Lst' D' hb _ J1 hM1
  obtain ⟨hni1, hnq1, hvfh1, -, -, -⟩ := budget_true_facts hnd hX hct hb
  obtain ⟨ct, hct1, -⟩ := spec_exists (sched.cur_thread.spec' (L := L) s1)
  have hcur : σb.curThread = ct.bv := (J1.curEq hct1).1
  have hf : FaultCorrG (.UnknownSyscall num) (.unknownSyscallException num.bv) := Or.inr (Or.inl ⟨num, rfl, rfl⟩)
  show (do let t ← sched.cur_thread st s1; faults.handle_fault st arI s1 a1 t (.UnknownSyscall num)) ⦃ _ ⦄
  rw [hct1, bind_ok]
  refine WP.spec_mono (WP.spec_and (J1.faultHypJZG hA hni1 hct1 hnq1 hvfh1 hf)
    (MKD.faults_handle_fault L.total hA hKD hM1)) ?_
  rintro r ⟨⟨z, hz, -, Z', H', Cs', Ac'', Lst'', D'', J', _⟩, hMr⟩
  refine ⟨z, ?_, ⟨Z', H', Cs', Ac'', Lst'', D'', J'.toR, inferInstance⟩, msF_mr hM hMr (MachF.mfk_handleFaultG4 _ _ σb z hz)⟩
  have e1 : (BitVec.ofNat 64 num.val : BitVec 64) = num.bv := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt num.bv.isLt
  have hz' : z ∈ (Fl4Spec.handleFault (Z := Unit) σb.curThread
      (.unknownSyscallException (BitVec.ofNat 64 num.val)) σb).1 := by
    rw [hcur, e1]; exact hz
  exact mem_bind_nd (x := (σb.curThread, σb)) rfl hz'

/-! ## The `int $N` entry -/

variable (arI) in
/-- FL4's `int $N` entry up to the finish: after the FaultIP write of the
current thread, the user-exception or the unknown-syscall branch. -/
def KFrontTrap (s : S) (a : A) (s' : S) (a' : A) : Prop :=
  ∃ (t v0 : U64), sched.cur_thread st s = ok t ∧
    ((∃ n c : U64, KFrontF2 (st := st) arI (brU (st := st) arI n c) (L.wr s (regA t layout.reg.FAULT_IP) v0) a s' a') ∨
     (∃ num : U64, KFrontF2 (st := st) arI (brK (st := st) (arI := arI) num)
        (L.wr s (regA t layout.reg.FAULT_IP) v0) a s' a'))

set_option maxHeartbeats 16000000 in
/-- **The FaultIP write at `J`** (the syscall entry's, `kernel_entryJ13P`). -/
theorem fip_pre {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) :
    ∃ x, σ.kheap σ.curThread = some (.tcb x) ∧ σ.curThread = ct.bv ∧
      ∃ V0, JAtZ (L := L) arI AR (Z.mv Z.G V0) H Cs Ac Lst D
        (L.wr s (regA ct layout.reg.FAULT_IP) (core.num.U64.wrapping_sub (L.mem s (regA ct layout.reg.NEXT_IP)) 2#u64))
        a (faultIPSt σ σ.curThread x) := by
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hI := J.xtop.irelK J.ks J.buf
  obtain ⟨x, hk, -⟩ := hI.1.tcb ct hctT
  have hxs := hI.1.toE.at_tcb hctT hk
  have hk' : σ.kheap σ.curThread = some (.tcb x) := by rw [hcur]; exact hk
  generalize hv : core.num.U64.wrapping_sub (L.mem s (regA ct layout.reg.NEXT_IP)) 2#u64 = v
  have hvb : v.bv = x.tcbArch.tcbContext.userRegs .nextIP - 2 := by
    rw [← hv, core.num.U64.wrapping_sub_bv_eq, ← hxs.regs .nextIP, regIdx_nextIP]; rfl
  have hX2 := reg_wr_irel J.ip hI hctT hk Fl4Spec.Register.faultIP (by decide) v
  rw [regIdx_faultIP] at hX2
  obtain ⟨V0, J0⟩ := J.regWrJ hctT hk Fl4Spec.Register.faultIP v (by rw [regIdx_faultIP]; exact hX2)
  rw [regIdx_faultIP, hvb] at J0
  rw [← hcur] at J0
  exact ⟨x, hk', hcur, V0, J0⟩

theorem shl24_lt (v : U64) (hv : v.val < 256) : (⟨v.bv <<< (24#i32 : I32).toNat⟩ : U64).val < 2 ^ 32 := by
  show (v.bv <<< (24#i32 : I32).toNat).toNat < 2 ^ 32
  rw [show (24#i32 : I32).toNat = 24 from rfl, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have hv' : v.bv.toNat < 256 := hv
  have := Nat.mod_le (v.bv.toNat * 2 ^ 24) (2 ^ 64)
  omega

theorem shl3_lt (v : U64) (hv : v.val < 256) : (⟨v.bv <<< (3#i32 : I32).toNat⟩ : U64).val < 2 ^ 28 := by
  show (v.bv <<< (3#i32 : I32).toNat).toNat < 2 ^ 28
  rw [show (3#i32 : I32).toNat = 3 from rfl, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have hv' : v.bv.toNat < 256 := hv
  have := Nat.mod_le (v.bv.toNat * 2 ^ 3) (2 ^ 64)
  omega

open Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvF in
set_option maxHeartbeats 16000000 in
/-- **The `int $N` entry at `J`** (module docstring): no `JEvRef`. -/
theorem jEvRef_trap (hnd : Fl4Spec.numDomains = 1) {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
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
      RJM (L := L) arI AR MR r.1 r.2 σ' ⦄ := by
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
    have hE := jEvRef_user 13#u64 code J0 hX0 hct1 hR0 (jFltHyp_user hnd hM hKD hA hX0 hct1 _ _ hU)
      (fun x hx Z' H' Cs' Ac' Lst' D' s' a' hfr J' => hFin0 _ (KEvSpec.trapF v _ _) x hx Z' H' Cs' Ac' Lst' D' s' a'
        ⟨ct, _, hct, Or.inl ⟨13#u64, code, by rw [hs0]; exact hfr⟩⟩ J')
      hARI hA hnd hM hKD hmrt hmb hT hmax htu
    refine WP.spec_mono (hE : syscall.handle_user_exception st arI s0 a 13#u64 code ⦃ _ ⦄) ?_
    rintro r ⟨σ', hO, hRJ⟩
    exact ⟨_, σ', KEvSpec.trapF v _ _, ⟨((), faultIPSt σ σ.curThread x), hF, hO⟩, hRJ⟩
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
    have hE := jEvRef_flt (ev := .unknownSyscall num.val) (G := brKS num.val) (B := brK (st := st) (arI := arI) num)
      rfl (fun _ h => by cases h) (fun h => by cases h) J0 hX0 hct1 hR0 (jFltHyp_unk hnd hM hKD hA hX0 hct1 num)
      (fun x hx Z' H' Cs' Ac' Lst' D' s' a' hfr J' => hFin0 _ (KEvSpec.trapU v _) x hx Z' H' Cs' Ac' Lst' D' s' a'
        ⟨ct, _, hct, Or.inr ⟨num, by rw [hs0]; exact hfr⟩⟩ J')
      hARI hA hnd hM hKD hmrt hmb hT hmax htu
    refine WP.spec_mono hE ?_
    rintro r ⟨σ', hO, hRJ⟩
    exact ⟨_, σ', KEvSpec.trapU v _, ⟨((), faultIPSt σ σ.curThread x), hF, hO⟩, hRJ⟩

end


/-! ## The induction's tops with the `int $N` entry -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 8000000 in
/-- **The `int $N` entry at every reachable state** (module docstring): from a
non-idle thread, for a vector below 256 [P], given the finish bundle at the
FaultIP states, `handle_trap_syscall` ends related to the spec's event of
this run (no `JEvRef`), with `SInvX`, `MR`, and `JReachE3` again. -/
theorem kernel_entry_reachE3T (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachE3 (L := L) arI AR MR s a σ)
    (v : U64) (hv : v.val < 256) (hct : σ.curThread ≠ σ.idleThread)
    (hFin : ∀ ev, KEvSpec (.trap v) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      KFinEv (L := L) arI AR ev (KFrontTrap (st := st) arI s a) w.2) :
    syscall.handle_trap_syscall st arI s a v ⦃ r => ∃ ev σ', KEvSpec (.trap v) true ev ∧ EvOut true ev σ σ' ∧
      RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
      JReachE3 (L := L) arI AR MR r.1 r.2 σ' ⦄ := by
  obtain ⟨⟨Z, H, Cs, Ac, Lst, D, J, _⟩, hX, hR⟩ := jreach_invE3 hnd hJ
  have hE := jEvRef_trap hnd v hv J hX hct hR hFin hARI hA hM hKD hmrt hmb hT hmax htu
  obtain ⟨⟨s', a'⟩, hrun, ev, σ', hK, hO, hRJM⟩ := spec_exists hE
  rw [hrun, WP.spec_ok]
  have hev : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread := fun _ => hct
  exact ⟨ev, σ', hK, hO, hRJM.1, sinvX_evOut hnd hX hev (fun _ => sinvX_fip hX) hO, hRJM.2,
    JReachE3.event (.trap v) true ev hJ hK hev hrun hO hRJM⟩

end

end

end Fl4Proofs.P3
