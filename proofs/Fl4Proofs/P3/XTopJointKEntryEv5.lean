/-
P3 (DESIGN.md §9), invariant line G4 (g4i, KENTRY-PLAN g4i; g4g's handoff (9)):
**the unknown-syscall entry through `handle_syscall` at `J`** (no `JEvRef`).

FL4's `handle_syscall n` runs `syscall n true`: the FaultIP write, then for a
`TRAP_SYSCALLS` thread or a number outside `[SYSCALL_MIN, SYSCALL_MAX]`
`unknown_syscall_fault` / `handle_unknown_syscall` with `fast = true`, which
first tries `fastpath::fault`.

* The fast path: the m-line's fast-fault equivalence as it stands (P1
  `usf_same` / `hus_same`, from FastFin's `fault_same`) under `StoreExt` [P]
  and the general path's reads `FastFaultOK` [J] at the entry state (P1
  derives them from `EntryInv`, `AsidOff`, `FaultNvmPre`:
  `fastFaultOK_of_p1`, the route of `kernel_entry.entry_of7`); with the
  declined case (`P1.syscall_decline`) this makes `handle_syscall` equal to
  `handle_syscall_general` on an unknown number (`handle_syscall_unk_eq`).
* The debug / TLS numbers (KENTRY-PLAN g4g (7) FINDING): **`NoDbgSys`** [S],
  the lead-decided scope premise, a predicate on the number at the entry
  state: not one of FL4's debug / TLS syscalls (-12 … -20), and
  `SysVMEnter` (-23) only when the platform has no virtualization or the
  current thread has no bound VCPU (l4v verifies the configuration without
  `CONFIG_PRINTING` / debug syscalls and without VT-x). Under it
  `handle_unknown_syscall` is `unknown_syscall_fault`
  (`handle_unknown_syscall_nd`).
* **`UnkSys`** [S] (event): the entry is the unknown-syscall one, i.e. the
  number is outside the native range or the thread has `TRAP_SYSCALLS` set
  after the FaultIP write (the complement of the syscall step's `NativeSys` /
  `hflag`).
* `jEvRef_sysU`: the general path is the FaultIP write (`fip_pre`), then
  `usf_eq`'s shape and g4f's `jEvRef_flt` with `jFltHyp_unk` (FaultCorrN's
  unknown syscall), event `KEvSpec.sysU n (hcast n).val`.
-/
import Fl4Proofs.P3.XTopJointKEntryEv4
import Fl4Proofs.P1.FastFaultEnt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **[S] (event) The unknown-syscall entry** (module docstring): the number
is outside FL4's native range, or the current thread has `TRAP_SYSCALLS`
set after the FaultIP write (the complement of the native step's
`NativeSys` range and `hflag`). Asked at the entry state. -/
def UnkSys (n : I64) (s : S) : Prop :=
  n < fl4_abi.syscall.SYSCALL_MIN ∨ n > fl4_abi.syscall.SYSCALL_MAX ∨
    ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) ≠ 0#u64 ⦄

/-- **[S] No debug / TLS syscall** (module docstring; KENTRY-PLAN g4g (7)):
the number is none of FL4's debug / TLS syscalls (`SysDebugPutChar` …
`SysSetTLSBase`, -12 … -20), and `SysVMEnter` (-23) only where FL4 faults
it: the platform reports no virtualization, or the current thread has no
bound VCPU (its `VCPU` word after the FaultIP write is 0). l4v verifies the
configuration without debug syscalls (`CONFIG_PRINTING` off) and without
VT-x. Asked at the entry state. -/
def NoDbgSys (n : I64) (s : S) (a : A) : Prop :=
  n ≠ fl4_abi.syscall.SysDebugPutChar ∧ n ≠ fl4_abi.syscall.SysDebugDumpScheduler ∧
  n ≠ fl4_abi.syscall.SysDebugHalt ∧ n ≠ fl4_abi.syscall.SysDebugSnapshot ∧
  n ≠ fl4_abi.syscall.SysDebugCapIdentify ∧ n ≠ fl4_abi.syscall.SysDebugNameThread ∧
  n ≠ fl4_abi.syscall.SysDebugGetThreadAffinity ∧ n ≠ fl4_abi.syscall.SysDebugSendIPI ∧
  n ≠ fl4_abi.syscall.SysSetTLSBase ∧
  (n = fl4_abi.syscall.SysVMEnter → arI.virtualization a = ok 0#u64 ∨
    ∀ ct v, sched.cur_thread st s = ok ct →
      vcpu.bound st (L.wr s (regA ct layout.reg.FAULT_IP) v) ct = ok 0#u64)

/-- **`handle_unknown_syscall` without the debug / TLS arms** is
`unknown_syscall_fault` (any `fast`). -/
theorem handle_unknown_syscall_nd (hA : P0.ArchTotal arI) (s : S) (a : A) (n : I64) (fast : Bool)
    (h1 : n ≠ fl4_abi.syscall.SysDebugPutChar) (h2 : n ≠ fl4_abi.syscall.SysDebugDumpScheduler)
    (h3 : n ≠ fl4_abi.syscall.SysDebugHalt) (h4 : n ≠ fl4_abi.syscall.SysDebugSnapshot)
    (h5 : n ≠ fl4_abi.syscall.SysDebugCapIdentify) (h6 : n ≠ fl4_abi.syscall.SysDebugNameThread)
    (h7 : n ≠ fl4_abi.syscall.SysDebugGetThreadAffinity) (h8 : n ≠ fl4_abi.syscall.SysDebugSendIPI)
    (h9 : n ≠ fl4_abi.syscall.SysSetTLSBase)
    (hv : n = fl4_abi.syscall.SysVMEnter → arI.virtualization a = ok 0#u64 ∨
      ∀ t, sched.cur_thread st s = ok t → vcpu.bound st s t = ok 0#u64) :
    syscall.handle_unknown_syscall st arI s a n fast =
      syscall.unknown_syscall_fault st arI s a (IScalar.hcast .U64 n) fast := by
  have e1 : fl4_abi.config.PRINTING = true := by unfold fl4_abi.config.PRINTING; rfl
  have e2 : fl4_abi.config.DEBUG_BUILD = true := by unfold fl4_abi.config.DEBUG_BUILD; rfl
  have e3 : fl4_abi.config.SET_TLS_BASE_SELF = true := by unfold fl4_abi.config.SET_TLS_BASE_SELF; rfl
  have e4 : fl4_abi.config.ENABLE_SMP_SUPPORT = true := by unfold fl4_abi.config.ENABLE_SMP_SUPPORT; rfl
  have hct := cur_thread_eq (L := L) s
  generalize L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) = t at hct
  obtain ⟨i, hi, -⟩ := spec_exists (hA.virtualization a)
  unfold syscall.handle_unknown_syscall syscall.debug_syscall
  simp only [hct, bind_ok, e1, e2, e3, e4, h1, h2, h3, h4, h5, h6, h7, h8, h9, ↓reduceIte, lift, uncurry_apply_pair,
    Bool.false_eq_true]
  by_cases h10 : n = fl4_abi.syscall.SysVMEnter
  · simp only [if_pos h10]
    rcases hv h10 with hz | hb
    · simp only [hz, bind_ok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      all_goals (try rfl)
    · simp only [hi, hb t hct, bind_ok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ite_self]
      all_goals (try rfl)
  · simp only [if_neg h10]
    all_goals (try rfl)

end

/-! ## The fast path on an unknown number -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- **A run of `syscall n true` on an unknown number is the general run**
(`fast = false`), under `StoreExt` [P] and the reads `FastFaultOK` [J]:
`P1.syscall_decline` when no fast path answered, else `P1.usf_same` (trap
route) / `P1.hus_same` (out-of-range route); the `reply_recv` route needs a
native number with the trap flag clear, excluded by `UnkSys`. -/
theorem syscall_unk_gen (hX : P1.StoreExt st) {s : S} {a : A} {n : I64}
    (hF : P1.FastFaultOK (L := L) arI s a n) (hU : UnkSys (L := L) n s) {b : Bool} {s' : S} {a' : A}
    (h : syscall.syscall st arI s a n true = ok (b, s', a')) :
    syscall.syscall st arI s a n false = ok (false, s', a') := by
  cases b
  · exact P1.syscall_decline st arI h
  have h' := P1.spec_of_eq_fd h
  clear h
  unfold syscall.syscall at h' ⊢
  simp only [lift, bind_ok] at h' ⊢
  obtain ⟨t, et, h'⟩ := P1.spec_bind_inv h'
  rw [et]; simp only [bind_ok, uncurry_apply_pair]
  obtain ⟨nx, enx, h'⟩ := P1.spec_bind_inv h'
  rw [enx]; simp only [bind_ok, uncurry_apply_pair]
  obtain ⟨s1, es1, h'⟩ := P1.spec_bind_inv h'
  rw [es1]; simp only [bind_ok, uncurry_apply_pair]
  obtain ⟨hU1, hH⟩ := hF t nx s1 et enx es1
  obtain ⟨i1, e, h'⟩ := P1.spec_bind_inv h'
  rw [e]; simp only [bind_ok, uncurry_apply_pair]
  by_cases c1 : (i1 &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true
  · simp only [if_pos c1] at h' ⊢
    exact P1.usf_same arI hX hU1 (P1.eq_of_spec_fd h')
  simp only [if_neg c1] at h' ⊢
  by_cases c2 : n < fl4_abi.syscall.SYSCALL_MIN
  · simp only [if_pos c2] at h' ⊢; exact P1.hus_same arI hX hH (P1.eq_of_spec_fd h')
  simp only [if_neg c2] at h' ⊢
  by_cases c3 : n > fl4_abi.syscall.SYSCALL_MAX
  · simp only [if_pos c3] at h' ⊢; exact P1.hus_same arI hX hH (P1.eq_of_spec_fd h')
  exfalso
  rcases hU with hu | hu | hu
  · exact c2 hu
  · exact c3 hu
  · have hs1 : s1 = L.wr s (regA t layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64) := by
      have h0 := Endp.obj.Tcb.set_reg.spec (L := L) s t layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64)
      rw [es1, WP.spec_ok] at h0; exact h0
    have h0 := hu t (core.num.U64.wrapping_sub nx 2#u64) et
    rw [← hs1, e, WP.spec_ok] at h0
    exact h0 (by by_contra hne; exact c1 (bne_iff_ne.2 hne))

/-- **`handle_syscall` on an unknown number is the general entry** (module
docstring). -/
theorem handle_syscall_unk_eq (hA : P0.ArchTotal arI) (hX : P1.StoreExt st) {s : S} {a : A} {n : I64}
    (hF : P1.FastFaultOK (L := L) arI s a n) (hU : UnkSys (L := L) n s) :
    syscall.handle_syscall st arI s a n = syscall.handle_syscall_general st arI s a n := by
  obtain ⟨⟨b, s', a'⟩, e, -⟩ := P1.spec_ex_fd (P0.syscall.handle_syscall_fast.p0 st arI s a n L.total hA)
  have e' : syscall.syscall st arI s a n true = ok (b, s', a') := by
    unfold syscall.handle_syscall_fast at e; exact e
  unfold syscall.handle_syscall syscall.handle_syscall_general
  rw [e', syscall_unk_gen hX hF hU e']
  all_goals (try simp only [bind_ok, uncurry_apply_pair])
  all_goals (try rfl)

/-- **`FastFaultOK` from the P1 invariants** (the route of P1's
`kernel_entry.entry_of7`): at a state where P1's `EntryInv` holds (with the
`Hyps4` admissibility of its sets), `AsidOff` [J] and `FaultNvmPre` [J]
give the general path's reads `FastFaultOK`. This is where the premise of
`jEvRef_sysU` is checked to hold in P1-reachable states. -/
theorem fastFaultOK_of_p1 {T Ω Cs Sg Rp Scs Nt U : Set U64} {H : P1.Heap} {Z : U64 → Nat} {P3Ok : S → Prop}
    {Adm : P1.PSets → Prop} (hA : P0.ArchTotal arI)
    (GF : ∀ σ : P1.PSets, Adm σ → P1.Hyps4 st arI Adm Cs U P3Ok σ)
    (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩) {Ac : Set U64} {s : S} {a : A} {n : I64} (hP : P3Ok s)
    (h : P1.EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hAs : P1.AsidOff (L := L) Ω Sg s)
    (hNv : P1.FaultNvmPre (L := L) arI s a n) : P1.FastFaultOK (L := L) arI s a n := by
  have E0 : P1.EntryHyps0 st arI T Cs Ω H Sg Rp Scs Nt Z U P3Ok := by
    have G3 : P1.InvGaps st arI Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok := by
      obtain ⟨P, C, ⟨V, Pd⟩, Pt, G, -⟩ := GF _ hσ
      exact (G.gaps3 hA hσ C Pd Pt P.xfer).gaps hA P C
    exact (P1.EntryHyps.of_gaps hA hσ (fun σ'' h'' => (GF σ'' h'').1) (GF _ hσ).1 G3).toEntryHyps0
  exact P1.FastFaultOK.of_pre arI hA E0 hP h (P1.FastFaultPre.of_asid arI hA E0 (GF _ hσ).1.xfer hP h hAs hNv)

end

/-! ## The unknown-syscall entry at `J` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

variable (arI) in
/-- FL4's unknown-syscall entry up to the finish: after the FaultIP write of
the current thread, `budget_ok` and the unknown-syscall fault branch. -/
def KFrontSysU (n : I64) (s : S) (a : A) (s' : S) (a' : A) : Prop :=
  ∃ (t v0 : U64), sched.cur_thread st s = ok t ∧
    KFrontF2 (st := st) arI (brK (st := st) (arI := arI) (IScalar.hcast .U64 n))
      (L.wr s (regA t layout.reg.FAULT_IP) v0) a s' a'

/-- `unknown_syscall_fault … false` in `jEvRef_flt`'s shape, the flag dropped. -/
theorem usf_spec (s0 : S) (a : A) (num : U64) {P : S × A → Prop}
    (h : (Std.bind (syscall.budget_ok st arI s0 a) (uncurry fun b => uncurry fun s1 a1 =>
        Std.bind (if b then brK (st := st) (arI := arI) num s1 a1 else ok (s1, a1))
          (uncurry fun s2 a2 => syscall.finish st arI s2 a2))) ⦃ P ⦄) :
    syscall.unknown_syscall_fault st arI s0 a num false ⦃ r => P (r.2.1, r.2.2) ⦄ := by
  have e := usf_eq (st := st) (arI := arI) s0 a num (fun r => ok (r.2.1, r.2.2)) (fun _ _ _ => rfl)
  rw [← e] at h
  obtain ⟨x, hx, hK⟩ := P1.spec_bind_inv h
  rw [hx, WP.spec_ok]
  rw [WP.spec_ok] at hK
  exact hK

open Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvF in
set_option maxHeartbeats 16000000 in
/-- **The unknown-syscall entry at `J`** (module docstring): no `JEvRef`. -/
theorem jEvRef_sysU (hnd : Fl4Spec.numDomains = 1) {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} (n : I64)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hX : SInvX σ) (hct0 : σ.curThread ≠ σ.idleThread)
    (hR : MR a σ.machineState)
    (hU : UnkSys (L := L) n s) (hD : NoDbgSys (L := L) arI n s a)
    (hSX : P1.StoreExt st) (hFF : P1.FastFaultOK (L := L) arI s a n)
    (hFin : ∀ ev, KEvSpec (.sysU n) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      KFinEv (L := L) arI AR ev (KFrontSysU (st := st) arI n s a) w.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_syscall st arI s a n ⦃ r => ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
      RJM (L := L) arI AR MR r.1 r.2 σ' ⦄ := by
  rw [handle_syscall_unk_eq hA hSX hFF hU]
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
      ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
        RJM (L := L) arI AR MR r.2.1 r.2.2 σ' ⦄ := by
    have hE := jEvRef_flt (ev := .unknownSyscall (IScalar.hcast .U64 n).val)
      (G := brKS (IScalar.hcast .U64 n).val) (B := brK (st := st) (arI := arI) (IScalar.hcast .U64 n))
      rfl (fun _ h => by cases h) (fun h => by cases h) J0 hX0 hct1 hR0
      (jFltHyp_unk hnd hM hKD hA hX0 hct1 (IScalar.hcast .U64 n))
      (fun x hx Z' H' Cs' Ac' Lst' D' s' a' hfr J' => hFin0 _ (KEvSpec.sysU n _) x hx Z' H' Cs' Ac' Lst' D' s' a'
        ⟨ct, _, hct, by rw [hs0]; exact hfr⟩ J')
      hARI hA hnd hM hKD hmrt hmb hT hmax htu
    refine WP.spec_mono (usf_spec s0 a (IScalar.hcast .U64 n) hE) ?_
    rintro r ⟨σ', hO, hRJ⟩
    exact ⟨_, σ', KEvSpec.sysU n _, ⟨((), faultIPSt σ σ.curThread x), hF, hO⟩, hRJ⟩
  suffices hG : syscall.syscall st arI s a n false ⦃ r => ∃ ev σ', KEvSpec (.sysU n) true ev ∧
      EvOut true ev σ σ' ∧ RJM (L := L) arI AR MR r.2.1 r.2.2 σ' ⦄ by
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

end

end

end Fl4Proofs.P3
