/-
P3 (DESIGN.md §9), invariant line G4 (g4g, KENTRY-PLAN g4g; g4f's handoff):
**the fault entries at `J` without `JFltHyp`**.

* `jFltHyp_user`: g4f's `JFltHyp` [W] for the user-exception entry is a
  theorem (XTopJointFaultG's `JAtZ.faultHypJZG` with `FaultCorrN`'s user
  exception, at the budget-checked state: `specBudget_true_shape` keeps the
  kernel heap, the current / idle thread, the ready queues and the scheduler
  action, so `Entered`, l4v `ct_not_in_q` and `valid_fault_handler` come from
  `SInvX` at the entry state; `MR` by MachKeepF's `MKD.faults_handle_fault`
  and `mfk_handleFaultG4`). Its one input: **`UserHw n c`** [P], FL4's
  unmasked `number` / `code` within the spec's 32 / 28-bit masks.
* `jFltHyp_vmf`: the same for the VM-fault entry (the spec's
  `handleVmFault` throws the VM fault, `handleVmFault_err`, caught by
  `handleFault`). Its one input: **`VmfHw ad c ft σ`** [P], the hardware's
  `cr2` / error code against the spec's machine reads at the entry state.
* `JReachE3` / `jreach_invE3` / `kernel_entry_reachE3`: g4f's `JReachE2` with
  the user-exception and VM-fault steps under `UserHw` / `VmfHw` (no
  `JFltHyp`).
-/
import Fl4Proofs.P3.XTopJointKEntryEv2
import Fl4Proofs.P3.XTopJointFaultG
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.MachF
open Fl4Spec

theorem mfk_handleNoFaultG4 (thread : ObjRef) : MFK (handleNoFault (Z := Unit) thread) := by
  unfold handleNoFault; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_handleNoFaultG4 _)

theorem mfk_handleFaultG4 (thread : ObjRef) (ex : Fault) : MFK (handleFault (Z := Unit) thread ex) := by
  unfold handleFault; mfk_auto

end Fl4Proofs.P3.MachF

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

/-! ## Spec facts -/

/-- **The spec's budget check with a sufficient budget** changes only the
clock (`updateTimeStamp`; `checkBudgetRestart` returns `true` unchanged). -/
theorem specBudget_true_shape (hnd : Fl4Spec.numDomains = 1) {σ σb : Fl4Spec.State Unit}
    (h : (true, σb) ∈ (specBudget σ).1) :
    σb.kheap = σ.kheap ∧ σb.curThread = σ.curThread ∧ σb.idleThread = σ.idleThread ∧
      σb.readyQueues = σ.readyQueues ∧ σb.schedulerAction = σ.schedulerAction ∧
      σb.machineState = gctState σ.machineState := by
  unfold specBudget at h
  obtain ⟨⟨u, σu⟩, hu, h2⟩ := h
  cases u
  have hb' : σb = σu := Sched.checkBudgetRestart_true h2 rfl
  have hE := Sched.updateTimeStamp_eq' hnd (doMachineOp_single (getCurrentTime_eq σ.machineState))
  rw [hE] at hu
  have e : σu = _ := congrArg Prod.snd (Set.mem_singleton_iff.1 hu)
  rw [hb', e]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The spec's instruction-fetch word of a VM fault kind. -/
def ftBit : Fl4Spec.VMFaultType → Fl4Spec.Word
  | .x64DataFault => 0
  | .x64InstructionFault => 1

theorem and_mask_lt (x : BitVec 64) {n : Nat} (hn : n < 64) (h : x.toNat < 2 ^ n) :
    x &&& (Fl4Spec.mask n : BitVec 64) = x :=
  BitVec.eq_of_toNat_eq (by rw [spec_mask_and x n hn]; exact Nat.mod_eq_of_lt h)

/-- **l4v `handle_vm_fault` throws the VM fault** of the machine's fault
address and the thread's error register. -/
theorem handleVmFault_err {σ : Fl4Spec.State Unit} {t : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb}
    (hk : σ.kheap t = some (.tcb x)) (ft : Fl4Spec.VMFaultType) {b : Fl4Spec.Word}
    (hb : b = ftBit ft) :
    ((.error (.archFault (.vmFault (Fl4Spec.getFaultAddressVal σ.machineState)
        [b, x.tcbArch.tcbContext.userRegs .errorRegister &&& Fl4Spec.mask 5])), σ) :
        Except Fl4Spec.Fault Unit × Fl4Spec.State Unit) ∈ ((Fl4Spec.handleVmFault (Z := Unit) t ft).run σ).1 := by
  subst hb
  have h1 : Fl4Spec.doMachineOp (Z := Unit) Fl4Spec.getFaultAddress σ =
      ({(Fl4Spec.getFaultAddressVal σ.machineState, σ)}, False) := doMachineOp_single rfl
  unfold Fl4Spec.handleVmFault
  refine mem_bindE_ok (a := Fl4Spec.getFaultAddressVal σ.machineState) (s' := σ)
    (mem_liftE (x := (Fl4Spec.getFaultAddressVal σ.machineState, σ)) (by rw [h1]; exact Set.mem_singleton _)) ?_
  refine mem_bindE_ok (a := x.tcbArch.tcbContext.userRegs .errorRegister) (s' := σ)
    (mem_liftE (x := (x.tcbArch.tcbContext.userRegs .errorRegister, σ))
      (by rw [Endp.asUser_getRegister_eq hk]; exact Set.mem_singleton _)) ?_
  cases ft <;> exact mem_throw _

/-- FL4's instruction-fetch flag of a page-fault error code (bit 4). -/
theorem ins_iff (c : U64) :
    ((((⟨c.bv >>> (4#i32 : I32).toNat⟩ : U64) &&& 1#u64) != 0#u64) = true) ↔ c.val / 16 % 2 = 1 := by
  have hv : (((⟨c.bv >>> (4#i32 : I32).toNat⟩ : U64) &&& 1#u64)).val = c.val / 16 % 2 := by
    rw [UScalar.val_and]
    show (c.bv >>> (4#i32 : I32).toNat).toNat &&& 1 = _
    rw [show (4#i32 : I32).toNat = 4 from rfl, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      Nat.and_one_is_mod]
    rfl
  rw [bne_iff_ne]
  constructor
  · intro h
    have : (((⟨c.bv >>> (4#i32 : I32).toNat⟩ : U64) &&& 1#u64)).val ≠ 0 := fun e =>
      h (UScalar.eq_of_val_eq (by rw [e]; rfl))
    omega
  · intro h e
    have : (((⟨c.bv >>> (4#i32 : I32).toNat⟩ : U64) &&& 1#u64)).val = 0 := by rw [e]; rfl
    omega

/-! ## The hardware facts of the fault entries -/

/-- **[P] The user-exception entry's arguments** (module docstring): FL4
stores `number` / `code` unmasked where l4v's `handle_event` masks them to
32 / 28 bits. True for every x86-64 user exception FL4's entry dispatches
(`v < 32`; the error codes of #TS / #NP / #SS / #GP are selectors, of #CP
15 bits, #AC / #DF 0, #VC an SVM exit code; `int $N` under `TRAP_SYSCALLS`
passes `(vector << 3) | 2 < 2^11`). Asked at the one step. -/
def UserHw (n c : U64) : Prop := n.val < 2 ^ 32 ∧ c.val < 2 ^ 28

/-- **[P] The VM-fault entry's hardware reads** (module docstring), at the
entry state: the faulting address FL4 is given (`cr2`) is the spec's machine
fault address after the clock read (`getFaultAddressVal`, opaque); the error
code is the current thread's `ErrorRegister` (FL4's entry stores it there
before the call, entry.rs) and below 32 (P, W, U, RSVD, I/D: FL4 enables
neither PKE nor CET, cpu.rs); the spec's fault kind is the error code's
instruction-fetch bit (l4v `handle_vm_fault`'s `VMFaultType`). -/
structure VmfHw (ad c : U64) (ft : Fl4Spec.VMFaultType) (σ : Fl4Spec.State Unit) : Prop where
  addr : Fl4Spec.getFaultAddressVal (gctState σ.machineState) = ad.bv
  err : ∀ x, σ.kheap σ.curThread = some (.tcb x) → x.tcbArch.tcbContext.userRegs .errorRegister = c.bv
  lt : c.val < 32
  kind : ft = .x64InstructionFault ↔ c.val / 16 % 2 = 1

/-! ## `JFltHyp` for the user-exception and VM-fault entries -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

/-- The facts at a budget-checked state of a fault entry, from `SInvX` at the
entry state. -/
theorem budget_true_facts (hnd : Fl4Spec.numDomains = 1) {σ σb : Fl4Spec.State Unit} (hX : SInvX σ)
    (hct : σ.curThread ≠ σ.idleThread) (hb : (true, σb) ∈ (specBudget σ).1) :
    Entered σb ∧ (∀ d p, σb.curThread ∉ σb.readyQueues d p) ∧
      (∀ x, σb.kheap σb.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler) ∧
      σb.kheap σb.curThread = σ.kheap σ.curThread ∧ σb.curThread = σ.curThread ∧
      σb.machineState = gctState σ.machineState := by
  obtain ⟨ek, ect, eid, erq, esa, ems⟩ := specBudget_true_shape hnd hb
  have hni := hX.entered hct
  refine ⟨⟨by rw [ect, eid]; exact hni.1, by rw [esa]; exact hni.2⟩, by rw [ect, erq]; exact hX.ctQ, ?_,
    by rw [ek, ect], ect, ems⟩
  rw [ek, ect]
  exact fun x hk => hX.sb.1.1.vfh _ x hk

set_option maxHeartbeats 8000000 in
/-- **`JFltHyp` of the user-exception entry** (module docstring). -/
theorem jFltHyp_user (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR)
    (hA : P0.ArchTotal arI) {Z : XSets} {H : P1.Heap} {Cs : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hX : SInvX σ) (hct : σ.curThread ≠ σ.idleThread) (n c : U64) (hU : UserHw n c) :
    JFltHyp (L := L) arI AR MR Z H Cs (brU (st := st) arI n c) (brUS n c) s a σ := by
  intro σb s1 a1 Ac' Lst' D' hb _ J1 hM1
  obtain ⟨hni1, hnq1, hvfh1, -, -, -⟩ := budget_true_facts hnd hX hct hb
  obtain ⟨ct, hct1, -⟩ := spec_exists (sched.cur_thread.spec' (L := L) s1)
  have hcur : σb.curThread = ct.bv := (J1.curEq hct1).1
  have hf : FaultCorrG (.UserException n c) (.userException n.bv c.bv) := Or.inr (Or.inr (Or.inl ⟨n, c, rfl, rfl⟩))
  show (do let t ← sched.cur_thread st s1; faults.handle_fault st arI s1 a1 t (.UserException n c)) ⦃ _ ⦄
  rw [hct1, bind_ok]
  refine WP.spec_mono (WP.spec_and (J1.faultHypJZG hA hni1 hct1 hnq1 hvfh1 hf)
    (MKD.faults_handle_fault L.total hA hKD hM1)) ?_
  rintro r ⟨⟨z, hz, -, Z', H', Cs', Ac'', Lst'', D'', J'⟩, hMr⟩
  refine ⟨z, ?_, ⟨Z', H', Cs', Ac'', Lst'', D'', J'.toR⟩, msF_mr hM hMr (MachF.mfk_handleFaultG4 _ _ σb z hz)⟩
  have e1 : n.bv &&& (Fl4Spec.mask 32 : BitVec 64) = n.bv := and_mask_lt n.bv (by decide) hU.1
  have e2 : c.bv &&& (Fl4Spec.mask 28 : BitVec 64) = c.bv := and_mask_lt c.bv (by decide) hU.2
  have hz' : z ∈ (Fl4Spec.handleFault (Z := Unit) σb.curThread
      (.userException (n.bv &&& Fl4Spec.mask 32) (c.bv &&& Fl4Spec.mask 28)) σb).1 := by
    rw [hcur, e1, e2]; exact hz
  exact mem_bind_nd (x := (σb.curThread, σb)) rfl hz'

set_option maxHeartbeats 8000000 in
/-- **`JFltHyp` of the VM-fault entry** (module docstring). -/
theorem jFltHyp_vmf (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR)
    (hA : P0.ArchTotal arI) {Z : XSets} {H : P1.Heap} {Cs : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hX : SInvX σ) (hct : σ.curThread ≠ σ.idleThread) (ad c : U64) (ft : Fl4Spec.VMFaultType)
    (hV : VmfHw ad c ft σ) :
    JFltHyp (L := L) arI AR MR Z H Cs (brV (st := st) arI ad c) (brVS ft) s a σ := by
  intro σb s1 a1 Ac' Lst' D' hb _ J1 hM1
  obtain ⟨hni1, hnq1, hvfh1, ekc, ect, ems⟩ := budget_true_facts hnd hX hct hb
  obtain ⟨x0, hx0, -⟩ := (SInvAll.SInvB.entryJ hX.sb hct).ctAct
  have hkb : σb.kheap σb.curThread = some (.tcb x0) := by rw [ekc]; exact hx0
  obtain ⟨ct, hct1, -⟩ := spec_exists (sched.cur_thread.spec' (L := L) s1)
  have hcur : σb.curThread = ct.bv := (J1.curEq hct1).1
  show (do
      let t ← sched.cur_thread st s1
      let i ← c >>> 4#i32
      let i1 ← lift (i &&& 1#u64)
      let f ← vspace.vm_fault ad c (i1 != 0#u64)
      faults.handle_fault st arI s1 a1 t f) ⦃ _ ⦄
  rw [hct1, bind_ok, shr_eq c 4#i32 (by decide) (by decide), bind_ok]
  simp only [lift, bind_ok, vspace.vm_fault]
  generalize hins : (((⟨c.bv >>> (4#i32 : I32).toNat⟩ : U64) &&& 1#u64) != 0#u64) = ins
  have hii := (ins_iff c).trans hV.kind.symm
  rw [hins] at hii
  have hf : FaultCorrG (.VmFault ad c ins) (.archFault (.vmFault ad.bv [(if ins then 1#u64 else 0#u64).bv, c.bv])) :=
    Or.inr (Or.inr (Or.inr ⟨ad, c, ins, rfl, rfl⟩))
  refine WP.spec_mono (WP.spec_and (J1.faultHypJZG hA hni1 hct1 hnq1 hvfh1 hf)
    (MKD.faults_handle_fault L.total hA hKD hM1)) ?_
  rintro r ⟨⟨z, hz, -, Z', H', Cs', Ac'', Lst'', D'', J'⟩, hMr⟩
  refine ⟨z, ?_, ⟨Z', H', Cs', Ac'', Lst'', D'', J'.toR⟩, msF_mr hM hMr (MachF.mfk_handleFaultG4 _ _ σb z hz)⟩
  have hb0 : (if ins then 1#u64 else 0#u64).bv = ftBit ft := by
    cases ft <;> cases ins
    · rfl
    · exact absurd (hii.1 rfl) (by intro h; cases h)
    · exact absurd (hii.2 rfl) (by intro h; cases h)
    · rfl
  have he := handleVmFault_err hkb ft hb0
  have e5 : x0.tcbArch.tcbContext.userRegs .errorRegister &&& (Fl4Spec.mask 5 : BitVec 64) = c.bv := by
    rw [hV.err x0 hx0]; exact and_mask_lt c.bv (by decide) hV.lt
  rw [e5, ems, hV.addr] at he
  have hz' : z ∈ (Fl4Spec.NonDetE.catch (Fl4Spec.handleVmFault (Z := Unit) σb.curThread ft)
      (Fl4Spec.handleFault σb.curThread) σb).1 :=
    mem_catch_err he (by rw [hcur]; exact hz)
  exact mem_bind_nd (x := (σb.curThread, σb)) rfl hz'

end

/-! ## The induction -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **The reachable joint states** (module docstring): `JReachE2` with the
user-exception and VM-fault steps under their hardware facts. -/
inductive JReachE3 : S → A → Fl4Spec.State Unit → Prop
  | start {s : S} {a : A} {σ : Fl4Spec.State Unit} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
      {Lst : U64 → List U64} {D : Set U64} :
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SInvX σ → MR a σ.machineState → JReachE3 s a σ
  | step {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (n : I64)
      (c : Fl4Spec.Syscall) :
      JReachE3 s a σ → σ.curThread ≠ σ.idleThread → NativeSys n c →
      syscall.handle_syscall st arI s a n = ok (s', a') →
      ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 →
      RJM (L := L) arI AR MR s' a' σ' → JReachE3 s' a' σ'
  | irq {s : S} {a a1 : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (w : U64) :
      JReachE3 s a σ → IrqHw AR MR a a1 σ w → syscall.handle_interrupt_entry st arI s a1 w = ok (s', a') →
      EvOut false .interrupt σ σ' → RJM (L := L) arI AR MR s' a' σ' → JReachE3 s' a' σ'
  | user {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (n c : U64) :
      JReachE3 s a σ → σ.curThread ≠ σ.idleThread → UserHw n c →
      syscall.handle_user_exception st arI s a n c = ok (s', a') →
      EvOut false (.userLevelFault n.bv c.bv) σ σ' → RJM (L := L) arI AR MR s' a' σ' → JReachE3 s' a' σ'
  | vmf {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (ad c : U64)
      (ft : Fl4Spec.VMFaultType) :
      JReachE3 s a σ → σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
      syscall.handle_vm_fault st arI s a ad c = ok (s', a') →
      EvOut false (.vmFaultEvent ft) σ σ' → RJM (L := L) arI AR MR s' a' σ' → JReachE3 s' a' σ'
  | event {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (e : KEv)
      (fip : Bool) (ev : Fl4Spec.Event) :
      JReachE3 s a σ → KEvSpec e fip ev → (ev ≠ .interrupt → σ.curThread ≠ σ.idleThread) →
      e.run st arI s a = ok (s', a') → EvOut fip ev σ σ' →
      RJM (L := L) arI AR MR s' a' σ' → JReachE3 s' a' σ'

variable {arI AR MR}

/-- Every `JReachE2` state is a `JReachE3` state. -/
theorem JReachE2.toE3 {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : JReachE2 (L := L) arI AR MR s a σ) :
    JReachE3 (L := L) arI AR MR s a σ := by
  induction h with
  | @start s a σ Z H Cs Ac Lst D J hX hR => exact JReachE3.start J hX hR
  | @step s a σ s' a' σ' n c _ hct hn hv hy hRJ ih => exact JReachE3.step n c ih hct hn hv hy hRJ
  | @irq s a a1 σ s' a' σ' w _ hI hv hO hRJ ih => exact JReachE3.irq w ih hI hv hO hRJ
  | @event s a σ s' a' σ' e fip ev _ hK hev hv hO hRJ ih => exact JReachE3.event e fip ev ih hK hev hv hO hRJ

/-- **The invariant** of `JReachE3`: `JAtZ` at some ghosts, `SInvX`, `MR`. -/
theorem jreach_invE3 (hnd : Fl4Spec.numDomains = 1) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : JReachE3 (L := L) arI AR MR s a σ) :
    (∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) ∧ SInvX σ ∧ MR a σ.machineState := by
  induction h with
  | @start s a σ Z H Cs Ac Lst D J hX hR => exact ⟨⟨_, _, _, _, _, _, J⟩, hX, hR⟩
  | @step s a σ s' a' σ' n c _ hct _ _ hy hRJ ih => exact ⟨hRJ.1.2, kentry_sinvX hnd c ih.2.1 hct _ hy, hRJ.2⟩
  | @irq s a a1 σ s' a' σ' w _ _ _ hO hRJ ih =>
    exact ⟨hRJ.1.2, kcall_sinvX hnd true .interrupt ih.2.1 (fun h => absurd rfl h) _ hO, hRJ.2⟩
  | @user s a σ s' a' σ' n c _ hct _ _ hO hRJ ih =>
    exact ⟨hRJ.1.2, sinvX_evOut hnd ih.2.1 (fun _ => hct) (fun h => by cases h) hO, hRJ.2⟩
  | @vmf s a σ s' a' σ' ad c ft _ hct _ _ hO hRJ ih =>
    exact ⟨hRJ.1.2, sinvX_evOut hnd ih.2.1 (fun _ => hct) (fun h => by cases h) hO, hRJ.2⟩
  | @event s a σ s' a' σ' e fip ev _ _ hev _ hO hRJ ih =>
    exact ⟨hRJ.1.2, sinvX_evOut hnd ih.2.1 hev (fun _ => sinvX_fip ih.2.1) hO, hRJ.2⟩

set_option maxHeartbeats 8000000 in
/-- **Refinement at every reachable state** (module docstring): as
`kernel_entry_reachE2`, but the user-exception and VM-fault entries from a
non-idle thread take only their hardware facts `UserHw` / `VmfHw` [P] and
the finish bundle (no `JFltHyp`, no `JEvRef`). -/
theorem kernel_entry_reachE3 [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInVal arI)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachE3 (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ SInvX σ ∧ MR a σ.machineState ∧
      (∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c →
        (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
          ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            KDispHypsKV35 (L := L) arI AR MR (Z.mv Z.G V') H Cs D' s' a' σb n c) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            JDispMRI (L := L) arI AR MR s' a' σb n c) →
        (∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
          (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
            JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
            KFinAtR31 (L := L) arI AR Z' H' Cs' s' a' x.2) →
        (n = fl4_abi.syscall.SysReplyRecv →
          FastRR (L := L) (arI := arI) s a n (fun r => KPostMS (L := L) arI AR MR c σ r)) →
        syscall.handle_syscall st arI s a n ⦃ r =>
          ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
            RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
            JReachE3 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (w : U64) (a1 : A), σ.curThread ≠ σ.idleThread → IrqHw AR MR a a1 σ w →
        KFinEv (L := L) arI AR .interrupt (KFrontI (st := st) arI s a1 w) σ →
        syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∃ σ', EvOut false .interrupt σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          JReachE3 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
        KFinEv (L := L) arI AR (.userLevelFault n.bv c.bv) (KFrontF2 (st := st) arI (brU (st := st) arI n c) s a) σ →
        syscall.handle_user_exception st arI s a n c ⦃ r => ∃ σ', EvOut false (.userLevelFault n.bv c.bv) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          JReachE3 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (ad c : U64) (ft : Fl4Spec.VMFaultType), σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
        KFinEv (L := L) arI AR (.vmFaultEvent ft) (KFrontF2 (st := st) arI (brV (st := st) arI ad c) s a) σ →
        syscall.handle_vm_fault st arI s a ad c ⦃ r => ∃ σ', EvOut false (.vmFaultEvent ft) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          JReachE3 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (e : KEv) (fip : Bool) (ev : Fl4Spec.Event), KEvSpec e fip ev →
        (ev ≠ .interrupt → σ.curThread ≠ σ.idleThread) →
        JEvRef (L := L) arI AR MR e fip ev s a σ →
        e.run st arI s a ⦃ r => ∃ σ', EvOut fip ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          JReachE3 (L := L) arI AR MR r.1 r.2 σ' ⦄) := by
  obtain ⟨⟨Z, H, Cs, Ac, Lst, D, J⟩, hX, hR⟩ := jreach_invE3 hnd hJ
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, hR, fun n c hct hn hflag hK hDM hFin hFast => ?_,
    fun w a1 hct hI hFin => ?_, fun n c hct hU hFin => ?_, fun ad c ft hct hV hFin => ?_,
    fun e fip ev hK hev hE => ?_⟩
  · have hE := kernel_entryJ37N (MR := MR) s a σ J hct hR hX n c hn hflag hK hDM hFin hARI hA hnd hM hKD hPA hIA
      hmrt hmb hT hmax htu hRef hPI hFast
    obtain ⟨⟨s', a'⟩, hv, σ', hy, hRJ, hM', hX'⟩ := spec_exists hE
    rw [hv, WP.spec_ok]
    exact ⟨σ', hy, hRJ, hX', hM', JReachE3.step n c hJ hct hn hv hy ⟨hRJ, hM'⟩⟩
  · have hE := jEvRef_irq J hX hct hI hFin hARI hA hnd hM hKD hIA hmrt hmb hT hmax htu
    obtain ⟨⟨s', a'⟩, hv, σ', hO, hRJM⟩ := spec_exists hE
    rw [hv, WP.spec_ok]
    exact ⟨σ', hO, hRJM.1, kcall_sinvX hnd true .interrupt hX (fun h => absurd rfl h) _ hO, hRJM.2,
      JReachE3.irq w hJ hI hv hO hRJM⟩
  · have hE := jEvRef_user n c J hX hct hR (jFltHyp_user hnd hM hKD hA hX hct n c hU) hFin hARI hA hnd hM hKD hmrt
      hmb hT hmax htu
    obtain ⟨⟨s', a'⟩, hv, σ', hO, hRJM⟩ := spec_exists hE
    rw [show syscall.handle_user_exception st arI s a n c = (KEv.user n c).run st arI s a from rfl, hv, WP.spec_ok]
    exact ⟨σ', hO, hRJM.1, sinvX_evOut hnd hX (fun _ => hct) (fun h => by cases h) hO, hRJM.2,
      JReachE3.user n c hJ hct hU hv hO hRJM⟩
  · have hE := jEvRef_vmf ad c ft J hX hct hR (jFltHyp_vmf hnd hM hKD hA hX hct ad c ft hV) hFin hARI hA hnd hM hKD
      hmrt hmb hT hmax htu
    obtain ⟨⟨s', a'⟩, hv, σ', hO, hRJM⟩ := spec_exists hE
    rw [show syscall.handle_vm_fault st arI s a ad c = (KEv.vmf ad c).run st arI s a from rfl, hv, WP.spec_ok]
    exact ⟨σ', hO, hRJM.1, sinvX_evOut hnd hX (fun _ => hct) (fun h => by cases h) hO, hRJM.2,
      JReachE3.vmf ad c ft hJ hct hV hv hO hRJM⟩
  · obtain ⟨⟨s', a'⟩, hv, σ', hO, hRJM⟩ := spec_exists hE
    rw [hv, WP.spec_ok]
    exact ⟨σ', hO, hRJM.1, sinvX_evOut hnd hX hev (fun _ => sinvX_fip hX) hO, hRJM.2,
      JReachE3.event e fip ev hJ hK hev hv hO hRJM⟩

end

end

end Fl4Proofs.P3
