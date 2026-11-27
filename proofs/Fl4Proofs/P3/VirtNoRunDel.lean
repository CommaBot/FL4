/-
P3x for virtualization (line virt, gen 18, item 2, first part): **the NV-free step transport, deletion and the
TCB / CNode invocations — F = V on every `NoRunVM` state, VCPUs and virtualization caps allowed.**

Gen 13 (P3/VirtF13) moved the top onto FL4's step by proving each `…VF` op equal to the *ported* op on `NR = NV ∧
NoRunVM` states; its deletion chain carries `NV` (no virtualization cap, no VCPU) as the frame of `lfp_agree`.
Beyond `NR` the ported op is the wrong target: the comparison is `…VF` against `…V` (both extended), whose only
difference in deletion is `finaliseCapVF` vs `finaliseCapV` (equal on `NoRunVM` states, gen 17's
`finaliseCapVF_eq_nr`). So the frame of `lfp_agree` is `NoRunVM` (= invA's `NativeScopeS`, `noRunVM_iff`) alone,
kept by the `V` ops:

* `NoRunVM` frames of the extended ops (the `ns_*` family, `ns_auto`): `ns_getEpt`, `ns_storeGuestEntry`,
  `ns_findGuestRoot`, `ns_guestLookupSlot`, `ns_guestUnmap`, `ns_getVcpu`, `ns_setVcpu`, `ns_vcpuUpdate`,
  `ns_vcpuDetach` (gen 15's `noRunVM_vcpuDetach`), `ns_ioPortRevoke`, **`ns_finaliseCapV`**, `ns_recDelFV`,
  **`ns_recDelV`**, `ns_capDeleteV`, `ns_capRevokeFV`, **`ns_capRevokeV`**, `ns_invokeCnodeV`, `ns_installTcbCapV`,
  `ns_installTcbFrameCapV`, `ns_invokeTcbV`, `ns_invokeSetEptRoot`.
* F = V (every `NoRunVM` state; no `NV`, no `hvk`): `recDel_agreeVF`, **`recDelVF_eq_nr`**, **`capDeleteVF_eq_nr`**,
  `capRevoke_agreeVF`, **`capRevokeVF_eq_nr`**, **`invokeCnodeVF_eq_nr`**, `installTcbCapVF_eq_nr`,
  `installTcbFrameCapVF_eq_nr`, **`invokeTcbVF_eq_nr`** (no `TcbCapsOK`: both sides are extended),
  **`invokeSetEptRootF_eq_nr`**.

No named premise; no [J]/[P]/[W]/[S]. New file only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtFinNR
open Classical

namespace Fl4Proofs.P3.VirtNoRunDel
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.VirtR7b Fl4Proofs.P3.VirtR7d Fl4Proofs.P3.VirtReportEq
  Fl4Proofs.P3.VirtNoRunF Fl4Proofs.P3.VirtFinNR

noncomputable section

set_option maxHeartbeats 1000000

/-! ## `NoRunVM` frames of the extended ops -/

theorem ns_getEpt (p : ObjRef) : SInv.NSK (getEpt (Z := Unit) p) := by
  unfold getEpt; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getEpt _)

theorem ns_storeGuestEntry (p : ObjRef) (i : BitVec 9) (e : Word) : SInv.NSK (storeGuestEntry (Z := Unit) p i e) := by
  unfold storeGuestEntry; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_storeGuestEntry _ _ _)

theorem ns_findGuestRoot (asid : Asid) : SInv.NSKE (findGuestRoot (Z := Unit) asid) := by
  unfold findGuestRoot; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_findGuestRoot _)

theorem ns_guestLookupSlot (root : ObjRef) (gpa : Word) (level : Nat) :
    SInv.NSKE (guestLookupSlot (Z := Unit) root gpa level) := by
  unfold guestLookupSlot
  generalize ([39, 30, 21] : List Nat) = l
  induction l generalizing root with
  | nil => unfold guestLookupSlot.go; exact ike_returnOk _
  | cons s rest ih =>
    unfold guestLookupSlot.go
    split
    · refine ike_bind (ike_liftE (ns_getEpt _)) fun p => ?_
      obtain ⟨_, es⟩ := p
      dsimp only
      split
      · exact ike_throw _
      · exact ih _
    · exact ike_returnOk _
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_guestLookupSlot _ _ _)

theorem ns_guestUnmap (asid : Asid) (gpa : Word) (ptr : ObjRef) (level : Nat) (table : Bool) :
    SInv.NSK (guestUnmap (Z := Unit) asid gpa ptr level table) := by
  unfold guestUnmap; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_guestUnmap _ _ _ _ _)

theorem ns_getVcpu (v : ObjRef) : SInv.NSK (getVcpu (Z := Unit) v) := by
  unfold getVcpu; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getVcpu _)

theorem ns_setVcpu (v : ObjRef) (st : VcpuState) : SInv.NSK (setVcpu (Z := Unit) v st) :=
  fun _ hn _ hx => noRunVM_setVcpu hn hx
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setVcpu _ _)

theorem ns_vcpuUpdate (v : ObjRef) (f : VcpuState → VcpuState) : SInv.NSK (vcpuUpdate (Z := Unit) v f) :=
  fun _ hn _ hx => noRunVM_vcpuUpdate hn hx
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_vcpuUpdate _ _)

theorem ns_vcpuDetach (t : ObjRef) : SInv.NSK (vcpuDetach (Z := Unit) t) :=
  fun _ hn _ hx => noRunVM_vcpuDetach hn hx
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_vcpuDetach _)

theorem ns_ioPortRevoke (c : ArchCap) : SInv.NSK (ioPortRevoke (Z := Unit) c) := by
  unfold ioPortRevoke; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_ioPortRevoke _)

/-- **`finaliseCapV` keeps `NoRunVM`** (arm by arm). -/
theorem ns_finaliseCapV (c : Cap) (fin : Bool) : SInv.NSK (finaliseCapV (Z := Unit) c fin) := by
  cases c with
  | threadCap t => unfold finaliseCapV; dsimp only; ns_auto
  | archObjectCap a =>
    cases a with
    | vcpuCap v => unfold finaliseCapV; dsimp only; ns_auto
    | eptCap r l m =>
      rcases m with _ | ⟨a, g⟩
      · exact ns_finaliseCap _ _
      · unfold finaliseCapV; dsimp only; ns_auto
    | pageCap d r ri mt sz m =>
      rcases m with _ | ⟨a, g⟩
      · cases mt <;> exact ns_finaliseCap _ _
      · cases mt with
        | vmEptMap => unfold finaliseCapV; dsimp only; ns_auto
        | _ => exact ns_finaliseCap _ _
    | ioPortCap f l => unfold finaliseCapV; dsimp only; ns_auto
    | _ => exact ns_finaliseCap _ _
  | _ => exact ns_finaliseCap _ _
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_finaliseCapV _ _)

theorem ns_recDelFV {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, SInv.NSK (f k)) (k : RecDelCall) : SInv.NSKE (recDelFV (Z := Unit) f k) := by
  have hrec' : ∀ k, SInv.NSKE (ε := Unit) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall sl e => unfold recDelFV withoutPreemption; ns_auto; all_goals exact hrec' _
  | finaliseSlotCall sl e => unfold recDelFV withoutPreemption; ns_auto; all_goals exact hrec' _
  | reduceZombieCall c sl e =>
    unfold recDelFV withoutPreemption
    split <;> ns_auto
    all_goals exact hrec' _

/-- **The extended `rec_del` keeps `NoRunVM`**. -/
theorem ns_recDelV (c : RecDelCall) : SInv.NSKE (recDelV (Z := Unit) c) := by
  unfold recDelV
  exact ik_lfp (fun f hf k => ns_recDelFV hf k) c
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_recDelV _)

theorem ns_capDeleteV (slot : CslotPtr) : SInv.NSKE (capDeleteV (Z := Unit) slot) := by
  unfold capDeleteV; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_capDeleteV _)

theorem ns_capRevokeFV {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, SInv.NSK (f k)) (sl : CslotPtr) : SInv.NSKE (capRevokeFV (Z := Unit) f sl) := by
  have hrec' : ∀ k, SInv.NSKE (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeFV withoutPreemption selectExt
  ns_auto
  all_goals exact hrec' _

/-- **The extended `cap_revoke` keeps `NoRunVM`**. -/
theorem ns_capRevokeV (sl : CslotPtr) : SInv.NSKE (capRevokeV (Z := Unit) sl) := by
  unfold capRevokeV
  exact ik_lfp (fun f hf k => ns_capRevokeFV hf k) sl
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_capRevokeV _)

theorem ns_invokeCnodeV (i : CnodeInvocation) : SInv.NSKE (invokeCnodeV (Z := Unit) i) := by
  cases i with
  | revokeCall sl => exact ns_capRevokeV sl
  | deleteCall sl => exact ns_capDeleteV sl
  | _ => exact ns_invokeCnode _
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_invokeCnodeV _)

theorem ns_installTcbCapV (target : ObjRef) (slot : CslotPtr) (n : Nat) (so : Option (Cap × CslotPtr)) :
    SInv.NSKE (installTcbCapV (Z := Unit) target slot n so) := by
  unfold installTcbCapV; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_installTcbCapV _ _ _ _)

theorem ns_installTcbFrameCapV (target : ObjRef) (slot : CslotPtr)
    (buffer : Option (VSpaceRef × Option (Cap × CslotPtr))) :
    SInv.NSKE (installTcbFrameCapV (Z := Unit) target slot buffer) := by
  unfold installTcbFrameCapV; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_installTcbFrameCapV _ _ _)

theorem ns_invokeTcbV (i : TcbInvocation) : SInv.NSKE (invokeTcbV (Z := Unit) i) := by
  cases i with
  | threadControlCaps target slot fh th cr vr buf => unfold invokeTcbV; ns_auto
  | threadControlSched target slot fh mcp prio sc => unfold invokeTcbV; ns_auto
  | _ => exact ns_invokeTcb _
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_invokeTcbV _)

theorem ns_invokeSetEptRoot (i : SetEptRootInvocation) : SInv.NSKE (invokeSetEptRoot (Z := Unit) i) := by
  unfold invokeSetEptRoot; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_invokeSetEptRoot _)

/-! ## Deletion: F = V on `NoRunVM` states -/

theorem ns_setCapE (c : Cap) (sl : CslotPtr) : SInv.NSKE (withoutPreemption (setCap (Z := Unit) c sl)) := by
  unfold withoutPreemption; ns_auto

/-- One step of the extended `rec_del` and of FL4's agree from a `NoRunVM` state. -/
theorem recDel_agreeVF (f g : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap)))
    (hpf : ∀ i, Pres NativeScopeS (f i)) (hfg : ∀ i s, NativeScopeS s → f i s = g i s) (k : RecDelCall)
    (s : State Unit) (hs : NativeScopeS s) : recDelFV (Z := Unit) f k s = recDelFVF (Z := Unit) g k s := by
  show ExceptT.run (recDelFV (Z := Unit) f k) s = ExceptT.run (recDelFVF (Z := Unit) g k) s
  cases k with
  | cTEDeleteCall sl e =>
    unfold recDelFV recDelFVF
    exact nde_bind_congr (hfg _ s hs) fun _ _ _ => rfl
  | finaliseSlotCall sl e =>
    obtain ⟨o, r⟩ := sl
    unfold recDelFV recDelFVF
    refine nde_bind_congr rfl fun cap t hmem => ?_
    obtain ⟨rfl, -⟩ := SInvV.vih_mem_getCap (mem_run_liftE' hmem)
    by_cases hn : cap = .nullCap
    · rw [if_pos hn, if_pos hn]
    rw [if_neg hn, if_neg hn]
    refine nde_bind_congr rfl fun fin t2 hmem2 => ?_
    have ht2 : t2 = t := by
      have h := mem_run_liftE' hmem2
      exact (Prod.mk.inj (Set.mem_singleton_iff.1 (h : (fin, t2) ∈ ({(decide (isFinalCap' cap t), t)} : Set _)))).2
    subst ht2
    refine nde_bind_congr (run_liftE_congr (finaliseCapVF_eq_nr hs cap fin).symm) fun p t3 hmem3 => ?_
    have hI3 : NativeScopeS t3 := ns_finaliseCapV cap fin t2 hs _ (mem_run_liftE' hmem3)
    obtain ⟨rem, ci⟩ := p
    dsimp only
    by_cases h1 : capRemoveable rem (o, r)
    · rw [if_pos h1, if_pos h1]
    rw [if_neg h1, if_neg h1]
    by_cases h2 : capCyclicZombie rem (o, r) ∧ ¬ e = true
    · rw [if_pos h2, if_pos h2]
    rw [if_neg h2, if_neg h2]
    refine nde_bind_congr rfl fun _ t4 hmem4 => ?_
    have hI4 : NativeScopeS t4 := ns_setCapE rem (o, r) t3 hI3 _ hmem4
    refine nde_bind_congr (hfg _ t4 hI4) fun _ t5 hmem5 => ?_
    have hI5 : NativeScopeS t5 := hpf _ t4 hI4 _ hmem5
    refine nde_bind_congr rfl fun _ t6 hmem6 => ?_
    have hI6 : NativeScopeS t6 := ns_preemptionPoint t5 hI5 _ hmem6
    exact hfg _ t6 hI6
  | reduceZombieCall c sl e =>
    cases c with
    | zombie ptr bits n =>
      cases n with
      | zero => rfl
      | succ n =>
        cases e with
        | false => rfl
        | true =>
          unfold recDelFV recDelFVF
          refine nde_bind_congr rfl fun _ t1 hmem1 => ?_
          have ht1 : t1 = s := (Prod.mk.inj (Set.mem_singleton_iff.1 hmem1)).2
          subst ht1
          exact nde_bind_congr (hfg _ t1 hs) fun _ _ _ => rfl
    | _ => rfl

/-- **FL4's `rec_del` is the extended one on `NoRunVM` states** (no `NV`). -/
theorem recDelVF_eq_nr (k : RecDelCall) {s : State Unit} (hs : NoRunVM s) :
    recDelVF (Z := Unit) k s = recDelV k s := by
  unfold recDelVF recDelV
  exact lfp_agree NativeScopeS _ _ recDelFV_mono VirtF13.recDelFVF_mono (fun k => ns_recDelV k)
    (fun f g hf _ hfg k s hs => recDel_agreeVF f g hf hfg k s hs) k s hs

theorem capDeleteVF_eq_nr (sl : CslotPtr) {s : State Unit} (hs : NoRunVM s) :
    capDeleteVF (Z := Unit) sl s = capDeleteV sl s := by
  show ExceptT.run (capDeleteVF (Z := Unit) sl) s = ExceptT.run (capDeleteV (Z := Unit) sl) s
  unfold capDeleteVF capDeleteV
  exact nde_bind_congr (recDelVF_eq_nr _ hs) fun _ _ _ => rfl

theorem capRevoke_agreeVF (f g : CslotPtr → NonDet (State Unit) (Except Unit Unit))
    (_hpf : ∀ i, Pres NativeScopeS (f i)) (hfg : ∀ i s, NativeScopeS s → f i s = g i s) (sl : CslotPtr)
    (s : State Unit) (hs : NativeScopeS s) : capRevokeFV (Z := Unit) f sl s = capRevokeFVF (Z := Unit) g sl s := by
  show ExceptT.run (capRevokeFV (Z := Unit) f sl) s = ExceptT.run (capRevokeFVF (Z := Unit) g sl) s
  unfold capRevokeFV capRevokeFVF withoutPreemption
  refine nde_bind_congr rfl fun cap t1 hmem1 => ?_
  have hI1 : NativeScopeS t1 := ike_liftE (ns_getCap _) s hs _ hmem1
  refine nde_bind_congr rfl fun cdt t2 hmem2 => ?_
  have hI2 : NativeScopeS t2 := ike_liftE (ik_gets _) t1 hI1 _ hmem2
  refine nde_bind_congr rfl fun d t3 hmem3 => ?_
  have hI3 : NativeScopeS t3 := ike_returnOk _ t2 hI2 _ hmem3
  unfold NonDetE.whenE
  by_cases hc : cap ≠ .nullCap ∧ d ≠ ∅
  · rw [if_pos hc, if_pos hc]
    refine nde_bind_congr rfl fun child t4 hmem4 => ?_
    have hI4 : NativeScopeS t4 := ike_liftE (ns_selectExt _ _) t3 hI3 _ hmem4
    refine nde_bind_congr rfl fun cap' t5 hmem5 => ?_
    have hI5 : NativeScopeS t5 := ike_liftE (ns_getCap _) t4 hI4 _ hmem5
    refine nde_bind_congr rfl fun _ t6 hmem6 => ?_
    have hI6 : NativeScopeS t6 := ike_assertE _ t5 hI5 _ hmem6
    refine nde_bind_congr (capDeleteV_eq_sym child hI6) fun _ t7 hmem7 => ?_
    have hI7 : NativeScopeS t7 := ns_capDeleteV child t6 hI6 _ hmem7
    refine nde_bind_congr rfl fun _ t8 hmem8 => ?_
    have hI8 : NativeScopeS t8 := ns_preemptionPoint t7 hI7 _ hmem8
    exact hfg _ t8 hI8
  · rw [if_neg hc, if_neg hc]
where
  capDeleteV_eq_sym (child : CslotPtr) {t : State Unit} (h : NativeScopeS t) :
      ExceptT.run (capDeleteV (Z := Unit) child) t = ExceptT.run (capDeleteVF (Z := Unit) child) t :=
    (capDeleteVF_eq_nr child h).symm

/-- **FL4's `cap_revoke` is the extended one on `NoRunVM` states** (no `NV`). -/
theorem capRevokeVF_eq_nr (sl : CslotPtr) {s : State Unit} (hs : NoRunVM s) :
    capRevokeVF (Z := Unit) sl s = capRevokeV sl s := by
  unfold capRevokeVF capRevokeV
  exact lfp_agree NativeScopeS _ _ capRevokeFV_mono VirtF13.capRevokeFVF_mono (fun k => ns_capRevokeV k)
    (fun f g hf _ hfg k s hs => capRevoke_agreeVF f g hf hfg k s hs) sl s hs

/-! ## CNode, TCB and SetEPTRoot invocations -/

theorem invokeCnodeVF_eq_nr (i : CnodeInvocation) {s : State Unit} (hs : NoRunVM s) :
    invokeCnodeVF (Z := Unit) i s = invokeCnodeV i s := by
  cases i with
  | revokeCall sl => exact capRevokeVF_eq_nr sl hs
  | deleteCall sl => exact capDeleteVF_eq_nr sl hs
  | _ => rfl

theorem installTcbCapVF_eq_nr (target : ObjRef) (slot : CslotPtr) (n : Nat) (so : Option (Cap × CslotPtr))
    {s : State Unit} (hs : NoRunVM s) :
    installTcbCapVF (Z := Unit) target slot n so s = installTcbCapV target slot n so s := by
  cases so with
  | none => rfl
  | some p =>
    obtain ⟨c, src⟩ := p
    show ExceptT.run (installTcbCapVF (Z := Unit) target slot n (some (c, src))) s =
      ExceptT.run (installTcbCapV (Z := Unit) target slot n (some (c, src))) s
    unfold installTcbCapVF installTcbCapV
    exact nde_bind_congr (capDeleteVF_eq_nr _ hs) fun _ _ _ => rfl

theorem installTcbFrameCapVF_eq_nr (target : ObjRef) (slot : CslotPtr)
    (buffer : Option (VSpaceRef × Option (Cap × CslotPtr))) {s : State Unit} (hs : NoRunVM s) :
    installTcbFrameCapVF (Z := Unit) target slot buffer s = installTcbFrameCapV target slot buffer s := by
  cases buffer with
  | none => rfl
  | some p =>
    obtain ⟨ptr, frame⟩ := p
    show ExceptT.run (installTcbFrameCapVF (Z := Unit) target slot (some (ptr, frame))) s =
      ExceptT.run (installTcbFrameCapV (Z := Unit) target slot (some (ptr, frame))) s
    unfold installTcbFrameCapVF installTcbFrameCapV
    exact nde_bind_congr (capDeleteVF_eq_nr _ hs) fun _ _ _ => rfl

/-- An outcome of FL4's install from a `NoRunVM` state is one of the extended install. -/
theorem toV {target : ObjRef} {slot : CslotPtr} {n : Nat} {o : Option (Cap × CslotPtr)} {s : State Unit}
    (hs : NoRunVM s) {x : Except Unit Unit × State Unit}
    (m : x ∈ (ExceptT.run (installTcbCapVF (Z := Unit) target slot n o) s).1) :
    x ∈ (ExceptT.run (installTcbCapV (Z := Unit) target slot n o) s).1 := by
  change x ∈ (installTcbCapVF (Z := Unit) target slot n o s).1 at m
  rw [installTcbCapVF_eq_nr target slot n o hs] at m
  exact m

/-- **The TCB invocations, F = V on `NoRunVM` states** (no `NV`, no `TcbCapsOK`). -/
theorem invokeTcbVF_eq_nr (i : TcbInvocation) {s : State Unit} (hs : NoRunVM s) :
    invokeTcbVF (Z := Unit) i s = invokeTcbV i s := by
  cases i with
  | threadControlCaps target slot fh th cr vr buf =>
    show ExceptT.run (invokeTcbVF (Z := Unit) (.threadControlCaps target slot fh th cr vr buf)) s =
      ExceptT.run (invokeTcbV (Z := Unit) (.threadControlCaps target slot fh th cr vr buf)) s
    unfold invokeTcbVF invokeTcbV
    refine nde_bind_congr (installTcbCapVF_eq_nr _ _ _ _ hs) fun _ t1 m1 => ?_
    have n1 : NoRunVM t1 := ns_installTcbCapV target slot 3 fh s hs _ (toV hs m1)
    refine nde_bind_congr (installTcbCapVF_eq_nr _ _ _ _ n1) fun _ t2 m2 => ?_
    have n2 : NoRunVM t2 := ns_installTcbCapV target slot 4 th t1 n1 _ (toV n1 m2)
    refine nde_bind_congr (installTcbCapVF_eq_nr _ _ _ _ n2) fun _ t3 m3 => ?_
    have n3 : NoRunVM t3 := ns_installTcbCapV target slot 0 cr t2 n2 _ (toV n2 m3)
    refine nde_bind_congr (installTcbCapVF_eq_nr _ _ _ _ n3) fun _ t4 m4 => ?_
    have n4 : NoRunVM t4 := ns_installTcbCapV target slot 1 vr t3 n3 _ (toV n3 m4)
    exact nde_bind_congr (installTcbFrameCapVF_eq_nr _ _ _ n4) fun _ _ _ => rfl
  | threadControlSched target slot fh mcp prio sc =>
    show ExceptT.run (invokeTcbVF (Z := Unit) (.threadControlSched target slot fh mcp prio sc)) s =
      ExceptT.run (invokeTcbV (Z := Unit) (.threadControlSched target slot fh mcp prio sc)) s
    unfold invokeTcbVF invokeTcbV
    exact nde_bind_congr (installTcbCapVF_eq_nr _ _ _ _ hs) fun _ _ _ => rfl
  | _ => rfl

/-- **TCBSetEPTRoot, F = V on `NoRunVM` states**. -/
theorem invokeSetEptRootF_eq_nr (i : SetEptRootInvocation) {s : State Unit} (hs : NoRunVM s) :
    invokeSetEptRootF (Z := Unit) i s = invokeSetEptRoot i s := by
  show ExceptT.run (invokeSetEptRootF (Z := Unit) i) s = ExceptT.run (invokeSetEptRoot (Z := Unit) i) s
  unfold invokeSetEptRootF invokeSetEptRoot
  exact nde_bind_congr (capDeleteVF_eq_nr _ hs) fun _ _ _ => rfl

end
end Fl4Proofs.P3.VirtNoRunDel
