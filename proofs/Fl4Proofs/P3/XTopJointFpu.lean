/-
P3 (DESIGN.md §9), TCB: **the FPU release at `J`** (`JAtZ.fpuReleaseJ`;
the last step of a final thread cap's finalisation, XTopJointFinThread's
`JAtZ.finThreadJ`, in place of a whole-step premise).

FL4's `fpu_release` (the extracted `finalise_cap_object`, Thread case:
`machineArchInst.fpu_release a4 ptr`) changes only the arch state `A`: the
store is not touched (the eager FPU switching and the remote FPU flush of
the arch backend live behind `machine.Arch`). The spec's `fpu_release`
(l4v `FPU_A.fpu_release`) changes, when the thread owns the FPU, the
thread's saved FPU image and `tcbCurFpu` (its registers kept), the current
FPU owner and the machine state (not the user memory); else nothing. No
relation of `JAtZ` reads those, so:

* `fpuRelease_outF`: an outcome of the spec's `fpu_release` of a TCB, in the
  normal form `{updK σ t (.tcb {x with tcbArch := ta}) with machineState :=
  ms, archState := {σ.archState with x64CurrentFpuOwner := o}}`, the
  registers (`ta`) and the user memory (`ms`) kept.
* `Ipc.irel_tcbArch`: `IRel` across a spec-only change of a TCB's
  `tcbArch` keeping its registers (`reg_wr_irel` without FL4's write).
* `JAtZ.tcbArchJ`: `JAtZ` across that change (XTopJointRegFrame's
  `JAtZ.reg_frame`, FL4's store kept: a quiet step `QKY`, an `ArchStep`).
* `JAtZ.arFrS`: `JAtZ` across a spec step in XTopJointFinVsSpec's frame
  `ArFr` with FL4's store kept and any arch state related by `XTopAt` after
  (as XTopJointFinVs's `finVsJb` with no word written).
* `XTopAt.fpuOwner`: `XTopAt` across the FPU owner's and the machine
  state's change (`XTopAt.frameStep`, the user memory kept), at an arch
  state related to the same CR3.
* `JAtZ.fpuReleaseJ`: FL4's `fpu_release` against the spec's at `J`, from
  `ARKeep.fpu_release` [P] (part of `ARIface`, already a top-level premise:
  `JDelParts.arKeep`).
-/
import Fl4Proofs.P3.XTopJointFinVs
import Fl4Proofs.P3.XTopJointYield
import Fl4Proofs.P3.SpecFinOutTcb
import Fl4Proofs.P3.IpcSuspend
open Aeneas Aeneas.Std Result

/-! ## The spec's `fpu_release`: an outcome in normal form -/

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp

noncomputable section

section Spec
open Fl4Spec Classical

/-- `fpuOp_ex` with the user memory kept. -/
theorem fpuOp_exU (f : MachineRestMonad Unit) (b : Bool) (σ : State Unit) :
    ∃ ms', ms'.underlyingMemory = σ.machineState.underlyingMemory ∧
      ((), { σ with machineState := ms' }) ∈
        (doMachineOp (Z := Unit) (machineOpLift f >>= fun _ =>
          NonDet.modify fun s : MachineState => { s with fpuEnabled := b }) σ).1 ∧ ms'.fpuEnabled = b := by
  obtain ⟨mr', h⟩ := ign_ex f σ.machineState.machineStateRest
  have hm1 : ((), { σ.machineState with machineStateRest := mr' }) ∈ (machineOpLift f σ.machineState).1 := by
    unfold machineOpLift machineRestLift
    refine mem_bind_nd (x := (σ.machineState.machineStateRest, σ.machineState)) rfl ?_
    refine mem_bind_nd (x := (((), mr'), σ.machineState)) ⟨h, rfl⟩ ?_
    refine mem_bind_nd (x := ((), { σ.machineState with machineStateRest := mr' })) (by rfl) ?_
    rfl
  exact ⟨{ { σ.machineState with machineStateRest := mr' } with fpuEnabled := b }, rfl,
    dmo_ex _ σ (mem_bind_nd hm1 (Set.mem_singleton _)), rfl⟩

/-- `readFpu_ex` with the user memory kept. -/
theorem readFpu_exU (m : MachineState) (h : m.fpuEnabled = true) :
    ∃ v m', m'.underlyingMemory = m.underlyingMemory ∧ (v, m') ∈ (readFpuState m).1 := by
  refine ⟨readFpuStateVal m.machineStateRest, { m with machineStateRest := m.machineStateRest }, rfl, ?_⟩
  unfold readFpuState machineRestLift
  refine mem_bind_nd (x := ((), m)) (by simp [NonDet.stateAssert, NonDet.assert, h]) ?_
  refine mem_bind_nd (x := (m.machineStateRest, m)) rfl ?_
  refine mem_bind_nd (x := ((readFpuStateVal m.machineStateRest, m.machineStateRest), m)) ⟨rfl, rfl⟩ ?_
  refine mem_bind_nd (x := ((), { m with machineStateRest := m.machineStateRest })) (Set.mem_singleton _) ?_
  exact Set.mem_singleton _

/-- **An outcome of the spec's `fpu_release` of a TCB** (module docstring):
the TCB's arch part changed with its registers kept, the machine state
changed with the user memory kept, the FPU owner changed; nothing else. -/
theorem fpuRelease_outF {σ : State Unit} {t : ObjRef} {x : Tcb} (hkt : σ.kheap t = some (.tcb x)) :
    ∃ (ta : ArchTcb) (ms : MachineState) (o : Option ObjRef),
      ta.tcbContext.userRegs = x.tcbArch.tcbContext.userRegs ∧
      ms.underlyingMemory = σ.machineState.underlyingMemory ∧
      ((), { updK σ t (.tcb { x with tcbArch := ta }) with
        machineState := ms, archState := { σ.archState with x64CurrentFpuOwner := o } }) ∈
        (fpuRelease (Z := Unit) t σ).1 := by
  unfold fpuRelease
  rw [Notif.nd_gets_bind]
  unfold NonDet.when
  split_ifs with ho
  · unfold switchLocalFpuOwner
    rw [Notif.nd_gets_bind, ho]
    obtain ⟨ms1, hu1, hm1, he1⟩ := fpuOp_exU enableFpuImpl true σ
    obtain ⟨v, ms2, hu2, hv⟩ := readFpu_exU ms1 he1
    have hkt2 : ({ { σ with machineState := ms1 } with machineState := ms2 } : State Unit).kheap t = some (.tcb x) :=
      hkt
    obtain ⟨uc0, huc0⟩ : ∃ uc0 : UserContext, uc0 = ⟨v, (archTcbContextGet x.tcbArch).userRegs⟩ := ⟨_, rfl⟩
    have hsv := asUser_one hkt2 (setFPUState v) (a := ()) (uc' := uc0) (by rw [huc0]; rfl)
    obtain ⟨ms4, hu4, hm4, -⟩ := fpuOp_exU disableFpuImpl false
      (updK ({ { σ with machineState := ms1 } with machineState := ms2 } : State Unit) t
        (.tcb { x with tcbArch := archTcbContextSet uc0 x.tcbArch }))
    have hkt4 : ({ updK ({ { σ with machineState := ms1 } with machineState := ms2 } : State Unit) t
        (.tcb { x with tcbArch := archTcbContextSet uc0 x.tcbArch }) with machineState := ms4 } : State Unit).kheap t =
        some (.tcb { x with tcbArch := archTcbContextSet uc0 x.tcbArch }) := by
      simp [updK]
    refine ⟨{ archTcbContextSet uc0 x.tcbArch with tcbCurFpu := false }, ms4, none, ?_, ?_, ?_⟩
    · subst huc0; rfl
    · exact hu4.trans (hu2.trans hu1)
    have key : ∀ {S' : Set (Unit × State Unit)} {σc σd : State Unit}, ((), σc) ∈ S' → σc = σd → ((), σd) ∈ S' := by
      intro _ _ _ h e; rw [← e]; exact h
    refine key (σc := ?σc) (mem_bind_nd (y := ((), ?σc)) hm1 ?mem) ?eq
    case mem =>
      refine mem_bind_nd (x := ((), updK ({ { σ with machineState := ms1 } with machineState := ms2 } : State Unit) t
        (.tcb { x with tcbArch := archTcbContextSet uc0 x.tcbArch }))) ?_ ?_
      · show ((), _) ∈ ((doMachineOp readFpuState >>= fun fs => asUser t (setFPUState fs)) _).1
        exact mem_bind_nd (dmo_ex _ _ hv) (by rw [hsv]; exact Set.mem_singleton _)
      refine mem_bind_nd (x := ((), { updK ({ { σ with machineState := ms1 } with machineState := ms2 } : State Unit) t
        (.tcb { x with tcbArch := archTcbContextSet uc0 x.tcbArch }) with machineState := ms4 })) ?_ ?_
      · dsimp only; exact hm4
      unfold setX64CurrentFpuOwner
      beta_reduce
      rw [Notif.nd_gets_bind]
      have ho4 : ({ updK ({ { σ with machineState := ms1 } with machineState := ms2 } : State Unit) t
          (.tcb { x with tcbArch := archTcbContextSet uc0 x.tcbArch }) with machineState := ms4 } : State Unit).archState.x64CurrentFpuOwner =
          some t := ho
      rw [ho4]
      simp only [NonDet.maybeM]
      rw [nd_bind_one (archThreadSet_eq hkt4 _)]
      refine mem_bind_nd (Set.mem_singleton _) ?_
      exact Set.mem_singleton _
    case eq =>
      simp only [updK, Function.update_idem]
  · refine ⟨x.tcbArch, σ.machineState, σ.archState.x64CurrentFpuOwner, rfl, rfl, ?_⟩
    have hx : ({ x with tcbArch := x.tcbArch } : Tcb) = x := rfl
    have e : ({ updK σ t (.tcb { x with tcbArch := x.tcbArch }) with
        machineState := σ.machineState,
        archState := { σ.archState with x64CurrentFpuOwner := σ.archState.x64CurrentFpuOwner } } : State Unit) = σ := by
      rw [hx, Fl4Proofs.P3.Endp.updK_self hkt]
    rw [e]
    exact Set.mem_singleton _

end Spec

end

end Fl4Proofs.P3.Sched

/-! ## `IRel` across a TCB's arch part changed, the registers kept -/

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

set_option maxHeartbeats 8000000 in
/-- **`IRel` across a spec-only change of a TCB's arch part keeping its
registers** (`reg_wr_irel` with no FL4 write: no relation reads the FPU
image or `tcbCurFpu`). -/
theorem irel_tcbArch (hP0 : IPlaced N T E R B) {s : S} {σ : Fl4Spec.State Unit}
    (hX : IRel st th cr N T C E R B c s σ) {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb}
    (hk : σ.kheap t.bv = some (.tcb x)) (ta : Fl4Spec.ArchTcb)
    (hr : ta.tcbContext.userRegs = x.tcbArch.tcbContext.userRegs) :
    IRel st th cr N T C E R B c s (Notif.updK σ t.bv (.tcb { x with tcbArch := ta })) := by
  obtain ⟨hIR, hSRT⟩ := hX
  have hPe := hP0.e
  have hSch := hSRT.2.1
  have hS1 : EpStep σ (Notif.updK σ t.bv (.tcb { x with tcbArch := ta })) := EpStep.tcb hk x.tcbState ta
  have hW1 : P1.WritesIn st s s (EWrite T E R B) := P1.WritesIn.refl s _
  have hx := hIR.toE.at_tcb ht hk
  have hR1 : EpStateRel T E R B (L.mem s) (Notif.updK σ t.bv (.tcb { x with tcbArch := ta })) :=
    hIR.toE.upd_tcb hPe ht _ (fun _ _ _ => rfl) (Or.inr ⟨rfl, rfl⟩)
      ⟨hx.st, hx.blk, hx.send, hx.recv, hx.reply, fun r => by rw [hx.regs r]; exact (congrFun hr r).symm,
        hx.prio, hx.fault0, hx.faultT, hx.bound, hx.faultR⟩
  have hSRT' : SRT st th cr N T C E R B c (SRE st N T C E R B c) s
      (Notif.updK σ t.bv (.tcb { x with tcbArch := ta })) :=
    ⟨hSRT.1.stableE hW1 hS1, hSRT.2.1.stableE hPe hSRT.2.2 hW1 hS1, hSRT.2.2.mono rfl (SzKeep.epStep hS1)⟩
  have hNt' : Notif.NtfnStateRel N T (L.mem s) (Notif.updK σ t.bv (.tcb { x with tcbArch := ta })) := by
    refine hIR.toN.frame hSch.placed (fun _ _ _ => rfl) ⟨fun q y hq => ?_, fun q y hq => ?_⟩
    · by_cases e : q = t.bv
      · subst e; rw [hk] at hq; cases hq
      · simp only [Notif.updK, Function.update_of_ne e]; exact hq
    · by_cases e : q = t.bv
      · subst e; rw [hk] at hq; cases hq
        refine ⟨{ x with tcbArch := ta }, by simp [Notif.updK], rfl, ?_, rfl⟩
        unfold Notif.badgeOf
        rw [hr]
      · exact ⟨y, by simp only [Notif.updK, Function.update_of_ne e]; exact hq, rfl, rfl, rfl⟩
  exact ⟨IpcRel.of hNt' hR1 (sched_sc hSRT'.2.1), hSRT'⟩

end

end

end Fl4Proofs.P3.Ipc

/-! ## `JAtZ` across the FPU release -/

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 8000000 in
/-- **`JAtZ` across a spec-only change of a TCB's arch part keeping its
registers** (`JAtZ.reg_frame` with FL4's store kept). -/
theorem JAtZ.tcbArchJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (ta : Fl4Spec.ArchTcb)
    (hr : ta.tcbContext.userRegs = x.tcbArch.tcbContext.userRegs) :
    ∃ V', JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst D s a (updK σ t.bv (.tcb { x with tcbArch := ta })) := by
  have hI := J.xtop.irelK J.ks J.buf
  have hI3 := irel_tcbArch J.ip hI ht hk ta hr
  have hAS : ArchStep σ (updK σ t.bv (.tcb { x with tcbArch := ta })) := archStep_updTcb hk rfl
  have hA : QKY σ (updK σ t.bv (.tcb { x with tcbArch := ta })) := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun q => ?_⟩
    by_cases e : q = t.bv
    · subst e; exact Or.inr (Or.inl ⟨x, { x with tcbArch := ta }, hk, by simp [updK], rfl⟩)
    · exact Or.inl (by simp [updK, e])
  exact J.reg_frame hI3 (P1.WritesIn.refl s _) hA hAS.ykeep (hAS.inv J.inv) J.blk (P1.WritesIn.refl s _)

set_option maxHeartbeats 8000000 in
/-- **`JAtZ` across an `ArFr` spec step with FL4's store kept** (XTopJointFinVs's
`finVsJb` with no word written): `XTopAt` after given (at any arch state). -/
theorem JAtZ.arFrS (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {a' : A} {σ' : Fl4Spec.State Unit}
    (F : ArFr σ σ') (hX : XTopAt (L := L) AR Z s a' σ') :
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a' σ' := by
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s) := SlotsSame.refl _ _
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have k1 : ∀ t ∈ Z.T, L.mem s (mcpA t) = L.mem s (mcpA t) := fun _ _ => rfl
  have k2 : ∀ t ∈ Z.T, L.mem s (P1.yieldA t) = L.mem s (P1.yieldA t) := fun _ _ => rfl
  have kb : ∀ t ∈ Z.T, L.mem s (tIpcBufA t) = L.mem s (tIpcBufA t) := fun _ _ => rfl
  have k3 : ∀ q ∈ Z.C, L.mem s (P1.scReplyA q) = L.mem s (P1.scReplyA q) := fun _ _ => rfl
  have k4 : ∀ r ∈ Z.R, L.mem s (P1.rPrevA r) = L.mem s (P1.rPrevA r) ∧
      L.mem s (P1.rNextA r) = L.mem s (P1.rNextA r) := fun _ _ => ⟨rfl, rfl⟩
  have ck : Sched.CKeep σ σ' := ⟨fun q y n hq => ⟨y, F.sc.2 hq, rfl⟩,
    fun q x hq => ⟨x, (F.look (fun _ e => by cases e)).2 hq, rfl, rfl⟩, fun p x n hp => ⟨x, F.sc.1 hp⟩⟩
  have yk : YKeep σ σ' := ⟨fun p x hp => ⟨x, (F.look (fun _ e => by cases e)).2 hp, rfl⟩,
    fun p x n hp => ⟨x, F.sc.2 hp, rfl⟩, fun p y n hp => ⟨y, F.sc.1 hp, rfl⟩⟩
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ rfl ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s σ' :=
    ⟨Tr, Cq, hJ.same hSS (fun q y n _ hq => F.szKeep q.bv y n hq) rfl (fun _ _ => rfl)⟩
  have hkern := J.kern_keepA rfl rfl hX.fin.1.1.1 F rfl
  have hutc : ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi dev) →
      Sched.UtCapP3 (L := L) arI Z.th s σ' Z.G sl p sb fi := by
    intro sl p sb fi dev hsl hcap
    have U := J.utc sl p sb fi dev hsl hcap
    refine ⟨U.pal, U.pfit, U.fiLe, U.high, U.actZ, U.free, U.zero, U.sb4, U.nostr, U.nsFree,
      fun h0 => U.ns (by rw [F.cdt] at h0; exact h0), U.pp, ?_, U.dwReg, by rw [F.gpml4]; exact U.gReg⟩
    intro h0 hf0
    rw [F.cdt] at h0
    obtain ⟨r1, r2, r3⟩ := U.rst h0 hf0
    exact ⟨fun sl' h => r1 sl' (by rw [← F.orig]; exact h), r2, r3⟩
  have R : JRest (L := L) arI { Z with G := Z.G } H Cs Ac Lst D s σ' :=
    ⟨hCR', hRF', J.yld.frame k2 yk, J.mcp.frame k1 (fun p x hp => ⟨x, (F.look (fun _ e => by cases e)).2 hp, rfl⟩),
      J.buf.frame kb (fun p x hp => ⟨x, (F.look (fun _ e => by cases e)).2 hp, rfl⟩), hRP',
      J.apart.sc_frame rfl F.szKeep, hjpl, J.jcov, hkern, hutc, J.nsc.ar F, J.inv.ar F, CurInvW.ar J.cur F,
      J.own.ar F, J.off.ar F, J.act.ar F, J.bsa.ar F, J.isorted.ar F, J.curRun.ar F, J.blk⟩
  exact J.cs_frame (G' := Z.G) rfl hX F.kback (JCs.same J hSS F.ksz) R

/-- **`XTopAt` across the FPU owner's and the machine state's change**, the
user memory kept, at an arch state related to the same CR3
(`XTopAt.frameStep` with no word written). -/
theorem XTopAt.fpuOwner (hX : XTopAt (L := L) AR Z s a σ) {a' : A} (ms : Fl4Spec.MachineState)
    (o : Option Fl4Spec.ObjRef) (hum : ms.underlyingMemory = σ.machineState.underlyingMemory)
    (hAR : AR a' σ.archState.x64CurrentCr3) :
    XTopAt (L := L) AR Z s a' { σ with
      machineState := ms, archState := { σ.archState with x64CurrentFpuOwner := o } } := by
  have hI := hX.fin.1.1.2.2.2.1
  exact hX.frameStep (P1.WritesIn.refl s (fun _ => False)) (fun _ h => h.elim) (fun _ h => h.elim)
    (fun _ h => h.elim) id rfl rfl rfl rfl hum rfl rfl
    (hX.fin.1.1.1.spec_congr rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) ⟨hI.st, hI.node⟩
    hX.fin.1.1.2.2.2.2.1 hX.rel.2.2.2.1 hAR

/-- The FPU owner's and the machine state's change is an `ArFr` step. -/
theorem arFr_fpuOwner (σ : Fl4Spec.State Unit) (ms : Fl4Spec.MachineState) (o : Option Fl4Spec.ObjRef) :
    ArFr σ { σ with machineState := ms, archState := { σ.archState with x64CurrentFpuOwner := o } } :=
  ⟨fun _ => Or.inl rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 8000000 in
/-- **FL4's `fpu_release` at `J`** (module docstring): against an outcome of
the spec's, `JAtZ` after at FL4's new arch state, from `ARKeep` [P]. -/
theorem JAtZ.fpuReleaseJ (hK : ARKeep arI AR) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64}
    (ht : t ∈ Z.T) :
    arI.fpu_release a t ⦃ a' => ∃ σ', ((), σ') ∈ (Fl4Spec.fpuRelease (Z := Unit) t.bv σ).1 ∧
      ∃ V', JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst D s a' σ' ⦄ := by
  have hAR : AR a σ.archState.x64CurrentCr3 := J.xtop.fin.1.1.2.2.2.2.2.2
  refine WP.spec_mono (hK.fpu_release a t _ hAR) ?_
  intro a' hAR'
  obtain ⟨Q, R0, hc, hs⟩ := J.xtop.fin.1.1.1.lists
  obtain ⟨x, hk, -⟩ := hs.tcb t ht
  obtain ⟨ta, ms, o, hr, hum, hm⟩ := Sched.fpuRelease_outF hk
  obtain ⟨V1, J1⟩ := J.tcbArchJ ht hk ta hr
  exact ⟨_, hm, V1, J1.arFrS (arFr_fpuOwner _ ms o) (J1.xtop.fpuOwner ms o hum hAR')⟩

end

end

end Fl4Proofs.P3
