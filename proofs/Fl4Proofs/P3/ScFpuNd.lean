/-
P3 (line p3J, gen 8): **`ArchNdF` from a fact about two opaque machine operations** (`archNdF_of`).

* **`FpuImplDet`** [P] (opaque constants, as ScSniPre's `SetDlDet`): Fl4Spec `Machine.lean`'s
  `opaque enableFpuImpl` / `opaque disableFpuImpl` (l4v `MachineOps.X64.enableFpu_impl` / `disableFpu_impl`,
  `consts'`) have at most one outcome. (`readFpuStateVal` is a function; `machine_op_lift`'s
  `ignore_failure` makes both total.)
* Frames: **`SchedRel.fpu`** (`ArchKeepsF` and the same `reprogram_timer`), **`NtfnStateRel.fpu`**
  (`HeapEqUpToFpu`): the relations read TCBs' state, priority, domain, SC and registers only.
* `apnd_eq`: the spec's `arch_prepare_next_domain` (`switch_local_fpu_owner None`: enable, save the owner's
  image (`FpuOwnOK`), disable, clear the owner flag and the owner) has one outcome, with `ArchKeepsF`, the
  timer flag and domain fields kept and no owner after.
* **`archNdF_of : FpuImplDet → ArchNdF st N T C c`** (for every ghost set).

Named premises: `FpuImplDet` [P] only. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.ScNextDomF
import Fl4Proofs.P3.SpecFinOutTcb
import Fl4Proofs.P3.ScSniPre
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-- **[P] The FPU enable / disable machine operations have at most one outcome** (module docstring;
Fl4Spec `Machine.lean` `opaque enableFpuImpl`, `opaque disableFpuImpl`, l4v `MachineOps.X64`). -/
structure FpuImplDet : Prop where
  /-- [P] `enableFpuImpl` (l4v `enableFpu_impl`). -/
  en : ∀ (mr : MachineStateRest) (x y : Unit × MachineStateRest),
    x ∈ (enableFpuImpl mr).1 → y ∈ (enableFpuImpl mr).1 → x = y
  /-- [P] `disableFpuImpl` (l4v `disableFpu_impl`). -/
  dis : ∀ (mr : MachineStateRest) (x y : Unit × MachineStateRest),
    x ∈ (disableFpuImpl mr).1 → y ∈ (disableFpuImpl mr).1 → x = y

theorem ign_one {σ : Type} (f : NonDet σ Unit) (s : σ) (hD : ∀ x y, x ∈ (f s).1 → y ∈ (f s).1 → x = y) :
    ∃ s', ignoreFailure f s = ({((), s')}, False) := by
  unfold ignoreFailure
  split_ifs with he
  · exact ⟨s, rfl⟩
  · obtain ⟨⟨⟨⟩, s'⟩, hx⟩ := Set.nonempty_iff_ne_empty.2 he
    refine ⟨s', Prod.ext ?_ rfl⟩
    ext y
    constructor
    · intro hy; exact Set.mem_singleton_iff.2 (hD _ _ hy hx)
    · intro hy; rw [Set.mem_singleton_iff.1 hy]; exact hx

/-- The one outcome of `ignore_failure f` at `mr`. -/
def ignR (f : MachineRestMonad Unit)
    (h : ∀ (mr : MachineStateRest) (x y : Unit × MachineStateRest), x ∈ (f mr).1 → y ∈ (f mr).1 → x = y)
    (mr : MachineStateRest) : MachineStateRest :=
  Classical.choose (ign_one f mr (h mr))

theorem ignR_eq (f : MachineRestMonad Unit)
    (h : ∀ (mr : MachineStateRest) (x y : Unit × MachineStateRest), x ∈ (f mr).1 → y ∈ (f mr).1 → x = y)
    (mr : MachineStateRest) : ignoreFailure f mr = ({((), ignR f h mr)}, False) :=
  Classical.choose_spec (ign_one f mr (h mr))

theorem mol_eq (f : MachineRestMonad Unit)
    (h : ∀ (mr : MachineStateRest) (x y : Unit × MachineStateRest), x ∈ (f mr).1 → y ∈ (f mr).1 → x = y)
    (ms : MachineState) :
    machineOpLift f ms = ({((), { ms with machineStateRest := ignR f h ms.machineStateRest })}, False) := by
  unfold machineOpLift machineRestLift
  rw [nd_gets_bind, ignR_eq f h, nd_bind_one (selectF_sni _ _)]
  dsimp only
  rw [nd_modify_bind']
  rfl

/-- The machine state after `enableFpu`. -/
def enMs (hD : FpuImplDet) (ms : MachineState) : MachineState :=
  { ms with machineStateRest := ignR enableFpuImpl hD.en ms.machineStateRest, fpuEnabled := true }

/-- The machine state after `disableFpu`. -/
def disMs (hD : FpuImplDet) (ms : MachineState) : MachineState :=
  { ms with machineStateRest := ignR disableFpuImpl hD.dis ms.machineStateRest, fpuEnabled := false }

theorem en_eq (hD : FpuImplDet) (ms : MachineState) : enableFpu ms = ({((), enMs hD ms)}, False) := by
  unfold enableFpu
  rw [nd_bind_one (mol_eq _ hD.en ms)]
  rfl

theorem dis_eq (hD : FpuImplDet) (ms : MachineState) : disableFpu ms = ({((), disMs hD ms)}, False) := by
  unfold disableFpu
  rw [nd_bind_one (mol_eq _ hD.dis ms)]
  rfl

theorem read_eq {ms : MachineState} (hE : ms.fpuEnabled = true) :
    readFpuState ms = ({(readFpuStateVal ms.machineStateRest, ms)}, False) := by
  unfold readFpuState
  rw [nd_bind_one (show NonDet.stateAssert (fun s : MachineState => s.fpuEnabled = true) ms = ({((), ms)}, False) by
    simp [NonDet.stateAssert, NonDet.assert, hE])]
  unfold machineRestLift
  rw [nd_gets_bind, nd_bind_one (show NonDet.selectF (σ := MachineState) (NonDet.gets readFpuStateVal ms.machineStateRest) ms =
    ({((readFpuStateVal ms.machineStateRest, ms.machineStateRest), ms)}, False) from selectF_sni _ _)]
  dsimp only
  rw [nd_modify_bind']
  rfl

/-- The state after `doMachineOp enableFpu`. -/
def enS (hD : FpuImplDet) (σ : State Unit) : State Unit := { σ with machineState := enMs hD σ.machineState }

/-- The state after `doMachineOp disableFpu`. -/
def disS (hD : FpuImplDet) (σ : State Unit) : State Unit := { σ with machineState := disMs hD σ.machineState }

theorem dmo_en (hD : FpuImplDet) (σ : State Unit) :
    doMachineOp (Z := Unit) enableFpu σ = ({((), enS hD σ)}, False) := doMachineOp_one (en_eq hD _)

theorem dmo_dis (hD : FpuImplDet) (σ : State Unit) :
    doMachineOp (Z := Unit) disableFpu σ = ({((), disS hD σ)}, False) := doMachineOp_one (dis_eq hD _)

/-- The owner's TCB after `save_fpu_state`. -/
def saveT (σ : State Unit) (x : Tcb) : Tcb :=
  { x with tcbArch := archTcbContextSet ⟨readFpuStateVal σ.machineState.machineStateRest,
    (archTcbContextGet x.tcbArch).userRegs⟩ x.tcbArch }

/-- A TCB with its FPU-owner flag cleared. -/
def fpuClrT (x : Tcb) : Tcb := { x with tcbArch := { x.tcbArch with tcbCurFpu := false } }

theorem save_eq {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (hE : σ.machineState.fpuEnabled = true) :
    saveFpuState (Z := Unit) t σ = ({((), updK σ t (.tcb (saveT σ x)))}, False) := by
  unfold saveFpuState
  rw [nd_bind_one (doMachineOp_one (read_eq hE))]
  exact asUser_one hk _ rfl

theorem mb_none {σ α β : Type} (f : α → NonDet σ Unit) (g : Unit → NonDet σ β) (s : σ) :
    (NonDet.maybeM f none >>= g) s = g () s :=
  Notif.nd_bind_one (m := NonDet.maybeM f none) (s := s) (s' := s) (a := ()) rfl g

theorem mb_some {σ α β : Type} (f : α → NonDet σ Unit) (a : α) (g : Unit → NonDet σ β) (s : σ) :
    (NonDet.maybeM f (some a) >>= g) s = (f a >>= g) s := rfl

theorem setOwner_none_eq {σ : State Unit} (ho : σ.archState.x64CurrentFpuOwner = none) :
    setX64CurrentFpuOwner (Z := Unit) none σ =
      ({((), { σ with archState := { σ.archState with x64CurrentFpuOwner := none } })}, False) := by
  unfold setX64CurrentFpuOwner
  rw [nd_gets_bind, ho, mb_none, nd_modify_bind']
  rfl

theorem setOwner_some_eq {σ : State Unit} {o : ObjRef} {x : Tcb} (ho : σ.archState.x64CurrentFpuOwner = some o)
    (hk : σ.kheap o = some (.tcb x)) :
    setX64CurrentFpuOwner (Z := Unit) none σ =
      ({((), { updK σ o (.tcb (fpuClrT x)) with archState := { σ.archState with x64CurrentFpuOwner := none } })},
        False) := by
  unfold setX64CurrentFpuOwner
  rw [nd_gets_bind, ho, mb_some, nd_bind_one (archThreadSet_eq hk _), nd_modify_bind']
  rfl

/-- **The spec's `arch_prepare_next_domain` has one outcome** under `FpuImplDet` and `FpuOwnOK`. -/
theorem apnd_eq (hD : FpuImplDet) (σ : State Unit) (hfo : FpuOwnOK σ) :
    ∃ σ1, archPrepareNextDomain (Z := Unit) σ = ({((), σ1)}, False) ∧ ArchKeepsF σ σ1 ∧
      σ1.reprogramTimer = σ.reprogramTimer ∧ σ1.domainList = σ.domainList ∧ σ1.domainIndex = σ.domainIndex ∧
      σ1.domainStartIndex = σ.domainStartIndex ∧ σ1.archState.x64CurrentFpuOwner = none := by
  rcases hc : σ.archState.x64CurrentFpuOwner with _ | o
  · refine ⟨{ disS hD (enS hD σ) with
      archState := { (disS hD (enS hD σ)).archState with x64CurrentFpuOwner := none } }, ?_, ?_⟩
    · unfold archPrepareNextDomain switchLocalFpuOwner
      rw [nd_gets_bind, nd_bind_one (dmo_en hD σ), hc, mb_none]
      dsimp only
      rw [nd_bind_one (dmo_dis hD _), setOwner_none_eq (σ := disS hD (enS hD σ)) hc]
    · exact ⟨⟨HeapEqUpToFpu.of_eq rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
        rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨x, hx⟩ := hfo o hc
    have hE : (enS hD σ).machineState.fpuEnabled = true := rfl
    have hk2 : (disS hD (updK (enS hD σ) o (.tcb (saveT (enS hD σ) x)))).kheap o =
        some (.tcb (saveT (enS hD σ) x)) := by
      simp [disS, updK]
    refine ⟨{ updK (disS hD (updK (enS hD σ) o (.tcb (saveT (enS hD σ) x)))) o (.tcb (fpuClrT (saveT (enS hD σ) x))) with
      archState := { (disS hD (updK (enS hD σ) o (.tcb (saveT (enS hD σ) x)))).archState with
        x64CurrentFpuOwner := none } }, ?_, ?_⟩
    · unfold archPrepareNextDomain switchLocalFpuOwner
      rw [nd_gets_bind, nd_bind_one (dmo_en hD σ), hc, mb_some, nd_bind_one (save_eq (σ := enS hD σ) hx hE)]
      dsimp only
      rw [nd_bind_one (dmo_dis hD _),
        setOwner_some_eq (σ := disS hD (updK (enS hD σ) o (.tcb (saveT (enS hD σ) x)))) hc hk2]
    · refine ⟨⟨fun p => ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩
      by_cases hp : p = o
      · subst hp
        refine Or.inr ⟨x, fpuClrT (saveT (enS hD σ) x), hx, ?_, And.intro rfl rfl⟩
        simp [updK]
      · refine Or.inl ?_
        simp [updK, disS, enS, Function.update_of_ne hp]

end Spec

/-! ## The relation frames -/

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **`SchedRel` across an FPU-only change** (`ArchKeepsF`, the same `reprogram_timer`). -/
theorem SchedRel.fpu {N T C : Set U64} {c : U64} {s : S} {σ σ' : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (hk : ArchKeepsF σ σ') (hr : σ'.reprogramTimer = σ.reprogramTimer) :
    SchedRel st N T C c s σ' := by
  obtain ⟨hh, hq, hrl, hct, hcs, hctm, hcons, hsa, hid, hcd, hdt, hisc⟩ := hk
  obtain ⟨placed, nodeNW, domNW, dtNW, scOut, scDisj, actW, act, repr, core, Q, R, hC, hSp⟩ := hS
  obtain ⟨rq, rqDom, rel, curThread, curSc, curTime, consumed, curDom, tcb, scMem, scs, idleSc, domTime,
    idleTh⟩ := hSp
  refine ⟨placed, nodeNW, domNW, dtNW, fun sc hsc x n hx => scOut sc hsc x n ((hh.sc).1 hx),
    fun sc hsc sc' hsc' hne x n x' n' hx hx' => scDisj sc hsc sc' hsc' hne x n x' n' ((hh.sc).1 hx) ((hh.sc).1 hx'),
    actW, by rw [hsa]; exact act, by rw [hr]; exact repr, core, Q, R, hC, ?_⟩
  refine ⟨fun p hp => by rw [hq]; exact rq p hp, fun d p hd => by rw [hq]; exact rqDom d p hd,
    by rw [hrl]; exact rel, by rw [hct]; exact curThread, by rw [hcs]; exact curSc, by rw [hctm]; exact curTime,
    by rw [hcons]; exact consumed, ⟨by rw [hcd]; exact curDom.1, curDom.2⟩, fun t ht => ?_, scMem,
    fun sc hsc => ?_, by rw [hisc]; exact idleSc, by rw [hdt]; exact domTime, by rw [hid]; exact idleTh⟩
  · obtain ⟨x, hx, a1, a2, a3, a4⟩ := tcb t ht
    obtain ⟨y, hy, e⟩ := hh.tcb hx
    have ed : y.tcbDomain = x.tcbDomain := by
      have e1 := congrArg Fl4Spec.Tcb.tcbDomain e.1; exact e1
    have ep : y.tcbPriority = x.tcbPriority := by
      have e1 := congrArg Fl4Spec.Tcb.tcbPriority e.1; exact e1
    exact ⟨y, hy, by rw [ed]; exact a1, a2, by rw [e.sc]; exact a3, by rw [ep]; exact a4⟩
  · obtain ⟨x, n, hx, hw⟩ := scs sc hsc
    exact ⟨x, n, (hh.sc).2 hx, by rw [hisc]; exact hw⟩

/-- **`NtfnStateRel` across an FPU-only change of the heap.** -/
theorem _root_.Fl4Proofs.P3.Notif.NtfnStateRel.fpu {N T : Set U64} {m : U64 → U64} {σ σ' : Fl4Spec.State Unit}
    (hR : NtfnStateRel N T m σ) (hh : HeapEqUpToFpu σ σ') : NtfnStateRel N T m σ' := by
  refine ⟨fun n hn => ?_, fun t ht => ?_⟩
  · obtain ⟨x, hx, hr⟩ := hR.ntfn n hn
    exact ⟨x, (hh.ntcb (fun _ e => by cases e)).2 hx, hr⟩
  · obtain ⟨x, hx, hr⟩ := hR.tcb t ht
    obtain ⟨y, hy, e⟩ := hh.tcb hx
    have est : y.tcbState = x.tcbState := e.st
    have epr : y.tcbPriority = x.tcbPriority := by
      have e1 := congrArg Fl4Spec.Tcb.tcbPriority e.1; exact e1
    have ebd : badgeOf y = badgeOf x := by unfold badgeOf; rw [e.2]
    exact ⟨y, hy, ⟨by rw [est]; exact hr.st, fun n hn => hr.blk n (est.symm.trans hn),
      by rw [ebd]; exact hr.badge, by rw [epr]; exact hr.prio⟩⟩

/-- **`ArchNdF` from `FpuImplDet`** (module docstring), at every ghost set. -/
theorem archNdF_of (hD : FpuImplDet) {N T C : Set U64} {c : U64} : ArchNdF st N T C c := by
  intro s σ hS hR hfo
  obtain ⟨σ1, e, hk, hr, h1, h2, h3, h4⟩ := apnd_eq hD σ hfo
  exact ⟨σ1, e, hS.fpu hk hr, hR.fpu hk.1, hk, h1, h2, h3, h4⟩

end

end

end Fl4Proofs.P3.Sched
