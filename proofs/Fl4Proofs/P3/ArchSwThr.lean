/-
P3 (line p3J, gen 11): **the thread half of `ArchSwF` is a theorem** (`archSwFT_of`), from the opaque
FPU-operation determinism premises only.

`ArchSwFT` (ArchSwIdle) asks, at every state with `SchedRel` / `NtfnStateRel` / `FpuOwnOK` / `VsRootOK`
and every `t ∈ T`: FL4's `set_vm_root` refines the spec's `archSwitchToThread t` (`setVmRoot t;
lazyFpuRestore t`) with one outcome, keeping `SchedRel`, `NtfnStateRel` and `ArchKeepsF`. Its post says
nothing about CR3 (that is `ArchRefines` / `AR`, carried separately by the g7e chain), so no `StateRel` /
`VsRel` is needed at the scheduler's intermediate states:

* FL4: `set_vm_root` writes no store word (`set_vm_root_s`) and is total (P0, `ArchTotal`).
* Spec `setVmRoot t` (`setVmRoot_one`): the TCB of `t ∈ T` is in the heap (`SchedRel`); a mapped PML4
  vtable has a nonzero ASID and every ASID-table entry names a pool (`VsRootOK`), so `findVspaceForAsid`
  has one outcome (VsRel's `findVspaceForAsid_none` / `_some`) and `setVmRoot` is `cr3Upd σ c` for some
  `c` (VsRoot's `setVmRoot_mapped` / `setVmRoot_other`; `setCurrentCr3` is a plain update).
* Spec `lazyFpuRestore t` (`lazy_eq`): `disableFpu` (FPU disabled flag), `enableFpu` (already owner), or
  `switchLocalFpuOwner (some t)` (`slfo_some_eq`): enable, save the old owner's image (`FpuOwnOK`), load
  `t`'s image (`writeFpuState`: **`writeFpuStateImpl`**), move the owner flag. The heap changes only in
  the two TCBs' arch part with the registers kept (`HeapEqUpToFpu`), nothing `ArchKeepsF` reads changes.

**Named premises.** `FpuImplDet` [P] (ScFpuNd, U41's `hFpu`: `enableFpuImpl` / `disableFpuImpl`) and
**`FpuWriteDet`** [P] (new, same shape: Fl4Spec `Machine.lean` `opaque writeFpuStateImpl`, l4v
`MachineOps.X64.writeFpuState_impl`, `consts'`, has at most one outcome). `FpuImplDet` does not cover
`writeFpuStateImpl`: the owner-switch branch of `lazyFpuRestore` runs it, and with an opaque constant of
two outcomes `archSwitchToThread` has two outcomes there, so `ArchSwFT`'s `= ({((), σ1)}, False)` is not
derivable from `FpuImplDet` alone (ScArchF's `ArchSwF` docstring lists `writeFpuStateImpl` among the
operations whose single outcome it assumes). `readFpuStateVal` is a function; the CR3 write is a plain
update. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.ArchSwIdle
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3 Fl4Proofs.P3.Vs

noncomputable section

section Spec
open Fl4Spec

/-- **[P] The FPU-image write has at most one outcome** (module docstring; Fl4Spec `Machine.lean`
`opaque writeFpuStateImpl`, l4v `MachineOps.X64.writeFpuState_impl`, `consts'`; the same shape as
`FpuImplDet`). -/
structure FpuWriteDet : Prop where
  /-- [P] `writeFpuStateImpl v` (l4v `writeFpuState_impl`). -/
  wr : ∀ (v : FpuState) (mr : MachineStateRest) (x y : Unit × MachineStateRest),
    x ∈ (writeFpuStateImpl v mr).1 → y ∈ (writeFpuStateImpl v mr).1 → x = y

/-- `ArchKeepsF` is transitive. -/
theorem akf_trans {σ1 σ2 σ3 : State Unit} (h1 : ArchKeepsF σ1 σ2) (h2 : ArchKeepsF σ2 σ3) : ArchKeepsF σ1 σ3 := by
  obtain ⟨a1, b1, c1, d1, e1, f1, g1, i1, j1, k1, l1, m1⟩ := h1
  obtain ⟨a2, b2, c2, d2, e2, f2, g2, i2, j2, k2, l2, m2⟩ := h2
  exact ⟨a1.trans a2, b2.trans b1, c2.trans c1, d2.trans d1, e2.trans e1, f2.trans f1, g2.trans g1,
    i2.trans i1, j2.trans j1, k2.trans k1, l2.trans l1, m2.trans m1⟩

/-- The state with FPU owner `o`. -/
def ownS (σ : State Unit) (o : Option ObjRef) : State Unit :=
  { σ with archState := { σ.archState with x64CurrentFpuOwner := o } }

/-- A TCB with its FPU-owner flag `b`. -/
def curT (b : Bool) (x : Tcb) : Tcb := { x with tcbArch := { x.tcbArch with tcbCurFpu := b } }

/-- A TCB after `as_user getFPUState` (its context written back unchanged). -/
def loadT (x : Tcb) : Tcb := { x with tcbArch := archTcbContextSet (archTcbContextGet x.tcbArch) x.tcbArch }

/-- The FPU image `load_fpu_state` reads. -/
def fpuV (x : Tcb) : FpuState := (archTcbContextGet x.tcbArch).userFpuState

/-- The state after `doMachineOp (writeFpuState v)`. -/
def fwrS (hW : FpuWriteDet) (v : FpuState) (σ : State Unit) : State Unit :=
  { σ with machineState := { σ.machineState with
      machineStateRest := ignR (writeFpuStateImpl v) (hW.wr v) σ.machineState.machineStateRest } }

theorem fwr_eq (hW : FpuWriteDet) (v : FpuState) {ms : MachineState} (hE : ms.fpuEnabled = true) :
    writeFpuState v ms =
      ({((), { ms with machineStateRest := ignR (writeFpuStateImpl v) (hW.wr v) ms.machineStateRest })}, False) := by
  unfold writeFpuState
  rw [nd_bind_one (show NonDet.stateAssert (fun s : MachineState => s.fpuEnabled = true) ms = ({((), ms)}, False) by
    simp [NonDet.stateAssert, NonDet.assert, hE])]
  exact mol_eq _ (hW.wr v) ms

theorem load_eq (hW : FpuWriteDet) {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (hE : σ.machineState.fpuEnabled = true) :
    loadFpuState (Z := Unit) t σ = ({((), fwrS hW (fpuV x) (updK σ t (.tcb (loadT x))))}, False) := by
  unfold loadFpuState
  rw [nd_bind_one (asUser_one hk getFPUState (a := fpuV x) (uc' := archTcbContextGet x.tcbArch) rfl)]
  exact doMachineOp_one (σ := updK σ t (.tcb (loadT x)))
    (fwr_eq hW (fpuV x) (ms := (updK σ t (.tcb (loadT x))).machineState) hE)

theorem setOwner_some_of_none {σ : State Unit} {t : ObjRef} {x : Tcb}
    (ho : σ.archState.x64CurrentFpuOwner = none) (hk : σ.kheap t = some (.tcb x)) :
    setX64CurrentFpuOwner (Z := Unit) (some t) σ =
      ({((), updK (ownS σ (some t)) t (.tcb (curT true x)))}, False) := by
  unfold setX64CurrentFpuOwner
  rw [nd_gets_bind, ho, mb_none, nd_modify_bind']
  exact archThreadSet_eq (σ := ownS σ (some t)) hk (fun a => { a with tcbCurFpu := true })

theorem setOwner_some_of_some {σ : State Unit} {o t : ObjRef} {xo xt : Tcb}
    (ho : σ.archState.x64CurrentFpuOwner = some o) (hko : σ.kheap o = some (.tcb xo))
    (hkt : σ.kheap t = some (.tcb xt)) (hne : o ≠ t) :
    setX64CurrentFpuOwner (Z := Unit) (some t) σ =
      ({((), updK (ownS (updK σ o (.tcb (curT false xo))) (some t)) t (.tcb (curT true xt)))}, False) := by
  have hkt' : (ownS (updK σ o (.tcb (curT false xo))) (some t)).kheap t = some (.tcb xt) := by
    simp [ownS, updK, Function.update_of_ne hne.symm, hkt]
  unfold setX64CurrentFpuOwner
  rw [nd_gets_bind, ho, mb_some, nd_bind_one (archThreadSet_eq hko _), nd_modify_bind']
  exact archThreadSet_eq hkt' (fun a => { a with tcbCurFpu := true })

/-- **`switch_local_fpu_owner (some t)` has one outcome** under `FpuImplDet`, `FpuWriteDet`, `FpuOwnOK`,
when `t` is a TCB and not already the owner. -/
theorem slfo_some_eq (hD : FpuImplDet) (hW : FpuWriteDet) {σ : State Unit} {t : ObjRef} {x : Tcb}
    (hk : σ.kheap t = some (.tcb x)) (hfo : FpuOwnOK σ) (ho : σ.archState.x64CurrentFpuOwner ≠ some t) :
    ∃ σ1, switchLocalFpuOwner (Z := Unit) (some t) σ = ({((), σ1)}, False) ∧ ArchKeepsF σ σ1 ∧
      σ1.reprogramTimer = σ.reprogramTimer := by
  rcases hc : σ.archState.x64CurrentFpuOwner with _ | o
  · refine ⟨updK (ownS (fwrS hW (fpuV x) (updK (enS hD σ) t (.tcb (loadT x)))) (some t)) t
      (.tcb (curT true (loadT x))), ?_, ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
    · unfold switchLocalFpuOwner
      rw [nd_gets_bind, nd_bind_one (dmo_en hD σ), hc, mb_none]
      dsimp only
      rw [nd_bind_one (load_eq hW (σ := enS hD σ) hk rfl)]
      exact setOwner_some_of_none (σ := fwrS hW (fpuV x) (updK (enS hD σ) t (.tcb (loadT x)))) hc
        (by simp [fwrS, updK])
    · intro q
      by_cases hq : q = t
      · rw [hq]
        exact Or.inr ⟨x, curT true (loadT x), hk, by simp [updK], ⟨rfl, rfl⟩⟩
      · exact Or.inl (by simp [updK, ownS, fwrS, enS, Function.update_of_ne hq])
  · obtain ⟨xo, hxo⟩ := hfo o hc
    have hne : o ≠ t := fun e => ho (by rw [hc, e])
    have hkS : (updK (enS hD σ) o (.tcb (saveT (enS hD σ) xo))).kheap t = some (.tcb x) := by
      simp [updK, enS, Function.update_of_ne hne.symm, hk]
    refine ⟨updK (ownS (updK (fwrS hW (fpuV x) (updK (updK (enS hD σ) o (.tcb (saveT (enS hD σ) xo))) t
        (.tcb (loadT x)))) o (.tcb (curT false (saveT (enS hD σ) xo)))) (some t)) t (.tcb (curT true (loadT x))),
      ?_, ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
    · unfold switchLocalFpuOwner
      rw [nd_gets_bind, nd_bind_one (dmo_en hD σ), hc, mb_some, nd_bind_one (save_eq (σ := enS hD σ) hxo rfl)]
      dsimp only
      rw [nd_bind_one (load_eq hW (σ := updK (enS hD σ) o (.tcb (saveT (enS hD σ) xo))) hkS rfl)]
      exact setOwner_some_of_some
        (σ := fwrS hW (fpuV x) (updK (updK (enS hD σ) o (.tcb (saveT (enS hD σ) xo))) t (.tcb (loadT x)))) hc
        (by simp [fwrS, updK, Function.update_of_ne hne]) (by simp [fwrS, updK]) hne
    · intro q
      by_cases hqt : q = t
      · rw [hqt]
        exact Or.inr ⟨x, curT true (loadT x), hk, by simp [updK], ⟨rfl, rfl⟩⟩
      · by_cases hqo : q = o
        · rw [hqo]
          exact Or.inr ⟨xo, curT false (saveT (enS hD σ) xo), hxo,
            by simp [updK, ownS, fwrS, Function.update_of_ne hne], ⟨rfl, rfl⟩⟩
        · exact Or.inl (by simp [updK, ownS, fwrS, enS, Function.update_of_ne hqt, Function.update_of_ne hqo])

/-- **`lazy_fpu_restore t` has one outcome** (module docstring). -/
theorem lazy_eq (hD : FpuImplDet) (hW : FpuWriteDet) {σ : State Unit} {t : ObjRef} {x : Tcb}
    (hk : σ.kheap t = some (.tcb x)) (hfo : FpuOwnOK σ) :
    ∃ σ1, lazyFpuRestore (Z := Unit) t σ = ({((), σ1)}, False) ∧ ArchKeepsF σ σ1 ∧
      σ1.reprogramTimer = σ.reprogramTimer := by
  unfold lazyFpuRestore
  rw [nd_bind_one (threadGet_eq Tcb.tcbFlags hk)]
  by_cases hf : TcbFlag.fpuDisabled ∈ x.tcbFlags
  · rw [if_pos hf]
    exact ⟨_, dmo_dis hD σ, ⟨HeapEqUpToFpu.of_eq rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · rw [if_neg hf, nd_gets_bind]
    try dsimp only
    by_cases ho : σ.archState.x64CurrentFpuOwner = some t
    · rw [if_pos ho]
      exact ⟨_, dmo_en hD σ, ⟨HeapEqUpToFpu.of_eq rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
    · rw [if_neg ho]
      exact slfo_some_eq hD hW hk hfo ho

/-- **The spec's `setVmRoot t` has one outcome, a CR3 update**, for a TCB whose mapped-PML4 vtable has a
nonzero ASID, at a state whose ASID-table entries name pools (`VsRootOK`). -/
theorem setVmRoot_one {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (h0 : ∀ p a, x.tcbVtable = .archObjectCap (.pml4Cap p (some a)) → a ≠ 0)
    (hp : ∀ i p, σ.archState.x64AsidTable i = some p → ∃ f, σ.kheap p = some (.archObj (.asidPool f))) :
    ∃ c, setVmRoot (Z := Unit) t σ = ({((), cr3Upd σ c)}, False) := by
  by_cases hm : ∃ p asid, x.tcbVtable = .archObjectCap (.pml4Cap p (some asid))
  · obtain ⟨p, asid, hv⟩ := hm
    have hpos : asid > 0 := by
      have hne := h0 p asid hv
      show 0 < asid.toNat
      exact Nat.pos_of_ne_zero (fun h => hne (BitVec.eq_of_toNat_eq (by simpa using h)))
    rcases ht : σ.archState.x64AsidTable (asidHighBitsOf asid) with _ | q
    · exact ⟨_, setVmRoot_mapped hk hv (findVspaceForAsid_none hpos ht)⟩
    · obtain ⟨f, hf⟩ := hp _ q ht
      exact ⟨_, setVmRoot_mapped hk hv (findVspaceForAsid_some hpos ht hf)⟩
  · push Not at hm
    exact ⟨_, setVmRoot_other hk hm⟩

end Spec

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- **The thread half of `ArchSwF` is a theorem** (module docstring), at every ghost set. -/
theorem archSwFT_of (hD : FpuImplDet) (hW : FpuWriteDet) (hAT : P0.ArchTotal ar) {N T C : Set U64} {c : U64} :
    ArchSwFT st ar N T C c := by
  intro s a σ hS hR hfo hvr t ht
  have hSt : P0.StoreTotal st := P1.LawfulStore.total
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x, hk, -⟩ := hs.tcb t ht
  obtain ⟨c1, hv⟩ := setVmRoot_one hk (hvr.1 t ht x hk) hvr.2
  obtain ⟨σ1, hl, hkf, hrt⟩ := lazy_eq hD hW (σ := cr3Upd σ c1) hk (fun o e => hfo o e)
  have hK : ArchKeepsF σ σ1 := akf_trans (archKeeps_cr3 σ c1).toF hkf
  refine WP.spec_mono (P1.spec_eq' (Fl4Proofs.P0.vspace.set_vm_root.p0 st ar s a t hSt hAT)) ?_
  rintro r ⟨hr, -⟩
  rw [set_vm_root_s hr]
  refine ⟨σ1, ?_, hS.fpu hK hrt, hR.fpu hK.1, hK⟩
  unfold Fl4Spec.archSwitchToThread
  rw [nd_bind_one hv]
  exact hl

/-- `ArchSwF` (both halves; `ArchSwF'` before collapse A, K) from the opaque FPU premises and `ArchTotal`. -/
theorem archSwF'_of (hD : FpuImplDet) (hW : FpuWriteDet) (hAT : P0.ArchTotal ar) {N T C : Set U64} {c : U64} :
    ArchSwF st ar N T C c :=
  (archSwFT_of hD hW hAT).toN hAT

end

end

end Fl4Proofs.P3.Sched
