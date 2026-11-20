/-
P3 (DESIGN.md §9), the invariant line (INV-PLAN §4 G1, invB): **`ValidMachineTime`
is kept by the syscall entry** (spec side only; outside the `JAtZ` cone).

* `ValidMachineTime σ` [J] (l4v `valid_machine_time`): `cur_time ≤
  last_machine_time ≤` the clock's cap. The same body as XTopJointMachRel's
  `ValidMachineTime` (the premise `hR`/`MachPlat.nowAgree` of
  `kernel_entryJ26P` reads), which is in the `JAtZ` cone; the two are
  definitionally equal (`Iff.rfl` at the wiring site).
* `uts_out`: `updateTimeStamp` sets the current time and the last machine time
  to the clock value (`getCurrentTime` returns the new last machine time) and
  keeps the interrupt table and the masks.
* **FINDING** `readFpu_breaks_vmt`: the spec's ReadFPU (Ext/Tcb `invokeFl4Tcb`
  `.fpuTransfer _ true _`, `invokeFl4Tcb_readFpu`) sets the WHOLE machine state
  to any value (`fpuStep`), so it can set the last machine time above the
  clock's cap (and below the current time). Trace: a thread holding a TCB cap
  and a writable non-device frame cap (64-aligned offset, room for the 576-byte
  image) calls ReadFPU (label `fl4TcbExtLabelNum .readFpu`); decode
  (`decodeFl4FpuTransfer true`) succeeds and the perform is `fpuStep`;
  `fl4Awaken`/`schedule`/`activateThread` never call `getCurrentTime`, so the
  entry's outcome has `lastMachineTime = allOnes`. FL4's ReadFPU writes only
  the frame (and the FPU), so this is a spec modelling gap: the step should
  change only `underlyingMemory` (and the FPU state). Stopped on this field.
* `wl_vmt_of` / `kentry_vmt_of`: the reduction, every leaf but ReadFPU's
  (`setIrqState`, the masking machine operations and the ack keep both
  times; `updateTimeStamp` by `uts_out`), so with a ReadFPU keeping the last
  machine time the whole syscall entry keeps `ValidMachineTime`
  (SpecInvValidMachineTimeGen's `gk_fl4KernelEntrySyscall`). Its hypothesis is
  FALSE in the current spec; not a top theorem.
* `boot_vmt`: the spec's initial state (`Init.initASt`).
-/
import Fl4Proofs.P3.SpecInvValidMachineTimeGen

open Classical

namespace Fl4Proofs.P3.SInvV
open Fl4Spec Fl4Proofs.P3.Vs

noncomputable section

/-- The cap of the spec's clock (`getCurrentTime`). -/
abbrev timeCapS : Nat := unat (-(getCurrentTimeBuffer + 1))

/-- **[J] l4v `valid_machine_time`** (module docstring). -/
def ValidMachineTime (σ : State Unit) : Prop :=
  σ.curTime ≤ σ.machineState.lastMachineTime ∧ unat σ.machineState.lastMachineTime ≤ timeCapS

/-! ## Monad facts -/

theorem sv_bind_single {σ α β : Type} {m : NonDet σ α} {f : α → NonDet σ β} {s : σ} {x : α × σ}
    (h : m s = ({x}, False)) : (m >>= f) s = f x.1 x.2 := by
  show NonDet.bind m f s = _
  unfold NonDet.bind
  rw [h]
  refine Prod.ext ?_ ?_
  · ext r; simp
  · simp

theorem sv_bind_gets {σ α β : Type} (g : σ → α) (f : α → NonDet σ β) (s : σ) :
    (NonDet.gets g >>= f) s = f (g s) s := sv_bind_single (m := NonDet.gets g) (x := (g s, s)) rfl

theorem sv_bind_modify {σ β : Type} (g : σ → σ) (f : Unit → NonDet σ β) (s : σ) :
    (NonDet.modify g >>= f) s = f () (g s) := sv_bind_single (m := NonDet.modify g) (x := ((), g s)) rfl

theorem sv_bind_pure {σ α β : Type} (a : α) (f : α → NonDet σ β) (s : σ) :
    ((pure a : NonDet σ α) >>= f) s = f a s := sv_bind_single (m := pure a) (x := (a, s)) rfl

/-- The value `getCurrentTime` computes (as a number). -/
def gctN (ms : MachineState) : Nat :=
  min timeCapS (unat ms.lastMachineTime + timeOracle (ms.timeState + 1))

/-- The machine state after `getCurrentTime`. -/
def gctS (ms : MachineState) : MachineState :=
  { ms with timeState := ms.timeState + 1, lastMachineTime := BitVec.ofNat 64 (gctN ms) }

theorem getCurrentTime_single (ms : MachineState) :
    getCurrentTime ms = ({(BitVec.ofNat 64 (gctN ms), gctS ms)}, False) := by
  unfold getCurrentTime
  rw [sv_bind_modify, sv_bind_gets, sv_bind_gets, sv_bind_pure, sv_bind_pure, sv_bind_modify]
  rfl

theorem dmo_single {α : Type} {mop : NonDet MachineState α} {σ : State Unit} {v : α}
    {ms' : MachineState} (h : mop σ.machineState = ({(v, ms')}, False)) :
    doMachineOp (Z := Unit) mop σ = ({(v, { σ with machineState := ms' })}, False) := by
  unfold doMachineOp
  rw [sv_bind_gets]
  have hs : NonDet.selectF (mop σ.machineState) σ = ({((v, ms'), σ)}, False) := by
    unfold NonDet.selectF
    rw [h]
    refine Prod.ext ?_ rfl
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩; exact Prod.ext h1 h2
    · rintro rfl; exact ⟨rfl, rfl⟩
  rw [sv_bind_single hs]
  dsimp only
  rw [sv_bind_modify]
  rfl

theorem gctN_le (ms : MachineState) : gctN ms ≤ timeCapS := Nat.min_le_left _ _

theorem gctN_toNat (ms : MachineState) : (BitVec.ofNat 64 (gctN ms)).toNat = gctN ms := by
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (gctN_le ms) (-(getCurrentTimeBuffer + 1)).isLt)

/-- **`updateTimeStamp`'s outcome** (module docstring). -/
theorem uts_out {σ : State Unit} {x : Unit × State Unit} (hx : x ∈ (updateTimeStamp (Z := Unit) σ).1) :
    x.2.curTime = BitVec.ofNat 64 (gctN σ.machineState) ∧
      x.2.machineState.lastMachineTime = BitVec.ofNat 64 (gctN σ.machineState) ∧
      x.2.interruptStates = σ.interruptStates ∧ x.2.machineState.irqMasks = σ.machineState.irqMasks := by
  unfold updateTimeStamp at hx
  rw [sv_bind_gets, sv_bind_single (dmo_single (getCurrentTime_single σ.machineState))] at hx
  dsimp only at hx
  rw [sv_bind_pure, sv_bind_modify, sv_bind_modify, sv_bind_gets] at hx
  have key : ∀ {m : NonDet (State Unit) Unit} {s : State Unit}, FK vw m → x ∈ (m s).1 → vw x.2 = vw s :=
    fun hm h => hm _ _ h
  have e := key (by dk_auto0) hx
  unfold vw at e
  simp only [Prod.mk.injEq] at e
  obtain ⟨e1, e2, e3, e4⟩ := e
  exact ⟨e1, e2, e3, e4⟩

/-! ## The leaves -/

/-- The current time and the last machine time. -/
def tl (σ : State Unit) := (σ.curTime, σ.machineState.lastMachineTime)

theorem fk_tl_dmo {α : Type} {mop : NonDet MachineState α}
    (h : ∀ ms x, x ∈ (mop ms).1 → x.2.lastMachineTime = ms.lastMachineTime) : FK tl (doMachineOp (Z := Unit) mop) := by
  intro σ x hx
  unfold doMachineOp at hx
  obtain ⟨⟨ms0, s1⟩, h1, ⟨⟨r, ms'⟩, s2⟩, h2, ⟨u, s3⟩, h3, hx⟩ := hx
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h1)
  obtain ⟨h2a, e2⟩ := h2
  dsimp only at e2 h2a
  subst e2
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h3)
  rw [Set.mem_singleton_iff.1 hx]
  exact Prod.ext rfl (h _ _ h2a)

theorem ik_of_tl {P : State Unit → Prop} (hP : ∀ σ σ', tl σ' = tl σ → P σ → P σ') {α : Type}
    {m : NonDet (State Unit) α} (h : FK tl m) : IK P m :=
  fun σ hσ x hx => hP σ x.2 (h σ x hx) hσ

theorem vmt_tl : ∀ σ σ' : State Unit, tl σ' = tl σ → ValidMachineTime σ → ValidMachineTime σ' := by
  intro σ σ' e h
  unfold tl at e; simp only [Prod.mk.injEq] at e
  unfold ValidMachineTime; rw [e.1, e.2]; exact h

theorem mask_lmt (m : Bool) (i : Irq) : ∀ ms x, x ∈ (maskInterrupt m i ms).1 →
    x.2.lastMachineTime = ms.lastMachineTime := by
  intro ms x hx; unfold maskInterrupt at hx; rw [Set.mem_singleton_iff.1 hx]

/-- The spec's ReadFPU machine step (Ext/Tcb `invokeFl4Tcb`, `.fpuTransfer _ true _`): any machine state. -/
abbrev fpuStep : NonDet (State Unit) Unit :=
  doMachineOp (Z := Unit) (NonDet.select (Set.univ : Set MachineState) >>= fun ms => NonDet.modify fun _ => ms)

/-- ReadFPU's perform is `fpuStep` (by definition). -/
theorem invokeFl4Tcb_readFpu (t f : ObjRef) :
    invokeFl4Tcb (Z := Unit) (.fpuTransfer t true f) = NonDetE.liftE (do fpuStep; return []) := rfl

/-- Every machine state is an outcome of `fpuStep`. -/
theorem fpuStep_any (σ : State Unit) (ms : MachineState) : ((), { σ with machineState := ms }) ∈ (fpuStep σ).1 := by
  show _ ∈ (doMachineOp (Z := Unit) _ σ).1
  unfold doMachineOp
  exact ⟨(σ.machineState, σ), rfl, (((), ms), σ), ⟨⟨(ms, σ.machineState), ⟨trivial, rfl⟩, rfl⟩, rfl⟩,
    ((), { σ with machineState := ms }), rfl, rfl⟩

/-- The cap is below `allOnes` (`getCurrentTime_buffer_pos`). -/
theorem timeCapS_lt : timeCapS < 2 ^ 64 - 1 := by
  have hb : getCurrentTimeBuffer ≠ 0 := by
    have := getCurrentTime_buffer_pos
    intro e; unfold getCurrentTimeBuffer timeBufferConst MAX_PERIOD at e; rw [e] at this
    exact (BitVec.lt_irrefl _) this
  have hc : timeCapS ≠ 2 ^ 64 - 1 := by
    intro e
    apply hb
    have e2 : -(getCurrentTimeBuffer + 1) = BitVec.allOnes 64 :=
      BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_allOnes]; exact e)
    have e3 : getCurrentTimeBuffer + 1 = 1 := by
      have := congrArg (fun x => -x) e2
      simp only [BitVec.neg_neg] at this
      rw [this]; decide
    have e4 := congrArg (fun x => x - 1) e3
    simpa using e4
  have hlt : timeCapS < 2 ^ 64 := (-(getCurrentTimeBuffer + 1)).isLt
  omega

/-- **FINDING (invB): the spec's ReadFPU breaks `ValidMachineTime`.** From
every state, `fpuStep` (ReadFPU's perform, `invokeFl4Tcb_readFpu`) has an
outcome whose last machine time is `allOnes`, above the clock's cap. The
rest of the syscall (`fl4Awaken`, `schedule`, `activateThread`) never calls
`getCurrentTime`, so the entry's outcome keeps it (module docstring of
SpecInvValidMachineTimeKit: every other step keeps the last machine time
or sets it to a capped clock value). -/
theorem readFpu_breaks_vmt (σ : State Unit) : ∃ y ∈ (fpuStep σ).1, ¬ ValidMachineTime y.2 := by
  refine ⟨_, fpuStep_any σ { σ.machineState with lastMachineTime := BitVec.allOnes 64 }, ?_⟩
  rintro ⟨-, h⟩
  have h' : (BitVec.allOnes 64).toNat ≤ timeCapS := h
  rw [BitVec.toNat_allOnes] at h'
  have := timeCapS_lt
  omega

/-- **The leaves of `ValidMachineTime` but ReadFPU's** (the reduction: with a
ReadFPU that keeps the last machine time, e.g. one writing only the frame's
memory, `hF` holds by `fk_tl_dmo` and `kentry_vmt_of` is the entry theorem).
`hF` itself is FALSE in the current spec (`readFpu_breaks_vmt`); this is not a
top theorem. -/
theorem wl_vmt_of (hF : IK ValidMachineTime fpuStep) : WL ValidMachineTime where
  view σ σ' e h := by
    refine vmt_tl σ σ' ?_ h
    unfold vw at e; simp only [Prod.mk.injEq] at e
    unfold tl; rw [e.1, e.2.1]
  uts σ _ x hx := by
    obtain ⟨e1, e2, -, -⟩ := uts_out hx
    refine ⟨by rw [e1, e2]; exact BitVec.le_refl _, ?_⟩
    show (x.2.machineState.lastMachineTime).toNat ≤ _
    rw [e2, gctN_toNat]; exact gctN_le _
  sis st i := by
    refine ik_of_tl vmt_tl ?_
    unfold setIrqState
    exact dk_bind (dk_modify fun _ => rfl) fun _ => fk_tl_dmo (mask_lmt _ i)
  msk mop h := ik_of_tl vmt_tl (fk_tl_dmo fun ms x hx => (h ms x hx).1)
  ack i := ik_of_tl vmt_tl (fk_tl_dmo (mask_lmt false i))
  fpu := hF

/-- The reduction at the syscall entry (see `wl_vmt_of`: `hF` is false today). -/
theorem kentry_vmt_of (hF : IK ValidMachineTime fpuStep) (c : Syscall) {σ : State Unit}
    (h : ValidMachineTime σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, ValidMachineTime y.2 :=
  gk_fl4KernelEntrySyscall true c _ (wl_vmt_of hF) σ h

/-- **`ValidMachineTime` at boot** (`initASt`: both times 0). -/
theorem boot_vmt : ValidMachineTime (initASt (Z := Unit)) :=
  ⟨BitVec.le_refl _, by show (0 : Nat) ≤ _; exact Nat.zero_le _⟩

end

end Fl4Proofs.P3.SInvV
