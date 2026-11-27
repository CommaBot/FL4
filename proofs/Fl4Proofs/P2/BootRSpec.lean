/-
# P2 (line p3mc, gen 39): the second boot start `σR` — `σB` with a running root thread (handoff §43b)

Gen 37 proved `NonIdle` false at the boot state `σB` (its current thread is the idle thread), so no vmF / vmR / sl
start (the only carriers of V13's `ybw` [J]) holds there. §43b's plan: **a second P3 start by `JReachU3.start`**,
`σB` plus one running root thread `tRp` that is the current thread, bound to a second scheduling context `scRp`.

`σR` is `σB` (P2/BootSpec, l4v `Init_A.X64_A.init_A_st` with the IRQ node relocated) with
* the root TCB at `tRp = kernelBase + 0x2000` (free since `σB` moved the IRQ node to `kbB + 1248`):
  state `Running`, bound to `scRp`, priority / domain / MCP 0, no fault, no bound notification, no yield, IPC
  buffer 0, `initArchTcb`; **its CSpace-root slot holds `threadCap tRp`**, every other slot the null cap;
* the root SC at `scRp = kernelBase + 0x3000`: the idle SC's record (l4v `Init_A`'s idle SC, MCS) with
  `scTcb = some tRp` (refills `[(0, MAX_PERIOD), (MAX_PERIOD, 0)]`, budget `MAX_PERIOD`, `MIN_REFILLS`, round
  robin), size bits 0 as the idle SC's;
* `curThread = tRp`, `curSc = scRp`; `isOriginalCap` the slots holding a non-null cap (`iocR`, as `iocB`);
  every other field `σB`'s (`idleThread` / `idleSc` the idle objects, empty queues, action `resumeCurThread`).

**Why one cap** (not the "null caps allowed" of §43b): P3's spec invariant `SInvA.live` (`IfLiveT`, l4v
`if_live_then_nonz_cap` at TCBs) asks a live thread (state `Running`) to be named by a thread cap in some slot. The
thread cap sits in the thread's own CSpace-root slot: no spec invariant restricts that slot's cap kind (only
`CnDom` for CNode caps, `VfhAll` for the fault handler), `SpecGlobS.irq` forbids it in an IRQ slot, and on FL4's
side `LiveJ.slots` is then met by the cap itself (an in-use slot of `tRp` named by a `Thread tRp` cap of the MDB).

Proved here: the addresses (`tRp_eq`, `scRp_eq`, `tRp_val`-style numbers), `kheapR`'s lookups (`kheapR_tR`,
`kheapR_scR`, `kheapR_of_ne`, **`kheapR_cases`**), **`capOpt_R`** (the one non-null cap of `σR`),
`iocR_iff` (the original slot), `σR`'s fields.

No premise. No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.BootZCheap
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.BootSt
open Fl4Spec Classical

noncomputable section

/-- The root TCB: `kernelBase + 0x2000`. -/
def tRp : ObjRef := BitVec.ofNat 64 18446744071562076160

/-- The root SC: `kernelBase + 0x3000`. -/
def scRp : ObjRef := BitVec.ofNat 64 18446744071562080256

theorem tRp_eq : tRp = kernelBase + 0x2000 := by decide
theorem scRp_eq : scRp = kernelBase + 0x3000 := by decide
theorem tRp_toNat : tRp.toNat = 18446744071562076160 := by decide
theorem scRp_toNat : scRp.toNat = 18446744071562080256 := by decide

/-- The root thread's TCB record (module docstring). -/
def tcbR : Tcb :=
  { tcbCtable := .threadCap tRp,
    tcbVtable := .nullCap,
    tcbIpcframe := .nullCap,
    tcbFaultHandler := .nullCap,
    tcbTimeoutHandler := .nullCap,
    tcbEpt := .nullCap,
    tcbState := .running,
    tcbIpcBuffer := 0,
    tcbFault := none,
    tcbBoundNotification := none,
    tcbMcpriority := 0,
    tcbSchedContext := some scRp,
    tcbYieldTo := none,
    tcbPriority := 0,
    tcbDomain := defaultDomain,
    tcbFlags := ∅,
    tcbArch := initArchTcb }

/-- The root SC's record: the idle SC's with `scTcb = some tRp`. -/
def scR : SchedContext :=
  { defaultSchedContext with
    scTcb := some tRp,
    scRefills := [{ rTime := 0, rAmount := MAX_PERIOD }, { rTime := MAX_PERIOD, rAmount := 0 }],
    scBudget := MAX_PERIOD,
    scRefillMax := MIN_REFILLS }

/-- `kheapB` with the root TCB and the root SC. -/
def kheapR : KHeap :=
  Function.update (Function.update kheapB tRp (some (.tcb tcbR))) scRp (some (.schedContext scR 0))

/-- The original slots: those holding a non-null cap (`iocB`'s definition over `kheapR`). -/
def iocR : CslotPtr → Bool := fun (a, b) =>
  decide (∃ obj, kheapR a = some obj ∧ (∃ cap, capOf obj b = some cap ∧ ¬cap = .nullCap))

/-- **The second boot start** (module docstring): `σB` with the root thread current. -/
def σR {Z : Type} [StateExt Z] : State Z :=
  { (σB (Z := Z)) with
    kheap := kheapR,
    isOriginalCap := iocR,
    curThread := tRp,
    curSc := scRp }

/-! ## Distinctness -/

theorem tRp_ne_idle : tRp ≠ idleThreadPtr := by decide
theorem scRp_ne_idle : scRp ≠ idleScPtr := by decide
theorem tRp_ne_scRp : tRp ≠ scRp := by decide
theorem scRp_ne_tRp : scRp ≠ tRp := by decide

/-- `kheapB` has nothing at the root TCB's or the root SC's address. -/
theorem kheapB_tRp : kheapB tRp = none := by
  unfold kheapB
  simp only [Function.update_apply]
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide)]
  rw [if_neg]
  rintro ⟨irq, hi, he⟩
  have h1 := congrArg BitVec.toNat he
  rw [tRp_toNat] at h1
  have := irq.isLt
  simp only [irqNodeB, ucast, cteLevelBits, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq] at h1
  omega

theorem kheapB_scRp : kheapB scRp = none := by
  unfold kheapB
  simp only [Function.update_apply]
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide)]
  rw [if_neg]
  rintro ⟨irq, hi, he⟩
  have h1 := congrArg BitVec.toNat he
  rw [scRp_toNat] at h1
  have := irq.isLt
  simp only [irqNodeB, ucast, cteLevelBits, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq] at h1
  omega

/-! ## `kheapR` lookups -/

theorem kheapR_tR : kheapR tRp = some (.tcb tcbR) := by
  unfold kheapR
  rw [Function.update_of_ne tRp_ne_scRp, Function.update_self]

theorem kheapR_scR : kheapR scRp = some (.schedContext scR 0) := by
  unfold kheapR
  rw [Function.update_self]

theorem kheapR_of_ne {p : ObjRef} (h1 : p ≠ tRp) (h2 : p ≠ scRp) : kheapR p = kheapB p := by
  unfold kheapR
  rw [Function.update_of_ne h2, Function.update_of_ne h1]

/-- **The objects of `σR`**: the root TCB, the root SC, or one of `σB`'s. -/
theorem kheapR_cases {o : ObjRef} {ko : KernelObject} (h : kheapR o = some ko) :
    (o = tRp ∧ ko = .tcb tcbR) ∨ (o = scRp ∧ ko = .schedContext scR 0) ∨
      (o ≠ tRp ∧ o ≠ scRp ∧ kheapB o = some ko) := by
  by_cases e1 : o = tRp
  · subst e1; rw [kheapR_tR] at h; cases h; exact Or.inl ⟨rfl, rfl⟩
  by_cases e2 : o = scRp
  · subst e2; rw [kheapR_scR] at h; cases h; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  rw [kheapR_of_ne e1 e2] at h
  exact Or.inr (Or.inr ⟨e1, e2, h⟩)

/-! ## `σR`'s fields -/

theorem σR_kheap : (σR (Z := Unit)).kheap = kheapR := rfl
theorem σR_cur : (σR (Z := Unit)).curThread = tRp := rfl
theorem σR_curSc : (σR (Z := Unit)).curSc = scRp := rfl
theorem σR_idle : (σR (Z := Unit)).idleThread = idleThreadPtr := rfl
theorem σR_idleSc : (σR (Z := Unit)).idleSc = idleScPtr := rfl
theorem σR_cur_ne : (σR (Z := Unit)).curThread ≠ (σR (Z := Unit)).idleThread := tRp_ne_idle

/-! ## The caps -/

/-- The root TCB's slots: the CSpace-root slot holds `threadCap tRp`, every other cap is the null cap. -/
theorem tcbR_map_some {c : CnodeIndex} {cap : Cap} (h : tcbCnodeMap tcbR c = some cap) :
    cap = .nullCap ∨ (c = tcbCnodeIndex 0 ∧ cap = .threadCap tRp) := by
  unfold tcbCnodeMap at h
  simp only [Function.update_apply] at h
  split_ifs at h <;> cases h
  all_goals first | exact Or.inl rfl | exact Or.inr ⟨by assumption, rfl⟩

theorem tcbR_root : tcbCnodeMap tcbR (tcbCnodeIndex 0) = some (.threadCap tRp) := by
  simp only [tcbCnodeMap, Function.update_apply]
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_pos trivial]
  rfl

/-- `capOpt` at an object is its `capView`. -/
theorem capOpt_some (o : KernelObject) (c : CnodeIndex) :
    Fl4Proofs.P3.capOpt (some o) c = Fl4Proofs.P3.SInvU.capView o c := by
  cases o with
  | cnode n cs =>
    simp only [Fl4Proofs.P3.capOpt, Fl4Proofs.P3.SInvU.capView]
    split_ifs <;> rfl
  | _ => rfl

/-- **The one non-null cap of `σR`** (by object): every cap of `kheapR` is the null cap except `threadCap tRp` in
the root thread's CSpace-root slot. -/
theorem capView_R {p : ObjRef} {o : KernelObject} (hp : kheapR p = some o) {c : CnodeIndex} {cap : Cap}
    (h : Fl4Proofs.P3.SInvU.capView o c = some cap) :
    cap = .nullCap ∨ (p = tRp ∧ c = tcbCnodeIndex 0 ∧ cap = .threadCap tRp) := by
  rcases kheapR_cases hp with ⟨e, he⟩ | ⟨e, he⟩ | ⟨e1, e2, he⟩
  · subst e he
    simp only [Fl4Proofs.P3.SInvU.capView] at h
    rcases tcbR_map_some h with e | ⟨e1, e2⟩
    · exact Or.inl e
    · exact Or.inr ⟨rfl, e1, e2⟩
  · subst e he
    simp [Fl4Proofs.P3.SInvU.capView] at h
  · exact Or.inl (Fl4Proofs.P3.SInvU.init_cv_B he h)

/-- **The one non-null cap of `σR`** (`capOpt` form). -/
theorem capOpt_R {p : ObjRef} {c : CnodeIndex} {cap : Cap} (h : Fl4Proofs.P3.capOpt (kheapR p) c = some cap) :
    cap = .nullCap ∨ (p = tRp ∧ c = tcbCnodeIndex 0 ∧ cap = .threadCap tRp) := by
  cases hp : kheapR p with
  | none => rw [hp] at h; cases h
  | some o => rw [hp, capOpt_some] at h; exact capView_R hp h

/-- **The one non-null cap of `σR`** (`capAt` form). -/
theorem capAt_R {sl : CslotPtr} {cap : Cap} (h : Fl4Proofs.P3.SInvU.capAt (σR (Z := Unit)) sl = some cap) :
    cap = .nullCap ∨ (sl = (tRp, tcbCnodeIndex 0) ∧ cap = .threadCap tRp) := by
  obtain ⟨p, i⟩ := sl
  unfold Fl4Proofs.P3.SInvU.capAt at h
  split at h
  · rename_i o ho
    rcases capView_R ho h with e | ⟨e1, e2, e3⟩
    · exact Or.inl e
    · subst e1 e2; exact Or.inr ⟨rfl, e3⟩
  · cases h

/-- The root thread's CSpace-root slot. -/
theorem capAt_R_root : Fl4Proofs.P3.SInvU.capAt (σR (Z := Unit)) (tRp, tcbCnodeIndex 0) = some (.threadCap tRp) := by
  show (match kheapR tRp with | some o => Fl4Proofs.P3.SInvU.capView o _ | none => none) = _
  rw [kheapR_tR]
  exact tcbR_root

/-- **The original slots of `σR`**: exactly the root thread's CSpace-root slot. -/
theorem iocR_iff (sl : CslotPtr) : (σR (Z := Unit)).isOriginalCap sl = true ↔ sl = (tRp, tcbCnodeIndex 0) := by
  obtain ⟨a, b⟩ := sl
  show iocR (a, b) = true ↔ _
  unfold iocR
  rw [decide_eq_true_iff]
  constructor
  · rintro ⟨o, ho, c, hc, hn⟩
    have hv : Fl4Proofs.P3.SInvU.capView o b = some c := by
      cases o with
      | cnode n cs =>
        rcases kheapR_cases ho with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, -, he⟩
        · cases e
        · cases e
        · rcases kheapB_cases he with ⟨-, _, e⟩ | ⟨-, _, _, e⟩ | ⟨-, _, e⟩ | ⟨-, e⟩
          · cases e
          · cases e
          · cases e
          · cases e
            simp only [Fl4Proofs.P3.SInvU.capView]
            rw [if_pos (by unfold wellFormedCnodeN emptyCnode dom; ext x; simp)]
            exact hc
      | tcb t => exact hc
      | _ => simp [Fl4Spec.capOf] at hc
    rcases capView_R ho hv with e | ⟨e1, e2, -⟩
    · exact absurd e hn
    · rw [e1, e2]
  · rintro h
    cases h
    refine ⟨_, kheapR_tR, .threadCap tRp, ?_, by intro h; cases h⟩
    exact tcbR_root

end

end Fl4Proofs.P2.BootSt
