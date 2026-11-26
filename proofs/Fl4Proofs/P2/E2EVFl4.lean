/-
P2 (line vlift, gen 5): **FL4's concrete local-path family under rule 7, and the end-to-end theorem over it**.

`fl4Loc LQ : Fl4Loc …` (shape: `P2/E2EVFam.lean`) fills every slot with the latest path on `int/j13`:

| slot | path (at) | index (the glue's choice) | lift |
|---|---|---|---|
| `vmF` VM fault | `vm_localPathG` (hpzg: program discharged) at `userV K` | `VmFArg`: `addr code`, P1 sets, `Locks` | U, `NoVcpuRW` proved (`vmFSlot.W`: `IoRS` / `IoWS` / `VmBase.dsSafe`) |
| `vmR` VM ReplyRecv | `rr_localPath` at `userV K` | `VmRArg`: `rptr ep`, P1 sets, `Locks` | U, proved (`rr_noVcpuRW`) |
| `io` I/O port | `io_localPathV` = `io_localPathK` (`ioBodyP`) at `userV K`, `Pre := SlJAt K ∧ Q` | `IoArg`: `number`, sets, `Locks`, `Q` | U, proved (`io_noVcpuRWV`) |
| `st` `TCB_SetTimer` | `tm_localPathV` = `set_timer_localPathM` at `userV K` narrowed to `SlJAt K ∧ Q` | `StArg`: `n target`, sets, `lk`, `Q` | U, proved (`tm_noVcpuRWV`) |
| `irq` timer interrupt | `irq_localPathV` (p2lf gen17's `irq_localPathJ3` at `userV K`, `Pre := SlJAt K ∧` memory) | `IrqArg`: `irq pl lk p` | U, proved (`irq_noVcpuRWV`) |
| `sl` syscall_local | `sl_pathsKC` (canonical `SlQ`) at `K` | `SlArg`: `n found`, sets, `Locks` | C, `AvoidV` proved (`sl_avoidVK`) |
| `vq` | `LQ : PathsV ν`, stated for `ownV` (lvm: `vexit_localPath` / `vexit_localPathP`; `vtimer_localPath` from par/lvm4) | `ν` | none needed |

Each route-U / route-C slot is conditional (`SlotU` / `SlotC`): its path is present at `(K, m)` exactly where its
premise record (`VmFPrem` … `SlPrem`) holds, and is the empty path elsewhere, so the records are asked only where the
glue starts the path (`SlotU.startAt` / `SlotC.startAt`).

**`serializable_fl4_local`**: every `ExecV` of FL4 (core steps and hardware VCPU writes) whose local runs are starts
of `fl4Loc LQ`'s paths, and which reaches a state with no local path in progress, is serializable (`RunAll`).

## Premise table

Global (once, for the kernel's one store `st` and Arch instance `ar`):
* `hA : ArchTotal ar` — proved for FL4's Arch model by P0 (totality); a parameter here.
* `hSt : StoreTotal st` — likewise (syscall_local's body).
* `hm` [P] `MasksWr st`: a memory write keeps the frame masks (fl4-sync's store).
* `a0 : A` — any Arch state (syscall_local's construction).

Of the execution (`serializable_e2eV`'s):
* `Init s0`, `ArmInv s0`, `MapsV K0 s0` — the initial configuration (proved shapes, given at boot).
* `RegionOKV K0`, `UserOKV K0` [J] — the boot layout's words lie as P1's typed heap says.
* `ExecV`'s `Fl4StepV` per core step: `arm` [P] (armed programs are pure glue), **`start` [P]** (a body the glue
  starts is a start of some slot's path, `StartAt`; for a slot this asks its premise record at the current layout
  and memory, and the path's `Pre` at the start state), `ser` [J] (a serial entry leaves a layout satisfying
  `RegionOKV` / `UserOKV` with ghost maps `ownV`'s), `keep`.
* `HwStepV` [P] per hardware step: the hardware writes only a running VCPU's words `VmRunFrame` allows, while
  `lock v` is free.
* `NoLoc s` at the end state.

Per slot, the premise record (asked at the `(K, m)` of each start):
* All U slots at `userV K` (`P2/E2EVUser.lean`): their obligations are about `userV K`'s user words
  (`K.user` plus the VCPU data words).
* `VFacts` [J] (`io`, `st`, `irq`, `sl`; `P2/E2EVFl4U.lean`): `VcpuHeap` [J] (`K.vcpus` free in P3), `VcpuTabOff`
  [J] (needs "every heap object lies in an untyped"), `UserObj` [J], `PoolObj` [J] (at bundle states), `wr` [J]
  (a VCPU-data-word write keeps P3's bundle `SlJAt`, as slhuf's `SlJAt.userWr` for user words).
* `vmF` (`VmFPrem`): `lay` [J] `IoLayA` (alignment facts of the layout), `mA` [J] (`ko`'s memory agrees on TCB
  affinity words at `VmPre` states), `uf` [J] (`VmPre` / locks / sets kept by user writes), `ro` [W] (declining
  `ReadOnce` of the generated tree). Start: `VmPre (userV K)` from `VmPre K` by `vmPre_userV` (`VcpuKs`, `TabNoV`).
* `vmR` (`VmRPrem`): `lay` [J], `mA` [J], `uf` [J], `pz` ([P] `IsProg`, [W] `NoZero`, [W] declining `ReadOnce`).
  Start: `vmRRPre_userV`.
* `io` (`IoPrem`): `vf` [J], `pe` (`IoPre` at bundle states: [J] P1 facts + fl4-sync contract), `mA` [J], `uf` [J]
  (`Q`, locks, sets kept by `userV K` user writes; the bundle part is derived), `pz` ([P] `IsProg` of `ioBodyP`, [W]
  `NoZero`, [W] declining `ReadOnce`). Start: `SlJAt K σ ∧ Q K m σ`.
* `st` (`StPrem`): `vf` [J], `pe` (`StEntK` at bundle states, [J]), `pz` ([P] `IsProg`, [W] `NoZero`, [W]
  `ReadOnce`), `eu` [J] (`StEnt` kept by user writes), `lk` [P] (locks kept by user writes), `nu` [J] (the node
  words are not user words), `uf` [J] (`Q` kept). Start: `SlJAt K σ ∧ Q K m σ`.
* `irq` (`IrqPrem`): `vf` [J], `lt` (`irq < 128`; the timer IRQ is 2), `hp` [P] (`IsProg`), `hz` [W] (`NoZero`),
  `ro` [W] (`ReadOnce` under `IrqPreV`), `lk` [P] (guarded lock contract), `pl` [P] (`PlanLk`). Start:
  `SlJAt K σ` and the memory agreement off `userV K`'s user words.
* `sl` (`SlPrem`): `vf` [J]; `sl_pathsKC`'s `hPBw` [J], `hArw` [P], `hlk` [P], `hpz` ([P] `IsProg`, [W] `NoZero`,
  [W] `ReadOnce`). Start: `SlJAt K σ ∧ SlQ … K m σ` (`SlPreB`, `SlEntL` [P], `SlSyncC` [P], `SlAccR` [P]).
* `vq`: lvm's paths carry their own premises (`VexitEnt`'s fields, `vin` [J] etc.).

Swapping a newer path in (integration: slhuf's `sl_pathsKC3`, hpzg's G2 versions, lvm's `vtimer_localPath`): replace
that slot's `SlotU` / `SlotC` value in `fl4Loc` (a premise record, a path under it and its lift lemma) or pass the
lvm paths as `LQ` (`PathsV.sum` for several); `serializable_fl4_localG` is unchanged.
-/
import Fl4Proofs.P2.E2EVFl4U
import Fl4Proofs.P2.ProgGenVmLP
import Fl4Proofs.P2.SlJQ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
open Fl4Proofs.P2.OwnMap (fld oAFFINITY)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll)

noncomputable section
open Classical

/-! ## Indices: the arguments the glue picks per start -/

/-- VM fault: the fault's `addr` / `code`, P1's sets and the locks. -/
structure VmFArg (S : Type) : Type where
  addr : U64
  code : U64
  T : Set U64
  Cs : Set U64
  Ω : Set U64
  U : Set U64
  Sg : Set U64
  Rp : Set U64
  Scs : Set U64
  Nt : Set U64
  Ac : Set U64
  H : Heap
  Z : U64 → Nat
  Locks : S → U64 → Prop

/-- VM ReplyRecv: the reply and endpoint, P1's sets and the locks. -/
structure VmRArg (S : Type) : Type where
  rptr : U64
  ep : U64
  T : Set U64
  Cs : Set U64
  Ω : Set U64
  Sg : Set U64
  Rp : Set U64
  Scs : Set U64
  Nt : Set U64
  Ac : Set U64
  H : Heap
  Z : U64 → Nat
  Locks : S → U64 → Prop

/-- I/O port: the syscall number, P1's sets, the locks and the extra entry fact `Q`. -/
structure IoArg (S : Type) : Type where
  number : I64
  Cs : Set U64
  Ω : Set U64
  Sg : Set U64
  Ac : Set U64
  Locks : S → U64 → Prop
  Q : KLayoutV → (U64 → U64) → S → Prop

/-- `TCB_SetTimer`: the syscall number and target, P1's sets, the locks and `Q`. -/
structure StArg (S : Type) : Type where
  n : I64
  target : U64
  Cs : Set U64
  Ω : Set U64
  Sg : Set U64
  Ac : Set U64
  lk : S → U64 → Prop
  Q : KLayoutV → (U64 → U64) → S → Prop

/-- The timer interrupt: the IRQ, fl4-sync's plan, the locks and the body's program. -/
structure IrqArg (S : Type) : Type where
  irq : U64
  pl : localtimer.TimerIrqPlan
  lk : S → U64 → Prop
  p : SProg Bool

/-- syscall_local: the syscall number and the found capability, P1's sets and the locks. -/
structure SlArg (S : Type) : Type where
  n : I64
  found : U64 × U64
  Cs : Set U64
  Ω : Set U64
  Sg : Set U64
  Ac : Set U64
  Locks : S → U64 → Prop

section fam
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)

/-! ## Premise records (module docstring's table) -/

/-- **VM fault's premises at `(K, m)`** (`vm_localPathG`'s, at `userV K`). -/
structure VmFPrem (i : VmFArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- [J] the layout's alignment facts. -/
  lay : IoLayA (userV K)
  /-- [J] `ko`'s memory agrees on TCB affinity words. -/
  mA : ∀ s, VmPre st ar (userV K) i.T i.Cs i.Ω i.U i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.Locks s →
    ∀ d, (userV K).heap d = some .tcb → m (fld d oAFFINITY) = L.mem s (fld d oAFFINITY)
  /-- [J] `VmPre`, locks and sets kept by user writes. -/
  uf : ∀ s b v, VmPre st ar (userV K) i.T i.Cs i.Ω i.U i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.Locks s →
    b ∈ (userV K).user → Aligned b →
    VmPre st ar (userV K) i.T i.Cs i.Ω i.U i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.Locks (L.wr s b v) ∧
      i.Locks (L.wr s b v) = i.Locks s ∧
      IoRS (st := st) (userV K) i.Locks (L.wr s b v) = IoRS (st := st) (userV K) i.Locks s ∧
      IoWS (st := st) (userV K) i.Locks (L.wr s b v) = IoWS (st := st) (userV K) i.Locks s ∧
      IoDS (st := st) (L.wr s b v) = IoDS (st := st) s
  /-- [W] declining `ReadOnce` of the generated tree. -/
  ro : ∀ s s' a r, VmPre st ar (userV K) i.T i.Cs i.Ω i.U i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.Locks s →
    (∃ b, VmRep st ar s a b) →
    Alt st (IoRS (st := st) (userV K) i.Locks s) (OwnMap.cls (userV K)) (OwnMap.ko (userV K) m)
      (· ∈ (userV K).user) s s' →
    interp st ar (R.syscall.handle_vm_fault_local i.addr i.code) s' a = ok r →
    E2E.Once st ar (IoRS (st := st) (userV K) i.Locks s) (· ∈ (userV K).user) ∅ ∅
      (R.syscall.handle_vm_fault_local i.addr i.code) s' a

/-- **VM ReplyRecv's premises at `(K, m)`** (`rr_localPath`'s, at `userV K`). -/
structure VmRPrem (i : VmRArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- [J] -/
  lay : IoLayA (userV K)
  /-- [J] -/
  mA : ∀ s, VmRRPre st ar (userV K) i.T i.Cs i.Ω i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.Locks i.rptr i.ep s →
    ∀ d, (userV K).heap d = some .tcb → m (fld d oAFFINITY) = L.mem s (fld d oAFFINITY)
  /-- [J] -/
  uf : ∀ s b v, VmRRPre st ar (userV K) i.T i.Cs i.Ω i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.Locks i.rptr i.ep s →
    b ∈ (userV K).user → Aligned b →
    VmRRPre st ar (userV K) i.T i.Cs i.Ω i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.Locks i.rptr i.ep (L.wr s b v) ∧
      i.Locks (L.wr s b v) = i.Locks s ∧
      IoRS (st := st) (userV K) i.Locks (L.wr s b v) = IoRS (st := st) (userV K) i.Locks s ∧
      IoWS (st := st) (userV K) i.Locks (L.wr s b v) = IoWS (st := st) (userV K) i.Locks s ∧
      IoDS (st := st) (L.wr s b v) = IoDS (st := st) s
  /-- [P] `IsProg`, [W] `NoZero`, [W] declining `ReadOnce`. -/
  pz : ∃ p : SProg Bool, IsProg (rrBody S i.rptr i.ep) p ∧ NoZero p ∧
    ∀ s s' a r, VmRRPre st ar (userV K) i.T i.Cs i.Ω i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.Locks i.rptr i.ep s →
      (∃ b, RrRep st i.rptr s b) →
      Alt st (IoRS (st := st) (userV K) i.Locks s) (OwnMap.cls (userV K)) (OwnMap.ko (userV K) m)
        (· ∈ (userV K).user) s s' →
      interp st ar p s' a = ok r →
      E2E.Once st ar (IoRS (st := st) (userV K) i.Locks s) (· ∈ (userV K).user) ∅ ∅ p s' a

/-- **I/O port's premises at `(K, m)`** (`io_localPathV`'s). -/
structure IoPrem (i : IoArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- [J] -/
  vf : VFacts L K
  /-- `IoPre` at bundle states ([J] P1 facts, fl4-sync contract). -/
  pe : ∀ s, SlJAt (L := L) K.toKLayout s → i.Q K m s →
    IoPre st K.toKLayout K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits i.Ac s
  /-- [J] -/
  mA : ∀ s, SlJAt (L := L) K.toKLayout s → i.Q K m s → ∀ d, K.heap d = some .tcb →
    m (fld d oAFFINITY) = L.mem s (fld d oAFFINITY)
  /-- [J] -/
  uf : ∀ s b v, SlJAt (L := L) K.toKLayout s → i.Q K m s → b ∈ (userV K).user → Aligned b →
    i.Q K m (L.wr s b v) ∧ i.Locks (L.wr s b v) = i.Locks s ∧
      IoRS (st := st) (userV K) i.Locks (L.wr s b v) = IoRS (st := st) (userV K) i.Locks s ∧
      IoWS (st := st) (userV K) i.Locks (L.wr s b v) = IoWS (st := st) (userV K) i.Locks s ∧
      IoDS (st := st) (L.wr s b v) = IoDS (st := st) s
  /-- [P] `IsProg` of `ioBodyP`, [W] `NoZero`, [W] declining `ReadOnce`. -/
  pz : ∃ p : SProg Bool, IsProg (ioBodyP S i.number) p ∧ NoZero p ∧
    ∀ s s' a r, (SlJAt (L := L) K.toKLayout s ∧ i.Q K m s) →
      (¬ ∃ s1 a1, syscall.handle_ioport_local st ar s a i.number = ok (true, s1, a1)) →
      Alt st (IoRS (st := st) (userV K) i.Locks s) (OwnMap.cls (userV K)) (OwnMap.ko (userV K) m)
        (· ∈ (userV K).user) s s' →
      interp st ar p s' a = ok r →
      E2E.Once st ar (IoRS (st := st) (userV K) i.Locks s) (· ∈ (userV K).user) ∅ ∅ p s' a

/-- **`TCB_SetTimer`'s premises at `(K, m)`** (`tm_localPathV`'s). -/
structure StPrem (i : StArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- [J] -/
  vf : VFacts L K
  /-- [J] `StEntK` at bundle states. -/
  pe : ∀ s, SlJAt (L := L) K.toKLayout s → i.Q K m s →
    StEntK K.toKLayout st K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits i.Ac
      i.target m s
  /-- [P] `IsProg`, [W] `NoZero`, [W] `ReadOnce`. -/
  pz : ∃ p : SProg Bool, IsProg (stBody S i.n i.target) p ∧ NoZero p ∧
    E2E.ReadOnce st ar p (OwnMap.cls (userV K)) (OwnMap.ko (userV K) m) (· ∈ (userV K).user)
      (StEntV K st i.Cs i.Ω i.Sg i.Ac i.target m) (MaxR (userV K) st i.lk)
  /-- [J] -/
  eu : ∀ s b v, StEnt (userV K) st K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns
      K.heap.scBits i.Ac i.target s → b ∈ (userV K).user → Aligned b →
    StEnt (userV K) st K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits i.Ac
      i.target (L.wr s b v)
  /-- [P] -/
  lk : ∀ s b v, b ∈ (userV K).user → i.lk (L.wr s b v) = i.lk s
  /-- [J] -/
  nu : ∀ s, StEnt (userV K) st K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns
      K.heap.scBits i.Ac i.target s → ∀ o : U64, o.val < 4288 → L.nodeAt s (L.cpu s) o ∉ (userV K).user
  /-- [J] -/
  uf : ∀ s b v, SlJAt (L := L) K.toKLayout s → i.Q K m s → b ∈ (userV K).user → Aligned b → i.Q K m (L.wr s b v)

/-- **The timer interrupt's premises at `(K, m)`** (`irq_localPathV`'s). -/
structure IrqPrem (i : IrqArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- [J] -/
  vf : VFacts L K
  /-- The IRQ's state word lies in the kernel-state block (the timer IRQ is 2). -/
  lt : i.irq.val < 128
  /-- [P] -/
  hp : IsProg (irqBody S i.irq i.pl) i.p
  /-- [W] -/
  hz : NoZero i.p
  /-- [W] -/
  ro : E2E.ReadOnce st ar i.p (OwnMap.cls (userV K)) (OwnMap.ko (userV K) m) (· ∈ (userV K).user)
    (IrqPreV K st m) (MaxR (userV K) st i.lk)
  /-- [P] -/
  lk : ∀ s b v, SlJAt (L := L) K.toKLayout s → b ∈ (userV K).user → Aligned b → i.lk (L.wr s b v) = i.lk s
  /-- [P] -/
  pl : PlanLk i.lk i.pl

/-- **syscall_local's premises** (`VFacts` at `K`; `sl_pathsKC`'s own, which are stated for every layout). -/
structure SlPrem (i : SlArg S) (K : KLayoutV) : Prop where
  /-- [J] -/
  vf : VFacts L K
  /-- [J] -/
  PBw : ∀ K m s b v, SlJAt (L := L) K s →
    SlPreB (st := st) ar K i.Locks m i.n i.found K.heap.tcbs i.Cs i.Ω K.user i.Sg K.heap.replies
      K.heap.scs K.heap.ntfns i.Ac K.heap K.heap.scBits s → b ∈ K.user → Aligned b →
    SlPreB (st := st) ar K i.Locks m i.n i.found K.heap.tcbs i.Cs i.Ω K.user i.Sg K.heap.replies
      K.heap.scs K.heap.ntfns i.Ac K.heap K.heap.scBits (L.wr s b v)
  /-- [P] -/
  Arw : ∀ K s b v, SlJAt (L := L) K s → SlAccR (st := st) ar K i.Locks i.found s → b ∈ K.user →
    Aligned b → SlAccR (st := st) ar K i.Locks i.found (L.wr s b v)
  /-- [P] -/
  lk : ∀ K s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → i.Locks (L.wr s b v) = i.Locks s
  /-- [P] `IsProg`, [W] `NoZero`, [W] `ReadOnce`. -/
  pz : ∀ K m, ∃ p : SProg Bool, IsProg (slBody S i.n i.found) p ∧ NoZero p ∧
    E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user)
      (fun s => SlJAt (L := L) K s ∧ Fl4Proofs.P2.PathObl.SlQ st ar i.Locks i.n i.found
        i.Cs i.Ω i.Sg i.Ac K m s)
      (SlRS (st := st) K i.Locks)

/-! ## The slots -/

variable (hA : P0.ArchTotal ar) (hSt : P0.StoreTotal st) (hm : E2E.MasksWr st) (a0 : A)

/-- **VM fault slot.** -/
def vmFSlot : SlotU (VmFArg S) where
  Prem i K m := VmFPrem st ar i K m
  path i K m hK hU h :=
    vm_localPathG (T := i.T) (Cs := i.Cs) (Ω := i.Ω) (U := i.U) (H := i.H) (Sg := i.Sg) (Rp := i.Rp)
      (Scs := i.Scs) (Nt := i.Nt) (Z := i.Z) (Ac := i.Ac) (Locks := i.Locks) (m0 := m)
      ar hA (regionOK_userV hK) (userOK_userV hK hU) h.lay (addr := i.addr) (code := i.code) hm h.mA h.uf h.ro
  W i K m hK hU h :=
    { rd := fun _ _ _ hr => ioRS_noV hr
      wr := fun s _ hp hw => hw.elim (ioWS_noV hK) fun hd =>
        Or.inl (safeW_noV hK (VmBase.dsSafe (show VmPre st ar (userV K) i.T i.Cs i.Ω i.U i.H i.Sg i.Rp i.Scs i.Nt
          i.Z i.Ac i.Locks s from hp).1.base hd).2) }

/-- **VM ReplyRecv slot.** -/
def vmRSlot : SlotU (VmRArg S) where
  Prem i K m := VmRPrem st ar i K m
  path i K m hK hU h :=
    rr_localPath (T := i.T) (Cs := i.Cs) (Ω := i.Ω) (H := i.H) (Sg := i.Sg) (Rp := i.Rp)
      (Scs := i.Scs) (Nt := i.Nt) (Z := i.Z) (Ac := i.Ac) (Locks := i.Locks) (m0 := m)
      ar hA (regionOK_userV hK) (userOK_userV hK hU) h.lay (rptr := i.rptr) (ep := i.ep) hm h.mA h.uf h.pz
  W i K m hK hU h :=
    rr_noVcpuRW ar hK hA (regionOK_userV hK) (userOK_userV hK hU) h.lay hm h.mA h.uf h.pz

/-- **I/O port slot.** -/
def ioSlot : SlotU (IoArg S) where
  Prem i K m := IoPrem st ar i K m
  path i K m hK hU h :=
    io_localPathV (Cs := i.Cs) (Ω := i.Ω) (Sg := i.Sg) (Ac := i.Ac) (m0 := m) (Locks := i.Locks) ar hA hK hU h.vf
      (number := i.number) hm (i.Q K m) h.pe h.mA h.uf h.pz
  W i K m hK hU h := io_noVcpuRWV ar hA hK hU h.vf hm (i.Q K m) h.pe h.mA h.uf h.pz

/-- **`TCB_SetTimer` slot.** -/
def stSlot : SlotU (StArg S) where
  Prem i K m := StPrem st ar i K m
  path i K m hK hU h :=
    tm_localPathV (Cs := i.Cs) (Ω := i.Ω) (Sg := i.Sg) (Ac := i.Ac) (lk := i.lk) (m := m) ar hA i.n i.target hK hU
      h.vf hm (i.Q K m) h.pe h.pz h.eu h.lk h.nu h.uf
  W i K m hK hU h := tm_noVcpuRWV ar hA i.n i.target hK hU h.vf hm (i.Q K m) h.pe h.pz h.eu h.lk h.nu h.uf

/-- **Timer interrupt slot.** -/
def irqSlot : SlotU (IrqArg S) where
  Prem i K m := IrqPrem st ar i K m
  path i K m hK hU h := irq_localPathV (m := m) ar hA hK hU h.vf h.lt h.hp h.hz hm h.ro h.lk h.pl
  W i K m hK hU h := irq_noVcpuRWV ar hA hK hU h.vf h.lt h.hp h.hz hm h.ro h.lk h.pl

/-- **syscall_local slot** (route C). -/
def slSlot : SlotC (SlArg S) where
  Prem i K _ := SlPrem st ar i K
  path i K m hK hU h :=
    sl_pathsKC (Locks := i.Locks) (n := i.n) (found := i.found) (Cs := i.Cs) (Ω := i.Ω) (Sg := i.Sg) (Ac := i.Ac)
      ar hSt hA hm a0 h.PBw h.Arw h.lk h.pz () K.toKLayout m hK.base hU.base
  Av i K m hK hU h := by
    unfold sl_pathsKC sl_pathsKF sl_pathsKU sl_pathsK
    exact sl_avoidVK ar hSt hA hm a0 hK hU.base (fun _ h' => h'.1) _ _ _ _ _ _ h.vf.heap h.vf.tab
      (fun s h' => h.vf.pool s h'.1) h.vf.user

/-- The empty path's store and Arch instance: FL4's own. -/
def fl4Dflt : Dflt := { S := S, A := A, st := st, L := L, ar := ar, masks := hm }

/-- **FL4's local-path family** (module docstring's table), with `LQ` the `ownV`-native paths. -/
def fl4Loc {ν : Type} (LQ : PathsV ν) :
    Fl4Loc (VmFArg S) (VmRArg S) (IoArg S) (StArg S) (IrqArg S) (SlArg S) ν where
  vmF := vmFSlot st ar hA hm
  vmR := vmRSlot st ar hA hm
  io := ioSlot st ar hA hm
  st := stSlot st ar hA hm
  irq := irqSlot st ar hA hm
  sl := slSlot st ar hA hSt hm a0
  vq := LQ

/-- **FL4 end to end with rule 7 over its concrete local-path family** (module docstring; premise table there):
every execution of FL4 whose local runs are starts of `fl4Loc LQ`'s paths (and whose hardware steps write only
running VCPUs' words), at a state with no local path in progress, ran exactly as some serial order of its completed
entries. -/
theorem serializable_fl4_local {ν : Type} (LQ : PathsV ν) {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutV}
    (h0 : Init s0) (hA0 : ArmInv s0) (hK0 : RegionOKV K0) (hU0 : UserOKV K0) (hM0 : MapsV K0 s0)
    (h : ExecV ((fl4Loc st ar hA hSt hm a0 LQ).paths (fl4Dflt st ar hm)) s0 K0 s K) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_fl4_localG _ _ h0 hA0 hK0 hU0 hM0 h hq

end fam

end
end Fl4Proofs.P2.E2EV
