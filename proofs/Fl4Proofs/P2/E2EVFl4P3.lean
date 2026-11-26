/-
P2 (line vlift, gen 8): **the end-to-end theorem at P3's scope (`K.vcpus = ∅`), and its `JVmL` form**.

`P2/E2EVFl4W.lean`'s `fl4LocW` asks `VFacts L K` [J] (six VM-layout facts: `VcpuHeap`, `VcpuTabOff`, `UserObj`,
`PoolObj`, `VcpuSpec`, `VcpuKsOff`) in the premise records of its `io`, `st`, `irq` and `sl` slots. Gen 7
(`P2/E2EVJVm.lean`) derived the whole record from one [J] `JVmL L K` and one bundle state (`VFacts.ofJVm`), and
`JVmL` holds outright when the layout has no VCPU (`jvmL_empty`). This module turns both into families and theorems:

* **`SlotU.ofJ` / `SlotC.ofJ`**: a slot whose premise record is `VFacts L K` plus a base record `R` that carries a
  bundle state of the layout; the new record is `JVmL L K ∧ R`. **`SlotU.ofP3` / `SlotC.ofP3`**: the new record is
  `K.vcpus = ∅ ∧ R` (`VFacts.ofEmpty`). Both are `SlotU.pull` / `SlotC.pull`, so the paths and lift lemmas are the
  old slots'. They are generic in the slot, so any later family on `fl4LocW`'s pattern (e.g. a newer `io` / `st` /
  `irq` record) is wrapped the same way: give its record without `vf` and the map back.
* Base records (each = the `fl4LocW` record without `vf`): **`IoPremB`** (`IoPrem` minus `vf`; its `bun` was there
  already), **`StPremB`**, **`IrqPremB`**, **`SlPremB`** (`StPremK` / `IrqPremK` / `SlPremK` minus `vf`, plus
  **`bun`**: some bundle state of `K.toKLayout`; no premise, the slot's start state is one, since each of these
  paths' `Pre` is `SlJAt K.toKLayout ∧ …`).
* **`fl4LocJ`** / **`serializable_fl4_localJ`**: `fl4LocW` with those four slots wrapped by `ofJ` (`VFacts` [J] →
  `JVmL` [J]): the form kept for the VT-x extension, where `JVm` at a nonempty `K.vcpus` is the placement half of a
  VT-x joint invariant.
* **`fl4LocP3`** / **`serializable_fl4_localP3`**: the same with `ofP3`: **no VM-layout [J] left**. The glue picks
  `K.vcpus := ∅` at the layouts where it starts these paths (`Fl4StepV.start` [P] asks `K.vcpus = ∅` there).

**Scope, stated honestly.** At every P3 state (`SlJAt`, i.e. `JAtZ`) no TCB is bound to a VCPU (`JExt.vw`,
`JAtZ.curVcpu0`), so the current thread's bound VCPU `vOf st s` is 0 (`vOf_zero`), and both VM paths of `vq`
(`local_vm_exit`, `local_vm_timer_irq`) never accept at a P3 state (their bodies check the exiting VCPU against
`vcpu.bound` of the current thread). With `K.vcpus = ∅` the hardware steps (`HwStepV`: only a running VCPU's words)
have nothing to write either. So in `serializable_fl4_localP3` **the VM paths are vacuous**: their slots stay in the
family (statement unchanged), but every start the glue can make of them at a P3 state is a start of a path that
declines. A non-vacuous statement about VT-x executions needs P3 over VT-x states, i.e. a VT-x joint invariant
(`JVm` at a nonempty `K.vcpus` is its layout half); `serializable_fl4_localJ` is the form for that.

Start-side adapters at `K.vcpus = ∅` (for the glue's `Fl4StepV.start`):
* `userV_empty`: `userV K = K.toKLayout` (no VCPU data words); `vmPre_userV_empty` / `vmRRPre_userV_empty`: the
  `vmF` / `vmR` starts (`VcpuKs`, `TabNoV` trivial).
* lvm's `vin` / `hvK` / `vlk` (decision (2) of gen 7, the vx slot side): **`bound_ne0`** (at a bundle, a `v` that is
  the bound VCPU `vOf st s` is 0, so any `v ≠ 0 → _` holds), **`vexitEnt_P3`** (lvm's `vexitEnt_of` with the glue's
  `v := vOf st s` at that start: `hV`, `hvK`, `vlk` discharged), **`vtmEnt_P3`** (lvm's `vtmEnt_of`: `VcpuHeap`,
  `VcpuTabOff`, `PoolObj` from `VFacts.ofEmpty`, and its `VexitEnt` at `vOf st s` by `vexitEnt_P3`).
  `VxArg.v` is an index of the family (fixed before the state), so "`v := vOf st s`" is the glue's choice of index
  at the start state, stated as the premise `hv : v = vOf st s` of the start lemma.

## Premise table diff vs `serializable_fl4_localW` (statement identical; only the family differs)

| slot | removed | added |
|---|---|---|
| `io` | `vf` [J] (`VFacts`: `VcpuHeap`, `VcpuTabOff`, `UserObj`, `PoolObj`, `VcpuSpec`, `VcpuKsOff`) | P3: `K.vcpus = ∅` (glue's choice of layout); J: `JVmL` [J] |
| `st` | `vf` [J] | P3: `K.vcpus = ∅`; J: `JVmL` [J]; both: `bun` (start state, no premise) |
| `irq` | `vf` [J] | as `st` |
| `sl` | `vf` [J] | as `st` |
| `vmF` / `vmR` | — (start: `VcpuKs` / `TabNoV` from `VFacts`) | start by `vmPre_userV_empty` / `vmRRPre_userV_empty` |
| `vq` (vx) | start: `VcpuHeap` [J], lvm's `hvK` / `vin` [J], `vlk` [P] | start at `v := vOf st s` (`vexitEnt_P3`) |
| `vq` (vt) | start: `VcpuHeap` / `VcpuTabOff` / `PoolObj` [J], `hvK` [J], `vlk` [P] | — (`vtmEnt_P3`) |

All other premises are `serializable_fl4_localW`'s (`P2/E2EVFl4.lean` / `P2/E2EVFl4W.lean` docstrings).
-/
import Fl4Proofs.P2.E2EVFl4W
import Fl4Proofs.P2.E2EVJVm
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
open Fl4Proofs.P2.OwnMap (fld oAFFINITY region TcbSlot)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll)

noncomputable section
open Classical

/-! ## No VCPU in the layout -/

section empty
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {K : KLayoutV}

theorem not_inVcpu_empty (h : K.vcpus = ∅) {v b : U64} : ¬ InVcpu K v b := fun hv => by
  have h1 : v ∈ K.vcpus := hv.1
  rw [h] at h1
  simp at h1

theorem not_vData_empty (h : K.vcpus = ∅) {x : U64} : ¬ VData K x :=
  fun ⟨_, hv, _⟩ => not_inVcpu_empty h hv

/-- With no VCPU, `userV K` is the base layout. -/
theorem userV_empty (h : K.vcpus = ∅) : userV K = K.toKLayout := by
  have hU : {x | x ∈ K.user ∨ VData K x} = K.toKLayout.user :=
    Set.ext fun _ => ⟨fun hx => hx.resolve_right (not_vData_empty h), Or.inl⟩
  unfold userV
  rw [hU]

theorem vcpuHeap_empty (h : K.vcpus = ∅) : VcpuHeap K := fun v hv => by
  rw [h] at hv
  simp at hv

theorem vcpuKs_empty (h : K.vcpus = ∅) : VcpuKs K := fun _ _ hv => absurd hv (not_inVcpu_empty h)

theorem tabNoV_empty (h : K.vcpus = ∅) {s : S} : TabNoV (L := L) K s :=
  fun _ _ => ⟨not_vData_empty h, fun _ _ _ => not_vData_empty h⟩

/-- **`VFacts` with no VCPU** (`VFacts.ofJVm` at `jvmL_empty`): only a bundle state of the layout is used. -/
theorem VFacts.ofEmpty (h : K.vcpus = ∅) {s0 : S} (h0 : SlJAt (L := L) K.toKLayout s0) : VFacts L K :=
  VFacts.ofJVm (jvmL_empty h) h0

/-- **At a bundle, a `v` that is the bound VCPU is 0** (`vOf_zero`), so any `v ≠ 0 → P` holds. -/
theorem bound_ne0 {K' : OwnMap.KLayout} {s : S} (hJ : SlJAt (L := L) K' s) {v : U64} (hv : v = vOf st s)
    {P : Prop} : v ≠ 0#u64 → P :=
  fun h0 => absurd (hv.trans (vOf_zero hJ)) h0

end empty

/-! ## Start-side adapters at `K.vcpus = ∅` -/

section starts
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayoutV}
variable {Locks : S → U64 → Prop} {A : Type} {ar : machine.Arch A} {s : S}

/-- The VM-fault start (`vmF`) with no VCPU. -/
theorem vmPre_userV_empty (hK : RegionOKV K) (nv : K.vcpus = ∅)
    (h : VmPre st ar K.toKLayout T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s) :
    VmPre st ar (userV K) T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s :=
  vmPre_userV hK (vcpuKs_empty nv) (tabNoV_empty nv) h

/-- The VM-ReplyRecv start (`vmR`) with no VCPU. -/
theorem vmRRPre_userV_empty (hK : RegionOKV K) (nv : K.vcpus = ∅) {rptr ep : U64}
    (h : VmRRPre st ar K.toKLayout T Cs Ω H Sg Rp Scs Nt Z Ac Locks rptr ep s) :
    VmRRPre st ar (userV K) T Cs Ω H Sg Rp Scs Nt Z Ac Locks rptr ep s :=
  vmRRPre_userV hK (vcpuKs_empty nv) (tabNoV_empty nv) h

/-- **lvm's `VexitEnt` at a P3 start with no VCPU**, the glue's `v` being the bound VCPU (module docstring):
`vexitEnt_of` with `VcpuHeap`, `hvK` and `vlk` discharged. -/
theorem vexitEnt_P3 {lk : S → U64 → Prop} {v n : U64} (nv : K.vcpus = ∅)
    (hJ : SlJAt (L := L) K.toKLayout s) (hv : v = vOf st s)
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hL : StLay K.toKLayout st T Scs Z s)
    (ntw : ∀ p ∈ Nt, ∀ k : U64, k.val < 64 → region K.toKLayout (core.num.U64.wrapping_add p k) = .ntfn p)
    (cs : ∀ k : U64, k.val < 192 → k.val % 32 < 16 → ∃ p,
      region K.toKLayout (core.num.U64.wrapping_add (L.curW s) k) = .slot p ∧ TcbSlot K.toKLayout p ∧
        (core.num.U64.wrapping_add (L.curW s) k).val - p.val < 16)
    (aff : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t))
    (curAff : L.mem s (affA (L.curW s)) = L.cpu s) (cscCore : L.mem s (scCoreA (L.cscW s)) = L.cpu s)
    (hKH : K.heap = H) (hTs : T = H.tcbs) (hΩ : Ω = H.omega) (hScs : ∀ c ∈ Scs, H c = some (.sc (Z c)))
    (hNt : ∀ q ∈ Nt, H q = some .ntfn) :
    VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n s :=
  vexitEnt_of hI hL ntw cs aff curAff cscCore (bound_ne0 hJ hv) hJ (vcpuHeap_empty nv) hKH hTs hΩ hScs hNt
    (bound_ne0 hJ hv)

/-- **lvm's `VtmEnt` at a P3 start with no VCPU** (`vtmEnt_of`, the layout facts from `VFacts.ofEmpty`). -/
theorem vtmEnt_P3 {lk : S → U64 → Prop} {irq n : U64} (nv : K.vcpus = ∅)
    (hJ : SlJAt (L := L) K.toKLayout s)
    (hE : VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk (vOf st s) n s) (hAs : AsidOff (L := L) Ω Sg s) :
    VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s :=
  have vf := VFacts.ofEmpty nv hJ
  vtmEnt_of hE hJ vf.heap vf.tab (vf.pool s hJ) hAs

end starts

/-! ## Generic: a slot's `VFacts` replaced by `JVmL` or by `K.vcpus = ∅` -/

/-- A route-C slot under a new premise record that gives the old one. -/
def SlotC.pull {ι : Type} (X : SlotC ι) (P : ι → KLayoutV → (U64 → U64) → Prop)
    (f : ∀ {i K m}, P i K m → X.Prem i K m) : SlotC ι where
  Prem := P
  path i K m hK hU h := X.path i K m hK hU (f h)
  Av i K m hK hU h := X.Av i K m hK hU (f h)

section gen
variable {S : Type} {st : machine.Store S} (L : LawfulStore st) {ι : Type}

/-- **`VFacts` from `JVmL` [J]** (route U). `R` is the old record without `VFacts`; `b` its bundle state. -/
def SlotU.ofJ (X : SlotU ι) (R : ι → KLayoutV → (U64 → U64) → Prop)
    (b : ∀ {i K m}, R i K m → ∃ s : S, SlJAt (L := L) K.toKLayout s)
    (f : ∀ {i K m}, VFacts L K → R i K m → X.Prem i K m) : SlotU ι :=
  X.pull (fun i K m => JVmL L K ∧ R i K m) (fun h => f (VFacts.ofJVm h.1 (b h.2).choose_spec) h.2)

/-- **`VFacts` from `K.vcpus = ∅`** (route U; P3's scope). -/
def SlotU.ofP3 (X : SlotU ι) (R : ι → KLayoutV → (U64 → U64) → Prop)
    (b : ∀ {i K m}, R i K m → ∃ s : S, SlJAt (L := L) K.toKLayout s)
    (f : ∀ {i K m}, VFacts L K → R i K m → X.Prem i K m) : SlotU ι :=
  X.pull (fun i K m => K.vcpus = ∅ ∧ R i K m) (fun h => f (VFacts.ofEmpty h.1 (b h.2).choose_spec) h.2)

/-- `SlotU.ofJ` for route C. -/
def SlotC.ofJ (X : SlotC ι) (R : ι → KLayoutV → (U64 → U64) → Prop)
    (b : ∀ {i K m}, R i K m → ∃ s : S, SlJAt (L := L) K.toKLayout s)
    (f : ∀ {i K m}, VFacts L K → R i K m → X.Prem i K m) : SlotC ι :=
  X.pull (fun i K m => JVmL L K ∧ R i K m) (fun h => f (VFacts.ofJVm h.1 (b h.2).choose_spec) h.2)

/-- `SlotU.ofP3` for route C. -/
def SlotC.ofP3 (X : SlotC ι) (R : ι → KLayoutV → (U64 → U64) → Prop)
    (b : ∀ {i K m}, R i K m → ∃ s : S, SlJAt (L := L) K.toKLayout s)
    (f : ∀ {i K m}, VFacts L K → R i K m → X.Prem i K m) : SlotC ι :=
  X.pull (fun i K m => K.vcpus = ∅ ∧ R i K m) (fun h => f (VFacts.ofEmpty h.1 (b h.2).choose_spec) h.2)

end gen

/-! ## The base records (the `fl4LocW` records without `vf`) -/

section fam
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)

/-- **I/O port's premises without `VFacts`** (`IoPrem` minus `vf`). -/
structure IoPremB (i : IoArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
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
  /-- Some bundle state of the layout (no premise: the start state). -/
  bun : ∃ σ : S, SlJAt (L := L) K.toKLayout σ
  /-- [W] declining `ReadOnce` of the generated tree `R.ioBodyG number`. -/
  ro : ∀ s s' a r, (SlJAt (L := L) K.toKLayout s ∧ i.Q K m s) →
    (¬ ∃ s1 a1, syscall.handle_ioport_local st ar s a i.number = ok (true, s1, a1)) →
    Alt st (IoRS (st := st) (userV K) i.Locks s) (OwnMap.cls (userV K)) (OwnMap.ko (userV K) m)
      (· ∈ (userV K).user) s s' →
    interp st ar (R.ioBodyG i.number) s' a = ok r →
    E2E.Once st ar (IoRS (st := st) (userV K) i.Locks s) (· ∈ (userV K).user) ∅ ∅ (R.ioBodyG i.number) s' a

theorem IoPremB.toIo {i : IoArg S} {K : KLayoutV} {m : U64 → U64} (vf : VFacts L K) (h : IoPremB st ar i K m) :
    IoPrem st ar i K m :=
  ⟨vf, h.pe, h.mA, h.uf, h.bun, h.ro⟩

/-- **`TCB_SetTimer`'s premises without `VFacts`** (`StPremK` minus `vf`, plus `bun`). -/
structure StPremB (i : StArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- Some bundle state of the layout (no premise: the start state, `Pre` = `SlJAt K ∧ Q`). -/
  bun : ∃ σ : S, SlJAt (L := L) K.toKLayout σ
  /-- [J] `StEntK` at bundle states. -/
  pe : ∀ s, SlJAt (L := L) K.toKLayout s → i.Q K m s →
    StEntK K.toKLayout st K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits i.Ac
      i.target m s
  /-- [W] `ReadOnce` of the generated tree. -/
  ro : E2E.ReadOnce st ar (R.localtimer.handle_set_timer_local i.n i.target) (OwnMap.cls (userV K))
      (OwnMap.ko (userV K) m) (· ∈ (userV K).user) (StEntV K st i.Cs i.Ω i.Sg i.Ac i.target m) (MaxR (userV K) st i.lk)
  /-- [J] -/
  eu : ∀ s b v, StEnt (userV K) st K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns
      K.heap.scBits i.Ac i.target s → b ∈ (userV K).user → Aligned b →
    StEnt (userV K) st K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits i.Ac
      i.target (L.wr s b v)
  /-- [P] the locks are determined by the core, the kernel base and the aligned words off `(userV K).user`. -/
  kd : ∀ s, KernDetS (L := L) (userV K).user i.lk s
  /-- [J] -/
  nu : ∀ s, StEnt (userV K) st K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns
      K.heap.scBits i.Ac i.target s → ∀ o : U64, o.val < 4288 → L.nodeAt s (L.cpu s) o ∉ (userV K).user
  /-- [J] -/
  uf : ∀ s b v, SlJAt (L := L) K.toKLayout s → i.Q K m s → b ∈ (userV K).user → Aligned b → i.Q K m (L.wr s b v)

theorem StPremB.toK {i : StArg S} {K : KLayoutV} {m : U64 → U64} (vf : VFacts L K) (h : StPremB st ar i K m) :
    StPremK st ar i K m :=
  ⟨vf, h.pe, h.ro, h.eu, h.kd, h.nu, h.uf⟩

/-- **The timer interrupt's premises without `VFacts`** (`IrqPremK` minus `vf`, plus `bun`). -/
structure IrqPremB (i : IrqArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- Some bundle state of the layout (no premise: the start state, whose `IrqPreV` includes `SlJAt K`). -/
  bun : ∃ σ : S, SlJAt (L := L) K.toKLayout σ
  /-- The IRQ's state word lies in the kernel-state block (the timer IRQ is 2). -/
  lt : i.irq.val < 128
  /-- [W] `ReadOnce` of the generated tree. -/
  ro : E2E.ReadOnce st ar (R.localtimer.handle_timer_irq_local i.irq i.pl) (OwnMap.cls (userV K))
    (OwnMap.ko (userV K) m) (· ∈ (userV K).user) (IrqPreV K st m) (MaxR (userV K) st i.lk)
  /-- [P] at bundle states the locks are determined by the words off `(userV K).user`. -/
  kd : ∀ s, SlJAt (L := L) K.toKLayout s → KernDetS (L := L) (userV K).user i.lk s
  /-- [P] -/
  pl : PlanLk i.lk i.pl

theorem IrqPremB.toK {i : IrqArg S} {K : KLayoutV} {m : U64 → U64} (vf : VFacts L K) (h : IrqPremB st ar i K m) :
    IrqPremK st ar i K m :=
  ⟨vf, h.lt, h.ro, h.kd, h.pl⟩

/-- **syscall_local's premises without `VFacts`** (`SlPremK` minus `vf`, plus `bun`). -/
structure SlPremB (i : SlArg S) (K : KLayoutV) : Prop where
  /-- Some bundle state of the layout (no premise: the start state, `Pre` = `SlJAt K ∧ SlQ`). -/
  bun : ∃ σ : S, SlJAt (L := L) K.toKLayout σ
  /-- [P] the glue's core set is below 64 (P3's sets: `SlJAt.hCs`). -/
  cs : ∀ c ∈ i.Cs, c.val < 64
  /-- [P] at bundle states the locks are determined by kernel words. -/
  kd : ∀ (K : OwnMap.KLayout) (s : S), SlJAt (L := L) K s → KernDetAt (L := L) K i.Locks s
  /-- [W] `ReadOnce` of the generated tree. -/
  ro : ∀ K m, E2E.ReadOnce st ar (R.syscall.handle_syscall_local i.n i.found) (OwnMap.cls K) (OwnMap.ko K m)
      (· ∈ K.user)
      (fun s => SlJAt (L := L) K s ∧ Fl4Proofs.P2.PathObl.SlQ st ar i.Locks i.n i.found
        i.Cs i.Ω i.Sg i.Ac K m s)
      (SlRS (st := st) K i.Locks)

theorem SlPremB.toK {i : SlArg S} {K : KLayoutV} (vf : VFacts L K) (h : SlPremB st ar i K) : SlPremK st ar i K :=
  ⟨vf, h.cs, h.kd, h.ro⟩

/-! ## The two families and theorems -/

variable (hA : P0.ArchTotal ar) (hSt : P0.StoreTotal st) (hm : E2E.MasksWr st) (a0 : A)

/-- I/O port slot, `JVmL` form. -/
def ioSlotJ : SlotU (IoArg S) :=
  (ioSlot st ar hA hm).ofJ L (IoPremB st ar) (fun h => h.bun) (fun vf h => IoPremB.toIo st ar vf h)

/-- `TCB_SetTimer` slot, `JVmL` form. -/
def stSlotJ : SlotU (StArg S) :=
  (stSlotK st ar hA hm).ofJ L (StPremB st ar) (fun h => h.bun) (fun vf h => StPremB.toK st ar vf h)

/-- Timer interrupt slot, `JVmL` form. -/
def irqSlotJ : SlotU (IrqArg S) :=
  (irqSlotK st ar hA hm).ofJ L (IrqPremB st ar) (fun h => h.bun) (fun vf h => IrqPremB.toK st ar vf h)

/-- syscall_local slot, `JVmL` form. -/
def slSlotJ : SlotC (SlArg S) :=
  (slSlotK st ar hA hSt hm a0).ofJ L (fun i K _ => SlPremB st ar i K) (fun h => h.bun) (fun vf h => SlPremB.toK st ar vf h)

/-- I/O port slot at P3's scope (`K.vcpus = ∅`). -/
def ioSlotP3 : SlotU (IoArg S) :=
  (ioSlot st ar hA hm).ofP3 L (IoPremB st ar) (fun h => h.bun) (fun vf h => IoPremB.toIo st ar vf h)

/-- `TCB_SetTimer` slot at P3's scope. -/
def stSlotP3 : SlotU (StArg S) :=
  (stSlotK st ar hA hm).ofP3 L (StPremB st ar) (fun h => h.bun) (fun vf h => StPremB.toK st ar vf h)

/-- Timer interrupt slot at P3's scope. -/
def irqSlotP3 : SlotU (IrqArg S) :=
  (irqSlotK st ar hA hm).ofP3 L (IrqPremB st ar) (fun h => h.bun) (fun vf h => IrqPremB.toK st ar vf h)

/-- syscall_local slot at P3's scope. -/
def slSlotP3 : SlotC (SlArg S) :=
  (slSlotK st ar hA hSt hm a0).ofP3 L (fun i K _ => SlPremB st ar i K) (fun h => h.bun) (fun vf h => SlPremB.toK st ar vf h)

/-- **FL4's eight local paths, VM layout facts from `JVmL` [J]** (module docstring). -/
def fl4LocJ : Fl4Loc (VmFArg S) (VmRArg S) (IoArg S) (StArg S) (IrqArg S) (SlArg S) (VxArg S ⊕ VtArg S) where
  vmF := vmFSlot st ar hA hm
  vmR := vmRSlot st ar hA hm
  io := ioSlotJ st ar hA hm
  st := stSlotJ st ar hA hm
  irq := irqSlotJ st ar hA hm
  sl := slSlotJ st ar hA hSt hm a0
  vq := fl4LQW st ar hA hm (fl4Dflt st ar hm)

/-- **FL4's eight local paths at P3's scope** (`K.vcpus = ∅` at every start of the `io` / `st` / `irq` / `sl`
slots; module docstring). -/
def fl4LocP3 : Fl4Loc (VmFArg S) (VmRArg S) (IoArg S) (StArg S) (IrqArg S) (SlArg S) (VxArg S ⊕ VtArg S) where
  vmF := vmFSlot st ar hA hm
  vmR := vmRSlot st ar hA hm
  io := ioSlotP3 st ar hA hm
  st := stSlotP3 st ar hA hm
  irq := irqSlotP3 st ar hA hm
  sl := slSlotP3 st ar hA hSt hm a0
  vq := fl4LQW st ar hA hm (fl4Dflt st ar hm)

/-- **FL4 end to end, VM-layout facts from the one [J] `JVmL`** (`serializable_fl4_localW`'s statement over
`fl4LocJ`): the form for the VT-x extension, where `JVm` at a nonempty `K.vcpus` is the layout half of a VT-x joint
invariant. -/
theorem serializable_fl4_localJ {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutV}
    (h0 : Init s0) (hA0 : ArmInv s0) (hK0 : RegionOKV K0) (hU0 : UserOKV K0) (hM0 : MapsV K0 s0)
    (h : ExecV ((fl4LocJ st ar hA hSt hm a0).paths (fl4Dflt st ar hm)) s0 K0 s K) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_fl4_localG _ _ h0 hA0 hK0 hU0 hM0 h hq

/-- **FL4 end to end at P3's scope, no VM-layout [J]** (`serializable_fl4_localW`'s statement over `fl4LocP3`):
every execution of FL4 whose local runs are starts of `fl4LocP3`'s eight paths (the `io` / `st` / `irq` / `sl`
slots at layouts with no VCPU), at a state with no local path in progress, ran exactly as some serial order of its
completed entries. **The VM paths are vacuous here**: at a P3 state no thread is bound to a VCPU (`JAtZ.curVcpu0`),
so `local_vm_exit` / `local_vm_timer_irq` cannot accept there, and with `K.vcpus = ∅` the hardware writes nothing;
a non-vacuous statement about VT-x executions needs a VT-x joint invariant (`serializable_fl4_localJ`'s `JVmL` is
its layout half). -/
theorem serializable_fl4_localP3 {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutV}
    (h0 : Init s0) (hA0 : ArmInv s0) (hK0 : RegionOKV K0) (hU0 : UserOKV K0) (hM0 : MapsV K0 s0)
    (h : ExecV ((fl4LocP3 st ar hA hSt hm a0).paths (fl4Dflt st ar hm)) s0 K0 s K) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_fl4_localG _ _ h0 hA0 hK0 hU0 hM0 h hq

end fam

end
end Fl4Proofs.P2.E2EV
