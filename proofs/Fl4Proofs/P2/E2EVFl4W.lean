/-
P2 (integration int/j15): **`fl4LocAll` with the newest slot values of the merged lines** (wiring only).

`P2/E2EVFl4.lean`'s `fl4LocAll` / `serializable_fl4_local` are unchanged; this module builds a second family
`fl4LocW` from the same slots, swapping three of them, and proves the same end-to-end statement over it
(`serializable_fl4_localW`, by `serializable_fl4_localG`).

* `SlotU.pull`: a slot whose premise record is replaced by a stronger-or-equal one (the path and the lift lemma
  are the old slot's, at the old record built from the new one).
* `st` (`stSlotK`): `StPremK` = `StPrem` with `lk` [P] replaced by **`kd` [P] `∀ s, KernDetS (userV K).user lk s`**
  (the locks are determined by the core, the kernel base and the aligned words off the user / VCPU data words;
  slhuf gen 6), `lk` by `hlk_of_kernelDetU` (`P := True`, as `StPrem.lk` is unguarded).
* `irq` (`irqSlotK`): `IrqPremK` = `IrqPrem` with `lk` [P] replaced by **`kd` [P] `∀ s, SlJAt K s →
  KernDetS (userV K).user lk s`**, `lk` by `hlk_of_kernelDetU` (`P := SlJAt K.toKLayout`).
* `sl` (`slSlotK`): `sl_pathsKC5` (slhuf gen 5/6) in place of `sl_pathsKC`. `SlPremK`: `vf` [J], **`cs` [P]
  `∀ c ∈ Cs, c.val < 64`** (P3's sets: `SlJAt.hCs` / `hCs_of_sub`), **`kd` [P] `KernDetAt` at bundle states**,
  `ro` [W]. So `SlPrem`'s `PBw` [J], `Arw` [P] and `lk` [P] are gone. `AvoidV` as `slSlot`'s (`sl_pathsKC5`
  unfolds to the same `sl_pathsKF` chain).
* `vq`'s timer slot (`vtSlotW`): lvm gen 9's `vtimer_localPathW`. `VtPremW` = `VtPrem` with `F` / `Fm` [W] asked
  only for the waking fire case (`¬ NoWake`) and **`M` [J]** (the map memory agrees with the entry on every
  thread's `AFFINITY`, lvm's `hM`). `fl4LQW` = `PathsV.sum vxSlot vtSlotW`.

Not swapped: `VxPrem.lk` / `VtPrem(W).lk` (lvm's `hlk` has no `Aligned b`, so `hlk_of_kernelDetU` does not apply;
lvm to align), `io` (its `uf` bundles the lock equation with `Q` / `IoRS` / `IoWS` / `IoDS`).
-/
import Fl4Proofs.P2.E2EVFl4
import Fl4Proofs.P2.SlJLk2
import Fl4Proofs.P2.AccessLvmTf
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
open Fl4Proofs.P2.OwnMap (fld oAFFINITY)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll)

noncomputable section
open Classical

/-- **A slot under a new premise record** that gives the old one. -/
def SlotU.pull {ι : Type} (X : SlotU ι) (P : ι → KLayoutV → (U64 → U64) → Prop)
    (f : ∀ {i K m}, P i K m → X.Prem i K m) : SlotU ι where
  Prem := P
  path i K m hK hU h := X.path i K m hK hU (f h)
  W i K m hK hU h := X.W i K m hK hU (f h)

section fam
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)

/-- **`TCB_SetTimer`'s premises, locks from kernel words** (module docstring). -/
structure StPremK (i : StArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- [J] -/
  vf : VFacts L K
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

theorem StPremK.toSt {i : StArg S} {K : KLayoutV} {m : U64 → U64} (h : StPremK st ar i K m) :
    StPrem st ar i K m :=
  ⟨h.vf, h.pe, h.ro, h.eu,
    fun s b v hb hba => hlk_of_kernelDetU (P := fun _ => True) (fun s _ => h.kd s) s b v trivial hb hba,
    h.nu, h.uf⟩

/-- **The timer interrupt's premises, locks from kernel words** (module docstring). -/
structure IrqPremK (i : IrqArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- [J] -/
  vf : VFacts L K
  /-- The IRQ's state word lies in the kernel-state block (the timer IRQ is 2). -/
  lt : i.irq.val < 128
  /-- [W] `ReadOnce` of the generated tree. -/
  ro : E2E.ReadOnce st ar (R.localtimer.handle_timer_irq_local i.irq i.pl) (OwnMap.cls (userV K))
    (OwnMap.ko (userV K) m) (· ∈ (userV K).user) (IrqPreV K st m) (MaxR (userV K) st i.lk)
  /-- [P] at bundle states the locks are determined by the words off `(userV K).user`. -/
  kd : ∀ s, SlJAt (L := L) K.toKLayout s → KernDetS (L := L) (userV K).user i.lk s
  /-- [P] -/
  pl : PlanLk i.lk i.pl

theorem IrqPremK.toIrq {i : IrqArg S} {K : KLayoutV} {m : U64 → U64} (h : IrqPremK st ar i K m) :
    IrqPrem st ar i K m :=
  ⟨h.vf, h.lt, h.ro, hlk_of_kernelDetU h.kd, h.pl⟩

/-- **syscall_local's premises for `sl_pathsKC5`** (module docstring). -/
structure SlPremK (i : SlArg S) (K : KLayoutV) : Prop where
  /-- [J] -/
  vf : VFacts L K
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

/-- **`local_vm_timer_irq`'s premises for `vtimer_localPathW`** (module docstring). -/
structure VtPremW (i : VtArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- [P] `IsProg`, [W] `NoZero`, [W] `ReadOnce`. -/
  pz : ∃ p : SProg Bool, IsProg (vtimerBody S i.irq i.pl i.n) p ∧ NoZero p ∧
    E2E.ReadOnce st ar p (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) (VtPre st i K)
      (VexitRS K st i.lk)
  /-- [J] -/
  eu : ∀ s b v', VtPre st i K s → b ∈ K.user → Aligned b → VtPre st i K (L.wr s b v')
  /-- [P] -/
  lk : ∀ s b v', b ∈ K.user → i.lk (L.wr s b v') = i.lk s
  /-- [W] the waking fire case, guarded run. -/
  F : ∀ s a s1 a1, VtPre st i K s → IrqFire st ar s a → ¬ NoWake st s →
    localvm.handle_vm_timer_irq_local st ar s a i.irq i.pl i.n = ok (true, s1, a1) →
    localvm.handle_vm_timer_irq_local (guard st (VexitRS K st i.lk s) (VexitWS K st i.lk s)) ar s a i.irq i.pl i.n =
      ok (true, s1, a1)
  /-- [W] the waking fire case, checked run. -/
  Fm : ∀ s a s1 a1, VtPre st i K s → IrqFire st ar s a → ¬ NoWake st s →
    localvm.handle_vm_timer_irq_local st ar s a i.irq i.pl i.n = ok (true, s1, a1) →
    localvm.handle_vm_timer_irq_local (mguard st
      (fun x y => StepOK (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) (L.cpu s)
        (i.lk s) (L.mem x) (L.mem y))) ar s a i.irq i.pl i.n = ok (true, s1, a1)
  /-- P1's notifications typed in the heap. -/
  Nt : ∀ q ∈ i.Nt, i.H q = some .ntfn
  /-- [J] the map memory agrees with the entry on every thread's `AFFINITY`. -/
  M : ∀ s, VtPre st i K s → ∀ y ∈ i.T, m (fld y oAFFINITY) = L.mem s (affA y)

variable (hA : P0.ArchTotal ar) (hSt : P0.StoreTotal st) (hm : E2E.MasksWr st) (a0 : A)

/-- **`TCB_SetTimer` slot, locks from kernel words.** -/
def stSlotK : SlotU (StArg S) := (stSlot st ar hA hm).pull (StPremK st ar) (fun h => h.toSt)

/-- **Timer interrupt slot, locks from kernel words.** -/
def irqSlotK : SlotU (IrqArg S) := (irqSlot st ar hA hm).pull (IrqPremK st ar) (fun h => h.toIrq)

/-- **syscall_local slot at `sl_pathsKC5`** (route C). -/
def slSlotK : SlotC (SlArg S) where
  Prem i K _ := SlPremK st ar i K
  path i K m hK hU h :=
    sl_pathsKC5 (Locks := i.Locks) (n := i.n) (found := i.found) (Cs := i.Cs) (Ω := i.Ω) (Sg := i.Sg) (Ac := i.Ac)
      ar hSt hA hm a0 h.cs h.kd
      (fun K' m' => ⟨_, sl_isProg S i.n i.found, sl_noZero i.n i.found, h.ro K' m'⟩) () K.toKLayout m hK.base hU.base
  Av i K m hK hU h := by
    unfold sl_pathsKC5 sl_pathsKC4 sl_pathsKF sl_pathsKU sl_pathsK
    exact sl_avoidVK ar hSt hA hm a0 hK hU.base (fun _ h' => h'.1) _ _ _ _ _ _ h.vf.heap h.vf.tab
      (fun s h' => h.vf.pool s h'.1) h.vf.user

/-- **`local_vm_timer_irq` slot at `vtimer_localPathW`.** -/
def vtSlotW : SlotN (VtArg S) where
  Prem i K m := VtPremW st ar i K m
  path i K m hK hU h :=
    vtimer_localPathW (T := i.T) (Cs := i.Cs) (Ω := i.Ω) (Sg := i.Sg) (Rp := i.Rp) (Scs := i.Scs) (Nt := i.Nt)
      (Ac := i.Ac) (H := i.H) (Z := i.Z) (lk := i.lk) (irq := i.irq) (n := i.n) (pl := i.pl) (m := m) ar hA hK hU
      h.pz.choose_spec.1 h.pz.choose_spec.2.1 hm h.pz.choose_spec.2.2 h.eu h.lk h.F h.Fm h.Nt h.M

/-- lvm's paths with the timer slot at `vtimer_localPathW`. -/
def fl4LQW (D : Dflt) : PathsV (VxArg S ⊕ VtArg S) :=
  PathsV.sum ((vxSlot st ar hA hm).fam D) ((vtSlotW st ar hA hm).fam D)

/-- **FL4's eight local paths, newest slots** (module docstring). -/
def fl4LocW : Fl4Loc (VmFArg S) (VmRArg S) (IoArg S) (StArg S) (IrqArg S) (SlArg S) (VxArg S ⊕ VtArg S) where
  vmF := vmFSlot st ar hA hm
  vmR := vmRSlot st ar hA hm
  io := ioSlot st ar hA hm
  st := stSlotK st ar hA hm
  irq := irqSlotK st ar hA hm
  sl := slSlotK st ar hA hSt hm a0
  vq := fl4LQW st ar hA hm (fl4Dflt st ar hm)

/-- **FL4 end to end with rule 7 over its eight local paths, newest slots** (`serializable_fl4_local`'s statement
over `fl4LocW`). -/
theorem serializable_fl4_localW {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutV}
    (h0 : Init s0) (hA0 : ArmInv s0) (hK0 : RegionOKV K0) (hU0 : UserOKV K0) (hM0 : MapsV K0 s0)
    (h : ExecV ((fl4LocW st ar hA hSt hm a0).paths (fl4Dflt st ar hm)) s0 K0 s K) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_fl4_localG _ _ h0 hA0 hK0 hU0 hM0 h hq

end fam

end
end Fl4Proofs.P2.E2EV
