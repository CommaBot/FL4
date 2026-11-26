/-
P2 (line vlift, gen 6): **lvm's `ownV`-native paths as conditional slots** (the `vq` part of `Fl4Loc`).

The two VT-x local paths of line lvm are stated for `ownV` directly (no lift): `vexit_localPathP`
(`local_vm_exit`, the pending-exit case included; `P2/AccessLvmPo.lean`) and `vtimer_localPath`
(`local_vm_timer_irq`; `P2/AccessLvmTl.lean`). A `PathsV` member must exist at every layout, so, as for the route-U /
route-C slots (`P2/E2EVFam.lean`), each is a **conditional slot**:

* `SlotN ι` (`Prem`, `path` under `Prem`), `SlotN.fam` (the empty path where `Prem` fails), `SlotN.fam_pos`,
  **`SlotN.startAt`** (a start of the slot's path where `Prem` holds is a start of the family member).
* `VxArg` / **`VxPrem`** / **`vxSlot`** (`vexit_localPathP`), `VtArg` / **`VtPrem`** / **`vtSlot`**
  (`vtimer_localPath`), **`fl4LQ := PathsV.sum (vxSlot.fam D) (vtSlot.fam D)`**.
* **`vexitPre_ofHeap`**: the vexit path's `Pre` (`VexitEnt ∧ VexitPEnt`) at a start from `VexitEnt` and
  `VexitPEnt.ofHeap`'s ingredients (int14's `P2/E2EVLvmPW.lean`: `vfit` / `pusr` from `vin` + `VcpuHeap`), so the
  glue's start obligation for the vexit slot asks no `VexitPEnt` of its own.

Premises (per slot record; asked at the `(K, m)` of each start, `SlotN.startAt`):
* `VxPrem`: `pz` ([P] `IsProg` of `vexitBody`, [W] `NoZero`, [W] `ReadOnce`; no generated tree for this body yet),
  `eu` [J] (`VexitEnt ∧ VexitPEnt` kept by user writes), `lk` [P] (locks kept by user writes; lvm's statement,
  not restricted to aligned words). Start: `VexitEnt` ([J] fields `vin` / `ksv` / `vfar` / `nfar`, lvm) and
  `VexitPEnt` (`vexitPre_ofHeap`: `usr` [J], `buf` [P], `aff0` [J], P1/P3 facts, `VcpuHeap` [J]).
* `VtPrem`: `pz` (as above for `vtimerBody`), `eu` [J], `lk` [P], `F` / `Fm` [W] (fire case), `D` [W] (declines).
  Start: `VtmEnt` (lvm's fields).
-/
import Fl4Proofs.P2.E2EVFam
import Fl4Proofs.P2.AccessLvmTl
import Fl4Proofs.P2.E2EVLvmPW
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.PathObl Fl4Proofs.P2.E2E Fl4Proofs.P2.OwnMapV
open Fl4Proofs.P2.OwnMap (fld oAFFINITY)

noncomputable section
open Classical

/-! ## Native conditional slots -/

/-- **A native slot**: a path stated for `ownV` where `Prem i K m` holds. -/
structure SlotN (ι : Type) : Type 1 where
  Prem : ι → KLayoutV → (U64 → U64) → Prop
  path : ∀ i (K : KLayoutV) m, RegionOKV K → UserOKV K → Prem i K m →
    LocalPath (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user)

/-- The slot completed to every layout by the empty path. -/
def SlotN.fam {ι : Type} (D : Dflt) (X : SlotN ι) : PathsV ι :=
  fun i K m hK hU => if h : X.Prem i K m then X.path i K m hK hU h else
    LocalPath.void D (OwnMap.ko_aligned hK.base hU.base m)

theorem SlotN.fam_pos {ι : Type} (D : Dflt) (X : SlotN ι) {i : ι} {K : KLayoutV} {m : U64 → U64}
    {hK : RegionOKV K} {hU : UserOKV K} (h : X.Prem i K m) : X.fam D i K m hK hU = X.path i K m hK hU h :=
  dif_pos h

/-- **Starting a native slot** (the glue's `Fl4StepV.start` [P] for this slot). -/
theorem SlotN.startAt {ι : Type} (D : Dflt) (X : SlotN ι) {i : ι} {K : KLayoutV} {m : U64 → U64}
    {hK : RegionOKV K} {hU : UserOKV K} (h : X.Prem i K m) {c : U64} {hs : U64 → Prop} {μ : U64 → U64}
    (σ : (X.path i K m hK hU h).S) (a : (X.path i K m hK hU h).A) (hP : (X.path i K m hK hU h).Pre σ)
    (hc : (X.path i K m hK hU h).L.cpu σ = c) (hl : (X.path i K m hK hU h).Locks σ = hs)
    (hμ : ∀ x, Aligned x → x ∉ K.user → (X.path i K m hK hU h).L.mem σ x = μ x) :
    ∃ q, StartAt (X.fam D i K m hK hU) c hs μ q := by
  have key : ∀ P, P = X.path i K m hK hU h → ∃ q, StartAt P c hs μ q := by
    rintro P rfl
    exact ⟨_, σ, a, hP, hc, hl, hμ, rfl⟩
  exact key _ (X.fam_pos D h)

/-! ## lvm's two paths -/

/-- `local_vm_exit`: the exiting VCPU and the glue's notification, P1's sets and the locks. -/
structure VxArg (S : Type) : Type where
  v : U64
  n : U64
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
  lk : S → U64 → Prop

/-- `local_vm_timer_irq`: the IRQ, fl4-sync's plan, the glue's notification, P1's sets and the locks. -/
structure VtArg (S : Type) : Type where
  irq : U64
  n : U64
  pl : localtimer.TimerIrqPlan
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
  lk : S → U64 → Prop

section lvm
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)

/-- The vexit path's `Pre`. -/
abbrev VxPre (i : VxArg S) (K : KLayoutV) (m : U64 → U64) (s : S) : Prop :=
  VexitEnt K st i.T i.Cs i.Ω i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.lk i.v i.n s ∧
    VexitPEnt K st i.T i.Cs i.H i.Sg i.Scs i.Z m i.v s

/-- **`local_vm_exit`'s premises at `(K, m)`** (`vexit_localPathP`'s). -/
structure VxPrem (i : VxArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- [P] `IsProg`, [W] `NoZero`, [W] `ReadOnce`. -/
  pz : ∃ p : SProg Bool, IsProg (vexitBody S i.v i.n) p ∧ NoZero p ∧
    E2E.ReadOnce st ar p (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) (VxPre st i K m)
      (VexitRS K st i.lk)
  /-- [J] the entry facts kept by user writes. -/
  eu : ∀ s b v', VxPre st i K m s → b ∈ K.user → Aligned b → VxPre st i K m (L.wr s b v')
  /-- [P] the locks kept by user writes. -/
  lk : ∀ s b v', b ∈ K.user → i.lk (L.wr s b v') = i.lk s

/-- The vtimer path's `Pre`. -/
abbrev VtPre (i : VtArg S) (K : KLayoutV) (s : S) : Prop :=
  VtmEnt K st i.T i.Cs i.Ω i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.lk i.irq i.n s

/-- **`local_vm_timer_irq`'s premises at `(K, m)`** (`vtimer_localPath`'s). -/
structure VtPrem (i : VtArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- [P] `IsProg`, [W] `NoZero`, [W] `ReadOnce`. -/
  pz : ∃ p : SProg Bool, IsProg (vtimerBody S i.irq i.pl i.n) p ∧ NoZero p ∧
    E2E.ReadOnce st ar p (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) (VtPre st i K)
      (VexitRS K st i.lk)
  /-- [J] -/
  eu : ∀ s b v', VtPre st i K s → b ∈ K.user → Aligned b → VtPre st i K (L.wr s b v')
  /-- [P] -/
  lk : ∀ s b v', b ∈ K.user → i.lk (L.wr s b v') = i.lk s
  /-- [W] the fire case, guarded run. -/
  F : ∀ s a s1 a1, VtPre st i K s → IrqFire st ar s a →
    localvm.handle_vm_timer_irq_local st ar s a i.irq i.pl i.n = ok (true, s1, a1) →
    localvm.handle_vm_timer_irq_local (guard st (VexitRS K st i.lk s) (VexitWS K st i.lk s)) ar s a i.irq i.pl i.n =
      ok (true, s1, a1)
  /-- [W] the fire case, checked run. -/
  Fm : ∀ s a s1 a1, VtPre st i K s → IrqFire st ar s a →
    localvm.handle_vm_timer_irq_local st ar s a i.irq i.pl i.n = ok (true, s1, a1) →
    localvm.handle_vm_timer_irq_local (mguard st
      (fun x y => StepOK (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) (L.cpu s)
        (i.lk s) (L.mem x) (L.mem y))) ar s a i.irq i.pl i.n = ok (true, s1, a1)
  /-- [W] the declines. -/
  D : ∀ s a s1 a1, VtPre st i K s →
    localvm.handle_vm_timer_irq_local st ar s a i.irq i.pl i.n = ok (false, s1, a1) →
    localvm.handle_vm_timer_irq_local (guard st (VexitRS K st i.lk s) (IrqDec st s)) ar s a i.irq i.pl i.n =
      ok (false, s1, a1)

variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- **`local_vm_exit` slot** (`vexit_localPathP`). -/
def vxSlot : SlotN (VxArg S) where
  Prem i K m := VxPrem st ar i K m
  path i K m hK hU h :=
    vexit_localPathP (T := i.T) (Cs := i.Cs) (Ω := i.Ω) (Sg := i.Sg) (Rp := i.Rp) (Scs := i.Scs) (Nt := i.Nt)
      (Ac := i.Ac) (H := i.H) (Z := i.Z) (lk := i.lk) (v := i.v) (n := i.n) (m := m) ar hA hK hU
      h.pz.choose_spec.1 h.pz.choose_spec.2.1 hm h.pz.choose_spec.2.2 h.eu h.lk

/-- **`local_vm_timer_irq` slot** (`vtimer_localPath`). -/
def vtSlot : SlotN (VtArg S) where
  Prem i K m := VtPrem st ar i K m
  path i K m hK hU h :=
    vtimer_localPath (T := i.T) (Cs := i.Cs) (Ω := i.Ω) (Sg := i.Sg) (Rp := i.Rp) (Scs := i.Scs) (Nt := i.Nt)
      (Ac := i.Ac) (H := i.H) (Z := i.Z) (lk := i.lk) (irq := i.irq) (n := i.n) (pl := i.pl) (m := m) ar hA hK hU
      h.pz.choose_spec.1 h.pz.choose_spec.2.1 hm h.pz.choose_spec.2.2 h.eu h.lk h.F h.Fm h.D

/-- **lvm's paths as one `PathsV` family** (`vq` of `fl4Loc`). -/
def fl4LQ (D : Dflt) : PathsV (VxArg S ⊕ VtArg S) :=
  PathsV.sum ((vxSlot st ar hA hm).fam D) ((vtSlot st ar hA hm).fam D)

/-- **The vexit path's `Pre` at a start from `VexitEnt` and `VexitPEnt.ofHeap`'s ingredients** (module
docstring). -/
theorem vexitPre_ofHeap {i : VxArg S} {K : KLayoutV} {m : U64 → U64} {s : S}
    (hE : VexitEnt K st i.T i.Cs i.Ω i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.lk i.v i.n s)
    (usr : ∀ x, x ∈ K.user → Aligned x → UsrW st i.T i.Cs i.H i.Sg i.Scs i.Z s x)
    (buf : msg.lookup_ipc_buffer st s true (L.curW s) ⦃ b => BufOK {x | x ∈ K.user ∧ Aligned x} b ⦄)
    (aff0 : m (fld (L.curW s) oAFFINITY) = L.mem s (affA (L.curW s)))
    (hT : i.T = i.H.tcbs) (hΩ : i.Ω = i.H.omega) (hSg : i.Sg = i.H.frame) (hH : HeapOK i.H)
    (hScs : ∀ c ∈ i.Scs, i.H c = some (.sc (i.Z c)))
    (hKI : ∀ p z, i.H p = some (.other z) → p.val + 2 ^ z ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ p.val ∨
      ((L.ksb s).val ≤ p.val ∧ p.val + 2 ^ z ≤ (L.ksb s).val + 13568))
    (hKH : K.heap = i.H) (hV : VcpuHeap K) : VxPre st i K m s :=
  ⟨hE, VexitPEnt.ofHeap usr buf aff0 hE.vin hE.inv hT hΩ hSg hH hScs hKI hKH hV⟩

end lvm

end
end Fl4Proofs.P2.E2EV
