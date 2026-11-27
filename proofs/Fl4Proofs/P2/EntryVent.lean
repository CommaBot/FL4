/-
P2 (vent): **the local entries that call `schedule` end in `AllCores` from
every reachable entry state, `VcpuEnt` replaced by the VCPU words' zero at
the entry (P3) and a run fact.**

## Why not `VcpuEnt`

comb's `timer_irq_local.allCoresExitF` / `set_timer_local.allCoresExitF`
(`P2/EntryFinal.lean`) take `VcpuEnt … s0` [P] (`P2/EntryVcpu.lean`). Its
static fields (`heap`, `sets`, `scs`, `ksIn`) hold at every reachable entry
state (`ventS_of_JAtZ` below), but its `pl : VcpuPl … s0` (P1
`QueueVcpu.lean`) is **not a fact of the entry state**: its clauses quantify
over every state `s` with `Fr0 s0 s` (writes since `s0` within `Cur0W s0`)
and `BXI s`, and

* `VcpuPl.bound` fails at `s := L.wr s0 (t + 3664) x` for any TCB `t ∈ T`
  and `x ≠ 0` with `H x ≠ some (.other 15)`: the write is a `KW` word (the
  TCB clause admits every offset in `[192, 4096)` but 3576/3584), so
  `Fr0 s0 s`, and no P1 invariant in `BXI` reads a TCB's VCPU word (offset
  3664), so `BXI s` from `BXI s0`;
* `VcpuPl.tcb` fails already at `s := s0`: `H`'s `.other 15` objects are
  not only VCPUs — P3's `JPlaced.cnode` puts every radix-10 CNode of the
  typed heap in `H` as `.other 15` — and `vcpu.TCB` = 20480 = slot 640 of
  such a CNode, whose first word is a cap word (nonzero, no TCB address) as
  soon as that slot holds a cap.

So no P3 lemma gives `VcpuEnt`. What `AllCores.exitV` really uses is
`VcpuUsr` at the state `vcpu::check` reads (after `activate_thread`), for
the current thread. P3 gives every TCB's VCPU word **zero** at a joint state
(`JExt.vw`, the native scope); the entry never writes that word, so
`VcpuUsr` holds there vacuously. The walks' footprints (`FootB`/`KWB`,
`FootN`/`KWN`, `FootDU`, `SFootB`) all admit offset 3664, so the keep is
asked of the run (below); `activate_thread`'s `TW` excludes it and is
proved (`vcpuWK_of_tw`).

## Here

* `VcpuZ` (every TCB's VCPU word zero), `VcpuWK` (those words kept),
  `vcpuWK_of_tw`.
* **`AllCores.exitZ`**: `AllCores.exitV` with `VcpuEnt` replaced by
  `VcpuZ s0` and `VcpuWK s0 s4` (`s4` = `schedule`'s end).
* `IrqVK` / `SetVK` **[W]**: the run's body and `schedule` keep every
  TCB's VCPU word, for the run pinned by its code (`IrqPre` / `SetPre`,
  exported by wire's `allCoresBW`). True of FL4 (only `vcpu::detach` and
  `X86VCPUSetTCB` write that word); a proof needs a footprint that
  excludes offset 3664 (a `KWB`-style re-walk of the body, `timer::fire`
  and `schedule`, or offset 3664 in P2's `PrW` exclusion layer).
* **`timer_irq_local.allCoresExitZ`**, **`set_timer_local.allCoresExitZ`**:
  comb's `allCoresExitF` with `V : VcpuEnt` replaced by `hz : VcpuZ s0` and
  the run premise `IrqVK` / `SetVK` [W].
* P3: `VcpuEntS` (`VcpuEnt` without `pl`), `ventS_of_JAtZ`,
  **`ventS_of_reachU17`**: at every `JReachU17` state, under
  `kernel_entry_domInvU29`'s premises only, some `H Cs Ac` with
  `L.cpu s ∈ Cs`, P1's `EntryInv` and `DomInv` over `H`'s sets, `VcpuEntS`
  and `VcpuZ`.
* **`timer_irq_local.allCoresExitJ`**, **`set_timer_local.allCoresExitJ`**:
  at every reachable entry state there are `H Cs Ac` such that every
  accepted run of the local entry from `AllCores` and `BufAt` (over `H`'s
  sets) ends in `AllCores`, under the run premise [W] (and `htg` for
  `TCB_SetTimer`).

**(vk) The run premise discharged.** `PrW` (P2/FootN) now protects every
TCB's VCPU word under `Nd`, so the body's `FootN (KI …) True` footprint,
`fire`'s `FK` frame (`FK.vc`) and the rest of `schedule` (`SFootN`) keep
them (`sched.schedule.vkB`, P2/FootN11); wire's `allCoresBW` exports the
keep from the entry to `schedule`'s end. Hence
**`timer_irq_local.allCoresExitZ2`** / **`set_timer_local.allCoresExitZ2`**
(`allCoresExitZ` without `IrqVK`/`SetVK`) and
**`timer_irq_local.allCoresExitJ2`** / **`set_timer_local.allCoresExitJ2`**
(`allCoresExitJ` without the run premise). `IrqVK`/`SetVK` and the
`…Z`/`…J` theorems are kept unchanged.

Inputs left (P2's own, not P3's): `AllCores s0` (other cores' clauses),
`BufAt s0` (user words / buffers), `IbKeep` (arch), `target ∈ T`.
Fixed-heap caveat (as slj2): `AllCores` is over one `H` for the run; P3
picks `H` per state, so chaining entries needs the next entry's `H` to be
this one (true when the run keeps the typed heap; not stated by P3).
-/
import Fl4Proofs.P2.EntryFinal
import Fl4Proofs.P3.XTopJointDomInv29
open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace Fl4Proofs.P2.Stall
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

attribute [local instance] atCpuI

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}
variable {A : Type _} {ar : machine.Arch A}

/-- Every TCB's VCPU word (offset 3664) is zero (P3 `JExt.vw`). -/
def VcpuZ (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s : S) : Prop :=
  ∀ t ∈ T, L.mem s (core.num.U64.wrapping_add t 3664#u64) = 0#u64

/-- Every TCB's VCPU word kept from `s0` to `s`. -/
def VcpuWK (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s0 s : S) : Prop :=
  ∀ t ∈ T, L.mem s (core.num.U64.wrapping_add t 3664#u64) = L.mem s0 (core.num.U64.wrapping_add t 3664#u64)

theorem VcpuWK.trans' {s0 s1 s2 : S} (h1 : VcpuWK st T s0 s1) (h2 : VcpuWK st T s1 s2) : VcpuWK st T s0 s2 :=
  fun t ht => (h2 t ht).trans (h1 t ht)

/-- `activate_thread`'s tail words (`TW`) miss every TCB's VCPU word. -/
theorem vcpuWK_of_tw {s4 s5 : S} {y : U64} (hT : TcbPlaced T) (hy : y ∈ T)
    (hN : NodePlaced st T s4 (L.cpu s4)) (w : WritesIn st s4 s5 (TW st T Cs Scs y s4)) :
    VcpuWK st T s4 s5 := by
  intro t ht
  have hta := hT t ht
  have hya := hT y hy
  have k1 : (3664#u64 : U64).val = 3664 := by simp
  refine w.2.2 _ (field_aligned hta (by rw [k1]; omega) (by rw [k1])) ?_
  rintro (((⟨ho, -⟩ | ⟨K, h1, h2, -, e⟩) | e) | e | e)
  · exact out_ne_field ho ht hta (by rw [k1]; omega) rfl
  · exact field_ne hta hya (by rw [k1]; omega) (by omega) (fun _ => by rw [k1]; omega) e
  · have k2 : (3472#u64 : U64).val = 3472 := by simp
    exact field_ne hta hya (K2 := 3472#u64) (by rw [k1]; omega) (by rw [k2]; omega)
      (fun _ => by rw [k1, k2]; omega) e
  · rw [stA_eq] at e
    have k2 : (3328#u64 : U64).val = 3328 := by simp
    exact field_ne hta hya (by rw [k1]; omega) (by rw [k2]; omega) (fun _ => by rw [k1, k2]; omega) e
  · exact node_ne_field hN (by rw [act_val]; omega) ht hta (by rw [k1]; omega) e.symm

/-- **From `schedule`'s start to the entry's exit, with the VCPU words**
(`AllCores.exitV` without `VcpuEnt`): every TCB's VCPU word zero at the
entry `s0` (`hz`) and kept to `schedule`'s end `s4` (`hk`). -/
theorem AllCores.exitZ (hA : P0.ArchTotal ar) (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (hS0 : (0#u64) ∉ Scs) {s0 s3 s4 s' : S} {a3 a4 a' : A}
    (hz : VcpuZ st T s0) (hk : VcpuWK st T s0 s4)
    (hB3 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s3) (hBA3 : BufAt st T Cs H Sg Scs Z U s3)
    (esc : sched.schedule st ar s3 a3 = ok (s4, a4)) (h4 : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s4)
    (E : (do
        let (s5, a5) ← sched.activate_thread st ar s4 a4
        let t ← sched.cur_thread st s5
        vcpu.check st ar s5 a5 t) = ok (s', a')) :
    AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s' := by
  have hB3' := hB3
  obtain ⟨⟨Q, R, hq⟩, hB, hX, hS, hSg⟩ := hB3'
  have hI := sched.schedule.entry hA IK hNt s3 a3 Q R hq hB hS hX hSg hBA3
  rw [esc, WP.spec_ok] at hI
  try simp only [WP.uncurry'_pair] at hI
  have hBA4 : BufAt st T Cs H Sg Scs Z U s4 := BufAt.of_fr hBA3 (schIb_holds hA IK hNt s3 a3 _ hB3 hBA3 esc)
  obtain ⟨Q4, R4, hq4⟩ := hI.1
  exact AllCores.tailV hA hNt h4 hS0 hI hBA4
    (fun s5 _ w5 t ht hn => absurd
      (((vcpuWK_of_tw hq4.tcbs hq4.curT (hq4.nodes _ hq4.cur) w5) t ht).trans ((hk t ht).trans (hz t ht))) hn) E

/-- **[W] The timer interrupt's run keeps the TCBs' VCPU words** from the
entry to `schedule`'s end, for the run its code pins (`IrqPre`; module
docstring). -/
def IrqVK (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A) (T : Set U64) (s0 : S) (a0 : A)
    (irq : U64) : Prop :=
  ∀ (s3 : S) (a3 : A) (s4 : S) (a4 : A), IrqPre st ar s0 a0 irq s3 a3 →
    sched.schedule st ar s3 a3 = ok (s4, a4) → VcpuWK st T s0 s4

/-- **[W] The `TCB_SetTimer` run keeps the TCBs' VCPU words** from the
entry to `schedule`'s end, for the run its code pins (`SetPre`; module
docstring). -/
def SetVK (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A) (T : Set U64) (s0 : S) (a0 : A)
    (target : U64) : Prop :=
  ∀ (s3 : S) (a3 : A) (s4 : S) (a4 : A), SetPre st ar s0 a0 target s3 a3 →
    sched.schedule st ar s3 a3 = ok (s4, a4) → VcpuWK st T s0 s4

/-- **The timer-interrupt local entry ends in `AllCores`** (comb's
`allCoresExitF` with `VcpuEnt` replaced). Entry facts: `h0`, `hcpu`, `hI0`,
`hBA0`, `hD0`, `hz` (`VcpuZ`, P3). Named premise: `VK` [W] (`IrqVK`). -/
theorem timer_irq_local.allCoresExitZ (hA : P0.ArchTotal ar) (IK : IbKeep st ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    {s0 s' : S} {a0 a' : A} {irq : U64} {p : localtimer.TimerIrqPlan}
    (h0 : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hcpu : L.cpu s0 ∈ Cs)
    (hI0 : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hBA0 : BufAt st T Cs H Sg Scs Z U s0)
    (hD0 : DomInv st T s0) (hz : VcpuZ st T s0) (VK : IrqVK st ar T s0 a0 irq)
    (e : localtimer.handle_timer_irq_local st ar s0 a0 irq p = ok (true, s', a')) :
    AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s' := by
  obtain ⟨s3, a3, s4, a4, hB3, hBA3, -, esc, W, -, E, pin⟩ :=
    timer_irq_local.allCoresBW hA IK hNt h0 hcpu hI0 hBA0 hD0 e
  have hS0 : (0#u64) ∉ Scs := by
    obtain ⟨-, -, hX0, -⟩ := hI0
    exact ObjsOK.zero_notScs hX0.1
  exact AllCores.exitZ hA IK hNt hS0 hz (VK s3 a3 s4 a4 pin esc) hB3 hBA3 esc W E

/-- **The `TCB_SetTimer` local entry ends in `AllCores`** (comb's
`allCoresExitF` with `VcpuEnt` replaced). Entry facts: `h0`, `hcpu`, `hI0`,
`hBA0`, `htg`, `hD0`, `hz` (`VcpuZ`, P3). Named premise: `VK` [W]
(`SetVK`). -/
theorem set_timer_local.allCoresExitZ (hA : P0.ArchTotal ar) (IK : IbKeep st ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    {s0 s' : S} {a0 a' : A} {n : I64} {target : U64}
    (h0 : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hcpu : L.cpu s0 ∈ Cs)
    (hI0 : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hBA0 : BufAt st T Cs H Sg Scs Z U s0) (htg : target ∈ T)
    (hD0 : DomInv st T s0) (hz : VcpuZ st T s0) (VK : SetVK st ar T s0 a0 target)
    (e : localtimer.handle_set_timer_local st ar s0 a0 n target = ok (true, s', a')) :
    AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s' := by
  obtain ⟨s3, a3, s4, a4, hB3, hBA3, -, esc, W, -, E, pin⟩ :=
    set_timer_local.allCoresBW hA IK hNt h0 hcpu hI0 hBA0 htg hD0 e
  have hS0 : (0#u64) ∉ Scs := by
    obtain ⟨-, -, hX0, -⟩ := hI0
    exact ObjsOK.zero_notScs hX0.1
  exact AllCores.exitZ hA IK hNt hS0 hz (VK s3 a3 s4 a4 pin esc) hB3 hBA3 esc W E

/-- (vk) **The timer-interrupt local entry ends in `AllCores`, no run
premise**: `allCoresExitZ` with `IrqVK` discharged (the run's VCPU words
kept, exported by `allCoresBW` from `sched.schedule.vkB`). Entry facts:
`h0`, `hcpu`, `hI0`, `hBA0`, `hD0`, `hz` (`VcpuZ`, P3). No named premise. -/
theorem timer_irq_local.allCoresExitZ2 (hA : P0.ArchTotal ar) (IK : IbKeep st ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    {s0 s' : S} {a0 a' : A} {irq : U64} {p : localtimer.TimerIrqPlan}
    (h0 : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hcpu : L.cpu s0 ∈ Cs)
    (hI0 : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hBA0 : BufAt st T Cs H Sg Scs Z U s0)
    (hD0 : DomInv st T s0) (hz : VcpuZ st T s0)
    (e : localtimer.handle_timer_irq_local st ar s0 a0 irq p = ok (true, s', a')) :
    AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s' := by
  obtain ⟨s3, a3, s4, a4, hB3, hBA3, -, esc, W, VK, E, -⟩ :=
    timer_irq_local.allCoresBW hA IK hNt h0 hcpu hI0 hBA0 hD0 e
  have hS0 : (0#u64) ∉ Scs := by
    obtain ⟨-, -, hX0, -⟩ := hI0
    exact ObjsOK.zero_notScs hX0.1
  exact AllCores.exitZ hA IK hNt hS0 hz VK hB3 hBA3 esc W E

/-- (vk) **The `TCB_SetTimer` local entry ends in `AllCores`, no run
premise**: `allCoresExitZ` with `SetVK` discharged. Entry facts: `h0`,
`hcpu`, `hI0`, `hBA0`, `htg`, `hD0`, `hz`. No named premise. -/
theorem set_timer_local.allCoresExitZ2 (hA : P0.ArchTotal ar) (IK : IbKeep st ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    {s0 s' : S} {a0 a' : A} {n : I64} {target : U64}
    (h0 : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hcpu : L.cpu s0 ∈ Cs)
    (hI0 : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hBA0 : BufAt st T Cs H Sg Scs Z U s0) (htg : target ∈ T)
    (hD0 : DomInv st T s0) (hz : VcpuZ st T s0)
    (e : localtimer.handle_set_timer_local st ar s0 a0 n target = ok (true, s', a')) :
    AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s' := by
  obtain ⟨s3, a3, s4, a4, hB3, hBA3, -, esc, W, VK, E, -⟩ :=
    set_timer_local.allCoresBW hA IK hNt h0 hcpu hI0 hBA0 htg hD0 e
  have hS0 : (0#u64) ∉ Scs := by
    obtain ⟨-, -, hX0, -⟩ := hI0
    exact ObjsOK.zero_notScs hX0.1
  exact AllCores.exitZ hA IK hNt hS0 hz VK hB3 hBA3 esc W E

/-- `VcpuEnt` without its `pl` (the facts that are the entry state's; module
docstring). -/
structure VcpuEntS (st : machine.Store S) [L : LawfulStore st] (T Ω : Set U64) (H : Heap) (Sg Scs : Set U64)
    (Z : U64 → Nat) (s0 : S) : Prop where
  heap : HeapOK H
  sets : T = H.tcbs ∧ Ω = H.omega ∧ Sg = H.frame
  scs : ∀ c ∈ Scs, H c = some (.sc (Z c))
  ksIn : ∀ p z, H p = some (.other z) → p.val + 2 ^ z ≤ (L.ksb s0).val ∨ (L.ksb s0).val + 13568 ≤ p.val ∨
    ((L.ksb s0).val ≤ p.val ∧ p.val + 2 ^ z ≤ (L.ksb s0).val + 13568)

/-- `VcpuEnt` from its static part and `VcpuPl` (the converse direction is
the field projection). -/
theorem VcpuEnt.of_static {s0 : S} (V : VcpuEntS st T Ω H Sg Scs Z s0) (P : VcpuPl st H Cs Rp Scs Nt Z s0) :
    VcpuEnt st T Cs Ω H Sg Rp Scs Nt Z s0 :=
  ⟨V.heap, V.sets, V.scs, V.ksIn, P⟩

end

end Fl4Proofs.P2.Stall

/-! ## P3: the entry facts at every reachable entry state -/

namespace Fl4Proofs.P2.Stall
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P3.Vs Fl4Proofs.P3.SInvR.G4 Fl4Proofs.P3.SInvR.G5

attribute [local instance] atCpuI

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **The VCPU entry facts at a joint-invariant state**: the core is one of
`Cs`, `VcpuEnt`'s static fields over `H`'s sets (`JKern.heap`,
`JKern.hksIn`), and every TCB's VCPU word zero (`JExt.vw`, `JPlaced.tcb`). -/
theorem ventS_of_JAtZ {A' : Type} {arI : machine.Arch A'} {AR : A' → Fl4Spec.Cr3 → Prop}
    {Zx : XSets} {H : Heap} {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64} {s : S} {a' : A'}
    {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Zx H Cx Ax Lst D s a' σ) :
    L.cpu s ∈ Cx ∧ VcpuEntS st (Heap.tcbs H) (Heap.omega H) H (Heap.frame H) (Heap.scs H) (Heap.scBits H) s ∧
      VcpuZ st (Heap.tcbs H) s := by
  refine ⟨J.kern.cpuCs, ⟨J.kern.heap, ⟨rfl, rfl, rfl⟩, fun c hc => ?_, J.kern.hksIn⟩, fun t ht => ?_⟩
  · obtain ⟨z, hz⟩ := hc
    have e : Heap.scBits H c = z := by unfold Heap.scBits; rw [hz]
    rw [e]; exact hz
  · obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact J.ext.vw t ((hJ.tcb t).2 ht)

set_option maxHeartbeats 4000000 in
/-- **The entry facts at every reachable entry state** (module docstring):
`kernel_entry_domInvU29`'s premises, no other. -/
theorem ventS_of_reachU17 {A : Type} (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop)
    (MR : A → Fl4Spec.MachineState → Prop) [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR)
    (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ) :
    ∃ (H : Heap) (Cs Ac : Set U64), L.cpu s ∈ Cs ∧
      EntryInv st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
        (Heap.scBits H) Ac s ∧ DomInv st (Heap.tcbs H) s ∧
      VcpuEntS st (Heap.tcbs H) (Heap.omega H) H (Heap.frame H) (Heap.scs H) (Heap.scBits H) s ∧
      VcpuZ st (Heap.tcbs H) s := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, ⟨hI, hD⟩, -⟩ :=
    kernel_entry_domInvU29 arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
  obtain ⟨hc, hV, hz⟩ := ventS_of_JAtZ J
  exact ⟨H, Cs, Ac, hc, hI, hD, hV, hz⟩

set_option maxHeartbeats 4000000 in
/-- **The timer-interrupt local entry ends in `AllCores` from every
reachable entry state** (module docstring): at a `JReachU17` state `s0`
there are `H Cs Ac` such that every accepted run of the local entry from
`AllCores` and `BufAt` over `H`'s sets ends in `AllCores`. Premises:
`kernel_entry_domInvU29`'s, `IK` (arch, as comb's), and the run premise
`IrqVK` [W]. -/
theorem timer_irq_local.allCoresExitJ {A : Type} (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop)
    (MR : A → Fl4Spec.MachineState → Prop) [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR)
    (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (IK : IbKeep st arI)
    {s0 : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s0 a σ) :
    ∃ (H : Heap) (Cs Ac : Set U64), ∀ (U : Set U64) (a0 a' : A) (s' : S) (irq : U64) (p : localtimer.TimerIrqPlan),
      AllCores st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
        (Heap.scBits H) Ac s0 →
      BufAt st (Heap.tcbs H) Cs H (Heap.frame H) (Heap.scs H) (Heap.scBits H) U s0 →
      IrqVK st arI (Heap.tcbs H) s0 a0 irq →
      localtimer.handle_timer_irq_local st arI s0 a0 irq p = ok (true, s', a') →
      AllCores st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
        (Heap.scBits H) Ac s' := by
  obtain ⟨H, Cs, Ac, hc, hI, hD, -, hz⟩ :=
    ventS_of_reachU17 arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
  exact ⟨H, Cs, Ac, fun U a0 a' s' irq p h0 hBA0 VK e =>
    timer_irq_local.allCoresExitZ hA IK (fun _ hn => hn) h0 hc hI hBA0 hD hz VK e⟩

set_option maxHeartbeats 4000000 in
/-- **The `TCB_SetTimer` local entry ends in `AllCores` from every reachable
entry state** (module docstring), as `timer_irq_local.allCoresExitJ`; inputs
also `target ∈ T`. Run premise `SetVK` [W]. -/
theorem set_timer_local.allCoresExitJ {A : Type} (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop)
    (MR : A → Fl4Spec.MachineState → Prop) [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR)
    (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (IK : IbKeep st arI)
    {s0 : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s0 a σ) :
    ∃ (H : Heap) (Cs Ac : Set U64), ∀ (U : Set U64) (a0 a' : A) (s' : S) (n : I64) (target : U64),
      AllCores st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
        (Heap.scBits H) Ac s0 →
      BufAt st (Heap.tcbs H) Cs H (Heap.frame H) (Heap.scs H) (Heap.scBits H) U s0 →
      target ∈ Heap.tcbs H →
      SetVK st arI (Heap.tcbs H) s0 a0 target →
      localtimer.handle_set_timer_local st arI s0 a0 n target = ok (true, s', a') →
      AllCores st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
        (Heap.scBits H) Ac s' := by
  obtain ⟨H, Cs, Ac, hc, hI, hD, -, hz⟩ :=
    ventS_of_reachU17 arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
  exact ⟨H, Cs, Ac, fun U a0 a' s' n target h0 hBA0 htg VK e =>
    set_timer_local.allCoresExitZ hA IK (fun _ hn => hn) h0 hc hI hBA0 htg hD hz VK e⟩


set_option maxHeartbeats 4000000 in
/-- (vk) **The timer-interrupt local entry ends in `AllCores` from every
reachable entry state, no run premise** (`allCoresExitJ` without `IrqVK`).
Premises: `kernel_entry_domInvU29`'s and `IK` (arch). -/
theorem timer_irq_local.allCoresExitJ2 {A : Type} (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop)
    (MR : A → Fl4Spec.MachineState → Prop) [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR)
    (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (IK : IbKeep st arI)
    {s0 : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s0 a σ) :
    ∃ (H : Heap) (Cs Ac : Set U64), ∀ (U : Set U64) (a0 a' : A) (s' : S) (irq : U64) (p : localtimer.TimerIrqPlan),
      AllCores st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
        (Heap.scBits H) Ac s0 →
      BufAt st (Heap.tcbs H) Cs H (Heap.frame H) (Heap.scs H) (Heap.scBits H) U s0 →
      localtimer.handle_timer_irq_local st arI s0 a0 irq p = ok (true, s', a') →
      AllCores st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
        (Heap.scBits H) Ac s' := by
  obtain ⟨H, Cs, Ac, hc, hI, hD, -, hz⟩ :=
    ventS_of_reachU17 arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
  exact ⟨H, Cs, Ac, fun U a0 a' s' irq p h0 hBA0 e =>
    timer_irq_local.allCoresExitZ2 hA IK (fun _ hn => hn) h0 hc hI hBA0 hD hz e⟩

set_option maxHeartbeats 4000000 in
/-- (vk) **The `TCB_SetTimer` local entry ends in `AllCores` from every
reachable entry state, no run premise** (`allCoresExitJ` without `SetVK`);
inputs also `target ∈ T`. -/
theorem set_timer_local.allCoresExitJ2 {A : Type} (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop)
    (MR : A → Fl4Spec.MachineState → Prop) [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR)
    (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (IK : IbKeep st arI)
    {s0 : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s0 a σ) :
    ∃ (H : Heap) (Cs Ac : Set U64), ∀ (U : Set U64) (a0 a' : A) (s' : S) (n : I64) (target : U64),
      AllCores st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
        (Heap.scBits H) Ac s0 →
      BufAt st (Heap.tcbs H) Cs H (Heap.frame H) (Heap.scs H) (Heap.scBits H) U s0 →
      target ∈ Heap.tcbs H →
      localtimer.handle_set_timer_local st arI s0 a0 n target = ok (true, s', a') →
      AllCores st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
        (Heap.scBits H) Ac s' := by
  obtain ⟨H, Cs, Ac, hc, hI, hD, -, hz⟩ :=
    ventS_of_reachU17 arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
  exact ⟨H, Cs, Ac, fun U a0 a' s' n target h0 hBA0 htg e =>
    set_timer_local.allCoresExitZ2 hA IK (fun _ hn => hn) h0 hc hI hBA0 htg hD hz e⟩

end

end Fl4Proofs.P2.Stall
