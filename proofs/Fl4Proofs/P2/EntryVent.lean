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

end Fl4Proofs.P2.Stall
