/-
P2 (comb): **the local entries that call `schedule` end in `AllCores`, with
`VcpuEnt` the only named premise.**

Combines wire's walks (`P2/EntryWire.lean`: `hR`, `hS0`, `hKS` discharged,
entry fact `hD0 : DomInv`) with sib's exit (`P2/EntryVcpu.lean`:
`AllCores.exitV`, `SchIb` discharged by `schIb_holds`, `VcpuUsr` derived from
`VcpuEnt` at the entry). wire's `B` wrappers export the body's `FootB` from
the entry to `schedule`'s start, which `AllCores.exitV` takes.

* **`timer_irq_local.allCoresExitF`**, **`set_timer_local.allCoresExitF`**:
  an accepted run of the local entry, from `AllCores` at the entry, ends in
  `AllCores`.

Entry facts (inputs): `AllCores s0`, `L.cpu s0 ∈ Cs`, P1's `EntryInv` and
`BufAt` at the entry (`hI0`, `hBA0`), `hD0 : DomInv st T s0`.
Named premise: `V : VcpuEnt … s0` **[P]** (P3's placement facts over P1's
heap at the entry state; `P2/EntryVcpu.lean`).

**Note (vk, 2026-11-26): `VcpuEnt` is unsatisfiable.** Its `pl : VcpuPl … s0`
quantifies over every `s` with `Fr0 s0 s` and `BXI s`; `VcpuPl.bound` fails
at `s := L.wr s0 (t + 3664) x` for a TCB `t` and any `x ≠ 0` with
`H x ≠ some (.other 15)` (e.g. a TCB address): the write is a `KW` word, so
`Fr0`, and no invariant of `BXI` reads a TCB's VCPU word (vent's finding,
`P2/EntryVent.lean`; rechecked by vk). So the theorems taking `VcpuEnt`
(`timer_irq_local.allCoresExitF`, `set_timer_local.allCoresExitF`) hold
vacuously; they are superseded by `…allCoresExitJ2` (`P2/EntryVent.lean`,
no run premise) and kept only for reference.
-/
import Fl4Proofs.P2.EntryWire
import Fl4Proofs.P2.EntryVcpu
open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace Fl4Proofs.P2.Stall
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

attribute [local instance] atCpuI

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}
variable {A : Type _} {ar : machine.Arch A}

/-- **The timer-interrupt local entry ends in `AllCores`** at the entry's
exit. Entry facts: `h0`, `hcpu`, `hI0`, `hBA0`, `hD0`. Named premise: `V`
[P] (`VcpuEnt`). -/
theorem timer_irq_local.allCoresExitF (hA : P0.ArchTotal ar) (IK : IbKeep st ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    {s0 s' : S} {a0 a' : A} {irq : U64} {p : localtimer.TimerIrqPlan}
    (h0 : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hcpu : L.cpu s0 ∈ Cs)
    (hI0 : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hBA0 : BufAt st T Cs H Sg Scs Z U s0)
    (hD0 : DomInv st T s0)
    (V : VcpuEnt st T Cs Ω H Sg Rp Scs Nt Z s0)
    (e : localtimer.handle_timer_irq_local st ar s0 a0 irq p = ok (true, s', a')) :
    AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s' := by
  obtain ⟨s3, a3, s4, a4, hB3, hBA3, B03, esc, W, -, E, -⟩ :=
    timer_irq_local.allCoresBW hA IK hNt h0 hcpu hI0 hBA0 hD0 e
  have hS0 : (0#u64) ∉ Scs := by
    obtain ⟨-, -, hX0, -⟩ := hI0
    exact ObjsOK.zero_notScs hX0.1
  exact AllCores.exitV hA IK hNt hS0 V hI0 B03 hB3 hBA3 esc W E

/-- **The `TCB_SetTimer` local entry ends in `AllCores`** at the entry's
exit. Entry facts: `h0`, `hcpu`, `hI0`, `hBA0`, `htg`, `hD0`. Named premise:
`V` [P] (`VcpuEnt`). -/
theorem set_timer_local.allCoresExitF (hA : P0.ArchTotal ar) (IK : IbKeep st ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    {s0 s' : S} {a0 a' : A} {n : I64} {target : U64}
    (h0 : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hcpu : L.cpu s0 ∈ Cs)
    (hI0 : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hBA0 : BufAt st T Cs H Sg Scs Z U s0) (htg : target ∈ T)
    (hD0 : DomInv st T s0)
    (V : VcpuEnt st T Cs Ω H Sg Rp Scs Nt Z s0)
    (e : localtimer.handle_set_timer_local st ar s0 a0 n target = ok (true, s', a')) :
    AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s' := by
  obtain ⟨s3, a3, s4, a4, hB3, hBA3, B03, esc, W, -, E, -⟩ :=
    set_timer_local.allCoresBW hA IK hNt h0 hcpu hI0 hBA0 htg hD0 e
  have hS0 : (0#u64) ∉ Scs := by
    obtain ⟨-, -, hX0, -⟩ := hI0
    exact ObjsOK.zero_notScs hX0.1
  exact AllCores.exitV hA IK hNt hS0 V hI0 B03 hB3 hBA3 esc W E

end

end Fl4Proofs.P2.Stall
