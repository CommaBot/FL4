/-
P3 (FL4 #94 / #97, KENTRY-PLAN lt1): **the local timer entries beside the serial gate**:
`kernel_entry_reachU29T` (accepted) and `kernel_entry_reachU29TD` (declined).

fl4-sync's `local_set_timer` runs `localtimer.handle_set_timer_local … number target` with the
`target` its locked lookup of the caller's `CAP` register found (`lookup_slot_locked`, one
`localtimer.cspace_step` per level); `local_timer_irq` runs `localtimer.handle_timer_irq_local …
irq p` with the plan `plan_timer_irq` returned.

* **Accepted `TCB_SetTimer`** (P1 `set_timer_local_same`): the general entry
  `handle_syscall … SysCall` from the same state. Inputs of the clause: U29's syscall clause's own,
  and **fl4-sync's contract** that the general CSpace lookup of the `CAP` register, at the entry
  state, finds a slot holding `Thread target` (fl4-sync's walk is that lookup, level by level, with
  the slots it reads locked; the contract is an input of the entry like lcv's plan and lcs's
  `found`, not a state premise). `target ∈ T` is derived (`JAtZ.threadCapT`: the cap is in a slot
  of `Z.th`, `SlotsValid` types it).
* **Accepted timer interrupt** (P1 `irq_local_same`): `handle_interrupt_entry` from the same
  state, for any plan (the plan only narrows when it runs). Inputs: U29's interrupt clause's own.
* **Declined** (`kernel_entry_reachU29TD`): lcd's `kernel_entry_reachU29D` (its five entries,
  unchanged) and the two new entries. `TCB_SetTimer` declines as the other syscall-type entries
  (`set_timer_local_decline`: entry state or `LocalPre` with `RoT`), so `DeclSysU29` (`declSys_of`).
  The interrupt entry declines at the entry state (U29's interrupt clause at `(s, a, σ)` for the
  run from `(s, a1)`) or after one `update_timestamp` (`irq_local_decline`); then the general
  entry runs as from the entry state with the Arch value the update left (`irq_pre_same`), and
  the clause holds at the reachable joint state `(s, a0, tick σ)` (`arI.now a = ok (n0, a0)`,
  `jreachU17_tick`) for the run from `(s, a')` (`DeclIrqU29`). As in U29 the clause takes the
  hardware fact `IrqHw` of the entry as an input, here at `tick σ` (the interrupt's line read and
  the one extra clock reading, in the spec's order: `tick` first).

Premises added to either top: none (U29's verbatim). No existing top statement changed.
-/
import Fl4Proofs.P3.XTopJointKEntryU29D
import Fl4Proofs.P3.XTopJointKEntryRRF
import Fl4Proofs.P1.LocalTimer
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **A thread cap the current thread's lookup finds names a TCB of `H`** (`SlotsValid` at the
found slot of `Z.th`). -/
theorem JAtZ.threadCapT {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t c p : U64} {r : cspace.Resolved} (et : sched.cur_thread st s = ok t)
    (h : cspace.lookup_slot st s t c = ok (core.result.Result.Ok r))
    (hc : obj.Slot.cap st r.slot s = ok (capability.Cap.Thread p)) : p ∈ P1.Heap.tcbs H := by
  have htcb := J.curW_tcb et
  have hR := J.xtop.rel.2.1.1
  have hV := J.xtop.rel.2.1.2.1
  have HL := lookup_slot_refines Z.th s σ hR hV t htcb c
  rw [h, WP.spec_ok] at HL
  obtain ⟨e, -, hrel, hok⟩ := HL
  cases e with
  | ok v =>
    obtain ⟨sl, rest⟩ := v
    obtain ⟨hsl, -⟩ := hrel
    obtain ⟨pp, hp, hth, -⟩ := hok
    have hca : capAt (L.mem s) (cslotAddr sl) = ok (capability.Cap.Thread p) := by
      rw [← hsl, ← slot_cap_eq]; exact hc
    have hv : Z.th p = some .tcb := hV.abs ⟨pp, hp, Or.inl hth⟩ hca
    exact J.zH.1 p (J.thT p hv)
  | error _ => exact hrel.elim

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **fl4-sync's `TCB_SetTimer` contract** (an input of the entry): at the entry state the general
CSpace lookup of the current thread's `CAP` register finds a slot holding `Thread target`. -/
def SetTimerFound (s : S) (target : U64) : Prop :=
  ∀ t, sched.cur_thread st s = ok t → ∃ r : cspace.Resolved,
    cspace.lookup_slot st s t (L.mem s (regA t layout.reg.CAP)) = ok (core.result.Result.Ok r) ∧
    obj.Slot.cap st r.slot s = ok (capability.Cap.Thread target)

end

end

end Fl4Proofs.P3.SInvR.G5
