/-
P2 (tmofr gen 3): **the P2 stall tops tied to P3.**

## What P3 gives, what it does not

* `XG` (P1 `QueueEntry`): `∃ s0, EntAt P3Ok s0 ∧ Fr0 s0 s`. In `stallAt.viewsT` /
  `stallAt.allT` the predicate `P3Ok` is a free parameter that occurs in no
  conclusion, so `XG` holds at **every** state with `P3Ok := fun _ => True`
  (`xg_triv`: `s0 := s`, `Ent s s` and `Fr0 s s` by reflexivity). Not a P3 fact:
  the premise was vacuous.
* `TmoCap` [P] (`hcap`) at the view of the stalled core `d`: **discharged at
  every `JAtZ` state**, for every `d` whose current thread is a TCB of `H`.
  `tmoCapW_of_JAtZt` (`JAtZ.timeoutTyped` at slot 4 of any TCB of `H`, through
  `JPlaced.tcb`) gives the cap typed at `s`; `tmoCap_of_capW` carries it to every
  state the budget check reaches (SC words — `Ω` by `XInv.scW` — and the core's
  node words miss the TCB's slot words 128/136); `tmoCap_view` is the view at `d`.
* Of `stallAt.viewsT`'s per-core premises, the **executing core's**
  (`c0 = L.cpu s`) follow from P3 at a reachable entry state
  (`kernel_entry_reachU29`'s `J` and `SInvX σ`):
  - `idleSc_of_JAtZ`: `IdleSc c0` (`SchedSpec.idleSc`, `SchedSpec.tcb`'s SC word of
    the idle thread, l4v `valid_idle`'s `tcb_sched_context = Some idle_sc`,
    `SInvI.vi_idle`);
  - `curNB_of_JAtZ`: `c0`'s current thread is not `Blocked` (ct = idle: `TS_IDLE`;
    otherwise `SInvX.entered` and `JAtZ.curRunnable`: runnable state word);
  - `CoreInv c0` (`EntryInv.toView` of `JAtZ.entryInv` and `idleSc_of_JAtZ`), `hnq` at
    `c0` (`JAtZ.curQ0`), `hidS` at `c0` (`JAtZ.idleTS`).
* **Not derivable from P3** (named in the theorems below, P2's all-core
  invariant `AllCores` supplies them): every fact about a core `c ≠ c0`'s node
  words (`CUR_THREAD`, `IDLE_THREAD`, `SCHED_ACTION`, `CUR_SC`, `IDLE_SC`) and
  the threads they name. P3's relation ties only the executing core's node to
  the spec (`SchedRel … Z.c`, `SchedCore.cur : L.cpu s = Z.c`; `JKern.cur`); the
  spec (l4v's abstract seL4) has one current thread, one idle thread and one
  scheduler action, and no counterpart of other cores' nodes. Hence:
  `EntryInv` at the view of `d ≠ c0`, `IdleSc d`, `hnq`/`hidS` at `d`, the other
  cores' `CoreInv` and `curNB`, and `hown`/`hactK` (the set `OtherK d` is made of
  the other cores' idle/current/action threads; even for `d = c0` it names
  only cores `≠ c0`).

## Here

* `xg_triv`, `tmoCap_of_capW`, `tmoCap_view`, `tmoCapW_of_JAtZt`.
* **`stallAt.allZ`**: at every `JAtZ` state (mid-entry included), a remote stall
  of `d` from `AllCores` over `H`'s sets ends in `AllCores`: `stallAt.allT` with
  `XG` and `TmoCap` [P] gone. Input `AllCores` only.
* **`stallAt.allJ`**: from every `JReachU17` entry state, premises
  `kernel_entry_domInvU29`'s only: some `H Cs Ac` with `L.cpu s ∈ Cs`, P1's
  `EntryInv`, and every stall of a `d ∈ Cs` from `AllCores` ends in `AllCores`.
* **`stallAt.viewsZ`**: `stallAt.viewsT` at a `JAtZ` state without `XG` and
  `TmoCap`.
* **`stallAt.viewsJ`** (remote `d ≠ c0`) and **`stallAt.viewsJ0`** (`d = c0`):
  from every `JReachU17` entry state, premises `kernel_entry_reachU29`'s
  (= `kernel_entry_domInvU29`'s); the executing core's facts discharged; left:
  the facts about cores `≠ c0` listed above.

No existing statement changed.
-/
import Fl4Proofs.P2.AllCores
import Fl4Proofs.P2.FootN5
import Fl4Proofs.P1.QueueFootS
import Fl4Proofs.P2.StallFull
import Fl4Proofs.P2.TmoFrC
import Fl4Proofs.P3.XTopJointDomInv29
open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace Fl4Proofs.P2.Stall
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

attribute [local instance] atCpuI

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- **`XG` holds at every state** for the entry predicate `fun _ => True`. -/
theorem xg_triv (s : S) : XG st T Cs Ω H Sg Scs Z (fun _ => True) s :=
  EntAt.xg ⟨s, trivial, WritesIn.refl _ _⟩

end

open Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P3.Vs Fl4Proofs.P3.SInvR.G4 Fl4Proofs.P3.SInvR.G5

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **Every TCB's timeout handler cap is typed at a `JAtZ` state**
(`tmoCapW_of_JAtZ` for any TCB of `H`, not only the current thread). -/
theorem tmoCapW_of_JAtZt {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} {Zx : XSets} {H : Heap}
    {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Zx H Cx Ax Lst D s a σ) {t : U64} (ht : t ∈ Heap.tcbs H) :
    TmoCapW st H (Heap.replies H) (Heap.ntfns H) s t := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hsl : IsSlot Zx.th (core.num.U64.wrapping_add t 128#u64) :=
    ⟨t, 4, Or.inr ⟨(hJ.tcb t).2 ht, by simp [tcbSlots]⟩, slotOf4 _⟩
  have h1 := J.timeoutTyped hsl
  rw [slot_cap_dec, tmoSlot8_eq] at h1
  exact h1

end

end Fl4Proofs.P2.Stall
