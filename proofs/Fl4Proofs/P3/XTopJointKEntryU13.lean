/-
P3 (issue #16, sd7; KENTRY-PLAN g7a-4, g7b-4 step 2): **`kernel_entry_reachU13`** =
g7a-3's `kernel_entry_reachU11` without D7 `idle` (INV-PLAN §1.U3L).

* `IdleVtS σ` (SpecInvSiE: the idle TCB's vtable slot holds the null cap, spec only) is
  carried with the reachable states: **`JReachU13 s a σ := JReachU3 s a σ ∧ IdleVtS σ`**
  (`JReachU3` itself unchanged). Every clause of U13 ends in `JReachU13` at the exit
  state: U11's exit gives `JReachU3`, and `IdleVtS σ'` comes from the whole-entry
  lemmas `kentry_idleVtS` / `kcall_idleVtS` / `fip_kcall_idleVtS` at the entry, with
  sg1's `SpecGlobS`, `IdleOutV` and ut8's `UtInv3` from `SInvX` (as `kentry_sinvX` /
  `kentry_zr` carry their facts).
* `KFinAtR13` = `KFinAtR11` without `idle`; `KFinEv13` likewise. U11's `idle`
  (`IdleVt` at the finish state) from `IdleVtS` there (`front_idleVtS` for the syscall
  finish and the trap / unknown-syscall events, `handleE_idleVtS` for the other events)
  and the idle TCB at the finish state's `JAtZR` (`JAtZR.idleTcb`: the idle word is in
  `T`, `SchedCore.idleT`, and a `T` thread is a spec TCB, `StateRel.tcb`): `idleVt_of`.

Premise removed (relative to U11): D7 `idle` [J] (in the syscall finish bundle and in
every event's). Added: none; the start-state fact `IdleVtS σ` is asked at one state, in
`JReachU13`'s base (`JReachU13.start`; it holds at boot, `boot_idleVtS`).
-/
import Fl4Proofs.P3.XTopJointKEntryU11
import Fl4Proofs.P3.SpecInvSiE
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

theorem sinvX_sg {σ : Fl4Spec.State Unit} (hX : SInvX σ) : SInvG.SpecGlobS σ := hX.1.1.1.1.1.1.1.1.sg

theorem sinvX_idleOut {σ : Fl4Spec.State Unit} (hX : SInvX σ) : SInvG.IdleOutV σ := hX.1.1.1.1.1.1.1.1.idleOut

/-- `IdleVt` from the spec-only vtable fact and the idle TCB. -/
theorem idleVt_of {σ : Fl4Spec.State Unit} (hx : ∃ x, σ.kheap σ.idleThread = some (.tcb x))
    (h : SInvIV.IdleVtS σ) : IdleVt σ := by
  obtain ⟨x, hx⟩ := hx
  refine ⟨x, hx, fun p asid e => ?_⟩
  have hc : SInvU.capAt σ (σ.idleThread, Fl4Spec.tcbCnodeIndex 1) = some x.tcbVtable := by
    unfold SInvU.capAt; rw [hx]; exact tcbCnodeMap_one x
  have e2 : x.tcbVtable = .nullCap := h _ hc
  rw [e2] at e; cases e

/-- `IdleVtS` at the exit of a kernel event. -/
theorem evOut_idleVtS {fip : Bool} {ev : Fl4Spec.Event} {σ σ' : Fl4Spec.State Unit} (hX : SInvX σ)
    (hV : SInvIV.IdleVtS σ) (h : EvOut fip ev σ σ') : SInvIV.IdleVtS σ' := by
  cases fip
  · unfold EvOut at h
    exact SInvIV.kcall_idleVtS true ev (sinvX_sg hX) (sinvX_idleOut hX) (sinvX_ut3 hX) hV _ h
  · unfold EvOut at h
    obtain ⟨w, hw, h⟩ := h
    exact SInvIV.fip_kcall_idleVtS σ.curThread ev (sinvX_sg hX) (sinvX_idleOut hX) (sinvX_ut3 hX) hV _ ⟨w, hw, h⟩

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`KFinAtR11` without `idle`.** -/
structure KFinAtR13 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop where
  arch : ArchSwF st arI Z.N Z.T Z.C Z.c
  archNd : ArchNdF st Z.N Z.T Z.C Z.c

/-- `KFinEv11` with `KFinAtR13`. -/
def KFinEv13 (AR : A → Fl4Spec.Cr3 → Prop) (ev : Fl4Spec.Event) (Kf : S → A → Prop) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ x ∈ ((Fl4Spec.NonDetE.handleE (Fl4Spec.fl4HandleEvent (Z := Unit) true ev)
      (fun _ => Fl4Spec.withoutPreemption Fl4Spec.preemptionPath)).run σ).1,
    ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
      Kf s' a' → JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 → KFinAtR13 (L := L) arI AR Z' H' Cs' s' a' x.2

variable {arI}

/-- **The idle thread is a spec TCB at a `JAtZR` state** (the idle word is a `T` thread). -/
theorem _root_.Fl4Proofs.P3.JAtZR.idleTcb {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) : ∃ x, σ.kheap σ.idleThread = some (.tcb x) := by
  obtain ⟨Q, R, hc, hs⟩ := J.xtop.fin.1.1.1.lists
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hth : Z.th (nodeW st s Z.c layout.node.IDLE_THREAD) = some .tcb := (hJ.tcb _).2 (J.zH.1 _ hc.idleT)
  obtain ⟨x, hkx, -⟩ := J.xtop.rel.2.1.1.tcb _ hth
  exact ⟨x, by rw [hs.idleTh]; exact hkx⟩

theorem KFinAtR13.to11 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : KFinAtR13 (L := L) arI AR Z H Cs s a σ) (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hV : SInvIV.IdleVtS σ) : KFinAtR11 (L := L) arI AR Z H Cs s a σ :=
  ⟨h.arch, h.archNd, idleVt_of J.idleTcb hV⟩

theorem KFinEv13.to11 {AR : A → Fl4Spec.Cr3 → Prop} {ev : Fl4Spec.Event} {Kf : S → A → Prop}
    {σ : Fl4Spec.State Unit} (hV : ∀ x ∈ ((Fl4Spec.NonDetE.handleE (Fl4Spec.fl4HandleEvent (Z := Unit) true ev)
      (fun _ => Fl4Spec.withoutPreemption Fl4Spec.preemptionPath)).run σ).1, SInvIV.IdleVtS x.2)
    (h : KFinEv13 (L := L) arI AR ev Kf σ) : KFinEv11 (L := L) arI AR ev Kf σ :=
  fun x hx Z' H' Cs' Ac' Lst' D' s' a' hK J' => (h x hx Z' H' Cs' Ac' Lst' D' s' a' hK J').to11 J' (hV x hx)

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **The reachable joint states carrying the idle vtable fact** (module docstring). -/
abbrev JReachU13 (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  JReachU3 (L := L) arI AR MR s a σ ∧ SInvIV.IdleVtS σ

variable {arI AR MR}

/-- The base: a start state of `JReachU3` with the idle vtable fact (one state). -/
theorem JReachU13.start {s : S} {a : A} {σ : Fl4Spec.State Unit} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hvx : VxE Z) (hX : SInvX σ)
    (hI : SInvIP σ) (hM : MR a σ.machineState) (hP : SInvUZ.UtPgR σ) (hV : SInvIV.IdleVtS σ) :
    JReachU13 (L := L) arI AR MR s a σ :=
  ⟨JReachU3.start J hvx hX hI hM hP, hV⟩

variable (arI AR MR)

end

end

end Fl4Proofs.P3.SInvR.G5
