/-
P3 (DESIGN.md §9), CSpace: **the deletion loop at `J`, by its steps**: the
loop run with a `JAtZ`-carrying invariant (`WJ`) and the readiness of the
slot to be emptied (`RdJ`, `EmptyReady`: the objects of the slot's cap dead
or covered by another cap), so that one cap's deletion at `J` (`JDelHyp`)
follows from premises about single steps of the loop (`DelHypsWR`, DelW),
some of them proved here.

* `WJ Z H Cs kb`: `JAtZ` at the sets `Z.mv G V` (the MDB ghost the loop's,
  the VSpace sets, the active SCs, the call stacks and the dead set chosen),
  P1's heap `H`, the cores `Cs` and the kernel-state base `kb` fixed;
  `EJ`: with `DelE`. `RdJ H`: `EmptyReady` (XTopJointEmpty).
* `WJR`: `WJ` and ScPPR's `PPR0` (what the loop's preemption points need of
  a zero consumed time), the loop's invariant; `EJ`: `WJR` with `DelE`.
* `JDelHyp`: one cap's deletion at `EJ` (`DelHypW`'s shape, the revoke's and
  the delete's premise); `JPreemptHyp`: the preemption point at `WJR`
  (proved, XTopJointPP's `jPreemptHyp_of`, from the platform's [P] facts).
* Proved steps: a notification cap's finalisation (`jFinAt_ntfn`: P3's
  `finNtfnJ`, P1's `fin_cap_ntfn.dead`, or `fin_idle` and another cap,
  `other_ntfn`); the readiness of the caps finalised without effect but
  zombies (`rdTrivJ`: the trivial caps cover nothing; a CNode cap's CNode is
  dead for `DeadP`, `cnode_ready`); the empty of a CNode slot
  (`emptyHypJ`: `emptyJR`, the untyped caps' facts after from the
  emptied slot's liveness readiness, `RdL`'s `ReadyLive`).
* The loop's readiness `RdL`: `RdJ` (`EmptyReady`) and `ReadyLive`
  (XTopJointLive: the other slots in use and the debug list's head live
  without the slot), asked only on the removable path (DelW's `RmOK`); from
  `LiveJ` [J] (`JDelParts.live`): `finJL`, `rdTrivJL`, `delete_oneJ`.
* Named premises [J] (`JDelParts`), each one step of the loop at `WJ`:
  `JFinAtF` (a final object cap's finalisation, but notification, IRQ
  handler, endpoint, frame and IO port caps, with `RdJ` after; a non-final one's is `jFin_nonfinal`:
  nothing, the slot ready by another cap alike it),
  `LiveJ` (XTopJointLive: l4v `if_unsafe_then_cap`,
  `if_live_then_nonz_cap`, the zombies' slots and TCB; it gives
  `ReadyLive`, `JZombieTcbHyp` (`jZombieTcbHyp_of_live`, then
  `jRdTrivHyp_of`) and `JThreadFinHyps.utTcb` (`utTcb_of_live`)).
* The frame and IO port caps' finalisation, final or not (`jFinAt_frio`,
  XTopJointFinFrIo): an unmapped frame's and an unowned IO port cap's do
  nothing; a VSpace-mapped frame's unmap by `jFrMap_of` (XTopJointFinVs's
  `JAtZ.finVsJb`, from `ArchRefines` [P], `JVsCapsHyp` [J] and
  `JVsApartHyp` [J]), the VT-x work (EPT-mapped frames, owned IO ports) by
  `jFrVt_of` (XTopJointFinVtJ's `JAtZ.frVtJ`, from `ARKeep` [P] and
  `JVtHyps` [J]); the slot ready after (a frame cap's memory holds no
  object of `H` but `other` ones: `JPlaced.cobj`, ScPlace's `CapObjH`; an
  IO port cap is not physical).
* A final VT-x object cap's finalisation (`jFinAt_vt`, XTopJointFinVtJ): an
  EPT cap but a mapped root's (`EptK`: nothing, or `ept::unmap` of a mapped
  non-root table's entry), a VCPU cap (`VcpuK`: `vcpu::finalise`, its unlink
  from the VCPU list); the spec keeps its state, FL4 writes VT-x words and the
  list's head word (`JAtZ.vtHJ`); the slot ready after (the object apart from
  `H`'s); from `ArchRefines` [P], `ARKeep` [P] and `JVtHyps` [J].
* A final mapped EPT root cap's finalisation (`jFinAt_eptRoot`, `EptRootK`):
  FL4's `delete_asid` of the root clears its guest-tagged ASID pool entry,
  as the spec's `arch_finalise_cap` of a mapped level-0 `EPTCap` does
  (`deleteAsid`); XTopJointFinVs's `JAtZ.finVsJb` (VsFin's `fin_ept_root`),
  the slot ready after (the EPT root apart from `H`'s objects,
  `JAtZ.ept_obj`); from `ArchRefines` [P], `JVsCapsHyp` [J], `JVsApartHyp` [J]
  and `JVtHyps` [J] (the root non-null: `JAtZ.ept_ne0`).
* A final IRQ handler cap's finalisation (`jFinAt_irq`, as XTopFinIrq):
  the IRQ node slot's cap deleted, null or a notification cap by
  `delete_oneJ` (`jFinNtfnK`, every slot kept, then `emptyHypJ`); from
  `JIrqSlotHyp` (the node's slots null or notification caps; from the
  spec's, `JSpecIrqNodeHyp` [J], by `jIrqSlotHyp_of`), `LiveJ` and
  `JAtZ.intL`.
* A final endpoint cap's finalisation (`jFinAt_ep`): XTopJointFinEp's
  `JAtZ.finEpJ` (`cancel_all_ipc`, `JAtZ` after), the endpoint dead after
  (P1's `fin_cap_ep.dead`, `JAtZ.ep_ready`); from `RecvReplyHyp` [J]
  (ScSignalBoundJ, l4v `valid_replies`: the replies it frees, of threads
  blocked receiving, are detached and unlinked), carried by `JDelParts` at
  every `P1.Heap` and set of cores.
* A final reply cap's finalisation (`jFinAt_reply`): XTopJointFinReply's
  `JAtZ.finReplyJ` (none, or the receiver's `cancel_ipc`, proved; the
  `reply_remove` of a thread blocked on the reply, `jReplyRemoveHyp`:
  XTopJointRemove's `JAtZ.replyRemoveJ`),
  the reply dead after (P1's `fin_cap_reply.dead`, `JAtZ.reply_ready`); with
  `RecvReplyHyp` [J] and `P0.ArchTotal` [P].
* A final native VSpace cap's finalisation (`jFinAt_vs`: page table, page
  directory, PDPT, PML4, ASID pool caps): XTopJointFinVs's `JAtZ.finVsJ`
  (`JAtZ` after at the same sets, the spec's frame `ArFr`), the slot ready
  (`JAtZ.vs_ready`: no object of `H` but `other` ones in the cap's frame);
  from `ArchRefines` [P], `JVsCapsHyp` [J] (l4v `valid_cap`) and
  `JVsApartHyp` [J] (the ASID table apart from `H`'s SCs outside `Z.C`),
  `JDelParts` fields.
* A final SC cap's finalisation (`jFinAt_sc`): XTopJointFinSc's
  `JScFinHyp` (the finalisation at `J`, by `jScFin_of` from the proved SC
  steps and `jYieldToHyp_of` from the thread's [P] `ticks`), the SC dead after
  (P1's `fin_cap_sc.dead`, `JAtZ.sc_ready`); the cap's SC the spec's of its
  size, not the idle SC, by `JAtZ.scCap` (`jScCapHyp_of`). The SC
  may be the current SC (XTopJointFinSc's docstring).
* A final thread cap's finalisation (`jFinAt_thread`): XTopJointFinThread's
  `JAtZ.finThreadJ` (the notification unbind, timer removal, `unbind_tcb`,
  `complete_yield_to`, `suspend` (its `cancel_ipc`: send, notification and
  reply proved, receive from `RecvReplyHyp` [J]), and
  debug-list removal proved; the narrow facts from `JThreadFinHyps` [J]/[P]), the slots by P1's
  `fin_cap_thread.slots`, the thread dead after (P1's `fin_cap_thread.dead`,
  `JAtZ.tcb_ready`).
* A zombie written over a cap alike it (`jZombieHyp`, XTopJointZombie's
  `JAtZ.zombieJCore`); a zombie swapped with its first slot (`jSwapHyp`,
  `JAtZ.swapJCore`, the zombie's first slot off the childless untyped
  regions by `ut_free`); a zombie's slot ready (`jRdTrivHyp_of`,
  `JAtZ.zombie_ready`: a CNode zombie's CNode dead for `DeadP`, a TCB
  zombie's TCB by `JZombieTcbHyp`).
* The empty of a ready slot (`emptyHypJ`): a CNode slot by `emptyJR`, a TCB
  slot by `emptyJRT` (a step changing the TCB's caps only, `KeepCT`), both
  with `RdL`'s `ReadyLive` for the untyped caps' facts after.
* `JDelHyp.of_parts`: `JDelHyp` from `JDelParts`, `JPreemptHyp` and
  `JPostDelHyp` (`delHyp_fullWR` at `WJR`; `JPreemptHyp` from the platform,
  XTopJointPP's `jPreemptHyp_of`; `JPostDelHyp` from the kernel-state
  layout, XTopJointPost's `jPostDelHyp_of`); `PPR0` kept by the slot edits
  (`PPK.of_cnK`) and by the finalisations (`jFinPPHyp`: SpecPPR's
  `ppr0_finaliseCap`, the spec's `finalise_cap` keeps it from `Inv`).
-/
import Fl4Proofs.P3.XTopJointStep
import Fl4Proofs.P3.XTopJointEmptyUt
import Fl4Proofs.P3.XTopJointFinEp
import Fl4Proofs.P3.XTopJointFinReply
import Fl4Proofs.P3.XTopJointFinVs
import Fl4Proofs.P3.XTopJointFinFrIo
import Fl4Proofs.P3.XTopJointFinVtJ
import Fl4Proofs.P3.XTopJointFinSc
import Fl4Proofs.P3.XTopJointFinThread
import Fl4Proofs.P3.XTopJointRemove
import Fl4Proofs.P3.IntInv
import Fl4Proofs.P3.XTopJointZombie
import Fl4Proofs.P3.XTopJointLive
import Fl4Proofs.P3.ScPPR
import Fl4Proofs.P3.SpecPPR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The deletion's invariant at `J`** (module docstring). -/
def WJ (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (G : MdbGhost) : Prop :=
  ∃ (V : XVs) (Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac Lst D s a σ ∧ L.ksb s = kb ∧ Vs.NoSwitch σ

/-- `WJ` and `PPR0` (the deletion loop's invariant at `J`, XTopJointPP). -/
def WJR (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (G : MdbGhost) : Prop :=
  ∃ (V : XVs) (Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac Lst D s a σ ∧ L.ksb s = kb ∧ Vs.NoSwitch σ ∧ PPR0 σ

theorem WJR.wj {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64} {kb : U64} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {G : MdbGhost} (h : WJR (L := L) arI AR Z H Cs kb s a σ G) :
    WJ (L := L) arI AR Z H Cs kb s a σ G :=
  let ⟨V, Ac, Lst, D, J, hk, hn, _⟩ := h; ⟨V, Ac, Lst, D, J, hk, hn⟩

theorem WJ.wjr {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64} {kb : U64} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {G : MdbGhost} (h : WJ (L := L) arI AR Z H Cs kb s a σ G) (hp : PPR0 σ) :
    WJR (L := L) arI AR Z H Cs kb s a σ G :=
  let ⟨V, Ac, Lst, D, J, hk, hn⟩ := h; ⟨V, Ac, Lst, D, J, hk, hn, hp⟩

theorem WJR.pp {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64} {kb : U64} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {G : MdbGhost} (h : WJR (L := L) arI AR Z H Cs kb s a σ G) : PPR0 σ :=
  let ⟨_, _, _, _, _, _, _, hp⟩ := h; hp

/-- `WJR` with `DelE` (the CSpace deletion's invariant and fuel bound). -/
abbrev EJ (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (K : Nat) (s : S)
    (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) : Prop :=
  DelE (L := L) Z.th K s σ ∧ WJR (L := L) arI AR Z H Cs kb s a σ G

/-- **The deletion's state after a preemption at `J`**: the post of a
preempting preemption point from `WJ` (FL4's `preemption_point` returning
`Preempted`, a preempting outcome of the spec's). Not `WJ` itself: the
preemption point updates the time, and the current SC's budget may then be
exhausted (`JAtZ`'s `OffOK` false), which the caller's
`mcs_preemption_point` charges before `schedule`. -/
def WJP (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (G : MdbGhost) : Prop :=
  ∃ (s0 : S) (a0 : A) (σ0 : Fl4Spec.State Unit), WJ (L := L) arI AR Z H Cs kb s0 a0 σ0 G ∧
    sched.preemption_point st arI s0 a0 = ok (.Err .Preempted, s, a) ∧
    (.error (), σ) ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ0).1 ∧
    DomRel (L.mem s) (L.ksb s) σ ∧ MdbOKV (L.ksb s) (L.mem s) G

/-- `WJP` with `DelE`. -/
abbrev EJP (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (K : Nat) (s : S)
    (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) : Prop :=
  DelE (L := L) Z.th K s σ ∧ WJP (L := L) arI AR Z H Cs kb s a σ G

/-- **The readiness at `J`** of a slot to be emptied: `EmptyReady`. -/
abbrev RdJ (H : P1.Heap) : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop :=
  fun s _ _ G x => EmptyReady (L := L) H G s x

/-- **The deletion loop's readiness at `J`**: `RdJ` and the liveness
readiness `ReadyLive` (XTopJointLive: the other slots in use and the debug
list's head live without the slot). -/
abbrev RdL (th : TypedHeap) (H : P1.Heap) : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop :=
  fun s _ σ G x => EmptyReady (L := L) H G s x ∧ ReadyLive (L := L) th s σ G x

/-- **One cap's deletion at `J`**: FL4's exposed `delete` of an MDB slot from
`EJ` (a `JAtZ` state at the sets `Z.mv G V`), a spec outcome of `cap_delete`
of the same kind, the CSpace relation, `EJ` after (`EJP` after a
preemption) and the ghost step (`DelHypW`). Derived from `JDelParts`
(`JDelHyp.of_parts`). -/
def JDelHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (K : Nat), Z.th = th →
    (∀ p r, th p = some (.cnode r) → 2 ^ r ≤ K) → 6 ≤ K →
    DelHypW (L := L) arI psiD th (EJ (L := L) arI AR Z H Cs kb K) (EJP (L := L) arI AR Z H Cs kb K)

/-- **The preemption point at `J`**: from `WJR` (a `JAtZ` state with
`PPR0`), the cap slots kept, a spec outcome of the same kind, the CSpace
relation and `WJR` after at the same MDB ghost, `WJP` after a preemption
(`PPHypDW`). FL4's preemption point runs `update_timestamp` (the SC and
time fields). Proved from the platform's [P] facts (XTopJointPP's
`jPreemptHyp_of`). -/
def JPreemptHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64), Z.th = th →
    PPHypDW (L := L) arI (WJR (L := L) arI AR Z H Cs kb) (WJP (L := L) arI AR Z H Cs kb) th

/-- **A cap's finalisation keeps `PPR0`**: from a `JAtZ` state, every
outcome of the spec's `finalise_cap` of a cap in a slot keeps `PPR0`
(ScPPR: at a zero consumed time, the current SC's head ready when active,
its threads outside the release queue). Proved (`jFinPPHyp`, SpecPPR's
`ppr0_finaliseCap`, from `Inv`): `finalise_cap` keeps the time, the consumed
time and the current SC, changes the current SC's refills only by
`sched_context_set_inactive` (the SC then inactive), never enqueues a thread
for release, and binds a thread to the current SC only by `reply_remove`'s
donation to a caller blocked on the reply, hence outside the release queue
(`Inv.rel`: its members are runnable). -/
def JFinPPHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit), Z.th = th → JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ →
    ∀ (sl : Fl4Spec.CslotPtr) (c : capability.Cap), AbsSlot th sl → capAt (L.mem s) (cslotAddr sl) = ok c →
      FinObjKind c → ∀ (x : Fl4Spec.Cap × Fl4Spec.Cap) (σ' : Fl4Spec.State Unit),
      (x, σ') ∈ (Fl4Spec.finaliseCap (Z := Unit) (absCap c) (decide (Fl4Spec.isFinalCap' (absCap c) σ)) σ).1 →
      PPR0 σ → PPR0 σ'

theorem jFinPPHyp {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} : JFinPPHyp (L := L) arI AR th :=
  fun _ _ _ _ _ _ _ _ σ _ J _ _ _ _ _ x σ' hx hP => PPS.ppr0_finaliseCap (x := (x, σ')) J.inv hx hP

/-! ## The named steps -/

/-- A notification cap. -/
def NtfnK (c : capability.Cap) : Prop := ∃ p b w r, c = .Notification p b w r

/-- **Hypothesis: the finalisation at `J` of the object caps of the kinds
`Kd`** [J]: `FinObjHypWR` at `WJ` with `RdJ` after, for those kinds (the
notification caps proved, `jFinAt_ntfn`). -/
def JFinAt (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (Kd : capability.Cap → Prop) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64), Z.th = th →
    FinObjHypWRK (L := L) arI (WJ (L := L) arI AR Z H Cs kb) (RdJ (L := L) (A := A) H) th Kd

/-- **Hypothesis: a final cap's finalisation at `J`, for the object caps of
the kinds `Kd`** [J]: `JFinAt` for final caps only (a non-final cap's,
`jFin_nonfinal`, is proved for every object cap but frames and IO port caps). -/
def JFinAtF (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (Kd : capability.Cap → Prop) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64), Z.th = th →
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (c : capability.Cap),
    DState (L := L) th s σ G → WJ (L := L) arI AR Z H Cs kb s a σ G → AbsSlot th sl →
    capAt (L.mem s) (cslotAddr sl) = ok c → FinObjKind c → Kd c → Fl4Spec.isFinalCap' (absCap c) σ →
    objects.finalise_cap st arI s a c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) false ⦃ r =>
      r.1.1 = finRem c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) ∧ CleanCap r.1.2 ∧ CapWf r.1.2 ∧
      ∃ σ' G', ((absCap r.1.1, absCap r.1.2), σ') ∈
          (Fl4Spec.finaliseCap (Z := Unit) (absCap c) (decide (Fl4Spec.isFinalCap' (absCap c) σ)) σ).1 ∧
        DState (L := L) th r.2.1 σ' G' ∧ capV (L.mem r.2.1) (cslotAddr sl) = c ∧
        (∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem r.2.1) y = capV (L.mem s) y ∨
          (capV (L.mem r.2.1) y = .Null ∧ isZb (capV (L.mem s) y) = false)) ∧
        MdbStep (L.mem s) G (L.mem r.2.1) G' ∧ WJ (L := L) arI AR Z H Cs kb r.2.1 r.2.2 σ' G' ∧
        RdJ (L := L) (A := A) H r.2.1 r.2.2 σ' G' (cslotAddr sl) ⦄

/-- A frame cap or an IO port cap (finalised with work when not final). -/
def FrIoK (c : capability.Cap) : Prop := isFrame c = true ∨ ∃ f l o, c = .IoPort f l o

/-- **A VSpace-mapped frame cap's finalisation at `J`** (`FrMapK`, final or
not: FL4's `vspace::unmap_page`, the spec's `unmap_page`), `WJ` after (the
readiness from `JPlaced.cobj`); proved, `jFrMap_of`. -/
def JFrMapHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64), Z.th = th →
    FinObjHypWRK (L := L) arI (WJ (L := L) arI AR Z H Cs kb) (fun _ _ _ _ _ => True) th FrMapK

/-- **The VT-x work of a finalisation at `J`** (`FrVtK`: an
EPT-mapped frame cap's `ept::unmap`, an owned IO port cap's
`vcpu::revoke_ports`; outside the semantic scope, DESIGN §5, as `XFinHyps.vm`
and `XFinHyps.io` at `XTop`), `WJ` after. Proved: `jFrVt_of`. -/
def JFrVtHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64), Z.th = th →
    FinObjHypWRK (L := L) arI (WJ (L := L) arI AR Z H Cs kb) (fun _ _ _ _ _ => True) th FrVtK

/-- **A zombie's slot is ready at `J`** (`RdTrivHyp` for zombies; their
finalisation leaves the state as it is): the objects in the zombie's range
(its CNode, or its TCB) dead. Proved from `JZombieTcbHyp`
(`jRdTrivHyp_of`, XTopJointZombie's `JAtZ.zombie_ready`): a CNode zombie's
CNode is dead for `DeadP` (`H`'s `other`). -/
def JRdTrivHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64), Z.th = th →
    ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (p zt n : U64),
      DState (L := L) th s σ G → WJ (L := L) arI AR Z H Cs kb s a σ G → AbsSlot th sl →
      capAt (L.mem s) (cslotAddr sl) = ok (.Zombie p zt n) →
      RdJ (L := L) (A := A) H s a σ G (cslotAddr sl)

/-- **A zombie written over a cap alike it keeps `WJ`** (`ZombieHypW` at
`WJ`). Proved, `jZombieHyp` (XTopJointZombie's `JAtZ.zombieJCore`, by
`jowes_slotD`: the written slot was linked before, so no `DestLive` is
read; the zombie covers what the cap it replaces covered). -/
def JZombieHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64), Z.th = th →
    ZombieHypW (L := L) (A := A) (WJ (L := L) arI AR Z H Cs kb) th

/-- **Hypothesis: a TCB zombie's TCB is dead at `J`** [J]: at `WJ`, the TCB
of a zombie of type 65 in a slot is `DeadP` (inactive, no SC, no bound
notification, neither the scheduler action nor idle). The thread cap's
finalisation leaves it so (P1's `fin_cap_thread.dead`, `jFinAt_thread`), and
nothing names the TCB after, but `JAtZ` has no field on zombies' objects
(a zombie outlives a preempted deletion, so the fact must hold at every
kernel entry: an invariant beside `JAtZ`, kept by every kernel step). l4v:
`rec_del` relies on the zombie's TCB not being `live` (its `finalise_cap`
post for a thread cap; `if_live_then_nonz_cap` with the zombie the only
cap). The narrowing of `JRdTrivHyp`: a CNode zombie's slot is ready from
`JAtZ` alone. -/
def JZombieTcbHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64), Z.th = th →
    ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost), WJ (L := L) arI AR Z H Cs kb s a σ G →
      ∀ x, IsSlot th x → ∀ p zt n, capV (L.mem s) x = .Zombie p zt n → zt.val = 65 → DeadP (L := L) H s p

/-- **A zombie swapped with its first slot keeps `WJ`** (`SwapHypW` at
`WJ`). Proved (`jSwapHyp`, XTopJointZombie's
`JAtZ.swapJCore`, by `jowes_slotD`: no `DestLive` is read; the TCBs' slot 3
holds no zombie, `JPlaced.fh`, and is no object's first slot). -/
def JSwapHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64), Z.th = th →
    SwapHypW (L := L) (A := A) (WJ (L := L) arI AR Z H Cs kb) th

/-- **A cleanup cap's `post_cap_deletion` keeps `WJR`** (`PostDelHypW` at
`WJR`; proved, XTopJointPost's `jPostDelHyp_of`). -/
def JPostDelHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64), Z.th = th →
    PostDelHypW (L := L) arI (WJR (L := L) arI AR Z H Cs kb) th

/-- `ReadyLive` at a `WJ` state, `x`'s cap naming no container (`LiveJHyp`). -/
theorem readyLive_wj_noRef {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} (hLv : LiveJHyp (L := L) arI AR th)
    {Z : XSets} {H : P1.Heap} {Cs : Set U64} {kb : U64} (hth : Z.th = th) {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {G : MdbGhost} (hW : WJ (L := L) arI AR Z H Cs kb s a σ G) {x : U64}
    (hn : ∀ q, ¬ RefsObj q (capV (L.mem s) x)) : ReadyLive (L := L) th s σ G x := by
  subst hth
  obtain ⟨V, Ac, Lst, D, J, -⟩ := hW
  exact J.readyLive_noRef (hLv (Z.mv G V) H Cs Ac Lst D s a σ rfl J) hn

/-- `ReadyLive` at a `WJ` state, another cap of `x`'s cap's key in the MDB. -/
theorem readyLive_wj_key {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} (hLv : LiveJHyp (L := L) arI AR th)
    {Z : XSets} {H : P1.Heap} {Cs : Set U64} {kb : U64} (hth : Z.th = th) {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {G : MdbGhost} (hW : WJ (L := L) arI AR Z H Cs kb s a σ G) {x y : U64}
    (hy : y ∈ G.chains.flatten) (hne : y ≠ x) (hk : okey (capV (L.mem s) y) = okey (capV (L.mem s) x))
    (hkn : okey (capV (L.mem s) x) ≠ none) : ReadyLive (L := L) th s σ G x := by
  subst hth
  obtain ⟨V, Ac, Lst, D, J, -⟩ := hW
  exact J.readyLive_key (hLv (Z.mv G V) H Cs Ac Lst D s a σ rfl J) hy hne hk hkn

/-- `ReadyLive` at a `WJ` state, at a removable zombie. -/
theorem readyLive_wj_zombie {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} (hLv : LiveJHyp (L := L) arI AR th)
    {Z : XSets} {H : P1.Heap} {Cs : Set U64} {kb : U64} (hth : Z.th = th) {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {G : MdbGhost} (hW : WJ (L := L) arI AR Z H Cs kb s a σ G) {x : U64}
    (hx : IsSlot th x) {p zt n : U64} (hz : capV (L.mem s) x = .Zombie p zt n)
    (hrm : n.val = 0 ∨ (n.val = 1 ∧ p = x)) : ReadyLive (L := L) th s σ G x := by
  subst hth
  obtain ⟨V, Ac, Lst, D, J, -⟩ := hW
  exact J.readyLive_zombie (hLv (Z.mv G V) H Cs Ac Lst D s a σ rfl J) hx hz hrm

/-- **A TCB zombie's TCB is dead** (`JZombieTcbHyp`, from `LiveJ.zdead`). -/
theorem jZombieTcbHyp_of_live {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} (hLv : LiveJHyp (L := L) arI AR th) :
    JZombieTcbHyp (L := L) arI AR th := by
  intro Z H Cs kb hth s a σ G hW x hx p zt n hz h65
  obtain ⟨V, Ac, Lst, D, J, -⟩ := hW
  exact (hLv (Z.mv G V) H Cs Ac Lst D s a σ hth J).zdead x (by show IsSlot Z.th x; rw [hth]; exact hx) p zt n hz h65


/-- An IRQ handler cap. -/
def IrqK (c : capability.Cap) : Prop := ∃ i, c = .IrqHandler i

/-- **The IRQ node's slots hold null or notification caps at `J`** (as
XTopFinIrq's `IrqSlotOK` premise). Derived from `JSpecIrqNodeHyp` [J]:
`jIrqSlotHyp_of`. -/
def JIrqSlotHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64), Z.th = th →
    ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost), WJ (L := L) arI AR Z H Cs kb s a σ G →
      ∀ i : U64, i.val < 128 → IrqSlotOK (L.mem s) (nodeA (L.ksb s) i)

/-- **Hypothesis: the spec's IRQ node slots hold null or notification caps at
`J`** [J] (IntInv's `SpecIrqNode` at every `JAtZ` state; a spec-only
invariant: the slots are written only by `invoke_irq_handler`'s
SetIRQHandler, a notification cap, and by deletions, since no cap names an
IRQ node CNode, l4v `valid_global_refs` with the IRQ nodes in `global_refs`,
`valid_irq_node`). -/
def JSpecIrqNodeHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit), Z.th = th → JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SpecIrqNode σ

/-- **`JIrqSlotHyp` from the spec's** (`irqSlotOK_of_spec` at `JAtZ`'s
interrupt layout `intL`, the CSpace relation and the IRQ relation). -/
theorem jIrqSlotHyp_of {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} (h : JSpecIrqNodeHyp (L := L) arI AR th) :
    JIrqSlotHyp (L := L) arI AR th := by
  intro Z H Cs kb hth s a σ G hW i hi
  obtain ⟨V, Ac, Lst, D, J, -, -⟩ := hW
  exact irqSlotOK_of_spec J.intL J.xtop.rel.2.1.1 J.xtop.fin.1.1.2.2.2.1 (h (Z.mv G V) H Cs Ac Lst D s a σ hth J) hi

/-- An endpoint cap. -/
def EpK (c : capability.Cap) : Prop := ∃ e b x1 x2 x3 x4, c = .Endpoint e b x1 x2 x3 x4

/-- A reply cap. -/
def RpK (c : capability.Cap) : Prop := ∃ p g, c = .Reply p g

/-- A native VSpace cap finalised with work when final: a page table, page
directory, PDPT, PML4 or ASID pool cap. -/
def VsK (c : capability.Cap) : Prop :=
  (∃ p m a v, c = .PageTable p m a v) ∨ (∃ p m a v, c = .PageDirectory p m a v) ∨
    (∃ p m a v, c = .Pdpt p m a v) ∨ (∃ p m a, c = .Pml4 p m a) ∨ ∃ p b, c = .AsidPool p b
/-- A mapped EPT root cap (its finalisation releases its ASID). -/
def EptRootK (c : capability.Cap) : Prop := ∃ p asid va, c = .Ept p 0#u64 true asid va
/-- A scheduling-context cap. -/
def ScK (c : capability.Cap) : Prop := ∃ p sb, c = .SchedContext p sb
/-- A thread (TCB) cap. -/
def TcbK (c : capability.Cap) : Prop := ∃ t, c = .Thread t

/-- **`reply_remove` at `J`** (the reply cap's finalisation of a thread
blocked on the reply): from `JAtZ`, FL4's `reply_remove` against the spec's
(deterministic), `JAtZ` after at fresh VSpace sets, the slots and the
kernel-state base kept. Proved: `jReplyRemoveHyp` (XTopJointRemove's
`JAtZ.replyRemoveJ`). -/
def JReplyRemoveHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit), Z.th = th → JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ →
    ∀ (r t : U64) (x : Fl4Spec.Tcb), r ∈ Z.R → t ∈ Z.T → σ.kheap t.bv = some (.tcb x) →
      x.tcbState = .blockedOnReply r.bv → ipc.reply_remove st arI s a r t ⦃ res => res.2 = a ∧
        ∃ σ' V' Ac' Lst' D', Fl4Spec.replyRemove (Z := Unit) t.bv r.bv σ = ({((), σ')}, False) ∧
          JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' res.1 res.2 σ' ∧
          SlotsSame Z.th (L.mem s) (L.mem res.1) ∧ L.ksb res.1 = L.ksb s ⦄

/-- **`reply_remove` at `J`** (XTopJointRemove's `JAtZ.replyRemoveJ`). -/
theorem jReplyRemoveHyp {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} (hT : P0.ArchTotal arI) :
    JReplyRemoveHyp (L := L) arI AR th :=
  fun _ _ _ _ _ _ _ _ _ _ J _ _ _ hr ht hk hst => J.replyRemoveJ hT hr ht hk hst

/-- `JThreadFinHyps` but `utTcb` (the latter from `LiveJ`, `utTcb_of_live`). -/
structure JThreadFinHypsU (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop where
  /-- [scope] XTopJointFinThread's `JThreadFinHyps.obj` (a native thread's VCPU word zero). -/
  obj : ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit), Z.th = th → JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ →
    ∀ (x p : U64), IsSlot Z.th x → capV (L.mem s) x = .Thread p →
      L.mem s (core.num.U64.wrapping_add p 3664#u64) = 0#u64
  /-- [J] XTopJointFinThread's `JThreadFinHyps.idle`. -/
  idle : ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit), Z.th = th → JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ →
    ∀ (x p : U64), IsSlot Z.th x → capV (L.mem s) x = .Thread p → L.idleW s ≠ p
  /-- [P] XTopJointFinThread's `JThreadFinHyps.ticks`. -/
  ticks : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
    ∀ (a : A) (v : U64), arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄

/-- **The named steps of the deletion at `J`** (module docstring). -/
structure JDelParts (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop where
  fin : JFinAtF (L := L) arI AR th (fun c => ¬ NtfnK c ∧ ¬ FrIoK c ∧ ¬ IrqK c ∧ ¬ EpK c ∧ ¬ RpK c ∧ ¬ VsK c ∧ ¬ ScK c ∧ ¬ TcbK c ∧
    ¬ (EptK c ∨ VcpuK c) ∧ ¬ EptRootK c)
  /-- `JSpecIrqNodeHyp` [J] (the spec's IRQ node slots null or notification
  caps; gives `JIrqSlotHyp` by `jIrqSlotHyp_of`). -/
  irq : JSpecIrqNodeHyp (L := L) arI AR th
  /-- ScSignalBoundJ's `RecvReplyLinksHyp` [J] (l4v `valid_replies`; gives `RecvReplyHyp` by
  `recvReplyHyp_of`), at every
  `P1.Heap` and set of cores: a final endpoint cap's finalisation frees the
  replies of the threads blocked receiving on it. -/
  recvRep : ∀ (H : P1.Heap) (Cs : Set U64), RecvReplyLinksHyp (L := L) arI AR H Cs
  /-- The x86 backend's obligations (VsArch's `ArchRefines` [P]), for a final
  native VSpace cap's finalisation. -/
  archRef : ArchRefines arI AR
  /-- XTopJointFinVs's `JVsCapsHyp` [J] (l4v `valid_cap` for the arch caps). -/
  vsCaps : JVsCapsHyp (L := L) arI AR th
  /-- XTopJointFinVs's `JVsApartHyp` [J] (the ASID table
  apart from `H`'s SCs outside `Z.C`). -/
  vsApart : JVsApartHyp (L := L) arI AR th
  /-- The x86 backend's VCPU barrier keeps the arch relation (`ARKeep` [P]),
  for the VT-x finalisations (`jFrVt_of`, `jFinAt_vt`). -/
  arKeep : ARKeep arI AR
  /-- XTopJointFinVtJ's `JVtHyps` [J] (the VCPU list's and the EPT walks'
  placement, the EPT-mapped frames' ASIDs, the VT-x objects apart from
  `H`'s). -/
  vt : JVtHyps (L := L) arI AR th
  /-- The steps of a final thread cap's finalisation at `J` not proved
  (XTopJointFinThread's `JThreadFinHyps` but `utTcb`, which `LiveJ` gives:
  `JDelParts.thread`). -/
  thr : JThreadFinHypsU (L := L) arI AR th
  /-- **The liveness of FL4's caps** (XTopJointLive's `LiveJ` [J]: the
  containers of the slots in use named by caps, the debug-list threads by
  thread caps, a zombie's slots from its count on unused, a TCB zombie's TCB
  dead; l4v `if_unsafe_then_cap`, `if_live_then_nonz_cap`, `zombies_final`).
  It gives the emptied slot's liveness readiness (`ReadyLive`), the debug
  successor's cover (`JThreadFinHyps.utTcb`) and `JZombieTcbHyp`. -/
  live : LiveJHyp (L := L) arI AR th

/-! ## The proved steps -/

variable {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap}

/-- `JThreadFinHyps` from `JDelParts` (`utTcb` from `LiveJ`, `utTcb_of_live`). -/
theorem JDelParts.thread (h : JDelParts (L := L) arI AR th) : JThreadFinHyps (L := L) arI AR th :=
  ⟨h.thr.obj, h.thr.idle, h.thr.ticks, utTcb_of_live arI h.live⟩

/-- **A notification cap's finalisation at `J`, every slot kept** (module
docstring): `jFinAt_ntfn`'s post with the cleanup null and every slot's cap
as it was (for `delete_oneJ`). -/
theorem jFinNtfnK [Fl4Proofs.P1.PlainStore st] (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (hth : Z.th = th)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (p b : U64) (w r : Bool)
    (hDS : DState (L := L) th s σ G) (hW : WJ (L := L) arI AR Z H Cs kb s a σ G) (hA : AbsSlot th sl)
    (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Notification p b w r)) :
    objects.finalise_cap st arI s a (.Notification p b w r)
        (decide (Fl4Spec.isFinalCap' (absCap (.Notification p b w r)) σ)) false ⦃ res =>
      res.1.1 = finRem (.Notification p b w r) (decide (Fl4Spec.isFinalCap' (absCap (.Notification p b w r)) σ)) ∧
      res.1.2 = .Null ∧ ∃ σ' G', ((absCap res.1.1, absCap res.1.2), σ') ∈ (Fl4Spec.finaliseCap (Z := Unit)
          (absCap (.Notification p b w r)) (decide (Fl4Spec.isFinalCap' (absCap (.Notification p b w r)) σ)) σ).1 ∧
        DState (L := L) th res.2.1 σ' G' ∧ (∀ y, IsSlot th y → capV (L.mem res.2.1) y = capV (L.mem s) y) ∧
        MdbStep (L.mem s) G (L.mem res.2.1) G' ∧ WJ (L := L) arI AR Z H Cs kb res.2.1 res.2.2 σ' G' ∧
        RdJ (L := L) (A := A) H res.2.1 res.2.2 σ' G' (cslotAddr sl) ⦄ := by
  subst hth
  obtain ⟨V, Ac, Lst, D, J, hkb, hns⟩ := hW
  have hP := J.xtop.rel.1
  have hcv := capV_of_capAt hc
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hHp : H p = some .ntfn := ((hJ.typed _ hA.isSlot).2.1 p b w r hcv).2
  have hpN : p ∈ (Z.mv G V).N := J.hset.2.1 p hHp
  by_cases hfin : Fl4Spec.isFinalCap' (absCap (.Notification p b w r)) σ
  · rw [decide_eq_true hfin]
    refine WP.spec_mono (WP.spec_and (J.finNtfnJ hpN)
      (P1.fin_cap_ntfn.dead (ar := arI) s a p b w r false J.blk hHp hHp)) ?_
    rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨⟨e1, e2, σ1, V1, hmem1, J1, -, hSS1, hks1⟩, d1, d2, d3⟩
    simp only at e1 e2 hmem1 J1 hSS1 hks1 d1 d2 d3
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e1
    subst e2
    have hdp : DeadP (L := L) H s1 p :=
      ⟨fun h => (by rw [hHp] at h; cases h), fun h => (by rw [hHp] at h; cases h), fun _ => ⟨d1, d2, d3⟩,
        fun h => (by rw [hHp] at h; cases h), fun z h => (by rw [hHp] at h; cases h)⟩
    have hcv1 : capV (L.mem s1) (cslotAddr sl) = .Notification p b w r := by
      rw [hSS1.capV hA.isSlot, hcv]
    refine ⟨rfl, rfl, σ1, G, hmem1, ⟨J1.xtop.rel.2.1, J1.del, J1.xtop.rel.2.2.1⟩,
      fun y hy => hSS1.capV hy, (MdbStep.refl hDS.1.2.2.1).same_right hDS.1.2.2.1 hSS1,
      ⟨V1, Ac, Lst, D, J1, hks1.trans hkb, ak_finaliseCap_ns hmem1 hns⟩, J1.ntfn_ready hA.isSlot hcv1 (Or.inl hdp)⟩
  · rw [decide_eq_false hfin]
    obtain ⟨cl, he, hmem, -, -, hnio⟩ := fin_idle (st := st) (L := L) arI s a σ (.Notification p b w r) trivial
      false (fun hw => by have := finWork_ntfn hw; cases this)
    have hcl0 : cl = .Null := hnio (fun f l e => by cases e)
    subst hcl0
    rw [he, WP.spec_ok]
    exact ⟨rfl, rfl, σ, G, hmem, hDS, fun y _ => rfl, MdbStep.refl hDS.1.2.2.1,
      ⟨V, Ac, Lst, D, J, hkb, ak_finaliseCap_ns hmem hns⟩, J.ntfn_ready hA.isSlot hcv (Or.inr (other_ntfn hP hDS hA hcv hfin))⟩

/-- **A notification cap's finalisation at `J`** (module docstring). -/
theorem jFinAt_ntfn [Fl4Proofs.P1.PlainStore st] : JFinAt (L := L) arI AR th NtfnK := by
  intro Z H Cs kb hth s a σ G sl c hDS hW hA hc _ hn
  obtain ⟨p, b, w, r, rfl⟩ := hn
  refine WP.spec_mono (jFinNtfnK arI Z H Cs kb hth s a σ G sl p b w r hDS hW hA hc) ?_
  rintro res ⟨h1, h2, σ', G', h4, h5, h6, h7, h8, h9⟩
  refine ⟨h1, by rw [h2]; trivial, by rw [h2]; trivial, σ', G', h4, h5, by rw [h6 _ hA.isSlot, capV_of_capAt hc],
    fun y hy _ => Or.inl (h6 y hy), h7, h8, h9⟩

/-- **Emptying a ready slot at `J`** (`EmptyHypWR` at `WJ`): a CNode slot by
`emptyJR`, a TCB slot by `emptyJRT`; `DelUtFact` after from `RdL`'s
`ReadyLive` (`JAtZ.delUtFact_of`). -/
theorem emptyHypJ [Fl4Proofs.P1.PlainStore st] (Z : XSets)
    (H : P1.Heap) (Cs : Set U64) (kb : U64) (hth : Z.th = th) :
    EmptyHypWR (L := L) (WJ (L := L) arI AR Z H Cs kb) (RdL (L := L) (A := A) th H) th := by
  intro s s' a σ σ' G G' sl hW hRdL hD1 hD2 hF hes hA hxn hx0 hoth hmS
  obtain ⟨hRd, hRL⟩ := hRdL
  subst hth
  obtain ⟨V, Ac, Lst, D, J, hkb, hns⟩ := hW
  have hnk := emptySlot_null_nkn _ σ ((), σ') hes
  obtain ⟨⟨V2, hX2⟩, -, -, -⟩ := slotHypW_XZ AR (Z.mv G V) kb s s' a σ σ' G G'
    ⟨⟨V, J.xtop⟩, J.ks, J.thT, hkb⟩ hD1 hD2 hF hnk hmS
  obtain ⟨hks, hkb2, hR⟩ : L.ksb s' = L.ksb s ∧ KBack σ σ' ∧ _ := by
    by_cases hcn : ∃ q, sl.1 = q.bv ∧ Z.th q = some (.cnode sl.2.length)
    · exact J.emptyJR hA hcn hxn hRd hes hD2 hx0 hoth hX2 (SlotFrame2.writesIn hF) hnk
    · exact J.emptyJRT hA hcn hxn hRd hes hD2 hx0 hoth hX2 (SlotFrame2.writesIn hF) hnk
  have hcs := emptySlot_cdt_orig J.xtop.rel.2.1.1 hA hxn hes
  have hw : P1.WritesIn st s s' (InSlot Z.th) :=
    (SlotFrame2.writesIn hF).mono fun b hb => slotWd_range J.xtop.rel.1 hb
  have hU : ∀ u up usb ufi udev, AbsSlot Z.th u → capAt (L.mem s) (cslotAddr u) = ok (.Untyped up usb ufi udev) →
      σ.cdt sl = some u → (∀ x, σ.cdt x = some u → x = sl) → (∀ x, σ.cdt x ≠ some sl) →
      DelUtFact (L := L) Z.th s' σ' up usb ufi udev := fun u up usb ufi udev hu hcu hpar honly hleaf =>
    let ⟨h1, h2⟩ := hRL
    J.delUtFact_of hA hD2 hX2.rel.2.2.2.2.1.1.2.1 hx0 hoth hw hcs.1 hcs.2 hu hcu hpar honly hleaf h1 h2
  obtain ⟨hC, Ac', Lst', D', R⟩ := hR hU
  exact ⟨V2, Ac', Lst', D', J.cs_frameV hks hX2 hkb2 hC R, hks.trans hkb,
    (ak_emptySlot' _ _).noSwitch hes hns⟩

set_option maxHeartbeats 4000000 in
/-- **`delete_one` of a notification cap at `J`** (as XTopDelOne's
`delete_one_xtopK`): the notification's finalisation (`jFinNtfnK`), then the
ready slot emptied (`emptyHypJ`, `ReadyLive` from `LiveJ`: a notification cap
names no container); the slot emptied, the
others kept, `WJ` after. -/
theorem delete_oneJ [Fl4Proofs.P1.PlainStore st] (hLv : LiveJHyp (L := L) arI AR th) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64)
    (hth : Z.th = th) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G)
    (hW : WJ (L := L) arI AR Z H Cs kb s a σ G) {sl : Fl4Spec.CslotPtr} (hA : AbsSlot th sl) {p b : U64}
    {w r : Bool} (hk : capV (L.mem s) (cslotAddr sl) = .Notification p b w r) :
    cdt.delete_one st arI s a (cslotAddr sl) ⦃ res =>
      ∃ σ' G', ((), σ') ∈ (Fl4Spec.capDeleteOne (Z := Unit) sl σ).1 ∧ DState (L := L) th res.1 σ' G' ∧
        capV (L.mem res.1) (cslotAddr sl) = .Null ∧
        (∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem res.1) y = capV (L.mem s) y) ∧
        MdbStep (L.mem s) G (L.mem res.1) G' ∧ WJ (L := L) arI AR Z H Cs kb res.1 res.2 σ' G' ⦄ := by
  have hP : Placed th := by obtain ⟨V, Ac, Lst, D, J, -⟩ := hW; exact hth ▸ J.xtop.rel.1
  obtain ⟨c, ac, hc, hca, hg⟩ := hDS.1.1.abs_cap hA
  rw [hca.abs] at hg
  have hcv := capV_of_capAt hc
  unfold cdt.delete_one
  rw [slot_cap_eq, hc]
  simp only [bind_ok, cap_is_null_eq]
  rw [hcv] at hk; subst hk
  have hcn : capability.Cap.Notification p b w r ≠ .Null := by simp
  simp only [isNullB_false hcn, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨bf, hbf, hbf2, -⟩ := finalHyp_full th hP s σ G sl _ hDS hA hc hcn
  have hNF : NeedsFin (.Notification p b w r) := Or.inl ⟨trivial, rfl⟩
  rw [hbf2 hNF] at hbf
  rw [is_final_with_cap_eq _ _ _ hc, hbf]; simp only [bind_ok]
  rw [← finalise_cap_ntfn arI s a p b w r _ false]
  apply WP.spec_bind (jFinNtfnK arI Z H Cs kb hth s a σ G sl p b w r hDS hW hA hc)
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨hrem, hcl, σ1, G1, hmem, hDS1, hkeep, hm1, hW1, hRd1⟩
  simp only at hrem hcl hmem hDS1 hkeep hm1 hW1 hRd1
  subst hcl
  simp only [uncurry_apply_pair]
  refine WP.spec_mono (empty_stepWR' arI (WJ (L := L) arI AR Z H Cs kb) (RdL (L := L) (A := A) th H) th hP
    (cl := .Null) (fun h => absurd rfl h) (emptyHypJ arI Z H Cs kb hth) s1 a1 σ1 G1 hDS1 hW1 hA
    (fun _ => ⟨hRd1, readyLive_wj_noRef arI hLv hth hW1 fun q h => by
      rw [hkeep _ hA.isSlot, capV_of_capAt hc] at h; exact h⟩) trivial trivial) ?_
  rintro ⟨s2, a2⟩ ⟨σ2, G2, hes, hDS2, hx2, hoth, -, -, -, hm2, hW2⟩
  refine ⟨σ2, G2, ?_, hDS2, hx2, fun y hy hyx => by rw [hoth y hy hyx, hkeep y hy], hm1.trans hm2, hW2⟩
  unfold Fl4Spec.capDeleteOne
  refine mem_bind_nd (x := (absCap (.Notification p b w r), σ)) (by rw [hg]; rfl) ?_
  simp only [absCap, Fl4Spec.NonDet.unless, reduceCtorEq, ↓reduceIte]
  refine mem_bind_nd (x := (decide (Fl4Spec.isFinalCap' (absCap (.Notification p b w r)) σ), σ)) rfl ?_
  refine mem_bind_nd (x := ((), σ1)) (fastFinalise_of_finaliseCap hmem) ?_
  exact hes

set_option maxHeartbeats 8000000 in
/-- **A final IRQ handler cap's finalisation at `J`** (as XTopFinIrq's
`xFinIrq_of`): FL4's `deleting_irq_handler` deletes the IRQ node slot's cap
(null, or a notification cap by `delete_oneJ`); the handler's slot is ready
(an IRQ handler cap is not physical). From `JIrqSlotHyp`, `LiveJ` [J] and
the interrupt layout (`JAtZ.intL`). -/
theorem jFinAt_irq [Fl4Proofs.P1.PlainStore st] (hLv : LiveJHyp (L := L) arI AR th) (hOK : JIrqSlotHyp (L := L) arI AR th) :
    JFinAtF (L := L) arI AR th IrqK := by
  intro Z H Cs kb hth s a σ G sl c hDS hW hA hc _ ⟨i, hci⟩ hfin
  subst hci
  obtain ⟨V, hX, hL⟩ : ∃ V, XTopAt (L := L) AR (Z.mv G V) s a σ ∧ IntLayout th (L.ksb s) := by
    obtain ⟨V, Ac, Lst, D, J, -⟩ := hW; exact ⟨V, J.xtop, hth ▸ J.intL⟩
  obtain ⟨c', ac, hc', hca, -⟩ := hDS.1.1.abs_cap hA
  rw [hc] at hc'; cases eq_of_ok_eq hc'
  have hcw : CapWf (.IrqHandler i) := hca.1
  have hi : i.val < 128 := hcw
  rw [decide_eq_true hfin]
  unfold objects.finalise_cap
  simp only [↓reduceIte]
  unfold interrupt.deleting_irq_handler
  rw [irq_slot_eq]; simp only [bind_ok]
  have hA' : AbsSlot th ((nodeA (L.ksb s) i).bv, []) := ⟨_, rfl, Or.inl (by simpa using hL.node i hi)⟩
  set sl' : Fl4Spec.CslotPtr := ((nodeA (L.ksb s) i).bv, []) with hsl'
  have hcs : cslotAddr sl' = nodeA (L.ksb s) i := cslotAddr_nil _
  have hcv := capV_of_capAt hc
  have hnode : σ.interruptIrqNode (BitVec.ofNat 8 i.val) = (nodeA (L.ksb s) i).bv :=
    hX.fin.1.1.2.2.2.1.node i hi
  have hfo : ∀ (s1 : S) (a1 : A), objects.finalise_cap_object st arI s1 a1 (.IrqHandler i) true =
      ok ((.Null, .IrqHandler i), s1, a1) := fun _ _ => rfl
  have hspec : ∀ σ1 : Fl4Spec.State Unit, ((), σ1) ∈ (Fl4Spec.capDeleteOne (Z := Unit) sl' σ).1 →
      ((absCap .Null, absCap (.IrqHandler i)), σ1) ∈
        (Fl4Spec.finaliseCap (Z := Unit) (absCap (.IrqHandler i)) true σ).1 := by
    intro σ1 h1
    show _ ∈ ((if true = true then do
        Fl4Spec.deletingIrqHandler (BitVec.ofNat 8 i.val)
        return (Fl4Spec.Cap.nullCap, Fl4Spec.Cap.irqHandlerCap (BitVec.ofNat 8 i.val))
      else return (Fl4Spec.Cap.nullCap, Fl4Spec.Cap.nullCap)) σ).1
    simp only [↓reduceIte]
    refine mem_bind_nd (x := ((), σ1)) ?_ (Set.mem_singleton _)
    unfold Fl4Spec.deletingIrqHandler Fl4Spec.getIrqSlot
    refine mem_bind_nd (x := (sl', σ)) (by
      show (((nodeA (L.ksb s) i).bv, []), σ) = ((σ.interruptIrqNode (BitVec.ofNat 8 i.val), []), σ)
      rw [hnode]) h1
  have hok := hOK Z H Cs kb hth s a σ G hW i hi
  have hne : cslotAddr sl ≠ nodeA (L.ksb s) i := by
    intro e
    rcases hok with h | ⟨p, b, w, r, h⟩
    · rw [← e, hcv] at h; cases h
    · rw [← e, hcv] at h; cases h
  have hphys : physF (.IrqHandler i) = false := ok_inj (phys_eq _).symm
  have hrd : ∀ (s' : S) (a' : A) (σ' : Fl4Spec.State Unit) (G' : MdbGhost),
      capV (L.mem s') (cslotAddr sl) = .IrqHandler i → RdJ (L := L) (A := A) H s' a' σ' G' (cslotAddr sl) := by
    intro s' a' σ' G' h hp
    rw [h, hphys] at hp; cases hp
  rcases hok with hnull | ⟨p, b, w, r, hn⟩
  · -- a null node slot: nothing to delete
    obtain ⟨c0, ac0, hc0, hca0, hg0⟩ := hDS.1.1.abs_cap hA'
    rw [hca0.abs] at hg0
    have hcv0 := capV_of_capAt hc0
    rw [hcs] at hcv0
    rw [hcv0] at hnull; subst hnull
    have e1 : cdt.delete_one st arI s a (nodeA (L.ksb s) i) = ok (s, a) := by
      unfold cdt.delete_one
      rw [slot_cap_eq, ← hcs, hc0]
      simp only [bind_ok, cap_is_null_eq, isNullB, ↓reduceIte]
    have e2 : Fl4Spec.capDeleteOne (Z := Unit) sl' σ = ({((), σ)}, False) := by
      unfold Fl4Spec.capDeleteOne
      rw [nd_bind_one hg0]
      simp [absCap, Fl4Spec.NonDet.unless, Fl4Spec.NonDet.pure]
    rw [e1]; simp only [bind_ok]
    show objects.finalise_cap_object st arI s a (.IrqHandler i) true ⦃ _ ⦄
    rw [hfo, WP.spec_ok]
    exact ⟨rfl, trivial, hcw, σ, G, hspec σ (by rw [e2]; exact Set.mem_singleton _), hDS, hcv,
      fun _ _ _ => Or.inl rfl, MdbStep.refl hDS.1.2.2.1, hW, hrd s a σ G hcv⟩
  · -- a notification cap: `delete_oneJ`
    have hd := delete_oneJ arI hLv Z H Cs kb hth s a σ G hDS hW hA' (by rw [hcs]; exact hn)
    rw [hcs] at hd
    refine WP.spec_bind hd ?_
    rintro ⟨s1, a1⟩ ⟨σ1, G1, hm1, hDS1, hx1, hoth1, hmS1, hW1⟩
    show objects.finalise_cap_object st arI s1 a1 (.IrqHandler i) true ⦃ _ ⦄
    rw [hfo, WP.spec_ok]
    have hcv1 : capV (L.mem s1) (cslotAddr sl) = .IrqHandler i := by
      rw [hoth1 _ hA.isSlot hne]; exact hcv
    refine ⟨rfl, trivial, hcw, σ1, G1, hspec σ1 hm1, hDS1, hcv1, fun y hy hyx => ?_, hmS1, hW1,
      hrd _ _ _ _ hcv1⟩
    by_cases e : y = nodeA (L.ksb s) i
    · subst e; refine Or.inr ⟨hx1, ?_⟩; rw [hn]; rfl
    · exact Or.inl (hoth1 y hy e)

/-- **An endpoint cap's slot is ready once the endpoint is dead** (as
XTopJointEmpty's `JAtZ.ntfn_ready`). -/
theorem JAtZ.ep_ready {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {x : U64} (hx : IsSlot Z.th x) {p b : U64}
    {x1 x2 x3 x4 : Bool} (hcv : capV (L.mem s) x = .Endpoint p b x1 x2 x3 x4) (hd : DeadP (L := L) H s p) :
    EmptyReady (L := L) H Z.G s x := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hHp : H p = some .ep := (hJ.typed _ hx).1 p b x1 x2 x3 x4 hcv
  have hpfit : p.val + 2 ^ 4 ≤ 2 ^ 64 := J.kern.heap.fits p _ hHp
  obtain ⟨e1, e2⟩ := range_ep p b x1 x2 x3 x4 hpfit
  unfold EmptyReady
  rw [hcv, e1, e2]
  intro _ _
  have hout : ∀ q k, H q = some k → q ≠ p → q.val + 2 ^ k.bits ≤ p.val ∨ p.val + 2 ^ 4 ≤ q.val := by
    intro q k hq hne
    have := J.kern.heap.disj q k p .ep hq hHp hne
    simpa only [show (P1.HKind.ep).bits = 4 from rfl] using this
  refine fun lo hi hlh h1 h2 => ?_
  · right
    intro q hq
    by_cases e : q = p
    · subst e; exact hd
    · cases hk : H q with
      | none => exact deadP_none hk
      | some k =>
        exfalso
        have : 1 ≤ 2 ^ k.bits := Nat.one_le_two_pow
        rcases hout q k hk e with h | h <;> omega

set_option maxHeartbeats 4000000 in
/-- **A final endpoint cap's finalisation at `J`** (XTopJointFinEp's
`JAtZ.finEpJ`, the endpoint dead after by P1's `fin_cap_ep.dead`), from
`RecvReplyHyp` [J]. -/
theorem jFinAt_ep (hRR : ∀ (H : P1.Heap) (Cs : Set U64), RecvReplyLinksHyp (L := L) arI AR H Cs) :
    JFinAtF (L := L) arI AR th EpK := by
  intro Z H Cs kb hth s a σ G sl c hDS hW hA hc _ ⟨e, b, x1, x2, x3, x4, hce⟩ hfin
  subst hce hth
  obtain ⟨V, Ac, Lst, D, J, hkb, hns⟩ := hW
  have hcv := capV_of_capAt hc
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hHe : H e = some .ep := (hJ.typed _ hA.isSlot).1 e b x1 x2 x3 x4 hcv
  have heE : e ∈ (Z.mv G V).E := J.hset.1 e hHe
  rw [decide_eq_true hfin]
  refine WP.spec_mono (WP.spec_and (J.finEpJ (hRR H Cs) heE)
    (P1.fin_cap_ep.dead (ar := arI) s a e b x1 x2 x3 x4 false J.blk hHe)) ?_
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨⟨e1, e2, σ1, V1, hmem1, J1, -, hSS1, hks1⟩, d1⟩
  simp only at e1 e2 hmem1 J1 hSS1 hks1 d1
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e1
  subst e2
  have hdp : DeadP (L := L) H s1 e :=
    ⟨fun h => (by rw [hHe] at h; cases h), fun _ => d1, fun h => (by rw [hHe] at h; cases h),
      fun h => (by rw [hHe] at h; cases h), fun z h => (by rw [hHe] at h; cases h)⟩
  have hcv1 : capV (L.mem s1) (cslotAddr sl) = .Endpoint e b x1 x2 x3 x4 := by
    rw [hSS1.capV hA.isSlot, hcv]
  exact ⟨rfl, trivial, trivial, σ1, G, hmem1, ⟨J1.xtop.rel.2.1, J1.del, J1.xtop.rel.2.2.1⟩, hcv1,
    fun y hy _ => Or.inl (hSS1.capV hy), (MdbStep.refl hDS.1.2.2.1).same_right hDS.1.2.2.1 hSS1,
    ⟨V1, Ac, Lst, D, J1, hks1.trans hkb, ak_finaliseCap_ns hmem1 hns⟩, JAtZ.ep_ready arI J1 hA.isSlot hcv1 hdp⟩

/-- **A reply cap's slot is ready once the reply is dead** (as
`JAtZ.ep_ready`). -/
theorem JAtZ.reply_ready {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {x : U64} (hx : IsSlot Z.th x) {p : U64} {g : Bool}
    (hcv : capV (L.mem s) x = .Reply p g) (hd : DeadP (L := L) H s p) :
    EmptyReady (L := L) H Z.G s x := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hHp : H p = some .reply := (hJ.typed _ hx).2.2 p g hcv
  have hpfit : p.val + 2 ^ 5 ≤ 2 ^ 64 := J.kern.heap.fits p _ hHp
  obtain ⟨e1, e2⟩ := range_reply p g hpfit
  unfold EmptyReady
  rw [hcv, e1, e2]
  intro _ _
  have hout : ∀ q k, H q = some k → q ≠ p → q.val + 2 ^ k.bits ≤ p.val ∨ p.val + 2 ^ 5 ≤ q.val := by
    intro q k hq hne
    have := J.kern.heap.disj q k p .reply hq hHp hne
    simpa only [show (P1.HKind.reply).bits = 5 from rfl] using this
  refine fun lo hi hlh h1 h2 => ?_
  · right
    intro q hq
    by_cases e : q = p
    · subst e; exact hd
    · cases hk : H q with
      | none => exact deadP_none hk
      | some k =>
        exfalso
        have : 1 ≤ 2 ^ k.bits := Nat.one_le_two_pow
        rcases hout q k hk e with h | h <;> omega

set_option maxHeartbeats 4000000 in
/-- **A final reply cap's finalisation at `J`** (XTopJointFinReply's
`JAtZ.finReplyJ`, the reply dead after by P1's `fin_cap_reply.dead`), from
`RecvReplyHyp` [J] and `JReplyRemoveHyp` [J]. -/
theorem jFinAt_reply [Fl4Proofs.P1.PlainStore st] (hT : P0.ArchTotal arI)
    (hRR : ∀ (H : P1.Heap) (Cs : Set U64), RecvReplyLinksHyp (L := L) arI AR H Cs)
    (hRm : JReplyRemoveHyp (L := L) arI AR th) : JFinAtF (L := L) arI AR th RpK := by
  intro Z H Cs kb hth s a σ G sl c hDS hW hA hc _ ⟨p, g, hce⟩ hfin
  subst hce hth
  obtain ⟨V, Ac, Lst, D, J, hkb, hns⟩ := hW
  have hcv := capV_of_capAt hc
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hHp : H p = some .reply := (hJ.typed _ hA.isSlot).2.2 p g hcv
  have hpR : p ∈ (Z.mv G V).R := J.hset.2.2 p hHp
  rw [decide_eq_true hfin]
  refine WP.spec_mono (WP.spec_and (J.finReplyJ hT (hRR H Cs) (hRm (Z.mv G V) H Cs Ac Lst D s a σ rfl J) hpR)
    (P1.fin_cap_reply.dead (ar := arI) hT s a p g false J.blk hHp)) ?_
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨⟨e1, e2, σ1, V1, Ac1, Lst1, D1, hmem1, J1, hSS1, hks1⟩, d1⟩
  simp only at e1 e2 hmem1 J1 hSS1 hks1 d1
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e1
  subst e2
  have hdp : DeadP (L := L) H s1 p :=
    ⟨fun h => (by rw [hHp] at h; cases h), fun h => (by rw [hHp] at h; cases h),
      fun h => (by rw [hHp] at h; cases h), fun _ => d1, fun z h => (by rw [hHp] at h; cases h)⟩
  have hcv1 : capV (L.mem s1) (cslotAddr sl) = .Reply p g := by
    rw [hSS1.capV hA.isSlot, hcv]
  exact ⟨rfl, trivial, trivial, σ1, G, hmem1, ⟨J1.xtop.rel.2.1, J1.del, J1.xtop.rel.2.2.1⟩, hcv1,
    fun y hy _ => Or.inl (hSS1.capV hy), (MdbStep.refl hDS.1.2.2.1).same_right hDS.1.2.2.1 hSS1,
    ⟨V1, Ac1, Lst1, D1, J1, hks1.trans hkb, ak_finaliseCap_ns hmem1 hns⟩, JAtZ.reply_ready arI J1 hA.isSlot hcv1 hdp⟩

set_option maxHeartbeats 4000000 in
/-- **A final native VSpace cap's finalisation at `J`** (XTopJointFinVs's
`JAtZ.finVsJ`; the slot ready, `JAtZ.vs_ready`), from `ArchRefines` [P],
`JVsCapsHyp` [J] and `JVsApartHyp` [J]. -/
theorem jFinAt_vs [Fl4Proofs.P1.PlainStore st] (hAR : ArchRefines arI AR) (hVC : JVsCapsHyp (L := L) arI AR th)
    (hAp : JVsApartHyp (L := L) arI AR th) : JFinAtF (L := L) arI AR th VsK := by
  intro Z H Cs kb hth s a σ G sl c hDS hW hA hc _ hv hfin
  obtain ⟨V, Ac, Lst, D, J, hkb, hns⟩ := hW
  have hVC0 := hVC (Z.mv G V) H Cs Ac Lst D s a σ hth J
  have Ap := hAp (Z.mv G V) H Cs Ac Lst D s a σ hth J
  subst hth
  have hcv := capV_of_capAt hc
  have hxm : cslotAddr sl ∈ G.chains.flatten := (hDS.1.2.2.1.members _).2 ⟨hA.isSlot, _, hc, fun h => by
    subst h
    rcases hv with ⟨_, _, _, _, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, _, e⟩ | ⟨_, _, e⟩ <;> cases e⟩
  rw [decide_eq_true hfin]
  refine WP.spec_mono (J.finVsJ hAR hVC0 Ap hDS hA hc hv) ?_
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨h1, h2, h3, σ1, hm, J1, hSS, hks⟩
  simp only at h1 h2 h3 hm J1 hSS hks ⊢
  have hcv1 : capV (L.mem s1) (cslotAddr sl) = c := by rw [hSS.capV hA.isSlot, hcv]
  exact ⟨h1, h2, h3, σ1, G, hm, ⟨J1.xtop.rel.2.1, J1.del, J1.xtop.rel.2.2.1⟩, hcv1,
    fun y hy _ => Or.inl (hSS.capV hy), (MdbStep.refl hDS.1.2.2.1).same_right hDS.1.2.2.1 hSS,
    ⟨V, Ac, Lst, D, J1, hks.trans hkb, ak_finaliseCap_ns hm hns⟩, J.vs_ready hVC0 hxm hcv hv hcv1⟩

set_option maxHeartbeats 4000000 in
/-- **A VSpace-mapped frame cap's finalisation at `J`** (XTopJointFinVs's
`JAtZ.finVsJb`, final or not), from `ArchRefines` [P], `JVsCapsHyp` [J] and
`JVsApartHyp` [J]. -/
theorem jFrMap_of [Fl4Proofs.P1.PlainStore st] (hAR : ArchRefines arI AR) (hVC : JVsCapsHyp (L := L) arI AR th)
    (hAp : JVsApartHyp (L := L) arI AR th) : JFrMapHyp (L := L) arI AR th := by
  intro Z H Cs kb hth s a σ G sl c hDS hW hA hc _ ⟨p, sz, r, d, asid, va, hce⟩
  obtain ⟨V, Ac, Lst, D, J, hkb, hns⟩ := hW
  have hVC0 := hVC (Z.mv G V) H Cs Ac Lst D s a σ hth J
  have Ap := hAp (Z.mv G V) H Cs Ac Lst D s a σ hth J
  subst hth hce
  have hcv := capV_of_capAt hc
  refine WP.spec_mono (J.finVsJb hAR hVC0 Ap hDS hA hc rfl ⟨_, rfl⟩ _
    (Or.inr ⟨p, sz, r, d, false, asid, va, rfl⟩)) ?_
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨h1, h2, h3, σ1, hm, J1, hSS, hks⟩
  simp only at h1 h2 h3 hm J1 hSS hks ⊢
  have hcv1 : capV (L.mem s1) (cslotAddr sl) = .Frame p sz r d true false asid va := by
    rw [hSS.capV hA.isSlot, hcv]
  exact ⟨h1, h2, h3, σ1, G, hm, ⟨J1.xtop.rel.2.1, J1.del, J1.xtop.rel.2.2.1⟩, hcv1,
    fun y hy _ => Or.inl (hSS.capV hy), (MdbStep.refl hDS.1.2.2.1).same_right hDS.1.2.2.1 hSS,
    ⟨V, Ac, Lst, D, J1, hks.trans hkb, ak_finaliseCap_ns hm hns⟩, trivial⟩

set_option maxHeartbeats 4000000 in
/-- **The VT-x work of a finalisation at `J`** (XTopJointFinVtJ's
`JAtZ.frVtJ`: an EPT-mapped frame's `ept::unmap`, an owned IO port's
`revoke_ports`, the spec state kept): `JFrVtHyp` from `ArchRefines` [P],
`ARKeep` [P] and `JVtHyps` [J]. -/
theorem jFrVt_of [Fl4Proofs.P1.PlainStore st] (hAR : ArchRefines arI AR) (hK : ARKeep arI AR) (hV : JVtHyps (L := L) arI AR th) :
    JFrVtHyp (L := L) arI AR th := by
  intro Z H Cs kb hth s a σ G sl c hDS hW hA hc _ hk
  obtain ⟨V, Ac, Lst, D, J, hkb, hns⟩ := hW
  subst hth
  have hcv := capV_of_capAt hc
  refine WP.spec_mono (J.frVtJ hAR hK hV hDS hA hc hk _) ?_
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨h1, h2, h3, hm, ⟨Ac1, Lst1, D1, J1⟩, hSS, hks⟩
  simp only at h1 h2 h3 hm J1 hSS hks ⊢
  have hcv1 : capV (L.mem s1) (cslotAddr sl) = c := by rw [hSS.capV hA.isSlot, hcv]
  exact ⟨h1, h2, h3, σ, G, hm, ⟨J1.xtop.rel.2.1, J1.del, J1.xtop.rel.2.2.1⟩, hcv1,
    fun y hy _ => Or.inl (hSS.capV hy), (MdbStep.refl hDS.1.2.2.1).same_right hDS.1.2.2.1 hSS,
    ⟨V, Ac1, Lst1, D1, J1, hks.trans hkb, hns⟩, trivial⟩

set_option maxHeartbeats 4000000 in
/-- **A final mapped EPT root cap's finalisation at `J`** (XTopJointFinVs's
`JAtZ.finVsJb` with VsFin's `fin_ept_root`: FL4's `delete_asid` of the root,
the spec's `deleteAsid`), the slot ready after (the root apart from `H`'s
objects but `other` ones, `JAtZ.ept_obj`); from `ArchRefines` [P],
`JVsCapsHyp` [J], `JVsApartHyp` [J] and `JVtHyps` [J]. -/
theorem jFinAt_eptRoot [Fl4Proofs.P1.PlainStore st] (hAR : ArchRefines arI AR) (hVC : JVsCapsHyp (L := L) arI AR th)
    (hAp : JVsApartHyp (L := L) arI AR th) (hV : JVtHyps (L := L) arI AR th) :
    JFinAtF (L := L) arI AR th EptRootK := by
  intro Z H Cs kb hth s a σ G sl c hDS hW hA hc _ hk hfin
  obtain ⟨p, asid, va, hce⟩ := hk
  obtain ⟨V, Ac, Lst, D, J, hkb, hns⟩ := hW
  have hVC0 := hVC (Z.mv G V) H Cs Ac Lst D s a σ hth J
  have Ap := hAp (Z.mv G V) H Cs Ac Lst D s a σ hth J
  subst hth hce
  have hcv := capV_of_capAt hc
  have hap0 := J.ept_obj hA.isSlot hcv
  have hp0 := J.ept_ne0 hA.isSlot hcv
  rw [decide_eq_true hfin]
  refine WP.spec_mono (J.finVsJb hAR hVC0 Ap hDS hA hc ⟨rfl, rfl, hp0⟩ ⟨_, rfl⟩ true
    (Or.inl ⟨Or.inl rfl, rfl, fun f l e => by cases e⟩)) ?_
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨h1, h2, h3, σ1, hm, J1, hSS, hks⟩
  simp only at h1 h2 h3 hm J1 hSS hks ⊢
  have hcv1 : capV (L.mem s1) (cslotAddr sl) = .Ept p 0#u64 true asid va := by rw [hSS.capV hA.isSlot, hcv]
  exact ⟨h1, h2, h3, σ1, G, hm, ⟨J1.xtop.rel.2.1, J1.del, J1.xtop.rel.2.2.1⟩, hcv1,
    fun y hy _ => Or.inl (hSS.capV hy), (MdbStep.refl hDS.1.2.2.1).same_right hDS.1.2.2.1 hSS,
    ⟨V, Ac, Lst, D, J1, hks.trans hkb, ak_finaliseCap_ns hm hns⟩, EmptyReady.of_apartO (by rw [hcv1]; exact hap0)⟩

set_option maxHeartbeats 4000000 in
/-- **A final VT-x object cap's finalisation at `J`** (XTopJointFinVtJ's
`JAtZ.finEptJ`, an EPT cap but a mapped root's; `JAtZ.finVcpuJ`, a VCPU
cap), the slot ready after; from `ArchRefines` [P], `ARKeep` [P] and
`JVtHyps` [J]. -/
theorem jFinAt_vt (hAR : ArchRefines arI AR) (hK : ARKeep arI AR) (hV : JVtHyps (L := L) arI AR th) :
    JFinAtF (L := L) arI AR th (fun c => EptK c ∨ VcpuK c) := by
  intro Z H Cs kb hth s a σ G sl c hDS hW hA hc _ hk hfin
  obtain ⟨V, Ac, Lst, D, J, hkb, hns⟩ := hW
  subst hth
  have hcv := capV_of_capAt hc
  rw [decide_eq_true hfin]
  have hsp : objects.finalise_cap st arI s a c true false ⦃ r =>
      VtPost (L := L) arI AR (Z.mv G V) H Cs s σ c true r ∧ EmptyReady (L := L) H G r.2.1 (cslotAddr sl) ⦄ := by
    rcases hk with he | hv
    · exact J.finEptJ hAR hV hA hc he
    · exact J.finVcpuJ hK hV hA hc hv
  refine WP.spec_mono hsp ?_
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨⟨h1, h2, h3, hm, ⟨Ac1, Lst1, D1, J1⟩, hSS, hks⟩, hRd⟩
  simp only at h1 h2 h3 hm J1 hSS hks hRd ⊢
  have hcv1 : capV (L.mem s1) (cslotAddr sl) = c := by rw [hSS.capV hA.isSlot, hcv]
  exact ⟨h1, h2, h3, σ, G, hm, ⟨J1.xtop.rel.2.1, J1.del, J1.xtop.rel.2.2.1⟩, hcv1,
    fun y hy _ => Or.inl (hSS.capV hy), (MdbStep.refl hDS.1.2.2.1).same_right hDS.1.2.2.1 hSS,
    ⟨V, Ac1, Lst1, D1, J1, hks.trans hkb, hns⟩, hRd⟩

/-- **The frame and IO port caps' finalisation at `J`**, final or not
(XTopJointFinFrIo's `finFrIo_of`): an unmapped frame's and an unowned IO
port cap's do nothing; a VSpace-mapped frame's from `JFrMapHyp` (`jFrMap_of`), the
VT-x work from `JFrVtHyp` [J]; the slot ready after (an IO port cap is not
physical; a frame's memory holds no object of `H` but `other` ones,
`JAtZ.cobj`, `EmptyReady.of_apartO`). -/
theorem jFinAt_frio [Fl4Proofs.P1.PlainStore st] (hM : JFrMapHyp (L := L) arI AR th) (hV : JFrVtHyp (L := L) arI AR th) :
    JFinAt (L := L) arI AR th FrIoK := by
  intro Z H Cs kb hth
  refine finFrIo_of arI (hM Z H Cs kb hth) (hV Z H Cs kb hth) ?_
  intro s a σ G sl c hW hA hcv hk
  rcases hk with hf | ⟨f, l, o, rfl⟩
  · cases c with
    | Frame p sz r d m ep a' va =>
      obtain ⟨V, Ac, Lst, D, J, -⟩ := hW
      subst hth
      have hC := J.cobj hA.isSlot
      rw [hcv] at hC
      exact EmptyReady.of_apartO (by rw [hcv]; exact hC)
    | _ => cases hf
  · exact EmptyReady.of_nonphys (by rw [hcv]; exact physF_ioPort f l o)
/-- **A final SC cap's finalisation at `J`** (`JScFinHyp` [J], the SC dead
after by P1's `fin_cap_sc.dead`, `JAtZ.sc_ready`), the cap's SC by
`JAtZ.scCap`; the SC may be the current SC. -/
theorem jFinAt_sc (hT : P0.ArchTotal arI) (hF : JScFinHyp (L := L) arI AR th) :
    JFinAtF (L := L) arI AR th ScK := by
  intro Z H Cs kb hth s a σ G sl c hDS hW hA hc _ ⟨p, sb, hce⟩ hfin
  subst hce hth
  obtain ⟨V, Ac, Lst, D, J, hkb, hns⟩ := hW
  have hcv := capV_of_capAt hc
  have hC' := J.scCap arI hA hc
  obtain ⟨hHp, -, hp0, hna, hidle, -⟩ :=
    JAtZ.scCapFacts arI J hA hc ⟨hC'.1, hC'.2, fun _ _ _ _ _ u hu => (hns u hu).elim⟩
  have hpS : p ∈ P1.Heap.scs H := ⟨_, hHp⟩
  rw [decide_eq_true hfin]
  refine WP.spec_mono (WP.spec_and (hF (Z.mv G V) H Cs Ac Lst D s a σ rfl J hns sl p sb hA hc hfin)
    (P1.fin_cap_sc.dead (ar := arI) hT s a p sb false J.blk hpS hp0 hna hidle)) ?_
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨⟨e1, σ1, V1, Ac1, Lst1, D1, hmem1, J1, hSS1, hks1⟩, ⟨d1, d2, d3⟩⟩
  simp only at e1 hmem1 J1 hSS1 hks1 d1 d2 d3
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e1
  have hdp : DeadP (L := L) H s1 p :=
    ⟨fun h => (by rw [hHp] at h; cases h), fun h => (by rw [hHp] at h; cases h),
      fun h => (by rw [hHp] at h; cases h), fun h => (by rw [hHp] at h; cases h), fun _ _ => ⟨d1, d2, d3⟩⟩
  have hcv1 : capV (L.mem s1) (cslotAddr sl) = .SchedContext p sb := by
    rw [hSS1.capV hA.isSlot, hcv]
  exact ⟨rfl, trivial, trivial, σ1, G, hmem1, ⟨J1.xtop.rel.2.1, J1.del, J1.xtop.rel.2.2.1⟩, hcv1,
    fun y hy _ => Or.inl (hSS1.capV hy), (MdbStep.refl hDS.1.2.2.1).same_right hDS.1.2.2.1 hSS1,
    ⟨V1, Ac1, Lst1, D1, J1, hks1.trans hkb, ak_finaliseCap_ns hmem1 hns⟩, JAtZ.sc_ready arI J1 hcv1 hHp hdp⟩
/-- **A final thread cap's finalisation at `J`** (XTopJointFinThread's
`JAtZ.finThreadJ`, from `JThreadFinHyps`), the slots kept and the kernel
base by P1's `fin_cap_thread.slots`, the thread dead after by P1's
`fin_cap_thread.dead` (`JAtZ.tcb_ready`). -/
theorem jFinAt_thread (hT : P0.ArchTotal arI) (hK : ARKeep arI AR) (hF : JThreadFinHyps (L := L) arI AR th)
    (hRR : ∀ (H : P1.Heap) (Cs : Set U64), RecvReplyLinksHyp (L := L) arI AR H Cs) :
    JFinAtF (L := L) arI AR th TcbK := by
  intro Z H Cs kb hth s a σ G sl c hDS hW hA hc _ ⟨p, hce⟩ hfin
  subst hce hth
  obtain ⟨V, Ac, Lst, D, J, hkb, hns⟩ := hW
  have hcv := capV_of_capAt hc
  have hthp : Z.th p = some .tcb := hDS.1.2.1.abs hA hc
  have hpT : p ∈ Z.T := J.thT p hthp
  have hpH : H p = some .tcb := J.zH.1 p hpT
  have hv0 := hF.obj (Z.mv G V) H Cs Ac Lst D s a σ rfl J _ p hA.isSlot hcv
  have hidle := hF.idle (Z.mv G V) H Cs Ac Lst D s a σ rfl J _ p hA.isSlot hcv
  have hna : L.actionW s ≠ p := J.action_ne_of_noSwitch hpT hns
  rw [decide_eq_true hfin]
  refine WP.spec_mono (WP.spec_and (WP.spec_and (JAtZ.finThreadJ (Z := Z.mv G V) hT hK hF hRR J hpT hv0 hna hidle)
    (P1.fin_cap_thread.dead (ar := arI) hT s a p false J.blk hpH hna hidle hv0))
    (P1.fin_cap_thread.slots (ar := arI) hT s a p true false J.blk hpH hna hidle hv0)) ?_
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨⟨⟨σ1, hm1, V1, Ac1, Lst1, D1, J1⟩, d1, d2, d3, d4, d5⟩, e, -, f, hW1⟩
  simp only [ite_true, Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  have hSS1 : SlotsSame Z.th (L.mem s) (L.mem s1) :=
    slotsSame_of_capw J.xtop.rel.1 (J.slotCapW (tLowSlots_all _)) hW1
  have hks1 : L.ksb s1 = L.ksb s := f.1
  have hdp : DeadP (L := L) H s1 p :=
    ⟨fun _ => ⟨d1, d2, d3, Ne.symm d4, Ne.symm d5⟩, fun h => (by rw [hpH] at h; cases h),
      fun h => (by rw [hpH] at h; cases h), fun h => (by rw [hpH] at h; cases h),
      fun z h => (by rw [hpH] at h; cases h)⟩
  have hcv1 : capV (L.mem s1) (cslotAddr sl) = .Thread p := by
    rw [hSS1.capV hA.isSlot, hcv]
  refine ⟨rfl, trivial, trivial, σ1, G, ?_, ⟨J1.xtop.rel.2.1, J1.del, J1.xtop.rel.2.2.1⟩, hcv1,
    fun y hy _ => Or.inl (hSS1.capV hy), (MdbStep.refl hDS.1.2.2.1).same_right hDS.1.2.2.1 hSS1,
    ⟨V1, Ac1, Lst1, D1, J1, hks1.trans hkb, ak_finaliseCap_ns hm1 hns⟩, J1.tcb_ready hcv1 hpH hdp⟩
  rw [absCap_zombieTcb]
  exact hm1

theorem okey_of_finObj {c : capability.Cap} (hk : FinObjKind c) : okey c ≠ none := by
  cases c <;> simp_all [FinObjKind, okey]

theorem isUt_of_finObj {c : capability.Cap} (hk : FinObjKind c) : isUt c = false := by
  cases c <;> simp_all [FinObjKind, isUt]

/-- **A non-final cap's finalisation at `J`**, every object cap but frames
and IO port caps: nothing (`fin_idle`), the slot ready by another cap alike
it (`other_key`, `EmptyReady.of_cover`). -/
theorem jFin_nonfinal [Fl4Proofs.P1.PlainStore st] (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (hth : Z.th = th)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (c : capability.Cap)
    (hDS : DState (L := L) th s σ G) (hW : WJ (L := L) arI AR Z H Cs kb s a σ G) (hA : AbsSlot th sl)
    (hc : capAt (L.mem s) (cslotAddr sl) = ok c) (hk : FinObjKind c) (hfi : ¬ FrIoK c)
    (hfin : ¬ Fl4Spec.isFinalCap' (absCap c) σ) :
    objects.finalise_cap st arI s a c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) false ⦃ r =>
      r.1.1 = finRem c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) ∧ CleanCap r.1.2 ∧ CapWf r.1.2 ∧
      ∃ σ' G', ((absCap r.1.1, absCap r.1.2), σ') ∈
          (Fl4Spec.finaliseCap (Z := Unit) (absCap c) (decide (Fl4Spec.isFinalCap' (absCap c) σ)) σ).1 ∧
        DState (L := L) th r.2.1 σ' G' ∧ capV (L.mem r.2.1) (cslotAddr sl) = c ∧
        (∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem r.2.1) y = capV (L.mem s) y ∨
          (capV (L.mem r.2.1) y = .Null ∧ isZb (capV (L.mem s) y) = false)) ∧
        MdbStep (L.mem s) G (L.mem r.2.1) G' ∧ WJ (L := L) arI AR Z H Cs kb r.2.1 r.2.2 σ' G' ∧
        RdJ (L := L) (A := A) H r.2.1 r.2.2 σ' G' (cslotAddr sl) ⦄ := by
  subst hth
  have hP : Placed Z.th := by obtain ⟨V, Ac, Lst, D, J, -⟩ := hW; exact J.xtop.rel.1
  have hcv := capV_of_capAt hc
  have hf : isFrame c = false := by
    cases h : isFrame c
    · rfl
    · exact absurd (Or.inl h) hfi
  have hio : ∀ f l o, c ≠ .IoPort f l o := fun f l o e => hfi (Or.inr ⟨f, l, o, e⟩)
  rw [decide_eq_false hfin]
  obtain ⟨cl, he, hmem, -, hrem, hnio⟩ := fin_idle (st := st) (L := L) arI s a σ c hk false (by
    rintro (⟨h | ⟨f, l, o, e, -⟩, -⟩ | ⟨p, sz, r, d, ep, asid, va, e⟩)
    · cases h
    · exact hio _ _ _ e
    · subst e; simp [isFrame] at hf)
  have hcl0 : cl = .Null := hnio (fun f l e => hio f l 0#u64 e)
  subst hcl0
  obtain ⟨y, hy, hne, hky⟩ := other_key hP hDS hA hcv hk hf hfin
  have hn : okey c ≠ none := okey_of_finObj hk
  have hsh : shape (capV (L.mem s) y) = shape c := shape_of_key hky (by rw [hky]; exact hn)
  obtain ⟨eb, et, ep⟩ := range_of_shape hsh
  have hut : isUt (capV (L.mem s) y) = false := by
    rw [isUt_of_shape hsh]; exact isUt_of_finObj hk
  rw [he, WP.spec_ok]
  exact ⟨hrem.symm, trivial, trivial, σ, G, hmem, hDS, hcv, fun y _ _ => Or.inl rfl, MdbStep.refl hDS.1.2.2.1,
    hW, EmptyReady.of_cover (x := cslotAddr sl) hy hne (fun h => by rw [ep]; rw [hcv] at h; exact h) hut
      (by rw [eb, hcv]) (by rw [et, hcv])⟩

/-- The object caps' finalisation at `J`, from the notification caps'
(`jFinAt_ntfn`), the non-final caps' (`jFin_nonfinal`), the final caps'
(`JDelParts.fin`) and the frame and IO port caps' (`jFinAt_frio`). -/
theorem finJ [Fl4Proofs.P1.PlainStore st] (h : JDelParts (L := L) arI AR th)
    (hT : P0.ArchTotal arI) (Z : XSets) (H : P1.Heap) (Cs : Set U64)
    (kb : U64) (hth : Z.th = th) :
    FinObjHypWR (L := L) arI (WJ (L := L) arI AR Z H Cs kb) (RdJ (L := L) (A := A) H) th := by
  intro s a σ G sl c hDS hW hA hc hk _
  by_cases hn : NtfnK c
  · exact jFinAt_ntfn arI Z H Cs kb hth s a σ G sl c hDS hW hA hc hk hn
  by_cases hfi : FrIoK c
  · exact jFinAt_frio arI (jFrMap_of arI h.archRef h.vsCaps h.vsApart) (jFrVt_of arI h.archRef h.arKeep h.vt) Z H Cs kb hth s a σ G sl c hDS hW hA hc hk hfi
  by_cases hfin : Fl4Spec.isFinalCap' (absCap c) σ
  · by_cases hq : IrqK c
    · exact jFinAt_irq arI h.live (jIrqSlotHyp_of arI h.irq) Z H Cs kb hth s a σ G sl c hDS hW hA hc hk hq hfin
    by_cases he : EpK c
    · exact jFinAt_ep arI h.recvRep Z H Cs kb hth s a σ G sl c hDS hW hA hc hk he hfin
    by_cases hr : RpK c
    · exact jFinAt_reply arI hT h.recvRep (jReplyRemoveHyp arI hT) Z H Cs kb hth s a σ G sl c hDS hW hA hc hk hr hfin
    by_cases hvs : VsK c
    · exact jFinAt_vs arI h.archRef h.vsCaps h.vsApart Z H Cs kb hth s a σ G sl c hDS hW hA hc hk hvs hfin
    by_cases hsc : ScK c
    · exact jFinAt_sc arI hT (jScFin_of arI hT (JThreadFinHyps.yieldToH arI hT h.thread)) Z H Cs kb hth s a σ G sl c hDS hW hA hc hk hsc hfin
    by_cases ht : TcbK c
    · exact jFinAt_thread arI hT h.arKeep h.thread h.recvRep Z H Cs kb hth s a σ G sl c hDS hW hA hc hk ht hfin
    by_cases hvt : EptK c ∨ VcpuK c
    · exact jFinAt_vt arI h.archRef h.arKeep h.vt Z H Cs kb hth s a σ G sl c hDS hW hA hc hk hvt hfin
    by_cases hrt : EptRootK c
    · exact jFinAt_eptRoot arI h.archRef h.vsCaps h.vsApart h.vt Z H Cs kb hth s a σ G sl c hDS hW hA hc hk hrt hfin
    · exact h.fin Z H Cs kb hth s a σ G sl c hDS hW hA hc hk ⟨hn, hfi, hq, he, hr, hvs, hsc, ht, hvt, hrt⟩ hfin
  · exact jFin_nonfinal arI Z H Cs kb hth s a σ G sl c hDS hW hA hc hk hfi hfin

/-- The trivially finalised caps but untyped ones are not physical. -/
theorem physF_triv (c : capability.Cap) (ht : TrivFin c) (hu : isUt c = false) : physF c = false := by
  cases c <;> simp only [TrivFin] at ht <;> first | exact ok_inj (phys_eq _).symm | simp [isUt] at hu

/-- A CNode cap's range: its CNode's `2 ^ (r + 5)` bytes. -/
theorem range_cnodeR (q r gs g : U64) (hr : r.val + 5 < 64) (hfit : q.val + 32 * 2 ^ r.val ≤ 2 ^ 64) :
    baseF (.CNode q r gs g) = q.val ∧ topF (.CNode q r gs g) = q.val + 32 * 2 ^ r.val - 1 := by
  have e5 : 2 ^ (r.val + 5) = 32 * 2 ^ r.val := by rw [pow_add]; ring
  have hsz : sizeF (.CNode q r gs g) = core.num.U64.wrapping_add r fl4_abi.consts.bits.SLOT :=
    ok_inj (size_eq _).symm
  have hs : (core.num.U64.wrapping_add r fl4_abi.consts.bits.SLOT).val = r.val + 5 := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits,
      fl4_abi.consts.bits.SLOT]
    omega
  have hm := maskF_val (b := core.num.U64.wrapping_add r fl4_abi.consts.bits.SLOT) (by rw [hs]; exact hr)
  rw [hs, e5] at hm
  have h1 : 1 ≤ 2 ^ r.val := Nat.one_le_two_pow
  refine ⟨by unfold baseF; rw [ptrF_cnode], ?_⟩
  unfold topF
  rw [ptrF_cnode, hsz]
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits, hm]
  omega

/-- A word holding an `other` object of `H` (a CNode) is dead (`DeadP`
reads the TCB, endpoint, notification, reply and SC words only). -/
theorem deadP_other {H : P1.Heap} {s : S} {q : U64} {z : Nat} (h : H q = some (.other z)) :
    DeadP (L := L) H s q :=
  ⟨fun e => (by rw [h] at e; cases e), fun e => (by rw [h] at e; cases e), fun e => (by rw [h] at e; cases e),
    fun e => (by rw [h] at e; cases e), fun z e => (by rw [h] at e; cases e)⟩

/-- **A CNode cap's slot is ready to be emptied**: the only object of `H`
in its range is its CNode (`other`, dead for `DeadP`). -/
theorem JAtZ.cnode_ready {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {x : U64} {q r gs g : U64}
    (hcv : capV (L.mem s) x = .CNode q r gs g) (hth : Z.th q = some (.cnode r.val)) :
    EmptyReady (L := L) H Z.G s x := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hHq : H q = some (.other (r.val + 5)) := hJ.cnode q r.val hth
  have e5 : 2 ^ (r.val + 5) = 32 * 2 ^ r.val := by rw [pow_add]; ring
  have hfit : q.val + 32 * 2 ^ r.val ≤ 2 ^ 64 := by
    have := J.kern.heap.fits q _ hHq; rw [← e5]; exact this
  have hlt : r.val + 5 < 64 := J.kern.heap.lt64 q _ hHq
  obtain ⟨e1, e2⟩ := range_cnodeR q r gs g hlt hfit
  unfold EmptyReady
  rw [hcv, e1, e2]
  intro _ _
  have hout : ∀ q' k, H q' = some k → q' ≠ q → q'.val + 2 ^ k.bits ≤ q.val ∨ q.val + 32 * 2 ^ r.val ≤ q'.val := by
    intro q' k hq' hne
    have := J.kern.heap.disj q' k q _ hq' hHq hne
    simpa only [show (P1.HKind.other (r.val + 5)).bits = r.val + 5 from rfl, e5] using this
  have h32 : 1 ≤ 2 ^ r.val := Nat.one_le_two_pow
  refine fun lo hi hlh h1 h2 => Or.inr fun q' hq' => ?_
  · by_cases e : q' = q
    · subst e; exact deadP_other hHq
    · cases hk : H q' with
      | none => exact deadP_none hk
      | some k =>
        exfalso
        have : 1 ≤ 2 ^ k.bits := Nat.one_le_two_pow
        rcases hout q' k hk e with h | h <;> omega

/-- **The readiness at `J` of a cap finalised without effect** (`RdTrivHyp`
at `WJ`): the trivial caps cover nothing, a CNode cap's CNode is dead for
`DeadP` (`cnode_ready`); zombies by `JRdTrivHyp`. -/
theorem rdTrivJ [Fl4Proofs.P1.PlainStore st] (hRT : JRdTrivHyp (L := L) arI AR th) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64)
    (hth : Z.th = th) : RdTrivHyp (L := L) (WJ (L := L) arI AR Z H Cs kb) (RdJ (L := L) (A := A) H) th := by
  intro s a σ G sl c hDS hW hA hc hcn hnk _ _
  rcases cap_cases c hcn with ht | hcn' | hz | ho
  · intro hp hu
    rw [capV_of_capAt hc] at hp hu
    rw [physF_triv c ht hu] at hp
    cases hp
  · obtain ⟨q, r, gs, g, rfl⟩ := hcn'
    have hcvd : CapValid th (.CNode q r gs g) := hDS.1.2.1.abs hA hc
    subst hth
    obtain ⟨V, Ac, Lst, D, J, -⟩ := hW
    exact JAtZ.cnode_ready arI J (capV_of_capAt hc)
      (show Z.th q = some (.cnode r.val) ∧ r.val ≠ 0 from hcvd).1
  · obtain ⟨p, zt, n, rfl⟩ := hz
    exact hRT Z H Cs kb hth s a σ G sl p zt n hDS hW hA hc
  · exact absurd ho hnk

/-- **A zombie's slot is ready at `J`** (`JAtZ.zombie_ready`, a TCB zombie's
TCB dead by `JZombieTcbHyp`). -/
theorem jRdTrivHyp_of (hZT : JZombieTcbHyp (L := L) arI AR th) : JRdTrivHyp (L := L) arI AR th := by
  intro Z H Cs kb hth s a σ G sl p zt n _ hW hA hc
  have hW' := hW
  subst hth
  obtain ⟨V, Ac, Lst, D, J, -⟩ := hW
  exact J.zombie_ready hA.isSlot (capV_of_capAt hc)
    (hZT Z H Cs kb rfl s a σ G hW' _ hA.isSlot p zt n (capV_of_capAt hc))

/-- **A zombie written over a cap alike it keeps `WJ`** (`slotHypW_XZ` for
`XTopAt` after, `JAtZ.zombieJCore`, `cs_frameV`). -/
theorem jZombieHyp : JZombieHyp (L := L) arI AR th := by
  intro Z H Cs kb hth s s' a σ σ' G sl p zt n hW hD1 hD2 hF hsc hA hxn hz hal hoth hmS
  subst hth
  obtain ⟨V, Ac, Lst, D, J, hkb, hns⟩ := hW
  have hnk := Ipc.nkn_setCap _ _ σ ((), σ') (mem_of_single hsc)
  obtain ⟨⟨V2, hX2⟩, -, -, -⟩ := slotHypW_XZ AR (Z.mv G V) kb s s' a σ σ' G G
    ⟨⟨V, J.xtop⟩, J.ks, J.thT, hkb⟩ hD1 hD2 hF hnk hmS
  obtain ⟨hks, hkb2, hC, Ac', Lst', D', R⟩ := J.zombieJCore hA hxn hal hsc hD2 hz hoth hX2
    (SlotFrame2.writesIn hF) hnk
  exact ⟨V2, Ac', Lst', D', J.cs_frameV hks hX2 hkb2 hC R, hks.trans hkb,
    (ak_setCap' _ _).noSwitch (mem_of_single hsc) hns⟩

/-- **A zombie swapped with its first slot keeps `WJ`** (`slotHypW_XZ` for
`XTopAt` after, `JAtZ.swapJCore`, `cs_frameV`). -/
theorem jSwapHyp : JSwapHyp (L := L) arI AR th := by
  intro Z H Cs kb hth s s' a σ σ' G G' sl p zt n hW hD1 hD2 hF hsw hA hz hpx hG' hcap hmS
  subst hth hG'
  obtain ⟨V, Ac, Lst, D, J, hkb, hns⟩ := hW
  have hnk := capSwapForDelete_nkn _ _ σ ((), σ') (mem_of_single hsw)
  obtain ⟨⟨V2, hX2⟩, -, -, -⟩ := slotHypW_XZ AR (Z.mv G V) kb s s' a σ σ' G _
    ⟨⟨V, J.xtop⟩, J.ks, J.thT, hkb⟩ hD1 hD2 hF hnk hmS
  obtain ⟨hks, hkb2, hC, Ac', Lst', D', R⟩ := J.swapJCore hA hz hpx hsw hD2 hcap hX2
    (SlotFrame2.writesIn hF) hnk
  exact ⟨V2, Ac', Lst', D', J.cs_frameV hks hX2 hkb2 hC R, hks.trans hkb,
    (ak_capSwapForDelete' _ _).noSwitch (mem_of_single hsw) hns⟩

set_option maxHeartbeats 4000000 in
/-- **A non-final cap's finalisation at `J` with the loop's readiness**
(`jFin_nonfinal` with `RdL`: another cap alike it gives `ReadyLive`). -/
theorem jFin_nonfinalL [Fl4Proofs.P1.PlainStore st] (hLv : LiveJHyp (L := L) arI AR th) (Z : XSets) (H : P1.Heap)
    (Cs : Set U64) (kb : U64) (hth : Z.th = th)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (c : capability.Cap)
    (hDS : DState (L := L) th s σ G) (hW : WJ (L := L) arI AR Z H Cs kb s a σ G) (hA : AbsSlot th sl)
    (hc : capAt (L.mem s) (cslotAddr sl) = ok c) (hk : FinObjKind c) (hfi : ¬ FrIoK c)
    (hfin : ¬ Fl4Spec.isFinalCap' (absCap c) σ) :
    objects.finalise_cap st arI s a c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) false ⦃ r =>
      r.1.1 = finRem c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) ∧ CleanCap r.1.2 ∧ CapWf r.1.2 ∧
      ∃ σ' G', ((absCap r.1.1, absCap r.1.2), σ') ∈
          (Fl4Spec.finaliseCap (Z := Unit) (absCap c) (decide (Fl4Spec.isFinalCap' (absCap c) σ)) σ).1 ∧
        DState (L := L) th r.2.1 σ' G' ∧ capV (L.mem r.2.1) (cslotAddr sl) = c ∧
        (∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem r.2.1) y = capV (L.mem s) y ∨
          (capV (L.mem r.2.1) y = .Null ∧ isZb (capV (L.mem s) y) = false)) ∧
        MdbStep (L.mem s) G (L.mem r.2.1) G' ∧ WJ (L := L) arI AR Z H Cs kb r.2.1 r.2.2 σ' G' ∧
        (RmOK r.1.1 (cslotAddr sl) → RdL (L := L) (A := A) th H r.2.1 r.2.2 σ' G' (cslotAddr sl)) ⦄ := by
  have hP : Placed th := by obtain ⟨V, Ac, Lst, D, J, -⟩ := hW; exact hth ▸ J.xtop.rel.1
  have hcv := capV_of_capAt hc
  have hf : isFrame c = false := by
    cases h : isFrame c
    · rfl
    · exact absurd (Or.inl h) hfi
  have hio : ∀ f l o, c ≠ .IoPort f l o := fun f l o e => hfi (Or.inr ⟨f, l, o, e⟩)
  rw [decide_eq_false hfin]
  obtain ⟨cl, he, hmem, -, hrem, hnio⟩ := fin_idle (st := st) (L := L) arI s a σ c hk false (by
    rintro (⟨h | ⟨f, l, o, e, -⟩, -⟩ | ⟨p, sz, r, d, ep, asid, va, e⟩)
    · cases h
    · exact hio _ _ _ e
    · subst e; simp [isFrame] at hf)
  have hcl0 : cl = .Null := hnio (fun f l e => hio f l 0#u64 e)
  subst hcl0
  obtain ⟨y, hy, hne, hky⟩ := other_key hP hDS hA hcv hk hf hfin
  have hn : okey c ≠ none := okey_of_finObj hk
  have hsh : shape (capV (L.mem s) y) = shape c := shape_of_key hky (by rw [hky]; exact hn)
  obtain ⟨eb, et, ep⟩ := range_of_shape hsh
  have hut : isUt (capV (L.mem s) y) = false := by
    rw [isUt_of_shape hsh]; exact isUt_of_finObj hk
  rw [he, WP.spec_ok]
  exact ⟨hrem.symm, trivial, trivial, σ, G, hmem, hDS, hcv, fun y _ _ => Or.inl rfl, MdbStep.refl hDS.1.2.2.1,
    hW, fun _ => ⟨EmptyReady.of_cover (x := cslotAddr sl) hy hne (fun h => by rw [ep]; rw [hcv] at h; exact h) hut
      (by rw [eb, hcv]) (by rw [et, hcv]),
      readyLive_wj_key arI hLv hth hW hy hne (by rw [hky, hcv]) (by rw [hcv]; exact hn)⟩⟩

set_option maxHeartbeats 4000000 in
/-- **The object caps' finalisation at `J` with the loop's readiness**
(`finJ`; `ReadyLive` when the remainder is removable: a final cap's names
no container (a final thread cap's remainder is a zombie still naming
slots), a non-final one's has another cap alike, `jFin_nonfinalL`). -/
theorem finJL [Fl4Proofs.P1.PlainStore st] (h : JDelParts (L := L) arI AR th)
    (hT : P0.ArchTotal arI) (Z : XSets) (H : P1.Heap) (Cs : Set U64)
    (kb : U64) (hth : Z.th = th) :
    FinObjHypWRc (L := L) arI (WJ (L := L) arI AR Z H Cs kb) (RdL (L := L) (A := A) th H) th := by
  intro s a σ G sl c hDS hW hA hc hk _
  by_cases hnf : ¬ FrIoK c ∧ ¬ Fl4Spec.isFinalCap' (absCap c) σ
  · exact jFin_nonfinalL arI h.live Z H Cs kb hth s a σ G sl c hDS hW hA hc hk hnf.1 hnf.2
  refine WP.spec_mono (finJ arI h hT Z H Cs kb hth s a σ G sl c hDS hW hA hc hk trivial) ?_
  rintro r ⟨h1, h2, h3, σ', G', h4, h5, h6, h7, h8, h9, h10⟩
  refine ⟨h1, h2, h3, σ', G', h4, h5, h6, h7, h8, h9, fun hrm => ⟨h10, readyLive_wj_noRef arI h.live hth h9 ?_⟩⟩
  intro q hr
  rw [h6] at hr
  cases c with
  | Thread t =>
    have hfin : Fl4Spec.isFinalCap' (absCap (.Thread t)) σ := by
      by_contra hf
      exact hnf ⟨fun hfi => by rcases hfi with hfi | ⟨f, l, o, e⟩ <;> simp_all [isFrame], hf⟩
    rw [h1] at hrm
    simp only [finRem, decide_eq_true hfin, ↓reduceIte] at hrm
    rcases hrm with e | ⟨p, zt, n, e, hn⟩
    · cases e
    · cases e
      rcases hn with hn | ⟨hn, -⟩ <;> exact absurd hn (by decide)
  | CNode => simp [FinObjKind] at hk
  | Zombie => simp [FinObjKind] at hk
  | _ => simp [RefsObj] at hr

/-- **The readiness at `J` of a cap finalised without effect, with the
loop's readiness** (`rdTrivJ` with `ReadyLive`: the trivial caps name no
container; a CNode cap is not final when removable (its radix is not `0`),
so another cap alike it; a removable zombie's slots are unused). -/
theorem rdTrivJL [Fl4Proofs.P1.PlainStore st] (hLv : LiveJHyp (L := L) arI AR th) (Z : XSets) (H : P1.Heap)
    (Cs : Set U64) (kb : U64) (hth : Z.th = th) :
    RdTrivHyp (L := L) (WJ (L := L) arI AR Z H Cs kb) (RdL (L := L) (A := A) th H) th := by
  intro s a σ G sl c hDS hW hA hc hcn hnk hCN hZ
  refine ⟨rdTrivJ arI (jRdTrivHyp_of arI (jZombieTcbHyp_of_live arI hLv)) Z H Cs kb hth s a σ G sl c hDS hW hA hc
    hcn hnk hCN hZ, ?_⟩
  have hcv := capV_of_capAt hc
  rcases cap_cases c hcn with ht | ⟨q, r, gs, g, rfl⟩ | ⟨p, zt, n, rfl⟩ | ho
  · exact readyLive_wj_noRef arI hLv hth hW fun q h => by
      rw [hcv] at h; cases c <;> simp [TrivFin] at ht <;> simp [RefsObj] at h
  · have hcvd : CapValid th (.CNode q r gs g) := hDS.1.2.1.abs hA hc
    have hfin : ¬ Fl4Spec.isFinalCap' (absCap (.CNode q r gs g)) σ := fun hf =>
      (show th q = some (.cnode r.val) ∧ r.val ≠ 0 from hcvd).2 (hCN q r gs g rfl hf).1
    have hP : Placed th := by obtain ⟨V, Ac, Lst, D, J, -⟩ := hW; exact hth ▸ J.xtop.rel.1
    obtain ⟨y, hy, hne, hky⟩ := other_keyN hP hDS hA hcv (Or.inr (Or.inl ⟨_, _, _, _, rfl⟩)) rfl hfin
    exact readyLive_wj_key arI hLv hth hW hy hne (by rw [hky, hcv]) (by rw [hcv]; simp [okey])
  · exact readyLive_wj_zombie arI hLv hth hW hA.isSlot hcv (hZ p zt n rfl)
  · exact absurd ho hnk

/-- **`JDelHyp` from the named steps** (`delHyp_fullWR` at `WJR`, `RdJ`):
the steps at `WJ`, with `PPR0` after a finalisation by `jFinPPHyp` and
after a slot edit by `PPK.of_cnK`. -/
theorem JDelHyp.of_parts [Fl4Proofs.P1.PlainStore st] (h : JDelParts (L := L) arI AR th) (hpp : JPreemptHyp (L := L) arI AR th)
    (hpost : JPostDelHyp (L := L) arI AR th)
    (hT : P0.ArchTotal arI) :
    JDelHyp (L := L) arI AR th := by
  intro Z H Cs kb K hth hK hK6 s a σ G c hCR hE hA hxm
  obtain ⟨V, Ac, Lst, D, J, -⟩ := hE.2
  have hP : Placed th := hth ▸ J.xtop.rel.1
  have hF := finJL (L := L) arI h hT Z H Cs kb hth
  have hZ := jZombieHyp (L := L) (AR := AR) arI Z H Cs kb hth
  have hS := jSwapHyp (L := L) (AR := AR) arI Z H Cs kb hth
  have hEm := emptyHypJ (L := L) (AR := AR) arI Z H Cs kb hth
  have hH : DelHypsWR (L := L) arI (WJR (L := L) arI AR Z H Cs kb) (WJP (L := L) arI AR Z H Cs kb)
      (RdL (L := L) (A := A) th H) th := by
    refine ⟨?_, ?_, hpp Z H Cs kb hth, hpost Z H Cs kb hth, ?_, ?_, ?_⟩
    · intro s a σ G sl c hDS hW hA hc hk hKd
      have hW' := hW.wj arI
      obtain ⟨V, Ac, Lst, D, J, -, -, hp0⟩ := hW
      refine WP.spec_mono (hF s a σ G sl c hDS hW' hA hc hk hKd) ?_
      rintro r ⟨h1, h2, h3, σ', G', h4, h5, h6, h7, h8, h9, h10⟩
      exact ⟨h1, h2, h3, σ', G', h4, h5, h6, h7, h8,
        h9.wjr arI (jFinPPHyp arI (Z.mv G V) H Cs Ac Lst D s a σ hth J sl c hA hc hk _ σ' h4 hp0), h10⟩
    · intro s a σ G sl c hDS hW hA hc hcn hnk hCN hZ
      exact rdTrivJL arI h.live Z H Cs kb hth s a σ G sl c hDS (hW.wj arI) hA hc hcn hnk hCN hZ
    · intro s s' a σ σ' G sl p zt n hW hD1 hD2 hFr hsc hA hxn hz hal hoth hmS
      exact (hZ s s' a σ σ' G sl p zt n (hW.wj arI) hD1 hD2 hFr hsc hA hxn hz hal hoth hmS).wjr arI
        (hW.pp arI |>.of_ppk (PPK.of_cnK (Ipc.nkn_setCap _ _ σ ((), σ') (mem_of_single hsc))))
    · intro s s' a σ σ' G G' sl p zt n hW hD1 hD2 hFr hsw hA hz hpx hG' hcap hmS
      exact (hS s s' a σ σ' G G' sl p zt n (hW.wj arI) hD1 hD2 hFr hsw hA hz hpx hG' hcap hmS).wjr arI
        (hW.pp arI |>.of_ppk (PPK.of_cnK (capSwapForDelete_nkn _ _ σ ((), σ') (mem_of_single hsw))))
    · intro s s' a σ σ' G G' sl hW hRd hD1 hD2 hFr hes hA hxn hx0 hoth hmS
      exact (hEm s s' a σ σ' G G' sl (hW.wj arI) hRd hD1 hD2 hFr hes hA hxn hx0 hoth hmS).wjr arI
        (hW.pp arI |>.of_ppk (PPK.of_cnK (emptySlot_null_nkn _ σ ((), σ') hes)))
  subst hth
  exact delHyp_fullWR arI _ _ _ Z.th hP (finalHyp_full Z.th hP) hH K hK hK6 s a σ G c hCR hE hA hxm

end

end

end Fl4Proofs.P3
