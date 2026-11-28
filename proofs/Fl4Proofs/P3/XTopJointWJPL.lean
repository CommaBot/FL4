/-
P3 (DESIGN.md §9), CSpace (KENTRY-PLAN g2f (a)): **the deletion's
preempted state keeps `LiveDN`**, so a CNode Delete / Revoke ends with
`LiveDN` on both branches.

* `JAtZ.ppw_tcbWord`, `JAtZ.ppw_nodeWord`: the preemption point's writes
  (P1's `PPW`: `WORK_UNITS` and the current node's `CUR_TIME` / `CONSUMED`)
  miss every TCB word (`ksOut`, `node_ne_field`) and every other word of the
  current node.
* `JAtZ.deadP_ppw`: a dead TCB stays dead across those writes (its state,
  SC, bound notification and yield words, the action and idle words).
* `JAtZ.liveDN_ppw`: `LiveDN` at the preempted state from `LiveDN` before:
  the slots kept (`SlotsSame`), the original bits (`pp_ksm'`, the spec's
  preemption point writes no CDT / original bit), the spec's idle thread
  (`gke_preemptionPoint'`), the debug words (`JAtZ.ppDbg`), the TCB zombies'
  TCBs dead (`deadP_ppw`; a TCB zombie's object is a TCB by `DelInv.zwf`),
  the affinities (`ppw_tcbWord`). No `JAtZ` is needed after (the preempted
  state need not be one: `OffOK` may fail).
* `JAtPreMVL` (`JAtPreMV` with `LiveDN` at the preempted state, at the ghosts
  of the `JAtZ` before the preemption point), `WJPML := WJP ∧ JAtPreMVL ∧
  LiveDN` (XTopJointMRDel's `WJPM` with the liveness),
  `jPreemptHypLML : PPHypDW (WMR MR WJL) WJPML` (XTopJointMRDel's
  `jPreemptHypLM` plus `liveDN_ppw` on the preempted branch).
* `delHypsJLML`, `JDelHypLML`, `JDelParts.jDelHypLML`: the whole deletion of
  one cap at `WJPML` (`DelHypsWRZ`'s `pp` replaced).
* `JAtL` (`JAt` with `LiveDN` at its own ghosts), `cn_del_topJLML`,
  `decode_invocation_cnode_{revoke,delete}JLML`: XTopJointMRCnode's
  `cn_del_topJLM` / `decode_invocation_cnode_{revoke,delete}JLM` with the
  posts `JAtL` / `JAtPreMVL`: `LiveDN` at the outcome on the error, the
  completed and the preempted branch (the error branch and the fast path at
  the entry state, from `hLv`).
-/
import Fl4Proofs.P3.XTopJointMRCnode
import Fl4Proofs.P3.UtResetSpecJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {th : TypedHeap} {Z : XSets}
  {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}

/-- **`JAtPreMV` with `LiveDN` at the preempted state** (module docstring):
the ghosts are those of the `JAtZ` before the preemption point. -/
def JAtPreMVL (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop :=
  ∃ (s0 : S) (a0 : A) (σ0 : Fl4Spec.State Unit) (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64)
    (Lst : U64 → List U64) (D : Set U64),
    (JAtZ (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 ∧ Vs.NoSwitch σ0 ∧ PPR0 σ0 ∧ MR a0 σ0.machineState ∧
      ValidMachineTime σ0 ∧ ValidIrqMasks σ0 ∧ VxE Z) ∧
    sched.preemption_point st arI s0 a0 = ok (.Err .Preempted, s, a) ∧
    (.error (), σ) ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ0).1 ∧
    LiveDN (L := L) Z.th H Cs Z.G s σ

theorem JAtPreMVL.toMV {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : JAtPreMVL (L := L) arI AR MR s a σ) :
    JAtPreMV (L := L) arI AR MR s a σ :=
  let ⟨s0, a0, σ0, Z, H, Cs, Ac, Lst, D, ⟨J, h1, h2, h3, h4, h5, _⟩, hp, hm, _⟩ := h
  ⟨s0, a0, σ0, ⟨⟨Z, H, Cs, Ac, Lst, D, J, inferInstance⟩, h1, h2, h3, h4, h5⟩, hp, hm⟩

/-- **The deletion's state after a preemption with liveness** (module
docstring). -/
def WJPML (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets) (H : P1.Heap)
    (Cs : Set U64) (kb : U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) : Prop :=
  WJP (L := L) arI AR Z H Cs kb s a σ G ∧ JAtPreMVL (L := L) arI AR MR s a σ ∧
    LiveDN (L := L) Z.th H Cs G s σ

theorem WJPML.toM {kb : U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    (h : WJPML (L := L) arI AR MR Z H Cs kb s a σ G) : WJPM (L := L) arI AR MR Z H Cs kb s a σ G :=
  ⟨h.1, h.2.1.toMV arI⟩

/-- **`JAt` with `LiveDN` at its own ghosts** (module docstring). -/
def JAtL (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ LiveDN (L := L) Z.th H Cs Z.G s σ ∧ VxE Z

theorem JAtL.toJAt {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : JAtL (L := L) arI AR s a σ) :
    JAt (L := L) arI AR s a σ :=
  let ⟨Z, H, Cs, Ac, Lst, D, J, _, _⟩ := h; ⟨Z, H, Cs, Ac, Lst, D, J, inferInstance⟩

end

end

end Fl4Proofs.P3
