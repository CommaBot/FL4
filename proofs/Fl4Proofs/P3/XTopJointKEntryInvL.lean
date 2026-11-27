/-
P3 (KENTRY-PLAN lcv): **the frame-cap invocation beside the serial gate,
accepted** (`syscall.handle_invocation_local`, fl4-sync `local_invocation`).

`JAtZ.sbufOK`: at a `JAtZ` state every TCB's *sender* IPC buffer (the lookup
with `is_receiver = false`, which also takes a read-only frame) lies outside
the TCBs and the nodes, word by word (`P1.BufOK`): the buffer the spec finds
is in `Z.B` (`BufCover` at `false`), its words are aligned (`balign`), apart
from every typed object (`JAtZ.bufWordG`, the receive-buffer lemma
generalised over the receiver flag) and from the nodes (`nodeB`). This is
the one placement fact P1's `inv_local_same` asks beyond pf1's (`BXI`,
`CnOff`): `lookup_extra_caps` reads the extra-cap words of that buffer.

**`kernel_entry_reachU29V`**: from `kernel_entry_reachU29`'s premises and
`JReachU17 s a σ`, an accepted `handle_invocation_local … n p` has the
postcondition of `kernel_entry_reachU29`'s syscall clause, under the clause's
own inputs and fl4-sync's contract that `p` is the plan
`localinv.plan st s n` computed at the entry state (an input, not a premise
on the state). No premise is added to the top.
-/
import Fl4Proofs.P3.XTopJointKEntryU29
import Fl4Proofs.P3.XTopJointKEntryRRF
import Fl4Proofs.P3.XTopJointKEntryFF
import Fl4Proofs.P1.LocalInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 8000000 in
/-- **Every TCB's sender buffer outside the TCBs and nodes** (module
docstring). -/
theorem JAtZ.sbufOK {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {y : U64} (hy : y ∈ P1.Heap.tcbs H) :
    msg.lookup_ipc_buffer st s false y ⦃ w => P1.BufOK {b | P1.OutsideObjs st (P1.Heap.tcbs H) Cs s b} w ⦄ := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hth : Z.th y = some .tcb := (hJ.tcb y).2 hy
  have hyT := J.thT y hth
  obtain ⟨xd, hk, hws⟩ := J.buf y hyT
  obtain ⟨hOK, hBC, -⟩ := J.xferH
  refine WP.spec_mono (lookup_buf_full s σ J.xtop.rel.2.1.1 J.xtop.rel.2.1.2.1 hth hk hOK false) ?_
  rintro w ⟨h0, hp⟩ hw0 i hi
  cases hb : Endp.ipcBufOf false xd with
  | none => exact absurd (h0.2 hb) hw0
  | some p' =>
    have e := hp hws p' hb
    have hwB := hBC y hyT xd false p' hk hb w e i hi
    have hal := (J.xtop.fin.1.2.ep.balign _ hwB).1
    obtain ⟨hAp, -⟩ := J.bufWordG hOK hth hk hb i.val hi (b := Endp.fl4BufA w i) (by rw [fl4BufA_bv, e])
    show P1.OutsideObjs st (P1.Heap.tcbs H) Cs s (Endp.fl4BufA w i)
    refine ⟨hal, fun t ht => ?_, fun c hc => ?_⟩
    · rcases hAp t .tcb ht (fun _ e => by cases e) with e | e
      · left; omega
      · right; simpa [P1.HKind.bits] using e
    · have e := J.nodeB _ hwB c (J.kern.csLt c hc)
      dsimp only at e
      rcases e with e | e <;> omega

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

end

end

end Fl4Proofs.P3.SInvR.G5
