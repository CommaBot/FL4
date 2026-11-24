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

set_option maxHeartbeats 8000000 in
/-- **The frame-cap invocation beside the serial gate, accepted** (module
docstring): `kernel_entry_reachU29`'s syscall clause for
`handle_invocation_local … n p` on the runs that return `true`, with `p`
fl4-sync's plan at the entry state. -/
theorem kernel_entry_reachU29V [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧
      (∀ (n : I64) (c : Fl4Spec.Syscall) (p : localinv.Plan), σ.curThread ≠ σ.idleThread → NativeSys n c →
        (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
          ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            KDispHypsKVU29 (L := L) arI AR (Z.mv Z.G V') H Cs D' s' a' σb n c) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            ∀ ct', sched.cur_thread st s' = ok ct' →
              JDecMRLK (L := L) arI VtxK AR MR (Z.mv Z.G V') H Cs D' s' a' σb ct') →
        (∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
          (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
            JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
            KFinAtR13 (L := L) arI AR Z' H' Cs' s' a' x.2) →
        localinv.plan st s n = ok (some p) →
        syscall.handle_invocation_local st arI s a n p ⦃ r => r.1 = true →
          ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
            RJ (L := L) arI AR r.2.1 r.2.2 σ' ∧ SInvX σ' ∧ MR r.2.2 σ'.machineState ∧
            SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ SInvUZ.UtPgR σ' ∧
            JReachU17 (L := L) arI AR MR r.2.1 r.2.2 σ' ⦄) := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, -, -, -, -, -, -, -, hSys, -⟩ :=
    kernel_entry_reachU29 arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
  refine ⟨Z, H, Cs, Ac, Lst, D, J, fun n c p hct hn hflag hK hDL hFin hp => ?_⟩
  have hbuf : ∀ t, sched.cur_thread st s = ok t →
      msg.lookup_ipc_buffer st s false t ⦃ w => P1.BufOK {b | P1.OutsideObjs st (P1.Heap.tcbs H) Cs s b} w ⦄ := by
    intro t et
    have hc : t ∈ P1.Heap.tcbs H := by
      obtain ⟨⟨_, _, hSQ⟩, -, -, -, -⟩ := J.bxi
      rw [P1.cur_thread_ok] at et; rw [← P1.ok_inj_ff et]; exact hSQ.curT
    exact J.sbufOK hc
  exact P1.inv_local_triple arI hA J.bxi (fun _ et => J.cnOff et) hbuf hflag hp
    (hSys n c hct hn hflag hK hDL hFin)

end

end

end Fl4Proofs.P3.SInvR.G5
