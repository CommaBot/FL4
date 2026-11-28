/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN sch14): **`kernel_entryJ9M`:
`JMidRecvHyp` narrowed to the receive under a pending switch or
reschedule.** The mid state of ReplyRecv / NBSendRecv / NBSendWait after a
resumed first phase is an entry state of the receive, so the receive there
is the proved one (`handle_recvJ` with `jRecvIpcHypL_of` / `jRecvSigHyp_of`).

* `hnq` (ct in no ready queue) and "no switch to ct pending" at the mid
  state: XTopJointMidRunQ's `midRunQ_shell` (a frame from the entry's
  `ctnq` [J] and resumed action), with `JMidPerfHypQ` [W] (sch12's
  `JMidPerfHyp` widened to the queue / action fact for the same three
  performs, same path restriction) for `JMidPerfHyp`.
* `JMidVfhHyp` [J]: the current thread's fault handler valid at the `.ok`
  outcomes of the first phase from the dispatch state (l4v `valid_objs`'
  `valid_tcb`, `valid_fault_handler (tcb_fault_handler)`, kept by
  `handle_invocation` (`hinv_invs`); JEntryAt's `vfh` [J] at the mid state).
  Not a frame: the first phase's cap writes (`cte_insert` of a granted cap,
  IRQ control's handler cap, the arch caps' updates) reach a slot found by a
  CSpace lookup, which is a CNode slot only by `valid_cap`, so the TCB's
  fault-handler slot is untouched only by that invariant.
* `JMidRecvHypS` [W] (narrows `JMidRecvHyp`): the receive only at the `.ok`
  outcomes whose action is NOT `resumeCurThread` (a switch to another thread
  or a reschedule pending after the first phase woke a thread), with `hnq`,
  "no switch to ct" and `hvfh` there as premises. l4v `handle_recv_corres`
  under `scheduler_act_sane` at that state. Removal: sch12 (2) (ii)/(iii)
  (the receive leaves from `MidE` with a switch action, a chooseNewThread mid
  state, the blocking leaves ending in `JAtZR`).
* `jMidRecvHyp_of`: `JMidRecvHyp` from the three (the resumed case by
  `handle_recvJ`), `KDispHyps9M` (`mid`: entry facts, `JMidPerfHypQ`,
  `JMidRecvHypS`, `JMidVfhHyp`), `dispatch_all9M`, `kernel_entryJ9M` =
  `kernel_entryJ8` with `KDispHyps9M` for `KDispHyps8`.
-/
import Fl4Proofs.P3.XTopJointMidRunQ
import Fl4Proofs.P3.XTopJointKEntry8
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **[W] The receive at a mid state with a pending switch or reschedule**
(module docstring). -/
def JMidRecvHypS (AR : A → Fl4Spec.Cr3 → Prop) (cptr : Fl4Spec.CapRef) (cr : Bool) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) true false false true true cptr).run σ).1, y.1 = .ok () →
    y.2.schedulerAction ≠ .resumeCurThread → (∀ d p, y.2.curThread ∉ y.2.readyQueues d p) →
    y.2.schedulerAction ≠ .switchThread y.2.curThread →
    (∀ x, y.2.kheap y.2.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler) →
    ∀ (s1 : S) (a1 : A), JMid (L := L) arI AR s1 a1 y.2 →
      syscall.handle_recv st arI s1 a1 true cr ⦃ r => ∃ z ∈ (Fl4Spec.handleRecv (Z := Unit) true cr y.2).1,
        RelTopM (L := L) r.1 z.2 ∧ ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
          JAtZR (L := L) arI AR Z H Cs Ac Lst D r.1 r.2 z.2 ∧ VxE Z ⦄

end

/-- **[J] The current thread's fault handler valid after the first phase**
(module docstring). -/
def JMidVfhHyp (cptr : Fl4Spec.CapRef) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) true false false true true cptr).run σ).1, y.1 = .ok () →
    ∀ x, y.2.kheap y.2.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop}

set_option maxHeartbeats 4000000 in
/-- **`JMidRecvHyp` from `JMidPerfHypQ` [W], `JMidVfhHyp` [J] and
`JMidRecvHypS` [W]** (module docstring): the resumed mid state is a receive
entry (`handle_recvJ`). -/
theorem jMidRecvHyp_of (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    {cptr : Fl4Spec.CapRef} {cr : Bool} {σ : Fl4Spec.State Unit}
    (hs : MidRun.CQ σ.curThread σ) (hq : MidRun.NQ σ.curThread σ) (hP : MidRun.JMidPerfHypQ true cptr σ)
    (hV : JMidVfhHyp cptr σ) (hS : JMidRecvHypS (L := L) arI AR cptr cr σ) :
    JMidRecvHyp (L := L) arI AR cptr cr σ := by
  intro y hy hok s1 a1 hM
  obtain ⟨⟨hct0, -⟩, hnq0, hsw⟩ := MidRun.midRunQ_shell true true cptr σ hs hq hP y hy
  have hnq : ∀ d p, y.2.curThread ∉ y.2.readyQueues d p := by rw [hct0]; exact hnq0
  have hvf := hV y hy hok
  by_cases ha : y.2.schedulerAction = .resumeCurThread
  · obtain ⟨-, ⟨Z, H, Cs, Ac, Lst, D, J, _⟩, -, hni1⟩ := hM
    have hni : Entered y.2 := ⟨hni1, ha⟩
    have hct := cur_thread_eq (L := L) s1
    obtain ⟨hcur, -⟩ := J.curEq hct
    have hctT := TopSR.cur_mem J.xtop.fin.1 hcur.symm
    refine WP.spec_mono (handle_recvJ arI hAT s1 a1 y.2 J hni hct hnq hvf true cr
      (jRecvIpcHypL_of hAT hmax (htu a1) J hctT hcur hni hnq true)
      (jRecvSigHyp_of hAT J hctT hcur hni hnq true)) ?_
    rintro r ⟨z, hz, hrl, Z', H', Cs', Ac', Lst', D', J', _⟩
    exact ⟨z, hz, hrl, Z', H', Cs', Ac', Lst', D', J'.toR, inferInstance⟩
  · exact hS y hy hok ha hnq (by rw [hct0]; exact hsw) hvf s1 a1 hM

/-- `CQ ∧ NQ` at a resumed dispatch state (`MidEntry` from `JEntryAt.cnf`,
`JEntryAt.ctnq`). -/
theorem JAtZ.midCQ {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (hE : JEntryAt (L := L) arI AR Z H Cs s a σ) : MidRun.CQ σ.curThread σ ∧ MidRun.NQ σ.curThread σ := by
  have hME := J.midEntry hni hE.cnf
  exact ⟨⟨⟨rfl, fun x hx => ⟨hME.run x hx, hME.nf x hx⟩⟩, hE.ctnq, by rw [hni.2]; intro e; cases e⟩, hME.nq⟩

end

end

end Fl4Proofs.P3

