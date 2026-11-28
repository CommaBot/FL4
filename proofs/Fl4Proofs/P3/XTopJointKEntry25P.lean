/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN mr10 GOAL 2): **`kernel_entryJ25P`**,
XTopJointKEntry23P's `kernel_entryJ23P` on the newest receive premise: the mid
receive leaves asked as sch23b's `JMidLeavesHyp14` [W] (XTopJointKEntry23M)
instead of sch22's `JMidLeavesHyp13`, converted per dispatch state by
`jMidLeavesHyp_of14` (as mr8's J21P did for `JMidLeavesHyp13`).

* `KDispHypsKV25`: `KDispHypsKV23` with `JMidLeavesHyp14`; `.to23`.
* `kernel_entryJ25P` (wrapper over J23P); `j25P_platform` (non-vacuity of the
  platform premises: `j23P_platform`).
-/
import Fl4Proofs.P3.XTopJointKEntry23P
import Fl4Proofs.P3.XTopJointKEntry23M
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`KDispHypsKV23` with sch23b's mid receive leaves** (module docstring). -/
structure KDispHypsKV25 (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets)
    (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JEntryGlobM (L := L) arI AR MR Z.th ∧ JEntryAt (L := L) arI AR Z H Cs s a σ ∧
    JPathAtM (L := L) arI AR Z H Cs D s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)) ∧
    JVtxHypMU (L := L) arI AR MR Z H Cs D s a σ ct
  recv : ∀ bl cr, RecvSys n bl cr → (∀ d p, σ.curThread ∉ σ.readyQueues d p) ∧
    (∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler)
  mid : ∀ ct rg sr cr, sched.cur_thread st s = ok ct → MidSysR n c rg sr cr →
    JEntryGlobM (L := L) arI AR MR Z.th ∧ JEntryAt (L := L) arI AR Z H Cs s a σ ∧
    JPathAtM (L := L) arI AR Z H Cs D s a σ ct false false true true (L.mem s (regA ct rg)) ∧
    MidRun.JMidPerfHypQ true (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ ∧
    JMidVfhHyp (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ ∧
    JMidLeavesHyp14 (L := L) arI AR (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ ∧
    JVtxHypMU (L := L) arI AR MR Z H Cs D s a σ ct

variable {arI} {MR : A → Fl4Spec.MachineState → Prop}

/-- **`KDispHypsKV23` from `KDispHypsKV25`** (sch23b's conversion). -/
theorem KDispHypsKV25.to23 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets}
    {H : P1.Heap} {Cs D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : KDispHypsKV25 (L := L) arI AR MR Z H Cs D s a σ n c) (hAT : P0.ArchTotal arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    KDispHypsKV23 (L := L) arI AR MR Z H Cs D s a σ n c where
  inv := h.inv
  recv := h.recv
  mid := fun ct rg sr cr hct hm => by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h.mid ct rg sr cr hct hm
    exact ⟨h1, h2, h3, h4, h5, jMidLeavesHyp_of14 hAT hmax htu h6, h7⟩

end

end

end Fl4Proofs.P3
