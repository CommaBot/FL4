/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN.md sch8 (1)):
**`kernel_entryJ2`: `kernel_entryJ` without `SignalRestJHyp` and `hvm`.**

Both premises are VT-x cases, outside the native scope, and `kernel_entryJ`
already takes `hNS` [S] (`NativeScope` at every `JHoleAt` state: no TCB is
`RunningVM`, IpcLeaves, DESIGN §9):
* `SignalRestJHyp` [W] (ScSignalJ; `KFinAt.w`) covers only an idle
  notification whose bound TCB is `RunningVM`: a `JAtZ` state is a `JHole`
  over itself (`JAtZ.toHole`), so `hNS` refutes the case
  (`signalRestJHyp_of_ns`, the argument XTopJointIrq uses inline).
* `hvm` [S] (the current thread of a `JAt` state is not `RunningVM`) likewise
  (`hvm_of_ns`).
`KFinAt2` is `KFinAt` without the `w` field.
-/
import Fl4Proofs.P3.XTopJointKEntry
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- `KFinAt` without `w` (`SignalRestJHyp`, discharged by `hNS`). -/
structure KFinAt2 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop where
  hd : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ
  vt : ∀ (V1 : XVs) (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (Ac1 : Set U64) (Lst1 : U64 → List U64)
      (D1 : Set U64), JAtZ (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s1 a1 σ1 → ∀ t ∈ Z.T,
        Z.th t = some .tcb ∧ ∀ p asid, capAt (L.mem s1) (slotOf t 1) = ok (.Pml4 p true asid) → asid ≠ 0#u64
  arch : ArchSwF st arI Z.N Z.T Z.C Z.c
  archNd : ArchNdF st Z.N Z.T Z.C Z.c
  fo : FpuOwnOK σ
  sni : SniHyp st arI Z.N Z.T Z.C Z.c
  send : SendHyp st arI Z.N Z.T Z.C Z.c
  tail : sched.schedule st arI s a ⦃ r => ∀ (rf : S × A) σ1 σ' (D1 : Set U64), Fires σ σ1 →
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) →
      P1.WritesIn st rf.1 r.1 (KFootN st Z.T Z.N Z.C Z.c rf.1 σ1) →
      SchedRel st Z.N Z.T Z.C Z.c r.1 σ' → Inv σ' → CurInv σ' → ActIdle σ' →
      SchTailHypsR AR Z H D1 r.1 r.2 σ' ⦄

variable {arI}

/-- **`SignalRestJHyp` from the native scope** (module docstring). -/
theorem signalRestJHyp_of_ns {AR : A → Fl4Spec.Cr3 → Prop}
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (H : P1.Heap) (Cs : Set U64) : SignalRestJHyp (L := L) arI AR H Cs := by
  intro Z1 Ac1 Lst1 D1 s1 a1 σ1 n1 b1 x1 J1 _ _ hb
  obtain ⟨-, t, tcb, -, hkt, hvm⟩ := hb
  exact absurd hvm (hNS s1 a1 σ1 ⟨Z1, H, Cs, Ac1, Lst1, D1, s1, a1, σ1, J1.toHole⟩ t tcb hkt)

/-- **`kernel_entryJ`'s `hvm` from the native scope** (module docstring). -/
theorem hvm_of_ns {AR : A → Fl4Spec.Cr3 → Prop}
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ) :
    ∀ s1 a1 σ1, JAt (L := L) arI AR s1 a1 σ1 → ∀ x, σ1.kheap σ1.curThread = some (.tcb x) →
      x.tcbState ≠ .runningVM := by
  rintro s1 a1 σ1 ⟨Z1, H1, Cs1, Ac1, Lst1, D1, J1⟩ x hk
  exact hNS s1 a1 σ1 ⟨Z1, H1, Cs1, Ac1, Lst1, D1, s1, a1, σ1, J1.toHole⟩ _ x hk

theorem KFinAt2.toK {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64} {s : S} {a : A}
    {σ : Fl4Spec.State Unit}
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (F : KFinAt2 (L := L) arI AR Z H Cs s a σ) : KFinAt (L := L) arI AR Z H Cs s a σ :=
  ⟨F.hd, F.vt, signalRestJHyp_of_ns hNS H Cs, F.arch, F.archNd, F.fo, F.sni, F.send, F.tail⟩

/-- **The kernel entry for a native system call at `J`**, `kernel_entryJ`
without `SignalRestJHyp` [W] (`KFinAt2`) and without `hvm` [S], both from
`hNS` (module docstring). Other premises as `kernel_entryJ`. -/
theorem kernel_entryJ2 [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → KBudget arI a (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZ (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' σb →
        KDispHyps (L := L) arI AR Z' H' Cs' D' s' a' σb n c)
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZ (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAt2 (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hPF : KPreFinHyp (L := L) arI AR c σ)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hRest : JPreemptRestHypJ (L := L) arI AR) (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_syscall st arI s a n ⦃ r => KPost (L := L) arI AR c σ r ⦄ :=
  kernel_entryJ s a σ J hni n c hn hflag hB hK
    (fun x hx Z' H' Cs' Ac' Lst' D' s' a' J' => (hFin x hx Z' H' Cs' Ac' Lst' D' s' a' J').toK hNS)
    hPF hARI hA hnd hPP hmrt hmb hIP hNS hRest hT hmax htu (hvm_of_ns hNS)

end

end

end Fl4Proofs.P3
