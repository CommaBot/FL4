/-
P3 (DESIGN.md §9), invariant line G4 (g4k, KENTRY-PLAN g4k (4)): **one
Untyped VT-x scope premise at the top.** `JDecMRLK VtxK` [scope] is not a
restatement of the carried `JVtxHypMU` (KDispHypsKV35's third conjunct): it
asks `MR` at the non-preempted outcome (`JAtM`), `JVtxHypMU` only `JAt`. The
converse holds: `jVtxHypMU_of` derives `JVtxHypMU` from `JDecMRLK VtxK` at the
same state (`XCapP.monoX`, `JAtM → JAt`). So the dispatch bundle drops it:

* `KDispHypsKV41`: `KDispHypsKV35` without the `JVtxHypMU` conjuncts;
  `KDispHypsKV41.to35` (with `JDecMRLK VtxK` at the same state).
* NEW TOPS **`kernel_entryJ41V`**, **`kernel_entry_reachMD4V`**: `kernel_entryJ41`
  / `kernel_entry_reachMD4` with `hK : … → KDispHypsKV41 …` (asked at the same
  states as `hDL`): the VT-x Untyped retype enters the top once, as `hDL`.
-/
import Fl4Proofs.P3.XTopJointKEntry41
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- **`XCapP` is monotone in the non-preempted post.** -/
theorem XCapP.monoX {X X' XP : S → A → Fl4Spec.State Unit → Prop} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    {lbl length slot : U64} {c : capability.Cap} {blk call don fp : Bool} {buf : U64}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data} {args : List Fl4Spec.Data}
    {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    {buffer : Option Fl4Spec.ObjRef} {ct : U64}
    (h : XCapP (L := L) arI X XP s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer ct)
    (hX : ∀ s a σ, X s a σ → X' s a σ) :
    XCapP (L := L) arI X' XP s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer ct := by
  rcases h with h | h
  · refine Or.inl (WP.spec_mono h fun res hr => ?_)
    have hI : ∀ s a σ, (if res.1 = .Err .Preempted then XP s a σ else X s a σ) →
        (if res.1 = .Err .Preempted then XP s a σ else X' s a σ) := fun s a σ hx => by
      split
      · rw [if_pos (by assumption)] at hx; exact hx
      · rw [if_neg (by assumption)] at hx; exact hX _ _ _ hx
    exact match hr with
    | Or.inl ⟨e, h1, h2, h3, h4⟩ => Or.inl ⟨e, h1, h2, h3, hI _ _ _ h4⟩
    | Or.inr ⟨inv, h1, σ1, h2, y, hy, h3, h4⟩ => Or.inr ⟨inv, h1, σ1, h2, y, hy, h3, hI _ _ _ h4⟩
  · refine Or.inr (WP.spec_mono h fun res hr => ?_)
    exact match hr with
    | Or.inl ⟨e, h1, h2, h3, h4⟩ => Or.inl ⟨e, h1, h2, h3, hX _ _ _ h4⟩
    | Or.inr ⟨h1, h2, inv, h3, σ1, h4, rr, σy, h5, z, hz, h6, h7⟩ =>
      Or.inr ⟨h1, h2, inv, h3, σ1, h4, rr, σy, h5, z, hz, h6, hX _ _ _ h7⟩

variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs D : Set U64}

/-- **`JVtxHypMU` from `JDecMRLK VtxK`** at the same state (module docstring). -/
theorem jVtxHypMU_of {s : S} {ar : A} {σ : Fl4Spec.State Unit} {ct : U64}
    (h : JDecMRLK (L := L) arI VtxK AR MR Z H Cs D s ar σ ct) :
    JVtxHypMU (L := L) arI AR MR Z H Cs D s ar σ ct := by
  intro hR hVT hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl p sb fi dev hc x hx
    h14 h19 excaps buffer hXO hXN hLb hA5 hN
  exact (h hR hVT hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl _ hc
    ⟨x, hx, h14, h19⟩ excaps buffer hXO hXN hLb hA5 hN).monoX fun _ _ _ h => h.1

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`KDispHypsKV35` without `JVtxHypMU`** (module docstring). -/
structure KDispHypsKV41 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets)
    (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JEntryAtR3 (L := L) arI AR Z s a σ ∧
    JPathAtM35 (L := L) arI AR Z H Cs D s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP))
  mid : ∀ ct rg sr cr, sched.cur_thread st s = ok ct → MidSysR n c rg sr cr →
    JEntryAtR3 (L := L) arI AR Z s a σ ∧
    JPathAtM35 (L := L) arI AR Z H Cs D s a σ ct false false true true (L.mem s (regA ct rg))

variable {arI}

theorem KDispHypsKV41.to35 {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets}
    {H : P1.Heap} {Cs D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : KDispHypsKV41 (L := L) arI AR Z H Cs D s a σ n c)
    (hDL : ∀ ct, sched.cur_thread st s = ok ct → JDecMRLK (L := L) arI VtxK AR MR Z H Cs D s a σ ct) :
    KDispHypsKV35 (L := L) arI AR MR Z H Cs D s a σ n c :=
  ⟨fun ct call bl don hct hi => let ⟨e, p⟩ := h.inv ct call bl don hct hi; ⟨e, p, jVtxHypMU_of (hDL ct hct)⟩,
   fun ct rg sr cr hct hm => let ⟨e, p⟩ := h.mid ct rg sr cr hct hm; ⟨e, p, jVtxHypMU_of (hDL ct hct)⟩⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **The newest top** (module docstring): `kernel_entryJ41` with `hK : … → KDispHypsKV41`
(no `JVtxHypMU`: derived from `hDL` at the same state, `KDispHypsKV41.to35`). -/
theorem kernel_entryJ41V [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hct : σ.curThread ≠ σ.idleThread)
    (hR : MR a σ.machineState) (hX : SInvX σ)
    (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        KDispHypsKV41 (L := L) arI AR (Z.mv Z.G V') H Cs D' s' a' σb n c)
    (hDL : ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        ∀ ct', sched.cur_thread st s' = ok ct' → JDecMRLK (L := L) arI VtxK AR MR (Z.mv Z.G V') H Cs D' s' a' σb ct')
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR31 (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR)
    (hFast : n = fl4_abi.syscall.SysReplyRecv →
      FastRR (L := L) (arI := arI) s a n (fun r => KPostM (L := L) arI AR MR c σ r)) :
    syscall.handle_syscall st arI s a n ⦃ r => KPostXM (L := L) arI AR MR c σ r ⦄ :=
  kernel_entryJ41 s a σ J hct hR hX n c hn hflag
    (fun σb hBA V' Ac' Lst' D' s' a' hfr J' =>
      (hK σb hBA V' Ac' Lst' D' s' a' hfr J').to35 (hDL σb hBA V' Ac' Lst' D' s' a' hfr J'))
    hDL hFin hARI hA hnd hM hKD hIo hIoa hPA hIA hmrt hmb hT hmax htu hRef hPI hFast

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **`kernel_entry_reachMD4` with `KDispHypsKV41`** (by `kernel_entryJ41V`): no `JDispMR` input; the
per-state premises are g4a's (`hflag`, `hK`, `hFin`, `hFast` for `KPostM`)
and `hDL` [W] (`JDecMRL2` at the dispatch states). -/
theorem kernel_entry_reachMD4V [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachM (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ SInvX σ ∧ MR a σ.machineState ∧
      ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c →
      (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
        ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
      (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
        (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
          JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
          KDispHypsKV41 (L := L) arI AR (Z.mv Z.G V') H Cs D' s' a' σb n c) →
      (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
        (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
          JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
          ∀ ct', sched.cur_thread st s' = ok ct' → JDecMRLK (L := L) arI VtxK AR MR (Z.mv Z.G V') H Cs D' s' a' σb ct') →
      (∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
        (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
          JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
          KFinAtR31 (L := L) arI AR Z' H' Cs' s' a' x.2) →
      (n = fl4_abi.syscall.SysReplyRecv →
        FastRR (L := L) (arI := arI) s a n (fun r => KPostM (L := L) arI AR MR c σ r)) →
      syscall.handle_syscall st arI s a n ⦃ r => (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).2 ∨
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          JReachM (L := L) arI AR MR r.1 r.2 σ' ⦄ := by
  obtain ⟨⟨Z, H, Cs, Ac, Lst, D, J⟩, hX, hR⟩ := jreach_invM hnd hJ
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, hR, fun n c hct hn hflag hK hDL hFin hFast => ?_⟩
  have hE := kernel_entryJ41V (MR := MR) s a σ J hct hR hX n c hn hflag hK hDL hFin hARI hA hnd hM hKD hIo hIoa hPA hIA
    hmrt hmb hT hmax htu hRef hPI hFast
  obtain ⟨⟨s', a'⟩, hv, hP⟩ := spec_exists hE
  rw [hv, WP.spec_ok]
  rcases hP with hF | ⟨σ', hy, hRJ, hM', hX'⟩
  · exact Or.inl hF
  · exact Or.inr ⟨σ', hy, hRJ, hX', hM', JReachM.step n c hJ hct hn hv hy ⟨hRJ, hM'⟩⟩

end

end

end Fl4Proofs.P3
