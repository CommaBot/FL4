/-
P3 (line p3J, gen 3): **`kernel_entry_reachU37`** = `kernel_entry_reachU36` for the invocations that are
not VT-x invocations, with the VT-x [scope] leaves of the path premise removed.

**What the spec extension says** (`Fl4Spec/Ext/VirtP3x`, `VirtDispatch`, `VirtFinalise`, `VirtEptInv`): the
extended decoder `fl4DecodeInvocationV` already models FL4 on all three mismatches of the p3J inventory —
label 88 on a thread cap (`fl4SetEptRootLabel`; FL4 `crates/fl4-core/src/tcb.rs:410-419`), label 60 on a
frame cap and the EPT-mapped frame's map / unmap (`fl4PageMapEptLabel`, `decodePageMapEpt`; FL4
`crates/fl4-core/src/arch/x86_64/vspace.rs:495-498`), and the VT-x retype gate (`untypedVtxGate`,
`fl4DecodeUntypedInvocationV`: `InvalidArgument 0` when `virtKind = none`; FL4
`crates/fl4-core/src/untyped.rs:43`). VirtP3x's `VirtRoute` names exactly these inputs, and
`fl4DecodeInvocationV_base` proves that off them the extended decoder *is* the ported one. P3's tops refine
the ported kernel (`fl4KernelEntrySyscall`, `fl4DecodeInvocation`), so on a VirtRoute entry FL4 and the
refined spec differ by construction (the "exact exceptions of P3x"); the composition of the extended kernel
(VIRT-PLAN R7) is not available to refine against. So no spec module is added: the bridge is a narrowing.

**The narrowing.** `VtxInv c lbl argsU` [S]: the invoked cap and message are a VT-x invocation — a thread cap
at `TCBSetEPTRoot` (88), a frame cap with the EPT flag or at `X86PageMapEPT` (60), an untyped cap with first
message word in 14..18 (FL4's VT-x object types `ot::X86Vcpu ..< ot::Count`). These are exactly the cases of
`JPathAtMU35` with a VT-x leaf (`JVtxScope`, inventory K6 / K7 / K3); they contain every `VirtRoute` input
of a native cap (`vtxInv_of_virtRoute`, P3JVtxBridge) and also the VT-x inputs on which ext and port agree
but FL4's VT-x path has no functional refinement (first-phase label 88, unmapped EPT-flagged frames, VT-x
retypes with VT-x present: still [scope]).
* `KNoVtx s σ n c` [S] (new antecedent of the syscall clause, at the dispatch states like `KDispHyps`): for
  the invocation (`inv`) and mid (`mid`) syscalls, the slot / cap the lookup returns (`LookAt`) with the
  current message is not a `VtxInv`.
* `JPathMEU37`: `JPathMEU30` with no VT-x leaf (thread and frame caps: `True`; untyped caps: `JUtPathU37`
  = `fan`, `core0`, `rcb`, without `vtx`). `JPathMEU37.toU30`: under `¬ VtxInv` it gives `JPathMEU30`.
* `JPathAtMU37`, `KDispHypsKVU37`: `JPathAtMU35` / `KDispHypsKVU36` on `JPathMEU37`; `KDispHypsKVU37.toU36`.

**Premise diff U36 → U37** (syscall clause): `KDispHypsKVU36 …` ↦ `KDispHypsKVU37 …` (the leaves K3 `vtx`, K6,
K7 removed), and the new antecedent `KNoVtx …` [S] before it (the clause now covers non-VT-x invocations
only, explicitly). Everything else verbatim. [W] 0.
Not narrowed here: `JDecMRLK … VtxK …` (D1 / D2) still quantifies every label and slot at the dispatch state.
It is *not* false (correction to the gen-1 inventory): its own `JPathM` hypothesis carries the same
`JVtxScope`, so D1 / D2 only ask that FL4's VT-x decode keep `MR` (the [J] MR upgrade `XCapP JAt → XCapP
JAtM JAtPreMV`); narrowing it to the invoked slot needs the gen-2 transport through `JDecMRL2` (open).
Named premises still open: as U36's (module docstring there), minus K3 / K6 / K7, plus [S] `KNoVtx`. No sorry.
-/
import Fl4Proofs.P3.XTopJointKEntryU36
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

/-- **A VT-x invocation** [S] (module docstring): the invoked cap and the message's label / first word. -/
def VtxInv : capability.Cap → U64 → List U64 → Prop
  | .Thread _, lbl, _ => lbl = fl4_abi.label.TCBSetEPTRoot
  | .Frame _ _ _ _ _ ep _ _, lbl, _ => ep = true ∨ lbl = fl4_abi.label.X86PageMapEPT
  | .Untyped .., _, argsU => ∃ x, argsU.head? = some x ∧ 14 ≤ x.val ∧ x.val < 19
  | _, _, _ => False

/-- `JUtPathMU29` / `JDevPathU28` without `vtx`. -/
structure JUtPathU37 (Z : XSets) : Prop where
  /-- [P] as `JUtPathM.fan`. -/
  fan : Fl4Spec.retypeFanOutLimit = 256#64
  /-- [P] as `JUtPathM.core0`. -/
  core0 : Z.c = 0#u64
  /-- [P] as `JUtPathM.rcb`. -/
  rcb : Fl4Spec.resetChunkBits = 16

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JPathMEU30` without the VT-x leaves**: thread and frame caps ask nothing, untyped caps `JUtPathU37`. -/
def JPathMEU37 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (lbl length : U64)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data)
    (argsU : List U64) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) (ct : U64) : capability.Cap → Prop
  | .Thread _ => True
  | .Frame .. => True
  | .Untyped .. => JUtPathU37 Z
  | c => JPathMEU30 (L := L) arI AR Z H Cs D s ar σ lbl length blk call don fp buf extra slbl argsU ci sl excaps
      buffer ct c

/-- **`JPathAtMU35` on `JPathMEU37`.** -/
def JPathAtMU37 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (ct : U64) (is_call blocking can_donate first_phase : Bool) (cptr : U64) : Prop :=
  ∀ (info : msginfo.MessageInfo) (mi : Fl4Spec.MessageInfo) (buf : U64) (buffer : Option Fl4Spec.ObjRef)
    (r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault)
    (er : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr))) (argsU : List U64),
    msg.msg_info st s ct = ok info →
    Fl4Spec.getMessageInfo (Z := Unit) ct.bv σ = ({(mi, σ)}, False) →
    msg.lookup_ipc_buffer st s false ct = ok buf →
    Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σ = ({(buffer, σ)}, False) →
    ipc.lookup_extra_caps st s ct buf info = ok r2 →
    (Fl4Spec.lookupExtraCaps (Z := Unit) ct.bv buffer mi).run σ = ({(er, σ)}, False) →
    Fl4Spec.getMrs (Z := Unit) ct.bv buffer mi σ = ({(argsU.map UScalar.bv, σ)}, False) →
    ∀ (sl : Fl4Spec.CslotPtr) (c : capability.Cap) (e : Aeneas.Std.Array obj.Slot 3#usize)
      (exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), (∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) →
      capAt (L.mem s) (cslotAddr sl) = ok c → Fl4Spec.getCap (Z := Unit) sl σ = ({(absCap c, σ)}, False) →
      r2 = .Ok e → er = .ok exs → Vs.NativeCap c → LookAt ct cptr σ sl c →
      JPathMEU37 (L := L) arI AR Z H Cs D s ar σ info.label (msgLen info buf) blocking is_call can_donate first_phase buf e
        mi.miLabel argsU (Fl4Spec.toBl cptr.bv) sl exs buffer ct c

/-- **The invoked cap is not a VT-x invocation** [S]: at the slot / cap the lookup returns, with the current
message's label and words. -/
def NoVtxAt (s : S) (σ : Fl4Spec.State Unit) (ct cptr : U64) : Prop :=
  ∀ (info : msginfo.MessageInfo) (mi : Fl4Spec.MessageInfo) (buffer : Option Fl4Spec.ObjRef) (argsU : List U64)
    (sl : Fl4Spec.CslotPtr) (c : capability.Cap),
    msg.msg_info st s ct = ok info →
    Fl4Spec.getMessageInfo (Z := Unit) ct.bv σ = ({(mi, σ)}, False) →
    Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σ = ({(buffer, σ)}, False) →
    Fl4Spec.getMrs (Z := Unit) ct.bv buffer mi σ = ({(argsU.map UScalar.bv, σ)}, False) →
    capAt (L.mem s) (cslotAddr sl) = ok c → LookAt ct cptr σ sl c → ¬ VtxInv c info.label argsU

/-- **The syscall's invocation is not a VT-x invocation** [S] (module docstring): `NoVtxAt` for the
invoking syscalls (`InvSys`, the cap register) and the mid syscalls (`MidSysR`, their register). -/
structure KNoVtx (s : S) (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  /-- [S] the invoking syscalls. -/
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    NoVtxAt (L := L) s σ ct (L.mem s (regA ct layout.reg.CAP))
  /-- [S] the mid syscalls. -/
  mid : ∀ ct rg sr cr, sched.cur_thread st s = ok ct → MidSysR n c rg sr cr →
    NoVtxAt (L := L) s σ ct (L.mem s (regA ct rg))

/-- **`KDispHypsKVU36` with `JPathAtMU37`** (no VT-x leaf). -/
structure KDispHypsKVU37 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets)
    (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  /-- [P]/[J] as `KDispHypsKVU36.inv`, without the VT-x leaves. -/
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JEntryAtR7V arI AR Z s a σ ∧
    JPathAtMU37 (L := L) arI AR Z H Cs D s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP))
  /-- [P]/[J] as `KDispHypsKVU36.mid`, without the VT-x leaves. -/
  mid : ∀ ct rg sr cr, sched.cur_thread st s = ok ct → MidSysR n c rg sr cr →
    JEntryAtR7V arI AR Z s a σ ∧
    JPathAtMU37 (L := L) arI AR Z H Cs D s a σ ct false false true true (L.mem s (regA ct rg))

variable {arI}

/-- **Off a VT-x invocation, `JPathMEU37` gives `JPathMEU30`** (the VT-x leaves' hypotheses fail). -/
theorem JPathMEU37.toU30 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} {lbl length : U64} {blk call don fp : Bool} {buf : U64}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data} {argsU : List U64} {ci : Fl4Spec.CapRef}
    {sl : Fl4Spec.CslotPtr} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {buffer : Option Fl4Spec.ObjRef}
    {ct : U64} {c : capability.Cap} (hn : ¬ VtxInv c lbl argsU)
    (h : JPathMEU37 (L := L) arI AR Z H Cs D s ar σ lbl length blk call don fp buf extra slbl argsU ci sl excaps
      buffer ct c) :
    JPathMEU30 (L := L) arI AR Z H Cs D s ar σ lbl length blk call don fp buf extra slbl argsU ci sl excaps
      buffer ct c := by
  cases c
  case Thread p => exact fun hl => absurd hl hn
  case Frame p sz r d m ep asid va => exact fun hl => absurd hl hn
  case Untyped p sb fi dev =>
    have h' : JUtPathU37 Z := h
    have hn' : ¬ ∃ x : U64, argsU.head? = some x ∧ 14 ≤ x.val ∧ x.val < 19 := hn
    exact ⟨fun _ => ⟨h'.fan, fun x hx h1 h2 => (hn' ⟨x, hx, h1, h2⟩).elim, h'.core0, h'.rcb⟩,
      fun _ => ⟨h'.fan, fun x hx h1 h2 => (hn' ⟨x, hx, h1, h2⟩).elim, h'.core0, h'.rcb⟩⟩
  all_goals exact h

/-- **`JPathAtMU37` gives `JPathAtMU35`** at an entry whose invoked cap is not a VT-x invocation. -/
theorem JPathAtMU37.toU35 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S}
    {ar : A} {σ : Fl4Spec.State Unit} {ct : U64} {ic bl cd fp : Bool} {cptr : U64}
    (hN : NoVtxAt (L := L) s σ ct cptr)
    (h : JPathAtMU37 (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr) :
    JPathAtMU35 (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr :=
  fun info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 hL =>
    JPathMEU37.toU30 (hN info mi buffer argsU sl c h1 h2 h4 h7 h9 hL)
      (h info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 hL)

/-- **`KDispHypsKVU37` gives `KDispHypsKVU36`** under `KNoVtx`. -/
theorem KDispHypsKVU37.toU36 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S}
    {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : KDispHypsKVU37 (L := L) arI AR Z H Cs D s a σ n c) (hN : KNoVtx (L := L) s σ n c) :
    KDispHypsKVU36 (L := L) arI AR Z H Cs D s a σ n c :=
  ⟨fun ct call bl don hct hi =>
    ⟨(h.inv ct call bl don hct hi).1, (h.inv ct call bl don hct hi).2.toU35 (hN.inv ct call bl don hct hi)⟩,
   fun ct rg sr cr hct hm =>
    ⟨(h.mid ct rg sr cr hct hm).1, (h.mid ct rg sr cr hct hm).2.toU35 (hN.mid ct rg sr cr hct hm)⟩⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

set_option maxHeartbeats 8000000 in
/-- **`kernel_entry_reachU37`** (module docstring): U36 for non-VT-x invocations (`KNoVtx` [S]), without
the VT-x leaves. -/
theorem kernel_entry_reachU37 [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatK arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU34 (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ SInvX σ ∧ SInvIB.IrqCapBound σ ∧ SInvR.B8w.SInvW σ ∧ SInvIP σ ∧
      SInvIo.IoNoOverlap σ ∧ MR a σ.machineState ∧ FlagsRel Z.T (L.mem s) σ ∧ SInvUZ.UtPgR σ ∧
      (∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c →
        (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
          ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            KNoVtx (L := L) s' σb n c) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            KDispHypsKVU37 (L := L) arI AR (Z.mv Z.G V') H Cs D' s' a' σb n c) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            ∀ ct', sched.cur_thread st s' = ok ct' →
              JDecMRLK (L := L) arI VtxK AR MR (Z.mv Z.G V') H Cs D' s' a' σb ct') →
        (∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
          (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
            JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
            KFinAtR13 (L := L) arI AR Z' H' Cs' s' a' x.2) →
        syscall.handle_syscall st arI s a n ⦃ r =>
          ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
            RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
            SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ SInvUZ.UtPgR σ' ∧ JReachU34 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
        KFinEv13 (L := L) arI AR .interrupt (KFrontI (st := st) arI s a1 w) σ →
        syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∃ σ', EvOut false .interrupt σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU34 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
        KFinEv13 (L := L) arI AR (.userLevelFault n.bv c.bv) (KFrontF2 (st := st) arI (brU (st := st) arI n c) s a) σ →
        syscall.handle_user_exception st arI s a n c ⦃ r => ∃ σ', EvOut false (.userLevelFault n.bv c.bv) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU34 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (ad c : U64) (ft : Fl4Spec.VMFaultType), σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
        KFinEv13 (L := L) arI AR (.vmFaultEvent ft) (KFrontF2 (st := st) arI (brV (st := st) arI ad c) s a) σ →
        syscall.handle_vm_fault st arI s a ad c ⦃ r => ∃ σ', EvOut false (.vmFaultEvent ft) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU34 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (v : U64), σ.curThread ≠ σ.idleThread → v.val < 256 →
        (∀ ev, KEvSpec (.trap v) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontTrap (st := st) arI s a) w.2) →
        syscall.handle_trap_syscall st arI s a v ⦃ r => ∃ ev σ', KEvSpec (.trap v) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU34 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n : I64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
        (∀ ev, KEvSpec (.sysU n) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontSysU (st := st) arI n s a) w.2) →
        syscall.handle_syscall st arI s a n ⦃ r => ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU34 (L := L) arI AR MR r.1 r.2 σ' ⦄)   := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hB, hW, hI, hN, hR, hFl, hPg, hSys, hRest⟩ :=
    kernel_entry_reachU36 arI AR MR hARI hA hnd hM hIp hKD hIo hIoa hPAi hIA hT hmax htu hRef hPI hSX hDR hJ
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, hB, hW, hI, hN, hR, hFl, hPg, ?_, hRest⟩
  intro n c hct hn hfl hNV hK hDL hFin
  exact hSys n c hct hn hfl
    (fun σb hb V' Ac' Lst' D' s' a' hF J' =>
      (hK σb hb V' Ac' Lst' D' s' a' hF J').toU36 (hNV σb hb V' Ac' Lst' D' s' a' hF J')) hDL hFin

end

end

end Fl4Proofs.P3.SInvR.G5
