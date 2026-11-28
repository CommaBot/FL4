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
`JPathAtMU30` with a VT-x leaf (`JVtxScope`, inventory K6 / K7 / K3); they contain every `VirtRoute` input
of a native cap (`vtxInv_of_virtRoute`, P3JVtxBridge) and also the VT-x inputs on which ext and port agree
but FL4's VT-x path has no functional refinement (first-phase label 88, unmapped EPT-flagged frames, VT-x
retypes with VT-x present: still [scope]).
* `KNoVtx s σ n c` [S] (new antecedent of the syscall clause, at the dispatch states like `KDispHyps`): for
  the invocation (`inv`) and mid (`mid`) syscalls, the slot / cap the lookup returns (`LookAt`) with the
  current message is not a `VtxInv`.
* `JPathMEU37`: `JPathMEU30` with no VT-x leaf (thread and frame caps: `True`; untyped caps: `JUtPathU37`
  = `fan`, `core0`, `rcb`, without `vtx`). `JPathMEU37.toU30`: under `¬ VtxInv` it gives `JPathMEU30`.
* `JPathAtMU37`, `KDispHypsKVU37`: `JPathAtMU30` / `KDispHypsKVU36` on `JPathMEU37`; `KDispHypsKVU37.toU36`.

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

/-- **`JPathAtMU30` on `JPathMEU37`.** -/
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

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

end

end

end Fl4Proofs.P3.SInvR.G5
