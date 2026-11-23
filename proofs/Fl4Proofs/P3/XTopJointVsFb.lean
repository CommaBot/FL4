/-
P3 (issue #16, FL4 #71), VSpace: **a PML4 cap's decode at `JAt` with
`X86PML4FrameBatch`** (KENTRY-PLAN fb3j).

* `decode_invocation_pml4_fbJV`: the batch label. FL4's
  `vspace::decode_frame_batch` replies in the decode (the reply class,
  `XCap`'s right disjunct, as a frame cap's GetAddress): the decode's
  checks against `decodeFrameBatch`, the loop entry by entry against
  `fbEntry` (from the spec's state *before* its `Restart`, transferred by
  SpecFbRestart's `performFrameBatch_restart`), the deferred
  `invalidate_asid` against `flushAll`, the reply and `TS_RUNNING` by
  VsFbReply's `fbTail_inv`, and `JAt` after (proved, `JPath`'s PML4 arm
  stays `True`). OPEN (the one FrameBatch site left on the P3 chain;
  scratch stub `proofs/scratch/fb3scratch.py`).
* `decode_invocation_pml4JV`: every label: the batch above, any other by
  XTopJointVsMap's `decode_invocation_pml4JVn`. The callers
  (XTopJointEntry, XTopJointKEntry13P, XTopJointKEntry23P) pass the
  message (`args`, `hlen`, `hargs`), the extra caps (`ExtraOK`,
  `ExtraNamed`) and the invoked slot (`AbsSlot`, its cap), as their other
  VSpace caps.
-/
import Fl4Proofs.P3.XTopJointVsMap
import Fl4Proofs.P3.JEntryIrq
import Fl4Proofs.P3.VsFbDec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 8000000 in
/-- **The FrameBatch label on a PML4 cap at `JAt`** (module docstring). OPEN: the decode walk is in
proofs/scratch/fb3j_dec_wip.lean (KENTRY-PLAN fb3j). -/
theorem decode_invocation_pml4_fbJV (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hA : ArchRefines arI AR)
    (hT : P0.ArchTotal arI)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlb : lbl = fl4_abi.label.X86PML4FrameBatch)
    (hslb : Fl4Spec.dataToNat slbl = Fl4Spec.fl4FrameBatchLabel)
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (p asid : U64) (mp : Bool) (h0 : mp = true → asid ≠ 0#u64) (length buf : U64) (blk call don fp : Bool)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl) (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Pml4 p mp asid))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hXO : ExtraOK Z.th (L.mem s) extra excaps) (hXN : ExtraNamed Z.th (L.mem s) extra)
    (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length (cslotAddr sl) (.Pml4 p mp asid) blk call don fp buf
      extra slbl (args.map UScalar.bv) ci sl excaps buffer ct := by
  fail "FB3 OPEN: the FrameBatch refinement (KENTRY-PLAN fb3j)"

set_option maxHeartbeats 4000000 in
/-- **A PML4 cap at `JAt`**, every label (module docstring). -/
theorem decode_invocation_pml4JV (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hA : ArchRefines arI AR)
    (hT : P0.ArchTotal arI)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.dataToNat slbl = Fl4Spec.fl4Pml4FlushLabel ↔ lbl = fl4_abi.label.X86PML4Flush)
    (hlfb : Fl4Spec.dataToNat slbl = Fl4Spec.fl4FrameBatchLabel ↔ lbl = fl4_abi.label.X86PML4FrameBatch)
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (p asid : U64) (mp : Bool) (h0 : mp = true → asid ≠ 0#u64) (length buf : U64) (blk call don fp : Bool)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl) (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Pml4 p mp asid))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hXO : ExtraOK Z.th (L.mem s) extra excaps) (hXN : ExtraNamed Z.th (L.mem s) extra)
    (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length (cslotAddr sl) (.Pml4 p mp asid) blk call don fp buf
      extra slbl (args.map UScalar.bv) ci sl excaps buffer ct := by
  by_cases hb : lbl = fl4_abi.label.X86PML4FrameBatch
  · exact decode_invocation_pml4_fbJV arI s ar σ J hni hA hT lbl slbl hb (hlfb.2 hb) ct hct p asid mp h0 length buf
      blk call don fp args hlen hargs sl hAs hc extra excaps hXO hXN ci buffer
  · exact decode_invocation_pml4JVn (st := st) (L := L) arI s ar σ J hni hA hT lbl slbl hlbl ⟨fun h => hb (hlfb.1 h), hb⟩ ct hct p asid
      mp h0 length _ buf blk call don fp extra _ ci sl excaps buffer

end

end

end Fl4Proofs.P3
