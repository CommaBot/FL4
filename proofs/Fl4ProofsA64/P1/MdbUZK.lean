/-
P1 (aarch64, gen 61): **the node-word case hypotheses from `KsOffA`** (goal 3 of gen 61) — MdbUZD's state fact
`KsOffA` (every RAM untyped region off the kernel state block and the nodes) with the scheduler invariant's node
placement (`SchedQueuesInvX.nodes` / `.cur`, P1 `NodePlaced`) discharges:

* gen 60's **`hnS`** (`NodeOffA` of the current core's `SCHED_ACTION` word) at the CNode decode tops:
  **`cnode.decode.cnode_stAK`** / **`syscall.decode_invocation.cnode_stAK`** (`StA H` before ⇒ after, `KsOffA`
  for `hnS`);
* gen 59's **`hnA`** (node 0's `DEBUG_TCBS` word aligned: `nodeAt_aligned`) and **`hnF`** (off every RAM free part:
  `KsOffA.node`) at the retype top: **`untyped.retype.mdbSTVUZK`**.

Not derivable from the carried facts (stated for the next step): gen 59's **`hnC`** (node 0's head word is no cap-slot
word: `NodePlaced.disj` keeps it off the TCBs' low words, but off `H.omega` — reply / SC / other objects — needs the
nodes off every heap object, a placement fact nothing carries; source reason: the nodes are kernel statics outside
all untyped memory, so no retyped object meets them — the same boot fact as `KsOffA`, over `H` instead of the
untypeds) and **`hhd0`** (node 0's head null or a heap TCB: P1 `DbgTz.dh` / the debug-list well-formedness, carried
by `JV` at the deletion but not by the retype's bundle).

No named premise.
-/
import Fl4ProofsA64.P1.MdbZF
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts Fl4Proofs.P3

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {Sg : Set U64}
variable {H : Heap} {Cs Rp Nt : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

variable {OS : Set U64}

/-- `SCHED_ACTION`'s offset. -/
theorem sched_action_val : layout.node.SCHED_ACTION.val = 16 := by simp [layout.node.SCHED_ACTION]

/-- **`hnS` from `KsOffA`** (module docstring). -/
theorem KsOffA.hnS {Cs X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (hK : KsOffA st Cs OS s) (q : SchedQueuesInvX st H.tcbs Cs H.omega H X s Q Rq) :
    NodeOffA st OS s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) :=
  KsOffA.node hK q.cur (q.nodes _ q.cur) (by rw [sched_action_val]; omega)

/-- **`cnode.decode.cnode_stA` with `KsOffA` for `hnS`** (module docstring). -/
theorem cnode.decode.cnode_stAK {A : Type _} {ar : machine.Arch A} (hH : HeapOK H)
    (hO : OSOK H.tcbs H.omega Sg OS) (hW : WinOK H.tcbs H.omega)
    {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st H.tcbs Cs H.omega H X s Q Rq) (hT : SlotTy st H.tcbs H.omega Sg H Rp Nt OS s)
    (hSt : StA st H OS s) (hK : KsOffA st Cs OS s)
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) {lbl len buf : U64}
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate ∨ lbl = fl4_abi.label.CNodeRotate)
    (c : capability.Cap) (hc : RootOK OS c) (hh : Held st OS s c) (hx : ∀ x ∈ extra.val, x ≠ 0#u64 → x ∈ OS) :
    cnode.decode st ar s a lbl len c buf extra ⦃ r s' _ => StA st H OS s' ⦄ :=
  cnode.decode.cnode_stA hH hO hW q hT hSt (KsOffA.hnS hK q) a hl c hc hh hx

/-- **`syscall.decode_invocation.cnode_stA` with `KsOffA` for `hnS`** (module docstring). -/
theorem syscall.decode_invocation.cnode_stAK {A : Type _} {ar : machine.Arch A} (hH : HeapOK H)
    (hO : OSOK H.tcbs H.omega Sg OS) (hW : WinOK H.tcbs H.omega)
    {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st H.tcbs Cs H.omega H X s Q Rq) (hT : SlotTy st H.tcbs H.omega Sg H Rp Nt OS s)
    (hSt : StA st H OS s) (hK : KsOffA st Cs OS s)
    (a : A) {lbl : U64} (len : U64) (slot : obj.Slot) (cap : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate ∨ lbl = fl4_abi.label.CNodeRotate)
    (hf : capFam cap = .cnode) (hslot : slot ∈ OS) (hcap : obj.Slot.cap st slot s = ok cap)
    (hx : ∀ x ∈ extra.val, x ≠ 0#u64 → x ∈ OS) :
    syscall.decode_invocation st ar s a lbl len slot cap blk call don fp buf extra ⦃ r s' _ => StA st H OS s' ⦄ :=
  syscall.decode_invocation.cnode_stA hH hO hW q hT hSt (KsOffA.hnS hK q) a len slot cap blk call don fp buf extra hl hf
    hslot hcap hx

section arch
variable {A : Type _} {ar : machine.Arch A}

/-- **`untyped.retype.mdbSTVUZ` with `KsOffA` and node 0's placement for `hnA` / `hnF`** (module docstring). -/
theorem untyped.retype.mdbSTVUZK {Sg : Set U64} (hA : P0.ArchTotal ar) (hH : HeapOK H)
    (hO : OSOK H.tcbs H.omega Sg OS) {s : S} {H' : Heap} (hS : MdbST st OS s) (hR : UtRev st OS s)
    (hV : ValidUntypedA st H OS s) (hUZ : UtZeroA st OS s) (a : A)
    {src p sb fi : U64} {dev : Bool} (hsrc : src ∈ OS) (hcs : capA st s src = .Untyped p sb fi dev)
    (nt us dcn off len base : U64) (device : Bool) (hdv : device = dev) (hn : nt.val < 15)
    (hz : (zA nt.val us).val < 64) (hdev : dev = true → nt.val ≠ 1 ∧ nt.val ≠ 12 ∧ nt.val ≠ 14)
    (hal : base.val % 8 = 0)
    (hfi : fi.val < 2 ^ sb.val) (hA0 : p.val + fi.val ≤ base.val)
    (hAw : base.val + len.val * 2 ^ (zA nt.val us).val ≤ p.val + 2 ^ sb.val)
    (hH' : ∀ q k, H' q = some k → H q = some k ∨
      (nt.val ≠ 0 ∧ base.val ≤ q.val ∧ q.val + 2 ^ k.bits ≤ base.val + len.val * 2 ^ (zA nt.val us).val))
    {Cs : Set U64} (hK : KsOffA st Cs OS s) (h0 : 0#u64 ∈ Cs) (hN0 : NodePlaced st H.tcbs s 0#u64)
    (hnC : ¬ W7.CapW H.tcbs H.omega Sg (nwA st s))
    (hhd0 : L.mem s (nwA st s) = 0#u64 ∨ H (L.mem s (nwA st s)) = some .tcb)
    (hdO : ∀ j, j < len.val → djA dcn off j ∈ OS)
    (hdn : ∀ j, j < len.val → capA st s (djA dcn off j) = .Null)
    (hdc : ∀ j, j < len.val → obj.sext48 (djA dcn off j) = ok (djA dcn off j))
    (hinj : ∀ j l, j < len.val → l < len.val → djA dcn off j = djA dcn off l → j = l)
    (hcan : ∀ j, j < len.val → CapRt.Canonical (bjA base (zA nt.val us) j)) (hus : us.val < 64) :
    untyped.retype st ar s a src false base nt us dcn off len device ⦃ r => r.1 = .Ok () ∧
      MdbST st OS r.2.1 ∧ UtRev st OS r.2.1 ∧ ValidUntypedA st H' OS r.2.1 ∧ UtZeroA st OS r.2.1 ⦄ :=
  untyped.retype.mdbSTVUZ hA hH hO hS hR hV hUZ a hsrc hcs nt us dcn off len base device hdv hn hz hdev hal hfi hA0
    hAw hH' (nodeAt_aligned hN0 (by rw [debug_val]; omega) (by rw [debug_val])) hnC
    (KsOffA.node hK h0 hN0 (by rw [debug_val]; omega)) hhd0 hdO hdn hdc hinj hcan hus

end arch

end ST
end R
end W7

end

end Fl4ProofsA64.P1
