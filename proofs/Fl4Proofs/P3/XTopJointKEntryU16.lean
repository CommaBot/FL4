/-
P3 (issue #16, jc1b; KENTRY-PLAN g7b-4 step 1, jc1): **`kernel_entry_reachU16`** =
sd7-2's `kernel_entry_reachU15` without C21 `bufObj` and without the `ArchFitHyp` half
of C16 / C22 / C24 `heapH` (INV-PLAN §1.U3L).

* Both facts are now `JAtZ.carry` (JCarryDefs' `JCarry`): `bufPg` (every IPC-buffer
  word in a non-device data page; `JCarry.bufObj` gives C21's `BufObjHyp`) and
  `archFit` (`ArchFitHyp`). Every `JAtZ` construction re-establishes it: the frame
  steps by `JCarry.frame` / `JCarry.of_ao` / `JCarry.of_keepC` / `JCarry.of_objCn`,
  the retypes by `ArchFitHyp.add` (UtEpSets' `JAtZ.addSetsA`, `newKind_default_le`)
  with `BufPgHyp.grow` at the frame retype (UtEpRet), the detypes by the
  no-straddle fact of `SpecFree` (UtDropJ2 / UtDevDrop `dropA*`: a kept buffer
  word's page has its base off the region), `MakePool` by `JCarry.addP`. The
  start state's `JCarry` is part of its `JAtZ` (no extra start premise).
* `JUtPathMU16` / `JDevPathU16` / `JAsidCPathU16`: `JUtPathM` / `JDevPathU12` /
  `JAsidCPath` without `bufObj` and with only `RegionUnrefAt` of `heapH`
  (`unref`); `JPathMEU16` / `JPathAtMU16` / `KDispHypsKVU16` = U12's with them;
  `.toU12` given `JCarryS Z.B H σ` at the dispatch state (the dispatch's own `JAtZ`,
  whose `H` and `B` the paths read).

Premises removed (relative to U15): C21 `bufObj` [J] (`JUtPathM.bufObj`,
`JDevPath.bufObj`), the `ArchFitHyp` half of C16 (`JAsidCPath.heapH.1`), C22
(`JUtPathM.heapH.1`) and C24 heapH (`JDevPath.heapH.1`). Added: none.
-/
import Fl4Proofs.P3.XTopJointKEntryU15
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JUtPathM` without C21 `bufObj` and C22's `ArchFitHyp`** (both from `JAtZ.carry`). -/
structure JUtPathMU16 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl length p sb fi : U64) (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (slbl : Fl4Spec.Data) (argsU : List U64) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) (ct : U64) : Prop where
  /-- [P] as `JUtPathM.fan`. -/
  fan : Fl4Spec.retypeFanOutLimit = 256#64
  /-- [scope] as `JUtPathM.vtx`. -/
  vtx : ∀ x, argsU.head? = some x → 14 ≤ x.val → x.val < 19 →
    JVtxScope (L := L) arI AR s ar σ lbl length (.Untyped p sb fi false) blk call don fp buf extra slbl argsU ci sl
      excaps buffer ct
  /-- [P] as `JUtPathM.core0`. -/
  core0 : Z.c = 0#u64
  /-- [J] the `RegionUnrefAt` half of `JUtPathM.heapH` (C22). -/
  unref : RegionUnrefAt (L := L) H Cs D s
  /-- [J] as `JUtPathM.vsReach`. -/
  vsReach : (∀ y, ¬ Mdb.Desc Z.G.par y (cslotAddr sl)) → ∀ s1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    Vs.VsReachMiss p.val (p.val + 2 ^ sb.val) (L.mem s1) (L.ksb s1)
        (Vs.NeedR Z.th (L.mem s1) 5) (Vs.NeedR Z.th (L.mem s1) 4) (Vs.NeedR Z.th (L.mem s1) 3)
        (Vs.NeedR Z.th (L.mem s1) 2) (Vs.NeedR Z.th (L.mem s1) 1)
  /-- [P] as `JUtPathM.rcb`. -/
  rcb : Fl4Spec.resetChunkBits = 16

/-- **`JDevPathU12` without `bufObj` and the `ArchFitHyp` half of `heapH`** (C24). -/
structure JDevPathU16 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl length p sb fi : U64) (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (slbl : Fl4Spec.Data) (argsU : List U64) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) (ct : U64) : Prop where
  /-- [P] as `JUtPath.fan`. -/
  fan : Fl4Spec.retypeFanOutLimit = 256#64
  /-- [scope] as `JDevPath.vtx`. -/
  vtx : ∀ x, argsU.head? = some x → 14 ≤ x.val → x.val < 19 →
    JVtxScope (L := L) arI AR s ar σ lbl length (.Untyped p sb fi true) blk call don fp buf extra slbl argsU ci sl
      excaps buffer ct
  /-- [P] as `JUtPath.core0`. -/
  core0 : Z.c = 0#u64
  /-- [J] the `RegionUnrefAt` half of `JDevPath.heapH` (C24 heapH). -/
  unref : RegionUnrefAt (L := L) H Cs D s
  /-- [J] as `JDevPath.devApart` (C25). -/
  devApart : DevApart (L := L) Z.th H Z.G Cs s
  /-- [J] as `JDevPath.devFree` (C26). -/
  devFree : DevFreeT (L.mem s) Z.G σ
  /-- [J] as `JDevPath.vsReach` (C24 vsReach). -/
  vsReach : (∀ y, ¬ Mdb.Desc Z.G.par y (cslotAddr sl)) → ∀ s1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    Vs.VsReachMiss p.val (p.val + 2 ^ sb.val) (L.mem s1) (L.ksb s1)
        (Vs.NeedR Z.th (L.mem s1) 5) (Vs.NeedR Z.th (L.mem s1) 4) (Vs.NeedR Z.th (L.mem s1) 3)
        (Vs.NeedR Z.th (L.mem s1) 2) (Vs.NeedR Z.th (L.mem s1) 1)
  /-- [P] as `JDevPath.rcb`. -/
  rcb : Fl4Spec.resetChunkBits = 16

/-- **`JAsidCPath` without the `ArchFitHyp` half of `heapH`** (C16). -/
structure JAsidCPathU16 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl length : U64) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data) (argsU : List U64) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (ct : U64) : Prop where
  /-- [J] the `RegionUnrefAt` half of `JAsidCPath.heapH` (C16). -/
  unref : RegionUnrefAt (L := L) H Cs D s
  /-- [J] as `JAsidCPath.vsReach`. -/
  vsReach : ∀ (x p fi : U64) (s1 : S), x ∈ Z.G.chains.flatten →
    capV (L.mem s) x = .Untyped p fl4_abi.consts.bits.ASID_POOL fi false → (∀ y, ¬ Mdb.Desc Z.G.par y x) →
    sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    Vs.VsReachMiss p.val (p.val + 2 ^ (fl4_abi.consts.bits.ASID_POOL).val) (L.mem s1) (L.ksb s1)
      (Vs.NeedR Z.th (L.mem s1) 5) (Vs.NeedR Z.th (L.mem s1) 4) (Vs.NeedR Z.th (L.mem s1) 3)
      (Vs.NeedR Z.th (L.mem s1) 2) (Vs.NeedR Z.th (L.mem s1) 1)

/-- **`JPathMEU12` with the U16 Untyped and ASID control paths.** -/
def JPathMEU16 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (lbl length : U64)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data)
    (argsU : List U64) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) (ct : U64) : capability.Cap → Prop
  | .Untyped p sb fi dev =>
      (dev = true → JDevPathU16 (L := L) arI AR Z H Cs D s ar σ lbl length p sb fi blk call don fp buf extra slbl argsU
        ci sl excaps buffer ct) ∧
      (dev = false → JUtPathMU16 (L := L) arI AR Z H Cs D s ar σ lbl length p sb fi blk call don fp buf extra slbl
        argsU ci sl excaps buffer ct)
  | .AsidControl => JAsidCPathU16 (L := L) AR Z H Cs D s ar σ lbl length blk call don fp buf extra slbl argsU ci sl
      excaps buffer ct
  | c => JPathMEU12 (L := L) arI AR Z H Cs D s ar σ lbl length blk call don fp buf extra slbl argsU ci sl excaps
      buffer ct c

/-- **`JPathAtMU12` with `JPathMEU16`.** -/
def JPathAtMU16 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A)
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
      r2 = .Ok e → er = .ok exs → Vs.NativeCap c →
      JPathMEU16 (L := L) arI AR Z H Cs D s ar σ info.label (msgLen info buf) blocking is_call can_donate first_phase buf
        e mi.miLabel argsU (Fl4Spec.toBl cptr.bv) sl exs buffer ct c

/-- **`KDispHypsKVU12` with `JPathAtMU16`.** -/
structure KDispHypsKVU16 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets)
    (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JEntryAtR6 (L := L) arI AR Z s a σ ∧
    JPathAtMU16 (L := L) arI AR Z H Cs D s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP))
  mid : ∀ ct rg sr cr, sched.cur_thread st s = ok ct → MidSysR n c rg sr cr →
    JEntryAtR6 (L := L) arI AR Z s a σ ∧
    JPathAtMU16 (L := L) arI AR Z H Cs D s a σ ct false false true true (L.mem s (regA ct rg))

variable {arI}

theorem JUtPathMU16.toM {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} {lbl length p sb fi : U64} {blk call don fp : Bool} {buf : U64}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data} {argsU : List U64} {ci : Fl4Spec.CapRef}
    {sl : Fl4Spec.CslotPtr} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {buffer : Option Fl4Spec.ObjRef} {ct : U64}
    (h : JUtPathMU16 (L := L) arI AR Z H Cs D s ar σ lbl length p sb fi blk call don fp buf extra slbl argsU ci sl excaps buffer ct) (hC : JCarryS Z.B H σ) :
    JUtPathM (L := L) arI AR Z H Cs D s ar σ lbl length p sb fi blk call don fp buf extra slbl argsU ci sl excaps buffer ct :=
  ⟨h.fan, h.vtx, h.core0, hC.bufObj, ⟨hC.archFit, h.unref⟩, h.vsReach, h.rcb⟩

theorem JAsidCPathU16.toA {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} {lbl length : U64} {blk call don fp : Bool} {buf : U64}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data} {argsU : List U64} {ci : Fl4Spec.CapRef}
    {sl : Fl4Spec.CslotPtr} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {buffer : Option Fl4Spec.ObjRef} {ct : U64}
    (h : JAsidCPathU16 (L := L) AR Z H Cs D s ar σ lbl length blk call don fp buf extra slbl argsU ci sl excaps buffer ct) (hC : JCarryS Z.B H σ) :
    JAsidCPath (L := L) AR Z H Cs D s ar σ lbl length blk call don fp buf extra slbl argsU ci sl excaps buffer ct :=
  ⟨⟨hC.archFit, h.unref⟩, h.vsReach⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

end

end

end Fl4Proofs.P3.SInvR.G5
