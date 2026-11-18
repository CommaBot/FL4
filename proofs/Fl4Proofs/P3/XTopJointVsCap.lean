/-
P3 (DESIGN.md §9), VSpace: **the native VSpace caps' decodes from `JAtZ`**
(XTopJointEntry's `JPath`): VsThX's producers at `FinXR` (the spec's decode
and invocation refined, every label: map, unmap, flush, ASID assignment,
the frame's address and accessed-bit replies), their premises from `JAtZ`
at the entry, lifted to `JAt` by XTopJointStep's `XCap.jat` with the
per-op premise `JPostHyp` [W] (`JAtZ` after the VSpace operation; only the
unmapping inside finalisation is proved at `J`, XTopJointFinVs's
`JAtZ.finVsJ`/`finVsJb`).

* `JAtZ.ctTcb`: the current thread a TCB of the typed heap (`CurOK`).
* `JVsExtra` [W]: the front end's first extra cap (VSpace's `vspace.extra`).
* `decode_invocation_{page_table, page_directory, pdpt, pml4, frame, asid_pool}J`:
  `XCap` at `JAt` from `JAtZ`, `ArchRefines` [P], XTopJointFinVs's
  `VsCapsIn` at the entry ([J] `JVsCapsHyp`, l4v `valid_cap`), the labels
  and extra caps [W], and `JPostHyp` [W]. The frame cap also takes VsThX's
  `hno` [J] (a large frame's slots against the other frame caps: l4v
  `valid_cap`/`cap_range` disjointness, as `decode_invocation_frame_thX`);
  the ASID pool its extra cap native ([scope]: guest-root assignment, DESIGN
  §9).
* `decode_invocation_asid_controlJ`: `MakePool`, the RAM untyped caps apart
  from the kernel-state block from `JCovD.ks` (`UtKsOut`); `MpPlacedHyp`
  and the childless untyped's region facts (`JMpExtra`) [J] (l4v
  `valid_untyped`, `descendants_range_in`; VsTopX proves them from the
  dead-free `JCov` only).
* `J{Pt,Pd,Pdpt,Pml4,Pool,Frame,AsidC}Path`: each cap's premises, as
  XTopJointEntry's `JPath` names them.
-/
import Fl4Proofs.P3.VsThX
import Fl4Proofs.P3.XTopJointStep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- The current thread of a `JAtZ` state is a TCB of the typed heap
(`CurOK`). -/
theorem JAtZ.ctTcb {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {ct : U64} (hct : sched.cur_thread st s = ok ct) : σ.curThread = ct.bv ∧ Z.th ct = some .tcb := by
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨t, ht, hth, -⟩ := J.xtop.fin.2.2.2.2
  have e : t = ct := P1.eq_of_bv (ht.trans hcur)
  subst e
  exact ⟨hcur, hth⟩

/-- **The front end's first extra cap of a VSpace decode** [W]. -/
structure JVsExtra (Z : XSets) (s : S) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) : Prop where
  hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
    ∃ x vc vc' xsl rest, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok vc ∧
      CapRel vc vc' ∧ excaps = (vc', xsl) :: rest
  hxs : ∀ x, vspace.extra extra 0#usize = ok (some x) → IsSlot Z.th x

/-- `XCap` at `FinXR` and `JPostHyp` give it at `JAt` (`XCap.jat`). -/
theorem XCap.jatR {Z' : XSets} {s : S} {ar : A} {σ : Fl4Spec.State Unit} {lbl length slot : U64}
    {c : capability.Cap} {blk call don fp : Bool} {buf : U64} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    {slbl : Fl4Spec.Data} {args : List Fl4Spec.Data} {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr}
    {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {buffer : Option Fl4Spec.ObjRef} {ct : U64}
    (h : XCap (L := L) arI (FinXR (L := L) AR Z') s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl
      excaps buffer ct) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hR : JPostHyp (L := L) arI AR s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer ct) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps
      buffer ct :=
  XCap.jat arI (h.imp arI fun _ _ _ hx => xtop_of_finXR hx) J hR

set_option maxHeartbeats 4000000 in
/-- **A page table cap at `JAt`** (`decode_invocation_page_table_thX`). -/
theorem decode_invocation_page_tableJ (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hA : ArchRefines arI AR)
    (hVC : VsCapsIn Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.mem s) Z.G)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlM : lbl = fl4_abi.label.X86PageTableMap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageTableMap)
    (hlU : lbl = fl4_abi.label.X86PageTableUnmap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageTableUnmap)
    (hlO : lbl ≠ fl4_abi.label.X86PageTableMap → lbl ≠ fl4_abi.label.X86PageTableUnmap →
      Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageTableMap ∧
        Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageTableUnmap)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : Z.th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {ptr asid0 va0 : U64} {mp : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.PageTable ptr mp asid0 va0))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hex : JVsExtra (L := L) Z s extra excaps)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hR : JPostHyp (L := L) arI AR s ar σ lbl length (cslotAddr (pc.bv, idx)) (.PageTable ptr mp asid0 va0) blk call
      don fp buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer ct) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length (cslotAddr (pc.bv, idx)) (.PageTable ptr mp asid0 va0)
      blk call don fp buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, htcb⟩ := J.ctTcb arI hct
  obtain ⟨-, hCR, hFI, hDR, hMO, hIA, -⟩ := hX.rel
  exact XCap.jatR arI (decode_invocation_page_table_thX arI Z.th s ar σ Z.G hCR hFI hMO hDR hA hX.fin.1
    hX.fin.2.2.2.1 hX.fin.2.2.2.2 hX.fin.2.1 hX.fin.2.2.1 hVC lbl slbl hlM hlU hlO length buf ct hct hcur htcb
    J.kern.act (J.curRun.run hni) args hlen hargs hpc hidx hcap extra excaps hex.hext blk call don fp ci buffer hex.hxs
    hX.esa hIA.dom) J hR

set_option maxHeartbeats 4000000 in
/-- **A page directory cap at `JAt`** (`decode_invocation_page_directory_thX`). -/
theorem decode_invocation_page_directoryJ (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hA : ArchRefines arI AR)
    (hVC : VsCapsIn Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.mem s) Z.G)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlM : lbl = fl4_abi.label.X86PageDirectoryMap →
      Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageDirectoryMap)
    (hlU : lbl = fl4_abi.label.X86PageDirectoryUnmap →
      Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageDirectoryUnmap)
    (hlO : lbl ≠ fl4_abi.label.X86PageDirectoryMap → lbl ≠ fl4_abi.label.X86PageDirectoryUnmap →
      Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageDirectoryMap ∧
        Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageDirectoryUnmap)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : Z.th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {ptr asid0 va0 : U64} {mp : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.PageDirectory ptr mp asid0 va0))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hex : JVsExtra (L := L) Z s extra excaps)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hR : JPostHyp (L := L) arI AR s ar σ lbl length (cslotAddr (pc.bv, idx)) (.PageDirectory ptr mp asid0 va0) blk
      call don fp buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer ct) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length (cslotAddr (pc.bv, idx))
      (.PageDirectory ptr mp asid0 va0) blk call don fp buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps
      buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, htcb⟩ := J.ctTcb arI hct
  obtain ⟨-, hCR, hFI, hDR, hMO, hIA, -⟩ := hX.rel
  exact XCap.jatR arI (decode_invocation_page_directory_thX arI Z.th s ar σ Z.G hCR hFI hMO hDR hA hX.fin.1
    hX.fin.2.2.2.1 hX.fin.2.2.2.2 hX.fin.2.1 hX.fin.2.2.1 hVC lbl slbl hlM hlU hlO length buf ct hct hcur htcb
    J.kern.act (J.curRun.run hni) args hlen hargs hpc hidx hcap extra excaps hex.hext blk call don fp ci buffer hex.hxs
    hX.esa hIA.dom) J hR

set_option maxHeartbeats 4000000 in
/-- **A PDPT cap at `JAt`** (`decode_invocation_pdpt_thX`). -/
theorem decode_invocation_pdptJ (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hA : ArchRefines arI AR)
    (hVC : VsCapsIn Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.mem s) Z.G)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlM : lbl = fl4_abi.label.X86PDPTMap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PDPTMap)
    (hlU : lbl = fl4_abi.label.X86PDPTUnmap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PDPTUnmap)
    (hlO : lbl ≠ fl4_abi.label.X86PDPTMap → lbl ≠ fl4_abi.label.X86PDPTUnmap →
      Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PDPTMap ∧
        Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PDPTUnmap)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : Z.th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {ptr asid0 va0 : U64} {mp : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Pdpt ptr mp asid0 va0))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hex : JVsExtra (L := L) Z s extra excaps)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hR : JPostHyp (L := L) arI AR s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Pdpt ptr mp asid0 va0) blk call don
      fp buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer ct) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Pdpt ptr mp asid0 va0) blk
      call don fp buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, htcb⟩ := J.ctTcb arI hct
  obtain ⟨-, hCR, hFI, hDR, hMO, hIA, -⟩ := hX.rel
  exact XCap.jatR arI (decode_invocation_pdpt_thX arI Z.th s ar σ Z.G hCR hFI hMO hDR hA hX.fin.1
    hX.fin.2.2.2.1 hX.fin.2.2.2.2 hX.fin.2.1 hX.fin.2.2.1 hVC lbl slbl hlM hlU hlO length buf ct hct hcur htcb
    J.kern.act (J.curRun.run hni) args hlen hargs hpc hidx hcap extra excaps hex.hext blk call don fp ci buffer hex.hxs
    hX.esa hIA.dom) J hR

set_option maxHeartbeats 4000000 in
/-- **A PML4 cap at `JAt`** (`decode_invocation_pml4_thX`; the ASID
invalidation total by `ArchTotal`). -/
theorem decode_invocation_pml4J (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hA : ArchRefines arI AR)
    (hT : P0.ArchTotal arI)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.dataToNat slbl = Fl4Spec.fl4Pml4FlushLabel ↔ lbl = fl4_abi.label.X86PML4Flush)
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (p asid : U64) (mp : Bool) (length slot buf : U64) (blk call don fp : Bool)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (hR : JPostHyp (L := L) arI AR s ar σ lbl length slot (.Pml4 p mp asid) blk call don fp buf extra slbl args ci sl
      excaps buffer ct) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length slot (.Pml4 p mp asid) blk call don fp buf extra slbl
      args ci sl excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, htcb⟩ := J.ctTcb arI hct
  obtain ⟨-, hCR, hFI, hDR, hMO, hIA, -⟩ := hX.rel
  have hinv : ∀ (a : A) (asid : U64), ∃ a', arI.invalidate_asid a asid = ok a' := fun a asid => by
    obtain ⟨r, hr, -⟩ := spec_exists (hT.invalidate_asid a asid)
    exact ⟨r, hr⟩
  exact XCap.jatR arI (decode_invocation_pml4_thX arI Z.th s ar σ Z.G hCR hFI hMO hDR hA hX.fin.1
    hX.fin.2.2.2.1 hX.fin.2.2.2.2 hX.fin.2.1 hX.fin.2.2.1 lbl slbl hlbl ct hct hcur htcb J.kern.act
    (J.curRun.run hni) hinv p asid mp length slot buf blk call don fp extra args ci sl excaps buffer hX.esa hIA.dom) J hR

set_option maxHeartbeats 4000000 in
/-- **An ASID pool cap at `JAt`** (`decode_invocation_asid_pool_thX`). -/
theorem decode_invocation_asid_poolJ (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (hVC : VsCapsIn Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.mem s) Z.G)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlA : lbl = fl4_abi.label.X86ASIDPoolAssign ↔
      Fl4Spec.invocationType slbl = .archInvocationLabel .x64ASIDPoolAssign)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct)
    (ptr base : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hNative : ∀ x, vspace.extra extra 0#usize = ok (some x) →
      ∀ p level mapped asid va, capAt (L.mem s) x ≠ ok (.Ept p level mapped asid va))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ (pc : U64) (r : Nat) (idx : List Bool) (vc : capability.Cap) (vc' : Fl4Spec.Cap)
        (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), Z.th pc = some (.cnode r) ∧ idx.length = r ∧
        vspace.extra extra 0#usize = ok (some (cslotAddr (pc.bv, idx))) ∧
        capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok vc ∧ CapRel vc vc' ∧ excaps = (vc', (pc.bv, idx)) :: rest)
    (slot : U64) (blk call don fp : Bool) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef)
    (hsl : IsSlot Z.th slot) (hcap : capAt (L.mem s) slot = ok (.AsidPool ptr base))
    (hR : JPostHyp (L := L) arI AR s ar σ lbl length slot (.AsidPool ptr base) blk call don fp buf extra slbl args ci
      sl excaps buffer ct) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length slot (.AsidPool ptr base) blk call don fp buf extra slbl
      args ci sl excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, htcb⟩ := J.ctTcb arI hct
  obtain ⟨-, hCR, hFI, hDR, hMO, hIA, -⟩ := hX.rel
  exact XCap.jatR arI (decode_invocation_asid_pool_thX arI Z.th s ar σ Z.G hCR hFI hMO hDR hX.fin.1 hX.fin.2.1
    hX.fin.2.2.1 hX.fin.2.2.2.1 hX.fin.2.2.2.2 hVC lbl slbl hlA length buf ct hct hcur htcb J.kern.act
    (J.curRun.run hni) ptr base extra excaps hNative hext slot blk call don fp args ci sl buffer hsl hcap hX.esa
    hIA.dom) J hR

set_option maxHeartbeats 4000000 in
/-- **A native frame cap at `JAt`** (`decode_invocation_frame_thX`; `hno`
[J] as there). -/
theorem decode_invocation_frameJ [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hA : ArchRefines arI AR)
    (hVC : VsCapsIn Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.mem s) Z.G)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : FrameLabel lbl slbl)
    (hlGA : Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageGetAddress →
      lbl = fl4_abi.label.X86PageGetAddress)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : Z.th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {p : U64} {sz : capability.FrameSize} {rt asid va : U64} {d m : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Frame p sz rt d m false asid va))
    (hno : sz = .Large → d = false → ∀ x ∈ Z.G.chains.flatten,
      Disj (capV (L.mem s) x) (.Frame p sz rt d m false asid va) ∨
      (isFrame (capV (L.mem s) x) = true ∧ revOf (L.mem s) x = false) ∨
      Within (.Frame p sz rt d m false asid va) (capV (L.mem s) x))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hex : JVsExtra (L := L) Z s extra excaps)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hR : JPostHyp (L := L) arI AR s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m false asid va) blk
      call don fp buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer ct) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length (cslotAddr (pc.bv, idx))
      (.Frame p sz rt d m false asid va) blk call don fp buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps
      buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, htcb⟩ := J.ctTcb arI hct
  obtain ⟨-, hCR, hFI, hDR, hMO, hIA, -⟩ := hX.rel
  exact XCap.jatR arI (decode_invocation_frame_thX arI Z.th s ar σ Z.G hCR hFI J.ut hMO hA hX.fin.1
    hX.fin.2.2.2.1 hX.fin.2.2.2.2 hX.fin.2.1 hX.fin.2.2.1 hVC lbl slbl hlbl hlGA length buf ct hct hcur htcb
    J.kern.act (J.curRun.run hni) args hlen hargs hpc hidx hcap (Or.inl trivial) hno extra excaps hex.hext hex.hxs
    blk call don fp ci buffer hDR hX.esa hIA.dom) J hR

/-- **The front end's extra caps of `MakePool`** [W], with the childless
untyped's region facts [J] (`MpRegion`, `RegOKTop`: l4v `valid_untyped`
and `descendants_range_in` for a childless untyped's region; VsTopX's
`regOKTop_childless` derives `RegOKTop` from the dead-free `JCov`). -/
def JMpExtra (Z : XSets) (s : S) (σ : Fl4Spec.State Unit)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) : Prop :=
  (∃ o0 o1, vspace.extra extra 0#usize = ok o0 ∧ vspace.extra extra 1#usize = ok o1 ∧
      (o0 = none ∨ o1 = none) ∧ excaps.length ≤ 1) ∨
    ∃ (pp : U64) (rs : Nat) (idx : List Bool) (y : obj.Slot) (uc : capability.Cap) (uc' : Fl4Spec.Cap)
      (rc : capability.Cap) (rc' : Fl4Spec.Cap) (ysl : Fl4Spec.CslotPtr)
      (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)),
      Z.th pp = some (.cnode rs) ∧ idx.length = rs ∧
      vspace.extra extra 0#usize = ok (some (cslotAddr (pp.bv, idx))) ∧ vspace.extra extra 1#usize = ok (some y) ∧
      capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok uc ∧ CapRel uc uc' ∧
      capAt (L.mem s) y = ok rc ∧ CapRel rc rc' ∧ CapValid Z.th rc ∧
      excaps = (uc', (pp.bv, idx)) :: (rc', ysl) :: rest ∧
      ∀ p fi, uc = .Untyped p fl4_abi.consts.bits.ASID_POOL fi false →
        (¬ ∃ sl, σ.cdt sl = some (pp.bv, idx)) →
        MpRegion Z.th Z.G Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) p ∧
          RegOKTop (L := L) Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ p

set_option maxHeartbeats 4000000 in
/-- **The ASID control cap at `JAt`** (`decode_invocation_asid_control_thX`;
the RAM untyped caps apart from the kernel-state block from `JCovD.ks`).
`hMP` [J]: VsTopX's `MpPlacedHyp` (the new pool's region holds no object of
the typed heap but the retyped untyped's: l4v `valid_untyped`,
`descendants_range_in`; VsTopX's `mpPlacedHyp_of` proves it from the
dead-free `JCov`, not yet from `JCovD`). -/
theorem decode_invocation_asid_controlJ (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (hMP : MpPlacedHyp st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.N Z.T Z.C Z.E Z.R Z.B Z.c AR s σ Z.G)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlM : lbl = fl4_abi.label.X86ASIDControlMakePool ↔
      Fl4Spec.invocationType slbl = .archInvocationLabel .x64ASIDControlMakePool)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : JMpExtra (L := L) Z s σ extra excaps)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef)
    (hR : JPostHyp (L := L) arI AR s ar σ lbl length slot .AsidControl blk call don fp buf extra slbl
      (args.map UScalar.bv) ci sl excaps buffer ct) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length slot .AsidControl blk call don fp buf extra slbl
      (args.map UScalar.bv) ci sl excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, htcb⟩ := J.ctTcb arI hct
  obtain ⟨-, hCR, hFI, hDR, hMO, hIA, -⟩ := hX.rel
  have hUK : UtKsOut (L.ksb s) (L.mem s) Z.G := fun x hx p sb fi h => (J.jcov.ks x hx p sb fi h).1
  exact XCap.jat arI ((decode_invocation_asid_control_thX arI Z.th s ar σ Z.G hCR hFI J.ut hMO hDR hX.fin.1
    hX.fin.2.1 hX.fin.2.2.1 hX.fin.2.2.2.1 hX.fin.2.2.2.2 hMP lbl slbl hlM length buf ct hct hcur htcb J.kern.act
    (J.curRun.run hni) args hlen hargs extra excaps hext hUK slot blk call don fp ci sl buffer hX.esa
    hIA.dom).imp arI fun _ _ _ ⟨_, hx⟩ => xtop_of_finXR hx) J hR

/-! ## The VSpace caps' paths (XTopJointEntry's `JPath`) -/

/-- The page table path: the labels and extra cap [W], `JPostHyp` [W]. -/
structure JPtPath (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl length : U64) (c : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data) (argsU : List U64) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (ct : U64) : Prop where
  hlM : lbl = fl4_abi.label.X86PageTableMap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageTableMap
  hlU : lbl = fl4_abi.label.X86PageTableUnmap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageTableUnmap
  hlO : lbl ≠ fl4_abi.label.X86PageTableMap → lbl ≠ fl4_abi.label.X86PageTableUnmap →
    Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageTableMap ∧
      Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageTableUnmap
  ex : JVsExtra (L := L) Z s extra excaps
  post : JPostHyp (L := L) arI AR s ar σ lbl length (cslotAddr sl) c blk call don fp buf extra slbl
    (argsU.map UScalar.bv) ci sl excaps buffer ct

/-- The page directory path: the labels and extra cap [W], `JPostHyp` [W]. -/
structure JPdPath (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl length : U64) (c : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data) (argsU : List U64) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (ct : U64) : Prop where
  hlM : lbl = fl4_abi.label.X86PageDirectoryMap →
    Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageDirectoryMap
  hlU : lbl = fl4_abi.label.X86PageDirectoryUnmap →
    Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageDirectoryUnmap
  hlO : lbl ≠ fl4_abi.label.X86PageDirectoryMap → lbl ≠ fl4_abi.label.X86PageDirectoryUnmap →
    Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageDirectoryMap ∧
      Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageDirectoryUnmap
  ex : JVsExtra (L := L) Z s extra excaps
  post : JPostHyp (L := L) arI AR s ar σ lbl length (cslotAddr sl) c blk call don fp buf extra slbl
    (argsU.map UScalar.bv) ci sl excaps buffer ct

/-- The PDPT path: the labels and extra cap [W], `JPostHyp` [W]. -/
structure JPdptPath (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl length : U64) (c : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data) (argsU : List U64) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (ct : U64) : Prop where
  hlM : lbl = fl4_abi.label.X86PDPTMap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PDPTMap
  hlU : lbl = fl4_abi.label.X86PDPTUnmap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PDPTUnmap
  hlO : lbl ≠ fl4_abi.label.X86PDPTMap → lbl ≠ fl4_abi.label.X86PDPTUnmap →
    Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PDPTMap ∧
      Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PDPTUnmap
  ex : JVsExtra (L := L) Z s extra excaps
  post : JPostHyp (L := L) arI AR s ar σ lbl length (cslotAddr sl) c blk call don fp buf extra slbl
    (argsU.map UScalar.bv) ci sl excaps buffer ct

/-- The PML4 path: the label [W], `JPostHyp` [W]. -/
structure JPml4Path (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl length : U64) (c : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data) (argsU : List U64) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (ct : U64) : Prop where
  hlbl : Fl4Spec.dataToNat slbl = Fl4Spec.fl4Pml4FlushLabel ↔ lbl = fl4_abi.label.X86PML4Flush
  post : JPostHyp (L := L) arI AR s ar σ lbl length (cslotAddr sl) c blk call don fp buf extra slbl
    (argsU.map UScalar.bv) ci sl excaps buffer ct

/-- The ASID pool path: the label and extra cap [W], the extra cap native
([scope]: guest-root ASID assignment, DESIGN §9), `JPostHyp` [W]. -/
structure JPoolPath (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl length : U64) (c : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data) (argsU : List U64) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (ct : U64) : Prop where
  hlA : lbl = fl4_abi.label.X86ASIDPoolAssign ↔
    Fl4Spec.invocationType slbl = .archInvocationLabel .x64ASIDPoolAssign
  native : ∀ x, vspace.extra extra 0#usize = ok (some x) →
    ∀ p level mapped asid va, capAt (L.mem s) x ≠ ok (.Ept p level mapped asid va)
  hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
    ∃ (pc : U64) (r : Nat) (idx : List Bool) (vc : capability.Cap) (vc' : Fl4Spec.Cap)
      (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), Z.th pc = some (.cnode r) ∧ idx.length = r ∧
      vspace.extra extra 0#usize = ok (some (cslotAddr (pc.bv, idx))) ∧
      capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok vc ∧ CapRel vc vc' ∧ excaps = (vc', (pc.bv, idx)) :: rest
  post : JPostHyp (L := L) arI AR s ar σ lbl length (cslotAddr sl) c blk call don fp buf extra slbl
    (argsU.map UScalar.bv) ci sl excaps buffer ct

/-- The native frame path: the labels and extra cap [W], `hno` [J] (l4v
`valid_cap`: a large frame's range against the other frame caps'),
`JPostHyp` [W]. -/
structure JFramePath (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl length : U64) (p : U64) (sz : capability.FrameSize) (rt : U64) (d m : Bool) (asid va : U64)
    (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data) (argsU : List U64) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (ct : U64) : Prop where
  hlbl : FrameLabel lbl slbl
  hlGA : Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageGetAddress → lbl = fl4_abi.label.X86PageGetAddress
  hno : sz = .Large → d = false → ∀ x ∈ Z.G.chains.flatten,
    Disj (capV (L.mem s) x) (.Frame p sz rt d m false asid va) ∨
    (isFrame (capV (L.mem s) x) = true ∧ revOf (L.mem s) x = false) ∨
    Within (.Frame p sz rt d m false asid va) (capV (L.mem s) x)
  ex : JVsExtra (L := L) Z s extra excaps
  post : JPostHyp (L := L) arI AR s ar σ lbl length (cslotAddr sl) (.Frame p sz rt d m false asid va) blk call don fp
    buf extra slbl (argsU.map UScalar.bv) ci sl excaps buffer ct

/-- The ASID control path: the label [W], the extra caps (`JMpExtra`, [W]
with the region facts [J]), `MpPlacedHyp` [J], `JPostHyp` [W]. -/
structure JAsidCPath (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl length : U64) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data) (argsU : List U64) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (ct : U64) : Prop where
  hlM : lbl = fl4_abi.label.X86ASIDControlMakePool ↔
    Fl4Spec.invocationType slbl = .archInvocationLabel .x64ASIDControlMakePool
  mp : MpPlacedHyp st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.N Z.T Z.C Z.E Z.R Z.B Z.c AR s σ Z.G
  hext : JMpExtra (L := L) Z s σ extra excaps
  post : JPostHyp (L := L) arI AR s ar σ lbl length (cslotAddr sl) .AsidControl blk call don fp buf extra slbl
    (argsU.map UScalar.bv) ci sl excaps buffer ct

end

end

end Fl4Proofs.P3
