/-
P3 (DESIGN.md §9), invariant line g5a (KENTRY-PLAN g5a; INV-PLAN §1.3 E4–E10,
§2, §4 G2 / G3): **`kernel_entryJ35E`** = `kernel_entryJ35` whose dispatch
bundle no longer asks five of `JEntryAtR3`'s seven joint fields.

At the dispatch state σb `hK` has `J' : JAtZ … σb` in hand. From it:
* `fnz` (`FrNZ`, no non-device frame cap at 0) is a theorem of `J'`
  (`JAtZ.fnzJ`): every non-device frame cap's bytes are in user frames
  (`JAtZ.fcap`), a user frame at 0 would be a spec arch object at 0, hence an
  object of `H` at 0 (`SpecCover.arch`), and `H 0 = none` (`JKern.h0`).
* `utks` (`UtNodesJ`, the RAM untyped regions miss the 64 cores' nodes) is a
  theorem of `J'` (`JAtZ.utksJ`): `UtKsApart`'s third part (ScPlaceUt) now
  asks the whole static area `[ksb+13568, ksb+304384)` (all 64 nodes and the
  ASID table), so `JAtZ.jcov.ks` gives it. The strengthened part is carried
  exactly as before (`UtKsApart.keep`, the retype's sub-range `omega`).
* `handlers`, `ports`, `urz` are FL4 readings of spec facts: with `StateRel`,
  `MdbLinks`, `IrqRel` / `IoRel` of `J'.xtop` each follows from a spec-only
  invariant (SpecInvG5: `SpecIrqH`, `SpecIoP`, `SpecUtZ`; l4v
  `valid_irq_handlers`, `valid_ioports`, `untyped_ranges_zero`): `JAtZ.handlersJ`,
  `JAtZ.portsJ` (IntInv's `handlersActive_of_spec` / `ioPortsAlloc_of_spec`)
  and `JAtZ.urzJ`. They are asked once, at the entry state σ (`hI : SInvI σ`),
  and carried to σb by `sinvI_disp` (the FaultIP write keeps every cap, the
  time stamp keeps the interrupt states, the IO ports and the memory).
* the Thread path's `hFr` (`JThreadPath`, ReadFPU's destination frame,
  KENTRY-PLAN g4a P1) is a theorem of `J'` (`JAtZ.fpuFrameJ`, from `fcap`
  since g5b; g5a used the spec-only `SpecFrPg`, now unused here):
  the dispatch bundle asks `JPathAtM35E` (`JPathME`: `JPathM` without
  `JThreadPath`), `JPathAtM35E.to35`.
Left in the dispatch bundle (`JEntryAtR5`): `stall`, `ioapics`, `archIrq`
[P] and the two genuinely joint fields `flags` (`FlagsRel`) and `vsTyp`
(`OffTabOK`) [J] (KENTRY-PLAN g5a: why they are not `JExt` fields yet).
-/
import Fl4Proofs.P3.XTopJointKEntry35
import Fl4Proofs.P3.SpecInvG5
import Fl4Proofs.P3.IntInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G5

noncomputable section

/-! ## The five fields from `JAtZ` (and the spec-only bundle) -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **No non-device frame cap at 0** (module docstring; INV-PLAN E16 (a)). -/
theorem JAtZ.fnzJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : FrNZ Z.th (L.mem s) := by
  intro y hy q sz r m e v w hc hq
  subst hq
  have h := J.fcap y hy
  rw [hc] at h
  obtain ⟨sz', hk⟩ := h rfl 0 (by simp) (by positivity)
  have e0 : ∀ m : BitVec 64, BitVec.ofNat 64 0 &&& m = 0 := fun m => by simp
  rw [e0] at hk
  obtain ⟨n, -, hH⟩ := J.cover.arch _ _ hk
  have h0 : H ⟨0⟩ = none := J.kern.h0
  rw [h0] at hH
  cases hH

/-- **`UtNodesJ` from `UtKsApart`** (its first and third parts). -/
theorem utNodesJ_of_ks {G : MdbGhost} (h : UtKsApart (L := L) G Cs s) : UtNodesJ (L.mem s) G (L.ksb s) := by
  intro x hx p sb fi hc
  obtain ⟨k1, -, k3⟩ := h x hx p sb fi hc
  unfold UtNodesAt
  omega

/-- **The RAM untyped regions miss every node** (INV-PLAN E18 (a), module docstring). -/
theorem JAtZ.utksJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : UtNodesJ (L.mem s) Z.G (L.ksb s) :=
  utNodesJ_of_ks J.jcov.ks

/-- **`IoPortsAlloc` from the spec's `SpecIoP`** (INV-PLAN E9). -/
theorem JAtZ.portsJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hS : SpecIoP σ) :
    IoPortsAlloc (L.mem s) (L.ksb s) Z.G :=
  ioPortsAlloc_of_spec J.xtop.rel.2.1.1 J.xtop.rel.2.1.2.2.1 J.xtop.fin.1.1.2.2.2.2.1 fun sl f l hg =>
    hS sl f l (SInvU.getCap_capAt (x := (_, σ)) (by rw [hg]; exact Set.mem_singleton _)).2

/-- **`UtZero` from the spec's `SpecUtZ`** (INV-PLAN E17): an MDB slot's
non-device untyped cap is the spec's `untypedCap false p sb fi` there. -/
theorem JAtZ.urzJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hS : SpecUtZ σ) :
    UtZero (L.mem s) Z.G σ := by
  intro x hx p sb fi hc w h1 h2
  have hR := J.xtop.rel.2.1.1
  have hM := J.xtop.rel.2.1.2.2.1
  obtain ⟨ysl, hys, rfl⟩ := ((hM.members _).1 hx).1.abs
  obtain ⟨c, ac, hc', hca, hg⟩ := hR.abs_cap hys
  rw [capV_of_capAt hc'] at hc; subst hc
  rw [hca.abs] at hg
  have hcap := (SInvU.getCap_capAt (x := (_, σ)) (by rw [hg]; exact Set.mem_singleton _)).2
  exact hS ysl p.bv sb.val fi.val hcap w h1 h2

/-- **ReadFPU's destination frame from `JAtZ`** (INV-PLAN P1, KENTRY-PLAN g4a
P1; g5b): `FpuFrameJHyp` is `JAtZ.fcap` at the slot (every byte of a
non-device frame cap in a spec user frame). -/
theorem JAtZ.fpuFrameJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (x : U64) :
    FpuFrameJHyp (L := L) Z s σ x := by
  intro sl0 hA hx p sz r m ep asid va hc a h1 h2
  subst hx
  have h := J.fcap _ hA.isSlot
  rw [hc] at h
  have hfb : (fbitsF sz).val = frameBitsN sz := by rw [fbitsF_val]; cases sz <;> rfl
  exact h rfl a h1 (by rw [hfb]; exact h2)

end

/-! ## The bundles -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JEntryAtR3` without `fnz`, `utks` (theorems of `JAtZ`) and `handlers`,
`ports`, `urz` (from `SInvI`)** (module docstring). -/
structure JEntryAtR5 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (s : S) (ar : A) (σ : Fl4Spec.State Unit) :
    Prop where
  /-- [P] `JEntryAt.stall` (one core). -/
  stall : ∀ q, smp.remote_tcb_stall st arI s ar q = ok (s, ar)
  /-- [J] joint `JEntryAt.flags` (l4v `tcb_relation`'s flags). -/
  flags : FlagsRel Z.T (L.mem s) σ
  /-- [P] `JEntryAt.ioapics`. -/
  ioapics : ∃ nA, arI.num_ioapics ar = ok nA ∧ nA.bv = σ.archState.x64NumIoapics
  /-- [P] `JEntryAt.archIrq`. -/
  archIrq : ArchIrqRel arI ar σ
  /-- [J] joint `JEntryAt.vsTyp` (l4v `valid_cap` typ_at, `pspace_distinct`). -/
  vsTyp : ∀ y, IsSlot Z.th y → OffTabOK (L := L) Z s σ (capV (L.mem s) y)

variable {arI}

variable (arI)

/-- **`JPathM` without the Thread path's `JThreadPath`** (`hFr`, ReadFPU's
destination frame, from `JAtZ.fpuFrameJ`); every other cap's
premise is `JPathM`'s. -/
def JPathME (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (lbl length : U64)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data)
    (argsU : List U64) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) (ct : U64) : capability.Cap → Prop
  | .Thread p =>
      lbl = fl4_abi.label.TCBSetEPTRoot →
        JVtxScope (L := L) arI AR s ar σ lbl length (.Thread p) blk call don fp buf extra slbl argsU ci sl excaps buffer
          ct
  | c => JPathM (L := L) arI AR Z H Cs D s ar σ lbl length blk call don fp buf extra slbl argsU ci sl excaps buffer ct c

/-- **`JPathAtM35` with `JPathME`.** -/
def JPathAtM35E (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A)
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
      JPathME (L := L) arI AR Z H Cs D s ar σ info.label (msgLen info buf) blocking is_call can_donate first_phase buf e
        mi.miLabel argsU (Fl4Spec.toBl cptr.bv) sl exs buffer ct c

variable {arI}

theorem JPathME.toM {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) {lbl length : U64}
    {blk call don fp : Bool} {buf : U64} {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data}
    {argsU : List U64} {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    {buffer : Option Fl4Spec.ObjRef} {ct : U64} {c : capability.Cap}
    (h : JPathME (L := L) arI AR Z H Cs D s ar σ lbl length blk call don fp buf extra slbl argsU ci sl excaps buffer ct c) :
    JPathM (L := L) arI AR Z H Cs D s ar σ lbl length blk call don fp buf extra slbl argsU ci sl excaps buffer ct c := by
  cases c
  case Thread p => exact ⟨h, fun _ => ⟨fun _ x0 _ => J.fpuFrameJ x0⟩⟩
  all_goals exact h

theorem JPathAtM35E.to35 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) {ct : U64} {ic bl cd fp : Bool} {cptr : U64}
    (h : JPathAtM35E (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr) :
    JPathAtM35 (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr :=
  fun info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 =>
    (h info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13).toM J

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

end

end Fl4Proofs.P3.SInvR.G5
