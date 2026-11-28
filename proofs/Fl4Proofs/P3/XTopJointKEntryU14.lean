/-
P3 (issue #16, s26): **`kernel_entry_reachU14`** = g7a-3's `kernel_entry_reachU11`
without C26 (INV-PLAN §1.U3L: the device Untyped path's `JDevPath.devFree`,
UtDevRet's `DevFreeT`, l4v `valid_untyped` for device untyped caps).

* The spec invariant `SInvDV.DevRangeS` (SpecInvDvW: every spec object misses
  the region of every device untyped cap or lies in its used part) is carried
  alongside `JReachU3`: `JReachU14 s a σ := JReachU3 s a σ ∧ DevRangeS σ`.
  Each clause of the top ends in `JReachU14` at its exit: `JReachU3` from
  U11's exit, `DevRangeS σ'` from the whole-entry preservation lemmas of
  SpecInvDvP (`kentry_devRange` for the syscall entry, `kcall_devRange` for
  the events, `fip_kcall_devRange` after the FaultIP write), as
  `kentry_sinvX` / `kentry_zr` do; they need only `UtInv3` (`SInvX`).
* `JDevPathU14` is `JDevPath` without `devFree`; `JPathMEU14`, `JPathAtMU14`,
  `KDispHypsKVU14` carry it. `KDispHypsKVU14.toU7` gives U11's bundle at a
  dispatch state from `DevRangeS` there (`budget_devRange` across the FaultIP
  write and the budget check, `BudgetAt`) through the bridge `devFreeT_of`:
  a chain slot is a typed-heap slot (`DState`'s `members`), whose FL4 cap is
  the spec's `absCap` of it (`J.dstate.1.1.abs_cap`), so `DevFreeT`'s free
  part reads the same base, size and free index.

Premise removed (relative to U11): C26 `devFree` [J]. Added: `DevRangeS σ` at
the start state, in `JReachU14` (one state, [S] start, as the rest of
`JReachU3`'s start bundle: true at boot, no spec object in a device range).
-/
import Fl4Proofs.P3.XTopJointKEntryU11
import Fl4Proofs.P3.SpecInvDvP
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The bridge** (module docstring): `DevFreeT` from the spec's `DevRangeS` at a `JAtZ` state. -/
theorem devFreeT_of {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hD : SInvDV.DevRangeS σ) : DevFreeT (L.mem s) Z.G σ := by
  intro x hx p sb fi d hc hP o ko ho
  obtain ⟨hd, -⟩ := hP
  subst hd
  obtain ⟨sl0, hA0, rfl⟩ := ((J.dstate.1.2.2.1.members x).1 hx).1.abs
  obtain ⟨c0, ac0, hc0, hca0, hg0⟩ := J.dstate.1.1.abs_cap hA0
  rw [capAt_capV, hc] at hc0; cases eq_of_ok_eq hc0
  rw [hca0.abs] at hg0
  have ha0 := (getCap_set_iff σ sl0.1 sl0.2 _).1 (congrArg Prod.fst hg0)
  have h := hD sl0.1 sl0.2 p.bv sb.val fi.val ha0 o ko ho
  unfold SInvDV.InUsed at h
  simp only [UScalar.bv_toNat] at h
  omega

/-- `JDevPath` without `devFree` (C26). -/
structure JDevPathU14 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl length p sb fi : U64) (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (slbl : Fl4Spec.Data) (argsU : List U64) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) (ct : U64) : Prop where
  /-- [P] `CONFIG_RETYPE_FAN_OUT_LIMIT` is FL4's 256 (as `JUtPath.fan`). -/
  fan : Fl4Spec.retypeFanOutLimit = 256#64
  /-- [scope] a VT-x object type (14 to 18), as `JUtPath.vtx` (the decode of a
  device cap refuses these types on both sides; `decode_invocation_untypedJ`
  takes the native types only). -/
  vtx : ∀ x, argsU.head? = some x → 14 ≤ x.val → x.val < 19 →
    JVtxScope (L := L) arI AR s ar σ lbl length (.Untyped p sb fi true) blk call don fp buf extra slbl argsU ci sl
      excaps buffer ct
  /-- [P] one core (as `JUtPath.core0`). -/
  core0 : Z.c = 0#u64
  /-- [J] as `JUtPath.bufObj`. -/
  bufObj : BufObjHyp Z.B σ
  /-- [J] as `JUtPath.heapH`. -/
  heapH : ArchFitHyp H σ ∧ RegionUnrefAt (L := L) H Cs D s
  /-- [J] DevJ's `DevApart` at the entry's sets and heap (l4v `valid_untyped` /
  `pspace_no_overlap` for device caps with `valid_global_refs` /
  `kernel_window`: no device untyped range covers a kernel object, a typed-heap
  object or a RAM object, `H`'s objects meeting it lie below its free index, and
  its range lies in one canonical half with a nonzero base, of size bits at
  least 4, l4v `untyped_min_bits`): true from boot by
  the boot checks (e408a625: no device untyped over the kernel image's names;
  9ab17db1: none at the pointer 0; RAM and device physical ranges are
  disjoint; physical memory below `2^47`; boot.rs gives out blocks of at
  least `MIN_UNTYPED` = 4 size bits), kept by retype
  (UtDevRet's `DevApart.retype`: a device child is a sub-range, a new device
  frame lies below the source's new free index). -/
  devApart : DevApart (L := L) Z.th H Z.G Cs s
  /-- [J] UtDevDrop's `DevGpm` (l4v `valid_global_refs`: no untyped range
  covers a global kernel object): the spec's global PML4 lies off every
  device untyped cap's range; true from boot (the global PML4 is a static of
  the kernel image, fl4-kernel paging.rs, and the boot check e408a625 skips
  device memory over the image), kept (`x64GlobalPml4` never changes, a
  device child is a sub-range). For the reset of a used device cap
  (UtDevReset's `JAtZ.utDevResetJ`, UtDevDrop's `JAtZ.dropAD`). -/
  devGpm : DevGpm (L.mem s) Z.G σ
  /-- [J] the reset's `VsReachMiss` at the restart's state, as
  `JUtPath.vsReach`, for the device cap's region (UtDevDrop's `JAtZ.dropAD`
  in UtDevReset's `JAtZ.reset_untypedDJ`). Asked only when the cap has no
  descendants (FINDING g7b-2: unguarded it is false). -/
  vsReach : (∀ y, ¬ Mdb.Desc Z.G.par y (cslotAddr sl)) → ∀ s1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    Vs.VsReachMiss p.val (p.val + 2 ^ sb.val) (L.mem s1) (L.ksb s1)
        (Vs.NeedR Z.th (L.mem s1) 5) (Vs.NeedR Z.th (L.mem s1) 4) (Vs.NeedR Z.th (L.mem s1) 3)
        (Vs.NeedR Z.th (L.mem s1) 2) (Vs.NeedR Z.th (L.mem s1) 1)
  /-- [P] `CONFIG_RESET_CHUNK_BITS` is FL4's 16, as `JUtPath.rcb` (the spec's
  device reset, UtDevDrop's `reset_devX`). -/
  rcb : Fl4Spec.resetChunkBits = 16

variable {arI}

end

/-- `DevRangeS` at a budget outcome (the FaultIP write, then the budget check). -/
theorem BudgetAt.devRange {σ σb : Fl4Spec.State Unit} (hD : SInvDV.DevRangeS σ) (h : BudgetAt σ σb true) :
    SInvDV.DevRangeS σb := by
  obtain ⟨σ0, h0, hb⟩ := h
  exact SInvDV.budget_devRange (SInvDV.faultIP_devRange _ hD _ h0) _ hb

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

end

end

end Fl4Proofs.P3.SInvR.G5
