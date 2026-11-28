/-
P3 (line mmuAD, gen 42b13): **the EPT table unmap of a final cap at decode level, from `VmEptState`** — FL4's
`ept::decode` at the unmap label (crates/fl4-core/src/ept.rs l. 265-283: `is_final_capability(dest)`, the caller's
restart, when mapped `ept::unmap(asid, gpa, ptr, level, true)` then `s.zero(ptr, 4096)`, then `set_cap` of the
unmapped cap) against the extended spec's `decodeEptInvocation` (Fl4Spec/Ext/VirtEptInv l. 154-159: `isFinalCap`,
then `.tableUnmap ptr level mapped slot`) and the perform's `guestUnmap` (l. 227-232).

* Spec: **`zv_eD_unmapF`** (a final cap: the single outcome `.tableUnmap`).
* FL4: **`zv_eptF_unmapF0`** (an unmapped final cap: restart, `set_cap`), **`EptCore.unmapF1`** (a mapped final cap:
  restart, then P3/EptUnmapRel's `EptCore.unmapRel` at the restart state, the zeroing, `set_cap`).
* **`VmEptState.tableUnmapDec`** — the top: from `VmEptState` at an `Entered` spec state, the invoked
  `Ept ptr level m asid va` cap (`level ≠ 0`) in a CNode slot, the unmap label and FL4's finality of the slot
  (`finF … = true`; the non-final arm is P3/JAtZV3EptE's `zv_eptF_unmapNF`): the restart states `s1`, `σ1` with
  `VmEptState` there (P3/EptSetRoot's `VmEptState.restart`), the spec decoder's single outcome `.tableUnmap ptr level
  mapped slot` (finality by P3/VsDecFrame's `fin_iff_of`), and FL4's `ept.decode` ⦃ `Ok ()`, the arch relation kept,
  and FL4's state after is `set_cap dest (Ept ptr level false 0 0)` of `s1` (unmapped) or of `zero(s3, ptr, 4096)`
  with `UnmapOut … s1 … s3 (guestUnmap … σ1)` (mapped: the walk path of `asid` / `va` at the restart state, the guest
  address below `2^47` by `JExtEpt.vtop`, the level 39 / 30 / 21 by `EptCore.capTbl`) ⦄.

Not here: the perform half (`VmEptState` after the unmap, the zeroing and `setCap`: the unmapped table's unique path
by `EptNamed` + finality + `RngOne`, per the Architect's sketch) and its syscall-level top.

Premise: `ArchRefines arI AR` [P] (as P3/EptUnmapRel). No new named premise. New file; root import after
`P3.EptUnmapRel`. No existing statement changed.
-/
import Fl4Proofs.P3.EptUnmapRel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
open Fl4Spec

/-- **The spec's table unmap of a final cap** (module docstring). -/
theorem zv_eD_unmapF {label : Data} (args : List Data) (slot : CslotPtr) (p : ObjRef) {l : Nat}
    (mp : Option (Asid × VSpaceRef)) (ec : List (Cap × CslotPtr)) (hl : l ≠ 0)
    (h1 : dataToNat label = (eptTableLabels l).2) (σ : State Unit)
    (hf : isFinalCap' (.archObjectCap (.eptCap p l mp)) σ) :
    ExceptT.run (decodeEptInvocation (Z := Unit) label args slot (.eptCap p l mp) ec) σ =
      ({(.ok (.tableUnmap p l mp slot), σ)}, False) := by
  unfold decodeEptInvocation
  dsimp only
  rw [if_neg hl]
  generalize eptTableLabels l = q at h1 ⊢
  obtain ⟨mL, uL⟩ := q
  dsimp only at h1 ⊢
  rw [if_pos h1]
  have hF : (isFinalCap (Z := Unit) (.archObjectCap (.eptCap p l mp))) σ = ({(true, σ)}, False) := by
    show ({(decide (isFinalCap' (Z := Unit) (.archObjectCap (.eptCap p l mp)) σ), σ)}, False) = _
    rw [decide_eq_true hf]
  rw [run_bind_ok (run_liftE hF)]
  simp only [NonDetE.unlessE, eq_self_iff_true, if_true, ndE_pure_bind]
  rfl

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
  {AR : A → Fl4Spec.Cr3 → Prop}

/-- FL4's table unmap of an unmapped final cap (module docstring). -/
theorem zv_eptF_unmapF0 (s : S) (a : A) {lbl len ptr level asid va : U64} (dest buf : U64)
    (ex : Array obj.Slot 3#usize) (h0 : level ≠ 0#u64)
    (hu : lbl.val = (Fl4Spec.eptTableLabels level.val).2) (hf : finF (L.mem s) dest = true) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) {s1 : S} (hs1 : sched.set_thread_state st s ct sched.TS_RESTART = ok s1) :
    ept.decode st arI s a lbl len (.Ept ptr level false asid va) dest buf ex =
      ok (.Ok (), wrCap (L := L) s1 dest (.Ept ptr level false 0#u64 0#u64), a) := by
  have hu' : lbl = (eptLbl level).2 := zv_lblEq (zv_eptLbl_val level).2 hu
  unfold ept.decode
  dsimp only
  rw [if_pos (show (level != 0#u64) = true by simpa using h0), zv_eptLblIf, bind_ok]
  generalize eptLbl level = q at hu' ⊢
  obtain ⟨mL, uL⟩ := q
  dsimp only at hu'
  simp only [uncurry_apply_pair]
  rw [hct, bind_ok, if_pos hu', is_final_eq, bind_ok, hf]
  simp only [↓reduceIte, hs1, bind_ok, Bool.false_eq_true, set_cap_eq]
  rfl

variable {X : Set U64} {XL : U64 → Nat} {th : TypedHeap}

set_option maxHeartbeats 4000000 in
/-- FL4's table unmap of a mapped final cap, with `ept::unmap` at the restart state (module docstring). -/
theorem EptCore.unmapF1 {s s1 : S} {σ1 : Fl4Spec.State Unit} (C1 : EptCore (L := L) X XL th s1 σ1) {P : Set U64}
    (hR1 : VsRel P (L.mem s1) (L.ksb s1) σ1) (hA : ArchRefines arI AR) (a : A) {c : Fl4Spec.Cr3} (hAR : AR a c)
    {lbl len ptr level asid va : U64} (dest buf : U64) (ex : Array obj.Slot 3#usize) (h0 : level ≠ 0#u64)
    (hlv : level.val = 39 ∨ level.val = 30 ∨ level.val = 21) (hva : va.val < 2 ^ 47)
    (hu : lbl.val = (Fl4Spec.eptTableLabels level.val).2) (hf : finF (L.mem s) dest = true) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) (hs1 : sched.set_thread_state st s ct sched.TS_RESTART = ok s1) :
    ept.decode st arI s a lbl len (.Ept ptr level true asid va) dest buf ex ⦃ res =>
      res.1 = .Ok () ∧ AR res.2.2 c ∧ ∃ s3 : S,
        UnmapOut (L := L) X XL σ1 s1 asid va ptr level true s3
          (Fl4Spec.guestUnmap (Z := Unit) asid.bv va.bv ptr.bv level.val true σ1) ∧
        res.2.1 = wrCap (L := L) (L.zr s3 ptr 4096#u64) dest (.Ept ptr level false 0#u64 0#u64) ⦄ := by
  have hu' : lbl = (eptLbl level).2 := zv_lblEq (zv_eptLbl_val level).2 hu
  unfold ept.decode
  dsimp only
  rw [if_pos (show (level != 0#u64) = true by simpa using h0), zv_eptLblIf, bind_ok]
  generalize eptLbl level = q at hu' ⊢
  obtain ⟨mL, uL⟩ := q
  dsimp only at hu'
  simp only [uncurry_apply_pair]
  rw [hct, bind_ok, if_pos hu', is_final_eq, bind_ok, hf]
  simp only [↓reduceIte, hs1, bind_ok]
  refine WP.spec_bind (Pₘ := fun r : S × A => AR r.2 c ∧ ∃ s3 : S,
      UnmapOut (L := L) X XL σ1 s1 asid va ptr level true s3
        (Fl4Spec.guestUnmap (Z := Unit) asid.bv va.bv ptr.bv level.val true σ1) ∧
      r.1 = L.zr s3 ptr 4096#u64) ?_ ?_
  · refine WP.spec_bind (C1.unmapRel hR1 hA a hAR asid va ptr level true hva (by omega)) ?_
    rintro ⟨s3, a2⟩ ⟨h1, h2⟩
    show (Std.bind (st.zero s3 ptr 4096#u64) fun s4 => ok (s4, a2)) ⦃ r => AR r.2 c ∧ ∃ s3' : S,
      UnmapOut (L := L) X XL σ1 s1 asid va ptr level true s3'
        (Fl4Spec.guestUnmap (Z := Unit) asid.bv va.bv ptr.bv level.val true σ1) ∧
      r.1 = L.zr s3' ptr 4096#u64 ⦄
    rw [L.zero_eq, bind_ok]
    exact (WP.spec_ok _).2 ⟨h1, s3, h2, rfl⟩
  · rintro ⟨s2, a1⟩ ⟨h1, s3, h2, h3⟩
    simp only at h3
    subst h3
    show (Std.bind (obj.Slot.set_cap st dest (L.zr s3 ptr 4096#u64) (.Ept ptr level false 0#u64 0#u64)) fun s4 =>
        ok (core.result.Result.Ok (), s4, a1)) ⦃ res => res.1 = .Ok () ∧ AR res.2.2 c ∧ ∃ s3' : S,
      UnmapOut (L := L) X XL σ1 s1 asid va ptr level true s3'
        (Fl4Spec.guestUnmap (Z := Unit) asid.bv va.bv ptr.bv level.val true σ1) ∧
      res.2.1 = wrCap (L := L) (L.zr s3' ptr 4096#u64) dest (.Ept ptr level false 0#u64 0#u64) ⦄
    rw [set_cap_eq, bind_ok]
    exact (WP.spec_ok _).2 ⟨rfl, h1, s3, h2, rfl⟩

variable {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V : Set U64}

open Fl4Proofs.P1

set_option maxHeartbeats 4000000 in
/-- **The EPT table unmap of a final cap at decode level, from `VmEptState`** (module docstring). -/
theorem VmEptState.tableUnmapDec (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (hA : ArchRefines arI AR) {c : Fl4Spec.Cr3} (hAR : AR a c)
    {lbl len ptr level asid va : U64} {m : Bool} (buf : U64) (ex : Array obj.Slot 3#usize)
    {pc : U64} {r : Nat} (hpc : Z.th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    (hcx : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Ept ptr level m asid va)) (h0 : level ≠ 0#u64)
    (hu : lbl.val = (Fl4Spec.eptTableLabels level.val).2) (hf : finF (L.mem s) (cslotAddr (pc.bv, idx)) = true)
    (args : List Fl4Spec.Data) (ec : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) :
    ∃ (s1 : S) (σ1 : Fl4Spec.State Unit) (Lst1 : U64 → List U64),
      sched.set_thread_state st s (L.curW s) sched.TS_RESTART = ok s1 ∧
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
      VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst1 D s1 a σ1 ∧
      ExceptT.run (Fl4Spec.decodeEptInvocation (Z := Unit) lbl.bv args (pc.bv, idx)
          (.eptCap ptr.bv level.val (if m then some (asid.bv, va.bv) else none)) ec) σ =
        ({(.ok (.tableUnmap ptr.bv level.val (if m then some (asid.bv, va.bv) else none) (pc.bv, idx)), σ)},
          False) ∧
      ept.decode st arI s a lbl len (.Ept ptr level m asid va) (cslotAddr (pc.bv, idx)) buf ex ⦃ res =>
        res.1 = .Ok () ∧ AR res.2.2 c ∧
        ((m = false ∧ res.2.1 = wrCap (L := L) s1 (cslotAddr (pc.bv, idx)) (.Ept ptr level false 0#u64 0#u64)) ∨
         (m = true ∧ ∃ s3 : S,
          UnmapOut (L := L) X XL σ1 s1 asid va ptr level true s3
            (Fl4Spec.guestUnmap (Z := Unit) asid.bv va.bv ptr.bv level.val true σ1) ∧
          res.2.1 = wrCap (L := L) (L.zr s3 ptr 4096#u64) (cslotAddr (pc.bv, idx))
            (.Ept ptr level false 0#u64 0#u64))) ⦄ := by
  have B := J.1.1
  have C := J.2
  have hct := P1.cur_thread_ok (L := L) s
  have hA0 : AbsSlot Z.th (pc.bv, idx) := ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩
  have hxs : IsSlot Z.th (cslotAddr (pc.bv, idx)) := hA0.isSlot
  have hcv : capV (L.mem s) (cslotAddr (pc.bv, idx)) = .Ept ptr level m asid va := capV_of_capAt hcx
  obtain ⟨-, hlv4, -⟩ := C.capTbl hxs hcv
  have hlv : level.val = 39 ∨ level.val = 30 ∨ level.val = 21 := by
    rcases hlv4 with h | h
    · exact absurd (UScalar.eq_of_val_eq (by rw [h]; rfl) : level = 0#u64) h0
    · exact h
  have hl0 : level.val ≠ 0 := by omega
  obtain ⟨s1, σ1, Lst1, hs1, hst1, J1⟩ := VmEptState.restart (arI := arI) J hni
  refine ⟨s1, σ1, Lst1, hs1, hst1, J1, ?_, ?_⟩
  · -- the spec decoder: finality by `fin_iff_of`
    have hfinR := fin_iff_of B.xtop.rel.1 B.xtop.rel.2.1 B.xtop.rel.2.2.1 hA0 hcx (Or.inl ⟨trivial, rfl⟩) rfl
      (by simp)
      (fun h => by
        have : Fl4Spec.GenObjRef.objRef ptr.bv ∈ Fl4Spec.genObjRefs (absCap (.Ept ptr level m asid va)) :=
          Set.mem_union_left _ (Set.mem_union_left _ ⟨ptr.bv, by simp [absCap, Fl4Spec.objRefs, Fl4Spec.aobjRef], rfl⟩)
        rw [h] at this; exact this)
    have hfin : Fl4Spec.isFinalCap' (absCap (.Ept ptr level m asid va)) σ := hfinR.1 hf
    exact zv_eD_unmapF _ _ _ _ _ hl0 (by rw [zv_dataToNat]; exact hu) σ hfin
  · cases m
    · rw [zv_eptF_unmapF0 s a _ buf ex h0 hu hf hct hs1]
      exact (WP.spec_ok _).2 ⟨rfl, hAR, Or.inl ⟨rfl, rfl⟩⟩
    · have hva : va.val < 2 ^ 47 := C.exte.vtop.1 _ hxs _ _ _ _ hcv
      refine WP.spec_mono (J1.2.unmapF1 J1.1.1.xtop.fin.2.1 hA a hAR _ buf ex h0 hlv hva hu hf hct hs1) ?_
      rintro res ⟨h1, h2, s3, h3, h4⟩
      exact ⟨h1, h2, Or.inr ⟨rfl, s3, h3, h4⟩⟩

end

end

end Fl4Proofs.P3
