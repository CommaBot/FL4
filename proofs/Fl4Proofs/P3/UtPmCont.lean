/-
P3 (DESIGN.md §9), untyped: **`untyped::retype` of PML4s without a reset,
with its one spec outcome** (`retype_cont_pml4R`: `retype_cont_pml4N`'s
no-reset case stated as `RetPost`, for the PML4 retype at `J`, UtPmRet).
-/
import Fl4Proofs.P3.UntypedPml4
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **The success continuation of `decode` for PML4s without a reset**
(`RetPost`: `retype_cont_pml4N`'s no-reset case, its one outcome kept), the
global PML4 a PML4 object of the spec, aligned, outside the untyped region. -/
theorem retype_cont_pml4R {A' : Type} (arI : machine.Arch A') (ar : A') (th : TypedHeap) (s : S)
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hU : UtInv (L.mem s) G) (horig : ∀ sl, σ.isOriginalCap sl = true → AbsSlot th sl)
    (ct : U64) (hcur : σ.curThread = ct.bv) (hct : sched.cur_thread st s = ok ct) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    {pp : U64} {rs : Nat} (hpp : th pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    {p sb fi : U64} {dev : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi dev))
    (hpal : p.val % 2 ^ sb.val = 0) (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64) (hfi : fi.val ≤ 2 ^ sb.val)
    (hhigh : 2 ^ 64 - 2 ^ 47 ≤ p.val)
    (hactZ : ¬ (p.val ≤ (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val ∧
      (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val < p.val + 2 ^ sb.val))
    (hfree : RegionFree th (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hzero : ZeroRegion (L.mem s) (p.val + fi.val) (p.val + 2 ^ sb.val))
    (bitsApi : Fl4Spec.ApiObjectType → Nat → Nat)
    (nt us dest off win : U64) (t : Fl4Spec.ApiObjectType) (r : Nat) (reset : Bool) (fiv : U64)
    (hn8 : nt.val = 8) (hrs0 : reset = false) (hb : bitsApi t us.val = zOf nt.val us.val)
    (hDWal : P1.Aligned (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))
    (hDWobj : ∀ a, IsSlot th a → ¬ (a.val ≤ (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val < a.val + 32))
    (hDWreg : ¬ (p.val ≤ (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val < p.val + 2 ^ sb.val))
    (hDWne : (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ≠ (stA ct).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ≠ (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val)
    (hhead : L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = 0#u64 ∨
      (th (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) = some .tcb ∧
        TcbOk (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))))
    (hgpm : HasPm σ σ.archState.x64GlobalPml4) (hga : σ.archState.x64GlobalPml4.toNat % 4096 = 0)
    (hgf : σ.archState.x64GlobalPml4.toNat + 4096 ≤ 2 ^ 64)
    (hgreg : ¬ (p.val ≤ σ.archState.x64GlobalPml4.toNat ∧ σ.archState.x64GlobalPml4.toNat < p.val + 2 ^ sb.val))
    (hctx : RetCtx (L := L) th s σ (pp.bv, idx) sb fi dev nt us dest off win t r reset fiv) :
    (do
      let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
      untyped.retype st arI s2 ar (cslotAddr (pp.bv, idx)) reset
        ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ nt us dest off win dev) ⦃ res =>
      RetPost (L := L) th (L.mem s) G σ ar arI s bitsApi (L.ksb s) (.retype (pp.bv, idx) reset p.bv
        (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val) dev) res ∧
        (∀ w : U64, P1.Aligned w → (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat ≤ w.val →
          w.val < (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat + win.val * 2 ^ zOf nt.val us.val →
          (w.val - (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat) % 2 ^ zOf nt.val us.val < 2048 →
          L.mem res.2.1 w = 0#u64) ⦄ := by
  have htP : t = .archObject .pml4Obj := by
    have := hctx.ty; rw [hn8] at this; simpa [objTypeOf, Fl4Spec.archDataToObjType] using this.symm
  have hgct : σ.archState.x64GlobalPml4 ≠ ct.bv := by
    intro e; obtain ⟨pt, hpt⟩ := hgpm; obtain ⟨tcb, hkt, -⟩ := hR.tcb ct htcb; rw [e, hkt] at hpt; cases hpt
  have hcase : ¬ (reset = true ∧ fi.val ≠ 0) := fun h => by rw [hrs0] at h; exact absurd h.1 (by simp)
  have hunused : (¬ ∃ x, σ.cdt x = some (pp.bv, idx)) → fi.val = 0 := by
    intro hnc
    by_contra hf
    exact hcase ⟨by rw [hctx.resetEq]; simpa using hnc, hf⟩
  have hactZ' : ¬ (p.val + fi.val ≤ (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val ∧
      (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val < p.val + 2 ^ sb.val) := fun h => hactZ ⟨by omega, h.2⟩
  obtain ⟨ht, ⟨hus, hz47, hsB, hsC, hsD⟩, ⟨hdest, hr64, -⟩, ⟨hw1, -, hwin⟩, hempty, hreset, hfiv, -, hmem, hdevc⟩ := hctx
  -- set_thread_state
  have htf := hP.fits ct _ htcb
  have hta := hP.align ct _ htcb
  have hstv : (stA ct).val = ct.val + 3328 := by
    rw [stA_eq, wordOf_val (by simp [objSize] at htf; simp; omega)]; simp
  obtain ⟨s2, hs2, hSS⟩ := spec_exists (set_thread_state_slots (L := L) th hP s ct sched.TS_RESTART htcb hact)
  obtain ⟨s2', hs2', hF⟩ := spec_exists (set_thread_state_frame (L := L) s ct sched.TS_RESTART
    (by unfold P1.Aligned; rw [hstv]; omega) hact.1)
  rw [hs2] at hs2'; have := eq_of_ok_eq hs2'; subst this
  rw [hs2]; simp only [bind_ok]
  obtain ⟨tcb, hkt, -⟩ := hR.tcb ct htcb
  obtain ⟨σ1, hst1, hR1, hV1, hM1, hC1, hcdt1, hio1⟩ := restart_rel hR hV hM hC hSS (t := ct.bv) hkt .restart
  have hI1 := MdbInv.of_same hM hI hSS
  have hU1 := UtInv.of_same hM hU hSS
  have hcap1 : capAt (L.mem s2) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi dev) := by
    rw [hSS.capAt (AbsSlot.isSlot ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩)]; exact hcap
  have hempty1 : ∀ i : Nat, off.val ≤ i → i < off.val + win.val →
      capAt (L.mem s2) (slotAddr dest.bv (BitVec.ofNat 64 i)) = ok .Null := by
    intro i h1 h2
    rw [hSS.capAt ⟨dest, i, Or.inl ⟨r, hdest, by omega⟩, rfl⟩]; exact hempty i h1 h2
  have hzero1 : ZeroRegion (L.mem s2) (p.val + fi.val) (p.val + 2 ^ sb.val) := by
    intro w hw h1 h2
    rw [hF w hw (by
      rw [hstv]; intro e
      have e4 : objSize ObjKind.tcb = 4096 := rfl
      rcases hfree ct _ htcb with h | h <;> omega) (by
      intro e; exact hactZ' (by rw [← e]; exact ⟨h1, h2⟩))]
    exact hzero w hw h1 h2
  have horig1 : ∀ sl, σ1.isOriginalCap sl = true → AbsSlot th sl := by rw [hio1]; exact horig
  have hsc : nt.val = 5 → 7 ≤ us.val := fun h => by omega
  have hct0 : nt.val = 4 → us.val ≠ 0 := fun h e => hsB ⟨h, e⟩
  obtain ⟨s2', hs2', hk2⟩ := spec_exists (sts_ksb_ret (L := L) s ct sched.TS_RESTART)
  rw [hs2] at hs2'; cases eq_of_ok_eq hs2'
  have hDW2 : L.nodeAt s2 0#u64 layout.node.DEBUG_TCBS = L.nodeAt s 0#u64 layout.node.DEBUG_TCBS :=
    nodeAt_ksb hk2 _ _
  have hDWm2 : L.mem s2 (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) :=
    hF _ hDWal hDWne.1 hDWne.2
  obtain ⟨σ1', hst1', hk1', harch1'⟩ := setThreadState_arch σ ct.bv tcb hkt .restart
  rw [hst1] at hst1'
  have e1 : σ1 = σ1' := by have := congrArg (fun x => x.1) hst1'; simpa using this
  subst e1
  have hgpm1 : HasPm σ1 σ1.archState.x64GlobalPml4 := by
    rw [harch1']; obtain ⟨pt, hpt⟩ := hgpm; exact ⟨pt, by rw [hk1', Function.update_of_ne hgct]; exact hpt⟩
  have hfiv' : fiv = fi := by
    rw [hfiv]
    cases hrs : reset
    · rfl
    · rw [hrs] at hreset
      have hnc : ¬ ∃ x, σ.cdt x = some (pp.bv, idx) := by simpa using hreset.symm
      exact (UScalar.eq_of_val_eq (by rw [hunused hnc]; rfl))
  subst hfiv'
  have hfull := retype_full_pml4 (L := L) arI ar th s2 σ1 G hR1 hV1 hP hM1 hC1 hI1 hU1 horig1 hpp hidx hcap1 hpal hpfit
    hfi hhigh nt us _ ht hn8 hus hdest (by omega) off win hwin hw1 hmem hempty1 hfree hzero1 bitsApi (by rw [← htP]; exact hb) hgpm1
    (by rw [harch1']; exact hga) (by rw [harch1']; exact hgf) (by rw [harch1']; exact hgreg)
    (by cases hd : dev
        · rfl
        · exact absurd hn8 (dev_nt ht (hdevc hd)).2.2)
  rw [← htP] at hfull
  obtain ⟨hWA1, -, hWA3, -⟩ :=
    retype_region p fiv sb.val (zOf nt.val us.val) win.val (capAt_untyped_inv hcap) (by omega) hpal hpfit hfi hw1 hmem
  have hWA2 : (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat % 2 ^ zOf nt.val us.val = 0 :=
    (retype_region p fiv sb.val (zOf nt.val us.val) win.val (capAt_untyped_inv hcap) (by omega) hpal hpfit hfi hw1 hmem).2.1
  have hRB0 : reset = true → (∃ p sb d, capAt (L.mem s2) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb 0#u64 d)) ∧
    untyped.reset_untyped st arI s2 ar (cslotAddr (pp.bv, idx)) = ok (.Ok (), s2, ar) := by
    intro hrs
    have hnc : ¬ ∃ x, σ.cdt x = some (pp.bv, idx) := by rw [hrs] at hreset; simpa using hreset.symm
    have hf0 : fiv = 0#u64 := UScalar.eq_of_val_eq (by rw [hunused hnc]; rfl)
    rw [hf0] at hcap1
    exact ⟨⟨_, _, _, hcap1⟩, reset_untyped_unused arI s2 ar _ hcap1⟩
  have hpost : ∀ res, (res.1 = .Ok () ∧ res.2.2 = ar ∧ ∃ σ' G' th',
        (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype (pp.bv, idx) false p.bv
          (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val
          (windowSlots dest r off.val win.val) dev)).run σ1 = ({(.ok (), σ')}, False) ∧
        Placed th' ∧ StateRel th' (L.mem res.2.1) σ' ∧ SlotsValid th' (L.mem res.2.1) ∧
        MdbLinks th' (L.mem res.2.1) G' ∧ CdtRel th' (L.mem res.2.1) σ' G' ∧ MdbInv (L.mem res.2.1) G' ∧
        (UtInv (L.mem res.2.1) G' ∧ MdbStep (L.mem s2) G (L.mem res.2.1) G') ∧ ZeroRegion (L.mem res.2.1)
          ((Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat + win.val * 2 ^ zOf nt.val us.val)
          (p.val + 2 ^ sb.val) ∧
        (FinInv th (L.mem s2) σ1 G → FinInv th' (L.mem res.2.1) σ' G') ∧ L.ksb res.2.1 = L.ksb s2 ∧
        WFrame (L := L) s2 res.2.1 (fun w => SlotSpan th w ∨ ((Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat ≤ w.val ∧
          w.val < (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat + win.val * 2 ^ zOf nt.val us.val ∧
          2048 ≤ (w.val - (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat) % 2 ^ zOf nt.val us.val)) ∧
        ∃ A k w dslot cj, RetExp th th' (L.mem s2) (L.mem res.2.1) G G' A k w dslot cj (cslotAddr (pp.bv, idx)) ∧
          A = (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat ∧ k = 2 ^ zOf nt.val us.val ∧ w = win.val ∧ (∀ j, j < w → isUt (cj j) = true → nt.val = 0) ∧ ThX th th' A k w nt.val us.val ∧ cj = cjOf nt.val us dev A k ∧ DslotC th dslot w) →
      (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype (pp.bv, idx) reset p.bv
          (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val
          (windowSlots dest r off.val win.val) dev)).run σ1 =
        (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype (pp.bv, idx) false p.bv
          (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val
          (windowSlots dest r off.val win.val) dev)).run σ1 →
      RetPost (L := L) th (L.mem s) G σ ar arI s bitsApi (L.ksb s) (.retype (pp.bv, idx) reset p.bv
        (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val) dev) res ∧
        (∀ w : U64, P1.Aligned w → (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat ≤ w.val →
          w.val < (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat + win.val * 2 ^ zOf nt.val us.val →
          (w.val - (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat) % 2 ^ zOf nt.val us.val < 2048 →
          L.mem res.2.1 w = 0#u64) := by
    rintro res ⟨h1, h2, σ', G', th', hrun, hP', hR', hV', hM', hC', hI', ⟨hU', hSt'⟩, -, hFin, hks, hWf, A, k, w, dslot,
      cj, hE, rfl, rfl, rfl, hnu, hthx, hcjE, hdsC⟩ he
    refine ⟨?_, fun w0 hw0 g1 g2 g3 => ?_⟩
    rotate_left
    · -- the new PML4s' user halves: zero before (`hzero1`), written by no step
      have hns : ¬ SlotSpan th w0 := by
        rintro ⟨a, ha, a1, a2⟩
        obtain ⟨q, kq, hq, hq1, hq2, -⟩ := slot_in_object hP ha
        rcases hfree q kq hq with h | h <;> omega
      rw [hWf.2.2 w0 hw0 (by
        rintro (h | ⟨-, -, h⟩)
        · exact hns h
        · exact absurd h (Nat.not_le.2 g3))]
      exact hzero1 w0 hw0 (by omega) (by omega)
    exact ⟨h1, h2, σ1, by rw [hcur]; exact hst1, σ', G', th', he.trans hrun, hP', hR', hV', hM', hC', hI', hU',
    MdbStep.same_left hM hSS hSt', fun hFI => hFin (hFI.of_same hM hSS (ksub_of_eq (setThreadState_nks _ _) hst1)),
    by rw [hks, hk2], _, _, _, dslot, cj, hE.same_left hM hSS,
    ⟨⟨ct, s2, hct, hs2, Or.inr ⟨h1, ⟨rfl, by rw [hb], by simp [windowSlots], hWA2⟩, s2, th, _, _, Or.inl ⟨rfl, rfl, rfl, rfl, hRB0⟩, le_rfl, le_rfl, hthx.2, fun a h => h, ⟨nt.val, ht, hthx, us, rfl, hcjE⟩, hdsC,
      hWf.mono fun v hv => hv.elim (fun h => Or.inl (Or.inr h)) (fun h => Or.inr ⟨htP, h.1, h.2.1⟩),
      fun ⟨_, hne⟩ => absurd htP hne, fun hT => absurd (htP.symm.trans hT) (by simp)⟩⟩, fun _ j hj hu => by have h0 := hnu j hj hu; rw [h0] at ht; simpa [objTypeOf] using ht.symm⟩⟩
  subst hrs0
  exact WP.spec_mono hfull (fun res h => hpost res h rfl)

end

end

end Fl4Proofs.P3
