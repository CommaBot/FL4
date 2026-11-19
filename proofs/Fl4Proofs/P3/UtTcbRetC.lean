/-
P3 (DESIGN.md §9), untyped: **the no-reset retype of TCBs with the new TCBs'
values** (handoff/utj.md "uttypes", ut37): UntypedTcbLoop's
`retype_full_tcb`, its creation loop replaced by UtTcbLoopC's
`create_loop_content_tcb`, so the post also has `TcbC` (registers, domain
words, debug links of the new TCBs) and the current-domain word kept.
-/
import Fl4Proofs.P3.UtTcbLoopC
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section
set_option linter.unusedSimpArgs false

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

set_option maxRecDepth 20000 in
/-- **`retype_full_tcb` with the new TCBs' values** (`TcbC`: registers,
domain words, debug links; the current-domain word kept), given that word
aligned and outside the old slots, the free region, the old debug-list head's
TCB and the head word, and the head word outside the old head's TCB. -/
theorem retype_full_tcbC {A' : Type} (arI : machine.Arch A') (ar : A') (th : TypedHeap) (s : S)
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hU : UtInv (L.mem s) G) (horig : ∀ sl, σ.isOriginalCap sl = true → AbsSlot th sl)
    {pp : U64} {rs : Nat} (hpp : th pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    {p sb fi : U64} {dev : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi dev))
    (hpal : p.val % 2 ^ sb.val = 0) (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64) (hfi : fi.val ≤ 2 ^ sb.val)
    (hhigh : 2 ^ 64 - 2 ^ 47 ≤ p.val)
    (nt us : U64) (t : Fl4Spec.ApiObjectType) (ht : objTypeOf nt.val = some t)
    (hnt : nt.val = 1) (hus : us.val < 64)
    {dest : U64} {r : Nat} (hdest : th dest = some (.cnode r)) (hr : r < 64)
    (off win : U64) (hwin : off.val + win.val ≤ 2 ^ r) (hw1 : 1 ≤ win.val)
    (hmem : win.val ≤ ((1#64 <<< sb.val : BitVec 64) - fi.bv).toNat >>> zOf nt.val us.val)
    (hempty : ∀ i : Nat, off.val ≤ i → i < off.val + win.val →
      capAt (L.mem s) (slotAddr dest.bv (BitVec.ofNat 64 i)) = ok .Null)
    (hfree : RegionFree th (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hzero : ZeroRegion (L.mem s) (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hDWal : P1.Aligned (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))
    (hDWobj : ∀ a, IsSlot th a → ¬ (a.val ≤ (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val < a.val + 32))
    (hDWreg : ¬ (p.val + fi.val ≤ (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val < p.val + 2 ^ sb.val))
    (hhead : L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = 0#u64 ∨
      (th (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) = some .tcb ∧
        TcbOk (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))))
    (hDWh0 : L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) ≠ 0#u64 →
      ¬ Rg (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) 0 4096 (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))
    (hCDal : P1.Aligned (Sched.curDomA st s))
    (hCDreg : ¬ (p.val + fi.val ≤ (Sched.curDomA st s).val ∧ (Sched.curDomA st s).val < p.val + 2 ^ sb.val))
    (hCDh0 : L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) ≠ 0#u64 →
      ¬ Rg (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) 0 4096 (Sched.curDomA st s))
    (hCDW : Sched.curDomA st s ≠ L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)
    (hCDobj : ∀ a, IsSlot th a → ¬ (a.val ≤ (Sched.curDomA st s).val ∧ (Sched.curDomA st s).val < a.val + 32))
    (bitsApi : Fl4Spec.ApiObjectType → Nat → Nat) (hb : bitsApi t us.val = zOf nt.val us.val) :
    untyped.retype st arI s ar (cslotAddr (pp.bv, idx)) false
      ⟨Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)⟩ nt us dest off win dev ⦃ res =>
      res.1 = .Ok () ∧ res.2.2 = ar ∧ ∃ σ' G' th',
        (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype (pp.bv, idx) false p.bv
          (Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)) t us.val
          (windowSlots dest r off.val win.val) dev)).run σ = ({(.ok (), σ')}, False) ∧
        Placed th' ∧ StateRel th' (L.mem res.2.1) σ' ∧ SlotsValid th' (L.mem res.2.1) ∧
        MdbLinks th' (L.mem res.2.1) G' ∧ CdtRel th' (L.mem res.2.1) σ' G' ∧ MdbInv (L.mem res.2.1) G' ∧
        (UtInv (L.mem res.2.1) G' ∧ MdbStep (L.mem s) G (L.mem res.2.1) G') ∧ ZeroRegion (L.mem res.2.1)
          ((Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)).toNat + win.val * 2 ^ zOf nt.val us.val)
          (p.val + 2 ^ sb.val) ∧
        (FinInv th (L.mem s) σ G → FinInv th' (L.mem res.2.1) σ' G') ∧ L.ksb res.2.1 = L.ksb s ∧
        WFrame (L := L) s res.2.1 (TcbLoopW th (Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)).toNat win.val
          (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))) ∧
        (TcbC (L.mem res.2.1) (Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)).toNat
          (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) (L.mem s (Sched.curDomA st s))
          (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) win.val ∧
          L.mem res.2.1 (Sched.curDomA st s) = L.mem s (Sched.curDomA st s)) ∧
        ∃ A k w dslot cj, RetExp th th' (L.mem s) (L.mem res.2.1) G G' A k w dslot cj (cslotAddr (pp.bv, idx)) ∧
          A = (Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)).toNat ∧ k = 2 ^ zOf nt.val us.val ∧ w = win.val ∧ (∀ j, j < w → isUt (cj j) = true → nt.val = 0) ∧ ThX th th' A k w nt.val us.val ∧ cj = cjOf nt.val us dev A k ∧ DslotC th dslot w ⦄ := by
  -- sizes and the region
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  have htT : t = .tcbObject := by rw [hnt] at ht; simpa [objTypeOf] using ht.symm
  subst htT
  have hz12 : zOf nt.val us.val = 12 := by simp [zOf, hnt]
  set z := zOf nt.val us.val with hzdef
  have hz : z < 64 := by omega
  have hz47 : z ≤ 47 := by omega
  set k := 2 ^ z with hkdef
  have hk4 : k = 4096 := by rw [hkdef, hz12]; rfl
  have hk1 : 1 ≤ k := Nat.one_le_two_pow
  obtain ⟨hA1, hA2, hA3, hA4⟩ := retype_region p fi sb.val z win.val hsb hz hpal hpfit hfi hw1 hmem
  rw [← hkdef] at hA2 hA3 hA4
  set Ab := Fl4Spec.alignUp (p.bv + fi.bv) z with hAbdef
  set A := Ab.toNat with hAdef
  set aligned : U64 := ⟨Ab⟩ with halig
  have halv : aligned.val = A := rfl
  have hn14 : nt.val < 14 := by omega
  set src := cslotAddr (pp.bv, idx) with hsrcdef
  have hAs : AbsSlot th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hs : IsSlot th src := hAs.isSlot
  have hsrcm : src ∈ G.chains.flatten := (hM.members src).2 ⟨hs, _, hcap, by simp⟩
  have hcv0 := capV_of_capAt hcap
  obtain ⟨hsb', hst'⟩ := topF_ut p sb fi dev hsb hpfit
  -- FL4: the cap update, then the loop
  obtain ⟨total, htot, hret⟩ := retype_noreset_eq (L := L) arI s ar src aligned nt us dest off win dev hn14 hus hz
    p sb fi dev hcap
  rw [hret]
  set nfi := core.num.U64.wrapping_sub (core.num.U64.wrapping_add aligned total) p with hnfi
  set srcC' : capability.Cap := .Untyped p sb nfi dev with hsrcC'
  have he' : EncWf srcC' := by
    have : EncWf (capability.Cap.Untyped p sb fi dev) := by rw [capAt_words] at hcap; exact decode_encWf hcap
    exact ⟨this.1, this.2⟩
  obtain ⟨s1, hs1, hU1⟩ := spec_exists (set_cap_upd (L := L) hP s hs srcC' he')
  obtain ⟨s1', hs1', σa, hσa, hR1, hV1, hcdt1, hio1⟩ := spec_exists
    (retype_set_untyped_rel (L := L) th s σ hR hV hP hpp hidx hcap aligned total win z htot)
  rw [hs1] at hs1'; have e := eq_of_ok_eq hs1'; subst e
  rw [hs1]; simp only [bind_ok]
  obtain ⟨hcs1, hco1, hlk1, hfr1⟩ := hU1
  have hupd : CapShapeUpd th (L.mem s) (L.mem s1) src :=
    { links := hlk1, caps := hco1
      shp := by rw [hcs1, hcv0]; rfl
      bdg := by rw [hcs1, hcv0]; rfl
      nn := by rw [hcs1]; simp [srcC'] }
  have hM1 := hupd.mdbLinks hM hsrcm
  have hI1 := hupd.mdbInv hM hI
  have hC1 := hupd.cdtRel hC hcdt1 hio1
  -- the spec's pieces
  have hgs : Fl4Spec.getCap (Z := Unit) (pp.bv, idx) σ = ({(.untypedCap dev p.bv sb.val fi.val, σ)}, False) := by
    obtain ⟨c, a, hc, hca, hg⟩ := hR.slot_cap (sl := (pp.bv, idx)) (p := pp) rfl (by simpa [hidx] using hpp)
    rw [hcap] at hc; have := eq_of_ok_eq hc; subst this
    rw [hg, hca.abs]; rfl
  have hwl : (windowSlots dest r off.val win.val).length = win.val := by simp [windowSlots]
  have hss : Fl4Spec.setCap (Z := Unit) (.untypedCap dev p.bv (Fl4Spec.bitsOf (.untypedCap dev p.bv sb.val fi.val))
      (Fl4Spec.unat (Ab + (BitVec.ofNat 64 (windowSlots dest r off.val win.val).length <<< bitsApi .tcbObject us.val) - p.bv)))
      (pp.bv, idx) σ = ({((), σa)}, False) := by
    rw [hwl, hb]; exact hσa
  have hrr := retypeRegionWith_eq bitsApi Ab win.val us.val .tcbObject dev σa
  rw [hb] at hrr
  rw [← hwl] at hrr
  -- the free region after the cap update
  have hzero1 : ZeroRegion (L.mem s1) (p.val + fi.val) (p.val + 2 ^ sb.val) := by
    intro w hw h1 h2
    obtain ⟨q, kq, hq, hq1, hq2, -⟩ := slot_in_object hP hs
    have hne : w.val ≠ src.val ∧ w.val ≠ src.val + 8 := by
      rcases hfree q kq hq with h | h <;> constructor <;> omega
    rw [hfr1 w hw hne.1 hne.2]; exact hzero w hw h1 h2
  have hrf : RegionFree th A (A + win.val * k) := by
    intro q kd hq
    rcases hfree q kd hq with h | h
    · left; omega
    · right; omega
  have hnn : ∀ q kd, th q = some kd → 1 ≤ objSize kd → ¬ NewP A k win.val q :=
    fun q kd hq hs1 => not_newP hk1 hrf hq hs1
  -- the debug list
  set DW := L.nodeAt s 0#u64 layout.node.DEBUG_TCBS with hDWdef
  have hksb1 : L.ksb s1 = L.ksb s := by
    have : obj.Slot.set_cap st src s srcC' ⦃ s' => L.ksb s' = L.ksb s ⦄ :=
      WP.spec_mono (set_cap_spec (L := L) src s srcC') (by rintro _ rfl; simp)
    obtain ⟨s', h', h''⟩ := spec_exists this
    rw [hs1] at h'; cases eq_of_ok_eq h'; exact h''
  have hDW : ∀ s' : S, L.ksb s' = L.ksb s → L.nodeAt s' 0#u64 layout.node.DEBUG_TCBS = DW :=
    fun s' h => nodeAt_ksb h _ _
  have hDWm : L.mem s1 DW = L.mem s DW := by
    obtain ⟨q, kq, hq, hq1, hq2, -⟩ := slot_in_object hP hs
    apply hfr1 DW hDWal
    · intro e; exact hDWobj src hs (by omega)
    · intro e; exact hDWobj src hs (by omega)
  have hfitA : A + win.val * 4096 ≤ 2 ^ 64 := by rw [← hk4]; omega
  have hA3' : A + win.val * 4096 ≤ p.val + 2 ^ sb.val := by rw [← hk4]; exact hA3
  have hal : A % 32 = 0 := by
    have h32 : 32 ∣ k := by rw [hk4]; decide
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans h32 (Nat.dvd_of_mod_eq_zero hA2))
  have hrf4 : RegionFree th A (A + win.val * 4096) := by rw [← hk4]; exact hrf
  have hzero4 : ZeroRegion (L.mem s1) A (A + win.val * 4096) :=
    fun w hw h1 h2 => hzero1 w hw (by omega) (by rw [← hk4] at h2; omega)
  have hio1' : ∀ sl, σa.isOriginalCap sl = true → AbsSlot th sl := by rw [hio1]; exact horig
  obtain ⟨hP', hR', hV', hM', hC'⟩ := extend_tcb_rel th (L.mem s1) σa G hR1 hV1 hP hM1 hC1 hio1' Ab A win.val rfl
    σa.curDomain hfitA (by omega) hal hrf4 hzero4
  set th' := extendTh th A 4096 win.val .tcb with hth'
  have hext : ∀ a, IsSlot th a → IsSlot th' a := fun a ha => ha.extend (by omega) hrf4
  have hold : ∀ a, IsSlot th a → a.val + 32 ≤ A ∨ p.val + 2 ^ sb.val ≤ a.val := by
    intro a ha
    obtain ⟨q, kq, hq, hq1, hq2, -⟩ := slot_in_object hP ha
    rcases hfree q kq hq with h | h
    · left; omega
    · right; omega
  have hnewP : ∀ i, i < win.val → NewP A 4096 win.val ⟨BitVec.ofNat 64 (A + i * 4096)⟩ := by
    intro i hi; refine ⟨i, hi, ?_⟩
    show (BitVec.ofNat 64 (A + i * 4096)).toNat = _
    have : i * 4096 < win.val * 4096 := Nat.mul_lt_mul_of_pos_right hi (by omega)
    simp; omega
  have hnew : ∀ i, i < win.val → th' ⟨BitVec.ofNat 64 (A + i * 4096)⟩ = some .tcb :=
    fun i hi => extendTh_new (hnewP i hi)
  have hnewslot : ∀ a, IsSlot th' a → ¬ IsSlot th a → ∃ q j, NewP A 4096 win.val q ∧ j < tcbSlots ∧ a = slotOf q j := by
    rintro a ⟨q, j, hj, rfl⟩ hn
    rcases hj.of_extend_tcb with hj | ⟨hq, hjl⟩
    · exact absurd ⟨q, j, hj, rfl⟩ hn
    · exact ⟨q, j, hq, hjl, rfl⟩
  have hnewv : ∀ q j, NewP A 4096 win.val q → j < tcbSlots →
      A ≤ (slotOf q j).val ∧ (slotOf q j).val + 32 ≤ A + win.val * 4096 ∧ (slotOf q j).val % 32 = 0 := by
    rintro q j ⟨i, hi, hqi⟩ hj
    have h1 : (i + 1) * 4096 ≤ win.val * 4096 := Nat.mul_le_mul_right _ hi
    rw [Nat.add_mul, Nat.one_mul] at h1
    simp [tcbSlots] at hj
    have hv : (slotOf q j).val = q.val + 32 * j := slotOf_val (by omega)
    rw [hv]; omega
  have hzs : ∀ a, IsSlot th' a → a.val + 32 ≤ A + win.val * 4096 ∨ p.val + 2 ^ sb.val ≤ a.val := by
    intro a ha
    by_cases ho : IsSlot th a
    · rcases hold a ho with h | h
      · left; omega
      · right; exact h
    · obtain ⟨q, j, hq, hj, rfl⟩ := hnewslot a ha ho
      left; exact (hnewv q j hq hj).2.1
  have hDWout : ∀ a, IsSlot th' a → ¬ (a.val ≤ DW.val ∧ DW.val < a.val + 32) := by
    intro a ha
    by_cases ho : IsSlot th a
    · exact hDWobj a ho
    · obtain ⟨q, j, hq, hj, rfl⟩ := hnewslot a ha ho
      have := hnewv q j hq hj
      intro h; exact hDWreg (by omega)
  have hsrc1 : capAt (L.mem s1) src = ok srcC' := by rw [capAt_capV, hcs1]
  have hsrcd : ∀ j, j < win.val → src ≠ slotAddr dest.bv (BitVec.ofNat 64 (off.val + j)) := by
    intro j hj e
    have := hempty (off.val + j) (by omega) (by omega)
    rw [← e, hcap] at this; cases eq_of_ok_eq this
  have hbA : (BitVec.ofNat 64 aligned.val : BitVec 64) = Ab := by rw [← bv_eq_ofNat]
  have hinv0 : LoopInv (L := L) th' (pp.bv, idx) srcC' (regionHeap σa (regionPtrs Ab win.val 4096)
        (.tcb (Fl4Spec.defaultTcb σa.curDomain)))
      (Fl4Spec.createCap (Z := Unit) .tcbObject us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 aligned.val) win.val (2 ^ zOf nt.val us.val)))
      aligned.val (2 ^ zOf nt.val us.val) win.val (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j)))
      (aligned.val + win.val * 4096) (p.val + 2 ^ sb.val) G (L.mem s1)
      (cjOf nt.val us dev aligned.val (2 ^ zOf nt.val us.val)) s1 0 := by
    refine ⟨_, G, fun σf h => h, hR', hV', hM', hC', hI1, hsrc1, ?_, ?_, ?_,
      fun w hw h1 h2 => hzero1 w hw (by omega) h2, fun x hx => Or.inl hx, fun x hx => hx,
      fun j hj => absurd hj (by omega), fun x _ => rfl, fun y x => ⟨Or.inl, by
        rintro (h | ⟨j, hj, -⟩)
        · exact h
        · omega⟩, fun h => h, fun ch hch => ⟨ch, hch, fun z hz => hz⟩, fun x _ => rfl, NullKeep.refl _ _⟩
    · intro j _ hj
      have hj' : off.val + j < 2 ^ r := by omega
      have hd : IsSlot th (slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) :=
        ⟨dest, off.val + j, Or.inl ⟨r, hdest, hj'⟩, rfl⟩
      have hnull := hempty (off.val + j) (by omega) (by omega)
      have hne : slotAddr dest.bv (BitVec.ofNat 64 (off.val + j)) ≠ src := by
        intro e; rw [e, hcap] at hnull; cases eq_of_ok_eq hnull
      rw [capAt_capV, hco1 _ hd hne, ← capAt_capV]; exact hnull
    · intro x hx hp
      have hxs : IsSlot th x := ((hM.members x).1 hx).1
      by_cases hxa : x = src
      · subst hxa
        rw [hcs1]
        refine ⟨?_, Or.inr ⟨rfl, ⟨le_refl _, le_refl _⟩⟩⟩
        obtain ⟨e1, e2, -⟩ := range_of_shape (show shape srcC' = shape (capability.Cap.Untyped p sb fi dev) from rfl)
        rw [e1, e2, hsb', hst']; have := Nat.one_le_two_pow (n := sb.val); omega
      · rw [hco1 x hxs hxa] at hp ⊢
        refine ⟨hU.reg x hx hp, ?_⟩
        rcases hU.noov src hsrcm p sb fi dev hcv0 x hx hp with h | ⟨hu, hw⟩
        · left; unfold DisjR at h ⊢; simp only [Nat.zero_mul, Nat.add_zero, show 2 ^ zOf nt.val us.val = 4096 from hk4]
          omega
        · right; refine ⟨hu, ?_⟩
          obtain ⟨e1, e2, -⟩ := range_of_shape (show shape srcC' = shape (capability.Cap.Untyped p sb fi dev) from rfl)
          unfold Within at hw ⊢; rw [hcv0] at hw; rw [e1, e2]; exact hw
    · intro y hy
      obtain ⟨hp1, hp2, hp3⟩ := hU.inc src hsrcm p sb fi dev hcv0 y hy
      have hym := (desc_mem hM hy).1
      have hys : IsSlot th y := ((hM.members y).1 hym).1
      have hya : y ≠ src := by
        intro e; subst e
        rw [hcv0, hst'] at hp3
        have : (1#64 <<< sb.val - fi.bv : BitVec 64).toNat = 2 ^ sb.val - fi.val := by
          rw [BitVec.toNat_sub, BitVec.toNat_shiftLeft]
          simp only [BitVec.toNat_ofNat, Nat.shiftLeft_eq, show fi.bv.toNat = fi.val from rfl]
          have hM' : 2 ^ sb.val < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hsb
          rw [show (1 % 2 ^ 64 * 2 ^ sb.val) % 2 ^ 64 = 2 ^ sb.val by
            rw [show (1 : Nat) % 2 ^ 64 = 1 from rfl, Nat.one_mul, Nat.mod_eq_of_lt hM']]
          omega
        rw [this, Nat.shiftRight_eq_div_pow, show 2 ^ sb.val - fi.val = 0 by omega] at hmem
        simp at hmem; omega
      rw [hco1 y hys hya]
      unfold DisjR; left; simp only [Nat.zero_mul, Nat.add_zero]; omega
  have hX0 : TcbX (L := L) th th' (L.ksb s) DW aligned.val win.val (p.val + 2 ^ sb.val) s1 0 := by
    refine ⟨hksb1, by rw [halv]; simpa using hzero4, ?_, ?_⟩
    · intro a ha ⟨c, hc, hcn⟩
      by_contra ho
      obtain ⟨q, j, hq, hj, rfl⟩ := hnewslot a ha ho
      obtain ⟨h1, h2, h3⟩ := hnewv q j hq hj
      have hz0 : ∀ w : U64, w.val = (slotOf q j).val ∨ w.val = (slotOf q j).val + 8 → L.mem s1 w = 0#u64 := by
        intro w hw
        have : w.val % 8 = 0 := by omega
        exact hzero4 w this (by omega) (by omega)
      rw [capAt_words, hz0 _ (Or.inl (by rw [wordOf_zero])), hz0 _ (Or.inr (by
        rw [wordOf_val (by have : (8#u64 : U64).val = 8 := rfl; omega)]; rfl))] at hc
      rw [decode_encode_null.2] at hc; exact hcn (eq_of_ok_eq hc).symm
    · rw [hDWm]
      rcases hhead with h | ⟨h1, h2⟩
      · exact Or.inl h
      · refine Or.inr ⟨(extendTh_of_old (by omega) hrf4 h1 objSize_pos_tcb).trans h1, h2, ?_⟩
        have e4 : objSize ObjKind.tcb = 4096 := rfl
        rcases hfree _ _ h1 with h | h
        · left; simp only [Nat.zero_mul, Nat.add_zero]; omega
        · right; exact h
  -- the current-domain word
  set CD := Sched.curDomA st s with hCDdef
  have hCDm : L.mem s1 CD = L.mem s CD := by
    obtain ⟨q, kq, hq, hq1, hq2, -⟩ := slot_in_object hP hs
    apply hfr1 CD hCDal
    · intro e; exact hCDobj src hs (by omega)
    · intro e; exact hCDobj src hs (by omega)
  have hCDs : ∀ a, IsSlot th' a → ¬ (a.val ≤ CD.val ∧ CD.val < a.val + 32) := by
    intro a ha
    by_cases ho : IsSlot th a
    · exact hCDobj a ho
    · obtain ⟨q, j, hq, hj, rfl⟩ := hnewslot a ha ho
      have := hnewv q j hq hj
      intro h; exact hCDreg (by omega)
  have hh0 : L.mem s1 DW ≠ 0#u64 → TcbOk (L.mem s1 DW) ∧ th' (L.mem s1 DW) = some .tcb ∧
      ((L.mem s1 DW).val + 4096 ≤ aligned.val ∨ p.val + 2 ^ sb.val ≤ (L.mem s1 DW).val) := by
    rw [hDWm]; intro hn
    rcases hhead with h | ⟨h1, h2⟩
    · exact absurd h hn
    · refine ⟨h2, (extendTh_of_old (by omega) hrf4 h1 objSize_pos_tcb).trans h1, ?_⟩
      have e4 : objSize ObjKind.tcb = 4096 := rfl
      rw [halv]
      rcases hfree _ _ h1 with h | h
      · left; omega
      · right; exact h
  obtain ⟨⟨s2, a2⟩, hres, ha2, hfin, hks2, hW2, hTC, hCDk⟩ := spec_exists (create_loop_content_tcb (L := L) arI ar th th' hP' hext
    ((extendTh_of_old (by omega) hrf4 hpp (objSize_pos_cnode _)).trans hpp) hidx hs hsb hpfit _
    ((extendTh_of_old (by omega) hrf4 hdest (objSize_pos_cnode _)).trans hdest) hdest (by omega)
    nt us dev .tcbObject ht hnt hus off win aligned hwin (by rw [halv]; omega) (by rw [halv]; omega)
    (by rw [halv]; exact hal) (by rw [halv]; omega) (by rw [halv]; rw [← hk4]; omega)
    (by rw [halv]; exact hnew) (p.val + 2 ^ sb.val) (by rw [halv]; rw [← hk4]; omega)
    (by rw [halv]; exact hzs) (by rw [halv]; exact hold) (L.ksb s) DW hDWal hDWout
    (by rw [halv]; omega) hDW G (L.mem s1) hsrcd (fun x hx => ((hM.members x).1 hx).1) s1 hinv0 hX0
    (by rw [halv]; omega) hh0 (by rw [hDWm]; exact hDWh0) CD (fun s' h => by rw [hCDdef]; unfold Sched.curDomA; rw [h])
    hCDal (by rw [halv]; intro h; exact hCDreg ⟨by omega, h.2⟩) (by rw [hDWm]; exact hCDh0) hCDW hCDs)
  rw [hres]
  simp only [bind_ok, uncurry_apply_pair]
  rw [WP.spec_ok]
  simp only at ha2 hfin
  obtain ⟨σf, Gf, hchain, hRf, hVf, hMf, hCf, hIf, -, -, -, -, hZf, hT1, hT1b, hT2a, hT2b, hT3, hFf, hChf, hRvf,
    hNKf⟩ := hfin
  have hdrop : ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 aligned.val) win.val
      (2 ^ zOf nt.val us.val))).drop win.val = [] := by
    apply List.drop_of_length_le; simp [windowSlots, regionPtrs]
  rw [hdrop] at hchain
  have hmx := hchain σf (mapMx_nil _ _)
  have hfiL : fi.val < 2 ^ sb.val := by
    have : (1#64 <<< sb.val - fi.bv : BitVec 64).toNat = 2 ^ sb.val - fi.val := by
      rw [BitVec.toNat_sub, BitVec.toNat_shiftLeft]
      simp only [BitVec.toNat_ofNat, Nat.shiftLeft_eq, show fi.bv.toNat = fi.val from rfl]
      have hM' : 2 ^ sb.val < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hsb
      rw [show (1 % 2 ^ 64 * 2 ^ sb.val) % 2 ^ 64 = 2 ^ sb.val by
        rw [show (1 : Nat) % 2 ^ 64 = 1 from rfl, Nat.one_mul, Nat.mod_eq_of_lt hM']]
      omega
    rw [this, Nat.shiftRight_eq_div_pow] at hmem
    by_contra hc
    rw [show 2 ^ sb.val - fi.val = 0 by omega] at hmem; simp at hmem; omega
  have hnfiv : nfi.val = A + win.val * k - p.val := by
    rw [← hA4]
    show (core.num.U64.wrapping_sub (core.num.U64.wrapping_add aligned total) p).bv.toNat = _
    rw [core.num.U64.wrapping_sub_bv_eq, core.num.U64.wrapping_add_bv_eq, htot, ← bv_eq_ofNat]
  have hzv : zOf nt.val us.val < 64 := by omega
  have hkk : 2 ^ zOf nt.val us.val = k := rfl
  have hRD : RetypeDelta th (L.mem s) (L.mem s1) (L.mem s2) G Gf src p sb fi nfi dev A k win.val
        (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) (cjOf nt.val us dev aligned.val k) := by
      refine ⟨hM, hsrcm, hcv0, hcs1, fun x hx hxs => hco1 x ((hM.members x).1 hx).1 hxs, hfiL, hA1,
        by omega, by omega, by omega, fun j _ => physF_newCap _ _ _ _, fun j hj => ?_, fun j hj => ?_,
        fun j hj hu => ?_, fun j _ q us' f d hc => cjOf_dev hc, fun j hj hm => ?_, fun j l hj hl he => ?_, hT1, hT1b,
        hT2a, hT2b, hT3⟩
      · have h1 : (j + 1) * k ≤ win.val * k := Nat.mul_le_mul_right _ hj
        rw [Nat.add_mul, Nat.one_mul] at h1
        obtain ⟨c1, -⟩ := newCap_range (n := nt.val) (by omega) ⟨BitVec.ofNat 64 (A + j * k)⟩ us dev hus hzv
          (by show (BitVec.ofNat 64 (A + j * k)).toNat + _ ≤ _; rw [hkk]; simp; omega)
        unfold cjOf; rw [halv, c1]; show (BitVec.ofNat 64 (A + j * k)).toNat = _; simp; omega
      · have h1 : (j + 1) * k ≤ win.val * k := Nat.mul_le_mul_right _ hj
        rw [Nat.add_mul, Nat.one_mul] at h1
        obtain ⟨-, c2⟩ := newCap_range (n := nt.val) (by omega) ⟨BitVec.ofNat 64 (A + j * k)⟩ us dev hus hzv
          (by show (BitVec.ofNat 64 (A + j * k)).toNat + _ ≤ _; rw [hkk]; simp; omega)
        unfold cjOf; rw [halv, c2]; show (BitVec.ofNat 64 (A + j * k)).toNat + _ - 1 = _; simp; omega
      · unfold cjOf at hu ⊢
        rw [halv] at hu ⊢
        obtain ⟨hn0, he⟩ := isUt_newCap hu
        refine ⟨us, dev, he, ?_⟩
        show 2 ^ us.val = 2 ^ zOf nt.val us.val
        simp [zOf, hn0]
      · obtain ⟨-, c0, h0, hn0⟩ := (hM.members _).1 hm
        rw [hempty (off.val + j) (by omega) (by omega)] at h0
        exact hn0 (eq_of_ok_eq h0).symm
      · have hj' : IsSlotAt th dest (off.val + j) := Or.inl ⟨r, hdest, by omega⟩
        have hl' : IsSlotAt th dest (off.val + l) := Or.inl ⟨r, hdest, by omega⟩
        by_contra hne
        rcases hj'.apart hP hl' (fun ⟨_, h2⟩ => hne (by omega)) with h | h <;>
          (change slotOf dest (off.val + j) = slotOf dest (off.val + l) at he; rw [he] at h; omega)
  have hth' : ∀ q kd, th' q = some kd → (th q = some kd ∧ (NewQ A k win.val (cjOf nt.val us dev aligned.val k) q →
      objSize kd = 0)) ∨ (NewQ A k win.val (cjOf nt.val us dev aligned.val k) q ∧ objSize kd ≤ k) := by
    rw [hk4]
    refine extendTh_shape (by omega) hrf4 (le_refl _) fun j _ => ?_
    cases hu : isUt (cjOf nt.val us dev aligned.val 4096 j)
    · rfl
    · exact absurd (isUt_newCap (by unfold cjOf at hu; exact hu)).1 (by omega)
  have hW : WFrame (L := L) s s2 (TcbLoopW th A win.val DW (L.mem s DW)) := by
    have hs' : IsSlot th src := hs
    obtain ⟨s1k, hs1k, k1⟩ := spec_exists (set_cap_kc (L := L) src s srcC')
    rw [hs1] at hs1k; cases eq_of_ok_eq hs1k
    have hd1 : L.mem s1 DW = L.mem s DW := hfr1 DW hDWal (fun e => hDWobj src hs ⟨by omega, by omega⟩)
      (fun e => hDWobj src hs ⟨by omega, by omega⟩)
    rw [hd1] at hW2
    refine WFrame.trans (s2 := s1) ⟨k1.1, k1.2, fun w hw hn => hfr1 w hw (fun e => hn (Or.inl ⟨src, hs', by omega, by omega⟩))
      (fun e => hn (Or.inl ⟨src, hs', by omega, by omega⟩))⟩ hW2
  refine ⟨rfl, ha2, σf, Gf, th', ?_, hP', hRf, hVf, hMf, hCf, hIf, ?_, ?_, fun hFI => ⟨?_, ?_⟩, by rw [hks2],
    hW, ⟨by rw [← hDWm, ← hCDm]; exact hTC, hCDk.trans hCDm⟩, A, k, win.val, _, _, hRD.toExp hU hMf hth'
      (fun hN => ((hupd.nullClr hN).extend hP' (by simp [objSize]) hzero4).of_keep hNKf), rfl, rfl, rfl, fun j hj hu => (isUt_newCap (by unfold cjOf at hu; exact hu)).1,
    ⟨fun q => by show extendTh th A 4096 win.val .tcb q = _; simp [extendTh, thKindN, hnt, hk4], hrf⟩, rfl,
    fun j hj => ⟨dest, r, hdest, off.val + j, by omega, rfl⟩⟩
  rotate_right 2
  · exact (ktyped_region (hFI.kt.sub (ksub_of_eq (nks_setCap _ _) hσa)) Ab A win.val 4096 rfl (by omega) hfitA hrf4
      (fun q kd hq hs => extendTh_of_old (by omega) hrf4 hq hs) _
      (fun q hq => ⟨fun r cs he _ => (by cases he), fun t _ => extendTh_new hq⟩)).sub
      (ksub_of_eq (nks_mapMx (nks_createCap _ _ _ _) _) hmx)
  · exact hFf (hFI.fm.recap hM.tree.nodup src (by rw [hcs1, hcv0]; exact CapSim.of_shape rfl rfl)
      (fun z hz hzs => hco1 z ((hM.members z).1 hz).1 hzs))
  · rw [hbA] at hmx
    have hrb : Fl4Spec.retypeRegionWith (Z := Unit) bitsApi Ab (windowSlots dest r off.val win.val).length us.val
        .tcbObject dev σa = ({(regionPtrs Ab (windowSlots dest r off.val win.val).length 4096,
          regionHeap σa (regionPtrs Ab win.val 4096) (.tcb (Fl4Spec.defaultTcb σa.curDomain)))}, False) := by
      rw [hrr]; simp only [ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte, hwl]
      rw [show 2 ^ z = 4096 from hk4]; rfl
    apply invokeUntyped_noreset_eq bitsApi (pp.bv, idx) p.bv Ab .tcbObject us.val _ dev σ σa _ σf _ _ hgs hss hrb
    · simp
    · rw [hwl]; rw [show 2 ^ zOf nt.val us.val = 4096 from hk4] at hmx; exact hmx
  · -- the untyped invariant
    exact ⟨hRD.utinv hU, MdbStep.retype hRD hI hChf
        (fun z hz => by rw [hRvf z hz, hupd.rv ((hM.members z).1 hz).1])
          (cjOf_vplaced rfl hA2 (by omega) (by omega) (by have := hRD.hAw; omega) (fun _ => by omega))⟩
  · rw [← hk4] at hZf; exact hZf

end

end

end Fl4Proofs.P3
