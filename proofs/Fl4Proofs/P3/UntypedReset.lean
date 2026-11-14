/-
P3 (DESIGN.md §9), untyped: **`untyped::reset_untyped` against l4v
`reset_untyped_cap`**, CSpace side.

* `detype` is matched by restricting the ghost typed heap to outside the
  untyped region (`restrictTh`); the CSpace relations move over
  (`detype_rel`) for an untyped cap with no descendants, using the
  untyped invariant's `drange` clause: no other cap meets the region except
  untyped ancestors.
* the cap's free index going down keeps `UtInv` (`UtInv.reset_fi`).
-/
import Fl4Proofs.P3.UntypedUtFull
import Fl4Proofs.P3.UntypedInvoke
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-! ## The ghost typed heap without a region -/

/-- `th` without the objects whose address is in `[lo, hi)` (l4v `detype`). -/
def restrictTh (th : TypedHeap) (lo hi : Nat) : TypedHeap :=
  fun q => if lo ≤ q.val ∧ q.val < hi then none else th q

/-- Hypothesis: every object lies wholly inside `[lo, hi)` or wholly outside. -/
def NoStraddle (th : TypedHeap) (lo hi : Nat) : Prop :=
  ∀ q k, th q = some k → (lo ≤ q.val ∧ q.val + objSize k ≤ hi) ∨ q.val + objSize k ≤ lo ∨ hi ≤ q.val

section
variable {th : TypedHeap} {lo hi : Nat}

theorem restrictTh_some {q : U64} {k : ObjKind} (h : restrictTh th lo hi q = some k) :
    th q = some k ∧ ¬ (lo ≤ q.val ∧ q.val < hi) := by
  unfold restrictTh at h; split_ifs at h with h1; exact ⟨h, h1⟩

theorem restrictTh_out {q : U64} (h : ¬ (lo ≤ q.val ∧ q.val < hi)) : restrictTh th lo hi q = th q := by
  simp [restrictTh, h]

theorem Placed.restrict (hP : Placed th) : Placed (restrictTh th lo hi) :=
  ⟨fun p k h => hP.align p k (restrictTh_some h).1, fun p k h => hP.fits p k (restrictTh_some h).1,
    fun p q kp kq h1 h2 hne => hP.disj p q kp kq (restrictTh_some h1).1 (restrictTh_some h2).1 hne,
    fun p k h => hP.high p k (restrictTh_some h).1⟩

theorem restrict_obj_out (hN : NoStraddle th lo hi) {q : U64} {k : ObjKind} (h : restrictTh th lo hi q = some k) :
    q.val + objSize k ≤ lo ∨ hi ≤ q.val := by
  obtain ⟨h1, h2⟩ := restrictTh_some h
  rcases hN q k h1 with h3 | h3 | h3 <;> omega

theorem RegionFree.restrict (hN : NoStraddle th lo hi) : RegionFree (restrictTh th lo hi) lo hi :=
  fun _ _ h => restrict_obj_out hN h

theorem IsSlotAt.of_restrict {q : U64} {i : Nat} (h : IsSlotAt (restrictTh th lo hi) q i) : IsSlotAt th q i := by
  rcases h with ⟨r, hr, hi⟩ | ⟨ht, hi⟩
  · exact Or.inl ⟨r, (restrictTh_some hr).1, hi⟩
  · exact Or.inr ⟨(restrictTh_some ht).1, hi⟩

theorem IsSlot.of_restrict {a : U64} (h : IsSlot (restrictTh th lo hi) a) : IsSlot th a := by
  obtain ⟨q, i, hi, rfl⟩ := h; exact ⟨q, i, hi.of_restrict, rfl⟩

/-- The words of a slot of the restricted heap are outside the region. -/
theorem IsSlot.restrict_words (hP : Placed th) (hN : NoStraddle th lo hi) {a : U64}
    (h : IsSlot (restrictTh th lo hi) a) : a.val + 32 ≤ lo ∨ hi ≤ a.val := by
  obtain ⟨q, i, hi', rfl⟩ := h
  obtain ⟨k, hk, hs⟩ := hi'.size
  have hv := hi'.val hP.restrict
  rcases restrict_obj_out hN hk with h | h <;> rw [hv] <;> omega

/-- The object of a slot outside the region is outside it. -/
theorem IsSlotAt.obj_out (hP : Placed th) (hN : NoStraddle th lo hi) {q : U64} {i : Nat} (h : IsSlotAt th q i)
    (hout : (slotOf q i).val < lo ∨ hi ≤ (slotOf q i).val) : ¬ (lo ≤ q.val ∧ q.val < hi) := by
  obtain ⟨k, hk, hs⟩ := h.size
  have hv := h.val hP
  rw [hv] at hout
  rcases hN q k hk with h3 | h3 | h3 <;> omega

theorem IsSlotAt.restrict (hP : Placed th) (hN : NoStraddle th lo hi) {q : U64} {i : Nat} (h : IsSlotAt th q i)
    (hout : (slotOf q i).val < lo ∨ hi ≤ (slotOf q i).val) : IsSlotAt (restrictTh th lo hi) q i := by
  have ho := h.obj_out hP hN hout
  unfold IsSlotAt; rw [restrictTh_out ho]; exact h

theorem IsSlot.restrict (hP : Placed th) (hN : NoStraddle th lo hi) {a : U64} (h : IsSlot th a)
    (hout : a.val < lo ∨ hi ≤ a.val) : IsSlot (restrictTh th lo hi) a := by
  obtain ⟨q, i, hi', rfl⟩ := h; exact ⟨q, i, hi'.restrict hP hN hout, rfl⟩

theorem AbsSlot.of_restrict {sl : Fl4Spec.CslotPtr} (h : AbsSlot (restrictTh th lo hi) sl) : AbsSlot th sl := by
  obtain ⟨p, h1, h2 | ⟨h2, hi⟩⟩ := h
  · exact ⟨p, h1, Or.inl (restrictTh_some h2).1⟩
  · exact ⟨p, h1, Or.inr ⟨(restrictTh_some h2).1, hi⟩⟩

theorem AbsSlot.restrict (hP : Placed th) (hN : NoStraddle th lo hi) {sl : Fl4Spec.CslotPtr} (h : AbsSlot th sl)
    (hout : (cslotAddr sl).val < lo ∨ hi ≤ (cslotAddr sl).val) : AbsSlot (restrictTh th lo hi) sl := by
  obtain ⟨q, i, hi', hq, he⟩ := h.at
  have ho := hi'.obj_out hP hN (by rw [← he]; exact hout)
  obtain ⟨p, h1, h2⟩ := h
  have : p = q := bv_inj (h1.symm.trans hq)
  subst this
  refine ⟨p, h1, ?_⟩
  rw [restrictTh_out ho]; exact h2

end

/-! ## Caps meeting the region of an untyped cap without descendants -/

theorem physF_cnode (q r g gb : U64) : physF (.CNode q r g gb) = true := ok_inj (phys_eq _).symm
theorem physF_thread (q : U64) : physF (.Thread q) = true := ok_inj (phys_eq _).symm
theorem ptrF_cnode (q r g gb : U64) : ptrF (.CNode q r g gb) = q := ok_inj (ptr_eq _).symm
theorem ptrF_thread (q : U64) : ptrF (.Thread q) = q := ok_inj (ptr_eq _).symm

/-- A physical cap whose base is in the region of an untyped cap `x` without
descendants is untyped (an ancestor of `x`), or is `x`. -/
theorem meet_reset {th : TypedHeap} {mem : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G)
    (hI : MdbInv mem G) (hU : UtInv mem G) {x p sb fi : U64} {dev : Bool} (hx : x ∈ G.chains.flatten)
    (hcx : capV mem x = .Untyped p sb fi dev) (hnd : ∀ y, ¬ Mdb.Desc G.par y x)
    {y : U64} (hy : y ∈ G.chains.flatten) (hp : physF (capV mem y) = true)
    (hb : p.val ≤ baseF (capV mem y)) (hb2 : baseF (capV mem y) < p.val + 2 ^ sb.val) :
    y = x ∨ isUt (capV mem y) = true := by
  by_cases hyx : y = x
  · exact Or.inl hyx
  right
  have hr := hU.reg y hy hp
  have hrx := hU.reg x hx (by rw [hcx]; exact physF_ut _ _ _ _)
  rw [hcx] at hrx
  obtain ⟨x1, x2, -⟩ := ut_range (capV_ut_sb hcx) hrx
  rcases hU.drange x hx p sb fi dev hcx y hy hyx hp (by unfold Disj; rw [hcx, x1, x2]; omega) with e | e
  · exact absurd e (hnd y)
  · exact hI.anc_ut e (by rw [hcx]; rfl)

/-! ## The relations without the region -/

section
variable {th : TypedHeap} {mem : U64 → U64} {G : MdbGhost}

/-- **`detype` on the CSpace relations**: for an untyped cap `x` without
descendants, with no linked slot in its region and no object straddling
it, the relations hold for the heap restricted to outside the region and
any spec state whose heap agrees outside it. -/
theorem detype_rel {Z : Type} {σ σd : Fl4Spec.State Z}
    (hR : StateRel th mem σ) (hV : SlotsValid th mem) (hP : Placed th)
    (hM : MdbLinks th mem G) (hC : CdtRel th mem σ G) (hI : MdbInv mem G) (hU : UtInv mem G)
    {x p sb fi : U64} {dev : Bool} (hx : x ∈ G.chains.flatten) (hcx : capV mem x = .Untyped p sb fi dev)
    (hnd : ∀ y, ¬ Mdb.Desc G.par y x)
    (hN : NoStraddle th p.val (p.val + 2 ^ sb.val))
    (hns : ∀ a ∈ G.chains.flatten, a.val < p.val ∨ p.val + 2 ^ sb.val ≤ a.val)
    (hk : ∀ q : U64, ¬ (p.val ≤ q.val ∧ q.val < p.val + 2 ^ sb.val) → σd.kheap q.bv = σ.kheap q.bv)
    (hcdt : σd.cdt = σ.cdt) (hio : σd.isOriginalCap = σ.isOriginalCap) :
    StateRel (restrictTh th p.val (p.val + 2 ^ sb.val)) mem σd ∧
      SlotsValid (restrictTh th p.val (p.val + 2 ^ sb.val)) mem ∧
      MdbLinks (restrictTh th p.val (p.val + 2 ^ sb.val)) mem G ∧
      CdtRel (restrictTh th p.val (p.val + 2 ^ sb.val)) mem σd G := by
  set lo := p.val
  set hi := p.val + 2 ^ sb.val
  have hpx : ∀ a, a ∈ G.chains.flatten → a.val < lo ∨ hi ≤ a.val := hns
  -- caps to objects of the region are only in the region
  have hcv : ∀ a c, IsSlot th a → capAt mem a = ok c → CapValid th c →
      CapValid (restrictTh th lo hi) c := by
    intro a c ha hc hv
    have hnn : ∀ q, (c = .CNode q (match c with | .CNode _ r _ _ => r | _ => 0#u64)
        (match c with | .CNode _ _ g _ => g | _ => 0#u64) (match c with | .CNode _ _ _ g => g | _ => 0#u64) ∨
        c = .Thread q) → ¬ (lo ≤ q.val ∧ q.val < hi) := by
      intro q hq hin
      have hcn : c ≠ .Null := by rcases hq with h | h <;> rw [h] <;> simp
      have ham := (hM.members a).2 ⟨ha, c, hc, hcn⟩
      have hcV : capV mem a = c := capV_of_capAt hc
      have hp : physF (capV mem a) = true := by
        rw [hcV]; rcases hq with h | h <;> rw [h]; exacts [physF_cnode _ _ _ _, physF_thread _]
      have hb : baseF (capV mem a) = q.val := by
        unfold baseF; rw [hcV]; rcases hq with h | h <;> rw [h]; exacts [by rw [ptrF_cnode], by rw [ptrF_thread]]
      rcases meet_reset hM hI hU hx hcx hnd ham hp (by omega) (by omega) with e | e
      · rw [e, hcx] at hcV; rcases hq with h | h <;> rw [h] at hcV <;> cases hcV
      · rw [hcV] at e; rcases hq with h | h <;> rw [h] at e <;> simp [isUt] at e
    cases c with
    | CNode q r g gb =>
      obtain ⟨h1, h2⟩ := hv
      exact ⟨by rw [restrictTh_out (hnn q (Or.inl rfl))]; exact h1, h2⟩
    | Thread q =>
      show restrictTh th lo hi q = some .tcb
      rw [restrictTh_out (hnn q (Or.inr rfl))]; exact hv
    | _ => trivial
  refine ⟨⟨fun q r hq => ?_, fun t ht => ?_⟩, ⟨fun q r hq i hi c hc => ?_, fun t ht i hi c hc => ?_⟩,
    ⟨hM.tree, hM.ne_nil, hM.chain, hM.head, hM.last, fun a => ?_⟩, ⟨fun sl hs => ?_, fun sl q hq => ?_,
      fun sl hs => ?_, fun a b hab => ?_⟩⟩
  · obtain ⟨h1, h2⟩ := restrictTh_some hq
    rw [hk q h2]; exact hR.cnode q r h1
  · obtain ⟨h1, h2⟩ := restrictTh_some ht
    rw [hk t h2]; exact hR.tcb t h1
  · have h1 := (restrictTh_some hq).1
    exact hcv _ c ⟨q, i, Or.inl ⟨r, h1, hi⟩, rfl⟩ hc (hV.cnode q r h1 i hi c hc)
  · have h1 := (restrictTh_some ht).1
    exact hcv _ c ⟨t, i, Or.inr ⟨h1, hi⟩, rfl⟩ hc (hV.tcb t h1 i hi c hc)
  · rw [hM.members a]
    constructor
    · rintro ⟨ha, rest⟩
      exact ⟨ha.restrict hP hN (hpx a ((hM.members a).2 ⟨ha, rest⟩)), rest⟩
    · rintro ⟨ha, rest⟩; exact ⟨ha.of_restrict, rest⟩
  · rw [hcdt]; exact hC.cdt sl hs.of_restrict
  · rw [hcdt] at hq
    obtain ⟨h1, h2⟩ := hC.cdt_slot sl q hq
    have e := hC.cdt sl h1
    rw [hq] at e
    obtain ⟨m1, m2⟩ := hM.tree.par_mem _ _ e.symm
    exact ⟨h1.restrict hP hN (hpx _ m1), h2.restrict hP hN (hpx _ m2)⟩
  · rw [hio]; exact hC.orig sl hs.of_restrict
  · obtain ⟨sl, h1, h2⟩ := hC.par_slot a b hab
    have m1 := (hM.tree.par_mem _ _ hab).1
    exact ⟨sl, h1.restrict hP hN (by rw [h2]; exact hpx _ m1), h2⟩

end

/-! ## The free index going down keeps `UtInv` -/

/-- **Lowering the free index of an untyped cap without descendants keeps
`UtInv`**: what meets its region is an untyped ancestor, whose used part
holds it, so is full if of the same region. -/
theorem UtInv.reset_fi {th : TypedHeap} {mem mem' : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G)
    (hI : MdbInv mem G) (hU : UtInv mem G) {x p sb fi f : U64} {dev : Bool} (hx : x ∈ G.chains.flatten)
    (hcx : capV mem x = .Untyped p sb fi dev) (hnd : ∀ y, ¬ Mdb.Desc G.par y x)
    (hcx' : capV mem' x = .Untyped p sb f dev) (hf : f.val ≤ 2 ^ sb.val)
    (hcap : ∀ z ∈ G.chains.flatten, z ≠ x → capV mem' z = capV mem z) : UtInv mem' G := by
  have hrx := hU.reg x hx (by rw [hcx]; exact physF_ut _ _ _ _)
  rw [hcx] at hrx
  obtain ⟨x1, x2, x3⟩ := ut_range (capV_ut_sb hcx) hrx
  have hsh : shape (capV mem' x) = shape (capV mem x) := by rw [hcx, hcx']; rfl
  obtain ⟨e1, e2, e3⟩ := range_of_shape hsh
  -- ranges and kinds are unchanged
  have rb : ∀ z ∈ G.chains.flatten, baseF (capV mem' z) = baseF (capV mem z) ∧ topF (capV mem' z) = topF (capV mem z) ∧
      physF (capV mem' z) = physF (capV mem z) ∧ isUt (capV mem' z) = isUt (capV mem z) := by
    intro z hz
    by_cases hzx : z = x
    · subst hzx; exact ⟨e1, e2, e3, isUt_of_shape hsh⟩
    · rw [hcap z hz hzx]; exact ⟨rfl, rfl, rfl, rfl⟩
  -- an untyped cap meeting `x` is an ancestor, and is full if of the same region
  have hanc : ∀ y ∈ G.chains.flatten, y ≠ x → physF (capV mem y) = true → ¬ Disj (capV mem y) (capV mem x) →
      Mdb.Desc G.par x y := by
    intro y hy hyx hp hd
    rcases hU.drange x hx p sb fi dev hcx y hy hyx hp hd with e | e
    · exact absurd e (hnd y)
    · exact e
  have hW : ∀ y ∈ G.chains.flatten, y ≠ x → physF (capV mem y) = true → ¬ Disj (capV mem y) (capV mem x) →
      isUt (capV mem y) = true ∧ baseF (capV mem y) ≤ p.val ∧ p.val + 2 ^ sb.val - 1 ≤ topF (capV mem y) := by
    intro y hy hyx hp hdj
    have ha := hanc y hy hyx hp hdj
    have hu : isUt (capV mem y) = true := hI.anc_ut ha (by rw [hcx]; rfl)
    obtain ⟨q', b', i', d', hq⟩ := isUt_iff.1 hu
    obtain ⟨-, g2, g3⟩ := hU.inc y hy q' b' i' d' hq x ha
    have hry := hU.reg y hy hp
    rw [hq] at hry
    obtain ⟨y1, y2, -⟩ := ut_range (capV_ut_sb hq) hry
    have hfb := hU.fib y hy q' b' i' d' hq
    rw [hcx, x1] at g2; rw [hcx, x2] at g3
    refine ⟨hu, ?_, ?_⟩ <;> rw [hq]
    · rw [y1]; exact g2
    · rw [y2]; omega
  have hfull : ∀ y ∈ G.chains.flatten, y ≠ x → ∀ i' d', capV mem y = .Untyped p sb i' d' → 2 ^ sb.val ≤ i'.val := by
    intro y hy hyx i' d' hc1
    have hry := hU.reg y hy (by rw [hc1]; exact physF_ut _ _ _ _)
    rw [hc1] at hry
    obtain ⟨y1, y2, -⟩ := ut_range (capV_ut_sb hc1) hry
    have ha := hanc y hy hyx (by rw [hc1]; exact physF_ut _ _ _ _)
      (by unfold Disj; rw [hc1, hcx, x1, x2, y1, y2]; omega)
    have g3 := (hU.inc y hy _ _ _ _ hc1 x ha).2.2
    rw [hcx, x2] at g3; omega
  refine ⟨fun z hz hp => ?_, fun z hz q b i d hc y hd => ?_, fun z hz q b i d hc y hy hp => ?_,
    fun z hz y hy hzy q b i i' d d' hcz hcy => ?_, fun z hz q b i d hc => ?_,
    fun z hz q b i d hc y hy hyz hp hd => ?_⟩
  · obtain ⟨r1, r2, r3, -⟩ := rb z hz
    rw [r3] at hp; rw [r1, r2]; exact hU.reg z hz hp
  · by_cases hzx : z = x
    · rw [hzx] at hd; exact absurd hd (hnd y)
    · rw [hcap z hz hzx] at hc
      obtain ⟨r1, r2, r3, -⟩ := rb y (desc_mem hM hd).1
      rw [r1, r2, r3]; exact hU.inc z hz q b i d hc y hd
  · obtain ⟨r1, r2, r3, r4⟩ := rb y hy
    rw [r3] at hp
    by_cases hzx : z = x
    · have hc' := hc; rw [hzx, hcx'] at hc'
      injection hc' with hq hb hi hdd
      rw [← hq, ← hb, ← hi, hzx]
      by_cases hyx : y = x
      · right; rw [hyx, hcx']; exact ⟨rfl, le_refl _, le_refl _⟩
      · by_cases hdj : Disj (capV mem y) (capV mem x)
        · left; unfold DisjR; unfold Disj at hdj; rw [hcx, x1, x2] at hdj; rw [r1, r2]; omega
        · right
          obtain ⟨g1, g2, g3⟩ := hW y hy hyx hp hdj
          rw [r4]; refine ⟨g1, ?_⟩
          unfold Within; rw [e1, e2, r1, r2, hcx, x1, x2]; exact ⟨g2, g3⟩
    · rw [hcap z hz hzx] at hc ⊢
      rcases hU.noov z hz q b i d hc y hy hp with g | ⟨g1, g2⟩
      · left; unfold DisjR at g ⊢; rw [r1, r2]; exact g
      · right; rw [r4]; refine ⟨g1, ?_⟩
        unfold Within at g2 ⊢; rw [r1, r2]; exact g2
  · by_cases hzx : z = x
    · have hc' := hcz; rw [hzx, hcx'] at hc'
      injection hc' with hq hb hi hdd
      have hyx : y ≠ x := fun e => hzy (hzx.trans e.symm)
      rw [hcap y hy hyx, ← hq, ← hb] at hcy
      right; rw [← hb]; exact hfull y hy hyx _ _ hcy
    · by_cases hyx : y = x
      · have hc' := hcy; rw [hyx, hcx'] at hc'
        injection hc' with hq hb hi hdd
        rw [hcap z hz hzx, ← hq, ← hb] at hcz
        left; rw [← hb]; exact hfull z hz hzx _ _ hcz
      · rw [hcap z hz hzx] at hcz; rw [hcap y hy hyx] at hcy
        exact hU.excl z hz y hy hzy _ _ _ _ _ _ hcz hcy
  · by_cases hzx : z = x
    · have hc' := hc; rw [hzx, hcx'] at hc'
      injection hc' with hq hb hi hdd
      rw [← hi, ← hb]; exact hf
    · rw [hcap z hz hzx] at hc; exact hU.fib z hz _ _ _ _ hc
  · have hz' : ∃ i0, capV mem z = .Untyped q b i0 d := by
      by_cases hzx : z = x
      · have hc' := hc; rw [hzx, hcx'] at hc'
        injection hc' with hq hb hi hdd
        rw [hzx, hcx, hq, hb, hdd]; exact ⟨_, rfl⟩
      · exact ⟨i, by rw [← hcap z hz hzx]; exact hc⟩
    obtain ⟨i0, hc0⟩ := hz'
    obtain ⟨r1, r2, r3, -⟩ := rb y hy
    obtain ⟨s1, s2, -, -⟩ := rb z hz
    rw [r3] at hp
    exact hU.drange z hz q b i0 d hc0 y hy hyz hp (by unfold Disj at hd ⊢; rw [r1, r2, s1, s2] at hd; exact hd)

end

end Fl4Proofs.P3
