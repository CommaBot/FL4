/-
P3 (line jboot, gen 4): **the CSpace and VSpace conjuncts of `JAtZ` at the richer witness** (`w1`, `σ1`, the
typed heap `thW1`, the MDB ghost `G1`; JBoot1Z). Three non-null slots: the root TCB's CSpace root (the CNode
cap `cnC` of `rC`), the root CNode's slots 0 and 1 (the thread cap `thC` of `rT`, the SC cap `scC` of `rS`);
each is a one-slot MDB chain with no parent and zero links, none revocable.

* the caps' ranges (`base_*`, `top_*`: `[rC, rC + 63]`, `[rT, rT + 4095]`, `[rS, rS + 127]`, pairwise disjoint)
  and same-region facts (`srB_*`);
* **`w1_crel`** (`CRel`: `StateRel` with the three caps related to the spec's `cnodeCap rC 1 []`, `threadCap rT`,
  `schedContextCap rS 0`; `SlotsValid`; `MdbLinks`; `CdtRel`; `MdbInv`), **`w1_finInv`**, **`w1_finM`** (`FinM`
  at every tree of the slots: the caps name distinct objects, so overlapping caps are one slot),
  **`w1_mdbOKV`**, **`w1_utInv`**, **`w1_delInv`**, **`w1_delBound`**, **`w1_sfree`**, **`w1_utc`** (no untyped);
* **`w1_vsc`**, **`w1_fcap`**, **`w1_ext`**, **`w1_bok`**, **`w1_fcov`**, **`w1_vsRel`**, **`w1_ptRel`**,
  **`w1_poolsIn`**, **`w1_curOK`** (the root TCB current, its VSpace slot null), **`w1_orig`**.

No sorry; no premises. New module; no existing statement changed.
-/
import Fl4Proofs.P3.JBoot1Z
import Fl4Proofs.P3.JBootCs
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.JBoot
open fl4_core Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P3.Notif Fl4Proofs.P2.Wit Classical

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The caps' ranges -/

theorem physF_scC : physF scC = true := ok_inj (phys_eq _).symm
theorem physF_cnC : physF cnC = true := physF_cnode _ _ _ _
theorem physF_thC : physF thC = true := physF_thread _

theorem sizeF_cnC : (sizeF cnC).val = 6 := by
  rw [sizeF_of (c := cnC) (v := core.num.U64.wrapping_add 1#u64 fl4_abi.consts.bits.SLOT) rfl]
  unfold fl4_abi.consts.bits.SLOT; decide
theorem sizeF_thC : (sizeF thC).val = 12 := by
  rw [sizeF_of (c := thC) (v := fl4_abi.consts.bits.TCB) rfl]
  unfold fl4_abi.consts.bits.TCB; decide
theorem sizeF_scC : (sizeF scC).val = 7 := by
  rw [sizeF_of (c := scC) (v := 7#u64) rfl]; rfl

theorem ptrF_scC : ptrF scC = rS := ok_inj (ptr_eq _).symm

theorem topF_v {c : capability.Cap} {n : Nat} (hs : (sizeF c).val = n) (hn : n < 64)
    (hf : (ptrF c).val + 2 ^ n ≤ 2 ^ 64) : topF c = (ptrF c).val + 2 ^ n - 1 := by
  unfold topF
  have hm := maskF_val (b := sizeF c) (by omega)
  rw [hs] at hm
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  rw [wa_val (by rw [hm]; omega), hm]; omega

theorem base_cnC : baseF cnC = 18446744071562108928 := by unfold baseF; rw [ptrF_cnode]; rfl
theorem base_thC : baseF thC = 18446744071562100736 := by unfold baseF; rw [ptrF_thread]; rfl
theorem base_scC : baseF scC = 18446744071562104832 := by unfold baseF; rw [ptrF_scC]; rfl
theorem top_cnC : topF cnC = 18446744071562108928 + 63 := by
  rw [topF_v sizeF_cnC (by omega) (by rw [ptrF_cnode]; decide), ptrF_cnode]; rfl
theorem top_thC : topF thC = 18446744071562100736 + 4095 := by
  rw [topF_v sizeF_thC (by omega) (by rw [ptrF_thread]; decide), ptrF_thread]; rfl
theorem top_scC : topF scC = 18446744071562104832 + 127 := by
  rw [topF_v sizeF_scC (by omega) (by rw [ptrF_scC]; decide), ptrF_scC]; rfl

theorem srB_cnC : srB cnC cnC = true := by
  have e := srB_eq cnC cnC
  rw [show objects.same_region_as cnC cnC = ok true by simp [objects.same_region_as]] at e
  exact (ok_inj e).symm
theorem srB_thC : srB thC thC = true := by
  have e := srB_eq thC thC
  rw [show objects.same_region_as thC thC = ok true by simp [objects.same_region_as]] at e
  exact (ok_inj e).symm
theorem srB_scC : srB scC scC = true := by
  have e := srB_eq scC scC
  rw [show objects.same_region_as scC scC = ok true by simp [objects.same_region_as]] at e
  exact (ok_inj e).symm

/-! ## The MDB members -/

theorem flat1 {x : U64} (hx : x ∈ G1.chains.flatten) :
    (x = rT ∧ capV (wL.mem w1) x = cnC) ∨ (x = rC ∧ capV (wL.mem w1) x = thC) ∨
      (x = rC1 ∧ capV (wL.mem w1) x = scC) := by
  rcases G1_flat.1 hx with rfl | rfl | rfl
  · exact Or.inl ⟨rfl, capV_rT⟩
  · exact Or.inr (Or.inl ⟨rfl, capV_rC⟩)
  · exact Or.inr (Or.inr ⟨rfl, capV_rC1⟩)

theorem slot_of_flat {x : U64} (hx : x ∈ G1.chains.flatten) : IsSlot thW1 x := by
  rcases G1_flat.1 hx with rfl | rfl | rfl
  · exact isSlot_rT
  · exact isSlot_rC
  · exact isSlot_rC1

/-- The members of a tree of the slots are the three cap slots. -/
theorem links_mem {G : MdbGhost} (hG : MdbLinks thW1 (wL.mem w1) G) {x : U64} (hx : x ∈ G.chains.flatten) :
    (x = rT ∧ capV (wL.mem w1) x = cnC) ∨ (x = rC ∧ capV (wL.mem w1) x = thC) ∨
      (x = rC1 ∧ capV (wL.mem w1) x = scC) := by
  obtain ⟨hs, c, hc, hne⟩ := (hG.members x).1 hx
  rw [capAt_capV] at hc
  rcases slot1_cases hs with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · rw [h] at hc; exact absurd (ok_inj hc).symm hne

theorem not_ovl_of {a b : Fl4Spec.Cap} (h : ∀ g, g ∈ genObjRefs a → g ∈ genObjRefs b → False) : ¬ Ovl a b :=
  fun h' => by obtain ⟨g, hg1, hg2⟩ := Set.nonempty_iff_ne_empty.2 h'; exact h g hg1 hg2

/-- Two caps naming different objects do not overlap. -/
macro "novl" : tactic => `(tactic| exact not_ovl_of (fun g h1 h2 => by simp [genObjRefs, objRefs, capIrqs, archGenRefs, absCap, capIrqOpt, archCapSetMap] at h1 h2; rw [h1] at h2; simp [rT, rS, rC] at h2))

/-- **Overlapping caps of the slots are in one slot** (distinct objects). -/
theorem ovl_same {x y : U64}
    (hx : (x = rT ∧ capV (wL.mem w1) x = cnC) ∨ (x = rC ∧ capV (wL.mem w1) x = thC) ∨
      (x = rC1 ∧ capV (wL.mem w1) x = scC))
    (hy : (y = rT ∧ capV (wL.mem w1) y = cnC) ∨ (y = rC ∧ capV (wL.mem w1) y = thC) ∨
      (y = rC1 ∧ capV (wL.mem w1) y = scC))
    (h : Ovl (absCap (capV (wL.mem w1) x)) (absCap (capV (wL.mem w1) y))) : x = y := by
  rcases hx with ⟨rfl, ex⟩ | ⟨rfl, ex⟩ | ⟨rfl, ex⟩ <;> rcases hy with ⟨rfl, ey⟩ | ⟨rfl, ey⟩ | ⟨rfl, ey⟩ <;>
    simp only [ex, ey] at h <;> first | rfl | exact absurd h (by novl)

theorem chain_uniq {L : List (List U64)} (h : L.flatten.Nodup) {a b : List U64} (ha : a ∈ L) (hb : b ∈ L)
    {x : U64} (hxa : x ∈ a) (hxb : x ∈ b) : a = b := by
  induction L with
  | nil => cases ha
  | cons c L ih =>
    rw [List.flatten_cons, List.nodup_append] at h
    obtain ⟨-, h2, h3⟩ := h
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · rfl
    · exact absurd (List.mem_flatten.2 ⟨b, hb', hxb⟩) (fun hm => by
        first | exact h3 x hxa hm | exact h3 x hxa x hm rfl | exact h3 hxa hm)
    · exact absurd (List.mem_flatten.2 ⟨a, ha', hxa⟩) (fun hm => by
        first | exact h3 x hxb hm | exact h3 x hxb x hm rfl | exact h3 hxb hm)
    · exact ih h2 ha' hb'

/-- **`FinM` at every tree of the slots.** -/
theorem w1_finM : ∀ G, MdbLinks thW1 (wL.mem w1) G → FinM (wL.mem w1) G := by
  intro G hG
  refine ⟨fun ch1 h1 ch2 h2 x hx y hy ho => ?_, fun x hx y hy hne ho _ _ _ => ?_, fun x hx y hy _ hf => ?_,
    fun x hx y hy _ hz => ?_⟩
  · have hxf := List.mem_flatten.2 ⟨ch1, h1, hx⟩
    have hyf := List.mem_flatten.2 ⟨ch2, h2, hy⟩
    have e := ovl_same (links_mem hG hxf) (links_mem hG hyf) ho
    subst e
    exact chain_uniq hG.tree.nodup h1 h2 hx hy
  · exact absurd (ovl_same (links_mem hG hx) (links_mem hG hy) ho) hne
  · rcases links_mem hG hx with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e] at hf <;> cases hf
  · rcases links_mem hG hx with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e] at hz <;> cases hz

/-! ## `CRel` -/

theorem cs_rT0 : cslotAddr (rT.bv, tcbCnodeIndex 0) = rT := by decide
theorem cs_rC0 : cslotAddr (rC.bv, [false]) = rC := by decide
theorem cs_rC1 : cslotAddr (rC.bv, [true]) = rC1 := by decide

theorem root_map (i : Nat) (hi : i < 6) :
    tcbCnodeMap rootTcbV (tcbCnodeIndex i) = some (if i = 0 then rootCnCap else .nullCap) := by
  unfold tcbCnodeMap
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]; rfl
  · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_self]; rfl
  · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_self]; rfl
  · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]; rfl
  · rw [Function.update_of_ne (by decide), Function.update_self]; rfl
  · rw [Function.update_self]; rfl

theorem capRel_cnC : CapRel cnC rootCnCap := ⟨⟨by decide, by decide, by decide⟩, rfl⟩
theorem capRel_thC : CapRel thC (.threadCap rT.bv) := ⟨trivial, rfl⟩
theorem capRel_scC : CapRel scC (.schedContextCap rS.bv 0) := ⟨show minSchedContextBits ≤ 7 by decide, rfl⟩

theorem slotOf_rT (i : Nat) (hi : i < 6) : (slotOf rT i).val = 18446744071562100736 + 32 * i :=
  slotOf_val (by rw [rT_val]; omega)

theorem slotOf_idT (i : Nat) (hi : i < 6) : (slotOf idT i).val = 18446744071562072064 + 32 * i :=
  slotOf_val (by rw [idT_val]; omega)

theorem ne_of_val {a b : U64} (h : a.val ≠ b.val) : a ≠ b := fun e => h (by rw [e])

theorem w1_stateRel : StateRel thW1 (wL.mem w1) σ1 where
  cnode p r hp := by
    rcases thW1_some hp with ⟨-, e⟩ | ⟨rfl, e⟩ | ⟨n1, n2, hp'⟩
    · cases e
    · cases e
      refine ⟨rootCs, kh1_rC, rootCs_wf, fun idx hidx => ?_⟩
      match idx, hidx with
      | [false], _ => exact ⟨thC, _, by rw [show slotAddr rC.bv (Fl4Spec.ofBl [false]) = rC from cs_rC0, capAt_capV,
          capV_rC], rfl, capRel_thC⟩
      | [true], _ => exact ⟨scC, _, by rw [show slotAddr rC.bv (Fl4Spec.ofBl [true]) = rC1 from cs_rC1, capAt_capV,
          capV_rC1], rfl, capRel_scC⟩
    · rcases thW_some hp' with ⟨-, e⟩ | ⟨irq, e, ek⟩
      · cases e
      cases ek
      have hk : σ1.kheap p.bv = some (.cnode 0 (emptyCnode 0)) := by
        rw [σ1_kheap, kh1_old (fun h => n1 (UScalar.eq_of_val_eq (congrArg BitVec.toNat h)))
          (fun h => (rS_irq irq) (e.trans h)) (fun h => n2 (UScalar.eq_of_val_eq (congrArg BitVec.toNat h)))]
        have h0 := fInitKheap_irq irq
        rwa [e] at h0
      refine ⟨emptyCnode 0, hk, emptyCnode0_wf, fun idx hidx => ?_⟩
      have hnil : idx = [] := List.length_eq_zero_iff.1 hidx
      subst hnil
      have hs : IsSlot thW1 (slotOf p 0) := ⟨p, 0, Or.inl ⟨0, hp, by norm_num⟩, rfl⟩
      have hv : (slotOf p 0).val = p.val := by rw [IsSlotAt.val placed_thW1 (Or.inl ⟨0, hp, by norm_num⟩)]; rfl
      have hne : p.val ≠ 18446744071562100736 ∧ p.val ≠ 18446744071562108928 ∧ p.val ≠ 18446744071562108960 := by
        rcases thW_pos hp' with ⟨-, e'⟩ | ⟨-, ⟨j, hj, hpv⟩ | ⟨j, hj, hj2, hpv⟩⟩
        · cases e'
        · omega
        · omega
      refine ⟨.Null, .nullCap, ?_, by simp [emptyCnode], ⟨trivial, rfl⟩⟩
      rw [show slotAddr p.bv (Fl4Spec.ofBl []) = slotOf p 0 from rfl, capAt_capV,
        capV1_slot hs (ne_of_val (by rw [hv, rT_val]; exact hne.1)) (ne_of_val (by rw [hv, rC_val]; exact hne.2.1))
          (ne_of_val (by rw [hv]; exact hne.2.2))]
  tcb t ht := by
    rcases thW1_some ht with ⟨rfl, -⟩ | ⟨-, e⟩ | ⟨-, -, ht'⟩
    · refine ⟨rootTcbV, kh1_rT, fun i hi => ?_⟩
      have hi6 : i < 6 := by unfold tcbSlots at hi; omega
      rw [root_map i hi6]
      by_cases h0 : i = 0
      · subst h0
        exact ⟨cnC, rootCnCap, by rw [show slotAddr rT.bv (BitVec.ofNat 64 0) = rT by decide, capAt_capV, capV_rT],
          by rw [if_pos rfl], capRel_cnC⟩
      · have hs : IsSlot thW1 (slotOf rT i) := ⟨rT, i, Or.inr ⟨thW1_rT, hi⟩, rfl⟩
        have hv := slotOf_rT i hi6
        refine ⟨.Null, .nullCap, ?_, by rw [if_neg h0], ⟨trivial, rfl⟩⟩
        rw [show slotAddr rT.bv (BitVec.ofNat 64 i) = slotOf rT i from rfl, capAt_capV,
          capV1_slot hs (ne_of_val (by rw [hv, rT_val]; omega)) (ne_of_val (by rw [hv, rC_val]; omega))
            (ne_of_val (by rw [hv]; show 18446744071562100736 + 32 * i ≠ 18446744071562108960; omega))]
    · cases e
    · rcases thW_some ht' with ⟨rfl, -⟩ | ⟨_, _, e⟩
      · refine ⟨idleTcbV, σ1_idleTcb, fun i hi => ?_⟩
        have hi6 : i < 6 := by unfold tcbSlots at hi; omega
        have hs : IsSlot thW1 (slotOf idT i) := ⟨idT, i, Or.inr ⟨thW1_idT, hi⟩, rfl⟩
        have hv := slotOf_idT i hi6
        refine ⟨.Null, .nullCap, ?_, idle_map i hi6, ⟨trivial, rfl⟩⟩
        rw [show slotAddr idT.bv (BitVec.ofNat 64 i) = slotOf idT i from rfl, capAt_capV,
          capV1_slot hs (ne_of_val (by rw [hv, rT_val]; omega)) (ne_of_val (by rw [hv, rC_val]; omega))
            (ne_of_val (by rw [hv]; show 18446744071562072064 + 32 * i ≠ 18446744071562108960; omega))]
      · cases e

theorem capValid1 {x : U64} (h : IsSlot thW1 x) : CapValid thW1 (capV (wL.mem w1) x) := by
  rcases slot1_cases h with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ | e <;> rw [e]
  · exact ⟨thW1_rC, by decide⟩
  · exact thW1_rT
  · show rS ≠ 0#u64; decide
  · trivial

theorem w1_slotsValid : SlotsValid thW1 (wL.mem w1) where
  cnode p r hp i hi c h := by
    have hs : IsSlot thW1 (slotOf p i) := ⟨p, i, Or.inl ⟨r, hp, hi⟩, rfl⟩
    rw [show slotAddr p.bv (BitVec.ofNat 64 i) = slotOf p i from rfl, capAt_capV] at h
    obtain rfl := ok_inj h; exact capValid1 hs
  tcb t ht i hi c h := by
    have hs : IsSlot thW1 (slotOf t i) := ⟨t, i, Or.inr ⟨ht, hi⟩, rfl⟩
    rw [show slotAddr t.bv (BitVec.ofNat 64 i) = slotOf t i from rfl, capAt_capV] at h
    obtain rfl := ok_inj h; exact capValid1 hs

theorem segOK_single (x : U64) : Mdb.SegOK (fun _ => none : U64 → Option U64) [x] := by
  intro pre y post h
  refine ⟨[], post, rfl, fun z => ⟨fun hd => (desc_none hd).elim, fun hz => by cases hz⟩⟩

theorem w1_links : MdbLinks thW1 (wL.mem w1) G1 where
  tree := ⟨by simp [G1]; decide, fun ch h => by
    simp only [G1, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> exact segOK_single _, fun a b h => by cases h⟩
  ne_nil ch h := by simp only [G1, List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl | rfl <;> simp
  chain ch h := by
    simp only [G1, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> exact List.isChain_singleton _
  head ch h _ := by
    simp only [G1, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · exact prevOf1 isSlot_rT
    · exact prevOf1 isSlot_rC
    · exact prevOf1 isSlot_rC1
  last ch h _ := by
    simp only [G1, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · exact nextOf1 isSlot_rT
    · exact nextOf1 isSlot_rC
    · exact nextOf1 isSlot_rC1
  members a := by
    constructor
    · intro h
      refine ⟨slot_of_flat h, ?_⟩
      rcases flat1 h with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ <;> exact ⟨_, by rw [capAt_capV, e], fun h => by cases h⟩
    · rintro ⟨hs, c, hc, hne⟩
      rw [capAt_capV] at hc
      rcases slot1_cases hs with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | e
      · exact G1_flat.2 (Or.inl rfl)
      · exact G1_flat.2 (Or.inr (Or.inl rfl))
      · exact G1_flat.2 (Or.inr (Or.inr rfl))
      · rw [e] at hc; exact absurd (ok_inj hc).symm hne

theorem σ1_cdt (sl : CslotPtr) : σ1.cdt sl = none := rfl
theorem σ1_orig (sl : CslotPtr) : σ1.isOriginalCap sl = false := rfl

theorem w1_cdtRel : CdtRel thW1 (wL.mem w1) σ1 G1 where
  cdt _ _ := rfl
  cdt_slot sl q h := by cases h
  orig sl h := by rw [σ1_orig, revOf1 h.isSlot]
  par_slot a b h := by cases h

theorem w1_mdbInv : MdbInv (wL.mem w1) G1 where
  orig c p h := by cases h
  desc x y h := (desc_none h).elim
  after y hy h := absurd (nextOf1 (slot_of_flat hy)) h
  chunk ch h := by
    simp only [G1, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> exact ⟨trivial, trivial⟩
  badges y hy h := absurd (nextOf1 (slot_of_flat hy)) h
  utrev x hx h := by rcases flat1 hx with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e] at h <;> cases h
  self x hx _ := by
    unfold srM
    rcases flat1 hx with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e]
    · exact srB_cnC
    · exact srB_thC
    · exact srB_scC

/-- **`CRel` at `w1`.** -/
theorem w1_crel : CRel thW1 (wL.mem w1) σ1 G1 :=
  ⟨w1_stateRel, w1_slotsValid, w1_links, w1_cdtRel, w1_mdbInv⟩

/-- **`FinInv` at `w1`.** -/
theorem w1_finInv : FinInv thW1 (wL.mem w1) σ1 G1 := ⟨kTyped_thW1, w1_finM G1 w1_links⟩

/-! ## The untyped and overlap facts -/

theorem flat1_cap {x : U64} (hx : x ∈ G1.chains.flatten) :
    capV (wL.mem w1) x = cnC ∨ capV (wL.mem w1) x = thC ∨ capV (wL.mem w1) x = scC := by
  rcases flat1 hx with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩
  · exact Or.inl e
  · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr e)

theorem flat1_nut {x : U64} (hx : x ∈ G1.chains.flatten) {p sb fi : U64} {d : Bool}
    (h : capV (wL.mem w1) x = .Untyped p sb fi d) : False := by
  rcases flat1_cap hx with e | e | e <;> rw [e] at h <;> cases h

/-- **`UtInv` at `w1`** (`JAtZ.ut`). -/
theorem w1_utInv : UtInv (wL.mem w1) G1 where
  reg x hx _ := by
    rcases flat1_cap hx with e | e | e <;> rw [e]
    · rw [base_cnC, top_cnC]; omega
    · rw [base_thC, top_thC]; omega
    · rw [base_scC, top_scC]; omega
  inc x hx _ _ _ _ h := (flat1_nut hx h).elim
  noov x hx _ _ _ _ h := (flat1_nut hx h).elim
  excl x hx _ _ _ _ _ _ _ _ _ h := (flat1_nut hx h).elim
  fib x hx _ _ _ _ h := (flat1_nut hx h).elim
  drange x hx _ _ _ _ h := (flat1_nut hx h).elim

theorem disj_lt {a b : capability.Cap} (h : topF a < baseF b ∨ topF b < baseF a) : Disj a b := h

theorem w1_noOverlap : NoOverlap (wL.mem w1) G1 := by
  have r : baseF cnC = 18446744071562108928 ∧ topF cnC = 18446744071562108928 + 63 ∧
      baseF thC = 18446744071562100736 ∧ topF thC = 18446744071562100736 + 4095 ∧
      baseF scC = 18446744071562104832 ∧ topF scC = 18446744071562104832 + 127 :=
    ⟨base_cnC, top_cnC, base_thC, top_thC, base_scC, top_scC⟩
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := r
  intro x hx y hy _ _ _
  rcases flat1 hx with ⟨rfl, ex⟩ | ⟨rfl, ex⟩ | ⟨rfl, ex⟩ <;> rcases flat1 hy with ⟨rfl, ey⟩ | ⟨rfl, ey⟩ | ⟨rfl, ey⟩ <;>
    first
    | (rw [ex]; exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩)))
    | (rw [ex, ey]; refine Or.inl (disj_lt ?_); omega)

/-- **`MdbOKV` at `w1`.** -/
theorem w1_mdbOKV : MdbOKV (wL.ksb w1) (wL.mem w1) G1 := by
  refine ⟨⟨fun x hx p r m ep a va h => ?_, w1_utInv, w1_noOverlap⟩, fun x hx => ?_,
    ⟨∅, ∅, ∅, ∅, ∅, fun x hx => ?_⟩, fun x hx _ _ _ h => (flat1_nut hx h).elim⟩
  · rcases flat1_cap hx with e | e | e <;> rw [e] at h <;> cases h
  · rcases flat1_cap hx with e | e | e <;> rw [e] <;> trivial
  · rcases flat1_cap hx with e | e | e <;> rw [e] <;> trivial

/-- **`DelInv` at `w1`.** -/
theorem w1_delInv : DelInv thW1 (wL.mem w1) where
  zwf y hy p zt n h := by rcases slot1_cases hy with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ | e <;> rw [e] at h <;> cases h
  zu y y' hy _ _ p zt n p' zt' n' h := by
    rcases slot1_cases hy with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ | e <;> rw [e] at h <;> cases h
  nc y hy _ := ⟨prevOf1 hy, nextOf1 hy⟩

theorem w1_delBound : DelBound thW1 := DelBound.of_placed placed_thW1

theorem w1_sfree : Sched.SpecFree (wL.mem w1) G1 σ1 := fun x hx _ _ _ h => (flat1_nut hx h).elim

theorem w1_utc : ∀ sl p sb fi dev, AbsSlot thW1 sl →
    capAt (wL.mem w1) (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
    Sched.UtCapP3 (L := wL) warI thW1 w1 σ1 G1 sl p sb fi := by
  intro sl p sb fi dev hs h _
  rw [capAt_capV] at h
  rcases slot1_cases hs.isSlot with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ | e <;> rw [e] at h <;> cases ok_inj h

/-! ## VSpace and frame conjuncts -/

theorem w1_vsc : Vs.VsSlotsW thW1 ∅ ∅ ∅ ∅ ∅ (wL.mem w1) := by
  intro y hy; rcases slot1_cases hy with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ | e <;> rw [e] <;> trivial

theorem w1_fcap : Vs.FrSlots thW1 (UFr σ1) (wL.mem w1) := by
  intro y hy; rcases slot1_cases hy with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ | e <;> rw [e] <;> trivial

theorem w1_ext : JExt (L := wL) thW1 w1 where
  nat y hy := by
    rcases slot1_cases hy with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ | e <;> rw [e]
    · trivial
    · trivial
    · trivial
    · exact Vs.NativeCap.null
  vw t ht := by
    unfold tVcpuA
    exact tZ1 t (thT_thW1 t ht) 3664#u64 (by decide) (by decide) (by decide) (by decide) (by decide)

theorem w1_bok : Endp.IpcBufCapOK σ1 := by
  intro t x h
  intro dev p R mt vms md hc
  rcases kh1_tcb_of h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp [rootTcbV, idleTcbV] at hc

theorem w1_fcov : FrameCover ∅ σ1 := by
  intro q vms h
  exfalso
  rcases kh1_objs h with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ | e | e | e | e | e | e <;> cases e

theorem w1_vsRel : Vs.VsRel ∅ (wL.mem w1) (wL.ksb w1) σ1 where
  table hi h := by
    have hk : fkb.val + 288000 + 16384 ≤ 2 ^ 64 := by rw [fkb_val]; norm_num
    have hv := Vs.atA_val (ksb := fkb) (hi := hi) hk h
    rw [fkb_val] at hv
    have hz : img1 (18446744071562133504 + 288000 + 8 * hi.val) = 0#u64 := by img1z
    rw [ksb_w1, mem1_al hv (by omega), hz, optRef_zero]; rfl
  tmem hi h hne := by
    have hk : fkb.val + 288000 + 16384 ≤ 2 ^ 64 := by rw [fkb_val]; norm_num
    have hv := Vs.atA_val (ksb := fkb) (hi := hi) hk h
    rw [fkb_val] at hv
    have hz : img1 (18446744071562133504 + 288000 + 8 * hi.val) = 0#u64 := by img1z
    rw [ksb_w1, mem1_al hv (by omega), hz] at hne
    exact (hne rfl).elim
  pool p hp := hp.elim

theorem w1_ptRel : Vs.PtRel ∅ ∅ ∅ ∅ (wL.mem w1) σ1 :=
  ⟨fun p hp => hp.elim, fun p hp => hp.elim, fun p hp => hp.elim, fun p hp => hp.elim⟩

theorem w1_poolsIn : Vs.PoolsIn ∅ ∅ (wL.mem w1) := fun p hp => hp.elim

/-- **VsDelRoot's `CurOK`**: the root TCB current, its VSpace slot null. -/
theorem w1_curOK : Vs.CurOK wst thW1 w1 σ1 := by
  refine ⟨rT, rfl, thW1_rT, fun p asid h => ?_⟩
  have hs : IsSlot thW1 (slotOf rT 1) := ⟨rT, 1, Or.inr ⟨thW1_rT, by unfold tcbSlots; omega⟩, rfl⟩
  have hv := slotOf_rT 1 (by omega)
  rw [capAt_capV, capV1_slot hs (ne_of_val (by rw [hv, rT_val]; omega)) (ne_of_val (by rw [hv, rC_val]; omega))
    (ne_of_val (by rw [hv]; decide))] at h
  cases ok_inj h

/-- **`JKern.orig`** (vacuous: no slot is original). -/
theorem w1_orig : ∀ sl, σ1.isOriginalCap sl = true → AbsSlot thW1 sl := by
  intro sl h; cases h

end

end Fl4Proofs.P3.JBoot
