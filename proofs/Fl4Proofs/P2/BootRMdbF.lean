/-
# P2 (line p3mc, gen 39, unit B): the CSpace / MDB `JAtZ` fields at the second boot start

Every slot of the typed heap `thR` is the root slot `tRw` (cap `Thread tRw`, revocable, links 0) or holds four zero
words (`slotR_cases`), so the MDB ghost is **`GR`** (one chain `[tRw]`, no parent) and every MDB tree of `thR` at
`sR` is that one (`uB_links_R`). At `ZR` (P2/BootRZ), as gen 34's `P2/BootMdbF` at `(sB, σB)`:

* `placed_R` (`Placed thR`), `delBound_R` (`DelBound`, `DelBound.of_placed`);
* `mdbLinks_R` (`MdbLinks`), `cdtRel_R` (`CdtRel`: `initCdt` empty, `σR`'s original-cap map true exactly at the root
  slot (`iocR_iff`), where the revocable bit is set (`revOf_R_root`), elsewhere 0), `finM_R` (`FinM` at every tree),
  `delInv_R` (`DelInv`), `utInv_R` (`UtInv` at `GR`: the thread cap's range does not wrap), `sfree_R`
  (`SpecFree`), `utc_R` (no untyped cap), `zD_R` (no zombie).

**`JAtZ.jcov` is false here** (`jcov_R_false`: `¬ JCovD thR HR GR DB CsB sR`): the root SC `scRw` is an object of
`HR` (`sc 7`, as `JPlaced.sc` asks of the spec's SC `scRp`), and it is not covered (the only cap of the MDB is
`Thread tRw`, whose range `[tRw, tRw + 4096)` ends at `scRw`), not in `DB`, not idle (`IDLE_SC` is `sciB`) and not in
the kernel-state block. A cap whose range holds `scRw` (e.g. `SchedContext scRw 7` in a slot of the MDB) would fix
it.

No premise. No existing statement changed.
-/
import Fl4Proofs.P2.BootRZ
import Fl4Proofs.P2.BootMdbF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.BootSt
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P1 Classical

noncomputable section

theorem placed_R : Placed thR where
  align p k hp := by rcases thR_cases hp with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, g1, g2, g3⟩ <;> omega
  fits p k hp := by
    rcases thR_cases hp with ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨rfl, g1, g2, g3⟩ <;> simp only [P3.objSize, Nat.pow_zero] <;>
      omega
  disj p q kp kq hp hq hne := by
    have hv := U64.ne_of_val hne
    rcases thR_cases hp with ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨rfl, g1, g2, g3⟩ <;>
      rcases thR_cases hq with ⟨f, rfl⟩ | ⟨f, rfl⟩ | ⟨rfl, f1, f2, f3⟩ <;>
      simp only [P3.objSize, Nat.pow_zero] <;> omega
  high p k hp := by rcases thR_cases hp with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, g1, g2, g3⟩ <;> omega

theorem delBound_R : DelBound thR := DelBound.of_placed placed_R

theorem uB_GR_chains : GR.chains = [[tRw]] := rfl

theorem uB_memGR {x : U64} (h : x ∈ GR.chains.flatten) : x = tRw := by
  rw [uB_GR_chains] at h; simpa using h

theorem uB_noDesc {x y : U64} : ¬ Mdb.Desc GR.par y x := by
  intro h
  rcases h with h | ⟨_, h⟩ <;> simp [GR] at h

theorem uB_root_nn : capV (bsL.mem sR) tRw ≠ .Null := by
  rw [capV_R_root]; intro e; cases e

theorem uB_null {y : U64} (hy : IsSlot thR y) (hne : y ≠ tRw) : capV (bsL.mem sR) y = .Null :=
  ((slotR_cases hy).resolve_left hne).1

theorem mdbLinks_R : MdbLinks thR (bsL.mem sR) GR where
  tree := by
    refine ⟨by rw [uB_GR_chains]; simp, ?_, fun _ _ h => by simp [GR] at h⟩
    intro ch hch
    rw [uB_GR_chains, List.mem_singleton] at hch
    subst hch
    intro pre x post _
    exact ⟨[], post, rfl, fun y => ⟨fun h => absurd h uB_noDesc, fun h => by cases h⟩⟩
  ne_nil ch h := by
    rw [uB_GR_chains, List.mem_singleton] at h
    subst h; exact List.cons_ne_nil _ _
  chain ch h := by
    rw [uB_GR_chains, List.mem_singleton] at h
    subst h; simp
  head ch h _ := by
    rw [uB_GR_chains, List.mem_singleton] at h
    subst h; exact prevOf_R_root
  last ch h _ := by
    rw [uB_GR_chains, List.mem_singleton] at h
    subst h; exact nextOf_R_root
  members a := by
    constructor
    · intro h
      rw [uB_memGR h]
      exact ⟨isSlot_R_root, _, capAt_capV _ _, uB_root_nn⟩
    · rintro ⟨hs, c, hc, hn⟩
      rw [capAt_capV] at hc
      have e := slotR_nonnull hs (by rw [ok_inj_ff hc]; exact hn)
      rw [e, uB_GR_chains]; simp

/-- **Every MDB tree of `thR` at `sR` is the one chain `[tRw]`.** -/
theorem uB_links_R {G : MdbGhost} (hM : MdbLinks thR (bsL.mem sR) G) : G.chains = [[tRw]] := by
  have hall : ∀ a ∈ G.chains.flatten, a = tRw := fun a ha => by
    obtain ⟨hs, c, hc, hn⟩ := (hM.members a).1 ha
    rw [capAt_capV] at hc
    exact slotR_nonnull hs (by rw [ok_inj_ff hc]; exact hn)
  have hin : tRw ∈ G.chains.flatten := (hM.members tRw).2 ⟨isSlot_R_root, _, capAt_capV _ _, uB_root_nn⟩
  have hf : G.chains.flatten = [tRw] := by
    rcases hl : G.chains.flatten with _ | ⟨a, _ | ⟨b, l⟩⟩
    · rw [hl] at hin; cases hin
    · rw [hall a (by rw [hl]; simp)]
    · exfalso
      have hn := hM.tree.nodup
      rw [hl] at hn
      have ha := hall a (by rw [hl]; simp)
      have hb := hall b (by rw [hl]; simp)
      exact (List.nodup_cons.1 hn).1 (by rw [ha, ← hb]; simp)
  cases hG : G.chains with
  | nil => rw [hG] at hf; simp at hf
  | cons ch rest =>
    have hne := hM.ne_nil ch (by rw [hG]; simp)
    rw [hG, List.flatten_cons] at hf
    rcases List.append_eq_singleton_iff.1 hf with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact absurd h1 hne
    · rw [h1]
      cases rest with
      | nil => rfl
      | cons ch2 r2 =>
        have hne2 := hM.ne_nil ch2 (by rw [hG]; simp)
        rw [List.flatten_cons] at h2
        exact absurd (List.append_eq_nil_iff.1 h2).1 hne2

theorem uB_cslot0 (t : U64) : cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 0) = slotOf t 0 := by
  show slotAddr t.bv (Fl4Spec.ofBl _) = _
  rw [slotAddr_ofBl, tcbCnodeIndex_blVal 0 (by decide)]

theorem uB_cslot_root : cslotAddr (tRp, Fl4Spec.tcbCnodeIndex 0) = tRw := by
  rw [show tRp = tRw.bv from rfl, uB_cslot0]
  exact eq_of_val'' (by rw [slotOf_val (by rw [tRw_val]; omega), tRw_val])

theorem cdtRel_R : CdtRel thR (bsL.mem sR) (σR (Z := Unit)) GR where
  cdt _ _ := rfl
  cdt_slot _ _ h := by cases h
  orig sl hs := by
    by_cases e : sl = (tRp, Fl4Spec.tcbCnodeIndex 0)
    · rw [(iocR_iff sl).2 e, e, uB_cslot_root, revOf_R_root]
    · have hf : (σR (Z := Unit)).isOriginalCap sl = false :=
        Bool.eq_false_iff.2 (fun h => e ((iocR_iff sl).1 h))
      rw [hf]
      rcases slotR_cases hs.isSlot with h | ⟨-, -, -, h, -⟩
      · exact absurd (cslotAddr_inj placed_R hs absSlot_R_root (by rw [h, uB_cslot_root])) e
      · exact h.symm
  par_slot _ _ h := by cases h

theorem finM_R : ∀ G, MdbLinks thR (bsL.mem sR) G → FinM (bsL.mem sR) G := by
  intro G hM
  have hG := uB_links_R hM
  have hm : ∀ x ∈ G.chains.flatten, x = tRw := fun x hx => by rw [hG] at hx; simpa using hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ch1 h1 ch2 h2 _ _ _ _ _
    rw [hG, List.mem_singleton] at h1 h2
    rw [h1, h2]
  · intro x hx y hy hne
    exact absurd ((hm x hx).trans (hm y hy).symm) hne
  · intro x hx y hy hne
    exact absurd ((hm x hx).trans (hm y hy).symm) hne
  · intro x hx y hy hne
    exact absurd ((hm x hx).trans (hm y hy).symm) hne

theorem delInv_R : DelInv thR (bsL.mem sR) where
  zwf y hy p zt n h := by
    rcases slotR_cases hy with rfl | ⟨hn, -⟩
    · rw [capV_R_root] at h; cases h
    · rw [hn] at h; cases h
  zu y y' hy _ _ p zt n p' zt' n' h := by
    rcases slotR_cases hy with rfl | ⟨hn, -⟩
    · rw [capV_R_root] at h; cases h
    · rw [hn] at h; cases h
  nc y hy hnull := by
    rcases slotR_cases hy with rfl | ⟨-, h1, h2, -⟩
    · exact absurd hnull uB_root_nn
    · exact ⟨h1, h2⟩

theorem uB_sizeF_thread (q : U64) : sizeF (.Thread q) = fl4_abi.consts.bits.TCB := ok_inj (size_eq _).symm

/-- The root thread cap's last byte. -/
theorem uB_topF_R : topF (.Thread tRw) = 18446744071562076160 + 4095 := by
  unfold topF
  rw [ptrF_thread, uB_sizeF_thread]
  have hm : (maskF fl4_abi.consts.bits.TCB).val = 4095 := by
    have hT : fl4_abi.consts.bits.TCB.val = 12 := by simp [fl4_abi.consts.bits.TCB]
    rw [maskF_val (b := fl4_abi.consts.bits.TCB) (by rw [hT]; decide), hT] <;> rfl
  simp only [core.num.U64.wrapping_add_val_eq, hm, tRw_val]; simp [U64.size, U64.numBits]

theorem utInv_R : UtInv (bsL.mem sR) GR where
  reg x hx _ := by
    rw [uB_memGR hx, capV_R_root]
    unfold baseF
    rw [ptrF_thread, uB_topF_R, tRw_val]; omega
  inc x hx p sb fi d h := by rw [uB_memGR hx, capV_R_root] at h; cases h
  noov x hx p sb fi d h := by rw [uB_memGR hx, capV_R_root] at h; cases h
  excl x hx y hy hne p sb fi fi' d d' h := by rw [uB_memGR hx, capV_R_root] at h; cases h
  fib x hx p sb fi d h := by rw [uB_memGR hx, capV_R_root] at h; cases h
  drange x hx p sb fi d h := by rw [uB_memGR hx, capV_R_root] at h; cases h

theorem sfree_R : SpecFree (bsL.mem sR) GR (σR (Z := Unit)) := by
  intro x hx p sb fi h
  rw [uB_memGR hx, capV_R_root] at h; cases h

theorem utc_R : ∀ sl p sb fi dev, AbsSlot thR sl → capAt (bsL.mem sR) (cslotAddr sl) = ok (.Untyped p sb fi dev) →
    dev = false → Sched.UtCapP3 (L := bsL) LocPlatM.archT thR sR (σR (Z := Unit)) GR sl p sb fi := by
  intro sl p sb fi dev hs hc _
  rw [capAt_capV] at hc
  rcases slotR_cases hs.isSlot with e | ⟨hn, -⟩
  · rw [e, capV_R_root] at hc; cases ok_inj_ff hc
  · rw [hn] at hc; cases ok_inj_ff hc

theorem zD_R : ∀ p ∈ ZTcb (L := bsL) thR sR, p ∈ DB := by
  rintro p ⟨y, hy, zt, n, h, -⟩
  rcases slotR_cases hy with rfl | ⟨hn, -⟩
  · rw [capV_R_root] at h; cases h
  · rw [hn] at h; cases h

theorem uB_idleScW : idleScW (L := bsL) sR = sciB := by
  unfold idleScW
  rw [sR_cpu]
  have h0 : layout.node.IDLE_SC.val = 32 := by simp [layout.node.IDLE_SC]
  rw [memR_mem (nodeR_aligned (by omega) (by omega)), sR_nodeAt_val (by omega), h0]
  rw [wordR_of (by omega)]
  simp [wordB]

/-- **`JAtZ.jcov` is false at `(sR, σR)`** with `D = DB` (module docstring): the root SC `scRw` is neither covered,
dead-set, idle nor in the kernel-state block. -/
theorem jcov_R_false : ¬ JCovD (L := bsL) thR HR GR DB CsB sR := by
  intro h
  rcases h.h scRw (.sc 7) HR_scR with ⟨y, hy, -, -, -, ht⟩ | hd | (e | e) | ⟨-, hk⟩
  · rw [uB_memGR hy, capV_R_root, uB_topF_R, scRw_val] at ht
    simp only [HKind.bits, Nat.reducePow] at ht; omega
  · have hd' : scRw.val = 18446744071562084352 ∨ scRw.val = 18446744071562088448 ∨
        scRw.val = 18446744071562092544 := hd
    rw [scRw_val] at hd'; omega
  · rw [sR_idleW] at e
    have := congrArg UScalar.val e; rw [scRw_val, tiB_val] at this; omega
  · rw [uB_idleScW] at e; exact scRw_ne_sciB e
  · have := hk (.sc 7) HR_scR
    unfold KsIn at this
    rw [sR_ksb, kbB_val, scRw_val] at this
    omega

end

end Fl4Proofs.P2.BootSt
