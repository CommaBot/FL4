/-
P3 (DESIGN.md §9), untyped: **the no-reset retype of PML4s at `J`**
(`JAtZ.utPmJ`; handoff/utj.md "uttypes (line ut22-)"; l4v
`invoke_untyped_corres` with `init_arch_objects`' `copy_global_mappings`).

`JAtZ.utEpJ`'s skeleton for type 8: FL4's `retype` (`retype_cont_pml4R`)
writes slot words and the window (each new PML4's kernel half,
`copy_global_mappings`); the spec adds the window's PML4s, each with the
global mappings copied in (`invokeUntyped_noreset_pml4`), then changes
CNodes. No set grows (the new PML4s are in none of `Z`'s sets; `XTopAt`
by `XTopAt.addStepW`, the window's words read by no relation, UtPmAdd). The
scheduler and untyped-cap fields across the window writes by UtPmKeep's
`uaRestW`, `addRPW`, `ret_utcW`; P1's creation by `JAtZ.create_noresetW`
(the window's words in new `other 12` objects, which P1 does not track).
-/
import Fl4Proofs.P3.UtPmKeep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

theorem objTypeOf_pml4 {n : Nat} (h : objTypeOf n = some (.archObject .pml4Obj)) : n = 8 := by
  have hn : n < 19 := by
    by_contra hc
    rw [(objTypeOf_none n).2 (by omega)] at h; cases h
  interval_cases n <;> simp_all [objTypeOf, Fl4Spec.archDataToObjType]

set_option maxHeartbeats 16000000 in
/-- **The no-reset retype of PML4s at `J`** (module docstring; `JAtZ.utEpJ`'s
skeleton, one core, `Z.c = 0`): from `JAtZ` at the decode (no reschedule
pending), the decoded arguments (`RetCtx`, no reset: the source cap has a
child), the source a CNode slot's RAM untyped cap, FL4's restart and
`untyped::retype` of PML4s (the kernel half copied into each new object)
end in `UtRetPostJ` (done, `JAt` after at the same sets but the MDB ghost). -/
theorem JAtZ.utPmJ {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) {ct : U64} (hct : sched.cur_thread st s = ok ct) {pp : U64} {rs : Nat} {idx : List Bool}
    (hpp : Z.th pp = some (.cnode rs)) (hidx : idx.length = rs) {p sb fi : U64}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false))
    {nt us dest off win : U64} {t : Fl4Spec.ApiObjectType} {r : Nat} {fiv : U64}
    (hnt : nt.val = 8) (hc0 : Z.c = 0#u64)
    (hctx : RetCtx (L := L) Z.th s σ (pp.bv, idx) sb fi false nt us dest off win t r false fiv)
    (hBO : BufObjHyp Z.B σ) (hAF : ArchFitHyp H σ) (hRU : RegionUnrefJ (L := L) arI H Cs) (blk call don : Bool) :
    (do
      let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
      untyped.retype st arI s2 ar (cslotAddr (pp.bv, idx)) false
        ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ nt us dest off win false) ⦃ res =>
      UtRetPostJ (L := L) arI AR σ blk call don (.retype (pp.bv, idx) false p.bv
        (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val) false)
        res ⦄ := by
  have hBF : BufFreeHyp Z.B (L.mem s) Z.G := bufFree_of_obj J.sfree hBO
  have hAs : AbsSlot Z.th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hU := J.utc _ p sb fi false hAs hcap rfl
  have hnd : Sched.NotDev (L.mem s) (cslotAddr (pp.bv, idx)) p sb fi := Sched.notDev_ram (capV_of_capAt hcap)
  obtain ⟨hP, ⟨hSR, hV, hM, hC, hI⟩, hFI0, -, hMO0, -⟩ := J.xtop.rel
  have hc2 : sched.cur_thread st s = ok (L.curW s) := cur_thread_eq s
  have hctE : ct = L.curW s := by rw [hct] at hc2; exact eq_of_ok_eq hc2
  subst hctE
  have hty := hctx.ty
  have ht : t = .archObject .pml4Obj := by
    have e := hty; rw [hnt] at e; simpa [objTypeOf, Fl4Spec.archDataToObjType] using e.symm
  have htU : t ≠ .untyped := by rw [ht]; simp
  have htT : t ≠ .tcbObject := by rw [ht]; simp
  have hb : Fl4Spec.fl4ObjBitsApi t us.val = zOf nt.val us.val := (objTypeOf_fl4 hty us.val).2.1
  have hfiv : fiv = fi := by rw [hctx.fidx]; rfl
  subst hfiv
  have hunused : (¬ ∃ x, σ.cdt x = some (pp.bv, idx)) → fiv.val = 0 := fun hnc => by
    have e := hctx.resetEq; simp [hnc] at e
  -- the restart, at `J` and at the CSpace
  obtain ⟨s1, σ1, x1, -, hst1, -, -, he1, hns1, hid1, hct1, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  obtain ⟨s1', σ1', -, hs1', -, hSS1, -, -, hk1, hcpu1⟩ :=
    restart_dstate Z.th hP s σ Z.G J.dstate (L.curW s) hct J.kern.cur J.kern.curT J.kern.act
  rw [hs1] at hs1'; cases eq_of_ok_eq hs1'
  have hksz : KSz σ σ1 := ksz_of_eq (nkz_setThreadState _ _) hst1
  -- the window, against the source cap
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  obtain ⟨hA1, hA2, hA3, -⟩ := retype_region p fiv sb.val (zOf nt.val us.val) win.val hsb (by simp [zOf, hnt]) hU.pal hU.pfit hU.fiLe hctx.window.1 hctx.memory
  refine WP.spec_mono (retype_cont_pml4R (L := L) arI ar Z.th s σ Z.G hSR hV hP hM hC hI J.ut J.kern.orig (L.curW s)
    J.kern.cur hct J.kern.curT J.kern.act hpp hidx hcap hU.pal hU.pfit hU.fiLe (hU.high hnd)
    (hU.actZ hnd) hU.free (hU.zero hnd) Fl4Spec.fl4ObjBitsApi nt us dest off win t r
    false fiv hnt rfl hb J.kern.dwAl J.kern.dwObj (hU.dwReg hnd) J.kern.dwNe J.kern.head
    J.kern.gpm J.kern.ga J.kern.gf (hU.gReg hnd) hctx) (fun res hRP => ?_)
  unfold UtRetPostJ
  have hRPN := RetPost.toN hRP
  obtain ⟨hok, har, σ1'', hst, σ', G', th', hrun, hP', hR', hV', hM', hC', hI', hU', hSt, hFin, hks, Aw, k, w, dslot, cj,
    hE, hRF, hRFu⟩ := hRP
  have e1 : σ1'' = σ1 := by
    have e := congrArg Prod.fst (hst.symm.trans hst1)
    simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at e
    exact e
  subst σ1''
  obtain ⟨ct0, s0, hct0, hs0, hbr⟩ := hRF
  rw [hct] at hct0; cases eq_of_ok_eq hct0
  rw [hs1] at hs0; cases eq_of_ok_eq hs0
  rcases hbr with ⟨e, -⟩ | ⟨-, ⟨eA, ek, ew, hAk⟩, sR, thR, lo, hi, hor, -, -, -, -, ⟨n0, hn0, hThX, uu, -, hcj⟩, -,
    hW, hWZ, -⟩
  · rw [hok] at e; cases e
  have hsR : sR = s1 ∧ thR = Z.th := by
    rcases hor with ⟨h1, h2, -⟩ | ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hRB⟩
    · exact ⟨h1, h2⟩
    · cases hRB
  obtain ⟨e2, e3⟩ := hsR
  subst sR
  subst thR
  have hn0v : n0 = nt.val := by
    rw [hnt]; have e := hn0; rw [ht] at e; exact objTypeOf_pml4 e
  subst hn0v
  have hk0 : thKindN nt.val us.val = none := by
    unfold thKindN; rw [if_neg (by omega), if_neg (by omega)]
  have hth : th' = Z.th := funext fun q => by rw [hThX.1 q, hk0]; simp
  subst hth
  -- FL4's writes: slot words and the window (the new PML4s' kernel half)
  have hw : P1.WritesIn st s1 res.2.1 (fun b => Sched.SlotWd Z.th b ∨ (Aw ≤ b.val ∧ b.val < Aw + w * k)) :=
    ⟨hW.1, hW.2.1, fun b hb hn => hW.2.2 b hb (fun h => hn (by
    rcases h with (⟨h1, -⟩ | h) | ⟨-, h⟩
    · exact absurd h1 htT
    · exact Or.inl (Sched.slotSpan_wd hP hb h)
    · exact Or.inr h))⟩
  -- the spec's outcome: the window's objects added, then CNodes changed
  have hSR1 := J1.xtop.rel.2.1.1
  have hlen : (windowSlots dest r off.val win.val).length = win.val := by simp [windowSlots]
  have hzW : zOf nt.val us.val = 12 := by simp [zOf, hnt]
  have hal : ∀ q ∈ regionPtrs (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
      (windowSlots dest r off.val win.val).length (2 ^ Fl4Spec.fl4ObjBitsApi (.archObject .pml4Obj) us.val),
      q.toNat % 4096 = 0 ∧ q.toNat + 4096 ≤ 2 ^ 64 := by
    intro q hq
    rw [hlen] at hq
    obtain ⟨j, hj, rfl⟩ := regionPtrs_mem hq
    rw [← ht, hb] at hq ⊢
    have hjk : (j + 1) * 2 ^ zOf nt.val us.val ≤ win.val * 2 ^ zOf nt.val us.val := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at hjk
    have hfit := hU.pfit
    have hqv := ptrAdd_toNat (rb := Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
      (n := j * 2 ^ zOf nt.val us.val) (by have := Nat.one_le_two_pow (n := zOf nt.val us.val); omega)
    rw [hqv]
    rw [hzW] at hjk hA2 hA3 ⊢
    simp only [Nat.reducePow] at hjk hA2 hA3 ⊢
    constructor <;> omega
  have hrunP := hrun
  rw [ht] at hrunP
  obtain ⟨-, σB, oo, hA, hpm, hcnk, hkc⟩ := invokeUntyped_noreset_pml4 Fl4Spec.fl4ObjBitsApi (pp.bv, idx) p.bv _ us.val
    (windowSlots dest r off.val win.val) false σ1 {pp.bv, dest.bv} (Or.inl rfl)
    (fun d hd => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hd
      exact Or.inr rfl)
    (by
      rintro q (rfl | hq)
      · obtain ⟨cs, h, -⟩ := hSR1.cnode pp rs hpp; exact ⟨rs, cs, h⟩
      · rw [Set.mem_singleton_iff.1 hq]; obtain ⟨cs, h, -⟩ := hSR1.cnode dest r hctx.cnode.1; exact ⟨r, cs, h⟩)
    (by
      intro q hq
      rw [hlen] at hq
      obtain ⟨j, hj, rfl⟩ := regionPtrs_mem hq
      rw [← ht, hb] at hq ⊢
      have hjk : (j + 1) * 2 ^ zOf nt.val us.val ≤ win.val * 2 ^ zOf nt.val us.val := Nat.mul_le_mul_right _ hj
      rw [Nat.add_mul, Nat.one_mul] at hjk
      have hfit := hU.pfit
      have hqv := ptrAdd_toNat (rb := Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
        (n := j * 2 ^ zOf nt.val us.val) (by have := Nat.one_le_two_pow (n := zOf nt.val us.val); omega)
      cases hq1 : σ1.kheap (Fl4Spec.ptrAdd (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
          (j * 2 ^ zOf nt.val us.val)) with
      | none => rfl
      | some ko =>
        exfalso
        obtain ⟨ko0, hko0, -⟩ := hksz _ _ hq1
        have hxG : cslotAddr (pp.bv, idx) ∈ Z.G.chains.flatten := (hM.members _).2 ⟨hAs.isSlot, _, hcap, by simp⟩
        have h1 := Nat.one_le_two_pow (n := Fl4Spec.objBits ko0)
        have hz1 := Nat.one_le_two_pow (n := zOf nt.val us.val)
        rcases J.sfree _ hxG p sb fiv (capV_of_capAt hcap) _ ko0 hko0 with h | ⟨h2, h3⟩
        · rw [hqv] at h; omega
        · rw [hqv] at h2 h3; omega)
    hal
    J1.kern.gpm J1.kern.ga J1.kern.gf
    (.ok (), σ') (by rw [hrunP]; rfl)
  have ho : ∀ q, q ∈ regionPtrs (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
      (windowSlots dest r off.val win.val).length (2 ^ Fl4Spec.fl4ObjBitsApi (.archObject .pml4Obj) us.val) →
      ∀ x n, oo q ≠ .schedContext x n := by
    intro q hq x n e; obtain ⟨pt, e'⟩ := hpm q hq; rw [e'] at e; cases e
  have hks1 : L.ksb s1 = L.ksb s := hk1
  have hcjne : ∀ j, j < w → ∀ p a, cj j ≠ .Pml4 p true a := by
    intro j _ p a
    rw [hcj]
    simp [cjOf, newCapOf, hnt]
  have hTS : ∀ t0, Z.th t0 = some .tcb → ∀ p0 asid, capAt (L.mem res.2.1) (slotOf t0 1) = ok (.Pml4 p0 true asid) →
      capAt (L.mem s1) (slotOf t0 1) = ok (.Pml4 p0 true asid) := by
    intro t0 ht0 p0 asid hc
    have hxs : IsSlot Z.th (slotOf t0 1) := ⟨t0, 1, Or.inr ⟨ht0, by decide⟩, rfl⟩
    rw [hSS1.capAt hxs]
    exact retExp_pml4_backT hE hM hM' hcjne hxs hc
  have hksR : L.ksb res.2.1 = L.ksb s := hw.1.trans hks1
  have hnbR : L.nodeBase res.2.1 Z.c = L.nodeBase s Z.c := by simp only [P1.LawfulStore.nodeBase, hksR]
  have hfit := hU.pfit
  have hhigh := hU.high hnd
  have hxG : cslotAddr (pp.bv, idx) ∈ Z.G.chains.flatten := (hM.members _).2 ⟨hAs.isSlot, _, hcap, by simp⟩
  obtain ⟨k1, k2, -⟩ := J.jcov.ks _ hxG p sb fiv (capV_of_capAt hcap)
  obtain ⟨Q0, R0, hcq, -⟩ := J.xtop.fin.1.1.1.lists
  have hcC : Z.c ∈ Cs := hcq.cur ▸ J.kern.cpuCs
  have k2c := k2 Z.c hcC
  obtain ⟨Tr, Cq, hJp⟩ := J.jpl
  have hwb : ∀ q ∈ (winSet (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat (2 ^ (zOf nt.val us.val)) win.val), p.val + fiv.val ≤ q.val ∧ q.val + 2 ^ (zOf nt.val us.val) ≤ p.val + 2 ^ sb.val ∧ q.val % 2 ^ (zOf nt.val us.val) = 0 := by
    intro q hq
    obtain ⟨b1, b2, b3⟩ := winSet_bd hq
    exact ⟨by omega, by omega, b3 hA2⟩
  have hreg : ∀ q ∈ (winSet (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat (2 ^ (zOf nt.val us.val)) win.val), q.bv ∈ regionPtrs (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
      (windowSlots dest r off.val win.val).length (2 ^ Fl4Spec.fl4ObjBitsApi t us.val) := by
    intro q hq
    obtain ⟨j, hj, e⟩ := hq
    rw [hlen, hb]
    unfold regionPtrs
    refine List.mem_map.2 ⟨j, List.mem_range.2 hj, ?_⟩
    have hjk : (j + 1) * 2 ^ (zOf nt.val us.val) ≤ win.val * 2 ^ (zOf nt.val us.val) := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at hjk
    have := Nat.one_le_two_pow (n := zOf nt.val us.val)
    apply BitVec.eq_of_toNat_eq
    beta_reduce
    rw [ptrAdd_toNat (rb := Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) (n := j * 2 ^ (zOf nt.val us.val))
      (by omega)]
    simp only [UScalar.bv_toNat]
    omega
  have hspec : ∀ q ∈ (winSet (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat (2 ^ (zOf nt.val us.val)) win.val), σ'.kheap q.bv = some (oo q.bv) := by
    intro q hq
    have hB := (hA.new _ (by rw [← ht]; exact hreg q hq)).2
    rcases hkc q.bv with e | ⟨r0, cs, cs', e1, -⟩
    · exact e.trans hB
    · have e2 := hB.symm.trans e1
      obtain ⟨pt, e'⟩ := hpm _ (by rw [← ht]; exact hreg q hq)
      rw [e'] at e2; cases e2
  have hsc : ∀ (q : U64) y n, σ'.kheap q.bv = some (.schedContext y n) →
      ∃ ko, σ.kheap q.bv = some ko ∧ Fl4Spec.objBits ko = n + Fl4Spec.minSchedContextBits := by
    intro q y n hq
    have hBk : σB.kheap q.bv = some (.schedContext y n) := by
      rcases hkc q.bv with e | ⟨r0, cs, cs', -, e2⟩
      · exact e.symm.trans hq
      · have e3 := e2.symm.trans hq; cases e3
    by_cases hWq : q.bv ∈ regionPtrs (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
        (windowSlots dest r off.val win.val).length (2 ^ Fl4Spec.fl4ObjBitsApi (.archObject .pml4Obj) us.val)
    · rw [(hA.new _ hWq).2] at hBk
      obtain ⟨pt, e'⟩ := hpm _ hWq
      rw [e'] at hBk; cases hBk
    · rw [hA.old _ hWq] at hBk
      obtain ⟨ko, hko, hty⟩ := hksz _ _ hBk
      exact ⟨ko, hko, objBits_of_aType_sc hty⟩
  have hfr0 := J.free_noObj hAs hcap hBF hksR hsc
  have hTT : ∀ q ∈ (winSet (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat (2 ^ (zOf nt.val us.val)) win.val), ∀ t0 ∈ Z.T, t0.val + 4096 ≤ q.val ∨ q.val + 2 ^ (zOf nt.val us.val) ≤ t0.val := by
    intro q hq t0 ht0
    have hth : Z.th t0 = some .tcb := (hJp.tcb t0).2 (J.zH.1 t0 ht0)
    have := hU.free t0 .tcb hth
    obtain ⟨b1, b2, -⟩ := hwb q hq
    simp only [objSize] at this; omega
  have hpos : 0 < 2 ^ (zOf nt.val us.val) := Nat.two_pow_pos _
  -- the window, with short names
  have hwv : w = win.val := by rw [ew, hlen]
  have hkv : k = 2 ^ zOf nt.val us.val := by rw [ek, hb]
  subst hwv hkv
  replace hE : RetExp Z.th Z.th (L.mem s) (L.mem res.2.1) Z.G G' Aw (2 ^ zOf nt.val us.val) win.val dslot cj
      (cslotAddr (pp.bv, idx)) := hE
  rw [← eA] at hwb hreg hspec hTT hA1 hA2 hA3
  -- `XTopAt` after (`XTopAt.addStepW`: the window's words read by no relation)
  have hsc1 : ∀ (q : U64) y n, σ1.kheap q.bv = some (.schedContext y n) →
      ∃ ko, σ.kheap q.bv = some ko ∧ Fl4Spec.objBits ko = n + Fl4Spec.minSchedContextBits := by
    intro q y n hq
    obtain ⟨ko, hko, hty'⟩ := hksz _ _ hq
    exact ⟨ko, hko, objBits_of_aType_sc hty'⟩
  have hfr1 := J.free_noObj hAs hcap hBF hks1 hsc1
  have hX' := XTopAt.addStepW J1.xtop hw
    (fun b ⟨g1, g2⟩ => hfr1 b (by omega) (by omega))
    (fun b ⟨g1, g2⟩ => by rw [hks1]; rcases k1 with h | h <;> omega)
    hA ho hcnk hkc ⟨hR', hV', hM', hC', hI'⟩ (hFin hFI0)
    (by rw [hks1]; exact hSt.okv hMO0) hTS
  -- no set grows (the new PML4s are in none of the sets)
  obtain ⟨En, Nn, Rn, hXZ, hEs, hNs, hRs, hEt, hNt, hRt, hWEN⟩ : ∃ En Nn Rn : Set U64,
      XTopAt (L := L) AR { Z with G := G', E := Z.E ∪ En, N := Z.N ∪ Nn, R := Z.R ∪ Rn } res.2.1 ar σ' ∧
      En ⊆ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧ Nn ⊆ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧
      Rn ⊆ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧
      (∀ e ∈ En, nt.val = 2) ∧ (∀ n ∈ Nn, nt.val = 3) ∧ (∀ r ∈ Rn, nt.val = 6) ∧
      ∀ q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val, q ∈ En ∨ q ∈ Nn ∨ q ∈ Rn ∨ nt.val = 8 := by
    refine ⟨∅, ∅, ∅, ?_, fun _ h => by simp at h, fun _ h => by simp at h, fun _ h => by simp at h,
      fun _ h => by simp at h, fun _ h => by simp at h, fun _ h => by simp at h, fun _ _ => Or.inr (Or.inr (Or.inr hnt))⟩
    simp only [Set.union_empty]
    exact hX'
  -- the spec side
  have hdet : ∀ σx, Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σx)}, False) → σx = σ1 :=
    fun σx h => by
      have e := congrArg Prod.fst (h.symm.trans hst1)
      simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at e
      exact e
  obtain ⟨hcdtK, horgK⟩ := invokeUntyped_noreset_coP Fl4Spec.fl4ObjBitsApi (pp.bv, idx) p.bv _ us.val
    (windowSlots dest r off.val win.val) false σ1 {pp.bv, dest.bv} (Or.inl rfl)
    (by
      rintro q (rfl | hq)
      · obtain ⟨cs, h, -⟩ := hSR1.cnode pp rs hpp; exact ⟨rs, cs, h⟩
      · rw [Set.mem_singleton_iff.1 hq]; obtain ⟨cs, h, -⟩ := hSR1.cnode dest r hctx.cnode.1; exact ⟨r, cs, h⟩)
    (fun q hq => by
      have hB := (hA.new q hq).1
      exact hB)
    (fun q hq => hal q hq)
    J1.kern.gpm J1.kern.ga J1.kern.gf (.ok (), σ') (by rw [hrunP]; rfl)
  have hσ1k : ∀ o, o ≠ (L.curW s).bv → σ1.kheap o = σ.kheap o := fun o ho => by
    rw [he1, Notif.stsAct_kheap, Notif.updK_kheap]; exact Function.update_of_ne ho _ _
  have hσ1c : ∃ y, σ1.kheap (L.curW s).bv = some (.tcb y) :=
    ⟨{ x1 with tcbState := .restart }, by rw [he1, Notif.stsAct_kheap, Notif.updK_kheap]; simp⟩
  have hσ1cdt : σ1.cdt = σ.cdt := by rw [he1]; unfold Notif.stsAct; split_ifs <;> rfl
  have hcsc1 : σ1.curSc = σ.curSc := by rw [he1]; unfold Notif.stsAct; split_ifs <;> rfl
  have hisc1 : σ1.idleSc = σ.idleSc := by rw [he1]; unfold Notif.stsAct; split_ifs <;> rfl
  have hC2 := CnStep.of_cnK hcnk
  have hctB : σB.curThread = σ1.curThread := by
    have e := congrArg Fl4Spec.AbstractState.curThread hA.abs; exact e
  have hcscB : σB.curSc = σ1.curSc := by
    have e := congrArg Fl4Spec.AbstractState.curSc hA.abs; exact e
  have hidB : σB.idleThread = σ1.idleThread := by
    have e := congrArg Fl4Spec.AbstractState.idleThread hA.abs; exact e
  have hiscB : σB.idleSc = σ1.idleSc := by
    have e := congrArg Fl4Spec.AbstractState.idleSc hA.abs; exact e
  have hgp' : σ'.archState.x64GlobalPml4 = σ1.archState.x64GlobalPml4 := by
    have e := congrArg (fun z => z.archState.x64GlobalPml4) hcnk.1
    exact e.trans (congrArg (fun a => a.x64GlobalPml4) hA.arch)
  have hao : ∀ q ao, σ1.kheap q = some (.archObj ao) → σ'.kheap q = some (.archObj ao) := fun q ao h => by
    have hB := hA.kold h
    rcases hkc q with e | ⟨r0, cs, cs', e1, -⟩
    · rw [e]; exact hB
    · rw [hB] at e1; cases e1
  -- the window's slots
  have hslA : ∀ d ∈ windowSlots dest r off.val win.val, AbsSlot Z.th d ∧
      ∃ i, off.val ≤ i ∧ i < off.val + win.val ∧ d = (dest.bv, Fl4Spec.natToCref r i) := by
    intro d hd
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hd
    rw [List.mem_range'_1] at hi
    refine ⟨⟨dest, rfl, Or.inl ?_⟩, i, hi.1, hi.2, rfl⟩
    rw [natToCref_length _ _ (by have := hctx.cnode.2.1; omega)]; exact hctx.cnode.1
  have horig : ∀ sl, σ'.isOriginalCap sl = true → σ1.isOriginalCap sl = true ∨ AbsSlot Z.th sl := fun sl h => by
    by_cases hs : sl ∈ windowSlots dest r off.val win.val
    · exact Or.inr (hslA sl hs).1
    · exact Or.inl (by rw [← horgK sl hs]; exact h)
  -- FL4's writes: inside slots
  have hwI : P1.WritesIn st s1 res.2.1 (fun b => InSlot Z.th b ∨
      (Aw ≤ b.val ∧ b.val < Aw + win.val * 2 ^ zOf nt.val us.val)) := ⟨hW.1, hW.2.1, fun b hb hn => hW.2.2 b hb (fun h => hn (by
    rcases h with (⟨h1, -⟩ | h) | ⟨-, h⟩
    · exact absurd h1 htT
    · exact Or.inl h
    · exact Or.inr h))⟩
  have hidl1 : IdleKeep (L := L) s s1 := J.idleW_keep J1.xtop.fin.1.1.1 hid1 hisc1
  have hidl2 : IdleKeep (L := L) s1 res.2.1 :=
    J1.idleW_keep hX'.fin.1.1.1 (hC2.idle.trans hidB) (hC2.isc.trans hiscB)
  have hidl : IdleKeep (L := L) s res.2.1 := hidl1.trans hidl2
  -- P1's creation: the heap after, `BlkOK`, `JCovD`
  have hcjU : ∀ j, j < win.val → isUt (cj j) = false := by
    intro j _; rw [hcj]; simp [cjOf, newCapOf, hnt, isUt]
  obtain ⟨H', Ac', hblk', hout, hjc'⟩ := J.create_noresetW hni J1 hs1 hct1 hcsc1 hid1 hisc1 hns1 hRU hpp hidx hcap hE
    (fun _ => hcjU) ⟨by omega, fun h => absurd h (by omega)⟩ (k := 2 ^ zOf nt.val us.val) rfl hAk htT hW
    (fun hz => absurd (by simp [newKind, hnt]) (hz 12)) hidl
  -- `JPlaced` after
  have hcap1 : capAt (L.mem s1) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fiv false) :=
    (hSS1.capAt hAs.isSlot).trans hcap
  have hg1 : Fl4Spec.getCap (Z := Unit) (pp.bv, idx) σ1 = ({(.untypedCap false p.bv sb.val fiv.val, σ1)}, False) := by
    obtain ⟨c, a, hc, hca, hg⟩ := J1.xtop.rel.2.1.1.slot_cap (sl := (pp.bv, idx)) (p := pp) rfl
      (by simpa [hidx] using hpp)
    rw [hcap1] at hc; have := eq_of_ok_eq hc; subst this
    rw [hg, hca.abs]; rfl
  have hgc : ∀ σx, Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σx)}, False) →
      ∀ y ∈ ((Fl4Spec.invokeUntypedWith (Z := Unit) Fl4Spec.fl4ObjBitsApi (.retype (pp.bv, idx) false p.bv
        (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val)
        false)).run σx).1,
      ∀ o sz cs y0 n0, σ.kheap o = some (.cnode sz cs) → ¬ Fl4Spec.wellFormedCnodeN sz cs →
        y.2.kheap o ≠ some (.schedContext y0 n0) := by
    intro σx hx y hy o sz cs y0 n0 h0 _ hk
    rw [hdet σx hx, hrun] at hy
    obtain rfl := Set.mem_singleton_iff.1 hy
    dsimp only at hk
    have hk' : σB.kheap o = some (.schedContext y0 n0) := by
      rcases hkc o with e | ⟨r0, cs0, cs', -, e2⟩
      · exact e.symm.trans hk
      · rw [e2] at hk; cases hk
    rcases hA.kback hk' with h1 | ⟨hW', h2⟩
    · by_cases ho : o = (L.curW s).bv
      · subst ho; obtain ⟨y1, hy1⟩ := hσ1c; rw [hy1] at h1; cases h1
      · rw [hσ1k o ho, h0] at h1; cases h1
    · obtain ⟨pt, e'⟩ := hpm _ hW'
      rw [e'] at h2; cases h2
  have hn1 : nt.val ≠ 1 := by omega
  obtain ⟨th2, σ2, A2, k2', w2, lo2, hi2, eA2, ek2, ew2, -, -, hor2, ⟨σ12, hst12, hhas2⟩, hthx2, hJP2⟩ :=
    Sched.JPlaced.retype (L := L) hJp J.jcov J.ut hI hM hRPN hok nt.val hty (by omega)
      (fun kd h => by rw [newKind_bits h, hb]) (fun kd h => by rw [newKind_bits h]; have := hctx.size.2.1; omega)
      (fun z h => by simp [newKind, hnt] at h) (fun h => absurd h hn1) (fun h => absurd h hn1)
      J.kern.ksbAl J.kern.nodeFit (fun ct h => by rw [hc2] at h; cases eq_of_ok_eq h; exact J.kern.curT) J.intL
      J.sfree hgc (capV_of_capAt hcap) rfl (fun σx hx => by rw [hdet σx hx]; exact hg1)
      (fun _ => by rw [← eA]; exact hA1) (fun h => rfl) hidl.2
  have e1' : Aw = A2 := eA.trans eA2.symm
  have e2' : k2' = 2 ^ zOf nt.val us.val := by rw [ek2, hb]
  have e3' : w2 = win.val := by rw [ew2, hlen]
  subst e1' e2' e3'
  have hlohi : Aw = lo2 ∧ Aw + win.val * 2 ^ zOf nt.val us.val = hi2 := by
    rcases hor2 with h | ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hRB⟩
    · exact ⟨h.1.symm, h.2.symm⟩
    · cases hRB
  obtain ⟨rfl, rfl⟩ := hlohi
  have hth2 : th2 = Z.th := funext fun q => by rw [(hthx2 rfl).1 q, hk0]; simp
  subst hth2
  obtain ⟨y2, hy2, -, hKS⟩ := hhas2
  rw [hdet σ12 hst12, hrun] at hy2
  obtain rfl := Set.mem_singleton_iff.1 hy2
  have hJPa := (hJP2 H' hout).of_kheap hKS.1
  -- `JKern` after
  have hWd : ¬ (Aw ≤ (L.nodeAt s1 0#u64 layout.node.DEBUG_TCBS).val ∧
      (L.nodeAt s1 0#u64 layout.node.DEBUG_TCBS).val < Aw + win.val * 2 ^ zOf nt.val us.val) := by
    rw [P1.nodeAt_of_ksb hks1]
    rintro ⟨g1, g2⟩
    exact hU.dwReg hnd ⟨by omega, by omega⟩
  have hDbg : L.mem res.2.1 (L.nodeAt s1 0#u64 layout.node.DEBUG_TCBS) =
      L.mem s1 (L.nodeAt s1 0#u64 layout.node.DEBUG_TCBS) :=
    hwI.mem_eq J1.kern.dwAl fun h => h.elim (fun ⟨x, hx, h1, h2⟩ => J1.kern.dwObj x hx ⟨h1, h2⟩) hWd
  have K1 := J1.kern_keep (D' := {q | q ∈ D ∧ ¬ NewQ Aw (2 ^ zOf nt.val us.val) win.val cj q}) hwI.1 hwI.2.1
    hX'.fin.1.1.1 (hC2.ct.trans hctB) (hC2.csc.trans hcscB) horig hgp' hao hDbg
  have hRD := (retype_window_dead J.jcov J.ut hI hE ⟨p, sb, fiv, capV_of_capAt hcap⟩).1
  have hoffD : ∀ q kd, H q = some kd → q ∉ D → H' q = some kd := fun q kd hq hqD =>
    hout_old hout rfl rfl hE.k1 hq (by
      by_contra hm
      exact hqD (hRD q kd hq (by unfold MeetsW; omega)).1)
  have hres : σ.schedulerAction ≠ .chooseNewThread := by rw [hni.2]; simp
  have hcs1 : L.cscW s1 = L.cscW s :=
    cscW_of_sched J.xtop.fin.1.1.1 J1.xtop.fin.1.1.1 hk1 hcpu1 hcsc1
  have hcsR : L.cscW res.2.1 = L.cscW s1 :=
    cscW_of_sched J1.xtop.fin.1.1.1 hX'.fin.1.1.1 hwI.1 hwI.2.1 (hC2.csc.trans hcscB)
  have hcscH : H' (L.cscW res.2.1) ≠ none := by
    rw [hcsR, hcs1]
    obtain ⟨kd, hkd⟩ := Option.ne_none_iff_exists'.1 J.kern.cscH
    rw [hoffD _ kd hkd (J.cscLive.resolve_right hres)]; simp
  have hcurR : (L.curW res.2.1).val + 2 ^ 12 ≤ Aw ∨ Aw + win.val * 2 ^ zOf nt.val us.val ≤ (L.curW res.2.1).val := by
    have := hU.free _ .tcb K1.curT; simp only [objSize] at this; omega
  have hnewK : ∀ q kd, NewAt Aw (2 ^ zOf nt.val us.val) win.val q → newKind nt.val us.val = some kd →
      (q.val + 2 ^ kd.bits ≤ (L.ksb res.2.1).val ∨ (L.ksb res.2.1).val + 13568 ≤ q.val) ∧
      ∀ c ∈ Cs, q.val + 2 ^ kd.bits ≤ L.nodeBase res.2.1 c ∨ L.nodeBase res.2.1 c + 4288 ≤ q.val := by
    intro q kd hq hK
    obtain ⟨j, hj, hqv⟩ := hq
    have hjk : (j + 1) * 2 ^ zOf nt.val us.val ≤ win.val * 2 ^ zOf nt.val us.val := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at hjk
    have hbk : 2 ^ kd.bits = 2 ^ zOf nt.val us.val := by rw [newKind_bits hK]
    have hnb : ∀ c, L.nodeBase res.2.1 c = L.nodeBase s c := fun c => by
      simp only [P1.LawfulStore.nodeBase, hksR]
    refine ⟨?_, fun c hc => ?_⟩
    · rw [hksR, hbk]; rcases k1 with h | h <;> omega
    · rw [hnb, hbk]; rcases k2 c hc with h | h <;> omega
  have hA0 : 0 < Aw := by omega
  have K2 := K1.hout (D' := {q | q ∈ D ∧ ¬ NewQ Aw (2 ^ zOf nt.val us.val) win.val cj q}) hJPa.heap hout hE.k1 hA0 hnewK hcurR hcscH
  -- the untyped caps' facts after
  obtain ⟨-, p0, sb0, fi0, fi1, d0, e0, e1u, -, hAf1, -, -, -⟩ := hE.usrc
  rw [capV_of_capAt hcap] at e0
  simp only [capability.Cap.Untyped.injEq] at e0
  obtain ⟨hp0, hsb0, hfi0, hd0⟩ := e0
  subst p0 sb0 fi0 d0
  have hsrcG' : cslotAddr (pp.bv, idx) ∈ G'.chains.flatten :=
    (hM'.members _).2 ⟨hAs.isSlot, _, capAt_capV _ _, by rw [e1u]; simp⟩
  have hfi1 : fi1.val ≤ 2 ^ sb.val := hU'.fib _ hsrcG' p sb fi1 false e1u
  have hDn0 : ∀ d ∈ windowSlots dest r off.val win.val, capAt (L.mem s) (cslotAddr d) = ok .Null := by
    intro d hd
    obtain ⟨-, i, h1, h2, rfl⟩ := hslA d hd
    rw [cslotAddr_natToCref _ _ _ (by have := hctx.cnode.2.1; omega) (by have := hctx.window.2.2; omega)]
    exact hctx.empty i h1 h2
  have hnull0 : ∀ d ∈ windowSlots dest r off.val win.val, cslotAddr d ∉ Z.G.chains.flatten := fun d hd h => by
    obtain ⟨-, c0, h0, hn⟩ := (hM.members _).1 h
    rw [hDn0 d hd] at h0; exact hn (eq_of_ok_eq h0).symm
  have hDu : ∀ d ∈ windowSlots dest r off.val win.val, ∀ p1 sb1 fi2 dv,
      capV (L.mem res.2.1) (cslotAddr d) ≠ .Untyped p1 sb1 fi2 dv := by
    intro d hd p1 sb1 fi2 dv e
    have hm : cslotAddr d ∈ G'.chains.flatten :=
      (hM'.members _).2 ⟨(hslA d hd).1.isSlot, _, capAt_capV _ _, by rw [e]; simp⟩
    rcases hE.gmem _ hm with h0 | ⟨j, hj, ej⟩
    · exact hnull0 d hd h0
    · rw [ej] at e
      have h3 := (hE.newc j hj).symm.trans e
      have h2 := hcjU j hj
      rw [h3, isUt_untyped] at h2; cases h2
  have hcapK : ∀ y, IsSlot Z.th y → y ≠ cslotAddr (pp.bv, idx) →
      (∀ d ∈ windowSlots dest r off.val win.val, y ≠ cslotAddr d) →
      capV (L.mem res.2.1) y = capV (L.mem s1) y := by
    intro y hy hyx hyd
    have e1 : capV (L.mem s1) y = capV (L.mem s) y := by
      have := hSS1.capAt hy; rw [capAt_capV, capAt_capV] at this; exact eq_of_ok_eq this
    rw [e1]
    by_cases hyG : y ∈ Z.G.chains.flatten
    · cases hu : isUt (capV (L.mem s) y)
      · exact (hE.keep y hyG hu).2
      · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h5⟩ := hE.usrc
        exact h5 y hyG hu hyx
    · have h0 : capV (L.mem s) y = .Null := by
        by_contra hn
        exact hyG ((hM.members y).2 ⟨hy, _, capAt_capV _ _, hn⟩)
      rw [h0]
      by_contra hn
      have hm : y ∈ G'.chains.flatten := (hM'.members y).2 ⟨hy, _, capAt_capV _ _, hn⟩
      rcases hE.gmem y hm with h1 | ⟨j, hj, rfl⟩
      · exact hyG h1
      · have hD : Mdb.Desc G'.par (dslot j) (cslotAddr (pp.bv, idx)) :=
          (hE.desc _ _).2 (Or.inr ⟨j, hj, rfl, Or.inl rfl⟩)
        obtain ⟨b, hb1, -⟩ := Relation.TransGen.head'_iff.1 hD
        obtain ⟨d, hdA, hdy⟩ := hC'.par_slot _ _ hb1
        have hcd := hC'.cdt d hdA
        rw [hdy, hb1] at hcd
        by_cases hdW : d ∈ windowSlots dest r off.val win.val
        · exact hyd d hdW hdy.symm
        · rw [hcdtK d hdW, hσ1cdt] at hcd
          have hcd0 := hC.cdt d hdA
          rw [hdy, hcd] at hcd0
          exact hyG (hM.tree.par_mem _ _ hcd0.symm).1
  have hDL : DestLive Z.th (L.mem s1) (L.ksb s1) dest := by
    obtain ⟨-, -, -, y, rr, gs, g, hy, hcy⟩ := hctx.cnode
    exact DestLive.same (Or.inl ⟨y, rr, gs, g, hy, capV_of_capAt hcy⟩) hSS1 hk1
  have hutc := J1.ret_utcW (G' := G') hAs (capV_of_capAt hcap1) e1u (by omega) hfi1
    (· ∈ windowSlots dest r off.val win.val) (fun d hd => (hslA d hd).1)
    (fun d hd => (hSS1.capAt (hslA d hd).1.isSlot).trans (hDn0 d hd)) hDu hcapK hwI
    (fun b ⟨_, g2⟩ => by omega)
    (fun sl1 p1 sb1 fi2 hsl1 hne hcv1 b ⟨g1, g2⟩ => by
      have hm1 : cslotAddr sl1 ∈ Z.G.chains.flatten :=
        (J1.xtop.rel.2.1.2.2.1.members _).2 ⟨hsl1.isSlot, _, capAt_capV _ _, by rw [hcv1]; simp⟩
      have hs1G : cslotAddr (pp.bv, idx) ∈ Z.G.chains.flatten :=
        (J1.xtop.rel.2.1.2.2.1.members _).2 ⟨hAs.isSlot, _, hcap1, by simp⟩
      exact ut_free_other J1.ut hm1 hs1G hne hcv1 (capV_of_capAt hcap1) (b := b.val) (by omega) (by omega))
    hWd hcdtK horgK hgp' hM'
    (RetExp.src_child hE hctx.window.1 hP' hC' hAs)
    (fun d hd sl p1 sb1 fi2 dev hsl hcv hdv hnc => by
      obtain ⟨-, i, -, -, rfl⟩ := hslA d hd
      exact J1.live_slot arI hsl hcv hdv hnc ⟨dest, r, rfl, hctx.cnode.1,
        natToCref_length _ _ (by have := hctx.cnode.2.1; omega), hDL⟩)
  -- the spec's invariants and the call stacks (`uaRest`, `addRP`)
  have hIN : IdleNew (fun q => q ∈ regionPtrs (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
      (windowSlots dest r off.val win.val).length (2 ^ Fl4Spec.fl4ObjBitsApi (.archObject .pml4Obj) us.val))
      oo := fun q hq => by
    obtain ⟨pt, e⟩ := hpm q hq
    exact Or.inr (Or.inr (Or.inr ⟨_, e⟩))
  have hWnN : ∀ n ∈ Nn, n.bv ∈ regionPtrs (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
      (windowSlots dest r off.val win.val).length (2 ^ Fl4Spec.fl4ObjBitsApi (.archObject .pml4Obj) us.val) :=
    fun n hn => by rw [← ht]; exact hreg n (hNs hn)
  -- the window's words apart from the scheduler's (`T`, `C`'s SCs, `R`)
  have hWT : ∀ b : U64, (Aw ≤ b.val ∧ b.val < Aw + win.val * 2 ^ zOf nt.val us.val) → ∀ t0 ∈ Z.T,
      b.val < t0.val ∨ t0.val + 4096 ≤ b.val := by
    rintro b ⟨g1, g2⟩ t0 ht0
    have hth : Z.th t0 = some .tcb := (hJp.tcb t0).2 (J.zH.1 t0 ht0)
    have := hU.free t0 .tcb hth
    simp only [objSize] at this; omega
  have hspec1' : ∀ o ko, σ1.kheap o = some ko →
      o.toNat + 2 ^ Fl4Spec.objBits ko ≤ p.val + fiv.val ∨ p.val + 2 ^ sb.val ≤ o.toNat := by
    intro o ko hk
    rcases J1.sfree _ hxG p sb fiv (capV_of_capAt hcap1) o ko hk with (h | h) | ⟨h3, h4⟩
    · left; omega
    · right; exact h
    · left; exact h4
  have hWC : ∀ b : U64, (Aw ≤ b.val ∧ b.val < Aw + win.val * 2 ^ zOf nt.val us.val) → ∀ q ∈ Z.C, ∀ x n,
      σ1.kheap q.bv = some (.schedContext x n) → b.val < q.val ∨ q.val + 2 ^ (n + Fl4Spec.minSchedContextBits) ≤ b.val := by
    rintro b ⟨g1, g2⟩ q hq x n hx
    have := hspec1' _ _ hx
    simp only [Fl4Spec.objBits, UScalar.bv_toNat] at this
    rw [Nat.add_comm n]; omega
  have hWR : ∀ b : U64, (Aw ≤ b.val ∧ b.val < Aw + win.val * 2 ^ zOf nt.val us.val) → ∀ r0 ∈ Z.R,
      b.val < r0.val ∨ r0.val + 32 ≤ b.val := by
    rintro b ⟨g1, g2⟩ r0 hr0
    obtain ⟨x, hx, -⟩ := J1.xtop.ipc.toE.reply r0 hr0
    have := hspec1' _ _ hx
    simp only [Fl4Spec.objBits, Fl4Spec.replyBits, UScalar.bv_toNat] at this; omega
  obtain ⟨hCR1, -, hRF1, hRR1, hY1, hMc1, hBw1, hNSC1, hInv1, hCur1, hOwn1, hOff1, hAct1, hBsa1, hIs1, hCRun1⟩ :=
    J1.uaRestW hwI hWT hWC hWR hA hIN hcnk hWnN
  have hspec1 : ∀ o ko, σ1.kheap o = some ko →
      o.toNat + 2 ^ Fl4Spec.objBits ko ≤ p.val + fiv.val ∨ p.val + 2 ^ sb.val ≤ o.toNat := by
    intro o ko hk
    rcases J1.sfree _ hxG p sb fiv (capV_of_capAt hcap1) o ko hk with (h | h) | ⟨h3, h4⟩
    · left; omega
    · right; exact h
    · left; exact h4
  have hNw0 : ∀ n ∈ Nn, n.val % 64 = 0 ∧ p.val + fiv.val ≤ n.val ∧ n.val + 64 ≤ p.val + 2 ^ sb.val ∧
      NewAt Aw (2 ^ zOf nt.val us.val) win.val n ∧ newKind nt.val us.val = some .ntfn := by
    intro n hn
    have h3 := hNt n hn
    have h64 : (2 : Nat) ^ zOf nt.val us.val = 64 := by simp [zOf, h3]
    obtain ⟨b1, b2, b3⟩ := hwb n (hNs hn)
    rw [h64] at b2 b3
    exact ⟨b3, b1, b2, hNs hn, by simp [newKind, h3]⟩
  have hEw0 : ∀ e ∈ En, e.val % 16 = 0 ∧ p.val + fiv.val ≤ e.val ∧ e.val + 16 ≤ p.val + 2 ^ sb.val ∧
      NewAt Aw (2 ^ zOf nt.val us.val) win.val e ∧ newKind nt.val us.val = some .ep := by
    intro e he
    have h2 := hEt e he
    have h16 : (2 : Nat) ^ zOf nt.val us.val = 16 := by simp [zOf, h2]
    obtain ⟨b1, b2, b3⟩ := hwb e (hEs he)
    rw [h16] at b2 b3
    exact ⟨b3, b1, b2, hEs he, by simp [newKind, h2]⟩
  have hRw0 : ∀ r ∈ Rn, r.val % 32 = 0 ∧ p.val + fiv.val ≤ r.val ∧ r.val + 32 ≤ p.val + 2 ^ sb.val ∧
      NewAt Aw (2 ^ zOf nt.val us.val) win.val r ∧ newKind nt.val us.val = some .reply := by
    intro r hr
    have h6 := hRt r hr
    have h32 : (2 : Nat) ^ zOf nt.val us.val = 32 := by simp [zOf, h6]
    obtain ⟨b1, b2, b3⟩ := hwb r (hRs hr)
    rw [h32] at b2 b3
    exact ⟨b3, b1, b2, hRs hr, by simp [newKind, h6]⟩
  -- the new replies: free, zero links, not old ones
  have hkR : ∀ r ∈ Rn, σ'.kheap r.bv = some (.reply Fl4Spec.defaultReply) := by
    intro r hr
    exfalso; have := hRt r hr; omega
  have hRz : ∀ r ∈ Rn, L.mem res.2.1 (P1.rNextA r) = 0#u64 ∧ L.mem res.2.1 (P1.rPrevA r) = 0#u64 := by
    intro r hr
    exfalso; have := hRt r hr; omega
  have hRn : ∀ r ∈ Rn, r ∉ Z.R := by
    intro r hr hrR
    obtain ⟨x, hx, -⟩ := J1.xtop.ipc.toE.reply r hrR
    have := hspec1 _ _ hx
    obtain ⟨-, b1, b2, -⟩ := hRw0 r hr
    simp only [Fl4Spec.objBits, Fl4Spec.replyBits, UScalar.bv_toNat] at this; omega
  have hnb0 : L.nodeBase s Z.c = (L.ksb s).val + 13568 := by
    unfold P1.LawfulStore.nodeBase; rw [hc0]; simp
  have hRks : ∀ r ∈ Rn, r.val + 32 ≤ (L.ksb res.2.1).val ∨ L.nodeBase res.2.1 Z.c + 4288 ≤ r.val := by
    intro r hr
    obtain ⟨-, b1, b2, -⟩ := hRw0 r hr
    have k2' := k2c
    rw [hnb0] at k2'
    rw [hnbR, hnb0, hksR]
    rcases k1 with h | h <;> rcases k2' with h' | h' <;> omega
  have hNR : Nn = ∅ ∨ Rn = ∅ := by
    rcases Set.eq_empty_or_nonempty Nn with h | ⟨n, hn⟩
    · exact Or.inl h
    · refine Or.inr (Set.ext fun r => ⟨fun hr => ?_, fun h => False.elim h⟩)
      exfalso; have := hNt n hn; have := hRt r hr; omega
  obtain ⟨hRP1, hSA1⟩ := J1.addRPW hwI hWT hWC hWR hA hIN hcnk hWnN (by omega) hU.pfit hU.free hspec1
    (fun n hn => ⟨(hNw0 n hn).2.1, (hNw0 n hn).2.2.1⟩) (fun r hr => ⟨(hRw0 r hr).1, (hRw0 r hr).2.1,
      (hRw0 r hr).2.2.1⟩) hRks hNR
  -- the set and heap fields (`addSets`)
  have hKn : ∀ q, NewAt Aw (2 ^ zOf nt.val us.val) win.val q → ∀ kd, newKind nt.val us.val = some kd →
      (kd = .ep ∧ q ∈ En) ∨ (kd = .ntfn ∧ q ∈ Nn) ∨ (kd = .reply ∧ q ∈ Rn) ∨ ∃ m, kd = .other m := by
    intro q hq kd hK
    rcases hWEN q hq with h | h | h | ha
    · have h2 := hEt q h; simp [newKind, h2] at hK; exact Or.inl ⟨hK.symm, h⟩
    · have h3 := hNt q h; simp [newKind, h3] at hK; exact Or.inr (Or.inl ⟨hK.symm, h⟩)
    · have h6 := hRt q h; simp [newKind, h6] at hK; exact Or.inr (Or.inr (Or.inl ⟨hK.symm, h⟩))
    · refine Or.inr (Or.inr (Or.inr ⟨12, ?_⟩))
      simp [newKind, ha] at hK; first | exact hK.symm | exact hK
  have hrev : ∀ o, o ∈ regionPtrs (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
      (windowSlots dest r off.val win.val).length (2 ^ Fl4Spec.fl4ObjBitsApi t us.val) →
      ∃ q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val, q.bv = o := by
    intro o ho
    obtain ⟨j, hj, rfl⟩ := regionPtrs_mem ho
    rw [hlen] at hj
    rw [hb]
    have hjk : (j + 1) * 2 ^ zOf nt.val us.val ≤ win.val * 2 ^ zOf nt.val us.val := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at hjk
    have hfit := hU.pfit
    have := Nat.one_le_two_pow (n := zOf nt.val us.val)
    refine ⟨⟨Fl4Spec.ptrAdd (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) (j * 2 ^ zOf nt.val us.val)⟩,
      ⟨j, hj, ?_⟩, rfl⟩
    show (Fl4Spec.ptrAdd _ _).toNat = _
    rw [ptrAdd_toNat (by omega), ← eA]
  have hback : ∀ o ko, σ'.kheap o = some ko → σ1.kheap o = some ko ∨
      (∃ r cs cs', σ1.kheap o = some (.cnode r cs) ∧ ko = .cnode r cs') ∨
      (∃ e ∈ En, e.bv = o ∧ ko = .endpoint Fl4Spec.defaultEp) ∨
      (∃ n ∈ Nn, n.bv = o ∧ ko = .notification Fl4Spec.defaultNotification) ∨
      (∃ r ∈ Rn, r.bv = o ∧ ko = .reply Fl4Spec.defaultReply) ∨
      (∃ q, NewAt Aw (2 ^ zOf nt.val us.val) win.val q ∧ q.bv = o ∧ (∃ ao, ko = .archObj ao) ∧
        ∃ m, 12 ≤ m ∧ newKind nt.val us.val = some (.other m)) := by
    intro o ko hk
    have hback1 : ∀ ko', σB.kheap o = some ko' → σ1.kheap o = some ko' ∨
        (∃ e ∈ En, e.bv = o ∧ ko' = .endpoint Fl4Spec.defaultEp) ∨
        (∃ n ∈ Nn, n.bv = o ∧ ko' = .notification Fl4Spec.defaultNotification) ∨
        (∃ r ∈ Rn, r.bv = o ∧ ko' = .reply Fl4Spec.defaultReply) ∨
        (∃ q, NewAt Aw (2 ^ zOf nt.val us.val) win.val q ∧ q.bv = o ∧ (∃ ao, ko' = .archObj ao) ∧
        ∃ m, 12 ≤ m ∧ newKind nt.val us.val = some (.other m)) := by
      intro ko' h
      rcases hA.kback h with h1 | ⟨hW', h2⟩
      · exact Or.inl h1
      · obtain ⟨q, hq, hqo⟩ := hrev o (by rw [ht]; exact hW')
        rcases hWEN q hq with hqE | hqN | hqR | ha
        · exfalso; have := hEt q hqE; omega
        · exfalso; have := hNt q hqN; omega
        · exfalso; have := hRt q hqR; omega
        · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨q, hq, hqo, ?_, ⟨12, le_rfl, by simp [newKind, ha]⟩⟩)))
          obtain ⟨pt, e⟩ := hpm o hW'
          exact ⟨_, by rw [h2, e]⟩
    rcases hkc o with e | ⟨r0, cs, cs', e1, e2⟩
    · rcases hback1 ko (e.symm.trans hk) with h1 | h1 | h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inr (Or.inl h1))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h1))))
    · rw [e2] at hk; cases hk
      rcases hback1 _ e1 with h1 | ⟨e, -, -, he⟩ | ⟨n, -, -, hn⟩ | ⟨n, -, -, hn⟩ | ⟨_, -, -, ⟨_, hn⟩, -⟩
      · exact Or.inr (Or.inl ⟨r0, cs, cs', h1, rfl⟩)
      · cases he
      · cases hn
      · cases hn
      · cases hn
  have harch1 : ArchFitHyp H σ1 := fun o ao n h hH => hAF o ao n (by
    by_cases ho : o = (L.curW s).bv
    · subst ho; obtain ⟨y1, hy1⟩ := hσ1c; rw [hy1] at h; cases h
    · rwa [hσ1k o ho] at h) hH
  obtain ⟨hKs', hIp', hnk', hcov', hobj', hzH', hset', hscC'⟩ :=
    J1.addSets (Z' := { Z with G := G', E := Z.E ∪ En, N := Z.N ∪ Nn, R := Z.R ∪ Rn }) hwI.1 (by omega) hU.pfit hU.free
      (by rw [hk1]; rcases k1 with h | h <;> omega) hspec1
      (fun wp hwp => hBF wp hwp _ hxG p sb fiv (capV_of_capAt hcap)) harch1 hA1 hA3 hE.k1 hout hEw0 hNw0 hRw0 hKn
      hback rfl rfl rfl rfl rfl rfl
  -- the CSpace fields (`JCs`)
  have hcjZ : ∀ j, j < win.val → ∀ p1 zt n1, cj j ≠ .Zombie p1 zt n1 := by
    intro j _ p1 zt n1; rw [hcj]; simp [cjOf, newCapOf, hnt]
  have hob : ∀ cd, Fl4Spec.objBits (Fl4Spec.defaultObject t false us.val cd) ≤ Fl4Spec.fl4ObjBitsApi t us.val := by
    intro cd
    rw [ht]; first | exact le_refl _ | decide | simp [Fl4Spec.defaultObject, Fl4Spec.objBits, Fl4Spec.fl4ObjBitsApi]
  have hSF' : SpecFree (L.mem res.2.1) G' σ' := SpecFree.retype J.sfree J.ut hksz (capV_of_capAt hcap) rfl hg1
    (fun _ => by rw [← eA]; exact hA1) (y := (.ok (), σ')) (by rw [hrun]; rfl) rfl hU' hI' hE
    (fun _ => ⟨eA, by rw [hb], by rw [hlen], hRFu hok⟩) hob
  have hCs : JCs (L := L) { Z with G := G', E := Z.E ∪ En, N := Z.N ∪ Nn, R := Z.R ∪ Rn } res.2.1 σ' :=
    JCs.retype rfl rfl J.del hE hM hP' hM' hcjZ (fun _ _ _ h => h) hU' (hFin hFI0).fm hSF'
  -- `JRest` and `JAtZ` after
  have hJR : JRest (L := L) arI { Z with G := G', E := Z.E ∪ En, N := Z.N ∪ Nn, R := Z.R ∪ Rn } H' Cs Ac' Lst1
      {q | q ∈ D ∧ ¬ NewQ Aw (2 ^ zOf nt.val us.val) win.val cj q} res.2.1 σ' :=
    ⟨hCR1.addR hkR hRz hRn, hRF1.addR hCR1 hRz hRn, hRR1.addR hRz, hY1, hMc1, hBw1, hRP1, hSA1, ⟨_, _, hJPa⟩, hjc', K2, hutc, hNSC1, hInv1, hCur1, hOwn1,
      hOff1, hAct1, hBsa1, hIs1, hCRun1, hblk'⟩
  have JZ := J1.add_frame (Z' := { Z with G := G', E := Z.E ∪ En, N := Z.N ∪ Nn, R := Z.R ∪ Rn }) rfl rfl rfl hwI.1 hXZ hCs hJR
    hKs' J1.thT hIp' hnk' hcov' hobj' hzH' hset' hscC'
  refine ⟨σ1, hst1, (.ok [], σ'), perf_ut_mem blk call don hrun, ⟨Z.th, G', Or.inl ⟨hok, rfl⟩, ?_⟩, ?_⟩
  · obtain ⟨hPl, hCR, hFI, hD, hMO, -, -⟩ := hXZ.rel
    exact ⟨hPl, hCR, hFI, hD, hMO⟩
  · rw [if_neg (by rw [hok]; simp), har]
    exact ⟨_, H', Cs, Ac', Lst1, _, JZ⟩


end

end

end Fl4Proofs.P3
