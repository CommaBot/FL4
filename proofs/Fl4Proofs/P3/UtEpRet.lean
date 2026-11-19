/-
P3 (DESIGN.md §9), untyped: **the no-reset retype of endpoints or
notifications at `J`** (handoff/utj.md "Round 4c"): FL4's restart and
`untyped::retype` from a CNode slot's RAM untyped cap, without a reset
(the cap has a child), of endpoints (type 2) or notifications (type 3),
end in XTopJointUt's `UtRetPostJ`: the spec's outcome related, with
`JAtZ` after at the sets grown by the window's objects (`E` or `N`), P1's
heap after the creation (`HOut`) and the dead set without the new objects.

* `perf_ut_mem`: the spec's `fl4PerformInvocation` of an untyped
  invocation returns `[]` after `invoke_untyped`.
* `cscW_of_sched`: the current SC word kept when the spec's current SC is.
* `JAtZ.utEpJ`: the step. Its J premises: `BufObjHyp` [J] (every IPC-buffer
  word inside a spec object), `ArchFitHyp` [J] (UtEpSets: `H`'s object at a
  spec arch object no larger than it) and `RegionUnrefJ` [J] (ScJoint: the
  kept objects and FL4's debug and timer lists name no dead object of the
  window). The fields after: `XTopAt` (as `JAtZ.utEpXTop`), `JCs`
  (`JCs.retype`), `JRest` (`JAtZ.uaRest`, `JAtZ.addRP`, `JPlaced.retype`,
  `JAtZ.create_noreset`, `JKern.hout`, `JAtZ.ret_utc`), the sets and heap
  (`JAtZ.addSets`), put together by `JAtZ.add_frame`.
-/
import Fl4Proofs.P3.UtEpJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

/-- The spec's `fl4PerformInvocation` of an untyped invocation: `[]` after
`invoke_untyped`'s outcome. -/
theorem perf_ut_mem {σ1 σ' : Fl4Spec.State Unit} {inv : Fl4Spec.UntypedInvocation} (blk call don : Bool)
    (h : (Fl4Spec.invokeUntypedWith (Z := Unit) Fl4Spec.fl4ObjBitsApi inv).run σ1 = ({(.ok (), σ')}, False)) :
    ((.ok [], σ') : Except Unit (List Fl4Spec.Data) × Fl4Spec.State Unit) ∈
      ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeUntyped inv)).run σ1).1 :=
  mem_bindE_ok (mem_of_run h) (mem_returnOk [])

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- The current SC word is kept by a step keeping the kernel-state base,
the core and the spec's current SC (`SchedRel`'s lists). -/
theorem cscW_of_sched {N T C : Set U64} {c : U64} {s s' : S} {σ σ' : Fl4Spec.State Unit}
    (hS : Sched.SchedRel st N T C c s σ) (hS' : Sched.SchedRel st N T C c s' σ')
    (hks : L.ksb s' = L.ksb s) (hcpu : L.cpu s' = L.cpu s) (hcsc : σ'.curSc = σ.curSc) : L.cscW s' = L.cscW s := by
  have hna : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨Q', R', hc', hs'⟩ := hS'.lists
  apply P1.eq_of_bv
  have h1 := hs'.curSc; have h2 := hs.curSc
  unfold P1.LawfulStore.cscW P1.LawfulStore.nodeA
  rw [hcpu, hna, hc.cur]
  unfold nodeW at h1 h2
  rw [hna] at h1
  rw [← h1, ← h2, hcsc]

set_option maxHeartbeats 16000000 in
/-- **The no-reset retype of endpoints or notifications at `J`** (module
docstring): from `JAtZ` at the decode (no reschedule pending), the decoded
arguments (`RetCtx`, no reset: the source cap has a child), the source a
CNode slot's RAM untyped cap, FL4's restart and `untyped::retype` end in
`UtRetPostJ` (done, `JAt` after). -/
theorem JAtZ.utEpJ {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) {ct : U64} (hct : sched.cur_thread st s = ok ct) {pp : U64} {rs : Nat} {idx : List Bool}
    (hpp : Z.th pp = some (.cnode rs)) (hidx : idx.length = rs) {p sb fi : U64}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false))
    {nt us dest off win : U64} {t : Fl4Spec.ApiObjectType} {r : Nat} {fiv : U64}
    (hnt : nt.val = 2 ∨ nt.val = 3)
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
  have ht : t = .endpointObject ∨ t = .notificationObject := by
    rcases hnt with h | h <;> rw [h] at hty <;> simp [objTypeOf] at hty <;> simp [hty]
  have htU : t ≠ .untyped := by rcases ht with rfl | rfl <;> simp
  have htP : t ≠ .archObject .pml4Obj := by rcases ht with rfl | rfl <;> simp
  have htT : t ≠ .tcbObject := by rcases ht with rfl | rfl <;> simp
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
  obtain ⟨hA1, hA2, hA3, -⟩ := retype_region p fiv sb.val (zOf nt.val us.val) win.val hsb (by rcases hnt with h | h <;>
    simp [zOf, h]) hU.pal hU.pfit hU.fiLe hctx.window.1 hctx.memory
  refine WP.spec_mono (retype_cont_all (L := L) arI ar Z.th s σ Z.G hSR hV hP hM hC hI J.ut J.kern.orig (L.curW s)
    J.kern.cur hct J.kern.curT J.kern.act hpp hidx hcap hU.pal hU.pfit hU.fiLe (hU.high hnd)
    (fun h => (hU.actZ hnd) ⟨by omega, h.2⟩) hU.free (hU.zero hnd) hunused Fl4Spec.fl4ObjBitsApi nt us dest off win t r
    false fiv (by omega) hb J.kern.dwAl J.kern.dwObj (fun h => (hU.dwReg hnd) ⟨by omega, h.2⟩) J.kern.dwNe J.kern.head
    hctx) (fun res hRP => ?_)
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
    rcases ht with rfl | rfl
    · rw [objTypeOf_ep hn0]; rcases hnt with h | h <;> rw [h] at hty <;> simp [objTypeOf] at hty ⊢ <;> omega
    · rw [objTypeOf_ntfn hn0]; rcases hnt with h | h <;> rw [h] at hty <;> simp [objTypeOf] at hty ⊢ <;> omega
  subst hn0v
  have hk0 : thKindN nt.val us.val = none := by
    unfold thKindN; rw [if_neg (by omega), if_neg (by omega)]
  have hth : th' = Z.th := funext fun q => by rw [hThX.1 q, hk0]; simp
  subst hth
  -- FL4's writes: slot words
  have hw : P1.WritesIn st s1 res.2.1 (Sched.SlotWd Z.th) := ⟨hW.1, hW.2.1, fun b hb hn => hW.2.2 b hb (fun h => hn (by
    rcases h with (⟨h1, -⟩ | h) | ⟨h1, -⟩
    · exact absurd h1 htT
    · exact Sched.slotSpan_wd hP hb h
    · exact absurd h1 htP))⟩
  -- the spec's outcome: the window's objects added, then CNodes changed
  have hSR1 := J1.xtop.rel.2.1.1
  have hlen : (windowSlots dest r off.val win.val).length = win.val := by simp [windowSlots]
  obtain ⟨-, σB, hA, hcnk, hkc⟩ := invokeUntyped_noreset_add Fl4Spec.fl4ObjBitsApi (pp.bv, idx) p.bv _ t us.val
    (windowSlots dest r off.val win.val) false σ1 htU htP {pp.bv, dest.bv} (Or.inl rfl)
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
      rw [hb] at hq ⊢
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
    (.ok (), σ') (by rw [hrun]; rfl)
  have ho : ∀ q, q ∈ regionPtrs (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
      (windowSlots dest r off.val win.val).length (2 ^ Fl4Spec.fl4ObjBitsApi t us.val) →
      ∀ x n, Fl4Spec.defaultObject t false us.val σ1.curDomain ≠ .schedContext x n := by
    intro q _ x n; rcases ht with rfl | rfl <;> simp [Fl4Spec.defaultObject]
  have hks1 : L.ksb s1 = L.ksb s := hk1
  have hcjne : ∀ j, j < w → ∀ p b a, cj j ≠ .Pml4 p b a := by
    intro j _ p b a
    rw [hcj]
    rcases hnt with h | h <;> simp [cjOf, newCapOf, h]
  have hTS : ∀ t0, Z.th t0 = some .tcb → ∀ p0 asid, capAt (L.mem res.2.1) (slotOf t0 1) = ok (.Pml4 p0 true asid) →
      capAt (L.mem s1) (slotOf t0 1) = ok (.Pml4 p0 true asid) := by
    intro t0 ht0 p0 asid hc
    have hxs : IsSlot Z.th (slotOf t0 1) := ⟨t0, 1, Or.inr ⟨ht0, by decide⟩, rfl⟩
    rw [hSS1.capAt hxs]
    exact retExp_pml4_back hE hM hM' hcjne hxs hc
  have hX' := XTopAt.addStep J1.xtop hw hA ho hcnk hkc ⟨hR', hV', hM', hC', hI'⟩ (hFin hFI0)
    (by rw [hks1]; exact hSt.okv hMO0) hTS
  -- the window's objects, added to `E` or `N` (`XTopAt.addE`/`addN`)
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
  have hspec : ∀ q ∈ (winSet (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat (2 ^ (zOf nt.val us.val)) win.val), σ'.kheap q.bv = some (Fl4Spec.defaultObject t false us.val σ1.curDomain) := by
    intro q hq
    have hB := (hA.new _ (hreg q hq)).2
    rcases hkc q.bv with e | ⟨r0, cs, cs', e1, -⟩
    · exact e.trans hB
    · have e2 := hB.symm.trans e1
      rcases ht with rfl | rfl <;> simp [Fl4Spec.defaultObject] at e2
  have hsc : ∀ (q : U64) y n, σ'.kheap q.bv = some (.schedContext y n) →
      ∃ ko, σ.kheap q.bv = some ko ∧ Fl4Spec.objBits ko = n + Fl4Spec.minSchedContextBits := by
    intro q y n hq
    have hBk : σB.kheap q.bv = some (.schedContext y n) := by
      rcases hkc q.bv with e | ⟨r0, cs, cs', -, e2⟩
      · exact e.symm.trans hq
      · have e3 := e2.symm.trans hq; cases e3
    by_cases hWq : q.bv ∈ regionPtrs (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
        (windowSlots dest r off.val win.val).length (2 ^ Fl4Spec.fl4ObjBitsApi t us.val)
    · rw [(hA.new _ hWq).2] at hBk
      rcases ht with rfl | rfl <;> simp [Fl4Spec.defaultObject] at hBk
    · rw [hA.old _ hWq] at hBk
      obtain ⟨ko, hko, hty⟩ := hksz _ _ hBk
      exact ⟨ko, hko, objBits_of_aType_sc hty⟩
  have hfr0 := J.free_noObj hAs hcap hBF hksR hsc
  have hWZ' : WinZero (L.mem res.2.1) (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat (2 ^ (zOf nt.val us.val)) win.val (t = .tcbObject) := by
    have h0 := hWZ ⟨rfl, htP⟩
    rw [eA, ek, ew, hlen, hb] at h0
    exact h0
  have hTn : ¬ t = .tcbObject := htT
  have hTT : ∀ q ∈ (winSet (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat (2 ^ (zOf nt.val us.val)) win.val), ∀ t0 ∈ Z.T, t0.val + 4096 ≤ q.val ∨ q.val + 2 ^ (zOf nt.val us.val) ≤ t0.val := by
    intro q hq t0 ht0
    have hth : Z.th t0 = some .tcb := (hJp.tcb t0).2 (J.zH.1 t0 ht0)
    have := hU.free t0 .tcb hth
    obtain ⟨b1, b2, -⟩ := hwb q hq
    simp only [objSize] at this; omega
  have hpos : 0 < 2 ^ (zOf nt.val us.val) := Nat.two_pow_pos _
  have hXZ : XTopAt (L := L) AR (Z.addW nt G' (winSet (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat
      (2 ^ (zOf nt.val us.val)) win.val)) res.2.1 ar σ' := by
    unfold XSets.addW
    split_ifs with h2
    · -- endpoints
      have htE : t = .endpointObject := by
        rcases ht with rfl | rfl
        · rfl
        · have := objTypeOf_ntfn hn0; omega
      have hz4 : zOf nt.val us.val = 4 := by simp [zOf, h2]
      have h16 : (2 : Nat) ^ (zOf nt.val us.val) = 16 := by rw [hz4]; rfl
      exact XTopAt.addE hX' (Wn := (winSet (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat (2 ^ (zOf nt.val us.val)) win.val))
        (fun e he => by rw [hspec e he, htE]; rfl)
        (fun e he => by
          obtain ⟨b1, b2, b3⟩ := hwb e he
          rw [h16] at b2 b3
          rw [Notif.epTSA_eq, Notif.epHeadA_eq]
          refine ⟨winZero_field hWZ' hTn he (by omega) (by omega) (by rw [h16]; simp) (by simp),
            winZero_field hWZ' hTn he (by omega) (by omega) (by rw [h16]; simp) (by simp)⟩)
        (fun e he => by obtain ⟨b1, b2, b3⟩ := hwb e he; rw [h16] at b2 b3; exact ⟨b3, by omega, by omega⟩)
        (fun e he t0 ht0 => by have := hTT e he t0 ht0; rw [h16] at this; exact this)
        (fun e he => by obtain ⟨b1, b2, -⟩ := hwb e he; rw [h16] at b2; rw [hksR]; omega)
        (fun e he b g1 g2 => by obtain ⟨b1, b2, -⟩ := hwb e he; rw [h16] at b2; exact hfr0 b (by omega) (by omega))
    · -- notifications
      have h3 : nt.val = 3 := hnt.resolve_left h2
      have htN : t = .notificationObject := by
        rcases ht with rfl | rfl
        · have := objTypeOf_ep hn0; omega
        · rfl
      have hz6 : zOf nt.val us.val = 6 := by simp [zOf, h3]
      have h64 : (2 : Nat) ^ (zOf nt.val us.val) = 64 := by rw [hz6]; rfl
      exact XTopAt.addN hX' (Wn := (winSet (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat (2 ^ (zOf nt.val us.val)) win.val))
        (fun n hn => by rw [hspec n hn, htN]; rfl)
        (fun n hn => by
          obtain ⟨b1, b2, b3⟩ := hwb n hn
          rw [h64] at b2 b3
          rw [Notif.epTSA_eq, Notif.epHeadA_eq, Notif.nBoundA_eq, Notif.nScA_eq]
          refine ⟨winZero_field hWZ' hTn hn (by omega) (by omega) (by rw [h64]; simp) (by simp),
            winZero_field hWZ' hTn hn (by omega) (by omega) (by rw [h64]; simp) (by simp),
            winZero_field hWZ' hTn hn (by omega) (by omega) (by rw [h64]; simp) (by simp),
            winZero_field hWZ' hTn hn (by omega) (by omega) (by rw [h64]; simp) (by simp)⟩)
        (fun n hn => by obtain ⟨b1, b2, b3⟩ := hwb n hn; rw [h64] at b2 b3; exact ⟨b3, by omega⟩)
        (fun n hn t0 ht0 => by have := hTT n hn t0 ht0; rw [h64] at this; exact this)
        (fun n hn => by obtain ⟨b1, b2, -⟩ := hwb n hn; rw [h64] at b2; rw [hnbR]; omega)
        (fun n hn => by obtain ⟨b1, b2, -⟩ := hwb n hn; rw [h64] at b2; rw [hksR]; omega)
        (fun n hn b g1 g2 => by obtain ⟨b1, b2, -⟩ := hwb n hn; rw [h64] at b2; exact hfr0 b (by omega) (by omega))
  -- the window, with short names
  have hwv : w = win.val := by rw [ew, hlen]
  have hkv : k = 2 ^ zOf nt.val us.val := by rw [ek, hb]
  subst hwv hkv
  replace hE : RetExp Z.th Z.th (L.mem s) (L.mem res.2.1) Z.G G' Aw (2 ^ zOf nt.val us.val) win.val dslot cj
      (cslotAddr (pp.bv, idx)) := hE
  rw [← eA] at hwb hreg hspec hTT hXZ hA1 hA2 hA3
  -- the new endpoints or notifications
  obtain ⟨En, Nn, hZ', hEN, hEs, hNs, hEt, hNt, hWEN⟩ : ∃ En Nn : Set U64,
      Z.addW nt G' (winSet Aw (2 ^ zOf nt.val us.val) win.val) =
        { Z with G := G', E := Z.E ∪ En, N := Z.N ∪ Nn } ∧
      (En = ∅ ∨ Nn = ∅) ∧ En ⊆ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧
      Nn ⊆ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧
      (∀ e ∈ En, nt.val = 2) ∧ (∀ n ∈ Nn, nt.val = 3) ∧
      ∀ q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val, q ∈ En ∨ q ∈ Nn := by
    by_cases h2 : nt.val = 2
    · exact ⟨_, ∅, XSets.addW_two h2, Or.inr rfl, fun _ h => h, fun _ h => by simp at h, fun _ _ => h2,
        fun _ h => by simp at h, fun q h => Or.inl h⟩
    · exact ⟨∅, _, XSets.addW_ne h2, Or.inl rfl, fun _ h => by simp at h, fun _ h => h, fun _ h => by simp at h,
        fun _ _ => hnt.resolve_left h2, fun q h => Or.inr h⟩
  rw [hZ'] at hXZ
  -- the spec side
  have hdet : ∀ σx, Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σx)}, False) → σx = σ1 :=
    fun σx h => by
      have e := congrArg Prod.fst (h.symm.trans hst1)
      simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at e
      exact e
  obtain ⟨hcdtK, horgK⟩ := invokeUntyped_noreset_co Fl4Spec.fl4ObjBitsApi (pp.bv, idx) p.bv _ t us.val
    (windowSlots dest r off.val win.val) false σ1 htU htP (.ok (), σ') (by rw [hrun]; rfl)
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
  have hwI : P1.WritesIn st s1 res.2.1 (InSlot Z.th) := ⟨hW.1, hW.2.1, fun b hb hn => hW.2.2 b hb (fun h => hn (by
    rcases h with (⟨h1, -⟩ | h) | ⟨h1, -⟩
    · exact absurd h1 htT
    · exact h
    · exact absurd h1 htP))⟩
  have hidl1 : IdleKeep (L := L) s s1 := J.idleW_keep J1.xtop.fin.1.1.1 hid1 hisc1
  have hidl2 : IdleKeep (L := L) s1 res.2.1 :=
    J1.idleW_keep hX'.fin.1.1.1 (hC2.idle.trans hidB) (hC2.isc.trans hiscB)
  have hidl : IdleKeep (L := L) s res.2.1 := hidl1.trans hidl2
  -- P1's creation: the heap after, `BlkOK`, `JCovD`
  have hcjU : ∀ j, j < win.val → isUt (cj j) = false := by
    intro j _; rw [hcj]; rcases hnt with h | h <;> simp [cjOf, newCapOf, h, isUt]
  obtain ⟨H', Ac', hblk', hout, hjc'⟩ := J.create_noreset hni J1 hs1 hct1 hcsc1 hid1 hisc1 hns1 hRU hpp hidx hcap hE
    hcjU hnt (k := 2 ^ zOf nt.val us.val) rfl hAk htT htP hW (hWZ ⟨rfl, htP⟩) hidl
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
    rcases hA.kback hk' with h1 | ⟨-, h2⟩
    · by_cases ho : o = (L.curW s).bv
      · subst ho; obtain ⟨y1, hy1⟩ := hσ1c; rw [hy1] at h1; cases h1
      · rw [hσ1k o ho, h0] at h1; cases h1
    · rcases ht with rfl | rfl <;> simp [Fl4Spec.defaultObject] at h2
  have hn1 : nt.val ≠ 1 := by omega
  obtain ⟨th2, σ2, A2, k2', w2, lo2, hi2, eA2, ek2, ew2, -, -, hor2, ⟨σ12, hst12, hhas2⟩, hthx2, hJP2⟩ :=
    Sched.JPlaced.retype (L := L) hJp J.jcov J.ut hI hM hRPN hok nt.val hty (by omega)
      (fun kd h => by rw [newKind_bits h, hb]) (fun kd h => by rw [newKind_bits h]; have := hctx.size.2.1; omega)
      (fun z h => by rcases hnt with h' | h' <;> simp [newKind, h'] at h) (fun h => absurd h hn1) (fun h => absurd h hn1)
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
  have hDbg : L.mem res.2.1 (L.nodeAt s1 0#u64 layout.node.DEBUG_TCBS) =
      L.mem s1 (L.nodeAt s1 0#u64 layout.node.DEBUG_TCBS) :=
    hwI.mem_eq J1.kern.dwAl fun ⟨x, hx, h1, h2⟩ => J1.kern.dwObj x hx ⟨h1, h2⟩
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
      (∀ z, kd ≠ .other z) ∧ (q.val + 2 ^ kd.bits ≤ (L.ksb res.2.1).val ∨ (L.ksb res.2.1).val + 13568 ≤ q.val) ∧
      ∀ c ∈ Cs, q.val + 2 ^ kd.bits ≤ L.nodeBase res.2.1 c ∨ L.nodeBase res.2.1 c + 4288 ≤ q.val := by
    intro q kd hq hK
    obtain ⟨j, hj, hqv⟩ := hq
    have hjk : (j + 1) * 2 ^ zOf nt.val us.val ≤ win.val * 2 ^ zOf nt.val us.val := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at hjk
    have hbk : 2 ^ kd.bits = 2 ^ zOf nt.val us.val := by rw [newKind_bits hK]
    have hnb : ∀ c, L.nodeBase res.2.1 c = L.nodeBase s c := fun c => by
      simp only [P1.LawfulStore.nodeBase, hksR]
    refine ⟨fun z e => ?_, ?_, fun c hc => ?_⟩
    · subst e; rcases hnt with h | h <;> simp [newKind, h] at hK
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
  have hutc := J1.ret_utc (G' := G') hAs (capV_of_capAt hcap1) e1u (by omega) hfi1
    (· ∈ windowSlots dest r off.val win.val) (fun d hd => (hslA d hd).1)
    (fun d hd => (hSS1.capAt (hslA d hd).1.isSlot).trans (hDn0 d hd)) hDu hcapK hwI hcdtK horgK hgp' hM'
    (RetExp.src_child hE hctx.window.1 hP' hC' hAs)
    (fun d hd sl p1 sb1 fi2 dev hsl hcv hdv hnc => by
      obtain ⟨-, i, -, -, rfl⟩ := hslA d hd
      exact J1.live_slot arI hsl hcv hdv hnc ⟨dest, r, rfl, hctx.cnode.1,
        natToCref_length _ _ (by have := hctx.cnode.2.1; omega), hDL⟩)
  -- the spec's invariants and the call stacks (`uaRest`, `addRP`)
  have hIN : IdleNew (fun q => q ∈ regionPtrs (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
      (windowSlots dest r off.val win.val).length (2 ^ Fl4Spec.fl4ObjBitsApi t us.val))
      (fun _ => Fl4Spec.defaultObject t false us.val σ1.curDomain) := fun q _ => by
    rcases ht with rfl | rfl <;> simp [Fl4Spec.defaultObject]
  have hWnN : ∀ n ∈ Nn, n.bv ∈ regionPtrs (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
      (windowSlots dest r off.val win.val).length (2 ^ Fl4Spec.fl4ObjBitsApi t us.val) := fun n hn => hreg n (hNs hn)
  obtain ⟨hCR1, -, hRF1, hRR1, hY1, hMc1, hBw1, hNSC1, hInv1, hCur1, hOwn1, hOff1, hAct1, hBsa1, hIs1, hCRun1⟩ :=
    J1.uaRest hwI hA hIN hcnk hWnN
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
  obtain ⟨hRP1, hSA1⟩ := J1.addRP hwI hA hIN hcnk hWnN hU.free hspec1
    (fun n hn => ⟨(hNw0 n hn).2.1, (hNw0 n hn).2.2.1⟩)
  -- the set and heap fields (`addSets`)
  have hKn : ∀ q, NewAt Aw (2 ^ zOf nt.val us.val) win.val q → ∀ kd, newKind nt.val us.val = some kd →
      (kd = .ep ∧ q ∈ En) ∨ (kd = .ntfn ∧ q ∈ Nn) := by
    intro q hq kd hK
    rcases hWEN q hq with h | h
    · have h2 := hEt q h; simp [newKind, h2] at hK; exact Or.inl ⟨hK.symm, h⟩
    · have h3 := hNt q h; simp [newKind, h3] at hK; exact Or.inr ⟨hK.symm, h⟩
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
      (∃ n ∈ Nn, n.bv = o ∧ ko = .notification Fl4Spec.defaultNotification) := by
    intro o ko hk
    have hback1 : ∀ ko', σB.kheap o = some ko' → σ1.kheap o = some ko' ∨
        (∃ e ∈ En, e.bv = o ∧ ko' = .endpoint Fl4Spec.defaultEp) ∨
        (∃ n ∈ Nn, n.bv = o ∧ ko' = .notification Fl4Spec.defaultNotification) := by
      intro ko' h
      rcases hA.kback h with h1 | ⟨hW', h2⟩
      · exact Or.inl h1
      · obtain ⟨q, hq, hqo⟩ := hrev o hW'
        rcases hWEN q hq with hqE | hqN
        · have h2' := hEt q hqE
          have htE : t = .endpointObject := by
            rcases ht with rfl | rfl
            · rfl
            · have := objTypeOf_ntfn hty; omega
          exact Or.inr (Or.inl ⟨q, hqE, hqo, by rw [h2, htE]; rfl⟩)
        · have h3' := hNt q hqN
          have htN : t = .notificationObject := by
            rcases ht with rfl | rfl
            · have := objTypeOf_ep hty; omega
            · rfl
          exact Or.inr (Or.inr ⟨q, hqN, hqo, by rw [h2, htN]; rfl⟩)
    rcases hkc o with e | ⟨r0, cs, cs', e1, e2⟩
    · rcases hback1 ko (e.symm.trans hk) with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inr (Or.inl h1))
      · exact Or.inr (Or.inr (Or.inr h1))
    · rw [e2] at hk; cases hk
      rcases hback1 _ e1 with h1 | ⟨e, -, -, he⟩ | ⟨n, -, -, hn⟩
      · exact Or.inr (Or.inl ⟨r0, cs, cs', h1, rfl⟩)
      · cases he
      · cases hn
  have harch1 : ArchFitHyp H σ1 := fun o ao n h hH => hAF o ao n (by
    by_cases ho : o = (L.curW s).bv
    · subst ho; obtain ⟨y1, hy1⟩ := hσ1c; rw [hy1] at h; cases h
    · rwa [hσ1k o ho] at h) hH
  obtain ⟨hKs', hIp', hnk', hcov', hobj', hzH', hset', hscC'⟩ :=
    J1.addSets (Z' := { Z with G := G', E := Z.E ∪ En, N := Z.N ∪ Nn }) hwI.1 (by omega) hU.pfit hU.free
      (by rw [hk1]; rcases k1 with h | h <;> omega) hspec1
      (fun wp hwp => hBF wp hwp _ hxG p sb fiv (capV_of_capAt hcap)) harch1 hA1 hA3 hE.k1 hout hEw0 hNw0 hEN hKn
      hback rfl rfl rfl rfl rfl rfl
  -- the CSpace fields (`JCs`)
  have hcjZ : ∀ j, j < win.val → ∀ p1 zt n1, cj j ≠ .Zombie p1 zt n1 := by
    intro j _ p1 zt n1; rw [hcj]; rcases hnt with h | h <;> simp [cjOf, newCapOf, h]
  have hob : ∀ cd, Fl4Spec.objBits (Fl4Spec.defaultObject t false us.val cd) ≤ Fl4Spec.fl4ObjBitsApi t us.val := by
    intro cd; rw [hb]
    rcases ht with rfl | rfl
    · rw [objTypeOf_ep hty]; simp [Fl4Spec.defaultObject, Fl4Spec.objBits, zOf, Fl4Spec.endpointBits]
    · rw [objTypeOf_ntfn hty]; simp [Fl4Spec.defaultObject, Fl4Spec.objBits, zOf, Fl4Spec.ntfnBits]
  have hSF' : SpecFree (L.mem res.2.1) G' σ' := SpecFree.retype J.sfree J.ut hksz (capV_of_capAt hcap) rfl hg1
    (fun _ => by rw [← eA]; exact hA1) (y := (.ok (), σ')) (by rw [hrun]; rfl) rfl hU' hI' hE
    (fun _ => ⟨eA, by rw [hb], by rw [hlen], hRFu hok⟩) hob
  have hCs : JCs (L := L) { Z with G := G', E := Z.E ∪ En, N := Z.N ∪ Nn } res.2.1 σ' :=
    JCs.retype rfl rfl J.del hE hM hP' hM' hcjZ (fun _ _ _ h => h) hU' (hFin hFI0).fm hSF'
  -- `JRest` and `JAtZ` after
  have hJR : JRest (L := L) arI { Z with G := G', E := Z.E ∪ En, N := Z.N ∪ Nn } H' Cs Ac' Lst1
      {q | q ∈ D ∧ ¬ NewQ Aw (2 ^ zOf nt.val us.val) win.val cj q} res.2.1 σ' :=
    ⟨hCR1, hRF1, hRR1, hY1, hMc1, hBw1, hRP1, hSA1, ⟨_, _, hJPa⟩, hjc', K2, hutc, hNSC1, hInv1, hCur1, hOwn1,
      hOff1, hAct1, hBsa1, hIs1, hCRun1, hblk'⟩
  have JZ := J1.add_frame (Z' := { Z with G := G', E := Z.E ∪ En, N := Z.N ∪ Nn }) rfl rfl rfl hwI.1 hXZ hCs hJR
    hKs' J1.thT hIp' hnk' hcov' hobj' hzH' hset' hscC'
  refine ⟨σ1, hst1, (.ok [], σ'), perf_ut_mem blk call don hrun, ⟨Z.th, G', Or.inl ⟨hok, rfl⟩, ?_⟩, ?_⟩
  · obtain ⟨hPl, hCR, hFI, hD, hMO, -, -⟩ := hXZ.rel
    exact ⟨hPl, hCR, hFI, hD, hMO⟩
  · rw [if_neg (by rw [hok]; simp), har]
    exact ⟨_, H', Cs, Ac', Lst1, _, JZ⟩

variable (arI) in
/-- **[W] The retype of a RAM untyped at `J`, outside `JAtZ.utEpJ`'s case**
(XTopJointUt's `JUtRetHyp` narrowed): asked only with a reset (the source
cap childless) or of an object type other than endpoints and notifications.
l4v: `invoke_untyped_corres` with `invoke_untyped_invs`. -/
def JUtRetHypR (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (sl : Fl4Spec.CslotPtr) (p sb fi ct : U64) (blk call don : Bool) (argsU : List U64) : Prop :=
  ∀ (nt us dest off win : U64) (t : Fl4Spec.ApiObjectType) (r : Nat) (reset : Bool) (fiv : U64),
    argsU.head? = some nt → RetCtx (L := L) th s σ sl sb fi false nt us dest off win t r reset fiv →
    (reset = true ∨ (nt.val ≠ 2 ∧ nt.val ≠ 3)) →
    (do
      let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
      untyped.retype st arI s2 ar (cslotAddr sl) reset ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ nt us
        dest off win false) ⦃ res =>
      UtRetPostJ (L := L) arI AR σ blk call don (.retype sl reset p.bv
        (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val) false)
        res ⦄

/-- **`JUtRetHyp` from its narrowed form**: the no-reset retype of
endpoints or notifications from a CNode slot by `JAtZ.utEpJ` (with
`BufObjHyp`, `ArchFitHyp`, `RegionUnrefJ` [J]), the rest `JUtRetHypR` [W]. -/
theorem JAtZ.jUtRetHyp {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) {ct : U64} (hct : sched.cur_thread st s = ok ct) {sl : Fl4Spec.CslotPtr}
    (hsl : ∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) {p sb fi : U64}
    (hcap : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi false))
    (hBO : BufObjHyp Z.B σ) (hAF : ArchFitHyp H σ) (hRU : RegionUnrefJ (L := L) arI H Cs)
    {blk call don : Bool} {argsU : List U64}
    (hR : JUtRetHypR (L := L) arI AR Z.th s ar σ sl p sb fi ct blk call don argsU) :
    JUtRetHyp (L := L) arI AR Z.th s ar σ sl p sb fi ct blk call don argsU := by
  intro nt us dest off win t r reset fiv hh hctx
  by_cases hc : reset = true ∨ (nt.val ≠ 2 ∧ nt.val ≠ 3)
  · exact hR nt us dest off win t r reset fiv hh hctx hc
  have hrs : reset = false := by
    cases reset
    · rfl
    · exact absurd (Or.inl rfl) hc
  have hnt : nt.val = 2 ∨ nt.val = 3 := by
    by_contra h
    exact hc (Or.inr ⟨fun e => h (Or.inl e), fun e => h (Or.inr e)⟩)
  subst hrs
  obtain ⟨sl1, idx⟩ := sl
  obtain ⟨pp, hp1, hpp⟩ := hsl
  dsimp only at hp1 hpp
  subst hp1
  exact J.utEpJ hni hct hpp rfl hcap hnt hctx hBO hAF hRU blk call don

end

end

end Fl4Proofs.P3
