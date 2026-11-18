/-
P3 (DESIGN.md §9), untyped: **the retype of endpoints or notifications
without a reset, from `JAtZ`** (first pieces of XTopJointUt's `JUtRetHyp`,
handoff/utj.md "Round 2"/"Round 3").

* `retExp_pml4_back`: a PML4 cap in a slot after a retype whose new caps are
  no PML4 caps was there before (`RetExp`'s `gmem`/`newc`/`keep`/`utk`).
* `JAtZ.utEpXTop`: from `JAtZ` at the decode (no switch pending), a CNode
  slot's RAM untyped cap and the decode's `RetCtx` for types 2/3 without a
  reset, the restart and `untyped::retype` end done (`Ok`), the spec's
  restart and `invoke_untyped` deterministic, and `XTopAt` after at the
  sets of `JAtZ` (new MDB ghost; the new objects not yet in `Z.E`/`Z.N`):
  `XTopAt.addStep` (UtEpXTop) over `JAtZ.restartJ`'s `XTopAt`, the creation's
  slot-word frame (`RetFrame`), and the spec's outcome split by
  `invokeUntyped_noreset_add` (the window free in the spec's heap by
  `SpecFree`).
-/
import Fl4Proofs.P3.UtEpXTop
import Fl4Proofs.P3.XTopJointTcbInstall
import Fl4Proofs.P3.XTopJointUt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

theorem objTypeOf_ep {n : Nat} (h : objTypeOf n = some .endpointObject) : n = 2 := by
  unfold objTypeOf at h
  split_ifs at h <;> simp_all

theorem objTypeOf_ntfn {n : Nat} (h : objTypeOf n = some .notificationObject) : n = 3 := by
  unfold objTypeOf at h
  split_ifs at h <;> simp_all

/-- **A PML4 cap after a retype was there before** when no new cap is one
(the new caps are in new slots; old non-untyped caps are kept; an old
untyped cap stays untyped). -/
theorem retExp_pml4_back {th : TypedHeap} {m m' : U64 → U64} {G G' : MdbGhost} {A k w : Nat}
    {dslot : Nat → U64} {cj : Nat → capability.Cap} {xs : U64}
    (hE : RetExp th th m m' G G' A k w dslot cj xs) (hM : MdbLinks th m G) (hM' : MdbLinks th m' G')
    (hcj : ∀ j, j < w → ∀ p b a, cj j ≠ .Pml4 p b a) {x p : U64} {b : Bool} {asid : U64} (hxs : IsSlot th x)
    (hx : capAt m' x = ok (.Pml4 p b asid)) : capAt m x = ok (.Pml4 p b asid) := by
  have hmem' : x ∈ G'.chains.flatten := (hM'.members x).2 ⟨hxs, _, hx, by simp⟩
  have hv' := capV_of_capAt hx
  rcases hE.gmem x hmem' with hx0 | ⟨j, hj, rfl⟩
  · obtain ⟨-, c, hc, -⟩ := (hM.members x).1 hx0
    have hv := capV_of_capAt hc
    cases hu : isUt (capV m x)
    · have e := (hE.keep x hx0 hu).2
      rw [hv', hv] at e
      rw [hc, ← e]
    · have e := hE.utk x hx0 hu
      rw [hv'] at e; cases e
  · have e := hE.newc j hj
    rw [hv'] at e
    exact absurd e.symm (hcj j hj _ _ _)

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 8000000 in
/-- **The no-reset retype of endpoints or notifications keeps `XTopAt` at
`JAtZ`'s sets** (module docstring). -/
theorem JAtZ.utEpXTop {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) {ct : U64} (hct : sched.cur_thread st s = ok ct) {pp : U64} {rs : Nat} {idx : List Bool}
    (hpp : Z.th pp = some (.cnode rs)) (hidx : idx.length = rs) {p sb fi : U64}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false))
    {nt us dest off win : U64} {t : Fl4Spec.ApiObjectType} {r : Nat} {fiv : U64}
    (hnt : nt.val = 2 ∨ nt.val = 3)
    (hctx : RetCtx (L := L) Z.th s σ (pp.bv, idx) sb fi false nt us dest off win t r false fiv) :
    (do
      let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
      untyped.retype st arI s2 ar (cslotAddr (pp.bv, idx)) false
        ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ nt us dest off win false) ⦃ res =>
      res.1 = .Ok () ∧ res.2.2 = ar ∧ ∃ σ1 σ' G',
        Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
        (Fl4Spec.invokeUntypedWith (Z := Unit) Fl4Spec.fl4ObjBitsApi (.retype (pp.bv, idx) false p.bv
          (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val)
          false)).run σ1 = ({(.ok (), σ')}, False) ∧
        XTopAt (L := L) AR { Z with G := G' } res.2.1 res.2.2 σ' ⦄ := by
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
  obtain ⟨s1, σ1, -, -, hst1, -, -, -, -, -, -, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  obtain ⟨s1', σ1', -, hs1', -, hSS1, -, -, hk1, -⟩ :=
    restart_dstate Z.th hP s σ Z.G J.dstate (L.curW s) hct J.kern.cur J.kern.curT J.kern.act
  rw [hs1] at hs1'; cases eq_of_ok_eq hs1'
  have hksz : KSz σ σ1 := ksz_of_eq (nkz_setThreadState _ _) hst1
  -- the window, against the source cap
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  obtain ⟨hA1, -, hA3, -⟩ := retype_region p fiv sb.val (zOf nt.val us.val) win.val hsb (by rcases hnt with h | h <;>
    simp [zOf, h]) hU.pal hU.pfit hU.fiLe hctx.window.1 hctx.memory
  refine WP.spec_mono (retype_cont_all (L := L) arI ar Z.th s σ Z.G hSR hV hP hM hC hI J.ut J.kern.orig (L.curW s)
    J.kern.cur hct J.kern.curT J.kern.act hpp hidx hcap hU.pal hU.pfit hU.fiLe (hU.high hnd)
    (fun h => (hU.actZ hnd) ⟨by omega, h.2⟩) hU.free (hU.zero hnd) hunused Fl4Spec.fl4ObjBitsApi nt us dest off win t r
    false fiv (by omega) hb J.kern.dwAl J.kern.dwObj (fun h => (hU.dwReg hnd) ⟨by omega, h.2⟩) J.kern.dwNe J.kern.head
    hctx) (fun res hRP => ?_)
  obtain ⟨hok, har, σ1'', hst, σ', G', th', hrun, -, hR', hV', hM', hC', hI', -, hSt, hFin, hks, Aw, k, w, dslot, cj,
    hE, hRF, -⟩ := hRP
  have e1 : σ1'' = σ1 := by
    have e := congrArg Prod.fst (hst.symm.trans hst1)
    simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at e
    exact e
  subst σ1''
  obtain ⟨ct0, s0, hct0, hs0, hbr⟩ := hRF
  rw [hct] at hct0; cases eq_of_ok_eq hct0
  rw [hs1] at hs0; cases eq_of_ok_eq hs0
  rcases hbr with ⟨e, -⟩ | ⟨-, ⟨eA, ek, ew, -⟩, sR, thR, lo, hi, hor, -, -, -, -, ⟨n0, hn0, hThX, uu, -, hcj⟩, -,
    hW, -, -⟩
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
  refine ⟨hok, har, σ1, σ', G', hst1, hrun, ?_⟩
  rw [har]
  exact XTopAt.addStep J1.xtop hw hA ho hcnk hkc ⟨hR', hV', hM', hC', hI'⟩ (hFin hFI0)
    (by rw [hks1]; exact hSt.okv hMO0) hTS

end

end

end Fl4Proofs.P3
