/-
P3 (line mmuAD, gen 42b6): **the ASID-pool assign of an EPT root at the base's top layer** — the route (b) of gen
42b5 (`setEptRoot_decode_vmEpt`'s shape: the extended decoder, no existing statement touched), first half.

* Spec: **`decV_asidPoolEpt`**: the extended decoder `fl4DecodeInvocationV` on an ASID-pool cap with label
  `X86ASIDPoolAssign` whose first extra cap is an unmapped level-0 `eptCap` is `decodeEptAsidPoolAssign`
  (Ext/VirtDispatch l. 74-76, `startsWithEptRoot`; the native `fl4DecodeInvocation` returns
  `invalidCapability 1` there, P3/VsDecFrame's `decodeAssign_bad`). **`vsSFr_eptAssign`**: the perform keeps
  `vsF` (P3/XTopJointVsMapSpec), so the spec's step after the restart is a
  `VsSFr` step (what `JAtZB.vsStepJXB` takes), from `performEptAssign_eq` and `vsF_upd`.
* `vsLike_eptAssign`: the rewritten cap `Ept r 0 true asid 0` is `VsLike` the old `Ept r 0 false …` (same shape, no
  object key, no badge, `vtF` true on both; an `Ept` cap is `VCapOK`-trivial).
  Gen 42b11: generalised in place to `vsLike_ept` (any level and guest address; the table map), the old name its
  corollary.
* **`JAtZB.eptAssignX`**: from `JAtZB` and `EptCore` at an `Entered` spec state, the invoked ASID-pool cap in a slot,
  its first extra cap the unmapped level-0 `Ept ptr1` of a CNode slot: FL4's `vspace.decode` at `X86ASIDPoolAssign`
  ends in an error related to the spec decoder's with the states unchanged, or `Ok ()` with the spec decoder's
  outcome `.poolAssign asid ptr (pc, idx)` (no failure), the single outcome `σ'` of restart + perform
  (`EptAssignSpec`), **`XTopAt AR Z` after** (the native capX/thX construction over P3/EptAssignRel's
  `assign_rel_ept`: `VsInvHyps.ptTop` of `VsInvHyps.foot` of `vsInvHyps_top`, `crelM_after`, `PoolsIn` after — the
  written pool word `ptr1 ||| 1` is tagged —, `CurOK.of_inv`, `DomRel.frame` by `dom_of_foot`, `FinXT.toXR`), the
  VSpace footprint `WritesIn … (VsFootW …)`, `SlotFoot`, `KFoot`, the pool-word footprint and `AssignFE`.

Not here yet (gen 42b6 stopped): the `JAtZB` + `VcpuCore` + `EptCore` step from these facts to `VmEptState` after
(`VmEptState.restart` to the restart state, FL4's writes after it as in `JAtZ.vsPostJ`'s pins, `JAtZB.vsStepJXB`
with `vsSFr_eptAssign`, `VsNamed` after for a tagged pool word, `VcpuCore.ofW`, `JExtEpt` after and
`EptCore.assignE`).

No named premise; the spec is not touched. No `sorry`; only the three standard axioms.
-/
import Fl4Proofs.P3.EptAssign
import Fl4Proofs.P3.EptSetRoot
import Fl4Proofs.P3.VsThX
import Fl4Proofs.P3.VsDomF
import Fl4Proofs.P3.XTopJointVsMapSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-! ## Spec side -/

section Spec
open Fl4Spec

/-- **The extended decoder on an ASID-pool cap, label `Assign`, first extra cap an unmapped level-0 EPT root** is
`decodeEptAsidPoolAssign` (Ext/VirtDispatch l. 74-76). -/
theorem decV_asidPoolEpt {p b : ObjRef} {slbl : Data}
    (hl : invocationType slbl = .archInvocationLabel .x64ASIDPoolAssign) (fp : Bool) (args : List Data)
    (ci : CapRef) (sl : CslotPtr) (r : ObjRef) (sl' : CslotPtr) (rest : List (Cap × CslotPtr))
    (buffer : Option ObjRef) :
    fl4DecodeInvocationV (Z := Unit) fp slbl args ci sl (.archObjectCap (.asidPoolCap p b))
      ((.archObjectCap (.eptCap r 0 none), sl') :: rest) buffer =
      NonDetE.liftME Fl4InvocationV.ept (decodeEptAsidPoolAssign p b sl') := by
  unfold fl4DecodeInvocationV
  dsimp only
  rw [if_pos ⟨hl, rfl⟩]
  try rfl

/-- **The spec's step of an EPT pool assign after the restart is a `VsSFr` step** (P3/EptAssignRel's
`performEptAssign_eq`: one CNode slot and one pool rewritten, `vsF_upd` twice). -/
theorem vsSFr_eptAssign {σ σ1 σ' : State Unit} {asid p : ObjRef} {pc : ObjRef} {r : Nat} {cs : CnodeContents}
    {idx : List Bool}
    (hst : setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (h : Vs.EptAssignSpec σ asid p (pc, idx) σ')
    (hk : σ1.kheap pc = some (.cnode r cs)) (hwf : wellFormedCnodeN r cs) (hidx : idx.length = r) {rt : ObjRef}
    {o : Option (Asid × VSpaceRef)} (hc : cs idx = some (.archObjectCap (.eptCap rt 0 o)))
    {f : AsidLowIndex → Option ObjRef} (hp : σ1.kheap p = some (.archObj (.asidPool f))) : VsSFr σ1 σ' := by
  unfold Vs.EptAssignSpec at h
  rw [Notif.nd_bind_one hst, Vs.performEptAssign_eq hk hwf hidx hc hp asid] at h
  have e := congrArg Prod.fst h
  simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at e
  subst e
  have hpc : p ≠ pc := Endp.kheap_ne hp hk (fun _ h1 h2 => by subst h1; cases h2)
  apply VsSFr.of_eq
  have hp' : (setCnodeSlot σ1 pc r cs idx (.archObjectCap (.eptCap rt 0 (some (asid, 0))))).kheap p =
      some (.archObj (.asidPool f)) := by simp [setCnodeSlot, hpc, hp]
  unfold Notif.updK
  refine (vsF_upd hp' ?_ ?_).trans ?_
  · rfl
  · rfl
  unfold setCnodeSlot
  refine vsF_upd hk ?_ ?_
  · simp [aType, hwf, wf_update _ hwf hidx]
  · rfl

end Spec

/-- **Any `Ept r l` cap is `VsLike` any other of the same table and level** (mmuAD gen 42b14: `vsLike_ept`
generalised in place to both mapped flags, for the table unmap's `Ept … true → Ept … false 0 0`). -/
theorem vsLike_eptG (r l : U64) (m : Bool) (asid v : U64) (m0 : Bool) (a0 v0 : U64) :
    Vs.VsLike (.Ept r l m asid v) (.Ept r l m0 a0 v0) :=
  ⟨⟨rfl, rfl, rfl, rfl⟩, fun _ _ _ _ _ _ => trivial⟩

/-- A mapped `Ept r l` cap is `VsLike` an unmapped one of the same table and level (mmuAD gen 42b11:
`vsLike_eptAssign` generalised in place to any level and guest address, for the table map; gen 42b14: the corollary
of `vsLike_eptG`). -/
theorem vsLike_ept (r l asid v a0 v0 : U64) :
    Vs.VsLike (.Ept r l true asid v) (.Ept r l false a0 v0) :=
  vsLike_eptG r l true asid v false a0 v0

/-- The rewritten EPT root cap is `VsLike` the old one. -/
theorem vsLike_eptAssign (r asid a0 v0 : U64) :
    Vs.VsLike (.Ept r 0#u64 true asid 0#u64) (.Ept r 0#u64 false a0 v0) := vsLike_ept r 0#u64 asid 0#u64 a0 v0

/-- A tagged word is not an untagged one. -/
theorem or1_and1_ne (x : U64) : (x ||| 1#u64) &&& 1#u64 ≠ 0#u64 := by
  intro h
  have e := congrArg (fun y : U64 => y.bv.getLsbD 0) h
  simp only [UScalar.bv_and, UScalar.bv_or, BitVec.getLsbD_and, BitVec.getLsbD_or, P1.one_bit] at e
  simp at e

/-! ## The base's top layer -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {X : Set U64} {XL : U64 → Nat}

open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P1

set_option maxHeartbeats 4000000 in
/-- **The ASID-pool assign of an unmapped EPT root at `JAtZB`'s top layer** (module docstring). -/
theorem JAtZB.eptAssignX (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (C : EptCore (L := L) X XL Z.th s σ) (hni : Entered σ)
    (ptr base : U64) {slot : U64} (hsl : IsSlot Z.th slot) (hcap : capAt (L.mem s) slot = ok (.AsidPool ptr base))
    (length : U64) (call : Bool) (buf : U64) (ex : Array obj.Slot 3#usize)
    {pc : U64} {r : Nat} (hpc : Z.th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    (hex : vspace.extra ex 0#usize = ok (some (cslotAddr (pc.bv, idx))))
    {ptr1 asid0 va0 : U64} (hcx : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Ept ptr1 0#u64 false asid0 va0)) :
    vspace.decode st arI s a fl4_abi.label.X86ASIDPoolAssign length slot (.AsidPool ptr base) call buf ex ⦃ res =>
      (∃ e e', res.1 = .Err e ∧ VsErrRel e e' ∧
        ExceptT.run (Fl4Spec.decodeEptAsidPoolAssign (Z := Unit) ptr.bv base.bv (pc.bv, idx)) σ =
          ({(.error e', σ)}, False) ∧
        res.2.1 = s ∧ res.2.2 = a) ∨
      (res.1 = .Ok () ∧
        ¬ (ExceptT.run (Fl4Spec.decodeEptAsidPoolAssign (Z := Unit) ptr.bv base.bv (pc.bv, idx)) σ).2 ∧
        ∃ asid σ', (.ok (.poolAssign asid ptr.bv (pc.bv, idx)), σ) ∈
          (ExceptT.run (Fl4Spec.decodeEptAsidPoolAssign (Z := Unit) ptr.bv base.bv (pc.bv, idx)) σ).1 ∧
          EptAssignSpec σ asid ptr.bv (pc.bv, idx) σ' ∧
          XTopAt (L := L) AR Z res.2.1 res.2.2 σ' ∧
          P1.WritesIn st s res.2.1 (VsFootW st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 s) ∧
          SlotFoot Z.th (L.mem s) (L.mem res.2.1) (cslotAddr (pc.bv, idx)) ∧ KFoot σ σ' ∧
          (∀ b, VsWrite Z.P (L.ksb s) b → L.mem res.2.1 b ≠ L.mem s b → L.mem res.2.1 b = (ptr1 ||| 1#u64)) ∧
          AssignFE (L.mem res.2.1) (cslotAddr (pc.bv, idx)) ptr1 σ σ') ⦄ := by
  have hX := J.xtop
  obtain ⟨hS, hR, hPt, hPI, hCur⟩ := hX.fin
  obtain ⟨-, hCR, hFI, hDR, hMO, hIA, -⟩ := hX.rel
  have hct := P1.cur_thread_ok (L := L) s
  obtain ⟨hcur, xct, hkt, hrun⟩ := J.curRunnable hni hct
  have htcb : Z.th (L.curW s) = some .tcb := (hX.curTcb hcur).1
  have hCR0 := hCR
  obtain ⟨hSt, hSV, -, -, -⟩ := hCR0
  have hw := J.vsc slot hsl
  rw [capV_of_capAt hcap] at hw
  simp only [VCapW, VCapOK] at hw
  have hcan : Canonical ptr1 := by
    have h := hcx; rw [capAt_words] at h; exact (decode_encWf h).1
  have hxs : IsSlot Z.th (cslotAddr (pc.bv, idx)) :=
    AbsSlot.isSlot (th := Z.th) (sl := (pc.bv, idx)) ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩
  have hev : ptr1.val % 2 = 0 := by
    have h := C.exte.cap _ hxs
    rw [capV_of_capAt hcx] at h
    have hp := (C.rel.place ptr1 h).1
    omega
  have hkt' : σ.kheap σ.curThread = some (.tcb xct) := by rw [hcur]; exact hkt
  have hst1 : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ =
      ({((), stsAct (updK σ (L.curW s).bv (.tcb { xct with tcbState := .restart })) (L.curW s).bv)}, False) := by
    rw [hcur]; exact Notif.setThreadState_eq .restart hkt
  have hH := VsInvHyps.ptTop (L1 := Z.L1) (L2 := Z.L2) (L3 := Z.L3) (L4 := Z.L4) (A := A) (N := Z.N) (T := Z.T)
    (C := Z.C) (E := Z.E) (R := Z.R) (B := Z.B) (c := Z.c) (AR := AR)
    (Vs.VsInvHyps.foot (s0 := s) (W := VsFootW st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 s) (fun _ h => h.toW) hS.2.pl
      (fun _ h => Or.inr (Or.inr (Or.inr (Or.inl h)))) (vsInvHyps_top curT_top))
  refine WP.spec_mono (assign_rel_ept (ar := arI) hH s a σ hS.2.pl hS.2.vs hS.2.sd hSt hSV hR
    ⟨⟨hS, P1.WritesIn.refl _ _⟩, hPt⟩ hkt' hrun ptr base hw.2.1 hw.2.2 length slot call buf
    ex hpc hidx hex hcx hcan hev
    (fun ct' h => by rw [show ct' = L.curW s from P1.eq_of_bv (h.trans hcur)]; exact htcb) J.kern.act hS.2.vo) ?_
  rintro res (⟨e, e', h1, he, hdec, h2, h2a⟩ |
    ⟨h1, hnf, asid, σ', hmem, hAS, hSt', hSV', hR', hSRq, hF, hK, hAW, hFE⟩)
  · exact Or.inl ⟨e, e', h1, he, hdec, h2, h2a⟩
  refine Or.inr ⟨h1, hnf, asid, σ', hmem, hAS, ?_, hSRq.1.2, hF, hK, hAW, hFE⟩
  obtain ⟨asid1, -, -, -, -, hcv1, -⟩ := hFE
  have hL : VsLike (capV (L.mem res.2.1) (cslotAddr (pc.bv, idx))) (.Ept ptr1 0#u64 false asid0 va0) := by
    rw [hcv1]; exact vsLike_eptAssign ptr1 asid1 asid0 va0
  obtain ⟨hCR', hFI', hMO'⟩ := crelM_after hCR hFI hMO hcx hSt' hSV' hF hL hK rfl
  have hks' : L.ksb res.2.1 = L.ksb s := hSRq.1.2.1
  have hPI' : PoolsIn Z.P Z.L4 (L.mem res.2.1) := by
    intro p hp lo hl hne h1'
    by_cases e : L.mem res.2.1 (peA p lo) = L.mem s (peA p lo)
    · rw [e] at hne h1' ⊢; exact hPI p hp lo hl hne h1'
    · rw [hAW _ (Or.inr ⟨p, hp, lo, hl, rfl⟩) e] at h1'
      exact absurd h1' (or1_and1_ne ptr1)
  have hFin : FinXT (L := L) Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.N Z.T Z.C Z.E Z.R Z.B Z.c AR (L.ksb s) σ res.2.1 res.2.2
      σ' :=
    ⟨⟨hSRq.1.1, hR', hSRq.2, hPI', CurOK.of_inv hCur hK hCR'.2.2.1 hMO'.2.2⟩,
      ⟨Z.G, hCR', hFI', by rw [hks']; exact hMO'⟩, hks', KFoot.szKeep hK⟩
  -- the domain schedule
  obtain ⟨-, hdw⟩ := dom_of_foot hS (Or.inr hSRq.1.2)
  obtain ⟨cs, hkc, hwf, hsl⟩ := hSt.cnode pc r hpc
  have hcs : cs idx = some (.archObjectCap (.eptCap ptr1.bv 0 none)) := by
    obtain ⟨c, ac, hc, hac, hca⟩ := hsl idx hidx
    have : c = .Ept ptr1 0#u64 false asid0 va0 := by
      have h2 : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok c := hc
      rw [hcx] at h2; exact (by simpa using h2 : capability.Cap.Ept ptr1 0#u64 false asid0 va0 = c).symm
    subst this
    rw [hac, ← hca.2]; rfl
  obtain ⟨fp, hkf, -⟩ := hR.pool ptr hw.1.1
  have hpct : pc.bv ≠ (L.curW s).bv := kheap_ne hkc hkt (fun _ h1 h2 => by subst h1; cases h2)
  have hptct : ptr.bv ≠ (L.curW s).bv := kheap_ne hkf hkt (fun _ h1 h2 => by subst h1; cases h2)
  have hkc1 : (stsAct (updK σ (L.curW s).bv (.tcb { xct with tcbState := .restart })) (L.curW s).bv).kheap pc.bv =
      some (.cnode r cs) := by rw [stsAct_kheap]; simp [hpct, hkc]
  have hkf1 : (stsAct (updK σ (L.curW s).bv (.tcb { xct with tcbState := .restart })) (L.curW s).bv).kheap ptr.bv =
      some (.archObj (.asidPool fp)) := by rw [stsAct_kheap]; simp [hptct, hkf]
  have hF1 := vsSFr_eptAssign hst1 hAS hkc1 hwf hidx hcs hkf1
  have hd1 := setThreadState_dom hkt' hst1
  have hD' : DomRel (L.mem res.2.1) (L.ksb res.2.1) σ' := by
    rw [hks']
    exact hDR.frame hdw (hF1.dl.trans hd1.1) (hF1.dsi.trans hd1.2)
  have hXR := FinXT.toXR Z.G hX.esa hIA.dom hFin hD'
  obtain ⟨hFin2, ⟨G0, hPl2, -, -, hD2, -, hIA2, hSA2⟩, hE⟩ := hXR
  obtain ⟨⟨⟨hSch, hEp, hNt, -⟩, -⟩, -⟩ := id hFin2
  exact ⟨hFin2, ⟨hPl2, hCR', hFI', hD2, by rw [hks']; exact hMO', hIA2, hSA2⟩, IpcRel.of hNt hEp (sched_sc hSch), hE⟩

end

end

end Fl4Proofs.P3
