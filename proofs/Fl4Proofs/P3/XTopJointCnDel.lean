/-
P3 (DESIGN.md §9), CSpace: **CNode Delete and Revoke with `JAt` after**, the
deletion loop run with a `JAtZ`-carrying invariant (`WJ`), so that the
deletion's premises are stated at `JAtZ` states (not at every `XTopAt`
state, as `XFinHyps`/`XPreemptHyp`, whose [J] premises no invariant can
supply).

* `WJ`, `EJ`, `JDelHyp`, `JPreemptHyp` [J] and `JDelParts` (the named steps
  of the deletion loop at `WJ`, from which `JDelHyp.of_parts` derives
  `JDelHyp`): XTopJointDelR.
* `EJ.restart`: the caller's restart keeps `EJ` (`JStepHyps.restart`).
* `cn_del_topJ`: a Delete's or Revoke's outcome at `EJ` gives `TopPostDMX`
  at `JAt`.
* `decode_invocation_cnode_{revoke,delete}J`: the Revoke and Delete labels
  with `JAt` after, from `JAtZ` at the start, `JStepHyps`, `JDelHyp`,
  `JPreemptHyp`.
* `decode_invocation_cnodeJ_steps` (moved here from XTopJointStep): the
  CNode cap with `JAt` after; the per-op premise `JPostHyp` [W] only at
  CancelBadgedSends and the invalid labels.
-/
import Fl4Proofs.P3.XTopJointDelR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **The caller's restart keeps `EJ`** (`JStepHyps.restart`, `cs_frame`). -/
theorem EJ.restart (hJ : JStepHyps (L := L) arI AR Z.th) {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) {K : Nat}
    (hDE : DelE (L := L) Z.th K s σ) {ct : U64} (hct : sched.cur_thread st s = ok ct) :
    ∀ s1 σ1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 → SlotsSame Z.th (L.mem s) (L.mem s1) →
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
      EJ (L := L) arI AR Z H Cs (L.ksb s) K s1 ar σ1 Z.G := by
  intro s1 σ1 hs1 hS hst
  have hDE1 := delE_restart hDE hS (ksub_of_eq (setThreadState_nks _ _) hst)
  obtain ⟨hcur, x, hk, hrun⟩ := J.curRunnable hni hct
  have htcb : Z.th ct = some .tcb := (J.xtop.curTcb hcur).1
  have e : σ1 = Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv := by
    rw [hcur, Notif.setThreadState_eq .restart hk] at hst
    have := congrArg (fun q => ((), σ1) ∈ q.1) hst
    simp only [Set.mem_singleton_iff, Prod.mk.injEq, true_and] at this
    exact of_eq_true this
  subst e
  refine ⟨hDE1, ?_⟩
  have h := XTopAt.restart J.xtop hcur hk hrun
  rw [hs1, WP.spec_ok] at h
  obtain ⟨hX1, hSS, hk1⟩ := h
  obtain ⟨hkb, hkz⟩ := kback_ksz_upd (σ' := Notif.stsAct (Notif.updK σ ct.bv
    (.tcb { x with tcbState := .restart })) ct.bv) hk (by rw [stsAct_kheap]; rfl)
  obtain ⟨Ac', Lst', D', R⟩ := hJ.restart s ar σ ct x s1 hcur hk htcb hrun hs1 Z H Cs Ac Lst D rfl J hX1
  exact ⟨Z.vs, Ac', Lst', D', J.cs_frame hk1 hX1 hkb (JCs.same J hSS hkz) R, hk1⟩

set_option maxHeartbeats 4000000 in
/-- **A Delete's or Revoke's outcome at `J`**: from `PInvPostW` at `EJ`,
`TopPostDMX` at `JAt` (the decode errors at the start's `JAtZ`). -/
theorem cn_del_topJ {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    {kb : U64} {K : Nat} {blk call don : Bool}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.CnodeInvocation} {res : core.result.Result Unit error.Exc × S × A}
    (hq : PInvPostW (L := L) Z.th σ Z.G m (EJ (L := L) arI AR Z H Cs kb K) s ar res) :
    TopPostDMX (L := L) (JAt (L := L) arI AR) σ blk call don
      (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeCNode m) s res := by
  obtain ⟨r, s', a'⟩ := res
  rcases hq with ⟨e, rfl, rfl, rfl, e', h1, h2⟩ |
    ⟨inv, hrun, σ1, hst, σ', G', hcase, -, -, -, -, V, Ac', Lst', D', J', -⟩
  · exact Or.inl ⟨e, rfl, rfl, ⟨e', run_liftME_err h1, Or.inl h2⟩, ⟨Z, H, Cs, Ac, Lst, D, J⟩⟩
  · have hX' := J'.xtop
    rcases hcase with ⟨rfl, hx⟩ | ⟨rfl, hx⟩
    · exact Or.inr ⟨_, DecOut.of_eq (run_liftME_ok hrun), σ1, hst, (.ok [], σ'),
        mem_bindE_ok hx (Set.mem_singleton _), ⟨Z.th, G', Or.inl ⟨rfl, rfl⟩, hX'.rel.1, hX'.rel.2.1,
          hX'.rel.2.2.1, hX'.rel.2.2.2.1, hX'.rel.2.2.2.2.1⟩, ⟨_, H, Cs, Ac', Lst', D', J'⟩⟩
    · exact Or.inr ⟨_, DecOut.of_eq (run_liftME_ok hrun), σ1, hst, (.error (), σ'),
        mem_bindE_err hx, ⟨Z.th, G', Or.inr ⟨rfl, rfl⟩, hX'.rel.1, hX'.rel.2.1,
          hX'.rel.2.2.1, hX'.rel.2.2.2.1, hX'.rel.2.2.2.2.1⟩, ⟨_, H, Cs, Ac', Lst', D', J'⟩⟩

set_option maxHeartbeats 4000000 in
/-- **`XCap` at `JAt` at the Revoke label** (25): `cnode_revoke_refinesW` at
`EJ` (`JDelHyp`, `rppHyp_fullW` of `JPreemptHyp`, `EJ.restart`), then
`cn_del_topJ`. -/
theorem decode_invocation_cnode_revokeJ (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hJ : JStepHyps (L := L) arI AR Z.th)
    (hJD : JDelHyp (L := L) arI AR Z.th) (hJP : JPreemptHyp (L := L) arI AR Z.th)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .cnodeRevoke)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (p r gs g : U64) (hwf : CapWf (.CNode p r gs g)) (hcv : CapValid Z.th (.CNode p r gs g))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ fl4_abi.label.CNodeRevoke length slot (.CNode p r gs g) blk call
      don fp buf extra slbl (args.map UScalar.bv) ci sl excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨K, hK, hK6, hDE⟩ := J.delE
  obtain ⟨⟨hR, hV, hM, hCd, hI⟩, -⟩ := And.intro hX.rel.2.1 hX.rel.2.2.1
  have htcb := (hX.curTcb hcur).1
  have hP := hX.rel.1
  have hfew : psiD (L.mem s) Z.G < 2 ^ 64 - 1 := by
    have := hDE.2.1 Z.G hM
    have : psiD (L.mem s) Z.G ≤ psiD (L.mem s) Z.G * (K + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  left
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact WP.spec_mono (cnode_revoke_refinesW arI Z.th s ar σ Z.G hR hV hP hM hCd slbl hlbl length buf ct hct
      args hlen hargs _ _ ⟨hwf, rfl⟩ hcv extra _ hI J.kern.act hcur htcb (EJ (L := L) arI AR Z H Cs (L.ksb s) K)
      psiD psiD_slotsSame (hJD Z H Cs (L.ksb s) K rfl hK hK6)
      (rppHyp_fullW arI (WJ (L := L) arI AR Z H Cs (L.ksb s)) Z.th K (hJP Z H Cs (L.ksb s) rfl))
      (EJ.restart arI hJ J hni hDE hct)
      (fun _ _ _ G1 hCR hE1 => ⟨hE1.1.2.2.1, hE1.1.2.2.2 G1 hCR.2.2.1⟩) hfew)
      fun res h => cn_del_topJ arI J h
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, ⟨Z, H, Cs, Ac, Lst, D, J⟩⟩

set_option maxHeartbeats 4000000 in
/-- **`XCap` at `JAt` at the Delete label** (26), for any cap: as
`decode_invocation_cnode_revokeJ`, by `cnode_delete_refinesW` at `EJ`. -/
theorem decode_invocation_cnode_deleteJ (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hJ : JStepHyps (L := L) arI AR Z.th)
    (hJD : JDelHyp (L := L) arI AR Z.th)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .cnodeDelete)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (p r gs g : U64) (hwf : CapWf (.CNode p r gs g)) (hcv : CapValid Z.th (.CNode p r gs g))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ fl4_abi.label.CNodeDelete length slot (.CNode p r gs g) blk call
      don fp buf extra slbl (args.map UScalar.bv) ci sl excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨K, hK, hK6, hDE⟩ := J.delE
  obtain ⟨⟨hR, hV, hM, hCd, hI⟩, -⟩ := And.intro hX.rel.2.1 hX.rel.2.2.1
  have htcb := (hX.curTcb hcur).1
  have hP := hX.rel.1
  left
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact WP.spec_mono (cnode_delete_refinesW arI Z.th s ar σ Z.G hR hV hP hM hCd slbl hlbl length buf ct hct
      args hlen hargs _ _ ⟨hwf, rfl⟩ hcv extra _ hI J.kern.act hcur htcb (EJ (L := L) arI AR Z H Cs (L.ksb s) K)
      psiD (hJD Z H Cs (L.ksb s) K rfl hK hK6) (EJ.restart arI hJ J hni hDE hct)
      (fun _ _ _ G1 hCR hE1 => ⟨hE1.1.2.2.1, hE1.1.2.2.2 G1 hCR.2.2.1⟩))
      fun res h => cn_del_topJ arI J h
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, ⟨Z, H, Cs, Ac, Lst, D, J⟩⟩

set_option maxHeartbeats 4000000 in
/-- **The CNode cap, `JAt` after**: the copy, mint, move, mutate and rotate
labels by their primitive steps (`decode_invocation_cnode_copyXS`,
`Steps.jat` with `JStepHyps`), Revoke and Delete by the deletion at `J`
(`decode_invocation_cnode_{revoke,delete}J`: `JDelHyp` from the deletion
loop's named steps `JDelParts` [J], `JDelHyp.of_parts`), the per-op premise (`JPostHyp` [W]) only at the other labels
(CancelBadgedSends, the invalid ones). -/
theorem decode_invocation_cnodeJ_steps (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hG : CsGlobal (L := L) arI AR Z.th)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI) (hJ : JStepHyps (L := L) arI AR Z.th)
    (hJDP : JDelParts (L := L) arI AR Z.th)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = cnodeLabelOf lbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl) (p r gs g : U64)
    (hsc : capV (L.mem s) (cslotAddr sl) = .CNode p r gs g)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel2 Z.th (L.mem s) x0 x1 (excaps.map Prod.fst))
    (hrun : ∀ xt, σ.kheap ct.bv = some (.tcb xt) → tsCode xt.tcbState < 3)
    (hZ : ∀ Z' : XSets, XTopAt (L := L) AR Z' s ar σ → KsApart Z'.N Z'.T Z'.E Z'.R Z'.B (L.ksb s) ∧
      BufWordRel Z'.T (L.mem s) σ ∧ IPlaced Z'.N Z'.T Z'.E Z'.R Z'.B)
    (hQ : ∀ e, Sched.EpQPre σ e)
    (hE : ∀ (Z' : XSets) (e b : U64) (sl : Fl4Spec.CslotPtr), XTopAt (L := L) AR Z' s ar σ → AbsSlot Z.th sl →
      capV (L.mem s) (cslotAddr sl) = .Endpoint e b true true true true → e ∈ Z'.E)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hR : ¬ (25 ≤ lbl.val ∧ lbl.val ≤ 26) → ¬ (28 ≤ lbl.val ∧ lbl.val ≤ 32) →
      JPostHyp (L := L) arI AR s ar σ lbl length (cslotAddr sl) (.CNode p r gs g) blk call don fp buf extra slbl
        (args.map UScalar.bv) ci sl excaps buffer ct) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length (cslotAddr sl) (.CNode p r gs g) blk call don fp buf extra
      slbl (args.map UScalar.bv) ci sl excaps buffer ct := by
  have hX := J.xtop
  have hJD := JDelHyp.of_parts arI hJDP
  have hJP := hJDP.pp
  obtain ⟨hwf, hcv⟩ := slot_cap_wf hX hAs hsc
  by_cases hcp : 28 ≤ lbl.val ∧ lbl.val ≤ 32
  · obtain ⟨hcur, -⟩ := J.curEq hct
    exact decode_invocation_cnode_copyXS arI s ar σ hX (J.curRun.run hni) ⟨Z, H, Cs, Ac, Lst, D, J⟩
      (fun _ _ _ h => Steps.jat arI hARI.toMask hJ h rfl J) (fun _ _ _ h => JAt.xtop arI h) lbl hcp slbl hlbl
      length buf ct hct args hlen hargs p r gs g hwf hcv ⟨cslotAddr sl, hAs.isSlot, hsc⟩ extra x0 x1 hx0 hx1
      excaps hex J.kern.act hcur (cslotAddr sl) blk call don fp ci sl buffer
  by_cases hrd : 25 ≤ lbl.val ∧ lbl.val ≤ 26
  · rcases (show lbl.val = 25 ∨ lbl.val = 26 by omega) with h | h
    · have e : lbl = fl4_abi.label.CNodeRevoke := UScalar.eq_of_val_eq (by rw [h, lbl_revoke_val])
      subst e
      exact decode_invocation_cnode_revokeJ arI s ar σ J hni hJ hJD hJP slbl (by rw [hlbl]; simp [cnodeLabelOf])
        length buf ct hct args hlen hargs p r gs g hwf hcv extra excaps (cslotAddr sl) blk call don fp ci sl buffer
    · have e : lbl = fl4_abi.label.CNodeDelete := UScalar.eq_of_val_eq (by rw [h, lbl_delete_val])
      subst e
      exact decode_invocation_cnode_deleteJ arI s ar σ J hni hJ hJD slbl (by rw [hlbl]; simp [cnodeLabelOf])
        length buf ct hct args hlen hargs p r gs g hwf hcv extra excaps (cslotAddr sl) blk call don fp ci sl buffer
  · exact decode_invocation_cnodeJ_step arI s ar σ J hni hG hARI hT lbl slbl hlbl length buf ct hct args hlen hargs
      sl hAs p r gs g hsc extra x0 x1 hx0 hx1 excaps hex hrun hZ hQ hE blk call don fp ci buffer (hR hrd hcp)

end

end

end Fl4Proofs.P3
