/-
P3 (DESIGN.md §9), IPC: **the endpoint transfers' scheduler tails on `IRel`**
(`IpcEpTailHyps` for `SRT … SRE`).

* `unblock_irel`: `unblock_sporadic` (the same body in the endpoint and
  notification code) refines the spec's sporadic unblock check on `IRel`,
  keeping the merged footprint and view: the SC's sporadic test and
  `unblock_check` (`unblock_check_refines`, its writes `unblock_check_scw`),
  lifted by `sc_step_lift`.
* `specSporadicAssert_eq`: the spec's assert form of the check
  (`receive_ipc`'s sender) is its test form (`specUnblock`); both run
  `refill_unblock_check` exactly when the SC is sporadic and not the current
  one. `nks_specUnblock`: the check changes only SC objects, so keeps every
  TCB (`IpcEpTailHyps.sporadicSc`).
* `ipcEpTailHyps_top`: every field of `IpcEpTailHyps`; named: the spec's
  switch target ready (`ActReady`, l4v `valid_sched`'s
  `weak_valid_sched_action`) on `IRel`, which `possible_switch_to` needs.
-/
import Fl4Proofs.P3.IpcSchedLift
import Fl4Proofs.P3.IpcReply
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

/-! ## The spec's sporadic check -/

section Spec
open Fl4Spec

/-- The assert form of the spec's sporadic check is its test form. -/
theorem specSporadicAssert_eq (t : ObjRef) : specSporadicAssert t = specUnblock t := by
  unfold specSporadicAssert specUnblock ifSporadicCurScAssertRefillUnblockCheck ifSporadicCurScTestRefillUnblockCheck
    ifCondRefillUnblockCheck
  congr 1; funext o
  cases o with
  | none => rfl
  | some p =>
    simp only [NonDet.maybeM]
    congr 1; funext sc; congr 1; funext cur; congr 1; funext g
    unfold NonDet.when
    split_ifs <;> first | rfl | (exfalso; simp_all) | simp_all

theorem nks_specUnblock (t : ObjRef) : NKS (specUnblock t) := by
  unfold specUnblock getTcbObjRef threadGet ifSporadicCurScTestRefillUnblockCheck ifCondRefillUnblockCheck
  refine nks_bind ?_ (fun o => ?_)
  · nks_auto
  · cases o with
    | none => exact nks_pure' _
    | some p =>
      simp only [NonDet.maybeM]
      refine nks_bind (nks_getSchedContext _) (fun _ => nks_bind (nks_gets _) (fun _ =>
        nks_bind (nks_pure _) (fun _ => nks_when (nks_when (nks_refillUnblockCheck _)))))

end Spec

/-! ## `unblock_sporadic` on `IRel` -/

section Unblock
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

theorem endpoint_unblock_sporadic_eq (s : S) (t : U64) :
    endpoint.unblock_sporadic st s t = notification.unblock_sporadic st s t := rfl

set_option maxHeartbeats 4000000 in
/-- **`unblock_sporadic` on `IRel`**, keeping the merged footprint and view. -/
theorem unblock_irel (hP0 : IPlaced N T E R B) (s : S) (σ : Fl4Spec.State Unit)
    (hX : IRel st th cr N T C E R B c s σ) (t : U64) (ht : t ∈ T) :
    notification.unblock_sporadic st s t ⦃ s' => ∃ σ', specUnblock t.bv σ = ({((), σ')}, False) ∧
      Agree (L.mem s) (L.mem s') (IFoot N T E R B) ∧ IKView σ σ' ∧ IRel st th cr N T C E R B c s' σ' ⦄ := by
  have hS := hX.2.2.1
  have hA := hX.2.2.2
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨xt, hkt, -, -, hsct, -⟩ := hs.tcb t ht
  have hspec0 : specUnblock t.bv σ = (Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit)
      (optRef (L.mem s (scA t)))) σ := by
    unfold specUnblock Fl4Spec.getTcbObjRef
    rw [nd_bind_one (threadGet_eq _ hkt), hsct]
  have skip : (Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit) (optRef (L.mem s (scA t)))) σ =
      ({((), σ)}, False) → ∃ σ', specUnblock t.bv σ = ({((), σ')}, False) ∧
        Agree (L.mem s) (L.mem s) (IFoot N T E R B) ∧ IKView σ σ' ∧ IRel st th cr N T C E R B c s σ' :=
    fun h => ⟨σ, by rw [hspec0, h], Agree.rfl', IKView.refl _, hX⟩
  unfold notification.unblock_sporadic
  step with Fl4Proofs.P1.obj.Tcb.sc.spec as ⟨i2, hi2⟩
  step with sporadic.sc_sporadic.spec' as ⟨b, b_post⟩
  subst hi2
  by_cases h0 : L.mem s (scA t) = 0#u64
  · have hb : b = false := by rw [b_post]; simp [h0]
    simp only [hb, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact skip (by rw [h0, optRef_zero]; rfl)
  have hscC := hs.scMem t ht h0
  obtain ⟨y, n, hky, hy⟩ := hs.scs _ hscC
  have hsp : (y.scSporadic = true) ↔ L.mem s (scW (L.mem s (scA t)) 64#u64) ≠ 0#u64 := by
    rw [hy.sporadic]; simp
  have hif : Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit) (optRef (L.mem s (scA t))) σ =
      (if y.scSporadic = true ∧ (L.mem s (scA t)).bv ≠ σ.curSc then
        Fl4Spec.refillUnblockCheck (L.mem s (scA t)).bv σ else ({((), σ)}, False)) := by
    rw [Notif.optRef_ne h0]
    unfold Fl4Spec.ifSporadicCurScTestRefillUnblockCheck Fl4Spec.ifCondRefillUnblockCheck
    simp only [Fl4Spec.NonDet.maybeM]
    rw [nd_bind_one (getSchedContext_eq hky), nd_gets_bind, nd_pure_bind']
    simp only [Fl4Spec.NonDet.when]
    by_cases e : y.scSporadic = true ∧ (L.mem s (scA t)).bv ≠ σ.curSc
    · simp only [e, ne_eq, not_false_eq_true, forall_const, and_self, ↓reduceIte, Option.some.injEq,
        Bool.false_eq_true, IsEmpty.forall_iff]
    · simp only [ne_eq, forall_const, ↓reduceIte, Option.some.injEq]
      rw [ite_f (c := y.scSporadic = true ∧ ¬ (L.mem s (scA t)).bv = σ.curSc) (by simpa only [ne_eq] using e),
        ite_f (c := y.scSporadic = true ∧ ¬ (L.mem s (scA t)).bv = σ.curSc) (by simpa only [ne_eq] using e)]
      rfl
  by_cases hsp' : L.mem s (scW (L.mem s (scA t)) 64#u64) ≠ 0#u64
  swap
  · have hb : b = false := by rw [b_post]; simp [h0]; simpa using hsp'
    simp only [hb, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact skip (by rw [hif, ite_f (fun h => hsp' (hsp.1 h.1))])
  have hb : b = true := by rw [b_post]; simp [h0, hsp']
  simp only [hb, ↓reduceIte]
  step with sched.cur_sc.spec' as ⟨s1, s1_post⟩
  rw [sc_ne_eq]
  simp only [bind_ok]
  rw [s1_post, hc.cur]
  by_cases e : L.mem s (scA t) = nodeW st s c layout.node.CUR_SC
  · simp only [e, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact skip (by rw [hif, ite_f]; rw [e, ← hs.curSc]; simp)
  · simp only [e, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
    refine WP.spec_mono (WP.spec_and (unblock_check_refines s σ hS hscC (hy.spor hsp')) (unblock_check_scw hS hscC (hy.spor hsp'))) ?_
    rintro s' ⟨⟨σ', he, -, -, hS'⟩, hW⟩
    have hK := nks_refillUnblockCheck _ σ ((), σ') (by rw [he]; rfl)
    refine ⟨σ', ?_, fun a ha hf => hW.mem_eq ha (fun hw => scw_not_ifoot hP0 hS hA hw hf), hK.ikview,
      sc_step_lift hP0 hX (hW.mono fun _ h => Or.inl h) hK hS'⟩
    rw [hspec0, hif, ite_t ⟨hsp.2 hsp', by rw [hs.curSc]; exact bv_ne e⟩, he]

end Unblock

/-! ## `IpcEpTailHyps` -/

section Tail
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- **`ActReadyW` gives `ActReady`**: a schedulable target's SC is active,
hence ready and sufficient. -/
theorem actReady_of_w {σ : Fl4Spec.State Unit} (h : SVK.ActReadyW σ) : ActReady σ := by
  intro u hu hs
  obtain ⟨x, scp, y, n, hk, hsc, -, hky, hact, -⟩ := Sched.schedulable_inv hs
  obtain ⟨hne, hsf, hrd⟩ := h u hu x scp y n hk hsc hky hact
  exact ⟨x, scp, hk, hsc, by rw [Sched.getScRefillSufficient_eq hky hne, hsf],
    by rw [Sched.getScRefillReady_eq hky hne, hrd]⟩

/-- **`ActReady` after the woken thread's sporadic check** from `WakeOK`. -/
theorem actReady_unblock {σ σ1 : Fl4Spec.State Unit} {t : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb}
    (hk : σ.kheap t = some (.tcb x)) (hW : SVK.WakeOK σ t)
    (hu : specUnblock t σ = ({((), σ1)}, False)) : ActReady σ1 :=
  actReady_of_w (SVK.unblock_wake hk _ _ hW (by
    show ((), σ1) ∈ (specUnblock t σ).1
    rw [hu]; exact Set.mem_singleton _)).1

set_option maxHeartbeats 1000000 in
/-- **`IpcEpTailHyps` for `SRT … SRE`**: the sporadic check by
`unblock_irel`, the switch by `switch_top`, the switch target ready after
the check by `WakeOK` (`actReady_unblock`). -/
theorem ipcEpTailHyps_top (hP0 : IPlaced N T E R B) :
    IpcEpTailHyps st A N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)) := by
  have sw : ∀ s (a : A) σ (t : U64), IpcRel N T E R B (L.mem s) σ →
      SRT st th cr N T C E R B c (SRE st N T C E R B c) s σ → t ∈ T → SVK.ActReadyW σ →
      (do
        let s1 ← sched.possible_switch_to st s t
        ok (s1, a)) ⦃ r => r.2 = a ∧ TailPostI st N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c))
          s σ (Fl4Spec.possibleSwitchTo t.bv) r.1 ⦄ := by
    intro s a σ t hR hS ht hA
    refine WP.spec_bind (switch_top hP0 s σ hR hS (actReady_of_w hA) t ht) ?_
    rintro s1 ⟨σ1, heq, -, hf, hv, hS1⟩
    rw [WP.spec_ok]
    exact ⟨rfl, by rw [heq]; exact id, σ1, by rw [heq]; rfl, hf, hv, hS1⟩
  refine ⟨fun s a σ t hR hS ht hW => ?_, fun s σ t hR hS ht => ?_, sw, fun σ σ' t x h hk => ?_⟩
  · rw [endpoint_unblock_sporadic_eq]
    refine WP.spec_bind (unblock_irel hP0 s σ ⟨hR, hS⟩ t ht) ?_
    rintro s1 ⟨σ1, hu, hf1, hv1, hR1, hS1⟩
    have hR1' : IpcRel N T E R B (L.mem s1) σ1 := hR1
    obtain ⟨x, hk, -⟩ := hR.tcb t ht
    refine WP.spec_mono (sw s1 a σ1 t hR1' hS1 ht (SVK.unblock_wake hk _ _ hW (by
      show ((), σ1) ∈ (specUnblock t.bv σ).1
      rw [hu]; exact Set.mem_singleton _)).1) ?_
    rintro r ⟨ha, hn, σ2, hm, hf2, hv2, hS2⟩
    have hsp : specWakeTailE t.bv σ = Fl4Spec.possibleSwitchTo (Z := Unit) t.bv σ1 := by
      have e : specWakeTailE t.bv = (specUnblock t.bv >>= fun _ => Fl4Spec.possibleSwitchTo t.bv) := by
        unfold specWakeTailE specUnblock; rw [nd_bind_assoc_fun]
      rw [e, nd_bind_one hu]
    refine ⟨ha, by rw [hsp]; exact hn, σ2, by rw [hsp]; exact hm, hf1.trans hf2, hv1.trans hv2, hS2⟩
  · rw [endpoint_unblock_sporadic_eq]
    refine WP.spec_mono (unblock_irel hP0 s σ ⟨hR, hS⟩ t ht) ?_
    rintro s' ⟨σ', hu, hf, hv, -, hS'⟩
    exact ⟨σ', by rw [specSporadicAssert_eq]; exact hu, hf, hv, hS'⟩
  · rw [specSporadicAssert_eq] at h
    have hK := nks_specUnblock t.bv σ ((), σ') (by rw [h]; rfl)
    exact ⟨x, hK.fwd hk (by intros; nofun), rfl⟩

end Tail

end

end Fl4Proofs.P3.Ipc
