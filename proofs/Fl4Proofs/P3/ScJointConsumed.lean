/-
P3 (DESIGN.md §9), scheduling contexts: **SchedContext Consumed's reply at
`J`** (`sc_consumedReplyJ`: `ScReplyJ` for the Consumed label, so the
premise is left only for an at-once YieldTo).

FL4's Consumed branch: the decode's prefix (the remote stall a no-op by
`hback`), the caller's restart (`JAtZ.restartJ`), `set_consumed` of the SC
to the caller (with the message when a call: XTopJointYield's
`JAtZ.setConsumedJ`; else only `update_consumed`: `JAtZ.updConsumedJ`, an
SC register-frame step as `setConsumedJ`'s), then `Running`
(`JAtZ.runJ`). The spec's restart, `return_consumed` and reply tail
(`reply_from_kernel` when a call, `Running`) end in the same state: the
spec's `set_consumed` is `return_consumed`'s update then
`reply_from_kernel` of its word.

Named [P]: the platform's `ticks_to_us`, `getMaxTicksToUs` (`hmax`, `htu`)
and `ArchTotal` (P1's `update_consumed.blk`), as `JAtZ.setConsumedJ`'s.
-/
import Fl4Proofs.P3.ScJointUnbind
import Fl4Proofs.P3.XTopJointYield
import Fl4Proofs.P3.XTopJointReply
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- The spec's `update_consumed` of an SC: one outcome. -/
theorem updConsumed_one {σ : Fl4Spec.State Unit} {p : Fl4Spec.ObjRef} {z : Fl4Spec.SchedContext} {n : Nat}
    (hks : σ.kheap p = some (.schedContext z n)) :
    ∃ c v, Fl4Spec.schedContextUpdateConsumed (Z := Unit) p σ =
      ({(c, updSc σ p (Fl4Spec.scConsumedUpdate (fun _ => v) z) n)}, False) := by
  unfold Fl4Spec.schedContextUpdateConsumed
  rw [nd_bind_one (getSchedContext_eq hks), nd_pure_bind']
  split_ifs
  · rw [nd_bind_one (updateSchedContext_eq hks _)]; exact ⟨_, _, rfl⟩
  · rw [nd_bind_one (updateSchedContext_eq hks _)]; exact ⟨_, _, rfl⟩

set_option maxHeartbeats 8000000 in
/-- **`update_consumed` of an SC at `J`** (module docstring): a register
frame step (`JAtZ.reg_frame`), the SC's consumed word its only write. -/
theorem JAtZ.updConsumedJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hAT : P0.ArchTotal arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) {p t : U64} (hpC : p ∈ Z.C)
    (ht : t ∈ Z.T) :
    schedcontext.update_consumed st arI s a p ⦃ r => ∃ σ1 c,
      Fl4Spec.schedContextUpdateConsumed (Z := Unit) p.bv σ = ({(c, σ1)}, False) ∧
      ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D r.2 a σ1 ⦄ := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨z, n, hkz, hz⟩ := hs.scs p hpC
  obtain ⟨x, hkx, -⟩ := hs.tcb t ht
  have hI := J.xtop.irelK J.ks J.buf
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hpS : p ∈ P1.Heap.scs H := ⟨_, (hJ.sc p z n (J.c0 p hpC) hkz).2⟩
  have hal : P1.Aligned (scW p 8#u64) := (hz.hdr (K := 8#u64) (by simp) (by simp)).1
  refine WP.spec_mono (WP.spec_and (update_consumed_irel (ar := arI) J.ip s a σ hI hpC hkz hmax htu)
    (P1.schedcontext.update_consumed.blk hAT s a p J.blk hpS)) ?_
  rintro ⟨cv, s1⟩ ⟨⟨hs1, -, he, hI1⟩, hP1⟩
  simp only at hs1 he hI1 hP1
  set w : Fl4Spec.SchedContext := { z with scConsumed := (0#u64 : U64).bv } with hwd
  have hpt : p.bv ≠ t.bv := fun e => by rw [e, hkx] at hkz; cases hkz
  have hk1 : (updSc σ p.bv w n).kheap t.bv = some (.tcb x) := by
    simp only [updSc, updK, Function.update_of_ne hpt.symm]; exact hkx
  have eS : updK (updSc σ p.bv w n) t.bv (.tcb x) = updSc σ p.bv w n := by
    unfold updK; rw [← hk1, Function.update_eq_self]
  have hA := QKY.upd2 (w := w) (x' := x) hkz hkx rfl rfl
  have hyk := ykeep_upd2 (w := w) (x' := x) hkz hkx rfl rfl
  rw [eS] at hA hyk
  have hInv := J.inv.scFields (y' := w) hkz rfl rfl rfl rfl
  rw [hs1] at hI1 hP1 ⊢
  have hw : P1.WritesIn st s (L.wr s (scW p 8#u64) 0#u64) (RegCW Z.T Z.C) :=
    (P1.writesIn_wr (st := st) (s := s) (v := 0#u64) hal).mono fun b hb => Or.inr ⟨p, hpC, hb⟩
  obtain ⟨V, J1⟩ := J.reg_frame hI1 hw hA hyk hInv hP1.1 hP1.2.1
  exact ⟨_, _, he, V, J1⟩


set_option maxHeartbeats 16000000 in
/-- **Consumed's reply at `J`** (module docstring): `ScReplyJ` for the
Consumed label. -/
theorem sc_consumedReplyJ (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) (hAT : P0.ArchTotal arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = scLabelOf lbl)
    (l44 : lbl = fl4_abi.label.SchedContextConsumed)
    {sc : U64} (sb : U64) (hsc : sc ∈ Z.C)
    (hback : L.mem s (scW sc 24#u64) ≠ 0#u64 →
      L.mem s (scW sc 24#u64) ∈ Z.T ∧ L.mem s (P1.scA (L.mem s (scW sc 24#u64))) = sc ∧
      (L.mem s (scW sc 24#u64)).bv ≠ σ.idleThread)
    {ct : U64} (hct : sched.cur_thread st s = ok ct)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (length slot buf : U64) (blk call don fp : Bool) :
    ScReplyJ (L := L) (arI := arI) AR s a σ lbl length slot sc sb blk call don fp buf extra slbl excaps ct := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R', hc, hs⟩ := hS.lists
  have hct' : ct = nodeW st s Z.c layout.node.CUR_THREAD := by
    have h := sched.cur_thread.spec' (L := L) s
    rw [hct, WP.spec_ok, hc.cur] at h; exact h
  have hctT : ct ∈ Z.T := hct' ▸ hc.curT
  have hg : Fl4Spec.genInvocationType slbl = .schedContextConsumed := by
    rw [hlbl, l44]; unfold scLabelOf; simp
  have hinv : ∀ inv, (Fl4Spec.decodeSchedContextInvocation (Z := Unit) slbl sc.bv (excaps.map Prod.fst)).run σ =
      ({(.ok inv, σ)}, False) → inv = .invokeSchedContextConsumed sc.bv := by
    intro inv hrun
    simp only [Fl4Spec.decodeSchedContextInvocation, hg] at hrun
    exact (retP_pure (P := fun v => v = Fl4Spec.SchedContextInvocation.invokeSchedContextConsumed sc.bv) rfl :
      RetP _ (Fl4Spec.NonDetE.returnOk (Fl4Spec.SchedContextInvocation.invokeSchedContextConsumed sc.bv))).of_run hrun
  -- the caller's restart
  obtain ⟨s1, σ1, x, -, he0, -, hcur, eσ1, -, -, -, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  rw [hcur] at he0
  have hk1 : σ1.kheap ct.bv = some (.tcb { x with tcbState := .restart }) := by
    rw [eσ1, stsAct_kheap]; simp [updK]
  -- the spec's update of the SC's consumed time
  obtain ⟨Q1, R1, hc1, hs1'⟩ := J1.xtop.fin.1.1.1.lists
  obtain ⟨z, n, hkz, -⟩ := hs1'.scs sc hsc
  obtain ⟨c, v, hv⟩ := updConsumed_one hkz
  set σu := updSc σ1 sc.bv (Fl4Spec.scConsumedUpdate (fun _ => v) z) n with hσu
  have hsct : ct.bv ≠ sc.bv := fun e => by rw [e, hkz] at hk1; cases hk1
  have hku : σu.kheap ct.bv = some (.tcb { x with tcbState := .restart }) := by
    simp only [hσu, updSc, updK, Function.update_of_ne hsct]; exact hk1
  have hrc : Fl4Spec.returnConsumed (Z := Unit) sc.bv σ1 = ({(Fl4Spec.wordsFromTime c, σu)}, False) := by
    unfold Fl4Spec.returnConsumed; rw [nd_bind_one hv]; rfl
  have hsetc : Fl4Spec.setConsumed (Z := Unit) sc.bv ct.bv σ1 =
      Fl4Spec.replyFromKernel (Z := Unit) ct.bv (0, Fl4Spec.wordsFromTime c) σu := by
    unfold Fl4Spec.setConsumed; rw [nd_bind_one hv]
  -- FL4's `set_consumed`, with the spec's reply when a call
  have hSC : schedcontext.set_consumed st arI s1 a sc ct call ⦃ s3 => ∃ σ2,
      Fl4Spec.NonDet.when (call = true) (Fl4Spec.replyFromKernel (Z := Unit) ct.bv (0, Fl4Spec.wordsFromTime c)) σu =
        ({((), σ2)}, False) ∧ ∃ y, σ2.kheap ct.bv = some (.tcb y) ∧ y.tcbState = .restart ∧
      ∃ (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac' Lst' D' s3 a σ2 ⦄ := by
    cases call
    · unfold schedcontext.set_consumed
      refine WP.spec_bind (J1.updConsumedJ hAT hmax htu hsc hctT) ?_
      rintro ⟨cv, s3⟩ ⟨σ2, c', he2, V, J2⟩
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hv] at he2
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst he2))
      refine (WP.spec_ok _).2 ⟨σu, ?_, _, hku, rfl, V, Ac1, Lst1, D1, J2⟩
      unfold Fl4Spec.NonDet.when; rw [ite_eq_right (by simp)]; rfl
    · refine WP.spec_mono (J1.setConsumedJ hAT hmax htu hsc hctT) ?_
      rintro s3 ⟨σ2, he2, -, V, J2⟩
      obtain ⟨v', w', he2'⟩ := Sched.setConsumed_shape hkz hk1
      have eσ2 := the_result he2' he2
      refine ⟨σ2, ?_, Endp.replyTcb { x with tcbState := .restart } w', by rw [eσ2]; simp [updK], rfl,
        V, Ac1, Lst1, D1, J2⟩
      unfold Fl4Spec.NonDet.when; rw [ite_eq_left rfl, ← hsetc]; exact he2
  -- the decode
  unfold ScReplyJ syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  swap
  · simp only [↓reduceIte, WP.spec_ok]
    intro h; cases h
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold schedcontext.decode
  step with P1.obj.Sc.tcb.spec as ⟨i, hi⟩
  rw [scTcbA_eq] at hi
  subst hi
  refine WP.spec_bind (show _ ⦃ r => r = (s, a) ⦄ from ?_) ?_
  · by_cases h0 : L.mem s (scW sc 24#u64) = 0#u64
    · have : (L.mem s (scW sc 24#u64) != 0#u64) = false := by simp [h0]
      simp only [this, Bool.false_eq_true, ↓reduceIte]; exact (WP.spec_ok _).mpr rfl
    · have : (L.mem s (scW sc 24#u64) != 0#u64) = true := by simp [h0]
      simp only [this, ↓reduceIte]; exact remote_tcb_stall_id (ar := arI) a hS (hback h0).1
  intro r hr
  subst hr
  show (sched.cur_thread st s >>= _) ⦃ _ ⦄
  rw [hct, bind_tc_ok, ite_eq_left l44, hs1]
  simp only [bind_ok]
  refine WP.spec_bind hSC ?_
  rintro s3 ⟨σ2, hrf, y, hk2, hrs2, V, Ac2, Lst2, D2, J2⟩
  refine WP.spec_bind (J2.runJ hctT hk2 hrs2) ?_
  rintro s4 ⟨Lst4, D4, J4⟩
  rw [WP.spec_ok]
  intro _ _ inv σ0 data σa σb hrun he0' he1 htail
  have e := hinv inv hrun
  subst e
  rw [he0] at he0'
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst he0'))
  have he1' : Fl4Spec.returnConsumed (Z := Unit) sc.bv σ1 = ({(data, σa)}, False) := he1
  rw [hrc] at he1'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst he1'))
  rw [specTail_of_restart hku rfl, nd_bind_one hrf, Notif.setThreadState_eq .running hk2] at htail
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 htail)
  exact ⟨_, _, _, _, _, _, J4⟩

end

end

end Fl4Proofs.P3
