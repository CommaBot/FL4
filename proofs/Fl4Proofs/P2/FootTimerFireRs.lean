/-
# P2 (p2lf): the fire case's tail after `awaken`, and its resume case

`schedule` splits at the state `Y` after `awaken` (`schedule_act_eq`): `actTail` is the rest (the action, `schedSw`
for an action other than `RESUME_CURRENT`, `schedRes`).

* `AwTailG`: `actTail`, `activate_thread`, `cur_thread` and `vcpu.check` on the guarded store `gS` are the real runs
  from `Y` on; `fire_tail_of_aw`: with the guarded `awaken` it gives `FireTailG` (`P2/FootTimerFireP`).
* `actTail.guard`: `actTail` on `gS` by its shape (as `sched.schedule.guard_sw`).
* `aw_tail_resume`: `AwTailG` at a state whose action is `RESUME_CURRENT` and whose current thread runs on the
  current SC, from P1 facts at `Y` (as `fire_tail_nw`'s end, stated at `Y`: `resume_hsw_hfr`, `schedTail_fp`,
  `activate_thread.gw`, `vcpu.check.guard_nvm`). Used for a waking signal that leaves the action `RESUME_CURRENT`.

No named premises.
-/
import Fl4Proofs.P2.FootTimerFireNw
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (ScAcc rhA tmA RdHead NodeSt bind_guard_congr)

/-- `schedule`'s part after `awaken`, on any store. -/
def actTail {S : Type _} {A : Type _} (M : machine.Store S) (ar : machine.Arch A) (Y : S) (a : A) :
    Result (S × A) := do
  let act ← sched.action M Y
  let (s3, a2) ← if act != sched.ACTION_RESUME_CURRENT then schedSw M ar Y a act else ok (Y, a)
  PathObl.LT.schedRes M ar s3 a2

theorem schedule_act_eq {S : Type _} {A : Type _} (M : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) :
    sched.schedule M ar s a = (do
      let (s1, a1) ← sched.awaken M ar s a
      actTail M ar s1 a1) := by
  rw [schedule_sw_eq]; rfl

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {T Cs Ω : Set U64}
variable {A : Type} (ar : machine.Arch A)

/-- The fire case's tail from the state `Y` after `awaken` on, on `gS`. -/
def AwTailG (st gS : machine.Store S) (ar : machine.Arch A) (Y : S) (a : A) : Prop :=
  actTail gS ar Y a = actTail st ar Y a ∧
    ∀ s4 a4, actTail st ar Y a = ok (s4, a4) →
      sched.activate_thread gS ar s4 a4 = sched.activate_thread st ar s4 a4 ∧
      ∀ s5 a5, sched.activate_thread st ar s4 a4 = ok (s5, a5) →
        sched.cur_thread gS s5 = sched.cur_thread st s5 ∧
        ∀ t, sched.cur_thread st s5 = ok t → vcpu.check gS ar s5 a5 t = vcpu.check st ar s5 a5 t

omit L in
theorem fire_tail_of_aw {gS : machine.Store S} {s3 Y : S} {a3 aY : A}
    (hg : sched.awaken gS ar s3 a3 = sched.awaken st ar s3 a3) (he : sched.awaken st ar s3 a3 = ok (Y, aY))
    (h : AwTailG st gS ar Y aY) : FireTailG st gS ar s3 a3 := by
  have e1 : sched.schedule st ar s3 a3 = actTail st ar Y aY := by
    rw [schedule_act_eq, he]; simp only [bind_ok]; rfl
  refine ⟨?_, fun s4 a4 e => ?_⟩
  · rw [schedule_act_eq, hg, he, e1]; simp only [bind_ok]; exact h.1
  · rw [e1] at e; exact h.2 s4 a4 e

variable {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]

/-- **`actTail` on the guarded store, by its shape.** -/
theorem actTail.guard (Y : S) (a : A)
    (rA : R (L.nodeAt Y (L.cpu Y) layout.node.SCHED_ACTION))
    (hsw : L.actionW Y ≠ sched.ACTION_RESUME_CURRENT →
      schedSw gS ar Y a (L.actionW Y) = schedSw st ar Y a (L.actionW Y))
    (hres : ∀ s3 a2, (if L.actionW Y != sched.ACTION_RESUME_CURRENT then schedSw st ar Y a (L.actionW Y)
        else ok (Y, a)) = ok (s3, a2) →
      PathObl.LT.schedRes gS ar s3 a2 = PathObl.LT.schedRes st ar s3 a2) :
    actTail gS ar Y a = actTail st ar Y a := by
  unfold actTail
  rw [PathObl.sched.action.guard (gS := gS) Y rA, eq_of_spec_fd (sched.action.spec (L := L) Y)]
  simp only [bind_ok]
  refine bind_guard_congr ?_ fun y hy => ?_
  · by_cases h : (L.actionW Y != sched.ACTION_RESUME_CURRENT) = true
    · rw [if_pos h, if_pos h]; exact hsw (bne_iff_ne.mp h)
    · rw [if_neg h, if_neg h]
  · obtain ⟨s3, a2⟩ := y
    simp only [Aeneas.Std.uncurry_apply_pair]
    exact hres s3 a2 hy

set_option maxHeartbeats 16000000 in
/-- **The tail after `awaken` when the action is `RESUME_CURRENT`** (module docstring). -/
theorem aw_tail_resume (hA : P0.ArchTotal ar) (Y : S) (a : A) {zc : Nat}
    (hcC : L.cpu Y ∈ Cs) (hN : NodePlaced st T Y (L.cpu Y)) (hT : TcbPlaced T)
    (homega : ∀ b ∈ Ω, OutsideObjs st T Cs Y b) (hct : L.curW Y ∈ T)
    (hsame : L.mem Y (scA (L.curW Y)) = L.cscW Y) (hc : SCq st Y Ω (L.cscW Y) zc)
    (hmx : L.rmax Y (L.cscW Y) ≠ 0#u64)
    (hNd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt Y (L.cpu Y) o) ∧ W (L.nodeAt Y (L.cpu Y) o))
    (hSc : ScAcc R W (L.cscW Y) zc)
    (hdt : R (core.num.U64.wrapping_add (L.ksb Y) layout.ks.DOMAIN_TIME))
    (hrs : L.mem Y (rhA (L := L) Y) ≠ 0#u64 → ∃ zr, L.mem Y (rhA (L := L) Y) ∈ T ∧
      R (scA (L.mem Y (rhA (L := L) Y))) ∧
      SCq st Y Ω (L.mem Y (scA (L.mem Y (rhA (L := L) Y)))) zr ∧
      L.rmax Y (L.mem Y (scA (L.mem Y (rhA (L := L) Y)))) ≠ 0#u64 ∧
      (∀ b, InSC (L.mem Y (scA (L.mem Y (rhA (L := L) Y)))) zr b → Aligned b → R b) ∧
      (L.mem Y (scA (L.mem Y (rhA (L := L) Y))) ≠ L.cscW Y →
        ∀ b, InSC (L.mem Y (scA (L.mem Y (rhA (L := L) Y)))) zr b → Outside b (L.cscW Y) zc) ∧
      (L.mem Y (scA (L.mem Y (rhA (L := L) Y))) = L.cscW Y → zr = zc))
    (htd : L.mem Y (tmA (L := L) Y) ≠ 0#u64 → L.mem Y (tmA (L := L) Y) ∈ T ∧
      R (core.num.U64.wrapping_add (L.mem Y (tmA (L := L) Y)) 3528#u64))
    (hact : L.actionW Y = sched.ACTION_RESUME_CURRENT)
    (hy0 : L.mem Y (yieldA (L.curW Y)) = 0#u64) (hnvm : L.mem Y (stA (L.curW Y)) ≠ sched.TS_RUNNING_VM)
    (haff : L.mem Y (affA (L.curW Y)) = L.cpu Y)
    (rYt : R (yieldA (L.curW Y))) (rSt : R (stA (L.curW Y))) (rFi : R (regA (L.curW Y) layout.reg.FAULT_IP))
    (wNi : W (regA (L.curW Y) layout.reg.NEXT_IP)) (rSc : R (scA (L.curW Y))) (rIq : R (inqA (L.curW Y)))
    (hwS : ∀ X, L.mem X (stA (L.curW Y)) = sched.TS_RESTART → L.mem X (affA (L.curW Y)) = L.cpu Y →
      gS.write X (stA (L.curW Y)) sched.TS_RUNNING = st.write X (stA (L.curW Y)) sched.TS_RUNNING) :
    AwTailG st gS ar Y a := by
  have ht' := hT _ hct
  have hres := resume_hsw_hfr (gS := gS) ar hA Y a hcC hN hT homega hct hsame hc hmx hNd hSc rSc hdt hrs htd
  have rMx : R (maxA (L.cscW Y)) := hSc.1 _ hc.2.2.2.2 hc.2.2.2.1
  have hacY : sched.action st Y = ok sched.ACTION_RESUME_CURRENT := by
    rw [eq_of_spec_fd (sched.action.spec (L := L) Y), hact]
  have eT : actTail st ar Y a = schedTail (st := st) ar Y a := by
    unfold actTail; rw [hacY]
    simp only [bind_ok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    rfl
  refine ⟨actTail.guard ar Y a (hNd _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])).1
    (fun h => absurd hact h) (fun s3' a2' e' => ?_), fun s4 a4 esc => ?_⟩
  · rw [hact, bne_self_eq_false, if_neg Bool.false_ne_true] at e'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (ok_inj_ff e')
    exact PathObl.LT.schedRes.guard ar Y a hNd hres.1 hres.2
  have hfp := schedTail_fp ar hA Y a (zc := zc)
    (B := fun b => (∀ K : U64, K.val < 4096 → b ≠ core.num.U64.wrapping_add (L.curW Y) K) ∧
      b ≠ L.nodeAt Y (L.cpu Y) layout.node.CUR_THREAD)
    hcC hN hT homega hct hsame hc
    (fun o ho h8 hz => by
      refine ⟨fun K hK => node_ne_field hN ho hct ht' hK, fun e => hz ?_⟩
      have e' := congrArg UScalar.val e
      rw [nodeAt_val hN ho, nodeAt_val hN (by rw [curth_val]; omega), curth_val] at e'
      omega)
    (fun b hb hin => by
      have ho := homega b (hc.2.1 b hb hin)
      exact ⟨fun K hK e => out_ne_field ho hct ht' hK (congrArg UScalar.val e).symm,
        fun e => out_ne_node ho hcC hN (by rw [curth_val]; omega) (congrArg UScalar.val e).symm⟩)
  rw [← eT, esc, WP.spec_ok] at hfp
  have w34 := hfp
  have e4N : ∀ o, L.nodeAt s4 (L.cpu s4) o = L.nodeAt Y (L.cpu Y) o := fun o => by
    rw [w34.2.1, nodeAt_of_ksb w34.1]
  have hcur4 : L.curW s4 = L.curW Y := by
    unfold LawfulStore.curW
    rw [w34.2.1, nodeAt_of_ksb w34.1,
      w34.mem_eq (nodeAt_aligned hN (by rw [curth_val]; omega) (by rw [curth_val])) (fun hb => hb.2 rfl)]
  have tK4 : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem s4 (core.num.U64.wrapping_add (L.curW Y) K) = L.mem Y (core.num.U64.wrapping_add (L.curW Y) K) :=
    fun K hK h8 => w34.mem_eq (field_aligned ht' hK h8) (fun hb => hb.1 K hK rfl)
  have hy4 : L.mem s4 (yieldA (L.curW Y)) = 0#u64 := by
    unfold yieldA; rw [tK4 _ (by simp) (by simp)]; exact hy0
  have hst4 : L.mem s4 (stA (L.curW Y)) = L.mem Y (stA (L.curW Y)) := by
    rw [stA_eq, tK4 _ (by simp) (by simp)]
  have sc4 : L.mem s4 (scA (L.curW Y)) = L.cscW Y := by
    rw [scA_eq, tK4 _ (by simp) (by simp), ← scA_eq]; exact hsame
  have aff4 : L.mem s4 (affA (L.curW Y)) = L.cpu Y := by
    unfold affA; rw [tK4 _ (by simp) (by simp)]; exact haff
  have hN4 : NodePlaced st T s4 (L.cpu s4) := by rw [w34.2.1]; exact hN.ksb w34.1
  have nrm4 : NodeSt (L := L) R W s4 := by
    unfold PathObl.NodeSt
    rw [e4N, e4N]
    exact ⟨(hNd _ (by rw [curth_val]; omega) (by rw [curth_val])).1,
      (hNd _ (by rw [act_val]; omega) (by rw [act_val])).1, (hNd _ (by rw [act_val]; omega) (by rw [act_val])).2⟩
  have eNx : regA (L.curW Y) layout.reg.NEXT_IP = core.num.U64.wrapping_add (L.curW Y) 368#u64 := by
    obtain ⟨K, hK, e⟩ := regA_eq ht' (r := layout.reg.NEXT_IP) (by simp [layout.reg.NEXT_IP])
    rw [e]
    congr 1
    apply UScalar.eq_of_val_eq
    rw [hK]
    simp [layout.reg.NEXT_IP]
  have aNx : Aligned (regA (L.curW Y) layout.reg.NEXT_IP) := by
    rw [eNx]; exact field_aligned ht' (by simp) (by simp)
  have sA : Aligned (stA (L.curW Y)) := by rw [stA_eq]; exact field_aligned ht' (by simp) (by simp)
  have aA : Aligned (affA (L.curW Y)) := field_aligned ht' (by simp) (by simp)
  have nNs : regA (L.curW Y) layout.reg.NEXT_IP ≠ stA (L.curW Y) := by
    rw [eNx, stA_eq]; exact tcb_word_ne ht' ht' (by simp) (by simp) (fun _ => by simp)
  have nNa : regA (L.curW Y) layout.reg.NEXT_IP ≠ affA (L.curW Y) := by
    rw [eNx]; exact tcb_word_ne ht' ht' (by simp) (by simp) (fun _ => by simp)
  have gac : sched.activate_thread gS ar s4 a4 = sched.activate_thread st ar s4 a4 :=
    activate_thread.gw ar s4 a4 hcur4 ht' hy4 nrm4 rYt rSt rFi wNi
      (fun hr pc => hwS _ (by rw [mem_wr_ne' aNx sA nNs]; exact hr) (by rw [mem_wr_ne' aNx aA nNa]; exact aff4))
      rSc (by rw [sc4]; exact rMx) rIq
  refine ⟨gac, fun s5 a5 eac => ?_⟩
  obtain ⟨w45, hst5⟩ := activate_fp ar hT hct hN4 hcur4 hy4 eac
  have e5N : ∀ o, L.nodeAt s5 (L.cpu s5) o = L.nodeAt Y (L.cpu Y) o := fun o => by
    rw [w45.2.1, nodeAt_of_ksb w45.1, e4N]
  have hst5' : L.mem s5 (stA (L.curW Y)) ≠ sched.TS_RUNNING_VM := by
    rcases hst5 with e | e
    · rw [e]; simp [sched.TS_RUNNING, sched.TS_RUNNING_VM]
    · rw [e, hst4]; exact hnvm
  have hcur5 : L.curW s5 = L.curW Y := by
    have e : L.curW s5 = L.curW s4 := by
      unfold LawfulStore.curW
      rw [w45.2.1, nodeAt_of_ksb w45.1]
      refine w45.mem_eq (nodeAt_aligned hN4 (by rw [curth_val]; omega) (by rw [curth_val])) ?_
      rintro (e | e | e)
      · exact tcb_node_ne hN4 hct ht' (by simp) (by rw [curth_val]; omega) e.symm
      · rw [stA_eq] at e
        exact tcb_node_ne hN4 hct ht' (by simp) (by rw [curth_val]; omega) e.symm
      · have e' := congrArg UScalar.val e
        rw [nodeAt_val hN4 (by rw [curth_val]; omega), nodeAt_val hN4 (by rw [act_val]; omega), curth_val,
          act_val] at e'
        omega
    rw [e, hcur4]
  refine ⟨PathObl.sched.cur_thread.guard s5
    (by rw [e5N]; exact (hNd _ (by rw [curth_val]; omega) (by rw [curth_val])).1), fun t et => ?_⟩
  rw [cur_thread_ok, hcur5] at et
  have et' := ok_inj_ff et
  subst et'
  exact vcpu.check.guard_nvm ar s5 a5 (L.curW Y) rSt hst5'

end main

end Fl4Proofs.P2
