/-
# P2: `schedule`'s resume tail on the guarded store, from P1 facts

`resume_hsw_hfr`: the premises `hsw` / `hfr` of `sched.schedule.guard_nodue` (p2io's `schedRes.guard`) at a
`schedule` state `X` whose current thread runs on the current SC (`switch_sched_context` with `i = c`, p2sl's
`switch_sched_context.guard`), from P1's facts at `X` (placement, the current SC's `SCq`, the release head's
SC `SCq` and disjointness from the current SC) and the guard sets covering this core's node words, the current
SC, the current thread's SC word, `DOMAIN_TIME`, the release head's SC word and SC, and the timer-min thread's
deadline. Between `set_action` and `set_next_interrupt`, `switch_sched_context` writes only this core's
`REPROGRAM` / `CONSUMED` / `CUR_SC` / `SCHED_ACTION` and the current SC (`switch_sched_context.fp`), so these
reads stay where they were.

No named premises.
-/
import Fl4Proofs.P2.FootTimerSetG
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (guard guard_read ScAcc rhA tmA RdHead)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
variable {T Cs Ω : Set U64}
variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **`hsw` / `hfr` of `schedule.guard_nodue` at a resume state** (module docstring). -/
theorem resume_hsw_hfr (hA : P0.ArchTotal ar) (X : S) (a : A) {zc : Nat}
    (hcC : L.cpu X ∈ Cs) (hN : NodePlaced st T X (L.cpu X)) (hT : TcbPlaced T)
    (homega : ∀ b ∈ Ω, OutsideObjs st T Cs X b) (hct : L.curW X ∈ T)
    (hsame : L.mem X (scA (L.curW X)) = L.cscW X) (hc : SCq st X Ω (L.cscW X) zc)
    (hmx : L.rmax X (L.cscW X) ≠ 0#u64)
    (hNd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt X (L.cpu X) o) ∧ W (L.nodeAt X (L.cpu X) o))
    (hSc : ScAcc R W (L.cscW X) zc) (hsc : R (scA (L.curW X)))
    (hdt : R (core.num.U64.wrapping_add (L.ksb X) layout.ks.DOMAIN_TIME))
    (hrs : L.mem X (rhA (L := L) X) ≠ 0#u64 → ∃ zr, L.mem X (rhA (L := L) X) ∈ T ∧
      R (scA (L.mem X (rhA (L := L) X))) ∧
      SCq st X Ω (L.mem X (scA (L.mem X (rhA (L := L) X)))) zr ∧
      L.rmax X (L.mem X (scA (L.mem X (rhA (L := L) X)))) ≠ 0#u64 ∧
      (∀ b, InSC (L.mem X (scA (L.mem X (rhA (L := L) X)))) zr b → Aligned b → R b) ∧
      (L.mem X (scA (L.mem X (rhA (L := L) X))) ≠ L.cscW X →
        ∀ b, InSC (L.mem X (scA (L.mem X (rhA (L := L) X)))) zr b → Outside b (L.cscW X) zc) ∧
      (L.mem X (scA (L.mem X (rhA (L := L) X))) = L.cscW X → zr = zc))
    (htd : L.mem X (tmA (L := L) X) ≠ 0#u64 → L.mem X (tmA (L := L) X) ∈ T ∧
      R (core.num.U64.wrapping_add (L.mem X (tmA (L := L) X)) 3528#u64)) :
    (∀ s4, sched.set_action st X sched.ACTION_RESUME_CURRENT = ok s4 →
      sched.switch_sched_context gS ar s4 a = sched.switch_sched_context st ar s4 a) ∧
    (∀ s4 s5 a3, sched.set_action st X sched.ACTION_RESUME_CURRENT = ok s4 →
      sched.switch_sched_context st ar s4 a = ok (s5, a3) →
      L.ksb s5 = L.ksb X ∧ L.cpu s5 = L.cpu X ∧
      (L.mem s5 (L.nodeAt s5 (L.cpu s5) layout.node.REPROGRAM) ≠ 0#u64 →
        sched.set_next_interrupt gS ar s5 a3 = sched.set_next_interrupt st ar s5 a3 ∧
        ∀ s7 a5, sched.set_next_interrupt st ar s5 a3 = ok (s7, a5) → L.ksb s7 = L.ksb X ∧ L.cpu s7 = L.cpu X)) := by
  have e1 := eq_of_spec_fd (sched.set_action.spec (L := L) X sched.ACTION_RESUME_CURRENT)
  set X1 := L.wr X (L.nodeAt X (L.cpu X) layout.node.SCHED_ACTION) sched.ACTION_RESUME_CURRENT with eX1
  have aA : Aligned (L.nodeAt X (L.cpu X) layout.node.SCHED_ACTION) :=
    nodeAt_aligned hN (by rw [act_val]; omega) (by rw [act_val])
  have kX : L.ksb X1 = L.ksb X := by rw [eX1, L.ksb_wr]
  have cX : L.cpu X1 = L.cpu X := by rw [eX1, LawfulStore.cpu_wr]
  have eN : ∀ o, L.nodeAt X1 (L.cpu X1) o = L.nodeAt X (L.cpu X) o := fun o => by rw [cX, nodeAt_of_ksb kX]
  have agN : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 16 →
      L.mem X1 (L.nodeAt X (L.cpu X) o) = L.mem X (L.nodeAt X (L.cpu X) o) := by
    intro o ho h8 h16
    rw [eX1]
    refine mem_wr_ne' aA (nodeAt_aligned hN ho h8) fun e => h16 ?_
    have e' := congrArg UScalar.val e
    rw [nodeAt_val hN (by rw [act_val]; omega), nodeAt_val hN ho, act_val] at e'
    omega
  have agΩ : ∀ b ∈ Ω, L.mem X1 b = L.mem X b := fun b hb => by
    rw [eX1]
    exact mem_wr_ne' aA (homega b hb).1 fun e =>
      out_ne_node (homega b hb) hcC hN (by rw [act_val]; omega) (congrArg UScalar.val e)
  have ecur : L.curW X1 = L.curW X := by
    unfold LawfulStore.curW; rw [eN]
    exact agN _ (by rw [curth_val]; omega) (by rw [curth_val]) (by rw [curth_val]; omega)
  have ecs : L.cscW X1 = L.cscW X := by
    unfold LawfulStore.cscW LawfulStore.nodeA; rw [eN]
    exact agN _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have esc : L.mem X1 (scA (L.curW X)) = L.mem X (scA (L.curW X)) := by
    rw [eX1, scA_eq]
    exact mem_wr_ne' aA (field_aligned (hT _ hct) (by simp) (by simp))
      (node_ne_field hN (by rw [act_val]; omega) hct (hT _ hct) (by simp))
  have hc1 : SCq st X1 Ω (L.cscW X) zc := SCq.agree hc agΩ
  have hN1 : NodePlaced st T X1 (L.cpu X1) := by rw [cX]; exact hN.ksb kX
  have hΩ1 : ∀ b ∈ Ω, OutsideObjs st T Cs X1 b := fun b hb => (homega b hb).ksb kX
  have hcC1 : L.cpu X1 ∈ Cs := cX ▸ hcC
  have hsame1 : L.mem X1 (scA (L.mem X1 (L.nodeA X1 layout.node.CUR_THREAD))) =
      L.mem X1 (L.nodeA X1 layout.node.CUR_SC) := by
    show L.mem X1 (scA (L.curW X1)) = L.cscW X1
    rw [ecur, esc, hsame, ecs]
  have hmx1 : L.rmax X1 (L.cscW X) ≠ 0#u64 := by
    unfold LawfulStore.rmax; rw [agΩ _ (hc.2.1 _ hc.2.2.2.2 hc.2.2.2.1)]; exact hmx
  have hcs1 : L.mem X1 (L.nodeA X1 layout.node.CUR_SC) = L.cscW X := ecs
  have hNd1 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeA X1 o) ∧ W (L.nodeA X1 o) := fun o h1 h2 => by
    unfold LawfulStore.nodeA; rw [eN]; exact hNd o h1 h2
  -- the write set of `switch_sched_context` from `X1`
  let B : U64 → Prop := fun b => b = L.nodeAt X (L.cpu X) layout.node.REPROGRAM ∨
    b = L.nodeAt X (L.cpu X) layout.node.CONSUMED ∨ b = L.nodeAt X (L.cpu X) layout.node.CUR_SC ∨
    InSC (L.cscW X) zc b
  have hfp := sched.switch_sched_context.fp hA X1 a (zt := zc) (zc := zc) (B := B) hcC1 hN1 hΩ1
    (by rw [hcs1]; exact hc1) (fun hne => absurd hsame1 hne)
    (by unfold LawfulStore.nodeA; rw [eN]; exact Or.inl rfl)
    (by unfold LawfulStore.nodeA; rw [eN]; exact Or.inr (Or.inl rfl))
    (by unfold LawfulStore.nodeA; rw [eN]; exact Or.inr (Or.inr (Or.inl rfl)))
    (fun hne => absurd hsame1 hne)
    (fun b _ h => by
      rw [hcs1] at h
      refine Or.inr (Or.inr (Or.inr ?_))
      rcases h with h | rfl
      · exact h.inSC
      · exact hc.2.2.1.1)
  -- words outside `B`
  have nB_node : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 56 → o.val ≠ 40 → o.val ≠ 24 →
      ¬ B (L.nodeAt X (L.cpu X) o) := by
    intro o ho h8 h56 h40 h24 hb
    have hO := node_out_place (st := st) hc.2.1 homega hcC hN ho h8
    rcases hb with e | e | e | e
    · have e' := congrArg UScalar.val e
      rw [nodeAt_val hN ho, nodeAt_val hN (by simp [layout.node.REPROGRAM])] at e'
      simp [layout.node.REPROGRAM] at e'; omega
    · have e' := congrArg UScalar.val e
      rw [nodeAt_val hN ho, nodeAt_val hN (by simp [layout.node.CONSUMED])] at e'
      simp [layout.node.CONSUMED] at e'; omega
    · have e' := congrArg UScalar.val e
      rw [nodeAt_val hN ho, nodeAt_val hN (by simp [layout.node.CUR_SC])] at e'
      simp [layout.node.CUR_SC] at e'; omega
    · unfold Outside at hO; unfold InSC at e; omega
  have nB_out : ∀ b, OutsideObjs st T Cs X b → ¬ InSC (L.cscW X) zc b → ¬ B b := by
    intro b hb hn h
    rcases h with e | e | e | e
    · exact out_ne_node hb hcC hN (by simp [layout.node.REPROGRAM]) (congrArg UScalar.val e).symm
    · exact out_ne_node hb hcC hN (by simp [layout.node.CONSUMED]) (congrArg UScalar.val e).symm
    · exact out_ne_node hb hcC hN (by simp [layout.node.CUR_SC]) (congrArg UScalar.val e).symm
    · exact hn e
  have nB_fld : ∀ y K : U64, y ∈ T → K.val < 4096 → K.val % 8 = 0 → ¬ B (core.num.U64.wrapping_add y K) := by
    intro y K hy hK h8 h
    rcases h with e | e | e | e
    · exact node_ne_field hN (by simp [layout.node.REPROGRAM]) hy (hT _ hy) hK e.symm
    · exact node_ne_field hN (by simp [layout.node.CONSUMED]) hy (hT _ hy) hK e.symm
    · exact node_ne_field hN (by simp [layout.node.CUR_SC]) hy (hT _ hy) hK e.symm
    · exact out_ne_field (homega _ (hc.2.1 _ (field_aligned (hT _ hy) hK h8) e)) hy (hT _ hy) hK rfl
  refine ⟨fun s4 e4 => ?_, fun s4 s5 a3 e4 e5 => ?_⟩
  · rw [e1] at e4; have e4' := ok_inj_ff e4; subst e4'
    refine PathObl.sched.switch_sched_context.guard hA X1 a (T := T) (zc := zc) (zt := zc) (i := L.cscW X)
      (c := L.cscW X) hN1 (by rw [ecur, esc, hsame]) hcs1 (fun o ho h8 => ?_) hc1.1 hc.2.2.2
      (fun h => absurd rfl h) hSc (fun h => absurd rfl h) hNd1 (by rw [ecur]; exact hsc)
    unfold LawfulStore.nodeA; rw [eN]
    exact ⟨nodeAt_aligned hN ho h8, node_out_place (st := st) hc.2.1 homega hcC hN ho h8, fun h => absurd rfl h⟩
  · rw [e1] at e4; have e4' := ok_inj_ff e4; subst e4'
    rw [e5, WP.spec_ok] at hfp
    obtain ⟨w5, -, hwf5, -⟩ := hfp
    rw [hcs1] at hwf5
    have k5 : L.ksb s5 = L.ksb X := w5.1.trans kX
    have c5 : L.cpu s5 = L.cpu X := w5.2.1.trans cX
    have eN5 : ∀ o, L.nodeAt s5 (L.cpu s5) o = L.nodeAt X (L.cpu X) o := fun o => by
      rw [c5, nodeAt_of_ksb k5]
    have ag5 : ∀ b, Aligned b → ¬ B b → L.mem s5 b = L.mem X1 b := fun b hb hn => w5.mem_eq hb hn
    have nodeK : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 56 → o.val ≠ 40 → o.val ≠ 24 → o.val ≠ 16 →
        L.mem s5 (L.nodeAt X (L.cpu X) o) = L.mem X (L.nodeAt X (L.cpu X) o) := by
      intro o ho h8 h56 h40 h24 h16
      rw [ag5 _ (nodeAt_aligned hN ho h8) (nB_node o ho h8 h56 h40 h24), agN o ho h8 h16]
    have fldK : ∀ y K : U64, y ∈ T → K.val < 4096 → K.val % 8 = 0 →
        L.mem s5 (core.num.U64.wrapping_add y K) = L.mem X (core.num.U64.wrapping_add y K) := by
      intro y K hy hK h8
      have al := field_aligned (hT _ hy) hK h8
      rw [ag5 _ al (nB_fld y K hy hK h8), eX1]
      exact mem_wr_ne' aA al (node_ne_field hN (by rw [act_val]; omega) hy (hT _ hy) hK)
    have cur5 : L.curW s5 = L.curW X := by
      unfold LawfulStore.curW; rw [eN5]
      exact nodeK _ (by rw [curth_val]; omega) (by rw [curth_val]) (by rw [curth_val]; omega)
        (by rw [curth_val]; omega) (by rw [curth_val]; omega) (by rw [curth_val]; omega)
    have sc5 : L.mem s5 (scA (L.curW s5)) = L.cscW X := by
      rw [cur5, scA_eq, fldK _ _ hct (by simp) (by simp), ← scA_eq, hsame]
    refine ⟨k5, c5, fun _ => ⟨?_, fun s7 a5 e7 => ?_⟩⟩
    · refine PathObl.sched.set_next_interrupt.guard ar s5 a3 (fun o h1 h2 => ?_) (by rw [k5]; exact hdt)
        (by rw [cur5]; exact hsc) (by rw [sc5]; exact hSc.head (hwf5 hmx1)) (fun hr => ?_) (fun ht => ?_)
      · unfold LawfulStore.nodeA; rw [eN5]; exact hNd o h1 h2
      · have erh : L.mem s5 (rhA (L := L) s5) = L.mem X (rhA (L := L) X) := by
          show L.mem s5 (L.nodeAt s5 (L.cpu s5) _) = _
          rw [eN5]
          exact nodeK _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
            (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
            (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
        rw [erh] at hr ⊢
        obtain ⟨zr, hrT, hRr, hq, hmr, hRall, hdis, hzr⟩ := hrs hr
        have esr : L.mem s5 (scA (L.mem X (rhA (L := L) X))) = L.mem X (scA (L.mem X (rhA (L := L) X))) := by
          rw [scA_eq, fldK _ _ hrT (by simp) (by simp)]
        rw [esr]
        refine ⟨hRr, ?_⟩
        have hwf : RefillsWF st s5 (L.mem X (scA (L.mem X (rhA (L := L) X)))) zr := by
          by_cases hne : L.mem X (scA (L.mem X (rhA (L := L) X))) = L.cscW X
          · have hwX := hq.1 hmr
            rw [hne] at hwX ⊢
            rw [hzr hne] at hwX ⊢; exact hwf5 hmx1
          · refine RefillsWF.agree (hq.1 hmr) fun b hb hin => ?_
            have hO := homega b (hq.2.1 b hb hin)
            rw [ag5 b hb (nB_out b hO (fun h => by
              have := hdis hne b hin; unfold Outside at this; unfold InSC at h; omega)), eX1]
            exact mem_wr_ne' aA hb fun e =>
              out_ne_node hO hcC hN (by rw [act_val]; omega) (congrArg UScalar.val e)
        exact PathObl.ScAcc.head (W := fun _ => True) ⟨fun b ha hi => hRall b hi ha, fun _ _ _ => trivial, trivial⟩ hwf
      · have etm : L.mem s5 (tmA (L := L) s5) = L.mem X (tmA (L := L) X) := by
          show L.mem s5 (L.nodeAt s5 (L.cpu s5) _) = _
          rw [eN5]
          exact nodeK _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
            (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
            (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
        rw [etm] at ht ⊢
        exact (htd ht).2
    · have hfp7 := sched.set_next_interrupt.fp hA s5 a3 (B := fun _ => True) (by rw [c5]; exact hN.ksb k5) trivial
      rw [e7, WP.spec_ok] at hfp7
      exact ⟨hfp7.1.trans k5, hfp7.2.1.trans c5⟩

end

end Fl4Proofs.P2
