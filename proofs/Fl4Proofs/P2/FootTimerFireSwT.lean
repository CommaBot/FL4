/-
# P2 (p2lf): `schedule`'s resume tail after a switch to another thread, on the guarded store

`switch_hsw_hfr`: the premises `hsw` / `hfr` of `schedRes.guard` (p2io's, `PathObl.LT`) at a state `X` whose current
thread `d` (just made current by `switch_to_thread`) may run on an SC `i` other than the current SC `c`:
`switch_sched_context` (p2sl's `switch_sched_context.guard`, its `i ≠ c` branch included) and, at the state it ends
in, `set_next_interrupt`. It is `resume_hsw_hfr` (`P2/FootTimerSetR`, `i = c`) generalised the way
`fastpath.switch_to.guard` (`P2/AccessSwitchTo`) handles the switch: the writes up to `set_next_interrupt` are the
action word and `switch_sched_context.fp`'s (`TWo`: node words, the rings of `c` and `i`, `c`'s `CONSUMED`), so
the release head's SC and the timer-min thread's deadline keep their entry values or their ring invariant.

No named premises.
-/
import Fl4Proofs.P2.AccessSwitchTo
import Fl4Proofs.P2.FootTimerFin
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts

section
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
  [L : LawfulStore st]
variable {T Cs Ω : Set U64}

set_option maxHeartbeats 8000000 in
/-- **`hsw` / `hfr` of `schedRes.guard` after a switch** (module docstring). -/
theorem switch_hsw_hfr {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (X : S) (a : A)
    {d : U64} {zc zt : Nat}
    (P : TailPld (L := L) T Cs Ω X d) (hcur : L.curW X = d)
    (hc : SCq st X Ω (L.cscW X) zc)
    (ht : L.mem X (scA d) ≠ L.cscW X → SCin st X Ω (L.mem X (scA d)) zt ∧
      ∀ b, InSC (L.mem X (scA d)) zt b → Outside b (L.cscW X) zc)
    (hact : L.mem X (scA d) = L.cscW X → L.rmax X (L.cscW X) ≠ 0#u64)
    (hrh : L.mem X (rhA (L := L) X) ≠ 0#u64 → L.mem X (rhA (L := L) X) ∈ T ∧
      R (scA (L.mem X (rhA (L := L) X))) ∧
      ∃ zq, SCin st X Ω (L.mem X (scA (L.mem X (rhA (L := L) X)))) zq ∧
        (∀ b, Aligned b → InSC (L.mem X (scA (L.mem X (rhA (L := L) X)))) zq b → R b) ∧
        (L.mem X (scA (L.mem X (rhA (L := L) X))) ≠ L.cscW X →
          ∀ b, InSC (L.mem X (scA (L.mem X (rhA (L := L) X)))) zq b → Outside b (L.cscW X) zc) ∧
        (L.mem X (scA (L.mem X (rhA (L := L) X))) ≠ L.mem X (scA d) → L.mem X (scA d) ≠ L.cscW X →
          ∀ b, InSC (L.mem X (scA (L.mem X (rhA (L := L) X)))) zq b → Outside b (L.mem X (scA d)) zt))
    (htm : L.mem X (tmA (L := L) X) ≠ 0#u64 → L.mem X (tmA (L := L) X) ∈ T ∧
      R (core.num.U64.wrapping_add (L.mem X (tmA (L := L) X)) 3528#u64))
    (hNd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeA X o) ∧ W (L.nodeA X o))
    (hdt : R (core.num.U64.wrapping_add (L.ksb X) layout.ks.DOMAIN_TIME))
    (hSc : ScAcc R W (L.cscW X) zc) (hSi : L.mem X (scA d) ≠ L.cscW X → ScAcc R W (L.mem X (scA d)) zt)
    (hsc : R (scA d)) :
    (∀ s4, sched.set_action st X sched.ACTION_RESUME_CURRENT = ok s4 →
      sched.switch_sched_context gS ar s4 a = sched.switch_sched_context st ar s4 a) ∧
    (∀ s4 s5 a3, sched.set_action st X sched.ACTION_RESUME_CURRENT = ok s4 →
      sched.switch_sched_context st ar s4 a = ok (s5, a3) →
      L.ksb s5 = L.ksb X ∧ L.cpu s5 = L.cpu X ∧
      (L.mem s5 (L.nodeAt s5 (L.cpu s5) layout.node.REPROGRAM) ≠ 0#u64 →
        sched.set_next_interrupt gS ar s5 a3 = sched.set_next_interrupt st ar s5 a3 ∧
        ∀ s7 a5, sched.set_next_interrupt st ar s5 a3 = ok (s7, a5) → L.ksb s7 = L.ksb X ∧ L.cpu s7 = L.cpu X)) := by
  have hd' := P.hT d P.hd
  have hcΩ : ∀ x, Aligned x → InSC (L.cscW X) zc x → x ∈ Ω := hc.2.1
  have hcC : InSC (L.cscW X) zc (core.num.U64.wrapping_add (L.cscW X) layout.sc.CONSUMED) := hc.2.2.1.1
  have hiΩ : L.mem X (scA d) ≠ L.cscW X → ∀ x, Aligned x → InSC (L.mem X (scA d)) zt x → x ∈ Ω :=
    fun hne => (ht hne).1.2
  -- the offsets
  let Osw : Nat → Prop := fun n => n = 16 ∨ n = 24 ∨ n = 40 ∨ n = 56
  let Oall : Nat → Prop := fun n => n = 16 ∨ n = 24 ∨ n = 40 ∨ n = 56 ∨ n = 80 ∨ n = 120
  have hOsw : ∀ n, Osw n → n < 4288 ∧ n % 8 = 0 := by
    intro n hn; rcases hn with h | h | h | h <;> subst h <;> decide
  have hOall : ∀ n, Oall n → n < 4288 ∧ n % 8 = 0 := by
    intro n hn; rcases hn with h | h | h | h | h | h <;> subst h <;> decide
  have swall : ∀ n, Osw n → Oall n := by
    intro n hn; rcases hn with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  let TA := TWo (L := L) X Oall (L.cscW X) (L.mem X (scA d)) zc zt
  have fNot : ∀ {y K : U64}, y ∈ T → K.val < 4096 → K.val % 8 = 0 →
      ¬ TA (core.num.U64.wrapping_add y K) := fun hy hK h8 =>
    field_not_TWo P (fun n hn => (hOall n hn).1) hcΩ hcC hiΩ hy hK h8
  have e1 := eq_of_spec_fd (sched.set_action.spec (L := L) X sched.ACTION_RESUME_CURRENT)
  set X1 := L.wr X (L.nodeAt X (L.cpu X) layout.node.SCHED_ACTION) sched.ACTION_RESUME_CURRENT with eX1
  have aA : Aligned (L.nodeAt X (L.cpu X) layout.node.SCHED_ACTION) :=
    nodeAt_aligned P.hN (by rw [act_val]; omega) (by rw [act_val])
  have kX : L.ksb X1 = L.ksb X := by rw [eX1, L.ksb_wr]
  have cX : L.cpu X1 = L.cpu X := by rw [eX1, LawfulStore.cpu_wr]
  have PX := P.ksb kX cX
  have nX : ∀ o, L.nodeA X1 o = L.nodeA X o := fun o => by
    unfold LawfulStore.nodeA; rw [cX, nodeAt_of_ksb kX]
  have w0 : WritesIn st X X1 TA := by
    rw [eX1]
    exact (writesIn_wr aA).mono fun b e =>
      Or.inl ⟨layout.node.SCHED_ACTION, by simp [Oall, layout.node.SCHED_ACTION], e⟩
  have ag : ∀ b, Aligned b → b ≠ L.nodeAt X (L.cpu X) layout.node.SCHED_ACTION → L.mem X1 b = L.mem X b := by
    intro b hb h2
    rw [eX1, mem_wr_ne' aA hb (Ne.symm h2)]
  have agΩ : ∀ b ∈ Ω, L.mem X1 b = L.mem X b := fun b hb => ag b (P.hΩ b hb).1
    (fun e => out_ne_node (P.hΩ b hb) P.hcC P.hN (by rw [act_val]; omega) (by rw [e]))
  have agT : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem X1 (core.num.U64.wrapping_add d K) = L.mem X (core.num.U64.wrapping_add d K) := fun K hK h8 =>
    ag _ (P.tcbAl hK h8) (fun e => node_ne_field P.hN (by rw [act_val]; omega) P.hd hd' hK e.symm)
  have csA : Aligned (L.nodeAt X (L.cpu X) layout.node.CUR_SC) :=
    nodeAt_aligned P.hN (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have ecs : L.mem X1 (L.nodeA X1 layout.node.CUR_SC) = L.cscW X := by
    unfold LawfulStore.nodeA LawfulStore.cscW LawfulStore.nodeA
    rw [cX, nodeAt_of_ksb kX]
    have v24 := nodeAt_val P.hN (off := layout.node.CUR_SC) (by simp [layout.node.CUR_SC])
    have v16 := nodeAt_val P.hN (off := layout.node.SCHED_ACTION) (by simp [layout.node.SCHED_ACTION])
    refine ag _ csA ?_
    apply ne_of_valne
    rw [v24, v16]; simp [layout.node.CUR_SC, layout.node.SCHED_ACTION]
  have cA : Aligned (L.nodeAt X (L.cpu X) layout.node.CUR_THREAD) :=
    nodeAt_aligned P.hN (by rw [curth_val]; omega) (by rw [curth_val])
  have hcur1 : L.mem X1 (L.nodeA X1 layout.node.CUR_THREAD) = d := by
    unfold LawfulStore.nodeA
    rw [cX, nodeAt_of_ksb kX, ag _ cA ?_]
    · exact hcur
    · apply ne_of_valne
      rw [nodeAt_val P.hN (by rw [curth_val]; omega), nodeAt_val P.hN (by rw [act_val]; omega), curth_val, act_val]
      omega
  have esc : L.mem X1 (scA d) = L.mem X (scA d) := by rw [scA_eq]; exact agT _ (by simp) (by simp)
  have hcX : SCq st X1 Ω (L.cscW X) zc := by
    refine ⟨fun hm => ?_, hc.2.1, hc.2.2⟩
    have em : L.rmax X1 (L.cscW X) = L.rmax X (L.cscW X) :=
      agΩ _ (hc.2.1 _ hc.2.2.2.2 hc.2.2.2.1)
    exact (hc.1 (em ▸ hm)).agree fun b hb hin => agΩ b (hc.2.1 b hb hin)
  have htX : L.mem X (scA d) ≠ L.cscW X →
      RefillsWF st X1 (L.mem X (scA d)) zt ∧ ∀ b, InSC (L.mem X (scA d)) zt b → Outside b (L.cscW X) zc := by
    intro hne
    obtain ⟨h1, h2⟩ := ht hne
    exact ⟨h1.1.agree fun b hb hin => agΩ b (h1.2 b hb hin), h2⟩
  refine ⟨fun s4 e4 => ?_, fun s4 s5 a3 e4 h4 => ?_⟩
  · rw [e1] at e4; have e4' := ok_inj_ff e4; subst e4'
    refine sched.switch_sched_context.guard hA X1 a (T := T) (zc := zc) (zt := zt) PX.hN
      (show L.mem X1 (scA (L.mem X1 (L.nodeA X1 layout.node.CUR_THREAD))) = L.mem X (scA d) by rw [hcur1, esc])
      ecs (fun o ho h8 => ?_) hcX.1 hc.2.2.2 htX hSc hSi (fun o ho h8 => by rw [nX]; exact hNd o ho h8)
      (show R (scA (L.mem X1 (L.nodeA X1 layout.node.CUR_THREAD))) by rw [hcur1]; exact hsc)
    refine ⟨nodeAt_aligned PX.hN ho h8, node_out_place hc.2.1 PX.hΩ PX.hcC PX.hN ho h8, fun hne => ?_⟩
    exact node_out_place (ht hne).1.2 PX.hΩ PX.hcC PX.hN ho h8
  rw [e1] at e4; have e4' := ok_inj_ff e4; subst e4'
  have F4 := post_of_ok (sched.switch_sched_context.fp hA X1 a (zt := zt) (zc := zc)
    (B := TWo (L := L) X Osw (L.cscW X) (L.mem X (scA d)) zc zt) PX.hcC PX.hN PX.hΩ
    (by rw [ecs]; exact hcX)
    (by rw [hcur1, esc, ecs]; intro hne; exact ⟨⟨(htX hne).1, (ht hne).1.2⟩, (ht hne).2⟩)
    (by rw [nX]; exact Or.inl ⟨layout.node.REPROGRAM, by simp [Osw, layout.node.REPROGRAM], rfl⟩)
    (by rw [nX]; exact Or.inl ⟨layout.node.CONSUMED, by simp [Osw, layout.node.CONSUMED], rfl⟩)
    (by rw [nX]; exact Or.inl ⟨layout.node.CUR_SC, by simp [Osw, layout.node.CUR_SC], rfl⟩)
    (fun hne b _ h => by
      rw [hcur1, esc, ecs] at hne; rw [hcur1, esc] at h
      exact Or.inr (Or.inr (Or.inr ⟨hne, h⟩)))
    (fun b _ h => by
      rw [ecs] at h
      rcases h with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h)))) h4
  rw [hcur1, esc, ecs] at F4
  obtain ⟨w34, -, wfc, wfi⟩ := F4
  have w4 : WritesIn st X s5 TA :=
    (w0.trans w34).mono fun b hb => hb.elim id (TWo.mono swall)
  have k4 : L.ksb s5 = L.ksb X := w4.1
  have c4 : L.cpu s5 = L.cpu X := w4.2.1
  have n4 : ∀ o, L.nodeA s5 o = L.nodeA X o := fun o => by
    unfold LawfulStore.nodeA; rw [c4, nodeAt_of_ksb k4]
  have P4 := P.ksb k4 c4
  have cur4 : L.curW s5 = d := by
    show L.mem s5 (L.nodeAt s5 (L.cpu s5) layout.node.CUR_THREAD) = d
    have e : L.nodeAt s5 (L.cpu s5) layout.node.CUR_THREAD = L.nodeA X layout.node.CUR_THREAD := n4 _
    rw [e, w4.mem_eq (show Aligned (L.nodeA X layout.node.CUR_THREAD) from cA) ?_]
    · exact hcur
    · exact node_not_TWo P (fun n hn => (hOall n hn).1) hcΩ hcC hiΩ (by simp [layout.node.CUR_THREAD])
        (by simp [layout.node.CUR_THREAD]) (by simp [Oall, layout.node.CUR_THREAD])
  have sc4 : L.mem s5 (scA d) = L.mem X (scA d) := by
    rw [scA_eq]; exact w4.mem_eq (P.tcbAl (by simp) (by simp)) (fNot P.hd (by simp) (by simp))
  have rmaxc : L.rmax X1 (L.cscW X) = L.rmax X (L.cscW X) := agΩ _ (hc.2.1 _ hc.2.2.2.2 hc.2.2.2.1)
  have hd4 : RdHead (L := L) R s5 (L.mem X (scA d)) := by
    by_cases hic : L.mem X (scA d) = L.cscW X
    · rw [hic]; exact hSc.head (wfc (by rw [rmaxc]; exact hact hic))
    · exact (hSi hic).head (wfi hic)
  have nkeep : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → ¬ Oall o.val →
      L.mem s5 (L.nodeA s5 o) = L.mem X (L.nodeA X o) := fun o ho h8 hno => by
    rw [n4]; exact w4.mem_eq (nodeAt_aligned P.hN ho h8)
      (node_not_TWo P (fun n hn => (hOall n hn).1) hcΩ hcC hiΩ ho h8 hno)
  have rh4 : L.mem s5 (rhA (L := L) s5) = L.mem X (rhA (L := L) X) :=
    nkeep layout.node.RELEASE_HEAD (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [Oall, layout.node.RELEASE_HEAD])
  have tm4 : L.mem s5 (tmA (L := L) s5) = L.mem X (tmA (L := L) X) :=
    nkeep layout.node.TIMER_MIN (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [Oall, layout.node.TIMER_MIN])
  have hrs4 : L.mem s5 (rhA (L := L) s5) ≠ 0#u64 → R (scA (L.mem s5 (rhA (L := L) s5))) ∧
      RdHead (L := L) R s5 (L.mem s5 (scA (L.mem s5 (rhA (L := L) s5)))) := by
    rw [rh4]
    intro h0
    obtain ⟨hrT, hrs, zq, hqin, hqR, hqc, hqi⟩ := hrh h0
    have eq4 : L.mem s5 (scA (L.mem X (rhA (L := L) X))) = L.mem X (scA (L.mem X (rhA (L := L) X))) := by
      rw [scA_eq]; exact w4.mem_eq ((P.hT _ hrT) |> fun h => field_aligned h (by simp) (by simp))
        (fNot hrT (by simp) (by simp))
    refine ⟨hrs, ?_⟩
    rw [eq4]
    by_cases hqc' : L.mem X (scA (L.mem X (rhA (L := L) X))) = L.cscW X
    · rw [hqc']
      refine hSc.head (wfc ?_)
      rw [rmaxc]
      have := hqin.1.min_le
      rw [hqc'] at this
      intro e; rw [e] at this; revert this; simp [sporadic.MIN_REFILLS]
    by_cases hqi' : L.mem X (scA (L.mem X (rhA (L := L) X))) = L.mem X (scA d)
    · have hne : L.mem X (scA d) ≠ L.cscW X := fun e => hqc' (hqi'.trans e)
      rw [hqi']; exact (hSi hne).head (wfi hne)
    · have hwf : RefillsWF st s5 (L.mem X (scA (L.mem X (rhA (L := L) X)))) zq :=
        hqin.1.writesIn w4 (sc_out_TWo P hOall hqin.2 hcC (hqc hqc') (hqi hqi'))
      exact (⟨hqR, fun _ _ _ => trivial, trivial⟩ : ScAcc R (fun _ => True) _ zq).head hwf
  have htd4 : L.mem s5 (tmA (L := L) s5) ≠ 0#u64 →
      R (core.num.U64.wrapping_add (L.mem s5 (tmA (L := L) s5)) 3528#u64) := by
    rw [tm4]; exact fun h0 => (htm h0).2
  refine ⟨k4, c4, fun _ => ⟨?_, fun s7 a5 e7 => ?_⟩⟩
  · exact sched.set_next_interrupt.guard ar s5 a3 (fun o ho h8 => by rw [n4]; exact hNd o ho h8)
      (by rw [k4]; exact hdt) (by rw [cur4]; exact hsc) (by rw [cur4, sc4]; exact hd4) hrs4 htd4
  · have hfp7 := sched.set_next_interrupt.fp hA s5 a3 (B := fun _ => True) P4.hN trivial
    rw [e7, WP.spec_ok] at hfp7
    exact ⟨hfp7.1.trans k4, hfp7.2.1.trans c4⟩

end

end Fl4Proofs.P2.PathObl
