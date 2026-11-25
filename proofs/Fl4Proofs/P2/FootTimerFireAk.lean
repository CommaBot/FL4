/-
# P2 (p2lf): `PathObl.acc` of a waking fire-case run

`irq_acc_fire_wk`: as `irq_acc_fire_nw` (`P2/FootTimerFireOwn`), for a run whose due thread's notification wakes a
thread (`¬ NoWake`): `irq_accG_fire_pre` with `fire_tail_wk` (`P2/FootTimerFireTk`) on the guarded store
`guard st (MaxR …) (MaxW …)`, its per-class premises discharged at the entry state: local threads' and SCs' words by
`loc_rd_own` / `loc_wr_own` (`P2/FootTimerFireLoc`), queue links of threads blocked on a held object and the
plan's endpoint / reply words by `lkw_own` with the lock set `Lk := lk s` (`PlanLk` gives the plan's notification and
endpoint), endpoint / reply words placed by `ObjLay`, the bound notification's words by `fire_wr_own` (`FNtW`).

Lemma hypotheses (discharged by the caller): `hPE` (the plan's endpoint is a heap endpoint whose words are aligned),
`hPR` (the plan's reply is a P1 reply object, its TCB word aligned), `hBA` (`BufAt` after `handle_interrupt`),
`hSwT` (`SwTailP`: the tail when the action is the woken thread). Named premises used: `PlanLk` [P], `ObjLay` [J].
-/
import Fl4Proofs.P2.FootTimerFireTk
import Fl4Proofs.P2.FootTimerFireLoc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.Serial (Owner)
open Fl4Proofs.P2.OwnMap Fl4Proofs.P2.PathObl
open Classical

section acc
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {A : Type} (ar : machine.Arch A) {m : U64 → U64}

/-- The plan's notification is the due thread's bound notification (`plan_facts'`, `fire_ok` of a null thread is
`false`). -/
theorem plan_ntfn {s s1 : S} {tip p : localtimer.TimerIrqPlan} {ct now : U64}
    (etip : localtimer.plan_objects st s = ok tip) (eb : localtimer.same_plan tip p = ok true)
    (efo : localtimer.fire_ok st s1 (L.cpu s) ct p now = ok true) :
    L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64 ∧
      p.ntfn = L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) := by
  obtain ⟨hpt, hpn⟩ := same_plan_tm eb
  have hp0 : p.tm ≠ 0#u64 := by
    intro e
    have h' := efo
    rw [fire_ok_eq, if_pos e] at h'
    exact Bool.false_ne_true (ok_inj_ff h')
  rcases plan_facts' etip with ⟨t1, -⟩ | ⟨t1, -, -, t4⟩
  · exact absurd (by rw [← hpt]; exact t1) hp0
  · rw [t1] at t4
    exact ⟨by rw [← t1, hpt]; exact hp0, by rw [← hpn, t4]⟩

set_option maxHeartbeats 16000000 in
/-- **`PathObl.acc` of a waking fire-case run** (module docstring). -/
theorem irq_acc_fire_wk (hA : P0.ArchTotal ar) (hK : RegionOK K) {s s' : S} {a a' : A} {irq : U64}
    {p : localtimer.TimerIrqPlan} {lk : S → U64 → Prop} {U : Set U64}
    (hE : IrqEntK K st T Cs Ω H Sg Rp Scs Nt Z Ac m s) (hY : IrqLay K st Nt irq s)
    (hAff : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t))
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (hOL : ObjLay K H Rp) (hPL : PlanLk lk p)
    (hPE : p.ep ≠ 0#u64 → H p.ep = some .ep ∧
      ∀ k : U64, k.val < 16 → k.val % 8 = 0 → Aligned (core.num.U64.wrapping_add p.ep k))
    (hPR : p.reply ≠ 0#u64 → p.reply ∈ Rp ∧ Aligned (rTcbA p.reply))
    (hBA : ∀ s2 a2 s3 a3, interrupt.handle_interrupt st ar s2 a2 irq = ok (s3, a3) →
      BufAt st T Cs H Sg Scs Z U s3)
    (hSwT : SwTailP st (guard st (MaxR K st lk s) (MaxW K st lk s)) ar T Cs Ω H Sg Rp Scs Nt Z Ac
      (MaxR K st lk s) s)
    (hq : IrqFire st ar s a) (hW : ¬ NoWake st s)
    (h : localtimer.handle_timer_irq_local st ar s a irq p = ok (true, s', a')) :
    localtimer.handle_timer_irq_local (guard st (MaxR K st lk s) (MaxW K st lk s)) ar s a irq p =
      ok (true, s', a') := by
  have hI := hE.inv
  have hL := hE.lay
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ h0.cur
  have hcT : L.curW s ∈ T := h0.curT
  have hX := hI.2.2.1
  have hO := hX.1
  obtain ⟨mx, now, i2, tip, x, s1, s2, s3, a1, a2, a3, emx, hle, ei1, etip, eb, eok, eq, eu, enow, erel, ei2, eb4,
    edue, efo, ecb, ehi⟩ := fire_eqs ar hA hq h
  have hTm := fire_tmHere etip eb efo
  obtain ⟨hTM0, hpN⟩ := plan_ntfn etip eb efo
  have hTMs := tmin_facts (BXI.blk hI) h0.cur hTM0
  have hB0 : L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) ≠ 0#u64 := fun e =>
    hW (Or.inl e)
  have hNN : L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) ∈ Nt :=
    hX.2.2.bnd _ hTMs.1 hB0
  have pn0 : p.ntfn ≠ 0#u64 := by rw [hpN]; exact hB0
  have aS : Aligned (stA (L.curW s)) := by
    rw [stA_eq]; exact field_aligned (h0.tcbs _ hcT) (by simp) (by simp)
  have wS : IrqWr st Z s (stA (L.curW s)) := Or.inr (Or.inl ⟨3328#u64, by simp, by simp, by simp, stA_eq _⟩)
  refine irq_accG_fire_pre (gS := guard st (MaxR K st lk s) (MaxW K st lk s)) (R := MaxR K st lk s)
    (W := MaxW K st lk s) ar hA hI hq
    (fun hok w ha hw => ⟨irq_rd_own hK hI hL hY hAff hok hw, ha⟩)
    (fun hok w ha hw _ => ⟨irq_wr_own hI hL hok hw, ha⟩)
    (fun _ i hi => ⟨rperm_none (hY.iq i hi).2 _, (hY.iq i hi).1⟩)
    (fun _ => ⟨rperm_none hL.dom _, hL.domA⟩)
    (fun _ => ⟨rperm_none hL.dtm _, hL.dtmA⟩) ?_ ?_ h
  · intro _ s1' a1' now' eu' _
    obtain ⟨n1, -, er⟩ := ut_now ar hA hN eu'
    simp only at er
    exact fire_rd hK hI hL hY hNt (by rw [er, utW_ksb]) (by rw [er, utW_cpu])
      (fun b hb h1 h2 => by rw [er]; exact utW_mem hN n1 hb h1 h2) etip eb _ _
  · intro hok s1' a1' x' s2' a2' s3' a3' now' eu' enow' efo' ecb' ehi'
    rw [eu] at eu'
    have e1 := ok_inj_ff eu'
    simp only [Prod.mk.injEq] at e1
    obtain ⟨rfl, rfl⟩ := e1
    rw [enow] at enow'
    obtain rfl := ok_inj_ff enow'
    have g3328 : ¬ GateField (3328#u64 : U64).val := by unfold GateField; simp
    have t3328 : ¬ TimerField (3328#u64 : U64).val := by unfold TimerField; simp
    have f3328 : ¬ GField (3328#u64 : U64).val := by unfold GField; simp
    exact fire_tail_wk (gS := guard st (MaxR K st lk s) (MaxW K st lk s)) (R := MaxR K st lk s)
      (W := MaxW K st lk s) (Lk := lk s) (U := U) ar hA hI hNt hok
      (fun w ha hw => ⟨fire_rd_own hK hI hL hY hAff hok hTm hw, ha⟩)
      (fun w ha hw _ => ⟨fire_wr_own hK hI hL hY hok hTm hw, ha⟩)
      ⟨rperm_none hL.dtm _, hL.dtmA⟩
      (fun X _ _ => PathObl.GWr.write (g := guard st (MaxR K st lk s) (MaxW K st lk s))
        ⟨irq_wr_own hI hL hok wS, aS⟩ X _)
      (fun X y v hy ha _ => PathObl.GWr.write (g := guard st (MaxR K st lk s) (MaxW K st lk s))
        ⟨held_core (ftree_own hL hT hy ha (k := 3568#u64) (by simp) (by simp) (by simp)),
          field_aligned (hT y hy) (by simp) (by simp)⟩ X v)
      (fun X y v hy ha _ _ _ => PathObl.GWr.write (g := guard st (MaxR K st lk s) (MaxW K st lk s))
        ⟨held_core (ftree_own hL hT hy ha (k := 3528#u64) (by simp) (by simp) (by simp)),
          field_aligned (hT y hy) (by simp) (by simp)⟩ X v)
      hW hAff
      (fun y hy K h1 h2 h3 ht hg => ⟨loc_rd_own hI hL (Or.inr (Or.inl ⟨y, hy, K, h1, h2, h3, ht, hg, rfl⟩)),
        field_aligned (hT y hy.1) h2 h3⟩)
      (fun y hy K h1 h2 h3 hga ht hg _ _ =>
        ⟨loc_wr_own hI hL (Or.inr (Or.inl ⟨y, hy, K, h1, h2, h3, hga, ht, hg, rfl⟩)),
          field_aligned (hT y hy.1) h2 h3⟩)
      (fun q hq hc b ha hb => ⟨loc_rd_own hI hL (Or.inr (Or.inr ⟨q, hq, hc, hb⟩)), ha⟩)
      (fun q hq hc b ha hb h16 => ⟨loc_wr_own hI hL (Or.inr (Or.inr ⟨q, hq, hc, hb, h16⟩)), ha⟩)
      (fun y hy hqs hlk k hk => by
        have o := lkw_own hI hL (Lk := lk s) (fun _ h => h) (Or.inl ⟨y, hy, hqs, hlk, k, hk, rfl⟩)
        have ha := field_aligned (hT y hy) (K := k) (by omega) (by omega)
        exact ⟨⟨o.2, ha⟩, ⟨o.1, ha⟩⟩)
      ⟨rperm_none hL.dom _, hL.domA⟩
      (fun X y v hy _ _ _ => PathObl.GWr.write (g := guard st (MaxR K st lk s) (MaxW K st lk s))
        ⟨loc_wr_own hI hL (Or.inr (Or.inl ⟨y, hy, 3328#u64, by simp, by simp, by simp, g3328, t3328, f3328,
          stA_eq _⟩)), by rw [stA_eq]; exact field_aligned (hT y hy.1) (by simp) (by simp)⟩ X v)
      ((hPL s).1 pn0) (hPL s).2.1
      (fun k h1 h2 h3 => by
        obtain ⟨p1, p2⟩ := hO.ntP _ hNN
        refine ⟨fire_wr_own hK hI hL hY hok hTm (Or.inr (Or.inr ⟨hTM0, hB0, k, h1, h2, h3, by rw [hpN]⟩)), ?_⟩
        rw [hpN]; unfold Aligned; rw [ntfn_word_val p1 p2 h1]; omega)
      (fun hep k h1 h2 => by
        obtain ⟨hH, hal⟩ := hPE hep
        have o := lkw_own hI hL (Lk := lk s) (fun _ h => h) (Or.inr ⟨p.ep, (hPL s).2.1 hep, hOL.1 _ hH k h1⟩)
        exact ⟨⟨o.2, hal k h1 h2⟩, ⟨o.1, hal k h1 h2⟩⟩)
      (fun hr => by
        obtain ⟨hR, hal⟩ := hPR hr
        have o := lkw_own hI hL (Lk := lk s) (w := rTcbA p.reply) (fun _ h => h)
          (Or.inr ⟨p.reply, (hPL s).2.2 hr, by unfold rTcbA; exact hOL.2 _ hR _ (by simp [layout.reply.TCB])⟩)
        exact ⟨o.1, hal⟩)
      etip eb eq eok eu enow erel ei2 eb4 edue efo' ecb' emx hle ei1 ehi' (hBA _ _ _ _ ehi') hSwT

end acc

end Fl4Proofs.P2
