/-
# P2 (p2lf): the fire case without a woken thread: ownership, `PathObl.acc` and `PathObl.move`

With the ownership map `OwnMap.own K`, at the entry state `s` of an accepted fire-case run (`IrqOk`, the due thread
`TM` this core's, `TmHere`):

* `ftree_own`: a timer field of a thread armed in this core's tree is this core's (`tOwner`: armed, its height's
  core); `fnt_ownE` / `fnt_own`: a word of `TM`'s bound notification `N` is `ntfnOwner`'s, so all but `BOUND_TCB` (the
  gate's) are `TM`'s home core's, this core (`BndS.tb`: `N` is bound back to `TM`);
* `fire_rd_own` / `fire_wr_own`: every word of `FireRd` is readable (`RPerm`), every word of `FireWr` writable
  (`WPerm`); `fire_wr_nondec`: the words of `FireWr` other than the current thread's `STATE` decide no owner;
* `irq_acc_fire_nw`: `PathObl.acc` of a fire-case run whose signal wakes nobody (`NoWake`): the run on
  `guard st (MaxR …) (MaxW …)` is the real run (`irq_accG_fire_pre` with `fire_rd` and `fire_tail_nw`; the tree
  code's height / deadline writes and the current thread's `STATE` write are this core's words);
* `irq_move_fire_nw`: `PathObl.move` of such a run (run on `gd st ⊤ (StWrOK …)`: the tree code's height / deadline
  writes by `stepOK_height` / `stepOK_deadline`, the current thread's `RESTART → RUNNING` by `stepOK_state`, the
  rest decides nothing; then `interp_gd` through `IsProg`).

No lock is needed: a non-waking signal writes no lock-owned word (`PlanLk` is for the waking branches).

Premises: `IrqLay` [J], `StLay` [J] (`IrqEntK.lay`), `AsidOff` [J] (`IrqEntK.asid`), `hAff` [J] (p2j `AffSc`), as
`irq_acc_own`; `hNt` (P1's notifications are its heap's, `fun _ h => h` at the canonical instantiation); `hp` [P]
(`IsProg`).
-/
import Fl4Proofs.P2.FootTimerFireNw
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.Serial (Owner)
open Fl4Proofs.P2.OwnMap Fl4Proofs.P2.PathObl
open Classical

section own
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}

/-- A timer field of a thread armed in this core's tree is this core's. -/
theorem ftree_own {s : S} (hL : StLay K st T Scs Z s) (hT : TcbPlaced T) {y k : U64} (hy : y ∈ T)
    (ha : FootLtArmed st s (L.cpu s) y) (h1 : 3528 ≤ k.val) (h2 : k.val < 3576) (h8 : k.val % 8 = 0) :
    own K (L.mem s) (core.num.U64.wrapping_add y k) = .core (L.cpu s) := by
  have e := hL.own_tcb hT (L.mem s) hy (k := k) (by omega) (by omega)
  unfold fld at e
  rw [e, tcbOwner, if_neg (show ¬ GateField k.val by unfold GateField; omega),
    if_pos (show TimerField k.val by unfold TimerField; omega), tOwner,
    if_pos (show (L.mem s (fld y oTIMER_DEADLINE)).val ≠ 0 from fun h => ha.1 (UScalar.eq_of_val_eq h))]
  have e2 := ha.2
  rw [Nat.shiftRight_eq_div_pow] at e2
  exact congrArg Owner.core (MoveTimer.treeCore_of (c := L.cpu s) e2)

/-- The owner of a word of the due thread's bound notification. -/
theorem fnt_ownE (hK : RegionOK K) {irq : U64} {s : S} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hY : IrqLay K st Nt irq s)
    (hne : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64)
    (hb : L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) ≠ 0#u64) {k : U64}
    (hk : k.val < 64) :
    own K (L.mem s) (core.num.U64.wrapping_add
        (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))) k) =
      ntfnOwner K (L.mem s) (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))) k.val := by
  have h0 := hI.1.choose_spec.choose_spec
  obtain ⟨q1, -⟩ := tmin_facts (BXI.blk hI) h0.cur hne
  have hNt := hI.2.2.1.2.2.bnd _ q1 hb
  obtain ⟨p1, p2⟩ := hI.2.2.1.1.ntP _ hNt
  simp only [own, hY.ntw _ hNt k hk]
  rw [ntfn_word_val p1 p2 hk, Nat.add_sub_cancel_left]

/-- A word of the due thread's bound notification other than `BOUND_TCB` is this core's. -/
theorem fnt_own (hK : RegionOK K) {irq : U64} {s : S} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hL : StLay K st T Scs Z s) (hY : IrqLay K st Nt irq s)
    (hne : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64)
    (hh : TmHere st s (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))
    (hb : L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) ≠ 0#u64) {k : U64}
    (hk : k.val < 64) (h24 : k.val ≠ 24) :
    own K (L.mem s) (core.num.U64.wrapping_add
        (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))) k) = .core (L.cpu s) := by
  have h0 := hI.1.choose_spec.choose_spec
  obtain ⟨q1, -⟩ := tmin_facts (BXI.blk hI) h0.cur hne
  have ha : L.mem s (affA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) = L.cpu s := by
    have e := hh.1
    rw [eq_of_spec_fd (obj.Tcb.affinity.spec (L := L) s _)] at e
    exact ok_inj_ff e
  have hbt := hI.2.2.1.2.2.bs.tb _ q1 hb
  have eB : L.mem s (fld (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))) 24#u64) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) := by
    have eA : fld (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))) 24#u64 =
        ntfnBtA (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))) := by
      unfold fld ntfnBtA layout.ntfn.BOUND_TCB
      rfl
    rw [eA]; exact hbt
  have ht : K.heap (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)) = some .tcb :=
    hK.tcbOf _ _ (hL.tcb _ q1 3328#u64 (by simp) (by simp))
  rw [fnt_ownE hK hI hY hne hb hk, ntfnOwner, if_neg h24, eB, if_pos ht]
  exact congrArg Owner.core ha

/-- **Every word of `FireRd` is readable** at an accepted fire-case run's entry. -/
theorem fire_rd_own (hK : RegionOK K) {irq : U64} {s : S} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hL : StLay K st T Scs Z s) (hY : IrqLay K st Nt irq s)
    (hAff : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t))
    (hok : IrqOk st s)
    (hTm : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64 →
      TmHere st s (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))
    {lk : U64 → Prop} {w : U64} (h : FireRd st T Z s w) :
    RPerm (own K) (L.cpu s) lk (L.mem s) w := by
  have hT : TcbPlaced T := hI.1.choose_spec.choose_spec.tcbs
  rcases h with h | ⟨y, hy, ha, k, h1, h2, h8, rfl⟩ | ⟨hne, hb, k, hk, -, rfl⟩
  · exact irq_rd_own hK hI hL hY hAff hok h
  · exact Or.inl (held_core (ftree_own hL hT hy ha h1 h2 h8))
  · by_cases h24 : k.val = 24
    · refine Or.inr ?_
      unfold GateOnly
      rw [fnt_ownE hK hI hY hne hb hk, ntfnOwner, if_pos h24]
    · exact Or.inl (held_core (fnt_own hK hI hL hY hne (hTm hne) hb hk h24))

/-- **No word of `FireRd` is a user word** (the case split of `fire_rd_own`). -/
theorem fire_rd_nu {irq : U64} {s : S} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hL : StLay K st T Scs Z s) (hY : IrqLay K st Nt irq s) {w : U64} (h : FireRd st T Z s w) : w ∉ K.user := by
  rcases h with h | ⟨y, hy, -, k, h1, h2, -, rfl⟩ | ⟨hne, hb, k, hk, -, rfl⟩
  · exact irq_rd_nu hI hL hY h
  · exact hL.nu_tcb hy (by omega) (by omega)
  · have h0 := hI.1.choose_spec.choose_spec
    obtain ⟨q1, -⟩ := tmin_facts (BXI.blk hI) h0.cur hne
    have hNt := hI.2.2.1.2.2.bnd _ q1 hb
    exact hL.nu (by rw [hY.ntw _ hNt k hk]; intro e; cases e)

/-- **Every word of `FireWr` is this core's** at an accepted fire-case run's entry. -/
theorem fire_wr_own (hK : RegionOK K) {irq : U64} {s : S} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hL : StLay K st T Scs Z s) (hY : IrqLay K st Nt irq s) (hok : IrqOk st s)
    (hTm : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64 →
      TmHere st s (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))
    {lk : U64 → Prop} {w : U64} (h : FireWr st T Z s w) :
    WPerm (own K) (L.cpu s) lk (L.mem s) w := by
  have hT : TcbPlaced T := hI.1.choose_spec.choose_spec.tcbs
  rcases h with h | ⟨y, hy, ha, k, h1, h2, h8, rfl⟩ | ⟨hne, hb, k, hk, -, h24, rfl⟩
  · exact irq_wr_own hI hL hok h
  · exact held_core (ftree_own hL hT hy ha (by omega) (by omega) h8)
  · exact held_core (fnt_own hK hI hL hY hne (hTm hne) hb hk h24)

/-- **The words of `FireWr` other than the current thread's `STATE` decide nothing** (`OwnMap.DecW`). -/
theorem fire_wr_nondec (hK : RegionOK K) {irq : U64} {s : S} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hL : StLay K st T Scs Z s) (hY : IrqLay K st Nt irq s) {w : U64} (h : FireWr st T Z s w)
    (hn : w ≠ stA (L.curW s)) : ¬ DecW K w := by
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  rcases h with h | ⟨y, hy, -, k, h1, h2, -, rfl⟩ | ⟨hne, hb, k, hk, -, h24, rfl⟩
  · exact irq_wr_nondec hK hI hL h hn
  · apply nondec_of_region hK
    have e : (core.num.U64.wrapping_add y k).val - y.val = k.val := by
      rw [field_val (hT y hy) (by omega)]; omega
    exact Or.inl ⟨y, hL.tcb y hy k (by omega) (by omega), by omega, by omega, by omega, by omega, by omega⟩
  · apply nondec_of_region hK
    obtain ⟨q1, -⟩ := tmin_facts (BXI.blk hI) h0.cur hne
    have hNt := hI.2.2.1.2.2.bnd _ q1 hb
    obtain ⟨p1, p2⟩ := hI.2.2.1.1.ntP _ hNt
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hY.ntw _ hNt k hk, ?_⟩))))
    rw [ntfn_word_val p1 p2 hk]
    omega

end own

section acc
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {A : Type} (ar : machine.Arch A) {m : U64 → U64}

/-- The due thread of an accepted fire-case run is this core's (`plan_facts'`, `fire_ok` of a null thread is
`false`). -/
theorem fire_tmHere {s s1 : S} {tip p : localtimer.TimerIrqPlan} {ct now : U64}
    (etip : localtimer.plan_objects st s = ok tip) (eb : localtimer.same_plan tip p = ok true)
    (efo : localtimer.fire_ok st s1 (L.cpu s) ct p now = ok true) :
    L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64 →
      TmHere st s (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)) := fun _ => by
  rcases plan_facts' etip with ⟨t1, -⟩ | ⟨t1, -, t3, -⟩
  · have hp0 : p.tm = 0#u64 := by rw [← (same_plan_tm eb).1]; exact t1
    rw [fire_ok_eq, if_pos hp0] at efo
    exact absurd (ok_inj_ff efo) (by decide)
  · rw [← t1]; exact t3

/-- The run's equations in the fire case, at the entry state's core, thread and SC. -/
theorem fire_eqs (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {irq : U64} {p : localtimer.TimerIrqPlan}
    (hq : IrqFire st ar s a) (h : localtimer.handle_timer_irq_local st ar s a irq p = ok (true, s', a')) :
    ∃ (mx now i2 : U64) (tip : localtimer.TimerIrqPlan) (x : Bool) (s1 s2 s3 : S) (a1 a2 a3 : A),
      layout.irq.MAX = ok mx ∧ ¬ irq > mx ∧ interrupt.irq_state st s irq = ok interrupt.IRQ_TIMER ∧
      localtimer.plan_objects st s = ok tip ∧ localtimer.same_plan tip p = ok true ∧
      localtimer.current_ok st s (L.cpu s) (L.curW s) (L.cscW s) = ok true ∧
      localtimer.sched_quiet st s (L.cpu s) = ok true ∧
      sched.update_timestamp st ar s a = ok (s1, a1) ∧ sched.cur_time st s1 = ok now ∧
      localtimer.release_due st s1 (L.cpu s) = ok false ∧ sched.consumed st s1 = ok i2 ∧
      sporadic.sufficient st ar s1 a1 (L.cscW s) i2 = ok true ∧
      localtimer.timer_due st s1 (L.cpu s) now = ok true ∧
      localtimer.fire_ok st s1 (L.cpu s) (L.curW s) p now = ok true ∧
      sched.check_budget st ar s1 a1 = ok (x, s2, a2) ∧
      interrupt.handle_interrupt st ar s2 a2 irq = ok (s3, a3) := by
  obtain ⟨cpu, mx, i1, ct, csc, now, i2, tip, b4, due, x, s1, s2, s3, s4, s5, a1, a2, a3, a4, a5, t, ecpu, emx,
    hle, ei1, hi1, etip, eb, ect, ecsc, eok, eq, eu, enow, erel, ei2, eb4, edue, hc, ecb, ehi, -, -, -,
    -⟩ := irq_accept_walk ar h
  subst hi1
  have ecp : cpu = L.cpu s := by
    have e := ecpu
    rw [L.cur_cpu_eq] at e; exact (ok_inj_ff e).symm
  have ecs : csc = L.cscW s := by
    have e := ecsc
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) s)] at e; exact (ok_inj_ff e).symm
  have ect' : ct = L.curW s := by
    have e := ect
    rw [cur_thread_ok] at e; exact (ok_inj_ff e).symm
  subst ecp ecs ect'
  obtain ⟨rfl, rfl⟩ := hq s1 a1 now i2 b4 due eu enow ei2 eb4 edue
  have efo : localtimer.fire_ok st s1 (L.cpu s) (L.curW s) p now = ok true := by
    cases hc with
    | quiet _ hd => exact absurd hd (by decide)
    | fire _ _ hf => exact hf
    | rr h4 _ _ => exact absurd h4 (by decide)
  exact ⟨mx, now, i2, tip, x, s1, s2, s3, a1, a2, a3, emx, hle, ei1, etip, eb, eok, eq, eu, enow, erel, ei2, eb4,
    edue, efo, ecb, ehi⟩

set_option maxHeartbeats 4000000 in
/-- **`PathObl.acc` of a fire-case run whose signal wakes nobody** (module docstring). -/
theorem irq_acc_fire_nw (hA : P0.ArchTotal ar) (hK : RegionOK K) {s s' : S} {a a' : A} {irq : U64}
    {p : localtimer.TimerIrqPlan} {lk : S → U64 → Prop}
    (hE : IrqEntK K st T Cs Ω H Sg Rp Scs Nt Z Ac m s) (hY : IrqLay K st Nt irq s)
    (hAff : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t))
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (hq : IrqFire st ar s a) (hNW : NoWake st s)
    (h : localtimer.handle_timer_irq_local st ar s a irq p = ok (true, s', a')) :
    localtimer.handle_timer_irq_local (guard st (MaxR K st lk s) (MaxW K st lk s)) ar s a irq p =
      ok (true, s', a') := by
  have hI := hE.inv
  have hL := hE.lay
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ h0.cur
  have hcT : L.curW s ∈ T := h0.curT
  obtain ⟨mx, now, i2, tip, x, s1, s2, s3, a1, a2, a3, emx, hle, ei1, etip, eb, eok, eq, eu, enow, erel, ei2, eb4,
    edue, efo, ecb, ehi⟩ := fire_eqs ar hA hq h
  have hTm := fire_tmHere etip eb efo
  have aS : Aligned (stA (L.curW s)) := by
    rw [stA_eq]; exact field_aligned (h0.tcbs _ hcT) (by simp) (by simp)
  have wS : IrqWr st Z s (stA (L.curW s)) := Or.inr (Or.inl ⟨3328#u64, by simp, by simp, by simp, stA_eq _⟩)
  refine irq_accG_fire_pre (gS := guard st (MaxR K st lk s) (MaxW K st lk s)) (R := MaxR K st lk s)
    (W := MaxW K st lk s) ar hA hI hq
    (fun hok w ha hw => ⟨irq_rd_own hK hI hL hY hAff hok hw, ha, irq_rd_nu hI hL hY hw⟩)
    (fun hok w ha hw _ => ⟨irq_wr_own hI hL hok hw, ha⟩)
    (fun _ i hi => ⟨rperm_none (hY.iq i hi).2 _, (hY.iq i hi).1, hY.iqU i hi⟩)
    (fun _ => ⟨rperm_none hL.dom _, hL.domA, hL.domU⟩)
    (fun _ => ⟨rperm_none hL.dtm _, hL.dtmA, hL.dtmU⟩) ?_ ?_ h
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
    exact fire_tail_nw (gS := guard st (MaxR K st lk s) (MaxW K st lk s)) (R := MaxR K st lk s)
      (W := MaxW K st lk s) ar hA hI hNt hok
      (fun w ha hw => ⟨fire_rd_own hK hI hL hY hAff hok hTm hw, ha, fire_rd_nu hI hL hY hw⟩)
      (fun w ha hw _ => ⟨fire_wr_own hK hI hL hY hok hTm hw, ha⟩)
      ⟨rperm_none hL.dtm _, hL.dtmA, hL.dtmU⟩
      (fun X _ _ => PathObl.GWr.write (g := guard st (MaxR K st lk s) (MaxW K st lk s))
        ⟨irq_wr_own hI hL hok wS, aS⟩ X _)
      (fun X y v hy ha _ => PathObl.GWr.write (g := guard st (MaxR K st lk s) (MaxW K st lk s))
        ⟨held_core (ftree_own hL hT hy ha (k := 3568#u64) (by simp) (by simp) (by simp)),
          field_aligned (hT y hy) (by simp) (by simp)⟩ X v)
      (fun X y v hy ha _ _ _ => PathObl.GWr.write (g := guard st (MaxR K st lk s) (MaxW K st lk s))
        ⟨held_core (ftree_own hL hT hy ha (k := 3528#u64) (by simp) (by simp) (by simp)),
          field_aligned (hT y hy) (by simp) (by simp)⟩ X v)
      hNW etip eb eq eok eu enow erel ei2 eb4 edue efo' ecb' emx hle ei1 ehi'

variable {irq : U64} {pl : localtimer.TimerIrqPlan} {lk : S → U64 → Prop} {p : SProg Bool}

set_option maxHeartbeats 4000000 in
/-- **`PathObl.move` of a fire-case run whose signal wakes nobody** (module docstring). -/
theorem irq_move_fire_nw (hA : P0.ArchTotal ar) (hK : RegionOK K) (hUO : E2E.UserOK K)
    (hp : IsProg (irqBody S irq pl) p) {s s1 : S} {a a1 : A}
    (hE : IrqEntK K st T Cs Ω H Sg Rp Scs Nt Z Ac m s) (hY : IrqLay K st Nt irq s)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (hq : IrqFire st ar s a) (hNW : NoWake st s)
    (h : localtimer.handle_timer_irq_local st ar s a irq pl = ok (true, s1, a1)) :
    localtimer.handle_timer_irq_local (mguard st
      (fun x y => StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) (L.cpu s) (lk s) (L.mem x)
        (L.mem y))) ar s a irq pl = ok (true, s1, a1) := by
  have hI := hE.inv
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  have hcT : L.curW s ∈ T := h0.curT
  have hL := hE.lay
  have heap : ∀ y ∈ T, K.heap y = some .tcb := fun y hy =>
    hK.tcbOf y _ (hL.tcb y hy 3328#u64 (by simp) (by simp))
  have m_aff : ∀ y ∈ T, m (fld y oAFFINITY) = L.mem s (affA y) := fun y hy =>
    (hE.mem _ (hUO.tcb y (heap y hy) oAFFINITY (Or.inl rfl)).1 (hUO.tcb y (heap y hy) oAFFINITY (Or.inl rfl)).2).symm
  have es : stA (L.curW s) = fld (L.curW s) oSTATE := by rw [stA_eq]; rfl
  obtain ⟨mx, now, i2, tip, x, s1', s2, s3, a1', a2, a3, emx, hle, ei1, etip, eb, eok, eq, eu, enow, erel, ei2,
    eb4, edue, efo, ecb, ehi⟩ := fire_eqs ar hA hq h
  set gS := gd st (fun _ => True) (StWrOK st K m (L.cpu s) (lk s)) with egS
  have hwS : IrqOk st s → ∀ X, L.mem X (stA (L.curW s)) = sched.TS_RESTART →
      L.mem X (affA (L.curW s)) = L.cpu s →
      gS.write X (stA (L.curW s)) sched.TS_RUNNING = st.write X (stA (L.curW s)) sched.TS_RUNNING :=
    fun hok X hX haff => gd_write (by
      show StWrOK st K m (L.cpu s) (lk s) X (stA (L.curW s)) sched.TS_RUNNING
      unfold StWrOK
      rw [es]
      exact stepOK_state hK hUO (heap _ hcT) haff (by rw [m_aff _ hcT]; exact hok.aff)
        (fun hq => absurd hq (by rw [← es, hX]; simp [QueuedState, sched.TS_RESTART]))
        (fun hq => absurd hq (by simp [QueuedState, sched.TS_RUNNING])))
  have hg : localtimer.handle_timer_irq_local gS ar s a irq pl = ok (true, s1, a1) := by
    refine irq_accG_fire_pre (gS := gS) (R := fun _ => True) (W := WAll (StWrOK st K m (L.cpu s) (lk s))) ar hA hI
      hq (fun _ _ _ _ => trivial)
      (fun _ w ha hw hn x v => stepOK_nondec hK hUO ha (irq_wr_nondec hK hI hL hw hn))
      (fun _ _ _ => trivial) (fun _ => trivial) (fun _ => trivial) ?_ ?_ h
    · intro _ s1'' a1'' now' _ _
      have mr : ∀ c t : U64, MayRdC st (fun _ => True) s1'' c t := fun _ _ _ =>
        ⟨trivial, fun _ => ⟨trivial, trivial, trivial, trivial, fun _ => trivial⟩⟩
      have tr : TopRdC st (fun _ => True) s1'' :=
        { l1 := trivial, dom := trivial, bm := ⟨trivial, fun _ _ => trivial⟩
          top := fun _ _ _ _ _ _ _ => ⟨trivial, fun _ => ⟨trivial, fun _ => ⟨trivial, trivial, trivial, trivial,
            fun _ => trivial⟩⟩⟩ }
      have wr : ∀ w n : U64, WakeRdC st (fun _ => True) s1'' w n := fun w n =>
        { may := mr _ w, dq := fun _ _ => ⟨trivial, trivial⟩, nsc := trivial, top := tr }
      have c1 : L.cpu s1'' = L.cpu s := by
        obtain ⟨n1, -, er⟩ := ut_now ar hA (h0.nodes _ h0.cur) (by assumption)
        simp only at er
        rw [er, utW_cpu]
      have := fire_ok.guardK (gS := gS) (R := fun _ => True) (s := s1'') (ct := L.curW s) (p := pl) (now := now')
        (fun _ => True) (fun _ => trivial) (fun _ => trivial) (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
        (fun _ _ => ⟨trivial, fun _ _ _ => trivial⟩) (fun _ _ => trivial)
        (fun _ => fireTail.guardC (fun _ => ⟨trivial, trivial, trivial, trivial, wr _ _, fun _ _ => wr _ _⟩))
      rwa [c1] at this
    · intro hok s1'' a1'' x' s2' a2' s3' a3' now' eu' enow' efo' ecb' ehi'
      rw [eu] at eu'
      have e1 := ok_inj_ff eu'
      simp only [Prod.mk.injEq] at e1
      obtain ⟨rfl, rfl⟩ := e1
      rw [enow] at enow'
      obtain rfl := ok_inj_ff enow'
      have hdl : ∀ y ∈ T, FootLtArmed st s (L.cpu s) y → thA y = fld y oTIMER_HEIGHT := fun _ _ _ => rfl
      have hdd : ∀ y ∈ T, FootLtArmed st s (L.cpu s) y → tdA y = fld y oTIMER_DEADLINE := fun _ _ _ => rfl
      exact fire_tail_nw (gS := gS) (R := fun _ => True) (W := WAll (StWrOK st K m (L.cpu s) (lk s))) ar hA hI
        hNt hok (fun _ _ _ => trivial)
        (fun w ha hw hn x v => stepOK_nondec hK hUO ha (fire_wr_nondec hK hI hL hY hw hn))
        trivial (hwS hok)
        (fun X y v hy ha hc => gd_write (by
          show StWrOK st K m (L.cpu s) (lk s) X (thA y) v
          unfold StWrOK
          rw [hdl y hy ha]
          exact stepOK_height hK hUO (heap y hy) hc))
        (fun X y v hy ha ha1 ha0 hc => gd_write (by
          show StWrOK st K m (L.cpu s) (lk s) X (tdA y) v
          unfold StWrOK
          rw [hdd y hy ha]
          exact stepOK_deadline hK hUO (heap y hy) ha1 (by rw [m_aff y hy]; exact ha0) hc))
        hNW etip eb eq eok eu enow erel ei2 eb4 edue efo' ecb' emx hle ei1 ehi'
  have eP : ∀ mm : machine.Store S,
      localtimer.handle_timer_irq_local mm ar s a irq pl = interp mm ar p s a :=
    fun mm => congrFun (congrFun (hp A ar mm) s) a
  rw [eP] at hg
  rw [eP]
  exact interp_gd (R := fun _ => True) (P := StWrOK st K m (L.cpu s) (lk s))
    (Q := fun x y => StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) (L.cpu s) (lk s) (L.mem x)
      (L.mem y)) (I := fun _ => True)
    (fun x q v x' _ hq hw => by
      rw [L.write_eq] at hw
      have e := ok_inj_ff hw
      subst e
      exact ⟨hq, trivial⟩) p s a _ trivial hg

end acc

end Fl4Proofs.P2
