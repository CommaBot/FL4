/-
# P2: the words an accepted timer interrupt touches are its own (`PathObl.acc` with `MaxR` / `MaxW`)

With the ownership map `OwnMap.own K`, at the entry state of an accepted run (`IrqOk`):

* `irq_rd_own`: every word of `IrqRd` is readable (`RPerm`): this core's node words; the current thread's words
  (the gate's or, the thread homed here, this core's: `IrqRd` leaves out its endpoint queue links); the current SC
  (`CORE` the gate's, the rest this core's); the release head's `SC` word (the gate's) and SC (this core's, by
  `AffSc`); of the earliest armed thread `tm`: `AFFINITY` / `BOUND_NTFN` (the gate's), the timer words (this core's
  tree's, `tm` armed in it), and once `tm` is this core's (`TmHere`) its `STATE`, `BLOCK_OBJ`, `REPLY_OBJ` (its home
  core's) and its bound notification (bound back to `tm`, P1 `BndS.tb`: `tm`'s home core's; `BOUND_TCB` the
  gate's); the current thread's slot cap words (the gate's).
* `irq_wr_own`: every word of `IrqWr` is this core's (`WPerm`).
* `irq_acc_own`: `PathObl.acc` for `ReadSet` / `WriteSet` = `MaxR` / `MaxW`, quiet or round-robin (`irq_accG`), the
  fire case a premise.

Premises: `IrqLay` [J] (layout facts beyond `StLay`, as `OwnMap.RegionOK`, from P1's typed-heap disjointness: the
IRQ state words, the kernel root word, the ASID table and pool words lie in no object; a notification of `Nt` is
its region's; the current thread's slot cap words (offsets below 192, its six TCB slots; p2lf gen14, was 256) lie in
its own TCB slots); `hAff` [J] (p2j `AffSc`, as
`st_rd_own`'s); `IrqEntK.lay` [J] / `asid` [J]; `hF` (the fire case, p2j's line).
-/
import Fl4Proofs.P2.FootTimerIrqLP
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.Serial (Owner)
open Fl4Proofs.P2.OwnMap Fl4Proofs.P2.PathObl
open Classical

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}

/-- **Layout facts of the timer interrupt** [J] (module docstring) at the entry state `s`. -/
structure IrqLay (K : KLayout) (st : machine.Store S) [L : LawfulStore st] (Nt : Set U64) (irq : U64) (s : S) :
    Prop where
  iq : ∀ i, interrupt.state_off irq = ok i →
    Aligned (core.num.U64.wrapping_add (L.ksb s) i) ∧ region K (core.num.U64.wrapping_add (L.ksb s) i) = .none
  kr : Aligned (krA (L := L) s) ∧ region K (krA (L := L) s) = .none
  tab : ∀ hi : U64, hi.val < 2048 →
    (Aligned (atAF (L.ksb s) hi) ∧ region K (atAF (L.ksb s) hi) = .none) ∧
    ∀ lo : U64, lo.val < 512 → L.mem s (atAF (L.ksb s) hi) ≠ 0#u64 →
      Aligned (peAF (L.mem s (atAF (L.ksb s) hi)) lo) ∧ region K (peAF (L.mem s (atAF (L.ksb s) hi)) lo) = .none
  ntw : ∀ n ∈ Nt, ∀ k : U64, k.val < 64 → region K (core.num.U64.wrapping_add n k) = .ntfn n
  cs : ∀ k : U64, k.val < 192 → k.val % 32 < 16 → ∃ p, region K (core.num.U64.wrapping_add (L.curW s) k) = .slot p ∧
    TcbSlot K p ∧ (core.num.U64.wrapping_add (L.curW s) k).val - p.val < 16

theorem rperm_none {lk : U64 → Prop} {m : U64 → U64} {x : U64} (h : region K x = .none) (c : U64) :
    RPerm (own K) c lk m x :=
  Or.inr (by unfold GateOnly; simp only [own, h])

/-- **What `plan_objects` / `timer_due` read of the earliest armed thread is readable** (`TmWords`; no
`current_ok` needed): its `AFFINITY` / `BOUND_NTFN` (the gate's), its timer words (this core's tree's), and once it is
this core's its `STATE`, `BLOCK_OBJ`, `REPLY_OBJ` (its home core's) and its bound notification's words. -/
theorem tmw_own (hK : RegionOK K) {irq : U64} {s : S} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hL : StLay K st T Scs Z s) (hY : IrqLay K st Nt irq s) {lk : U64 → Prop} {w : U64}
    (hne : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64)
    (hw : TmWords st s (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)) w) :
    RPerm (own K) (L.cpu s) lk (L.mem s) w := by
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  have gate : ∀ {x k : U64}, x ∈ T → 256 ≤ k.val → k.val < 4096 → GateField k.val →
      RPerm (own K) (L.cpu s) lk (L.mem s) (core.num.U64.wrapping_add x k) := fun hx h1 h2 hg =>
    Or.inr (by
      have e := hL.own_tcb hT (L.mem s) hx h1 h2
      unfold fld at e
      unfold GateOnly; rw [e, tcbOwner, if_pos hg])
  have home : ∀ {x k : U64}, x ∈ T → 256 ≤ k.val → k.val < 4096 → L.mem s (affA x) = L.cpu s →
      ¬ TimerField k.val → ¬ GField k.val →
      RPerm (own K) (L.cpu s) lk (L.mem s) (core.num.U64.wrapping_add x k) := @fun x k hx h1 h2 ha hti hg => by
    have e := hL.own_tcb hT (L.mem s) hx h1 h2
    unfold fld at e
    unfold RPerm GateOnly
    rw [e]
    unfold tcbOwner
    by_cases hga : GateField k.val
    · rw [if_pos hga]; exact Or.inr rfl
    · rw [if_neg hga, if_neg hti, if_neg hg]; exact Or.inl ha
  obtain ⟨q1, harm⟩ := tmin_facts (BXI.blk hI) h0.cur hne
  rcases hw with ⟨k, hk, rfl⟩ | ⟨hh, ⟨k, hk, rfl⟩ | ⟨hb, rfl | rfl⟩⟩
  · rcases hk with hk | hk | hk | hk
    · exact gate q1 (by omega) (by omega) (by unfold GateField; omega)
    rotate_left 2
    · exact gate q1 (by omega) (by omega) (by unfold GateField; omega)
    all_goals
      have e := hL.own_tcb hT (L.mem s) q1 (k := k) (by omega) (by omega)
      unfold fld at e
      refine Or.inl ?_
      rw [e, tcbOwner, if_neg (show ¬ GateField k.val by unfold GateField; omega),
        if_pos (show TimerField k.val by unfold TimerField; omega), tOwner,
        if_pos (show (L.mem s (fld (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)) oTIMER_DEADLINE)).val ≠ 0
          from fun h => harm.1 (UScalar.eq_of_val_eq h))]
      have e2 := harm.2
      rw [Nat.shiftRight_eq_div_pow] at e2
      exact MoveTimer.treeCore_of (c := L.cpu s) e2
  · have ha : L.mem s (affA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) = L.cpu s := by
      have e := hh.1
      rw [eq_of_spec_fd (obj.Tcb.affinity.spec (L := L) s _)] at e
      exact ok_inj_ff e
    exact home q1 (by omega) (by omega) ha (by unfold TimerField; omega) (by unfold GField; omega)
  all_goals
    have ha : L.mem s (affA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) = L.cpu s := by
      have e := hh.1
      rw [eq_of_spec_fd (obj.Tcb.affinity.spec (L := L) s _)] at e
      exact ok_inj_ff e
    have hNt := hI.2.2.1.2.2.bnd _ q1 hb
    have hbt := hI.2.2.1.2.2.bs.tb _ q1 hb
    obtain ⟨p1, p2⟩ := hI.2.2.1.1.ntP _ hNt
    have nown : ∀ k : U64, k.val < 64 →
        own K (L.mem s) (core.num.U64.wrapping_add
          (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))) k) =
        ntfnOwner K (L.mem s) (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))) k.val := by
      intro k hk
      simp only [own, hY.ntw _ hNt k hk]
      rw [ntfn_word_val p1 p2 hk, Nat.add_sub_cancel_left]
  · have e := nown layout.ntfn.TAIL_STATE (by simp [layout.ntfn.TAIL_STATE])
    have eB : L.mem s (fld (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))) 24#u64) =
        L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) := by
      have eA : fld (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))) 24#u64 =
          ntfnBtA (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))) := by
        unfold fld ntfnBtA layout.ntfn.BOUND_TCB
        rfl
      rw [eA]; exact hbt
    have ht : K.heap (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)) = some .tcb :=
      hK.tcbOf _ _ (hL.tcb _ q1 3328#u64 (by simp) (by simp))
    have hv : layout.ntfn.TAIL_STATE.val = 8 := by simp [layout.ntfn.TAIL_STATE]
    refine Or.inl ?_
    rw [e, hv, ntfnOwner, if_neg (by omega), eB, if_pos ht]
    exact ha
  · have e := nown layout.ntfn.BOUND_TCB (by simp [layout.ntfn.BOUND_TCB])
    have hv : layout.ntfn.BOUND_TCB.val = 24 := by simp [layout.ntfn.BOUND_TCB]
    refine Or.inr ?_
    unfold GateOnly
    rw [e, hv, ntfnOwner, if_pos rfl]

/-- **Every word of `IrqRd` is readable** at an accepted run's entry (module docstring). -/
theorem irq_rd_own (hK : RegionOK K) {irq : U64} {s : S} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hL : StLay K st T Scs Z s) (hY : IrqLay K st Nt irq s)
    (hAff : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t))
    (hok : IrqOk st s) {lk : U64 → Prop} {w : U64} (h : IrqRd st Z s w) :
    RPerm (own K) (L.cpu s) lk (L.mem s) w := by
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  have hcT : L.curW s ∈ T := h0.curT
  have hcs : L.cscW s ∈ Scs := hI.2.2.1.2.2.cur
  have scw : ∀ {p b : U64}, p ∈ Scs → InSC p (Z p) b → L.mem s (scCoreA p) = L.cpu s →
      RPerm (own K) (L.cpu s) lk (L.mem s) b := fun hp hb hc => by
    have e := sc_own hL hp hb hc
    split at e
    · exact Or.inr e
    · exact Or.inl (held_core e)
  have gate : ∀ {x k : U64}, x ∈ T → 256 ≤ k.val → k.val < 4096 → GateField k.val →
      RPerm (own K) (L.cpu s) lk (L.mem s) (core.num.U64.wrapping_add x k) := fun hx h1 h2 hg =>
    Or.inr (by
      have e := hL.own_tcb hT (L.mem s) hx h1 h2
      unfold fld at e
      unfold GateOnly; rw [e, tcbOwner, if_pos hg])
  have home : ∀ {x k : U64}, x ∈ T → 256 ≤ k.val → k.val < 4096 → L.mem s (affA x) = L.cpu s →
      ¬ TimerField k.val → ¬ GField k.val →
      RPerm (own K) (L.cpu s) lk (L.mem s) (core.num.U64.wrapping_add x k) := @fun x k hx h1 h2 ha hti hg => by
    have e := hL.own_tcb hT (L.mem s) hx h1 h2
    unfold fld at e
    unfold RPerm GateOnly
    rw [e]
    unfold tcbOwner
    by_cases hga : GateField k.val
    · rw [if_pos hga]; exact Or.inr rfl
    · rw [if_neg hga, if_neg hti, if_neg hg]; exact Or.inl ha
  rcases h with ⟨o, ho, -, rfl⟩ | ⟨k, h1, h2, -, h4, h5, h6, rfl⟩ | h | ⟨hne, rfl | h⟩ | ⟨hne, hw⟩ |
      ⟨k, hk, hk32, -, rfl⟩
  · exact Or.inl (held_core (hL.own_node _ ho))
  · exact home hcT h1 h2 hok.aff (by unfold TimerField; omega) (by unfold GField; omega)
  · exact scw hcs h hok.core
  · obtain ⟨r1, -, -, -, -⟩ := rel_facts hI hne
    exact gate r1 (by simp) (by simp) (by simp [GateField])
  · obtain ⟨r1, r2, r3, r4, -⟩ := rel_facts hI hne
    exact scw r4 h (by rw [hAff _ r1 r3, r2])
  · exact tmw_own hK hI hL hY hne hw
  · obtain ⟨p, hr, hts, hlt⟩ := hY.cs k hk hk32
    refine Or.inr ?_
    unfold GateOnly
    simp only [own, hr, slotOwner]
    rw [if_neg (by omega), if_pos hts]

/-- **Every word of `IrqWr` is this core's** at an accepted run's entry. -/
theorem irq_wr_own {s : S} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hL : StLay K st T Scs Z s)
    (hok : IrqOk st s) {lk : U64 → Prop} {w : U64} (h : IrqWr st Z s w) :
    WPerm (own K) (L.cpu s) lk (L.mem s) w := by
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  have hcT : L.curW s ∈ T := h0.curT
  have hcs : L.cscW s ∈ Scs := hI.2.2.1.2.2.cur
  have hq := scq_of hI.2.2.1.1 hI.2.2.2.2 hcs
  have home : ∀ k : U64, 256 ≤ k.val → k.val < 4096 → ¬ GateField k.val → ¬ TimerField k.val →
      ¬ GField k.val → WPerm (own K) (L.cpu s) lk (L.mem s) (core.num.U64.wrapping_add (L.curW s) k) :=
    fun k h1 h2 hga hti hg => by
      have e := hL.own_tcb hT (L.mem s) hcT h1 h2
      unfold fld at e
      unfold WPerm
      rw [e, tcbOwner, if_neg hga, if_neg hti, if_neg hg]
      exact hok.aff
  rcases h with ⟨o, ho, -, rfl⟩ | ⟨k, h1, h2, -, rfl⟩ | h | rfl | rfl | rfl | rfl
  · exact held_core (hL.own_node _ ho)
  · exact home k h1 (by omega) (by unfold GateField; omega) (by unfold TimerField; omega)
      (by unfold GField; omega)
  · have e := sc_own hL hcs h.inSC hok.core
    rw [if_neg (by unfold InRing at h; omega)] at e
    exact held_core e
  · have e := sc_own hL hcs hq.2.2.1.1 hok.core
    obtain ⟨hP, hz⟩ := hI.2.2.1.1.sc _ hcs
    have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
    have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
    rw [if_neg (by rw [hv, hcv]; omega)] at e
    exact held_core e
  · exact home 3480#u64 (by simp) (by simp) (by simp [GateField]) (by simp [TimerField]) (by simp [GField])
  · exact home 3488#u64 (by simp) (by simp) (by simp [GateField]) (by simp [TimerField]) (by simp [GField])
  · exact home 3592#u64 (by simp) (by simp) (by simp [GateField]) (by simp [TimerField]) (by simp [GField])

variable {A : Type} (ar : machine.Arch A) {m : U64 → U64}

/-- **`PathObl.acc` for the timer interrupt**, quiet or round-robin, the fire case a premise (module docstring). -/
theorem irq_acc_own (hA : P0.ArchTotal ar) (hK : RegionOK K) {s s' : S} {a a' : A} {irq : U64}
    {p : localtimer.TimerIrqPlan} {lk : S → U64 → Prop}
    (hE : IrqEntK K st T Cs Ω H Sg Rp Scs Nt Z Ac m s) (hY : IrqLay K st Nt irq s)
    (hAff : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t))
    (hF : IrqFire st ar s a → localtimer.handle_timer_irq_local (guard st (MaxR K st lk s) (MaxW K st lk s)) ar s a
      irq p = ok (true, s', a'))
    (h : localtimer.handle_timer_irq_local st ar s a irq p = ok (true, s', a')) :
    localtimer.handle_timer_irq_local (guard st (MaxR K st lk s) (MaxW K st lk s)) ar s a irq p =
      ok (true, s', a') := by
  have hI := hE.inv
  have hL := hE.lay
  have h0 := hI.1.choose_spec.choose_spec
  have hcT : L.curW s ∈ T := h0.curT
  have aS : Aligned (stA (L.curW s)) := by
    rw [stA_eq]; exact field_aligned (h0.tcbs _ hcT) (by simp) (by simp)
  have wS : IrqWr st Z s (stA (L.curW s)) := Or.inr (Or.inl ⟨3328#u64, by simp, by simp, by simp, stA_eq _⟩)
  exact irq_accG (gS := guard st (MaxR K st lk s) (MaxW K st lk s)) (R := MaxR K st lk s) (W := MaxW K st lk s)
    ar hA hI
    (fun hok w ha hw => ⟨irq_rd_own hK hI hL hY hAff hok hw, ha⟩)
    (fun hok w ha hw _ => ⟨irq_wr_own hI hL hok hw, ha⟩)
    (fun _ i hi => ⟨rperm_none (hY.iq i hi).2 _, (hY.iq i hi).1⟩)
    (fun _ => ⟨rperm_none hL.dom _, hL.domA⟩)
    (fun _ => ⟨rperm_none hL.dtm _, hL.dtmA⟩)
    (fun hok X _ _ => PathObl.GWr.write (g := guard st (MaxR K st lk s) (MaxW K st lk s))
      ⟨irq_wr_own hI hL hok wS, aS⟩ X _)
    (fun _ => ⟨rperm_none hY.kr.2 _, hY.kr.1⟩)
    (fun _ hi hhi => ⟨⟨rperm_none (hY.tab hi hhi).1.2 _, (hY.tab hi hhi).1.1⟩,
      fun lo hlo hne => ⟨rperm_none ((hY.tab hi hhi).2 lo hlo hne).2 _, ((hY.tab hi hhi).2 lo hlo hne).1⟩⟩)
    hE.asid hF h

end

end Fl4Proofs.P2
