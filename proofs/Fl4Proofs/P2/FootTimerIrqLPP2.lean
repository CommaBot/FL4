/-
# P2 (p2lf): the timer interrupt local path with the whole waking fire case proved

`irq_localPathP2`: `irq_localPathP` (`P2/FootTimerIrqLPP`) with `hSwT` / `hSwTm` discharged: `irq_acc_fire_wk2` /
`irq_move_fire_wk2` are `irq_acc_fire_wk` / `irq_move_fire_wk` with `fire_tail_wk2` (`P2/FootTimerFireSy`, the tail
when the action is the woken thread proved by `aw_tail_sw`) in place of `fire_tail_wk`; the switch block's reads of
the new thread's VSpace slot words come from `SlotLay` (`slot_maxR`), the kernel root and ASID table from
`IrqLay.kr` / `.tab`, the ASID table's frame from P1 `AsidOff` (`IrqEntK.asid`).

`irq_acc_fire_wk2` / `irq_move_fire_wk2` take `hBA` over this run's own states (gen13: `update_timestamp` from `s`,
`check_budget`, `handle_interrupt`), so `irq_localPathP3` (`P2/FootTimerIrqLPP3`) can prove it; `irq_localPathP2`
keeps its statement (its arbitrary-state `hBA` implies the run form).

Premises: as `irq_localPathP` without `hSwT` / `hSwTm` (`hp` [P], `hz` [W], `hm` [P], `hro` [W], `IrqEnt`'s [J]
parts, `hEU` [J], `hlk` [P], `hPL` [P], `hOL` [J], `hBA` [P]), plus

* `hSL` [J] (`SlotLay K st T s`: the capability words of the TCB slots of every thread homed on this core lie in
  slot regions of TCBs — `IrqLay.cs` generalised from the current thread to every local thread).
-/
import Fl4Proofs.P2.FootTimerFireSy
import Fl4Proofs.P2.FootTimerIrqLPP
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.Serial (Owner)
open Fl4Proofs.P2.OwnMap Fl4Proofs.P2.PathObl
open Classical

section slot
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {K : KLayout}

/-- **[J] The slot words of this core's threads** (`IrqLay.cs` for every thread homed on this core at `s`): the
capability words of each TCB slot lie in a slot region of a TCB. -/
def SlotLay (K : KLayout) (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s : S) : Prop :=
  ∀ y, LocT st T s y → ∀ k : U64, k.val < 256 → k.val % 32 < 16 → ∃ p,
    region K (core.num.U64.wrapping_add y k) = .slot p ∧ TcbSlot K p ∧
      (core.num.U64.wrapping_add y k).val - p.val < 16

theorem slot_maxR {s : S} {lk : S → U64 → Prop} (hT : TcbPlaced T) (hSL : SlotLay K st T s)
    (hu : ∀ b ∈ K.user, region K b = .none) {y : U64}
    (hy : LocT st T s y) :
    MaxR K st lk s (vtA y) ∧ MaxR K st lk s (core.num.U64.wrapping_add (vtA y) 8#u64) := by
  have hy' := hT y hy.1
  have one : ∀ k : U64, k.val < 256 → k.val % 32 < 16 → k.val % 8 = 0 →
      MaxR K st lk s (core.num.U64.wrapping_add y k) := fun k hk hk32 hk8 => by
    obtain ⟨p, hr, hts, hlt⟩ := hSL y hy k hk hk32
    refine ⟨Or.inr ?_, field_aligned hy' (by omega) hk8, fun hb => by rw [hu _ hb] at hr; cases hr⟩
    unfold GateOnly
    simp only [own, hr, slotOwner]
    rw [if_neg (by omega), if_pos hts]
  have e1 : vtA y = core.num.U64.wrapping_add y 32#u64 := by
    apply UScalar.eq_of_val_eq
    rw [vtA_val hy', tcb_wadd_val hy' (by simp)]; simp
  have e2 : core.num.U64.wrapping_add (vtA y) 8#u64 = core.num.U64.wrapping_add y 40#u64 := by
    apply UScalar.eq_of_val_eq
    have := hy'.fits
    rw [tcb_wadd_val hy' (by simp)]
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, vtA_val hy']
    omega
  rw [e2, e1]
  exact ⟨one _ (by simp) (by simp) (by simp), one _ (by simp) (by simp) (by simp)⟩

/-- **[J] The VSpace slot words of this core's threads** (gen13; what the switch block reads, `SwAcc`): `SlotLay`
narrowed to the two words of TCB slot 1 (`vtA y`, `vtA y + 8`). Unlike `SlotLay` (offsets below 256, eight slots)
it holds for P3's layout (`layoutJ`: a TCB has `tcbSlots = 6` slots), `slotLayV_of_JAtZ` (P2/FootTimerIrqSlotJ). -/
def SlotLayV (K : KLayout) (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s : S) : Prop :=
  ∀ y, LocT st T s y → ∀ k : U64, (k.val = 32 ∨ k.val = 40) → ∃ p,
    region K (core.num.U64.wrapping_add y k) = .slot p ∧ TcbSlot K p ∧
      (core.num.U64.wrapping_add y k).val - p.val < 16

theorem SlotLay.v {s : S} (h : SlotLay K st T s) : SlotLayV K st T s :=
  fun y hy k hk => h y hy k (by omega) (by omega)

theorem slot_maxRV {s : S} {lk : S → U64 → Prop} (hT : TcbPlaced T) (hSL : SlotLayV K st T s)
    (hu : ∀ b ∈ K.user, region K b = .none) {y : U64}
    (hy : LocT st T s y) :
    MaxR K st lk s (vtA y) ∧ MaxR K st lk s (core.num.U64.wrapping_add (vtA y) 8#u64) := by
  have hy' := hT y hy.1
  have one : ∀ k : U64, (k.val = 32 ∨ k.val = 40) → MaxR K st lk s (core.num.U64.wrapping_add y k) :=
    fun k hk => by
    obtain ⟨p, hr, hts, hlt⟩ := hSL y hy k hk
    refine ⟨Or.inr ?_, field_aligned hy' (by omega) (by omega), fun hb => by rw [hu _ hb] at hr; cases hr⟩
    unfold GateOnly
    simp only [own, hr, slotOwner]
    rw [if_neg (by omega), if_pos hts]
  have e1 : vtA y = core.num.U64.wrapping_add y 32#u64 := by
    apply UScalar.eq_of_val_eq
    rw [vtA_val hy', tcb_wadd_val hy' (by simp)]; simp
  have e2 : core.num.U64.wrapping_add (vtA y) 8#u64 = core.num.U64.wrapping_add y 40#u64 := by
    apply UScalar.eq_of_val_eq
    have := hy'.fits
    rw [tcb_wadd_val hy' (by simp)]
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, vtA_val hy']
    omega
  rw [e2, e1]
  exact ⟨one _ (Or.inl (by simp)), one _ (Or.inr (by simp))⟩

end slot

section acc
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {A : Type} (ar : machine.Arch A) {m : U64 → U64}

set_option maxHeartbeats 16000000 in
/-- **`PathObl.acc` of a waking fire-case run**, the action-`w` tail proved (module docstring). -/
theorem irq_acc_fire_wk2 (hA : P0.ArchTotal ar) (hK : RegionOK K) {s s' : S} {a a' : A} {irq : U64}
    {p : localtimer.TimerIrqPlan} {lk : S → U64 → Prop} {U : Set U64}
    (hE : IrqEntK K st T Cs Ω H Sg Rp Scs Nt Z Ac m s) (hY : IrqLay K st Nt irq s)
    (hAff : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t))
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (hOL : ObjLay K H Rp) (hPL : PlanLk lk p)
    (hBA : ∀ s1 a1 x s2 a2 s3 a3, sched.update_timestamp st ar s a = ok (s1, a1) →
      sched.check_budget st ar s1 a1 = ok (x, s2, a2) → interrupt.handle_interrupt st ar s2 a2 irq = ok (s3, a3) →
      BufAt st T Cs H Sg Scs Z U s3)
    (hSL : SlotLayV K st T s)
    (hq : IrqFire st ar s a) (hW : ¬ NoWake st s)
    (h : localtimer.handle_timer_irq_local st ar s a irq p = ok (true, s', a')) :
    localtimer.handle_timer_irq_local (guard st (MaxR K st lk s) (MaxW K st lk s)) ar s a irq p =
      ok (true, s', a') := by
  have hI := hE.inv
  have hb := irq_lt_of_acc ar h
  have hL := hE.lay
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ h0.cur
  have hcT : L.curW s ∈ T := h0.curT
  have hX := hI.2.2.1
  have hO := hX.1
  obtain ⟨mx, now, i2, tip, x, s1, s2, s3, a1, a2, a3, emx, hle, ei1, etip, eb, eok, eq, eu, enow, erel, ei2, eb4,
    edue, efo, ecb, ehi⟩ := fire_eqs ar hA hq h
  obtain ⟨hPE, hPR⟩ := plan_pe_pr hI etip eb
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
    (fun hok w ha hw => ⟨irq_rd_own hK hI hL hY hAff hok hw, ha, irq_rd_nu hI hL hY hw⟩)
    (fun hok w ha hw _ => ⟨irq_wr_own hI hL hok hw, ha⟩)
    (fun _ i hi => ⟨rperm_none (hY.iq hb i hi).2 _, (hY.iq hb i hi).1, hY.iqU hb i hi⟩)
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
    have g3328 : ¬ GateField (3328#u64 : U64).val := by unfold GateField; simp
    have t3328 : ¬ TimerField (3328#u64 : U64).val := by unfold TimerField; simp
    have f3328 : ¬ GField (3328#u64 : U64).val := by unfold GField; simp
    exact fire_tail_wk2 (gS := guard st (MaxR K st lk s) (MaxW K st lk s)) (R := MaxR K st lk s)
      (W := MaxW K st lk s) (Lk := lk s) (U := U) ar hA hI hNt hok
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
      hW hAff
      (fun y hy K h1 h2 h3 ht hg => ⟨loc_rd_own hI hL (Or.inr (Or.inl ⟨y, hy, K, h1, h2, h3, ht, hg, rfl⟩)),
        field_aligned (hT y hy.1) h2 h3, hL.nu_tcb hy.1 h1 h2⟩)
      (fun y hy K h1 h2 h3 hga ht hg _ _ =>
        ⟨loc_wr_own hI hL (Or.inr (Or.inl ⟨y, hy, K, h1, h2, h3, hga, ht, hg, rfl⟩)),
          field_aligned (hT y hy.1) h2 h3⟩)
      (fun q hq hc b ha hb => ⟨loc_rd_own hI hL (Or.inr (Or.inr ⟨q, hq, hc, hb⟩)), ha, hL.nu_sc hq hb⟩)
      (fun q hq hc b ha hb h16 => ⟨loc_wr_own hI hL (Or.inr (Or.inr ⟨q, hq, hc, hb, h16⟩)), ha⟩)
      (fun y hy hqs hlk k hk => by
        have o := lkw_own hI hL (Lk := lk s) (fun _ h => h) (Or.inl ⟨y, hy, hqs, hlk, k, hk, rfl⟩)
        have ha := field_aligned (hT y hy) (K := k) (by omega) (by omega)
        exact ⟨⟨o.2, ha, hL.nu_held o.1⟩, ⟨o.1, ha⟩⟩)
      ⟨rperm_none hL.dom _, hL.domA, hL.domU⟩
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
        exact ⟨⟨o.2, hal k h1 h2, hL.nu_held o.1⟩, ⟨o.1, hal k h1 h2⟩⟩)
      (fun hr => by
        obtain ⟨hR, hal⟩ := hPR hr
        have o := lkw_own hI hL (Lk := lk s) (w := rTcbA p.reply) (fun _ h => h)
          (Or.inr ⟨p.reply, (hPL s).2.2 hr, by unfold rTcbA; exact hOL.2 _ hR _ (by simp [layout.reply.TCB])⟩)
        exact ⟨o.1, hal⟩)
      etip eb eq eok eu enow erel ei2 eb4 edue efo' ecb' emx hle ei1 ehi' (hBA _ _ _ _ _ _ _ eu ecb' ehi') hE.asid
        (fun y hy => slot_maxRV hT hSL hL.user hy) ⟨rperm_none hY.kr.2 _, hY.kr.1, hY.krU⟩
        (fun hi hhi => ⟨⟨rperm_none (hY.tab hi hhi).1.2 _, (hY.tab hi hhi).1.1, (hY.tabU hi hhi).1⟩,
          fun lo hlo hne => ⟨rperm_none ((hY.tab hi hhi).2 lo hlo hne).2 _, ((hY.tab hi hhi).2 lo hlo hne).1,
            (hY.tabU hi hhi).2 lo hlo hne⟩⟩)

end acc

section move
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {A : Type} (ar : machine.Arch A) {m : U64 → U64}
variable {irq : U64} {pl : localtimer.TimerIrqPlan} {lk : S → U64 → Prop} {p : SProg Bool}

set_option maxHeartbeats 16000000 in
/-- **`PathObl.move` of a waking fire-case run**, the action-`w` tail proved (module docstring). -/
theorem irq_move_fire_wk2 (hA : P0.ArchTotal ar) (hK : RegionOK K) (hUO : E2E.UserOK K)
    (hp : IsProg (irqBody S irq pl) p) {s s1 : S} {a a1 : A} {U : Set U64}
    (hE : IrqEntK K st T Cs Ω H Sg Rp Scs Nt Z Ac m s) (hY : IrqLay K st Nt irq s)
    (hAff : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t))
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (hOL : ObjLay K H Rp) (hPL : PlanLk lk pl)
    (hBA : ∀ s1 a1 x s2 a2 s3 a3, sched.update_timestamp st ar s a = ok (s1, a1) →
      sched.check_budget st ar s1 a1 = ok (x, s2, a2) → interrupt.handle_interrupt st ar s2 a2 irq = ok (s3, a3) →
      BufAt st T Cs H Sg Scs Z U s3)
    (hq : IrqFire st ar s a) (hW : ¬ NoWake st s)
    (h : localtimer.handle_timer_irq_local st ar s a irq pl = ok (true, s1, a1)) :
    localtimer.handle_timer_irq_local (mguard st
      (fun x y => StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) (L.cpu s) (lk s) (L.mem x)
        (L.mem y))) ar s a irq pl = ok (true, s1, a1) := by
  have hI := hE.inv
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  have hcT : L.curW s ∈ T := h0.curT
  have hL := hE.lay
  have hX := hI.2.2.1
  have hO := hX.1
  have heap : ∀ y ∈ T, K.heap y = some .tcb := fun y hy =>
    hK.tcbOf y _ (hL.tcb y hy 3328#u64 (by simp) (by simp))
  have m_aff : ∀ y ∈ T, m (fld y oAFFINITY) = L.mem s (affA y) := fun y hy =>
    (hE.mem _ (hUO.tcb y (heap y hy) oAFFINITY (Or.inl rfl)).1 (hUO.tcb y (heap y hy) oAFFINITY (Or.inl rfl)).2).symm
  have es : ∀ y, stA y = fld y oSTATE := fun y => by rw [stA_eq]; rfl
  have eB : ∀ y, blockA y = fld y oBLOCK_OBJ := fun y => by rw [blockA_eq]; rfl
  obtain ⟨mx, now, i2, tip, x, s1', s2, s3, a1', a2, a3, emx, hle, ei1, etip, eb, eok, eq, eu, enow, erel, ei2,
    eb4, edue, efo, ecb, ehi⟩ := fire_eqs ar hA hq h
  obtain ⟨hPE, hPR⟩ := plan_pe_pr hI etip eb
  obtain ⟨hTM0, hpN⟩ := plan_ntfn etip eb efo
  have hTMs := tmin_facts (BXI.blk hI) h0.cur hTM0
  have hB0 : L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) ≠ 0#u64 := fun e =>
    hW (Or.inl e)
  have hNN : L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) ∈ Nt :=
    hX.2.2.bnd _ hTMs.1 hB0
  have pn0 : pl.ntfn ≠ 0#u64 := by rw [hpN]; exact hB0
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
  have hSW : StW st gS T (lk s) s := fun X y v hy haff hq0 hv => gd_write (by
    show StWrOK st K m (L.cpu s) (lk s) X (stA y) v
    unfold StWrOK
    rw [es]
    exact stepOK_state hK hUO (heap _ hy.1) haff (by rw [m_aff _ hy.1]; exact hy.2)
      (fun hq => by rw [← eB]; exact hq0 (by rw [es]; exact hq)) (fun hq => absurd hq hv))
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
      exact fire_tail_wk2 (gS := gS) (R := fun _ => True) (W := WAll (StWrOK st K m (L.cpu s) (lk s)))
        (Lk := lk s) (U := U) ar hA hI hNt hok (fun _ _ _ => trivial)
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
        hW hAff (fun _ _ _ _ _ _ _ _ => trivial)
        (fun y hy k h1 h2 h3 hga ht _ n1 n2 x v => stepOK_nondec hK hUO (field_aligned (hT y hy.1) h2 h3)
          (locw_nondec hK hT hL hy.1 h1 h2 hga ht n1 n2))
        (fun _ _ _ _ _ _ => trivial)
        (fun q hq _ b ha hb h16 x v => stepOK_nondec hK hUO ha (scw_nondec hK hL hq hb h16))
        (fun y hy hqs hlk k hk => ⟨trivial, fun x v => stepOK_nondec hK hUO
          (field_aligned (hT y hy) (K := k) (by omega) (by omega))
          (lkw_nondec hK hI hL (Lk := lk s) (Or.inl ⟨y, hy, hqs, hlk, k, hk, rfl⟩))⟩)
        trivial hSW ((hPL s).1 pn0) (hPL s).2.1
        (fun k h1 h2 h3 x v => by
          obtain ⟨p1, p2⟩ := hO.ntP _ hNN
          rw [hpN]
          refine stepOK_nondec hK hUO (by unfold Aligned; rw [ntfn_word_val p1 p2 h1]; omega)
            (nondec_of_region hK (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hY.ntw _ hNN k h1, ?_⟩))))))
          rw [ntfn_word_val p1 p2 h1]; omega)
        (fun hep k h1 h2 => by
          obtain ⟨hH, hal⟩ := hPE hep
          exact ⟨trivial, fun x v => stepOK_nondec hK hUO (hal k h1 h2)
            (lkw_nondec hK hI hL (Lk := lk s) (Or.inr ⟨pl.ep, (hPL s).2.1 hep, hOL.1 _ hH k h1⟩))⟩)
        (fun hr x v => by
          obtain ⟨hR, hal⟩ := hPR hr
          exact stepOK_nondec hK hUO hal (lkw_nondec hK hI hL (Lk := lk s) (w := rTcbA pl.reply)
            (Or.inr ⟨pl.reply, (hPL s).2.2 hr, by unfold rTcbA; exact hOL.2 _ hR _ (by simp [layout.reply.TCB])⟩)))
        etip eb eq eok eu enow erel ei2 eb4 edue efo' ecb' emx hle ei1 ehi' (hBA _ _ _ _ _ _ _ eu ecb' ehi') hE.asid
        (fun _ _ => ⟨trivial, trivial⟩) trivial (fun _ _ => ⟨trivial, fun _ _ _ => trivial⟩)
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

end move

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {irq : U64} {m : U64 → U64}
variable {A : Type} (ar : machine.Arch A) {pl : localtimer.TimerIrqPlan}
variable {lk : S → U64 → Prop} {p : PathObl.SProg Bool}

/-- **The timer interrupt is a local path, the whole waking fire case proved** (module docstring). -/
noncomputable def irq_localPathP2 (hA : P0.ArchTotal ar) (hK : RegionOK K) (hUO : E2E.UserOK K)
    (hp : IsProg (irqBody S irq pl) p) (hz : NoZero p) (hm : E2E.MasksWr st)
    (hro : E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user)
      (IrqEntM K st T Cs Ω H Sg Rp Scs Nt Z Ac irq m) (MaxR K st lk))
    (hEU : ∀ s b v, IrqEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac irq s → b ∈ K.user → Aligned b →
      IrqEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac irq (L.wr s b v))
    (hlk : ∀ s b v, b ∈ K.user → lk (L.wr s b v) = lk s)
    (hPL : PlanLk lk pl) (hOL : ObjLay K H Rp)
    (hBA : ∀ s a, IrqEntM K st T Cs Ω H Sg Rp Scs Nt Z Ac irq m s → IrqFire st ar s a → ¬ NoWake st s →
      ∃ U : Set U64, ∀ s2 a2 s3 a3, interrupt.handle_interrupt st ar s2 a2 irq = ok (s3, a3) →
        BufAt st T Cs H Sg Scs Z U s3)
    (hSL : ∀ s, IrqEntM K st T Cs Ω H Sg Rp Scs Nt Z Ac irq m s → SlotLay K st T s) :
    E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) :=
  irq_localPathW ar hA hK hUO hp hz hm hro hEU hlk
    (fun s a s1 a1 hE hf hw h => by
      obtain ⟨U, hU⟩ := hBA s a hE hf hw
      exact irq_acc_fire_wk2 ar hA hK hE.k hE.ent.ly hE.ent.aff hE.ent.nth hOL hPL
        (fun _ _ _ _ _ _ _ _ _ e => hU _ _ _ _ e) (hSL s hE).v hf hw h)
    (fun s a s1 a1 hE hf hw h => by
      obtain ⟨U, hU⟩ := hBA s a hE hf hw
      exact irq_move_fire_wk2 ar hA hK hUO hp hE.k hE.ent.ly hE.ent.aff hE.ent.nth hOL hPL
        (fun _ _ _ _ _ _ _ _ _ e => hU _ _ _ _ e) hf hw h)

end

end Fl4Proofs.P2
