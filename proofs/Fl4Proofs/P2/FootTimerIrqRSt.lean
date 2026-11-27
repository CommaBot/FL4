/-
# P2: the round-robin case's walk: the `schedule` state

`sq_dt`: an accepted `sched_quiet` saw domain time left.

`rr_s3`: from the state `s1` after `update_timestamp` (P1 invariant `BXI`, `round_robin_ok` accepted, budget
insufficient, nothing due), through `check_budget` (`rr_cb_state`) and the timer handler (`REPROGRAM`, `ARMED`:
`handle_interrupt_timer`; the IRQ's state word is a kernel-global word outside the current SC, so the round-robin
writes keep it), the `schedule` state `s3` has: writes only `RrWT`, the action `CHOOSE_NEW`, the current thread
schedulable, queued, alone in the highest ready queue, the current SC's ring well formed, no timer due
(`rr_nodue`) and no release due (`rr_rel`).

No named premises.
-/
import Fl4Proofs.P2.FootTimerIrqRD
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

section law
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- **An accepted `sched_quiet` saw domain time left.** -/
theorem sq_dt {X : S} {c : U64} (h : localtimer.sched_quiet st X c = ok true) :
    L.mem X (core.num.U64.wrapping_add (L.ksb X) layout.ks.DOMAIN_TIME) ≠ 0#u64 := by
  unfold localtimer.sched_quiet at h
  rw [eq_of_spec_fd (sched.action.spec (L := L) X)] at h
  simp only [bind_ok] at h
  by_cases ha : L.actionW X = sched.ACTION_RESUME_CURRENT
  · rw [if_pos ha, domain_time_eq] at h
    simp only [bind_ok] at h
    intro h0
    rw [h0] at h
    simp at h
  · rw [if_neg ha] at h
    simp at h

end law

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}

set_option maxHeartbeats 4000000 in
/-- **The `schedule` state of the round-robin case** (module docstring). -/
theorem rr_s3 {A : Type} (ar : machine.Arch A) {s1 s2 s3 : S} {a1 a2 a3 : A} {x : Bool} {irq mx now : U64}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s1)
    (hrr : localtimer.round_robin_ok st ar s1 a1 (L.cpu s1) (L.curW s1) (L.cscW s1) (L.curTime s1) = ok true)
    (haff : L.mem s1 (affA (L.curW s1)) = L.cpu s1) (hsct : L.mem s1 (scA (L.curW s1)) = L.cscW s1)
    (hAc : L.cscW s1 ∈ Ac) (hact : L.actionW s1 = sched.ACTION_RESUME_CURRENT)
    (hins : ∀ c, sched.consumed st s1 = ok c → sporadic.sufficient st ar s1 a1 (L.cscW s1) c = ok false)
    (ecb : sched.check_budget st ar s1 a1 = ok (x, s2, a2))
    (hnow : L.curTime s1 = now)
    (erel : localtimer.release_due st s1 (L.cpu s1) = ok false)
    (edue : localtimer.timer_due st s1 (L.cpu s1) now = ok false)
    (emx : layout.irq.MAX = ok mx) (hle : ¬ irq > mx)
    (eis1 : interrupt.irq_state st s1 irq = ok interrupt.IRQ_TIMER)
    (ehi : interrupt.handle_interrupt st ar s2 a2 irq = ok (s3, a3)) :
    a2 = a1 ∧ WritesIn st s1 s3 (RrWT st T s1 (L.curW s1) (L.cscW s1) (Z (L.cscW s1))) ∧
      L.actionW s3 = sched.ACTION_CHOOSE_NEW ∧ sched.is_schedulable st s3 (L.curW s1) = ok true ∧
      (L.mem s3 (inqA (L.curW s1)) &&& sched.Q_QUEUED) ≠ 0#u64 ∧
      sched.highest_prio st s3 0#u64 = ok (L.mem s1 (prioA (L.curW s1))) ∧ L.l1W s3 (L.cpu s3) ≠ 0#u64 ∧
      L.mem s3 (L.nodeAt s1 (L.cpu s1) (rqOff (L.mem s1 (prioA (L.curW s1))))) = L.curW s1 ∧
      L.mem s3 (L.nodeAt s1 (L.cpu s1) (rqTailOff (L.mem s1 (prioA (L.curW s1))))) = L.curW s1 ∧
      RefillsWF st s3 (L.cscW s1) (Z (L.cscW s1)) ∧
      (L.mem s3 (L.nodeAt s3 (L.cpu s3) layout.node.TIMER_MIN) = 0#u64 ∨
        L.mem s3 (L.nodeAt s3 (L.cpu s3) layout.node.CUR_TIME) <
          L.mem s3 (tdA (L.mem s3 (L.nodeAt s3 (L.cpu s3) layout.node.TIMER_MIN)))) ∧
      RelNone st s3 ∧ interrupt.irq_state st s2 irq = ok interrupt.IRQ_TIMER ∧ L.ksb s2 = L.ksb s1 ∧
      L.cpu s2 = L.cpu s1 := by
  obtain ⟨Qq, Rq, h1⟩ := hI.1
  have hX1 := hI.2.2.1
  have hS1 := hI.2.2.2.2
  have hT : TcbPlaced T := h1.tcbs
  have hcC : L.cpu s1 ∈ Cs := h1.cur
  have hN1 : NodePlaced st T s1 (L.cpu s1) := h1.nodes _ hcC
  have hcT : L.curW s1 ∈ T := h1.curT
  have hcS : L.cscW s1 ∈ Scs := hX1.2.2.cur
  obtain ⟨-, -, -, -, -, htime, -, -⟩ := round_robin_ok_true hrr
  obtain ⟨ha2, w12, hact2, hsch2, hq2, hhp2, hl12, hH2, hE2, ⟨NE, hB2⟩, hWF2⟩ :=
    rr_cb_state ar hI hrr haff hsct hAc hact hins ecb
  -- the current SC's words
  obtain ⟨hP, hz⟩ := hX1.1.sc _ hcS
  obtain ⟨-, h128, -⟩ := sc_lo hP hz
  have hcv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
  have hcv' : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
  have inΩ : ∀ b, Aligned b → (InRing (L.cscW s1) (Z (L.cscW s1)) b ∨
      b = core.num.U64.wrapping_add (L.cscW s1) layout.sc.CONSUMED) → b ∈ Ω := by
    rintro b hb (hh | rfl)
    · exact hX1.1.scW _ hcS b hb hh.inSC
    · exact hX1.1.scW _ hcS _ hb ⟨by rw [hcv]; omega, by rw [hcv, hcv']; omega⟩
  have hmΩ : maxA (L.cscW s1) ∈ Ω := hS1.sub _ (hS1.all _ hcS).2.1
  obtain ⟨-, kT2, kΩ2⟩ := rrw_keep h1 hcT inΩ w12
  -- the IRQ's state word at `s2`
  have hirq : irq.val ≤ 127 := by
    rw [eq_of_spec_fd layout.irq.MAX.spec] at emx
    have e := ok_inj_ff emx
    subst e
    scalar_tac
  obtain ⟨i, hi, hiv⟩ : ∃ i, interrupt.state_off irq = ok i ∧ i.val = 224 + 8 * irq.val := by
    unfold interrupt.state_off
    simp only [lift, bind_ok]
    rw [eq_of_spec_fd layout.ks.IRQ_STATE.spec]
    simp only [bind_ok]
    refine ⟨_, rfl, ?_⟩
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits,
      UScalar.size]
    try omega
  have hi' : i.val < 13568 := by omega
  have hi8 : i.val % 8 = 0 := by omega
  have hiS : ¬ InSC (L.cscW s1) (Z (L.cscW s1)) (core.num.U64.wrapping_add (L.ksb s1) i) := fun hin => by
    have hsg := (hS1.all _ hcS).2.2 _ (ks_aligned hN1 hi' hi8) hin
    have := hS1.ks _ hsg
    rw [ks_word_val hN1 hi'] at this
    omega
  have eis2 : interrupt.irq_state st s2 irq = ok interrupt.IRQ_TIMER := by
    rw [← eis1]
    unfold interrupt.irq_state
    rw [hi]
    simp only [bind_ok]
    rw [eq_of_spec_fd (obj.ks_get.spec (L := L) s2 i), eq_of_spec_fd (obj.ks_get.spec (L := L) s1 i), w12.1,
      kΩ2 _ (hS1.ksΩ i hi' hi8) (fun hr => hiS hr.inSC)
        (fun e => hiS (by rw [e]; exact ⟨by rw [hcv]; omega, by rw [hcv, hcv']; omega⟩))]
  -- the timer handler
  obtain ⟨s2', eh2, eh3, -⟩ := handle_interrupt_timer ar emx hle eis2 ehi
  have k2 : L.ksb s2 = L.ksb s1 := w12.1
  have c2 : L.cpu s2 = L.cpu s1 := w12.2.1
  have hN2 : NodePlaced st T s2 (L.cpu s2) := by rw [c2]; exact hN1.ksb k2
  have hcC2 : L.cpu s2 ∈ Cs := by rw [c2]; exact hcC
  have w23 : WritesIn st s2 s3 (HW st s2) := handle_interrupt_timer_writes hN2 eh2 eh3
  have w13 : WritesIn st s1 s3 (RrWT st T s1 (L.curW s1) (L.cscW s1) (Z (L.cscW s1))) :=
    w12.trans1 (w23.mono fun b hb => by
      obtain ⟨o, ho, ho1, ho2, e⟩ := hb
      have ho' : o.val = 56 ∨ o.val = 80 := ho
      exact Or.inr (Or.inr (Or.inl ⟨o, by
        show o.val = 16 ∨ o.val = 40 ∨ o.val = 56 ∨ o.val = 80 ∨ 120 ≤ o.val
        omega, ho1, ho2, by rw [e, c2, nodeAt_of_ksb k2]⟩)))
  have e2N : ∀ o, L.nodeAt s2 (L.cpu s2) o = L.nodeAt s1 (L.cpu s1) o := fun o => by rw [c2, nodeAt_of_ksb k2]
  have hn23 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 56 ∧ o.val ≠ 80 →
      L.mem s3 (L.nodeAt s1 (L.cpu s1) o) = L.mem s2 (L.nodeAt s1 (L.cpu s1) o) := fun o ho h8 hn => by
    rw [← e2N]; exact hw_node hN2 w23 ho h8 hn
  have ht23 : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem s3 (core.num.U64.wrapping_add y K) = L.mem s2 (core.num.U64.wrapping_add y K) :=
    fun y hy K hK h8 => hw_tcb hT hN2 w23 hy hK h8
  have hsc2 : L.mem s2 (scA (L.curW s1)) = L.cscW s1 := by
    rw [scA_eq, kT2 _ hcT 3464#u64 (by simp) (by simp) (by simp) (by simp) (by simp), ← scA_eq]; exact hsct
  have hsch3 : sched.is_schedulable st s3 (L.curW s1) = ok true := by
    rw [← hsch2]
    refine is_schedulable_congr ?_ ?_ ?_ ?_
    · rw [stA_eq, ht23 _ hcT 3328#u64 (by simp) (by simp)]
    · rw [scA_eq, ht23 _ hcT 3464#u64 (by simp) (by simp)]
    · intro _
      rw [hsc2]
      unfold LawfulStore.rmax
      exact hw_outside hN2 hcC2 w23 ((h1.omega _ hmΩ).ksb k2)
    · rw [inqA_eq, ht23 _ hcT 3592#u64 (by simp) (by simp)]
  have hl1' : L.l1W s3 (L.cpu s2) = L.l1W s2 (L.cpu s2) := by
    unfold LawfulStore.l1W
    rw [nodeAt_of_ksb w23.1]
    exact hw_node hN2 w23 (by rw [l1Off_val]; omega) (by rw [l1Off_val]) (by rw [l1Off_val]; omega)
  have hl2' : ∀ g < 4, L.l2W s3 (L.cpu s2) g = L.l2W s2 (L.cpu s2) g := fun g hg => by
    unfold LawfulStore.l2W
    rw [nodeAt_of_ksb w23.1]
    exact hw_node hN2 w23 (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega)
  have hp1 : (L.mem s1 (prioA (L.curW s1))).val < 256 := h1.prio _ hcT
  obtain ⟨kN, -, -⟩ := rrw_keep h1 hcT inΩ w13
  -- no timer due, no release due
  have nd3 : NoDueT st s3 now :=
    rr_nodue h1 hcT inΩ ((TInv.tm (BXI.blk hI)).min _ hcC) w13 (td_false edue)
  have hct3 : L.mem s3 (L.nodeAt s3 (L.cpu s3) layout.node.CUR_TIME) = now := by
    rw [w13.2.1, nodeAt_of_ksb w13.1,
      kN _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
        (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])]
    exact hnow
  refine ⟨ha2, w13, by rw [action_hw hN2 w23]; exact hact2, hsch3, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    rr_rel hI hcT htime w13 (rel_false erel), eis2, k2, c2⟩
  · rw [inqA_eq, ht23 _ hcT 3592#u64 (by simp) (by simp), ← inqA_eq]; exact hq2
  · rw [highest_prio_agree (Z := s3) _ hN2 (by rw [c2]; exact hB2) (by rw [c2]; exact hl12) w23.1 w23.2.1 hl1' hl2']
    exact hhp2
  · rw [w23.2.1, hl1', c2]; exact hl12
  · rw [hn23 (rqOff (L.mem s1 (prioA (L.curW s1)))) (by rw [rqOff_val hp1]; omega) (by rw [rqOff_val hp1]; omega)
      ⟨by rw [rqOff_val hp1]; omega, by rw [rqOff_val hp1]; omega⟩]
    exact hH2
  · rw [hn23 (rqTailOff (L.mem s1 (prioA (L.curW s1)))) (by rw [rqTailOff_val hp1]; omega)
      (by rw [rqTailOff_val hp1]; omega) ⟨by rw [rqTailOff_val hp1]; omega, by rw [rqTailOff_val hp1]; omega⟩]
    exact hE2
  · exact hWF2.agree fun b hb hin => hw_outside hN2 hcC2 w23 ((h1.omega b (hX1.1.scW _ hcS b hb hin)).ksb k2)
  · rw [hct3]; exact nd3

end main

end Fl4Proofs.P2
