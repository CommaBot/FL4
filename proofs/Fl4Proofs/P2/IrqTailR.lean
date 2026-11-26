/-
# P2 (line p3mc, gen 22): the timer interrupt's tail replayed and declined on a generic guarded store

Handoff §26c items 1–2. The tail `irqTailF` (P2/IrqTailE.lean, the extracted body after the plan check) as a run on
another store:

* `irq_splitF`: the extracted `handle_timer_irq_local` is its head followed by `irqTailF` (`unfold; rfl`);
  `irqTailS_run`: a run of `irqTailF` is the run of the tree `irqTailS` (`irqTailS_eq`).
* `fire_ok_tm0`: `fire_ok` with an empty plan (`p.tm = 0`) is `ok false` on every store, reading nothing.
* `irqTail_accept_walk` / `irqTail_replay`: `irq_accept_walk` / `irq_replay` for the tail (from `cur_thread` on).
* **`irqTail_accT`**: an accepted tail run with `p.tm = 0` (so quiet or round-robin) is the same run on any store
  answering the gen-21 cores' reads (`IrqRdT`, no word of the plan's thread but its deadline) and writes (`IrqWr`):
  `irq_accT_quiet_core` / `irq_accT_rr_core`, then `irqTail_replay` (the final `vcpu::check` by
  `vcpu.check.guard_nvm`).
* **`irqTail_decT`**: a declined tail run with `p.tm = 0` is the same run on any store answering `current_ok` (given
  as an equation, `current_ok.guardC` builds it), the current core's node words, the `IrqRdT` reads once `current_ok`
  passed, `CUR_DOMAIN` / `DOMAIN_TIME`, and the two clock writes (`IrqDec`): `irq_dec_guard`'s walk over a generic
  read set (as `set_timer_dec_guardS` for st, gen 19); the fire branch is `fire_ok_tm0`.
* **`irqTail_guardT`**: both together: every tail run on `st` with `p.tm = 0` is the run on such a store.

No named premises beyond the cores' own (`hAs`, P1's `AsidOff`, an argument); no existing statement changed.
-/
import Fl4Proofs.P2.IrqTailE
import Fl4Proofs.P2.IrqTailT
import Fl4Proofs.P2.FootTimerIrqDec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (irqTailF irqTailS irqTailS_eq tr_bind tr_bind_same tr_ite ScAcc)

section split
variable {S : Type} {A : Type} (st : machine.Store S) (ar : machine.Arch A)

/-- **The extracted timer interrupt is its head, then `irqTailF`** (module docstring). -/
theorem irq_splitF (s : S) (a : A) (irq : U64) (p : localtimer.TimerIrqPlan) :
    localtimer.handle_timer_irq_local st ar s a irq p = (do
      let cpu ← st.cur_cpu s
      if layout.NUM_DOMAINS != 1#u64 then ok (false, s, a)
      else
        let i ← layout.irq.MAX
        if irq > i then ok (false, s, a)
        else
          let i1 ← interrupt.irq_state st s irq
          if i1 != interrupt.IRQ_TIMER then ok (false, s, a)
          else
            let tip ← localtimer.plan_objects st s
            let b ← localtimer.same_plan tip p
            if b then irqTailF st ar s a irq cpu p else ok (false, s, a)) := by
  unfold localtimer.handle_timer_irq_local irqTailF
  rfl

/-- A run of the tail function is the run of the tail tree. -/
theorem irqTailS_run {s : S} {a : A} {irq cpu : U64} {p : localtimer.TimerIrqPlan} {r : Bool × S × A}
    (h : irqTailF st ar s a irq cpu p = ok r) : PathObl.interp st ar (irqTailS irq cpu p) s a = ok r := by
  rw [irqTailS_eq, h]
  simp only [bind_ok, bind_tc_ok]

/-- **`fire_ok` with an empty plan** declines at once, on every store. -/
theorem fire_ok_tm0 (s : S) (cpu ct : U64) {p : localtimer.TimerIrqPlan} (now : U64) (h : p.tm = 0#u64) :
    localtimer.fire_ok st s cpu ct p now = ok false := by
  unfold localtimer.fire_ok
  rw [if_pos h]

end split

section walk
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **An accepted tail, step by step** (`irq_accept_walk` from `cur_thread` on). -/
theorem irqTail_accept_walk {s s' : S} {a a' : A} {irq cpu : U64} {p : localtimer.TimerIrqPlan}
    (h : irqTailF st ar s a irq cpu p = ok (true, s', a')) :
    ∃ (ct csc now i2 : U64) (b4 due x : Bool) (s1 s2 s3 s4 s5 : S) (a1 a2 a3 a4 a5 : A) (t : U64),
      sched.cur_thread st s = ok ct ∧ sched.cur_sc st s = ok csc ∧
      localtimer.current_ok st s cpu ct csc = ok true ∧ localtimer.sched_quiet st s cpu = ok true ∧
      sched.update_timestamp st ar s a = ok (s1, a1) ∧ sched.cur_time st s1 = ok now ∧
      localtimer.release_due st s1 cpu = ok false ∧ sched.consumed st s1 = ok i2 ∧
      sporadic.sufficient st ar s1 a1 csc i2 = ok b4 ∧ localtimer.timer_due st s1 cpu now = ok due ∧
      IrqCase st ar s1 a1 cpu ct csc p now b4 due ∧
      sched.check_budget st ar s1 a1 = ok (x, s2, a2) ∧
      interrupt.handle_interrupt st ar s2 a2 irq = ok (s3, a3) ∧
      sched.schedule st ar s3 a3 = ok (s4, a4) ∧ sched.activate_thread st ar s4 a4 = ok (s5, a5) ∧
      sched.cur_thread st s5 = ok t ∧ vcpu.check st ar s5 a5 t = ok (s', a') := by
  unfold irqTailF at h
  obtain ⟨ct, ect, h⟩ := bind_eq_ok h
  obtain ⟨csc, ecsc, h⟩ := bind_eq_ok h
  obtain ⟨b1, eb1, h⟩ := bind_eq_ok h
  cases b1
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨b2, eb2, h⟩ := bind_eq_ok h
  cases b2
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨⟨s1, a1⟩, eu, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨now, enow, h⟩ := bind_eq_ok h
  obtain ⟨b3, eb3, h⟩ := bind_eq_ok h
  cases b3
  swap
  · simp at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨i2, ei2, h⟩ := bind_eq_ok h
  obtain ⟨b4, eb4, h⟩ := bind_eq_ok h
  obtain ⟨due, edue, h⟩ := bind_eq_ok h
  obtain ⟨ok1, eok1, h⟩ := bind_eq_ok h
  cases ok1
  · simp at h
  simp only [↓reduceIte] at h
  have hc : IrqCase st ar s1 a1 cpu ct csc p now b4 due := by
    cases b4 <;> cases due <;> simp at eok1
    · exact .rr rfl rfl eok1
    · exact .quiet rfl rfl
    · exact .fire rfl rfl eok1
  obtain ⟨⟨x, s2, a2⟩, ecb, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  try dsimp only at h
  obtain ⟨⟨s3, a3⟩, ehi, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨⟨s4, a4⟩, esc, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨⟨s5, a5⟩, eac, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨t, et, h⟩ := bind_eq_ok h
  obtain ⟨⟨s6, a6⟩, evc, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  have e := ok_inj_ff h
  simp only [Prod.mk.injEq, true_and] at e
  obtain ⟨rfl, rfl⟩ := e
  exact ⟨ct, csc, now, i2, b4, due, x, s1, s2, s3, s4, s5, a1, a2, a3, a4, a5, t, ect, ecsc, eb1, eb2, eu, enow,
    eb3, ei2, eb4, edue, hc, ecb, ehi, esc, eac, et, evc⟩

set_option maxHeartbeats 4000000 in
/-- **Replaying an accepted tail** on another store answering its calls (`irq_replay` without the head). -/
theorem irqTail_replay {st' : machine.Store S} {s s' : S} {a a' : A} {irq cpu : U64} {p : localtimer.TimerIrqPlan}
    {ct csc now i2 : U64} {b4 due x : Bool}
    {s1 s2 s3 s4 s5 : S} {a1 a2 a3 a4 a5 : A} {t : U64}
    (ect : sched.cur_thread st s = ok ct) (gct : sched.cur_thread st' s = sched.cur_thread st s)
    (ecsc : sched.cur_sc st s = ok csc) (gcsc : sched.cur_sc st' s = sched.cur_sc st s)
    (eb1 : localtimer.current_ok st s cpu ct csc = ok true)
    (gb1 : localtimer.current_ok st' s cpu ct csc = localtimer.current_ok st s cpu ct csc)
    (eb2 : localtimer.sched_quiet st s cpu = ok true)
    (gb2 : localtimer.sched_quiet st' s cpu = localtimer.sched_quiet st s cpu)
    (eu : sched.update_timestamp st ar s a = ok (s1, a1))
    (gu : sched.update_timestamp st' ar s a = sched.update_timestamp st ar s a)
    (enow : sched.cur_time st s1 = ok now) (gnow : sched.cur_time st' s1 = sched.cur_time st s1)
    (eb3 : localtimer.release_due st s1 cpu = ok false)
    (gb3 : localtimer.release_due st' s1 cpu = localtimer.release_due st s1 cpu)
    (ei2 : sched.consumed st s1 = ok i2) (gi2 : sched.consumed st' s1 = sched.consumed st s1)
    (eb4 : sporadic.sufficient st ar s1 a1 csc i2 = ok b4)
    (gb4 : sporadic.sufficient st' ar s1 a1 csc i2 = sporadic.sufficient st ar s1 a1 csc i2)
    (edue : localtimer.timer_due st s1 cpu now = ok due)
    (gdue : localtimer.timer_due st' s1 cpu now = localtimer.timer_due st s1 cpu now)
    (hc : IrqCase st ar s1 a1 cpu ct csc p now b4 due)
    (grr : b4 = false → localtimer.round_robin_ok st' ar s1 a1 cpu ct csc now =
      localtimer.round_robin_ok st ar s1 a1 cpu ct csc now)
    (gfire : due = true → localtimer.fire_ok st' s1 cpu ct p now = localtimer.fire_ok st s1 cpu ct p now)
    (ecb : sched.check_budget st ar s1 a1 = ok (x, s2, a2))
    (gcb : sched.check_budget st' ar s1 a1 = sched.check_budget st ar s1 a1)
    (ehi : interrupt.handle_interrupt st ar s2 a2 irq = ok (s3, a3))
    (ghi : interrupt.handle_interrupt st' ar s2 a2 irq = interrupt.handle_interrupt st ar s2 a2 irq)
    (esc : sched.schedule st ar s3 a3 = ok (s4, a4))
    (gsc : sched.schedule st' ar s3 a3 = sched.schedule st ar s3 a3)
    (eac : sched.activate_thread st ar s4 a4 = ok (s5, a5))
    (gac : sched.activate_thread st' ar s4 a4 = sched.activate_thread st ar s4 a4)
    (et : sched.cur_thread st s5 = ok t) (gt : sched.cur_thread st' s5 = sched.cur_thread st s5)
    (evc : vcpu.check st ar s5 a5 t = ok (s', a'))
    (gvc : vcpu.check st' ar s5 a5 t = vcpu.check st ar s5 a5 t) :
    irqTailF st' ar s a irq cpu p = ok (true, s', a') := by
  unfold irqTailF
  rw [gct, ect]
  simp only [bind_ok]
  rw [gcsc, ecsc]
  simp only [bind_ok]
  rw [gb1, eb1]
  simp only [bind_ok, ↓reduceIte]
  rw [gb2, eb2]
  simp only [bind_ok, ↓reduceIte]
  rw [gu, eu]
  simp only [bind_ok, uncurry_apply_pair]
  rw [gnow, enow]
  simp only [bind_ok]
  rw [gb3, eb3]
  simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
  rw [gi2, ei2]
  simp only [bind_ok]
  rw [gb4, eb4]
  simp only [bind_ok]
  rw [gdue, edue]
  simp only [bind_ok]
  cases hc with
  | quiet h4 hd =>
    subst h4 hd
    simp only [Bool.false_eq_true, not_false_eq_true, not_true_eq_false, ↓reduceIte, bind_ok]
    rw [gcb, ecb]; simp only [bind_ok, uncurry_apply_pair]
    rw [ghi, ehi]; simp only [bind_ok, uncurry_apply_pair]
    rw [gsc, esc]; simp only [bind_ok, uncurry_apply_pair]
    rw [gac, eac]; simp only [bind_ok, uncurry_apply_pair]
    rw [gt, et]; simp only [bind_ok]
    rw [gvc, evc]; simp only [bind_ok, uncurry_apply_pair]
  | fire h4 hd hf =>
    subst h4 hd
    simp only [Bool.false_eq_true, not_false_eq_true, not_true_eq_false, ↓reduceIte, bind_ok]
    rw [gfire rfl, hf]
    simp only [bind_ok, ↓reduceIte]
    rw [gcb, ecb]; simp only [bind_ok, uncurry_apply_pair]
    rw [ghi, ehi]; simp only [bind_ok, uncurry_apply_pair]
    rw [gsc, esc]; simp only [bind_ok, uncurry_apply_pair]
    rw [gac, eac]; simp only [bind_ok, uncurry_apply_pair]
    rw [gt, et]; simp only [bind_ok]
    rw [gvc, evc]; simp only [bind_ok, uncurry_apply_pair]
  | rr h4 hd hr =>
    subst h4 hd
    simp only [Bool.false_eq_true, not_false_eq_true, not_true_eq_false, ↓reduceIte, bind_ok]
    rw [grr rfl, hr]
    simp only [bind_ok, ↓reduceIte]
    rw [gcb, ecb]; simp only [bind_ok, uncurry_apply_pair]
    rw [ghi, ehi]; simp only [bind_ok, uncurry_apply_pair]
    rw [gsc, esc]; simp only [bind_ok, uncurry_apply_pair]
    rw [gac, eac]; simp only [bind_ok, uncurry_apply_pair]
    rw [gt, et]; simp only [bind_ok]
    rw [gvc, evc]; simp only [bind_ok, uncurry_apply_pair]

end walk

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 8000000 in
/-- **An accepted tail with an empty plan, on any store answering `IrqRdT` / `IrqWr`** (module docstring). -/
theorem irqTail_accT {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
    (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {irq mx : U64} {p : localtimer.TimerIrqPlan}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (gRd : IrqOk st s → ∀ w, Aligned w → IrqRdT st Z s w → R w)
    (gWr : IrqOk st s → ∀ w, Aligned w → IrqWr st Z s w → w ≠ stA (L.curW s) → W w)
    (hIq : IrqOk st s → ∀ i, interrupt.state_off irq = ok i → R (core.num.U64.wrapping_add (L.ksb s) i))
    (hD1 : IrqOk st s → R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hD2 : IrqOk st s → R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME))
    (hwS : IrqOk st s → L.mem s (stA (L.curW s)) = sched.TS_RESTART → ∀ X, L.mem X (stA (L.curW s)) = sched.TS_RESTART →
      L.mem X (affA (L.curW s)) = L.cpu s →
      gS.write X (stA (L.curW s)) sched.TS_RUNNING = st.write X (stA (L.curW s)) sched.TS_RUNNING)
    (hKr : IrqOk st s → R (krA (L := L) s)) (hTab : IrqOk st s → PathObl.RdTab (L := L) R s)
    (hAs : AsidOff (L := L) Ω Sg s)
    (emx : layout.irq.MAX = ok mx) (hle : ¬ irq > mx)
    (ei1 : interrupt.irq_state st s irq = ok interrupt.IRQ_TIMER) (hp0 : p.tm = 0#u64)
    (h : irqTailF st ar s a irq (L.cpu s) p = ok (true, s', a')) :
    irqTailF gS ar s a irq (L.cpu s) p = ok (true, s', a') := by
  obtain ⟨ct, csc, now, i2, b4, due, x, s1, s2, s3, s4, s5, a1, a2, a3, a4, a5, t, ect, ecsc, eok, eq, eu, enow,
    erel, ei2, eb4, edue, hc, ecb, ehi, esc, eac, et, evc⟩ := irqTail_accept_walk ar h
  have ecpu : st.cur_cpu s = ok (L.cpu s) := L.cur_cpu_eq s
  have ectr := ect
  have ecscr := ecsc
  rw [cur_thread_ok] at ect
  have etc : L.curW s = ct := ok_inj_ff ect
  subst etc
  rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) s)] at ecsc
  have ecs' : L.cscW s = csc := ok_inj_ff ecsc
  subst ecs'
  obtain ⟨hmr, hsct, hcore⟩ := current_ok_true eok
  obtain ⟨-, haff, hnvm, -⟩ := may_run_here_true hmr
  cases hc with
  | quiet h4 hd =>
    subst h4 hd
    have G := irq_accT_quiet_core ar hA hI gRd gWr hIq hD1 hD2 hwS ecpu emx hle ei1 ectr ecscr haff hsct
      hcore (mrh_yield hmr) eq eu enow erel ei2 eb4 edue ecb ehi esc eac et
    have et' := G.et
    subst et'
    have hst5 : L.mem s5 (stA (L.curW s)) ≠ sched.TS_RUNNING_VM := by
      rcases G.st5 with e | e
      · rw [e]; simp [sched.TS_RUNNING, sched.TS_RUNNING_VM]
      · rw [e]; exact hnvm
    exact irqTail_replay ar ectr G.gct ecscr G.gcsc eok G.gcok eq G.gb2 eu G.gu enow G.gnow erel G.gb3 ei2
      G.gi2 eb4 G.gb4 edue G.gdue (IrqCase.quiet rfl rfl) (fun h => nomatch h) (fun h => nomatch h) ecb G.gcb
      ehi G.ghi esc G.gsc eac G.gac et G.gt evc (vcpu.check.guard_nvm ar s5 a5 (L.curW s) G.rSt hst5)
  | fire h4 hd hf =>
    rw [fire_ok_tm0 st s1 _ _ now hp0] at hf
    exact absurd (ok_inj_ff hf) Bool.false_ne_true
  | rr h4 hd hr =>
    subst h4 hd
    have G := irq_accT_rr_core ar hA hI gRd gWr hIq hD1 hD2 hwS hKr hTab hAs ecpu emx hle ei1 ectr ecscr haff
      hsct hcore (mrh_yield hmr) eq eu enow erel ei2 eb4 edue hr ecb ehi esc eac et
    have et' := G.et
    subst et'
    have hst5 : L.mem s5 (stA (L.curW s)) ≠ sched.TS_RUNNING_VM := by
      rcases G.st5 with e | e
      · rw [e]; simp [sched.TS_RUNNING, sched.TS_RUNNING_VM]
      · rw [e]; exact hnvm
    exact irqTail_replay ar ectr G.gct ecscr G.gcsc eok G.gcok eq G.gb2 eu G.gu enow G.gnow erel G.gb3 ei2
      G.gi2 eb4 G.gb4 edue G.gdue (IrqCase.rr rfl rfl hr) (fun _ => G.grr rfl) (fun h => nomatch h) ecb G.gcb
      ehi G.ghi esc G.gsc eac G.gac et G.gt evc (vcpu.check.guard_nvm ar s5 a5 (L.curW s) G.rSt hst5)

set_option maxHeartbeats 32000000 in
/-- **A declined tail with an empty plan, on any store answering its reads** (module docstring). -/
theorem irqTail_decT {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
    (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {irq : U64} {p : localtimer.TimerIrqPlan}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (nR : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o))
    (gcok : localtimer.current_ok gS s (L.cpu s) (L.curW s) (L.cscW s) =
      localtimer.current_ok st s (L.cpu s) (L.curW s) (L.cscW s))
    (gRd : IrqOk st s → ∀ w, Aligned w → IrqRdT st Z s w → R w)
    (hD1 : IrqOk st s → R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hD2 : IrqOk st s → R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME))
    (hW1 : W (ctA (L := L) s)) (hW2 : W (cnA (L := L) s)) (hp0 : p.tm = 0#u64)
    (h : irqTailF st ar s a irq (L.cpu s) p = ok (false, s', a')) :
    irqTailF gS ar s a irq (L.cpu s) p = ok (false, s', a') := by
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  have hcC : L.cpu s ∈ Cs := h0.cur
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ hcC
  have hcT : L.curW s ∈ T := h0.curT
  have ht' := hT _ hcT
  have hX := hI.2.2.1
  have hO := hX.1
  have hS := hI.2.2.2.2
  have hcs : L.cscW s ∈ Scs := hX.2.2.cur
  have hcq : SCq st s Ω (L.cscW s) (Z (L.cscW s)) := scq_of hO hS hcs
  have hmaxΩ : maxA (L.cscW s) ∈ Ω := hcq.2.1 _ hcq.2.2.2.2 hcq.2.2.2.1
  -- the walk
  revert h
  unfold irqTailF
  rw [PathObl.sched.cur_thread.guard (gS := gS) s (nR _ (by rw [curth_val]; omega) (by rw [curth_val])),
    cur_thread_ok]
  simp only [bind_ok]
  rw [PathObl.sched.cur_sc.guard (gS := gS) s (nR _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))]
  refine tr_bind_same (fun csc ecsc => ?_)
  have ecsc' : L.cscW s = csc := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) s)] at ecsc; exact ok_inj_ff ecsc
  subst ecsc'
  rw [gcok]
  refine tr_bind_same (fun b1 eb1 => ?_)
  refine tr_ite (fun hb1 => ?_) (fun _ h => h)
  subst hb1
  -- past `current_ok`: every read is `IrqRdT`'s
  obtain ⟨hmr, hsct, hcore⟩ := current_ok_true eb1
  obtain ⟨-, haff, -, -⟩ := may_run_here_true hmr
  have hok : IrqOk st s := ⟨haff, hsct, hcore⟩
  have gRd' := gRd hok
  have rD1 := hD1 hok
  have rD2 := hD2 hok
  have cR : ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → (K.val < 3528 ∨ 3576 ≤ K.val) →
      K.val ≠ 3496 → K.val ≠ 3504 → R (core.num.U64.wrapping_add (L.curW s) K) := fun K h1 h2 h3 h4 h5 h6 =>
    gRd' _ (field_aligned ht' h2 h3) (Or.inr (Or.inl ⟨K, h1, h2, h3, h4, h5, h6, rfl⟩))
  have scR : ∀ b, InSC (L.cscW s) (Z (L.cscW s)) b → Aligned b → R b := fun b hb ha =>
    gRd' _ ha (Or.inr (Or.inr (Or.inl hb)))
  have hSc : ScAcc R (fun _ => True) (L.cscW s) (Z (L.cscW s)) :=
    ⟨fun b ha hb => scR b hb ha, fun _ _ _ => trivial, trivial⟩
  have rSt : R (stA (L.curW s)) := by rw [stA_eq]; exact cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rSc : R (scA (L.curW s)) := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rIq : R (inqA (L.curW s)) := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rMx : R (maxA (L.cscW s)) := scR _ hcq.2.2.2.1 hcq.2.2.2.2
  rw [sched_quiet.guard (gS := gS) s (nR _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))
    rD2 (nR _ (by simp [layout.node.IPI_PENDING]) (by simp [layout.node.IPI_PENDING]))]
  refine tr_bind_same (fun b2 eb2 => ?_)
  refine tr_ite (fun hb2 => ?_) (fun _ h => h)
  subst hb2
  have hact0 : L.actionW s = sched.ACTION_RESUME_CURRENT := sq_true eb2
  have hsc0 : L.mem s (scA (L.curW s)) ≠ 0#u64 := hI.2.1.resume (hact0.trans resume_val)
  have hAc : L.cscW s ∈ Ac := by
    rw [← hsct]
    exact hI.2.1.sact _ hcT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hact0.trans resume_val, rfl⟩))))) hsc0
  have hmx0 : L.rmax s (L.cscW s) ≠ 0#u64 := (hS.act _ hcs).1 hAc
  rw [PathObl.sched.update_timestamp.guard (gS := gS) ar s a
    (nR _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])) hW1
    (nR _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])) hW2]
  refine tr_bind_same (fun q eu => ?_)
  obtain ⟨s1, a1⟩ := q
  simp only [uncurry_apply_pair]
  -- `s → s1`: the timestamp update
  obtain ⟨n1, -, er⟩ := ut_now ar hA hN eu
  simp only at er
  have k1 : L.ksb s1 = L.ksb s := by rw [er, utW_ksb]
  have c1 : L.cpu s1 = L.cpu s := by rw [er, utW_cpu]
  have m1 : ∀ b, Aligned b → b ≠ ctA (L := L) s → b ≠ cnA (L := L) s → L.mem s1 b = L.mem s b :=
    fun b hb h1 h2 => by rw [er]; exact utW_mem hN n1 hb h1 h2
  have e1N : ∀ o, L.nodeAt s1 (L.cpu s1) o = L.nodeAt s (L.cpu s) o := fun o => by rw [c1, nodeAt_of_ksb k1]
  have hnode1 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 40 → o.val ≠ 48 →
      L.mem s1 (L.nodeAt s (L.cpu s) o) = L.mem s (L.nodeAt s (L.cpu s) o) := by
    intro o ho h8 h40 h48
    refine m1 _ (nodeAt_aligned hN ho h8) (fun e => ?_) (fun e => ?_)
    · have e' := congrArg UScalar.val e
      unfold ctA at e'
      rw [nodeAt_val hN ho, nodeAt_val hN (by simp [layout.node.CUR_TIME])] at e'
      simp [layout.node.CUR_TIME] at e'; omega
    · have e' := congrArg UScalar.val e
      unfold cnA at e'
      rw [nodeAt_val hN ho, nodeAt_val hN (by simp [layout.node.CONSUMED])] at e'
      simp [layout.node.CONSUMED] at e'; omega
  have htcb1 : ∀ {y K : U64}, y ∈ T → K.val < 4096 → K.val % 8 = 0 →
      L.mem s1 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
    intro y K hy hK h8
    exact m1 _ (field_aligned (hT y hy) hK h8) (tcb_node_ne hN hy (hT y hy) hK (by simp [layout.node.CUR_TIME]))
      (tcb_node_ne hN hy (hT y hy) hK (by simp [layout.node.CONSUMED]))
  have hout1 : ∀ b, OutsideObjs st T Cs s b → L.mem s1 b = L.mem s b := fun b hb =>
    m1 b hb.1 (fun e => out_ne_node hb hcC hN (by simp [layout.node.CUR_TIME]) (congrArg UScalar.val e).symm)
      (fun e => out_ne_node hb hcC hN (by simp [layout.node.CONSUMED]) (congrArg UScalar.val e).symm)
  have agΩ1 : ∀ b ∈ Ω, L.mem s1 b = L.mem s b := fun b hb => hout1 b (h0.omega b hb)
  have ndR : ∀ (Y : S), (∀ o, L.nodeAt Y (L.cpu Y) o = L.nodeAt s (L.cpu s) o) → ∀ o : U64, o.val < 4288 →
      o.val % 8 = 0 → R (L.nodeAt Y (L.cpu Y) o) := fun Y e o h1 h2 => by rw [e]; exact nR o h1 h2
  have scK1 : ∀ y ∈ T, L.mem s1 (scA y) = L.mem s (scA y) := fun y hy => by
    rw [scA_eq]; exact htcb1 hy (by simp) (by simp)
  have wf1 : RefillsWF st s1 (L.cscW s) (Z (L.cscW s)) :=
    (SCq.agree hcq agΩ1).1 (by unfold LawfulStore.rmax; rw [agΩ1 _ hmaxΩ]; exact hmx0)
  rw [PathObl.sched.cur_time.guard (gS := gS) s1
    (ndR s1 e1N _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))]
  refine tr_bind_same (fun now enow => ?_)
  -- the release head at `s1`
  have grdue : localtimer.release_due gS s1 (L.cpu s) = localtimer.release_due st s1 (L.cpu s) := by
    have := release_due.guard (gS := gS) s1
      (ndR s1 e1N _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]))
      (fun hne => by
        have e : L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.RELEASE_HEAD) =
            L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) := by
          rw [e1N]
          exact hnode1 _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
            (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
        rw [e] at hne ⊢
        obtain ⟨r1, -, -, r4, r5⟩ := rel_facts hI hne
        have hqr := scq_of hO hS r4
        rw [scK1 _ r1]
        refine ⟨gRd' _ ?_ (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne, Or.inl rfl⟩)))), ?_⟩
        · rw [scA_eq]; exact field_aligned (hT _ r1) (by simp) (by simp)
        · exact PathObl.ScAcc.head (W := fun _ => True)
            ⟨fun b ha hb => gRd' _ ha (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne, Or.inr hb⟩)))), fun _ _ _ => trivial,
              trivial⟩
            ((SCq.agree hqr agΩ1).1 (by
              unfold LawfulStore.rmax; rw [agΩ1 _ (hqr.2.1 _ hqr.2.2.2.2 hqr.2.2.2.1)]; exact r5)))
      (ndR s1 e1N _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
    rwa [c1] at this
  rw [grdue]
  refine tr_bind_same (fun b3 _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  rw [PathObl.sched.consumed.guard (gS := gS) s1
    (ndR s1 e1N _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))]
  refine tr_bind_same (fun i2 ei2 => ?_)
  rw [PathObl.sporadic.sufficient.guard (gS := gS) ar s1 a1 (L.cscW s) i2 (hSc.head wf1)]
  refine tr_bind_same (fun b4 eb4 => ?_)
  have tm1e : L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.TIMER_MIN) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) := by
    rw [e1N]
    exact hnode1 _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
  have gtdue : localtimer.timer_due gS s1 (L.cpu s) now = localtimer.timer_due st s1 (L.cpu s) now := by
    have := timer_due.guard (gS := gS) s1 now
      (ndR s1 e1N _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])) (fun hne => by
        rw [tm1e] at hne ⊢
        have hT0 := (tmin_facts (BXI.blk hI) hcC hne).1
        exact gRd' _ (field_aligned (hT _ hT0) (by simp) (by simp)) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨hne, rfl⟩))))))
    rwa [c1] at this
  rw [gtdue]
  refine tr_bind_same (fun due edue => ?_)
  have grr : localtimer.round_robin_ok gS ar s1 a1 (L.cpu s) (L.curW s) (L.cscW s) now =
      localtimer.round_robin_ok st ar s1 a1 (L.cpu s) (L.curW s) (L.cscW s) now := by
    have := round_robin_ok.guard (gS := gS) ar (s := s1) a1 (ct := L.curW s) (csc := L.cscW s) (now := now)
      (ndR s1 e1N _ (by simp [layout.node.IDLE_SC]) (by simp [layout.node.IDLE_SC]))
      (hSc.off wf1 _ (by simp [layout.sc.PERIOD]) (by simp [layout.sc.PERIOD]))
      rSt rSc (by rw [scK1 _ hcT, hsct]; exact rMx) rIq
      (hSc.off wf1 _ (by simp [layout.sc.REFILL_HEAD]) (by simp [layout.sc.REFILL_HEAD]))
      (hSc.off wf1 _ (by simp [layout.sc.REFILL_TAIL]) (by simp [layout.sc.REFILL_TAIL]))
      ⟨(hSc.rt wf1 wf1.head_lt).1, (hSc.rt wf1 wf1.head_lt).2.2.1⟩
      ⟨(hSc.rt wf1 wf1.tail_lt).1, (hSc.rt wf1 wf1.tail_lt).2.2.1⟩
      (ndR s1 e1N _ (by simp [layout.node.L1_BITMAP]) (by simp [layout.node.L1_BITMAP]))
      (by rw [k1]; exact rD1)
      ⟨ndR s1 e1N _ (by rw [l1Off_val]; omega) (by rw [l1Off_val]), fun inv hinv =>
        ndR s1 e1N _ (by simp; omega) (by simp)⟩
      (cR 3448#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))
    rwa [c1] at this
  have gfire : localtimer.fire_ok gS s1 (L.cpu s) (L.curW s) p now =
      localtimer.fire_ok st s1 (L.cpu s) (L.curW s) p now := by
    rw [fire_ok_tm0 gS s1 _ _ now hp0, fire_ok_tm0 st s1 _ _ now hp0]
  refine tr_bind (fun ok1 e1 _ => ?_) (fun ok1 _ hk => ?_)
  · cases b4 <;> cases due
    · simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte] at e1 ⊢
      rw [grr]; exact e1
    · simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte] at e1 ⊢
      exact e1
    · simp only [Bool.false_eq_true, not_true_eq_false, ↓reduceIte] at e1 ⊢
      exact e1
    · simp only [Bool.false_eq_true, not_true_eq_false, ↓reduceIte] at e1 ⊢
      rw [gfire]; exact e1
  · cases ok1
    · rw [if_neg Bool.false_ne_true] at hk ⊢; exact hk
    · exfalso
      rw [if_pos rfl] at hk
      obtain ⟨⟨x2, s2, a2⟩, -, hk⟩ := bind_eq_ok hk
      try simp only [uncurry_apply_pair] at hk
      try dsimp only at hk
      obtain ⟨⟨s3, a3⟩, -, hk⟩ := bind_eq_ok hk
      try simp only [uncurry_apply_pair] at hk
      obtain ⟨⟨s4, a4⟩, -, hk⟩ := bind_eq_ok hk
      try simp only [uncurry_apply_pair] at hk
      obtain ⟨⟨s5, a5⟩, -, hk⟩ := bind_eq_ok hk
      try simp only [uncurry_apply_pair] at hk
      obtain ⟨t, -, hk⟩ := bind_eq_ok hk
      obtain ⟨⟨s6, a6⟩, -, hk⟩ := bind_eq_ok hk
      try simp only [uncurry_apply_pair] at hk
      have e := ok_inj_ff hk
      simp at e

/-- **Every tail run with an empty plan is the run on a store answering its reads and writes** (module
docstring): `irqTail_accT` and `irqTail_decT`. -/
theorem irqTail_guardT {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
    (hA : P0.ArchTotal ar) {s : S} {a : A} {irq mx : U64} {p : localtimer.TimerIrqPlan} {r : Bool × S × A}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (nR : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o))
    (gcok : localtimer.current_ok gS s (L.cpu s) (L.curW s) (L.cscW s) =
      localtimer.current_ok st s (L.cpu s) (L.curW s) (L.cscW s))
    (gRd : IrqOk st s → ∀ w, Aligned w → IrqRdT st Z s w → R w)
    (gWr : IrqOk st s → ∀ w, Aligned w → IrqWr st Z s w → w ≠ stA (L.curW s) → W w)
    (hIq : IrqOk st s → ∀ i, interrupt.state_off irq = ok i → R (core.num.U64.wrapping_add (L.ksb s) i))
    (hD1 : IrqOk st s → R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hD2 : IrqOk st s → R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME))
    (hwS : IrqOk st s → L.mem s (stA (L.curW s)) = sched.TS_RESTART → ∀ X, L.mem X (stA (L.curW s)) = sched.TS_RESTART →
      L.mem X (affA (L.curW s)) = L.cpu s →
      gS.write X (stA (L.curW s)) sched.TS_RUNNING = st.write X (stA (L.curW s)) sched.TS_RUNNING)
    (hKr : IrqOk st s → R (krA (L := L) s)) (hTab : IrqOk st s → PathObl.RdTab (L := L) R s)
    (hAs : AsidOff (L := L) Ω Sg s) (hW1 : W (ctA (L := L) s)) (hW2 : W (cnA (L := L) s))
    (emx : layout.irq.MAX = ok mx) (hle : ¬ irq > mx)
    (ei1 : interrupt.irq_state st s irq = ok interrupt.IRQ_TIMER) (hp0 : p.tm = 0#u64)
    (h : irqTailF st ar s a irq (L.cpu s) p = ok r) :
    irqTailF gS ar s a irq (L.cpu s) p = ok r := by
  obtain ⟨b, s', a'⟩ := r
  cases b
  · exact irqTail_decT ar hA hI nR gcok gRd hD1 hD2 hW1 hW2 hp0 h
  · exact irqTail_accT ar hA hI gRd gWr hIq hD1 hD2 hwS hKr hTab hAs emx hle ei1 hp0 h

end main

end Fl4Proofs.P2
