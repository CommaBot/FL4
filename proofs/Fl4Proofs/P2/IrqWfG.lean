/-
# P2 (line p3mc, gen 25): the timer interrupt whose signal's head waiter is another core's, generic pieces

Handoff §29c item 1 (W-f). At an irq view start whose earliest thread `tm` is homed but whose bound notification is
`WAITING` with a head waiter `w` of another core (in `ρ`), the real run declines inside `fire_ok` (`wake_ok` →
`may_run_here`: `AFFINITY w ≠ cpu`), while the run at the view start `σ` (where every `AFFINITY` reads the core) may
accept. The certificate (P2/IrqWfAnn) therefore runs the head and the notification check at the real state `s`
(carrying `ρ`), and only the part of the tail before `fire_ok` at `σ` (with the plan's `tm` set to 0, which
`fire_ok` cannot tell apart once it declines):

* `may_run_here_falseW`, `wake_ok_falseW`, **`fireTail_falseW`**: a `WAITING` notification's check declines on a
  store answering its head's `AFFINITY` with another core;
* **`fire_ok.guardKF`** (`fire_ok.guardK` with the tail declining), **`fire_ok_guardWF`** (`fire_ok_guardNW`'s walk:
  `fire_ok` after the timestamp declines on any store answering the tree words `FTree` whose notification check
  declines, at a state agreeing with the invariant state on those words);
* `irqTailF_plan` (the tail depends on the plan only through `fire_ok`), **`irq_pl_guardE`** (`irq_pl_guard` with
  the tail's result left open).

No named premises; no existing statement changed.
-/
import Fl4Proofs.P2.IrqHnAnn
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap
open Fl4Proofs.P2.PathObl (bind_guard_congr irqTailF)

section w
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- `may_run_here` declines on a store answering the thread's `AFFINITY` with another core. -/
theorem may_run_here_falseW {gS : machine.Store S} {x : S} {cpu w : U64}
    (haf : w ≠ 0#u64 → ∃ v, gS.read x (affA w) = ok v ∧ v ≠ cpu) :
    localtimer.may_run_here gS x cpu w = ok false := by
  unfold localtimer.may_run_here
  rw [show obj.Tcb.is_null w = ok (decide (w = 0#u64)) from rfl]
  simp only [bind_ok]
  by_cases h0 : w = 0#u64
  · rw [if_pos (by simpa using h0)]
  rw [if_neg (by simpa using h0)]
  obtain ⟨v, ev, hv⟩ := haf h0
  have ea : obj.Tcb.affinity gS w x = ok v := by
    unfold obj.Tcb.affinity
    rw [PathObl.eq_ok_of_spec Fl4Proofs.P0.Consts.layout.tcb.AFFINITY.spec]
    simp only [lift, bind_ok]
    exact ev
  rw [ea]
  simp only [bind_ok]
  rw [if_neg hv]

/-- `wake_ok` declines on a store answering the woken thread's `AFFINITY` with another core. -/
theorem wake_ok_falseW {gS : machine.Store S} {x : S} {cpu ct w n : U64}
    (haf : w ≠ ct → w ≠ 0#u64 → ∃ v, gS.read x (affA w) = ok v ∧ v ≠ cpu) :
    localtimer.wake_ok gS x cpu ct w n = ok false := by
  unfold localtimer.wake_ok
  obtain ⟨b, eb, hb⟩ := spec_ex_fd (Fl4Proofs.P1.tcb_ne.spec' w ct)
  rw [eb]
  simp only [bind_ok]
  cases b
  · rw [if_neg Bool.false_ne_true]
  rw [if_pos rfl, may_run_here_falseW (haf (hb.1 rfl))]
  simp only [bind_ok]
  rw [if_neg Bool.false_ne_true]

/-- **A waiting notification's check declines on a store answering its head's `AFFINITY` with another core**
(module docstring). -/
theorem fireTail_falseW {R : U64 → Prop} {gS : machine.Store S} [PathObl.GRd gS st R] {x : S} {ct : obj.Tcb}
    {p : localtimer.TimerIrqPlan} {w : U64} (hn0 : p.ntfn ≠ 0#u64)
    (h1 : R (core.num.U64.wrapping_add p.ntfn layout.ntfn.TAIL_STATE))
    (h2 : R (core.num.U64.wrapping_add p.ntfn layout.ntfn.HEAD))
    (hwt : L.epState x p.ntfn = obj.NTFN_WAITING) (hw : L.mem x (epHeadA p.ntfn) = w)
    (haf : w ≠ ct → w ≠ 0#u64 → ∃ v, gS.read x (affA w) = ok v ∧ v ≠ L.cpu x) :
    fireTail gS x (L.cpu x) ct p = ok false := by
  unfold fireTail
  rw [if_neg hn0, ntfn_state_guard p.ntfn x h1, eq_of_spec_fd (obj.Ntfn.state.spec (L := L) x _)]
  simp only [bind_ok]
  rw [hwt, if_neg (by unfold obj.NTFN_WAITING obj.NTFN_ACTIVE; decide), if_neg ntfn_waiting_ne_idle, if_pos rfl,
    PathObl.obj.Ntfn.head.guard (gS := gS) p.ntfn x h2, ntfn_head_ok]
  simp only [bind_ok]
  have e : (L.epQ x p.ntfn).head = w := hw
  rw [e]
  exact wake_ok_falseW haf

variable {R : U64 → Prop} {gS : machine.Store S} [PathObl.GRd gS st R]

/-- **`fire_ok` on the guarded store when its notification check declines** (module docstring): the tree reads as
`fire_ok.guardK`, the run on `st` given (its totality). -/
theorem fire_ok.guardKF {s : S} {ct : obj.Tcb} {p : localtimer.TimerIrqPlan} {now : U64} (P : U64 → Prop)
    (hr : p.tm ≠ 0#u64 → R (core.num.U64.wrapping_add p.tm 3552#u64))
    (hp : p.tm ≠ 0#u64 → R (core.num.U64.wrapping_add p.tm 3560#u64))
    (hd1 : p.tm ≠ 0#u64 → ∀ x, obj.Tcb.timer_parent st p.tm s = ok x → x ≠ 0#u64 →
      R (core.num.U64.wrapping_add x 3528#u64))
    (hP0 : p.tm ≠ 0#u64 → ∀ x, obj.Tcb.timer_right st p.tm s = ok x → x ≠ 0#u64 → P x)
    (hP : ∀ x, P x → R (core.num.U64.wrapping_add x 3544#u64) ∧
      ∀ y, obj.Tcb.timer_left st x s = ok y → y ≠ 0#u64 → P y)
    (hd2 : ∀ x, P x → R (core.num.U64.wrapping_add x 3528#u64))
    (hT : p.tm ≠ 0#u64 → fireTail gS s (L.cpu s) ct p = ok false) {b0 : Bool}
    (h : localtimer.fire_ok st s (L.cpu s) ct p now = ok b0) :
    localtimer.fire_ok gS s (L.cpu s) ct p now = ok false := by
  rw [fire_ok_eq] at h ⊢
  by_cases h0 : p.tm = 0#u64
  · rw [if_pos h0]
  rw [if_neg h0] at h ⊢
  rw [PathObl.obj.Tcb.timer_right.guard (gS := gS) p.tm s (hr h0)]
  obtain ⟨i, ei, h⟩ := bind_eq_ok h
  rw [ei]
  simp only [bind_ok]
  rw [PathObl.obj.Tcb.timer_parent.guard (gS := gS) p.tm s (hp h0)]
  obtain ⟨i1, ei1, h⟩ := bind_eq_ok h
  rw [ei1]
  simp only [bind_ok]
  obtain ⟨b, eb, h⟩ := bind_eq_ok h
  rw [eb]
  simp only [bind_ok]
  cases b
  · have hi0 : i ≠ 0#u64 := fun e => by have h' := is_null_eq eb; simp [e] at h'
    rw [if_neg Bool.false_ne_true] at h ⊢
    have g := fire_ok_loop.guardK (gS := gS) P hP (hP0 h0 i ei hi0) (fuel := layout.TREE_FUEL)
    rw [g.1]
    obtain ⟨i2, ei2, h⟩ := bind_eq_ok h
    have hi2 : P i2 := g.2 i2 ei2
    rw [ei2]
    simp only [bind_ok]
    obtain ⟨b1, eb1, h⟩ := bind_eq_ok h
    rw [eb1]
    simp only [bind_ok]
    cases b1
    · rw [if_neg Bool.false_ne_true] at h ⊢
      rw [PathObl.obj.Tcb.timer_deadline.guard (gS := gS) i2 s (hd2 i2 hi2)]
      obtain ⟨d, ed, -⟩ := bind_eq_ok h
      rw [ed]
      simp only [bind_ok]
      by_cases hd : d ≤ now
      · rw [if_pos hd]
      · rw [if_neg hd]; exact hT h0
    · rw [if_pos rfl]; exact hT h0
  · rw [if_pos rfl] at h ⊢
    obtain ⟨b1, eb1, h⟩ := bind_eq_ok h
    rw [eb1]
    simp only [bind_ok]
    cases b1
    · have hi1 : i1 ≠ 0#u64 := fun e => by have h' := is_null_eq eb1; simp [e] at h'
      rw [if_neg Bool.false_ne_true] at h ⊢
      rw [PathObl.obj.Tcb.timer_deadline.guard (gS := gS) i1 s (hd1 h0 i1 ei1 hi1)]
      obtain ⟨d, ed, -⟩ := bind_eq_ok h
      rw [ed]
      simp only [bind_ok]
      by_cases hd : d ≤ now
      · rw [if_pos hd]
      · rw [if_neg hd]; exact hT h0
    · rw [if_pos rfl]; exact hT h0

end w

section own
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}

set_option maxHeartbeats 32000000 in
/-- **`fire_ok` after the timestamp declines on a store answering `FireRd` whose notification check declines**
(module docstring; `fire_ok_guardNW`'s walk). -/
theorem fire_ok_guardWF {R : U64 → Prop} {gS : machine.Store S} [PathObl.GRd gS st R] {s s1 : S}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hL : StLay K st T Scs Z s)
    (gRd : ∀ w, FTree st T s w → R w)
    (c1 : L.cpu s1 = L.cpu s)
    (m1 : ∀ b, FTree st T s b → L.mem s1 b = L.mem s b)
    {p : localtimer.TimerIrqPlan}
    (hpt0 : p.tm ≠ 0#u64 → p.tm = L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)) (ct : obj.Tcb) (now : U64)
    (hTl : p.tm ≠ 0#u64 → fireTail gS s1 (L.cpu s1) ct p = ok false) :
    localtimer.fire_ok gS s1 (L.cpu s) ct p now = ok false := by
  by_cases hp0 : p.tm = 0#u64
  · rw [fire_ok_eq, if_pos hp0]
  obtain ⟨Q, Rq, h0⟩ := hI.1
  have hT : TcbPlaced T := h0.tcbs
  have hcC : L.cpu s ∈ Cs := h0.cur
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ hcC
  obtain ⟨TM, eTM⟩ : ∃ x, L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) = x := ⟨_, rfl⟩
  have hpt : p.tm = TM := by rw [hpt0 hp0, eTM]
  have hne : TM ≠ 0#u64 := by rw [← hpt]; exact hp0
  have q1 : TM ∈ T := by
    have := (tmin_facts (BXI.blk hI) hcC (by rw [eTM]; exact hne)).1
    rw [eTM] at this
    exact this
  obtain ⟨tr, ctr⟩ := (TInv.rb (BXI.blk hI)).tree _ hcC
  have hk : TM ∈ tr.keys := by
    have e := ctr.min
    rw [eTM] at e
    rw [e]
    exact tr.minKey_mem.resolve_left (by rw [← e]; exact hne)
  have keyF : ∀ {y k : U64}, y ∈ tr.keys → 3528 ≤ k.val → k.val < 3576 → k.val % 8 = 0 →
      FTree st T s (core.num.U64.wrapping_add y k) := @fun y k hy h1 h2 h3 =>
    ⟨y, ctr.inT y hy, ⟨ctr.armed y hy, ctr.core y hy⟩, k, h1, h2, h3, rfl⟩
  have keyR : ∀ {y k : U64}, y ∈ tr.keys → 3528 ≤ k.val → k.val < 3576 → k.val % 8 = 0 →
      R (core.num.U64.wrapping_add y k) := @fun y k hy h1 h2 h3 => gRd _ (keyF hy h1 h2 h3)
  have mT : ∀ {y k : U64}, y ∈ tr.keys → 3528 ≤ k.val → k.val < 3576 → k.val % 8 = 0 →
      L.mem s1 (core.num.U64.wrapping_add y k) = L.mem s (core.num.U64.wrapping_add y k) :=
    @fun y k hy h1 h2 h3 => m1 _ (keyF hy h1 h2 h3)
  have lks := ctr.rep.links TM hk
  simp only [lk_l, lk_r, lk_p] at lks
  have mtr : L.mem s1 (trA TM) = L.mem s (trA TM) := mT (k := 3552#u64) hk (by simp) (by simp) (by simp)
  have mtp : L.mem s1 (tpA TM) = L.mem s (tpA TM) := mT (k := 3560#u64) hk (by simp) (by simp) (by simp)
  have hd1 : p.tm ≠ 0#u64 → ∀ x, obj.Tcb.timer_parent st p.tm s1 = ok x → x ≠ 0#u64 →
      R (core.num.U64.wrapping_add x 3528#u64) := fun _ x ex hx0 => by
    rw [hpt, eq_of_spec_fd (obj.Tcb.timer_parent.val (L := L) s1 TM), mtp] at ex
    have ex' := ok_inj_ff ex
    subst ex'
    exact keyR (lks.2.2.resolve_left hx0) (by simp) (by simp) (by simp)
  have hP0 : p.tm ≠ 0#u64 → ∀ x, obj.Tcb.timer_right st p.tm s1 = ok x → x ≠ 0#u64 → x ∈ tr.keys :=
    fun _ x ex hx0 => by
      rw [hpt, eq_of_spec_fd (obj.Tcb.timer_right.val (L := L) s1 TM), mtr] at ex
      have ex' := ok_inj_ff ex
      subst ex'
      exact lks.2.1.resolve_left hx0
  have hP : ∀ x, x ∈ tr.keys → R (core.num.U64.wrapping_add x 3544#u64) ∧
      ∀ y, obj.Tcb.timer_left st x s1 = ok y → y ≠ 0#u64 → y ∈ tr.keys := fun x hx => by
    refine ⟨keyR hx (by simp) (by simp) (by simp), fun y ey hy0 => ?_⟩
    have hl := ctr.rep.links x hx
    simp only [lk_l, lk_r, lk_p] at hl
    have mtl : L.mem s1 (tlA x) = L.mem s (tlA x) := mT (k := 3544#u64) hx (by simp) (by simp) (by simp)
    rw [eq_of_spec_fd (obj.Tcb.timer_left.val (L := L) s1 x), mtl] at ey
    have ey' := ok_inj_ff ey
    subst ey'
    exact hl.1.resolve_left hy0
  obtain ⟨b0, hb0, -⟩ := spec_ex_fd (P0.localtimer.fire_ok.p0 st s1 (L.cpu s1) ct p now LawfulStore.total)
  have g := fire_ok.guardKF (gS := gS) (s := s1) (ct := ct) (p := p) (now := now) (fun x => x ∈ tr.keys)
    (fun _ => by rw [hpt]; exact keyR hk (by simp) (by simp) (by simp))
    (fun _ => by rw [hpt]; exact keyR hk (by simp) (by simp) (by simp))
    hd1 hP0 hP (fun x hx => keyR hx (by simp) (by simp) (by simp)) hTl hb0
  rwa [c1] at g

end own

section plan
variable {S : Type} {A : Type}

/-- **The tail depends on the plan only through `fire_ok`** (module docstring). -/
theorem irqTailF_plan (M : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) (irq cpu : U64)
    (p p' : localtimer.TimerIrqPlan)
    (h : ∀ s1 a1 now ct, sched.update_timestamp M ar s a = ok (s1, a1) → sched.cur_time M s1 = ok now →
      sched.cur_thread M s = ok ct →
      localtimer.fire_ok M s1 cpu ct p now = localtimer.fire_ok M s1 cpu ct p' now) :
    irqTailF M ar s a irq cpu p = irqTailF M ar s a irq cpu p' := by
  unfold irqTailF
  refine bind_guard_congr rfl fun ct ect => ?_
  refine bind_guard_congr rfl fun csc _ => ?_
  refine bind_guard_congr rfl fun b1 _ => ?_
  cases b1
  · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
  rw [if_pos rfl, if_pos rfl]
  refine bind_guard_congr rfl fun b2 _ => ?_
  cases b2
  · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
  rw [if_pos rfl, if_pos rfl]
  refine bind_guard_congr rfl fun q eu => ?_
  obtain ⟨s1, a1⟩ := q
  try dsimp only
  refine bind_guard_congr rfl fun now enow => ?_
  rw [h s1 a1 now ct eu enow ect]

end plan

section guard
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {R : U64 → Prop} {gS : machine.Store S} [PathObl.GRd gS st R] {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **The whole run on a store answering the head's reads, its tail given to run** (module docstring). -/
theorem irq_pl_guardE {s : S} {a : A} {irq : U64} {p : localtimer.TimerIrqPlan} {r : Bool × S × A}
    (hi : irq.val < 128 → ∀ i, interrupt.state_off irq = ok i → R (core.num.U64.wrapping_add (L.ksb s) i))
    (h1 : R (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))
    (h2 : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64 →
      PlanTm st R s (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))
    (htail : ∀ mx, layout.irq.MAX = ok mx → ¬ irq > mx →
      interrupt.irq_state st s irq = ok interrupt.IRQ_TIMER → ∀ tip, localtimer.plan_objects st s = ok tip →
      localtimer.same_plan tip p = ok true → ∃ r', irqTailF gS ar s a irq (L.cpu s) p = ok r')
    (h : localtimer.handle_timer_irq_local st ar s a irq p = ok r) :
    ∃ r', localtimer.handle_timer_irq_local gS ar s a irq p = ok r' := by
  have hpl := plan_objects.guard (gS := gS) h1 h2
  rw [irq_splitF st] at h
  rw [irq_splitF gS, PathObl.gst_cur_cpu (g := gS)]
  rw [L.cur_cpu_eq] at h ⊢
  simp only [bind_ok, num_domains_ne_one_false, Bool.false_eq_true, ↓reduceIte] at h ⊢
  obtain ⟨mx, emx, h⟩ := bind_eq_ok h
  rw [emx]
  simp only [bind_ok]
  by_cases hle : irq > mx
  · rw [if_pos hle]; exact ⟨_, rfl⟩
  rw [if_neg hle] at h ⊢
  have hlt : irq.val < 128 := by
    rw [eq_of_spec_fd layout.irq.MAX.spec] at emx
    have e := ok_inj_ff emx
    subst e
    scalar_tac
  have eirq : interrupt.irq_state gS s irq = interrupt.irq_state st s irq := by
    unfold interrupt.irq_state
    exact bind_guard_congr rfl fun i ei => PathObl.obj.ks_get.guard (gS := gS) s i (hi hlt i ei)
  rw [eirq]
  obtain ⟨i1, ei1, h⟩ := bind_eq_ok h
  rw [ei1]
  simp only [bind_ok]
  by_cases hi1 : (i1 != interrupt.IRQ_TIMER) = true
  · rw [if_pos hi1]; exact ⟨_, rfl⟩
  rw [if_neg hi1] at h ⊢
  have e1 : i1 = interrupt.IRQ_TIMER := by
    by_contra hne
    exact hi1 (bne_iff_ne.mpr hne)
  subst e1
  rw [hpl]
  obtain ⟨tip, etip, h⟩ := bind_eq_ok h
  rw [etip]
  simp only [bind_ok]
  obtain ⟨b, eb, h⟩ := bind_eq_ok h
  rw [eb]
  simp only [bind_ok]
  cases b
  · rw [if_neg Bool.false_ne_true]; exact ⟨_, rfl⟩
  · rw [if_pos rfl]; exact htail mx emx hle ei1 tip etip eb

end guard

end Fl4Proofs.P2
