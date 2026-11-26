/-
# P2: a declined `fire_ok` on the guarded store

* Conditional guards (as `plan_objects.guard`'s `TmHere` split): `MayRdC` / `may_run_here.guardZ` (nothing read of
  a null thread, its words after `AFFINITY` only once `AFFINITY` is the core), `TopRdC` / `top_ok.guardC` (the
  ready-queue head read only for a non-empty bitmap, its words by `MayRdC`), `WakeRdC` / `wake_ok.guardC` (the
  woken thread's `DOMAIN` / `IN_QUEUES` only once `may_run_here` holds), `fireTail.guardC` (the notification's
  words only for a non-null one), `fire_ok_loop.guardK` / `fire_ok.guardK` (links read only of non-null threads).
* `plan_facts`, `same_plan_tm`: a plan's due thread is null, or `TIMER_MIN` homed here (`TmHere`), its notification
  null or the thread's bound one.
* `fire_rd`: at the entry state `s` of the timer interrupt (P1's invariant, `StLay`, `IrqLay`, the notifications
  `Nt` typed in P1's heap `H`) and a state `s1` differing from `s` only at the node's `CUR_TIME` / `CONSUMED`,
  `fire_ok` at `s1` for the plan agreeing with `plan_objects s` is the same on `guard st (MaxR …) W`: the due
  thread's tree links and its successor walk are words of this core's tree (`TRB.Rep.links`: a key's links are null
  or keys), the notification is the due thread's bound one (`BndS.tb`), so all its words but `BOUND_TCB` (the
  gate's) are the due thread's home core's (`ntfnOwner`), the queue heads (notification queue, P1 `EpsWit`; ready
  queue, `ReadyRel`) are null or TCBs, whose words `may_run_here` reads are the gate's or, once homed here, this
  core's.

Premises: `StLay` [J], `IrqLay` [J] (as `irq_rd_own`); `hNt` (P1's notifications `Nt` are notifications of its heap
`H`: `fun _ h => h` at the canonical instantiation `Nt = H.ntfns`).
-/
import Fl4Proofs.P2.FootTimerIrqOwn
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.Serial (Owner)
open Fl4Proofs.P2.OwnMap
open Fl4Proofs.P2.PathObl (guard RPerm WPerm HeldBy GateOnly bind_guard_congr)

section g
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R : U64 → Prop}
variable {gS : machine.Store S} [PathObl.GRd gS st R]

/-- What `may_run_here s cpu t` reads: nothing for a null `t`, its `AFFINITY`, and once that is `cpu` its `STATE`,
`YIELD_TO`, VCPU word, `SC` and the SC's `CORE`. -/
def MayRdC (st : machine.Store S) [L : LawfulStore st] (R : U64 → Prop) (s : S) (cpu t : U64) : Prop :=
  t ≠ 0#u64 → R (affA t) ∧ (L.mem s (affA t) = cpu → R (stA t) ∧ R (yieldA t) ∧
    R (core.num.U64.wrapping_add t 3664#u64) ∧ R (scA t) ∧
    (L.mem s (scA t) ≠ 0#u64 → R (scCoreA (L.mem s (scA t)))))

/-- **`may_run_here` on the guarded store** (`MayRdC`). -/
theorem may_run_here.guardZ (s : S) (cpu t : U64) (h : MayRdC st R s cpu t) :
    localtimer.may_run_here gS s cpu t = localtimer.may_run_here st s cpu t := by
  unfold localtimer.may_run_here
  refine bind_guard_congr rfl fun b eb => ?_
  by_cases hb : b = true
  · rw [if_pos hb, if_pos hb]
  have ht : t ≠ 0#u64 := fun e => hb (by rw [is_null_eq eb]; exact decide_eq_true e)
  obtain ⟨h1, h⟩ := h ht
  rw [if_neg hb, if_neg hb, PathObl.obj.Tcb.affinity.guard t s h1]
  refine bind_guard_congr rfl fun i ei => ?_
  by_cases hi : i = cpu
  swap
  · rw [if_neg hi, if_neg hi]
  rw [aff_ok] at ei
  obtain ⟨h2, h3, h4, h5, h6⟩ := h ((ok_inj_ff ei).trans hi)
  rw [if_pos hi, if_pos hi, PathObl.obj.Tcb.state.guard t s h2, PathObl.obj.Tcb.yield_to.guard t s h3,
    PathObl.obj.Tcb.sc.guard t s h5, eq_of_spec_fd (obj.Tcb.sc.spec s t)]
  simp only [bind_ok]
  by_cases h0 : L.mem s (scA t) = 0#u64
  · rw [if_pos h0, if_pos h0]
  · rw [if_neg h0, if_neg h0, PathObl.obj.Sc.cpu.guard _ s (h6 h0)]

/-- What `top_ok` reads: the bitmaps, the current domain, and for a non-empty bitmap the head of the highest queue
and what `may_run_here` reads of it. -/
structure TopRdC (st : machine.Store S) [L : LawfulStore st] (R : U64 → Prop) (s : S) : Prop where
  l1 : R (L.nodeAt s (L.cpu s) layout.node.L1_BITMAP)
  dom : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN)
  bm : PathObl.RdBitmap (L := L) R s
  top : L.mem s (L.nodeAt s (L.cpu s) layout.node.L1_BITMAP) ≠ 0#u64 → ∀ d p q, sched.cur_domain st s = ok d →
    sched.highest_prio st s d = ok p → layout.node.READY_QUEUES = ok q →
    R (L.nodeAt s (L.cpu s) (core.num.U64.wrapping_add q (core.num.U64.wrapping_mul p 16#u64))) ∧
    MayRdC st R s (L.cpu s)
      (L.mem s (L.nodeAt s (L.cpu s) (core.num.U64.wrapping_add q (core.num.U64.wrapping_mul p 16#u64))))

theorem top_ok.guardC {s : S} (h : TopRdC st R s) :
    localtimer.top_ok gS s (L.cpu s) = localtimer.top_ok st s (L.cpu s) := by
  unfold localtimer.top_ok
  rw [PathObl.obj.node_get.guard (gS := gS) s _ _ h.l1]
  refine bind_guard_congr rfl fun i ei => ?_
  by_cases h0 : i = 0#u64
  · rw [if_pos h0, if_pos h0]
  rw [node_get_ok] at ei
  have hl1 : L.mem s (L.nodeAt s (L.cpu s) layout.node.L1_BITMAP) ≠ 0#u64 := fun e =>
    h0 (by rw [← ok_inj_ff ei]; exact e)
  rw [if_neg h0, if_neg h0, PathObl.sched.cur_domain.guard (gS := gS) s h.dom]
  refine bind_guard_congr rfl fun d ed => ?_
  rw [PathObl.sched.highest_prio.guard (gS := gS) s d h.bm]
  refine bind_guard_congr rfl fun p ep => ?_
  simp only [lift, bind_ok]
  refine bind_guard_congr rfl fun q eq => ?_
  obtain ⟨h1, h2⟩ := h.top hl1 d p q ed ep eq
  rw [PathObl.obj.node_get.guard (gS := gS) s _ _ h1]
  refine bind_guard_congr rfl fun t et => ?_
  rw [node_get_ok] at et
  rw [← ok_inj_ff et]
  exact may_run_here.guardZ s _ _ h2

/-- What `wake_ok s cpu ct w n` reads (`MayRdC` for `w`, its `DOMAIN` / `IN_QUEUES` once `may_run_here` holds). -/
structure WakeRdC (st : machine.Store S) [L : LawfulStore st] (R : U64 → Prop) (s : S) (w n : U64) : Prop where
  may : MayRdC st R s (L.cpu s) w
  dq : w ≠ 0#u64 → L.mem s (affA w) = L.cpu s → R (domA w) ∧ R (inqA w)
  nsc : R (ntfnScA n)
  top : TopRdC st R s

theorem wake_ok.guardC {s : S} {ct w n : U64} (h : WakeRdC st R s w n) :
    localtimer.wake_ok gS s (L.cpu s) ct w n = localtimer.wake_ok st s (L.cpu s) ct w n := by
  unfold localtimer.wake_ok
  refine bind_guard_congr rfl fun b _ => ?_
  cases b
  · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
  rw [if_pos rfl, if_pos rfl, may_run_here.guardZ s (L.cpu s) w h.may]
  refine bind_guard_congr rfl fun b1 eb1 => ?_
  cases b1
  · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
  obtain ⟨hw0, haff, -, -⟩ := may_run_here_true eb1
  obtain ⟨hd, hq⟩ := h.dq hw0 haff
  have hsc : R (scA w) := ((h.may hw0).2 haff).2.2.2.1
  rw [if_pos rfl, if_pos rfl, PathObl.obj.Tcb.domain.guard (gS := gS) w s hd]
  refine bind_guard_congr rfl fun i _ => ?_
  rw [PathObl.sched.cur_domain.guard (gS := gS) s h.top.dom]
  refine bind_guard_congr rfl fun i1 _ => ?_
  by_cases hi : i = i1
  swap
  · rw [if_neg hi, if_neg hi]
  rw [if_pos hi, if_pos hi, PathObl.sched.queued.guard (gS := gS) s w hq]
  refine bind_guard_congr rfl fun b2 _ => ?_
  cases b2
  swap
  · rw [if_pos rfl, if_pos rfl]
  rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, PathObl.obj.Tcb.sc.guard (gS := gS) w s hsc]
  refine bind_guard_congr rfl fun i2 _ => ?_
  by_cases h2 : i2 = 0#u64
  swap
  · rw [if_neg h2, if_neg h2]; exact top_ok.guardC h.top
  rw [if_pos h2, if_pos h2, PathObl.obj.Ntfn.sc.guard (gS := gS) n s h.nsc]
  refine bind_guard_congr rfl fun i3 _ => ?_
  by_cases h3 : (i3 != 0#u64) = true
  · rw [if_pos h3, if_pos h3]
  · rw [if_neg h3, if_neg h3]; exact top_ok.guardC h.top

/-- `fireTail` on the guarded store, the notification's words read only for a non-null one. -/
theorem fireTail.guardC {s : S} {ct : obj.Tcb} {p : localtimer.TimerIrqPlan}
    (h : p.ntfn ≠ 0#u64 → R (core.num.U64.wrapping_add p.ntfn layout.ntfn.TAIL_STATE) ∧
      R (core.num.U64.wrapping_add p.ntfn layout.ntfn.BOUND_TCB) ∧
      R (core.num.U64.wrapping_add p.ntfn layout.ntfn.HEAD) ∧
      R (core.num.U64.wrapping_add p.tm layout.tcb.STATE) ∧ WakeRdC st R s p.tm p.ntfn ∧
      ∀ w, obj.Ntfn.head st p.ntfn s = ok w → WakeRdC st R s w p.ntfn) :
    fireTail gS s (L.cpu s) ct p = fireTail st s (L.cpu s) ct p := by
  unfold fireTail
  by_cases h0 : p.ntfn = 0#u64
  · rw [if_pos h0, if_pos h0]
  obtain ⟨h1, h2, h4, h3, hw1, hw2⟩ := h h0
  rw [if_neg h0, if_neg h0, ntfn_state_guard p.ntfn s h1]
  refine bind_guard_congr rfl fun x _ => ?_
  by_cases ha : x = obj.NTFN_ACTIVE
  · rw [if_pos ha, if_pos ha]
  rw [if_neg ha, if_neg ha]
  by_cases hi : x = obj.NTFN_IDLE
  · rw [if_pos hi, if_pos hi, PathObl.obj.Ntfn.bound_tcb.guard (gS := gS) p.ntfn s h2]
    refine bind_guard_congr rfl fun b2 _ => ?_
    by_cases hz : b2 = 0#u64
    · rw [if_pos hz, if_pos hz]
    rw [if_neg hz, if_neg hz]
    by_cases hn : (b2 != p.tm) = true
    · rw [if_pos hn, if_pos hn]
    rw [if_neg hn, if_neg hn, PathObl.obj.Tcb.state.guard (gS := gS) p.tm s h3]
    refine bind_guard_congr rfl fun bs _ => ?_
    by_cases hv : bs = sched.TS_RUNNING_VM
    · rw [if_pos hv, if_pos hv]
    rw [if_neg hv, if_neg hv]
    by_cases hr : bs = sched.TS_BLOCKED_ON_RECV
    · rw [if_pos hr, if_pos hr]
      by_cases hwt : p.waiter = p.tm
      swap
      · rw [if_neg hwt, if_neg hwt]
      rw [if_pos hwt, if_pos hwt]
      by_cases he : (p.ep != 0#u64) = true
      swap
      · rw [if_neg he, if_neg he]
      rw [if_pos he, if_pos he]
      exact wake_ok.guardC hw1
    · rw [if_neg hr, if_neg hr]
  · rw [if_neg hi, if_neg hi]
    by_cases hw : x = obj.NTFN_WAITING
    swap
    · rw [if_neg hw, if_neg hw]
    rw [if_pos hw, if_pos hw, PathObl.obj.Ntfn.head.guard (gS := gS) p.ntfn s h4]
    exact bind_guard_congr rfl fun w ew => wake_ok.guardC (hw2 w ew)

/-- The walk to the due thread's successor, left links read only of non-null threads. -/
theorem fire_ok_loop.guardK {s : S} (P : U64 → Prop)
    (hP : ∀ x, P x → R (core.num.U64.wrapping_add x 3544#u64) ∧
      ∀ y, obj.Tcb.timer_left st x s = ok y → y ≠ 0#u64 → P y)
    {i fuel : U64} (hi : P i) :
    GE (localtimer.fire_ok_loop gS s i fuel) (localtimer.fire_ok_loop st s i fuel) P := by
  unfold localtimer.fire_ok_loop
  refine GE.loop (fun y : U64 × U64 => P y.1) (fun y => y.2.val) (fun y hy => ?_) (i, fuel) hi
  obtain ⟨i1, f1⟩ := y
  show GE (localtimer.fire_ok_loop.body gS s i1 f1) (localtimer.fire_ok_loop.body st s i1 f1) _
  unfold localtimer.fire_ok_loop.body
  rw [PathObl.obj.Tcb.timer_left.guard (gS := gS) i1 s (hP i1 hy).1]
  refine GE.bind (GE.refl _) fun j ej => ?_
  refine GE.ite (fun hj => GE.ite (fun hf => GE.bind (GE.refl _) fun f2 ef => GE.ret ?_)
    (fun _ => GE.ret ?_)) (fun _ => GE.ret ?_)
  · unfold LoopPost; exact ⟨(hP i1 hy).2 j ej (bne_iff_ne.mp hj), ge_sub1_lt hf ef⟩
  · unfold LoopPost; exact hy
  · unfold LoopPost; exact hy

/-- **`fire_ok` on the guarded store**, the due thread's words read only for a non-null one and the links only of
non-null threads. -/
theorem fire_ok.guardK {s : S} {ct : obj.Tcb} {p : localtimer.TimerIrqPlan} {now : U64} (P : U64 → Prop)
    (hr : p.tm ≠ 0#u64 → R (core.num.U64.wrapping_add p.tm 3552#u64))
    (hp : p.tm ≠ 0#u64 → R (core.num.U64.wrapping_add p.tm 3560#u64))
    (hd1 : p.tm ≠ 0#u64 → ∀ x, obj.Tcb.timer_parent st p.tm s = ok x → x ≠ 0#u64 →
      R (core.num.U64.wrapping_add x 3528#u64))
    (hP0 : p.tm ≠ 0#u64 → ∀ x, obj.Tcb.timer_right st p.tm s = ok x → x ≠ 0#u64 → P x)
    (hP : ∀ x, P x → R (core.num.U64.wrapping_add x 3544#u64) ∧
      ∀ y, obj.Tcb.timer_left st x s = ok y → y ≠ 0#u64 → P y)
    (hd2 : ∀ x, P x → R (core.num.U64.wrapping_add x 3528#u64))
    (hT : p.tm ≠ 0#u64 → fireTail gS s (L.cpu s) ct p = fireTail st s (L.cpu s) ct p) :
    localtimer.fire_ok gS s (L.cpu s) ct p now = localtimer.fire_ok st s (L.cpu s) ct p now := by
  rw [fire_ok_eq, fire_ok_eq]
  by_cases h0 : p.tm = 0#u64
  · rw [if_pos h0, if_pos h0]
  rw [if_neg h0, if_neg h0, PathObl.obj.Tcb.timer_right.guard (gS := gS) p.tm s (hr h0)]
  refine bind_guard_congr rfl fun i ei => ?_
  rw [PathObl.obj.Tcb.timer_parent.guard (gS := gS) p.tm s (hp h0)]
  refine bind_guard_congr rfl fun i1 ei1 => ?_
  refine bind_guard_congr rfl fun b eb => ?_
  cases b
  · have hi0 : i ≠ 0#u64 := fun e => by have h' := is_null_eq eb; simp [e] at h'
    rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    refine (GE.bind (Q := fun _ => True) (fire_ok_loop.guardK P hP (hP0 h0 i ei hi0)) fun i2 hi2 =>
      ⟨?_, fun _ _ => trivial⟩).1
    refine bind_guard_congr rfl fun b1 _ => ?_
    cases b1
    · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true,
        PathObl.obj.Tcb.timer_deadline.guard (gS := gS) i2 s (hd2 i2 hi2)]
      refine bind_guard_congr rfl fun d _ => ?_
      by_cases hd : d ≤ now
      · rw [if_pos hd, if_pos hd]
      · rw [if_neg hd, if_neg hd]; exact hT h0
    · rw [if_pos rfl, if_pos rfl]; exact hT h0
  · rw [if_pos rfl, if_pos rfl]
    refine bind_guard_congr rfl fun b1 eb1 => ?_
    cases b1
    · have hi1 : i1 ≠ 0#u64 := fun e => by have h' := is_null_eq eb1; simp [e] at h'
      rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true,
        PathObl.obj.Tcb.timer_deadline.guard (gS := gS) i1 s (hd1 h0 i1 ei1 hi1)]
      refine bind_guard_congr rfl fun d _ => ?_
      by_cases hd : d ≤ now
      · rw [if_pos hd, if_pos hd]
      · rw [if_neg hd, if_neg hd]; exact hT h0
    · rw [if_pos rfl, if_pos rfl]; exact hT h0

end g

section own
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}

/-- Equal plans have the same due thread and notification. -/
theorem same_plan_tm {x y : localtimer.TimerIrqPlan} (h : localtimer.same_plan x y = ok true) :
    x.tm = y.tm ∧ x.ntfn = y.ntfn := by
  unfold localtimer.same_plan at h
  by_cases h1 : x.tm = y.tm
  · by_cases h2 : x.ntfn = y.ntfn
    · exact ⟨h1, h2⟩
    · rw [if_pos h1, if_neg h2] at h
      exact absurd (ok_inj_ff h) Bool.false_ne_true
  · rw [if_neg h1] at h
    exact absurd (ok_inj_ff h) Bool.false_ne_true

set_option maxHeartbeats 4000000 in
/-- **`plan_objects`' due thread**: null (with a null notification), or `TIMER_MIN` homed here (`TmHere`) with a
null notification or its bound one. -/
theorem plan_facts {s : S} {tip : localtimer.TimerIrqPlan} (h : localtimer.plan_objects st s = ok tip) :
    (tip.tm = 0#u64 ∧ tip.ntfn = 0#u64) ∨
    (tip.tm = L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ∧ tip.tm ≠ 0#u64 ∧ TmHere st s tip.tm ∧
      (tip.ntfn = 0#u64 ∨ tip.ntfn = L.mem s (boundA tip.tm))) := by
  unfold localtimer.plan_objects at h
  obtain ⟨cpu, ecpu, h⟩ := bind_eq_ok h
  rw [L.cur_cpu_eq] at ecpu
  obtain rfl := ok_inj_ff ecpu
  obtain ⟨i, ei, h⟩ := bind_eq_ok h
  rw [node_get_ok] at ei
  obtain rfl := ok_inj_ff ei
  obtain ⟨b, eb, h⟩ := bind_eq_ok h
  rw [is_null_ok] at eb
  obtain rfl := ok_inj_ff eb
  by_cases h0 : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) = 0#u64
  · rw [if_pos (decide_eq_true h0)] at h
    obtain rfl := ok_inj_ff h
    exact Or.inl ⟨rfl, rfl⟩
  rw [if_neg (by simpa using h0)] at h
  obtain ⟨i1, ei1, h⟩ := bind_eq_ok h
  by_cases ha : (i1 != L.cpu s) = true
  · rw [if_pos ha] at h
    obtain rfl := ok_inj_ff h
    exact Or.inl ⟨rfl, rfl⟩
  rw [if_neg ha] at h
  have e1 : i1 = L.cpu s := by by_contra hne; exact ha (bne_iff_ne.mpr hne)
  subst e1
  obtain ⟨i2, ei2, h⟩ := bind_eq_ok h
  by_cases hb : (i2 != L.cpu s) = true
  · rw [if_pos hb] at h
    obtain rfl := ok_inj_ff h
    exact Or.inl ⟨rfl, rfl⟩
  rw [if_neg hb] at h
  have e2 : i2 = L.cpu s := by by_contra hne; exact hb (bne_iff_ne.mpr hne)
  subst e2
  have hh : TmHere st s (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)) := And.intro ei1 ei2
  obtain ⟨n, en, h⟩ := bind_eq_ok h
  rw [eq_of_spec_fd (obj.Tcb.bound_ntfn.val (L := L) s _)] at en
  obtain rfl := ok_inj_ff en
  by_cases hn : L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) = 0#u64
  · rw [if_pos hn] at h
    obtain rfl := ok_inj_ff h
    exact Or.inr ⟨rfl, h0, hh, Or.inl rfl⟩
  rw [if_neg hn] at h
  obtain ⟨⟨x0, bk⟩, -, h⟩ := bind_eq_ok h
  obtain ⟨i3, -, h⟩ := bind_eq_ok h
  by_cases h3 : (i3 != obj.NTFN_IDLE) = true
  · rw [if_pos h3] at h
    obtain rfl := ok_inj_ff h
    exact Or.inr ⟨rfl, h0, hh, Or.inr rfl⟩
  rw [if_neg h3] at h
  obtain ⟨i4, -, h⟩ := bind_eq_ok h
  by_cases h4 : (i4 != L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)) = true
  · rw [if_pos h4] at h
    obtain rfl := ok_inj_ff h
    exact Or.inr ⟨rfl, h0, hh, Or.inr rfl⟩
  rw [if_neg h4] at h
  obtain ⟨i5, -, h⟩ := bind_eq_ok h
  by_cases h5 : (i5 != sched.TS_BLOCKED_ON_RECV) = true
  · rw [if_pos h5] at h
    obtain rfl := ok_inj_ff h
    exact Or.inr ⟨rfl, h0, hh, Or.inr rfl⟩
  rw [if_neg h5] at h
  obtain ⟨ep, -, h⟩ := bind_eq_ok h
  by_cases h6 : ep = 0#u64
  · rw [if_pos h6] at h
    obtain rfl := ok_inj_ff h
    exact Or.inr ⟨rfl, h0, hh, Or.inr rfl⟩
  rw [if_neg h6] at h
  obtain ⟨⟨y0, bk1⟩, -, h⟩ := bind_eq_ok h
  obtain ⟨r, -, h⟩ := bind_eq_ok h
  by_cases h7 : (r != 0#u64) = true
  · rw [if_pos h7] at h
    obtain ⟨a3, -, h⟩ := bind_eq_ok h
    obtain rfl := ok_inj_ff h
    exact Or.inr ⟨rfl, h0, hh, Or.inr rfl⟩
  rw [if_neg h7] at h
  obtain rfl := ok_inj_ff h
  exact Or.inr ⟨rfl, h0, hh, Or.inr rfl⟩

theorem headD_tz {T : Set U64} (l : List U64) (hl : ∀ t ∈ l, t ∈ T) :
    l.headD 0#u64 = 0#u64 ∨ l.headD 0#u64 ∈ T := by
  cases l with
  | nil => exact Or.inl rfl
  | cons a l => exact Or.inr (hl a List.mem_cons_self)

set_option maxHeartbeats 32000000 in
/-- **A declined `fire_ok` on a guarded store, any read set `R`** that contains every word `own K` lets the path
read at `s` in a region other than `.none` (`hR`) and the `CUR_DOMAIN` word (`hRD`); the layout facts are
`StLay` and the notification regions `ntw` (`IrqLay.ntw`). `fire_rd` is `R = MaxR`. -/
theorem fire_rdG (hK : RegionOK K) {s s1 : S} {lk : U64 → Prop} {R W : U64 → Prop}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hL : StLay K st T Scs Z s)
    (ntw : ∀ n ∈ Nt, ∀ k : U64, k.val < 64 → region K (core.num.U64.wrapping_add n k) = .ntfn n)
    (hR : ∀ w, RPerm (own K) (L.cpu s) lk (L.mem s) w → Aligned w → region K w ≠ .none → R w)
    (hRD : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (k1 : L.ksb s1 = L.ksb s) (c1 : L.cpu s1 = L.cpu s)
    (m1 : ∀ b, Aligned b → b ≠ ctA (L := L) s → b ≠ cnA (L := L) s → L.mem s1 b = L.mem s b)
    {tip p : localtimer.TimerIrqPlan} (etip : localtimer.plan_objects st s = ok tip)
    (esp : localtimer.same_plan tip p = ok true) (ct : obj.Tcb) (now : U64) :
    localtimer.fire_ok (guard st R W) s1 (L.cpu s) ct p now =
      localtimer.fire_ok st s1 (L.cpu s) ct p now := by
  have hsp := same_plan_tm esp
  rcases plan_facts etip with ⟨t1, -⟩ | ⟨t1, t2, t3, t4⟩
  · have hp0 : p.tm = 0#u64 := by rw [← hsp.1]; exact t1
    rw [fire_ok_eq, fire_ok_eq, if_pos hp0, if_pos hp0]
  obtain ⟨Q, Rq, h0⟩ := hI.1
  have hT : TcbPlaced T := h0.tcbs
  have hcC : L.cpu s ∈ Cs := h0.cur
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ hcC
  have hX := hI.2.2.1
  have hO := hX.1
  have treg : ∀ {x k : U64}, x ∈ T → 256 ≤ k.val → k.val < 4096 →
      region K (core.num.U64.wrapping_add x k) ≠ .none := fun hx h1 h2 => by
    have e := hL.tcb _ hx _ h1 h2
    unfold fld at e
    rw [e]; intro e; cases e
  obtain ⟨TM, eTM⟩ : ∃ x, L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) = x := ⟨_, rfl⟩
  have hpt : p.tm = TM := by rw [← hsp.1, t1, eTM]
  have hne : TM ≠ 0#u64 := by rw [← hpt, ← hsp.1]; exact t2
  have hh : TmHere st s TM := by rw [← hpt, ← hsp.1]; exact t3
  obtain ⟨N, eN⟩ : ∃ x, L.mem s (boundA TM) = x := ⟨_, rfl⟩
  have hpn : p.ntfn = 0#u64 ∨ p.ntfn = N := by rw [← eN, ← hsp.2, ← hpt, ← hsp.1]; exact t4
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
  have ha : L.mem s (affA TM) = L.cpu s := by
    have e := hh.1
    rw [aff_ok] at e
    exact ok_inj_ff e
  -- `s1` agrees with `s` off the node's `CUR_TIME` / `CONSUMED`
  have mT : ∀ {y k : U64}, y ∈ T → k.val < 4096 → k.val % 8 = 0 →
      L.mem s1 (core.num.U64.wrapping_add y k) = L.mem s (core.num.U64.wrapping_add y k) := by
    intro y k hy hk h8
    exact m1 _ (field_aligned (hT y hy) hk h8) (tcb_node_ne hN hy (hT y hy) hk (by simp [layout.node.CUR_TIME]))
      (tcb_node_ne hN hy (hT y hy) hk (by simp [layout.node.CONSUMED]))
  have mN : ∀ {n k : U64}, n ∈ Nt → k.val < 64 → k.val % 8 = 0 →
      L.mem s1 (core.num.U64.wrapping_add n k) = L.mem s (core.num.U64.wrapping_add n k) := by
    intro n k hn hk h8
    obtain ⟨p1, p2⟩ := hO.ntP _ hn
    have hr := ntw _ hn k hk
    refine m1 _ (by unfold Aligned; rw [ntfn_word_val p1 p2 hk]; omega) (fun e => ?_) (fun e => ?_)
    · rw [e, hL.nd layout.node.CUR_TIME (by simp [layout.node.CUR_TIME])] at hr
      cases hr
    · rw [e, hL.nd layout.node.CONSUMED (by simp [layout.node.CONSUMED])] at hr
      cases hr
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
  have e1N : ∀ o, L.nodeAt s1 (L.cpu s1) o = L.nodeAt s (L.cpu s) o := fun o => by rw [c1, nodeAt_of_ksb k1]
  -- readable words
  have nR : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o) := fun o h1 h2 =>
    hR _ (Or.inl (held_core (hL.own_node _ h1))) (nodeAt_aligned hN h1 h2) (by rw [hL.nd _ h1]; intro e; cases e)
  have ndR : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s1 (L.cpu s1) o) := fun o h1 h2 => by
    rw [e1N]; exact nR o h1 h2
  have gateR : ∀ {x : U64} {k : U64}, x ∈ T → 256 ≤ k.val → k.val < 4096 → k.val % 8 = 0 → GateField k.val →
      R (core.num.U64.wrapping_add x k) := fun hx h1 h2 h8 hg =>
    hR _ (Or.inr (by
      have e := hL.own_tcb hT (L.mem s) hx h1 h2
      unfold fld at e
      unfold GateOnly; rw [e, tcbOwner, if_pos hg])) (field_aligned (hT _ hx) h2 h8) (treg hx h1 h2)
  have homeX : ∀ {x k : U64}, x ∈ T → 256 ≤ k.val → k.val < 4096 → k.val % 8 = 0 →
      (k.val < 3528 ∨ 3576 ≤ k.val) → k.val ≠ 3496 → k.val ≠ 3504 → L.mem s (affA x) = L.cpu s →
      R (core.num.U64.wrapping_add x k) := @fun x k hx h1 h2 h3 h4 h5 h6 hax => by
    refine hR _ ?_ (field_aligned (hT _ hx) h2 h3) (treg hx h1 h2)
    have e := hL.own_tcb hT (L.mem s) hx h1 h2
    unfold fld at e
    unfold RPerm GateOnly
    rw [e]
    unfold tcbOwner
    by_cases hga : GateField k.val
    · rw [if_pos hga]; exact Or.inr rfl
    · rw [if_neg hga, if_neg (show ¬ TimerField k.val by unfold TimerField; omega),
        if_neg (show ¬ GField k.val by unfold GField; omega)]
      exact Or.inl hax
  have keyR : ∀ {y k : U64}, y ∈ tr.keys → 3528 ≤ k.val → k.val < 3576 → k.val % 8 = 0 →
      R (core.num.U64.wrapping_add y k) := @fun y k hy h1 h2 h3 => by
    have hyT := ctr.inT y hy
    refine hR _ (Or.inl ?_) (field_aligned (hT _ hyT) (by omega) h3) (treg hyT (by omega) (by omega))
    have e := hL.own_tcb hT (L.mem s) hyT (k := k) (by omega) (by omega)
    unfold fld at e
    rw [e, tcbOwner, if_neg (show ¬ GateField k.val by unfold GateField; omega),
      if_pos (show TimerField k.val by unfold TimerField; omega), tOwner,
      if_pos (show (L.mem s (fld y oTIMER_DEADLINE)).val ≠ 0 from fun h => ctr.armed y hy (UScalar.eq_of_val_eq h))]
    have e2 := ctr.core y hy
    rw [Nat.shiftRight_eq_div_pow] at e2
    exact MoveTimer.treeCore_of (c := L.cpu s) e2
  have coreR : ∀ {q : U64}, q ∈ Scs → R (scCoreA q) := @fun q hq => by
    obtain ⟨hP, hz⟩ := hO.sc _ hq
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hv := sc_word_val hP hz (o := layout.sc.CORE) (by simp [layout.sc.CORE])
    have hcv : layout.sc.CORE.val = 16 := by simp [layout.sc.CORE]
    have hin : InSC q (Z q) (scCoreA q) :=
      ⟨by unfold scCoreA; rw [hv]; omega, by unfold scCoreA; rw [hv, hcv]; omega⟩
    have e : own K (L.mem s) (scCoreA q) = .gate := by
      simp only [own, hL.sc q hq _ hin]
      rw [if_pos (by unfold scCoreA; rw [hv, hcv])]
    exact hR _ (Or.inr e) (by unfold Aligned scCoreA; rw [hv, hcv]; omega) (by rw [hL.sc q hq _ hin]; intro e; cases e)
  have rD1 : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN) := hRD
  -- what `may_run_here` reads of a null thread or a TCB, at `s1`
  have mayZ : ∀ x : U64, (x = 0#u64 ∨ x ∈ T) → MayRdC st R s1 (L.cpu s1) x ∧
      (x ≠ 0#u64 → L.mem s1 (affA x) = L.cpu s1 → R (domA x) ∧ R (inqA x)) := fun x hx => by
    have ma : x ≠ 0#u64 → L.mem s1 (affA x) = L.cpu s1 → x ∈ T ∧ L.mem s (affA x) = L.cpu s := fun hx0 ha1 => by
      have hxT := hx.resolve_left hx0
      refine ⟨hxT, ?_⟩
      rw [← c1, ← ha1]
      exact (mT (k := 3520#u64) hxT (by simp) (by simp)).symm
    refine ⟨fun hx0 => ⟨gateR (hx.resolve_left hx0) (by simp) (by simp) (by simp) (Or.inl (by simp)),
      fun ha1 => ?_⟩, fun hx0 ha1 => ?_⟩
    · obtain ⟨hxT, hax⟩ := ma hx0 ha1
      have ms : L.mem s1 (scA x) = L.mem s (scA x) := mT (k := 3464#u64) hxT (by simp) (by simp)
      refine ⟨by rw [stA_eq]; exact homeX hxT (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) hax,
        homeX hxT (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) hax,
        gateR hxT (by simp) (by simp) (by simp) (by unfold GateField; simp),
        gateR hxT (by simp) (by simp) (by simp) (by unfold GateField; simp), fun hs0 => ?_⟩
      rw [ms] at hs0 ⊢
      exact coreR (hX.2.2.bound _ hxT hs0).1
    · obtain ⟨hxT, hax⟩ := ma hx0 ha1
      exact ⟨gateR hxT (by simp) (by simp) (by simp) (by unfold GateField; simp),
        homeX hxT (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) hax⟩
  -- what `top_ok` reads at `s1`
  have eL1 : layout.node.L1_BITMAP = l1Off := by unfold layout.node.L1_BITMAP l1Off w64; rfl
  have topC : TopRdC st R s1 := by
    refine ⟨ndR _ (by simp [layout.node.L1_BITMAP]) (by simp [layout.node.L1_BITMAP]), by rw [k1]; exact rD1,
      ⟨ndR _ (by rw [l1Off_val]; omega) (by rw [l1Off_val]), fun inv hinv => ndR _ (by simp; omega) (by simp)⟩,
      fun hl1 d pr q ed ep eq => ?_⟩
    have hB1 : BitmapOK st s1 (L.cpu s1) (fun p => Q (L.cpu s) p ≠ []) := by
      rw [c1]
      refine (h0.ready _ hcC).2.agree ?_ fun g hg => ?_
      · unfold LawfulStore.l1W
        rw [nodeAt_of_ksb k1]
        exact hnode1 _ (by rw [l1Off_val]; omega) (by rw [l1Off_val]) (by rw [l1Off_val]; omega)
          (by rw [l1Off_val]; omega)
      · unfold LawfulStore.l2W
        rw [nodeAt_of_ksb k1]
        exact hnode1 _ (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega)
          (by rw [l2Off_val hg]; omega)
    have hne1 : L.l1W s1 (L.cpu s1) ≠ 0#u64 := by
      unfold LawfulStore.l1W
      rw [← eL1]
      exact hl1
    have hp : pr.val < 256 := by
      obtain ⟨q', hq', hq1, -, -⟩ :=
        spec_ex_fd (sched.highest_prio.spec (T := T) s1 d _ (by rw [c1]; exact hN.ksb k1) hB1 hne1)
      rw [hq'] at ep
      rw [← ok_inj_ff ep]
      exact hq1
    have eo : core.num.U64.wrapping_add q (core.num.U64.wrapping_mul pr 16#u64) = rqOff pr := by
      obtain ⟨off, hoff, ho1, -⟩ := spec_ex_fd (sched.rq_head_off.spec 0#u64 pr hp)
      unfold sched.rq_head_off at hoff
      simp only [rq_index_one, lift, bind_ok, eq] at hoff
      rw [← ho1]
      exact ok_inj_ff hoff
    have hov : (rqOff pr).val = 168 + 16 * pr.val := rqOff_val hp
    have hw : L.mem s1 (L.nodeAt s1 (L.cpu s1) (core.num.U64.wrapping_add q (core.num.U64.wrapping_mul pr 16#u64))) =
        (Q (L.cpu s) pr).headD 0#u64 := by
      rw [eo, e1N, hnode1 (rqOff pr) (by omega) (by omega) (by omega) (by omega),
        ← ((h0.ready _ hcC).1.rel pr hp).head]
      rfl
    rw [hw]
    exact ⟨by rw [eo, e1N]; exact nR (rqOff pr) (by omega) (by omega),
      (mayZ _ (headD_tz _ fun t ht => h0.memT hcC hp ht)).1⟩
  -- the due thread's tree links
  have lks := ctr.rep.links TM hk
  simp only [lk_l, lk_r, lk_p] at lks
  have mtr : L.mem s1 (trA TM) = L.mem s (trA TM) := mT (k := 3552#u64) q1 (by simp) (by simp)
  have mtp : L.mem s1 (tpA TM) = L.mem s (tpA TM) := mT (k := 3560#u64) q1 (by simp) (by simp)
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
    have mtl : L.mem s1 (tlA x) = L.mem s (tlA x) := mT (k := 3544#u64) (ctr.inT x hx) (by simp) (by simp)
    rw [eq_of_spec_fd (obj.Tcb.timer_left.val (L := L) s1 x), mtl] at ey
    have ey' := ok_inj_ff ey
    subst ey'
    exact hl.1.resolve_left hy0
  -- the tail: the due thread's bound notification
  have hTl : p.tm ≠ 0#u64 → fireTail (guard st R W) s1 (L.cpu s1) ct p = fireTail st s1 (L.cpu s1) ct p :=
    fun _ => fireTail.guardC (fun hn0 => by
      have hpN : p.ntfn = N := hpn.resolve_left hn0
      have hb0 : L.mem s (boundA TM) ≠ 0#u64 := by rw [eN, ← hpN]; exact hn0
      have hNN : N ∈ Nt := by rw [← eN]; exact hX.2.2.bnd _ q1 hb0
      have eBt : L.mem s (ntfnBtA N) = TM := by rw [← eN]; exact hX.2.2.bs.tb _ q1 hb0
      obtain ⟨p1, p2⟩ := hO.ntP _ hNN
      have eB : L.mem s (fld N 24#u64) = TM := by
        have eA : fld N 24#u64 = ntfnBtA N := by
          unfold fld ntfnBtA layout.ntfn.BOUND_TCB
          rfl
        rw [eA]; exact eBt
      have ht : K.heap TM = some .tcb := hK.tcbOf _ _ (hL.tcb _ q1 3328#u64 (by simp) (by simp))
      have ntR : ∀ k : U64, k.val < 64 → k.val % 8 = 0 → R (core.num.U64.wrapping_add N k) := fun k hk h8 => by
        refine hR _ ?_ (by unfold Aligned; rw [ntfn_word_val p1 p2 hk]; omega)
          (by rw [ntw _ hNN k hk]; intro e; cases e)
        have e : own K (L.mem s) (core.num.U64.wrapping_add N k) = ntfnOwner K (L.mem s) N k.val := by
          simp only [own, ntw _ hNN k hk]
          rw [ntfn_word_val p1 p2 hk, Nat.add_sub_cancel_left]
        by_cases h24 : k.val = 24
        · refine Or.inr ?_
          unfold GateOnly
          rw [e, ntfnOwner, if_pos h24]
        · refine Or.inl ?_
          rw [e, ntfnOwner, if_neg h24, eB, if_pos ht]
          exact ha
      rw [hpN, hpt]
      refine ⟨ntR layout.ntfn.TAIL_STATE (by simp [layout.ntfn.TAIL_STATE]) (by simp [layout.ntfn.TAIL_STATE]),
        ntR layout.ntfn.BOUND_TCB (by simp [layout.ntfn.BOUND_TCB]) (by simp [layout.ntfn.BOUND_TCB]),
        ntR layout.ntfn.HEAD (by simp [layout.ntfn.HEAD]) (by simp [layout.ntfn.HEAD]),
        by show R (stA TM); rw [stA_eq]; exact homeX q1 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) ha,
        ⟨(mayZ TM (Or.inr q1)).1, (mayZ TM (Or.inr q1)).2,
          ntR layout.ntfn.SC (by simp [layout.ntfn.SC]) (by simp [layout.ntfn.SC]), topC⟩, fun w ew => ?_⟩
      have ehd : obj.Ntfn.head st N s1 = ok (L.mem s1 (core.num.U64.wrapping_add N layout.ntfn.HEAD)) := by
        unfold obj.Ntfn.head
        simp only [lift, bind_ok, L.read_eq]
      rw [ehd, mN (k := layout.ntfn.HEAD) hNN (by simp [layout.ntfn.HEAD]) (by simp [layout.ntfn.HEAD])] at ew
      have ew' := ok_inj_ff ew
      subst ew'
      have htz : L.mem s (core.num.U64.wrapping_add N layout.ntfn.HEAD) = 0#u64 ∨
          L.mem s (core.num.U64.wrapping_add N layout.ntfn.HEAD) ∈ T := by
        obtain ⟨E, EQ, hEW⟩ := h0.eps
        have he : N ∈ E := (hEW.2.2.2.2.2.2.2.1 N).2 (Or.inr (hNt N hNN))
        obtain ⟨-, -, hq⟩ := hEW.1 N he
        have e : L.mem s (core.num.U64.wrapping_add N layout.ntfn.HEAD) = (EQ N).headD 0#u64 := by
          rw [← hq.head, ntfn_head_eq]
          rfl
        rw [e]
        exact headD_tz _ hq.mem
      exact ⟨(mayZ _ htz).1, (mayZ _ htz).2,
        ntR layout.ntfn.SC (by simp [layout.ntfn.SC]) (by simp [layout.ntfn.SC]), topC⟩)
  have g := fire_ok.guardK (gS := guard st R W) (s := s1) (ct := ct) (p := p) (now := now) (fun x => x ∈ tr.keys)
    (fun _ => by rw [hpt]; exact keyR hk (by simp) (by simp) (by simp))
    (fun _ => by rw [hpt]; exact keyR hk (by simp) (by simp) (by simp))
    hd1 hP0 hP (fun x hx => keyR hx (by simp) (by simp) (by simp)) hTl
  rwa [c1] at g


/-- **A declined `fire_ok` on the guarded store** (module docstring): `fire_rdG` at `R = MaxR`. -/
theorem fire_rd (hK : RegionOK K) {irq : U64} {s s1 : S} {lk : S → U64 → Prop} {W : U64 → Prop}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hL : StLay K st T Scs Z s) (hY : IrqLay K st Nt irq s)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (k1 : L.ksb s1 = L.ksb s) (c1 : L.cpu s1 = L.cpu s)
    (m1 : ∀ b, Aligned b → b ≠ ctA (L := L) s → b ≠ cnA (L := L) s → L.mem s1 b = L.mem s b)
    {tip p : localtimer.TimerIrqPlan} (etip : localtimer.plan_objects st s = ok tip)
    (esp : localtimer.same_plan tip p = ok true) (ct : obj.Tcb) (now : U64) :
    localtimer.fire_ok (guard st (MaxR K st lk s) W) s1 (L.cpu s) ct p now =
      localtimer.fire_ok st s1 (L.cpu s) ct p now :=
  fire_rdG hK hI hL hY.ntw (fun _ hp ha hr => ⟨hp, ha, hL.nu hr⟩) ⟨rperm_none hL.dom _, hL.domA, hL.domU⟩ hNt k1 c1
    m1 etip esp ct now

end own

end Fl4Proofs.P2
