/-
# P2 (line p3mc, gen 24): the timer interrupt at a homed earliest thread, generic pieces

Handoff §27b item 3(a), the fire case whose signal wakes nobody (`NoWake`), on a generic guarded store whose read set
holds only the fire case's own reads (`FireRd`), not `MaxR`:

* **`fireTail.guardNW`**: `fireTail` (`fire_ok`'s notification check) on `gS` as on `st` reading only the
  notification's `TAIL_STATE` / `BOUND_TCB` and the due thread's `STATE`, when the notification is not waiting and,
  if idle, its bound thread is null or not blocked on receive (`fireTail.guardC` asked `wake_ok`'s reads, which may
  be another core's thread: a waiting notification's head);
* **`fire_ok_guardNW`**: `fire_ok` after the timestamp on any `gS` answering `FireRd` (`fire_rdG`'s walk with the
  tree keys' timer words from `FTree`, the notification words from `FNt`, the due thread's `STATE` from `TmWords`);
* **`irq_pl_guard`**: the whole run on `gS` answering the IRQ word, `TIMER_MIN` and `PlanTm` (`plan_objects.guard`)
  is the real one, given the tail on `gS` (as gen 23's `irq_fh_guard2`, for any earliest thread);
* **`irq_acc_fire_nwG`**: an accepted fire-case run whose signal wakes nobody, on any `gS` answering `FireRd` /
  `FireWr` and the tree's height writes, the deadline write asked **only for the due thread**
  (`irq_accG_fire_pre` with `fire_ok_guardNW` and `GED.fire_tail_nwD`).

No named premises; no existing statement changed.
-/
import Fl4Proofs.P2.IrqFireD
import Fl4Proofs.P2.FootTimerFireOwn
import Fl4Proofs.P2.IrqTailR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.Serial (Owner)
open Fl4Proofs.P2.OwnMap
open Fl4Proofs.P2.PathObl (guard RPerm WPerm HeldBy GateOnly bind_guard_congr irqTailF tr_bind_same tr_ite)

section g
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R : U64 → Prop}
variable {gS : machine.Store S} [PathObl.GRd gS st R]

/-- **`fireTail` on the guarded store when the notification wakes nobody** (module docstring). -/
theorem fireTail.guardNW {s : S} {ct : obj.Tcb} {p : localtimer.TimerIrqPlan}
    (h : p.ntfn ≠ 0#u64 → R (core.num.U64.wrapping_add p.ntfn layout.ntfn.TAIL_STATE) ∧
      R (core.num.U64.wrapping_add p.ntfn layout.ntfn.BOUND_TCB) ∧
      R (core.num.U64.wrapping_add p.tm layout.tcb.STATE))
    (hNW : p.ntfn ≠ 0#u64 → L.epState s p.ntfn ≠ obj.NTFN_WAITING ∧ (L.epState s p.ntfn = obj.NTFN_IDLE →
      L.mem s (ntfnBtA p.ntfn) = 0#u64 ∨ L.mem s (stA (L.mem s (ntfnBtA p.ntfn))) ≠ sched.TS_BLOCKED_ON_RECV)) :
    fireTail gS s (L.cpu s) ct p = fireTail st s (L.cpu s) ct p := by
  unfold fireTail
  by_cases h0 : p.ntfn = 0#u64
  · rw [if_pos h0, if_pos h0]
  obtain ⟨h1, h2, h3⟩ := h h0
  obtain ⟨nw, ni⟩ := hNW h0
  rw [if_neg h0, if_neg h0, ntfn_state_guard p.ntfn s h1]
  refine bind_guard_congr rfl fun x ex => ?_
  rw [eq_of_spec_fd (obj.Ntfn.state.spec (L := L) s _)] at ex
  have ex' : L.epState s p.ntfn = x := ok_inj_ff ex
  by_cases ha : x = obj.NTFN_ACTIVE
  · rw [if_pos ha, if_pos ha]
  rw [if_neg ha, if_neg ha]
  by_cases hi : x = obj.NTFN_IDLE
  · rw [if_pos hi, if_pos hi, PathObl.obj.Ntfn.bound_tcb.guard (gS := gS) p.ntfn s h2]
    refine bind_guard_congr rfl fun b2 eb2 => ?_
    rw [eq_of_spec_fd (obj.Ntfn.bound_tcb.val (L := L) s _)] at eb2
    have eb2' : L.mem s (ntfnBtA p.ntfn) = b2 := ok_inj_ff eb2
    by_cases hz : b2 = 0#u64
    · rw [if_pos hz, if_pos hz]
    rw [if_neg hz, if_neg hz]
    by_cases hn : (b2 != p.tm) = true
    · rw [if_pos hn, if_pos hn]
    have e : b2 = p.tm := by by_contra hne; exact hn (bne_iff_ne.mpr hne)
    rw [if_neg hn, if_neg hn, PathObl.obj.Tcb.state.guard (gS := gS) p.tm s h3]
    refine bind_guard_congr rfl fun bs ebs => ?_
    rw [eq_of_spec_fd (obj.Tcb.state.spec (L := L) s _)] at ebs
    have ebs' : L.mem s (stA p.tm) = bs := ok_inj_ff ebs
    by_cases hv : bs = sched.TS_RUNNING_VM
    · rw [if_pos hv, if_pos hv]
    rw [if_neg hv, if_neg hv]
    by_cases hr : bs = sched.TS_BLOCKED_ON_RECV
    · exfalso
      rcases ni (ex'.trans hi) with h' | h'
      · exact hz (eb2'.symm.trans h')
      · apply h'
        rw [eb2', e, ebs']
        exact hr
    · rw [if_neg hr, if_neg hr]
  · rw [if_neg hi, if_neg hi]
    by_cases hw : x = obj.NTFN_WAITING
    · exact absurd (ex'.trans hw) nw
    rw [if_neg hw, if_neg hw]

end g

section own
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}

set_option maxHeartbeats 32000000 in
/-- **`fire_ok` after the timestamp on a store answering `FireRd`, the signal waking nobody** (module docstring). -/
theorem fire_ok_guardNW {R : U64 → Prop} {gS : machine.Store S} [PathObl.GRd gS st R] {s s1 : S}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hL : StLay K st T Scs Z s)
    (ntw : ∀ n ∈ Nt, ∀ k : U64, k.val < 64 → region K (core.num.U64.wrapping_add n k) = .ntfn n)
    (gRd : ∀ w, Aligned w → FireRd st T Z s w → R w) (hNW : NoWake st s)
    (k1 : L.ksb s1 = L.ksb s) (c1 : L.cpu s1 = L.cpu s)
    (m1 : ∀ b, Aligned b → b ≠ ctA (L := L) s → b ≠ cnA (L := L) s → L.mem s1 b = L.mem s b)
    {tip p : localtimer.TimerIrqPlan} (etip : localtimer.plan_objects st s = ok tip)
    (esp : localtimer.same_plan tip p = ok true) (ct : obj.Tcb) (now : U64) :
    localtimer.fire_ok gS s1 (L.cpu s) ct p now = localtimer.fire_ok st s1 (L.cpu s) ct p now := by
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
  -- the tree keys' timer words are `FTree`'s
  have keyR : ∀ {y k : U64}, y ∈ tr.keys → 3528 ≤ k.val → k.val < 3576 → k.val % 8 = 0 →
      R (core.num.U64.wrapping_add y k) := @fun y k hy h1 h2 h3 => by
    have hyT := ctr.inT y hy
    exact gRd _ (field_aligned (hT _ hyT) (by omega) h3)
      (Or.inr (Or.inl ⟨y, hyT, ⟨ctr.armed y hy, ctr.core y hy⟩, k, h1, h2, h3, rfl⟩))
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
  -- the tail: the due thread's bound notification, waking nobody
  unfold NoWake at hNW
  rw [eTM, eN] at hNW
  have hTl : p.tm ≠ 0#u64 → fireTail gS s1 (L.cpu s1) ct p = fireTail st s1 (L.cpu s1) ct p := by
    intro _
    by_cases hn0 : p.ntfn = 0#u64
    · exact fireTail.guardNW (fun h => absurd hn0 h) (fun h => absurd hn0 h)
    have hpN : p.ntfn = N := hpn.resolve_left hn0
    have hb0 : L.mem s (boundA TM) ≠ 0#u64 := by rw [eN, ← hpN]; exact hn0
    have hNN : N ∈ Nt := by rw [← eN]; exact hX.2.2.bnd _ q1 hb0
    have eBt : L.mem s (ntfnBtA N) = TM := by rw [← eN]; exact hX.2.2.bs.tb _ q1 hb0
    obtain ⟨p1, p2⟩ := hO.ntP _ hNN
    have hN0 : N ≠ 0#u64 := by rw [← eN]; exact hb0
    have ntR : ∀ k : U64, k.val < 64 → k.val % 8 = 0 → R (core.num.U64.wrapping_add N k) := fun k hk h8 =>
      gRd _ (by unfold Aligned; rw [ntfn_word_val p1 p2 hk]; omega)
        (Or.inr (Or.inr ⟨by rw [eTM]; exact hne, by rw [eTM, eN]; exact hN0, k, hk, h8, by rw [eTM, eN]⟩))
    have stR : R (stA TM) := by
      rw [stA_eq]
      exact gRd _ (field_aligned (hT _ q1) (by simp) (by simp))
        (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by rw [eTM]; exact hne,
          Or.inr ⟨by rw [eTM]; exact hh, Or.inl ⟨3328#u64, Or.inl (by simp), by rw [eTM]⟩⟩⟩))))))
    have eS : L.epState s1 N = L.epState s N := by
      unfold LawfulStore.epState epTSA
      rw [mN (k := layout.ep.TAIL_STATE) hNN (by simp [layout.ep.TAIL_STATE]) (by simp [layout.ep.TAIL_STATE])]
    have eB : L.mem s1 (ntfnBtA N) = L.mem s (ntfnBtA N) := by
      unfold ntfnBtA
      exact mN (k := layout.ntfn.BOUND_TCB) hNN (by simp [layout.ntfn.BOUND_TCB]) (by simp [layout.ntfn.BOUND_TCB])
    have eSt : L.mem s1 (stA TM) = L.mem s (stA TM) := by
      rw [stA_eq]; exact mT (k := 3328#u64) q1 (by simp) (by simp)
    refine fireTail.guardNW (fun _ => ?_) (fun _ => ?_)
    · rw [hpN, hpt]
      exact ⟨ntR layout.ntfn.TAIL_STATE (by simp [layout.ntfn.TAIL_STATE]) (by simp [layout.ntfn.TAIL_STATE]),
        ntR layout.ntfn.BOUND_TCB (by simp [layout.ntfn.BOUND_TCB]) (by simp [layout.ntfn.BOUND_TCB]), stR⟩
    · rw [hpN, eS, eB, eBt, eSt]
      rcases hNW with h' | ⟨hi, hw⟩ | ⟨hi, hb⟩
      · exact absurd h' hN0
      · exact ⟨hw, fun h' => absurd h' hi⟩
      · refine ⟨by rw [hi]; simp [obj.NTFN_IDLE, obj.NTFN_WAITING], fun _ => ?_⟩
        rcases hb with h' | h'
        · exact Or.inl (eBt.symm.trans h')
        · rw [eBt] at h'; exact Or.inr h'
  have g := fire_ok.guardK (gS := gS) (s := s1) (ct := ct) (p := p) (now := now) (fun x => x ∈ tr.keys)
    (fun _ => by rw [hpt]; exact keyR hk (by simp) (by simp) (by simp))
    (fun _ => by rw [hpt]; exact keyR hk (by simp) (by simp) (by simp))
    hd1 hP0 hP (fun x hx => keyR hx (by simp) (by simp) (by simp)) hTl
  rwa [c1] at g

end own

section guard
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {R : U64 → Prop} {gS : machine.Store S} [PathObl.GRd gS st R] {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **The whole run on a store answering the head's reads, given the tail** (module docstring). -/
theorem irq_pl_guard {s : S} {a : A} {irq : U64} {p : localtimer.TimerIrqPlan} {r : Bool × S × A}
    (hi : irq.val < 128 → ∀ i, interrupt.state_off irq = ok i → R (core.num.U64.wrapping_add (L.ksb s) i))
    (h1 : R (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))
    (h2 : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64 →
      PlanTm st R s (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))
    (htail : ∀ mx, layout.irq.MAX = ok mx → ¬ irq > mx →
      interrupt.irq_state st s irq = ok interrupt.IRQ_TIMER → ∀ tip, localtimer.plan_objects st s = ok tip →
      localtimer.same_plan tip p = ok true →
      irqTailF st ar s a irq (L.cpu s) p = ok r → irqTailF gS ar s a irq (L.cpu s) p = ok r)
    (h : localtimer.handle_timer_irq_local st ar s a irq p = ok r) :
    localtimer.handle_timer_irq_local gS ar s a irq p = ok r := by
  have hpl := plan_objects.guard (gS := gS) h1 h2
  revert h
  rw [irq_splitF st, irq_splitF gS, PathObl.gst_cur_cpu (g := gS), L.cur_cpu_eq]
  simp only [bind_ok, num_domains_ne_one_false, Bool.false_eq_true, ↓reduceIte]
  refine tr_bind_same (fun mx emx => ?_)
  refine tr_ite (fun _ h => h) (fun hle => ?_)
  have hlt : irq.val < 128 := by
    rw [eq_of_spec_fd layout.irq.MAX.spec] at emx
    have e := ok_inj_ff emx
    subst e
    scalar_tac
  have eirq : interrupt.irq_state gS s irq = interrupt.irq_state st s irq := by
    unfold interrupt.irq_state
    exact bind_guard_congr rfl fun i ei => PathObl.obj.ks_get.guard (gS := gS) s i (hi hlt i ei)
  rw [eirq]
  refine tr_bind_same (fun i1 ei1 => ?_)
  refine tr_ite (fun _ h => h) (fun hi1 => ?_)
  have e1 : i1 = interrupt.IRQ_TIMER := by
    by_contra hne
    exact hi1 (bne_iff_ne.mpr hne)
  subst e1
  rw [hpl]
  refine tr_bind_same (fun tip etip => ?_)
  refine tr_bind_same (fun b eb => ?_)
  refine tr_ite (fun hb => ?_) (fun _ h => h)
  subst hb
  exact htail mx emx hle ei1 tip etip eb

end guard

section acc
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 8000000 in
/-- **An accepted fire-case run waking nobody, on a store answering `FireRd` / `FireWr`** (module docstring). -/
theorem irq_acc_fire_nwG {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
    (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {irq : U64} {p : localtimer.TimerIrqPlan}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hL : StLay K st T Scs Z s)
    (ntw : ∀ n ∈ Nt, ∀ k : U64, k.val < 64 → region K (core.num.U64.wrapping_add n k) = .ntfn n)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (hq : IrqFire st ar s a) (hNW : NoWake st s)
    (gRd : IrqOk st s → ∀ w, Aligned w → FireRd st T Z s w → R w)
    (gWr : IrqOk st s → ∀ w, Aligned w → FireWr st T Z s w → w ≠ stA (L.curW s) → W w)
    (hIq : IrqOk st s → ∀ i, interrupt.state_off irq = ok i → R (core.num.U64.wrapping_add (L.ksb s) i))
    (hD1 : IrqOk st s → R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hD2 : IrqOk st s → R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME))
    (hwS : IrqOk st s → ∀ X, L.mem X (stA (L.curW s)) = sched.TS_RESTART → L.mem X (affA (L.curW s)) = L.cpu s →
      gS.write X (stA (L.curW s)) sched.TS_RUNNING = st.write X (stA (L.curW s)) sched.TS_RUNNING)
    (hwH : ∀ X y v, y ∈ T → FootLtArmed st s (L.cpu s) y →
      (L.mem X (tdA y) ≠ 0#u64 → (L.mem X (thA y)).val >>> 8 = (L.cpu s).val ∧ v.val >>> 8 = (L.cpu s).val) →
      gS.write X (thA y) v = st.write X (thA y) v)
    (hwD : ∀ X y v, y ∈ T → FootLtArmed st s (L.cpu s) y →
      y = L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) → L.mem X (affA y) = L.cpu s →
      L.mem s (affA y) = L.cpu s →
      (L.mem X (tdA y) ≠ 0#u64 ∨ v ≠ 0#u64 → (L.mem X (thA y)).val >>> 8 = (L.cpu s).val) →
      gS.write X (tdA y) v = st.write X (tdA y) v)
    (h : localtimer.handle_timer_irq_local st ar s a irq p = ok (true, s', a')) :
    localtimer.handle_timer_irq_local gS ar s a irq p = ok (true, s', a') := by
  have h0 := hI.1.choose_spec.choose_spec
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ h0.cur
  obtain ⟨mx, now, i2, tip, x, s1, s2, s3, a1, a2, a3, emx, hle, ei1, etip, eb, eok, eq, eu, enow, erel, ei2, eb4,
    edue, efo, ecb, ehi⟩ := fire_eqs ar hA hq h
  refine irq_accG_fire_pre (gS := gS) (R := R) (W := W) ar hA hI hq
    (fun hok w ha hw => gRd hok w ha (Or.inl hw)) (fun hok w ha hw hn => gWr hok w ha (Or.inl hw) hn)
    hIq hD1 hD2 ?_ ?_ h
  · intro hok s1' a1' now' eu' _
    obtain ⟨n1, -, er⟩ := ut_now ar hA hN eu'
    simp only at er
    exact fire_ok_guardNW hI hL ntw (gRd hok) hNW (by rw [er, utW_ksb]) (by rw [er, utW_cpu])
      (fun b hb h1 h2 => by rw [er]; exact utW_mem hN n1 hb h1 h2) etip eb _ _
  · intro hok s1' a1' x' s2' a2' s3' a3' now' eu' enow' efo' ecb' ehi'
    rw [eu] at eu'
    have e1 := ok_inj_ff eu'
    simp only [Prod.mk.injEq] at e1
    obtain ⟨rfl, rfl⟩ := e1
    rw [enow] at enow'
    obtain rfl := ok_inj_ff enow'
    exact GED.fire_tail_nwD (gS := gS) (R := R) (W := W) ar hA hI hNt hok (gRd hok)
      (fun w ha hw hn => gWr hok w ha hw hn) (hD2 hok) (hwS hok) hwH hwD
      hNW etip eb eq eok eu enow erel ei2 eb4 edue efo' ecb' emx hle ei1 ehi'

end acc

end Fl4Proofs.P2
