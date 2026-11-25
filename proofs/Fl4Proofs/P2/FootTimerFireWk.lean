/-
# P2 (p2lf): a fired timer's signal that wakes a thread, on the guarded store

The two `send_signal` branches `fire_ok` accepts that wake a thread `w` (`P2/FootTimerFireSig`): a `WAITING`
notification `n` (its queue head, `ntfn_dequeue`) and an idle one whose bound thread waits in `Recv` (`cancel_ipc`).

* `wakeTail.gw`: `wakeTail.guard` (`P2/FootTimerFireW`) with the woken thread's `STATE` write answered as `st`'s at
  the one state it happens in (as `set_thread_state.gw`), not at every state (`SWr`): the move store (`gd`) answers
  it only where the write is a legal step.
* `WkPre.agree`: `wakeTail`'s state facts carry to a state agreeing on the words they read.
* `wake_wait_guard`: the `WAITING` branch of `send_signal` on `gS` is its real run, from facts at its start state
  `X` only: P1's queue invariant at `X` (`SchedQueuesInvX`, `EpsWit`: the notification's queue and its members),
  the queue words and the head's links (and its successor's `EP_PREV`) read / written, `wakeTail`'s facts at `X`
  (`WkPre` at `X`; `ntfn_dequeue` writes only the queue's links and the notification's queue words,
  `epfoot_keep`), and the head's `STATE` write `RUNNING` at the state after the dequeue.
* `wake_recv_guard`: the idle-bound branch whose bound thread `t` waits in `Recv` on `ep` with reply `r`: the guarded
  `cancel_ipc` (`ipc.cancel_ipc.guard_recv`: fault word, `ep_dequeue`, `reply_unlink`, `INACTIVE`) and `wakeTail`
  are the real runs from facts at `X` (`cancel_recv_st`: the `st` run step by step; `CnD`: what it writes; the two
  `STATE` writes answered as `st`'s at the states `CnD` writes reach; `hRt`: the reply's `TCB` word is none of the
  words read later).

No named premises.
-/
import Fl4Proofs.P2.FootTimerFireNw
import Fl4Proofs.P2.FootTimerFireC
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (bind_guard_congr NodeSt ScAcc)

section gst
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]

set_option maxHeartbeats 4000000 in
/-- **`wakeTail` on the guarded store, the `STATE` write at its state** (module docstring). -/
theorem wakeTail.gw {A : Type} (ar : machine.Arch A) (X : S) (a : A) (w n badge : U64) {sb : Nat}
    (hcur : w ≠ L.curW X) (hn : NodeSt (L := L) R W X)
    (aS : Aligned (stA w)) (aR : Aligned (regA w layout.reg.BADGE)) (nSR : stA w ≠ regA w layout.reg.BADGE)
    (aA : Aligned (L.nodeAt X (L.cpu X) layout.node.SCHED_ACTION))
    (nA1 : L.nodeAt X (L.cpu X) layout.node.SCHED_ACTION ≠ stA w)
    (nA2 : L.nodeAt X (L.cpu X) layout.node.SCHED_ACTION ≠ regA w layout.reg.BADGE)
    (aC : Aligned (L.nodeAt X (L.cpu X) layout.node.CUR_THREAD))
    (nC1 : L.nodeAt X (L.cpu X) layout.node.CUR_THREAD ≠ stA w)
    (rS : R (stA w)) (wS : gS.write X (stA w) sched.TS_RUNNING = st.write X (stA w) sched.TS_RUNNING)
    (rSc : R (scA w)) (rI : R (inqA w))
    (rD : R (domA w)) (rA : R (affA w)) (wB : W (regA w layout.reg.BADGE))
    (hac : L.actionW X = sched.ACTION_RESUME_CURRENT)
    (hY : ∀ Y, WritesIn st X Y (WkD st X w) → WkPre st R W Y w n sb) :
    wakeTail gS ar X a w n badge = wakeTail st ar X a w n badge := by
  have wi2 : WritesIn st X (L.wr X (stA w) sched.TS_RUNNING) (WkD st X w) :=
    ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun b hb hb' => mem_wr_ne' aS hb (fun e => hb' (Or.inl e.symm))⟩
  have hc2 : L.curW (L.wr X (stA w) sched.TS_RUNNING) = L.curW X := by
    unfold LawfulStore.curW
    rw [nodeAt_wr, L.cpu_wr]
    exact mem_wr_ne' aS aC (Ne.symm nC1)
  have hst2 : sched.set_thread_state st X w sched.TS_RUNNING = ok (L.wr X (stA w) sched.TS_RUNNING) := by
    unfold sched.set_thread_state
    rw [PathObl.set_state_ok']
    simp only [bind_ok]
    unfold sched.schedule_tcb
    rw [cur_thread_ok, hc2]
    simp only [bind_ok]
    rw [eq_of_spec_fd (tcb_eq.blk w (L.curW X))]
    simp only [bind_ok, hcur, decide_false, Bool.false_eq_true, ↓reduceIte]
  unfold wakeTail
  rw [set_thread_state.gwC (gS := gS) X w _ hn wS rS rSc (hY _ wi2).mx rI, hst2]
  simp only [bind_ok]
  rw [PathObl.obj.Tcb.set_reg.guard (gS := gS) w _ _ _ wB, PathObl.set_reg_ok']
  simp only [bind_ok]
  have wi3 : WritesIn st X (L.wr (L.wr X (stA w) sched.TS_RUNNING) (regA w layout.reg.BADGE) badge)
      (WkD st X w) :=
    ⟨by rw [L.ksb_wr, L.ksb_wr], by rw [L.cpu_wr, L.cpu_wr], fun b hb hb' => by
      rw [mem_wr_ne' aR hb (fun e => hb' (Or.inr (Or.inl e.symm)))]
      exact wi2.2.2 b hb hb'⟩
  have P3 := hY _ wi3
  obtain ⟨m1, m2⟩ := notification.maybe_donate_sched_context.guard_nd (gS := gS) ar
    (L.wr (L.wr X (stA w) sched.TS_RUNNING) (regA w layout.reg.BADGE) badge) a w n rSc P3.nsc P3.nd
  rw [m1, m2]
  simp only [bind_ok, Aeneas.Std.uncurry_apply_pair]
  rw [sched.is_schedulable.guardC (gS := gS) _ w rS rSc P3.mx rI]
  refine bind_guard_congr rfl fun b _ => ?_
  have hac3 : L.actionW (L.wr (L.wr X (stA w) sched.TS_RUNNING) (regA w layout.reg.BADGE) badge) =
      sched.ACTION_RESUME_CURRENT := by
    unfold LawfulStore.actionW
    rw [nodeAt_wr, nodeAt_wr, L.cpu_wr, L.cpu_wr, mem_wr_ne' aR aA (Ne.symm nA2), mem_wr_ne' aS aA (Ne.symm nA1)]
    exact hac
  have hn3 := NodeSt.of_wi hn wi3
  refine bind_guard_congr ?_ fun s5 h5 => ?_
  · by_cases hb : b = true
    · rw [if_pos hb, if_pos hb]
      exact sched.possible_switch_to.guard_here (gS := gS) _ w hn3 rSc rI P3.cd rD rA P3.dom P3.aff hac3
    · rw [if_neg hb, if_neg hb]
  · have wi5 : WritesIn st X s5 (WkD st X w) := by
      by_cases hb : b = true
      · rw [if_pos hb] at h5
        rcases possible_switch_to_here_st _ w P3.dom P3.aff hac3 with e | e
        · rw [e] at h5; rw [← ok_inj_ff h5]; exact wi3
        · rw [e] at h5
          rw [← ok_inj_ff h5]
          refine ⟨by rw [L.ksb_wr]; exact wi3.1, by rw [L.cpu_wr]; exact wi3.2.1, fun c hc hc' => ?_⟩
          rw [nodeAt_wr, nodeAt_wr, L.cpu_wr, L.cpu_wr, mem_wr_ne' aA hc (fun e => hc' (Or.inr (Or.inr e.symm)))]
          exact wi3.2.2 c hc hc'
      · rw [if_neg hb] at h5; rw [← ok_inj_ff h5]; exact wi3
    have P5 := hY s5 wi5
    rw [notification.unblock_sporadic.guard (gS := gS) s5 w rSc P5.sp P5.cs P5.acc P5.wf P5.rep P5.ct P5.rp]

end gst

section agree
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}

/-- **`wakeTail`'s state facts at an agreeing state** (module docstring). -/
theorem WkPre.agree {X Y : S} {w n : U64} {sb : Nat} (P : WkPre st R W X w n sb)
    (k : L.ksb Y = L.ksb X) (c : L.cpu Y = L.cpu X)
    (e1 : L.mem Y (scA w) = L.mem X (scA w)) (e2 : L.mem Y (ntfnScA n) = L.mem X (ntfnScA n))
    (e3 : L.mem Y (domA w) = L.mem X (domA w))
    (e4 : L.mem Y (core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN) =
      L.mem X (core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN))
    (e5 : L.mem Y (affA w) = L.mem X (affA w))
    (e6 : L.mem X (scA w) ≠ 0#u64 → ∀ b, Aligned b → InSC (L.mem X (scA w)) sb b → L.mem Y b = L.mem X b) :
    WkPre st R W Y w n sb := by
  have hN : ∀ o, L.nodeAt Y (L.cpu Y) o = L.nodeAt X (L.cpu X) o := fun o => by rw [c, nodeAt_of_ksb k]
  have hNA : ∀ o, L.nodeA Y o = L.nodeA X o := fun o => hN o
  obtain ⟨mx, nsc, nd, dom, aff, sp, acc, wf, rep, ct, rp, cs, cd⟩ := P
  refine ⟨fun h => by rw [e1] at h ⊢; exact mx h, fun h => nsc (by rw [← e1]; exact h),
    fun h => by rw [e2]; exact nd (by rw [← e1]; exact h),
    by rw [e3, k, e4]; exact dom, by rw [e5, c]; exact aff, fun h => by rw [e1] at h ⊢; exact sp h,
    fun h => by rw [e1] at h ⊢; exact acc h, fun h => by rw [e1] at h ⊢; exact (wf h).agree (e6 h),
    fun h => by rw [hNA, e1]; rw [e1] at h; exact rep h, ?_, by rw [hNA]; exact rp, by rw [hN]; exact cs,
    by rw [k]; exact cd⟩
  show R (L.nodeAt Y (L.cpu Y) layout.node.CUR_TIME)
  rw [hN]; exact ct

end agree

section wait
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
variable {T Cs Ω : Set U64} {H : Heap}

theorem ntfn_waiting_ne_idle : obj.NTFN_WAITING ≠ obj.NTFN_IDLE := by
  unfold obj.NTFN_WAITING obj.NTFN_IDLE; decide

set_option maxHeartbeats 8000000 in
/-- **The `WAITING` branch of a fired timer's `send_signal` on the guarded store** (module docstring): `w` the
queue's head at `X`. -/
theorem wake_wait_guard {A : Type} (ar : machine.Arch A) (X : S) (a : A) (n badge w : U64) {sb : Nat}
    {Xs E : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {EQ : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H Xs X Q Rq) (hEW : EpsWit st T Cs Ω H Xs X E EQ) (he : n ∈ E)
    (hwt : L.epState X n = obj.NTFN_WAITING) (hwq : (L.epQ X n).head = w) (hmem : w ∈ EQ n)
    (r1 : R (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE))
    (rH : R (core.num.U64.wrapping_add n layout.ntfn.HEAD))
    (wT : W (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE))
    (wH : W (core.num.U64.wrapping_add n layout.ntfn.HEAD)) (aB : Aligned (ntfnBdA n))
    (rP : R (prevA .Ep w)) (rN : R (nextA .Ep w)) (wP : W (prevA .Ep w)) (wN : W (nextA .Ep w))
    (wPn : (L.epQ X n).end ≠ w → W (prevA .Ep (L.mem X (nextA .Ep w))))
    (hcur : w ≠ L.curW X) (hn : NodeSt (L := L) R W X)
    (rS : R (stA w)) (rSc : R (scA w)) (rI : R (inqA w)) (rD : R (domA w)) (rA : R (affA w))
    (wB : W (regA w layout.reg.BADGE)) (hac : L.actionW X = sched.ACTION_RESUME_CURRENT)
    (wS : ∀ Y, WritesIn st X Y (EpFoot (EQ n) n) →
      gS.write Y (stA w) sched.TS_RUNNING = st.write Y (stA w) sched.TS_RUNNING)
    (P : WkPre st R W X w n sb) (hnsΩ : ntfnScA n ∈ Ω)
    (hscΩ : L.mem X (scA w) ≠ 0#u64 → ∀ b, Aligned b → InSC (L.mem X (scA w)) sb b → b ∈ Ω) :
    notification.send_signal gS ar X a n badge = notification.send_signal st ar X a n badge := by
  obtain ⟨hE, hEN, hq⟩ := hEW.1 n he
  have hT := h.tcbs
  have hw : w ∈ T := hq.mem w hmem
  have ht' := hT w hw
  have hcC := h.cur
  have hN : NodePlaced st T X (L.cpu X) := h.nodes _ hcC
  refine notification.send_signal.guardF (gS := gS) ar X a n badge r1 (ep_aligned hE).2 aB
    (fun _ h2 => absurd hwt h2) (fun h1 => absurd (hwt.symm.trans h1) ntfn_waiting_ne_idle) (fun _ => ?_)
  rw [hwq]
  refine ⟨rH, ?_, fun X1 hX1 => ?_⟩
  · refine notification.ntfn_dequeue.guard (gS := gS) X n w rH r1 wH wT fun q hq' => ?_
    rw [eq_of_spec_fd (notification.get_queue.spec (L := L) X n)] at hq'
    have eq' := ok_inj_ff hq'
    subst eq'
    exact tcbqueue.remove.guardL (gS := gS) X .Ep _ w rP rN (fun hE' => wPn hE')
      (fun hH => absurd hwq hH) wN wP
  -- the state after the dequeue
  have wi : WritesIn st X X1 (EpFoot (EQ n) n) := by
    have := notification.ntfn_dequeue.foot (st := st) X n w (EQ n) hT hE hq hmem
    rw [hX1, WP.spec_ok] at this
    exact this
  obtain ⟨kT, kΩ, kN⟩ := epfoot_keep h hEW he (fun y hy => hq.mem y hy) wi
  have k1 : L.ksb X1 = L.ksb X := wi.1
  have c1 : L.cpu X1 = L.cpu X := wi.2.1
  have e1N : ∀ o, L.nodeAt X1 (L.cpu X1) o = L.nodeAt X (L.cpu X) o := fun o => by rw [c1, nodeAt_of_ksb k1]
  have hN1 : NodePlaced st T X1 (L.cpu X1) := by rw [c1]; exact hN.ksb k1
  have hbv : layout.reg.BADGE.val = 0 := by unfold layout.reg.BADGE layout.reg.RDI; rfl
  obtain ⟨KB, hKB, eKB⟩ := regA_eq ht' (r := layout.reg.BADGE) (by rw [hbv]; omega)
  have hKB' : KB.val = 256 := by rw [hKB, hbv]
  have aS : Aligned (stA w) := by rw [stA_eq]; exact field_aligned ht' (by simp) (by simp)
  have aR : Aligned (regA w layout.reg.BADGE) := by
    rw [eKB]; exact field_aligned ht' (by omega) (by rw [hKB]; omega)
  have nSR : stA w ≠ regA w layout.reg.BADGE := by
    rw [stA_eq, eKB]; exact tcb_word_ne ht' ht' (by simp) (by omega) (fun _ h => by simp at h; omega)
  have aA : Aligned (L.nodeAt X1 (L.cpu X1) layout.node.SCHED_ACTION) :=
    nodeAt_aligned hN1 (by rw [act_val]; omega) (by rw [act_val])
  have aC : Aligned (L.nodeAt X1 (L.cpu X1) layout.node.CUR_THREAD) :=
    nodeAt_aligned hN1 (by rw [curth_val]; omega) (by rw [curth_val])
  have nF : ∀ o K : U64, o.val < 4288 → K.val < 4096 → L.nodeAt X1 (L.cpu X1) o ≠ core.num.U64.wrapping_add w K :=
    fun o K ho hK => node_ne_field hN1 ho hw ht' hK
  -- the words `wakeTail` reads keep their values along `WkD` writes after the dequeue
  have notWk : ∀ (Y : S) (b : U64), WritesIn st X1 Y (WkD st X1 w) → Aligned b → b ≠ stA w →
      b ≠ regA w layout.reg.BADGE → b ≠ L.nodeAt X1 (L.cpu X1) layout.node.SCHED_ACTION → L.mem Y b = L.mem X1 b :=
    fun Y b wY hb h1 h2 h3 => wY.mem_eq hb (by rintro (e | e | e) <;> [exact h1 e; exact h2 e; exact h3 e])
  have tK : ∀ (Y : S) (K : U64), WritesIn st X1 Y (WkD st X1 w) → K.val < 4096 → K.val % 8 = 0 →
      K.val ≠ 3496 → K.val ≠ 3504 → K.val ≠ 3328 → K.val ≠ KB.val →
      L.mem Y (core.num.U64.wrapping_add w K) = L.mem X (core.num.U64.wrapping_add w K) := by
    intro Y K wY hK h8 h1 h2 h3 h4
    rw [notWk Y _ wY (field_aligned ht' hK h8)
      (by rw [stA_eq]; exact tcb_word_ne ht' ht' hK (by simp) (fun _ e => h3 (by rw [e]; rfl)))
      (by rw [eKB]; exact tcb_word_ne ht' ht' hK (by omega) (fun _ => h4))
      (fun e => nF _ K (by rw [act_val]; omega) hK e.symm)]
    exact kT w hw K hK h8 h1 h2
  have oK : ∀ (Y : S) (b : U64), WritesIn st X1 Y (WkD st X1 w) → b ∈ Ω → L.mem Y b = L.mem X b := by
    intro Y b wY hb
    have ho := h.omega b hb
    have ho1 : OutsideObjs st T Cs X1 b := ho.ksb k1
    rw [notWk Y b wY ho.1 (fun e => out_ne_field ho1 hw ht' (K := 3328#u64) (by simp) (by rw [← stA_eq, e]))
      (fun e => out_ne_field ho1 hw ht' (K := KB) (by omega) (by rw [← eKB, e]))
      (fun e => out_ne_node ho1 (by rw [c1]; exact hcC) hN1 (o := layout.node.SCHED_ACTION) (by rw [act_val]; omega)
        (by rw [e]))]
    exact kΩ b hb
  have hcdv : layout.ks.CUR_DOMAIN.val = 8 := by simp [layout.ks.CUR_DOMAIN]
  have cdK : ∀ (Y : S), WritesIn st X1 Y (WkD st X1 w) →
      L.mem Y (core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN) =
        L.mem X (core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN) := by
    intro Y wY
    have hv : (core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN).val = (L.ksb X).val + 8 := by
      rw [ks_word_val hN (by rw [hcdv]; omega), hcdv]
    have ha : Aligned (core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN) :=
      ks_aligned hN (by rw [hcdv]; omega) (by rw [hcdv])
    have tne : ∀ y K, y ∈ T → K.val < 4096 →
        core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN ≠ core.num.U64.wrapping_add y K := by
      intro y K hy hK e
      have e' := congrArg UScalar.val e
      rw [hv, field_val (hT y hy) hK] at e'
      rcases h.ksOut y hy with h' | h' <;> omega
    rw [notWk Y _ wY ha (by rw [stA_eq]; exact tne w _ hw (by simp))
      (by rw [eKB]; exact tne w _ hw (by omega))
      (by rw [e1N]; exact ks_ne_node hN (by rw [hcdv]; omega) (by rw [act_val]; omega))]
    refine wi.mem_eq ha ?_
    rintro (⟨y, hy, e | e⟩ | e | e)
    · exact tne y (nextOff .Ep) (hq.mem y hy) (by simp [nextOff]) (by rw [e]; rfl)
    · exact tne y (prevOff .Ep) (hq.mem y hy) (by simp [prevOff]) (by rw [e]; rfl)
    · have e' := congrArg UScalar.val e
      rw [hv, epHeadA_val] at e'
      rcases hEN.2 with h' | h' <;> omega
    · have e' := congrArg UScalar.val e
      rw [hv, epTSA_val hE] at e'
      rcases hEN.2 with h' | h' <;> omega
  refine wakeTail.gw (gS := gS) ar X1 a w n badge (sb := sb) ?_ (NodeSt.of_wi hn wi) aS aR nSR aA
    (fun e => nF _ 3328#u64 (by rw [act_val]; omega) (by simp) (by rw [← stA_eq]; exact e))
    (fun e => nF _ KB (by rw [act_val]; omega) (by omega) (by rw [← eKB]; exact e)) aC
    (fun e => nF _ 3328#u64 (by rw [curth_val]; omega) (by simp) (by rw [← stA_eq]; exact e)) rS (wS X1 wi) rSc rI rD rA wB ?_ ?_
  · have : L.curW X1 = L.curW X := by
      unfold LawfulStore.curW
      exact kN layout.node.CUR_THREAD (by rw [curth_val]; omega) (by rw [curth_val])
    rw [this]; exact hcur
  · have : L.actionW X1 = L.actionW X := by
      unfold LawfulStore.actionW
      exact kN layout.node.SCHED_ACTION (by rw [act_val]; omega) (by rw [act_val])
    rw [this]; exact hac
  · intro Y wY
    refine P.agree (wY.1.trans k1) (wY.2.1.trans c1) ?_ (oK Y _ wY hnsΩ) ?_ (cdK Y wY) ?_
      (fun h0 b hb hin => oK Y b wY (hscΩ h0 b hb hin))
    · rw [scA_eq]; exact tK Y 3464#u64 wY (by simp) (by simp) (by simp) (by simp) (by simp) (by rw [hKB']; simp)
    · exact tK Y 3432#u64 wY (by simp) (by simp) (by simp) (by simp) (by simp) (by rw [hKB']; simp)
    · exact tK Y 3520#u64 wY (by simp) (by simp) (by simp) (by simp) (by simp) (by rw [hKB']; simp)

end wait

section recv
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
variable {T Cs Ω : Set U64} {H : Heap}

/-- What `cancel_ipc` of a thread `t` in `Recv` on the endpoint `ep` (queue `xs`) with reply `r` writes. -/
def CnD (xs : List U64) (ep t r b : U64) : Prop :=
  b = faultA t ∨ EpFoot xs ep b ∨ (r ≠ 0#u64 ∧ b = rTcbA r) ∨ b = stA t

omit [PathObl.GRd gS st R] [PathObl.GWr gS st W] in
/-- `set_thread_state` of a thread that is not the current one: its `STATE` word. -/
theorem sts_ok (Y : S) (t v : U64) (hcur : t ≠ L.curW Y) (aS : Aligned (stA t))
    (aC : Aligned (L.nodeAt Y (L.cpu Y) layout.node.CUR_THREAD))
    (nC : L.nodeAt Y (L.cpu Y) layout.node.CUR_THREAD ≠ stA t) :
    sched.set_thread_state st Y t v = ok (L.wr Y (stA t) v) := by
  have hc2 : L.curW (L.wr Y (stA t) v) = L.curW Y := by
    unfold LawfulStore.curW
    rw [nodeAt_wr, L.cpu_wr]
    exact mem_wr_ne' aS aC (Ne.symm nC)
  unfold sched.set_thread_state
  rw [PathObl.set_state_ok']
  simp only [bind_ok]
  unfold sched.schedule_tcb
  rw [cur_thread_ok, hc2]
  simp only [bind_ok]
  rw [eq_of_spec_fd (tcb_eq.blk t (L.curW Y))]
  simp only [bind_ok, hcur, decide_false, Bool.false_eq_true, ↓reduceIte]

omit [PathObl.GRd gS st R] [PathObl.GWr gS st W] in
/-- The run of `cancel_ipc` of a thread in `Recv`, on `st`, step by step. -/
theorem cancel_recv_st {A : Type} (ar : machine.Arch A) (X : S) (a : A) (t : U64) {X4 : S} {a4 : A}
    (hs : L.mem (L.wr X (faultA t) fl4_abi.consts.fault.NullFault) (stA t) = sched.TS_BLOCKED_ON_RECV)
    (h : ipc.cancel_ipc st ar X a t = ok (X4, a4)) :
    a4 = a ∧ ∃ X2, endpoint.ep_dequeue st (L.wr X (faultA t) fl4_abi.consts.fault.NullFault)
        (L.mem (L.wr X (faultA t) fl4_abi.consts.fault.NullFault) (blockA t)) t = ok X2 ∧
      ∃ X3, (if L.mem X2 (replyA t) != 0#u64 then ipc.reply_unlink st X2 (L.mem X2 (replyA t)) t else ok X2) =
        ok X3 ∧ sched.set_thread_state st X3 t sched.TS_INACTIVE = ok X4 := by
  have e1 : faults.clear_fault st X t = ok (L.wr X (faultA t) fl4_abi.consts.fault.NullFault) := by
    unfold faults.clear_fault
    exact eq_of_spec_fd (obj.Tcb.set_fault_type.spec (L := L) X t _)
  have eC : ipc.cancel_ipc st ar X a t = (do
      let s2 ← endpoint.ep_dequeue st (L.wr X (faultA t) fl4_abi.consts.fault.NullFault)
        (L.mem (L.wr X (faultA t) fl4_abi.consts.fault.NullFault) (blockA t)) t
      let s3 ← (do
        let i ← obj.Tcb.reply_obj st t s2
        if i != 0#u64 then ipc.reply_unlink st s2 i t else ok s2)
      let s4 ← sched.set_thread_state st s3 t sched.TS_INACTIVE
      ok (s4, a)) := by
    unfold ipc.cancel_ipc
    rw [e1]
    simp only [bind_ok]
    rw [eq_of_spec_fd (obj.Tcb.state.spec (L := L) _ t), hs]
    simp only [bind_ok, if_neg recv_ne_send, eq_self_iff_true, if_true, ↓reduceIte]
    rw [eq_of_spec_fd (obj.Tcb.block_obj.spec (L := L) _ t)]
    simp only [bind_ok]
  rw [eC] at h
  obtain ⟨X2, h2, h⟩ := bind_eq_ok h
  obtain ⟨X3, h3, h⟩ := bind_eq_ok h
  rw [eq_of_spec_fd (obj.Tcb.reply_obj.spec (L := L) X2 t)] at h3
  simp only [bind_ok] at h3
  obtain ⟨X4', h4, h⟩ := bind_eq_ok h
  have e := ok_inj_ff h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact ⟨rfl, X2, h2, X3, h3, h4⟩

theorem ntfn_idle_ne_waiting : obj.NTFN_IDLE ≠ obj.NTFN_WAITING := by
  unfold obj.NTFN_WAITING obj.NTFN_IDLE; decide

theorem recv_ne_vm : sched.TS_BLOCKED_ON_RECV ≠ sched.TS_RUNNING_VM := by
  unfold sched.TS_BLOCKED_ON_RECV sched.TS_RUNNING_VM; decide

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
/-- **The idle-bound `Recv` branch of a fired timer's `send_signal` on the guarded store**: `t` the notification's
bound thread, waiting in `Recv` on the endpoint `ep` with reply `r` (premises at the start state `X`; the two
`STATE` writes `INACTIVE` / `RUNNING` answered as `st`'s at the states reached by `cancel_ipc`'s writes `CnD`). -/
theorem wake_recv_guard {A : Type} (ar : machine.Arch A) (X : S) (a : A) (n badge t ep r : U64) {sb : Nat}
    {Xs E : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {EQ : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H Xs X Q Rq) (hEW : EpsWit st T Cs Ω H Xs X E EQ)
    (hidle : L.epState X n = obj.NTFN_IDLE) (hbt : L.mem X (ntfnBtA n) = t) (ht0 : t ≠ 0#u64)
    (hrecv : L.mem X (stA t) = sched.TS_BLOCKED_ON_RECV)
    (heq : L.mem X (blockA t) = ep) (hep : ep ∈ E) (hmem : t ∈ EQ ep) (hr : L.mem X (replyA t) = r)
    (r1 : R (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE)) (aT : Aligned (epTSA n)) (aB : Aligned (ntfnBdA n))
    (rBt : R (core.num.U64.wrapping_add n layout.ntfn.BOUND_TCB))
    (wF : W (faultA t)) (rS : R (stA t)) (rB : R (blockA t)) (rRp : R (replyA t))
    (rEH : R (core.num.U64.wrapping_add ep layout.ep.HEAD)) (rET : R (core.num.U64.wrapping_add ep layout.ep.TAIL_STATE))
    (wEH : W (core.num.U64.wrapping_add ep layout.ep.HEAD)) (wET : W (core.num.U64.wrapping_add ep layout.ep.TAIL_STATE))
    (rP : R (prevA .Ep t)) (rN : R (nextA .Ep t)) (wP : W (prevA .Ep t)) (wN : W (nextA .Ep t))
    (wPn : (L.epQ X ep).end ≠ t → W (prevA .Ep (L.mem X (nextA .Ep t))))
    (wNp : (L.epQ X ep).head ≠ t → W (nextA .Ep (L.mem X (prevA .Ep t))))
    (wRt : r ≠ 0#u64 → W (rTcbA r) ∧ Aligned (rTcbA r))
    (rMx : L.mem X (scA t) ≠ 0#u64 → R (maxA (L.mem X (scA t))))
    (hcur : t ≠ L.curW X) (hn : NodeSt (L := L) R W X)
    (rSc : R (scA t)) (rI : R (inqA t)) (rD : R (domA t)) (rA : R (affA t))
    (wB : W (regA t layout.reg.BADGE)) (hac : L.actionW X = sched.ACTION_RESUME_CURRENT)
    (wI : ∀ Y, WritesIn st X Y (CnD (EQ ep) ep t r) →
      gS.write Y (stA t) sched.TS_INACTIVE = st.write Y (stA t) sched.TS_INACTIVE)
    (wS : ∀ Y, WritesIn st X Y (CnD (EQ ep) ep t r) →
      gS.write Y (stA t) sched.TS_RUNNING = st.write Y (stA t) sched.TS_RUNNING)
    (P : WkPre st R W X t n sb) (hnsΩ : ntfnScA n ∈ Ω)
    (hscΩ : L.mem X (scA t) ≠ 0#u64 → ∀ b, Aligned b → InSC (L.mem X (scA t)) sb b → b ∈ Ω)
    (hRt : r ≠ 0#u64 → ∀ b, (b = ntfnScA n ∨ (Aligned b ∧ InSC (L.mem X (scA t)) sb b) ∨
      b = core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN ∨
      (∃ o : U64, o.val < 4288 ∧ b = L.nodeAt X (L.cpu X) o) ∨
      (∃ K : U64, K.val < 4096 ∧ b = core.num.U64.wrapping_add t K)) → b ≠ rTcbA r) :
    notification.send_signal gS ar X a n badge = notification.send_signal st ar X a n badge := by
  obtain ⟨hE, hEN, hq⟩ := hEW.1 ep hep
  have hT := h.tcbs
  have ht : t ∈ T := hq.mem t hmem
  have ht' := hT t ht
  have hcC := h.cur
  have hN : NodePlaced st T X (L.cpu X) := h.nodes _ hcC
  have hbv : layout.reg.BADGE.val = 0 := by unfold layout.reg.BADGE layout.reg.RDI; rfl
  obtain ⟨KB, hKB, eKB⟩ := regA_eq ht' (r := layout.reg.BADGE) (by rw [hbv]; omega)
  have hKB' : KB.val = 256 := by rw [hKB, hbv]
  have hcdv : layout.ks.CUR_DOMAIN.val = 8 := by simp [layout.ks.CUR_DOMAIN]
  have aF : Aligned (faultA t) := field_aligned ht' (by simp) (by simp)
  have aS : Aligned (stA t) := by rw [stA_eq]; exact field_aligned ht' (by simp) (by simp)
  have aR : Aligned (regA t layout.reg.BADGE) := by
    rw [eKB]; exact field_aligned ht' (by omega) (by rw [hKB'])
  -- the queue's members and the endpoint's words against a word of `t`
  have epT : ∀ (K : U64), K.val < 4096 → ∀ b, (b = epHeadA ep ∨ b = epTSA ep) →
      core.num.U64.wrapping_add t K ≠ b := by
    intro K hK b hb e
    have e' := congrArg UScalar.val e
    rw [field_val ht' hK] at e'
    rcases hb with rfl | rfl
    · rw [epHeadA_val] at e'; rcases hE.disj t ht with h' | h' <;> omega
    · rw [epTSA_val hE] at e'; rcases hE.disj t ht with h' | h' <;> omega
  have lnkT : ∀ (K : U64), K.val < 4096 → K.val ≠ 3496 → K.val ≠ 3504 → ∀ b, LinkOf .Ep (EQ ep) b →
      core.num.U64.wrapping_add t K ≠ b := by
    rintro K hK h1 h2 b ⟨y, hy, rfl | rfl⟩ <;>
      exact tcb_word_ne ht' (hT y (hq.mem y hy)) hK (by simp [nextOff, prevOff])
        (fun e => by subst e; simp [nextOff, prevOff]; omega)
  -- the fault word written
  set X' := L.wr X (faultA t) fl4_abi.consts.fault.NullFault with eX'
  have mF : ∀ b, Aligned b → b ≠ faultA t → L.mem X' b = L.mem X b := fun b hb hne =>
    mem_wr_ne' aF hb (Ne.symm hne)
  have fT : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3376 →
      L.mem X' (core.num.U64.wrapping_add t K) = L.mem X (core.num.U64.wrapping_add t K) := fun K hK h8 h1 =>
    mF _ (field_aligned ht' hK h8) (tcb_word_ne ht' ht' hK (by simp) (fun _ => by simp; omega))
  have hs : L.mem X' (stA t) = sched.TS_BLOCKED_ON_RECV := by rw [stA_eq, fT _ (by simp) (by simp) (by simp), ← stA_eq, hrecv]
  have eB : L.mem X' (blockA t) = ep := by rw [blockA_eq, fT _ (by simp) (by simp) (by simp), ← blockA_eq, heq]
  have eR : L.mem X' (replyA t) = r := by
    show L.mem X' (core.num.U64.wrapping_add t 3360#u64) = r
    rw [fT _ (by simp) (by simp) (by simp)]; exact hr
  have eQ : L.epQ X' ep = L.epQ X ep := by
    simp only [LawfulStore.epQ]
    rw [mF _ (ep_aligned hE).1 (fun e => epT 3376#u64 (by simp) _ (Or.inl rfl) e.symm),
      mF _ (ep_aligned hE).2 (fun e => epT 3376#u64 (by simp) _ (Or.inr rfl) e.symm)]
  have hq' : QueueRel (L.mem X') T .Ep (L.epQ X' ep) (EQ ep) := by
    rw [eQ]
    exact QueueRel.wr_out hT hq aF fun y hy =>
      ⟨fun e => lnkT 3376#u64 (by simp) (by simp) (by simp) _ ⟨y, hy, Or.inl rfl⟩ e,
       fun e => lnkT 3376#u64 (by simp) (by simp) (by simp) _ ⟨y, hy, Or.inr rfl⟩ e⟩
  have eNx : L.mem X' (nextA .Ep t) = L.mem X (nextA .Ep t) := fT (nextOff .Ep) (by simp [nextOff]) (by simp [nextOff]) (by simp [nextOff])
  have ePv : L.mem X' (prevA .Ep t) = L.mem X (prevA .Ep t) := fT (prevOff .Ep) (by simp [prevOff]) (by simp [prevOff]) (by simp [prevOff])
  -- frames: a write set reached from `X`
  have wiF : WritesIn st X X' (CnD (EQ ep) ep t r) :=
    (writesIn_wr aF).mono fun b hb => Or.inl hb
  have nodeK : ∀ (Y : S), WritesIn st X Y (CnD (EQ ep) ep t r) → ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem Y (L.nodeAt Y (L.cpu Y) o) = L.mem X (L.nodeAt X (L.cpu X) o) := by
    intro Y wY o ho h8
    rw [wY.2.1, nodeAt_of_ksb wY.1]
    refine wY.mem_eq (nodeAt_aligned hN ho h8) ?_
    rintro (e | e | ⟨hr0, e⟩ | e)
    · exact node_ne_field hN ho ht ht' (K := 3376#u64) (by simp) e
    · rcases e with ⟨y, hy, e | e⟩ | e | e
      · exact node_ne_field hN ho (hq.mem y hy) (hT y (hq.mem y hy)) (K := nextOff .Ep) (by simp [nextOff]) e
      · exact node_ne_field hN ho (hq.mem y hy) (hT y (hq.mem y hy)) (K := prevOff .Ep) (by simp [prevOff]) e
      · have e' := congrArg UScalar.val e
        rw [nodeAt_val hN ho, epHeadA_val] at e'
        rcases hEN.1 _ hcC with h' | h' <;> omega
      · have e' := congrArg UScalar.val e
        rw [nodeAt_val hN ho, epTSA_val hE] at e'
        rcases hEN.1 _ hcC with h' | h' <;> omega
    · exact hRt hr0 _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨o, ho, rfl⟩)))) e
    · rw [stA_eq] at e; exact node_ne_field hN ho ht ht' (by simp) e
  refine notification.send_signal.guardF (gS := gS) ar X a n badge r1 aT aB
    (fun h1 _ => absurd hidle h1) (fun _ => ?_) (fun h1 => absurd (hidle.symm.trans h1) ntfn_idle_ne_waiting)
  rw [hbt]
  refine ⟨rBt, fun hc => ?_, fun _ => ⟨rS, by rw [hrecv]; exact recv_ne_vm, fun hn' => absurd hrecv hn', fun _ => ?_⟩⟩
  · rcases hc with hc | hc
    · exact absurd hc ht0
    · exact absurd hrecv hc
  -- the reply and the endpoint dequeue on `st`
  have stsK : ∀ (Y : S) (v : U64), WritesIn st X Y (CnD (EQ ep) ep t r) →
      sched.set_thread_state st Y t v = ok (L.wr Y (stA t) v) := by
    intro Y v wY
    have eC : L.nodeAt Y (L.cpu Y) layout.node.CUR_THREAD = L.nodeAt X (L.cpu X) layout.node.CUR_THREAD := by
      rw [wY.2.1, nodeAt_of_ksb wY.1]
    refine sts_ok Y t v ?_ aS (by rw [eC]; exact nodeAt_aligned hN (by rw [curth_val]; omega) (by rw [curth_val]))
      (by rw [eC, stA_eq]; exact node_ne_field hN (by rw [curth_val]; omega) ht ht' (by simp))
    have : L.curW Y = L.curW X := nodeK Y wY _ (by rw [curth_val]; omega) (by rw [curth_val])
    rw [this]; exact hcur
  have deq : ∀ X2, endpoint.ep_dequeue st X' ep t = ok X2 → WritesIn st X X2 (CnD (EQ ep) ep t r) := by
    intro X2 h2
    have := endpoint.ep_dequeue.foot (st := st) X' ep t (EQ ep) hT hE hq' hmem
    rw [h2, WP.spec_ok] at this
    exact (wiF.trans this).mono fun b hb => hb.elim id fun hb => Or.inr (Or.inl hb)
  have rep : ∀ X2, WritesIn st X X2 (CnD (EQ ep) ep t r) → L.mem X2 (replyA t) = r := by
    intro X2 wX
    show L.mem X2 (core.num.U64.wrapping_add t 3360#u64) = r
    rw [wX.mem_eq (field_aligned ht' (by simp) (by simp)) ?_]
    · exact hr
    rintro (e | e | ⟨hr0, e⟩ | e)
    · exact tcb_word_ne ht' ht' (K1 := 3360#u64) (K2 := 3376#u64) (by simp) (by simp) (fun _ => by simp) e
    · rcases e with e | e | e
      · exact lnkT 3360#u64 (by simp) (by simp) (by simp) _ e rfl
      · exact epT 3360#u64 (by simp) _ (Or.inl e) rfl
      · exact epT 3360#u64 (by simp) _ (Or.inr e) rfl
    · exact hRt hr0 _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨3360#u64, by simp, rfl⟩)))) e
    · rw [stA_eq] at e; exact tcb_word_ne ht' ht' (K1 := 3360#u64) (K2 := 3328#u64) (by simp) (by simp) (fun _ => by simp) e
  have runl : ∀ X2 X3, WritesIn st X X2 (CnD (EQ ep) ep t r) →
      (if L.mem X2 (replyA t) != 0#u64 then ipc.reply_unlink st X2 (L.mem X2 (replyA t)) t else ok X2) = ok X3 →
      WritesIn st X X3 (CnD (EQ ep) ep t r) := by
    intro X2 X3 wX h3
    rw [rep X2 wX] at h3
    by_cases hr0 : r ≠ 0#u64
    · rw [if_pos (bne_iff_ne.mpr hr0)] at h3
      unfold ipc.reply_unlink at h3
      unfold obj.Reply.set_tcb at h3
      simp only [lift, bind_ok, L.write_eq] at h3
      have w1 : WritesIn st X (L.wr X2 (rTcbA r) 0#u64) (CnD (EQ ep) ep t r) :=
        (wX.trans (writesIn_wr (wRt hr0).2)).mono fun b hb => hb.elim id fun e => Or.inr (Or.inr (Or.inl ⟨hr0, e⟩))
      rw [show core.num.U64.wrapping_add r layout.reply.TCB = rTcbA r from rfl, stsK _ _ w1] at h3
      rw [← ok_inj_ff h3]
      exact (w1.trans (writesIn_wr aS)).mono fun b hb => hb.elim id fun e => Or.inr (Or.inr (Or.inr e))
    · rw [if_neg (by simpa using hr0)] at h3
      rw [← ok_inj_ff h3]; exact wX
  have scK : ∀ (Y : S), WritesIn st X Y (CnD (EQ ep) ep t r) → L.mem Y (scA t) = L.mem X (scA t) := by
    intro Y wY
    rw [scA_eq]
    refine wY.mem_eq (field_aligned ht' (by simp) (by simp)) ?_
    rintro (e | e | ⟨hr0, e⟩ | e)
    · exact tcb_word_ne ht' ht' (K1 := 3464#u64) (K2 := 3376#u64) (by simp) (by simp) (fun _ => by simp) e
    · rcases e with e | e | e
      · exact lnkT 3464#u64 (by simp) (by simp) (by simp) _ e rfl
      · exact epT 3464#u64 (by simp) _ (Or.inl e) rfl
      · exact epT 3464#u64 (by simp) _ (Or.inr e) rfl
    · exact hRt hr0 _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨3464#u64, by simp, rfl⟩)))) e
    · rw [stA_eq] at e; exact tcb_word_ne ht' ht' (K1 := 3464#u64) (K2 := 3328#u64) (by simp) (by simp) (fun _ => by simp) e
  have stG : ∀ (Y : S) (v : U64), WritesIn st X Y (CnD (EQ ep) ep t r) →
      (gS.write Y (stA t) v = st.write Y (stA t) v) →
      sched.set_thread_state gS Y t v = sched.set_thread_state st Y t v := by
    intro Y v wY hw
    refine set_thread_state.gwC (gS := gS) Y t v (NodeSt.of_wi hn wY) hw rS rSc ?_ rI
    rw [PathObl.st_wr_sc ht', scK Y wY]; exact rMx
  constructor
  · -- `cancel_ipc` on the guarded store
    refine Fl4Proofs.P2.ipc.cancel_ipc.guard_recv (gS := gS) ar X a t wF rS rB rRp hs ?_ fun X2 h2 => ?_
    · rw [eB]
      refine endpoint.ep_dequeue.guard (gS := gS) X' ep t rEH rET wEH wET fun q hq'' => ?_
      rw [eq_of_spec_fd (endpoint.get_queue.spec (L := L) X' ep), eQ] at hq''
      have e := ok_inj_ff hq''
      subst e
      exact tcbqueue.remove.guardL (gS := gS) X' .Ep _ t rP rN (fun h' => by rw [eNx]; exact wPn h')
        (fun h' => by rw [ePv]; exact wNp h') wN wP
    · rw [eB] at h2
      have wX2 := deq X2 h2
      refine ⟨fun hr0 => ?_, fun X3 h3 => stG X3 _ (runl X2 X3 wX2 h3) (wI X3 (runl X2 X3 wX2 h3))⟩
      rw [rep X2 wX2] at hr0 ⊢
      unfold ipc.reply_unlink
      have g1 : obj.Reply.set_tcb gS r X2 0#u64 = ok (L.wr X2 (rTcbA r) 0#u64) := by
        unfold obj.Reply.set_tcb; simp only [lift, bind_ok]
        rw [show core.num.U64.wrapping_add r layout.reply.TCB = rTcbA r from rfl, PathObl.gst_write (wRt hr0).1,
          L.write_eq]
      have g2 : obj.Reply.set_tcb st r X2 0#u64 = ok (L.wr X2 (rTcbA r) 0#u64) := by
        unfold obj.Reply.set_tcb; simp only [lift, bind_ok, L.write_eq]; rfl
      rw [g1, g2]
      simp only [bind_ok]
      have w1 : WritesIn st X (L.wr X2 (rTcbA r) 0#u64) (CnD (EQ ep) ep t r) :=
        (wX2.trans (writesIn_wr (wRt hr0).2)).mono fun b hb => hb.elim id fun e => Or.inr (Or.inr (Or.inl ⟨hr0, e⟩))
      exact stG _ _ w1 (wI _ w1)
  · -- `wakeTail` after it
    intro X4 a4 h4
    obtain ⟨ea, X2, h2, X3, h3, h5⟩ := cancel_recv_st ar X a t hs h4
    rw [ea]
    rw [eB] at h2
    have wX3 := runl X2 X3 (deq X2 h2) h3
    rw [stsK X3 _ wX3] at h5
    have wX4 : WritesIn st X X4 (CnD (EQ ep) ep t r) := by
      rw [← ok_inj_ff h5]
      exact (wX3.trans (writesIn_wr aS)).mono fun b hb => hb.elim id fun e => Or.inr (Or.inr (Or.inr e))
    have k4 : L.ksb X4 = L.ksb X := wX4.1
    have c4 : L.cpu X4 = L.cpu X := wX4.2.1
    have e4N : ∀ o, L.nodeAt X4 (L.cpu X4) o = L.nodeAt X (L.cpu X) o := fun o => by rw [c4, nodeAt_of_ksb k4]
    have hN4 : NodePlaced st T X4 (L.cpu X4) := by rw [c4]; exact hN.ksb k4
    have nF : ∀ o K : U64, o.val < 4288 → K.val < 4096 → L.nodeAt X4 (L.cpu X4) o ≠ core.num.U64.wrapping_add t K :=
      fun o K ho hK => node_ne_field hN4 ho ht ht' hK
    have hRn : r ≠ 0#u64 → ntfnScA n ≠ rTcbA r := fun hr0 => hRt hr0 (ntfnScA n) (Or.inl (Eq.refl _))
    have nSR : stA t ≠ regA t layout.reg.BADGE := by
      rw [stA_eq, eKB]; exact tcb_word_ne ht' ht' (by simp) (by omega) (fun _ h => by simp at h; omega)
    -- the words `wakeTail` reads, from `X` across `CnD` then `WkD`
    have gen : ∀ (Y : S) (b : U64), WritesIn st X4 Y (WkD st X4 t) → Aligned b →
        ¬ CnD (EQ ep) ep t r b → b ≠ stA t → b ≠ regA t layout.reg.BADGE →
        b ≠ L.nodeAt X4 (L.cpu X4) layout.node.SCHED_ACTION → L.mem Y b = L.mem X b := by
      intro Y b wY hb hC h1 h2 h3
      rw [wY.mem_eq hb (by rintro (e | e | e) <;> [exact h1 e; exact h2 e; exact h3 e])]
      exact wX4.mem_eq hb hC
    have tK : ∀ (Y : S) (K : U64), WritesIn st X4 Y (WkD st X4 t) → K.val < 4096 → K.val % 8 = 0 →
        K.val ≠ 3496 → K.val ≠ 3504 → K.val ≠ 3328 → K.val ≠ 3376 → K.val ≠ 256 →
        L.mem Y (core.num.U64.wrapping_add t K) = L.mem X (core.num.U64.wrapping_add t K) := by
      intro Y K wY hK h8 h1 h2 h3 h4 h5
      refine gen Y _ wY (field_aligned ht' hK h8) ?_ (by rw [stA_eq]; exact tcb_word_ne ht' ht' hK (by simp) (fun _ e => h3 (by rw [e]; rfl)))
        (by rw [eKB]; exact tcb_word_ne ht' ht' hK (by omega) (fun _ => by omega)) (fun e => nF _ K (by rw [act_val]; omega) hK e.symm)
      rintro (e | e | ⟨hr0, e⟩ | e)
      · exact tcb_word_ne ht' ht' hK (K2 := 3376#u64) (by simp) (fun _ e' => h4 (by rw [e']; rfl)) e
      · rcases e with e | e | e
        · exact lnkT K hK h1 h2 _ e rfl
        · exact epT K hK _ (Or.inl e) rfl
        · exact epT K hK _ (Or.inr e) rfl
      · exact hRt hr0 _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨K, hK, rfl⟩)))) e
      · rw [stA_eq] at e; exact tcb_word_ne ht' ht' hK (K2 := 3328#u64) (by simp) (fun _ e' => h3 (by rw [e']; rfl)) e
    have oK : ∀ (Y : S) (b : U64), WritesIn st X4 Y (WkD st X4 t) → b ∈ Ω →
        (r ≠ 0#u64 → b ≠ rTcbA r) → L.mem Y b = L.mem X b := by
      intro Y b wY hb hbr
      have ho := h.omega b hb
      have ho4 : OutsideObjs st T Cs X4 b := ho.ksb k4
      refine gen Y b wY ho.1 ?_ (fun e => out_ne_field ho ht ht' (K := 3328#u64) (by simp) (by rw [← stA_eq, e]))
        (fun e => out_ne_field ho ht ht' (K := KB) (by omega) (by rw [← eKB, e]))
        (fun e => out_ne_node ho4 (by rw [c4]; exact hcC) hN4 (o := layout.node.SCHED_ACTION) (by rw [act_val]; omega)
          (by rw [e]))
      rintro (e | e | ⟨hr0, e⟩ | e)
      · exact out_ne_field ho ht ht' (K := 3376#u64) (by simp) (by rw [e]; rfl)
      · rcases e with ⟨y, hy, e | e⟩ | e | e
        · exact out_ne_field ho (hq.mem y hy) (hT y (hq.mem y hy)) (K := nextOff .Ep) (by simp [nextOff]) (by rw [e]; rfl)
        · exact out_ne_field ho (hq.mem y hy) (hT y (hq.mem y hy)) (K := prevOff .Ep) (by simp [prevOff]) (by rw [e]; rfl)
        · have e' := congrArg UScalar.val e
          rw [epHeadA_val] at e'
          rcases hEW.2.2.1 ep hep b hb with h' | h' <;> omega
        · have e' := congrArg UScalar.val e
          rw [epTSA_val hE] at e'
          rcases hEW.2.2.1 ep hep b hb with h' | h' <;> omega
      · exact hbr hr0 e
      · exact out_ne_field ho ht ht' (K := 3328#u64) (by simp) (by rw [← stA_eq, e])
    have cdK : ∀ (Y : S), WritesIn st X4 Y (WkD st X4 t) →
        L.mem Y (core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN) =
          L.mem X (core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN) := by
      intro Y wY
      have hv : (core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN).val = (L.ksb X).val + 8 := by
        rw [ks_word_val hN (by rw [hcdv]; omega), hcdv]
      have ha : Aligned (core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN) :=
        ks_aligned hN (by rw [hcdv]; omega) (by rw [hcdv])
      have tne : ∀ y K, y ∈ T → K.val < 4096 →
          core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN ≠ core.num.U64.wrapping_add y K := by
        intro y K hy hK e
        have e' := congrArg UScalar.val e
        rw [hv, field_val (hT y hy) hK] at e'
        rcases h.ksOut y hy with h' | h' <;> omega
      refine gen Y _ wY ha ?_ (by rw [stA_eq]; exact tne t _ ht (by simp)) (by rw [eKB]; exact tne t _ ht (by omega))
        (by rw [e4N]; exact ks_ne_node hN (by rw [hcdv]; omega) (by rw [act_val]; omega))
      rintro (e | e | ⟨hr0, e⟩ | e)
      · exact tne t (3376#u64) ht (by simp) (by rw [e]; rfl)
      · rcases e with ⟨y, hy, e | e⟩ | e | e
        · exact tne y (nextOff .Ep) (hq.mem y hy) (by simp [nextOff]) (by rw [e]; rfl)
        · exact tne y (prevOff .Ep) (hq.mem y hy) (by simp [prevOff]) (by rw [e]; rfl)
        · have e' := congrArg UScalar.val e
          rw [hv, epHeadA_val] at e'
          rcases hEN.2 with h' | h' <;> omega
        · have e' := congrArg UScalar.val e
          rw [hv, epTSA_val hE] at e'
          rcases hEN.2 with h' | h' <;> omega
      · exact hRt hr0 _ (Or.inr (Or.inr (Or.inl rfl))) e
      · rw [stA_eq] at e; exact tne t _ ht (by simp) e
    refine wakeTail.gw (gS := gS) ar X4 a t n badge (sb := sb) ?_ (NodeSt.of_wi hn wX4) aS aR nSR
      (nodeAt_aligned hN4 (by rw [act_val]; omega) (by rw [act_val]))
      (fun e => nF _ 3328#u64 (by rw [act_val]; omega) (by simp) (by rw [← stA_eq]; exact e))
      (fun e => nF _ KB (by rw [act_val]; omega) (by omega) (by rw [← eKB]; exact e))
      (nodeAt_aligned hN4 (by rw [curth_val]; omega) (by rw [curth_val]))
      (fun e => nF _ 3328#u64 (by rw [curth_val]; omega) (by simp) (by rw [← stA_eq]; exact e)) rS (wS X4 wX4) rSc rI
      rD rA wB ?_ ?_
    · have : L.curW X4 = L.curW X := nodeK X4 wX4 layout.node.CUR_THREAD (by rw [curth_val]; omega) (by rw [curth_val])
      rw [this]; exact hcur
    · have : L.actionW X4 = L.actionW X := nodeK X4 wX4 layout.node.SCHED_ACTION (by rw [act_val]; omega) (by rw [act_val])
      rw [this]; exact hac
    · intro Y wY
      have e1 : L.mem Y (scA t) = L.mem X (scA t) := by
        rw [scA_eq]; exact tK Y 3464#u64 wY (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      have e3 : L.mem Y (domA t) = L.mem X (domA t) :=
        tK Y 3432#u64 wY (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      have e5 : L.mem Y (affA t) = L.mem X (affA t) :=
        tK Y 3520#u64 wY (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      have e2 : L.mem Y (ntfnScA n) = L.mem X (ntfnScA n) := oK Y (ntfnScA n) wY hnsΩ hRn
      have e4 := cdK Y wY
      have e6 : L.mem X (scA t) ≠ 0#u64 → ∀ b, Aligned b → InSC (L.mem X (scA t)) sb b → L.mem Y b = L.mem X b :=
        fun h0 b hb hin =>
        oK Y b wY (hscΩ h0 b hb hin) fun hr0 => hRt hr0 b (Or.inr (Or.inl ⟨hb, hin⟩))
      exact P.agree (wY.1.trans k4) (wY.2.1.trans c4) e1 e2 e3 e4 e5 e6

end recv

end Fl4Proofs.P2

