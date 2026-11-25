/-
# P2 (line p2sl): declined fast-path arms on a store guarded to a read set

The walks `SlThr.home` / `SlThr.away` need: a declining run of an arm of
`handle_syscall_local` reads only a given read set `R` (no writes after the prefix).

* `fastpath.schedulable_here.guard'`: `schedulable_here.guard` with `to`'s domain, SC and
  queue words needed only when its `AFFINITY` is this core (otherwise it answers `false` right
  after reading `AFFINITY`);
* `FltDec R X t`, `DestDec R X d`: the words the trap arm reads at its entry state `X` for the
  current thread `t` and the receiver `d` up to its last check; the receiver's words after
  `AFFINITY` only when it is homed here;
* **`fastpath.fault.guard_dec`**: a declined trap arm on `st` runs the same on `gS` with `R`
  holding `FltDec`;
* `PreDec`, `sl_pre_dec`, **`syscall.handle_syscall_local.guard_dec`**: the prefix on `gS`
  (reads `R`, writes `W` of the prefix words), the arms given as hypotheses;
* `UDec`, `RrDec`, **`fastpath.reply_recv_found.guard_dec`**: the same for the ReplyRecv arm.

No premises (the facts are hypotheses of the lemmas, discharged by the callers).
-/
import Fl4Proofs.P2.SlThr
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts

section
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
  [L : LawfulStore st]

/-- **`schedulable_here to`, `to`'s later words only when homed here.** -/
theorem fastpath.schedulable_here.guard' (s : S) (t : obj.Tcb)
    (hct : R (ctA (L := L) s)) (htm : R (tmA (L := L) s)) (hrh : R (rhA (L := L) s))
    (htd : L.mem s (tmA (L := L) s) ≠ 0#u64 →
      R (core.num.U64.wrapping_add (L.mem s (tmA (L := L) s)) 3528#u64))
    (hrs : L.mem s (rhA (L := L) s) ≠ 0#u64 → R (scA (L.mem s (rhA (L := L) s))) ∧
      RdHead (L := L) R s (L.mem s (scA (L.mem s (rhA (L := L) s)))))
    (hdt : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME))
    (hcd : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (haf : R (affA t))
    (hrest : L.mem s (affA t) = L.cpu s →
      R (core.num.U64.wrapping_add t 3432#u64) ∧ R (scA t) ∧ R (inqA t)) :
    fastpath.schedulable_here gS s t = fastpath.schedulable_here st s t := by
  by_cases ha : L.mem s (affA t) = L.cpu s
  · obtain ⟨h1, h2, h3⟩ := hrest ha
    exact fastpath.schedulable_here.guard (gS := gS) s t hct htm hrh htd hrs hdt hcd haf h1 h2 h3
  · unfold fastpath.schedulable_here
    simp only [gst_cur_cpu, L.cur_cpu_eq, bind_ok]
    rw [sched.cur_time.guard (gS := gS) s hct, obj.node_get.guard (gS := gS) s _ _ htm, obj.node_get.guard (gS := gS) s _ _ hrh,
      sched.is_cur_domain_expired.guard (gS := gS) (st := st) s, sched.domain_time.guard (gS := gS) s hdt,
      obj.Tcb.affinity.guard (gS := gS) t s haf, aff_ok]
    rw [node_get_ok s _ layout.node.TIMER_MIN, node_get_ok s _ layout.node.RELEASE_HEAD]
    simp only [bind_ok, is_null_ok, ha, ↓reduceIte]
    by_cases h0 : L.mem s (tmA (L := L) s) = 0#u64
    · simp only [h0, decide_true, ↓reduceIte]
      by_cases h1 : L.mem s (rhA (L := L) s) = 0#u64
      · simp only [h1, decide_true, ↓reduceIte]
      · obtain ⟨hs1, hs2⟩ := hrs h1
        rw [obj.Tcb.sc.guard (gS := gS) _ s hs1, tcb_sc_ok s (L.mem s (rhA (L := L) s))]
        simp only [bind_ok]
        rw [sporadic.ready.guard (gS := gS) s _ hs2 hct]
    · rw [obj.Tcb.timer_deadline.guard (gS := gS) _ s (htd h0)]
      by_cases h1 : L.mem s (rhA (L := L) s) = 0#u64
      · simp only [h1, decide_true, ↓reduceIte]
      · obtain ⟨hs1, hs2⟩ := hrs h1
        rw [obj.Tcb.sc.guard (gS := gS) _ s hs1, tcb_sc_ok s (L.mem s (rhA (L := L) s))]
        simp only [bind_ok]
        rw [sporadic.ready.guard (gS := gS) s _ hs2 hct]

/-- The receiver's words a declining trap arm reads (`AFFINITY` first; the rest only when it
is homed here). -/
structure DestDec (R : U64 → Prop) (X : S) (d : U64) : Prop where
  rp : R (replyA d)
  af : R (affA d)
  rest : L.mem X (affA d) = L.cpu X →
    R (core.num.U64.wrapping_add d 3432#u64) ∧ R (scA d) ∧ R (inqA d) ∧ R (prioA d)

/-- **The words a declining trap arm reads** at its entry state `X` (current thread `t`). -/
structure FltDec (R : U64 → Prop) (X : S) (t : U64) : Prop where
  nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt X (L.cpu X) o)
  dt : R (core.num.U64.wrapping_add (L.ksb X) layout.ks.DOMAIN_TIME)
  cd : R (core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN)
  bm : RdBitmap (L := L) R X
  tm : L.mem X (tmA (L := L) X) ≠ 0#u64 → R (core.num.U64.wrapping_add (L.mem X (tmA (L := L) X)) 3528#u64)
  rh : L.mem X (rhA (L := L) X) ≠ 0#u64 → R (scA (L.mem X (rhA (L := L) X))) ∧
    RdHead (L := L) R X (L.mem X (scA (L.mem X (rhA (L := L) X))))
  fh : R (slotIdx t layout.tcb.SLOT_FAULT_HANDLER) ∧
    R (core.num.U64.wrapping_add (slotIdx t layout.tcb.SLOT_FAULT_HANDLER) 8#u64)
  ep : ∀ ptr b x y g gr, obj.Slot.cap st (slotIdx t layout.tcb.SLOT_FAULT_HANDLER) X =
      ok (capability.Cap.Endpoint ptr b x y g gr) →
    R (epTSA ptr) ∧ R (epHeadA ptr) ∧ ∀ d, obj.Ep.head st ptr X = ok d → DestDec (L := L) R X d

variable {A : Type} {ar : machine.Arch A}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **A declined trap arm on the guarded store** (`R` holding `FltDec`). -/
theorem fastpath.fault.guard_dec {X : S} {a : A} {t n : U64} {r : Bool × S × A}
    (D : FltDec (L := L) R X t) (h : fastpath.fault st ar X a t n = ok r) (hn : r.1 ≠ true) :
    fastpath.fault gS ar X a t n = ok r := by
  unfold fastpath.fault at h ⊢
  revert h
  rw [sched.action.guard (gS := gS) X (D.nd _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))]
  refine tr_bind_same (fun i _ => ?_)
  refine tr_ite (fun _ h' => h') (fun _ => ?_)
  rw [tcb_slot_val]
  simp only [bind_ok]
  rw [obj.Slot.cap.guard (gS := gS) _ X D.fh.1 D.fh.2]
  refine tr_bind_same (fun c hc => ?_)
  cases c
  case Endpoint ptr badge x y g gr =>
    refine tr_ite (fun _ => ?_) (fun _ => tr_ite (fun _ => ?_) (fun _ h' => h'))
    · obtain ⟨hs, hh, hd⟩ := D.ep ptr badge x y g gr hc
      rw [obj.Ep.state.guard (gS := gS) ptr X hs]
      refine tr_bind_same (fun i1 _ => ?_)
      refine tr_ite (fun _ h' => h') (fun _ => ?_)
      rw [obj.Ep.head.guard (gS := gS) ptr X hh]
      refine tr_bind_same (fun d ed => ?_)
      have Dd := hd d ed
      rw [obj.Tcb.reply_obj.guard (gS := gS) d X Dd.rp]
      refine tr_bind_same (fun i3 _ => ?_)
      refine tr_ite (fun _ h' => h') (fun _ => ?_)
      rw [fastpath.schedulable_here.guard' (gS := gS) X d (D.nd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
        (D.nd _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]))
        (D.nd _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]))
        D.tm D.rh D.dt D.cd Dd.af (fun h => ⟨(Dd.rest h).1, (Dd.rest h).2.1, (Dd.rest h).2.2.1⟩)]
      refine tr_bind_same (fun b hb => ?_)
      refine tr_ite (fun hbt => ?_) (fun _ h' => h')
      have HF := here_facts (L := L) (show fastpath.schedulable_here st X d = ok true by rw [hb, hbt])
      rw [sched.cur_domain.guard (gS := gS) X D.cd]
      refine tr_bind_same (fun i4 _ => ?_)
      rw [obj.Tcb.prio.guard (gS := gS) d X (Dd.rest HF.aff).2.2.2]
      refine tr_bind_same (fun i5 _ => ?_)
      rw [sched.is_highest_prio.guard (gS := gS) X _ _ D.bm]
      refine tr_bind_same (fun b1 _ => ?_)
      refine tr_ite (fun _ => ?_) (fun _ h' => h')
      intro hk
      exfalso
      apply hn
      acc_true hk
    · obtain ⟨hs, hh, hd⟩ := D.ep ptr badge x y g gr hc
      rw [obj.Ep.state.guard (gS := gS) ptr X hs]
      refine tr_bind_same (fun i1 _ => ?_)
      refine tr_ite (fun _ h' => h') (fun _ => ?_)
      rw [obj.Ep.head.guard (gS := gS) ptr X hh]
      refine tr_bind_same (fun d ed => ?_)
      have Dd := hd d ed
      rw [obj.Tcb.reply_obj.guard (gS := gS) d X Dd.rp]
      refine tr_bind_same (fun i3 _ => ?_)
      refine tr_ite (fun _ h' => h') (fun _ => ?_)
      rw [fastpath.schedulable_here.guard' (gS := gS) X d (D.nd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
        (D.nd _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]))
        (D.nd _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]))
        D.tm D.rh D.dt D.cd Dd.af (fun h => ⟨(Dd.rest h).1, (Dd.rest h).2.1, (Dd.rest h).2.2.1⟩)]
      refine tr_bind_same (fun b hb => ?_)
      refine tr_ite (fun hbt => ?_) (fun _ h' => h')
      have HF := here_facts (L := L) (show fastpath.schedulable_here st X d = ok true by rw [hb, hbt])
      rw [sched.cur_domain.guard (gS := gS) X D.cd]
      refine tr_bind_same (fun i4 _ => ?_)
      rw [obj.Tcb.prio.guard (gS := gS) d X (Dd.rest HF.aff).2.2.2]
      refine tr_bind_same (fun i5 _ => ?_)
      rw [sched.is_highest_prio.guard (gS := gS) X _ _ D.bm]
      refine tr_bind_same (fun b1 _ => ?_)
      refine tr_ite (fun _ => ?_) (fun _ h' => h')
      intro hk
      exfalso
      apply hn
      acc_true hk
  all_goals exact fun h' => h'

/-- The replied thread's words a declining ReplyRecv arm reads (`AFFINITY` and the words
before it; the rest only when it is homed here). -/
structure UDec (R : U64 → Prop) (X : S) (u : U64) : Prop where
  ust : R (stA u)
  ft : R (core.num.U64.wrapping_add u 3376#u64)
  sc : R (scA u)
  af : R (affA u)
  rest : L.mem X (affA u) = L.cpu X →
    R (core.num.U64.wrapping_add u 3432#u64) ∧ R (inqA u) ∧ R (prioA u) ∧
      ∀ usc, obj.Tcb.sc st u X = ok usc → RdHead (L := L) R X usc

/-- **The words a declining ReplyRecv arm reads** at its entry state `X` (current thread `t`,
reply object `rptr`, endpoint `ep`). -/
structure RrDec (R : U64 → Prop) (X : S) (t rptr ep : U64) : Prop where
  nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt X (L.cpu X) o)
  dt : R (core.num.U64.wrapping_add (L.ksb X) layout.ks.DOMAIN_TIME)
  cd : R (core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN)
  bm : RdBitmap (L := L) R X
  tm : L.mem X (tmA (L := L) X) ≠ 0#u64 → R (core.num.U64.wrapping_add (L.mem X (tmA (L := L) X)) 3528#u64)
  rh : L.mem X (rhA (L := L) X) ≠ 0#u64 → R (scA (L.mem X (rhA (L := L) X))) ∧
    RdHead (L := L) R X (L.mem X (scA (L.mem X (rhA (L := L) X))))
  tSt : R (stA t)
  tSc : R (scA t)
  tMx : R (maxA (L.mem X (scA t)))
  tIq : R (inqA t)
  tMi : R (regA t layout.reg.MSG_INFO)
  tBn : R (core.num.U64.wrapping_add t 3368#u64)
  tPr : R (prioA t)
  ntf : ∀ n, obj.Tcb.bound_ntfn st t X = ok n → (n != 0#u64) = true →
    R (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE) ∧ R (core.num.U64.wrapping_add n layout.ntfn.SC)
  rRt : R (rTcbA rptr)
  rNx : R (rNextA rptr)
  eTS : R (epTSA ep)
  uu : ∀ u, obj.Reply.tcb st rptr X = ok u → UDec (L := L) R X u

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **A declined ReplyRecv arm on the guarded store** (`R` holding `RrDec`). -/
theorem fastpath.reply_recv_found.guard_dec {X : S} {a : A} {t rptr ep : U64} {r : Bool × S × A}
    (D : RrDec (L := L) R X t rptr ep) (h : fastpath.reply_recv_found st ar X a t rptr ep = ok r)
    (hn : r.1 ≠ true) :
    fastpath.reply_recv_found gS ar X a t rptr ep = ok r := by
  unfold fastpath.reply_recv_found at h ⊢
  revert h
  rw [sched.action.guard (gS := gS) X (D.nd _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))]
  refine tr_bind_same (fun i _ => ?_)
  refine tr_ite (fun _ h' => h') (fun _ => ?_)
  rw [sched.is_schedulable.guard (gS := gS) X t D.tSt D.tSc D.tMx D.tIq]
  refine tr_bind_same (fun b _ => ?_)
  refine tr_ite (fun _ => ?_) (fun _ h' => h')
  rw [msg.msg_info.guard (gS := gS) X t D.tMi]
  refine tr_bind_same (fun info _ => ?_)
  refine tr_ite (fun _ h' => h') (fun _ => ?_)
  refine tr_ite (fun _ h' => h') (fun _ => ?_)
  rw [obj.Reply.tcb.guard (gS := gS) rptr X D.rRt]
  refine tr_bind_same (fun u eu => ?_)
  have U := D.uu u eu
  refine tr_bind_same (fun b1 _ => ?_)
  refine tr_ite (fun _ h' => h') (fun _ => ?_)
  rw [obj.Tcb.state.guard (gS := gS) u X U.ust]
  refine tr_bind_same (fun i2 _ => ?_)
  refine tr_ite (fun _ h' => h') (fun _ => ?_)
  rw [obj.Tcb.fault_type.guard (gS := gS) u X U.ft]
  refine tr_bind_same (fun i3 _ => ?_)
  refine tr_ite (fun _ h' => h') (fun _ => ?_)
  rw [obj.Reply.next.guard (gS := gS) X rptr D.rNx]
  refine tr_bind_same (fun i4 _ => ?_)
  refine tr_ite (fun _ => ?_) (fun _ => ?_)
  · rw [obj.Reply.next_is_head.guard (gS := gS) X rptr D.rNx]
    refine tr_bind_same (fun b2 _ => ?_)
    refine tr_ite (fun _ h' => h') (fun _ => ?_)
    rw [obj.Tcb.sc.guard (gS := gS) u X U.sc]
    refine tr_bind_same (fun i5 e5 => ?_)
    refine tr_bind_same (fun b3 _ => ?_)
    refine tr_ite (fun _ h' => h') (fun _ => ?_)
    rw [fastpath.schedulable_here.guard' (gS := gS) X u
      (D.nd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
      (D.nd _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]))
      (D.nd _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]))
      D.tm D.rh D.dt D.cd U.af (fun h => ⟨(U.rest h).1, U.sc, (U.rest h).2.1⟩)]
    refine tr_bind_same (fun b4 hb4 => ?_)
    refine tr_ite (fun hbt => ?_) (fun _ h' => h')
    have HF := here_facts (L := L) (show fastpath.schedulable_here st X u = ok true by rw [hb4, hbt])
    obtain ⟨-, -, hpu, hhd⟩ := U.rest HF.aff
    rw [sporadic.ready.guard (gS := gS) X i5 (hhd i5 e5)
      (D.nd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))]
    refine tr_bind_same (fun b5 _ => ?_)
    refine tr_ite (fun _ => ?_) (fun _ h' => h')
    rw [sporadic.sufficient.guard (gS := gS) ar X a i5 0#u64 (hhd i5 e5)]
    refine tr_bind_same (fun b6 _ => ?_)
    refine tr_ite (fun _ => ?_) (fun _ h' => h')
    rw [obj.Tcb.bound_ntfn.guard (gS := gS) t X D.tBn]
    refine tr_bind_same (fun i6 e6 => ?_)
    refine tr_ite (fun h6 => ?_) (fun _ => ?_)
    · rw [obj.Ntfn.state.guard (gS := gS) i6 X (D.ntf i6 e6 h6).1]
      refine tr_bind_same (fun i7 _ => ?_)
      refine tr_ite (fun _ h' => h') (fun _ => ?_)
      rw [obj.Ntfn.sc.guard (gS := gS) i6 X (D.ntf i6 e6 h6).2]
      refine tr_bind_same (fun i8 _ => ?_)
      refine tr_ite (fun _ => ?_) (fun _ => ?_)
      · rw [obj.Tcb.sc.guard (gS := gS) t X D.tSc]
        refine tr_bind_same (fun i9 _ => ?_)
        refine tr_ite (fun _ h' => h') (fun _ => ?_)
        rw [obj.Ep.state.guard (gS := gS) ep X D.eTS]
        refine tr_bind_same (fun i10 _ => ?_)
        refine tr_ite (fun _ h' => h') (fun _ => ?_)
        rw [sched.idle_thread.guard (gS := gS) X (D.nd _ (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD]))]
        refine tr_bind_same (fun t1 _ => ?_)
        refine tr_bind_same (fun b7 _ => ?_)
        rw [obj.Tcb.prio.guard (gS := gS) u X hpu, obj.Tcb.prio.guard (gS := gS) t X D.tPr]
        refine tr_bind_same (fun ff _ => ?_)
        refine tr_ite (fun _ => ?_) (fun _ => ?_)
        · rw [sched.cur_domain.guard (gS := gS) X D.cd]
          refine tr_bind_same (fun i11 _ => ?_)
          refine tr_bind_same (fun i12 _ => ?_)
          rw [sched.is_highest_prio.guard (gS := gS) X _ _ D.bm]
          refine tr_bind_same (fun b8 _ => ?_)
          refine tr_ite (fun _ => ?_) (fun _ h' => h')
          intro hk
          exfalso
          apply hn
          acc_true hk
        · intro hk
          exfalso
          apply hn
          acc_true hk
      · rw [obj.Ep.state.guard (gS := gS) ep X D.eTS]
        refine tr_bind_same (fun i10 _ => ?_)
        refine tr_ite (fun _ h' => h') (fun _ => ?_)
        rw [sched.idle_thread.guard (gS := gS) X (D.nd _ (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD]))]
        refine tr_bind_same (fun t1 _ => ?_)
        refine tr_bind_same (fun b7 _ => ?_)
        rw [obj.Tcb.prio.guard (gS := gS) u X hpu, obj.Tcb.prio.guard (gS := gS) t X D.tPr]
        refine tr_bind_same (fun ff _ => ?_)
        refine tr_ite (fun _ => ?_) (fun _ => ?_)
        · rw [sched.cur_domain.guard (gS := gS) X D.cd]
          refine tr_bind_same (fun i11 _ => ?_)
          refine tr_bind_same (fun i12 _ => ?_)
          rw [sched.is_highest_prio.guard (gS := gS) X _ _ D.bm]
          refine tr_bind_same (fun b8 _ => ?_)
          refine tr_ite (fun _ => ?_) (fun _ h' => h')
          intro hk
          exfalso
          apply hn
          acc_true hk
        · intro hk
          exfalso
          apply hn
          acc_true hk
    · rw [obj.Ep.state.guard (gS := gS) ep X D.eTS]
      refine tr_bind_same (fun i10 _ => ?_)
      refine tr_ite (fun _ h' => h') (fun _ => ?_)
      rw [sched.idle_thread.guard (gS := gS) X (D.nd _ (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD]))]
      refine tr_bind_same (fun t1 _ => ?_)
      refine tr_bind_same (fun b7 _ => ?_)
      rw [obj.Tcb.prio.guard (gS := gS) u X hpu, obj.Tcb.prio.guard (gS := gS) t X D.tPr]
      refine tr_bind_same (fun ff _ => ?_)
      refine tr_ite (fun _ => ?_) (fun _ => ?_)
      · rw [sched.cur_domain.guard (gS := gS) X D.cd]
        refine tr_bind_same (fun i11 _ => ?_)
        refine tr_bind_same (fun i12 _ => ?_)
        rw [sched.is_highest_prio.guard (gS := gS) X _ _ D.bm]
        refine tr_bind_same (fun b8 _ => ?_)
        refine tr_ite (fun _ => ?_) (fun _ h' => h')
        intro hk
        exfalso
        apply hn
        acc_true hk
      · intro hk
        exfalso
        apply hn
        acc_true hk
  · rw [obj.Tcb.sc.guard (gS := gS) u X U.sc]
    refine tr_bind_same (fun i5 e5 => ?_)
    refine tr_bind_same (fun b3 _ => ?_)
    refine tr_ite (fun _ h' => h') (fun _ => ?_)
    rw [fastpath.schedulable_here.guard' (gS := gS) X u
      (D.nd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
      (D.nd _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]))
      (D.nd _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]))
      D.tm D.rh D.dt D.cd U.af (fun h => ⟨(U.rest h).1, U.sc, (U.rest h).2.1⟩)]
    refine tr_bind_same (fun b4 hb4 => ?_)
    refine tr_ite (fun hbt => ?_) (fun _ h' => h')
    have HF := here_facts (L := L) (show fastpath.schedulable_here st X u = ok true by rw [hb4, hbt])
    obtain ⟨-, -, hpu, hhd⟩ := U.rest HF.aff
    rw [sporadic.ready.guard (gS := gS) X i5 (hhd i5 e5)
      (D.nd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))]
    refine tr_bind_same (fun b5 _ => ?_)
    refine tr_ite (fun _ => ?_) (fun _ h' => h')
    rw [sporadic.sufficient.guard (gS := gS) ar X a i5 0#u64 (hhd i5 e5)]
    refine tr_bind_same (fun b6 _ => ?_)
    refine tr_ite (fun _ => ?_) (fun _ h' => h')
    rw [obj.Tcb.bound_ntfn.guard (gS := gS) t X D.tBn]
    refine tr_bind_same (fun i6 e6 => ?_)
    refine tr_ite (fun h6 => ?_) (fun _ => ?_)
    · rw [obj.Ntfn.state.guard (gS := gS) i6 X (D.ntf i6 e6 h6).1]
      refine tr_bind_same (fun i7 _ => ?_)
      refine tr_ite (fun _ h' => h') (fun _ => ?_)
      rw [obj.Ntfn.sc.guard (gS := gS) i6 X (D.ntf i6 e6 h6).2]
      refine tr_bind_same (fun i8 _ => ?_)
      refine tr_ite (fun _ => ?_) (fun _ => ?_)
      · rw [obj.Tcb.sc.guard (gS := gS) t X D.tSc]
        refine tr_bind_same (fun i9 _ => ?_)
        refine tr_ite (fun _ h' => h') (fun _ => ?_)
        rw [obj.Ep.state.guard (gS := gS) ep X D.eTS]
        refine tr_bind_same (fun i10 _ => ?_)
        refine tr_ite (fun _ h' => h') (fun _ => ?_)
        rw [sched.idle_thread.guard (gS := gS) X (D.nd _ (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD]))]
        refine tr_bind_same (fun t1 _ => ?_)
        refine tr_bind_same (fun b7 _ => ?_)
        rw [obj.Tcb.prio.guard (gS := gS) u X hpu, obj.Tcb.prio.guard (gS := gS) t X D.tPr]
        refine tr_bind_same (fun ff _ => ?_)
        refine tr_ite (fun _ => ?_) (fun _ => ?_)
        · rw [sched.cur_domain.guard (gS := gS) X D.cd]
          refine tr_bind_same (fun i11 _ => ?_)
          refine tr_bind_same (fun i12 _ => ?_)
          rw [sched.is_highest_prio.guard (gS := gS) X _ _ D.bm]
          refine tr_bind_same (fun b8 _ => ?_)
          refine tr_ite (fun _ => ?_) (fun _ h' => h')
          intro hk
          exfalso
          apply hn
          acc_true hk
        · intro hk
          exfalso
          apply hn
          acc_true hk
      · rw [obj.Ep.state.guard (gS := gS) ep X D.eTS]
        refine tr_bind_same (fun i10 _ => ?_)
        refine tr_ite (fun _ h' => h') (fun _ => ?_)
        rw [sched.idle_thread.guard (gS := gS) X (D.nd _ (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD]))]
        refine tr_bind_same (fun t1 _ => ?_)
        refine tr_bind_same (fun b7 _ => ?_)
        rw [obj.Tcb.prio.guard (gS := gS) u X hpu, obj.Tcb.prio.guard (gS := gS) t X D.tPr]
        refine tr_bind_same (fun ff _ => ?_)
        refine tr_ite (fun _ => ?_) (fun _ => ?_)
        · rw [sched.cur_domain.guard (gS := gS) X D.cd]
          refine tr_bind_same (fun i11 _ => ?_)
          refine tr_bind_same (fun i12 _ => ?_)
          rw [sched.is_highest_prio.guard (gS := gS) X _ _ D.bm]
          refine tr_bind_same (fun b8 _ => ?_)
          refine tr_ite (fun _ => ?_) (fun _ h' => h')
          intro hk
          exfalso
          apply hn
          acc_true hk
        · intro hk
          exfalso
          apply hn
          acc_true hk
    · rw [obj.Ep.state.guard (gS := gS) ep X D.eTS]
      refine tr_bind_same (fun i10 _ => ?_)
      refine tr_ite (fun _ h' => h') (fun _ => ?_)
      rw [sched.idle_thread.guard (gS := gS) X (D.nd _ (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD]))]
      refine tr_bind_same (fun t1 _ => ?_)
      refine tr_bind_same (fun b7 _ => ?_)
      rw [obj.Tcb.prio.guard (gS := gS) u X hpu, obj.Tcb.prio.guard (gS := gS) t X D.tPr]
      refine tr_bind_same (fun ff _ => ?_)
      refine tr_ite (fun _ => ?_) (fun _ => ?_)
      · rw [sched.cur_domain.guard (gS := gS) X D.cd]
        refine tr_bind_same (fun i11 _ => ?_)
        refine tr_bind_same (fun i12 _ => ?_)
        rw [sched.is_highest_prio.guard (gS := gS) X _ _ D.bm]
        refine tr_bind_same (fun b8 _ => ?_)
        refine tr_ite (fun _ => ?_) (fun _ h' => h')
        intro hk
        exfalso
        apply hn
        acc_true hk
      · intro hk
        exfalso
        apply hn
        acc_true hk

/-- The prefix's words for a declined run on a store guarded to reads `R` and writes `W`. -/
structure PreDec (R W : U64 → Prop) (s : S) : Prop where
  nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o)
  ct : W (ctA (L := L) s)
  cn : W (cnA (L := L) s)
  fl : R (core.num.U64.wrapping_add (L.curW s) 3456#u64)
  nx : R (regA (L.curW s) layout.reg.NEXT_IP)
  fi : W (regA (L.curW s) layout.reg.FAULT_IP)

variable (ar) in
set_option maxHeartbeats 4000000 in
/-- The prefix and the arms of the syscall entry on the guarded store, given the arms. -/
theorem sl_pre_dec {T : Set U64} (hA : P0.ArchTotal ar) {s : S} {a : A} {n : I64} {rp ep : U64}
    {r : Bool × S × A} (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (hcT : L.curW s ∈ T)
    (hp : PreDec (L := L) R W s)
    (hhd : ∀ X a1 csc, LocalPre (st := st) ar s a (X, a1) → sched.cur_sc st X = ok csc →
      RdHead (L := L) R X csc)
    (i1 : U64)
    (hfa : (i1 != 0#u64) = true → ∀ X a1 n', LocalPre (st := st) ar s a (X, a1) →
      fastpath.fault st ar X a1 (L.curW s) n' = ok r → fastpath.fault gS ar X a1 (L.curW s) n' = ok r)
    (hra : ¬ (i1 != 0#u64) = true → ∀ X a1, LocalPre (st := st) ar s a (X, a1) →
      fastpath.reply_recv_found st ar X a1 (L.curW s) rp ep = ok r →
      fastpath.reply_recv_found gS ar X a1 (L.curW s) rp ep = ok r) :
    (do
      let next ← obj.Tcb.reg st (L.curW s) s layout.reg.NEXT_IP
      let i2 ← lift (core.num.U64.wrapping_sub next 2#u64)
      let s1 ← obj.Tcb.set_reg st (L.curW s) s layout.reg.FAULT_IP i2
      let (s2, a1) ← sched.update_timestamp st ar s1 a
      let csc ← sched.cur_sc st s2
      let i3 ← sched.consumed st s2
      let b ← sporadic.sufficient st ar s2 a1 csc i3
      if b then
        if i1 != 0#u64 then do
          let i4 ← lift (IScalar.hcast .U64 n)
          fastpath.fault st ar s2 a1 (L.curW s) i4
        else fastpath.reply_recv_found st ar s2 a1 (L.curW s) rp ep
      else ok (false, s2, a1)) = ok r →
    (do
      let next ← obj.Tcb.reg gS (L.curW s) s layout.reg.NEXT_IP
      let i2 ← lift (core.num.U64.wrapping_sub next 2#u64)
      let s1 ← obj.Tcb.set_reg gS (L.curW s) s layout.reg.FAULT_IP i2
      let (s2, a1) ← sched.update_timestamp gS ar s1 a
      let csc ← sched.cur_sc gS s2
      let i3 ← sched.consumed gS s2
      let b ← sporadic.sufficient gS ar s2 a1 csc i3
      if b then
        if i1 != 0#u64 then do
          let i4 ← lift (IScalar.hcast .U64 n)
          fastpath.fault gS ar s2 a1 (L.curW s) i4
        else fastpath.reply_recv_found gS ar s2 a1 (L.curW s) rp ep
      else ok (false, s2, a1)) = ok r := by
  have ht' := hT _ hcT
  rw [obj.Tcb.reg.guard (gS := gS) _ _ _ hp.nx]
  refine tr_bind_same (fun nx enx => ?_)
  simp only [lift, bind_ok]
  rw [obj.Tcb.set_reg.guard (gS := gS) _ _ _ _ hp.fi]
  refine tr_bind_same (fun s1 es1 => ?_)
  have e1 := set_fip_wr ht' es1
  have hk1 : L.ksb s1 = L.ksb s := by rw [e1, L.ksb_wr]
  have hc1 : L.cpu s1 = L.cpu s := by rw [e1, LawfulStore.cpu_wr]
  have n1 : ∀ o, L.nodeAt s1 (L.cpu s1) o = L.nodeAt s (L.cpu s) o := fun o => by rw [hc1, nodeAt_of_ksb hk1]
  have rct : R (ctA (L := L) s1) := by
    show R (L.nodeAt s1 (L.cpu s1) layout.node.CUR_TIME)
    rw [n1]; exact hp.nd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
  have rcn : R (cnA (L := L) s1) := by
    show R (L.nodeAt s1 (L.cpu s1) layout.node.CONSUMED)
    rw [n1]; exact hp.nd _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
  have wct : W (ctA (L := L) s1) := by
    show W (L.nodeAt s1 (L.cpu s1) layout.node.CUR_TIME)
    rw [n1]; exact hp.ct
  have wcn : W (cnA (L := L) s1) := by
    show W (L.nodeAt s1 (L.cpu s1) layout.node.CONSUMED)
    rw [n1]; exact hp.cn
  rw [sched.update_timestamp.guard (gS := gS) ar s1 a rct wct rcn wcn]
  refine tr_bind_same (fun q eu => ?_)
  obtain ⟨s2, a1⟩ := q
  simp only [uncurry_apply_pair]
  have hP : LocalPre (st := st) ar s a (s2, a1) := ⟨_, nx, s1, cur_thread_ok s, enx, es1, eu⟩
  obtain ⟨hk2, hc2, -⟩ := sl_pre_agree (Cs := ∅) ar hA hT hN hcT hP
  have nd2 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s2 (L.cpu s2) o) := fun o h1 h2 => by
    rw [hc2, nodeAt_of_ksb hk2]; exact hp.nd o h1 h2
  rw [sched.cur_sc.guard (gS := gS) s2 (nd2 _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))]
  refine tr_bind_same (fun csc ecsc => ?_)
  rw [sched.consumed.guard (gS := gS) s2 (nd2 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))]
  refine tr_bind_same (fun i3 _ => ?_)
  rw [sporadic.sufficient.guard (gS := gS) ar s2 a1 csc i3 (hhd _ _ _ hP ecsc)]
  refine tr_bind_same (fun b _ => ?_)
  exact tr_ite (fun _ => tr_ite (fun h1 => hfa h1 _ _ _ hP)
    (fun h1 => hra h1 _ _ hP)) (fun _ h' => h')

set_option maxHeartbeats 4000000 in
/-- **A run of the syscall entry on the guarded store**, given its arms on it (`R` / `W`
holding `PreDec` and the head refill of the current SC). -/
theorem syscall.handle_syscall_local.guard_dec {T : Set U64} (hA : P0.ArchTotal ar)
    {s : S} {a : A} {n : I64} {found : U64 × U64} {r : Bool × S × A}
    (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (hcT : L.curW s ∈ T)
    (hp : PreDec (L := L) R W s)
    (hhd : ∀ X a1 csc, LocalPre (st := st) ar s a (X, a1) → sched.cur_sc st X = ok csc →
      RdHead (L := L) R X csc)
    (hfa : SlTrap st s → ∀ X a1 n', LocalPre (st := st) ar s a (X, a1) →
      fastpath.fault st ar X a1 (L.curW s) n' = ok r → fastpath.fault gS ar X a1 (L.curW s) n' = ok r)
    (hra : ¬ SlTrap st s → ∀ X a1, LocalPre (st := st) ar s a (X, a1) →
      fastpath.reply_recv_found st ar X a1 (L.curW s) found.1 found.2 = ok r →
      fastpath.reply_recv_found gS ar X a1 (L.curW s) found.1 found.2 = ok r)
    (h : syscall.handle_syscall_local st ar s a n found = ok r) :
    syscall.handle_syscall_local gS ar s a n found = ok r := by
  obtain ⟨rp, ep⟩ := found
  unfold syscall.handle_syscall_local at h ⊢
  revert h
  rw [sched.cur_thread.guard (gS := gS) s (hp.nd _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])),
    cur_thread_ok]
  simp only [bind_ok]
  rw [obj.Tcb.flags.guard (gS := gS) _ _ hp.fl]
  refine tr_bind_same (fun i ei => ?_)
  refine tr_bind_same (fun i1 ei1 => ?_)
  have e1 : i &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS = i1 := ok_inj_ff ei1
  have ht : (i1 != 0#u64) = true → SlTrap st s := fun h => ⟨i, ei, by rw [e1]; exact h⟩
  have hnt : ¬ (i1 != 0#u64) = true → ¬ SlTrap st s := fun h ⟨f, ef, hf'⟩ =>
    h (by rw [← e1, ok_inj_ff (ei.symm.trans ef)]; exact hf')
  have hpd := sl_pre_dec ar hA hT hN hcT hp hhd (n := n) (rp := rp) (ep := ep) i1 (fun h1 => hfa (ht h1)) (fun h1 => hra (hnt h1))
  exact tr_ite (fun _ h' => h') (fun _ => tr_ite (fun _ => hpd) (fun _ => tr_ite (fun _ h' => h') (fun _ => hpd)))

end

end Fl4Proofs.P2.PathObl
