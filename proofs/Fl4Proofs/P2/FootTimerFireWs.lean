/-
# P2 (p2lf): a fired timer's waking signal, on `st`: what it writes and the action it leaves

The two waking branches of `send_signal` (`P2/FootTimerFireWk`) on the real store, from facts at their start state
`X` only (P1's queue invariant `SchedQueuesInvX` / `EpsWit` and `wakeTail`'s facts `WkPre` at `X`, any read / write
sets, e.g. `fun _ => True`):

* `wake_wait_st`: a `WAITING` notification `n` whose queue head is `w`: the run returns the `Arch` unchanged, writes
  only the queue's links and `n`'s queue words (`EpFoot`), `w`'s `STATE` and badge register and this core's
  `SCHED_ACTION` (`WkD`), `w`'s SC ring and this core's `REPROGRAM`, and leaves the action `RESUME_CURRENT` or `w`.
* `wake_recv_st`: an idle notification whose bound thread `t` waits in `Recv` on `ep` with reply `r`: the same with
  `cancel_ipc`'s writes (`CnD`: `t`'s fault word, the endpoint queue's footprint, the reply's `TCB` word, `t`'s
  `STATE`).

* (lvm gen 10) `wake_wait_st` also gives: the notification is not left `ACTIVE` (`ntfn_dequeue.rel`: idle or
  unchanged `WAITING`; `wakeTail` writes none of its words), when the SC ring size is 0 for a null SC.
No named premises.
-/
import Fl4Proofs.P2.FootTimerFireWt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (bind_guard_congr NodeSt ScAcc)

section st
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {T Cs Ω : Set U64} {H : Heap}

set_option maxHeartbeats 8000000 in
/-- **The `WAITING` branch of a fired timer's `send_signal` on `st`** (module docstring). -/
theorem wake_wait_st {A : Type} (ar : machine.Arch A) (X : S) (a : A) (n badge w : U64) {sb : Nat}
    {Xs E : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {EQ : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H Xs X Q Rq) (hEW : EpsWit st T Cs Ω H Xs X E EQ) (he : n ∈ E)
    (hwt : L.epState X n = obj.NTFN_WAITING) (hwq : (L.epQ X n).head = w) (hmem : w ∈ EQ n)
    (hcur : w ≠ L.curW X) (hac : L.actionW X = sched.ACTION_RESUME_CURRENT)
    (P : WkPre st R W X w n sb) (hnsΩ : ntfnScA n ∈ Ω)
    (hscΩ : L.mem X (scA w) ≠ 0#u64 → ∀ b, Aligned b → InSC (L.mem X (scA w)) sb b → b ∈ Ω)
    (hAo : Outside (L.nodeA X layout.node.SCHED_ACTION) (L.mem X (scA w)) sb)
    {X' : S} {a' : A} (hr : notification.send_signal st ar X a n badge = ok (X', a')) :
    a' = a ∧
      WritesIn st X X' (fun b => EpFoot (EQ n) n b ∨ WkD st X w b ∨ InRing (L.mem X (scA w)) sb b ∨
        b = L.nodeA X layout.node.REPROGRAM) ∧
      (L.actionW X' = sched.ACTION_RESUME_CURRENT ∨ L.actionW X' = w) ∧ L.mem X' (stA w) = sched.TS_RUNNING ∧
      ((L.mem X (scA w) = 0#u64 → sb = 0) → L.epState X' n ≠ obj.NTFN_ACTIVE) := by
  obtain ⟨hE, hEN, hq⟩ := hEW.1 n he
  have hT := h.tcbs
  have hw : w ∈ T := hq.mem w hmem
  have ht' := hT w hw
  have hcC := h.cur
  have hN : NodePlaced st T X (L.cpu X) := h.nodes _ hcC
  have eS : obj.Ntfn.state st n X = ok obj.NTFN_WAITING := by
    rw [eq_of_spec_fd (obj.Ntfn.state.spec (L := L) X n), hwt]
  rw [send_signal_wait st ar X a n badge eS, eq_of_spec_fd (notification.get_queue.spec (L := L) X n)] at hr
  simp only [bind_ok] at hr
  rw [hwq] at hr
  obtain ⟨X1, hX1, hr⟩ := bind_eq_ok hr
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
  have aA : Aligned (L.nodeAt X1 (L.cpu X1) layout.node.SCHED_ACTION) :=
    nodeAt_aligned hN1 (by rw [act_val]; omega) (by rw [act_val])
  have aC : Aligned (L.nodeAt X1 (L.cpu X1) layout.node.CUR_THREAD) :=
    nodeAt_aligned hN1 (by rw [curth_val]; omega) (by rw [curth_val])
  have nF : ∀ o K : U64, o.val < 4288 → K.val < 4096 → L.nodeAt X1 (L.cpu X1) o ≠ core.num.U64.wrapping_add w K :=
    fun o K ho hK => node_ne_field hN1 ho hw ht' hK
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
  have hcur1 : L.curW X1 = L.curW X := by
    unfold LawfulStore.curW
    exact kN layout.node.CUR_THREAD (by rw [curth_val]; omega) (by rw [curth_val])
  have hac1 : L.actionW X1 = L.actionW X := by
    unfold LawfulStore.actionW
    exact kN layout.node.SCHED_ACTION (by rw [act_val]; omega) (by rw [act_val])
  have sc1 : L.mem X1 (scA w) = L.mem X (scA w) := by
    rw [scA_eq]; exact kT w hw _ (by simp) (by simp) (by simp) (by simp)
  have nA1 : ∀ o, L.nodeA X1 o = L.nodeA X o := fun o => e1N o
  have hY : ∀ Y, WritesIn st X1 Y (WkD st X1 w) → WkPre st R W Y w n sb := by
    intro Y wY
    refine P.agree (wY.1.trans k1) (wY.2.1.trans c1) ?_ (oK Y _ wY hnsΩ) ?_ (cdK Y wY) ?_
      (fun h0 b hb hin => oK Y b wY (hscΩ h0 b hb hin))
    · rw [scA_eq]; exact tK Y 3464#u64 wY (by simp) (by simp) (by simp) (by simp) (by simp) (by rw [hKB']; simp)
    · exact tK Y 3432#u64 wY (by simp) (by simp) (by simp) (by simp) (by simp) (by rw [hKB']; simp)
    · exact tK Y 3520#u64 wY (by simp) (by simp) (by simp) (by simp) (by simp) (by rw [hKB']; simp)
  obtain ⟨ea, wT, acT, rT⟩ := wakeTail_st (R' := R) (W' := W) ar X1 a w n badge (sb := sb) (by rw [hcur1]; exact hcur)
    aS aR aA
    (fun e => nF _ 3328#u64 (by rw [act_val]; omega) (by simp) (by rw [← stA_eq]; exact e))
    (fun e => nF _ KB (by rw [act_val]; omega) (by omega) (by rw [← eKB]; exact e)) aC
    (fun e => nF _ 3328#u64 (by rw [curth_val]; omega) (by simp) (by rw [← stA_eq]; exact e))
    (by rw [nA1, sc1]; exact hAo)
    (by
      rw [nA1, nA1]
      exact nodeAt_ne hN (by rw [act_val]; omega) (by simp [layout.node.REPROGRAM])
        (by rw [act_val]; simp [layout.node.REPROGRAM]))
    (fun Y wY => by
      rw [scA_eq]
      exact (tK Y 3464#u64 wY (by simp) (by simp) (by simp) (by simp) (by simp) (by rw [hKB']; simp)).trans
        (kT w hw _ (by simp) (by simp) (by simp) (by simp)).symm)
    (by rw [hac1]; exact hac) hY
    (by rw [eKB, stA_eq]; exact tcb_word_ne ht' ht' (by omega) (by simp) (fun _ h => by simp at h; omega))
    (by
      rw [sc1]; intro h0 b hb e; subst e
      exact out_ne_field (h.omega _ (hscΩ h0 _ aS hb.inSC)) hw ht' (K := 3328#u64) (by simp) (by rw [← stA_eq]))
    (fun e => nF layout.node.REPROGRAM 3328#u64 (by simp [layout.node.REPROGRAM]) (by simp) (by rw [← stA_eq]; exact e)) hr
  refine ⟨ea, (wi.trans wT).mono fun b hb => ?_, acT, rT, fun hsb => ?_⟩
  rotate_left
  · -- lvm gen 10: the dequeue leaves `n` idle or waiting, and the rest writes none of its words
    have hrel := notification.ntfn_dequeue.rel (st := st) X n w (EQ n) hT hE hq hmem
    rw [hX1, WP.spec_ok] at hrel
    have eS1 : L.epState X1 n ≠ obj.NTFN_ACTIVE := by
      rw [hrel.2]
      split
      · unfold obj.NTFN_ACTIVE; decide
      · rw [hwt]; unfold obj.NTFN_ACTIVE obj.NTFN_WAITING; decide
    have aT : Aligned (epTSA n) := (ep_aligned hE).2
    have oT : OutsideObjs st T Cs X1 (epTSA n) := (ep_out hE hEN).2.ksb k1
    have nΩ : epTSA n ∉ Ω := fun hΩ => by
      have := hEW.2.2.1 n he _ hΩ
      rw [epTSA_val hE] at this
      omega
    have eT : L.mem X' (epTSA n) = L.mem X1 (epTSA n) := by
      refine wT.mem_eq aT ?_
      rintro ((e | e | e) | hr' | e)
      · rw [stA_eq] at e; exact out_ne_field oT hw ht' (by simp) (congrArg UScalar.val e).symm
      · rw [eKB] at e; exact out_ne_field oT hw ht' (by omega) (congrArg UScalar.val e).symm
      · exact out_ne_node oT (by rw [c1]; exact hcC) hN1 (by rw [act_val]; omega) (congrArg UScalar.val e).symm
      · by_cases h0 : L.mem X1 (scA w) = 0#u64
        · rw [sc1] at h0
          have := hsb h0
          subst this
          have i1 := hr'.1; have i2 := hr'.2
          simp only [pow_zero] at i2
          omega
        · rw [sc1] at h0 hr'
          exact nΩ (hscΩ h0 _ aT hr'.inSC)
      · exact out_ne_node oT (by rw [c1]; exact hcC) hN1 (by simp [layout.node.REPROGRAM]) (congrArg UScalar.val e).symm
    unfold LawfulStore.epState at eS1 ⊢
    rw [eT]; exact eS1
  rcases hb with hb | hb | hb | hb
  · exact Or.inl hb
  · refine Or.inr (Or.inl ?_)
    unfold WkD at hb ⊢
    rw [e1N] at hb; exact hb
  · rw [sc1] at hb; exact Or.inr (Or.inr (Or.inl hb))
  · rw [nA1] at hb; exact Or.inr (Or.inr (Or.inr hb))


set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
/-- **The idle-bound `Recv` branch of a fired timer's `send_signal` on `st`** (module docstring): `t` the
notification's bound thread, waiting in `Recv` on `ep` with reply `r`. -/
theorem wake_recv_st {A : Type} (ar : machine.Arch A) (X : S) (a : A) (n badge t ep r : U64) {sb : Nat}
    {Xs E : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {EQ : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H Xs X Q Rq) (hEW : EpsWit st T Cs Ω H Xs X E EQ)
    (hidle : L.epState X n = obj.NTFN_IDLE) (hbt : L.mem X (ntfnBtA n) = t) (ht0 : t ≠ 0#u64)
    (hrecv : L.mem X (stA t) = sched.TS_BLOCKED_ON_RECV)
    (heq : L.mem X (blockA t) = ep) (hep : ep ∈ E) (hmem : t ∈ EQ ep) (hr : L.mem X (replyA t) = r)
    (aRt : r ≠ 0#u64 → Aligned (rTcbA r))
    (hcur : t ≠ L.curW X) (hac : L.actionW X = sched.ACTION_RESUME_CURRENT)
    (P : WkPre st R W X t n sb) (hnsΩ : ntfnScA n ∈ Ω)
    (hscΩ : L.mem X (scA t) ≠ 0#u64 → ∀ b, Aligned b → InSC (L.mem X (scA t)) sb b → b ∈ Ω)
    (hRt : r ≠ 0#u64 → ∀ b, (b = ntfnScA n ∨ (Aligned b ∧ InSC (L.mem X (scA t)) sb b) ∨
      b = core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN ∨
      (∃ o : U64, o.val < 4288 ∧ b = L.nodeAt X (L.cpu X) o) ∨
      (∃ K : U64, K.val < 4096 ∧ b = core.num.U64.wrapping_add t K)) → b ≠ rTcbA r)
    (hAo : Outside (L.nodeA X layout.node.SCHED_ACTION) (L.mem X (scA t)) sb)
    {X' : S} {a' : A} (hrun : notification.send_signal st ar X a n badge = ok (X', a')) :
    a' = a ∧
      WritesIn st X X' (fun b => CnD (EQ ep) ep t r b ∨ WkD st X t b ∨ InRing (L.mem X (scA t)) sb b ∨
        b = L.nodeA X layout.node.REPROGRAM) ∧
      (L.actionW X' = sched.ACTION_RESUME_CURRENT ∨ L.actionW X' = t) ∧ L.mem X' (stA t) = sched.TS_RUNNING := by
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
  have wRt : r ≠ 0#u64 → True ∧ Aligned (rTcbA r) := fun h0 => ⟨trivial, aRt h0⟩
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
  -- the run: `cancel_ipc`, then `wakeTail`
  have eS : obj.Ntfn.state st n X = ok obj.NTFN_IDLE := by
    rw [eq_of_spec_fd (obj.Ntfn.state.spec (L := L) X n), hidle]
  have eBt : obj.Ntfn.bound_tcb st n X = ok t := by
    rw [eq_of_spec_fd (obj.Ntfn.bound_tcb.val (L := L) X n), hbt]
  have eT : obj.Tcb.state st t X = ok sched.TS_BLOCKED_ON_RECV := by
    rw [eq_of_spec_fd (obj.Tcb.state.spec (L := L) X t), hrecv]
  rw [send_signal_recv st ar X a n badge eS eBt ht0 eT] at hrun
  obtain ⟨⟨X4, a4⟩, h4, hrun⟩ := bind_eq_ok hrun
  simp only [Aeneas.Std.uncurry_apply_pair] at hrun
  obtain ⟨ea, X2, h2, X3, h3, h5⟩ := cancel_recv_st ar X a t hs h4
  rw [ea] at hrun
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
  have sc4 : L.mem X4 (scA t) = L.mem X (scA t) := by
    rw [scA_eq]
    exact tK X4 3464#u64 (WritesIn.refl _ _) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have nA4 : ∀ o, L.nodeA X4 o = L.nodeA X o := fun o => e4N o
  have hY : ∀ Y, WritesIn st X4 Y (WkD st X4 t) → WkPre st R W Y t n sb := by
    intro Y wY
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
  have hcur4 : t ≠ L.curW X4 := by
    have : L.curW X4 = L.curW X := nodeK X4 wX4 layout.node.CUR_THREAD (by rw [curth_val]; omega) (by rw [curth_val])
    rw [this]; exact hcur
  have hac4 : L.actionW X4 = sched.ACTION_RESUME_CURRENT := by
    have : L.actionW X4 = L.actionW X := nodeK X4 wX4 layout.node.SCHED_ACTION (by rw [act_val]; omega) (by rw [act_val])
    rw [this]; exact hac
  obtain ⟨ea2, wT, acT, rT⟩ := wakeTail_st (R' := R) (W' := W) ar X4 a t n badge (sb := sb) hcur4 aS aR
    (nodeAt_aligned hN4 (by rw [act_val]; omega) (by rw [act_val]))
    (fun e => nF _ 3328#u64 (by rw [act_val]; omega) (by simp) (by rw [← stA_eq]; exact e))
    (fun e => nF _ KB (by rw [act_val]; omega) (by omega) (by rw [← eKB]; exact e))
    (nodeAt_aligned hN4 (by rw [curth_val]; omega) (by rw [curth_val]))
    (fun e => nF _ 3328#u64 (by rw [curth_val]; omega) (by simp) (by rw [← stA_eq]; exact e))
    (by rw [nA4, sc4]; exact hAo)
    (by
      rw [nA4, nA4]
      exact nodeAt_ne hN (by rw [act_val]; omega) (by simp [layout.node.REPROGRAM])
        (by rw [act_val]; simp [layout.node.REPROGRAM]))
    (fun Y wY => by
      rw [scA_eq]
      exact (tK Y 3464#u64 wY (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).trans
        (tK X4 3464#u64 (WritesIn.refl _ _) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
          (by simp)).symm)
    hac4 hY (Ne.symm nSR)
    (by
      rw [sc4]; intro h0 b hb e; subst e
      exact out_ne_field (h.omega _ (hscΩ h0 _ aS hb.inSC)) ht ht' (K := 3328#u64) (by simp) (by rw [← stA_eq]))
    (fun e => nF layout.node.REPROGRAM 3328#u64 (by simp [layout.node.REPROGRAM]) (by simp) (by rw [← stA_eq]; exact e)) hrun
  refine ⟨ea2, (wX4.trans wT).mono fun b hb => ?_, acT, rT⟩
  rcases hb with hb | hb | hb | hb
  · exact Or.inl hb
  · refine Or.inr (Or.inl ?_)
    unfold WkD at hb ⊢
    rw [e4N] at hb; exact hb
  · rw [sc4] at hb; exact Or.inr (Or.inr (Or.inl hb))
  · rw [nA4] at hb; exact Or.inr (Or.inr (Or.inr hb))

end st

end Fl4Proofs.P2
