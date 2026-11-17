/-
P3 (DESIGN.md §9), IPC: **`cancel_all_signals` on `IRel`** (a notification's
finalisation: every thread waiting on it restarted).

FL4 walks the notification's queue from its head, reading each thread's
successor before the thread's step (`ntfn_dequeue`, `set_thread_state
Restart`, `unblock_sporadic`, `possible_switch_to`); the spec runs
`remove_and_restart_ntfn_queued_thread` over the queue (`mapM_x`), then
`reschedule_required`.

* `ntfn_restart_irel`: one thread's step, the head of the notification's
  queue (the dequeue as `cancel_ipc_ntfnI`'s, the restart, the sporadic
  unblock by `unblock_irel`, the switch by `switch_top`).
* `cancel_all_signals_irel`: the loop, by the queue still to visit (the
  notification's queue itself), the spec's outcomes from it included in
  the whole's (`mapMx`); FL4's fuel (`WALK_FUEL`) exceeds any queue.

Every slot is kept (`SlotsSame`, from the steps' footprints:
`unblock_sporadic_tfoot` for the sporadic unblock).

Named, as for `cancel_badged_irel`: the switch target ready (`ActReady`)
at every `IRel` state, the notification in `N`.
-/
import Fl4Proofs.P3.IpcCancelBadged
import Fl4Proofs.P3.IpcCancelAll
import Fl4Proofs.P3.IpcSlotsSame
import Fl4Proofs.P3.DomSched
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section Step
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

open Fl4Spec in
/-- One step of the spec's loop. -/
abbrev rrn (n : U64) (t : ObjRef) : SMonad Unit Unit := removeAndRestartNtfnQueuedThread t n.bv

/-- **`unblock_sporadic` writes in the SC code's footprint** (`TFoot`): the
SC's words (`unblock_check_scw`), or nothing. -/
theorem unblock_sporadic_tfoot {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ) (t : U64)
    (ht : t ∈ T) : notification.unblock_sporadic st s t ⦃ s' => WritesIn st s s' (TFoot st T N C c s σ) ⦄ := by
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  unfold notification.unblock_sporadic
  step with Fl4Proofs.P1.obj.Tcb.sc.spec as ⟨i2, hi2⟩
  step with sporadic.sc_sporadic.spec' as ⟨b, b_post⟩
  subst hi2
  by_cases h0 : L.mem s (scA t) = 0#u64
  · have hb : b = false := by rw [b_post]; simp [h0]
    simp only [hb, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact WritesIn.refl _ _
  have hscC := hs.scMem t ht h0
  obtain ⟨y, n, hky, hy⟩ := hs.scs _ hscC
  by_cases hsp' : L.mem s (scW (L.mem s (scA t)) 64#u64) ≠ 0#u64
  swap
  · have hb : b = false := by rw [b_post]; simp [h0]; simpa using hsp'
    simp only [hb, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact WritesIn.refl _ _
  have hb : b = true := by rw [b_post]; simp [h0, hsp']
  simp only [hb, ↓reduceIte]
  step with sched.cur_sc.spec' as ⟨s1, s1_post⟩
  rw [sc_ne_eq]
  simp only [bind_ok]
  rw [s1_post, hc.cur]
  by_cases e : L.mem s (scA t) = nodeW st s c layout.node.CUR_SC
  · simp only [e, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact WritesIn.refl _ _
  · simp only [e, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
    refine WP.spec_mono (unblock_check_scw hS hscC (hy.spor hsp')) fun s' hw => hw.mono fun b hb => ?_
    rcases hb with h | h
    · exact Or.inl (KFoot.of_sw h)
    · exact Or.inl (KFoot.of_sfoot (Or.inr h))

set_option maxHeartbeats 8000000 in
/-- **One waiting thread of a notification restarted** (the head `t` of its
queue `t :: rest`) on `IRel`: the notification's queue `rest` after. -/
theorem ntfn_restart_irel (hP0 : IPlaced N T E R B)
    (hAct : ∀ s σ, IRel st th cr N T C E R B c s σ → ActReady σ)
    (s : S) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ) {n : U64} (hnN : n ∈ N)
    {xn : Fl4Spec.Notification} (hkn : σ.kheap n.bv = some (.notification xn)) {t : U64} {rest : List U64}
    (hq : Fl4Spec.ntfnQueueOf xn = (t :: rest).map UScalar.bv) {γ : Type} (k : S → Result γ) {Q : γ → Prop}
    (hkont : ∀ s' σ' xn', ((), σ') ∈ (rrn n t.bv σ).1 → IRel st th cr N T C E R B c s' σ' →
      σ'.kheap n.bv = some (.notification xn') → Fl4Spec.ntfnQueueOf xn' = rest.map UScalar.bv →
      SlotsSame th (L.mem s) (L.mem s') → k s' ⦃ Q ⦄) :
    (do
      let s1 ← notification.ntfn_dequeue st s n t
      let s2 ← sched.set_thread_state st s1 t sched.TS_RESTART
      let s3 ← notification.unblock_sporadic st s2 t
      let s4 ← sched.possible_switch_to st s3 t
      k s4) ⦃ Q ⦄ := by
  have hP := hP0.e
  obtain ⟨hR, hSRT⟩ := hX
  have hx2 := hR.toN.at_ntfn hnN hkn
  obtain ⟨xs, hQ, hxs, hB⟩ := hx2.obj.queue
  have hxs' : xs = t :: rest := by
    have h1 : xn.ntfnObj.ntfnQueue = (t :: rest).map UScalar.bv := hq
    rw [hxs] at h1
    exact List.map_injective_iff.2 (fun a b h => eq_of_bv h) h1
  subst hxs'
  have ht : t ∈ T := hQ.mem t (by simp)
  have htxs : t ∈ t :: rest := by simp
  have hta := hP.tcb t ht
  obtain ⟨x, hk, hx⟩ := hR.tcb t ht
  have hqn : t.bv ∈ Fl4Spec.ntfnQueueOf xn := by rw [hq]; simp
  have htn : t.bv ≠ n.bv := by intro h; rw [h, hkn] at hk; cases hk
  have hnd := hQ.nodup
  have hb1 : L.mem s (tBlockA t) = n := (hB t htxs).2
  have hst6 : (L.mem s (tStA t)).val = 6 := (hB t htxs).1
  -- the dequeue
  refine WP.spec_bind (ntfn_dequeue_full hP0.n s hnN t (t :: rest) hQ htxs) ?_
  rintro s2 ⟨hA1, hA2, hA3⟩
  have hSS1 : SlotsSame th (L.mem s) (L.mem s2) :=
    IRel.slotsSame_of ⟨hR, hSRT⟩ hA3.foot fun b hb => iwords_oobj (NWrite.iwords hP.tcb hb)
  obtain ⟨q', hq'⟩ : ∃ q', Fl4Spec.removeAll t.bv (Fl4Spec.ntfnQueueOf xn) = q' := ⟨_, rfl⟩
  have herase : (t :: rest).erase t = rest := List.erase_cons_head t rest
  have hrm : q' = rest.map UScalar.bv := by
    rw [← hq', hq, removeAll_map hnd t, herase]
  set xn' : Fl4Spec.Notification :=
    { xn with ntfnObj := if q' = [] then Fl4Spec.Ntfn.idleNtfn else Fl4Spec.Ntfn.waitingNtfn q' } with hxn'
  have hdeq : Fl4Spec.tcbNtfnDequeue (Z := Unit) t.bv n.bv σ = ({((), updK σ n.bv (.notification xn'))}, False) := by
    rw [tcbNtfnDequeue_eq hkn hqn, hq', hxn']
    cases q' <;> simp [Fl4Spec.ntfnObjUpdate]
  set σ2 := updK σ n.bv (.notification xn') with hσ2
  have hbw : ∀ w ∈ t :: rest, w ∈ T ∧ L.mem s (tBlockA w) = n := fun w hw => ⟨hQ.mem w hw, (hB w hw).2⟩
  rw [herase] at hA1 hA2
  have hR2 : IpcRel N T E R B (L.mem s2) σ2 := by
    refine hR.upd_ntfn hP0 hnN _ (fun b hb ⟨_, hnw, hnl⟩ => hA3.agree b hb
        (fun w hw => by
          obtain ⟨hwT, hwb⟩ := hbw w hw
          have hwa := hP.tcb w hwT
          exact ⟨fun e => hnl ⟨w, hwT, hwb, Or.inl (by rw [e, val_next hwa])⟩,
            fun e => hnl ⟨w, hwT, hwb, Or.inr (by rw [e, val_prev hwa])⟩⟩)
        (fun e => hnw (e ▸ (nw_words hP0 hnN).1)) (fun e => hnw (e ▸ (nw_words hP0 hnN).2.1)))
      ⟨?_, ?_, ?_, ?_⟩
    · show NtfnObjRel _ T n (if q' = [] then Fl4Spec.Ntfn.idleNtfn else Fl4Spec.Ntfn.waitingNtfn q')
      by_cases hemp : rest = []
      · have : q' = [] := by rw [hrm, hemp]; rfl
        rw [if_pos this]
        rw [hemp] at hA1
        exact ⟨by rw [hA2, if_pos hemp], hA1⟩
      · have hne : q' ≠ [] := by rw [hrm]; simpa using hemp
        rw [if_neg hne]
        have hstn : stOf (L.mem s) n = 1#u64 := by
          have := hx2.obj
          cases h : xn.ntfnObj with
          | idleNtfn => rw [h] at hxs; simp [Fl4Spec.Ntfn.ntfnQueue] at hxs
          | activeNtfn b => rw [h] at hxs; simp [Fl4Spec.Ntfn.ntfnQueue] at hxs
          | waitingNtfn q => rw [h] at this; exact this.1
        refine ⟨by rw [hA2, if_neg hemp]; exact hstn, rest, hemp, hrm, hA1, fun y hy => ?_⟩
        have hyx : y ∈ t :: rest := List.mem_cons_of_mem t hy
        have e := hA3.tcb y (hQ.mem y hyx)
        exact ⟨by rw [e.st]; exact (hB y hyx).1, by rw [e.blk]; exact (hB y hyx).2⟩
    · show xn.ntfnBoundTcb = _; rw [hA3.bound]; exact hx2.bound
    · rw [hA3.bound]; exact hx2.bound_mem
    · show xn.ntfnSc = _; rw [hA3.sc]; exact hx2.sc
  have hK := NtfnStep.ntfn (y := xn') hkn rfl rfl
  have hS2 : SRT st th cr N T C E R B c (SRE st N T C E R B c) s2 σ2 :=
    ⟨hSRT.1.stableN hSRT.2.1.placed hA3.foot hK, hSRT.2.1.stable hA3.foot hK,
      hSRT.2.2.mono hA3.foot.1 (SzKeep.ntfnStep hK)⟩
  have hk2 : σ2.kheap t.bv = some (.tcb x) := by simp [hσ2, updK, htn, hk]
  have hkn2 : σ2.kheap n.bv = some (.notification xn') := by simp [hσ2, updK]
  have hb2 : (L.mem s2 (tStA t)).val = 6 := by rw [(hA3.tcb t ht).st]; exact hst6
  have hq2 : ∀ e ∈ E, ∀ z', σ2.kheap e.bv = some (.endpoint z') → t.bv ∉ z'.epQueue :=
    Notif.IpcRel.not_ep_queued hR2 (by rw [hb2]; omega)
  have hqn2 : ∀ n' ∈ N, ∀ z', σ2.kheap n'.bv = some (.notification z') → t.bv ∉ z'.ntfnObj.ntfnQueue := by
    intro n' hn' z' hz' hm
    by_cases e : n' = n
    · subst e
      rw [hkn2] at hz'; cases hz'
      change t.bv ∈ (if q' = [] then Fl4Spec.Ntfn.idleNtfn else Fl4Spec.Ntfn.waitingNtfn q').ntfnQueue at hm
      by_cases hq2 : q' = []
      · rw [if_pos hq2] at hm; simp [Fl4Spec.Ntfn.ntfnQueue] at hm
      · rw [if_neg hq2] at hm; simp only [Fl4Spec.Ntfn.ntfnQueue] at hm
        rw [hrm, mem_map_bv] at hm
        rw [← herase] at hm
        exact hnd.not_mem_erase hm
    · obtain ⟨z0, hz0, hzr⟩ := hR2.toN.ntfn n' hn'
      rw [hz'] at hz0; cases hz0
      obtain ⟨ys, -, hys, hBy⟩ := hzr.obj.queue
      rw [hys, mem_map_bv] at hm
      have hb := (hBy t hm).2
      have hbt : L.mem s2 (tBlockA t) = n := by rw [(hA3.tcb t ht).blk, hb1]
      exact e (hb.symm.trans hbt)
  -- the restart
  have hcode : sched.TS_RESTART.val = tsCode .restart := by unfold sched.TS_RESTART; rfl
  refine WP.spec_bind (WP.spec_and (set_thread_state_cq (ipcCore_top hP) hP0 hP s2 σ2 hR2.toE
    (IpcRel.toSRN hR2 hS2) ht hk2 hq2 hqn2 .restart (by decide) sched.TS_RESTART hcode)
    (set_thread_state_sfoot hS2.2.1 ht sched.TS_RESTART)) ?_
  rintro s3 ⟨⟨hE3, hS3⟩, hw3⟩
  have hSS2 : SlotsSame th (L.mem s2) (L.mem s3) :=
    IRel.slotsSame_of ⟨hR2, hS2⟩ hw3 fun b hb => tfoot_oobj hS2.2.1 (Or.inl (KFoot.of_sfoot hb))
  have hX3 := IpcRel.ofSRN hE3 hS3
  set σ3 := stsAct (updK σ2 t.bv (.tcb { x with tcbState := .restart })) t.bv with hσ3
  have hkn3 : σ3.kheap n.bv = some (.notification xn') := by
    rw [hσ3, stsAct_kheap]; simp [updK, Ne.symm htn, hkn2]
  -- the sporadic unblock and the switch
  refine WP.spec_bind (WP.spec_and (unblock_irel hP0 s3 _ hX3 t ht) (unblock_sporadic_tfoot hX3.2.2.1 t ht)) ?_
  rintro s4 ⟨⟨σ4, hu, hf4, hv4, hX4⟩, hw4⟩
  have hSS3 : SlotsSame th (L.mem s3) (L.mem s4) :=
    IRel.slotsSame_of hX3 hw4 fun b hb => tfoot_oobj hX3.2.2.1 hb
  refine WP.spec_bind (WP.spec_and (switch_top hP0 s4 σ4 hX4.1 hX4.2 (hAct _ _ hX4) t ht)
    (possible_switch_to_sfootI hX4.1.toN hX4.2.2.1 (hAct _ _ hX4) ht)) ?_
  rintro s5 ⟨⟨σ5, hps, hk5, hf5, hv5, hS5⟩, hw5⟩
  have hSS4 : SlotsSame th (L.mem s4) (L.mem s5) :=
    IRel.slotsSame_of hX4 hw5 fun b hb => sfootI_oobj hP.tcb hb
  refine hkont s5 σ5 xn' ?_ ⟨hX4.1.frame hP0 hf5 hv5, hS5⟩ (by rw [hk5]; exact hv4.1.1 _ _ hkn3) ?_
    (((hSS1.trans hSS2).trans hSS3).trans hSS4)
  · show ((), σ5) ∈ (Fl4Spec.removeAndRestartNtfnQueuedThread (Z := Unit) t.bv n.bv σ).1
    unfold Fl4Spec.removeAndRestartNtfnQueuedThread
    rw [nd_bind_one hdeq, nd_bind_one (Notif.setThreadState_eq .restart hk2), restart_spec_eq,
      specSporadicAssert_eq, nd_bind_one hu, hps]
    rfl
  · show (if q' = [] then Fl4Spec.Ntfn.idleNtfn else Fl4Spec.Ntfn.waitingNtfn q').ntfnQueue = _
    by_cases hq0 : q' = []
    · rw [if_pos hq0, ← hrm, hq0]; rfl
    · rw [if_neg hq0, ← hrm]; rfl

end Step

/-! ## The loop -/

section Loop
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

variable (st th cr N T C E R B c) in
/-- The loop invariant: the queue still to visit is the notification's,
from FL4's next thread, the spec's outcomes from it among the whole's. -/
def SInv (n : U64) (s0 : S) (σ0 : Fl4Spec.State Unit) (q0 : List Fl4Spec.ObjRef) (x : S × U64 × U64) : Prop :=
  ∃ σ' xn, ∃ rest : List U64, IRel st th cr N T C E R B c x.1 σ' ∧ σ'.kheap n.bv = some (.notification xn) ∧
    Fl4Spec.ntfnQueueOf xn = rest.map UScalar.bv ∧ x.2.1 = rest.headD 0#u64 ∧ rest.length ≤ x.2.2.val ∧
    (∀ z, z ∈ (Fl4Spec.NonDet.mapMx (rrn n) (rest.map UScalar.bv) σ').1 →
      z ∈ (Fl4Spec.NonDet.mapMx (rrn n) q0 σ0).1) ∧ SlotsSame th (L.mem s0) (L.mem x.1)

set_option maxHeartbeats 4000000 in
/-- **The loop of `cancel_all_signals`** on `IRel`. -/
theorem signals_loop (hP0 : IPlaced N T E R B)
    (hAct : ∀ s σ, IRel st th cr N T C E R B c s σ → ActReady σ)
    {n : U64} (hnN : n ∈ N) (s0 : S) (σ0 : Fl4Spec.State Unit) (q0 : List Fl4Spec.ObjRef) (x0 : S × U64 × U64)
    (h0 : SInv st th cr N T C E R B c n s0 σ0 q0 x0) :
    notification.cancel_all_signals_loop st x0.1 n x0.2.1 x0.2.2 ⦃ s' => ∃ σf,
      ((), σf) ∈ (Fl4Spec.NonDet.mapMx (rrn n) q0 σ0).1 ∧ IRel st th cr N T C E R B c s' σf ∧
      SlotsSame th (L.mem s0) (L.mem s') ⦄ := by
  have hP := hP0.e
  unfold notification.cancel_all_signals_loop
  apply loop.spec_decr_nat (measure := fun x : S × U64 × U64 => x.2.2.val)
    (inv := SInv st th cr N T C E R B c n s0 σ0 q0) _ _ x0 ?_ h0
  rintro ⟨s, t, fuel⟩ ⟨σ', xn, rest, hX, hkn, hq, ht, hlen, hinc, hss⟩
  simp only at hX hkn hq ht hlen hinc hss ⊢
  have hx2 := hX.1.toN.at_ntfn hnN hkn
  obtain ⟨xs, hQ, hxs, -⟩ := hx2.obj.queue
  have hxs' : xs = rest := by
    have h1 : xn.ntfnObj.ntfnQueue = rest.map UScalar.bv := hq
    rw [hxs] at h1
    exact List.map_injective_iff.2 (fun a b h => eq_of_bv h) h1
  subst hxs'
  unfold notification.cancel_all_signals_loop.body
  step with obj.Tcb.is_null.spec as ⟨bn, hbn⟩
  cases xs with
  | nil =>
    simp only [List.headD_nil] at ht
    subst ht
    simp only [hbn, decide_true, ↓reduceIte, WP.spec_ok]
    exact ⟨σ', hinc _ rfl, hX, hss⟩
  | cons t0 rest' =>
    simp only [List.headD_cons] at ht
    subst t
    have ht00 : t0 ≠ 0#u64 := hQ.ne0 hP.tcb t0 (by simp)
    simp only [hbn, ht00, decide_false, Bool.false_eq_true, ↓reduceIte]
    have hf0 : fuel > 0#u64 := by
      simp only [List.length_cons] at hlen
      show (0#u64 : U64).val < fuel.val; simp; omega
    simp only [hf0, ↓reduceIte]
    step as ⟨fuel1, hfuel1⟩
    -- the successor
    have hseg := hQ.seg
    rw [show t0 :: rest' = [] ++ t0 :: rest' from rfl, Seg_mid] at hseg
    obtain ⟨-, -, hnext, -⟩ := hseg
    unfold tcbqueue.next_of
    step with tcbqueue.next.spec as ⟨nx, hnx⟩
    try simp only [bind_ok]
    refine ntfn_restart_irel hP0 hAct s σ' hX hnN hkn hq _ fun s4 σ'' xn' hres hX4 hkn4 hq4 hss4 => ?_
    rw [WP.spec_ok]
    refine ⟨⟨σ'', xn', rest', hX4, hkn4, hq4, by rw [hnx, hnext], ?_, ?_, hss.trans hss4⟩, ?_⟩
    · rw [hfuel1]; simp only [List.length_cons] at hlen; scalar_tac
    · exact fun z hz => hinc z (by rw [List.map_cons]; exact mapMx_cons_mem (l := rest'.map UScalar.bv) hres z hz)
    · rw [hfuel1]; scalar_tac

set_option maxHeartbeats 4000000 in
/-- **`cancel_all_signals` on `IRel`.** -/
theorem cancel_all_signals_irel (hP0 : IPlaced N T E R B)
    (hAct : ∀ s σ, IRel st th cr N T C E R B c s σ → ActReady σ)
    (s : S) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ) {n : U64} (hnN : n ∈ N) :
    notification.cancel_all_signals st s n ⦃ s' => ∃ σ',
      ((), σ') ∈ (Fl4Spec.cancelAllSignals (Z := Unit) n.bv σ).1 ∧ IRel st th cr N T C E R B c s' σ' ∧
      SlotsSame th (L.mem s) (L.mem s') ⦄ := by
  have hP := hP0.e
  obtain ⟨xn, hkn, hx2⟩ := hX.1.toN.ntfn n hnN
  unfold notification.cancel_all_signals
  step with obj.Ntfn.state.spec as ⟨i, hi⟩
  rw [epState_eq] at hi
  have hsp : Fl4Spec.cancelAllSignals (Z := Unit) n.bv σ = (match xn.ntfnObj with
        | .waitingNtfn queue => (do Fl4Spec.NonDet.mapMx (fun t => Fl4Spec.removeAndRestartNtfnQueuedThread t n.bv)
                                      queue
                                    Fl4Spec.rescheduleRequired)
        | _ => return ()) σ := by
    unfold Fl4Spec.cancelAllSignals
    rw [nd_bind_one (getNotification_eq hkn)]
    rfl
  have hob := hx2.obj
  cases hxo : xn.ntfnObj with
  | idleNtfn =>
    rw [hxo] at hob
    have h0 : i ≠ obj.NTFN_WAITING := by rw [hi, hob.1]; unfold obj.NTFN_WAITING; decide
    simp only [h0, bne_iff_ne, ne_eq, not_false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨σ, by rw [hsp, hxo]; rfl, hX, SlotsSame.refl _ _⟩
  | activeNtfn b =>
    rw [hxo] at hob
    have h0 : i ≠ obj.NTFN_WAITING := by rw [hi, hob.1]; unfold obj.NTFN_WAITING; decide
    simp only [h0, bne_iff_ne, ne_eq, not_false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨σ, by rw [hsp, hxo]; rfl, hX, SlotsSame.refl _ _⟩
  | waitingNtfn q =>
    rw [hxo] at hob
    obtain ⟨h1, xs, -, hqx, hQ, -⟩ := hob
    have h0 : i = obj.NTFN_WAITING := by rw [hi, h1]; unfold obj.NTFN_WAITING; rfl
    simp only [h0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    step with notification.get_queue.spec as ⟨qq, hqq⟩
    have hfuel : layout.WALK_FUEL.val = 2 ^ 64 - 1 := by simp [layout.WALK_FUEL, U64.rMax]
    have hI0 : SInv st th cr N T C E R B c n s σ q (s, qq.head, layout.WALK_FUEL) :=
      ⟨σ, xn, xs, hX, hkn, by show xn.ntfnObj.ntfnQueue = _; rw [hxo, hqx]; rfl,
        by rw [hqq, epQ_eq, hQ.head], by rw [hfuel]; exact len_le_max xs hQ.nodup (hQ.ne0 hP.tcb),
        fun z hz => by rw [hqx]; exact hz, SlotsSame.refl _ _⟩
    refine WP.spec_bind (signals_loop hP0 hAct hnN s σ q _ hI0) ?_
    rintro s1 ⟨σf, hmf, hXf, hss1⟩
    refine WP.spec_mono (WP.spec_and (resched_irel hP0 s1 σf hXf (hAct _ _ hXf))
      (reschedule_required_sfootI hXf.2.2.1)) ?_
    rintro s2 ⟨⟨σr, hrs, -, hX2⟩, hw2⟩
    refine ⟨σr, ?_, hX2, hss1.trans (IRel.slotsSame_of hXf hw2 fun b hb => sfootI_oobj hP.tcb hb)⟩
    rw [hsp, hxo]
    exact ⟨((), σf), hmf, by show ((), σr) ∈ (Fl4Spec.rescheduleRequired σf).1; rw [hrs]; rfl⟩

end Loop

end

end Fl4Proofs.P3.Ipc
