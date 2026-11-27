/-
# P2 (line p3mc, gen 26): the waking signal of a fired timer with the per-class premises asked of homed objects

Handoff §30c (W-h). The waking chain (`wake_wait_fire`, `wake_recv_fire`, `wk_sig`, `fire_wk_step`;
P2/FootTimerFireWf, Wr, Wa, We) asks its read / write premises over classes defined at the entry state `s`: words of
every thread whose `AFFINITY` is the core (`rL` / `wL`), of every SC whose `CORE` is the core (`rS` / `wS`), and
the per-state `STATE` writes of every such thread (`StW`). At a view start (P2/CoreView) every `AFFINITY` and
every SC `CORE` reads as the core, so these classes contain other cores' threads and SCs, whose words the view does
not keep. The chain uses them only for specific objects (the woken thread, `TIMER_MIN`'s thread, the woken thread's
SC). Here the same statements, proved by the same text (copied by a script), with those premises asked only of
threads satisfying a predicate `Hm` and SCs satisfying `Hs`, and the chain given `Hm` of the woken thread / the
due thread and `Hs` of the SC of every thread with an SC (`hHs`):

* `StWH`: `StW` asked only for threads with `Hm`.
* **`WH.wake_wait_fire`** (`hHw`: `Hm` of the notification's head), **`WH.wake_recv_fire`** (`hHt`: `Hm` of the
  bound thread), **`WH.wk_sig`**, **`WH.fire_wk_step`** (`hHw` at every state `remove` may reach, `hHtm`: `Hm`
  of the due thread).

No named premises; no existing statement changed.
-/
import Fl4Proofs.P2.FootTimerFireWe
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.WH
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2
open Fl4Proofs.P2.OwnMap
open Fl4Proofs.P2.PathObl (NodeSt ScAcc)

section
variable {S : Type}

/-- **`StW` asked only of threads with `Hm`** (module docstring). -/
def StWH (st gS : machine.Store S) [L : LawfulStore st] (T : Set U64) (Lk : U64 → Prop) (Hm : U64 → Prop)
    (s : S) : Prop :=
  ∀ X y v, LocT st T s y → Hm y → L.mem X (affA y) = L.cpu s →
    (QueuedState (L.mem X (stA y)) → Lk (L.mem X (blockA y))) → ¬ QueuedState v →
    gS.write X (stA y) v = st.write X (stA y) v

end

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
variable {Hm Hs : U64 → Prop}

set_option maxRecDepth 4000 in
set_option maxHeartbeats 16000000 in
/-- **The `WAITING` branch of a fired timer's signal on the guarded store, from the entry state's sets**
(module docstring). -/
theorem wake_wait_fire {A : Type} (ar : machine.Arch A) {s X : S} (a : A) {N badge : U64} {Lk : U64 → Prop}
    (hTX : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac X) (hNN : N ∈ Nt) (hHN : H N = some .ntfn)
    (hAffSc : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t))
    (kX : L.ksb X = L.ksb s) (cX : L.cpu X = L.cpu s)
    (kT : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (K.val < 3528 ∨ 3576 ≤ K.val) →
      L.mem X (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K))
    (hcur : (L.epQ X N).head ≠ L.curW X) (hac : L.actionW X = sched.ACTION_RESUME_CURRENT)
    (hwt : L.epState X N = obj.NTFN_WAITING)
    (haf : L.mem X (affA (L.epQ X N).head) = L.cpu s)
    (hdom : L.mem X (domA (L.epQ X N).head) =
      L.mem X (core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN))
    (hnd : L.mem X (scA (L.epQ X N).head) = 0#u64 → L.mem X (ntfnScA N) = 0#u64)
    (rN : ∀ k : U64, k.val < 64 → k.val % 8 = 0 → R (core.num.U64.wrapping_add N k))
    (wN : ∀ k : U64, k.val < 64 → k.val % 8 = 0 → k.val ≠ 24 → W (core.num.U64.wrapping_add N k))
    (rL : ∀ y, LocT st T s y → Hm y → ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ TimerField K.val →
      ¬ GField K.val → R (core.num.U64.wrapping_add y K))
    (wL : ∀ y, LocT st T s y → Hm y → ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ GateField K.val →
      ¬ TimerField K.val → ¬ GField K.val → K.val ≠ 3328 → K.val ≠ 3336 →
      W (core.num.U64.wrapping_add y K))
    (rS : ∀ p ∈ Scs, L.mem s (scCoreA p) = L.cpu s → Hs p → ∀ b, Aligned b → InSC p (Z p) b → R b)
    (wS : ∀ p ∈ Scs, L.mem s (scCoreA p) = L.cpu s → Hs p → ∀ b, Aligned b → InSC p (Z p) b → b.val ≠ p.val + 16 → W b)
    (lkL : ∀ y ∈ T, QueuedState (L.mem s (stA y)) → Lk (L.mem s (blockA y)) → ∀ k : U64,
      (k.val = 3496 ∨ k.val = 3504) → R (core.num.U64.wrapping_add y k) ∧ W (core.num.U64.wrapping_add y k))
    (hLk : Lk N)
    (nRW : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      R (L.nodeAt s (L.cpu s) o) ∧ W (L.nodeAt s (L.cpu s) o))
    (rCD : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hSW : StWH st gS T Lk Hm s) (hHw : Hm (L.epQ X N).head)
    (hHs : ∀ y ∈ T, L.mem s (scA y) ≠ 0#u64 → Hs (L.mem s (scA y))) :
    notification.send_signal gS ar X a N badge = notification.send_signal st ar X a N badge := by
  obtain ⟨⟨Q, Rq, hq⟩, hBd, hXX, hSS, hSgX⟩ := hTX
  obtain ⟨E, EQ, hEW⟩ := hq.eps
  have hT := hq.tcbs
  have he : N ∈ E := (hEW.2.2.2.2.2.2.2.1 N).2 (Or.inr hHN)
  obtain ⟨hE, -, hqr⟩ := hEW.1 N he
  obtain ⟨k1, -, -, -, -, k5⟩ := hEW.2.2.2.2.2
  have hwt1 : L.epState X N = 1#u64 := by rw [hwt]; simp [obj.NTFN_WAITING]
  -- the queue's members: blocked on `N`
  have mst : ∀ z ∈ EQ N, z ∈ T ∧ L.mem X (blockA z) = N ∧ L.mem X (stA z) = sched.TS_BLOCKED_ON_NTFN := by
    intro z hz
    obtain ⟨-, hbe, hbl⟩ := hEW.2.2.2.1 N he z hz
    have hzT := hqr.mem z hz
    refine ⟨hzT, hbe, ?_⟩
    rcases hbl with hb | hb | hb
    · have := k1 z hzT (by simp) (Or.inl hb); rw [hbe, hHN] at this; cases this
    · have := k1 z hzT (by simp) (Or.inr hb); rw [hbe, hHN] at this; cases this
    · exact hb
  have hne : EQ N ≠ [] := fun h0 => (k5 N he h0).2 hHN hwt1
  obtain ⟨y0, ys, hys⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨w, ew⟩ : ∃ w, (L.epQ X N).head = w := ⟨_, rfl⟩
  rw [ew] at hcur haf hdom hnd hHw
  have hmem : w ∈ EQ N := by
    have : w = y0 := by rw [← ew, hqr.head, hys]; rfl
    rw [this, hys]; exact List.mem_cons_self
  obtain ⟨hwT, hbw, hsw⟩ := mst w hmem
  have ht' := hT w hwT
  -- the woken thread at `s`
  have k3328 : L.mem X (stA w) = L.mem s (stA w) := by
    rw [stA_eq]; exact kT w hwT 3328#u64 (by simp) (by simp) (Or.inl (by simp))
  have k3336 : L.mem X (blockA w) = L.mem s (blockA w) := by
    rw [blockA_eq]; exact kT w hwT 3336#u64 (by simp) (by simp) (Or.inl (by simp))
  have k3464 : L.mem X (scA w) = L.mem s (scA w) := by
    rw [scA_eq]; exact kT w hwT 3464#u64 (by simp) (by simp) (Or.inl (by simp))
  have hloc : LocT st T s w := by
    refine ⟨hwT, ?_⟩
    rw [← haf]; unfold affA; exact (kT w hwT 3520#u64 (by simp) (by simp) (Or.inl (by simp))).symm
  have qS : ∀ z ∈ EQ N, QueuedState (L.mem s (stA z)) ∧ Lk (L.mem s (blockA z)) := by
    intro z hz
    obtain ⟨hzT, hb, hs⟩ := mst z hz
    rw [stA_eq, ← kT z hzT 3328#u64 (by simp) (by simp) (Or.inl (by simp)), ← stA_eq, hs,
      blockA_eq, ← kT z hzT 3336#u64 (by simp) (by simp) (Or.inl (by simp)), ← blockA_eq, hb]
    exact ⟨Or.inr (by simp [sched.TS_BLOCKED_ON_NTFN]), hLk⟩
  have lnk : ∀ z ∈ EQ N, R (prevA .Ep z) ∧ R (nextA .Ep z) ∧ W (prevA .Ep z) ∧ W (nextA .Ep z) := by
    intro z hz
    obtain ⟨q1, q2⟩ := qS z hz
    have hzT := hqr.mem z hz
    obtain ⟨p1, p2⟩ := lkL z hzT q1 q2 3504#u64 (Or.inr (by simp))
    obtain ⟨n1, n2⟩ := lkL z hzT q1 q2 3496#u64 (Or.inl (by simp))
    exact ⟨p1, n1, p2, n2⟩
  have rw' : ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ TimerField K.val → ¬ GField K.val →
      R (core.num.U64.wrapping_add w K) := rL w hloc hHw
  -- the node
  have eN : ∀ o, L.nodeAt X (L.cpu X) o = L.nodeAt s (L.cpu s) o := fun o => by rw [cX, nodeAt_of_ksb kX]
  have hn : NodeSt (L := L) R W X := by
    unfold PathObl.NodeSt
    rw [eN, eN]
    exact ⟨(nRW _ (by rw [curth_val]; omega) (by rw [curth_val])).1,
      (nRW _ (by rw [act_val]; omega) (by rw [act_val])).1, (nRW _ (by rw [act_val]; omega) (by rw [act_val])).2⟩
  -- the badge register
  have hbv : layout.reg.BADGE.val = 0 := by unfold layout.reg.BADGE layout.reg.RDI; rfl
  obtain ⟨KB, hKB, eKB⟩ := regA_eq ht' (r := layout.reg.BADGE) (by rw [hbv]; omega)
  have hKB' : KB.val = 256 := by rw [hKB, hbv]
  have gB1 : ¬ GateField KB.val := by unfold GateField; omega
  have gB2 : ¬ TimerField KB.val := by unfold TimerField; omega
  have gB3 : ¬ GField KB.val := by unfold GField; omega
  -- the woken thread's SC
  have scF : L.mem X (scA w) ≠ 0#u64 → L.mem X (scA w) ∈ Scs ∧ L.mem s (scCoreA (L.mem X (scA w))) = L.cpu s ∧
      L.mem X (scA w) ∈ Ac := by
    intro h0
    have hs0 : L.mem s (scA w) ≠ 0#u64 := by rw [← k3464]; exact h0
    refine ⟨(hXX.2.2.toScExtra0.bound w hwT h0).1, by rw [k3464, hAffSc w hwT hs0]; exact hloc.2, ?_⟩
    exact hBd.sact w hwT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr hsw)))))))) h0
  have hsw0 : L.mem X (scA w) ≠ 0#u64 → Hs (L.mem X (scA w)) := fun h0 => by
    rw [k3464]; exact hHs w hwT (by rw [← k3464]; exact h0)
  let sb : Nat := Z (L.mem X (scA w))
  have P : WkPre st R W X w N sb := by
    refine ⟨fun h0 => ?_, fun _ => ?_, hnd, hdom, by rw [haf, cX], fun h0 => ?_, fun h0 => ?_, fun h0 => ?_,
      fun h0 => ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨c1, c2, -⟩ := scF h0
      have hcq := scq_of hXX.1 hSS c1
      exact rS _ c1 c2 (hsw0 h0) _ hcq.2.2.2.2 hcq.2.2.2.1
    · exact rN layout.ntfn.SC (by simp [layout.ntfn.SC]) (by simp [layout.ntfn.SC])
    · obtain ⟨c1, c2, -⟩ := scF h0
      obtain ⟨hP, hz⟩ := hXX.1.sc _ c1
      obtain ⟨h8, h128, -⟩ := sc_lo hP hz
      have hv := sc_word_val hP hz (o := layout.sc.SPORADIC) (by simp [layout.sc.SPORADIC])
      have hsv : layout.sc.SPORADIC.val = 64 := by simp [layout.sc.SPORADIC]
      exact rS _ c1 c2 (hsw0 h0) _ (by unfold Aligned; unfold sporA; rw [hv, hsv]; omega)
        ⟨by unfold sporA; rw [hv]; omega, by unfold sporA; rw [hv, hsv]; omega⟩
    · obtain ⟨c1, c2, -⟩ := scF h0
      have hcq := scq_of hXX.1 hSS c1
      refine ⟨fun b ha hb => rS _ c1 c2 (hsw0 h0) b ha hb, fun b ha hb => wS _ c1 c2 (hsw0 h0) b ha hb.inSC (by
        have := hb.1; omega), ?_⟩
      obtain ⟨⟨q1, q2⟩, q3⟩ := hcq.2.2.1
      have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
      obtain ⟨hP, hz⟩ := hXX.1.sc _ c1
      have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
      exact wS _ c1 c2 (hsw0 h0) _ q3 ⟨q1, q2⟩ (by rw [hv, hcv]; omega)
    · obtain ⟨c1, -, c3⟩ := scF h0
      have hcq := scq_of hXX.1 hSS c1
      exact hcq.1 ((hSS.act _ c1).1 c3)
    · obtain ⟨c1, -, -⟩ := scF h0
      have hN : NodePlaced st T X (L.cpu X) := hq.nodes _ hq.cur
      have aR : Aligned (L.nodeA X layout.node.REPROGRAM) :=
        nodeAt_aligned hN (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
      refine ⟨aR, ?_⟩
      unfold Outside
      by_contra hc
      push_neg at hc
      have hΩ := hXX.1.scW _ c1 _ aR ⟨hc.1, hc.2⟩
      exact out_ne_node (hq.omega _ hΩ) hq.cur hN (o := layout.node.REPROGRAM) (by simp [layout.node.REPROGRAM]) rfl
    · show R (L.nodeAt X (L.cpu X) layout.node.CUR_TIME)
      rw [eN]; exact (nRW _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).1
    · show W (L.nodeAt X (L.cpu X) layout.node.REPROGRAM)
      rw [eN]; exact (nRW _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])).2
    · rw [eN]; exact (nRW _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])).1
    · rw [kX]; exact rCD
  refine wake_wait_guard ar X a N badge w (sb := sb) hq hEW he hwt ew hmem
    (rN _ (by simp [layout.ntfn.TAIL_STATE]) (by simp [layout.ntfn.TAIL_STATE]))
    (rN _ (by simp [layout.ntfn.HEAD]) (by simp [layout.ntfn.HEAD]))
    (wN _ (by simp [layout.ntfn.TAIL_STATE]) (by simp [layout.ntfn.TAIL_STATE]) (by simp [layout.ntfn.TAIL_STATE]))
    (wN _ (by simp [layout.ntfn.HEAD]) (by simp [layout.ntfn.HEAD]) (by simp [layout.ntfn.HEAD]))
    (hq.omega _ (hSgX.sub _ (hXX.1.ntB N hNN).1)).1 (lnk w hmem).1 (lnk w hmem).2.1 (lnk w hmem).2.2.1 (lnk w hmem).2.2.2
    (fun hE' => (lnk _ ((qmem_nbrs hqr hmem).1 hE')).2.2.1) hcur hn
    (by rw [stA_eq]; exact rw' 3328#u64 (by simp) (by simp) (by simp) (by simp [TimerField]) (by simp [GField]))
    (by rw [scA_eq]; exact rw' 3464#u64 (by simp) (by simp) (by simp) (by simp [TimerField]) (by simp [GField]))
    (by rw [inqA_eq]; exact rw' 3592#u64 (by simp) (by simp) (by simp) (by simp [TimerField]) (by simp [GField]))
    (rw' 3432#u64 (by simp) (by simp) (by simp) (by simp [TimerField]) (by simp [GField]))
    (rw' 3520#u64 (by simp) (by simp) (by simp) (by simp [TimerField]) (by simp [GField]))
    (by rw [eKB]; exact wL w hloc hHw KB (by omega) (by omega) (by omega) gB1 gB2 gB3 (by omega) (by omega)) hac ?_ P
    (hSgX.sub _ (hXX.1.ntW N hNN)) (fun h0 b hb hin => hXX.1.scW _ (scF h0).1 b hb hin)
  intro Y wY
  obtain ⟨kT', -, -⟩ := epfoot_keep hq hEW he (fun y hy => hqr.mem y hy) wY
  refine hSW Y w _ hloc hHw ?_ (fun _ => ?_) (by simp [QueuedState, sched.TS_RUNNING])
  · unfold affA
    rw [kT' w hwT 3520#u64 (by simp) (by simp) (by simp) (by simp)]
    exact (kT w hwT 3520#u64 (by simp) (by simp) (Or.inl (by simp))).trans hloc.2
  · rw [blockA_eq, kT' w hwT 3336#u64 (by simp) (by simp) (by simp) (by simp), ← blockA_eq, hbw]; exact hLk

set_option maxRecDepth 4000 in
set_option maxHeartbeats 16000000 in
/-- **The idle-bound `Recv` branch of a fired timer's signal on the guarded store, from the entry state's sets**
(module docstring). `t` is the notification's bound thread, in `Recv` on `ep` with reply `r`. -/
theorem wake_recv_fire {A : Type} (ar : machine.Arch A) {s X : S} (a : A) {N badge t ep r : U64}
    {Lk : U64 → Prop}
    (hTX : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac X) (hNN : N ∈ Nt) (hHN : H N = some .ntfn)
    (hAffSc : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t))
    (kX : L.ksb X = L.ksb s) (cX : L.cpu X = L.cpu s)
    (kT : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (K.val < 3528 ∨ 3576 ≤ K.val) →
      L.mem X (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K))
    (hidle : L.epState X N = obj.NTFN_IDLE) (hbt : L.mem X (ntfnBtA N) = t) (ht0 : t ≠ 0#u64)
    (hrecv : L.mem X (stA t) = sched.TS_BLOCKED_ON_RECV)
    (heq : L.mem X (blockA t) = ep) (hr : L.mem X (replyA t) = r)
    (hcur : t ≠ L.curW X) (hac : L.actionW X = sched.ACTION_RESUME_CURRENT)
    (haf : L.mem X (affA t) = L.cpu s)
    (hdom : L.mem X (domA t) = L.mem X (core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN))
    (hnd : L.mem X (scA t) = 0#u64 → L.mem X (ntfnScA N) = 0#u64)
    (rN : ∀ k : U64, k.val < 64 → k.val % 8 = 0 → R (core.num.U64.wrapping_add N k))
    (rL : ∀ y, LocT st T s y → Hm y → ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ TimerField K.val →
      ¬ GField K.val → R (core.num.U64.wrapping_add y K))
    (wL : ∀ y, LocT st T s y → Hm y → ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ GateField K.val →
      ¬ TimerField K.val → ¬ GField K.val → K.val ≠ 3328 → K.val ≠ 3336 →
      W (core.num.U64.wrapping_add y K))
    (rS : ∀ p ∈ Scs, L.mem s (scCoreA p) = L.cpu s → Hs p → ∀ b, Aligned b → InSC p (Z p) b → R b)
    (wS : ∀ p ∈ Scs, L.mem s (scCoreA p) = L.cpu s → Hs p → ∀ b, Aligned b → InSC p (Z p) b → b.val ≠ p.val + 16 → W b)
    (lkL : ∀ y ∈ T, QueuedState (L.mem s (stA y)) → Lk (L.mem s (blockA y)) → ∀ k : U64,
      (k.val = 3496 ∨ k.val = 3504) → R (core.num.U64.wrapping_add y k) ∧ W (core.num.U64.wrapping_add y k))
    (hLkE : Lk ep)
    (rwE : ∀ k : U64, k.val < 16 → k.val % 8 = 0 →
      R (core.num.U64.wrapping_add ep k) ∧ W (core.num.U64.wrapping_add ep k))
    (wRt : r ≠ 0#u64 → W (rTcbA r))
    (nRW : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      R (L.nodeAt s (L.cpu s) o) ∧ W (L.nodeAt s (L.cpu s) o))
    (rCD : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hSW : StWH st gS T Lk Hm s) (hHt : Hm t)
    (hHs : ∀ y ∈ T, L.mem s (scA y) ≠ 0#u64 → Hs (L.mem s (scA y))) :
    notification.send_signal gS ar X a N badge = notification.send_signal st ar X a N badge := by
  have hTX' := hTX
  obtain ⟨⟨Q, Rq, hq⟩, hBd, hXX, hSS, hSgX⟩ := hTX
  obtain ⟨E, EQ, hEW⟩ := hq.eps
  have hT := hq.tcbs
  have htT : t ∈ T := by
    rcases TInv.ntb hTX' N hNN with h | h
    · rw [hbt] at h; exact absurd h ht0
    · rwa [hbt] at h
  have hblk : Blocked (L.mem X (stA t)) := Or.inr (Or.inl hrecv)
  obtain ⟨hep, hmem⟩ := hEW.2.2.2.2.1 t htT (by simp) hblk
  rw [heq] at hep hmem
  obtain ⟨hE, -, hqr⟩ := hEW.1 ep hep
  obtain ⟨-, -, -, k3, -, -⟩ := hEW.2.2.2.2.2
  have ht' := hT t htT
  -- `t` at `s`
  have k3328 : L.mem X (stA t) = L.mem s (stA t) := by
    rw [stA_eq]; exact kT t htT 3328#u64 (by simp) (by simp) (Or.inl (by simp))
  have k3336 : L.mem X (blockA t) = L.mem s (blockA t) := by
    rw [blockA_eq]; exact kT t htT 3336#u64 (by simp) (by simp) (Or.inl (by simp))
  have k3464 : L.mem X (scA t) = L.mem s (scA t) := by
    rw [scA_eq]; exact kT t htT 3464#u64 (by simp) (by simp) (Or.inl (by simp))
  have hloc : LocT st T s t := by
    refine ⟨htT, ?_⟩
    rw [← haf]; unfold affA; exact (kT t htT 3520#u64 (by simp) (by simp) (Or.inl (by simp))).symm
  -- the endpoint queue's members: receivers blocked on `ep`, queued at `s`
  have qS : ∀ z ∈ EQ ep, QueuedState (L.mem s (stA z)) ∧ Lk (L.mem s (blockA z)) := by
    intro z hz
    obtain ⟨-, hb, -⟩ := hEW.2.2.2.1 ep hep z hz
    have hzT := hqr.mem z hz
    have hs : L.mem X (stA z) = sched.TS_BLOCKED_ON_RECV := by rw [k3 ep hep z hz t hmem, hrecv]
    rw [stA_eq, ← kT z hzT 3328#u64 (by simp) (by simp) (Or.inl (by simp)), ← stA_eq, hs,
      blockA_eq, ← kT z hzT 3336#u64 (by simp) (by simp) (Or.inl (by simp)), ← blockA_eq, hb]
    exact ⟨Or.inl (by simp [sched.TS_BLOCKED_ON_RECV]), hLkE⟩
  have lnk : ∀ z ∈ EQ ep, R (prevA .Ep z) ∧ R (nextA .Ep z) ∧ W (prevA .Ep z) ∧ W (nextA .Ep z) := by
    intro z hz
    obtain ⟨q1, q2⟩ := qS z hz
    have hzT := hqr.mem z hz
    obtain ⟨p1, p2⟩ := lkL z hzT q1 q2 3504#u64 (Or.inr (by simp))
    obtain ⟨n1, n2⟩ := lkL z hzT q1 q2 3496#u64 (Or.inl (by simp))
    exact ⟨p1, n1, p2, n2⟩
  have rw' : ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ TimerField K.val → ¬ GField K.val →
      R (core.num.U64.wrapping_add t K) := rL t hloc hHt
  -- the node
  have eN : ∀ o, L.nodeAt X (L.cpu X) o = L.nodeAt s (L.cpu s) o := fun o => by rw [cX, nodeAt_of_ksb kX]
  have hn : NodeSt (L := L) R W X := by
    unfold PathObl.NodeSt
    rw [eN, eN]
    exact ⟨(nRW _ (by rw [curth_val]; omega) (by rw [curth_val])).1,
      (nRW _ (by rw [act_val]; omega) (by rw [act_val])).1, (nRW _ (by rw [act_val]; omega) (by rw [act_val])).2⟩
  -- the badge register
  have hbv : layout.reg.BADGE.val = 0 := by unfold layout.reg.BADGE layout.reg.RDI; rfl
  obtain ⟨KB, hKB, eKB⟩ := regA_eq ht' (r := layout.reg.BADGE) (by rw [hbv]; omega)
  have hKB' : KB.val = 256 := by rw [hKB, hbv]
  have gB1 : ¬ GateField KB.val := by unfold GateField; omega
  have gB2 : ¬ TimerField KB.val := by unfold TimerField; omega
  have gB3 : ¬ GField KB.val := by unfold GField; omega
  -- the woken thread's SC
  have scF : L.mem X (scA t) ≠ 0#u64 → L.mem X (scA t) ∈ Scs ∧ L.mem s (scCoreA (L.mem X (scA t))) = L.cpu s ∧
      L.mem X (scA t) ∈ Ac := by
    intro h0
    have hs0 : L.mem s (scA t) ≠ 0#u64 := by rw [← k3464]; exact h0
    refine ⟨(hXX.2.2.toScExtra0.bound t htT h0).1, by rw [k3464, hAffSc t htT hs0]; exact hloc.2, ?_⟩
    exact hBd.sact t htT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl hrecv)))))))) h0
  have hsw0 : L.mem X (scA t) ≠ 0#u64 → Hs (L.mem X (scA t)) := fun h0 => by
    rw [k3464]; exact hHs t htT (by rw [← k3464]; exact h0)
  let sb : Nat := scSb Z (L.mem X (scA t))
  have esb : L.mem X (scA t) ≠ 0#u64 → sb = Z (L.mem X (scA t)) := fun h0 => scSb_ne h0
  have P : WkPre st R W X t N sb := by
    refine ⟨fun h0 => ?_, fun _ => ?_, hnd, hdom, by rw [haf, cX], fun h0 => ?_, fun h0 => ?_, fun h0 => ?_,
      fun h0 => ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨c1, c2, -⟩ := scF h0
      have hcq := scq_of hXX.1 hSS c1
      exact rS _ c1 c2 (hsw0 h0) _ hcq.2.2.2.2 hcq.2.2.2.1
    · exact rN layout.ntfn.SC (by simp [layout.ntfn.SC]) (by simp [layout.ntfn.SC])
    · obtain ⟨c1, c2, -⟩ := scF h0
      obtain ⟨hP, hz⟩ := hXX.1.sc _ c1
      obtain ⟨h8, h128, -⟩ := sc_lo hP hz
      have hv := sc_word_val hP hz (o := layout.sc.SPORADIC) (by simp [layout.sc.SPORADIC])
      have hsv : layout.sc.SPORADIC.val = 64 := by simp [layout.sc.SPORADIC]
      exact rS _ c1 c2 (hsw0 h0) _ (by unfold Aligned; unfold sporA; rw [hv, hsv]; omega)
        ⟨by unfold sporA; rw [hv]; omega, by unfold sporA; rw [hv, hsv]; omega⟩
    · rw [esb h0]
      obtain ⟨c1, c2, -⟩ := scF h0
      have hcq := scq_of hXX.1 hSS c1
      refine ⟨fun b ha hb => rS _ c1 c2 (hsw0 h0) b ha hb, fun b ha hb => wS _ c1 c2 (hsw0 h0) b ha hb.inSC (by
        have := hb.1; omega), ?_⟩
      obtain ⟨⟨q1, q2⟩, q3⟩ := hcq.2.2.1
      have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
      obtain ⟨hP, hz⟩ := hXX.1.sc _ c1
      have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
      exact wS _ c1 c2 (hsw0 h0) _ q3 ⟨q1, q2⟩ (by rw [hv, hcv]; omega)
    · rw [esb h0]
      obtain ⟨c1, -, c3⟩ := scF h0
      have hcq := scq_of hXX.1 hSS c1
      exact hcq.1 ((hSS.act _ c1).1 c3)
    · rw [esb h0]
      obtain ⟨c1, -, -⟩ := scF h0
      have hN : NodePlaced st T X (L.cpu X) := hq.nodes _ hq.cur
      have aR : Aligned (L.nodeA X layout.node.REPROGRAM) :=
        nodeAt_aligned hN (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
      refine ⟨aR, ?_⟩
      unfold Outside
      by_contra hc
      push_neg at hc
      have hΩ := hXX.1.scW _ c1 _ aR ⟨hc.1, hc.2⟩
      exact out_ne_node (hq.omega _ hΩ) hq.cur hN (o := layout.node.REPROGRAM) (by simp [layout.node.REPROGRAM]) rfl
    · show R (L.nodeAt X (L.cpu X) layout.node.CUR_TIME)
      rw [eN]; exact (nRW _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).1
    · show W (L.nodeAt X (L.cpu X) layout.node.REPROGRAM)
      rw [eN]; exact (nRW _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])).2
    · rw [eN]; exact (nRW _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])).1
    · rw [kX]; exact rCD
  -- the reply
  have hRt := fun hr0 => (recv_rt (Z := Z) hTX' hNN htT hrecv hr hr0).2
  have aRt := fun hr0 => (recv_rt (Z := Z) hTX' hNN htT hrecv hr hr0).1
  -- `t`'s words outside the ones `cancel_ipc` writes keep their values along `CnD`
  have epT : ∀ (K : U64), K.val < 4096 → ∀ b, (b = epHeadA ep ∨ b = epTSA ep) →
      core.num.U64.wrapping_add t K ≠ b := by
    intro K hK b hb e
    have e' := congrArg UScalar.val e
    rw [field_val ht' hK] at e'
    rcases hb with rfl | rfl
    · rw [epHeadA_val] at e'; rcases hE.disj t htT with h' | h' <;> omega
    · rw [epTSA_val hE] at e'; rcases hE.disj t htT with h' | h' <;> omega
  have lnkT : ∀ (K : U64), K.val < 4096 → K.val ≠ 3496 → K.val ≠ 3504 → ∀ b, LinkOf .Ep (EQ ep) b →
      core.num.U64.wrapping_add t K ≠ b := by
    rintro K hK h1 h2 b ⟨y, hy, rfl | rfl⟩ <;>
      exact tcb_word_ne ht' (hT y (hqr.mem y hy)) hK (by simp [nextOff, prevOff])
        (fun e => by subst e; simp [nextOff, prevOff]; omega)
  have cK : ∀ (Y : S), WritesIn st X Y (CnD (EQ ep) ep t r) → ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      K.val ≠ 3376 → K.val ≠ 3496 → K.val ≠ 3504 → K.val ≠ 3328 →
      L.mem Y (core.num.U64.wrapping_add t K) = L.mem X (core.num.U64.wrapping_add t K) := by
    intro Y wY K hK h8 n1 n2 n3 n4
    refine wY.mem_eq (field_aligned ht' hK h8) ?_
    rintro (e | e | ⟨hr0, e⟩ | e)
    · exact tcb_word_ne ht' ht' (K2 := 3376#u64) hK (by simp) (fun _ => by simp; omega) e
    · rcases e with e | e | e
      · exact lnkT K hK n2 n3 _ e rfl
      · exact epT K hK _ (Or.inl e) rfl
      · exact epT K hK _ (Or.inr e) rfl
    · exact hRt hr0 _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨K, hK, rfl⟩)))) e
    · rw [stA_eq] at e; exact tcb_word_ne ht' ht' (K2 := 3328#u64) hK (by simp) (fun _ => by simp; omega) e
  have sW : ∀ v : U64, ¬ QueuedState v → ∀ Y, WritesIn st X Y (CnD (EQ ep) ep t r) →
      gS.write Y (stA t) v = st.write Y (stA t) v := by
    intro v hv Y wY
    refine hSW Y t v hloc hHt ?_ (fun _ => ?_) hv
    · unfold affA
      rw [cK Y wY 3520#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]
      exact (kT t htT 3520#u64 (by simp) (by simp) (Or.inl (by simp))).trans hloc.2
    · rw [blockA_eq, cK Y wY 3336#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp), ← blockA_eq,
        heq]; exact hLkE
  have hE0 := rwE layout.ep.HEAD (by simp [layout.ep.HEAD]) (by simp [layout.ep.HEAD])
  have hE8 := rwE layout.ep.TAIL_STATE (by simp [layout.ep.TAIL_STATE]) (by simp [layout.ep.TAIL_STATE])
  have rT : ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ TimerField K.val → ¬ GField K.val →
      R (core.num.U64.wrapping_add t K) := rw'
  refine wake_recv_guard ar X a N badge t ep r (sb := sb) hq hEW hidle hbt ht0 hrecv heq hep hmem hr
    (rN _ (by simp [layout.ntfn.TAIL_STATE]) (by simp [layout.ntfn.TAIL_STATE]))
    (ep_aligned (hEW.1 N ((hEW.2.2.2.2.2.2.2.1 N).2 (Or.inr hHN))).1).2
    (hq.omega _ (hSgX.sub _ (hXX.1.ntB N hNN).1)).1
    (rN _ (by simp [layout.ntfn.BOUND_TCB]) (by simp [layout.ntfn.BOUND_TCB]))
    (wL t hloc hHt 3376#u64 (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])
      (by simp [GField]) (by simp) (by simp))
    (by rw [stA_eq]; exact rT 3328#u64 (by simp) (by simp) (by simp) (by simp [TimerField]) (by simp [GField]))
    (by rw [blockA_eq]; exact rT 3336#u64 (by simp) (by simp) (by simp) (by simp [TimerField]) (by simp [GField]))
    (rT 3360#u64 (by simp) (by simp) (by simp) (by simp [TimerField]) (by simp [GField]))
    hE0.1 hE8.1 hE0.2 hE8.2
    (lnk t hmem).1 (lnk t hmem).2.1 (lnk t hmem).2.2.1 (lnk t hmem).2.2.2
    (fun hE' => (lnk _ ((qmem_nbrs hqr hmem).1 hE')).2.2.1)
    (fun hH' => (lnk _ ((qmem_nbrs hqr hmem).2 hH')).2.2.2)
    (fun hr0 => ⟨wRt hr0, aRt hr0⟩) P.mx hcur hn
    (by rw [scA_eq]; exact rT 3464#u64 (by simp) (by simp) (by simp) (by simp [TimerField]) (by simp [GField]))
    (by rw [inqA_eq]; exact rT 3592#u64 (by simp) (by simp) (by simp) (by simp [TimerField]) (by simp [GField]))
    (rT 3432#u64 (by simp) (by simp) (by simp) (by simp [TimerField]) (by simp [GField]))
    (rT 3520#u64 (by simp) (by simp) (by simp) (by simp [TimerField]) (by simp [GField]))
    (by rw [eKB]; exact wL t hloc hHt KB (by omega) (by omega) (by omega) gB1 gB2 gB3 (by omega) (by omega)) hac
    (sW _ (by simp [QueuedState, sched.TS_INACTIVE])) (sW _ (by simp [QueuedState, sched.TS_RUNNING])) P
    (hSgX.sub _ (hXX.1.ntW N hNN)) (fun h0 b hb hin => hXX.1.scW _ (scF h0).1 b hb (by rw [← esb h0]; exact hin))
    hRt

set_option maxRecDepth 4000 in
set_option maxHeartbeats 16000000 in
/-- **The waking signal on both stores** (module docstring). -/
theorem wk_sig {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) {s X : S} (a : A) {N badge t : U64}
    {Lk : U64 → Prop} {U : Set U64}
    (hTX : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac X) (hBA : BufAt st T Cs H Sg Scs Z U X)
    (hNN : N ∈ Nt) (hHN : H N = some .ntfn)
    (hAffSc : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t))
    (kX : L.ksb X = L.ksb s) (cX : L.cpu X = L.cpu s)
    (kT : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (K.val < 3528 ∨ 3576 ≤ K.val) →
      L.mem X (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K))
    (hac : L.actionW X = sched.ACTION_RESUME_CURRENT)
    (hwk : WkCase st R W Lk (L.cpu s) X N t)
    (rN : ∀ k : U64, k.val < 64 → k.val % 8 = 0 → R (core.num.U64.wrapping_add N k))
    (wN : ∀ k : U64, k.val < 64 → k.val % 8 = 0 → k.val ≠ 24 → W (core.num.U64.wrapping_add N k))
    (rL : ∀ y, LocT st T s y → Hm y → ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ TimerField K.val →
      ¬ GField K.val → R (core.num.U64.wrapping_add y K))
    (wL : ∀ y, LocT st T s y → Hm y → ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ GateField K.val →
      ¬ TimerField K.val → ¬ GField K.val → K.val ≠ 3328 → K.val ≠ 3336 →
      W (core.num.U64.wrapping_add y K))
    (rS : ∀ p ∈ Scs, L.mem s (scCoreA p) = L.cpu s → Hs p → ∀ b, Aligned b → InSC p (Z p) b → R b)
    (wS : ∀ p ∈ Scs, L.mem s (scCoreA p) = L.cpu s → Hs p → ∀ b, Aligned b → InSC p (Z p) b → b.val ≠ p.val + 16 → W b)
    (lkL : ∀ y ∈ T, QueuedState (L.mem s (stA y)) → Lk (L.mem s (blockA y)) → ∀ k : U64,
      (k.val = 3496 ∨ k.val = 3504) → R (core.num.U64.wrapping_add y k) ∧ W (core.num.U64.wrapping_add y k))
    (hLk : Lk N)
    (nRW : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      R (L.nodeAt s (L.cpu s) o) ∧ W (L.nodeAt s (L.cpu s) o))
    (rCD : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hSW : StWH st gS T Lk Hm s) (hHw : L.epState X N = obj.NTFN_WAITING → Hm (L.epQ X N).head)
    (hHt : Hm t) (hHs : ∀ y ∈ T, L.mem s (scA y) ≠ 0#u64 → Hs (L.mem s (scA y))) :
    notification.send_signal gS ar X a N badge = notification.send_signal st ar X a N badge ∧
    ∀ X2 a2, notification.send_signal st ar X a N badge = ok (X2, a2) →
      TInv st T Cs Ω H Sg Rp Scs Nt Z Ac X2 ∧ TAgree st T Cs X X2 ∧ L.ksb X2 = L.ksb X ∧ L.cpu X2 = L.cpu X ∧
      ∃ w ∈ T, (L.actionW X2 = sched.ACTION_RESUME_CURRENT ∨ L.actionW X2 = w) ∧ WkKeep st T Ω Sg Scs Z X X2 w ∧
        Blocked (L.mem X (stA w)) ∧ L.mem X (affA w) = L.cpu s ∧ w ≠ L.curW X ∧
        L.mem X2 (stA w) = sched.TS_RUNNING ∧ L.mem X (yieldA w) = 0#u64 ∧ WkV st T Cs Ω H X X2 N := by
  have hTX' := hTX
  obtain ⟨⟨Q, Rq, hq⟩, hBd, hXX, hSS, hSgX⟩ := hTX
  obtain ⟨E, EQ, hEW⟩ := hq.eps
  have hT := hq.tcbs
  have he : N ∈ E := (hEW.2.2.2.2.2.2.2.1 N).2 (Or.inr hHN)
  have hnsΩ : ntfnScA N ∈ Ω := hSgX.sub _ (hXX.1.ntW N hNN)
  -- `TInv`, `TAgree`, `ksb` after the signal on `st`
  have post : ∀ X2 a2, notification.send_signal st ar X a N badge = ok (X2, a2) →
      TInv st T Cs Ω H Sg Rp Scs Nt Z Ac X2 ∧ TAgree st T Cs X X2 ∧ L.ksb X2 = L.ksb X := by
    intro X2 a2 hr
    have tg := notification.send_signal.tagree hA X a N badge hTX' hNN hHN hBA.1 hBA.2
    rw [hr, WP.spec_ok] at tg
    try simp only [WP.uncurry'_pair] at tg
    exact tg
  -- lvm gen 10: the frame's common cases
  have hN0 : NodePlaced st T X (L.cpu X) := hq.nodes _ hq.cur
  have vT : ∀ b y K, OutsideObjs st T Cs X b → y ∈ T → K.val < 4096 → b ≠ core.num.U64.wrapping_add y K :=
    fun b y K ho hy hK e => out_ne_field ho hy (hT y hy) hK (congrArg UScalar.val e).symm
  have vN : ∀ b o, OutsideObjs st T Cs X b → o.val < 4288 → b ≠ L.nodeAt X (L.cpu X) o :=
    fun b o ho h e => out_ne_node ho hq.cur hN0 h (congrArg UScalar.val e).symm
  have vL : ∀ b (xs : List U64), (∀ y ∈ xs, y ∈ T) → OutsideObjs st T Cs X b → ¬ LinkOf .Ep xs b := by
    rintro b xs hxs ho ⟨y, hy, e | e⟩
    · rw [nextA_eq'] at e; exact vT b y _ ho (hxs y hy) (by simp [nextOff]) e
    · rw [prevA_eq'] at e; exact vT b y _ ho (hxs y hy) (by simp [prevOff]) e
  have vR : ∀ b w, b ∉ Ω → w ∈ T → Aligned b → ¬ InRing (L.mem X (scA w)) (scSb Z (L.mem X (scA w))) b := by
    intro b w hΩ hw hb hr
    by_cases h0 : L.mem X (scA w) = 0#u64
    · rw [h0] at hr; unfold scSb at hr; rw [if_pos rfl] at hr
      have i1 := hr.1; have i2 := hr.2
      simp only [pow_zero] at i2
      omega
    · rw [scSb_ne h0] at hr
      exact hΩ (hXX.1.scW _ (hXX.2.2.bound w hw h0).1 b hb hr.inSC)
  have vB : ∀ b w, w ∈ T → OutsideObjs st T Cs X b → b ≠ regA w layout.reg.BADGE := by
    intro b w hw ho e
    have hbv : layout.reg.BADGE.val = 0 := by unfold layout.reg.BADGE layout.reg.RDI; rfl
    obtain ⟨KB, hKB, eB⟩ := regA_eq (hT w hw) (r := layout.reg.BADGE) (by rw [hbv]; omega)
    rw [eB] at e
    exact vT b w KB ho hw (by rw [hKB, hbv]; omega) e
  have vW : ∀ b w, w ∈ T → OutsideObjs st T Cs X b → ¬ WkD st X w b := by
    rintro b w hw ho (e | e | e)
    · rw [stA_eq] at e; exact vT b w _ ho hw (by simp) e
    · exact vB b w hw ho e
    · exact vN b _ ho (by rw [act_val]; omega) e
  have vP : ∀ b, OutsideObjs st T Cs X b → b ≠ L.nodeA X layout.node.REPROGRAM :=
    fun b ho e => vN b _ ho (by simp [layout.node.REPROGRAM]) e
  rcases hwk with ⟨hwt, hcur, haf, hdom, hnd, hyl⟩ | ⟨hidle, hbt, ht0, hrecv, hcur, haf, hdom, hnd, hLkE, rwE, wRt, hyl⟩
  · -- `WAITING`
    refine ⟨WH.wake_wait_fire ar a hTX' hNN hHN hAffSc kX cX kT hcur hac hwt haf hdom hnd rN wN rL wL rS wS lkL hLk
      nRW rCD hSW (hHw hwt) hHs, fun X2 a2 hr => ?_⟩
    obtain ⟨p1, p2, p3⟩ := post X2 a2 hr
    obtain ⟨hE, -, hqr⟩ := hEW.1 N he
    obtain ⟨-, -, -, -, -, k5⟩ := hEW.2.2.2.2.2
    have hwt1 : L.epState X N = 1#u64 := by rw [hwt]; simp [obj.NTFN_WAITING]
    have hne : EQ N ≠ [] := fun h0 => (k5 N he h0).2 hHN hwt1
    obtain ⟨y0, ys, hys⟩ := List.exists_cons_of_ne_nil hne
    obtain ⟨w, ew⟩ : ∃ w, (L.epQ X N).head = w := ⟨_, rfl⟩
    rw [ew] at hcur haf hdom hnd hyl
    have hmem : w ∈ EQ N := by
      have : w = y0 := by rw [← ew, hqr.head, hys]; rfl
      rw [this, hys]; exact List.mem_cons_self
    obtain ⟨-, -, hbl⟩ := hEW.2.2.2.1 N he w hmem
    have hwT : w ∈ T := hqr.mem w hmem
    obtain ⟨P, hscΩ, hAo⟩ := wkpre_true (N := N) hTX' hAffSc kX cX kT hwT hbl haf hdom hnd
    obtain ⟨-, wi, act, wrun, wna⟩ := wake_wait_st ar X a N badge w hq hEW he hwt ew hmem hcur hac P hnsΩ hscΩ hAo hr
    obtain ⟨dΩ, dN, dT⟩ := epfoot_nd (n := N) hq hEW he (fun y hy => hqr.mem y hy)
    refine ⟨p1, p2, p3, wi.2.1, w, hwT, act, wk_keep hTX' hwT wi (fun o ho h8 => dN o ho h8)
      (fun y hy K hK h8 h1 h2 _ => dT y hy K hK h8 h1 h2) (fun c hc b hb hin => dΩ b hb (hXX.1.scW c hc b hb hin))
      (fun b hb hΩ _ => dΩ b hb hΩ),
      hbl, haf, hcur, wrun, hyl, fun b hb ho hΩ h1 h2 _ => wi.mem_eq hb ?_,
      fun _ => wna (fun h0 => by unfold scSb; rw [if_pos h0])⟩
    rintro ((hl | e | e) | hd | hr' | e)
    · exact vL b _ (fun y hy => hqr.mem y hy) ho hl
    · exact h1 e
    · exact h2 e
    · exact vW b w hwT ho hd
    · exact vR b w hΩ hwT hb hr'
    · exact vP b ho e
  · -- idle-bound `Recv`
    obtain ⟨ep, heq⟩ : ∃ ep, L.mem X (blockA t) = ep := ⟨_, rfl⟩
    obtain ⟨r, hr⟩ : ∃ r, L.mem X (replyA t) = r := ⟨_, rfl⟩
    rw [heq] at hLkE rwE
    rw [hr] at wRt
    refine ⟨WH.wake_recv_fire ar a hTX' hNN hHN hAffSc kX cX kT hidle hbt ht0 hrecv heq hr hcur hac haf hdom hnd rN
      rL wL rS wS lkL hLkE rwE wRt nRW rCD hSW hHt hHs, fun X2 a2 hrun => ?_⟩
    obtain ⟨p1, p2, p3⟩ := post X2 a2 hrun
    have htT : t ∈ T := by
      rcases TInv.ntb hTX' N hNN with h | h
      · rw [hbt] at h; exact absurd h ht0
      · rwa [hbt] at h
    have hblk : Blocked (L.mem X (stA t)) := Or.inr (Or.inl hrecv)
    obtain ⟨hep, hmem⟩ := hEW.2.2.2.2.1 t htT (by simp) hblk
    rw [heq] at hep hmem
    obtain ⟨P, hscΩ, hAo⟩ := wkpre_true (N := N) hTX' hAffSc kX cX kT htT hblk haf hdom hnd
    obtain ⟨-, wi, act, wrun⟩ := wake_recv_st ar X a N badge t ep r hq hEW hidle hbt ht0 hrecv heq hep hmem hr
      (fun hr0 => (recv_rt (Z := Z) hTX' hNN htT hrecv hr hr0).1) hcur hac P hnsΩ hscΩ
      (fun hr0 => (recv_rt (Z := Z) hTX' hNN htT hrecv hr hr0).2) hAo hrun
    have hN : NodePlaced st T X (L.cpu X) := hq.nodes _ hq.cur
    have hcC := hq.cur
    have ht' := hT t htT
    obtain ⟨dΩ, dN, dT⟩ := epfoot_nd (n := ep) hq hEW hep (fun y hy => (hEW.1 ep hep).2.2.mem y hy)
    have hrO : r ≠ 0#u64 → OutsideObjs st T Cs X (rTcbA r) ∧ (rTcbA r).val = r.val ∧
        ∀ c ∈ Scs, r.val + 32 ≤ c.val ∨ c.val + 2 ^ Z c ≤ r.val := by
      intro hr0
      have hrp : r ∈ Rp := by
        have := (hXX.2.1.recv t htT hrecv (by rw [hr]; exact hr0)).1; rwa [hr] at this
      obtain ⟨-, rv, -, -⟩ := rp_facts hXX.1 hrp
      exact ⟨hq.omega _ (hSgX.sub _ (hXX.1.tcbW hrp)), rv, hXX.1.rpSc r hrp⟩
    obtain ⟨k1, -⟩ := hEW.2.2.2.2.2
    have hHep : H ep = some .ep := by have := k1 t htT (by simp) (Or.inr hrecv); rwa [heq] at this
    refine ⟨p1, p2, p3, wi.2.1, t, htT, act, wk_keep hTX' htT wi ?_ ?_ ?_ ?_, hblk, haf, hcur, wrun, hyl,
      fun b hb ho hΩ _ _ h3 => wi.mem_eq hb ?_,
      fun hw => absurd (hidle.symm.trans hw) (by unfold obj.NTFN_IDLE obj.NTFN_WAITING; decide)⟩
    rotate_left 4
    · rintro ((e | hf | ⟨hr0, e⟩ | e) | hd | hr' | e)
      · unfold faultA at e; exact vT b t _ ho htT (by simp) e
      · rcases hf with hl | e | e
        · exact vL b _ (fun y hy => (hEW.1 ep hep).2.2.mem y hy) ho hl
        · exact (h3 ep hHep).1 e
        · exact (h3 ep hHep).2 e
      · have hrp : r ∈ Rp := by
          have := (hXX.2.1.recv t htT hrecv (by rw [hr]; exact hr0)).1; rwa [hr] at this
        subst e; exact hΩ (hSgX.sub _ (hXX.1.tcbW hrp))
      · rw [stA_eq] at e; exact vT b t _ ho htT (by simp) e
      · exact vW b t htT ho hd
      · exact vR b t hΩ htT hb hr'
      · exact vP b ho e
    · intro o ho h8
      rintro (e | hf | ⟨hr0, e⟩ | e)
      · unfold faultA at e; exact node_ne_field hN ho htT ht' (by simp) e
      · exact dN o ho h8 hf
      · exact out_ne_node (hrO hr0).1 hcC hN ho (congrArg UScalar.val e)
      · rw [stA_eq] at e; exact node_ne_field hN ho htT ht' (by simp) e
    · intro y hy K hK h8 h1 h2 hyw
      rintro (e | hf | ⟨hr0, e⟩ | e)
      · unfold faultA at e; exact field_ne (hT y hy) ht' hK (by simp) (fun h => by simp; exact (hyw h).2) e
      · exact dT y hy K hK h8 h1 h2 hf
      · exact out_ne_field (hrO hr0).1 hy (hT y hy) hK (congrArg UScalar.val e)
      · rw [stA_eq] at e; exact field_ne (hT y hy) ht' hK (by simp) (fun h => by simp; exact (hyw h).1) e
    · intro c hc b hb hin
      have ho := hq.omega b (hXX.1.scW c hc b hb hin)
      rintro (e | hf | ⟨hr0, e⟩ | e)
      · subst e; unfold faultA at ho; exact out_ne_field ho htT ht' (by simp) rfl
      · exact dΩ b hb (hXX.1.scW c hc b hb hin) hf
      · obtain ⟨-, rv, rs⟩ := hrO hr0
        have ev := congrArg UScalar.val e
        rw [rv] at ev
        have := rs c hc; have := hin.1; have := hin.2
        omega
      · subst e; rw [stA_eq] at ho; exact out_ne_field ho htT ht' (by simp) rfl
    · intro b hb hΩ hSg
      have ho := hq.omega b hΩ
      rintro (e | hf | ⟨hr0, e⟩ | e)
      · subst e; unfold faultA at ho; exact out_ne_field ho htT ht' (by simp) rfl
      · exact dΩ b hb hΩ hf
      · have hrp : r ∈ Rp := by
          have := (hXX.2.1.recv t htT hrecv (by rw [hr]; exact hr0)).1; rwa [hr] at this
        subst e; exact hSg (hXX.1.tcbW hrp)
      · subst e; rw [stA_eq] at ho; exact out_ne_field ho htT ht' (by simp) rfl

set_option maxRecDepth 4000 in
set_option maxHeartbeats 16000000 in
/-- **`fire` with one due timer whose signal wakes a thread** (module docstring). -/
theorem fire_wk_step {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) {s X : S} (a : A)
    {TM N now t : U64} {Lk : U64 → Prop} {U : Set U64}
    {s1 : S} {cpu : U64} {ct : obj.Tcb} {p : localtimer.TimerIrqPlan}
    (hTX : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac X) (hBA : BufAt st T Cs H Sg Scs Z U X)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (hAffSc : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t))
    (kX : L.ksb X = L.ksb s) (cX : L.cpu X = L.cpu s)
    (kT : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (K.val < 3528 ∨ 3576 ≤ K.val) →
      L.mem X (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K))
    (eTM : L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN) = TM) (hne : TM ≠ 0#u64) (hTMT : TM ∈ T)
    (hTMl : L.mem s (affA TM) = L.cpu s)
    (hct : L.mem X (L.nodeAt X (L.cpu X) layout.node.CUR_TIME) = now) (hdue : ¬ L.mem X (tdA TM) > now)
    (eN : L.mem X (boundA TM) = N) (hN0 : N ≠ 0#u64)
    (hac : L.actionW X = sched.ACTION_RESUME_CURRENT)
    (hwk : ∀ X1, WritesIn st X X1 (Fl4Proofs.P1.TW st T Cs X) → WkCase st R W Lk (L.cpu s) X1 N t)
    (hpt : p.tm = TM)
    (hag : ∀ y ∈ T, ∀ K : U64, 3528 ≤ K.val → K.val < 3576 → K.val % 8 = 0 →
      L.mem s1 (core.num.U64.wrapping_add y K) = L.mem X (core.num.U64.wrapping_add y K))
    (hfo : localtimer.fire_ok st s1 cpu ct p now = ok true)
    (rN : ∀ k : U64, k.val < 64 → k.val % 8 = 0 → R (core.num.U64.wrapping_add N k))
    (wN : ∀ k : U64, k.val < 64 → k.val % 8 = 0 → k.val ≠ 24 → W (core.num.U64.wrapping_add N k))
    (rL : ∀ y, LocT st T s y → Hm y → ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ TimerField K.val →
      ¬ GField K.val → R (core.num.U64.wrapping_add y K))
    (wL : ∀ y, LocT st T s y → Hm y → ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ GateField K.val →
      ¬ TimerField K.val → ¬ GField K.val → K.val ≠ 3328 → K.val ≠ 3336 →
      W (core.num.U64.wrapping_add y K))
    (rS : ∀ p ∈ Scs, L.mem s (scCoreA p) = L.cpu s → Hs p → ∀ b, Aligned b → InSC p (Z p) b → R b)
    (wS : ∀ p ∈ Scs, L.mem s (scCoreA p) = L.cpu s → Hs p → ∀ b, Aligned b → InSC p (Z p) b → b.val ≠ p.val + 16 → W b)
    (lkL : ∀ y ∈ T, QueuedState (L.mem s (stA y)) → Lk (L.mem s (blockA y)) → ∀ k : U64,
      (k.val = 3496 ∨ k.val = 3504) → R (core.num.U64.wrapping_add y k) ∧ W (core.num.U64.wrapping_add y k))
    (hLk : Lk N)
    (nRW : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      R (L.nodeAt s (L.cpu s) o) ∧ W (L.nodeAt s (L.cpu s) o))
    (rCD : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hSW : StWH st gS T Lk Hm s)
    (hHw : ∀ X1, WritesIn st X X1 (Fl4Proofs.P1.TW st T Cs X) → L.epState X1 N = obj.NTFN_WAITING →
      Hm (L.epQ X1 N).head) (hHt : Hm t) (hHtm : Hm TM) (hHs : ∀ y ∈ T, L.mem s (scA y) ≠ 0#u64 → Hs (L.mem s (scA y)))
    (rD : R (tdA TM)) (rB : R (tbA TM)) (rDa : ∀ y ∈ T, FootLtArmed st X (L.cpu X) y → R (tdA y))
    (hrmg : timer.remove gS X TM = timer.remove st X TM) :
    ∃ Y aY, timer.fire st ar X a = ok (Y, aY) ∧ timer.fire gS ar X a = timer.fire st ar X a ∧
      TInv st T Cs Ω H Sg Rp Scs Nt Z Ac Y ∧ FireStop st R Y now ∧ L.ksb Y = L.ksb s ∧ L.cpu Y = L.cpu s ∧
      ∃ w ∈ T, (L.actionW Y = sched.ACTION_RESUME_CURRENT ∨ L.actionW Y = w) ∧ FwKeep st T Ω Sg Scs Z X Y w ∧
        Blocked (L.mem X (stA w)) ∧ L.mem X (affA w) = L.cpu s ∧ w ≠ L.curW X ∧
        L.mem Y (stA w) = sched.TS_RUNNING ∧ L.mem X (yieldA w) = 0#u64 ∧ WkV st T Cs Ω H X Y N := by
  have hTX' := hTX
  obtain ⟨⟨Q, Rq, hq⟩, -, hXX, -, -⟩ := hTX
  have hN := hq.nodes _ hq.cur
  have eXN : ∀ o, L.nodeAt X (L.cpu X) o = L.nodeAt s (L.cpu s) o := fun o => by rw [cX, nodeAt_of_ksb kX]
  have hNN : N ∈ Nt := by
    have := hXX.2.2.bnd TM hTMT (by rw [eN]; exact hN0); rwa [eN] at this
  -- `remove`
  obtain ⟨X1, eX1, hT1, -, -, tk1, w31⟩ := spec_ex_fd (timer.remove.tf (s0 := X) X TM (TF.start hTX') hTMT)
  have F1 := timer.remove.ibFr X TM hTX' hTMT
  rw [eX1, WP.spec_ok] at F1
  have BA1 : BufAt st T Cs H Sg Scs Z U X1 := hBA.of_fr F1
  have kT1 : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (K.val < 3528 ∨ 3576 ≤ K.val) →
      L.mem X1 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K h1 h2 h3 => (tk1 y hy K h1 h2 h3).trans (kT y hy K h1 h2 h3)
  have kX1 : L.ksb X1 = L.ksb s := w31.1.trans kX
  have cX1 : L.cpu X1 = L.cpu s := w31.2.1.trans cX
  have bX1 : L.mem X1 (boundA TM) = N := by
    rw [← eN]; exact tk1 TM hTMT 3368#u64 (by simp) (by simp) (Or.inl (by simp))
  have hac1 : L.actionW X1 = sched.ACTION_RESUME_CURRENT := by
    rw [← hac]
    unfold LawfulStore.actionW
    rw [w31.2.1, nodeAt_of_ksb w31.1]
    exact w31.mem_eq (nodeAt_aligned hN (by rw [act_val]; omega) (by rw [act_val]))
      (node_not_tw hq (by rw [act_val]; omega) (by rw [act_val]; omega) (by rw [act_val]; omega))
  -- the waking signal
  obtain ⟨gsig, ssig⟩ := WH.wk_sig (badge := L.mem X (tbA TM)) ar hA a hT1 BA1 hNN (hNt N hNN) hAffSc kX1 cX1 kT1
    hac1 (hwk X1 w31) rN wN rL wL rS wS lkL hLk nRW rCD hSW (hHw X1 w31) hHt hHs
  obtain ⟨⟨X2, a2⟩, eX2, -⟩ := spec_ex_fd
    (notification.send_signal.tagree hA X1 a N (L.mem X (tbA TM)) hT1 hNN (hNt N hNN) BA1.1 BA1.2)
  obtain ⟨T2, -, k2, c2, w, hwT, act2, kp, wbl, waf, wcur, wrun, wyl, kv⟩ := ssig X2 a2 eX2
  have hsg : (if L.mem X1 (boundA TM) != 0#u64 then
      notification.send_signal st ar X1 a (L.mem X1 (boundA TM)) (L.mem X (tbA TM)) else ok (X1, a)) =
      ok (X2, a2) := by
    rw [bX1, if_pos (bne_iff_ne.mpr hN0)]; exact eX2
  have hst : FireStop st R (L.wr X2 (L.nodeAt X2 (L.cpu X2) layout.node.REPROGRAM) 1#u64) now := by
    refine fire_stop_sig hA hTX' hBA hNt (by rw [eTM, hpt]) (by rw [hpt]; exact hne) hag hfo
      (by rw [hpt]; exact eX1) (fun h => by rw [hpt] at h ⊢; rw [bX1] at h ⊢; exact hNN)
      (by rw [hpt]; exact hsg) ?_ rDa
    rw [eXN]; exact (nRW _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])).1
  have hfire : timer.fire st ar X a =
      ok (L.wr X2 (L.nodeAt X2 (L.cpu X2) layout.node.REPROGRAM) 1#u64, a2) :=
    fire_run (R' := R) ar X a (by rw [eTM]; exact hne) (by rw [eTM, hct]; exact hdue) (by rw [eTM]; exact eX1)
      (by rw [eTM]; exact hsg) (by rw [hct]; exact hst)
  have e2N : ∀ o, L.nodeAt X2 (L.cpu X2) o = L.nodeAt s (L.cpu s) o := fun o => by
    rw [c2, nodeAt_of_ksb k2, cX1, nodeAt_of_ksb kX1]
  have gfire : timer.fire gS ar X a = timer.fire st ar X a := by
    refine timer.fire.guard_one ar X a
      (by rw [eXN]; exact (nRW _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).1)
      (by rw [eXN]; exact (nRW _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])).1)
      (by rw [eTM]; exact hne) (by rw [eTM]; exact rD) (by rw [eTM, hct]; exact hdue) (by rw [eTM]; exact rB)
      (by rw [eTM]; exact hrmg) ?_
    rw [eTM]
    intro X1' e1'
    rw [eX1] at e1'
    obtain rfl := ok_inj_ff e1'
    refine ⟨rL TM ⟨hTMT, hTMl⟩ hHtm 3368#u64 (by simp) (by simp) (by simp) (by simp [TimerField]) (by simp [GField]),
      fun _ => by rw [bX1]; exact gsig, fun X2' a2' e2' => ?_⟩
    rw [hsg] at e2'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (ok_inj_ff e2')
    refine ⟨by rw [e2N]; exact (nRW _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])).2, ?_⟩
    rw [hct]; exact hst
  -- the state after `fire`
  have hN2 : NodePlaced st T X2 (L.cpu X2) := by rw [c2, cX1, ← cX]; exact hN.ksb (k2.trans (kX1.trans kX.symm))
  have aRP : Aligned (L.nodeAt X2 (L.cpu X2) layout.node.REPROGRAM) :=
    nodeAt_aligned hN2 (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
  have aSA : Aligned (L.nodeAt X2 (L.cpu X2) layout.node.SCHED_ACTION) :=
    nodeAt_aligned hN2 (by rw [act_val]; omega) (by rw [act_val])
  have nRA : L.nodeAt X2 (L.cpu X2) layout.node.REPROGRAM ≠ L.nodeAt X2 (L.cpu X2) layout.node.SCHED_ACTION :=
    nodeAt_ne hN2 (by simp [layout.node.REPROGRAM]) (by rw [act_val]; omega)
      (by rw [act_val]; simp [layout.node.REPROGRAM])
  have eA : L.actionW (L.wr X2 (L.nodeAt X2 (L.cpu X2) layout.node.REPROGRAM) 1#u64) = L.actionW X2 := by
    unfold LawfulStore.actionW
    rw [nodeAt_of_ksb (L.ksb_wr _ _ _), LawfulStore.cpu_wr]
    exact mem_wr_ne' aRP aSA nRA
  have hT := hq.tcbs
  have kY : FwKeep st T Ω Sg Scs Z X (L.wr X2 (L.nodeAt X2 (L.cpu X2) layout.node.REPROGRAM) 1#u64) w := by
    have eRP : L.nodeAt X2 (L.cpu X2) layout.node.REPROGRAM = L.nodeAt X (L.cpu X) layout.node.REPROGRAM := by
      rw [e2N, eXN]
    have e1X : ∀ o, L.nodeAt X1 (L.cpu X1) o = L.nodeAt X (L.cpu X) o := fun o => by
      rw [cX1, nodeAt_of_ksb kX1, eXN]
    refine ⟨fun o ho h8 h16 h56 h104 h112 => ?_, fun y hy K hK h8 hK' h1 h2 hyw => ?_,
      fun c hc hne b hb hin => ?_, fun b hb hΩ hSg => ?_⟩
    · rw [mem_wr_ne' aRP (nodeAt_aligned hN ho h8) (by
          rw [eRP]; exact nodeAt_ne hN (by simp [layout.node.REPROGRAM]) ho (by simp [layout.node.REPROGRAM]; omega)),
        ← e1X o, kp.1 o ho h8 h16 h56, e1X o]
      exact w31.mem_eq (nodeAt_aligned hN ho h8) (node_not_tw hq ho h104 h112)
    · have hy' := hT y hy
      rw [mem_wr_ne' aRP (field_aligned hy' hK h8) (by
          rw [eRP]; exact node_ne_field hN (by simp [layout.node.REPROGRAM]) hy hy' hK),
        kp.2.1 y hy K hK h8 h1 h2 hyw]
      exact tk1 y hy K hK h8 hK'
    · have ho := hq.omega b (hXX.1.scW c hc b hb hin)
      have e3 : L.mem X1 (scA w) = L.mem X (scA w) := tk1 w hwT 3464#u64 (by simp) (by simp) (Or.inl (by simp))
      rw [mem_wr_ne' aRP hb (fun e => out_ne_node (o := layout.node.REPROGRAM) ho hq.cur hN (by simp [layout.node.REPROGRAM]) (by rw [← eRP, e])),
        kp.2.2.1 c hc (by rw [e3]; exact hne) b hb hin]
      exact w31.mem_eq hb (out_not_tw hT hq.nodes ho)
    · have ho := hq.omega b hΩ
      rw [mem_wr_ne' aRP hb (fun e => out_ne_node (o := layout.node.REPROGRAM) ho hq.cur hN (by simp [layout.node.REPROGRAM]) (by rw [← eRP, e])),
        kp.2.2.2 b hb hΩ hSg]
      exact w31.mem_eq hb (out_not_tw hT hq.nodes ho)
  have wfacts : Blocked (L.mem X (stA w)) ∧ L.mem X (affA w) = L.cpu s ∧ w ≠ L.curW X := by
    have e1 : L.mem X1 (stA w) = L.mem X (stA w) := by
      rw [stA_eq]; exact tk1 w hwT 3328#u64 (by simp) (by simp) (Or.inl (by simp))
    have e2 : L.mem X1 (affA w) = L.mem X (affA w) := tk1 w hwT 3520#u64 (by simp) (by simp) (Or.inl (by simp))
    have e3 : L.curW X1 = L.curW X := by
      unfold LawfulStore.curW
      rw [w31.2.1, nodeAt_of_ksb w31.1]
      exact w31.mem_eq (nodeAt_aligned hN (by rw [curth_val]; omega) (by rw [curth_val]))
        (node_not_tw hq (by rw [curth_val]; omega) (by rw [curth_val]; omega) (by rw [curth_val]; omega))
    rw [e1] at wbl; rw [e2] at waf; rw [e3] at wcur
    exact ⟨wbl, waf, wcur⟩
  have rY : L.mem (L.wr X2 (L.nodeAt X2 (L.cpu X2) layout.node.REPROGRAM) 1#u64) (stA w) = sched.TS_RUNNING := by
    rw [stA_eq, mem_wr_ne' aRP (field_aligned (hT w hwT) (by simp) (by simp))
      (node_ne_field hN2 (by simp [layout.node.REPROGRAM]) hwT (hT w hwT) (by simp)), ← stA_eq]
    exact wrun
  -- lvm gen 10: the words outside the objects and `Ω`, and `N`'s state
  have eRP' : L.nodeAt X2 (L.cpu X2) layout.node.REPROGRAM = L.nodeAt X (L.cpu X) layout.node.REPROGRAM := by
    rw [e2N, eXN]
  have kX2 : L.ksb X2 = L.ksb X := k2.trans (kX1.trans kX.symm)
  have kV : WkV st T Cs Ω H X (L.wr X2 (L.nodeAt X2 (L.cpu X2) layout.node.REPROGRAM) 1#u64) N := by
    refine ⟨fun b hb ho hΩ h1 h2 h3 => ?_, fun hw => ?_⟩
    · rw [mem_wr_ne' aRP hb (fun e => out_ne_node (o := layout.node.REPROGRAM) ho hq.cur hN
          (by simp [layout.node.REPROGRAM]) (by rw [← eRP', e])),
        kv.1 b hb (ho.ksb (kX1.trans kX.symm)) hΩ h1 h2 h3]
      exact w31.mem_eq hb (out_not_tw hT hq.nodes ho)
    · have oT : OutsideObjs st T Cs X (epTSA N) := ntfn_ts_out hq (hNt N hNN)
      have e1 : L.epState X1 N = L.epState X N := by
        unfold LawfulStore.epState
        rw [w31.mem_eq oT.1 (out_not_tw hT hq.nodes oT)]
      have hna := kv.2 (by rw [e1]; exact hw)
      unfold LawfulStore.epState at hna ⊢
      rw [mem_wr_ne' aRP oT.1 (fun e => out_ne_node (o := layout.node.REPROGRAM) oT hq.cur hN
          (by simp [layout.node.REPROGRAM]) (by rw [← eRP', e]))]
      exact hna
  refine ⟨_, a2, hfire, gfire, reprogram.tinv T2, hst, ?_, ?_, w, hwT, by rw [eA]; exact act2, kY, wfacts.1,
    wfacts.2.1, wfacts.2.2, rY, ?_, kV⟩
  · rw [L.ksb_wr]; exact k2.trans kX1
  · rw [LawfulStore.cpu_wr]; exact c2.trans cX1
  · rw [← wyl]; exact (tk1 w hwT 3472#u64 (by simp) (by simp) (Or.inl (by simp))).symm

end main

end Fl4Proofs.P2.WH
