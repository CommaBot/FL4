/-
# P2 (p2lf): a fired timer's waking signal on the guarded store, from the entry state's word sets

`wake_wait_guard` (`P2/FootTimerFireWk`) asks its reads / writes word by word at the signal's start state `X`.
Here they come from the entry state `s` of the timer interrupt, through broad per-class premises (what the caller
gets from `FireRd ∨ LocRd ∨ LkW` / `FireWr ∨ LocWr ∨ LkW` at `s`): the bound notification's words (`rN` / `wN`),
words of threads homed here outside their timer fields and queue links (`rL` / `wL`, no `STATE` write), words of
SCs homed here (`rS` / `wS`, no `CORE` write), queue links of a thread queued on an object whose lock is held
(`lkL`), this core's node words (`nRW`), and `STATE` writes answered per state (`StW`). The facts at `X` come from
P1's `TInv` at `X` (queues, SCs) and the TCB words outside the timer fields kept since `s` (`kT`).

* `qmem_nbrs`: a queue member's neighbours are members.
* `StW`: the per-state `STATE` write premise (for `move` by `stepOK_state` and `PlanLk`, for `acc` by `GWr`).
* `wake_wait_fire`: the `WAITING` branch of `send_signal` on `gS` is its real run.

No named premises.
-/
import Fl4Proofs.P2.FootTimerFireLoc
import Fl4Proofs.P2.FootTimerFireWk
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap
open Fl4Proofs.P2.PathObl (NodeSt ScAcc)

/-- A queue member's neighbours are members. -/
theorem qmem_nbrs {m : U64 → U64} {T : Set U64} {l : tcbqueue.Link} {q : tcbqueue.Queue} {xs : List U64}
    {t : U64} (h : QueueRel m T l q xs) (ht : t ∈ xs) :
    (q.end ≠ t → m (nextA l t) ∈ xs) ∧ (q.head ≠ t → m (prevA l t) ∈ xs) := by
  obtain ⟨xs1, bs, rfl⟩ := List.append_of_mem ht
  have hs := (Seg_mid m l 0#u64 xs1 t bs 0#u64).1 h.seg
  refine ⟨fun he => ?_, fun hh => ?_⟩
  · rw [hs.2.2.1]
    cases bs with
    | nil => exact absurd (by rw [h.last]; simp) he
    | cons y ys => simp
  · rw [hs.2.1]
    obtain rfl | ⟨zs, z, rfl⟩ := xs1.eq_nil_or_concat
    · exact absurd (by rw [h.head]; simp) hh
    · simp

section
variable {S : Type}

/-- **The per-state `STATE` write premise of a waking run** (module docstring): a `STATE` write of a non-queued
value to a thread homed here at `s`, at a state where it is still homed here and, if queued, blocked on an object
whose lock is held (`Lk`). -/
def StW (st gS : machine.Store S) [L : LawfulStore st] (T : Set U64) (Lk : U64 → Prop) (s : S) : Prop :=
  ∀ X y v, LocT st T s y → L.mem X (affA y) = L.cpu s →
    (QueuedState (L.mem X (stA y)) → Lk (L.mem X (blockA y))) → ¬ QueuedState v →
    gS.write X (stA y) v = st.write X (stA y) v

end

section wait
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}

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
    (rL : ∀ y, LocT st T s y → ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ TimerField K.val →
      ¬ GField K.val → R (core.num.U64.wrapping_add y K))
    (wL : ∀ y, LocT st T s y → ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ GateField K.val →
      ¬ TimerField K.val → ¬ GField K.val → K.val ≠ 3328 → W (core.num.U64.wrapping_add y K))
    (rS : ∀ p ∈ Scs, L.mem s (scCoreA p) = L.cpu s → ∀ b, Aligned b → InSC p (Z p) b → R b)
    (wS : ∀ p ∈ Scs, L.mem s (scCoreA p) = L.cpu s → ∀ b, Aligned b → InSC p (Z p) b → b.val ≠ p.val + 16 → W b)
    (lkL : ∀ y ∈ T, QueuedState (L.mem s (stA y)) → Lk (L.mem s (blockA y)) → ∀ k : U64,
      (k.val = 3496 ∨ k.val = 3504) → R (core.num.U64.wrapping_add y k) ∧ W (core.num.U64.wrapping_add y k))
    (hLk : Lk N)
    (nRW : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      R (L.nodeAt s (L.cpu s) o) ∧ W (L.nodeAt s (L.cpu s) o))
    (rCD : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hSW : StW st gS T Lk s) :
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
  rw [ew] at hcur haf hdom hnd
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
      R (core.num.U64.wrapping_add w K) := rL w hloc
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
  let sb : Nat := Z (L.mem X (scA w))
  have P : WkPre st R W X w N sb := by
    refine ⟨fun h0 => ?_, fun _ => ?_, hnd, hdom, by rw [haf, cX], fun h0 => ?_, fun h0 => ?_, fun h0 => ?_,
      fun h0 => ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨c1, c2, -⟩ := scF h0
      have hcq := scq_of hXX.1 hSS c1
      exact rS _ c1 c2 _ hcq.2.2.2.2 hcq.2.2.2.1
    · exact rN layout.ntfn.SC (by simp [layout.ntfn.SC]) (by simp [layout.ntfn.SC])
    · obtain ⟨c1, c2, -⟩ := scF h0
      obtain ⟨hP, hz⟩ := hXX.1.sc _ c1
      obtain ⟨h8, h128, -⟩ := sc_lo hP hz
      have hv := sc_word_val hP hz (o := layout.sc.SPORADIC) (by simp [layout.sc.SPORADIC])
      have hsv : layout.sc.SPORADIC.val = 64 := by simp [layout.sc.SPORADIC]
      exact rS _ c1 c2 _ (by unfold Aligned; unfold sporA; rw [hv, hsv]; omega)
        ⟨by unfold sporA; rw [hv]; omega, by unfold sporA; rw [hv, hsv]; omega⟩
    · obtain ⟨c1, c2, -⟩ := scF h0
      have hcq := scq_of hXX.1 hSS c1
      refine ⟨fun b ha hb => rS _ c1 c2 b ha hb, fun b ha hb => wS _ c1 c2 b ha hb.inSC (by
        have := hb.1; omega), ?_⟩
      obtain ⟨⟨q1, q2⟩, q3⟩ := hcq.2.2.1
      have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
      obtain ⟨hP, hz⟩ := hXX.1.sc _ c1
      have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
      exact wS _ c1 c2 _ q3 ⟨q1, q2⟩ (by rw [hv, hcv]; omega)
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
    (by rw [eKB]; exact wL w hloc KB (by omega) (by omega) (by omega) gB1 gB2 gB3 (by omega)) hac ?_ P
    (hSgX.sub _ (hXX.1.ntW N hNN)) (fun h0 b hb hin => hXX.1.scW _ (scF h0).1 b hb hin)
  intro Y wY
  obtain ⟨kT', -, -⟩ := epfoot_keep hq hEW he (fun y hy => hqr.mem y hy) wY
  refine hSW Y w _ hloc ?_ (fun _ => ?_) (by simp [QueuedState, sched.TS_RUNNING])
  · unfold affA
    rw [kT' w hwT 3520#u64 (by simp) (by simp) (by simp) (by simp)]
    exact (kT w hwT 3520#u64 (by simp) (by simp) (Or.inl (by simp))).trans hloc.2
  · rw [blockA_eq, kT' w hwT 3336#u64 (by simp) (by simp) (by simp) (by simp), ← blockA_eq, hbw]; exact hLk

end wait

end Fl4Proofs.P2
