/-
# P2 (p2lf): the woken thread's `WkPre` at the signal's start state, from the entry state's word sets

`wake_wait_fire` / `wake_recv_fire` build `WkPre` inside; the `st` runs `wake_wait_st` / `wake_recv_st` need it too
(with any `R` / `W`, e.g. `fun _ => True`), together with the SC's placement in `Ω` and the `SCHED_ACTION` word
outside the SC. `wkpre_fire` gives all three from `TInv` at the start state `X` and the per-class premises at the
entry state `s`, with the SC size `scSb Z (scA w)` (`P2/FootTimerFireWr`).

No named premises.
-/
import Fl4Proofs.P2.FootTimerFireWr
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap
open Fl4Proofs.P2.PathObl (NodeSt ScAcc)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}

set_option maxHeartbeats 4000000 in
/-- **The woken thread's `WkPre`, its SC in `Ω` and `SCHED_ACTION` outside its SC** (module docstring). -/
theorem wkpre_fire {s X : S} {w N : U64}
    (hTX : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac X)
    (hAffSc : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t))
    (kX : L.ksb X = L.ksb s) (cX : L.cpu X = L.cpu s)
    (kT : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (K.val < 3528 ∨ 3576 ≤ K.val) →
      L.mem X (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K))
    (hwT : w ∈ T) (hbl : Blocked (L.mem X (stA w))) (haf : L.mem X (affA w) = L.cpu s)
    (hdom : L.mem X (domA w) = L.mem X (core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN))
    (hnd : L.mem X (scA w) = 0#u64 → L.mem X (ntfnScA N) = 0#u64)
    (rNs : R (ntfnScA N))
    (rS : ∀ p ∈ Scs, L.mem s (scCoreA p) = L.cpu s → ∀ b, Aligned b → InSC p (Z p) b → R b)
    (wS : ∀ p ∈ Scs, L.mem s (scCoreA p) = L.cpu s → ∀ b, Aligned b → InSC p (Z p) b → b.val ≠ p.val + 16 → W b)
    (nRW : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      R (L.nodeAt s (L.cpu s) o) ∧ W (L.nodeAt s (L.cpu s) o))
    (rCD : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN)) :
    WkPre st R W X w N (scSb Z (L.mem X (scA w))) ∧
      (L.mem X (scA w) ≠ 0#u64 → ∀ b, Aligned b → InSC (L.mem X (scA w)) (scSb Z (L.mem X (scA w))) b → b ∈ Ω) ∧
      Outside (L.nodeA X layout.node.SCHED_ACTION) (L.mem X (scA w)) (scSb Z (L.mem X (scA w))) := by
  obtain ⟨⟨Q, Rq, hq⟩, hBd, hXX, hSS, -⟩ := hTX
  have k3464 : L.mem X (scA w) = L.mem s (scA w) := by
    rw [scA_eq]; exact kT w hwT 3464#u64 (by simp) (by simp) (Or.inl (by simp))
  have hafs : L.mem s (affA w) = L.cpu s := by
    rw [← haf]; unfold affA; exact (kT w hwT 3520#u64 (by simp) (by simp) (Or.inl (by simp))).symm
  have eN : ∀ o, L.nodeAt X (L.cpu X) o = L.nodeAt s (L.cpu s) o := fun o => by rw [cX, nodeAt_of_ksb kX]
  have hN : NodePlaced st T X (L.cpu X) := hq.nodes _ hq.cur
  have scF : L.mem X (scA w) ≠ 0#u64 → L.mem X (scA w) ∈ Scs ∧ L.mem s (scCoreA (L.mem X (scA w))) = L.cpu s ∧
      L.mem X (scA w) ∈ Ac := by
    intro h0
    have hs0 : L.mem s (scA w) ≠ 0#u64 := by rw [← k3464]; exact h0
    refine ⟨(hXX.2.2.toScExtra0.bound w hwT h0).1, by rw [k3464, hAffSc w hwT hs0]; exact hafs, ?_⟩
    exact hBd.sact w hwT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hbl)))))) h0
  have esb : L.mem X (scA w) ≠ 0#u64 → scSb Z (L.mem X (scA w)) = Z (L.mem X (scA w)) := fun h0 => scSb_ne h0
  -- a node word against the SC
  have outN : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → 0 < o.val →
      Outside (L.nodeAt X (L.cpu X) o) (L.mem X (scA w)) (scSb Z (L.mem X (scA w))) := by
    intro o ho h8 hpos
    by_cases h0 : L.mem X (scA w) = 0#u64
    · unfold Outside scSb; rw [h0, if_pos rfl]; right
      rw [nodeAt_val hN ho]; simp; omega
    · rw [esb h0]
      obtain ⟨c1, -, -⟩ := scF h0
      have aR : Aligned (L.nodeAt X (L.cpu X) o) := nodeAt_aligned hN ho h8
      unfold Outside
      by_contra hc
      push_neg at hc
      have hΩ := hXX.1.scW _ c1 _ aR ⟨hc.1, hc.2⟩
      exact out_ne_node (hq.omega _ hΩ) hq.cur hN ho rfl
  refine ⟨⟨fun h0 => ?_, fun _ => rNs, hnd, hdom, by rw [haf, cX], fun h0 => ?_, fun h0 => ?_, fun h0 => ?_,
      fun h0 => ?_, ?_, ?_, ?_, ?_⟩, fun h0 b hb hin => hXX.1.scW _ (scF h0).1 b hb (by rw [← esb h0]; exact hin),
      outN _ (by rw [act_val]; omega) (by rw [act_val]) (by rw [act_val]; omega)⟩
  · obtain ⟨c1, c2, -⟩ := scF h0
    have hcq := scq_of hXX.1 hSS c1
    exact rS _ c1 c2 _ hcq.2.2.2.2 hcq.2.2.2.1
  · obtain ⟨c1, c2, -⟩ := scF h0
    obtain ⟨hP, hz⟩ := hXX.1.sc _ c1
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hv := sc_word_val hP hz (o := layout.sc.SPORADIC) (by simp [layout.sc.SPORADIC])
    have hsv : layout.sc.SPORADIC.val = 64 := by simp [layout.sc.SPORADIC]
    exact rS _ c1 c2 _ (by unfold Aligned; unfold sporA; rw [hv, hsv]; omega)
      ⟨by unfold sporA; rw [hv]; omega, by unfold sporA; rw [hv, hsv]; omega⟩
  · rw [esb h0]
    obtain ⟨c1, c2, -⟩ := scF h0
    have hcq := scq_of hXX.1 hSS c1
    refine ⟨fun b ha hb => rS _ c1 c2 b ha hb, fun b ha hb => wS _ c1 c2 b ha hb.inSC (by
      have := hb.1; omega), ?_⟩
    obtain ⟨⟨q1, q2⟩, q3⟩ := hcq.2.2.1
    have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
    obtain ⟨hP, hz⟩ := hXX.1.sc _ c1
    have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
    exact wS _ c1 c2 _ q3 ⟨q1, q2⟩ (by rw [hv, hcv]; omega)
  · rw [esb h0]
    obtain ⟨c1, -, c3⟩ := scF h0
    have hcq := scq_of hXX.1 hSS c1
    exact hcq.1 ((hSS.act _ c1).1 c3)
  · exact ⟨nodeAt_aligned hN (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]),
      outN _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])⟩
  · show R (L.nodeAt X (L.cpu X) layout.node.CUR_TIME)
    rw [eN]; exact (nRW _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).1
  · show W (L.nodeAt X (L.cpu X) layout.node.REPROGRAM)
    rw [eN]; exact (nRW _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])).2
  · rw [eN]; exact (nRW _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])).1
  · rw [kX]; exact rCD

/-- `wkpre_fire` with no read / write premises (`R = W = True`), for the `st` runs. -/
theorem wkpre_true {s X : S} {w N : U64}
    (hTX : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac X)
    (hAffSc : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t))
    (kX : L.ksb X = L.ksb s) (cX : L.cpu X = L.cpu s)
    (kT : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (K.val < 3528 ∨ 3576 ≤ K.val) →
      L.mem X (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K))
    (hwT : w ∈ T) (hbl : Blocked (L.mem X (stA w))) (haf : L.mem X (affA w) = L.cpu s)
    (hdom : L.mem X (domA w) = L.mem X (core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN))
    (hnd : L.mem X (scA w) = 0#u64 → L.mem X (ntfnScA N) = 0#u64) :
    WkPre st (fun _ => True) (fun _ => True) X w N (scSb Z (L.mem X (scA w))) ∧
      (L.mem X (scA w) ≠ 0#u64 → ∀ b, Aligned b → InSC (L.mem X (scA w)) (scSb Z (L.mem X (scA w))) b → b ∈ Ω) ∧
      Outside (L.nodeA X layout.node.SCHED_ACTION) (L.mem X (scA w)) (scSb Z (L.mem X (scA w))) :=
  wkpre_fire hTX hAffSc kX cX kT hwT hbl haf hdom hnd trivial (fun _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ => trivial) (fun _ _ _ => ⟨trivial, trivial⟩) trivial

end

end Fl4Proofs.P2
