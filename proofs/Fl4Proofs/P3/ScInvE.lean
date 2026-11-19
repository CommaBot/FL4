/-
P3 (DESIGN.md §9), scheduling contexts: **the invariant across endpoint
steps** (`EpStep`, the IPC code's spec steps): `Inv.stepE`, and
`Inv.blockE`, blocking a thread on an endpoint (send or receive) when its SC
is released (`RelIfBound`), for the handler compositions.
-/
import Fl4Proofs.P3.ScInv
import Fl4Proofs.P3.IpcSchedInst
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Classical

noncomputable section

section Spec
open Fl4Spec

theorem EpStep.tcb_back {σ σ' : State Unit} (h : EpStep σ σ') {p : ObjRef} {y : Tcb}
    (hk : σ'.kheap p = some (.tcb y)) : ∃ x, σ.kheap p = some (.tcb x) ∧ y.tcbSchedContext = x.tcbSchedContext := by
  rcases h.2.2 p with e | ⟨a, b, -, hb⟩ | ⟨a, b, -, hb, -⟩ | ⟨a, b, ha, hb, e⟩
  · exact ⟨y, e ▸ hk, rfl⟩
  · rw [hk] at hb; cases hb
  · rw [hk] at hb; cases hb
  · rw [hk] at hb; cases hb; exact ⟨a, ha, by rw [e]⟩

theorem EpStep.sc_back {σ σ' : State Unit} (h : EpStep σ σ') {p : ObjRef} {y : SchedContext} {n : Nat}
    (hk : σ'.kheap p = some (.schedContext y n)) : σ.kheap p = some (.schedContext y n) := by
  rcases h.2.2 p with e | ⟨a, b, -, hb⟩ | ⟨a, b, -, hb, -⟩ | ⟨a, b, -, hb, -⟩
  · rw [← e]; exact hk
  all_goals (rw [hk] at hb; cases hb)

theorem EpStep.ntfn_back {σ σ' : State Unit} (h : EpStep σ σ') {p : ObjRef} {y : Notification}
    (hk : σ'.kheap p = some (.notification y)) : σ.kheap p = some (.notification y) := by
  rcases h.2.2 p with e | ⟨a, b, -, hb⟩ | ⟨a, b, -, hb, -⟩ | ⟨a, b, -, hb, -⟩
  · rw [← e]; exact hk
  all_goals (rw [hk] at hb; cases hb)

theorem EpStep.fault {σ σ' : State Unit} (h : EpStep σ σ') {p : ObjRef} {x y : Tcb}
    (hx : σ.kheap p = some (.tcb x)) (hy : σ'.kheap p = some (.tcb y)) : y.tcbFault = x.tcbFault := by
  rcases h.2.2 p with e | ⟨a, b, -, hb⟩ | ⟨a, b, -, hb, -⟩ | ⟨a, b, ha, hb, e⟩
  · rw [e, hx] at hy; cases hy; rfl
  · rw [hy] at hb; cases hb
  · rw [hy] at hb; cases hb
  · rw [hx] at ha; cases ha; rw [hy] at hb; cases hb; rw [e]

theorem EpStep.relIfBound {σ σ' : State Unit} (h : EpStep σ σ') {u : ObjRef} (hr : RelIfBound σ u) :
    RelIfBound σ' u := by
  obtain ⟨-, e2, -, -, -, e6, -⟩ := Ipc.EpStep.abs h
  intro x scp y n h1 h2 h3 h4 h5
  obtain ⟨x0, h1', hs⟩ := EpStep.tcb_back h h1
  rw [released_congr e6]
  exact hr x0 scp y n h1' (hs ▸ h2) (EpStep.sc_back h h3) h4 (by rw [← e2]; exact h5)

/-- **An endpoint step keeps the invariant**, given what it does to the
states: `hst` for the queued threads, `hrd` for the threads of `inClass`
(as `Inv.step` for notification steps). -/
theorem Inv.stepE {σ σ' : State Unit} (h : Inv σ) (hn : EpStep σ σ')
    (hst : ∀ u x y, σ.kheap u = some (.tcb x) → σ'.kheap u = some (.tcb y) →
      ((∃ d p, u ∈ σ.readyQueues d p) ∨ u ∈ σ.releaseQueue) → runnable x.tcbState = true →
      runnable y.tcbState = true)
    (hrd : ∀ u x y, σ.kheap u = some (.tcb x) → σ'.kheap u = some (.tcb y) → inClassR y.tcbState y.tcbFault →
      RelIfBound σ u) : Inv σ' := by
  obtain ⟨e1, e2, -, -, -, e6, -⟩ := Ipc.EpStep.abs hn
  refine ⟨fun d p u hu => ?_, fun u hu => ?_, ?_, fun u y hy hc => ?_, fun p y n hy => ?_,
    fun u y p hy hp => ?_, fun q y p hy hp => ?_, fun p y n hy => h.ne p y n (EpStep.sc_back hn hy),
    fun p y n hy => h.rr p y n (EpStep.sc_back hn hy)⟩
  · rw [e1] at hu
    obtain ⟨x, scp, yc, n, h1, h2, h3, h4, h5⟩ := h.rq d p u hu
    obtain ⟨y, hy, -, hs, -⟩ := Ipc.EpStep.tcbSched hn h1
    exact ⟨y, scp, yc, n, hy, hs.trans h2, hst u x y h1 hy (Or.inl ⟨d, p, hu⟩) h3, Ipc.EpStep.sc hn h4, h5⟩
  · rw [e2] at hu
    obtain ⟨x, scp, yc, n, h1, h2, h3, h4, h5⟩ := h.rel u hu
    obtain ⟨y, hy, -, hs, -⟩ := Ipc.EpStep.tcbSched hn h1
    exact ⟨y, scp, yc, n, hy, hs.trans h2, hst u x y h1 hy (Or.inr hu) h3, Ipc.EpStep.sc hn h4, h5⟩
  · rw [e2]
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) h.sorted
    obtain ⟨xa, pa, ya, na, h1, h2, -, h4, h5⟩ := h.rel a ha
    obtain ⟨xb, pb, yb, nb, g1, g2, -, g4, g5⟩ := h.rel b hb
    have nea := h.ne _ _ _ h4 h5
    have neb := h.ne _ _ _ g4 g5
    obtain ⟨ya', hya, -, hsa, -⟩ := Ipc.EpStep.tcbSched hn h1
    obtain ⟨yb', hyb, -, hsb, -⟩ := Ipc.EpStep.tcbSched hn g1
    rw [specRt_eq hya (hsa.trans h2) (Ipc.EpStep.sc hn h4) nea,
      specRt_eq hyb (hsb.trans g2) (Ipc.EpStep.sc hn g4) neb]
    rw [specRt_eq h1 h2 h4 nea, specRt_eq g1 g2 g4 neb] at hab
    exact hab
  · obtain ⟨x, hx, -⟩ := EpStep.tcb_back hn hy
    exact EpStep.relIfBound hn (hrd u x y hx hy hc)
  · exact h.refills p y n (EpStep.sc_back hn hy)
  · obtain ⟨x, hx, hs⟩ := EpStep.tcb_back hn hy
    obtain ⟨yc, n, h1, h2⟩ := h.back u x p hx (hs ▸ hp)
    exact ⟨yc, n, Ipc.EpStep.sc hn h1, h2⟩
  · obtain ⟨yc, n, h1⟩ := h.ntfnSc q y p (EpStep.ntfn_back hn hy) hp
    exact ⟨yc, n, Ipc.EpStep.sc hn h1⟩

/-- **Blocking a thread on an endpoint keeps the invariant**: an endpoint
step changing the state of no TCB but `t`, which is in no queue and whose
SC is released (`RelIfBound`). -/
theorem Inv.blockE {σ σ' : State Unit} {t : ObjRef} (h : Inv σ) (hn : EpStep σ σ') (hq : NotQueued σ t)
    (hrt : RelIfBound σ t)
    (hoth : ∀ p x y, σ.kheap p = some (.tcb x) → σ'.kheap p = some (.tcb y) → p ≠ t → y.tcbState = x.tcbState) :
    Inv σ' := by
  refine h.stepE hn (fun u x y h1 h2 hm hr => ?_) (fun u x y h1 h2 hc => ?_)
  · have hut : u ≠ t := by
      rintro rfl
      rcases hm with ⟨d, p, hm⟩ | hm
      · exact hq.1 d p hm
      · exact hq.2 hm
    rw [hoth u x y h1 h2 hut]; exact hr
  · by_cases hut : u = t
    · subst hut; exact hrt
    · exact h.rd u x h1 (hc.congr (hoth u x y h1 h2 hut).symm fun _ => (EpStep.fault hn h1 h2).symm)

end Spec

end

end Fl4Proofs.P3.Sched
