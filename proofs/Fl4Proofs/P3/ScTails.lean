/-
P3 (DESIGN.md §9), scheduling contexts: the receive tails and the
wake-up hypotheses, from the donation hypothesis.

`DonateHyp`: `maybe_donate_sched_context` refines `maybe_donate_sc` (single
spec outcome, footprint, `KView`, `SchedRel`). Its no-donation cases are
`maybe_donate_nodonate` (ScDonate.lean); the donation case (seL4
`schedContext_donate` and `schedContext_resume`, with the postponing into
the release queue) is left open.

* `recvTail_of`: `RecvHyps.recvTail` from `DonateHyp` (the sporadic check
  after the donation: `recv_check_refines`);
* `completeTail_of`: `RecvHyps.completeTail` from `DonateHyp`;
* `wakeHyps_of`: `WakeHyps` from the donation hypothesis of a wake-up
  (with `ActReady` after it) and `unblock_sporadic_refines`.
-/
import Fl4Proofs.P3.ScDonate
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- The donation hypothesis. -/
def DonateHyp (st : machine.Store S) (ar : machine.Arch A) [L : LawfulStore st] (N T C : Set U64) (c : U64) :
    Prop :=
  ∀ s (a : A) σ (t n : U64), NtfnStateRel N T (L.mem s) σ → SchedRel st N T C c s σ → t ∈ T → n ∈ N →
    notification.maybe_donate_sched_context st ar s a t n ⦃ r => ∃ σ1,
      Fl4Spec.maybeDonateSc (Z := Unit) t.bv n.bv σ = ({((), σ1)}, False) ∧ FootEq N T (L.mem s) (L.mem r.1) ∧
      KView σ σ1 ∧ SchedRel st N T C c r.1 σ1 ⦄

theorem ifSporadic_none (σ : Fl4Spec.State Unit) :
    Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit) none σ = ({((), σ)}, False) := rfl

theorem ifSporadic_some {σ : Fl4Spec.State Unit} {p : Fl4Spec.ObjRef} {x : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext x n)) :
    Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit) (some p) σ =
      (if x.scSporadic = true ∧ ¬ p = σ.curSc then Fl4Spec.refillUnblockCheck p σ else ({((), σ)}, False)) := by
  unfold Fl4Spec.ifSporadicCurScTestRefillUnblockCheck Fl4Spec.ifCondRefillUnblockCheck
  simp only [Fl4Spec.NonDet.maybeM]
  rw [nd_bind_one (getSchedContext_eq hk), nd_gets_bind, nd_pure_bind']
  simp only [Fl4Spec.NonDet.when]
  by_cases e : x.scSporadic = true ∧ ¬ p = σ.curSc
  · simp only [e, ne_eq, not_false_eq_true, forall_const, and_self, ↓reduceIte, Option.some.injEq,
      Bool.false_eq_true, IsEmpty.forall_iff]
  · simp only [ne_eq, forall_const, ↓reduceIte, Option.some.injEq]
    rw [ite_f (c := x.scSporadic = true ∧ ¬ p = σ.curSc) e, ite_f (c := x.scSporadic = true ∧ ¬ p = σ.curSc) e]
    rfl

/-- The check after a donation in `receive_signal` (active case). -/
theorem recv_check_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (t : U64) (ht : t ∈ T) :
    (do
      let i ← obj.Tcb.sc st t s
      let s4 ← sched.cur_sc st s
      let b1 ← core.cmp.PartialEq.ne.trait_default obj.Sc.Insts.CoreCmpPartialEqSc i s4
      if b1
      then
        let b2 ← sporadic.sc_sporadic st s i
        if b2
        then
          let s5 ← sporadic.unblock_check st s i
          ok (s5, a)
        else ok (s, a)
      else ok (s, a)) ⦃ r => ¬ (specUnblock t.bv σ).2 ∧ ∃ σ', ((), σ') ∈ (specUnblock t.bv σ).1 ∧
        FootEq N T (L.mem s) (L.mem r.1) ∧ KView σ σ' ∧ SchedRel st N T C c r.1 σ' ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨xt, hkt, -, -, hsct, -⟩ := hs.tcb t ht
  have hspec0 : specUnblock t.bv σ = (Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit)
      (optRef (L.mem s (scA t)))) σ := by
    unfold specUnblock Fl4Spec.getTcbObjRef
    rw [nd_bind_one (threadGet_eq _ hkt), hsct]
  have fin : ∀ s' σ', Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit) (optRef (L.mem s (scA t))) σ =
      ({((), σ')}, False) → FootEq N T (L.mem s) (L.mem s') → KView σ σ' → SchedRel st N T C c s' σ' →
      ¬ (specUnblock t.bv σ).2 ∧ ∃ σ', ((), σ') ∈ (specUnblock t.bv σ).1 ∧ FootEq N T (L.mem s) (L.mem s') ∧
        KView σ σ' ∧ SchedRel st N T C c s' σ' := by
    intro s' σ' he hf hv hS'
    rw [hspec0, he]
    exact ⟨id, σ', rfl, hf, hv, hS'⟩
  -- the cases where nothing happens
  have none_case : ∀ (h : L.mem s (scA t) = 0#u64 ∨
      (L.mem s (scA t) ∈ C ∧ ∀ x n, σ.kheap (L.mem s (scA t)).bv = some (.schedContext x n) →
        ¬ (x.scSporadic = true ∧ ¬ (L.mem s (scA t)).bv = σ.curSc))),
      ¬ (specUnblock t.bv σ).2 ∧ ∃ σ', ((), σ') ∈ (specUnblock t.bv σ).1 ∧ FootEq N T (L.mem s) (L.mem s) ∧
        KView σ σ' ∧ SchedRel st N T C c s σ' := by
    intro h
    refine fin s σ ?_ FootEq.rfl' (KView.refl σ) hS
    rcases h with h0 | ⟨hC, hn⟩
    · rw [h0, optRef_zero]; rfl
    · by_cases h0 : L.mem s (scA t) = 0#u64
      · rw [h0, optRef_zero]; rfl
      · obtain ⟨x, n, hk, -⟩ := hs.scs _ hC
        rw [optRef_ne h0, ifSporadic_some hk, ite_f (hn x n hk)]
  step
  step
  rw [sc_ne_eq]
  simp only [bind_ok]
  rw [i_post, s4_post, hc.cur]
  by_cases e : L.mem s (scA t) = nodeW st s c layout.node.CUR_SC
  · simp only [e, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    by_cases h0 : L.mem s (scA t) = 0#u64
    · exact none_case (Or.inl h0)
    · exact none_case (Or.inr ⟨hs.scMem t ht h0, fun x n _ h => h.2 (by rw [hs.curSc, e])⟩)
  · simp only [e, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
    step
    by_cases h0 : L.mem s (scA t) = 0#u64
    · have hb : b2 = false := by rw [b2_post]; simp [h0]
      simp only [hb, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      exact none_case (Or.inl h0)
    · have hscC := hs.scMem t ht h0
      obtain ⟨x, n, hk, hx⟩ := hs.scs _ hscC
      by_cases hsp : L.mem s (scW (L.mem s (scA t)) 64#u64) ≠ 0#u64
      · have hb : b2 = true := by rw [b2_post]; simp [h0, hsp]
        simp only [hb, ↓reduceIte]
        refine WP.spec_bind (unblock_check_refines s σ hS hscC) ?_
        rintro s' ⟨σ', he, hf, hv, hS'⟩
        simp only [WP.spec_ok]
        refine fin s' σ' ?_ hf hv hS'
        rw [optRef_ne h0, ifSporadic_some hk, ite_t ⟨by rw [hx.sporadic]; simpa using hsp,
          by rw [hs.curSc]; exact bv_ne e⟩, he]
      · have hb : b2 = false := by rw [b2_post]; simp [h0]; simpa using hsp
        simp only [hb, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact none_case (Or.inr ⟨hscC, fun x' n' hk' h => by
          rw [hk] at hk'; cases hk'; rw [hx.sporadic] at h; exact hsp (by simpa using h.1)⟩)

/-- **`RecvHyps.recvTail`** from the donation hypothesis. -/
theorem recvTail_of {N T C : Set U64} {c : U64} (hD : DonateHyp st ar N T C c) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (t n : U64) (hR : NtfnStateRel N T (L.mem s) σ) (hS : SchedRel st N T C c s σ)
    (ht : t ∈ T) (hn : n ∈ N) :
    TailRef st N T (SchedRel st N T C c) Prod.fst s σ (rustRecvTail st ar s a t n) (specRecvTail t.bv n.bv) := by
  unfold TailRef rustRecvTail
  refine WP.spec_bind (hD s a σ t n hR hS ht hn) ?_
  rintro ⟨s3, a1⟩ ⟨σ1, hd, hf1, hv1, hS1⟩
  refine WP.spec_mono (recv_check_refines (st := st) (A := A) s3 a1 σ1 hS1 t ht) ?_
  rintro r ⟨hnf, σ', hm, hf, hv, hS'⟩
  have hspec : specRecvTail t.bv n.bv σ = specUnblock t.bv σ1 := by
    unfold specRecvTail; rw [nd_bind_one hd]; rfl
  rw [hspec]
  exact ⟨hnf, σ', hm, FootEq.trans' hf1 hf, KView.trans hv1 hv, hS'⟩

/-- **`WakeHyps`** from the donation hypothesis of a wake-up (which also
gives `ActReady` after the donation) and `unblock_sporadic_refines`. -/
theorem wakeHyps_of {N T C : Set U64} {c : U64}
    (hD : ∀ s (a : A) σ (t n : U64) (x : Fl4Spec.Tcb), NtfnStateRel N T (L.mem s) σ → SchedRel st N T C c s σ →
      t ∈ T → n ∈ N → σ.kheap t.bv = some (.tcb x) → x.tcbState = .running →
      notification.maybe_donate_sched_context st ar s a t n ⦃ r => ∃ σ1,
        Fl4Spec.maybeDonateSc (Z := Unit) t.bv n.bv σ = ({((), σ1)}, False) ∧ FootEq N T (L.mem s) (L.mem r.1) ∧
        KView σ σ1 ∧ SchedRel st N T C c r.1 σ1 ∧ ActReady σ1 ⦄) :
    WakeHyps st ar N T C c :=
  ⟨hD, fun s σ t _ hS ht => unblock_sporadic_refines s σ hS t ht⟩

/-- The spec's check after the donation in `complete_signal`. -/
def specCompleteCheck (tptr ntfnptr : Fl4Spec.ObjRef) : Fl4Spec.SMonad Unit Unit := do
  let scOpt ← Fl4Spec.getTcbObjRef Fl4Spec.Tcb.tcbSchedContext tptr
  Fl4Spec.NonDet.maybeM (fun scp => do
      let sc ← Fl4Spec.getSchedContext scp
      Fl4Spec.NonDet.when sc.scSporadic <| do
        let ntfnScp ← Fl4Spec.getNtfnObjRef Fl4Spec.Notification.ntfnSc ntfnptr
        let curScPtr ← Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curSc
        Fl4Spec.NonDet.when (scOpt = ntfnScp ∧ scp ≠ curScPtr) <| Fl4Spec.refillUnblockCheck scp)
    scOpt

/-- The check after a donation in `complete_signal`. -/
theorem complete_check_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hR : NtfnStateRel N T (L.mem s) σ) (hS : SchedRel st N T C c s σ) (t n : U64) (ht : t ∈ T) (hn : n ∈ N) :
    (do
      let i1 ← obj.Tcb.sc st t s
      let b2 ← sporadic.sc_sporadic st s i1
      if b2
      then
        let i2 ← obj.Ntfn.sc st n s
        if i1 = i2
        then
          let s4 ← sched.cur_sc st s
          let b3 ← core.cmp.PartialEq.ne.trait_default obj.Sc.Insts.CoreCmpPartialEqSc i1 s4
          if b3
          then
            let s5 ← sporadic.unblock_check st s i1
            ok (s5, a)
          else ok (s, a)
        else ok (s, a)
      else ok (s, a)) ⦃ r => ¬ (specCompleteCheck t.bv n.bv σ).2 ∧ ∃ σ', ((), σ') ∈ (specCompleteCheck t.bv n.bv σ).1 ∧
        FootEq N T (L.mem s) (L.mem r.1) ∧ KView σ σ' ∧ SchedRel st N T C c r.1 σ' ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨xt, hkt, -, -, hsct, -⟩ := hs.tcb t ht
  obtain ⟨xn, hkn, hxn⟩ := hR.ntfn n hn
  set w := L.mem s (scA t)
  have fin : ∀ s' σ', specCompleteCheck t.bv n.bv σ = ({((), σ')}, False) → FootEq N T (L.mem s) (L.mem s') →
      KView σ σ' → SchedRel st N T C c s' σ' →
      ¬ (specCompleteCheck t.bv n.bv σ).2 ∧ ∃ σ', ((), σ') ∈ (specCompleteCheck t.bv n.bv σ).1 ∧
        FootEq N T (L.mem s) (L.mem s') ∧ KView σ σ' ∧ SchedRel st N T C c s' σ' := by
    intro s' σ' he hf hv hS'
    rw [he]; exact ⟨id, σ', rfl, hf, hv, hS'⟩
  have hspec0 : specCompleteCheck t.bv n.bv σ = Fl4Spec.NonDet.maybeM (fun scp => do
      let sc ← Fl4Spec.getSchedContext scp
      Fl4Spec.NonDet.when sc.scSporadic <| do
        let ntfnScp ← Fl4Spec.getNtfnObjRef Fl4Spec.Notification.ntfnSc n.bv
        let curScPtr ← Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curSc
        Fl4Spec.NonDet.when (optRef w = ntfnScp ∧ scp ≠ curScPtr) <| Fl4Spec.refillUnblockCheck scp)
      (optRef w) σ := by
    unfold specCompleteCheck Fl4Spec.getTcbObjRef
    rw [nd_bind_one (threadGet_eq _ hkt), hsct]
  step
  rw [i1_post]
  step
  by_cases h0 : w = 0#u64
  · have hb : b2 = false := by rw [b2_post]; simp [w, h0]
    simp only [hb, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    refine fin s σ ?_ FootEq.rfl' (KView.refl σ) hS
    rw [hspec0, h0, optRef_zero]; rfl
  have hscC := hs.scMem t ht h0
  obtain ⟨x, nn, hk, hx⟩ := hs.scs _ hscC
  have hsp0 : specCompleteCheck t.bv n.bv σ = (Fl4Spec.NonDet.when (x.scSporadic = true)
      (Fl4Spec.NonDet.when (some w.bv = optRef (L.mem s (nScA n)) ∧ w.bv ≠ σ.curSc)
        (Fl4Spec.refillUnblockCheck w.bv))) σ := by
    rw [hspec0, optRef_ne h0]
    simp only [Fl4Spec.NonDet.maybeM]
    rw [nd_bind_one (getSchedContext_eq hk)]
    by_cases h1 : x.scSporadic = true
    · simp only [Fl4Spec.NonDet.when, h1, ↓reduceIte]
      rw [nd_bind_one (getNtfnSc_eq hkn), nd_gets_bind, hxn.sc]
    · simp only [Fl4Spec.NonDet.when, h1, ↓reduceIte, Bool.false_eq_true]
  by_cases hsp : L.mem s (scW w 64#u64) ≠ 0#u64
  · have hb : b2 = true := by rw [b2_post]; simp [w, h0, hsp]
    have hxs : x.scSporadic = true := by rw [hx.sporadic]; simpa using hsp
    simp only [hb, ↓reduceIte]
    step
    rw [i2_post]
    by_cases e1 : w = L.mem s (nScA n)
    · have e1' : L.mem s (scA t) = L.mem s (nScA n) := e1
      simp only [e1', ↓reduceIte]
      step
      rw [sc_ne_eq]
      simp only [bind_ok]
      rw [s4_post, hc.cur]
      by_cases e2 : L.mem s (nScA n) = nodeW st s c layout.node.CUR_SC
      · simp only [e2, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        refine fin s σ ?_ FootEq.rfl' (KView.refl σ) hS
        rw [hsp0, Fl4Spec.NonDet.when, ite_t hxs, Fl4Spec.NonDet.when, ite_f (fun h => h.2 (by rw [hs.curSc, e1, e2]))]
        rfl
      · simp only [e2, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
        rw [← e1]
        refine WP.spec_bind (unblock_check_refines s σ hS hscC) ?_
        rintro s' ⟨σ', he, hf, hv, hS'⟩
        simp only [WP.spec_ok]
        refine fin s' σ' ?_ hf hv hS'
        rw [hsp0, Fl4Spec.NonDet.when, ite_t hxs, Fl4Spec.NonDet.when,
          ite_t ⟨by rw [e1, optRef_ne (by rw [← e1]; exact h0)], by rw [hs.curSc, e1]; exact bv_ne e2⟩, he]
    · have e1' : ¬ L.mem s (scA t) = L.mem s (nScA n) := e1
      simp only [e1', ↓reduceIte, WP.spec_ok]
      refine fin s σ ?_ FootEq.rfl' (KView.refl σ) hS
      rw [hsp0, Fl4Spec.NonDet.when, ite_t hxs, Fl4Spec.NonDet.when,
        ite_f (fun h => e1 (optRef_inj.1 ((optRef_ne h0).trans h.1)))]
      rfl
  · have hb : b2 = false := by rw [b2_post]; simp [w, h0]; simpa using hsp
    simp only [hb, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    refine fin s σ ?_ FootEq.rfl' (KView.refl σ) hS
    have hxs : ¬ x.scSporadic = true := by rw [hx.sporadic]; simpa using hsp
    rw [hsp0, Fl4Spec.NonDet.when, ite_f hxs]; rfl

/-- **`RecvHyps.completeTail`** from the donation hypothesis. -/
theorem completeTail_of {N T C : Set U64} {c : U64} (hD : DonateHyp st ar N T C c) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (t n : U64) (hR : NtfnStateRel N T (L.mem s) σ) (hS : SchedRel st N T C c s σ)
    (ht : t ∈ T) (hn : n ∈ N) :
    TailRef st N T (SchedRel st N T C c) Prod.fst s σ (rustCompleteTail st ar s a t n)
      (specCompleteTail t.bv n.bv) := by
  unfold TailRef rustCompleteTail
  refine WP.spec_bind (hD s a σ t n hR hS ht hn) ?_
  rintro ⟨s3, a1⟩ ⟨σ1, hd, hf1, hv1, hS1⟩
  have hR1 : NtfnStateRel N T (L.mem s3) σ1 := hR.frame hS.placed hf1 hv1
  refine WP.spec_mono (complete_check_refines (st := st) (A := A) s3 a1 σ1 hR1 hS1 t n ht hn) ?_
  rintro r ⟨hnf, σ', hm, hf, hv, hS'⟩
  have hspec : specCompleteTail t.bv n.bv σ = specCompleteCheck t.bv n.bv σ1 := by
    unfold specCompleteTail; rw [nd_bind_one hd]; rfl
  rw [hspec]
  exact ⟨hnf, σ', hm, FootEq.trans' hf1 hf, KView.trans hv1 hv, hS'⟩

end

end

end Fl4Proofs.P3.Sched
