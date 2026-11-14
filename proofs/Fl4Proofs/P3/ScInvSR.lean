/-
P3 (DESIGN.md §9), scheduling contexts: **the notification proofs' hypotheses
for `SRI`**, the scheduler relation with the invariant: `SchedRel`, `Inv`
(ScInv.lean) and `NSC` (a notification's SC is one of `C`).

With `SRI`, `DonatePre`'s facts, `RelOK` and `ActReady` follow from the
invariant; what remains is the platform's `MIN_BUDGET` (`hmb`) and the IPC
hypothesis `cancel_ipc` (passed through).

* `wakeTail_SRI`: `SchedHyps.wakeTail`;
* `schedHyps_SRI`: `SchedHyps` for `SRI`;
* `recvTail_SRI`, `completeTail_SRI`, `returnSc_SRI`: `RecvHyps` for `SRI`.
-/
import Fl4Proofs.P3.ScInvR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- A notification's SC is one of `C`. -/
def NSC (N C : Set U64) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ n ∈ N, ∀ x p, σ.kheap n.bv = some (.notification x) → x.ntfnSc = some p → ∃ sc ∈ C, sc.bv = p

/-- The scheduler relation with the invariant. -/
def SRI (st : machine.Store S) [L : LawfulStore st] (N T C : Set U64) (c : U64) (s : S) (σ : Fl4Spec.State Unit) :
    Prop :=
  SchedRel st N T C c s σ ∧ Inv σ ∧ NSC N C σ

theorem NSC.kview {N T C : Set U64} {m : U64 → U64} {σ σ' : Fl4Spec.State Unit} (h : NSC N C σ)
    (hR : NtfnStateRel N T m σ) (hv : KView σ σ') : NSC N C σ' := by
  intro n hn x p hx hp
  obtain ⟨x0, hk0, -⟩ := hR.ntfn n hn
  rw [hv.1 _ _ hk0] at hx; cases hx
  exact h n hn _ p hk0 hp

theorem NSC.step {N C : Set U64} {σ σ' : Fl4Spec.State Unit} (h : NSC N C σ) (hn : NtfnStep σ σ') : NSC N C σ' := by
  intro n hn' x p hx hp
  obtain ⟨x0, h0, hs⟩ := NtfnStep.ntfn_back hn hx
  exact h n hn' x0 p h0 (hs ▸ hp)

theorem Inv.relOK {σ : Fl4Spec.State Unit} (h : Inv σ) : RelOK σ :=
  ⟨fun u hu => by obtain ⟨x, p, -, -, h1, h2, -⟩ := h.rel u hu; exact ⟨x, p, h1, h2⟩, h.sorted⟩

theorem NSC.mem {N T C : Set U64} {s : S} {σ : Fl4Spec.State Unit} (h : NSC N C σ)
    (hR : NtfnStateRel N T (L.mem s) σ) {n : U64} (hn : n ∈ N) (h0 : L.mem s (nScA n) ≠ 0#u64) :
    L.mem s (nScA n) ∈ C := by
  obtain ⟨xn, hkn, hxn⟩ := hR.ntfn n hn
  obtain ⟨sc, hsc, e⟩ := h n hn xn _ hkn (by rw [hxn.sc, optRef_ne h0])
  rw [← eq_of_bv e]; exact hsc

/-- **`SchedHyps.wakeTail` for `SRI`.** -/
theorem wakeTail_SRI {N T C : Set U64} {c : U64}
    (hmb : ∀ a : A, sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (t n : U64) (x : Fl4Spec.Tcb) (hR : NtfnStateRel N T (L.mem s) σ)
    (hSRI : SRI st N T C c s σ) (ht : t ∈ T) (hn : n ∈ N) (hk : σ.kheap t.bv = some (.tcb x))
    (hx : x.tcbState = .running) (hNQ : NotQueued σ t.bv) :
    rustWakeTail st ar s a t n ⦃ r => ¬ (specWakeTail t.bv n.bv σ).2 ∧ ∃ σ', ((), σ') ∈ (specWakeTail t.bv n.bv σ).1 ∧
      FootEq N T (L.mem s) (L.mem r.1) ∧ KView σ σ' ∧ SRI st N T C c r.1 σ' ⦄ := by
  obtain ⟨hS, hI, hN⟩ := hSRI
  have hP := hS.placed
  obtain ⟨xn, hkn, -⟩ := hR.ntfn n hn
  unfold rustWakeTail
  refine WP.spec_bind (maybe_donate_refines s a σ hR hS hI.relOK (hmb a) t n ht hn (hN.mem hR hn)
    (fun _ y hy => by rw [hk] at hy; cases hy; exact hNQ.1 _ _)) ?_
  rintro ⟨s4, a2⟩ ⟨σ1, hd, hf1, hv1, hS1, -⟩
  have hS1 : SchedRel st N T C c s4 σ1 := hS1
  have hf1 : FootEq N T (L.mem s) (L.mem s4) := hf1
  have hR1 : NtfnStateRel N T (L.mem s4) σ1 := hR.frame hP hf1 hv1
  obtain ⟨hI1, hrq1⟩ := Inv.donate hI hk hkn (by rw [hx]; rfl) hNQ hd
  have hN1 := hN.kview hR hv1
  step with sched.is_schedulable.spec' as ⟨b1, b1_post⟩
  rw [schedulable_eq hR1 hS1 ht] at b1_post
  have hmid : (if b1 = true then sched.possible_switch_to st s4 t else ok s4) ⦃ s5 => ∃ σ2,
      (Fl4Spec.NonDet.when (Fl4Spec.schedulable t.bv σ1 = true) (Fl4Spec.possibleSwitchTo t.bv)) σ1 =
        ({((), σ2)}, False) ∧ FootEq N T (L.mem s4) (L.mem s5) ∧ σ2.kheap = σ1.kheap ∧
        SchedRel st N T C c s5 σ2 ∧ Inv σ2 ∧ σ2.releaseQueue = σ1.releaseQueue ∧ σ2.curTime = σ1.curTime ⦄ := by
    rw [b1_post]
    by_cases e : Fl4Spec.schedulable t.bv σ1 = true
    · simp only [e, ↓reduceIte, Fl4Spec.NonDet.when]
      refine WP.spec_mono (possible_switch_to_refines s4 σ1 hR1 hS1 hI1.actReady t ht) ?_
      rintro s5 ⟨σ2, hp, hk2, hf, hS2⟩
      have hq := possibleSwitchTo_qchange hI1 e hp
      exact ⟨σ2, hp, hf, hk2, hS2, hI1.qchange hq, hq.2.1, hq.2.2.1⟩
    · simp only [e, Bool.false_eq_true, ↓reduceIte, Fl4Spec.NonDet.when, WP.spec_ok]
      exact ⟨σ1, rfl, FootEq.rfl', rfl, hS1, hI1, rfl, rfl⟩
  refine WP.spec_bind hmid ?_
  rintro s5 ⟨σ2, hw2, hf2, hk2, hS2, hI2, hr2, ht2⟩
  have hR2 : NtfnStateRel N T (L.mem s5) σ2 := hR1.frame hP hf2 (KView.of_kheap hk2)
  have hN2 : NSC N C σ2 := hN1.kview hR1 (KView.of_kheap hk2)
  refine WP.spec_bind (unblock_sporadic_refines s5 σ2 hS2 t ht) ?_
  rintro s6 ⟨hnf, σ', hm, hf3, hv3, hS3⟩
  simp only [WP.spec_ok]
  have hspec : specWakeTail t.bv n.bv σ = specUnblock t.bv σ2 := by
    unfold specWakeTail
    rw [nd_bind_one hd, nd_gets_bind, nd_bind_one hw2]
    rfl
  obtain ⟨Q2, R2, hc2, hs2⟩ := hS2.lists
  obtain ⟨x2, hkt2, -⟩ := hs2.tcb t ht
  have hI3 := hI2.unblockTail hkt2 (fun p y m h1 h2 h3 => by
    rw [hk2] at hkt2 h2; rw [hr2] at h3; rw [ht2]
    exact hrq1 x2 p y m hkt2 h1 h2 h3) hm
  rw [hspec]
  exact ⟨hnf, σ', hm, FootEq.trans' (FootEq.trans' hf1 hf2) hf3,
    KView.trans (KView.trans hv1 (KView.of_kheap hk2)) hv3, hS3, hI3, hN2.kview hR2 hv3⟩

/-- **`SchedHyps` for `SRI`**, from the platform's `MIN_BUDGET` and the IPC
hypothesis `cancel_ipc`. -/
theorem schedHyps_SRI {N T C : Set U64} {c : U64}
    (hmb : ∀ a : A, sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hC : ∀ s (a : A) σ (t : U64) (x : Fl4Spec.Tcb), NtfnStateRel N T (L.mem s) σ → SRI st N T C c s σ →
      t ∈ T → σ.kheap t.bv = some (.tcb x) → Fl4Spec.receiveBlocked x.tcbState = true →
      ipc.cancel_ipc st ar s a t ⦃ r => ∃ σ' x', Fl4Spec.cancelIpc (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
        NtfnStateRel N T (L.mem r.1) σ' ∧ SRI st N T C c r.1 σ' ∧ σ'.kheap t.bv = some (.tcb x') ∧
        x'.tcbState = .inactive ∧ RelIfBound σ' t.bv ⦄) :
    SchedHyps st ar N T (SRI st N T C c) where
  stable := fun _ _ _ _ ⟨hS, hI, hN⟩ hw hn hb => ⟨hS.stable hw hn, hI.stable hn hb, hN.step hn⟩
  notQueued := fun _ _ _ _ ⟨_, hI, _⟩ hk hr => hI.notQueued hk hr
  block := fun _ _ _ _ _ ⟨hS, hI, hN⟩ hq hrt hw hn hoth => ⟨hS.stable hw hn, hI.block hn hq hrt hoth, hN.step hn⟩
  scheduleTcb := fun s σ t hR ⟨hS, hI, hN⟩ ht => WP.spec_mono (schedule_tcb_refines s σ hR hS t ht)
    (fun _ ⟨hf, hS'⟩ => ⟨hf, hS', hI.qchange (qchange_stsAct σ t.bv), hN.kview hR (KView.stsAct σ t.bv)⟩)
  wakeTail := fun s a σ t n x hR hS ht hn hk hx hq => wakeTail_SRI hmb s a σ t n x hR hS ht hn hk hx hq
  cancelIpc := hC

/-- **`RecvHyps.recvTail` for `SRI`.** -/
theorem recvTail_SRI {N T C : Set U64} {c : U64}
    (hmb : ∀ a : A, sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (t n : U64) (hR : NtfnStateRel N T (L.mem s) σ)
    (hSRI : SRI st N T C c s σ) (ht : t ∈ T) (hn : n ∈ N) (hNQ : NotQueued σ t.bv)
    (hRun : ∀ x, σ.kheap t.bv = some (.tcb x) → Fl4Spec.runnable x.tcbState = true) :
    TailRef st N T (SRI st N T C c) Prod.fst s σ (rustRecvTail st ar s a t n) (specRecvTail t.bv n.bv) := by
  obtain ⟨hS, hI, hN⟩ := hSRI
  obtain ⟨xn, hkn, -⟩ := hR.ntfn n hn
  obtain ⟨xt, hkt, -⟩ := hR.tcb t ht
  unfold TailRef rustRecvTail
  refine WP.spec_bind (maybe_donate_refines s a σ hR hS hI.relOK (hmb a) t n ht hn (hN.mem hR hn)
    (fun _ y hy => by rw [hkt] at hy; cases hy; exact hNQ.1 _ _)) ?_
  rintro ⟨s3, a1⟩ ⟨σ1, hd, hf1, hv1, hS1, -⟩
  obtain ⟨hI1, hrq1⟩ := Inv.donate hI hkt hkn (hRun xt hkt) hNQ hd
  have hR1 : NtfnStateRel N T (L.mem s3) σ1 := hR.frame hS.placed hf1 hv1
  have hN1 := hN.kview hR hv1
  refine WP.spec_mono (recv_check_refines (st := st) (A := A) s3 a1 σ1 hS1 t ht) ?_
  rintro r ⟨hnf, σ', hm, hf, hv, hS'⟩
  have hspec : specRecvTail t.bv n.bv σ = specUnblock t.bv σ1 := by
    unfold specRecvTail; rw [nd_bind_one hd]; rfl
  obtain ⟨xt1, hkt1, -⟩ := hR1.tcb t ht
  rw [hspec]
  exact ⟨hnf, σ', hm, FootEq.trans' hf1 hf, KView.trans hv1 hv,
    hS', hI1.unblockTail hkt1 (fun p y m h1 h2 h3 => hrq1 xt1 p y m hkt1 h1 h2 h3) hm, hN1.kview hR1 hv⟩

/-- **`RecvHyps.completeTail` for `SRI`.** -/
theorem completeTail_SRI {N T C : Set U64} {c : U64}
    (hmb : ∀ a : A, sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (t n : U64) (hR : NtfnStateRel N T (L.mem s) σ)
    (hSRI : SRI st N T C c s σ) (ht : t ∈ T) (hn : n ∈ N) (hNQ : NotQueued σ t.bv)
    (hRun : ∀ x, σ.kheap t.bv = some (.tcb x) → Fl4Spec.runnable x.tcbState = true) :
    TailRef st N T (SRI st N T C c) Prod.fst s σ (rustCompleteTail st ar s a t n)
      (specCompleteTail t.bv n.bv) := by
  obtain ⟨hS, hI, hN⟩ := hSRI
  obtain ⟨xn, hkn, -⟩ := hR.ntfn n hn
  obtain ⟨xt, hkt, -⟩ := hR.tcb t ht
  unfold TailRef rustCompleteTail
  refine WP.spec_bind (maybe_donate_refines s a σ hR hS hI.relOK (hmb a) t n ht hn (hN.mem hR hn)
    (fun _ y hy => by rw [hkt] at hy; cases hy; exact hNQ.1 _ _)) ?_
  rintro ⟨s3, a1⟩ ⟨σ1, hd, hf1, hv1, hS1, -⟩
  obtain ⟨hI1, hrq1⟩ := Inv.donate hI hkt hkn (hRun xt hkt) hNQ hd
  have hR1 : NtfnStateRel N T (L.mem s3) σ1 := hR.frame hS.placed hf1 hv1
  have hN1 := hN.kview hR hv1
  refine WP.spec_mono (complete_check_refines (st := st) (A := A) s3 a1 σ1 hR1 hS1 t n ht hn) ?_
  rintro r ⟨hnf, σ', hm, hf, hv, hS'⟩
  have hspec : specCompleteTail t.bv n.bv σ = specCompleteCheck t.bv n.bv σ1 := by
    unfold specCompleteTail; rw [nd_bind_one hd]; rfl
  obtain ⟨xt1, hkt1, -⟩ := hR1.tcb t ht
  obtain ⟨xn1, hkn1, -⟩ := hR1.ntfn n hn
  rw [hspec]
  exact ⟨hnf, σ', hm, FootEq.trans' hf1 hf, KView.trans hv1 hv,
    hS', hI1.completeCheck hkt1 hkn1 (fun p y m h1 h2 h3 => hrq1 xt1 p y m hkt1 h1 h2 h3) hm, hN1.kview hR1 hv⟩

/-- **`RecvHyps.returnSc` for `SRI`.** -/
theorem returnSc_SRI {N T C : Set U64} {c : U64} (s : S) (σ0 σ : Fl4Spec.State Unit) (t n : U64)
    (hR : NtfnStateRel N T (L.mem s) σ) (hSRI : SRI st N T C c s σ) (ht : t ∈ T) (hn : n ∈ N)
    (_hA : ActReady σ0) (hb : BlockStep σ0 σ t.bv n.bv) :
    TailRef st N T (SRI st N T C c) id s σ (notification.maybe_return_sched_context st s n t)
      (Fl4Spec.maybeReturnSc n.bv t.bv) := by
  obtain ⟨hS, hI, hN⟩ := hSRI
  obtain ⟨xn, hkn, -⟩ := hR.ntfn n hn
  obtain ⟨-, -, -, -, -, ⟨x0, y, -, hky, -, hry⟩⟩ := hb
  refine WP.spec_mono (maybe_return_refines s σ hR hS hI.actReady t n ht hn) ?_
  rintro s' ⟨hnf, σ', hm, hf, hv, hS'⟩
  exact ⟨hnf, σ', hm, hf, hv, hS', hI.ret hky hkn hry hm, hN.kview hR hv⟩

/-- **`RecvHyps` for `SRI`.** -/
theorem recvHyps_SRI {N T C : Set U64} {c : U64}
    (hmb : ∀ a : A, sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) :
    RecvHyps st ar N T (SRI st N T C c) :=
  ⟨fun s a σ t n hR hS ht hn hq hr => recvTail_SRI hmb s a σ t n hR hS ht hn hq hr,
   fun s a σ t n hR hS ht hn hq hr => completeTail_SRI hmb s a σ t n hR hS ht hn hq hr,
   fun s σ0 σ t n hR hS ht hn hA hb => returnSc_SRI s σ0 σ t n hR hS ht hn hA hb⟩

end

end

end Fl4Proofs.P3.Sched
