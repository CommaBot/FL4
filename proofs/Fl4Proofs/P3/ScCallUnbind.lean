/-
P3 (DESIGN.md §9), scheduling contexts: **`unbind_reply`** against l4v
`sched_context_unbind_reply` (SchedContext `Unbind`'s reply step): the SC's
whole call stack becomes detached.
-/
import Fl4Proofs.P3.ScCallOps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- An SC's `REPLY` word: aligned, at offset 32, inside the object. -/
theorem sc_reply_word {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {sc : U64} (hsc : sc ∈ C) :
    Aligned (scReplyA sc) ∧ (scReplyA sc).val = sc.val + 32 ∧
      ∀ x n, σ.kheap sc.bv = some (.schedContext x n) → sc.val + 40 ≤ sc.val + 2 ^ n := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x, n, hk, hx⟩ := hs.scs sc hsc
  obtain ⟨h8, h2, hfit⟩ := hx.bounds
  obtain ⟨ha, hin⟩ := hx.hdr (K := 32#u64) (by simp) (by simp)
  have hv : (scW sc 32#u64).val = sc.val + 32 := by rw [scW_val (by simp; omega)]; rfl
  refine ⟨by rw [scReplyA_eq]; exact ha, by rw [scReplyA_eq]; exact hv, fun x' n' hk' => ?_⟩
  rw [hk] at hk'; cases hk'
  have hin' := hx.in_obj hin
  unfold ScObj at hin'; rw [hv] at hin'
  have h6 : 6 ≤ n := by
    by_contra h
    have : 2 ^ n ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have : 2 ^ 6 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h6
  omega


theorem reply_bit {r : U64} (h : r.val % 32 = 0) : r &&& 1#u64 = 0#u64 := by
  apply UScalar.eq_of_val_eq
  rw [UScalar.val_and, show (1#u64 : U64).val = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  show r.val % 2 = 0; omega

/-- Words of distinct replies, and the `PREV` and `NEXT` words, differ. -/
theorem rwords_ne {r r' : U64} (h : r.val % 32 = 0 ∧ r ≠ 0#u64 ∧ r.val + 32 ≤ 2 ^ 64)
    (h' : r'.val % 32 = 0 ∧ r' ≠ 0#u64 ∧ r'.val + 32 ≤ 2 ^ 64) :
    (rPrevA r).val ≠ (rNextA r').val ∧ (r ≠ r' → (rPrevA r).val ≠ (rPrevA r').val ∧ (rNextA r).val ≠ (rNextA r').val) := by
  rw [rPrevA_val h, rNextA_val h', rPrevA_val h', rNextA_val h]
  refine ⟨by omega, fun hne => ?_⟩
  have : r.val ≠ r'.val := fun e => hne (UScalar.eq_of_val_eq e)
  constructor <;> omega

/-- **`unbind_reply` refines `sched_context_unbind_reply`**: the stack is
detached. -/
theorem unbind_reply_refines {N T C R : Set U64} {c : U64} (s : S) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    {Lst : U64 → List U64} (hCR : CallRel (L.mem s) R C σ Lst) (hRP : RPlaced st N T C R c s σ)
    {p : U64} (hp : p ∈ C) (hp0 : p ≠ 0#u64) {y : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap p.bv = some (.schedContext y n)) (hRF : RFree (L.mem s) R C σ Lst) :
    schedcontext.unbind_reply st s p ⦃ s' => ∃ σ' Lst',
      Fl4Spec.schedContextUnbindReply (Z := Unit) p.bv σ = ({((), σ')}, False) ∧
      SchedRel st N T C c s' σ' ∧ NtfnStateRel N T (L.mem s') σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      CallRel (L.mem s') R C σ' Lst' ∧ RPlaced st N T C R c s' σ' ∧ (ActIdle σ → ActIdle σ') ∧
      RFree (L.mem s') R C σ' Lst' ⦄ := by
  have hP := hS.placed
  obtain ⟨⟨y', n', hk', hyL⟩, hLR, hLnd, hLw⟩ := hCR.stack p hp
  rw [hk] at hk'; cases hk'
  obtain ⟨haP, hvP, hszP⟩ := sc_reply_word hS hp
  unfold schedcontext.unbind_reply
  step with obj.Sc.is_null.spec' as ⟨b, hb⟩
  simp only [hb, hp0, decide_false, Bool.false_eq_true, ↓reduceIte]
  refine WP.spec_bind (obj.Sc.reply.val s p) ?_
  intro i hi
  rw [hLw.1] at hi
  subst hi
  have hsp0 : ∀ σ', (Fl4Spec.NonDet.unless (y.scReplies = []) (do
      Fl4Spec.setReplyObjRef Fl4Spec.replyScUpdate (Fl4Spec.the y.scReplies.head?) none
      Fl4Spec.setScObjRef Fl4Spec.scRepliesUpdate p.bv [])) σ = ({((), σ')}, False) →
      Fl4Spec.schedContextUnbindReply (Z := Unit) p.bv σ = ({((), σ')}, False) := by
    intro σ' h
    unfold Fl4Spec.schedContextUnbindReply
    rw [nd_bind_one (nd_liftM_one (getSchedContext_eq hk) _)]; exact h
  cases hL : Lst p with
  | nil =>
    simp only [List.headD_nil, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    refine ⟨σ, Lst, hsp0 σ (by rw [hyL, hL]; rfl), hS, hR, hN, hI, hCR, hRP, id, hRF⟩
  | cons r0 rest =>
    have hr0R : r0 ∈ R := hLR r0 (by rw [hL]; simp)
    have hA0 := hRP.align r0 hr0R
    have hne0 : (r0 != 0#u64) = true := by simpa using hA0.2.1
    simp only [List.headD_cons, hne0, ↓reduceIte]
    obtain ⟨x0, hkr0, hx0⟩ := hCR.reply r0 hr0R
    -- the head reply's `NEXT` word
    refine WP.spec_bind (obj.Reply.set_next.val0 s r0 0#u64) ?_
    rintro s1 rfl
    rw [rz_next]
    have hn0 : Aligned (rNextA r0) := hRP.aligned hr0R (Or.inr (rNextA_val hA0))
    have hS1 : SchedRel st N T C c (L.wr s (rNextA r0) 0#u64) (updK σ r0.bv (.reply { x0 with replySc := none })) :=
      (hS.wr_far hn0 (hRP.far hr0R (Or.inr (rNextA_val hA0))) 0#u64).stableW (WritesIn.refl _ _)
        (NtfnStepW.updReply hkr0 _)
    have hR1 : NtfnStateRel N T (L.mem (L.wr s (rNextA r0) 0#u64)) (updK σ r0.bv (.reply { x0 with replySc := none })) :=
      hR.frame hP (footEq_wr_far hP hn0 (fun n hn => by have := hRP.ntfn r0 hr0R n hn; rw [rNextA_val hA0]; omega)
        (fun t ht => by have := hRP.tcb r0 hr0R t ht; rw [rNextA_val hA0]; omega) 0#u64) (KView.updReply hkr0 _)
    set σ1 := updK σ r0.bv (.reply { x0 with replySc := none }) with hσ1
    have hpr : p.bv ≠ r0.bv := fun e => by rw [e, hkr0] at hk; cases hk
    have hk1 : σ1.kheap p.bv = some (.schedContext y n) := by simp [σ1, updK, hpr, hk]
    -- the SC's `REPLY` word
    refine WP.spec_mono (obj.Sc.set_reply.spec _ p 0#u64) ?_
    rintro s2 rfl
    obtain ⟨hS2, hf2, hK2, -⟩ := hS1.set_sc_reply hp hk1 0#u64 []
    set σ2 := updSc σ1 p.bv { y with scReplies := [] } n with hσ2
    set m := L.mem s
    set m2 := L.mem (L.wr (L.wr s (rNextA r0) 0#u64) (scReplyA p) 0#u64)
    -- the words
    have hM : ∀ b, Aligned b → b.val ≠ (scReplyA p).val → b.val ≠ (rNextA r0).val → m2 b = m b := by
      intro b hb h1 h2
      show L.mem _ b = _
      rw [L.mem_wr_ne haP hb (Ne.symm h1), L.mem_wr_ne hn0 hb (Ne.symm h2)]
    have hMp : m2 (scReplyA p) = 0#u64 := L.mem_wr_same haP
    have hMr : m2 (rNextA r0) = 0#u64 := by
      show L.mem _ _ = _
      rw [L.mem_wr_ne haP hn0 (by
        have := hRP.sc r0 hr0R p hp y n hk; have := hszP y n hk; rw [hvP, rNextA_val hA0]; omega)]
      exact L.mem_wr_same hn0
    have hfarS : ∀ q ∈ C, ∀ r ∈ R, (scReplyA q).val ≠ (rPrevA r).val ∧ (scReplyA q).val ≠ (rNextA r).val := by
      intro q hq r hr
      obtain ⟨-, hvq, hszq⟩ := sc_reply_word hS hq
      obtain ⟨Q, R', hc, hs⟩ := hS.lists
      obtain ⟨xq, nq, hkq, -⟩ := hs.scs q hq
      have := hRP.sc r hr q hq xq nq hkq; have := hszq xq nq hkq
      rw [hvq, rPrevA_val (hRP.align r hr), rNextA_val (hRP.align r hr)]; omega
    have hSne : ∀ q ∈ C, q ≠ p → (scReplyA q).val ≠ (scReplyA p).val := by
      intro q hq e
      obtain ⟨-, hvq, -⟩ := sc_reply_word hS hq
      rw [hvq, hvP]; exact fun h => e (UScalar.eq_of_val_eq (by omega))
    have hal : ∀ r ∈ R, Aligned (rPrevA r) ∧ Aligned (rNextA r) := fun r hr =>
      ⟨hRP.aligned hr (Or.inl (rPrevA_val (hRP.align r hr))), hRP.aligned hr (Or.inr (rNextA_val (hRP.align r hr)))⟩
    have hMprev : ∀ r ∈ R, m2 (rPrevA r) = m (rPrevA r) := fun r hr =>
      hM _ (hal r hr).1 (fun e => (hfarS p hp r hr).1 e.symm) (rwords_ne (hRP.align r hr) hA0).1
    have hMnext : ∀ r ∈ R, r ≠ r0 → m2 (rNextA r) = m (rNextA r) := fun r hr hne =>
      hM _ (hal r hr).2 (fun e => (hfarS p hp r hr).2 e.symm) ((rwords_ne (hRP.align r hr) hA0).2 hne).2
    have hMsc : ∀ q ∈ C, q ≠ p → m2 (scReplyA q) = m (scReplyA q) := fun q hq hne => by
      obtain ⟨haq, -, -⟩ := sc_reply_word hS hq
      exact hM _ haq (hSne q hq hne) (hfarS q hq r0 hr0R).2
    -- other stacks do not hold `r0`
    have hr0p : ∀ q ∈ C, r0 ∈ Lst q → q = p := fun q hq h => hCR.excl q hq p hp r0 h (by rw [hL]; simp)
    set Lst' := Function.update Lst p [] with hLst'
    have hL'p : Lst' p = [] := by simp [Lst']
    have hL'q : ∀ q, q ≠ p → Lst' q = Lst q := fun q hq => by simp [Lst', hq]
    have hdet' : ∀ d, d ∈ Lst p → Detached C Lst' d := by
      intro d hd q hq hdq
      by_cases e : q = p
      · subst e; rw [hL'p] at hdq; cases hdq
      · rw [hL'q q e] at hdq; exact e (hCR.excl q hq p hp d hdq hd)
    have hdet'' : ∀ d, Detached C Lst d → Detached C Lst' d := by
      intro d hd q hq hdq
      by_cases e : q = p
      · subst e; rw [hL'p] at hdq; cases hdq
      · rw [hL'q q e] at hdq; exact hd q hq hdq
    have hCR2 : CallRel m2 R C σ2 Lst' := by
      refine ⟨fun q hq => ?_, fun q hq q' hq' r h1 h2 => ?_, fun r hr => ?_, fun d hd hdd => ?_⟩
      · by_cases e : q = p
        · subst e
          refine ⟨⟨{ y with scReplies := [] }, n, by simp [σ2, updK], by rw [hL'p]; rfl⟩, by rw [hL'p]; simp,
            by rw [hL'p]; exact List.nodup_nil, ?_⟩
          rw [hL'p]; exact ⟨hMp, fun i h => absurd h (by simp)⟩
        · rw [hL'q q e]
          obtain ⟨⟨yq, nq, hkq, hyq⟩, hqR, hqnd, hqw⟩ := hCR.stack q hq
          have hqr0 : q.bv ≠ r0.bv := fun h => by rw [h, hkr0] at hkq; cases hkq
          refine ⟨⟨yq, nq, by simp [σ2, σ1, updK, bv_ne e, hqr0, hkq], hyq⟩, hqR, hqnd, ?_, fun i hi => ?_⟩
          · rw [hMsc q hq e]; exact hqw.1
          · have hmem : (Lst q)[i] ∈ Lst q := List.getElem_mem hi
            have hne : (Lst q)[i] ≠ r0 := fun h => e (hr0p q hq (h ▸ hmem))
            rw [hMprev _ (hqR _ hmem), hMnext _ (hqR _ hmem) hne]; exact hqw.2 i hi
      · have g1 : r ∈ Lst q := by
          by_cases e : q = p
          · subst e; rw [hL'p] at h1; cases h1
          · rw [hL'q q e] at h1; exact h1
        have g2 : r ∈ Lst q' := by
          by_cases e : q' = p
          · subst e; rw [hL'p] at h2; cases h2
          · rw [hL'q q' e] at h2; exact h2
        exact hCR.excl q hq q' hq' r g1 g2
      · obtain ⟨x, hkx, hxs⟩ := hCR.reply r hr
        have hrp : r.bv ≠ p.bv := fun h => by rw [h, hk] at hkx; cases hkx
        by_cases e : r = r0
        · subst e
          refine ⟨{ x0 with replySc := none }, by simp [σ2, σ1, updK, hrp], fun p' => ⟨fun h => (by cases h), ?_⟩⟩
          rintro ⟨q, hq, -, hhd⟩
          have hmem : r ∈ Lst' q := List.mem_of_mem_head? hhd
          exact (hdet' r (by rw [hL]; simp) q hq hmem).elim
        · have hrr0 : r.bv ≠ r0.bv := bv_ne e
          refine ⟨x, by simp [σ2, σ1, updK, hrp, hrr0, hkx], fun p' => ?_⟩
          rw [hxs p']
          constructor
          · rintro ⟨q, hq, hqp, hhd⟩
            refine ⟨q, hq, hqp, ?_⟩
            by_cases e' : q = p
            · subst e'; rw [hL] at hhd; simp at hhd; exact absurd hhd.symm e
            · rw [hL'q q e']; exact hhd
          · rintro ⟨q, hq, hqp, hhd⟩
            refine ⟨q, hq, hqp, ?_⟩
            by_cases e' : q = p
            · subst e'; rw [hL'p] at hhd; cases hhd
            · rw [hL'q q e'] at hhd; exact hhd
      · by_cases hdp : d ∈ Lst p
        · -- a reply of the detached stack
          rw [hL] at hdp
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hdp
          have hw := hLw.2
          rw [hL] at hw
          obtain ⟨hpv, hnx⟩ := hw i hi
          have hmemL : ∀ j (hj : j < (r0 :: rest).length), (r0 :: rest)[j] ∈ Lst p := fun j hj => by
            rw [hL]; exact List.getElem_mem hj
          have hdL : ∀ j (hj : j < (r0 :: rest).length), Detached C Lst' (r0 :: rest)[j] :=
            fun j hj => hdet' _ (hmemL j hj)
          have hRL : ∀ j (hj : j < (r0 :: rest).length), (r0 :: rest)[j] ∈ R := fun j hj => hLR _ (hmemL j hj)
          have hnd : (r0 :: rest).Nodup := hL ▸ hLnd
          refine ⟨?_, fun hne => ?_, fun hne => ?_⟩
          · cases i with
            | zero => show m2 (rNextA r0) &&& 1#u64 = 0#u64; rw [hMr]; rfl
            | succ j =>
              have hne : (r0 :: rest)[j + 1] ≠ r0 := fun h => by
                have := (List.nodup_iff_injective_get.1 hnd) (a₁ := ⟨j + 1, hi⟩) (a₂ := ⟨0, by simp⟩) (by simpa using h)
                simp at this
              dsimp only at hnx
              rw [hMnext _ (hRL _ hi) hne, hnx]
              have hj : j < (r0 :: rest).length := by omega
              rw [List.getD_eq_getElem _ _ hj]
              exact reply_bit (hRP.align _ (hRL j hj)).1
          · cases i with
            | zero => exact absurd hMr hne
            | succ j =>
              have hne' : (r0 :: rest)[j + 1] ≠ r0 := fun h => by
                have := (List.nodup_iff_injective_get.1 hnd) (a₁ := ⟨j + 1, hi⟩) (a₂ := ⟨0, by simp⟩) (by simpa using h)
                simp at this
              have hj : j < (r0 :: rest).length := by omega
              dsimp only at hnx
              rw [hMnext _ (hRL _ hi) hne', hnx, List.getD_eq_getElem _ _ hj]
              refine ⟨hRL j hj, hdL j hj, ?_⟩
              rw [hMprev _ (hRL j hj), (hw j hj).1, List.getD_eq_getElem _ _ hi]
          · rw [hMprev _ (hRL _ hi), hpv] at hne ⊢
            have hi1 : i + 1 < (r0 :: rest).length := by
              by_contra h
              rw [List.getD_eq_default _ _ (by omega)] at hne; exact hne rfl
            rw [List.getD_eq_getElem _ _ hi1]
            refine ⟨hRL _ hi1, hdL _ hi1, ?_⟩
            have hne' : (r0 :: rest)[i + 1] ≠ r0 := fun h => by
              have := (List.nodup_iff_injective_get.1 hnd) (a₁ := ⟨i + 1, hi1⟩) (a₂ := ⟨0, by simp⟩) (by simpa using h)
              simp at this
            have := (hw (i + 1) hi1).2
            dsimp only at this
            rw [hMnext _ (hRL _ hi1) hne', this]
            rw [List.getD_eq_getElem _ _ hi]
        · -- an old detached reply
          have hdo : Detached C Lst d := by
            intro q hq hdq
            by_cases e : q = p
            · subst e; exact hdp hdq
            · exact hdd q hq (by rw [hL'q q e]; exact hdq)
          have hdr0 : d ≠ r0 := fun h => hdp (by rw [h, hL]; simp)
          obtain ⟨t1, t2, t3⟩ := hCR.det d hd hdo
          have hnotp : ∀ e, Detached C Lst e → e ≠ r0 := fun e he h => he p hp (by rw [h, hL]; simp)
          rw [hMnext d hd hdr0, hMprev d hd]
          refine ⟨t1, fun hne => ?_, fun hne => ?_⟩
          · obtain ⟨g1, g2, g3⟩ := t2 hne
            exact ⟨g1, hdet'' _ g2, by rw [hMprev _ g1]; exact g3⟩
          · obtain ⟨g1, g2, g3⟩ := t3 hne
            exact ⟨g1, hdet'' _ g2, by rw [hMnext _ g1 (hnotp _ g2)]; exact g3⟩
    have hSz : SzKeep σ σ2 := by
      intro q x' n' hq
      by_cases e : q = p.bv
      · subst e; rw [show σ2.kheap p.bv = some (.schedContext { y with scReplies := [] } n) by simp [σ2, updK]] at hq
        cases hq; exact ⟨y, hk⟩
      · have : σ2.kheap q = σ1.kheap q := by simp [σ2, updK, e]
        rw [this] at hq
        by_cases e' : q = r0.bv
        · subst e'; simp [σ1, updK] at hq
        · have : σ1.kheap q = σ.kheap q := by simp [σ1, updK, e']
          rw [this] at hq; exact ⟨x', hq⟩
    refine ⟨σ2, Lst', ?_, hS2, hR1.frame hS1.placed hf2 hK2, (hN.updReply hkr0 _).updSc,
      (hI.updReply hkr0).scFields hk1 rfl rfl rfl rfl, hCR2, hRP.frame (by simp) hSz, fun hA => ?_, ?_⟩
    · refine hsp0 _ ?_
      rw [hyL, hL]
      unfold Fl4Spec.NonDet.unless
      rw [if_neg (by simp)]
      simp only [List.map_cons, List.head?_cons, Fl4Spec.the]
      rw [nd_bind_one (setReplySc_eq none hkr0)]
      exact updateSchedContext_eq hk1 _
    · have hA1 : ActIdle σ1 := hA.keepE (E := fun _ => False) (TKeepE.updReply _ hkr0 _) (fun u hu => Or.inl hu)
        (Or.inl rfl) rfl (fun _ _ h => h) id
      exact hA1.keepE (E := fun _ => False) (TKeepE.updSc _ hk1 rfl) (fun u hu => Or.inl hu) (Or.inl rfl) rfl
        (fun _ _ h => h) id
    · intro d hd hfd
      obtain ⟨xd, hkd, -⟩ := hCR.reply d hd
      have hfσ : Free σ d := by
        obtain ⟨x', hk', hx'⟩ := hfd
        have hdp : d.bv ≠ p.bv := fun e => by rw [e, hk] at hkd; cases hkd
        have h2 : σ2.kheap d.bv = σ1.kheap d.bv := by simp [σ2, updK, hdp]
        rw [h2] at hk'
        by_cases e : d = r0
        · subst e; simp [σ1, updK] at hk'; subst hk'; rw [hkr0] at hkd; cases hkd; exact ⟨_, hkr0, hx'⟩
        · have h1 : σ1.kheap d.bv = σ.kheap d.bv := by simp [σ1, updK, bv_ne e]
          rw [h1] at hk'; exact ⟨x', hk', hx'⟩
      obtain ⟨hdet, h0n, h0p⟩ := hRF d hd hfσ
      have hdr0 : d ≠ r0 := fun h => hdet p hp (by rw [h, hL]; simp)
      exact ⟨hdet'' d hdet, by rw [hMnext d hd hdr0]; exact h0n, by rw [hMprev d hd]; exact h0p⟩

end

end

end Fl4Proofs.P3.Sched
