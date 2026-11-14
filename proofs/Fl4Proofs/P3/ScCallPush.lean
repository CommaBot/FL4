/-
P3 (DESIGN.md §9), scheduling contexts: **pushing a reply on a call stack**
(`reply_push`'s donation branch) against l4v `bind_sc_reply` and
`sched_context_donate`.

* `CallRel.push`: the call-stack relation after the push, from the four
  written words (the old head's `NEXT`, the reply's `PREV` and `NEXT`, the
  SC's `REPLY`) and the spec's new `sc_replies` and `reply_sc`; the pushed
  reply was detached and isolated.
-/
import Fl4Proofs.P3.ScDonateB
import Fl4Proofs.P3.ScCallUnbind
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

theorem even_bit0 (x : U64) (h : x.val % 2 = 0) : x.bv.getLsbD 0 = false := by
  rw [BitVec.getLsbD, Nat.testBit_zero, UScalar.bv_toNat]; simp [h]

theorem and_not1 (x : U64) (h : x.val % 2 = 0) : x &&& ~~~1#u64 = x := by
  apply eq_of_bv; apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [UScalar.bv_and, UScalar.bv_not, BitVec.getLsbD_and, BitVec.getLsbD_not, one_bit, hi]
  by_cases h0 : i = 0
  · subst h0; have := even_bit0 x h; simp only [BitVec.getLsbD_eq_getElem hi] at this; simp [this]
  · simp [h0]

theorem or0 (x : U64) : x ||| 0#u64 = x := by
  apply eq_of_bv; simp

/-- **The call-stack relation after a push** of the detached, isolated reply
`r` on `sc`'s stack. -/
theorem CallRel.push {R C : Set U64} {m m' : U64 → U64} {σ σ' : Fl4Spec.State Unit} {Lst : U64 → List U64}
    (h : CallRel m R C σ Lst) {sc r : U64} (hsc : sc ∈ C) (hr : r ∈ R) (hdet : Detached C Lst r)
    (hiso : Isolated m R r)
    (hmP : ∀ d ∈ R, d ≠ r → m' (rPrevA d) = m (rPrevA d))
    (hmN : ∀ d ∈ R, d ≠ r → (Lst sc).head? ≠ some d → m' (rNextA d) = m (rNextA d))
    (hmH : ∀ d, (Lst sc).head? = some d → m' (rNextA d) = r)
    (hmPr : m' (rPrevA r) = (Lst sc).headD 0#u64) (hmNr : m' (rNextA r) = sc ||| 1#u64)
    (hmS : m' (scReplyA sc) = r) (hmS' : ∀ q ∈ C, q ≠ sc → m' (scReplyA q) = m (scReplyA q))
    {y : Fl4Spec.SchedContext} {n : Nat} (hk : σ.kheap sc.bv = some (.schedContext y n))
    (hk' : σ'.kheap sc.bv = some (.schedContext { y with scReplies := r.bv :: y.scReplies } n))
    (hkq : ∀ q ∈ C, q ≠ sc → σ'.kheap q.bv = σ.kheap q.bv)
    {xr : Fl4Spec.Reply} (hkr : σ.kheap r.bv = some (.reply xr))
    (hkr' : σ'.kheap r.bv = some (.reply { xr with replySc := some sc.bv }))
    (hkh : ∀ d x, (Lst sc).head? = some d → σ.kheap d.bv = some (.reply x) →
      σ'.kheap d.bv = some (.reply { x with replySc := none }))
    (hkd : ∀ d ∈ R, d ≠ r → (Lst sc).head? ≠ some d → σ'.kheap d.bv = σ.kheap d.bv) :
    CallRel m' R C σ' (Function.update Lst sc (r :: Lst sc)) := by
  set Ls := Lst sc with hLs
  set Lst' := Function.update Lst sc (r :: Ls)
  have hL'sc : Lst' sc = r :: Ls := by simp [Lst']
  have hL'q : ∀ q, q ≠ sc → Lst' q = Lst q := fun q hq => by simp [Lst', hq]
  obtain ⟨⟨y0, n0, hk0, hy0⟩, hLR, hLnd, hLw⟩ := h.stack sc hsc
  rw [hk] at hk0; cases hk0
  have hrL : r ∉ Ls := hdet sc hsc
  -- the members of `sc`'s old stack
  have hmemsc : ∀ d q, q ∈ C → d ∈ Lst q → d ∈ Ls → q = sc := fun d q hq h1 h2 => h.excl q hq sc hsc d h1 h2
  refine ⟨fun q hq => ?_, fun q hq q' hq' d h1 h2 => ?_, fun d hd => ?_, fun d hd hdd => ?_⟩
  · by_cases e : q = sc
    · subst e
      refine ⟨⟨_, n, hk', by rw [hL'sc, hy0]; rfl⟩, ?_, ?_, ?_, ?_⟩
      · rw [hL'sc]; intro d hd'; rcases List.mem_cons.1 hd' with rfl | hd'
        · exact hr
        · exact hLR d hd'
      · rw [hL'sc]; exact List.nodup_cons.2 ⟨hrL, hLnd⟩
      · rw [hL'sc, hmS]; rfl
      · rw [hL'sc]; intro i hi
        cases i with
        | zero =>
          refine ⟨?_, ?_⟩
          · show m' (rPrevA r) = (r :: Ls).getD 1 0#u64
            rw [hmPr]; cases Ls <;> rfl
          · exact hmNr
        | succ j =>
          have hj : j < Ls.length := by simpa using hi
          have hdj := hLR _ (List.getElem_mem hj)
          have hh0 : Ls.head? = some Ls[0] := by
            rw [List.head?_eq_getElem?]; exact List.getElem?_eq_getElem (by omega)
          have hne : Ls[j] ≠ r := fun e => hrL (e ▸ List.getElem_mem hj)
          obtain ⟨g1, g2⟩ := hLw.2 j hj
          refine ⟨?_, ?_⟩
          · show m' (rPrevA Ls[j]) = (r :: Ls).getD (j + 2) 0#u64
            rw [hmP _ hdj hne, g1]; rfl
          · show m' (rNextA Ls[j]) = (r :: Ls).getD j 0#u64
            cases j with
            | zero =>
              rw [hmH _ hh0]; rfl
            | succ k =>
              have hnh : Ls.head? ≠ some Ls[k + 1] := by
                intro e
                rw [hh0] at e
                have := (List.nodup_iff_injective_get.1 hLnd) (a₁ := ⟨k + 1, hj⟩) (a₂ := ⟨0, Nat.zero_lt_of_lt hj⟩)
                  (by simpa using (Option.some.inj e).symm)
                simp at this
              rw [hmN _ hdj hne hnh, g2]; rfl
    · rw [hL'q q e]
      obtain ⟨⟨yq, nq, hkq0, hyq⟩, hqR, hqnd, hqw⟩ := h.stack q hq
      refine ⟨⟨yq, nq, by rw [hkq q hq e]; exact hkq0, hyq⟩, hqR, hqnd, by rw [hmS' q hq e]; exact hqw.1,
        fun i hi => ?_⟩
      have hm := List.getElem_mem hi
      have hne : (Lst q)[i] ≠ r := fun e' => hdet q hq (e' ▸ hm)
      have hnh : Ls.head? ≠ some (Lst q)[i] := fun e' => e (hmemsc _ q hq hm (List.mem_of_mem_head? e'))
      rw [hmP _ (hqR _ hm) hne, hmN _ (hqR _ hm) hne hnh]; exact hqw.2 i hi
  · have g : ∀ q, q ∈ C → d ∈ Lst' q → d = r ∧ q = sc ∨ d ∈ Lst q := fun q hq hdq => by
      by_cases e : q = sc
      · subst e; rw [hL'sc] at hdq; rcases List.mem_cons.1 hdq with rfl | hdq
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr hdq
      · rw [hL'q q e] at hdq; exact Or.inr hdq
    rcases g q hq h1 with ⟨rfl, rfl⟩ | g1 <;> rcases g q' hq' h2 with ⟨e', rfl⟩ | g2
    · rfl
    · exact absurd g2 (hdet q' hq')
    · subst e'; exact absurd g1 (hdet q hq)
    · exact h.excl q hq q' hq' d g1 g2
  · obtain ⟨x, hkx, hxs⟩ := h.reply d hd
    by_cases e : d = r
    · subst e
      rw [hkr] at hkx; cases hkx
      refine ⟨_, hkr', fun p => ⟨fun hp => ?_, fun ⟨q, hq, hqp, hhd⟩ => ?_⟩⟩
      · cases hp; exact ⟨sc, hsc, rfl, by rw [hL'sc]; rfl⟩
      · by_cases e' : q = sc
        · subst e'; rw [← hqp]
        · rw [hL'q q e'] at hhd; exact absurd (List.mem_of_mem_head? hhd) (hdet q hq)
    · by_cases eh : Ls.head? = some d
      · refine ⟨_, hkh d x eh hkx, fun p => ⟨fun hp => (by cases hp), fun ⟨q, hq, hqp, hhd⟩ => ?_⟩⟩
        by_cases e' : q = sc
        · subst e'; rw [hL'sc] at hhd; simp at hhd; exact absurd hhd.symm e
        · rw [hL'q q e'] at hhd
          exact absurd (hmemsc d q hq (List.mem_of_mem_head? hhd) (List.mem_of_mem_head? eh)) e'
      · refine ⟨x, by rw [hkd d hd e eh]; exact hkx, fun p => ?_⟩
        rw [hxs p]
        constructor
        · rintro ⟨q, hq, hqp, hhd⟩
          refine ⟨q, hq, hqp, ?_⟩
          by_cases e' : q = sc
          · subst e'; exact absurd hhd eh
          · rw [hL'q q e']; exact hhd
        · rintro ⟨q, hq, hqp, hhd⟩
          refine ⟨q, hq, hqp, ?_⟩
          by_cases e' : q = sc
          · subst e'; rw [hL'sc] at hhd; simp at hhd; exact absurd hhd.symm e
          · rw [hL'q q e'] at hhd; exact hhd
  · -- a detached reply stays detached, with its links
    have hdr : d ≠ r := fun e => hdd sc hsc (by rw [e, hL'sc]; simp)
    have hdo : Detached C Lst d := by
      intro q hq hdq
      by_cases e : q = sc
      · subst e; exact hdd q hq (by rw [hL'sc]; exact List.mem_cons_of_mem _ hdq)
      · exact hdd q hq (by rw [hL'q q e]; exact hdq)
    have hnh : ∀ e, Detached C Lst e → Ls.head? ≠ some e := fun e he h' => he sc hsc (List.mem_of_mem_head? h')
    have hdet' : ∀ e, Detached C Lst e → e ≠ r → Detached C Lst' e := by
      intro e he her q hq heq
      by_cases e' : q = sc
      · subst e'; rw [hL'sc] at heq; rcases List.mem_cons.1 heq with rfl | heq
        · exact her rfl
        · exact he q hq heq
      · rw [hL'q q e'] at heq; exact he q hq heq
    obtain ⟨t1, t2, t3⟩ := h.det d hd hdo
    rw [hmP d hd hdr, hmN d hd hdr (hnh d hdo)]
    refine ⟨t1, fun hne => ?_, fun hne => ?_⟩
    · obtain ⟨g1, g2, g3⟩ := t2 hne
      have hner : m (rNextA d) ≠ r := (hiso.2.2 d hd).1
      exact ⟨g1, hdet' _ g2 hner, by rw [hmP _ g1 hner]; exact g3⟩
    · obtain ⟨g1, g2, g3⟩ := t3 hne
      have hner : m (rPrevA d) ≠ r := (hiso.2.2 d hd).2
      exact ⟨g1, hdet' _ g2 hner, by rw [hmN _ g1 hner (hnh _ g2)]; exact g3⟩

end


section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- A donation's footprint (the scheduler words and an SC's `TCB` word) keeps
the call-stack words. -/
theorem callWords_of_dfoot {N T C R : Set U64} {c : U64} {s s' : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (hRP : RPlaced st N T C R c s σ) {sc : U64} (hsc : sc ∈ C)
    (hw : WritesIn st s s' (fun b => SFoot st T c s b ∨ b = scW sc 24#u64)) :
    (∀ q ∈ C, L.mem s' (scReplyA q) = L.mem s (scReplyA q)) ∧
    (∀ r ∈ R, L.mem s' (rPrevA r) = L.mem s (rPrevA r) ∧ L.mem s' (rNextA r) = L.mem s (rNextA r)) := by
  obtain ⟨Q, R', hc, hs⟩ := hS.lists
  obtain ⟨x, n, hk, hx⟩ := hs.scs sc hsc
  have hb := hx.bounds
  have hv24 : (scW sc 24#u64).val = sc.val + 24 := by rw [scW_val (by simp; omega)]; rfl
  have h24 : ScObj sc n (scW sc 24#u64) := hx.in_obj (by unfold ScIn; rw [hv24]; omega)
  -- the SFoot part
  have hw' : ∀ b, Aligned b → ¬ SFoot st T c s b → b ≠ scW sc 24#u64 → L.mem s' b = L.mem s b :=
    fun b hb' h1 h2 => hw.mem_eq hb' (fun h => h.elim h1 h2)
  have base := callWords_of_sfoot hS hRP (s' := s) (WritesIn.refl _ _)
  refine ⟨fun q hq => ?_, fun r hr => ?_⟩
  · obtain ⟨xq, nq, hkq, hxq⟩ := hs.scs q hq
    have ha := hxq.hdr (K := 32#u64) (by simp) (by simp)
    obtain ⟨-, h2, h3, -⟩ := hS.scOutIn hq ha.2
    rw [scReplyA_eq]
    refine hw' _ ha.1 ?_ ?_
    · rintro (⟨y, hy, g1, g2⟩ | ⟨g1, g2⟩)
      · have := h3 y hy; omega
      · omega
    · intro e
      by_cases eq : q = sc
      · subst eq; have := congrArg UScalar.val e; rw [hv24, scW_val (by have := hxq.bounds; simp; omega)] at this
        simp at this
      · exact hS.scDisj q hq sc hsc eq xq nq x n hkq hk _ (hxq.in_obj ha.2) (e ▸ h24)
  · have hA := hRP.align r hr
    have v1 := rPrevA_val hA
    have v2 := rNextA_val hA
    have hfar := hRP.sc r hr sc hsc x n hk
    unfold ScObj at h24
    refine ⟨hw' _ (hRP.aligned hr (Or.inl v1)) ?_ ?_, hw' _ (hRP.aligned hr (Or.inr v2)) ?_ ?_⟩
    · rintro (⟨y, hy, g1, g2⟩ | ⟨g1, g2⟩)
      · have := hRP.tcb r hr y hy; omega
      · have := hRP.ksb r hr; simp only [LawfulStore.nodeBase] at this g1 g2; omega
    · intro e; have := congrArg UScalar.val e; omega
    · rintro (⟨y, hy, g1, g2⟩ | ⟨g1, g2⟩)
      · have := hRP.tcb r hr y hy; omega
      · have := hRP.ksb r hr; simp only [LawfulStore.nodeBase] at this g1 g2; omega
    · intro e; have := congrArg UScalar.val e; omega

/-- A reply on no stack with no links is isolated: no stack member links to
it, and a detached reply linking to it would be its neighbour. -/
theorem CallRel.isolated {R C : Set U64} {m : U64 → U64} {σ : Fl4Spec.State Unit} {Lst : U64 → List U64}
    (h : CallRel m R C σ Lst) (hR0 : ∀ d ∈ R, d ≠ 0#u64 ∧ d.val % 2 = 0) {r : U64} (hr : r ∈ R)
    (hd : Detached C Lst r) (hn : m (rNextA r) = 0#u64) (hp : m (rPrevA r) = 0#u64) : Isolated m R r := by
  refine ⟨hn, hp, fun d hd' => ?_⟩
  by_cases hdet : Detached C Lst d
  · obtain ⟨-, t2, t3⟩ := h.det d hd' hdet
    refine ⟨fun e => ?_, fun e => ?_⟩
    · have := (t2 (by rw [e]; exact (hR0 r hr).1)).2.2
      rw [e, hp] at this; exact (hR0 d hd').1 this.symm
    · have := (t3 (by rw [e]; exact (hR0 r hr).1)).2.2
      rw [e, hn] at this; exact (hR0 d hd').1 this.symm
  · simp only [Detached, not_forall, not_not] at hdet
    obtain ⟨q, hq, hdq⟩ := hdet
    obtain ⟨-, hqR, -, hqw⟩ := h.stack q hq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hdq
    obtain ⟨g1, g2⟩ := hqw.2 i hi
    refine ⟨fun e => ?_, fun e => ?_⟩
    · rw [g2] at e
      cases i with
      | zero =>
        dsimp only at e
        have e1 : (q ||| 1#u64).bv.getLsbD 0 = true := by
          simp only [UScalar.bv_or, BitVec.getLsbD_or, one_bit]; simp
        rw [e, even_bit0 r (hR0 r hr).2] at e1
        exact absurd e1 (by decide)
      | succ j =>
        change (Lst q).getD j 0#u64 = r at e
        rw [List.getD_eq_getElem _ _ (by omega)] at e
        exact hd q hq (e ▸ List.getElem_mem _)
    · rw [g1] at e
      by_cases hlt : i + 1 < (Lst q).length
      · rw [List.getD_eq_getElem _ _ hlt] at e
        exact hd q hq (e ▸ List.getElem_mem _)
      · rw [List.getD_eq_default _ _ (by omega)] at e
        exact (hR0 r hr).1 e.symm

/-- **`reply_push`'s precondition from `RFree`**: a free reply is detached
and isolated. -/
theorem RFree.push_ready {R C : Set U64} {m : U64 → U64} {σ : Fl4Spec.State Unit} {Lst : U64 → List U64}
    (h : RFree m R C σ Lst) (hCR : CallRel m R C σ Lst) (hR0 : ∀ d ∈ R, d ≠ 0#u64 ∧ d.val % 2 = 0)
    {r : U64} (hr : r ∈ R) (hf : Free σ r) : Detached C Lst r ∧ Isolated m R r := by
  obtain ⟨hd, hn, hp⟩ := h r hr hf
  exact ⟨hd, hCR.isolated hR0 hr hd hn hp⟩

end

end

end Fl4Proofs.P3.Sched
