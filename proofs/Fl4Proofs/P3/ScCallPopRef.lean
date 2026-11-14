/-
P3 (DESIGN.md §9), scheduling contexts: **`reply_pop`** (`reply_remove` of
a stack's head) against l4v `reply_unlink_sc` and the donation of the SC
back to the caller `t` if it has none (`reply_remove`'s middle part). The
final `reply_unlink` (`reply_unlink_tcb`, the endpoint side) is a
hypothesis `hU`, given the relations at that point and the popped reply
isolated.
-/
import Fl4Proofs.P3.ScCallPop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

theorem obj.Reply.next_raw.spec2 (s : S) (r : obj.Reply) :
    obj.Reply.next_raw st r s ⦃ v => v = L.mem s (rNextA r) ⦄ := by
  unfold obj.Reply.next_raw; step*; simp_all [rNextA]

theorem obj.Reply.set_next_raw.spec2 (s : S) (r : obj.Reply) (v : U64) :
    obj.Reply.set_next_raw st r s v ⦃ s' => s' = L.wr s (rNextA r) v ⦄ := by
  unfold obj.Reply.set_next_raw; step*; simp_all [rNextA]

theorem or1_and_not1 (x : U64) (h : x.val % 2 = 0) : (x ||| 1#u64) &&& ~~~1#u64 = x := by
  apply eq_of_bv; apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [UScalar.bv_and, UScalar.bv_or, UScalar.bv_not, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not, one_bit, hi]
  by_cases h0 : i = 0
  · subst h0; have := even_bit0 x h; simp only [BitVec.getLsbD_eq_getElem hi] at this; simp [this]
  · simp [h0]


theorem getD1_cons {α : Type} (a : α) (l : List α) (d : α) : (a :: l).getD 1 d = l.headD d := by
  cases l <;> rfl

/-- **`reply_pop` refines `reply_unlink_sc`, the donation back to `t`, and
(by `hU`) `reply_unlink_tcb`.** -/
theorem reply_pop_refines {N T C R : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    {Lst : U64 → List U64} (hCR : CallRel (L.mem s) R C σ Lst) (hRP : RPlaced st N T C R c s σ)
    {sc : U64} (hsc : sc ∈ C) (hsc0 : sc ≠ 0#u64) {y : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap sc.bv = some (.schedContext y n)) {r : U64} {rest : List U64} (hL : Lst sc = r :: rest)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hdon : xt.tcbSchedContext = none → ∃ f, f ∈ T ∧ y.scTcb = some f.bv ∧ f ≠ t)
    (hrel : xt.tcbSchedContext = none → inClass xt.tcbState → Fl4Spec.scActive y = true → released σ y)
    (Q : S × A → Prop)
    (hU : ∀ (s5 : S) (σ5 : Fl4Spec.State Unit) (Lst5 : U64 → List U64),
      SchedRel st N T C c s5 σ5 → NtfnStateRel N T (L.mem s5) σ5 → NSC N C σ5 → Inv σ5 →
      CallRel (L.mem s5) R C σ5 Lst5 → RPlaced st N T C R c s5 σ5 → Isolated (L.mem s5) R r →
      (do
        Fl4Spec.replyUnlinkSc (Z := Unit) sc.bv r.bv
        Fl4Spec.NonDet.when (xt.tcbSchedContext = none) (Fl4Spec.schedContextDonate (Z := Unit) sc.bv t.bv) :
        Fl4Spec.SMonad Unit Unit) σ = ({((), σ5)}, False) →
      ipc.reply_unlink st s5 r t ⦃ s6 => Q (s6, a) ⦄) :
    ipc.reply_pop st ar s a r t ⦃ Q ⦄ := by
  have hP := hS.placed
  obtain ⟨Q0, R0, hc, hs⟩ := hS.lists
  obtain ⟨⟨y0, n0, hk0, hyL⟩, hLR, hLnd, hLw⟩ := hCR.stack sc hsc
  rw [hk] at hk0; cases hk0
  have hLw' := hLw
  rw [hL] at hLR hLnd hLw hyL
  obtain ⟨haP, hvP, hszP⟩ := sc_reply_word hS hsc
  have hrR : r ∈ R := hLR r (by simp)
  have hA := hRP.align r hrR
  have hal : ∀ d ∈ R, Aligned (rPrevA d) ∧ Aligned (rNextA d) := fun d hd =>
    ⟨hRP.aligned hd (Or.inl (rPrevA_val (hRP.align d hd))), hRP.aligned hd (Or.inr (rNextA_val (hRP.align d hd)))⟩
  have hev : ∀ d ∈ R, d.val % 2 = 0 := fun d hd => by have := (hRP.align d hd).1; omega
  have hsc2 : sc.val % 2 = 0 := by
    obtain ⟨x, n', -, hx⟩ := hs.scs sc hsc
    have := hx.bounds.1; omega
  have hfarS : ∀ q ∈ C, ∀ d ∈ R, (scReplyA q).val ≠ (rPrevA d).val ∧ (scReplyA q).val ≠ (rNextA d).val := by
    intro q hq d hd
    obtain ⟨-, hvq, hszq⟩ := sc_reply_word hS hq
    obtain ⟨xq, nq, hkq, -⟩ := hs.scs q hq
    have := hRP.sc d hd q hq xq nq hkq; have := hszq xq nq hkq
    rw [hvq, rPrevA_val (hRP.align d hd), rNextA_val (hRP.align d hd)]; omega
  have hSne : ∀ q ∈ C, q ≠ sc → (scReplyA q).val ≠ (scReplyA sc).val := by
    intro q hq e
    obtain ⟨-, hvq, -⟩ := sc_reply_word hS hq
    rw [hvq, hvP]; exact fun h => e (UScalar.eq_of_val_eq (by omega))
  have hrrest : r ∉ rest := (List.nodup_cons.1 hLnd).1
  have hrestR : ∀ d ∈ rest, d ∈ R := fun d hd => hLR d (List.mem_cons_of_mem _ hd)
  have hhR : ∀ d, rest.head? = some d → d ∈ R := fun d h => hrestR d (List.mem_of_mem_head? h)
  have hhr : ∀ d, rest.head? = some d → d ≠ r := fun d h e => hrrest (e ▸ List.mem_of_mem_head? h)
  have hhe : (rest.headD 0#u64).val % 2 = 0 := by
    cases hr' : rest with
    | nil => rfl
    | cons d l => exact hev d (hrestR d (by rw [hr']; simp))
  obtain ⟨xr, hkr, hxr⟩ := hCR.reply r hrR
  have hpr : sc.bv ≠ r.bv := fun e => by rw [e, hkr] at hk; cases hk
  have hm0 := hLw.2 0 (by simp)
  simp only [List.getElem_cons_zero] at hm0
  obtain ⟨hpv0, hnx0⟩ := hm0
  rw [getD1_cons] at hpv0
  have hpt : sc.bv ≠ t.bv := fun e => by rw [e, hkt] at hk; cases hk
  have hrt : r.bv ≠ t.bv := fun e => by rw [e, hkt] at hkr; cases hkr
  have hrsc : xr.replySc = some sc.bv := (hxr sc.bv).2 ⟨sc, hsc, rfl, by rw [hL]; rfl⟩
  unfold ipc.reply_pop
  step with obj.Reply.next.spec as ⟨nx, hnx⟩
  have hnx' : nx = sc := by rw [hnx, hnx0]; exact or1_and_not1 _ hsc2
  clear hnx
  subst nx
  step with obj.Reply.prev.spec as ⟨pv, hpv⟩
  have hpv' : pv = rest.headD 0#u64 := by rw [hpv, hpv0]; exact and_not1 _ hhe
  clear hpv
  subst pv
  refine WP.spec_bind (obj.Reply.next_raw.spec2 s r) ?_
  intro nr hnr
  rw [hnx0] at hnr
  subst hnr
  -- the SC's `REPLY` word: the new head
  refine WP.spec_bind (obj.Sc.set_reply.spec s sc (rest.headD 0#u64)) ?_
  rintro s1 rfl
  obtain ⟨hS1, hf1, hK1, hw1⟩ := hS.set_sc_reply hsc hk (rest.headD 0#u64) y.scReplies.tail
  set σa := updSc σ sc.bv { y with scReplies := y.scReplies.tail } n with hσa
  have hR1 := hR.frame hP hf1 hK1
  have hka : ∀ q, q ≠ sc.bv → σa.kheap q = σ.kheap q := fun q hq => by simp [σa, updK, hq]
  have hkasc : σa.kheap sc.bv = some (.schedContext { y with scReplies := y.scReplies.tail } n) := by
    simp [σa, updK]
  have hIa : Inv σa := hI.scFields hk rfl rfl rfl rfl
  have hNa : NSC N C σa := hN.updSc
  have hkra : σa.kheap r.bv = some (.reply xr) := by rw [hka _ (Ne.symm hpr)]; exact hkr
  -- the part after the new head's `NEXT` word
  have cont : ∀ (s2 : S) (σb : Fl4Spec.State Unit),
      SchedRel st N T C c s2 σb → NtfnStateRel N T (L.mem s2) σb → NSC N C σb → Inv σb →
      L.ksb s2 = L.ksb s →
      (∀ q, q ≠ sc.bv → (∀ d, rest.head? = some d → q ≠ d.bv) → σb.kheap q = σ.kheap q) →
      σb.kheap sc.bv = some (.schedContext { y with scReplies := y.scReplies.tail } n) →
      (∀ d x, rest.head? = some d → σ.kheap d.bv = some (.reply x) →
        σb.kheap d.bv = some (.reply { x with replySc := some sc.bv })) →
      σb.curTime = σ.curTime →
      ((rest = [] ∧ σb = σa) ∨ (∃ d l x, rest = d :: l ∧ σ.kheap d.bv = some (.reply x) ∧
        σb = updK σa d.bv (.reply { x with replySc := some sc.bv }))) →
      (∀ b, Aligned b → b.val ≠ (scReplyA sc).val → (∀ d, rest.head? = some d → b.val ≠ (rNextA d).val) →
        L.mem s2 b = L.mem s b) →
      L.mem s2 (scReplyA sc) = rest.headD 0#u64 →
      (∀ d, rest.head? = some d → L.mem s2 (rNextA d) = sc ||| 1#u64) →
      (do
        let s3 ← obj.Reply.set_next st r s2 0#u64 false
        let i ← obj.Tcb.sc st t s3
        let (s4, a1) ← if i = 0#u64 then schedcontext.donate st ar s3 a sc t else ok (s3, a)
        let s5 ← obj.Reply.set_prev st r s4 0#u64
        let s6 ← ipc.reply_unlink st s5 r t
        ok (s6, a1)) ⦃ Q ⦄ := by
    intro s2 σb hS2 hR2 hN2 hI2 hks2 hkb hkbsc hkbh htmb hcase hm2 hm2s hm2h
    have hnh_sc : ∀ d, rest.head? = some d → sc.bv ≠ d.bv := fun d h e => by
      obtain ⟨xd, hkd, -⟩ := hCR.reply d (hhR d h); rw [← e, hk] at hkd; cases hkd
    have hnh_r : ∀ d, rest.head? = some d → r.bv ≠ d.bv := fun d h e => hhr d h (eq_of_bv e).symm
    have hkrb : σb.kheap r.bv = some (.reply xr) := by rw [hkb _ (Ne.symm hpr) hnh_r]; exact hkr
    have hSzb : SzKeep σ σb := by
      intro q x' n' hq
      by_cases e : q = sc.bv
      · subst e; rw [hkbsc] at hq; cases hq; exact ⟨y, hk⟩
      by_cases hq' : ∃ d, rest.head? = some d ∧ q = d.bv
      · obtain ⟨d, hh, rfl⟩ := hq'
        obtain ⟨xd, hkd, -⟩ := hCR.reply d (hhR d hh)
        rw [hkbh d xd hh hkd] at hq; cases hq
      · rw [hkb q e (fun d hh e' => hq' ⟨d, hh, e'⟩)] at hq; exact ⟨x', hq⟩
    have hRP2 : RPlaced st N T C R c s2 σb := hRP.frame hks2 hSzb
    -- `NEXT` of `r`
    refine WP.spec_bind (obj.Reply.set_next.val0 s2 r 0#u64) ?_
    rintro s3 rfl
    rw [rz_next]
    have hNr := (hal r hrR).2
    have hPr := (hal r hrR).1
    set σc := updK σb r.bv (.reply { xr with replySc := none }) with hσc
    have hS3 := (hS2.wr_far hNr (hRP2.far hrR (Or.inr (rNextA_val hA))) 0#u64).stableW
      (WritesIn.refl _ _) (NtfnStepW.updReply hkrb { xr with replySc := none })
    have hR3 : NtfnStateRel N T (L.mem (L.wr s2 (rNextA r) 0#u64)) σc :=
      hR2.frame hP (footEq_wr_far hP hNr (fun n hn => by have := hRP.ntfn r hrR n hn; rw [rNextA_val hA]; omega)
        (fun t ht => by have := hRP.tcb r hrR t ht; rw [rNextA_val hA]; omega) _) (KView.updReply hkrb _)
    have hI3 : Inv σc := hI2.updReply hkrb
    have hN3 : NSC N C σc := hN2.updReply hkrb _
    have hkc : ∀ q, q ≠ r.bv → σc.kheap q = σb.kheap q := fun q hq => by simp [σc, updK, hq]
    have hkcr : σc.kheap r.bv = some (.reply { xr with replySc := none }) := by simp [σc, updK]
    have hSzc : SzKeep σb σc := by
      intro q x' n' hq
      by_cases e : q = r.bv
      · subst e; rw [hkcr] at hq; cases hq
      · rw [hkc q e] at hq; exact ⟨x', hq⟩
    have hRP3 : RPlaced st N T C R c (L.wr s2 (rNextA r) 0#u64) σc := hRP2.frame (by simp) hSzc
    -- the spec's `reply_unlink_sc`
    have hunl : Fl4Spec.replyUnlinkSc (Z := Unit) sc.bv r.bv σ = ({((), σc)}, False) := by
      unfold Fl4Spec.replyUnlinkSc
      rw [nd_bind_one (nd_liftM_one (getSchedContext_eq hk) _), nd_bind_one (Fl4Proofs.P3.Endp.getReply_eq hkr)]
      rw [hyL]
      simp only [List.map_cons, List.head?_cons, Fl4Spec.the, ↓reduceIte]
      have hass : (Fl4Spec.NonDet.assert (xr.replySc = some sc.bv) : Fl4Spec.SMonad Unit Unit) σ =
          ({((), σ)}, False) := by
        show (({x | xr.replySc = some sc.bv ∧ x = ((), σ)}, ¬ xr.replySc = some sc.bv) :
          Set (Unit × Fl4Spec.State Unit) × Prop) = ({((), σ)}, False)
        simp [hrsc]
      rw [nd_bind_one hass]
      show (Fl4Spec.updateSchedContext sc.bv _ >>= _) σ = _
      rw [nd_bind_one (updateSchedContext_eq hk _)]
      rcases hcase with ⟨hr0, rfl⟩ | ⟨d, l, x, hr0, hkd, rfl⟩
      · subst hr0
        exact setReplySc_eq none hkra
      · subst hr0
        simp only [List.map_cons, List.tail_cons]
        have hdp : d.bv ≠ sc.bv := fun e => hnh_sc d rfl e.symm
        have hkad : σa.kheap d.bv = some (.reply x) := by rw [hka _ hdp]; exact hkd
        exact (nd_bind_one (setReplySc_eq (some sc.bv) hkad) _).trans (setReplySc_eq none hkrb)
    -- the TCB's SC word
    obtain ⟨Q3, R3, hc3, hs3⟩ := hS3.lists
    have hktc : σc.kheap t.bv = some (.tcb xt) := by
      rw [hkc _ (Ne.symm hrt), hkb _ (Ne.symm hpt) (fun d hh e => by
        obtain ⟨xd, hkd, -⟩ := hCR.reply d (hhR d hh); rw [← e, hkt] at hkd; cases hkd)]
      exact hkt
    step with obj.Tcb.sc.spec as ⟨i, hi⟩
    have hti : xt.tcbSchedContext = optRef i := by
      obtain ⟨x', hk', -, -, h3, -⟩ := hs3.tcb t ht
      rw [hktc] at hk'; cases hk'; rw [h3, hi]
    -- the memory after `PREV` of `r` (on the call-stack words)
    have hcall : ∀ (s4 : S), (∀ q ∈ C, L.mem s4 (scReplyA q) = L.mem (L.wr s2 (rNextA r) 0#u64) (scReplyA q)) →
        (∀ d ∈ R, L.mem s4 (rPrevA d) = L.mem (L.wr s2 (rNextA r) 0#u64) (rPrevA d) ∧
          L.mem s4 (rNextA d) = L.mem (L.wr s2 (rNextA r) 0#u64) (rNextA d)) →
        ∀ (σ4 : Fl4Spec.State Unit), (∀ q ∈ C, ∀ y0 n0, σc.kheap q.bv = some (.schedContext y0 n0) →
          ∃ y', σ4.kheap q.bv = some (.schedContext y' n0) ∧ y'.scReplies = y0.scReplies) →
        (∀ d ∈ R, ∀ x, σc.kheap d.bv = some (.reply x) → ∃ x', σ4.kheap d.bv = some (.reply x') ∧
          x'.replySc = x.replySc) →
        CallRel (L.mem (L.wr s4 (rPrevA r) 0#u64)) R C σ4 (Function.update Lst sc rest) ∧
          Isolated (L.mem (L.wr s4 (rPrevA r) 0#u64)) R r := by
      intro s4 cw1 cw2 σ4 hsp1 hsp2
      have hR0 : ∀ d ∈ R, d ≠ 0#u64 ∧ d.val % 2 = 0 := fun d hd => ⟨(hRP.align d hd).2.1, hev d hd⟩
      set m5 := L.mem (L.wr s4 (rPrevA r) 0#u64)
      have hm5 : ∀ b, Aligned b → b.val ≠ (rPrevA r).val → m5 b = L.mem s4 b := fun b hb h =>
        L.mem_wr_ne hPr hb (Ne.symm h)
      have hm3 : ∀ b, Aligned b → b.val ≠ (rNextA r).val → L.mem (L.wr s2 (rNextA r) 0#u64) b = L.mem s2 b :=
        fun b hb h => L.mem_wr_ne hNr hb (Ne.symm h)
      obtain ⟨hCRc, hiso⟩ := CallRel.pop (m' := m5) (σ' := σc) hCR hR0 hsc hL
        (fun d hd hdr => by
          rw [hm5 _ (hal d hd).1 ((rwords_ne (hRP.align d hd) hA).2 hdr).1, (cw2 d hd).1,
            hm3 _ (hal d hd).1 ((rwords_ne (hRP.align d hd) hA).1),
            hm2 _ (hal d hd).1 (fun e => (hfarS sc hsc d hd).1 e.symm)
              (fun e he => (rwords_ne (hRP.align d hd) (hRP.align e (hhR e he))).1)])
        (fun d hd hdr hnh => by
          rw [hm5 _ (hal d hd).2 (fun e => (rwords_ne hA (hRP.align d hd)).1 e.symm), (cw2 d hd).2,
            hm3 _ (hal d hd).2 ((rwords_ne (hRP.align d hd) hA).2 hdr).2,
            hm2 _ (hal d hd).2 (fun e => (hfarS sc hsc d hd).2 e.symm)
              (fun e he => ((rwords_ne (hRP.align d hd) (hRP.align e (hhR e he))).2
                (fun h' => hnh (h' ▸ he))).2)])
        (fun d hh => by
          have hdR := hhR d hh
          rw [hm5 _ (hal d hdR).2 (fun e => (rwords_ne hA (hRP.align d hdR)).1 e.symm), (cw2 d hdR).2,
            hm3 _ (hal d hdR).2 ((rwords_ne (hRP.align d hdR) hA).2 (hhr d hh)).2]
          exact hm2h d hh)
        (L.mem_wr_same hPr)
        (by rw [hm5 _ hNr (by rw [rNextA_val hA, rPrevA_val hA]; omega), (cw2 r hrR).2]; exact L.mem_wr_same hNr)
        (by
          rw [hm5 _ haP (fun e => (hfarS sc hsc r hrR).1 e), cw1 sc hsc,
            hm3 _ haP (fun e => (hfarS sc hsc r hrR).2 e)]
          exact hm2s)
        (fun q hq hne => by
          obtain ⟨haq, -, -⟩ := sc_reply_word hS hq
          rw [hm5 _ haq (fun e => (hfarS q hq r hrR).1 e), cw1 q hq, hm3 _ haq (fun e => (hfarS q hq r hrR).2 e),
            hm2 _ haq (hSne q hq hne) (fun e he => (hfarS q hq e (hhR e he)).2)])
        hk (by rw [hkc _ hpr]; exact hkbsc)
        (fun q hq hne => by
          have hqr : q.bv ≠ r.bv := fun e => by
            obtain ⟨xq, nq, hkq, -⟩ := hs.scs q hq; rw [e, hkr] at hkq; cases hkq
          rw [hkc _ hqr, hkb _ (bv_ne hne) (fun d hh e => by
            obtain ⟨xd, hkd, -⟩ := hCR.reply d (hhR d hh)
            obtain ⟨xq, nq, hkq, -⟩ := hs.scs q hq
            rw [e, hkd] at hkq; cases hkq)])
        hkr hkcr
        (fun d x hh hkd => by rw [hkc _ (fun e => hhr d hh (eq_of_bv e))]; exact hkbh d x hh hkd)
        (fun d hd hdr hnh => by
          have hdsc : d.bv ≠ sc.bv := fun e => by
            obtain ⟨xd, hkd, -⟩ := hCR.reply d hd; rw [e, hk] at hkd; cases hkd
          rw [hkc _ (bv_ne hdr), hkb _ hdsc (fun d' hh' e => hnh (by rw [hh', ← eq_of_bv e]))])
      exact ⟨hCRc.frame (fun q hq => rfl) (fun d hd => ⟨rfl, rfl⟩) hsp1 hsp2, hiso⟩
    by_cases hi0 : i = 0#u64
    · -- the donation back to `t`
      rw [if_pos hi0]
      have hxt0 : xt.tcbSchedContext = none := by rw [hti, hi0, optRef_zero]
      obtain ⟨f, hf, hyf, hft⟩ := hdon hxt0
      obtain ⟨xf, hkf, -⟩ := hs.tcb f hf
      have hkfc : σc.kheap f.bv = some (.tcb xf) := by
        rw [hkc _ (fun e => by rw [e, hkr] at hkf; cases hkf), hkb _ (fun e => by rw [e, hk] at hkf; cases hkf)
          (fun d hh e => by obtain ⟨xd, hkd, -⟩ := hCR.reply d (hhR d hh); rw [← e, hkf] at hkd; cases hkd)]
        exact hkf
      have hkcsc : σc.kheap sc.bv = some (.schedContext { y with scReplies := y.scReplies.tail } n) := by
        rw [hkc _ hpr]; exact hkbsc
      have hrelc : inClass xt.tcbState → Fl4Spec.scActive { y with scReplies := y.scReplies.tail } = true →
          released σc { y with scReplies := y.scReplies.tail } := fun h1 h2 => by
        have := hrel hxt0 h1 h2
        unfold released at this ⊢
        rw [show σc.curTime = σ.curTime from htmb]; exact this
      refine WP.spec_bind (donate_bound_refines _ a σc hS3 hR3 hN3 hI3 hsc hsc0 hkcsc hf hyf hkfc ht hktc hxt0 hft
        hrelc) ?_
      rintro ⟨s4, a4⟩ ⟨σ4, hdon4, ha4, hS4, hR4, hN4, hI4, hw4, hksc4, hko4, hkf4, hkt4, -, -, -⟩
      simp only at ha4
      subst ha4
      obtain ⟨cw1, cw2⟩ := callWords_of_dfoot hS3 hRP3 hsc hw4
      refine WP.spec_bind (obj.Reply.set_prev.val s4 r 0#u64) ?_
      rintro s5 rfl
      rw [zero_or_masked]
      have hSz4 : SzKeep σc σ4 := by
        intro q x' n' hq
        by_cases e : q = sc.bv
        · subst e; rw [hksc4] at hq; cases hq; exact ⟨_, hkcsc⟩
        by_cases ef : q = f.bv
        · subst ef; rw [hkf4] at hq; cases hq
        by_cases et : q = t.bv
        · subst et; rw [hkt4] at hq; cases hq
        · rw [hko4 q e ef et] at hq; exact ⟨x', hq⟩
      have hRP4 : RPlaced st N T C R c s4 σ4 := hRP3.frame hw4.1 hSz4
      have hqft : ∀ q ∈ C, q.bv ≠ f.bv ∧ q.bv ≠ t.bv := fun q hq => by
        obtain ⟨xq, nq, hkq, -⟩ := hs.scs q hq
        exact ⟨fun e => (by rw [e, hkf] at hkq; cases hkq), fun e => (by rw [e, hkt] at hkq; cases hkq)⟩
      obtain ⟨hCR5, hiso5⟩ := hcall s4 cw1 cw2 σ4
        (fun q hq y0 n0 hy0 => by
          by_cases e : q = sc
          · subst e; rw [hkcsc] at hy0; cases hy0; exact ⟨_, hksc4, rfl⟩
          · exact ⟨y0, by rw [hko4 _ (bv_ne e) (hqft q hq).1 (hqft q hq).2]; exact hy0, rfl⟩)
        (fun d hd x hx => by
          have hdsc : d.bv ≠ sc.bv := fun e => by rw [e, hkcsc] at hx; cases hx
          have hdf : d.bv ≠ f.bv := fun e => by rw [e, hkfc] at hx; cases hx
          have hdt : d.bv ≠ t.bv := fun e => by rw [e, hktc] at hx; cases hx
          exact ⟨x, by rw [hko4 _ hdsc hdf hdt]; exact hx, rfl⟩)
      refine WP.spec_bind (hU _ σ4 _ (hS4.wr_far hPr (hRP4.far hrR (Or.inl (rPrevA_val hA))) 0#u64)
        (hR4.frame hP (footEq_wr_far hP hPr (fun n hn => by have := hRP.ntfn r hrR n hn; rw [rPrevA_val hA]; omega)
          (fun t ht => by have := hRP.tcb r hrR t ht; rw [rPrevA_val hA]; omega) _) (KView.refl _))
        hN4 hI4 hCR5 (hRP4.frame (by simp) (SzKeep.of_kheap rfl)) hiso5 ?_) ?_
      · rw [nd_bind_one hunl]
        unfold Fl4Spec.NonDet.when
        rw [if_pos hxt0]; exact hdon4
      · intro s6 h6; rw [WP.spec_ok]; exact h6
    · -- no donation
      rw [if_neg hi0]
      have hxt1 : ¬ xt.tcbSchedContext = none := by rw [hti, optRef_ne hi0]; simp
      simp only [bind_ok]
      refine WP.spec_bind (obj.Reply.set_prev.val _ r 0#u64) ?_
      rintro s5 rfl
      rw [zero_or_masked]
      obtain ⟨hCR5, hiso5⟩ := hcall _ (fun q _ => rfl) (fun d _ => ⟨rfl, rfl⟩) σc
        (fun q _ y0 n0 hy0 => ⟨y0, hy0, rfl⟩) (fun d _ x hx => ⟨x, hx, rfl⟩)
      refine WP.spec_bind (hU _ σc _ (hS3.wr_far hPr (hRP3.far hrR (Or.inl (rPrevA_val hA))) 0#u64)
        (hR3.frame hP (footEq_wr_far hP hPr (fun n hn => by have := hRP.ntfn r hrR n hn; rw [rPrevA_val hA]; omega)
          (fun t ht => by have := hRP.tcb r hrR t ht; rw [rPrevA_val hA]; omega) _) (KView.refl _))
        hN3 hI3 hCR5 (hRP3.frame (by simp) (SzKeep.of_kheap rfl)) hiso5 ?_) ?_
      · rw [nd_bind_one hunl]
        unfold Fl4Spec.NonDet.when
        rw [if_neg hxt1]; rfl
      · intro s6 h6; rw [WP.spec_ok]; exact h6
  have hm1 : ∀ b, Aligned b → b.val ≠ (scReplyA sc).val → L.mem (L.wr s (scReplyA sc) (rest.headD 0#u64)) b = L.mem s b :=
    fun b hb h => L.mem_wr_ne haP hb (Ne.symm h)
  by_cases hr0 : rest = []
  · have hb : (rest.headD 0#u64 != 0#u64) = false := by rw [hr0]; rfl
    rw [hb]
    simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
    exact cont _ σa hS1 hR1 hNa hIa (by simp) (fun q hq _ => hka q hq) hkasc
      (fun d x hh => by rw [hr0] at hh; cases hh) rfl (Or.inl ⟨hr0, rfl⟩)
      (fun b hb h1 _ => hm1 b hb h1) (L.mem_wr_same haP) (fun d hh => by rw [hr0] at hh; cases hh)
  · obtain ⟨d, l, hr'⟩ := List.exists_cons_of_ne_nil hr0
    have hhd : rest.headD 0#u64 = d := by rw [hr']; rfl
    have hhh : rest.head? = some d := by rw [hr']; rfl
    have hdR : d ∈ R := hhR d hhh
    have hAd := hRP.align d hdR
    have hb : (rest.headD 0#u64 != 0#u64) = true := by rw [hhd]; simpa using hAd.2.1
    rw [hb]
    simp only [↓reduceIte]
    refine WP.spec_bind (obj.Reply.set_next_raw.spec2 _ _ (sc ||| 1#u64)) ?_
    rintro s2 rfl
    obtain ⟨xd, hkd, -⟩ := hCR.reply d hdR
    have hdsc : d.bv ≠ sc.bv := fun e => by rw [e, hk] at hkd; cases hkd
    have hkad : σa.kheap d.bv = some (.reply xd) := by rw [hka _ hdsc]; exact hkd
    have hNd : Aligned (rNextA (rest.headD 0#u64)) := by rw [hhd]; exact (hal d hdR).2
    have hRPa : RPlaced st N T C R c (L.wr s (scReplyA sc) (rest.headD 0#u64)) σa := hRP.frame (by simp) (by
      intro q x' n' hq
      by_cases e : q = sc.bv
      · subst e; rw [hkasc] at hq; cases hq; exact ⟨y, hk⟩
      · rw [hka q e] at hq; exact ⟨x', hq⟩)
    have hS2 := (hS1.wr_far hNd (by rw [show rNextA (rest.headD 0#u64) = rNextA d by rw [hhd]]; exact hRPa.far hdR (Or.inr (rNextA_val hAd))) (sc ||| 1#u64)).stableW
      (WritesIn.refl _ _) (NtfnStepW.updReply hkad { xd with replySc := some sc.bv })
    have hR2 : NtfnStateRel N T (L.mem (L.wr (L.wr s (scReplyA sc) (rest.headD 0#u64))
        (rNextA (rest.headD 0#u64)) (sc ||| 1#u64))) (updK σa d.bv (.reply { xd with replySc := some sc.bv })) :=
      hR1.frame hP (footEq_wr_far hP hNd (fun n hn => by have := hRP.ntfn d hdR n hn; rw [hhd, rNextA_val hAd]; omega)
        (fun t ht => by have := hRP.tcb d hdR t ht; rw [hhd, rNextA_val hAd]; omega) _) (KView.updReply hkad _)
    refine cont _ _ hS2 hR2 (hNa.updReply hkad _) (hIa.updReply hkad) (by simp)
      (fun q hq hne => by
        have : q ≠ d.bv := hne d hhh
        simp only [updK_kheap, Function.update_of_ne this]; exact hka q hq)
      (by simp only [updK_kheap, Function.update_of_ne (Ne.symm hdsc)]; exact hkasc)
      (fun d' x hh hkd' => by
        rw [hhh] at hh; cases hh; rw [hkd] at hkd'; cases hkd'; simp [updK])
      rfl (Or.inr ⟨d, l, xd, hr', hkd, rfl⟩)
      (fun b hb h1 h2 => by
        rw [L.mem_wr_ne hNd hb (by rw [hhd]; exact (h2 d hhh).symm)]; exact hm1 b hb h1)
      (by
        rw [L.mem_wr_ne hNd haP (by rw [hhd]; exact fun e => (hfarS sc hsc d hdR).2 e.symm)]
        exact L.mem_wr_same haP)
      (fun d' hh => by rw [hhh] at hh; cases hh; rw [← hhd]; exact L.mem_wr_same hNd)

end

end

end Fl4Proofs.P3.Sched
