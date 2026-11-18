/-
P3 (DESIGN.md §9), scheduling contexts: **`reply_remove`** against l4v
`reply_remove`'s call-stack part (`replyRemoveSc`: `sc_with_reply`,
`reply_unlink_sc`, the donation back): the head case is `reply_pop`; a
non-head reply is cut out with the older ones (`CallRel.cut`), a detached
one is spliced out (`CallRel.dsplice`). The final `reply_unlink` is the
continuation `hU` (given the relations, the call-stack step `CallStep` and
`UFrame`), as for `reply_pop_refines`; `reply_remove_full_refines`
(ScCallUnlink.lean) discharges it with `reply_unlink_refines`.
-/
import Fl4Proofs.P3.ScCallCut
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-- l4v `reply_remove` between the reply's assertion and
`reply_unlink_tcb`: the call-stack part. -/
def replyRemoveSc (caller r : ObjRef) : SMonad Unit Unit := do
  let rScOpt ← NonDet.gets (scWithReply r)
  match rScOpt with
  | none => pure ()
  | some scPtr => do
    let replies ← NonDet.liftM SchedContext.scReplies (getSchedContext scPtr)
    let callerSc ← getTcbObjRef Tcb.tcbSchedContext caller
    replyUnlinkSc scPtr r
    NonDet.when (the replies.head? = r ∧ callerSc = none) <| schedContextDonate scPtr caller

end Spec

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

theorem takeWhile_bv (Ls : List U64) (hnd : Ls.Nodup) (k : Nat) (hk : k < Ls.length) :
    (Ls.map UScalar.bv).takeWhile (fun x => decide (x ≠ Ls[k].bv)) = (Ls.take k).map UScalar.bv := by
  induction Ls generalizing k with
  | nil => simp at hk
  | cons a l ih =>
    cases k with
    | zero => simp
    | succ k =>
      have hk' : k < l.length := by simpa using hk
      have hne : a ≠ l[k] := fun e => (List.nodup_cons.1 hnd).1 (e ▸ List.getElem_mem hk')
      have hne' : a.bv ≠ l[k].bv := fun e => hne (eq_of_bv e)
      simp only [List.map_cons, List.getElem_cons_succ, List.take_succ_cons]
      rw [List.takeWhile_cons_of_pos (by simpa using hne')]
      rw [ih (List.nodup_cons.1 hnd).2 k hk']

theorem set_prev0_eq (s : S) (x : U64) : obj.Reply.set_prev st x s 0#u64 = ok (L.wr s (rPrevA x) 0#u64) := by
  unfold obj.Reply.set_prev obj.Reply.set_prev_raw
  simp only [lift, bind_ok, L.write_eq, zero_or_masked]; rfl

theorem set_next0_eq (s : S) (x : U64) : obj.Reply.set_next st x s 0#u64 false = ok (L.wr s (rNextA x) 0#u64) := by
  unfold obj.Reply.set_next obj.Reply.set_next_raw
  simp only [lift, bind_ok, L.write_eq, Bool.false_eq_true, ↓reduceIte, rz_next]; rfl

theorem even_of_bit {x : U64} (h : x &&& 1#u64 = 0#u64) : x.val % 2 = 0 := by
  have := congrArg UScalar.val h
  rw [UScalar.val_and, show (1#u64 : U64).val = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod] at this
  simpa using this


/-- A write to a reply word keeps the scheduler and notification relations
and the placement. -/
theorem rword_keep {N T C R : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hRP : RPlaced st N T C R c s σ)
    {d : U64} (hd : d ∈ R) {a : U64} (ha : a.val = d.val + 8 ∨ a.val = d.val + 16) (v : U64) :
    SchedRel st N T C c (L.wr s a v) σ ∧ NtfnStateRel N T (L.mem (L.wr s a v)) σ ∧
      RPlaced st N T C R c (L.wr s a v) σ := by
  have hal := hRP.aligned hd ha
  refine ⟨hS.wr_far hal (hRP.far hd ha) v, hR.frame hS.placed (footEq_wr_far hS.placed hal
    (fun n hn => by have := hRP.ntfn d hd n hn; omega) (fun t ht => by have := hRP.tcb d hd t ht; omega) v)
    (KView.refl _), hRP.frame (by simp) (SzKeep.of_kheap rfl)⟩

/-- **The splice of `reply_remove`**: the neighbours' links to `r` and `r`'s
own links are cleared; the call-stack relation afterwards is `hC`'s. -/
theorem splice_refines {N T C R : Set U64} {c : U64} (s : S) (a : A) (σ' : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ') (hR : NtfnStateRel N T (L.mem s) σ') (hN : NSC N C σ') (hI : Inv σ')
    (hRP : RPlaced st N T C R c s σ') {r : U64} (hr : r ∈ R) {nx pv : U64} (hnx : nx = 0#u64 ∨ nx ∈ R)
    (hpv : pv = 0#u64 ∨ pv ∈ R) (t : U64) (Q : S × A → Prop)
    {Lst' : U64 → List U64}
    (hC : ∀ m' : U64 → U64, (∀ q ∈ C, m' (scReplyA q) = L.mem s (scReplyA q)) →
      (∀ d ∈ R, d ≠ r → d ≠ nx → m' (rPrevA d) = L.mem s (rPrevA d)) →
      (∀ d ∈ R, d ≠ r → d ≠ pv → m' (rNextA d) = L.mem s (rNextA d)) →
      (nx ≠ 0#u64 → m' (rPrevA nx) = 0#u64) → (pv ≠ 0#u64 → m' (rNextA pv) = 0#u64) →
      m' (rPrevA r) = 0#u64 → m' (rNextA r) = 0#u64 → CallRel m' R C σ' Lst' ∧ Isolated m' R r)
    (hU : ∀ s4 : S, SchedRel st N T C c s4 σ' → NtfnStateRel N T (L.mem s4) σ' → NSC N C σ' → Inv σ' →
      CallRel (L.mem s4) R C σ' Lst' → RPlaced st N T C R c s4 σ' → Isolated (L.mem s4) R r →
      (∀ d ∈ R, d ≠ r → d ≠ nx → d ≠ pv →
        L.mem s4 (rNextA d) = L.mem s (rNextA d) ∧ L.mem s4 (rPrevA d) = L.mem s (rPrevA d)) →
      WritesIn st s s4 (CallW' R C) →
      ipc.reply_unlink st s4 r t ⦃ s6 => Q (s6, a) ⦄) :
    (do
      let s1 ← if nx != 0#u64 then obj.Reply.set_prev st nx s 0#u64 else ok s
      let s2 ← if pv != 0#u64 then obj.Reply.set_next st pv s1 0#u64 false else ok s1
      let s3 ← obj.Reply.set_prev st r s2 0#u64
      let s4 ← obj.Reply.set_next st r s3 0#u64 false
      let s5 ← ipc.reply_unlink st s4 r t
      ok (s5, a)) ⦃ Q ⦄ := by
  have hA := hRP.align r hr
  have hvP : ∀ d ∈ R, (rPrevA d).val = d.val + 8 := fun d hd => rPrevA_val (hRP.align d hd)
  have hvN : ∀ d ∈ R, (rNextA d).val = d.val + 16 := fun d hd => rNextA_val (hRP.align d hd)
  have hal : ∀ d ∈ R, Aligned (rPrevA d) ∧ Aligned (rNextA d) := fun d hd =>
    ⟨hRP.aligned hd (Or.inl (hvP d hd)), hRP.aligned hd (Or.inr (hvN d hd))⟩
  set s1 := if nx = 0#u64 then s else L.wr s (rPrevA nx) 0#u64 with hs1
  have e1 : (if nx != 0#u64 then obj.Reply.set_prev st nx s 0#u64 else ok s) = ok s1 := by
    by_cases h : nx = 0#u64 <;> simp [h, s1, set_prev0_eq]
  set s2 := if pv = 0#u64 then s1 else L.wr s1 (rNextA pv) 0#u64 with hs2
  have e2 : (if pv != 0#u64 then obj.Reply.set_next st pv s1 0#u64 false else ok s1) = ok s2 := by
    by_cases h : pv = 0#u64 <;> simp [h, s2, set_next0_eq]
  rw [e1]; simp only [bind_ok]; rw [e2]; simp only [bind_ok, set_prev0_eq, set_next0_eq]
  -- the relations
  have k1 : SchedRel st N T C c s1 σ' ∧ NtfnStateRel N T (L.mem s1) σ' ∧ RPlaced st N T C R c s1 σ' := by
    by_cases h : nx = 0#u64
    · simp only [s1, h, ↓reduceIte]; exact ⟨hS, hR, hRP⟩
    · simp only [s1, h, ↓reduceIte]
      exact rword_keep hS hR hRP (hnx.resolve_left h) (Or.inl (hvP _ (hnx.resolve_left h))) _
  have k2 : SchedRel st N T C c s2 σ' ∧ NtfnStateRel N T (L.mem s2) σ' ∧ RPlaced st N T C R c s2 σ' := by
    by_cases h : pv = 0#u64
    · simp only [s2, h, ↓reduceIte]; exact k1
    · simp only [s2, h, ↓reduceIte]
      exact rword_keep k1.1 k1.2.1 k1.2.2 (hpv.resolve_left h) (Or.inr (hvN _ (hpv.resolve_left h))) _
  obtain ⟨g1, g2, g3⟩ := rword_keep k2.1 k2.2.1 k2.2.2 hr (Or.inl (hvP r hr)) 0#u64
  obtain ⟨g4, g5, g6⟩ := rword_keep g1 g2 g3 hr (Or.inr (hvN r hr)) 0#u64
  -- the memory
  set s4 := L.wr (L.wr s2 (rPrevA r) 0#u64) (rNextA r) 0#u64
  have hne : ∀ b, Aligned b → b.val ≠ (rPrevA r).val → b.val ≠ (rNextA r).val →
      (nx ≠ 0#u64 → b.val ≠ (rPrevA nx).val) → (pv ≠ 0#u64 → b.val ≠ (rNextA pv).val) →
      L.mem s4 b = L.mem s b := by
    intro b hb h1 h2 h3 h4
    show L.mem (L.wr (L.wr s2 _ _) _ _) b = _
    rw [L.mem_wr_ne (hal r hr).2 hb (Ne.symm h2), L.mem_wr_ne (hal r hr).1 hb (Ne.symm h1)]
    simp only [s2, s1]
    by_cases hp : pv = 0#u64 <;> by_cases hn : nx = 0#u64 <;> simp only [hp, hn, ↓reduceIte]
    · rw [L.mem_wr_ne (hal nx (hnx.resolve_left hn)).1 hb (Ne.symm (h3 hn))]
    · rw [L.mem_wr_ne (hal pv (hpv.resolve_left hp)).2 hb (Ne.symm (h4 hp))]
    · rw [L.mem_wr_ne (hal pv (hpv.resolve_left hp)).2 hb (Ne.symm (h4 hp)),
        L.mem_wr_ne (hal nx (hnx.resolve_left hn)).1 hb (Ne.symm (h3 hn))]
  have hwd : ∀ d d' : U64, d ∈ R → d' ∈ R → d ≠ d' →
      (rPrevA d).val ≠ (rPrevA d').val ∧ (rNextA d).val ≠ (rNextA d').val := fun d d' hd hd' h =>
    (rwords_ne (hRP.align d hd) (hRP.align d' hd')).2 h
  have hpn : ∀ d d' : U64, d ∈ R → d' ∈ R → (rPrevA d).val ≠ (rNextA d').val := fun d d' hd hd' =>
    (rwords_ne (hRP.align d hd) (hRP.align d' hd')).1
  have hfarS : ∀ q ∈ C, ∀ d ∈ R, (scReplyA q).val ≠ (rPrevA d).val ∧ (scReplyA q).val ≠ (rNextA d).val := by
    intro q hq d hd
    obtain ⟨-, hvq, hszq⟩ := sc_reply_word hS hq
    obtain ⟨Q0, R0, hc, hs⟩ := hS.lists
    obtain ⟨xq, nq, hkq, -⟩ := hs.scs q hq
    have := hRP.sc d hd q hq xq nq hkq; have := hszq xq nq hkq
    rw [hvq, hvP d hd, hvN d hd]; omega
  have hPr0 : L.mem s4 (rPrevA r) = 0#u64 := by
    show L.mem (L.wr (L.wr s2 _ _) _ _) _ = _
    rw [L.mem_wr_ne (hal r hr).2 (hal r hr).1 (fun e => hpn r r hr hr e.symm)]
    exact L.mem_wr_same (hal r hr).1
  have hNr0 : L.mem s4 (rNextA r) = 0#u64 := L.mem_wr_same (hal r hr).2
  have hPs : ∀ d ∈ R, d ≠ r → d ≠ nx → L.mem s4 (rPrevA d) = L.mem s (rPrevA d) :=
    fun d hd h1 h2 => hne _ (hal d hd).1 (hwd d r hd hr h1).1 (hpn d r hd hr)
      (fun h => (hwd d nx hd (hnx.resolve_left h) h2).1) (fun h => hpn d pv hd (hpv.resolve_left h))
  have hNs : ∀ d ∈ R, d ≠ r → d ≠ pv → L.mem s4 (rNextA d) = L.mem s (rNextA d) :=
    fun d hd h1 h2 => hne _ (hal d hd).2 (fun e => hpn r d hr hd e.symm) (hwd d r hd hr h1).2
      (fun h => fun e => hpn nx d (hnx.resolve_left h) hd e.symm) (fun h => (hwd d pv hd (hpv.resolve_left h) h2).2)
  obtain ⟨hCR, hiso⟩ := hC (L.mem s4)
    (fun q hq => by
      obtain ⟨haq, -, -⟩ := sc_reply_word hS hq
      exact hne _ haq (hfarS q hq r hr).1 (hfarS q hq r hr).2 (fun h => (hfarS q hq nx (hnx.resolve_left h)).1)
        (fun h => (hfarS q hq pv (hpv.resolve_left h)).2))
    hPs hNs
    (fun h => by
      have hR' := hnx.resolve_left h
      by_cases hnxr : nx = r
      · rw [hnxr]; exact hPr0
      show L.mem (L.wr (L.wr s2 _ _) _ _) _ = _
      rw [L.mem_wr_ne (hal r hr).2 (hal nx hR').1 (fun e => hpn nx r hR' hr e.symm),
        L.mem_wr_ne (hal r hr).1 (hal nx hR').1 (fun e => (hwd nx r hR' hr hnxr).1 e.symm)]
      simp only [s2, s1, h, ↓reduceIte]
      by_cases hp : pv = 0#u64
      · simp only [hp, ↓reduceIte]; exact L.mem_wr_same (hal nx hR').1
      · simp only [hp, ↓reduceIte]
        rw [L.mem_wr_ne (hal pv (hpv.resolve_left hp)).2 (hal nx hR').1
          (fun e => hpn nx pv hR' (hpv.resolve_left hp) e.symm)]
        exact L.mem_wr_same (hal nx hR').1)
    (fun h => by
      have hR' := hpv.resolve_left h
      by_cases hpvr : pv = r
      · rw [hpvr]; exact hNr0
      show L.mem (L.wr (L.wr s2 _ _) _ _) _ = _
      rw [L.mem_wr_ne (hal r hr).2 (hal pv hR').2 (fun e => (hwd pv r hR' hr hpvr).2 e.symm),
        L.mem_wr_ne (hal r hr).1 (hal pv hR').2 (hpn r pv hr hR')]
      simp only [s2, h, ↓reduceIte]
      exact L.mem_wr_same (hal pv hR').2)
    hPr0 hNr0
  have cw : ∀ {s0 : S} {a : U64} {v : U64}, Aligned a → CallW' R C a → WritesIn st s0 (L.wr s0 a v) (CallW' R C) :=
    fun ha hc => (writesIn_wr ha).mono fun b hb => hb ▸ hc
  have tr : ∀ {x y z : S}, WritesIn st x y (CallW' R C) → WritesIn st y z (CallW' R C) → WritesIn st x z (CallW' R C) :=
    fun h1 h2 => (h1.trans h2).mono fun b hb => hb.elim id id
  have w1 : WritesIn st s s1 (CallW' R C) := by
    by_cases h : nx = 0#u64
    · simp only [s1, h, ↓reduceIte]; exact WritesIn.refl _ _
    · simp only [s1, h, ↓reduceIte]
      exact cw (hal nx (hnx.resolve_left h)).1 (Or.inl ⟨nx, hnx.resolve_left h, Or.inr rfl⟩)
  have w2 : WritesIn st s1 s2 (CallW' R C) := by
    by_cases h : pv = 0#u64
    · simp only [s2, h, ↓reduceIte]; exact WritesIn.refl _ _
    · simp only [s2, h, ↓reduceIte]
      exact cw (hal pv (hpv.resolve_left h)).2 (Or.inl ⟨pv, hpv.resolve_left h, Or.inl rfl⟩)
  have hw4 : WritesIn st s s4 (CallW' R C) :=
    tr (tr w1 w2) (tr (cw (hal r hr).1 (Or.inl ⟨r, hr, Or.inr rfl⟩))
      (cw (hal r hr).2 (Or.inl ⟨r, hr, Or.inl rfl⟩)))
  refine WP.spec_bind (hU _ g4 g5 hN hI hCR g6 hiso
    (fun d hd h1 h2 h3 => ⟨hNs d hd h1 h3, hPs d hd h1 h2⟩) hw4) ?_
  intro s6 h6; exact (WP.spec_ok _).mpr h6


theorem headBit_or1 (x : U64) : headBit (x ||| 1#u64) = true := by
  have e1 : ((x ||| 1#u64) &&& 1#u64).bv.getLsbD 0 = true := by
    simp only [UScalar.bv_and, UScalar.bv_or, BitVec.getLsbD_and, BitVec.getLsbD_or, one_bit]; simp
  unfold headBit
  by_cases h : (x ||| 1#u64) &&& 1#u64 = 0#u64
  · rw [h] at e1; simp at e1
  · simp [h]

theorem headBit_even {x : U64} (h : x.val % 2 = 0) : headBit x = false := by
  unfold headBit; simp [reply_bit' h]

/-- The spec's `sc_replies` changed with no memory write. -/
theorem SchedRel.set_replies {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {sc : U64} (hsc : sc ∈ C) {x : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap sc.bv = some (.schedContext x n)) (l : List Fl4Spec.ObjRef) :
    SchedRel st N T C c s (updSc σ sc.bv { x with scReplies := l } n) := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x', n', hk', hx⟩ := hs.scs sc hsc
  rw [hk] at hk'; cases hk'
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hx
  exact hS.sc_updateW hsc hk (WritesIn.refl _ _) rfl _ ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, fun h => by
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := a12 h
    exact ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩⟩

theorem nd_when_false' {σ' : Type} {P : Prop} [Decidable P] (h : ¬ P) (m : Fl4Spec.NonDet σ' Unit) :
    Fl4Spec.NonDet.when P m = pure () := by
  unfold Fl4Spec.NonDet.when; rw [ite_eq_right h]; rfl

theorem nd_when_congr {σ' : Type} {P P' : Prop} [Decidable P] [Decidable P'] (h : P ↔ P')
    (m : Fl4Spec.NonDet σ' Unit) : Fl4Spec.NonDet.when P m = Fl4Spec.NonDet.when P' m := by
  unfold Fl4Spec.NonDet.when
  by_cases hp : P
  · rw [ite_eq_left hp, ite_eq_left (h.1 hp)]
  · rw [ite_eq_right hp, ite_eq_right (mt h.2 hp)]

/-- **`reply_remove`'s call-stack part against l4v**: the head of a stack is
popped (`reply_pop`, with the donation back), a reply further down is cut out
with the older ones, and a detached one is spliced out of its chain.  `hU` is
the final `reply_unlink` (`reply_unlink_tcb` on the spec side), given the
relations, the reply isolated, and the spec's `replyRemoveSc`.  `hdon`: the
popped reply's SC goes back bound to another thread of `T`, or bound to none
(its thread deleted while the caller waited). -/
theorem reply_remove_refinesU {N T C R : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    {Lst : U64 → List U64} (hCR : CallRel (L.mem s) R C σ Lst) (hRP : RPlaced st N T C R c s σ)
    (hC0 : ∀ q ∈ C, q ≠ 0#u64)
    (hSCs : ∀ p y n, σ.kheap p = some (.schedContext y n) → ∃ q ∈ C, q.bv = p)
    {r : U64} (hr : r ∈ R) {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hdon : ∀ sc ∈ C, ∀ y n, σ.kheap sc.bv = some (.schedContext y n) → (Lst sc).head? = some r →
      xt.tcbSchedContext = none → (∃ f, f ∈ T ∧ y.scTcb = some f.bv ∧ f ≠ t) ∨ y.scTcb = none)
    (hrel : ∀ sc ∈ C, ∀ y n, σ.kheap sc.bv = some (.schedContext y n) → (Lst sc).head? = some r →
      xt.tcbSchedContext = none → inClass xt.tcbState → Fl4Spec.scActive y = true → released σ y)
    (Q : S × A → Prop)
    (hU : ∀ (s5 : S) (σ5 : Fl4Spec.State Unit) (Lst5 : U64 → List U64),
      SchedRel st N T C c s5 σ5 → NtfnStateRel N T (L.mem s5) σ5 → NSC N C σ5 → Inv σ5 →
      CallRel (L.mem s5) R C σ5 Lst5 → RPlaced st N T C R c s5 σ5 → Isolated (L.mem s5) R r → UFrame σ σ5 →
      CallStep (L.mem s) (L.mem s5) R C Lst Lst5 r →
      replyRemoveSc t.bv r.bv σ = ({((), σ5)}, False) →
      WritesIn st s s5 (fun b => KFoot st T N C c s σ b ∨ CallW' R C b) →
      ipc.reply_unlink st s5 r t ⦃ s6 => Q (s6, a) ⦄) :
    ipc.reply_remove st ar s a r t ⦃ Q ⦄ := by
  have hev : ∀ d ∈ R, d.val % 2 = 0 := fun d hd => by have := (hRP.align d hd).1; omega
  have hR0 : ∀ d ∈ R, d ≠ 0#u64 := fun d hd => (hRP.align d hd).2.1
  obtain ⟨xr, hkr, hxr⟩ := hCR.reply r hr
  have hscs_eq : ∀ q ∈ C, ∀ y n, σ.kheap q.bv = some (.schedContext y n) → y.scReplies = (Lst q).map UScalar.bv := by
    intro q hq y n hk
    obtain ⟨⟨y0, n0, hk0, hy0⟩, -⟩ := hCR.stack q hq
    rw [hk] at hk0; cases hk0; exact hy0
  have hmemb : ∀ q ∈ C, ∀ y n, σ.kheap q.bv = some (.schedContext y n) → (r.bv ∈ y.scReplies ↔ r ∈ Lst q) := by
    intro q hq y n hk
    rw [hscs_eq q hq y n hk, List.mem_map]
    exact ⟨fun ⟨d, hd, e⟩ => (eq_of_bv e) ▸ hd, fun h => ⟨r, h, rfl⟩⟩
  by_cases hlive : ∃ sc ∈ C, r ∈ Lst sc
  · obtain ⟨sc, hsc, hrL⟩ := hlive
    obtain ⟨⟨y, n, hk, hyL⟩, hLR, hLnd, hLw⟩ := hCR.stack sc hsc
    have hwr : Fl4Spec.scWithReply r.bv σ = some sc.bv := scWithReply_some fun q =>
      ⟨fun ⟨y', n', hq, hm⟩ => by
        obtain ⟨q', hq', rfl⟩ := hSCs q y' n' hq
        rw [hCR.excl q' hq' sc hsc r ((hmemb q' hq' y' n' hq).1 hm) hrL],
       fun e => by subst e; exact ⟨y, n, hk, (hmemb sc hsc y n hk).2 hrL⟩⟩
    have hsc2 : sc.val % 2 = 0 := by
      obtain ⟨Q0, R0, hc, hs⟩ := hS.lists
      obtain ⟨x, n', -, hx⟩ := hs.scs sc hsc
      have := hx.bounds.1; omega
    obtain ⟨k, hkl, e⟩ := List.getElem_of_mem hrL
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · -- the head: `reply_pop`
      obtain ⟨rest, hL⟩ : ∃ rest, Lst sc = r :: rest := by
        cases hLs : Lst sc with
        | nil => simp [hLs] at hkl
        | cons d rest => refine ⟨rest, ?_⟩; simp only [hLs, List.getElem_cons_zero] at e; rw [e]
      have hhd : (Lst sc).head? = some r := by rw [hL]; rfl
      have hrem : replyRemoveSc t.bv r.bv σ =
          (do
            Fl4Spec.replyUnlinkSc (Z := Unit) sc.bv r.bv
            Fl4Spec.NonDet.when (xt.tcbSchedContext = none) (Fl4Spec.schedContextDonate (Z := Unit) sc.bv t.bv) :
            Fl4Spec.SMonad Unit Unit) σ := by
        unfold replyRemoveSc
        rw [nd_gets_bind, hwr]
        dsimp only
        rw [nd_bind_one (nd_liftM_one (getSchedContext_eq hk) _),
          nd_bind_one (Fl4Proofs.P3.Endp.getTcbObjRef_eq _ hkt), hyL, hL]
        rw [nd_when_congr (P' := xt.tcbSchedContext = none) (by simp [Fl4Spec.the])]
      have hm0 := (hLw.2 0 (by omega)).2
      simp only [e] at hm0
      unfold ipc.reply_remove
      step with obj.Reply.next.spec as ⟨nx, hnx⟩
      have hnx' : nx = sc := by rw [hnx, hm0]; exact or1_and_not1 _ hsc2
      clear hnx; subst nx
      step with obj.Reply.prev.spec as ⟨pv, hpv⟩
      have hnz : (sc != 0#u64) = true := by simp [hC0 sc hsc]
      simp only [hnz, ↓reduceIte]
      refine WP.spec_bind (obj.Reply.next_is_head.spec s r) ?_
      rintro b rfl
      rw [hm0, headBit_or1]; simp only [↓reduceIte]
      exact reply_pop_refines s a σ hS hR hN hI hCR hRP hsc (hC0 sc hsc) hk hL ht hkt
        (hdon sc hsc y n hk hhd) (hrel sc hsc y n hk hhd) Q
        (fun s5 σ5 Lst5 h1 h2 h3 h4 h5 h6 h7 hu hcs hsp hw => hU s5 σ5 Lst5 h1 h2 h3 h4 h5 h6 h7 hu hcs (hrem.trans hsp) hw)
    · -- further down: cut out with the older replies
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      subst e
      have hjl : j < (Lst sc).length := by omega
      have hmL : ∀ i (hi : i < (Lst sc).length), (Lst sc)[i] ∈ R := fun i hi => hLR _ (List.getElem_mem hi)
      have hne0j : (Lst sc)[0] ≠ (Lst sc)[j + 1] := fun h => by
        have := nodup_idx hLnd (by omega) hkl h; omega
      have hnej : (Lst sc)[j] ≠ (Lst sc)[j + 1] := fun h => by
        have := nodup_idx hLnd hjl hkl h; omega
      obtain ⟨hp, hn⟩ := hLw.2 (j + 1) hkl
      dsimp only at hn
      rw [List.getD_eq_getElem _ _ hjl] at hn
      have hpvE : ((Lst sc).getD (j + 2) 0#u64 = 0#u64 ∨ (Lst sc).getD (j + 2) 0#u64 ∈ R) ∧
          (∀ h : j + 2 < (Lst sc).length, (Lst sc).getD (j + 2) 0#u64 = (Lst sc)[j + 2]) ∧
          ((Lst sc).getD (j + 2) 0#u64 ≠ 0#u64 → j + 2 < (Lst sc).length) := by
        by_cases hlt : j + 2 < (Lst sc).length
        · rw [List.getD_eq_getElem _ _ hlt]
          exact ⟨Or.inr (hmL _ hlt), fun _ => rfl, fun _ => hlt⟩
        · rw [List.getD_eq_default _ _ (by omega)]
          exact ⟨Or.inl rfl, fun h => absurd h hlt, fun h => absurd rfl h⟩
      have hpvEv : ((Lst sc).getD (j + 2) 0#u64).val % 2 = 0 := by
        rcases hpvE.1 with h | h
        · rw [h]; rfl
        · exact hev _ h
      -- the spec side
      set σ' := updSc σ sc.bv { y with scReplies := ((Lst sc).take (j + 1)).map UScalar.bv } n with hσ'
      have hhd : (Lst sc).head? = some (Lst sc)[0] := by
        rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
      have hrsc0 : xr.replySc = none := by
        cases h : xr.replySc with
        | none => rfl
        | some p =>
          obtain ⟨sc', hsc', -, hh⟩ := (hxr p).1 h
          have hsc'e := hCR.excl sc' hsc' sc hsc _ (List.mem_of_mem_head? hh) hrL
          subst hsc'e
          exact (hne0j (Option.some.inj (hhd.symm.trans hh))).elim
      have hnh : ¬ (Fl4Spec.the ((Lst sc).map UScalar.bv).head? = (Lst sc)[j + 1].bv) := by
        rw [List.head?_map, hhd]
        simp only [Option.map_some, Fl4Spec.the]
        exact fun h => hne0j (eq_of_bv h)
      have hunl : Fl4Spec.replyUnlinkSc (Z := Unit) sc.bv (Lst sc)[j + 1].bv σ = ({((), σ')}, False) := by
        unfold Fl4Spec.replyUnlinkSc
        rw [nd_bind_one (nd_liftM_one (getSchedContext_eq hk) _), nd_bind_one (Fl4Proofs.P3.Endp.getReply_eq hkr),
          hyL, ite_eq_right hnh]
        have hass : (Fl4Spec.NonDet.assert (xr.replySc = none) : Fl4Spec.SMonad Unit Unit) σ =
            ({((), σ)}, False) := by
          show (({x | xr.replySc = none ∧ x = ((), σ)}, ¬ xr.replySc = none) :
            Set (Unit × Fl4Spec.State Unit) × Prop) = ({((), σ)}, False)
          simp [hrsc0]
        rw [nd_bind_one hass, updateSchedContext_eq hk]
        simp only [σ', Fl4Spec.scRepliesUpdate, hyL, takeWhile_bv _ hLnd _ hkl]
      have hrem : replyRemoveSc t.bv (Lst sc)[j + 1].bv σ = ({((), σ')}, False) := by
        unfold replyRemoveSc
        rw [nd_gets_bind, hwr]
        dsimp only
        rw [nd_bind_one (nd_liftM_one (getSchedContext_eq hk) _),
          nd_bind_one (Fl4Proofs.P3.Endp.getTcbObjRef_eq _ hkt), nd_bind_one hunl, hyL,
          nd_when_false' (fun h => hnh h.1)]
        rfl
      have hkσ' : σ'.kheap sc.bv = some (.schedContext { y with scReplies := ((Lst sc).take (j + 1)).map UScalar.bv } n) := by
        simp [σ', updK]
      have hko : ∀ q, q ≠ sc.bv → σ'.kheap q = σ.kheap q := fun q hq => by simp [σ', updK, hq]
      have hS' := hS.set_replies hsc hk (((Lst sc).take (j + 1)).map UScalar.bv)
      have hR' : NtfnStateRel N T (L.mem s) σ' := hR.frame hS.placed (fun _ _ _ => rfl) (KView.of_sc hk)
      have hRP' : RPlaced st N T C R c s σ' :=
        hRP.frame rfl (SzKeep.updK hk fun x n' h => by cases h; exact ⟨y, rfl⟩)
      -- the implementation
      unfold ipc.reply_remove
      step with obj.Reply.next.spec as ⟨nx, hnx⟩
      have hnx' : nx = (Lst sc)[j] := by rw [hnx, hn]; exact and_not1 _ (hev _ (hmL _ hjl))
      clear hnx; subst nx
      step with obj.Reply.prev.spec as ⟨pv, hpv⟩
      have hpv' : pv = (Lst sc).getD (j + 2) 0#u64 := by rw [hpv, hp]; exact and_not1 _ hpvEv
      clear hpv; subst pv
      have H := splice_refines s a σ' hS' hR' hN.updSc (hI.scFields hk rfl rfl rfl rfl) hRP' (hmL _ hkl)
        (Or.inr (hmL _ hjl)) hpvE.1 t Q
        (Lst' := Function.update Lst sc ((Lst sc).take (j + 1)))
        (fun m' hmS hmP hmN hmPn hmNp hmPr hmNr =>
          CallRel.cut (m' := m') (k := j + 1) hCR hR0 hev hsc (by omega) hkl hmS
            (fun d hd h1 h2 => hmP d hd h1 h2)
            (fun d hd h1 h2 => hmN d hd h1 fun e => by
              by_cases hlt : j + 2 < (Lst sc).length
              · rw [hpvE.2.1 hlt] at e; exact h2 hlt e
              · rw [List.getD_eq_default _ _ (by omega)] at e; exact hR0 d hd e)
            (hmPn (hR0 _ (hmL _ hjl)))
            (fun h => by rw [← hpvE.2.1 h]; exact hmNp (by rw [hpvE.2.1 h]; exact hR0 _ (hmL _ h)))
            hmPr hmNr hk hkσ' hko)
        (fun s4 h1 h2 h3 h4 h5 h6 h7 hm hw4 => hU s4 σ' _ h1 h2 h3 h4 h5 h6 h7 (UFrame.updSc hk) ⟨fun d hd hdet _ _ hdr => hm d hd hdr
          (fun e => hdet sc hsc (e ▸ List.getElem_mem hjl)) (fun e => by
            by_cases hlt : j + 2 < (Lst sc).length
            · rw [hpvE.2.1 hlt] at e; exact hdet sc hsc (e ▸ List.getElem_mem hlt)
            · rw [List.getD_eq_default _ _ (by omega)] at e; exact hR0 d hd e),
          fun q hq d hdq => by
            by_cases e : q = sc
            · subst e; simp only [Function.update_self] at hdq; exact List.mem_of_mem_take hdq
            · simpa [e] using hdq,
          fun q hq hdq => by
            by_cases e : q = sc
            · subst e; simp only [Function.update_self] at hdq
              obtain ⟨i, hi, hie⟩ := List.getElem_of_mem hdq
              rw [List.getElem_take] at hie
              have := nodup_idx hLnd (by simp at hi; omega) hkl hie
              simp at hi; omega
            · simp only [ne_eq, e, not_false_eq_true, Function.update_of_ne] at hdq
              exact e (hCR.excl q hq sc hsc _ hdq (List.getElem_mem hkl))⟩ hrem (hw4.mono fun _ h => Or.inr h))
      have hnz : ((Lst sc)[j] != 0#u64) = true := by simp [hR0 _ (hmL _ hjl)]
      simp only [hnz, ↓reduceIte] at H ⊢
      refine WP.spec_bind (obj.Reply.next_is_head.spec s _) ?_
      rintro b rfl
      rw [hn, headBit_even (hev _ (hmL _ hjl))]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact H
  · -- detached: spliced out of its chain
    have hdet : Detached C Lst r := fun q hq h => hlive ⟨q, hq, h⟩
    obtain ⟨t1, t2, t3⟩ := hCR.det r hr hdet
    have hrem : replyRemoveSc t.bv r.bv σ = ({((), σ)}, False) := by
      unfold replyRemoveSc
      rw [nd_gets_bind, scWithReply_none fun q y n hq hm => by
        obtain ⟨q', hq', rfl⟩ := hSCs q y n hq
        exact hdet q' hq' ((hmemb q' hq' y n hq).1 hm)]
      rfl
    unfold ipc.reply_remove
    step with obj.Reply.next.spec as ⟨nx, hnx⟩
    have hnx' : nx = L.mem s (rNextA r) := by rw [hnx]; exact and_not1 _ (even_of_bit t1)
    clear hnx; subst nx
    step with obj.Reply.prev.spec as ⟨pv, hpv⟩
    have hpv' : pv = L.mem s (rPrevA r) := by
      rw [hpv]
      by_cases h0 : L.mem s (rPrevA r) = 0#u64
      · rw [h0]; rfl
      · exact and_not1 _ (hev _ (t3 h0).1)
    clear hpv; subst pv
    have hnxR : L.mem s (rNextA r) = 0#u64 ∨ L.mem s (rNextA r) ∈ R := by
      by_cases h0 : L.mem s (rNextA r) = 0#u64
      · exact Or.inl h0
      · exact Or.inr (t2 h0).1
    have hpvR : L.mem s (rPrevA r) = 0#u64 ∨ L.mem s (rPrevA r) ∈ R := by
      by_cases h0 : L.mem s (rPrevA r) = 0#u64
      · exact Or.inl h0
      · exact Or.inr (t3 h0).1
    have H := splice_refines s a σ hS hR hN hI hRP hr hnxR hpvR t Q (Lst' := Lst)
      (fun m' hmS hmP hmN hmPn hmNp hmPr hmNr =>
        CallRel.dsplice (m' := m') hCR hR0 hev hr hdet hmS hmP hmN hmPn hmNp hmPr hmNr)
      (fun s4 h1 h2 h3 h4 h5 h6 h7 hm hw4 => hU s4 σ Lst h1 h2 h3 h4 h5 h6 h7 (UFrame.refl σ)
        ⟨fun d hd hdet hn0 hp0 hdr => hm d hd hdr (fun e => by
            have h0 : L.mem s (rNextA r) ≠ 0#u64 := fun h => hR0 d hd (e.trans h)
            have := (t2 h0).2.2; rw [← e] at this; rw [hp0] at this; exact hR0 r hr this.symm)
          (fun e => by
            have h0 : L.mem s (rPrevA r) ≠ 0#u64 := fun h => hR0 d hd (e.trans h)
            have := (t3 h0).2.2; rw [← e] at this; rw [hn0] at this; exact hR0 r hr this.symm),
          fun q _ d hdq => hdq, hdet⟩ hrem (hw4.mono fun _ h => Or.inr h))
    by_cases hz : L.mem s (rNextA r) = 0#u64
    · have hb : (L.mem s (rNextA r) != 0#u64) = false := by simp [hz]
      simp only [hb, Bool.false_eq_true, ↓reduceIte] at H ⊢
      exact H
    · have hb : (L.mem s (rNextA r) != 0#u64) = true := by simp [hz]
      simp only [hb, ↓reduceIte] at H ⊢
      refine WP.spec_bind (obj.Reply.next_is_head.spec s _) ?_
      rintro b rfl
      rw [headBit_even (even_of_bit t1)]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact H

/-- **`reply_remove`'s call-stack part against l4v**, the popped reply's SC
going back bound to another thread (`reply_remove_refinesU`). -/
theorem reply_remove_refines {N T C R : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    {Lst : U64 → List U64} (hCR : CallRel (L.mem s) R C σ Lst) (hRP : RPlaced st N T C R c s σ)
    (hC0 : ∀ q ∈ C, q ≠ 0#u64)
    (hSCs : ∀ p y n, σ.kheap p = some (.schedContext y n) → ∃ q ∈ C, q.bv = p)
    {r : U64} (hr : r ∈ R) {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hdon : ∀ sc ∈ C, ∀ y n, σ.kheap sc.bv = some (.schedContext y n) → (Lst sc).head? = some r →
      xt.tcbSchedContext = none → ∃ f, f ∈ T ∧ y.scTcb = some f.bv ∧ f ≠ t)
    (hrel : ∀ sc ∈ C, ∀ y n, σ.kheap sc.bv = some (.schedContext y n) → (Lst sc).head? = some r →
      xt.tcbSchedContext = none → inClass xt.tcbState → Fl4Spec.scActive y = true → released σ y)
    (Q : S × A → Prop)
    (hU : ∀ (s5 : S) (σ5 : Fl4Spec.State Unit) (Lst5 : U64 → List U64),
      SchedRel st N T C c s5 σ5 → NtfnStateRel N T (L.mem s5) σ5 → NSC N C σ5 → Inv σ5 →
      CallRel (L.mem s5) R C σ5 Lst5 → RPlaced st N T C R c s5 σ5 → Isolated (L.mem s5) R r → UFrame σ σ5 →
      CallStep (L.mem s) (L.mem s5) R C Lst Lst5 r →
      replyRemoveSc t.bv r.bv σ = ({((), σ5)}, False) →
      WritesIn st s s5 (fun b => KFoot st T N C c s σ b ∨ CallW' R C b) →
      ipc.reply_unlink st s5 r t ⦃ s6 => Q (s6, a) ⦄) :
    ipc.reply_remove st ar s a r t ⦃ Q ⦄ :=
  reply_remove_refinesU s a σ hS hR hN hI hCR hRP hC0 hSCs hr ht hkt
    (fun sc hsc y n h1 h2 h3 => Or.inl (hdon sc hsc y n h1 h2 h3)) hrel Q hU

end

end

end Fl4Proofs.P3.Sched
