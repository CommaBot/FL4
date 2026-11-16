/-
P3 (DESIGN.md §9), scheduling contexts: **`reply_remove_tcb`'s call-stack
part** (`cancel_ipc` of a thread blocked on its reply: Suspend, Resume,
finalisation) against l4v `reply_remove_tcb` before `reply_unlink_tcb`
(`replyRemoveTcbSc`: `sc_with_reply`, the stack cut at the reply,
`takeWhile (≠ r)`, the reply's `reply_sc` cleared; no donation).

FL4's side (`rrtCut`, `reply_remove_tcb` before `reply_unlink`): a head reply
leaves its SC with no stack (`Sc.set_reply 0`, `CallRel.cut0`); a reply
further down is cut out with the older ones (`CallRel.cut`); a detached one is
spliced out (`CallRel.dsplice`); the reply's own links are cleared
(`splice_post`).

* `reply_remove_tcb_sc_refines`: the relations after (`SchedRel`,
  `NtfnStateRel`, `NSC`, `Inv`, `CallRel`, `RPlaced`, `RFree`), the reply
  isolated, `UFrame`, and the writes in the call-stack words.
-/
import Fl4Proofs.P3.ScCallRemove
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-- l4v `reply_remove_tcb` between the thread-state assertion and
`reply_unlink_tcb`: the call-stack part. -/
def replyRemoveTcbSc (rptr : ObjRef) : SMonad Unit Unit := do
  let scPtrOpt ← NonDet.gets (scWithReply rptr)
  match scPtrOpt with
  | none => pure ()
  | some scPtr => do
    let scReplies ← NonDet.liftM SchedContext.scReplies (getSchedContext scPtr)
    let replySc ← getReplyObjRef Reply.replySc rptr
    NonDet.assert (if the scReplies.head? = rptr then replySc = some scPtr else replySc = none)
    updateSchedContext scPtr (scRepliesUpdate (List.takeWhile fun r => decide (r ≠ rptr)))
    setReplyObjRef replyScUpdate rptr none

theorem getReplySc_eq {σ : State Unit} {p : ObjRef} {x : Reply} (hk : σ.kheap p = some (.reply x)) :
    getReplyObjRef (Z := Unit) Reply.replySc p σ = ({(x.replySc, σ)}, False) := by
  show getSkObjRef KernelObject.reply Reply.replySc p σ = _
  unfold getSkObjRef
  rw [nd_bind_one (Fl4Proofs.P3.Endp.getReply_eq hk)]; rfl

theorem nd_assert_true {P : Prop} (h : P) (σ : State Unit) :
    (NonDet.assert P : SMonad Unit Unit) σ = ({((), σ)}, False) := by
  show (({x | P ∧ x = ((), σ)}, ¬ P) : Set (Unit × State Unit) × Prop) = ({((), σ)}, False)
  simp [h]

/-- A step changing only a reply's `reply_sc`. -/
theorem UFrame.updReplySc {σ : State Unit} {r : ObjRef} {x : Reply} (hk : σ.kheap r = some (.reply x))
    (v : Option ObjRef) : UFrame σ (updK σ r (.reply { x with replySc := v })) := by
  refine ⟨fun q x' hq => ?_, fun q x' hq => ⟨x', ?_, rfl⟩⟩
  · by_cases e : q = r
    · subst e; rw [hk] at hq; cases hq; exact ⟨{ x with replySc := v }, by simp [updK], rfl⟩
    · exact ⟨x', by simp [updK, e, hq], rfl⟩
  · have : q ≠ r := by rintro rfl; rw [hk] at hq; cases hq
    simp [updK, this, hq]

end Spec

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **The splice of a reply** (`splice_refines` without the continuation): the
neighbours' links to `r` and `r`'s own links are cleared; the call-stack
relation afterwards is `hC`'s. -/
theorem splice_post {N T C R : Set U64} {c : U64} (s : S) (σ' : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ') (hR : NtfnStateRel N T (L.mem s) σ')
    (hRP : RPlaced st N T C R c s σ') {r : U64} (hr : r ∈ R) {nx pv : U64} (hnx : nx = 0#u64 ∨ nx ∈ R)
    (hpv : pv = 0#u64 ∨ pv ∈ R)
    {Lst' : U64 → List U64}
    (hC : ∀ m' : U64 → U64, (∀ q ∈ C, m' (scReplyA q) = L.mem s (scReplyA q)) →
      (∀ d ∈ R, d ≠ r → d ≠ nx → m' (rPrevA d) = L.mem s (rPrevA d)) →
      (∀ d ∈ R, d ≠ r → d ≠ pv → m' (rNextA d) = L.mem s (rNextA d)) →
      (nx ≠ 0#u64 → m' (rPrevA nx) = 0#u64) → (pv ≠ 0#u64 → m' (rNextA pv) = 0#u64) →
      m' (rPrevA r) = 0#u64 → m' (rNextA r) = 0#u64 → CallRel m' R C σ' Lst' ∧ Isolated m' R r) :
    (do
      let s1 ← if nx != 0#u64 then obj.Reply.set_prev st nx s 0#u64 else ok s
      let s2 ← if pv != 0#u64 then obj.Reply.set_next st pv s1 0#u64 false else ok s1
      let s3 ← obj.Reply.set_prev st r s2 0#u64
      obj.Reply.set_next st r s3 0#u64 false) ⦃ s4 =>
      SchedRel st N T C c s4 σ' ∧ NtfnStateRel N T (L.mem s4) σ' ∧ RPlaced st N T C R c s4 σ' ∧
      CallRel (L.mem s4) R C σ' Lst' ∧ Isolated (L.mem s4) R r ∧
      (∀ d ∈ R, d ≠ r → d ≠ nx → d ≠ pv →
        L.mem s4 (rNextA d) = L.mem s (rNextA d) ∧ L.mem s4 (rPrevA d) = L.mem s (rPrevA d)) ∧
      WritesIn st s s4 (CallW' R C) ⦄ := by
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
  rw [WP.spec_ok]
  exact ⟨g4, g5, g6, hCR, hiso, fun d hd h1 h2 h3 => ⟨hNs d hd h1 h3, hPs d hd h1 h2⟩, hw4⟩

/-- **The call-stack relation after cutting a stack at its head** (`k = 0`
of `CallRel.cut`): the SC keeps no stack, its head `(Lst sc)[0]` loses its
`reply_sc` and its links, the older replies stay linked, detached. -/
theorem CallRel.cut0 {R C : Set U64} {m m' : U64 → U64} {σ σ' : Fl4Spec.State Unit} {Lst : U64 → List U64}
    (h : CallRel m R C σ Lst) (hR0 : ∀ d ∈ R, d ≠ 0#u64) (hEv : ∀ d ∈ R, d.val % 2 = 0) {sc : U64} (hsc : sc ∈ C)
    (hl : 0 < (Lst sc).length)
    (hmS : ∀ q ∈ C, q ≠ sc → m' (scReplyA q) = m (scReplyA q)) (hmS0 : m' (scReplyA sc) = 0#u64)
    (hmP : ∀ d ∈ R, d ≠ (Lst sc)[0] → m' (rPrevA d) = m (rPrevA d))
    (hmN : ∀ d ∈ R, d ≠ (Lst sc)[0] → (∀ h : 1 < (Lst sc).length, d ≠ (Lst sc)[1]) →
      m' (rNextA d) = m (rNextA d))
    (hmNo : ∀ h : 1 < (Lst sc).length, m' (rNextA (Lst sc)[1]) = 0#u64)
    (hmPr : m' (rPrevA (Lst sc)[0]) = 0#u64) (hmNr : m' (rNextA (Lst sc)[0]) = 0#u64)
    {y : Fl4Spec.SchedContext} {n : Nat} (hky : σ.kheap sc.bv = some (.schedContext y n))
    {xr : Fl4Spec.Reply} (hkr : σ.kheap (Lst sc)[0].bv = some (.reply xr))
    (hk' : σ'.kheap sc.bv = some (.schedContext { y with scReplies := [] } n))
    (hkr' : σ'.kheap (Lst sc)[0].bv = some (.reply { xr with replySc := none }))
    (hko : ∀ q, q ≠ sc.bv → q ≠ (Lst sc)[0].bv → σ'.kheap q = σ.kheap q) :
    CallRel m' R C σ' (Function.update Lst sc []) ∧ Isolated m' R (Lst sc)[0] := by
  set Lst' := Function.update Lst sc ([] : List U64)
  have hL'sc : Lst' sc = [] := by simp [Lst']
  have hL'q : ∀ q, q ≠ sc → Lst' q = Lst q := fun q hq => by simp [Lst', hq]
  obtain ⟨⟨y0, n0, hk0, hy0⟩, hLR, hLnd, hLw⟩ := h.stack sc hsc
  rw [hky] at hk0; cases hk0
  have hmemL : ∀ i (hi : i < (Lst sc).length), (Lst sc)[i] ∈ Lst sc := fun i hi => List.getElem_mem hi
  have hRL : ∀ i (hi : i < (Lst sc).length), (Lst sc)[i] ∈ R := fun i hi => hLR _ (hmemL i hi)
  have hinj : ∀ i j (hi : i < (Lst sc).length) (hj : j < (Lst sc).length), (Lst sc)[i] = (Lst sc)[j] → i = j :=
    fun i j hi hj e => nodup_idx hLnd hi hj e
  have hneI : ∀ i j (hi : i < (Lst sc).length) (hj : j < (Lst sc).length), i ≠ j → (Lst sc)[i] ≠ (Lst sc)[j] :=
    fun i j hi hj hne e => hne (hinj i j hi hj e)
  have hother : ∀ q ∈ C, q ≠ sc → ∀ d ∈ Lst q, d ∉ Lst sc := fun q hq hne d hd hdL =>
    hne (h.excl q hq sc hsc d hd hdL)
  have hr0 : (Lst sc)[0] ≠ 0#u64 := hR0 _ (hRL 0 hl)
  have hdetL : ∀ j (hj : j < (Lst sc).length), Detached C Lst' (Lst sc)[j] := by
    intro j hj q hq hdq
    by_cases e : q = sc
    · subst q; rw [hL'sc] at hdq; simp at hdq
    · rw [hL'q q e] at hdq; exact hother q hq e _ hdq (hmemL j hj)
  have hdetold : ∀ d, Detached C Lst d → Detached C Lst' d := by
    intro d hd q hq h'
    by_cases e : q = sc
    · subst q; rw [hL'sc] at h'; simp at h'
    · rw [hL'q q e] at h'; exact hd q hq h'
  have hdet_ne : ∀ d, Detached C Lst d → ∀ j (hj : j < (Lst sc).length), d ≠ (Lst sc)[j] := fun d hd j hj e =>
    hd sc hsc (e ▸ hmemL j hj)
  have hpr : sc.bv ≠ (Lst sc)[0].bv := fun e => by rw [e, hkr] at hky; cases hky
  refine ⟨⟨fun q hq => ?_, fun q hq q' hq' d h1 h2 => ?_, fun d hd => ?_, fun d hd hdd => ?_⟩, ?_⟩
  · by_cases e : q = sc
    · subst q
      refine ⟨⟨_, n, hk', by rw [hL'sc]; rfl⟩, by rw [hL'sc]; simp, by rw [hL'sc]; exact List.nodup_nil, ?_, ?_⟩
      · rw [hL'sc, hmS0]; rfl
      · rw [hL'sc]; intro i hi; simp at hi
    · rw [hL'q q e]
      obtain ⟨⟨yq, nq, hkq0, hyq⟩, hqR, hqnd, hqw⟩ := h.stack q hq
      have hqr : q.bv ≠ (Lst sc)[0].bv := fun e' => by rw [e', hkr] at hkq0; cases hkq0
      refine ⟨⟨yq, nq, by rw [hko _ (bv_ne e) hqr]; exact hkq0, hyq⟩, hqR, hqnd, by rw [hmS q hq e]; exact hqw.1,
        fun i hi => ?_⟩
      have hm := List.getElem_mem hi
      have hnL : ∀ j (hj : j < (Lst sc).length), (Lst q)[i] ≠ (Lst sc)[j] := fun j hj e' =>
        hother q hq e _ hm (e' ▸ hmemL j hj)
      rw [hmP _ (hqR _ hm) (hnL 0 hl), hmN _ (hqR _ hm) (hnL 0 hl) (fun h' => hnL 1 h')]
      exact hqw.2 i hi
  · have g : ∀ q, q ∈ C → d ∈ Lst' q → d ∈ Lst q := fun q hq hdq => by
      by_cases e : q = sc
      · subst q; rw [hL'sc] at hdq; simp at hdq
      · rw [hL'q q e] at hdq; exact hdq
    exact h.excl q hq q' hq' d (g q hq h1) (g q' hq' h2)
  · obtain ⟨x, hkx, hxs⟩ := h.reply d hd
    have hdsc : d.bv ≠ sc.bv := fun e => by rw [e, hky] at hkx; cases hkx
    by_cases edr : d = (Lst sc)[0]
    · subst edr
      refine ⟨_, hkr', fun p => ⟨fun h' => by simp at h', ?_⟩⟩
      rintro ⟨q, hq, -, hhq⟩
      by_cases e : q = sc
      · subst q; rw [hL'sc] at hhq; simp at hhq
      · rw [hL'q q e] at hhq; exact (hother q hq e _ (List.mem_of_mem_head? hhq) (hmemL 0 hl)).elim
    · refine ⟨x, by rw [hko _ hdsc (bv_ne edr)]; exact hkx, fun p => ?_⟩
      rw [hxs p]
      constructor
      · rintro ⟨q, hq, hqp, hhq⟩
        refine ⟨q, hq, hqp, ?_⟩
        by_cases e : q = sc
        · subst q
          have : (Lst sc).head? = some (Lst sc)[0] := by
            rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hl]
          rw [this] at hhq; exact absurd (Option.some.inj hhq).symm edr
        · rw [hL'q q e]; exact hhq
      · rintro ⟨q, hq, hqp, hhq⟩
        refine ⟨q, hq, hqp, ?_⟩
        by_cases e : q = sc
        · subst q; rw [hL'sc] at hhq; simp at hhq
        · rw [hL'q q e] at hhq; exact hhq
  · by_cases hdL : d ∈ Lst sc
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hdL
      by_cases hj0 : j = 0
      · subst hj0
        rw [hmNr, hmPr]; exact ⟨rfl, fun h' => absurd rfl h', fun h' => absurd rfl h'⟩
      have hnr : (Lst sc)[j] ≠ (Lst sc)[0] := hneI j 0 hj hl hj0
      obtain ⟨g1, g2⟩ := hLw.2 j hj
      rw [hmP _ (hRL j hj) hnr, g1]
      by_cases hj1 : j = 1
      · subst hj1
        rw [hmNo hj]
        refine ⟨rfl, fun h' => absurd rfl h', fun hne => ?_⟩
        have hj2 : 2 < (Lst sc).length := by
          by_contra h''; rw [List.getD_eq_default _ _ (by omega)] at hne; exact hne rfl
        rw [List.getD_eq_getElem _ _ hj2]
        refine ⟨hRL _ hj2, hdetL _ hj2, ?_⟩
        have := (hLw.2 2 hj2).2
        dsimp only at this
        rw [hmN _ (hRL _ hj2) (hneI _ 0 hj2 hl (by omega)) (fun h' => hneI _ 1 hj2 h' (by omega)), this]
        rw [List.getD_eq_getElem _ _ hj]
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        dsimp only at g2
        rw [hmN _ (hRL _ hj) hnr (fun h' => hneI _ 1 hj h' hj1), g2]
        show ((Lst sc).getD j' 0#u64 &&& 1#u64) = 0#u64 ∧ _ ∧ _
        have hj' : j' < (Lst sc).length := by omega
        rw [List.getD_eq_getElem _ _ hj']
        refine ⟨reply_bit' (hEv _ (hRL j' hj')), fun _ => ⟨hRL j' hj', hdetL j' hj', ?_⟩, fun hne => ?_⟩
        · rw [hmP _ (hRL j' hj') (hneI j' 0 hj' hl (by omega)), (hLw.2 j' hj').1, List.getD_eq_getElem _ _ hj]
        · have hj2 : j' + 2 < (Lst sc).length := by
            by_contra h''; rw [List.getD_eq_default _ _ (by omega)] at hne; exact hne rfl
          rw [List.getD_eq_getElem _ _ hj2]
          refine ⟨hRL _ hj2, hdetL _ hj2, ?_⟩
          have := (hLw.2 (j' + 2) hj2).2
          dsimp only at this
          rw [hmN _ (hRL _ hj2) (hneI _ 0 hj2 hl (by omega)) (fun h' => hneI _ 1 hj2 h' (by omega)), this]
          rw [List.getD_eq_getElem _ _ hj]
    · have hdo : Detached C Lst d := by
        intro q hq hdq
        by_cases e : q = sc
        · subst q; exact hdL hdq
        · exact hdd q hq (by rw [hL'q q e]; exact hdq)
      obtain ⟨t1, t2, t3⟩ := h.det d hd hdo
      rw [hmP d hd (hdet_ne d hdo 0 hl), hmN d hd (hdet_ne d hdo 0 hl) (fun h' => hdet_ne d hdo 1 h')]
      refine ⟨t1, fun hne => ?_, fun hne => ?_⟩
      · obtain ⟨g1, g2, g3⟩ := t2 hne
        exact ⟨g1, hdetold _ g2, by rw [hmP _ g1 (hdet_ne _ g2 0 hl)]; exact g3⟩
      · obtain ⟨g1, g2, g3⟩ := t3 hne
        exact ⟨g1, hdetold _ g2, by
          rw [hmN _ g1 (hdet_ne _ g2 0 hl) (fun h' => hdet_ne _ g2 1 h')]; exact g3⟩
  · -- the head is isolated
    refine ⟨hmNr, hmPr, fun d hd => ?_⟩
    by_cases e : d = (Lst sc)[0]
    · rw [e, hmNr, hmPr]; exact ⟨fun h' => hr0 h'.symm, fun h' => hr0 h'.symm⟩
    by_cases hdL : d ∈ Lst sc
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hdL
      have hj0 : j ≠ 0 := fun h' => e (by subst h'; rfl)
      obtain ⟨g1, g2⟩ := hLw.2 j hj
      refine ⟨?_, ?_⟩
      · by_cases hj1 : j = 1
        · subst hj1; rw [hmNo hj]; exact fun h' => hr0 h'.symm
        rw [hmN _ (hRL j hj) (hneI j 0 hj hl hj0) (fun h' => hneI j 1 hj h' hj1), g2]
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        show (Lst sc).getD j' 0#u64 ≠ (Lst sc)[0]
        rw [List.getD_eq_getElem _ _ (by omega)]; exact hneI j' 0 (by omega) hl (by omega)
      · rw [hmP _ (hRL j hj) (hneI j 0 hj hl hj0), g1]
        by_cases hj1 : j + 1 < (Lst sc).length
        · rw [List.getD_eq_getElem _ _ hj1]; exact hneI (j + 1) 0 hj1 hl (by omega)
        · rw [List.getD_eq_default _ _ (by omega)]; exact fun h' => hr0 h'.symm
    · by_cases hdd : Detached C Lst d
      · obtain ⟨-, t2, t3⟩ := h.det d hd hdd
        rw [hmP d hd (hdet_ne d hdd 0 hl), hmN d hd (hdet_ne d hdd 0 hl) (fun h' => hdet_ne d hdd 1 h')]
        refine ⟨fun h' => ?_, fun h' => ?_⟩
        · exact hdet_ne _ (t2 (by rw [h']; exact hr0)).2.1 0 hl h'
        · exact hdet_ne _ (t3 (by rw [h']; exact hr0)).2.1 0 hl h'
      · simp only [Detached, not_forall, not_not] at hdd
        obtain ⟨q, hq, hdq⟩ := hdd
        have hne : q ≠ sc := fun e' => hdL (e' ▸ hdq)
        obtain ⟨-, hqR, -, hqw⟩ := h.stack q hq
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hdq
        have hnL : ∀ j (hj : j < (Lst sc).length), (Lst q)[i] ≠ (Lst sc)[j] := fun j hj e' =>
          hother q hq hne _ hdq (e' ▸ hmemL j hj)
        rw [hmP _ hd (hnL 0 hl), hmN _ hd (hnL 0 hl) (fun h' => hnL 1 h')]
        obtain ⟨g1, g2⟩ := hqw.2 i hi
        have hrq : ∀ j (hj : j < (Lst q).length), (Lst q)[j] ≠ (Lst sc)[0] := fun j hj e' =>
          hother q hq hne _ (List.getElem_mem hj) (e' ▸ hmemL 0 hl)
        refine ⟨?_, ?_⟩
        · rw [g2]
          cases i with
          | zero => exact odd_ne_even (hEv _ (hRL 0 hl))
          | succ j' =>
            show (Lst q).getD j' 0#u64 ≠ (Lst sc)[0]
            rw [List.getD_eq_getElem _ _ (by omega)]; exact hrq j' (by omega)
        · rw [g1]
          by_cases hj1 : i + 1 < (Lst q).length
          · rw [List.getD_eq_getElem _ _ hj1]; exact hrq _ hj1
          · rw [List.getD_eq_default _ _ (by omega)]; exact fun h' => hr0 h'.symm

theorem rrt_exists {α : Type} {m : Result α} {P : α → Prop} (h : m ⦃ r => P r ⦄) : ∃ v, m = ok v ∧ P v := by
  revert h; cases m <;> simp [WP.spec_vis, WP.spec_div, WP.spec_ok]

/-- **The post of `reply_remove_tcb`'s call-stack part** (module docstring). -/
def RrtPost (N T C R : Set U64) (c : U64) (s : S) (σ : Fl4Spec.State Unit) (Lst : U64 → List U64) (r : U64)
    (s4 : S) : Prop :=
  ∃ (σ' : Fl4Spec.State Unit) (Lst' : U64 → List U64),
    replyRemoveTcbSc r.bv σ = ({((), σ')}, False) ∧
    SchedRel st N T C c s4 σ' ∧ NtfnStateRel N T (L.mem s4) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
    CallRel (L.mem s4) R C σ' Lst' ∧ RPlaced st N T C R c s4 σ' ∧ RFree (L.mem s4) R C σ' Lst' ∧
    Isolated (L.mem s4) R r ∧ UFrame σ σ' ∧ CallStep (L.mem s) (L.mem s4) R C Lst Lst' r ∧
    (∃ x', σ'.kheap r.bv = some (.reply x') ∧ x'.replySc = none) ∧
    WritesIn st s s4 (fun b => KFoot st T N C c s σ b ∨ CallW' R C b)

/-- The relations across the spec's `reply_sc` update of a reply. -/
theorem updReply_rels {N T C R : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hRP : RPlaced st N T C R c s σ) {r : Fl4Spec.ObjRef} {x : Fl4Spec.Reply} (hk : σ.kheap r = some (.reply x))
    (x' : Fl4Spec.Reply) :
    SchedRel st N T C c s (updK σ r (.reply x')) ∧ NtfnStateRel N T (L.mem s) (updK σ r (.reply x')) ∧
      NSC N C (updK σ r (.reply x')) ∧ Inv (updK σ r (.reply x')) ∧ RPlaced st N T C R c s (updK σ r (.reply x')) :=
  ⟨hS.stableW (WritesIn.refl _ _) (NtfnStepW.updReply hk x'), hR.frame hS.placed (fun _ _ _ => rfl) (KView.updReply hk x'),
    hN.updReply hk x', hI.updReply hk, hRP.frame rfl (SzKeep.updK hk fun _ _ h => by cases h)⟩

/-- `RFree` after the step, from the call-stack step and `r` unlinked. -/
theorem rfree_after {R C : Set U64} {m m' : U64 → U64} {σ σ' : Fl4Spec.State Unit} {Lst Lst' : U64 → List U64}
    {r : U64} (h : RFree m R C σ Lst) (hcs : CallStep m m' R C Lst Lst' r) (hiso : Isolated m' R r)
    (hk : ∀ d ∈ R, d ≠ r → ∀ x, σ'.kheap d.bv = some (.reply x) → σ.kheap d.bv = some (.reply x)) :
    RFree m' R C σ' Lst' :=
  RFree.step h hcs (fun d hd ⟨x, hx, hx0⟩ hdr => ⟨x, hk d hd hdr x hx, hx0⟩) (fun _ => ⟨hiso.1, hiso.2.1⟩)

/-- **`reply_remove_tcb` before `reply_unlink`** (module docstring). -/
def rrtCut (s : S) (r : U64) : Result S := do
  let next ← obj.Reply.next st r s
  let prev ← obj.Reply.prev st r s
  let s1 ← if next != 0#u64 then do
      let b ← obj.Reply.next_is_head st r s
      if b then obj.Sc.set_reply st next s 0#u64 else obj.Reply.set_prev st next s 0#u64
    else ok s
  let s2 ← if prev != 0#u64 then obj.Reply.set_next st prev s1 0#u64 false else ok s1
  let s3 ← obj.Reply.set_prev st r s2 0#u64
  obj.Reply.set_next st r s3 0#u64 false

omit L in
theorem reply_remove_tcb_eq (s : S) (t : U64) :
    ipc.reply_remove_tcb st s t = (do
      let i ← obj.Tcb.reply_obj st t s
      let s4 ← rrtCut (st := st) s i
      ipc.reply_unlink st s4 i t) := by
  unfold ipc.reply_remove_tcb rrtCut
  simp only [Std.bind_assoc]

set_option maxHeartbeats 4000000 in
/-- **`reply_remove_tcb`'s call-stack part against l4v** (module docstring):
the head of a stack leaves its SC with no stack, a reply further down is cut
out with the older ones, a detached one is spliced out; the spec's
`replyRemoveTcbSc` (`sc_with_reply`, the cut, `reply_sc` cleared). -/
theorem reply_remove_tcb_sc_refines {N T C R : Set U64} {c : U64} (s : S) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    {Lst : U64 → List U64} (hCR : CallRel (L.mem s) R C σ Lst) (hRP : RPlaced st N T C R c s σ)
    (hRF : RFree (L.mem s) R C σ Lst) (hC0 : ∀ q ∈ C, q ≠ 0#u64)
    (hSCs : ∀ p y n, σ.kheap p = some (.schedContext y n) → ∃ q ∈ C, q.bv = p)
    {r : U64} (hr : r ∈ R) :
    rrtCut (st := st) s r ⦃ s4 => RrtPost (L := L) N T C R c s σ Lst r s4 ⦄ := by
  have hP := hS.placed
  have hev : ∀ d ∈ R, d.val % 2 = 0 := fun d hd => by have := (hRP.align d hd).1; omega
  have hR0 : ∀ d ∈ R, d ≠ 0#u64 := fun d hd => (hRP.align d hd).2.1
  have hal : ∀ d ∈ R, Aligned (rPrevA d) ∧ Aligned (rNextA d) := fun d hd =>
    ⟨hRP.aligned hd (Or.inl (rPrevA_val (hRP.align d hd))), hRP.aligned hd (Or.inr (rNextA_val (hRP.align d hd)))⟩
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
    rw [hvq, rPrevA_val (hRP.align d hd), rNextA_val (hRP.align d hd)]; omega
  have cwM : ∀ {s' : S} (P : U64 → Prop), WritesIn st s s' (CallW' R C) → WritesIn st s s' (fun b => P b ∨ CallW' R C b) :=
    fun P h => h.mono fun _ hb => Or.inr hb
  obtain ⟨xr, hkr, hxr⟩ := hCR.reply r hr
  have hscs_eq : ∀ q ∈ C, ∀ y n, σ.kheap q.bv = some (.schedContext y n) → y.scReplies = (Lst q).map UScalar.bv := by
    intro q hq y n hk
    obtain ⟨⟨y0, n0, hk0, hy0⟩, -⟩ := hCR.stack q hq
    rw [hk] at hk0; cases hk0; exact hy0
  have hmemb : ∀ q ∈ C, ∀ y n, σ.kheap q.bv = some (.schedContext y n) → (r.bv ∈ y.scReplies ↔ r ∈ Lst q) := by
    intro q hq y n hk
    rw [hscs_eq q hq y n hk, List.mem_map]
    exact ⟨fun ⟨d, hd, e⟩ => (eq_of_bv e) ▸ hd, fun h => ⟨r, h, rfl⟩⟩
  -- the reads
  unfold rrtCut
  obtain ⟨nx, hnxE, rfl⟩ := rrt_exists (obj.Reply.next.spec (L := L) s r)
  rw [hnxE]; simp only [bind_ok]
  obtain ⟨pv, hpvE, rfl⟩ := rrt_exists (obj.Reply.prev.spec (L := L) s r)
  rw [hpvE]; simp only [bind_ok]
  obtain ⟨b, hbE, rfl⟩ := rrt_exists (obj.Reply.next_is_head.spec (L := L) s r)
  rw [hbE]; simp only [bind_ok]
  by_cases hlive : ∃ sc ∈ C, r ∈ Lst sc
  swap
  · -- detached: spliced out of its chain
    have hdet : Detached C Lst r := fun q hq h => hlive ⟨q, hq, h⟩
    obtain ⟨t1, t2, t3⟩ := hCR.det r hr hdet
    have hrem : replyRemoveTcbSc r.bv σ = ({((), σ)}, False) := by
      unfold replyRemoveTcbSc
      rw [nd_gets_bind, scWithReply_none fun q y n hq hm => by
        obtain ⟨q', hq', rfl⟩ := hSCs q y n hq
        exact hdet q' hq' ((hmemb q' hq' y n hq).1 hm)]
      rfl
    have hrs0 : xr.replySc = none := by
      cases h : xr.replySc with
      | none => rfl
      | some p =>
        obtain ⟨sc', hsc', -, hh⟩ := (hxr p).1 h
        exact absurd (List.mem_of_mem_head? hh) (hdet sc' hsc')
    rw [headBit_even (even_of_bit t1)]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hnx' : L.mem s (rNextA r) &&& ~~~1#u64 = L.mem s (rNextA r) := and_not1 _ (even_of_bit t1)
    have hpv' : L.mem s (rPrevA r) &&& ~~~1#u64 = L.mem s (rPrevA r) := by
      by_cases h0 : L.mem s (rPrevA r) = 0#u64
      · rw [h0]; rfl
      · exact and_not1 _ (hev _ (t3 h0).1)
    rw [hnx', hpv']
    have hnxR : L.mem s (rNextA r) = 0#u64 ∨ L.mem s (rNextA r) ∈ R := by
      by_cases h0 : L.mem s (rNextA r) = 0#u64
      · exact Or.inl h0
      · exact Or.inr (t2 h0).1
    have hpvR : L.mem s (rPrevA r) = 0#u64 ∨ L.mem s (rPrevA r) ∈ R := by
      by_cases h0 : L.mem s (rPrevA r) = 0#u64
      · exact Or.inl h0
      · exact Or.inr (t3 h0).1
    refine WP.spec_mono (splice_post s σ hS hR hRP hr hnxR hpvR (Lst' := Lst)
      (fun m' hmS hmP hmN hmPn hmNp hmPr hmNr =>
        CallRel.dsplice (m' := m') hCR hR0 hev hr hdet hmS hmP hmN hmPn hmNp hmPr hmNr)) ?_
    rintro s4 ⟨h1, h2, h3, h4, h5, hm, hw⟩
    have hcs : CallStep (L.mem s) (L.mem s4) R C Lst Lst r :=
      ⟨fun d hd _ hn0 hp0 hdr => hm d hd hdr (fun e => by
          have h0 : L.mem s (rNextA r) ≠ 0#u64 := fun h => hR0 d hd (e.trans h)
          have := (t2 h0).2.2; rw [← e] at this; rw [hp0] at this; exact hR0 r hr this.symm)
        (fun e => by
          have h0 : L.mem s (rPrevA r) ≠ 0#u64 := fun h => hR0 d hd (e.trans h)
          have := (t3 h0).2.2; rw [← e] at this; rw [hn0] at this; exact hR0 r hr this.symm),
       fun q _ d hdq => hdq, hdet⟩
    exact ⟨σ, Lst, hrem, h1, h2, hN, hI, h4, h3, rfree_after hRF hcs h5 (fun d _ _ x hx => hx), h5,
      UFrame.refl σ, hcs, ⟨xr, hkr, hrs0⟩, cwM _ hw⟩
  obtain ⟨sc, hsc, hrL⟩ := hlive
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
  have hpr : sc.bv ≠ r.bv := fun e => by rw [e, hkr] at hk; cases hk
  have hmL : ∀ i (hi : i < (Lst sc).length), (Lst sc)[i] ∈ R := fun i hi => hLR _ (List.getElem_mem hi)
  have hko1 : ∀ (l : List Fl4Spec.ObjRef) q, q ≠ sc.bv →
      (updSc σ sc.bv { y with scReplies := l } n).kheap q = σ.kheap q := fun l q hq => by simp [updK, hq]
  have hkσ1 : ∀ l : List Fl4Spec.ObjRef,
      (updSc σ sc.bv { y with scReplies := l } n).kheap sc.bv = some (.schedContext { y with scReplies := l } n) :=
    fun l => by simp [updK]
  obtain ⟨k, hkl, e⟩ := List.getElem_of_mem hrL
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · -- the head: the SC keeps no stack
    obtain ⟨hp, hn⟩ := hLw.2 0 hkl
    dsimp only at hn
    rw [e] at hp hn
    have hpE : ((Lst sc).getD 1 0#u64 = 0#u64 ∨ (Lst sc).getD 1 0#u64 ∈ R) ∧
        (∀ h : 1 < (Lst sc).length, (Lst sc).getD 1 0#u64 = (Lst sc)[1]) ∧
        ((Lst sc).getD 1 0#u64 ≠ 0#u64 → 1 < (Lst sc).length) := by
      by_cases hlt : 1 < (Lst sc).length
      · rw [List.getD_eq_getElem _ _ hlt]
        exact ⟨Or.inr (hmL _ hlt), fun _ => rfl, fun _ => hlt⟩
      · rw [List.getD_eq_default _ _ (by omega)]
        exact ⟨Or.inl rfl, fun h => absurd h hlt, fun h => absurd rfl h⟩
    have hpEv : ((Lst sc).getD 1 0#u64).val % 2 = 0 := by
      rcases hpE.1 with h | h
      · rw [h]; rfl
      · exact hev _ h
    have hhd : (Lst sc).head? = some r := by
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hkl, e]
    have hrsc : xr.replySc = some sc.bv := (hxr sc.bv).2 ⟨sc, hsc, rfl, hhd⟩
    have hh : Fl4Spec.the ((Lst sc).map UScalar.bv).head? = r.bv := by
      rw [List.head?_map, hhd]; rfl
    have hr0 : r ≠ 0#u64 := hR0 _ hr
    -- the spec side
    set σ1 := updSc σ sc.bv { y with scReplies := [] } n with hσ1
    have hkr1 : σ1.kheap r.bv = some (.reply xr) := by rw [hσ1, hko1 _ _ (Ne.symm hpr)]; exact hkr
    set σ2 := updK σ1 r.bv (.reply { xr with replySc := none }) with hσ2
    have hrem : replyRemoveTcbSc r.bv σ = ({((), σ2)}, False) := by
      unfold replyRemoveTcbSc
      rw [nd_gets_bind, hwr]
      dsimp only
      rw [nd_bind_one (nd_liftM_one (getSchedContext_eq hk) _), nd_bind_one (getReplySc_eq hkr), hyL,
        if_pos hh, nd_bind_one (nd_assert_true hrsc σ), nd_bind_one (updateSchedContext_eq hk _)]
      have e1 : updSc σ sc.bv (Fl4Spec.scRepliesUpdate
          (List.takeWhile fun x => decide (x ≠ r.bv)) y) n = σ1 := by
        have := takeWhile_bv _ hLnd 0 hkl
        simp only [List.take_zero, List.map_nil, e] at this
        simp only [σ1, Fl4Spec.scRepliesUpdate, hyL, this]
      rw [e1]; exact setReplySc_eq none hkr1
    obtain ⟨hS1, hf1, hK1, -⟩ := hS.set_sc_reply hsc hk 0#u64 []
    have hR1 := hR.frame hP hf1 hK1
    have hRP1 : RPlaced st N T C R c (L.wr s (scReplyA sc) 0#u64) σ1 :=
      hRP.frame (by simp) (SzKeep.updK hk fun x n' h => by cases h; exact ⟨y, rfl⟩)
    -- the implementation
    have hnx' : (L.mem s (rNextA r) &&& ~~~1#u64) = sc := by rw [hn]; exact or1_and_not1 _ hsc2
    have hpv' : (L.mem s (rPrevA r) &&& ~~~1#u64) = (Lst sc).getD 1 0#u64 := by
      rw [hp]; exact and_not1 _ hpEv
    rw [hnx', hpv', hn, headBit_or1]
    have hnz : (sc != 0#u64) = true := by simp [hC0 sc hsc]
    simp only [hnz, ↓reduceIte]
    obtain ⟨s1', hs1E, rfl⟩ := rrt_exists (obj.Sc.set_reply.spec (L := L) s sc 0#u64)
    rw [hs1E]; simp only [bind_ok]
    set pv := (Lst sc).getD 1 0#u64 with hpvd
    set s1 := L.wr s (scReplyA sc) 0#u64 with hs1
    set s2 := if pv = 0#u64 then s1 else L.wr s1 (rNextA pv) 0#u64 with hs2
    have e2 : (if pv != 0#u64 then obj.Reply.set_next st pv s1 0#u64 false else ok s1) = ok s2 := by
      by_cases h : pv = 0#u64 <;> simp [h, s2, set_next0_eq]
    rw [e2]; simp only [bind_ok, set_prev0_eq, set_next0_eq, WP.spec_ok]
    -- the relations
    have k2 : SchedRel st N T C c s2 σ1 ∧ NtfnStateRel N T (L.mem s2) σ1 ∧ RPlaced st N T C R c s2 σ1 := by
      by_cases h : pv = 0#u64
      · simp only [s2, h, ↓reduceIte]; exact ⟨hS1, hR1, hRP1⟩
      · simp only [s2, h, ↓reduceIte]
        exact rword_keep hS1 hR1 hRP1 (hpE.1.resolve_left h) (Or.inr (rNextA_val (hRP.align _ (hpE.1.resolve_left h)))) _
    obtain ⟨q1, q2, q3⟩ := rword_keep k2.1 k2.2.1 k2.2.2 hr (Or.inl (rPrevA_val (hRP.align r hr))) 0#u64
    obtain ⟨q4, q5, q6⟩ := rword_keep q1 q2 q3 hr (Or.inr (rNextA_val (hRP.align r hr))) 0#u64
    obtain ⟨g1, g2, g3, g4, g5⟩ := updReply_rels q4 q5 hN.updSc (hI.scFields hk rfl rfl rfl rfl) q6 hkr1
      { xr with replySc := none }
    -- the memory
    set s4 := L.wr (L.wr s2 (rPrevA r) 0#u64) (rNextA r) 0#u64 with hs4
    obtain ⟨haS, hvS, -⟩ := sc_reply_word hS hsc
    have hSne : ∀ q ∈ C, q ≠ sc → (scReplyA q).val ≠ (scReplyA sc).val := by
      intro q hq e
      obtain ⟨-, hvq, -⟩ := sc_reply_word hS hq
      rw [hvq, hvS]; exact fun h => e (UScalar.eq_of_val_eq (by omega))
    have hpvR : pv ≠ 0#u64 → pv ∈ R := fun h => hpE.1.resolve_left h
    have hne : ∀ b, Aligned b → b.val ≠ (scReplyA sc).val → (pv ≠ 0#u64 → b.val ≠ (rNextA pv).val) →
        b.val ≠ (rPrevA r).val → b.val ≠ (rNextA r).val → L.mem s4 b = L.mem s b := by
      intro b hb h1 h2 h3 h4
      rw [hs4, L.mem_wr_ne (hal r hr).2 hb (Ne.symm h4), L.mem_wr_ne (hal r hr).1 hb (Ne.symm h3)]
      simp only [s2, s1]
      by_cases hp0 : pv = 0#u64 <;> simp only [hp0, ↓reduceIte]
      · rw [L.mem_wr_ne haS hb (Ne.symm h1)]
      · rw [L.mem_wr_ne (hal pv (hpvR hp0)).2 hb (Ne.symm (h2 hp0)), L.mem_wr_ne haS hb (Ne.symm h1)]
    have hPr0 : L.mem s4 (rPrevA r) = 0#u64 := by
      rw [hs4, L.mem_wr_ne (hal r hr).2 (hal r hr).1 (fun e => hpn r r hr hr e.symm)]
      exact L.mem_wr_same (hal r hr).1
    have hNr0 : L.mem s4 (rNextA r) = 0#u64 := L.mem_wr_same (hal r hr).2
    have hS0 : L.mem s4 (scReplyA sc) = 0#u64 := by
      rw [hs4, L.mem_wr_ne (hal r hr).2 haS (Ne.symm (hfarS sc hsc r hr).2),
        L.mem_wr_ne (hal r hr).1 haS (Ne.symm (hfarS sc hsc r hr).1)]
      simp only [s2, s1]
      by_cases hp0 : pv = 0#u64 <;> simp only [hp0, ↓reduceIte]
      · exact L.mem_wr_same haS
      · rw [L.mem_wr_ne (hal pv (hpvR hp0)).2 haS (Ne.symm (hfarS sc hsc pv (hpvR hp0)).2)]; exact L.mem_wr_same haS
    have hNo : ∀ h : 1 < (Lst sc).length, L.mem s4 (rNextA (Lst sc)[1]) = 0#u64 := by
      intro h
      have hpv1 : pv = (Lst sc)[1] := hpE.2.1 h
      have h1R := hmL 1 h
      have hn1 : (Lst sc)[1] ≠ r := fun e' => by
        have := nodup_idx hLnd h hkl (e'.trans e.symm); omega
      rw [hs4, L.mem_wr_ne (hal r hr).2 (hal _ h1R).2 (fun e => (hwd _ r h1R hr hn1).2 e.symm),
        L.mem_wr_ne (hal r hr).1 (hal _ h1R).2 (hpn r _ hr h1R)]
      have hp0 : pv ≠ 0#u64 := by rw [hpv1]; exact hR0 _ h1R
      simp only [s2, hp0, ↓reduceIte, ← hpv1]
      exact L.mem_wr_same (hal pv (hpvR hp0)).2
    have hPs : ∀ d ∈ R, d ≠ r → L.mem s4 (rPrevA d) = L.mem s (rPrevA d) := fun d hd h1 =>
      hne _ (hal d hd).1 (fun e => (hfarS sc hsc d hd).1 e.symm) (fun h => hpn d pv hd (hpvR h))
        (hwd d r hd hr h1).1 (hpn d r hd hr)
    have hNs : ∀ d ∈ R, d ≠ r → (∀ h : 1 < (Lst sc).length, d ≠ (Lst sc)[1]) →
        L.mem s4 (rNextA d) = L.mem s (rNextA d) := fun d hd h1 h2 =>
      hne _ (hal d hd).2 (fun e => (hfarS sc hsc d hd).2 e.symm)
        (fun h => (hwd d pv hd (hpvR h) (fun e => h2 (hpE.2.2 h) (e.trans (hpE.2.1 (hpE.2.2 h))))).2)
        (fun e => hpn r d hr hd e.symm) (hwd d r hd hr h1).2
    have hSs : ∀ q ∈ C, q ≠ sc → L.mem s4 (scReplyA q) = L.mem s (scReplyA q) := by
      intro q hq hne'
      obtain ⟨haq, -, -⟩ := sc_reply_word hS hq
      exact hne _ haq (hSne q hq hne') (fun h => (hfarS q hq pv (hpvR h)).2) (hfarS q hq r hr).1 (hfarS q hq r hr).2
    have hkσ2 : σ2.kheap sc.bv = some (.schedContext { y with scReplies := [] } n) := by
      rw [show σ2.kheap sc.bv = σ1.kheap sc.bv by simp [σ2, updK, hpr]]; exact hkσ1 []
    have hkr2 : σ2.kheap r.bv = some (.reply { xr with replySc := none }) := by simp [σ2, updK]
    have hko2 : ∀ q, q ≠ sc.bv → q ≠ r.bv → σ2.kheap q = σ.kheap q := fun q h1 h2 => by
      rw [show σ2.kheap q = σ1.kheap q by simp [σ2, updK, h2]]; exact hko1 _ _ h1
    obtain ⟨hCR2, hiso⟩ := CallRel.cut0 (m' := L.mem s4) (σ' := σ2) hCR hR0 hev hsc hkl hSs hS0
      (by rw [e]; exact hPs) (by rw [e]; exact hNs) hNo (by rw [e]; exact hPr0) (by rw [e]; exact hNr0) hk
      (by rw [e]; exact hkr) hkσ2 (by rw [e]; exact hkr2) (by rw [e]; exact hko2)
    rw [e] at hiso
    -- the writes
    have cw : ∀ {s0 : S} {a : U64} {v : U64}, Aligned a → CallW' R C a → WritesIn st s0 (L.wr s0 a v) (CallW' R C) :=
      fun ha hc => (writesIn_wr ha).mono fun b hb => hb ▸ hc
    have tr : ∀ {x y z : S}, WritesIn st x y (CallW' R C) → WritesIn st y z (CallW' R C) →
        WritesIn st x z (CallW' R C) := fun h1 h2 => (h1.trans h2).mono fun b hb => hb.elim id id
    have w2 : WritesIn st s1 s2 (CallW' R C) := by
      by_cases h : pv = 0#u64
      · simp only [s2, h, ↓reduceIte]; exact WritesIn.refl _ _
      · simp only [s2, h, ↓reduceIte]; exact cw (hal pv (hpvR h)).2 (Or.inl ⟨pv, hpvR h, Or.inl rfl⟩)
    have hw4 : WritesIn st s s4 (CallW' R C) :=
      tr (tr (cw haS (Or.inr ⟨sc, hsc, rfl⟩)) w2) (tr (cw (hal r hr).1 (Or.inl ⟨r, hr, Or.inr rfl⟩))
        (cw (hal r hr).2 (Or.inl ⟨r, hr, Or.inl rfl⟩)))
    have hdet1 : ∀ h : 1 < (Lst sc).length, ∀ d, Detached C Lst d → d ≠ (Lst sc)[1] := fun h d hd e =>
      hd sc hsc (e ▸ List.getElem_mem h)
    have hcs : CallStep (L.mem s) (L.mem s4) R C Lst (Function.update Lst sc []) r :=
      ⟨fun d hd hdet _ _ hdr => ⟨hNs d hd hdr fun h => hdet1 h d hdet, hPs d hd hdr⟩,
        fun q hq d hdq => by
          by_cases e : q = sc
          · subst e; simp at hdq
          · simpa [e] using hdq,
        fun q hq hdq => by
          by_cases e : q = sc
          · subst e; simp at hdq
          · simp only [ne_eq, e, not_false_eq_true, Function.update_of_ne] at hdq
            exact e (hCR.excl q hq sc hsc _ hdq hrL)⟩
    refine ⟨σ2, _, hrem, g1, g2, g3, g4, hCR2, g5, rfree_after hRF hcs hiso (fun d hd hdr x hx => ?_), hiso,
      (UFrame.updSc hk).trans (UFrame.updReplySc hkr1 none), hcs, ⟨{ xr with replySc := none }, hkr2, rfl⟩,
      cwM _ hw4⟩
    have e1 : d.bv ≠ r.bv := bv_ne hdr
    rw [show σ2.kheap d.bv = σ1.kheap d.bv by simp [σ2, updK, e1]] at hx
    have e2 : d.bv ≠ sc.bv := fun e' => by rw [e', hkσ1] at hx; cases hx
    rw [hσ1, hko1 _ _ e2] at hx; exact hx
  · -- further down: cut out with the older replies
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    subst e
    have hjl : j < (Lst sc).length := by omega
    have hne0j : (Lst sc)[0] ≠ (Lst sc)[j + 1] := fun h => by
      have := nodup_idx hLnd (by omega) hkl h; omega
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
    -- the spec side
    set σ1 := updSc σ sc.bv { y with scReplies := ((Lst sc).take (j + 1)).map UScalar.bv } n with hσ1
    have hkr1 : σ1.kheap (Lst sc)[j + 1].bv = some (.reply xr) := by rw [hσ1, hko1 _ _ (Ne.symm hpr)]; exact hkr
    set σ2 := updK σ1 (Lst sc)[j + 1].bv (.reply { xr with replySc := none }) with hσ2
    have hrem : replyRemoveTcbSc (Lst sc)[j + 1].bv σ = ({((), σ2)}, False) := by
      unfold replyRemoveTcbSc
      rw [nd_gets_bind, hwr]
      dsimp only
      rw [nd_bind_one (nd_liftM_one (getSchedContext_eq hk) _), nd_bind_one (getReplySc_eq hkr), hyL,
        if_neg hnh, nd_bind_one (nd_assert_true hrsc0 σ), nd_bind_one (updateSchedContext_eq hk _)]
      have e1 : updSc σ sc.bv (Fl4Spec.scRepliesUpdate
          (List.takeWhile fun r => decide (r ≠ (Lst sc)[j + 1].bv)) y) n = σ1 := by
        simp only [σ1, Fl4Spec.scRepliesUpdate, hyL, takeWhile_bv _ hLnd _ hkl]
      rw [e1]; exact setReplySc_eq none hkr1
    have hS1 := hS.set_replies hsc hk (((Lst sc).take (j + 1)).map UScalar.bv)
    have hR1 : NtfnStateRel N T (L.mem s) σ1 := hR.frame hS.placed (fun _ _ _ => rfl) (KView.of_sc hk)
    have hRP1 : RPlaced st N T C R c s σ1 :=
      hRP.frame rfl (SzKeep.updK hk fun x n' h => by cases h; exact ⟨y, rfl⟩)
    -- the implementation
    have hnx' : (L.mem s (rNextA (Lst sc)[j + 1]) &&& ~~~1#u64) = (Lst sc)[j] := by
      rw [hn]; exact and_not1 _ (hev _ (hmL _ hjl))
    have hpv' : (L.mem s (rPrevA (Lst sc)[j + 1]) &&& ~~~1#u64) = (Lst sc).getD (j + 2) 0#u64 := by
      rw [hp]; exact and_not1 _ hpvEv
    rw [hnx', hpv', hn, headBit_even (hev _ (hmL _ hjl))]
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_mono (splice_post s σ1 hS1 hR1 hRP1 (hmL _ hkl) (Or.inr (hmL _ hjl)) hpvE.1
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
          hmPr hmNr hk (hkσ1 _) (hko1 _))) ?_
    rintro s4 ⟨h1, h2, h3, h4, h5, hm, hw⟩
    obtain ⟨g1, g2, g3, g4, g5⟩ := updReply_rels h1 h2 hN.updSc (hI.scFields hk rfl rfl rfl rfl) h3 hkr1
      { xr with replySc := none }
    have hk2 : ∀ q, q ≠ (Lst sc)[j + 1].bv → σ2.kheap q = σ1.kheap q := fun q hq => by simp [σ2, updK, hq]
    have hCR2 : CallRel (L.mem s4) R C σ2 (Function.update Lst sc ((Lst sc).take (j + 1))) := by
      refine h4.frame (fun _ _ => rfl) (fun _ _ => ⟨rfl, rfl⟩) (fun q _ y' n' hq => ⟨y', ?_, rfl⟩)
        (fun d _ x hx => ?_)
      · have : q.bv ≠ (Lst sc)[j + 1].bv := fun e' => by rw [e', hkr1] at hq; cases hq
        rw [hk2 _ this]; exact hq
      · by_cases e' : d.bv = (Lst sc)[j + 1].bv
        · rw [e', hkr1] at hx; cases hx
          exact ⟨{ xr with replySc := none }, by rw [e']; simp [σ2, updK], hrsc0.symm⟩
        · exact ⟨x, by rw [hk2 _ e']; exact hx, rfl⟩
    have hcs : CallStep (L.mem s) (L.mem s4) R C Lst (Function.update Lst sc ((Lst sc).take (j + 1))) (Lst sc)[j + 1] :=
      ⟨fun d hd hdet _ _ hdr => hm d hd hdr
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
            exact e (hCR.excl q hq sc hsc _ hdq (List.getElem_mem hkl))⟩
    refine ⟨σ2, _, hrem, g1, g2, g3, g4, hCR2, g5, rfree_after hRF hcs h5 (fun d hd hdr x hx => ?_), h5,
      (UFrame.updSc hk).trans (UFrame.updReplySc hkr1 none), hcs, ⟨{ xr with replySc := none }, by simp [σ2, updK], rfl⟩,
      cwM _ hw⟩
    have e1 : d.bv ≠ (Lst sc)[j + 1].bv := bv_ne hdr
    rw [hk2 _ e1] at hx
    have e2 : d.bv ≠ sc.bv := fun e' => by rw [e', hkσ1] at hx; cases hx
    rw [hσ1, hko1 _ _ e2] at hx; exact hx

end

end

end Fl4Proofs.P3.Sched
