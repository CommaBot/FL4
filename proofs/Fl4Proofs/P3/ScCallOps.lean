/-
P3 (DESIGN.md §9), scheduling contexts: **operations on the call stack**:
the spec-side frames (`Inv.updReply`, `setReplySc_eq`), the SC `REPLY`
word (`SchedRel.set_sc_reply`), and `unbind_reply` against l4v
`sched_context_unbind_reply` (SchedContext `Unbind`'s reply step).
-/
import Fl4Proofs.P3.ScCall
import Fl4Proofs.P3.ScFoot
import Fl4Proofs.P3.EpSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-- **Replacing a reply object keeps `Inv`.** -/
theorem Inv.updReply {σ : State Unit} (h : Inv σ) {r : ObjRef} {x x' : Reply}
    (hk : σ.kheap r = some (.reply x)) : Inv (updK σ r (.reply x')) := by
  set σ' := updK σ r (.reply x')
  have ko : ∀ q, q ≠ r → σ'.kheap q = σ.kheap q := fun q hq => by simp [σ', updK, hq]
  have kn : σ'.kheap r = some (.reply x') := by simp [σ', updK]
  have kt : ∀ q y, σ'.kheap q = some (.tcb y) ↔ σ.kheap q = some (.tcb y) := by
    intro q y
    by_cases e : q = r
    · subst e; rw [kn, hk]; simp
    · rw [ko q e]
  have ks : ∀ q y m, σ'.kheap q = some (.schedContext y m) ↔ σ.kheap q = some (.schedContext y m) := by
    intro q y m
    by_cases e : q = r
    · subst e; rw [kn, hk]; simp
    · rw [ko q e]
  have kn' : ∀ q y, σ'.kheap q = some (.notification y) ↔ σ.kheap q = some (.notification y) := by
    intro q y
    by_cases e : q = r
    · subst e; rw [kn, hk]; simp
    · rw [ko q e]
  have rt : ∀ u ∈ σ.releaseQueue, specRt σ' u = specRt σ u := by
    intro u hu
    obtain ⟨xu, scp, yu, nu, h1, h2, -, h4, -⟩ := h.rel u hu
    have hne := h.ne scp yu nu h4
    rw [specRt_eq ((kt _ _).2 h1) h2 ((ks _ _ _).2 h4) hne, specRt_eq h1 h2 h4 hne]
  refine ⟨fun d q u hu => ?_, fun u hu => ?_, ?_, fun u y hy hc => ?_, fun q y m hy => ?_,
    fun u y q hy hq => ?_, fun q y q' hy hq => ?_, fun q y m hy => ?_, fun q y m hy => ?_⟩
  · obtain ⟨xu, scp, yu, nu, h1, h2, h3, h4, h5⟩ := h.rq d q u hu
    exact ⟨xu, scp, yu, nu, (kt _ _).2 h1, h2, h3, (ks _ _ _).2 h4, h5⟩
  · obtain ⟨xu, scp, yu, nu, h1, h2, h3, h4, h5⟩ := h.rel u hu
    exact ⟨xu, scp, yu, nu, (kt _ _).2 h1, h2, h3, (ks _ _ _).2 h4, h5⟩
  · show σ.releaseQueue.Pairwise _
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) h.sorted
    rw [rt a ha, rt b hb]; exact hab
  · intro x' scp yu nu h1 h2 h3 h4 h5
    exact h.rd u y ((kt _ _).1 hy) hc x' scp yu nu ((kt _ _).1 h1) h2 ((ks _ _ _).1 h3) h4 h5
  · exact h.refills q y m ((ks _ _ _).1 hy)
  · obtain ⟨yq, mq, h1, h2⟩ := h.back u y q ((kt _ _).1 hy) hq
    exact ⟨yq, mq, (ks _ _ _).2 h1, h2⟩
  · obtain ⟨yq, mq, h1⟩ := h.ntfnSc q y q' ((kn' _ _).1 hy) hq
    exact ⟨yq, mq, (ks _ _ _).2 h1⟩
  · exact h.ne q y m ((ks _ _ _).1 hy)
  · exact h.rr q y m ((ks _ _ _).1 hy)

theorem TKeepE.updReply (E : ObjRef → Prop) {σ : State Unit} {r : ObjRef} {x : Reply}
    (hk : σ.kheap r = some (.reply x)) (x' : Reply) : TKeepE E σ (updK σ r (.reply x')) := by
  refine ⟨fun q y _ hy => ?_, fun q y m hy => ⟨y, ?_, rfl⟩⟩
  · have : q ≠ r := by rintro rfl; rw [hk] at hy; cases hy
    simp [updK, this, hy]
  · have : q ≠ r := by rintro rfl; rw [hk] at hy; cases hy
    simp [updK, this, hy]

theorem setReplySc_eq {σ : State Unit} {p : ObjRef} {x : Reply} (v : Option ObjRef)
    (hk : σ.kheap p = some (.reply x)) :
    setReplyObjRef (Z := Unit) replyScUpdate p v σ = ({((), updK σ p (.reply { x with replySc := v }))}, False) := by
  show updateSkObjRef KernelObject.reply replyScUpdate p v σ = _
  unfold updateSkObjRef
  rw [nd_bind_one (Fl4Proofs.P3.Endp.getReply_eq hk)]
  exact Fl4Proofs.P3.Endp.setReply_eq _ hk

theorem nd_liftM_one {σ α β : Type} {m : NonDet σ α} {s s' : σ} {a : α} (h : m s = ({(a, s')}, False))
    (f : α → β) : NonDet.liftM f m s = ({(f a, s')}, False) := by
  unfold NonDet.liftM; rw [nd_bind_one' h]; rfl

/-- What `reply_unlink_tcb` reads, kept: the replies' `reply_tcb` and the
TCBs' state. -/
def UFrame (σ σ' : State Unit) : Prop :=
  (∀ p x, σ.kheap p = some (.reply x) → ∃ x', σ'.kheap p = some (.reply x') ∧ x'.replyTcb = x.replyTcb) ∧
  (∀ p x, σ.kheap p = some (.tcb x) → ∃ x', σ'.kheap p = some (.tcb x') ∧ x'.tcbState = x.tcbState)

theorem UFrame.refl (σ : State Unit) : UFrame σ σ :=
  ⟨fun _ x h => ⟨x, h, rfl⟩, fun _ x h => ⟨x, h, rfl⟩⟩

theorem UFrame.trans {σ σ1 σ2 : State Unit} (h1 : UFrame σ σ1) (h2 : UFrame σ1 σ2) : UFrame σ σ2 := by
  refine ⟨fun p x hp => ?_, fun p x hp => ?_⟩
  · obtain ⟨y, hy, e⟩ := h1.1 p x hp; obtain ⟨z, hz, e'⟩ := h2.1 p y hy; exact ⟨z, hz, e'.trans e⟩
  · obtain ⟨y, hy, e⟩ := h1.2 p x hp; obtain ⟨z, hz, e'⟩ := h2.2 p y hy; exact ⟨z, hz, e'.trans e⟩

/-- A step changing only SCs. -/
theorem UFrame.updSc {σ : State Unit} {p : ObjRef} {y y' : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext y n)) : UFrame σ (updK σ p (.schedContext y' n)) := by
  refine ⟨fun q x hq => ⟨x, ?_, rfl⟩, fun q x hq => ⟨x, ?_, rfl⟩⟩ <;>
  · have : q ≠ p := by rintro rfl; rw [hk] at hq; cases hq
    simp [updK, this, hq]

end Spec

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

theorem scReplyA_eq (sc : U64) : scReplyA sc = scW sc 32#u64 := by unfold scReplyA scW layout.sc.REPLY; rfl

theorem rz_next : (0#u64 &&& ~~~1#u64) ||| 0#u64 = 0#u64 := by
  apply eq_of_bv; have : (0#u64).bv = 0#64 := rfl; simp [this]

/-- Writing an SC's `REPLY` word (the spec's `sc_replies` is not read by the
SC relation). -/
theorem SchedRel.set_sc_reply {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {sc : U64} (hsc : sc ∈ C) {x : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap sc.bv = some (.schedContext x n)) (v : U64) (l : List Fl4Spec.ObjRef) :
    SchedRel st N T C c (L.wr s (scReplyA sc) v) (updSc σ sc.bv { x with scReplies := l } n) ∧
      FootEq N T (L.mem s) (L.mem (L.wr s (scReplyA sc) v)) ∧
      KView σ (updSc σ sc.bv { x with scReplies := l } n) ∧
      (∀ K' : U64, K'.val < 96 → K'.val % 8 = 0 → K' ≠ 32#u64 →
        L.mem (L.wr s (scReplyA sc) v) (scW sc K') = L.mem s (scW sc K')) := by
  rw [scReplyA_eq]
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x', n', hk', hx⟩ := hs.scs sc hsc
  rw [hk] at hk'; cases hk'
  obtain ⟨hW', ep, em, hrs, hw, hv, hwr⟩ := hx.wr_hdr (K := 32#u64) (by simp [HdrK]) v
  have hx' : ScRel1 st (L.wr s (scW sc 32#u64) v) sc { x with scReplies := l } n :=
    ⟨hW', by rw [ep]; exact hx.period, by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.consumed,
      by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.tcb,
      by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.ntfn,
      by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.badge,
      by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.yieldFrom,
      by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.sporadic, by rw [em]; exact hx.max,
      by rw [hrs]; exact hx.refills⟩
  exact ⟨hS.sc_update hsc hk (hwr.mono fun b hb => hx.in_obj hb) (hw _ (by simp) (by simp) (by decide)) _ hx',
    scin_footEq hS hsc hwr, KView.of_sc hk, hw⟩

/-- A spec step changing only reply objects. -/
theorem NtfnStepW.updReply {σ : Fl4Spec.State Unit} {r : Fl4Spec.ObjRef} {x : Fl4Spec.Reply}
    (hk : σ.kheap r = some (.reply x)) (x' : Fl4Spec.Reply) : NtfnStepW σ (updK σ r (.reply x')) := by
  refine ⟨rfl, rfl, fun q => ?_⟩
  by_cases e : q = r
  · subst e; exact Or.inr (Or.inr (Or.inr ⟨x, x', hk, by simp [updK]⟩))
  · exact Or.inl (by simp [updK, e])

theorem KView.updReply {σ : Fl4Spec.State Unit} {r : Fl4Spec.ObjRef} {x : Fl4Spec.Reply}
    (hk : σ.kheap r = some (.reply x)) (x' : Fl4Spec.Reply) : KView σ (updK σ r (.reply x')) := by
  refine ⟨fun q y hq => ?_, fun q y hq => ⟨y, ?_, rfl, rfl, rfl⟩⟩
  · have : q ≠ r := by rintro rfl; rw [hk] at hq; cases hq
    simp [updK, this, hq]
  · have : q ≠ r := by rintro rfl; rw [hk] at hq; cases hq
    simp [updK, this, hq]

theorem NSC.updReply {N C : Set U64} {σ : Fl4Spec.State Unit} (h : NSC N C σ) {r : Fl4Spec.ObjRef}
    {x : Fl4Spec.Reply} (hk : σ.kheap r = some (.reply x)) (x' : Fl4Spec.Reply) :
    NSC N C (updK σ r (.reply x')) := by
  intro m hm y q hy hq
  by_cases e : m.bv = r
  · rw [e] at hy; simp [updK] at hy
  · simp only [updK_kheap, Function.update_of_ne e] at hy; exact h m hm y q hy hq


/-- **The call-stack relation reads only the call-stack words** and the spec's
`sc_replies`, `reply_sc`. -/
theorem CallRel.frame {R C : Set U64} {m m' : U64 → U64} {σ σ' : Fl4Spec.State Unit} {Lst : U64 → List U64}
    (h : CallRel m R C σ Lst) (hs : ∀ sc ∈ C, m' (scReplyA sc) = m (scReplyA sc))
    (hr : ∀ r ∈ R, m' (rPrevA r) = m (rPrevA r) ∧ m' (rNextA r) = m (rNextA r))
    (hsc : ∀ sc ∈ C, ∀ y n, σ.kheap sc.bv = some (.schedContext y n) →
      ∃ y', σ'.kheap sc.bv = some (.schedContext y' n) ∧ y'.scReplies = y.scReplies)
    (hrp : ∀ r ∈ R, ∀ x, σ.kheap r.bv = some (.reply x) → ∃ x', σ'.kheap r.bv = some (.reply x') ∧
      x'.replySc = x.replySc) :
    CallRel m' R C σ' Lst := by
  refine ⟨fun sc hsc' => ?_, h.excl, fun r hr' => ?_, fun d hd hdd => ?_⟩
  · obtain ⟨⟨y, n, hk, hy⟩, h1, h2, h3, h4⟩ := h.stack sc hsc'
    obtain ⟨y', hk', hy'⟩ := hsc sc hsc' y n hk
    refine ⟨⟨y', n, hk', hy'.trans hy⟩, h1, h2, by rw [hs sc hsc']; exact h3, fun i hi => ?_⟩
    have hm := h1 _ (List.getElem_mem hi)
    rw [(hr _ hm).1, (hr _ hm).2]; exact h4 i hi
  · obtain ⟨x, hk, hx⟩ := h.reply r hr'
    obtain ⟨x', hk', hx'⟩ := hrp r hr' x hk
    exact ⟨x', hk', fun p => by rw [hx']; exact hx p⟩
  · obtain ⟨t1, t2, t3⟩ := h.det d hd hdd
    rw [(hr d hd).1, (hr d hd).2]
    refine ⟨t1, fun hne => ?_, fun hne => ?_⟩
    · obtain ⟨g1, g2, g3⟩ := t2 hne
      exact ⟨g1, g2, by rw [(hr _ g1).1]; exact g3⟩
    · obtain ⟨g1, g2, g3⟩ := t3 hne
      exact ⟨g1, g2, by rw [(hr _ g1).2]; exact g3⟩

/-- A write in the scheduler footprint keeps the call-stack words. -/
theorem callWords_of_sfoot {N T C R : Set U64} {c : U64} {s s' : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (hRP : RPlaced st N T C R c s σ) (hw : WritesIn st s s' (SFoot st T c s)) :
    (∀ sc ∈ C, L.mem s' (scReplyA sc) = L.mem s (scReplyA sc)) ∧
    (∀ r ∈ R, L.mem s' (rPrevA r) = L.mem s (rPrevA r) ∧ L.mem s' (rNextA r) = L.mem s (rNextA r)) := by
  obtain ⟨Q0, R0, hc0, -⟩ := hS.lists
  refine ⟨fun sc hsc => ?_, fun r hr => ?_⟩
  · obtain ⟨Q, R', hc, hs⟩ := hS.lists
    obtain ⟨x, n, hk, hx⟩ := hs.scs sc hsc
    have ha := hx.hdr (K := 32#u64) (by simp) (by simp)
    rw [scReplyA_eq]
    refine hw.mem_eq ha.1 ?_
    obtain ⟨-, h2, h3, -⟩ := hS.scOutIn hsc ha.2
    intro hb
    rcases hb.range hc0.tcbs with ⟨y, hy, g1, g2⟩ | ⟨g1, g2⟩
    · have := h3 y hy; omega
    · omega
  · have hA := hRP.align r hr
    have k1 := hRP.ksb r hr
    have k2 := hRP.tcb r hr
    have v1 := rPrevA_val hA
    have v2 := rNextA_val hA
    refine ⟨hw.mem_eq (hRP.aligned hr (Or.inl v1)) ?_, hw.mem_eq (hRP.aligned hr (Or.inr v2)) ?_⟩
    · intro hb
      rcases hb.range hc0.tcbs with ⟨y, hy, g1, g2⟩ | ⟨g1, g2⟩
      · have := k2 y hy; omega
      · simp only [LawfulStore.nodeBase] at k1 g1 g2; omega
    · intro hb
      rcases hb.range hc0.tcbs with ⟨y, hy, g1, g2⟩ | ⟨g1, g2⟩
      · have := k2 y hy; omega
      · simp only [LawfulStore.nodeBase] at k1 g1 g2; omega

/-- **The call-stack words**: the replies' `PREV`, `NEXT` and `TCB` words and
the SCs' `REPLY` words, what `reply_remove`, `reply_pop` and `reply_unlink`
write besides the scheduler's footprint. -/
def CallW (R C : Set U64) (b : U64) : Prop :=
  (∃ r ∈ R, b = rNextA r ∨ b = rPrevA r ∨ b = rTcbA r) ∨ (∃ q ∈ C, b = scReplyA q)

/-- **A call-stack step on `r`**: the replies off every stack with no links
(other than `r`) keep their words, no stack gains a reply, and `r` leaves
every stack. -/
def CallStep (m m' : U64 → U64) (R C : Set U64) (Lst Lst' : U64 → List U64) (r : U64) : Prop :=
  (∀ d ∈ R, Detached C Lst d → m (rNextA d) = 0#u64 → m (rPrevA d) = 0#u64 → d ≠ r →
    m' (rNextA d) = m (rNextA d) ∧ m' (rPrevA d) = m (rPrevA d)) ∧
  (∀ q ∈ C, ∀ d ∈ Lst' q, d ∈ Lst q) ∧ Detached C Lst' r

/-- A free reply: its `reply_tcb` is `None`. -/
def Free (σ : Fl4Spec.State Unit) (d : U64) : Prop := ∃ x, σ.kheap d.bv = some (.reply x) ∧ x.replyTcb = none

/-- **Free replies are on no call stack and have no links** (so they are
isolated, `CallRel.isolated`): the invariant that gives `reply_push` its
isolated reply. -/
def RFree (m : U64 → U64) (R C : Set U64) (σ : Fl4Spec.State Unit) (Lst : U64 → List U64) : Prop :=
  ∀ d ∈ R, Free σ d → Detached C Lst d ∧ m (rNextA d) = 0#u64 ∧ m (rPrevA d) = 0#u64

/-- `RFree` across a call-stack step on `r` that frees at most `r`, leaving it
unlinked. -/
theorem RFree.step {R C : Set U64} {m m' : U64 → U64} {σ σ' : Fl4Spec.State Unit} {Lst Lst' : U64 → List U64}
    {r : U64} (h : RFree m R C σ Lst) (hcs : CallStep m m' R C Lst Lst' r)
    (hf : ∀ d ∈ R, Free σ' d → d ≠ r → Free σ d)
    (hr : Free σ' r → m' (rNextA r) = 0#u64 ∧ m' (rPrevA r) = 0#u64) : RFree m' R C σ' Lst' := by
  intro d hd hfd
  by_cases e : d = r
  · subst e; exact ⟨hcs.2.2, hr hfd⟩
  · obtain ⟨hdet, h0n, h0p⟩ := h d hd (hf d hd hfd e)
    obtain ⟨e1, e2⟩ := hcs.1 d hd hdet h0n h0p e
    exact ⟨fun q hq hm => hdet q hq (hcs.2.1 q hq d hm), e1.trans h0n, e2.trans h0p⟩

/-- `RFree` across a step that keeps the call-stack words and the stacks and
frees no reply. -/
theorem RFree.frame {R C : Set U64} {m m' : U64 → U64} {σ σ' : Fl4Spec.State Unit} {Lst : U64 → List U64}
    (h : RFree m R C σ Lst)
    (hm : ∀ d ∈ R, m' (rPrevA d) = m (rPrevA d) ∧ m' (rNextA d) = m (rNextA d))
    (hf : ∀ d ∈ R, Free σ' d → Free σ d) : RFree m' R C σ' Lst := by
  intro d hd hfd
  obtain ⟨hdet, h0n, h0p⟩ := h d hd (hf d hd hfd)
  exact ⟨hdet, (hm d hd).2.trans h0n, (hm d hd).1.trans h0p⟩

end

end

end Fl4Proofs.P3.Sched
