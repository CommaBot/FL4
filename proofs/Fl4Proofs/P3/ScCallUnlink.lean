/-
P3 (DESIGN.md §9), scheduling contexts: **`reply_unlink` against l4v
`reply_unlink_tcb`** (`reply_unlink_refines`), discharging the continuation
`hU` of `reply_pop_refines` and `reply_remove_refines`.

What the Ep side provides: the reply's `reply_tcb` is the thread
(`hrt`), and the thread is blocked on the reply (`hts`: `BlockedOnReply r`,
or `BlockedOnReceive _ (some r) _`): l4v's two assertions. The reply's
`TCB` word (`reply_tcb` in FL4) is the Ep relation's; here it is only
written (outside what the scheduler and call-stack relations read).
-/
import Fl4Proofs.P3.ScCallRemove
import Fl4Proofs.P3.ScYieldTo
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-- **Deactivating a thread that is not runnable keeps the invariant.** -/
theorem Inv.deactivate {σ : State Unit} (h : Inv σ) {p : ObjRef} {x : Tcb}
    (hk : σ.kheap p = some (.tcb x)) (hnr : runnable x.tcbState = false) :
    Inv (stsAct (updK σ p (.tcb { x with tcbState := .inactive })) p) := by
  have h1 : Inv (updK σ p (.tcb { x with tcbState := .inactive })) := by
    refine h.step (NtfnStep.tcb hk .inactive x.tcbArch) (fun u x' y h1 h2 _ hr => ?_) (fun u x' y h1 h2 hc => ?_)
    · by_cases e : u = p
      · subst e; rw [hk] at h1; cases h1; rw [hnr] at hr; cases hr
      · have : y = x' := by
          have h2' : σ.kheap u = some (.tcb y) := by simpa [updK, e] using h2
          rw [h1] at h2'; cases h2'; rfl
        rw [this]; exact hr
    · by_cases e : u = p
      · subst e
        simp only [updK_kheap, Function.update_self, Option.some.injEq, KernelObject.tcb.injEq] at h2
        subst h2
        rcases hc with hc | ⟨n, hc⟩ <;> cases hc
      · have h2' : σ.kheap u = some (.tcb y) := by simpa [updK, e] using h2
        exact h.rd u y h2' hc
  exact h1.qchange (qchange_stsAct _ _)

/-- The spec's `reply_unlink_tcb`, under its two assertions. -/
theorem replyUnlinkTcb_eq {σ : State Unit} {t r : ObjRef} {xr : Reply} {xt : Tcb}
    (hkr : σ.kheap r = some (.reply xr)) (hrt : xr.replyTcb = some t)
    (hkt : σ.kheap t = some (.tcb xt))
    (hts : xt.tcbState = .blockedOnReply r ∨ ∃ ep d, xt.tcbState = .blockedOnReceive ep (some r) d)
    (htr : t ≠ r) :
    replyUnlinkTcb (Z := Unit) t r σ = setThreadState (Z := Unit) t .inactive
      (updK σ r (.reply { xr with replyTcb := none })) := by
  unfold replyUnlinkTcb
  rw [nd_bind_one (Fl4Proofs.P3.Endp.getReply_eq hkr)]
  have hass : (NonDet.assert (xr.replyTcb = some t) : SMonad Unit Unit) σ = ({((), σ)}, False) := by
    show (({x | xr.replyTcb = some t ∧ x = ((), σ)}, ¬ xr.replyTcb = some t) :
      Set (Unit × State Unit) × Prop) = ({((), σ)}, False)
    simp [hrt]
  rw [nd_bind_one hass, nd_bind_one (getThreadState_eq hkt)]
  have hass2 : (NonDet.assert (xt.tcbState = .blockedOnReply r ∨ ∃ ep d, xt.tcbState = .blockedOnReceive ep (some r) d) :
      SMonad Unit Unit) σ = ({((), σ)}, False) := by
    show (({x | (xt.tcbState = .blockedOnReply r ∨ ∃ ep d, xt.tcbState = .blockedOnReceive ep (some r) d) ∧
      x = ((), σ)}, ¬ (xt.tcbState = .blockedOnReply r ∨ ∃ ep d, xt.tcbState = .blockedOnReceive ep (some r) d)) :
      Set (Unit × State Unit) × Prop) = ({((), σ)}, False)
    simp only [hts, true_and, not_true_eq_false]
    rfl
  rw [nd_bind_one hass2]
  have hset : setReplyObjRef (Z := Unit) replyTcbUpdate r none σ =
      ({((), updK σ r (.reply { xr with replyTcb := none }))}, False) := by
    show updateSkObjRef KernelObject.reply replyTcbUpdate r none σ = _
    unfold updateSkObjRef
    rw [nd_bind_one (Fl4Proofs.P3.Endp.getReply_eq hkr)]
    exact Fl4Proofs.P3.Endp.setReply_eq _ hkr
  rw [nd_bind_one hset]

end Spec

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

theorem rTcbA_val {r : U64} (h : r.val % 32 = 0 ∧ r ≠ 0#u64 ∧ r.val + 32 ≤ 2 ^ 64) : (rTcbA r).val = r.val := by
  unfold rTcbA layout.reply.TCB; rw [rword_val h (by simp)]; rfl

/-- `schedule_tcb` writes at most the action word (in the scheduler footprint). -/
theorem schedule_tcb_sfoot {N T C : Set U64} {c : U64} {s s1 : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (h1 : WritesIn st s s1 (SFoot st T c s)) (t : U64) :
    sched.schedule_tcb st s1 t ⦃ s' => WritesIn st s s' (SFoot st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hN := hc.node
  have hact : sched.set_action st s1 sched.ACTION_CHOOSE_NEW ⦃ s' => WritesIn st s s' (SFoot st T c s) ⦄ := by
    refine WP.spec_mono (sched.set_action.spec' s1 _) ?_
    rintro s' rfl
    have ho : (layout.node.SCHED_ACTION).val < 4288 := by simp [layout.node.SCHED_ACTION]
    refine (h1.trans ((writesIn_wr ?_).mono fun b hb => ?_)).mono fun b hb => by rcases hb with hb | hb <;> exact hb
    · rw [nodeAt_ksb h1.1, h1.2.1, hc.cur]; exact nodeAt_aligned hN ho (by simp [layout.node.SCHED_ACTION])
    · rw [hb, nodeAt_ksb h1.1, h1.2.1, hc.cur]
      exact Or.inr ⟨by rw [nodeAt_val hN ho]; omega, by rw [nodeAt_val hN ho]; omega⟩
  unfold sched.schedule_tcb
  step with sched.cur_thread.spec' as ⟨t1, _ht1⟩
  step as ⟨b, _hb⟩
  split
  · step with sched.action.spec' as ⟨i, _hi⟩
    split
    · step with sched.is_schedulable.spec' as ⟨b1, _hb1⟩
      split
      · exact (WP.spec_ok _).mpr h1
      · exact hact
    · exact (WP.spec_ok _).mpr h1
  · exact (WP.spec_ok _).mpr h1

/-- `set_thread_state` writes in the scheduler footprint. -/
theorem set_thread_state_sfoot {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {t : U64} (ht : t ∈ T) (v : U64) :
    sched.set_thread_state st s t v ⦃ s' => WritesIn st s s' (SFoot st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  unfold sched.set_thread_state
  step
  subst s1_post
  rw [show stA t = tStA t from rfl, tStA_eq]
  exact schedule_tcb_sfoot hS (writesIn_tcb hc.tcbs ht (by simp) (by simp) v) t

/-- **`reply_unlink` refines l4v `reply_unlink_tcb`**, given its assertions
(the Ep side's: `hrt`, `hts`): the relations, the call-stack relation and
the reply's isolation are kept, and `ActIdle`. -/
theorem reply_unlink_refines {N T C R : Set U64} {c : U64} (s : S) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    {Lst : U64 → List U64} (hCR : CallRel (L.mem s) R C σ Lst) (hRP : RPlaced st N T C R c s σ)
    {r : U64} (hr : r ∈ R) (hiso : Isolated (L.mem s) R r)
    {t : U64} (ht : t ∈ T) {xr : Fl4Spec.Reply} (hkr : σ.kheap r.bv = some (.reply xr))
    (hrt : xr.replyTcb = some t.bv) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hts : xt.tcbState = .blockedOnReply r.bv ∨ ∃ ep d, xt.tcbState = .blockedOnReceive ep (some r.bv) d) :
    ipc.reply_unlink st s r t ⦃ s' => ∃ σ', Fl4Spec.replyUnlinkTcb (Z := Unit) t.bv r.bv σ = ({((), σ')}, False) ∧
      SchedRel st N T C c s' σ' ∧ NtfnStateRel N T (L.mem s') σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      CallRel (L.mem s') R C σ' Lst ∧ RPlaced st N T C R c s' σ' ∧ Isolated (L.mem s') R r ∧
      (∃ x', σ'.kheap r.bv = some (.reply x') ∧ x'.replyTcb = none ∧ x'.replySc = xr.replySc) ∧
      (ActIdle σ → ActIdle σ') ∧
      (∀ d ∈ R, L.mem s' (rNextA d) = L.mem s (rNextA d) ∧ L.mem s' (rPrevA d) = L.mem s (rPrevA d)) ∧
      (∀ q, q ≠ r.bv → q ≠ t.bv → σ'.kheap q = σ.kheap q) ⦄ := by
  obtain ⟨Q, R', hc, hs⟩ := hS.lists
  have hP := hS.placed
  have hA := hRP.align r hr
  have htr : t.bv ≠ r.bv := fun e => by rw [e, hkr] at hkt; cases hkt
  have hnr : Fl4Spec.runnable xt.tcbState = false := by
    rcases hts with h | ⟨_, _, h⟩ <;> rw [h] <;> rfl
  have hnb : ∀ n, xt.tcbState ≠ .blockedOnNotification n := by
    intro n h; rcases hts with h' | ⟨_, _, h'⟩ <;> rw [h'] at h <;> cases h
  -- the reply's `TCB` word
  have hva := rTcbA_val hA
  have hal : Aligned (rTcbA r) := by unfold Aligned; rw [hva]; omega
  have hfar : Far st T C c s σ (rTcbA r) := by
    refine ⟨?_, fun t ht => ?_, fun sc hsc x n hx => ?_⟩
    · have := hRP.ksb r hr; rw [hva]; omega
    · have := hRP.tcb r hr t ht; rw [hva]; omega
    · have := hRP.sc r hr sc hsc x n hx; rw [hva]; omega
  unfold ipc.reply_unlink
  refine WP.spec_bind (obj.Reply.set_tcb.spec s r 0#u64) ?_
  rintro s1 rfl
  set σa := updK σ r.bv (.reply { xr with replyTcb := none }) with hσa
  have hS1 := (hS.wr_far hal hfar 0#u64).stableW (WritesIn.refl _ _) (NtfnStepW.updReply hkr { xr with replyTcb := none })
  have hR1 : NtfnStateRel N T (L.mem (L.wr s (rTcbA r) 0#u64)) σa :=
    hR.frame hP (footEq_wr_far hP hal (fun n hn => by have := hRP.ntfn r hr n hn; rw [hva]; omega)
      (fun t ht => by have := hRP.tcb r hr t ht; rw [hva]; omega) _) (KView.updReply hkr _)
  have hN1 : NSC N C σa := hN.updReply hkr _
  have hI1 : Inv σa := hI.updReply hkr
  have hmw : ∀ b, Aligned b → b.val ≠ r.val → L.mem (L.wr s (rTcbA r) 0#u64) b = L.mem s b :=
    fun b hb hne => L.mem_wr_ne hal hb (by rw [hva]; exact Ne.symm hne)
  have hkra : σa.kheap r.bv = some (.reply { xr with replyTcb := none }) := by simp [σa, updK]
  have hko : ∀ q, q ≠ r.bv → σa.kheap q = σ.kheap q := fun q hq => by simp [σa, updK, hq]
  have hCR1 : CallRel (L.mem (L.wr s (rTcbA r) 0#u64)) R C σa Lst := by
    refine hCR.frame (fun q hq => ?_) (fun d hd => ⟨?_, ?_⟩) (fun q hq y n hy => ?_) (fun d hd x hx => ?_)
    · obtain ⟨haq, hvq, hszq⟩ := sc_reply_word hS hq
      obtain ⟨xq, nq, hkq, -⟩ := hs.scs q hq
      refine hmw _ haq ?_
      have := hRP.sc r hr q hq xq nq hkq; have := hszq xq nq hkq; rw [hvq]; omega
    · have hAd := hRP.align d hd
      refine hmw _ (hRP.aligned hd (Or.inl (rPrevA_val hAd))) ?_
      rw [rPrevA_val hAd]; omega
    · have hAd := hRP.align d hd
      refine hmw _ (hRP.aligned hd (Or.inr (rNextA_val hAd))) ?_
      rw [rNextA_val hAd]; omega
    · have hq' : q.bv ≠ r.bv := fun e => by rw [e, hkr] at hy; cases hy
      exact ⟨y, by rw [hko _ hq']; exact hy, rfl⟩
    · by_cases e : d.bv = r.bv
      · rw [e, hkr] at hx; cases hx; exact ⟨{ xr with replyTcb := none }, by rw [e]; exact hkra, rfl⟩
      · exact ⟨x, by rw [hko _ e]; exact hx, rfl⟩
  have hRP1 : RPlaced st N T C R c (L.wr s (rTcbA r) 0#u64) σa :=
    hRP.frame (by simp) (SzKeep.updK hkr fun _ _ e => by cases e)
  have hiso1 : Isolated (L.mem (L.wr s (rTcbA r) 0#u64)) R r := by
    obtain ⟨i1, i2, i3⟩ := hiso
    have hAr := hRP.align r hr
    refine ⟨by rw [hmw _ (hRP.aligned hr (Or.inr (rNextA_val hAr))) (by rw [rNextA_val hAr]; omega)]; exact i1,
      by rw [hmw _ (hRP.aligned hr (Or.inl (rPrevA_val hAr))) (by rw [rPrevA_val hAr]; omega)]; exact i2,
      fun d hd => ?_⟩
    have hAd := hRP.align d hd
    rw [hmw _ (hRP.aligned hd (Or.inr (rNextA_val hAd))) (by rw [rNextA_val hAd]; omega),
      hmw _ (hRP.aligned hd (Or.inl (rPrevA_val hAd))) (by rw [rPrevA_val hAd]; omega)]
    exact i3 d hd
  have hkta : σa.kheap t.bv = some (.tcb xt) := by rw [hko _ htr]; exact hkt
  -- the thread's state
  refine WP.spec_mono (WP.spec_and (set_thread_state_refines _ σa hR1 hS1 ht hkta
    (fun n hn z hz hm => by
      obtain ⟨z', hz', hrz⟩ := hR1.ntfn n hn
      rw [hz] at hz'; cases hz'
      have hst := (hR1.at_tcb ht hkta).st
      have obj := hrz.obj
      revert hm obj
      cases z.ntfnObj with
      | idleNtfn => intro hm; simp [Fl4Spec.Ntfn.ntfnQueue] at hm
      | activeNtfn b => intro hm; simp [Fl4Spec.Ntfn.ntfnQueue] at hm
      | waitingNtfn q =>
        intro hm obj
        obtain ⟨-, xs, -, rfl, -, hb⟩ := obj
        have h6 := (hb t (mem_map_bv.1 hm)).1
        rw [hst] at h6
        rcases hts with h | ⟨_, _, h⟩ <;> rw [h] at h6 <;> simp [tsCode] at h6)
    sched.TS_INACTIVE .inactive (by unfold sched.TS_INACTIVE; rfl) (fun n h => by cases h))
    (set_thread_state_sfoot hS1 ht _)) ?_
  rintro s2 ⟨⟨σ2, he2, hR2, hS2⟩, hw2⟩
  have hσ2 := the_result (Fl4Proofs.P3.Notif.setThreadState_eq .inactive hkta) he2
  obtain ⟨hcs, hcr⟩ := callWords_of_sfoot hS1 hRP1 hw2
  have hk2 : ∀ q, q ≠ t.bv → σ2.kheap q = σa.kheap q := fun q hq => by
    rw [hσ2, stsAct_kheap]; simp [updK, hq]
  refine ⟨σ2, by rw [replyUnlinkTcb_eq hkr hrt hkt hts htr]; exact he2, hS2, hR2, ?_,
    by rw [hσ2]; exact hI1.deactivate hkta hnr, ?_, ?_, ?_, ?_, fun hAI => ?_, fun d hd => ?_,
    fun q hq1 hq2 => by rw [hk2 _ hq2, hko _ hq1]⟩
  · rw [hσ2]; unfold Fl4Proofs.P3.Notif.stsAct; split <;> exact hN1.updTcb
  · refine hCR1.frame hcs hcr (fun q hq y n hy => ⟨y, ?_, rfl⟩) (fun d hd x hx => ⟨x, ?_, rfl⟩)
    · have : q.bv ≠ t.bv := fun e => by rw [e, hkta] at hy; cases hy
      rw [hk2 _ this]; exact hy
    · have : d.bv ≠ t.bv := fun e => by rw [e, hkta] at hx; cases hx
      rw [hk2 _ this]; exact hx
  · refine hRP1.frame hw2.1 fun q y n hq => ⟨y, ?_⟩
    have : q ≠ t.bv := fun e => by rw [e, hσ2, stsAct_kheap] at hq; simp [updK] at hq
    rw [← hk2 _ this]; exact hq
  · obtain ⟨i1, i2, i3⟩ := hiso1
    refine ⟨by rw [(hcr r hr).2]; exact i1, by rw [(hcr r hr).1]; exact i2, fun d hd => ?_⟩
    rw [(hcr d hd).1, (hcr d hd).2]; exact i3 d hd
  · exact ⟨{ xr with replyTcb := none }, by rw [hk2 _ (Ne.symm htr)]; exact hkra, rfl, rfl⟩
  · have hAa : ActIdle σa := hAI.keep (TKeepE.updReply _ hkr _) (fun _ h => h) (Or.inl rfl) rfl
    rw [hσ2]
    refine ActIdle.ofSts (ActIdle.block (t := t.bv) hAa (NtfnStep.tcb hkta .inactive xt.tcbArch) ?_ ?_ ?_) _
    · intro p x y h1 h2 hp
      have h2' : σa.kheap p = some (.tcb y) := by simpa [updK, hp] using h2
      rw [h1] at h2'; cases h2'; rfl
    · intro u hu e
      subst e
      obtain ⟨x', -, -, -, h1, -, h3, -⟩ := schedulable_inv (hAa.1 _ hu)
      rw [hkta] at h1; cases h1; rw [hnr] at h3; cases h3
    · intro e
      obtain ⟨xi, h1, -, h3, -⟩ := hAa.2
      rw [← e, hkta] at h1; cases h1
      rcases hts with h | ⟨_, _, h⟩ <;> rw [h] at h3 <;> cases h3
  · have hAd := hRP.align d hd
    rw [(hcr d hd).2, (hcr d hd).1,
      hmw _ (hRP.aligned hd (Or.inr (rNextA_val hAd))) (by rw [rNextA_val hAd]; omega),
      hmw _ (hRP.aligned hd (Or.inl (rPrevA_val hAd))) (by rw [rPrevA_val hAd]; omega)]
    exact ⟨rfl, rfl⟩

theorem nd_assoc_f {σ' α β γ : Type} (m : Fl4Spec.NonDet σ' α) (f : α → Fl4Spec.NonDet σ' β)
    (g : β → Fl4Spec.NonDet σ' γ) : ((m >>= f) >>= g) = (m >>= fun a => f a >>= g) := by
  funext s
  simp only [nd_bind_apply']
  refine Prod.ext (Set.ext fun r => ?_) (propext ?_)
  · simp only [Set.mem_setOf_eq]; constructor
    · rintro ⟨x, ⟨y, hy, hx⟩, hr⟩; exact ⟨y, hy, x, hx, hr⟩
    · rintro ⟨y, hy, x, hx, hr⟩; exact ⟨x, ⟨y, hy, hx⟩, hr⟩
  · simp only [Set.mem_setOf_eq]; constructor
    · rintro ((h | ⟨y, hy, h⟩) | ⟨x, ⟨y, hy, hx⟩, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨y, hy, Or.inl h⟩
      · exact Or.inr ⟨y, hy, Or.inr ⟨x, hx, h⟩⟩
    · rintro (h | ⟨y, hy, h | ⟨x, hx, h⟩⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨y, hy, h⟩)
      · exact Or.inr ⟨x, ⟨y, hy, hx⟩, h⟩

/-- **`reply_remove` refines l4v `reply_remove`**: the call-stack part
(`reply_remove_refines`) and `reply_unlink_tcb` (`reply_unlink_refines`).
The Ep side provides l4v's assertions: the reply's `reply_tcb` is `t`
(`hrt`) and `t` is blocked on the reply (`hts`). -/
theorem reply_remove_full_refines {N T C R : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    {Lst : U64 → List U64} (hCR : CallRel (L.mem s) R C σ Lst) (hRP : RPlaced st N T C R c s σ)
    (hC0 : ∀ q ∈ C, q ≠ 0#u64)
    (hSCs : ∀ p y n, σ.kheap p = some (.schedContext y n) → ∃ q ∈ C, q.bv = p)
    {r : U64} (hr : r ∈ R) {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    {xr : Fl4Spec.Reply} (hkr : σ.kheap r.bv = some (.reply xr)) (hrt : xr.replyTcb = some t.bv)
    (hts : xt.tcbState = .blockedOnReply r.bv ∨ ∃ ep d, xt.tcbState = .blockedOnReceive ep (some r.bv) d)
    (hdon : ∀ sc ∈ C, ∀ y n, σ.kheap sc.bv = some (.schedContext y n) → (Lst sc).head? = some r →
      xt.tcbSchedContext = none → ∃ f, f ∈ T ∧ y.scTcb = some f.bv ∧ f ≠ t)
    (hrel : ∀ sc ∈ C, ∀ y n, σ.kheap sc.bv = some (.schedContext y n) → (Lst sc).head? = some r →
      xt.tcbSchedContext = none → inClass xt.tcbState → Fl4Spec.scActive y = true → released σ y)
    (hRF : RFree (L.mem s) R C σ Lst) :
    ipc.reply_remove st ar s a r t ⦃ res => res.2 = a ∧ ∃ (σ' : Fl4Spec.State Unit) (Lst' : U64 → List U64),
      Fl4Spec.replyRemove (Z := Unit) t.bv r.bv σ = ({((), σ')}, False) ∧
      SchedRel st N T C c res.1 σ' ∧ NtfnStateRel N T (L.mem res.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      CallRel (L.mem res.1) R C σ' Lst' ∧ RPlaced st N T C R c res.1 σ' ∧ Isolated (L.mem res.1) R r ∧
      RFree (L.mem res.1) R C σ' Lst' ∧ ∃ x', σ'.kheap r.bv = some (.reply x') ∧ x'.replyTcb = none ⦄ := by
  refine reply_remove_refines s a σ hS hR hN hI hCR hRP hC0 hSCs hr ht hkt hdon hrel _ ?_
  intro s5 σ5 Lst5 h1 h2 h3 h4 h5 h6 h7 huf hcs hsp
  obtain ⟨xr5, hkr5, er5⟩ := huf.1 _ xr hkr
  obtain ⟨xt5, hkt5, et5⟩ := huf.2 _ xt hkt
  refine WP.spec_mono (reply_unlink_refines s5 σ5 h1 h2 h3 h4 h5 h6 hr h7 ht hkr5 (er5.trans hrt) hkt5
    (by rw [et5]; exact hts)) ?_
  rintro s6 ⟨σ6, hul, hS6, hR6, hN6, hI6, hCR6, hRP6, hiso6, ⟨x', hkx, hx1, -⟩, -, hm6, hk6⟩
  have hRF6 : RFree (L.mem s6) R C σ6 Lst5 := by
    refine RFree.step hRF ⟨fun d hd hdet h0n h0p hdr => ?_, hcs.2.1, hcs.2.2⟩ (fun d hd hfd hdr => ?_)
      (fun _ => ⟨hiso6.1, hiso6.2.1⟩)
    · obtain ⟨e1, e2⟩ := hcs.1 d hd hdet h0n h0p hdr
      exact ⟨(hm6 d hd).1.trans e1, (hm6 d hd).2.trans e2⟩
    · obtain ⟨x6, hk6d, hx6⟩ := hfd
      have hdt : d.bv ≠ t.bv := fun e => by
        obtain ⟨xd, hkd, -⟩ := hCR.reply d hd
        rw [e, hkt] at hkd; cases hkd
      rw [hk6 _ (bv_ne hdr) hdt] at hk6d
      obtain ⟨xd, hkd, -⟩ := hCR.reply d hd
      obtain ⟨xd5, hkd5, ed⟩ := huf.1 _ xd hkd
      rw [hkd5] at hk6d; cases hk6d
      exact ⟨xd, hkd, ed ▸ hx6⟩
  refine ⟨rfl, σ6, Lst5, ?_, hS6, hR6, hN6, hI6, hCR6, hRP6, hiso6, hRF6, x', hkx, hx1⟩
  unfold replyRemoveSc at hsp
  rw [nd_gets_bind] at hsp
  unfold Fl4Spec.replyRemove
  rw [nd_bind_one (Fl4Proofs.P3.Endp.getReply_eq hkr)]
  have hass : (Fl4Spec.NonDet.assert (xr.replyTcb = some t.bv) : Fl4Spec.SMonad Unit Unit) σ = ({((), σ)}, False) := by
    show (({x | xr.replyTcb = some t.bv ∧ x = ((), σ)}, ¬ xr.replyTcb = some t.bv) :
      Set (Unit × Fl4Spec.State Unit) × Prop) = ({((), σ)}, False)
    simp [hrt]
  rw [nd_bind_one hass, nd_gets_bind]
  cases hw : Fl4Spec.scWithReply r.bv σ with
  | none =>
    rw [hw] at hsp
    have e := (nd_pure_one hsp).1
    subst e
    exact hul
  | some p =>
    rw [hw] at hsp
    dsimp only at hsp ⊢
    simp only [← nd_assoc_f]
    rw [nd_bind_one hsp]
    exact hul

end

end

end Fl4Proofs.P3.Sched
