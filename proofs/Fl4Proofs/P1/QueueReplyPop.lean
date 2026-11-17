/-
P1: `reply_pop`, `reply_remove` and the Reply branch of `finalise_cap`
keep `BlkOK`.  `reply_pop` breaks the reply-stack head link (`RHead`) for
two writes (the SC's `REPLY` word names the new head before the old head's
`NEXT` word is cleared); between them only `XInvR` (no `RHead`) is kept,
and `RHead` is re-established after the third write.
-/
import Fl4Proofs.P1.QueueFootD
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Es : Set U64}

theorem obj.Reply.next_raw.val (s : S) (r : obj.Reply) :
    obj.Reply.next_raw st r s ⦃ v => v = L.mem s (rNextA r) ⦄ := by
  unfold obj.Reply.next_raw; simp [lift, L.read_eq, rNextA]

theorem obj.Reply.set_next_raw.val (s : S) (r : obj.Reply) (v : U64) :
    obj.Reply.set_next_raw st r s v ⦃ s' => s' = L.wr s (rNextA r) v ⦄ := by
  unfold obj.Reply.set_next_raw
  simp only [lift, bind_ok, L.write_eq, WP.spec_ok]; rfl

/-- `link_all` with the reply-stack heads (`RHead`) not tracked: `XInvR`. -/
theorem link_allR {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {a w : U64}
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInvR st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s)
    (haΩ : a ∈ Ω) (ht : ∀ r ∈ Rp, a.val ≠ (rTcbA r).val)
    (hc : ∀ c ∈ Scs, a.val ≠ (scTcbA c).val ∧ a.val ≠ (scCoreA c).val ∧ a.val ≠ (maxA c).val ∧
      a.val ≠ (headA c).val ∧ a.val ≠ (tailA c).val)
    (hn : ∀ r ∈ Rp, a.val = (rNextA r).val → w &&& ~~~1#u64 ≠ 0#u64 →
      (headBit w = true → w &&& ~~~1#u64 ∈ Scs) ∧ (headBit w = false → w &&& ~~~1#u64 ∈ Rp))
    (hp : ∀ r ∈ Rp, a.val = (rPrevA r).val → w &&& ~~~1#u64 ≠ 0#u64 → w &&& ~~~1#u64 ∈ Rp)
    (hs : ∀ c ∈ Scs, a.val = (scReplyA c).val → w ≠ 0#u64 → w ∈ Rp ∧ c ∈ Ac ∧ L.mem s (scTcbA c) ≠ L.idleW s)
    (hnt : ∀ n ∈ Nt, a.val ≠ (ntfnScA n).val) (hnb : ∀ n ∈ Nt, a.val ≠ (ntfnBtA n).val)
    (hsn : ∀ c ∈ Scs, a.val ≠ (scNtfnA c).val) (hsy : ∀ c ∈ Scs, a.val ≠ (scYieldFromA c).val)
    (hsp : ∀ c ∈ Scs, a.val ≠ (sporA c).val) :
    SchedQueuesInv st T Cs Ω H (L.wr s a w) Q R ∧ BoundInv st T Ac (L.wr s a w) ∧
      XInvR st T Cs Ω Sg Rp Scs Nt Z (L.wr s a w) ∧ SCsOK st T Ω Sg Scs Z Ac (L.wr s a w) ∧
      SgOK st Ω Sg (L.wr s a w) ∧
      L.actionW (L.wr s a w) = L.actionW s ∧ L.idleW (L.wr s a w) = L.idleW s ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        L.mem (L.wr s a w) (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ b ∈ Ω, a.val ≠ b.val → L.mem (L.wr s a w) b = L.mem s b) := by
  have ho := h.omega a haΩ
  have hN := h.nodes _ h.cur
  obtain ⟨h1, ea, f⟩ := omega_wr (v := w) h haΩ
  have nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem (L.wr s a w) (L.nodeAt (L.wr s a w) (L.cpu (L.wr s a w)) o) = L.mem s (L.nodeAt s (L.cpu s) o) :=
    fun o h1 h2 => by
      simp only [LawfulStore.cpu_wr, nodeAt_wr]
      exact L.mem_wr_ne ho.1 (nodeAt_aligned hN h1 h2) (fun e => out_ne_node ho h.cur hN h1 e.symm)
  refine ⟨h1, BoundInv.owr h hB haΩ, XInvR.wr_linkT h hX hSg.sub haΩ ht
      (fun c hcs => ⟨(hc c hcs).1, (hc c hcs).2.1, (hc c hcs).2.2.1⟩)
      hn hp (fun c hc e h0 => ⟨(hs c hc e h0).1, (hs c hc e h0).2.2⟩) (fun n hn e => absurd e (hnt n hn))
      (fun c hc e => absurd e (hsn c hc)) (fun n hn e => absurd e (hnb n hn)) (fun c hc e => absurd e (hsn c hc))
      (fun c hc e => absurd e (hsy c hc)),
    SCsOK.wr' h hS hX.1 ho.1 (fun y hy => (out_ne_field (K := 3464#u64) ho hy (h.tcbs y hy) (by simp)).symm)
      (out_ne_node ho h.cur hN (by simp [layout.node.CUR_SC])).symm (fun c hcs => (hc c hcs).2.2) hsp
      (fun c hcs e h0 => (hs c hcs e h0).2.1),
    ⟨hSg.sub, fun b hb => by rw [L.ksb_wr]; exact hSg.ks b hb, fun o h1 h2 => by rw [L.ksb_wr]; exact hSg.ksΩ o h1 h2⟩,
    ea, nd _ (by rw [idle8]; omega) (by rw [idle8]), f,
    fun b hb hne => L.mem_wr_ne ho.1 (h.omega b hb).1 hne⟩

/-- A write of an SC's `REPLY` word (null or a reply object, the SC active). -/
theorem screp_wrR {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {c w : U64}
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInvR st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hc : c ∈ Scs) (hw : w ≠ 0#u64 → w ∈ Rp ∧ c ∈ Ac ∧ L.mem s (scTcbA c) ≠ L.idleW s) :
    SchedQueuesInv st T Cs Ω H (L.wr s (scReplyA c) w) Q R ∧ BoundInv st T Ac (L.wr s (scReplyA c) w) ∧
      XInvR st T Cs Ω Sg Rp Scs Nt Z (L.wr s (scReplyA c) w) ∧ SCsOK st T Ω Sg Scs Z Ac (L.wr s (scReplyA c) w) ∧
      SgOK st Ω Sg (L.wr s (scReplyA c) w) ∧
      L.actionW (L.wr s (scReplyA c) w) = L.actionW s ∧ L.idleW (L.wr s (scReplyA c) w) = L.idleW s ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        L.mem (L.wr s (scReplyA c) w) (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ b ∈ Ω, (scReplyA c).val ≠ b.val → L.mem (L.wr s (scReplyA c) w) b = L.mem s b) := by
  have hO := hX.1
  obtain ⟨hP, hz⟩ := hO.sc c hc
  have av := scReplyA_val hP hz
  obtain ⟨h128, -⟩ := sc_facts hO hc
  have hm : scReplyA c ∈ Ω := hSg.sub _ (hO.repW c hc)
  have same : ∀ c' ∈ Scs, (scReplyA c).val = (scReplyA c').val → c' = c := fun c' hc' e => by
    by_contra hne
    obtain ⟨-, -, -, -, -, -, e7, -⟩ := sc_facts hO hc'
    rw [av, e7] at e
    have := hO.scDisj c hc c' hc' (Ne.symm hne); have := (sc_facts hO hc').1; omega
  exact link_allR h hB hX hS hSg hm
    (fun r hr => by rw [av, (rp_facts hO hr).2.1]; have := hO.rpSc r hr c hc; omega)
    (fun c' hc' => by
      obtain ⟨h128', e1, e2, e3, e4, e5, -⟩ := sc_facts hO hc'
      rw [av, e1, e2, e3, e4, e5]
      by_cases e : c = c'
      · subst e; omega
      · have := hO.scDisj c hc c' hc' e; omega)
    (fun r hr e => by rw [av, (rp_facts hO hr).2.2.2] at e; have := hO.rpSc r hr c hc; omega)
    (fun r hr e => by rw [av, (rp_facts hO hr).2.2.1] at e; have := hO.rpSc r hr c hc; omega)
    (fun c' hc' e h0 => by rw [same c' hc' e]; exact hw h0)
    (fun n hn e => by
      rw [av, ntfnScA_val (hO.ntP n hn)] at e; have := hO.ntOSc n hn c hc; omega)
    (fun n hn e => by
      rw [av, ntfnBtA_val (hO.ntP n hn)] at e; have := hO.ntOSc n hn c hc; omega)
    (fun c' hc' e => by
      obtain ⟨hPc, hzc⟩ := hO.sc c' hc'
      exact scw_ne hO hc hc' av (scNtfnA_val hPc hzc) (by omega) (by omega) (by omega) e)
    (fun c' hc' e => by
      exact scw_ne hO hc hc' av (sc_facts hO hc').2.2.2.2.2.2.2 (by omega) (by omega) (by omega) e)
    (scw_ne_spor hO hc av (by omega) (by omega))

/-- A write of a reply's `PREV` or `NEXT` word. -/
theorem rword_wrR {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {r a w : U64}
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInvR st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hr : r ∈ Rp)
    (ha : a = rPrevA r ∨ a = rNextA r)
    (hn : a = rNextA r → w &&& ~~~1#u64 ≠ 0#u64 →
      (headBit w = true → w &&& ~~~1#u64 ∈ Scs) ∧ (headBit w = false → w &&& ~~~1#u64 ∈ Rp))
    (hp : a = rPrevA r → w &&& ~~~1#u64 ≠ 0#u64 → w &&& ~~~1#u64 ∈ Rp) :
    SchedQueuesInv st T Cs Ω H (L.wr s a w) Q R ∧ BoundInv st T Ac (L.wr s a w) ∧
      XInvR st T Cs Ω Sg Rp Scs Nt Z (L.wr s a w) ∧ SCsOK st T Ω Sg Scs Z Ac (L.wr s a w) ∧
      SgOK st Ω Sg (L.wr s a w) ∧
      L.actionW (L.wr s a w) = L.actionW s ∧ L.idleW (L.wr s a w) = L.idleW s ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        L.mem (L.wr s a w) (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ b ∈ Ω, a.val ≠ b.val → L.mem (L.wr s a w) b = L.mem s b) := by
  have hO := hX.1
  obtain ⟨r32, -, rp8, rn16⟩ := rp_facts hO hr
  have rr : ∀ r' ∈ Rp, r'.val % 32 = 0 := fun r' hr' => (hO.rp r' hr').1
  have hav : a.val = r.val + 8 ∨ a.val = r.val + 16 := by
    rcases ha with rfl | rfl
    · exact Or.inl rp8
    · exact Or.inr rn16
  have hin : r.val ≤ a.val ∧ a.val < r.val + 32 := by omega
  have hm : a ∈ Ω := by
    rcases ha with rfl | rfl
    · exact hSg.sub _ (hO.prevW hr)
    · exact hSg.sub _ (hO.nextW hr)
  have same : ∀ r' ∈ Rp, a.val = (rNextA r').val ∨ a.val = (rPrevA r').val → r' = r := fun r' hr' e =>
    UScalar.eq_of_val_eq (by
      rw [rNextA_val (hO.rp r' hr'), rPrevA_val (hO.rp r' hr')] at e
      have := rr r' hr'; have := rr r hr; omega)
  exact link_allR h hB hX hS hSg hm
    (fun r' hr' e => by rw [rTcbA_val (hO.rp r' hr')] at e; have := rr r' hr'; have := rr r hr; omega)
    (rword_ne_sc hO hr hin)
    (fun r' hr' e h0 => by
      have := same r' hr' (Or.inl e); subst this
      refine hn ?_ h0
      rcases ha with rfl | rfl
      · rw [rp8, rn16] at e; omega
      · rfl)
    (fun r' hr' e h0 => by
      have := same r' hr' (Or.inr e); subst this
      refine hp ?_ h0
      rcases ha with rfl | rfl
      · rfl
      · rw [rp8, rn16] at e; omega)
    (fun c hc e => absurd e (rword_ne_screp hO hr hin c hc))
    (fun n hn e => by have := hO.ntRp n hn r hr; omega)
    (fun n hn e => by rw [ntfnBtA_val (hO.ntP n hn)] at e; have := hO.ntORp n hn r hr; omega)
    (rword_ne_scn hO hr hin) (rword_ne_scy hO hr hin) (rword_ne_spor hO hr hin)

/-- `RHead` when every reply's `NEXT` word is kept or cleared and the SCs'
`REPLY` words are kept. -/
theorem RHead.keep0 {s s' : S} (h : RHead st Rp s)
    (hn : ∀ r ∈ Rp, L.mem s' (rNextA r) = L.mem s (rNextA r) ∨ L.mem s' (rNextA r) &&& ~~~1#u64 = 0#u64)
    (hsr : ∀ c ∈ Scs, L.mem s' (scReplyA c) = L.mem s (scReplyA c))
    (hnx : ∀ r ∈ Rp, L.mem s (rNextA r) &&& ~~~1#u64 ≠ 0#u64 → headBit (L.mem s (rNextA r)) = true →
      L.mem s (rNextA r) &&& ~~~1#u64 ∈ Scs) : RHead st Rp s' := fun r hr hb h0 => by
  rcases hn r hr with e | e
  · rw [e] at hb h0 ⊢
    rw [hsr _ (hnx r hr h0 hb)]; exact h r hr hb h0
  · exact absurd e h0

/-- `reply_unlink` of a thread blocked on the reply: `BlkOK` is kept and the
thread becomes inactive. -/
theorem ipc.reply_unlink.blk (s : S) (r t : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hr : r ∈ Rp)
    (ht : t ∈ T) (hrt : L.mem s (rTcbA r) = t) (hst : L.mem s (stA t) = sched.TS_BLOCKED_ON_REPLY) :
    ipc.reply_unlink st s r t ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      L.mem s' (stA t) = sched.TS_INACTIVE ∧ KeepT st T Cs Rp Scs Nt t s s' ∧ L.mem s' (rTcbA r) = 0#u64 ∧
      Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hnr : ¬ Runnable (L.mem s (stA t)) := by rw [hst]; exact not_runnable_reply
  refine WP.spec_mono (WP.spec_and (ipc.reply_unlink.inv s r t Q R h0 ht hX.1 hSg.sub hr hrt hnr
    (Or.inr (by rw [hst]; exact not_blocked_reply'))) (ipc.reply_unlink.kw (Es := Es) s r t h0 hX hSg.sub hr ht)) ?_
  rintro s' ⟨⟨h', e', k, z⟩, fk⟩
  have h'' : SchedQueuesInv st T Cs Ω H s' Q R := h'.congrX empty_congr
  have nb : ¬ Blocked (L.mem s' (stA t)) := by rw [e']; exact not_blocked_inactive
  have nrp : L.mem s' (stA t) ≠ sched.TS_BLOCKED_ON_REPLY := by rw [e', ts_inactive, ts_reply]; decide
  have nrc : L.mem s' (stA t) ≠ sched.TS_BLOCKED_ON_RECV := by
    rw [e', ts_inactive]; unfold sched.TS_BLOCKED_ON_RECV; decide
  have hclr : ∀ r' ∈ Rp, L.mem s (rTcbA r') = t → L.mem s' (rTcbA r') = 0#u64 := by
    intro r' hr' e
    have ht0 : t ≠ 0#u64 := fun e0 => (h0.tcbs t ht).ne0 (by rw [e0]; rfl)
    obtain ⟨-, -, b2, -⟩ := hX.2.1.back r' hr' (by rw [e]; exact ht0)
    obtain ⟨-, -, b2', -⟩ := hX.2.1.back r hr (by rw [hrt]; exact ht0)
    rw [e] at b2; rw [hrt] at b2'
    rw [← b2, b2']; exact z
  exact ⟨⟨⟨Q, R, h''⟩, hB.keepT h0 k nb nrp, XInv.keepT hX k ⟨nrp, nrc⟩ hclr, hS.keepT hX k,
    ⟨hSg.sub, fun b hb => by rw [k.ksb]; exact hSg.ks b hb, fun o h1 h2 => by rw [k.ksb]; exact hSg.ksΩ o h1 h2⟩⟩,
    e', k, z, fk⟩

/-- A write of a reply's `PREV` word keeps `BlkOK`. -/
theorem rprev_wr_all {s : S} {r w : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hr : r ∈ Rp)
    (hp : w &&& ~~~1#u64 ≠ 0#u64 → w &&& ~~~1#u64 ∈ Rp) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s (rPrevA r) w) ∧ L.actionW (L.wr s (rPrevA r) w) = L.actionW s ∧
      L.idleW (L.wr s (rPrevA r) w) = L.idleW s ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        L.mem (L.wr s (rPrevA r) w) (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ b ∈ Ω, (rPrevA r).val ≠ b.val → L.mem (L.wr s (rPrevA r) w) b = L.mem s b) := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hO := hX.1
  obtain ⟨h1, hB1, hX1, hS1, hSg1, a1, i1, f1, o1⟩ := rword_wrR (w := w) h0 hB hX.xr hS hSg hr (Or.inl rfl)
    (fun e => absurd (congrArg UScalar.val e) (by
      rw [rPrevA_val (hO.rp r hr), rNextA_val (hO.rp r hr)]; omega)) (fun _ => hp)
  obtain ⟨-, -, rp8, -⟩ := rp_facts hO hr
  have hd : RHead st Rp (L.wr s (rPrevA r) w) := hX.2.1.head.keep
    (fun r' hr' => o1 _ (hSg.sub _ (hO.nextW hr')) (by
      rw [rp8, rNextA_val (hO.rp r' hr')]; have := (hO.rp r' hr').1; have := (hO.rp r hr).1; omega))
    (fun c hc => o1 _ (hSg.sub _ (hO.repW c hc)) (rword_ne_screp hO hr (by omega) c hc))
    (fun r' hr' h0 hb => (hX.2.1.next r' hr' h0).1 hb)
  exact ⟨⟨⟨Q, R, h1⟩, hB1, hX1.x hd, hS1, hSg1⟩, a1, i1, f1, o1⟩


/-! ## The idle word across `donate` -/

/-- `reschedule_required` keeps the idle word (and the queue invariant). -/
theorem sched.reschedule_required.idle {X : Set U64} (s : S) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hS : SgOK st Ω Sg s) :
    sched.reschedule_required st s ⦃ s' => L.idleW s' = L.idleW s ⦄ := by
  unfold sched.reschedule_required
  step with sched.action.spec as ⟨act, act_post⟩
  refine WP.spec_bind (Pₘ := fun s1 => (∃ Q1 R1, SchedQueuesInvX st T Cs Ω H X s1 Q1 R1) ∧ L.idleW s1 = L.idleW s)
    ?_ ?_
  · split
    · split
      · rename_i h1 h2
        have hT : act ∈ T := by
          rcases h.action with e | e | e
          · rw [← act_post] at e; exfalso; rw [e, resume_val] at h1; simp at h1
          · rw [← act_post] at e; exfalso; rw [e, choose_val] at h2; simp at h2
          · rw [← act_post] at e; exact e
        have hrun : Runnable (L.mem s (stA act)) := by
          have := (h.actOK (act_post ▸ hT)).1; rw [← act_post] at this; exact this
        step with sched.is_schedulable.spec as ⟨b, hb⟩
        split
        · have hc := h.aff act hT
          have hp := h.prio act hT
          refine WP.spec_mono (WP.spec_and (sched.enqueue.inv s act Q R h hT (fun _ => hb ‹_›) (fun _ => hrun))
            (sched.enqueue.foot s act _ h.tcbs hT hp (h.nodes _ hc) (h.nodes _ h.cur) ((h.ready _ hc).1.rel _ hp)
              (fun h0 => h.notQ hT h0 hc hp))) fun s1 hh => ?_
          obtain ⟨h1', hw, -⟩ := hh
          have hW : ∀ w ∈ act :: Q (L.mem s (affA act)) (L.mem s (prioA act)), w ∈ T := by
            intro w hw; rcases List.mem_cons.1 hw with rfl | hw
            · exact hT
            · exact h.memT hc hp hw
          obtain ⟨-, -, -, -, ei⟩ := qfoot_keep h hS hW hc hT p128 hw
          exact ⟨⟨_, _, h1'⟩, ei⟩
        · exact (WP.spec_ok _).2 ⟨⟨Q, R, h⟩, rfl⟩
      · exact (WP.spec_ok _).2 ⟨⟨Q, R, h⟩, rfl⟩
    · exact (WP.spec_ok _).2 ⟨⟨Q, R, h⟩, rfl⟩
  · rintro s1 ⟨⟨Q1, R1, h1⟩, i1⟩
    refine WP.spec_mono (sched.set_action.spec s1 _) fun s2 e => ?_
    subst e
    rw [← i1]
    exact rd_cur_node h1 (by rw [act_val]; omega) (by rw [act_val]) (by rw [idle8]; omega) (by rw [idle8])
      (by rw [act_val, idle8]; omega)

/-- **`donate` keeps the idle word.** -/
theorem schedcontext.donate.idle {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (sc dst : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hsc : sc ∈ Scs) (hdst : dst ∈ T) :
    schedcontext.donate st ar s a sc dst ⦃ s' _ => L.idleW s' = L.idleW s ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hT := h0.tcbs
  have hO := hX.1
  have hsub := hSg.sub
  have hm : scTcbA sc ∈ Ω := hSg.sub _ (hO.fixW sc hsc).1
  have hcO : scCoreA sc ∈ Ω := ((objs_omega hO hsub).2 sc hsc).2.1
  have hcSg : scCoreA sc ∈ Sg := (hO.fixW sc hsc).2
  unfold schedcontext.donate
  step with obj.Sc.tcb.spec as ⟨i, ei⟩
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => (∃ Q1 R1, SchedQueuesInv st T Cs Ω H r.1 Q1 R1) ∧
      SgOK st Ω Sg r.1 ∧ L.idleW r.1 = L.idleW s ∧ DbgTz st T Cs r.1 ∧
      L.mem r.1 (scCoreA sc) = L.mem s (scCoreA sc)) ?_ ?_
  · split
    · exact (WP.spec_ok _).2 ⟨⟨Q, R, h0⟩, hSg, rfl, hX.dbg, rfl⟩
    rename_i hb
    have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    have hiT : i ∈ T := by rw [ei]; exact hX.2.2.yt.1 sc hsc (by rw [← ei]; exact hi0)
    refine WP.spec_bind (smp.remote_tcb_stall.all hA s a i h0 hB hX hS hSg) ?_
    rintro ⟨s2, a2⟩ ⟨h2, -, hX2, -, hSg2, -, -, ei2, -, -, o2⟩
    try simp only [WP.uncurry'_pair]
    have D2 := hX2.dbg
    have c2 : L.mem s2 (scCoreA sc) = L.mem s (scCoreA sc) := o2 _ hcO
    have hc2 := h2.aff i hiT
    have hp2 := h2.prio i hiT
    refine WP.spec_bind (WP.spec_and (sched.dequeue.inv s2 i Q R h2 hiT)
      (sched.dequeue.foot s2 i _ hT hiT hp2 (h2.nodes _ hc2) (h2.nodes _ h2.cur) ((h2.ready _ hc2).1.rel _ hp2)
        (h2.queued i hiT).1)) fun s3 hh3 => ?_
    obtain ⟨h3, hw3, -⟩ := hh3
    have hW2 : ∀ w ∈ Q (L.mem s2 (affA i)) (L.mem s2 (prioA i)), w ∈ T := fun w hw => h2.memT hc2 hp2 hw
    obtain ⟨fr3, -, -, -, ei3⟩ := qfoot_keep (Sg := Sg) h2 hSg2 hW2 hc2 hiT p128 hw3
    have D3 := DbgTz.of_fr fr3 h2.nodes D2
    have c3 : L.mem s3 (scCoreA sc) = L.mem s (scCoreA sc) := (fr3.sig _ hcSg).trans c2
    have hSg3 : SgOK st Ω Sg s3 := hSg2.ksb' hw3.1
    have hc3 := h3.aff i hiT
    refine WP.spec_bind (WP.spec_and (sched.release_remove.inv s3 i _ R h3 hiT)
      (sched.release_remove.foot s3 i _ hT hiT (h3.nodes _ hc3) (h3.nodes _ h3.cur) (h3.release _ hc3)
        (h3.released i hiT).1)) fun s4 hh4 => ?_
    obtain ⟨h4, hw4, -⟩ := hh4
    have hW3 : ∀ w ∈ R (L.mem s3 (affA i)), w ∈ T := fun w hw => h3.memTR hc3 hw
    obtain ⟨fr4, -, -, -, ei4⟩ := qfoot_keep (Sg := Sg) h3 hSg3 hW3 hc3 hiT prel hw4
    have D4 := DbgTz.of_fr fr4 h3.nodes D3
    have c4 : L.mem s4 (scCoreA sc) = L.mem s (scCoreA sc) := (fr4.sig _ hcSg).trans c3
    have hSg4 : SgOK st Ω Sg s4 := hSg3.ksb' hw4.1
    step with obj.Tcb.set_sc.wr as ⟨s5, e5⟩
    subst e5
    obtain ⟨h5, -, -⟩ := field_wr_keep (K := 3464#u64) (v := 0#u64) h4 hiT (by simp) (by simp) (by simp)
    have ei5 : L.idleW (L.wr s4 (core.num.U64.wrapping_add i 3464#u64) 0#u64) = L.idleW s4 :=
      (ani_field hT (h4.nodes _ h4.cur) hiT (K := 3464#u64) (v := 0#u64) (by simp) (by simp)).2.1
    have hSg5 : SgOK st Ω Sg (L.wr s4 (core.num.U64.wrapping_add i 3464#u64) 0#u64) := hSg4.ksb' (L.ksb_wr _ _ _)
    have hfa : Aligned (core.num.U64.wrapping_add i 3464#u64) := field_aligned (hT i hiT) (by simp) (by simp)
    have D5 : DbgTz st T Cs (L.wr s4 (core.num.U64.wrapping_add i 3464#u64) 0#u64) :=
      DbgTz.wr_out hT h4.nodes hfa (notDbgW_field hT h4.nodes hiT (by simp) (by simp)) D4
    have hco4 := h4.omega _ hcO
    have c5 : L.mem (L.wr s4 (core.num.U64.wrapping_add i 3464#u64) 0#u64) (scCoreA sc) = L.mem s (scCoreA sc) :=
      (L.mem_wr_ne hfa hco4.1 (out_ne_field hco4 hiT (hT i hiT) (by simp))).trans c4
    have E := ei5.trans (ei4.trans (ei3.trans ei2))
    step with sched.cur_thread.spec as ⟨t1, _⟩
    step with tcb_eq.blk as ⟨b1, _⟩
    refine WP.spec_bind (Pₘ := fun s6 => (∃ Q1 R1, SchedQueuesInv st T Cs Ω H s6 Q1 R1) ∧ SgOK st Ω Sg s6 ∧
        L.idleW s6 = L.idleW s ∧ DbgTz st T Cs s6 ∧ L.mem s6 (scCoreA sc) = L.mem s (scCoreA sc)) ?_
      fun s6 h6 => (WP.spec_ok _).2 h6
    have RR' : sched.reschedule_required st (L.wr s4 (core.num.U64.wrapping_add i 3464#u64) 0#u64) ⦃ s6 =>
        (∃ Q1 R1, SchedQueuesInv st T Cs Ω H s6 Q1 R1) ∧ SgOK st Ω Sg s6 ∧ L.idleW s6 = L.idleW s ∧
        DbgTz st T Cs s6 ∧ L.mem s6 (scCoreA sc) = L.mem s (scCoreA sc) ⦄ :=
      WP.spec_mono (WP.spec_and (WP.spec_and (sched.reschedule_required.kw (Sg := ∅) (Scs := ∅) (Z := Z)
        (Es := ∅) _ h5) (sched.reschedule_required.inv _ _ _ h5)) (sched.reschedule_required.idle _ _ _ h5 hSg5))
        fun s6 ⟨⟨f6, ⟨Q6, h6⟩, _, _⟩, i6⟩ => ⟨⟨_, _, h6⟩, hSg5.ksb' f6.1, i6.trans E, Foot0.dbg hT h5.nodes f6 D5,
          (Foot0.out hT h5.nodes f6 (h5.omega _ hcO)).trans c5⟩
    split
    · exact RR'
    · step with sched.action.spec as ⟨ac, _⟩
      split
      · exact RR'
      · exact (WP.spec_ok _).2 ⟨⟨_, _, h5⟩, hSg5, E, D5, c5⟩
  rintro ⟨s1, a1⟩ ⟨⟨Q1, R1, h1⟩, hSg1, i1, D1, c1⟩
  try simp only [WP.uncurry'_pair]
  refine WP.spec_mono (donate_tail.frame hA s1 a1 sc dst h1 D1 hO.ksb hsub hsc hdst
    (by rw [c1]; exact hX.2.2.core sc hsc)) ?_
  rintro ⟨s', a'⟩ w
  try simp only [WP.uncurry'_pair] at w ⊢
  exact (donW_keeps hT h1.nodes h1.cur (h1.omega _ hm) hdst w).2.1.trans i1

/-- seL4 `reply_remove` of a stack head (`reply_pop`): the SC `c` that the
head `r` names gets `r`'s `prev` as its new head, which takes over `r`'s
`NEXT` word; `r`'s links are cleared; `c` goes back to `t` if `t` has no
SC; `t` becomes inactive. -/
theorem ipc.reply_pop.blk {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (r t : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hr : r ∈ Rp) (ht : t ∈ T) (hrt : L.mem s (rTcbA r) = t)
    (hst : L.mem s (stA t) = sched.TS_BLOCKED_ON_REPLY)
    (hb : headBit (L.mem s (rNextA r)) = true) (hn0 : L.mem s (rNextA r) &&& ~~~1#u64 ≠ 0#u64) :
    ipc.reply_pop st ar s a r t ⦃ res => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac res.1 ∧
      L.mem res.1 (stA t) = sched.TS_INACTIVE ∧ FootD st T Cs Sg Scs Z Es s res.1 ∧
      (L.mem res.1 (scA t) ≠ 0#u64 → L.mem res.1 (scA t) ∈ Ac) ∧ L.idleW res.1 = L.idleW s ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hO := hX.1
  have hsub := hSg.sub
  obtain ⟨hrΩ, hcΩ⟩ := objs_omega hO hsub
  have rr : ∀ r' ∈ Rp, r'.val % 32 = 0 := fun r' hr' => (hO.rp r' hr').1
  obtain ⟨-, -, rp8, rn16⟩ := rp_facts hO hr
  obtain ⟨c, hc⟩ : ∃ c, L.mem s (rNextA r) &&& ~~~1#u64 = c := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p, L.mem s (rPrevA r) &&& ~~~1#u64 = p := ⟨_, rfl⟩
  rw [hc] at hn0
  have hcS : c ∈ Scs := by rw [← hc]; exact (hX.2.1.next r hr (by rw [hc]; exact hn0)).1 hb
  have hcr : L.mem s (scReplyA c) = r := by rw [← hc]; exact hX.2.1.head r hr hb (by rw [hc]; exact hn0)
  have hcA : c ∈ Ac := hS.rep c hcS (by rw [hcr]; exact hO.rp0 r hr)
  have hci : L.mem s (scTcbA c) ≠ L.idleW s := fun e => hO.rp0 r hr (hcr.symm.trans (hX.2.1.idle c hcS e))
  have hpR : p ≠ 0#u64 → p ∈ Rp := fun h0' => by rw [← hp]; exact hX.2.1.prev r hr (by rw [hp]; exact h0')
  have ht0 : t ≠ 0#u64 := fun e0 => (h0.tcbs t ht).ne0 (by rw [e0]; rfl)
  have hrp : L.mem s (replyA t) = r := by
    obtain ⟨-, -, b2, -⟩ := hX.2.1.back r hr (by rw [hrt]; exact ht0)
    rw [hrt] at b2; exact b2
  have hscR : (scReplyA c).val = c.val + 32 := (sc_facts hO hcS).2.2.2.2.2.2.1
  have hscT : (scTcbA c).val = c.val + 24 := (sc_facts hO hcS).2.1
  have hcm : scReplyA c ∈ Ω := hsub _ (hO.repW c hcS)
  have hal : ∀ b ∈ Ω, Aligned b := fun b hb => (h0.omega b hb).1
  unfold ipc.reply_pop
  step with obj.Reply.next.spec as ⟨nx, enx⟩
  step with obj.Reply.prev.spec as ⟨pv, epv⟩
  refine WP.spec_bind (obj.Reply.next_raw.val s r) fun raw eraw => ?_
  rw [hc] at enx; rw [hp] at epv
  subst nx pv raw
  step with obj.Sc.set_reply.spec as ⟨s1, e1⟩
  subst e1
  obtain ⟨h1, hB1, hX1, hS1, hSg1, a1, i1, f1, o1⟩ :=
    screp_wrR (w := p) h0 hB hX.xr hS hSg hcS (fun hp0 => ⟨hpR hp0, hcA, hci⟩)
  have G1 : Foot st T Cs Sg Scs Z Es s (L.wr s (scReplyA c) p) := foot_sgw (hal _ hcm) (hO.repW c hcS)
  -- the new head takes `r`'s `NEXT` word
  refine WP.spec_bind (Pₘ := fun s2 => SchedQueuesInv st T Cs Ω H s2 Q R ∧ BoundInv st T Ac s2 ∧
      XInvR st T Cs Ω Sg Rp Scs Nt Z s2 ∧ SCsOK st T Ω Sg Scs Z Ac s2 ∧ SgOK st Ω Sg s2 ∧
      L.actionW s2 = L.actionW s ∧ L.idleW s2 = L.idleW s ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        L.mem s2 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ b ∈ Ω, (scReplyA c).val ≠ b.val → (p ≠ 0#u64 → (rNextA p).val ≠ b.val) → L.mem s2 b = L.mem s b) ∧
      L.mem s2 (scReplyA c) = p ∧ (p ≠ 0#u64 → L.mem s2 (rNextA p) = L.mem s (rNextA r)) ∧
      Foot st T Cs Sg Scs Z Es s s2) ?_ ?_
  · split
    · rename_i hp0
      have hp0' : p ≠ 0#u64 := by simpa using hp0
      have hpR' := hpR hp0'
      refine WP.spec_mono (obj.Reply.set_next_raw.val _ p _) fun s2 e2 => ?_
      subst e2
      obtain ⟨-, -, pp8, pn16⟩ := rp_facts hO hpR'
      obtain ⟨h2, hB2, hX2, hS2, hSg2, a2, i2, f2, o2⟩ := rword_wrR (w := L.mem s (rNextA r)) h1 hB1 hX1 hS1 hSg1
        hpR' (Or.inr rfl) (fun _ h0' => hX.2.1.next r hr h0')
        (fun e => absurd (congrArg UScalar.val e) (by rw [pp8, pn16]; omega))
      have hpn : (rNextA p).val ≠ (scReplyA c).val := rword_ne_screp hO hpR' (by omega) c hcS
      refine ⟨h2, hB2, hX2, hS2, hSg2, a2.trans a1, i2.trans i1, fun y hy K h1' h2' => (f2 y hy K h1' h2').trans
        (f1 y hy K h1' h2'), fun b hb n1 n2 => (o2 b hb (n2 hp0')).trans (o1 b hb n1), ?_,
        fun _ => L.mem_wr_same (hal _ (hrΩ p hpR').2.2), G1.trans (foot_sgw (hal _ (hrΩ p hpR').2.2) (hO.nextW hpR'))⟩
      rw [o2 _ hcm hpn]; exact L.mem_wr_same (hal _ hcm)
    · rename_i hp0
      have hp0' : p = 0#u64 := UScalar.eq_of_val_eq (by simpa using hp0)
      exact (WP.spec_ok _).2 ⟨h1, hB1, hX1, hS1, hSg1, a1, i1, f1, fun b hb n1 _ => o1 b hb n1,
        L.mem_wr_same (hal _ hcm), fun h' => absurd hp0' h', G1⟩
  intro s2 ⟨h2, hB2, hX2, hS2, hSg2, a2, i2, f2, o2, r2, n2, G2⟩
  -- `r`'s `NEXT` word is cleared: `RHead` again
  refine WP.spec_bind (obj.Reply.set_next.val0 s2 r 0#u64) fun s3 e3 => ?_
  rw [zero_link] at e3
  subst e3
  obtain ⟨h3, hB3, hX3, hS3, hSg3, a3, i3, f3, o3⟩ := rword_wrR (w := 0#u64) h2 hB2 hX2 hS2 hSg2 hr (Or.inr rfl)
    (fun _ h0' => absurd zero_or_masked h0') (fun e => by
      exfalso; have h' := congrArg (fun x : U64 => x.val) e; rw [rp8, rn16] at h'; omega)
  have hd : RHead st Rp (L.wr s2 (rNextA r) 0#u64) := by
    intro r' hr' hb' h0'
    by_cases e : r' = r
    · subst e; rw [L.mem_wr_same (hal _ (hrΩ r' hr').2.2)] at h0'; exact absurd zero_or_masked h0'
    have nrr : (rNextA r).val ≠ (rNextA r').val := by
      rw [rn16, rNextA_val (hO.rp r' hr')]; have := rr r' hr'; have := rr r hr
      have : r.val ≠ r'.val := fun e' => e (UScalar.eq_of_val_eq e').symm
      omega
    rw [o3 _ (hrΩ r' hr').2.2 nrr] at hb' h0' ⊢
    by_cases ep : p ≠ 0#u64 ∧ r' = p
    · obtain ⟨hp0, rfl⟩ := ep
      rw [n2 hp0] at hb' h0' ⊢
      rw [hc, o3 _ hcm (rword_ne_screp hO hr (by omega) c hcS), r2]
    · have e2 : L.mem s2 (rNextA r') = L.mem s (rNextA r') := o2 _ (hrΩ r' hr').2.2
        (fun e' => rword_ne_screp hO hr' (by rw [rNextA_val (hO.rp r' hr')]; omega) c hcS e'.symm)
        (fun hp0 e' => ep ⟨hp0, by
          apply UScalar.eq_of_val_eq
          rw [rNextA_val (hO.rp p (hpR hp0)), rNextA_val (hO.rp r' hr')] at e'
          have := rr r' hr'; have := rr p (hpR hp0); omega⟩)
      rw [e2] at hb' h0' ⊢
      have hc'S := (hX.2.1.next r' hr' h0').1 hb'
      have hhd := hX.2.1.head r' hr' hb' h0'
      have hne : L.mem s (rNextA r') &&& ~~~1#u64 ≠ c := fun e' => by rw [e', hcr] at hhd; exact e hhd.symm
      have hsc' := (sc_facts hO hc'S).2.2.2.2.2.2.1
      have nsc : (scReplyA c).val ≠ (scReplyA (L.mem s (rNextA r') &&& ~~~1#u64)).val := by
        rw [hscR, hsc']
        have := hO.scDisj c hcS _ hc'S (Ne.symm hne); have := (sc_facts hO hc'S).1; have := (sc_facts hO hcS).1
        omega
      have hm' := hsub _ (hO.repW _ hc'S)
      rw [o3 _ hm' (rword_ne_screp hO hr (by omega) _ hc'S), o2 _ hm' nsc
        (fun hp0 => rword_ne_screp hO (hpR hp0) (by rw [rNextA_val (hO.rp p (hpR hp0))]; omega) _ hc'S)]
      exact hhd
  have hX3' := hX3.x hd
  have G3 : Foot st T Cs Sg Scs Z Es s (L.wr s2 (rNextA r) 0#u64) :=
    G2.trans (foot_sgw (hal _ (hrΩ r hr).2.2) (hO.nextW hr))
  -- facts at `s3`
  have F3 : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem (L.wr s2 (rNextA r) 0#u64) (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K h1' h2' => (f3 y hy K h1' h2').trans (f2 y hy K h1' h2')
  have hst3 : L.mem (L.wr s2 (rNextA r) 0#u64) (stA t) = sched.TS_BLOCKED_ON_REPLY := by
    rw [stA_eq, F3 t ht _ (by simp) (by simp), ← stA_eq]; exact hst
  have hrp3 : L.mem (L.wr s2 (rNextA r) 0#u64) (replyA t) = r := by
    exact (F3 t ht 3360#u64 (by simp) (by simp)).trans hrp
  have tc3 : L.mem (L.wr s2 (rNextA r) 0#u64) (scTcbA c) = L.mem s (scTcbA c) := by
    have hm := (hcΩ c hcS).1
    rw [o3 _ hm (rword_ne_sc hO hr (by omega) c hcS).1, o2 _ hm (by rw [hscR, hscT]; omega)
      (fun hp0 => (rword_ne_sc hO (hpR hp0) (by rw [rNextA_val (hO.rp p (hpR hp0))]; omega) c hcS).1)]
  -- the donation back to `t`
  step with obj.Tcb.sc.spec as ⟨i, ei⟩
  have hk3 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s2 (rNextA r) 0#u64) := ⟨⟨Q, R, h3⟩, hB3, hX3', hS3, hSg3⟩
  have scs : L.mem s (scA t) ≠ 0#u64 → L.mem s (scA t) ∈ Ac := fun h0' =>
    hB.sact t ht (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hst)))))) h0'
  refine WP.spec_bind (Pₘ := fun res : S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac res.1 ∧
      L.mem res.1 (stA t) = sched.TS_BLOCKED_ON_REPLY ∧ L.mem res.1 (replyA t) = r ∧
      FootD st T Cs Sg Scs Z Es (L.wr s2 (rNextA r) 0#u64) res.1 ∧
      (L.mem res.1 (scA t) ≠ 0#u64 → L.mem res.1 (scA t) ∈ Ac) ∧
      L.idleW res.1 = L.idleW (L.wr s2 (rNextA r) 0#u64)) ?_ ?_
  · split
    · rename_i hi0
      have hsc0 : L.mem (L.wr s2 (rNextA r) 0#u64) (scA t) = 0#u64 := by rw [← ei]; exact hi0
      obtain ⟨dq, dr, da⟩ := blocked_out h3 ht (by rw [hst3]; exact not_runnable_reply)
      by_cases hf0 : L.mem (L.wr s2 (rNextA r) 0#u64) (scTcbA c) = 0#u64
      · refine WP.spec_mono (WP.spec_and (WP.spec_and (schedcontext.donate.unbound hA (X := ∅) _ a c t Q R h3 hB3 hX3' hS3 hSg3 ht dq dr
          hcS hn0 hf0 (hX3'.2.2.core c hcS) (fun _ => hcA) hsc0
          (fun e => hB3.idleNB (by rw [e, hst3]; exact Or.inr rfl)))
          (schedcontext.donate.kw (Es := Es) hA _ a c t hk3 hcS ht)) (schedcontext.donate.idle hA _ a c t hk3 hcS ht)) ?_
        rintro ⟨s4, a4⟩ ⟨⟨⟨hk, st4, rp4, -, sc4, -, -⟩, fk⟩, id4⟩
        exact ⟨hk, by rw [st4 t ht]; exact hst3, by rw [rp4 t ht]; exact hrp3, fk, fun _ => by rw [sc4]; exact hcA, id4⟩
      · have hfT := hX3'.2.2.yt.1 c hcS hf0
        have hscf := hX3'.2.2.tsc c hcS hn0 hf0
        refine WP.spec_mono (WP.spec_and (WP.spec_and (schedcontext.donate.gen hA _ a c t _ Q R h3 hB3 hX3' hS3 hSg3 hfT hscf hn0
          ?_ ht hsc0 dq dr da ?_ hcA (fun e => hB3.idleNB (by rw [e, hst3]; exact Or.inr rfl)))
          (schedcontext.donate.kw (Es := Es) hA _ a c t hk3 hcS ht)) (schedcontext.donate.idle hA _ a c t hk3 hcS ht)) ?_
        · rw [i3, i2, tc3]; exact fun e => hci e.symm
        · intro e; rw [← e, hsc0] at hscf; exact hn0 hscf.symm
        · rintro ⟨s4, a4⟩ ⟨⟨⟨hk, st4, rp4, sc4⟩, fk⟩, id4⟩
          exact ⟨hk, by rw [st4 t ht]; exact hst3, by rw [rp4 t ht]; exact hrp3, fk, fun _ => by rw [sc4]; exact hcA, id4⟩
    · exact (WP.spec_ok _).2 ⟨hk3, hst3, hrp3, WritesIn.refl _ _, by
        have e3 : L.mem (L.wr s2 (rNextA r) 0#u64) (scA t) = L.mem s (scA t) := by
          rw [scA_eq]; exact F3 t ht _ (by simp) (by simp)
        rw [e3]; exact scs, rfl⟩
  rintro ⟨s4, a4⟩ ⟨hk4, st4, rp4, G4, sc4, id4⟩
  try simp only [WP.uncurry'_pair]
  dsimp only at hk4 st4 rp4 G4 ⊢
  refine WP.spec_bind (obj.Reply.set_prev.val s4 r 0#u64) fun s5 e5 => ?_
  rw [zero_or_masked] at e5
  subst e5
  obtain ⟨hk5, -, id5, f5, -⟩ := rprev_wr_all hk4 hr (fun h0' => absurd zero_or_masked h0')
  have hst5 : L.mem (L.wr s4 (rPrevA r) 0#u64) (stA t) = sched.TS_BLOCKED_ON_REPLY := by
    rw [stA_eq, f5 t ht _ (by simp) (by simp), ← stA_eq]; exact st4
  have hrp5 : L.mem (L.wr s4 (rPrevA r) 0#u64) (replyA t) = r := by
    exact (f5 t ht 3360#u64 (by simp) (by simp)).trans rp4
  have hrt5 := (hk5.2.2.1.2.1.reply t ht hst5).2
  rw [hrp5] at hrt5
  have G5 : Foot st T Cs Sg Scs Z Es s4 (L.wr s4 (rPrevA r) 0#u64) :=
    foot_sgw (hal _ (hrΩ r hr).2.1) (hO.prevW hr)
  have sc5 : L.mem (L.wr s4 (rPrevA r) 0#u64) (scA t) = L.mem s4 (scA t) := by
    rw [scA_eq]; exact f5 t ht _ (by simp) (by simp)
  refine WP.spec_bind (ipc.reply_unlink.blk (Es := Es) _ r t hk5 hr ht hrt5 hst5) ?_
  rintro s6 ⟨h6, e6, k6, -, G6⟩
  exact (WP.spec_ok _).2 ⟨h6, e6, G3.d.trans (G4.trans (G5.trans G6).d), by
    rw [k6.scf ht, sc5]; exact sc4, by rw [k6.idleW, id5, id4, i3, i2]⟩

/-- Clearing a reply's `PREV` or `NEXT` word keeps `BlkOK`. -/
theorem rword_wr0_all {s : S} {r a : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hr : r ∈ Rp)
    (ha : a = rPrevA r ∨ a = rNextA r) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s a 0#u64) ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        L.mem (L.wr s a 0#u64) (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hO := hX.1
  obtain ⟨-, -, rp8, rn16⟩ := rp_facts hO hr
  obtain ⟨h1, hB1, hX1, hS1, hSg1, -, -, f1, o1⟩ := rword_wrR (w := 0#u64) h0 hB hX.xr hS hSg hr ha
    (fun _ h0' => absurd zero_or_masked h0') (fun _ h0' => absurd zero_or_masked h0')
  have hav : a.val = r.val + 8 ∨ a.val = r.val + 16 := by
    rcases ha with rfl | rfl
    · exact Or.inl rp8
    · exact Or.inr rn16
  have ho := h0.omega a (by rcases ha with rfl | rfl; exacts [hSg.sub _ (hO.prevW hr), hSg.sub _ (hO.nextW hr)])
  have hd : RHead st Rp (L.wr s a 0#u64) := hX.2.1.head.keep0 (Scs := Scs)
    (fun r' hr' => by
      rw [L.mem_wr_val ho.1 (h0.omega _ (hSg.sub _ (hO.nextW hr'))).1]
      split
      · exact Or.inr zero_or_masked
      · exact Or.inl rfl)
    (fun c hc => o1 _ (hSg.sub _ (hO.repW c hc)) (rword_ne_screp hO hr (by omega) c hc))
    (fun r' hr' h0 hb => (hX.2.1.next r' hr' h0).1 hb)
  exact ⟨⟨⟨Q, R, h1⟩, hB1, hX1.x hd, hS1, hSg1⟩, f1⟩

/-- seL4 `reply_remove`: a stack head is popped (`reply_pop`); otherwise the
reply leaves the middle of its stack (its neighbours' links to it are
cleared) or is on no stack.  Then `t` (blocked on the reply) becomes
inactive. -/
theorem ipc.reply_remove.blk {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (r t : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hr : r ∈ Rp) (ht : t ∈ T) (hrt : L.mem s (rTcbA r) = t)
    (hst : L.mem s (stA t) = sched.TS_BLOCKED_ON_REPLY) :
    ipc.reply_remove st ar s a r t ⦃ res => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac res.1 ∧
      L.mem res.1 (stA t) = sched.TS_INACTIVE ∧ FootD st T Cs Sg Scs Z Es s res.1 ∧
      (L.mem res.1 (scA t) ≠ 0#u64 → L.mem res.1 (scA t) ∈ Ac) ∧ L.idleW res.1 = L.idleW s ⦄ := by
  have scs : L.mem s (scA t) ≠ 0#u64 → L.mem s (scA t) ∈ Ac := fun h0' =>
    h.2.1.sact t ht (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hst)))))) h0'
  have hX := h.2.2.1
  have hO := hX.1
  have ht0 : t ≠ 0#u64 := fun e0 => (h.1.choose_spec.choose_spec.tcbs t ht).ne0 (by rw [e0]; rfl)
  have hrp : L.mem s (replyA t) = r := by
    obtain ⟨-, -, b2, -⟩ := hX.2.1.back r hr (by rw [hrt]; exact ht0)
    rw [hrt] at b2; exact b2
  -- the unlinking writes keep `BlkOK` and `t`'s fields
  have W : ∀ {s₁ : S} {r' a' : U64}, BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s₁ →
      L.mem s₁ (stA t) = sched.TS_BLOCKED_ON_REPLY → L.mem s₁ (replyA t) = r → r' ∈ Rp →
      (a' = rPrevA r' ∨ a' = rNextA r') →
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s₁ a' 0#u64) ∧
        L.mem (L.wr s₁ a' 0#u64) (stA t) = sched.TS_BLOCKED_ON_REPLY ∧ L.mem (L.wr s₁ a' 0#u64) (replyA t) = r ∧
        Foot st T Cs Sg Scs Z Es s₁ (L.wr s₁ a' 0#u64) ∧ L.mem (L.wr s₁ a' 0#u64) (scA t) = L.mem s₁ (scA t) ∧
        L.idleW (L.wr s₁ a' 0#u64) = L.idleW s₁ :=
    fun h₁ e₁ e₂ hr' ha' => by
      obtain ⟨k, f⟩ := rword_wr0_all h₁ hr' ha'
      have hO₁ := h₁.2.2.1.1
      refine ⟨k, by rw [stA_eq, f t ht _ (by simp) (by simp), ← stA_eq]; exact e₁,
        (f t ht 3360#u64 (by simp) (by simp)).trans e₂, ?_, by rw [scA_eq]; exact f t ht _ (by simp) (by simp),
        idleW_wr_out h₁.1.choose_spec.choose_spec (by
          rcases ha' with rfl | rfl
          · exact h₁.2.2.2.2.sub _ (hO₁.prevW hr')
          · exact h₁.2.2.2.2.sub _ (hO₁.nextW hr'))⟩
      rcases ha' with rfl | rfl
      · exact foot_sgw (rp_aligned hO hr').2.1 (hO.prevW hr')
      · exact foot_sgw (rp_aligned hO hr').2.2 (hO.nextW hr')
  have tail : ∀ s₂ : S, BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s₂ →
      L.mem s₂ (stA t) = sched.TS_BLOCKED_ON_REPLY → L.mem s₂ (replyA t) = r →
      L.mem s₂ (scA t) = L.mem s (scA t) →
      (do
        let s3 ← obj.Reply.set_prev st r s₂ 0#u64
        let s4 ← obj.Reply.set_next st r s3 0#u64 false
        let s5 ← ipc.reply_unlink st s4 r t
        ok (s5, a)) ⦃ res => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac res.1 ∧
          L.mem res.1 (stA t) = sched.TS_INACTIVE ∧ Foot st T Cs Sg Scs Z Es s₂ res.1 ∧
          (L.mem res.1 (scA t) ≠ 0#u64 → L.mem res.1 (scA t) ∈ Ac) ∧ L.idleW res.1 = L.idleW s₂ ⦄ := by
    intro s₂ h₂ e₂ r₂ c₂
    refine WP.spec_bind (obj.Reply.set_prev.val s₂ r 0#u64) fun s3 e3 => ?_
    rw [zero_or_masked] at e3; subst e3
    obtain ⟨h3, e3, r3, g3, c3, i3⟩ := W h₂ e₂ r₂ hr (Or.inl rfl)
    refine WP.spec_bind (obj.Reply.set_next.val0 _ r 0#u64) fun s4 e4 => ?_
    rw [zero_link] at e4; subst e4
    obtain ⟨h4, e4, r4, g4, c4, i4⟩ := W h3 e3 r3 hr (Or.inr rfl)
    have hrt4 := (h4.2.2.1.2.1.reply t ht e4).2
    rw [r4] at hrt4
    refine WP.spec_bind (ipc.reply_unlink.blk (Es := Es) _ r t h4 hr ht hrt4 e4) ?_
    rintro s5 ⟨h5, e5, k5, -, g5⟩
    exact (WP.spec_ok _).2 ⟨h5, e5, g3.trans (g4.trans g5), by rw [k5.scf ht, c4, c3, c₂]; exact scs,
      by rw [k5.idleW, i4, i3]⟩
  unfold ipc.reply_remove
  step with obj.Reply.next.spec as ⟨nx, enx⟩
  step with obj.Reply.prev.spec as ⟨pv, epv⟩
  subst nx pv
  have hpR : L.mem s (rPrevA r) &&& ~~~1#u64 ≠ 0#u64 → L.mem s (rPrevA r) &&& ~~~1#u64 ∈ Rp := hX.2.1.prev r hr
  -- the prev neighbour's `NEXT` word, then the tail
  have P : ∀ s₁ : S, BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s₁ →
      L.mem s₁ (stA t) = sched.TS_BLOCKED_ON_REPLY → L.mem s₁ (replyA t) = r →
      L.mem s₁ (scA t) = L.mem s (scA t) →
      (do
        let s2 ← if (L.mem s (rPrevA r) &&& ~~~1#u64) != 0#u64
          then obj.Reply.set_next st (L.mem s (rPrevA r) &&& ~~~1#u64) s₁ 0#u64 false else ok s₁
        let s3 ← obj.Reply.set_prev st r s2 0#u64
        let s4 ← obj.Reply.set_next st r s3 0#u64 false
        let s5 ← ipc.reply_unlink st s4 r t
        ok (s5, a)) ⦃ res => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac res.1 ∧
          L.mem res.1 (stA t) = sched.TS_INACTIVE ∧ Foot st T Cs Sg Scs Z Es s₁ res.1 ∧
          (L.mem res.1 (scA t) ≠ 0#u64 → L.mem res.1 (scA t) ∈ Ac) ∧ L.idleW res.1 = L.idleW s₁ ⦄ := by
    intro s₁ h₁ e₁ r₁ c₁
    split
    · rename_i hp0
      refine WP.spec_bind (obj.Reply.set_next.val0 s₁ _ 0#u64) fun s2 e2 => ?_
      rw [zero_link] at e2; subst e2
      obtain ⟨h2, e2, r2, g2, c2, i2⟩ := W h₁ e₁ r₁ (hpR (by simpa using hp0)) (Or.inr rfl)
      exact WP.spec_mono (tail _ h2 e2 r2 (c2.trans c₁)) fun r hr =>
        ⟨hr.1, hr.2.1, g2.trans hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.trans i2⟩
    · simp only [Aeneas.Std.bind_ok]; exact tail s₁ h₁ e₁ r₁ c₁
  split
  · rename_i hn0
    have hn0' : L.mem s (rNextA r) &&& ~~~1#u64 ≠ 0#u64 := by simpa using hn0
    step with obj.Reply.next_is_head.spec as ⟨b, eb⟩
    split
    · rename_i hb
      have hb' : headBit (L.mem s (rNextA r)) = true := by rw [← eb]; exact hb
      exact ipc.reply_pop.blk hA s a r t h hr ht hrt hst hb' hn0'
    · rename_i hb
      have hb' : headBit (L.mem s (rNextA r)) = false := by rw [← eb]; simpa using hb
      have hnR := (hX.2.1.next r hr hn0').2 hb'
      refine WP.spec_bind (obj.Reply.set_prev.val s _ 0#u64) fun s1 e1 => ?_
      rw [zero_or_masked] at e1; subst e1
      obtain ⟨h1, e1, r1, g1, c1, i1⟩ := W h hst hrp hnR (Or.inl rfl)
      exact WP.spec_mono (P _ h1 e1 r1 c1) fun r hr =>
        ⟨hr.1, hr.2.1, (g1.trans hr.2.2.1).d, hr.2.2.2.1, hr.2.2.2.2.trans i1⟩
  · rename_i hn0
    simp only [Aeneas.Std.bind_ok]
    exact WP.spec_mono (P s h hst hrp rfl) fun r hr => ⟨hr.1, hr.2.1, hr.2.2.1.d, hr.2.2.2.1, hr.2.2.2.2⟩

/-! ## The Reply branch of `finalise_cap` -/

/-- `finalise_cap` of a final reply cap: a thread blocked on the reply is
removed from it (`reply_remove`), one blocked on receive with it has its
receive cancelled. -/
theorem fin_reply.blk {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (p : U64) (x : Bool)
    (fin : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hp : p ∈ Rp) :
    objects.finalise_cap_object st ar s a (.Reply p x) fin ⦃ r =>
      r.1 = (.Null, .Null) ∧ BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ∧ FootD st T Cs Sg Scs Z (EH H) s r.2.1 ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  split
  swap
  · exact (WP.spec_ok _).2 ⟨rfl, h, WritesIn.refl _ _⟩
  refine WP.spec_bind (obj.Reply.tcb.blk s p) fun i ei => ?_
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 ⟨rfl, h, WritesIn.refl _ _⟩
  rename_i hb
  have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
  have hX := h.2.2.1
  obtain ⟨-, hiT, -, -⟩ := hX.2.1.back p hp (by rw [← ei]; exact hi0)
  rw [← ei] at hiT
  step with obj.Tcb.state.spec as ⟨v, ev⟩
  split
  · rename_i hv
    refine WP.spec_bind (ipc.reply_remove.blk (Es := EH H) hA s a p i h hp hiT ei.symm (by rw [← ev, hv])) ?_
    rintro ⟨s1, a1⟩ ⟨h1, -, f1, -, -⟩
    exact (WP.spec_ok _).2 ⟨rfl, h1, f1⟩
  split
  · obtain ⟨⟨Q, R, h0⟩, hB, -, hS, hSg⟩ := h
    refine WP.spec_bind (WP.spec_and (ipc.cancel_ipc.all s a i Q R h0 hiT hB hX hSg.sub)
      (ipc.cancel_ipc.kw s a i h0 hiT hX.1 hSg.sub (fun hs => by
        obtain ⟨h1, h2⟩ := hX.2.1.reply i hiT hs
        exact ⟨h1, h2, hX.2.1.next _ h1, hX.2.1.prev _ h1⟩) (fun hs h0' => (hX.2.1.recv i hiT hs h0').1))) ?_
    rintro ⟨s1, a1⟩ ⟨⟨h1, hB1, hX1, -, -, -, k1, -⟩, f1⟩
    exact (WP.spec_ok _).2 ⟨rfl, ⟨⟨Q, R, h1⟩, hB1, hX1, hS.keepT hX k1,
      ⟨hSg.sub, fun b hb => by rw [k1.ksb]; exact hSg.ks b hb, fun o h1' h2' => by rw [k1.ksb]; exact hSg.ksΩ o h1' h2'⟩⟩, f1.d⟩
  · exact (WP.spec_ok _).2 ⟨rfl, h, WritesIn.refl _ _⟩

end

end Fl4Proofs.P1
