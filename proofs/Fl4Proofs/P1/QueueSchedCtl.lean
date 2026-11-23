/-
P1: InvGaps4's `schedControl` family (`SchedControl_ConfigureFlags`,
`decode_sched_control` and `configure_flags`).  This file: the writes to an
SC's own words other than the ones `XInv` reads (`scw_bx`).
-/
import Fl4Proofs.P1.QueueDecTcb2
import Fl4Proofs.P1.QueueFinThr
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {s : S}

theorem not_prot_scw {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) {c b : U64} (hc : c ∈ Scs)
    (hb : Aligned b) (hin : InSC c (Z c) b)
    (hno : b.val ≠ c.val + 16 ∧ b.val ≠ c.val + 24 ∧ b.val ≠ c.val + 32 ∧ b.val ≠ c.val + 40 ∧
      b.val ≠ c.val + 56 ∧ b.val ≠ c.val + 72) :
    ¬ Prot T Rp Scs Nt b := by
  obtain ⟨hP, hz⟩ := hO.sc c hc
  obtain ⟨-, h128, -⟩ := sc_lo hP hz
  have := hin.1; have := hin.2
  rintro (⟨r, hr', e⟩ | ⟨c', hc', e⟩ | ⟨t, ht, e⟩ | ⟨n, hn, rfl⟩)
  rotate_right
  · have := hO.ntSc n hn c hc; have := hin.1; have := hin.2; omega
  · have hp := hO.rp r hr'
    have hrv : b.val = r.val ∨ b.val = r.val + 8 ∨ b.val = r.val + 16 := by
      rcases e with rfl | rfl | rfl
      · exact Or.inl (rTcbA_val hp)
      · exact Or.inr (Or.inl (rPrevA_val hp))
      · exact Or.inr (Or.inr (rNextA_val hp))
    have := hO.rpSc r hr' c hc
    omega
  · obtain ⟨hP', hz'⟩ := hO.sc c' hc'
    obtain ⟨-, h128', -⟩ := sc_lo hP' hz'
    have hcv : b.val = c'.val + 24 ∨ b.val = c'.val + 16 ∨ b.val = c'.val + 32 ∨ b.val = c'.val + 40 ∨
        b.val = c'.val + 56 ∨ b.val = c'.val + 72 := by
      rcases e with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl (scTcbA_val hP' hz')
      · exact Or.inr (Or.inl (scCoreA_val hP' hz'))
      · exact Or.inr (Or.inr (Or.inl (scReplyA_val hP' hz')))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (scNtfnA_val hP' hz'))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (scYieldA_val hP' hz')))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (maxA_val hP' hz')))))
    by_cases e' : c = c'
    · subst e'; omega
    · have := hO.scDisj c hc c' hc' e'; omega
  · have hm := hO.scW c hc b hb hin
    have hout := (h.omega _ hm).2.1 t ht
    have hv : b.val = t.val + 3464 ∨ b.val = t.val + 3360 ∨ b.val = t.val + 3328 ∨ b.val = t.val + 3368 ∨
        b.val = t.val + 3472 := by
      rcases e with rfl | rfl | rfl | rfl | rfl
      · left; rw [scA_eq, field_val (h.tcbs t ht) (by simp)]; simp
      · right; left; unfold replyA; rw [field_val (h.tcbs t ht) (by simp)]; simp
      · right; right; left; rw [stA_eq, field_val (h.tcbs t ht) (by simp)]; simp
      · right; right; right; left; unfold boundA; rw [field_val (h.tcbs t ht) (by simp)]; simp
      · right; right; right; right; unfold yieldA; rw [field_val (h.tcbs t ht) (by simp)]; simp
    omega

theorem scw_bx {X : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {c : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hSg : SgOK st Ω Sg s) (hc : c ∈ Scs)
    {B : U64 → Prop} (w : WritesIn st s s' B) (hBi : ∀ b, B b → InSC c (Z c) b)
    (hBo : ∀ b, B b → b.val ≠ c.val + 16 ∧ b.val ≠ c.val + 24 ∧ b.val ≠ c.val + 32 ∧ b.val ≠ c.val + 40 ∧
      b.val ≠ c.val + 56 ∧ b.val ≠ c.val + 72) :
    SchedQueuesInvX st T Cs Ω H X s' Q R ∧ BoundInv st T Ac s' ∧ XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧ SgOK st Ω Sg s' ∧
      L.actionW s' = L.actionW s ∧ L.curW s' = L.curW s ∧ L.cscW s' = L.cscW s ∧
      (∀ y ∈ T, L.mem s' (scA y) = L.mem s (scA y) ∧ L.mem s' (stA y) = L.mem s (stA y) ∧
        L.mem s' (inqA y) = L.mem s (inqA y)) := by
  obtain ⟨hP, hz⟩ := hX.1.sc c hc
  obtain ⟨h8, h128, -⟩ := sc_lo hP hz
  have hN' := h.nodes _ h.cur
  have inΩ : ∀ b, Aligned b → B b → b ∈ Ω := fun b hb hh => hX.1.scW c hc b hb (hBi b hh)
  have wF : WritesIn st s s' (L.Free s Ω Cs) := w.mono' fun b hb hh => Or.inl (inΩ b hb hh)
  have nodeK : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem s' (L.nodeAt s' (L.cpu s') o) = L.mem s (L.nodeAt s (L.cpu s) o) := fun o ho h8' => by
    rw [w.2.1, nodeAt_of_ksb w.1]
    exact w.mem_eq (nodeAt_aligned hN' ho h8') fun hh =>
      out_ne_node (h.omega _ (inΩ _ (nodeAt_aligned hN' ho h8') hh)) h.cur hN' ho rfl
  have fldK : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := fun y hy K hK hK8 =>
    w.mem_eq (field_aligned (h.tcbs y hy) hK hK8) fun hh =>
      out_ne_field (h.omega _ (inΩ _ (field_aligned (h.tcbs y hy) hK hK8) hh)) hy (h.tcbs y hy) hK rfl
  have ecs : L.cscW s' = L.cscW s := by
    unfold LawfulStore.cscW LawfulStore.nodeA; exact nodeK _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  refine ⟨inv_of_free h wF, hB.free h wF, hX.writes h.tcbs
    (w.mono' (B := fun b => ¬ Prot T Rp Scs Nt b) fun b hb hh => not_prot_scw h hX.1 hc hb (hBi b hh) (hBo b hh)) (fun b hb => hb)
    (by rw [ecs]; exact hX.2.2.cur) (hX.tn_writes h w fun b hb hh => notTmW_insc h hX.1 hSg.sub hc hb (hBi b hh))
    (by unfold LawfulStore.idleW; exact nodeK _ (by rw [idle8]; omega) (by rw [idle8])),
    ⟨hSg.sub, fun b hb => by rw [w.1]; exact hSg.ks b hb, fun o h1 h2 => by rw [w.1]; exact hSg.ksΩ o h1 h2⟩,
    by unfold LawfulStore.actionW; exact nodeK _ (by rw [act_val]; omega) (by rw [act_val]),
    by unfold LawfulStore.curW; exact nodeK _ (by rw [curth0]; omega) (by rw [curth0]), ecs,
    fun y hy => ⟨by rw [scA_eq]; exact fldK y hy _ (by simp) (by simp),
      by rw [stA_eq]; exact fldK y hy _ (by simp) (by simp), by rw [inqA_eq]; exact fldK y hy _ (by simp) (by simp)⟩⟩

theorem XInv0.keepM {s s' : S} (hX : XInv0 st T Cs Ω Sg Rp Scs Nt Z s)
    (hrw : ∀ r ∈ Rp, L.mem s' (rTcbA r) = L.mem s (rTcbA r) ∧ L.mem s' (rPrevA r) = L.mem s (rPrevA r) ∧
      L.mem s' (rNextA r) = L.mem s (rNextA r))
    (hft : ∀ c ∈ Scs, L.mem s' (scTcbA c) = L.mem s (scTcbA c)) (hcore : ∀ c ∈ Scs, L.mem s' (scCoreA c) ∈ Cs)
    (hsc : ∀ t ∈ T, L.mem s' (scA t) = L.mem s (scA t))
    (hrep : ∀ t ∈ T, L.mem s' (replyA t) = L.mem s (replyA t))
    (hst : ∀ t ∈ T, L.mem s' (stA t) = L.mem s (stA t))
    (hcs : L.cscW s' ∈ Scs)
    (hsr : ∀ c ∈ Scs, L.mem s' (scReplyA c) = L.mem s (scReplyA c))
    (hbd : ∀ t ∈ T, L.mem s' (boundA t) = L.mem s (boundA t))
    (hns : ∀ n ∈ Nt, L.mem s' (ntfnScA n) = L.mem s (ntfnScA n))
    (htn : TimerOK st T Cs s' ∧ NtbOK st T Nt s' ∧ TimerRB st T Cs s' ∧ (∀ n ∈ Nt, L.mem s' (ntfnBtA n) = L.mem s (ntfnBtA n)))
    (hsn : ∀ c ∈ Scs, L.mem s' (scNtfnA c) = L.mem s (scNtfnA c))
    (hyt : YT st T Scs s')
    (hiw : L.idleW s' = L.idleW s) :
    XInv0 st T Cs Ω Sg Rp Scs Nt Z s' := by
  obtain ⟨hO, hR, hE⟩ := hX
  refine ⟨hO.ksb, ⟨⟨fun t ht hs => ?_, fun t ht hs hn => ?_, fun r hr => ?_, fun r hr => ?_, fun r hr hn => ?_,
      fun c hc => by rw [hsr c hc]; exact hR.screp c hc,
      idleRep_keep hR.idle hiw (fun c hc => hft c hc) (fun c hc => Or.inl (hsr c hc))⟩,
      hR.head.keep (fun r hr => (hrw r hr).2.2) hsr (fun r hr h0 hb => (hR.next r hr h0).1 hb)⟩,
    ⟨fun t ht hb => ?_, hcs, hcore,
      fun t ht => by rw [hbd t ht]; exact hE.bnd t ht, fun n hn h0 => by
        rw [hns n hn] at h0 ⊢
        obtain ⟨h1, h2⟩ := hE.nsc n hn h0
        exact ⟨h1, by rw [hsn _ h1]; exact h2⟩,
      htn.1, htn.2.1, htn.2.2.1, fun c hc => by rw [hsn c hc]; exact hE.scn c hc, hyt,
      hE.bs.keep hE.bnd hE.ntb hE.scn hbd htn.2.2.2 hns hsn⟩⟩
  rotate_left 4
  · rw [(hrw r hr).1] at hn ⊢
    obtain ⟨b0, b1, b2, b3⟩ := hR.back r hr hn
    rw [hrep _ b1, hst _ b1]; exact ⟨b0, b1, b2, b3⟩
  rotate_right 4
  · rw [hst t ht] at hs
    obtain ⟨h1, h2⟩ := hR.reply t ht hs
    rw [hrep t ht, (hrw _ h1).1]; exact ⟨h1, h2⟩
  · rw [hst t ht] at hs; rw [hrep t ht] at hn ⊢
    obtain ⟨h1, h2⟩ := hR.recv t ht hs hn
    rw [(hrw _ h1).1]; exact ⟨h1, h2⟩
  · rw [(hrw r hr).2.2]; exact hR.next r hr
  · rw [(hrw r hr).2.1]; exact hR.prev r hr
  · rw [hsc t ht] at hb ⊢
    obtain ⟨h1, h2, h3⟩ := hE.bound t ht hb
    rw [hft _ h1]; exact ⟨h1, h2, hcore _ h1⟩


theorem XInv.keepM {s s' : S} (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hrw : ∀ r ∈ Rp, L.mem s' (rTcbA r) = L.mem s (rTcbA r) ∧ L.mem s' (rPrevA r) = L.mem s (rPrevA r) ∧
      L.mem s' (rNextA r) = L.mem s (rNextA r))
    (hft : ∀ c ∈ Scs, L.mem s' (scTcbA c) = L.mem s (scTcbA c)) (hcore : ∀ c ∈ Scs, L.mem s' (scCoreA c) ∈ Cs)
    (hsc : ∀ t ∈ T, L.mem s' (scA t) = L.mem s (scA t))
    (hrep : ∀ t ∈ T, L.mem s' (replyA t) = L.mem s (replyA t))
    (hst : ∀ t ∈ T, L.mem s' (stA t) = L.mem s (stA t))
    (hcs : L.cscW s' ∈ Scs)
    (hsr : ∀ c ∈ Scs, L.mem s' (scReplyA c) = L.mem s (scReplyA c))
    (hbd : ∀ t ∈ T, L.mem s' (boundA t) = L.mem s (boundA t))
    (hns : ∀ n ∈ Nt, L.mem s' (ntfnScA n) = L.mem s (ntfnScA n))
    (htn : TimerOK st T Cs s' ∧ NtbOK st T Nt s' ∧ TimerRB st T Cs s' ∧ (∀ n ∈ Nt, L.mem s' (ntfnBtA n) = L.mem s (ntfnBtA n)))
    (hsn : ∀ c ∈ Scs, L.mem s' (scNtfnA c) = L.mem s (scNtfnA c))
    (hyl : ∀ t ∈ T, L.mem s' (yieldA t) = L.mem s (yieldA t))
    (hyf : ∀ c ∈ Scs, L.mem s' (scYieldFromA c) = L.mem s (scYieldFromA c))
    (hiw : L.idleW s' = L.idleW s) :
    XInv st T Cs Ω Sg Rp Scs Nt Z s' :=
  (hX.x0.keepM hrw hft hcore hsc hrep hst hcs hsr hbd hns htn
    hsn (hX.2.2.yt.keep (fun c hc => hft c hc) hyl hyf) hiw).x
    (hX.2.2.tsc.keep hX.2.2.yt.1 (fun c hc => hft c hc) hsc)

/-- The words `XInv` reads other than the SCs' `CORE` and `REFILL_MAX` words. -/
def ProtM (T Rp Scs Nt : Set U64) (b : U64) : Prop :=
  (∃ r ∈ Rp, b = rTcbA r ∨ b = rPrevA r ∨ b = rNextA r) ∨
  (∃ c ∈ Scs, b = scTcbA c ∨ b = scReplyA c ∨ b = scNtfnA c ∨ b = scYieldFromA c) ∨
  (∃ t ∈ T, b = scA t ∨ b = replyA t ∨ b = stA t ∨ b = boundA t ∨ b = yieldA t) ∨
  (∃ n ∈ Nt, b = ntfnScA n)

theorem ProtM.prot {T Rp Scs Nt : Set U64} {b : U64} (h : ProtM T Rp Scs Nt b) : Prot T Rp Scs Nt b := by
  rcases h with h | ⟨c, hc, e | e | e | e⟩ | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨c, hc, Or.inl e⟩)
  · exact Or.inr (Or.inl ⟨c, hc, Or.inr (Or.inr (Or.inl e))⟩)
  · exact Or.inr (Or.inl ⟨c, hc, Or.inr (Or.inr (Or.inr (Or.inl e)))⟩)
  · exact Or.inr (Or.inl ⟨c, hc, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e))))⟩)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

/-- **`XInv` across writes that may change SCs' `CORE` (to cores) and
`REFILL_MAX` words**, avoiding the other words it reads. -/
theorem XInv.writesM {s s' : S} {B : U64 → Prop} (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hT : TcbPlaced T)
    (hw : WritesIn st s s' B) (hB : ∀ b, B b → ¬ ProtM T Rp Scs Nt b) (hcore : ∀ c ∈ Scs, L.mem s' (scCoreA c) ∈ Cs)
    (hcs : L.cscW s' ∈ Scs) (htn : TimerOK st T Cs s' ∧ NtbOK st T Nt s' ∧ TimerRB st T Cs s' ∧ (∀ n ∈ Nt, L.mem s' (ntfnBtA n) = L.mem s (ntfnBtA n))) (hiw : L.idleW s' = L.idleW s) :
    XInv st T Cs Ω Sg Rp Scs Nt Z s' := by
  have k : ∀ b, ProtM T Rp Scs Nt b → L.mem s' b = L.mem s b := fun b hb =>
    hw.mem_eq (hX.1.aligned hT hb.prot) (fun h => hB b h hb)
  exact hX.keepM (fun r hr => ⟨k _ (Or.inl ⟨r, hr, Or.inl rfl⟩), k _ (Or.inl ⟨r, hr, Or.inr (Or.inl rfl)⟩),
      k _ (Or.inl ⟨r, hr, Or.inr (Or.inr rfl)⟩)⟩)
    (fun c hc => k _ (Or.inr (Or.inl ⟨c, hc, Or.inl rfl⟩))) hcore
    (fun t ht => k _ (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inl rfl⟩))))
    (fun t ht => k _ (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inr (Or.inl rfl)⟩))))
    (fun t ht => k _ (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inr (Or.inr (Or.inl rfl))⟩)))) hcs
    (fun c hc => k _ (Or.inr (Or.inl ⟨c, hc, Or.inr (Or.inl rfl)⟩)))
    (fun t ht => k _ (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩))))
    (fun n hn => k _ (Or.inr (Or.inr (Or.inr ⟨n, hn, rfl⟩)))) htn
    (fun c hc => k _ (Or.inr (Or.inl ⟨c, hc, Or.inr (Or.inr (Or.inl rfl))⟩)))
    (fun t ht => k _ (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩))))
    (fun c hc => k _ (Or.inr (Or.inl ⟨c, hc, Or.inr (Or.inr (Or.inr rfl))⟩))) hiw

theorem not_protM_scw {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) {c b : U64} (hc : c ∈ Scs)
    (hb : Aligned b) (hin : InSC c (Z c) b)
    (hno : b.val ≠ c.val + 24 ∧ b.val ≠ c.val + 32 ∧ b.val ≠ c.val + 40 ∧ b.val ≠ c.val + 56) :
    ¬ ProtM T Rp Scs Nt b := by
  obtain ⟨hP, hz⟩ := hO.sc c hc
  obtain ⟨-, h128, -⟩ := sc_lo hP hz
  have := hin.1; have := hin.2
  rintro (⟨r, hr', e⟩ | ⟨c', hc', e⟩ | ⟨t, ht, e⟩ | ⟨n, hn, rfl⟩)
  rotate_right
  · have := hO.ntSc n hn c hc; have := hin.1; have := hin.2; omega
  · have hp := hO.rp r hr'
    have hrv : b.val = r.val ∨ b.val = r.val + 8 ∨ b.val = r.val + 16 := by
      rcases e with rfl | rfl | rfl
      · exact Or.inl (rTcbA_val hp)
      · exact Or.inr (Or.inl (rPrevA_val hp))
      · exact Or.inr (Or.inr (rNextA_val hp))
    have := hO.rpSc r hr' c hc
    omega
  · obtain ⟨hP', hz'⟩ := hO.sc c' hc'
    obtain ⟨-, h128', -⟩ := sc_lo hP' hz'
    have hcv : b.val = c'.val + 24 ∨ b.val = c'.val + 32 ∨ b.val = c'.val + 40 ∨ b.val = c'.val + 56 := by
      rcases e with rfl | rfl | rfl | rfl
      · exact Or.inl (scTcbA_val hP' hz')
      · exact Or.inr (Or.inl (scReplyA_val hP' hz'))
      · exact Or.inr (Or.inr (Or.inl (scNtfnA_val hP' hz')))
      · exact Or.inr (Or.inr (Or.inr (scYieldA_val hP' hz')))
    by_cases e' : c = c'
    · subst e'; omega
    · have := hO.scDisj c hc c' hc' e'; omega
  · have hm := hO.scW c hc b hb hin
    have hout := (h.omega _ hm).2.1 t ht
    have hv : b.val = t.val + 3464 ∨ b.val = t.val + 3360 ∨ b.val = t.val + 3328 ∨ b.val = t.val + 3368 ∨
        b.val = t.val + 3472 := by
      rcases e with rfl | rfl | rfl | rfl | rfl
      · left; rw [scA_eq, field_val (h.tcbs t ht) (by simp)]; simp
      · right; left; unfold replyA; rw [field_val (h.tcbs t ht) (by simp)]; simp
      · right; right; left; rw [stA_eq, field_val (h.tcbs t ht) (by simp)]; simp
      · right; right; right; left; unfold boundA; rw [field_val (h.tcbs t ht) (by simp)]; simp
      · right; right; right; right; unfold yieldA; rw [field_val (h.tcbs t ht) (by simp)]; simp
    omega

theorem scw_bxM {X : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {c : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hSg : SgOK st Ω Sg s) (hc : c ∈ Scs)
    {B : U64 → Prop} (w : WritesIn st s s' B) (hBi : ∀ b, B b → InSC c (Z c) b)
    (hBo : ∀ b, B b → b.val ≠ c.val + 24 ∧ b.val ≠ c.val + 32 ∧ b.val ≠ c.val + 40 ∧ b.val ≠ c.val + 56)
    (hcore : ∀ c' ∈ Scs, L.mem s' (scCoreA c') ∈ Cs) :
    SchedQueuesInvX st T Cs Ω H X s' Q R ∧ BoundInv st T Ac s' ∧ XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧ SgOK st Ω Sg s' ∧
      L.actionW s' = L.actionW s ∧ L.curW s' = L.curW s ∧ L.cscW s' = L.cscW s ∧
      (∀ y ∈ T, L.mem s' (scA y) = L.mem s (scA y) ∧ L.mem s' (stA y) = L.mem s (stA y) ∧
        L.mem s' (inqA y) = L.mem s (inqA y)) := by
  obtain ⟨hP, hz⟩ := hX.1.sc c hc
  obtain ⟨h8, h128, -⟩ := sc_lo hP hz
  have hN' := h.nodes _ h.cur
  have inΩ : ∀ b, Aligned b → B b → b ∈ Ω := fun b hb hh => hX.1.scW c hc b hb (hBi b hh)
  have wF : WritesIn st s s' (L.Free s Ω Cs) := w.mono' fun b hb hh => Or.inl (inΩ b hb hh)
  have nodeK : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem s' (L.nodeAt s' (L.cpu s') o) = L.mem s (L.nodeAt s (L.cpu s) o) := fun o ho h8' => by
    rw [w.2.1, nodeAt_of_ksb w.1]
    exact w.mem_eq (nodeAt_aligned hN' ho h8') fun hh =>
      out_ne_node (h.omega _ (inΩ _ (nodeAt_aligned hN' ho h8') hh)) h.cur hN' ho rfl
  have fldK : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := fun y hy K hK hK8 =>
    w.mem_eq (field_aligned (h.tcbs y hy) hK hK8) fun hh =>
      out_ne_field (h.omega _ (inΩ _ (field_aligned (h.tcbs y hy) hK hK8) hh)) hy (h.tcbs y hy) hK rfl
  have ecs : L.cscW s' = L.cscW s := by
    unfold LawfulStore.cscW LawfulStore.nodeA; exact nodeK _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  refine ⟨inv_of_free h wF, hB.free h wF, hX.writesM h.tcbs
    (w.mono' (B := fun b => ¬ ProtM T Rp Scs Nt b) fun b hb hh => not_protM_scw h hX.1 hc hb (hBi b hh) (hBo b hh))
    (fun b hb => hb) hcore
    (by rw [ecs]; exact hX.2.2.cur) (hX.tn_writes h w fun b hb hh => notTmW_insc h hX.1 hSg.sub hc hb (hBi b hh))
    (by unfold LawfulStore.idleW; exact nodeK _ (by rw [idle8]; omega) (by rw [idle8])),
    ⟨hSg.sub, fun b hb => by rw [w.1]; exact hSg.ks b hb, fun o h1 h2 => by rw [w.1]; exact hSg.ksΩ o h1 h2⟩,
    by unfold LawfulStore.actionW; exact nodeK _ (by rw [act_val]; omega) (by rw [act_val]),
    by unfold LawfulStore.curW; exact nodeK _ (by rw [curth0]; omega) (by rw [curth0]), ecs,
    fun y hy => ⟨by rw [scA_eq]; exact fldK y hy _ (by simp) (by simp),
      by rw [stA_eq]; exact fldK y hy _ (by simp) (by simp), by rw [inqA_eq]; exact fldK y hy _ (by simp) (by simp)⟩⟩

/-- **`SCsOK` after rewriting an SC's refills**: writes inside the SC `c`
that leave it well formed make it active (`insert c Ac`). -/
theorem SCsOK.reset {s' : S} {c : U64}
    {B : U64 → Prop} (hS : SCsOK st T Ω Sg Scs Z Ac s) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hc : c ∈ Scs)
    (w : WritesIn st s s' B) (hBi : ∀ b, B b → InSC c (Z c) b)
    (hsc : ∀ y ∈ T, L.mem s' (scA y) = L.mem s (scA y)) (hcs : L.cscW s' = L.cscW s)
    (hwf : RefillsWF st s' c (Z c)) : SCsOK st T Ω Sg Scs Z (insert c Ac) s' := by
  have out : ∀ c' ∈ Scs, c' ≠ c → ∀ b, Aligned b → B b → Outside b c' (Z c') := fun c' hc' hne b _ hb => by
    have := hO.scDisj c' hc' c hc hne; have := (hBi b hb).1; have := (hBi b hb).2
    unfold Outside; omega
  have kw : ∀ c' ∈ Scs, c' ≠ c → ∀ b, Aligned b → c'.val ≤ b.val → b.val < c'.val + 2 ^ Z c' →
      L.mem s' b = L.mem s b := fun c' hc' hne b hb h1 h2 =>
    w.mem_eq hb fun hh => by have := out c' hc' hne b hb hh; unfold Outside at this; omega
  have mx0 : L.rmax s' c ≠ 0#u64 := fun e => by
    have := hwf.min_le; rw [e] at this; simp [sporadic.MIN_REFILLS] at this
  refine ⟨hS.sub, fun b hb => by rw [w.1]; exact hS.ks b hb, fun o h1 h2 => by rw [w.1]; exact hS.ksΩ o h1 h2,
    fun y hy hb hne => ?_, fun c' hc' => ?_, fun c' hc' => ?_, fun c' hc' h0' => ?_, hS.spSg,
    fun c' hc' h0' => ?_, hS.repSg⟩
  · rw [hsc y hy] at hb hne ⊢; rw [hcs] at hne ⊢; exact hS.disj y hy hb hne
  · by_cases e : c' = c
    · subst e; exact (hS.all c' hc').mk' fun _ => hwf
    obtain ⟨a1, a2, a3⟩ := maxA_facts hO hc'
    exact (hS.all c' hc').writesIn a1 ⟨a2, a3⟩ w (out c' hc' e)
  · by_cases e : c' = c
    · subst e; exact ⟨fun _ => mx0, fun _ => Set.mem_insert _ _⟩
    · obtain ⟨a1, a2, a3⟩ := maxA_facts hO hc'
      have : L.rmax s' c' = L.rmax s c' := kw c' hc' e _ a1 a2 a3
      rw [this]
      exact ⟨fun hh => (hS.act c' hc').1 (hh.resolve_left e), fun hh => Or.inr ((hS.act c' hc').2 hh)⟩
  · by_cases e : c' = c
    · subst e; exact Set.mem_insert _ _
    · obtain ⟨hPc, hzc⟩ := hO.sc c' hc'
      obtain ⟨h8c, h128c, -⟩ := sc_lo hPc hzc
      have spv := sporA_val hPc hzc
      have al : Aligned (sporA c') := by unfold Aligned; omega
      rw [kw c' hc' e _ al (by omega) (by omega)] at h0'
      exact Or.inr (hS.spor c' hc' h0')
  · by_cases e : c' = c
    · subst e; exact Set.mem_insert _ _
    · obtain ⟨hPc, hzc⟩ := hO.sc c' hc'
      obtain ⟨h8c, h128c, -⟩ := sc_lo hPc hzc
      have rpv := scReplyA_val hPc hzc
      have al : Aligned (scReplyA c') := by unfold Aligned; omega
      rw [kw c' hc' e _ al (by omega) (by omega)] at h0'
      exact Or.inr (hS.rep c' hc' h0')

/-- `BoundInv` for a larger active set. -/
theorem BoundInv.mono {Ac' : Set U64} (hB : BoundInv st T Ac s) (h : Ac ⊆ Ac') : BoundInv st T Ac' s :=
  { hB with sact := fun y hy hS h0 => h (hB.sact y hy hS h0) }

/-! ## The refill rewrites -/

/-- The words of an SC the refill rewrites write: `PERIOD`, `REFILL_MAX` and
the ring (from `REFILL_HEAD` on). -/
def RFW (c : U64) (sb : Nat) (b : U64) : Prop := b = periodA c ∨ b = maxA c ∨ InRing c sb b

theorem RFW.insc {c b : U64} {sb : Nat} (hP : Placed c sb) (hz : 7 ≤ sb) (h : RFW c sb b) : InSC c sb b := by
  obtain ⟨h8, h128, hfit⟩ := sc_lo hP hz
  rcases h with rfl | rfl | h
  · unfold periodA; rw [InSC, sc_word_val hP hz (by simp [layout.sc.PERIOD])]; simp [layout.sc.PERIOD] <;> omega
  · rw [InSC, maxA_val hP hz]; omega
  · exact h.inSC

theorem RFW.offs {c b : U64} {sb : Nat} (hP : Placed c sb) (hz : 7 ≤ sb) (h : RFW c sb b) :
    b.val ≠ c.val + 24 ∧ b.val ≠ c.val + 32 ∧ b.val ≠ c.val + 40 ∧ b.val ≠ c.val + 56 := by
  rcases h with rfl | rfl | h
  · unfold periodA; rw [sc_word_val hP hz (by simp [layout.sc.PERIOD])]; simp [layout.sc.PERIOD]
  · rw [maxA_val hP hz]; omega
  · have := h.1; omega

theorem rfw_facts {c : U64} {sb : Nat} (hP : Placed c sb) (hz : 7 ≤ sb) :
    (Aligned (periodA c) ∧ RFW c sb (periodA c)) ∧ (Aligned (maxA c) ∧ RFW c sb (maxA c)) ∧
    (Aligned (headA c) ∧ RFW c sb (headA c)) ∧ (Aligned (tailA c) ∧ RFW c sb (tailA c)) ∧
    (Aligned (rtA c 0#u64) ∧ RFW c sb (rtA c 0#u64)) ∧ (Aligned (raA c 0#u64) ∧ RFW c sb (raA c 0#u64)) := by
  obtain ⟨h8, h128, hfit⟩ := sc_lo hP hz
  have pv : (periodA c).val = c.val := by
    unfold periodA; rw [sc_word_val hP hz (by simp [layout.sc.PERIOD])]; simp [layout.sc.PERIOD]
  have mv := maxA_val hP hz
  have hv := headA_val' hP hz
  have tv := tailA_val' hP hz
  have rv : (rtA c 0#u64).val = c.val + 96 := by
    unfold rtA
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits,
      layout.sc.REFILLS, layout.sc.REFILL_SIZE]; omega
  have av : (raA c 0#u64).val = c.val + 104 := by
    unfold raA; rw [core.num.U64.wrapping_add_val_eq, rv]; simp [U64.size_def, U64.numBits]; omega
  refine ⟨⟨by unfold Aligned; omega, Or.inl rfl⟩, ⟨by unfold Aligned; omega, Or.inr (Or.inl rfl)⟩,
    ⟨by unfold Aligned; omega, Or.inr (Or.inr ⟨by omega, by omega⟩)⟩,
    ⟨by unfold Aligned; omega, Or.inr (Or.inr ⟨by omega, by omega⟩)⟩,
    ⟨by unfold Aligned; omega, Or.inr (Or.inr ⟨by omega, by omega⟩)⟩,
    ⟨by unfold Aligned; omega, Or.inr (Or.inr ⟨by omega, by omega⟩)⟩⟩

theorem rfw_wr {s : S} {c a v : U64} {sb : Nat} (ha : Aligned a) (hr : RFW c sb a) :
    WritesIn st s (L.wr s a v) (RFW c sb) := (writesIn_wr ha).mono fun b e => e ▸ hr

theorem rfw_trans {s₁ s₂ s₃ : S} {c : U64} {sb : Nat} (h₁ : WritesIn st s₁ s₂ (RFW c sb))
    (h₂ : WritesIn st s₂ s₃ (RFW c sb)) : WritesIn st s₁ s₃ (RFW c sb) := h₁.trans1 h₂

theorem rfw_ring {s₁ s₂ : S} {c : U64} {sb : Nat} (h : WritesIn st s₁ s₂ (InRing c sb)) :
    WritesIn st s₁ s₂ (RFW c sb) := h.mono fun _ hb => Or.inr (Or.inr hb)

theorem sporadic.refill_new.fr {s : S} {sc : obj.Sc} {sb : Nat} (max_refills budget period : U64)
    (hP : Placed sc sb) (hz : 7 ≤ sb)
    (h2 : sporadic.MIN_REFILLS.val ≤ max_refills.val) (hm : max_refills.val ≤ absMax sb) :
    sporadic.refill_new st s sc max_refills budget period ⦃ s' =>
      RefillsWF st s' sc sb ∧ WritesIn st s s' (RFW sc sb) ⦄ := by
  obtain ⟨⟨aP, rP⟩, ⟨aM, rM⟩, ⟨aH, rH⟩, ⟨aT, rT⟩, -⟩ := rfw_facts hP hz
  unfold sporadic.refill_new
  refine WP.spec_bind (obj.Sc.set_period.spec s sc period) fun s1 e1 => ?_
  subst e1
  refine WP.spec_bind (obj.Sc.set_refill_head.spec _ sc 0#u64) fun s2 e2 => ?_
  subst e2
  refine WP.spec_bind (obj.Sc.set_refill_tail.spec _ sc 0#u64) fun s3 e3 => ?_
  subst e3
  refine WP.spec_bind (obj.Sc.set_refill_max.spec _ sc max_refills) fun s4 e4 => ?_
  subst e4
  have hW : RefillsWF st _ sc sb := RefillsWF.reset (s := L.wr s (periodA sc) period) hP h2 hm
  have w4 : WritesIn st s (L.wr (L.wr (L.wr (L.wr s (periodA sc) period) (headA sc) 0#u64) (tailA sc) 0#u64)
      (maxA sc) max_refills) (RFW sc sb) :=
    rfw_trans (rfw_trans (rfw_trans (rfw_wr aP rP) (rfw_wr aH rH)) (rfw_wr aT rT)) (rfw_wr aM rM)
  refine WP.spec_bind (sporadic.cur_time.spec _) fun now _ => ?_
  refine WP.spec_bind (sporadic.put.spec _ sc 0#u64 _) fun s5 e5 => ?_
  subst e5
  have hi : (0#u64).val < (L.rmax (L.wr (L.wr (L.wr (L.wr s (periodA sc) period) (headA sc) 0#u64) (tailA sc) 0#u64)
      (maxA sc) max_refills) sc).val := by have := hW.min_le; simp [sporadic.MIN_REFILLS] at this ⊢; omega
  exact WP.spec_mono (sporadic.maybe_add_empty_tail.fr (hW.putS hi)) fun s6 ⟨h6, w6⟩ =>
    ⟨h6, rfw_trans w4 (rfw_trans (rfw_ring (hW.frame_putS hi)) (rfw_ring w6))⟩

theorem sporadic.refill_update.fr {s : S} {sc : obj.Sc} {sb : Nat} (new_period new_budget new_max_refills : U64)
    (hP : Placed sc sb) (hz : 7 ≤ sb)
    (h2 : sporadic.MIN_REFILLS.val ≤ new_max_refills.val) (hm : new_max_refills.val ≤ absMax sb) :
    sporadic.refill_update st s sc new_period new_budget new_max_refills ⦃ s' =>
      RefillsWF st s' sc sb ∧ WritesIn st s s' (RFW sc sb) ⦄ := by
  obtain ⟨⟨aP, rP⟩, ⟨aM, rM⟩, ⟨aH, rH⟩, ⟨aT, rT⟩, ⟨a0, r0⟩, ⟨a1, r1⟩⟩ := rfw_facts hP hz
  unfold sporadic.refill_update
  refine WP.spec_bind (sporadic.head.spec s sc) fun h _ => ?_
  refine WP.spec_bind (sporadic.put.spec s sc 0#u64 h) fun s1 e1 => ?_
  subst e1
  have w1 : WritesIn st s (L.putS s sc 0#u64 h) (RFW sc sb) := rfw_trans (rfw_wr a0 r0) (rfw_wr a1 r1)
  refine WP.spec_bind (obj.Sc.set_refill_head.spec _ sc 0#u64) fun s2 e2 => ?_
  subst e2
  refine WP.spec_bind (obj.Sc.set_refill_tail.spec _ sc 0#u64) fun s3 e3 => ?_
  subst e3
  refine WP.spec_bind (obj.Sc.set_refill_max.spec _ sc new_max_refills) fun s4 e4 => ?_
  subst e4
  refine WP.spec_bind (obj.Sc.set_period.spec _ sc new_period) fun s5 e5 => ?_
  subst e5
  have hW5 : RefillsWF st _ sc sb := (RefillsWF.reset (st := st) (s := L.putS s sc 0#u64 h) hP h2 hm).wr_period (v := new_period)
  have w5 : WritesIn st s (L.wr (L.wr (L.wr (L.wr (L.putS s sc 0#u64 h) (headA sc) 0#u64) (tailA sc) 0#u64)
      (maxA sc) new_max_refills) (periodA sc) new_period) (RFW sc sb) :=
    rfw_trans (rfw_trans (rfw_trans (rfw_trans (rfw_trans w1 (rfw_wr aH rH)) (rfw_wr aT rT)) (rfw_wr aM rM))
      (rfw_wr aP rP)) (WritesIn.refl _ _)
  refine WP.spec_bind (sporadic.ready.spec _ sc) fun b _ => ?_
  refine WP.spec_bind (Pₘ := fun s6 => RefillsWF st s6 sc sb ∧ WritesIn st s s6 (RFW sc sb)) ?_ ?_
  · split
    · refine WP.spec_bind (sporadic.cur_time.spec _) fun now _ => ?_
      refine WP.spec_bind (sporadic.head.spec _ sc) fun r _ => ?_
      exact WP.spec_mono (sporadic.set_head.fr _ hW5) fun s6 ⟨h6, w6⟩ => ⟨h6, rfw_trans w5 (rfw_ring w6)⟩
    · exact (WP.spec_ok _).2 ⟨hW5, w5⟩
  rintro s6 ⟨h6, w6⟩
  refine WP.spec_bind (sporadic.head.spec _ sc) fun hd _ => ?_
  split
  · refine WP.spec_bind (sporadic.set_head.fr _ h6) fun s7 ⟨h7, w7⟩ => ?_
    exact WP.spec_mono (sporadic.maybe_add_empty_tail.fr h7) fun s8 ⟨h8, w8⟩ =>
      ⟨h8, rfw_trans w6 (rfw_trans (rfw_ring w7) (rfw_ring w8))⟩
  · simp only [lift, bind_ok]
    refine WP.spec_bind (Pₘ := fun _ => True) ?_ fun i1 _ => ?_
    · exact (by
        rename_i hlt
        have : new_budget.val ≥ hd.amount.val := by
          simp [UScalar.le_equiv] at hlt; omega
        exact WP.spec_mono (UScalar.sub_spec this) fun _ _ => trivial)
    exact WP.spec_mono (sporadic.add_tail.fr _ h6) fun s7 ⟨h7, w7⟩ => ⟨h7, rfw_trans w6 (rfw_ring w7)⟩

/-- **A refill rewrite keeps the invariants** and makes the SC active. -/
theorem refill_blk {s' : S} {c : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hc : c ∈ Scs)
    (w : WritesIn st s s' (RFW c (Z c))) (hwf : RefillsWF st s' c (Z c)) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z (insert c Ac) s' ∧ L.actionW s' = L.actionW s ∧ L.curW s' = L.curW s ∧
      L.cscW s' = L.cscW s ∧ (∀ y ∈ T, L.mem s' (scA y) = L.mem s (scA y) ∧ L.mem s' (stA y) = L.mem s (stA y) ∧
        L.mem s' (inqA y) = L.mem s (inqA y)) := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hO := hX.1
  obtain ⟨hP, hz⟩ := hO.sc c hc
  have hcore : ∀ c' ∈ Scs, L.mem s' (scCoreA c') ∈ Cs := fun c' hc' => by
    obtain ⟨hP', hz'⟩ := hO.sc c' hc'
    obtain ⟨h8', h128', -⟩ := sc_lo hP' hz'
    have cv := scCoreA_val hP' hz'
    have hn : ¬ RFW c (Z c) (scCoreA c') := fun hh => by
      have hin := RFW.insc hP hz hh
      by_cases e : c' = c
      · subst e
        have pv : (periodA c').val = c'.val := by
          unfold periodA; rw [sc_word_val hP hz (by simp [layout.sc.PERIOD])]; simp [layout.sc.PERIOD]
        rcases hh with e | e | e
        · have := congrArg UScalar.val e; rw [cv, pv] at this; omega
        · have := congrArg UScalar.val e; rw [cv, maxA_val hP hz] at this; omega
        · have := e.1; omega
      · have := hO.scDisj c' hc' c hc e; have := hin.1; have := hin.2; omega
    rw [w.mem_eq (by unfold Aligned; omega) hn]
    exact hX.2.2.core c' hc'
  obtain ⟨h1, hB1, hX1, hSg1, ea, ec, ecs, fl⟩ := scw_bxM h0 hB hX hSg hc w (fun b hb => RFW.insc hP hz hb)
    (fun b hb => RFW.offs hP hz hb) hcore
  exact ⟨⟨⟨Q, R, h1⟩, hB1.mono (Set.subset_insert _ _), hX1,
    SCsOK.reset hS hO hc w (fun b hb => RFW.insc hP hz hb) (fun y hy => (fl y hy).1) ecs hwf, hSg1⟩,
    ea, ec, ecs, fl⟩

/-- **A write of an active SC's `CORE`, `BADGE` or `SPORADIC` word** (a core
for `CORE`) keeps the invariants. -/
theorem scword_blk {c a v : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hc : c ∈ Scs) (hcA : c ∈ Ac)
    (ha : a.val = c.val + 16 ∨ a.val = c.val + 48 ∨ a.val = c.val + 64) (hv : a = scCoreA c → v ∈ Cs) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s a v) ∧ L.actionW (L.wr s a v) = L.actionW s ∧
      L.curW (L.wr s a v) = L.curW s ∧ L.cscW (L.wr s a v) = L.cscW s ∧
      (∀ y ∈ T, L.mem (L.wr s a v) (scA y) = L.mem s (scA y) ∧ L.mem (L.wr s a v) (stA y) = L.mem s (stA y) ∧
        L.mem (L.wr s a v) (inqA y) = L.mem s (inqA y)) := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hO := hX.1
  obtain ⟨hP, hz⟩ := hO.sc c hc
  obtain ⟨h8, h128, hfit⟩ := sc_lo hP hz
  have hal : Aligned a := by unfold Aligned; omega
  have hin : InSC c (Z c) a := ⟨by omega, by omega⟩
  have w := writesIn_wr (st := st) (s := s) (v := v) hal
  have hwf0 : RefillsWF st s c (Z c) := (hS.all c hc).1 ((hS.act c hc).1 hcA)
  have mv := maxA_val hP hz
  have hv' := headA_val' hP hz
  have tv := tailA_val' hP hz
  have hwf : RefillsWF st (L.wr s a v) c (Z c) := by
    have k : ∀ b, Aligned b → a.val ≠ b.val → L.mem (L.wr s a v) b = L.mem s b := fun b hb hne =>
      L.mem_wr_ne hal hb hne
    refine hwf0.of_hdr (k _ (maxA_facts hO hc).1 (by rw [mv]; omega)) ?_ ?_
    · show (L.mem (L.wr s a v) (headA c)).val < _
      rw [k _ (by unfold Aligned; omega) (by rw [hv']; omega)]; exact hwf0.head_lt
    · show (L.mem (L.wr s a v) (tailA c)).val < _
      rw [k _ (by unfold Aligned; omega) (by rw [tv]; omega)]; exact hwf0.tail_lt
  have hcore : ∀ c' ∈ Scs, L.mem (L.wr s a v) (scCoreA c') ∈ Cs := fun c' hc' => by
    obtain ⟨hP', hz'⟩ := hO.sc c' hc'
    obtain ⟨h8', h128', -⟩ := sc_lo hP' hz'
    have cv := scCoreA_val hP' hz'
    by_cases e : a = scCoreA c'
    · have hcc : c' = c := by
        by_contra hne
        have := hO.scDisj c' hc' c hc hne
        have := congrArg UScalar.val e; omega
      subst hcc; rw [← e, L.mem_wr_same hal]; exact hv e
    · rw [L.mem_wr_ne hal (by unfold Aligned; omega) (fun e' => e (UScalar.eq_of_val_eq e'))]
      exact hX.2.2.core c' hc'
  obtain ⟨h1, hB1, hX1, hSg1, ea, ec, ecs, fl⟩ := scw_bxM h0 hB hX hSg hc w (fun b hb => hb ▸ hin)
    (fun b hb => by subst hb; omega) hcore
  have hS1 := SCsOK.reset hS hO hc w (fun b hb => hb ▸ hin) (fun y hy => (fl y hy).1) ecs hwf
  rw [Set.insert_eq_of_mem hcA] at hS1
  exact ⟨⟨⟨Q, R, h1⟩, hB1, hX1, hS1, hSg1⟩, ea, ec, ecs, fl⟩

/-! ## `commit_time` -/

/-- The words of an SC's ring or `CONSUMED` word, or of the current node
(below `CUR_SC`'s offset or above it). -/
def RingNode (st : machine.Store S) [L : LawfulStore st] (c : U64) (sb : Nat) (s : S) (b : U64) : Prop :=
  (InRing c sb b ∨ b = core.num.U64.wrapping_add c layout.sc.CONSUMED) ∨
    ∃ o : U64, LowFree o.val ∧ o.val % 8 = 0 ∧ o.val ≠ 24 ∧ b = L.nodeA s o

/-- `SCsOK` across writes to an SC's ring and `CONSUMED` word and to current
node words other than `CUR_SC`, the SC well formed afterwards if active. -/
theorem SCsOK.ringNode {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {s' : S} {c : U64}
    (h0 : SchedQueuesInvX st T Cs Ω H X s Q R) (hS : SCsOK st T Ω Sg Scs Z Ac s) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s)
    (hc : c ∈ Scs) (w : WritesIn st s s' (RingNode st c (Z c) s))
    (hsc : ∀ y ∈ T, L.mem s' (scA y) = L.mem s (scA y)) (hcs : L.cscW s' = L.cscW s)
    (hwf : L.rmax s c ≠ 0#u64 → RefillsWF st s' c (Z c)) : SCsOK st T Ω Sg Scs Z Ac s' := by
  have hN' := h0.nodes _ h0.cur
  obtain ⟨hP, hz⟩ := hO.sc c hc
  obtain ⟨h8, h128, -⟩ := sc_lo hP hz
  have cv : (core.num.U64.wrapping_add c layout.sc.CONSUMED).val = c.val + 8 := by
    rw [sc_word_val hP hz (by simp [layout.sc.CONSUMED])]; simp [layout.sc.CONSUMED]
  -- every written word lies outside the SCs other than `c`, and inside `c` at offset 8 or from 80 on
  have outN : ∀ c' ∈ Scs, ∀ o : U64, LowFree o.val → o.val % 8 = 0 → Outside (L.nodeA s o) c' (Z c') :=
    fun c' hc' o ho h8' => node_out_place (fun b hb hin => hO.scW c' hc' b hb hin) h0.omega h0.cur hN'
      (by unfold LowFree at ho; omega) h8'
  have out : ∀ c' ∈ Scs, c' ≠ c → ∀ b, Aligned b → RingNode st c (Z c) s b → Outside b c' (Z c') := by
    intro c' hc' hne b hb hh
    rcases hh with (hh | rfl) | ⟨o, ho, h8', -, rfl⟩
    · have := hO.scDisj c' hc' c hc hne; unfold Outside; unfold InRing at hh; omega
    · have := hO.scDisj c' hc' c hc hne; unfold Outside; rw [cv]; omega
    · exact outN c' hc' o ho h8'
  have kw : ∀ c' ∈ Scs, ∀ b, Aligned b → c'.val ≤ b.val → b.val < c'.val + 80 → b.val ≠ c'.val + 8 →
      L.mem s' b = L.mem s b := fun c' hc' b hb h1 h2 h3 => w.mem_eq hb fun hh => by
    by_cases e : c' = c
    · subst e
      rcases hh with (hh | rfl) | ⟨o, ho, h8', -, rfl⟩
      · unfold InRing at hh; omega
      · exact h3 cv
      · have := outN c' hc' o ho h8'; unfold Outside at this; omega
    · have := out c' hc' e b hb hh; unfold Outside at this; obtain ⟨hPc, hzc⟩ := hO.sc c' hc'
      have := (sc_lo hPc hzc).2.1; omega
  refine ⟨hS.sub, fun b hb => by rw [w.1]; exact hS.ks b hb, fun o h1 h2 => by rw [w.1]; exact hS.ksΩ o h1 h2,
    fun y hy hb hne => ?_, fun c' hc' => ?_, fun c' hc' => ?_, fun c' hc' h0' => ?_, hS.spSg,
    fun c' hc' h0' => ?_, hS.repSg⟩
  · rw [hsc y hy] at hb hne ⊢; rw [hcs] at hne ⊢; exact hS.disj y hy hb hne
  · obtain ⟨a1, a2, a3⟩ := maxA_facts hO hc'
    obtain ⟨hPc, hzc⟩ := hO.sc c' hc'
    have mvc := maxA_val hPc hzc
    have km : L.rmax s' c' = L.rmax s c' := kw c' hc' _ a1 a2 (by omega) (by omega)
    by_cases e : c' = c
    · subst e; exact (hS.all c' hc').mk' fun hm => hwf (by rw [← km]; exact hm)
    exact (hS.all c' hc').writesIn a1 ⟨a2, a3⟩ w (out c' hc' e)
  · obtain ⟨a1, a2, a3⟩ := maxA_facts hO hc'
    obtain ⟨hPc, hzc⟩ := hO.sc c' hc'
    have mvc := maxA_val hPc hzc
    rw [show L.rmax s' c' = L.rmax s c' from kw c' hc' _ a1 a2 (by omega) (by omega)]
    exact hS.act c' hc'
  · obtain ⟨hPc, hzc⟩ := hO.sc c' hc'
    obtain ⟨h8c, h128c, -⟩ := sc_lo hPc hzc
    have spv := sporA_val hPc hzc
    rw [kw c' hc' _ (by unfold Aligned; omega) (by omega) (by omega) (by omega)] at h0'
    exact hS.spor c' hc' h0'
  · obtain ⟨hPc, hzc⟩ := hO.sc c' hc'
    obtain ⟨h8c, h128c, -⟩ := sc_lo hPc hzc
    have rpv := scReplyA_val hPc hzc
    rw [kw c' hc' _ (by unfold Aligned; omega) (by omega) (by omega) (by omega)] at h0'
    exact hS.rep c' hc' h0'

/-- **`commit_time` keeps the invariants**: it charges the current SC's ring
and `CONSUMED` word and clears the node's `CONSUMED` word. -/
theorem sched.commit_time.blk {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (a : A)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    sched.commit_time st ar s a ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ L.actionW s' = L.actionW s ∧
      L.curW s' = L.curW s ∧ L.cscW s' = L.cscW s ∧ L.idleW s' = L.idleW s ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hO := hX.1
  have hc : L.cscW s ∈ Scs := hX.2.2.cur
  have hN' := h0.nodes _ h0.cur
  obtain ⟨hP, hz⟩ := hO.sc _ hc
  have cnv : layout.node.CONSUMED.val = 40 := by simp [layout.node.CONSUMED]
  have aC : Aligned (L.nodeA s layout.node.CONSUMED) := nodeAt_aligned hN' (by rw [cnv]; omega) (by rw [cnv])
  have oC : Outside (L.nodeA s layout.node.CONSUMED) (L.cscW s) (Z (L.cscW s)) :=
    node_out_place (fun b hb hin => hO.scW _ hc b hb hin) h0.omega h0.cur hN' (by rw [cnv]; omega) (by rw [cnv])
  refine WP.spec_mono (sched.commit_time.fr hA a (hS.all _ hc).1 rfl aC oC) fun s' ⟨w, wf'⟩ => ?_
  have inΩ : ∀ b, Aligned b → (InRing (L.cscW s) (Z (L.cscW s)) b ∨
      b = core.num.U64.wrapping_add (L.cscW s) layout.sc.CONSUMED) → b ∈ Ω := by
    rintro b hb (hh | rfl)
    · exact hO.scW _ hc b hb hh.inSC
    · obtain ⟨-, h128, -⟩ := sc_lo hP hz
      have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
      exact hO.scW _ hc _ hb ⟨by rw [hv]; simp, by rw [hv]; simp [layout.sc.CONSUMED]; omega⟩
  have wR : WritesIn st s s' (RingNode st (L.cscW s) (Z (L.cscW s)) s) := w.mono fun b hb => by
    rcases hb with hb | hb
    · exact Or.inl hb
    · exact Or.inr ⟨layout.node.CONSUMED, by rw [cnv]; unfold LowFree; omega, by rw [cnv], by rw [cnv]; omega, hb⟩
  have wF : WritesIn st s s' (L.Free s Ω Cs) := w.mono' fun b hb hh => by
    rcases hh with hh | rfl
    · exact Or.inl (inΩ b hb hh)
    · exact free_cur_node h0.cur (by rw [cnv]; unfold LowFree; omega)
  obtain ⟨h1, hB1⟩ := free_step h0 hB wF
  obtain ⟨ka, kc, ki, ks⟩ := free_keys h0 wF
  have fld : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := fun y hy K hK hK8 =>
    w.mem_eq (field_aligned (h0.tcbs y hy) hK hK8) fun hh => by
      rcases hh with hh | e
      · exact out_ne_field (h0.omega _ (inΩ _ (field_aligned (h0.tcbs y hy) hK hK8) hh)) hy (h0.tcbs y hy) hK rfl
      · exact node_ne_field hN' (by rw [cnv]; omega) hy (h0.tcbs y hy) hK e.symm
  have hcs : L.cscW s' = L.cscW s := by
    unfold LawfulStore.cscW; rw [cscW_eq w.1 w.2.1]
    refine w.mem_eq (nodeAt_aligned hN' (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])) ?_
    rintro (hh | e)
    · exact out_ne_node (h0.omega _ (inΩ _ (nodeAt_aligned hN' (by simp [layout.node.CUR_SC])
        (by simp [layout.node.CUR_SC])) hh)) h0.cur hN' (by simp [layout.node.CUR_SC]) rfl
    · have := congrArg UScalar.val e
      unfold LawfulStore.nodeA at this
      rw [nodeAt_val hN' (by simp [layout.node.CUR_SC]), nodeAt_val hN' (by rw [cnv]; omega)] at this
      simp [layout.node.CUR_SC, layout.node.CONSUMED] at this
  have hΩn : ∀ n ∈ Nt, OutsideObjs st T Cs s (ntfnBtA n) := fun n hn => h0.omega _ (hSg.sub _ (hO.ntB n hn).2)
  have hX1 : XInv st T Cs Ω Sg Rp Scs Nt Z s' :=
    hX.writes h0.tcbs (w.mono' (B := fun b => ¬ Prot T Rp Scs Nt b) fun b hb hh => by
        rcases hh with hh | rfl
        · exact not_prot_ring h0 hO hc hb hh
        · exact not_prot_node h0 hO hSg.sub h0.cur (by rw [cnv]; omega))
      (fun b hb => hb) (by rw [hcs]; exact hc)
      (hX.tn_writes h0 w fun b hb hh => by
        rcases hh with hh | rfl
        · exact notTmW_ring h0 hO hSg.sub hc hb hh
        · exact notTmW_node h0.tcbs h0.nodes hΩn h0.cur (by rw [cnv]; omega) (by rw [cnv]; omega)) ki
  exact ⟨⟨⟨Q, R, h1⟩, hB1, hX1, SCsOK.ringNode h0 hS hO hc wR ks hcs wf',
    ⟨hSg.sub, fun b hb => by rw [w.1]; exact hSg.ks b hb, fun o h1 h2 => by rw [w.1]; exact hSg.ksΩ o h1 h2⟩⟩,
    ka, kc, hcs, ki, fld⟩

/-! ## `configure_flags` -/

/-- `configure_flags`' first block: the SC's thread is stalled, taken out of
its release and ready queues, and the current SC charged if it is the SC. -/
theorem cfA {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (a : A) (i target : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hi : i ∈ T) (hna : ∀ y ∈ T, L.actionW s ≠ y) :
    (do
      let (s2, a2) ← smp.remote_tcb_stall st ar s a i
      let s3 ← sched.release_remove st s2 i
      let s4 ← sched.dequeue st s3 i
      let s5 ← sched.cur_sc st s4
      let b1 ← obj.Sc.Insts.CoreCmpPartialEqSc.eq s5 target
      let t ← if b1 then sched.commit_time st ar s4 a2 else ok s4
      ok (t, a2)) ⦃ r => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
        (L.mem r.1 (inqA i) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem r.1 (inqA i) &&& sched.Q_RELEASE) = 0#u64 ∧
        (∀ y ∈ T, L.actionW r.1 ≠ y) ∧ L.mem r.1 (scA i) = L.mem s (scA i) ∧ L.idleW r.1 = L.idleW s ⦄ := by
  have hT := h.1.choose_spec.choose_spec.tcbs
  refine WP.spec_bind (WP.spec_and (smp.remote_tcb_stall.blk hA s a i h) (smp.remote_tcb_stall.spec hA s a i)) ?_
  rintro ⟨s2, a2⟩ hh
  simp only [WP.uncurry'_pair] at hh ⊢
  obtain ⟨⟨h2, -, ea2, -, ei2⟩, hs2⟩ := hh
  have sc2 : L.mem s2 (scA i) = L.mem s (scA i) := by
    rcases hs2 with rfl | ⟨v, rfl⟩
    · rfl
    · obtain ⟨⟨Q, R, h0⟩, -⟩ := h
      rw [scA_eq]; exact field_wr_node h0 h0.cur (by simp [layout.node.IPI_PENDING]) (by simp [layout.node.IPI_PENDING])
        hi (by simp) (by simp)
  obtain ⟨⟨Q2, R2, q2⟩, hB2, hX2, hS2, hSg2⟩ := h2
  have hc2 := q2.aff i hi
  refine WP.spec_bind (WP.spec_and (sched.release_remove.sch s2 i Q2 R2 q2 hB2 hSg2 hi)
    (sched.release_remove.foot s2 i _ q2.tcbs hi (q2.nodes _ hc2) (q2.nodes _ q2.cur) (q2.release _ hc2)
      (q2.released i hi).1)) ?_
  rintro s3 ⟨⟨⟨⟨Q3, R3, q3⟩, hB3, f3⟩, ea3, -, -⟩, -, iq3⟩
  have hc3 := q3.aff i hi
  have hp3 := q3.prio i hi
  have r3 : (L.mem s3 (inqA i) &&& sched.Q_RELEASE) = 0#u64 := by
    rw [iq3]; split
    · exact andn_qr_qr _
    · rename_i hn; exact not_not.1 hn
  refine WP.spec_bind (WP.spec_and (sched.dequeue.sch s3 i Q3 R3 q3 hB3 (hSg2.fr f3) hi)
    (sched.dequeue.foot s3 i _ q3.tcbs hi hp3 (q3.nodes _ hc3) (q3.nodes _ q3.cur) ((q3.ready _ hc3).1.rel _ hp3)
      (q3.queued i hi).1)) ?_
  rintro s4 ⟨⟨⟨⟨Q4, R4, q4⟩, hB4, f4⟩, ea4, -⟩, -, iq4⟩
  have r4 : (L.mem s4 (inqA i) &&& sched.Q_RELEASE) = 0#u64 := by
    rw [iq4]; split
    · rw [andn_qq_qr]; exact r3
    · exact r3
  have n4 : (L.mem s4 (inqA i) &&& sched.Q_QUEUED) = 0#u64 := by
    rw [iq4]; split
    · exact andn_qq_qq _
    · rename_i hn; exact not_not.1 hn
  have h4 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s4 :=
    ⟨⟨Q4, R4, q4⟩, hB4, (hX2.fr f3).fr f4, (hS2.fr f3).fr f4, (hSg2.fr f3).fr f4⟩
  have sc4 : L.mem s4 (scA i) = L.mem s (scA i) := by rw [f4.sc i hi, f3.sc i hi, sc2]
  have ea : L.actionW s4 = L.actionW s := by rw [ea4, ea3, ea2]
  have ei : L.idleW s4 = L.idleW s := by
    have e4 := f4.idle; have e3 := f3.idle; rw [e4, e3, ei2]
  step with sched.cur_sc.spec as ⟨s5, _⟩
  refine WP.spec_bind (Pₘ := fun _ => True) (by unfold obj.Sc.Insts.CoreCmpPartialEqSc.eq; simp) fun b1 _ => ?_
  refine WP.spec_bind (Pₘ := fun t5 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac t5 ∧ L.actionW t5 = L.actionW s4 ∧
      L.idleW t5 = L.idleW s4 ∧ ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        L.mem t5 (core.num.U64.wrapping_add y K) = L.mem s4 (core.num.U64.wrapping_add y K)) ?_ ?_
  · split
    · exact WP.spec_mono (sched.commit_time.blk hA a2 h4) fun t5 ⟨h5, e1, _, _, e2, e3⟩ => ⟨h5, e1, e2, e3⟩
    · exact (WP.spec_ok _).2 ⟨h4, rfl, rfl, fun _ _ _ _ _ => rfl⟩
  rintro t5 ⟨h5, ea5, ei5, fl5⟩
  refine (WP.spec_ok _).2 ⟨h5, by rw [inqA_eq, fl5 i hi _ (by simp) (by simp), ← inqA_eq]; exact n4,
    by rw [inqA_eq, fl5 i hi _ (by simp) (by simp), ← inqA_eq]; exact r4,
    fun y hy => by rw [ea5, ea]; exact hna y hy,
    by rw [scA_eq, fl5 i hi _ (by simp) (by simp), ← scA_eq]; exact sc4, by rw [ei5, ei]⟩

/-- **A write of a free word of any core's node** (not the timer-tree or
`CUR_SC` words) keeps the invariants. -/
theorem node_any_blk {c o v : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hc : c ∈ Cs) (ho : LowFree o.val)
    (hto : o.val ≠ 88 ∧ o.val ≠ 104 ∧ o.val ≠ 112) (h24 : o.val ≠ 24) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s (L.nodeAt s c o) v) ∧
      L.actionW (L.wr s (L.nodeAt s c o) v) = L.actionW s ∧ L.curW (L.wr s (L.nodeAt s c o) v) = L.curW s ∧
      L.cscW (L.wr s (L.nodeAt s c o) v) = L.cscW s ∧ L.idleW (L.wr s (L.nodeAt s c o) v) = L.idleW s ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        L.mem (L.wr s (L.nodeAt s c o) v) (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hO := hX.1
  have hN := h0.nodes c hc
  have hN' := h0.nodes _ h0.cur
  have ho' : o.val < 4288 := by unfold LowFree at ho; omega
  have h8 : o.val % 8 = 0 := by unfold LowFree at ho; omega
  have ha := nodeAt_aligned hN ho' h8
  have wF : WritesIn st s (L.wr s (L.nodeAt s c o) v) (L.Free s Ω Cs) := free_node_write rfl hc hN ho
  obtain ⟨h1, hB1⟩ := free_step h0 hB wF
  obtain ⟨ka, kc, ki, ks⟩ := free_keys h0 wF
  have csv : layout.node.CUR_SC.val = 24 := by simp [layout.node.CUR_SC]
  have hcsne : (L.nodeAt s c o).val ≠ (L.nodeA s layout.node.CUR_SC).val :=
    node_ne_node hN hN' ho' (by rw [csv]; omega) (fun _ => by rw [csv]; exact h24)
  have hcs : L.cscW (L.wr s (L.nodeAt s c o) v) = L.cscW s := by
    unfold LawfulStore.cscW
    rw [cscW_eq (L.ksb_wr _ _ _) (L.cpu_wr _ _ _)]
    exact L.mem_wr_ne ha (nodeAt_aligned hN' (by rw [csv]; omega) (by rw [csv])) hcsne
  have hΩn : ∀ n ∈ Nt, OutsideObjs st T Cs s (ntfnBtA n) := fun n hn => h0.omega _ (hSg.sub _ (hO.ntB n hn).2)
  obtain ⟨hrΩ, hcΩ⟩ := objs_omega hO hSg.sub
  have no : ∀ b ∈ Ω, (L.nodeAt s c o).val ≠ b.val := fun b hb => out_ne_node (h0.omega _ hb) hc hN ho'
  have hX1 : XInv st T Cs Ω Sg Rp Scs Nt Z (L.wr s (L.nodeAt s c o) v) :=
    hX.writes h0.tcbs (writesIn_wr ha) (fun b hb => hb ▸ not_prot_node h0 hO hSg.sub hc ho')
      (by rw [hcs]; exact hX.2.2.cur)
      (hX.tn_writes h0 (writesIn_wr ha) fun b _ e => e ▸ notTmW_node h0.tcbs h0.nodes hΩn hc ho' hto) ki
  have hS1 : SCsOK st T Ω Sg Scs Z Ac (L.wr s (L.nodeAt s c o) v) :=
    SCsOK.wr h0 hS hX ha (fun y hy e => node_ne_field hN ho' hy (h0.tcbs y hy) (K := 3464#u64) (by simp)
        (by have := UScalar.eq_of_val_eq e; rwa [scA_eq] at this)) hcsne
      (fun c' hc' => ⟨no _ (hcΩ c' hc').2.2.1, no _ (hcΩ c' hc').2.2.2.1, no _ (hcΩ c' hc').2.2.2.2⟩)
      (fun c' hc' => no _ (hSg.sub _ (hS.spSg c' hc')))
      (fun c' hc' e => absurd e (no _ (hSg.sub _ (hO.repW c' hc'))))
  exact ⟨⟨⟨Q, R, h1⟩, hB1, hX1, hS1,
    ⟨hSg.sub, fun b hb => by rw [L.ksb_wr]; exact hSg.ks b hb, fun o h1 h2 => by rw [L.ksb_wr]; exact hSg.ksΩ o h1 h2⟩⟩,
    ka, kc, hcs, ki, fun y hy K hK hK8 => field_wr_node h0 hc ho' h8 hy hK hK8⟩

abbrev NodeK (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s s' : S) : Prop :=
  L.actionW s' = L.actionW s ∧ L.curW s' = L.curW s ∧ L.cscW s' = L.cscW s ∧ L.idleW s' = L.idleW s ∧
    (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K))

theorem NodeK.refl (s : S) : NodeK st T s s := ⟨rfl, rfl, rfl, rfl, fun _ _ _ _ _ => rfl⟩

theorem NodeK.trans {s₁ s₂ s₃ : S} (h₁ : NodeK st T s₁ s₂) (h₂ : NodeK st T s₂ s₃) : NodeK st T s₁ s₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.1.trans h₁.2.2.2.1,
    fun y hy K a b => (h₂.2.2.2.2 y hy K a b).trans (h₁.2.2.2.2 y hy K a b)⟩

theorem smp.remote_reschedule.blk {A : Type _} {ar : machine.Arch A} (a : A) (cpu : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    smp.remote_reschedule st ar s a cpu ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ NodeK st T s s' ⦄ := by
  have hc := h.1.choose_spec.choose_spec.cur
  unfold smp.remote_reschedule
  step with LawfulStore.cur_cpu_spec as ⟨i, ei⟩
  subst ei
  split
  · step with obj.node_get.spec as ⟨i1, _⟩
    try simp only [lift, bind_ok]
    step as ⟨i3, _⟩
    try simp only [lift, bind_ok]
    refine WP.spec_bind (obj.node_set.spec s _ _ _) fun s1 e1 => ?_
    subst e1
    simp only [WP.spec_ok, WP.uncurry'_pair]
    exact node_any_blk h hc (by rw [ipi_val]; unfold LowFree; omega) (by rw [ipi_val]; omega) (by rw [ipi_val]; omega)
  · simp only [WP.spec_ok, WP.uncurry'_pair]; exact ⟨h, NodeK.refl _⟩

theorem sched.set_reprogram_on.blk (cpu : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hc : cpu ∈ Cs) :
    sched.set_reprogram_on st s cpu ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ NodeK st T s s' ⦄ := by
  unfold sched.set_reprogram_on
  refine WP.spec_mono (obj.node_set.spec s cpu _ _) fun s' e => ?_
  subst e
  exact node_any_blk h hc (by rw [repr_val]; unfold LowFree; omega) (by rw [repr_val]; omega) (by rw [repr_val]; omega)

set_option maxHeartbeats 4000000 in
/-- `configure_flags`' last block for a bound SC: the thread migrates to the
SC's core, the SC is resumed, and the thread is switched to, enqueued or
the remote core told to reprogram; the current core reschedules if the
thread is current. -/
theorem cfD {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s3 : S) (a1 : A) (i target cpu : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s3) (hi : i ∈ T)
    (htq : (L.mem s3 (inqA i) &&& sched.Q_QUEUED) = 0#u64) (htr : (L.mem s3 (inqA i) &&& sched.Q_RELEASE) = 0#u64)
    (hsc : L.mem s3 (scA i) = target) (ht0 : target ≠ 0#u64) (htS : target ∈ Scs) (htA : target ∈ Ac)
    (hcpu : cpu ∈ Cs) (hna : ∀ y ∈ T, L.actionW s3 ≠ y) :
    (do
  let (s5, a3) ←
    smp.migrate_tcb st ar s3 a1 i cpu
  let (s6, a4) ←
    schedcontext.resume st ar s5 a3 target
  let i1 ← st.cur_cpu s6
  let (s7, a5) ←
    if cpu = i1
    then
      do
      let b1 ← sched.is_runnable st s6 i
      let t ←
        if b1
        then
          do
          let t1 ← sched.cur_thread st s6
          let b2 ←
            core.cmp.PartialEq.ne.trait_default
              obj.Tcb.Insts.CoreCmpPartialEqTcb i t1
          if b2
          then sched.possible_switch_to st s6 i
          else ok s6
        else ok s6
      ok (t, a4)
    else
      do
      let b1 ← sched.is_schedulable st s6 i
      if b1
      then
        let s8 ← sched.enqueue st s6 i
        smp.remote_reschedule st ar s8 a4 cpu
      else
        let s8 ← sched.set_reprogram_on st s6 cpu
        smp.remote_reschedule st ar s8 a4 cpu
  let t ← sched.cur_thread st s7
  let b1 ← obj.Tcb.Insts.CoreCmpPartialEqTcb.eq i t
  let t1 ←
    if b1
    then sched.reschedule_required st s7
    else ok s7
  ok (t1, a5)) ⦃ r => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  refine WP.spec_bind (migrate_tail hA s3 a1 target i cpu Q R h0 hB hX hS hSg hi htq htr hcpu htS) ?_
  rintro ⟨s5, a3⟩ hh
  simp only [WP.uncurry'_pair] at hh ⊢
  obtain ⟨⟨⟨Q5, R5, h5⟩, hB5, hX5, hS5, hSg5⟩, -, -, -, ⟨sc5, -, ea5⟩⟩ := hh
  have sc5' : L.mem s5 (scA i) = target := sc5.trans hsc
  have tc5 : L.mem s5 (scTcbA target) = i := by
    have := (hX5.2.2.bound i hi (by rw [sc5']; exact ht0)).2.1; rwa [sc5'] at this
  refine WP.spec_bind (schedcontext.resume.all hA s5 a3 target Q5 R5 h5 hB5 hX5 hSg5 hS5 fun _ _ => ?_) ?_
  · rw [tc5]
    exact ⟨hi, h5.omega _ ((objs_omega hX5.1 hSg5.sub).2 target htS).2.1, hX5.2.2.core target htS,
      by rw [ea5]; exact hna i hi⟩
  rintro ⟨s6, a4⟩ hh
  simp only [WP.uncurry'_pair] at hh ⊢
  obtain ⟨Q6, R6, h6, hB6, hX6, hSg6, f6⟩ := hh
  have hS6 := hS5.fr f6
  have sc6 : L.mem s6 (scA i) = target := (f6.sc i hi).trans sc5'
  have hb6 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s6 := ⟨⟨Q6, R6, h6⟩, hB6, hX6, hS6, hSg6⟩
  step with LawfulStore.cur_cpu_spec as ⟨i1, ei1⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1) ?_ ?_
  · split
    · step with sched.is_runnable.spec' as ⟨b1, hb1⟩
      refine WP.spec_bind (Pₘ := fun t => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac t) ?_ fun t ht => (WP.spec_ok _).2 ht
      split
      · rename_i hb1t
        step with sched.cur_thread.spec as ⟨t1, _⟩
        step with tcb_ne.blk as ⟨b2, _⟩
        split
        · exact WP.spec_mono (sched.possible_switch_to.sch s6 i Q6 R6 h6 hB6 hSg6 hi (hb1 hb1t)
            (fun _ => by rw [sc6]; exact htA)) fun s7 ⟨⟨⟨Q7, R7, h7⟩, hB7, f7⟩, _, _⟩ =>
              ⟨⟨Q7, R7, h7⟩, hB7, hX6.fr f7, hS6.fr f7, hSg6.fr f7⟩
        · exact (WP.spec_ok _).2 hb6
      · exact (WP.spec_ok _).2 hb6
    · step with sched.is_schedulable.spec' as ⟨b1, eb1⟩
      split
      · rename_i hb1
        obtain ⟨hrun, hbd, hrl, hrm⟩ := eb1 hb1
        have hA6 : L.mem s6 (scA i) ∈ Ac := (hS6.act _ (hX6.2.2.bound i hi hbd).1).2 hrm
        refine WP.spec_bind (sched.enqueue.sch s6 i Q6 R6 h6 hB6 hSg6 hi (fun _ => hrl) (fun _ => hrun)
          (fun _ => hbd) (fun _ => hA6)) ?_
        rintro s8 ⟨⟨⟨Q8, R8, h8⟩, hB8, f8⟩, -, -, -⟩
        exact WP.spec_mono (smp.remote_reschedule.blk a4 cpu ⟨⟨Q8, R8, h8⟩, hB8, hX6.fr f8, hS6.fr f8, hSg6.fr f8⟩)
          fun r hr => by obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at hr ⊢; exact hr.1
      · refine WP.spec_bind (sched.set_reprogram_on.blk cpu hb6 hcpu) fun s8 hh8 => ?_
        exact WP.spec_mono (smp.remote_reschedule.blk a4 cpu hh8.1)
          fun r hr => by obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at hr ⊢; exact hr.1
  rintro ⟨s7, a5⟩ h7
  try simp only [WP.uncurry'_pair] at h7 ⊢
  step with sched.cur_thread.spec as ⟨t, _⟩
  step with tcb_eq.blk as ⟨b1, _⟩
  refine WP.spec_bind (Pₘ := fun t1 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac t1) ?_ fun t1 h => (WP.spec_ok _).2 h
  split
  · obtain ⟨⟨Q7, R7, q7⟩, hB7, hX7, hS7, hSg7⟩ := h7
    exact WP.spec_mono (sched.reschedule_required.sch s7 Q7 R7 q7 hB7 hSg7)
      fun s' ⟨⟨⟨Q', R', q'⟩, hB', f'⟩, _, _, _⟩ => ⟨⟨Q', R', q'⟩, hB', hX7.fr f', hS7.fr f', hSg7.fr f'⟩
  · exact (WP.spec_ok _).2 h7

/-! ## The decoder's reads -/

theorem obj.Sc.set_cpu.wr (s : S) (c : obj.Sc) (v : U64) :
    obj.Sc.set_cpu st c s v ⦃ s' => s' = L.wr s (scCoreA c) v ⦄ := by
  unfold obj.Sc.set_cpu; step*; simp_all [scCoreA]

theorem obj.Sc.set_badge.wr (s : S) (c : obj.Sc) (v : U64) :
    obj.Sc.set_badge st c s v ⦃ s' => s' = L.wr s (core.num.U64.wrapping_add c layout.sc.BADGE) v ⦄ := by
  unfold obj.Sc.set_badge; step*; simp_all

theorem sporadic.refill_absolute_max.val (sz : U64) :
    sporadic.refill_absolute_max sz ⦃ m => m.val = absMax sz.val ⦄ := by
  unfold sporadic.refill_absolute_max
  split
  · rename_i h; simp [absMax]; simp [UScalar.le_equiv] at h; omega
  · rename_i h
    have h64 : sz.val < 64 := by simp [UScalar.le_equiv] at h; omega
    simp only [lift, bind_ok]
    have hm : (sz &&& 63#u64).val = sz.val := by
      have : (sz &&& 63#u64).val = sz.val % 64 := by
        rw [UScalar.val_and]; simp [Nat.and_two_pow_sub_one_eq_mod _ 6]
      rw [this]; omega
    step as ⟨b, hb⟩
    have hbv : b.val = 2 ^ sz.val := by
      rw [hb]; simp [hm]
      try (rw [Nat.mod_eq_of_lt]; exact Nat.pow_lt_pow_right (by norm_num) h64)
    split
    · rename_i hlt
      simp [absMax, show ¬ (64 ≤ sz.val) by omega]
      simp [UScalar.lt_equiv, layout.sc.REFILLS] at hlt; omega
    · rename_i hlt
      simp [UScalar.lt_equiv, layout.sc.REFILLS] at hlt
      step*
      simp [absMax, show ¬ (64 ≤ sz.val) by omega]
      simp_all [layout.sc.REFILLS, layout.sc.REFILL_SIZE]

theorem schedcontext.extra_cap.gen {s : S} {extra : Aeneas.Std.Array obj.Slot 3#usize} {P : capability.Cap → Prop}
    (hx : ∀ sl ∈ extra.val, sl ≠ 0#u64 → obj.Slot.cap st sl s ⦃ c => P c ⦄) :
    schedcontext.extra_cap st s extra 0#usize ⦃ o => ∀ c, o = some c → P c ⦄ := by
  unfold schedcontext.extra_cap
  have hl0 : (0#usize).val < extra.val.length := by rw [extra.property]; simp
  split
  · simp_all
  refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec extra 0#usize hl0) fun sl hsl => ?_
  simp only [obj.Slot.is_null, bind_ok]
  split
  · simp
  rename_i h0
  refine WP.spec_bind (hx sl (hsl ▸ List.getElem_mem hl0) (by simpa using h0)) fun c hc => ?_
  exact (WP.spec_ok _).2 fun c' e => by cases e; exact hc

set_option maxHeartbeats 8000000 in
/-- **seL4 `schedControl_configureFlags` keeps the invariants**, the SC made
active (`insert target Ac`): its thread (if any) is taken out of the queues,
the refills are rewritten, the SC moves to `cpu`, the thread migrates and is
resumed, then the badge and the sporadic flag are set. -/
theorem schedcontext.configure_flags.blk {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (a : A)
    (target cpu budget period max_refills badge flags : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (htS : target ∈ Scs) (ht0 : target ≠ 0#u64) (hcpu : cpu ∈ Cs)
    (h2 : sporadic.MIN_REFILLS.val ≤ max_refills.val) (hm : max_refills.val ≤ absMax (Z target))
    (hna : ∀ y ∈ T, L.actionW s ≠ y) :
    schedcontext.configure_flags st ar s a target cpu budget period max_refills badge flags ⦃ r =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z (insert target Ac) r.1 ⦄ := by
  have hX := h.2.2.1
  have hO := hX.1
  obtain ⟨hP, hz⟩ := hO.sc target htS
  have hTA : target ∈ insert target Ac := Set.mem_insert _ _
  unfold schedcontext.configure_flags
  step with obj.Sc.tcb.spec as ⟨i, ei⟩
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  have hiT : i ≠ 0#u64 → i ∈ T := fun h0 => by rw [ei]; exact hX.2.2.yt.1 target htS (by rw [← ei]; exact h0)
  have hsci : i ≠ 0#u64 → L.mem s (scA i) = target := fun h0 => by
    rw [ei]; exact hX.2.2.tsc target htS ht0 (by rw [← ei]; exact h0)
  have hbi : b = false → i ≠ 0#u64 := fun hf e => by rw [eb, e] at hf; simp at hf
  -- the thread out of the queues
  refine WP.spec_bind (Pₘ := fun r : S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
      (b = false → (L.mem r.1 (inqA i) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem r.1 (inqA i) &&& sched.Q_RELEASE) = 0#u64 ∧
        L.mem r.1 (scA i) = target) ∧ (∀ y ∈ T, L.actionW r.1 ≠ y)) ?_ ?_
  · split
    · rename_i hb
      exact (WP.spec_ok _).2 ⟨h, fun hf => absurd (hf.symm.trans hb) (by simp), hna⟩
    · rename_i hb
      have hi0 : i ≠ 0#u64 := hbi (by simpa using hb)
      exact WP.spec_mono (cfA hA a i target h (hiT hi0) hna) fun r ⟨h1, q1, r1, a1, s1, _⟩ =>
        ⟨h1, fun _ => ⟨q1, r1, s1.trans (hsci hi0)⟩, a1⟩
  rintro ⟨s1, a1⟩ ⟨h1, hq1, ha1⟩
  try simp only [WP.uncurry'_pair]
  -- the refills
  have keep : ∀ s2 : S, BlkOK st T Cs Ω H Sg Rp Scs Nt Z (insert target Ac) s2 →
      L.actionW s2 = L.actionW s1 →
      (∀ y ∈ T, L.mem s2 (scA y) = L.mem s1 (scA y) ∧ L.mem s2 (stA y) = L.mem s1 (stA y) ∧
        L.mem s2 (inqA y) = L.mem s1 (inqA y)) →
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z (insert target Ac) s2 ∧
      (b = false → (L.mem s2 (inqA i) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s2 (inqA i) &&& sched.Q_RELEASE) = 0#u64 ∧
        L.mem s2 (scA i) = target) ∧ (∀ y ∈ T, L.actionW s2 ≠ y) := fun s2 h2' ea fl =>
    ⟨h2', fun hf => by
      have hiT' := hiT (hbi hf)
      obtain ⟨q, r, sc⟩ := hq1 hf
      rw [(fl i hiT').2.2, (fl i hiT').1]; exact ⟨q, r, sc⟩, fun y hy => by rw [ea]; exact ha1 y hy⟩
  have RN : ∀ m bud per : U64, sporadic.MIN_REFILLS.val ≤ m.val → m.val ≤ absMax (Z target) →
      sporadic.refill_new st s1 target m bud per ⦃ s2 =>
        BlkOK st T Cs Ω H Sg Rp Scs Nt Z (insert target Ac) s2 ∧
        (b = false → (L.mem s2 (inqA i) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s2 (inqA i) &&& sched.Q_RELEASE) = 0#u64 ∧
          L.mem s2 (scA i) = target) ∧ (∀ y ∈ T, L.actionW s2 ≠ y) ⦄ := fun m bud per hm2 hmm =>
    WP.spec_mono (sporadic.refill_new.fr m bud per hP hz hm2 hmm) fun s2 ⟨wf, w⟩ => by
      obtain ⟨h2', ea, -, -, fl⟩ := refill_blk h1 htS w wf
      exact keep s2 h2' ea fl
  have RU : ∀ per bud m : U64, sporadic.MIN_REFILLS.val ≤ m.val → m.val ≤ absMax (Z target) →
      sporadic.refill_update st s1 target per bud m ⦃ s2 =>
        BlkOK st T Cs Ω H Sg Rp Scs Nt Z (insert target Ac) s2 ∧
        (b = false → (L.mem s2 (inqA i) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s2 (inqA i) &&& sched.Q_RELEASE) = 0#u64 ∧
          L.mem s2 (scA i) = target) ∧ (∀ y ∈ T, L.actionW s2 ≠ y) ⦄ := fun per bud m hm2 hmm =>
    WP.spec_mono (sporadic.refill_update.fr per bud m hP hz hm2 hmm) fun s2 ⟨wf, w⟩ => by
      obtain ⟨h2', ea, -, -, fl⟩ := refill_blk h1 htS w wf
      exact keep s2 h2' ea fl
  have hmin : sporadic.MIN_REFILLS.val ≤ absMax (Z target) := h2.trans hm
  refine WP.spec_bind (Pₘ := fun s2 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z (insert target Ac) s2 ∧
      (b = false → (L.mem s2 (inqA i) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s2 (inqA i) &&& sched.Q_RELEASE) = 0#u64 ∧
        L.mem s2 (scA i) = target) ∧ (∀ y ∈ T, L.actionW s2 ≠ y)) ?_ ?_
  · split
    · exact RN _ _ _ (le_refl _) hmin
    · step with obj.Sc.cpu.spec as ⟨i1, _⟩
      split
      · step with sporadic.sc_active.val as ⟨b1, _⟩
        split
        · split
          · exact RN _ _ _ h2 hm
          · step with sched.is_runnable.spec' as ⟨b2, _⟩
            split
            · exact RU _ _ _ h2 hm
            · exact RN _ _ _ h2 hm
        · exact RN _ _ _ h2 hm
      · exact RN _ _ _ h2 hm
  rintro s2 ⟨h2', hq2, ha2⟩
  -- the core
  refine WP.spec_bind (obj.Sc.set_cpu.wr s2 target cpu) fun s3 e3 => ?_
  subst e3
  obtain ⟨h3, ea3, -, -, fl3⟩ := scword_blk h2' htS hTA (Or.inl (scCoreA_val hP hz)) (fun _ => hcpu)
  -- the thread
  refine WP.spec_bind (Pₘ := fun r : S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z (insert target Ac) r.1) ?_ ?_
  · split
    · exact (WP.spec_ok _).2 h3
    · rename_i hb
      have hbf : b = false := by simpa using hb
      have hiT' := hiT (hbi hbf)
      obtain ⟨q2, r2, sc2⟩ := hq2 hbf
      exact cfD hA _ a1 i target cpu h3 hiT' (by rw [(fl3 i hiT').2.2]; exact q2)
        (by rw [(fl3 i hiT').2.2]; exact r2) (by rw [(fl3 i hiT').1]; exact sc2) ht0 htS hTA hcpu
        (fun y hy => by rw [ea3]; exact ha2 y hy)
  rintro ⟨s4, a2⟩ h4
  try simp only [WP.uncurry'_pair] at h4 ⊢
  -- the badge and the sporadic flag
  refine WP.spec_bind (obj.Sc.set_badge.wr s4 target badge) fun s5 e5 => ?_
  subst e5
  have h5 := (scword_blk (v := badge) h4 htS hTA (Or.inr (Or.inl (by
    rw [sc_word_val hP hz (o := layout.sc.BADGE) (by simp [layout.sc.BADGE])]; simp [layout.sc.BADGE])))
    (fun e => by
      have := congrArg UScalar.val e
      rw [sc_word_val hP hz (o := layout.sc.BADGE) (by simp [layout.sc.BADGE]), scCoreA_val hP hz] at this; simp [layout.sc.BADGE] at this)).1
  simp only [lift, bind_ok]
  have spv : ∀ v : U64, BlkOK st T Cs Ω H Sg Rp Scs Nt Z (insert target Ac)
      (L.wr (L.wr s4 (core.num.U64.wrapping_add target layout.sc.BADGE) badge)
        (core.num.U64.wrapping_add target layout.sc.SPORADIC) v) := fun v =>
    (scword_blk (v := v) h5 htS hTA (Or.inr (Or.inr (by
      rw [sc_word_val hP hz (o := layout.sc.SPORADIC) (by simp [layout.sc.SPORADIC])]; simp [layout.sc.SPORADIC])))
      (fun e => by
        have := congrArg UScalar.val e
        rw [sc_word_val hP hz (o := layout.sc.SPORADIC) (by simp [layout.sc.SPORADIC]), scCoreA_val hP hz] at this
        simp [layout.sc.SPORADIC] at this)).1
  split
  · exact WP.spec_bind (obj.Sc.set_sporadic.wr _ target 1#u64) fun s6 e6 => (WP.spec_ok _).2 (by subst e6; exact spv _)
  · exact WP.spec_bind (obj.Sc.set_sporadic.wr _ target 0#u64) fun s6 e6 => (WP.spec_ok _).2 (by subst e6; exact spv _)

/-! ## The decode -/

/-- **`SchedControl`'s placement premises** (P3's, from `JPlaced.sc`): the
`SchedControl` cap's core is a core, and an SC cap in an extra slot has its
object's size bits. -/
structure ScCtlPlace (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop) : Prop where
  core : ∀ (Ac : Set U64) (s : S) (cap : capability.Cap) (extra : Aeneas.Std.Array obj.Slot 3#usize),
    EntAt st P3Ok s → DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra → ∀ cpu, cap = .SchedControl cpu → cpu ∈ Cs
  size : ∀ (Ac : Set U64) (s : S) (cap : capability.Cap) (extra : Aeneas.Std.Array obj.Slot 3#usize),
    EntAt st P3Ok s → DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra → ∀ sl ∈ extra.val, sl ≠ 0#u64 →
      obj.Slot.cap st sl s ⦃ c => ∀ ptr sz, c = .SchedContext ptr sz → sz.val = Z ptr ⦄

set_option hygiene false in
/-- An error leaf with the state unchanged. -/
local macro "errD" : tactic => `(tactic| first
  | exact (WP.spec_ok _).2 (DecPost.of_bxi D.bxi (by simp))
  | (simp only [error.range, error.illegal, error.truncated, error.invalid_cap, bind_ok]
     exact (WP.spec_ok _).2 (DecPost.of_bxi D.bxi (by simp))))

set_option maxHeartbeats 8000000 in
/-- **`SchedControl_ConfigureFlags`** keeps the invariants, from `ScCtlPlace`. -/
theorem schedcontext.decode_sched_control.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {U : Set U64} (Pl : ScCtlPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) {a : A} {lbl cpu len buf : U64}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.SchedControl cpu) extra)
    (hE : EntAt st P3Ok s) :
    schedcontext.decode_sched_control st ar s a lbl cpu len buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hct : L.curW s ∈ T := D.bxi.1.choose_spec.choose_spec.curT
  have hT := D.bxi.1.choose_spec.choose_spec.tcbs
  have hcpu := Pl.core Ac s _ extra hE D cpu rfl
  unfold schedcontext.decode_sched_control
  split
  · errD
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  refine WP.spec_bind (schedcontext.extra_cap.gen (P := fun c => CapOK st T Rp Scs Nt H s c ∧
      ∀ ptr sz, c = .SchedContext ptr sz → sz.val = Z ptr)
    (fun sl hsl h0 => WP.spec_and (D.extra s (WritesIn.refl _ _) sl hsl h0) (Pl.size Ac s _ extra hE D sl hsl h0))) ?_
  rintro o ho
  rcases o with _ | c
  · errD
  obtain ⟨hcO, hsz⟩ := ho c rfl
  simp only
  split
  · errD
  refine WP.spec_bind (P0.sporadic.max_period_us.p0 ar a hA) fun max_us _ => ?_
  step with sporadic.min_budget_us.spec as ⟨min_us, _⟩
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s ct buf 0#u64 hS) fun budget_us _ => ?_
  split
  · errD
  refine WP.spec_bind (hA.us_to_ticks a budget_us) fun budget _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s ct buf 1#u64 hS) fun period_us _ => ?_
  split
  · errD
  refine WP.spec_bind (hA.us_to_ticks a period_us) fun period _ => ?_
  refine WP.spec_bind (sporadic.min_budget.ok hA a) fun mb _ => ?_
  split
  · errD
  split
  · errD
  split
  · errD
  cases c
  all_goals first | errD | skip
  rename_i ptr sz
  obtain ⟨hpS, hp0, -⟩ := hcO.2.2 ptr sz rfl
  have hszv := hsz ptr sz rfl
  dsimp only
  obtain ⟨hP, hz⟩ := D.bxi.2.2.1.1.sc ptr hpS
  have h64 := hP.lt64
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s ct buf 2#u64 hS) fun er _ => ?_
  refine WP.spec_bind (sporadic.refill_absolute_max.val sz) fun mr hmr => ?_
  rw [hszv] at hmr
  have hab : 2 ≤ absMax (Z ptr) := by
    unfold absMax; rw [if_neg (by omega)]
    have : 2 ^ 7 ≤ 2 ^ Z ptr := Nat.pow_le_pow_right (by norm_num) hz
    omega
  have hlt := absMax_lt (Z ptr)
  simp only [lift, bind_ok]
  split
  · errD
  rename_i hle
  have hsub : (core.num.U64.wrapping_sub mr sporadic.MIN_REFILLS).val = mr.val - 2 := by
    simp [core.num.U64.wrapping_sub_val_eq, sporadic.MIN_REFILLS, U64.size_def, U64.numBits]; omega
  have hle' : er.val ≤ mr.val - 2 := by have := hle; rw [gt_iff_val, hsub] at this; omega
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s ct buf 3#u64 hS) fun badge _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s ct buf 4#u64 hS) fun flags _ => ?_
  have ect' : ct = L.curW s := ect
  subst ect'
  have hr := runnable_ok D.run
  refine WP.spec_bind (sched.set_thread_state.restart_blk (Es := ∅) s _ D.bxi.blk hct hr.1 hr.2) ?_
  rintro s1 ⟨h1, -, -, k1⟩
  try simp only [lift, bind_ok]
  have hadd : (core.num.U64.wrapping_add er sporadic.MIN_REFILLS).val = er.val + 2 := by
    simp [core.num.U64.wrapping_add_val_eq, sporadic.MIN_REFILLS, U64.size_def, U64.numBits]; omega
  have hna : ∀ y ∈ T, L.actionW s1 ≠ y := fun y hy e => by
    rcases k1.act with e' | e'
    · rw [e', D.act] at e; exact notT_small hT (by simp) (e ▸ hy)
    · rw [e'] at e; exact notT_small hT (by simp) (e ▸ hy)
  refine WP.spec_bind (schedcontext.configure_flags.blk hA a ptr cpu budget period _ badge flags h1 hpS hp0 hcpu
    (by rw [hadd]; simp [sporadic.MIN_REFILLS]) (by rw [hadd]; omega) hna) ?_
  rintro ⟨s2, a2⟩ h2
  exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h2))

/-- **InvGaps' `schedControl`, discharged** from `ScCtlPlace`. -/
theorem decGap_schedControl {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {U : Set U64}
    (Pl : ScCtlPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .schedControl := by
  intro Ac s a lbl len slot cap blk call don fp buf extra hf D _hslot hE
  cases cap <;> simp [capFam] at hf
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec as ⟨ct, _⟩
  try dsimp only
  split
  · exact (WP.spec_ok _).2 (DecPost.keep D.bxi (by simp))
  · exact schedcontext.decode_sched_control.dec hA Pl D hE

end

end Fl4Proofs.P1
