/-
P1: `bind_tcb` (seL4 `schedContext_bindTCB`) keeps `BlkOK`.  Its two writes
(the thread's `SC` field, then the SC's `TCB` word) leave the same words as
`donate`'s (in the other order), so `donate_pair` applies through `agree_all`.
-/
import Fl4Proofs.P1.QueueTcbInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}

/-- The invariants only read words: a state that agrees with one meeting them
on every aligned word (and on `ksb` and the CPU) meets them too. -/
theorem agree_all {X : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s)
    (hk : L.ksb s' = L.ksb s) (hc : L.cpu s' = L.cpu s) (hm : ∀ b, Aligned b → L.mem s' b = L.mem s b) :
    SchedQueuesInvX st T Cs Ω H X s' Q R ∧ BoundInv st T Ac s' ∧ XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧
      SCsOK st T Ω Sg Scs Z Ac s' ∧ SgOK st Ω Sg s' := by
  have hT := h.tcbs
  have hN := h.nodes _ h.cur
  have w : WritesIn st s s' (L.Free s Ω Cs) := ⟨hk, hc, fun b hb _ => hm b hb⟩
  have fa : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K hK hK8 => hm _ (field_aligned (hT y hy) hK hK8)
  have f : Fr st T Sg s s' := by
    refine ⟨hk, hc, fun b hb => hm b (h.omega _ (hSg.sub b hb)).1, fun y hy => by
        rw [scA_eq]; exact fa y hy _ (by simp) (by simp), ?_,
      fun y hy => fa y hy _ (by simp) (by simp), fun y hy => by rw [stA_eq]; exact fa y hy _ (by simp) (by simp),
      fun y hy => fa y hy _ (by simp) (by simp), fun y hy K h1 h2 h3 => fa y hy K (by omega) h3,
      fun c hc' o ho => hm _ (nodeAt_aligned hc' (by omega) (by omega)),
      fun y hy => fa y hy _ (by simp) (by simp)⟩
    unfold LawfulStore.cscW LawfulStore.nodeA LawfulStore.nodeAt
    rw [hk, hc]
    exact hm _ (by
      have := nodeAt_aligned hN (off := layout.node.CUR_SC) (by simp [layout.node.CUR_SC])
        (by simp [layout.node.CUR_SC])
      exact this)
  exact ⟨inv_of_free h w, hB.free h w, hX.fr f, hS.fr f, hSg.fr f⟩

/-- `bind_tcb`'s two writes agree with `donate_pair`'s. -/
theorem bind_swap {s : S} {sc t : U64} (ha : Aligned (scA t)) (hb : Aligned (scTcbA sc))
    (hne : (scA t).val ≠ (scTcbA sc).val) (b : U64) (hb' : Aligned b) :
    L.mem (L.wr (L.wr s (scA t) sc) (scTcbA sc) t) b = L.mem (L.wr (L.wr s (scTcbA sc) t) (scA t) sc) b := by
  rw [L.mem_wr_val hb hb', L.mem_wr_val ha hb', L.mem_wr_val ha hb', L.mem_wr_val hb hb']
  split_ifs with h1 h2 <;> first | rfl | omega

/-- seL4 `schedContext_bindTCB` of an SC bound to no thread and a thread with
no SC.  A thread with no SC is `Sch` only if blocked (on IPC, a notification
or a reply); then the SC must be active (the decode checks that a blocked
thread's SC is released). -/
theorem schedcontext.bind_tcb.blk {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (sc t : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T) (hsc : sc ∈ Scs) (hsc0 : sc ≠ 0#u64)
    (ht0 : L.mem s (scA t) = 0#u64) (hc0 : L.mem s (scTcbA sc) = 0#u64)
    (hbA : BlockedR (L.mem s (stA t)) → sc ∈ Ac) :
    schedcontext.bind_tcb st ar s a sc t ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hT := h0.tcbs
  have hta := hT t ht
  have hO := hX.1
  have hv0 := sc_facts hO hsc
  have hm : scTcbA sc ∈ Ω := hSg.sub _ (hO.fixW sc hsc).1
  have ho := h0.omega _ hm
  -- facts about `t` and `sc` before
  have htq : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 := by
    by_contra hq; exact hB.q t ht hq ht0
  have htr : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
    by_contra hq; exact hB.r t ht hq ht0
  have hna : L.actionW s ≠ t := fun e => hB.act (e ▸ ht) (by rw [e]; exact ht0)
  have hnb : ∀ y ∈ T, L.mem s (scA y) ≠ sc := fun y hy e => by
    obtain ⟨-, h2, -⟩ := hX.2.2.bound y hy (by rw [e]; exact hsc0)
    rw [e, hc0] at h2; exact (hT y hy).ne0 (by rw [← h2]; rfl)
  have hdisj : sc ≠ L.cscW s → ∀ b, InSC sc (Z sc) b → Outside b (L.cscW s) (Z (L.cscW s)) := by
    intro hne b hb
    have := hO.scDisj sc hsc _ hX.2.2.cur hne
    unfold Outside; unfold InSC at hb; omega
  have hcore := hX.2.2.core sc hsc
  have hsA : Sch st s t → sc ∈ Ac := by
    rintro (e | e | e | e | ⟨e1, e2⟩ | e)
    · exact absurd htq e
    · exact absurd htr e
    · exact absurd e hna
    · exact absurd (by rw [e]; exact ht0) hB.idle
    · exact absurd (by rw [e2]; exact ht0) (hB.resume e1)
    · exact hbA e
  -- the two writes
  unfold schedcontext.bind_tcb
  step with obj.Tcb.set_sc.wr as ⟨s1, e1⟩
  step with obj.Sc.set_tcb.wr as ⟨s2, e2⟩
  subst e1 e2
  obtain ⟨p8, pB, pX, pS, pSg, -, pfl, pcore, psc, ptc, pact⟩ :=
    donate_pair h0 hB hX.x0 hX.2.2.tsc.x ht0 hS hSg ht hsc hsc0 hnb hcore hdisj hsA
  have hsw := bind_swap (L := L) (s := s) (scA_aligned hta) ho.1
    (fun e => out_ne_field (K := 3464#u64) ho ht hta (by simp) e)
  obtain ⟨h2, hB2, hX2, hS2, hSg2⟩ := agree_all p8 pB pX pS pSg (by simp) (by simp) hsw
  set s2 := L.wr (L.wr s (scA t) sc) (scTcbA sc) t with hs2
  have fl2 : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (y = t → K.val ≠ 3464) →
      L.mem s2 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K hK hK8 hne => (hsw _ (field_aligned (hT y hy) hK hK8)).trans (pfl y hy K hK hK8 hne)
  have sc2 : L.mem s2 (scA t) = sc := (hsw _ (scA_aligned hta)).trans psc
  have core2 : L.mem s2 (scCoreA sc) = L.mem s (scCoreA sc) :=
    (hsw _ (h0.omega _ ((objs_omega hO hSg.sub).2 sc hsc).2.1).1).trans pcore
  have ea2 : L.actionW s2 = L.actionW s := by
    have e : L.actionW s2 = L.actionW (L.wr (L.wr s (scTcbA sc) t) (scA t) sc) := by
      unfold LawfulStore.actionW
      rw [show L.nodeAt s2 (L.cpu s2) layout.node.SCHED_ACTION =
        L.nodeAt (L.wr (L.wr s (scTcbA sc) t) (scA t) sc) (L.cpu (L.wr (L.wr s (scTcbA sc) t) (scA t) sc))
          layout.node.SCHED_ACTION by simp [hs2, nodeAt_wr]]
      exact hsw _ (nodeAt_aligned (p8.nodes _ p8.cur) (by rw [act_val]; omega) (by rw [act_val]))
    rw [e, pact]
  have iq2 : L.mem s2 (inqA t) = L.mem s (inqA t) := by
    rw [inqA_eq]; exact fl2 t ht _ (by simp) (by simp) (fun _ => by simp)
  -- migration
  step with obj.Sc.cpu.spec as ⟨cpu, ecpu⟩
  have hc' : cpu ∈ Cs := by rw [ecpu, core2]; exact hcore
  refine WP.spec_bind (migrate_tail hA s2 a sc t cpu Q R h2 hB2 hX2 hS2 hSg2 ht (by rw [iq2]; exact htq)
    (by rw [iq2]; exact htr) hc' hsc) ?_
  rintro ⟨s3, a1⟩ ⟨⟨⟨Q3, R3, h3⟩, hB3, hX3, hS3, hSg3⟩, -, -, -, sc3, -, ea3⟩
  try simp only [WP.uncurry'_pair]
  rw [sc2] at sc3
  -- the sporadic unblock check
  step with sporadic.sc_sporadic.spec as ⟨b, eb⟩
  refine WP.spec_bind (Pₘ := fun s4 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s4 ∧ L.mem s4 (scA t) = sc ∧
      L.actionW s4 = L.actionW s) ?_ ?_
  · have ok3 : (ok s3 : Result S) ⦃ s4 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s4 ∧ L.mem s4 (scA t) = sc ∧
        L.actionW s4 = L.actionW s ⦄ :=
      (WP.spec_ok _).2 ⟨⟨⟨Q3, R3, h3⟩, hB3, hX3, hS3, hSg3⟩, sc3, by rw [ea3, ea2]⟩
    split
    · step with sporadic.sc_active.val as ⟨b1, eb1⟩
      split
      · rename_i hb1
        step with sched.cur_sc.spec as ⟨c4, _⟩
        step with sc_ne.spec as ⟨b2⟩
        split
        · refine WP.spec_mono (sporadic.unblock_check.all s3 t sc h3 hB3 hX3 hS3 hSg3 ht sc3.symm hsc0
            ((hS3.act sc hsc).2 (eb1 hb1))) fun s4 hh => ?_
          obtain ⟨h4, hB4, hX4, hS4, hSg4, ea4, -, -, f4, -⟩ := hh
          exact ⟨⟨⟨Q3, R3, h4⟩, hB4, hX4, hS4, hSg4⟩, by rw [scA_eq, f4 t ht _ (by simp) (by simp), ← scA_eq]; exact sc3,
            by rw [ea4, ea3, ea2]⟩
        · exact ok3
      · exact ok3
    · exact ok3
  rintro s4 ⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, sc4, ea4⟩
  -- resume
  have tc4 : L.mem s4 (scTcbA sc) = t := by
    have := (hX4.2.2.bound t ht (by rw [sc4]; exact hsc0)).2.1; rwa [sc4] at this
  refine WP.spec_bind (schedcontext.resume.all hA s4 a1 sc Q4 R4 h4 hB4 hX4 hSg4 hS4 fun _ _ => ?_) ?_
  · rw [tc4]
    exact ⟨ht, h4.omega _ ((objs_omega hX4.1 hSg4.sub).2 sc hsc).2.1, hX4.2.2.core sc hsc,
      by rw [ea4]; exact hna⟩
  rintro ⟨s5, a2⟩ ⟨Q5, R5, h5, hB5, hX5, hSg5, f5⟩
  have hS5 := hS4.fr f5
  try simp only [WP.uncurry'_pair]
  -- enqueue if schedulable
  step with sched.is_schedulable.spec' as ⟨b3, eb3⟩
  split
  · rename_i hb3
    obtain ⟨hrun, hbd, hrl, hrm⟩ := eb3 hb3
    have hA5 : L.mem s5 (scA t) ∈ Ac := (hS5.act _ (hX5.2.2.bound t ht hbd).1).2 hrm
    refine WP.spec_bind (sched.enqueue.sch s5 t Q5 R5 h5 hB5 hSg5 ht (fun _ => hrl) (fun _ => hrun)
      (fun _ => hbd) (fun _ => hA5)) ?_
    rintro s6 ⟨⟨⟨Q6, R6, h6⟩, hB6, f6⟩, -, -, -⟩
    refine WP.spec_bind (sched.reschedule_required.sch s6 Q6 R6 h6 hB6 (hSg5.fr f6)) ?_
    rintro s7 ⟨⟨⟨Q7, R7, h7⟩, hB7, f7⟩, -, -, -⟩
    exact (WP.spec_ok _).2 ⟨⟨Q7, R7, h7⟩, hB7, (hX5.fr f6).fr f7, (hS5.fr f6).fr f7, (hSg5.fr f6).fr f7⟩
  · exact (WP.spec_ok _).2 ⟨⟨Q5, R5, h5⟩, hB5, hX5, hS5, hSg5⟩

end

end Fl4Proofs.P1
