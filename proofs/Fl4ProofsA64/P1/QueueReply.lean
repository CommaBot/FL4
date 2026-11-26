-- AArch64 port of Fl4Proofs.P1.QueueReply (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
/-
P1: the Reply branch of `finalise_cap`: `donate` of an SC from a thread that
may be queued, current or the switch-to candidate (`donate.gen`).

a64: `donate.gen` takes `hrv` (the receiver runs no VCPU; AArch64 `migrate_tcb` in `donate_tail`), carried over
the first half by the field frames (`remote_tcb_stall.all`, `field_qfoot`, `clear_sc_state`,
`reschedule_required.rv0`). No named premises.
-/
import Fl4ProofsA64.P1.QueueBind
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}

/-- `reschedule_required` when the action is to resume the current thread or
is a thread with no SC: it only sets `CHOOSE_NEW`. -/
theorem sched.reschedule_required.unsched (s : S) (t : U64) (hT : TcbPlaced T) (ht : t ∈ T)
    (h0 : L.mem s (scA t) = 0#u64) (ha : L.actionW s = 0#u64 ∨ L.actionW s = t) :
    sched.reschedule_required st s ⦃ s' => s' = L.wr s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) 1#u64 ⦄ := by
  rcases ha with ha | ha
  · exact sched.reschedule_required.resume s ha
  unfold sched.reschedule_required
  step with sched.action.spec as ⟨act, ea⟩
  have e : act = t := by rw [ea]; exact ha
  subst e
  have hta := hT act ht
  split
  · split
    · step with sched.is_schedulable.spec' as ⟨b, eb⟩
      split
      · rename_i hb; exact absurd h0 (eb hb).2.1
      · try simp only [Aeneas.Std.bind_ok]
        rw [choose_val]; exact sched.set_action.spec s _
    · try simp only [Aeneas.Std.bind_ok]
      rw [choose_val]; exact sched.set_action.spec s _
  · try simp only [Aeneas.Std.bind_ok]
    rw [choose_val]; exact sched.set_action.spec s _

/-- seL4 `schedContext_donate` of the SC `sc` of `fr` (not idle; it may be in
a ready or release queue, current, or the switch-to candidate) to `dst`
(unbound, in no queue, not the candidate). -/
theorem schedcontext.donate.gen {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (sc dst fr : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hfr : fr ∈ T) (hscf : L.mem s (scA fr) = sc)
    (hsc0 : sc ≠ 0#u64)
    (hfi : L.idleW s ≠ fr) (hdst : dst ∈ T) (hd0 : L.mem s (scA dst) = 0#u64)
    (hdq : (L.mem s (inqA dst) &&& sched.Q_QUEUED) = 0#u64) (hdr : (L.mem s (inqA dst) &&& sched.Q_RELEASE) = 0#u64)
    (hda : L.actionW s ≠ dst) (hne : dst ≠ fr) (hscA : sc ∈ Ac) (hdi : L.idleW s ≠ dst)
    (hrv : L.mem s (runVcpuA dst) = 0#u64) :  -- a64: the receiver runs no VCPU
    schedcontext.donate st ar s a sc dst ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      (∀ y ∈ T, L.mem s' (stA y) = L.mem s (stA y)) ∧ (∀ y ∈ T, L.mem s' (replyA y) = L.mem s (replyA y)) ∧
      L.mem s' (scA dst) = sc ⦄ := by
  have hT := h.tcbs
  have hfa := hT fr hfr
  obtain ⟨hscS, htcb, hcore⟩ := hX.2.2.bound fr hfr (by rw [hscf]; exact hsc0)
  rw [hscf] at hscS htcb hcore
  have hdisj0 : sc ≠ L.cscW s → ∀ b, InSC sc (Z sc) b → Outside b (L.cscW s) (Z (L.cscW s)) := by
    have := hS.disj fr hfr (by rw [hscf]; exact hsc0); rw [hscf] at this; exact this
  have hnb0 : ∀ y ∈ T, y ≠ fr → L.mem s (scA y) ≠ sc := fun y hy hyf e => by
    obtain ⟨-, h2, -⟩ := hX.2.2.bound y hy (by rw [e]; exact hsc0)
    rw [e, htcb] at h2; exact hyf h2.symm
  have hfixΩ := (hX.1.fixW sc hscS)
  unfold schedcontext.donate
  step with obj.Sc.tcb.spec as ⟨i, ei⟩
  have hi : i = fr := ei.trans htcb
  subst hi
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  have hb : b = false := by
    rw [eb]; simp only [decide_eq_false_iff_not]; exact fun e => hfa.ne0 (by rw [e]; rfl)
  -- the first half, up to the state `s6`
  refine WP.spec_bind (Pₘ := fun r : S × A => ∃ Q6 R6, SchedQueuesInv st T Cs Ω H r.1 Q6 R6 ∧
      BoundInv st T Ac r.1 ∧ XInv0 st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ TScX st Scs sc r.1 ∧
      SCsOK st T Ω Sg Scs Z Ac r.1 ∧ SgOK st Ω Sg r.1 ∧
      (∀ y ∈ T, L.mem r.1 (stA y) = L.mem s (stA y)) ∧ (∀ y ∈ T, L.mem r.1 (replyA y) = L.mem s (replyA y)) ∧
      L.mem r.1 (scA i) = 0#u64 ∧
      (∀ y ∈ T, y ≠ i → L.mem r.1 (scA y) = L.mem s (scA y)) ∧ L.mem r.1 (inqA dst) = L.mem s (inqA dst) ∧
      (∀ b ∈ Sg, L.mem r.1 b = L.mem s b) ∧ L.cscW r.1 = L.cscW s ∧ L.idleW r.1 = L.idleW s ∧
      (∀ y ∈ T, L.mem r.1 (affA y) = L.mem s (affA y)) ∧
      L.mem r.1 (runVcpuA dst) = L.mem s (runVcpuA dst)) ?_ ?_
  rotate_left
  · rintro ⟨s6, a6⟩ ⟨Q6, R6, h6, hB6, hX6, tx6, hS6, hSg6, st6, rp6, sf6, sy6, iq6, sg6, cs6, ei6, af6, rv6⟩
    try simp only [WP.uncurry'_pair]
    have haf6 : ScAff st T s6 := (ScAffX.keep (d := i) (hX.2.2.aff.x i) (fun t ht _ h0 => (hX.2.2.bound t ht h0).1)
      sy6 (fun c hc => sg6 _ (hX.1.fixW c hc).2) (fun t ht _ => af6 t ht)).full (fun _ h0 => absurd sf6 h0)
    refine WP.spec_mono (donate_tail hA s6 a6 sc dst Q6 R6 h6 hB6 hX6 tx6 haf6 (by rw [sy6 dst hdst hne]; exact hd0)
      hS6 hSg6 hdst
      (by rw [iq6]; exact hdq) (by rw [iq6]; exact hdr) hscS hsc0 (fun y hy => ?_)
      (by rw [sg6 _ hfixΩ.2]; exact hcore) (by rw [cs6]; exact hdisj0) (fun _ => hscA)
      (by rw [ei6]; exact hdi) (rv6.trans hrv)) fun r hr => ?_
    · by_cases e : y = i
      · subst e; rw [sf6]; exact Ne.symm hsc0
      · rw [sy6 y hy e]; exact hnb0 y hy e
    · obtain ⟨s', a'⟩ := r
      simp only [WP.uncurry'_pair] at hr ⊢
      exact ⟨hr.1, fun y hy => (hr.2.1 y hy).trans (st6 y hy), fun y hy => (hr.2.2.1 y hy).trans (rp6 y hy),
        hr.2.2.2.2.1⟩
  split
  · rename_i hbt; rw [hb] at hbt; exact absurd hbt (by simp)
  refine WP.spec_bind (smp.remote_tcb_stall.all hA s a i h hB hX hS hSg) ?_
  rintro ⟨s2, a2⟩ ⟨h2, hB2, hX2, hS2, hSg2, ea2, ec2, ei2, ecs2, f2, o2⟩
  try simp only [WP.uncurry'_pair]
  -- dequeue and release-remove `i`
  have hc2 := h2.aff i hfr
  have hp2 := h2.prio i hfr
  refine WP.spec_bind (WP.spec_and (sched.dequeue.sch (Sg := Sg) s2 i Q R h2 hB2 hSg2 hfr)
    (sched.dequeue.foot s2 i _ h2.tcbs hfr hp2 (h2.nodes _ hc2) (h2.nodes _ h2.cur) ((h2.ready _ hc2).1.rel _ hp2)
      (h2.queued i hfr).1)) fun s3 hh3 => ?_
  obtain ⟨⟨⟨⟨Q3, R3, h3⟩, hB3, f3⟩, ea3, ec3⟩, hw3, iq3⟩ := hh3
  have hW2 : ∀ w ∈ Q (L.mem s2 (affA i)) (L.mem s2 (prioA i)), w ∈ T := fun w hw => h2.memT hc2 hp2 hw
  obtain ⟨-, qi3, -, -, ei3⟩ := qfoot_keep (Sg := Sg) h2 hSg2 hW2 hc2 hfr p128 hw3
  have hc3 := h3.aff i hfr
  refine WP.spec_bind (WP.spec_and (sched.release_remove.sch (Sg := Sg) s3 i Q3 R3 h3 hB3 (hSg2.fr f3) hfr)
    (sched.release_remove.foot s3 i _ h3.tcbs hfr (h3.nodes _ hc3) (h3.nodes _ h3.cur) (h3.release _ hc3)
      (h3.released i hfr).1)) fun s4 hh4 => ?_
  obtain ⟨⟨⟨⟨Q4, R4, h4⟩, hB4, f4⟩, ea4, ec4, -⟩, hw4, iq4⟩ := hh4
  have hW3 : ∀ w ∈ R3 (L.mem s3 (affA i)), w ∈ T := fun w hw => h3.memTR hc3 hw
  obtain ⟨-, qi4, -, -, ei4⟩ := qfoot_keep (Sg := Sg) h3 (hSg2.fr f3) hW3 hc3 hfr prel hw4
  have hX4 := (hX2.fr f3).fr f4
  have hS4 := (hS2.fr f3).fr f4
  have hSg4 := (hSg2.fr f3).fr f4
  have iq4' : L.mem s4 (inqA i) = (if (L.mem s3 (inqA i) &&& sched.Q_RELEASE) ≠ 0#u64
      then L.mem s3 (inqA i) &&& ~~~sched.Q_RELEASE else L.mem s3 (inqA i)) := iq4
  have q3 : (L.mem s3 (inqA i) &&& sched.Q_QUEUED) = 0#u64 := by
    rw [iq3]; split_ifs with e
    · exact andn_qq_qq _
    · exact not_not.1 e
  have qq4 : (L.mem s4 (inqA i) &&& sched.Q_QUEUED) = 0#u64 := by
    rw [iq4']; split_ifs
    · rw [andn_qr_qq]; exact q3
    · exact q3
  have qr4 : (L.mem s4 (inqA i) &&& sched.Q_RELEASE) = 0#u64 := by
    rw [iq4']
    split_ifs with e
    · exact andn_qr_qr _
    · exact not_not.1 e
  -- `i`'s SC field
  step with obj.Tcb.set_sc.wr as ⟨s5, e5⟩
  have key := clear_sc_state h4 hB4 hX4 hS4 hSg4 hfr ⟨qq4, qr4⟩ (by rw [ei4, ei3, ei2]; exact hfi)
  rw [← e5] at key
  obtain ⟨k1, kB, kB3, k3, ktx, k4, k5, ka, kc, ki, kcs, kf, kΩ, ks0⟩ := key
  have ktx' : TScX st Scs sc s5 := by
    revert ktx
    rw [f4.sc i hfr, f3.sc i hfr, scA_eq, f2 i hfr _ (by simp) (by simp), ← scA_eq, hscf]; exact id
  have fT : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3464 →
      (K.val = 3328 ∨ K.val = 3360) → L.mem s5 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
    intro y hy K hK hK8 hK' hKs
    rw [kf y hy K hK hK8 (fun _ => hK'), ← f2 y hy K hK hK8]
    rcases hKs with e | e
    · have e' : K = 3328#u64 := by apply UScalar.eq_of_val_eq; simpa using e
      subst e'
      rw [← stA_eq, f4.st y hy, f3.st y hy]
    · have e' : K = 3360#u64 := by apply UScalar.eq_of_val_eq; simpa using e
      subst e'
      exact (f4.rep y hy).trans (f3.rep y hy)
  have sg5 : ∀ b ∈ Sg, L.mem s5 b = L.mem s b := fun b hb =>
    (kΩ b (hSg.sub b hb)).trans ((f4.sig b hb).trans ((f3.sig b hb).trans (o2 b (hSg.sub b hb))))
  have sy5 : ∀ y ∈ T, y ≠ i → L.mem s5 (scA y) = L.mem s (scA y) := fun y hy hyi => by
    rw [scA_eq, kf y hy 3464#u64 (by simp) (by simp) (fun e => absurd e hyi), ← scA_eq, f4.sc y hy, f3.sc y hy,
      scA_eq]; exact f2 y hy _ (by simp) (by simp)
  have st5 : ∀ y ∈ T, L.mem s5 (stA y) = L.mem s (stA y) := fun y hy => by
    rw [stA_eq]; exact fT y hy _ (by simp) (by simp) (by simp) (Or.inl (by simp))
  have rp5 : ∀ y ∈ T, L.mem s5 (replyA y) = L.mem s (replyA y) := fun y hy =>
    fT y hy _ (by simp) (by simp) (by simp) (Or.inr (by simp))
  have iq5 : L.mem s5 (inqA dst) = L.mem s (inqA dst) := by
    rw [inqA_eq, kf dst hdst _ (by simp) (by simp) (fun _ => by simp), ← inqA_eq, qi4 dst hdst hne, qi3 dst hdst hne,
      inqA_eq]; exact f2 dst hdst _ (by simp) (by simp)
  have af5 : ∀ y ∈ T, L.mem s5 (affA y) = L.mem s (affA y) := fun y hy => by
    rw [affA_eq, kf y hy _ (by simp) (by simp) (fun _ => by simp), ← affA_eq, f4.aff y hy, f3.aff y hy, affA_eq]
    exact f2 y hy _ (by simp) (by simp)
  have cs5 : L.cscW s5 = L.cscW s := kcs.trans (f4.csc.trans (f3.csc.trans ecs2))
  have ea5 : L.actionW s5 = L.actionW s := ka.trans (ea4.trans (ea3.trans ea2))
  have rv5 : L.mem s5 (runVcpuA dst) = L.mem s (runVcpuA dst) :=
    (kf dst hdst 3672#u64 (by simp) (by simp) (fun _ => by simp)).trans
      ((field_qfoot h3.tcbs hW3 (h3.nodes _ hc3) (h3.nodes _ h3.cur) hfr hw4 hdst (K := 3672#u64) (by simp) (by simp)
        (by simp) (fun _ => by simp)).trans
      ((field_qfoot h2.tcbs hW2 (h2.nodes _ hc2) (h2.nodes _ h2.cur) hfr hw3 hdst (K := 3672#u64) (by simp) (by simp)
        (by simp) (fun _ => by simp)).trans (f2 dst hdst 3672#u64 (by simp) (by simp))))

  -- `reschedule_required` when the action is to resume or is `i` (no SC now): it only sets `CHOOSE_NEW`
  have R1 : (L.actionW s5 = 0#u64 ∨ L.actionW s5 = i) → sched.reschedule_required st s5 ⦃ s6 =>
      ∃ Q6 R6, SchedQueuesInv st T Cs Ω H s6 Q6 R6 ∧ BoundInv st T Ac s6 ∧ XInv0 st T Cs Ω Sg Rp Scs Nt Z s6 ∧
      TScX st Scs sc s6 ∧ SCsOK st T Ω Sg Scs Z Ac s6 ∧ SgOK st Ω Sg s6 ∧
      (∀ y ∈ T, L.mem s6 (stA y) = L.mem s (stA y)) ∧ (∀ y ∈ T, L.mem s6 (replyA y) = L.mem s (replyA y)) ∧
      L.mem s6 (scA i) = 0#u64 ∧
      (∀ y ∈ T, y ≠ i → L.mem s6 (scA y) = L.mem s (scA y)) ∧ L.mem s6 (inqA dst) = L.mem s (inqA dst) ∧
      (∀ b ∈ Sg, L.mem s6 b = L.mem s b) ∧ L.cscW s6 = L.cscW s ∧ L.idleW s6 = L.idleW s ∧
      (∀ y ∈ T, L.mem s6 (affA y) = L.mem s (affA y)) ∧
      L.mem s6 (runVcpuA dst) = L.mem s (runVcpuA dst) ⦄ := fun ha0 => by
    refine WP.spec_mono (sched.reschedule_required.unsched s5 i k1.tcbs hfr ks0 ha0) fun s6 e6 => ?_
    subst e6
    have f := fr_node (Sg := Sg) (hi8 := fun _ => by simp [layout.node.SCHED_ACTION]) (v := 1#u64) k1 k5 k1.cur
      (by rw [act_val]; omega) (by rw [act_val])
      (hto := ⟨by rw [act_val]; omega, by rw [act_val]; omega⟩)
      (fun _ => by rw [act_val]; omega)
    obtain ⟨j1, -⟩ := inv_set_action k1 (Or.inr (Or.inl rfl)) (fun h1T => absurd h1T (notT_small k1.tcbs (by simp)))
    have fw : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        L.mem (L.wr s5 (L.nodeAt s5 (L.cpu s5) layout.node.SCHED_ACTION) 1#u64) (core.num.U64.wrapping_add y K) =
          L.mem s5 (core.num.U64.wrapping_add y K) := fun y hy K hK hK8 =>
      field_wr_node k1 k1.cur (by rw [act_val]; omega) (by rw [act_val]) hy hK hK8
    refine ⟨Q4, R4, j1, kB3, k3.fr f, ktx'.keep k3.2.2.yt.1
        (fun c hc _ => f.sig _ (k3.1.fixW c hc).1) f.sc, k4.fr f, k5.fr f, fun y hy => ?_,
      fun y hy => (fw y hy _ (by simp) (by simp)).trans (rp5 y hy), ?_, fun y hy hyi => ?_, ?_,
      fun b hb => (f.sig b hb).trans (sg5 b hb), f.csc.trans cs5, f.idle.trans (ki.trans (f4.idle.trans (f3.idle.trans ei2))),
      fun y hy => (fw y hy _ (by simp) (by simp)).trans (af5 y hy), (fw dst hdst 3672#u64 (by simp) (by simp)).trans rv5⟩
    · rw [stA_eq, fw y hy _ (by simp) (by simp), ← stA_eq]; exact st5 y hy
    · rw [scA_eq, fw i hfr _ (by simp) (by simp), ← scA_eq]; exact ks0
    · rw [scA_eq, fw y hy _ (by simp) (by simp), ← scA_eq]; exact sy5 y hy hyi
    · rw [inqA_eq, fw dst hdst _ (by simp) (by simp), ← inqA_eq]; exact iq5
  step with sched.cur_thread.spec as ⟨t1, et1⟩
  step with tcb_eq.blk as ⟨b1, eb1⟩
  split
  · by_cases ha0 : L.actionW s5 = 0#u64 ∨ L.actionW s5 = i
    · exact WP.spec_bind (R1 ha0) fun s6 h6 => (WP.spec_ok _).2 h6
    · push_neg at ha0
      have kB2 := kB (fun e => ha0.2 (by rw [ka, e])) (fun _ => ha0.1)
      have hda5 : L.actionW s5 ≠ dst := by rw [ea5]; exact hda
      refine WP.spec_bind (WP.spec_and (sched.reschedule_required.schX s5 Q4 R4 k1 kB2 k5)
        (sched.reschedule_required.rv0 s5 k1)) fun s6 hh => ?_
      obtain ⟨⟨⟨Q6, R6, h6⟩, hB6, fr6, -, -, kp6, -, iq6⟩, g6⟩ := hh
      refine (WP.spec_ok _).2 ⟨Q6, R6, h6, hB6, k3.fr fr6, ktx'.keep k3.2.2.yt.1
          (fun c hc _ => fr6.sig _ (k3.1.fixW c hc).1) fr6.sc, k4.fr fr6, k5.fr fr6,
        fun y hy => (kp6.1 y hy).trans (st5 y hy), fun y hy => (fr6.rep y hy).trans (rp5 y hy), (fr6.sc i hfr).trans ks0,
        fun y hy hyi => (fr6.sc y hy).trans (sy5 y hy hyi), (iq6 dst hdst hda5).trans iq5,
        fun b hb => (fr6.sig b hb).trans (sg5 b hb), fr6.csc.trans cs5, fr6.idle.trans (ki.trans (f4.idle.trans (f3.idle.trans ei2))),
        fun y hy => (fr6.aff y hy).trans (af5 y hy), (g6 dst hdst).trans rv5⟩
  · rename_i hb1
    have hne' : i ≠ t1 := fun e => hb1 (by rw [eb1, decide_eq_true_eq]; exact e)
    step with sched.action.spec as ⟨i1, ei1⟩
    split
    · rename_i hii
      exact WP.spec_bind (R1 (Or.inr (by rw [← ei1, hii]))) fun s6 h6 => (WP.spec_ok _).2 h6
    · rename_i hii
      have kB2 := kB (fun e => hii (by rw [ei1, ka, e])) (fun e => absurd (by rw [et1]; exact e.symm) hne')
      try simp only [Aeneas.Std.bind_ok]
      refine (WP.spec_ok _).2 ?_
      exact ⟨Q4, R4, k1, kB2, k3, ktx', k4, k5, st5, rp5, ks0, sy5, iq5, sg5, cs5, ki.trans (f4.idle.trans (f3.idle.trans ei2)), af5,
        rv5⟩

end

end Fl4ProofsA64.P1
