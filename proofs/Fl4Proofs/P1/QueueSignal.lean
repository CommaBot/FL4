/-
P1: `send_signal` keeps the IPC invariants, the timer-tree typing and the
notifications' bound-TCB typing (`TInv`).
-/
import Fl4Proofs.P1.QueueTimer
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}

theorem TInv.of_tmfr {s s' : S} (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hb : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s')
    (f : TmFr st T Cs Nt s s') : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' :=
  hb

/-! ## `unblock_sporadic` leaves the timer words alone -/

theorem endpoint.unblock_sporadic.tmfr {X : Set U64} (s : S) (t : obj.Tcb) {Q : U64 → U64 → List U64}
    {R : U64 → List U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T) :
    endpoint.unblock_sporadic st s t ⦃ s' => TmFr st T Cs Nt s s' ⦄ := by
  have hT := h.tcbs
  have hO := hX.1
  unfold endpoint.unblock_sporadic
  step with obj.Tcb.sc.spec as ⟨i, i_post⟩
  step with sporadic.sc_sporadic.spec as ⟨b1, b1_post⟩
  split
  · rename_i hb1
    obtain ⟨hi0, hsp⟩ := b1_post hb1
    have hbt : L.mem s (scA t) ≠ 0#u64 := by rw [← i_post]; exact hi0
    obtain ⟨hiS, -, -⟩ := hX.2.2.bound t ht hbt
    rw [← i_post] at hiS
    have hW : RefillsWF st s i (Z i) := hS.wf hiS (hS.spor i hiS hsp)
    have hSCin : SCin st s Ω i (Z i) := ⟨hW, hX.1.scW i hiS⟩
    step with sched.cur_sc.spec as ⟨c4, _⟩
    step with sc_ne.spec as ⟨b2⟩
    split
    · have hN' := h.nodes _ h.cur
      have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
      have aR : Aligned (L.nodeA s layout.node.REPROGRAM) := nodeAt_aligned hN' (by rw [rp]; omega) (by rw [rp])
      have oR : Outside (L.nodeA s layout.node.REPROGRAM) i (Z i) :=
        hSCin.node_out h.omega h.cur hN' (by rw [rp]; omega) (by rw [rp])
      refine WP.spec_mono (sporadic.unblock_check.fr hW ⟨aR, oR⟩) fun s3 w3 => ?_
      have hΩ : ∀ n ∈ Nt, OutsideObjs st T Cs s (ntfnBtA n) := fun n hn => h.omega _ (hSg.sub _ (hO.ntB n hn).2)
      refine TmFr.of_writes hT h.nodes hO
        (w3.mono' (B := fun b => Aligned b ∧ (InRing i (Z i) b ∨ b = L.nodeA s layout.node.REPROGRAM))
          fun b hb hh => ⟨hb, hh⟩) ?_
      rintro b ⟨hb, hh | hh⟩
      · have hm := hO.scW i hiS b hb hh.inSC
        refine notTmW_omega hT h.nodes (h.omega _ hm) (fun n hn e => ?_)
        rw [ntfnBtA_val (hO.ntP n hn)] at e
        have := hO.ntOSc n hn i hiS; have := hh.1; have := hh.2; omega
      · subst hh
        exact notTmW_node hT h.nodes hΩ h.cur (by rw [rp]; omega) (by rw [rp]; omega)
    · exact (WP.spec_ok _).2 (TmFr.refl (L := L) _)
  · exact (WP.spec_ok _).2 (TmFr.refl (L := L) _)

/-! ## `maybe_donate_sched_context` with the timer frame -/

theorem notification.maybe_donate_sched_context.tinv {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (t n : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T)
    (htq : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64) (htr : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64)
    (hta' : L.actionW s ≠ t) (hti : L.idleW s ≠ t)
    (hns : L.mem s (ntfnScA n) ≠ 0#u64 → L.mem s (scTcbA (L.mem s (ntfnScA n))) = 0#u64 →
      L.mem s (scA t) = 0#u64 → L.mem s (ntfnScA n) ∈ Scs ∧ L.mem s (scCoreA (L.mem s (ntfnScA n))) ∈ Cs ∧
        (Sch st s t → L.mem s (ntfnScA n) ∈ Ac)) :
    notification.maybe_donate_sched_context st ar s a t n ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      TmFr st T Cs Nt s s' ⦄ := by
  have ok0 : (ok (s, a) : Result (S × A)) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ TmFr st T Cs Nt s s' ⦄ :=
    (WP.spec_ok _).2 ⟨⟨⟨Q, R, h⟩, hB, hX, hS, hSg⟩, TmFr.refl (L := L) _⟩
  unfold notification.maybe_donate_sched_context
  step with obj.Tcb.sc.spec as ⟨i, ei⟩
  split
  · rename_i hi
    step with obj.Ntfn.sc.val as ⟨i1, ei1⟩
    step with obj.Sc.is_null.spec as ⟨b, eb⟩
    split
    · exact ok0
    rename_i hb
    have hi10 : i1 ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    step with obj.Sc.tcb.spec as ⟨i2, ei2⟩
    split
    · rename_i hi2
      have htc0 : L.mem s (scTcbA i1) = 0#u64 := by rw [← ei2, hi2]
      obtain ⟨hS1, hcore1, hin1⟩ := hns (by rw [← ei1]; exact hi10) (by rw [← ei1]; exact htc0) (by rw [← ei, hi])
      rw [← ei1] at hS1 hin1 hcore1
      refine WP.spec_bind (schedcontext.donate.unbound hA s a i1 t Q R h hB hX hS hSg ht htq htr hS1 hi10 htc0
        hcore1 hin1 (by rw [← ei, hi]) hti) ?_
      rintro ⟨s4, a4⟩ ⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, -, -, tm4, sc4, tc4, ea4⟩
      try simp only [WP.uncurry'_pair]
      refine WP.spec_mono (schedcontext.resume.all hA s4 a4 i1 Q4 R4 h4 hB4 hX4 hSg4 hS4 fun _ _ => ?_) ?_
      · obtain ⟨-, -, hc4⟩ := hX4.2.2.bound t ht (by rw [sc4]; exact hi10)
        rw [sc4] at hc4
        rw [tc4]
        exact ⟨ht, h4.omega _ ((objs_omega hX4.1 hSg4.sub).2 i1 hS1).2.1, hc4, by rw [ea4]; exact hta'⟩
      · rintro ⟨s5, a5⟩ ⟨Q5, R5, h5, hB5, hX5, hSg5, f5⟩
        exact ⟨⟨⟨Q5, R5, h5⟩, hB5, hX5, hS4.fr f5, hSg5⟩, tm4.trans (TmFr.of_fr f5 hX4.1 h4.nodes)⟩
    · exact ok0
  · exact ok0

/-! ## Waking the signalled thread -/

/-- A notification's SC word holds an SC object, if any. -/
theorem ntfn_sc_ok {Ac : Set U64} {s : S} {n t : U64} (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hn : n ∈ Nt) (hsA : L.mem s (scA t) = 0#u64 → ¬ Sch st s t) :
    L.mem s (ntfnScA n) ≠ 0#u64 → L.mem s (scTcbA (L.mem s (ntfnScA n))) = 0#u64 →
      L.mem s (scA t) = 0#u64 → L.mem s (ntfnScA n) ∈ Scs ∧ L.mem s (scCoreA (L.mem s (ntfnScA n))) ∈ Cs ∧
        (Sch st s t → L.mem s (ntfnScA n) ∈ Ac) := fun h0 _ h3 => by
  obtain ⟨hc, -⟩ := hX.2.2.nsc n hn h0
  exact ⟨hc, hX.2.2.core _ hc, fun hS => absurd hS (hsA h3)⟩

/-- The end of `send_signal` on a woken thread `dst` (running, in no ready or
release queue, not the switch-to candidate): the badge, the SC donation, the
possible switch and the sporadic unblock. -/
theorem signal_tail {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s2 : S) (a1 : A) (dst n badge : U64)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h2 : SchedQueuesInv st T Cs Ω H s2 Q R) (hB2 : BoundInv st T Ac s2) (hX2 : XInv st T Cs Ω Sg Rp Scs Nt Z s2)
    (hS2 : SCsOK st T Ω Sg Scs Z Ac s2) (hSg2 : SgOK st Ω Sg s2) (hd : dst ∈ T) (hn : n ∈ Nt)
    (dq : (L.mem s2 (inqA dst) &&& sched.Q_QUEUED) = 0#u64) (dr : (L.mem s2 (inqA dst) &&& sched.Q_RELEASE) = 0#u64)
    (da : L.actionW s2 ≠ dst) (di : L.idleW s2 ≠ dst) (dR : ¬ BlockedR (L.mem s2 (stA dst))) :
    (do
      let s3 ← obj.Tcb.set_reg st dst s2 layout.reg.BADGE badge
      let (s4, a2) ← notification.maybe_donate_sched_context st ar s3 a1 dst n
      let b1 ← sched.is_schedulable st s4 dst
      let s5 ← if b1 then sched.possible_switch_to st s4 dst else ok s4
      let s6 ← notification.unblock_sporadic st s5 dst
      ok (s6, a2)) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ TmFr st T Cs Nt s2 s' ⦄ := by
  have hT := h2.tcbs
  have hta := hT dst hd
  refine WP.spec_bind (obj.Tcb.set_reg.badge s2 dst badge hta) fun s3 e3 => ?_
  subst e3
  obtain ⟨h3, hB3, hX3, hS3, hSg3⟩ := badge_all (v := badge) h2 hB2 hX2 hS2 hSg2 hd
  have tm3 : TmFr st T Cs Nt s2 (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) :=
    TmFr.wr hT h2.nodes hX2.1 (field_aligned hta (by simp) (by simp))
      (notTmW_field hT h2.nodes (fun n hn => h2.omega _ (hSg2.sub _ (hX2.1.ntB n hn).2)) hd (by simp) (by simp))
  have iq3 : L.mem (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) (inqA dst) = L.mem s2 (inqA dst) := by
    rw [inqA_eq]
    exact L.mem_wr_ne (field_aligned hta (by simp) (by simp)) (field_aligned hta (by simp) (by simp))
      (fun e => field_ne (K1 := 256#u64) (K2 := 3592#u64) hta hta (by simp) (by simp) (fun _ => by simp)
        (UScalar.eq_of_val_eq e))
  have ea3 : L.actionW (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) = L.actionW s2 :=
    act_wr_field (h2.nodes _ h2.cur) hd hta rfl (by simp) (by simp)
  have ei3 : L.idleW (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) = L.idleW s2 := by
    unfold LawfulStore.idleW; rw [LawfulStore.cpu_wr, nodeAt_wr]
    exact L.mem_wr_ne (field_aligned hta (by simp) (by simp))
      (nodeAt_aligned (h2.nodes _ h2.cur) (by rw [idle8]; omega) (by rw [idle8]))
      (fun e => node_ne_field (K := 256#u64) (h2.nodes _ h2.cur) (by rw [idle8]; omega) hd hta (by simp)
        (UScalar.eq_of_val_eq e).symm)
  have sc3 : L.mem (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) (scA dst) = L.mem s2 (scA dst) := by
    rw [scA_eq]
    exact L.mem_wr_ne (field_aligned hta (by simp) (by simp)) (field_aligned hta (by simp) (by simp))
      (fun e => field_ne (K1 := 256#u64) (K2 := 3464#u64) hta hta (by simp) (by simp) (fun _ => by simp)
        (UScalar.eq_of_val_eq e))
  have hsA3 : L.mem (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) (scA dst) = 0#u64 →
      ¬ Sch st (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) dst := fun h0 hS => by
    rw [sc3] at h0
    rcases Sch.wr_field h2 hd (by simp) (by simp) (by simp) hd hS with e | e | e | e | ⟨e1, e2⟩ | e
    · exact e dq
    · exact e dr
    · exact da e
    · exact di e
    · exact hB2.resume e1 (by rw [e2]; exact h0)
    · exact dR e
  refine WP.spec_bind (notification.maybe_donate_sched_context.tinv hA _ a1 dst n Q R h3 hB3 hX3 hS3 hSg3 hd
    (by rw [iq3]; exact dq) (by rw [iq3]; exact dr) (by rw [ea3]; exact da) (by rw [ei3]; exact di)
    (ntfn_sc_ok hX3 hn hsA3)) ?_
  rintro ⟨s4, a2⟩ ⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, tm4⟩
  try simp only [WP.uncurry'_pair]
  step with sched.is_schedulable.spec' as ⟨b1, hb1⟩
  refine WP.spec_bind (Pₘ := fun s5 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s5 ∧ TmFr st T Cs Nt s4 s5) ?_ ?_
  · split
    · rename_i hb
      refine WP.spec_mono (sched.possible_switch_to.sch s4 dst Q4 R4 h4 hB4 hSg4 hd (hb1 hb).1
        (fun _ => (hS4.act _ (hX4.2.2.bound dst hd (hb1 hb).2.1).1).2 (hb1 hb).2.2.2)) fun s5 hh => ?_
      obtain ⟨p5, -, -⟩ := hh
      exact ⟨⟨p5.inv, p5.bnd, hX4.fr p5.fr, hS4.fr p5.fr, hSg4.fr p5.fr⟩, TmFr.of_fr p5.fr hX4.1 h4.nodes⟩
    · exact (WP.spec_ok _).2 ⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, TmFr.refl (L := L) _⟩
  rintro s5 ⟨⟨⟨Q5, R5, h5⟩, hB5, hX5, hS5, hSg5⟩, tm5⟩
  refine WP.spec_bind (WP.spec_and (endpoint.unblock_sporadic.all s5 dst h5 hB5 hX5 hS5 hSg5 hd)
    (endpoint.unblock_sporadic.tmfr s5 dst h5 hX5 hS5 hSg5 hd)) ?_
  rintro s6 ⟨⟨h6, hB6, hX6, hS6, hSg6, -⟩, tm6⟩
  exact (WP.spec_ok _).2 ⟨⟨⟨Q5, R5, h6⟩, hB6, hX6, hS6, hSg6⟩, tm3.trans (tm4.trans (tm5.trans tm6))⟩

/-! ## Notification words -/

theorem obj.Ntfn.bound_tcb.val (s : S) (n : obj.Ntfn) : obj.Ntfn.bound_tcb st n s ⦃ v => v = L.mem s (ntfnBtA n) ⦄ := by
  unfold obj.Ntfn.bound_tcb; step*; simp_all [ntfnBtA]
theorem obj.Ntfn.badge.val (s : S) (n : obj.Ntfn) : obj.Ntfn.badge st n s ⦃ v => v = L.mem s (ntfnBdA n) ⦄ := by
  unfold obj.Ntfn.badge; step*; simp_all [ntfnBdA]
theorem obj.Ntfn.set_badge.wr (s : S) (n : obj.Ntfn) (v : U64) :
    obj.Ntfn.set_badge st n s v ⦃ s' => s' = L.wr s (ntfnBdA n) v ⦄ := by
  unfold obj.Ntfn.set_badge; step*; simp_all [ntfnBdA]

/-- A write of a notification's badge word. -/
theorem ntfn_badge_all {s : S} {n v : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hn : n ∈ Nt) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s (ntfnBdA n) v) ∧ TmFr st T Cs Nt s (L.wr s (ntfnBdA n) v) := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hO := hX.1
  have hP := hO.ntP n hn
  have av := ntfnBdA_val hP
  have hm : ntfnBdA n ∈ Ω := hSg.sub _ (hO.ntB n hn).1
  obtain ⟨h1, hB1, hX1, hS1, hSg1, -⟩ := link_all (w := v) h0 hB hX hS hSg hm
    (fun r hr => by rw [av, (rp_facts hO hr).2.1]; have := hO.ntORp n hn r hr; omega)
    (fun c hc => by
      obtain ⟨h128, e1, e2, e3, e4, e5, -⟩ := sc_facts hO hc
      rw [av, e1, e2, e3, e4, e5]; have := hO.ntOSc n hn c hc; omega)
    (fun r hr e => by rw [av, (rp_facts hO hr).2.2.2] at e; have := hO.ntORp n hn r hr; omega)
    (fun r hr e => by rw [av, (rp_facts hO hr).2.2.1] at e; have := hO.ntORp n hn r hr; omega)
    (fun c hc e => by
      rw [av, (sc_facts hO hc).2.2.2.2.2.2.1] at e; have := hO.ntOSc n hn c hc; have := (sc_facts hO hc).1; omega)
    (fun n' hn' e => by
      rw [av, ntfnScA_val (hO.ntP n' hn')] at e; have := hP.1; have := (hO.ntP n' hn').1; omega)
    (fun n' hn' e => by
      rw [av, ntfnBtA_val (hO.ntP n' hn')] at e; have := hP.1; have := (hO.ntP n' hn').1; omega)
    (fun c hc e => by
      obtain ⟨hPc, hzc⟩ := hO.sc c hc
      rw [av, scNtfnA_val hPc hzc] at e; have := hO.ntOSc n hn c hc; have := (sc_facts hO hc).1; omega)
    (fun c hc e => by
      rw [av, show scYieldFromA c = core.num.U64.wrapping_add c layout.sc.YIELD_FROM from rfl,
        (sc_facts hO hc).2.2.2.2.2.2.2] at e; have := hO.ntOSc n hn c hc; have := (sc_facts hO hc).1; omega)
    (fun c hc => by
      obtain ⟨hPc, hzc⟩ := hO.sc c hc
      rw [av, sporA_val hPc hzc]; have := hO.ntOSc n hn c hc; have := (sc_facts hO hc).1; omega)
    (fun r hr e _ _ => absurd e (by rw [av, (rp_facts hO hr).2.2.2]; have := hO.ntORp n hn r hr; omega))
    (fun c hc e => absurd e (by
      rw [av, (sc_facts hO hc).2.2.2.2.2.2.1]; have := hO.ntOSc n hn c hc; have := (sc_facts hO hc).1; omega))
  refine ⟨⟨⟨Q, R, h1⟩, hB1, hX1, hS1, hSg1⟩, TmFr.wr h0.tcbs h0.nodes hO (h0.omega _ hm).1
    (notTmW_omega h0.tcbs h0.nodes (h0.omega _ hm) (fun n' hn' e => ?_))⟩
  rw [av, ntfnBtA_val (hO.ntP n' hn')] at e
  have := hP.1; have := (hO.ntP n' hn').1; omega

theorem ntfn_state_all {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {n : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hn : H n = some .ntfn) (hact : L.epState s n ≠ 1#u64) {w : U64}
    (hw : w &&& 3#u64 = 0#u64 ∨ w &&& 3#u64 = 2#u64) :
    SchedQueuesInvX st T Cs Ω H X
        (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (w &&& 3#u64))) Q R ∧
      BoundInv st T Ac (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (w &&& 3#u64))) ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (w &&& 3#u64))) ∧
      SCsOK st T Ω Sg Scs Z Ac (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (w &&& 3#u64))) ∧
      SgOK st Ω Sg (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (w &&& 3#u64))) ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
        L.mem (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (w &&& 3#u64)))
          (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ a ∈ Ω, L.mem (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (w &&& 3#u64))) a =
        L.mem s a) ∧
      L.actionW (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (w &&& 3#u64))) = L.actionW s ∧
      L.idleW (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (w &&& 3#u64))) = L.idleW s ∧
      L.epState (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (w &&& 3#u64))) n = w &&& 3#u64 ∧
      TmFr st T Cs Nt s (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (w &&& 3#u64))) := by
  obtain ⟨E, EQ, hEW⟩ := h.eps
  have he : n ∈ E := (hEW.2.2.2.2.2.2.2.1 n).2 (Or.inr hn)
  obtain ⟨hE, -, hq⟩ := hEW.1 n he
  obtain ⟨k1, k2, -, -, k4, -⟩ := hEW.2.2.2.2.2
  have h0 : EQ n = [] := by
    by_contra hne
    obtain ⟨y, ys, hys⟩ := List.exists_cons_of_ne_nil hne
    have hy : y ∈ EQ n := by rw [hys]; exact List.mem_cons_self
    obtain ⟨hyX, hbe, hbl⟩ := hEW.2.2.2.1 n he y hy
    have hyT := hq.mem y hy
    obtain ⟨-, -, c3⟩ := k4 n he y hy
    rcases hbl with hb | hb | hb
    · have := k1 y hyT hyX (Or.inl hb); rw [hbe, hn] at this; cases this
    · have := k1 y hyT hyX (Or.inr hb); rw [hbe, hn] at this; cases this
    · exact hact (c3 hb)
  obtain ⟨a1, a2⟩ := ep_aligned hE
  set v := (L.mem s (epTSA n) &&& ~~~3#u64) ||| (w &&& 3#u64) with hv0
  have hwr : WritesIn st s (L.wr s (epTSA n) v) (EpFoot (EQ n) n) :=
    (writesIn_wr a2).mono fun b hb => Or.inr (Or.inr hb)
  have hhd : L.mem (L.wr s (epTSA n) v) (epHeadA n) = L.mem s (epHeadA n) :=
    L.mem_wr_ne a2 a1 (by rw [epTSA_val hE, epHeadA_val]; omega)
  have hq_eq : L.epQ (L.wr s (epTSA n) v) n = L.epQ s n := by
    simp only [LawfulStore.epQ, hhd]; rw [L.mem_wr_same a2, hv0, ts_end]
  have hst' : L.epState (L.wr s (epTSA n) v) n = w &&& 3#u64 := by
    simp only [LawfulStore.epState]; rw [L.mem_wr_same a2, hv0, ts_state]
  have hq' : QueueRel (L.mem (L.wr s (epTSA n) v)) T .Ep (L.epQ (L.wr s (epTSA n) v) n) [] := by
    rw [hq_eq]; rw [h0] at hq
    exact ⟨hq.nodup, hq.mem, hq.head, hq.last, by simp⟩
  have hinv := inv_ep_step (X' := X) h hEW he hwr hq' (fun hne => absurd rfl hne)
    (fun _ => ⟨fun hep => absurd (hn.symm.trans hep) (by simp), fun _ => by rw [hst']; rcases hw with e | e <;> rw [e] <;> decide⟩) (fun y hy => absurd hy (by simp))
    (fun y hy => absurd hy (by rw [h0]; simp)) (fun y hy => hy) (fun y hy => Or.inl hy)
    (fun y hy => absurd hy (by simp))
  have hWT : ∀ y ∈ EQ n, y ∈ T := fun y hy => absurd hy (by rw [h0]; simp)
  obtain ⟨kf, kΩ, kn⟩ := epfoot_keep h hEW he hWT hwr
  have knc := epfoot_nodes h hEW he hWT hwr
  obtain ⟨b1, b2, b3, b4, ea, -, ei⟩ := frame_bx h hB hX hS hSg kf kΩ (fun o h1 h2 => kn o h1 h2) hwr.1
    (TmFr.mk0 ⟨hwr.1, fun y hy K h1 h2 h3 => kf y hy K (by omega) h3 (by omega) (by omega),
      fun c hc o ho => knc c hc o (by omega) (by omega), fun n' hn' => kΩ _ (hSg.sub _ (hX.1.ntB n' hn').2)⟩)
  refine ⟨hinv, b1, b2, b3, b4, kf, kΩ, ea, ei, hst', TmFr.mk0 ⟨hwr.1,
    fun y hy K h1 h2 h3 => kf y hy K (by omega) h3 (by omega) (by omega),
    fun c hc o ho => knc c hc o (by omega) (by omega), fun n' hn' => kΩ _ (hSg.sub _ (hX.1.ntB n' hn').2)⟩⟩


/-! ## `send_signal` -/

/-- The head of a waiting notification's queue: a TCB blocked on it. -/
theorem ntfn_head {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {n : U64}
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hH : H n = some .ntfn) (hst : L.epState s n = 1#u64) :
    (L.epQ s n).head ∈ T ∧ L.mem s (blockA (L.epQ s n).head) = n ∧
      L.mem s (stA (L.epQ s n).head) = sched.TS_BLOCKED_ON_NTFN := by
  obtain ⟨E, EQ, hEW⟩ := h.eps
  have he : n ∈ E := (hEW.2.2.2.2.2.2.2.1 n).2 (Or.inr hH)
  obtain ⟨hE, -, hq⟩ := hEW.1 n he
  obtain ⟨k1, k2, -, -, k4, k5⟩ := hEW.2.2.2.2.2
  have hne : EQ n ≠ [] := fun h0 => (k5 n he h0).2 hH hst
  obtain ⟨y, ys, hys⟩ := List.exists_cons_of_ne_nil hne
  have hhd : (L.epQ s n).head = y := by rw [hq.head, hys]; rfl
  have hy : y ∈ EQ n := by rw [hys]; exact List.mem_cons_self
  obtain ⟨-, hbe, hbl⟩ := hEW.2.2.2.1 n he y hy
  have hyT := hq.mem y hy
  rw [hhd]
  refine ⟨hyT, hbe, ?_⟩
  rcases hbl with hb | hb | hb
  · have := k1 y hyT (by simp) (Or.inl hb); rw [hbe, hH] at this; cases this
  · have := k1 y hyT (by simp) (Or.inr hb); rw [hbe, hH] at this; cases this
  · exact hb

theorem ntfn_active_and : obj.NTFN_ACTIVE &&& 3#u64 = 2#u64 := by unfold obj.NTFN_ACTIVE; decide

/-- `set_active` on a notification that is not waiting. -/
theorem notification.set_active.tinv (s : S) (n badge : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hn : n ∈ Nt) (hH : H n = some .ntfn) (hst : L.epState s n ≠ 1#u64) :
    notification.set_active st s n badge ⦃ s' => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  have hI := h
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  unfold notification.set_active
  refine WP.spec_bind (obj.Ntfn.set_state.val s n _) fun s1 e1 => ?_
  subst e1
  obtain ⟨h1, hB1, hX1, hS1, hSg1, -, -, -, -, -, tm1⟩ :=
    ntfn_state_all (w := obj.NTFN_ACTIVE) h0 hB hX hS hSg hH hst (Or.inr ntfn_active_and)
  refine WP.spec_mono (obj.Ntfn.set_badge.wr _ n badge) fun s2 e2 => ?_
  subst e2
  obtain ⟨b2, tm2⟩ := ntfn_badge_all (v := badge) (⟨⟨Q, R, h1⟩, hB1, hX1, hS1, hSg1⟩ : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac _) hn
  exact hI.of_tmfr b2 (tm1.trans tm2)

/-! ## #63: the same-core `RunningVM` completion -/

/-- An `if` in a triple, branch by branch (P0's `p0_if`), without `split`
(which exceeds `simp`'s step limit on #63's `send_signal`). -/
theorem sig_if {α : Type _} (c : Prop) [Decidable c] (x y : Result α) (P : α → Prop)
    (hx : c → x ⦃ P ⦄) (hy : ¬ c → y ⦃ P ⦄) : (if c then x else y) ⦃ P ⦄ := by
  by_cases h : c
  · rw [if_pos h]; exact hx h
  · rw [if_neg h]; exact hy h

theorem not_blocked_vm : ¬ Blocked sched.TS_RUNNING_VM := fun hb => blocked_not_runnable hb (Or.inr (Or.inr rfl))

/-- A TCB register write is one word write (as `obj.Tcb.set_reg.wrK`, QueueFinal). -/
theorem obj.Tcb.set_reg.wrS (s : S) (t : obj.Tcb) (r v : U64) (ht : TcbAddr t) (hr : r.val < 384) :
    obj.Tcb.set_reg st t s r v ⦃ s' => ∃ K : U64, K.val = 256 + 8 * r.val ∧
      s' = L.wr s (core.num.U64.wrapping_add t K) v ⦄ := by
  unfold obj.Tcb.set_reg
  step*
  subst_vars
  have := ht.fits
  have hK : (core.num.U64.wrapping_add 256#u64 (core.num.U64.wrapping_mul r 8#u64)).val = 256 + 8 * r.val := by
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]; omega
  refine ⟨core.num.U64.wrapping_add 256#u64 (core.num.U64.wrapping_mul r 8#u64), hK, ?_⟩
  congr 1
  apply UScalar.eq_of_val_eq
  simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits,
    layout.tcb.REGS] at hK ⊢
  omega

/-- A write of a TCB register word (below `STATE`) keeps the invariants and
the thread's state word. -/
theorem reg_all {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t K v : U64}
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T) (hK : 256 ≤ K.val ∧ K.val < 3328)
    (hK8 : K.val % 8 = 0) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s (core.num.U64.wrapping_add t K) v) ∧
      L.mem (L.wr s (core.num.U64.wrapping_add t K) v) (stA t) = L.mem s (stA t) := by
  have hT := h.tcbs
  have hta := hT t ht
  obtain ⟨b1, b2⟩ := bx_field (K := K) (v := v) h hB hX hSg.sub ht (by omega) hK8
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega) (Or.inl (by omega))
  refine ⟨⟨⟨Q, R, inv_wr_field h ht (by omega) hK8 (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega)⟩, b1, b2,
    SCsOK.field h hS hX ht (by omega) hK8 (by omega),
    ⟨hSg.sub, fun b hb => by rw [L.ksb_wr]; exact hSg.ks b hb, fun o h1 h2 => by rw [L.ksb_wr]; exact hSg.ksΩ o h1 h2⟩⟩, ?_⟩
  rw [stA_eq]
  exact L.mem_wr_ne (field_aligned hta (by omega) hK8) (field_aligned hta (by simp) (by simp))
    (fun e => field_ne (K1 := K) (K2 := 3328#u64) hta hta (by omega) (by simp) (fun _ => by first | omega | (simp; omega) | simp)
      (UScalar.eq_of_val_eq e))

/-- A register write of a TCB keeps the invariants and its state word. -/
theorem obj.Tcb.set_reg.blk (s : S) {t r v : U64} (hr : r.val < 384) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ht : t ∈ T) :
    obj.Tcb.set_reg st t s r v ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ L.mem s' (stA t) = L.mem s (stA t) ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  refine WP.spec_mono (obj.Tcb.set_reg.wrS s t r v (h0.tcbs t ht) hr) ?_
  rintro s1 ⟨K, hK, rfl⟩
  exact reg_all h0 hB hX hS hSg ht (by omega) (by omega)

/-- `set_mr` of one of the first three message registers (registers on x86_64). -/
theorem msg.set_mr.blk (s : S) {t buf i v : U64} (hi : i.val < 3) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ht : t ∈ T) :
    msg.set_mr st s t buf i v ⦃ r => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2 ∧ L.mem r.2 (stA t) = L.mem s (stA t) ⦄ := by
  unfold msg.set_mr
  have hlt : i < msg.N_MSG_REGISTERS := by simp only [msg.N_MSG_REGISTERS]; scalar_tac
  rw [if_pos hlt]
  refine WP.spec_bind (Pₘ := fun r => r.val < 384) ?_ fun r hr => ?_
  · unfold msg.msg_register
    split
    · exact (WP.spec_ok _).2 (by simp [layout.reg.R10])
    split
    · exact (WP.spec_ok _).2 (by simp [layout.reg.R8])
    split
    · exact (WP.spec_ok _).2 (by simp [layout.reg.R9])
    · exact (WP.spec_ok _).2 (by simp [layout.reg.R15])
  refine WP.spec_bind (obj.Tcb.set_reg.blk s hr h ht) fun s1 h1 => ?_
  simp only [lift, bind_ok]
  exact (WP.spec_ok _).2 h1

set_option maxHeartbeats 4000000 in
/-- **#63's `vcpu.report` without a saved exit** (`signal_completes`: the
thread has a VCPU with `PENDING = 0`): MR0..2 (registers R10/R8/R9) get the
entry state, then the message info, the badge and `TS_RUNNING`; no IPC-buffer
word is written. -/
theorem vcpu.report.blk {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (t badge : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T) (hvm : L.mem s (stA t) = sched.TS_RUNNING_VM)
    (hc : L.mem s (core.num.U64.wrapping_add t 3664#u64) ≠ 0#u64 →
      L.mem s (core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add t 3664#u64)) vcpu.PENDING) = 0#u64) :
    vcpu.report st ar s a t badge ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      L.mem s' (stA t) = sched.TS_RUNNING ⦄ := by
  have hS0 : P0.StoreTotal st := L.total
  unfold vcpu.report vcpu.bound
  step as ⟨o, ho⟩
  simp only [lift, bind_ok]
  refine WP.spec_bind (LawfulStore.read_spec s _) fun v ev => ?_
  subst ho
  refine WP.spec_bind (Pₘ := fun p => p = false) ?_ fun pending hp => ?_
  · split
    · rename_i hv
      unfold vcpu.get
      simp only [lift, bind_ok]
      refine WP.spec_bind (LawfulStore.read_spec s _) fun i ei => ?_
      have hv0 : v ≠ 0#u64 := by simpa using hv
      have : i = 0#u64 := by rw [ei, ev]; exact hc (by rw [← ev]; exact hv0)
      exact (WP.spec_ok _).2 (by simp [this])
    · exact (WP.spec_ok _).2 rfl
  subst hp
  refine WP.spec_bind (Fl4Proofs.P0.msg.lookup_ipc_buffer.p0 st s true t hS0) fun b _ => ?_
  rw [if_neg Bool.false_ne_true]
  refine WP.spec_bind (hA.virtualization a) fun i _ => ?_
  refine WP.spec_bind (Pₘ := fun _ => True) ?_ ?_
  · repeat' (first
      | exact (WP.spec_ok _).2 trivial
      | exact Fl4Proofs.P0.vcpu.get.p0 _ _ _ _ hS0
      | exact Fl4Proofs.P0.vcpu.read_vmcs.p0 _ _ _ _ hS0
      | split
      | (step as ⟨_, _⟩)
      | refine WP.spec_bind (Fl4Proofs.P0.vcpu.get.p0 _ _ _ _ hS0) fun _ _ => ?_
      | refine WP.spec_bind (Fl4Proofs.P0.vcpu.read_vmcs.p0 _ _ _ _ hS0) fun _ _ => ?_)
  rintro ⟨ip, ctl, intr⟩ -
  try dsimp only
  refine WP.spec_bind (msg.set_mr.blk s (by simp) h ht) ?_
  rintro ⟨_, s1⟩ ⟨h1, e1⟩
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (msg.set_mr.blk s1 (by simp) h1 ht) ?_
  rintro ⟨_, s2⟩ ⟨h2, e2⟩
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (msg.set_mr.blk s2 (by simp) h2 ht) ?_
  rintro ⟨_, s3⟩ ⟨h3, e3⟩
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (obj.Tcb.set_reg.blk s3 (by simp [layout.reg.MSG_INFO, layout.reg.RSI]) h3 ht) fun s4 ⟨h4, e4⟩ => ?_
  refine WP.spec_bind (obj.Tcb.set_reg.blk s4 (by simp [layout.reg.BADGE, layout.reg.RDI]) h4 ht) fun s5 ⟨h5, e5⟩ => ?_
  obtain ⟨⟨Q5, R5, q5⟩, hB5, hX5, hS5, hSg5⟩ := h5
  have st5 : L.mem s5 (stA t) = sched.TS_RUNNING_VM := by rw [e5, e4, e3, e2, e1, hvm]
  refine WP.spec_mono (sts_all s5 t _ Q5 R5 q5 hB5 hX5 hS5 hSg5 ht not_blocked_running running_ne
    (Or.inr (by rw [st5]; exact not_blocked_vm))
    (hX5.noref (q5.tcbs t ht) (by rw [st5]; exact runnable_ne_reply (Or.inr (Or.inr rfl)))
      (by rw [st5]; exact runnable_ne_recv (Or.inr (Or.inr rfl))))
    ⟨fun _ _ _ _ _ => runnable_running, fun _ _ _ => runnable_running, fun _ => runnable_running⟩) ?_
  rintro s6 ⟨q6, hB6, hX6, hS6, hSg6, st6, -⟩
  exact ⟨⟨⟨Q5, R5, q6.congrX empty_congr⟩, hB6, hX6, hS6, hSg6⟩, st6⟩

/-- `maybe_donate_sched_context` on a thread that may be queued: it does
nothing unless the thread has no SC, and then `BoundInv` keeps it out of the
queues and off the switch-to candidate and the idle thread. -/
theorem notification.maybe_donate_sched_context.tinvB {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (t n : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T)
    (hns : L.mem s (ntfnScA n) ≠ 0#u64 → L.mem s (scTcbA (L.mem s (ntfnScA n))) = 0#u64 →
      L.mem s (scA t) = 0#u64 → L.mem s (ntfnScA n) ∈ Scs ∧ L.mem s (scCoreA (L.mem s (ntfnScA n))) ∈ Cs ∧
        (Sch st s t → L.mem s (ntfnScA n) ∈ Ac)) :
    notification.maybe_donate_sched_context st ar s a t n ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      TmFr st T Cs Nt s s' ⦄ := by
  by_cases h0 : L.mem s (scA t) = 0#u64
  · refine notification.maybe_donate_sched_context.tinv hA s a t n Q R h hB hX hS hSg ht ?_ ?_ ?_ ?_ hns
    · by_contra hq; exact hB.q t ht hq h0
    · by_contra hq; exact hB.r t ht hq h0
    · intro e; exact hB.act (by rw [e]; exact ht) (by rw [e]; exact h0)
    · intro e; exact hB.idle (by rw [e]; exact h0)
  · unfold notification.maybe_donate_sched_context
    step with obj.Tcb.sc.spec as ⟨i, ei⟩
    rw [if_neg (by rw [ei]; exact h0)]
    exact (WP.spec_ok _).2 ⟨⟨⟨Q, R, h⟩, hB, hX, hS, hSg⟩, TmFr.refl (L := L) _⟩

/-- `vcpu.signal_completes`: a VCPU without a pending exit. -/
theorem vcpu.signal_completes.blk (s : S) (t : U64) :
    vcpu.signal_completes st s t ⦃ b => b = true →
      (L.mem s (core.num.U64.wrapping_add t 3664#u64) ≠ 0#u64 →
        L.mem s (core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add t 3664#u64)) vcpu.PENDING) = 0#u64) ⦄ := by
  have hS0 : P0.StoreTotal st := L.total
  unfold vcpu.signal_completes vcpu.bound
  step as ⟨o, ho⟩
  simp only [lift, bind_ok]
  refine WP.spec_bind (LawfulStore.read_spec s _) fun v ev => ?_
  subst ho
  split
  · unfold vcpu.get
    simp only [lift, bind_ok]
    refine WP.spec_bind (LawfulStore.read_spec s _) fun i ei => ?_
    refine (WP.spec_ok _).2 fun hb _ => ?_
    rw [← ev, ← ei]; simpa using hb
  · exact (WP.spec_ok _).2 fun hb => absurd hb (by simp)

/-- **#63's same-core `RunningVM` branch of `send_signal`**: the thread's
VMEnter completes (`vcpu.report.blk`), then the SC donation, the possible
switch and the sporadic unblock, as for a woken receiver. -/
theorem signal_vm {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s1 : S) (a : A) (i n : U64)
    (h1 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1) (hiT : i ∈ T) (hn : n ∈ Nt)
    (st1 : L.mem s1 (stA i) = sched.TS_RUNNING) :
    (do
      let (s2, a1) ← notification.maybe_donate_sched_context st ar s1 a i n
      let b2 ← sched.is_schedulable st s2 i
      let s3 ← if b2 = true then sched.possible_switch_to st s2 i else ok s2
      let i4 ← obj.Tcb.sc st i s3
      let b3 ← obj.Sc.is_null i4
      if b3 = true then ok (s3, a1)
      else do
        let b4 ← sporadic.sc_active st s3 i4
        if b4 = true then do
          let i5 ← obj.Ntfn.sc st n s3
          if i4 = i5 then do
            let b5 ← sporadic.sc_sporadic st s3 i4
            if b5 = true then do
              let s4 ← sched.cur_sc st s3
              let b6 ← core.cmp.PartialEq.ne.trait_default obj.Sc.Insts.CoreCmpPartialEqSc i4 s4
              if b6 = true then do
                let s5 ← sporadic.unblock_check st s3 i4
                ok (s5, a1)
              else ok (s3, a1)
            else ok (s3, a1)
          else ok (s3, a1)
        else ok (s3, a1)) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  obtain ⟨⟨Q1, R1, q1⟩, hB1, hX1, hS1, hSg1⟩ := h1
  have hsA1 : L.mem s1 (scA i) = 0#u64 → ¬ Sch st s1 i := fun h0 hS => by
    rcases hS with e | e | e | e | ⟨e1, e2⟩ | e
    · exact hB1.q i hiT e h0
    · exact hB1.r i hiT e h0
    · exact hB1.act (by rw [e]; exact hiT) (by rw [e]; exact h0)
    · exact hB1.idle (by rw [e]; exact h0)
    · exact hB1.resume e1 (by rw [e2]; exact h0)
    · rw [st1] at e
      rcases e with e | e
      · exact not_blocked_running e
      · exact running_ne.1 e
  refine WP.spec_bind (notification.maybe_donate_sched_context.tinvB hA s1 a i n Q1 R1 q1 hB1 hX1 hS1 hSg1 hiT
    (ntfn_sc_ok hX1 hn hsA1)) ?_
  rintro ⟨s2, a1⟩ ⟨⟨⟨Q2, R2, q2⟩, hB2, hX2, hS2, hSg2⟩, -⟩
  try simp only [WP.uncurry'_pair]
  step with sched.is_schedulable.spec' as ⟨b2, hb2⟩
  refine WP.spec_bind (Pₘ := fun s3 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s3) ?_ ?_
  · split
    · rename_i hb
      refine WP.spec_mono (sched.possible_switch_to.sch s2 i Q2 R2 q2 hB2 hSg2 hiT (hb2 hb).1
        (fun _ => (hS2.act _ (hX2.2.2.bound i hiT (hb2 hb).2.1).1).2 (hb2 hb).2.2.2)) fun s3 hh => ?_
      obtain ⟨p3, -, -⟩ := hh
      exact ⟨p3.inv, p3.bnd, hX2.fr p3.fr, hS2.fr p3.fr, hSg2.fr p3.fr⟩
    · exact (WP.spec_ok _).2 ⟨⟨Q2, R2, q2⟩, hB2, hX2, hS2, hSg2⟩
  rintro s3 ⟨⟨Q3, R3, q3⟩, hB3, hX3, hS3, hSg3⟩
  have ok3 : (ok (s3, a1) : Result (S × A)) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ :=
    (WP.spec_ok _).2 ⟨⟨Q3, R3, q3⟩, hB3, hX3, hS3, hSg3⟩
  step with obj.Tcb.sc.spec as ⟨i4, ei4⟩
  step with obj.Sc.is_null.spec as ⟨b3, _hb3⟩
  refine sig_if _ _ _ _ (fun _ => ok3) (fun _ => ?_)
  refine WP.spec_bind (sporadic.sc_active.spec s3 i4) fun b4 _ => ?_
  refine sig_if _ _ _ _ (fun _ => ?_) (fun _ => ok3)
  refine WP.spec_bind (obj.Ntfn.sc.any s3 n) fun i5 _ => ?_
  refine sig_if _ _ _ _ (fun _ => ?_) (fun _ => ok3)
  step with sporadic.sc_sporadic.spec as ⟨b5, eb5⟩
  refine sig_if _ _ _ _ (fun hb5 => ?_) (fun _ => ok3)
  step with sched.cur_sc.spec as ⟨c4, _⟩
  step with sc_ne.spec as ⟨b6⟩
  refine sig_if _ _ _ _ (fun _ => ?_) (fun _ => ok3)
  have hi4S : i4 ∈ Scs := (hX3.2.2.bound i hiT (by rw [← ei4]; exact (eb5 hb5).1)).1 |> fun h => by
    rw [← ei4] at h; exact h
  refine WP.spec_bind (sporadic.unblock_check.all s3 i i4 q3 hB3 hX3 hS3 hSg3 hiT ei4 (eb5 hb5).1
    (hS3.spor i4 hi4S (eb5 hb5).2)) fun s5 hh => ?_
  obtain ⟨q5, hB5, hX5, hS5, hSg5, -⟩ := hh
  exact (WP.spec_ok _).2 ⟨⟨Q3, R3, q5⟩, hB5, hX5, hS5, hSg5⟩

/-- seL4 `sendSignal`: an idle notification with a bound thread blocked on
receive wakes it (its receive is cancelled), otherwise it becomes active; a
waiting notification wakes its first waiter; an active one accumulates the
badge.  The woken thread gets the badge, the notification's SC (if unbound),
and is a switch candidate. -/
theorem notification.send_signal.tinv {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (n badge : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hn : n ∈ Nt)
    (hH : H n = some .ntfn) :
    notification.send_signal st ar s a n badge ⦃ s' _ => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  have hI := h
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hTm := hX.2.2.tm
  have hNb := hX.2.2.ntb
  have hT := h0.tcbs
  have act : ∀ (s1 : S), notification.set_active st s n badge ⦃ s' => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ →
      (do let s1 ← notification.set_active st s n badge; ok (s1, a)) ⦃ s' _ => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ :=
    fun _ hsa => WP.spec_bind hsa fun s1 h1 => (WP.spec_ok _).2 h1
  unfold notification.send_signal
  step with obj.Ntfn.state.spec as ⟨v, hv⟩
  refine sig_if _ _ _ _ (fun hidl => ?_) (fun hnidl => ?_)
  · -- an idle notification
    have hst0 : L.epState s n ≠ 1#u64 := by rw [← hv, hidl]; unfold obj.NTFN_IDLE; decide
    have sa := notification.set_active.tinv s n badge hI hn hH hst0
    step with obj.Ntfn.bound_tcb.val as ⟨i, ei⟩
    step with obj.Tcb.is_null.spec as ⟨b, eb⟩
    refine sig_if _ _ _ _ (fun hb => ?_) (fun hb => ?_)
    · rw [if_pos hb]
      refine WP.spec_bind sa fun s1 h1 => ?_
      rw [if_pos hb]
      exact (WP.spec_ok _).2 h1
    have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    have hiT : i ∈ T := by
      rcases hNb n hn with e | e
      · rw [← ei] at e; exact absurd e hi0
      · rw [← ei] at e; exact e
    have hta := hT i hiT
    step with obj.Tcb.state.spec as ⟨i1, ei1⟩
    refine sig_if _ _ _ _ (fun hrecv => ?_) (fun hnrecv => ?_)
    · have hst : L.mem s (stA i) = sched.TS_BLOCKED_ON_RECV := by rw [← ei1, hrecv]
      have hbl : Blocked (L.mem s (stA i)) := by rw [hst]; exact Or.inr (Or.inl rfl)
      obtain ⟨dq, dr, da⟩ := blocked_out h0 hiT (not_runnable_of_blocked hbl)
      refine WP.spec_bind (ipc.cancel_ipc.all s a i Q R h0 hiT hB hX hSg.sub) ?_
      rintro ⟨s1, a1⟩ ⟨h1, hB1, hX1, nb1, nr1, -, k1, -⟩
      try simp only [WP.uncurry'_pair]
      have hS1 := hS.keepT hX k1
      have hSg1 : SgOK st Ω Sg s1 := ⟨hSg.sub, fun b hb => by rw [k1.ksb]; exact hSg.ks b hb,
        fun o h1' h2' => by rw [k1.ksb]; exact hSg.ksΩ o h1' h2'⟩
      have dq1 : (L.mem s1 (inqA i) &&& sched.Q_QUEUED) = 0#u64 := by rw [k1.inqf hiT]; exact dq
      have dr1 : (L.mem s1 (inqA i) &&& sched.Q_RELEASE) = 0#u64 := by rw [k1.inqf hiT]; exact dr
      have da1 : L.actionW s1 ≠ i := by
        rcases k1.act with e | e
        · rw [e]; exact da
        · rw [e]; exact fun e' => notT_small hT (by simp) (e' ▸ hiT)
      refine WP.spec_bind (sts_all s1 i _ Q R h1 hB1 hX1 hS1 hSg1 hiT not_blocked_running running_ne
        (Or.inr nb1) (hX1.noref hta nr1 (fun e => nb1 (by rw [e]; exact Or.inr (Or.inl rfl))))
        ⟨fun _ _ _ _ _ => runnable_running, fun _ _ _ => runnable_running, fun _ => runnable_running⟩) ?_
      rintro s2 ⟨h2, hB2, hX2, hS2, hSg2, st2, k2⟩
      have h2' : SchedQueuesInv st T Cs Ω H s2 Q R := h2.congrX empty_congr
      have dq2 : (L.mem s2 (inqA i) &&& sched.Q_QUEUED) = 0#u64 := by rw [k2.inqf hiT]; exact dq1
      have dr2 : (L.mem s2 (inqA i) &&& sched.Q_RELEASE) = 0#u64 := by rw [k2.inqf hiT]; exact dr1
      have da2 : L.actionW s2 ≠ i := by
        rcases k2.act with e | e
        · rw [e]; exact da1
        · rw [e]; exact fun e' => notT_small hT (by simp) (e' ▸ hiT)
      refine WP.spec_mono (signal_tail hA s2 a1 i n badge Q R h2' hB2 hX2 hS2 hSg2 hiT hn dq2 dr2 da2
        (fun e => hB.idleNB (by rw [← k1.idleW, ← k2.idleW, e]; exact Or.inl hbl))
        (by rw [st2]; rintro (hb | hb); exact not_blocked_running hb; exact running_ne.1 hb)) ?_
      rintro ⟨s', a'⟩ ⟨hb', tm'⟩
      exact hI.of_tmfr hb' ((TmFr.of_keepT k1).trans ((TmFr.of_keepT k2).trans tm'))
    · -- not receiving: #63's same-core `RunningVM` completion, else active
      have OLD : (do
          let s1 ← notification.set_active st s n badge
          if b = true then ok (s1, a)
          else do
            let i2 ← obj.Tcb.state st i s1
            if i2 = sched.TS_RUNNING_VM then smp.remote_tcb_stall st ar s1 a i else ok (s1, a))
          ⦃ s' _ => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
        refine WP.spec_bind sa fun s1 h1 => ?_
        rw [if_neg hb]
        step with obj.Tcb.state.spec
        split
        · obtain ⟨⟨Q1, R1, hq1⟩, hb1, hx1, hs1, hg1⟩ := h1
          exact WP.spec_mono (smp.remote_tcb_stall.all hA s1 a i hq1 hb1 hx1 hs1 hg1)
            fun r ⟨hq2, hb2, hx2, hs2, hg2, _⟩ => ⟨⟨Q1, R1, hq2⟩, hb2, hx2, hs2, hg2⟩
        · exact (WP.spec_ok _).2 h1
      rw [if_neg hb]
      refine sig_if _ _ _ _ (fun hvm => ?_) (fun _ => OLD)
      step with obj.Tcb.affinity.spec as ⟨i2, _hi2⟩
      step with LawfulStore.cur_cpu_spec as ⟨i3, _hi3⟩
      refine sig_if _ _ _ _ (fun _ => ?_) (fun _ => OLD)
      refine WP.spec_bind (vcpu.signal_completes.blk s i) fun b1 hb1 => ?_
      refine sig_if _ _ _ _ (fun hb1t => ?_) (fun _ => OLD)
      have hvmS : L.mem s (stA i) = sched.TS_RUNNING_VM := by rw [← ei1]; exact hvm
      refine WP.spec_bind (vcpu.report.blk hA s a i badge hI hiT hvmS (hb1 hb1t)) ?_
      rintro s1 ⟨h1, st1⟩
      exact signal_vm hA s1 a i n h1 hiT hn st1
  · split
    · -- a waiting notification
      rename_i hwait
      have hst1 : L.epState s n = 1#u64 := by rw [← hv, hwait]; unfold obj.NTFN_WAITING; rfl
      obtain ⟨hdT, hbe, hds⟩ := ntfn_head h0 hH hst1
      step with notification.get_queue.spec as ⟨q, eq⟩
      subst eq
      set hd := (L.epQ s n).head with hhd
      have hta := hT hd hdT
      have hbl : Blocked (L.mem s (stA hd)) := by rw [hds]; exact Or.inr (Or.inr rfl)
      obtain ⟨dq, dr, da⟩ := blocked_out h0 hdT (not_runnable_of_blocked hbl)
      have hdq := notification.ntfn_dequeue.inv s hd Q R h0 hdT (by simp) hbl
      rw [hbe] at hdq
      refine WP.spec_bind hdq ?_
      rintro s1 ⟨h1, f1, o1, n1, k1, c1, nc1⟩
      have tm1 : TmFr st T Cs Nt s s1 := TmFr.mk0 ⟨k1, fun y hy K a b c => f1 y hy K (by omega) c (by omega) (by omega),
        fun c hc o ho => nc1 c hc o (by omega) (by omega), fun n' hn' => o1 _ (hSg.sub _ (hX.1.ntB n' hn').2)⟩
      obtain ⟨hB1, hX1, hS1, hSg1, ea1, ec1, ei1⟩ := frame_bx h0 hB hX hS hSg f1 o1 n1 k1 tm1
      have st1 : L.mem s1 (stA hd) = sched.TS_BLOCKED_ON_NTFN := by
        rw [stA_eq, f1 hd hdT _ (by simp) (by simp) (by simp) (by simp), ← stA_eq]; exact hds
      have iq1 : L.mem s1 (inqA hd) = L.mem s (inqA hd) := by
        rw [inqA_eq]; exact f1 hd hdT _ (by simp) (by simp) (by simp) (by simp)
      obtain ⟨-, -, r3, -, r6⟩ := ts_vals
      refine WP.spec_bind (sts_all s1 hd _ Q R h1 hB1 hX1 hS1 hSg1 hdT not_blocked_running running_ne
        (Or.inl (Or.inr rfl)) (hX1.noref hta (by rw [st1]; exact blocked_ne_reply (Or.inr (Or.inr rfl)))
          (by rw [st1, r3, r6]; decide))
        ⟨fun _ _ _ _ _ => runnable_running, fun _ _ _ => runnable_running, fun _ => runnable_running⟩) ?_
      rintro s2 ⟨h2, hB2, hX2, hS2, hSg2, st2, k2⟩
      have h2' : SchedQueuesInv st T Cs Ω H s2 Q R := h2.congrX empty_congr'
      have dq2 : (L.mem s2 (inqA hd) &&& sched.Q_QUEUED) = 0#u64 := by rw [k2.inqf hdT, iq1]; exact dq
      have dr2 : (L.mem s2 (inqA hd) &&& sched.Q_RELEASE) = 0#u64 := by rw [k2.inqf hdT, iq1]; exact dr
      have da2 : L.actionW s2 ≠ hd := by
        rcases k2.act with e | e
        · rw [e, ea1]; exact da
        · rw [e]; exact fun e' => notT_small hT (by simp) (e' ▸ hdT)
      refine WP.spec_mono (signal_tail hA s2 a hd n badge Q R h2' hB2 hX2 hS2 hSg2 hdT hn dq2 dr2 da2
        (fun e => hB.idleNB (by rw [← ei1, ← k2.idleW, e]; exact Or.inl hbl))
        (by rw [st2]; rintro (hb | hb); exact not_blocked_running hb; exact running_ne.1 hb)) ?_
      rintro ⟨s', a'⟩ ⟨hb', tm'⟩
      exact hI.of_tmfr hb' (tm1.trans ((TmFr.of_keepT k2).trans tm'))
    · -- an active notification
      step with obj.Ntfn.badge.val as ⟨i, ei⟩
      simp only [lift, Aeneas.Std.bind_ok]
      refine WP.spec_bind (obj.Ntfn.set_badge.wr s n _) fun s1 e1 => ?_
      subst e1
      obtain ⟨b1, tm1⟩ := ntfn_badge_all (v := i ||| badge)
        (⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) hn
      exact (WP.spec_ok _).2 (hI.of_tmfr b1 tm1)


/-! ## Binding a notification to a TCB (`BOUND_TCB` / `BOUND_NTFN` writes) -/

theorem obj.Ntfn.set_bound_tcb.wr (s : S) (n : obj.Ntfn) (v : U64) :
    obj.Ntfn.set_bound_tcb st n s v ⦃ s' => s' = L.wr s (ntfnBtA n) v ⦄ := by
  unfold obj.Ntfn.set_bound_tcb; step*; simp_all [ntfnBtA]
theorem obj.Tcb.set_bound_ntfn.wr (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_bound_ntfn st t s v ⦃ s' => s' = L.wr s (boundA t) v ⦄ := by
  unfold obj.Tcb.set_bound_ntfn; step*; simp_all [boundA]

/-- A write of a null or a TCB to a notification's `BOUND_TCB` word. -/
theorem ntbt_all {s : S} {n v : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hn : n ∈ Nt) (hv : Tz T v) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s (ntfnBtA n) v) := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hO := hX.1
  have hP := hO.ntP n hn
  have av := ntfnBtA_val hP
  have hm : ntfnBtA n ∈ Ω := hSg.sub _ (hO.ntB n hn).2
  obtain ⟨h1, hB1, hX1, hS1, hSg1, -⟩ := link_allT (w := v) h0 hB hX hS hSg hm
    (fun r hr => by rw [av, (rp_facts hO hr).2.1]; have := hO.ntORp n hn r hr; omega)
    (fun c hc => by
      obtain ⟨h128, e1, e2, e3, e4, e5, -⟩ := sc_facts hO hc
      rw [av, e1, e2, e3, e4, e5]; have := hO.ntOSc n hn c hc; omega)
    (fun r hr e => by rw [av, (rp_facts hO hr).2.2.2] at e; have := hO.ntORp n hn r hr; omega)
    (fun r hr e => by rw [av, (rp_facts hO hr).2.2.1] at e; have := hO.ntORp n hn r hr; omega)
    (fun c hc e => by
      rw [av, (sc_facts hO hc).2.2.2.2.2.2.1] at e; have := hO.ntOSc n hn c hc; have := (sc_facts hO hc).1; omega)
    (fun n' hn' e => absurd e (by
      rw [av, ntfnScA_val (hO.ntP n' hn')]; have := hP.1; have := (hO.ntP n' hn').1; omega))
    (fun c hc e => absurd e (by
      obtain ⟨hPc, hzc⟩ := hO.sc c hc
      rw [av, scNtfnA_val hPc hzc]; have := hO.ntOSc n hn c hc; have := (sc_facts hO hc).1; omega))
    (fun _ _ _ => hv)
    (fun c hc e => absurd e (by
      obtain ⟨hPc, hzc⟩ := hO.sc c hc
      rw [av, scNtfnA_val hPc hzc]; have := hO.ntOSc n hn c hc; have := (sc_facts hO hc).1; omega))
    (fun c hc e => absurd e (by
      rw [av, show scYieldFromA c = core.num.U64.wrapping_add c layout.sc.YIELD_FROM from rfl,
        (sc_facts hO hc).2.2.2.2.2.2.2]; have := hO.ntOSc n hn c hc; have := (sc_facts hO hc).1; omega))
    (fun c hc => by
      obtain ⟨hPc, hzc⟩ := hO.sc c hc
      rw [av, sporA_val hPc hzc]; have := hO.ntOSc n hn c hc; have := (sc_facts hO hc).1; omega)
    (fun r hr e _ _ => absurd e (by rw [av, (rp_facts hO hr).2.2.2]; have := hO.ntORp n hn r hr; omega))
    (fun c hc e => absurd e (by
      rw [av, (sc_facts hO hc).2.2.2.2.2.2.1]; have := hO.ntOSc n hn c hc; have := (sc_facts hO hc).1; omega))
  exact ⟨⟨Q, R, h1⟩, hB1, hX1, hS1, hSg1⟩

/-- A write of a null or a notification to a TCB's `BOUND_NTFN` field. -/
theorem bnd_all {s : S} {t v : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T)
    (hv : v ≠ 0#u64 → v ∈ Nt) : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s (boundA t) v) := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hT := h0.tcbs
  have hya := hT t ht
  have hN' := h0.nodes _ h0.cur
  have ha : Aligned (boundA t) := field_aligned hya (K := 3368#u64) (by simp) (by simp)
  have fk : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (y = t → K.val ≠ 3368) →
      L.mem (L.wr s (boundA t) v) (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K hK hK8 hne => L.mem_wr_ne ha (field_aligned (hT y hy) hK hK8) fun e =>
      field_ne hya (hT y hy) (K1 := 3368#u64) (by simp) hK (fun e' => by have := hne e'.symm; simp; omega)
        (UScalar.eq_of_val_eq e)
  have om : ∀ b ∈ Ω, L.mem (L.wr s (boundA t) v) b = L.mem s b := fun b hb =>
    L.mem_wr_ne ha (h0.omega _ hb).1 (out_ne_field (K := 3368#u64) (h0.omega _ hb) ht hya (by simp))
  have nd : ∀ o : U64, (o.val = 0 ∨ o.val = 8 ∨ o.val = 16 ∨ o.val = 24) →
      L.mem (L.wr s (boundA t) v) (L.nodeAt (L.wr s (boundA t) v) (L.cpu (L.wr s (boundA t) v)) o) =
        L.mem s (L.nodeAt s (L.cpu s) o) := fun o ho => by
    simp only [LawfulStore.cpu_wr, nodeAt_wr]
    exact L.mem_wr_ne ha (nodeAt_aligned hN' (by omega) (by omega))
      (fun e => node_ne_field (K := 3368#u64) hN' (by omega) ht hya (by simp) (UScalar.eq_of_val_eq e).symm)
  have hsc : ∀ y ∈ T, L.mem (L.wr s (boundA t) v) (scA y) = L.mem s (scA y) := fun y hy => by
    rw [scA_eq]; exact fk y hy _ (by simp) (by simp) (fun _ => by simp)
  have hiq : ∀ y ∈ T, L.mem (L.wr s (boundA t) v) (inqA y) = L.mem s (inqA y) := fun y hy => by
    rw [inqA_eq]; exact fk y hy _ (by simp) (by simp) (fun _ => by simp)
  have hst : ∀ y ∈ T, L.mem (L.wr s (boundA t) v) (stA y) = L.mem s (stA y) := fun y hy => by
    rw [stA_eq]; exact fk y hy _ (by simp) (by simp) (fun _ => by simp)
  have hrp : ∀ y ∈ T, L.mem (L.wr s (boundA t) v) (replyA y) = L.mem s (replyA y) := fun y hy =>
    fk y hy _ (by simp) (by simp) (fun _ => by simp)
  have ea : L.actionW (L.wr s (boundA t) v) = L.actionW s := by
    unfold LawfulStore.actionW; exact nd _ (by rw [act_val]; omega)
  have ec : L.curW (L.wr s (boundA t) v) = L.curW s := by unfold LawfulStore.curW; exact nd _ (by rw [curth0]; omega)
  have ei : L.idleW (L.wr s (boundA t) v) = L.idleW s := by unfold LawfulStore.idleW; exact nd _ (by rw [idle8]; omega)
  have ecs : L.cscW (L.wr s (boundA t) v) = L.cscW s := by
    unfold LawfulStore.cscW LawfulStore.nodeA; exact nd _ (by simp [layout.node.CUR_SC])
  obtain ⟨hrΩ, hcΩ⟩ := objs_omega hX.1 hSg.sub
  refine ⟨⟨Q, R, inv_wr_field (K := 3368#u64) h0 ht (by simp) (by simp) (by simp)⟩,
    hB.mk' hsc (fun y hy hf => Or.inl (by rw [← hiq y hy]; exact hf))
      (fun y hy hf => Or.inr (Or.inl (by rw [← hiq y hy]; exact hf))) (fun haT => ?_)
      (by rw [ei]; exact ⟨h0.idleT, hB.idle⟩) (fun h1 => ?_) (hB.nb ei (hst _ h0.idleT))
      (fun y hy hS _ => Or.inl (Sch.of_eq (fun hf => by rwa [hiq y hy] at hf) (fun hf => by rwa [hiq y hy] at hf)
        ea ei ec (hst y hy) hS)),
    hX.keep' (fun r hr => ⟨om _ (hrΩ r hr).1, om _ (hrΩ r hr).2.1, om _ (hrΩ r hr).2.2⟩)
      (fun c hc => ⟨om _ (hcΩ c hc).1, om _ (hcΩ c hc).2.1⟩) hsc hrp hst (by rw [ecs]; exact hX.2.2.cur)
      (fun c hc => om _ (hSg.sub _ (hX.1.repW c hc))) (fun y hy hb => ?_)
      (fun n hn => om _ (hSg.sub _ (hX.1.ntW n hn)))
      (hX.tn_field (K := 3368#u64) h0 hSg.sub ht (by simp) (by simp) (by simp))
      (fun c hc => om _ (hSg.sub _ (hX.1.snW c hc)))
      (hX.2.2.yt.keep (fun c hc => om _ (hcΩ c hc).1) (fun y hy => fk y hy _ (by simp) (by simp) (fun _ => by simp))
        (fun c hc => om _ (hSg.sub _ (hX.1.syW c hc)))) (fun c hc => om _ (hcΩ c hc).2.2.1) ei,
    SCsOK.field (K := 3368#u64) h0 hS hX ht (by simp) (by simp) (by simp),
    ⟨hSg.sub, fun b hb => by rw [L.ksb_wr]; exact hSg.ks b hb, fun o h1 h2 => by rw [L.ksb_wr]; exact hSg.ksΩ o h1 h2⟩⟩
  · rw [ea] at haT ⊢; exact ⟨haT, hB.act haT⟩
  · rw [ea] at h1; rw [ec]; exact ⟨h0.curT, hB.resume h1⟩
  · by_cases e : y = t
    · subst e; rw [L.mem_wr_same ha] at hb ⊢; exact hv hb
    · have k : L.mem (L.wr s (boundA t) v) (boundA y) = L.mem s (boundA y) :=
        fk y hy _ (by simp) (by simp) (fun e' => absurd e' e)
      rw [k] at hb ⊢; exact hX.2.2.bnd y hy hb

/-- seL4 `bindNotification`. -/
theorem notification.bind_notification.blk (s : S) (t n : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ht : t ∈ T) (hn : n ∈ Nt) :
    notification.bind_notification st s t n ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  unfold notification.bind_notification
  refine WP.spec_bind (obj.Ntfn.set_bound_tcb.wr s n t) fun s1 e1 => ?_
  subst e1
  refine WP.spec_mono (obj.Tcb.set_bound_ntfn.wr _ t n) fun s2 e2 => ?_
  subst e2
  exact bnd_all (ntbt_all h hn (Tz.of_mem ht)) ht fun _ => hn

/-- seL4 `unbindNotification`. -/
theorem notification.unbind_notification.blk (s : S) (t : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ht : t ∈ T) :
    notification.unbind_notification st s t ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  unfold notification.unbind_notification
  refine WP.spec_bind (obj.Tcb.bound_ntfn.val s t) fun i ei => ?_
  split
  · rename_i hi
    have hi0 : L.mem s (boundA t) ≠ 0#u64 := by rw [← ei]; simpa using hi
    have hin : i ∈ Nt := by rw [ei]; exact h.2.2.1.2.2.bnd t ht hi0
    refine WP.spec_bind (obj.Ntfn.set_bound_tcb.wr s i 0#u64) fun s1 e1 => ?_
    subst e1
    refine WP.spec_mono (obj.Tcb.set_bound_ntfn.wr _ t 0#u64) fun s2 e2 => ?_
    subst e2
    exact bnd_all (ntbt_all h hin Tz.zero) ht fun h0 => absurd rfl h0
  · exact (WP.spec_ok _).2 h

/-- seL4 `unbindMaybeNotification`. -/
theorem notification.unbind_maybe_notification.blk (s : S) (n : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hn : n ∈ Nt) :
    notification.unbind_maybe_notification st s n ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  unfold notification.unbind_maybe_notification
  refine WP.spec_bind (obj.Ntfn.bound_tcb.val s n) fun i ei => ?_
  refine WP.spec_bind (obj.Tcb.is_null.spec i) fun b eb => ?_
  subst eb
  split
  · exact (WP.spec_ok _).2 h
  · rename_i hb
    have hiT : i ∈ T := by
      rcases (show Tz T i by rw [ei]; exact h.2.2.1.2.2.ntb n hn) with e | e
      · exact absurd (by simp [e]) hb
      · exact e
    refine WP.spec_bind (obj.Ntfn.set_bound_tcb.wr s n 0#u64) fun s1 e1 => ?_
    subst e1
    refine WP.spec_mono (obj.Tcb.set_bound_ntfn.wr _ i 0#u64) fun s2 e2 => ?_
    subst e2
    exact bnd_all (ntbt_all h hn Tz.zero) hiT fun h0 => absurd rfl h0

theorem notification.bind_notification.tinv (s : S) (t n : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ht : t ∈ T) (hn : n ∈ Nt) :
    notification.bind_notification st s t n ⦃ s' => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ :=
  WP.spec_mono (notification.bind_notification.blk s t n h ht hn) fun _ h' => h'.tinv
theorem notification.unbind_notification.tinv (s : S) (t : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ht : t ∈ T) :
    notification.unbind_notification st s t ⦃ s' => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ :=
  WP.spec_mono (notification.unbind_notification.blk s t h ht) fun _ h' => h'.tinv
theorem notification.unbind_maybe_notification.tinv (s : S) (n : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hn : n ∈ Nt) :
    notification.unbind_maybe_notification st s n ⦃ s' => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ :=
  WP.spec_mono (notification.unbind_maybe_notification.blk s n h hn) fun _ h' => h'.tinv

end

end Fl4Proofs.P1
