/-
P1: `send_signal` keeps the IPC invariants, the timer-tree typing and the
notifications' bound-TCB typing (`TInv`).

(int6, FL4 #80 / #85) Since #80 a bound `TS_RUNNING_VM` thread's VMEnter
completion (`vcpu.report`) answers a full-state caller in its IPC buffer, and
since #85 it does so from any core: `send_signal`'s lemmas take the placement
of the TCBs' IPC buffers (`BufOK` in the user words `U`, `UsrW`) at the
signal's state (P3: `JAtZ.bufOK`, `JAtZ.bufU_out`; P1's entry: `XferHyps.buf`).
-/
import Fl4Proofs.P1.QueueTimerR
import Fl4Proofs.P1.QueueIpc
import Fl4Proofs.P1.VcpuReport
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}

/-- The words of a (non-null) IPC buffer are user words: its 128 words
(1024 bytes). FL4's IPC buffer is only 1024-byte aligned
(`check_valid_ipc_buffer`, `bits::IPC_BUFFER = 10`) and `lookup_ipc_buffer`
returns the frame pointer plus the in-frame offset, so only these 128 words
are guaranteed inside the frame (l4v `ipc_buffer_wp_at` / P3
`Endp.IpcBufCapOK`: `k < 128`). Every buffer index the kernel writes is below
128 (`msg_max_length` 120 + 1, the three extra-cap / badge words at 122..124,
the receive CNode / index / depth words 125..127; the fault messages and the
register / VCPU transfers write fewer). (Before m72 this claimed 512 words,
false for a buffer at frame offset 3072 followed by a TCB: KENTRY-PLAN m71.) -/
def BufOK (U : Set U64) (buf : U64) : Prop :=
  buf ≠ 0#u64 → ∀ i : U64, i.val < 128 → core.num.U64.wrapping_add buf (core.num.U64.wrapping_mul i 8#u64) ∈ U

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

/-- `WP` of a total computation for a post that always holds. -/
theorem spec_true_imp {α : Type _} {m : Result α} {Q : α → Prop} (hq : ∀ x, Q x) (h : m ⦃ fun _ => True ⦄) :
    m ⦃ Q ⦄ := WP.spec_mono h fun x _ => hq x

/-- (int6) **A user word a VMEnter completion may write**: outside the TCBs and
nodes, apart from the endpoints and notifications, off the frame words `Sg`,
the kernel-global area and the SC objects (with `Ω`-free placement: P1's
entry gets it from `UserOK`, P3 from `JAtZ`'s buffer facts). -/
structure UsrW (st : machine.Store S) [L : LawfulStore st] (T Cs : Set U64) (H : Heap) (Sg Scs : Set U64)
    (Z : U64 → Nat) (s : S) (b : U64) : Prop where
  out : OutsideObjs st T Cs s b
  eps : ∀ e, (H e = some .ep ∨ H e = some .ntfn) → b.val + 8 ≤ e.val ∨ e.val + 16 ≤ b.val
  sg : b ∉ Sg
  ks : ∀ o : U64, o.val < 13568 → o.val % 8 = 0 → core.num.U64.wrapping_add (L.ksb s) o ≠ b
  sc : ∀ c ∈ Scs, ¬ InSC c (Z c) b

theorem UsrW.ksb {s s' : S} {b : U64} (h : UsrW st T Cs H Sg Scs Z s b) (hk : L.ksb s' = L.ksb s) :
    UsrW st T Cs H Sg Scs Z s' b :=
  ⟨h.out.ksb hk, h.eps, h.sg, fun o h1 h2 => by rw [hk]; exact h.ks o h1 h2, h.sc⟩

/-- `UsrW` from P1's `UserOK` (the user words are off `Ω`, which holds `Sg`,
the kernel-global area and the SC objects). -/
theorem UserOK.usrW {U : Set U64} {s : S} (hU : UserOK st T Cs Ω H U s) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s b := fun b hb => by
  obtain ⟨⟨Q, R, h0⟩, -, hX, hS, hSg⟩ := h
  obtain ⟨ho, hn, he⟩ := hU b hb
  exact ⟨ho, he, fun hs => hn (hSg.sub b hs), fun o h1 h2 e => hn (e ▸ hSg.ksΩ o h1 h2),
    fun c hc hin => hn (hX.1.scW c hc b ho.1 hin)⟩

/-- `BlkOK` over a smaller `Ω₁` (holding the frame words, the kernel-global
area and the SC objects). -/
theorem BlkOK.shrinkΩ {Ω₁ Ω₂ : Set U64} {s : S} (h : BlkOK st T Cs Ω₂ H Sg Rp Scs Nt Z Ac s)
    (h12 : ∀ b ∈ Ω₁, b ∈ Ω₂)
    (hks : ∀ o : U64, o.val < 13568 → o.val % 8 = 0 → core.num.U64.wrapping_add (L.ksb s) o ∈ Ω₁)
    (hsc : ∀ c ∈ Scs, ∀ b : U64, Aligned b → InSC c (Z c) b → b ∈ Ω₁) (hsg : ∀ b ∈ Sg, b ∈ Ω₁) :
    BlkOK st T Cs Ω₁ H Sg Rp Scs Nt Z Ac s := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  obtain ⟨E, EQ, w1, w2, w3, w4, w5, k⟩ := h0.eps
  have q : SchedQueuesInv st T Cs Ω₁ H s Q R :=
    { h0 with
      eps := ⟨E, EQ, w1, w2, fun e he a ha => w3 e he a (h12 a ha), w4, w5, k⟩
      omega := fun a ha => h0.omega a (h12 a ha) }
  have x : XInv st T Cs Ω₁ Sg Rp Scs Nt Z s := ⟨{ hX.1 with scW := hsc }, hX.2⟩
  exact ⟨⟨Q, R, q⟩, hB, x, { hS with sub := hsg, ksΩ := hks }, ⟨hsg, hSg.ks, hks⟩⟩

/-- `BlkOK` over a larger `Ω₂` whose new words are outside the TCBs and nodes
and apart from the endpoints and notifications. -/
theorem BlkOK.growΩ {Ω₁ Ω₂ : Set U64} {s : S} (h : BlkOK st T Cs Ω₁ H Sg Rp Scs Nt Z Ac s)
    (h12 : ∀ b ∈ Ω₁, b ∈ Ω₂)
    (h21 : ∀ b ∈ Ω₂, b ∈ Ω₁ ∨ (OutsideObjs st T Cs s b ∧
      ∀ e, (H e = some .ep ∨ H e = some .ntfn) → b.val + 8 ≤ e.val ∨ e.val + 16 ≤ b.val)) :
    BlkOK st T Cs Ω₂ H Sg Rp Scs Nt Z Ac s := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  obtain ⟨E, EQ, w1, w2, w3, w4, w5, k⟩ := h0.eps
  have k3 := k.2.2.1
  have q : SchedQueuesInv st T Cs Ω₂ H s Q R :=
    { h0 with
      eps := ⟨E, EQ, w1, w2, fun e he a ha => (h21 a ha).elim (w3 e he a) fun hu => hu.2 e ((k3 e).1 he), w4, w5, k⟩
      omega := fun a ha => (h21 a ha).elim (h0.omega a) fun hu => hu.1 }
  have x : XInv st T Cs Ω₂ Sg Rp Scs Nt Z s :=
    ⟨{ hX.1 with scW := fun c hc b ha hin => h12 _ (hX.1.scW c hc b ha hin) }, hX.2⟩
  exact ⟨⟨Q, R, q⟩, hB, x, { hS with sub := fun b hb => h12 _ (hS.sub b hb), ksΩ := fun o h1 h2 => h12 _ (hS.ksΩ o h1 h2) },
    ⟨fun b hb => h12 _ (hSg.sub b hb), hSg.ks, fun o h1 h2 => h12 _ (hSg.ksΩ o h1 h2)⟩⟩

/-- **A write of user registers and `UsrW` words keeps `BlkOK`** (`xfer_all`
over `Ω` without the written user words) and the TCB fields past the
registers. -/
theorem bufw_xfer {U : Set U64} {s s' : S} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hU : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s b) (hw : WritesIn st s s' (XferFoot T U)) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      (∀ y ∈ T, ∀ K : U64, 3328 ≤ K.val → K.val < 4096 → K.val % 8 = 0 →
        L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) := by
  have hO := h.2.2.1.1
  have h1 : BlkOK st T Cs {b | b ∈ Ω ∧ b ∉ U} H Sg Rp Scs Nt Z Ac s :=
    h.shrinkΩ (fun b hb => hb.1)
      (fun o h1 h2 => ⟨h.2.2.2.2.ksΩ o h1 h2, fun hu => (hU _ hu).ks o h1 h2 rfl⟩)
      (fun c hc b ha hin => ⟨hO.scW c hc b ha hin, fun hu => (hU b hu).sc c hc hin⟩)
      (fun b hb => ⟨h.2.2.2.2.sub b hb, fun hu => (hU b hu).sg hb⟩)
  have hU1 : UserOK st T Cs {b | b ∈ Ω ∧ b ∉ U} H U s := fun b hb => ⟨(hU b hb).out, fun hm => hm.2 hb, (hU b hb).eps⟩
  obtain ⟨⟨Q, R, q⟩, hB, hX, hS, hSg⟩ := h1
  obtain ⟨q2, hB2, hX2, hS2, hSg2, -, -, -, -, f, -⟩ := xfer_all q hB hX hS hSg hU1 hw
  refine ⟨BlkOK.growΩ ⟨⟨Q, R, q2⟩, hB2, hX2, hS2, hSg2⟩ (fun b hb => hb.1) (fun b hb => ?_), f⟩
  by_cases hu : b ∈ U
  · exact Or.inr ⟨(hU b hu).out.ksb hw.1, (hU b hu).eps⟩
  · exact Or.inl ⟨hb, hu⟩

/-- (int6) The words `vcpu.report` writes before the final state change: the
thread's register words (TCB+256..3328) and the user words `U`. -/
def RepW (t : U64) (U : Set U64) (b : U64) : Prop :=
  (∃ K : U64, 256 ≤ K.val ∧ K.val < 3328 ∧ K.val % 8 = 0 ∧ b = core.num.U64.wrapping_add t K) ∨ b ∈ U

theorem RepW.xfer {U : Set U64} {t b : U64} (ht : t ∈ T) (h : RepW t U b) : XferFoot T U b :=
  h.elim (fun ⟨K, _, h2, h3, e⟩ => Or.inl ⟨t, ht, K, h2, h3, e⟩) Or.inr

/-- (int6) A message-register write of a TCB: a user register, or a word of
its IPC buffer (user words `U`, `BufOK`). -/
theorem msg.set_mr.xw {U : Set U64} (s : S) {t buf i v : U64} (hta : TcbAddr t) (hb : BufOK U buf)
    (hU : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s b) (hi : i.val < 127) :
    msg.set_mr st s t buf i v ⦃ r => WritesIn st s r.2 (RepW t U) ⦄ := by
  unfold msg.set_mr
  split
  · have hreg : msg.msg_register i ⦃ r => r.val < 384 ⦄ := by
      unfold msg.msg_register
      split; · simp [layout.reg.R10]
      split; · simp [layout.reg.R8]
      split; · simp [layout.reg.R9]
      simp [layout.reg.R15]
    refine WP.spec_bind hreg fun r hr => ?_
    refine WP.spec_bind (obj.Tcb.set_reg.wrS s t r v hta hr) fun s1 hs1 => ?_
    obtain ⟨K, hK, e⟩ := hs1
    subst e
    simp only [lift, bind_ok]
    exact (WP.spec_ok _).2 ((writesIn_wr (field_aligned hta (by omega) (by omega))).mono fun b e =>
      Or.inl ⟨K, by omega, by omega, by omega, e⟩)
  · split
    · rename_i hne
      have h0 : buf ≠ 0#u64 := by simpa using hne
      simp only [lift, bind_ok]
      have hi1 : (core.num.U64.wrapping_add i 1#u64).val < 128 := by
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      have hu := hb h0 _ hi1
      refine WP.spec_bind (Pₘ := fun s1 => WritesIn st s s1 (RepW t U)) ?_ fun s1 h1 => (WP.spec_ok _).2 h1
      unfold msg.buf_set
      simp only [lift, bind_ok]
      refine WP.spec_mono (LawfulStore.write_spec s _ v) fun s' e => ?_
      subst e
      exact (writesIn_wr (hU _ hu).out.1).mono fun b e => Or.inr (e ▸ hu)
    · exact (WP.spec_ok _).2 (WritesIn.refl _ _)

/-- The report's `RepW` words keep the timer words (`TmFr`). -/
theorem RepW.tmfr {U : Set U64} {s s1 : S} {t : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hU : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s b) (ht : t ∈ T) (w : WritesIn st s s1 (RepW t U)) :
    TmFr st T Cs Nt s s1 := by
  obtain ⟨⟨Q, R, h0⟩, -, hX, -, hSg⟩ := h
  have hT := h0.tcbs
  have hΩ : ∀ n ∈ Nt, OutsideObjs st T Cs s (ntfnBtA n) := fun n hn => h0.omega _ (hSg.sub _ (hX.1.ntB n hn).2)
  refine TmFr.of_writes hT h0.nodes hX.1 w fun b hb => ?_
  rcases hb with ⟨K, h1, h2, h3, rfl⟩ | hu
  · exact notTmW_field hT h0.nodes hΩ ht (by omega) (Or.inl (by omega))
  · exact notTmW_omega hT h0.nodes (hU b hu).out fun n hn e =>
      (hU b hu).sg (by rw [UScalar.eq_of_val_eq e]; exact (hX.1.ntB n hn).2)

/-- A `RepW` step of the report keeps `BlkOK`, the thread's state word and
the accumulated `RepW` frame. -/
theorem xw_step {U : Set U64} {s s1 s2 : S} {t : U64} (h1 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1)
    (st1 : L.mem s1 (stA t) = sched.TS_RUNNING_VM) (w1 : WritesIn st s s1 (RepW t U))
    (hU1 : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s1 b) (w : WritesIn st s1 s2 (RepW t U)) (ht : t ∈ T) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s2 ∧ L.mem s2 (stA t) = sched.TS_RUNNING_VM ∧
      WritesIn st s s2 (RepW t U) := by
  obtain ⟨h2, f⟩ := bufw_xfer h1 hU1 (w.mono fun _ hb => RepW.xfer ht hb)
  refine ⟨h2, ?_, (w1.trans w).mono fun _ hb => hb.elim id id⟩
  rw [stA_eq, f t ht _ (by simp) (by simp) (by simp), ← stA_eq]; exact st1

/-- (int6, #63 / #80 / #85) **`vcpu.report` of a `TS_RUNNING_VM` thread
without a pending exit** (`signal_completes`: the thread has no VCPU or one
with `PENDING = 0`): its writes before the final state change are its user
registers and, for a full-state caller (#80), words of its IPC buffer (user
words `U`, `BufOK` of the buffer it looks up), the `RepW` words; then
`set_thread_state TS_RUNNING`. -/
theorem vcpu.report.xf {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t badge : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T)
    (hvm : L.mem s (stA t) = sched.TS_RUNNING_VM)
    (hc : L.mem s (core.num.U64.wrapping_add t 3664#u64) ≠ 0#u64 →
      L.mem s (core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add t 3664#u64)) vcpu.PENDING) = 0#u64)
    (hU : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s b) (hbuf : msg.lookup_ipc_buffer st s true t ⦃ b => BufOK U b ⦄) :
    vcpu.report st ar s a t badge ⦃ s' => ∃ s1, BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1 ∧
      L.mem s1 (stA t) = sched.TS_RUNNING_VM ∧ WritesIn st s s1 (RepW t U) ∧
      sched.set_thread_state st s1 t sched.TS_RUNNING = ok s' ⦄ := by
  have hS0 : P0.StoreTotal st := L.total
  have hT : TcbPlaced T := h.1.choose_spec.choose_spec.tcbs
  refine vcpu.report.gen (Bok := BufOK U) (vOk := fun _ => False)
    (P := fun s1 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1 ∧ L.mem s1 (stA t) = sched.TS_RUNNING_VM ∧
      WritesIn st s s1 (RepW t U)) hA ⟨?_, ?_, fun _ _ _ hv => hv.elim⟩ ?_ ⟨h, hvm, WritesIn.refl _ _⟩
    hbuf (fun h0 hp => absurd (hc h0) hp)
  · rintro s1 b i v hb ⟨h1, st1, w1⟩ hi
    exact WP.spec_mono (msg.set_mr.xw s1 (hT t ht) hb (fun b hb => (hU b hb).ksb w1.1) (by omega)) fun r w =>
      xw_step h1 st1 w1 (fun b hb => (hU b hb).ksb w1.1) w ht
  · rintro s1 r v ⟨h1, st1, w1⟩ hr
    have hr' : r.val < 384 := by
      rcases hr with rfl | rfl | rfl <;>
        simp [layout.reg.MSG_INFO, layout.reg.BADGE, layout.reg.FAULT_IP, layout.reg.RSI, layout.reg.RDI]
    refine WP.spec_mono (obj.Tcb.set_reg.wrS s1 t r v (hT t ht) hr') fun s2 hs2 => ?_
    obtain ⟨K, hK, e⟩ := hs2
    subst e
    exact xw_step h1 st1 w1 (fun b hb => (hU b hb).ksb w1.1) ((writesIn_wr (field_aligned (hT t ht) (by omega) (by omega))).mono
      fun b e => Or.inl ⟨K, by omega, by omega, by omega, e⟩) ht
  · intro s1 h1
    exact WP.spec_mono (spec_eq' (Fl4Proofs.P0.sched.set_thread_state.p0 _ _ _ _ hS0)) fun s' hs' =>
      ⟨s1, h1.1, h1.2.1, h1.2.2, hs'.1⟩

/-- **#63's `vcpu.report` without a saved exit** (`signal_completes`), from
`vcpu.report.xf`: the thread made running, the invariants kept (since #80 a
full-state caller's IPC-buffer words are written too, user words `U`). -/
theorem vcpu.report.blk {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t badge : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T)
    (hvm : L.mem s (stA t) = sched.TS_RUNNING_VM)
    (hc : L.mem s (core.num.U64.wrapping_add t 3664#u64) ≠ 0#u64 →
      L.mem s (core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add t 3664#u64)) vcpu.PENDING) = 0#u64)
    (hU : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s b) (hbuf : msg.lookup_ipc_buffer st s true t ⦃ b => BufOK U b ⦄) :
    vcpu.report st ar s a t badge ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      L.mem s' (stA t) = sched.TS_RUNNING ⦄ := by
  refine WP.spec_mono (vcpu.report.xf hA s a t badge h ht hvm hc hU hbuf) ?_
  rintro s' ⟨s1, h1, st1, -, e⟩
  obtain ⟨⟨Q5, R5, q5⟩, hB5, hX5, hS5, hSg5⟩ := h1
  have hst := sts_all s1 t _ Q5 R5 q5 hB5 hX5 hS5 hSg5 ht not_blocked_running running_ne
    (Or.inr (by rw [st1]; exact not_blocked_vm))
    (hX5.noref (q5.tcbs t ht) (by rw [st1]; exact runnable_ne_reply (Or.inr (Or.inr rfl)))
      (by rw [st1]; exact runnable_ne_recv (Or.inr (Or.inr rfl))))
    ⟨fun _ _ _ _ _ => runnable_running, fun _ _ _ => runnable_running, fun _ => runnable_running⟩
  rw [e, WP.spec_ok] at hst
  obtain ⟨q6, hB6, hX6, hS6, hSg6, st6, -⟩ := hst
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

/-- `vcpu.signal_completes` (#85: same core, or a full-state caller that is
not its core's current thread): only for a VCPU without a pending exit. -/
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
  refine WP.spec_bind (obj.Tcb.affinity.spec s t) fun cpu _ => ?_
  split
  · unfold vcpu.get
    simp only [lift, bind_ok]
    refine WP.spec_bind (LawfulStore.read_spec s _) fun i ei => ?_
    split
    · rename_i hi
      refine spec_true_imp (fun _ _ _ => by rw [← ev, ← ei]; exact hi) ?_
      refine WP.spec_bind (L.cur_cpu_spec s) fun c _ => ?_
      split
      · exact (WP.spec_ok _).2 trivial
      refine WP.spec_bind (Fl4Proofs.P0.vcpu.full_reply.p0 _ _ _ hS0) fun f _ => ?_
      split
      · exact WP.spec_bind (obj.node_get.spec s _ _) fun _ _ => (WP.spec_ok _).2 trivial
      · exact (WP.spec_ok _).2 trivial
    · exact (WP.spec_ok _).2 fun hb => absurd hb (by simp)
  · exact (WP.spec_ok _).2 fun hb => absurd hb (by simp)

/-- (#85) `kick_guest` writes nothing: a reschedule IPI to the thread's core
when it is that core's current thread. -/
theorem notification.kick_guest.same {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t : obj.Tcb) : notification.kick_guest st ar s a t ⦃ r => r.1 = s ⦄ := by
  unfold notification.kick_guest
  refine WP.spec_bind (obj.Tcb.affinity.spec s t) fun cpu _ => ?_
  refine WP.spec_bind (L.cur_cpu_spec s) fun c _ => ?_
  split
  · refine WP.spec_bind (obj.node_get.spec s _ _) fun _ _ => ?_
    split
    · simp only [lift, bind_ok]
      refine WP.spec_bind (Pₘ := fun _ => True) (by p0_auto) fun _ _ => ?_
      exact WP.spec_bind (hA.send_reschedule _ _) fun _ _ => (WP.spec_ok _).2 rfl
    · exact (WP.spec_ok _).2 rfl
  · exact (WP.spec_ok _).2 rfl

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
and is a switch candidate.  (int6, FL4 #80 / #85) A bound `TS_RUNNING_VM`
thread whose VMEnter `signal_completes` has it completed by `vcpu.report`,
which for a full-state caller writes words of its IPC buffer: hence the
placement of the threads' IPC buffers in the user words `U` (`hU`, `hbuf`). -/
theorem notification.send_signal.tinv {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (n badge : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hn : n ∈ Nt)
    (hH : H n = some .ntfn) (hU : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s b)
    (hbuf : ∀ y ∈ T, msg.lookup_ipc_buffer st s true y ⦃ b => BufOK U b ⦄) :
    notification.send_signal st ar s a n badge ⦃ s' _ => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  have hI := h
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hTm := hX.2.2.tm
  have hNb := hX.2.2.ntb
  have hT := h0.tcbs
  unfold notification.send_signal
  step with obj.Ntfn.state.spec as ⟨v, hv⟩
  refine sig_if _ _ _ _ (fun hidl => ?_) (fun hnidl => ?_)
  · -- an idle notification
    have hst0 : L.epState s n ≠ 1#u64 := by rw [← hv, hidl]; unfold obj.NTFN_IDLE; decide
    have sa := notification.set_active.tinv s n badge hI hn hH hst0
    step with obj.Ntfn.bound_tcb.val as ⟨i, ei⟩
    step with obj.Tcb.is_null.spec as ⟨b, eb⟩
    -- the notification made active, then (#85) a `TS_RUNNING_VM` thread kicked
    have OLD : (do
        let s1 ← notification.set_active st s n badge
        if b = true then ok (s1, a)
        else do
          let i2 ← obj.Tcb.state st i s1
          if i2 = sched.TS_RUNNING_VM then notification.kick_guest st ar s1 a i else ok (s1, a))
        ⦃ s' _ => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
      refine WP.spec_bind sa fun s1 h1 => ?_
      refine sig_if _ _ _ _ (fun _ => (WP.spec_ok _).2 h1) (fun _ => ?_)
      step with obj.Tcb.state.spec
      refine sig_if _ _ _ _ (fun _ => ?_) (fun _ => (WP.spec_ok _).2 h1)
      refine WP.spec_mono (notification.kick_guest.same hA s1 a i) fun r hr => ?_
      obtain ⟨s', a'⟩ := r
      simp only at hr
      subst hr
      exact h1
    by_cases hb : b = true
    · rw [if_pos hb, if_pos hb]
      refine WP.spec_bind sa fun s1 h1 => ?_
      rw [if_pos hb]
      exact (WP.spec_ok _).2 h1
    rw [if_neg hb]
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
    · -- not receiving: (#63 / #85) the `RunningVM` completion, else active (and kicked)
      rw [if_neg hb]
      refine sig_if _ _ _ _ (fun hvm => ?_) (fun _ => OLD)
      refine WP.spec_bind (vcpu.signal_completes.blk s i) fun b1 hb1 => ?_
      refine sig_if _ _ _ _ (fun hb1t => ?_) (fun _ => OLD)
      have hvmS : L.mem s (stA i) = sched.TS_RUNNING_VM := by rw [← ei1]; exact hvm
      refine WP.spec_bind (vcpu.report.blk hA s a i badge hI hiT hvmS (hb1 hb1t) hU (hbuf i hiT)) ?_
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


/-! ## (int6) The IPC-buffer placement and the words `lookup_ipc_buffer` reads -/

/-- A TCB's `IPC_BUFFER` field (TCB+3512). -/
def ibWordA (t : U64) : U64 := core.num.U64.wrapping_add t 3512#u64
/-- A TCB's IPC-buffer cap slot (its first word; the second is at +8). -/
def sbWordA (t : U64) : U64 :=
  core.num.U64.wrapping_add t (core.num.U64.wrapping_mul layout.tcb.SLOT_BUFFER layout.cte.SIZE)

/-- The three words `lookup_ipc_buffer` reads of a TCB `t` (its `IPC_BUFFER`
field, its buffer cap slot's two words) are the same at `s'` as at `s`. -/
def IbSame (s s' : S) (t : U64) : Prop :=
  L.mem s' (ibWordA t) = L.mem s (ibWordA t) ∧ L.mem s' (sbWordA t) = L.mem s (sbWordA t) ∧
    L.mem s' (core.num.U64.wrapping_add (sbWordA t) 8#u64) = L.mem s (core.num.U64.wrapping_add (sbWordA t) 8#u64)

/-- **The buffer-lookup frame**: the key-space base kept and `IbSame` for
every TCB of `T` (what `timer::fire`'s loop keeps, `IbKeep`). -/
def IbFr (T : Set U64) (s s' : S) : Prop := L.ksb s' = L.ksb s ∧ ∀ t ∈ T, IbSame (L := L) s s' t

theorem IbFr.refl (s : S) : IbFr (L := L) T s s := ⟨rfl, fun _ _ => ⟨rfl, rfl, rfl⟩⟩

theorem IbFr.trans {s₁ s₂ s₃ : S} (h₁ : IbFr (L := L) T s₁ s₂) (h₂ : IbFr (L := L) T s₂ s₃) :
    IbFr (L := L) T s₁ s₃ :=
  ⟨h₂.1.trans h₁.1, fun t ht => ⟨(h₂.2 t ht).1.trans (h₁.2 t ht).1, (h₂.2 t ht).2.1.trans (h₁.2 t ht).2.1,
    (h₂.2 t ht).2.2.trans (h₁.2 t ht).2.2⟩⟩

theorem sbWordA_eq (t : U64) : sbWordA t = core.num.U64.wrapping_add t 64#u64 := by
  apply UScalar.eq_of_val_eq
  unfold sbWordA layout.tcb.SLOT_BUFFER layout.cte.SIZE
  simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]

theorem sbWordA8_eq (t : U64) :
    core.num.U64.wrapping_add (sbWordA t) 8#u64 = core.num.U64.wrapping_add t 72#u64 := by
  apply UScalar.eq_of_val_eq
  rw [sbWordA_eq]
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
  try omega

/-- A `KeepT0` frame (a thread's state change) keeps the buffer-lookup words. -/
theorem IbFr.of_keepT {Cs Rp Scs Nt : Set U64} {t : U64} {s s' : S}
    (k : KeepT0 st T Cs Rp Scs Nt t s s') : IbFr (L := L) T s s' := by
  refine ⟨k.ksb, fun y hy => ⟨?_, ?_, ?_⟩⟩
  · exact k.fld y hy _ (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)
  · rw [sbWordA_eq]; exact k.fld y hy _ (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)
  · rw [sbWordA8_eq]; exact k.fld y hy _ (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)

theorem ib_eq_of_spec {α : Type _} {m : Result α} {y : α} (h : m ⦃ r => r = y ⦄) : m = ok y := by
  revert h; cases m <;> simp [WP.spec_vis, WP.spec_div, WP.spec_ok]

theorem ipc_buffer_word (s : S) (t : obj.Tcb) : obj.Tcb.ipc_buffer st t s = ok (L.mem s (ibWordA t)) := by
  apply ib_eq_of_spec; unfold obj.Tcb.ipc_buffer; step*; simp_all [ibWordA]

/-- `lookup_ipc_buffer` reads only the three `IbSame` words. -/
theorem lookup_ipc_buffer_same {s s' : S} {t : U64} (h : IbSame (L := L) s s' t) :
    msg.lookup_ipc_buffer st s' true t = msg.lookup_ipc_buffer st s true t := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold msg.lookup_ipc_buffer
  rw [ipc_buffer_word, ipc_buffer_word, h1]
  have hs : obj.Tcb.slot t layout.tcb.SLOT_BUFFER = ok (sbWordA t) := by simp [obj.Tcb.slot, lift, sbWordA]
  rw [hs]; simp only [bind_ok]
  have hc : obj.Slot.cap st (sbWordA t) s' = obj.Slot.cap st (sbWordA t) s := by
    unfold obj.Slot.cap; rw [L.read_pair_eq, L.read_pair_eq, h2, h3]
  rw [hc]

/-- **The IPC-buffer placement at `s`** (int6): the user words `U` are
`UsrW` words and every TCB's IPC buffer is in `U` (`BufOK`); what
`send_signal` needs since #80 / #85. -/
def BufAt (st : machine.Store S) [L : LawfulStore st] (T Cs : Set U64) (H : Heap) (Sg Scs : Set U64) (Z : U64 → Nat)
    (U : Set U64) (s : S) : Prop :=
  (∀ b ∈ U, UsrW st T Cs H Sg Scs Z s b) ∧ ∀ y ∈ T, msg.lookup_ipc_buffer st s true y ⦃ b => BufOK U b ⦄

/-- `BufAt` along the buffer-lookup frame. -/
theorem BufAt.of_fr {U : Set U64} {s s' : S} (h : BufAt st T Cs H Sg Scs Z U s) (f : IbFr (L := L) T s s') :
    BufAt st T Cs H Sg Scs Z U s' :=
  ⟨fun b hb => (h.1 b hb).ksb f.1, fun y hy => by rw [lookup_ipc_buffer_same (f.2 y hy)]; exact h.2 y hy⟩

/-- `BufAt` from P1's `UserOK` and a buffer fact (`XferHyps.buf`). -/
theorem BufAt.of_user {U : Set U64} {s : S} (hU : UserOK st T Cs Ω H U s) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hb : ∀ y ∈ T, msg.lookup_ipc_buffer st s true y ⦃ b => BufOK U b ⦄) : BufAt st T Cs H Sg Scs Z U s :=
  ⟨hU.usrW h, hb⟩

/-- **[deferred, int6 → par/a6f: discharged by `ibKeep_holds`] The steps of
`timer::fire`'s loop keep the buffer-lookup frame** (`IbFr`): `timer.remove`
of a TCB, `send_signal` of a notification of `Nt` (with the placement
`send_signal.tinv` needs), and the current node's `REPROGRAM` write. A P1
lemma (as `TmoXG`), not a premise of any top. -/
def IbKeep (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A) : Prop :=
  ∀ (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac U : Set U64),
    (∀ (s : S) (t : U64), TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s → t ∈ T →
      timer.remove st s t ⦃ s' => IbFr (L := L) T s s' ⦄) ∧
    (∀ (s : S) (a : A) (n bd : U64), TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s → n ∈ Nt → H n = some .ntfn →
      BufAt st T Cs H Sg Scs Z U s → notification.send_signal st ar s a n bd ⦃ s' _ => IbFr (L := L) T s s' ⦄) ∧
    (∀ (s : S) (v : U64), TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s →
      IbFr (L := L) T s (L.wr s (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) v))


/-! ## Binding a notification to a TCB (`BOUND_TCB` / `BOUND_NTFN` writes) -/

theorem obj.Ntfn.set_bound_tcb.wr (s : S) (n : obj.Ntfn) (v : U64) :
    obj.Ntfn.set_bound_tcb st n s v ⦃ s' => s' = L.wr s (ntfnBtA n) v ⦄ := by
  unfold obj.Ntfn.set_bound_tcb; step*; simp_all [ntfnBtA]
theorem obj.Tcb.set_bound_ntfn.wr (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_bound_ntfn st t s v ⦃ s' => s' = L.wr s (boundA t) v ⦄ := by
  unfold obj.Tcb.set_bound_ntfn; step*; simp_all [boundA]

/-- A write of a null or a TCB to a notification's `BOUND_TCB` word. -/
theorem ntbt_all {s : S} {n v : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hn : n ∈ Nt) (hv : Tz T v) :
    BlkOKM st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s (ntfnBtA n) v) := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hO := hX.1
  have hP := hO.ntP n hn
  have av := ntfnBtA_val hP
  have hm : ntfnBtA n ∈ Ω := hSg.sub _ (hO.ntB n hn).2
  obtain ⟨h1, hB1, hX1, hS1, hSg1, -⟩ := link_allTM (w := v) h0 hB hX.m hS hSg hm
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
theorem bnd_all {s : S} {t v : U64} (h : BlkOKM st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T)
    (hv : v ≠ 0#u64 → v ∈ Nt) : BlkOKM st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s (boundA t) v) := by
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
    XInvM.keep' hX (fun r hr => ⟨om _ (hrΩ r hr).1, om _ (hrΩ r hr).2.1, om _ (hrΩ r hr).2.2⟩)
      (fun c hc => ⟨om _ (hcΩ c hc).1, om _ (hcΩ c hc).2.1⟩) hsc hrp hst (by rw [ecs]; exact hX.2.2.cur)
      (fun c hc => om _ (hSg.sub _ (hX.1.repW c hc))) (fun y hy hb => ?_)
      (fun n hn => om _ (hSg.sub _ (hX.1.ntW n hn)))
      (hX.tn (TmFr.wr hT h0.nodes hX.1 ha (notTmW_field (K := 3368#u64) hT h0.nodes
        (fun n hn => h0.omega _ (hSg.sub _ (hX.1.ntB n hn).2)) ht (by simp) (by simp))))
      (fun c hc => om _ (hSg.sub _ (hX.1.snW c hc)))
      (hX.2.2.yt.keep (fun c hc => om _ (hcΩ c hc).1) (fun y hy => fk y hy _ (by simp) (by simp) (fun _ => by simp))
        (fun c hc => om _ (hSg.sub _ (hX.1.syW c hc)))) (fun c hc => om _ (hcΩ c hc).2.2.1) ei,
    SCsOK.fieldO (K := 3368#u64) h0 hS hX.1 ht (by simp) (by simp) (by simp),
    ⟨hSg.sub, fun b hb => by rw [L.ksb_wr]; exact hSg.ks b hb, fun o h1 h2 => by rw [L.ksb_wr]; exact hSg.ksΩ o h1 h2⟩⟩
  · rw [ea] at haT ⊢; exact ⟨haT, hB.act haT⟩
  · rw [ea] at h1; rw [ec]; exact ⟨h0.curT, hB.resume h1⟩
  · by_cases e : y = t
    · subst e; rw [L.mem_wr_same ha] at hb ⊢; exact hv hb
    · have k : L.mem (L.wr s (boundA t) v) (boundA y) = L.mem s (boundA y) :=
        fk y hy _ (by simp) (by simp) (fun e' => absurd e' e)
      rw [k] at hb ⊢; exact hX.2.2.bnd y hy hb

/-- **Unbinding a TCB and the notification bound to it** (the notification's
`BOUND_TCB` word, then the TCB's `BOUND_NTFN` word, both cleared). -/
theorem unbind_pair {s : S} {t n : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T) (hn : n ∈ Nt)
    (hb : L.mem s (boundA t) = n) (hnb : L.mem s (ntfnBtA n) = t) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr (L.wr s (ntfnBtA n) 0#u64) (boundA t) 0#u64) :=
  (bnd_all (ntbt_all h hn Tz.zero) ht fun h0 => absurd rfl h0).x
    (BndS.pairTN h.2.2.1.2.2.toScExtra0 h.1.choose_spec.choose_spec h.2.2.1.1 h.2.2.2.2.sub ht hn
      (Or.inr ⟨rfl, rfl, hb, hnb⟩))

/-- seL4 `bindNotification`. -/
theorem notification.bind_notification.blk (s : S) (t n : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ht : t ∈ T) (hn : n ∈ Nt) (h0t : L.mem s (boundA t) = 0#u64) (h0n : L.mem s (ntfnBtA n) = 0#u64) :
    notification.bind_notification st s t n ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  unfold notification.bind_notification
  refine WP.spec_bind (obj.Ntfn.set_bound_tcb.wr s n t) fun s1 e1 => ?_
  subst e1
  refine WP.spec_mono (obj.Tcb.set_bound_ntfn.wr _ t n) fun s2 e2 => ?_
  subst e2
  exact (bnd_all (ntbt_all h hn (Tz.of_mem ht)) ht fun _ => hn).x
    (BndS.pairTN h.2.2.1.2.2.toScExtra0 h.1.choose_spec.choose_spec h.2.2.1.1 h.2.2.2.2.sub ht hn (Or.inl ⟨rfl, rfl, h0t, h0n⟩))

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
    have tb := h.2.2.1.2.2.bs.tb t ht hi0
    rw [← ei] at tb
    exact unbind_pair h ht hin ei.symm tb
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
    have hi0 : L.mem s (ntfnBtA n) ≠ 0#u64 := fun e0 => absurd (by simp [ei, e0]) hb
    have nt := h.2.2.1.2.2.bs.nt n hn hi0
    rw [← ei] at nt
    exact unbind_pair h hiT hn nt ei.symm

theorem notification.bind_notification.tinv (s : S) (t n : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ht : t ∈ T) (hn : n ∈ Nt) (h0t : L.mem s (boundA t) = 0#u64) (h0n : L.mem s (ntfnBtA n) = 0#u64) :
    notification.bind_notification st s t n ⦃ s' => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ :=
  WP.spec_mono (notification.bind_notification.blk s t n h ht hn h0t h0n) fun _ h' => h'.tinv
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
