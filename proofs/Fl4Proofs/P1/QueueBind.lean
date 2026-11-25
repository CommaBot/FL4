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
    {d : U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T Ac s)
    (hX : XInvW st T Cs Ω Sg Rp Scs Nt Z d s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s)
    (hk : L.ksb s' = L.ksb s) (hc : L.cpu s' = L.cpu s) (hm : ∀ b, Aligned b → L.mem s' b = L.mem s b) :
    SchedQueuesInvX st T Cs Ω H X s' Q R ∧ BoundInv st T Ac s' ∧ XInvW st T Cs Ω Sg Rp Scs Nt Z d s' ∧
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
      fun y hy => fa y hy _ (by simp) (by simp), ?_, fun y hy => fa y hy _ (by simp) (by simp)⟩
    rotate_right
    · unfold LawfulStore.idleW; rw [hc, nodeAt_of_ksb hk]
      exact hm _ (nodeAt_aligned hN (by rw [idle8]; omega) (by rw [idle8]))
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
    donate_pair h0 hB hX.x0 hX.2.2.tsc.x hX.2.2.aff ht0 hS hSg ht hsc hsc0 hnb hcore hdisj hsA
      (fun e => hB.idle (by rw [e]; exact ht0))
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
    (by rw [iq2]; exact htr) hc' hsc (fun _ => by rw [sc2, ecpu])) ?_
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

theorem cur_wr_field {s : S} {t K v : U64} (hN : NodePlaced st T s (L.cpu s)) (ht : t ∈ T) (hta : TcbAddr t)
    (hK : K.val < 4096) (hK8 : K.val % 8 = 0) :
    L.curW (L.wr s (core.num.U64.wrapping_add t K) v) = L.curW s := by
  unfold LawfulStore.curW
  simp only [LawfulStore.cpu_wr, nodeAt_wr]
  exact L.mem_wr_ne (field_aligned hta hK hK8) (nodeAt_aligned hN (by rw [curth0]; omega) (by rw [curth0]))
    (fun e => node_ne_field hN (by rw [curth0]; omega) ht hta hK (UScalar.eq_of_val_eq e).symm)

/-- The scheduling half of `thread_control_sched` after the fault-handler
install: `MCP`, priority, then binding the SC or unbinding the thread's SC.
`s0` is the state the caller's facts are about; `s1` keeps what `PFr`
keeps, the current thread, and drops release flags only. -/
theorem tcs_tail {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s0 s1 : S) (a1 : A)
    (target : obj.Tcb) (mcp prio : U64) (sc : obj.Sc) (flags : U64)
    (h1 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1) (ht : target ∈ T) (pf : PFr st T Sg s0 s1)
    (ec : L.curW s1 = L.curW s0)
    (hrel : (L.mem s1 (inqA target) &&& sched.Q_RELEASE) ≠ 0#u64 → (L.mem s0 (inqA target) &&& sched.Q_RELEASE) ≠ 0#u64)
    (hprio : (flags &&& tcb.SCHED_UPDATE_PRIO) ≠ 0#u64 → prio.val < 256 ∧ (target = L.curW s0 →
      (L.mem s0 (inqA target) &&& sched.Q_RELEASE) = 0#u64 ∧ L.mem s0 (scA target) ≠ 0#u64 ∧
        L.mem s0 (scA target) ∈ Ac))
    (hbind : (flags &&& tcb.SCHED_UPDATE_SC) ≠ 0#u64 → sc ≠ 0#u64 → sc ∈ Scs ∧ L.mem s0 (scA target) = 0#u64 ∧
      L.mem s0 (scTcbA sc) = 0#u64 ∧ (BlockedR (L.mem s0 (stA target)) → sc ∈ Ac))
    (hunb : (flags &&& tcb.SCHED_UPDATE_SC) ≠ 0#u64 → sc = 0#u64 → L.actionW s0 ≠ target ∧ L.idleW s0 ≠ target) :
    (do
      let i1 ← lift (flags &&& tcb.SCHED_UPDATE_MCP)
      let s3 ←
        if i1 != 0#u64
        then obj.Tcb.set_mcp st target s1 mcp
        else ok s1
      let i2 ← lift (flags &&& tcb.SCHED_UPDATE_PRIO)
      let s4 ←
        if i2 != 0#u64
        then sched.set_priority st s3 target prio
        else ok s3
      let i3 ← lift (flags &&& tcb.SCHED_UPDATE_SC)
      if i3 != 0#u64
      then
        let b ← obj.Sc.is_null sc
        if b
        then
          let i4 ← obj.Tcb.sc st target s4
          let b1 ← obj.Sc.is_null i4
          if b1
          then ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s4, a1)
          else
            let s5 ← schedcontext.unbind_tcb st s4 i4
            ok (core.result.Result.Ok (), s5, a1)
        else
          let (s5, a2) ← schedcontext.bind_tcb st ar s4 a1 sc target
          ok (core.result.Result.Ok (), s5, a2)
      else ok (core.result.Result.Ok (), s4, a1)) ⦃ r => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ⦄ := by
  have hT := h1.1.choose_spec.choose_spec.tcbs
  have hta := hT target ht
  simp only [lift, Aeneas.Std.bind_ok]
  -- `MCP`
  refine WP.spec_bind (Pₘ := fun s3 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s3 ∧ PFr st T Sg s0 s3 ∧
      L.curW s3 = L.curW s0 ∧
      ((L.mem s3 (inqA target) &&& sched.Q_RELEASE) ≠ 0#u64 → (L.mem s0 (inqA target) &&& sched.Q_RELEASE) ≠ 0#u64))
    ?_ ?_
  · split
    · refine WP.spec_mono (obj.Tcb.set_mcp.wr s1 target mcp) fun s' e => ?_
      subst e
      obtain ⟨Q1, R1, h1'⟩ := h1.1
      have hN := h1'.nodes _ h1'.cur
      refine ⟨(plainW_all (K := 3440#u64) (v := mcp) h1 ht (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).1,
        pf.trans (PFr.of_fr (fr_field (K := 3440#u64) h1' h1.2.2.2.2 ht (by simp) (by simp) (by simp))
          (Or.inl (act_wr_field hN ht hta rfl (by simp) (by simp)))),
        (cur_wr_field hN ht hta (by simp) (by simp)).trans ec, fun hf => hrel ?_⟩
      rwa [inqA_eq, L.mem_wr_ne (field_aligned (K := 3440#u64) hta (by simp) (by simp))
        (field_aligned (K := 3592#u64) hta (by simp) (by simp))
        (fun e => field_ne (K1 := 3440#u64) (K2 := 3592#u64) hta hta (by simp) (by simp) (fun _ => by simp)
          (UScalar.eq_of_val_eq e)), ← inqA_eq] at hf
    · exact (WP.spec_ok _).2 ⟨h1, pf, ec, hrel⟩
  rintro s3 ⟨h3, pf3, ec3, hrel3⟩
  -- priority
  refine WP.spec_bind (Pₘ := fun s4 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s4 ∧ PFr st T Sg s0 s4) ?_ ?_
  · split
    · rename_i hf
      obtain ⟨hv, hc⟩ := hprio (by simpa using hf)
      have hcur3 : target = L.mem s3 (L.nodeAt s3 (L.cpu s3) layout.node.CUR_THREAD) → target = L.curW s0 :=
        fun e => e.trans ec3
      refine WP.spec_mono (sched.set_priority.blk s3 target prio h3 ht hv
        (fun e => by
          by_contra hn; exact hrel3 hn (hc (hcur3 e)).1)
        (fun e => by rw [pf3.sc target ht]; exact (hc (hcur3 e)).2.1)
        (fun e => by rw [pf3.sc target ht]; exact (hc (hcur3 e)).2.2)) fun s4 hh => ⟨hh.1, pf3.trans hh.2.2⟩
    · exact (WP.spec_ok _).2 ⟨h3, pf3⟩
  rintro s4 ⟨h4, pf4⟩
  -- the SC
  split
  · rename_i hfs
    have hfs' : (flags &&& tcb.SCHED_UPDATE_SC) ≠ 0#u64 := by simpa using hfs
    step with obj.Sc.is_null.spec as ⟨b, eb⟩
    split
    · rename_i hb
      have hsc0 : sc = 0#u64 := by simpa [eb] using hb
      obtain ⟨hna, hid⟩ := hunb hfs' hsc0
      step with obj.Tcb.sc.spec as ⟨i4, ei4⟩
      step with obj.Sc.is_null.spec as ⟨b1, eb1⟩
      split
      · exact (WP.spec_ok _).2 h4
      · rename_i hb1
        have hi0 : i4 ≠ 0#u64 := fun e => hb1 (by rw [eb1, e]; rfl)
        obtain ⟨hiS, hit, -⟩ := h4.2.2.1.2.2.bound target ht (by rw [← ei4]; exact hi0)
        rw [← ei4] at hiS hit
        have hT4 := h4.1.choose_spec.choose_spec.tcbs
        refine WP.spec_bind (schedcontext.unbind_tcb.blk s4 i4 h4 hiS hi0 (fun _ => ?_) (fun _ => ?_))
          fun s5 hh => (WP.spec_ok _).2 hh.1
        · rw [hit]
          rcases pf4.act with e | e
          · rw [e]; exact hna
          · rw [e]; exact fun e' => notT_small hT4 (by simp) (e' ▸ ht)
        · rw [hit, pf4.idle]; exact hid
    · rename_i hb
      have hsc0 : sc ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
      obtain ⟨hsc, ht0, hc0, hbA⟩ := hbind hfs' hsc0
      refine WP.spec_bind (schedcontext.bind_tcb.blk hA s4 a1 sc target h4 ht hsc hsc0
        (by rw [pf4.sc target ht]; exact ht0)
        (by rw [pf4.sig _ (h4.2.2.1.1.fixW sc hsc).1]; exact hc0)
        (fun hb' => hbA (by rw [← pf4.st target ht]; exact hb'))) fun r hr => ?_
      obtain ⟨s5, a2⟩ := r
      exact (WP.spec_ok _).2 hr
  · exact (WP.spec_ok _).2 h4

/-- seL4 `TCB_SetSchedParams`'s scheduling step (`thread_control_sched`):
the fault handler is installed (`install_tcb_cap`, a hypothesis: it keeps
the invariants and the scheduling words), then `MCP`, priority and SC. -/
theorem tcb.thread_control_sched.blk {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (target : obj.Tcb) (slot : obj.Slot) (fh : capability.Cap × obj.Slot) (mcp prio : U64) (sc : obj.Sc)
    (flags : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : target ∈ T)
    (hinst : tcb.install_tcb_cap st ar s a target slot layout.tcb.SLOT_FAULT_HANDLER fh.1 fh.2 ⦃ r =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ∧ PFr st T Sg s r.2.1 ∧ L.curW r.2.1 = L.curW s ∧
      ((L.mem r.2.1 (inqA target) &&& sched.Q_RELEASE) ≠ 0#u64 →
        (L.mem s (inqA target) &&& sched.Q_RELEASE) ≠ 0#u64) ⦄)
    (hprio : (flags &&& tcb.SCHED_UPDATE_PRIO) ≠ 0#u64 → prio.val < 256 ∧ (target = L.curW s →
      (L.mem s (inqA target) &&& sched.Q_RELEASE) = 0#u64 ∧ L.mem s (scA target) ≠ 0#u64 ∧
        L.mem s (scA target) ∈ Ac))
    (hbind : (flags &&& tcb.SCHED_UPDATE_SC) ≠ 0#u64 → sc ≠ 0#u64 → sc ∈ Scs ∧ L.mem s (scA target) = 0#u64 ∧
      L.mem s (scTcbA sc) = 0#u64 ∧ (BlockedR (L.mem s (stA target)) → sc ∈ Ac))
    (hunb : (flags &&& tcb.SCHED_UPDATE_SC) ≠ 0#u64 → sc = 0#u64 → L.actionW s ≠ target ∧ L.idleW s ≠ target) :
    tcb.thread_control_sched st ar s a target slot fh mcp prio sc flags ⦃ r =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ⦄ := by
  unfold tcb.thread_control_sched
  simp only [lift, Aeneas.Std.bind_ok]
  split
  · obtain ⟨c, sl⟩ := fh
    refine WP.spec_bind hinst ?_
    rintro ⟨r, s2, a1⟩ ⟨h2, pf2, ec2, hrel2⟩
    simp only [uncurry_apply_pair] at h2 pf2 ec2 hrel2 ⊢
    cases r with
    | Ok u =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Aeneas.Std.bind_ok]
      have := tcs_tail hA s s2 a1 target mcp prio sc flags h2 ht pf2 ec2 hrel2 hprio hbind hunb
      simp only [lift, Aeneas.Std.bind_ok] at this
      exact this
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        Aeneas.Std.bind_ok, WP.spec_ok]
      exact WP.spec_bind (Pₘ := fun _ => True) (WP.spec_bind (Pₘ := fun _ => True) ((WP.spec_ok _).2 trivial)
        fun _ _ => (WP.spec_ok _).2 trivial) fun _ _ => (WP.spec_ok _).2 h2
  · have := tcs_tail hA s s a target mcp prio sc flags h ht (PFr.refl _ _) rfl id hprio hbind hunb
    simp only [lift, Aeneas.Std.bind_ok] at this
    exact this

end

end Fl4Proofs.P1
