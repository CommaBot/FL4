/-
P1: the pieces of the invocations the P3 side composes.

* `sched.set_thread_state.restart_blk`, `tcb.restart_caller.blk`: the
  caller's restart (seL4 `setThreadState Restart` on the current thread)
  keeps `BlkOK`, with its footprint and `KeepT`; `restart_ok`/`restart_hB`
  give it in the `= ok s1` form `SetPrioHyp`'s `hB` takes.
* `smp.migrate_tcb.kw`, `schedcontext.bind_tcb.blkF`: `bind_tcb` keeps
  `BlkOK` with its footprint (`Foot`, writes inside `KW`).
* The SchedContext invocations after their decode (restart, then
  `bind_tcb` / `unbind_tcb` / `unbind_all_tcbs`, `unbind_ntfn`,
  `unbind_reply`), with `BlkOK` and `Foot`.
-/
import Fl4Proofs.P1.QueueFootS
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {Es : Set U64}

/-! ## The caller's restart -/

/-- seL4 `setThreadState Restart` on a thread that is not blocked on an
endpoint, a notification or a reply (e.g. the current thread at a system
call): `BlkOK` is kept, with the footprint of `set_thread_state` and
`KeepT` (everything but the thread's state and the scheduler action, which
may become `CHOOSE_NEW`). -/
theorem sched.set_thread_state.restart_blk (s : S) (t : obj.Tcb) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ht : t ∈ T) (hnb : ¬ Blocked (L.mem s (stA t))) (hnr : L.mem s (stA t) ≠ sched.TS_BLOCKED_ON_REPLY) :
    sched.set_thread_state st s t sched.TS_RESTART ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      Foot st T Cs Sg Scs Z Es s s' ∧ L.mem s' (stA t) = sched.TS_RESTART ∧ KeepT st T Cs Rp Scs Nt t s s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hnoref : ∀ r ∈ Rp, L.mem s (rTcbA r) ≠ t :=
    hX.noref (h0.tcbs t ht) hnr (fun e => hnb (Or.inr (Or.inl e)))
  refine WP.spec_mono (WP.spec_and (sts_all s t _ Q R h0 hB hX hS hSg ht not_blocked_restart restart_ne
    (Or.inr hnb) hnoref ⟨fun _ _ _ _ _ => runnable_restart, fun _ _ _ => runnable_restart, fun _ => runnable_restart⟩)
    (sched.set_thread_state.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s t _ h0 ht)) ?_
  rintro s' ⟨⟨h1, hB1, hX1, hS1, hSg1, e1, k1⟩, f1⟩
  exact ⟨⟨⟨Q, R, h1.congrX empty_congr⟩, hB1, hX1, hS1, hSg1⟩, f1, e1, k1⟩

/-- `restart_caller`: `set_thread_state Restart` on the current thread. -/
theorem tcb.restart_caller.blk (s : S) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hnb : ¬ Blocked (L.mem s (stA (L.curW s)))) (hnr : L.mem s (stA (L.curW s)) ≠ sched.TS_BLOCKED_ON_REPLY) :
    tcb.restart_caller st s ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      Foot st T Cs Sg Scs Z Es s s' ∧ L.mem s' (stA (L.curW s)) = sched.TS_RESTART ∧
      KeepT st T Cs Rp Scs Nt (L.curW s) s s' ⦄ := by
  unfold tcb.restart_caller
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e
  exact sched.set_thread_state.restart_blk s _ h h.1.choose_spec.choose_spec.curT hnb hnr

/-- The restart in the `= ok s1` form: `BlkOK`, the footprint, and the words
the current-thread conditions of the later steps read (the current thread
and SC, every thread's queue flags and SC). -/
theorem sched.set_thread_state.restart_ok {s s1 : S} {t : obj.Tcb} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ht : t ∈ T) (hnb : ¬ Blocked (L.mem s (stA t))) (hnr : L.mem s (stA t) ≠ sched.TS_BLOCKED_ON_REPLY)
    (e : sched.set_thread_state st s t sched.TS_RESTART = ok s1) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1 ∧ Foot st T Cs Sg Scs Z Es s s1 ∧
      L.mem s1 (stA t) = sched.TS_RESTART ∧ L.ksb s1 = L.ksb s ∧ L.curW s1 = L.curW s ∧ L.cscW s1 = L.cscW s ∧
      L.idleW s1 = L.idleW s ∧ (L.actionW s1 = L.actionW s ∨ L.actionW s1 = 1#u64) ∧
      (∀ y ∈ T, L.mem s1 (inqA y) = L.mem s (inqA y) ∧ L.mem s1 (scA y) = L.mem s (scA y)) ∧
      (∀ c ∈ Scs, L.mem s1 (scTcbA c) = L.mem s (scTcbA c)) := by
  have hh := sched.set_thread_state.restart_blk (Es := Es) s t h ht hnb hnr
  rw [e, WP.spec_ok] at hh
  obtain ⟨hb, f, est, k⟩ := hh
  exact ⟨hb, f, est, k.ksb, k.curW, k.cscW, k.idleW, k.act, fun y hy => ⟨k.inqf hy, k.scf hy⟩,
    fun c hc => (k.fix c hc).1⟩

/-- The shape of the P3 side's `hB` (`SetPrioHyp`): after the current
thread's restart, `BlkOK` and the current-thread conditions of
`set_priority`, from those conditions before. -/
theorem restart_hB (s : S) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hnb : ¬ Blocked (L.mem s (stA (L.curW s)))) (hnr : L.mem s (stA (L.curW s)) ≠ sched.TS_BLOCKED_ON_REPLY)
    (hcur : (L.mem s (inqA (L.curW s)) &&& sched.Q_RELEASE) = 0#u64 ∧ L.mem s (scA (L.curW s)) ≠ 0#u64 ∧
      L.mem s (scA (L.curW s)) ∈ Ac) :
    ∀ s1, sched.set_thread_state st s (L.curW s) sched.TS_RESTART = ok s1 →
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1 ∧ Foot st T Cs Sg Scs Z Es s s1 ∧ L.ksb s1 = L.ksb s ∧
      ∀ t, t = L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.CUR_THREAD) →
        (L.mem s1 (inqA t) &&& sched.Q_RELEASE) = 0#u64 ∧ L.mem s1 (scA t) ≠ 0#u64 ∧ L.mem s1 (scA t) ∈ Ac := by
  intro s1 e
  have hc : L.curW s ∈ T := h.1.choose_spec.choose_spec.curT
  obtain ⟨hb, f, -, hk, hcw, -, -, -, hy, -⟩ := sched.set_thread_state.restart_ok (Es := Es) h hc hnb hnr e
  refine ⟨hb, f, hk, fun t et => ?_⟩
  have et' : t = L.curW s := et.trans hcw
  subst et'
  rw [(hy _ hc).1, (hy _ hc).2]
  exact hcur

/-! ## `bind_tcb` with its footprint -/

/-- `migrate_tcb` writes the thread's affinity field and, when the thread
changes core, the debug-list words (`FootD`). -/
theorem smp.migrate_tcb.kw {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t cpu : U64) (hT : TcbPlaced T) (hN : ∀ c ∈ Cs, NodePlaced st T s c) (hD : DbgTz st T Cs s)
    (hc : L.mem s (affA t) ∈ Cs) (hcpu : cpu ∈ Cs) (ht : t ∈ T) :
    smp.migrate_tcb st ar s a t cpu ⦃ s' _ => FootD st T Cs Sg Scs Z Es s s' ⦄ :=
  WP.spec_mono (smp.migrate_tcb.frame hA s a t cpu hT hN hD hc hcpu ht) fun _ hr => by
    obtain ⟨w, -⟩ := hr
    exact w.mono fun b hb => hb.elim (fun e => Or.inl (by
      rw [e, affA_eq]; exact kw_field ht (by simp) (by simp) (by simp))) Or.inr

/-- **`bind_tcb` with its footprint**: `schedcontext.bind_tcb.blk` and the
words it writes (the thread's `SC` and affinity fields, the SC's `TCB` word,
its refills and the core's `REPROGRAM` word in the unblock check, then
`resume`, `enqueue` and `reschedule_required`). -/
theorem schedcontext.bind_tcb.blkF {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (sc t : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T) (hsc : sc ∈ Scs) (hsc0 : sc ≠ 0#u64)
    (ht0 : L.mem s (scA t) = 0#u64) (hc0 : L.mem s (scTcbA sc) = 0#u64)
    (hbA : BlockedR (L.mem s (stA t)) → sc ∈ Ac) :
    schedcontext.bind_tcb st ar s a sc t ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      FootD st T Cs Sg Scs Z Es s s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hT := h0.tcbs
  have hta := hT t ht
  have hO := hX.1
  have hm : scTcbA sc ∈ Ω := hSg.sub _ (hO.fixW sc hsc).1
  have ho := h0.omega _ hm
  have hal : Aligned (scTcbA sc) := by
    obtain ⟨hP, hz⟩ := hO.sc sc hsc
    have := (sc_lo hP hz).1
    unfold Aligned; rw [scTcbA_val hP hz]; omega
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
  have fw2 : Foot st T Cs Sg Scs Z Es s (L.wr (L.wr s (scA t) sc) (scTcbA sc) t) := by
    have f1 : Foot st T Cs Sg Scs Z Es s (L.wr s (scA t) sc) := by
      rw [scA_eq]; exact foot_field hT ht (by simp) (by simp) (by simp) (by simp)
    exact f1.trans (foot_wr hal (kw_sg (hO.fixW sc hsc).1))
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
  refine WP.spec_bind (WP.spec_and (migrate_tail hA s2 a sc t cpu Q R h2 hB2 hX2 hS2 hSg2 ht (by rw [iq2]; exact htq)
    (by rw [iq2]; exact htr) hc' hsc (fun _ => by rw [sc2, ecpu])) (smp.migrate_tcb.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) (Cs := Cs)
      hA s2 a t cpu h2.tcbs h2.nodes ⟨hX2.1.2.2.tm.dn, hX2.1.2.2.tm.dp, hX2.1.2.2.tm.dh⟩ (h2.aff t ht) hc' ht)) ?_
  rintro ⟨s3, a1⟩ ⟨⟨⟨⟨Q3, R3, h3⟩, hB3, hX3, hS3, hSg3⟩, -, -, -, sc3, -, ea3⟩, fw3⟩
  try simp only [WP.uncurry'_pair]
  rw [sc2] at sc3
  have fw3' : FootD st T Cs Sg Scs Z Es s s3 := fw2.d.trans fw3
  -- the sporadic unblock check
  step with sporadic.sc_sporadic.spec as ⟨b, eb⟩
  refine WP.spec_bind (Pₘ := fun s4 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s4 ∧ L.mem s4 (scA t) = sc ∧
      L.actionW s4 = L.actionW s ∧ FootD st T Cs Sg Scs Z Es s s4) ?_ ?_
  · have ok3 : (ok s3 : Result S) ⦃ s4 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s4 ∧ L.mem s4 (scA t) = sc ∧
        L.actionW s4 = L.actionW s ∧ FootD st T Cs Sg Scs Z Es s s4 ⦄ :=
      (WP.spec_ok _).2 ⟨⟨⟨Q3, R3, h3⟩, hB3, hX3, hS3, hSg3⟩, sc3, by rw [ea3, ea2], fw3'⟩
    split
    · step with sporadic.sc_active.val as ⟨b1, eb1⟩
      split
      · rename_i hb1
        step with sched.cur_sc.spec as ⟨c4, _⟩
        step with sc_ne.spec as ⟨b2⟩
        split
        · have hAc : sc ∈ Ac := (hS3.act sc hsc).2 (eb1 hb1)
          have hW : RefillsWF st s3 sc (Z sc) := hS3.wf hsc hAc
          have hSCin : SCin st s3 Ω sc (Z sc) := ⟨hW, hX3.1.scW sc hsc⟩
          have hN' := h3.nodes _ h3.cur
          have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
          have aR : Aligned (L.nodeA s3 layout.node.REPROGRAM) := nodeAt_aligned hN' (by rw [rp]; omega) (by rw [rp])
          have oR : Outside (L.nodeA s3 layout.node.REPROGRAM) sc (Z sc) :=
            hSCin.node_out h3.omega h3.cur hN' (by rw [rp]; omega) (by rw [rp])
          refine WP.spec_mono (WP.spec_and (sporadic.unblock_check.all s3 t sc h3 hB3 hX3 hS3 hSg3 ht sc3.symm hsc0
            hAc) (sporadic.unblock_check.fr hW ⟨aR, oR⟩)) fun s4 hh => ?_
          obtain ⟨⟨h4, hB4, hX4, hS4, hSg4, ea4, -, -, f4, -⟩, w4⟩ := hh
          have fw4 : Foot st T Cs Sg Scs Z Es s3 s4 := Foot.of w4 fun b hb => by
            rcases hb with hb | rfl
            · exact hb.kw hsc
            · exact kw_node h3.cur (by rw [rp]; omega) (by rw [rp]; omega)
          exact ⟨⟨⟨Q3, R3, h4⟩, hB4, hX4, hS4, hSg4⟩, by rw [scA_eq, f4 t ht _ (by simp) (by simp), ← scA_eq]; exact sc3,
            by rw [ea4, ea3, ea2], fw3'.trans fw4.d⟩
        · exact ok3
      · exact ok3
    · exact ok3
  rintro s4 ⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, sc4, ea4, fw4⟩
  -- resume
  have tc4 : L.mem s4 (scTcbA sc) = t := by
    have := (hX4.2.2.bound t ht (by rw [sc4]; exact hsc0)).2.1; rwa [sc4] at this
  have hres : sc ≠ 0#u64 → L.mem s4 (scTcbA sc) ≠ 0#u64 →
      L.mem s4 (scTcbA sc) ∈ T ∧ OutsideObjs st T Cs s4 (scCoreA sc) ∧ L.mem s4 (scCoreA sc) ∈ Cs ∧
        L.actionW s4 ≠ L.mem s4 (scTcbA sc) := fun _ _ => by
    rw [tc4]
    exact ⟨ht, h4.omega _ ((objs_omega hX4.1 hSg4.sub).2 sc hsc).2.1, hX4.2.2.core sc hsc,
      by rw [ea4]; exact hna⟩
  refine WP.spec_bind (WP.spec_and (schedcontext.resume.all hA s4 a1 sc Q4 R4 h4 hB4 hX4 hSg4 hS4 hres)
    (schedcontext.resume.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) hA s4 a1 sc Q4 R4 h4 hres)) ?_
  rintro ⟨s5, a2⟩ ⟨⟨Q5, R5, h5, hB5, hX5, hSg5, f5⟩, fw5⟩
  have hS5 := hS4.fr f5
  have fw5' : FootD st T Cs Sg Scs Z Es s s5 := fw4.trans fw5.d
  try simp only [WP.uncurry'_pair]
  -- enqueue if schedulable
  step with sched.is_schedulable.spec' as ⟨b3, eb3⟩
  split
  · rename_i hb3
    obtain ⟨hrun, hbd, hrl, hrm⟩ := eb3 hb3
    have hA5 : L.mem s5 (scA t) ∈ Ac := (hS5.act _ (hX5.2.2.bound t ht hbd).1).2 hrm
    refine WP.spec_bind (WP.spec_and (sched.enqueue.sch s5 t Q5 R5 h5 hB5 hSg5 ht (fun _ => hrl) (fun _ => hrun)
      (fun _ => hbd) (fun _ => hA5)) (sched.enqueue.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s5 t h5 ht)) ?_
    rintro s6 ⟨⟨⟨⟨Q6, R6, h6⟩, hB6, f6⟩, -, -, -⟩, fw6⟩
    refine WP.spec_bind (WP.spec_and (sched.reschedule_required.sch s6 Q6 R6 h6 hB6 (hSg5.fr f6))
      (sched.reschedule_required.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s6 h6)) ?_
    rintro s7 ⟨⟨⟨⟨Q7, R7, h7⟩, hB7, f7⟩, -, -, -⟩, fw7⟩
    exact (WP.spec_ok _).2 ⟨⟨⟨Q7, R7, h7⟩, hB7, (hX5.fr f6).fr f7, (hS5.fr f6).fr f7, (hSg5.fr f6).fr f7⟩,
      fw5'.trans (fw6.trans fw7).d⟩
  · exact (WP.spec_ok _).2 ⟨⟨⟨Q5, R5, h5⟩, hB5, hX5, hS5, hSg5⟩, fw5'⟩

/-! ## The SchedContext invocations (after their decode)

Each begins with the caller's restart (`ct`, runnable) and is stated in the
form the P3 decode theorems (`ScDecodeSc`) use. -/

theorem runnable_ok {v : U64} (h : Runnable v) : ¬ Blocked v ∧ v ≠ sched.TS_BLOCKED_ON_REPLY :=
  ⟨fun hb => not_runnable_of_blocked hb h, runnable_ne_reply h⟩

/-- An SC's bound thread is not the scheduler action after the restart, when
it was not before (the action may become `CHOOSE_NEW`). -/
theorem act_after_restart {s s1 : S} {c : U64} (hT : TcbPlaced T) (hcT : L.mem s (scTcbA c) ∈ T)
    (ha : L.actionW s ≠ L.mem s (scTcbA c)) (h1 : L.actionW s1 = L.actionW s ∨ L.actionW s1 = 1#u64)
    (hk : L.mem s1 (scTcbA c) = L.mem s (scTcbA c)) : L.actionW s1 ≠ L.mem s1 (scTcbA c) := by
  rw [hk]
  rcases h1 with e | e
  · rw [e]; exact ha
  · rw [e]; intro e'; exact notT_small hT (by rw [← e']; decide) hcT

/-- **SchedContext `Unbind`**: restart, `unbind_all_tcbs`, `unbind_ntfn`,
`unbind_reply`. -/
theorem sc_unbind.blkF {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (ct sc : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hct : ct ∈ T) (hr : Runnable (L.mem s (stA ct)))
    (hsc : sc ∈ Scs) (hsc0 : sc ≠ 0#u64)
    (hna : L.mem s (scTcbA sc) ≠ 0#u64 → L.actionW s ≠ L.mem s (scTcbA sc))
    (hidle : L.mem s (scTcbA sc) ≠ 0#u64 → L.idleW s ≠ L.mem s (scTcbA sc)) :
    (do
      let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
      let (s3, a2) ← schedcontext.unbind_all_tcbs st ar s2 a sc
      let s4 ← schedcontext.unbind_ntfn st s3 sc
      let s5 ← schedcontext.unbind_reply st s4 sc
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, a2)) ⦃ r s' _ =>
      r = .Ok () ∧ BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z ∅ s s' ∧ L.cscW s' = L.cscW s ⦄ := by
  have hT := h.1.choose_spec.choose_spec.tcbs
  have hyt := h.2.2.1.2.2.yt.1
  refine WP.spec_bind (sched.set_thread_state.restart_blk (Es := ∅) s ct h hct (runnable_ok hr).1
    (runnable_ok hr).2) ?_
  rintro s2 ⟨h2, f2, -, k2⟩
  have tc2 := (k2.fix sc hsc).1
  refine WP.spec_bind (schedcontext.unbind_all_tcbs.blk hA s2 a sc h2 hsc hsc0
    (fun hz => act_after_restart hT (hyt sc hsc (by rw [← tc2]; exact hz)) (hna (by rw [← tc2]; exact hz))
      k2.act tc2)
    (fun hz => by rw [k2.idleW, tc2]; exact hidle (by rw [← tc2]; exact hz))) ?_
  rintro ⟨s3, a2⟩ ⟨h3, f3, -, -, -, ec3⟩
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (schedcontext.unbind_ntfn.blk s3 sc h3 fun _ => hsc) ?_
  rintro s4 ⟨h4, f4, -, ec4, -⟩
  refine WP.spec_bind (schedcontext.unbind_reply.blk s4 sc sc h4 (fun _ => hsc) hsc) ?_
  rintro s5 ⟨h5, f5, k5, -⟩
  simp only [WP.spec_ok, WP.uncurry'_pair]
  exact ⟨by first | trivial | rfl, h5, f2.trans (f3.trans (f4.trans f5)), by rw [k5.2.2.1, ec4, ec3, k2.cscW]⟩

/-- **SchedContext `UnbindObject` (thread)**: restart, `unbind_tcb`. -/
theorem sc_unbind_tcb.blkF {A : Type _} (s : S) (a : A) (ct sc : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hct : ct ∈ T) (hr : Runnable (L.mem s (stA ct)))
    (hsc : sc ∈ Scs) (hsc0 : sc ≠ 0#u64)
    (hna : L.mem s (scTcbA sc) ≠ 0#u64 → L.actionW s ≠ L.mem s (scTcbA sc))
    (hidle : L.mem s (scTcbA sc) ≠ 0#u64 → L.idleW s ≠ L.mem s (scTcbA sc)) :
    (do
      let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
      let s3 ← schedcontext.unbind_tcb st s2 sc
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s3, a)) ⦃ r s' _ =>
      r = .Ok () ∧ BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z ∅ s s' ∧ L.cscW s' = L.cscW s ⦄ := by
  have hT := h.1.choose_spec.choose_spec.tcbs
  have hyt := h.2.2.1.2.2.yt.1
  refine WP.spec_bind (sched.set_thread_state.restart_blk (Es := ∅) s ct h hct (runnable_ok hr).1
    (runnable_ok hr).2) ?_
  rintro s2 ⟨h2, f2, -, k2⟩
  have tc2 := (k2.fix sc hsc).1
  refine WP.spec_bind (schedcontext.unbind_tcb.blk s2 sc h2 hsc hsc0
    (fun hz => act_after_restart hT (hyt sc hsc (by rw [← tc2]; exact hz)) (hna (by rw [← tc2]; exact hz))
      k2.act tc2)
    (fun hz => by rw [k2.idleW, tc2]; exact hidle (by rw [← tc2]; exact hz))) ?_
  rintro s3 ⟨h3, f3, -, -, -, ec3⟩
  simp only [WP.spec_ok]
  exact ⟨by first | trivial | rfl, h3, f2.trans f3, by rw [ec3, k2.cscW]⟩

/-- **SchedContext `UnbindObject` (notification)**: restart, `unbind_ntfn`. -/
theorem sc_unbind_ntfn.blkF {A : Type _} (s : S) (a : A) (ct sc : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hct : ct ∈ T) (hr : Runnable (L.mem s (stA ct)))
    (hsc : sc ∈ Scs) :
    (do
      let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
      let s3 ← schedcontext.unbind_ntfn st s2 sc
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s3, a)) ⦃ r s' _ =>
      r = .Ok () ∧ BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z ∅ s s' ∧ L.cscW s' = L.cscW s ⦄ := by
  refine WP.spec_bind (sched.set_thread_state.restart_blk (Es := ∅) s ct h hct (runnable_ok hr).1
    (runnable_ok hr).2) ?_
  rintro s2 ⟨h2, f2, -, k2⟩
  refine WP.spec_bind (schedcontext.unbind_ntfn.blk s2 sc h2 fun _ => hsc) ?_
  rintro s3 ⟨h3, f3, -, ec3, -⟩
  simp only [WP.spec_ok]
  exact ⟨by first | trivial | rfl, h3, f2.trans f3, by rw [ec3, k2.cscW]⟩

/-- **SchedContext `Bind` (thread)**: restart, `bind_tcb` of an SC bound to
no thread and a thread with no SC (`bind_tcb.blkF`'s conditions, before the
restart). -/
theorem sc_bind_tcb.blkF {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (ct sc t : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hct : ct ∈ T) (hr : Runnable (L.mem s (stA ct)))
    (ht : t ∈ T) (hsc : sc ∈ Scs) (hsc0 : sc ≠ 0#u64)
    (ht0 : L.mem s (scA t) = 0#u64) (hc0 : L.mem s (scTcbA sc) = 0#u64)
    (hbA : BlockedR (L.mem s (stA t)) → sc ∈ Ac) :
    (do
      let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
      let (s3, a2) ← schedcontext.bind_tcb st ar s2 a sc t
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s3, a2)) ⦃ r s' _ =>
      r = .Ok () ∧ BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ FootD st T Cs Sg Scs Z ∅ s s' ⦄ := by
  refine WP.spec_bind (sched.set_thread_state.restart_blk (Es := ∅) s ct h hct (runnable_ok hr).1
    (runnable_ok hr).2) ?_
  rintro s2 ⟨h2, f2, e2, k2⟩
  have hbA2 : BlockedR (L.mem s2 (stA t)) → sc ∈ Ac := by
    by_cases e : t = ct
    · subst e; rw [e2]
      rintro (hb | hb)
      · exact absurd hb not_blocked_restart
      · exact absurd hb restart_ne.1
    · rw [k2.stf ht e]; exact hbA
  refine WP.spec_bind (schedcontext.bind_tcb.blkF (Es := ∅) hA s2 a sc t h2 ht hsc hsc0 (by rw [k2.scf ht]; exact ht0)
    (by rw [(k2.fix sc hsc).1]; exact hc0) hbA2) ?_
  rintro ⟨s3, a2⟩ ⟨h3, f3⟩
  try simp only [WP.uncurry'_pair]
  exact (WP.spec_ok _).2 ⟨by first | trivial | rfl, h3, f2.d.trans f3⟩

/-! ## The endpoint and notification invocations (`decode_invocation`'s
`Endpoint` and `Notification` branches: restart, then `send_ipc` /
`send_signal`) -/

/-- `CanBlock` survives the thread's own restart. -/
theorem CanBlock.restart {s s1 : S} {t : U64} (hc : CanBlock st T Ac s t) (hT : TcbPlaced T)
    (k : KeepT st T Cs Rp Scs Nt t s s1) (e : L.mem s1 (stA t) = sched.TS_RESTART) : CanBlock st T Ac s1 t where
  mem := hc.mem
  nb := by rw [e]; exact not_blocked_restart
  nrp := by rw [e]; exact restart_ne.1
  nq := by rw [k.inqf hc.mem]; exact hc.nq
  nr := by rw [k.inqf hc.mem]; exact hc.nr
  na := by
    rcases k.act with e' | e'
    · rw [e']; exact hc.na
    · rw [e']; intro e''; exact notT_small hT (by rw [← e'']; decide) hc.mem
  ni := by rw [k.idleW]; exact hc.ni
  ac := by rw [k.scf hc.mem]; exact hc.ac

/-- **Endpoint send** (`Send`/`Call`/`NBSend` on an endpoint cap): restart,
`send_ipc`.  The caller can block (`CanBlock`, as at a receive), and the user
words are outside the kernel objects. -/
theorem ep_send.blk {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {U : Set U64}
    {G : S → Prop} (hxf : XferOK st ar T Cs Ω H Sg Rp Scs Nt Z U G) (s : S) (a : A) (blk call : Bool) (badge : U64)
    (grant grant_reply don : Bool) (ct e : U64)
    (hG : ∀ s1 s2, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 → H e = some .ep →
      (L.epState s1 e = 1#u64 ∨ L.epState s1 e = 2#u64) → endpoint.ep_dequeue st s1 e (L.epQ s1 e).head = ok s2 → G s2)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hU : UserOK st T Cs Ω H U s)
    (hc : CanBlock st T Ac s ct) (hdon : don = true → L.mem s (scA ct) ≠ 0#u64) (hH : H e = some .ep) :
    (do
      let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
      let (s2, a1) ← endpoint.send_ipc st ar s1 a blk call badge grant grant_reply don ct e
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1)) ⦃ r s' _ =>
      r = .Ok () ∧ BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  have hT := h.1.choose_spec.choose_spec.tcbs
  refine WP.spec_bind (spec_eq' (sched.set_thread_state.restart_blk (Es := ∅) s ct h hc.mem hc.nb hc.nrp)) ?_
  rintro s1 ⟨eq1, ⟨⟨Q1, R1, h1⟩, hB1, hX1, hS1, hSg1⟩, -, e1, k1⟩
  refine WP.spec_bind (endpoint.send_ipc.ipc hA hxf s1 a blk call badge grant grant_reply don ct e Q1 R1
    (fun s2 => hG s1 s2 eq1) h1 hB1 hX1
    hS1 hSg1 (hU.ksb k1.ksb) (hc.restart hT k1 e1) (fun hd => by rw [k1.scf hc.mem]; exact hdon hd) hH) ?_
  rintro ⟨s2, a1⟩ h2
  try simp only [WP.uncurry'_pair] at h2 ⊢
  exact (WP.spec_ok _).2 ⟨by first | trivial | rfl, h2⟩

/-- **Notification signal** (`Send` on a notification cap): restart,
`send_signal`, with its footprint (int6: with the TCBs' IPC buffers in the
user words `U`, `BufAt`; the footprint has those words, `FootDU`). -/
theorem ntfn_signal.blkF {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (ct n badge : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hct : ct ∈ T) (hr : Runnable (L.mem s (stA ct)))
    (hn : n ∈ Nt) (hH : H n = some .ntfn) (hBA : BufAt st T Cs H Sg Scs Z U s) :
    (do
      let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
      let (s2, a1) ← notification.send_signal st ar s1 a n badge
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1)) ⦃ r s' _ =>
      r = .Ok () ∧ BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ FootDU st T Cs Sg Scs Z (EH H) U s s' ⦄ := by
  refine WP.spec_bind (sched.set_thread_state.restart_blk (Es := EH H) s ct h hct (runnable_ok hr).1
    (runnable_ok hr).2) ?_
  rintro s1 ⟨h1, f1, -, k1⟩
  have hB1 := hBA.of_fr (IbFr.of_keepT k1.toKeepT0)
  refine WP.spec_bind (notification.send_signal.tinvF hA s1 a n badge h1 hn hH hB1.1 hB1.2) ?_
  rintro ⟨s2, a1⟩ ⟨h2, f2, -, -⟩
  try simp only [WP.uncurry'_pair]
  exact (WP.spec_ok _).2 ⟨by first | trivial | rfl, h2, (FootD.u (Foot.d f1)).trans f2⟩

/-! ## TCB `SetPriority` (restart, then `set_priority`) -/

/-- **TCB `SetPriority`** (`thread_control_sched` with only
`SCHED_UPDATE_PRIO`, after the caller's restart), with its footprint: the
current-thread conditions of `set_priority` are asked of the state before
the restart. -/
theorem tcb_set_priority.blkF {A : Type _} (s : S) (a : A) (t prio : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hr : Runnable (L.mem s (stA (L.curW s))))
    (ht : t ∈ T) (hv : prio.val < 256)
    (hcur : t = L.curW s → (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64 ∧ L.mem s (scA t) ≠ 0#u64 ∧
      L.mem s (scA t) ∈ Ac) :
    (do
      let s1 ← sched.set_thread_state st s (L.curW s) sched.TS_RESTART
      let s2 ← sched.set_priority st s1 t prio
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a)) ⦃ r s' _ =>
      r = .Ok () ∧ BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z (EH H) s s' ⦄ := by
  have hc : L.curW s ∈ T := h.1.choose_spec.choose_spec.curT
  refine WP.spec_bind (sched.set_thread_state.restart_blk (Es := EH H) s _ h hc (runnable_ok hr).1
    (runnable_ok hr).2) ?_
  rintro s1 ⟨h1, f1, -, k1⟩
  have hc1 : t = L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.CUR_THREAD) → t = L.curW s := fun e =>
    e.trans k1.curW
  refine WP.spec_bind (sched.set_priority.blk s1 t prio h1 ht hv
    (fun e => by rw [k1.inqf ht]; exact (hcur (hc1 e)).1)
    (fun e => by rw [k1.scf ht]; exact (hcur (hc1 e)).2.1)
    (fun e => by rw [k1.scf ht]; exact (hcur (hc1 e)).2.2)) ?_
  rintro s2 ⟨h2, f2, -⟩
  exact (WP.spec_ok _).2 ⟨by first | trivial | rfl, h2, f1.trans f2⟩

end

end Fl4Proofs.P1
