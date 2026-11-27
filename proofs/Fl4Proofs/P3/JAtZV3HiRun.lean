/-
P3 (line mmuAD, gen 41): **the current thread's two state changes of `handle_invocation`'s tail at `JAtZV3`** —
FL4's `set_thread_state ct TS_RESTART` (a VCPU invocation with an empty reply ends with it, P3/JAtZV3VDec's
`VDecTail`) and `set_thread_state ct TS_RUNNING` of a `Restart` thread (syscall.rs l. 199-204, `flTail`), paired with
the spec's `setThreadState ct .restart` / `.running` (the `stsAct` form, P3/NtfnSpec).

* **`JAtZB.runJDB`**: XTopJointReply's `JAtZ.runJD` over `JAtZB` (verbatim as P3/JAtZV3RunVm's `JAtZB.runVmJD`, with
  the `Restart` lines of the source: `hrs : .restart`, `TS_RESTART`, `running_blk`), post with the `TFoot`
  footprint. Source setting `maxHeartbeats 16000000` kept.
* **`JAtZV3.runJ`**: the same at `JAtZV3` by `JAtZV3.ofBS` (P3/JAtZV3RunVm's `JAtZV3.runVmJ` verbatim but for the
  thread's old state).
* `P1.sched.set_thread_state.runningR_blk`, **`JAtZB.runRJDB`**, **`JAtZV3.runRJ`**: the same for a `Running` thread
  (FL4's in-decode VCPU replies end with `TS_RUNNING` of the still-`Running` caller, P3/JAtZV3VDec's `VDecTail`):
  `running_blk` with `running_ne` / `not_blocked_running`, `runJDB` / `runJ` with `hrs : .running` (every use of the
  old state — not IPC-queued, `IpcFree`, runnable, not the idle thread — holds of `running`).
* **`JAtZB.restartRest`**: P3/XTopJointRest's `jowes_restartD` (`jStepHyps`'s `restart` field) over `JAtZB`, verbatim
  (every `J.<name>` it reads exists over `JAtZB`, checked with gen 39's closure script); source `maxHeartbeats 8000000`.
* **`JAtZB.restartJB`**: P3/XTopJointStep's `JAtZ.restartSJ` over `JAtZB` (`JAtZB.cs_frame` takes no `VKeep`,
  `JCs.sameB`), the post adding the `TFoot` footprint (`set_thread_state_sfoot`); source `maxHeartbeats 4000000`.
* **`JAtZV3.restartJ`**: the caller's `TS_RESTART` at `JAtZV3` (by `JAtZV3.ofBS`, as `runJ`), from a runnable
  current thread.

No named premise. No existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3VFront
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt Ac Es : Set U64} {Z : U64 → Nat}

/-- **`set_thread_state Running` of a `Running` thread keeps `BlkOK`**, with the footprint of `set_thread_state`
(XTopJointReply's `running_blk` with the old state `TS_RUNNING`; same proof). -/
theorem sched.set_thread_state.runningR_blk (s : S) (t : obj.Tcb) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ht : t ∈ T) (hr : L.mem s (stA t) = sched.TS_RUNNING) :
    sched.set_thread_state st s t sched.TS_RUNNING ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hnoref : ∀ r ∈ Rp, L.mem s (rTcbA r) ≠ t :=
    hX.noref (h0.tcbs t ht) (by rw [hr]; exact running_ne.1) (by rw [hr]; exact running_ne.2)
  refine WP.spec_mono (WP.spec_and (sts_all s t _ Q R h0 hB hX hS hSg ht not_blocked_running running_ne
    (Or.inr (by rw [hr]; exact not_blocked_running)) hnoref
    ⟨fun _ _ _ _ _ => runnable_running, fun _ _ _ => runnable_running, fun _ => runnable_running⟩)
    (sched.set_thread_state.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s t _ h0 ht)) ?_
  rintro s' ⟨⟨h1, hB1, hX1, hS1, hSg1, -, -⟩, f1⟩
  exact ⟨⟨⟨Q, R, h1.congrX empty_congr⟩, hB1, hX1, hS1, hSg1⟩, f1⟩

end

end Fl4Proofs.P1

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

set_option maxHeartbeats 16000000 in
/-- **`set_thread_state Running` of a `Restart` thread at `JAtZB`** (XTopJointReply's `JAtZ.runJD` over `JAtZB`,
verbatim as P3/JAtZV3RunVm's `JAtZB.runVmJD`; the post adds the `TFoot` footprint). -/
theorem JAtZB.runJDB (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hrs : x.tcbState = .restart) :
    sched.set_thread_state st s t sched.TS_RUNNING ⦃ s6 => ∃ (Lst' : U64 → List U64),
      JAtZB (L := L) arI AR Z H Cs Ac Lst' D s6 a
        (stsAct (updK σ t.bv (.tcb { x with tcbState := .running })) t.bv) ∧
      SlotsSame Z.th (L.mem s) (L.mem s6) ∧ P1.DbgKeep st (P1.Heap.tcbs H) Cs s s6 ∧
      P1.WritesIn st s s6 (TFoot st Z.T Z.N Z.C Z.c s σ) ⦄ := by
  have hP0 := J.ip
  have hI := J.xtop.irelK J.ks J.buf
  have hS := J.xtop.fin.1.1.1
  have hT : TcbPlaced Z.T := hP0.e.tcb
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  obtain ⟨x0, hk0, hTR⟩ := hI.1.tcb t ht
  rw [hk] at hk0; cases hk0
  have hst : (L.mem s (tStA t)).val = tsCode x.tcbState := hTR.st
  have hq := IpcRel.not_ep_queued hI.1 (t := t) ⟨by rw [hst, hrs]; decide, by rw [hst, hrs]; decide⟩
  have hH := ipcCore_top (st := st) (th := Z.th) (cr := σ.archState.x64CurrentCr3) (N := Z.N) (C := Z.C)
    (c := Z.c) hP0.e
  have hSR := IpcRel.toSRN hI.1 hI.2
  have hr0 : L.mem s (P1.stA t) = sched.TS_RESTART := by
    apply UScalar.eq_of_val_eq
    rw [P1.stA_eq, ← tStA_eq, hst, hrs]; unfold sched.TS_RESTART; rfl
  refine WP.spec_mono (WP.spec_and (WP.spec_and (WP.spec_and (set_thread_state_c hH hP0 hP0.e s σ hI.1.toE hSR ht
    hk hq (by rw [hrs]; decide) .running (by decide) sched.TS_RUNNING (by unfold sched.TS_RUNNING; rfl))
    (set_thread_state_sfoot hS ht _)) (set_thread_state_yw hS ht _))
    (P1.sched.set_thread_state.running_blk (Es := P1.EH H) s t J.blk htH hr0)) ?_
  rintro s6 ⟨⟨⟨⟨hR6, hS6r⟩, hw6⟩, hy6⟩, hblk, hfoot⟩
  have hX6 := IpcRel.ofSRN hR6 hS6r
  have hDbg := J.kw_dbg hfoot
  have hKd := J.kw_dbgKeep hfoot
  set x6 : Fl4Spec.Tcb := { x with tcbState := .running } with hx6
  set σ1 := updK σ t.bv (.tcb x6) with hσ1
  set σ6 := stsAct σ1 t.bv with hσ6
  have hrec : σ6 = { σ1 with schedulerAction := σ6.schedulerAction } := stsAct_rec σ1 t.bv
  have hk1 : σ1.kheap t.bv = some (.tcb x6) := by simp [hσ1, updK]
  have hk6 : σ6.kheap t.bv = some (.tcb x6) := by rw [hσ6, stsAct_kheap]; exact hk1
  have hkp : ∀ p, p ≠ t.bv → σ6.kheap p = σ.kheap p := by
    intro p hp; rw [hσ6, stsAct_kheap, hσ1]; simp [updK, hp]
  have hact6 : σ6.schedulerAction = .chooseNewThread ∨ σ6.schedulerAction = σ.schedulerAction :=
    stsAct_action σ1 t.bv
  have e_ct : σ6.curThread = σ.curThread := by rw [hrec]; rfl
  have e_csc : σ6.curSc = σ.curSc := by rw [hrec]; rfl
  have e_cons : σ6.consumedTime = σ.consumedTime := by rw [hrec]; rfl
  have e_tm : σ6.curTime = σ.curTime := by rw [hrec]; rfl
  have e_idle : σ6.idleThread = σ.idleThread := by rw [hrec]; rfl
  have e_isc : σ6.idleSc = σ.idleSc := by rw [hrec]; rfl
  have e_rel : σ6.releaseQueue = σ.releaseQueue := by rw [hrec]; rfl
  have hW : P1.WritesIn st s s6 (TFoot st Z.T Z.N Z.C Z.c s σ) := WritesIn.tfoot_sfoot (P1.WritesIn.refl _ _) hw6
  have hfx : IpcFree x.tcbState := by
    rw [hrs]; exact ⟨rfl, rfl, fun _ e => by cases e⟩
  have hK : ScTKw (fun p => p = t.bv) σ σ6 := by
    refine ⟨fun p => ?_, by rw [hrec]; rfl, by rw [hrec]; rfl, by rw [hrec]; rfl, by rw [hrec]; rfl,
      by rw [hrec]; rfl, by rw [hrec]; rfl, by rw [hrec]; rfl, by rw [hrec]; rfl, e_ct, e_isc⟩
    by_cases hp : p = t.bv
    · subst hp; rw [hk, hk6]
      show TKObj _ _ _
      exact Or.inr (Or.inl ⟨x, x6, rfl, rfl, rfl, Or.inr ⟨rfl, hfx, rfl, rfl, fun _ e => by cases e⟩⟩)
    · rw [hkp p hp]; exact OTK.refl _ _
  have hX' : XTopAt (L := L) AR Z s6 a σ6 := xtop_sc_step J.xtop hP0 J.nk hW hK hX6.2.2.1 hX6.1.toN id
  -- `Inv`
  have hI1 : Inv σ1 := by
    refine J.inv.step (NtfnStep.tcb hk .running x.tcbArch) (fun u x0 y h1 h2 _ hr => ?_)
      (fun u x0 y h1 h2 hc => ?_)
    · by_cases e : u = t.bv
      · subst e; rw [hk] at h1; cases h1; simp [hσ1, updK] at h2; subst h2; rfl
      · have h2' : σ.kheap u = some (.tcb y) := by simpa [hσ1, updK, e] using h2
        rw [h1] at h2'; cases h2'; exact hr
    · by_cases e : u = t.bv
      · subst e; exact J.inv.rd _ x hk (Or.inl (by rw [hrs]; rfl))
      · have h2' : σ.kheap u = some (.tcb y) := by simpa [hσ1, updK, e] using h2
        exact J.inv.rd u y h2' hc
  have hInv : Inv σ6 := hI1.qchange (qchange_stsAct σ1 t.bv)
  -- the yield words
  have hY6 : YieldRel Z.T Z.C (L.mem s6) σ6 := by
    have h1 := J.yld.frame (m' := L.mem s6) (σ' := σ1)
      (fun y hy => hy6.mem_eq (yieldA_aligned hT hy) fun h => h ⟨y, hy, rfl⟩)
      (YK.YKS.updTcb (y := x6) hk rfl).ykeep
    exact h1.frame (m' := L.mem s6) (σ' := σ6) (fun _ _ => rfl) (YKeep.of_kheap (stsAct_kheap _ _))
  have hYK6 : YKeep σ σ6 := (YK.YKS.updTcb (y := x6) hk rfl).ykeep.trans (YKeep.of_kheap (stsAct_kheap _ _))
  have hsp : Fl4Spec.setThreadState (Z := Unit) t.bv .running σ = ({((), σ6)}, False) :=
    Notif.setThreadState_eq .running hk
  have hsok : SOK (false, true) σ σ6 := Pres.of_eq (pres_setThreadState _ _ _) hsp
  have hNSC : NSC Z.N Z.C σ6 := by
    intro n hn y p hy hp
    by_cases e : n.bv = t.bv
    · rw [e, hk6] at hy; cases hy
    · rw [hkp _ e] at hy; exact J.nsc n hn y p hy hp
  obtain ⟨-, hY', hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ :=
    ScAll.of_tr hS J.rp J.mcp J.call J.rfree ⟨hX6.2.2.1, hX6.1.toN, hNSC, hInv⟩ hY6 (hW.mono fun _ h => Or.inl h)
      hsok rfl
  -- the scheduler facts
  have hsched : ∀ u, Fl4Spec.schedulable u σ = true → Fl4Spec.schedulable u σ6 = true := by
    intro u hs
    obtain ⟨y, scp, z, n, hky, hsc, hrun, hkz, hac, hnr⟩ := schedulable_inv hs
    have hzt : scp ≠ t.bv := by rintro rfl; rw [hk] at hkz; cases hkz
    have hkz6 : σ6.kheap scp = some (.schedContext z n) := by rw [hkp _ hzt]; exact hkz
    have hnr6 : u ∉ σ6.releaseQueue := by rw [e_rel]; exact hnr
    by_cases e : u = t.bv
    · subst e; rw [hk] at hky; cases hky
      exact schedulable_of hk6 hsc rfl hkz6 hac hnr6
    · exact schedulable_of (by rw [hkp _ e]; exact hky) hsc hrun hkz6 hac hnr6
  have hidt : σ.idleThread ≠ t.bv := by
    intro e
    obtain ⟨y, h1, -, h3, -⟩ := J.act.2
    rw [e, hk] at h1; cases h1; rw [hrs] at h3; cases h3
  have hAI : ActIdle σ6 := by
    refine ⟨fun u hu => ?_, ?_⟩
    · have hu0 : σ.schedulerAction = .switchThread u := by
        rcases hact6 with e | e
        · rw [e] at hu; cases hu
        · rw [← e]; exact hu
      exact hsched u (J.act.1 u hu0)
    · obtain ⟨y, h1, h2, h3, h4⟩ := J.act.2
      exact ⟨y, by rw [e_idle, hkp _ hidt]; exact h1, by rw [e_isc]; exact h2, h3, by rw [e_idle, e_rel]; exact h4⟩
  have hoff : OffOK σ6 := by
    intro h0 y n hy ha
    rw [e_cons] at h0 ⊢; rw [e_tm]; rw [e_csc] at hy; rw [e_csc, e_isc] at ha
    by_cases e : σ.curSc = t.bv
    · rw [e, hk6] at hy; cases hy
    · rw [hkp _ e] at hy; exact J.off h0 y n hy ha
  have hcur6 : σ6.schedulerAction = .chooseNewThread ∨ CurInv σ6 := by
    rcases J.cur with e | hC
    · left
      rcases hact6 with e' | e'
      · exact e'
      · rw [e', e]
    · right
      obtain ⟨xt, hkc, hcs, hnb⟩ := hC.tcb
      obtain ⟨y1, n1, hk1'⟩ := hC.sc
      have hne : σ.curSc ≠ t.bv := by intro e; rw [e, hk] at hk1'; cases hk1'
      refine ⟨?_, ⟨y1, n1, by rw [e_csc, hkp _ hne]; exact hk1'⟩, fun hne' y n hy => ?_,
        fun hm => hC.notRel (by rw [e_ct, e_rel] at hm; exact hm)⟩
      · by_cases hct : σ.curThread = t.bv
        · rw [hct, hk] at hkc; cases hkc
          have hnb6 : NotIpcBlk Fl4Spec.ThreadState.running := by
            refine ⟨?_, ?_, ?_⟩
            · intro _ e; cases e
            · intro _ _ e; cases e
            · intro _ _ _ e; cases e
          exact ⟨x6, by rw [e_ct, hct]; exact hk6, by rw [e_csc]; exact hcs, hnb6⟩
        · exact ⟨xt, by rw [e_ct, hkp _ hct]; exact hkc, by rw [e_csc]; exact hcs, hnb⟩
      · rw [e_csc, e_isc] at hne'; rw [e_csc] at hy
        rw [hkp _ hne] at hy
        exact hC.active hne' y n hy
  have hown6 : CurOwnW Z.T Z.C σ6 := by
    have hsc6 : ∀ y n, σ6.kheap σ6.curSc = some (.schedContext y n) → σ.kheap σ.curSc = some (.schedContext y n) := by
      intro y n hy
      rw [e_csc] at hy
      by_cases e : σ.curSc = t.bv
      · rw [e, hk6] at hy; cases hy
      · rw [hkp _ e] at hy; exact hy
    rcases J.own with ⟨u, hu, xt, hkt, hxs, hown, hnr⟩ | ⟨hcs, hun⟩
    · left
      by_cases hut : u.bv = t.bv
      · rw [hut, hk] at hkt; cases hkt
        exact ⟨u, hu, x6, by rw [hut]; exact hk6, by rw [e_csc]; exact hxs, fun y n hy => hown y n (hsc6 y n hy),
          fun h0 hm => hnr (by rw [← e_cons]; exact h0) (by rw [e_rel] at hm; exact hm)⟩
      · exact ⟨u, hu, xt, by rw [hkp _ hut]; exact hkt, by rw [e_csc]; exact hxs, fun y n hy => hown y n (hsc6 y n hy),
          fun h0 hm => hnr (by rw [← e_cons]; exact h0) (by rw [e_rel] at hm; exact hm)⟩
    · exact Or.inr ⟨by rw [e_csc]; exact hcs, fun y n hy => hun y n (hsc6 y n hy)⟩
  have hcr6 : CurRunM σ6 := by
    by_cases hnr : σ6.schedulerAction ≠ .resumeCurThread
    · exact Or.inl hnr
    have hr' : σ6.schedulerAction = .resumeCurThread := not_not.1 hnr
    have ha : σ6.schedulerAction = σ.schedulerAction := hact6.resolve_left (by rw [hr']; intro e; cases e)
    have h0 : ¬ σ.schedulerAction ≠ .resumeCurThread := fun e => e (by rw [← ha]; exact hr')
    right
    rcases J.curRun.resolve_left h0 with h | h
    · left
      intro y hy
      rw [e_ct] at hy
      by_cases hct : σ.curThread = t.bv
      · rw [hct, hk6] at hy; cases hy; rfl
      · rw [hkp _ hct] at hy; exact h y hy
    · right; rw [e_ct, e_idle]; exact h
  have hlk : LK (fun _ => False) σ σ6 := fun p => Or.inr (by
    by_cases hp : p = t.bv
    · subst hp; rw [hk, hk6]
      show LObj _ _
      refine ⟨?_, ?_, ?_⟩
      · intro y ey; cases ey; exact ⟨_, rfl, Or.inl rfl⟩
      · intro y n ey; cases ey
      · intro y ey; cases ey
    · rw [hkp p hp]; exact OL.refl _)
  have hfk : FK σ σ6 := ⟨e_csc, e_idle, e_isc⟩
  have hdead : ∀ q ∈ D, DeadP (L := L) H s6 q := fun q hq =>
    J.deadP_sc_stepG hX' hW hK (fun p x' hp hk' h0 y hy => by
        subst hp; rw [hk] at hk'; cases hk'; rw [hrs] at h0; simp [tsCode] at h0)
      hlk hfk hAI.1 hY' (hYK6.dk q.bv) (fun h => h) (J.jcov.dead q hq)
  exact ⟨Lst', J.sc_frame hW hK hX' hCR' hRF' hY' hM' (J.sc_buf hW hK) hRP' (J.sc_apart hW hK)
    (J.sc_jpl hW hK (J.idleW_keep hX'.fin.1.1.1 hfk.2.1 hfk.2.2).2) (J.sc_jcov hW hdead (fun q hq hn => absurd hq hn) (J.idleW_keep hX'.fin.1.1.1 hfk.2.1 hfk.2.2) hKd subset_rfl) (J.sc_kern hW hK hfk hX' hDbg fun _ h => h)
    (J.sc_utc hW hK hDbg) hNSC hInv hcur6 hown6 hoff hAI (BlockedScActive.tkw J.bsa hK fun p y n hp ha => by
      by_cases e : p = t.bv
      · rw [e, hk6] at hp; cases hp
      · rw [hkp _ e] at hp; exact ⟨y, hp, ha, fun _ h => h, id⟩) hcr6 hblk hKd (J.idleW_keep hX'.fin.1.1.1 hfk.2.1 hfk.2.2).1 J.zD,
    J.xtop.slotsSame_of hW (fun b hb => tfoot_oobj hS hb), P1.Foot.dbgKeep J.blk (fun _ h => h) hfoot, hW⟩

/-- **`set_thread_state Running` of a `Restart` thread at `JAtZV3`** (module docstring). -/
theorem JAtZV3.runJ (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hrs : x.tcbState = .restart) :
    sched.set_thread_state st s t sched.TS_RUNNING ⦃ s6 => ∃ Lst' : U64 → List U64,
      JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst' D s6 a
        (stsAct (updK σ t.bv (.tcb { x with tcbState := .running })) t.bv) ⦄ := by
  have B := J.z2.zv.base
  have hS := B.xtop.fin.1.1.1
  refine WP.spec_mono (B.runJDB ht hk hrs) fun s6 h6 => ?_
  obtain ⟨Lst', B', -, -, hW⟩ := h6
  refine ⟨Lst', ?_⟩
  have hk7 : (stsAct (updK σ t.bv (.tcb { x with tcbState := .running })) t.bv).kheap t.bv =
      some (.tcb { x with tcbState := .running }) := by rw [stsAct_kheap]; simp [updK]
  have hkp7 : ∀ p, p ≠ t.bv → (stsAct (updK σ t.bv (.tcb { x with tcbState := .running })) t.bv).kheap p =
      σ.kheap p := by intro p hp; rw [stsAct_kheap]; simp [updK, hp]
  refine J.ofBS B' hW (fun b hb => tfoot_oobj hS hb) (fun b hb => B.tfoot_nh hb) (VKeep.of_tfoot hS B.thT hW)
    (fun u hu => ?_) (fun o ko' ho => ?_) (fun o x' ho hx => ?_) (fun o vs ho => ?_)
  · obtain ⟨vu, hvu⟩ := J.z2.zv.vm.spec u hu
    refine hkp7 _ fun e => ?_
    rw [e, hk] at hvu; cases hvu
  · by_cases e : o = t.bv
    · subst e
      rw [hk7] at ho; cases ho
      exact ⟨_, hk, rfl⟩
    · rw [hkp7 _ e] at ho; exact ⟨ko', ho, rfl⟩
  · by_cases e : o = t.bv
    · subst e
      rw [hk7] at ho; cases ho
      cases hx
    · rw [hkp7 _ e] at ho; exact ⟨x', ho, hx⟩
  · by_cases e : o = t.bv
    · subst e
      rw [hk7] at ho; cases ho
    · rw [hkp7 _ e] at ho; exact ho

set_option maxHeartbeats 16000000 in
/-- **`set_thread_state Running` of a `Running` thread at `JAtZB`** (`runJDB` with the old state `running`: the same
proof, `runningR_blk` for `running_blk`; every use of the old state holds of `running` too). -/
theorem JAtZB.runRJDB (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hrs : x.tcbState = .running) :
    sched.set_thread_state st s t sched.TS_RUNNING ⦃ s6 => ∃ (Lst' : U64 → List U64),
      JAtZB (L := L) arI AR Z H Cs Ac Lst' D s6 a
        (stsAct (updK σ t.bv (.tcb { x with tcbState := .running })) t.bv) ∧
      SlotsSame Z.th (L.mem s) (L.mem s6) ∧ P1.DbgKeep st (P1.Heap.tcbs H) Cs s s6 ∧
      P1.WritesIn st s s6 (TFoot st Z.T Z.N Z.C Z.c s σ) ⦄ := by
  have hP0 := J.ip
  have hI := J.xtop.irelK J.ks J.buf
  have hS := J.xtop.fin.1.1.1
  have hT : TcbPlaced Z.T := hP0.e.tcb
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  obtain ⟨x0, hk0, hTR⟩ := hI.1.tcb t ht
  rw [hk] at hk0; cases hk0
  have hst : (L.mem s (tStA t)).val = tsCode x.tcbState := hTR.st
  have hq := IpcRel.not_ep_queued hI.1 (t := t) ⟨by rw [hst, hrs]; decide, by rw [hst, hrs]; decide⟩
  have hH := ipcCore_top (st := st) (th := Z.th) (cr := σ.archState.x64CurrentCr3) (N := Z.N) (C := Z.C)
    (c := Z.c) hP0.e
  have hSR := IpcRel.toSRN hI.1 hI.2
  have hr0 : L.mem s (P1.stA t) = sched.TS_RUNNING := by
    apply UScalar.eq_of_val_eq
    rw [P1.stA_eq, ← tStA_eq, hst, hrs]; unfold sched.TS_RUNNING; rfl
  refine WP.spec_mono (WP.spec_and (WP.spec_and (WP.spec_and (set_thread_state_c hH hP0 hP0.e s σ hI.1.toE hSR ht
    hk hq (by rw [hrs]; decide) .running (by decide) sched.TS_RUNNING (by unfold sched.TS_RUNNING; rfl))
    (set_thread_state_sfoot hS ht _)) (set_thread_state_yw hS ht _))
    (P1.sched.set_thread_state.runningR_blk (Es := P1.EH H) s t J.blk htH hr0)) ?_
  rintro s6 ⟨⟨⟨⟨hR6, hS6r⟩, hw6⟩, hy6⟩, hblk, hfoot⟩
  have hX6 := IpcRel.ofSRN hR6 hS6r
  have hDbg := J.kw_dbg hfoot
  have hKd := J.kw_dbgKeep hfoot
  set x6 : Fl4Spec.Tcb := { x with tcbState := .running } with hx6
  set σ1 := updK σ t.bv (.tcb x6) with hσ1
  set σ6 := stsAct σ1 t.bv with hσ6
  have hrec : σ6 = { σ1 with schedulerAction := σ6.schedulerAction } := stsAct_rec σ1 t.bv
  have hk1 : σ1.kheap t.bv = some (.tcb x6) := by simp [hσ1, updK]
  have hk6 : σ6.kheap t.bv = some (.tcb x6) := by rw [hσ6, stsAct_kheap]; exact hk1
  have hkp : ∀ p, p ≠ t.bv → σ6.kheap p = σ.kheap p := by
    intro p hp; rw [hσ6, stsAct_kheap, hσ1]; simp [updK, hp]
  have hact6 : σ6.schedulerAction = .chooseNewThread ∨ σ6.schedulerAction = σ.schedulerAction :=
    stsAct_action σ1 t.bv
  have e_ct : σ6.curThread = σ.curThread := by rw [hrec]; rfl
  have e_csc : σ6.curSc = σ.curSc := by rw [hrec]; rfl
  have e_cons : σ6.consumedTime = σ.consumedTime := by rw [hrec]; rfl
  have e_tm : σ6.curTime = σ.curTime := by rw [hrec]; rfl
  have e_idle : σ6.idleThread = σ.idleThread := by rw [hrec]; rfl
  have e_isc : σ6.idleSc = σ.idleSc := by rw [hrec]; rfl
  have e_rel : σ6.releaseQueue = σ.releaseQueue := by rw [hrec]; rfl
  have hW : P1.WritesIn st s s6 (TFoot st Z.T Z.N Z.C Z.c s σ) := WritesIn.tfoot_sfoot (P1.WritesIn.refl _ _) hw6
  have hfx : IpcFree x.tcbState := by
    rw [hrs]; exact ⟨rfl, rfl, fun _ e => by cases e⟩
  have hK : ScTKw (fun p => p = t.bv) σ σ6 := by
    refine ⟨fun p => ?_, by rw [hrec]; rfl, by rw [hrec]; rfl, by rw [hrec]; rfl, by rw [hrec]; rfl,
      by rw [hrec]; rfl, by rw [hrec]; rfl, by rw [hrec]; rfl, by rw [hrec]; rfl, e_ct, e_isc⟩
    by_cases hp : p = t.bv
    · subst hp; rw [hk, hk6]
      show TKObj _ _ _
      exact Or.inr (Or.inl ⟨x, x6, rfl, rfl, rfl, Or.inr ⟨rfl, hfx, rfl, rfl, fun _ e => by cases e⟩⟩)
    · rw [hkp p hp]; exact OTK.refl _ _
  have hX' : XTopAt (L := L) AR Z s6 a σ6 := xtop_sc_step J.xtop hP0 J.nk hW hK hX6.2.2.1 hX6.1.toN id
  -- `Inv`
  have hI1 : Inv σ1 := by
    refine J.inv.step (NtfnStep.tcb hk .running x.tcbArch) (fun u x0 y h1 h2 _ hr => ?_)
      (fun u x0 y h1 h2 hc => ?_)
    · by_cases e : u = t.bv
      · subst e; rw [hk] at h1; cases h1; simp [hσ1, updK] at h2; subst h2; rfl
      · have h2' : σ.kheap u = some (.tcb y) := by simpa [hσ1, updK, e] using h2
        rw [h1] at h2'; cases h2'; exact hr
    · by_cases e : u = t.bv
      · subst e; exact J.inv.rd _ x hk (Or.inl (by rw [hrs]; rfl))
      · have h2' : σ.kheap u = some (.tcb y) := by simpa [hσ1, updK, e] using h2
        exact J.inv.rd u y h2' hc
  have hInv : Inv σ6 := hI1.qchange (qchange_stsAct σ1 t.bv)
  -- the yield words
  have hY6 : YieldRel Z.T Z.C (L.mem s6) σ6 := by
    have h1 := J.yld.frame (m' := L.mem s6) (σ' := σ1)
      (fun y hy => hy6.mem_eq (yieldA_aligned hT hy) fun h => h ⟨y, hy, rfl⟩)
      (YK.YKS.updTcb (y := x6) hk rfl).ykeep
    exact h1.frame (m' := L.mem s6) (σ' := σ6) (fun _ _ => rfl) (YKeep.of_kheap (stsAct_kheap _ _))
  have hYK6 : YKeep σ σ6 := (YK.YKS.updTcb (y := x6) hk rfl).ykeep.trans (YKeep.of_kheap (stsAct_kheap _ _))
  have hsp : Fl4Spec.setThreadState (Z := Unit) t.bv .running σ = ({((), σ6)}, False) :=
    Notif.setThreadState_eq .running hk
  have hsok : SOK (false, true) σ σ6 := Pres.of_eq (pres_setThreadState _ _ _) hsp
  have hNSC : NSC Z.N Z.C σ6 := by
    intro n hn y p hy hp
    by_cases e : n.bv = t.bv
    · rw [e, hk6] at hy; cases hy
    · rw [hkp _ e] at hy; exact J.nsc n hn y p hy hp
  obtain ⟨-, hY', hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ :=
    ScAll.of_tr hS J.rp J.mcp J.call J.rfree ⟨hX6.2.2.1, hX6.1.toN, hNSC, hInv⟩ hY6 (hW.mono fun _ h => Or.inl h)
      hsok rfl
  -- the scheduler facts
  have hsched : ∀ u, Fl4Spec.schedulable u σ = true → Fl4Spec.schedulable u σ6 = true := by
    intro u hs
    obtain ⟨y, scp, z, n, hky, hsc, hrun, hkz, hac, hnr⟩ := schedulable_inv hs
    have hzt : scp ≠ t.bv := by rintro rfl; rw [hk] at hkz; cases hkz
    have hkz6 : σ6.kheap scp = some (.schedContext z n) := by rw [hkp _ hzt]; exact hkz
    have hnr6 : u ∉ σ6.releaseQueue := by rw [e_rel]; exact hnr
    by_cases e : u = t.bv
    · subst e; rw [hk] at hky; cases hky
      exact schedulable_of hk6 hsc rfl hkz6 hac hnr6
    · exact schedulable_of (by rw [hkp _ e]; exact hky) hsc hrun hkz6 hac hnr6
  have hidt : σ.idleThread ≠ t.bv := by
    intro e
    obtain ⟨y, h1, -, h3, -⟩ := J.act.2
    rw [e, hk] at h1; cases h1; rw [hrs] at h3; cases h3
  have hAI : ActIdle σ6 := by
    refine ⟨fun u hu => ?_, ?_⟩
    · have hu0 : σ.schedulerAction = .switchThread u := by
        rcases hact6 with e | e
        · rw [e] at hu; cases hu
        · rw [← e]; exact hu
      exact hsched u (J.act.1 u hu0)
    · obtain ⟨y, h1, h2, h3, h4⟩ := J.act.2
      exact ⟨y, by rw [e_idle, hkp _ hidt]; exact h1, by rw [e_isc]; exact h2, h3, by rw [e_idle, e_rel]; exact h4⟩
  have hoff : OffOK σ6 := by
    intro h0 y n hy ha
    rw [e_cons] at h0 ⊢; rw [e_tm]; rw [e_csc] at hy; rw [e_csc, e_isc] at ha
    by_cases e : σ.curSc = t.bv
    · rw [e, hk6] at hy; cases hy
    · rw [hkp _ e] at hy; exact J.off h0 y n hy ha
  have hcur6 : σ6.schedulerAction = .chooseNewThread ∨ CurInv σ6 := by
    rcases J.cur with e | hC
    · left
      rcases hact6 with e' | e'
      · exact e'
      · rw [e', e]
    · right
      obtain ⟨xt, hkc, hcs, hnb⟩ := hC.tcb
      obtain ⟨y1, n1, hk1'⟩ := hC.sc
      have hne : σ.curSc ≠ t.bv := by intro e; rw [e, hk] at hk1'; cases hk1'
      refine ⟨?_, ⟨y1, n1, by rw [e_csc, hkp _ hne]; exact hk1'⟩, fun hne' y n hy => ?_,
        fun hm => hC.notRel (by rw [e_ct, e_rel] at hm; exact hm)⟩
      · by_cases hct : σ.curThread = t.bv
        · rw [hct, hk] at hkc; cases hkc
          have hnb6 : NotIpcBlk Fl4Spec.ThreadState.running := by
            refine ⟨?_, ?_, ?_⟩
            · intro _ e; cases e
            · intro _ _ e; cases e
            · intro _ _ _ e; cases e
          exact ⟨x6, by rw [e_ct, hct]; exact hk6, by rw [e_csc]; exact hcs, hnb6⟩
        · exact ⟨xt, by rw [e_ct, hkp _ hct]; exact hkc, by rw [e_csc]; exact hcs, hnb⟩
      · rw [e_csc, e_isc] at hne'; rw [e_csc] at hy
        rw [hkp _ hne] at hy
        exact hC.active hne' y n hy
  have hown6 : CurOwnW Z.T Z.C σ6 := by
    have hsc6 : ∀ y n, σ6.kheap σ6.curSc = some (.schedContext y n) → σ.kheap σ.curSc = some (.schedContext y n) := by
      intro y n hy
      rw [e_csc] at hy
      by_cases e : σ.curSc = t.bv
      · rw [e, hk6] at hy; cases hy
      · rw [hkp _ e] at hy; exact hy
    rcases J.own with ⟨u, hu, xt, hkt, hxs, hown, hnr⟩ | ⟨hcs, hun⟩
    · left
      by_cases hut : u.bv = t.bv
      · rw [hut, hk] at hkt; cases hkt
        exact ⟨u, hu, x6, by rw [hut]; exact hk6, by rw [e_csc]; exact hxs, fun y n hy => hown y n (hsc6 y n hy),
          fun h0 hm => hnr (by rw [← e_cons]; exact h0) (by rw [e_rel] at hm; exact hm)⟩
      · exact ⟨u, hu, xt, by rw [hkp _ hut]; exact hkt, by rw [e_csc]; exact hxs, fun y n hy => hown y n (hsc6 y n hy),
          fun h0 hm => hnr (by rw [← e_cons]; exact h0) (by rw [e_rel] at hm; exact hm)⟩
    · exact Or.inr ⟨by rw [e_csc]; exact hcs, fun y n hy => hun y n (hsc6 y n hy)⟩
  have hcr6 : CurRunM σ6 := by
    by_cases hnr : σ6.schedulerAction ≠ .resumeCurThread
    · exact Or.inl hnr
    have hr' : σ6.schedulerAction = .resumeCurThread := not_not.1 hnr
    have ha : σ6.schedulerAction = σ.schedulerAction := hact6.resolve_left (by rw [hr']; intro e; cases e)
    have h0 : ¬ σ.schedulerAction ≠ .resumeCurThread := fun e => e (by rw [← ha]; exact hr')
    right
    rcases J.curRun.resolve_left h0 with h | h
    · left
      intro y hy
      rw [e_ct] at hy
      by_cases hct : σ.curThread = t.bv
      · rw [hct, hk6] at hy; cases hy; rfl
      · rw [hkp _ hct] at hy; exact h y hy
    · right; rw [e_ct, e_idle]; exact h
  have hlk : LK (fun _ => False) σ σ6 := fun p => Or.inr (by
    by_cases hp : p = t.bv
    · subst hp; rw [hk, hk6]
      show LObj _ _
      refine ⟨?_, ?_, ?_⟩
      · intro y ey; cases ey; exact ⟨_, rfl, Or.inl rfl⟩
      · intro y n ey; cases ey
      · intro y ey; cases ey
    · rw [hkp p hp]; exact OL.refl _)
  have hfk : FK σ σ6 := ⟨e_csc, e_idle, e_isc⟩
  have hdead : ∀ q ∈ D, DeadP (L := L) H s6 q := fun q hq =>
    J.deadP_sc_stepG hX' hW hK (fun p x' hp hk' h0 y hy => by
        subst hp; rw [hk] at hk'; cases hk'; rw [hrs] at h0; simp [tsCode] at h0)
      hlk hfk hAI.1 hY' (hYK6.dk q.bv) (fun h => h) (J.jcov.dead q hq)
  exact ⟨Lst', J.sc_frame hW hK hX' hCR' hRF' hY' hM' (J.sc_buf hW hK) hRP' (J.sc_apart hW hK)
    (J.sc_jpl hW hK (J.idleW_keep hX'.fin.1.1.1 hfk.2.1 hfk.2.2).2) (J.sc_jcov hW hdead (fun q hq hn => absurd hq hn) (J.idleW_keep hX'.fin.1.1.1 hfk.2.1 hfk.2.2) hKd subset_rfl) (J.sc_kern hW hK hfk hX' hDbg fun _ h => h)
    (J.sc_utc hW hK hDbg) hNSC hInv hcur6 hown6 hoff hAI (BlockedScActive.tkw J.bsa hK fun p y n hp ha => by
      by_cases e : p = t.bv
      · rw [e, hk6] at hp; cases hp
      · rw [hkp _ e] at hp; exact ⟨y, hp, ha, fun _ h => h, id⟩) hcr6 hblk hKd (J.idleW_keep hX'.fin.1.1.1 hfk.2.1 hfk.2.2).1 J.zD,
    J.xtop.slotsSame_of hW (fun b hb => tfoot_oobj hS hb), P1.Foot.dbgKeep J.blk (fun _ h => h) hfoot, hW⟩

/-- **`set_thread_state Running` of a `Running` thread at `JAtZV3`** (module docstring). -/
theorem JAtZV3.runRJ (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hrs : x.tcbState = .running) :
    sched.set_thread_state st s t sched.TS_RUNNING ⦃ s6 => ∃ Lst' : U64 → List U64,
      JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst' D s6 a
        (stsAct (updK σ t.bv (.tcb { x with tcbState := .running })) t.bv) ⦄ := by
  have B := J.z2.zv.base
  have hS := B.xtop.fin.1.1.1
  refine WP.spec_mono (B.runRJDB ht hk hrs) fun s6 h6 => ?_
  obtain ⟨Lst', B', -, -, hW⟩ := h6
  refine ⟨Lst', ?_⟩
  have hk7 : (stsAct (updK σ t.bv (.tcb { x with tcbState := .running })) t.bv).kheap t.bv =
      some (.tcb { x with tcbState := .running }) := by rw [stsAct_kheap]; simp [updK]
  have hkp7 : ∀ p, p ≠ t.bv → (stsAct (updK σ t.bv (.tcb { x with tcbState := .running })) t.bv).kheap p =
      σ.kheap p := by intro p hp; rw [stsAct_kheap]; simp [updK, hp]
  refine J.ofBS B' hW (fun b hb => tfoot_oobj hS hb) (fun b hb => B.tfoot_nh hb) (VKeep.of_tfoot hS B.thT hW)
    (fun u hu => ?_) (fun o ko' ho => ?_) (fun o x' ho hx => ?_) (fun o vs ho => ?_)
  · obtain ⟨vu, hvu⟩ := J.z2.zv.vm.spec u hu
    refine hkp7 _ fun e => ?_
    rw [e, hk] at hvu; cases hvu
  · by_cases e : o = t.bv
    · subst e
      rw [hk7] at ho; cases ho
      exact ⟨_, hk, rfl⟩
    · rw [hkp7 _ e] at ho; exact ⟨ko', ho, rfl⟩
  · by_cases e : o = t.bv
    · subst e
      rw [hk7] at ho; cases ho
      cases hx
    · rw [hkp7 _ e] at ho; exact ⟨x', ho, hx⟩
  · by_cases e : o = t.bv
    · subst e
      rw [hk7] at ho; cases ho
    · rw [hkp7 _ e] at ho; exact ho

set_option maxHeartbeats 8000000 in
/-- **P3/XTopJointRest's `jowes_restartD` over `JAtZB`** (statement and proof verbatim, `J : JAtZ` read as
`J : JAtZB`; every `J.<field>` / `J.<lemma>` it reads exists over `JAtZB`; the source's `maxHeartbeats 8000000`). -/
theorem JAtZB.restartRest (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (ct : U64) (x : Fl4Spec.Tcb) (s1 : S) (hcur : σ.curThread = ct.bv) (hk : σ.kheap ct.bv = some (.tcb x))
    (htcb : Z.th ct = some .tcb) (hrun : Fl4Spec.runnable x.tcbState = true)
    (hs1 : sched.set_thread_state st s ct sched.TS_RESTART = ok s1)
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hX1 : XTopAt (L := L) AR Z s1 a (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv)) :
    ∃ Lst' : U64 → List U64, JRest (L := L) arI Z H Cs Ac Lst' D s1
      (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) := by
  set σ1 := Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv with hσ1
  have hX := J.xtop
  have hS := hX.fin.1.1.1
  have hT : ct ∈ Z.T := J.thT ct htcb
  have he1 : Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) := setThreadState_eq' hk _
  have hm1 : ((), σ1) ∈ (Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ).1 := by
    rw [he1]; exact Set.mem_singleton _
  have hK : ScTKw (fun p => p = ct.bv) σ σ1 :=
    tk_setThreadState hk (ipcFree_of_runnable hrun) ipcFree_restart _ hm1
  have hwS : P1.WritesIn st s s1 (SFoot st Z.T Z.c s) := by
    have h := set_thread_state_sfoot (L := L) hS hT sched.TS_RESTART
    rw [hs1, WP.spec_ok] at h; exact h
  have hwK : P1.WritesIn st s s1 (KFoot st Z.T Z.N Z.C Z.c s σ) := hwS.mono fun b hb => KFoot.of_sfoot hb
  have hwT : P1.WritesIn st s s1 (TFoot st Z.T Z.N Z.C Z.c s σ) := WritesIn.tfoot_of_kfoot hwK
  have hS1 := hX1.fin.1.1.1
  have hN1 := hX1.fin.1.1.2.2.1
  have hNsc : NSC Z.N Z.C σ1 := nsc_updTcb J.nsc _ _
  have hI1 : Inv σ1 := Inv.restart J.inv hk hrun
  have hSOK : SOK (true, true) σ σ1 := pres_setThreadState (f := (true, true)) _ _ σ _ hm1
  obtain ⟨-, hY', hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ :=
    ScAll.of_k hS J.rp J.yld J.mcp J.call J.rfree ⟨⟨hS1, hN1, hNsc, hI1⟩, hwK, hSOK⟩
  have hRR' : RRecv (L.mem s1) Z.R σ1 :=
    J.rrecv.frame (TFoot.keep hS J.rp hwT).2.2 (KhRB.of_sctkw hK)
  have hF : FK σ σ1 := (fk_setThreadState _ _).of_eq he1
  have hBK : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s1 ∧ P1.DbgKeep st (P1.Heap.tcbs H) Cs s s1 := by
    obtain ⟨x', hk', hRt⟩ := J.xtop.ipc.tcb ct hT
    rw [hk] at hk'; cases hk'
    have hnbr : ¬ P1.BlockedR (L.mem s (P1.stA ct)) := fun hb => by
      have hq := Sched.blockedR_queued hRt.st hb
      cases hx : x.tcbState <;> simp_all [Fl4Spec.runnable, Fl4Spec.ipcQueuedThreadState]
    have hTe : Z.T = P1.Heap.tcbs H := by
      obtain ⟨Tr, Cq, hJ⟩ := J.jpl
      exact Set.ext fun t => ⟨fun h => J.zH.1 t h, fun h => J.thT t ((hJ.tcb t).2 h)⟩
    rw [hTe] at hT
    have hr := P1.sched.set_thread_state.restart_ok (Es := ∅) J.blk hT (fun h => hnbr (Or.inl h))
      (fun h => hnbr (Or.inr h)) hs1
    exact ⟨hr.1, P1.Foot.dbgKeep J.blk (Set.empty_subset _) hr.2.1⟩
  have hBlk' := hBK.1
  have hKd := hBK.2
  have hDbg : L.mem s1 (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) =
      L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) := by
    have hP := hX.rel.1
    have hctW : ct = L.curW s := P1.eq_of_bv (hcur.symm.trans J.kern.cur)
    have htf := hP.fits ct _ htcb
    have hta := hP.align ct _ htcb
    have hstv : (stA ct).val = ct.val + 3328 := by
      rw [stA_eq, wordOf_val (by simp [objSize] at htf; simp; omega)]; simp
    have h := set_thread_state_frame (L := L) s ct sched.TS_RESTART (by unfold P1.Aligned; rw [hstv]; omega)
      J.kern.act.1
    rw [hs1, WP.spec_ok] at h
    exact h _ J.kern.dwAl (fun e => J.kern.dwNe.1 (by rw [← hctW]; exact e)) J.kern.dwNe.2
  have hkc : σ.kheap σ.curThread = some (.tcb x) := by rw [hcur]; exact hk
  have hcur' : σ1.schedulerAction = .chooseNewThread ∨ CurInv σ1 := by
    rcases J.cur with h | h
    · left
      show (Notif.stsAct _ ct.bv).schedulerAction = _
      unfold Notif.stsAct; split_ifs with hc
      · rfl
      · exact h
    · right
      have := CurInv.restart h hkc
      rw [hcur] at this; exact this
  have hB' : BlockedScActive σ1 := J.bsa.bk (bk_restart hk hrun hm1) hSOK
  have hCR'' : CurRun σ1 := by
    intro y hy
    rw [show σ1.curThread = σ.curThread from (stsAct_fields _ _).2.1, hcur, stsAct_kheap, updK_kheap,
      Function.update_self] at hy
    cases hy; rfl
  have hAI : ActIdle σ1 := (ActIdle.updState J.act hk hrun .restart rfl).ofSts ct.bv
  have hL : LK (fun _ => False) σ σ1 := (lkm_setThreadState (W := fun _ => False) _ _).of_eq he1
  have hDead : ∀ q ∈ D, DeadP (L := L) H s1 q := fun q hq =>
    J.deadP_sc_step hX1 hwT hK (fun p y e hy => by subst e; rw [hk] at hy; cases hy; exact hrun) hL hF hAI.1
      hY' ((hSOK.ykeep rfl).dk q.bv) (fun h => h) (J.jcov.dead q hq)
  refine ⟨Lst', ⟨hCR', hRF', hRR', hY', hM', J.sc_buf hwT hK, hRP', J.sc_apart hwT hK, J.sc_jpl hwT hK (J.idleW_keep hX1.fin.1.1.1 hF.2.1 hF.2.2).2,
    J.sc_jcov hwT hDead (fun q hq hn => absurd hq hn) (J.idleW_keep hX1.fin.1.1.1 hF.2.1 hF.2.2) hKd subset_rfl, J.sc_kern hwT hK hF hX1 hDbg (fun _ h => h),
    J.sc_utc hwT hK hDbg, hNsc, hI1, hcur', curOwnW_updTcb J.own hk _, OffOK.restart J.off _, hAI, hB',
    J.isorted.tkw hK, Or.inr (Or.inl hCR''), hBlk'⟩⟩

set_option maxHeartbeats 4000000 in
/-- **The caller's restart at `JAtZB`** (P3/XTopJointStep's `JAtZ.restartSJ` over `JAtZB`: `jStepHyps`'s `restart`
field is `jowes_restartD`, here `JAtZB.restartRest`; `JAtZB.cs_frame` (no `VKeep` argument), `JCs.sameB`; the post
adds the `TFoot` footprint, as `jowes_restartD` derives it; source setting `maxHeartbeats 4000000`). -/
theorem JAtZB.restartJB (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {ct : U64} {x : Fl4Spec.Tcb} {s1 : S} (hcur : σ.curThread = ct.bv) (hk : σ.kheap ct.bv = some (.tcb x))
    (htcb : Z.th ct = some .tcb) (hrun : Fl4Spec.runnable x.tcbState = true)
    (hs1 : sched.set_thread_state st s ct sched.TS_RESTART = ok s1) :
    ∃ Lst' : U64 → List U64, JAtZB (L := L) arI AR Z H Cs Ac Lst' D s1 a
      (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      P1.WritesIn st s s1 (TFoot st Z.T Z.N Z.C Z.c s σ) := by
  have h := XTopAt.restart J.xtop hcur hk hrun
  rw [hs1, WP.spec_ok] at h
  obtain ⟨hX1, hSS, hk1⟩ := h
  obtain ⟨hkb, hkz⟩ := kback_ksz_upd (σ' := Notif.stsAct (Notif.updK σ ct.bv
    (.tcb { x with tcbState := .restart })) ct.bv) hk (by rw [stsAct_kheap]; rfl)
  obtain ⟨Lst', R⟩ := J.restartRest s a σ ct x s1 hcur hk htcb hrun hs1 hX1
  have hT : ct ∈ Z.T := J.thT ct htcb
  have hK : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s1 := by
    obtain ⟨x', hk', hRt⟩ := J.xtop.ipc.tcb ct hT
    rw [hk] at hk'; cases hk'
    have hnbr : ¬ P1.BlockedR (L.mem s (P1.stA ct)) := fun hb => by
      have hq := Sched.blockedR_queued hRt.st hb
      cases hx : x.tcbState <;> simp_all [Fl4Spec.runnable, Fl4Spec.ipcQueuedThreadState]
    have hT' : ct ∈ P1.Heap.tcbs H := by rw [← J.tcbs_eq.1]; exact hT
    exact P1.Foot.dbgKeep J.blk (Set.empty_subset _)
      (P1.sched.set_thread_state.restart_ok (Es := ∅) J.blk hT' (fun h => hnbr (Or.inl h))
        (fun h => hnbr (Or.inr h)) hs1).2.1
  have hid : (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv).idleThread =
      σ.idleThread := by unfold Notif.stsAct; split <;> rfl
  have hwT : P1.WritesIn st s s1 (TFoot st Z.T Z.N Z.C Z.c s σ) := by
    have h := set_thread_state_sfoot (L := L) J.xtop.fin.1.1.1 hT sched.TS_RESTART
    rw [hs1, WP.spec_ok] at h
    exact WritesIn.tfoot_of_kfoot (h.mono fun b hb => KFoot.of_sfoot hb)
  refine ⟨Lst', ?_, hwT⟩
  exact J.cs_frame (G' := Z.G) (hvn := J.vsSS (G' := Z.G) hX1 hk1 hSS
      (Vs.ArchShr.of_keep (Vs.sts_keep hk { x with tcbState := .restart }).1 (Vs.sts_keep hk _).2)) hk1 hX1 hkb
    ((IpcFrKeep.of_updTcb (y := { x with tcbState := .restart }) hk rfl rfl).trans
      (IpcFrKeep.of_kheap (by rw [stsAct_kheap]))) (J.carry.frame subset_rfl ((IpcFrKeep.of_updTcb (y := { x with tcbState := .restart }) hk rfl rfl).trans
      (IpcFrKeep.of_kheap (by rw [stsAct_kheap]))) hkz)
    (devFrom_same J.xtop.rel.2.1.2.2.1 hX1.rel.2.1.2.2.1 hSS) (JCs.sameB J hSS hkz) R (Vs.VsSlotsT.of_eq fun y hy => hSS.capV hy)
    (J.liveX hX1 rfl rfl rfl hSS hK
      (orig_eq_of_slots J.xtop.rel.2.1.2.2.2.1 hX1.rel.2.1.2.2.2.1 J.kern.orig R.kern.orig hSS)
      (XTopAt.idleW_eqS J.xtop hX1 hid) fun p hp => R.jcov.dead p (J.zD p hp))
    (J.zDX hSS J.zD)

/-- **The caller's restart at `JAtZV3`** (module docstring). -/
theorem JAtZV3.restartJ (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ)
    {ct : U64} {x : Fl4Spec.Tcb} {s1 : S} (hcur : σ.curThread = ct.bv) (hk : σ.kheap ct.bv = some (.tcb x))
    (htcb : Z.th ct = some .tcb) (hrun : Fl4Spec.runnable x.tcbState = true)
    (hs1 : sched.set_thread_state st s ct sched.TS_RESTART = ok s1) :
    ∃ Lst' : U64 → List U64, JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst' D s1 a
      (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) := by
  have B := J.z2.zv.base
  have hS := B.xtop.fin.1.1.1
  obtain ⟨Lst', B', hW⟩ := B.restartJB hcur hk htcb hrun hs1
  refine ⟨Lst', ?_⟩
  have hk7 : (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv).kheap ct.bv =
      some (.tcb { x with tcbState := .restart }) := by rw [stsAct_kheap]; simp [updK]
  have hkp7 : ∀ p, p ≠ ct.bv → (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv).kheap p =
      σ.kheap p := by intro p hp; rw [stsAct_kheap]; simp [updK, hp]
  refine J.ofBS B' hW (fun b hb => tfoot_oobj hS hb) (fun b hb => B.tfoot_nh hb) (VKeep.of_tfoot hS B.thT hW)
    (fun u hu => ?_) (fun o ko' ho => ?_) (fun o x' ho hx => ?_) (fun o vs ho => ?_)
  · obtain ⟨vu, hvu⟩ := J.z2.zv.vm.spec u hu
    refine hkp7 _ fun e => ?_
    rw [e, hk] at hvu; cases hvu
  · by_cases e : o = ct.bv
    · subst e
      rw [hk7] at ho; cases ho
      exact ⟨_, hk, rfl⟩
    · rw [hkp7 _ e] at ho; exact ⟨ko', ho, rfl⟩
  · by_cases e : o = ct.bv
    · subst e
      rw [hk7] at ho; cases ho
      cases hx
    · rw [hkp7 _ e] at ho; exact ⟨x', ho, hx⟩
  · by_cases e : o = ct.bv
    · subst e
      rw [hk7] at ho; cases ho
    · rw [hkp7 _ e] at ho; exact ho

end

end

end

end Fl4Proofs.P3
