/-
P3 (line mmuAD, gen 29): **`set_thread_state Running` then `postpone` at `JAtZV2`** (gen 28's "Next" item 3,
`runPostJ`).

* **`JAtZB.runPostJV`**: P3/JAtZBRunPost's `JAtZB.runPostJ` (gen 28) with its post extended by three facts its proof
  already has: FL4's writes lie in `TFoot` (`hW7`), the thread's spec TCB is `{x with tcbState := .running}` and
  every other spec object is unchanged (`postpone` keeps the spec heap: `hke`). Proof verbatim otherwise.
* **`JAtZV2.runPostJ`**: the same step at `JAtZV2 V X` for any `V` (`JAtZV2.ofBS`: VCPU objects kept — the
  thread is a TCB, not a VCPU; sizes kept; the only changed TCB is now `running`, so no new `runningVM`).
  Premises exactly `JAtZ.runPostJ`'s.

No named premise. No existing statement changed.
-/
import Fl4Proofs.P3.JAtZBRunPost
import Fl4Proofs.P3.JAtZBYield
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

set_option maxHeartbeats 32000000 in
/-- **`Running`, then `postpone`, at `J`, the post also naming the footprint and the spec heap** (P3/JAtZBRunPost's
`JAtZB.runPostJ`, proof verbatim; module docstring). -/
theorem JAtZB.runPostJV (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) (htD : t ∉ D)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hrs : x.tcbState = .inactive)
    (htc : t.bv ≠ σ.curThread) {sc : U64} (hsc : sc ∈ Z.C) (hxsc : x.tcbSchedContext = some sc.bv)
    {y : Fl4Spec.SchedContext} {n : Nat} (hky : σ.kheap sc.bv = some (.schedContext y n))
    (hya : Fl4Spec.scActive y = true)
    (hnrel : ¬ (Fl4Spec.refillReady σ.curTime (Fl4Spec.refillHd y) = true ∧
      Fl4Spec.refillSufficient 0 (Fl4Spec.refillHd y) = true)) :
    sched.set_thread_state st s t sched.TS_RUNNING ⦃ s6 =>
      XTopAt (L := L) AR Z s6 a (stsAct (updK σ t.bv (.tcb { x with tcbState := .running })) t.bv) ∧
      IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s6
        (stsAct (updK σ t.bv (.tcb { x with tcbState := .running })) t.bv) ∧
      sched.postpone st s6 sc ⦃ s7 => ∃ σ7, Fl4Spec.postpone (Z := Unit) sc.bv
          (stsAct (updK σ t.bv (.tcb { x with tcbState := .running })) t.bv) = ({((), σ7)}, False) ∧
        P1.WritesIn st s s7 (TFoot st Z.T Z.N Z.C Z.c s σ) ∧
        σ7.kheap t.bv = some (.tcb { x with tcbState := .running }) ∧ (∀ p, p ≠ t.bv → σ7.kheap p = σ.kheap p) ∧
        ∃ Lst' : U64 → List U64, JAtZB (L := L) arI AR Z H Cs Ac Lst' D s7 a σ7 ⦄ ⦄ := by
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
  have hr0 : L.mem s (P1.stA t) = sched.TS_INACTIVE := by
    apply UScalar.eq_of_val_eq
    rw [P1.stA_eq, ← tStA_eq, hst, hrs]; unfold sched.TS_INACTIVE; rfl
  -- the thread is in no queue
  have hnq : NotQueued σ t.bv := by
    refine ⟨fun d p hm => ?_, fun hm => ?_⟩
    · obtain ⟨x', -, -, -, h1, -, h3, -⟩ := J.inv.rq d p t.bv hm
      rw [hk] at h1; cases h1; rw [hrs] at h3; cases h3
    · obtain ⟨x', -, -, -, h1, -, h3, -⟩ := J.inv.rel t.bv hm
      rw [hk] at h1; cases h1; rw [hrs] at h3; cases h3
  have hts : t.bv ≠ sc.bv := fun e => by rw [e, hky] at hk; cases hk
  obtain ⟨y0, n0, hky0, hyt⟩ := J.inv.back t.bv x sc.bv hk hxsc
  rw [hky] at hky0; cases hky0
  -- the action is no switch to the thread (it is not schedulable)
  have hnsw : σ.schedulerAction ≠ .switchThread t.bv := fun e => by
    obtain ⟨x', -, -, -, h1, -, h3, -⟩ := schedulable_inv (J.act.1 _ e)
    rw [hk] at h1; cases h1; rw [hrs] at h3; cases h3
  refine WP.spec_mono (WP.spec_and (WP.spec_and (WP.spec_and (set_thread_state_c hH hP0 hP0.e s σ hI.1.toE hSR ht
    hk hq (by rw [hrs]; decide) .running (by decide) sched.TS_RUNNING (by unfold sched.TS_RUNNING; rfl))
    (set_thread_state_sfoot hS ht _)) (set_thread_state_yw hS ht _))
    (P1.sched.set_thread_state.running_blkI (Es := P1.EH H) s t J.blk htH hr0)) ?_
  rintro s6 ⟨⟨⟨⟨hR6, hS6r⟩, hw6⟩, hy6⟩, hblk6, hfoot6⟩
  have hX6 := IpcRel.ofSRN hR6 hS6r
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
  have hks6 : L.ksb s6 = L.ksb s := hW.1
  have hbuf6 : BufWordRel Z.T (L.mem s6) σ6 := J.sc_buf hW hK
  have hI6 : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s6 σ6 := by
    have h := hX'.irelK (by rw [hks6]; exact J.ks) hbuf6
    have e : σ6.archState = σ.archState := hK.arch
    rw [e] at h; exact h
  refine ⟨hX', hI6, ?_⟩
  -- the spec's `Running`
  have hsp : Fl4Spec.setThreadState (Z := Unit) t.bv .running σ = ({((), σ6)}, False) :=
    Notif.setThreadState_eq .running hk
  have hIB6 : InvBut σ6 t.bv ∧ NotQueued σ6 t.bv := (J.inv.toBut t.bv).ik hnq ((ikm_setThreadState .running).of_eq hsp)
  -- the yield words
  have hY6 : YieldRel Z.T Z.C (L.mem s6) σ6 := by
    have h1 := J.yld.frame (m' := L.mem s6) (σ' := σ1)
      (fun y hy => hy6.mem_eq (yieldA_aligned hT hy) fun h => h ⟨y, hy, rfl⟩)
      (YK.YKS.updTcb (y := x6) hk rfl).ykeep
    exact h1.frame (m' := L.mem s6) (σ' := σ6) (fun _ _ => rfl) (YKeep.of_kheap (stsAct_kheap _ _))
  have hYK6 : YKeep σ σ6 := (YK.YKS.updTcb (y := x6) hk rfl).ykeep.trans (YKeep.of_kheap (stsAct_kheap _ _))
  have hsok6 : SOK (false, true) σ σ6 := Pres.of_eq (pres_setThreadState _ _ _) hsp
  -- the FL4 facts at `s6` for `postpone`
  have hS6 : SchedRel st Z.N Z.T Z.C Z.c s6 σ6 := hX6.2.2.1
  have hR6N : NtfnStateRel Z.N Z.T (L.mem s6) σ6 := hX6.1.toN
  obtain ⟨Q6, R6, hc6, hs6⟩ := hS6.lists
  obtain ⟨xt6, hkt6, -, -, hsct6, -⟩ := hs6.tcb t ht
  rw [hk6] at hkt6; cases hkt6
  have hxsc6 : x6.tcbSchedContext = some sc.bv := hxsc
  have h0 : L.mem s6 (scA t) ≠ 0#u64 := (Notif.optRef_some (hsct6.symm.trans hxsc6)).1
  have hst6 : L.mem s6 (scA t) = sc := P1.eq_of_bv (Notif.optRef_some (hsct6.symm.trans hxsc6)).2
  have hky6 : σ6.kheap sc.bv = some (.schedContext y n) := by rw [hkp _ (Ne.symm hts)]; exact hky
  obtain ⟨y', n', hky', hy'⟩ := hs6.scs sc hsc
  rw [hky6] at hky'; cases hky'
  have htw : L.mem s6 (scW sc 24#u64) = t := P1.eq_of_bv (Notif.optRef_some (hy'.tcb.symm.trans hyt)).2
  have hnr6 : t.bv ∉ σ6.releaseQueue := hIB6.2.2
  have hr06 : (L.mem s6 (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
    by_contra hne
    have hm := (hc6.released t ht).1 hne
    exact hnr6 (by rw [hs6.rel, mem_map_bv]; exact hm)
  have hrw6 : L.mem s6 (tStA t) = sched.TS_RUNNING := by
    obtain ⟨x7, hk7, hTR7⟩ := hI6.1.tcb t ht
    rw [hk6] at hk7; cases hk7
    apply UScalar.eq_of_val_eq; rw [hTR7.st]; unfold sched.TS_RUNNING; rfl
  have hrun6 : P1.Runnable (L.mem s6 (P1.stA t)) := by
    rw [stA_tStA, hrw6]; exact P1.runnable_running
  have hns6 : σ6.schedulerAction ≠ .switchThread t.bv := by
    rcases hact6 with e | e <;> rw [e]
    · intro h; cases h
    · exact hnsw
  have hna6 : L.actionW s6 ≠ t := actionW_ne_of hS6 ht hns6
  have hmx : (L.rmax s6 (L.mem s6 (scA t))).val ≠ 0 := by rw [hst6]; exact hy'.rmax_ne hya
  have htw' : L.mem s6 (P1.scTcbA sc) = t := by rw [Sched.scTcbA_eq]; exact htw
  have hRel6 : RelOK σ6 := by
    refine ⟨fun u hu => ?_, hIB6.1.sorted, fun u hu xu p hku hsu => ?_⟩
    · obtain ⟨xu, p, -, -, h1, h2, -⟩ := hIB6.1.rel u hu; exact ⟨xu, p, h1, h2⟩
    · obtain ⟨xu', p', y1, n1, h1, h2, -, h4, h5⟩ := hIB6.1.rel u hu
      rw [hku] at h1; cases h1; rw [hsu] at h2; cases h2; exact ⟨y1, n1, h4, h5⟩
  refine WP.spec_mono (WP.spec_and (postpone_refines s6 σ6 hS6 hRel6 hsc ht htw h0 hr06 hmx)
    (P1.sched.postpone.blk (Es := P1.EH H) s6 sc hblk6 (by rw [htw']; exact htH) (by rw [htw', hst6])
      (J.c0 sc hsc) (by rw [htw']; exact hr06) (by rw [htw']; exact hrun6)
      (by rw [htw']; exact hna6) (fun e => hmx (by rw [hst6, e]; rfl)))) ?_
  rintro s7 ⟨⟨σ7, he, hke, hae, hte, hrq7, hfe, hw7, hS7⟩, hblk, hfoot7⟩
  refine ⟨σ7, he, ?_⟩
  have mem7 : ((), σ7) ∈ (Fl4Spec.postpone (Z := Unit) sc.bv σ6).1 := by rw [he]; exact Set.mem_singleton _
  -- the spec state after `postpone`
  have hne6 : ∀ p y1 n1, σ6.kheap p = some (.schedContext y1 n1) → Fl4Spec.scActive y1 = true →
      y1.scRefills ≠ [] := hIB6.1.ne
  obtain ⟨b, hpe⟩ := postpone_eq hky6 hyt hk6 (specRt σ6) (fun u hu => by
    rcases hu with rfl | hu
    · exact ⟨x6, sc.bv, y, n, hk6, hxsc6, hky6, hne6 _ _ _ hky6 hya, specRt_eq hk6 hxsc6 hky6 (hne6 _ _ _ hky6 hya)⟩
    · obtain ⟨xu, scp, yu, nu, h1, h2, -, h4, h5⟩ := hIB6.1.rel u hu
      exact ⟨xu, scp, yu, nu, h1, h2, h4, hne6 _ _ _ h4 h5, specRt_eq h1 h2 h4 (hne6 _ _ _ h4 h5)⟩)
  have hσ7 := congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst (he.symm.trans hpe)))
  simp only at hσ7
  have hI7 : Inv σ7 := by
    rw [hσ7]; exact hIB6.1.postponed hk6 hxsc6 rfl hky6 hya b
  have e7_ct : σ7.curThread = σ.curThread := by rw [hσ7]; exact e_ct
  have e7_csc : σ7.curSc = σ.curSc := by rw [hσ7]; exact e_csc
  have e7_cons : σ7.consumedTime = σ.consumedTime := by rw [hσ7]; exact e_cons
  have e7_tm : σ7.curTime = σ.curTime := hte.trans e_tm
  have e7_idle : σ7.idleThread = σ.idleThread := by rw [hσ7]; exact e_idle
  have e7_isc : σ7.idleSc = σ.idleSc := by rw [hσ7]; exact e_isc
  have hk7 : σ7.kheap t.bv = some (.tcb x6) := by rw [hke]; exact hk6
  have hkp7 : ∀ p, p ≠ t.bv → σ7.kheap p = σ.kheap p := fun p hp => by rw [hke]; exact hkp p hp
  have hrel7 : ∀ u, u ∈ σ7.releaseQueue ↔ u = t.bv ∨ u ∈ σ.releaseQueue := fun u => by
    rw [hrq7 u, e_rel]
  have hact7 : σ7.schedulerAction = .chooseNewThread ∨ σ7.schedulerAction = σ.schedulerAction := by
    rw [hae]; exact hact6
  -- the frame
  have hW7 : P1.WritesIn st s s7 (TFoot st Z.T Z.N Z.C Z.c s σ) := WritesIn.tfoot_sfoot hW hw7
  have hK7 : ScTKw (fun p => p = t.bv) σ σ7 := hK.trans (nkt_postpone _ σ6 _ mem7).ofFalse
  have hR7 : NtfnStateRel Z.N Z.T (L.mem s7) σ7 := hR6N.frame hS6.placed hfe (KView.of_kheap hke)
  have hX7 : XTopAt (L := L) AR Z s7 a σ7 := xtop_sc_step J.xtop hP0 J.nk hW7 hK7 hS7 hR7 id
  have hNSC : NSC Z.N Z.C σ7 := by
    intro m hm y1 p hy hp
    by_cases e : m.bv = t.bv
    · rw [e, hk7] at hy; cases hy
    · rw [hkp7 _ e] at hy; exact J.nsc m hm y1 p hy hp
  have hw7K : P1.WritesIn st s6 s7 (KFoot st Z.T Z.N Z.C Z.c s6 σ6) := WritesIn.kfoot_of_sfoot hw7
  have hY7 : YieldRel Z.T Z.C (L.mem s7) σ7 :=
    hY6.frame (fun y1 hy1 => hw7K.mem_eq (yieldA_aligned hT hy1) fun hb => hb.ne_yield hS6 hy1 rfl)
      (YKeep.of_kheap hke)
  have hsok7 : SOK (false, true) σ σ7 := hsok6.trans (pres_postpone (f := (false, true)) _ σ6 _ mem7)
  obtain ⟨-, hY', hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ :=
    ScAll.of_tr hS J.rp J.mcp J.call J.rfree ⟨hS7, hR7, hNSC, hI7⟩ hY7 (hW7.mono fun _ h => Or.inl h)
      hsok7 rfl
  -- the scheduler facts
  have hidt : σ.idleThread ≠ t.bv := by
    intro e
    obtain ⟨y1, h1, -, h3, -⟩ := J.act.2
    rw [e, hk] at h1; cases h1; rw [hrs] at h3; cases h3
  have hsched : ∀ u, u ≠ t.bv → Fl4Spec.schedulable u σ = true → Fl4Spec.schedulable u σ7 = true := by
    intro u hut hs
    obtain ⟨y1, scp, z, n1, hky1, hsc1, hrun, hkz, hac, hnr⟩ := schedulable_inv hs
    have hzt : scp ≠ t.bv := by rintro rfl; rw [hk] at hkz; cases hkz
    have hkz7 : σ7.kheap scp = some (.schedContext z n1) := by rw [hkp7 _ hzt]; exact hkz
    have hnr7 : u ∉ σ7.releaseQueue := fun hm => (hrel7 u).1 hm |>.elim hut hnr
    exact schedulable_of (by rw [hkp7 _ hut]; exact hky1) hsc1 hrun hkz7 hac hnr7
  have hAI : ActIdle σ7 := by
    refine ⟨fun u hu => ?_, ?_⟩
    · have hu0 : σ.schedulerAction = .switchThread u := by
        rcases hact7 with e | e
        · rw [e] at hu; cases hu
        · rw [← e]; exact hu
      have hut : u ≠ t.bv := fun e => hnsw (e ▸ hu0)
      exact hsched u hut (J.act.1 u hu0)
    · obtain ⟨y1, h1, h2, h3, h4⟩ := J.act.2
      exact ⟨y1, by rw [e7_idle, hkp7 _ hidt]; exact h1, by rw [e7_isc]; exact h2, h3, by
        rw [e7_idle]; intro hm; rcases (hrel7 _).1 hm with e | e; exact hidt e; exact h4 e⟩
  have hoff : OffOK σ7 := by
    intro h0' y1 n1 hy ha
    rw [e7_cons] at h0' ⊢; rw [e7_tm]; rw [e7_csc] at hy; rw [e7_csc, e7_isc] at ha
    by_cases e : σ.curSc = t.bv
    · rw [e, hk7] at hy; cases hy
    · rw [hkp7 _ e] at hy; exact J.off h0' y1 n1 hy ha
  have hcur7 : σ7.schedulerAction = .chooseNewThread ∨ CurInv σ7 := by
    rcases J.cur with e | hC
    · left
      rcases hact7 with e' | e'
      · exact e'
      · rw [e', e]
    · right
      obtain ⟨xt, hkc, hcs, hnb⟩ := hC.tcb
      obtain ⟨y1, n1, hk1'⟩ := hC.sc
      have hne : σ.curSc ≠ t.bv := by intro e; rw [e, hk] at hk1'; cases hk1'
      refine ⟨?_, ⟨y1, n1, by rw [e7_csc, hkp7 _ hne]; exact hk1'⟩, fun hne' y2 n2 hy => ?_,
        fun hm => ?_⟩
      · exact ⟨xt, by rw [e7_ct, hkp7 _ (Ne.symm htc)]; exact hkc, by rw [e7_csc]; exact hcs, hnb⟩
      · rw [e7_csc, e7_isc] at hne'; rw [e7_csc] at hy
        rw [hkp7 _ hne] at hy
        exact hC.active hne' y2 n2 hy
      · rw [e7_ct] at hm
        rcases (hrel7 _).1 hm with e | e
        · exact htc e.symm
        · exact hC.notRel e
  have hown7 : CurOwnW Z.T Z.C σ7 := by
    have hsc7 : ∀ y1 n1, σ7.kheap σ7.curSc = some (.schedContext y1 n1) →
        σ.kheap σ.curSc = some (.schedContext y1 n1) := by
      intro y1 n1 hy
      rw [e7_csc] at hy
      by_cases e : σ.curSc = t.bv
      · rw [e, hk7] at hy; cases hy
      · rw [hkp7 _ e] at hy; exact hy
    rcases J.own with ⟨u, hu, xt, hkt, hxs, hown, hnr⟩ | ⟨hcs, hun⟩
    · left
      have hnr' : 0 < σ7.consumedTime → u.bv ∉ σ7.releaseQueue := by
        intro h0' hm
        rw [e7_cons] at h0'
        rcases (hrel7 _).1 hm with e | e
        · -- the postponed thread owns the current SC: `OffOK` makes its SC released
          rw [e, hk] at hkt; cases hkt
          have ecs : σ.curSc = sc.bv := Option.some.inj (hxs.symm.trans hxsc)
          obtain ⟨h1, -, h3⟩ := J.off h0' y n (by rw [ecs]; exact hky) (fun _ => hya)
          exact hnrel ⟨h3, restart_suff0 h1⟩
        · exact hnr h0' e
      by_cases hut : u.bv = t.bv
      · rw [hut, hk] at hkt; cases hkt
        exact ⟨u, hu, x6, by rw [hut]; exact hk7, by rw [e7_csc]; exact hxs,
          fun y1 n1 hy => hown y1 n1 (hsc7 y1 n1 hy), hnr'⟩
      · exact ⟨u, hu, xt, by rw [hkp7 _ hut]; exact hkt, by rw [e7_csc]; exact hxs,
          fun y1 n1 hy => hown y1 n1 (hsc7 y1 n1 hy), hnr'⟩
    · exact Or.inr ⟨by rw [e7_csc]; exact hcs, fun y1 n1 hy => hun y1 n1 (hsc7 y1 n1 hy)⟩
  have hcr7 : CurRunM σ7 := by
    by_cases hnr : σ7.schedulerAction ≠ .resumeCurThread
    · exact Or.inl hnr
    have hr' : σ7.schedulerAction = .resumeCurThread := not_not.1 hnr
    have ha : σ7.schedulerAction = σ.schedulerAction := hact7.resolve_left (by rw [hr']; intro e; cases e)
    have h0' : ¬ σ.schedulerAction ≠ .resumeCurThread := fun e => e (by rw [← ha]; exact hr')
    right
    rcases J.curRun.resolve_left h0' with h | h
    · left
      intro y1 hy
      rw [e7_ct] at hy
      rw [hkp7 _ (Ne.symm htc)] at hy; exact h y1 hy
    · right; rw [e7_ct, e7_idle]; exact h
  have hlk : LK (fun _ => False) σ σ7 := fun p => Or.inr (by
    by_cases hp : p = t.bv
    · subst hp; rw [hk, hk7]
      show LObj _ _
      refine ⟨?_, ?_, ?_⟩
      · intro y1 ey; cases ey; exact ⟨_, rfl, Or.inl rfl⟩
      · intro y1 n1 ey; cases ey
      · intro y1 ey; cases ey
    · rw [hkp7 p hp]; exact OL.refl _)
  have hfk : FK σ σ7 := ⟨e7_csc, e7_idle, e7_isc⟩
  have hDbg := J.kw_dbg (P1.Foot.trans hfoot6 hfoot7)
  have hKd := J.kw_dbgKeep (P1.Foot.trans hfoot6 hfoot7)
  have hdead : ∀ q ∈ D, DeadP (L := L) H s7 q := fun q hq =>
    J.deadP_sc_stepQ hX7 hW7 hK7 (fun _ hp => absurd (show q = t from P1.eq_of_bv hp) (fun e => htD (e ▸ hq)))
      hlk hfk hAI.1 hY' ((hYK6.trans (YKeep.of_kheap hke)).dk q.bv) (fun h => h) (J.jcov.dead q hq)
  exact ⟨hW7, hk7, hkp7, Lst', J.sc_frame hW7 hK7 hX7 hCR' hRF' hY' hM' (J.sc_buf hW7 hK7) hRP' (J.sc_apart hW7 hK7)
    (J.sc_jpl hW7 hK7 (J.idleW_keep hX7.fin.1.1.1 hfk.2.1 hfk.2.2).2) (J.sc_jcov hW7 hdead (fun q hq hn => absurd hq hn) (J.idleW_keep hX7.fin.1.1.1 hfk.2.1 hfk.2.2) hKd subset_rfl)
    (J.sc_kern hW7 hK7 hfk hX7 hDbg fun _ h => h)
    (J.sc_utc hW7 hK7 hDbg) hNSC hI7 hcur7 hown7 hoff hAI (BlockedScActive.tkw J.bsa hK7 fun p y1 n1 hp ha => by
      by_cases e : p = t.bv
      · rw [e, hk7] at hp; cases hp
      · rw [hkp7 _ e] at hp; exact ⟨y1, hp, ha, fun _ h => h, id⟩) hcr7 hblk hKd (J.idleW_keep hX7.fin.1.1.1 hfk.2.1 hfk.2.2).1 J.zD⟩


/-- **`Running`, then `postpone`, at `JAtZV2`** (module docstring). -/
theorem JAtZV2.runPostJ (J : JAtZV2 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    (htD : t ∉ D)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hrs : x.tcbState = .inactive)
    (htc : t.bv ≠ σ.curThread) {sc : U64} (hsc : sc ∈ Z.C) (hxsc : x.tcbSchedContext = some sc.bv)
    {y : Fl4Spec.SchedContext} {n : Nat} (hky : σ.kheap sc.bv = some (.schedContext y n))
    (hya : Fl4Spec.scActive y = true)
    (hnrel : ¬ (Fl4Spec.refillReady σ.curTime (Fl4Spec.refillHd y) = true ∧
      Fl4Spec.refillSufficient 0 (Fl4Spec.refillHd y) = true)) :
    sched.set_thread_state st s t sched.TS_RUNNING ⦃ s6 =>
      sched.postpone st s6 sc ⦃ s7 => ∃ σ7, Fl4Spec.postpone (Z := Unit) sc.bv
          (stsAct (updK σ t.bv (.tcb { x with tcbState := .running })) t.bv) = ({((), σ7)}, False) ∧
        ∃ Lst' : U64 → List U64, JAtZV2 (L := L) arI V X AR Z H Cs Ac Lst' D s7 a σ7 ⦄ ⦄ := by
  have B := J.zv.base
  have hS := B.xtop.fin.1.1.1
  refine WP.spec_mono (B.runPostJV ht htD hk hrs htc hsc hxsc hky hya hnrel) fun s6 ⟨_, _, h6⟩ => ?_
  refine WP.spec_mono h6 fun s7 ⟨σ7, he, hW, hk7, hkp7, Lst', B'⟩ => ⟨σ7, he, Lst', ?_⟩
  refine J.ofBS B' hW (fun b hb => tfoot_oobj hS hb) (fun b hb => B.tfoot_nh hb) (VKeep.of_tfoot hS B.thT hW)
    (fun u hu => ?_) (fun o ko' ho => ?_) (fun o x' ho hx => ?_)
  · obtain ⟨vu, hvu⟩ := J.zv.vm.spec u hu
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

end

end

end

end Fl4Proofs.P3
