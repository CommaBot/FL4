/-
# P2 (line p3mc, gen 24): the timer interrupt's tail on a generic guarded store, any plan

Handoff §27b item 3. `irqTail_accT` / `irqTail_decT` / `irqTail_guardT` (P2/IrqTailR, gen 22) assume an empty plan
(`p.tm = 0`), which made the fire branch `ok false` without reads. At a view start whose earliest thread is homed
the plan is not empty. Here, with the same proofs (copied by `scratchpad/tailp.py`):

* **`irqTail_accP`**: an accepted tail whose run is not a fire case (`¬ IrqFire`: after the timestamp, not both
  sufficient and due) on any store answering `IrqRdT` / `IrqWr` — the fire branch is excluded by determinism;
* **`irqTail_decP`**: a declined tail on such a store, given `gfo` (`fire_ok` on `gS` as on `st` after the
  timestamp: the fire branch's only reads beyond the decline's);
* **`irqTail_guardP`**: both: every tail run, if accepted not a fire case.

The accepted fire case is the whole-run lemma of P2/IrqHnG. No named premises; no existing statement changed.
-/
import Fl4Proofs.P2.IrqTailR
import Fl4Proofs.P2.FootTimerIrqLP
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (irqTailF irqTailS irqTailS_eq tr_bind tr_bind_same tr_ite ScAcc)

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 8000000 in
/-- **An accepted tail with any plan, the fire branch excluded or its `fire_ok` given, on any store answering `IrqRdT` / `IrqWr`** (module docstring). -/
theorem irqTail_accP {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
    (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {irq mx : U64} {p : localtimer.TimerIrqPlan}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (gRd : IrqOk st s → ∀ w, Aligned w → IrqRdT st Z s w → R w)
    (gWr : IrqOk st s → ∀ w, Aligned w → IrqWr st Z s w → w ≠ stA (L.curW s) → W w)
    (hIq : IrqOk st s → ∀ i, interrupt.state_off irq = ok i → R (core.num.U64.wrapping_add (L.ksb s) i))
    (hD1 : IrqOk st s → R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hD2 : IrqOk st s → R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME))
    (hwS : IrqOk st s → L.mem s (stA (L.curW s)) = sched.TS_RESTART → ∀ X, L.mem X (stA (L.curW s)) = sched.TS_RESTART →
      L.mem X (affA (L.curW s)) = L.cpu s →
      gS.write X (stA (L.curW s)) sched.TS_RUNNING = st.write X (stA (L.curW s)) sched.TS_RUNNING)
    (hKr : IrqOk st s → R (krA (L := L) s)) (hTab : IrqOk st s → PathObl.RdTab (L := L) R s)
    (hAs : AsidOff (L := L) Ω Sg s)
    (emx : layout.irq.MAX = ok mx) (hle : ¬ irq > mx)
    (ei1 : interrupt.irq_state st s irq = ok interrupt.IRQ_TIMER) (hnf : ¬ IrqFire st ar s a)
    (h : irqTailF st ar s a irq (L.cpu s) p = ok (true, s', a')) :
    irqTailF gS ar s a irq (L.cpu s) p = ok (true, s', a') := by
  obtain ⟨ct, csc, now, i2, b4, due, x, s1, s2, s3, s4, s5, a1, a2, a3, a4, a5, t, ect, ecsc, eok, eq, eu, enow,
    erel, ei2, eb4, edue, hc, ecb, ehi, esc, eac, et, evc⟩ := irqTail_accept_walk ar h
  have ecpu : st.cur_cpu s = ok (L.cpu s) := L.cur_cpu_eq s
  have ectr := ect
  have ecscr := ecsc
  rw [cur_thread_ok] at ect
  have etc : L.curW s = ct := ok_inj_ff ect
  subst etc
  rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) s)] at ecsc
  have ecs' : L.cscW s = csc := ok_inj_ff ecsc
  subst ecs'
  obtain ⟨hmr, hsct, hcore⟩ := current_ok_true eok
  obtain ⟨-, haff, hnvm, -⟩ := may_run_here_true hmr
  cases hc with
  | quiet h4 hd =>
    subst h4 hd
    have G := irq_accT_quiet_core ar hA hI gRd gWr hIq hD1 hD2 hwS ecpu emx hle ei1 ectr ecscr haff hsct
      hcore (mrh_yield hmr) eq eu enow erel ei2 eb4 edue ecb ehi esc eac et
    have et' := G.et
    subst et'
    have hst5 : L.mem s5 (stA (L.curW s)) ≠ sched.TS_RUNNING_VM := by
      rcases G.st5 with e | e
      · rw [e]; simp [sched.TS_RUNNING, sched.TS_RUNNING_VM]
      · rw [e]; exact hnvm
    exact irqTail_replay ar ectr G.gct ecscr G.gcsc eok G.gcok eq G.gb2 eu G.gu enow G.gnow erel G.gb3 ei2
      G.gi2 eb4 G.gb4 edue G.gdue (IrqCase.quiet rfl rfl) (fun h => nomatch h) (fun h => nomatch h) ecb G.gcb
      ehi G.ghi esc G.gsc eac G.gac et G.gt evc (vcpu.check.guard_nvm ar s5 a5 (L.curW s) G.rSt hst5)
  | fire h4 hd hf =>
    exfalso
    apply hnf
    intro s1' a1' now' i2' b4' due' eu' enow' ei2' eb4' edue'
    rw [eu] at eu'
    have e1 := ok_inj_ff eu'
    simp only [Prod.mk.injEq] at e1
    obtain ⟨rfl, rfl⟩ := e1
    rw [enow] at enow'
    obtain rfl := ok_inj_ff enow'
    rw [ei2] at ei2'
    obtain rfl := ok_inj_ff ei2'
    rw [eb4] at eb4'
    obtain rfl := ok_inj_ff eb4'
    rw [edue] at edue'
    obtain rfl := ok_inj_ff edue'
    exact ⟨h4, hd⟩
  | rr h4 hd hr =>
    subst h4 hd
    have G := irq_accT_rr_core ar hA hI gRd gWr hIq hD1 hD2 hwS hKr hTab hAs ecpu emx hle ei1 ectr ecscr haff
      hsct hcore (mrh_yield hmr) eq eu enow erel ei2 eb4 edue hr ecb ehi esc eac et
    have et' := G.et
    subst et'
    have hst5 : L.mem s5 (stA (L.curW s)) ≠ sched.TS_RUNNING_VM := by
      rcases G.st5 with e | e
      · rw [e]; simp [sched.TS_RUNNING, sched.TS_RUNNING_VM]
      · rw [e]; exact hnvm
    exact irqTail_replay ar ectr G.gct ecscr G.gcsc eok G.gcok eq G.gb2 eu G.gu enow G.gnow erel G.gb3 ei2
      G.gi2 eb4 G.gb4 edue G.gdue (IrqCase.rr rfl rfl hr) (fun _ => G.grr rfl) (fun h => nomatch h) ecb G.gcb
      ehi G.ghi esc G.gsc eac G.gac et G.gt evc (vcpu.check.guard_nvm ar s5 a5 (L.curW s) G.rSt hst5)

set_option maxHeartbeats 32000000 in
/-- **A declined tail with any plan, the fire branch excluded or its `fire_ok` given, on any store answering its reads** (module docstring). -/
theorem irqTail_decP {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
    (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {irq : U64} {p : localtimer.TimerIrqPlan}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (nR : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o))
    (gcok : localtimer.current_ok gS s (L.cpu s) (L.curW s) (L.cscW s) =
      localtimer.current_ok st s (L.cpu s) (L.curW s) (L.cscW s))
    (gRd : IrqOk st s → ∀ w, Aligned w → IrqRdT st Z s w → R w)
    (hD1 : IrqOk st s → R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hD2 : IrqOk st s → R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME))
    (hW1 : W (ctA (L := L) s)) (hW2 : W (cnA (L := L) s))
    (gfo : IrqOk st s → ∀ s1 a1 now, sched.update_timestamp st ar s a = ok (s1, a1) →
      sched.cur_time st s1 = ok now →
      localtimer.fire_ok gS s1 (L.cpu s) (L.curW s) p now = localtimer.fire_ok st s1 (L.cpu s) (L.curW s) p now)
    (h : irqTailF st ar s a irq (L.cpu s) p = ok (false, s', a')) :
    irqTailF gS ar s a irq (L.cpu s) p = ok (false, s', a') := by
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  have hcC : L.cpu s ∈ Cs := h0.cur
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ hcC
  have hcT : L.curW s ∈ T := h0.curT
  have ht' := hT _ hcT
  have hX := hI.2.2.1
  have hO := hX.1
  have hS := hI.2.2.2.2
  have hcs : L.cscW s ∈ Scs := hX.2.2.cur
  have hcq : SCq st s Ω (L.cscW s) (Z (L.cscW s)) := scq_of hO hS hcs
  have hmaxΩ : maxA (L.cscW s) ∈ Ω := hcq.2.1 _ hcq.2.2.2.2 hcq.2.2.2.1
  -- the walk
  revert h
  unfold irqTailF
  rw [PathObl.sched.cur_thread.guard (gS := gS) s (nR _ (by rw [curth_val]; omega) (by rw [curth_val])),
    cur_thread_ok]
  simp only [bind_ok]
  rw [PathObl.sched.cur_sc.guard (gS := gS) s (nR _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))]
  refine tr_bind_same (fun csc ecsc => ?_)
  have ecsc' : L.cscW s = csc := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) s)] at ecsc; exact ok_inj_ff ecsc
  subst ecsc'
  rw [gcok]
  refine tr_bind_same (fun b1 eb1 => ?_)
  refine tr_ite (fun hb1 => ?_) (fun _ h => h)
  subst hb1
  -- past `current_ok`: every read is `IrqRdT`'s
  obtain ⟨hmr, hsct, hcore⟩ := current_ok_true eb1
  obtain ⟨-, haff, -, -⟩ := may_run_here_true hmr
  have hok : IrqOk st s := ⟨haff, hsct, hcore⟩
  have gRd' := gRd hok
  have rD1 := hD1 hok
  have rD2 := hD2 hok
  have cR : ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → (K.val < 3528 ∨ 3576 ≤ K.val) →
      K.val ≠ 3496 → K.val ≠ 3504 → R (core.num.U64.wrapping_add (L.curW s) K) := fun K h1 h2 h3 h4 h5 h6 =>
    gRd' _ (field_aligned ht' h2 h3) (Or.inr (Or.inl ⟨K, h1, h2, h3, h4, h5, h6, rfl⟩))
  have scR : ∀ b, InSC (L.cscW s) (Z (L.cscW s)) b → Aligned b → R b := fun b hb ha =>
    gRd' _ ha (Or.inr (Or.inr (Or.inl hb)))
  have hSc : ScAcc R (fun _ => True) (L.cscW s) (Z (L.cscW s)) :=
    ⟨fun b ha hb => scR b hb ha, fun _ _ _ => trivial, trivial⟩
  have rSt : R (stA (L.curW s)) := by rw [stA_eq]; exact cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rSc : R (scA (L.curW s)) := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rIq : R (inqA (L.curW s)) := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rMx : R (maxA (L.cscW s)) := scR _ hcq.2.2.2.1 hcq.2.2.2.2
  rw [sched_quiet.guard (gS := gS) s (nR _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))
    rD2 (nR _ (by simp [layout.node.IPI_PENDING]) (by simp [layout.node.IPI_PENDING]))]
  refine tr_bind_same (fun b2 eb2 => ?_)
  refine tr_ite (fun hb2 => ?_) (fun _ h => h)
  subst hb2
  have hact0 : L.actionW s = sched.ACTION_RESUME_CURRENT := sq_true eb2
  have hsc0 : L.mem s (scA (L.curW s)) ≠ 0#u64 := hI.2.1.resume (hact0.trans resume_val)
  have hAc : L.cscW s ∈ Ac := by
    rw [← hsct]
    exact hI.2.1.sact _ hcT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hact0.trans resume_val, rfl⟩))))) hsc0
  have hmx0 : L.rmax s (L.cscW s) ≠ 0#u64 := (hS.act _ hcs).1 hAc
  rw [PathObl.sched.update_timestamp.guard (gS := gS) ar s a
    (nR _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])) hW1
    (nR _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])) hW2]
  refine tr_bind_same (fun q eu => ?_)
  obtain ⟨s1, a1⟩ := q
  simp only [uncurry_apply_pair]
  -- `s → s1`: the timestamp update
  obtain ⟨n1, -, er⟩ := ut_now ar hA hN eu
  simp only at er
  have k1 : L.ksb s1 = L.ksb s := by rw [er, utW_ksb]
  have c1 : L.cpu s1 = L.cpu s := by rw [er, utW_cpu]
  have m1 : ∀ b, Aligned b → b ≠ ctA (L := L) s → b ≠ cnA (L := L) s → L.mem s1 b = L.mem s b :=
    fun b hb h1 h2 => by rw [er]; exact utW_mem hN n1 hb h1 h2
  have e1N : ∀ o, L.nodeAt s1 (L.cpu s1) o = L.nodeAt s (L.cpu s) o := fun o => by rw [c1, nodeAt_of_ksb k1]
  have hnode1 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 40 → o.val ≠ 48 →
      L.mem s1 (L.nodeAt s (L.cpu s) o) = L.mem s (L.nodeAt s (L.cpu s) o) := by
    intro o ho h8 h40 h48
    refine m1 _ (nodeAt_aligned hN ho h8) (fun e => ?_) (fun e => ?_)
    · have e' := congrArg UScalar.val e
      unfold ctA at e'
      rw [nodeAt_val hN ho, nodeAt_val hN (by simp [layout.node.CUR_TIME])] at e'
      simp [layout.node.CUR_TIME] at e'; omega
    · have e' := congrArg UScalar.val e
      unfold cnA at e'
      rw [nodeAt_val hN ho, nodeAt_val hN (by simp [layout.node.CONSUMED])] at e'
      simp [layout.node.CONSUMED] at e'; omega
  have htcb1 : ∀ {y K : U64}, y ∈ T → K.val < 4096 → K.val % 8 = 0 →
      L.mem s1 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
    intro y K hy hK h8
    exact m1 _ (field_aligned (hT y hy) hK h8) (tcb_node_ne hN hy (hT y hy) hK (by simp [layout.node.CUR_TIME]))
      (tcb_node_ne hN hy (hT y hy) hK (by simp [layout.node.CONSUMED]))
  have hout1 : ∀ b, OutsideObjs st T Cs s b → L.mem s1 b = L.mem s b := fun b hb =>
    m1 b hb.1 (fun e => out_ne_node hb hcC hN (by simp [layout.node.CUR_TIME]) (congrArg UScalar.val e).symm)
      (fun e => out_ne_node hb hcC hN (by simp [layout.node.CONSUMED]) (congrArg UScalar.val e).symm)
  have agΩ1 : ∀ b ∈ Ω, L.mem s1 b = L.mem s b := fun b hb => hout1 b (h0.omega b hb)
  have ndR : ∀ (Y : S), (∀ o, L.nodeAt Y (L.cpu Y) o = L.nodeAt s (L.cpu s) o) → ∀ o : U64, o.val < 4288 →
      o.val % 8 = 0 → R (L.nodeAt Y (L.cpu Y) o) := fun Y e o h1 h2 => by rw [e]; exact nR o h1 h2
  have scK1 : ∀ y ∈ T, L.mem s1 (scA y) = L.mem s (scA y) := fun y hy => by
    rw [scA_eq]; exact htcb1 hy (by simp) (by simp)
  have wf1 : RefillsWF st s1 (L.cscW s) (Z (L.cscW s)) :=
    (SCq.agree hcq agΩ1).1 (by unfold LawfulStore.rmax; rw [agΩ1 _ hmaxΩ]; exact hmx0)
  rw [PathObl.sched.cur_time.guard (gS := gS) s1
    (ndR s1 e1N _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))]
  refine tr_bind_same (fun now enow => ?_)
  -- the release head at `s1`
  have grdue : localtimer.release_due gS s1 (L.cpu s) = localtimer.release_due st s1 (L.cpu s) := by
    have := release_due.guard (gS := gS) s1
      (ndR s1 e1N _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]))
      (fun hne => by
        have e : L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.RELEASE_HEAD) =
            L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) := by
          rw [e1N]
          exact hnode1 _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
            (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
        rw [e] at hne ⊢
        obtain ⟨r1, -, -, r4, r5⟩ := rel_facts hI hne
        have hqr := scq_of hO hS r4
        rw [scK1 _ r1]
        refine ⟨gRd' _ ?_ (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne, Or.inl rfl⟩)))), ?_⟩
        · rw [scA_eq]; exact field_aligned (hT _ r1) (by simp) (by simp)
        · exact PathObl.ScAcc.head (W := fun _ => True)
            ⟨fun b ha hb => gRd' _ ha (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne, Or.inr hb⟩)))), fun _ _ _ => trivial,
              trivial⟩
            ((SCq.agree hqr agΩ1).1 (by
              unfold LawfulStore.rmax; rw [agΩ1 _ (hqr.2.1 _ hqr.2.2.2.2 hqr.2.2.2.1)]; exact r5)))
      (ndR s1 e1N _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
    rwa [c1] at this
  rw [grdue]
  refine tr_bind_same (fun b3 _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  rw [PathObl.sched.consumed.guard (gS := gS) s1
    (ndR s1 e1N _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))]
  refine tr_bind_same (fun i2 ei2 => ?_)
  rw [PathObl.sporadic.sufficient.guard (gS := gS) ar s1 a1 (L.cscW s) i2 (hSc.head wf1)]
  refine tr_bind_same (fun b4 eb4 => ?_)
  have tm1e : L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.TIMER_MIN) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) := by
    rw [e1N]
    exact hnode1 _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
  have gtdue : localtimer.timer_due gS s1 (L.cpu s) now = localtimer.timer_due st s1 (L.cpu s) now := by
    have := timer_due.guard (gS := gS) s1 now
      (ndR s1 e1N _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])) (fun hne => by
        rw [tm1e] at hne ⊢
        have hT0 := (tmin_facts (BXI.blk hI) hcC hne).1
        exact gRd' _ (field_aligned (hT _ hT0) (by simp) (by simp)) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨hne, rfl⟩))))))
    rwa [c1] at this
  rw [gtdue]
  refine tr_bind_same (fun due edue => ?_)
  have grr : localtimer.round_robin_ok gS ar s1 a1 (L.cpu s) (L.curW s) (L.cscW s) now =
      localtimer.round_robin_ok st ar s1 a1 (L.cpu s) (L.curW s) (L.cscW s) now := by
    have := round_robin_ok.guard (gS := gS) ar (s := s1) a1 (ct := L.curW s) (csc := L.cscW s) (now := now)
      (ndR s1 e1N _ (by simp [layout.node.IDLE_SC]) (by simp [layout.node.IDLE_SC]))
      (hSc.off wf1 _ (by simp [layout.sc.PERIOD]) (by simp [layout.sc.PERIOD]))
      rSt rSc (by rw [scK1 _ hcT, hsct]; exact rMx) rIq
      (hSc.off wf1 _ (by simp [layout.sc.REFILL_HEAD]) (by simp [layout.sc.REFILL_HEAD]))
      (hSc.off wf1 _ (by simp [layout.sc.REFILL_TAIL]) (by simp [layout.sc.REFILL_TAIL]))
      ⟨(hSc.rt wf1 wf1.head_lt).1, (hSc.rt wf1 wf1.head_lt).2.2.1⟩
      ⟨(hSc.rt wf1 wf1.tail_lt).1, (hSc.rt wf1 wf1.tail_lt).2.2.1⟩
      (ndR s1 e1N _ (by simp [layout.node.L1_BITMAP]) (by simp [layout.node.L1_BITMAP]))
      (by rw [k1]; exact rD1)
      ⟨ndR s1 e1N _ (by rw [l1Off_val]; omega) (by rw [l1Off_val]), fun inv hinv =>
        ndR s1 e1N _ (by simp; omega) (by simp)⟩
      (cR 3448#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))
    rwa [c1] at this
  have gfire : localtimer.fire_ok gS s1 (L.cpu s) (L.curW s) p now =
      localtimer.fire_ok st s1 (L.cpu s) (L.curW s) p now := gfo hok s1 a1 now eu enow
  refine tr_bind (fun ok1 e1 _ => ?_) (fun ok1 _ hk => ?_)
  · cases b4 <;> cases due
    · simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte] at e1 ⊢
      rw [grr]; exact e1
    · simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte] at e1 ⊢
      exact e1
    · simp only [Bool.false_eq_true, not_true_eq_false, ↓reduceIte] at e1 ⊢
      exact e1
    · simp only [Bool.false_eq_true, not_true_eq_false, ↓reduceIte] at e1 ⊢
      rw [gfire]; exact e1
  · cases ok1
    · rw [if_neg Bool.false_ne_true] at hk ⊢; exact hk
    · exfalso
      rw [if_pos rfl] at hk
      obtain ⟨⟨x2, s2, a2⟩, -, hk⟩ := bind_eq_ok hk
      try simp only [uncurry_apply_pair] at hk
      try dsimp only at hk
      obtain ⟨⟨s3, a3⟩, -, hk⟩ := bind_eq_ok hk
      try simp only [uncurry_apply_pair] at hk
      obtain ⟨⟨s4, a4⟩, -, hk⟩ := bind_eq_ok hk
      try simp only [uncurry_apply_pair] at hk
      obtain ⟨⟨s5, a5⟩, -, hk⟩ := bind_eq_ok hk
      try simp only [uncurry_apply_pair] at hk
      obtain ⟨t, -, hk⟩ := bind_eq_ok hk
      obtain ⟨⟨s6, a6⟩, -, hk⟩ := bind_eq_ok hk
      try simp only [uncurry_apply_pair] at hk
      have e := ok_inj_ff hk
      simp at e

/-- **Every tail run with any plan, the fire branch excluded or its `fire_ok` given is the run on a store answering its reads and writes** (module
docstring): `irqTail_accP` and `irqTail_decP`. -/
theorem irqTail_guardP {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
    (hA : P0.ArchTotal ar) {s : S} {a : A} {irq mx : U64} {p : localtimer.TimerIrqPlan} {r : Bool × S × A}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (nR : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o))
    (gcok : localtimer.current_ok gS s (L.cpu s) (L.curW s) (L.cscW s) =
      localtimer.current_ok st s (L.cpu s) (L.curW s) (L.cscW s))
    (gRd : IrqOk st s → ∀ w, Aligned w → IrqRdT st Z s w → R w)
    (gWr : IrqOk st s → ∀ w, Aligned w → IrqWr st Z s w → w ≠ stA (L.curW s) → W w)
    (hIq : IrqOk st s → ∀ i, interrupt.state_off irq = ok i → R (core.num.U64.wrapping_add (L.ksb s) i))
    (hD1 : IrqOk st s → R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hD2 : IrqOk st s → R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME))
    (hwS : IrqOk st s → L.mem s (stA (L.curW s)) = sched.TS_RESTART → ∀ X, L.mem X (stA (L.curW s)) = sched.TS_RESTART →
      L.mem X (affA (L.curW s)) = L.cpu s →
      gS.write X (stA (L.curW s)) sched.TS_RUNNING = st.write X (stA (L.curW s)) sched.TS_RUNNING)
    (hKr : IrqOk st s → R (krA (L := L) s)) (hTab : IrqOk st s → PathObl.RdTab (L := L) R s)
    (hAs : AsidOff (L := L) Ω Sg s) (hW1 : W (ctA (L := L) s)) (hW2 : W (cnA (L := L) s))
    (emx : layout.irq.MAX = ok mx) (hle : ¬ irq > mx)
    (ei1 : interrupt.irq_state st s irq = ok interrupt.IRQ_TIMER)
    (gfo : IrqOk st s → ∀ s1 a1 now, sched.update_timestamp st ar s a = ok (s1, a1) →
      sched.cur_time st s1 = ok now →
      localtimer.fire_ok gS s1 (L.cpu s) (L.curW s) p now = localtimer.fire_ok st s1 (L.cpu s) (L.curW s) p now)
    (hnf : r.1 = true → ¬ IrqFire st ar s a)
    (h : irqTailF st ar s a irq (L.cpu s) p = ok r) :
    irqTailF gS ar s a irq (L.cpu s) p = ok r := by
  obtain ⟨b, s', a'⟩ := r
  cases b
  · exact irqTail_decP ar hA hI nR gcok gRd hD1 hD2 hW1 hW2 gfo h
  · exact irqTail_accP ar hA hI gRd gWr hIq hD1 hD2 hwS hKr hTab hAs emx hle ei1 (hnf rfl) h

end main

end Fl4Proofs.P2
