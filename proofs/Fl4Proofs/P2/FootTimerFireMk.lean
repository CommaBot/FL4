/-
# P2 (p2lf): `PathObl.move` of a waking fire-case run

`irq_move_fire_wk`: as `irq_move_fire_nw` (`P2/FootTimerFireOwn`), for a run whose due thread's notification wakes a
thread (`¬ NoWake`): the run on `gd st ⊤ (StWrOK …)` is the real run (`irq_accG_fire_pre` with `fire_tail_wk`,
`P2/FootTimerFireTk`), then `interp_gd` through `IsProg`. Every write the waking tail asks for passes `StepOK`:

* local threads' words outside `STATE` / `BLOCK_OBJ` / gate / timer fields (`locw_nondec`), local SCs' words but
  `CORE` (`scw_nondec`), queue links of threads blocked on a held object and the plan's endpoint / reply words
  (`lkw_nondec`), the bound notification's words but `BOUND_TCB` decide no owner (`stepOK_nondec`);
* a local thread's `STATE` write (`StW`) by `stepOK_state`: queued before ⇒ its `BLOCK_OBJ`'s lock is held (`StW`'s
  hypothesis with `Lk := lk s`), the new value is not queued.

Lemma hypotheses (discharged by the caller): `hBA`, `hSwT` as `irq_acc_fire_wk`
(`P2/FootTimerFireAk`). Named premises used: `PlanLk` [P], `ObjLay` [J], `hp` [P] (`IsProg`).
-/
import Fl4Proofs.P2.FootTimerFireAk
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.Serial (Owner)
open Fl4Proofs.P2.OwnMap Fl4Proofs.P2.PathObl
open Classical

section nondec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}

/-- A local thread's word outside `STATE` / `BLOCK_OBJ` / gate / timer fields decides no owner. -/
theorem locw_nondec (hK : RegionOK K) {s : S} (hT : TcbPlaced T) (hL : StLay K st T Scs Z s) {y k : U64}
    (hy : y ∈ T) (h1 : 256 ≤ k.val) (h2 : k.val < 4096) (hga : ¬ GateField k.val) (ht : ¬ TimerField k.val)
    (n1 : k.val ≠ 3328) (n2 : k.val ≠ 3336) : ¬ DecW K (core.num.U64.wrapping_add y k) := by
  apply nondec_of_region hK
  have e : (core.num.U64.wrapping_add y k).val - y.val = k.val := by
    rw [field_val (hT y hy) h2]; omega
  have n3 : k.val ≠ 3520 := fun e' => hga (by unfold GateField; omega)
  have n4 : k.val ≠ 3528 := fun e' => ht (by unfold TimerField; omega)
  have n5 : k.val ≠ 3568 := fun e' => ht (by unfold TimerField; omega)
  exact Or.inl ⟨_, hL.tcb y hy k h1 h2, by rw [e]; exact n3, by rw [e]; exact n1, by rw [e]; exact n2,
    by rw [e]; exact n4, by rw [e]; exact n5⟩

/-- A word of an SC of `Scs` other than its `CORE` decides no owner. -/
theorem scw_nondec (hK : RegionOK K) {s : S} (hL : StLay K st T Scs Z s) {p b : U64} (hp : p ∈ Scs)
    (hb : InSC p (Z p) b) (h16 : b.val ≠ p.val + 16) : ¬ DecW K b :=
  nondec_of_region hK (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, hL.sc _ hp b hb, h16⟩)))))

end nondec

section move
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {A : Type} (ar : machine.Arch A) {m : U64 → U64}
variable {irq : U64} {pl : localtimer.TimerIrqPlan} {lk : S → U64 → Prop} {p : SProg Bool}

set_option maxHeartbeats 16000000 in
/-- **`PathObl.move` of a waking fire-case run** (module docstring). -/
theorem irq_move_fire_wk (hA : P0.ArchTotal ar) (hK : RegionOK K) (hUO : E2E.UserOK K)
    (hp : IsProg (irqBody S irq pl) p) {s s1 : S} {a a1 : A} {U : Set U64}
    (hE : IrqEntK K st T Cs Ω H Sg Rp Scs Nt Z Ac m s) (hY : IrqLay K st Nt irq s)
    (hAff : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t))
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (hOL : ObjLay K H Rp) (hPL : PlanLk lk pl)
    (hBA : ∀ s2 a2 s3 a3, interrupt.handle_interrupt st ar s2 a2 irq = ok (s3, a3) →
      BufAt st T Cs H Sg Scs Z U s3)
    (hSwT : SwTailP st (gd st (fun _ => True) (StWrOK st K m (L.cpu s) (lk s))) ar T Cs Ω H Sg Rp Scs Nt Z Ac
      (fun _ => True) s)
    (hq : IrqFire st ar s a) (hW : ¬ NoWake st s)
    (h : localtimer.handle_timer_irq_local st ar s a irq pl = ok (true, s1, a1)) :
    localtimer.handle_timer_irq_local (mguard st
      (fun x y => StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) (L.cpu s) (lk s) (L.mem x)
        (L.mem y))) ar s a irq pl = ok (true, s1, a1) := by
  have hI := hE.inv
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  have hcT : L.curW s ∈ T := h0.curT
  have hL := hE.lay
  have hX := hI.2.2.1
  have hO := hX.1
  have heap : ∀ y ∈ T, K.heap y = some .tcb := fun y hy =>
    hK.tcbOf y _ (hL.tcb y hy 3328#u64 (by simp) (by simp))
  have m_aff : ∀ y ∈ T, m (fld y oAFFINITY) = L.mem s (affA y) := fun y hy =>
    (hE.mem _ (hUO.tcb y (heap y hy) oAFFINITY (Or.inl rfl)).1 (hUO.tcb y (heap y hy) oAFFINITY (Or.inl rfl)).2).symm
  have es : ∀ y, stA y = fld y oSTATE := fun y => by rw [stA_eq]; rfl
  have eB : ∀ y, blockA y = fld y oBLOCK_OBJ := fun y => by rw [blockA_eq]; rfl
  obtain ⟨mx, now, i2, tip, x, s1', s2, s3, a1', a2, a3, emx, hle, ei1, etip, eb, eok, eq, eu, enow, erel, ei2,
    eb4, edue, efo, ecb, ehi⟩ := fire_eqs ar hA hq h
  obtain ⟨hPE, hPR⟩ := plan_pe_pr hI etip eb
  obtain ⟨hTM0, hpN⟩ := plan_ntfn etip eb efo
  have hTMs := tmin_facts (BXI.blk hI) h0.cur hTM0
  have hB0 : L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) ≠ 0#u64 := fun e =>
    hW (Or.inl e)
  have hNN : L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) ∈ Nt :=
    hX.2.2.bnd _ hTMs.1 hB0
  have pn0 : pl.ntfn ≠ 0#u64 := by rw [hpN]; exact hB0
  set gS := gd st (fun _ => True) (StWrOK st K m (L.cpu s) (lk s)) with egS
  have hwS : IrqOk st s → ∀ X, L.mem X (stA (L.curW s)) = sched.TS_RESTART →
      L.mem X (affA (L.curW s)) = L.cpu s →
      gS.write X (stA (L.curW s)) sched.TS_RUNNING = st.write X (stA (L.curW s)) sched.TS_RUNNING :=
    fun hok X hX haff => gd_write (by
      show StWrOK st K m (L.cpu s) (lk s) X (stA (L.curW s)) sched.TS_RUNNING
      unfold StWrOK
      rw [es]
      exact stepOK_state hK hUO (heap _ hcT) haff (by rw [m_aff _ hcT]; exact hok.aff)
        (fun hq => absurd hq (by rw [← es, hX]; simp [QueuedState, sched.TS_RESTART]))
        (fun hq => absurd hq (by simp [QueuedState, sched.TS_RUNNING])))
  have hSW : StW st gS T (lk s) s := fun X y v hy haff hq0 hv => gd_write (by
    show StWrOK st K m (L.cpu s) (lk s) X (stA y) v
    unfold StWrOK
    rw [es]
    exact stepOK_state hK hUO (heap _ hy.1) haff (by rw [m_aff _ hy.1]; exact hy.2)
      (fun hq => by rw [← eB]; exact hq0 (by rw [es]; exact hq)) (fun hq => absurd hq hv))
  have hg : localtimer.handle_timer_irq_local gS ar s a irq pl = ok (true, s1, a1) := by
    refine irq_accG_fire_pre (gS := gS) (R := fun _ => True) (W := WAll (StWrOK st K m (L.cpu s) (lk s))) ar hA hI
      hq (fun _ _ _ _ => trivial)
      (fun _ w ha hw hn x v => stepOK_nondec hK hUO ha (irq_wr_nondec hK hI hL hw hn))
      (fun _ _ _ => trivial) (fun _ => trivial) (fun _ => trivial) ?_ ?_ h
    · intro _ s1'' a1'' now' _ _
      have mr : ∀ c t : U64, MayRdC st (fun _ => True) s1'' c t := fun _ _ _ =>
        ⟨trivial, fun _ => ⟨trivial, trivial, trivial, trivial, fun _ => trivial⟩⟩
      have tr : TopRdC st (fun _ => True) s1'' :=
        { l1 := trivial, dom := trivial, bm := ⟨trivial, fun _ _ => trivial⟩
          top := fun _ _ _ _ _ _ _ => ⟨trivial, fun _ => ⟨trivial, fun _ => ⟨trivial, trivial, trivial, trivial,
            fun _ => trivial⟩⟩⟩ }
      have wr : ∀ w n : U64, WakeRdC st (fun _ => True) s1'' w n := fun w n =>
        { may := mr _ w, dq := fun _ _ => ⟨trivial, trivial⟩, nsc := trivial, top := tr }
      have c1 : L.cpu s1'' = L.cpu s := by
        obtain ⟨n1, -, er⟩ := ut_now ar hA (h0.nodes _ h0.cur) (by assumption)
        simp only at er
        rw [er, utW_cpu]
      have := fire_ok.guardK (gS := gS) (R := fun _ => True) (s := s1'') (ct := L.curW s) (p := pl) (now := now')
        (fun _ => True) (fun _ => trivial) (fun _ => trivial) (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
        (fun _ _ => ⟨trivial, fun _ _ _ => trivial⟩) (fun _ _ => trivial)
        (fun _ => fireTail.guardC (fun _ => ⟨trivial, trivial, trivial, trivial, wr _ _, fun _ _ => wr _ _⟩))
      rwa [c1] at this
    · intro hok s1'' a1'' x' s2' a2' s3' a3' now' eu' enow' efo' ecb' ehi'
      rw [eu] at eu'
      have e1 := ok_inj_ff eu'
      simp only [Prod.mk.injEq] at e1
      obtain ⟨rfl, rfl⟩ := e1
      rw [enow] at enow'
      obtain rfl := ok_inj_ff enow'
      have hdl : ∀ y ∈ T, FootLtArmed st s (L.cpu s) y → thA y = fld y oTIMER_HEIGHT := fun _ _ _ => rfl
      have hdd : ∀ y ∈ T, FootLtArmed st s (L.cpu s) y → tdA y = fld y oTIMER_DEADLINE := fun _ _ _ => rfl
      exact fire_tail_wk (gS := gS) (R := fun _ => True) (W := WAll (StWrOK st K m (L.cpu s) (lk s)))
        (Lk := lk s) (U := U) ar hA hI hNt hok (fun _ _ _ => trivial)
        (fun w ha hw hn x v => stepOK_nondec hK hUO ha (fire_wr_nondec hK hI hL hY hw hn))
        trivial (hwS hok)
        (fun X y v hy ha hc => gd_write (by
          show StWrOK st K m (L.cpu s) (lk s) X (thA y) v
          unfold StWrOK
          rw [hdl y hy ha]
          exact stepOK_height hK hUO (heap y hy) hc))
        (fun X y v hy ha ha1 ha0 hc => gd_write (by
          show StWrOK st K m (L.cpu s) (lk s) X (tdA y) v
          unfold StWrOK
          rw [hdd y hy ha]
          exact stepOK_deadline hK hUO (heap y hy) ha1 (by rw [m_aff y hy]; exact ha0) hc))
        hW hAff (fun _ _ _ _ _ _ _ _ => trivial)
        (fun y hy k h1 h2 h3 hga ht _ n1 n2 x v => stepOK_nondec hK hUO (field_aligned (hT y hy.1) h2 h3)
          (locw_nondec hK hT hL hy.1 h1 h2 hga ht n1 n2))
        (fun _ _ _ _ _ _ => trivial)
        (fun q hq _ b ha hb h16 x v => stepOK_nondec hK hUO ha (scw_nondec hK hL hq hb h16))
        (fun y hy hqs hlk k hk => ⟨trivial, fun x v => stepOK_nondec hK hUO
          (field_aligned (hT y hy) (K := k) (by omega) (by omega))
          (lkw_nondec hK hI hL (Lk := lk s) (Or.inl ⟨y, hy, hqs, hlk, k, hk, rfl⟩))⟩)
        trivial hSW ((hPL s).1 pn0) (hPL s).2.1
        (fun k h1 h2 h3 x v => by
          obtain ⟨p1, p2⟩ := hO.ntP _ hNN
          rw [hpN]
          refine stepOK_nondec hK hUO (by unfold Aligned; rw [ntfn_word_val p1 p2 h1]; omega)
            (nondec_of_region hK (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hY.ntw _ hNN k h1, ?_⟩))))))
          rw [ntfn_word_val p1 p2 h1]; omega)
        (fun hep k h1 h2 => by
          obtain ⟨hH, hal⟩ := hPE hep
          exact ⟨trivial, fun x v => stepOK_nondec hK hUO (hal k h1 h2)
            (lkw_nondec hK hI hL (Lk := lk s) (Or.inr ⟨pl.ep, (hPL s).2.1 hep, hOL.1 _ hH k h1⟩))⟩)
        (fun hr x v => by
          obtain ⟨hR, hal⟩ := hPR hr
          exact stepOK_nondec hK hUO hal (lkw_nondec hK hI hL (Lk := lk s) (w := rTcbA pl.reply)
            (Or.inr ⟨pl.reply, (hPL s).2.2 hr, by unfold rTcbA; exact hOL.2 _ hR _ (by simp [layout.reply.TCB])⟩)))
        etip eb eq eok eu enow erel ei2 eb4 edue efo' ecb' emx hle ei1 ehi' (hBA _ _ _ _ ehi') hSwT
  have eP : ∀ mm : machine.Store S,
      localtimer.handle_timer_irq_local mm ar s a irq pl = interp mm ar p s a :=
    fun mm => congrFun (congrFun (hp A ar mm) s) a
  rw [eP] at hg
  rw [eP]
  exact interp_gd (R := fun _ => True) (P := StWrOK st K m (L.cpu s) (lk s))
    (Q := fun x y => StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) (L.cpu s) (lk s) (L.mem x)
      (L.mem y)) (I := fun _ => True)
    (fun x q v x' _ hq hw => by
      rw [L.write_eq] at hw
      have e := ok_inj_ff hw
      subst e
      exact ⟨hq, trivial⟩) p s a _ trivial hg

end move

end Fl4Proofs.P2
