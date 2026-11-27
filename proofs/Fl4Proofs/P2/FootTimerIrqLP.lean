/-
# P2: the timer interrupt local path's accepted runs: case split and `PathObl.move`

* `IrqFire` (the fire case selected at the entry state, as `IrqQuiet` / `IrqRR`) and `irq_sel`: an accepted run of
  `localtimer.handle_timer_irq_local` is in one of the three cases (`irq_accept_walk`'s `IrqCase`, the selectors
  hold since every call before the check is a function of the entry state).
* `irq_accG`: an accepted run is the same run on any store `gS` answering `IrqRd` reads and `IrqWr` writes as `st`
  (`irq_accG_quiet`, `irq_accG_rr`), the fire case a premise (`hF`: p2j owns fire's footprint).
* `irq_wr_nondec`: the words of `IrqWr` other than the current thread's `STATE` decide no owner (`OwnMap.DecW`).
* `irq_move_acc`: `PathObl.move` for accepted runs (as `set_timer_move`: run on `gd st ⊤ (StWrOK …)`, the
  current thread's `STATE` write `RESTART → RUNNING` by `stepOK_state`, then `interp_gd` through `IsProg`), the
  fire case a premise (`hFm`).

Premises: `hp` [P] (`IsProg`); `IrqEntK.asid` [J] (P1 `AsidOff`, as `irq_accG_rr`'s); `IrqEntK.lay` [J]
(`StLay`); `hF` / `hFm` (the fire case, p2j's line).
-/
import Fl4Proofs.P2.FootTimerIrqRG
import Fl4Proofs.P2.FootTimerSetMv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap Fl4Proofs.P2.PathObl
open Classical

section sel
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} (ar : machine.Arch A)

/-- The fire case selected at the entry state: after `update_timestamp` the budget is sufficient and a timer is
due. -/
def IrqFire (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A) (s : S) (a : A) : Prop :=
  ∀ s1 a1 now i2 b4 due, sched.update_timestamp st ar s a = ok (s1, a1) → sched.cur_time st s1 = ok now →
    sched.consumed st s1 = ok i2 → sporadic.sufficient st ar s1 a1 (L.cscW s) i2 = ok b4 →
    localtimer.timer_due st s1 (L.cpu s) now = ok due → b4 = true ∧ due = true

/-- **An accepted timer interrupt has `irq < 128`** (gen16): the body declines `irq > irqn::MAX = 127` before it
reads the IRQ state word (`irq_accept_walk`). -/
theorem irq_lt_of_acc {s s' : S} {a a' : A} {irq : U64} {p : localtimer.TimerIrqPlan}
    (h : localtimer.handle_timer_irq_local st ar s a irq p = ok (true, s', a')) : irq.val < 128 := by
  obtain ⟨cpu, mx, i1, ct, csc, now, i2, tip, b4, due, x, s1, s2, s3, s4, s5, a1, a2, a3, a4, a5, t, ecpu, emx,
    hle, -⟩ := irq_accept_walk ar h
  rw [eq_of_spec_fd layout.irq.MAX.spec] at emx
  have e := ok_inj_ff emx
  subst e
  scalar_tac

/-- **An accepted timer interrupt is quiet, round-robin or fire** (module docstring). -/
theorem irq_sel {s s' : S} {a a' : A} {irq : U64} {p : localtimer.TimerIrqPlan}
    (h : localtimer.handle_timer_irq_local st ar s a irq p = ok (true, s', a')) :
    IrqQuiet st ar s a ∨ IrqRR st ar s a ∨ IrqFire st ar s a := by
  obtain ⟨cpu, mx, i1, ct, csc, now, i2, tip, b4, due, x, s1, s2, s3, s4, s5, a1, a2, a3, a4, a5, t, ecpu, emx,
    hle, ei1, hi1, etip, eb, ect, ecsc, eok, eq, eu, enow, erel, ei2, eb4, edue, hc, -⟩ := irq_accept_walk ar h
  have ecp : cpu = L.cpu s := by
    have e := ecpu
    rw [L.cur_cpu_eq] at e; exact (ok_inj_ff e).symm
  have ecs : csc = L.cscW s := by
    have e := ecsc
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) s)] at e; exact (ok_inj_ff e).symm
  have key : ∀ s1' a1' now' i2' b4' due', sched.update_timestamp st ar s a = ok (s1', a1') →
      sched.cur_time st s1' = ok now' → sched.consumed st s1' = ok i2' →
      sporadic.sufficient st ar s1' a1' (L.cscW s) i2' = ok b4' →
      localtimer.timer_due st s1' (L.cpu s) now' = ok due' → b4' = b4 ∧ due' = due := by
    intro s1' a1' now' i2' b4' due' eu' enow' ei2' eb4' edue'
    rw [eu] at eu'
    have e1 := ok_inj_ff eu'
    simp only [Prod.mk.injEq] at e1
    obtain ⟨rfl, rfl⟩ := e1
    rw [enow] at enow'
    obtain rfl := ok_inj_ff enow'
    rw [ei2] at ei2'
    obtain rfl := ok_inj_ff ei2'
    rw [← ecs, eb4] at eb4'
    rw [← ecp, edue] at edue'
    exact ⟨(ok_inj_ff eb4').symm, (ok_inj_ff edue').symm⟩
  cases hc with
  | quiet h4 hd =>
    refine Or.inl fun s1' a1' now' i2' b4' due' e1 e2 e3 e4 e5 => ?_
    obtain ⟨rfl, rfl⟩ := key s1' a1' now' i2' b4' due' e1 e2 e3 e4 e5
    exact ⟨h4, hd⟩
  | rr h4 hd _ =>
    refine Or.inr (Or.inl fun s1' a1' now' i2' b4' due' e1 e2 e3 e4 e5 => ?_)
    obtain ⟨rfl, rfl⟩ := key s1' a1' now' i2' b4' due' e1 e2 e3 e4 e5
    exact ⟨h4, hd⟩
  | fire h4 hd _ =>
    refine Or.inr (Or.inr fun s1' a1' now' i2' b4' due' e1 e2 e3 e4 e5 => ?_)
    obtain ⟨rfl, rfl⟩ := key s1' a1' now' i2' b4' due' e1 e2 e3 e4 e5
    exact ⟨h4, hd⟩

end sel

section acc
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
variable {A : Type} (ar : machine.Arch A)

/-- **An accepted timer interrupt on the guarded store**, quiet or round-robin, the fire case a premise (module
docstring). -/
theorem irq_accG {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
    (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {irq : U64} {p : localtimer.TimerIrqPlan}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (gRd : IrqOk st s → ∀ w, Aligned w → IrqRd st Z s w → R w)
    (gWr : IrqOk st s → ∀ w, Aligned w → IrqWr st Z s w → w ≠ stA (L.curW s) → W w)
    (hIq : IrqOk st s → ∀ i, interrupt.state_off irq = ok i → R (core.num.U64.wrapping_add (L.ksb s) i))
    (hD1 : IrqOk st s → R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hD2 : IrqOk st s → R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME))
    (hwS : IrqOk st s → ∀ X, L.mem X (stA (L.curW s)) = sched.TS_RESTART → L.mem X (affA (L.curW s)) = L.cpu s →
      gS.write X (stA (L.curW s)) sched.TS_RUNNING = st.write X (stA (L.curW s)) sched.TS_RUNNING)
    (hKr : IrqOk st s → R (krA (L := L) s)) (hTab : IrqOk st s → PathObl.RdTab (L := L) R s)
    (hAs : AsidOff (L := L) Ω Sg s)
    (hF : IrqFire st ar s a → localtimer.handle_timer_irq_local gS ar s a irq p = ok (true, s', a'))
    (h : localtimer.handle_timer_irq_local st ar s a irq p = ok (true, s', a')) :
    localtimer.handle_timer_irq_local gS ar s a irq p = ok (true, s', a') := by
  rcases irq_sel ar h with hq | hq | hq
  · exact irq_accG_quiet ar hA hI hq gRd gWr hIq hD1 hD2 hwS h
  · exact irq_accG_rr ar hA hI hq gRd gWr hIq hD1 hD2 hwS hKr hTab hAs h
  · exact hF hq

end acc

section mv
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}

/-- **The entry facts of the timer interrupt for a layout and a model memory**: P1's invariant, the layout [J],
the store agreeing with `m` on aligned kernel words, and P1's `AsidOff` [J]. -/
structure IrqEntK (K : KLayout) (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac : Set U64) (m : U64 → U64) (s : S) : Prop where
  inv : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s
  lay : StLay K st T Scs Z s
  mem : ∀ x, Aligned x → x ∉ K.user → L.mem s x = m x
  asid : AsidOff (L := L) Ω Sg s

/-- **The words of `IrqWr` other than the current thread's `STATE` decide nothing** (`OwnMap.DecW`): this core's
node words, the current thread's registers, sched links and queue word, the current SC's ring and `CONSUMED`. -/
theorem irq_wr_nondec (hK : RegionOK K) {s : S} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hL : StLay K st T Scs Z s) {w : U64} (h : IrqWr st Z s w) (hn : w ≠ stA (L.curW s)) : ¬ DecW K w := by
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  have hcT : L.curW s ∈ T := h0.curT
  have hcs : L.cscW s ∈ Scs := hI.2.2.1.2.2.cur
  have hq := scq_of hI.2.2.1.1 hI.2.2.2.2 hcs
  apply nondec_of_region hK
  have tcbw : ∀ k : U64, 256 ≤ k.val → k.val < 4096 → k.val ≠ 3520 → k.val ≠ 3328 → k.val ≠ 3336 →
      k.val ≠ 3528 → k.val ≠ 3568 →
      (∃ t, region K (core.num.U64.wrapping_add (L.curW s) k) = .tcb t ∧
        (core.num.U64.wrapping_add (L.curW s) k).val - t.val ≠ 3520 ∧
        (core.num.U64.wrapping_add (L.curW s) k).val - t.val ≠ 3328 ∧
        (core.num.U64.wrapping_add (L.curW s) k).val - t.val ≠ 3336 ∧
        (core.num.U64.wrapping_add (L.curW s) k).val - t.val ≠ 3528 ∧
        (core.num.U64.wrapping_add (L.curW s) k).val - t.val ≠ 3568) := by
    intro k h1 h2 n1 n2 n3 n4 n5
    have e : (core.num.U64.wrapping_add (L.curW s) k).val - (L.curW s).val = k.val := by
      rw [field_val (hT _ hcT) h2]; omega
    exact ⟨_, hL.tcb _ hcT k h1 h2, by omega, by omega, by omega, by omega, by omega⟩
  rcases h with ⟨o, ho, -, rfl⟩ | ⟨k, h1, h2, -, rfl⟩ | h | rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inl ⟨_, hL.nd o ho⟩)
  · have k1 : k.val ≠ 3328 := fun e' => hn (by
      rw [stA_eq, show k = 3328#u64 from UScalar.eq_of_val_eq (by simp [e'])])
    exact Or.inl (tcbw k h1 (by omega) (by omega) k1 (by omega) (by omega) (by omega))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, hL.sc _ hcs w h.inSC, by unfold InRing at h; omega⟩))))
  · obtain ⟨hP, hz⟩ := hI.2.2.1.1.sc _ hcs
    have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
    have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, hL.sc _ hcs _ hq.2.2.1.1, by rw [hv, hcv]; omega⟩))))
  · exact Or.inl (tcbw 3480#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))
  · exact Or.inl (tcbw 3488#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))
  · exact Or.inl (tcbw 3592#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))

variable {m : U64 → U64} {A : Type} (ar : machine.Arch A) {irq : U64} {pl : localtimer.TimerIrqPlan}
variable {lk : S → U64 → Prop} {p : SProg Bool}

/-- The body as `E2E.LocalPath.F`. -/
abbrev irqBody (S : Type) (irq : U64) (pl : localtimer.TimerIrqPlan) : ∀ {A : Type}, machine.Arch A →
    machine.Store S → S → A → Result (Bool × S × A) :=
  fun ar m s a => localtimer.handle_timer_irq_local m ar s a irq pl

/-- **`PathObl.move` for an accepted timer interrupt**, quiet or round-robin, the fire case a premise (module
docstring). -/
theorem irq_move_acc (hA : P0.ArchTotal ar) (hK : RegionOK K) (hUO : E2E.UserOK K)
    (hp : IsProg (irqBody S irq pl) p) {s s1 : S} {a a1 : A}
    (hE : IrqEntK K st T Cs Ω H Sg Rp Scs Nt Z Ac m s)
    (hFm : IrqFire st ar s a → localtimer.handle_timer_irq_local (mguard st
      (fun x y => StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) (L.cpu s) (lk s) (L.mem x)
        (L.mem y))) ar s a irq pl = ok (true, s1, a1))
    (h : localtimer.handle_timer_irq_local st ar s a irq pl = ok (true, s1, a1)) :
    localtimer.handle_timer_irq_local (mguard st
      (fun x y => StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) (L.cpu s) (lk s) (L.mem x)
        (L.mem y))) ar s a irq pl = ok (true, s1, a1) := by
  have hI := hE.inv
  have h0 := hI.1.choose_spec.choose_spec
  have hcT : L.curW s ∈ T := h0.curT
  have hL := hE.lay
  have heap : ∀ y ∈ T, K.heap y = some .tcb := fun y hy =>
    hK.tcbOf y _ (hL.tcb y hy 3328#u64 (by simp) (by simp))
  have m_aff : ∀ y ∈ T, m (fld y oAFFINITY) = L.mem s (affA y) := fun y hy =>
    (hE.mem _ (hUO.tcb y (heap y hy) oAFFINITY (Or.inl rfl)).1 (hUO.tcb y (heap y hy) oAFFINITY (Or.inl rfl)).2).symm
  have es : stA (L.curW s) = fld (L.curW s) oSTATE := by rw [stA_eq]; rfl
  rcases irq_sel ar h with hq | hq | hq
  rotate_left 2
  · exact hFm hq
  all_goals
    have hwS : IrqOk st s → ∀ X, L.mem X (stA (L.curW s)) = sched.TS_RESTART →
        L.mem X (affA (L.curW s)) = L.cpu s →
        (gd st (fun _ => True) (StWrOK st K m (L.cpu s) (lk s))).write X (stA (L.curW s)) sched.TS_RUNNING =
          st.write X (stA (L.curW s)) sched.TS_RUNNING := fun hok X hX haff => gd_write (by
      show StWrOK st K m (L.cpu s) (lk s) X (stA (L.curW s)) sched.TS_RUNNING
      unfold StWrOK
      rw [es]
      exact stepOK_state hK hUO (heap _ hcT) haff (by rw [m_aff _ hcT]; exact hok.aff)
        (fun hq => absurd hq (by rw [← es, hX]; simp [QueuedState, sched.TS_RESTART]))
        (fun hq => absurd hq (by simp [QueuedState, sched.TS_RUNNING])))
    have gWr : IrqOk st s → ∀ w, Aligned w → IrqWr st Z s w → w ≠ stA (L.curW s) →
        WAll (StWrOK st K m (L.cpu s) (lk s)) w := fun _ w ha hw hn x v =>
      stepOK_nondec hK hUO ha (irq_wr_nondec hK hI hL hw hn)
    have eP : ∀ mm : machine.Store S,
        localtimer.handle_timer_irq_local mm ar s a irq pl = interp mm ar p s a :=
      fun mm => congrFun (congrFun (hp A ar mm) s) a
  · have hg : localtimer.handle_timer_irq_local (gd st (fun _ => True) (StWrOK st K m (L.cpu s) (lk s))) ar s a
        irq pl = ok (true, s1, a1) :=
      irq_accG_quiet (gS := gd st (fun _ => True) (StWrOK st K m (L.cpu s) (lk s))) (R := fun _ => True)
        (W := WAll (StWrOK st K m (L.cpu s) (lk s))) ar hA hI hq (fun _ _ _ _ => trivial) gWr
        (fun _ _ _ => trivial) (fun _ => trivial) (fun _ => trivial) hwS h
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
  · have hg : localtimer.handle_timer_irq_local (gd st (fun _ => True) (StWrOK st K m (L.cpu s) (lk s))) ar s a
        irq pl = ok (true, s1, a1) :=
      irq_accG_rr (gS := gd st (fun _ => True) (StWrOK st K m (L.cpu s) (lk s))) (R := fun _ => True)
        (W := WAll (StWrOK st K m (L.cpu s) (lk s))) ar hA hI hq (fun _ _ _ _ => trivial) gWr
        (fun _ _ _ => trivial) (fun _ => trivial) (fun _ => trivial) hwS (fun _ => trivial)
        (fun _ _ _ => ⟨trivial, fun _ _ _ => trivial⟩) hE.asid h
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

end mv

end Fl4Proofs.P2
