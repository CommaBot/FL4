/-
# P2 (p2lf): `timer::fire` with one timer due whose signal wakes a thread, on `gS` and on `st`

The fire step of the waking fire case, at the state `X` before `fire` (in the interrupt path: after
`handle_interrupt`): `remove` of the due thread `TM` (`timer.remove.tf`: `TInv`, timer words only), the waking
signal (`wk_sig`, the waking case `WkCase` asked at every state `remove` may reach), the `REPROGRAM` write and the
stopping second iteration (`fire_stop_sig`, from `BufAt`).

* `node_not_tw`: a node word of this core other than the timer root / min is no timer word.
* `FwKeep`: what the waking fire step keeps (`WkKeep` minus the timer words `remove` writes).
* `fire_wk_step`: `fire gS = fire st`, `fire st = ok (Y, aY)` with `TInv Y`, `FireStop` at `Y`, `ksb` / `cpu`
  kept, the action at `Y` `RESUME_CURRENT` or the woken thread `w`, and `FwKeep X Y w`.

No named premises.
-/
import Fl4Proofs.P2.FootTimerFireWa
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap
open Fl4Proofs.P2.PathObl (NodeSt ScAcc)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T Cs Ω : Set U64} {H : Heap}

/-- A node word of this core other than `TIMER_ROOT` / `TIMER_MIN` is no timer word (`P1.TW`). -/
theorem node_not_tw {X : S} {Xs : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64}
    (hq : SchedQueuesInvX st T Cs Ω H Xs X Q Rq) {o : U64} (ho : o.val < 4288) (h1 : o.val ≠ 104)
    (h2 : o.val ≠ 112) : ¬ Fl4Proofs.P1.TW st T Cs X (L.nodeAt X (L.cpu X) o) := by
  have hN := hq.nodes _ hq.cur
  rintro (⟨y, hy, K, k1, k2, e⟩ | ⟨c, hc, o', ho', e⟩)
  · exact node_ne_field hN ho hy (hq.tcbs y hy) (by omega) e
  · by_cases hcc : c = L.cpu X
    · subst hcc; exact nodeAt_ne hN ho (by rcases ho' with h | h <;> omega) (by rcases ho' with h | h <;> omega) e
    · exact nodeAt_ne_cpu hN (hq.nodes c hc) ho (by rcases ho' with h | h <;> omega) (Ne.symm hcc) e

/-- **What the waking fire step keeps** from its start `X` to its end `Y`: `WkKeep` and also the timer words
(`TIMER_ROOT` 104 / `TIMER_MIN` 112 and the threads' timer fields 3528–3568), which `remove` writes. -/
def FwKeep (st : machine.Store S) [L : LawfulStore st] (T Scs : Set U64) (Z : U64 → Nat) (X Y : S) (w : U64) :
    Prop :=
  (∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 16 → o.val ≠ 56 → o.val ≠ 104 → o.val ≠ 112 →
    L.mem Y (L.nodeAt X (L.cpu X) o) = L.mem X (L.nodeAt X (L.cpu X) o)) ∧
  (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (K.val < 3528 ∨ 3576 ≤ K.val) → K.val ≠ 3496 →
    K.val ≠ 3504 → (y = w → K.val ≠ 3328 ∧ K.val ≠ 256 ∧ K.val ≠ 3376) →
    L.mem Y (core.num.U64.wrapping_add y K) = L.mem X (core.num.U64.wrapping_add y K)) ∧
  (∀ c ∈ Scs, c ≠ L.mem X (scA w) → ∀ b, Aligned b → InSC c (Z c) b → L.mem Y b = L.mem X b)

end

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}

set_option maxRecDepth 4000 in
set_option maxHeartbeats 16000000 in
/-- **`fire` with one due timer whose signal wakes a thread** (module docstring). -/
theorem fire_wk_step {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) {s X : S} (a : A)
    {TM N now t : U64} {Lk : U64 → Prop} {U : Set U64}
    {s1 : S} {cpu : U64} {ct : obj.Tcb} {p : localtimer.TimerIrqPlan}
    (hTX : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac X) (hBA : BufAt st T Cs H Sg Scs Z U X)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (hAffSc : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t))
    (kX : L.ksb X = L.ksb s) (cX : L.cpu X = L.cpu s)
    (kT : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (K.val < 3528 ∨ 3576 ≤ K.val) →
      L.mem X (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K))
    (eTM : L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN) = TM) (hne : TM ≠ 0#u64) (hTMT : TM ∈ T)
    (hTMl : L.mem s (affA TM) = L.cpu s)
    (hct : L.mem X (L.nodeAt X (L.cpu X) layout.node.CUR_TIME) = now) (hdue : ¬ L.mem X (tdA TM) > now)
    (eN : L.mem X (boundA TM) = N) (hN0 : N ≠ 0#u64)
    (hac : L.actionW X = sched.ACTION_RESUME_CURRENT)
    (hwk : ∀ X1, WritesIn st X X1 (Fl4Proofs.P1.TW st T Cs X) → WkCase st R W Lk (L.cpu s) X1 N t)
    (hpt : p.tm = TM)
    (hag : ∀ y ∈ T, ∀ K : U64, 3528 ≤ K.val → K.val < 3576 → K.val % 8 = 0 →
      L.mem s1 (core.num.U64.wrapping_add y K) = L.mem X (core.num.U64.wrapping_add y K))
    (hfo : localtimer.fire_ok st s1 cpu ct p now = ok true)
    (rN : ∀ k : U64, k.val < 64 → k.val % 8 = 0 → R (core.num.U64.wrapping_add N k))
    (wN : ∀ k : U64, k.val < 64 → k.val % 8 = 0 → k.val ≠ 24 → W (core.num.U64.wrapping_add N k))
    (rL : ∀ y, LocT st T s y → ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ TimerField K.val →
      ¬ GField K.val → R (core.num.U64.wrapping_add y K))
    (wL : ∀ y, LocT st T s y → ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ GateField K.val →
      ¬ TimerField K.val → ¬ GField K.val → K.val ≠ 3328 → K.val ≠ 3336 →
      W (core.num.U64.wrapping_add y K))
    (rS : ∀ p ∈ Scs, L.mem s (scCoreA p) = L.cpu s → ∀ b, Aligned b → InSC p (Z p) b → R b)
    (wS : ∀ p ∈ Scs, L.mem s (scCoreA p) = L.cpu s → ∀ b, Aligned b → InSC p (Z p) b → b.val ≠ p.val + 16 → W b)
    (lkL : ∀ y ∈ T, QueuedState (L.mem s (stA y)) → Lk (L.mem s (blockA y)) → ∀ k : U64,
      (k.val = 3496 ∨ k.val = 3504) → R (core.num.U64.wrapping_add y k) ∧ W (core.num.U64.wrapping_add y k))
    (hLk : Lk N)
    (nRW : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      R (L.nodeAt s (L.cpu s) o) ∧ W (L.nodeAt s (L.cpu s) o))
    (rCD : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hSW : StW st gS T Lk s)
    (rD : R (tdA TM)) (rB : R (tbA TM)) (rDa : ∀ y ∈ T, FootLtArmed st X (L.cpu X) y → R (tdA y))
    (hrmg : timer.remove gS X TM = timer.remove st X TM) :
    ∃ Y aY, timer.fire st ar X a = ok (Y, aY) ∧ timer.fire gS ar X a = timer.fire st ar X a ∧
      TInv st T Cs Ω H Sg Rp Scs Nt Z Ac Y ∧ FireStop st R Y now ∧ L.ksb Y = L.ksb s ∧ L.cpu Y = L.cpu s ∧
      ∃ w ∈ T, (L.actionW Y = sched.ACTION_RESUME_CURRENT ∨ L.actionW Y = w) ∧ FwKeep st T Scs Z X Y w ∧
        Blocked (L.mem X (stA w)) ∧ L.mem X (affA w) = L.cpu s ∧ w ≠ L.curW X ∧
        L.mem Y (stA w) = sched.TS_RUNNING := by
  have hTX' := hTX
  obtain ⟨⟨Q, Rq, hq⟩, -, hXX, -, -⟩ := hTX
  have hN := hq.nodes _ hq.cur
  have eXN : ∀ o, L.nodeAt X (L.cpu X) o = L.nodeAt s (L.cpu s) o := fun o => by rw [cX, nodeAt_of_ksb kX]
  have hNN : N ∈ Nt := by
    have := hXX.2.2.bnd TM hTMT (by rw [eN]; exact hN0); rwa [eN] at this
  -- `remove`
  obtain ⟨X1, eX1, hT1, -, -, tk1, w31⟩ := spec_ex_fd (timer.remove.tf (s0 := X) X TM (TF.start hTX') hTMT)
  have F1 := timer.remove.ibFr X TM hTX' hTMT
  rw [eX1, WP.spec_ok] at F1
  have BA1 : BufAt st T Cs H Sg Scs Z U X1 := hBA.of_fr F1
  have kT1 : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (K.val < 3528 ∨ 3576 ≤ K.val) →
      L.mem X1 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K h1 h2 h3 => (tk1 y hy K h1 h2 h3).trans (kT y hy K h1 h2 h3)
  have kX1 : L.ksb X1 = L.ksb s := w31.1.trans kX
  have cX1 : L.cpu X1 = L.cpu s := w31.2.1.trans cX
  have bX1 : L.mem X1 (boundA TM) = N := by
    rw [← eN]; exact tk1 TM hTMT 3368#u64 (by simp) (by simp) (Or.inl (by simp))
  have hac1 : L.actionW X1 = sched.ACTION_RESUME_CURRENT := by
    rw [← hac]
    unfold LawfulStore.actionW
    rw [w31.2.1, nodeAt_of_ksb w31.1]
    exact w31.mem_eq (nodeAt_aligned hN (by rw [act_val]; omega) (by rw [act_val]))
      (node_not_tw hq (by rw [act_val]; omega) (by rw [act_val]; omega) (by rw [act_val]; omega))
  -- the waking signal
  obtain ⟨gsig, ssig⟩ := wk_sig (badge := L.mem X (tbA TM)) ar hA a hT1 BA1 hNN (hNt N hNN) hAffSc kX1 cX1 kT1
    hac1 (hwk X1 w31) rN wN rL wL rS wS lkL hLk nRW rCD hSW
  obtain ⟨⟨X2, a2⟩, eX2, -⟩ := spec_ex_fd
    (notification.send_signal.tagree hA X1 a N (L.mem X (tbA TM)) hT1 hNN (hNt N hNN) BA1.1 BA1.2)
  obtain ⟨T2, -, k2, c2, w, hwT, act2, kp, wbl, waf, wcur, wrun⟩ := ssig X2 a2 eX2
  have hsg : (if L.mem X1 (boundA TM) != 0#u64 then
      notification.send_signal st ar X1 a (L.mem X1 (boundA TM)) (L.mem X (tbA TM)) else ok (X1, a)) =
      ok (X2, a2) := by
    rw [bX1, if_pos (bne_iff_ne.mpr hN0)]; exact eX2
  have hst : FireStop st R (L.wr X2 (L.nodeAt X2 (L.cpu X2) layout.node.REPROGRAM) 1#u64) now := by
    refine fire_stop_sig hA hTX' hBA hNt (by rw [eTM, hpt]) (by rw [hpt]; exact hne) hag hfo
      (by rw [hpt]; exact eX1) (fun h => by rw [hpt] at h ⊢; rw [bX1] at h ⊢; exact hNN)
      (by rw [hpt]; exact hsg) ?_ rDa
    rw [eXN]; exact (nRW _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])).1
  have hfire : timer.fire st ar X a =
      ok (L.wr X2 (L.nodeAt X2 (L.cpu X2) layout.node.REPROGRAM) 1#u64, a2) :=
    fire_run (R' := R) ar X a (by rw [eTM]; exact hne) (by rw [eTM, hct]; exact hdue) (by rw [eTM]; exact eX1)
      (by rw [eTM]; exact hsg) (by rw [hct]; exact hst)
  have e2N : ∀ o, L.nodeAt X2 (L.cpu X2) o = L.nodeAt s (L.cpu s) o := fun o => by
    rw [c2, nodeAt_of_ksb k2, cX1, nodeAt_of_ksb kX1]
  have gfire : timer.fire gS ar X a = timer.fire st ar X a := by
    refine timer.fire.guard_one ar X a
      (by rw [eXN]; exact (nRW _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).1)
      (by rw [eXN]; exact (nRW _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])).1)
      (by rw [eTM]; exact hne) (by rw [eTM]; exact rD) (by rw [eTM, hct]; exact hdue) (by rw [eTM]; exact rB)
      (by rw [eTM]; exact hrmg) ?_
    rw [eTM]
    intro X1' e1'
    rw [eX1] at e1'
    obtain rfl := ok_inj_ff e1'
    refine ⟨rL TM ⟨hTMT, hTMl⟩ 3368#u64 (by simp) (by simp) (by simp) (by simp [TimerField]) (by simp [GField]),
      fun _ => by rw [bX1]; exact gsig, fun X2' a2' e2' => ?_⟩
    rw [hsg] at e2'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (ok_inj_ff e2')
    refine ⟨by rw [e2N]; exact (nRW _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])).2, ?_⟩
    rw [hct]; exact hst
  -- the state after `fire`
  have hN2 : NodePlaced st T X2 (L.cpu X2) := by rw [c2, cX1, ← cX]; exact hN.ksb (k2.trans (kX1.trans kX.symm))
  have aRP : Aligned (L.nodeAt X2 (L.cpu X2) layout.node.REPROGRAM) :=
    nodeAt_aligned hN2 (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
  have aSA : Aligned (L.nodeAt X2 (L.cpu X2) layout.node.SCHED_ACTION) :=
    nodeAt_aligned hN2 (by rw [act_val]; omega) (by rw [act_val])
  have nRA : L.nodeAt X2 (L.cpu X2) layout.node.REPROGRAM ≠ L.nodeAt X2 (L.cpu X2) layout.node.SCHED_ACTION :=
    nodeAt_ne hN2 (by simp [layout.node.REPROGRAM]) (by rw [act_val]; omega)
      (by rw [act_val]; simp [layout.node.REPROGRAM])
  have eA : L.actionW (L.wr X2 (L.nodeAt X2 (L.cpu X2) layout.node.REPROGRAM) 1#u64) = L.actionW X2 := by
    unfold LawfulStore.actionW
    rw [nodeAt_of_ksb (L.ksb_wr _ _ _), LawfulStore.cpu_wr]
    exact mem_wr_ne' aRP aSA nRA
  have hT := hq.tcbs
  have kY : FwKeep st T Scs Z X (L.wr X2 (L.nodeAt X2 (L.cpu X2) layout.node.REPROGRAM) 1#u64) w := by
    have eRP : L.nodeAt X2 (L.cpu X2) layout.node.REPROGRAM = L.nodeAt X (L.cpu X) layout.node.REPROGRAM := by
      rw [e2N, eXN]
    have e1X : ∀ o, L.nodeAt X1 (L.cpu X1) o = L.nodeAt X (L.cpu X) o := fun o => by
      rw [cX1, nodeAt_of_ksb kX1, eXN]
    refine ⟨fun o ho h8 h16 h56 h104 h112 => ?_, fun y hy K hK h8 hK' h1 h2 hyw => ?_,
      fun c hc hne b hb hin => ?_⟩
    · rw [mem_wr_ne' aRP (nodeAt_aligned hN ho h8) (by
          rw [eRP]; exact nodeAt_ne hN (by simp [layout.node.REPROGRAM]) ho (by simp [layout.node.REPROGRAM]; omega)),
        ← e1X o, kp.1 o ho h8 h16 h56, e1X o]
      exact w31.mem_eq (nodeAt_aligned hN ho h8) (node_not_tw hq ho h104 h112)
    · have hy' := hT y hy
      rw [mem_wr_ne' aRP (field_aligned hy' hK h8) (by
          rw [eRP]; exact node_ne_field hN (by simp [layout.node.REPROGRAM]) hy hy' hK),
        kp.2.1 y hy K hK h8 h1 h2 hyw]
      exact tk1 y hy K hK h8 hK'
    · have ho := hq.omega b (hXX.1.scW c hc b hb hin)
      have e3 : L.mem X1 (scA w) = L.mem X (scA w) := tk1 w hwT 3464#u64 (by simp) (by simp) (Or.inl (by simp))
      rw [mem_wr_ne' aRP hb (fun e => out_ne_node (o := layout.node.REPROGRAM) ho hq.cur hN (by simp [layout.node.REPROGRAM]) (by rw [← eRP, e])),
        kp.2.2 c hc (by rw [e3]; exact hne) b hb hin]
      exact w31.mem_eq hb (out_not_tw hT hq.nodes ho)
  have wfacts : Blocked (L.mem X (stA w)) ∧ L.mem X (affA w) = L.cpu s ∧ w ≠ L.curW X := by
    have e1 : L.mem X1 (stA w) = L.mem X (stA w) := by
      rw [stA_eq]; exact tk1 w hwT 3328#u64 (by simp) (by simp) (Or.inl (by simp))
    have e2 : L.mem X1 (affA w) = L.mem X (affA w) := tk1 w hwT 3520#u64 (by simp) (by simp) (Or.inl (by simp))
    have e3 : L.curW X1 = L.curW X := by
      unfold LawfulStore.curW
      rw [w31.2.1, nodeAt_of_ksb w31.1]
      exact w31.mem_eq (nodeAt_aligned hN (by rw [curth_val]; omega) (by rw [curth_val]))
        (node_not_tw hq (by rw [curth_val]; omega) (by rw [curth_val]; omega) (by rw [curth_val]; omega))
    rw [e1] at wbl; rw [e2] at waf; rw [e3] at wcur
    exact ⟨wbl, waf, wcur⟩
  have rY : L.mem (L.wr X2 (L.nodeAt X2 (L.cpu X2) layout.node.REPROGRAM) 1#u64) (stA w) = sched.TS_RUNNING := by
    rw [stA_eq, mem_wr_ne' aRP (field_aligned (hT w hwT) (by simp) (by simp))
      (node_ne_field hN2 (by simp [layout.node.REPROGRAM]) hwT (hT w hwT) (by simp)), ← stA_eq]
    exact wrun
  refine ⟨_, a2, hfire, gfire, reprogram.tinv T2, hst, ?_, ?_, w, hwT, by rw [eA]; exact act2, kY, wfacts.1,
    wfacts.2.1, wfacts.2.2, rY⟩
  · rw [L.ksb_wr]; exact k2.trans kX1
  · rw [LawfulStore.cpu_wr]; exact c2.trans cX1

end main

end Fl4Proofs.P2
