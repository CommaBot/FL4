/-
# P2 (p2lf): the waking fire tail when the action is the woken thread

* `scacc_of`: an SC of `Scs` whose words this core reads and (but its `REFILL_MAX` word) writes is `ScAcc`.
* **`aw_tail_sw`**: `AwTailG` at the post-`awaken` state `Y` (`AwFacts` relative to the entry state `s`) when the
  action is the woken thread `w`: `aw_of_sw` with the guarded switch block from `schedSw_guard` (`SwAcc` at `Y` from
  the per-class premises at `s`, the VSpace slot words of this core's threads `hSlot`, the kernel root `hKr` and the
  ASID table `hTab`, kept to `Y` by `AwFacts`' kernel-global keep and P1's `AsidOff`) and the tail after it from
  `schedSw_run` + `sw_tail`, with `d` the new current thread: the current thread (facts from `current_ok`), `w`
  (`AwFacts`: `RUNNING`, yield 0, the action's SC active by P1 `BoundInv.act`) or the old head of the highest ready
  queue (`AwFacts`' top facts, queued hence its SC active by `BoundInv.q` / `.sact`); its SC's words at `Y` come from
  P1's `SCsOK` at `Y` (`TInv`), and the switch block (`SWN`) writes none of them.
* `fire_tail_wk2`: `fire_tail_wk` with `hSwT` discharged by `aw_tail_sw`.

* (lvm gen 10) `aw_tail_sw_core` (`hy0`, `VcG`: a new current thread running a VM is the entry's, re-queued and
  chosen again), `fire_tail_wk2_core` (by `fire_wk_aw_core`, `hVc` at every post-`awaken` state with `AwFacts`/`WkV`).
No named premises.
-/
import Fl4Proofs.P2.FootTimerFireSy2
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap
open Fl4Proofs.P2.PathObl (ScAcc rhA tmA RdHead NodeSt bind_guard_congr)

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
variable {A : Type} (ar : machine.Arch A)

theorem scacc_of {s : S} (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) {p : U64} (hp : p ∈ Scs)
    (rS : ∀ b, Aligned b → InSC p (Z p) b → R b)
    (wS : ∀ b, Aligned b → InSC p (Z p) b → b.val ≠ p.val + 16 → W b) : ScAcc R W p (Z p) := by
  obtain ⟨hP, hz⟩ := hO.sc _ hp
  obtain ⟨h8, h128, -⟩ := sc_lo hP hz
  have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
  have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
  refine ⟨rS, fun b ha hb => wS b ha ⟨by have := hb.1; omega, hb.2⟩ (by have := hb.1; omega), ?_⟩
  exact wS _ (by unfold Aligned; rw [hv, hcv]; omega) ⟨by rw [hv]; omega, by rw [hv, hcv]; omega⟩
    (by rw [hv, hcv]; omega)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 64000000 in
/-- **The waking tail when the action is the woken thread, without `current_ok`** (`aw_tail_sw_core`, lvm gen 10):
`aw_tail_sw` with `eok` replaced by the yield fact it used (`hy0`) and the final `vcpu::check` of the entry's current
thread, when it runs a VM and stays (or becomes again) current, by `VcG`. -/
theorem aw_tail_sw_core {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
    (hA : P0.ArchTotal ar) {s Y : S} {aY : A} {now w : U64} {Lk : U64 → Prop}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hok : IrqOk st s) (hAs : AsidOff (L := L) Ω Sg s)
    (gRd : ∀ w, Aligned w → FireRd st T Z s w → R w)
    (gWr : ∀ w, Aligned w → FireWr st T Z s w → w ≠ stA (L.curW s) → W w)
    (hD2 : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME))
    (hAffSc : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t))
    (rL : ∀ y, LocT st T s y → ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ TimerField K.val →
      ¬ GField K.val → R (core.num.U64.wrapping_add y K))
    (wL : ∀ y, LocT st T s y → ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ GateField K.val →
      ¬ TimerField K.val → ¬ GField K.val → K.val ≠ 3328 → K.val ≠ 3336 →
      W (core.num.U64.wrapping_add y K))
    (rS : ∀ p ∈ Scs, L.mem s (scCoreA p) = L.cpu s → ∀ b, Aligned b → InSC p (Z p) b → R b)
    (wS : ∀ p ∈ Scs, L.mem s (scCoreA p) = L.cpu s → ∀ b, Aligned b → InSC p (Z p) b → b.val ≠ p.val + 16 → W b)
    (rCD : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hSW : StW st gS T Lk s)
    (hSlot : ∀ y, LocT st T s y → R (vtA y) ∧ R (core.num.U64.wrapping_add (vtA y) 8#u64))
    (hKr : R (krA (L := L) s)) (hTab : PathObl.RdTab (L := L) R s)
    (eq : localtimer.sched_quiet st s (L.cpu s) = ok true)
    (hy0 : L.mem s (yieldA (L.curW s)) = 0#u64)
    (hF : AwFacts st T Cs Ω H Sg Rp Scs Nt Z Ac R s Y now w)
    (hact : L.actionW Y = w) (hvc : VcG st gS ar T Cs Scs Z s Y) :
    AwTailG st gS ar Y aY := by
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  have hcC : L.cpu s ∈ Cs := h0.cur
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ hcC
  have hcT : L.curW s ∈ T := h0.curT
  have ht' := hT _ hcT
  obtain ⟨haff, hsct, hcore⟩ := hok
  have hXI := hI.2.2.1
  have hS := hI.2.2.2.2
  have hO := hXI.1
  have hcs : L.cscW s ∈ Scs := hXI.2.2.cur
  have hcq : SCq st s Ω (L.cscW s) (Z (L.cscW s)) := scq_of hO hS hcs
  have hact0 : L.actionW s = sched.ACTION_RESUME_CURRENT := sq_true eq
  have hsc0 : L.mem s (scA (L.curW s)) ≠ 0#u64 := hI.2.1.resume (hact0.trans resume_val)
  have hAc : L.cscW s ∈ Ac := by
    rw [← hsct]
    exact hI.2.1.sact _ hcT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hact0.trans resume_val, rfl⟩))))) hsc0
  have hmx0 : L.rmax s (L.cscW s) ≠ 0#u64 := (hS.act _ hcs).1 hAc
  obtain ⟨TY, kY, cY, nY, tY, scY, -, hstY, -, hwT, wbl, waff, wcur, -, hstw, hyw, htop, hout⟩ := hF
  have hBY := TY.bxi
  obtain ⟨⟨Q, Rq, hq⟩, hBd, hXY, -, hSY⟩ := hBY
  have eYN : ∀ o, L.nodeAt Y (L.cpu Y) o = L.nodeAt s (L.cpu s) o := fun o => by rw [cY, nodeAt_of_ksb kY]
  have hNY : NodePlaced st T Y (L.cpu Y) := by rw [cY]; exact hN.ksb kY
  have hcCY : L.cpu Y ∈ Cs := by rw [cY]; exact hcC
  -- the guarded store: what it admits
  have nR : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o) := fun o h1 h2 =>
    gRd _ (nodeAt_aligned hN h1 h2) (Or.inl (Or.inl ⟨o, h1, h2, rfl⟩))
  have nW : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → W (L.nodeAt s (L.cpu s) o) := fun o h1 h2 =>
    gWr _ (nodeAt_aligned hN h1 h2) (Or.inl (Or.inl ⟨o, h1, h2, rfl⟩)) (fun e => by
      rw [stA_eq] at e; exact node_ne_field hN h1 hcT ht' (by simp) e)
  have rK : ∀ y, LocT st T s y → ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 →
      ¬ (3528 ≤ K.val ∧ K.val ≤ 3568) → K.val ≠ 3496 → K.val ≠ 3504 → R (core.num.U64.wrapping_add y K) :=
    fun y hy K h1 h2 h3 h4 h5 h6 => rL y hy K h1 h2 h3 (by unfold TimerField; exact h4) (by unfold GField; omega)
  have wK : ∀ y, LocT st T s y → ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ GateField K.val →
      ¬ (3528 ≤ K.val ∧ K.val ≤ 3568) → K.val ≠ 3496 → K.val ≠ 3504 → K.val ≠ 3328 → K.val ≠ 3336 →
      W (core.num.U64.wrapping_add y K) :=
    fun y hy K h1 h2 h3 hg h4 h5 h6 h7 h8 =>
      wL y hy K h1 h2 h3 hg (by unfold TimerField; exact h4) (by unfold GField; omega) h7 h8
  have coreS : ∀ y ∈ T, L.mem s (affA y) = L.cpu s → L.mem s (scA y) ≠ 0#u64 →
      L.mem s (scCoreA (L.mem s (scA y))) = L.cpu s := fun y hy ha h0' => (hAffSc y hy h0').trans ha
  -- frames from `AwFacts`
  have scaY : ∀ y ∈ T, L.mem Y (scA y) = L.mem s (scA y) := fun y hy => by
    rw [scA_eq]; exact tY y hy _ (by simp) (by simp) (Or.inl (by simp)) (by simp) (by simp) (fun _ => by simp)
  have affY : ∀ y ∈ T, L.mem Y (affA y) = L.mem s (affA y) := fun y hy => by
    unfold affA; exact tY y hy _ (by simp) (by simp) (Or.inl (by simp)) (by simp) (by simp) (fun _ => by simp)
  have yldY : ∀ y ∈ T, L.mem Y (yieldA y) = L.mem s (yieldA y) := fun y hy => by
    unfold yieldA; exact tY y hy _ (by simp) (by simp) (Or.inl (by simp)) (by simp) (by simp) (fun _ => by simp)
  have inqY : ∀ y ∈ T, L.mem Y (inqA y) = L.mem s (inqA y) := fun y hy => by
    unfold inqA; exact tY y hy _ (by simp) (by simp) (Or.inr (by simp)) (by simp) (by simp) (fun _ => by simp)
  have stY : ∀ y ∈ T, y ≠ w → L.mem Y (stA y) = L.mem s (stA y) := fun y hy hyw => by
    rw [stA_eq]
    exact tY y hy _ (by simp) (by simp) (Or.inl (by simp)) (by simp) (by simp) (fun e => absurd e hyw)
  have hcurY : L.curW Y = L.curW s := by
    unfold LawfulStore.curW
    rw [eYN]
    exact nY _ (by rw [curth_val]; omega) (by rw [curth_val]) (by rw [curth_val]; omega)
      (by rw [curth_val]; omega) (by rw [curth_val]; omega) (by rw [curth_val]; omega) (by rw [curth_val]; omega)
      (by rw [curth_val]; omega) (by rw [curth_val]; omega)
  have hcsY : L.cscW Y = L.cscW s := by
    unfold LawfulStore.cscW LawfulStore.nodeA
    rw [eYN]
    exact nY _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have hneB : ∀ y ∈ T, y ≠ w → L.mem s (scA y) ≠ 0#u64 → L.mem s (scA y) ≠ L.mem s (scA w) := by
    intro y hy hyw hs0 e
    have b1 := (hXI.2.2.bound y hy hs0).2.1
    have hw0 : L.mem s (scA w) ≠ 0#u64 := by rw [← e]; exact hs0
    have b2 := (hXI.2.2.bound w hwT hw0).2.1
    rw [e] at b1
    exact hyw (b1.symm.trans b2)
  have hcw : L.cscW s ≠ L.mem s (scA w) := by
    rw [← hsct]; exact hneB _ hcT (fun e => wcur e.symm) hsc0
  have rmY : L.rmax Y (L.cscW s) = L.rmax s (L.cscW s) := by
    unfold LawfulStore.rmax; rw [scY _ hcs hcw _ hcq.2.2.2.2 hcq.2.2.2.1]
  -- facts at `Y` for the guarded switch block
  have hwT' := hT w hwT
  have hwaY : L.mem Y (affA w) = L.cpu Y := by rw [affY _ hwT, cY]; exact waff
  have hcaY : L.mem Y (affA (L.curW Y)) = L.cpu Y := by rw [hcurY, affY _ hcT, cY]; exact haff
  have hwc : w ≠ L.curW Y := by rw [hcurY]; exact wcur
  have hwq : (L.mem Y (inqA w) &&& sched.Q_QUEUED) = 0#u64 := by
    rw [inqY _ hwT]
    by_contra hne
    have hm := (h0.queued w hwT).1 hne
    exact not_runnable_of_blocked wbl
      (h0.runQ _ (h0.aff w hwT) _ (h0.prio w hwT) _ hm)
  have hdtv : (layout.ks.DOMAIN_TIME : U64).val < 13568 := by simp [layout.ks.DOMAIN_TIME]
  have hdt8 : (layout.ks.DOMAIN_TIME : U64).val % 8 = 0 := by simp [layout.ks.DOMAIN_TIME]
  have hdtY : L.mem Y (core.num.U64.wrapping_add (L.ksb Y) layout.ks.DOMAIN_TIME) ≠ 0#u64 := by
    rw [kY, hout _ (ks_aligned hN hdtv hdt8) (hS.ksΩ _ hdtv hdt8) (fun hsg => by
      have := hS.ks _ hsg
      rw [ks_word_val hN hdtv] at this
      simp [layout.ks.DOMAIN_TIME] at this
      omega)]
    exact sq_dt eq
  have hAtE : ∀ hi : U64, hi.val < 2048 → L.mem Y (atAF (L.ksb s) hi) = L.mem s (atAF (L.ksb s) hi) :=
    fun hi hhi => hout _ (h0.omega _ (hAs hi hhi).1).1 (hAs hi hhi).1 (hAs hi hhi).2.1
  have hAtY : ∀ hi : U64, hi.val < 2048 → OutsideObjs st T Cs Y (atAF (L.ksb Y) hi) := fun hi hhi => by
    rw [kY]; exact (h0.omega _ (hAs hi hhi).1).ksb kY
  have hlocY : ∀ y ∈ T, L.mem Y (affA y) = L.cpu Y → LocT st T s y := fun y hy ha =>
    ⟨hy, by rw [← affY y hy, ha, cY]⟩
  have hacc : SwAcc st R W T Y := by
    refine ⟨fun o h1 h2 => by rw [eYN]; exact ⟨nR o h1 h2, nW o h1 h2⟩, fun y hy ha => ?_, by rw [kY]; exact rCD,
      by rw [kY]; exact hD2, by unfold krA; rw [kY]; exact hKr, fun hi hhi => ?_⟩
    · have hl := hlocY y hy ha
      have n1 : R (nextA .Sched y) := by
        rw [nextA_eq']
        exact rK y hl (nextOff .Sched) (by simp [nextOff]) (by simp [nextOff]) (by simp [nextOff])
          (by simp [nextOff]) (by simp [nextOff]) (by simp [nextOff])
      have n2 : W (nextA .Sched y) := by
        rw [nextA_eq']
        exact wK y hl (nextOff .Sched) (by simp [nextOff]) (by simp [nextOff]) (by simp [nextOff])
          (by unfold GateField; simp [nextOff]) (by simp [nextOff]) (by simp [nextOff]) (by simp [nextOff])
          (by simp [nextOff]) (by simp [nextOff])
      have p1 : R (prevA .Sched y) := by
        rw [prevA_eq']
        exact rK y hl (prevOff .Sched) (by simp [prevOff]) (by simp [prevOff]) (by simp [prevOff])
          (by simp [prevOff]) (by simp [prevOff]) (by simp [prevOff])
      have p2 : W (prevA .Sched y) := by
        rw [prevA_eq']
        exact wK y hl (prevOff .Sched) (by simp [prevOff]) (by simp [prevOff]) (by simp [prevOff])
          (by unfold GateField; simp [prevOff]) (by simp [prevOff]) (by simp [prevOff]) (by simp [prevOff])
          (by simp [prevOff]) (by simp [prevOff])
      have i1 : R (inqA y) := rK y hl 3592#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      have i2 : W (inqA y) := wK y hl 3592#u64 (by simp) (by simp) (by simp) (by unfold GateField; simp) (by simp)
        (by simp) (by simp) (by simp) (by simp)
      have a1 : R (affA y) := rK y hl 3520#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      have d1 : R (domA y) := rK y hl 3432#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      have q1 : R (prioA y) := rK y hl 3448#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      exact ⟨i1, i2, a1, d1, q1, n1, n2, p1, p2, (hSlot y hl).1, (hSlot y hl).2⟩
    · rw [kY, hAtE hi hhi]
      refine ⟨(hTab hi hhi).1, fun lo hlo hne => (hTab hi hhi).2 lo hlo hne⟩
  have rMc : R (maxA (L.cscW s)) := rS _ hcs hcore _ hcq.2.2.2.2 hcq.2.2.2.1
  have hlct : LocT st T s (L.curW s) := ⟨hcT, haff⟩
  have hsw : schedSw gS ar Y aY (L.actionW Y) = schedSw st ar Y aY (L.actionW Y) := by
    rw [hact]
    refine schedSw_guard hA Y aY hq hwT hwaY hact hcaY hwc hwq hdtY hAtY hacc ?_ ?_ ?_
    · rw [hcurY, stA_eq]
      exact rK _ hlct _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    · rw [hcurY]; exact rK _ hlct _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    · rw [hcurY, scaY _ hcT, hsct]; exact rMc
  -- the tail after the switch block, for its new current thread `d`
  have key : ∀ X a' d, WritesIn st Y X (SWN st T Y) → L.curW X = d → d ∈ T → L.mem s (affA d) = L.cpu s →
      L.mem Y (yieldA d) = 0#u64 → (L.mem Y (stA d) = sched.TS_RUNNING_VM → d = L.curW s) →
      L.mem s (scA d) ≠ 0#u64 →
      (L.mem s (scA d) = L.cscW s ∨ L.rmax Y (L.mem s (scA d)) ≠ 0#u64) → SwTail st gS ar X a' := by
    intro X a' d hW hcur hd d2 d3 d4 d5 d6
    have hd' := hT d hd
    have hl : LocT st T s d := ⟨hd, d2⟩
    have eXN : ∀ o, L.nodeAt X (L.cpu X) o = L.nodeAt Y (L.cpu Y) o := fun o => by
      rw [hW.2.1, nodeAt_of_ksb hW.1]
    have kXn : ∀ o : U64, o.val < 128 → o.val % 8 = 0 → o.val ≠ 0 → o.val ≠ 16 → o.val ≠ 120 →
        L.mem X (L.nodeAt Y (L.cpu Y) o) = L.mem Y (L.nodeAt Y (L.cpu Y) o) := fun o h1 h2 h3 h4 h5 =>
      hW.mem_eq (nodeAt_aligned hNY (by omega) h2) (swn_node hT hNY (by omega) h3 h4 h5 h1)
    have kXt : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3480 → K.val ≠ 3488 → K.val ≠ 3592 →
        L.mem X (core.num.U64.wrapping_add y K) = L.mem Y (core.num.U64.wrapping_add y K) :=
      fun y hy K h1 h2 h3 h4 h5 => hW.mem_eq (field_aligned (hT y hy) h1 h2) (swn_tcb hT hNY hy h1 h3 h4 h5)
    have kXsc : ∀ p ∈ Scs, ∀ b, Aligned b → InSC p (Z p) b → L.mem X b = L.mem Y b := fun p hp b hb hin => by
      have hΩ := hSY.sub _ ((hSY.all p hp).2.2 b hb hin)
      exact hW.mem_eq hb (swn_out hT hNY hcCY (hq.omega b hΩ))
    have hcsX : L.cscW X = L.cscW s := by
      rw [← hcsY]
      unfold LawfulStore.cscW LawfulStore.nodeA
      rw [eXN]
      exact kXn _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
        (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
    have rmX : L.rmax X (L.cscW s) = L.rmax s (L.cscW s) := by
      rw [← rmY]; unfold LawfulStore.rmax; exact kXsc _ hcs _ hcq.2.2.2.2 hcq.2.2.2.1
    have pX : L.mem X (scA d) = L.mem s (scA d) := by
      rw [← scaY d hd, scA_eq]; exact kXt d hd _ (by simp) (by simp) (by simp) (by simp) (by simp)
    have hpS : L.mem s (scA d) ∈ Scs := (hXI.2.2.bound d hd d5).1
    have scinX : ∀ p ∈ Scs, L.rmax Y p ≠ 0#u64 → SCin st X Ω p (Z p) := fun p hp hm =>
      ⟨((hSY.all p hp).1 hm).agree (fun b hb hin => kXsc p hp b hb hin),
        fun b hb hin => hSY.sub _ ((hSY.all p hp).2.2 b hb hin)⟩
    have outS : ∀ p ∈ Scs, ∀ q ∈ Scs, p ≠ q → ∀ b, InSC p (Z p) b → Outside b q (Z q) := fun p hp q hq' hne b hb => by
      have := hO.scDisj _ hp _ hq' hne
      unfold Outside; unfold InSC at hb; omega
    have P : TailPld (L := L) T Cs Ω X d :=
      ⟨hT, hd, by rw [hW.2.1]; exact hNY.ksb hW.1, by rw [hW.2.1]; exact hcCY,
        fun b hb => (hq.omega b hb).ksb hW.1⟩
    have cX : L.cpu X = L.cpu s := hW.2.1.trans cY
    refine sw_tail_core (gS := gS) ar hA X a' P hcur (zc := Z (L.cscW s)) (zt := Z (L.mem s (scA d))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hcsX]
      exact SCq.agree' hcq (fun b hb hin => (kXsc _ hcs b hb hin).trans (scY _ hcs hcw b hb hin))
    · intro hne
      rw [pX, hcsX] at hne ⊢
      rcases d6 with e | hm
      · exact absurd e hne
      · exact ⟨scinX _ hpS hm, outS _ hpS _ hcs hne⟩
    · intro _
      rw [hcsX, rmX]; exact hmx0
    · intro hne'
      have eR : L.mem X (rhA (L := L) X) = L.mem Y (L.nodeAt Y (L.cpu Y) layout.node.RELEASE_HEAD) := by
        show L.mem X (L.nodeAt X (L.cpu X) _) = _
        rw [eXN]
        exact kXn _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
          (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
          (by simp [layout.node.RELEASE_HEAD])
      rw [eR] at hne' ⊢
      obtain ⟨r1, r2, r3, r4, r5⟩ := rel_facts TY.bxi hne'
      generalize L.mem Y (L.nodeAt Y (L.cpu Y) layout.node.RELEASE_HEAD) = rh at r1 r2 r3 r4 r5 ⊢
      have prX : L.mem X (scA rh) = L.mem Y (scA rh) := by
        rw [scA_eq]; exact kXt rh r1 _ (by simp) (by simp) (by simp) (by simp) (by simp)
      have hrl : LocT st T s rh := hlocY rh r1 r2
      have r3s : L.mem s (scA rh) ≠ 0#u64 := by rw [← scaY rh r1]; exact r3
      rw [prX, pX, hcsX]
      refine ⟨r1, by rw [scA_eq]; exact rK _ hrl _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp),
        Z (L.mem Y (scA rh)), scinX _ r4 r5, fun b hb hin => ?_, fun hne b hb => outS _ r4 _ hcs hne b hb,
        fun hne _ b hb => outS _ r4 _ hpS hne b hb⟩
      rw [scaY rh r1] at hin
      rw [scaY rh r1] at r4
      exact rS _ r4 (coreS rh r1 hrl.2 r3s) b hb hin
    · intro hne'
      have eT : L.mem X (tmA (L := L) X) = L.mem Y (tmA (L := L) Y) := by
        show L.mem X (L.nodeAt X (L.cpu X) _) = L.mem Y (L.nodeAt Y (L.cpu Y) _)
        rw [eXN]
        exact kXn _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
          (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      rw [eT] at hne' ⊢
      exact ⟨(tmin_facts TY hcCY hne').1, (hstY.2 hne').1⟩
    · intro o h1 h2; rw [eXN, eYN]; exact ⟨nR o h1 h2, nW o h1 h2⟩
    · rw [hW.1, kY]; exact hD2
    · rw [hcsX]
      exact scacc_of hO hcs (fun b hb hin => rS _ hcs hcore b hb hin) (fun b hb hin h16 => wS _ hcs hcore b hb hin h16)
    · intro _
      rw [pX]
      have hc' := coreS d hd d2 d5
      exact scacc_of hO hpS (fun b hb hin => rS _ hpS hc' b hb hin) (fun b hb hin h16 => wS _ hpS hc' b hb hin h16)
    · unfold yieldA; rw [kXt d hd _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact d3
    · unfold affA; rw [kXt d hd _ (by simp) (by simp) (by simp) (by simp) (by simp)]
      change L.mem Y (affA d) = _
      rw [affY d hd, d2, cX]
    · exact rK _ hl _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    · rw [stA_eq]; exact rK _ hl _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    · obtain ⟨K, hK, e⟩ := regA_eq hd' (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])
      have hr : layout.reg.FAULT_IP.val < 384 := by simp [layout.reg.FAULT_IP]
      have : K.val < 3328 := by omega
      rw [e]; exact rK _ hl K (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · obtain ⟨K, hK, e⟩ := regA_eq hd' (r := layout.reg.NEXT_IP) (by simp [layout.reg.NEXT_IP])
      have hr : layout.reg.NEXT_IP.val < 384 := by simp [layout.reg.NEXT_IP]
      have : K.val < 3328 := by omega
      rw [e]; exact wK _ hl K (by omega) (by omega) (by omega) (by unfold GateField; omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)
    · rw [scA_eq]; exact rK _ hl _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    · exact rK _ hl _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    · rw [pX]
      obtain ⟨m1, m2, m3⟩ := maxA_facts hO hpS
      exact rS _ hpS (coreS d hd d2 d5) _ m1 ⟨m2, m3⟩
    · intro X' h1 h2
      exact hSW X' d sched.TS_RUNNING hl (by rw [h2, cX]) (fun hq' => absurd hq' (by
        rw [h1]; unfold QueuedState; simp [sched.TS_RESTART])) (by unfold QueuedState; simp [sched.TS_RUNNING])
    · -- lvm gen 10: `d` runs a VM, so it is the entry's current thread (`d4`), and `VcG` applies
      intro hvm s4 a4 w4 hc4 s5 a5 eac
      have hvmY : L.mem Y (stA d) = sched.TS_RUNNING_VM := by
        rw [stA_eq, ← kXt d hd _ (by simp) (by simp) (by simp) (by simp) (by simp), ← stA_eq]; exact hvm
      obtain rfl := d4 hvmY
      have tK : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3480 → K.val ≠ 3488 → K.val ≠ 3592 →
          L.mem s4 (core.num.U64.wrapping_add (L.curW s) K) = L.mem Y (core.num.U64.wrapping_add (L.curW s) K) := by
        intro K hK h8 h1 h2 h3
        rw [← kXt _ hcT K hK h8 h1 h2 h3]
        refine w4.mem_eq (field_aligned hd' hK h8) ?_
        rintro (⟨o, ho', e⟩ | hin | ⟨-, hin⟩)
        · exact node_ne_field hNY ho' hcT hd' hK (by rw [← eXN]; exact e.symm)
        · rw [hcsX] at hin
          exact out_ne_field (h0.omega _ (hcq.2.1 _ (field_aligned hd' hK h8) hin)) hcT hd' hK rfl
        · rw [pX, hsct] at hin
          exact out_ne_field (h0.omega _ (hcq.2.1 _ (field_aligned hd' hK h8) hin)) hcT hd' hK rfl
      have hst4 : L.mem s4 (stA (L.curW s)) = sched.TS_RUNNING_VM := by
        rw [stA_eq, tK _ (by simp) (by simp) (by simp) (by simp) (by simp), ← stA_eq]; exact hvmY
      have hy4 : L.mem s4 (yieldA (L.curW s)) = 0#u64 := by
        unfold yieldA; rw [tK _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact d3
      have eac' := activate_nr ar s4 a4 (by rw [hc4]; exact hy4)
        (by rw [hc4, hst4]; simp [sched.TS_RUNNING_VM, sched.TS_RESTART])
      rw [eac'] at eac
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (ok_inj_ff eac)
      refine hvc (by rw [← stY _ hcT (fun e => wcur e.symm)]; exact hvmY) s4 a4 hc4 (fun b hv => ?_) tK
      rw [w4.mem_eq hv.1.1 ?_]
      · exact hW.mem_eq hv.1.1 (swn_out hT hNY hcCY (hv.1.ksb kY))
      rintro (⟨o, ho', e⟩ | hin | ⟨-, hin⟩)
      · exact out_ne_node hv.1 hcC hN ho' (by rw [e, eXN, eYN])
      · rw [hcsX] at hin; exact hv.2 _ hcs hin
      · rw [pX, hsct] at hin; exact hv.2 _ hcs hin
  refine aw_of_sw (gS := gS) ar Y aY (by rw [eYN]; exact nR _ (by rw [act_val]; omega) (by rw [act_val]))
    (by rw [hact, resume_val]; exact fun e => hwT'.ne0 (by rw [e]; rfl)) hsw ?_
  intro X a' e
  rw [hact] at e
  obtain ⟨hW, -, hcases⟩ := schedSw_run hA Y aY hq hwT hwaY hact (fun _ => hcaY) hdtY e
  rcases hcases with hc | hc | ⟨h, hh, hne, hmax, hc⟩
  · -- the current thread stays
    rw [hcurY] at hc
    refine key X a' _ hW hc hcT haff ?_ ?_ hsc0 (Or.inl hsct)
    · rw [yldY _ hcT]; exact hy0
    · exact fun _ => rfl
  · -- the woken thread
    have hwY0 : L.mem Y (scA w) ≠ 0#u64 := by
      have := hBd.act (by rw [hact]; exact hwT); rwa [hact] at this
    have hAcw : L.mem Y (scA w) ∈ Ac := hBd.sact w hwT (Or.inr (Or.inr (Or.inl hact))) hwY0
    have hwS : L.mem Y (scA w) ∈ Scs := (hXY.2.2.bound w hwT hwY0).1
    refine key X a' w hW hc hwT waff (by rw [yldY _ hwT]; exact hyw)
      (fun h => absurd (hstw.symm.trans h) (by simp [sched.TS_RUNNING, sched.TS_RUNNING_VM]))
      (by rw [← scaY _ hwT]; exact hwY0) (Or.inr ?_)
    rw [← scaY _ hwT]; exact (hSY.act _ hwS).1 hAcw
  · -- the old head of the highest ready queue
    obtain ⟨t1, t2, t3⟩ := htop (Q (L.cpu Y)) (hq.ready _ hq.cur) h hh hne hmax
    have hm := headD_mem hne 0#u64
    generalize (Q (L.cpu Y) h).headD 0#u64 = d at t1 t2 t3 hm hc
    have hd : d ∈ T := hq.memT hq.cur hh hm
    obtain ⟨i1, i2⟩ := hq.inQ _ hq.cur h hh d hm
    have hqd : (L.mem Y (inqA d) &&& sched.Q_QUEUED) ≠ 0#u64 := (hq.queued d hd).2 (by rw [i1, i2]; exact hm)
    have hdw : d ≠ w := fun e => by rw [e] at hqd; exact hqd hwq
    have hdY0 : L.mem Y (scA d) ≠ 0#u64 := hBd.q d hd hqd
    have hAcd : L.mem Y (scA d) ∈ Ac := hBd.sact d hd (Or.inl hqd) hdY0
    have hdS : L.mem Y (scA d) ∈ Scs := (hXY.2.2.bound d hd hdY0).1
    refine key X a' d hW hc hd t3 (by rw [yldY _ hd]; exact t1)
      (fun h => absurd (by rw [← stY _ hd hdw]; exact h) t2)
      (by rw [← scaY _ hd]; exact hdY0) (Or.inr ?_)
    rw [← scaY _ hd]; exact (hSY.act _ hdS).1 hAcd

/-- **The waking tail when the action is the woken thread** (module docstring). -/
theorem aw_tail_sw {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
    (hA : P0.ArchTotal ar) {s Y : S} {aY : A} {now w : U64} {Lk : U64 → Prop}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hok : IrqOk st s) (hAs : AsidOff (L := L) Ω Sg s)
    (gRd : ∀ w, Aligned w → FireRd st T Z s w → R w)
    (gWr : ∀ w, Aligned w → FireWr st T Z s w → w ≠ stA (L.curW s) → W w)
    (hD2 : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME))
    (hAffSc : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t))
    (rL : ∀ y, LocT st T s y → ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ TimerField K.val →
      ¬ GField K.val → R (core.num.U64.wrapping_add y K))
    (wL : ∀ y, LocT st T s y → ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ GateField K.val →
      ¬ TimerField K.val → ¬ GField K.val → K.val ≠ 3328 → K.val ≠ 3336 →
      W (core.num.U64.wrapping_add y K))
    (rS : ∀ p ∈ Scs, L.mem s (scCoreA p) = L.cpu s → ∀ b, Aligned b → InSC p (Z p) b → R b)
    (wS : ∀ p ∈ Scs, L.mem s (scCoreA p) = L.cpu s → ∀ b, Aligned b → InSC p (Z p) b → b.val ≠ p.val + 16 → W b)
    (rCD : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hSW : StW st gS T Lk s)
    (hSlot : ∀ y, LocT st T s y → R (vtA y) ∧ R (core.num.U64.wrapping_add (vtA y) 8#u64))
    (hKr : R (krA (L := L) s)) (hTab : PathObl.RdTab (L := L) R s)
    (eq : localtimer.sched_quiet st s (L.cpu s) = ok true)
    (eok : localtimer.current_ok st s (L.cpu s) (L.curW s) (L.cscW s) = ok true)
    (hF : AwFacts st T Cs Ω H Sg Rp Scs Nt Z Ac R s Y now w)
    (hact : L.actionW Y = w) :
    AwTailG st gS ar Y aY := by
  obtain ⟨hmr, -, -⟩ := current_ok_true eok
  obtain ⟨-, -, hnvm, -⟩ := may_run_here_true hmr
  exact aw_tail_sw_core ar hA hI hok hAs gRd gWr hD2 hAffSc rL wL rS wS rCD hSW hSlot hKr hTab eq (mrh_yield hmr) hF
    hact (fun h => absurd h hnvm)

set_option maxHeartbeats 4000000 in
/-- **The waking fire tail**, its action-`w` tail by `aw_tail_sw` (module docstring). -/
theorem fire_tail_wk2 {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
    (hA : P0.ArchTotal ar) {s s1 s2 s3 : S} {a a1 a2 a3 : A} {mx irq now i2 : U64} {x : Bool}
    {tip p : localtimer.TimerIrqPlan}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (hok : IrqOk st s)
    (gRd : ∀ w, Aligned w → FireRd st T Z s w → R w)
    (gWr : ∀ w, Aligned w → FireWr st T Z s w → w ≠ stA (L.curW s) → W w)
    (hD2 : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME))
    (hwS : ∀ X, L.mem X (stA (L.curW s)) = sched.TS_RESTART → L.mem X (affA (L.curW s)) = L.cpu s →
      gS.write X (stA (L.curW s)) sched.TS_RUNNING = st.write X (stA (L.curW s)) sched.TS_RUNNING)
    (hwH : ∀ X y v, y ∈ T → FootLtArmed st s (L.cpu s) y →
      (L.mem X (tdA y) ≠ 0#u64 → (L.mem X (thA y)).val >>> 8 = (L.cpu s).val ∧ v.val >>> 8 = (L.cpu s).val) →
      gS.write X (thA y) v = st.write X (thA y) v)
    (hwD : ∀ X y v, y ∈ T → FootLtArmed st s (L.cpu s) y → L.mem X (affA y) = L.cpu s →
      L.mem s (affA y) = L.cpu s →
      (L.mem X (tdA y) ≠ 0#u64 ∨ v ≠ 0#u64 → (L.mem X (thA y)).val >>> 8 = (L.cpu s).val) →
      gS.write X (tdA y) v = st.write X (tdA y) v)
    (hWk : ¬ NoWake st s) {Lk : U64 → Prop} {U : Set U64}
    (hAffSc : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t))
    (rL : ∀ y, LocT st T s y → ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ TimerField K.val →
      ¬ GField K.val → R (core.num.U64.wrapping_add y K))
    (wL : ∀ y, LocT st T s y → ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ GateField K.val →
      ¬ TimerField K.val → ¬ GField K.val → K.val ≠ 3328 → K.val ≠ 3336 →
      W (core.num.U64.wrapping_add y K))
    (rS : ∀ p ∈ Scs, L.mem s (scCoreA p) = L.cpu s → ∀ b, Aligned b → InSC p (Z p) b → R b)
    (wS : ∀ p ∈ Scs, L.mem s (scCoreA p) = L.cpu s → ∀ b, Aligned b → InSC p (Z p) b → b.val ≠ p.val + 16 → W b)
    (lkL : ∀ y ∈ T, QueuedState (L.mem s (stA y)) → Lk (L.mem s (blockA y)) → ∀ k : U64,
      (k.val = 3496 ∨ k.val = 3504) → R (core.num.U64.wrapping_add y k) ∧ W (core.num.U64.wrapping_add y k))
    (rCD : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hSW : StW st gS T Lk s)
    (hLkN : Lk p.ntfn) (hLkE : p.ep ≠ 0#u64 → Lk p.ep)
    (wNt : ∀ k : U64, k.val < 64 → k.val % 8 = 0 → k.val ≠ 24 → W (core.num.U64.wrapping_add p.ntfn k))
    (rwE : p.ep ≠ 0#u64 → ∀ k : U64, k.val < 16 → k.val % 8 = 0 →
      R (core.num.U64.wrapping_add p.ep k) ∧ W (core.num.U64.wrapping_add p.ep k))
    (wRt : p.reply ≠ 0#u64 → W (rTcbA p.reply))
    (etip : localtimer.plan_objects st s = ok tip) (eb : localtimer.same_plan tip p = ok true)
    (eq : localtimer.sched_quiet st s (L.cpu s) = ok true)
    (eok : localtimer.current_ok st s (L.cpu s) (L.curW s) (L.cscW s) = ok true)
    (eu : sched.update_timestamp st ar s a = ok (s1, a1)) (enow : sched.cur_time st s1 = ok now)
    (erel : localtimer.release_due st s1 (L.cpu s) = ok false) (ei2 : sched.consumed st s1 = ok i2)
    (eb4 : sporadic.sufficient st ar s1 a1 (L.cscW s) i2 = ok true)
    (edue : localtimer.timer_due st s1 (L.cpu s) now = ok true)
    (efo : localtimer.fire_ok st s1 (L.cpu s) (L.curW s) p now = ok true)
    (ecb : sched.check_budget st ar s1 a1 = ok (x, s2, a2))
    (emx : layout.irq.MAX = ok mx) (hle : ¬ irq > mx)
    (ei1 : interrupt.irq_state st s irq = ok interrupt.IRQ_TIMER)
    (ehi : interrupt.handle_interrupt st ar s2 a2 irq = ok (s3, a3))
    (hBA : BufAt st T Cs H Sg Scs Z U s3)
    (hAs : AsidOff (L := L) Ω Sg s)
    (hSlot : ∀ y, LocT st T s y → R (vtA y) ∧ R (core.num.U64.wrapping_add (vtA y) 8#u64))
    (hKr : R (krA (L := L) s)) (hTab : PathObl.RdTab (L := L) R s) :
    FireTailG st gS ar s3 a3 :=
  fire_wk_aw ar hA hI hNt hok gRd gWr hD2 hwS hwH hwD hWk hAffSc rL wL rS wS lkL rCD hSW hLkN hLkE wNt rwE wRt etip
    eb eq eok eu enow erel ei2 eb4 edue efo ecb emx hle ei1 ehi hBA (fun Y aY w haw hF =>
      hF.2.2.2.2.2.2.2.2.2.2.2.2.2.1.elim
        (fun hact => aw_resume ar hA hI hok gRd gWr hD2 hwS eq eok hF hact)
        (fun hact => aw_tail_sw ar hA hI hok hAs gRd gWr hD2 hAffSc rL wL rS wS rCD hSW hSlot hKr hTab eq eok
          hF hact))


set_option maxHeartbeats 4000000 in
/-- **The waking fire tail without `current_ok`** (`fire_tail_wk2_core`, lvm gen 10): `fire_tail_wk2` with `eok`
replaced by the yield fact (`hy0`), the current thread's `STATE` write asked only when it is in `RESTART` at `s`,
and the final `vcpu::check` of a current thread running a VM by `VcG` at every post-`awaken` state with `AwFacts`
and `WkV` (`hVc`); by `fire_wk_aw_core`, `aw_resume_core`, `aw_tail_sw_core`. -/
theorem fire_tail_wk2_core {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
    (hA : P0.ArchTotal ar) {s s1 s2 s3 : S} {a a1 a2 a3 : A} {mx irq now i2 : U64} {x : Bool}
    {tip p : localtimer.TimerIrqPlan}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (hok : IrqOk st s)
    (gRd : ∀ w, Aligned w → FireRd st T Z s w → R w)
    (gWr : ∀ w, Aligned w → FireWr st T Z s w → w ≠ stA (L.curW s) → W w)
    (hD2 : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME))
    (hwS : L.mem s (stA (L.curW s)) = sched.TS_RESTART → ∀ X, L.mem X (stA (L.curW s)) = sched.TS_RESTART →
      L.mem X (affA (L.curW s)) = L.cpu s →
      gS.write X (stA (L.curW s)) sched.TS_RUNNING = st.write X (stA (L.curW s)) sched.TS_RUNNING)
    (hwH : ∀ X y v, y ∈ T → FootLtArmed st s (L.cpu s) y →
      (L.mem X (tdA y) ≠ 0#u64 → (L.mem X (thA y)).val >>> 8 = (L.cpu s).val ∧ v.val >>> 8 = (L.cpu s).val) →
      gS.write X (thA y) v = st.write X (thA y) v)
    (hwD : ∀ X y v, y ∈ T → FootLtArmed st s (L.cpu s) y → L.mem X (affA y) = L.cpu s →
      L.mem s (affA y) = L.cpu s →
      (L.mem X (tdA y) ≠ 0#u64 ∨ v ≠ 0#u64 → (L.mem X (thA y)).val >>> 8 = (L.cpu s).val) →
      gS.write X (tdA y) v = st.write X (tdA y) v)
    (hWk : ¬ NoWake st s) {Lk : U64 → Prop} {U : Set U64}
    (hAffSc : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t))
    (rL : ∀ y, LocT st T s y → ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ TimerField K.val →
      ¬ GField K.val → R (core.num.U64.wrapping_add y K))
    (wL : ∀ y, LocT st T s y → ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ GateField K.val →
      ¬ TimerField K.val → ¬ GField K.val → K.val ≠ 3328 → K.val ≠ 3336 →
      W (core.num.U64.wrapping_add y K))
    (rS : ∀ p ∈ Scs, L.mem s (scCoreA p) = L.cpu s → ∀ b, Aligned b → InSC p (Z p) b → R b)
    (wS : ∀ p ∈ Scs, L.mem s (scCoreA p) = L.cpu s → ∀ b, Aligned b → InSC p (Z p) b → b.val ≠ p.val + 16 → W b)
    (lkL : ∀ y ∈ T, QueuedState (L.mem s (stA y)) → Lk (L.mem s (blockA y)) → ∀ k : U64,
      (k.val = 3496 ∨ k.val = 3504) → R (core.num.U64.wrapping_add y k) ∧ W (core.num.U64.wrapping_add y k))
    (rCD : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hSW : StW st gS T Lk s)
    (hLkN : Lk p.ntfn) (hLkE : p.ep ≠ 0#u64 → Lk p.ep)
    (wNt : ∀ k : U64, k.val < 64 → k.val % 8 = 0 → k.val ≠ 24 → W (core.num.U64.wrapping_add p.ntfn k))
    (rwE : p.ep ≠ 0#u64 → ∀ k : U64, k.val < 16 → k.val % 8 = 0 →
      R (core.num.U64.wrapping_add p.ep k) ∧ W (core.num.U64.wrapping_add p.ep k))
    (wRt : p.reply ≠ 0#u64 → W (rTcbA p.reply))
    (etip : localtimer.plan_objects st s = ok tip) (eb : localtimer.same_plan tip p = ok true)
    (eq : localtimer.sched_quiet st s (L.cpu s) = ok true)
    (hy0 : L.mem s (yieldA (L.curW s)) = 0#u64)
    (eu : sched.update_timestamp st ar s a = ok (s1, a1)) (enow : sched.cur_time st s1 = ok now)
    (erel : localtimer.release_due st s1 (L.cpu s) = ok false) (ei2 : sched.consumed st s1 = ok i2)
    (eb4 : sporadic.sufficient st ar s1 a1 (L.cscW s) i2 = ok true)
    (edue : localtimer.timer_due st s1 (L.cpu s) now = ok true)
    (efo : localtimer.fire_ok st s1 (L.cpu s) (L.curW s) p now = ok true)
    (ecb : sched.check_budget st ar s1 a1 = ok (x, s2, a2))
    (emx : layout.irq.MAX = ok mx) (hle : ¬ irq > mx)
    (ei1 : interrupt.irq_state st s irq = ok interrupt.IRQ_TIMER)
    (ehi : interrupt.handle_interrupt st ar s2 a2 irq = ok (s3, a3))
    (hBA : BufAt st T Cs H Sg Scs Z U s3)
    (hAs : AsidOff (L := L) Ω Sg s)
    (hSlot : ∀ y, LocT st T s y → R (vtA y) ∧ R (core.num.U64.wrapping_add (vtA y) 8#u64))
    (hKr : R (krA (L := L) s)) (hTab : PathObl.RdTab (L := L) R s)
    (hVc : ∀ Y now w, AwFacts st T Cs Ω H Sg Rp Scs Nt Z Ac R s Y now w →
      WkV st T Cs Ω H s Y (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))) →
      VcG st gS ar T Cs Scs Z s Y) :
    FireTailG st gS ar s3 a3 :=
  fire_wk_aw_core ar hA hI hNt hok gRd gWr hD2 hwH hwD hWk hAffSc rL wL rS wS lkL rCD hSW hLkN hLkE wNt rwE wRt
    etip eb eq eu enow erel ei2 eb4 edue efo ecb emx hle ei1 ehi hBA (fun Y aY w haw hF hV =>
      hF.2.2.2.2.2.2.2.2.2.2.2.2.2.1.elim
        (fun hact => aw_resume_core ar hA hI hok gRd gWr hD2 hwS eq hy0 hF hact (hVc Y _ w hF hV))
        (fun hact => aw_tail_sw_core ar hA hI hok hAs gRd gWr hD2 hAffSc rL wL rS wS rCD hSW hSlot hKr hTab eq hy0
          hF hact (hVc Y _ w hF hV)))

end main

end Fl4Proofs.P2
