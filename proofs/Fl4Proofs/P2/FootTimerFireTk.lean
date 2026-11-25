/-
# P2 (p2lf): the waking fire case's tail when the action stays `RESUME_CURRENT`

* `aw_resume`: `AwTailG` at the state `Y` after `awaken` (waking case, `AwFacts` relative to the entry state `s`)
  when the action is `RESUME_CURRENT`: `aw_tail_resume` with its facts at `Y` from `AwFacts`' frames (node words,
  TCB words of every thread but the woken one's STATE / badge / fault, SC words of every SC but the woken thread's)
  and the facts at `s` (`current_ok`, `sched_quiet`, `BXI`); the current SC is not the woken thread's (SC back-
  pointers, P1 `XInv.bound`), and neither is the release head's (it is runnable, the woken thread blocked).
* `fire_tail_wk`: `fire_wk_aw` with its tail discharged by `aw_resume` when the action is `RESUME_CURRENT`; the tail
  when the action is the woken thread is asked as `hSwT` (`SwTailP`: at every post-`awaken` state with `AwFacts`
  whose action is the woken thread).

No named premises.
-/
import Fl4Proofs.P2.FootTimerFireAw
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap
open Fl4Proofs.P2.PathObl (ScAcc rhA tmA RdHead NodeSt bind_guard_congr)

section defs

/-- **The waking tail when the action is the woken thread** (the remaining step of the waking fire case): at every
state `Y` with `AwFacts` relative to the entry state `s` whose action is the woken thread `w`, the tail after
`awaken` (`AwTailG`) on `gS` is the real one. -/
def SwTailP {S : Type} (st gS : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A) (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac : Set U64) (R : U64 → Prop) (s : S) : Prop :=
  ∀ Y aY w now, AwFacts st T Cs Ω H Sg Rp Scs Nt Z Ac R s Y now w → L.actionW Y = w → AwTailG st gS ar Y aY

end defs

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
variable {A : Type} (ar : machine.Arch A)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 16000000 in
/-- **The waking tail when the action stays `RESUME_CURRENT`** (module docstring). -/
theorem aw_resume {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
    (hA : P0.ArchTotal ar) {s Y : S} {aY : A} {now w : U64}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hok : IrqOk st s)
    (gRd : ∀ w, Aligned w → FireRd st T Z s w → R w)
    (gWr : ∀ w, Aligned w → FireWr st T Z s w → w ≠ stA (L.curW s) → W w)
    (hD2 : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME))
    (hwS : ∀ X, L.mem X (stA (L.curW s)) = sched.TS_RESTART → L.mem X (affA (L.curW s)) = L.cpu s →
      gS.write X (stA (L.curW s)) sched.TS_RUNNING = st.write X (stA (L.curW s)) sched.TS_RUNNING)
    (eq : localtimer.sched_quiet st s (L.cpu s) = ok true)
    (eok : localtimer.current_ok st s (L.cpu s) (L.curW s) (L.cscW s) = ok true)
    (hF : AwFacts st T Cs Ω H Sg Rp Scs Nt Z Ac R s Y now w)
    (hact : L.actionW Y = sched.ACTION_RESUME_CURRENT) :
    AwTailG st gS ar Y aY := by
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  have hcC : L.cpu s ∈ Cs := h0.cur
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ hcC
  have hcT : L.curW s ∈ T := h0.curT
  have ht' := hT _ hcT
  obtain ⟨haff, hsct, -⟩ := hok
  obtain ⟨hmr, -, -⟩ := current_ok_true eok
  obtain ⟨-, -, hnvm, -⟩ := may_run_here_true hmr
  have hy0 : L.mem s (yieldA (L.curW s)) = 0#u64 := mrh_yield hmr
  have hX := hI.2.2.1
  have hS := hI.2.2.2.2
  have hO := hX.1
  have hcs : L.cscW s ∈ Scs := hX.2.2.cur
  have hcq : SCq st s Ω (L.cscW s) (Z (L.cscW s)) := scq_of hO hS hcs
  have hact0 : L.actionW s = sched.ACTION_RESUME_CURRENT := sq_true eq
  have hsc0 : L.mem s (scA (L.curW s)) ≠ 0#u64 := hI.2.1.resume (hact0.trans resume_val)
  have hAc : L.cscW s ∈ Ac := by
    rw [← hsct]
    exact hI.2.1.sact _ hcT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hact0.trans resume_val, rfl⟩))))) hsc0
  have hmx0 : L.rmax s (L.cscW s) ≠ 0#u64 := (hS.act _ hcs).1 hAc
  obtain ⟨TY, kY, cY, nY, tY, scY, -, hstY, -, hwT, wbl, -, wcur, -, -, -⟩ := hF
  have eYN : ∀ o, L.nodeAt Y (L.cpu Y) o = L.nodeAt s (L.cpu s) o := fun o => by rw [cY, nodeAt_of_ksb kY]
  have hNY : NodePlaced st T Y (L.cpu Y) := by rw [cY]; exact hN.ksb kY
  have hcCY : L.cpu Y ∈ Cs := by rw [cY]; exact hcC
  -- the guarded store: what it admits (as `fire_tail_nw`)
  have nR : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o) := fun o h1 h2 =>
    gRd _ (nodeAt_aligned hN h1 h2) (Or.inl (Or.inl ⟨o, h1, h2, rfl⟩))
  have nW : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → W (L.nodeAt s (L.cpu s) o) := fun o h1 h2 =>
    gWr _ (nodeAt_aligned hN h1 h2) (Or.inl (Or.inl ⟨o, h1, h2, rfl⟩)) (fun e => by
      rw [stA_eq] at e; exact node_ne_field hN h1 hcT ht' (by simp) e)
  have cR : ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → (K.val < 3528 ∨ 3576 ≤ K.val) →
      K.val ≠ 3496 → K.val ≠ 3504 → R (core.num.U64.wrapping_add (L.curW s) K) := fun K h1 h2 h3 h4 h5 h6 =>
    gRd _ (field_aligned ht' h2 h3) (Or.inl (Or.inr (Or.inl ⟨K, h1, h2, h3, h4, h5, h6, rfl⟩)))
  have cW : ∀ K : U64, 256 ≤ K.val → K.val < 3328 → K.val % 8 = 0 → W (core.num.U64.wrapping_add (L.curW s) K) :=
    fun K h1 h2 h3 =>
    gWr _ (field_aligned ht' (by omega) h3) (Or.inl (Or.inr (Or.inl ⟨K, h1, by omega, h3, rfl⟩))) (fun e => by
      rw [stA_eq] at e
      exact tcb_word_ne ht' ht' (by omega) (by simp) (fun _ h => by simp at h; omega) e)
  have rR : ∀ r : U64, r.val < 384 → R (regA (L.curW s) r) := fun r hr => by
    obtain ⟨K, hK, e⟩ := regA_eq ht' hr
    rw [e]; exact cR K (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have rW : ∀ r : U64, r.val < 384 → W (regA (L.curW s) r) := fun r hr => by
    obtain ⟨K, hK, e⟩ := regA_eq ht' hr
    rw [e]; exact cW K (by omega) (by omega) (by omega)
  have scR : ∀ b, InSC (L.cscW s) (Z (L.cscW s)) b → Aligned b → R b := fun b hb ha =>
    gRd _ ha (Or.inl (Or.inr (Or.inr (Or.inl hb))))
  have scNS : ∀ b, Aligned b → InSC (L.cscW s) (Z (L.cscW s)) b → b ≠ stA (L.curW s) := fun b ha hb e => by
    rw [stA_eq] at e
    exact out_ne_field (h0.omega b (hcq.2.1 b ha hb)) hcT ht' (by simp) (congrArg UScalar.val e).symm
  have hSc : ScAcc R W (L.cscW s) (Z (L.cscW s)) := ⟨fun b ha hb => scR b hb ha, fun b h1 h2 =>
    gWr _ h1 (Or.inl (Or.inr (Or.inr (Or.inl h2)))) (scNS b h1 ⟨by have := h2.1; omega, h2.2⟩),
    gWr _ hcq.2.2.1.2 (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (scNS _ hcq.2.2.1.2 hcq.2.2.1.1)⟩
  have rSt : R (stA (L.curW s)) := by rw [stA_eq]; exact cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rSc : R (scA (L.curW s)) := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rIq : R (inqA (L.curW s)) := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rYt : R (yieldA (L.curW s)) := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  -- frames from `AwFacts`
  have scaY : ∀ y ∈ T, L.mem Y (scA y) = L.mem s (scA y) := fun y hy => by
    rw [scA_eq]; exact tY y hy _ (by simp) (by simp) (Or.inl (by simp)) (by simp) (by simp) (fun _ => by simp)
  have tC : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (K.val < 3528 ∨ 3576 ≤ K.val) → K.val ≠ 3496 →
      K.val ≠ 3504 → L.mem Y (core.num.U64.wrapping_add (L.curW s) K) =
        L.mem s (core.num.U64.wrapping_add (L.curW s) K) :=
    fun K h1 h2 h3 h4 h5 => tY _ hcT K h1 h2 h3 h4 h5 (fun e => absurd e.symm wcur)
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
  -- no runnable thread, nor the current thread, shares `w`'s SC
  have hneB : ∀ y ∈ T, y ≠ w → L.mem s (scA y) ≠ 0#u64 → L.mem s (scA y) ≠ L.mem s (scA w) := by
    intro y hy hyw hs0 e
    have b1 := (hX.2.2.bound y hy hs0).2.1
    have hw0 : L.mem s (scA w) ≠ 0#u64 := by rw [← e]; exact hs0
    have b2 := (hX.2.2.bound w hwT hw0).2.1
    rw [e] at b1
    exact hyw (b1.symm.trans b2)
  have hneR : ∀ y ∈ T, Runnable (L.mem s (stA y)) → L.mem s (scA y) ≠ 0#u64 →
      L.mem s (scA y) ≠ L.mem s (scA w) := fun y hy hrun hs0 =>
    hneB y hy (fun e => by subst e; exact not_runnable_of_blocked wbl hrun) hs0
  have hcw : L.cscW s ≠ L.mem s (scA w) := by
    rw [← hsct]; exact hneB _ hcT (fun e => wcur e.symm) hsc0
  have rhY : L.mem Y (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) :=
    nY _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
  have hy0Y : L.mem Y (yieldA (L.curW Y)) = 0#u64 := by
    rw [hcurY]; unfold yieldA; rw [tC _ (by simp) (by simp) (Or.inl (by simp)) (by simp) (by simp)]; exact hy0
  have hnvmY : L.mem Y (stA (L.curW Y)) ≠ sched.TS_RUNNING_VM := by
    rw [hcurY, stA_eq, tC _ (by simp) (by simp) (Or.inl (by simp)) (by simp) (by simp), ← stA_eq]; exact hnvm
  have haffY : L.mem Y (affA (L.curW Y)) = L.cpu Y := by
    rw [hcurY, cY]; unfold affA; rw [tC _ (by simp) (by simp) (Or.inl (by simp)) (by simp) (by simp)]; exact haff
  refine aw_tail_resume (gS := gS) ar hA Y aY (zc := Z (L.cscW s)) hcCY hNY hT
    (fun b hb => (h0.omega b hb).ksb kY) (by rw [hcurY]; exact hcT)
    (by rw [hcurY, hcsY, scaY _ hcT]; exact hsct)
    (by rw [hcsY]; exact SCq.agree' hcq (fun b hb hin => scY _ hcs hcw b hb hin))
    (by rw [hcsY]; unfold LawfulStore.rmax; rw [scY _ hcs hcw _ hcq.2.2.2.2 hcq.2.2.2.1]; exact hmx0)
    (fun o h1 h2 => by rw [eYN]; exact ⟨nR o h1 h2, nW o h1 h2⟩) (by rw [hcsY]; exact hSc)
    (by rw [kY]; exact hD2) ?_ ?_ hact hy0Y hnvmY haffY
    (by rw [hcurY]; exact rYt) (by rw [hcurY]; exact rSt) (by rw [hcurY]; exact rR _ (by simp [layout.reg.FAULT_IP]))
    (by rw [hcurY]; exact rW _ (by simp [layout.reg.NEXT_IP])) (by rw [hcurY]; exact rSc)
    (by rw [hcurY]; exact rIq) (fun X h1 h2 => by rw [hcurY] at h1 h2 ⊢; rw [cY] at h2; exact hwS X h1 h2)
  · intro hne'
    have hne'' := hne'
    change L.mem Y (L.nodeAt Y (L.cpu Y) layout.node.RELEASE_HEAD) ≠ 0#u64 at hne''
    rw [eYN, rhY] at hne''
    obtain ⟨r1, -, r3, r4, r5⟩ := rel_facts hI hne''
    have hscw := hneR _ r1 (rel_head_run hI hne'') r3
    have hqr := scq_of hO hS r4
    have e0 : L.mem Y (rhA (L := L) Y) = L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) := by
      show L.mem Y (L.nodeAt Y (L.cpu Y) _) = _
      rw [eYN, rhY]
    rw [e0, scaY _ r1, hcsY]
    refine ⟨_, r1, gRd _ (by rw [scA_eq]; exact field_aligned (hT _ r1) (by simp) (by simp))
      (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne'', Or.inl rfl⟩))))),
      SCq.agree' hqr (fun b hb hin => scY _ r4 hscw b hb hin), ?_,
      fun b hb ha => gRd _ ha (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne'', Or.inr hb⟩))))),
      fun hn b hb => ?_, fun e => by rw [e]⟩
    · unfold LawfulStore.rmax
      rw [scY _ r4 hscw _ hqr.2.2.2.2 hqr.2.2.2.1]; exact r5
    · have := hO.scDisj _ r4 _ hcs hn
      unfold Outside; unfold InSC at hb; omega
  · intro hne'
    exact ⟨(tmin_facts TY hcCY hne').1, (hstY.2 hne').1⟩

set_option maxHeartbeats 4000000 in
/-- **The waking fire tail**, the action-`w` tail asked as `hSwT` (module docstring). -/
theorem fire_tail_wk {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
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
    (hSwT : SwTailP st gS ar T Cs Ω H Sg Rp Scs Nt Z Ac R s) :
    FireTailG st gS ar s3 a3 :=
  fire_wk_aw ar hA hI hNt hok gRd gWr hD2 hwS hwH hwD hWk hAffSc rL wL rS wS lkL rCD hSW hLkN hLkE wNt rwE wRt etip
    eb eq eok eu enow erel ei2 eb4 edue efo ecb emx hle ei1 ehi hBA (fun Y aY w haw hF =>
      hF.2.2.2.2.2.2.2.2.2.2.2.2.2.1.elim
        (fun hact => aw_resume ar hA hI hok gRd gWr hD2 hwS eq eok hF hact)
        (fun hact => hSwT Y aY w now hF hact))

end main

end Fl4Proofs.P2
