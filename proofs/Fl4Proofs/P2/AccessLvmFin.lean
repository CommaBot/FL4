/-
# P2 (line lvm, gen 5): `local_vm_exit`'s `schedule` guard, the quiet `vcpu.check`, and the report's frame

Pieces `VexitAcc` (`AccessLvmExit`) needs at concrete states:

* **`sched.schedule.guard_resumeP`**: `schedule` on a guarded store at a resume state (action
  `RESUME_CURRENT`, nothing due, the current thread on the current SC), from P1 facts at that state: the existing
  P2 schedule guards composed (`sched.schedule.guard_nodue`, `FootTimerSetG`, with its `hsw` / `hfr` from
  `resume_hsw_hfr`, `FootTimerSetR`, as `FootTimerIrqAcc`'s quiet walk uses them). This is `localvm.finish.guardP`'s
  `hsch` for the exit path, whose `sched_quiet` / `awaken_quiet` checks give the resume action and no due timer.
* **`vcpu.check.guard_vmq`**: `vcpu.check` of a thread still in `TS_RUNNING_VM` with its VCPU's `PENDING = 0`
  and its bound notification not active (the exit path's case without a pending exit: the work's
  `vcpu.check` and `finish`'s last `vcpu.check` both decide nothing): reads the state, binding, `PENDING`,
  bound-notification and its `TAIL_STATE` words only.
* **The report's frame** `RepFr` (P1's `vcpu.report.xfV` invariant: `BlkOK`, the thread still `RUNNING_VM`,
  the writes so far `RepW` words) with **`repFr_steps`** (`RepSteps` for the looked-up buffer, the VCPU's
  `PENDING` a word of P1's `U`) and **`repFr_fin`** (the final `set_thread_state TS_RUNNING` is guarded at every
  `RepFr` state: the SC word and `REFILL_MAX` are read where the entry state had them, `scA t` not being a
  `RepW` word). These are `vcpu.report.guardP`'s `Rs` and `hfin`.

No named premises.
-/
import Fl4Proofs.P2.AccessLvmExit
import Fl4Proofs.P2.FootTimerSetR
import Fl4Proofs.P2.FootTimerFireW
import Fl4Proofs.P1.VcpuCheckInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (ScAcc rhA tmA RdHead NodeSt)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
variable {T Cs Ω : Set U64}
variable {A : Type} (ar : machine.Arch A)

/-- **`schedule` at a resume state on a guarded store** (module docstring). -/
theorem sched.schedule.guard_resumeP (hA : P0.ArchTotal ar) (X : S) (a : A) {zc : Nat}
    (hcC : L.cpu X ∈ Cs) (hN : NodePlaced st T X (L.cpu X)) (hTp : TcbPlaced T)
    (homega : ∀ b ∈ Ω, OutsideObjs st T Cs X b) (hct : L.curW X ∈ T)
    (hsame : L.mem X (scA (L.curW X)) = L.cscW X) (hc : SCq st X Ω (L.cscW X) zc)
    (hmx : L.rmax X (L.cscW X) ≠ 0#u64)
    (hNd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt X (L.cpu X) o) ∧ W (L.nodeAt X (L.cpu X) o))
    (hSc : ScAcc R W (L.cscW X) zc) (hsc : R (scA (L.curW X)))
    (hdt : R (core.num.U64.wrapping_add (L.ksb X) layout.ks.DOMAIN_TIME))
    (hrs : L.mem X (rhA (L := L) X) ≠ 0#u64 → ∃ zr, L.mem X (rhA (L := L) X) ∈ T ∧
      R (scA (L.mem X (rhA (L := L) X))) ∧
      SCq st X Ω (L.mem X (scA (L.mem X (rhA (L := L) X)))) zr ∧
      L.rmax X (L.mem X (scA (L.mem X (rhA (L := L) X)))) ≠ 0#u64 ∧
      (∀ b, InSC (L.mem X (scA (L.mem X (rhA (L := L) X)))) zr b → Aligned b → R b) ∧
      (L.mem X (scA (L.mem X (rhA (L := L) X))) ≠ L.cscW X →
        ∀ b, InSC (L.mem X (scA (L.mem X (rhA (L := L) X)))) zr b → Outside b (L.cscW X) zc) ∧
      (L.mem X (scA (L.mem X (rhA (L := L) X))) = L.cscW X → zr = zc))
    (htd : L.mem X (tmA (L := L) X) ≠ 0#u64 → L.mem X (tmA (L := L) X) ∈ T ∧
      R (core.num.U64.wrapping_add (L.mem X (tmA (L := L) X)) 3528#u64))
    (hT : L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN) = 0#u64 ∨
      L.mem X (L.nodeAt X (L.cpu X) layout.node.CUR_TIME) <
        L.mem X (tdA (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))))
    (h2 : L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD) ≠ 0#u64 →
      R (scA (L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD))) ∧
      RdHead (L := L) R X (L.mem X (scA (L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD)))))
    (hRel : L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD) = 0#u64 ∨
      ¬ ((L.refill X (L.mem X (scA (L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD))))
          (L.rhead X (L.mem X (scA (L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD)))))).time ≤
        L.curTime X))
    (ha : L.actionW X = sched.ACTION_RESUME_CURRENT) :
    sched.schedule gS ar X a = sched.schedule st ar X a := by
  have hres := resume_hsw_hfr (gS := gS) ar hA X a hcC hN hTp homega hct hsame hc hmx hNd hSc hsc hdt hrs htd
  exact sched.schedule.guard_nodue ar X a hNd (fun hne => (htd hne).2) hT h2 hRel ha hres.1 hres.2

end

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]

/-- **`vcpu.check` of a `RUNNING_VM` thread with nothing to report** (module docstring). -/
theorem vcpu.check.guard_vmq {A : Type} (ar : machine.Arch A) (s : S) (a : A) (t v n : U64)
    (hst : R (stA t)) (hvw : R (core.num.U64.wrapping_add t 3664#u64))
    (hbn : R (core.num.U64.wrapping_add t 3368#u64)) (hp : R (core.num.U64.wrapping_add v vcpu.PENDING))
    (hn : n ≠ 0#u64 → R (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE))
    (eb : vcpu.bound st s t = ok v) (hv0 : v ≠ 0#u64) (ep : vcpu.get st s v vcpu.PENDING = ok 0#u64)
    (en : obj.Tcb.bound_ntfn st t s = ok n)
    (hq : n ≠ 0#u64 → ∀ x, obj.Ntfn.state st n s = ok x → x ≠ obj.NTFN_ACTIVE) :
    vcpu.check gS ar s a t = vcpu.check st ar s a t := by
  have hb : (v != 0#u64) = true := bne_iff_ne.mpr hv0
  unfold vcpu.check
  rw [PathObl.obj.Tcb.state.guard _ s hst]
  refine PathObl.bind_guard_congr rfl fun i _ => ?_
  refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
  rw [vcpu.bound.guardT s t hvw, eb]
  simp only [bind_ok]
  rw [if_pos hb, if_pos hb, vcpu.get.guard s v _ hp, ep]
  simp only [bind_ok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [PathObl.obj.Tcb.bound_ntfn.guard _ s hbn, en]
  simp only [bind_ok]
  by_cases h0 : n = 0#u64
  · subst h0; simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hv0]
  · have hb2 : (n != 0#u64) = true := bne_iff_ne.mpr h0
    rw [if_pos hb2, if_pos hb2, PathObl.obj.Ntfn.state.guard n s (hn h0)]
    refine PathObl.bind_guard_congr rfl fun x hx => ?_
    rw [if_neg (hq h0 x hx), if_neg (hq h0 x hx), if_neg hv0, if_neg hv0]

end

/-! ## The report's frame -/

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac U : Set U64} {H : Heap} {Z : U64 → Nat}

/-- **The report's frame** from the entry state `s0` (P1's `vcpu.report.xfV` invariant). -/
def RepFr (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (Ac : Set U64) (t : U64) (U : Set U64) (s0 s1 : S) : Prop :=
  BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1 ∧ L.mem s1 (stA t) = sched.TS_RUNNING_VM ∧ WritesIn st s0 s1 (RepW t U)

/-- **`RepSteps` for the frame** (the looked-up buffer `b`, `BufOK`; the VCPU's `PENDING` a word of `U`). -/
theorem repFr_steps {s0 : S} {t b : U64} (ht : t ∈ T) (hU : ∀ x ∈ U, UsrW st T Cs H Sg Scs Z s0 x)
    (hb : BufOK U b) :
    RepSteps st t (· = b) (RepFr st T Cs Ω H Sg Rp Scs Nt Z Ac t U s0)
      (fun v => core.num.U64.wrapping_add v vcpu.PENDING ∈ U) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro s1 b' i v rfl ⟨h1, st1, w1⟩ hi
    have hT : TcbPlaced T := h1.1.choose_spec.choose_spec.tcbs
    exact WP.spec_mono (msg.set_mr.xw s1 (hT t ht) hb (fun x hx => (hU x hx).ksb w1.1) (by omega)) fun r w =>
      xw_step h1 st1 w1 (fun x hx => (hU x hx).ksb w1.1) w ht
  · rintro s1 r v ⟨h1, st1, w1⟩ hr
    have hT : TcbPlaced T := h1.1.choose_spec.choose_spec.tcbs
    have hr' : r.val < 384 := by
      rcases hr with rfl | rfl | rfl <;>
        simp [layout.reg.MSG_INFO, layout.reg.BADGE, layout.reg.FAULT_IP, layout.reg.RSI, layout.reg.RDI]
    refine WP.spec_mono (obj.Tcb.set_reg.wrS s1 t r v (hT t ht) hr') fun s2 hs2 => ?_
    obtain ⟨K, hK, e⟩ := hs2
    subst e
    exact xw_step h1 st1 w1 (fun x hx => (hU x hx).ksb w1.1) ((writesIn_wr (field_aligned (hT t ht) (by omega)
      (by omega))).mono fun x e => Or.inl ⟨K, by omega, by omega, by omega, e⟩) ht
  · rintro s1 v ⟨h1, st1, w1⟩ hv
    have hv' : core.num.U64.wrapping_add v vcpu.PENDING ∈ U := hv
    unfold vcpu.set
    simp only [lift, bind_ok]
    refine WP.spec_mono (LawfulStore.write_spec s1 _ 0#u64) fun s2 e => ?_
    subst e
    exact xw_step h1 st1 w1 (fun x hx => (hU x hx).ksb w1.1)
      ((writesIn_wr (hU _ hv').out.1).mono fun x e => Or.inr (by rw [e]; exact hv')) ht

/-- `scA t` is no `RepW` word of `t` (it is at offset 3464, above the registers), given it is not in `U`. -/
theorem scA_not_repW {t : U64} (ht : TcbAddr t) (hsU : scA t ∉ U) : ¬ RepW t U (scA t) := by
  rintro (⟨K, h1, h2, -, e⟩ | hu)
  · exact tcb_word_ne ht ht (K1 := 3464#u64) (K2 := K) (by simp) (by omega) (fun _ => by simp; omega) e
  · exact hsU hu

variable {R W : U64 → Prop} {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]

/-- **The report's last step is guarded at every frame state** (module docstring). -/
theorem repFr_fin {s0 : S} {t : U64} (ht : TcbAddr t) (hsU : scA t ∉ U) (hn : NodeSt (L := L) R W s0)
    (hw : W (stA t)) (h1 : R (stA t)) (h2 : R (scA t)) (h3 : R (maxA (L.mem s0 (scA t)))) (h4 : R (inqA t)) :
    ∀ s1, RepFr st T Cs Ω H Sg Rp Scs Nt Z Ac t U s0 s1 →
      sched.set_thread_state gS s1 t sched.TS_RUNNING = sched.set_thread_state st s1 t sched.TS_RUNNING := by
  rintro s1 ⟨-, -, w⟩
  have aS : Aligned (stA t) := by rw [stA_eq]; exact field_aligned ht (by simp) (by simp)
  have aC : Aligned (scA t) := field_aligned ht (by simp) (by simp)
  have nSC : stA t ≠ scA t := by
    rw [stA_eq]; exact tcb_word_ne ht ht (by simp) (by simp) (fun _ => by simp)
  refine PathObl.sched.set_thread_state.guard s1 t _ (NodeSt.of_wi hn w) hw h1 h2 ?_ h4
  rw [mem_wr_ne' aS aC nSC, w.2.2 _ aC (scA_not_repW ht hsU)]
  exact h3

end

end Fl4Proofs.P2
