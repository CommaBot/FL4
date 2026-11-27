/-
# P2 (line lvm, gen 10): **`local_vm_timer_irq`'s waking fire case**

p2lf's waking fire chain split over its prefix as gen 9 split the non-waking one (`FootTimerFireAw/Rs/Tk/Sx/Sy`):
`fire_wk_aw_core` (no `current_ok`; the tail also gets `WkV`: the words outside the objects and `Ω` but the due
notification's and the endpoints' queue words kept from the entry to the post-`awaken` state, and a `WAITING` due
notification not left `ACTIVE`), `aw_resume_core` / `aw_tail_sw_core` / `fire_tail_wk2_core` (`hy0` for `eok`; the
final `vcpu::check` of the entry's current thread, when it runs a VM and is current again after `schedule` — it
stays, or the switch re-queued it and chose it again — asked as `VcG`, at a state agreeing with the post-`awaken`
state on every `VFar` word and on the thread's words but its queue links). The woken thread and the old ready
head do not run a VM (`RUNNING`; `top_ok`), so their final checks are `guard_nvm`'s as before; the preempted VM
thread is re-queued by `schedSw`'s `enqueue` (`RUNNING_VM` is runnable), which `schedSw_guard` already covers.

Here:

* **`vtimer_accG_fwk`**: an accepted VM-timer run in the waking fire case is the same run on any `GRd` / `GWr`
  store answering what `fire_tail_wk2_core` asks plus the VM head's words. `VcG` is discharged as
  `vcpu.check.guard_vmq`: the bound VCPU word and bound-notification word of the thread are kept; `PENDING` is kept
  to the post-`awaken` state (in `Ω`: `AwFacts`' `Ω ∖ Sg` frame with `pSg`; outside `Ω`: `WkV` with `pQ`) and
  beyond (`VFar`); the bound notification `n` is not `ACTIVE` at the end: `n = N` (the due one) only when `N` is
  `WAITING` (an idle `N` bound to a thread running a VM wakes nobody), and then `WkV`'s state half; `n ≠ N`: its
  state word is no `Ω` word and no queue word of `N` or of an endpoint (P1's `EpsWit`), so `WkV` keeps it.
* `slot_rdV`, `pending_not_q` (`PENDING` is in no region, `N`'s words are `.ntfn`, an endpoint's `.obj`);
  **`vtimer_acc_fwk_own`** / **`vtimer_move_fwk`**: `acc` / `move` under `ownV` (typed regions: `rpV`,
  `wpermV_of_own'`; kernel-global words in no VCPU; `*_nondec`, `stepOK_state` / `_height` / `_deadline` with `hM`);
* **`vtimer_localPathF`**: `vtimer_localPathW` with `hF` / `hFm` discharged — `local_vm_timer_irq` is an
  `E2E.LocalPath` under `ownV` with the whole fire case proved.

Named premises of `vtimer_localPathF` (beside `vtimer_localPathW`'s: [P] `hp`, [W] `hz`, [P] `hm`, [W] `hro`, [J]
`hK`, [J] `hU`, [J] `hEU`, [P] `hlk`, `hNt`, [J] `hM` — discharged at the family level as `IrqEntK.mem`, and
`VtmEnt`'s fields): [J] `hOL` (`ObjLay`), [P] `hPL` (`PlanLk`), [J] `hUB` (`UserOK` + IPC-buffer lookups, as
`irq_localPathP3`'s), [J] `hSL` (`SlotLayV`), [J] `hpSg` (`PENDING ∉ Sg`; `usrW_vcpu`'s `UsrW.sg` at `Sg = H.frame`).
-/
import Fl4Proofs.P2.AccessLvmTf
import Fl4Proofs.P2.FootTimerIrqLPP3
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.Serial (Owner)
open Fl4Proofs.P2.OwnMapV (KLayoutV ownV InVcpu RegionOKV UserOKV rpermV_of_own wpermV_of_own'
  stepOKV_of_stepOK)

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 32000000 in
/-- **An accepted VM-timer run in the waking fire case, on the guarded store** (module docstring). -/
theorem vtimer_accG_fwk {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
    (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {irq n v : U64} {p : localtimer.TimerIrqPlan}
    {Lk : U64 → Prop} {U : Set U64}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hNt : ∀ q ∈ Nt, H q = some .ntfn)
    (gRd : IrqOk st s → (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64 →
      TmHere st s (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) →
      ∀ w, Aligned w → FireRd st T Z s w → R w)
    (gWr : IrqOk st s → (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64 →
      TmHere st s (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) →
      ∀ w, Aligned w → FireWr st T Z s w → w ≠ stA (L.curW s) → W w)
    (hIq : ∀ i, interrupt.state_off irq = ok i → R (core.num.U64.wrapping_add (L.ksb s) i))
    (hD1 : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hD2 : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME))
    (gfire : ∀ (s1 : S), L.ksb s1 = L.ksb s → L.cpu s1 = L.cpu s →
      (∀ b, Aligned b → b ≠ ctA (L := L) s → b ≠ cnA (L := L) s → L.mem s1 b = L.mem s b) → ∀ now : U64,
      localtimer.fire_ok gS s1 (L.cpu s) (L.curW s) p now = localtimer.fire_ok st s1 (L.cpu s) (L.curW s) p now)
    (hwH : ∀ X y v, y ∈ T → FootLtArmed st s (L.cpu s) y →
      (L.mem X (tdA y) ≠ 0#u64 → (L.mem X (thA y)).val >>> 8 = (L.cpu s).val ∧ v.val >>> 8 = (L.cpu s).val) →
      gS.write X (thA y) v = st.write X (thA y) v)
    (hwD : ∀ X y v, y ∈ T → FootLtArmed st s (L.cpu s) y → L.mem X (affA y) = L.cpu s →
      L.mem s (affA y) = L.cpu s →
      (L.mem X (tdA y) ≠ 0#u64 ∨ v ≠ 0#u64 → (L.mem X (thA y)).val >>> 8 = (L.cpu s).val) →
      gS.write X (tdA y) v = st.write X (tdA y) v)
    (hvb : vcpu.bound st s (L.curW s) = ok v)
    (hRp : R (core.num.U64.wrapping_add v vcpu.PENDING))
    (hRn : n ≠ 0#u64 → R (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE))
    (fP : VFar st T Cs Scs Z s (core.num.U64.wrapping_add v vcpu.PENDING))
    (fN : n ≠ 0#u64 → VFar st T Cs Scs Z s (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE))
    (pSg : core.num.U64.wrapping_add v vcpu.PENDING ∉ Sg)
    (pQ : ∀ e, (e = L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) ∧ e ≠ 0#u64 ∧
        L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64) ∨
      H e = some .ep → core.num.U64.wrapping_add v vcpu.PENDING ≠ epHeadA e ∧
        core.num.U64.wrapping_add v vcpu.PENDING ≠ epTSA e)
    (hAff : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t))
    (rL : ∀ y, LocT st T s y → ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ TimerField K.val →
      ¬ GField K.val → R (core.num.U64.wrapping_add y K))
    (wL : ∀ y, LocT st T s y → ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ GateField K.val →
      ¬ TimerField K.val → ¬ GField K.val → K.val ≠ 3328 → K.val ≠ 3336 →
      W (core.num.U64.wrapping_add y K))
    (rS : ∀ p ∈ Scs, L.mem s (scCoreA p) = L.cpu s → ∀ b, Aligned b → InSC p (Z p) b → R b)
    (wS : ∀ p ∈ Scs, L.mem s (scCoreA p) = L.cpu s → ∀ b, Aligned b → InSC p (Z p) b → b.val ≠ p.val + 16 → W b)
    (lkL : ∀ y ∈ T, QueuedState (L.mem s (stA y)) → Lk (L.mem s (blockA y)) → ∀ k : U64,
      (k.val = 3496 ∨ k.val = 3504) → R (core.num.U64.wrapping_add y k) ∧ W (core.num.U64.wrapping_add y k))
    (hSW : StW st gS T Lk s)
    (hLkN : p.ntfn ≠ 0#u64 → Lk p.ntfn) (hLkE : p.ep ≠ 0#u64 → Lk p.ep)
    (wNt : IrqOk st s → (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64 →
      TmHere st s (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) →
      L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64 →
      L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) ≠ 0#u64 →
      ∀ k : U64, k.val < 64 → k.val % 8 = 0 → k.val ≠ 24 →
        W (core.num.U64.wrapping_add (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))) k))
    (rwE : p.ep ≠ 0#u64 → ∀ k : U64, k.val < 16 → k.val % 8 = 0 →
      R (core.num.U64.wrapping_add p.ep k) ∧ W (core.num.U64.wrapping_add p.ep k))
    (wRt : p.reply ≠ 0#u64 → W (rTcbA p.reply))
    (hU : UserOK st T Cs Ω H U s) (hbU : ∀ y ∈ T, msg.lookup_ipc_buffer st s true y ⦃ b => BufOK U b ⦄)
    (hAs : AsidOff (L := L) Ω Sg s)
    (hSlot : ∀ y, LocT st T s y → R (vtA y) ∧ R (core.num.U64.wrapping_add (vtA y) 8#u64))
    (hKr : R (krA (L := L) s)) (hTab : PathObl.RdTab (L := L) R s)
    (hq : IrqFire st ar s a) (hWk : ¬ NoWake st s)
    (h : localvm.handle_vm_timer_irq_local st ar s a irq p n = ok (true, s', a')) :
    localvm.handle_vm_timer_irq_local gS ar s a irq p n = ok (true, s', a') := by
  obtain ⟨mx, tip, emx, hle, ei1, etip, eb, hstv, en, enq, evr, eok, eq, et⟩ := vtimer_split ar h
  obtain ⟨s1, a1, now, i2, b4, due, s2, a2, x, s3, a3, s4, a4, eu, enow, erel, ei2, eb4, edue, hc, evc1, ecb,
    ehi, efin⟩ := vtimerTail_split ar et
  obtain ⟨s5, a5, s6, a6, t, esc, eac, ett, evc5⟩ := vfinish_split ar efin
  obtain ⟨v', ev', hv0, hp0⟩ := vm_running_true evr
  rw [hvb] at ev'
  obtain rfl := ok_inj_ff ev'
  have hnq := nq_true enq
  obtain ⟨haff, hy0, hsct, hcore⟩ := current_vm_ok_true eok
  obtain ⟨rfl, rfl⟩ := hq s1 a1 now i2 b4 due eu enow ei2 eb4 edue
  have efo : localtimer.fire_ok st s1 (L.cpu s) (L.curW s) p now = ok true := by
    cases hc with
    | quiet _ hd => exact absurd hd (by decide)
    | fire _ _ hf => exact hf
    | rr h4 _ _ => exact absurd h4 (by decide)
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  have hcC : L.cpu s ∈ Cs := h0.cur
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ hcC
  have hcT : L.curW s ∈ T := h0.curT
  have ht' := hT _ hcT
  have hX := hI.2.2.1
  have hS := hI.2.2.2.2
  have hO := hX.1
  have hcs : L.cscW s ∈ Scs := hX.2.2.cur
  have hcq : SCq st s Ω (L.cscW s) (Z (L.cscW s)) := scq_of hO hS hcs
  -- `s → s1`: the timestamp update
  obtain ⟨n1, -, er⟩ := ut_now ar hA hN eu
  simp only at er
  have k1 : L.ksb s1 = L.ksb s := by rw [er, utW_ksb]
  have c1 : L.cpu s1 = L.cpu s := by rw [er, utW_cpu]
  have m1 : ∀ b, Aligned b → b ≠ ctA (L := L) s → b ≠ cnA (L := L) s → L.mem s1 b = L.mem s b :=
    fun b hb h1 h2 => by rw [er]; exact utW_mem hN n1 hb h1 h2
  have htcb1 : ∀ {y K : U64}, y ∈ T → K.val < 4096 → K.val % 8 = 0 →
      L.mem s1 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
    intro y K hy hK h8
    exact m1 _ (field_aligned (hT y hy) hK h8) (tcb_node_ne hN hy (hT y hy) hK (by simp [layout.node.CUR_TIME]))
      (tcb_node_ne hN hy (hT y hy) hK (by simp [layout.node.CONSUMED]))
  have hout1 : ∀ b, OutsideObjs st T Cs s b → L.mem s1 b = L.mem s b := fun b hb =>
    m1 b hb.1 (fun e => out_ne_node hb hcC hN (by simp [layout.node.CUR_TIME]) (congrArg UScalar.val e).symm)
      (fun e => out_ne_node hb hcC hN (by simp [layout.node.CONSUMED]) (congrArg UScalar.val e).symm)
  -- `vcpu.check` at `s1` reports nothing
  have eb1 : vcpu.bound st s1 (L.curW s) = ok v := by
    rw [vcpu_bound_congr (htcb1 hcT (by simp) (by simp))]; exact hvb
  have en1 : obj.Tcb.bound_ntfn st (L.curW s) s1 = ok n := by
    rw [bound_ntfn_congr (by unfold boundA; exact htcb1 hcT (by simp) (by simp))]; exact en
  have ep1 : vcpu.get st s1 v vcpu.PENDING = ok 0#u64 := by
    rw [vcpu_get_congr (hout1 _ fP.1)]; exact hp0
  have hq1 : n ≠ 0#u64 → ∀ x, obj.Ntfn.state st n s1 = ok x → x ≠ obj.NTFN_ACTIVE := fun hn x ex =>
    hnq hn x (by rw [← ntfn_state_congr (hout1 _ (fN hn).1)]; exact ex)
  have evc1' := vcpu.check_np ar s1 a1 (L.curW s) v n eb1 hv0 ep1 en1 hq1
  rw [evc1'] at evc1
  obtain ⟨rfl, rfl⟩ : s1 = s2 ∧ a1 = a2 := by
    have e := ok_inj_ff evc1
    simp only [Prod.mk.injEq] at e
    exact e
  -- the due thread and its notification
  have hok : IrqOk st s := ⟨haff, hsct, hcore⟩
  have hTm := fire_tmHere etip eb efo
  obtain ⟨hTM0, hpN⟩ := plan_ntfn etip eb efo
  have gRd' := gRd hok hTm
  have gWr' := gWr hok hTm
  -- the guarded store: what it admits
  have nR : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o) := fun o h1 h2 =>
    gRd' _ (nodeAt_aligned hN h1 h2) (Or.inl (Or.inl ⟨o, h1, h2, rfl⟩))
  have cR : ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → (K.val < 3528 ∨ 3576 ≤ K.val) →
      K.val ≠ 3496 → K.val ≠ 3504 → R (core.num.U64.wrapping_add (L.curW s) K) := fun K h1 h2 h3 h4 h5 h6 =>
    gRd' _ (field_aligned ht' h2 h3) (Or.inl (Or.inr (Or.inl ⟨K, h1, h2, h3, h4, h5, h6, rfl⟩)))
  have scR : ∀ b, InSC (L.cscW s) (Z (L.cscW s)) b → Aligned b → R b := fun b hb ha =>
    gRd' _ ha (Or.inl (Or.inr (Or.inr (Or.inl hb))))
  have rSt : R (stA (L.curW s)) := by rw [stA_eq]; exact cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rVc : R (core.num.U64.wrapping_add (L.curW s) 3664#u64) :=
    cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rBn : R (core.num.U64.wrapping_add (L.curW s) 3368#u64) :=
    cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rMx : R (maxA (L.cscW s)) := scR _ hcq.2.2.2.1 hcq.2.2.2.2
  have rCore : R (scCoreA (L.cscW s)) := by
    obtain ⟨hP, hz⟩ := hO.sc _ hcs
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hv := sc_word_val hP hz (o := layout.sc.CORE) (by simp [layout.sc.CORE])
    have hcv : layout.sc.CORE.val = 16 := by simp [layout.sc.CORE]
    exact scR _ ⟨by unfold scCoreA; rw [hv]; omega, by unfold scCoreA; rw [hv, hcv]; omega⟩
      (by unfold Aligned scCoreA; rw [hv, hcv]; omega)
  have gvc1 : vcpu.check gS ar s1 a1 (L.curW s) = vcpu.check st ar s1 a1 (L.curW s) :=
    vcpu.check.guard_vmq ar s1 a1 (L.curW s) v n rSt rVc rBn hRp hRn eb1 hv0 ep1 en1 hq1
  have hR : LvmRd st R s (L.curW s) (L.cscW s) :=
    { cur := nR _ (by rw [curth_val]; omega) (by rw [curth_val])
      curSc := nR _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      vcpu := rVc
      bntfn := rBn
      aff := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      yld := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      sc := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      scCore := rCore
      idle := nR _ (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD])
      dom := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      curDom := hD1
      state := rSt
      maxA := by rw [hsct]; exact rMx
      inq := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      act := nR _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
      domTime := hD2
      ipi := nR _ (by simp [layout.node.IPI_PENDING]) (by simp [layout.node.IPI_PENDING]) }
  have ebv : L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64) = v := by
    rw [eq_of_spec_fd (vcpu.bound.spec (L := L) s _)] at hvb; exact ok_inj_ff hvb
  have hbn : L.mem s (boundA (L.curW s)) = n := by
    rw [eq_of_spec_fd (obj.Tcb.bound_ntfn.val (L := L) s _)] at en; exact ok_inj_ff en
  have ecpu : st.cur_cpu s = ok (L.cpu s) := by rw [L.cur_cpu_eq]
  have ecsc : sched.cur_sc st s = ok (L.cscW s) := eq_of_spec_fd (sched.cur_sc.spec (L := L) s)
  -- the due notification `N`
  obtain ⟨N, eN⟩ : ∃ x, L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) = x :=
    ⟨_, rfl⟩
  have hWk' := hWk
  unfold NoWake at hWk'
  rw [eN] at hWk'
  have hN0 : N ≠ 0#u64 := fun e => hWk' (Or.inl e)
  have q1 := (tmin_facts (BXI.blk hI) hcC hTM0).1
  have hNNt : N ∈ Nt := by rw [← eN]; exact hX.2.2.bnd _ q1 (by rw [eN]; exact hN0)
  obtain ⟨Q0, R0, hq0⟩ := hI.1
  obtain ⟨E, EQ, hEW⟩ := hq0.eps
  have eTS : core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE = epTSA n := by
    apply UScalar.eq_of_val_eq
    unfold epTSA
    simp [core.num.U64.wrapping_add_val_eq, layout.ntfn.TAIL_STATE, layout.ep.TAIL_STATE]
  -- `VcG`: the final `vcpu::check` of the thread running a VM
  have hVc : ∀ Y now' w, AwFacts st T Cs Ω H Sg Rp Scs Nt Z Ac R s Y now' w →
      WkV st T Cs Ω H s Y (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))) →
      VcG st gS ar T Cs Scs Z s Y := by
    intro Y now' w hF hV _ X a'' hcX hfr htk
    rw [eN] at hV
    obtain ⟨-, -, -, -, tY, -, -, -, -, -, -, -, wcur, -, -, -, -, hout⟩ := hF
    have tYc : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (K.val < 3528 ∨ 3576 ≤ K.val) → K.val ≠ 3496 →
        K.val ≠ 3504 → L.mem Y (core.num.U64.wrapping_add (L.curW s) K) =
          L.mem s (core.num.U64.wrapping_add (L.curW s) K) :=
      fun K h1 h2 h3 h4 h5 => tY _ hcT K h1 h2 h3 h4 h5 (fun e => absurd e.symm wcur)
    have eb5 : vcpu.bound st X (L.curW s) = ok v := by
      rw [vcpu_bound_congr ((htk 3664#u64 (by simp) (by simp) (by simp) (by simp) (by simp)).trans
        (tYc _ (by simp) (by simp) (Or.inr (by simp)) (by simp) (by simp)))]
      exact hvb
    have en5 : obj.Tcb.bound_ntfn st (L.curW s) X = ok n := by
      rw [bound_ntfn_congr (by
        unfold boundA
        exact (htk 3368#u64 (by simp) (by simp) (by simp) (by simp) (by simp)).trans
          (tYc _ (by simp) (by simp) (Or.inl (by simp)) (by simp) (by simp)))]
      exact en
    have hPY : L.mem Y (core.num.U64.wrapping_add v vcpu.PENDING) =
        L.mem s (core.num.U64.wrapping_add v vcpu.PENDING) := by
      by_cases hΩ : core.num.U64.wrapping_add v vcpu.PENDING ∈ Ω
      · exact hout _ fP.1.1 hΩ pSg
      · have e1 := pQ N (Or.inl ⟨eN.symm, hN0, hTM0⟩)
        exact hV.1 _ fP.1.1 fP.1 hΩ e1.1 e1.2 (fun e he => pQ e (Or.inr he))
    have ep5 : vcpu.get st X v vcpu.PENDING = ok 0#u64 := by
      rw [vcpu_get_congr ((hfr _ fP).trans hPY)]; exact hp0
    have hq5 : n ≠ 0#u64 → ∀ x, obj.Ntfn.state st n X = ok x → x ≠ obj.NTFN_ACTIVE := by
      intro hn x ex
      rw [eq_of_spec_fd (obj.Ntfn.state.spec (L := L) X n)] at ex
      obtain rfl := ok_inj_ff ex
      have eXY : L.epState X n = L.epState Y n := by
        unfold LawfulStore.epState; rw [← eTS, hfr _ (fN hn)]
      rw [eXY]
      have hnNt : n ∈ Nt := by rw [← hbn]; exact hX.2.2.bnd _ hcT (by rw [hbn]; exact hn)
      by_cases hnN : n = N
      · subst hnN
        refine hV.2 ?_
        by_contra hw
        by_cases hid : L.epState s n = obj.NTFN_IDLE
        · have hbt : L.mem s (ntfnBtA n) = L.curW s := by
            rw [← hbn]; exact hX.2.2.bs.tb _ hcT (by rw [hbn]; exact hn)
          refine hWk' (Or.inr (Or.inr ⟨hid, Or.inr ?_⟩))
          rw [hbt, hstv]; unfold sched.TS_RUNNING_VM sched.TS_BLOCKED_ON_RECV; decide
        · exact hWk' (Or.inr (Or.inl ⟨hid, hw⟩))
      · have he : n ∈ E := (hEW.2.2.2.2.2.2.2.1 n).2 (Or.inr (hNt n hnNt))
        obtain ⟨pn1, pn2⟩ := hO.ntP _ hnNt
        obtain ⟨pN1, pN2⟩ := hO.ntP _ hNNt
        have vT : (epTSA n).val = n.val + 8 := epTSA_val' (by omega)
        have hΩ : epTSA n ∉ Ω := fun hΩ => by
          have := hEW.2.2.1 n he _ hΩ
          omega
        have nv : n.val ≠ N.val := fun e => hnN (UScalar.eq_of_val_eq e)
        have eYs : L.mem Y (epTSA n) = L.mem s (epTSA n) := by
          refine hV.1 _ (by rw [← eTS]; exact (fN hn).1.1) (by rw [← eTS]; exact (fN hn).1) hΩ ?_ ?_ ?_
          · intro e; have := congrArg UScalar.val e; rw [vT, epHeadA_val] at this; omega
          · intro e; have := congrArg UScalar.val e; rw [vT, epTSA_val' (by omega)] at this; omega
          · intro e hHe
            have he' : e ∈ E := (hEW.2.2.2.2.2.2.2.1 e).2 (Or.inl hHe)
            have hen : e ≠ n := fun x => by rw [x, hNt n hnNt] at hHe; cases hHe
            have dj := hEW.2.1 e he' n he hen
            refine ⟨fun x => ?_, fun x => ?_⟩
            · have := congrArg UScalar.val x; rw [vT, epHeadA_val] at this; omega
            · have := congrArg UScalar.val x
              rw [vT, epTSA_val (hEW.1 e he').1] at this; omega
        have eS : L.epState Y n = L.epState s n := by unfold LawfulStore.epState; rw [eYs]
        rw [eS]
        exact hnq hn _ (eq_of_spec_fd (obj.Ntfn.state.spec (L := L) s n))
    exact vcpu.check.guard_vmq (gS := gS) ar X a'' (L.curW s) v n rSt rVc rBn hRp hRn eb5 hv0 ep5 en5 hq5
  -- the prefix and the waking fire tail, by the timer interrupt's cores
  have G := irq_accG_fire_core (gS := gS) ar hA hI (fun _ w ha hw => gRd' w ha (Or.inl hw))
    (fun _ w ha hw hn => gWr' w ha (Or.inl hw) hn) (fun _ => hIq) (fun _ => hD1) (fun _ => hD2) ecpu emx hle ei1
    etip eb (cur_thread_ok s) ecsc haff hsct hcore eq eu enow erel ei2 eb4 edue efo ecb ehi
  obtain ⟨gsc, post⟩ := fire_tail_wk2_core (gS := gS) (Lk := Lk) (U := U) ar hA hI hNt hok gRd' gWr' hD2
    (fun hr => absurd (hstv.symm.trans hr) (by simp [sched.TS_RUNNING_VM, sched.TS_RESTART])) hwH hwD hWk hAff
    rL wL rS wS lkL hD1 hSW (hLkN (by rw [hpN, eN]; exact hN0)) hLkE
    (fun k h1 h2 h3 => by rw [hpN]; exact wNt hok hTm hTM0 (by rw [eN]; exact hN0) k h1 h2 h3) rwE wRt etip eb eq hy0 eu enow erel ei2 eb4 edue efo ecb emx hle ei1 ehi
    (fire_bufAt3 ar hA hI hU hbU eu ei2 eb4 ecb emx hle ei1 ehi) hAs hSlot hKr hTab hVc
  obtain ⟨gac, post5⟩ := post s5 a5 esc
  obtain ⟨gt, gvc⟩ := post5 s6 a6 eac
  have gfin : localvm.finish gS ar s4 a4 = ok (s', a') := by
    unfold localvm.finish
    rw [gsc, esc]
    simp only [bind_ok, uncurry_apply_pair]
    rw [gac, eac]
    simp only [bind_ok, uncurry_apply_pair]
    rw [gt, ett]
    simp only [bind_ok]
    rw [gvc t ett]
    exact evc5
  have gfire1 := gfire s1 k1 c1 m1 now
  have hTl : vtimerTail gS ar s a irq p (L.curW s) (L.cscW s) (L.cpu s) =
      vtimerTail st ar s a irq p (L.curW s) (L.cscW s) (L.cpu s) := by
    rw [et]
    exact vtimerTail_replay ar eu G.gu enow G.gnow erel G.gb3 ei2 G.gi2 eb4 G.gb4 edue G.gdue hc
      (fun h => nomatch h) (fun _ => gfire1) evc1' gvc1 ecb G.gcb ehi G.ghi gfin
  rw [vtimer_eq, vtimerHead.guardE (gS := gS) s a irq p n (L.cscW s) G.gi1 G.gtip ecsc hR
    (fun _ => by rw [ebv]; exact hRp) hRn (T1 := vtimerTail gS ar s a irq p) (T2 := vtimerTail st ar s a irq p) hTl,
    ← vtimer_eq]
  exact h

end main

section own
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayoutV}
variable {A : Type} (ar : machine.Arch A) {lk : S → U64 → Prop}

/-- The two VSpace slot words of a local thread are readable under `ownV` (`slot_maxRV`; slot regions). -/
theorem slot_rdV (hK : RegionOKV K) {s : S} (hT : TcbPlaced T) (hSL : SlotLayV K.toKLayout st T s)
    (hu : ∀ b ∈ K.user, region K.toKLayout b = .none) {y : U64} (hy : LocT st T s y) :
    VexitRS K st lk s (vtA y) ∧ VexitRS K st lk s (core.num.U64.wrapping_add (vtA y) 8#u64) := by
  obtain ⟨m1, m2⟩ := slot_maxRV (lk := lk) hT hSL hu hy
  have hy' := hT y hy.1
  have e1 : vtA y = core.num.U64.wrapping_add y 32#u64 := by
    apply UScalar.eq_of_val_eq
    rw [vtA_val hy', tcb_wadd_val hy' (by simp)]; simp
  have e2 : core.num.U64.wrapping_add (vtA y) 8#u64 = core.num.U64.wrapping_add y 40#u64 := by
    apply UScalar.eq_of_val_eq
    have := hy'.fits
    rw [tcb_wadd_val hy' (by simp)]
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, vtA_val hy']
    omega
  obtain ⟨p1, r1, -⟩ := hSL y hy 32#u64 (Or.inl (by simp))
  obtain ⟨p2, r2, -⟩ := hSL y hy 40#u64 (Or.inr (by simp))
  exact ⟨⟨m1.2.1, Or.inr (rpV hK (by rw [e1, r1]; simp) m1.1)⟩, ⟨m2.2.1, Or.inr (rpV hK (by rw [e2, r2]; simp) m2.1)⟩⟩

/-- **`PENDING` is no queue word of the due notification or of an endpoint** (a VCPU word is in no region). -/
theorem pending_not_q (hK : RegionOKV K) {irq n : U64} {s : S} {Rp' : Set U64}
    (hE : VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s) (hOL : ObjLay K.toKLayout H Rp')
    (hv0 : vOf st s ≠ 0#u64) (e : U64)
    (he : (e = L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) ∧ e ≠ 0#u64 ∧
        L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64) ∨ H e = some .ep) :
    core.num.U64.wrapping_add (vOf st s) vcpu.PENDING ≠ epHeadA e ∧
      core.num.U64.wrapping_add (vOf st s) vcpu.PENDING ≠ epTSA e := by
  have E := hE.ent
  have hI := E.inv
  have hn := hK.none _ _ (E.vin hv0)
  have reg : ∀ k : U64, k.val < 16 → region K.toKLayout (core.num.U64.wrapping_add e k) ≠ .none := by
    intro k hk
    rcases he with ⟨rfl, h0, hne⟩ | hH
    · have h0' := hI.1.choose_spec.choose_spec
      obtain ⟨q1, -⟩ := tmin_facts (BXI.blk hI) h0'.cur hne
      have hNNt := hI.2.2.1.2.2.bnd _ q1 h0
      rw [E.ntw _ hNNt k (by omega)]; intro x; cases x
    · rw [hOL.1 _ hH k hk]; intro x; cases x
  refine ⟨fun x => ?_, fun x => ?_⟩
  · rw [x] at hn; unfold epHeadA at hn; exact reg _ (by simp [layout.ep.HEAD]) hn
  · rw [x] at hn; unfold epTSA at hn; exact reg _ (by simp [layout.ep.TAIL_STATE]) hn

set_option maxHeartbeats 16000000 in
/-- **`acc` of an accepted `local_vm_timer_irq` in the waking fire case**, under `ownV` (module docstring):
`vtimer_accG_fwk` on `guard st (VexitRS …) (VexitWS …)`, every word read or written in a typed region (`rpV`,
`wpermV_of_own'`) or, for the kernel-global words, in no VCPU (`VtmEnt`). Premises beyond `VtmEnt` / `hNt`: `hOL`,
`hPL`, `hUB`, `hSL`, `pSg` (module docstring of `vtimer_localPathF`). -/
theorem vtimer_acc_fwk_own (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hNt : ∀ q ∈ Nt, H q = some .ntfn)
    {s s' : S} {a a' : A} {irq n : U64} {p : localtimer.TimerIrqPlan} {U : Set U64}
    (hE : VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s) (hOL : ObjLay K.toKLayout H Rp) (hPL : PlanLk lk p)
    (hU : UserOK st T Cs Ω H U s) (hbU : ∀ y ∈ T, msg.lookup_ipc_buffer st s true y ⦃ b => BufOK U b ⦄)
    (hSL : SlotLayV K.toKLayout st T s) (pSg : core.num.U64.wrapping_add (vOf st s) vcpu.PENDING ∉ Sg)
    (hq : IrqFire st ar s a) (hWk : ¬ NoWake st s)
    (h : localvm.handle_vm_timer_irq_local st ar s a irq p n = ok (true, s', a')) :
    localvm.handle_vm_timer_irq_local (guard st (VexitRS K st lk s) (VexitWS K st lk s)) ar s a irq p n =
      ok (true, s', a') := by
  have hb := vtimer_irq_lt ar h
  obtain ⟨hvb, hv0, hbn⟩ := vtimer_bnd ar h
  obtain ⟨-, tip, -, -, -, etip, eb, -⟩ := vtimer_split ar h
  obtain ⟨hPE, hPR⟩ := plan_pe_pr hE.ent.inv etip eb
  have E := hE.ent
  have hI := E.inv
  have hL := E.lay
  have hT : TcbPlaced T := hI.1.choose_spec.choose_spec.tcbs
  have vRd : ∀ w, Aligned w → region K.toKLayout w ≠ .none → RPerm (own K.toKLayout) (L.cpu s) (lk s) (L.mem s) w →
      VexitRS K st lk s w := fun w ha hr hp => ⟨ha, Or.inr (rpV hK hr hp)⟩
  have vWr : ∀ w, Aligned w → WPerm (own K.toKLayout) (L.cpu s) (lk s) (L.mem s) w → VexitWS K st lk s w :=
    fun w ha hp => ⟨ha, Or.inr (wpermV_of_own' hK hp)⟩
  have treg : ∀ {y k : U64}, y ∈ T → 256 ≤ k.val → k.val < 4096 →
      region K.toKLayout (core.num.U64.wrapping_add y k) ≠ .none := fun hy h1 h2 => by
    have e := hL.tcb _ hy _ h1 h2
    unfold fld at e
    rw [e]; simp
  have rD : VexitRS K st lk s (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN) :=
    ⟨hL.domA, Or.inr (rpermV_of_own E.ksv.1 (rperm_none hL.dom _))⟩
  have wr : ∀ (X : S) (w v' : U64), VexitWS K st lk s w →
      (guard st (VexitRS K st lk s) (VexitWS K st lk s)).write X w v' = st.write X w v' :=
    fun X w v' hw => PathObl.GWr.write (g := guard st (VexitRS K st lk s) (VexitWS K st lk s)) hw X v'
  have g3328 : ¬ GateField (3328#u64 : U64).val := by unfold GateField; simp
  have t3328 : ¬ TimerField (3328#u64 : U64).val := by unfold TimerField; simp
  have f3328 : ¬ GField (3328#u64 : U64).val := by unfold GField; simp
  exact vtimer_accG_fwk (gS := guard st (VexitRS K st lk s) (VexitWS K st lk s)) (R := VexitRS K st lk s)
    (W := VexitWS K st lk s) (Lk := lk s) (U := U) ar hA hI hNt
    (fun hok hTm w ha hw => ⟨ha, Or.inr (fire_rdV hK hI hL E.ntw E.cs E.aff hok hTm hw)⟩)
    (fun hok hTm w ha hw _ => ⟨ha, Or.inr (fire_wrV hK hI hL E.ntw hok hTm hw)⟩)
    (fun i hi => ⟨(hE.iq hb i hi).1,
      Or.inr (rpermV_of_own (hE.iq hb i hi).2.2 (rperm_none (hE.iq hb i hi).2.1 _))⟩)
    rD ⟨hL.dtmA, Or.inr (rpermV_of_own E.ksv.2 (rperm_none hL.dtm _))⟩
    (fun s1 k1 c1 m1 now =>
      fire_rdG hK.base hI hL E.ntw (lk := lk s) (fun w hp ha hr => ⟨ha, Or.inr (rpV hK hr hp)⟩) rD hNt k1 c1
        m1 etip eb _ now)
    (fun X y v' hy ha _ => wr X _ v' ⟨field_aligned (hT y hy) (by simp) (by simp),
      Or.inr (wpermV_of_own' hK (held_core (ftree_own hL hT hy ha (k := 3568#u64) (by simp) (by simp) (by simp))))⟩)
    (fun X y v' hy ha _ _ _ => wr X _ v' ⟨field_aligned (hT y hy) (by simp) (by simp),
      Or.inr (wpermV_of_own' hK (held_core (ftree_own hL hT hy ha (k := 3528#u64) (by simp) (by simp) (by simp))))⟩)
    hvb ⟨(E.vfar hv0).1.1, Or.inr (pending_rd hK (E.vin hv0) (E.vlk hv0))⟩
    (fun hn => by
      rw [← hbn] at hn ⊢
      obtain ⟨q1, q2⟩ := ntfn_tail_rd (lk := lk s) hK hI hL E.ntw E.curAff hn
      exact ⟨q1, Or.inr q2⟩)
    (E.vfar hv0) (fun hn => E.nfar n hbn hn) pSg (pending_not_q hK hE hOL hv0) E.aff
    (fun y hy K h1 h2 h3 ht hg => vRd _ (field_aligned (hT y hy.1) h2 h3) (treg hy.1 h1 h2)
      (loc_rd_own hI hL (Or.inr (Or.inl ⟨y, hy, K, h1, h2, h3, ht, hg, rfl⟩))))
    (fun y hy K h1 h2 h3 hga ht hg _ _ => vWr _ (field_aligned (hT y hy.1) h2 h3)
      (loc_wr_own hI hL (Or.inr (Or.inl ⟨y, hy, K, h1, h2, h3, hga, ht, hg, rfl⟩))))
    (fun q hq hc b ha hb => vRd _ ha (by rw [hL.sc _ hq _ hb]; simp)
      (loc_rd_own hI hL (Or.inr (Or.inr ⟨q, hq, hc, hb⟩))))
    (fun q hq hc b ha hb h16 => vWr _ ha (loc_wr_own hI hL (Or.inr (Or.inr ⟨q, hq, hc, hb, h16⟩))))
    (fun y hy hqs hlk k hk => by
      have o := lkw_own hI hL (Lk := lk s) (fun _ h => h) (Or.inl ⟨y, hy, hqs, hlk, k, hk, rfl⟩)
      have ha := field_aligned (hT y hy) (K := k) (by omega) (by omega)
      exact ⟨vRd _ ha (treg hy (by omega) (by omega)) o.2, vWr _ ha o.1⟩)
    (fun X y v' hy _ _ _ => wr X _ v' (vWr _ (by rw [stA_eq]; exact field_aligned (hT y hy.1) (by simp) (by simp))
      (loc_wr_own hI hL (Or.inr (Or.inl ⟨y, hy, 3328#u64, by simp, by simp, by simp, g3328, t3328, f3328,
        stA_eq _⟩)))))
    (fun hn => (hPL s).1 hn) (fun hep => (hPL s).2.1 hep)
    (fun hok hTm h1 h2 k hk h8 h24 => by
      have h0 := hI.1.choose_spec.choose_spec
      obtain ⟨q1, -⟩ := tmin_facts (BXI.blk hI) h0.cur h1
      obtain ⟨p1, p2⟩ := hI.2.2.1.1.ntP _ (hI.2.2.1.2.2.bnd _ q1 h2)
      exact ⟨by unfold Aligned; rw [ntfn_word_val p1 p2 hk]; omega,
        Or.inr (fire_wrV hK hI hL E.ntw hok hTm (Or.inr (Or.inr ⟨h1, h2, k, hk, h8, h24, rfl⟩)))⟩)
    (fun hep k h1 h2 => by
      obtain ⟨hH, hal⟩ := hPE hep
      have o := lkw_own hI hL (Lk := lk s) (fun _ h => h) (Or.inr ⟨p.ep, (hPL s).2.1 hep, hOL.1 _ hH k h1⟩)
      exact ⟨vRd _ (hal k h1 h2) (by rw [hOL.1 _ hH k h1]; simp) o.2, vWr _ (hal k h1 h2) o.1⟩)
    (fun hr => by
      obtain ⟨hR, hal⟩ := hPR hr
      have o := lkw_own hI hL (Lk := lk s) (w := rTcbA p.reply) (fun _ h => h)
        (Or.inr ⟨p.reply, (hPL s).2.2 hr, by unfold rTcbA; exact hOL.2 _ hR _ (by simp [layout.reply.TCB])⟩)
      exact vWr _ hal o.1)
    hU hbU hE.asid (fun y hy => slot_rdV hK hT hSL hL.user hy)
    ⟨hE.kr.1, Or.inr (rpermV_of_own hE.kr.2.2 (rperm_none hE.kr.2.1 _))⟩
    (fun hi hhi => ⟨⟨(hE.tab hi hhi).1.1, Or.inr (rpermV_of_own (hE.tab hi hhi).1.2.2
        (rperm_none (hE.tab hi hhi).1.2.1 _))⟩,
      fun lo hlo hne => ⟨((hE.tab hi hhi).2 lo hlo hne).1, Or.inr (rpermV_of_own ((hE.tab hi hhi).2 lo hlo hne).2.2
        (rperm_none ((hE.tab hi hhi).2 lo hlo hne).2.1 _))⟩⟩)
    hq hWk h

end own

section mv
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayoutV}
variable {A : Type} (ar : machine.Arch A) {lk : S → U64 → Prop}

set_option maxHeartbeats 16000000 in
/-- **`move` of an accepted `local_vm_timer_irq` in the waking fire case**, under `ownV`: `vtimer_accG_fwk` on the
store whose writes are `ownV`'s `StepOK` (every write not deciding (`*_nondec`), or a `STATE` / tree write by
`stepOK_state` / `stepOK_height` / `stepOK_deadline` with `hM`), then `interp_gd`. -/
theorem vtimer_move_fwk (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hU : UserOKV K) (hNt : ∀ q ∈ Nt, H q = some .ntfn)
    {m : U64 → U64} {F : ∀ {A : Type}, machine.Arch A → machine.Store S → S → A → Result (Bool × S × A)}
    {p : SProg Bool} {irq n : U64} {pl : localtimer.TimerIrqPlan} {U : Set U64}
    (hF : IsProg F p)
    (eF : ∀ mm : machine.Store S, F ar mm = fun s a => localvm.handle_vm_timer_irq_local mm ar s a irq pl n)
    {s s' : S} {a a' : A}
    (hE : VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s) (hOL : ObjLay K.toKLayout H Rp) (hPL : PlanLk lk pl)
    (hUs : UserOK st T Cs Ω H U s) (hbU : ∀ y ∈ T, msg.lookup_ipc_buffer st s true y ⦃ b => BufOK U b ⦄)
    (pSg : core.num.U64.wrapping_add (vOf st s) vcpu.PENDING ∉ Sg)
    (hM : ∀ y ∈ T, m (fld y oAFFINITY) = L.mem s (affA y))
    (hq : IrqFire st ar s a) (hWk : ¬ NoWake st s)
    (h : localvm.handle_vm_timer_irq_local st ar s a irq pl n = ok (true, s', a')) :
    localvm.handle_vm_timer_irq_local (mguard st
      (fun x y => StepOK (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) (L.cpu s) (lk s)
        (L.mem x) (L.mem y))) ar s a irq pl n = ok (true, s', a') := by
  obtain ⟨hvb, hv0, hbn⟩ := vtimer_bnd ar h
  obtain ⟨-, tip, -, -, -, etip, eb, -⟩ := vtimer_split ar h
  obtain ⟨hPE, hPR⟩ := plan_pe_pr hE.ent.inv etip eb
  have E := hE.ent
  have hI := E.inv
  have hL := E.lay
  have hT : TcbPlaced T := hI.1.choose_spec.choose_spec.tcbs
  have heap : ∀ y ∈ T, K.heap y = some .tcb := fun y hy =>
    hK.base.tcbOf y _ (hL.tcb y hy 3328#u64 (by simp) (by simp))
  have es : ∀ y, stA y = fld y oSTATE := fun y => by rw [stA_eq]; rfl
  have eB : ∀ y, blockA y = fld y oBLOCK_OBJ := fun y => by rw [blockA_eq]; rfl
  have nd : ∀ {w : U64} (x : S) (v' : U64), Aligned w → ¬ DecW K.toKLayout w →
      StWrOKV st K m (L.cpu s) (lk s) x w v' := fun x v' ha hd => by
    unfold StWrOKV; exact stepOKV_of_stepOK hK (stepOK_nondec hK.base hU.base ha hd)
  have hg : localvm.handle_vm_timer_irq_local (gd st (fun _ => True) (StWrOKV st K m (L.cpu s) (lk s))) ar s a
      irq pl n = ok (true, s', a') := by
    refine vtimer_accG_fwk (gS := gd st (fun _ => True) (StWrOKV st K m (L.cpu s) (lk s))) (R := fun _ => True)
      (W := WAll (StWrOKV st K m (L.cpu s) (lk s))) (Lk := lk s) (U := U) ar hA hI hNt (fun _ _ _ _ _ => trivial)
      (fun _ _ w ha hw hn x v' => nd x v' ha (fire_wr_nondecV hK hI hL E.ntw hw hn))
      (fun _ _ => trivial) trivial trivial ?_
      (fun X y v' hy _ hc => gd_write (by
        show StWrOKV st K m (L.cpu s) (lk s) X (thA y) v'
        unfold StWrOKV
        exact stepOKV_of_stepOK hK (stepOK_height hK.base hU.base (heap y hy) hc)))
      (fun X y v' hy _ ha1 ha0 hc => gd_write (by
        show StWrOKV st K m (L.cpu s) (lk s) X (tdA y) v'
        unfold StWrOKV
        exact stepOKV_of_stepOK hK
          (stepOK_deadline hK.base hU.base (heap y hy) ha1 (by rw [hM y hy]; exact ha0) hc)))
      hvb trivial (fun _ => trivial) (E.vfar hv0) (fun hn => E.nfar n hbn hn) pSg (pending_not_q hK hE hOL hv0)
      E.aff (fun _ _ _ _ _ _ _ _ => trivial)
      (fun y hy k h1 h2 h3 hga ht _ n1 n2 x v' => nd x v' (field_aligned (hT y hy.1) h2 h3)
        (locw_nondec hK.base hT hL hy.1 h1 h2 hga ht n1 n2))
      (fun _ _ _ _ _ _ => trivial)
      (fun q hq _ b ha hb h16 x v' => nd x v' ha (scw_nondec hK.base hL hq hb h16))
      (fun y hy hqs hlk k hk => ⟨trivial, fun x v' => nd x v' (field_aligned (hT y hy) (K := k) (by omega) (by omega))
        (lkw_nondec hK.base hI hL (Lk := lk s) (Or.inl ⟨y, hy, hqs, hlk, k, hk, rfl⟩))⟩)
      (fun X y v' hy haff hq0 hv => gd_write (by
        show StWrOKV st K m (L.cpu s) (lk s) X (stA y) v'
        unfold StWrOKV
        rw [es]
        exact stepOKV_of_stepOK hK (stepOK_state hK.base hU.base (heap _ hy.1) haff (by rw [hM _ hy.1]; exact hy.2)
          (fun hq' => by rw [← eB]; exact hq0 (by rw [es]; exact hq')) (fun hq' => absurd hq' hv))))
      (fun hn => (hPL s).1 hn) (fun hep => (hPL s).2.1 hep)
      (fun _ _ h1 h2 k hk h8 _ x v' => by
        have h0 := hI.1.choose_spec.choose_spec
        obtain ⟨q1, -⟩ := tmin_facts (BXI.blk hI) h0.cur h1
        have hNN := hI.2.2.1.2.2.bnd _ q1 h2
        obtain ⟨p1, p2⟩ := hI.2.2.1.1.ntP _ hNN
        refine nd x v' (by unfold Aligned; rw [ntfn_word_val p1 p2 hk]; omega)
          (nondec_of_region hK.base (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, E.ntw _ hNN k hk, ?_⟩))))))
        rw [ntfn_word_val p1 p2 hk]; omega)
      (fun hep k h1 h2 => by
        obtain ⟨hH, hal⟩ := hPE hep
        exact ⟨trivial, fun x v' => nd x v' (hal k h1 h2)
          (lkw_nondec hK.base hI hL (Lk := lk s) (Or.inr ⟨pl.ep, (hPL s).2.1 hep, hOL.1 _ hH k h1⟩))⟩)
      (fun hr x v' => by
        obtain ⟨hR, hal⟩ := hPR hr
        exact nd x v' hal (lkw_nondec hK.base hI hL (Lk := lk s) (w := rTcbA pl.reply)
          (Or.inr ⟨pl.reply, (hPL s).2.2 hr, by unfold rTcbA; exact hOL.2 _ hR _ (by simp [layout.reply.TCB])⟩)))
      hUs hbU hE.asid (fun _ _ => ⟨trivial, trivial⟩) trivial (fun _ _ => ⟨trivial, fun _ _ _ => trivial⟩)
      hq hWk h
    intro s1 _ c1 _ now
    have mr : ∀ c t : U64, MayRdC st (fun _ => True) s1 c t := fun _ _ _ =>
      ⟨trivial, fun _ => ⟨trivial, trivial, trivial, trivial, fun _ => trivial⟩⟩
    have tr : TopRdC st (fun _ => True) s1 :=
      { l1 := trivial, dom := trivial, bm := ⟨trivial, fun _ _ => trivial⟩
        top := fun _ _ _ _ _ _ _ => ⟨trivial, fun _ => ⟨trivial, fun _ => ⟨trivial, trivial, trivial, trivial,
          fun _ => trivial⟩⟩⟩ }
    have wr : ∀ w n : U64, WakeRdC st (fun _ => True) s1 w n := fun w n =>
      { may := mr _ w, dq := fun _ _ => ⟨trivial, trivial⟩, nsc := trivial, top := tr }
    have := fire_ok.guardK (gS := gd st (fun _ => True) (StWrOKV st K m (L.cpu s) (lk s))) (R := fun _ => True)
      (s := s1) (ct := L.curW s) (p := pl) (now := now)
      (fun _ => True) (fun _ => trivial) (fun _ => trivial) (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
      (fun _ _ => ⟨trivial, fun _ _ _ => trivial⟩) (fun _ _ => trivial)
      (fun _ => fireTail.guardC (fun _ => ⟨trivial, trivial, trivial, trivial, wr _ _, fun _ _ => wr _ _⟩))
    rwa [c1] at this
  have eP : ∀ mm : machine.Store S, localvm.handle_vm_timer_irq_local mm ar s a irq pl n = interp mm ar p s a := by
    intro mm
    have e1 := congrFun (congrFun (eF mm) s) a
    have e2 := congrFun (congrFun (hF A ar mm) s) a
    rw [← e1]
    exact e2
  rw [eP] at hg
  rw [eP]
  exact interp_gd (R := fun _ => True) (P := StWrOKV st K m (L.cpu s) (lk s))
    (Q := fun x y => StepOK (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) (L.cpu s)
      (lk s) (L.mem x) (L.mem y)) (I := fun _ => True)
    (fun x q w x' _ hq hw => by
      rw [L.write_eq] at hw
      have e := ok_inj_ff hw
      subst e
      exact ⟨hq, trivial⟩) p s a _ trivial hg

end mv

section lp
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayoutV}
variable {A : Type} (ar : machine.Arch A) {irq n : U64} {pl : localtimer.TimerIrqPlan} {lk : S → U64 → Prop}
  {p : SProg Bool} {m : U64 → U64}

/-- **`local_vm_timer_irq` is a local path under `ownV`, the whole fire case proved** (lvm gen 10):
`vtimer_localPathW` with its waking-case `hF` / `hFm` discharged by `vtimer_acc_fwk_own` / `vtimer_move_fwk`.

Premises: as `vtimer_localPathW` without `hF` / `hFm` — [P] `hp` `IsProg`, [W] `hz` `NoZero`, [P] `hm` `MasksWr`,
[W] `hro` `ReadOnce`, [J] `hK` `RegionOKV`, [J] `hU` `UserOKV`, [J] `hEU` (`VtmEnt` survives an aligned user write),
[P] `hlk` (so do the glue's locks, aligned user writes), `hNt` (P1's notifications typed in `H`), [J] `hM` (the
map memory agrees with the entry on every thread's `AFFINITY`; discharged at the family level as `IrqEntK.mem`) —
plus, for the waking case (the native timer path's `irq_localPathP3` asks the same):

* [J] `hOL` (`ObjLay`: endpoints and replies lie in their object regions);
* [P] `hPL` (`PlanLk`: the glue holds the plan's notification / endpoint / reply locks);
* [J] `hUB` (at every entry state some user-word set `U` with P1 `UserOK` and every TCB's IPC-buffer lookup in it);
* [J] `hSL` (`SlotLayV`: the VSpace slot words of this core's threads lie in TCB slot regions);
* [J] `hpSg` (the bound VCPU's `PENDING` is no frame word `Sg`: P2 `usrW_vcpu`'s `UsrW.sg` at `Sg = H.frame`). -/
noncomputable def vtimer_localPathF (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hU : UserOKV K)
    (hp : IsProg (vtimerBody S irq pl n) p) (hz : NoZero p) (hm : E2E.MasksWr st)
    (hro : E2E.ReadOnce st ar p (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user)
      (VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n) (VexitRS K st lk))
    (hEU : ∀ s b v', VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s → b ∈ K.user → Aligned b →
      VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n (L.wr s b v'))
    (hlk : ∀ s b v', b ∈ K.user → Aligned b → lk (L.wr s b v') = lk s)
    (hNt : ∀ q ∈ Nt, H q = some .ntfn)
    (hM : ∀ s, VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s → ∀ y ∈ T, m (fld y oAFFINITY) = L.mem s (affA y))
    (hOL : ObjLay K.toKLayout H Rp) (hPL : PlanLk lk pl)
    (hUB : ∀ s, VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s →
      ∃ U : Set U64, UserOK st T Cs Ω H U s ∧ ∀ y ∈ T, msg.lookup_ipc_buffer st s true y ⦃ b => BufOK U b ⦄)
    (hSL : ∀ s, VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s → SlotLayV K.toKLayout st T s)
    (hpSg : ∀ s, VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s →
      core.num.U64.wrapping_add (vOf st s) vcpu.PENDING ∉ Sg) :
    E2E.LocalPath (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) :=
  vtimer_localPathW ar hA hK hU hp hz hm hro hEU hlk
    (fun s a s1 a1 hE hf hw h => by
      obtain ⟨U, hUs, hb⟩ := hUB s hE
      exact vtimer_acc_fwk_own ar hA hK hNt hE hOL hPL hUs hb (hSL s hE) (hpSg s hE) hf hw h)
    (fun s a s1 a1 hE hf hw h => by
      obtain ⟨U, hUs, hb⟩ := hUB s hE
      exact vtimer_move_fwk ar hA hK hU hNt hp (fun _ => rfl) hE hOL hPL hUs hb (hpSg s hE) (hM s hE) hf hw h)
    hNt hM

end lp

end Fl4Proofs.P2
