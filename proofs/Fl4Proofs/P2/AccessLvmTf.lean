/-
# P2 (line lvm, gen 9): **`local_vm_timer_irq`'s fire case when the signal wakes nobody**

The timer interrupt's fire walk split over its prefix as the quiet / round-robin walks were in gen 8:
`irq_accG_fire_core` (`P2/FootTimerFireP.lean`: the checks, `update_timestamp`, `check_budget`,
`handle_interrupt`, from the facts `current_ok` gave) and `fire_tail_nw_core` (`P2/FootTimerFireNw.lean`: `fire`,
`schedule`, `activate_thread` when `NoWake`, returning the frame at the `schedule` result instead of the final
`vcpu::check`). Here:

* `fireTail_vm`: an accepted `fireTail` whose notification is quiet, idle or not waiting, and bound to a thread
  running a VM is impossible (`fireTail_idle`);
* **`vtimer_accG_fnw`**: an accepted VM-timer run in the fire case with `NoWake` is the same run on any `GRd` /
  `GWr` store answering `FireRd` / `FireWr` (as `fire_tail_nw`), the kernel-global words, the IRQ state word, a
  declined-or-not `fire_ok` (`gfire`), the tree's deadline / height writes (`hwH` / `hwD`), the bound VCPU's
  `PENDING` and the bound notification's `TAIL_STATE`. Both `vcpu::check`s are no-ops (`vcpu.check_np` /
  `vcpu.check.guard_vmq`): the fire's writes miss `PENDING` (`sP`: not the due notification's state / badge word)
  and the bound notification's `TAIL_STATE` (the due notification is not the current thread's: an idle bound
  notification of a thread running a VM declines `fire_ok`, `fireTail_vm`);
* `fire_rdV` / `fire_wrV`: `FireRd` / `FireWr` under `ownV` (typed regions: `rpV`, `wpermV_of_own'`) from
  `VexitEnt`'s layout fields;
* **`vtimer_acc_fnw_own`**: `PathObl.acc` of that case on `guard st (VexitRS …) (VexitWS …)` from `VtmEnt` and
  `hNt`; **`vtimer_move_fnw`**: its `PathObl.move` (`fire_wr_nondecV`, `stepOK_height` / `stepOK_deadline`, `hM`);
* **`vtimer_localPathW`**: `vtimer_localPath` with `hF` / `hFm` asked only for the waking fire case.

Premises: `VtmEnt`, `hNt` (P1's notifications typed in `H`), and for `move` **`hM` [J]** (the map memory agrees
with the entry on every thread's `AFFINITY`, as `IrqEntK.mem`). The waking fire case (`¬ NoWake`: the due
notification wakes its waiting / receiving thread, then `schedule` may switch) stays [W] `hF` / `hFm` of
`vtimer_localPathW`.
-/
import Fl4Proofs.P2.AccessLvmTj
import Fl4Proofs.P2.FootTimerFireOwn
import Fl4Proofs.P2.FootTimerFireAk
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.Serial (Owner)
open Fl4Proofs.P2.OwnMapV (KLayoutV ownV InVcpu RegionOKV UserOKV rpermV_of_own wpermV_of_own'
  stepOKV_of_stepOK)

section help
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **An accepted `fireTail` cannot signal a quiet notification bound to a thread running a VM** (module
docstring). -/
theorem fireTail_vm {s : S} {cpu c : U64} {ct : obj.Tcb} {p : localtimer.TimerIrqPlan}
    (h : fireTail st s cpu ct p = ok true) (hn : p.ntfn ≠ 0#u64)
    (hA : L.epState s p.ntfn ≠ obj.NTFN_ACTIVE)
    (hW : L.epState s p.ntfn = obj.NTFN_IDLE ∨ L.epState s p.ntfn ≠ obj.NTFN_WAITING)
    (hbt : L.mem s (ntfnBtA p.ntfn) = c) (hc0 : c ≠ 0#u64) (hst : L.mem s (stA c) = sched.TS_RUNNING_VM) :
    False := by
  by_cases hI : L.epState s p.ntfn = obj.NTFN_IDLE
  · obtain ⟨e1, e2⟩ := fireTail_idle h hn hI (by rw [hbt]; exact hc0)
    rw [hbt] at e1
    rw [← e1] at e2
    exact e2 hst
  · have hW' := hW.resolve_left hI
    unfold fireTail at h
    rw [if_neg hn, eq_of_spec_fd (obj.Ntfn.state.spec (L := L) s _)] at h
    simp only [bind_ok] at h
    rw [if_neg hA, if_neg hI, if_neg hW'] at h
    exact Bool.false_ne_true (ok_inj_ff h)

end help

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 32000000 in
/-- **An accepted VM-timer run in the fire case, nobody woken, on the guarded store** (module docstring). -/
theorem vtimer_accG_fnw {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
    (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {irq n v : U64} {p : localtimer.TimerIrqPlan}
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
    (sP : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64 →
      L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) ≠ 0#u64 →
      ¬ SaD (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))))
        (core.num.U64.wrapping_add v vcpu.PENDING))
    (hq : IrqFire st ar s a) (hNW : NoWake st s)
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
  have hSg := hI.2.2.2.1
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
  have ecpu : st.cur_cpu s = ok (L.cpu s) := by rw [L.cur_cpu_eq]
  have ecsc : sched.cur_sc st s = ok (L.cscW s) := eq_of_spec_fd (sched.cur_sc.spec (L := L) s)
  -- the prefix and the fire tail, by the timer interrupt's cores
  have G := irq_accG_fire_core (gS := gS) ar hA hI (fun _ w ha hw => gRd' w ha (Or.inl hw))
    (fun _ w ha hw hn => gWr' w ha (Or.inl hw) hn) (fun _ => hIq) (fun _ => hD1) (fun _ => hD2) ecpu emx hle ei1
    etip eb (cur_thread_ok s) ecsc haff hsct hcore eq eu enow erel ei2 eb4 edue efo ecb ehi
  obtain ⟨gsc, rSt', post⟩ := fire_tail_nw_core (gS := gS) ar hA hI hNt hok gRd' gWr' hD2
    (fun hr => absurd (hstv.symm.trans hr) (by simp [sched.TS_RUNNING_VM, sched.TS_RESTART])) hwH hwD hNW etip eb eq
    hy0 eu enow erel ei2 eb4 edue efo ecb emx hle ei1 ehi
  obtain ⟨hcur4, tK4, fr4, gac, post5⟩ := post s5 a5 esc
  -- the due notification is not the current thread's bound one
  have hnN : n ≠ 0#u64 → L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) ≠ 0#u64 →
      ¬ SaD (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))))
      (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE) := by
    intro hn0 hNF0 hsd
    have hbn : L.mem s (boundA (L.curW s)) = n := by
      rw [eq_of_spec_fd (obj.Tcb.bound_ntfn.val (L := L) s _)] at en; exact ok_inj_ff en
    have hnNt : n ∈ Nt := by rw [← hbn]; exact hX.2.2.bnd _ hcT (by rw [hbn]; exact hn0)
    have q1 := (tmin_facts (BXI.blk hI) hcC hTM0).1
    obtain ⟨p1, p2⟩ := hO.ntP _ hnNt
    have eTS : core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE = epTSA n := by
      apply UScalar.eq_of_val_eq
      unfold epTSA
      simp [core.num.U64.wrapping_add_val_eq, layout.ntfn.TAIL_STATE, layout.ep.TAIL_STATE]
    have hNNt := hX.2.2.bnd _ q1 hNF0
    obtain ⟨r1, r2⟩ := hO.ntP _ hNNt
    -- the two notifications coincide
    have eN : L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) = n := by
      rcases hsd with e | e
      · rw [eTS] at e
        apply UScalar.eq_of_val_eq
        have ev := congrArg UScalar.val e
        rw [epTSA_val' (by omega), epTSA_val' (by omega)] at ev
        omega
      · exfalso
        rw [eTS] at e
        have ev := congrArg UScalar.val e
        rw [epTSA_val' (by omega), ntfnBdA_val ⟨r1, r2⟩] at ev
        omega
    -- its state and bound thread at `s1`
    have oT : OutsideObjs st T Cs s (epTSA n) := by rw [← eTS]; exact (fN hn0).1
    have oBt : OutsideObjs st T Cs s (ntfnBtA n) := h0.omega _ (hSg.sub _ (hO.ntB n hnNt).2)
    have eSt1 : L.epState s1 n = L.epState s n := by unfold LawfulStore.epState; rw [hout1 _ oT]
    have hbt : L.mem s1 (ntfnBtA n) = L.curW s := by
      rw [hout1 _ oBt, ← hbn]; exact hX.2.2.bs.tb _ hcT (by rw [hbn]; exact hn0)
    have hst1 : L.mem s1 (stA (L.curW s)) = sched.TS_RUNNING_VM := by
      rw [stA_eq, htcb1 hcT (by simp) (by simp), ← stA_eq]; exact hstv
    have hA1 : L.epState s1 n ≠ obj.NTFN_ACTIVE := by
      rw [eSt1]
      exact hnq hn0 _ (eq_of_spec_fd (obj.Ntfn.state.spec (L := L) s n))
    have hpn : p.ntfn = n := hpN.trans eN
    have hW1 : L.epState s1 n = obj.NTFN_IDLE ∨ L.epState s1 n ≠ obj.NTFN_WAITING := by
      rw [eSt1]
      have hNW' := hNW
      unfold NoWake at hNW'
      rw [eN] at hNW'
      rcases hNW' with e | ⟨-, e⟩ | ⟨e, -⟩
      · exact absurd e hn0
      · exact Or.inr e
      · exact Or.inl e
    rw [← hpn] at hA1 hW1 hbt
    exact fireTail_vm (fire_ok_tail efo) (by rw [hpn]; exact hn0) hA1 hW1 hbt
      (fun e => ht'.ne0 (by rw [e]; simp)) hst1
  -- `activate_thread` keeps the `RUNNING_VM` thread
  have hy5 : L.mem s5 (yieldA (L.curW s)) = 0#u64 := by
    unfold yieldA; rw [tK4 _ (by simp) (by simp) (Or.inl (by simp))]; exact hy0
  have hs5 : L.mem s5 (stA (L.curW s)) = L.mem s (stA (L.curW s)) := by
    rw [stA_eq, tK4 _ (by simp) (by simp) (Or.inl (by simp))]
  have eac' := activate_id ar s5 a5 (by rw [hcur4]; exact hy5)
    (by rw [hcur4, hs5, hstv]; simp [sched.TS_RUNNING_VM, sched.TS_RESTART])
  have eac2 := eac
  rw [eac'] at eac2
  obtain ⟨rfl, rfl⟩ : s5 = s6 ∧ a5 = a6 := by
    have e := ok_inj_ff eac2
    simp only [Prod.mk.injEq] at e
    exact e
  obtain ⟨gt, -, -⟩ := post5 s5 a5 eac
  have ht : t = L.curW s := by
    rw [cur_thread_ok, hcur4] at ett
    exact (ok_inj_ff ett).symm
  subst ht
  -- the final `vcpu.check` reports nothing
  have eb5 : vcpu.bound st s5 (L.curW s) = ok v := by
    rw [vcpu_bound_congr (tK4 _ (by simp) (by simp) (Or.inr (by simp)))]; exact hvb
  have en5 : obj.Tcb.bound_ntfn st (L.curW s) s5 = ok n := by
    rw [bound_ntfn_congr (by unfold boundA; exact tK4 _ (by simp) (by simp) (Or.inl (by simp)))]
    exact en
  have ep5 : vcpu.get st s5 v vcpu.PENDING = ok 0#u64 := by
    rw [vcpu_get_congr (fr4 _ fP (fun ⟨h1, h2⟩ => sP hTM0 h1 h2))]; exact hp0
  have hq5 : n ≠ 0#u64 → ∀ x, obj.Ntfn.state st n s5 = ok x → x ≠ obj.NTFN_ACTIVE := fun hn x ex =>
    hnq hn x (by rw [← ntfn_state_congr (fr4 _ (fN hn) (fun ⟨h1, h2⟩ => hnN hn h1 h2))]; exact ex)
  have gvc5 := vcpu.check.guard_vmq (gS := gS) ar s5 a5 (L.curW s) v n rSt' rVc rBn hRp hRn eb5 hv0 ep5 en5 hq5
  have gfin : localvm.finish gS ar s4 a4 = ok (s', a') := by
    unfold localvm.finish
    rw [gsc, esc]
    simp only [bind_ok, uncurry_apply_pair]
    rw [gac, eac']
    simp only [bind_ok, uncurry_apply_pair]
    rw [gt, ett]
    simp only [bind_ok]
    rw [gvc5]
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

/-- The owner of a word of the due thread's bound notification (`fnt_ownE` from the notification regions). -/
theorem fnt_ownEV {s : S} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ntw : ∀ p ∈ Nt, ∀ k : U64, k.val < 64 → region K.toKLayout (core.num.U64.wrapping_add p k) = .ntfn p)
    (hne : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64)
    (hb : L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) ≠ 0#u64) {k : U64}
    (hk : k.val < 64) :
    region K.toKLayout (core.num.U64.wrapping_add
        (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))) k) ≠ .none ∧
    own K.toKLayout (L.mem s) (core.num.U64.wrapping_add
        (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))) k) =
      ntfnOwner K.toKLayout (L.mem s) (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))))
        k.val := by
  have h0 := hI.1.choose_spec.choose_spec
  obtain ⟨q1, -⟩ := tmin_facts (BXI.blk hI) h0.cur hne
  have hNt := hI.2.2.1.2.2.bnd _ q1 hb
  obtain ⟨p1, p2⟩ := hI.2.2.1.1.ntP _ hNt
  refine ⟨(by rw [ntw _ hNt k hk]; intro e; cases e), ?_⟩
  simp only [own, ntw _ hNt k hk]
  rw [ntfn_word_val p1 p2 hk, Nat.add_sub_cancel_left]

/-- A word of the due thread's bound notification other than `BOUND_TCB` is this core's (`fnt_own`). -/
theorem fnt_ownV (hK : RegionOKV K) {s : S} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hL : StLay K.toKLayout st T Scs Z s)
    (ntw : ∀ p ∈ Nt, ∀ k : U64, k.val < 64 → region K.toKLayout (core.num.U64.wrapping_add p k) = .ntfn p)
    (hne : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64)
    (hh : TmHere st s (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))
    (hb : L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) ≠ 0#u64) {k : U64}
    (hk : k.val < 64) (h24 : k.val ≠ 24) :
    own K.toKLayout (L.mem s) (core.num.U64.wrapping_add
        (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))) k) = .core (L.cpu s) := by
  have h0 := hI.1.choose_spec.choose_spec
  obtain ⟨q1, -⟩ := tmin_facts (BXI.blk hI) h0.cur hne
  have ha : L.mem s (affA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) = L.cpu s := by
    have e := hh.1
    rw [eq_of_spec_fd (obj.Tcb.affinity.spec (L := L) s _)] at e
    exact ok_inj_ff e
  have hbt := hI.2.2.1.2.2.bs.tb _ q1 hb
  have eB : L.mem s (fld (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))) 24#u64) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) := by
    have eA : fld (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))) 24#u64 =
        ntfnBtA (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))) := by
      unfold fld ntfnBtA layout.ntfn.BOUND_TCB
      rfl
    rw [eA]; exact hbt
  have ht : K.heap (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)) = some .tcb :=
    hK.base.tcbOf _ _ (hL.tcb _ q1 3328#u64 (by simp) (by simp))
  rw [(fnt_ownEV hI ntw hne hb hk).2, ntfnOwner, if_neg h24, eB, if_pos ht]
  exact congrArg Owner.core ha

/-- **Every word of `FireRd` is readable under `ownV`** (each lies in a typed region). -/
theorem fire_rdV (hK : RegionOKV K) {s : S} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hL : StLay K.toKLayout st T Scs Z s)
    (ntw : ∀ p ∈ Nt, ∀ k : U64, k.val < 64 → region K.toKLayout (core.num.U64.wrapping_add p k) = .ntfn p)
    (cs : ∀ k : U64, k.val < 192 → k.val % 32 < 16 → ∃ p,
      region K.toKLayout (core.num.U64.wrapping_add (L.curW s) k) = .slot p ∧ TcbSlot K.toKLayout p ∧
        (core.num.U64.wrapping_add (L.curW s) k).val - p.val < 16)
    (hAff : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t))
    (hok : IrqOk st s)
    (hTm : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64 →
      TmHere st s (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))
    {lk : U64 → Prop} {w : U64} (h : FireRd st T Z s w) :
    RPerm (ownV K) (L.cpu s) lk (L.mem s) w := by
  have hT : TcbPlaced T := hI.1.choose_spec.choose_spec.tcbs
  rcases h with h | ⟨y, hy, ha, k, h1, h2, h8, rfl⟩ | ⟨hne, hb, k, hk, -, rfl⟩
  · exact vexit_rd hK hI hL ntw cs hAff hok.aff hok.core h
  · refine rpV hK ?_ (Or.inl (held_core (ftree_own hL hT hy ha h1 h2 h8)))
    have e := hL.tcb _ hy k (by omega) (by omega)
    unfold fld at e
    rw [e]; intro e; cases e
  · obtain ⟨hr, ho⟩ := fnt_ownEV hI ntw hne hb hk
    by_cases h24 : k.val = 24
    · refine rpV hK hr (Or.inr ?_)
      unfold GateOnly
      rw [ho, ntfnOwner, if_pos h24]
    · exact rpV hK hr (Or.inl (held_core (fnt_ownV hK hI hL ntw hne (hTm hne) hb hk h24)))

/-- **Every word of `FireWr` is writable under `ownV`** (`fire_wr_own` with `fnt_ownV`). -/
theorem fire_wrV (hK : RegionOKV K) {s : S} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hL : StLay K.toKLayout st T Scs Z s)
    (ntw : ∀ p ∈ Nt, ∀ k : U64, k.val < 64 → region K.toKLayout (core.num.U64.wrapping_add p k) = .ntfn p)
    (hok : IrqOk st s)
    (hTm : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64 →
      TmHere st s (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))
    {lk : U64 → Prop} {w : U64} (h : FireWr st T Z s w) :
    WPerm (ownV K) (L.cpu s) lk (L.mem s) w := by
  have hT : TcbPlaced T := hI.1.choose_spec.choose_spec.tcbs
  refine wpermV_of_own' hK ?_
  rcases h with h | ⟨y, hy, ha, k, h1, h2, h8, rfl⟩ | ⟨hne, hb, k, hk, -, h24, rfl⟩
  · exact irq_wr_own hI hL hok h
  · exact held_core (ftree_own hL hT hy ha (by omega) (by omega) h8)
  · exact held_core (fnt_ownV hK hI hL ntw hne (hTm hne) hb hk h24)

/-- **No word of `FireWr` but the current thread's `STATE` decides anything** (`fire_wr_nondec` from the
notification regions). -/
theorem fire_wr_nondecV (hK : RegionOKV K) {s : S} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hL : StLay K.toKLayout st T Scs Z s)
    (ntw : ∀ p ∈ Nt, ∀ k : U64, k.val < 64 → region K.toKLayout (core.num.U64.wrapping_add p k) = .ntfn p)
    {w : U64} (h : FireWr st T Z s w) (hn : w ≠ stA (L.curW s)) : ¬ DecW K.toKLayout w := by
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  rcases h with h | ⟨y, hy, -, k, h1, h2, -, rfl⟩ | ⟨hne, hb, k, hk, -, h24, rfl⟩
  · exact irq_wr_nondec hK.base hI hL h hn
  · apply nondec_of_region hK.base
    have e : (core.num.U64.wrapping_add y k).val - y.val = k.val := by
      rw [field_val (hT y hy) (by omega)]; omega
    exact Or.inl ⟨y, hL.tcb y hy k (by omega) (by omega), by omega, by omega, by omega, by omega, by omega⟩
  · apply nondec_of_region hK.base
    obtain ⟨q1, -⟩ := tmin_facts (BXI.blk hI) h0.cur hne
    have hNt := hI.2.2.1.2.2.bnd _ q1 hb
    obtain ⟨p1, p2⟩ := hI.2.2.1.1.ntP _ hNt
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, ntw _ hNt k hk, ?_⟩))))
    rw [ntfn_word_val p1 p2 hk]
    omega

/-- The bound VCPU's `PENDING` is no state / badge word of the due notification (a VCPU word is in no region). -/
theorem pending_not_sad (hK : RegionOKV K) {lk : S → U64 → Prop} {irq n : U64} {s : S}
    (hE : VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s) (hv0 : vOf st s ≠ 0#u64)
    (hne : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64)
    (hb0 : L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) ≠ 0#u64) :
    ¬ SaD (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))))
      (core.num.U64.wrapping_add (vOf st s) vcpu.PENDING) := by
  have E := hE.ent
  have hI := E.inv
  have h0 := hI.1.choose_spec.choose_spec
  obtain ⟨q1, -⟩ := tmin_facts (BXI.blk hI) h0.cur hne
  have hNNt := hI.2.2.1.2.2.bnd _ q1 hb0
  have hn := hK.none _ _ (E.vin hv0)
  intro hsd
  rcases hsd with e | e
  · rw [e] at hn
    unfold epTSA at hn
    rw [E.ntw _ hNNt _ (by simp [layout.ep.TAIL_STATE])] at hn
    cases hn
  · rw [e] at hn
    unfold ntfnBdA at hn
    rw [E.ntw _ hNNt _ (by simp [layout.ntfn.BADGE])] at hn
    cases hn

variable {A : Type} (ar : machine.Arch A) {lk : S → U64 → Prop}

/-- **`acc` of an accepted `local_vm_timer_irq` in the fire case with `NoWake`**, under `ownV` (module
docstring). -/
theorem vtimer_acc_fnw_own (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hNt : ∀ q ∈ Nt, H q = some .ntfn)
    {s s' : S} {a a' : A} {irq n : U64} {p : localtimer.TimerIrqPlan}
    (hE : VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s) (hq : IrqFire st ar s a) (hNW : NoWake st s)
    (h : localvm.handle_vm_timer_irq_local st ar s a irq p n = ok (true, s', a')) :
    localvm.handle_vm_timer_irq_local (guard st (VexitRS K st lk s) (VexitWS K st lk s)) ar s a irq p n =
      ok (true, s', a') := by
  have hb := vtimer_irq_lt ar h
  obtain ⟨hvb, hv0, hbn⟩ := vtimer_bnd ar h
  have E := hE.ent
  have hI := E.inv
  have hL := E.lay
  have hT : TcbPlaced T := hI.1.choose_spec.choose_spec.tcbs
  have rD : VexitRS K st lk s (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN) :=
    ⟨hL.domA, Or.inr (rpermV_of_own E.ksv.1 (rperm_none hL.dom _))⟩
  have wr : ∀ (X : S) (w v' : U64), VexitWS K st lk s w →
      (guard st (VexitRS K st lk s) (VexitWS K st lk s)).write X w v' = st.write X w v' :=
    fun X w v' hw => PathObl.GWr.write (g := guard st (VexitRS K st lk s) (VexitWS K st lk s)) hw X v'
  exact vtimer_accG_fnw (gS := guard st (VexitRS K st lk s) (VexitWS K st lk s)) (R := VexitRS K st lk s)
    (W := VexitWS K st lk s) ar hA hI hNt
    (fun hok hTm w ha hw => ⟨ha, Or.inr (fire_rdV hK hI hL E.ntw E.cs E.aff hok hTm hw)⟩)
    (fun hok hTm w ha hw _ => ⟨ha, Or.inr (fire_wrV hK hI hL E.ntw hok hTm hw)⟩)
    (fun i hi => ⟨(hE.iq hb i hi).1,
      Or.inr (rpermV_of_own (hE.iq hb i hi).2.2 (rperm_none (hE.iq hb i hi).2.1 _))⟩)
    rD ⟨hL.dtmA, Or.inr (rpermV_of_own E.ksv.2 (rperm_none hL.dtm _))⟩
    (fun s1 k1 c1 m1 now => by
      obtain ⟨mx, tip, -, -, -, etip, eb, -⟩ := vtimer_split ar h
      exact fire_rdG hK.base hI hL E.ntw (lk := lk s) (fun w hp ha hr => ⟨ha, Or.inr (rpV hK hr hp)⟩) rD hNt k1 c1
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
    (E.vfar hv0) (fun hn => E.nfar n hbn hn)
    (fun hne hb0 => pending_not_sad hK hE hv0 hne hb0)
    hq hNW h


/-- **`move` of an accepted `local_vm_timer_irq` in the fire case with `NoWake`**, under `ownV`: the run on the
checked store whose writes are `ownV`'s `StepOK` is the real one (`vtimer_accG_fnw`: `FireWr` words by
`fire_wr_nondecV`, the tree's height / deadline writes by `stepOK_height` / `stepOK_deadline`, the latter with the
map memory `m` agreeing on the armed threads' `AFFINITY`, `hM`), and `interp_gd` turns it into the run on
`mguard`. -/
theorem vtimer_move_fnw (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hU : UserOKV K) (hNt : ∀ q ∈ Nt, H q = some .ntfn)
    {m : U64 → U64} {F : ∀ {A : Type}, machine.Arch A → machine.Store S → S → A → Result (Bool × S × A)}
    {p : SProg Bool} {irq n : U64} {pl : localtimer.TimerIrqPlan}
    (hF : IsProg F p)
    (eF : ∀ mm : machine.Store S, F ar mm = fun s a => localvm.handle_vm_timer_irq_local mm ar s a irq pl n)
    {s s' : S} {a a' : A}
    (hE : VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s)
    (hM : ∀ y ∈ T, m (fld y oAFFINITY) = L.mem s (affA y))
    (hq : IrqFire st ar s a) (hNW : NoWake st s)
    (h : localvm.handle_vm_timer_irq_local st ar s a irq pl n = ok (true, s', a')) :
    localvm.handle_vm_timer_irq_local (mguard st
      (fun x y => StepOK (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) (L.cpu s) (lk s)
        (L.mem x) (L.mem y))) ar s a irq pl n = ok (true, s', a') := by
  obtain ⟨hvb, hv0, hbn⟩ := vtimer_bnd ar h
  have E := hE.ent
  have hI := E.inv
  have hL := E.lay
  have heap : ∀ y ∈ T, K.heap y = some .tcb := fun y hy =>
    hK.base.tcbOf y _ (hL.tcb y hy 3328#u64 (by simp) (by simp))
  have hg : localvm.handle_vm_timer_irq_local (gd st (fun _ => True) (StWrOKV st K m (L.cpu s) (lk s))) ar s a
      irq pl n = ok (true, s', a') := by
    refine vtimer_accG_fnw (gS := gd st (fun _ => True) (StWrOKV st K m (L.cpu s) (lk s))) (R := fun _ => True)
      (W := WAll (StWrOKV st K m (L.cpu s) (lk s))) ar hA hI hNt (fun _ _ _ _ _ => trivial)
      (fun _ _ w ha hw hn x v' => stepOKV_of_stepOK hK
        (stepOK_nondec hK.base hU.base ha (fire_wr_nondecV hK hI hL E.ntw hw hn)))
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
      hvb trivial (fun _ => trivial) (E.vfar hv0) (fun hn => E.nfar n hbn hn)
      (fun hne hb0 => pending_not_sad hK hE hv0 hne hb0) hq hNW h
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
    try simp only at e1
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

end own


section lp
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayoutV}
variable {A : Type} (ar : machine.Arch A) {irq n : U64} {pl : localtimer.TimerIrqPlan} {lk : S → U64 → Prop}
  {p : SProg Bool} {m : U64 → U64}

/-- **`local_vm_timer_irq` is a local path under `ownV`, its non-waking fire case's `acc` proved** (gen 9):
`vtimer_localPath` with `hF` asked only when the due notification wakes a thread (`¬ NoWake`); the non-waking
case is `vtimer_acc_fnw_own` / `vtimer_move_fnw`; `hFm` likewise only for `¬ NoWake`. New premise `hM` [J]: the map
memory `m` agrees with the entry on every thread's `AFFINITY` (as `IrqEntK.mem`), for the tree's deadline writes. -/
noncomputable def vtimer_localPathW (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hU : UserOKV K)
    (hp : IsProg (vtimerBody S irq pl n) p) (hz : NoZero p) (hm : E2E.MasksWr st)
    (hro : E2E.ReadOnce st ar p (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user)
      (VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n) (VexitRS K st lk))
    (hEU : ∀ s b v', VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s → b ∈ K.user → Aligned b →
      VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n (L.wr s b v'))
    (hlk : ∀ s b v', b ∈ K.user → lk (L.wr s b v') = lk s)
    (hF : ∀ s a s1 a1, VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s → IrqFire st ar s a → ¬ NoWake st s →
      localvm.handle_vm_timer_irq_local st ar s a irq pl n = ok (true, s1, a1) →
      localvm.handle_vm_timer_irq_local (guard st (VexitRS K st lk s) (VexitWS K st lk s)) ar s a irq pl n =
        ok (true, s1, a1))
    (hFm : ∀ s a s1 a1, VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s → IrqFire st ar s a → ¬ NoWake st s →
      localvm.handle_vm_timer_irq_local st ar s a irq pl n = ok (true, s1, a1) →
      localvm.handle_vm_timer_irq_local (mguard st
        (fun x y => StepOK (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) (L.cpu s)
          (lk s) (L.mem x) (L.mem y))) ar s a irq pl n = ok (true, s1, a1))
    (hNt : ∀ q ∈ Nt, H q = some .ntfn)
    (hM : ∀ s, VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s → ∀ y ∈ T, m (fld y oAFFINITY) = L.mem s (affA y)) :
    E2E.LocalPath (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) :=
  vtimer_localPath ar hA hK hU hp hz hm hro hEU hlk
    (fun s a s1 a1 hE hf h => by
      by_cases hNW : NoWake st s
      · exact vtimer_acc_fnw_own ar hA hK hNt hE hf hNW h
      · exact hF s a s1 a1 hE hf hNW h)
    (fun s a s1 a1 hE hf h => by
      by_cases hNW : NoWake st s
      · exact vtimer_move_fnw ar hA hK hU hNt hp (fun _ => rfl) hE (hM s hE) hf hNW h
      · exact hFm s a s1 a1 hE hf hNW h)
    hNt

end lp

end Fl4Proofs.P2
