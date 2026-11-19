/-
P3 (DESIGN.md §9), scheduling contexts: **the Yield system call at `J`**
(KENTRY-PLAN item 9: `handle_yield` = `charge_budget` of the head refill
without timeout faults, then the current SC's consumed word).

* `JAtZ.setScConsumedJ`: FL4's write of an SC's `CONSUMED` word (any value)
  at `J`, a register-frame step (`JAtZ.reg_frame`, as ScJointConsumed's
  `JAtZ.updConsumedJ`; the IPC relation by `sc_step_lift`, P1 by
  `consumedW_all`).
* `JAtZ.handleYieldJ`: FL4's `syscall::handle_yield` refines l4v
  `handle_yield` (the same reads: the SC's consumed word, the consumed time,
  the head refill's amount; `JAtZ.chargeBudgetJ`; the consumed word).
-/
import Fl4Proofs.P3.ScChargeJ
import Fl4Proofs.P3.ScJointConsumed
import Fl4Proofs.P3.XTopJointDispatch
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 8000000 in
/-- **An SC's `CONSUMED` word written at `J`** (module docstring). -/
theorem JAtZ.setScConsumedJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {p t : U64} (hpC : p ∈ Z.C)
    (ht : t ∈ Z.T) {z : Fl4Spec.SchedContext} {n : Nat} (hkz : σ.kheap p.bv = some (.schedContext z n)) (v : U64) :
    ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D (L.wr s (scW p 8#u64) v) a
      (updSc σ p.bv { z with scConsumed := v.bv } n) := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨z', n', hkz', hz⟩ := hs.scs p hpC
  rw [hkz] at hkz'; cases hkz'
  obtain ⟨x, hkx, -⟩ := hs.tcb t ht
  have hI := J.xtop.irelK J.ks J.buf
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hpS : p ∈ P1.Heap.scs H := ⟨_, (hJ.sc p z n (J.c0 p hpC) hkz).2⟩
  have hal : P1.Aligned (scW p 8#u64) := (hz.hdr (K := 8#u64) (by simp) (by simp)).1
  obtain ⟨hS1, -, -⟩ := hS.set_sc_consumed hpC hkz v
  have hW1 : P1.WritesIn st s (L.wr s (scW p 8#u64) v)
      (fun b => ScW st Z.C Z.c s σ b ∨ SFootI st Z.T Z.c s b) :=
    (P1.writesIn_wr hal).mono fun b hb => Or.inl (Or.inl (hb ▸ sw_hdr hS hpC (K := 8#u64) (by simp) (by simp) (by decide)))
  have hK := Ipc.nks_updateSchedContext p.bv (fun y => { y with scConsumed := v.bv }) σ ((), _)
    (by rw [updateSchedContext_eq hkz]; exact Set.mem_singleton _)
  have hI1 := sc_step_lift J.ip hI hW1 hK hS1
  set w : Fl4Spec.SchedContext := { z with scConsumed := v.bv } with hwd
  have hpt : p.bv ≠ t.bv := fun e => by rw [e, hkx] at hkz; cases hkz
  have hk1 : (updSc σ p.bv w n).kheap t.bv = some (.tcb x) := by
    simp only [updSc, updK, Function.update_of_ne hpt.symm]; exact hkx
  have eS : updK (updSc σ p.bv w n) t.bv (.tcb x) = updSc σ p.bv w n := by
    unfold updK; rw [← hk1, Function.update_eq_self]
  have hA := QKY.upd2 (w := w) (x' := x) hkz hkx rfl rfl
  have hyk := ykeep_upd2 (w := w) (x' := x) hkz hkx rfl rfl
  rw [eS] at hA hyk
  have hInv := J.inv.scFields (y' := w) hkz rfl rfl rfl rfl
  have ea : scW p 8#u64 = core.num.U64.wrapping_add p layout.sc.CONSUMED := by
    unfold scW layout.sc.CONSUMED; rfl
  obtain ⟨hB1, hF1, -⟩ := P1.consumedW_all (v := v) J.blk hpS
  rw [← ea] at hB1 hF1
  have hw : P1.WritesIn st s (L.wr s (scW p 8#u64) v) (RegCW Z.T Z.C) :=
    (P1.writesIn_wr (st := st) (s := s) (v := v) hal).mono fun b hb => Or.inr ⟨p, hpC, hb⟩
  exact J.reg_frame hI1 hw hA hyk hInv hB1 hF1

set_option maxHeartbeats 16000000 in
/-- **Yield at `J`** (KENTRY-PLAN item 9; module docstring): from `JAtZ` with
the current thread's `CurInv`, not the idle thread and not the switch
target, FL4's `handle_yield` refines l4v `handle_yield` and ends at `JAtZ`
(the VSpace sets and call lists existential). The platform's
`MAX_RELEASE_TIME` and `MIN_BUDGET` ([P], `hmrt`, `hmb`). -/
theorem JAtZ.handleYieldJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hAT : P0.ArchTotal arI)
    (hC : CurInv σ) (hni : σ.curThread ≠ σ.idleThread)
    (hnsw : σ.schedulerAction ≠ .switchThread σ.curThread)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) :
    syscall.handle_yield st arI s a ⦃ r => r.2 = a ∧ ∃ σ', Fl4Spec.handleYield (Z := Unit) σ = ({((), σ')}, False) ∧
      ∃ (V : XVs) (Lst' : U64 → List U64), JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst' D r.1 a σ' ⦄ := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨hscC, hsc0, htw, hts, hact, hnr, hnb⟩ := CurInv.facts hS J.inv hC
  have hct : nodeW st s Z.c layout.node.CUR_THREAD ∈ Z.T := hc.curT
  have hpc : (nodeW st s Z.c layout.node.CUR_SC).bv = σ.curSc := hs.curSc.symm
  obtain ⟨x, n, hk, hx⟩ := hs.scs _ hscC
  have hxa : Fl4Spec.scActive x = true := hact (by rw [hpc]; exact J.curSc_ne_idle hC hni) x n hk
  have hx1 := hx.strong hxa
  have hne : x.scRefills ≠ [] := by
    rw [hx1.refills]; intro e; exact refills_ne' hx1.wf (List.map_eq_nil_iff.1 e)
  unfold syscall.handle_yield
  step with sched.cur_sc.spec' as ⟨csc, hcsc⟩
  rw [hc.cur] at hcsc
  subst hcsc
  step with obj.Sc.consumed.spec' as ⟨i, hi⟩
  step with sched.consumed.spec' as ⟨i1, hi1⟩
  rw [hc.cur] at hi1
  simp only [lift, bind_ok]
  step with sporadic.head.spec as ⟨hd, hhd⟩
  have hhead : (Fl4Spec.refillHd x).rAmount = hd.amount.bv := by
    rw [refillHd_eq hx1.wf hx1.refills, rf0_eq hx1.wf, ← hhd]; rfl
  refine WP.spec_bind (J.chargeBudgetJ hAT hC hni hnsw hmrt hmb hd.amount) ?_
  rintro ⟨s1, a1⟩ ⟨ha1, σ1, h1, Lst1, J1⟩
  simp only at ha1 J1
  step with Sched.obj.Sc.set_consumed.spec' as ⟨s2, hs2⟩
  subst hs2
  obtain ⟨Q1, R1, hc1, hs1⟩ := J1.xtop.fin.1.1.1.lists
  obtain ⟨z, n1, hkz, -⟩ := hs1.scs _ hscC
  obtain ⟨V, J2⟩ := J1.setScConsumedJ hscC hct hkz (core.num.U64.wrapping_add i i1)
  refine ⟨ha1, _, ?_, V, Lst1, J2⟩
  have hsp : Fl4Spec.handleYield (Z := Unit) σ = (Fl4Spec.chargeBudget (Z := Unit) hd.amount.bv false >>= fun _ =>
      Fl4Spec.setScObjRef Fl4Spec.scConsumedUpdate (nodeW st s Z.c layout.node.CUR_SC).bv
        (x.scConsumed + σ.consumedTime)) σ := by
    unfold Fl4Spec.handleYield
    rw [nd_gets_bind, ← hpc, nd_bind_one (getSchedContext_eq hk), nd_gets_bind,
      nd_bind_one (getRefillHead_eq hk hne), hhead]
  rw [hsp, nd_bind_one h1]
  unfold Fl4Spec.setScObjRef
  rw [updateSchedContext_eq hkz]
  have ev : x.scConsumed + σ.consumedTime = (core.num.U64.wrapping_add i i1).bv := by
    rw [core.num.U64.wrapping_add_bv_eq, hi, hi1, hx.consumed, hs.consumed]
  rw [ev]; rfl


set_option maxHeartbeats 16000000 in
/-- **`dispatch_syscall` for Yield at `J`** (KENTRY-PLAN item 9): at a
system call's entry state (`Entered`: the action `resumeCurThread`, so
`CurInv` by `JAtZ.cur`), against `fl4HandleSyscall rep .sysYield`
(`withoutPreemption handle_yield`). -/
theorem dispatch_yieldJ (rep : Bool) (hAT : P0.ArchTotal arI) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) :
    syscall.dispatch_syscall st arI s a fl4_abi.syscall.SysYield ⦃ r =>
      ∃ y ∈ ((Fl4Spec.fl4HandleSyscall (Z := Unit) rep .sysYield).run σ).1,
        y.1 = .ok () ∧ RJ (L := L) arI AR r.1 r.2 y.2 ⦄ := by
  have hC : CurInv σ := J.cur.resolve_left (by rw [hni.2]; intro h; cases h)
  have h := J.handleYieldJ hAT hC hni.1 (by rw [hni.2]; intro h; cases h) hmrt hmb
  unfold syscall.dispatch_syscall
  rw [hct]; simp only [bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.CAP) ?_
  rintro c0 -
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.REPLY) ?_
  rintro c1 -
  rw [if_neg (show fl4_abi.syscall.SysYield ≠ fl4_abi.syscall.SysSend by unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysSend; decide)]
  rw [if_neg (show fl4_abi.syscall.SysYield ≠ fl4_abi.syscall.SysNBSend by unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysNBSend; decide)]
  rw [if_neg (show fl4_abi.syscall.SysYield ≠ fl4_abi.syscall.SysCall by unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysCall; decide)]
  rw [if_neg (show fl4_abi.syscall.SysYield ≠ fl4_abi.syscall.SysRecv by unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysRecv; decide)]
  rw [if_neg (show fl4_abi.syscall.SysYield ≠ fl4_abi.syscall.SysNBRecv by unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysNBRecv; decide)]
  rw [if_neg (show fl4_abi.syscall.SysYield ≠ fl4_abi.syscall.SysWait by unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysWait; decide)]
  rw [if_neg (show fl4_abi.syscall.SysYield ≠ fl4_abi.syscall.SysNBWait by unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysNBWait; decide)]
  rw [if_neg (show fl4_abi.syscall.SysYield ≠ fl4_abi.syscall.SysReplyRecv by unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysReplyRecv; decide)]
  rw [if_neg (show fl4_abi.syscall.SysYield ≠ fl4_abi.syscall.SysNBSendRecv by unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysNBSendRecv; decide)]
  rw [if_neg (show fl4_abi.syscall.SysYield ≠ fl4_abi.syscall.SysNBSendWait by unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysNBSendWait; decide)]
  rw [if_pos trivial]
  refine WP.spec_mono h ?_
  rintro ⟨s', a'⟩ ⟨ha, σ', hsp, V, Lst', J'⟩
  simp only at ha
  have e : Fl4Spec.fl4HandleSyscall (Z := Unit) rep .sysYield = Fl4Spec.withoutPreemption Fl4Spec.handleYield := rfl
  rw [e]
  refine ⟨((.ok ()), σ'), mem_liftE (ε := Unit) (m := Fl4Spec.handleYield (Z := Unit)) (s := σ) (x := ((), σ'))
    (by rw [hsp]; exact Set.mem_singleton _), rfl, ?_⟩
  simp only
  rw [ha]
  exact ⟨J'.xtop.relTop, _, _, _, _, _, _, J'⟩

end

end

end Fl4Proofs.P3
