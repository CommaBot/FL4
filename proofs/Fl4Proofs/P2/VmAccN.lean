/-
# P2 (line p3mc, gen 12): the accepted VM-fault local path on any guard holding its words (`vm_accR`)

`vm_accG` (`P2/AccessVmTail.lean`) runs the accepted VM-fault fast path on any store answering
`IoRS K Locks s` as `st`: the read set is fixed. Here the same chain (`vm_acc_of_tail`, `VmMidF.chk`,
`VmMidF.preRW`, `VmMidF.tailAcc`, `vm_accG`) is restated for **arbitrary** read / write sets `R`, `W`, given
the record **`VmNarA K T Z Locks DQ R W s`** of the words the accepted run touches, at the entry state `s`:
the core's node, the kernel words below 256, the ASID words (`RdTab`), the current thread's home words and
registers, every TCB slot, the handler's words (for a handler `d` with `DQ d`, homed at `s`: home words,
gate words, registers, its SC), the queue links of threads blocked on receive on a held endpoint, the held
endpoints' and reply objects' words, the current SC, the earliest timer's deadline and the release head's SC.
`DQ` is a predicate the handler must satisfy (`hDQ`: every handler the checks find satisfies it); a caller
proving `VmNarA` for a narrow `R` (the words a core's view keeps, P2/VmBView) uses it to know the handler is
really homed.

* **`vm_accR`**: an accepted run is the run on `PathObl.guard st R W`.

No premise beyond `VmFPre` (P2/AccessVmAcc) and the record. No existing statement changed.
-/
import Fl4Proofs.P2.AccessVmTail
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region GateField TimerField GField tcbOwner TcbSlot NullOrFrame
  slotOwner treeCore)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S} {K : KLayout}
variable {Locks : S → U64 → Prop}

/-- **The words the accepted VM-fault run touches, in `R` (read) and `W` (written)** (module docstring). -/
structure VmNarA (st : machine.Store S) [L : LawfulStore st] (K : KLayout) (T : Set U64) (Z : U64 → Nat) (Locks : S → U64 → Prop) (DQ : U64 → Prop)
    (R W : U64 → Prop) (s : S) : Prop where
  nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o) ∧ W (L.nodeAt s (L.cpu s) o)
  ks : ∀ o : U64, o.val < 256 → o.val % 8 = 0 → R (core.num.U64.wrapping_add (L.ksb s) o)
  tab : RdTab (L := L) R s
  home : ∀ off : U64, 192 ≤ off.val → off.val < 4096 → off.val % 8 = 0 → ¬ GateField off.val →
    ¬ TimerField off.val → R (fld (L.curW s) off) ∧ W (fld (L.curW s) off)
  reg : ∀ r : U64, r.val < 384 → R (regA (L.curW s) r) ∧ W (regA (L.curW s) r)
  tslot : ∀ y ∈ T, ∀ i sl : U64, obj.Tcb.slot y i = ok sl → i.val < 6 →
    R sl ∧ R (core.num.U64.wrapping_add sl 8#u64)
  dhome : ∀ d ∈ T, DQ d → L.mem s (affA d) = L.cpu s → ∀ off : U64, 192 ≤ off.val → off.val < 4096 →
    off.val % 8 = 0 → ¬ GateField off.val → ¬ TimerField off.val → ¬ GField off.val → R (fld d off) ∧ W (fld d off)
  dgate : ∀ d ∈ T, DQ d → ∀ off : U64, 192 ≤ off.val → off.val < 4096 → off.val % 8 = 0 → GateField off.val →
    R (fld d off)
  dreg : ∀ d ∈ T, DQ d → L.mem s (affA d) = L.cpu s → ∀ r : U64, r.val < 384 → R (regA d r) ∧ W (regA d r)
  link : ∀ y ∈ T, ∀ p : U64, L.mem s (stA y) = sched.TS_BLOCKED_ON_RECV → L.mem s (blockA y) = p → Locks s p →
    ∀ off : U64, (off.val = 3496 ∨ off.val = 3504) → R (fld y off) ∧ W (fld y off)
  ep : ∀ p b : U64, K.heap p = some .ep → InW p 16 b → Aligned b → Locks s p → R b ∧ W b
  rp : ∀ p b : U64, K.heap p = some .reply → InW p 32 b → Aligned b → Locks s p → R b ∧ W b
  csc : ScAcc R W (L.cscW s) (Z (L.cscW s))
  dsc : ∀ d ∈ T, DQ d → L.mem s (affA d) = L.cpu s → L.mem s (scA d) ≠ 0#u64 →
    ScAcc R W (L.mem s (scA d)) (Z (L.mem s (scA d)))
  td : L.mem s (tmA (L := L) s) ≠ 0#u64 → R (core.num.U64.wrapping_add (L.mem s (tmA (L := L) s)) 3528#u64)
  rs : L.mem s (rhA (L := L) s) ≠ 0#u64 → R (scA (L.mem s (rhA (L := L) s))) ∧
    (∀ b, Aligned b → InSC (L.mem s (scA (L.mem s (rhA (L := L) s))))
      (Z (L.mem s (scA (L.mem s (rhA (L := L) s))))) b → R b) ∧
    RdHead (L := L) R s (L.mem s (scA (L.mem s (rhA (L := L) s))))

variable {DQ R W : U64 → Prop}

set_option maxHeartbeats 4000000 in
/-- **The accepted VM-fault local path, up to its tail, on any store answering `R`/`W` as `st`**
(`vm_acc_of_tail` with `VmNarA` in place of `IoRS`/`IoWS`). -/
theorem vm_acc_of_tailR {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s' : S} {a a' : A}
    {addr code : U64} (P : VmFPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s)
    {gS : machine.Store S} [GRd gS st R] [GWr gS st W] (N : VmNarA st K T Z Locks DQ R W s)
    (hDQ : ∀ s1 a1 ptr badge dest r, sched.update_timestamp st ar s a = ok (s1, a1) →
      FaultChecks st s1 (L.curW s1) ptr badge dest r → DQ dest)
    (htail : ∀ s1 a1 t ins ptr badge dest r s14, sched.update_timestamp st ar s a = ok (s1, a1) →
      sched.cur_thread st s1 = ok t → FaultChecks st s1 t ptr badge dest r →
      vmPre14 st ar s1 a1 t (error.Fault.VmFault addr code ins) fl4_abi.consts.fault.VMFault ptr badge dest r =
        ok s14 →
      faultTail3 st ar s14 a1 dest = ok (true, s', a') →
      faultTail3 gS ar s14 a1 dest = ok (true, s', a'))
    (h : syscall.handle_vm_fault_local st ar s a addr code = ok (true, s', a')) :
    syscall.handle_vm_fault_local gS ar s a addr code = ok (true, s', a') := by
  have B := P.base
  have hN := B.np
  have hT := B.tp
  have hut : ∀ s1 a1, sched.update_timestamp st ar s a = ok (s1, a1) → ∃ n, s1 = utW (L := L) s n := by
    intro s1 a1 eu
    obtain ⟨⟨n, a2⟩, hn, -⟩ := spec_ex_fd (hA.now a)
    rw [update_timestamp_ok ar hN hn] at eu
    exact ⟨n, (Prod.mk.inj (ok_inj_ff eu)).1.symm⟩
  refine syscall.handle_vm_fault_local.guard_acc (gS := gS) ar
    (N.nd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).1
    (N.nd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).2
    (N.nd _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).1
    (N.nd _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).2 ?_ ?_ ?_ h
  · intro s1 a1 eu
    obtain ⟨n, rfl⟩ := hut s1 a1 eu
    rw [ut_nodeAt, ut_nodeAt, ut_nodeAt]
    exact ⟨(N.nd _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])).1,
      (N.nd _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).1,
      (N.nd _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1⟩
  · intro s1 a1 csc eu ecsc
    obtain ⟨n, rfl⟩ := hut s1 a1 eu
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) _)] at ecsc
    have e : csc = L.cscW s := by
      rw [← ut_csc hN n]; exact (ok_inj_ff ecsc).symm
    subst e
    exact rdHead_ut B.bxi n B.cscS (N.csc.head B.cscwf)
  · intro s1 a1 t i2 f eu et ef ptr badge dest r C
    have et' : t = L.curW s1 := by rw [cur_thread_ok] at et; exact (ok_inj_ff et).symm
    have hdq : DQ dest := hDQ s1 a1 ptr badge dest r eu (by rw [← et']; exact C)
    have hlk := P.lk a s1 a1 ptr badge dest r eu (by rw [← et']; exact C)
    have HY := P.hyp a s1 a1 eu
    have htl := htail s1 a1 t (i2 != 0#u64) ptr badge dest r
    have ef' : f = error.Fault.VmFault addr code (i2 != 0#u64) := by
      unfold vspace.vm_fault at ef; exact (ok_inj_ff ef).symm
    subst ef'
    obtain ⟨n, rfl⟩ := hut s1 a1 eu
    have hF := faultEntAt_ofT HY.bxi et HY.nb HY.cap HY.user HY.buf HY.asid
    obtain ⟨hr, rest, E⟩ := hF.2 ptr badge dest r C
    have hrecv := faultRecv_ofT HY.bxi et HY.cap C
    have hpH : H ptr = some .ep := by
      obtain ⟨sl, x, y, g, gr, esl, ecap, -⟩ := C.cap
      have h1 := HY.cap
      rw [← et', esl, WP.spec_ok, ecap, WP.spec_ok] at h1
      exact h1.1 ptr badge x y g gr rfl
    have hhd : dest = L.mem (utW (L := L) s n) (epHeadA ptr) := by
      have h1 := C.head
      rw [eq_of_spec_fd (obj.Ep.head.spec' (L := L) _ ptr)] at h1; exact (ok_inj_ff h1).symm
    have hQ := vm_queue HY.bxi hpH E.hst hhd hrecv
    have hdT : dest ∈ T := E.hq.mem dest (by simp)
    have HF := here_facts (L := L) C.here
    have hrP : r.val % 32 = 0 ∧ r.val + 32 ≤ 2 ^ 64 := by
      obtain ⟨-, -, hX, -, -⟩ := HY.bxi; exact hX.1.rp r hr
    have M : VmMidF st K T H Rp Locks s (utW (L := L) s n) t ptr dest r :=
      { k := utW_ksb s n
        c := utW_cpu s n
        cur := by rw [et', ut_cur hN n]
        tT := E.ht
        dT := hdT
        hT := hT
        hN := hN
        ep := E.hE
        epK := P.hEp ptr hpH
        rK := P.hRp r hr
        rP := hrP
        lp := hlk.1
        lr := hlk.2
        aff := by
          have e := ut_tcb hN hT n hdT (Kx := 3520#u64) (by simp) (by simp)
          calc L.mem s (affA dest) = L.mem (utW (L := L) s n) (affA dest) := e.symm
            _ = L.cpu (utW (L := L) s n) := HF.aff
            _ = L.cpu s := utW_cpu s n
        q := fun y hy => by
          obtain ⟨hyT, hb, hs⟩ := hQ y hy
          refine ⟨hyT, ?_, ?_⟩
          · rw [← hb, blockA_eq]; exact (ut_tcb hN hT n hyT (by simp) (by simp)).symm
          · rw [← hs, stA_eq]; exact (ut_tcb hN hT n hyT (by simp) (by simp)).symm }
    have ndN : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
        R (L.nodeAt (utW (L := L) s n) (L.cpu (utW (L := L) s n)) o) := fun o ho h8 => by
      rw [ut_nodeAt]; exact (N.nd o ho h8).1
    have dh : ∀ off : U64, 192 ≤ off.val → off.val < 4096 → off.val % 8 = 0 → ¬ GateField off.val →
        ¬ TimerField off.val → ¬ GField off.val → R (fld dest off) ∧ W (fld dest off) :=
      N.dhome dest hdT hdq M.aff
    have th : ∀ off : U64, 192 ≤ off.val → off.val < 4096 → off.val % 8 = 0 → ¬ GateField off.val →
        ¬ TimerField off.val → R (fld t off) ∧ W (fld t off) := fun off h1 h2 h3 h4 h5 => by
      rw [M.cur]; exact N.home off h1 h2 h3 h4 h5
    have epw : ∀ b, InW ptr 16 b → Aligned b → R b ∧ W b := fun b hb ha => N.ep ptr b M.epK hb ha M.lp
    have mts : R (core.num.U64.wrapping_add ptr layout.ep.TAIL_STATE) ∧
        W (core.num.U64.wrapping_add ptr layout.ep.TAIL_STATE) := by
      have h := epTSA_val M.ep
      have := M.ep.fits; have := M.ep.align
      exact epw (epTSA ptr) ⟨by omega, by omega⟩ (by unfold Aligned; omega)
    have mhd : R (core.num.U64.wrapping_add ptr layout.ep.HEAD) ∧ W (core.num.U64.wrapping_add ptr layout.ep.HEAD) := by
      have h := epHeadA_val (ep := ptr)
      have := M.ep.fits; have := M.ep.align
      exact epw (epHeadA ptr) ⟨by omega, by omega⟩ (by unfold Aligned; omega)
    have lnk : ∀ {y off : U64}, (y = dest ∨ ((L.epQ (utW (L := L) s n) ptr).end ≠ dest ∧
        y = L.mem (utW (L := L) s n) (nextA .Ep dest))) → (off.val = 3496 ∨ off.val = 3504) →
        R (fld y off) ∧ W (fld y off) := fun {y off} hy hoff => by
      obtain ⟨hyT, hb, hs⟩ := M.q y hy
      exact N.link y hyT ptr hs hb M.lp off hoff
    have mrt : W (core.num.U64.wrapping_add r layout.reply.TCB) := by
      have h := rTcbA_val0 r
      have := M.rP.1; have := M.rP.2
      exact (N.rp r (rTcbA r) M.rK ⟨by omega, by omega⟩ (by unfold Aligned; omega) M.lr).2
    -- `schedulable_here` on the guarded store
    have etm : L.mem (utW (L := L) s n) (tmA (L := L) (utW (L := L) s n)) = L.mem s (tmA (L := L) s) := by
      show L.mem (utW (L := L) s n) (L.nodeAt (utW (L := L) s n) (L.cpu (utW (L := L) s n)) layout.node.TIMER_MIN) = _
      rw [ut_nodeAt]
      exact ut_node hN n (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
        (by simp [layout.node.TIMER_MIN, layout.node.CUR_TIME]) (by simp [layout.node.TIMER_MIN, layout.node.CONSUMED])
    have erh : L.mem (utW (L := L) s n) (rhA (L := L) (utW (L := L) s n)) = L.mem s (rhA (L := L) s) := by
      show L.mem (utW (L := L) s n) (L.nodeAt (utW (L := L) s n) (L.cpu (utW (L := L) s n)) layout.node.RELEASE_HEAD) = _
      rw [ut_nodeAt]
      exact ut_node hN n (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
        (by simp [layout.node.RELEASE_HEAD, layout.node.CUR_TIME])
        (by simp [layout.node.RELEASE_HEAD, layout.node.CONSUMED])
    have hhere := fastpath.schedulable_here.guard (gS := gS)
      (utW (L := L) s n) dest
      (ndN _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
      (ndN _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]))
      (ndN _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]))
      (fun h0 => by rw [etm] at h0 ⊢; exact N.td h0)
      (fun h0 => by
        rw [erh] at h0 ⊢
        obtain ⟨hrT, hscS, -⟩ := bxi_rh B.bxi h0
        have esc : L.mem (utW (L := L) s n) (scA (L.mem s (rhA (L := L) s))) = L.mem s (scA (L.mem s (rhA (L := L) s))) :=
          ut_tcb hN hT n hrT (Kx := 3464#u64) (by simp) (by simp)
        rw [esc]
        obtain ⟨h1, -, h2⟩ := N.rs h0
        exact ⟨h1, rdHead_ut B.bxi n hscS h2⟩)
      (by rw [utW_ksb]; exact N.ks _ (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME]))
      (by rw [utW_ksb]; exact N.ks _ (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN]))
      (N.dgate dest hdT hdq (off := 3520#u64) (by simp) (by simp) (by simp) (by simp [GateField]))
      (N.dgate dest hdT hdq (off := 3432#u64) (by simp) (by simp) (by simp) (by simp [GateField]))
      (N.dgate dest hdT hdq (off := 3464#u64) (by simp) (by simp) (by simp) (by simp [GateField]))
      (dh (3592#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])
        (by simp [GField])).1
    have hq0 := M.q dest (Or.inl rfl)
    have hsd : ∀ v, (v = sched.TS_INACTIVE ∨ v = sched.TS_RUNNING) → SWr gS st dest v := fun v _ =>
      SWr.of_W (gS := gS) (by
        have e : core.num.U64.wrapping_add dest layout.tcb.STATE = core.num.U64.wrapping_add dest 3328#u64 := stA_eq dest
        rw [e]
        exact (dh 3328#u64 (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])
          (by simp [GField])).2)
    have hst : SWr gS st t sched.TS_BLOCKED_ON_REPLY :=
      SWr.of_W (gS := gS) (by
        have e : core.num.U64.wrapping_add t layout.tcb.STATE = core.num.U64.wrapping_add t 3328#u64 := stA_eq t
        rw [e]
        exact (th 3328#u64 (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).2)
    have hchk : FaultChecks gS (utW (L := L) s n) t ptr badge dest r := by
      refine FaultChecks.guard (gS := gS) C (ndN _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))
        (fun sl hsl => ?_) mts.1 mhd.1
        (dh (3360#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])
          (by simp [GField])).1 hhere ?_
        (N.dgate dest hdT hdq (off := 3448#u64) (by simp) (by simp) (by simp) (by simp [GateField])) ?_
      · rw [M.cur] at hsl
        exact N.tslot _ B.cT _ sl hsl (by simp [layout.tcb.SLOT_FAULT_HANDLER])
      · rw [M.k]; exact N.ks _ (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN])
      · refine ⟨ndN l1Off (by rw [l1Off_val]; omega) (by rw [l1Off_val]), fun inv hinv => ?_⟩
        exact ndN _ (by simp only [w64_val]; omega) (by simp only [w64_val]; omega)
    -- the words `vmPre14` touches
    have hdT' := hT dest hdT
    have ht' := hT t M.tT
    have nT : ∀ y ∈ T, ∀ Kx : U64, Kx.val < 4096 → Kx.val ≠ 3376 →
        core.num.U64.wrapping_add y Kx ≠ faultA t :=
      fun y hy Kx hKx hne => field_ne (hT y hy) ht' hKx (K2 := 3376#u64) (by simp) (fun _ => by simpa using hne)
    have hpre : VmPreRW (st := st) R W ar (utW (L := L) s n) a1 t
        (error.Fault.VmFault addr code (i2 != 0#u64)) ptr dest r := by
      refine
      { fw := ⟨(th 3376#u64 (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).2,
          (th 3384#u64 (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).2,
          (th 3392#u64 (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).2,
          (th 3400#u64 (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).2⟩
        ts := mts.1
        wh := mhd.2
        wt := mts.2
        nx := (lnk (y := dest) (off := 3496#u64) (Or.inl rfl) (Or.inl (by simp))).1
        pv := ?_
        dn := (lnk (y := dest) (off := 3496#u64) (Or.inl rfl) (Or.inl (by simp))).2
        dp := (lnk (y := dest) (off := 3504#u64) (Or.inl rfl) (Or.inr (by simp))).2
        ib := N.dgate dest hdT hdq (off := 3512#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        bs := ⟨_, tcb_slot_eq dest _, N.tslot dest hdT _ _ (tcb_slot_eq dest _) (by simp [layout.tcb.SLOT_BUFFER])⟩
        ty := ?_
        mrs :=
          { ft := (th 3376#u64 (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).1
            w0 := (th 3384#u64 (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).1
            w1 := (th 3392#u64 (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).1
            w2 := (th 3400#u64 (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).1
            ip := by rw [M.cur]; exact (N.reg _ (by simp [layout.reg.FAULT_IP])).1
            mr := fun i _ r e => (N.dreg dest hdT hdq M.aff _ (post_of_ok (msg.msg_register.lt i) e)).2 }
        mi := (N.dreg dest hdT hdq M.aff _ (by simp [layout.reg.MSG_INFO])).2
        bd := (N.dreg dest hdT hdq M.aff _ (by simp [layout.reg.BADGE, layout.reg.RDI])).2
        rt := mrt
        ro := (th 3360#u64 (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).2 }
      · -- the successor's `EP_PREV`
        intro s2 tl i6 e2 etl hne e6
        rw [set_fault_vm] at e2
        obtain rfl := ok_inj_ff e2
        rw [obj.Ep.tail.ok] at etl
        obtain rfl := ok_inj_ff etl
        rw [obj.Tcb.ep_next.ok] at e6
        obtain rfl := ok_inj_ff e6
        rw [M.sfQ B] at hne
        have en : L.mem (sfG (L := L) (utW (L := L) s n) t fl4_abi.consts.fault.VMFault addr code
            (if (i2 != 0#u64) then 1#u64 else 0#u64)) (nextA .Ep dest) =
              L.mem (utW (L := L) s n) (nextA .Ep dest) := by
          rw [nextA_eq']; exact M.sft B M.dT (by simp [nextOff]) (by simp [nextOff]) (Or.inr (by simp [nextOff]))
        rw [en]
        exact (lnk (y := L.mem (utW (L := L) s n) (nextA .Ep dest)) (off := 3504#u64) (Or.inr ⟨hne, rfl⟩)
          (Or.inr (by simp))).2
      · -- the fault type read back after the dequeue
        intro s2 tl s3 s4 s5 e2 etl e3 e4 e5
        rw [set_fault_vm] at e2
        obtain rfl := ok_inj_ff e2
        generalize hs2 : sfG (L := L) (utW (L := L) s n) t fl4_abi.consts.fault.VMFault addr code
          (if (i2 != 0#u64) then 1#u64 else 0#u64) = s2 at etl e3 e4 e5
        rw [obj.Ep.tail.ok] at etl
        obtain rfl := ok_inj_ff etl
        have e45 : s5 = epFast (L := L) s2 ptr dest := by
          rw [obj.Tcb.set_ep_next.ok] at e4
          obtain rfl := ok_inj_ff e4
          rw [obj.Tcb.set_ep_prev.ok] at e5
          obtain rfl := ok_inj_ff e5
          by_cases htl : (L.epQ s2 ptr).end = dest
          · rw [if_pos htl, obj.Ep.set_queue.ok] at e3
            obtain rfl := ok_inj_ff e3
            unfold epFast; simp only [htl, ↓reduceIte]
          · rw [if_neg htl, obj.Tcb.ep_next.ok] at e3
            simp only [bind_ok] at e3
            rw [obj.Tcb.set_ep_prev.ok] at e3
            simp only [bind_ok] at e3
            rw [obj.Ep.set_queue.ok] at e3
            obtain rfl := ok_inj_ff e3
            unfold epFast; simp only [htl, ↓reduceIte]
        subst e45
        rw [fault_type_ok]
        congr 1
        have fA : Aligned (faultA t) := field_aligned ht' (K := 3376#u64) (by simp) (by simp)
        have vF : (faultA t).val = t.val + 3376 := field_val ht' (K := 3376#u64) (by simp)
        have hdj := M.ep.disj t M.tT
        have hsucc : (L.epQ s2 ptr).end ≠ dest → L.mem s2 (nextA .Ep dest) ∈ T := fun h => by
          have eQ : L.epQ s2 ptr = L.epQ (utW (L := L) s n) ptr := by rw [← hs2]; exact M.sfQ B
          have en : L.mem s2 (nextA .Ep dest) = L.mem (utW (L := L) s n) (nextA .Ep dest) := by
            rw [← hs2, nextA_eq']; exact M.sft B M.dT (by simp [nextOff]) (by simp [nextOff])
              (Or.inr (by simp [nextOff]))
          rw [eQ] at h; rw [en]
          exact (M.q _ (Or.inr ⟨h, rfl⟩)).1
        rw [epFast_mem fA
          ⟨by unfold Aligned; rw [epHeadA_val]; exact M.ep.align, fun e => by
            have := congrArg UScalar.val e; rw [epHeadA_val, vF] at this; omega⟩
          ⟨by unfold Aligned; rw [epTSA_val M.ep]; have := M.ep.align; omega, fun e => by
            have := congrArg UScalar.val e; rw [epTSA_val M.ep, vF] at this; omega⟩
          ⟨by rw [nextA_eq']; exact field_aligned hdT' (by simp [nextOff]) (by simp [nextOff]),
            by rw [nextA_eq']; exact nT dest M.dT _ (by simp [nextOff]) (by simp [nextOff])⟩
          ⟨by rw [prevA_eq']; exact field_aligned hdT' (by simp [prevOff]) (by simp [prevOff]),
            by rw [prevA_eq']; exact nT dest M.dT _ (by simp [prevOff]) (by simp [prevOff])⟩
          (fun h => ⟨by rw [prevA_eq']; exact field_aligned (hT _ (hsucc h)) (by simp [prevOff]) (by simp [prevOff]),
            by rw [prevA_eq']; exact nT _ (hsucc h) _ (by simp [prevOff]) (by simp [prevOff])⟩)]
        rw [← hs2]
        unfold sfG
        have ne : ∀ Kx : U64, Kx.val < 4096 → Kx.val ≠ 3376 → core.num.U64.wrapping_add t Kx ≠ faultA t :=
          fun Kx hKx hne => nT t M.tT Kx hKx hne
        rw [mem_wr_ne' (field_aligned ht' (by simp) (by simp)) fA (ne _ (by simp) (by simp)),
          mem_wr_ne' (field_aligned ht' (by simp) (by simp)) fA (ne _ (by simp) (by simp)),
          mem_wr_ne' (field_aligned ht' (by simp) (by simp)) fA (ne _ (by simp) (by simp)), L.mem_wr_same fA]
    exact
    { chk := hchk
      pre := vmPre14.guard (gS := gS) ar _ a1 t addr code (i2 != 0#u64) _ ptr badge dest r hpre hsd hst
      tail := fun s14 e14 h3 => htl s14 eu et C e14 h3 }

set_option maxHeartbeats 4000000 in
/-- **`VmTailAcc` from `VmNarA`** (`VmMidF.tailAcc` with the record in place of `VmBase`'s `IoRS` facts). -/
theorem VmMidF.tailAccR {t ptr dest r n : U64} (P : VmBase st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (M : VmMidF st K T H Rp Locks s (utW (L := L) s n) t ptr dest r) (N : VmNarA st K T Z Locks DQ R W s)
    (hdq : DQ dest) (hAs : AsidOff (L := L) Ω Sg (utW (L := L) s n))
    (hsc0 : L.mem (utW (L := L) s n) (scA dest) ≠ 0#u64) :
    VmTailAcc (L := L) Z R W (utW (L := L) s n) dest := by
  have hN := P.np
  have hT := P.tp
  obtain ⟨⟨Q, Rq, hq⟩, -, ⟨hO, -, hX⟩, -, -⟩ := P.bxi
  have hcC : L.cpu s ∈ Cs := hq.cur
  have hX0 : ScExtra0 st T Cs Scs Nt s := hX.toScExtra0
  have esc : L.mem (utW (L := L) s n) (scA dest) = L.mem s (scA dest) :=
    ut_tcb hN hT n M.dT (Kx := 3464#u64) (by simp) (by simp)
  have hne : L.mem s (scA dest) ≠ 0#u64 := by rw [← esc]; exact hsc0
  have hdsc : L.mem s (scA dest) ∈ Scs := (hX0.bound dest M.dT hne).1
  have hacc := N.dsc dest M.dT hdq M.aff hne
  have dh := N.dhome dest M.dT hdq M.aff
  have etm : L.mem (utW (L := L) s n) (tmA (L := L) (utW (L := L) s n)) = L.mem s (tmA (L := L) s) := by
    show L.mem (utW (L := L) s n) (L.nodeAt (utW (L := L) s n) (L.cpu (utW (L := L) s n)) layout.node.TIMER_MIN) = _
    rw [ut_nodeAt]
    exact ut_node hN n (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN, layout.node.CUR_TIME]) (by simp [layout.node.TIMER_MIN, layout.node.CONSUMED])
  have erh : L.mem (utW (L := L) s n) (rhA (L := L) (utW (L := L) s n)) = L.mem s (rhA (L := L) s) := by
    show L.mem (utW (L := L) s n) (L.nodeAt (utW (L := L) s n) (L.cpu (utW (L := L) s n)) layout.node.RELEASE_HEAD) = _
    rw [ut_nodeAt]
    exact ut_node hN n (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD, layout.node.CUR_TIME])
      (by simp [layout.node.RELEASE_HEAD, layout.node.CONSUMED])
  refine
  { nd := fun o ho h8 => by rw [ut_nodeAt]; exact N.nd o ho h8
    dt := by rw [utW_ksb]; exact N.ks _ (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME])
    kr := by unfold krA; rw [utW_ksb]; exact N.ks _ (by simp [layout.ks.KERNEL_ROOT]) (by simp [layout.ks.KERNEL_ROOT])
    tab := ?_
    dvt := N.tslot dest M.dT _ _ (tcb_slot_eq dest layout.tcb.SLOT_VTABLE) (by simp [layout.tcb.SLOT_VTABLE])
    dsc0 := N.dgate dest M.dT hdq (off := 3464#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    diq := (dh (3592#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])
      (by simp [GField])).1
    dyt := (dh (3472#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])
      (by simp [GField])).1
    dst := by
      rw [stA_eq]
      exact (dh (3328#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])
        (by simp [GField])).1
    dfi := (N.dreg dest M.dT hdq M.aff (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])).1
    dni := (N.dreg dest M.dT hdq M.aff (r := layout.reg.NEXT_IP) (by simp [layout.reg.NEXT_IP])).2
    dsw := ⟨(dh (3480#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])
      (by simp [GField])).2,
      (dh (3488#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])
        (by simp [GField])).2⟩
    spo := by
      rw [esc]
      have hw := sc_word_in hO hdsc (o := layout.sc.SPORADIC) (by simp [layout.sc.SPORADIC])
        (by simp [layout.sc.SPORADIC])
      exact hacc.rd _ hw.1 hw.2
    dsc := by rw [esc]; exact hacc
    csc := by rw [ut_csc hN n]; exact N.csc
    tm := fun h0 => by rw [etm] at h0 ⊢; exact N.td h0
    rh := fun h0 => by
      rw [erh] at h0 ⊢
      obtain ⟨hrT, hscS, -⟩ := bxi_rh P.bxi h0
      have e1 : L.mem (utW (L := L) s n) (scA (L.mem s (rhA (L := L) s))) =
          L.mem s (scA (L.mem s (rhA (L := L) s))) :=
        ut_tcb hN hT n hrT (Kx := 3464#u64) (by simp) (by simp)
      rw [e1]
      obtain ⟨h1, h2, h3⟩ := N.rs h0
      exact ⟨h1, h2, rdHead_ut P.bxi n hscS h3⟩ }
  intro hi hhi
  have hA1 := hAs hi hhi
  rw [utW_ksb] at hA1 ⊢
  have e : L.mem (utW (L := L) s n) (atAF (L.ksb s) hi) = L.mem s (atAF (L.ksb s) hi) :=
    ut_out hN hcC n (hq.omega _ hA1.1)
  rw [e]
  exact N.tab hi hhi

set_option maxHeartbeats 4000000 in
/-- **The accepted VM-fault local path on any guard holding its words** (module docstring). -/
theorem vm_accR {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s' : S} {a a' : A}
    {addr code : U64} (P : VmFPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s)
    (N : VmNarA st K T Z Locks DQ R W s)
    (hDQ : ∀ s1 a1 ptr badge dest r, sched.update_timestamp st ar s a = ok (s1, a1) →
      FaultChecks st s1 (L.curW s1) ptr badge dest r → DQ dest)
    (h : syscall.handle_vm_fault_local st ar s a addr code = ok (true, s', a')) :
    syscall.handle_vm_fault_local (PathObl.guard st R W) ar s a addr code = ok (true, s', a') := by
  have B := P.base
  have hN := B.np
  have hT := B.tp
  refine vm_acc_of_tailR (gS := PathObl.guard st R W) hA P N hDQ ?_ h
  intro s1 a1 t ins ptr badge dest r s14 eu et C e14 h3
  have et' : t = L.curW s1 := by rw [cur_thread_ok] at et; exact (ok_inj_ff et).symm
  have hdq : DQ dest := hDQ s1 a1 ptr badge dest r eu (by rw [← et']; exact C)
  have hlk := P.lk a s1 a1 ptr badge dest r eu (by rw [← et']; exact C)
  have HY := P.hyp a s1 a1 eu
  have hy0 := P.hyt a s1 a1 ptr badge dest r eu (by rw [← et']; exact C)
  obtain ⟨⟨n, a2⟩, hn, -⟩ := spec_ex_fd (hA.now a)
  rw [update_timestamp_ok ar hN hn] at eu
  have eS := (Prod.mk.inj (ok_inj_ff eu)).1
  subst eS
  have hF := faultEntAt_ofT HY.bxi et HY.nb HY.cap HY.user HY.buf HY.asid
  obtain ⟨hr, rest, E⟩ := hF.2 ptr badge dest r C
  have hrecv := faultRecv_ofT HY.bxi et HY.cap C
  have hpH : H ptr = some .ep := by
    obtain ⟨sl, x, y, g, gr, esl, ecap, -⟩ := C.cap
    have h1 := HY.cap
    rw [← et', esl, WP.spec_ok, ecap, WP.spec_ok] at h1
    exact h1.1 ptr badge x y g gr rfl
  have hhd : dest = L.mem (utW (L := L) s n) (epHeadA ptr) := by
    have h1 := C.head
    rw [eq_of_spec_fd (obj.Ep.head.spec' (L := L) _ ptr)] at h1; exact (ok_inj_ff h1).symm
  have hQ := vm_queue HY.bxi hpH E.hst hhd hrecv
  have hdT : dest ∈ T := E.hq.mem dest (by simp)
  have HF := here_facts (L := L) C.here
  have hrP : r.val % 32 = 0 ∧ r.val + 32 ≤ 2 ^ 64 := by
    obtain ⟨-, -, hX, -, -⟩ := HY.bxi; exact hX.1.rp r hr
  have M : VmMidF st K T H Rp Locks s (utW (L := L) s n) t ptr dest r :=
    { k := utW_ksb s n
      c := utW_cpu s n
      cur := by rw [et', ut_cur hN n]
      tT := E.ht
      dT := hdT
      hT := hT
      hN := hN
      ep := E.hE
      epK := P.hEp ptr hpH
      rK := P.hRp r hr
      rP := hrP
      lp := hlk.1
      lr := hlk.2
      aff := by
        have e := ut_tcb hN hT n hdT (Kx := 3520#u64) (by simp) (by simp)
        calc L.mem s (affA dest) = L.mem (utW (L := L) s n) (affA dest) := e.symm
          _ = L.cpu (utW (L := L) s n) := HF.aff
          _ = L.cpu s := utW_cpu s n
      q := fun y hy => by
        obtain ⟨hyT, hb, hs⟩ := hQ y hy
        refine ⟨hyT, ?_, ?_⟩
        · rw [← hb, blockA_eq]; exact (ut_tcb hN hT n hyT (by simp) (by simp)).symm
        · rw [← hs, stA_eq]; exact (ut_tcb hN hT n hyT (by simp) (by simp)).symm }
  have hyX : L.mem (utW (L := L) s n) (yieldA dest) = 0#u64 := by
    rw [show yieldA dest = core.num.U64.wrapping_add dest 3472#u64 from rfl,
      ut_tcb hN hT n hdT (Kx := 3472#u64) (by simp) (by simp)]
    exact hy0
  have hSW : SWr (PathObl.guard st R W) st dest sched.TS_RUNNING :=
    SWr.of_W (gS := PathObl.guard st R W) (by
      have e : core.num.U64.wrapping_add dest layout.tcb.STATE = core.num.U64.wrapping_add dest 3328#u64 := stA_eq dest
      rw [e]
      exact (N.dhome dest hdT hdq M.aff 3328#u64 (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField]) (by simp [GField])).2)
  exact faultTail3.guardVm (gS := PathObl.guard st R W) ar hA HY.bxi
    hF C hrecv hyX (M.tailAccR B N hdq HY.asid HF.sc) hSW e14 h3

end

end Fl4Proofs.P2.PathObl
