/-
P3 (DESIGN.md §9), TCB invocations: **WriteRegisters from `JAtZ`** (the
fold's re-scoping of `writeRegsXHyp_of`).

* `write_registers_irelS`: `write_registers_irel` with the scheduler facts at
  the start, carried across the register writes (a `TView` step:
  `SchedValid.tcbView`, `ObjCover.tcbView`, `Inv.tcbView`;
  `removeTcbOK_regs`, FL4 writing only the target's register words), the
  restart's spec facts (`RestartSpecOK`) at the state after the writes, and
  `Inv` after the restart for the reschedule.
* `writeRegsXHypJ`: from `JAtZ` at the decode's state, `JAtZ` after the
  caller's restart (`jat_restart`).
-/
import Fl4Proofs.P3.IpcWriteRegs
import Fl4Proofs.P3.IpcResumeJ
import Fl4Proofs.P3.ScRestartSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

/-- The fields of a TCB the scheduler invariants read, equal. -/
def TcbViewEq (y x : Fl4Spec.Tcb) : Prop :=
  y.tcbState = x.tcbState ∧ y.tcbSchedContext = x.tcbSchedContext ∧
    y.tcbBoundNotification = x.tcbBoundNotification ∧ y.tcbYieldTo = x.tcbYieldTo

theorem sanRegs_viewEq : ∀ (x : Fl4Spec.Tcb) (rs : List Fl4Spec.Register) (vs : List Fl4Spec.Word),
    TcbViewEq (sanRegs x rs vs) x
  | x, r :: rs, v :: vs => sanRegs_viewEq (setReg x r (Fl4Spec.sanitiseRegister false r v)) rs vs
  | x, [], _ => ⟨rfl, rfl, rfl, rfl⟩
  | x, _ :: _, [] => ⟨rfl, rfl, rfl, rfl⟩

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- A register write of `p` keeps every word but `p`'s registers. -/
theorem agree_wr_reg {s : S} {p : U64} (hta : TcbAddr p) (r : Fl4Spec.Register) (v : U64) :
    Agree (L.mem s) (L.mem (L.wr s (regA p (regIdx r)) v)) (fun b => ¬ RcvReg p b) :=
  fun a ha hn => L.mem_wr_ne (a_reg hta r).1 ha (fun e => hn ⟨r, e.symm⟩)

/-- **`RemoveTcbOK` across the target's register writes** (`TView`; FL4
writing only the target's register words). -/
theorem removeTcbOK_regs {s s' : S} {σ σ' : Fl4Spec.State Unit} (hX : IRel st th cr N T C E R B c s σ)
    {p : U64} (hp : p ∈ T) (h : RemoveTcbOK st N T C E R c s σ) (hV : TView σ σ')
    (hq : σ'.readyQueues = σ.readyQueues) (hr : σ'.releaseQueue = σ.releaseQueue) (ht : σ'.curTime = σ.curTime)
    (hag : Agree (L.mem s) (L.mem s') (fun b => ¬ RcvReg p b)) (hks : L.ksb s' = L.ksb s) :
    RemoveTcbOK st N T C E R c s' σ' := by
  have hS := hX.2.2.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hta := hc.tcbs p hp
  obtain ⟨-, -, -, hRP, -⟩ := id h
  have hreg : ∀ (b : U64), RcvReg p b → p.val ≤ b.val ∧ b.val < p.val + 4096 := by
    rintro b ⟨r, e⟩
    rw [e, regA_val hta (regIdx_lt r)]; have := regIdx_lt r; omega
  refine removeTcbOK_tview h hV hq hr ht hks (fun sc hsc => ?_) (fun d hd => ?_)
  · obtain ⟨y, n, hky, hy⟩ := hs.scs sc hsc
    obtain ⟨hal, hin⟩ := hy.hdr (K := 32#u64) (by decide) (by decide)
    rw [scReplyA_eq]
    refine hag _ hal fun hR => ?_
    have := (hS.scOutIn hsc hin).2.2.1 p hp
    have := hreg _ hR; omega
  · have hra := hRP.align d hd
    have htr := hRP.tcb d hd p hp
    refine ⟨hag _ (hRP.aligned hd (Or.inl (rPrevA_val hra))) fun hR => ?_,
      hag _ (hRP.aligned hd (Or.inr (rNextA_val hra))) fun hR => ?_⟩
    · have := hreg _ hR; rw [rPrevA_val hra] at this; omega
    · have := hreg _ hR; rw [rNextA_val hra] at this; omega

/-- `Inv` across a TCB update keeping its view. -/
theorem inv_updView' {σ : Fl4Spec.State Unit} (h : Inv σ) {p : Fl4Spec.ObjRef} {x y : Fl4Spec.Tcb}
    (hk : σ.kheap p = some (.tcb x)) (hv : TcbViewEq y x) : Inv (Notif.updK σ p (.tcb y)) := by
  have hTV := TView.upd hk hv.1 hv.2.1 hv.2.2.1 hv.2.2.2
  refine h.tcbView (fun q => ?_) rfl rfl rfl
  rcases hTV q with e | ⟨a1, b1, h1, h2, e1, e2, -⟩
  · exact Or.inl e
  · exact Or.inr ⟨a1, b1, h1, h2, e1, e2⟩

set_option maxHeartbeats 16000000 in
/-- **`write_registers` on `IRel`, re-scoped** (module docstring). -/
theorem write_registers_irelS (hP0 : IPlaced N T E R B)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ) {p : U64} (hp : p ∈ T)
    (resume : Bool) (n buf : U64) {V : List Fl4Spec.Word} (hVn : V.length = n.val)
    {ct : U64} (hct : σ.curThread = ct.bv) {x : Fl4Spec.Tcb} (hk : σ.kheap p.bv = some (.tcb x))
    (hRd : ∀ n' : U64, n'.val = min n.val 20 →
      WrRead (L := L) T E R B (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))) s σ p x ct buf n' V)
    (hSV : SchedValid σ) (hOC : ObjCover N T E R C σ) (hInv : Inv σ) (hOK : RemoveTcbOK st N T C E R c s σ)
    (hRS : ∀ x4 : Fl4Spec.Tcb, TcbViewEq x4 x → RestartSpecOK p.bv (updK σ p.bv (.tcb x4)))
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) :
    tcb.write_registers st ar s a p resume n buf ⦃ r => r.2 = a ∧ ∃ σ',
      specWr p.bv resume V σ = ({((), σ')}, False) ∧ IRel st th cr N T C E R B c r.1 σ' ⦄ := by
  have hS := hX.2.2.1
  unfold tcb.write_registers
  refine WP.spec_bind (cur_thread_bv hS) ?_
  rintro ct' hct'
  obtain rfl : ct = ct' := (eq_of_bv (hct'.trans hct)).symm
  have hf : tcb.N_FRAME.val = 18 := by unfold tcb.N_FRAME; rfl
  have hg : tcb.N_GP.val = 2 := by unfold tcb.N_GP; rfl
  obtain ⟨i, hie, hiv⟩ := spec_exists (U64.add_spec (x := tcb.N_FRAME) (y := tcb.N_GP) (by rw [hf, hg]; scalar_tac))
  rw [hie, bind_ok]
  have hi20 : i.val = 20 := by have := hiv; simp only [hf, hg] at this ⊢; omega
  obtain ⟨n', hn'e, hn'v⟩ : ∃ n' : U64, (if n > i then ok i else ok n : Result U64) = ok n' ∧
      n'.val = min n.val 20 := by
    by_cases h : n > i
    · exact ⟨i, if_pos h, by have := (P1.gt_iff_val).1 h; omega⟩
    · exact ⟨n, if_neg h, by have := (P1.gt_iff_val).not.1 h; omega⟩
  rw [hn'e, bind_ok]
  have hH := ipcCore_top (st := st) (th := th) (cr := cr) (N := N) (C := C) (c := c) hP0.e
  have hEH := hH.epHyps hP0
  have hSR := IpcRel.toSRN hX.1 hX.2
  have hI0 := rgInv_init (L := L) (T := T) (E := E) (R := R) (B := B) hX.1.toE hSR.1 hk
  have hn20 : n'.val ≤ 20 := by omega
  have hVl : n'.val ≤ V.length := by omega
  refine WP.spec_bind (wr_loop0 hEH hP0.e hp hn20 hVl (hRd n' hn'v) s hI0) ?_
  intro s1 hI1
  refine WP.spec_bind (wr_loop1 hEH hP0.e hp hn20 hVl (hRd n' hn'v) s1 hI1) ?_
  intro s2 hI2
  unfold RgInv at hI2
  rw [sanRegs_take x wrRegs V n'.val (by rw [wrRegs_length]; omega)] at hI2
  obtain ⟨hE2, hS2, hA2, hks2⟩ := hI2
  set x2 := sanRegs x wrRegs V with hx2
  have hk2 : (updK σ p.bv (.tcb x2)).kheap p.bv = some (.tcb x2) := by simp [updK]
  have hN2 := ntfn_lift_rcv hP0.toC hX.1.toN hE2 hp (hA2.mono fun _ h => h.1)
    (fun q hq => by simp [updK, hq]) hk hk2 (sanRegs_fields x _ _).1
  have hX2 : IRel st th cr N T C E R B c s2 (updK σ p.bv (.tcb x2)) := IpcRel.ofSRN hE2 ⟨hS2, hN2⟩
  have hv2 : TcbViewEq x2 x := sanRegs_viewEq x _ _
  -- the restart PC
  step with Endp.obj.Tcb.reg.spec as ⟨pc, hpc⟩
  have hF : layout.reg.FAULT_IP = regIdx .faultIP := by unfold layout.reg.FAULT_IP; rfl
  have hNx : layout.reg.NEXT_IP = regIdx .nextIP := by unfold layout.reg.NEXT_IP; rfl
  obtain ⟨x2', hk2', hTR2⟩ := hX2.1.tcb p hp
  rw [hk2] at hk2'; cases hk2'
  have hpcv : pc.bv = x2.tcbArch.tcbContext.userRegs .faultIP := by rw [hpc, hF]; exact hTR2.regs .faultIP
  refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s2 p _ pc) ?_
  rintro s3 rfl
  rw [hNx]
  have hX3 := reg_wr_irel hP0 hX2 hp hk2 .nextIP (by decide) pc
  rw [hpcv] at hX3
  set σ3 := Notif.updK (updK σ p.bv (.tcb x2)) p.bv (.tcb (Notif.setReg x2 .nextIP (x2.tcbArch.tcbContext.userRegs .faultIP)))
    with hσ3
  have hσ3' : σ3 = updK σ p.bv (.tcb (setReg x2 .nextIP (x2.tcbArch.tcbContext.userRegs .faultIP))) := by
    rw [hσ3]; simp only [Notif.updK, updK, Function.update_idem]
  have hk3 : σ3.kheap p.bv = some (.tcb (Notif.setReg x2 .nextIP (x2.tcbArch.tcbContext.userRegs .faultIP))) := by
    rw [hσ3]; simp [Notif.updK]
  have hct3 : σ3.curThread = ct.bv := by rw [hσ3]; exact hct
  -- `post_modify_registers`
  have hpm : tcb.post_modify_registers st (L.wr s2 (regA p (regIdx .nextIP)) pc) p ⦃ s4 => ∃ σ4,
      Fl4Spec.archPostModifyRegisters (Z := Unit) ct.bv p.bv σ3 = ({((), σ4)}, False) ∧
      IRel st th cr N T C E R B c s4 σ4 ∧ σ4.curThread = ct.bv ∧
      (∃ x4, σ4 = updK σ p.bv (.tcb x4) ∧ TcbViewEq x4 x) ∧ Agree (L.mem s) (L.mem s4) (fun b => ¬ RcvReg p b) ∧
      L.ksb s4 = L.ksb s ⦄ := by
    unfold tcb.post_modify_registers
    refine WP.spec_bind (cur_thread_bv hX3.2.2.1) ?_
    rintro ct3 hc3
    obtain rfl : ct = ct3 := (eq_of_bv (hc3.trans hct3)).symm
    rw [tcb_ne_eq, bind_ok]
    by_cases hpc' : p = ct
    · subst hpc'
      simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      refine ⟨σ3, ?_, hX3, hct3, ⟨_, hσ3', hv2⟩,
        Agree.trans hA2 (agree_wr_reg (hP0.e.tcb p hp) .nextIP pc), by rw [L.ksb_wr]; exact hks2⟩
      unfold Fl4Spec.archPostModifyRegisters Fl4Spec.NonDet.when
      rw [if_neg (by simp)]; rfl
    · simp only [ne_eq, hpc', not_false_eq_true, decide_true, ↓reduceIte]
      have hE : layout.reg.ERROR = regIdx .errorRegister := by unfold layout.reg.ERROR; rfl
      refine WP.spec_mono (Endp.obj.Tcb.set_reg.spec _ p _ 0#u64) ?_
      rintro s4 rfl
      rw [hE]
      refine ⟨_, ?_, reg_wr_irel hP0 hX3 hp hk3 .errorRegister (by decide) 0#u64, by simp [Notif.updK, hct3],
        ⟨setReg (setReg x2 .nextIP (x2.tcbArch.tcbContext.userRegs .faultIP)) .errorRegister (0#u64).bv,
          by rw [hσ3']; simp only [Notif.updK, updK, Function.update_idem], hv2⟩,
        Agree.trans (Agree.trans hA2 (agree_wr_reg (hP0.e.tcb p hp) .nextIP pc))
          (agree_wr_reg (hP0.e.tcb p hp) .errorRegister _), by simp only [L.ksb_wr]; exact hks2⟩
      unfold Fl4Spec.archPostModifyRegisters Fl4Spec.NonDet.when
      rw [if_pos (fun e => hpc' (eq_of_bv e)), asUser_setRegister_eq _ _ hk3]
      rfl
  refine WP.spec_bind hpm ?_
  rintro s4 ⟨σ4, hpm4, hX4, hct4, ⟨x4, hσ4, hv4⟩, hag4, hks4⟩
  have hTV4 : TView σ σ4 := by rw [hσ4]; exact TView.upd hk hv4.1 hv4.2.1 hv4.2.2.1 hv4.2.2.2
  have hOK4 : RemoveTcbOK st N T C E R c s4 σ4 :=
    removeTcbOK_regs hX hp hOK hTV4 (by subst hσ4; rfl) (by subst hσ4; rfl) (by subst hσ4; rfl) hag4 hks4
  have hInv4 : Inv σ4 := hInv.tcbView (fun q => by
    rcases hTV4 q with e | ⟨a1, b1, h1, h2, e1, e2, -⟩
    · exact Or.inl e
    · exact Or.inr ⟨a1, b1, h1, h2, e1, e2⟩) (by subst hσ4; rfl) (by subst hσ4; rfl) (by subst hσ4; rfl)
  -- the restart
  have hrs : (if resume then sched.restart st ar s4 a p else ok (s4, a)) ⦃ r => r.2 = a ∧ ∃ σ5,
      Fl4Spec.NonDet.when resume (Fl4Spec.restart (Z := Unit) p.bv) σ4 = ({((), σ5)}, False) ∧
      IRel st th cr N T C E R B c r.1 σ5 ∧ σ5.curThread = ct.bv ∧ Inv σ5 ⦄ := by
    cases resume
    · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      exact ⟨trivial, σ4, rfl, hX4, hct4, hInv4⟩
    · simp only [↓reduceIte]
      refine WP.spec_mono (restart_tcb_irelS hP0 (removeTcbHypP_ok hP0) s4 a σ4 hX4 hp (hSV.tcbView hTV4 (by subst hσ4; rfl))
        (hOC.tcbView hTV4) hInv4 (fun x' hk' => removeTcbOK_fault hP0 hX4 hp hk' hOK4) (by rw [hσ4]; exact hRS x4 hv4)
        hmb) ?_
      rintro r ⟨h1, σ5, h2, h3, h4, h5⟩
      exact ⟨h1, σ5, by simpa [Fl4Spec.NonDet.when] using h2, h3, h4.trans hct4, h5⟩
  refine WP.spec_bind hrs ?_
  rintro ⟨s5, a1⟩ ⟨rfl, σ5, hrs5, hX5, hct5, hInv5⟩
  refine WP.spec_bind (cur_thread_bv hX5.2.2.1) ?_
  rintro ct5 hc5
  obtain rfl : ct = ct5 := (eq_of_bv (hc5.trans hct5)).symm
  unfold obj.Tcb.Insts.CoreCmpPartialEqTcb.eq
  simp only [bind_ok]
  have hfin : ∀ σ6, Fl4Spec.NonDet.when (p.bv = ct.bv) (Fl4Spec.rescheduleRequired (Z := Unit)) σ5 =
      ({((), σ6)}, False) → specWr p.bv resume V σ = ({((), σ6)}, False) := by
    intro σ6 h6
    unfold specWr
    rw [nd_gets_bind, hct, nd_bind_one (show Fl4Spec.archGetSanitiseRegisterInfo (Z := Unit) p.bv σ =
      ({(false, σ)}, False) from rfl), nd_bind_one (wr_regs_eq hk V), ← hσ3', nd_bind_one hpm4, nd_bind_one hrs5, h6]
  by_cases hpc' : p = ct
  · subst hpc'
    simp only [decide_true, ↓reduceIte]
    refine WP.spec_bind (resched_irel hP0 s5 σ5 hX5 hInv5.actReady) ?_
    rintro s6 ⟨σ6, h6, -, hX6⟩
    rw [WP.spec_ok]
    exact ⟨rfl, σ6, hfin σ6 (by simpa [Fl4Spec.NonDet.when] using h6), hX6⟩
  · simp only [hpc', decide_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨trivial, σ5, hfin σ5 (by unfold Fl4Spec.NonDet.when; rw [if_neg (fun e => hpc' (eq_of_bv e))]; rfl), hX5⟩

end

end

end Fl4Proofs.P3.Ipc

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

set_option maxHeartbeats 8000000 in
/-- **`WriteRegsXHyp` from `JAtZ`** (`writeRegsXHyp_of` re-scoped): `JAtZ`
after the caller's restart (`jat_restart`), `IRel` at its sets, then
`write_registers_irelS` with its scheduler facts and `RemoveTcbOK`. Named:
the target and the caller among the TCBs, the caller's IPC buffer mapped
(`BufMap`), the syscall arguments after the restart (the decode's), the
platform's `MIN_BUDGET` [P]. The restart's spec facts after the register
writes by `restartSpecOK_of` (ScRestartSpec), from `Inv` and `SchedValid`
there. -/
theorem writeRegsXHypJ {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {ar : A} {σ : Fl4Spec.State Unit} {ct p buf : U64}
    {args : List U64} {blk call don : Bool}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hJS : JStepHyps (L := L) arI AR Z.th)
    (hcur : σ.curThread = ct.bv) (hpT : p ∈ Z.T) (hctT : ct ∈ Z.T)
    (hbuf : buf ≠ 0#u64 → ∃ sp, BufMap Z.B buf sp)
    (hargs : ∀ s1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s1 ct buf i = ok x)
    (hmb : ∀ a, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) :
    WriteRegsXHyp (L := L) arI AR s σ ct p buf args blk call don := by
  intro s1 σ1 flags n a hs1 hst hn ⟨Z', hX'⟩
  have hAR : AR a σ1.archState.x64CurrentCr3 := hX'.fin.1.1.2.2.2.2.2.2
  obtain ⟨Ac', Lst', D', J'⟩ := jat_restart J hJS hcur hs1 hst
  have hP0 := J.ip
  have hI := J'.xtop.irelK J'.ks J'.buf
  obtain ⟨x, hk, -⟩ := hI.1.tcb p hpT
  set V := ((args.drop 2).map UScalar.bv).take n.val with hV
  have hVn : V.length = n.val := by simp [hV]; omega
  have hK := TscK.sk_setThreadState' ct.bv .restart σ ((), σ1) (by rw [hst]; exact Set.mem_singleton _)
  have hcur1 : σ1.curThread = ct.bv := hK.2.2.trans hcur
  obtain ⟨sp, hbm⟩ : ∃ sp, buf ≠ 0#u64 → BufMap Z.B buf sp := by
    by_cases hb : buf = 0#u64
    · exact ⟨0, fun h => absurd hb h⟩
    · obtain ⟨sp, h⟩ := hbuf hb; exact ⟨sp, fun _ => h⟩
  have hRd : ∀ n' : U64, n'.val = min n.val 20 → WrRead (L := L) Z.T Z.E Z.R Z.B
      (SRS st Z.T (SRT st Z.th σ1.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
        (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) s1 σ1 p x ct buf n' V := by
    intro n' hn'
    refine wrRead_of hP0.e hI.1.toE hpT hk hctT hbm (by omega) fun j i2 hi2 hj => ?_
    have hjl : j + 2 < args.length := by omega
    refine ⟨args[j + 2], hargs s1 hs1 i2 _ (by rw [hi2]; exact List.getElem?_eq_getElem hjl), ?_⟩
    have hjV : j < V.length := by omega
    rw [getElem!_pos V j hjV]
    simp only [hV, List.getElem_take, List.getElem_map, List.getElem_drop]
    congr 2; omega
  refine WP.spec_mono (write_registers_irelS (ar := arI) hP0 s1 a σ1 hI hpT _ n buf hVn hcur1 hk hRd J'.sv J'.obj
    J'.inv J'.removeTcbOK (fun x4 hv => Sched.restartSpecOK_of (inv_updView' J'.inv hk hv)
      (fun q y n hq => (J'.sv.tcbView (TView.upd hk hv.1 hv.2.1 hv.2.2.1 hv.2.2.2) rfl).scSpor q y n hq)) (hmb a)) ?_
  rintro r ⟨hr2, σ', hsp, hI'⟩
  obtain ⟨⟨Z'', -, -, -, -, -, -, -, -, hZ''⟩, -⟩ :=
    IRel.xtop (L := L) (AR := AR) (a := r.2) hI' (by rw [hr2]; exact hAR)
  refine ⟨(.ok [], σ'), ?_, rfl, (SRT.relTop hI').1, Z'', hZ''⟩
  show _ ∈ ((Fl4Spec.invokeTcb (Z := Unit) _).run σ1).1
  rw [invokeTcb_wr, ← and1_ne0]
  exact mem_liftE (x := ([], σ')) (mem_bind_nd (by rw [hsp]; exact Set.mem_singleton _) (Set.mem_singleton _))


set_option maxHeartbeats 4000000 in
/-- **Resume from `JAtZ`, discharged** (`resumeXLeafJ` with its
`RestartSpecOK` by `restartSpecOK_of` from `JAtZ`'s `Inv` and `SchedValid`
after the caller's restart). Named: the target among the TCBs, the
platform's `MIN_BUDGET` [P]. -/
theorem resumeXLeafJD {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {ar : A} {σ σ1 : Fl4Spec.State Unit} {p : U64}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hJS : JStepHyps (L := L) arI AR Z.th)
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False)) (hpT : p ∈ Z.T)
    (hmb : sporadic.min_budget arI ar ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) :
    ResumeXLeaf (L := L) arI AR s ar σ σ1 p := by
  refine xleaf_restartJ J hJS hst fun s1 Ac' Lst' D' J' _ hI1 => ?_
  have hP0 := J.ip
  have hAR : AR ar σ.archState.x64CurrentCr3 := J.xtop.fin.1.1.2.2.2.2.2.2
  refine WP.spec_bind (restart_tcb_irelS (ar := arI) hP0 (removeTcbHypP_ok hP0) s1 ar σ1 hI1 hpT J'.sv J'.obj
    J'.inv (fun x hk => removeTcbOK_fault hP0 hI1 hpT hk J'.removeTcbOK)
    (Sched.restartSpecOK_of J'.inv J'.sv.scSpor) hmb) ?_
  rintro ⟨s2, a2⟩ ⟨rfl, σ2, hm, hI2, -, -⟩
  exact (WP.spec_ok _).2 ⟨rfl, hAR, ((), σ2), by rw [hm]; exact Set.mem_singleton _, hI2⟩
end

end

end Fl4Proofs.P3
