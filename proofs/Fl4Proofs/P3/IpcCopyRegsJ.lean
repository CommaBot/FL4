/-
P3 (DESIGN.md §9), TCB invocations: **CopyRegisters from `JAtZ`** (the
fold's re-scoping of `copyRegsXHyp_of`).

* `crb_out`: the spec's register copy into `dest` is one TCB update keeping
  what the scheduler invariants read (`TcbViewEq`).
-/
import Fl4Proofs.P3.IpcCopyRegs
import Fl4Proofs.P3.IpcWriteRegsJ
import Fl4Proofs.P3.TcbSpecInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section Spec
open Fl4Spec

/-- **The spec's register copy** (module docstring). -/
theorem crb_out {src dest : ObjRef} : ∀ (rs : List Register) (σ : State Unit) (x : Tcb),
    σ.kheap dest = some (.tcb x) → (∃ xs, σ.kheap src = some (.tcb xs)) →
    ∃ x', NonDet.mapMx (crb src dest) rs σ = ({((), updK σ dest (.tcb x'))}, False) ∧ TcbViewEq x' x
  | [], σ, x, hk, _ => ⟨x, by rw [updK_self hk]; rfl, rfl, rfl, rfl, rfl, rfl⟩
  | r :: rs, σ, x, hk, ⟨xs, hks⟩ => by
    set σa := updK σ dest (.tcb (setReg x r (sanitiseRegister false r (xs.tcbArch.tcbContext.userRegs r)))) with hσa
    have h1 : crb src dest r σ = ({((), σa)}, False) := by
      unfold crb
      rw [nd_bind_one (asUser_getRegister_eq hks _), asUser_setRegister_eq _ _ hk]
    have hka : σa.kheap dest = some (.tcb (setReg x r (sanitiseRegister false r (xs.tcbArch.tcbContext.userRegs r)))) := by
      simp [hσa, updK]
    have hksa : ∃ xs', σa.kheap src = some (.tcb xs') := by
      by_cases e : src = dest
      · subst e; exact ⟨_, hka⟩
      · exact ⟨xs, by simp [hσa, updK, Function.update_of_ne e, hks]⟩
    obtain ⟨x', h2, hv⟩ := crb_out rs σa _ hka hksa
    refine ⟨x', ?_, hv⟩
    show (crb src dest r >>= fun _ => NonDet.mapMx (crb src dest) rs) σ = _
    rw [nd_bind_one h1, h2, hσa]
    simp only [updK, Function.update_idem]

end Spec


section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- `Inv` across a TCB update keeping its view. -/
theorem inv_updView {σ : Fl4Spec.State Unit} (h : Inv σ) {p : Fl4Spec.ObjRef} {x y : Fl4Spec.Tcb}
    (hk : σ.kheap p = some (.tcb x)) (hv : TcbViewEq y x) : Inv (Notif.updK σ p (.tcb y)) := by
  have hTV := TView.upd hk hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1 (Or.inl hv.2.2.2.2)
  refine h.tcbView (fun q => ?_) rfl rfl rfl
  rcases hTV q with e | ⟨a1, b1, h1, h2, e1, e2, -, -, e5⟩
  · exact Or.inl e
  · exact Or.inr ⟨a1, b1, h1, h2, e1, e2, e5⟩

/-- `Inv` across the spec's register copy (`crb_out`). -/
theorem inv_crb {s : S} {σ σ' : Fl4Spec.State Unit} (hX : IRel st th cr N T C E R B c s σ) {src dest : U64}
    (hs : src ∈ T) (hd : dest ∈ T) (hI : Inv σ) {rs : List Fl4Spec.Register}
    (hm : Fl4Spec.NonDet.mapMx (crb src.bv dest.bv) rs σ = ({((), σ')}, False)) : Inv σ' := by
  obtain ⟨x, hk, -⟩ := hX.1.tcb dest hd
  obtain ⟨xs, hks, -⟩ := hX.1.tcb src hs
  obtain ⟨x', h1, hv⟩ := crb_out rs σ x hk ⟨xs, hks⟩
  rw [the_result h1 hm]
  exact inv_updView hI hk hv

set_option maxHeartbeats 8000000 in
/-- **The tail of `copy_registers`** (`cr_tail` with `ActReady` at the
start, carried across `post_modify_registers`). -/
theorem cr_tailA (hP0 : IPlaced N T E R B)
    {s : S} {σ : Fl4Spec.State Unit} (hA : ActReady σ) (hX : IRel st th cr N T C E R B c s σ) {dest : U64} (hd : dest ∈ T) (a : A) :
    (do
      let s6 ← tcb.post_modify_registers st s dest
      let t ← sched.cur_thread st s6
      let b ← obj.Tcb.Insts.CoreCmpPartialEqTcb.eq dest t
      if b then do
        let s7 ← sched.reschedule_required st s6
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s7, a)
      else ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s6, a)) ⦃ r =>
      r.1 = .Ok () ∧ r.2.2 = a ∧ ∃ σ', (do
        let cur ← Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread
        Fl4Spec.archPostModifyRegisters cur dest.bv
        Fl4Spec.NonDet.when (dest.bv = cur) Fl4Spec.rescheduleRequired) σ = ({((), σ')}, False) ∧
        IRel st th cr N T C E R B c r.2.1 σ' ⦄ := by
  obtain ⟨x, hk, -⟩ := hX.1.tcb dest hd
  have hpm : tcb.post_modify_registers st s dest ⦃ s4 => ∃ ct : U64, σ.curThread = ct.bv ∧ ∃ σ4,
      Fl4Spec.archPostModifyRegisters (Z := Unit) ct.bv dest.bv σ = ({((), σ4)}, False) ∧
      IRel st th cr N T C E R B c s4 σ4 ∧ σ4.curThread = ct.bv ∧ ActReady σ4 ⦄ := by
    unfold tcb.post_modify_registers
    refine WP.spec_bind (cur_thread_bv hX.2.2.1) ?_
    rintro ct hct
    rw [tcb_ne_eq, bind_ok]
    by_cases hpc' : dest = ct
    · subst hpc'
      simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      refine ⟨dest, hct.symm, σ, ?_, hX, hct.symm, hA⟩
      unfold Fl4Spec.archPostModifyRegisters Fl4Spec.NonDet.when
      rw [if_neg (by simp)]; rfl
    · simp only [ne_eq, hpc', not_false_eq_true, decide_true, ↓reduceIte]
      have hE : layout.reg.ERROR = regIdx .errorRegister := by unfold layout.reg.ERROR; rfl
      refine WP.spec_mono (Endp.obj.Tcb.set_reg.spec _ dest _ 0#u64) ?_
      rintro s4 rfl
      rw [hE]
      refine ⟨ct, hct.symm, _, ?_, reg_any_wr_irel hP0 hX hd hk .errorRegister 0#u64, by simp [Notif.updK, hct],
        actReady_upd (y := Notif.setReg x .errorRegister (0#u64).bv) hA hk rfl rfl rfl rfl rfl rfl⟩
      unfold Fl4Spec.archPostModifyRegisters Fl4Spec.NonDet.when
      rw [if_pos (fun e => hpc' (eq_of_bv e)), asUser_setRegister_eq _ _ hk]
      rfl
  refine WP.spec_bind hpm ?_
  rintro s4 ⟨ct, hct, σ4, hpm4, hX4, hct4, hA4⟩
  refine WP.spec_bind (cur_thread_bv hX4.2.2.1) ?_
  rintro ct5 hc5
  obtain rfl : ct = ct5 := (eq_of_bv (hc5.trans hct4)).symm
  unfold obj.Tcb.Insts.CoreCmpPartialEqTcb.eq
  simp only [bind_ok]
  have hfin : ∀ σ6, Fl4Spec.NonDet.when (dest.bv = ct.bv) (Fl4Spec.rescheduleRequired (Z := Unit)) σ4 =
      ({((), σ6)}, False) → (do
        let cur ← Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread
        Fl4Spec.archPostModifyRegisters cur dest.bv
        Fl4Spec.NonDet.when (dest.bv = cur) Fl4Spec.rescheduleRequired) σ = ({((), σ6)}, False) := by
    intro σ6 h6
    rw [nd_gets_bind, hct, nd_bind_one hpm4, h6]
  by_cases hpc' : dest = ct
  · subst hpc'
    simp only [decide_true, ↓reduceIte]
    refine WP.spec_bind (resched_irel hP0 s4 σ4 hX4 hA4) ?_
    rintro s6 ⟨σ6, h6, -, hX6⟩
    rw [WP.spec_ok]
    exact ⟨rfl, rfl, σ6, hfin σ6 (by simpa [Fl4Spec.NonDet.when] using h6), hX6⟩
  · simp only [hpc', decide_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨trivial, trivial, σ4, hfin σ4 (by unfold Fl4Spec.NonDet.when; rw [if_neg (fun e => hpc' (eq_of_bv e))]; rfl), hX4⟩

set_option maxHeartbeats 16000000 in
/-- **`copy_registers` on `IRel`, re-scoped**: the scheduler facts at the
start; the source's suspend keeping them (`hSus`, the Suspend `JAtZ` step's
building block); `RestartSpecOK` after it by `restartSpecOK_of`; `Inv`
carried across the restart and the register copies, for the tail's
reschedule. -/
theorem copy_registers_irelS (hP0 : IPlaced N T E R B)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ) {src dest : U64}
    (hs : src ∈ T) (hd : dest ∈ T) (flags : U64)
    (hSV : SchedValid σ) (hOC : ObjCover N T E R C σ) (hInv : Inv σ) (hOK : RemoveTcbOK st N T C E R c s σ)
    (hSus : sched.suspend st ar s a src ⦃ r => r.2 = a ∧ ∃ σ', Fl4Spec.suspend (Z := Unit) src.bv σ = ({((), σ')}, False) ∧
      IRel st th cr N T C E R B c r.1 σ' ∧ SchedValid σ' ∧ ObjCover N T E R C σ' ∧ Inv σ' ∧
      RemoveTcbOK st N T C E R c r.1 σ' ⦄)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) :
    tcb.copy_registers st ar s a dest src flags ⦃ r => r.1 = .Ok () ∧ r.2.2 = a ∧ ∃ σ',
      specCr dest.bv src.bv (Fl4Spec.testBit flags.bv 0) (Fl4Spec.testBit flags.bv 1) (Fl4Spec.testBit flags.bv 2)
        (Fl4Spec.testBit flags.bv 3) σ = ({((), σ')}, False) ∧ IRel st th cr N T C E R B c r.2.1 σ' ⦄ := by
  unfold tcb.copy_registers
  simp only [lift, bind_ok]
  rw [andk_ne0 flags 1#u64 0 (by decide) (by decide), andk_ne0 flags 2#u64 1 (by decide) (by decide),
    andk_ne0 flags 4#u64 2 (by decide) (by decide), andk_ne0 flags 8#u64 3 (by decide) (by decide)]
  generalize Fl4Spec.testBit flags.bv 0 = b0
  generalize Fl4Spec.testBit flags.bv 1 = b1
  generalize Fl4Spec.testBit flags.bv 2 = b2
  generalize Fl4Spec.testBit flags.bv 3 = b3
  -- the source's suspend
  have h1 : (if b0 = true then sched.suspend st ar s a src else ok (s, a)) ⦃ r => r.2 = a ∧ ∃ σ1,
      Fl4Spec.NonDet.when (b0 = true) (Fl4Spec.suspend (Z := Unit) src.bv) σ = ({((), σ1)}, False) ∧
      IRel st th cr N T C E R B c r.1 σ1 ∧ SchedValid σ1 ∧ ObjCover N T E R C σ1 ∧ Inv σ1 ∧
      RemoveTcbOK st N T C E R c r.1 σ1 ⦄ := by
    cases b0
    · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      exact ⟨trivial, σ, rfl, hX, hSV, hOC, hInv, hOK⟩
    · simp only [↓reduceIte]
      refine WP.spec_mono hSus ?_
      rintro r ⟨h1, σ1, h2, h3⟩
      exact ⟨h1, σ1, by simpa [Fl4Spec.NonDet.when] using h2, h3⟩
  refine WP.spec_bind h1 ?_
  rintro ⟨s1, a1⟩ ⟨ha1, σ1, hm1, hX1, hSV1, hOC1, hInv1, hOK1⟩
  obtain rfl : a = a1 := ha1.symm
  -- the target's restart
  have h2 : (if b1 = true then sched.restart st ar s1 a dest else ok (s1, a)) ⦃ r => r.2 = a ∧ ∃ σ2,
      Fl4Spec.NonDet.when (b1 = true) (Fl4Spec.restart (Z := Unit) dest.bv) σ1 = ({((), σ2)}, False) ∧
      IRel st th cr N T C E R B c r.1 σ2 ∧ Inv σ2 ⦄ := by
    cases b1
    · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      exact ⟨trivial, σ1, rfl, hX1, hInv1⟩
    · simp only [↓reduceIte]
      refine WP.spec_mono (restart_tcb_irelS hP0 (removeTcbHypP_ok hP0) s1 a σ1 hX1 hd hSV1 hOC1 hInv1
        (fun x hk hfr => removeTcbOK_fault hP0 hX1 hd hk hfr hOK1) (Sched.restartSpecOK_of hInv1 hSV1.scSpor) hmb) ?_
      rintro r ⟨h1, σ2, h2, h3, -, h5⟩
      exact ⟨h1, σ2, by simpa [Fl4Spec.NonDet.when] using h2, h3, h5⟩
  refine WP.spec_bind h2 ?_
  rintro ⟨s2, a2⟩ ⟨ha2, σ2, hm2, hX2, hInv2⟩
  obtain rfl : a = a2 := ha2.symm
  -- the register copies and the tail
  have hfr := frame_regs_val
  have hgr := gp_regs_val
  have hgp : ∀ (lp : S → Result S) (s3 : S) (σ3 : Fl4Spec.State Unit), IRel st th cr N T C E R B c s3 σ3 →
      Inv σ3 →
      (∀ s' σ', IRel st th cr N T C E R B c s' σ' → Inv σ' → lp s' ⦃ s'' => ∃ σ'',
        Fl4Spec.NonDet.mapMx (crb src.bv dest.bv) Fl4Spec.gpRegisters σ' = ({((), σ'')}, False) ∧
        IRel st th cr N T C E R B c s'' σ'' ∧ Inv σ'' ⦄) →
      (if b3 = true then do
        let s5 ← lp s3
        let s6 ← tcb.post_modify_registers st s5 dest
        let t ← sched.cur_thread st s6
        let b ← obj.Tcb.Insts.CoreCmpPartialEqTcb.eq dest t
        if b then do
          let s7 ← sched.reschedule_required st s6
          ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s7, a)
        else ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s6, a)
      else do
        let s6 ← tcb.post_modify_registers st s3 dest
        let t ← sched.cur_thread st s6
        let b ← obj.Tcb.Insts.CoreCmpPartialEqTcb.eq dest t
        if b then do
          let s7 ← sched.reschedule_required st s6
          ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s7, a)
        else ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s6, a)) ⦃ r =>
      r.1 = .Ok () ∧ r.2.2 = a ∧ ∃ σ', (do
        Fl4Spec.NonDet.when (b3 = true) (Fl4Spec.NonDet.mapMx (crb src.bv dest.bv) Fl4Spec.gpRegisters)
        let cur ← Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread
        Fl4Spec.archPostModifyRegisters cur dest.bv
        Fl4Spec.NonDet.when (dest.bv = cur) Fl4Spec.rescheduleRequired) σ3 = ({((), σ')}, False) ∧
        IRel st th cr N T C E R B c r.2.1 σ' ⦄ := by
    intro lp s3 σ3 hX3 hI3 hlp
    cases b3
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine WP.spec_mono (cr_tailA hP0 hI3.actReady hX3 hd a) ?_
      rintro r ⟨h1, h2, σ', h3, h4⟩
      refine ⟨h1, h2, σ', ?_, h4⟩
      rw [nd_bind_one (show Fl4Spec.NonDet.when (false = true) _ σ3 = ({((), σ3)}, False) from rfl)]
      exact h3
    · simp only [↓reduceIte]
      refine WP.spec_bind (hlp s3 σ3 hX3 hI3) ?_
      rintro s5 ⟨σ5, hm5, hX5, hI5⟩
      refine WP.spec_mono (cr_tailA hP0 hI5.actReady hX5 hd a) ?_
      rintro r ⟨h1, h2, σ', h3, h4⟩
      refine ⟨h1, h2, σ', ?_, h4⟩
      rw [nd_bind_one (show Fl4Spec.NonDet.when (true = true) _ σ3 = ({((), σ5)}, False) by
        unfold Fl4Spec.NonDet.when; rw [if_pos rfl]; exact hm5)]
      exact h3
  have hlpg : ∀ (body : S → U64 → Result (ControlFlow (S × U64) S)), (∀ s i, body s i = if i < tcb.N_GP then (do
        let i1 ← lift (UScalar.cast .Usize i)
        let r ← Aeneas.Std.Array.index_usize regs.GP_REGISTERS i1
        let v ← obj.Tcb.reg st src s r
        let i2 ← regs.sanitise r v
        let s1 ← obj.Tcb.set_reg st dest s r i2
        let i3 ← i + 1#u64
        ok (ControlFlow.cont (s1, i3)))
      else ok (ControlFlow.done s)) →
      ∀ s' σ', IRel st th cr N T C E R B c s' σ' → Inv σ' → loop (fun (x : S × U64) => body x.1 x.2) (s', 0#u64) ⦃ s'' => ∃ σ'',
        Fl4Spec.NonDet.mapMx (crb src.bv dest.bv) Fl4Spec.gpRegisters σ' = ({((), σ'')}, False) ∧
        IRel st th cr N T C E R B c s'' σ'' ∧ Inv σ'' ⦄ :=
    fun body hbody s' σ' hX' hI' => WP.spec_mono (cr_loop_gen hP0 regs.GP_REGISTERS tcb.N_GP Fl4Spec.gpRegisters hgr
      (by unfold tcb.N_GP; rfl) (by decide) hs hd body hbody s' σ' hX') fun s'' ⟨σ'', hm, hX''⟩ =>
        ⟨σ'', hm, hX'', inv_crb hX' hs hd hI' hm⟩
  have hspec : ∀ σ3 σ', (Fl4Spec.NonDet.when (b2 = true) (do
        Fl4Spec.NonDet.mapMx (crb src.bv dest.bv) Fl4Spec.frame_registers
        let pc ← Fl4Spec.asUser (Z := Unit) dest.bv Fl4Spec.getRestartPC
        Fl4Spec.asUser dest.bv (Fl4Spec.setNextPC pc))) σ2 = ({((), σ3)}, False) →
      (do
        Fl4Spec.NonDet.when (b3 = true) (Fl4Spec.NonDet.mapMx (crb src.bv dest.bv) Fl4Spec.gpRegisters)
        let cur ← Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread
        Fl4Spec.archPostModifyRegisters cur dest.bv
        Fl4Spec.NonDet.when (dest.bv = cur) Fl4Spec.rescheduleRequired) σ3 = ({((), σ')}, False) →
      specCr dest.bv src.bv b0 b1 b2 b3 σ = ({((), σ')}, False) := by
    intro σ3 σ' e3 e4
    unfold specCr
    rw [nd_bind_one hm1, nd_bind_one hm2, nd_bind_one (show Fl4Spec.archGetSanitiseRegisterInfo (Z := Unit) dest.bv σ2 =
      ({(false, σ2)}, False) from rfl)]
    exact (nd_bind_one e3 _).trans e4
  cases b2
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_mono (hgp (fun s' => tcb.copy_registers_loop2 st s' dest src 0#u64) s2 σ2 hX2 hInv2
      (fun s' σ' hX' hI' => by unfold tcb.copy_registers_loop2; exact hlpg _ (fun _ _ => rfl) s' σ' hX' hI')) ?_
    rintro r ⟨h1, h2, σ', h3, h4⟩
    exact ⟨h1, h2, σ', hspec σ2 σ' rfl h3, h4⟩
  · simp only [↓reduceIte]
    have hl0 := cr_loop_gen hP0 regs.FRAME_REGISTERS tcb.N_FRAME Fl4Spec.frame_registers hfr
      (by unfold tcb.N_FRAME; rfl) (by decide) hs hd _ (fun _ _ => rfl) s2 σ2 hX2
    unfold tcb.copy_registers_loop0
    refine WP.spec_bind hl0 ?_
    rintro s3 ⟨σ3, hm3, hX3⟩
    have hInv3 : Inv σ3 := inv_crb hX2 hs hd hInv2 hm3
    obtain ⟨x3, hk3, hTR3⟩ := hX3.1.tcb dest hd
    step with Endp.obj.Tcb.reg.spec as ⟨pc, hpc⟩
    have hF : layout.reg.FAULT_IP = regIdx .faultIP := by unfold layout.reg.FAULT_IP; rfl
    have hNx : layout.reg.NEXT_IP = regIdx .nextIP := by unfold layout.reg.NEXT_IP; rfl
    have hpcv : pc.bv = x3.tcbArch.tcbContext.userRegs .faultIP := by rw [hpc, hF]; exact hTR3.regs .faultIP
    refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s3 dest _ pc) ?_
    rintro s4 rfl
    rw [hNx]
    have hX4 := reg_wr_irel hP0 hX3 hd hk3 .nextIP (by decide) pc
    have hInv4 : Inv (Notif.updK σ3 dest.bv (.tcb (Notif.setReg x3 .nextIP pc.bv))) :=
      inv_updView hInv3 hk3 ⟨rfl, rfl, rfl, rfl, rfl⟩
    refine WP.spec_mono (hgp (fun s' => tcb.copy_registers_loop1 st s' dest src 0#u64) _ _ hX4 hInv4
      (fun s' σ' hX' hI' => by unfold tcb.copy_registers_loop1; exact hlpg _ (fun _ _ => rfl) s' σ' hX' hI')) ?_
    rintro r ⟨h1, h2, σ', h3, h4⟩
    refine ⟨h1, h2, σ', hspec _ σ' ?_ h3, h4⟩
    unfold Fl4Spec.NonDet.when
    rw [if_pos rfl, nd_bind_one hm3,
      nd_bind_one (show Fl4Spec.asUser (Z := Unit) dest.bv Fl4Spec.getRestartPC σ3 =
        ({(x3.tcbArch.tcbContext.userRegs .faultIP, σ3)}, False) from asUser_getRegister_eq hk3 .faultIP), ← hpcv]
    exact asUser_setRegister_eq .nextIP pc.bv hk3


end

end

end Fl4Proofs.P3.Ipc

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

variable (st) in
/-- **The rest of the scheduler facts across a suspend** [J-step; the
Suspend `JAtZ` step's building block, narrowed from the former
`SuspendKeeps`]: from `IRel` with `JAtZ`'s scheduler facts and P1's
`BlkOK`, at the outcome of the spec's `suspend` related to FL4's state after
`sched::suspend`: l4v `valid_sched`/`valid_objs` (`SchedValid`, `ObjCover`)
and the call stacks (`CallRel`, `RFree` at some ghost lists).

The rest of the former premise is proved (`copyRegsXHypJ`): `IRel` by
`suspend_irelY`; `Inv` by TcbSpecInv's `suspend_inv` (the thread queued at
most in its own ready queue by `SchedSpec`, `rq_own`); `NSC`, the SCs'
sizes and so `RPlaced` from its `OIK` frame and P1's `sched.suspend.kw`
(the kernel-state base kept); the SCs nonzero (static).

Not proved here: the four facts need `cancel_ipc`'s per-state effects
beyond `IK` (the endpoint/notification queue removal and the waiter's state
for `SchedValid`'s queue clauses; the endpoint and reply objects' kinds for
`ObjCover`, which `IK` does not track; the call-stack pop of
`reply_remove_tcb` with FL4's reply links for `CallRel`/`RFree`), i.e. a
`cancel_ipc` `JAtZ` step (as `finNtfnJ` for `cancel_all_signals`). -/
def SuspendSV (arI : machine.Arch A) (Z : XSets) (H : P1.Heap) (Cs : Set U64) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (cr : Fl4Spec.Cr3) (t : U64) (Ac : Set U64),
    IRel st Z.th cr Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ → SchedValid σ → ObjCover Z.N Z.T Z.E Z.R Z.C σ → Inv σ →
    RemoveTcbOK st Z.N Z.T Z.C Z.E Z.R Z.c s σ → YieldRel Z.T Z.C (L.mem s) σ →
    P1.BlkOK st Z.T Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H) (P1.Heap.scs H)
      (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s → t ∈ Z.T →
    sched.suspend st arI s a t ⦃ r => ∀ σ', Fl4Spec.suspend (Z := Unit) t.bv σ = ({((), σ')}, False) →
      IRel st Z.th cr Z.N Z.T Z.C Z.E Z.R Z.B Z.c r.1 σ' → SchedValid σ' ∧ ObjCover Z.N Z.T Z.E Z.R Z.C σ' ∧
      ∃ Lst : U64 → List U64, CallRel (L.mem r.1) Z.R Z.C σ' Lst ∧ RFree (L.mem r.1) Z.R Z.C σ' Lst ⦄

/-- A thread is at most in its own ready queue (`SchedSpec`: domain 0, the
queue of its priority word). -/
theorem rq_own {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ)
    {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) :
    ∀ d p, t.bv ∈ σ.readyQueues d p → d = x.tcbDomain ∧ p = x.tcbPriority := by
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨x', hk', hd, -, -, hpr⟩ := hs.tcb t ht
  rw [hk] at hk'; cases hk'
  intro d p hm
  by_cases hd0 : d = 0
  · subst hd0
    obtain ⟨pw, hpw, rfl⟩ := Sched.prio_of_spec p
    rw [hs.rq pw hpw, Sched.mem_map_bv] at hm
    have e := hc.inQ pw hpw t hm
    refine ⟨hd.symm, ?_⟩
    rw [← e]; exact Sched.specPrio_eq hpr
  · rw [hs.rqDom d p hd0] at hm; simp at hm

variable {arI : machine.Arch A}

set_option maxHeartbeats 8000000 in
/-- **`CopyRegsXHyp` from `JAtZ`** (`copyRegsXHyp_of` re-scoped): `JAtZ`
after the caller's restart (`jat_restart`), `IRel` at its sets, then
`copy_registers_irelS` with its facts. Named: the target among the TCBs, a
thread cap's object among them (l4v `valid_cap`, the decode's); the
scheduler facts across the source's suspend not proved here (`SuspendSV`)
[J-step]; the platform's `MIN_BUDGET` [P]. -/
theorem copyRegsXHypJ {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {ar : A} {σ : Fl4Spec.State Unit} {ct p : U64}
    {blk call don : Bool}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hJS : JStepHyps (L := L) arI AR Z.th)
    (hcur : σ.curThread = ct.bv) (hpT : p ∈ Z.T)
    (hsT : ∀ src : U64, (∃ x, IsSlot Z.th x ∧ capV (L.mem s) x = .Thread src) → src ∈ Z.T)
    (hSK : SuspendSV st arI Z H Cs)
    (hmb : ∀ a, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) :
    CopyRegsXHyp (L := L) arI AR Z.th s σ ct p blk call don := by
  intro s1 σ1 src flags a hs1 hst hsrc ⟨Zx, hXx⟩
  have hAR : AR a σ1.archState.x64CurrentCr3 := hXx.fin.1.1.2.2.2.2.2.2
  obtain ⟨Ac', Lst', D', J'⟩ := jat_restart J hni hJS hcur hs1 hst
  have hP0 := J.ip
  have hI := J'.xtop.irelK J'.ks J'.buf
  have hsrcT := hsT src hsrc
  have hB := J'.blk
  rw [← J'.tcbs_eq.1] at hB
  -- the source's suspend: `IRel`, the proved facts, `SuspendSV`
  have hSus : sched.suspend st arI s1 a src ⦃ r => r.2 = a ∧ ∃ σ',
      Fl4Spec.suspend (Z := Unit) src.bv σ1 = ({((), σ')}, False) ∧
      IRel st Z.th σ1.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c r.1 σ' ∧ SchedValid σ' ∧
      ObjCover Z.N Z.T Z.E Z.R Z.C σ' ∧ Inv σ' ∧ RemoveTcbOK st Z.N Z.T Z.C Z.E Z.R Z.c r.1 σ' ⦄ := by
    have hB' := hB
    obtain ⟨⟨Q1, R1, h0⟩, hBd, hXI, -, hSg⟩ := hB'
    refine WP.spec_mono (WP.spec_and (WP.spec_and (suspend_irelY (ar := arI) hP0 (removeTcbHypP_ok hP0) s1 a σ1
      hI hsrcT J'.sv J'.obj J'.inv (fun x hk hfr => removeTcbOK_fault hP0 hI hsrcT hk hfr J'.removeTcbOK) J'.yld hB)
      (Fl4Proofs.P1.sched.suspend.kw s1 a src h0 hsrcT hBd hXI hSg.sub))
      (hSK s1 a σ1 _ src Ac' hI J'.sv J'.obj J'.inv J'.removeTcbOK J'.yld hB hsrcT)) ?_
    rintro ⟨s2, a2⟩ ⟨⟨⟨h1, σ2, h2, h3⟩, hF⟩, hW⟩
    try simp only [WP.uncurry'_pair] at hF
    obtain ⟨hsv2, hoc2, Lst2, hcr2, hrf2⟩ := hW σ2 h2 h3
    obtain ⟨xs, hks, -⟩ := hI.1.tcb src hsrcT
    obtain ⟨hInv2, hO⟩ := Sched.suspend_inv J'.inv hks (rq_own hI.2.2.1 hsrcT hks)
      (by rw [h2]; exact Set.mem_singleton _)
    exact ⟨h1, σ2, h2, h3, hsv2, hoc2, hInv2, Lst2, hcr2, hrf2, J'.rp.frame hF.1 (Sched.oik_szKeep hO),
      J'.nsc.oik hO, hInv2, J'.c0, hsv2, hoc2⟩
  refine WP.spec_mono (copy_registers_irelS (ar := arI) hP0 s1 a σ1 hI hsrcT hpT flags J'.sv J'.obj J'.inv
    J'.removeTcbOK hSus (hmb a)) ?_
  rintro r ⟨h1, hr2, σ', hsp, hI'⟩
  obtain ⟨⟨Z', -, -, -, -, -, -, -, -, hZ'⟩, -⟩ := IRel.xtop (L := L) (AR := AR) (a := r.2.2) hI' (by rw [hr2]; exact hAR)
  refine ⟨h1, (.ok [], σ'), ?_, rfl, (SRT.relTop hI').1, Z', hZ'⟩
  show _ ∈ ((Fl4Spec.invokeTcb (Z := Unit) _).run σ1).1
  rw [invokeTcb_cr]
  exact mem_liftE (x := ([], σ')) (mem_bind_nd (by rw [hsp]; exact Set.mem_singleton _) (Set.mem_singleton _))

end

end

end Fl4Proofs.P3
