/-
P3 (DESIGN.md §9), TCB invocations: **CopyRegisters on `IRel`**
(`tcb::copy_registers` against l4v `invoke_tcb CopyRegisters`), and its leaf
at `XTop` (XTopTcbSched's `CopyRegsXHyp`).

The source's suspend (`suspend_irel`), the target's restart
(`restart_tcb_irel`), the register copies (`cr_loop_gen`: each step reads
the source's register and writes the target's, sanitised, on `IRel` by
`reg_any_wr_irel`), the restart PC, then `post_modify_registers` and the
reschedule of the current thread (`cr_tail`).
-/
import Fl4Proofs.P3.IpcWriteRegs
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

theorem andk_ne0 (f c : U64) (k : Nat) (hk : k < 64) (hc : c.bv = BitVec.twoPow 64 k) :
    ((f &&& c) != 0#u64) = Fl4Spec.testBit f.bv k := by
  have e : (f &&& c).bv = if f.bv.getLsbD k then BitVec.twoPow 64 k else 0#64 := by
    simp only [UScalar.bv_and, hc]; exact BitVec.and_twoPow _ _
  have h0 : BitVec.twoPow 64 k ≠ 0 := by
    intro h; have := congrArg BitVec.toNat h
    rw [BitVec.toNat_twoPow, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hk)] at this
    simp at this
  cases hb : f.bv.getLsbD k
  · rw [hb] at e
    have : (f &&& c) = 0#u64 := UScalar.eq_of_val_eq (by
      have := congrArg BitVec.toNat e; simpa using this)
    simp [this, hb]
  · rw [hb] at e
    have h1 : (f &&& c).bv ≠ 0 := by rw [e]; simpa using h0
    have : (f &&& c) ≠ 0#u64 := fun h' => h1 (by rw [h']; rfl)
    simp [this, hb]

section Spec
open Fl4Spec

/-- One step of the spec's register copy. -/
abbrev crb (src dest : ObjRef) (r : Register) : SMonad Unit Unit := do
  let v ← asUser src <| getRegister r
  asUser dest <| setRegister r (sanitiseRegister false r v)

theorem mapMx_snoc {α : Type} (f : α → SMonad Unit Unit) : ∀ (l : List α) (a : α),
    NonDet.mapMx f (l ++ [a]) = (NonDet.mapMx f l >>= fun _ => f a >>= fun _ => pure ())
  | [], a => by
    show NonDet.bind (f a) (fun _ => NonDet.pure ()) = _
    funext σ
    show _ = ((pure () : NonDet (State Unit) Unit) >>= _) σ
    rw [nd_pure_bind']
    rfl
  | b :: l, a => by
    show NonDet.bind (f b) (fun _ => NonDet.mapMx f (l ++ [a])) = _
    rw [mapMx_snoc f l a]
    show (f b >>= fun _ => NonDet.mapMx f l >>= fun _ => f a >>= fun _ => pure ()) =
      ((f b >>= fun _ => NonDet.mapMx f l) >>= fun _ => f a >>= fun _ => pure ())
    rw [nd_assoc_f]

/-- The spec's CopyRegisters, before its empty result. -/
def specCr (dest src : ObjRef) (sS rT tF tI : Bool) : SMonad Unit Unit := do
  NonDet.when sS <| suspend src
  NonDet.when rT <| restart dest
  let sanitiseInfo ← archGetSanitiseRegisterInfo dest
  NonDet.when tF <| do
    NonDet.mapMx (fun r => do
        let v ← asUser src <| getRegister r
        asUser dest <| setRegister r (sanitiseRegister sanitiseInfo r v)) frame_registers
    let pc ← asUser dest getRestartPC
    asUser dest <| setNextPC pc
  NonDet.when tI <|
    NonDet.mapMx (fun r => do
        let v ← asUser src <| getRegister r
        asUser dest <| setRegister r (sanitiseRegister sanitiseInfo r v)) gpRegisters
  let cur ← NonDet.gets fun s : State Unit => s.curThread
  archPostModifyRegisters cur dest
  NonDet.when (dest = cur) rescheduleRequired

theorem invokeTcb_cr (dest src : ObjRef) (sS rT tF tI : Bool) (arch : ArchCopyRegisterSets) :
    invokeTcb (Z := Unit) (.copyRegisters dest src sS rT tF tI arch) =
      NonDetE.liftE (specCr dest src sS rT tF tI >>= fun _ => pure []) := by
  unfold invokeTcb specCr
  simp only [nd_assoc_f]

end Spec

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

set_option maxHeartbeats 8000000 in
/-- **`IRel` across any register write** of a TCB's saved context: the badge
register by the notification code's `set_badge_reg_relI`, the others by
`reg_wr_irel`. -/
theorem reg_any_wr_irel (hP0 : IPlaced N T E R B) {s : S} {σ : Fl4Spec.State Unit}
    (hX : IRel st th cr N T C E R B c s σ) {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb}
    (hk : σ.kheap t.bv = some (.tcb x)) (r : Fl4Spec.Register) (v : U64) :
    IRel st th cr N T C E R B c (L.wr s (regA t (regIdx r)) v) (Notif.updK σ t.bv (.tcb (Notif.setReg x r v.bv))) := by
  by_cases hr : r = Fl4Spec.badge_register
  · subst hr
    rw [← badgeRegA_eq_regA]
    obtain ⟨hR', hW, hS⟩ := set_badge_reg_relI hP0 hX.1 ht hk v
    exact ⟨hR', hX.2.1.stableN hP0.n hW hS, hX.2.2.1.stable hW hS, hX.2.2.2.mono hW.1 (SzKeep.ntfnStep hS)⟩
  · exact reg_wr_irel hP0 hX ht hk r hr v

set_option maxHeartbeats 8000000 in
/-- **A register-copy loop of `copy_registers`** over the registers `Lr`. -/
theorem cr_loop_gen (hP0 : IPlaced N T E R B) {k : Usize} (arr : Aeneas.Std.Array U64 k) (Nl : U64)
    (Lr : List Fl4Spec.Register) (harr : arr.val = Lr.map regIdx) (hN : Nl.val = Lr.length) (hLr : Lr.length ≤ 18)
    {src dest : U64} (hs : src ∈ T) (hd : dest ∈ T)
    (body : S → U64 → Result (ControlFlow (S × U64) S))
    (hbody : ∀ s i, body s i = if i < Nl then (do
        let i1 ← lift (UScalar.cast .Usize i)
        let r ← Aeneas.Std.Array.index_usize arr i1
        let v ← obj.Tcb.reg st src s r
        let i2 ← regs.sanitise r v
        let s1 ← obj.Tcb.set_reg st dest s r i2
        let i3 ← i + 1#u64
        ok (ControlFlow.cont (s1, i3)))
      else ok (ControlFlow.done s))
    (s : S) (σ0 : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ0) :
    loop (fun (x : S × U64) => body x.1 x.2) (s, 0#u64) ⦃ s' => ∃ σ',
      Fl4Spec.NonDet.mapMx (crb src.bv dest.bv) Lr σ0 = ({((), σ')}, False) ∧ IRel st th cr N T C E R B c s' σ' ⦄ := by
  apply loop.spec_decr_nat (measure := fun x => Lr.length - x.2.val)
    (inv := fun x => x.2.val ≤ Lr.length ∧ ∃ σ', Fl4Spec.NonDet.mapMx (crb src.bv dest.bv) (Lr.take x.2.val) σ0 =
      ({((), σ')}, False) ∧ IRel st th cr N T C E R B c x.1 σ')
  · rintro ⟨s', i⟩ ⟨hi, σ', hm, hX'⟩
    simp only at hi hm hX' ⊢
    rw [hbody]
    by_cases h1 : i < Nl
    swap
    · rw [if_neg h1, WP.spec_ok]
      have : i.val = Lr.length := by have := (P1.gt_iff_val).not.1 h1; omega
      rw [this, List.take_length] at hm
      exact ⟨σ', hm, hX'⟩
    rw [if_pos h1]
    have hiL : i.val < Lr.length := by have := (P1.gt_iff_val).1 h1; omega
    simp only [lift, bind_ok]
    refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec _ _ (by
      rw [cast_to_us' i (by omega)]; simp [harr]; omega)) ?_
    rintro rr hrr
    have hrv : rr = regIdx Lr[i.val] := by
      rw [hrr, List.getElem_of_eq harr, List.getElem_map]
      congr 1
      simp [cast_to_us' i (by omega)]
    subst hrv
    obtain ⟨xs, hks, hTs⟩ := hX'.1.tcb src hs
    obtain ⟨xd, hkd, -⟩ := hX'.1.tcb dest hd
    refine WP.spec_bind (Endp.obj.Tcb.reg.spec s' src _) ?_
    rintro v rfl
    obtain ⟨w, hw, hwv⟩ := sanitise_eq Lr[i.val] (L.mem s' (regA src (regIdx Lr[i.val])))
    rw [hw, bind_ok]
    refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s' dest _ w) ?_
    rintro s2 rfl
    obtain ⟨i3, h3e, h3v⟩ := spec_exists (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
    rw [h3e, bind_ok, WP.spec_ok]
    have hi3 : i3.val = i.val + 1 := by simpa using h3v
    refine ⟨⟨by show i3.val ≤ Lr.length; omega, _, ?_, reg_any_wr_irel hP0 hX' hd hkd Lr[i.val] w⟩,
      by show Lr.length - i3.val < Lr.length - i.val; omega⟩
    rw [hi3, List.take_succ, List.getElem?_eq_getElem hiL]
    simp only [Option.toList_some]
    rw [mapMx_snoc, nd_bind_one hm]
    unfold crb
    simp only [nd_assoc_f]
    rw [nd_bind_one (asUser_getRegister_eq hks _), ← hTs.regs, ← hwv, nd_bind_one (asUser_setRegister_eq _ _ hkd)]
    rfl
  · exact ⟨by simp, σ0, by simp; rfl, hX⟩

set_option maxHeartbeats 8000000 in
/-- **The tail of `copy_registers`**: `post_modify_registers`, then the
reschedule if the target is the current thread. -/
theorem cr_tail (hP0 : IPlaced N T E R B) (hAct : ∀ s' σ', IRel st th cr N T C E R B c s' σ' → ActReady σ')
    {s : S} {σ : Fl4Spec.State Unit} (hX : IRel st th cr N T C E R B c s σ) {dest : U64} (hd : dest ∈ T) (a : A) :
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
      IRel st th cr N T C E R B c s4 σ4 ∧ σ4.curThread = ct.bv ⦄ := by
    unfold tcb.post_modify_registers
    refine WP.spec_bind (cur_thread_bv hX.2.2.1) ?_
    rintro ct hct
    rw [tcb_ne_eq, bind_ok]
    by_cases hpc' : dest = ct
    · subst hpc'
      simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      refine ⟨dest, hct.symm, σ, ?_, hX, hct.symm⟩
      unfold Fl4Spec.archPostModifyRegisters Fl4Spec.NonDet.when
      rw [if_neg (by simp)]; rfl
    · simp only [ne_eq, hpc', not_false_eq_true, decide_true, ↓reduceIte]
      have hE : layout.reg.ERROR = regIdx .errorRegister := by unfold layout.reg.ERROR; rfl
      refine WP.spec_mono (Endp.obj.Tcb.set_reg.spec _ dest _ 0#u64) ?_
      rintro s4 rfl
      rw [hE]
      refine ⟨ct, hct.symm, _, ?_, reg_any_wr_irel hP0 hX hd hk .errorRegister 0#u64, by simp [Notif.updK, hct]⟩
      unfold Fl4Spec.archPostModifyRegisters Fl4Spec.NonDet.when
      rw [if_pos (fun e => hpc' (eq_of_bv e)), asUser_setRegister_eq _ _ hk]
      rfl
  refine WP.spec_bind hpm ?_
  rintro s4 ⟨ct, hct, σ4, hpm4, hX4, hct4⟩
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
    refine WP.spec_bind (resched_irel hP0 s4 σ4 hX4 (hAct _ _ hX4)) ?_
    rintro s6 ⟨σ6, h6, -, hX6⟩
    rw [WP.spec_ok]
    exact ⟨rfl, rfl, σ6, hfin σ6 (by simpa [Fl4Spec.NonDet.when] using h6), hX6⟩
  · simp only [hpc', decide_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨trivial, trivial, σ4, hfin σ4 (by unfold Fl4Spec.NonDet.when; rw [if_neg (fun e => hpc' (eq_of_bv e))]; rfl), hX4⟩

set_option maxHeartbeats 16000000 in
/-- **`copy_registers` on `IRel`** (module docstring). Named: `SchedValid`,
`ObjCover`, `Inv`, `YieldRel`, `ActReady` on `IRel` [J], `RemoveTcbHyp`,
the platform's `MIN_BUDGET`. -/
theorem copy_registers_irel (hP0 : IPlaced N T E R B) (hRT : RemoveTcbHyp st th cr N T C E R B c)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ) {src dest : U64}
    (hs : src ∈ T) (hd : dest ∈ T) (flags : U64)
    (hSV : ∀ s' σ', IRel st th cr N T C E R B c s' σ' → SchedValid σ')
    (hOC : ∀ s' σ', IRel st th cr N T C E R B c s' σ' → ObjCover N T E R C σ')
    (hInvI : ∀ s' σ', IRel st th cr N T C E R B c s' σ' → Inv σ')
    (hY : ∀ s' σ', IRel st th cr N T C E R B c s' σ' → YieldRel T C (L.mem s') σ')
    (hAct : ∀ s' σ', IRel st th cr N T C E R B c s' σ' → ActReady σ')
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
      IRel st th cr N T C E R B c r.1 σ1 ⦄ := by
    cases b0
    · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      exact ⟨trivial, σ, rfl, hX⟩
    · simp only [↓reduceIte]
      refine WP.spec_mono (suspend_irel hP0 hRT s a σ hX hs (hSV _ _ hX) (hOC _ _ hX) (hInvI _ _ hX) hY) ?_
      rintro r ⟨h1, σ1, h2, h3⟩
      exact ⟨h1, σ1, by simpa [Fl4Spec.NonDet.when] using h2, h3⟩
  refine WP.spec_bind h1 ?_
  rintro ⟨s1, a1⟩ ⟨ha1, σ1, hm1, hX1⟩
  obtain rfl : a = a1 := ha1.symm
  -- the target's restart
  have h2 : (if b1 = true then sched.restart st ar s1 a dest else ok (s1, a)) ⦃ r => r.2 = a ∧ ∃ σ2,
      Fl4Spec.NonDet.when (b1 = true) (Fl4Spec.restart (Z := Unit) dest.bv) σ1 = ({((), σ2)}, False) ∧
      IRel st th cr N T C E R B c r.1 σ2 ⦄ := by
    cases b1
    · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      exact ⟨trivial, σ1, rfl, hX1⟩
    · simp only [↓reduceIte]
      refine WP.spec_mono (restart_tcb_irel hP0 hRT s1 a σ1 hX1 hd (hSV _ _ hX1) (hOC _ _ hX1) (hInvI _ _ hX1)
        hInvI hAct hmb) ?_
      rintro r ⟨h1, σ2, h2, h3, -⟩
      exact ⟨h1, σ2, by simpa [Fl4Spec.NonDet.when] using h2, h3⟩
  refine WP.spec_bind h2 ?_
  rintro ⟨s2, a2⟩ ⟨ha2, σ2, hm2, hX2⟩
  obtain rfl : a = a2 := ha2.symm
  -- the register copies and the tail
  have hfr := frame_regs_val
  have hgr := gp_regs_val
  have hgp : ∀ (lp : S → Result S) (s3 : S) (σ3 : Fl4Spec.State Unit), IRel st th cr N T C E R B c s3 σ3 →
      (∀ s' σ', IRel st th cr N T C E R B c s' σ' → lp s' ⦃ s'' => ∃ σ'',
        Fl4Spec.NonDet.mapMx (crb src.bv dest.bv) Fl4Spec.gpRegisters σ' = ({((), σ'')}, False) ∧
        IRel st th cr N T C E R B c s'' σ'' ⦄) →
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
    intro lp s3 σ3 hX3 hlp
    cases b3
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine WP.spec_mono (cr_tail hP0 hAct hX3 hd a) ?_
      rintro r ⟨h1, h2, σ', h3, h4⟩
      refine ⟨h1, h2, σ', ?_, h4⟩
      rw [nd_bind_one (show Fl4Spec.NonDet.when (false = true) _ σ3 = ({((), σ3)}, False) from rfl)]
      exact h3
    · simp only [↓reduceIte]
      refine WP.spec_bind (hlp s3 σ3 hX3) ?_
      rintro s5 ⟨σ5, hm5, hX5⟩
      refine WP.spec_mono (cr_tail hP0 hAct hX5 hd a) ?_
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
      ∀ s' σ', IRel st th cr N T C E R B c s' σ' → loop (fun (x : S × U64) => body x.1 x.2) (s', 0#u64) ⦃ s'' => ∃ σ'',
        Fl4Spec.NonDet.mapMx (crb src.bv dest.bv) Fl4Spec.gpRegisters σ' = ({((), σ'')}, False) ∧
        IRel st th cr N T C E R B c s'' σ'' ⦄ :=
    fun body hbody s' σ' hX' => cr_loop_gen hP0 regs.GP_REGISTERS tcb.N_GP Fl4Spec.gpRegisters hgr
      (by unfold tcb.N_GP; rfl) (by decide) hs hd body hbody s' σ' hX'
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
    refine WP.spec_mono (hgp (fun s' => tcb.copy_registers_loop2 st s' dest src 0#u64) s2 σ2 hX2 (fun s' σ' hX' => by
      unfold tcb.copy_registers_loop2; exact hlpg _ (fun _ _ => rfl) s' σ' hX')) ?_
    rintro r ⟨h1, h2, σ', h3, h4⟩
    exact ⟨h1, h2, σ', hspec σ2 σ' rfl h3, h4⟩
  · simp only [↓reduceIte]
    have hl0 := cr_loop_gen hP0 regs.FRAME_REGISTERS tcb.N_FRAME Fl4Spec.frame_registers hfr
      (by unfold tcb.N_FRAME; rfl) (by decide) hs hd _ (fun _ _ => rfl) s2 σ2 hX2
    unfold tcb.copy_registers_loop0
    refine WP.spec_bind hl0 ?_
    rintro s3 ⟨σ3, hm3, hX3⟩
    obtain ⟨x3, hk3, hTR3⟩ := hX3.1.tcb dest hd
    step with Endp.obj.Tcb.reg.spec as ⟨pc, hpc⟩
    have hF : layout.reg.FAULT_IP = regIdx .faultIP := by unfold layout.reg.FAULT_IP; rfl
    have hNx : layout.reg.NEXT_IP = regIdx .nextIP := by unfold layout.reg.NEXT_IP; rfl
    have hpcv : pc.bv = x3.tcbArch.tcbContext.userRegs .faultIP := by rw [hpc, hF]; exact hTR3.regs .faultIP
    refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s3 dest _ pc) ?_
    rintro s4 rfl
    rw [hNx]
    have hX4 := reg_wr_irel hP0 hX3 hd hk3 .nextIP (by decide) pc
    refine WP.spec_mono (hgp (fun s' => tcb.copy_registers_loop1 st s' dest src 0#u64) _ _ hX4 (fun s' σ' hX' => by
      unfold tcb.copy_registers_loop1; exact hlpg _ (fun _ _ => rfl) s' σ' hX')) ?_
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
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

set_option maxHeartbeats 8000000 in
/-- **`CopyRegsXHyp`** (module docstring). Named, at every `Z` an `XTopAt`
holds at: `KsApart`, the IPC placement, the target among the TCBs, a thread
cap's object among the TCBs (l4v `valid_cap`), `SuspendOK` and `ActReady` on
`IRel` [J]; `BufWordRel` at `XTopAt`; the platform's `MIN_BUDGET`. -/
theorem copyRegsXHyp_of {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} {s : S} {σ : Fl4Spec.State Unit}
    {ct p : U64} {blk call don : Bool}
    (hZ : ∀ (Z : XSets) s' a' σ', XTopAt (L := L) AR Z s' a' σ' → KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s') ∧
      IPlaced Z.N Z.T Z.E Z.R Z.B ∧ p ∈ Z.T ∧
      (∀ src : U64, (∃ x, IsSlot th x ∧ capV (L.mem s) x = .Thread src) → src ∈ Z.T) ∧
      (∀ s'' σ'', IRel st Z.th σ'.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s'' σ'' →
        SuspendOK st Z s'' σ'' ∧ Notif.ActReady σ''))
    (hBW : ∀ (Z : XSets) s' a' σ', XTopAt (L := L) AR Z s' a' σ' → BufWordRel Z.T (L.mem s') σ')
    (hmb : ∀ a, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) :
    CopyRegsXHyp (L := L) arI AR th s σ ct p blk call don := by
  intro s1 σ1 src flags a _ _ hsrc ⟨Z, hX⟩
  obtain ⟨hKA, hP0, hpT, hsT, hOK⟩ := hZ Z _ _ _ hX
  have hAR : AR a σ1.archState.x64CurrentCr3 := hX.fin.1.1.2.2.2.2.2.2
  have hI := hX.irelK hKA (hBW _ _ _ _ hX)
  refine WP.spec_mono (copy_registers_irel (ar := arI) hP0
    (removeTcbHyp_of hP0 fun s' σ' h => (hOK s' σ' h).1.1) s1 a σ1 hI (hsT src hsrc) hpT flags
    (fun s' σ' h => let ⟨⟨⟨_, _, _, _, _, _, _, hSV, _⟩, _⟩, _⟩ := hOK s' σ' h; hSV)
    (fun s' σ' h => let ⟨⟨⟨_, _, _, _, _, _, _, _, hOC⟩, _⟩, _⟩ := hOK s' σ' h; hOC)
    (fun s' σ' h => let ⟨⟨⟨_, _, _, _, _, hI, _⟩, _⟩, _⟩ := hOK s' σ' h; hI)
    (fun s' σ' h => (hOK s' σ' h).1.2) (fun s' σ' h => (hOK s' σ' h).2) (hmb a)) ?_
  rintro r ⟨h1, hr2, σ', hsp, hI'⟩
  obtain ⟨⟨Z', -, -, -, -, -, -, -, -, hZ'⟩, -⟩ := IRel.xtop (L := L) (AR := AR) (a := r.2.2) hI' (by rw [hr2]; exact hAR)
  refine ⟨h1, (.ok [], σ'), ?_, rfl, (SRT.relTop hI').1, Z', hZ'⟩
  show _ ∈ ((Fl4Spec.invokeTcb (Z := Unit) _).run σ1).1
  rw [invokeTcb_cr]
  exact mem_liftE (x := ([], σ')) (mem_bind_nd (by rw [hsp]; exact Set.mem_singleton _) (Set.mem_singleton _))

end

end

end Fl4Proofs.P3
