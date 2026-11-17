/-
P3 (DESIGN.md §9), TCB invocations: **CopyRegisters on `IRel`**: the
spec side (`specCr`, `crb`) and the register-copy steps (`cr_loop_gen`: each
step reads the source's register and writes the target's, sanitised, on
`IRel` by `reg_any_wr_irel`). The leaf from `JAtZ` is IpcCopyRegsJ's
`copyRegsXHypJ` (the former `copyRegsXHyp_of` with its "at every `IRel`"
premises is retired).
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

end

end

end Fl4Proofs.P3.Ipc

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

end

end

end Fl4Proofs.P3
