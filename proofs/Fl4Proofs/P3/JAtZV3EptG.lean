/-
P3 (line mmuAD, gen 40): **the EPT map arm's guest-address bound at `JAtZV3`** — FL4's `ept::decode` map label
(crates/fl4-core/src/ept.rs l. 288-292: `gpa = arg0 & !((1 << (level & 63)) - 1)`, `gpa >= LIMIT` →
`InvalidArgument 0`) against the extended spec's `decodeEptInvocation` (Ext/VirtEptInv: `args.getD 0 0 &&&
~~~((1 <<< level) - 1) ≥ guestGpaLimit` → `invalidArgument 0`), after the checks of P3/JAtZV3EptE.

* `capV_ept_level`: a decoded EPT cap has `level < 64` (`decodeF`: `(w0 >>> 53) &&& 63`, capability.rs l. 205), so
  FL4's `level & 63` is `level` and the two masks agree (`zv_gpaMask`: FL4's `!((1 << (level & 63)) - 1)` word is the
  spec's `~~~((1 <<< level.val) - 1)`).
* `zv_eptF_gpa` (FL4), `zv_eD_gpa` (spec); **`JAtZV3.eptGpaJ`**: from `JAtZV3`, the invoked slot `sl` holding an
  unmapped `Ept ptr level false asid va` (`level ≠ 0`), the map label, `length ≥ 2`, a non-null `ex[0]`, and FL4's
  first argument word `i` (`syscall_arg … 0 = ok i`) whose masked guest address is at or above `2^47`: FL4 returns
  `InvalidArgument 0` with the store and arch state unchanged (`JAtZV3` after), and for every spec argument list
  agreeing with FL4's words (`VArgs`, length ≥ 2) and non-empty extra caps, the extended decoder's single outcome is
  `(.error (.invalidArgument 0), σ)`.

Still not covered (P3/JAtZV3EptE's docstring): `ept::root` and everything after it (the root-shape error comes
first there: an `ex[0]` cap that is not a mapped level-0 EPT cap gives invalid cap 1 on both sides, not done).

No named premise. No existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3EptE
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- A decoded EPT cap's level is below 64 (module docstring). -/
theorem capV_ept_level {m : U64 → U64} {y p l a v : U64} {mm : Bool} (h : capV m y = .Ept p l mm a v) :
    l.val < 64 := by
  unfold capV decodeF at h
  dsimp only at h
  split at h <;> first | (cases h; done) | skip
  all_goals
    injection h with e1 e2 e3 e4 e5
    subst e2
    show (((m y).bv >>> 53) &&& 63#64).toNat < 64
    rw [BitVec.toNat_and]
    exact lt_of_le_of_lt Nat.and_le_right (by decide)

theorem zv_pow64 {l : Nat} (hl : l < 64) : 1 ≤ 2 ^ l ∧ 2 ^ l < 2 ^ 64 :=
  ⟨Nat.one_le_two_pow, Nat.pow_lt_pow_right (by decide) hl⟩

/-- FL4's mask word against the spec's (module docstring). -/
theorem zv_gpaMask {l z i3 : U64} (hl : l.val < 64) (hz : z.val = 2 ^ l.val) (hi3 : i3.val = z.val - 1) :
    i3.bv = (1#64 <<< l.val) - 1 := by
  obtain ⟨p1, p2⟩ := zv_pow64 hl
  apply BitVec.eq_of_toNat_eq
  have e1 : (1#64 <<< l.val).toNat = 2 ^ l.val := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    simp only [BitVec.toNat_ofNat, Nat.one_mod_two_pow (by decide : 0 < 64), Nat.one_mul]
    exact Nat.mod_eq_of_lt p2
  rw [BitVec.toNat_sub, e1]
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
  have hb : i3.bv.toNat = i3.val := rfl
  rw [hb, hi3, hz]
  have h1 : (1 : BitVec 64).toNat = 1 := by decide
  rw [h1]
  rw [h64] at p2 ⊢
  generalize 2 ^ l.val = X at p1 p2 ⊢
  omega

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

theorem zv_eptF_gpa (s : S) (a : A) {lbl len ptr level asid va : U64} (dest buf : U64)
    (ex : Array obj.Slot 3#usize) (h0 : level ≠ 0#u64) (hl64 : level.val < 64)
    (hu : lbl.val ≠ (Fl4Spec.eptTableLabels level.val).2) (hm : lbl.val = (Fl4Spec.eptTableLabels level.val).1)
    (hl : ¬ len.val < 2) (hz : exAt ex 0 ≠ 0#u64) {ct : U64} (hct : sched.cur_thread st s = ok ct) {i : U64}
    (hsa : msg.syscall_arg st s ct buf 0#u64 = ok i)
    (hg : (i.bv &&& ~~~((1#64 <<< level.val) - 1)) ≥ Fl4Spec.guestGpaLimit) :
    ept.decode st arI s a lbl len (.Ept ptr level false asid va) dest buf ex =
      ok (.Err (.Sys (.InvalidArgument 0#u64)), s, a) := by
  have hu' : lbl ≠ (eptLbl level).2 := zv_lblNe (zv_eptLbl_val level).2 hu
  have hm' : lbl = (eptLbl level).1 := zv_lblEq (zv_eptLbl_val level).1 hm
  unfold ept.decode
  dsimp only
  rw [if_pos (show (level != 0#u64) = true by simpa using h0), zv_eptLblIf, bind_ok]
  generalize eptLbl level = q at hu' hm' ⊢
  obtain ⟨mL, uL⟩ := q
  dsimp only at hu' hm'
  simp only [uncurry_apply_pair]
  rw [hct, bind_ok, if_neg hu', if_pos hm']
  have g2 : ¬ len < 2#u64 := by scalar_tac
  rw [if_neg g2, zv_ex0Idx, bind_ok, zv_ex0Null, bind_ok,
    if_neg (show ¬ (decide (exAt ex 0 = 0#u64) = true) by simpa using hz),
    if_neg (show ¬ (false = true) by decide), hsa, bind_ok]
  obtain ⟨z, hz2, hzv⟩ := shl_radix hl64
  have hz1 : 1 ≤ z.val := by rw [hzv]; exact (zv_pow64 hl64).1
  obtain ⟨i3, hi3, hi3v, -⟩ := spec_exists (U64.sub_spec (x := z) (y := 1#u64) (by scalar_tac))
  obtain ⟨i5, hi5, hi5v⟩ := spec_exists Fl4Proofs.P0.Consts.ept.LIMIT.spec
  simp only [lift, bind_ok, hz2, hi3, hi5]
  have hm3 := zv_gpaMask hl64 hzv (by rw [hi3v]; rfl)
  have hge : (i &&& ~~~i3) >= i5 := by
    subst hi5v
    show (140737488355328#u64).val ≤ (i &&& ~~~i3).val
    have hv : (i &&& ~~~i3).val = (i.bv &&& ~~~((1#64 <<< level.val) - 1)).toNat := by
      rw [← hm3]; rfl
    rw [hv]
    have hg' : (Fl4Spec.guestGpaLimit).toNat ≤ (i.bv &&& ~~~((1#64 <<< level.val) - 1)).toNat := hg
    have hL : (Fl4Spec.guestGpaLimit).toNat = 140737488355328 := by
      unfold Fl4Spec.guestGpaLimit; decide
    rw [hL] at hg'
    exact hg'
  rw [if_pos hge]
  simp [error.invalid_arg]

end

section
open Fl4Spec

theorem zv_eD_gpa {label : Data} {args : List Data} (slot : CslotPtr) (p : ObjRef) {l : Nat}
    (x : Cap × CslotPtr) (rest : List (Cap × CslotPtr)) (hl : l ≠ 0)
    (h1 : dataToNat label ≠ (eptTableLabels l).2) (h2 : dataToNat label = (eptTableLabels l).1)
    (hn : ¬ args.length < 2) (hg : (args.getD 0 0 &&& ~~~(((1 : Word) <<< l) - 1)) ≥ guestGpaLimit) (σ : State Unit) :
    ExceptT.run (decodeEptInvocation (Z := Unit) label args slot (.eptCap p l none) (x :: rest)) σ =
      ({(.error (.invalidArgument 0), σ)}, False) := by
  unfold decodeEptInvocation
  dsimp only
  rw [if_neg hl]
  generalize eptTableLabels l = q at h1 h2 ⊢
  obtain ⟨mL, uL⟩ := q
  dsimp only at h1 h2 ⊢
  rw [if_neg h1, if_pos h2, if_neg hn, if_neg (by simp)]
  exact run_bind_error (by unfold NonDetE.whenE; rw [if_pos hg]; rfl) _

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

/-- **The EPT map arm's guest-address bound at `JAtZV3`** (module docstring). -/
theorem JAtZV3.eptGpaJ (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {sl : Fl4Spec.CslotPtr}
    {ptr level asid va : U64} (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Ept ptr level false asid va))
    (lbl len : U64) (block call cd fp : Bool) (buf : U64) (ex : Array obj.Slot 3#usize) (h0 : level ≠ 0#u64)
    (hu : lbl.val ≠ (Fl4Spec.eptTableLabels level.val).2) (hm : lbl.val = (Fl4Spec.eptTableLabels level.val).1)
    (hl : ¬ len.val < 2) (hz : exAt ex 0 ≠ 0#u64) {ct : U64} (hct : sched.cur_thread st s = ok ct) {i : U64}
    (hsa : msg.syscall_arg st s ct buf 0#u64 = ok i)
    (hg : (i.bv &&& ~~~((1#64 <<< level.val) - 1)) ≥ Fl4Spec.guestGpaLimit) :
    syscall.decode_invocation st arI s a lbl len (cslotAddr sl) (.Ept ptr level false asid va) block call cd fp
        buf ex = ok (.Err (.Sys (.InvalidArgument 0#u64)), s, a) ∧ JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ ∧
      ∀ (args : List Fl4Spec.Data) (ec : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), VArgs st s ct buf len args →
        ec ≠ [] → ∀ (fp' : Bool) (cref : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef),
          ErrRel (.Sys (.InvalidArgument 0#u64)) (.invalidArgument 0) ∧
          ExceptT.run (Fl4Spec.fl4DecodeInvocationV (Z := Unit) fp' lbl.bv args cref sl
            (absCap (.Ept ptr level false asid va)) ec buffer) σ = ({(.error (.invalidArgument 0), σ)}, False) := by
  have hl64 : level.val < 64 := capV_ept_level (m := L.mem s) (y := cslotAddr sl) (by
    rw [capAt_capV] at hc; exact ok_inj hc)
  have hl0 : level.val ≠ 0 := fun e => h0 (UScalar.eq_of_val_eq (by rw [e]; rfl))
  refine ⟨by rw [zv_sysdec_ept]; exact zv_eptF_gpa s a _ buf ex h0 hl64 hu hm hl hz hct hsa hg, J,
    fun args ec hA hne fp' cref buffer => ⟨Or.inl rfl, ?_⟩⟩
  obtain ⟨x, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have ha0 : args.getD 0 0 = i.bv := hA.a0 (by omega) hsa
  have habs : absCap (.Ept ptr level false asid va) =
      .archObjectCap (.eptCap ptr.bv level.val none) := rfl
  rw [habs, zv_decV_ept]
  exact run_liftME_err (zv_eD_gpa _ _ x rest hl0 hu hm (by rw [hA.1]; exact hl) (by rw [ha0]; exact hg) σ)

end

end

end Fl4Proofs.P3
