/-
P3 (line mmuAD, gen 34): **message words at `JAtZV3`, appended or overwritten** (step 1 of gen 33's plan toward
`ReportJ3`): P3/XTopJointFault's `MrJ` / `setMrJ` over `JAtZV3`, with the overwrite of an already-written word.

The spec state after the words `ms` is XTopJointFault's `jMrSt σ0 rcv x0 pb ms`; `mrUpd ms k v` is `ms` with word `k`
replaced (`k < |ms|`) or `v` appended (`k = |ms|`).

* (mmuAD gen 42b18) the gen-34 copies `JAtZB.scAlign8B` / `JAtZB.bufPlacedB` are removed: BufInv's `scAlign8` /
  `bufPlacedJ` are now stated over `JAtZB` in place (`JAtZB.scAlign8`, `JAtZB.bufPlacedJ`).
* **`JAtZV3.mrReg`** (word `k < 4`, a register; gen 30's `JAtZV3.regWr`, gen 33's `v3_jMrSt_set_lt` for the
  overwrite), **`JAtZV3.mrBuf`** (word `4 ≤ k`, the receive buffer; gen 33's `JAtZV3.userWr` with
  `JAtZB.bufWordG`, `mrState_snoc_ge` / this gen's `v3_mrState_set_ge`), **`JAtZV3.mrNone`** (no buffer, `4 ≤ k`:
  nothing written).
* **`setMrJ3`**: FL4's `set_mr rcv rw i v` at `JAtZV3 … (jMrSt … ms)`, `i ≤ |ms| < 120`, ends at `JAtZV3 … (jMrSt …
  (mrUpd ms i v))`.
* `v3_syscall_arg2`: `syscall_arg t b 2` reads MR2's register.

No named premise. No existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3MrMem
import Fl4Proofs.P3.JAtZV3RegW
import Fl4Proofs.P3.BufInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-- `ms` with word `k` replaced (`k < |ms|`) or `v` appended. -/
def mrUpd (ms : List Fl4Spec.Word) (k : Nat) (v : Fl4Spec.Word) : List Fl4Spec.Word :=
  if k < ms.length then ms.set k v else ms ++ [v]

theorem mrUpd_length (ms : List Fl4Spec.Word) {k : Nat} (hk : k ≤ ms.length) (v : Fl4Spec.Word) :
    (mrUpd ms k v).length = max ms.length (k + 1) := by
  unfold mrUpd
  split
  · rw [List.length_set]; omega
  · simp; omega

section
open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

variable {σ0 : Fl4Spec.State Unit} {rcv : U64} {x0 : Fl4Spec.Tcb} {pb : Option Fl4Spec.ObjRef}

/-- **A message register written (appended or overwritten) at `JAtZV3`.** -/
theorem JAtZV3.mrReg {ms : List Fl4Spec.Word}
    (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a (jMrSt σ0 rcv.bv x0 pb ms))
    (hr : rcv ∈ Z.T) (k : Nat) (hk4 : k < 4) (hk : k ≤ ms.length) (v : U64) :
    JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D (L.wr s (Endp.regA rcv (regIdx (Endp.mrIdx k))) v) a
      (jMrSt σ0 rcv.bv x0 pb (mrUpd ms k v.bv)) := by
  have J2 := J.regWr hr (jMrSt_rcv σ0 rcv.bv x0 pb ms) (Endp.mrIdx k) v
  unfold mrUpd
  by_cases hlt : k < ms.length
  · rw [if_pos hlt, ← v3_jMrSt_set_lt σ0 rcv.bv x0 pb ms v.bv hlt hk4]
    exact J2
  · rw [if_neg hlt]
    have e : Notif.updK (jMrSt σ0 rcv.bv x0 pb ms) rcv.bv (.tcb (Notif.setReg (Endp.withRegs x0
        (Endp.mrRegs x0.tcbArch.tcbContext.userRegs ms)) (Endp.mrIdx k) v.bv)) =
        jMrSt σ0 rcv.bv x0 pb (ms ++ [v.bv]) := by
      cases pb with
      | none => exact Endp.mrStateN_snoc_lt _ _ _ _ _ k (by omega) (by omega)
      | some p => exact Endp.mrState_snoc_lt _ _ _ _ _ _ k (by omega) (by omega)
    rw [← e]
    exact J2

set_option maxHeartbeats 8000000 in
/-- **A buffer word of the message written (appended or overwritten) at `JAtZV3`** (word `k`, `4 ≤ k ≤ |ms| <
120`, FL4 buffer index `i1 = k + 1`). -/
theorem JAtZV3.mrBuf {ms : List Fl4Spec.Word} {p : Fl4Spec.ObjRef}
    (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a (jMrSt σ0 rcv.bv x0 (some p) ms))
    (hr : rcv ∈ Z.T) (hq : Endp.ipcBufOf true x0 = some p) {rw : U64} (hmr : Endp.BufMap Z.B rw p)
    (hrw : rw.bv = p) (i1 : U64) (k : Nat) (hi1 : i1.val = k + 1) (h4 : 4 ≤ k) (hk : k ≤ ms.length)
    (h120 : ms.length < 120) (v : U64) :
    JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D (L.wr s (Endp.fl4BufA rw i1) v) a
      (jMrSt σ0 rcv.bv x0 (some p) (mrUpd ms k v.bv)) := by
  have B := J.z2.zv.base
  obtain ⟨Tr, Cq, hJ⟩ := B.jpl
  have hrT : Z.th rcv = some .tcb := (hJ.tcb rcv).2 (B.zH.1 rcv hr)
  have hwB := hmr i1 (by omega)
  have hk' := jMrSt_rcv σ0 rcv.bv x0 (some p) ms
  obtain ⟨hAp, hObj⟩ := B.bufWordG B.bok hrT hk' (isR := true) hq i1.val (by omega) (b := Endp.fl4BufA rw i1)
    (by rw [fl4BufA_bv, hrw])
  have J2 := J.userWr B.bufPlacedJ hwB hAp hObj v
  unfold mrUpd
  by_cases hlt : k < ms.length
  · rw [if_pos hlt]
    show JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D _ a (Endp.mrState σ0 rcv.bv x0 p (ms.set k v.bv))
    rw [← Endp.v3_mrState_set_ge _ _ _ _ _ _ h4 hlt (by omega), ← hi1]
    exact J2
  · rw [if_neg hlt]
    have hkl : k = ms.length := by omega
    subst hkl
    show JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D _ a (Endp.mrState σ0 rcv.bv x0 p (ms ++ [v.bv]))
    rw [← Endp.mrState_snoc_ge _ _ _ _ _ _ h4 h120, ← hi1]
    exact J2

/-- **A buffer word without a buffer**: the spec state is unchanged. -/
theorem jMrSt_mrUpdN {ms : List Fl4Spec.Word} {k : Nat} (h4 : 4 ≤ k) (hk : k ≤ ms.length) (v : Fl4Spec.Word) :
    jMrSt σ0 rcv.bv x0 none (mrUpd ms k v) = jMrSt σ0 rcv.bv x0 none ms := by
  unfold mrUpd
  by_cases hlt : k < ms.length
  · rw [if_pos hlt]; exact v3_jMrSt_setN_ge _ _ _ _ _ h4
  · rw [if_neg hlt]; exact jMrSt_appendN _ _ _ _ _ (by omega)

set_option maxHeartbeats 8000000 in
/-- **FL4's `set_mr` of word `i ≤ |ms|` at `JAtZV3`**, appended or overwritten, into a receive buffer or without
one (module docstring). -/
theorem setMrJ3 {ms : List Fl4Spec.Word}
    (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a (jMrSt σ0 rcv.bv x0 pb ms))
    (hr : rcv ∈ Z.T) (hq : ∀ p, pb = some p → Endp.ipcBufOf true x0 = some p) {rw : U64} (hb : JBufR Z.B rw pb)
    (i : U64) (hi : i.val ≤ ms.length) (h120 : ms.length < 120) (v : U64) :
    msg.set_mr st s rcv rw i v ⦃ r =>
      JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D r.2 a (jMrSt σ0 rcv.bv x0 pb (mrUpd ms i.val v.bv)) ⦄ := by
  have hN : msg.N_MSG_REGISTERS.val = 4 := by unfold msg.N_MSG_REGISTERS; rfl
  unfold msg.set_mr
  by_cases h4 : i < msg.N_MSG_REGISTERS
  · have hi4 : i.val < 4 := by have := (P1.gt_iff_val).1 h4; omega
    simp only [h4, ↓reduceIte]
    refine WP.spec_bind (Endp.msg_register_spec i hi4) ?_
    rintro r rfl
    refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s rcv _ v) ?_
    rintro s1 rfl
    unfold lift
    apply ok_bind_spec
    simp only [WP.spec_ok]
    exact J.mrReg hr i.val hi4 hi v
  · have hi4 : 4 ≤ i.val := by
      have : ¬ i.val < 4 := fun h' => h4 ((P1.gt_iff_val).2 (by rw [hN]; exact h')); omega
    rw [if_neg h4]
    cases pb with
    | none =>
      have hb' : rw = 0#u64 := hb
      subst hb'
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      rw [jMrSt_mrUpdN hi4 hi]
      exact J
    | some p =>
      obtain ⟨hrw0, hmr, hrw⟩ := hb
      have hb1 : (rw != 0#u64) = true := by simp [hrw0]
      simp only [hb1, ↓reduceIte]
      unfold lift
      apply ok_bind_spec
      refine WP.spec_bind (Endp.msg.buf_set.spec s rw _ v) ?_
      rintro s1 rfl
      apply ok_bind_spec
      simp only [WP.spec_ok]
      have hiv : (core.num.U64.wrapping_add i 1#u64).val = i.val + 1 := by
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      exact J.mrBuf hr (hq p rfl) hmr hrw _ i.val hiv hi4 hi h120 v

/-- `syscall_arg t b 2` reads MR2's register. -/
theorem v3_syscall_arg2 (s : S) (t b : U64) :
    msg.syscall_arg st s t b 2#u64 ⦃ r => r = L.mem s (Endp.regA t (regIdx (Endp.mrIdx 2))) ⦄ := by
  have hN : msg.N_MSG_REGISTERS.val = 4 := by unfold msg.N_MSG_REGISTERS; rfl
  have h2 : (2#u64 : U64).val = 2 := by simp
  have h : (2#u64 : U64) < msg.N_MSG_REGISTERS := (P1.gt_iff_val).2 (by rw [hN, h2]; omega)
  unfold msg.syscall_arg
  simp only [h, ↓reduceIte]
  refine WP.spec_bind (Endp.msg_register_spec 2#u64 (by rw [h2]; omega)) ?_
  rintro r rfl
  rw [h2]
  exact Endp.obj.Tcb.reg.spec s t _

end

end

end Fl4Proofs.P3
