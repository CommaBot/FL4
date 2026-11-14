/-
P3 (DESIGN.md §9), endpoints: writing a register of a saved user context.

`write_reg_rel`: FL4's `set_reg t (regIdx r) v` is related to the spec's
`as_user t (setRegister r v)` (`setReg`): one register word changes, the
thread state does not.
-/
import Fl4Proofs.P3.EpBlock
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {T E R : Set U64} {B : Set (U64 × Fl4Spec.Word)}

theorem setReg_regs (x : Fl4Spec.Tcb) (r : Fl4Spec.Register) (v : Fl4Spec.Word) :
    (setReg x r v).tcbArch.tcbContext.userRegs = Function.update x.tcbArch.tcbContext.userRegs r v := rfl

theorem regA_ne {t : U64} (ht : TcbAddr t) {r r' : Fl4Spec.Register} (h : r' ≠ r) :
    (regA t (regIdx r')).val ≠ (regA t (regIdx r)).val := by
  rw [regA_val ht (regIdx_lt r'), regA_val ht (regIdx_lt r)]
  intro e
  exact h (regIdx_inj (by omega))

/-- A TCB with one register changed. -/
theorem TcbRelE.set_reg {m m' : U64 → U64} {t : U64} {x : Fl4Spec.Tcb} (ht : TcbAddr t) (h : TcbRelE R m t x)
    (r : Fl4Spec.Register) (v : U64)
    (hA : Agree m m' (fun b => TF t b ∧ b.val ≠ (regA t (regIdx r)).val)) (hv : m' (regA t (regIdx r)) = v) :
    TcbRelE R m' t (setReg x r v.bv) := by
  have g : ∀ {b}, Aligned b ∧ TF t b → b.val ≠ (regA t (regIdx r)).val → m' b = m b :=
    fun hb hne => hA _ hb.1 ⟨hb.2, hne⟩
  have hr := regA_val ht (regIdx_lt r)
  have := regIdx_lt r
  refine ⟨?_, fun e he => ?_, fun e d he => ?_, fun e rr d he => ?_, fun rr he => ?_, fun r' => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g (a_st ht) (by rw [val_st ht]; omega)]; exact h.st
  · rw [g (a_blk ht) (by rw [val_blk ht]; omega)]; exact h.blk e he
  · rw [g (a_badge ht) (by rw [val_badge ht]; omega), g (a_flags ht) (by rw [val_flags ht]; omega)]
    exact h.send e d he
  · rw [g (a_reply ht) (by rw [val_reply ht]; omega)]; exact h.recv e rr d he
  · rw [g (a_reply ht) (by rw [val_reply ht]; omega)]; exact h.reply rr he
  · rw [setReg_regs]
    by_cases e : r' = r
    · subst e; rw [hv]; simp
    · rw [g (a_reg ht r') (regA_ne ht e), Function.update_of_ne e]; exact h.regs r'
  · rw [g (a_prio ht) (by rw [val_prio ht]; omega)]; exact h.prio
  · rw [g (a_fault ht) (by rw [val_fault ht]; omega)]; exact h.fault0
  · rw [g (a_fault ht) (by rw [val_fault ht]; omega)]; exact h.faultT
  · rw [g (a_bound ht) (by rw [val_bound ht]; omega)]; exact h.bound
  · exact h.faultR.congr (g (a_fault ht) (by rw [val_fault ht]; omega)) (g (a_fw0 ht) (by rw [val_fw0 ht]; omega)) (g (a_fw1 ht) (by rw [val_fw1 ht]; omega)) (g (a_lf ht) (by rw [val_lf ht]; omega)) (g (a_lf0 ht) (by rw [val_lf0 ht]; omega)) (g (a_lf1 ht) (by rw [val_lf1 ht]; omega)) (g (a_fw2 ht) (by rw [val_fw2 ht]; omega))

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

theorem twf_reg {t : U64} (ht : TcbAddr t) (r : Fl4Spec.Register) : TWF t (regA t (regIdx r)) := by
  have hr := regA_val ht (regIdx_lt r)
  have := regIdx_lt r
  exact ⟨by omega, by rw [hr]; unfold TWOffN; omega⟩

/-- **Writing register `r` of the TCB at `t`.** -/
theorem write_reg_rel (hP : EPlaced T E R B) (s : S) (σ : Fl4Spec.State Unit)
    (hR : EpStateRel T E R B (L.mem s) σ) {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb}
    (hk : σ.kheap t.bv = some (.tcb x)) (r : Fl4Spec.Register) (v : U64) :
    EpStateRel T E R B (L.mem (L.wr s (regA t (regIdx r)) v)) (updK σ t.bv (.tcb (setReg x r v.bv))) ∧
      WritesIn st s (L.wr s (regA t (regIdx r)) v) (EWrite T E R B) ∧
      EpStep σ (updK σ t.bv (.tcb (setReg x r v.bv))) := by
  have hta := hP.tcb t ht
  have hx := hR.at_tcb ht hk
  have ha := a_reg hta r
  have hag := agree_wr (L := L) (s := s) (v := v) ha.1
  refine ⟨hR.upd_tcb hP ht _ (hag.mono fun b hb => tf_ne_of hb.2 ha.2)
    (Or.inr ⟨hag _ (a_st hta).1 (by show (tStA t).val ≠ _; rw [val_st hta, regA_val hta (regIdx_lt r)]; have := regIdx_lt r; omega),
      hag _ (a_blk hta).1 (by show (tBlockA t).val ≠ _; rw [val_blk hta, regA_val hta (regIdx_lt r)]; have := regIdx_lt r; omega)⟩)
    (hx.set_reg hta r v (hag.mono fun b hb => hb.2) (rd_wr_eq ha.1)), wr_ewrite ht (twf_reg hta r) ha.1 s v,
    EpStep.tcb hk x.tcbState _⟩

end

end

end

end Fl4Proofs.P3.Endp
