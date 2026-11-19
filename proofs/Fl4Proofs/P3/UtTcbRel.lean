/-
P3 (DESIGN.md §9), untyped: **a new TCB and `default_tcb`** (handoff/utj.md
"uttypes", ut37; l4v `retype_region` of `TCBObject`s, `default_tcb` with
`new_context`).

* `winZero_tcbF`: after a TCB retype (`WinZero` with the creation words
  `InT`), a new TCB's words in `[F, F + 272)` (state, IPC fields, fault,
  domain .. scheduler fields, links) are zero, but the domain word and the
  debug links;
* `TcbRel` with `default_tcb d` does NOT follow yet: FL4's `init_context`
  writes CS = 0x33, SS = 0x2b (Linux selector layout, l4h 0028), while
  Fl4Spec's `new_context` has l4v's `selCS3` = 0x2b, `selDS3` = 0x33
  (`gdtCs3` = 5, `gdtDs3` = 6); `TcbRel.regs` compares every register
  (handoff/utj.md ut37: needs an owner decision).
-/
import Fl4Proofs.P3.UtTcbRetC
import Fl4Proofs.P3.UtTcbSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

/-- **A new TCB's fields after a TCB retype are zero**, but the domain word
and the debug links (`InT`'s exceptions in `[F, F + 272)`). -/
theorem winZero_tcbF {m : U64 → U64} {A win : Nat} {T : Prop} (hWZ : WinZero m A 4096 win T)
    (hfit : A + win * 4096 ≤ 2 ^ 64) {j : Nat} (hj : j < win) (w : U64) (hw : P1.Aligned w)
    (h1 : (bT A j).val + 3328 ≤ w.val) (h2 : w.val < (bT A j).val + 3600) (h3 : w.val ≠ (bT A j).val + 3432)
    (h4 : w.val ≠ (bT A j).val + 3576) (h5 : w.val ≠ (bT A j).val + 3584) : m w = 0#u64 := by
  have hb := bT_v hj hfit
  rw [hb] at h1 h2 h3 h4 h5
  have hjk : (j + 1) * 4096 ≤ win * 4096 := Nat.mul_le_mul_right _ hj
  rcases hWZ w hw (by omega) (by omega) with h | ⟨-, j', hj', hin⟩
  · exact h
  · exfalso
    have e : (⟨BitVec.ofNat 64 (A + j' * 4096)⟩ : U64).val = A + j' * 4096 := bT_v hj' hfit
    unfold InT at hin
    rw [e] at hin
    obtain ⟨g1, g2, g3, g4⟩ := hin
    rcases Nat.lt_trichotomy j' j with hl | rfl | hl
    · omega
    · omega
    · omega


end

end Fl4Proofs.P3
