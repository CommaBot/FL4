/-
# P2: `E2E.Once` of `ioport.invocation_ok`'s tree and its continuation (line hpzg, gen 3)

`io_inv_once`: from the post-prefix state, with `IoMidR` for a read set `Rd` without user words, the tree of
`ioport.invocation_ok` followed by a continuation `K` reads each racy word once, from the empty touched set:
the CTable root slot is in `Rd`; the walk is `rab_loop_once`; a found slot (`bits_left = 0`) is read once, and
unless it holds an I/O port cap (then it is in `Rd`, `IoMidR.hIo`) the check answers `false`, whose
continuation `K false` reads nothing racy (`hK0`); an I/O port cap is followed by reads in `Rd` (the IPC buffer
word and slot, register `R10`) and `K true` from the empty touched set (`hK1`). A slot read that ends the walk
with `bits_left ≠ 0` is followed by `K false` alone.

No premises.
-/
import Fl4Proofs.P2.IoOnceA
import Fl4Proofs.P2.IoOnceB
import Fl4Proofs.P2.VmOnce
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.E2E (Once)

theorem ite_ret {X : Type} {c : Prop} [Decidable c] (x y : X) :
    (if c then SProg.ret x else SProg.ret y) = SProg.ret (if c then x else y) := by
  split <;> rfl

section
variable {S A : Type} {st : machine.Store S} [L : LawfulStore st] {ar : machine.Arch A} {Rd User : U64 → Prop}

set_option maxHeartbeats 4000000 in
/-- **`ioport.invocation_ok`'s tree, then `K`** (module docstring). -/
theorem io_inv_once {t cptr : U64} {info : msginfo.MessageInfo} {C : U64 → U64 → Prop} {sl : U64} {x : S}
    (M : IoMidR (L := L) Rd x t C sl) (hU : ∀ q, Rd q → ¬ User q) {K : Bool → SProg Bool} {Wd : Set U64}
    {a : A} {r' : Bool × S × A}
    (h : interp st ar ((R.ioport.invocation_ok t cptr info).sbind K) x a = ok r')
    (hK0 : ∀ Wd' T', Once st ar Rd User Wd' T' (K false) x a)
    (hK1 : ∀ Wd', interp st ar (K true) x a = ok r' → Once st ar Rd User Wd' ∅ (K true) x a) :
    Once st ar Rd User Wd ∅ ((R.ioport.invocation_ok t cptr info).sbind K) x a := by
  have hR0 : ∀ q, Rd q → Rd q ∧ ¬ User q := fun q hq => ⟨hq, hU q hq⟩
  have hW0 : ∀ q, (fun _ => False) q → ¬ User q := fun _ h => h.elim
  unfold R.ioport.invocation_ok at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_liftR h (fun size _ h => ?_)
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_ite h (fun _ h => ?_) (fun _ h => ?_)
  · simp only [SProg.sbind]; exact hK0 _ _
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  unfold R.cspace.lookup_slot at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_liftR h (fun s1 hs1 h => ?_)
  rw [M.hsl] at hs1
  cases ok_inj_ff hs1
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_slotcap h (fun _ => Set.notMem_empty _) (fun _ => q8_not_tch _) (fun root hroot h => ?_)
  rw [tch_empty_of (hR0 _ M.hR0), tch_empty_of (hR0 _ M.hR8)]
  unfold R.cspace.resolve_address_bits at h ⊢
  unfold R.cspace.resolve_address_bits_loop at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine rab_loop_once C (fun p r m y p' r1 gs' g' hp hm hc =>
      ⟨hR0 _ (M.hRc p r m y p' r1 gs' g' hp hm hc).1, hR0 _ (M.hRc p r m y p' r1 gs' g' hp hm hc).2⟩) M.hcl
    (fun e h => ?_) (fun p r m y hp hm h => ?_) (fun q bl hbl T' => ?_) _ _
    (fun p r gs g e => M.hroot p r gs g (by rw [← e]; exact hroot)) h
  · simp only [SProg.sbind]; exact hK0 _ _
  · -- the found slot
    have hb : ¬ ((0#u64 != 0#u64) = true) := by decide
    simp only [SProg.sbind] at h ⊢
    rw [if_neg hb] at h ⊢
    try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
    refine once_slotcap h (fun _ => Set.notMem_empty _) (fun _ => q8_not_tch _) (fun c hc h => ?_)
    by_cases hio : ∃ f l z, c = .IoPort f l z
    · obtain ⟨f, l, z, rfl⟩ := hio
      obtain ⟨h0, h8⟩ := M.hIo p r m y f l z hp hm hc
      rw [tch_empty_of (hR0 _ h0), tch_empty_of (hR0 _ h8)]
      simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind] at h ⊢
      -- the IPC buffer
      refine once_gstep (R0 := Rd) (W0 := fun _ => False) hR0 hW0 (R.msg.lookup_ipc_buffer_nz _ _) h
        (fun r h1 => ?_) (fun r h1 hk Wd' _ => ?_)
      · obtain ⟨bsl, hbsl⟩ := buffer_slot_ok t
        rw [R.msg.lookup_ipc_buffer_eq] at h1 ⊢
        rw [msg.lookup_ipc_buffer.guard (gS := guard st Rd (fun _ => False)) x false t hbsl M.ib (M.bs bsl hbsl).1
          (M.bs bsl hbsl).2]
        exact h1
      replace h := hk
      rw [R.msg.lookup_ipc_buffer_eq] at h1
      obtain ⟨buf, -, rfl⟩ := bind_shape h1
      dsimp only at h ⊢
      try simp only [SProg.blk, ite_ret, SProg.sbind] at h ⊢
      refine once_liftR h (fun b _ h => ?_)
      try simp only [SProg.blk, ite_ret, SProg.sbind] at h ⊢
      refine once_ite h (fun _ h => ?_) (fun _ h => ?_)
      · simp only [SProg.sbind]; exact hK0 _ _
      try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
      refine once_gstep (R0 := Rd) (W0 := fun _ => False) hR0 hW0 (R.msg.syscall_arg_nz _ _ _) h
        (fun r h1 => ?_) (fun r h1 hk Wd2 _ => ?_)
      · rw [R.msg.syscall_arg_eq] at h1 ⊢
        rw [msg.syscall_arg.guard_lt (gS := guard st Rd (fun _ => False)) x t buf 0#u64 zero_lt_nmr
          (fun r hr => by rw [msg_register_zero] at hr; cases ok_inj_ff hr; exact M.r10)]
        exact h1
      replace h := hk
      rw [R.msg.syscall_arg_eq] at h1
      obtain ⟨i1, -, rfl⟩ := bind_shape h1
      dsimp only at h ⊢
      try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
      refine once_liftR h (fun r2 _ h => ?_)
      try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
      refine once_liftR h (fun b' _ h => ?_)
      cases b'
      · exact hK0 _ _
      · exact hK1 _ h
    · cases c <;> (try exact absurd ⟨_, _, _, rfl⟩ hio) <;> (simp only [SProg.sbind]) <;> exact hK0 _ _
  · have hb : (bl != 0#u64) = true := by simpa using hbl
    simp only [SProg.sbind]
    rw [if_pos hb]
    simp only [SProg.sbind]
    exact hK0 _ _

end

end Fl4Proofs.P2.PathObl
