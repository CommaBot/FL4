/-
# P2: guarded-store lemma for `ioport.invocation_ok` (line p2io)

Split from `P2/AccessIo.lean` (elaboration memory).

* `ioport.invocation_ok.guard`, run-relative: the CSpace walk, the found slot,
  the IPC buffer word and slot, register `R10`.

Premises: none.
-/
import Fl4Proofs.P2.AccessIo
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1

section
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} [L : LawfulStore st]

theorem zero_lt_nmr : (0#u64 : U64) < msg.N_MSG_REGISTERS := by rw [n_msg_regs]; decide

theorem one_lt_nmr : (1#u64 : U64) < msg.N_MSG_REGISTERS := by rw [n_msg_regs]; decide

/-- **`ioport.invocation_ok`**, run-relative: the CSpace walk (`lookup_slot`'s
hypotheses), the found slot, the IPC buffer word and slot, register `R10`. -/
theorem ioport.invocation_ok.guard {s : S} {t cptr : U64} {info : msginfo.MessageInfo} {b : Bool}
  (C : U64 → Prop) {sl : U64}
  (hsl : obj.Tcb.slot t layout.tcb.SLOT_CTABLE = ok sl)
  (hR0 : R sl) (hR8 : R (core.num.U64.wrapping_add sl 8#u64))
  (hRc : ∀ p off p' r' gs' g', C p → obj.Slot.cap st (cnSlot p off) s = ok (.CNode p' r' gs' g') →
    R (cnSlot p off) ∧ R (core.num.U64.wrapping_add (cnSlot p off) 8#u64))
  (hcl : ∀ p off p' r' gs' g', C p → obj.Slot.cap st (cnSlot p off) s = ok (.CNode p' r' gs' g') → C p')
  (hroot : ∀ p r gs g, obj.Slot.cap st sl s = ok (.CNode p r gs g) → C p)
  (hRf : ∀ x, cspace.lookup_slot st s t cptr = ok (.Ok x) →
    R x.slot ∧ R (core.num.U64.wrapping_add x.slot 8#u64))
  (hib : R (core.num.U64.wrapping_add t 3512#u64))
  (hbs : ∀ bsl, obj.Tcb.slot t layout.tcb.SLOT_BUFFER = ok bsl →
    R bsl ∧ R (core.num.U64.wrapping_add bsl 8#u64))
  (hr10 : R (regA t layout.reg.R10))
  (h : ioport.invocation_ok st s t cptr info = ok b) :
  ioport.invocation_ok (PathObl.guard st R W) s t cptr info = ok b := by
  have n0 := zero_lt_nmr
  unfold ioport.invocation_ok at h ⊢
  revert h
  refine tr_bind_same (fun size _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  refine tr_bind (fun res hres _ => cspace.lookup_slot.guard C hsl hR0 hR8 hRc hcl hroot
    (fun x e => hRf x (e ▸ hres)) hres) (fun res hres => ?_)
  cases res with
  | Err e => exact fun h => h
  | Ok r1 =>
    obtain ⟨h0, h8⟩ := hRf r1 hres
    dsimp only
    rw [obj.Slot.cap.guard _ s h0 h8]
    refine tr_bind_same (fun c _ => ?_)
    cases c <;> try exact fun h => h
    obtain ⟨bsl, hbsl⟩ := buffer_slot_ok t
    rw [msg.lookup_ipc_buffer.guard s false t hbsl hib (hbs bsl hbsl).1 (hbs bsl hbsl).2]
    have e : ∀ bf, msg.syscall_arg (PathObl.guard st R W) s t bf 0#u64 = msg.syscall_arg st s t bf 0#u64 :=
      fun bf => msg.syscall_arg.guard_lt s t bf 0#u64 n0
        (fun r hr => by rw [msg_register_zero] at hr; cases ok_inj_ff hr; exact hr10)
    simp only [e]
    exact fun h => h

end

end Fl4Proofs.P2.PathObl
