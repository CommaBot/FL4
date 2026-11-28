/-
P2 (tmofr, part C): **vexit's `htk` discharged** by the shared timeout-fault
lemma (`tmoIbVI_of`, P2/TmoFrB).

* `TmoCapW s t`: thread `t`'s timeout handler cap, decoded from its two slot
  words (TCB offsets 128, 136), is typed. `TmoCapW.slot`: the cap read
  `handle_timeout` does. `tmoIbVI_ofW`: `tmoIbVI_of` with the cap fact at the
  budget check's start only (`ChgW` writes miss the TCB's cap slots).
* **`vexit_tk`**: `htk` (`update_timestamp ⦃ vcpu.check ⦃ TmoIbVI ⦄ ⦄`) from
  facts at the VM exit's entry: `EntryInv`, `BufAt`, `PendAt`, `IrqOff`, the
  current thread not queued (`hnq`), the idle thread not runnable (`hni`) and
  `TmoCapW` of the current thread. `update_timestamp` writes node words only;
  `vcpu.check` writes (`VckW.frames`) only the current thread's register words
  and state word, so the queue word, the idle thread's state and the cap slot
  words reach the budget check (on `RUNNING_VM` the current thread is runnable,
  hence not the idle thread).
* **`syscall.handle_vcpu_exit.entryK`**, **`vm_timer_local.entryK`**: `entryI`
  with the run premise `htk` replaced by the entry facts `hnq`, `hni` [P] and
  `hcw` [P].
* `tmoCapW_of_JAtZ`: `hcw` at a P3 `JAtZ` state (`JAtZ.timeoutTyped` at the
  current thread's slot 4).
* **`syscall.handle_vcpu_exit.entryJ4`**, **`vm_timer_local.entryJ4`**: from
  every reachable entry state (`JReachU17`), premises `kernel_entry_domInvU29`'s
  and two facts about the entry state itself, no run premise: `hnq` [P] (the
  current thread's `Q_QUEUED` bit clear: P3 `JAtZ.curBits` from the spec's
  `SInvC.ctQ`) and `hni` [P] (the idle thread's state word not runnable: the
  spec's valid-idle invariant).
-/
import Fl4Proofs.P2.FootN5
import Fl4Proofs.P1.QueueFootS
import Fl4Proofs.P2.VcpuExitI
open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace Fl4Proofs.P2.Stall
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

theorem tmo_slot (t : U64) :
    obj.Tcb.slot t layout.tcb.SLOT_TIMEOUT_HANDLER = ok (core.num.U64.wrapping_add t 128#u64) := by
  rw [tcb_slot_val]; unfold slotIdx
  have e : core.num.U64.wrapping_mul layout.tcb.SLOT_TIMEOUT_HANDLER 32#u64 = 128#u64 := by
    apply UScalar.eq_of_val_eq
    simp [layout.tcb.SLOT_TIMEOUT_HANDLER, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
  rw [e]

theorem tmoSlot8_eq (t : U64) :
    core.num.U64.wrapping_add (core.num.U64.wrapping_add t 128#u64) 8#u64 = core.num.U64.wrapping_add t 136#u64 := by
  apply UScalar.eq_of_val_eq
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
  try omega

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}

/-- Thread `t`'s timeout handler cap, decoded from its slot's two words at `s`, is typed. -/
def TmoCapW (st : machine.Store S) [L : LawfulStore st] (H : Heap) (Rp Nt : Set U64) (s : S) (t : U64) : Prop :=
  capability.Cap.decode (L.mem s (core.num.U64.wrapping_add t 128#u64))
    (L.mem s (core.num.U64.wrapping_add t 136#u64)) ⦃ c => CapTyped H Rp Nt c ⦄

theorem TmoCapW.slot {s : S} {t : U64} (h : TmoCapW st H Rp Nt s t) :
    obj.Tcb.slot t layout.tcb.SLOT_TIMEOUT_HANDLER ⦃ sl =>
      obj.Slot.cap st sl s ⦃ c => CapTyped H Rp Nt c ⦄ ⦄ := by
  rw [tmo_slot, WP.spec_ok, slot_cap_dec, tmoSlot8_eq]; exact h

theorem TmoCapW.of_eq {s s' : S} {t : U64} (h : TmoCapW st H Rp Nt s t)
    (e1 : L.mem s' (core.num.U64.wrapping_add t 128#u64) = L.mem s (core.num.U64.wrapping_add t 128#u64))
    (e2 : L.mem s' (core.num.U64.wrapping_add t 136#u64) = L.mem s (core.num.U64.wrapping_add t 136#u64)) :
    TmoCapW st H Rp Nt s' t := by
  unfold TmoCapW; rw [e1, e2]; exact h

variable {A : Type _} {ar : machine.Arch A}

end

/-! ## From a reachable entry state -/

open Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P3.Vs Fl4Proofs.P3.SInvR.G4 Fl4Proofs.P3.SInvR.G5

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

theorem slotOf4 (t : U64) : core.num.U64.wrapping_add t 128#u64 = slotOf t 4 := by
  apply UScalar.eq_of_val_eq
  show (core.num.U64.wrapping_add t 128#u64).val = (t.bv + BitVec.ofNat 64 4 * 32#64).toNat
  rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
  try omega

end

end Fl4Proofs.P2.Stall
