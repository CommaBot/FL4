/-
P3 (DESIGN.md §9), IPC: **the decode of the IPC caps** for
`handle_invocation_refinesMX` (HandleTopX): `DecOKDMX X` for an endpoint
cap (`send_ipc`) and a notification cap (`send_signal`), from the leaves
`set_thread_state Restart` then `send_ipc` / `send_signal` against the spec's
`set_thread_state Restart` then `send_ipc` / `send_signal` (the IPC theorems
on `IpcRel` for the cases they cover). Without the send right, the decode
is `InvalidCapability 0`, the state unchanged. The spec's result of both
invocations is `[]`.
-/
import Fl4Proofs.P3.IpcRecvTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- The spec's decode of an endpoint cap. -/
theorem specDec_endpoint (fp : Bool) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (p b : U64) (sd rv g gr : Bool) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) (σ : Fl4Spec.State Unit) :
    (specDec fp slbl args ci sl (.Endpoint p b sd rv g gr) excaps buffer).run σ =
      if sd then ({(.ok (.invokeEndpoint p.bv b.bv g gr), σ)}, False)
      else ({(.error (.invalidCapability 0), σ)}, False) := by
  unfold specDec Fl4Spec.fl4DecodeInvocation
  simp only [absCap]
  cases sd <;> cases g <;> cases gr <;>
    simp [rightsOf, Fl4Spec.AllowSend, Fl4Spec.NonDetE.returnOk, Fl4Spec.NonDetE.throwError] <;> rfl

/-- The spec's decode of a notification cap. -/
theorem specDec_notification (fp : Bool) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (p b : U64) (sd rv : Bool) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) (σ : Fl4Spec.State Unit) :
    (specDec fp slbl args ci sl (.Notification p b sd rv) excaps buffer).run σ =
      if sd then ({(.ok (.invokeNotification p.bv b.bv), σ)}, False)
      else ({(.error (.invalidCapability 0), σ)}, False) := by
  unfold specDec Fl4Spec.fl4DecodeInvocation
  simp only [absCap]
  cases sd <;> simp [rightsOf, Fl4Spec.AllowSend, Fl4Spec.NonDetE.returnOk, Fl4Spec.NonDetE.throwError] <;> rfl

/-- The perform of an endpoint invocation, from an outcome of `send_ipc`. -/
theorem mem_perform_endpoint {σ1 : Fl4Spec.State Unit} {blk call don : Bool} {ep b : Fl4Spec.Word} {g gr : Bool}
    {z : Unit × Fl4Spec.State Unit}
    (hz : z ∈ (Fl4Spec.sendIpc (Z := Unit) blk call b g gr don σ1.curThread ep σ1).1) :
    ((.ok [], z.2) : Except Unit (List Fl4Spec.Data) × _) ∈
      ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeEndpoint ep b g gr)).run σ1).1 := by
  unfold Fl4Spec.fl4PerformInvocation Fl4Spec.withoutPreemption
  refine mem_liftE (x := ([], z.2)) ?_
  exact mem_bind_nd (x := (σ1.curThread, σ1)) rfl (mem_bind_nd hz rfl)

/-- The perform of a notification invocation, from an outcome of `send_signal`. -/
theorem mem_perform_notification {σ1 : Fl4Spec.State Unit} {blk call don : Bool} {n b : Fl4Spec.Word}
    {z : Unit × Fl4Spec.State Unit} (hz : z ∈ (Fl4Spec.sendSignal (Z := Unit) n b σ1).1) :
    ((.ok [], z.2) : Except Unit (List Fl4Spec.Data) × _) ∈
      ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeNotification n b)).run σ1).1 := by
  unfold Fl4Spec.fl4PerformInvocation Fl4Spec.withoutPreemption
  exact mem_bindE_ok (a := ()) (s' := z.2) (mem_liftE (x := ((), z.2)) hz) (mem_returnOk _)

/-- **An endpoint cap, for `handle_invocation_refinesMX`**: `DecOKDMX X`,
from the leaf `set_thread_state Restart` then `send_ipc`. -/
theorem decode_endpointDMX (X : S → A → Fl4Spec.State Unit → Prop) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl length slot : U64) (p b : U64) (sd rv g gr : Bool) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hX0 : X s ar σ) {σ1 : Fl4Spec.State Unit}
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (hsend : sd = true → (do
        let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
        let (s2, a1) ← endpoint.send_ipc st arI s1 ar blk call b g gr don ct p
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1)) ⦃ r => r.1 = .Ok () ∧
      ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) blk call b.bv g gr don σ1.curThread p.bv σ1).1,
        RelTopM (L := L) r.2.1 z.2 ∧ X r.2.1 r.2.2 z.2 ⦄) :
    DecOKDMX (L := L) arI X s ar σ lbl length slot (.Endpoint p b sd rv g gr) blk call don fp buf extra slbl args
      ci sl excaps buffer := by
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases sd
  · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    refine Or.inl ⟨_, rfl, rfl, ⟨.invalidCapability 0, by rw [specDec_endpoint]; rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, hX0⟩
  simp only [↓reduceIte]
  refine WP.spec_mono (hsend rfl) ?_
  rintro res ⟨hres, z, hz, ⟨th', G', hP', hCR', hFI', hDR', hMO'⟩, hXz⟩
  refine Or.inr ⟨_, DecOut.of_eq (by rw [specDec_endpoint]; rfl), σ1, hst, (.ok [], z.2), mem_perform_endpoint hz,
    ⟨th', G', Or.inl ⟨hres, rfl⟩, hP', hCR', hFI', hDR', hMO'⟩, hXz⟩

/-- **A notification cap, for `handle_invocation_refinesMX`**: `DecOKDMX X`,
from the leaf `set_thread_state Restart` then `send_signal`. -/
theorem decode_notificationDMX (X : S → A → Fl4Spec.State Unit → Prop) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl length slot : U64) (p b : U64) (sd rv : Bool) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hX0 : X s ar σ) {σ1 : Fl4Spec.State Unit}
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (hsend : sd = true → (do
        let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
        let (s2, a1) ← notification.send_signal st arI s1 ar p b
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1)) ⦃ r => r.1 = .Ok () ∧
      ∃ z ∈ (Fl4Spec.sendSignal (Z := Unit) p.bv b.bv σ1).1,
        RelTopM (L := L) r.2.1 z.2 ∧ X r.2.1 r.2.2 z.2 ⦄) :
    DecOKDMX (L := L) arI X s ar σ lbl length slot (.Notification p b sd rv) blk call don fp buf extra slbl args
      ci sl excaps buffer := by
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases sd
  · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    refine Or.inl ⟨_, rfl, rfl, ⟨.invalidCapability 0, by rw [specDec_notification]; rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, hX0⟩
  simp only [↓reduceIte]
  refine WP.spec_mono (hsend rfl) ?_
  rintro res ⟨hres, z, hz, ⟨th', G', hP', hCR', hFI', hDR', hMO'⟩, hXz⟩
  refine Or.inr ⟨_, DecOut.of_eq (by rw [specDec_notification]; rfl), σ1, hst, (.ok [], z.2), mem_perform_notification hz,
    ⟨th', G', Or.inl ⟨hres, rfl⟩, hP', hCR', hFI', hDR', hMO'⟩, hXz⟩

/-- The spec's decode of a reply cap. -/
theorem specDec_reply (fp : Bool) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (p : U64) (g : Bool) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) (σ : Fl4Spec.State Unit) :
    (specDec fp slbl args ci sl (.Reply p g) excaps buffer).run σ = ({(.ok (.invokeReply p.bv g), σ)}, False) := by
  unfold specDec Fl4Spec.fl4DecodeInvocation
  simp only [absCap]
  cases g <;> simp [replyRights, Fl4Spec.NonDetE.returnOk]

/-- The perform of a reply invocation, from an outcome of `do_reply_transfer`. -/
theorem mem_perform_reply {σ1 : Fl4Spec.State Unit} {blk call don : Bool} {r : Fl4Spec.ObjRef} {g : Bool}
    {z : Unit × Fl4Spec.State Unit}
    (hz : z ∈ (Fl4Spec.doReplyTransfer (Z := Unit) σ1.curThread r g σ1).1) :
    ((.ok [], z.2) : Except Unit (List Fl4Spec.Data) × _) ∈
      ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeReply r g)).run σ1).1 := by
  unfold Fl4Spec.fl4PerformInvocation
  refine mem_liftE (x := ([], z.2)) ?_
  exact mem_bind_nd (x := (σ1.curThread, σ1)) rfl (mem_bind_nd hz rfl)

/-- **A reply cap, for `handle_invocation_refinesMX`**: `DecOKDMX X`, from
the leaf `set_thread_state Restart` then `do_reply_transfer`. -/
theorem decode_replyDMX (X : S → A → Fl4Spec.State Unit → Prop) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl length slot : U64) (p : U64) (g : Bool) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    {σ1 : Fl4Spec.State Unit}
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (hrep : (do
        let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
        let (s2, a1) ← ipc.do_reply_transfer st arI s1 ar ct p g
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1)) ⦃ r => r.1 = .Ok () ∧
      ∃ z ∈ (Fl4Spec.doReplyTransfer (Z := Unit) σ1.curThread p.bv g σ1).1,
        RelTopM (L := L) r.2.1 z.2 ∧ X r.2.1 r.2.2 z.2 ⦄) :
    DecOKDMX (L := L) arI X s ar σ lbl length slot (.Reply p g) blk call don fp buf extra slbl args
      ci sl excaps buffer := by
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  refine WP.spec_mono hrep ?_
  rintro res ⟨hres, z, hz, ⟨th', G', hP', hCR', hFI', hDR', hMO'⟩, hXz⟩
  exact Or.inr ⟨_, DecOut.of_eq (by rw [specDec_reply]), σ1, hst, (.ok [], z.2), mem_perform_reply hz,
    ⟨th', G', Or.inl ⟨hres, rfl⟩, hP', hCR', hFI', hDR', hMO'⟩, hXz⟩

end

end

end Fl4Proofs.P3
