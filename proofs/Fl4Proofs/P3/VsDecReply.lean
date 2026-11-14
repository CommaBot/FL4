/-
P3 (DESIGN.md §9), VSpace: **the frame labels that reply inside the
decode** (`TopPostR`/`DecOKR` of HandleTop, as IO port `In` called).

* `decode_invocation_frame_getaddr`: `GetAddress`. FL4 restarts the thread
  and replies the frame's physical address itself; the reply is the named
  hypothesis `GetAddrHyp` (the Ep side: `set_mr`, `set_msg_info`,
  `Running`, against the spec's success tail of `[addrFromPPtr p]`).
-/
import Fl4Proofs.P3.HandleTop
import Fl4Proofs.P3.VsDecFrame
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Vs

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The `GetAddress` reply** (for the IPC proofs): FL4's `Restart` and
`reply1` of the physical address, against the spec's restart and success
tail of `[addrFromPPtr p]`: FL4 is done, its thread no longer `Restart`,
and the spec has an outcome related to FL4's state. -/
def GetAddrHyp (s : S) (σ : Fl4Spec.State Unit) (ar : A) (ct p : U64) (call : Bool) : Prop :=
  (do
    let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
    let s2 ← vspace.reply1 st s1 ct call (core.num.U64.wrapping_sub p layout.PPTR_BASE)
    ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, ar)) ⦃ res =>
    res.1 = .Ok () ∧ L.mem res.2.1 (stA ct) ≠ sched.TS_RESTART ∧ ∀ σ1,
      Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) →
      ∃ z ∈ (specTail call ct.bv [Fl4Spec.addrFromPPtr p.bv] σ1).1, RelTop (L := L) res.2.1 z.2 ⦄

/-- **Frame `GetAddress`** (`DecOKR`, the reply `GetAddrHyp`). -/
theorem decode_invocation_frame_getaddr (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : FrameLabel lbl slbl) (hl : lbl = fl4_abi.label.X86PageGetAddress)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hcur : σ.curThread = ct.bv) {tcb : Fl4Spec.Tcb} (hkt : σ.kheap ct.bv = some (.tcb tcb))
    {p : U64} {sz : capability.FrameSize} {rt asid va : U64} {d m : Bool}
    (slot : U64) (blk call don fp : Bool) (hga : GetAddrHyp (L := L) s σ ar ct p call) (extra : Aeneas.Std.Array obj.Slot 3#usize) (args : List Fl4Spec.Data)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) :
    DecOKR (L := L) arI s ar σ lbl length slot (.Frame p sz rt d m asid va) blk call don fp buf extra slbl args ci sl
      excaps buffer ct := by
  subst hl
  unfold DecOKR syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  have n1 : ¬ fl4_abi.label.X86PageGetAddress = fl4_abi.label.X86PageMap := by
    unfold fl4_abi.label.X86PageGetAddress fl4_abi.label.X86PageMap; decide
  have n2 : ¬ fl4_abi.label.X86PageGetAddress = fl4_abi.label.X86PageUnmap := by
    unfold fl4_abi.label.X86PageGetAddress fl4_abi.label.X86PageUnmap; decide
  have n3 : ¬ fl4_abi.label.X86PageGetAddress = fl4_abi.label.X86PageDeriveSubframe := by
    unfold fl4_abi.label.X86PageGetAddress fl4_abi.label.X86PageDeriveSubframe; decide
  have n4 : ¬ fl4_abi.label.X86PageGetAddress = fl4_abi.label.X86PageTestAndClearAccessed := by
    unfold fl4_abi.label.X86PageGetAddress fl4_abi.label.X86PageTestAndClearAccessed; decide
  have hspec : specDec fp slbl args ci sl (.Frame p sz rt d m asid va) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeArchObject
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4ArchInvocation.spec (Fl4Spec.archDecodeInvocation (Z := Unit) slbl
          args ci sl (frameACapG ⟨p, sz, rt, d, m, asid, va⟩) excaps)) := by
    show Fl4Spec.NonDetE.liftME _ (Fl4Spec.fl4ArchDecodeInvocation (Z := Unit) slbl args ci sl
      (frameACapG ⟨p, sz, rt, d, m, asid, va⟩) excaps) = _
    unfold Fl4Spec.fl4ArchDecodeInvocation frameACapG; dsimp only
    rw [if_neg (fun h => n3 (hlbl.ds h)), if_neg (fun h => n4 (hlbl.tac h))]
  rw [hspec]
  unfold vspace.decode
  rw [hct]; simp only [bind_ok]
  unfold vspace.decode_frame
  simp only [vspace.as_frame, bind_ok, n1, n2, ↓reduceIte]
  rw [hct]; simp only [bind_ok, layout.paddr]
  refine WP.spec_mono hga ?_
  rintro res ⟨h1, hne, hall⟩
  obtain ⟨σ1, hst, -⟩ := setThreadState_eq σ ct.bv tcb hkt .restart
  obtain ⟨z, hz, hRT⟩ := hall σ1 hst
  have hdec := decodeGetAddr_eq (hlbl.ga rfl) args sl d p.bv (vmRightsOf rt) (if m then .vmVSpaceMap else .vmNoMap)
    (frameSizeOf sz) (if m then some (asid.bv, va.bv) else none) excaps σ
  refine Or.inr ⟨h1, hne, _, DecOut.of_eq (run_liftME_ok (run_liftME_ok hdec)), σ1, by rw [hcur]; exact hst,
    [Fl4Spec.addrFromPPtr p.bv], σ1, ?_, z, hz, hRT⟩
  exact mem_liftE (ε := Unit) (x := ([Fl4Spec.addrFromPPtr p.bv], σ1)) rfl

end

end

end Fl4Proofs.P3
