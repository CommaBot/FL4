/-
P3 (line stpost, generation 6): **the Thread cap's decode at the label `TCBSetTimer`, stable ghosts, with
`MR`** (`decode_threadTmJSt`; split from StPostTmInv, whose `handle_invocation_threadTmJSt` uses it as
the cap case of StPostInv's `refinesMXPF`). The canonical label (`tcb_canon`, `XCapP.lbl_congr`),
`xcapP_of_tcb` of StPostTmLeaf's `tcb_set_timerJSt` (never preempted: `thread_noPre_of`), `MR` by
`XCapP.mrG` with `MKD.decode_thread_nonins` / `perfF_tcbN`. No premise added.
-/
import Fl4Proofs.P3.StPostTmLeaf
import Fl4Proofs.P3.StPostInv
import Fl4Proofs.P3.XTopJointKEntry40
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section StTmDec
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

theorem setTimer_nonIns : TcbNonIns fl4_abi.label.TCBSetTimer := by
  unfold TcbNonIns fl4_abi.label.TCBSetTimer fl4_abi.label.TCBSetEPTRoot fl4_abi.label.TCBConfigure
    fl4_abi.label.TCBSetSchedParams fl4_abi.label.TCBSetIPCBuffer fl4_abi.label.TCBSetSpace
    fl4_abi.label.TCBSetTimeoutEndpoint
  decide

theorem setTimer_l5 : fl4_abi.label.TCBSetTimer.val ≠ 5 ∧ fl4_abi.label.TCBSetTimer.val ≠ 8 ∧
    fl4_abi.label.TCBSetTimer.val ≠ 9 ∧ fl4_abi.label.TCBSetTimer.val ≠ 10 ∧
    fl4_abi.label.TCBSetTimer.val ≠ 11 := by
  simp [fl4_abi.label.TCBSetTimer]

/-- The SetTimer label's spec labels. -/
theorem setTimer_lbls : tcbLabelOf fl4_abi.label.TCBSetTimer = .invalidInvocation ∧
    tcbExtOf fl4_abi.label.TCBSetTimer = some .setTimer := by
  simp [tcbLabelOf, tcbExtOf]

/-- (stpost) The SetTimer arm at stable ghosts, never preempted (`TcbOKXP`). -/
theorem decode_threadTmOK (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z] (hni : Entered σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (is_call can_donate : Bool) (length buf : U64)
    (argsU : List U64) (hLen : length.val = argsU.length)
    (hArgs : ∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl) {p : U64}
    (hsc : capV (L.mem s) (cslotAddr sl) = .Thread p)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (e : Aeneas.Std.Array obj.Slot 3#usize) (exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) (ci : Fl4Spec.CapRef)
    (sl' : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType sl' = tcbLabelOf fl4_abi.label.TCBSetTimer)
    (hext : Fl4Spec.genInvocationType sl' = .invalidInvocation →
      Fl4Spec.fl4TcbExtLabelOf sl' = tcbExtOf fl4_abi.label.TCBSetTimer)  :
    TcbOKXP (L := L) arI (JStab (L := L) arI AR Z H Cs) (fun _ _ _ => False) s ar σ
      fl4_abi.label.TCBSetTimer p ⟨length, buf, is_call, cslotAddr sl, e⟩ true is_call can_donate sl'
      (argsU.map UScalar.bv) ci sl exs buffer := by
  have hpT : p ∈ Z.T := J.thT p (slot_cap_wf J.xtop hAs hsc).2
  obtain ⟨hg, he⟩ := ext_lbl hlbl hext setTimer_lbls.1 setTimer_lbls.2
  have hT0 := tcb_set_timerJSt arI s ar σ J hni p hpT (cslotAddr sl) hAs.isSlot (by rw [capAt_capV, hsc]) sl' hg he
    length buf ct hct argsU hLen hArgs hstall is_call (cslotAddr sl) e true can_donate ci sl exs buffer
  exact WP.spec_mono hT0 fun _ hr => TopPostDMX.toPN hr (thread_noPre_of hlbl setTimer_l5)

/-- (stpost) **The SetTimer arm at stable ghosts, as `DecOKDMXP` at the canonical label `sl'`**
(module docstring; `xcapP_of_tcb`'s proof, by hand: its application elaborates slowly). -/
theorem decode_threadTmD (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z] (hni : Entered σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (is_call can_donate : Bool) (length buf : U64)
    (argsU : List U64) (hLen : length.val = argsU.length)
    (hArgs : ∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl) {p : U64}
    (hsc : capV (L.mem s) (cslotAddr sl) = .Thread p)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (e : Aeneas.Std.Array obj.Slot 3#usize) (exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) (ci : Fl4Spec.CapRef)
    (sl' : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType sl' = tcbLabelOf fl4_abi.label.TCBSetTimer)
    (hext : Fl4Spec.genInvocationType sl' = .invalidInvocation →
      Fl4Spec.fl4TcbExtLabelOf sl' = tcbExtOf fl4_abi.label.TCBSetTimer) :
    DecOKDMXP (L := L) arI (JStab (L := L) arI AR Z H Cs) (fun _ _ _ => False) s ar σ fl4_abi.label.TCBSetTimer
      length (cslotAddr sl) (.Thread p) true is_call can_donate false buf e sl' (argsU.map UScalar.bv)
      ci sl exs buffer := by
  unfold DecOKDMXP syscall.decode_invocation
  rw [hct]; simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
  exact decode_threadTmOK s ar σ J hni ct hct is_call can_donate length buf argsU hLen hArgs sl hAs hsc hstall e exs buffer ci sl' hlbl hext

/-- FL4's Thread-cap decode at `TCBSetTimer` keeps `MR` (`MKD.decode_thread_nonins`), in
`XCapP.mrG`'s form. -/
theorem decode_threadTm_mr (hA : P0.ArchTotal arI) (hKD : MRKeepD arI MR) (s : S) (ar : A)
    (ms : Fl4Spec.MachineState) (hR : MR ar ms) (length slot p buf : U64) (is_call can_donate : Bool)
    (e : Aeneas.Std.Array obj.Slot 3#usize) :
    syscall.decode_invocation st arI s ar fl4_abi.label.TCBSetTimer length slot (.Thread p) true is_call
      can_donate false buf e ⦃ r => MR r.2.2 (if r.1 = .Ok () then id ms else ms) ⦄ :=
  WP.spec_mono (MKD.decode_thread_nonins L.total hA hKD setTimer_nonIns hR) fun r h => by
    split <;> exact h

/-- (stpost) **The Thread cap at `TCBSetTimer`, stable ghosts, `MR` after** (module docstring). -/
theorem decode_threadTmJSt (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z] (hni : Entered σ)
    (hA : P0.ArchTotal arI) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hR : MR ar σ.machineState)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (is_call can_donate : Bool) (length buf : U64)
    (argsU : List U64) (hLen : length.val = argsU.length)
    (hArgs : ∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl) {p : U64}
    (hsc : capV (L.mem s) (cslotAddr sl) = .Thread p)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (e : Aeneas.Std.Array obj.Slot 3#usize) (exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) (ci : Fl4Spec.CapRef) :
    XCapP (L := L) arI (JStabM (L := L) arI AR MR Z H Cs) (fun _ _ _ => False) s ar σ fl4_abi.label.TCBSetTimer
      length (cslotAddr sl) (.Thread p) true is_call can_donate false buf e fl4_abi.label.TCBSetTimer.bv
      (argsU.map UScalar.bv) ci sl exs buffer ct := by
  obtain ⟨sl', hlbl, hext, hd⟩ := tcb_canon fl4_abi.label.TCBSetTimer
  refine XCapP.lbl_congr arI (specDec_thread p hd) ?_
  left
  have hD := decode_threadTmD s ar σ J hni ct hct is_call can_donate length buf argsU hLen hArgs sl hAs hsc hstall e
    exs buffer ci sl' hlbl hext
  have hW := decode_threadTm_mr (st := st) hA hKD s ar σ.machineState hR length (cslotAddr sl) p buf is_call can_donate e
  have hq := perfF_tcbN hlbl setTimer_l5 σ true is_call can_donate false (argsU.map UScalar.bv) ci sl exs buffer p
  unfold DecOKDMXP at hD ⊢
  exact WP.spec_mono (WP.spec_and hD hW) fun _ ⟨h1, h2⟩ => h1.mrG hM h2 hq

end StTmDec

end

end Fl4Proofs.P3
