/-
P3 (DESIGN.md §9): **the spec keeps `cur_thread`** (`CTK`), a mechanical copy
of TcbDom's `DK` (the domain schedule) for `cur_thread`: no step of the
arch invocations, the deletions or `install_tcb_cap` writes it.
-/
import Fl4Proofs.P3.CurRecDel
import Fl4Proofs.P3.TcbReadRegsSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs.CurK
open Fl4Spec Classical

noncomputable section

theorem ctk_orderedInsert' {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β)
    (R : β → β → Prop) : CTK (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_orderedInsert' _ _ _ _)

theorem ctk_readyTimesAppend' (t : ObjRef) (q : List ObjRef) : CTK (readyTimesAppend (Z := Unit) t q) := by
  unfold readyTimesAppend; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_readyTimesAppend' _ _)

theorem ctk_tcbReleaseEnqueue' (t : ObjRef) : CTK (tcbReleaseEnqueue (Z := Unit) t) := by
  unfold tcbReleaseEnqueue; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_tcbReleaseEnqueue' _)

theorem ctk_tcbAppend' (t : ObjRef) (q : List ObjRef) : CTK (tcbAppend (Z := Unit) t q) := by
  unfold tcbAppend; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_tcbAppend' _ _)

theorem ctk_postpone' (sc : ObjRef) : CTK (postpone (Z := Unit) sc) := by
  unfold postpone; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_postpone' _)

theorem ctk_threadSetPriority' (t : ObjRef) (p : Priority) : CTK (threadSetPriority (Z := Unit) t p) := by
  unfold threadSetPriority; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_threadSetPriority' _ _)

theorem ctk_reorderEp' (e t : ObjRef) : CTK (reorderEp (Z := Unit) e t) := by
  unfold reorderEp; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_reorderEp' _ _)

theorem ctk_reorderNtfn' (n t : ObjRef) : CTK (reorderNtfn (Z := Unit) n t) := by
  unfold reorderNtfn; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_reorderNtfn' _ _)

theorem ctk_archPostModifyRegisters' (c t : ObjRef) : CTK (archPostModifyRegisters (Z := Unit) c t) := by
  unfold archPostModifyRegisters; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_archPostModifyRegisters' _ _)

theorem ctk_schedContextResume' (sc : ObjRef) : CTK (schedContextResume (Z := Unit) sc) := by
  unfold schedContextResume; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_schedContextResume' _)

theorem ctk_testPossibleSwitchTo' (t : ObjRef) : CTK (testPossibleSwitchTo (Z := Unit) t) := by
  unfold testPossibleSwitchTo; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_testPossibleSwitchTo' _)

theorem ctk_ifSporadicCurScTestRefillUnblockCheck' (o : Option ObjRef) : CTK (ifSporadicCurScTestRefillUnblockCheck (Z := Unit) o) := by
  unfold ifSporadicCurScTestRefillUnblockCheck; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_ifSporadicCurScTestRefillUnblockCheck' _)

theorem ctk_restart' (t : ObjRef) : CTK (restart (Z := Unit) t) := by
  unfold restart; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_restart' _)

theorem ctk_setMcpriority' (t : ObjRef) (m : Priority) : CTK (setMcpriority (Z := Unit) t m) := by
  unfold setMcpriority; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_setMcpriority' _ _)

theorem ctk_setPriority' (t : ObjRef) (p : Priority) : CTK (setPriority (Z := Unit) t p) := by
  unfold setPriority; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_setPriority' _ _)

theorem ctk_schedContextBindTcb' (sc t : ObjRef) : CTK (schedContextBindTcb (Z := Unit) sc t) := by
  unfold schedContextBindTcb; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_schedContextBindTcb' _ _)

theorem ctk_bindNotification' (t n : ObjRef) : CTK (bindNotification (Z := Unit) t n) := by
  unfold bindNotification; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_bindNotification' _ _)

theorem ctk_setFlags' (t : ObjRef) (f : TcbFlags) : CTK (setFlags (Z := Unit) t f) := by
  unfold setFlags; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_setFlags' _ _)

theorem ctk_lazyFpuRestore' (t : ObjRef) : CTK (lazyFpuRestore (Z := Unit) t) := by
  unfold lazyFpuRestore; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_lazyFpuRestore' _)

theorem ctk_archPostSetFlags' (t : ObjRef) (f : TcbFlags) : CTK (archPostSetFlags (Z := Unit) t f) := by
  unfold archPostSetFlags; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_archPostSetFlags' _ _)

theorem ctk_checkCapAt' (c : Cap) (sl : CslotPtr) {m : SMonad Unit Unit} (h : CTK m) :
    CTK (checkCapAt (Z := Unit) c sl m) := by
  unfold checkCapAt; ctk_auto; exact h
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible refine ctk_checkCapAt' _ _ ?_)

theorem ctke_installTcbCap' (t : ObjRef) (sl : CslotPtr) (n : Nat) (o : Option (Cap × CslotPtr)) :
    CTKE (installTcbCap (Z := Unit) t sl n o) := by
  unfold installTcbCap; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctke_installTcbCap' _ _ _ _)

theorem ctke_installTcbFrameCap' (t : ObjRef) (sl : CslotPtr) (b : Option (VSpaceRef × Option (Cap × CslotPtr))) :
    CTKE (installTcbFrameCap (Z := Unit) t sl b) := by
  unfold installTcbFrameCap; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctke_installTcbFrameCap' _ _ _)

end

end Fl4Proofs.P3.Vs.CurK
