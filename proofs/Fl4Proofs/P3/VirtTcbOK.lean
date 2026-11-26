/-
P3x for virtualization, spec side (line virt, gen 5; proofs/VIRT-PLAN.md §10 "Remaining (R7)" (e)):
**`TcbCapsOK` of every TCB invocation the ported decoder returns** — gen 4's `TcbCapsOK` [S] becomes a theorem,
and the scope premise of the R7 (e) top is left with the three route conditions only.

No state invariant is needed: l4v's `decode_tcb_invocation` checks every cap a `ThreadControlCaps` installs —
the fault / timeout handlers by `check_handler_ep` (`valid_fault_handler`: an endpoint or null cap), the CSpace
root by `is_cnode_cap`, the VSpace root by `is_valid_vtable_root` (a mapped PML4 cap) after `derive_cap` — and
none of those is a virtualization cap.

* `vfh_nv`, `cnode_nv`, `vt_nv`; `okd_checkHandlerEp`, `okd_decodeCvSpace`, `okd_decodeSetSpace`,
  `okd_decodeTcbConfigure`, `okd_decodeSetTimeoutEp`, `okd_decodeSetIpcBuffer`, **`okd_decodeTcb`**
  (`decodeTcbInvocation`), **`okd_fl4DecodeTcb_invOK`** (`fl4DecodeTcbInvocation`: `InvOK`).
* `OffRoute5` / `OffRouteS5`: the scope reduced to `¬ Route3` (VirtOffNv) at the decode points;
  `offRoute4_of5`, `offRouteS4_of5`.
* **`fl4CallKernelV_eqNR5`**: `fl4CallKernelV onCore rep ev σ = fl4CallKernel rep ev σ` on an `NR` state.

Named premises (of `fl4CallKernelV_eqNR5`):
* **`hvk : virtKind = .none` [S]** (route scope, VirtInvOK).
* **`hr5 : ∀ c, ev = .syscallEvent c → ∀ t, EntryPt σ t → OffRouteS5 c t` [S]**: no decode point the syscall
  reaches is on one of the three routes (label 60 on a frame cap, label 88 on a thread cap in the second phase,
  the VT-x retype gate on an untyped cap); those inputs are covered by the route-B posts.

No [J]/[P]/[W]. New file only.
-/
import Fl4Proofs.P3.VirtInvOK
open Classical

namespace Fl4Proofs.P3.VirtTcbOK
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvDom Fl4Proofs.P3.SInvL
  Fl4Proofs.P3.VirtR7b Fl4Proofs.P3.VirtNvTcb Fl4Proofs.P3.VirtR7e Fl4Proofs.P3.VirtR7eK
  Fl4Proofs.P3.VirtOffNv Fl4Proofs.P3.VirtInvOK

noncomputable section

set_option maxHeartbeats 1000000

theorem vfh_nv {c : Cap} (h : validFaultHandler c) : ¬ IsVirtCap c := by
  rcases h with ⟨h1, _⟩ | h2
  · cases c <;> simp_all [isEpCap, IsVirtCap]
  · subst h2; exact fun h => h

theorem cnode_nv {c : Cap} (h : isCnodeCap c = true) : ¬ IsVirtCap c := by
  cases c <;> simp_all [isCnodeCap, IsVirtCap]

theorem vt_nv {c : Cap} (h : isValidVtableRoot c) : ¬ IsVirtCap c := by
  obtain ⟨r, a, rfl⟩ := h
  exact fun h => h

theorem capOK_none : CapOK none := fun _ _ h => by cases h

theorem okd_checkHandlerEp (pos : Nat) (hc : Cap × CslotPtr) (σ : State Unit) :
    OkDAt σ (fun _ r => ¬ IsVirtCap r.1) (checkHandlerEp (Z := Unit) pos hc) := by
  unfold checkHandlerEp
  exact okdAt_unlessE_bind _ _ fun h => okdAt_returnOk (vfh_nv h)

/-- Through binds keeping the values (the checked caps). -/
macro "tk_keep" : tactic => `(tactic| repeat' (first
  | exact okdAt_throw _
  | (refine okdAt_unlessE_bind _ _ fun _ => ?_)
  | (refine okdAt_whenE_bind _ _ fun _ => ?_)
  | (with_reducible refine okdAt_returnOk_bind ?_)
  | (with_reducible refine okdAt_bind fun _ _ _ => ?_)
  | (refine okdAt_ite _ ?_ ?_)))

/-- Through binds whose values do not matter. -/
macro "tk_gen" : tactic => `(tactic| repeat' (first
  | exact okdAt_throw _
  | exact okdAt_returnOk trivial
  | (refine okdAt_ite _ ?_ ?_)
  | (with_reducible refine okdAt_bind fun _ _ _ => ?_)
  | split))

theorem okd_decodeCvSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr))
    (σ : State Unit) :
    OkDAt σ (fun _ ti => CapOK ti.tcNewCroot ∧ CapOK ti.tcNewVroot) (decodeCvSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeCvSpace
  tk_keep
  all_goals refine okdAt_returnOk ⟨?_, ?_⟩
  all_goals (intro c src h; cases h; first | exact cnode_nv (by assumption) | exact vt_nv (by assumption))

theorem okd_decodeSetSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr))
    (σ : State Unit) : OkDAt σ (fun _ ti => TcbCapsOK ti) (decodeSetSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeSetSpace
  refine okdAt_whenE_bind _ _ fun _ => ?_
  refine okdAt_bind fun sp s hsp => ?_
  have hsp' := okd_decodeCvSpace _ _ _ _ σ sp s hsp
  refine okdAt_returnOk_bind ?_
  refine okdAt_bind fun fh s2 hfh => ?_
  have hf := okd_checkHandlerEp _ _ s fh s2 hfh
  exact okdAt_returnOk ⟨fun c src h => by cases h; exact hf, capOK_none, hsp'.1, hsp'.2⟩

theorem okd_decodeTcbConfigure (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr))
    (σ : State Unit) : OkDAt σ (fun _ ti => TcbCapsOK ti) (decodeTcbConfigure (Z := Unit) args cap slot excaps) := by
  unfold decodeTcbConfigure
  refine okdAt_whenE_bind _ _ fun _ => ?_
  refine okdAt_whenE_bind _ _ fun _ => ?_
  refine okdAt_returnOk_bind ?_
  refine okdAt_returnOk_bind ?_
  refine okdAt_bind fun _ s _ => ?_
  refine okdAt_bind fun sp s2 hsp => ?_
  have hsp' := okd_decodeCvSpace _ _ _ _ s sp s2 hsp
  exact okdAt_returnOk ⟨capOK_none, capOK_none, hsp'.1, hsp'.2⟩

theorem okd_decodeSetTimeoutEp (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) (σ : State Unit) :
    OkDAt σ (fun _ ti => TcbCapsOK ti) (decodeSetTimeoutEp (Z := Unit) cap slot excaps) := by
  unfold decodeSetTimeoutEp
  refine okdAt_whenE_bind _ _ fun _ => ?_
  refine okdAt_returnOk_bind ?_
  refine okdAt_bind fun th s hth => ?_
  have hf := okd_checkHandlerEp _ _ σ th s hth
  exact okdAt_returnOk ⟨capOK_none, fun c src h => by cases h; exact hf, capOK_none, capOK_none⟩

theorem okd_decodeSetIpcBuffer (args : List Data) (cap : Cap) (slot : CslotPtr) (excs : List (Cap × CslotPtr))
    (σ : State Unit) : OkDAt σ (fun _ ti => TcbCapsOK ti) (decodeSetIpcBuffer (Z := Unit) args cap slot excs) := by
  unfold decodeSetIpcBuffer
  repeat' (first
    | exact okdAt_throw _
    | exact okdAt_returnOk ⟨capOK_none, capOK_none, capOK_none, capOK_none⟩
    | (refine okdAt_whenE_bind _ _ fun _ => ?_)
    | (with_reducible refine okdAt_bind fun _ _ _ => ?_)
    | split)

/-- **Every `ThreadControlCaps` the ported TCB decoder returns installs no virtualization cap.** -/
theorem okd_decodeTcb (label : Data) (args : List Data) (cap : Cap) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) (σ : State Unit) :
    OkDAt σ (fun _ ti => TcbCapsOK ti) (decodeTcbInvocation (Z := Unit) label args cap slot excs) := by
  unfold decodeTcbInvocation
  split
  all_goals first
    | exact okd_decodeTcbConfigure _ _ _ _ _
    | exact okd_decodeSetSpace _ _ _ _ _
    | exact okd_decodeSetTimeoutEp _ _ _ _
    | exact okd_decodeSetIpcBuffer _ _ _ _ _
    | exact okdAt_returnOk trivial
    | exact okdAt_throw _
    | (unfold decodeReadRegisters; tk_gen; done)
    | (unfold decodeWriteRegisters; tk_gen; done)
    | (unfold decodeCopyRegisters; tk_gen; done)
    | (unfold decodeSetPriority; tk_gen; done)
    | (unfold decodeSetMcpriority; tk_gen; done)
    | (unfold decodeSetSchedParams; tk_gen; done)
    | (unfold decodeBindNotification; tk_gen; done)
    | (unfold decodeUnbindNotification; tk_gen; done)
    | (unfold decodeSetTlsBase; tk_gen; done)
    | (unfold decodeSetFlags; tk_gen; done)

/-- **`InvOK` of FL4's TCB decoder.** -/
theorem okd_fl4DecodeTcb_invOK (label : Data) (args : List Data) (cap : Cap) (slot : CslotPtr)
    (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) (σ : State Unit) :
    OkDAt σ (fun _ i => InvOK i) (fl4DecodeTcbInvocation (Z := Unit) label args cap slot excaps buffer) := by
  unfold fl4DecodeTcbInvocation
  split
  · exact okdAt_liftME fun _ _ _ => trivial
  · split
    · exact okdAt_liftME fun _ _ _ => trivial
    · exact okdAt_liftME (okd_decodeTcb _ _ _ _ _ σ)

/-- **The scope: off the three routes** (the [S] premise, module docstring). -/
def OffRoute5 (fp : Bool) (cptr : CapRef) (s : State Unit) : Prop :=
  ∀ info a args u, DecPt cptr s info a args u → ¬ Route3 fp info.miLabel args a.2.1 a.2.2.1

theorem offRoute4_of5 {fp : Bool} {cptr : CapRef} {s : State Unit} (h : OffRoute5 fp cptr s) :
    OffRoute4 fp cptr s :=
  fun info a args u hd => ⟨h info a args u hd, fun _ _ => okd_fl4DecodeTcb_invOK _ _ _ _ _ _ u⟩

def OffRouteS5 (c : Syscall) (t : State Unit) : Prop :=
  ∀ reg, sysReg c = some reg → ∀ cptr t', (cptr, t') ∈ (getCapReg (Z := Unit) reg t).1 → ∀ fp, OffRoute5 fp cptr t'

theorem offRouteS4_of5 {c : Syscall} {t : State Unit} (h : OffRouteS5 c t) : OffRouteS4 c t :=
  fun reg hr cptr t' hm fp => offRoute4_of5 (h reg hr cptr t' hm fp)

/-- **R7 (e), gen 5 top**: the extended kernel step is the ported one on an `NR` state, given only the route
scope (`hvk`, `hr5` [S], module docstring). -/
theorem fl4CallKernelV_eqNR5 (hvk : virtKind = .none) (onCore : ObjRef → Bool) (rep : Bool) (ev : Event)
    {σ : State Unit} (hs : NR σ) (hr5 : ∀ c, ev = .syscallEvent c → ∀ t, EntryPt σ t → OffRouteS5 c t) :
    fl4CallKernelV (Z := Unit) onCore rep ev σ = fl4CallKernel rep ev σ :=
  fl4CallKernelV_eqNR4 hvk onCore rep ev hs fun c hc t ht => offRouteS4_of5 (hr5 c hc t ht)

end

end Fl4Proofs.P3.VirtTcbOK
