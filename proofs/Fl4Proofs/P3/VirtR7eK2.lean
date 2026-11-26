/-
P3x for virtualization, spec side (line virt, gen 5; proofs/VIRT-PLAN.md §10 "Remaining (R7)" (e)):
**the extended kernel step is the ported one on `NR` states, without gen 4's `hnvc` [W]**.

* `nvc_entryPt`: at every entry point of a syscall event (`EntryPt`, VirtR7eK: after `update_time_stamp` and a
  passing `check_budget_restart`) `NVC` holds, from `NVC` at the event (VirtNvcW's `nvc_updateTimeStamp`,
  `nvc_checkBudgetRestart`). This is gen 4's premise `hnvc` [W], now a theorem.
* **`fl4CallKernelV_eqNR'`**: `fl4CallKernelV onCore rep ev σ = fl4CallKernel rep ev σ` on an `NR` state, with
  the one remaining premise below (gen 4's `fl4CallKernelV_eqNR` is kept unchanged).

Named premise:
* **`hoff : ∀ c, ev = .syscallEvent c → ∀ t, EntryPt σ t → OffRouteS c t` [S]** (syscall events only), as in
  VirtR7eK: the scope of the virtualization routes; on-route entries are covered by the route-B posts.

No [J]/[P]/[W]. New file only.
-/
import Fl4Proofs.P3.VirtNvcW
open Classical

namespace Fl4Proofs.P3.VirtR7eK2
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvL Fl4Proofs.P3.VirtR7b Fl4Proofs.P3.VirtR7e
  Fl4Proofs.P3.VirtR7eK Fl4Proofs.P3.VirtNvcW

noncomputable section

/-- **Gen 4's `hnvc` [W] discharged**: `NVC` at every entry point of a syscall event. -/
theorem nvc_entryPt {σ t : State Unit} (h : NVC σ) (ht : EntryPt σ t) : NVC t := by
  obtain ⟨t1, h1, h2⟩ := ht
  exact nvc_checkBudgetRestart t1 (nvc_updateTimeStamp σ h _ h1) _ h2

/-- **R7 (e) without `hnvc`**: the extended kernel step is the ported one on an `NR` state (premise `hoff` [S],
module docstring). -/
theorem fl4CallKernelV_eqNR' (onCore : ObjRef → Bool) (rep : Bool) (ev : Event) {σ : State Unit} (hs : NR σ)
    (hoff : ∀ c, ev = .syscallEvent c → ∀ t, EntryPt σ t → OffRouteS c t) :
    fl4CallKernelV (Z := Unit) onCore rep ev σ = fl4CallKernel rep ev σ :=
  fl4CallKernelV_eqNR onCore rep ev hs hoff fun _ _ _ ht => nvc_entryPt hs.1.1 ht

end

end Fl4Proofs.P3.VirtR7eK2
