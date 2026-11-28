/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN mr4): **`kernel_entryJ13P`, the
kernel entry under `MachPlat`, with no `PPPlat` / `IrqPlat` anywhere below it**
(irq1 NEXT (3), mr3 NEXT (c)). Every top up to `kernel_entryJ15M` takes
`PPPlat` (false: `PPPlat.false`) and `IrqPlat` (degenerate), directly and
through `JEntryGlob.pp`, so they are vacuous; this one is not (`j13P_platform`).

* The budget step under `MachPlat`: FL4's `check_budget_restart` has no
  clock/IRQ arch op after the timestamp (`MK.sched_check_budget`, `MRKeep` [P]),
  `MachF.mfk_checkBudgetRestart` (spec: the MR fields and the interrupt table
  kept), `budget_ok_mr` (FL4's `budget_ok` = one clock read), `budget_mr_at`
  (at the spec's budget outcome `σb`: `MR a1 σb.ms` and `ValidIrqMasks σb`).
* `JEntryGlobM`: `JEntryGlob` with `pp : PPPlat` replaced by its arch-only part
  `ppA : PPPlatA` [P].
* `JPreDecHyp` [W] (THE remaining path-restricted premise of mr3 NEXT (b)):
  at the dispatch state, with `MR ar σ.ms ∧ ValidMachineTime σ ∧
  ValidIrqMasks σ` there, the decode and invocation of a CNode, Thread or
  Untyped cap (exactly the cap kinds whose spec decode can yield a
  preemptible invocation, `NoPreKind`/`PreInv`) refines with `JAt` after and
  `JAtPreMV` after a preempted invocation (`XCapP … JAtPreMV`). Not ∀σ: it is
  asked only at the decode's own values (the hypotheses of `decOK_J`) at the
  state `kernel_entryJ13P` dispatches from. l4v: `invoke_cnode_corres`
  (revoke/delete), `invoke_tcb_corres` (threadControlCaps/Sched),
  `invoke_untyped_corres` (`reset_untyped_cap`) with the machine state shared
  (`preemption_point_corres`, `do_machine_op` corres) and `valid_machine_time`,
  `valid_irq_masks` kept. These three families are proved at `J` but only from
  `PPPlat` (their loops call `ppJD`); mr4's `JAtZ.reset_loopJM` (UtResetLoopJM)
  is the first loop redone under `MachPlat`.
* `decOK_JM`: `decOK_J` with `JEntryGlobM` and `JAtPreMV`; every other cap
  kind by its existing J lemma (none preempts: `XCapP.reXP` /
  `specDec_noPreK` move `XP`).
* `handle_invocation_entryJM`, `invoke_afterJM`, `dispatch_invokeJM`,
  `dispatch_invokeJAllM` (preemption path by mr3's `hPre_ofZQIM`),
  `mid_invRecvJM`, `dispatch_midJM`, `KDispHyps13P` (= `KDispHyps15M` with
  `JEntryGlobM`, `JPreDecHyp`, and `ValidMachineTime` [J] at the dispatch
  state), `dispatch_all13P`, `kernel_entryJ13P`.
-/
import Fl4Proofs.P3.XTopJointKEntry15M
import Fl4Proofs.P3.XTopJointMRHole2
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

namespace MachF
open Fl4Spec Fl4Proofs.P3.Vs

/-- **The spec's budget check keeps the MR fields and the interrupt table.** -/
theorem mfk_checkBudgetRestart : MFK (checkBudgetRestart (Z := Unit)) := by
  unfold checkBudgetRestart
  mfk_auto
  all_goals exact mfk_checkBudget

end MachF


section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
  {MR : A → Fl4Spec.MachineState → Prop}

/-- **FL4's `budget_ok` reads the clock once** (`update_timestamp_mr`, then
`check_budget_restart` by `MRKeep`). -/
theorem budget_ok_mr (hM : MachPlat arI MR) (hK : MRKeep arI MR) (hA : P0.ArchTotal arI) {a : A}
    {ms : Fl4Spec.MachineState} (hR : MR a ms) (s : S) :
    syscall.budget_ok st arI s a ⦃ r => MR r.2.2 (gctState ms) ⦄ := by
  unfold syscall.budget_ok
  refine WP.spec_bind (update_timestamp_mr hM hR s) ?_
  rintro ⟨s1, a1⟩ h1
  have hS := L.total
  unfold sched.check_budget_restart
  refine WP.spec_bind (MK.sched_check_budget hS hA hK h1) ?_
  rintro ⟨r, s2, a2⟩ h2
  simp only at h2
  mk_walk

/-- **`MR` and `ValidIrqMasks` at the spec's budget outcome**: the
timestamp's one clock read (`updateTimeStamp_eq'`) and `checkBudgetRestart`
keeping `msF`. -/
theorem budget_mr_at (hM : MachPlat arI MR) (hnd : Fl4Spec.numDomains = 1) {σ0 σb : Fl4Spec.State Unit} {b : Bool}
    (hmem : (b, σb) ∈ ((Fl4Spec.updateTimeStamp (Z := Unit) >>= fun _ => Fl4Spec.checkBudgetRestart) σ0).1)
    {a1 : A} (hR : MR a1 (gctState σ0.machineState)) (hVI : ValidIrqMasks σ0) :
    MR a1 σb.machineState ∧ ValidIrqMasks σb := by
  have hE := Sched.updateTimeStamp_eq' hnd (doMachineOp_single (getCurrentTime_eq σ0.machineState))
  obtain ⟨⟨u, σu⟩, hu, h2⟩ := hmem
  rw [hE] at hu
  have e : σu = _ := congrArg Prod.snd (Set.mem_singleton_iff.1 hu)
  have hms : σu.machineState = gctState σ0.machineState := by rw [e]
  have his : σu.interruptStates = σ0.interruptStates := by rw [e]
  have hk := MachF.mfk_checkBudgetRestart σu _ h2
  have hRu : MR a1 σu.machineState := hms ▸ hR
  refine ⟨msF_mr hM hRu hk, msF_vim (σ := σu) ?_ hk⟩
  intro i hi
  rw [hms]
  exact hVI i (his ▸ hi)

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`XCapP` at another `XP`** when the cap's spec decode yields no
invocation with a preemption point (`TopPostDMX.not_preempted`). -/
theorem XCapP.reXP {X XP XP' : S → A → Fl4Spec.State Unit → Prop} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    {lbl length slot : U64} {c : capability.Cap} {blk call don fp : Bool} {buf : U64}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data} {args : List Fl4Spec.Data}
    {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    {buffer : Option Fl4Spec.ObjRef} {ct : U64}
    (h : XCapP (L := L) arI X XP s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer ct)
    (hnp : ∀ inv, DecOut (specDec fp slbl args ci sl c excaps buffer) σ inv → ¬ NoPre.PreInv inv) :
    XCapP (L := L) arI X XP' s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer ct := by
  rcases h with h | h
  · refine Or.inl (WP.spec_mono h fun res hr => ?_)
    have hne := TopPostDMX.not_preempted hr hnp
    have hI : ∀ s a σ, (if res.1 = .Err .Preempted then XP s a σ else X s a σ) →
        (if res.1 = .Err .Preempted then XP' s a σ else X s a σ) := fun s a σ hx => by
      rw [if_neg hne] at hx ⊢; exact hx
    exact match hr with
    | Or.inl ⟨e, h1, h2, h3, h4⟩ => Or.inl ⟨e, h1, h2, h3, hI _ _ _ h4⟩
    | Or.inr ⟨inv, h1, σ1, h2, y, hy, h3, h4⟩ => Or.inr ⟨inv, h1, σ1, h2, y, hy, h3, hI _ _ _ h4⟩
  · exact Or.inr h

variable {arI} in
/-- `HIPostMXP` at `JAtPreMV` gives it at `JAtPre`. -/
theorem HIPostMXP.toPreMV {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}
    {X : S → A → Fl4Spec.State Unit → Prop} {rep : Bool} {σ : Fl4Spec.State Unit} {c b d f : Bool}
    {cptr : Fl4Spec.CapRef} {res : core.result.Result Unit error.Exc × S × A}
    (h : HIPostMXP (L := L) X (JAtPreMV (L := L) arI AR MR) rep σ c b d f cptr res) :
    HIPostMXP (L := L) X (JAtPre (L := L) arI AR) rep σ c b d f cptr res := by
  obtain ⟨y, hy, hc, hR, hX⟩ := h
  refine ⟨y, hy, hc, hR, ?_⟩
  by_cases hp : res.1 = .Err .Preempted
  · rw [if_pos hp] at hX ⊢; exact hX.toPre
  · rw [if_neg hp] at hX ⊢; exact hX

/-- **[P]/[J]/[W] The global premises without `PPPlat`** (module docstring):
`JEntryGlob`'s fields, `pp` replaced by `ppA`. -/
structure JEntryGlobM (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (th : TypedHeap) : Prop where
  /-- [P] the arch relation's interface (`ARKeep`, `ARMask`). -/
  ari : ARIface arI AR
  /-- [P] the arch operations total. -/
  tot : P0.ArchTotal arI
  /-- [J]/[P] XTopJointDelR's `JDelParts`: the deletion's named steps (its
  own fields tagged there): platform and scope facts only. Every deletion
  runs at `WJL` from `JEntryAt.live` (CNode, IRQ handler: `JDelParts.jDelHypL`;
  the Thread cap's installs: XTopJointTcbInsL's `tcbInsW_wjl`). -/
  delParts : JDelParts (L := L) arI AR th
  /-- [P] one domain. -/
  nd : Fl4Spec.numDomains = 1
  /-- [P] the arch-only part of the preemption point's platform (`PPPlatA`:
  the IRQ read keeps `AR`, `min_budget`); the clock and the IRQ line are
  `MachPlat`'s, at the top. -/
  ppA : PPPlatA arI AR
  /-- [P] the domain configuration (`DomConfig`). -/
  dom : DomConfig
  /-- [P] the port-in values (`PortInVal`, the IO port decode for a call). -/
  portIn : PortInValMR arI MR
  /-- [P] the platform's timer agreement (`TimeAgree`; the Thread cap's
  SetSchedParams, `bind_tcb_refines`). -/
  timeAg : TimeAgree arI
  /-- [P] the platform's timer constants for a timeout fault's consumed time
  (`maxTicksToUs`, `ticks_to_us` at every arch state; as `JSchedCPath`'s
  `max`/`tu`): the reply's `do_fault_transfer` of a replier with a timeout
  fault and an SC (`JAtZ.xferAllJ`). -/
  maxTU : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv
  tu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄


variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

variable {arI} in
set_option maxHeartbeats 4000000 in
/-- **The notification cap's leaf at `J` with `NativeScope` at the invocation's
state** (g3e): `notifLeafJ` with no `SignalRestJHyp`. The spec's restart writes
`Restart` (`SInv.ns_setThreadState`), so `NativeScope` holds at the restart
state, where `JAtZ.signal_atN` (g3b) signals. -/
theorem notifLeafJN (hAT : P0.ArchTotal arI)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {s : S} {ar : A} {σ σ1 : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (hN : NativeScope σ) (hni : Entered σ) {ct : U64} (hct : sched.cur_thread st s = ok ct)
    {sl : Fl4Spec.CslotPtr} (hA : AbsSlot Z.th sl) {p b : U64} {w r : Bool}
    (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Notification p b w r))
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False)) :
    XLeaf (L := L) (JAt (L := L) arI AR) s ar σ (do
        let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
        let (s2, a1) ← notification.send_signal st arI s1 ar p b
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1))
      (Fl4Spec.sendSignal (Z := Unit) p.bv b.bv σ1) := by
  intro _
  have hpN := (J.slotN hA hc).1
  obtain ⟨s1, σ1', x, -, hst1, -, -, -, -, -, -, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  have hN1 := SInv.ns_setThreadState σ.curThread .restart (by intro e; cases e) σ hN _
    (by rw [hst1]; exact Set.mem_singleton _)
  obtain rfl := restart_out_eq hst1 hst
  rw [hs1]
  simp only [bind_ok]
  refine WP.spec_bind (J1.signal_atN hAT hmb hN1 p b hpN) ?_
  rintro ⟨s2, a1⟩ ⟨σ', V', Ac', Lst', D', hsp, -, J'⟩
  apply (WP.spec_ok _).2
  refine ⟨rfl, ((), σ'), by rw [hsp]; exact Set.mem_singleton _, J'.xtop.relTop, _, _, _, _, _, _, J', inferInstance⟩

end

end

end Fl4Proofs.P3
