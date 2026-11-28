/-
P3 (issue #16, m70): **`kernel_entryJ33H` / `kernel_entryJ34H` / `kernel_entryJ34HW`**, m69's
`kernel_entryJ33F` / `J34F` / `J34FW` without m67's `nvm` read `hRP5 : P1.RRPreAt5` [J]: at every
dispatch state of the entry, `RRPre5` from the dispatch state's `JAtZ` (`JAtZ.rrDisp`: `BXI`, the
cap typing, `RRSum` from `RV`) by P1's `rrPre5_of` (FastTailRR: the fast run's tail ends with the
receiver current and `Running`).
-/
import Fl4Proofs.P3.XTopJointKEntryRRF
import Fl4Proofs.P1.FastTailRR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {MR : A → Fl4Spec.MachineState → Prop}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **m67's `RRPreAt5` from the joint relation** (module docstring). -/
theorem JAtZ.rrPre5At {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z]
    (hni : Entered σ) (hR : MR a σ.machineState) (hS : SInvAll.SInvB σ)
    (hQ : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → OffReady (faultIPSt σ σ.curThread x))
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRV : SInvR.RV σ) : P1.RRPreAt5 (L := L) arI s a := by
  intro t nx s1 s2 a2 et enx es1 hb
  obtain ⟨x, σb, -, ekh, V0, Ac', Lst', D', J'⟩ :=
    J.rrDisp hni hR hS hQ hB hARI hA hnd hM hmrt hmb hmax htu et enx es1 hb
  exact P1.rrPre5_of arI J'.bxi (fun _ _ _ _ _ et' hrc hC => P1.rrPl_lk arI (fun _ h => h) J'.bxi J'.lkTyped et' hrc hC)
    (J'.rrSum (rv_faultIP ekh hRV)) hA

end

end

end Fl4Proofs.P3
