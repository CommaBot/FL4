/-
P3 (FL4 #71, pf1): **`P1.VmFaultOK` from the joint relation** (m73's
`JAtZ.fastFaultOK` for the VM fault fast path).

`P1.VmFaultOK s a` (the general VM-fault path's reads at every state after a
passing `budget_ok`, where `handle_vm_fault_local` enters
`fastpath_vm.vm_fault`) at a `JAtZ` entry state: the entry has no `FAULT_IP`
write, so `JAtZ.budgetOkB` runs at the entry's own spec state `σ` (no
`faultIPSt`); at the post-`budget_ok` state the facts `vmFault_of` asks are
m73's (`JAtZ.bxiU`, `curNb`, `fhTyped`, `bufU_out`, `bufOK`, `asidOffU`).
`OffReady σ` is asked at the entry state (the `KBudgetB` field; the
syscall route has it of `faultIPSt σ`, which differs from `σ` only in the
current thread's `FAULT_IP`).

`JAtZ.rrPreAtG`: the ReplyRecv bundle `P1.RRPreAtG ty` (any fault type with a
restart instance; used at `VMFault`) from the joint relation, as m69 / m70's
`JAtZ.rrPreAt` / `rrPre5At` (`JAtZ.rrDisp` and the P1 `…G` lemmas).

**`kernel_entry_reachU15Vm`** (pf1 step 2, the page-fault entries beside the
serial gate, accepted case): from `JReachU15` and `kernel_entry_reachU15`'s
premises, an accepted `handle_vm_fault_local` has the postcondition of
`kernel_entry_reachU15`'s VM-fault clause, and an accepted
`handle_reply_recv_vm_local` that of its syscall clause at `SysReplyRecv`
(so the existing refinement covers both). No premise is added: the ReplyRecv
clause's one extra input is fl4-sync's contract that `found` is what
`reply_caps` returns for the current thread at the entry state (P1
`rr_prefix_keep` carries it to the dispatch state).
-/
import Fl4Proofs.P3.XTopJointKEntryFF
import Fl4Proofs.P3.XTopJointKEntryRRG
import Fl4Proofs.P3.XTopJointKEntryU15
import Fl4Proofs.P1.FastVmLocal
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {MR : A → Fl4Spec.MachineState → Prop}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- **`P1.VmFaultOK` at a `JAtZ` entry state** (module docstring). -/
theorem JAtZ.vmFaultOK {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z]
    (hni : Entered σ) (hR : MR a σ.machineState) (hS : SInvAll.SInvB σ)
    (hQ : ∀ d p, σ.curThread ∉ σ.readyQueues d p) (hOff : OffReady σ)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    P1.VmFaultOK (L := L) arI s a := by
  intro s1 a1 t addr fsr ins hb et
  have hC : CurInv σ := J.cur.resolve_left (by rw [hni.2]; intro e; cases e)
  have hBu : KBudgetB arI a σ := ⟨hM.nowAgree hR hS.1.1.vmt, hC, hOff, Or.inr hQ⟩
  have hBud := JAtZ.budgetOkB J hni hBu hS.1.1.ns hARI.toARKeep hA hnd hmrt hmb hmax htu
  rw [hb, WP.spec_ok] at hBud
  obtain ⟨σb, -, -, -, -, -, -, hCb, -, Ac', Lst', D', J'⟩ := hBud.1 rfl
  exact P1.vmFault_of arI hA J'.bxiU et (J'.curNb hCb) J'.fhTyped (fun b hb => J'.bufU_out hb)
    (fun y hy => J'.bufOK hy) J'.asidOffU

set_option maxHeartbeats 4000000 in
/-- **`P1.RRPreAtG` from the joint relation** (module docstring), for any
fault type with a restart instance (m69 / m70's `JAtZ.rrPreAt` / `rrPre5At`
through the `…G` lemmas). -/
theorem JAtZ.rrPreAtG {ty : U64} [P1.HfrRestart st arI ty] {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z]
    (hni : Entered σ) (hR : MR a σ.machineState) (hS : SInvAll.SInvB σ)
    (hQ : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → OffReady (faultIPSt σ σ.curThread x))
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRV : SInvR.RV σ) : P1.RRPreAtG (L := L) arI ty s a := by
  intro t nx s1 s2 a2 et enx es1 hb
  obtain ⟨x, σb, -, ekh, V0, Ac', Lst', D', J'⟩ :=
    J.rrDisp hni hR hS hQ hB hARI hA hnd hM hmrt hmb hmax htu et enx es1 hb
  have hSum := J'.rrSum (rv_faultIP ekh hRV)
  exact P1.RRPre.of2G arI (T := P1.Heap.tcbs H)
    (fun _ _ _ _ _ et' hrc hC => P1.rrEnt_lkG arI J'.bxi J'.lkTyped et' hrc hC)
    (P1.RRPre2.of3G arI (fun _ _ _ _ _ et' hrc hC => P1.rrPl_lkG arI (fun _ h => h) J'.bxi J'.lkTyped et' hrc hC) hSum
      (P1.RRPre3.of5G arI (fun _ _ _ _ _ et' hrc hC => P1.rrPl_lkG arI (fun _ h => h) J'.bxi J'.lkTyped et' hrc hC)
        hSum (fun _ et' => J'.cnOff et')
        (P1.rrPre5_ofG arI J'.bxi
          (fun _ _ _ _ _ et' hrc hC => P1.rrPl_lkG arI (fun _ h => h) J'.bxi J'.lkTyped et' hrc hC) hSum hA)))

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

end

end

end Fl4Proofs.P3.SInvR.G5
