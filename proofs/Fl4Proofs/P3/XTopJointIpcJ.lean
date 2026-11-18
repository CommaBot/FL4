/-
P3 (DESIGN.md §9): **the IPC caps' leaves at `J`** (XTopJointEntry's
`JPath` for the Endpoint, Notification and Reply caps): the caller's
restart, then FL4's `send_signal` / `do_reply_transfer` / `send_ipc`,
against the spec's, from `JAtZ` at the invocation to `JAt` after.

* `notifLeafJ`: the caller's restart at `J` (`JAtZ.restartJ`), the cap's
  notification one of `N` (`JAtZ.slotN`), then ScSignalJ's `SignalJHyp`
  (`signalJHyp_of`: from `SignalRestJHyp` [J], the bound thread
  `RunningVM`, VT-x; `RecvReplyLinksHyp` [J]; the platform's `MIN_BUDGET`
  [P]).
-/
import Fl4Proofs.P3.XTopJointTcb
import Fl4Proofs.P3.ScSignalJ
import Fl4Proofs.P3.JProducers
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- The caller's restart in the spec is deterministic. -/
theorem restart_out_eq {σ σ1 σ2 : Fl4Spec.State Unit}
    (h1 : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (h2 : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ2)}, False)) : σ1 = σ2 := by
  have e := (Prod.mk.inj (h1.symm.trans h2)).1
  exact congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 e)

set_option maxHeartbeats 4000000 in
/-- **The notification cap's leaf at `J`** (module docstring). -/
theorem notifLeafJ (hAT : P0.ArchTotal arI) (hW : SignalRestJHyp (L := L) arI AR H Cs)
    (hRR : RecvReplyLinksHyp (L := L) arI AR H Cs)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {s : S} {ar : A} {σ σ1 : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) {ct : U64} (hct : sched.cur_thread st s = ok ct)
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
  obtain rfl := restart_out_eq hst1 hst
  rw [hs1]
  simp only [bind_ok]
  refine WP.spec_bind (signalJHyp_of hAT hW hRR hmb Z Ac1 Lst1 D1 s1 ar σ1' p b J1 hpN) ?_
  rintro ⟨s2, a1⟩ ⟨σ', V', Ac', Lst', D', hsp, -, J'⟩
  apply (WP.spec_ok _).2
  refine ⟨rfl, ((), σ'), by rw [hsp]; exact Set.mem_singleton _, J'.xtop.relTop, _, _, _, _, _, _, J'⟩

end

end

end Fl4Proofs.P3
