/-
P3 (DESIGN.md §9), IPC: **the IPC caps' tails with their facts at the
post-restart state** (the fold's re-scoping of `send_tail_top`,
`send_tail_ntfn`, `reply_tail_inv`): the "at every `IRel`" premises are
used only after the caller's restart; here they are taken there
(`SchedValid`, `QSorted`, `SendRest` for a send; `NativeScope` for a signal;
`SchedValid`, `ObjCover` for a reply).
-/
import Fl4Proofs.P3.IpcXTop
import Fl4Proofs.P3.IpcTcbJAll
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Ipc

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {c : U64}

set_option maxHeartbeats 4000000 in
/-- `send_tail_top` with its facts at the post-restart state. -/
theorem send_tail_topS (hH : IpcSchedHyps st ar N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBf : EpBufHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBm : EpBufMapHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hTl : IpcEpTailHyps st A N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hP : IPlaced N T E R B)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ)
    {ct : U64} (hct : ct ∈ T) (hcur : σ.curThread = ct.bv) {xt : Fl4Spec.Tcb} (hkt : σ.kheap ct.bv = some (.tcb xt))
    (hrun : tsCode xt.tcbState < 3) (hft : xt.tcbFault = none)
    {σ1 : Fl4Spec.State Unit} (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    {p : U64} (hp : p ∈ E) (b : U64) (blk call g gr don : Bool)
    (hF : ∀ s1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 → Sched.SchedValid σ1 ∧
      QSorted st T E s1 ∧ SendRest st ar (IRel st th cr N T C E R B c) T s1 a σ1 blk call b g gr don ct p) :
    (do
      let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
      let (s2, a1) ← endpoint.send_ipc st ar s1 a blk call b g gr don ct p
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1)) ⦃ r => r.1 = .Ok () ∧
      ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) blk call b.bv g gr don σ1.curThread p.bv σ1).1,
        RelTopM (L := L) r.2.1 z.2 ∧ IRel st th cr N T C E R B c r.2.1 z.2 ⦄ := by
  obtain ⟨hIR, hSRT⟩ := hX
  have hSB := IpcRel.toSRN hIR hSRT
  have hsteps := IpcSchedHyps.stepsG (A := A) hH hBf hBm hP
  obtain ⟨xt0, hk0, hTR⟩ := hIR.tcb ct hct
  rw [hkt] at hk0; cases hk0
  have hq := IpcRel.not_ep_queued hIR (t := ct) (by rw [hTR.st]; omega)
  have hcode : sched.TS_RESTART.val = tsCode .restart := by unfold sched.TS_RESTART; rfl
  obtain ⟨s1, hs1, hE1, hS1⟩ := spec_exists (hsteps.sts hP.e s σ hIR.toE hSB hct hkt hq (show tsCode xt.tcbState ≠ 6 by omega) .restart
    (by decide) sched.TS_RESTART hcode)
  rw [hs1]
  simp only [bind_ok]
  obtain ⟨hF1⟩ := (⟨hF s1 hs1⟩ : Nonempty _)
  rw [hcur, Notif.setThreadState_eq .restart hkt] at hst
  have hσ1 : σ1 = stsAct (updK σ ct.bv (.tcb { xt with tcbState := .restart })) ct.bv := by
    have := congrArg (fun q => ((), σ1) ∈ q.1) hst
    simp only [Set.mem_singleton_iff, Prod.mk.injEq, true_and, iff_true] at this
    simpa using this.symm
  subst hσ1
  obtain ⟨hIR1, hSRT1⟩ := IpcRel.ofSRN hE1 hS1
  have hX1 : IRel st th cr N T C E R B c s1 _ := ⟨hIR1, hSRT1⟩
  have hkt1 : (stsAct (updK σ ct.bv (.tcb { xt with tcbState := .restart })) ct.bv).kheap ct.bv =
      some (.tcb { xt with tcbState := .restart }) := by rw [stsAct_kheap]; simp
  have hc1 : (stsAct (updK σ ct.bv (.tcb { xt with tcbState := .restart })) ct.bv).curThread = ct.bv := by
    unfold stsAct; split_ifs <;> exact hcur
  refine WP.spec_bind (send_ipc_top hH hBf hBm hTl hP s1 a _ hIR1 hSRT1 hF1.1 hct hkt1
    (by simp [tsCode]) (fun m h => by cases h) (by simp [tsCode]) hft hp (hF1.2.1 p hp) blk call b g gr don
    hF1.2.2) ?_
  rintro ⟨s2, a1⟩ ⟨-, z, hz, hIR2, hSRT2⟩
  apply (WP.spec_ok _).2
  exact ⟨rfl, z, by rw [hc1]; exact hz, (SRT.relTop ⟨hIR2, hSRT2⟩).1, hIR2, hSRT2⟩

set_option maxHeartbeats 4000000 in
/-- `send_tail_ntfn` with `NativeScope` at the post-restart state. -/
theorem send_tail_ntfnS (hH : IpcSchedHyps st ar N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBf : EpBufHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBm : EpBufMapHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hP : IPlaced N T E R B)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ)
    {ct : U64} (hct : ct ∈ T) (hcur : σ.curThread = ct.bv) {xt : Fl4Spec.Tcb} (hkt : σ.kheap ct.bv = some (.tcb xt))
    (hrun : tsCode xt.tcbState < 3)
    {σ1 : Fl4Spec.State Unit} (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    {p : U64} (hp : p ∈ N) (b : U64) (hF : NativeScope σ1) :
    (do
      let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
      let (s2, a1) ← notification.send_signal st ar s1 a p b
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1)) ⦃ r => r.1 = .Ok () ∧
      ∃ z ∈ (Fl4Spec.sendSignal (Z := Unit) p.bv b.bv σ1).1,
        RelTopM (L := L) r.2.1 z.2 ∧ IRel st th cr N T C E R B c r.2.1 z.2 ⦄ := by
  obtain ⟨hIR, hSRT⟩ := hX
  have hSB := IpcRel.toSRN hIR hSRT
  have hsteps := IpcSchedHyps.stepsG (A := A) hH hBf hBm hP
  obtain ⟨xt0, hk0, hTR⟩ := hIR.tcb ct hct
  rw [hkt] at hk0; cases hk0
  have hq := IpcRel.not_ep_queued hIR (t := ct) (by rw [hTR.st]; omega)
  have hcode : sched.TS_RESTART.val = tsCode .restart := by unfold sched.TS_RESTART; rfl
  obtain ⟨s1, hs1, hE1, hS1⟩ := spec_exists (hsteps.sts hP.e s σ hIR.toE hSB hct hkt hq (show tsCode xt.tcbState ≠ 6 by omega) .restart
    (by decide) sched.TS_RESTART hcode)
  rw [hs1]
  simp only [bind_ok]
  rw [hcur, Notif.setThreadState_eq .restart hkt] at hst
  have hσ1 : σ1 = stsAct (updK σ ct.bv (.tcb { xt with tcbState := .restart })) ct.bv := by
    have := congrArg (fun q => ((), σ1) ∈ q.1) hst
    simp only [Set.mem_singleton_iff, Prod.mk.injEq, true_and, iff_true] at this
    simpa using this.symm
  subst hσ1
  obtain ⟨hIR1, hSRT1⟩ := IpcRel.ofSRN hE1 hS1
  have hX1 : IRel st th cr N T C E R B c s1 _ := ⟨hIR1, hSRT1⟩
  refine WP.spec_bind (send_signal_top hH hP s1 a _ hX1 hp hF b) ?_
  rintro ⟨s2, a1⟩ ⟨z, hz, hIR2, hSRT2⟩
  apply (WP.spec_ok _).2
  exact ⟨rfl, z, hz, (SRT.relTop ⟨hIR2, hSRT2⟩).1, hIR2, hSRT2⟩

set_option maxHeartbeats 8000000 in
/-- `reply_tail_inv` with its facts at the post-restart state. -/
theorem reply_tail_invS (hH : IpcSchedHyps st ar N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBf : EpBufHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBm : EpBufMapHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hP0 : IPlaced N T E R B) (hRH : ReplyHyps st ar th cr N T C E R B c)
    (hTl : IpcEpTailHyps st A N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hmb : ∀ a : A, sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ)
    {ct : U64} (hct : ct ∈ T) (hcur : σ.curThread = ct.bv) {xt : Fl4Spec.Tcb} (hkt : σ.kheap ct.bv = some (.tcb xt))
    (hrun : tsCode xt.tcbState < 3) (hft : xt.tcbFault = none)
    {σ1 : Fl4Spec.State Unit} (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    {p : U64} (hp : p ∈ R) (g : Bool) (hF : Sched.SchedValid σ1 ∧ Sched.ObjCover N T E R C σ1) :
    (do
      let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
      let (s2, a1) ← ipc.do_reply_transfer st ar s1 a ct p g
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1)) ⦃ r => r.1 = .Ok () ∧
      ∃ z ∈ (Fl4Spec.doReplyTransfer (Z := Unit) σ1.curThread p.bv g σ1).1,
        RelTopM (L := L) r.2.1 z.2 ∧ IRel st th cr N T C E R B c r.2.1 z.2 ⦄ := by
  obtain ⟨hIR, hSRT⟩ := hX
  have hSB := IpcRel.toSRN hIR hSRT
  have hsteps := IpcSchedHyps.stepsG (A := A) hH hBf hBm hP0
  obtain ⟨xt0, hk0, hTR⟩ := hIR.tcb ct hct
  rw [hkt] at hk0; cases hk0
  have hq := IpcRel.not_ep_queued hIR (t := ct) (by rw [hTR.st]; omega)
  have hcode : sched.TS_RESTART.val = tsCode .restart := by unfold sched.TS_RESTART; rfl
  obtain ⟨s1, hs1, hE1, hS1⟩ := spec_exists (hsteps.sts hP0.e s σ hIR.toE hSB hct hkt hq (show tsCode xt.tcbState ≠ 6 by omega) .restart
    (by decide) sched.TS_RESTART hcode)
  rw [hs1]
  simp only [bind_ok]
  rw [hcur, Notif.setThreadState_eq .restart hkt] at hst
  have hσ1 : σ1 = stsAct (updK σ ct.bv (.tcb { xt with tcbState := .restart })) ct.bv := by
    have := congrArg (fun q => ((), σ1) ∈ q.1) hst
    simp only [Set.mem_singleton_iff, Prod.mk.injEq, true_and] at this
    simpa using this.symm
  subst hσ1
  obtain ⟨hIR1, hSRT1⟩ := IpcRel.ofSRN hE1 hS1
  have hX1 : IRel st th cr N T C E R B c s1 _ := ⟨hIR1, hSRT1⟩
  have hkt1 : (stsAct (updK σ ct.bv (.tcb { xt with tcbState := .restart })) ct.bv).kheap ct.bv =
      some (.tcb { xt with tcbState := .restart }) := by rw [stsAct_kheap]; simp
  have hc1 : (stsAct (updK σ ct.bv (.tcb { xt with tcbState := .restart })) ct.bv).curThread = ct.bv := by
    unfold stsAct; split_ifs <;> exact hcur
  refine WP.spec_bind (do_reply_transfer_top hH hBf hBm hP0 hRH hTl hmb s1 a _ hX1 hF.1 hF.2 hct hkt1
    hft (by simp [tsCode]) hp g) ?_
  rintro ⟨s2, a1⟩ ⟨z, hz, hIR2, hSRT2⟩
  apply (WP.spec_ok _).2
  exact ⟨rfl, z, by rw [hc1]; exact hz, (SRT.relTop ⟨hIR2, hSRT2⟩).1, hIR2, hSRT2⟩

end

end

end Fl4Proofs.P3.Endp

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P1 Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- **An IPC leaf from `JAtZ`**: `XTopAt` and `IRel` at `JAtZ`'s sets. -/
theorem xleaf_of_irelJ {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {prog : Result ((core.result.Result Unit error.Exc) × S × A)} {spec : Set (Unit × Fl4Spec.State Unit) × Prop}
    (hI : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ → prog ⦃ r => r.1 = .Ok () ∧
      ∃ z ∈ spec.1, RelTopM (L := L) r.2.1 z.2 ∧
        IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c r.2.1 z.2 ⦄)
    (hAk : ∀ cr, AR a cr → prog ⦃ r => AR r.2.2 cr ⦄) :
    XLeaf (L := L) (XTop (L := L) AR) s a σ prog spec := by
  intro _
  refine WP.spec_mono (xtopAt_of_irel J.xtop J.ks J.buf hI hAk) ?_
  rintro r ⟨h1, z, hz, hRT, ⟨Z', -, -, -, -, -, -, -, -, hZ'⟩, -⟩
  exact ⟨h1, z, hz, hRT, Z', hZ'⟩

/-- `QSorted` of the endpoints from `JAtZ` (`IpcSorted`). -/
theorem JAtZ.qsortedE {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : QSorted st Z.T Z.E s := by
  have hI := J.xtop.irelK J.ks J.buf
  have hQ := Sched.qSorted_of_spec (L := L) hI.1.toE hI.1.toN J.ip.e.tcb J.isorted
  exact fun e he => hQ e (Or.inl he)

set_option maxHeartbeats 4000000 in
/-- **`IpcVsFrame` for an endpoint cap with the send right, from `JAtZ`**
(`ipcVsFrame_endpoint` re-scoped): `send_tail_topS` with `SchedValid` and
`QSorted` from `JAtZ` after the caller's restart (`jat_restart`). Named:
`IpcZ` at `JAtZ`'s sets (the IPC tails' bundles), the endpoint in `Z.E`,
`SendRest` at `JAtZ` after the restart (the donating send), the arch
relation by `ARKeep` [P]. -/
theorem ipcVsFrame_endpointJ {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {ar : A} {σ σ1 : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hJS : JStepHyps (L := L) arI AR Z.th)
    {ct : U64} (hcur : σ.curThread = ct.bv) {xt : Fl4Spec.Tcb} (hkt : σ.kheap ct.bv = some (.tcb xt))
    (hrun : tsCode xt.tcbState < 3) (hft : xt.tcbFault = none)
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (blk call don : Bool) (p b : U64) (rv g gr : Bool)
    (hz : IpcZ (L := L) arI σ.archState.x64CurrentCr3 s σ ct Z) (hp : p ∈ Z.E)
    (hU : ∀ s1 Ac' Lst' D', JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' s1 ar σ1 →
      SendRest st arI (IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c) Z.T s1 ar σ1 blk call b
        g gr don ct p)
    (hS : P0.StoreTotal st) (hA : P0.ArchTotal arI) (hK : ARKeep arI AR) :
    IpcVsFrame (L := L) arI AR s ar σ σ1 ct blk call don (.Endpoint p b true rv g gr) := by
  have hst' := hst
  rw [hcur] at hst'
  exact xleaf_of_irelJ J (fun hI => send_tail_topS hz.H hz.Bf hz.Bm hz.Tl hz.P s ar σ hI hz.ct hcur hkt hrun hft hst
    hp b blk call g gr don fun s1 hs1 => by
      obtain ⟨Ac', Lst', D', J'⟩ := jat_restart J hJS hcur hs1 hst'
      exact ⟨J'.sv, J'.qsortedE, hU s1 Ac' Lst' D' J'⟩)
    (fun _ h => AK.send_tail hS hA hK h)

set_option maxHeartbeats 4000000 in
/-- **`IpcVsFrame` for a notification cap with the send right, from
`JAtZ`** (`ipcVsFrame_notification` re-scoped). Named: `IpcZ`, the
notification in `Z.N`, no thread `RunningVM` (`NativeScope`, FL4 has no
VT-x path) after the caller's restart, `ARKeep` [P]. -/
theorem ipcVsFrame_notificationJ {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {ar : A} {σ σ1 : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    {ct : U64} (hcur : σ.curThread = ct.bv) {xt : Fl4Spec.Tcb} (hkt : σ.kheap ct.bv = some (.tcb xt))
    (hrun : tsCode xt.tcbState < 3)
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (blk call don : Bool) (p b : U64) (rv : Bool)
    (hz : IpcZ (L := L) arI σ.archState.x64CurrentCr3 s σ ct Z) (hp : p ∈ Z.N) (hvm : NativeScope σ1)
    (hS : P0.StoreTotal st) (hA : P0.ArchTotal arI) (hK : ARKeep arI AR) :
    IpcVsFrame (L := L) arI AR s ar σ σ1 ct blk call don (.Notification p b true rv) :=
  xleaf_of_irelJ J (fun hI => send_tail_ntfnS hz.H hz.Bf hz.Bm hz.P s ar σ hI hz.ct hcur hkt hrun hst hp b hvm)
    (fun _ h => AK.signal_tail hS hA hK h)

set_option maxHeartbeats 4000000 in
/-- **`IpcVsFrame` for a reply cap, from `JAtZ`** (`ipcVsFrame_reply`
re-scoped): `reply_tail_invS` with `SchedValid` and `ObjCover` from `JAtZ`
after the caller's restart. Named: `IpcZ`, `ReplyHyps`, `min_budget` [P], the
reply in `Z.R`, `ARKeep` [P]. -/
theorem ipcVsFrame_replyJ {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {ar : A} {σ σ1 : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hJS : JStepHyps (L := L) arI AR Z.th)
    {ct : U64} (hcur : σ.curThread = ct.bv) {xt : Fl4Spec.Tcb} (hkt : σ.kheap ct.bv = some (.tcb xt))
    (hrun : tsCode xt.tcbState < 3) (hft : xt.tcbFault = none)
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (blk call don : Bool) (p : U64) (g : Bool)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hz : IpcZ (L := L) arI σ.archState.x64CurrentCr3 s σ ct Z)
    (hRH : ReplyHyps st arI Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c) (hp : p ∈ Z.R)
    (hS : P0.StoreTotal st) (hA : P0.ArchTotal arI) (hK : ARKeep arI AR) :
    IpcVsFrame (L := L) arI AR s ar σ σ1 ct blk call don (.Reply p g) := by
  have hst' := hst
  rw [hcur] at hst'
  obtain ⟨-, x, hk⟩ := J.xtop.curTcb hcur
  have hrn : Fl4Spec.runnable x.tcbState = true := J.curRun x (by rw [hcur]; exact hk)
  obtain ⟨s1, hs1, -⟩ := spec_exists (XTopAt.restart J.xtop hcur hk hrn)
  obtain ⟨Ac', Lst', D', J'⟩ := jat_restart J hJS hcur hs1 hst'
  exact xleaf_of_irelJ J (fun hI => reply_tail_invS hz.H hz.Bf hz.Bm hz.P hRH hz.Tl hmb s ar σ hI hz.ct hcur hkt hrun
    hft hst hp g ⟨J'.sv, J'.obj⟩) (fun _ h => AK.reply_tail hS hA hK h)

end

end

end Fl4Proofs.P3
