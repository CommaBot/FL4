/-
P3 (DESIGN.md §9), TCB invocations: **the SetPriority, BindNotification and
UnbindNotification leaves at `XTop`** (XTopTcbSched's `SetPrioXLeaf`,
`BindXLeaf`, `UnbindXLeaf`), from `set_priority_irel` (IpcSetPrio) and
`bound_wr_irel` (IpcTcbBind).

* `xleaf_restart`: the generic leaf after the caller's restart
  (`XTopAt.restart`, `IRel` by `XTopAt.irelK`, back by `IRel.xtop`).

* `SetPrioOK`: what `set_priority_irel` needs beyond `IRel` at the state
  after the caller's restart (l4v `valid_sched` and `valid_objs`): the current
  thread in no release queue, `SchedValid`, `Inv`, `ObjCover`, the endpoint
  and notification queues sorted.
* `setPrioXLeaf_of`: `xleaf_restart` with `set_priority_irel`.
* `unbindXLeaf_of`, `bindXLeaf_of`: `xleaf_restart` with `bound_wr_irel`;
  `bindXLeaf_of` names the notification non-null (l4v `valid_cap`).
-/
import Fl4Proofs.P3.IpcSetPrio
import Fl4Proofs.P3.IpcTcbBind
import Fl4Proofs.P3.XTopTcbSched
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-- **What SetPriority's scheduler step needs beyond `IRel`** [J] (l4v
`valid_sched`: `ct_not_in_release_q`, `valid_queues`; `sym_refs`; the queues
ordered by priority): for the target `p`. -/
def SetPrioOK (st : machine.Store S) [L : P1.LawfulStore st] (Z : XSets) (p : U64) (s : S)
    (σ : Fl4Spec.State Unit) : Prop :=
  (σ.curThread = p.bv → p.bv ∉ σ.releaseQueue) ∧ SchedValid σ ∧ Inv σ ∧ ObjCover Z.N Z.T Z.E Z.R Z.C σ ∧
    QSorted st Z.T Z.E s ∧ QSorted st Z.T Z.N s

set_option maxHeartbeats 4000000 in
/-- **A TCB leaf after the caller's restart, on `IRel`**: the restart
(`XTopAt.restart`), `IRel` at every `Z` by `XTopAt.irelK` (`KsApart` at the
entry, `BufWordRel` at `XTopAt`), the rest on `IRel` keeping the arch
relation, back by `IRel.xtop`. -/
theorem xleaf_restart {AR : A → Fl4Spec.Cr3 → Prop} {s : S} {ar : A} {σ σ1 : Fl4Spec.State Unit}
    {g : S → Result ((core.result.Result Unit error.Exc) × S × A)} {spec : Set (Unit × Fl4Spec.State Unit) × Prop}
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False)) (hC : CurRun σ)
    (hKA : ∀ Z : XSets, XTopAt (L := L) AR Z s ar σ → KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s))
    (hBW : ∀ (Z : XSets) s' a' σ', XTopAt (L := L) AR Z s' a' σ' → BufWordRel Z.T (L.mem s') σ')
    (hI : ∀ (Z : XSets) (s1 : S), XTopAt (L := L) AR Z s ar σ → L.ksb s1 = L.ksb s →
      (∀ q y, σ1.kheap q = some (.tcb y) → ∃ y0, σ.kheap q = some (.tcb y0) ∧ y = { y0 with tcbState := y.tcbState }) →
      IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s1 σ1 →
      g s1 ⦃ r => r.1 = .Ok () ∧ AR r.2.2 σ.archState.x64CurrentCr3 ∧ ∃ z ∈ spec.1,
        IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c r.2.1 z.2 ⦄) :
    XLeaf (L := L) (XTop (L := L) AR) s ar σ (do
      let s1 ← tcb.restart_caller st s
      g s1) spec := by
  rintro ⟨Z, hX⟩
  have hSch := hX.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hSch.lists
  set ct := L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) with hctd
  have hcur : σ.curThread = ct.bv := by rw [hs.curThread, hctd, hc.cur]; rfl
  obtain ⟨-, x, hk⟩ := hX.curTcb hcur
  have hrun : Fl4Spec.runnable x.tcbState = true := hC x (by rw [hcur]; exact hk)
  have hσ1 : σ1 = Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv := by
    rw [hcur, Notif.setThreadState_eq .restart hk] at hst
    have := congrArg (fun q => ((), σ1) ∈ q.1) hst
    simp only [Set.mem_singleton_iff, Prod.mk.injEq, true_and] at this
    exact of_eq_true this
  subst hσ1
  have hcr : (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv).archState.x64CurrentCr3 =
      σ.archState.x64CurrentCr3 := by
    unfold Notif.stsAct; split <;> rfl
  unfold tcb.restart_caller
  step with P1.sched.cur_thread.spec as ⟨ct', hct'⟩
  subst hct'
  refine WP.spec_bind (XTopAt.restart hX hcur hk hrun) ?_
  rintro s1 ⟨hX1, -, hks1⟩
  have hI1 := hX1.irelK (by rw [hks1]; exact hKA Z hX) (hBW _ _ _ _ hX1)
  rw [hcr] at hI1
  have hkeep : ∀ q y, (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv).kheap q =
      some (.tcb y) → ∃ y0, σ.kheap q = some (.tcb y0) ∧ y = { y0 with tcbState := y.tcbState } := by
    intro q y hq
    rw [Notif.stsAct_kheap] at hq
    by_cases e : q = ct.bv
    · subst e; simp [Notif.updK] at hq; subst hq; exact ⟨x, hk, rfl⟩
    · simp only [Notif.updK, Function.update_of_ne e] at hq; exact ⟨y, hq, rfl⟩
  refine WP.spec_mono (hI Z s1 hX hks1 hkeep hI1) ?_
  rintro r ⟨h1, hAR, z, hz, hI2⟩
  obtain ⟨⟨Z', -, -, -, -, -, -, -, -, hZ'⟩, -⟩ := IRel.xtop (L := L) (AR := AR) (a := r.2.2) hI2 hAR
  exact ⟨h1, z, hz, (SRT.relTop hI2).1, Z', hZ'⟩

/-- **`SetPrioXLeaf`** (module docstring). Named, at every `Z` the entry's
`XTopAt` holds at: `KsApart`, the IPC placement, the target among the TCBs,
`ActReady` on `IRel` [J], `SetPrioOK` on `IRel`; `BufWordRel` at `XTopAt`
(as XTopTcbSched's `hBT`); the caller runnable (`CurRun`) [J]. -/
theorem setPrioXLeaf_of {AR : A → Fl4Spec.Cr3 → Prop} {s : S} {ar : A} {σ σ1 : Fl4Spec.State Unit} {p v : U64}
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False)) (hv : v.val < 256)
    (hC : CurRun σ)
    (hZ : ∀ Z : XSets, XTopAt (L := L) AR Z s ar σ → KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s) ∧
      IPlaced Z.N Z.T Z.E Z.R Z.B ∧ p ∈ Z.T ∧
      (∀ s' σ', IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ' → Notif.ActReady σ') ∧
      (∀ s' σ', IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ' → SetPrioOK st Z p s' σ'))
    (hBW : ∀ (Z : XSets) s' a' σ', XTopAt (L := L) AR Z s' a' σ' → BufWordRel Z.T (L.mem s') σ') :
    SetPrioXLeaf (L := L) AR s ar σ σ1 p v := by
  refine xleaf_restart hst hC (fun Z hX => (hZ Z hX).1) hBW fun Z s1 hX _ hkp hI1 => ?_
  obtain ⟨-, hP0, hpT, hAct, hOK⟩ := hZ Z hX
  have hAR : AR ar σ.archState.x64CurrentCr3 := hX.fin.1.1.2.2.2.2.2.2
  obtain ⟨hRel, hSV, hInv, hOC, hSE, hSN⟩ := hOK _ _ hI1
  refine WP.spec_bind (set_priority_irel hP0 hI1 hpT v hv (hAct _ _ hI1) hRel hSV hInv hOC hSE hSN) ?_
  rintro s2 ⟨σ2, hm, hI2⟩
  simp only [WP.spec_ok]
  exact ⟨trivial, hAR, ((), σ2), by rw [hm]; exact Set.mem_singleton _, hI2⟩

/-- The bound notification of a TCB on `IRel` (l4v `valid_objs`: the object
exists, `ObjCover`: it is tracked): from the TCB's bound word. -/
theorem bound_ntfn_of {Z : XSets} {cr : Fl4Spec.Cr3} {s : S} {σ : Fl4Spec.State Unit}
    (hI : IRel st Z.th cr Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ) (hSV : SchedValid σ) (hOC : ObjCover Z.N Z.T Z.E Z.R Z.C σ)
    {p : U64} (hp : p ∈ Z.T) (h0 : L.mem s (P1.boundA p) ≠ 0#u64) :
    ∃ x xn, σ.kheap p.bv = some (.tcb x) ∧ x.tcbBoundNotification = some (L.mem s (P1.boundA p)).bv ∧
      L.mem s (P1.boundA p) ∈ Z.N ∧ σ.kheap (L.mem s (P1.boundA p)).bv = some (.notification xn) := by
  obtain ⟨x, hk, hx⟩ := hI.1.tcb p hp
  have hb : x.tcbBoundNotification = some (L.mem s (P1.boundA p)).bv := by
    rw [hx.bound, show tBoundA p = P1.boundA p from rfl]; exact Notif.optRef_ne h0
  obtain ⟨xn, hkn⟩ := hSV.tcbNtfn _ _ _ hk hb
  obtain ⟨n', hn', e⟩ := hOC.ntfn _ xn hkn
  have : n' = L.mem s (P1.boundA p) := P1.eq_of_bv e
  subst this
  exact ⟨x, xn, hk, hb, hn', hkn⟩

/-- **`UnbindXLeaf`**: the restart (`xleaf_restart`), the two bound words
(`bound_wr_irel`). Named, at every `Z`: `KsApart`, the IPC placement, the
target among the TCBs, `SchedValid` and `ObjCover` on `IRel` [J];
`BufWordRel` at `XTopAt`; `CurRun` [J]. -/
theorem unbindXLeaf_of {AR : A → Fl4Spec.Cr3 → Prop} {s : S} {ar : A} {σ σ1 : Fl4Spec.State Unit} {p : U64}
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False)) (hC : CurRun σ)
    (hb0 : L.mem s (P1.boundA p) ≠ 0#u64)
    (hZ : ∀ Z : XSets, XTopAt (L := L) AR Z s ar σ → KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s) ∧
      IPlaced Z.N Z.T Z.E Z.R Z.B ∧ p ∈ Z.T ∧
      (∀ s' σ', IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ' →
        SchedValid σ' ∧ ObjCover Z.N Z.T Z.E Z.R Z.C σ'))
    (hBW : ∀ (Z : XSets) s' a' σ', XTopAt (L := L) AR Z s' a' σ' → BufWordRel Z.T (L.mem s') σ') :
    UnbindXLeaf (L := L) AR s ar σ σ1 p := by
  refine xleaf_restart hst hC (fun Z hX => (hZ Z hX).1) hBW fun Z s1 hX _ hkp hI1 => ?_
  obtain ⟨hKA, hP0, hpT, hJ⟩ := hZ Z hX
  have hAR : AR ar σ.archState.x64CurrentCr3 := hX.fin.1.1.2.2.2.2.2.2
  -- the bound word survives the restart
  have hI0 := hX.irelK hKA (hBW _ _ _ _ hX)
  obtain ⟨x0, hk0, hx0⟩ := hI0.1.tcb p hpT
  obtain ⟨x1, hk1, hx1⟩ := hI1.1.tcb p hpT
  have hb1 : L.mem s1 (P1.boundA p) ≠ 0#u64 := by
    intro h0
    have e1 : x1.tcbBoundNotification = none := by
      rw [hx1.bound]; show Notif.optRef (L.mem s1 (P1.boundA p)) = none; rw [h0]; rfl
    have e0 : x0.tcbBoundNotification ≠ none := by
      rw [hx0.bound, show tBoundA p = P1.boundA p from rfl, Notif.optRef_ne hb0]; simp
    -- `σ1` is the restart of `σ`: the bound field is kept
    obtain ⟨y0, hy0, ey⟩ := hkp _ _ hk1
    rw [hk0] at hy0; cases hy0
    exact e0 (by rw [ey] at e1; exact e1)
  obtain ⟨hSV, hOC⟩ := hJ _ _ hI1
  obtain ⟨x, xn, hk, hb, hn, hkn⟩ := bound_ntfn_of hI1 hSV hOC hpT hb1
  have hX2 := bound_wr_irel hP0 hI1 hpT hn hk hkn 0#u64 0#u64 (fun h => absurd rfl h)
  rw [Notif.optRef_zero] at hX2
  rw [Sched.unbind_ntfn_eq s1 p hb1]
  simp only [bind_ok, WP.spec_ok]
  refine ⟨trivial, hAR, ((), _), ?_, hX2⟩
  rw [Sched.unbindNotification_eq hkn hk hb]
  exact Set.mem_singleton _

/-- **`BindXLeaf`**: the restart (`xleaf_restart`), the two bound words
(`bound_wr_irel`). Named, at every `Z`: `KsApart`, the IPC placement, the
target among the TCBs, the notification `q` among the notifications and not
at address 0 [J] (l4v `valid_cap`); `BufWordRel` at `XTopAt`; `CurRun` [J]. -/
theorem bindXLeaf_of {AR : A → Fl4Spec.Cr3 → Prop} {s : S} {ar : A} {σ σ1 : Fl4Spec.State Unit} {p q : U64}
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False)) (hC : CurRun σ)
    (hZ : ∀ Z : XSets, XTopAt (L := L) AR Z s ar σ → KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s) ∧
      IPlaced Z.N Z.T Z.E Z.R Z.B ∧ p ∈ Z.T ∧ q ∈ Z.N ∧ q ≠ 0#u64)
    (hBW : ∀ (Z : XSets) s' a' σ', XTopAt (L := L) AR Z s' a' σ' → BufWordRel Z.T (L.mem s') σ') :
    BindXLeaf (L := L) AR s ar σ σ1 p q := by
  refine xleaf_restart hst hC (fun Z hX => (hZ Z hX).1) hBW fun Z s1 hX _ hkp hI1 => ?_
  obtain ⟨hKA, hP0, hpT, hqN, hq0⟩ := hZ Z hX
  have hAR : AR ar σ.archState.x64CurrentCr3 := hX.fin.1.1.2.2.2.2.2.2
  obtain ⟨x, hk, -⟩ := hI1.1.tcb p hpT
  obtain ⟨xn, hkn, -⟩ := hI1.1.ntfn q hqN
  have hp0 : p ≠ 0#u64 := fun e => (hP0.e.tcb p hpT).ne0 (by rw [e]; rfl)
  have hX2 := bound_wr_irel hP0 hI1 hpT hqN hk hkn p q (fun _ => hpT)
  rw [Notif.optRef_ne hp0, Notif.optRef_ne hq0] at hX2
  rw [Sched.bind_ntfn_eq s1 p q]
  simp only [bind_ok, WP.spec_ok]
  refine ⟨trivial, hAR, ((), _), ?_, hX2⟩
  rw [Sched.bindNotification_eq hkn hk]
  exact Set.mem_singleton _

end

end

end Fl4Proofs.P3
