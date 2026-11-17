/-
P3 (DESIGN.md §9): **producers of [J] premises from `JAtZ`** (issue #16's
"[J] producers"). Each named premise tagged [J] whose content is a
conjunction of facts `JAtZ` already carries gets a producer here:

* the caps in the typed heap's slots name objects of the sets
  (`JAtZ.slotN`, `slotE`, `slotR`, `slotT`: P1's `CapTyped` through
  `JPlaced.typed` and `JAtZ.hset`, the CSpace relation's `CapValid` with
  `JAtZ.thT`), and the sets' TCBs are the typed heap's (`JAtZ.thOfT`:
  `JPlaced.tcb` with `JAtZ.zH`);
* `NtfnFinPre` (`JAtZ.ntfnFinPre`) and `EpFinPre` (`JAtZ.epFinPre`) in full;
* `ReplyFinPre` (`JAtZ.replyFinPre`) and `ThreadFinPre`
  (`JAtZ.threadFinPre`) but for their "at every `IRel` state" parts, which
  are not state facts;
* `ScFinPreX` (`JAtZ.scFinPreX`) from the narrower `ScCapJ` [J] (the SC cap's
  object exists in the spec, is not the idle SC, and its bound thread is not
  the idle thread: what `JAtZ` lacks);
* the vtable-ASID premise `hVt` of `jat_scheduleT2` / `jat_scheduleF` /
  `jat_scheduleS` from the narrower `VtAsidJ` [J] (`hVt_ofT2`, `hVt_ofF`):
  its first half (the sets' TCBs in the typed heap) is `JAtZ.thOfT`.

The consumers of `NtfnFinPre` .. `ScFinPreX` (`xFinNtfn_of` etc.) quantify
over every `XTopAt` state of the typed heap (the `XFinHyps` [W] shape), not
over `JAtZ` states, so these producers discharge them only once the
finalisation premises are re-scoped to the states the deletion loop carries.
-/
import Fl4Proofs.P3.XTopJointFin
import Fl4Proofs.P3.IpcCancelAllIpc
import Fl4Proofs.P3.IpcFinReply
import Fl4Proofs.P3.XTopFinThread
import Fl4Proofs.P3.IpcTcbJAll
import Fl4Proofs.P3.ScSchTailP1
import Fl4Proofs.P3.XTopJoint
import Fl4Proofs.P3.IpcSuspendJ
import Fl4Proofs.P3.IpcCapJ
import Fl4Proofs.P3.IpcResume
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P1 Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc
  Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-! ## The slots' caps and the sets -/

/-- The sets' TCBs are the typed heap's (`JPlaced.tcb`, `JAtZ.zH`). -/
theorem JAtZ.thOfT (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) :
    Z.th t = some .tcb := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  exact (hJ.tcb t).2 (J.zH.1 t ht)

/-- A notification cap in a slot names one of the notifications, not 0. -/
theorem JAtZ.slotN (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {sl : Fl4Spec.CslotPtr}
    (hA : AbsSlot Z.th sl) {p b : U64} {w r : Bool}
    (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Notification p b w r)) : p ∈ Z.N ∧ p ≠ 0#u64 :=
  J.capN ⟨cslotAddr sl, b, w, r, hA.isSlot, capV_of_capAt hc⟩

/-- An endpoint cap in a slot names one of the endpoints (`CapTyped`, `hset`). -/
theorem JAtZ.slotE (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {sl : Fl4Spec.CslotPtr}
    (hA : AbsSlot Z.th sl) {e b : U64} {x1 x2 x3 x4 : Bool}
    (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Endpoint e b x1 x2 x3 x4)) : e ∈ Z.E := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  exact J.hset.1 e ((hJ.typed _ hA.isSlot).1 e b x1 x2 x3 x4 (capV_of_capAt hc))

/-- A reply cap in a slot names one of the replies (`CapTyped`, `hset`). -/
theorem JAtZ.slotR (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {sl : Fl4Spec.CslotPtr}
    (hA : AbsSlot Z.th sl) {p : U64} {g : Bool}
    (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Reply p g)) : p ∈ Z.R := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  exact J.hset.2.2 p ((hJ.typed _ hA.isSlot).2.2 p g (capV_of_capAt hc))

/-- A thread cap in a slot names one of the TCBs (`CapValid`, `thT`). -/
theorem JAtZ.slotT (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {sl : Fl4Spec.CslotPtr}
    (hA : AbsSlot Z.th sl) {p : U64}
    (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Thread p)) : p ∈ Z.T :=
  J.thT p (J.xtop.rel.2.1.2.1.abs hA hc)

/-! ## The finalisation premises -/

/-- **`NtfnFinPre` from `JAtZ`**. -/
theorem JAtZ.ntfnFinPre (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : NtfnFinPre (L := L) Z s σ := by
  refine ⟨J.buf, J.ip, J.nsc, fun n hn => J.ntfn_link hn, fun n hn => ?_,
    fun _ _ _ _ _ hA hc => (J.slotN hA hc).1⟩
  obtain ⟨xn, hkn, -⟩ := J.xtop.ipc.ntfn n hn
  exact ntfnPre_of_valid J.inv J.inv.actReady J.sv ⟨xn, hkn⟩

/-- **`EpFinPre` from `JAtZ`**. -/
theorem JAtZ.epFinPre (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : EpFinPre (L := L) Z s σ := by
  refine ⟨J.buf, J.ip, fun e he => ?_, fun _ _ _ _ _ _ _ hA hc => J.slotE hA hc⟩
  obtain ⟨x, hk, -⟩ := J.xtop.ipc.ep e he
  exact epPre_of_valid J.inv J.inv.actReady J.sv ⟨x, hk⟩

/-- **`ReplyFinPre` from `JAtZ`**, but for its two parts quantified over
every `IRel` state (`RemoveOK`, `BlockedScActive` there), which are not
facts of one state. -/
theorem JAtZ.replyFinPre (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hD : ∀ s' σ' (r t : U64), IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ' →
      r ∈ Z.R → t ∈ Z.T → RemoveOK st Z.N Z.T Z.C Z.R Z.c s' σ' r t)
    (hB : ∀ s' σ', IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ' →
      BlockedScActive σ') :
    ReplyFinPre (L := L) Z s σ :=
  ⟨J.buf, J.ip, hD, hB, J.sv, J.obj, J.inv, fun _ _ xr t hk ht => J.sv.replyTcb _ xr t hk ht,
    fun _ _ _ hA hc => J.slotR hA hc⟩

/-- **`ThreadFinPre` from `JAtZ`**, but for its two parts quantified over
every `IRel` state (`RemoveTcbHyp`, `YieldRel` there). -/
theorem JAtZ.threadFinPre (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hRT : ∀ cr, RemoveTcbHyp st Z.th cr Z.N Z.T Z.C Z.E Z.R Z.B Z.c)
    (hY : ∀ cr s' σ', IRel st Z.th cr Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ' → YieldRel Z.T Z.C (L.mem s') σ') :
    ThreadFinPre (L := L) Cs Z s σ :=
  ⟨J.ks, J.buf, J.nk, J.ip, J.sv, J.obj, J.inv, J.nsc, J.otherTmOK, hRT, hY⟩

/-- **[J] What `JAtZ` lacks of `ScFinPreX`**: an SC cap in a slot names an
SC of the spec (l4v `valid_cap`), not the idle SC (l4v
`valid_global_refs`: no cap to the idle SC), whose bound thread is not the
idle thread (l4v `sym_refs` between an SC and its TCB, with the idle
thread bound to the idle SC). -/
def ScCapJ (Z : XSets) (s : S) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ sl p sb, AbsSlot Z.th sl → capAt (L.mem s) (cslotAddr sl) = ok (.SchedContext p sb) →
    (∃ y n, σ.kheap p.bv = some (.schedContext y n)) ∧ p.bv ≠ Fl4Spec.idleScPtr ∧
    ∀ y n, σ.kheap p.bv = some (.schedContext y n) → ∀ t, y.scTcb = some t → t ≠ σ.idleThread

/-- **`ScFinPreX` from `JAtZ` and `ScCapJ`**: the SC among the SCs by
`ObjCover`, non-null by `JAtZ.c0`, its bound thread and notification among
the sets by `SchedValid`'s links and `ObjCover`. -/
theorem JAtZ.scFinPreX (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hSC : ScCapJ (L := L) Z s σ) :
    ScFinPreX (L := L) Z s σ := by
  refine ⟨J.ip, J.nsc, J.inv, ⟨Lst, J.call, J.rp, J.rfree⟩, fun sl p sb hA hc => ?_⟩
  obtain ⟨⟨y0, n0, hk0⟩, hpi, hidle⟩ := hSC sl p sb hA hc
  obtain ⟨q, hq, hqp⟩ := J.obj.sc _ y0 n0 hk0
  have hpq : q = p := P1.eq_of_bv hqp
  subst hpq
  refine ⟨hq, J.c0 q hq, hpi, fun y n hk => ⟨fun t ht => ?_, fun m hm => ?_⟩⟩
  · obtain ⟨x, hx⟩ := J.sv.scTcb _ y n _ hk ht
    obtain ⟨t', ht', htt⟩ := J.obj.tcb _ x hx
    have : t' = t := P1.eq_of_bv htt
    subst this
    exact ⟨ht', hidle y n hk _ ht⟩
  · obtain ⟨xn, hxn⟩ := J.sv.scNtfn _ y n _ hk hm
    obtain ⟨m', hm', hmm⟩ := J.obj.ntfn _ xn hxn
    have : m' = m := P1.eq_of_bv hmm
    subst this
    exact hm'

/-! ## The TCB leaves' state facts -/

/-- `QSorted` of the notifications from `JAtZ` (`IpcSorted`; as `JAtZ.qsortedE`). -/
theorem JAtZ.qsortedN (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : QSorted st Z.T Z.N s := by
  have hI := J.xtop.irelK J.ks J.buf
  have hQ := Sched.qSorted_of_spec (L := L) hI.1.toE hI.1.toN J.ip.e.tcb J.isorted
  exact fun n hn => hQ n (Or.inr hn)

/-! ## The vtable-ASID premise of `jat_schedule*` -/

/-- **[J] The vtable ASID** (issue #16's vtable-ASID fact; what `hVt` of
`jat_scheduleF`/`jat_scheduleS` asks beyond `JAtZ`): at the `JAtZ` states,
a TCB's mapped PML4 vtable cap has a non-zero ASID (l4v `valid_cap` of the
arch caps, `VCapOK`'s `.Pml4` clause, at the TCBs' vtable slots; `JAtZ`
carries neither `VsCapsIn` nor the vtable slots in the ghost tree). -/
def VtAsidJ (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) :
    Prop :=
  ∀ (V1 : XVs) (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (Ac1 : Set U64) (Lst1 : U64 → List U64)
    (D1 : Set U64), JAtZ (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s1 a1 σ1 → ∀ t ∈ Z.T,
      ∀ p asid, capAt (L.mem s1) (slotOf t 1) = ok (.Pml4 p true asid) → asid ≠ 0#u64

/-- `hVt` of `jat_scheduleF` / `jat_scheduleS` from `VtAsidJ`. -/
theorem hVt_ofF (h : VtAsidJ (L := L) arI AR Z H Cs) :
    ∀ (V1 : XVs) (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (Ac1 : Set U64) (Lst1 : U64 → List U64)
      (D1 : Set U64), JAtZ (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s1 a1 σ1 → ∀ t ∈ Z.T,
        Z.th t = some .tcb ∧ ∀ p asid, capAt (L.mem s1) (slotOf t 1) = ok (.Pml4 p true asid) → asid ≠ 0#u64 :=
  fun V1 s1 a1 σ1 Ac1 Lst1 D1 J1 t ht => ⟨J1.thOfT ht, h V1 s1 a1 σ1 Ac1 Lst1 D1 J1 t ht⟩

/-- `hVt` of `jat_scheduleT2` from `VtAsidJ`. -/
theorem hVt_ofT2 (h : VtAsidJ (L := L) arI AR Z H Cs) :
    ∀ (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D1 : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac1 Lst1 D1 s1 a1 σ1 → ∀ t ∈ Z.T, Z.th t = some .tcb ∧
        ∀ p asid, capAt (L.mem s1) (slotOf t 1) = ok (.Pml4 p true asid) → asid ≠ 0#u64 :=
  fun s1 a1 σ1 Ac1 Lst1 D1 J1 => hVt_ofF h Z.vs s1 a1 σ1 Ac1 Lst1 D1 J1

end

end

end Fl4Proofs.P3
