/-
P3 (DESIGN.md §9), CSpace: **a final SC cap's finalisation at `J`**: its
premises and the readiness of its slot after (toward `jFinAt_sc`,
XTopJointDelR).

FL4's `finalise_cap_object` of a final SC cap runs `unbind_all_tcbs`,
`unbind_ntfn`, `unbind_reply`, the yielder's `complete_yield_to`, then
clears `REFILL_MAX` and `SPORADIC`; it never writes the current-SC word.

* `JAtZ.sc_ready`: an SC cap's slot is ready (`EmptyReady`) once the SC is
  dead (P1's `fin_cap_sc.dead`: its `TCB`, `REPLY` and `NTFN` words null),
  given the cap's size is the SC's (`JAtZ.scCap`).
* The SC may be the current SC (the invoking thread deleting or revoking the
  last cap to its own bound SC, or to the SC it runs on). seL4 and FL4 then
  leave `ksCurSC` naming the dead, inactive SC until the next `schedule`,
  whose `commit_time` skips an inactive SC. `JAtZ` allows it: unbinding the
  current thread asks for a reschedule (and `CurInv` cannot hold once the
  current SC has no thread, `Inv.back`), `OffOK` asks nothing of an inactive
  current SC, `EmptyReady` asks nothing of the current SC, and the current
  SC's liveness is derived (`JAtZ.cscLive`) only while no reschedule is
  pending.

What the finalisation reads of the SC cap's SC is derived:

* `jScCapHyp_of` (`JAtZ.scCap`): an SC cap in a slot names an SC of the
  spec of the cap's size (l4v `valid_cap`'s `obj_bits`), not the idle SC
  (l4v `valid_global_refs`): `JPlaced.cobj` (ScPlace's `CapObjH`: the
  cap's SC is `H`'s of its size and not the idle SC), `JAtZ.hscC` (`H`'s
  SCs are `Z.C`'s), the scheduler relation (each SC of `Z.C` the spec's)
  and `JPlaced.sc` (the spec SC's size `H`'s). The rest is
  `JAtZ.scCapFacts`: the SC one of `Z.C`, the pointer non-null (`c0`), its
  bound thread not the idle thread (`scBack_of`, `IdleOK`) and not the
  scheduler's switch target (P1's `fin_cap_sc` precondition): no switch is
  pending during a deletion (SpecNoSwitch's `NoSwitch`, l4v
  `simple_sched_action`, carried by the deletion loop's `WJ`; a premise of
  `JScFinHyp`).

* `JScFinHyp`: from `JAtZ`, FL4's `finalise_cap` of a final SC cap
  against the spec's, `JAtZ` after: **proved** from the steps
  (`jScFin_of`, `JAtZ.finScJ`, as XTop's `xFinSc_of`), the SC's links
  cleared and the current SC word kept between steps by P1's per-step
  lemmas, the slots and base by P1's `fin_cap_sc.slots`. Every SC step is
  proved: `JAtZ.unbindAllJ` (XTopJointFinScAll, through XTopJointFinThreadSc's
  `JAtZ.unbindTcbJ`, the current thread's reschedule included),
  `JAtZ.unbindNtfnJ`, `JAtZ.unbindReplyJ` (XTopJointFinScReply),
  `JAtZ.setInactiveJ`; only the yielder's step is a premise.
* `JYieldToHyp`, the yielder's `complete_yield_to` of an SC of the set:
  proved (`jYieldToHyp_of`, XTopJointYield's `JAtZ.completeYieldJ`) from the
  platform's `ticks_to_us` [P] (`JThreadFinHyps.ticks`, `yieldToH`).
-/
import Fl4Proofs.P3.XTopJointEmpty
import Fl4Proofs.P3.ScDeadStep
import Fl4Proofs.P3.XTopJointFinScAll
import Fl4Proofs.P3.SpecNoSwitch
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **An SC cap's object at `J`** (module docstring): the spec's SC of the
cap's size (l4v `valid_cap`'s `obj_bits`), not the idle SC (l4v
`valid_global_refs`). Proved: `jScCapHyp_of`. -/
def JScCapHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit), Z.th = th → JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ →
    ∀ (sl : Fl4Spec.CslotPtr) (p sb : U64), AbsSlot Z.th sl →
      capAt (L.mem s) (cslotAddr sl) = ok (.SchedContext p sb) →
      (∃ y n, σ.kheap p.bv = some (.schedContext y n) ∧ n + Fl4Spec.minSchedContextBits = sb.val) ∧
      p.bv ≠ Fl4Spec.idleScPtr

/-- **An SC cap names a spec SC of its size, not the idle SC** (l4v
`valid_cap`, `valid_global_refs`): the cap's SC is `H`'s of the cap's size
and not the idle SC (`JPlaced.cobj`), one of `Z.C` (`JAtZ.hscC`), so the
spec's (the scheduler relation's `scs`), whose size is `H`'s
(`JPlaced.sc`). -/
theorem JAtZ.scCap {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {sl : Fl4Spec.CslotPtr} {p sb : U64}
    (hA : AbsSlot Z.th sl) (hc : capAt (L.mem s) (cslotAddr sl) = ok (.SchedContext p sb)) :
    (∃ y n, σ.kheap p.bv = some (.schedContext y n) ∧ n + Fl4Spec.minSchedContextBits = sb.val) ∧
      p.bv ≠ Fl4Spec.idleScPtr := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hO := hJ.cobj _ hA.isSlot
  rw [capV_of_capAt hc] at hO
  obtain ⟨hH, hpi⟩ := hO
  have hpC : p ∈ Z.C := J.hscC p _ hH
  obtain ⟨Q, R, hc', hs⟩ := J.xtop.fin.1.1.1.lists
  obtain ⟨y, n, hk, -⟩ := hs.scs p hpC
  have hH' := (hJ.sc p y n (J.c0 p hpC) hk).2
  rw [hH] at hH'
  exact ⟨⟨y, n, hk, (HKind.sc.inj (Option.some.inj hH')).symm⟩, hpi⟩

/-- **`JScCapHyp` holds** (`JAtZ.scCap`). -/
theorem jScCapHyp_of (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : JScCapHyp (L := L) arI AR th :=
  fun _ _ _ _ _ _ _ _ _ _ J _ _ _ hA hc => J.scCap arI hA hc

/-- **What the finalisation reads of an SC cap's SC, from `JAtZ`** (with
`JAtZ.scCap`'s facts and the switch-target clause as `hC`): the SC is `H`'s of the cap's size (`JPlaced.sc`, the cap's
pointer non-null by `CapValid`) and one of `Z.C` (`ObjCover`); its bound
thread (one of `Z.T`, an SC's thread holding it: `scBack_of`) is not the
idle thread (`IdleOK`: the idle thread holds the idle SC) and, by the
switch-target clause, not the action word (`JAtZ.words_of_spec`). -/
theorem JAtZ.scCapFacts {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {sl : Fl4Spec.CslotPtr} {p sb : U64}
    (hA : AbsSlot Z.th sl) (hc : capAt (L.mem s) (cslotAddr sl) = ok (.SchedContext p sb))
    (hC : (∃ y n, σ.kheap p.bv = some (.schedContext y n) ∧ n + Fl4Spec.minSchedContextBits = sb.val) ∧
      p.bv ≠ Fl4Spec.idleScPtr ∧
      ∀ y n t, σ.kheap p.bv = some (.schedContext y n) → y.scTcb = some t →
        ∀ u, σ.schedulerAction = .switchThread u → u ≠ t) :
    H p = some (.sc sb.val) ∧ p ∈ Z.C ∧ p ≠ 0#u64 ∧
      (L.mem s (P1.scTcbA p) ≠ 0#u64 → L.actionW s ≠ L.mem s (P1.scTcbA p)) ∧
      (L.mem s (P1.scTcbA p) ≠ 0#u64 → L.idleW s ≠ L.mem s (P1.scTcbA p)) ∧
      (∃ y n, σ.kheap p.bv = some (.schedContext y n)) ∧ p.bv ≠ Fl4Spec.idleScPtr := by
  obtain ⟨⟨y, n, hk, hn⟩, hpi, hsa⟩ := hC
  have hp0 : p ≠ 0#u64 := J.xtop.rel.2.1.2.1.abs hA hc
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hHp : H p = some (.sc sb.val) := by rw [← hn]; exact (hJ.sc p y n hp0 hk).2
  have hpC : p ∈ Z.C := by
    obtain ⟨q, hq, hqp⟩ := J.obj.sc _ y n hk
    rw [← P1.eq_of_bv hqp]; exact hq
  have hpS : p ∈ P1.Heap.scs H := ⟨_, hHp⟩
  have hw : L.mem s (P1.scTcbA p) ≠ 0#u64 →
      L.actionW s ≠ L.mem s (P1.scTcbA p) ∧ L.idleW s ≠ L.mem s (P1.scTcbA p) := by
    intro h0
    obtain ⟨Q, R, hc', hs⟩ := J.xtop.fin.1.1.1.lists
    obtain ⟨y', n', hk', hx⟩ := hs.scs p hpC
    rw [hk] at hk'; cases hk'
    have hf : y.scTcb = some (L.mem s (P1.scTcbA p)).bv := by
      rw [hx.tcb, ← scTcbA_eq, Notif.optRef_ne h0]
    obtain ⟨u, huT, hu, x, hkx, hxs⟩ := scBack_of J.xtop.fin.1.1.1 J.blk.2.2.1 J.tcbs_eq.1.symm hpC hpS hp0 hk hf
    have hu' : u = L.mem s (P1.scTcbA p) := P1.eq_of_bv hu
    subst hu'
    refine J.words_of_spec huT (hsa y n _ hk hf) fun e => ?_
    obtain ⟨xi, hki, hsci, -⟩ := J.act.2
    rw [← e, hkx] at hki
    cases hki
    rw [hxs] at hsci
    exact hpi (Option.some.inj hsci)
  exact ⟨hHp, hpC, hp0, fun h => (hw h).1, fun h => (hw h).2, ⟨y, n, hk⟩, hpi⟩

/-- **An SC cap in a slot, as SchedControl's decode reads it** (l4v
`valid_cap`, `sym_refs`, `valid_global_refs`), from `JAtZ` (the slot any
slot of the typed heap, e.g. an extra cap's, `ExtraRel`'s `IsSlot`): the
cap's size below 64 (`H`'s SC of the cap's size fits, `JPlaced.cobj`,
`HeapOK.fits`, the pointer non-null), its SC one of `Z.C` (`JAtZ.hscC`),
the spec's of the cap's size (`JPlaced.sc`), whose bound thread is one of
`Z.T` holding it (`scBack_of`), and not the idle SC (`JPlaced.cobj`). -/
theorem JAtZ.scCtlExtra {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {x p sb : U64} (hx : IsSlot Z.th x)
    (hc : capAt (L.mem s) x = ok (.SchedContext p sb)) :
    sb.val < 64 ∧
      (p ∈ Z.C ∧ p ≠ 0#u64 ∧
        ∃ y, σ.kheap p.bv = some (.schedContext y (sb.val - Fl4Spec.minSchedContextBits)) ∧
          ∀ t : U64, y.scTcb = some t.bv →
            t ∈ Z.T ∧ ∃ xt, σ.kheap t.bv = some (.tcb xt) ∧ xt.tcbSchedContext = some p.bv) ∧
      p.bv ≠ Fl4Spec.idleScPtr := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hO := hJ.cobj _ hx
  rw [capV_of_capAt hc] at hO
  obtain ⟨hH, hpi⟩ := hO
  have hpC : p ∈ Z.C := J.hscC p _ hH
  have hp0 : p ≠ 0#u64 := J.c0 p hpC
  obtain ⟨Q, R, hc', hs⟩ := J.xtop.fin.1.1.1.lists
  obtain ⟨y, n, hk, -⟩ := hs.scs p hpC
  have hH' := (hJ.sc p y n hp0 hk).2
  rw [hH] at hH'
  have hn : sb.val = n + Fl4Spec.minSchedContextBits := HKind.sc.inj (Option.some.inj hH')
  have hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64 := by
    have := J.kern.heap.fits p _ hH
    simpa only [P1.HKind.bits] using this
  have hp1 : 1 ≤ p.val := by
    rcases Nat.eq_zero_or_pos p.val with h | h
    · exact absurd (UScalar.eq_of_val_eq (by rw [h]; rfl)) hp0
    · exact h
  have hsb : sb.val < 64 := by
    by_contra hge
    have : 2 ^ 64 ≤ 2 ^ sb.val := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hpS : p ∈ P1.Heap.scs H := ⟨_, hH⟩
  refine ⟨hsb, ⟨hpC, hp0, y, by rw [hn, Nat.add_sub_cancel]; exact hk, fun t ht => ?_⟩, hpi⟩
  obtain ⟨u, huT, hu, xt, hkt, hxt⟩ :=
    scBack_of J.xtop.fin.1.1.1 J.blk.2.2.1 J.tcbs_eq.1.symm hpC hpS hp0 hk ht
  have e := P1.eq_of_bv hu
  subst e
  exact ⟨huT, xt, hkt, hxt⟩

/-- **A final SC cap's finalisation at `J`** (module docstring; the SC may
be the current one): the statement `jFinAt_sc` reads, proved by
`jScFin_of` from the SC steps. -/
def JScFinHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit), Z.th = th → JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → Vs.NoSwitch σ →
    ∀ (sl : Fl4Spec.CslotPtr) (p sb : U64), AbsSlot Z.th sl →
      capAt (L.mem s) (cslotAddr sl) = ok (.SchedContext p sb) →
      Fl4Spec.isFinalCap' (absCap (.SchedContext p sb)) σ →
      objects.finalise_cap st arI s a (.SchedContext p sb) true false ⦃ res =>
        res.1 = (capability.Cap.Null, capability.Cap.Null) ∧
        ∃ σ' V' Ac' Lst' D', ((absCap res.1.1, absCap res.1.2), σ') ∈
            (Fl4Spec.finaliseCap (Z := Unit) (absCap (.SchedContext p sb)) true σ).1 ∧
          JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' res.2.1 res.2.2 σ' ∧
          SlotsSame Z.th (L.mem s) (L.mem res.2.1) ∧ L.ksb res.2.1 = L.ksb s ⦄

/-- **The yielder's `complete_yield_to` at `J`**, of an SC `q` of the set
(shared by the thread and the SC finalisations; XTop: `ScYieldFinHyp`);
proved by `jYieldToHyp_of` from XTopJointYield's `JAtZ.completeYieldJ`. -/
def JYieldToHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S)
    (a : A) (σ : Fl4Spec.State Unit), Z.th = th → JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ →
    ∀ q ∈ Z.C, L.mem s (scYieldFromA q) ≠ 0#u64 →
      schedcontext.complete_yield_to st arI s a (L.mem s (scYieldFromA q)) ⦃ r => ∃ σ',
        Fl4Spec.completeYieldTo (Z := Unit) (L.mem s (scYieldFromA q)).bv σ = ({((), σ')}, False) ∧
        JTP (L := L) arI AR Z H Cs r.1 r.2 σ' ⦄

/-- **`JYieldToHyp` proved** (`JAtZ.completeYieldJ`; the yielder in `Z.T` by
`YieldRel.frm`), from the platform's `ticks_to_us` and `getMaxTicksToUs` [P]. -/
theorem jYieldToHyp_of {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} (hT : P0.ArchTotal arI)
    (hticks : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      ∀ (a : A) (v : U64), arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    JYieldToHyp (L := L) arI AR th := by
  intro Z H Cs Ac Lst D s a σ _ J q hq h0
  obtain ⟨Q, R, hc, hs⟩ := J.xtop.fin.1.1.1.lists
  obtain ⟨y5, n5, hk5, hx5⟩ := hs.scs q hq
  have e5 : y5.scYieldFrom = some (L.mem s (scYieldFromA q)).bv := by
    rw [hx5.yieldFrom, ← scYieldFromA_eq, Notif.optRef_ne h0]
  obtain ⟨t, ht, et, -⟩ := J.yld.frm q hq y5 n5 hk5 _ e5
  have hjT : L.mem s (scYieldFromA q) ∈ Z.T := by rw [← P1.eq_of_bv et]; exact ht
  exact J.completeYieldJ hT hticks.1 (hticks.2 a) hjT

theorem JThreadFinHyps.yieldToH {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} (hT : P0.ArchTotal arI)
    (h : JThreadFinHyps (L := L) arI AR th) : JYieldToHyp (L := L) arI AR th := jYieldToHyp_of arI hT h.ticks

/-- **An SC cap's slot is ready once the SC is dead** (as `JAtZ.ep_ready`),
the cap of the SC's size. -/
theorem JAtZ.sc_ready {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {x : U64} {p sb : U64}
    (hcv : capV (L.mem s) x = .SchedContext p sb) (hHp : H p = some (.sc sb.val)) (hd : DeadP (L := L) H s p) :
    EmptyReady (L := L) H Z.G s x := by
  have hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64 := by
    have := J.kern.heap.fits p _ hHp
    simpa only [P1.HKind.bits] using this
  have hp0 : p ≠ 0#u64 := fun e => by rw [e, J.kern.h0] at hHp; cases hHp
  have hp1 : 1 ≤ p.val := by
    rcases Nat.eq_zero_or_pos p.val with h | h
    · exact absurd (UScalar.eq_of_val_eq (by rw [h]; rfl)) hp0
    · exact h
  have hsb : sb.val < 64 := by
    by_contra hge
    have : 2 ^ 64 ≤ 2 ^ sb.val := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  obtain ⟨e1, e2⟩ := range_sc p sb hsb hpfit
  unfold EmptyReady
  rw [hcv, e1, e2]
  intro _ _
  have hout : ∀ q k, H q = some k → q ≠ p → q.val + 2 ^ k.bits ≤ p.val ∨ p.val + 2 ^ sb.val ≤ q.val := by
    intro q k hq hne
    have := J.kern.heap.disj q k p (.sc sb.val) hq hHp hne
    simpa only [P1.HKind.bits] using this
  have hpos : 1 ≤ 2 ^ sb.val := Nat.one_le_two_pow
  refine fun lo hi hlh h1 h2 => ?_
  · right
    intro q hq
    by_cases e : q = p
    · subst e; exact hd
    · cases hk : H q with
      | none => exact deadP_none hk
      | some k =>
        exfalso
        have : 1 ≤ 2 ^ k.bits := Nat.one_le_two_pow
        rcases hout q k hk e with h | h <;> omega

set_option maxHeartbeats 16000000 in
/-- **`JAtZ` across a final SC cap's finalisation** (as XTop's `xFinSc_of`),
from the SC steps (`JAtZ.unbindAllJ`, `unbindNtfnJ`, `unbindReplyJ`) and the
yielder's `JYieldToHyp`; the SC's
links cleared and the current SC word kept along the way by P1's per-step
lemmas (`unbind_all_tcbs.blk`, `unbind_ntfn.blk`, `unbind_reply.blk`,
`complete_yield_to.blkS`) at each step's `BlkOK`; the inactive SC by
`JAtZ.setInactiveJ`. -/
theorem JAtZ.finScJ {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hT : P0.ArchTotal arI) (hY : JYieldToHyp (L := L) arI AR Z.th)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {p sb : U64} (hpC : p ∈ Z.C) (hp0 : p ≠ 0#u64)
    (hpi : p.bv ≠ Fl4Spec.idleScPtr) (hpS : p ∈ P1.Heap.scs H)
    (hna : L.mem s (P1.scTcbA p) ≠ 0#u64 → L.actionW s ≠ L.mem s (P1.scTcbA p))
    (hidle : L.mem s (P1.scTcbA p) ≠ 0#u64 → L.idleW s ≠ L.mem s (P1.scTcbA p)) :
    objects.finalise_cap st arI s a (.SchedContext p sb) true false ⦃ r => ∃ σ',
      ((Fl4Spec.Cap.nullCap, Fl4Spec.Cap.nullCap), σ') ∈
        (Fl4Spec.finaliseCap (Z := Unit) (absCap (.SchedContext p sb)) true σ).1 ∧
      JTP (L := L) arI AR Z H Cs r.2.1 r.2.2 σ' ⦄ := by
  rw [P1.fin_cap_eq_obj (by simp)]
  unfold objects.finalise_cap_object
  simp only [↓reduceIte]
  -- `unbind_all_tcbs`
  refine WP.spec_bind (WP.spec_and (JAtZ.unbindAllJ arI J hpC hp0 hpi hna hidle)
    (P1.schedcontext.unbind_all_tcbs.blk hT s a p J.blk hpS hp0 hna hidle)) ?_
  rintro ⟨s1, a1⟩ ⟨⟨σ1, he1, V1, Ac1, Lst1, D1, J1⟩, hP1⟩
  try simp only [WP.uncurry'_pair] at hP1
  obtain ⟨-, -, -, -, t1, -⟩ := hP1
  -- `unbind_ntfn`
  refine WP.spec_bind (WP.spec_and (JAtZ.unbindNtfnJ arI J1 hpC hp0)
    (P1.schedcontext.unbind_ntfn.blk s1 p J1.blk fun _ => hpS)) ?_
  rintro s2 ⟨⟨σ2, he2, V2, Ac2, Lst2, D2, J2⟩, -, -, t2, -, n2⟩
  have t2' : L.mem s2 (P1.scTcbA p) = 0#u64 := by rw [t2, t1]
  -- `unbind_reply`
  refine WP.spec_bind (WP.spec_and
    (JAtZ.unbindReplyJ arI J2 hpC hp0)
    (P1.schedcontext.unbind_reply.blk s2 p p J2.blk (fun _ => hpS) hpS)) ?_
  rintro s3 ⟨⟨σ3, he3, V3, Ac3, Lst3, D3, J3⟩, -, -, k3, r3⟩
  have t3 : L.mem s3 (P1.scTcbA p) = 0#u64 := by rw [k3.1, t2']
  have n3 : L.mem s3 (P1.scNtfnA p) = 0#u64 := by rw [k3.2.1, n2 hp0]
  have r3' : L.mem s3 (P1.scReplyA p) = 0#u64 := r3 hp0
  obtain ⟨Q3, R3, hc3, hs3⟩ := J3.xtop.fin.1.1.1.lists
  obtain ⟨y3, n3', hk3, hx3⟩ := hs3.scs p hpC
  -- the inactive SC and the post
  have fin5 : ∀ (s4 : S) (a4 : A) (σ4 : Fl4Spec.State Unit) (V4 : XVs) (Ac4 : Set U64) (Lst4 : U64 → List U64)
      (D4 : Set U64), JAtZ (L := L) arI AR (Z.mv Z.G V4) H Cs Ac4 Lst4 D4 s4 a4 σ4 →
      L.mem s4 (P1.scTcbA p) = 0#u64 → L.mem s4 (P1.scNtfnA p) = 0#u64 → L.mem s4 (P1.scReplyA p) = 0#u64 →
      Fl4Spec.schedContextUnbindYieldFrom (Z := Unit) p.bv σ3 = ({((), σ4)}, False) →
      (do
        let s5 ← obj.Sc.set_refill_max st p s4 0#u64
        let s6 ← obj.Sc.set_sporadic st p s5 0#u64
        ok ((capability.Cap.Null, capability.Cap.Null), s6, a4)) ⦃ r => ∃ σ',
          ((Fl4Spec.Cap.nullCap, Fl4Spec.Cap.nullCap), σ') ∈
            (Fl4Spec.finaliseCap (Z := Unit) (absCap (.SchedContext p sb)) true σ).1 ∧
          JTP (L := L) arI AR Z H Cs r.2.1 r.2.2 σ' ⦄ := by
    intro s4 a4 σ4 V4 Ac4 Lst4 D4 J4 t4 n4 r4 he4
    step with obj.Sc.set_refill_max.spec as ⟨s5, hs5⟩
    step with obj.Sc.set_sporadic.spec2 as ⟨s6, hs6⟩
    subst hs5 hs6
    obtain ⟨σ5, he5, V5, Ac5, Lst5, D5, J5⟩ := JAtZ.setInactiveJ arI J4 hpC hp0 hpi t4 n4 r4
    exact ⟨σ5, finSc_mem he1 he2 he3 he4 he5, V5, Ac5, Lst5, D5, J5⟩
  -- the yielder
  step with obj.Sc.yield_from.spec' as ⟨i, hi⟩
  step with obj.Tcb.is_null.spec as ⟨b0, hb0⟩
  by_cases h0 : i = 0#u64
  · have hb : b0 = true := by rw [hb0, h0]; rfl
    simp only [hb, ↓reduceIte, bind_ok]
    refine fin5 s3 a1 σ3 V3 Ac3 Lst3 D3 J3 t3 n3 r3' (unbindYieldFrom_none hk3 ?_)
    rw [hx3.yieldFrom, ← scYieldFromA_eq, ← hi, h0, Notif.optRef_zero]
  · have hb : b0 = false := by rw [hb0]; simp [h0]
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    rw [hi]
    have hy : L.mem s3 (scYieldFromA p) ≠ 0#u64 → L.mem s3 (scYieldFromA p) ∈ P1.Heap.tcbs H := fun hy0 =>
      J3.blk.2.2.1.2.2.yt.2.2 p hpS hy0
    refine WP.spec_bind (WP.spec_and (hY (Z.mv Z.G V3) H Cs Ac3 Lst3 D3 s3 a1 σ3 rfl J3 p hpC (by rw [← hi]; exact h0))
      (P1.schedcontext.complete_yield_to.blkS hT s3 a1 _ p J3.blk hy hpS)) ?_
    rintro ⟨s4, a4⟩ ⟨⟨σ4, e4, V4, Ac4, Lst4, D4, J4⟩, hP4⟩
    try simp only [WP.uncurry'_pair] at hP4
    obtain ⟨-, -, -, k4⟩ := hP4
    refine fin5 s4 a4 σ4 V4 Ac4 Lst4 D4 J4 (by rw [k4.1, t3])
      (by rw [k4.2.1, n3]) (k4.2.2.2 r3') (unbindYieldFrom_some hk3 ?_ e4)
    rw [hx3.yieldFrom, ← scYieldFromA_eq, Notif.optRef_ne (by rw [← hi]; exact h0)]

/-- **`JScFinHyp` from the SC steps** (`JAtZ.finScJ`), the slots and the
kernel-state base kept by P1's `fin_cap_sc.slots`. -/
theorem jScFin_of {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} (hT : P0.ArchTotal arI)
    (hY : JYieldToHyp (L := L) arI AR th) :
    JScFinHyp (L := L) arI AR th := by
  intro Z H Cs Ac Lst D s a σ hth J hns sl p sb hA hc _
  have hC' := J.scCap arI hA hc
  subst hth
  obtain ⟨hHp, hpC, hp0, hna, hidle, -, hpi⟩ :=
    JAtZ.scCapFacts arI J hA hc ⟨hC'.1, hC'.2, fun _ _ _ _ _ u hu => (hns u hu).elim⟩
  have hpS : p ∈ P1.Heap.scs H := ⟨_, hHp⟩
  refine WP.spec_mono (WP.spec_and (JAtZ.finScJ arI hT hY J hpC hp0 hpi hpS hna hidle)
    (P1.fin_cap_sc.slots (ar := arI) hT s a p sb true false J.blk hpS hp0 hna hidle)) ?_
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨⟨σ1, hm1, V1, Ac1, Lst1, D1, J1⟩, e, -, f, hW1⟩
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  have hSS1 : SlotsSame Z.th (L.mem s) (L.mem s1) :=
    slotsSame_of_capw J.xtop.rel.1 (J.slotCapW (tLowSlots_all _)) hW1
  exact ⟨rfl, σ1, V1, Ac1, Lst1, D1, hm1, J1, hSS1, f.1⟩

end

end

end Fl4Proofs.P3
