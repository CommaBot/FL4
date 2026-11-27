/-
P3 (issue #16, jc6b; KENTRY-PLAN jc6 (3)(b), jc6b): **part (b) of `RegionUnrefAt`
from the bound-notification and SC–notification symmetry**.

* `BndSym σ` (l4v `sym_refs` for `tcb_bound_notification` / `ntfn_bound_tcb` and
  `sc_ntfn` / `ntfn_sc`, with the referenced objects' kinds): a TCB's bound
  notification is a notification bound back to it, and conversely; an SC's
  notification is a notification whose SC is that SC, and conversely. Spec side,
  stated on `σ`: the FL4 words follow through the relation (`TcbRel1.bound`,
  `NtfnRel1.bound` / `.sc`, `ScRelW.ntfn`). The fourth clause is SInvA's
  `NtfnScB` and P1's `ScExtra0.nsc`; the consumers below read only the first three.
* `BndView σ σ'`: the objects' kinds and their four link fields the same at `σ` and
  `σ'`, both ways; `BndSym.view` keeps `BndSym` across it, `BndView.updTcb` gives
  it for a TCB update keeping the bound notification (the caller's restart).
* **`JAtZ.keptB J hS : KeptRefsBAll H D s`** (jc6a's carried form of (b)): a link
  of either kind to a dead object has a spec back-link, read from a word of the dead
  object that `DeadP` zeroes (`ntfnBtA`, `ntfnScA`, `boundA`), so it is impossible.
  The target's kind comes from P1's `ScExtra0` (`bnd`, `scn`) and `NtfnRel1.bound_mem`.
* **`JAtZ.unrefB J hni hS : RegionUnrefB H D s`** at an `Entered` `JAtZ` state:
  `keptB` at the restart's `JAtZ` (`JAtZ.restartSJ`, the same `H` and `D`), the
  symmetry kept by the restart (`BndView.updTcb`), then `KeptRefsBAll.region`.

`BndSym σ` is NOT yet carried (KENTRY-PLAN jc6b: the generic `JAtZ` frames do not
keep the four link fields, so carrying it is a per-call-site obligation, sized there).
-/
import Fl4Proofs.P3.UnrefParts
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Sched

noncomputable section

section Spec
open Fl4Spec

/-- **The bound-notification and SC–notification symmetry** (module docstring). -/
def BndSym (σ : State Unit) : Prop :=
  (∀ t x n, σ.kheap t = some (.tcb x) → x.tcbBoundNotification = some n →
    ∃ xn, σ.kheap n = some (.notification xn) ∧ xn.ntfnBoundTcb = some t) ∧
  (∀ n xn t, σ.kheap n = some (.notification xn) → xn.ntfnBoundTcb = some t →
    ∃ x, σ.kheap t = some (.tcb x) ∧ x.tcbBoundNotification = some n) ∧
  (∀ c y k n, σ.kheap c = some (.schedContext y k) → y.scNtfn = some n →
    ∃ xn, σ.kheap n = some (.notification xn) ∧ xn.ntfnSc = some c) ∧
  (∀ n xn c, σ.kheap n = some (.notification xn) → xn.ntfnSc = some c →
    ∃ y k, σ.kheap c = some (.schedContext y k) ∧ y.scNtfn = some n)

/-- **The objects' kinds and link fields kept** from `σ` to `σ'` (one direction). -/
def BndFwd (σ σ' : State Unit) : Prop :=
  (∀ q x, σ.kheap q = some (.tcb x) → ∃ x', σ'.kheap q = some (.tcb x') ∧
    x'.tcbBoundNotification = x.tcbBoundNotification) ∧
  (∀ q x, σ.kheap q = some (.notification x) → ∃ x', σ'.kheap q = some (.notification x') ∧
    x'.ntfnBoundTcb = x.ntfnBoundTcb ∧ x'.ntfnSc = x.ntfnSc) ∧
  (∀ q y k, σ.kheap q = some (.schedContext y k) → ∃ y' k', σ'.kheap q = some (.schedContext y' k') ∧
    y'.scNtfn = y.scNtfn)

/-- `BndFwd` both ways. -/
def BndView (σ σ' : State Unit) : Prop := BndFwd σ σ' ∧ BndFwd σ' σ

theorem BndSym.view {σ σ' : State Unit} (h : BndSym σ) (v : BndView σ σ') : BndSym σ' := by
  obtain ⟨⟨fT, fN, fC⟩, ⟨bT, bN, bC⟩⟩ := v
  refine ⟨fun t x n hk hb => ?_, fun n xn t hk hb => ?_, fun c y k n hk hb => ?_, fun n xn c hk hb => ?_⟩
  · obtain ⟨x0, hk0, e⟩ := bT t x hk
    obtain ⟨xn, hkn, hn⟩ := h.1 t x0 n hk0 (e.trans hb)
    obtain ⟨xn', hkn', e1, -⟩ := fN n xn hkn
    exact ⟨xn', hkn', e1.trans hn⟩
  · obtain ⟨xn0, hk0, e, -⟩ := bN n xn hk
    obtain ⟨x, hkx, hx⟩ := h.2.1 n xn0 t hk0 (e.trans hb)
    obtain ⟨x', hkx', e1⟩ := fT t x hkx
    exact ⟨x', hkx', e1.trans hx⟩
  · obtain ⟨y0, k0, hk0, e⟩ := bC c y k hk
    obtain ⟨xn, hkn, hn⟩ := h.2.2.1 c y0 k0 n hk0 (e.trans hb)
    obtain ⟨xn', hkn', -, e1⟩ := fN n xn hkn
    exact ⟨xn', hkn', e1.trans hn⟩
  · obtain ⟨xn0, hk0, -, e⟩ := bN n xn hk
    obtain ⟨y, k, hky, hy⟩ := h.2.2.2 n xn0 c hk0 (e.trans hb)
    obtain ⟨y', k', hky', e1⟩ := fC c y k hky
    exact ⟨y', k', hky', e1.trans hy⟩

/-- `BndView` across a kheap update of a TCB keeping its bound notification. -/
theorem BndView.updTcb {σ σ' : State Unit} {p : ObjRef} {x y : Tcb} (hk : σ.kheap p = some (.tcb x))
    (hy : y.tcbBoundNotification = x.tcbBoundNotification)
    (e : σ'.kheap = Function.update σ.kheap p (some (.tcb y))) : BndView σ σ' := by
  have hne : ∀ q, q ≠ p → σ'.kheap q = σ.kheap q := fun q hq => by rw [e, Function.update_of_ne hq]
  have hp : σ'.kheap p = some (.tcb y) := by rw [e, Function.update_self]
  refine ⟨⟨fun q x0 hq => ?_, fun q x0 hq => ?_, fun q y0 k hq => ?_⟩,
    ⟨fun q x0 hq => ?_, fun q x0 hq => ?_, fun q y0 k hq => ?_⟩⟩
  · by_cases ep : q = p
    · subst ep; rw [hk] at hq; cases hq; exact ⟨y, hp, hy⟩
    · exact ⟨x0, by rw [hne q ep]; exact hq, rfl⟩
  · by_cases ep : q = p
    · subst ep; rw [hk] at hq; cases hq
    · exact ⟨x0, by rw [hne q ep]; exact hq, rfl, rfl⟩
  · by_cases ep : q = p
    · subst ep; rw [hk] at hq; cases hq
    · exact ⟨y0, k, by rw [hne q ep]; exact hq, rfl⟩
  · by_cases ep : q = p
    · subst ep; rw [hp] at hq; cases hq; exact ⟨x, hk, hy.symm⟩
    · exact ⟨x0, by rw [← hne q ep]; exact hq, rfl⟩
  · by_cases ep : q = p
    · subst ep; rw [hp] at hq; cases hq
    · exact ⟨x0, by rw [← hne q ep]; exact hq, rfl, rfl⟩
  · by_cases ep : q = p
    · subst ep; rw [hp] at hq; cases hq
    · exact ⟨y0, k, by rw [← hne q ep]; exact hq, rfl⟩

/-- `BndSym` across the caller's restart (`JAtZ.restartSJ`'s spec state). -/
theorem BndSym.restart {σ : State Unit} (h : BndSym σ) {ct : ObjRef} {x : Tcb}
    (hk : σ.kheap ct = some (.tcb x)) :
    BndSym (Notif.stsAct (Notif.updK σ ct (.tcb { x with tcbState := .restart })) ct) :=
  h.view (BndView.updTcb (y := { x with tcbState := .restart }) hk rfl (by rw [Notif.stsAct_kheap, Notif.updK_kheap]))

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **(b), carried form, at a `JAtZ` state with the symmetry** (module docstring). -/
theorem JAtZ.keptB (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hS : BndSym σ) :
    KeptRefsBAll (L := L) H D s := by
  have h0 := J.kern.h0
  have hI := J.xtop.ipc
  obtain ⟨Q, R, -, hs⟩ := J.xtop.fin.1.1.1.lists
  have hE := J.blk.2.2.1.2.2
  refine ⟨fun t ht hw hD => ?_, fun c hc hw hD => ?_, fun n hn hw hD => ?_⟩
  · -- a TCB's bound notification
    have hw0 : L.mem s (P1.boundA t) ≠ 0#u64 := fun e => hw (by rw [e]; exact h0)
    have hwN : L.mem s (P1.boundA t) ∈ P1.Heap.ntfns H := hE.bnd t ht hw0
    have htT : t ∈ Z.T := by rw [J.tcbs_eq.1]; exact ht
    obtain ⟨x, hkx, hR⟩ := hI.tcb t htT
    have hb : x.tcbBoundNotification = some (L.mem s (P1.boundA t)).bv := by
      rw [hR.bound]; exact Notif.optRef_ne hw0
    obtain ⟨xn, hkn, hnb⟩ := hS.1 _ x _ hkx hb
    obtain ⟨xn', hkn', hR'⟩ := hI.ntfn _ (J.hset.2.1 _ hwN)
    rw [hkn] at hkn'; cases hkn'
    have d : L.mem s (Notif.nBoundA (L.mem s (P1.boundA t))) = 0#u64 := ((J.jcov.dead _ hD).2.2.1 hwN).2.1
    rw [hR'.bound, d, Notif.optRef_zero] at hnb; cases hnb
  · -- an SC's notification
    have hw0 : L.mem s (P1.scNtfnA c) ≠ 0#u64 := fun e => hw (by rw [e]; exact h0)
    have hwN : L.mem s (P1.scNtfnA c) ∈ P1.Heap.ntfns H := hE.scn c hc hw0
    obtain ⟨z, hz⟩ := hc
    obtain ⟨y, k, hky, hx⟩ := hs.scs c (J.hscC c z hz)
    have hyn : y.scNtfn = some (L.mem s (P1.scNtfnA c)).bv := by
      rw [hx.ntfn, scW_ntfn]; exact Notif.optRef_ne hw0
    obtain ⟨xn, hkn, hns⟩ := hS.2.2.1 _ y k _ hky hyn
    obtain ⟨xn', hkn', hR'⟩ := hI.ntfn _ (J.hset.2.1 _ hwN)
    rw [hkn] at hkn'; cases hkn'
    have d : L.mem s (Notif.nScA (L.mem s (P1.scNtfnA c))) = 0#u64 := ((J.jcov.dead _ hD).2.2.1 hwN).2.2
    rw [hR'.sc, d, Notif.optRef_zero] at hns; cases hns
  · -- a notification's bound TCB
    have hw0 : L.mem s (P1.ntfnBtA n) ≠ 0#u64 := fun e => hw (by rw [e]; exact h0)
    obtain ⟨xn, hkn, hR⟩ := hI.ntfn n (J.hset.2.1 n hn)
    have hwT : L.mem s (P1.ntfnBtA n) ∈ Z.T := hR.bound_mem hw0
    have hb : xn.ntfnBoundTcb = some (L.mem s (P1.ntfnBtA n)).bv := by
      rw [hR.bound]; exact Notif.optRef_ne hw0
    obtain ⟨x, hkx, hxb⟩ := hS.2.1 _ xn _ hkn hb
    obtain ⟨x', hkx', hR'⟩ := hI.tcb _ hwT
    rw [hkx] at hkx'; cases hkx'
    have d : L.mem s (Endp.tBoundA (L.mem s (P1.ntfnBtA n))) = 0#u64 :=
      ((J.jcov.dead _ hD).1 (J.zH.1 _ hwT)).2.2.1
    rw [hR'.bound, d, Notif.optRef_zero] at hxb; cases hxb

/-- **(b) of `RegionUnrefAt` at an `Entered` `JAtZ` state with the symmetry**
(module docstring). -/
theorem JAtZ.unrefB (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) (hS : BndSym σ) :
    RegionUnrefB (L := L) H D s := by
  intro s1 hs1 lo hi hD
  have hct : sched.cur_thread st s = ok (L.curW s) := cur_thread_eq s
  obtain ⟨hcur, x, hk, hrun⟩ := J.curRunnable hni hct
  have htcb : Z.th (L.curW s) = some .tcb := (J.xtop.curTcb hcur).1
  obtain ⟨Ac', Lst', J1⟩ := J.restartSJ (jStepHyps arI) hcur hk htcb hrun hs1
  exact (J1.keptB (hS.restart hk)).region hD

end

end

end Fl4Proofs.P3
