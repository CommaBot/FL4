/-
P3 (DESIGN.md §9), scheduling contexts: **an SC cap's finalisation at
`XTop`** (`XFinHyps.sc`, `xFinSc_of`).

FL4's `finalise_cap_object` of a final SC cap: `unbind_all_tcbs`,
`unbind_ntfn`, `unbind_reply`, the yielder's `complete_yield_to`, then
`REFILL_MAX` and `SPORADIC` cleared; the spec's: `sched_context_unbind_all_tcbs`,
`_unbind_ntfn`, `_unbind_reply`, `_unbind_yield_from`, `_set_inactive`.
Every step but the yield is an SC step at `XTop` (`xtop_sc_step`,
`xtop_sc_stepCW` for the reply's call-stack words), from the SC side's
refinement lemmas (`unbind_all_tcbs_refines`, `unbind_ntfn_refines`,
`unbind_reply_refines`) and, for the last, `SchedRel.set_inactive` (an SC with
`REFILL_MAX` 0 is related by its header words alone, `ScRelW`).

Named: `ScYieldFinHyp` [W], the yielder's `complete_yield_to` at `XTop`
(its `set_consumed` reply writes the yielder's registers, XProd's
`ScReplyLeaf`); `ScFinPreX` [J], at the `XTopAt` states: the IPC placement
(the notifications and replies apart from the kernel-global block from
`XFinAt`'s `KsApart`), `NSC`,
`Inv`, the call-stack relation, and the cap's SC among the SCs, non-null, not
the idle SC, its bound thread and notification among the sets.
-/
import Fl4Proofs.P3.ScXProd
import Fl4Proofs.P3.ScDecodeSc
import Fl4Proofs.P3.ScUnblock
import Fl4Proofs.P3.XTopDel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open Classical

noncomputable section

/-! ## The spec side -/

section Spec
open Fl4Spec Fl4Proofs.P3.Notif

/-- The SC after `sched_context_set_inactive`. -/
abbrev inactSc (x : SchedContext) : SchedContext :=
  { x with scRefills := [], scRefillMax := 0, scBudget := 0, scSporadic := false }

theorem setInactive_eq {σ : State Unit} {p : ObjRef} {x : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext x n)) :
    schedContextSetInactive (Z := Unit) p σ = ({((), updSc σ p (inactSc x) n)}, False) := by
  unfold schedContextSetInactive
  have k : ∀ (σ' : State Unit) y, (updSc σ' p y n).kheap p = some (.schedContext y n) := fun _ _ => by
    simp [updK]
  rw [nd_bind_one (updateSchedContext_eq hk _), nd_bind_one (updateSchedContext_eq (k _ _) _),
    nd_bind_one (updateSchedContext_eq (k _ _) _), updateSchedContext_eq (k _ _), updSc_updSc, updSc_updSc,
    updSc_updSc]
  rfl

theorem nkt_schedContextUnbindAllTcbs (p : ObjRef) : NKT (schedContextUnbindAllTcbs (Z := Unit) p) := by
  unfold schedContextUnbindAllTcbs
  repeat (first | exact nkt_schedContextUnbindTcb _ | nkt_step2)

theorem nkt_schedContextUnbindReply (p : ObjRef) : NKT (schedContextUnbindReply (Z := Unit) p) := by
  unfold schedContextUnbindReply; repeat nkt_step2

theorem nkt_schedContextSetInactive (p : ObjRef) : NKT (schedContextSetInactive (Z := Unit) p) := by
  unfold schedContextSetInactive; repeat nkt_step2

theorem unbindYieldFrom_none {σ : State Unit} {p : ObjRef} {y : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext y n)) (hy : y.scYieldFrom = none) :
    schedContextUnbindYieldFrom (Z := Unit) p σ = ({((), σ)}, False) := by
  unfold schedContextUnbindYieldFrom
  rw [nd_bind_one (getSchedContext_eq hk), hy]; rfl

theorem unbindYieldFrom_some {σ σ' : State Unit} {p t : ObjRef} {y : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext y n)) (hy : y.scYieldFrom = some t)
    (h : completeYieldTo (Z := Unit) t σ = ({((), σ')}, False)) :
    schedContextUnbindYieldFrom (Z := Unit) p σ = ({((), σ')}, False) := by
  unfold schedContextUnbindYieldFrom
  rw [nd_bind_one (getSchedContext_eq hk), hy]; exact h

/-- **The spec's SC finalisation** from its five steps. -/
theorem finSc_mem {σ σ1 σ2 σ3 σ4 σ5 : State Unit} {p : ObjRef} {b : Nat}
    (h1 : schedContextUnbindAllTcbs (Z := Unit) p σ = ({((), σ1)}, False))
    (h2 : schedContextUnbindNtfn (Z := Unit) p σ1 = ({((), σ2)}, False))
    (h3 : schedContextUnbindReply (Z := Unit) p σ2 = ({((), σ3)}, False))
    (h4 : schedContextUnbindYieldFrom (Z := Unit) p σ3 = ({((), σ4)}, False))
    (h5 : schedContextSetInactive (Z := Unit) p σ4 = ({((), σ5)}, False)) :
    ((Cap.nullCap, Cap.nullCap), σ5) ∈ (finaliseCap (Z := Unit) (.schedContextCap p b) true σ).1 := by
  unfold finaliseCap NonDet.when
  simp only [↓reduceIte]
  rw [nd_bind_one h1, nd_bind_one h2, nd_bind_one h3, nd_bind_one h4, nd_bind_one h5]
  exact Set.mem_singleton _

end Spec

/-! ## Clearing `REFILL_MAX` and `SPORADIC` -/

section
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

set_option maxHeartbeats 2000000 in
/-- **An SC made inactive** (`REFILL_MAX` and `SPORADIC` 0), not the idle SC,
against `sched_context_set_inactive`: `SchedRel` kept (an inactive SC is
related by its header words), the notification words and the spec's views
kept. -/
theorem SchedRel.set_inactive {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {sc : U64} (hsc : sc ∈ C) {x : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap sc.bv = some (.schedContext x n)) (hid : sc.bv ≠ Fl4Spec.idleScPtr) :
    SchedRel st N T C c (L.wr (L.wr s (maxA sc) 0#u64) (scW sc 64#u64) 0#u64) (updSc σ sc.bv (inactSc x) n) ∧
      FootEq N T (L.mem s) (L.mem (L.wr (L.wr s (maxA sc) 0#u64) (scW sc 64#u64) 0#u64)) ∧
      KView σ (updSc σ sc.bv (inactSc x) n) ∧
      WritesIn st s (L.wr (L.wr s (maxA sc) 0#u64) (scW sc 64#u64) 0#u64)
        (fun b => b = scW sc 72#u64 ∨ b = scW sc 64#u64) := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x', n', hk', hx⟩ := hs.scs sc hsc
  rw [hk] at hk'; cases hk'
  obtain ⟨h8, h2, hfit⟩ := hx.bounds
  have a72 := hx.hdr (K := 72#u64) (by simp) (by simp)
  have a64 := hx.hdr (K := 64#u64) (by simp) (by simp)
  have v72 := scW_val (sc := sc) (K := 72#u64) (by simp; omega)
  have v64 := scW_val (sc := sc) (K := 64#u64) (by simp; omega)
  rw [maxA_eq]
  have hw : WritesIn st s (L.wr (L.wr s (scW sc 72#u64) 0#u64) (scW sc 64#u64) 0#u64)
      (fun b => b = scW sc 72#u64 ∨ b = scW sc 64#u64) := (writesIn_wr a72.1).trans (writesIn_wr a64.1)
  have hm : ∀ K : U64, K.val < 96 → K.val % 8 = 0 → K ≠ 72#u64 → K ≠ 64#u64 →
      L.mem (L.wr (L.wr s (scW sc 72#u64) 0#u64) (scW sc 64#u64) 0#u64) (scW sc K) = L.mem s (scW sc K) := by
    intro K h1 h2 h3 h4
    have vK := scW_val (sc := sc) (K := K) (by omega)
    refine hw.mem_eq (hx.hdr h1 h2).1 ?_
    rintro (e | e)
    · apply h3; apply UScalar.eq_of_val_eq; have := congrArg UScalar.val e; rw [vK, v72] at this; have e72 : (72#u64 : U64).val = 72 := rfl; show K.val = 72; omega
    · apply h4; apply UScalar.eq_of_val_eq; have := congrArg UScalar.val e; rw [vK, v64] at this; have e64 : (64#u64 : U64).val = 64 := rfl; show K.val = 64; omega
  have m72 : L.mem (L.wr (L.wr s (scW sc 72#u64) 0#u64) (scW sc 64#u64) 0#u64) (scW sc 72#u64) = 0#u64 := by
    rw [L.mem_wr_ne a64.1 a72.1 (by rw [v64, v72]; simp)]
    exact rd_wr_eq a72.1
  have m64 : L.mem (L.wr (L.wr s (scW sc 72#u64) 0#u64) (scW sc 64#u64) 0#u64) (scW sc 64#u64) = 0#u64 :=
    rd_wr_eq a64.1
  have hrm : L.rmax (L.wr (L.wr s (scW sc 72#u64) 0#u64) (scW sc 64#u64) 0#u64) sc = 0#u64 := by
    simp only [LawfulStore.rmax, maxA_eq]; exact m72
  have hx' : ScRelW st (L.wr (L.wr s (scW sc 72#u64) 0#u64) (scW sc 64#u64) 0#u64) sc (inactSc x) n := by
    refine ⟨hx.pl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun h => absurd m64 h, fun h => absurd h hid, ?_,
      fun h => (h (by rw [hrm]; rfl)).elim⟩
    · have := hx.period
      simp only [LawfulStore.rperiod, periodA_eq] at this ⊢
      rw [hm 0#u64 (by simp) (by simp) (by decide) (by decide)]; exact this
    · show x.scConsumed = _; rw [hm 8#u64 (by simp) (by simp) (by decide) (by decide)]; exact hx.consumed
    · show x.scTcb = _; rw [hm 24#u64 (by simp) (by simp) (by decide) (by decide)]; exact hx.tcb
    · show x.scNtfn = _; rw [hm 40#u64 (by simp) (by simp) (by decide) (by decide)]; exact hx.ntfn
    · show x.scBadge = _; rw [hm 48#u64 (by simp) (by simp) (by decide) (by decide)]; exact hx.badge
    · show x.scYieldFrom = _; rw [hm 56#u64 (by simp) (by simp) (by decide) (by decide)]; exact hx.yieldFrom
    · show false = _; rw [m64]; simp
    · rw [hrm]; rfl
  refine ⟨hS.sc_updateW hsc hk (hw.mono fun b hb => ?_) (hm 16#u64 (by simp) (by simp) (by decide) (by decide)) _ hx',
    scin_footEq hS hsc (hw.mono fun b hb => ?_), KView.of_sc hk, hw⟩
  · rcases hb with rfl | rfl
    · exact hx.in_obj a72.2
    · exact hx.in_obj a64.2
  · rcases hb with rfl | rfl
    · exact a72.2
    · exact a64.2

end

end

end Fl4Proofs.P3.Sched

/-! ## At `XTop` -/

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- The slots kept by an SC step's writes (`TFoot` and the call-stack
words). -/
theorem XTopAt.ssTF {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s s' : S} {a : A} {σ : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s a σ) (hP0 : IPlaced Z.N Z.T Z.E Z.R Z.B)
    (hRk : ∀ r ∈ Z.R, r.val + 32 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ r.val)
    (hW : WritesIn st s s' (fun b => TFoot st Z.T Z.N Z.C Z.c s σ b ∨ CallW' Z.R Z.C b)) :
    SlotsSame Z.th (L.mem s) (L.mem s') :=
  slotsSame_of_iw hX.rel.1 hX.rel.2.2.2.2.2.1 hX.rel.2.2.2.2.2.2 hW fun _ hb =>
    hb.elim (tfoot_iw hX.fin.1.1.1) fun h => (callW'_xtop hX hP0 hRk h).2.2.2

theorem finWork_sc {p sb : U64} {fb : Bool} (h : FinWork (.SchedContext p sb) fb) : fb = true := by
  unfold FinWork at h
  rcases h with ⟨hb | ⟨f, l, o, e, -⟩, -⟩ | ⟨p, sz, r, d, ep, asid, va, e⟩
  · exact hb
  · cases e
  · cases e

/-- **The yielder's `complete_yield_to` at `XTop`** [W] (module docstring):
from `XTopAt Z` with the SC `p` yielded to, the spec's `complete_yield_to`
of the yielder, `XTopAt Z` after, the slots and the kernel base kept, the
spec's caps kept. -/
def ScYieldFinHyp (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (p : U64) : Prop :=
  ∀ s a σ, XTopAt (L := L) AR Z s a σ → L.mem s (scYieldFromA p) ≠ 0#u64 →
    schedcontext.complete_yield_to st arI s a (L.mem s (scYieldFromA p)) ⦃ r => ∃ σ', ∃ V' : XVs,
      Fl4Spec.completeYieldTo (Z := Unit) (L.mem s (scYieldFromA p)).bv σ = ({((), σ')}, False) ∧
      XTopAt (L := L) AR (Z.mv Z.G V') r.1 r.2 σ' ∧ SlotsSame Z.th (L.mem s) (L.mem r.1) ∧ L.ksb r.1 = L.ksb s ∧
      Fl4Proofs.P3.CKeep σ σ' ⦄

/-- **What an SC cap's finalisation at `XTop` reads** [J] (module docstring). -/
def ScFinPreX (Z : XSets) (s : S) (σ : Fl4Spec.State Unit) : Prop :=
  IPlaced Z.N Z.T Z.E Z.R Z.B ∧ NSC Z.N Z.C σ ∧ Inv σ ∧
  (∃ Lst, CallRel (L.mem s) Z.R Z.C σ Lst ∧ RPlaced st Z.N Z.T Z.C Z.R Z.c s σ ∧ RFree (L.mem s) Z.R Z.C σ Lst) ∧
  ∀ sl p sb, AbsSlot Z.th sl → capAt (L.mem s) (cslotAddr sl) = ok (.SchedContext p sb) →
    p ∈ Z.C ∧ p ≠ 0#u64 ∧ p.bv ≠ Fl4Spec.idleScPtr ∧
    ∀ y n, σ.kheap p.bv = some (.schedContext y n) →
      (∀ t : U64, y.scTcb = some t.bv → t ∈ Z.T ∧ t.bv ≠ σ.idleThread) ∧ (∀ m : U64, y.scNtfn = some m.bv → m ∈ Z.N)

set_option maxHeartbeats 16000000 in
/-- **`XFinHyps.sc` holds** (module docstring). -/
theorem xFinSc_of {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap}
    (hpre : ∀ (Z : XSets) s a σ, Z.th = th → XTopAt (L := L) AR Z s a σ → ScFinPreX (L := L) Z s σ)
    (hY : ∀ (Z : XSets) p, Z.th = th → ScYieldFinHyp (L := L) arI AR Z p) :
    XFinAt (L := L) arI FinScK AR th := by
  intro Z s a σ sl c hth hX hK hTh ⟨p, sb, hc0⟩ hDS hA hc hk hw
  have hYp := hY Z p hth
  subst hth hc0
  obtain ⟨hP0, hNS, hInv, ⟨Lst, hCR, hRP, hRF⟩, hcap⟩ := hpre Z s a σ rfl hX
  have hNk : ∀ n ∈ Z.N, n.val + 40 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ n.val := fun n hn =>
    (hK.ntfn n hn).imp (fun h => by omega) id
  have hRk : ∀ r ∈ Z.R, r.val + 32 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ r.val := hK.rep
  obtain ⟨hpC, hp0, hpi, hyk⟩ := hcap sl p sb hA hc
  have hfin := finWork_sc hw
  set fin := decide (Fl4Spec.isFinalCap' (absCap (.SchedContext p sb)) σ) with hfd
  have hfc : objects.finalise_cap st arI s a (.SchedContext p sb) fin false =
      objects.finalise_cap_object st arI s a (.SchedContext p sb) fin := by
    simp [objects.finalise_cap]
  rw [hfc]
  unfold objects.finalise_cap_object
  simp only [hfin, ↓reduceIte]
  have hS0 := hX.fin.1.1.1
  have hR0 := hX.fin.1.1.2.2.1
  obtain ⟨Q0, R0, hc0', hs0⟩ := hS0.lists
  obtain ⟨y, n, hky, hxy⟩ := hs0.scs p hpC
  obtain ⟨hbnd, hbn⟩ := hyk y n hky
  -- `unbind_all_tcbs`
  refine WP.spec_bind (unbind_all_tcbs_refines (ar := arI) s a σ hS0 hR0 hNS hInv hpC hpi hky hbnd) ?_
  rintro ⟨s1, a1⟩ ⟨ha1, σ1, he1, hS1, hR1, hN1, hI1, -, hw1, hck1⟩
  simp only at ha1 hS1 hR1 hw1 hN1
  subst ha1
  have hK1 : ScTKw (fun q => q = σ.curThread) σ σ1 :=
    (nkt_schedContextUnbindAllTcbs p.bv σ ((), σ1) (by rw [he1]; exact Set.mem_singleton _)).mono fun _ h => h.elim
  have hW1 := Sched.WritesIn.tfoot_of_kfoot (Sched.WritesIn.kfoot_of_sfoot_scw hS0 hpC (K := 24#u64) (by simp) (by simp) (by decide) hw1)
  have hX1 := xtop_sc_step (ct := σ.curThread) hX hP0 hNk hW1 hK1 hS1 hR1 id
  have hss1 := hX.ssTF hP0 hRk (hW1.mono fun _ h => Or.inl h)
  have kb1 : L.ksb s1 = L.ksb s := hW1.1
  have hm40 : L.mem s1 (scW p 40#u64) = L.mem s (scW p 40#u64) := by
    have ha := hxy.hdr (K := 40#u64) (by simp) (by simp)
    obtain ⟨-, h2, h3, -⟩ := hS0.scOutIn hpC ha.2
    refine hw1.mem_eq ha.1 ?_
    rintro (hb0 | e)
    · rcases hb0.range hc0'.tcbs with ⟨t, ht, g1, g2⟩ | ⟨g1, g2⟩
      · have := h3 t ht; omega
      · omega
    · have hb := hxy.bounds
      have := congrArg UScalar.val e
      rw [scW_val (by simp; omega), scW_val (by simp; omega)] at this
      simp at this
  obtain ⟨y1, n1, hk1, hy1⟩ := scNtfn_keep hS0 hS1 hpC hm40 hky
  obtain ⟨hCR1, hRP1⟩ := CallRel.carry hCR hRP (callWords_of_dfoot hS0 hRP hpC hw1) hw1.1 hck1
  have hRF1 := RFree.carry hRF hCR (callWords_of_dfoot hS0 hRP hpC hw1).2 hck1
  -- `unbind_ntfn`
  refine WP.spec_bind (unbind_ntfn_refines s1 σ1 hS1 hR1 hN1 hI1 hpC hp0 hk1 (fun m hm => hbn m (hy1 ▸ hm))) ?_
  rintro s2 ⟨σ2, he2, hS2, hR2, hN2, hI2, -, hw2, hck2⟩
  have hK2 : ScTKw (fun q => q = σ.curThread) σ1 σ2 :=
    (nkt_schedContextUnbindNtfn p.bv σ1 ((), σ2) (by rw [he2]; exact Set.mem_singleton _)).mono fun _ h => h.elim
  have hW2 := Sched.WritesIn.tfoot_of_kfoot (Sched.WritesIn.kfoot_of_nw_scw hS1 hpC (K := 40#u64) (by simp) (by simp) (by decide) hw2)
  have hX2 := xtop_sc_step (ct := σ.curThread) hX1 hP0 (by rw [kb1]; exact hNk) hW2 hK2 hS2 hR2 id
  have hss2 := hX1.ssTF hP0 (by rw [kb1]; exact hRk) (hW2.mono fun _ h => Or.inl h)
  have kb2 : L.ksb s2 = L.ksb s := hW2.1.trans kb1
  have hcw2 := callWords_of_nwfoot hS1 hRP1 hpC (hw2.mono fun b hb => hb.imp_left Or.inl)
  obtain ⟨hCR2, hRP2⟩ := CallRel.carry hCR1 hRP1 hcw2 hw2.1 hck2
  have hRF2 := RFree.carry hRF1 hCR1 hcw2.2 hck2
  obtain ⟨Q2, R2, hc2, hs2⟩ := hS2.lists
  obtain ⟨y2, n2, hk2, -⟩ := hs2.scs p hpC
  -- `unbind_reply`
  refine WP.spec_bind (unbind_reply_refines s2 σ2 hS2 hR2 hN2 hI2 hCR2 hRP2 hpC hp0 hk2 hRF2) ?_
  rintro s3 ⟨σ3, Lst3, he3, hS3, hR3, -, -, -, -, -, -, hw3⟩
  have hK3 : ScTKw (fun q => q = σ.curThread) σ2 σ3 :=
    (nkt_schedContextUnbindReply p.bv σ2 ((), σ3) (by rw [he3]; exact Set.mem_singleton _)).mono fun _ h => h.elim
  have hW3 : WritesIn st s2 s3 (fun b => TFoot st Z.T Z.N Z.C Z.c s2 σ2 b ∨ CallW' Z.R Z.C b) :=
    hw3.mono fun b hb => Or.inr (hb.imp (fun ⟨r, hr, e⟩ => ⟨r, hr, Or.inl e⟩) id)
  have hX3 := xtop_sc_stepCW (ct := σ.curThread) hX2 hP0 (by rw [kb2]; exact hNk) (by rw [kb2]; exact hRk) hW3
    hK3 hS3 hR3 id
  have hss3 := hX2.ssTF hP0 (by rw [kb2]; exact hRk) hW3
  have kb3 : L.ksb s3 = L.ksb s := hW3.1.trans kb2
  have hck3 : Fl4Proofs.P3.CKeep σ σ3 := (hK1.trans (hK2.trans hK3)).ckeep
  have hssA3 : SlotsSame Z.th (L.mem s) (L.mem s3) := hss1.trans (hss2.trans hss3)
  obtain ⟨Q3, R3, hc3, hs3⟩ := hS3.lists
  obtain ⟨y3, n3, hk3, hx3⟩ := hs3.scs p hpC
  -- the inactive SC and the post
  have fin5 : ∀ (s4 : S) (a4 : A) (σ4 : Fl4Spec.State Unit) (V : XVs), XTopAt (L := L) AR (Z.mv Z.G V) s4 a4 σ4 →
      SlotsSame Z.th (L.mem s) (L.mem s4) → L.ksb s4 = L.ksb s → Fl4Proofs.P3.CKeep σ σ4 →
      Fl4Spec.schedContextUnbindYieldFrom (Z := Unit) p.bv σ3 = ({((), σ4)}, False) →
      (do
        let s5 ← obj.Sc.set_refill_max st p s4 0#u64
        let s6 ← obj.Sc.set_sporadic st p s5 0#u64
        ok ((capability.Cap.Null, capability.Cap.Null), s6, a4)) ⦃ r =>
        FinXPost (L := L) AR Z s σ sl (.SchedContext p sb) r ⦄ := by
    intro s4 a4 σ4 V hX4 hss4 kb4 hck4 he4
    have hS4 := hX4.fin.1.1.1
    have hR4 := hX4.fin.1.1.2.2.1
    obtain ⟨Q4, R4, hc4, hs4⟩ := hS4.lists
    obtain ⟨y4, n4, hk4, -⟩ := hs4.scs p hpC
    step with obj.Sc.set_refill_max.spec as ⟨s5, hs5⟩
    step with obj.Sc.set_sporadic.spec2 as ⟨s6, hs6⟩
    subst hs5 hs6
    obtain ⟨hS6, hFE, hKV, hw6⟩ := hS4.set_inactive hpC hk4 hpi
    have hR6 := hR4.frame hS4.placed hFE hKV
    have he5 := setInactive_eq hk4
    have hK6 : ScTKw (fun q => q = σ.curThread) σ4 (updSc σ4 p.bv (inactSc y4) n4) :=
      (nkt_schedContextSetInactive p.bv σ4 ((), _) (by rw [he5]; exact Set.mem_singleton _)).mono fun _ h => h.elim
    have hW6 : WritesIn st s4 (L.wr (L.wr s4 (maxA p) 0#u64) (scW p 64#u64) 0#u64)
        (TFoot st Z.T Z.N Z.C Z.c s4 σ4) := by
      refine hw6.mono fun b hb => Or.inl (KFoot.of_sw ?_)
      rcases hb with rfl | rfl
      · exact sw_hdr hS4 hpC (K := 72#u64) (by simp) (by simp) (by decide)
      · exact sw_hdr hS4 hpC (K := 64#u64) (by simp) (by simp) (by decide)
    have hX6 := xtop_sc_step (ct := σ.curThread) hX4 hP0 (by rw [kb4]; exact hNk) hW6 hK6 hS6 hR6 id
    have hss6 := hX4.ssTF hP0 (by rw [kb4]; exact hRk) (hW6.mono fun _ h => Or.inl h)
    have hssA := hss4.trans hss6
    have hck := hck4.trans hK6.ckeep
    refine ⟨rfl, trivial, trivial, _, Z.G, ?_, DState.of_same hDS hssA hX6.rel.2.1 hck.ks,
      by rw [hssA.capV hA.isSlot]; exact capV_of_capAt hc, fun y hy _ => Or.inl (hssA.capV hy),
      MdbStep.of_same hDS.1.2.2.1 hssA, ⟨V, hX6⟩, hW6.1.trans kb4⟩
    rw [← hfd, hfin]
    exact finSc_mem he1 he2 he3 he4 he5
  -- the yielder
  step with obj.Sc.yield_from.spec' as ⟨i, hi⟩
  step with obj.Tcb.is_null.spec as ⟨b0, hb0⟩
  by_cases h0 : i = 0#u64
  · have hb : b0 = true := by rw [hb0, h0]; rfl
    simp only [hb, ↓reduceIte, bind_ok]
    refine fin5 s3 a1 σ3 Z.vs hX3 hssA3 kb3 hck3 (unbindYieldFrom_none hk3 ?_)
    rw [hx3.yieldFrom, ← scYieldFromA_eq, ← hi, h0, Notif.optRef_zero]
  · have hb : b0 = false := by rw [hb0]; simp [h0]
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    rw [hi]
    refine WP.spec_bind (hYp s3 a1 σ3 hX3 (by rw [← hi]; exact h0)) ?_
    rintro ⟨s4, a4⟩ ⟨σ4, V4, e4, hX4, hss4, kb4, hck4⟩
    refine fin5 s4 a4 σ4 V4 hX4 (hssA3.trans hss4) (kb4.trans kb3) (hck3.trans hck4) (unbindYieldFrom_some hk3 ?_ e4)
    rw [hx3.yieldFrom, ← scYieldFromA_eq, Notif.optRef_ne (by rw [← hi]; exact h0)]

end

end

end Fl4Proofs.P3
