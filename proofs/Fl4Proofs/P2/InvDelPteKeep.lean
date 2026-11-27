/-
# P2 (line invj, generation 4): stpost's `KeepS` with one more written set (the CNodeDelete PTE arm)

`KeepS` (P2/InvBlkFin.lean) lets the Delete decode block write the caller's `IoTW` words and capability-slot words.
The PTE arm also writes the leaf PTE. This module is the `keep` section of InvBlkFin copied verbatim with
`SlotW K` replaced by `SlotWX K X := SlotW K ∨ X` (an extra written set `X`, here the planned leaf `{e}`), and
`KeepS` / `SlotOK` renamed `KeepSX` / `SlotOKX`.

No named premise. No existing statement changes.
-/
import Fl4Proofs.P2.InvDelPteFin
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot
  slotOwner)

/-- A capability-slot word or a word of `X`. -/
def SlotWX (K : KLayout) (X : U64 → Prop) (b : U64) : Prop := SlotW K b ∨ X b

section keepX
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {X : U64 → Prop} {s0 x y : S} {t : U64}

variable (st) in
/-- From `s0`: only `IoTW t` and capability-slot words written, the action `RESUME_CURRENT`, `t` runnable. -/
def KeepSX (K : KLayout) (X : U64 → Prop) (s0 : S) (t : U64) (x : S) : Prop :=
  WritesIn st s0 x (fun b => IoTW t b ∨ SlotWX K X b) ∧ L.actionW x = sched.ACTION_RESUME_CURRENT ∧
    (L.mem x (stA t) = sched.TS_RESTART ∨ L.mem x (stA t) = sched.TS_RUNNING)

/-- The words `KeepSX`'s slot writes must miss, at `s0`. -/
structure SlotOKX (K : KLayout) (X : U64 → Prop) (s0 : S) (t : U64) : Prop where
  nd : ∀ o : U64, o.val < 4288 → ¬ SlotWX K X (L.nodeAt s0 (L.cpu s0) o)
  tf : ∀ k : U64, 192 ≤ k.val → k.val < 4096 → ¬ SlotWX K X (core.num.U64.wrapping_add t k)
  mx : ¬ SlotWX K X (maxA (L.mem s0 (scA t)))

theorem KeepSX.of_keepA (h : KeepA (L := L) s0 t x) : KeepSX st K X s0 t x :=
  ⟨h.1.mono fun _ hb => Or.inl hb, h.2⟩

theorem KeepSX.node (h : KeepSX st K X s0 t x) (o : U64) : L.nodeAt x (L.cpu x) o = L.nodeAt s0 (L.cpu s0) o := by
  rw [h.1.2.1, nodeAt_of_ksb h.1.1]

theorem KeepSX.mem (h : KeepSX st K X s0 t x) {b : U64} (hb : Aligned b) (hn : ¬ IoTW t b) (hs : ¬ SlotWX K X b) :
    L.mem x b = L.mem s0 b := h.1.2.2 b hb (fun h' => h'.elim hn hs)

theorem KeepSX.nd (F : SchedOK (L := L) s0 t) (O : SlotOKX (L := L) K X s0 t) (h : KeepSX st K X s0 t x) (o : U64)
    (ho : o.val < 4288) (h8 : o.val % 8 = 0) :
    L.mem x (L.nodeAt x (L.cpu x) o) = L.mem s0 (L.nodeAt s0 (L.cpu s0) o) := by
  rw [h.node]; exact h.mem (F.nd o ho h8).1 (F.nd o ho h8).2 (O.nd o ho)

theorem KeepSX.cur (F : SchedOK (L := L) s0 t) (O : SlotOKX (L := L) K X s0 t) (h : KeepSX st K X s0 t x) :
    L.curW x = t := by
  unfold LawfulStore.curW
  rw [h.nd F O _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])]; exact F.cur

/-- A TCB field of `t` from offset 3328 on (not `STATE`) is kept by `KeepSX`. -/
theorem KeepSX.tcbF (F : SchedOK (L := L) s0 t) (O : SlotOKX (L := L) K X s0 t) (h : KeepSX st K X s0 t x) {k : U64}
    (h1 : 3328 < k.val) (h2 : k.val < 4096) (h8 : k.val % 8 = 0) :
    L.mem x (core.num.U64.wrapping_add t k) = L.mem s0 (core.num.U64.wrapping_add t k) :=
  h.mem (field_aligned F.tcb h2 h8) (iotw_field F.tcb h2 h1) (O.tf k (by omega) h2)

/-- **`SchedOK` carried to a `KeepSX` state.** -/
theorem KeepSX.sched (F : SchedOK (L := L) s0 t) (O : SlotOKX (L := L) K X s0 t) (h : KeepSX st K X s0 t x) :
    SchedOK (L := L) x t := by
  have esc : L.mem x (scA t) = L.mem s0 (scA t) := h.tcbF F O (k := 3464#u64) (by simp) (by simp) (by simp)
  have eiq : L.mem x (inqA t) = L.mem s0 (inqA t) := h.tcbF F O (k := 3592#u64) (by simp) (by simp) (by simp)
  have emx : L.rmax x (L.mem s0 (scA t)) = L.rmax s0 (L.mem s0 (scA t)) := by
    unfold LawfulStore.rmax; exact h.mem F.mx.1 F.mx.2 O.mx
  refine ⟨F.tcb, h.cur F O, ?_, ?_, ?_, ?_, ?_⟩
  · rw [esc]; exact F.sc
  · rw [esc, emx]; exact F.act
  · rw [eiq]; exact F.nr
  · intro o ho h8; rw [h.node]; exact F.nd o ho h8
  · rw [esc]; exact F.mx

/-- `KeepSX` then a `KeepA` step. -/
theorem KeepSX.keepA (h : KeepSX st K X s0 t x) (h' : KeepA (L := L) x t y) : KeepSX st K X s0 t y :=
  ⟨(h.1.trans h'.1).mono fun _ hb => by rcases hb with hb | hb; exact hb; exact Or.inl hb, h'.2⟩

/-- `KeepSX` then writes of slot words only. -/
theorem KeepSX.slots (F : SchedOK (L := L) s0 t) (O : SlotOKX (L := L) K X s0 t) (h : KeepSX st K X s0 t x)
    (w : WritesIn st x y (SlotWX K X)) : KeepSX st K X s0 t y := by
  have hn := F.nd layout.node.SCHED_ACTION (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
  refine ⟨(h.1.trans w).mono fun _ hb => by rcases hb with hb | hb; exact hb; exact Or.inr hb, ?_, ?_⟩
  · unfold LawfulStore.actionW
    rw [wi_node w, h.node, w.2.2 _ hn.1 (O.nd _ (by simp [layout.node.SCHED_ACTION])), ← h.node]
    exact h.2.1
  · have e : L.mem y (stA t) = L.mem x (stA t) :=
      w.2.2 _ (iotw_aligned F.tcb (Or.inr rfl)) (O.tf _ (by rw [st_val]; omega) (by rw [st_val]; omega))
    rw [e]; exact h.2.2

/-- **`finish`'s queue reads survive the invocation** (`KeepA.fin` with slot writes): the slot writes miss the
earliest timer's deadline word, the release head's SC word, and that SC's head / refill-time words. -/
theorem KeepSX.fin (F : SchedOK (L := L) s0 t) (O : SlotOKX (L := L) K X s0 t) (Q : QOK (L := L) s0 t)
    (h : KeepSX st K X s0 t x)
    {R : U64 → Prop} (hnd : NoDue (L := L) s0)
    (htd : L.mem s0 (tmA (L := L) s0) ≠ 0#u64 →
      R (core.num.U64.wrapping_add (L.mem s0 (tmA (L := L) s0)) 3528#u64))
    (hrs : L.mem s0 (rhA (L := L) s0) ≠ 0#u64 → R (scA (L.mem s0 (rhA (L := L) s0))) ∧
      RdHead (L := L) R s0 (L.mem s0 (scA (L.mem s0 (rhA (L := L) s0)))))
    (stm : L.mem s0 (tmA (L := L) s0) ≠ 0#u64 → ¬ SlotWX K X (tdA (L.mem s0 (tmA (L := L) s0))))
    (srh : L.mem s0 (rhA (L := L) s0) ≠ 0#u64 → ¬ SlotWX K X (scA (L.mem s0 (rhA (L := L) s0))) ∧
      ¬ SlotWX K X (headA (L.mem s0 (scA (L.mem s0 (rhA (L := L) s0))))) ∧
      ¬ SlotWX K X (rtA (L.mem s0 (scA (L.mem s0 (rhA (L := L) s0))))
        (L.rhead s0 (L.mem s0 (scA (L.mem s0 (rhA (L := L) s0))))))) :
    NoDue (L := L) x ∧
    (L.mem x (tmA (L := L) x) ≠ 0#u64 →
      R (core.num.U64.wrapping_add (L.mem x (tmA (L := L) x)) 3528#u64)) ∧
    (L.mem x (rhA (L := L) x) ≠ 0#u64 → R (scA (L.mem x (rhA (L := L) x))) ∧
      RdHead (L := L) R x (L.mem x (scA (L.mem x (rhA (L := L) x))))) := by
  have eT : L.mem x (tmA (L := L) x) = L.mem s0 (tmA (L := L) s0) :=
    h.nd F O _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
  have eR : L.mem x (rhA (L := L) x) = L.mem s0 (rhA (L := L) s0) :=
    h.nd F O _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
  have eC : L.curTime x = L.curTime s0 := by
    unfold LawfulStore.curTime LawfulStore.nodeA
    exact h.nd F O _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
  have eS : ∀ h0 : L.mem s0 (rhA (L := L) s0) ≠ 0#u64,
      L.mem x (scA (L.mem s0 (rhA (L := L) s0))) = L.mem s0 (scA (L.mem s0 (rhA (L := L) s0))) := fun h0 =>
    h.mem (field_aligned (Q.rh h0) (by simp) (by simp)) (iotw_tcb F.tcb (Q.rh h0) (by simp) (by simp))
      (srh h0).1
  have eH : ∀ h0 : L.mem s0 (rhA (L := L) s0) ≠ 0#u64,
      L.rhead x (L.mem s0 (scA (L.mem s0 (rhA (L := L) s0)))) =
        L.rhead s0 (L.mem s0 (scA (L.mem s0 (rhA (L := L) s0)))) := fun h0 => by
    unfold LawfulStore.rhead; exact h.mem (Q.hd h0).1 (Q.hd h0).2.1 (srh h0).2.1
  obtain ⟨n1, n2⟩ := hnd
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · show L.mem x (tmA (L := L) x) = 0#u64 ∨ L.mem x (L.nodeAt x (L.cpu x) layout.node.CUR_TIME) <
      L.mem x (tdA (L.mem x (tmA (L := L) x)))
    rw [eT, h.nd F O _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])]
    by_cases h0 : L.mem s0 (tmA (L := L) s0) = 0#u64
    · exact Or.inl h0
    right
    have e := h.mem (field_aligned (Q.tm h0) (by simp) (by simp)) (iotw_tcb F.tcb (Q.tm h0) (by simp) (by simp))
      (stm h0)
    unfold tdA at e ⊢
    rw [e]
    exact n1.resolve_left h0
  · show L.mem x (rhA (L := L) x) = 0#u64 ∨ ¬ ((L.refill x (L.mem x (scA (L.mem x (rhA (L := L) x))))
      (L.rhead x (L.mem x (scA (L.mem x (rhA (L := L) x)))))).time ≤ L.curTime x)
    rw [eR, eC]
    by_cases h0 : L.mem s0 (rhA (L := L) s0) = 0#u64
    · exact Or.inl h0
    right
    rw [eS h0, eH h0]
    unfold LawfulStore.refill
    simp only
    rw [h.mem (Q.hd h0).2.2.1 (Q.hd h0).2.2.2 (srh h0).2.2]
    exact n2.resolve_left h0
  · rw [eT]; exact htd
  · rw [eR]; intro h0
    refine ⟨(hrs h0).1, ?_⟩
    rw [eS h0]
    unfold RdHead; rw [eH h0]; exact (hrs h0).2

end keepX

end Fl4Proofs.P2.PathObl
