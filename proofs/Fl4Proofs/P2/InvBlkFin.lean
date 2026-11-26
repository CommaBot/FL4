/-
# P2 (line stpost, generation 13): `FinOK` after the CNodeDelete-no-PTE decode block

The I/O port's `io_hfin` route (AccessIoEnt) for the frame-cap invocation's Delete arm. The I/O port's
invocation writes only the caller's register / `STATE` words (`KeepA`); the Delete arm also writes capability-slot
words (the target's four words, its `PREV` neighbour's `NEXT` word, its `NEXT` neighbour's `PREV` / `NEXT` words).
Those lie in `region … = .slot q`, disjoint from the node, the TCB fields from offset 192 and the SC words, so every
fact `finish` needs survives them.

* `SlotW K b` (a word of a capability slot), `KeepS K s0 t x` (`KeepA` with slot-word writes too), `SlotOK`
  (the node words and `t`'s TCB fields from offset 192 are no slot words, nor `t`'s SC's `REFILL_MAX`);
* `KeepS.mem`, `KeepS.cur`, `KeepS.sched` (`SchedOK` carried to a `KeepS` state), `KeepS.keepA` (then a `KeepA`
  step), `KeepS.slots` (then slot writes), `KeepS.fin` (`KeepA.fin` with slot writes);
* `SwOK.frameE` (`SwOK.frame` for the prefix writes and slot writes, given the slot words miss the node, the TCB
  fields from offset 3328 and `Ω`), `SwOK.shrink` (`Ω` cut to the SC words of `Scs`);
* the run: `finCap_frame_keep`, `finImm_frame_keep`, `emptySlot_keep`, `del_frame_keep` (deleting a slot holding an
  unmapped (or ASID 0) small RAM frame cap returns `Ok ()` and writes slot words only), `cnDel_keep` (the CNode
  decode at `CNodeDelete` with `length ≥ 2` and the target's facts), `decode_cnode_eq`, `invRep_ok_keep`,
  `decDel_keep` (decode then `invRep`: `KeepS` from the decode state, reply `Ok ()`);
* **`delFin`**: `FinOK` after the decode block at an accepted run's post-prefix state.

No named premise: `delFin` takes the entry facts (`IoPre`, `DelEnt`), the plan's slot a capability slot (`hsl`,
from the plan side's `del_core`), and `hlen : ¬ length < 2`. The latter is a real restriction of the arm: with
`length < 2` the Delete decode returns `TruncatedMessage`, and `invRep` replies through `reply_error`, which (with
`KERNEL_INVOCATION_REPORT_ERROR_IPC = true` and a set IPC buffer) reads and writes a word of the caller's IPC
buffer, a user word outside `IoRS` / `IoWS`. No existing statement changes; no `kernel_entry_reach*` is touched.
-/
import Fl4Proofs.P2.InvDelEnt
import Fl4Proofs.P3.StPostInvAcc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot
  slotOwner)

/-- A word of a capability slot. -/
def SlotW (K : KLayout) (b : U64) : Prop := ∃ q ∈ K.slots, InW q 32 b

section keep
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {s0 x y : S} {t : U64}

variable (st) in
/-- From `s0`: only `IoTW t` and capability-slot words written, the action `RESUME_CURRENT`, `t` runnable. -/
def KeepS (K : KLayout) (s0 : S) (t : U64) (x : S) : Prop :=
  WritesIn st s0 x (fun b => IoTW t b ∨ SlotW K b) ∧ L.actionW x = sched.ACTION_RESUME_CURRENT ∧
    (L.mem x (stA t) = sched.TS_RESTART ∨ L.mem x (stA t) = sched.TS_RUNNING)

/-- The words `KeepS`'s slot writes must miss, at `s0`. -/
structure SlotOK (K : KLayout) (s0 : S) (t : U64) : Prop where
  nd : ∀ o : U64, o.val < 4288 → ¬ SlotW K (L.nodeAt s0 (L.cpu s0) o)
  tf : ∀ k : U64, 192 ≤ k.val → k.val < 4096 → ¬ SlotW K (core.num.U64.wrapping_add t k)
  mx : ¬ SlotW K (maxA (L.mem s0 (scA t)))

theorem KeepS.of_keepA (h : KeepA (L := L) s0 t x) : KeepS st K s0 t x :=
  ⟨h.1.mono fun _ hb => Or.inl hb, h.2⟩

theorem KeepS.node (h : KeepS st K s0 t x) (o : U64) : L.nodeAt x (L.cpu x) o = L.nodeAt s0 (L.cpu s0) o := by
  rw [h.1.2.1, nodeAt_of_ksb h.1.1]

theorem KeepS.mem (h : KeepS st K s0 t x) {b : U64} (hb : Aligned b) (hn : ¬ IoTW t b) (hs : ¬ SlotW K b) :
    L.mem x b = L.mem s0 b := h.1.2.2 b hb (fun h' => h'.elim hn hs)

theorem KeepS.nd (F : SchedOK (L := L) s0 t) (O : SlotOK (L := L) K s0 t) (h : KeepS st K s0 t x) (o : U64)
    (ho : o.val < 4288) (h8 : o.val % 8 = 0) :
    L.mem x (L.nodeAt x (L.cpu x) o) = L.mem s0 (L.nodeAt s0 (L.cpu s0) o) := by
  rw [h.node]; exact h.mem (F.nd o ho h8).1 (F.nd o ho h8).2 (O.nd o ho)

theorem KeepS.cur (F : SchedOK (L := L) s0 t) (O : SlotOK (L := L) K s0 t) (h : KeepS st K s0 t x) :
    L.curW x = t := by
  unfold LawfulStore.curW
  rw [h.nd F O _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])]; exact F.cur

/-- A TCB field of `t` from offset 3328 on (not `STATE`) is kept by `KeepS`. -/
theorem KeepS.tcbF (F : SchedOK (L := L) s0 t) (O : SlotOK (L := L) K s0 t) (h : KeepS st K s0 t x) {k : U64}
    (h1 : 3328 < k.val) (h2 : k.val < 4096) (h8 : k.val % 8 = 0) :
    L.mem x (core.num.U64.wrapping_add t k) = L.mem s0 (core.num.U64.wrapping_add t k) :=
  h.mem (field_aligned F.tcb h2 h8) (iotw_field F.tcb h2 h1) (O.tf k (by omega) h2)

/-- **`SchedOK` carried to a `KeepS` state.** -/
theorem KeepS.sched (F : SchedOK (L := L) s0 t) (O : SlotOK (L := L) K s0 t) (h : KeepS st K s0 t x) :
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

/-- `KeepS` then a `KeepA` step. -/
theorem KeepS.keepA (h : KeepS st K s0 t x) (h' : KeepA (L := L) x t y) : KeepS st K s0 t y :=
  ⟨(h.1.trans h'.1).mono fun _ hb => by rcases hb with hb | hb; exact hb; exact Or.inl hb, h'.2⟩

/-- `KeepS` then writes of slot words only. -/
theorem KeepS.slots (F : SchedOK (L := L) s0 t) (O : SlotOK (L := L) K s0 t) (h : KeepS st K s0 t x)
    (w : WritesIn st x y (SlotW K)) : KeepS st K s0 t y := by
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
theorem KeepS.fin (F : SchedOK (L := L) s0 t) (O : SlotOK (L := L) K s0 t) (Q : QOK (L := L) s0 t)
    (h : KeepS st K s0 t x)
    {R : U64 → Prop} (hnd : NoDue (L := L) s0)
    (htd : L.mem s0 (tmA (L := L) s0) ≠ 0#u64 →
      R (core.num.U64.wrapping_add (L.mem s0 (tmA (L := L) s0)) 3528#u64))
    (hrs : L.mem s0 (rhA (L := L) s0) ≠ 0#u64 → R (scA (L.mem s0 (rhA (L := L) s0))) ∧
      RdHead (L := L) R s0 (L.mem s0 (scA (L.mem s0 (rhA (L := L) s0)))))
    (stm : L.mem s0 (tmA (L := L) s0) ≠ 0#u64 → ¬ SlotW K (tdA (L.mem s0 (tmA (L := L) s0))))
    (srh : L.mem s0 (rhA (L := L) s0) ≠ 0#u64 → ¬ SlotW K (scA (L.mem s0 (rhA (L := L) s0))) ∧
      ¬ SlotW K (headA (L.mem s0 (scA (L.mem s0 (rhA (L := L) s0))))) ∧
      ¬ SlotW K (rtA (L.mem s0 (scA (L.mem s0 (rhA (L := L) s0))))
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

end keep

/-! ## `SwOK` across slot writes -/

section frame
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} [L : LawfulStore st]
variable {K : KLayout} {T Cs Ω : Set U64} {x y : S} {c : U64} {zc : Nat}

section
variable (F : SwOK st T Cs Ω R W x c zc) (w : WritesIn st x y (fun b => IoPW st x b ∨ SlotW K b))
  (hn : ∀ o : U64, o.val < 4288 → ¬ SlotW K (L.nodeAt x (L.cpu x) o))
  (ht : ∀ t ∈ T, ∀ k : U64, 3328 < k.val → k.val < 4096 → ¬ SlotW K (core.num.U64.wrapping_add t k))
  (ho : ∀ b ∈ Ω, ¬ SlotW K b)
include F w hn

theorem SwOK.nodeE (o : U64) (ho' : o.val < 4288) (h8 : o.val % 8 = 0)
    (hno : ¬ (o.val = 16 ∨ o.val = 40 ∨ o.val = 48)) :
    L.mem y (L.nodeAt y (L.cpu y) o) = L.mem x (L.nodeAt x (L.cpu x) o) := by
  rw [wi_node w]
  refine w.2.2 _ (nodeAt_aligned F.np ho' h8) ?_
  rintro ((⟨o', ho'', e⟩ | ⟨r, hr, e⟩ | e) | hs)
  · by_cases hv : o.val = o'.val
    · omega
    · exact nodeAt_ne F.np ho' (by omega) hv e
  · have hv := congrArg UScalar.val e
    rw [regA_val (F.tp _ F.cT) hr, nodeAt_val F.np ho'] at hv
    have := F.np.disj _ F.cT; omega
  · exact node_ne_field F.np ho' F.cT (F.tp _ F.cT) (by rw [st_val]; omega) e
  · exact hn o ho' hs

omit hn in
include ht in
theorem SwOK.tcbE {t k : U64} (htT : t ∈ T) (hk : k.val < 4096) (h8 : k.val % 8 = 0) (hge : 3328 < k.val) :
    L.mem y (core.num.U64.wrapping_add t k) = L.mem x (core.num.U64.wrapping_add t k) := by
  refine w.2.2 _ (field_aligned (F.tp t htT) hk h8) ?_
  rintro ((⟨o, ho', e⟩ | hi) | hs)
  · exact node_ne_field F.np (by omega) htT (F.tp t htT) hk e.symm
  · exact iotw_tcb (F.tp _ F.cT) (F.tp t htT) hk hge hi
  · exact ht t htT k hge hk hs

omit hn in
include ho in
theorem SwOK.omE {b : U64} (hb : b ∈ Ω) : L.mem y b = L.mem x b := by
  refine w.2.2 _ (F.om b hb).1 ?_
  have htt := F.tp _ F.cT
  have h1 := (F.om b hb).2.1 _ F.cT
  rintro ((⟨o, ho', e⟩ | ⟨r, hr, e⟩ | e) | hs)
  · exact out_ne_node (F.om b hb) F.cpu F.np (by omega) (congrArg UScalar.val e).symm
  · have hv := congrArg UScalar.val e
    rw [regA_val htt hr] at hv; omega
  · have hv := congrArg UScalar.val e
    unfold stA at hv
    rw [tcb_wadd_val htt (by rw [st_val]; omega), st_val] at hv; omega
  · exact ho b hb hs

include ht ho in
/-- **`SwOK` survives the prefix writes and slot writes** missing the node, the TCB fields and `Ω`. -/
theorem SwOK.frameE : SwOK st T Cs Ω R W y c zc := by
  have hcur : L.curW y = L.curW x := F.nodeE w hn _ (by simp [layout.node.CUR_THREAD])
    (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
  have hcsc : L.mem y (L.nodeA y layout.node.CUR_SC) = L.mem x (L.nodeA x layout.node.CUR_SC) :=
    F.nodeE w hn _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have htm : L.mem y (tmA (L := L) y) = L.mem x (tmA (L := L) x) :=
    F.nodeE w hn _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN])
  have hrh : L.mem y (rhA (L := L) y) = L.mem x (rhA (L := L) x) :=
    F.nodeE w hn _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD])
  have hcs : ∀ t ∈ T, L.mem y (scA t) = L.mem x (scA t) := fun t htT =>
    F.tcbE w ht htT (k := 3464#u64) (by simp) (by simp) (by simp)
  have hmx : L.rmax y c = L.rmax x c := F.omE w ho (F.q.2.1 _ F.q.2.2.2.2 F.q.2.2.2.1)
  have wfE : RefillsWF st x c zc → RefillsWF st y c zc := fun h =>
    h.agree fun b hb hin => F.omE w ho (F.q.2.1 b hb hin)
  refine ⟨F.tp, ?_, ?_, ?_, ?_, hcsc.trans F.csc, ?_, ⟨?_, F.q.2⟩, ?_, F.acc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [w.2.1]; exact F.cpu
  · rw [w.2.1]; exact F.np.ksb w.1
  · exact fun a ha => (F.om a ha).ksb w.1
  · rw [hcur]; exact F.cT
  · rw [hcur, hcs _ F.cT]; exact F.i
  · rw [hmx]; exact fun h => wfE (F.q.1 h)
  · rw [hmx]; exact F.act
  · intro o ho' h8; rw [wi_node w]; exact F.nd o ho' h8
  · rw [hcur]; exact F.sc
  · rw [w.1]; exact F.dt
  · rw [htm]; exact F.td
  · rw [hrh]
    intro h0
    rw [hcs _ (F.rh h0).1]
    refine ⟨(F.rs h0).1, ?_⟩
    rcases (F.rh h0).2 with e | ⟨ho', ho''⟩
    · rw [e]; exact F.acc.head (wfE (F.q.1 F.act))
    · have hb : L.rhead y (L.mem x (scA (L.mem x (rhA (L := L) x)))) =
          L.rhead x (L.mem x (scA (L.mem x (rhA (L := L) x)))) := F.omE w ho ho'
      have := (F.rs h0).2
      unfold RdHead at this ⊢
      rw [hb]; exact this
  · rw [hrh]
    intro h0
    rw [hcs _ (F.rh h0).1]; exact F.rh h0

end

/-- **`Ω` cut to the SC words of `Scs`**: `SwOK` keeps holding (the current SC is in `Scs` with size `Z c`, and the
release head's SC, when there is one, is in `Scs` with its head word inside it). -/
theorem SwOK.shrink {Scs : Set U64} {Z : U64 → Nat} (F : SwOK st T Cs Ω R W x c zc) (hc : c ∈ Scs) (hz : zc = Z c)
    (hrh : L.mem x (rhA (L := L) x) ≠ 0#u64 → L.mem x (scA (L.mem x (rhA (L := L) x))) ∈ Scs ∧
      InSC (L.mem x (scA (L.mem x (rhA (L := L) x)))) (Z (L.mem x (scA (L.mem x (rhA (L := L) x)))))
        (headA (L.mem x (scA (L.mem x (rhA (L := L) x)))))) :
    SwOK st T Cs {b | b ∈ Ω ∧ ∃ c' ∈ Scs, InSC c' (Z c') b} R W x c zc := by
  refine ⟨F.tp, F.cpu, F.np, fun a ha => F.om a ha.1, F.cT, F.csc, F.i,
    ⟨F.q.1, fun b hb hin => ⟨F.q.2.1 b hb hin, c, hc, hz ▸ hin⟩, F.q.2.2⟩, F.act, F.acc, F.nd, F.sc, F.dt, F.td,
    F.rs, fun h0 => ⟨(F.rh h0).1, ?_⟩⟩
  rcases (F.rh h0).2 with e | ⟨ho, hout⟩
  · exact Or.inl e
  · exact Or.inr ⟨⟨ho, _, (hrh h0).1, (hrh h0).2⟩, hout⟩

end frame

/-! ## The run: slot writes -/

section run
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} (ar : machine.Arch A)
variable {K : KLayout}

/-- The capability slots' layout facts (`IoLay.slot8`). -/
abbrev Slot8 (K : KLayout) : Prop := ∀ q ∈ K.slots, q.val % 8 = 0 ∧ q.val + 32 ≤ 2 ^ 64

theorem slotW_of {q o : U64} (hL : Slot8 K) (hq : q ∈ K.slots) (ho : o.val < 32) :
    SlotW K (core.num.U64.wrapping_add q o) := ⟨q, hq, slot_inW (hL q hq).2 ho⟩

theorem slot_al {q o : U64} (hL : Slot8 K) (hq : q ∈ K.slots) (ho : o.val < 32) (h8 : o.val % 8 = 0) :
    Aligned (core.num.U64.wrapping_add q o) := by
  unfold Aligned; rw [slot_word_val (hL q hq).2 ho]; have := (hL q hq).1; omega

theorem wr_slotW {x : S} {q o v : U64} (hL : Slot8 K) (hq : q ∈ K.slots) (ho : o.val < 32) (h8 : o.val % 8 = 0) :
    WritesIn st x (L.wr x (core.num.U64.wrapping_add q o) v) (SlotW K) :=
  (writesIn_wr (slot_al hL hq ho h8)).mono fun _ hb => by subst hb; exact slotW_of hL hq ho

theorem set_next_keep {x x' : S} {q n : U64} (hL : Slot8 K) (hq : q ∈ K.slots)
    (h : obj.Slot.set_next st q x n = ok x') : WritesIn st x x' (SlotW K) := by
  unfold obj.Slot.set_next obj.Slot.next_word at h
  simp only [lift, bind_ok, L.read_eq, L.write_eq] at h
  cases ok_inj_ff h
  exact wr_slotW hL hq (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT])

theorem set_prev_keep {x x' : S} {q n : U64} (hL : Slot8 K) (hq : q ∈ K.slots)
    (h : obj.Slot.set_prev st q x n = ok x') : WritesIn st x x' (SlotW K) := by
  unfold obj.Slot.set_prev at h
  simp only [lift, bind_ok, L.write_eq] at h
  cases ok_inj_ff h
  exact wr_slotW hL hq (by simp [layout.cte.PREV]) (by simp [layout.cte.PREV])

theorem set_fb_keep {x x' : S} {q : U64} {v : Bool} (hL : Slot8 K) (hq : q ∈ K.slots)
    (h : obj.Slot.set_first_badged st q x v = ok x') : WritesIn st x x' (SlotW K) := by
  unfold obj.Slot.set_first_badged obj.Slot.next_word at h
  simp only [lift, bind_ok, L.read_eq] at h
  obtain ⟨i1, -, h⟩ := bind_eq_ok h
  cases v
  · simp only [Bool.false_eq_true, ↓reduceIte, lift, bind_ok, L.write_eq] at h
    cases ok_inj_ff h
    exact wr_slotW hL hq (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT])
  · simp only [↓reduceIte, lift, bind_ok, L.write_eq] at h
    cases ok_inj_ff h
    exact wr_slotW hL hq (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT])

theorem clear_keep {x x' : S} {q : U64} (hL : Slot8 K) (hq : q ∈ K.slots)
    (h : obj.Slot.clear st q x = ok x') : WritesIn st x x' (SlotW K) := by
  unfold obj.Slot.clear at h
  simp only [lift, bind_ok, L.write_eq] at h
  cases ok_inj_ff h
  have w0 : WritesIn st x (L.wr x q 0#u64) (SlotW K) := by
    have e : core.num.U64.wrapping_add q 0#u64 = q := by
      apply UScalar.eq_of_val_eq; rw [slot_word_val (hL q hq).2 (by simp)]; simp
    have := wr_slotW (st := st) (x := x) (v := 0#u64) hL hq (o := 0#u64) (by simp) (by simp)
    rw [e] at this; exact this
  exact ((w0.trans1 (wr_slotW hL hq (by simp) (by simp))).trans1 (wr_slotW hL hq (by simp) (by simp))).trans1
    (wr_slotW hL hq (by simp) (by simp))

/-- **`empty_slot` with a null cleanup writes slot words only**, given the slot and its CDT neighbours (when not
null) are capability slots. -/
theorem emptySlot_keep {x : S} {a : A} {slot : U64} {y : S × A} (hL : Slot8 K) (hd : slot ∈ K.slots)
    (hp : L.mem x (core.num.U64.wrapping_add slot layout.cte.PREV) ≠ 0#u64 →
      L.mem x (core.num.U64.wrapping_add slot layout.cte.PREV) ∈ K.slots)
    (hn : ∀ nx, obj.Slot.next st slot x = ok nx → nx ≠ 0#u64 → nx ∈ K.slots)
    (h : cdt.empty_slot st ar x a slot .Null = ok y) : WritesIn st x y.1 (SlotW K) ∧ y.2 = a := by
  unfold cdt.empty_slot at h
  obtain ⟨c, -, h⟩ := bind_eq_ok h
  obtain ⟨b, -, h⟩ := bind_eq_ok h
  by_cases hb : b = true
  · rw [if_pos hb] at h; cases ok_inj_ff h; exact ⟨WritesIn.refl _ _, rfl⟩
  rw [if_neg hb] at h
  obtain ⟨prev, ep, h⟩ := bind_eq_ok h
  have eprev : prev = L.mem x (core.num.U64.wrapping_add slot layout.cte.PREV) := by
    unfold obj.Slot.prev at ep; simp only [lift, bind_ok, L.read_eq] at ep; exact (ok_inj_ff ep).symm
  obtain ⟨nx, en, h⟩ := bind_eq_ok h
  obtain ⟨fb, -, h⟩ := bind_eq_ok h
  obtain ⟨b1, eb1, h⟩ := bind_eq_ok h
  obtain ⟨s1, es1, h⟩ := bind_eq_ok h
  have w1 : WritesIn st x s1 (SlotW K) := by
    unfold obj.Slot.is_null at eb1
    have e1 := ok_inj_ff eb1
    by_cases hb1 : b1 = true
    · rw [if_pos hb1] at es1; cases ok_inj_ff es1; exact WritesIn.refl _ _
    · rw [if_neg hb1] at es1
      have hne : prev ≠ 0#u64 := fun e0 => hb1 (by rw [← e1]; simp [e0])
      exact set_next_keep hL (eprev ▸ hp (eprev ▸ hne)) es1
  obtain ⟨b2, eb2, h⟩ := bind_eq_ok h
  obtain ⟨s2, es2, h⟩ := bind_eq_ok h
  have w2 : WritesIn st s1 s2 (SlotW K) := by
    unfold obj.Slot.is_null at eb2
    have e2 := ok_inj_ff eb2
    by_cases hb2 : b2 = true
    · rw [if_pos hb2] at es2; cases ok_inj_ff es2; exact WritesIn.refl _ _
    · rw [if_neg hb2] at es2
      have hne : nx ≠ 0#u64 := fun e0 => hb2 (by rw [← e2]; simp [e0])
      have hq := hn nx en hne
      obtain ⟨s3, es3, es2⟩ := bind_eq_ok es2
      obtain ⟨nfb, -, es2⟩ := bind_eq_ok es2
      have w3 := set_prev_keep hL hq es3
      by_cases hf : nfb = true
      · rw [if_pos hf] at es2; exact w3.trans1 (set_fb_keep hL hq es2)
      · rw [if_neg hf] at es2; exact w3.trans1 (set_fb_keep hL hq es2)
  obtain ⟨s3, es3, h⟩ := bind_eq_ok h
  have w3 := clear_keep hL hd es3
  simp only [objects.post_cap_deletion] at h
  cases ok_inj_ff h
  exact ⟨(w1.trans1 w2).trans1 w3, rfl⟩

/-- `finalise_cap` of an unmapped (or ASID 0) non-device non-EPT frame cap: no access, null remainder and
cleanup. -/
theorem finCap_frame_keep {x : S} {a : A} {fp rt asid va : U64} {sz : capability.FrameSize} {mp fin : Bool}
    (hm : mp = false ∨ asid = 0#u64) {y : (capability.Cap × capability.Cap) × S × A}
    (h : objects.finalise_cap st ar x a (.Frame fp sz rt false mp false asid va) fin false = ok y) :
    y = ((.Null, .Null), x, a) := by
  unfold objects.finalise_cap objects.finalise_cap_object at h
  simp only [bind_ok] at h
  rcases hm with rfl | rfl
  · cases fin <;> simp at h <;> exact h.symm
  · cases mp <;> cases fin <;> simp at h <;> exact h.symm

set_option maxHeartbeats 4000000 in
/-- **`finalise_slot_immediate` on such a frame cap returns at its first round**, the state unchanged, with a null
cleanup. -/
theorem finImm_frame_keep {x : S} {a : A} {slot fp rt asid va : U64} {mp : Bool}
    (hc : obj.Slot.cap st slot x = ok (.Frame fp .Small rt false mp false asid va))
    (hm : mp = false ∨ asid = 0#u64) {y : core.result.Result cdt.Finalised error.Exc × S × A}
    (h : cdt.finalise_slot_immediate st ar x a slot = ok y) :
    y = (.Ok { success := true, cleanup := .Null }, x, a) := by
  unfold cdt.finalise_slot_immediate cdt.finalise_slot_immediate_loop at h
  rw [loop] at h
  obtain ⟨cf, hb, h⟩ := bind_eq_ok h
  have hf : layout.WALK_FUEL > 0#u64 := by simp [layout.WALK_FUEL, U64.rMax]
  obtain ⟨v, hv, -⟩ := spec_ex_fd (U64.sub_spec (x := layout.WALK_FUEL) (y := 1#u64)
    (by simp [layout.WALK_FUEL, U64.rMax]))
  unfold cdt.finalise_slot_immediate_loop.body at hb
  simp only [hf, ↓reduceIte, hv, bind_ok, hc, capability.Cap.is_null, Bool.false_eq_true] at hb
  obtain ⟨fin, -, hb⟩ := bind_eq_ok hb
  obtain ⟨⟨⟨rem, cl⟩, s1, a1⟩, hfc, hb⟩ := bind_eq_ok hb
  have e := finCap_frame_keep ar hm hfc
  simp only [Prod.mk.injEq] at e
  obtain ⟨⟨hr1, hr2⟩, hs1, ha1⟩ := e
  rw [hr1, hr2, hs1, ha1] at hb
  simp only [cdt.cap_removable, bind_ok, ↓reduceIte, uncurry_apply_pair] at hb
  rw [← ok_inj_ff hb] at h
  try dsimp only at h
  exact (ok_inj_ff h).symm

/-- **Deleting a slot that holds an unmapped (or ASID 0) small RAM frame cap** returns `Ok ()` and writes slot
words only. -/
theorem del_frame_keep {x : S} {a : A} {dest fp rt asid va : U64} {mp : Bool} (hL : Slot8 K) (hd : dest ∈ K.slots)
    (hc : obj.Slot.cap st dest x = ok (.Frame fp .Small rt false mp false asid va))
    (hm : mp = false ∨ asid = 0#u64)
    (hp : L.mem x (core.num.U64.wrapping_add dest layout.cte.PREV) ≠ 0#u64 →
      L.mem x (core.num.U64.wrapping_add dest layout.cte.PREV) ∈ K.slots)
    (hn : ∀ nx, obj.Slot.next st dest x = ok nx → nx ≠ 0#u64 → nx ∈ K.slots)
    {y : core.result.Result Unit error.Exc × S × A}
    (h : cdt.delete st ar x a dest true = ok y) : y.1 = .Ok () ∧ WritesIn st x y.2.1 (SlotW K) := by
  unfold cdt.delete at h
  simp only [↓reduceIte] at h
  obtain ⟨⟨r, s1, a1⟩, hf, h⟩ := bind_eq_ok h
  have e := finImm_frame_keep ar hc hm hf
  simp only [Prod.mk.injEq] at e
  obtain ⟨hr, hs1, ha1⟩ := e
  rw [hr, hs1, ha1] at h
  obtain ⟨cf, ecf, h⟩ := bind_eq_ok h
  try simp only [core.result.Result.Insts.CoreOpsTry.branch] at ecf
  rw [← ok_inj_ff ecf] at h
  try dsimp only at h
  obtain ⟨⟨s2, a2⟩, he, h⟩ := bind_eq_ok h
  rw [← ok_inj_ff h]
  exact ⟨rfl, (emptySlot_keep ar hL hd hp hn he).1⟩

end run

/-! ## The decode block: `KeepS` -/

section dec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} (ar : machine.Arch A)
variable {K : KLayout}

theorem lblD1 : ¬ fl4_abi.label.CNodeDelete < fl4_abi.label.CNodeRevoke := by
  have h1 : fl4_abi.label.CNodeRevoke.val = 25 := by simp [fl4_abi.label.CNodeRevoke]
  have h2 : fl4_abi.label.CNodeDelete.val = 26 := by simp [fl4_abi.label.CNodeDelete]
  scalar_tac
theorem lblD2 : ¬ fl4_abi.label.CNodeDelete > fl4_abi.label.CNodeRotate := by
  have h1 : fl4_abi.label.CNodeRotate.val = 32 := by simp [fl4_abi.label.CNodeRotate]
  have h2 : fl4_abi.label.CNodeDelete.val = 26 := by simp [fl4_abi.label.CNodeDelete]
  scalar_tac
theorem lblD3 : ¬ fl4_abi.label.CNodeDelete ≥ fl4_abi.label.CNodeCopy := by
  have h1 : fl4_abi.label.CNodeCopy.val = 28 := by simp [fl4_abi.label.CNodeCopy]
  have h2 : fl4_abi.label.CNodeDelete.val = 26 := by simp [fl4_abi.label.CNodeDelete]
  scalar_tac
theorem lblD4 : ¬ fl4_abi.label.CNodeDelete = fl4_abi.label.CNodeRevoke := by
  intro e
  have h1 : fl4_abi.label.CNodeRevoke.val = 25 := by simp [fl4_abi.label.CNodeRevoke]
  have h2 : fl4_abi.label.CNodeDelete.val = 26 := by simp [fl4_abi.label.CNodeDelete]
  have := congrArg UScalar.val e; omega

/-- A slot word is no `IoTW t` word (`SlotOK.tf`). -/
theorem SlotOK.notT {s0 : S} {t b : U64} (F : SchedOK (L := L) s0 t) (O : SlotOK (L := L) K s0 t) (hs : SlotW K b) :
    ¬ IoTW t b := by
  rintro (⟨r, hr, e⟩ | e)
  · obtain ⟨k, hk, ek⟩ := regA_eq F.tcb hr
    rw [ek] at e; subst e
    exact O.tf k (by omega) (by omega) hs
  · subst e
    exact O.tf _ (by rw [st_val]; omega) (by rw [st_val]; omega) hs

/-- Two states agreeing on a capability slot's words read its cap alike. -/
theorem cap_agree {x x' : S} {q : U64} (hL : Slot8 K) (hq : q ∈ K.slots)
    (h : ∀ b, SlotW K b → Aligned b → L.mem x' b = L.mem x b) : obj.Slot.cap st q x' = obj.Slot.cap st q x := by
  have e0 : core.num.U64.wrapping_add q 0#u64 = q := by
    apply UScalar.eq_of_val_eq; rw [slot_word_val (hL q hq).2 (by simp)]; simp
  have h0 := h _ (slotW_of hL hq (o := 0#u64) (by simp)) (slot_al hL hq (by simp) (by simp))
  rw [e0] at h0
  unfold obj.Slot.cap
  rw [L.read_pair_eq, L.read_pair_eq, h0, h _ (slotW_of hL hq (by simp)) (slot_al hL hq (by simp) (by simp))]

theorem next_agree {x x' : S} {q : U64} (hL : Slot8 K) (hq : q ∈ K.slots)
    (h : ∀ b, SlotW K b → Aligned b → L.mem x' b = L.mem x b) : obj.Slot.next st q x' = obj.Slot.next st q x := by
  unfold obj.Slot.next obj.Slot.next_word
  simp only [lift, bind_ok, L.read_eq]
  rw [h _ (slotW_of hL hq (by simp [layout.cte.NEXT])) (slot_al hL hq (by simp [layout.cte.NEXT])
    (by simp [layout.cte.NEXT]))]

/-- **The Delete decode writes `IoTW t` and slot words only** (from the decode state `x`, where `t` is current,
schedulable, the action `RESUME_CURRENT`), returning `Ok ()`: `set_thread_state RESTART`, then the frame's
deletion. -/
theorem cnDel_keep {x : S} {a : A} {t length buf cp cr cg cgb dest fp rt asid va : U64} {mp : Bool}
    {ex : Aeneas.Std.Array obj.Slot 3#usize}
    (F : SchedOK (L := L) x t) (O : SlotOK (L := L) K x t) (ha : L.actionW x = sched.ACTION_RESUME_CURRENT)
    (hr : L.mem x (stA t) = sched.TS_RESTART ∨ L.mem x (stA t) = sched.TS_RUNNING)
    (hL : Slot8 K) (hlen : ¬ length < 2#u64)
    (hlk : cspace.lookup_target_slot st x (.CNode cp cr cg cgb) (L.mem x (regA t layout.reg.R10))
      (L.mem x (regA t layout.reg.R8)) = ok (.Ok dest))
    (hd : dest ∈ K.slots) (hc : obj.Slot.cap st dest x = ok (.Frame fp .Small rt false mp false asid va))
    (hm : mp = false ∨ asid = 0#u64)
    (hp : L.mem x (core.num.U64.wrapping_add dest layout.cte.PREV) ≠ 0#u64 →
      L.mem x (core.num.U64.wrapping_add dest layout.cte.PREV) ∈ K.slots)
    (hn : ∀ nx, obj.Slot.next st dest x = ok nx → nx ≠ 0#u64 → nx ∈ K.slots)
    {y : core.result.Result Unit error.Exc × S × A}
    (h : cnode.decode st ar x a fl4_abi.label.CNodeDelete length (.CNode cp cr cg cgb) buf ex = ok y) :
    y.1 = .Ok () ∧ KeepS st K x t y.2.1 := by
  unfold cnode.decode at h
  rw [if_neg lblD1, if_neg lblD2, if_neg hlen, cur_thread_ok, F.cur] at h
  simp only [bind_ok] at h
  rw [sarg0_reg, sarg1_reg, reg_ok, reg_ok] at h
  simp only [bind_ok] at h
  rw [hlk] at h
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, lblD3, lblD4, ↓reduceIte] at h
  obtain ⟨s3, hs3, h⟩ := bind_eq_ok h
  have K3 : KeepA (L := L) x t s3 := (KeepA.refl ha hr).sts F (Or.inl rfl) hs3
  have ag : ∀ b, SlotW K b → Aligned b → L.mem s3 b = L.mem x b := fun b hs hb =>
    K3.mem hb (O.notT F hs)
  have hc3 : obj.Slot.cap st dest s3 = ok (.Frame fp .Small rt false mp false asid va) := by
    rw [cap_agree hL hd ag]; exact hc
  have ep : L.mem s3 (core.num.U64.wrapping_add dest layout.cte.PREV) =
      L.mem x (core.num.U64.wrapping_add dest layout.cte.PREV) :=
    ag _ (slotW_of hL hd (by simp [layout.cte.PREV])) (slot_al hL hd (by simp [layout.cte.PREV])
      (by simp [layout.cte.PREV]))
  obtain ⟨hy1, wd⟩ := del_frame_keep ar hL hd hc3 hm (by rw [ep]; exact hp)
    (fun nx e => hn nx (by rw [← next_agree hL hd ag]; exact e)) h
  exact ⟨hy1, (KeepS.of_keepA K3).slots F O wd⟩

/-- `decode_invocation` on a CNode cap (second phase) is the CNode decode. -/
theorem decode_cnode_eq {x : S} {a : A} {lbl length slot buf cp cr cg cgb : U64} {b1 b2 b3 : Bool}
    {ex : Aeneas.Std.Array obj.Slot 3#usize} :
    syscall.decode_invocation st ar x a lbl length slot (.CNode cp cr cg cgb) b1 b2 b3 false buf ex =
      cnode.decode st ar x a lbl length (.CNode cp cr cg cgb) buf ex := by
  unfold syscall.decode_invocation
  rw [cur_thread_ok]
  simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]

/-- **`invRep` of `Ok`** from a `KeepS` state where `t` is current: `reply_success_empty` and `set_thread_state
RUNNING` when `t` is `RESTART`; result `Ok ()`. -/
theorem invRep_ok_keep {s0 x : S} {t : U64} {a : A} {z : S × A × core.result.Result Unit error.Exc}
    (F : SchedOK (L := L) s0 t) (O : SlotOK (L := L) K s0 t) (hk : KeepS st K s0 t x)
    (h : invRep st t x a (.Ok ()) = ok z) : z.2.2 = .Ok () ∧ KeepS st K s0 t z.1 := by
  have Fx := hk.sched F O
  unfold invRep at h
  obtain ⟨i6, -, h⟩ := bind_eq_ok h
  obtain ⟨t1, et1, h⟩ := bind_eq_ok h
  cases ok_inj_ff h
  refine ⟨rfl, ?_⟩
  by_cases hi : i6 = sched.TS_RESTART
  · rw [if_pos hi] at et1
    obtain ⟨s5, es5, et1⟩ := bind_eq_ok et1
    have k5 : KeepA (L := L) x t s5 := by
      unfold msg.reply_success_empty at es5
      rw [set_reg_ok'] at es5; simp only [bind_ok] at es5
      obtain ⟨mi, -, es5⟩ := bind_eq_ok es5
      unfold msg.set_msg_info at es5
      obtain ⟨w, -, es5⟩ := bind_eq_ok es5
      rw [set_reg_ok'] at es5
      cases ok_inj_ff es5
      exact ((KeepA.refl hk.2.1 hk.2.2).wr_reg Fx rB384).wr_reg Fx rM384
    exact hk.keepA (k5.sts Fx (Or.inr rfl) et1)
  · rw [if_neg hi] at et1
    cases ok_inj_ff et1
    exact hk

/-- **The decode block's footprint**: from the decode state `x`, the Delete decode then `invRep` write `IoTW t`
and slot words only, and the reply is `Ok ()`. -/
theorem decDel_keep {x : S} {a : A} {t length buf cp cr cg cgb dest fp rt asid va slot : U64} {mp : Bool}
    {ex : Aeneas.Std.Array obj.Slot 3#usize}
    (F : SchedOK (L := L) x t) (O : SlotOK (L := L) K x t) (ha : L.actionW x = sched.ACTION_RESUME_CURRENT)
    (hr : L.mem x (stA t) = sched.TS_RESTART ∨ L.mem x (stA t) = sched.TS_RUNNING)
    (hL : Slot8 K) (hlen : ¬ length < 2#u64)
    (hlk : cspace.lookup_target_slot st x (.CNode cp cr cg cgb) (L.mem x (regA t layout.reg.R10))
      (L.mem x (regA t layout.reg.R8)) = ok (.Ok dest))
    (hd : dest ∈ K.slots) (hc : obj.Slot.cap st dest x = ok (.Frame fp .Small rt false mp false asid va))
    (hm : mp = false ∨ asid = 0#u64)
    (hp : L.mem x (core.num.U64.wrapping_add dest layout.cte.PREV) ≠ 0#u64 →
      L.mem x (core.num.U64.wrapping_add dest layout.cte.PREV) ∈ K.slots)
    (hn : ∀ nx, obj.Slot.next st dest x = ok nx → nx ≠ 0#u64 → nx ∈ K.slots)
    {y : core.result.Result Unit error.Exc × S × A} {z : S × A × core.result.Result Unit error.Exc}
    (hy : syscall.decode_invocation st ar x a fl4_abi.label.CNodeDelete length slot (.CNode cp cr cg cgb)
      true true true false buf ex = ok y)
    (hz : invRep st t y.2.1 y.2.2 y.1 = ok z) : z.2.2 = .Ok () ∧ KeepS st K x t z.1 := by
  rw [decode_cnode_eq] at hy
  obtain ⟨hy1, k1⟩ := cnDel_keep ar F O ha hr hL hlen hlk hd hc hm hp hn hy
  rw [hy1] at hz
  exact invRep_ok_keep F O k1 hz

end dec

/-! ## `FinOK` after the decode block -/

section fin
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S}

/-- A slot word's region is a slot. -/
theorem IoPre.slotW_region (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) {b : U64} (h : SlotW K b) :
    ∃ q, region K b = .slot q := by
  obtain ⟨q, hq, hb⟩ := h; exact ⟨q, P.lay.slotw q hq b hb⟩

theorem IoPre.node_notSlot (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) {o : U64} (ho : o.val < 4288) :
    ¬ SlotW K (L.nodeAt s (L.cpu s) o) := fun hs => by
  obtain ⟨q, hq⟩ := P.slotW_region hs
  rw [P.lay.node _ _ (P.inNode o ho)] at hq; cases hq

theorem IoPre.tcb_notSlot (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) {t k : U64} (ht : K.heap t = some .tcb)
    (h1 : 192 ≤ k.val) (h2 : k.val < 4096) : ¬ SlotW K (core.num.U64.wrapping_add t k) := fun hs => by
  obtain ⟨q, hq⟩ := P.slotW_region hs
  have := P.lay.tcbw t ht k h1 h2
  unfold fld at this
  rw [this] at hq; cases hq

theorem IoPre.sc_notSlot (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) {c : U64} {zb : Nat}
    (hc : K.heap c = some (.sc zb)) {b : U64} (hin : InSC c zb b) : ¬ SlotW K b := fun hs => by
  obtain ⟨q, hq⟩ := P.slotW_region hs
  rw [P.lay.scw c zb hc b ⟨hin.1, hin.2⟩] at hq; cases hq

set_option maxHeartbeats 4000000 in
/-- (stpost gen 13) **`FinOK` after the CNodeDelete-no-PTE decode block** (the I/O port's `io_hfin` route with the
Delete arm's slot writes): at an accepted run's post-prefix state `s2` (`InvChk`), a decode of the CNode cap at the
plan's slot at `CNodeDelete` with `length ≥ 2`, then `invRep`, reply `Ok ()` and leave `FinOK`. Inputs: `IoPre` and
`DelEnt` at the entry, the plan's slot a capability slot, the write set `W` covering the prefix words (`IoWr`) and
the caller's `STATE`. -/
theorem delFin {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {a : A}
    {nx : U64} {s1 s2 : S} {a1 : A} {length buf : U64} {cap : capability.Cap}
    {y : (core.result.Result Unit error.Exc) × S × A} {z : S × A × core.result.Result Unit error.Exc}
    {W : U64 → Prop} {gS : machine.Store S} [GRd gS st (IoRS (st := st) K Locks s)] [GWr gS st W]
    (P : IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hW : IoWr st W K.heap.scBits s) (hsw : W (stA (L.curW s)))
    (E : DelEnt st K Cs Locks p s) (hsl : p.slot ∈ K.slots) (hlen : ¬ length < 2#u64)
    (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (hcap : obj.Slot.cap st p.slot s2 = ok cap)
    (hy : syscall.decode_invocation st ar s2 a1 fl4_abi.label.CNodeDelete length p.slot cap true true true false
      buf p.extra = ok y)
    (hz : invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z) :
    z.2.2 = .Ok () ∧ FinOK (L := L) gS (IoRS (st := st) K Locks s) W ar s z.1 z.2.1 := by
  obtain ⟨cp, cr, cg, cgb, dest, fp, rt, asid, va, mp, Cw, hcs, hlk, hdc, hm, hC, hcl, hWk, hd, -, -, hpv, hnx⟩ := E
  obtain ⟨-, es1, eu, eac, ey, ehere, -⟩ := C
  have Ent := P.ent (Locks := Locks) hW
  have Hf := here_facts ehere
  have I := IoS2.of_ent hA Ent es1 eu Hf.sc
  have hct : L.curW s2 = L.curW s := I.cur
  have hL : Slot8 K := fun q hq => P.lay.slot8 q hq
  have w0 := prefix_writes ar hA P.tp P.np P.cT es1 eu
  have ag : ∀ b, SlotW K b → Aligned b → L.mem s2 b = L.mem s b := fun b hs hb => by
    obtain ⟨q, hq, hbq⟩ := hs
    exact P.slot_keep w0 hq hbq hb
  -- the invoked cap is the CNode cap
  have hcap' : cap = .CNode cp cr cg cgb := by
    rw [cap_agree hL hsl ag, hcs] at hcap; exact (ok_inj_ff hcap).symm
  subst hcap'
  -- the registers `R10`, `R8`
  have tk : ∀ k : U64, k.val < 4096 → k.val % 8 = 0 → k.val ≠ 392 →
      L.mem s2 (core.num.U64.wrapping_add (L.curW s) k) = L.mem s (core.num.U64.wrapping_add (L.curW s) k) :=
    fun k h1 h2 h3 => w0.2.2 _ (field_aligned P.tA h1 h2) (preW_tcb P.tA P.np P.cT h1 h3)
  have r10 : L.mem s2 (regA (L.curW s) layout.reg.R10) = L.mem s (regA (L.curW s) layout.reg.R10) := by
    have e := reg_keepK (st := st) P.tA (r := layout.reg.R10) (by simp [layout.reg.R10])
      (by simp [layout.reg.R10]) tk
    rw [reg_ok, reg_ok] at e; exact ok_inj_ff e
  have r8 : L.mem s2 (regA (L.curW s) layout.reg.R8) = L.mem s (regA (L.curW s) layout.reg.R8) := by
    have e := reg_keepK (st := st) P.tA (r := layout.reg.R8) (by simp [layout.reg.R8])
      (by simp [layout.reg.R8]) tk
    rw [reg_ok, reg_ok] at e; exact ok_inj_ff e
  -- the target lookup at `s2`
  have slotK : ∀ p r, Cw p r → ∀ m, cspace.mask r = ok m → ∀ x : U64,
      obj.Slot.cap st (cnSlot p (x &&& m)) s2 = obj.Slot.cap st (cnSlot p (x &&& m)) s :=
    fun p r hp m hm x => cap_agree hL (hWk p r m x hp hm).1 ag
  have hCn' : ∀ p1 r1 gs1 g1, capability.Cap.CNode cp cr cg cgb = .CNode p1 r1 gs1 g1 → Cw p1 r1 := by
    intro p1 r1 gs1 g1 e; cases e; exact hC
  have hlk2 : cspace.lookup_target_slot st s2 (.CNode cp cr cg cgb) (L.mem s2 (regA (L.curW s) layout.reg.R10))
      (L.mem s2 (regA (L.curW s) layout.reg.R8)) = ok (.Ok dest) := by
    rw [r10, r8]
    unfold cspace.lookup_target_slot cspace.lookup_slot_for_cnode_op at hlk ⊢
    simp only [bind_ok, ↓reduceIte] at hlk ⊢
    by_cases d1 : L.mem s (regA (L.curW s) layout.reg.R8) < 1#u64
    · rw [if_pos d1] at hlk; simp at hlk
    rw [if_neg d1] at hlk ⊢
    by_cases d2 : L.mem s (regA (L.curW s) layout.reg.R8) > cspace.WORD_BITS
    · rw [if_pos d2] at hlk; simp at hlk
    rw [if_neg d2] at hlk ⊢
    unfold cspace.resolve_address_bits at hlk ⊢
    obtain ⟨res, eres, hl⟩ := bind_eq_ok hlk
    have eres' := rab_loop_congr2 st Cw slotK hcl 66 _ _ 65#u64 res (by simp) hCn' eres
    rw [eres']; simp only [bind_ok]; exact hl
  -- the target's facts at `s2`
  have hdc2 : obj.Slot.cap st dest s2 = ok (.Frame fp .Small rt false mp false asid va) := by
    rw [cap_agree hL hd ag]; exact hdc
  have hpv2 : L.mem s2 (core.num.U64.wrapping_add dest layout.cte.PREV) ≠ 0#u64 →
      L.mem s2 (core.num.U64.wrapping_add dest layout.cte.PREV) ∈ K.slots := by
    rw [ag _ (slotW_of hL hd (by simp [layout.cte.PREV])) (slot_al hL hd (by simp [layout.cte.PREV])
      (by simp [layout.cte.PREV]))]
    exact fun h0 => (hpv h0).1
  have hnx2 : ∀ nx, obj.Slot.next st dest s2 = ok nx → nx ≠ 0#u64 → nx ∈ K.slots := fun nx e h0 =>
    (hnx nx (by rw [← next_agree hL hd ag]; exact e) h0).1
  -- the scheduler facts at `s2` (io_hfin)
  have ha2 : L.actionW s2 = sched.ACTION_RESUME_CURRENT := by
    rw [eq_of_spec_fd (sched.action.spec (L := L) s2)] at eac; exact ok_inj_ff eac
  have hy2 : L.mem s2 (yieldA (L.curW s)) = 0#u64 := by
    rw [eq_ok_of_spec (obj.Tcb.yield_to.spec (L := L) s2 (L.curW s))] at ey; exact ok_inj_ff ey
  have hrun : L.mem s2 (stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s2 (stA (L.curW s)) = sched.TS_RUNNING := by
    rw [I.st]; exact Ent.run
  have A0 := Ent.acc
  have hK0 := SchedOK.of_sw I.F (by rw [hct]; exact Hf.sc) (by rw [hct]; exact Hf.nr)
  rw [hct] at hK0
  have hK : SchedOK (L := L) s2 (L.curW s) := hK0
  -- the slot words miss the node, the TCB fields and the SC words
  have hn2 : ∀ o : U64, o.val < 4288 → ¬ SlotW K (L.nodeAt s2 (L.cpu s2) o) := fun o ho => by
    rw [I.cp, nodeAt_of_ksb I.k]; exact P.node_notSlot ho
  have hmx : ¬ SlotW K (maxA (L.mem s2 (scA (L.curW s)))) := by
    rw [← hct, I.F.i]
    exact P.sc_notSlot (P.hSc _ P.cscS) I.F.q.2.2.2.1
  have O : SlotOK (L := L) K s2 (L.curW s) :=
    ⟨hn2, fun k h1 h2 => P.tcb_notSlot (P.hT _ P.cT) h1 h2, hmx⟩
  -- the run
  obtain ⟨hz2, kz⟩ := decDel_keep ar hK O ha2 hrun hL hlen hlk2 hd hdc2 hm hpv2 hnx2 hy hz
  refine ⟨hz2, ?_⟩
  -- `Ω` cut to the SC words
  have hrh0 : L.mem s (rhA (L := L) s) ≠ 0#u64 → L.mem s (scA (L.mem s (rhA (L := L) s))) ∈ K.heap.scs ∧
      InSC (L.mem s (scA (L.mem s (rhA (L := L) s)))) (K.heap.scBits (L.mem s (scA (L.mem s (rhA (L := L) s)))))
        (headA (L.mem s (scA (L.mem s (rhA (L := L) s))))) := fun h0 => by
    obtain ⟨-, hc, -⟩ := bxi_rh P.bxi h0
    obtain ⟨⟨Q, Rq, hq⟩, hbd, ⟨hO, -, hX⟩, -, hS⟩ := P.bxi
    obtain ⟨hP, hz⟩ := hO.sc _ hc
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hh := headA_val' hP hz
    exact ⟨hc, by omega, by omega⟩
  have F0' := I.F0.shrink P.cscS rfl hrh0
  have F2' := F0'.frame I.w
  have rh0' : RhSc st {b | b ∈ Ω ∧ ∃ c' ∈ K.heap.scs, InSC c' (K.heap.scBits c') b} s := fun h0 => by
    obtain ⟨-, hc, ha⟩ := bxi_rh P.bxi h0
    obtain ⟨hW', hΩ⟩ := bxi_scin P.bxi hc ha
    exact ⟨_, hW', fun b hb hin => ⟨hΩ b hb hin, _, hc, hin⟩⟩
  have rh2' := rh0'.frame F0' I.w
  have Q0 := QOK.of_sw F2' rh2' I.tm
  rw [hct] at Q0
  have ho' : ∀ b ∈ {b | b ∈ Ω ∧ ∃ c' ∈ K.heap.scs, InSC c' (K.heap.scBits c') b}, ¬ SlotW K b := by
    rintro b ⟨-, c', hc', hin⟩
    exact P.sc_notSlot (P.hSc _ hc') hin
  have stm : L.mem s2 (tmA (L := L) s2) ≠ 0#u64 → ¬ SlotW K (tdA (L.mem s2 (tmA (L := L) s2))) := fun h0 => by
    unfold tdA
    exact P.tcb_notSlot (I.tm h0) (by simp) (by simp)
  have srh : L.mem s2 (rhA (L := L) s2) ≠ 0#u64 → ¬ SlotW K (scA (L.mem s2 (rhA (L := L) s2))) ∧
      ¬ SlotW K (headA (L.mem s2 (scA (L.mem s2 (rhA (L := L) s2))))) ∧
      ¬ SlotW K (rtA (L.mem s2 (scA (L.mem s2 (rhA (L := L) s2))))
        (L.rhead s2 (L.mem s2 (scA (L.mem s2 (rhA (L := L) s2)))))) := fun h0 => by
    refine ⟨?_, ?_⟩
    · unfold scA; exact P.tcb_notSlot (F2'.rh h0).1 (by simp) (by simp)
    obtain ⟨zr, hW', hΩ⟩ := rh2' h0
    obtain ⟨h8, hmm, hfit⟩ := hW'.bounds
    obtain ⟨h96, -, -, hhd, -, hrt⟩ := hW'.inside
    obtain ⟨e1, e2, e3⟩ := hrt _ hW'.head_lt
    exact ⟨ho' _ (hΩ _ (by unfold Aligned; omega) ⟨by omega, by omega⟩),
      ho' _ (hΩ _ (by unfold Aligned; omega) ⟨by omega, by omega⟩)⟩
  have FIN := kz.fin hK O Q0 Hf.nd I.F.td I.F.rs stm srh
  have hcur3 : L.curW z.1 = L.curW s := kz.cur hK O
  have w3 : WritesIn st s2 z.1 (fun b => IoPW st s2 b ∨ SlotW K b) :=
    kz.1.mono fun b hb => hb.imp_left fun h => Or.inr (by rw [hct]; exact h)
  have Fz := F2'.frameE w3 hn2 (fun t ht k h1 h2 => P.tcb_notSlot ht (by omega) h2) ho'
  refine FinOK.of_sw hA (kz.1.1.trans I.k) (kz.1.2.1.trans I.cp) FIN.1 kz.2.1 Fz ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    (by rw [hcur3]; exact SWr.of_W hsw)
  · rw [hcur3]
    exact (kz.tcbF hK O (k := 3472#u64) (by simp) (by simp) (by simp)).trans hy2
  · rw [hcur3]; exact kz.2.2
  · rw [hcur3]; exact A0.ryl
  · rw [hcur3]; exact A0.rst
  · rw [hcur3]; exact A0.rfi
  · rw [hcur3]; exact A0.wnx
  · rw [hcur3]; exact A0.rin

end fin

end Fl4Proofs.P2.PathObl
