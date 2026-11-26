/-
# P2 (line stpost, generation 14): the truncated CNodeDelete (`length < 2`) decode block

A Delete with fewer than two message words is accepted by `localinv.plan`; its decode returns `TruncatedMessage`
without touching the store, and `invRep` replies through `syscall.reply_error`, which (with
`KERNEL_INVOCATION_REPORT_ERROR_IPC = true` and the IPC buffer set) reads and writes the caller's buffer word
`DEBUG_MESSAGE_START + 1`, a **user word**. This module proves the block on any store reading `IoRS s` and the
aligned user words as `st` (`truncAcc`), and `FinOK` after it (`truncFin`), for writes `IoTW t ∪ {aligned user
words}`:

* `UserW K b` (an aligned user word), `KeepU` / `UsrOK` / `KeepU.fin` / `SwOK.frameU` (InvBlkFin's `KeepS` /
  `SlotOK` / `KeepS.fin` / `SwOK.frameE` with user words for slot words), `IoPre.node_notUser`,
  `IoPre.tcb_notUser`, `IoPre.sc_notUser` (user words have region `.none`);
* `cnode_decode_trunc` (no store access), `error_mrs_trunc`, `syscall.reply_error.guard_trunc`, `truncRun` (the st
  run: reply `Ok ()`, `KeepU` from the decode state);
* **`truncAcc`**, **`truncFin`**.

Named premise: [J] `InvBufJ` (the caller's IPC buffer words, when the buffer is set, are aligned user words).
No existing statement changes; no `kernel_entry_reach*` is touched.
-/
import Fl4Proofs.P2.InvBlkFin
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot
  slotOwner)

/-- An aligned user word. -/
def UserW (K : KLayout) (b : U64) : Prop := Aligned b ∧ b ∈ K.user

/-- [J] **The caller's IPC buffer words are aligned user words**: at `s`, when the current thread's receive-side
buffer lookup gives a non-zero `b`, each word `b + 8 i` (`i < 512`) is aligned and a user word. -/
def InvBufJ {S : Type} (st : machine.Store S) [L : LawfulStore st] (K : KLayout) (s : S) : Prop :=
  ∀ b, msg.lookup_ipc_buffer st s true (L.curW s) = ok b → b ≠ 0#u64 → ∀ i : U64, i.val < 512 →
    UserW K (core.num.U64.wrapping_add b (core.num.U64.wrapping_mul i 8#u64))

section keepU
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {s0 x y : S} {t : U64}

variable (st) in
/-- From `s0`: only `IoTW t` and capability-slot words written, the action `RESUME_CURRENT`, `t` runnable. -/
def KeepU (K : KLayout) (s0 : S) (t : U64) (x : S) : Prop :=
  WritesIn st s0 x (fun b => IoTW t b ∨ UserW K b) ∧ L.actionW x = sched.ACTION_RESUME_CURRENT ∧
    (L.mem x (stA t) = sched.TS_RESTART ∨ L.mem x (stA t) = sched.TS_RUNNING)

/-- The words `KeepU`'s slot writes must miss, at `s0`. -/
structure UsrOK (K : KLayout) (s0 : S) (t : U64) : Prop where
  nd : ∀ o : U64, o.val < 4288 → ¬ UserW K (L.nodeAt s0 (L.cpu s0) o)
  tf : ∀ k : U64, 192 ≤ k.val → k.val < 4096 → ¬ UserW K (core.num.U64.wrapping_add t k)
  mx : ¬ UserW K (maxA (L.mem s0 (scA t)))

theorem KeepU.of_keepA (h : KeepA (L := L) s0 t x) : KeepU st K s0 t x :=
  ⟨h.1.mono fun _ hb => Or.inl hb, h.2⟩

theorem KeepU.node (h : KeepU st K s0 t x) (o : U64) : L.nodeAt x (L.cpu x) o = L.nodeAt s0 (L.cpu s0) o := by
  rw [h.1.2.1, nodeAt_of_ksb h.1.1]

theorem KeepU.mem (h : KeepU st K s0 t x) {b : U64} (hb : Aligned b) (hn : ¬ IoTW t b) (hs : ¬ UserW K b) :
    L.mem x b = L.mem s0 b := h.1.2.2 b hb (fun h' => h'.elim hn hs)

theorem KeepU.nd (F : SchedOK (L := L) s0 t) (O : UsrOK (L := L) K s0 t) (h : KeepU st K s0 t x) (o : U64)
    (ho : o.val < 4288) (h8 : o.val % 8 = 0) :
    L.mem x (L.nodeAt x (L.cpu x) o) = L.mem s0 (L.nodeAt s0 (L.cpu s0) o) := by
  rw [h.node]; exact h.mem (F.nd o ho h8).1 (F.nd o ho h8).2 (O.nd o ho)

theorem KeepU.cur (F : SchedOK (L := L) s0 t) (O : UsrOK (L := L) K s0 t) (h : KeepU st K s0 t x) :
    L.curW x = t := by
  unfold LawfulStore.curW
  rw [h.nd F O _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])]; exact F.cur

/-- A TCB field of `t` from offset 3328 on (not `STATE`) is kept by `KeepU`. -/
theorem KeepU.tcbF (F : SchedOK (L := L) s0 t) (O : UsrOK (L := L) K s0 t) (h : KeepU st K s0 t x) {k : U64}
    (h1 : 3328 < k.val) (h2 : k.val < 4096) (h8 : k.val % 8 = 0) :
    L.mem x (core.num.U64.wrapping_add t k) = L.mem s0 (core.num.U64.wrapping_add t k) :=
  h.mem (field_aligned F.tcb h2 h8) (iotw_field F.tcb h2 h1) (O.tf k (by omega) h2)

/-- **`SchedOK` carried to a `KeepU` state.** -/
theorem KeepU.sched (F : SchedOK (L := L) s0 t) (O : UsrOK (L := L) K s0 t) (h : KeepU st K s0 t x) :
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

/-- `KeepU` then a `KeepA` step. -/
theorem KeepU.keepA (h : KeepU st K s0 t x) (h' : KeepA (L := L) x t y) : KeepU st K s0 t y :=
  ⟨(h.1.trans h'.1).mono fun _ hb => by rcases hb with hb | hb; exact hb; exact Or.inl hb, h'.2⟩

/-- `KeepU` then writes of slot words only. -/
theorem KeepU.users (F : SchedOK (L := L) s0 t) (O : UsrOK (L := L) K s0 t) (h : KeepU st K s0 t x)
    (w : WritesIn st x y (UserW K)) : KeepU st K s0 t y := by
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
theorem KeepU.fin (F : SchedOK (L := L) s0 t) (O : UsrOK (L := L) K s0 t) (Q : QOK (L := L) s0 t)
    (h : KeepU st K s0 t x)
    {R : U64 → Prop} (hnd : NoDue (L := L) s0)
    (htd : L.mem s0 (tmA (L := L) s0) ≠ 0#u64 →
      R (core.num.U64.wrapping_add (L.mem s0 (tmA (L := L) s0)) 3528#u64))
    (hrs : L.mem s0 (rhA (L := L) s0) ≠ 0#u64 → R (scA (L.mem s0 (rhA (L := L) s0))) ∧
      RdHead (L := L) R s0 (L.mem s0 (scA (L.mem s0 (rhA (L := L) s0)))))
    (stm : L.mem s0 (tmA (L := L) s0) ≠ 0#u64 → ¬ UserW K (tdA (L.mem s0 (tmA (L := L) s0))))
    (srh : L.mem s0 (rhA (L := L) s0) ≠ 0#u64 → ¬ UserW K (scA (L.mem s0 (rhA (L := L) s0))) ∧
      ¬ UserW K (headA (L.mem s0 (scA (L.mem s0 (rhA (L := L) s0))))) ∧
      ¬ UserW K (rtA (L.mem s0 (scA (L.mem s0 (rhA (L := L) s0))))
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

end keepU

/-! ## `SwOK` across slot writes -/

section frameU
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} [L : LawfulStore st]
variable {K : KLayout} {T Cs Ω : Set U64} {x y : S} {c : U64} {zc : Nat}

section
variable (F : SwOK st T Cs Ω R W x c zc) (w : WritesIn st x y (fun b => IoPW st x b ∨ UserW K b))
  (hn : ∀ o : U64, o.val < 4288 → ¬ UserW K (L.nodeAt x (L.cpu x) o))
  (ht : ∀ t ∈ T, ∀ k : U64, 3328 < k.val → k.val < 4096 → ¬ UserW K (core.num.U64.wrapping_add t k))
  (ho : ∀ b ∈ Ω, ¬ UserW K b)
include F w hn

theorem SwOK.nodeU (o : U64) (ho' : o.val < 4288) (h8 : o.val % 8 = 0)
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
theorem SwOK.tcbU {t k : U64} (htT : t ∈ T) (hk : k.val < 4096) (h8 : k.val % 8 = 0) (hge : 3328 < k.val) :
    L.mem y (core.num.U64.wrapping_add t k) = L.mem x (core.num.U64.wrapping_add t k) := by
  refine w.2.2 _ (field_aligned (F.tp t htT) hk h8) ?_
  rintro ((⟨o, ho', e⟩ | hi) | hs)
  · exact node_ne_field F.np (by omega) htT (F.tp t htT) hk e.symm
  · exact iotw_tcb (F.tp _ F.cT) (F.tp t htT) hk hge hi
  · exact ht t htT k hge hk hs

omit hn in
include ho in
theorem SwOK.omU {b : U64} (hb : b ∈ Ω) : L.mem y b = L.mem x b := by
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
theorem SwOK.frameU : SwOK st T Cs Ω R W y c zc := by
  have hcur : L.curW y = L.curW x := F.nodeU w hn _ (by simp [layout.node.CUR_THREAD])
    (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
  have hcsc : L.mem y (L.nodeA y layout.node.CUR_SC) = L.mem x (L.nodeA x layout.node.CUR_SC) :=
    F.nodeU w hn _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have htm : L.mem y (tmA (L := L) y) = L.mem x (tmA (L := L) x) :=
    F.nodeU w hn _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN])
  have hrh : L.mem y (rhA (L := L) y) = L.mem x (rhA (L := L) x) :=
    F.nodeU w hn _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD])
  have hcs : ∀ t ∈ T, L.mem y (scA t) = L.mem x (scA t) := fun t htT =>
    F.tcbU w ht htT (k := 3464#u64) (by simp) (by simp) (by simp)
  have hmx : L.rmax y c = L.rmax x c := F.omU w ho (F.q.2.1 _ F.q.2.2.2.2 F.q.2.2.2.1)
  have wfE : RefillsWF st x c zc → RefillsWF st y c zc := fun h =>
    h.agree fun b hb hin => F.omU w ho (F.q.2.1 b hb hin)
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
          L.rhead x (L.mem x (scA (L.mem x (rhA (L := L) x)))) := F.omU w ho ho'
      have := (F.rs h0).2
      unfold RdHead at this ⊢
      rw [hb]; exact this
  · rw [hrh]
    intro h0
    rw [hcs _ (F.rh h0).1]; exact F.rh h0

end

end frameU

/-! ## User words miss the node, the TCB fields and the SC words -/

section regions
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S}

theorem IoPre.user_none (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) {b : U64} (h : UserW K b) :
    region K b = .none := (P.lay.user b h.2).1

theorem IoPre.node_notUser (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) {o : U64} (ho : o.val < 4288) :
    ¬ UserW K (L.nodeAt s (L.cpu s) o) := fun hs => by
  have hq := P.user_none hs
  rw [P.lay.node _ _ (P.inNode o ho)] at hq; cases hq

theorem IoPre.tcb_notUser (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) {t k : U64} (ht : K.heap t = some .tcb)
    (h1 : 192 ≤ k.val) (h2 : k.val < 4096) : ¬ UserW K (core.num.U64.wrapping_add t k) := fun hs => by
  have hq := P.user_none hs
  have := P.lay.tcbw t ht k h1 h2
  unfold fld at this
  rw [this] at hq; cases hq

theorem IoPre.sc_notUser (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) {c : U64} {zb : Nat}
    (hc : K.heap c = some (.sc zb)) {b : U64} (hin : InSC c zb b) : ¬ UserW K b := fun hs => by
  have hq := P.user_none hs
  rw [P.lay.scw c zb hc b ⟨hin.1, hin.2⟩] at hq; cases hq

end regions

/-! ## The run -/

section run
variable {S : Type} {A : Type} (ar : machine.Arch A)

/-- The CNode decode at `CNodeDelete` with fewer than two words: `TruncatedMessage`, no access (any store). -/
theorem cnode_decode_trunc (m : machine.Store S) {x : S} {a : A} {length buf : U64} {cap : capability.Cap}
    {ex : Aeneas.Std.Array obj.Slot 3#usize} (hlen : length < 2#u64) :
    cnode.decode m ar x a fl4_abi.label.CNodeDelete length cap buf ex =
      ok (.Err (.Sys .TruncatedMessage), x, a) := by
  unfold cnode.decode
  rw [if_neg lblD1, if_neg lblD2, if_pos hlen]
  simp only [error.truncated, bind_ok]

theorem error_mrs_trunc (m : machine.Store S) (x : S) (t buf : U64) :
    syscall.error_mrs m x t buf .TruncatedMessage = ok (0#u64, x) := by
  unfold syscall.error_mrs; rfl

theorem dbg_idx : ∃ i : U64, syscall.DEBUG_MESSAGE_START + 1#u64 = ok i ∧ i.val < 512 := by
  have h6 : syscall.DEBUG_MESSAGE_START.val = 6 := by simp [syscall.DEBUG_MESSAGE_START]
  have h1 : (1#u64 : U64).val = 1 := by simp
  obtain ⟨v, hv, hvv⟩ := spec_ex_fd (U64.add_spec (x := syscall.DEBUG_MESSAGE_START) (y := 1#u64)
    (by rw [h6, h1]; simp [U64.max, U64.numBits]))
  refine ⟨v, hv, ?_⟩
  omega

end run

section g
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
  [L : LawfulStore st]

/-- **`reply_error TruncatedMessage` on the guarded store**, run-relative: the buffer lookup (as `st`), the reply
registers, and the buffer word `DEBUG_MESSAGE_START + 1` when the buffer is set. -/
theorem syscall.reply_error.guard_trunc {x : S} {t : U64} {z : S}
    (hlk : msg.lookup_ipc_buffer gS x true t = msg.lookup_ipc_buffer st x true t)
    (hB : W (regA t layout.reg.BADGE)) (hM : W (regA t layout.reg.MSG_INFO))
    (hbuf : ∀ b, msg.lookup_ipc_buffer st x true t = ok b → b ≠ 0#u64 → ∀ i : U64, i.val < 512 →
      R (core.num.U64.wrapping_add b (core.num.U64.wrapping_mul i 8#u64)) ∧
      W (core.num.U64.wrapping_add b (core.num.U64.wrapping_mul i 8#u64)))
    (h : syscall.reply_error st x t .TruncatedMessage = ok z) :
    syscall.reply_error gS x t .TruncatedMessage = ok z := by
  unfold syscall.reply_error at h ⊢
  rw [hlk]
  revert h
  refine tr_bind_same (fun b eb => ?_)
  rw [obj.Tcb.set_reg.guard (gS := gS) t x _ _ hB]
  refine tr_bind_same (fun s1 _ => ?_)
  rw [error_mrs_trunc, error_mrs_trunc]
  simp only [bind_ok, uncurry_apply_pair, fl4_abi.config.KERNEL_INVOCATION_REPORT_ERROR_IPC, if_true]
  refine tr_bind (fun q eq _ => ?_) (fun q _ => ?_)
  · by_cases hb0 : (b != 0#u64) = true
    · rw [if_pos hb0] at eq ⊢
      have hne : b ≠ 0#u64 := by simpa using hb0
      obtain ⟨i, hi, hiv⟩ := dbg_idx
      revert eq
      rw [hi]
      simp only [bind_ok]
      rw [msg.buf_get.guard (gS := gS) s1 b i (hbuf b eb hne i hiv).1]
      refine tr_bind_same (fun w _ => ?_)
      simp only [lift, bind_ok]
      rw [msg.buf_set.guard (gS := gS) s1 b i _ (hbuf b eb hne i hiv).2]
      exact id
    · rw [if_neg hb0] at eq ⊢; exact eq
  · obtain ⟨s3, len1⟩ := q
    simp only [uncurry_apply_pair]
    refine tr_bind_same (fun i _ => ?_)
    refine tr_bind_same (fun mi _ => ?_)
    rw [msg.set_msg_info.guard (gS := gS) s3 t _ hM]
    exact id

end g

section trun
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} (ar : machine.Arch A)
variable {K : KLayout}

/-- **The st run of the truncated block**: from the decode state `x`, the reply is `Ok ()` and the state after it is
`KeepU` (the reply registers, and the buffer word, an aligned user word by `hbuf`). -/
theorem truncRun {x : S} {a : A} {t length buf slot cp cr cg cgb : U64} {ex : Aeneas.Std.Array obj.Slot 3#usize}
    (F : SchedOK (L := L) x t) (O : UsrOK (L := L) K x t) (ha : L.actionW x = sched.ACTION_RESUME_CURRENT)
    (hr : L.mem x (stA t) = sched.TS_RESTART ∨ L.mem x (stA t) = sched.TS_RUNNING) (hlen : length < 2#u64)
    (hbuf : ∀ b, msg.lookup_ipc_buffer st x true t = ok b → b ≠ 0#u64 → ∀ i : U64, i.val < 512 →
      UserW K (core.num.U64.wrapping_add b (core.num.U64.wrapping_mul i 8#u64)))
    {y : core.result.Result Unit error.Exc × S × A} {z : S × A × core.result.Result Unit error.Exc}
    (hy : syscall.decode_invocation st ar x a fl4_abi.label.CNodeDelete length slot (.CNode cp cr cg cgb)
      true true true false buf ex = ok y)
    (hz : invRep st t y.2.1 y.2.2 y.1 = ok z) : z.2.2 = .Ok () ∧ KeepU st K x t z.1 := by
  rw [decode_cnode_eq ar, cnode_decode_trunc ar st hlen] at hy
  cases ok_inj_ff hy
  unfold invRep at hz
  obtain ⟨q0, eq0, hz⟩ := bind_eq_ok hz
  cases ok_inj_ff hz
  obtain ⟨s5, es5, e5⟩ := bind_eq_ok eq0
  cases ok_inj_ff e5
  refine ⟨rfl, ?_⟩
  simp only
  unfold syscall.reply_error at es5
  obtain ⟨b, eb, es5⟩ := bind_eq_ok es5
  rw [set_reg_ok'] at es5
  simp only [bind_ok, error_mrs_trunc, uncurry_apply_pair, fl4_abi.config.KERNEL_INVOCATION_REPORT_ERROR_IPC,
    if_true] at es5
  have k1 : KeepA (L := L) x t (L.wr x (regA t layout.reg.BADGE) 0#u64) := (KeepA.refl ha hr).wr_reg F rB384
  have u1 : KeepU st K x t (L.wr x (regA t layout.reg.BADGE) 0#u64) := KeepU.of_keepA k1
  obtain ⟨q, eq, es5⟩ := bind_eq_ok es5
  have uq : KeepU st K x t q.1 := by
    by_cases hb0 : (b != 0#u64) = true
    · rw [if_pos hb0] at eq
      have hne : b ≠ 0#u64 := by simpa using hb0
      obtain ⟨i, hi, hiv⟩ := dbg_idx
      rw [hi] at eq
      simp only [bind_ok] at eq
      obtain ⟨w, -, eq⟩ := bind_eq_ok eq
      simp only [lift, bind_ok] at eq
      obtain ⟨s4, es4, eq⟩ := bind_eq_ok eq
      cases ok_inj_ff eq
      unfold msg.buf_set at es4
      simp only [lift, bind_ok, L.write_eq] at es4
      cases ok_inj_ff es4
      have hu := hbuf b eb hne i hiv
      exact u1.users F O ((writesIn_wr hu.1).mono fun _ e => by subst e; exact hu)
    · rw [if_neg hb0] at eq
      cases ok_inj_ff eq
      exact u1
  obtain ⟨s3, len1⟩ := q
  simp only [uncurry_apply_pair] at es5 uq
  obtain ⟨i, -, es5⟩ := bind_eq_ok es5
  obtain ⟨mi, -, es5⟩ := bind_eq_ok es5
  unfold msg.set_msg_info at es5
  obtain ⟨wv, -, es5⟩ := bind_eq_ok es5
  rw [set_reg_ok'] at es5
  cases ok_inj_ff es5
  exact uq.keepA ((KeepA.refl uq.2.1 uq.2.2).wr_reg (uq.sched F O) rM384)

end trun

/-! ## The block on the guarded store, and `FinOK` -/

section blk
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S}

/-- (stpost gen 14) **The truncated Delete block on a store reading `IoRS s` and the aligned user words as `st`**
(run-relative): the decode (no access beyond the current-thread read) and the error reply (`reply_error`: the
buffer lookup, `BADGE`, the buffer word, `MSG_INFO`). [J] `hbuf : InvBufJ`. -/
theorem truncAcc {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {a : A}
    {nx : U64} {s1 s2 : S} {a1 : A} {length buf : U64} {cap : capability.Cap} {cp cr cg cgb : U64}
    {y : (core.result.Result Unit error.Exc) × S × A}
    {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
    (P : IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hR : ∀ b, IoRS (st := st) K Locks s b → R b) (hRu : ∀ b, UserW K b → R b)
    (hW : IoWr st W K.heap.scBits s) (hWu : ∀ b, UserW K b → W b)
    (hcs : obj.Slot.cap st p.slot s = ok (.CNode cp cr cg cgb)) (hsl : p.slot ∈ K.slots) (hbuf : InvBufJ st K s)
    (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (hcap : obj.Slot.cap st p.slot s2 = ok cap) (hlen : length < 2#u64)
    (hy : syscall.decode_invocation st ar s2 a1 fl4_abi.label.CNodeDelete length p.slot cap true true true false
      buf p.extra = ok y) :
    syscall.decode_invocation gS ar s2 a1 fl4_abi.label.CNodeDelete length p.slot cap true true true false
      buf p.extra = ok y ∧
    ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z → invRep gS (L.curW s) y.2.1 y.2.2 y.1 = ok z := by
  obtain ⟨-, es1, eu, eac, ey, ehere, -⟩ := C
  have Ent := P.ent (Locks := Locks) (P.ioWr (Locks := Locks))
  have Hf := here_facts ehere
  have I := IoS2.of_ent hA Ent es1 eu Hf.sc
  have hct : L.curW s2 = L.curW s := I.cur
  have hL : Slot8 K := fun q hq => P.lay.slot8 q hq
  have w0 := prefix_writes ar hA P.tp P.np P.cT es1 eu
  have ag : ∀ b, SlotW K b → Aligned b → L.mem s2 b = L.mem s b := fun b hs hb => by
    obtain ⟨q, hq, hbq⟩ := hs
    exact P.slot_keep w0 hq hbq hb
  have hcap' : cap = .CNode cp cr cg cgb := by
    rw [cap_agree hL hsl ag, hcs] at hcap; exact (ok_inj_ff hcap).symm
  subst hcap'
  have tk : ∀ k : U64, k.val < 4096 → k.val % 8 = 0 → k.val ≠ 392 →
      L.mem s2 (core.num.U64.wrapping_add (L.curW s) k) = L.mem s (core.num.U64.wrapping_add (L.curW s) k) :=
    fun k h1 h2 h3 => w0.2.2 _ (field_aligned P.tA h1 h2) (preW_tcb P.tA P.np P.cT h1 h3)
  have hlb : msg.lookup_ipc_buffer st s2 true (L.curW s) = msg.lookup_ipc_buffer st s true (L.curW s) :=
    lookup_buf_keep P.tA true tk
  have hbuf2 : ∀ b, msg.lookup_ipc_buffer st s2 true (L.curW s) = ok b → b ≠ 0#u64 → ∀ i : U64, i.val < 512 →
      UserW K (core.num.U64.wrapping_add b (core.num.U64.wrapping_mul i 8#u64)) := fun b eb hne i hi =>
    hbuf b (by rw [← hlb]; exact eb) hne i hi
  have hctR : R (L.nodeAt s2 (L.cpu s2) layout.node.CUR_THREAD) := by
    rw [I.cp, nodeAt_of_ksb I.k]
    exact hR _ (P.nd layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1
  rw [decode_cnode_eq ar, cnode_decode_trunc ar st hlen] at hy
  cases ok_inj_ff hy
  refine ⟨?_, fun z hz => ?_⟩
  · unfold syscall.decode_invocation
    rw [sched.cur_thread.guard (gS := gS) s2 hctR, cur_thread_ok]
    simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
    exact cnode_decode_trunc ar gS hlen
  · obtain ⟨bsl, hbsl⟩ := buffer_slot_ok (L.curW s)
    obtain ⟨hb1, hb2⟩ := P.lay.tslot _ (P.hT _ P.cT) _ bsl hbsl (by simp [layout.tcb.SLOT_BUFFER])
    have hbs := P.slot (Locks := Locks) hb1 (Or.inl hb2)
    have hI : R (core.num.U64.wrapping_add (L.curW s) 3512#u64) :=
      hR _ (P.gate (off := 3512#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField]))
    have hlk := msg.lookup_ipc_buffer.guard (gS := gS) s2 true (L.curW s) hbsl hI (hR _ hbs.1) (hR _ hbs.2)
    unfold invRep at hz ⊢
    revert hz
    refine tr_bind (fun q e _ => ?_) (fun _ _ h => h)
    revert e
    exact tr_bind (fun s5 e _ => syscall.reply_error.guard_trunc (gS := gS) hlk (hW.reg _ rB384) (hW.reg _ rM384)
      (fun b eb hne i hi => ⟨hRu _ (hbuf2 b eb hne i hi), hWu _ (hbuf2 b eb hne i hi)⟩) e) (fun _ _ h => h)

set_option maxHeartbeats 4000000 in
/-- (stpost gen 14) **`FinOK` after the truncated Delete block** (delFin's route, with the buffer word an aligned
user word written instead of slot words): reply `Ok ()`. [J] `hbuf : InvBufJ`. -/
theorem truncFin {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {a : A}
    {nx : U64} {s1 s2 : S} {a1 : A} {length buf : U64} {cap : capability.Cap} {cp cr cg cgb : U64}
    {y : (core.result.Result Unit error.Exc) × S × A} {z : S × A × core.result.Result Unit error.Exc}
    {W : U64 → Prop} {gS : machine.Store S} [GRd gS st (IoRS (st := st) K Locks s)] [GWr gS st W]
    (P : IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hW : IoWr st W K.heap.scBits s) (hsw : SWr gS st (L.curW s) sched.TS_RUNNING)
    (hcs : obj.Slot.cap st p.slot s = ok (.CNode cp cr cg cgb)) (hsl : p.slot ∈ K.slots) (hbuf : InvBufJ st K s)
    (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (hcap : obj.Slot.cap st p.slot s2 = ok cap) (hlen : length < 2#u64)
    (hy : syscall.decode_invocation st ar s2 a1 fl4_abi.label.CNodeDelete length p.slot cap true true true false
      buf p.extra = ok y)
    (hz : invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z) :
    z.2.2 = .Ok () ∧ FinOK (L := L) gS (IoRS (st := st) K Locks s) W ar s z.1 z.2.1 := by
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
  have hcap' : cap = .CNode cp cr cg cgb := by
    rw [cap_agree hL hsl ag, hcs] at hcap; exact (ok_inj_ff hcap).symm
  subst hcap'
  have tk : ∀ k : U64, k.val < 4096 → k.val % 8 = 0 → k.val ≠ 392 →
      L.mem s2 (core.num.U64.wrapping_add (L.curW s) k) = L.mem s (core.num.U64.wrapping_add (L.curW s) k) :=
    fun k h1 h2 h3 => w0.2.2 _ (field_aligned P.tA h1 h2) (preW_tcb P.tA P.np P.cT h1 h3)
  have hlb : msg.lookup_ipc_buffer st s2 true (L.curW s) = msg.lookup_ipc_buffer st s true (L.curW s) :=
    lookup_buf_keep P.tA true tk
  have hbuf2 : ∀ b, msg.lookup_ipc_buffer st s2 true (L.curW s) = ok b → b ≠ 0#u64 → ∀ i : U64, i.val < 512 →
      UserW K (core.num.U64.wrapping_add b (core.num.U64.wrapping_mul i 8#u64)) := fun b eb hne i hi =>
    hbuf b (by rw [← hlb]; exact eb) hne i hi
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
  have hn2 : ∀ o : U64, o.val < 4288 → ¬ UserW K (L.nodeAt s2 (L.cpu s2) o) := fun o ho => by
    rw [I.cp, nodeAt_of_ksb I.k]; exact P.node_notUser ho
  have hmx : ¬ UserW K (maxA (L.mem s2 (scA (L.curW s)))) := by
    rw [← hct, I.F.i]
    exact P.sc_notUser (P.hSc _ P.cscS) I.F.q.2.2.2.1
  have O : UsrOK (L := L) K s2 (L.curW s) :=
    ⟨hn2, fun k h1 h2 => P.tcb_notUser (P.hT _ P.cT) h1 h2, hmx⟩
  obtain ⟨hz2, kz⟩ := truncRun ar hK O ha2 hrun hlen hbuf2 hy hz
  refine ⟨hz2, ?_⟩
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
  have ho' : ∀ b ∈ {b | b ∈ Ω ∧ ∃ c' ∈ K.heap.scs, InSC c' (K.heap.scBits c') b}, ¬ UserW K b := by
    rintro b ⟨-, c', hc', hin⟩
    exact P.sc_notUser (P.hSc _ hc') hin
  have stm : L.mem s2 (tmA (L := L) s2) ≠ 0#u64 → ¬ UserW K (tdA (L.mem s2 (tmA (L := L) s2))) := fun h0 => by
    unfold tdA
    exact P.tcb_notUser (I.tm h0) (by simp) (by simp)
  have srh : L.mem s2 (rhA (L := L) s2) ≠ 0#u64 → ¬ UserW K (scA (L.mem s2 (rhA (L := L) s2))) ∧
      ¬ UserW K (headA (L.mem s2 (scA (L.mem s2 (rhA (L := L) s2))))) ∧
      ¬ UserW K (rtA (L.mem s2 (scA (L.mem s2 (rhA (L := L) s2))))
        (L.rhead s2 (L.mem s2 (scA (L.mem s2 (rhA (L := L) s2)))))) := fun h0 => by
    refine ⟨?_, ?_⟩
    · unfold scA; exact P.tcb_notUser (F2'.rh h0).1 (by simp) (by simp)
    obtain ⟨zr, hW', hΩ⟩ := rh2' h0
    obtain ⟨h8, hmm, hfit⟩ := hW'.bounds
    obtain ⟨h96, -, -, hhd, -, hrt⟩ := hW'.inside
    obtain ⟨e1, e2, e3⟩ := hrt _ hW'.head_lt
    exact ⟨ho' _ (hΩ _ (by unfold Aligned; omega) ⟨by omega, by omega⟩),
      ho' _ (hΩ _ (by unfold Aligned; omega) ⟨by omega, by omega⟩)⟩
  have FIN := kz.fin hK O Q0 Hf.nd I.F.td I.F.rs stm srh
  have hcur3 : L.curW z.1 = L.curW s := kz.cur hK O
  have w3 : WritesIn st s2 z.1 (fun b => IoPW st s2 b ∨ UserW K b) :=
    kz.1.mono fun b hb => hb.imp_left fun h => Or.inr (by rw [hct]; exact h)
  have Fz := F2'.frameU w3 hn2 (fun t ht k h1 h2 => P.tcb_notUser ht (by omega) h2) ho'
  refine FinOK.of_sw hA (kz.1.1.trans I.k) (kz.1.2.1.trans I.cp) FIN.1 kz.2.1 Fz ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    (by rw [hcur3]; exact hsw)
  · rw [hcur3]
    exact (kz.tcbF hK O (k := 3472#u64) (by simp) (by simp) (by simp)).trans hy2
  · rw [hcur3]; exact kz.2.2
  · rw [hcur3]; exact A0.ryl
  · rw [hcur3]; exact A0.rst
  · rw [hcur3]; exact A0.rfi
  · rw [hcur3]; exact A0.wnx
  · rw [hcur3]; exact A0.rin


end blk

end Fl4Proofs.P2.PathObl
