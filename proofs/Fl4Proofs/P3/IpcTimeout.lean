/-
P3 (DESIGN.md §9), IPC: **the timeout branch of `do_reply_transfer`**
(`ReplyHyps.tmo`): FL4's `valid_timeout_handler`, then `handle_timeout` or
`postpone`, against l4v's `is_ep_cap` test of `tcb_timeout_handler`, then
`handle_timeout` or `postpone` (`reply_tmo_top`; `ReplyHyps.ofT`).

* `valid_timeout_handler_rel`: on the CSpace relation alone, FL4's test of
  the timeout-handler slot is l4v's `is_valid_timeout_handler`.
* `set_fault_timeout_top`: `set_fault` of a timeout (the four fault words,
  `fault_set_ipc`, `fault_word_sre`, `fault_word_top`) is l4v's `thread_set`
  of the fault, on `IRel`.
* `send_ipc_faultI`: `send_ipc` of a faulted sender (no call, no donation)
  on `IRel`, by the endpoint's state (EpSendF.lean for a waiting receiver).
* `handle_timeout_top`: `set_fault`, then `send_ipc_faultI`, against l4v
  `handle_timeout` (`handleTimeout_mem`).
* Named (`ReplyTmoHyps`): `postpone` on `IRel` for a thread in no release
  queue (the caller's, l4v `not_in_release_q`; `RelOK`), the timeout fault's transfer from a thread
  with an SC (`tmoXfer`: the message carries the consumed time,
  `update_consumed`), and the timeout handler's endpoint in the ghost set
  (`epE`, l4v `valid_objs`).
-/
import Fl4Proofs.P3.IpcFaultReply
import Fl4Proofs.P3.EpSendF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Ipc

noncomputable section

section Spec
open Fl4Spec

theorem tcbCnodeMap_four (x : Tcb) : tcbCnodeMap x (tcbCnodeIndex 4) = some x.tcbTimeoutHandler := by
  unfold tcbCnodeMap
  rw [Function.update_of_ne (by decide), Function.update_self]

theorem getCap_tcb_four {Z : Type} [StateExt Z] {σ : State Z} {t : ObjRef} {x : Tcb}
    (hk : σ.kheap t = some (.tcb x)) :
    getCap (Z := Z) (t, tcbCnodeIndex 4) σ = ({(x.tcbTimeoutHandler, σ)}, False) := by
  unfold getCap
  dsimp only
  rw [nd_bind_one (getObject_eq hk)]
  dsimp only
  rw [nd_pure_bind', tcbCnodeMap_four]
  rfl

theorem isValidTimeoutHandler_eq {Z : Type} [StateExt Z] {σ : State Z} {t : ObjRef} {x : Tcb}
    (hk : σ.kheap t = some (.tcb x)) :
    isValidTimeoutHandler (Z := Z) t σ = ({(isEpCap x.tcbTimeoutHandler, σ)}, False) := by
  unfold isValidTimeoutHandler getTcbTimeoutHandlerPtr
  rw [nd_pure_bind', nd_bind_one (getCap_tcb_four hk)]
  rfl

open Classical in
/-- **l4v `handle_timeout`** with an endpoint cap as the timeout handler:
the fault set, then the send. -/
theorem handleTimeout_mem {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    {p bd : Word} {r : CapRights} (hc : x.tcbTimeoutHandler = .endpointCap p bd r) (ex : Fault)
    {z : Unit × State Unit}
    (hz : z ∈ (sendIpc (Z := Unit) true false bd (decide (Rights.allowGrant ∈ r)) (decide (Rights.allowGrantReply ∈ r))
      false t p (Notif.updK σ t (.tcb { x with tcbFault := some ex }))).1) :
    ((), z.2) ∈ (handleTimeout (Z := Unit) t ex σ).1 := by
  unfold handleTimeout
  rw [nd_bind_one (isValidTimeoutHandler_eq hk), hc]
  rw [nd_bind_one (assert_true' (show isEpCap (.endpointCap p bd r) = true from rfl) σ), nd_pure_bind']
  unfold getTcbTimeoutHandlerPtr
  rw [nd_bind_one (getCap_tcb_four hk), hc]
  unfold sendFaultIpc
  dsimp only
  rw [nd_bind_assoc_fun, nd_bind_one (Notif.threadSet_eq _ hk)]
  refine mem_bind_nd (x := (true, z.2)) ?_ ?_
  · refine mem_bind_nd (x := z) hz ?_
    simp [pure, NonDet.pure]
  · simp [pure, NonDet.pure]

end Spec

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

theorem tcb_slot_timeout (t : U64) : obj.Tcb.slot t layout.tcb.SLOT_TIMEOUT_HANDLER = ok (slotOf t 4) := by
  unfold obj.Tcb.slot layout.tcb.SLOT_TIMEOUT_HANDLER layout.cte.SIZE
  simp only [lift, bind_ok]
  congr 1

/-- The timeout-handler slot of a related TCB: FL4's cap and the spec's. -/
theorem _root_.Fl4Proofs.P3.StateRel.timeoutCap {Z : Type} {th : TypedHeap} {s : S} {σ : Fl4Spec.State Z}
    (hR : StateRel th (L.mem s) σ) {t : U64} (ht : th t = some .tcb) :
    ∃ x c, σ.kheap t.bv = some (.tcb x) ∧ capAt (L.mem s) (slotOf t 4) = ok c ∧ CapRel c x.tcbTimeoutHandler := by
  obtain ⟨x, hkx, hsl⟩ := hR.tcb t ht
  obtain ⟨c, ac, hc, hac, hca⟩ := hsl 4 (by decide)
  rw [tcbCnodeMap_four] at hac
  cases hac
  exact ⟨x, c, hkx, hc, hca⟩

/-- **`valid_timeout_handler` refines l4v `is_valid_timeout_handler`** on
the CSpace relation alone. -/
theorem valid_timeout_handler_rel {Z : Type} [Fl4Spec.StateExt Z] {th : TypedHeap} (s : S) (σ : Fl4Spec.State Z)
    (hR : StateRel th (L.mem s) σ) {t : U64} (ht : th t = some .tcb) :
    faults.valid_timeout_handler st s t ⦃ b => Fl4Spec.isValidTimeoutHandler (Z := Z) t.bv σ = ({(b, σ)}, False) ∧
      ∃ x, σ.kheap t.bv = some (.tcb x) ∧ b = Fl4Spec.isEpCap x.tcbTimeoutHandler ⦄ := by
  obtain ⟨x, c, hkx, hc, hca⟩ := hR.timeoutCap ht
  have hb : ∀ b, b = Fl4Spec.isEpCap x.tcbTimeoutHandler →
      Fl4Spec.isValidTimeoutHandler (Z := Z) t.bv σ = ({(b, σ)}, False) ∧
      ∃ x', σ.kheap t.bv = some (.tcb x') ∧ b = Fl4Spec.isEpCap x'.tcbTimeoutHandler := fun b hb =>
    ⟨by rw [isValidTimeoutHandler_eq hkx, hb], x, hkx, hb⟩
  unfold faults.valid_timeout_handler
  rw [tcb_slot_timeout]
  apply ok_bind_spec
  rw [slot_cap_eq, hc]
  apply ok_bind_spec
  have hx := hca.2
  cases c <;> exact (WP.spec_ok _).2 (hb _ (by rw [← hx]; simp [absCap, Fl4Spec.isEpCap]))

end


/-! ## Setting a fault -/

section Fault
open Fl4Proofs.P3.Sched
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

theorem tf_faultRange {t b : U64} (hta : TcbAddr t) (hb : Aligned b) (h1 : t.val + 3376 ≤ b.val)
    (h2 : b.val < t.val + 3408) : TF t b := by
  have := hta.align
  unfold TF TOffN; unfold Aligned at hb; omega

/-- **The fault words of a TCB rewritten** (type and three words, from
`t + 3376` to `t + 3408`): the merged relation for the TCB with the fault
`f` they encode. -/
theorem fault_set_ipc (hP0 : IPlaced N T E R B) {s s' : S} {σ : Fl4Spec.State Unit}
    (hR : IpcRel N T E R B (L.mem s) σ) {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb}
    (hk : σ.kheap t.bv = some (.tcb x)) (f : Option Fl4Spec.Fault)
    (hag : ∀ w, Aligned w → (w.val < t.val + 3376 ∨ t.val + 3408 ≤ w.val) → L.mem s' w = L.mem s w)
    (h0 : L.mem s' (tFaultA t) = 0#u64 ↔ f = none) (h5 : L.mem s' (tFaultA t) = 5#u64 ↔ ∃ b, f = some (.timeout b))
    (hfr : FaultRel (L.mem s') t f) :
    IpcRel N T E R B (L.mem s') (updK σ t.bv (.tcb { x with tcbFault := f })) := by
  have hta := hP0.e.tcb t ht
  have g : ∀ w, Aligned w → (w.val < t.val + 3376 ∨ t.val + 3408 ≤ w.val) → L.mem s' w = L.mem s w := hag
  obtain ⟨x0, hk0, hx⟩ := hR.tcb t ht
  rw [hk] at hk0; injection hk0 with hk0; injection hk0 with hk0; subst hk0
  refine hR.upd_tcb hP0 ht _ (fun b hb ⟨_, hnt⟩ => g b hb (by
      by_contra hc; push_neg at hc
      exact hnt (Or.inl (tf_faultRange hta hb hc.1 hc.2)))) (Or.inr ⟨g _ (a_st hta).1 (by rw [val_st hta]; omega),
      g _ (a_blk hta).1 (by rw [val_blk hta]; omega)⟩) ?_
  have hreg : ∀ r, (regA t (regIdx r)).val < t.val + 3376 := fun r => by
    rw [regA_val hta (regIdx_lt r)]; have := regIdx_lt r; omega
  refine ⟨?_, fun e he => ?_, fun n hn => ?_, fun e d h => ?_, fun e r d h => ?_, fun r h => ?_, fun r => ?_,
    ?_, h0, h5, ?_, hfr, ?_⟩
  · rw [g _ (a_st hta).1 (by rw [val_st hta]; omega)]; exact hx.st
  · rw [g _ (a_blk hta).1 (by rw [val_blk hta]; omega)]; exact hx.blkE e he
  · rw [g _ (a_blk hta).1 (by rw [val_blk hta]; omega)]; exact hx.blkN n hn
  · rw [g _ (a_badge hta).1 (by rw [val_badge hta]; omega), g _ (a_flags hta).1 (by rw [val_flags hta]; omega)]
    exact hx.send e d h
  · rw [g _ (a_reply hta).1 (by rw [val_reply hta]; omega)]; exact hx.recv e r d h
  · rw [g _ (a_reply hta).1 (by rw [val_reply hta]; omega)]; exact hx.reply r h
  · rw [g _ (a_reg hta r).1 (Or.inl (hreg r))]; exact hx.regs r
  · rw [g _ (a_prio hta).1 (by rw [val_prio hta]; omega)]; exact hx.prio
  · rw [g _ (a_bound hta).1 (by rw [val_bound hta]; omega)]; exact hx.bound
  · rw [g _ (scA_aligned hta) (by rw [scA_val hta]; omega)]; exact hx.sc

/-- A fault-word offset of a TCB. -/
def FaultOff (K : U64) : Prop := K = 3376#u64 ∨ K = 3384#u64 ∨ K = 3392#u64 ∨ K = 3400#u64

theorem FaultOff.val {K : U64} (h : FaultOff K) : 3376 ≤ K.val ∧ K.val < 3408 ∧ K.val % 8 = 0 := by
  rcases h with rfl | rfl | rfl | rfl <;> decide

/-- **The scheduler relation after a write to a fault word.** -/
theorem fault_word_sre {s : S} {σ : Fl4Spec.State Unit} (hS : SRE st N T C E R B c s σ) {t : U64} (ht : t ∈ T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (f : Option Fl4Spec.Fault) {K : U64} (hK : FaultOff K)
    (v : U64) :
    SRE st N T C E R B c (L.wr s (core.num.U64.wrapping_add t K) v) (updK σ t.bv (.tcb { x with tcbFault := f })) := by
  obtain ⟨Q, R0, hc, -⟩ := hS.1.lists
  have hta := hc.tcbs t ht
  obtain ⟨k1, k2, k3⟩ := hK.val
  have hK' : K.val < 4096 := by omega
  have ha := sagree_tcb_wr hS.1 ht (K := K) hK' k3 (fun K' h => by
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hK with rfl | rfl | rfl | rfl <;> decide) v
  have hw : Aligned (core.num.U64.wrapping_add t K) := field_aligned hta hK' k3
  have hn : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      nodeW st (L.wr s (core.num.U64.wrapping_add t K) v) c o = nodeW st s c o := fun o ho h8 => by
    unfold Fl4Proofs.P3.Sched.nodeW; rw [Sched.nodeAt_ksb (st := st) (L.ksb_wr _ _ _)]
    exact rd_wr_ne hw (nodeAt_aligned hc.node ho h8) (Ne.symm (nodeAt_ne_tfield hc.node ho ht hta hK'))
  refine ⟨hS.1.of_sagreeE ha (hn _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))
    (hn _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])) hS.1.nodeNW hS.1.domNW hS.1.dtNW
    (SchedStep.updK_tcb hk rfl rfl rfl), hS.2.mono (L.ksb_wr _ _ _) (SzKeep.updK hk (fun _ _ h => by cases h))⟩

/-- **`RelTopI ∧ SRE` after a write to a fault word.** -/
theorem fault_word_top {s : S} {σ : Fl4Spec.State Unit} (hS : SRT st th cr N T C E R B c (SRE st N T C E R B c) s σ)
    {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (f : Option Fl4Spec.Fault)
    {K : U64} (hK : FaultOff K) (v : U64) :
    SRT st th cr N T C E R B c (SRE st N T C E R B c) (L.wr s (core.num.U64.wrapping_add t K) v)
      (updK σ t.bv (.tcb { x with tcbFault := f })) := by
  obtain ⟨Q, R0, hc, -⟩ := hS.2.1.lists
  have hta := hc.tcbs t ht
  obtain ⟨k1, k2, k3⟩ := hK.val
  have hK' : K.val < 4096 := by omega
  have hv := tfield_val hta hK'
  refine ⟨hS.1.frame (writesIn_wr (field_aligned hta hK' k3)) (fun a ha => Or.inl ⟨t, ht, ?_, ?_⟩)
    (fun a ha => by rw [ha]; exact NoBufW.off hc.tcbs ht hK' (by omega)) ?_ rfl rfl
    (VsKeep.updK_tcb hk rfl),
    fault_word_sre hS.2 ht hk f hK v⟩
  · rw [ha, hv]; omega
  · rw [ha, hv]; omega
  · refine ⟨fun o => ?_, fun o r cs hc' _ => ?_, fun o y hy => ?_, rfl, rfl⟩
    · by_cases e : o = t.bv
      · subst e
        refine ⟨fun r cs h _ => by simp [updK] at h, fun _ _ => ⟨x, hk⟩, fun hn => by rw [hk] at hn; cases hn⟩
      · simp only [updK, Function.update_of_ne e]
        exact ⟨fun r cs h hw => ⟨cs, h, hw⟩, fun y h => ⟨y, h⟩, id⟩
    · have e : o ≠ t.bv := by rintro rfl; rw [hk] at hc'; cases hc'
      simp only [updK, Function.update_of_ne e]; exact hc'
    · by_cases e : o = t.bv
      · subst e; rw [hk] at hy; cases hy
        exact ⟨{ x with tcbFault := f }, by simp [updK], rfl⟩
      · exact ⟨y, by simp only [updK, Function.update_of_ne e]; exact hy, rfl⟩

theorem set_fault_w0_spec (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_fault_w0 st t s v ⦃ s' => s' = L.wr s (tFw0A t) v ⦄ := by
  unfold obj.Tcb.set_fault_w0; step*; simp_all [tFw0A]
theorem set_fault_w1_spec (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_fault_w1 st t s v ⦃ s' => s' = L.wr s (tFw1A t) v ⦄ := by
  unfold obj.Tcb.set_fault_w1; step*; simp_all [tFw1A]
theorem set_fault_w2_spec (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_fault_w2 st t s v ⦃ s' => s' = L.wr s (tFw2A t) v ⦄ := by
  unfold obj.Tcb.set_fault_w2; step*; simp_all [tFw2A]

theorem updK_idem' (σ : Fl4Spec.State Unit) (p : Fl4Spec.ObjRef) (o o' : Fl4Spec.KernelObject) :
    updK (updK σ p o) p o' = updK σ p o' := by
  simp only [updK, Function.update_idem]

set_option maxHeartbeats 4000000 in
/-- **`set_fault` of a timeout fault** refines l4v's `thread_set` of the
fault, on `IRel`. -/
theorem set_fault_timeout_top (hP0 : IPlaced N T E R B) {s : S} {σ : Fl4Spec.State Unit}
    (hX : IRel st th cr N T C E R B c s σ) {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x))
    (b : U64) :
    faults.set_fault st s t (error.Fault.Timeout b) ⦃ s' =>
      Fl4Spec.threadSet (Z := Unit) (fun tcb => { tcb with tcbFault := some (.timeout b.bv) }) t.bv σ =
        ({((), updK σ t.bv (.tcb { x with tcbFault := some (.timeout b.bv) }))}, False) ∧
      IRel st th cr N T C E R B c s' (updK σ t.bv (.tcb { x with tcbFault := some (.timeout b.bv) })) ⦄ := by
  obtain ⟨hIR, hSRT⟩ := hX
  have hta := hP0.e.tcb t ht
  set f : Option Fl4Spec.Fault := some (.timeout b.bv)
  set y : Fl4Spec.Tcb := { x with tcbFault := f }
  set σ' := updK σ t.bv (.tcb y)
  have hk' : σ'.kheap t.bv = some (.tcb y) := by simp [σ']
  have hidem : updK σ' t.bv (.tcb { y with tcbFault := f }) = σ' := by
    show updK (updK σ t.bv (.tcb y)) t.bv (.tcb y) = _; rw [updK_idem']
  unfold faults.set_fault
  simp only [bind_ok]
  step with Fl4Proofs.P1.obj.Tcb.set_fault_type.spec as ⟨s1, hs1⟩
  step with set_fault_w0_spec as ⟨s2, hs2⟩
  step with set_fault_w1_spec as ⟨s3, hs3⟩
  refine WP.spec_mono (set_fault_w2_spec s3 t 0#u64) ?_
  rintro s4 rfl
  subst hs1 hs2 hs3
  rw [show Fl4Proofs.P1.faultA t = tFaultA t from rfl]
  refine ⟨Notif.threadSet_eq _ hk, ?_, ?_⟩
  · -- the IPC relation
    have hfa := (a_fault hta).1
    have h0a := (a_fw0 hta).1
    have h1a := (a_fw1 hta).1
    have h2a := (a_fw2 hta).1
    have vf := val_fault hta
    have v0 := val_fw0 hta
    have v1 := val_fw1 hta
    have v2 := val_fw2 hta
    have rd : ∀ w, Aligned w → w ≠ tFw0A t → w ≠ tFw1A t → w ≠ tFw2A t →
        L.mem (L.wr (L.wr (L.wr (L.wr s (tFaultA t) fl4_abi.consts.fault.Timeout) (tFw0A t) b) (tFw1A t) 0#u64)
          (tFw2A t) 0#u64) w = L.mem (L.wr s (tFaultA t) fl4_abi.consts.fault.Timeout) w := by
      intro w hw n0 n1 n2
      rw [rd_wr_ne h2a hw (Ne.symm n2), rd_wr_ne h1a hw (Ne.symm n1), rd_wr_ne h0a hw (Ne.symm n0)]
    have hft : L.mem (L.wr (L.wr (L.wr (L.wr s (tFaultA t) fl4_abi.consts.fault.Timeout) (tFw0A t) b)
        (tFw1A t) 0#u64) (tFw2A t) 0#u64) (tFaultA t) = 5#u64 := by
      rw [rd (tFaultA t) hfa (fun e => by have := congrArg UScalar.val e; omega)
        (fun e => by have := congrArg UScalar.val e; omega) (fun e => by have := congrArg UScalar.val e; omega)]
      rw [rd_wr_eq hfa]; unfold fl4_abi.consts.fault.Timeout; rfl
    have hw0 : L.mem (L.wr (L.wr (L.wr (L.wr s (tFaultA t) fl4_abi.consts.fault.Timeout) (tFw0A t) b)
        (tFw1A t) 0#u64) (tFw2A t) 0#u64) (tFw0A t) = b := by
      rw [rd_wr_ne h2a h0a (fun e => by have := congrArg UScalar.val e; omega),
        rd_wr_ne h1a h0a (fun e => by have := congrArg UScalar.val e; omega), rd_wr_eq h0a]
    have h0 : L.mem (L.wr (L.wr (L.wr (L.wr s (tFaultA t) fl4_abi.consts.fault.Timeout) (tFw0A t) b)
        (tFw1A t) 0#u64) (tFw2A t) 0#u64) (tFaultA t) = 0#u64 ↔ f = none :=
      ⟨fun h => absurd (hft.symm.trans h) (by decide), fun h => absurd h (by simp [f])⟩
    have h5 : L.mem (L.wr (L.wr (L.wr (L.wr s (tFaultA t) fl4_abi.consts.fault.Timeout) (tFw0A t) b)
        (tFw1A t) 0#u64) (tFw2A t) 0#u64) (tFaultA t) = 5#u64 ↔ ∃ b', f = some (.timeout b') :=
      ⟨fun _ => ⟨b.bv, rfl⟩, fun _ => hft⟩
    refine fault_set_ipc hP0 hIR ht hk f (fun w hw hr => ?_) h0 h5 ⟨hft, by rw [hw0]⟩
    have n0 : w ≠ tFw0A t := fun e => by subst e; omega
    have n1 : w ≠ tFw1A t := fun e => by subst e; omega
    have n2 : w ≠ tFw2A t := fun e => by subst e; omega
    rw [rd w hw n0 n1 n2, rd_wr_ne hfa hw (fun e => by subst e; omega)]
  · -- the scheduler and top relations
    have e1 := fault_word_top hSRT ht hk f (K := 3376#u64) (Or.inl rfl) fl4_abi.consts.fault.Timeout
    have e2 := fault_word_top e1 ht hk' f (K := 3384#u64) (Or.inr (Or.inl rfl)) b
    rw [hidem] at e2
    have e3 := fault_word_top e2 ht hk' f (K := 3392#u64) (Or.inr (Or.inr (Or.inl rfl))) 0#u64
    rw [hidem] at e3
    have e4 := fault_word_top e3 ht hk' f (K := 3400#u64) (Or.inr (Or.inr (Or.inr rfl))) 0#u64
    rw [hidem] at e4
    exact e4

end Fault


/-! ## A faulted sender's `send_ipc` -/

section SendF
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

set_option maxHeartbeats 4000000 in
/-- **`send_ipc` of a faulted sender** (no call, no donation) on
`IpcRel ∧ SRT … SRE`, by the endpoint's state, over the transfer to the
waiting receiver (`hXf`; `xferX_top` but for a timeout fault with an SC). -/
theorem send_ipc_faultI (hH : IpcSchedHyps st ar N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBf : EpBufHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBm : EpBufMapHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hTl : IpcEpTailHyps st A N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hP : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hR : IpcRel N T E R B (L.mem s) σ) (hSR : SRT st th cr N T C E R B c (SRE st N T C E R B c) s σ)
    (hV : Sched.SchedValid σ) (hTO : SVK.TailOK σ)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hnn : ∀ m, xt.tcbState ≠ .blockedOnNotification m)
    (hns : tsCode xt.tcbState ≠ 6) (hft : xt.tcbFault ≠ none)
    {e : U64} (he : e ∈ E)
    (hsort : ∀ xs, QueueRel (L.mem s) T .Ep (qOf (L.mem s) e) xs → PrioSorted (fun y => L.mem s (prioA y)) xs)
    (blk : Bool) (badge : U64) (g gr : Bool)
    (hXf : ∀ (d : U64) (xd : Fl4Spec.Tcb), d ∈ T → t ≠ d → ∀ (s1 : S) (σ1 : Fl4Spec.State Unit),
      EpStateRel T E R B (L.mem s1) σ1 → SRN st N T (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))) s1 σ1 →
      σ1.kheap t.bv = some (.tcb xt) → σ1.kheap d.bv = some (.tcb xd) →
      ipc.do_ipc_transfer st ar s1 a t e badge g d ⦃ s' => XferPost (L := L) T E R B
        (SRN st N T (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c)))) s1 σ1 t d e badge g xd s' ⦄) :
    endpoint.send_ipc st ar s a blk false badge g gr false t e ⦃ r => r.2 = a ∧
      ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) blk false badge.bv g gr false t.bv e.bv σ).1,
        IpcRel N T E R B (L.mem r.1) z.2 ∧ SRT st th cr N T C E R B c (SRE st N T C E R B c) r.1 z.2 ⦄ := by
  obtain ⟨x, hk, hx⟩ := hR.ep e he
  have blockCase : CanBlock false x → endpoint.send_ipc st ar s a blk false badge g gr false t e ⦃ r => r.2 = a ∧
      ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) blk false badge.bv g gr false t.bv e.bv σ).1,
        IpcRel N T E R B (L.mem r.1) z.2 ∧ SRT st th cr N T C E R B c (SRE st N T C E R B c) r.1 z.2 ⦄ := by
    intro hc
    cases blk
    · exact WP.spec_mono (send_ipc_noblockI (ar := ar) s a σ hR hSR he hk hc false badge g gr false t)
        fun _ ⟨h1, σ', h2, h3, h4⟩ => ⟨h1, ((), σ'), by rw [h2]; rfl, h3, h4⟩
    · exact WP.spec_mono (send_ipc_blockI hH hP s a σ hR hSR ht hkt hnb hnn he hk hc hsort false badge g gr false)
        fun _ ⟨h1, σ', h2, h3, h4⟩ => ⟨h1, ((), σ'), by rw [h2]; rfl, h3, h4⟩
  cases x with
  | idleEP => exact blockCase trivial
  | sendEP q => exact blockCase rfl
  | recvEP q =>
    obtain ⟨-, xs, hne, hq, hQ, hQO⟩ := hx
    obtain ⟨d, ys, rfl⟩ : ∃ d ys, xs = d :: ys := by
      cases xs with
      | nil => exact absurd rfl hne
      | cons d ys => exact ⟨d, ys, rfl⟩
    have hd : d ∈ T := hQ.mem d (by simp)
    obtain ⟨xd, hkd, -⟩ := hR.tcb d hd
    have hk' : σ.kheap e.bv = some (.endpoint (.recvEP (d.bv :: ys.map UScalar.bv))) := by rw [hk, hq]; rfl
    have hback := hback_of hV hkd
    obtain ⟨xt0, hkt0, hTRt⟩ := hR.tcb t ht
    rw [hkt] at hkt0; cases hkt0
    have htd : t ≠ d := by
      rintro rfl
      exact hnb.1 (hTRt.st.symm.trans (hQO t (by simp)).1)
    have hXs := IpcSchedHyps.stepsG (A := A) hH hBf hBm hP
    have hSB := IpcRel.toSRN hR hSR
    have hXf' := hXf d xd hd htd
    have cvN : ∀ r : S × A, (r.2 = a ∧ ¬ (Fl4Spec.sendIpc (Z := Unit) blk false badge.bv g gr false t.bv e.bv σ).2 ∧
        ∃ σ', ((), σ') ∈ (Fl4Spec.sendIpc (Z := Unit) blk false badge.bv g gr false t.bv e.bv σ).1 ∧
        EpStateRel T E R B (L.mem r.1) σ' ∧
        SRN st N T (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))) r.1 σ') →
        r.2 = a ∧ ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) blk false badge.bv g gr false t.bv e.bv σ).1,
          IpcRel N T E R B (L.mem r.1) z.2 ∧ SRT st th cr N T C E R B c (SRE st N T C E R B c) r.1 z.2 :=
      fun _ ⟨h1, _, σ', h2, h3, h4⟩ => ⟨h1, ((), σ'), h2, IpcRel.ofSRN h3 h4⟩
    by_cases hgg : g = true ∨ gr = true
    · by_cases hrp : ∀ e' rep dd, xd.tcbState = .blockedOnReceive e' rep dd → rep ≠ none
      · exact WP.spec_mono (send_ipc_callF_gen hXs.toEpSteps (hTl.tail hP) hP.e s a σ hR.toE hSB ht hkt hnb hns hft
          he hk' hkd badge g gr hXf' hback hgg hrp hTO blk) cvN
      · refine WP.spec_mono (send_ipc_call_inactiveF_gen hXs.toEpSteps (hTl.tail hP) hP.e s a σ hR.toE hSB ht hkt
          hnb hns hft he hk' hkd badge g gr hXf' hback (Or.inr ?_) hTO blk) cvN
        intro e' rep dd hs
        by_contra hn
        refine hrp fun e'' rep' dd' hs' => ?_
        rw [hs] at hs'; cases hs'; exact hn
    · refine WP.spec_mono (send_ipc_call_inactiveF_gen hXs.toEpSteps (hTl.tail hP) hP.e s a σ hR.toE hSB ht hkt hnb
        hns hft he hk' hkd badge g gr hXf' hback (Or.inl ?_) hTO blk) cvN
      cases g <;> cases gr <;> simp_all

open Classical in
theorem rights_grant (sd rv g gr : Bool) : decide (Fl4Spec.Rights.allowGrant ∈ rightsOf sd rv g gr) = g := by
  cases g <;> simp [rightsOf]

open Classical in
theorem rights_grantReply (sd rv g gr : Bool) :
    decide (Fl4Spec.Rights.allowGrantReply ∈ rightsOf sd rv g gr) = gr := by
  cases gr <;> simp [rightsOf]

set_option maxHeartbeats 8000000 in
/-- **`handle_timeout` refines l4v `handle_timeout`** on `IRel`, for a
thread whose timeout handler is an endpoint cap: `set_fault`
(`set_fault_timeout_top`), then the faulted send (`send_ipc_faultI`) over
the transfer of the timeout fault (`hXf`). -/
theorem handle_timeout_top (hH : IpcSchedHyps st ar N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBf : EpBufHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBm : EpBufMapHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hTl : IpcEpTailHyps st A N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hP : IPlaced N T E R B)
    (hSV : ∀ s' σ', IRel st th cr N T C E R B c s' σ' → Sched.SchedValid σ')
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ) (hS0 : Sched.IpcSorted σ)
    (hTO : SVK.TailOK σ)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hnn : ∀ m, xt.tcbState ≠ .blockedOnNotification m)
    (hns : tsCode xt.tcbState ≠ 6)
    {p bd : Fl4Spec.Word} {r : Fl4Spec.CapRights} (hc : xt.tcbTimeoutHandler = .endpointCap p bd r)
    (hpE : ∀ e : U64, e.bv = p → e ∈ E) (b : U64)
    (hXf : ∀ (e bdg : U64) (g : Bool) (d : U64) (xd : Fl4Spec.Tcb), d ∈ T → t ≠ d → ∀ (s1 : S) (σ1 : Fl4Spec.State Unit),
      EpStateRel T E R B (L.mem s1) σ1 → SRN st N T (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))) s1 σ1 →
      σ1.kheap t.bv = some (.tcb { xt with tcbFault := some (.timeout b.bv) }) → σ1.kheap d.bv = some (.tcb xd) →
      ipc.do_ipc_transfer st ar s1 a t e bdg g d ⦃ s' => XferPost (L := L) T E R B
        (SRN st N T (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c)))) s1 σ1 t d e bdg g xd s' ⦄) :
    faults.handle_timeout st ar s a t (error.Fault.Timeout b) ⦃ res => res.2 = a ∧
      ∃ z ∈ (Fl4Spec.handleTimeout (Z := Unit) t.bv (.timeout b.bv) σ).1, IRel st th cr N T C E R B c res.1 z.2 ⦄ := by
  obtain ⟨hIR, hSRT⟩ := hX
  obtain ⟨⟨G, hB⟩, -⟩ := hSRT.1
  have htt := hB.tcbT hkt
  obtain ⟨x, cv, hkx, hcv, hca⟩ := hB.2.1.1.timeoutCap htt
  rw [hkt] at hkx; cases hkx
  have habs := hca.2
  rw [hc] at habs
  unfold faults.handle_timeout
  rw [tcb_slot_timeout]
  apply ok_bind_spec
  rw [slot_cap_eq, hcv]
  apply ok_bind_spec
  cases cv with
  | Endpoint ptr bdg sd rv g gr =>
    simp only [absCap, Fl4Spec.Cap.endpointCap.injEq] at habs
    obtain ⟨hp, hbd, hr⟩ := habs
    subst hp hbd hr
    refine WP.spec_bind (Pₘ := fun r : Bool × S × A => r.2.2 = a ∧
      ∃ z ∈ (Fl4Spec.handleTimeout (Z := Unit) t.bv (.timeout b.bv) σ).1, IRel st th cr N T C E R B c r.2.1 z.2) ?_ ?_
    swap
    · rintro ⟨b0, s2, a2⟩ hr
      exact (WP.spec_ok _).2 hr
    unfold faults.send_fault_ipc
    dsimp only
    refine WP.spec_bind (set_fault_timeout_top hP ⟨hIR, hSRT⟩ ht hkt b) ?_
    rintro s1 ⟨-, hX1⟩
    set xt' : Fl4Spec.Tcb := { xt with tcbFault := some (.timeout b.bv) }
    have hk1 : (updK σ t.bv (.tcb xt')).kheap t.bv = some (.tcb xt') := by simp
    have hpE' := hpE ptr rfl
    refine WP.spec_bind (send_ipc_faultI hH hBf hBm hTl hP s1 a _ hX1.1 hX1.2 (hSV _ _ hX1) (tailOK_upd hTO hkt rfl rfl) ht hk1 hnb hnn hns
      (by simp [xt']) hpE' (Sched.qSorted_of_spec (L := L) hX1.1.toE hX1.1.toN hP.e.tcb
        (QPK.QPS.sorted (QPK.qps_upd (ko := .tcb xt') hkt rfl) hS0) ptr (Or.inl hpE')) true bdg g gr
      (fun d xd hd htd => hXf ptr bdg g d xd hd htd)) ?_
    rintro ⟨s2, a2⟩ ⟨ha2, z, hz, hIz, hSz⟩
    simp only at ha2
    subst ha2
    refine (WP.spec_ok _).2 ⟨rfl, ((), z.2), handleTimeout_mem hkt hc _ ?_, hIz, hSz⟩
    rw [rights_grant, rights_grantReply]
    exact hz
  | _ => simp [absCap] at habs

variable (st ar th cr N T C E R B c) in
/-- **The named steps of the reply's timeout branch** (`ReplyHyps.tmo`):
`postpone` on `IRel` for a thread in no release queue (l4v
`not_in_release_q`, given by the caller; `RelOK` from `valid_sched`), the timeout fault's transfer from a thread with an SC (its
message carries the consumed time, `update_consumed`), and the timeout
handler's endpoint in the ghost set (l4v `valid_objs`). -/
structure ReplyTmoHyps : Prop where
  postpone : ∀ s (a : A) σ (t sc : U64) (x : Fl4Spec.Tcb) (y : Fl4Spec.SchedContext) (n : Nat),
    IRel st th cr N T C E R B c s σ → t ∈ T → sc ∈ C → σ.kheap t.bv = some (.tcb x) →
    Fl4Spec.runnable x.tcbState = true → x.tcbSchedContext = some sc.bv → σ.kheap sc.bv = some (.schedContext y n) →
    Fl4Spec.scActive y = true → t.bv ∉ σ.releaseQueue →
    (do let s4 ← sched.postpone st s sc; ok (s4, a)) ⦃ res =>
      ∃ z ∈ (Fl4Spec.postpone (Z := Unit) sc.bv σ).1, IRel st th cr N T C E R B c res.1 z.2 ⦄
  tmoXfer : ∀ (a : A) (t : U64) (xt : Fl4Spec.Tcb) (bb : Fl4Spec.Word) (e bdg : U64) (g : Bool) (d : U64)
    (xd : Fl4Spec.Tcb), t ∈ T → d ∈ T → t ≠ d → xt.tcbFault = some (.timeout bb) → xt.tcbSchedContext ≠ none →
    ∀ (s1 : S) (σ1 : Fl4Spec.State Unit),
      EpStateRel T E R B (L.mem s1) σ1 → SRN st N T (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))) s1 σ1 →
      σ1.kheap t.bv = some (.tcb xt) → σ1.kheap d.bv = some (.tcb xd) →
      ipc.do_ipc_transfer st ar s1 a t e bdg g d ⦃ s' => XferPost (L := L) T E R B
        (SRN st N T (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c)))) s1 σ1 t d e bdg g xd s' ⦄
  epE : ∀ s σ (t : U64) (x : Fl4Spec.Tcb) (p bd : Fl4Spec.Word) (r : Fl4Spec.CapRights),
    IRel st th cr N T C E R B c s σ → t ∈ T → σ.kheap t.bv = some (.tcb x) →
    x.tcbTimeoutHandler = .endpointCap p bd r → ∀ e : U64, e.bv = p → e ∈ E

set_option maxHeartbeats 8000000 in
/-- **The timeout branch of the reply tail** (`ReplyHyps.tmo`):
`valid_timeout_handler` (`valid_timeout_handler_rel`), `handle_timeout`
(`handle_timeout_top`) or `postpone`, against l4v's. -/
theorem reply_tmo_top (hH : IpcSchedHyps st ar N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBf : EpBufHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBm : EpBufMapHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hTl : IpcEpTailHyps st A N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hP : IPlaced N T E R B)
    (hSV : ∀ s' σ', IRel st th cr N T C E R B c s' σ' → Sched.SchedValid σ')
    (hTH : ReplyTmoHyps st ar th cr N T C E R B c) :
    ∀ s (a : A) σ (t sc ft : U64) (fault : Option Fl4Spec.Fault) (y : Fl4Spec.SchedContext) (n : Nat),
    IRel st th cr N T C E R B c s σ → t ∈ T → sc ∈ C → σ.kheap sc.bv = some (.schedContext y n) →
    Fl4Spec.scActive y = true → ∀ x : Fl4Spec.Tcb, σ.kheap t.bv = some (.tcb x) → Fl4Spec.runnable x.tcbState = true →
    x.tcbSchedContext = some sc.bv → t.bv ∉ σ.releaseQueue → Sched.IpcSorted σ → (ft = 0#u64 ↔ fault = none) →
    (ft = 5#u64 ↔ ∃ b, fault = some (.timeout b)) → SVK.TailOK σ →
    fl4ReplyTmo st ar t ft sc s a ⦃ res => ∃ z ∈ (specReplyTmo t.bv fault y sc.bv σ).1,
      IRel st th cr N T C E R B c res.1 z.2 ⦄ := by
  intro s a σ t sc ft fault y n hX ht hsc hky hya x hk hrn hxsc hnrq hS0 hf0 hf5 hTO
  obtain ⟨hIR, hSRT⟩ := hX
  obtain ⟨⟨G, hB⟩, -⟩ := hSRT.1
  have htt := hB.tcbT hk
  have hspec : ∀ P : Prop, ∀ [Decidable P], specReplyTmo t.bv fault y sc.bv σ =
      (if Fl4Spec.isEpCap x.tcbTimeoutHandler ∧ ¬(fault.elim false Fl4Spec.isTimeoutFault = true)
        then Fl4Spec.handleTimeout (Z := Unit) t.bv (.timeout y.scBadge) else Fl4Spec.postpone (Z := Unit) sc.bv) σ :=
    fun _ _ => by unfold specReplyTmo; rw [nd_bind_one (getTcb_eq hk)]
  have hspec' := hspec True
  have post : (do let s4 ← sched.postpone st s sc; ok (s4, a)) ⦃ res =>
      ∃ z ∈ (Fl4Spec.postpone (Z := Unit) sc.bv σ).1, IRel st th cr N T C E R B c res.1 z.2 ⦄ :=
    hTH.postpone s a σ t sc x y n ⟨hIR, hSRT⟩ ht hsc hk hrn hxsc hky hya hnrq
  have hrunc : tsCode x.tcbState ≠ 3 ∧ tsCode x.tcbState ≠ 4 ∧ (∀ m, x.tcbState ≠ .blockedOnNotification m) ∧
      tsCode x.tcbState ≠ 6 := by
    cases h : x.tcbState <;> simp_all [Fl4Spec.runnable, tsCode]
  unfold fl4ReplyTmo
  refine WP.spec_bind (valid_timeout_handler_rel s σ hB.2.1.1 htt) ?_
  rintro b5 ⟨-, x', hkx', hb5⟩
  rw [hk] at hkx'; cases hkx'
  by_cases hv : Fl4Spec.isEpCap x.tcbTimeoutHandler = true
  swap
  · rw [if_neg (by rw [hb5]; exact hv)]
    rw [hspec', if_neg (fun h => hv h.1)]
    exact post
  rw [if_pos (by rw [hb5]; exact hv)]
  by_cases hto : ft = fl4_abi.consts.fault.Timeout
  · rw [if_neg (by simp [hto])]
    have : ∃ b, fault = some (.timeout b) := hf5.1 (by rw [hto]; unfold fl4_abi.consts.fault.Timeout; rfl)
    obtain ⟨bb, hbb⟩ := this
    rw [hspec', if_neg (fun h => h.2 (by rw [hbb]; rfl))]
    exact post
  rw [if_pos (by simpa using hto)]
  have hnt : ¬(fault.elim false Fl4Spec.isTimeoutFault = true) := by
    intro h
    apply hto
    obtain ⟨bb, hbb⟩ : ∃ b, fault = some (.timeout b) := by
      cases fault with
      | none => simp at h
      | some f => cases f <;> simp_all [Option.elim, Fl4Spec.isTimeoutFault]
    rw [hf5.2 ⟨bb, hbb⟩]; unfold fl4_abi.consts.fault.Timeout; rfl
  rw [hspec', if_pos ⟨hv, hnt⟩]
  step with Fl4Proofs.P3.Sched.obj.Sc.badge.spec' as ⟨bw, hbw⟩
  subst hbw
  obtain ⟨Q, R0, -, hsp⟩ := hSRT.2.1.lists
  obtain ⟨y', n', hky', hy'⟩ := hsp.scs sc hsc
  rw [hky] at hky'; cases hky'
  rw [hy'.badge]
  obtain ⟨p, bd, r, hc⟩ : ∃ p bd r, x.tcbTimeoutHandler = .endpointCap p bd r := by
    cases h : x.tcbTimeoutHandler <;> simp [h, Fl4Spec.isEpCap] at hv
    exact ⟨_, _, _, rfl⟩
  have hsc0 : x.tcbSchedContext ≠ none := by rw [hxsc]; simp
  refine WP.spec_mono (handle_timeout_top hH hBf hBm hTl hP hSV s a σ ⟨hIR, hSRT⟩ hS0 hTO ht hk
    ⟨hrunc.1, hrunc.2.1⟩ hrunc.2.2.1 hrunc.2.2.2 hc (hTH.epE s σ t x p bd r ⟨hIR, hSRT⟩ ht hk hc)
    (L.mem s (Sched.scW sc 48#u64))
    (fun e bdg g d xd hd htd => hTH.tmoXfer a t { x with tcbFault := some (.timeout (L.mem s (Sched.scW sc 48#u64)).bv) }
      _ e bdg g d xd ht hd htd rfl hsc0)) ?_
  rintro _ ⟨-, z, hz, hXz⟩
  exact ⟨z, hz, hXz⟩

/-- **`ReplyHyps` from `remove`, `unblock` and the timeout branch's steps**
(`ReplyTmoHyps`): `faultReply`, `grantXfer` and `tmo` proved. -/
theorem ReplyHyps.ofT (hH : IpcSchedHyps st ar N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBf : EpBufHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBm : EpBufMapHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hTl : IpcEpTailHyps st A N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hP : IPlaced N T E R B)
    (hSV : ∀ s' σ', IRel st th cr N T C E R B c s' σ' → Sched.SchedValid σ')
    (hTH : ReplyTmoHyps st ar th cr N T C E R B c)
    (hrem : ∀ s (a : A) σ (r t : U64) (x : Fl4Spec.Tcb), IRel st th cr N T C E R B c s σ → r ∈ R → t ∈ T →
      σ.kheap t.bv = some (.tcb x) → x.tcbState = .blockedOnReply r.bv →
      ipc.reply_remove st ar s a r t ⦃ res => res.2 = a ∧ ∃ σ' x',
        Fl4Spec.replyRemove (Z := Unit) t.bv r.bv σ = ({((), σ')}, False) ∧ IRel st th cr N T C E R B c res.1 σ' ∧
        σ'.kheap t.bv = some (.tcb x') ∧ x'.tcbState = .inactive ∧ x'.tcbFault = x.tcbFault ∧
        (∀ p y n, σ'.kheap p = some (.schedContext y n) → y.scTcb = some t.bv → Fl4Spec.scActive y = true) ∧
        ∀ p y, p ≠ t.bv → σ.kheap p = some (.tcb y) → ∃ y', σ'.kheap p = some (.tcb y') ∧
          y'.tcbFault = y.tcbFault ∧ y'.tcbState = y.tcbState ⦄)
    (hunb : ∀ s σ (t : U64) (x : Fl4Spec.Tcb) (k : S → Result (S × A)) (P : S × A → Prop),
      IRel st th cr N T C E R B c s σ → t ∈ T → σ.kheap t.bv = some (.tcb x) →
      (∀ s' σ', (Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbSchedContext t.bv >>=
          Fl4Spec.ifSporadicCurScTestRefillUnblockCheck) σ = ({((), σ')}, False) → IRel st th cr N T C E R B c s' σ' →
        (∀ p y, σ.kheap p = some (.tcb y) → σ'.kheap p = some (.tcb y)) → k s' ⦃ P ⦄) →
      (do
        let i2 ← obj.Tcb.sc st t s
        let b1 ← sporadic.sc_sporadic st s i2
        let s2 ←
          if b1
          then
            do
            let i3 ← obj.Sc.cpu st i2 s
            let i4 ← obj.node_get st s i3 layout.node.CUR_SC
            if i2 != i4
            then sporadic.unblock_check st s i2
            else ok s
          else ok s
        k s2) ⦃ P ⦄)
    (hinv : ∀ s σ, IRel st th cr N T C E R B c s σ → Sched.Inv σ) :
    ReplyHyps st ar th cr N T C E R B c :=
  ReplyHyps.of hH hBf hBm hP hrem hunb (reply_tmo_top hH hBf hBm hTl hP hSV hTH) hinv

end SendF

end

end Fl4Proofs.P3.Endp
