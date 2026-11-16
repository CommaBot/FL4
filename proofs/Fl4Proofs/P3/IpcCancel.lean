/-
P3 (DESIGN.md §9), IPC: **`cancel_ipc` of a thread blocked on a receive**
(the `cancelIpc` field of `IpcSchedHyps`), on the merged relation.

* `IpcCore`: the part of `IpcSchedHyps` the endpoint step lemmas use
  (`stableE`, `scheduleTcb`), so that `cancel_ipc` can be proved without the
  `cancelIpc` field itself; `IpcCore.epHyps`, `IpcCore.schedC` and the step
  lemmas `ep_dequeue_c`, `reply_unlink_c`, `set_thread_state_c` are those of
  IpcEpBase/IpcEpSteps on `IpcCore`. `ipcCore_top`: `IpcCore` for
  `SRT … SRE`.
* `fault_clear_ipc`, `fault_clear_sre`, `fault_clear_top`: `clear_fault`
  (the fault word, outside `EWrite`) keeps the merged relation, the
  scheduler relation (`sagree_tcb_wr`, `SchedStep.updK_tcb`) and `RelTopI`.
* `cancel_ipc_recvI`: `cancel_ipc` of a thread blocked on a receive refines
  l4v `cancel_ipc` (clear the fault, dequeue, unlink the reply if any, set
  `Inactive`), with `RelIfBound` kept (`SKeep`), from the named state facts
  `CancelRecvHyp` (the spec's `CancelOK`, the endpoint in `E`,
  `RelIfBound`); `cancelIpc_top`: the `cancelIpc` field for `SRT … SRE`.
-/
import Fl4Proofs.P3.IpcSchedInst
import Fl4Proofs.P3.SpecFinOutTcb
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section Core
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- **The part of `IpcSchedHyps` the endpoint step lemmas use.** -/
structure IpcCore (N T E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (SR : S → Fl4Spec.State Unit → Prop) :
    Prop where
  stableE : ∀ s s' σ σ', SR s σ → WritesIn st s s' (EWrite T E R B) → EpStep σ σ' → SR s' σ'
  scheduleTcb : ∀ s σ (t : U64), EpStateRel T E R B (L.mem s) σ → ScRelM T (L.mem s) σ → SR s σ → t ∈ T →
    sched.schedule_tcb st s t ⦃ s' => Agree (L.mem s) (L.mem s') (IFoot N T E R B) ∧ SR s' (stsAct σ t.bv) ⦄

end Core

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {N T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

theorem IpcSchedHyps.core (hH : IpcSchedHyps st ar N T E R B SR) : IpcCore st N T E R B SR :=
  ⟨hH.stableE, hH.scheduleTcb⟩

theorem IpcCore.epHyps (hH : IpcCore st N T E R B SR) (hP : IPlaced N T E R B) :
    EpHyps st T E R B (SRS st T SR) :=
  ⟨fun _ _ _ _ h1 h2 h3 => ⟨hH.stableE _ _ _ _ h1.1 h2 h3, ScRelM.ep_step hP h1.2 h2.2.2 h3⟩,
   fun s σ t hR hS ht => WP.spec_mono (hH.scheduleTcb s σ t hR hS.2 hS.1 ht) fun _ ⟨hf, hS'⟩ =>
     ⟨fun a ha hfa => hf a ha (EFoot.ifoot hfa), hS', ScRelM.frame hP hS.2 hf (Notif.IKView.stsAct _ _)⟩⟩

theorem IpcCore.schedC (hH : IpcCore st N T E R B SR) (hP : IPlaced N T E R B) (s : S)
    (σ : Fl4Spec.State Unit) (t : U64) (hR : EpStateRel T E R B (L.mem s) σ) (hS : SRS st T SR s σ) (ht : t ∈ T) :
    sched.schedule_tcb st s t ⦃ s' => FootEq T E R B (L.mem s) (L.mem s') ∧ Notif.FootEq N T (L.mem s) (L.mem s') ∧
      SRS st T SR s' (stsAct σ t.bv) ⦄ :=
  WP.spec_mono (hH.scheduleTcb s σ t hR hS.2 hS.1 ht) fun _ ⟨hf, hS'⟩ =>
    ⟨fun a ha hfa => hf a ha (EFoot.ifoot hfa), fun a ha hfa => hf a ha (NFoot.ifoot hP hfa), hS',
      ScRelM.frame hP hS.2 hf (Notif.IKView.stsAct _ _)⟩

/-- `ep_dequeue` with the notification relation (`IpcSchedHyps.steps`' `deq`). -/
theorem ep_dequeue_c (hH : IpcCore st N T E R B SR) (hP0 : IPlaced N T E R B) (hP : EPlaced T E R B) (s : S)
    (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SRN st N T (SRS st T SR) s σ)
    {e : U64} (he : e ∈ E) {x : Fl4Spec.Endpoint} (hk : σ.kheap e.bv = some (.endpoint x)) {d : U64}
    (hd : d.bv ∈ x.epQueue) :
    endpoint.ep_dequeue st s e d ⦃ s' =>
      Fl4Spec.tcbEpDequeue (Z := Unit) d.bv e.bv σ = ({((), updK σ e.bv (.endpoint (epDeq x d.bv)))}, False) ∧
      EpStateRel T E R B (L.mem s') (updK σ e.bv (.endpoint (epDeq x d.bv))) ∧
      SRN st N T (SRS st T SR) s' (updK σ e.bv (.endpoint (epDeq x d.bv))) ∧
      Agree (L.mem s) (L.mem s') (AllTF T) ⦄ := by
  obtain ⟨xs, hQ, hxs, hB⟩ := (hR.at_ep he hk).queue
  have hdx : d ∈ xs := by
    rw [hxs, List.mem_map] at hd
    obtain ⟨y, hy, ey⟩ := hd
    rw [← eq_of_bv ey]; exact hy
  refine WP.spec_mono (WP.spec_and (ep_dequeue_rel (hH.epHyps hP0) hP s σ hR hSR.1 he hk hd)
    (ep_dequeue_full hP s he d xs hQ hdx)) ?_
  rintro s' ⟨⟨h1, h2, h3, h4⟩, -, -, hQA, -, -, -⟩
  have hkv : Notif.KView σ (updK σ e.bv (.endpoint (epDeq x d.bv))) := by
    refine ⟨fun p y h => ?_, fun p y h => ⟨y, ?_, rfl, rfl, rfl⟩⟩
    · have : p ≠ e.bv := by intro h'; rw [h', hk] at h; cases h
      simp [this, h]
    · have : p ≠ e.bv := by intro h'; rw [h', hk] at h; cases h
      simp [this, h]
  have hW : ∀ w ∈ xs, w ∈ T ∧ (L.mem s (tStA w)).val ≠ 6 := fun w hw =>
    ⟨hQ.mem w hw, by rcases (hB w hw).2 with h | h <;> rw [h] <;> simp⟩
  exact ⟨h1, h2, ⟨h3, ntfn_frame_ep hP0.toC hSR.2 he hW hQA hkv⟩, h4⟩

/-- `set_thread_state` to a state below 3, with the notification relation. -/
theorem set_thread_state_c (hH : IpcCore st N T E R B SR) (hP0 : IPlaced N T E R B) (hP : EPlaced T E R B) (s : S)
    (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SRN st N T (SRS st T SR) s σ) {t : U64} (ht : t ∈ T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x))
    (hq : ∀ e ∈ E, ∀ z, σ.kheap e.bv = some (.endpoint z) → t.bv ∉ z.epQueue) (hns : tsCode x.tcbState ≠ 6)
    (ts : Fl4Spec.ThreadState) (hts : tsCode ts < 3) (code : U64) (hcode : code.val = tsCode ts) :
    sched.set_thread_state st s t code ⦃ s' =>
      EpStateRel T E R B (L.mem s') (stsAct (updK σ t.bv (.tcb { x with tcbState := ts })) t.bv) ∧
      SRN st N T (SRS st T SR) s' (stsAct (updK σ t.bv (.tcb { x with tcbState := ts })) t.bv) ⦄ := by
  have hqn := not_member hSR.2 ht hk (tsCode_ne6 hns)
  have hta := hP.tcb t ht
  have ha := a_st hta
  have hag := agree_wr (L := L) (s := s) (v := code) ha.1
  have g : ∀ b, Aligned b → (b.val < t.val + 3328 ∨ t.val + 3368 ≤ b.val) →
      L.mem (L.wr s (tStA t) code) b = L.mem s b := fun b hb hv => hag b hb (by rw [val_st hta]; omega)
  have hx1 := hSR.2.at_tcb ht hk
  have hN1 : NtfnStateRel N T (L.mem (L.wr s (tStA t) code)) (updK σ t.bv (.tcb { x with tcbState := ts })) := by
    refine ntfn_upd_fields hP0.toC hSR.2 ht _ g hqn ⟨?_, ?_, ?_, ?_⟩
    · rw [rd_wr_eq ha.1]; exact hcode
    · intro n h; simp only at h; rw [h] at hts; simp [tsCode] at hts
    · show (L.mem _ (badgeRegA t)).bv = badgeOf { x with tcbState := ts }
      rw [g _ (by rw [badgeRegA_eq_regA]; exact (a_reg hta _).1) (by
        rw [badgeRegA_eq, tw_val hta (by simp)]; left; simp)]
      exact hx1.badge
    · show (L.mem _ (prioA t)).val = _
      rw [g _ (a_prio hta).1 (by rw [val_prio hta]; omega)]
      exact hx1.prio
  unfold sched.set_thread_state
  step
  subst s1_post
  obtain ⟨hR1, hW1, hS1⟩ := write_state_rel hP s σ hR ht hk hq ts hts code hcode
  refine WP.spec_mono ((hH.schedC hP0 _ _ t hR1 ((hH.epHyps hP0).stable _ _ _ _ hSR.1 hW1 hS1) ht)) ?_
  rintro s2 ⟨hf, hfN, hS⟩
  exact ⟨hR1.frame hP hf (KView.stsAct' _ _), hS, hN1.frame hP0.n hfN (Notif.KView.stsAct _ _)⟩

/-- **`reply_unlink`**, with the notification relation. -/
theorem reply_unlink_c (hH : IpcCore st N T E R B SR) (hP0 : IPlaced N T E R B) (hP : EPlaced T E R B) (s : S)
    (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SRN st N T (SRS st T SR) s σ) {t : U64} (ht : t ∈ T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) {e' : Fl4Spec.ObjRef} {dd : Fl4Spec.ReceiverPayload}
    {r : U64} (hst : x.tcbState = .blockedOnReceive e' (some r.bv) dd) (hr : r ∈ R) {xr : Fl4Spec.Reply}
    (hkr : σ.kheap r.bv = some (.reply xr)) (hback : xr.replyTcb = some t.bv)
    (hq : ∀ e ∈ E, ∀ z, σ.kheap e.bv = some (.endpoint z) → t.bv ∉ z.epQueue) :
    ipc.reply_unlink st s r t ⦃ s' =>
      Fl4Spec.replyUnlinkTcb (Z := Unit) t.bv r.bv σ =
        ({((), stsAct (updK (updK σ r.bv (.reply { xr with replyTcb := none })) t.bv
          (.tcb { x with tcbState := .inactive })) t.bv)}, False) ∧
      EpStateRel T E R B (L.mem s') (stsAct (updK (updK σ r.bv (.reply { xr with replyTcb := none })) t.bv
          (.tcb { x with tcbState := .inactive })) t.bv) ∧
      SRN st N T (SRS st T SR) s' (stsAct (updK (updK σ r.bv (.reply { xr with replyTcb := none })) t.bv
          (.tcb { x with tcbState := .inactive })) t.bv) ⦄ := by
  obtain ⟨e1, hR1, hS1, hA1⟩ := reply_write_rel (hH.epHyps hP0) hP s σ hR hSR.1 hr hkr 0#u64
  have hN1 := ntfn_reply_write hP0.toC hSR.2 hr hA1 hkr { xr with replyTcb := optRef 0#u64 }
  rw [optRef_zero] at e1 hR1 hS1 hN1
  have hrt : r.bv ≠ t.bv := kheap_ne hkr hk (fun _ h1 h2 => by subst h1; cases h2)
  have hk1 : (updK σ r.bv (.reply { xr with replyTcb := none })).kheap t.bv = some (.tcb x) := by
    simp [Ne.symm hrt, hk]
  have hq1 : ∀ e ∈ E, ∀ z, (updK σ r.bv (.reply { xr with replyTcb := none })).kheap e.bv = some (.endpoint z) →
      t.bv ∉ z.epQueue := by
    intro e he z hz
    have hre : r.bv ≠ e.bv := by
      intro h; rw [← h] at hz; simp at hz
    exact hq e he z (by simpa [Ne.symm hre] using hz)
  unfold ipc.reply_unlink
  step as ⟨s1, hs1⟩
  subst hs1
  refine WP.spec_mono (set_thread_state_c hH hP0 hP _ _ hR1 ⟨hS1, hN1⟩ ht hk1 hq1 (by rw [hst]; simp [tsCode])
    .inactive (by simp [tsCode]) sched.TS_INACTIVE (by unfold sched.TS_INACTIVE; rfl)) ?_
  rintro s2 ⟨hR2, hS2⟩
  refine ⟨?_, hR2, hS2⟩
  unfold Fl4Spec.replyUnlinkTcb
  rw [nd_bind_one (getReply_eq hkr), nd_bind_one (assert_true hback σ), nd_bind_one (getThreadState_eq hk),
    nd_bind_one (assert_true (Or.inr ⟨e', dd, hst⟩) σ), nd_bind_one e1, Notif.setThreadState_eq _ hk1]

/-! ## Clearing the fault -/

/-- **Clearing a TCB's fault word**: the merged relation for the TCB with no
fault. -/
theorem fault_clear_ipc (hP0 : IPlaced N T E R B) {s : S} {σ : Fl4Spec.State Unit}
    (hR : IpcRel N T E R B (L.mem s) σ) {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb}
    (hk : σ.kheap t.bv = some (.tcb x)) :
    IpcRel N T E R B (L.mem (L.wr s (tFaultA t) 0#u64)) (updK σ t.bv (.tcb { x with tcbFault := none })) := by
  have hta := hP0.e.tcb t ht
  have hfa := a_fault hta
  have g : ∀ w, Aligned w → w.val ≠ t.val + 3376 → L.mem (L.wr s (tFaultA t) 0#u64) w = L.mem s w :=
    fun w hw hne => rd_wr_ne hfa.1 hw (fun e => hne (by rw [← e, val_fault hta]))
  obtain ⟨x0, hk0, hx⟩ := hR.tcb t ht
  rw [hk] at hk0; injection hk0 with hk0; injection hk0 with hk0; subst hk0
  refine hR.upd_tcb hP0 ht _ (fun b hb ⟨_, hnt⟩ => g b hb (fun hv => hnt (Or.inl (TF.of_val hfa.2 (by
      rw [hv, val_fault hta]))))) (Or.inr ⟨g _ (a_st hta).1 (by rw [val_st hta]; omega),
      g _ (a_blk hta).1 (by rw [val_blk hta]; omega)⟩) ?_
  have hreg : ∀ r, (regA t (regIdx r)).val ≠ t.val + 3376 := fun r => by
    rw [regA_val hta (regIdx_lt r)]; have := regIdx_lt r; omega
  refine ⟨?_, fun e he => ?_, fun n hn => ?_, fun e d h => ?_, fun e r d h => ?_, fun r h => ?_, fun r => ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g _ (a_st hta).1 (by rw [val_st hta]; omega)]; exact hx.st
  · rw [g _ (a_blk hta).1 (by rw [val_blk hta]; omega)]; exact hx.blkE e he
  · rw [g _ (a_blk hta).1 (by rw [val_blk hta]; omega)]; exact hx.blkN n hn
  · rw [g _ (a_badge hta).1 (by rw [val_badge hta]; omega), g _ (a_flags hta).1 (by rw [val_flags hta]; omega)]
    exact hx.send e d h
  · rw [g _ (a_reply hta).1 (by rw [val_reply hta]; omega)]; exact hx.recv e r d h
  · rw [g _ (a_reply hta).1 (by rw [val_reply hta]; omega)]; exact hx.reply r h
  · rw [g _ (a_reg hta r).1 (hreg r)]; exact hx.regs r
  · rw [g _ (a_prio hta).1 (by rw [val_prio hta]; omega)]; exact hx.prio
  · rw [rd_wr_eq hfa.1]; simp
  · rw [rd_wr_eq hfa.1]; simp
  · rw [g _ (a_bound hta).1 (by rw [val_bound hta]; omega)]; exact hx.bound
  · show FaultRel' _ _ _ _ _ _ _ none
    show L.mem (L.wr s (tFaultA t) 0#u64) (tFaultA t) = 0#u64
    exact rd_wr_eq hfa.1
  · rw [g _ (scA_aligned hta) (by rw [scA_val hta]; omega)]; exact hx.sc

end

/-! ## The scheduler relation across a TCB-field write -/

section Sched
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- A write to a TCB word that is no scheduler field keeps what `SchedRel`
reads. -/
theorem sagree_tcb_wr {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ) {t : U64} (ht : t ∈ T)
    {K : U64} (hK : K.val < 4096) (hK8 : K.val % 8 = 0) (hKs : ∀ K', SchedField K' → K'.val ≠ K.val) (v : U64) :
    SAgree st T C c s (L.wr s (core.num.U64.wrapping_add t K) v) := by
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hta := hc.tcbs t ht
  have hw := field_aligned hta hK hK8
  have hv := tfield_val hta hK
  have hko := hc.ksOut t ht
  have h1 := hc.node.align
  have h2 := hc.node.fits
  simp only [LawfulStore.nodeBase] at h1 h2
  refine ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun o ho h8 _ _ => rd_wr_ne hw (nodeAt_aligned hc.node ho h8)
    (Ne.symm (nodeAt_ne_tfield hc.node ho ht hta hK)), fun y hy K' hK' => ?_, ?_, ?_,
    fun sc hsc a ha hin => rd_wr_ne hw ha fun e => ?_⟩
  · obtain ⟨k1, k2, -⟩ := schedField_ok hK'
    refine rd_wr_ne hw (field_aligned (hc.tcbs y hy) k1 k2) fun e => ?_
    have := congrArg UScalar.val e
    rw [hv, tfield_val (hc.tcbs y hy) k1] at this
    have hKs' := hKs K' hK'
    have := (hc.tcbs y hy).align
    have := hta.align
    by_cases eyt : y = t
    · subst eyt; omega
    · have := val_ne_of_ne eyt; omega
  · have hal : Aligned (curDomA st s) := by
      unfold Aligned curDomA
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
      omega
    refine rd_wr_ne hw hal fun e => ?_
    have := congrArg UScalar.val e
    rw [hv] at this
    unfold curDomA at this
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits] at this
    omega
  · refine rd_wr_ne hw (dtA_aligned hc.node) fun e => ?_
    have := congrArg UScalar.val e
    rw [hv, dtA_val hc.node] at this
    omega
  · have := (hS.scOutIn hsc hin).2.2.1 t ht
    rw [← e, hv] at this; omega

/-- **The scheduler relation after clearing a TCB's fault.** -/
theorem fault_clear_sre {s : S} {σ : Fl4Spec.State Unit} (hS : SRE st N T C E R B c s σ) {t : U64} (ht : t ∈ T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) :
    SRE st N T C E R B c (L.wr s (tFaultA t) 0#u64) (updK σ t.bv (.tcb { x with tcbFault := none })) := by
  obtain ⟨Q, R0, hc, -⟩ := hS.1.lists
  have hta := hc.tcbs t ht
  have hK : (3376#u64 : U64).val < 4096 := by decide
  have ha := sagree_tcb_wr hS.1 ht (K := 3376#u64) hK (by decide) (fun K' h => by
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) 0#u64
  have hw : Aligned (tFaultA t) := (a_fault hta).1
  have hn : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      nodeW st (L.wr s (tFaultA t) 0#u64) c o = nodeW st s c o := fun o ho h8 => by
    unfold Fl4Proofs.P3.Sched.nodeW; rw [Sched.nodeAt_ksb (st := st) (L.ksb_wr _ _ _)]
    exact rd_wr_ne hw (nodeAt_aligned hc.node ho h8) (Ne.symm (nodeAt_ne_tfield hc.node ho ht hta hK))
  refine ⟨hS.1.of_sagreeE ha (hn _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))
    (hn _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])) hS.1.nodeNW hS.1.domNW hS.1.dtNW
    (SchedStep.updK_tcb hk rfl rfl rfl), hS.2.mono (L.ksb_wr _ _ _) (SzKeep.updK hk (fun _ _ h => by cases h))⟩

end Sched

section Top
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- **`IpcCore` for `SRT … SRE`.** -/
theorem ipcCore_top (hP : EPlaced T E R B) : IpcCore st N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)) where
  stableE s s' σ σ' h hW hK := ⟨h.1.stableE hW hK, h.2.1.stableE hP h.2.2 hW hK,
    h.2.2.mono hW.1 (SzKeep.epStep hK)⟩
  scheduleTcb s σ t hR _ h ht := by
    refine WP.spec_mono (WP.spec_and (WP.spec_and (schedule_tcb_refinesE s σ hR h.2.1 h.2.2 t ht)
      (schedule_tcb_cases s t)) (relTopI_schedule_tcb s σ h.2.1 h.1 t)) ?_
    rintro s' ⟨⟨⟨hF, hS'⟩, hc⟩, hT'⟩
    refine ⟨hF, hT', hS', h.2.2.mono ?_ (SzKeep.of_kheap (stsAct_kheap σ t.bv))⟩
    rcases hc with rfl | rfl
    · rfl
    · exact L.ksb_wr _ _ _

/-- **`RelTopI ∧ SRE` after clearing a TCB's fault.** -/
theorem fault_clear_top {s : S} {σ : Fl4Spec.State Unit} (hS : SRT st th cr N T C E R B c (SRE st N T C E R B c) s σ)
    {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) :
    SRT st th cr N T C E R B c (SRE st N T C E R B c) (L.wr s (tFaultA t) 0#u64)
      (updK σ t.bv (.tcb { x with tcbFault := none })) := by
  obtain ⟨Q, R0, hc, -⟩ := hS.2.1.lists
  have hta := hc.tcbs t ht
  refine ⟨hS.1.frame (writesIn_wr (a_fault hta).1) (fun a ha => Or.inl ⟨t, ht, ?_, ?_⟩)
    (fun a ha => NoBufW.tcb hc.tcbs ht (by rw [ha, val_fault hta]; omega) (by rw [ha, val_fault hta]; omega)
      (by rw [ha, val_fault hta]; omega)) ?_ rfl rfl
    (VsKeep.updK_tcb hk rfl),
    fault_clear_sre hS.2 ht hk⟩
  · rw [ha, val_fault hta]; omega
  · rw [ha, val_fault hta]; omega
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
        exact ⟨{ x with tcbFault := none }, by simp [updK], rfl⟩
      · exact ⟨y, by simp only [updK, Function.update_of_ne e]; exact hy, rfl⟩

end Top

/-! ## The scheduler facts the spec keeps -/

section Keep
open Fl4Spec

/-- What `RelIfBound` reads: the release queue, the time, the TCBs' SC
pointers and the SC objects. -/
def SKeep (σ σ' : State Unit) : Prop :=
  σ'.releaseQueue = σ.releaseQueue ∧ σ'.curTime = σ.curTime ∧
  (∀ p y, σ'.kheap p = some (.tcb y) → ∃ x, σ.kheap p = some (.tcb x) ∧ x.tcbSchedContext = y.tcbSchedContext) ∧
  (∀ p y n, σ'.kheap p = some (.schedContext y n) → σ.kheap p = some (.schedContext y n))

theorem SKeep.trans {σ1 σ2 σ3 : State Unit} (h1 : SKeep σ1 σ2) (h2 : SKeep σ2 σ3) : SKeep σ1 σ3 := by
  refine ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, fun p y hy => ?_, fun p y n hy => h1.2.2.2 _ _ _ (h2.2.2.2 _ _ _ hy)⟩
  obtain ⟨x2, hx2, e2⟩ := h2.2.2.1 p y hy
  obtain ⟨x1, hx1, e1⟩ := h1.2.2.1 p x2 hx2
  exact ⟨x1, hx1, e1.trans e2⟩

theorem SKeep.stsAct (σ : State Unit) (t : ObjRef) : SKeep σ (stsAct σ t) := by
  refine ⟨?_, ?_, fun p y hy => ⟨y, by rw [stsAct_kheap] at hy; exact hy, rfl⟩,
    fun p y n hy => by rw [stsAct_kheap] at hy; exact hy⟩ <;> (unfold Notif.stsAct; split <;> rfl)

theorem SKeep.updK {σ : State Unit} {p : ObjRef} {o : KernelObject}
    (h1 : ∀ y, o = .tcb y → ∃ x, σ.kheap p = some (.tcb x) ∧ x.tcbSchedContext = y.tcbSchedContext)
    (h2 : ∀ y n, o ≠ .schedContext y n) : SKeep σ (Notif.updK σ p o) := by
  refine ⟨rfl, rfl, fun q y hy => ?_, fun q y n hy => ?_⟩
  · by_cases e : q = p
    · subst e; simp [Notif.updK] at hy; exact h1 y hy
    · exact ⟨y, by simpa [Notif.updK, e] using hy, rfl⟩
  · by_cases e : q = p
    · subst e; simp [Notif.updK] at hy; exact absurd hy (h2 y n)
    · simpa [Notif.updK, e] using hy

theorem RelIfBound.of_keep {σ σ' : State Unit} {t : ObjRef} (h : RelIfBound σ t) (hk : SKeep σ σ') :
    RelIfBound σ' t := by
  intro y scp z n hy hscp hz ha hnq
  obtain ⟨x, hx, e⟩ := hk.2.2.1 _ _ hy
  have := h x scp z n hx (e.trans hscp) (hk.2.2.2 _ _ _ hz) ha (hk.1 ▸ hnq)
  unfold released at *; rw [hk.2.1]; exact this

end Keep

/-! ## `cancel_ipc` of a receiver -/

section Cancel
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {N T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

/-- **What `cancel_ipc` of a receiver needs of the state** (l4v `valid_objs`
and `sym_refs` for the thread, and `valid_sched` for its SC): the spec's
`CancelOK`, the endpoint in the ghost set, and `RelIfBound`. -/
structure CancelRecvHyp (E : Set U64) (m : U64 → U64) (σ : Fl4Spec.State Unit) (t : U64) (x : Fl4Spec.Tcb) :
    Prop where
  ok : CancelOK σ t.bv x
  ep : m (tBlockA t) ∈ E
  rib : RelIfBound σ t.bv

set_option maxHeartbeats 4000000 in
/-- **`cancel_ipc` of a thread blocked on a receive** refines l4v
`cancel_ipc` on the merged relation. -/
theorem cancel_ipc_recvI (hH : IpcCore st N T E R B SR)
    (hF : ∀ s σ (t : U64) (x : Fl4Spec.Tcb), SR s σ → t ∈ T → σ.kheap t.bv = some (.tcb x) →
      SR (L.wr s (tFaultA t) 0#u64) (updK σ t.bv (.tcb { x with tcbFault := none })))
    (hP0 : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : IpcRel N T E R B (L.mem s) σ)
    (hSR : SR s σ) {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x))
    (hrb : Fl4Spec.receiveBlocked x.tcbState = true) (hC : CancelRecvHyp E (L.mem s) σ t x) :
    ipc.cancel_ipc st ar s a t ⦃ r => ∃ σ' x', Fl4Spec.cancelIpc (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      IpcRel N T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ∧ σ'.kheap t.bv = some (.tcb x') ∧
      x'.tcbState = .inactive ∧ RelIfBound σ' t.bv ⦄ := by
  have hP := hP0.e
  have hta := hP.tcb t ht
  obtain ⟨e, ro, d, hst⟩ : ∃ e ro d, x.tcbState = .blockedOnReceive e ro d := by
    cases h : x.tcbState <;> simp [h, Fl4Spec.receiveBlocked] at hrb
    exact ⟨_, _, _, rfl⟩
  obtain ⟨x0, hk0, hx⟩ := hR.tcb t ht
  rw [hk] at hk0; injection hk0 with hk0; injection hk0 with hk0; subst hk0
  have hevb : (L.mem s (tBlockA t)).bv = e := hx.blkE e (by simp [Fl4Spec.epBlocked, hst])
  subst hevb
  set ev := L.mem s (tBlockA t) with hev
  obtain ⟨z, hkz, hqz⟩ := hC.ok.2.1 _ ro d hst
  have heE : ev ∈ E := hC.ep
  have hrec := hx.recv _ ro d hst
  -- clearing the fault
  set s1 := L.wr s (tFaultA t) 0#u64 with hs1
  set x1 : Fl4Spec.Tcb := { x with tcbFault := none } with hx1
  set σ1 := updK σ t.bv (.tcb x1) with hσ1
  have hR1 : IpcRel N T E R B (L.mem s1) σ1 := fault_clear_ipc hP0 hR ht hk
  have hS1 : SR s1 σ1 := hF s σ t x hSR ht hk
  have hfa := a_fault hta
  have g : ∀ w, Aligned w → w.val ≠ t.val + 3376 → L.mem s1 w = L.mem s w :=
    fun w hw hne => rd_wr_ne hfa.1 hw (fun e => hne (by rw [← e, val_fault hta]))
  have hk1 : σ1.kheap t.bv = some (.tcb x1) := by simp [hσ1, updK]
  have hte : t.bv ≠ ev.bv := by intro h; rw [h, hkz] at hk; cases hk
  have hkz1 : σ1.kheap ev.bv = some (.endpoint z) := by simp [hσ1, updK, Ne.symm hte, hkz]
  have hst1 : x1.tcbState = .blockedOnReceive ev.bv ro d := hst
  have hts : Fl4Spec.threadSet (Z := Unit) (fun tcb => { tcb with tcbFault := none }) t.bv σ =
      ({((), σ1)}, False) := threadSet_eq _ hk
  have hw3 : L.mem s1 (P1.stA t) = sched.TS_BLOCKED_ON_RECV := by
    rw [P1.stA_eq, ← tStA_eq, g _ (a_st hta).1 (by rw [val_st hta]; omega)]
    have h3 := hx.st
    rw [hst] at h3
    apply UScalar.eq_of_val_eq
    rw [h3, tsVals.2.2.1]; rfl
  have hb1 : L.mem s1 (tBlockA t) = ev := g _ (a_blk hta).1 (by rw [val_blk hta]; omega)
  have hr1 : L.mem s1 (tReplyA t) = L.mem s (tReplyA t) := g _ (a_reply hta).1 (by rw [val_reply hta]; omega)
  have hRS : sched.TS_BLOCKED_ON_RECV ≠ sched.TS_BLOCKED_ON_SEND := by
    rw [tsVals.2.2.1, tsVals.2.2.2.1]; decide
  -- the spec's prefix
  have hspec0 : ∀ (σ' : Fl4Spec.State Unit),
      Fl4Spec.blockedCancelIpc (Z := Unit) (.blockedOnReceive ev.bv ro d) t.bv ro σ1 = ({((), σ')}, False) →
      Fl4Spec.cancelIpc (Z := Unit) t.bv σ = ({((), σ')}, False) := by
    intro σ' h
    unfold Fl4Spec.cancelIpc
    rw [nd_bind_one (getThreadState_eq hk), nd_bind_one hts, hst]
    exact h
  unfold ipc.cancel_ipc faults.clear_fault
  step with Fl4Proofs.P1.obj.Tcb.set_fault_type.spec as ⟨s1', hs1'⟩
  have e1 : s1' = s1 := by rw [hs1']; unfold fl4_abi.consts.fault.NullFault; rfl
  subst e1
  step with Fl4Proofs.P1.obj.Tcb.state.spec as ⟨w, hw⟩
  rw [hw, hw3, if_neg hRS, if_pos rfl]
  simp only [↓reduceIte]
  step with Fl4Proofs.P1.obj.Tcb.block_obj.spec as ⟨ep, hep⟩
  have hep' : ep = ev := by rw [hep]; exact hb1
  subst hep'
  refine WP.spec_bind (ep_dequeue_c hH hP0 hP s1 σ1 hR1.toE (IpcRel.toSRN hR1 hS1) heE hkz1 hqz) ?_
  rintro s2 ⟨hdq, hR2, hS2, hA2⟩
  set σ2 := updK σ1 ev.bv (.endpoint (epDeq z t.bv)) with hσ2
  have hk2 : σ2.kheap t.bv = some (.tcb x1) := by simp [hσ2, updK, hte, hk1]
  have hb2 : L.mem s2 (tBlockA t) = ev := (hA2 _ (a_blk hta).1 ⟨t, ht, (a_blk hta).2⟩).trans hb1
  have hr2 : L.mem s2 (tReplyA t) = L.mem s (tReplyA t) :=
    (hA2 _ (a_reply hta).1 ⟨t, ht, (a_reply hta).2⟩).trans hr1
  have hq2 : ∀ e ∈ E, ∀ z', σ2.kheap e.bv = some (.endpoint z') → t.bv ∉ z'.epQueue :=
    dequeued_not_queued hR2 heE hb2 (x := epDeq z t.bv) (by simp [hσ2, updK]) (epDeq_not_mem _)
  have hK2 : SKeep σ σ2 := (SKeep.updK (o := .tcb x1) (fun y h => ⟨x, hk, by cases h; rfl⟩)
    (fun _ _ h => by cases h)).trans (SKeep.updK (fun _ h => by cases h) (fun _ _ h => by cases h))
  step with Fl4Proofs.P1.obj.Tcb.reply_obj.spec as ⟨i, hi⟩
  have hi' : i = L.mem s (tReplyA t) := by rw [hi]; exact hr2
  split
  · -- a reply object
    rename_i hnz
    have hi0 : i ≠ 0#u64 := by simpa using hnz
    have hro : ro = some i.bv := by rw [← hrec.1, ← hi', optRef_ne hi0]
    subst hro
    have hiR : i ∈ R := by rw [hi']; exact hrec.2 (by simp)
    obtain ⟨xr, hkr, hback⟩ := hC.ok.2.2.1 _ i.bv d hst
    have hit : i.bv ≠ t.bv := by intro h; rw [h, hk] at hkr; cases hkr
    have hie : i.bv ≠ ev.bv := by intro h; rw [h, hkz] at hkr; cases hkr
    have hkr2 : σ2.kheap i.bv = some (.reply xr) := by simp [hσ2, hσ1, updK, hit, hie, hkr]
    refine WP.spec_bind (reply_unlink_c hH hP0 hP s2 σ2 hR2 hS2 ht hk2 hst1 hiR hkr2 hback hq2) ?_
    rintro s3 ⟨e3, hR3, hS3⟩
    set x3 : Fl4Spec.Tcb := { x1 with tcbState := .inactive } with hx3
    set σ3 := stsAct (updK (updK σ2 i.bv (.reply { xr with replyTcb := none })) t.bv (.tcb x3)) t.bv with hσ3
    have hk3 : σ3.kheap t.bv = some (.tcb x3) := by simp [hσ3, stsAct_kheap, updK]
    have hq3 : ∀ e ∈ E, ∀ z', σ3.kheap e.bv = some (.endpoint z') → t.bv ∉ z'.epQueue := by
      intro e he z' hz'
      have h1 : e.bv ≠ t.bv := by intro h; rw [h, hk3] at hz'; cases hz'
      have h2 : e.bv ≠ i.bv := by
        intro h; rw [h] at hz'; simp [hσ3, stsAct_kheap, updK, hit] at hz'
      refine hq2 e he z' ?_
      simpa [hσ3, stsAct_kheap, updK, h1, h2] using hz'
    refine WP.spec_bind (set_thread_state_c hH hP0 hP s3 σ3 hR3 hS3 ht hk3 hq3 (by simp [hx3, tsCode])
      .inactive (by simp [tsCode]) sched.TS_INACTIVE (by unfold sched.TS_INACTIVE; rfl)) ?_
    rintro s4 ⟨hR4, hS4⟩
    simp only [WP.spec_ok]
    have hK3 : SKeep σ2 σ3 := ((SKeep.updK (fun _ h => by cases h) (fun _ _ h => by cases h)).trans
      (SKeep.updK (o := .tcb x3) (fun y h => ⟨x1, by simp [updK, Ne.symm hit, hk2], by cases h; rfl⟩)
        (fun _ _ h => by cases h))).trans (SKeep.stsAct _ _)
    refine ⟨_, { x3 with tcbState := .inactive }, hspec0 _ ?_, (IpcRel.ofSRN hR4 hS4).1,
      (IpcRel.ofSRN hR4 hS4).2, by simp [stsAct_kheap, updK], rfl, ?_⟩
    · unfold Fl4Spec.blockedCancelIpc Fl4Spec.getBlockingObject
      rw [nd_bind_one (show Fl4Spec.NonDet.assertOpt (σ := Fl4Spec.State Unit)
        (Fl4Spec.epBlocked (.blockedOnReceive ev.bv (some i.bv) d)) σ1 = ({(ev.bv, σ1)}, False) from rfl),
        nd_bind_one hdq]
      dsimp only
      rw [nd_bind_one e3, Notif.setThreadState_eq _ hk3]
    · refine Ipc.RelIfBound.of_keep hC.rib ((hK2.trans hK3).trans ?_)
      exact (SKeep.updK (o := .tcb { x3 with tcbState := .inactive }) (fun y h => ⟨x3, hk3, by cases h; rfl⟩)
        (fun _ _ h => by cases h)).trans (SKeep.stsAct _ _)
  · -- no reply object
    rename_i hz0
    have hi0 : i = 0#u64 := by apply UScalar.eq_of_val_eq; simpa using hz0
    have hro : ro = none := by rw [← hrec.1, ← hi', hi0, optRef_zero]
    subst hro
    simp only [bind_ok]
    refine WP.spec_bind (set_thread_state_c hH hP0 hP s2 σ2 hR2 hS2 ht hk2 hq2 (by simp [hst1, tsCode])
      .inactive (by simp [tsCode]) sched.TS_INACTIVE (by unfold sched.TS_INACTIVE; rfl)) ?_
    rintro s4 ⟨hR4, hS4⟩
    simp only [WP.spec_ok]
    refine ⟨_, { x1 with tcbState := .inactive }, hspec0 _ ?_, (IpcRel.ofSRN hR4 hS4).1,
      (IpcRel.ofSRN hR4 hS4).2, by simp [stsAct_kheap, updK], rfl, ?_⟩
    · unfold Fl4Spec.blockedCancelIpc Fl4Spec.getBlockingObject
      rw [nd_bind_one (show Fl4Spec.NonDet.assertOpt (σ := Fl4Spec.State Unit)
        (Fl4Spec.epBlocked (.blockedOnReceive ev.bv none d)) σ1 = ({(ev.bv, σ1)}, False) from rfl),
        nd_bind_one hdq]
      dsimp only
      rw [Notif.setThreadState_eq _ hk2]
    · refine Ipc.RelIfBound.of_keep hC.rib (hK2.trans ?_)
      exact (SKeep.updK (o := .tcb { x1 with tcbState := .inactive }) (fun y h => ⟨x1, hk2, by cases h; rfl⟩)
        (fun _ _ h => by cases h)).trans (SKeep.stsAct _ _)

/-- **The `cancelIpc` field of `IpcSchedHyps` for `SRT … SRE`**, from
`CancelRecvHyp` for every receiver of a related state. -/
theorem cancelIpc_top {C : Set U64} {c : U64} (hP0 : IPlaced N T E R B)
    (hX : ∀ s σ (t : U64) (x : Fl4Spec.Tcb), IpcRel N T E R B (L.mem s) σ →
      SRT st th cr N T C E R B c (SRE st N T C E R B c) s σ → t ∈ T → σ.kheap t.bv = some (.tcb x) →
      Fl4Spec.receiveBlocked x.tcbState = true → CancelRecvHyp E (L.mem s) σ t x) :
    ∀ s (a : A) σ (t : U64) (x : Fl4Spec.Tcb), IpcRel N T E R B (L.mem s) σ →
      SRT st th cr N T C E R B c (SRE st N T C E R B c) s σ → t ∈ T →
      σ.kheap t.bv = some (.tcb x) → Fl4Spec.receiveBlocked x.tcbState = true →
      ipc.cancel_ipc st ar s a t ⦃ r => ∃ σ' x', Fl4Spec.cancelIpc (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
        IpcRel N T E R B (L.mem r.1) σ' ∧ SRT st th cr N T C E R B c (SRE st N T C E R B c) r.1 σ' ∧
        σ'.kheap t.bv = some (.tcb x') ∧ x'.tcbState = .inactive ∧ RelIfBound σ' t.bv ⦄ :=
  fun s a σ t x hR hS ht hk hrb => cancel_ipc_recvI (ipcCore_top hP0.e)
    (fun _ _ _ _ h ht hk => fault_clear_top h ht hk) hP0 s a σ hR hS ht hk hrb (hX s σ t x hR hS ht hk hrb)

end Cancel

end

end Fl4Proofs.P3.Ipc
