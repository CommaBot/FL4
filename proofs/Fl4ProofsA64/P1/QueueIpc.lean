-- AArch64 port of Fl4Proofs.P1.QueueIpc (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
/-
P1: the non-blocking ends of IPC: the message transfer (`do_ipc_transfer`,
taken as the hypothesis `XferOK`, proved in QueueXfer),
`reply_push` with SC donation, `receive_from_sender`, the `send_ipc` branch
on a receiving endpoint and `complete_signal`; then the whole `send_ipc` and
`receive_ipc`.

a64 named premise: **[J] `RunVcpuInv`** (`RunVcpu`; `hRV` of `endpoint.send_ipc.ipc`,
`endpoint.receive_from_sender.ipc`, `notification.complete_signal.ipc`, and at the `RecvPre` states in `endpoint.receive_ipc.ipc`). AArch64's
`migrate_tcb` (the donation's last step) also flushes a VCPU the thread runs and writes its `OWNER_CPU`; under
`RunVcpuInv` the donation's receiver, blocked on the endpoint (`send_ipc`) or not in `TS_RUNNING_VM`
(`receive_ipc`'s receiver, the caller-level `hvm`), has `RUN_VCPU` 0, so that branch writes nothing
(`migrate_vcpu_idle`). The lemmas below the entry points carry the derived `RUN_VCPU` 0 fact (`hrv`, `hdrv`,
`hcrv`) as ordinary hypotheses discharged by their callers. Other a64 edits: `--sub 128=136` on the node
predicates; `ipi_all` takes either word of the two-word `IPI_PENDING`; AArch64's `remote_tcb_stall` makes up
to two `remote_reschedule`s (`IpiW`, `smp.remote_reschedule.ipi`, `smp.remote_tcb_stall.ipi`);
`sched.reschedule_required.fldX` (TCB fields outside the queue links are kept).
-/
import Fl4ProofsA64.P1.QueueBlock
import Fl4ProofsA64.P1.QueueBudget2
import Fl4ProofsA64.P1.QueueTimerW
import Fl4ProofsA64.P1.RunVcpu
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}

/-! ## The message transfer as an opaque write -/

/-- What a message transfer may write: the user context of the TCBs (fields
below `STATE`) and the user-memory words `U`. -/
def XferFoot (T U : Set U64) (b : U64) : Prop :=
  (∃ y ∈ T, ∃ K : U64, K.val < 3328 ∧ K.val % 8 = 0 ∧ b = core.num.U64.wrapping_add y K) ∨ b ∈ U

/-- The user-memory words lie outside the TCBs, nodes, the other kernel
objects and the heap's endpoints and notifications. -/
def UserOK (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (U : Set U64) (s : S) :
    Prop :=
  ∀ b ∈ U, OutsideObjs st T Cs s b ∧ b ∉ Ω ∧
    ∀ e, (H e = some .ep ∨ H e = some .ntfn) → b.val + 8 ≤ e.val ∨ e.val + 16 ≤ b.val

theorem UserOK.ksb {U : Set U64} {s s' : S} (h : UserOK st T Cs Ω H U s) (hk : L.ksb s' = L.ksb s) :
    UserOK st T Cs Ω H U s' := fun b hb => ⟨(h b hb).1.ksb hk, (h b hb).2⟩

/-- What an `XferFoot` write leaves alone. -/
theorem xfer_keep {X : Set U64} {U : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hU : UserOK st T Cs Ω H U s)
    (hw : WritesIn st s s' (XferFoot T U)) :
    (∀ y ∈ T, ∀ K : U64, 3328 ≤ K.val → K.val < 4096 → K.val % 8 = 0 →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
    (∀ a ∈ Ω, L.mem s' a = L.mem s a) ∧
    (∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o)) ∧
    (∀ e, (H e = some .ep ∨ H e = some .ntfn) → EpPlaced T e →
      L.mem s' (epHeadA e) = L.mem s (epHeadA e) ∧ L.mem s' (epTSA e) = L.mem s (epTSA e)) := by
  have hT := h.tcbs
  refine ⟨fun y hy K h1 h2 h3 => ?_, fun a ha => ?_, fun c hc o ho h8 => ?_, fun e he hE => ?_⟩
  · refine hw.mem_eq (field_aligned (hT y hy) h2 h3) ?_
    rintro (⟨y', hy', K', hK', -, e⟩ | hb)
    · exact field_ne (hT y hy) (hT y' hy') h2 (by omega) (fun _ => by omega) e
    · exact out_ne_field (hU _ hb).1 hy (hT y hy) h2 rfl
  · have ho := h.omega a ha
    refine hw.mem_eq ho.1 ?_
    rintro (⟨y', hy', K', hK', -, e⟩ | hb)
    · exact out_ne_field ho hy' (hT y' hy') (by omega) (congrArg UScalar.val e).symm
    · exact (hU _ hb).2.1 ha
  · have hN := h.nodes c hc
    refine hw.mem_eq (nodeAt_aligned hN ho h8) ?_
    rintro (⟨y', hy', K', hK', -, e⟩ | hb)
    · exact node_ne_field hN ho hy' (hT y' hy') (by omega) e
    · exact out_ne_node (hU _ hb).1 hc hN ho rfl
  · obtain ⟨a1, a2⟩ := ep_aligned hE
    have k : ∀ a, Aligned a → (a.val = e.val ∨ a.val = e.val + 8) → L.mem s' a = L.mem s a := by
      intro a ha hv
      refine hw.mem_eq ha ?_
      rintro (⟨y', hy', K', hK', -, e'⟩ | hb)
      · have := congrArg UScalar.val e'
        rw [field_val (hT y' hy') (by omega)] at this
        have := hE.disj y' hy'; omega
      · have := (hU _ hb).2.2 e he
        omega
    exact ⟨k _ a1 (Or.inl epHeadA_val), k _ a2 (Or.inr (epTSA_val hE))⟩

/-- The endpoint queues after a change that keeps the TCBs' queue fields
and the heap endpoints' words. -/
theorem EpsOK.agreeE {Cs X : Set U64} {s s' : S} (h : EpsOK st T Cs Ω H X s) (hk : L.ksb s' = L.ksb s)
    (hsb : ∀ y ∈ T, L.mem s' (stA y) = L.mem s (stA y) ∧ L.mem s' (blockA y) = L.mem s (blockA y))
    (hEp : ∀ y ∈ T, L.mem s' (nextA .Ep y) = L.mem s (nextA .Ep y) ∧ L.mem s' (prevA .Ep y) = L.mem s (prevA .Ep y))
    (hout : ∀ e, (H e = some .ep ∨ H e = some .ntfn) → EpPlaced T e →
      L.mem s' (epHeadA e) = L.mem s (epHeadA e) ∧ L.mem s' (epTSA e) = L.mem s (epTSA e)) :
    EpsOK st T Cs Ω H X s' := by
  obtain ⟨E, EQ, h1, h2, h5, h3, h4, h6⟩ := h
  have hnb : ∀ c, L.nodeBase s' c = L.nodeBase s c := fun c => by simp [LawfulStore.nodeBase, hk]
  have hH : ∀ e ∈ E, H e = some .ep ∨ H e = some .ntfn := fun e he => (h6.2.2.1 e).1 he
  refine ⟨E, EQ, fun e he => ?_, h2, h5, fun e he y hy => ?_, fun y hy hyX hb => ?_,
    h6.agree (fun y hy => Or.inl hy) (fun y hy _ _ => hsb y hy) (fun _ _ _ hy => hy)
      (fun e he y hy => (hsb y (((h1 e he).2.2).mem y hy)).1) (fun e he _ => ?_)
      (fun e he h0 => Or.inl ⟨h0, ?_⟩)⟩
  · obtain ⟨hE, hEN, hq⟩ := h1 e he
    obtain ⟨o1, o2⟩ := hout e (hH e he) hE
    have eq : L.epQ s' e = L.epQ s e := by simp only [LawfulStore.epQ, o1, o2]
    refine ⟨hE, ⟨fun c hc => by rw [hnb]; exact hEN.1 c hc, by rw [hk]; exact hEN.2⟩, ?_⟩
    rw [eq]
    exact ⟨hq.nodup, hq.mem, hq.head, hq.last, hq.seg.congr fun y hy =>
      ⟨(hEp y (hq.mem y hy)).2, (hEp y (hq.mem y hy)).1⟩⟩
  · have hyT := ((h1 e he).2.2).mem y hy
    rw [(hsb y hyT).1, (hsb y hyT).2]; exact h3 e he y hy
  · rw [(hsb y hy).1] at hb
    rw [(hsb y hy).2]; exact h4 y hy hyX hb
  · obtain ⟨hE, -, -⟩ := h1 e he
    simp only [LawfulStore.epState, (hout e (hH e he) hE).2]
  · obtain ⟨hE, -, -⟩ := h1 e he
    simp only [LawfulStore.epState, (hout e (hH e he) hE).2]

/-- The invariants after an `XferFoot` write. -/
theorem xfer_all {X : Set U64} {U : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hU : UserOK st T Cs Ω H U s)
    (hw : WritesIn st s s' (XferFoot T U)) :
    SchedQueuesInvX st T Cs Ω H X s' Q R ∧ BoundInv st T Ac s' ∧ XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧
      SCsOK st T Ω Sg Scs Z Ac s' ∧ SgOK st Ω Sg s' ∧ L.actionW s' = L.actionW s ∧ L.curW s' = L.curW s ∧
      L.idleW s' = L.idleW s ∧ L.cscW s' = L.cscW s ∧
      (∀ y ∈ T, ∀ K : U64, 3328 ≤ K.val → K.val < 4096 → K.val % 8 = 0 →
        L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ a ∈ Ω, L.mem s' a = L.mem s a) := by
  obtain ⟨f1, f2, f3, f4⟩ := xfer_keep h hU hw
  have hT := h.tcbs
  have nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem s' (L.nodeAt s' (L.cpu s') o) = L.mem s (L.nodeAt s (L.cpu s) o) := fun o ho h8 => by
    rw [hw.2.1, nodeAt_of_ksb hw.1]; exact f3 _ h.cur o ho h8
  have ea : L.actionW s' = L.actionW s := nd _ (by rw [act_val]; omega) (by rw [act_val])
  have ec : L.curW s' = L.curW s := nd _ (by rw [curth0]; omega) (by rw [curth0])
  have ei : L.idleW s' = L.idleW s := nd _ (by rw [idle8]; omega) (by rw [idle8])
  have ecs : L.cscW s' = L.cscW s := nd _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have F : ∀ y ∈ T, ∀ K : U64, 3328 ≤ K.val → K.val < 4096 → K.val % 8 = 0 →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := f1
  have scf : ∀ y ∈ T, L.mem s' (scA y) = L.mem s (scA y) := fun y hy => by
    rw [scA_eq]; exact F y hy _ (by simp) (by simp) (by simp)
  have iqf : ∀ y ∈ T, L.mem s' (inqA y) = L.mem s (inqA y) := fun y hy => by
    rw [inqA_eq]; exact F y hy _ (by simp) (by simp) (by simp)
  have stf : ∀ y ∈ T, L.mem s' (stA y) = L.mem s (stA y) := fun y hy => by
    rw [stA_eq]; exact F y hy _ (by simp) (by simp) (by simp)
  have blf : ∀ y ∈ T, L.mem s' (blockA y) = L.mem s (blockA y) := fun y hy => by
    rw [blockA_eq]; exact F y hy _ (by simp) (by simp) (by simp)
  have rpf : ∀ y ∈ T, L.mem s' (replyA y) = L.mem s (replyA y) := fun y hy =>
    F y hy _ (by simp) (by simp) (by simp)
  obtain ⟨hrΩ, hcΩ⟩ := objs_omega hX.1 hSg.sub
  have hsb : ∀ y ∈ T, L.mem s' (stA y) = L.mem s (stA y) ∧ L.mem s' (blockA y) = L.mem s (blockA y) :=
    fun y hy => ⟨stf y hy, blf y hy⟩
  refine ⟨inv_of_agree h hw.1 hw.2.1 (fun y hy => ⟨?_, ?_⟩) (fun c hc o h1 h2 _ => f3 c hc o h1 h2)
    iqf (fun y hy => F y hy _ (by simp) (by simp) (by simp))
    (fun y hy => Or.inl (F y hy _ (by simp) (by simp) (by simp))) (by rw [ea]; exact h.action) hsb
    (by rw [ea]; intro haT; rw [stf _ haT]; exact h.actOK haT)
    (h.eps.agreeE hw.1 hsb (fun y hy => ⟨?_, ?_⟩) f4)
    (by rw [show L.mem s' (L.nodeAt s' (L.cpu s') layout.node.CUR_THREAD) = L.curW s' from rfl, ec]; exact h.curT)
    (by rw [show L.mem s' (L.nodeAt s' (L.cpu s') layout.node.IDLE_THREAD) = L.idleW s' from rfl, ei]; exact h.idleT),
    hB.keep scf iqf ea ec ei stf h.curT h.idleT,
    hX.keep (fun r hr => ⟨f2 _ (hrΩ r hr).1, f2 _ (hrΩ r hr).2.1, f2 _ (hrΩ r hr).2.2⟩)
      (fun c hc => ⟨f2 _ (hcΩ c hc).1, f2 _ (hcΩ c hc).2.1⟩) scf rpf stf (by rw [ecs]; exact hX.2.2.cur)
      (fun c hc => f2 _ (hSg.sub _ (hX.1.repW c hc)))
      (fun y hy => F y hy _ (by simp) (by simp) (by simp)) (fun n hn => f2 _ (hSg.sub _ (hX.1.ntW n hn)))
      (hX.tn (TmFr.mk0 ⟨hw.1, fun y hy K a b c => f1 y hy K (by omega) (by omega) c, fun c hc o ho => f3 c hc o (by omega) (by omega),
        fun n hn => f2 _ (hSg.sub _ (hX.1.ntB n hn).2)⟩)) (fun c hc => f2 _ (hSg.sub _ (hX.1.snW c hc)))
      (fun y hy => F y hy _ (by simp) (by simp) (by simp)) (fun c hc => f2 _ (hSg.sub _ (hX.1.syW c hc)))
      (fun c hc => f2 _ (hcΩ c hc).2.2.1) ei (fun y hy => F y hy _ (by simp) (by simp) (by simp)),
    SCsOK.keep hS hX hw.1 scf ecs (fun c hc => ⟨f2 _ (hcΩ c hc).2.2.1, f2 _ (hcΩ c hc).2.2.2.1,
      f2 _ (hcΩ c hc).2.2.2.2⟩) (fun c hc => f2 _ (spor_omega hX.1 hc)) (fun c hc => f2 _ (hSg.sub _ (hX.1.repW c hc))),
    ⟨hSg.sub, fun b hb => by rw [hw.1]; exact hSg.ks b hb, fun o h1 h2 => by rw [hw.1]; exact hSg.ksΩ o h1 h2⟩,
    ea, ec, ei, ecs, F, f2⟩
  · rw [nextA_eq']; exact F y hy _ (by simp [nextOff]) (by simp [nextOff]) (by simp [nextOff])
  · rw [prevA_eq']; exact F y hy _ (by simp [prevOff]) (by simp [prevOff]) (by simp [prevOff])
  · rw [nextA_eq']; exact F y hy _ (by simp [nextOff]) (by simp [nextOff]) (by simp [nextOff])
  · rw [prevA_eq']; exact F y hy _ (by simp [prevOff]) (by simp [prevOff]) (by simp [prevOff])

/-! ## Affinity writes -/

theorem inv_of_agree_aff {Cs : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    {X X' : Set U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hk : L.ksb s' = L.ksb s) (hcpu : L.cpu s' = L.cpu s)
    (hlink : ∀ y ∈ T, L.mem s' (nextA .Sched y) = L.mem s (nextA .Sched y) ∧
      L.mem s' (prevA .Sched y) = L.mem s (prevA .Sched y))
    (hnode : ∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → (o.val = 64 ∨ o.val = 72 ∨ 136 ≤ o.val) →  -- a64: 128->136
      L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o))
    (hinq : ∀ y ∈ T, L.mem s' (inqA y) = L.mem s (inqA y))
    (haff : ∀ y ∈ T, L.mem s' (affA y) = L.mem s (affA y) ∨
      ((L.mem s (inqA y) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s (inqA y) &&& sched.Q_RELEASE) = 0#u64 ∧
        L.mem s' (affA y) ∈ Cs))
    (hprio : ∀ y ∈ T, L.mem s' (prioA y) = L.mem s (prioA y) ∨
      ((L.mem s (inqA y) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s' (prioA y)).val < 256))
    (hact : L.actionW s' = 0#u64 ∨ L.actionW s' = 1#u64 ∨ L.actionW s' ∈ T)
    (hsb : ∀ y ∈ T, L.mem s' (stA y) = L.mem s (stA y) ∧ L.mem s' (blockA y) = L.mem s (blockA y))
    (hact2 : L.actionW s' ∈ T → Runnable (L.mem s' (stA (L.actionW s'))) ∧ ∀ c ∈ Cs, L.actionW s' ∉ R c)
    (heps : EpsOK st T Cs Ω H X' s')
    (hcurT : L.mem s' (L.nodeAt s' (L.cpu s') layout.node.CUR_THREAD) ∈ T)
    (hidleT : L.mem s' (L.nodeAt s' (L.cpu s') layout.node.IDLE_THREAD) ∈ T) :
    SchedQueuesInvX st T Cs Ω H X' s' Q R := by
  have hT := h.tcbs
  have hn : ∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → (o.val = 64 ∨ o.val = 72 ∨ 136 ≤ o.val) →  -- a64: 128->136
      L.mem s' (L.nodeAt s' c o) = L.mem s (L.nodeAt s c o) := by
    intro c hc o h1 h2 h3; rw [nodeAt_of_ksb hk]; exact hnode c hc o h1 h2 h3
  have hle : ∀ y ∈ T, ∀ c ∈ Cs, ∀ p : U64, p.val < 256 → y ∈ Q c p → L.mem s' (prioA y) = L.mem s (prioA y) := by
    intro y hy c hc p hp hq
    rcases hprio y hy with e | ⟨h0, -⟩
    · exact e
    · exact absurd hq (h.notQ hy h0 hc hp)
  have hrel : ∀ {q xs}, QueueRel (L.mem s) T .Sched q xs → QueueRel (L.mem s') T .Sched q xs := fun hq =>
    ⟨hq.nodup, hq.mem, hq.head, hq.last, hq.seg.congr fun y hy =>
      ⟨(hlink y (hq.mem y hy)).2, (hlink y (hq.mem y hy)).1⟩⟩
  have hpr : ∀ y ∈ T, (L.mem s' (prioA y)).val < 256 := fun y hy => by
    rcases hprio y hy with e | ⟨-, hlt⟩
    · rw [e]; exact h.prio y hy
    · exact hlt
  refine ⟨hT, fun c hc => (h.nodes c hc).ksb hk, hcpu ▸ h.cur, fun y hy => by
      rcases haff y hy with e | ⟨-, -, hc⟩
      · rw [e]; exact h.aff y hy
      · exact hc,
    fun y hy => ?_, fun c hc => ?_, fun c hc => ?_, ?_, ?_, ?_, ?_, ?_, hact,
    fun c hc p hp y hy => by rw [(hsb y (h.memT hc hp hy)).1]; exact h.runQ c hc p hp y hy,
    fun c hc y hy => by rw [(hsb y (h.memTR hc hy)).1]; exact h.runR c hc y hy,
    hact2, heps, hcurT, hidleT, by rw [hk]; exact h.ksOut,
    fun a ha => (h.omega a ha).ksb hk⟩
  · rcases hprio y hy with e | ⟨-, hlt⟩
    · rw [e]; exact h.prio y hy
    · exact hlt
  · have hNc := h.nodes c hc
    have hv : ViewsEq st s s' c := by
      refine ⟨fun p hp => ?_, ?_, fun g hg => ?_⟩
      · simp only [LawfulStore.rqQ]
        rw [hn c hc _ (by rw [rqOff_val hp]; omega) (by rw [rqOff_val hp]; omega) (by rw [rqOff_val hp]; omega),
          hn c hc _ (by rw [rqTailOff_val hp]; omega) (by rw [rqTailOff_val hp]; omega)
            (by rw [rqTailOff_val hp]; omega)]
      · exact hn c hc _ (by rw [l1Off_val]; omega) (by rw [l1Off_val]) (by rw [l1Off_val]; omega)
      · exact hn c hc _ (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega)
    refine ⟨(h.ready c hc).1.agree hv.1 fun p hp y hy => ?_, (h.ready c hc).2.views hv⟩
    exact hlink y (((h.ready c hc).1.rel p hp).mem y hy)
  · have e : L.relQ s' c = L.relQ s c := by
      simp only [LawfulStore.relQ]
      rw [hn c hc _ (by rw [relh_val]; omega) (by rw [relh_val]) (by rw [relh_val]; simp),
        hn c hc _ (by rw [relt_val]; omega) (by rw [relt_val]) (by rw [relt_val]; omega)]
    rw [e]; exact hrel (h.release c hc)
  · intro c hc p hp y hy
    have := h.inQ c hc p hp y hy
    have hyT := h.memT hc hp hy
    rcases haff y hyT with e | ⟨h0, -, -⟩
    · exact ⟨e.trans this.1, (hle y hyT c hc p hp hy).trans this.2⟩
    · exact absurd hy (h.notQ hyT h0 hc hp)
  · intro c hc y hy
    rcases haff y (h.memTR hc hy) with e | ⟨-, h0, -⟩
    · exact e.trans (h.inR c hc y hy)
    · exact absurd hy (h.notR (h.memTR hc hy) h0 hc)
  · intro y hy
    rw [hinq y hy]
    rcases haff y hy with ea | ⟨h0, -, hc'⟩
    · rw [ea]
      rcases hprio y hy with e | ⟨h0, hlt⟩
      · rw [e]; exact h.queued y hy
      · constructor
        · intro h1; exact absurd h0 h1
        · intro h1; exact absurd h1 (h.notQ hy h0 (h.aff y hy) hlt)
    · constructor
      · intro h1; exact absurd h0 h1
      · intro h1; exact absurd h1 (h.notQ hy h0 hc' (hpr y hy))
  · intro y hy
    rw [hinq y hy]
    rcases haff y hy with ea | ⟨-, h0, hc'⟩
    · rw [ea]; exact h.released y hy
    · constructor
      · intro h1; exact absurd h0 h1
      · intro h1; exact absurd h1 (h.notR hy h0 hc')
  · intro y hy hq
    rcases haff y hy with ea | ⟨h0, -, hc'⟩
    · rw [ea] at hq ⊢
      rcases hprio y hy with e | ⟨h0, hlt⟩
      · rw [e] at hq; exact h.excl y hy hq
      · exact absurd hq (h.notQ hy h0 (h.aff y hy) hlt)
    · exact absurd hq (h.notQ hy h0 hc' (hpr y hy))


/-! ## Small invariant steps for donation -/

/-- A write to one word of the current core's `IPI_PENDING` pair. a64: `o` is `IPI_PENDING` (120) or
`IPI_PENDING_HI` (128); x86_64 states it for `IPI_PENDING`. -/
theorem ipi_all {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {v : U64} {o : U64} (ho : o.val = 120 ∨ o.val = 128)
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) :
    SchedQueuesInvX st T Cs Ω H X (L.wr s (L.nodeAt s (L.cpu s) o) v) Q R ∧
      BoundInv st T Ac (L.wr s (L.nodeAt s (L.cpu s) o) v) ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z (L.wr s (L.nodeAt s (L.cpu s) o) v) ∧
      SCsOK st T Ω Sg Scs Z Ac (L.wr s (L.nodeAt s (L.cpu s) o) v) ∧
      SgOK st Ω Sg (L.wr s (L.nodeAt s (L.cpu s) o) v) ∧
      L.actionW (L.wr s (L.nodeAt s (L.cpu s) o) v) = L.actionW s ∧
      L.curW (L.wr s (L.nodeAt s (L.cpu s) o) v) = L.curW s ∧
      L.idleW (L.wr s (L.nodeAt s (L.cpu s) o) v) = L.idleW s ∧
      L.cscW (L.wr s (L.nodeAt s (L.cpu s) o) v) = L.cscW s ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        L.mem (L.wr s (L.nodeAt s (L.cpu s) o) v) (core.num.U64.wrapping_add y K) =
          L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ a ∈ Ω, L.mem (L.wr s (L.nodeAt s (L.cpu s) o) v) a = L.mem s a) := by
  have hN' := h.nodes _ h.cur
  obtain ⟨h1, hB1, hX1, hSg1, ea, ec, ecs, -⟩ := node_bx (v := v) h hB hX hSg (o := o)
    (by simp only [LowFree]; omega) (by omega) (by omega)
  have ha : Aligned (L.nodeAt s (L.cpu s) o) := nodeAt_aligned hN' (by omega) (by omega)
  obtain ⟨-, hcΩ⟩ := objs_omega hX.1 hS.sub
  refine ⟨h1, hB1, hX1, SCsOK.wr h hS hX ha (fun y hy e => ?_) ?_ (fun c hc => ?_)
    (fun c hc => out_ne_node (h.omega _ (spor_omega hX.1 hc)) h.cur hN' (by omega))
    (fun c hc e => absurd e (out_ne_node (h.omega _ (hS.sub _ (hX.1.repW c hc))) h.cur hN' (by omega))),
    hSg1, ea, ec, ?_, ecs,
    fun y hy K hK hK8 => field_wr_node h h.cur (by omega) (by omega) hy hK hK8, fun a ha' => ?_⟩
  · rw [scA_eq] at e
    exact node_ne_field hN' (by omega) hy (h.tcbs y hy) (by simp) (UScalar.eq_of_val_eq e)
  · intro e
    simp only [LawfulStore.nodeA] at e
    rw [nodeAt_val hN' (by omega), nodeAt_val hN' (by simp [layout.node.CUR_SC])] at e
    simp [layout.node.CUR_SC] at e; omega
  · obtain ⟨-, -, c3, c4, c5⟩ := hcΩ c hc
    exact ⟨out_ne_node (h.omega _ c3) h.cur hN' (by omega),
      out_ne_node (h.omega _ c4) h.cur hN' (by omega), out_ne_node (h.omega _ c5) h.cur hN' (by omega)⟩
  · exact rd_cur_node h (by omega) (by omega) (by rw [idle8]; omega) (by rw [idle8]) (by rw [idle8]; omega)
  · have hoΩ := h.omega a ha'
    exact L.mem_wr_ne ha hoΩ.1 (fun e => out_ne_node hoΩ h.cur hN' (by omega) e)

/-- `XInv0` when the SC fields are kept or cleared. -/
theorem XInv0.keep0 {s s' : S} (hX : XInv0 st T Cs Ω Sg Rp Scs Nt Z s)
    (hrw : ∀ r ∈ Rp, L.mem s' (rTcbA r) = L.mem s (rTcbA r) ∧ L.mem s' (rPrevA r) = L.mem s (rPrevA r) ∧
      L.mem s' (rNextA r) = L.mem s (rNextA r))
    (hfx : ∀ c ∈ Scs, L.mem s' (scTcbA c) = L.mem s (scTcbA c) ∧ L.mem s' (scCoreA c) = L.mem s (scCoreA c))
    (hsc : ∀ t ∈ T, L.mem s' (scA t) = L.mem s (scA t) ∨ L.mem s' (scA t) = 0#u64)
    (hrep : ∀ t ∈ T, L.mem s' (replyA t) = L.mem s (replyA t))
    (hst : ∀ t ∈ T, L.mem s' (stA t) = L.mem s (stA t))
    (hcs : L.cscW s' ∈ Scs)
    (hsr : ∀ c ∈ Scs, L.mem s' (scReplyA c) = L.mem s (scReplyA c))
    (hbd : ∀ t ∈ T, L.mem s' (boundA t) = L.mem s (boundA t))
    (hns : ∀ n ∈ Nt, L.mem s' (ntfnScA n) = L.mem s (ntfnScA n))
    (htn : TimerOK st T Cs s' ∧ NtbOK st T Nt s' ∧ TimerRB st T Cs s' ∧ (∀ n ∈ Nt, L.mem s' (ntfnBtA n) = L.mem s (ntfnBtA n)))
    (hsn : ∀ c ∈ Scs, L.mem s' (scNtfnA c) = L.mem s (scNtfnA c))
    (hyl : ∀ t ∈ T, L.mem s' (yieldA t) = L.mem s (yieldA t))
    (hyf : ∀ c ∈ Scs, L.mem s' (scYieldFromA c) = L.mem s (scYieldFromA c))
    (hmx : ∀ c ∈ Scs, L.mem s' (maxA c) = L.mem s (maxA c)) (hiw : L.idleW s' = L.idleW s) :
    XInv0 st T Cs Ω Sg Rp Scs Nt Z s' := by
  obtain ⟨hO, hR, hE⟩ := hX
  refine ⟨hO.ksb, ⟨⟨fun t ht hs => ?_, fun t ht hs hn => ?_, fun r hr => ?_, fun r hr => ?_, fun r hr hn => ?_,
      fun c hc => by rw [hsr c hc]; exact hR.screp c hc,
      idleRep_keep hR.idle hiw (fun c hc => (hfx c hc).1) (fun c hc => Or.inl (hsr c hc))⟩,
      hR.head.keep (fun r hr => (hrw r hr).2.2) hsr (fun r hr h0 hb => (hR.next r hr h0).1 hb)⟩,
    ⟨fun t ht hb => ?_, hcs, fun c hc => by rw [(hfx c hc).2]; exact hE.core c hc,
      fun t ht => by rw [hbd t ht]; exact hE.bnd t ht, ScExtra.nsc_keep hE.nsc hns hsn hmx,
      htn.1, htn.2.1, htn.2.2.1, fun c hc => by rw [hsn c hc]; exact hE.scn c hc,
      hE.yt.keep (fun c hc => (hfx c hc).1) hyl hyf,
      hE.bs.keep hE.bnd hE.ntb hE.scn hbd htn.2.2.2 hns hsn⟩⟩
  · rw [hst t ht] at hs
    obtain ⟨h1, h2⟩ := hR.reply t ht hs
    rw [hrep t ht, (hrw _ h1).1]; exact ⟨h1, h2⟩
  · rw [hst t ht] at hs; rw [hrep t ht] at hn ⊢
    obtain ⟨h1, h2⟩ := hR.recv t ht hs hn
    rw [(hrw _ h1).1]; exact ⟨h1, h2⟩
  · rw [(hrw r hr).2.2]; exact hR.next r hr
  · rw [(hrw r hr).2.1]; exact hR.prev r hr
  · rw [(hrw r hr).1] at hn ⊢
    obtain ⟨b0, b1, b2, b3⟩ := hR.back r hr hn
    rw [hrep _ b1, hst _ b1]; exact ⟨b0, b1, b2, b3⟩
  · rcases hsc t ht with e | e
    · rw [e] at hb ⊢
      obtain ⟨h1, h2, h3⟩ := hE.bound t ht hb
      rw [(hfx _ h1).1, (hfx _ h1).2]; exact ⟨h1, h2, h3⟩
    · exact absurd e hb

/-- `BoundInv` after a nonzero SC field write (and nothing else it reads). -/
theorem BoundInv.set_sc {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t c : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T Ac s) (ht : t ∈ T) (hc : c ≠ 0#u64)
    (hcA : Sch st s t → c ∈ Ac) :
    BoundInv st T Ac (L.wr s (scA t) c) := by
  have hT := h.tcbs
  have hta := hT t ht
  have hN := h.nodes _ h.cur
  have ha := scA_aligned hta
  have fk : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (y = t → K.val ≠ 3464) →
      L.mem (L.wr s (scA t) c) (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K hK hK8 hne => L.mem_wr_ne ha (field_aligned (hT y hy) hK hK8)
      (fun e => field_ne (K1 := 3464#u64) hta (hT y hy) (by simp) hK
        (fun e' => by subst e'; exact fun h' => hne rfl h'.symm) (UScalar.eq_of_val_eq e))
  have nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem (L.wr s (scA t) c) (L.nodeAt (L.wr s (scA t) c) (L.cpu (L.wr s (scA t) c)) o) =
        L.mem s (L.nodeAt s (L.cpu s) o) := fun o h1 h2 => by
    simp only [LawfulStore.cpu_wr, nodeAt_wr]
    exact L.mem_wr_ne ha (nodeAt_aligned hN h1 h2)
      (fun e => node_ne_field (K := 3464#u64) hN h1 ht hta (by simp) (UScalar.eq_of_val_eq e).symm)
  have sc' : ∀ y ∈ T, L.mem (L.wr s (scA t) c) (scA y) ≠ 0#u64 ↔ L.mem s (scA y) ≠ 0#u64 ∨ y = t := by
    intro y hy
    by_cases e : y = t
    · subst e; rw [L.mem_wr_same ha]; simp [hc]
    · have := fk y hy 3464#u64 (by simp) (by simp) (fun e' => absurd e' e)
      rw [show scA y = core.num.U64.wrapping_add y 3464#u64 from rfl, this]; simp [e]
  have iq : ∀ y ∈ T, L.mem (L.wr s (scA t) c) (inqA y) = L.mem s (inqA y) := fun y hy => by
    rw [inqA_eq]; exact fk y hy _ (by simp) (by simp) (fun _ => by simp)
  have ea : L.actionW (L.wr s (scA t) c) = L.actionW s := nd _ (by rw [act_val]; omega) (by rw [act_val])
  have ec : L.curW (L.wr s (scA t) c) = L.curW s := nd _ (by rw [curth0]; omega) (by rw [curth0])
  have ei : L.idleW (L.wr s (scA t) c) = L.idleW s := nd _ (by rw [idle8]; omega) (by rw [idle8])
  refine ⟨fun y hy hf => ?_, fun y hy hf => ?_, fun haT => ?_, ?_, fun h0 => ?_,
    hB.nb ei (by rw [stA_eq]; exact fk (L.idleW s) h.idleT _ (by simp) (by simp) (fun _ => by simp)),
    fun y hy hS h0 => ?_⟩
  rotate_right
  · have hS' : Sch st s y := Sch.of_eq (fun hf => by rwa [iq y hy] at hf) (fun hf => by rwa [iq y hy] at hf) ea ei ec
      (by rw [stA_eq]; exact fk y hy _ (by simp) (by simp) (fun _ => by simp)) hS
    by_cases e : y = t
    · subst e; rw [L.mem_wr_same ha]; exact hcA hS'
    · have := fk y hy 3464#u64 (by simp) (by simp) (fun e' => absurd e' e)
      rw [show scA y = core.num.U64.wrapping_add y 3464#u64 from rfl, this] at h0 ⊢
      exact hB.sact y hy hS' h0
  · rw [iq y hy] at hf; exact (sc' y hy).2 (Or.inl (hB.q y hy hf))
  · rw [iq y hy] at hf; exact (sc' y hy).2 (Or.inl (hB.r y hy hf))
  · rw [ea] at haT ⊢; exact (sc' _ haT).2 (Or.inl (hB.act haT))
  · rw [ei]; exact (sc' _ h.idleT).2 (Or.inl hB.idle)
  · rw [ea] at h0; rw [ec]; exact (sc' _ h.curT).2 (Or.inl (hB.resume h0))

/-- Setting the affinity of a thread in no ready or release queue to a
core keeps the invariant. -/
theorem inv_wr_aff {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t v : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) (hq : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64)
    (hr : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64) (hv : v ∈ Cs) :
    SchedQueuesInvX st T Cs Ω H X (L.wr s (affA t) v) Q R := by
  have hT := h.tcbs
  have hta := hT t ht
  have ha : Aligned (affA t) := field_aligned hta (by simp) (by simp)
  have fld : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (y = t → K.val ≠ 3520) →
      L.mem (L.wr s (affA t) v) (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K hK hK8 hne => L.mem_wr_ne ha (field_aligned (hT y hy) hK hK8)
      (fun e => field_ne hta (hT y hy) (by simp) hK (fun e' => by subst e'; exact fun h => hne rfl h.symm)
        (UScalar.eq_of_val_eq e))
  have hN' := h.nodes _ h.cur
  have e : L.actionW (L.wr s (affA t) v) = L.actionW s := by
    unfold LawfulStore.actionW
    simp only [LawfulStore.cpu_wr, nodeAt_wr]
    exact L.mem_wr_ne ha (nodeAt_aligned hN' (by rw [act_val]; omega) (by rw [act_val]))
      (fun e => node_ne_field hN' (by rw [act_val]; omega) ht hta (by simp) (UScalar.eq_of_val_eq e).symm)
  have hsb : ∀ y ∈ T, L.mem (L.wr s (affA t) v) (stA y) = L.mem s (stA y) ∧
      L.mem (L.wr s (affA t) v) (blockA y) = L.mem s (blockA y) := fun y hy =>
    ⟨by rw [stA_eq]; exact fld y hy _ (by simp) (by simp) (fun _ => by simp),
      by rw [blockA_eq]; exact fld y hy _ (by simp) (by simp) (fun _ => by simp)⟩
  refine inv_of_agree_aff h (L.ksb_wr _ _ _) (L.cpu_wr _ _ _) (fun y hy => ⟨?_, ?_⟩) (fun c hc o' h1 h2 h3 => ?_)
    (fun y hy => by rw [inqA_eq]; exact fld y hy _ (by simp) (by simp) (fun _ => by simp)) (fun y hy => ?_)
    (fun y hy => Or.inl (fld y hy _ (by simp) (by simp) (fun _ => by simp))) (by rw [e]; exact h.action) hsb
    (by rw [e]; intro haT; rw [(hsb _ haT).1]; exact h.actOK haT)
    (h.eps.agree (L.ksb_wr _ _ _) hsb
      (fun y hy => ⟨by rw [nextA_eq']; exact fld y hy _ (by simp [nextOff]) (by simp [nextOff]) (fun _ => by simp [nextOff]),
        by rw [prevA_eq']; exact fld y hy _ (by simp [prevOff]) (by simp [prevOff]) (fun _ => by simp [prevOff])⟩)
      (fun a hao => L.mem_wr_ne ha hao.1 (out_ne_field hao ht hta (by simp))))
    (curidle_wr_field (K := 3520#u64) h ht (by simp) (by simp)).1
    (curidle_wr_field (K := 3520#u64) h ht (by simp) (by simp)).2
  · rw [nextA_eq']; exact fld y hy _ (by simp [nextOff]) (by simp [nextOff]) (fun _ => by simp [nextOff])
  · rw [prevA_eq']; exact fld y hy _ (by simp [prevOff]) (by simp [prevOff]) (fun _ => by simp [prevOff])
  · exact L.mem_wr_ne ha (nodeAt_aligned (h.nodes c hc) h1 h2)
      (fun e => node_ne_field (h.nodes c hc) h1 ht hta (by simp) (UScalar.eq_of_val_eq e).symm)
  · by_cases e' : y = t
    · subst e'; right; exact ⟨hq, hr, by rw [L.mem_wr_same ha]; exact hv⟩
    · left; exact fld y hy _ (by simp) (by simp) (fun e2 => absurd e2 e')

/-- The idle thread word is not null. -/
theorem idle_ne0 {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) : L.idleW s ≠ 0#u64 := fun e => by
  have e' := e
  unfold LawfulStore.idleW at e'
  exact (h.tcbs _ h.idleT).ne0 (by rw [e']; rfl)

/-- `XInv` after writing the `TCB` word of an SC no thread is bound to. -/
theorem XInv.set_sctcb {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {c0 v : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hX : XInv0 st T Cs Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (hc0 : c0 ∈ Scs) (hnb : ∀ y ∈ T, L.mem s (scA y) ≠ c0) (hvT : v ≠ 0#u64 → v ∈ T)
    (hvi : v = L.idleW s → L.mem s (scReplyA c0) = 0#u64) :
    XInv0 st T Cs Ω Sg Rp Scs Nt Z (L.wr s (scTcbA c0) v) := by
  obtain ⟨hO, hR, hE⟩ := hX
  have hm : scTcbA c0 ∈ Ω := hsub _ (hO.fixW c0 hc0).1
  have ho := h.omega _ hm
  have hN := h.nodes _ h.cur
  have hv0 := sc_facts hO hc0
  have tmS : TmFr st T Cs Nt s (L.wr s (scTcbA c0) v) :=
    TmFr.wr h.tcbs h.nodes hO ho.1 (notTmW_insc h hO hsub hc0 ho.1 ⟨by rw [hv0.2.1]; omega,
      by rw [hv0.2.1]; have := hv0.1; omega⟩)
  have k : ∀ a, Aligned a → a.val ≠ (scTcbA c0).val → L.mem (L.wr s (scTcbA c0) v) a = L.mem s a :=
    fun a ha hne => L.mem_wr_ne ho.1 ha (fun e => hne e.symm)
  have fk : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem (L.wr s (scTcbA c0) v) (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K hK hK8 => k _ (field_aligned (h.tcbs y hy) hK hK8) (out_ne_field ho hy (h.tcbs y hy) hK)
  obtain ⟨hrΩ, hcΩ⟩ := objs_omega hO hsub
  have rw' : ∀ r ∈ Rp, ∀ a ∈ Ω, (a = rTcbA r ∨ a = rPrevA r ∨ a = rNextA r) →
      L.mem (L.wr s (scTcbA c0) v) a = L.mem s a := by
    intro r hr a ha e
    refine k a (h.omega a ha).1 (fun e' => ?_)
    obtain ⟨-, e1, e2, e3⟩ := rp_facts hO hr
    have := hO.rpSc r hr c0 hc0
    rw [hv0.2.1] at e'
    rcases e with rfl | rfl | rfl
    · rw [e1] at e'; omega
    · rw [e2] at e'; omega
    · rw [e3] at e'; omega
  have scw : ∀ c ∈ Scs, ∀ a ∈ Ω, (a.val = c.val + 16 ∨ a.val = c.val + 32 ∨ (c ≠ c0 ∧ a.val = c.val + 24)) →
      L.mem (L.wr s (scTcbA c0) v) a = L.mem s a := by
    intro c hc a ha hv
    refine k a (h.omega a ha).1 (fun e => ?_)
    rw [hv0.2.1] at e
    have := (sc_facts hO hc).1; have := hv0.1
    by_cases hcc : c = c0
    · subst hcc; rcases hv with hv | hv | ⟨hne, -⟩
      · omega
      · omega
      · exact hne rfl
    · have := hO.scDisj c hc c0 hc0 hcc
      rcases hv with hv | hv | ⟨-, hv⟩ <;> omega
  have ecs : L.cscW (L.wr s (scTcbA c0) v) = L.cscW s := by
    unfold LawfulStore.cscW; rw [nodeA_wr]
    exact k _ (nodeAt_aligned hN (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))
      (out_ne_node ho h.cur hN (by simp [layout.node.CUR_SC]))
  have st' : ∀ y ∈ T, L.mem (L.wr s (scTcbA c0) v) (stA y) = L.mem s (stA y) := fun y hy => by
    rw [stA_eq]; exact fk y hy _ (by simp) (by simp)
  have rp' : ∀ y ∈ T, L.mem (L.wr s (scTcbA c0) v) (replyA y) = L.mem s (replyA y) := fun y hy =>
    fk y hy _ (by simp) (by simp)
  have sc' : ∀ y ∈ T, L.mem (L.wr s (scTcbA c0) v) (scA y) = L.mem s (scA y) := fun y hy => by
    rw [scA_eq]; exact fk y hy _ (by simp) (by simp)
  have ei : L.idleW (L.wr s (scTcbA c0) v) = L.idleW s := by
    unfold LawfulStore.idleW; rw [LawfulStore.cpu_wr, nodeAt_wr]
    exact k _ (nodeAt_aligned hN (by rw [idle8]; omega) (by rw [idle8]))
      (out_ne_node ho h.cur hN (by rw [idle8]; omega))
  have sr' : ∀ c ∈ Scs, L.mem (L.wr s (scTcbA c0) v) (scReplyA c) = L.mem s (scReplyA c) := fun c hc =>
    scw c hc _ (hsub _ (hO.repW c hc)) (Or.inr (Or.inl (sc_facts hO hc).2.2.2.2.2.2.1))
  have hid : ∀ c ∈ Scs, L.mem (L.wr s (scTcbA c0) v) (scTcbA c) = L.idleW (L.wr s (scTcbA c0) v) →
      L.mem (L.wr s (scTcbA c0) v) (scReplyA c) = 0#u64 := fun c hc e => by
    rw [sr' c hc]; rw [ei] at e
    by_cases hcc : c = c0
    · subst hcc; rw [L.mem_wr_same ho.1] at e; exact hvi e
    · refine hR.idle c hc ?_
      rw [← e, scw c hc _ (hcΩ _ hc).1 (Or.inr (Or.inr ⟨hcc, (sc_facts hO hc).2.1⟩))]
  refine ⟨hO.ksb, ⟨⟨fun u hu hs => ?_, fun u hu hs hn => ?_, fun r hr => ?_, fun r hr => ?_, fun r hr hn => ?_,
      fun c hc => ?_, hid⟩, hR.head.keep (fun r hr => rw' r hr _ (hrΩ _ hr).2.2 (Or.inr (Or.inr rfl)))
        (fun c hc => scw c hc _ (hsub _ (hO.repW c hc)) (Or.inr (Or.inl (sc_facts hO hc).2.2.2.2.2.2.1)))
        (fun r hr h0 hb => (hR.next r hr h0).1 hb)⟩, ⟨fun u hu hb => ?_, by rw [ecs]; exact hE.cur, fun c hc => by rw [scw c hc _ (hcΩ _ hc).2.1 (Or.inl (sc_facts hO hc).2.2.1)]; exact hE.core c hc,
      fun u hu => by
        rw [show L.mem (L.wr s (scTcbA c0) v) (boundA u) = L.mem s (boundA u) from fk u hu _ (by simp) (by simp)]
        exact hE.bnd u hu,
      ScExtra.nsc_keep hE.nsc
        (fun n hn => k _ (hO.ntAl n hn) (fun e => by rw [hv0.2.1] at e; have := hO.ntSc n hn c0 hc0; have := hv0.1; omega))
        (fun c hc => by
          obtain ⟨hPc, hzc⟩ := hO.sc c hc
          exact k _ (h.omega _ (hsub _ (hO.snW c hc))).1 (fun e => by
            rw [hv0.2.1, scNtfnA_val hPc hzc] at e
            have := (sc_facts hO hc).1; have := hv0.1
            by_cases hcc : c = c0
            · subst hcc; omega
            · have := hO.scDisj c hc c0 hc0 hcc; omega))
        (fun c hc => k _ (maxA_facts hO hc).1 (fun e => by
          rw [hv0.2.1, maxA_val (hO.sc c hc).1 (hO.sc c hc).2] at e
          have := (sc_facts hO hc).1; have := hv0.1
          by_cases hcc : c = c0
          · subst hcc; omega
          · have := hO.scDisj c hc c0 hc0 hcc; omega)),
      hE.tm.tmfr tmS, hE.ntb.tmfr tmS, hE.rb.tmfr tmS,
      fun c hc => by
        obtain ⟨hPc, hzc⟩ := hO.sc c hc
        rw [k _ (h.omega _ (hsub _ (hO.snW c hc))).1 (fun e => by
          rw [hv0.2.1, scNtfnA_val hPc hzc] at e
          have := (sc_facts hO hc).1; have := hv0.1
          by_cases hcc : c = c0
          · subst hcc; omega
          · have := hO.scDisj c hc c0 hc0 hcc; omega)]
        exact hE.scn c hc,
      ⟨fun c hc h0 => by
        rw [L.mem_wr_val ho.1 (h.omega _ (hsub _ (hO.fixW c hc).1)).1] at h0 ⊢
        split
        · rename_i e; rw [if_pos e] at h0; exact hvT h0
        · rename_i e; rw [if_neg e] at h0; exact hE.yt.1 c hc h0,
       fun u hu => by
        rw [show yieldA u = core.num.U64.wrapping_add u 3472#u64 from rfl, fk u hu _ (by simp) (by simp)]
        exact hE.yt.2.1 u hu,
       fun c hc => by
        rw [k _ (h.omega _ (hsub _ (hO.syW c hc))).1 (fun e => by
          rw [hv0.2.1, show scYieldFromA c = core.num.U64.wrapping_add c layout.sc.YIELD_FROM from rfl,
            (sc_facts hO hc).2.2.2.2.2.2.2] at e
          have := (sc_facts hO hc).1; have := hv0.1
          by_cases hcc : c = c0
          · subst hcc; omega
          · have := hO.scDisj c hc c0 hc0 hcc; omega)]
        exact hE.yt.2.2 c hc⟩,
      BndS.wr_scw (o := 24) hE h hO hsub hm hc0 hv0.2.1 (by omega) (by omega)⟩⟩
  · rw [st' u hu] at hs
    obtain ⟨h1, h2⟩ := hR.reply u hu hs
    rw [rp' u hu, rw' _ h1 _ (hrΩ _ h1).1 (Or.inl rfl)]; exact ⟨h1, h2⟩
  · rw [st' u hu] at hs; rw [rp' u hu] at hn ⊢
    obtain ⟨h1, h2⟩ := hR.recv u hu hs hn
    rw [rw' _ h1 _ (hrΩ _ h1).1 (Or.inl rfl)]; exact ⟨h1, h2⟩
  · rw [rw' r hr _ (hrΩ _ hr).2.2 (Or.inr (Or.inr rfl))]; exact hR.next r hr
  · rw [rw' r hr _ (hrΩ _ hr).2.1 (Or.inr (Or.inl rfl))]; exact hR.prev r hr
  · rw [rw' r hr _ (hrΩ _ hr).1 (Or.inl rfl)] at hn ⊢
    obtain ⟨b0, b1, b2, b3⟩ := hR.back r hr hn
    rw [rp' _ b1, st' _ b1]; exact ⟨b0, b1, b2, b3⟩
  · rw [scw c hc _ (hsub _ (hO.repW c hc)) (Or.inr (Or.inl (sc_facts hO hc).2.2.2.2.2.2.1))]
    exact hR.screp c hc
  · rw [sc' u hu] at hb ⊢
    obtain ⟨h1, h2, h3⟩ := hE.bound u hu hb
    have hne : L.mem s (scA u) ≠ c0 := hnb u hu
    rw [scw _ h1 _ (hcΩ _ h1).1 (Or.inr (Or.inr ⟨hne, (sc_facts hO h1).2.1⟩)),
      scw _ h1 _ (hcΩ _ h1).2.1 (Or.inl (sc_facts hO h1).2.2.1)]
    exact ⟨h1, h2, h3⟩

/-- `TScX` after writing the `TCB` word of the excepted SC. -/
theorem TScX.set_sctcb {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {c0 v : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (hc0 : c0 ∈ Scs) (htx : TScX st Scs c0 s) (hyt : ∀ c ∈ Scs, L.mem s (scTcbA c) ≠ 0#u64 → L.mem s (scTcbA c) ∈ T) :
    TScX st Scs c0 (L.wr s (scTcbA c0) v) := by
  have ho := h.omega _ (hsub _ (hO.fixW c0 hc0).1)
  refine htx.keep hyt (fun c hc hne => L.mem_wr_ne ho.1 (h.omega _ (hsub _ (hO.fixW c hc).1)).1 ?_)
    (fun y hy => L.mem_wr_ne ho.1 (scA_aligned (h.tcbs y hy)) (out_ne_field (K := 3464#u64) ho hy (h.tcbs y hy) (by simp)).symm)
  rw [(sc_facts hO hc0).2.1, (sc_facts hO hc).2.1]
  have := hO.scDisj c hc c0 hc0 hne; have := (sc_facts hO hc).1; have := (sc_facts hO hc0).1; omega

/-- `TSc` after binding `t` to the excepted SC `c0`, which names `t`, when no
other SC names `t`. -/
theorem TSc.bind {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t c0 : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (ht : t ∈ T) (htx : TScX st Scs c0 s) (htc : L.mem s (scTcbA c0) = t)
    (huq : ∀ c ∈ Scs, c ≠ 0#u64 → L.mem s (scTcbA c) = t → c = c0)
    (hyt : ∀ c ∈ Scs, L.mem s (scTcbA c) ≠ 0#u64 → L.mem s (scTcbA c) ∈ T) :
    TSc st Scs (L.wr s (scA t) c0) := by
  have hT := h.tcbs
  have hta := hT t ht
  have ha := scA_aligned hta
  intro c hc hc0 h0
  have fx : L.mem (L.wr s (scA t) c0) (scTcbA c) = L.mem s (scTcbA c) :=
    L.mem_wr_ne ha (h.omega _ (hsub _ (hO.fixW c hc).1)).1
      (fun e => out_ne_field (K := 3464#u64) (h.omega _ (hsub _ (hO.fixW c hc).1)) ht hta (by simp) e)
  rw [fx] at h0 ⊢
  by_cases e : c = c0
  · subst e; rw [htc]; exact L.mem_wr_same ha
  have hyT := hyt c hc h0
  by_cases ey : L.mem s (scTcbA c) = t
  · exact absurd (huq c hc hc0 ey) e
  rw [L.mem_wr_ne ha (scA_aligned (hT _ hyT)) (fun e' => field_ne (K1 := 3464#u64) (K2 := 3464#u64) hta (hT _ hyT)
    (by simp) (by simp) (fun e2 => absurd e2.symm ey) (UScalar.eq_of_val_eq e'))]
  exact htx c hc e hc0 h0

/-- `XInv0` after binding `t` to the SC `c0`, which names `t` and a core. -/
theorem XInv.bind {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t c0 : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hX : XInv0 st T Cs Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (ht : t ∈ T) (hc0 : c0 ∈ Scs) (htc : L.mem s (scTcbA c0) = t) (hcore : L.mem s (scCoreA c0) ∈ Cs) :
    XInv0 st T Cs Ω Sg Rp Scs Nt Z (L.wr s (scA t) c0) := by
  obtain ⟨hO, hR, hE⟩ := hX
  have hT := h.tcbs
  have hta := hT t ht
  have ha := scA_aligned hta
  have hN := h.nodes _ h.cur
  have fk : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (y = t → K.val ≠ 3464) →
      L.mem (L.wr s (scA t) c0) (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K hK hK8 hne => L.mem_wr_ne ha (field_aligned (hT y hy) hK hK8)
      (fun e => field_ne (K1 := 3464#u64) hta (hT y hy) (by simp) hK
        (fun e' => by subst e'; exact fun h' => hne rfl h'.symm) (UScalar.eq_of_val_eq e))
  have ok : ∀ a ∈ Ω, L.mem (L.wr s (scA t) c0) a = L.mem s a := fun a haΩ =>
    L.mem_wr_ne ha (h.omega a haΩ).1 (fun e => out_ne_field (K := 3464#u64) (h.omega a haΩ) ht hta (by simp) e)
  obtain ⟨hrΩ, hcΩ⟩ := objs_omega hO hsub
  have tmB : TmFr st T Cs Nt s (L.wr s (scA t) c0) :=
    TmFr.wr h.tcbs h.nodes hO ha (notTmW_field (K := 3464#u64) h.tcbs h.nodes
      (fun n hn => h.omega _ (hsub _ (hO.ntB n hn).2)) ht (by simp) (by simp))
  have st' : ∀ y ∈ T, L.mem (L.wr s (scA t) c0) (stA y) = L.mem s (stA y) := fun y hy => by
    rw [stA_eq]; exact fk y hy _ (by simp) (by simp) (fun _ => by simp)
  have rp' : ∀ y ∈ T, L.mem (L.wr s (scA t) c0) (replyA y) = L.mem s (replyA y) := fun y hy =>
    fk y hy _ (by simp) (by simp) (fun _ => by simp)
  have ecs : L.cscW (L.wr s (scA t) c0) = L.cscW s := by
    unfold LawfulStore.cscW; rw [nodeA_wr]
    exact L.mem_wr_ne ha (nodeAt_aligned hN (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))
      (fun e => node_ne_field (K := 3464#u64) hN (by simp [layout.node.CUR_SC]) ht hta (by simp)
        (UScalar.eq_of_val_eq e).symm)
  have ei : L.idleW (L.wr s (scA t) c0) = L.idleW s := by
    unfold LawfulStore.idleW; rw [LawfulStore.cpu_wr, nodeAt_wr]
    exact L.mem_wr_ne ha (nodeAt_aligned hN (by rw [idle8]; omega) (by rw [idle8]))
      (fun e => node_ne_field (K := 3464#u64) hN (by rw [idle8]; omega) ht hta (by simp)
        (UScalar.eq_of_val_eq e).symm)
  refine ⟨hO.ksb, ⟨⟨fun u hu hs => ?_, fun u hu hs hn => ?_, fun r hr => ?_, fun r hr => ?_, fun r hr hn => ?_,
      fun c hc => ?_, idleRep_keep hR.idle ei (fun c hc => ok _ (hcΩ _ hc).1)
        (fun c hc => Or.inl (ok _ (hsub _ (hO.repW c hc))))⟩,
      hR.head.keep (fun r hr => ok _ (hrΩ _ hr).2.2) (fun c hc => ok _ (hsub _ (hO.repW c hc)))
        (fun r hr h0 hb => (hR.next r hr h0).1 hb)⟩, ⟨fun u hu hb => ?_, by rw [ecs]; exact hE.cur, fun c hc => by rw [ok _ (hcΩ _ hc).2.1]; exact hE.core c hc,
      fun u hu => by
        rw [show L.mem (L.wr s (scA t) c0) (boundA u) = L.mem s (boundA u) from
          fk u hu _ (by simp) (by simp) (fun _ => by simp)]
        exact hE.bnd u hu,
      ScExtra.nsc_keep hE.nsc (fun n hn => ok _ (hsub _ (hO.ntW n hn))) (fun c hc => ok _ (hsub _ (hO.snW c hc)))
        (fun c hc => ok _ (hcΩ c hc).2.2.1),
      hE.tm.tmfr tmB, hE.ntb.tmfr tmB, hE.rb.tmfr tmB, fun c hc => by rw [ok _ (hsub _ (hO.snW c hc))]; exact hE.scn c hc,
      hE.yt.keep (fun c hc => ok _ (hcΩ c hc).1)
        (fun u hu => fk u hu _ (by simp) (by simp) (fun _ => by simp))
        (fun c hc => ok _ (hsub _ (hO.syW c hc))),
      BndS.wr_field (K := 3464#u64) hE h hO hsub ht (by simp) (by simp) (by simp)⟩⟩
  · rw [st' u hu] at hs
    obtain ⟨h1, h2⟩ := hR.reply u hu hs
    rw [rp' u hu, ok _ (hrΩ _ h1).1]; exact ⟨h1, h2⟩
  · rw [st' u hu] at hs; rw [rp' u hu] at hn ⊢
    obtain ⟨h1, h2⟩ := hR.recv u hu hs hn
    rw [ok _ (hrΩ _ h1).1]; exact ⟨h1, h2⟩
  · rw [ok _ (hrΩ _ hr).2.2]; exact hR.next r hr
  · rw [ok _ (hrΩ _ hr).2.1]; exact hR.prev r hr
  · rw [ok _ (hrΩ _ hr).1] at hn ⊢
    obtain ⟨b0, b1, b2, b3⟩ := hR.back r hr hn
    rw [rp' _ b1, st' _ b1]; exact ⟨b0, b1, b2, b3⟩
  · rw [ok _ (hsub _ (hO.repW c hc))]; exact hR.screp c hc
  · by_cases e : u = t
    · subst e
      rw [L.mem_wr_same ha, ok _ (hcΩ _ hc0).1, ok _ (hcΩ _ hc0).2.1]
      exact ⟨hc0, htc, hcore⟩
    · have hsc : L.mem (L.wr s (scA t) c0) (scA u) = L.mem s (scA u) := by
        rw [show scA u = core.num.U64.wrapping_add u 3464#u64 from rfl]
        exact fk u hu _ (by simp) (by simp) (fun e' => absurd e' e)
      rw [hsc] at hb ⊢
      obtain ⟨h1, h2, h3⟩ := hE.bound u hu hb
      rw [ok _ (hcΩ _ h1).1, ok _ (hcΩ _ h1).2.1]; exact ⟨h1, h2, h3⟩

/-- `SCsOK` after binding `t` to the well-formed SC `c0`, disjoint from the
current SC unless it is the current SC. -/
theorem SCsOK.bind {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t c0 : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hS : SCsOK st T Ω Sg Scs Z Ac s) (ht : t ∈ T)
    (hdisj : c0 ≠ L.cscW s → ∀ b, InSC c0 (Z c0) b → Outside b (L.cscW s) (Z (L.cscW s))) :
    SCsOK st T Ω Sg Scs Z Ac (L.wr s (scA t) c0) := by
  have hT := h.tcbs
  have hta := hT t ht
  have ha := scA_aligned hta
  have hN := h.nodes _ h.cur
  have ag : ∀ b ∈ Sg, L.mem (L.wr s (scA t) c0) b = L.mem s b := fun b hb =>
    L.mem_wr_ne ha (h.omega _ (hS.sub b hb)).1
      (fun e => out_ne_field (K := 3464#u64) (h.omega _ (hS.sub b hb)) ht hta (by simp) e)
  have ecs : L.cscW (L.wr s (scA t) c0) = L.cscW s := by
    unfold LawfulStore.cscW; rw [nodeA_wr]
    exact L.mem_wr_ne ha (nodeAt_aligned hN (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))
      (fun e => node_ne_field (K := 3464#u64) hN (by simp [layout.node.CUR_SC]) ht hta (by simp)
        (UScalar.eq_of_val_eq e).symm)
  have scy : ∀ y ∈ T, y ≠ t → L.mem (L.wr s (scA t) c0) (scA y) = L.mem s (scA y) := fun y hy hyt =>
    L.mem_wr_ne ha (scA_aligned (hT y hy)) (fun e => field_ne (K1 := 3464#u64) (K2 := 3464#u64) hta (hT y hy)
      (by simp) (by simp) (fun e' => absurd e'.symm hyt) (UScalar.eq_of_val_eq e))
  refine ⟨hS.sub, fun b hb => by rw [L.ksb_wr]; exact hS.ks b hb, fun o h1 h2 => by rw [L.ksb_wr]; exact hS.ksΩ o h1 h2,
    fun y hy hb hne => ?_, fun c hc => (hS.all c hc).agree ag,
    fun c hc => by rw [show L.rmax (L.wr s (scA t) c0) c = L.rmax s c from ag _ (hS.all c hc).2.1]; exact hS.act c hc,
    fun c hc h0 => hS.spor c hc (by rw [← ag _ (hS.spSg c hc)]; exact h0), hS.spSg,
    fun c hc h0 => hS.rep c hc (by rw [← ag _ (hS.repSg c hc)]; exact h0), hS.repSg, fun c hc => by rw [L.ksb_wr]; exact hS.scKs c hc⟩
  · rw [ecs] at hne ⊢
    by_cases e : y = t
    · subst e; rw [L.mem_wr_same ha] at hne ⊢; exact hdisj hne
    · rw [scy y hy e] at hb hne ⊢; exact hS.disj y hy hb hne

/-- Clearing the SC field of a thread in no ready or release queue, not the
switch-to candidate and not the idle thread. -/
theorem clear_sc_state {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T)
    (hout : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64)
    (hidle : L.idleW s ≠ t) :
    SchedQueuesInvX st T Cs Ω H X (L.wr s (scA t) 0#u64) Q R ∧
      (L.actionW s ≠ t → (L.curW (L.wr s (scA t) 0#u64) = t → L.actionW (L.wr s (scA t) 0#u64) ≠ 0#u64) →
        BoundInv st T Ac (L.wr s (scA t) 0#u64)) ∧
      BoundInv st T Ac (L.wr (L.wr s (scA t) 0#u64)
        (L.nodeAt (L.wr s (scA t) 0#u64) (L.cpu (L.wr s (scA t) 0#u64)) layout.node.SCHED_ACTION) 1#u64) ∧
      XInv0 st T Cs Ω Sg Rp Scs Nt Z (L.wr s (scA t) 0#u64) ∧
      TScX st Scs (L.mem s (scA t)) (L.wr s (scA t) 0#u64) ∧ SCsOK st T Ω Sg Scs Z Ac (L.wr s (scA t) 0#u64) ∧
      SgOK st Ω Sg (L.wr s (scA t) 0#u64) ∧
      L.actionW (L.wr s (scA t) 0#u64) = L.actionW s ∧ L.curW (L.wr s (scA t) 0#u64) = L.curW s ∧
      L.idleW (L.wr s (scA t) 0#u64) = L.idleW s ∧ L.cscW (L.wr s (scA t) 0#u64) = L.cscW s ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (y = t → K.val ≠ 3464) →
        L.mem (L.wr s (scA t) 0#u64) (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ a ∈ Ω, L.mem (L.wr s (scA t) 0#u64) a = L.mem s a) ∧ L.mem (L.wr s (scA t) 0#u64) (scA t) = 0#u64 := by
  obtain ⟨hq0, hr0⟩ := hout
  have hT := h.tcbs
  have hta := hT t ht
  have hN := h.nodes _ h.cur
  have ha := scA_aligned hta
  set s2 := L.wr s (scA t) 0#u64 with hs2
  have h2 : SchedQueuesInvX st T Cs Ω H X s2 Q R := inv_wr_field (K := 3464#u64) h ht (by simp) (by simp) (by simp)
  have F1 : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (y = t → K.val ≠ 3464) →
      L.mem s2 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K hK hK8 hne => L.mem_wr_ne ha (field_aligned (hT y hy) hK hK8)
      (fun e => field_ne (K1 := 3464#u64) hta (hT y hy) (by simp) hK
        (fun e' => by subst e'; exact fun h' => hne rfl h'.symm) (UScalar.eq_of_val_eq e))
  have F2 : ∀ a ∈ Ω, L.mem s2 a = L.mem s a := fun a haΩ =>
    L.mem_wr_ne ha (h.omega a haΩ).1 (fun e => out_ne_field (K := 3464#u64) (h.omega a haΩ) ht hta (by simp) e)
  have F3 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem s2 (L.nodeAt s2 (L.cpu s2) o) = L.mem s (L.nodeAt s (L.cpu s) o) := fun o h1 h2 => by
    rw [hs2]; simp only [LawfulStore.cpu_wr, nodeAt_wr]
    exact L.mem_wr_ne ha (nodeAt_aligned hN h1 h2)
      (fun e => node_ne_field (K := 3464#u64) hN h1 ht hta (by simp) (UScalar.eq_of_val_eq e).symm)
  have sct : L.mem s2 (scA t) = 0#u64 := L.mem_wr_same ha
  have scy : ∀ y ∈ T, y ≠ t → L.mem s2 (scA y) = L.mem s (scA y) := fun y hy hyt =>
    F1 y hy 3464#u64 (by simp) (by simp) (fun e => absurd e hyt)
  have iqy : ∀ y ∈ T, L.mem s2 (inqA y) = L.mem s (inqA y) := fun y hy => by
    rw [inqA_eq]; exact F1 y hy _ (by simp) (by simp) (fun _ => by simp)
  have ea : L.actionW s2 = L.actionW s := F3 _ (by rw [act_val]; omega) (by rw [act_val])
  have ec : L.curW s2 = L.curW s := F3 _ (by rw [curth0]; omega) (by rw [curth0])
  have ei : L.idleW s2 = L.idleW s := F3 _ (by rw [idle8]; omega) (by rw [idle8])
  have ecs : L.cscW s2 = L.cscW s := F3 _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have bq : ∀ y ∈ T, (L.mem s2 (inqA y) &&& sched.Q_QUEUED) ≠ 0#u64 → L.mem s2 (scA y) ≠ 0#u64 := by
    intro y hy hf
    rw [iqy y hy] at hf
    by_cases e : y = t
    · subst e; exact absurd hq0 hf
    · rw [scy y hy e]; exact hB.q y hy hf
  have br : ∀ y ∈ T, (L.mem s2 (inqA y) &&& sched.Q_RELEASE) ≠ 0#u64 → L.mem s2 (scA y) ≠ 0#u64 := by
    intro y hy hf
    rw [iqy y hy] at hf
    by_cases e : y = t
    · subst e; exact absurd hr0 hf
    · rw [scy y hy e]; exact hB.r y hy hf
  have bidle : L.mem s2 (scA (L.idleW s2)) ≠ 0#u64 := by
    rw [ei, scy (L.idleW s) h.idleT hidle]; exact hB.idle
  obtain ⟨hrΩ, hcΩ⟩ := objs_omega hX.1 hSg.sub
  have bnb : ¬ BlockedR (L.mem s2 (stA (L.idleW s2))) := by
    rw [ei, stA_eq, F1 (L.idleW s) h.idleT _ (by simp) (by simp) (fun _ => by simp), ← stA_eq]; exact hB.idleNB
  have bsa : ∀ y ∈ T, Sch st s2 y → L.mem s2 (scA y) ≠ 0#u64 → L.mem s2 (scA y) ∈ Ac := by
    intro y hy hS h0
    have hyt : y ≠ t := fun e => by subst e; exact h0 sct
    rw [scy y hy hyt] at h0 ⊢
    exact hB.sact y hy (Sch.of_eq (fun hf => by rwa [iqy y hy] at hf) (fun hf => by rwa [iqy y hy] at hf)
      ea ei ec (by rw [stA_eq]; exact F1 y hy _ (by simp) (by simp) (fun _ => by simp)) hS) h0
  have tx2 : TScX st Scs (L.mem s (scA t)) s2 := by
    intro c hc hne hc0 h0
    have e1 : L.mem s2 (scTcbA c) = L.mem s (scTcbA c) := F2 _ (hSg.sub _ (hX.1.fixW c hc).1)
    rw [e1] at h0 ⊢
    have hb := hX.2.2.tsc c hc hc0 h0
    by_cases ey : L.mem s (scTcbA c) = t
    · rw [ey] at hb; exact absurd hb.symm hne
    · rw [scy _ (hX.2.2.yt.1 c hc h0) ey]; exact hb
  refine ⟨h2, fun hna hcur => ⟨bq, br, fun haT => ?_, bidle, fun h0 => ?_, bnb, bsa⟩, BoundInv.choose h2 bq br bidle bnb bsa,
    hX.x0.keep0 (fun r hr => ⟨F2 _ (hrΩ r hr).1, F2 _ (hrΩ r hr).2.1, F2 _ (hrΩ r hr).2.2⟩)
      (fun c hc => ⟨F2 _ (hcΩ c hc).1, F2 _ (hcΩ c hc).2.1⟩)
      (fun y hy => by
        by_cases e : y = t
        · subst e; exact Or.inr sct
        · exact Or.inl (scy y hy e))
      (fun y hy => F1 y hy _ (by simp) (by simp) (fun _ => by simp))
      (fun y hy => by rw [stA_eq]; exact F1 y hy _ (by simp) (by simp) (fun _ => by simp))
      (by rw [ecs]; exact hX.2.2.cur) (fun c hc => F2 _ (hSg.sub _ (hX.1.repW c hc)))
      (fun y hy => F1 y hy _ (by simp) (by simp) (fun _ => by simp)) (fun n hn => F2 _ (hSg.sub _ (hX.1.ntW n hn)))
      (hX.tn_field (v := 0#u64) h hSg.sub ht (K := 3464#u64) (by simp) (by simp) (by simp))
      (fun c hc => F2 _ (hSg.sub _ (hX.1.snW c hc)))
      (fun y hy => F1 y hy _ (by simp) (by simp) (fun _ => by simp)) (fun c hc => F2 _ (hSg.sub _ (hX.1.syW c hc)))
      (fun c hc => F2 _ (hcΩ c hc).2.2.1) ei, tx2,
    SCsOK.keep' hS hX (by simp [hs2]) (fun y hy => by
        by_cases e : y = t
        · subst e; exact Or.inr sct
        · exact Or.inl (scy y hy e)) ecs
      (fun c hc => ⟨F2 _ (hcΩ c hc).2.2.1, F2 _ (hcΩ c hc).2.2.2.1, F2 _ (hcΩ c hc).2.2.2.2⟩)
      (fun c hc => F2 _ (spor_omega hX.1 hc)) (fun c hc => F2 _ (hSg.sub _ (hX.1.repW c hc))),
    ⟨hSg.sub, fun b hb => by simp only [hs2, LawfulStore.ksb_wr]; exact hSg.ks b hb,
      fun o h1 h2 => by simp only [hs2, LawfulStore.ksb_wr]; exact hSg.ksΩ o h1 h2⟩,
    ea, ec, ei, ecs, F1, F2, sct⟩
  · rw [ea] at haT ⊢; rw [scy _ haT hna]; exact hB.act haT
  · rw [ea] at h0; rw [ec]
    have hct : L.curW s ≠ t := fun e => hcur (by rw [ec]; exact e) (by rw [ea]; exact h0)
    rw [scy (L.curW s) h.curT hct]; exact hB.resume h0

/-! ## Scheduler steps with an exception set -/

theorem sched.enqueue.schX {X : Set U64} (s : S) (t : obj.Tcb) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T Ac s) (hS : SgOK st Ω Sg s) (ht : t ∈ T)
    (hr : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 → (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64)
    (hrun : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 → Runnable (L.mem s (stA t)))
    (hbd : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 → L.mem s (scA t) ≠ 0#u64)
    (hba : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 → L.mem s (scA t) ∈ Ac) :
    sched.enqueue st s t ⦃ s' => (∃ Q' R', SchedQueuesInvX st T Cs Ω H X s' Q' R') ∧ BoundInv st T Ac s' ∧
      Fr st T Sg s s' ∧ L.actionW s' = L.actionW s ∧ L.curW s' = L.curW s ∧ Keeps st T s s' ∧
      L.idleW s' = L.idleW s ∧ ∀ y ∈ T, y ≠ t → L.mem s' (inqA y) = L.mem s (inqA y) ⦄ := by
  have hc := h.aff t ht
  have hp := h.prio t ht
  refine WP.spec_mono (WP.spec_and (sched.enqueue.inv s t Q R h ht hr hrun)
    (sched.enqueue.foot s t _ h.tcbs ht hp (h.nodes _ hc) (h.nodes _ h.cur) ((h.ready _ hc).1.rel _ hp)
      (fun h0 => h.notQ ht h0 hc hp))) ?_
  rintro s' ⟨h1, hw, hinq⟩
  have hW : ∀ w ∈ t :: Q (L.mem s (affA t)) (L.mem s (prioA t)), w ∈ T := by
    intro w hw; rcases List.mem_cons.1 hw with rfl | hw
    · exact ht
    · exact h.memT hc hp hw
  obtain ⟨f, hi, ea, ec, ei⟩ := qfoot_keep h hS hW hc ht p128 hw
  obtain ⟨hsb, -, -⟩ := ext_qfoot h.tcbs hW (h.nodes _ hc) (h.nodes _ h.cur) ht hc h.cur hw
  have rf : (L.mem s' (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64 → (L.mem s (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64 := by
    intro hf; rw [hinq] at hf
    split_ifs at hf with e
    · exact hf
    · rw [or_qq_qr] at hf; exact hf
  refine ⟨⟨_, _, h1⟩, hB.qstep h f.sc hi ea ec ei ?_ (fun hf => Or.inr (Or.inl (rf hf))) (fun y hy => (hsb y hy).1)
    (fun _ _ => ?_), f, ea, ec, ⟨fun y hy => (hsb y hy).1, fun y hy hf => ?_⟩, ei, hi⟩
  · intro hf; rw [hinq] at hf
    by_cases e : (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64
    · exact Or.inl e
    · exact Or.inr (Or.inr (hbd (not_not.1 e)))
  · by_cases e : (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64
    · exact Or.inl (Or.inl e)
    · exact Or.inr (hba (not_not.1 e))
  · by_cases e : y = t
    · subst e; exact rf hf
    · rw [hi y hy e] at hf; exact hf

/-- `reschedule_required` with an exception set; the `IN_QUEUES` word of a
thread other than the switch-to candidate and the idle thread are kept. -/
theorem sched.reschedule_required.schX {X : Set U64} (s : S) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T Ac s) (hS : SgOK st Ω Sg s) :
    sched.reschedule_required st s ⦃ s' => (∃ Q' R', SchedQueuesInvX st T Cs Ω H X s' Q' R') ∧ BoundInv st T Ac s' ∧
      Fr st T Sg s s' ∧ L.actionW s' = 1#u64 ∧ L.curW s' = L.curW s ∧ Keeps st T s s' ∧ L.idleW s' = L.idleW s ∧
      ∀ y ∈ T, L.actionW s ≠ y → L.mem s' (inqA y) = L.mem s (inqA y) ⦄ := by
  unfold sched.reschedule_required
  step with sched.action.spec as ⟨act, act_post⟩
  refine WP.spec_bind (Pₘ := fun s1 => (∃ Q1 R1, SchedQueuesInvX st T Cs Ω H X s1 Q1 R1) ∧ BoundInv st T Ac s1 ∧
      Fr st T Sg s s1 ∧ L.curW s1 = L.curW s ∧ Keeps st T s s1 ∧ L.idleW s1 = L.idleW s ∧
      ∀ y ∈ T, L.actionW s ≠ y → L.mem s1 (inqA y) = L.mem s (inqA y)) ?_ ?_
  · split
    · split
      · rename_i h1 h2
        have hT : act ∈ T := by
          rcases h.action with e | e | e
          · rw [← act_post] at e; exfalso; rw [e, resume_val] at h1; simp at h1
          · rw [← act_post] at e; exfalso; rw [e, choose_val] at h2; simp at h2
          · rw [← act_post] at e; exact e
        have hrun : Runnable (L.mem s (stA act)) := by
          have := (h.actOK (act_post ▸ hT)).1; rw [← act_post] at this; exact this
        have hbd : L.mem s (scA act) ≠ 0#u64 := by
          have := hB.act (act_post ▸ hT); rw [← act_post] at this; exact this
        step with sched.is_schedulable.spec as ⟨b, hb⟩
        split
        · exact WP.spec_mono (sched.enqueue.schX s act Q R h hB hS hT (fun _ => hb ‹_›) (fun _ => hrun)
            (fun _ => hbd) (fun _ => hB.sact act hT (Or.inr (Or.inr (Or.inl act_post.symm))) hbd)) fun s1 h1 => ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2.1, h1.2.2.2.2.2.2.1,
              fun y hy hne => h1.2.2.2.2.2.2.2 y hy (fun e => hne (by rw [← act_post, e]))⟩
        · exact (WP.spec_ok _).2 ⟨⟨Q, R, h⟩, hB, Fr.refl _ _, rfl, Keeps.refl _, rfl, fun _ _ _ => rfl⟩
      · exact (WP.spec_ok _).2 ⟨⟨Q, R, h⟩, hB, Fr.refl _ _, rfl, Keeps.refl _, rfl, fun _ _ _ => rfl⟩
    · exact (WP.spec_ok _).2 ⟨⟨Q, R, h⟩, hB, Fr.refl _ _, rfl, Keeps.refl _, rfl, fun _ _ _ => rfl⟩
  · rintro s1 ⟨⟨Q1, R1, h1⟩, hB1, f1, ec1, k1, ei1, iq1⟩
    refine WP.spec_mono (sched.set_action.spec s1 _) fun s2 e2 => ?_
    subst e2
    rw [choose_val]
    obtain ⟨j1, ej⟩ := inv_set_action h1 (Or.inr (Or.inl rfl)) (fun hT => absurd hT (one_notT h))
    have hB2 := hB1.wr_node h1 (o := layout.node.SCHED_ACTION) (v := 1#u64) (by rw [act_val]; omega) (by rw [act_val])
      (by rw [act_val]; omega) (fun _ => ⟨fun hT => absurd hT (one_notT h), fun e => by simp at e⟩)
      (fun e => by rw [act_val] at e; omega) (fun _ hT => absurd hT (one_notT h))
    have f := fr_node (Sg := Sg) (hi8 := fun _ => by simp [layout.node.SCHED_ACTION, layout.node.REPROGRAM, layout.node.CUR_THREAD]) (v := 1#u64) h1 (hS.fr f1) h1.cur (by rw [act_val]; omega) (by rw [act_val])
      (hto := ⟨by rw [act_val]; omega, by rw [act_val]; omega⟩)
      (fun _ => by rw [act_val]; omega)
    have ec := rd_cur_node (v := 1#u64) h1 (by rw [act_val]; omega) (by rw [act_val]) (by rw [curth0]; omega)
      (by rw [curth0]) (by rw [act_val, curth0]; omega)
    have ei := rd_cur_node (v := 1#u64) h1 (by rw [act_val]; omega) (by rw [act_val]) (by rw [idle8]; omega)
      (by rw [idle8]) (by rw [act_val, idle8]; omega)
    have fk : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        L.mem (L.wr s1 (L.nodeAt s1 (L.cpu s1) layout.node.SCHED_ACTION) 1#u64) (core.num.U64.wrapping_add y K) =
          L.mem s1 (core.num.U64.wrapping_add y K) := fun y hy K hK hK8 =>
      field_wr_node h1 h1.cur (by rw [act_val]; omega) (by rw [act_val]) hy hK hK8
    refine ⟨⟨Q1, R1, j1⟩, hB2, f1.trans f, ej, ec.trans ec1, k1.trans ⟨fun y hy => ?_, fun y hy hf => ?_⟩,
      ei.trans ei1, fun y hy hne => ?_⟩
    · rw [stA_eq, fk y hy _ (by simp) (by simp), ← stA_eq]
    · rw [inqA_eq, fk y hy _ (by simp) (by simp), ← inqA_eq] at hf; exact hf
    · rw [inqA_eq, fk y hy _ (by simp) (by simp), ← inqA_eq]; exact iq1 y hy hne

/-- a64: `reschedule_required` keeps every TCB field outside the queue links (`field_qfoot`), e.g.
`RUN_VCPU`: its `enqueue` writes queue words, its `set_action` a node word. -/
theorem sched.reschedule_required.fldX {X : Set U64} (s : S) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T Ac s) (hS : SgOK st Ω Sg s) {K : U64}
    (hK : K.val < 4096) (hK8 : K.val % 8 = 0)
    (hKl : K.val ≠ 3480 ∧ K.val ≠ 3488 ∧ K.val ≠ 3496 ∧ K.val ≠ 3504) (hKq : K.val ≠ 3592) :
    sched.reschedule_required st s ⦃ s' => ∀ y ∈ T,
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) ⦄ := by
  unfold sched.reschedule_required
  step with sched.action.spec as ⟨act, act_post⟩
  refine WP.spec_bind (Pₘ := fun s1 => (∃ Q1 R1, SchedQueuesInvX st T Cs Ω H X s1 Q1 R1) ∧
      ∀ y ∈ T, L.mem s1 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ?_ ?_
  · split
    · split
      · rename_i h1 h2
        have hT : act ∈ T := by
          rcases h.action with e | e | e
          · rw [← act_post] at e; exfalso; rw [e, resume_val] at h1; simp at h1
          · rw [← act_post] at e; exfalso; rw [e, choose_val] at h2; simp at h2
          · rw [← act_post] at e; exact e
        have hrun : Runnable (L.mem s (stA act)) := by
          have := (h.actOK (act_post ▸ hT)).1; rw [← act_post] at this; exact this
        have hbd : L.mem s (scA act) ≠ 0#u64 := by
          have := hB.act (act_post ▸ hT); rw [← act_post] at this; exact this
        step with sched.is_schedulable.spec as ⟨b, hb⟩
        split
        · have hc := h.aff act hT
          have hp := h.prio act hT
          refine WP.spec_mono (WP.spec_and (sched.enqueue.schX s act Q R h hB hS hT (fun _ => hb ‹_›)
            (fun _ => hrun) (fun _ => hbd) (fun _ => hB.sact act hT (Or.inr (Or.inr (Or.inl act_post.symm))) hbd))
            (sched.enqueue.foot s act _ h.tcbs hT hp (h.nodes _ hc) (h.nodes _ h.cur) ((h.ready _ hc).1.rel _ hp)
              (fun h0 => h.notQ hT h0 hc hp))) fun s1 hh => ?_
          obtain ⟨⟨p1, -⟩, hw, -⟩ := hh
          have hW : ∀ w ∈ act :: Q (L.mem s (affA act)) (L.mem s (prioA act)), w ∈ T := by
            intro w hw; rcases List.mem_cons.1 hw with rfl | hw
            · exact hT
            · exact h.memT hc hp hw
          exact ⟨p1, fun y hy => field_qfoot h.tcbs hW (h.nodes _ hc) (h.nodes _ h.cur) hT hw hy hK hK8 hKl
            (fun _ => hKq)⟩
        · exact (WP.spec_ok _).2 ⟨⟨Q, R, h⟩, fun _ _ => rfl⟩
      · exact (WP.spec_ok _).2 ⟨⟨Q, R, h⟩, fun _ _ => rfl⟩
    · exact (WP.spec_ok _).2 ⟨⟨Q, R, h⟩, fun _ _ => rfl⟩
  · rintro s1 ⟨⟨Q1, R1, h1⟩, e1⟩
    refine WP.spec_mono (sched.set_action.spec s1 _) fun s2 e2 => ?_
    subst e2
    intro y hy
    rw [field_wr_node h1 h1.cur (by rw [act_val]; omega) (by rw [act_val]) hy hK hK8]
    exact e1 y hy

/-! ## `donate` -/

/-- The IPC invariants with an exception set. -/
def BlkOKX (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (Ac : Set U64) (X : Set U64) (s : S) : Prop :=
  (∃ Q R, SchedQueuesInvX st T Cs Ω H X s Q R) ∧ BoundInv st T Ac s ∧ XInv st T Cs Ω Sg Rp Scs Nt Z s ∧
    SCsOK st T Ω Sg Scs Z Ac s ∧ SgOK st Ω Sg s

/-- `XInv` with `ScAff` off the thread `d` (`XInv0`, `TSc` and `ScAffX d`): the
states between the SC write that binds `d` (`donate`, `bind_tcb`), or
configure's `CORE` write of `d`'s SC, and `migrate_tcb`'s affinity write. -/
def XInvW (st : machine.Store S) [L : LawfulStore st] (T Cs Ω Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (d : U64)
    (s : S) : Prop :=
  XInv0 st T Cs Ω Sg Rp Scs Nt Z s ∧ TSc st Scs s ∧ ScAffX st T d s

theorem XInv.w {s : S} (h : XInv st T Cs Ω Sg Rp Scs Nt Z s) (d : U64) : XInvW st T Cs Ω Sg Rp Scs Nt Z d s :=
  ⟨h.x0, h.2.2.tsc, h.2.2.aff.x d⟩

/-- `BlkOKX` with `XInvW d` for `XInv`. -/
def BlkOKW (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (Ac : Set U64) (X : Set U64) (d : U64) (s : S) : Prop :=
  (∃ Q R, SchedQueuesInvX st T Cs Ω H X s Q R) ∧ BoundInv st T Ac s ∧ XInvW st T Cs Ω Sg Rp Scs Nt Z d s ∧
    SCsOK st T Ω Sg Scs Z Ac s ∧ SgOK st Ω Sg s

/-- `XInv.fr` for `XInvW`. -/
theorem XInvW.fr {s s' : S} {d : U64} (hX : XInvW st T Cs Ω Sg Rp Scs Nt Z d s) (f : Fr st T Sg s s') :
    XInvW st T Cs Ω Sg Rp Scs Nt Z d s' :=
  ⟨hX.1.fr f, hX.2.1.keep hX.1.2.2.yt.1 (fun c hc => f.sig _ (hX.1.1.fixW c hc).1) f.sc,
    hX.2.2.keep (fun t ht _ h0 => (hX.1.2.2.bound t ht h0).1) (fun t ht _ => f.sc t ht)
      (fun c hc => f.sig _ (hX.1.1.fixW c hc).2) (fun t ht _ => f.aff t ht)⟩

/-- `XInv.writes` for `XInvW`. -/
theorem XInvW.writes {s s' : S} {B : U64 → Prop} {d : U64} (hX : XInvW st T Cs Ω Sg Rp Scs Nt Z d s)
    (hT : TcbPlaced T) (hw : WritesIn st s s' B) (hB : ∀ b, B b → ¬ Prot T Rp Scs Nt b) (hcs : L.cscW s' ∈ Scs)
    (htn : TimerOK st T Cs s' ∧ NtbOK st T Nt s' ∧ TimerRB st T Cs s' ∧ (∀ n ∈ Nt, L.mem s' (ntfnBtA n) = L.mem s (ntfnBtA n))) (hiw : L.idleW s' = L.idleW s) :
    XInvW st T Cs Ω Sg Rp Scs Nt Z d s' := by
  obtain ⟨hX0, htc, haf⟩ := hX
  have k : ∀ b, Prot T Rp Scs Nt b → L.mem s' b = L.mem s b := fun b hb =>
    hw.mem_eq (hX0.1.aligned hT hb) (fun h => hB b h hb)
  have hsc : ∀ t ∈ T, L.mem s' (scA t) = L.mem s (scA t) := fun t ht => k _ (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inl rfl⟩)))
  have hfx : ∀ c ∈ Scs, L.mem s' (scTcbA c) = L.mem s (scTcbA c) ∧ L.mem s' (scCoreA c) = L.mem s (scCoreA c) :=
    fun c hc => ⟨k _ (Or.inr (Or.inl ⟨c, hc, Or.inl rfl⟩)), k _ (Or.inr (Or.inl ⟨c, hc, Or.inr (Or.inl rfl)⟩))⟩
  refine ⟨hX0.keep (fun r hr => ⟨k _ (Or.inl ⟨r, hr, Or.inl rfl⟩), k _ (Or.inl ⟨r, hr, Or.inr (Or.inl rfl)⟩),
      k _ (Or.inl ⟨r, hr, Or.inr (Or.inr rfl)⟩)⟩) hfx hsc
    (fun t ht => k _ (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inr (Or.inl rfl)⟩))))
    (fun t ht => k _ (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inr (Or.inr (Or.inl rfl))⟩)))) hcs
    (fun c hc => k _ (Or.inr (Or.inl ⟨c, hc, Or.inr (Or.inr (Or.inl rfl))⟩)))
    (fun t ht => k _ (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩))))
    (fun n hn => k _ (Or.inr (Or.inr (Or.inr ⟨n, hn, rfl⟩)))) htn
    (fun c hc => k _ (Or.inr (Or.inl ⟨c, hc, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩)))
    (fun t ht => k _ (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩))))
    (fun c hc => k _ (Or.inr (Or.inl ⟨c, hc, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩)))
    (fun c hc => k _ (Or.inr (Or.inl ⟨c, hc, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))⟩))) hiw,
    htc.keep hX0.2.2.yt.1 (fun c hc => (hfx c hc).1) hsc,
    haf.keep (fun t ht _ h0 => (hX0.2.2.bound t ht h0).1) (fun t ht _ => hsc t ht) (fun c hc => (hfx c hc).2)
      (fun t ht _ => k _ (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))⟩))))⟩

/-- `bx_wr` for `XInvW`. -/
theorem bx_wrW {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {a v d : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T Ac s) (hX : XInvW st T Cs Ω Sg Rp Scs Nt Z d s)
    (ha : Aligned a) (hP : ¬ Prot T Rp Scs Nt a) (hsi : ∀ y ∈ T, a.val ≠ (scA y).val ∧ a.val ≠ (inqA y).val)
    (hn : ∀ o : U64, (o.val = 0 ∨ o.val = 8 ∨ o.val = 16 ∨ o.val = 24) → a.val ≠ (L.nodeAt s (L.cpu s) o).val)
    (htn : TimerOK st T Cs (L.wr s a v) ∧ NtbOK st T Nt (L.wr s a v) ∧ TimerRB st T Cs (L.wr s a v) ∧ (∀ n ∈ Nt, L.mem (L.wr s a v) (ntfnBtA n) = L.mem s (ntfnBtA n))) :
    BoundInv st T Ac (L.wr s a v) ∧ XInvW st T Cs Ω Sg Rp Scs Nt Z d (L.wr s a v) := by
  obtain ⟨hB', ecs⟩ := bnd_wr (v := v) h hB ha hsi hn
    (fun y hy e => hP (Or.inr (Or.inr (Or.inl ⟨_, hy, Or.inr (Or.inr (Or.inl (UScalar.eq_of_val_eq e)))⟩))))
  refine ⟨hB', hX.writes h.tcbs (writesIn_wr (v := v) ha) (fun b hb => hb ▸ hP) (by rw [ecs]; exact hX.1.2.2.cur) htn ?_⟩
  unfold LawfulStore.idleW; rw [LawfulStore.cpu_wr, nodeAt_wr]
  exact L.mem_wr_ne ha (nodeAt_aligned (h.nodes _ h.cur) (by rw [idle8]; omega) (by rw [idle8]))
    (hn _ (Or.inr (Or.inl idle8)))

/-- `bx_field'` for `XInvW`. -/
theorem bx_fieldW' {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {y K v d : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T Ac s) (hX : XInvW st T Cs Ω Sg Rp Scs Nt Z d s)
    (hsub : ∀ b ∈ Sg, b ∈ Ω) (hy : y ∈ T) (hK : K.val < 4096) (hK8 : K.val % 8 = 0)
    (hKn : K.val ≠ 3464 ∧ K.val ≠ 3360 ∧ K.val ≠ 3328 ∧ K.val ≠ 3592 ∧ K.val ≠ 3368 ∧ K.val ≠ 3472 ∧ K.val ≠ 3520)
    (htn : TimerOK st T Cs (L.wr s (core.num.U64.wrapping_add y K) v) ∧
      NtbOK st T Nt (L.wr s (core.num.U64.wrapping_add y K) v) ∧
      TimerRB st T Cs (L.wr s (core.num.U64.wrapping_add y K) v) ∧
      (∀ n ∈ Nt, L.mem (L.wr s (core.num.U64.wrapping_add y K) v) (ntfnBtA n) = L.mem s (ntfnBtA n))) :
    BoundInv st T Ac (L.wr s (core.num.U64.wrapping_add y K) v) ∧
      XInvW st T Cs Ω Sg Rp Scs Nt Z d (L.wr s (core.num.U64.wrapping_add y K) v) := by
  have hya := h.tcbs y hy
  have hN' := h.nodes _ h.cur
  refine bx_wrW h hB hX (field_aligned hya hK hK8) ?_ (fun y' hy' => ⟨?_, ?_⟩) (fun o ho => ?_) htn
  · intro hp
    rcases hX.1.1.prot_cases hsub hp with hm | ⟨t', ht', K', hK', e⟩
    · exact out_ne_field (h.omega _ hm) hy hya hK rfl
    · rcases hp with ⟨r, hr, e'⟩ | ⟨c, hc, e'⟩ | ⟨u, hu, e'⟩ | ⟨n, hn, e'⟩
      rotate_right
      · have hm : core.num.U64.wrapping_add y K ∈ Ω := by rw [e']; exact hsub _ (hX.1.1.ntW n hn)
        exact out_ne_field (h.omega _ hm) hy hya hK rfl
      · have hm : core.num.U64.wrapping_add y K ∈ Ω := by
          rcases e' with e' | e' | e' <;> rw [e']
          · exact hsub _ (hX.1.1.tcbW hr)
          · exact hsub _ (hX.1.1.prevW hr)
          · exact hsub _ (hX.1.1.nextW hr)
        exact out_ne_field (h.omega _ hm) hy hya hK rfl
      · have hm : core.num.U64.wrapping_add y K ∈ Ω := by
          rcases e' with e' | e' | e' | e' | e' | e' <;> rw [e']
          · exact hsub _ (hX.1.1.fixW c hc).1
          · exact hsub _ (hX.1.1.fixW c hc).2
          · exact hsub _ (hX.1.1.repW c hc)
          · exact hsub _ (hX.1.1.snW c hc)
          · exact hsub _ (hX.1.1.syW c hc)
          · exact hsub _ (hX.1.1.mxW c hc)
        exact out_ne_field (h.omega _ hm) hy hya hK rfl
      · rcases e' with e' | e' | e' | e' | e' | e'
        · rw [scA_eq] at e'
          exact field_ne hya (h.tcbs u hu) hK (by simp) (fun _ => by simp; omega) e'
        · exact field_ne hya (h.tcbs u hu) hK (by simp) (fun _ => by simp; omega) e'
        · rw [stA_eq] at e'
          exact field_ne hya (h.tcbs u hu) hK (by simp) (fun _ => by simp; omega) e'
        · exact field_ne hya (h.tcbs u hu) hK (by simp) (fun _ => by simp; omega) e'
        · exact field_ne hya (h.tcbs u hu) hK (by simp) (fun _ => by simp; omega) e'
        · exact field_ne hya (h.tcbs u hu) hK (by simp) (fun _ => by simp; omega) e'
  · rw [scA_eq]
    exact fun e => field_ne hya (h.tcbs y' hy') hK (by simp) (fun _ => by simp; omega) (UScalar.eq_of_val_eq e)
  · rw [inqA_eq]
    exact fun e => field_ne hya (h.tcbs y' hy') hK (by simp) (fun _ => by simp; omega) (UScalar.eq_of_val_eq e)
  · exact fun e => node_ne_field hN' (by omega) hy hya hK (UScalar.eq_of_val_eq e).symm

/-- The two writes of `donate`'s second half (and of `bind_tcb`, in the other
order): the SC `sc` (bound to no thread) names `dst` (with no SC, in no ready
or release queue), and `dst` gets `sc`. -/
theorem donate_pair {X : Set U64} {s6 : S} {sc dst : U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h6 : SchedQueuesInvX st T Cs Ω H X s6 Q R) (hB6 : BoundInv st T Ac s6) (hX6 : XInv0 st T Cs Ω Sg Rp Scs Nt Z s6)
    (htx6 : TScX st Scs sc s6) (haf6 : ScAff st T s6) (hd0 : L.mem s6 (scA dst) = 0#u64)
    (hS6 : SCsOK st T Ω Sg Scs Z Ac s6) (hSg6 : SgOK st Ω Sg s6) (hto : dst ∈ T)
    (hsc : sc ∈ Scs) (hsc0 : sc ≠ 0#u64) (hnb : ∀ y ∈ T, L.mem s6 (scA y) ≠ sc)
    (hcore : L.mem s6 (scCoreA sc) ∈ Cs)
    (hdisj : sc ≠ L.cscW s6 → ∀ b, InSC sc (Z sc) b → Outside b (L.cscW s6) (Z (L.cscW s6)))
    (hsA : Sch st s6 dst → sc ∈ Ac) (hdi : L.idleW s6 ≠ dst) :
    SchedQueuesInvX st T Cs Ω H X (L.wr (L.wr s6 (scTcbA sc) dst) (scA dst) sc) Q R ∧
      BoundInv st T Ac (L.wr (L.wr s6 (scTcbA sc) dst) (scA dst) sc) ∧
      XInvW st T Cs Ω Sg Rp Scs Nt Z dst (L.wr (L.wr s6 (scTcbA sc) dst) (scA dst) sc) ∧
      SCsOK st T Ω Sg Scs Z Ac (L.wr (L.wr s6 (scTcbA sc) dst) (scA dst) sc) ∧
      SgOK st Ω Sg (L.wr (L.wr s6 (scTcbA sc) dst) (scA dst) sc) ∧
      TmFr st T Cs Nt s6 (L.wr (L.wr s6 (scTcbA sc) dst) (scA dst) sc) ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (y = dst → K.val ≠ 3464) →
        L.mem (L.wr (L.wr s6 (scTcbA sc) dst) (scA dst) sc) (core.num.U64.wrapping_add y K) =
          L.mem s6 (core.num.U64.wrapping_add y K)) ∧
      L.mem (L.wr (L.wr s6 (scTcbA sc) dst) (scA dst) sc) (scCoreA sc) = L.mem s6 (scCoreA sc) ∧
      L.mem (L.wr (L.wr s6 (scTcbA sc) dst) (scA dst) sc) (scA dst) = sc ∧
      L.mem (L.wr (L.wr s6 (scTcbA sc) dst) (scA dst) sc) (scTcbA sc) = dst ∧
      L.actionW (L.wr (L.wr s6 (scTcbA sc) dst) (scA dst) sc) = L.actionW s6 := by
  have hT := h6.tcbs
  have hta := hT dst hto
  have hN := h6.nodes _ h6.cur
  have hO := hX6.1
  have hv0 := sc_facts hO hsc
  obtain ⟨hrΩ, hcΩ⟩ := objs_omega hO hSg6.sub
  have hm : scTcbA sc ∈ Ω := hSg6.sub _ (hO.fixW sc hsc).1
  have ho := h6.omega _ hm
  obtain ⟨s7, e7⟩ : ∃ s7, s7 = L.wr s6 (scTcbA sc) dst := ⟨_, rfl⟩
  have tm7 : TmFr st T Cs Nt s6 s7 := by
    rw [e7]
    exact TmFr.wr hT h6.nodes hO ho.1 (notTmW_omega hT h6.nodes ho
      (fun n hn => by
        rw [hv0.2.1, ntfnBtA_val (hO.ntP n hn)]; have := hO.ntOSc n hn sc hsc; have := hv0.1; omega))
  -- the `TCB` word of `sc`
  obtain ⟨h7, a7, f7⟩ := omega_wr (v := dst) h6 hm
  have hB7 := BoundInv.owr (v := dst) h6 hB6 hm
  have hX7 := XInv.set_sctcb (v := dst) h6 hX6 hSg6.sub hsc hnb (fun _ => hto) (fun e => absurd e.symm hdi)
  have nh : ∀ c ∈ Scs, (scTcbA sc).val ≠ (maxA c).val ∧ (scTcbA sc).val ≠ (headA c).val ∧
      (scTcbA sc).val ≠ (tailA c).val := by
    intro c hc
    obtain ⟨h128, -, -, e3, e4, e5, -⟩ := sc_facts hO hc
    rw [hv0.2.1, e3, e4, e5]
    by_cases hcc : c = sc
    · subst hcc; omega
    · have := hO.scDisj c hc sc hsc hcc; have := hv0.1; omega
  have tx7 := TScX.set_sctcb (v := dst) h6 hX6.1 hSg6.sub hsc htx6 hX6.2.2.yt.1
  have hS7 := SCsOK.wr' (v := dst) h6 hS6 hX6.1 ho.1
    (fun y hy => (out_ne_field (K := 3464#u64) ho hy (hT y hy) (by simp)).symm)
    (out_ne_node ho h6.cur hN (by simp [layout.node.CUR_SC])).symm nh
    (fun c hc => by
      obtain ⟨hPc, hzc⟩ := hO.sc c hc
      rw [hv0.2.1, sporA_val hPc hzc]
      by_cases hcc : c = sc
      · subst hcc; omega
      · have := hO.scDisj c hc sc hsc hcc; have := hv0.1; have := (sc_facts hO hc).1; omega)
    (fun c hc e => absurd e (scw_ne_screp hO hsc hv0.2.1 (by omega) (by omega) c hc))
  have hsA7 : Sch st s7 dst → sc ∈ Ac := fun hS => hsA (Sch.wr_out h6 hm hto (by rw [← e7]; exact hS))
  rw [← e7] at h7 a7 f7 hB7 hX7 hS7 tx7
  have hSg7 : SgOK st Ω Sg s7 := ⟨hSg6.sub, fun b hb => by rw [e7, L.ksb_wr]; exact hSg6.ks b hb,
    fun o h1 h2 => by rw [e7, L.ksb_wr]; exact hSg6.ksΩ o h1 h2⟩
  have t7 : L.mem s7 (scTcbA sc) = dst := by rw [e7]; exact L.mem_wr_same ho.1
  have k7 : ∀ a ∈ Ω, a.val ≠ (scTcbA sc).val → L.mem s7 a = L.mem s6 a := fun a ha hne => by
    rw [e7]; exact L.mem_wr_ne ho.1 (h6.omega a ha).1 (fun e => hne e.symm)
  have ecs7 : L.cscW s7 = L.cscW s6 := by
    unfold LawfulStore.cscW; rw [e7, nodeA_wr]
    exact L.mem_wr_ne ho.1 (nodeAt_aligned hN (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))
      (out_ne_node ho h6.cur hN (by simp [layout.node.CUR_SC])).symm
  have core7 : L.mem s7 (scCoreA sc) = L.mem s6 (scCoreA sc) :=
    k7 _ (hcΩ _ hsc).2.1 (by rw [hv0.2.1, hv0.2.2.1]; omega)
  -- `dst` gets the SC
  obtain ⟨s8, e8⟩ : ∃ s8, s8 = L.wr s7 (scA dst) sc := ⟨_, rfl⟩
  have tm8 : TmFr st T Cs Nt s7 s8 := by
    rw [e8]
    exact TmFr.wr hT h7.nodes hX7.1 (scA_aligned hta)
      (notTmW_field (K := 3464#u64) hT h7.nodes (fun n hn => h7.omega _ (hSg6.sub _ (hO.ntB n hn).2)) hto
        (by simp) (by simp))
  have h8 : SchedQueuesInvX st T Cs Ω H X s8 Q R := by
    rw [e8]; exact inv_wr_field (K := 3464#u64) h7 hto (by simp) (by simp) (by simp)
  have hB8 : BoundInv st T Ac s8 := by rw [e8]; exact BoundInv.set_sc h7 hB7 hto hsc0 hsA7
  have hX8 : XInv0 st T Cs Ω Sg Rp Scs Nt Z s8 ∧ TSc st Scs s8 := by
    have huq : ∀ c ∈ Scs, c ≠ 0#u64 → L.mem s7 (scTcbA c) = dst → c = sc := fun c hc hc0 e => by
      by_contra hne
      have e1 : L.mem s7 (scTcbA c) = L.mem s6 (scTcbA c) := k7 _ (hcΩ c hc).1 (by
        rw [hv0.2.1, (sc_facts hO hc).2.1]
        have := hO.scDisj c hc sc hsc hne; have := (sc_facts hO hc).1; have := hv0.1; omega)
      rw [e1] at e
      have := htx6 c hc hne hc0 (by rw [e]; exact fun e0 => (hT dst hto).ne0 (by rw [e0]; rfl))
      rw [e, hd0] at this; exact hc0 this.symm
    rw [e8]; exact ⟨XInv.bind h7 hX7 hSg6.sub hto hsc t7 (by rw [core7]; exact hcore),
      TSc.bind h7 hX7.1 hSg6.sub hto tx7 t7 huq hX7.2.2.yt.1⟩
  have hS8 : SCsOK st T Ω Sg Scs Z Ac s8 := by
    rw [e8]; exact SCsOK.bind h7 hS7 hto (by rw [ecs7]; exact hdisj)
  have hSg8 : SgOK st Ω Sg s8 := ⟨hSg6.sub, fun b hb => by rw [e8, L.ksb_wr]; exact hSg7.ks b hb,
    fun o h1 h2 => by rw [e8, L.ksb_wr]; exact hSg7.ksΩ o h1 h2⟩
  have fld8 : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (y = dst → K.val ≠ 3464) →
      L.mem s8 (core.num.U64.wrapping_add y K) = L.mem s6 (core.num.U64.wrapping_add y K) := by
    intro y hy K hK hK8 hne
    rw [e8, L.mem_wr_ne (scA_aligned hta) (field_aligned (hT y hy) hK hK8)
      (fun e => field_ne (K1 := 3464#u64) hta (hT y hy) (by simp) hK
        (fun e' => by subst e'; exact fun h' => hne rfl h'.symm) (UScalar.eq_of_val_eq e))]
    exact f7 y hy K hK hK8
  have core8 : L.mem s8 (scCoreA sc) = L.mem s6 (scCoreA sc) := by
    rw [e8, L.mem_wr_ne (scA_aligned hta) (h7.omega _ (hcΩ _ hsc).2.1).1
      (fun e => out_ne_field (K := 3464#u64) (h7.omega _ (hcΩ _ hsc).2.1) hto hta (by simp) e)]
    exact core7
  have sc8 : L.mem s8 (scA dst) = sc := by rw [e8]; exact L.mem_wr_same (scA_aligned hta)
  have t8 : L.mem s8 (scTcbA sc) = dst := by
    rw [e8, L.mem_wr_ne (scA_aligned hta) ho.1 (fun e => out_ne_field (K := 3464#u64) ho hto hta (by simp) e)]
    exact t7
  have a8 : L.actionW s8 = L.actionW s6 := by
    rw [e8, act_wr_field (K := 3464#u64) (a := scA dst) (h7.nodes _ h7.cur) hto hta rfl (by simp) (by simp)]
    exact a7
  have co8 : ∀ c ∈ Scs, L.mem s8 (scCoreA c) = L.mem s6 (scCoreA c) := fun c hc => by
    have hm' := h7.omega _ (hcΩ _ hc).2.1
    rw [e8, L.mem_wr_ne (scA_aligned hta) hm'.1 (fun e => out_ne_field (K := 3464#u64) hm' hto hta (by simp) e)]
    refine k7 _ (hcΩ _ hc).2.1 ?_
    rw [hv0.2.1, (sc_facts hO hc).2.2.1]
    by_cases hcc : c = sc
    · subst hcc; omega
    · have := hO.scDisj c hc sc hsc hcc; have := (sc_facts hO hc).1; have := hv0.1; omega
  have aff8 : ScAffX st T dst s8 := ScAff.pairX haf6 (fun t ht h0 => (hX6.2.2.bound t ht h0).1)
    (fun t ht hne => by rw [scA_eq]; exact fld8 t ht _ (by simp) (by simp) (fun e => absurd e hne))
    co8 (fun t ht => fld8 t ht _ (by simp) (by simp) (fun _ => by simp))
  rw [← e7, ← e8]
  exact ⟨h8, hB8, ⟨hX8.1, hX8.2, aff8⟩, hS8, hSg8, tm7.trans tm8, fld8, core8, sc8, t8, a8⟩

/-! ## The debug lists

`migrate_tcb` moves a thread from its old core's debug list to its new
core's. The lemmas here keep the IPC invariants with an exception set, the
timer frame `TmFr`, and say that only the debug-list words change. -/

/-- The debug-list words: the TCBs' debug links and the nodes' list heads. -/
def DbgW (st : machine.Store S) [L : LawfulStore st] (T Cs : Set U64) (s0 : S) (b : U64) : Prop :=
  (∃ y ∈ T, b = dnA y ∨ b = dpA y) ∨ (∃ c ∈ Cs, b = L.nodeAt s0 c layout.node.DEBUG_TCBS)

theorem DbgW.ksb {s0 s1 : S} {b : U64} (hk : L.ksb s1 = L.ksb s0) (h : DbgW st T Cs s1 b) :
    DbgW st T Cs s0 b := by
  rcases h with h | ⟨c, hc, e⟩
  · exact Or.inl h
  · exact Or.inr ⟨c, hc, by rw [e, nodeAt_of_ksb hk]⟩

theorem DbgW.trans {s₁ s₂ s₃ : S} (h₁ : WritesIn st s₁ s₂ (DbgW st T Cs s₁))
    (h₂ : WritesIn st s₂ s₃ (DbgW st T Cs s₂)) : WritesIn st s₁ s₃ (DbgW st T Cs s₁) :=
  WritesIn.mono (WritesIn.trans h₁ h₂) fun b hb => by
    rcases hb with hb | ⟨y, hy, e⟩ | ⟨c, hc, e⟩
    · exact hb
    · exact Or.inl ⟨y, hy, e⟩
    · exact Or.inr ⟨c, hc, by rw [e, nodeAt_of_ksb h₁.1]⟩

/-- Writes that avoid the debug-list words keep the debug lists typed. -/
theorem DbgTz.of_writes {s s' : S} {B : U64 → Prop} (hT : TcbPlaced T) (hN : ∀ c ∈ Cs, NodePlaced st T s c)
    (hw : WritesIn st s s' B) (hB : ∀ b, Aligned b → B b → ¬ DbgW st T Cs s b) (D : DbgTz st T Cs s) :
    DbgTz st T Cs s' := by
  refine ⟨fun y hy => ?_, fun y hy => ?_, fun c hc => ?_⟩
  · have ha : Aligned (dnA y) := field_aligned (K := 3576#u64) (hT y hy) (by simp) (by simp)
    rw [hw.mem_eq ha (fun hb => hB _ ha hb (Or.inl ⟨y, hy, Or.inl rfl⟩))]
    exact D.dn y hy
  · have ha : Aligned (dpA y) := field_aligned (K := 3584#u64) (hT y hy) (by simp) (by simp)
    rw [hw.mem_eq ha (fun hb => hB _ ha hb (Or.inl ⟨y, hy, Or.inr rfl⟩))]
    exact D.dp y hy
  · have ha : Aligned (L.nodeAt s c layout.node.DEBUG_TCBS) :=
      nodeAt_aligned (hN c hc) (by simp [debug_val]) (by simp [debug_val])
    rw [nodeAt_of_ksb hw.1, hw.mem_eq ha (fun hb => hB _ ha hb (Or.inr ⟨c, hc, rfl⟩))]
    exact D.dh c hc

/-- A write of a word that is no debug-list word keeps the debug lists typed. -/
theorem DbgTz.wr_out {s : S} {a v : U64} (hT : TcbPlaced T) (hN : ∀ c ∈ Cs, NodePlaced st T s c) (ha : Aligned a)
    (hna : ¬ DbgW st T Cs s a) (D : DbgTz st T Cs s) : DbgTz st T Cs (L.wr s a v) :=
  DbgTz.of_writes hT hN (writesIn_wr ha) (fun b _ hb => by subst hb; exact hna) D

/-- A TCB field other than the debug links is no debug-list word. -/
theorem notDbgW_field {s : S} {y K : U64} (hT : TcbPlaced T) (hN : ∀ c ∈ Cs, NodePlaced st T s c) (hy : y ∈ T)
    (hK : K.val < 4096) (hKd : K.val ≠ 3576 ∧ K.val ≠ 3584) :
    ¬ DbgW st T Cs s (core.num.U64.wrapping_add y K) := by
  have e1 : (3576#u64).val = 3576 := by simp
  have e2 : (3584#u64).val = 3584 := by simp
  rintro (⟨y', hy', e | e⟩ | ⟨c, hc, e⟩)
  · exact field_ne (K2 := 3576#u64) (hT y hy) (hT y' hy') hK (by omega) (fun _ => by omega) e
  · exact field_ne (K2 := 3584#u64) (hT y hy) (hT y' hy') hK (by omega) (fun _ => by omega) e
  · exact node_ne_field (hN c hc) (by simp [debug_val]) hy (hT y hy) hK e.symm

/-- A word outside the TCBs and nodes is no debug-list word. -/
theorem notDbgW_out {s : S} {a : U64} (hT : TcbPlaced T) (hN : ∀ c ∈ Cs, NodePlaced st T s c)
    (ha : OutsideObjs st T Cs s a) : ¬ DbgW st T Cs s a := by
  rintro (⟨y, hy, e | e⟩ | ⟨c, hc, e⟩)
  · exact out_ne_field (K := 3576#u64) ha hy (hT y hy) (by simp) (congrArg UScalar.val e).symm
  · exact out_ne_field (K := 3584#u64) ha hy (hT y hy) (by simp) (congrArg UScalar.val e).symm
  · exact out_ne_node ha hc (hN c hc) (by simp [debug_val]) (congrArg UScalar.val e).symm

/-- A node word other than the debug-list head is no debug-list word. -/
theorem notDbgW_node {s : S} {c o : U64} (hT : TcbPlaced T) (hN : ∀ c ∈ Cs, NodePlaced st T s c) (hc : c ∈ Cs)
    (ho : o.val < 4288) (h88 : o.val ≠ 88) : ¬ DbgW st T Cs s (L.nodeAt s c o) := by
  have d88 := debug_val
  rintro (⟨y, hy, e | e⟩ | ⟨c', hc', e⟩)
  · exact node_ne_field (K := 3576#u64) (hN c hc) ho hy (hT y hy) (by simp) e
  · exact node_ne_field (K := 3584#u64) (hN c hc) ho hy (hT y hy) (by simp) e
  · exact node_ne_node (hN c hc) (hN c' hc') ho (by omega) (fun _ => by omega) (congrArg UScalar.val e)

/-- The action word is no debug-list word, so a debug-list footprint keeps it. -/
theorem WritesIn.dbg_act {s s' : S} (hT : TcbPlaced T) (hN : ∀ c ∈ Cs, NodePlaced st T s c) (hc : L.cpu s ∈ Cs)
    (hw : WritesIn st s s' (DbgW st T Cs s)) : L.actionW s' = L.actionW s := by
  unfold LawfulStore.actionW
  rw [hw.2.1, nodeAt_of_ksb hw.1]
  exact hw.mem_eq (nodeAt_aligned (hN _ hc) (by rw [act_val]; omega) (by rw [act_val]))
    (notDbgW_node hT hN hc (by rw [act_val]; omega) (by rw [act_val]; omega))

/-- The idle-thread word is no debug-list word, so a debug-list footprint keeps it. -/
theorem WritesIn.dbg_idle {s s' : S} (hT : TcbPlaced T) (hN : ∀ c ∈ Cs, NodePlaced st T s c) (hc : L.cpu s ∈ Cs)
    (hw : WritesIn st s s' (DbgW st T Cs s)) : L.idleW s' = L.idleW s := by
  unfold LawfulStore.idleW
  rw [hw.2.1, nodeAt_of_ksb hw.1]
  exact hw.mem_eq (nodeAt_aligned (hN _ hc) (by rw [idle8]; omega) (by rw [idle8]))
    (notDbgW_node hT hN hc (by rw [idle8]; omega) (by rw [idle8]; omega))

theorem obj.Tcb.debug_next.val (s : S) (t : obj.Tcb) : obj.Tcb.debug_next st t s ⦃ v => v = L.mem s (dnA t) ⦄ := by
  unfold obj.Tcb.debug_next; step*; simp_all [dnA]
theorem obj.Tcb.debug_prev.val (s : S) (t : obj.Tcb) : obj.Tcb.debug_prev st t s ⦃ v => v = L.mem s (dpA t) ⦄ := by
  unfold obj.Tcb.debug_prev; step*; simp_all [dpA]
theorem obj.Tcb.set_debug_next.wr (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_debug_next st t s v ⦃ s' => s' = L.wr s (dnA t) v ⦄ := by
  unfold obj.Tcb.set_debug_next; step*; simp_all [dnA]
theorem obj.Tcb.set_debug_prev.wr (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_debug_prev st t s v ⦃ s' => s' = L.wr s (dpA t) v ⦄ := by
  unfold obj.Tcb.set_debug_prev; step*; simp_all [dpA]

/-- A write of a debug link of a TCB (a null or a TCB). -/
theorem dbgF_x {X : Set U64} {s : S} {y K v : U64} (h : BlkOKX st T Cs Ω H Sg Rp Scs Nt Z Ac X s) (hy : y ∈ T)
    (hK : K.val = 3576 ∨ K.val = 3584) (hv : Tz T v) :
    BlkOKX st T Cs Ω H Sg Rp Scs Nt Z Ac X (L.wr s (core.num.U64.wrapping_add y K) v) ∧
      TmFr st T Cs Nt s (L.wr s (core.num.U64.wrapping_add y K) v) ∧
      WritesIn st s (L.wr s (core.num.U64.wrapping_add y K) v) (DbgW st T Cs s) := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hT := h0.tcbs
  have hya := hT y hy
  have ha := field_aligned hya (K := K) (by omega) (by omega)
  have hΩ : ∀ n ∈ Nt, OutsideObjs st T Cs s (ntfnBtA n) := fun n hn => h0.omega _ (hSg.sub _ (hX.1.ntB n hn).2)
  obtain ⟨b1, b2⟩ := bx_field' (K := K) (v := v) h0 hB hX hSg.sub hy (by omega) (by omega) (by omega)
    ⟨hX.2.2.tm.wr_ptr hT h0.nodes hy (by omega) hv,
     hX.2.2.ntb.wr hX.1 ha (fun n hn => out_ne_field (hΩ n hn) hy hya (by omega)),
     hX.2.2.rb.tmfr (TmFr.dbgF hT h0.nodes hΩ hy hK hv), (TmFr.dbgF hT h0.nodes hΩ hy hK hv).2.2.2.1⟩
  refine ⟨⟨⟨Q, R, inv_wr_field h0 hy (by omega) (by omega) (by omega)⟩, b1, b2,
    SCsOK.field h0 hS hX hy (by omega) (by omega) (by omega),
    ⟨hSg.sub, fun b hb => by rw [L.ksb_wr]; exact hSg.ks b hb, fun o h1 h2 => by rw [L.ksb_wr]; exact hSg.ksΩ o h1 h2⟩⟩,
    TmFr.dbgF hT h0.nodes hΩ hy hK hv,
    (writesIn_wr ha).mono fun b hb => Or.inl ⟨y, hy, ?_⟩⟩
  subst hb
  rcases hK with e | e
  · left; unfold dnA; congr; exact UScalar.eq_of_val_eq (by rw [e]; rfl)
  · right; unfold dpA; congr; exact UScalar.eq_of_val_eq (by rw [e]; rfl)

/-- A write of a core's debug-list head (a null or a TCB). -/
theorem dbgN_x {X : Set U64} {s : S} {c v : U64} (h : BlkOKX st T Cs Ω H Sg Rp Scs Nt Z Ac X s) (hc : c ∈ Cs)
    (hv : Tz T v) :
    BlkOKX st T Cs Ω H Sg Rp Scs Nt Z Ac X (L.wr s (L.nodeAt s c layout.node.DEBUG_TCBS) v) ∧
      TmFr st T Cs Nt s (L.wr s (L.nodeAt s c layout.node.DEBUG_TCBS) v) ∧
      WritesIn st s (L.wr s (L.nodeAt s c layout.node.DEBUG_TCBS) v) (DbgW st T Cs s) := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hT := h0.tcbs
  have hN := h0.nodes c hc
  have hN' := h0.nodes _ h0.cur
  have d88 := debug_val
  have ha : Aligned (L.nodeAt s c layout.node.DEBUG_TCBS) := nodeAt_aligned hN (by omega) (by omega)
  have hΩ : ∀ n ∈ Nt, OutsideObjs st T Cs s (ntfnBtA n) := fun n hn => h0.omega _ (hSg.sub _ (hX.1.ntB n hn).2)
  have hw : WritesIn st s (L.wr s (L.nodeAt s c layout.node.DEBUG_TCBS) v) (L.Free s Ω Cs) :=
    free_node_write rfl hc hN (by simp only [LowFree]; omega)
  have hcs : (L.nodeAt s c layout.node.DEBUG_TCBS).val ≠ (L.nodeA s layout.node.CUR_SC).val :=
    node_ne_node hN hN' (by omega) (by simp [layout.node.CUR_SC]) (fun _ => by rw [d88]; simp [layout.node.CUR_SC])
  have ecs : L.cscW (L.wr s (L.nodeAt s c layout.node.DEBUG_TCBS) v) = L.cscW s := by
    unfold LawfulStore.cscW; rw [nodeA_wr]
    exact L.mem_wr_ne ha (nodeAt_aligned hN' (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])) hcs
  obtain ⟨-, hcΩ⟩ := objs_omega hX.1 hSg.sub
  refine ⟨⟨⟨Q, R, inv_of_free h0 hw⟩, hB.free h0 hw,
    hX.writes h0.tcbs (writesIn_wr (v := v) ha) (fun b hb => hb ▸ not_prot_node h0 hX.1 hSg.sub hc (by omega))
      (by rw [ecs]; exact hX.2.2.cur)
      ⟨hX.2.2.tm.wr_node hT h0.nodes hc (by omega) hv,
       hX.2.2.ntb.wr hX.1 ha (fun n hn => out_ne_node (hΩ n hn) hc hN (by omega)),
       hX.2.2.rb.tmfr (TmFr.dbgN hT h0.nodes hΩ hc hv), (TmFr.dbgN hT h0.nodes hΩ hc hv).2.2.2.1⟩
      (by
        unfold LawfulStore.idleW; rw [LawfulStore.cpu_wr, nodeAt_wr]
        exact L.mem_wr_ne ha (nodeAt_aligned hN' (by rw [idle8]; omega) (by rw [idle8]))
          (node_ne_node hN hN' (by omega) (by rw [idle8]; omega) (fun _ => by rw [d88, idle8]; simp))),
    SCsOK.wr h0 hS hX ha (fun y hy e => node_ne_field (o := layout.node.DEBUG_TCBS) hN (by omega) hy (hT y hy)
        (K := 3464#u64)
        (by simp) (UScalar.eq_of_val_eq (by rw [← scA_eq]; exact e))) hcs
      (fun c' hc' => ⟨fun e => out_ne_node (h0.omega _ (hcΩ c' hc').2.2.1) hc hN (by omega) e,
        fun e => out_ne_node (h0.omega _ (hcΩ c' hc').2.2.2.1) hc hN (by omega) e,
        fun e => out_ne_node (h0.omega _ (hcΩ c' hc').2.2.2.2) hc hN (by omega) e⟩)
      (fun c' hc' e => out_ne_node (h0.omega _ (spor_omega hX.1 hc')) hc hN (by omega) e)
      (fun c' hc' e => absurd e (out_ne_node (h0.omega _ (hSg.sub _ (hX.1.repW c' hc'))) hc hN (by omega))),
    ⟨hSg.sub, fun b hb => by rw [L.ksb_wr]; exact hSg.ks b hb, fun o h1 h2 => by rw [L.ksb_wr]; exact hSg.ksΩ o h1 h2⟩⟩,
    TmFr.dbgN hT h0.nodes hΩ hc hv,
    (writesIn_wr ha).mono fun b hb => Or.inr ⟨c, hc, hb⟩⟩

theorem dbg_next_x {X : Set U64} {s : S} {y v : U64} (h : BlkOKX st T Cs Ω H Sg Rp Scs Nt Z Ac X s) (hy : y ∈ T)
    (hv : Tz T v) :
    BlkOKX st T Cs Ω H Sg Rp Scs Nt Z Ac X (L.wr s (dnA y) v) ∧ TmFr st T Cs Nt s (L.wr s (dnA y) v) ∧
      WritesIn st s (L.wr s (dnA y) v) (DbgW st T Cs s) :=
  dbgF_x (K := 3576#u64) h hy (Or.inl rfl) hv
theorem dbg_prev_x {X : Set U64} {s : S} {y v : U64} (h : BlkOKX st T Cs Ω H Sg Rp Scs Nt Z Ac X s) (hy : y ∈ T)
    (hv : Tz T v) :
    BlkOKX st T Cs Ω H Sg Rp Scs Nt Z Ac X (L.wr s (dpA y) v) ∧ TmFr st T Cs Nt s (L.wr s (dpA y) v) ∧
      WritesIn st s (L.wr s (dpA y) v) (DbgW st T Cs s) :=
  dbgF_x (K := 3584#u64) h hy (Or.inr rfl) hv

/-- `debug_remove`: the thread leaves its core's debug list. -/
theorem objects.debug_remove.x {X : Set U64} (s : S) (t : U64) (h : BlkOKX st T Cs Ω H Sg Rp Scs Nt Z Ac X s)
    (ht : t ∈ T) :
    objects.debug_remove st s t ⦃ s' => BlkOKX st T Cs Ω H Sg Rp Scs Nt Z Ac X s' ∧ TmFr st T Cs Nt s s' ∧
      WritesIn st s s' (DbgW st T Cs s) ⦄ := by
  have hc : L.mem s (affA t) ∈ Cs := h.1.choose_spec.choose_spec.aff t ht
  have hTm := h.2.2.1.2.2.tm
  unfold objects.debug_remove
  step with obj.Tcb.affinity.spec as ⟨cpu, ecpu⟩
  step with obj.node_get.spec as ⟨hd, ehd⟩
  step with obj.Tcb.debug_next.val as ⟨nx, enx⟩
  step with obj.Tcb.debug_prev.val as ⟨pv, epv⟩
  have hcpu : cpu ∈ Cs := by rw [ecpu]; exact hc
  have tnx : Tz T nx := by rw [enx]; exact hTm.dn t ht
  have tpv : Tz T pv := by rw [epv]; exact hTm.dp t ht
  refine WP.spec_bind (Pₘ := fun s1 => BlkOKX st T Cs Ω H Sg Rp Scs Nt Z Ac X s1 ∧ TmFr st T Cs Nt s s1 ∧
    WritesIn st s s1 (DbgW st T Cs s)) ?_ ?_
  · split
    · exact WP.spec_mono (obj.node_set.spec s cpu _ nx) fun s1 e => by subst e; exact dbgN_x h hcpu tnx
    · split
      · rename_i _ hp
        have hpT : pv ∈ T := tpv.ne0 (by simpa using hp)
        exact WP.spec_mono (obj.Tcb.set_debug_next.wr s pv nx) fun s1 e => by subst e; exact dbg_next_x h hpT tnx
      · exact (WP.spec_ok _).2 ⟨h, TmFr.refl (L := L) _, WritesIn.refl _ _⟩
  intro s1 ⟨h1, m1, f1⟩
  refine WP.spec_bind (Pₘ := fun s2 => BlkOKX st T Cs Ω H Sg Rp Scs Nt Z Ac X s2 ∧ TmFr st T Cs Nt s s2 ∧
    WritesIn st s s2 (DbgW st T Cs s)) ?_ ?_
  · split
    · rename_i hn
      have hnT : nx ∈ T := tnx.ne0 (by simpa using hn)
      exact WP.spec_mono (obj.Tcb.set_debug_prev.wr s1 nx pv) fun s2 e => by
        subst e; obtain ⟨b, m, f⟩ := dbg_prev_x h1 hnT tpv; exact ⟨b, m1.trans m, DbgW.trans f1 f⟩
    · exact (WP.spec_ok _).2 ⟨h1, m1, f1⟩
  intro s2 ⟨h2, m2, f2⟩
  refine WP.spec_bind (obj.Tcb.set_debug_prev.wr s2 t 0#u64) fun s3 e3 => ?_
  subst e3
  obtain ⟨h3, m3, f3⟩ := dbg_prev_x h2 ht Tz.zero
  refine WP.spec_mono (obj.Tcb.set_debug_next.wr _ t 0#u64) fun s4 e4 => ?_
  subst e4
  obtain ⟨h4, m4, f4⟩ := dbg_next_x h3 ht Tz.zero
  exact ⟨h4, m2.trans (m3.trans m4), DbgW.trans f2 (DbgW.trans f3 f4)⟩

/-- `dbgF_x` for `BlkOKW`. -/
theorem dbgF_w {X : Set U64} {s : S} {y K v d : U64} (h : BlkOKW st T Cs Ω H Sg Rp Scs Nt Z Ac X d s) (hy : y ∈ T)
    (hK : K.val = 3576 ∨ K.val = 3584) (hv : Tz T v) :
    BlkOKW st T Cs Ω H Sg Rp Scs Nt Z Ac X d (L.wr s (core.num.U64.wrapping_add y K) v) ∧
      TmFr st T Cs Nt s (L.wr s (core.num.U64.wrapping_add y K) v) ∧
      WritesIn st s (L.wr s (core.num.U64.wrapping_add y K) v) (DbgW st T Cs s) := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hT := h0.tcbs
  have hya := hT y hy
  have ha := field_aligned hya (K := K) (by omega) (by omega)
  have hΩ : ∀ n ∈ Nt, OutsideObjs st T Cs s (ntfnBtA n) := fun n hn => h0.omega _ (hSg.sub _ (hX.1.1.ntB n hn).2)
  obtain ⟨b1, b2⟩ := bx_fieldW' (K := K) (v := v) h0 hB hX hSg.sub hy (by omega) (by omega) (by omega)
    ⟨hX.1.2.2.tm.wr_ptr hT h0.nodes hy (by omega) hv,
     hX.1.2.2.ntb.wr hX.1.1 ha (fun n hn => out_ne_field (hΩ n hn) hy hya (by omega)),
     hX.1.2.2.rb.tmfr (TmFr.dbgF hT h0.nodes hΩ hy hK hv), (TmFr.dbgF hT h0.nodes hΩ hy hK hv).2.2.2.1⟩
  refine ⟨⟨⟨Q, R, inv_wr_field h0 hy (by omega) (by omega) (by omega)⟩, b1, b2,
    SCsOK.fieldO h0 hS hX.1.1 hy (by omega) (by omega) (by omega),
    ⟨hSg.sub, fun b hb => by rw [L.ksb_wr]; exact hSg.ks b hb, fun o h1 h2 => by rw [L.ksb_wr]; exact hSg.ksΩ o h1 h2⟩⟩,
    TmFr.dbgF hT h0.nodes hΩ hy hK hv,
    (writesIn_wr ha).mono fun b hb => Or.inl ⟨y, hy, ?_⟩⟩
  subst hb
  rcases hK with e | e
  · left; unfold dnA; congr; exact UScalar.eq_of_val_eq (by rw [e]; rfl)
  · right; unfold dpA; congr; exact UScalar.eq_of_val_eq (by rw [e]; rfl)

/-- `dbgN_x` for `BlkOKW`. -/
theorem dbgN_w {X : Set U64} {s : S} {c v d : U64} (h : BlkOKW st T Cs Ω H Sg Rp Scs Nt Z Ac X d s) (hc : c ∈ Cs)
    (hv : Tz T v) :
    BlkOKW st T Cs Ω H Sg Rp Scs Nt Z Ac X d (L.wr s (L.nodeAt s c layout.node.DEBUG_TCBS) v) ∧
      TmFr st T Cs Nt s (L.wr s (L.nodeAt s c layout.node.DEBUG_TCBS) v) ∧
      WritesIn st s (L.wr s (L.nodeAt s c layout.node.DEBUG_TCBS) v) (DbgW st T Cs s) := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hT := h0.tcbs
  have hN := h0.nodes c hc
  have hN' := h0.nodes _ h0.cur
  have d88 := debug_val
  have ha : Aligned (L.nodeAt s c layout.node.DEBUG_TCBS) := nodeAt_aligned hN (by omega) (by omega)
  have hΩ : ∀ n ∈ Nt, OutsideObjs st T Cs s (ntfnBtA n) := fun n hn => h0.omega _ (hSg.sub _ (hX.1.1.ntB n hn).2)
  have hw : WritesIn st s (L.wr s (L.nodeAt s c layout.node.DEBUG_TCBS) v) (L.Free s Ω Cs) :=
    free_node_write rfl hc hN (by simp only [LowFree]; omega)
  have hcs : (L.nodeAt s c layout.node.DEBUG_TCBS).val ≠ (L.nodeA s layout.node.CUR_SC).val :=
    node_ne_node hN hN' (by omega) (by simp [layout.node.CUR_SC]) (fun _ => by rw [d88]; simp [layout.node.CUR_SC])
  have ecs : L.cscW (L.wr s (L.nodeAt s c layout.node.DEBUG_TCBS) v) = L.cscW s := by
    unfold LawfulStore.cscW; rw [nodeA_wr]
    exact L.mem_wr_ne ha (nodeAt_aligned hN' (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])) hcs
  obtain ⟨-, hcΩ⟩ := objs_omega hX.1.1 hSg.sub
  refine ⟨⟨⟨Q, R, inv_of_free h0 hw⟩, hB.free h0 hw,
    hX.writes h0.tcbs (writesIn_wr (v := v) ha) (fun b hb => hb ▸ not_prot_node h0 hX.1.1 hSg.sub hc (by omega))
      (by rw [ecs]; exact hX.1.2.2.cur)
      ⟨hX.1.2.2.tm.wr_node hT h0.nodes hc (by omega) hv,
       hX.1.2.2.ntb.wr hX.1.1 ha (fun n hn => out_ne_node (hΩ n hn) hc hN (by omega)),
       hX.1.2.2.rb.tmfr (TmFr.dbgN hT h0.nodes hΩ hc hv), (TmFr.dbgN hT h0.nodes hΩ hc hv).2.2.2.1⟩
      (by
        unfold LawfulStore.idleW; rw [LawfulStore.cpu_wr, nodeAt_wr]
        exact L.mem_wr_ne ha (nodeAt_aligned hN' (by rw [idle8]; omega) (by rw [idle8]))
          (node_ne_node hN hN' (by omega) (by rw [idle8]; omega) (fun _ => by rw [d88, idle8]; simp))),
    SCsOK.wr' h0 hS hX.1.1 ha (fun y hy e => node_ne_field (o := layout.node.DEBUG_TCBS) hN (by omega) hy (hT y hy)
        (K := 3464#u64)
        (by simp) (UScalar.eq_of_val_eq (by rw [← scA_eq]; exact e))) hcs
      (fun c' hc' => ⟨fun e => out_ne_node (h0.omega _ (hcΩ c' hc').2.2.1) hc hN (by omega) e,
        fun e => out_ne_node (h0.omega _ (hcΩ c' hc').2.2.2.1) hc hN (by omega) e,
        fun e => out_ne_node (h0.omega _ (hcΩ c' hc').2.2.2.2) hc hN (by omega) e⟩)
      (fun c' hc' e => out_ne_node (h0.omega _ (spor_omega hX.1.1 hc')) hc hN (by omega) e)
      (fun c' hc' e => absurd e (out_ne_node (h0.omega _ (hSg.sub _ (hX.1.1.repW c' hc'))) hc hN (by omega))),
    ⟨hSg.sub, fun b hb => by rw [L.ksb_wr]; exact hSg.ks b hb, fun o h1 h2 => by rw [L.ksb_wr]; exact hSg.ksΩ o h1 h2⟩⟩,
    TmFr.dbgN hT h0.nodes hΩ hc hv,
    (writesIn_wr ha).mono fun b hb => Or.inr ⟨c, hc, hb⟩⟩

theorem dbg_next_w {X : Set U64} {s : S} {y v d : U64} (h : BlkOKW st T Cs Ω H Sg Rp Scs Nt Z Ac X d s) (hy : y ∈ T)
    (hv : Tz T v) :
    BlkOKW st T Cs Ω H Sg Rp Scs Nt Z Ac X d (L.wr s (dnA y) v) ∧ TmFr st T Cs Nt s (L.wr s (dnA y) v) ∧
      WritesIn st s (L.wr s (dnA y) v) (DbgW st T Cs s) :=
  dbgF_w (K := 3576#u64) h hy (Or.inl rfl) hv
theorem dbg_prev_w {X : Set U64} {s : S} {y v d : U64} (h : BlkOKW st T Cs Ω H Sg Rp Scs Nt Z Ac X d s) (hy : y ∈ T)
    (hv : Tz T v) :
    BlkOKW st T Cs Ω H Sg Rp Scs Nt Z Ac X d (L.wr s (dpA y) v) ∧ TmFr st T Cs Nt s (L.wr s (dpA y) v) ∧
      WritesIn st s (L.wr s (dpA y) v) (DbgW st T Cs s) :=
  dbgF_w (K := 3584#u64) h hy (Or.inr rfl) hv

/-- `debug_remove` from a `BlkOKW` state (`migrate_tcb` of a thread whose
SC's core differs from its affinity). -/
theorem objects.debug_remove.w {X : Set U64} {d : U64} (s : S) (t : U64) (h : BlkOKW st T Cs Ω H Sg Rp Scs Nt Z Ac X d s)
    (ht : t ∈ T) :
    objects.debug_remove st s t ⦃ s' => BlkOKW st T Cs Ω H Sg Rp Scs Nt Z Ac X d s' ∧ TmFr st T Cs Nt s s' ∧
      WritesIn st s s' (DbgW st T Cs s) ⦄ := by
  have hc : L.mem s (affA t) ∈ Cs := h.1.choose_spec.choose_spec.aff t ht
  have hTm := h.2.2.1.1.2.2.tm
  unfold objects.debug_remove
  step with obj.Tcb.affinity.spec as ⟨cpu, ecpu⟩
  step with obj.node_get.spec as ⟨hd, ehd⟩
  step with obj.Tcb.debug_next.val as ⟨nx, enx⟩
  step with obj.Tcb.debug_prev.val as ⟨pv, epv⟩
  have hcpu : cpu ∈ Cs := by rw [ecpu]; exact hc
  have tnx : Tz T nx := by rw [enx]; exact hTm.dn t ht
  have tpv : Tz T pv := by rw [epv]; exact hTm.dp t ht
  refine WP.spec_bind (Pₘ := fun s1 => BlkOKW st T Cs Ω H Sg Rp Scs Nt Z Ac X d s1 ∧ TmFr st T Cs Nt s s1 ∧
    WritesIn st s s1 (DbgW st T Cs s)) ?_ ?_
  · split
    · exact WP.spec_mono (obj.node_set.spec s cpu _ nx) fun s1 e => by subst e; exact dbgN_w h hcpu tnx
    · split
      · rename_i _ hp
        have hpT : pv ∈ T := tpv.ne0 (by simpa using hp)
        exact WP.spec_mono (obj.Tcb.set_debug_next.wr s pv nx) fun s1 e => by subst e; exact dbg_next_w h hpT tnx
      · exact (WP.spec_ok _).2 ⟨h, TmFr.refl (L := L) _, WritesIn.refl _ _⟩
  intro s1 ⟨h1, m1, f1⟩
  refine WP.spec_bind (Pₘ := fun s2 => BlkOKW st T Cs Ω H Sg Rp Scs Nt Z Ac X d s2 ∧ TmFr st T Cs Nt s s2 ∧
    WritesIn st s s2 (DbgW st T Cs s)) ?_ ?_
  · split
    · rename_i hn
      have hnT : nx ∈ T := tnx.ne0 (by simpa using hn)
      exact WP.spec_mono (obj.Tcb.set_debug_prev.wr s1 nx pv) fun s2 e => by
        subst e; obtain ⟨b, m, f⟩ := dbg_prev_w h1 hnT tpv; exact ⟨b, m1.trans m, DbgW.trans f1 f⟩
    · exact (WP.spec_ok _).2 ⟨h1, m1, f1⟩
  intro s2 ⟨h2, m2, f2⟩
  refine WP.spec_bind (obj.Tcb.set_debug_prev.wr s2 t 0#u64) fun s3 e3 => ?_
  subst e3
  obtain ⟨h3, m3, f3⟩ := dbg_prev_w h2 ht Tz.zero
  refine WP.spec_mono (obj.Tcb.set_debug_next.wr _ t 0#u64) fun s4 e4 => ?_
  subst e4
  obtain ⟨h4, m4, f4⟩ := dbg_next_w h3 ht Tz.zero
  exact ⟨h4, m2.trans (m3.trans m4), DbgW.trans f2 (DbgW.trans f3 f4)⟩

/-- `debug_append`: the thread goes to the head of its core's debug list. -/
theorem objects.debug_append.x {X : Set U64} (s : S) (t : U64) (h : BlkOKX st T Cs Ω H Sg Rp Scs Nt Z Ac X s)
    (ht : t ∈ T) :
    objects.debug_append st s t ⦃ s' => BlkOKX st T Cs Ω H Sg Rp Scs Nt Z Ac X s' ∧ TmFr st T Cs Nt s s' ∧
      WritesIn st s s' (DbgW st T Cs s) ⦄ := by
  have hc : L.mem s (affA t) ∈ Cs := h.1.choose_spec.choose_spec.aff t ht
  have hTm := h.2.2.1.2.2.tm
  unfold objects.debug_append
  step with obj.Tcb.affinity.spec as ⟨cpu, ecpu⟩
  step with obj.node_get.spec as ⟨hd, ehd⟩
  have hcpu : cpu ∈ Cs := by rw [ecpu]; exact hc
  have thd : Tz T hd := by rw [ehd]; exact hTm.dh cpu hcpu
  refine WP.spec_bind (obj.Tcb.set_debug_prev.wr s t 0#u64) fun s1 e1 => ?_
  subst e1
  obtain ⟨h1, m1, f1⟩ := dbg_prev_x h ht Tz.zero
  refine WP.spec_bind (obj.Tcb.set_debug_next.wr _ t hd) fun s2 e2 => ?_
  subst e2
  obtain ⟨h2, m2, f2⟩ := dbg_next_x h1 ht thd
  have f12 := DbgW.trans f1 f2
  refine WP.spec_bind (Pₘ := fun r : S × U64 => r.2 = t ∧ BlkOKX st T Cs Ω H Sg Rp Scs Nt Z Ac X r.1 ∧
    TmFr st T Cs Nt s r.1 ∧ WritesIn st s r.1 (DbgW st T Cs s)) ?_ ?_
  · split
    · rename_i hn
      have hdT : hd ∈ T := thd.ne0 (by simpa using hn)
      refine WP.spec_bind (obj.Tcb.set_debug_prev.wr _ hd t) fun s3 e3 => ?_
      subst e3
      obtain ⟨h3, m3, f3⟩ := dbg_prev_x h2 hdT (Tz.of_mem ht)
      exact (WP.spec_ok _).2 ⟨rfl, h3, m1.trans (m2.trans m3), DbgW.trans f12 f3⟩
    · exact (WP.spec_ok _).2 ⟨rfl, h2, m1.trans m2, f12⟩
  rintro ⟨s3, t1⟩ hr
  simp only at hr
  obtain ⟨e, h3, m3, f3⟩ := hr
  subst e
  try simp only [WP.uncurry'_pair]
  refine WP.spec_mono (obj.node_set.spec s3 cpu _ _) fun s4 e4 => ?_
  subst e4
  obtain ⟨h4, m4, f4⟩ := dbgN_x h3 hcpu (Tz.of_mem ht)
  exact ⟨h4, m3.trans m4, DbgW.trans f3 f4⟩

/-! ### The debug-list steps as frames (from the debug lists typed alone) -/

/-- A write of a debug link of a TCB of `T` (a null or a TCB), after a
debug-list footprint: still a debug-list footprint, the lists still typed. -/
theorem dbgF_frame {s s1 : S} {y K v : U64} (hT : TcbPlaced T) (hN : ∀ c ∈ Cs, NodePlaced st T s c)
    (w : WritesIn st s s1 (DbgW st T Cs s)) (D : DbgTz st T Cs s1) (hy : y ∈ T) (hK : K.val = 3576 ∨ K.val = 3584)
    (hv : Tz T v) :
    WritesIn st s (L.wr s1 (core.num.U64.wrapping_add y K) v) (DbgW st T Cs s) ∧
      DbgTz st T Cs (L.wr s1 (core.num.U64.wrapping_add y K) v) := by
  have ha := field_aligned (hT y hy) (K := K) (by omega) (by omega)
  refine ⟨WritesIn.mono (WritesIn.trans w (writesIn_wr ha)) fun b hb => ?_,
    DbgTz.wr hT (fun c hc => (hN c hc).ksb w.1) ha hv D⟩
  rcases hb with hb | e
  · exact hb
  · subst e
    refine Or.inl ⟨y, hy, ?_⟩
    rcases hK with e | e
    · left; unfold dnA; congr; exact UScalar.eq_of_val_eq (by rw [e]; rfl)
    · right; unfold dpA; congr; exact UScalar.eq_of_val_eq (by rw [e]; rfl)

/-- A write of a core's debug-list head (a null or a TCB), after a
debug-list footprint. -/
theorem dbgN_frame {s s1 : S} {c v : U64} (hT : TcbPlaced T) (hN : ∀ c ∈ Cs, NodePlaced st T s c)
    (w : WritesIn st s s1 (DbgW st T Cs s)) (D : DbgTz st T Cs s1) (hc : c ∈ Cs) (hv : Tz T v) :
    WritesIn st s (L.wr s1 (L.nodeAt s1 c layout.node.DEBUG_TCBS) v) (DbgW st T Cs s) ∧
      DbgTz st T Cs (L.wr s1 (L.nodeAt s1 c layout.node.DEBUG_TCBS) v) := by
  have hN1 : ∀ c ∈ Cs, NodePlaced st T s1 c := fun c hc => (hN c hc).ksb w.1
  have ha : Aligned (L.nodeAt s1 c layout.node.DEBUG_TCBS) :=
    nodeAt_aligned (hN1 c hc) (by simp [debug_val]) (by simp [debug_val])
  refine ⟨WritesIn.mono (WritesIn.trans w (writesIn_wr ha)) fun b hb => ?_, DbgTz.wr hT hN1 ha hv D⟩
  rcases hb with hb | e
  · exact hb
  · exact Or.inr ⟨c, hc, by rw [e, nodeAt_of_ksb w.1]⟩

/-- `debug_remove` writes only debug-list words and keeps the lists typed. -/
theorem objects.debug_remove.frame (s : S) (t : U64) (hT : TcbPlaced T) (hN : ∀ c ∈ Cs, NodePlaced st T s c)
    (hD : DbgTz st T Cs s) (hc : L.mem s (affA t) ∈ Cs) (ht : t ∈ T) :
    objects.debug_remove st s t ⦃ s' => WritesIn st s s' (DbgW st T Cs s) ∧ DbgTz st T Cs s' ⦄ := by
  unfold objects.debug_remove
  step with obj.Tcb.affinity.spec as ⟨cpu, ecpu⟩
  step with obj.node_get.spec as ⟨hd, ehd⟩
  step with obj.Tcb.debug_next.val as ⟨nx, enx⟩
  step with obj.Tcb.debug_prev.val as ⟨pv, epv⟩
  have hcpu : cpu ∈ Cs := by rw [ecpu]; exact hc
  have tnx : Tz T nx := by rw [enx]; exact hD.dn t ht
  have tpv : Tz T pv := by rw [epv]; exact hD.dp t ht
  have w0 : WritesIn st s s (DbgW st T Cs s) := WritesIn.refl _ _
  refine WP.spec_bind (Pₘ := fun s1 => WritesIn st s s1 (DbgW st T Cs s) ∧ DbgTz st T Cs s1) ?_ ?_
  · split
    · exact WP.spec_mono (obj.node_set.spec s cpu _ nx) fun s1 e => by
        subst e; exact dbgN_frame hT hN w0 hD hcpu tnx
    · split
      · rename_i _ hp
        have hpT : pv ∈ T := tpv.ne0 (by simpa using hp)
        exact WP.spec_mono (obj.Tcb.set_debug_next.wr s pv nx) fun s1 e => by
          subst e; exact dbgF_frame (K := 3576#u64) hT hN w0 hD hpT (Or.inl rfl) tnx
      · exact (WP.spec_ok _).2 ⟨w0, hD⟩
  intro s1 ⟨w1, D1⟩
  refine WP.spec_bind (Pₘ := fun s2 => WritesIn st s s2 (DbgW st T Cs s) ∧ DbgTz st T Cs s2) ?_ ?_
  · split
    · rename_i hn
      have hnT : nx ∈ T := tnx.ne0 (by simpa using hn)
      exact WP.spec_mono (obj.Tcb.set_debug_prev.wr s1 nx pv) fun s2 e => by
        subst e; exact dbgF_frame (K := 3584#u64) hT hN w1 D1 hnT (Or.inr rfl) tpv
    · exact (WP.spec_ok _).2 ⟨w1, D1⟩
  intro s2 ⟨w2, D2⟩
  refine WP.spec_bind (obj.Tcb.set_debug_prev.wr s2 t 0#u64) fun s3 e3 => ?_
  subst e3
  obtain ⟨w3, D3⟩ := dbgF_frame (K := 3584#u64) hT hN w2 D2 ht (Or.inr rfl) Tz.zero
  refine WP.spec_mono (obj.Tcb.set_debug_next.wr _ t 0#u64) fun s4 e4 => ?_
  subst e4
  exact dbgF_frame (K := 3576#u64) hT hN w3 D3 ht (Or.inl rfl) Tz.zero

/-- `debug_append` writes only debug-list words and keeps the lists typed. -/
theorem objects.debug_append.frame (s : S) (t : U64) (hT : TcbPlaced T) (hN : ∀ c ∈ Cs, NodePlaced st T s c)
    (hD : DbgTz st T Cs s) (hc : L.mem s (affA t) ∈ Cs) (ht : t ∈ T) :
    objects.debug_append st s t ⦃ s' => WritesIn st s s' (DbgW st T Cs s) ∧ DbgTz st T Cs s' ⦄ := by
  unfold objects.debug_append
  step with obj.Tcb.affinity.spec as ⟨cpu, ecpu⟩
  step with obj.node_get.spec as ⟨hd, ehd⟩
  have hcpu : cpu ∈ Cs := by rw [ecpu]; exact hc
  have thd : Tz T hd := by rw [ehd]; exact hD.dh cpu hcpu
  refine WP.spec_bind (obj.Tcb.set_debug_prev.wr s t 0#u64) fun s1 e1 => ?_
  subst e1
  obtain ⟨w1, D1⟩ := dbgF_frame (K := 3584#u64) hT hN (WritesIn.refl _ _) hD ht (Or.inr rfl) Tz.zero
  refine WP.spec_bind (obj.Tcb.set_debug_next.wr _ t hd) fun s2 e2 => ?_
  subst e2
  obtain ⟨w2, D2⟩ := dbgF_frame (K := 3576#u64) hT hN w1 D1 ht (Or.inl rfl) thd
  refine WP.spec_bind (Pₘ := fun r : S × U64 => r.2 = t ∧ WritesIn st s r.1 (DbgW st T Cs s) ∧
    DbgTz st T Cs r.1) ?_ ?_
  · split
    · rename_i hn
      have hdT : hd ∈ T := thd.ne0 (by simpa using hn)
      refine WP.spec_bind (obj.Tcb.set_debug_prev.wr _ hd t) fun s3 e3 => ?_
      subst e3
      obtain ⟨w3, D3⟩ := dbgF_frame (K := 3584#u64) hT hN w2 D2 hdT (Or.inr rfl) (Tz.of_mem ht)
      exact (WP.spec_ok _).2 ⟨rfl, w3, D3⟩
    · exact (WP.spec_ok _).2 ⟨rfl, w2, D2⟩
  rintro ⟨s3, t1⟩ hr
  simp only at hr
  obtain ⟨e, w3, D3⟩ := hr
  subst e
  try simp only [WP.uncurry'_pair]
  refine WP.spec_mono (obj.node_set.spec s3 cpu _ _) fun s4 e4 => ?_
  subst e4
  exact dbgN_frame hT hN w3 D3 hcpu (Tz.of_mem ht)

/-- a64: AArch64 `migrate_tcb`'s VCPU steps, for a thread with no `ARMVCPURun` in flight (`RUN_VCPU` 0): the
bound VCPU's flush is an Arch call, and the `RUN_VCPU` branch (flushes and the VCPU's `OWNER_CPU` write) is
skipped, so the store stays `s1`. -/
theorem migrate_vcpu_idle {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s1 : S) (a2 : A)
    (t cpu : U64) (hrv : L.mem s1 (runVcpuA t) = 0#u64) (f : S × A → Result (S × A)) {P : S × A → Prop}
    (hf : ∀ a3, f (s1, a3) ⦃ P ⦄) :
    (do
      let v ← vcpu.bound st s1 t
      let a3 ← if v != 0#u64 then ar.vcpu_flush a2 v else ok a2
      let i1 ← layout.tcb.RUN_VCPU
      let i2 ← lift (core.num.U64.wrapping_add t i1)
      let rv ← st.read s1 i2
      let r ←
        if rv != 0#u64
        then
          do
          let a5 ← ar.vcpu_flush a3 rv
          let i3 ← lift (core.num.U64.wrapping_add rv vcpu.TCB)
          let gt ← st.read s1 i3
          let a6 ←
            if gt != 0#u64
            then
              do
              let a7 ← ar.fpu_flush a5 gt
              ar.fpu_release a7 gt
            else ok a5
          let i4 ← lift (core.num.U64.wrapping_add rv vcpu.OWNER_CPU)
          let i5 ← lift (core.num.U64.wrapping_add cpu 1#u64)
          let s3 ← st.write s1 i4 i5
          ok (s3, a6)
        else ok (s1, a3)
      f r) ⦃ P ⦄ := by
  refine WP.spec_bind (P0.vcpu.bound.p0 st s1 t L.total) fun v _ => ?_
  refine WP.spec_bind (show (if (v != 0#u64) = true then ar.vcpu_flush a2 v else ok a2) ⦃ _ => True ⦄ from ?_)
    fun a3 _ => ?_
  · by_cases hv : (v != 0#u64) = true
    · rw [if_pos hv]; exact hA.vcpu_flush_spec _ _
    · rw [if_neg hv]; exact (WP.spec_ok _).2 trivial
  · refine WP.spec_bind P0.Consts.layout.tcb.RUN_VCPU.spec fun i1 ei1 => ?_
    subst ei1
    simp only [lift, bind_ok]
    refine WP.spec_bind (L.read_spec s1 _) fun rv erv => ?_
    have hrv0 : rv = 0#u64 := erv.trans hrv
    subst hrv0
    rw [if_neg (by simp)]
    simp only [bind_ok]
    exact hf a3

/-- **`migrate_tcb` as a frame**: it writes the thread's affinity and
debug-list words only, and keeps the debug lists typed; to the thread's own
core it does nothing. a64: for a thread with `RUN_VCPU` 0 (`hrv`; under [J] `RunVcpuInv`, any thread not in
`TS_RUNNING_VM`), so that AArch64's VCPU steps write nothing (`migrate_vcpu_idle`). -/
theorem smp.migrate_tcb.frame {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t cpu : U64) (hT : TcbPlaced T) (hN : ∀ c ∈ Cs, NodePlaced st T s c) (hD : DbgTz st T Cs s)
    (hc : L.mem s (affA t) ∈ Cs) (hcpu : cpu ∈ Cs) (ht : t ∈ T) (hrv : L.mem s (runVcpuA t) = 0#u64) :
    smp.migrate_tcb st ar s a t cpu ⦃ s' _ => WritesIn st s s' (fun b => b = affA t ∨ DbgW st T Cs s b) ∧
      DbgTz st T Cs s' ∧ (L.mem s (affA t) = cpu → s' = s) ⦄ := by
  have hta := hT t ht
  have haa : Aligned (affA t) := field_aligned (K := 3520#u64) hta (by simp) (by simp)
  unfold smp.migrate_tcb
  step with obj.Tcb.affinity.spec as ⟨af, haf⟩
  split
  · rename_i hne
    have hne' : L.mem s (affA t) ≠ cpu := fun e => by
      subst haf; rw [e] at hne; simp at hne
    refine WP.spec_bind (objects.debug_remove.frame s t hT hN hD hc ht) fun s1 ⟨w1, D1⟩ => ?_
    refine WP.spec_bind (hA.fpu_flush _ _) fun a2 _ => ?_
    refine WP.spec_bind (hA.fpu_release _ _) fun a3 _ => ?_
    -- a64: the VCPU steps (`RUN_VCPU` is 0 at `s1`: `debug_remove` writes debug-list words only)
    have rv1 : L.mem s1 (runVcpuA t) = 0#u64 :=
      (w1.mem_eq (field_aligned (K := 3672#u64) hta (by simp) (by simp))
        (notDbgW_field (K := 3672#u64) hT hN ht (by simp) (by simp))).trans hrv
    refine migrate_vcpu_idle hA s1 a3 t cpu rv1 _ fun a4 => ?_
    try dsimp only
    refine WP.spec_bind (obj.Tcb.set_affinity.wr s1 t cpu) fun s2 e2 => ?_
    subst e2
    have hN2 : ∀ c ∈ Cs, NodePlaced st T (L.wr s1 (affA t) cpu) c := fun c hc' => ((hN c hc').ksb w1.1).wr
    have D2 : DbgTz st T Cs (L.wr s1 (affA t) cpu) := by
      refine ⟨fun y hy => ?_, fun y hy => ?_, fun c hc' => ?_⟩
      · rw [show dnA y = core.num.U64.wrapping_add y 3576#u64 from rfl, L.mem_wr_ne haa (field_aligned (K := 3576#u64) (hT y hy) (by simp) (by simp))
          (fun e => field_ne (K1 := 3520#u64) (K2 := 3576#u64) hta (hT y hy) (by simp) (by simp)
            (fun _ => by simp) (UScalar.eq_of_val_eq e))]
        exact D1.dn y hy
      · rw [show dpA y = core.num.U64.wrapping_add y 3584#u64 from rfl, L.mem_wr_ne haa (field_aligned (K := 3584#u64) (hT y hy) (by simp) (by simp))
          (fun e => field_ne (K1 := 3520#u64) (K2 := 3584#u64) hta (hT y hy) (by simp) (by simp)
            (fun _ => by simp) (UScalar.eq_of_val_eq e))]
        exact D1.dp y hy
      · have hN1 := (hN c hc').ksb w1.1
        rw [nodeAt_wr, L.mem_wr_ne haa (nodeAt_aligned hN1 (by simp [debug_val]) (by simp [debug_val]))
          (fun e => node_ne_field (K := 3520#u64) hN1 (by simp [debug_val]) ht hta (by simp)
            (UScalar.eq_of_val_eq e).symm)]
        exact D1.dh c hc'
    have w2 : WritesIn st s (L.wr s1 (affA t) cpu) (fun b => b = affA t ∨ DbgW st T Cs s b) :=
      WritesIn.mono (WritesIn.trans w1 (writesIn_wr haa)) fun b hb => hb.elim Or.inr Or.inl
    have hc2 : L.mem (L.wr s1 (affA t) cpu) (affA t) ∈ Cs := by rw [L.mem_wr_same haa]; exact hcpu
    refine WP.spec_bind (objects.debug_append.frame _ t hT hN2 D2 hc2 ht) fun s3 ⟨w3, D3⟩ => ?_
    refine (WP.spec_ok _).2 ⟨WritesIn.mono (WritesIn.trans w2 w3) fun b hb => ?_, D3, fun e => absurd e hne'⟩
    rcases hb with hb | hb | ⟨c, hc', e⟩
    · exact hb
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr ⟨c, hc', by rw [e, nodeAt_wr, nodeAt_of_ksb w1.1]⟩)
  · try simp only [Aeneas.Std.bind_ok]
    exact (WP.spec_ok _).2 ⟨WritesIn.refl _ _, hD, fun _ => rfl⟩

/-- A `Fr` frame keeps the debug lists (`Fr` keeps the TCBs' fields
3528–3592 and the nodes' word 88). -/
theorem DbgTz.of_fr {s s' : S} {Sg : Set U64} (f : Fr st T Sg s s') (hN : ∀ c ∈ Cs, NodePlaced st T s c)
    (D : DbgTz st T Cs s) : DbgTz st T Cs s' := by
  refine ⟨fun y hy => ?_, fun y hy => ?_, fun c hc => ?_⟩
  · rw [show dnA y = core.num.U64.wrapping_add y 3576#u64 from rfl, f.tmr y hy _ (by simp) (by simp) (by simp)]
    exact D.dn y hy
  · rw [show dpA y = core.num.U64.wrapping_add y 3584#u64 from rfl, f.tmr y hy _ (by simp) (by simp) (by simp)]
    exact D.dp y hy
  · rw [nodeAt_of_ksb f.ksb, f.tnd c (hN c hc) _ (by rw [debug_val]; simp)]
    exact D.dh c hc

/-- The debug lists typed, from `XInv`. -/
theorem XInv.dbg {s : S} (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) : DbgTz st T Cs s :=
  ⟨hX.2.2.tm.dn, hX.2.2.tm.dp, hX.2.2.tm.dh⟩

/-- **The second half of `donate` as a frame**: the SC's `TCB` word, the
receiver's `SC` field, then `migrate_tcb` (its affinity and the debug-list
words). -/
theorem donate_tail.frame {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {X : Set U64} (s6 : S) (a : A)
    (sc dst : U64) {Q : U64 → U64 → List U64} {R : U64 → List U64} (h6 : SchedQueuesInvX st T Cs Ω H X s6 Q R)
    (D6 : DbgTz st T Cs s6) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s6) (hsub : ∀ b ∈ Sg, b ∈ Ω) (hsc : sc ∈ Scs)
    (hdst : dst ∈ T) (hcore : L.mem s6 (scCoreA sc) ∈ Cs) (hrv : L.mem s6 (runVcpuA dst) = 0#u64) :
    (do
      let s2 ← obj.Sc.set_tcb st sc s6 dst
      let s3 ← obj.Tcb.set_sc st dst s2 sc
      let i1 ← obj.Sc.cpu st sc s3
      smp.migrate_tcb st ar s3 a dst i1) ⦃ s' _ =>
        WritesIn st s6 s' (fun b => b = scTcbA sc ∨ b = scA dst ∨ b = affA dst ∨ DbgW st T Cs s6 b) ∧
        (L.mem s6 (affA dst) = L.mem s6 (scCoreA sc) →
          WritesIn st s6 s' (fun b => b = scTcbA sc ∨ b = scA dst)) ⦄ := by
  have hT := h6.tcbs
  have hta := hT dst hdst
  have hm : scTcbA sc ∈ Ω := ((objs_omega hO hsub).2 sc hsc).1
  have hcO : scCoreA sc ∈ Ω := ((objs_omega hO hsub).2 sc hsc).2.1
  have hne : (scTcbA sc).val ≠ (scCoreA sc).val := by
    obtain ⟨hP, hz⟩ := hO.sc sc hsc; rw [scTcbA_val hP hz, scCoreA_val hP hz]; omega
  have ho := h6.omega _ hm
  have hco := h6.omega _ hcO
  step with obj.Sc.set_tcb.wr as ⟨s7, e7⟩
  step with obj.Tcb.set_sc.wr as ⟨s8, e8⟩
  subst e7 e8
  step with obj.Sc.cpu.spec as ⟨cpu, ecpu⟩
  set s8 := L.wr (L.wr s6 (scTcbA sc) dst) (scA dst) sc with hs8
  have k8 : L.ksb s8 = L.ksb s6 := by simp [hs8, L.ksb_wr]
  have w8 : WritesIn st s6 s8 (fun b => b = scTcbA sc ∨ b = scA dst) :=
    WritesIn.mono (WritesIn.trans (writesIn_wr ho.1) (writesIn_wr (scA_aligned hta))) fun _ hb => hb
  have hN8 : ∀ c ∈ Cs, NodePlaced st T s8 c := fun c hc => (h6.nodes c hc).ksb k8
  have hdW : ∀ b, Aligned b → (b = scTcbA sc ∨ b = scA dst) → ¬ DbgW st T Cs s6 b := by
    rintro b - (rfl | rfl)
    · exact notDbgW_out hT h6.nodes ho
    · rw [scA_eq]; exact notDbgW_field hT h6.nodes hdst (by simp) (by simp)
  have D8 : DbgTz st T Cs s8 := DbgTz.of_writes hT h6.nodes w8 hdW D6
  have haffe : L.mem s8 (affA dst) = L.mem s6 (affA dst) := by
    rw [show affA dst = core.num.U64.wrapping_add dst 3520#u64 from rfl, w8.mem_eq (field_aligned (K := 3520#u64) hta (by simp) (by simp)) (by
      rintro (e | e)
      · exact out_ne_field (K := 3520#u64) ho hdst hta (by simp) (congrArg UScalar.val e)
      · exact field_ne (K1 := 3520#u64) (K2 := 3464#u64) hta hta (by simp) (by simp) (fun _ => by simp) e)]
  have ha8 : L.mem s8 (affA dst) ∈ Cs := by rw [haffe]; exact h6.aff dst hdst
  have hcpue : cpu = L.mem s6 (scCoreA sc) := by
    rw [ecpu, w8.mem_eq hco.1 (by
      rintro (e | e)
      · exact hne (congrArg UScalar.val e).symm
      · exact out_ne_field (K := 3464#u64) hco hdst hta (by simp) (congrArg UScalar.val e).symm)]
  have hc8 : cpu ∈ Cs := by rw [hcpue]; exact hcore
  have rv8 : L.mem s8 (runVcpuA dst) = 0#u64 := by
    rw [show runVcpuA dst = core.num.U64.wrapping_add dst 3672#u64 from rfl, w8.mem_eq (field_aligned (K := 3672#u64) hta (by simp) (by simp)) (by
      rintro (e | e)
      · exact out_ne_field (K := 3672#u64) ho hdst hta (by simp) (congrArg UScalar.val e)
      · exact field_ne (K1 := 3672#u64) (K2 := 3464#u64) hta hta (by simp) (by simp) (fun _ => by simp) e)]
    exact hrv
  refine WP.spec_mono (smp.migrate_tcb.frame hA s8 a dst cpu hT hN8 D8 ha8 hc8 hdst rv8) fun r hr => ?_
  obtain ⟨s', a'⟩ := r
  obtain ⟨w, -, hid⟩ := hr
  refine ⟨WritesIn.mono (WritesIn.trans w8 w) fun b hb => ?_, fun he => ?_⟩
  swap
  · rw [hid (by rw [haffe, hcpue]; exact he)]; exact w8
  rcases hb with (hb | hb) | hb | hb | ⟨c, hc, e⟩
  · exact Or.inl hb
  · exact Or.inr (Or.inl hb)
  · exact Or.inr (Or.inr (Or.inl hb))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hb)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨c, hc, by rw [e, nodeAt_of_ksb k8]⟩)))

/-- What `donate`'s second half keeps: the current core's thread, idle,
action and current-SC words, and the TCB fields other than the receiver's
`SC` and affinity fields and the debug links. -/
theorem donW_keeps {s s' : S} {sc dst : U64} (hT : TcbPlaced T) (hN : ∀ c ∈ Cs, NodePlaced st T s c)
    (hcur : L.cpu s ∈ Cs) (hm : OutsideObjs st T Cs s (scTcbA sc)) (hdst : dst ∈ T)
    (w : WritesIn st s s' (fun b => b = scTcbA sc ∨ b = scA dst ∨ b = affA dst ∨ DbgW st T Cs s b)) :
    L.curW s' = L.curW s ∧ L.idleW s' = L.idleW s ∧ L.actionW s' = L.actionW s ∧ L.cscW s' = L.cscW s ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3576 → K.val ≠ 3584 →
        (y = dst → K.val ≠ 3464 ∧ K.val ≠ 3520) →
        L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) := by
  have hNc := hN _ hcur
  have hta := hT dst hdst
  have nod : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 88 →
      L.mem s' (L.nodeAt s' (L.cpu s') o) = L.mem s (L.nodeAt s (L.cpu s) o) := fun o h1 h2 h3 => by
    rw [w.2.1, nodeAt_of_ksb w.1]
    refine w.mem_eq (nodeAt_aligned hNc h1 h2) ?_
    rintro (e | e | e | hd)
    · exact out_ne_node hm hcur hNc h1 (congrArg UScalar.val e)
    · exact node_ne_field (K := 3464#u64) hNc h1 hdst hta (by simp) e
    · exact node_ne_field (K := 3520#u64) hNc h1 hdst hta (by simp) e
    · exact notDbgW_node hT hN hcur h1 h3 hd
  refine ⟨nod _ (by simp [curth0]) (by simp [curth0]) (by simp [curth0]),
    nod _ (by simp [idle8]) (by simp [idle8]) (by simp [idle8]),
    nod _ (by simp [act_val]) (by simp [act_val]) (by simp [act_val]),
    by unfold LawfulStore.cscW LawfulStore.nodeA
       exact nod _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]),
    fun y hy K hK hK8 h1 h2 hne => ?_⟩
  refine w.mem_eq (field_aligned (hT y hy) hK hK8) ?_
  rintro (e | e | e | hd)
  · exact out_ne_field hm hy (hT y hy) hK (congrArg UScalar.val e)
  · exact field_ne (K2 := 3464#u64) (hT y hy) hta hK (by simp)
      (fun e' => by have := (hne e').1; simpa using this) e
  · exact field_ne (K2 := 3520#u64) (hT y hy) hta hK (by simp)
      (fun e' => by have := (hne e').2; simpa using this) e
  · exact notDbgW_field hT hN hy hK ⟨h1, h2⟩ hd

/-- The debug-list steps keep the fields `migrate_tcb`'s callers track. -/
theorem dbgW_keeps {s s' : S} {dst sc : U64} (hT : TcbPlaced T) (hN : ∀ c ∈ Cs, NodePlaced st T s c)
    (hcur : L.cpu s ∈ Cs) (ho : OutsideObjs st T Cs s (scTcbA sc)) (hd : dst ∈ T)
    (hw : WritesIn st s s' (DbgW st T Cs s)) :
    (∀ y ∈ T, L.mem s' (stA y) = L.mem s (stA y)) ∧ (∀ y ∈ T, L.mem s' (replyA y) = L.mem s (replyA y)) ∧
      L.mem s' (scA dst) = L.mem s (scA dst) ∧ L.mem s' (scTcbA sc) = L.mem s (scTcbA sc) ∧
      L.actionW s' = L.actionW s ∧ L.mem s' (inqA dst) = L.mem s (inqA dst) := by
  refine ⟨fun y hy => ?_, fun y hy => ?_, ?_, hw.mem_eq ho.1 (notDbgW_out hT hN ho), hw.dbg_act hT hN hcur, ?_⟩
  · rw [stA_eq]
    exact hw.mem_eq (field_aligned (hT y hy) (by simp) (by simp)) (notDbgW_field hT hN hy (by simp) (by simp))
  · exact hw.mem_eq (field_aligned (K := 3360#u64) (hT y hy) (by simp) (by simp))
      (notDbgW_field (K := 3360#u64) hT hN hy (by simp) (by simp))
  · rw [scA_eq]
    exact hw.mem_eq (field_aligned (hT dst hd) (by simp) (by simp)) (notDbgW_field hT hN hd (by simp) (by simp))
  · rw [inqA_eq]
    exact hw.mem_eq (field_aligned (hT dst hd) (by simp) (by simp)) (notDbgW_field hT hN hd (by simp) (by simp))

/-- The affinity write of `migrate_tcb`, for a thread `dst` in no ready or
release queue whose SC (if any) is on the core `cpu`: `ScAff` is restored. -/
theorem migrate_aff {X : Set U64} {s8 : S} {sc dst cpu : U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h8 : SchedQueuesInvX st T Cs Ω H X s8 Q R) (hB8 : BoundInv st T Ac s8) (hX8 : XInvW st T Cs Ω Sg Rp Scs Nt Z dst s8)
    (hS8 : SCsOK st T Ω Sg Scs Z Ac s8) (hSg8 : SgOK st Ω Sg s8) (hto : dst ∈ T)
    (htq : (L.mem s8 (inqA dst) &&& sched.Q_QUEUED) = 0#u64) (htr : (L.mem s8 (inqA dst) &&& sched.Q_RELEASE) = 0#u64)
    (hc' : cpu ∈ Cs) (hsc : sc ∈ Scs)
    (hcore : L.mem s8 (scA dst) ≠ 0#u64 → L.mem s8 (scCoreA (L.mem s8 (scA dst))) = cpu) :
    BlkOKX st T Cs Ω H Sg Rp Scs Nt Z Ac X (L.wr s8 (affA dst) cpu) ∧
      (∀ y ∈ T, L.mem (L.wr s8 (affA dst) cpu) (stA y) = L.mem s8 (stA y)) ∧
      (∀ y ∈ T, L.mem (L.wr s8 (affA dst) cpu) (replyA y) = L.mem s8 (replyA y)) ∧
      TmFr st T Cs Nt s8 (L.wr s8 (affA dst) cpu) ∧
      (L.mem (L.wr s8 (affA dst) cpu) (scA dst) = L.mem s8 (scA dst) ∧
        L.mem (L.wr s8 (affA dst) cpu) (scTcbA sc) = L.mem s8 (scTcbA sc) ∧
        L.actionW (L.wr s8 (affA dst) cpu) = L.actionW s8) := by
  have hT := h8.tcbs
  have hta := hT dst hto
  have hO := hX8.1.1
  have hE := hX8.1.2.2
  have hN' := h8.nodes _ h8.cur
  have hm : scTcbA sc ∈ Ω := hSg8.sub _ (hO.fixW sc hsc).1
  have ho := h8.omega _ hm
  obtain ⟨hrΩ, hcΩ⟩ := objs_omega hO hSg8.sub
  have ha : Aligned (affA dst) := field_aligned (K := 3520#u64) hta (by simp) (by simp)
  have tm9 : TmFr st T Cs Nt s8 (L.wr s8 (affA dst) cpu) :=
    TmFr.wr hT h8.nodes hO ha
      (notTmW_field (K := 3520#u64) hT h8.nodes (fun n hn => h8.omega _ (hSg8.sub _ (hO.ntB n hn).2)) hto
        (by simp) (by simp))
  -- the frame of the write
  have kf : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (y = dst → K.val ≠ 3520) →
      L.mem (L.wr s8 (affA dst) cpu) (core.num.U64.wrapping_add y K) = L.mem s8 (core.num.U64.wrapping_add y K) :=
    fun y hy K hK hK8 hne => L.mem_wr_ne ha (field_aligned (hT y hy) hK hK8)
      (fun e => field_ne (K1 := 3520#u64) hta (hT y hy) (by simp) hK
        (fun e' => by subst e'; exact fun h' => hne rfl h'.symm) (UScalar.eq_of_val_eq e))
  have ko : ∀ a ∈ Ω, L.mem (L.wr s8 (affA dst) cpu) a = L.mem s8 a := fun a ha' =>
    L.mem_wr_ne ha (h8.omega a ha').1 (fun e => out_ne_field (K := 3520#u64) (h8.omega a ha') hto hta (by simp) e)
  have hn : ∀ o : U64, (o.val = 0 ∨ o.val = 8 ∨ o.val = 16 ∨ o.val = 24) →
      (affA dst).val ≠ (L.nodeAt s8 (L.cpu s8) o).val :=
    fun o ho' e => node_ne_field hN' (by omega) hto hta (K := 3520#u64) (by simp) (UScalar.eq_of_val_eq e).symm
  obtain ⟨b1, ecs⟩ := bnd_wr (v := cpu) h8 hB8 ha
    (fun y hy => ⟨fun e => field_ne (K1 := 3520#u64) (K2 := 3464#u64) hta (hT y hy) (by simp) (by simp)
        (fun _ => by simp) (UScalar.eq_of_val_eq e),
      fun e => by
        rw [inqA_eq] at e
        exact field_ne (K1 := 3520#u64) hta (hT y hy) (by simp) (by simp) (fun _ => by simp) (UScalar.eq_of_val_eq e)⟩)
    hn (fun y hy e => by
      rw [stA_eq] at e
      exact field_ne (K1 := 3520#u64) hta (hT y hy) (by simp) (by simp) (fun _ => by simp) (UScalar.eq_of_val_eq e))
  have ei : L.idleW (L.wr s8 (affA dst) cpu) = L.idleW s8 := by
    unfold LawfulStore.idleW; rw [LawfulStore.cpu_wr, nodeAt_wr]
    exact L.mem_wr_ne ha (nodeAt_aligned hN' (by rw [idle8]; omega) (by rw [idle8]))
      (hn _ (Or.inr (Or.inl idle8)))
  have hsc9 : ∀ y ∈ T, L.mem (L.wr s8 (affA dst) cpu) (scA y) = L.mem s8 (scA y) := fun y hy => by
    rw [scA_eq]; exact kf y hy _ (by simp) (by simp) (fun _ => by simp)
  have x0 : XInv0 st T Cs Ω Sg Rp Scs Nt Z (L.wr s8 (affA dst) cpu) := hX8.1.keep
    (fun r hr => ⟨ko _ (hrΩ r hr).1, ko _ (hrΩ r hr).2.1, ko _ (hrΩ r hr).2.2⟩)
    (fun c hc => ⟨ko _ (hcΩ c hc).1, ko _ (hcΩ c hc).2.1⟩) hsc9
    (fun y hy => kf y hy _ (by simp) (by simp) (fun _ => by simp))
    (fun y hy => by rw [stA_eq]; exact kf y hy _ (by simp) (by simp) (fun _ => by simp))
    (by rw [ecs]; exact hE.cur)
    (fun c hc => ko _ (hSg8.sub _ (hO.repW c hc)))
    (fun y hy => kf y hy _ (by simp) (by simp) (fun _ => by simp))
    (fun n hn => ko _ (hSg8.sub _ (hO.ntW n hn)))
    ⟨hE.tm.tmfr tm9, hE.ntb.tmfr tm9, hE.rb.tmfr tm9, tm9.2.2.2.1⟩
    (fun c hc => ko _ (hSg8.sub _ (hO.snW c hc)))
    (fun y hy => kf y hy _ (by simp) (by simp) (fun _ => by simp))
    (fun c hc => ko _ (hSg8.sub _ (hO.syW c hc)))
    (fun c hc => ko _ (hSg8.sub _ (hO.mxW c hc))) ei
  have b2 : XInv st T Cs Ω Sg Rp Scs Nt Z (L.wr s8 (affA dst) cpu) := x0.x
    (hX8.2.1.keep hE.yt.1 (fun c hc => ko _ (hcΩ c hc).1) hsc9)
    (ScAffX.restore hX8.2.2 (fun t ht h0 => (hE.bound t ht h0).1) hsc9 (fun c hc => ko _ (hcΩ c hc).2.1)
      (fun t ht hne => kf t ht _ (by simp) (by simp) (fun e => absurd e hne))
      (fun _ h0 => by rw [L.mem_wr_same ha]; exact (hcore h0).symm))
  refine ⟨⟨⟨Q, R, inv_wr_aff h8 hto htq htr hc'⟩, b1, b2,
    SCsOK.fieldO (K := 3520#u64) h8 hS8 hO hto (by simp) (by simp) (by simp),
    ⟨hSg8.sub, fun b hb => by rw [L.ksb_wr]; exact hSg8.ks b hb, fun o h1 h2 => by rw [L.ksb_wr]; exact hSg8.ksΩ o h1 h2⟩⟩,
    fun y hy => ?_, fun y hy => kf y hy _ (by simp) (by simp) (fun _ => by simp), tm9,
    hsc9 dst hto, ko _ hm, act_wr_field (K := 3520#u64) (a := affA dst) hN' hto hta rfl (by simp) (by simp)⟩
  rw [stA_eq]; exact kf y hy _ (by simp) (by simp) (fun _ => by simp)

/-- `migrate_tcb` of a thread `dst` in no ready or release queue to the core
`cpu` of its SC (if any): off its old core's debug list, the affinity write,
onto the new core's. `ScAff` holds off `dst` before and in full after. -/
theorem migrate_tail {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {X : Set U64} (s8 : S) (a : A)
    (sc dst cpu : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h8 : SchedQueuesInvX st T Cs Ω H X s8 Q R) (hB8 : BoundInv st T Ac s8) (hX8 : XInvW st T Cs Ω Sg Rp Scs Nt Z dst s8)
    (hS8 : SCsOK st T Ω Sg Scs Z Ac s8) (hSg8 : SgOK st Ω Sg s8) (hto : dst ∈ T)
    (htq : (L.mem s8 (inqA dst) &&& sched.Q_QUEUED) = 0#u64) (htr : (L.mem s8 (inqA dst) &&& sched.Q_RELEASE) = 0#u64)
    (hc' : cpu ∈ Cs) (hsc : sc ∈ Scs)
    (hcore : L.mem s8 (scA dst) ≠ 0#u64 → L.mem s8 (scCoreA (L.mem s8 (scA dst))) = cpu)
    (hrv : L.mem s8 (runVcpuA dst) = 0#u64) :
    smp.migrate_tcb st ar s8 a dst cpu ⦃ s' _ => BlkOKX st T Cs Ω H Sg Rp Scs Nt Z Ac X s' ∧
        (∀ y ∈ T, L.mem s' (stA y) = L.mem s8 (stA y)) ∧ (∀ y ∈ T, L.mem s' (replyA y) = L.mem s8 (replyA y)) ∧
        TmFr st T Cs Nt s8 s' ∧
        (L.mem s' (scA dst) = L.mem s8 (scA dst) ∧ L.mem s' (scTcbA sc) = L.mem s8 (scTcbA sc) ∧
          L.actionW s' = L.actionW s8) ⦄ := by
  have hT := h8.tcbs
  have hO := hX8.1.1
  have hm : scTcbA sc ∈ Ω := hSg8.sub _ (hO.fixW sc hsc).1
  have h0 : BlkOKW st T Cs Ω H Sg Rp Scs Nt Z Ac X dst s8 := ⟨⟨Q, R, h8⟩, hB8, hX8, hS8, hSg8⟩
  unfold smp.migrate_tcb
  step with obj.Tcb.affinity.spec as ⟨af, eaf⟩
  split
  · refine WP.spec_bind (objects.debug_remove.w s8 dst h0 hto) fun s1 ⟨h1, m1, w1⟩ => ?_
    obtain ⟨st1, rp1, sc1, t1, a1, iq1⟩ := dbgW_keeps hT h8.nodes h8.cur (h8.omega _ hm) hto w1
    obtain ⟨⟨Q1, R1, q1⟩, hB1, hX1, hS1, hSg1⟩ := h1
    have hcore1 : L.mem s1 (scA dst) ≠ 0#u64 → L.mem s1 (scCoreA (L.mem s1 (scA dst))) = cpu := fun h0' => by
      rw [sc1] at h0' ⊢
      have hco := h8.omega _ (hSg8.sub _ (hO.fixW _ (hX8.1.2.2.bound dst hto h0').1).2)
      rw [w1.mem_eq hco.1 (notDbgW_out hT h8.nodes hco)]; exact hcore h0'
    refine WP.spec_bind (hA.fpu_flush _ _) fun a2 _ => ?_
    refine WP.spec_bind (hA.fpu_release _ _) fun a3 _ => ?_
    -- a64: the VCPU steps (`RUN_VCPU` is 0 at `s1`: `debug_remove` writes debug-list words only)
    have rv1 : L.mem s1 (runVcpuA dst) = 0#u64 :=
      (w1.mem_eq (field_aligned (K := 3672#u64) (hT dst hto) (by simp) (by simp))
        (notDbgW_field (K := 3672#u64) hT h8.nodes hto (by simp) (by simp))).trans hrv
    refine migrate_vcpu_idle hA s1 a3 dst cpu rv1 _ fun a4 => ?_
    try dsimp only
    refine WP.spec_bind (obj.Tcb.set_affinity.wr s1 dst cpu) fun s2 e2 => ?_
    subst e2
    obtain ⟨g2, st2, rp2, m2, sc2, t2, a2'⟩ := migrate_aff (sc := sc) q1 hB1 hX1 hS1 hSg1 hto
      (by rw [iq1]; exact htq) (by rw [iq1]; exact htr) hc' hsc hcore1
    have q2 := g2.1.choose_spec.choose_spec
    refine WP.spec_bind (objects.debug_append.x _ dst g2 hto) fun s3 ⟨h3, m3, w3⟩ => ?_
    obtain ⟨st3, rp3, sc3, t3, a3', -⟩ := dbgW_keeps hT q2.nodes q2.cur (q2.omega _ hm) hto w3
    refine (WP.spec_ok _).2 ⟨h3, fun y hy => (st3 y hy).trans ((st2 y hy).trans (st1 y hy)),
      fun y hy => (rp3 y hy).trans ((rp2 y hy).trans (rp1 y hy)), m1.trans (m2.trans m3),
      sc3.trans (sc2.trans sc1), t3.trans (t2.trans t1), a3'.trans (a2'.trans a1)⟩
  · rename_i hne
    have e : af = cpu := UScalar.eq_of_val_eq (by simpa using hne)
    have hX : XInv st T Cs Ω Sg Rp Scs Nt Z s8 :=
      hX8.1.x hX8.2.1 (hX8.2.2.full fun _ h0' => by rw [hcore h0', ← eaf, e])
    try simp only [Aeneas.Std.bind_ok]
    exact (WP.spec_ok _).2 ⟨⟨⟨Q, R, h8⟩, hB8, hX, hS8, hSg8⟩, fun _ _ => rfl, fun _ _ => rfl, TmFr.refl (L := L) _,
      rfl, rfl, rfl⟩


/-- The second half of `donate`: the SC `sc` (bound to no thread) gets `to`
(in no ready or release queue), which migrates to the SC's core. -/
theorem donate_tail {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {X : Set U64} (s6 : S) (a : A) (sc dst : U64)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h6 : SchedQueuesInvX st T Cs Ω H X s6 Q R) (hB6 : BoundInv st T Ac s6) (hX6 : XInv0 st T Cs Ω Sg Rp Scs Nt Z s6)
    (htx6 : TScX st Scs sc s6) (haf6 : ScAff st T s6) (hd0 : L.mem s6 (scA dst) = 0#u64)
    (hS6 : SCsOK st T Ω Sg Scs Z Ac s6) (hSg6 : SgOK st Ω Sg s6) (hto : dst ∈ T)
    (htq : (L.mem s6 (inqA dst) &&& sched.Q_QUEUED) = 0#u64) (htr : (L.mem s6 (inqA dst) &&& sched.Q_RELEASE) = 0#u64)
    (hsc : sc ∈ Scs) (hsc0 : sc ≠ 0#u64) (hnb : ∀ y ∈ T, L.mem s6 (scA y) ≠ sc)
    (hcore : L.mem s6 (scCoreA sc) ∈ Cs)
    (hdisj : sc ≠ L.cscW s6 → ∀ b, InSC sc (Z sc) b → Outside b (L.cscW s6) (Z (L.cscW s6)))
    (hsA : Sch st s6 dst → sc ∈ Ac) (hdi : L.idleW s6 ≠ dst) (hrv : L.mem s6 (runVcpuA dst) = 0#u64) :
    (do
      let s2 ← obj.Sc.set_tcb st sc s6 dst
      let s3 ← obj.Tcb.set_sc st dst s2 sc
      let i1 ← obj.Sc.cpu st sc s3
      smp.migrate_tcb st ar s3 a dst i1) ⦃ s' _ => BlkOKX st T Cs Ω H Sg Rp Scs Nt Z Ac X s' ∧
        (∀ y ∈ T, L.mem s' (stA y) = L.mem s6 (stA y)) ∧ (∀ y ∈ T, L.mem s' (replyA y) = L.mem s6 (replyA y)) ∧
        TmFr st T Cs Nt s6 s' ∧
        (L.mem s' (scA dst) = sc ∧ L.mem s' (scTcbA sc) = dst ∧ L.actionW s' = L.actionW s6) ⦄ := by
  have hO := hX6.1
  step with obj.Sc.set_tcb.wr as ⟨s7, e7⟩
  step with obj.Tcb.set_sc.wr as ⟨s8, e8⟩
  subst e7 e8
  obtain ⟨h8, hB8, hX8, hS8, hSg8, tm8, fld8, core8, sc8, t8, a8⟩ :=
    donate_pair h6 hB6 hX6 htx6 haf6 hd0 hS6 hSg6 hto hsc hsc0 hnb hcore hdisj hsA hdi
  step with obj.Sc.cpu.spec as ⟨cpu, ecpu⟩
  have hc' : cpu ∈ Cs := by rw [ecpu, core8]; exact hcore
  have iq8 : L.mem (L.wr (L.wr s6 (scTcbA sc) dst) (scA dst) sc) (inqA dst) = L.mem s6 (inqA dst) := by
    rw [inqA_eq]; exact fld8 dst hto _ (by simp) (by simp) (fun _ => by simp)
  refine WP.spec_mono (migrate_tail hA _ a sc dst cpu Q R h8 hB8 hX8 hS8 hSg8 hto (by rw [iq8]; exact htq)
    (by rw [iq8]; exact htr) hc' hsc (fun _ => by rw [sc8, ecpu])
    ((fld8 dst hto 3672#u64 (by simp) (by simp) (fun _ => by simp)).trans hrv)) fun r hh => ?_
  obtain ⟨s', a'⟩ := r
  obtain ⟨b1, st1, rp1, tm1, sc1, t1, a1⟩ := hh
  refine ⟨b1, fun y hy => (st1 y hy).trans ?_, fun y hy => (rp1 y hy).trans ?_, tm8.trans tm1,
    sc1.trans sc8, t1.trans t8, a1.trans a8⟩
  · rw [stA_eq]; exact fld8 y hy _ (by simp) (by simp) (fun _ => by simp)
  · exact fld8 y hy _ (by simp) (by simp) (fun _ => by simp)

/-- a64: `s'` is `s`, or `s` with one word of the current core's `IPI_PENDING` pair written. -/
def IpiW (st : machine.Store S) [L : LawfulStore st] (s s' : S) : Prop :=
  s' = s ∨ ∃ o v, (o.val = 120 ∨ o.val = 128) ∧ s' = L.wr s (L.nodeAt s (L.cpu s) o) v

/-- a64: `remote_reschedule` (AArch64: `smp::add_pending`) writes at most one word of the pair. -/
theorem smp.remote_reschedule.ipi {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (cpu : U64) :
    smp.remote_reschedule st ar s a cpu ⦃ s' _ => IpiW st s s' ⦄ := by
  unfold smp.remote_reschedule
  step with LawfulStore.cur_cpu_spec as ⟨i, _⟩
  split
  · refine WP.spec_bind (smp.add_pending.spec s cpu) fun s1 h1 => ?_
    simp only [WP.spec_ok, WP.uncurry'_pair]; exact Or.inr h1
  · simp only [WP.spec_ok, WP.uncurry'_pair]; exact Or.inl rfl

/-- a64: AArch64's `remote_tcb_stall` stalls the core running `t` and, for a thread with a bound VCPU, the
core running the VCPU's `RUN_CALLER`: at most two `remote_reschedule`s, each one word of the pair. -/
theorem smp.remote_tcb_stall.ipi {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t : obj.Tcb) :
    smp.remote_tcb_stall st ar s a t ⦃ s' _ => ∃ s1, IpiW st s s1 ∧ IpiW st s1 s' ⦄ := by
  unfold smp.remote_tcb_stall
  refine WP.spec_bind (obj.Tcb.affinity.spec s t) fun cpu _ => ?_
  refine WP.spec_bind (LawfulStore.cur_cpu_spec s) fun i _ => ?_
  refine WP.spec_bind (Pₘ := fun r : S × A × obj.Tcb => IpiW st s r.1 ∧ r.2.2 = t) ?_ ?_
  · split
    · refine WP.spec_bind (obj.node_get.spec s cpu _) fun i1 _ => ?_
      refine WP.spec_bind (Pₘ := fun r : S × A => IpiW st s r.1) ?_ fun r hr => ?_
      · split
        · refine WP.spec_bind (hA.remote_stall_spec _ _) fun a2 _ => ?_
          exact WP.spec_mono (smp.remote_reschedule.ipi s a2 cpu) fun r hr => by
            obtain ⟨_, _⟩ := r; exact hr
        · exact (WP.spec_ok _).2 (Or.inl rfl)
      · obtain ⟨t2, t3⟩ := r
        try dsimp only
        exact (WP.spec_ok _).2 ⟨hr, rfl⟩
    · exact (WP.spec_ok _).2 ⟨Or.inl rfl, rfl⟩
  · rintro ⟨s1, a1, t1⟩ ⟨h1, e1⟩
    try dsimp only at h1 e1 ⊢
    subst e1
    refine WP.spec_bind (P0.vcpu.bound.p0 st s1 t1 L.total) fun v _ => ?_
    have fin : ((ok (s1, a1)) : Result (S × A)) ⦃ s' _ => ∃ s2, IpiW st s s2 ∧ IpiW st s2 s' ⦄ :=
      (WP.spec_ok _).2 ⟨s1, h1, Or.inl rfl⟩
    split
    · simp only [lift, bind_ok]
      refine WP.spec_bind (L.read_spec s1 _) fun caller _ => ?_
      split
      · refine WP.spec_bind (obj.Tcb.affinity.spec s1 caller) fun c_cpu _ => ?_
        refine WP.spec_bind (LawfulStore.cur_cpu_spec s1) fun i2 _ => ?_
        split
        · refine WP.spec_bind (obj.node_get.spec s1 c_cpu _) fun i3 _ => ?_
          split
          · refine WP.spec_bind (hA.remote_stall_spec _ _) fun a2 _ => ?_
            exact WP.spec_mono (smp.remote_reschedule.ipi s1 a2 c_cpu) fun r hr => by
              obtain ⟨_, _⟩ := r; exact ⟨s1, h1, hr⟩
          · exact fin
        · exact fin
      · exact fin
    · exact fin

/-- `remote_tcb_stall` keeps the invariants. a64: through the two possible `IPI_PENDING` writes
(`remote_tcb_stall.ipi`), each by `ipi_all`. -/
theorem smp.remote_tcb_stall.all {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t : obj.Tcb) {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) :
    smp.remote_tcb_stall st ar s a t ⦃ s' _ => SchedQueuesInvX st T Cs Ω H X s' Q R ∧ BoundInv st T Ac s' ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧ SCsOK st T Ω Sg Scs Z Ac s' ∧ SgOK st Ω Sg s' ∧
      L.actionW s' = L.actionW s ∧ L.curW s' = L.curW s ∧ L.idleW s' = L.idleW s ∧ L.cscW s' = L.cscW s ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ a ∈ Ω, L.mem s' a = L.mem s a) ⦄ := by
  have one : ∀ s0 s0' : S, SchedQueuesInvX st T Cs Ω H X s0 Q R → BoundInv st T Ac s0 →
      XInv st T Cs Ω Sg Rp Scs Nt Z s0 → SCsOK st T Ω Sg Scs Z Ac s0 → SgOK st Ω Sg s0 → IpiW st s0 s0' →
      SchedQueuesInvX st T Cs Ω H X s0' Q R ∧ BoundInv st T Ac s0' ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z s0' ∧ SCsOK st T Ω Sg Scs Z Ac s0' ∧ SgOK st Ω Sg s0' ∧
      L.actionW s0' = L.actionW s0 ∧ L.curW s0' = L.curW s0 ∧ L.idleW s0' = L.idleW s0 ∧ L.cscW s0' = L.cscW s0 ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        L.mem s0' (core.num.U64.wrapping_add y K) = L.mem s0 (core.num.U64.wrapping_add y K)) ∧
      (∀ a ∈ Ω, L.mem s0' a = L.mem s0 a) := by
    intro s0 s0' h0 hB0 hX0 hS0 hSg0 hw
    rcases hw with rfl | ⟨o, v, ho, rfl⟩
    · exact ⟨h0, hB0, hX0, hS0, hSg0, rfl, rfl, rfl, rfl, fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩
    · exact ipi_all ho h0 hB0 hX0 hS0 hSg0
  refine WP.spec_mono (smp.remote_tcb_stall.ipi hA s a t) fun r hr => ?_
  obtain ⟨s', a'⟩ := r
  simp only [WP.uncurry'_pair] at hr ⊢
  obtain ⟨s1, w1, w2⟩ := hr
  obtain ⟨a1, b1, c1, d1, e1, f1, g1, h1, i1, j1, k1⟩ := one _ _ h hB hX hS hSg w1
  obtain ⟨a2, b2, c2, d2, e2, f2, g2, h2, i2, j2, k2⟩ := one _ _ a1 b1 c1 d1 e1 w2
  exact ⟨a2, b2, c2, d2, e2, f2.trans f1, g2.trans g1, h2.trans h1, i2.trans i1,
    fun y hy K hK hK8 => (j2 y hy K hK hK8).trans (j1 y hy K hK hK8), fun a ha => (k2 a ha).trans (k1 a ha)⟩

/-- seL4 `schedContext_donate` of the SC `sc` of `fr` (in no ready or
release queue, not the switch-to candidate, not idle) to `dst` (unbound, in no
queue, not the candidate). -/
theorem schedcontext.donate.ipc {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {X : Set U64} (s : S) (a : A)
    (sc dst fr : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hfr : fr ∈ T) (hscf : L.mem s (scA fr) = sc)
    (hsc0 : sc ≠ 0#u64)
    (hfout : (L.mem s (inqA fr) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s (inqA fr) &&& sched.Q_RELEASE) = 0#u64 ∧
      L.actionW s ≠ fr)
    (hfi : L.idleW s ≠ fr) (hdst : dst ∈ T) (hd0 : L.mem s (scA dst) = 0#u64)
    (hdq : (L.mem s (inqA dst) &&& sched.Q_QUEUED) = 0#u64) (hdr : (L.mem s (inqA dst) &&& sched.Q_RELEASE) = 0#u64)
    (hda : L.actionW s ≠ dst) (hne : dst ≠ fr) (hscA : sc ∈ Ac) (hdi : L.idleW s ≠ dst)
    (hdrv : L.mem s (runVcpuA dst) = 0#u64) :
    schedcontext.donate st ar s a sc dst ⦃ s' _ => BlkOKX st T Cs Ω H Sg Rp Scs Nt Z Ac X s' ∧
      (∀ y ∈ T, L.mem s' (stA y) = L.mem s (stA y)) ∧ (∀ y ∈ T, L.mem s' (replyA y) = L.mem s (replyA y)) ∧
      L.mem s' (scA dst) = sc ⦄ := by
  have hT := h.tcbs
  have hfa := hT fr hfr
  obtain ⟨hscS, htcb, hcore⟩ := hX.2.2.bound fr hfr (by rw [hscf]; exact hsc0)
  rw [hscf] at hscS htcb hcore
  have hdisj0 : sc ≠ L.cscW s → ∀ b, InSC sc (Z sc) b → Outside b (L.cscW s) (Z (L.cscW s)) := by
    have := hS.disj fr hfr (by rw [hscf]; exact hsc0); rw [hscf] at this; exact this
  have hnb0 : ∀ y ∈ T, y ≠ fr → L.mem s (scA y) ≠ sc := fun y hy hyf e => by
    obtain ⟨-, h2, -⟩ := hX.2.2.bound y hy (by rw [e]; exact hsc0)
    rw [e, htcb] at h2; exact hyf h2.symm
  have hfixΩ := (hX.1.fixW sc hscS)
  unfold schedcontext.donate
  step with obj.Sc.tcb.spec as ⟨i, ei⟩
  have hi : i = fr := ei.trans htcb
  subst hi
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  have hb : b = false := by
    rw [eb]; simp only [decide_eq_false_iff_not]; exact fun e => hfa.ne0 (by rw [e]; rfl)
  -- the first half, up to the state `s6`
  refine WP.spec_bind (Pₘ := fun r : S × A => ∃ Q6 R6, SchedQueuesInvX st T Cs Ω H X r.1 Q6 R6 ∧
      BoundInv st T Ac r.1 ∧ XInv0 st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ TScX st Scs sc r.1 ∧
      SCsOK st T Ω Sg Scs Z Ac r.1 ∧ SgOK st Ω Sg r.1 ∧
      (∀ y ∈ T, L.mem r.1 (stA y) = L.mem s (stA y)) ∧ (∀ y ∈ T, L.mem r.1 (replyA y) = L.mem s (replyA y)) ∧
      L.mem r.1 (scA i) = 0#u64 ∧
      (∀ y ∈ T, y ≠ i → L.mem r.1 (scA y) = L.mem s (scA y)) ∧ L.mem r.1 (inqA dst) = L.mem s (inqA dst) ∧
      (∀ b ∈ Sg, L.mem r.1 b = L.mem s b) ∧ L.cscW r.1 = L.cscW s ∧ L.idleW r.1 = L.idleW s ∧
      (∀ y ∈ T, L.mem r.1 (affA y) = L.mem s (affA y)) ∧
      L.mem r.1 (runVcpuA dst) = L.mem s (runVcpuA dst)) ?_ ?_
  rotate_left
  · rintro ⟨s6, a6⟩ ⟨Q6, R6, h6, hB6, hX6, tx6, hS6, hSg6, st6, rp6, sf6, sy6, iq6, sg6, cs6, ei6, af6, rv6⟩
    try simp only [WP.uncurry'_pair]
    have haf6 : ScAff st T s6 := (ScAffX.keep (d := i) (hX.2.2.aff.x i) (fun t ht _ h0 => (hX.2.2.bound t ht h0).1)
      sy6 (fun c hc => sg6 _ (hX.1.fixW c hc).2) (fun t ht _ => af6 t ht)).full (fun _ h0 => absurd sf6 h0)
    refine WP.spec_mono (donate_tail hA s6 a6 sc dst Q6 R6 h6 hB6 hX6 tx6 haf6 (by rw [sy6 dst hdst hne]; exact hd0)
      hS6 hSg6 hdst
      (by rw [iq6]; exact hdq) (by rw [iq6]; exact hdr) hscS hsc0 (fun y hy => ?_)
      (by rw [sg6 _ hfixΩ.2]; exact hcore) (by rw [cs6]; exact hdisj0) (fun _ => hscA)
      (by rw [ei6]; exact hdi) (rv6.trans hdrv)) fun r hh => ?_
    · by_cases e : y = i
      · subst e; rw [sf6]; exact Ne.symm hsc0
      · rw [sy6 y hy e]; exact hnb0 y hy e
    · obtain ⟨s', a'⟩ := r
      simp only [WP.uncurry'_pair] at hh ⊢
      exact ⟨hh.1, fun y hy => (hh.2.1 y hy).trans (st6 y hy), fun y hy => (hh.2.2.1 y hy).trans (rp6 y hy),
        hh.2.2.2.2.1⟩
  split
  · rename_i hbt; rw [hb] at hbt; exact absurd hbt (by simp)
  refine WP.spec_bind (smp.remote_tcb_stall.all hA s a i h hB hX hS hSg) ?_
  rintro ⟨s2, a2⟩ ⟨h2, hB2, hX2, hS2, hSg2, ea2, ec2, ei2, ecs2, f2, o2⟩
  try simp only [WP.uncurry'_pair]
  have iq2 : L.mem s2 (inqA i) = L.mem s (inqA i) := by rw [inqA_eq]; exact f2 i hfr _ (by simp) (by simp)
  have hna2 : L.actionW s2 ≠ i := by rw [ea2]; exact hfout.2.2
  refine WP.spec_bind (sched.dequeue.noop s2 i (by rw [iq2]; exact hfout.1)) fun s3 e3 => ?_
  subst e3
  refine WP.spec_bind (sched.release_remove.noop s3 i (by rw [iq2]; exact hfout.2.1)) fun s4 e4 => ?_
  subst e4
  step with obj.Tcb.set_sc.wr as ⟨s5, e5⟩
  have key := clear_sc_state h2 hB2 hX2 hS2 hSg2 hfr
    ⟨by rw [iq2]; exact hfout.1, by rw [iq2]; exact hfout.2.1⟩ (by rw [ei2]; exact hfi)
  rw [← e5] at key
  obtain ⟨k1, kB, kB3, k3, ktx, k4, k5, ka, kc, ki, kcs, kf, kΩ, ks0⟩ := key
  have ktx' : TScX st Scs sc s5 := by
    revert ktx
    rw [scA_eq, f2 i hfr _ (by simp) (by simp), ← scA_eq, hscf]; exact id
  have sg5 : ∀ b ∈ Sg, L.mem s5 b = L.mem s b := fun b hb => (kΩ b (hSg.sub b hb)).trans (o2 b (hSg.sub b hb))
  have sy5 : ∀ y ∈ T, y ≠ i → L.mem s5 (scA y) = L.mem s (scA y) := fun y hy hyi =>
    (kf y hy 3464#u64 (by simp) (by simp) (fun e => absurd e hyi)).trans (f2 y hy _ (by simp) (by simp))
  have st5 : ∀ y ∈ T, L.mem s5 (stA y) = L.mem s (stA y) := fun y hy => by
    rw [stA_eq]; exact (kf y hy _ (by simp) (by simp) (fun _ => by simp)).trans (f2 y hy _ (by simp) (by simp))
  have rp5 : ∀ y ∈ T, L.mem s5 (replyA y) = L.mem s (replyA y) := fun y hy =>
    (kf y hy _ (by simp) (by simp) (fun _ => by simp)).trans (f2 y hy _ (by simp) (by simp))
  have iq5 : L.mem s5 (inqA dst) = L.mem s (inqA dst) := by
    rw [inqA_eq]; exact (kf dst hdst _ (by simp) (by simp) (fun _ => by simp)).trans (f2 dst hdst _ (by simp) (by simp))
  have af5 : ∀ y ∈ T, L.mem s5 (affA y) = L.mem s (affA y) := fun y hy =>
    (kf y hy _ (by simp) (by simp) (fun _ => by simp)).trans (f2 y hy _ (by simp) (by simp))
  have rv5 : L.mem s5 (runVcpuA dst) = L.mem s (runVcpuA dst) :=
    (kf dst hdst 3672#u64 (by simp) (by simp) (fun _ => by simp)).trans (f2 dst hdst _ (by simp) (by simp))
  have cs5 : L.cscW s5 = L.cscW s := kcs.trans ecs2
  have ea5 : L.actionW s5 = L.actionW s := ka.trans ea2
  step with sched.cur_thread.spec as ⟨t1, et1⟩
  step with tcb_eq.blk as ⟨b1, eb1⟩
  split
  · by_cases ha0 : L.actionW s5 = 0#u64
    · refine WP.spec_bind (sched.reschedule_required.resume s5 ha0) fun s6 e6 => ?_
      subst e6
      have f := fr_node (Sg := Sg) (hi8 := fun _ => by simp [layout.node.SCHED_ACTION, layout.node.REPROGRAM, layout.node.CUR_THREAD]) (v := 1#u64) k1 k5 k1.cur (by rw [act_val]; omega) (by rw [act_val])
        (hto := ⟨by rw [act_val]; omega, by rw [act_val]; omega⟩)
        (fun _ => by rw [act_val]; omega)
      obtain ⟨j1, -⟩ := inv_set_action k1 (Or.inr (Or.inl rfl)) (fun h1T => absurd h1T (notT_small k1.tcbs (by simp)))
      have fw : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
          L.mem (L.wr s5 (L.nodeAt s5 (L.cpu s5) layout.node.SCHED_ACTION) 1#u64) (core.num.U64.wrapping_add y K) =
            L.mem s5 (core.num.U64.wrapping_add y K) := fun y hy K hK hK8 =>
        field_wr_node k1 k1.cur (by rw [act_val]; omega) (by rw [act_val]) hy hK hK8
      refine (WP.spec_ok _).2 ⟨Q, R, j1, kB3, k3.fr f, ktx'.keep k3.2.2.yt.1
          (fun c hc _ => f.sig _ (k3.1.fixW c hc).1) f.sc, k4.fr f, k5.fr f, fun y hy => ?_,
        fun y hy => (fw y hy _ (by simp) (by simp)).trans (rp5 y hy), ?_, fun y hy hyi => ?_, ?_,
        fun b hb => (f.sig b hb).trans (sg5 b hb), f.csc.trans cs5, f.idle.trans (ki.trans ei2),
        fun y hy => (fw y hy _ (by simp) (by simp)).trans (af5 y hy),
        (fw dst hdst 3672#u64 (by simp) (by simp)).trans rv5⟩
      · rw [stA_eq, fw y hy _ (by simp) (by simp), ← stA_eq]; exact st5 y hy
      · rw [scA_eq, fw i hfr _ (by simp) (by simp), ← scA_eq]; exact ks0
      · rw [scA_eq, fw y hy _ (by simp) (by simp), ← scA_eq]; exact sy5 y hy hyi
      · rw [inqA_eq, fw dst hdst _ (by simp) (by simp), ← inqA_eq]; exact iq5
    · have kB2 := kB hna2 (fun _ => ha0)
      have hda5 : L.actionW s5 ≠ dst := by rw [ea5]; exact hda
      refine WP.spec_bind (WP.spec_and (sched.reschedule_required.schX s5 Q R k1 kB2 k5)
        (sched.reschedule_required.fldX (K := 3672#u64) s5 Q R k1 kB2 k5 (by simp) (by simp) (by simp) (by simp)))
        fun s6 hh2 => ?_
      obtain ⟨hh, hrr⟩ := hh2
      obtain ⟨⟨Q6, R6, h6⟩, hB6, fr6, -, -, kp6, -, iq6⟩ := hh
      refine (WP.spec_ok _).2 ⟨Q6, R6, h6, hB6, k3.fr fr6, ktx'.keep k3.2.2.yt.1
          (fun c hc _ => fr6.sig _ (k3.1.fixW c hc).1) fr6.sc, k4.fr fr6, k5.fr fr6,
        fun y hy => (kp6.1 y hy).trans (st5 y hy), fun y hy => (fr6.rep y hy).trans (rp5 y hy), (fr6.sc i hfr).trans ks0,
        fun y hy hyi => (fr6.sc y hy).trans (sy5 y hy hyi), (iq6 dst hdst hda5).trans iq5,
        fun b hb => (fr6.sig b hb).trans (sg5 b hb), fr6.csc.trans cs5, fr6.idle.trans (ki.trans ei2),
        fun y hy => (fr6.aff y hy).trans (af5 y hy), (hrr dst hdst).trans rv5⟩
  · rename_i hb1
    have hne' : i ≠ t1 := fun e => hb1 (by rw [eb1, decide_eq_true_eq]; exact e)
    have kB2 := kB hna2 (fun e => absurd (by rw [et1]; exact e.symm) hne')
    step with sched.action.spec as ⟨i1, ei1⟩
    split
    · rename_i hii; exfalso; exact hfout.2.2 (by rw [← ea5, ← ei1, hii])
    · try simp only [Aeneas.Std.bind_ok]
      refine (WP.spec_ok _).2 ?_
      exact ⟨Q, R, k1, kB2, k3, ktx', k4, k5, st5, rp5, ks0, sy5, iq5, sg5, cs5, ki.trans (ei2), af5, rv5⟩

/-! ## Reply-stack words -/

theorem zero_bit (j : Nat) : (0#u64).bv.getLsbD j = false := by
  have : (0#u64).bv = 0#64 := rfl
  rw [this]; simp

theorem nx_mask (v b : U64) (hb : b = 0#u64 ∨ b = 1#u64) : ((v &&& ~~~1#u64) ||| b) &&& ~~~1#u64 = v &&& ~~~1#u64 := by
  apply eq_of_bv; apply BitVec.eq_of_getLsbD_eq; intro i hi
  rcases hb with rfl | rfl <;>
  simp only [UScalar.bv_and, UScalar.bv_or, UScalar.bv_not, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not, one_bit, zero_bit] <;>
  by_cases h : i = 0 <;> simp [h, hi]

theorem nx_head1 (v : U64) : headBit ((v &&& ~~~1#u64) ||| 1#u64) = true := by
  have : ((v &&& ~~~1#u64) ||| 1#u64) &&& 1#u64 = 1#u64 := by
    apply eq_of_bv; apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [UScalar.bv_and, UScalar.bv_or, UScalar.bv_not, BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_not, one_bit]
    by_cases h : i = 0 <;> simp [h, hi]
  unfold headBit; rw [this]; decide

theorem nx_head0 (v : U64) : headBit ((v &&& ~~~1#u64) ||| 0#u64) = false := by
  have : ((v &&& ~~~1#u64) ||| 0#u64) &&& 1#u64 = 0#u64 := by
    apply eq_of_bv; apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [UScalar.bv_and, UScalar.bv_or, UScalar.bv_not, BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_not, one_bit, zero_bit]
    by_cases h : i = 0 <;> simp [h, hi]
  unfold headBit; rw [this]; decide

theorem mask1_of_even {x : U64} (h : x.val % 2 = 0) : x &&& ~~~1#u64 = x := by
  apply eq_of_bv; apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [UScalar.bv_and, UScalar.bv_not, BitVec.getLsbD_and, BitVec.getLsbD_not, one_bit]
  by_cases h2 : i = 0
  · subst h2
    have hb : x.bv.getLsbD 0 = x.val.testBit 0 := rfl
    rw [hb, Nat.testBit_zero]; simp [h]
  · simp [h2, hi]

/-- `XInv` after a write to a word of `Ω` that is no reply's or SC's `TCB`
word and no SC's `CORE` word: the reply links and SC `REPLY` words it may
hit get values of the right kind. -/
theorem XInvRM.wr_linkT {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {a w : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hX : XInvRM st T Cs Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (haΩ : a ∈ Ω) (ht : ∀ r ∈ Rp, a.val ≠ (rTcbA r).val)
    (hc : ∀ c ∈ Scs, a.val ≠ (scTcbA c).val ∧ a.val ≠ (scCoreA c).val ∧ a.val ≠ (maxA c).val)
    (hn : ∀ r ∈ Rp, a.val = (rNextA r).val → w &&& ~~~1#u64 ≠ 0#u64 →
      (headBit w = true → w &&& ~~~1#u64 ∈ Scs) ∧ (headBit w = false → w &&& ~~~1#u64 ∈ Rp))
    (hp : ∀ r ∈ Rp, a.val = (rPrevA r).val → w &&& ~~~1#u64 ≠ 0#u64 → w &&& ~~~1#u64 ∈ Rp)
    (hs : ∀ c ∈ Scs, a.val = (scReplyA c).val → w ≠ 0#u64 → w ∈ Rp ∧ L.mem s (scTcbA c) ≠ L.idleW s)
    (hnt : ∀ n ∈ Nt, a.val = (ntfnScA n).val → w ≠ 0#u64 →
      w ∈ Scs ∧ L.mem s (scNtfnA w) = n)
    (hnB : ∀ c ∈ Scs, a.val = (scNtfnA c).val → ∀ n ∈ Nt, L.mem s (ntfnScA n) = c → w = n)
    (hnb : ∀ n ∈ Nt, a.val = (ntfnBtA n).val → Tz T w)
    (hsnT : ∀ c ∈ Scs, a.val = (scNtfnA c).val → w ≠ 0#u64 → w ∈ Nt)
    (hsyT : ∀ c ∈ Scs, a.val = (scYieldFromA c).val → w ≠ 0#u64 → w ∈ T) :
    XInvRM st T Cs Ω Sg Rp Scs Nt Z (L.wr s a w) := by
  obtain ⟨hO, hR, hE⟩ := hX
  have ho := h.omega a haΩ
  have hN := h.nodes _ h.cur
  obtain ⟨hrΩ, hcΩ⟩ := objs_omega hO hsub
  have al : ∀ b ∈ Ω, Aligned b := fun b hb => (h.omega b hb).1
  have k : ∀ b, Aligned b → a.val ≠ b.val → L.mem (L.wr s a w) b = L.mem s b := fun b hb hne =>
    L.mem_wr_ne ho.1 hb hne
  have fk : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem (L.wr s a w) (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K hK hK8 => k _ (field_aligned (h.tcbs y hy) hK hK8) (fun e => out_ne_field ho hy (h.tcbs y hy) hK e.symm)
  have st' : ∀ y ∈ T, L.mem (L.wr s a w) (stA y) = L.mem s (stA y) := fun y hy => by
    rw [stA_eq]; exact fk y hy _ (by simp) (by simp)
  have rp' : ∀ y ∈ T, L.mem (L.wr s a w) (replyA y) = L.mem s (replyA y) := fun y hy => fk y hy _ (by simp) (by simp)
  have sc' : ∀ y ∈ T, L.mem (L.wr s a w) (scA y) = L.mem s (scA y) := fun y hy => by
    rw [scA_eq]; exact fk y hy _ (by simp) (by simp)
  have rt' : ∀ r ∈ Rp, L.mem (L.wr s a w) (rTcbA r) = L.mem s (rTcbA r) := fun r hr =>
    k _ (al _ (hrΩ r hr).1) (ht r hr)
  have ecs : L.cscW (L.wr s a w) = L.cscW s := by
    unfold LawfulStore.cscW; rw [nodeA_wr]
    exact k _ (nodeAt_aligned hN (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))
      (out_ne_node ho h.cur hN (by simp [layout.node.CUR_SC])).symm
  have ei : L.idleW (L.wr s a w) = L.idleW s := by
    unfold LawfulStore.idleW; rw [LawfulStore.cpu_wr, nodeAt_wr]
    exact k _ (nodeAt_aligned hN (by rw [idle8]; omega) (by rw [idle8]))
      (out_ne_node ho h.cur hN (by rw [idle8]; omega)).symm
  have hid : ∀ c ∈ Scs, L.mem (L.wr s a w) (scTcbA c) = L.idleW (L.wr s a w) →
      L.mem (L.wr s a w) (scReplyA c) = 0#u64 := fun c hcs e => by
    rw [ei, k _ (al _ (hcΩ _ hcs).1) (hc _ hcs).1] at e
    rw [L.mem_wr_val ho.1 (al _ (hsub _ (hO.repW c hcs)))]
    split
    · rename_i ea; by_contra h0; exact (hs c hcs ea h0).2 e
    · exact hR.idle c hcs e
  refine ⟨hO.ksb, ⟨fun u hu hs => ?_, fun u hu hs hn' => ?_, fun r hr => ?_, fun r hr => ?_, fun r hr hn' => ?_,
      fun c hcs => ?_, hid⟩, ⟨⟨fun u hu hb => ?_, by rw [ecs]; exact hE.cur, fun c' hc' => by rw [k _ (al _ (hcΩ _ hc').2.1) (hc _ hc').2.1]; exact hE.core c' hc',
      fun u hu => by
        rw [show L.mem (L.wr s a w) (boundA u) = L.mem s (boundA u) from fk u hu _ (by simp) (by simp)]
        exact hE.bnd u hu,
      fun n hn => by
        rw [L.mem_wr_val ho.1 (hO.ntAl n hn)]
        split
        · rename_i ea
          intro h0; obtain ⟨h1, h2⟩ := hnt n hn ea h0
          refine ⟨h1, ?_⟩
          obtain ⟨hPc, hzc⟩ := hO.sc w h1
          rw [k _ (al _ (hsub _ (hO.snW w h1))) (by
            rw [ea, ntfnScA_val (hO.ntP n hn), scNtfnA_val hPc hzc]
            have := hO.ntOSc n hn w h1; have := (sc_facts hO h1).1; omega)]
          exact h2
        · intro h0; obtain ⟨h1, h2⟩ := hE.nsc n hn h0
          refine ⟨h1, ?_⟩
          rw [L.mem_wr_val ho.1 (al _ (hsub _ (hO.snW _ h1)))]
          split
          · exact hnB _ h1 ‹_› n hn rfl
          · exact h2,
      hE.tm.wr_out h.tcbs h.nodes ho, hE.ntb.wr_tz hO ho.1 hnb, hE.rb.wr_out h.tcbs h.nodes ho, fun c hc => by
        rw [L.mem_wr_val ho.1 (al _ (hsub _ (hO.snW c hc)))]
        split
        · exact hsnT c hc ‹_›
        · exact hE.scn c hc,
      ⟨fun c' hc' => by rw [k _ (al _ (hcΩ _ hc').1) (hc _ hc').1]; exact hE.yt.1 c' hc',
       fun u hu => by
        rw [show yieldA u = core.num.U64.wrapping_add u 3472#u64 from rfl, fk u hu _ (by simp) (by simp)]
        exact hE.yt.2.1 u hu,
       fun c hc => by
        rw [L.mem_wr_val ho.1 (al _ (hsub _ (hO.syW c hc)))]
        split
        · exact hsyT c hc ‹_›
        · exact hE.yt.2.2 c hc⟩⟩,
      hE.tsc.keep hE.yt.1 (fun c' hc' => k _ (al _ (hcΩ _ hc').1) (hc _ hc').1) sc',
      hE.aff.keep (fun u hu h0 => (hE.bound u hu h0).1) sc' (fun c' hc' => k _ (al _ (hcΩ _ hc').2.1) (hc _ hc').2.1)
        (fun u hu => fk u hu _ (by simp) (by simp))⟩⟩
  · rw [st' u hu] at hs
    obtain ⟨h1, h2⟩ := hR.reply u hu hs
    rw [rp' u hu, rt' _ h1]; exact ⟨h1, h2⟩
  · rw [st' u hu] at hs; rw [rp' u hu] at hn' ⊢
    obtain ⟨h1, h2⟩ := hR.recv u hu hs hn'
    rw [rt' _ h1]; exact ⟨h1, h2⟩
  · rw [L.mem_wr_val ho.1 (al _ (hrΩ r hr).2.2)]
    split
    · exact hn r hr ‹_›
    · exact hR.next r hr
  · rw [L.mem_wr_val ho.1 (al _ (hrΩ r hr).2.1)]
    split
    · exact hp r hr ‹_›
    · exact hR.prev r hr
  · rw [rt' r hr] at hn' ⊢
    obtain ⟨b0, b1, b2, b3⟩ := hR.back r hr hn'
    rw [rp' _ b1, st' _ b1]; exact ⟨b0, b1, b2, b3⟩
  · rw [L.mem_wr_val ho.1 (al _ (hsub _ (hO.repW c hcs)))]
    split
    · exact fun h0 => (hs c hcs ‹_› h0).1
    · exact hR.screp c hcs
  · rw [sc' u hu] at hb ⊢
    obtain ⟨h1, h2, h3⟩ := hE.bound u hu hb
    rw [k _ (al _ (hcΩ _ h1).1) (hc _ h1).1, k _ (al _ (hcΩ _ h1).2.1) (hc _ h1).2.1]
    exact ⟨h1, h2, h3⟩

/-- `XInvRM.wr_linkT` with the symmetry after the write. -/
theorem XInvR.wr_linkT {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {a w : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hX : XInvR st T Cs Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (haΩ : a ∈ Ω) (ht : ∀ r ∈ Rp, a.val ≠ (rTcbA r).val)
    (hc : ∀ c ∈ Scs, a.val ≠ (scTcbA c).val ∧ a.val ≠ (scCoreA c).val ∧ a.val ≠ (maxA c).val)
    (hn : ∀ r ∈ Rp, a.val = (rNextA r).val → w &&& ~~~1#u64 ≠ 0#u64 →
      (headBit w = true → w &&& ~~~1#u64 ∈ Scs) ∧ (headBit w = false → w &&& ~~~1#u64 ∈ Rp))
    (hp : ∀ r ∈ Rp, a.val = (rPrevA r).val → w &&& ~~~1#u64 ≠ 0#u64 → w &&& ~~~1#u64 ∈ Rp)
    (hs : ∀ c ∈ Scs, a.val = (scReplyA c).val → w ≠ 0#u64 → w ∈ Rp ∧ L.mem s (scTcbA c) ≠ L.idleW s)
    (hnt : ∀ n ∈ Nt, a.val = (ntfnScA n).val → w ≠ 0#u64 →
      w ∈ Scs ∧ L.mem s (scNtfnA w) = n)
    (hnB : ∀ c ∈ Scs, a.val = (scNtfnA c).val → ∀ n ∈ Nt, L.mem s (ntfnScA n) = c → w = n)
    (hnb : ∀ n ∈ Nt, a.val = (ntfnBtA n).val → Tz T w)
    (hsnT : ∀ c ∈ Scs, a.val = (scNtfnA c).val → w ≠ 0#u64 → w ∈ Nt)
    (hsyT : ∀ c ∈ Scs, a.val = (scYieldFromA c).val → w ≠ 0#u64 → w ∈ T)
    (hbs : BndS st T Scs Nt (L.wr s a w)) :
    XInvR st T Cs Ω Sg Rp Scs Nt Z (L.wr s a w) :=
  (XInvRM.wr_linkT h hX.m hsub haΩ ht hc hn hp hs hnt hnB hnb hsnT hsyT).x hbs

theorem XInvM.wr_linkT {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {a w : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hX : XInvM st T Cs Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (haΩ : a ∈ Ω) (ht : ∀ r ∈ Rp, a.val ≠ (rTcbA r).val)
    (hc : ∀ c ∈ Scs, a.val ≠ (scTcbA c).val ∧ a.val ≠ (scCoreA c).val ∧ a.val ≠ (maxA c).val)
    (hn : ∀ r ∈ Rp, a.val = (rNextA r).val → w &&& ~~~1#u64 ≠ 0#u64 →
      (headBit w = true → w &&& ~~~1#u64 ∈ Scs) ∧ (headBit w = false → w &&& ~~~1#u64 ∈ Rp))
    (hp : ∀ r ∈ Rp, a.val = (rPrevA r).val → w &&& ~~~1#u64 ≠ 0#u64 → w &&& ~~~1#u64 ∈ Rp)
    (hs : ∀ c ∈ Scs, a.val = (scReplyA c).val → w ≠ 0#u64 → w ∈ Rp ∧ L.mem s (scTcbA c) ≠ L.idleW s)
    (hnt : ∀ n ∈ Nt, a.val = (ntfnScA n).val → w ≠ 0#u64 →
      w ∈ Scs ∧ L.mem s (scNtfnA w) = n)
    (hnB : ∀ c ∈ Scs, a.val = (scNtfnA c).val → ∀ n ∈ Nt, L.mem s (ntfnScA n) = c → w = n)
    (hnb : ∀ n ∈ Nt, a.val = (ntfnBtA n).val → Tz T w)
    (hsnT : ∀ c ∈ Scs, a.val = (scNtfnA c).val → w ≠ 0#u64 → w ∈ Nt)
    (hsyT : ∀ c ∈ Scs, a.val = (scYieldFromA c).val → w ≠ 0#u64 → w ∈ T)
    (hnh : ∀ r ∈ Rp, a.val = (rNextA r).val → headBit w = true → w &&& ~~~1#u64 ≠ 0#u64 →
      L.mem s (scReplyA (w &&& ~~~1#u64)) = r)
    (hsh : ∀ c ∈ Scs, a.val = (scReplyA c).val → ∀ r ∈ Rp, headBit (L.mem s (rNextA r)) = true →
      L.mem s (rNextA r) &&& ~~~1#u64 ≠ 0#u64 → L.mem s (rNextA r) &&& ~~~1#u64 = c → w = r) :
    XInvM st T Cs Ω Sg Rp Scs Nt Z (L.wr s a w) := by
  refine (XInvRM.wr_linkT h hX.xr hsub haΩ ht hc hn hp hs hnt hnB hnb hsnT hsyT).x' ?_
  obtain ⟨hO, hR, hE⟩ := hX
  have ho := h.omega a haΩ
  obtain ⟨hrΩ, hcΩ⟩ := objs_omega hO hsub
  have al : ∀ b ∈ Ω, Aligned b := fun b hb => (h.omega b hb).1
  have k : ∀ b, Aligned b → a.val ≠ b.val → L.mem (L.wr s a w) b = L.mem s b := fun b hb hne =>
    L.mem_wr_ne ho.1 hb hne
  intro r hr hb h0
  have aN := al _ (hrΩ r hr).2.2
  by_cases ea : a.val = (rNextA r).val
  · have ew : L.mem (L.wr s a w) (rNextA r) = w := by rw [L.mem_wr_val ho.1 aN, if_pos ea]
    rw [ew] at hb h0 ⊢
    have hcS := ((hn r hr ea h0).1 hb)
    rw [k _ (al _ (hsub _ (hO.repW _ hcS))) (by
      rw [ea]; exact rword_ne_screp hO hr (by rw [(rp_facts hO hr).2.2.2]; omega) _ hcS)]
    exact hnh r hr ea hb h0
  · have ek : L.mem (L.wr s a w) (rNextA r) = L.mem s (rNextA r) := k _ aN ea
    rw [ek] at hb h0 ⊢
    have hcS := (hR.next r hr h0).1 hb
    rw [L.mem_wr_val ho.1 (al _ (hsub _ (hO.repW _ hcS)))]
    split
    · exact hsh _ hcS ‹_› r hr hb h0 rfl
    · exact hR.head r hr hb h0

/-- `XInvM.wr_linkT` with the symmetry after the write. -/
theorem XInv.wr_linkT {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {a w : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (haΩ : a ∈ Ω) (ht : ∀ r ∈ Rp, a.val ≠ (rTcbA r).val)
    (hc : ∀ c ∈ Scs, a.val ≠ (scTcbA c).val ∧ a.val ≠ (scCoreA c).val ∧ a.val ≠ (maxA c).val)
    (hn : ∀ r ∈ Rp, a.val = (rNextA r).val → w &&& ~~~1#u64 ≠ 0#u64 →
      (headBit w = true → w &&& ~~~1#u64 ∈ Scs) ∧ (headBit w = false → w &&& ~~~1#u64 ∈ Rp))
    (hp : ∀ r ∈ Rp, a.val = (rPrevA r).val → w &&& ~~~1#u64 ≠ 0#u64 → w &&& ~~~1#u64 ∈ Rp)
    (hs : ∀ c ∈ Scs, a.val = (scReplyA c).val → w ≠ 0#u64 → w ∈ Rp ∧ L.mem s (scTcbA c) ≠ L.idleW s)
    (hnt : ∀ n ∈ Nt, a.val = (ntfnScA n).val → w ≠ 0#u64 →
      w ∈ Scs ∧ L.mem s (scNtfnA w) = n)
    (hnB : ∀ c ∈ Scs, a.val = (scNtfnA c).val → ∀ n ∈ Nt, L.mem s (ntfnScA n) = c → w = n)
    (hnb : ∀ n ∈ Nt, a.val = (ntfnBtA n).val → Tz T w)
    (hsnT : ∀ c ∈ Scs, a.val = (scNtfnA c).val → w ≠ 0#u64 → w ∈ Nt)
    (hsyT : ∀ c ∈ Scs, a.val = (scYieldFromA c).val → w ≠ 0#u64 → w ∈ T)
    (hnh : ∀ r ∈ Rp, a.val = (rNextA r).val → headBit w = true → w &&& ~~~1#u64 ≠ 0#u64 →
      L.mem s (scReplyA (w &&& ~~~1#u64)) = r)
    (hsh : ∀ c ∈ Scs, a.val = (scReplyA c).val → ∀ r ∈ Rp, headBit (L.mem s (rNextA r)) = true →
      L.mem s (rNextA r) &&& ~~~1#u64 ≠ 0#u64 → L.mem s (rNextA r) &&& ~~~1#u64 = c → w = r)
    (hbs : BndS st T Scs Nt (L.wr s a w)) :
    XInv st T Cs Ω Sg Rp Scs Nt Z (L.wr s a w) :=
  (XInvM.wr_linkT h hX.m hsub haΩ ht hc hn hp hs hnt hnB hnb hsnT hsyT hnh hsh).x hbs

theorem XInv.wr_link {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {a w : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (haΩ : a ∈ Ω) (ht : ∀ r ∈ Rp, a.val ≠ (rTcbA r).val)
    (hc : ∀ c ∈ Scs, a.val ≠ (scTcbA c).val ∧ a.val ≠ (scCoreA c).val ∧ a.val ≠ (maxA c).val)
    (hn : ∀ r ∈ Rp, a.val = (rNextA r).val → w &&& ~~~1#u64 ≠ 0#u64 →
      (headBit w = true → w &&& ~~~1#u64 ∈ Scs) ∧ (headBit w = false → w &&& ~~~1#u64 ∈ Rp))
    (hp : ∀ r ∈ Rp, a.val = (rPrevA r).val → w &&& ~~~1#u64 ≠ 0#u64 → w &&& ~~~1#u64 ∈ Rp)
    (hs : ∀ c ∈ Scs, a.val = (scReplyA c).val → w ≠ 0#u64 → w ∈ Rp ∧ L.mem s (scTcbA c) ≠ L.idleW s)
    (hnt : ∀ n ∈ Nt, a.val ≠ (ntfnScA n).val) (hnb : ∀ n ∈ Nt, a.val ≠ (ntfnBtA n).val)
    (hsn : ∀ c ∈ Scs, a.val ≠ (scNtfnA c).val) (hsy : ∀ c ∈ Scs, a.val ≠ (scYieldFromA c).val)
    (hnh : ∀ r ∈ Rp, a.val = (rNextA r).val → headBit w = true → w &&& ~~~1#u64 ≠ 0#u64 →
      L.mem s (scReplyA (w &&& ~~~1#u64)) = r)
    (hsh : ∀ c ∈ Scs, a.val = (scReplyA c).val → ∀ r ∈ Rp, headBit (L.mem s (rNextA r)) = true →
      L.mem s (rNextA r) &&& ~~~1#u64 ≠ 0#u64 → L.mem s (rNextA r) &&& ~~~1#u64 = c → w = r) :
    XInv st T Cs Ω Sg Rp Scs Nt Z (L.wr s a w) :=
  hX.wr_linkT h hsub haΩ ht hc hn hp hs (fun n hn e => absurd e (hnt n hn)) (fun c hc e => absurd e (hsn c hc))
    (fun n hn e => absurd e (hnb n hn))
    (fun c hc e => absurd e (hsn c hc)) (fun c hc e => absurd e (hsy c hc)) hnh hsh
    (BndS.wr_omega hX.2.2.toScExtra0 h hX.1 hsub haΩ (fun n hn => ⟨hnb n hn, hnt n hn⟩) hsn)

/-- The invariants after a write of a word of another object (a reply link,
an SC `REPLY` word, a notification's badge or `BOUND_TCB`), without `BndS`. -/
theorem link_allTM {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {a w : U64}
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInvM st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s)
    (haΩ : a ∈ Ω) (ht : ∀ r ∈ Rp, a.val ≠ (rTcbA r).val)
    (hc : ∀ c ∈ Scs, a.val ≠ (scTcbA c).val ∧ a.val ≠ (scCoreA c).val ∧ a.val ≠ (maxA c).val ∧
      a.val ≠ (headA c).val ∧ a.val ≠ (tailA c).val)
    (hn : ∀ r ∈ Rp, a.val = (rNextA r).val → w &&& ~~~1#u64 ≠ 0#u64 →
      (headBit w = true → w &&& ~~~1#u64 ∈ Scs) ∧ (headBit w = false → w &&& ~~~1#u64 ∈ Rp))
    (hp : ∀ r ∈ Rp, a.val = (rPrevA r).val → w &&& ~~~1#u64 ≠ 0#u64 → w &&& ~~~1#u64 ∈ Rp)
    (hs : ∀ c ∈ Scs, a.val = (scReplyA c).val → w ≠ 0#u64 → w ∈ Rp ∧ c ∈ Ac ∧ L.mem s (scTcbA c) ≠ L.idleW s)
    (hnt : ∀ n ∈ Nt, a.val = (ntfnScA n).val → w ≠ 0#u64 →
      w ∈ Scs ∧ L.mem s (scNtfnA w) = n)
    (hnB : ∀ c ∈ Scs, a.val = (scNtfnA c).val → ∀ n ∈ Nt, L.mem s (ntfnScA n) = c → w = n)
    (hnb : ∀ n ∈ Nt, a.val = (ntfnBtA n).val → Tz T w)
    (hsnT : ∀ c ∈ Scs, a.val = (scNtfnA c).val → w ≠ 0#u64 → w ∈ Nt)
    (hsyT : ∀ c ∈ Scs, a.val = (scYieldFromA c).val → w ≠ 0#u64 → w ∈ T)
    (hsp : ∀ c ∈ Scs, a.val ≠ (sporA c).val)
    (hnh : ∀ r ∈ Rp, a.val = (rNextA r).val → headBit w = true → w &&& ~~~1#u64 ≠ 0#u64 →
      L.mem s (scReplyA (w &&& ~~~1#u64)) = r)
    (hsh : ∀ c ∈ Scs, a.val = (scReplyA c).val → ∀ r ∈ Rp, headBit (L.mem s (rNextA r)) = true →
      L.mem s (rNextA r) &&& ~~~1#u64 ≠ 0#u64 → L.mem s (rNextA r) &&& ~~~1#u64 = c → w = r) :
    SchedQueuesInv st T Cs Ω H (L.wr s a w) Q R ∧ BoundInv st T Ac (L.wr s a w) ∧
      XInvM st T Cs Ω Sg Rp Scs Nt Z (L.wr s a w) ∧ SCsOK st T Ω Sg Scs Z Ac (L.wr s a w) ∧ SgOK st Ω Sg (L.wr s a w) ∧
      L.actionW (L.wr s a w) = L.actionW s ∧ L.curW (L.wr s a w) = L.curW s ∧ L.idleW (L.wr s a w) = L.idleW s ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        L.mem (L.wr s a w) (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ b ∈ Ω, a.val ≠ b.val → L.mem (L.wr s a w) b = L.mem s b) := by
  have ho := h.omega a haΩ
  have hN := h.nodes _ h.cur
  obtain ⟨h1, ea, f⟩ := omega_wr (v := w) h haΩ
  have nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem (L.wr s a w) (L.nodeAt (L.wr s a w) (L.cpu (L.wr s a w)) o) = L.mem s (L.nodeAt s (L.cpu s) o) :=
    fun o h1 h2 => by
      simp only [LawfulStore.cpu_wr, nodeAt_wr]
      exact L.mem_wr_ne ho.1 (nodeAt_aligned hN h1 h2) (fun e => out_ne_node ho h.cur hN h1 e.symm)
  refine ⟨h1, BoundInv.owr h hB haΩ, XInvM.wr_linkT h hX hSg.sub haΩ ht (fun c hcs => ⟨(hc c hcs).1, (hc c hcs).2.1, (hc c hcs).2.2.1⟩)
      hn hp (fun c hc e h0 => ⟨(hs c hc e h0).1, (hs c hc e h0).2.2⟩) hnt hnB hnb hsnT hsyT hnh hsh,
    SCsOK.wr' h hS hX.1 ho.1 (fun y hy => (out_ne_field (K := 3464#u64) ho hy (h.tcbs y hy) (by simp)).symm)
      (out_ne_node ho h.cur hN (by simp [layout.node.CUR_SC])).symm (fun c hcs => (hc c hcs).2.2) hsp
      (fun c hcs e h0 => (hs c hcs e h0).2.1),
    ⟨hSg.sub, fun b hb => by rw [L.ksb_wr]; exact hSg.ks b hb, fun o h1 h2 => by rw [L.ksb_wr]; exact hSg.ksΩ o h1 h2⟩,
    ea, nd _ (by rw [curth0]; omega) (by rw [curth0]), nd _ (by rw [idle8]; omega) (by rw [idle8]), f,
    fun b hb hne => L.mem_wr_ne ho.1 (h.omega b hb).1 hne⟩

/-- The invariants after a write of a word of another object (a reply link,
an SC `REPLY` word, a notification's badge or `BOUND_TCB`). -/
theorem link_allT {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {a w : U64}
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s)
    (haΩ : a ∈ Ω) (ht : ∀ r ∈ Rp, a.val ≠ (rTcbA r).val)
    (hc : ∀ c ∈ Scs, a.val ≠ (scTcbA c).val ∧ a.val ≠ (scCoreA c).val ∧ a.val ≠ (maxA c).val ∧
      a.val ≠ (headA c).val ∧ a.val ≠ (tailA c).val)
    (hn : ∀ r ∈ Rp, a.val = (rNextA r).val → w &&& ~~~1#u64 ≠ 0#u64 →
      (headBit w = true → w &&& ~~~1#u64 ∈ Scs) ∧ (headBit w = false → w &&& ~~~1#u64 ∈ Rp))
    (hp : ∀ r ∈ Rp, a.val = (rPrevA r).val → w &&& ~~~1#u64 ≠ 0#u64 → w &&& ~~~1#u64 ∈ Rp)
    (hs : ∀ c ∈ Scs, a.val = (scReplyA c).val → w ≠ 0#u64 → w ∈ Rp ∧ c ∈ Ac ∧ L.mem s (scTcbA c) ≠ L.idleW s)
    (hnt : ∀ n ∈ Nt, a.val = (ntfnScA n).val → w ≠ 0#u64 →
      w ∈ Scs ∧ L.mem s (scNtfnA w) = n)
    (hnB : ∀ c ∈ Scs, a.val = (scNtfnA c).val → ∀ n ∈ Nt, L.mem s (ntfnScA n) = c → w = n)
    (hnb : ∀ n ∈ Nt, a.val = (ntfnBtA n).val → Tz T w)
    (hsnT : ∀ c ∈ Scs, a.val = (scNtfnA c).val → w ≠ 0#u64 → w ∈ Nt)
    (hsyT : ∀ c ∈ Scs, a.val = (scYieldFromA c).val → w ≠ 0#u64 → w ∈ T)
    (hsp : ∀ c ∈ Scs, a.val ≠ (sporA c).val)
    (hnh : ∀ r ∈ Rp, a.val = (rNextA r).val → headBit w = true → w &&& ~~~1#u64 ≠ 0#u64 →
      L.mem s (scReplyA (w &&& ~~~1#u64)) = r)
    (hsh : ∀ c ∈ Scs, a.val = (scReplyA c).val → ∀ r ∈ Rp, headBit (L.mem s (rNextA r)) = true →
      L.mem s (rNextA r) &&& ~~~1#u64 ≠ 0#u64 → L.mem s (rNextA r) &&& ~~~1#u64 = c → w = r)
    (hbs : BndS st T Scs Nt (L.wr s a w)) :
    SchedQueuesInv st T Cs Ω H (L.wr s a w) Q R ∧ BoundInv st T Ac (L.wr s a w) ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z (L.wr s a w) ∧ SCsOK st T Ω Sg Scs Z Ac (L.wr s a w) ∧ SgOK st Ω Sg (L.wr s a w) ∧
      L.actionW (L.wr s a w) = L.actionW s ∧ L.curW (L.wr s a w) = L.curW s ∧ L.idleW (L.wr s a w) = L.idleW s ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        L.mem (L.wr s a w) (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ b ∈ Ω, a.val ≠ b.val → L.mem (L.wr s a w) b = L.mem s b) := by
  obtain ⟨h1, hB1, hX1, r⟩ := link_allTM h hB hX.m hS hSg haΩ ht hc hn hp hs hnt hnB hnb hsnT hsyT hsp hnh hsh
  exact ⟨h1, hB1, hX1.x hbs, r⟩

/-- The invariants after a reply-link or SC `REPLY` write. -/
theorem link_all {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {a w : U64}
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s)
    (haΩ : a ∈ Ω) (ht : ∀ r ∈ Rp, a.val ≠ (rTcbA r).val)
    (hc : ∀ c ∈ Scs, a.val ≠ (scTcbA c).val ∧ a.val ≠ (scCoreA c).val ∧ a.val ≠ (maxA c).val ∧
      a.val ≠ (headA c).val ∧ a.val ≠ (tailA c).val)
    (hn : ∀ r ∈ Rp, a.val = (rNextA r).val → w &&& ~~~1#u64 ≠ 0#u64 →
      (headBit w = true → w &&& ~~~1#u64 ∈ Scs) ∧ (headBit w = false → w &&& ~~~1#u64 ∈ Rp))
    (hp : ∀ r ∈ Rp, a.val = (rPrevA r).val → w &&& ~~~1#u64 ≠ 0#u64 → w &&& ~~~1#u64 ∈ Rp)
    (hs : ∀ c ∈ Scs, a.val = (scReplyA c).val → w ≠ 0#u64 → w ∈ Rp ∧ c ∈ Ac ∧ L.mem s (scTcbA c) ≠ L.idleW s)
    (hnt : ∀ n ∈ Nt, a.val ≠ (ntfnScA n).val) (hnb : ∀ n ∈ Nt, a.val ≠ (ntfnBtA n).val)
    (hsn : ∀ c ∈ Scs, a.val ≠ (scNtfnA c).val) (hsy : ∀ c ∈ Scs, a.val ≠ (scYieldFromA c).val)
    (hsp : ∀ c ∈ Scs, a.val ≠ (sporA c).val)
    (hnh : ∀ r ∈ Rp, a.val = (rNextA r).val → headBit w = true → w &&& ~~~1#u64 ≠ 0#u64 →
      L.mem s (scReplyA (w &&& ~~~1#u64)) = r)
    (hsh : ∀ c ∈ Scs, a.val = (scReplyA c).val → ∀ r ∈ Rp, headBit (L.mem s (rNextA r)) = true →
      L.mem s (rNextA r) &&& ~~~1#u64 ≠ 0#u64 → L.mem s (rNextA r) &&& ~~~1#u64 = c → w = r) :
    SchedQueuesInv st T Cs Ω H (L.wr s a w) Q R ∧ BoundInv st T Ac (L.wr s a w) ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z (L.wr s a w) ∧ SCsOK st T Ω Sg Scs Z Ac (L.wr s a w) ∧ SgOK st Ω Sg (L.wr s a w) ∧
      L.actionW (L.wr s a w) = L.actionW s ∧ L.curW (L.wr s a w) = L.curW s ∧ L.idleW (L.wr s a w) = L.idleW s ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        L.mem (L.wr s a w) (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ b ∈ Ω, a.val ≠ b.val → L.mem (L.wr s a w) b = L.mem s b) :=
  link_allT h hB hX hS hSg haΩ ht hc hn hp hs (fun n hn e => absurd e (hnt n hn)) (fun c hc e => absurd e (hsn c hc))
    (fun n hn e => absurd e (hnb n hn)) (fun c hc e => absurd e (hsn c hc)) (fun c hc e => absurd e (hsy c hc)) hsp
    hnh hsh
    (BndS.wr_omega hX.2.2.toScExtra0 h hX.1 hSg.sub haΩ (fun n hn => ⟨hnb n hn, hnt n hn⟩) hsn)

/-! ## `reply_push` -/

theorem reply_val : sched.TS_BLOCKED_ON_REPLY = 5#u64 := by unfold sched.TS_BLOCKED_ON_REPLY; rfl

theorem not_blocked_reply' : ¬ Blocked sched.TS_BLOCKED_ON_REPLY := fun hb => blocked_ne_reply hb rfl

/-- The reply object names the caller, which blocks on it (`set_blocked_on_reply`). -/
theorem sched.set_blocked_on_reply.ipc {X : Set U64} (s : S) (caller r : U64) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hXc : ExcT X caller)
    (hx : caller ∈ X ∨ ¬ Blocked (L.mem s (stA caller)))
    (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s)
    (hcl : caller ∈ T) (hcq : (L.mem s (inqA caller) &&& sched.Q_QUEUED) = 0#u64)
    (hcr : (L.mem s (inqA caller) &&& sched.Q_RELEASE) = 0#u64) (hca : L.actionW s ≠ caller)
    (hci : L.idleW s ≠ caller)
    (hcold : L.mem s (stA caller) ≠ sched.TS_BLOCKED_ON_REPLY ∧ L.mem s (stA caller) ≠ sched.TS_BLOCKED_ON_RECV)
    (hr : r ∈ Rp) (hr00 : r ≠ 0#u64) (hr0 : L.mem s (rTcbA r) = 0#u64)
    (hcA : L.mem s (scA caller) ≠ 0#u64 → L.mem s (scA caller) ∈ Ac) :
    sched.set_blocked_on_reply st (L.wr s (rTcbA r) caller) caller r ⦃ s2 =>
      SchedQueuesInv st T Cs Ω H s2 Q R ∧ BoundInv st T Ac s2 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z s2 ∧
      SCsOK st T Ω Sg Scs Z Ac s2 ∧ SgOK st Ω Sg s2 ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        (y = caller → K.val ≠ 3328 ∧ K.val ≠ 3336 ∧ K.val ≠ 3344 ∧ K.val ≠ 3352 ∧ K.val ≠ 3360) →
        L.mem s2 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ a ∈ Ω, a ≠ rTcbA r → L.mem s2 a = L.mem s a) ∧
      (L.actionW s2 = L.actionW s ∨ L.actionW s2 = 1#u64) ∧ L.curW s2 = L.curW s ∧ L.idleW s2 = L.idleW s ∧
      L.mem s2 (stA caller) = sched.TS_BLOCKED_ON_REPLY ⦄ := by
  have hT := h.tcbs
  have hta := hT caller hcl
  have hN := h.nodes _ h.cur
  have hm : rTcbA r ∈ Ω := hSg.sub _ (hX.1.tcbW hr)
  have hmo := h.omega _ hm
  obtain ⟨h1, a1, f1⟩ := omega_wr (v := caller) h hm
  set s1 := L.wr s (rTcbA r) caller with hs1
  have iq1 : L.mem s1 (inqA caller) = L.mem s (inqA caller) := by rw [inqA_eq]; exact f1 caller hcl _ (by simp) (by simp)
  have st1 : L.mem s1 (stA caller) = L.mem s (stA caller) := by rw [stA_eq]; exact f1 caller hcl _ (by simp) (by simp)
  have hq1 : (∀ c ∈ Cs, ∀ p : U64, p.val < 256 → caller ∈ Q c p → Runnable sched.TS_BLOCKED_ON_REPLY) ∧
      (∀ c ∈ Cs, caller ∈ R c → Runnable sched.TS_BLOCKED_ON_REPLY) ∧
      (L.actionW s1 = caller → Runnable sched.TS_BLOCKED_ON_REPLY) :=
    ⟨fun c hc p hp hm' => absurd hm' (h1.notQ hcl (by rw [iq1]; exact hcq) hc hp),
      fun c hc hm' => absurd hm' (h1.notR hcl (by rw [iq1]; exact hcr) hc),
      fun e => absurd (by rw [← a1]; exact e) hca⟩
  unfold sched.set_blocked_on_reply
  step with obj.Tcb.set_state.spec as ⟨s1a, e1a⟩
  step with obj.Tcb.set_reply_obj.wr as ⟨s1b, e1b⟩
  have h1a : SchedQueuesInvX st T Cs Ω H {y | y ∈ X ∧ y ≠ caller} s1a Q R := by
    rw [e1a]; exact inv_set_state h1 hcl not_blocked_reply' (by rw [st1]; exact hx) hq1
  have h1b : SchedQueuesInvX st T Cs Ω H {y | y ∈ X ∧ y ≠ caller} s1b Q R := by
    rw [e1b]; exact inv_wr_field (K := 3360#u64) h1a hcl (by simp) (by simp) (by simp)
  rw [stA_eq] at e1a
  have w1 : WritesIn st s s1 (BlkFoot st s caller r) :=
    (writesIn_wr hmo.1).mono fun b hb => Or.inr (Or.inr ⟨hr00, hb⟩)
  have w1b : WritesIn st s s1b (BlkFoot st s caller r) := by
    rw [e1b, e1a]
    exact blk_wr_field (K := 3360#u64) hta (blk_wr_field (K := 3328#u64) hta w1 (by simp)) (by simp)
  have v1b : L.mem s1b (stA caller) = sched.TS_BLOCKED_ON_REPLY := by
    rw [e1b, fld_wr_ne' (K := 3360#u64) (a := replyA caller) hta rfl (stA_eq caller) (by simp) (by simp) (by simp)
      (by simp) (by simp), e1a, stA_eq]
    exact L.mem_wr_same (field_aligned hta (by simp) (by simp))
  have rp1b : L.mem s1b (replyA caller) = r := by rw [e1b]; exact L.mem_wr_same (field_aligned hta (by simp) (by simp))
  have rt1b : L.mem s1b (rTcbA r) = caller := by
    rw [e1b, L.mem_wr_ne (a := replyA caller) (field_aligned (K := 3360#u64) hta (by simp) (by simp)) hmo.1
      (fun e => out_ne_field hmo hcl hta (by simp) e), e1a,
      L.mem_wr_ne (field_aligned (K := 3328#u64) hta (by simp) (by simp)) hmo.1
      (fun e => out_ne_field hmo hcl hta (by simp) e)]
    exact L.mem_wr_same hmo.1
  have a1b : L.actionW s1b = L.actionW s := by
    rw [e1b, act_wr_field (K := 3360#u64) (a := replyA caller) (h1a.nodes _ h1a.cur) hcl hta rfl (by simp) (by simp),
      e1a, act_wr_field (h1.nodes _ h1.cur) hcl hta rfl (by simp) (by simp), a1]
  refine WP.spec_mono (sched.schedule_tcb.blk s1b caller h1b (by rw [v1b]; exact not_runnable_reply)) ?_
  rintro s2 ⟨h2, e2, -⟩
  obtain ⟨w2, a2, v2, -, rp2, om2⟩ := blk_sched h1b hcl w1b a1b e2
  rw [v1b] at v2; rw [rp1b] at rp2
  have rt2 : L.mem s2 (rTcbA r) = caller := (om2 _ hm).trans rt1b
  obtain ⟨E, EQ, hEW⟩ := h.eps
  obtain ⟨k1, k2, k3, -⟩ := blkfoot_keep h hEW hcl (fun _ => hm) w2
  have h2' : SchedQueuesInv st T Cs Ω H s2 Q R := h2.congrX fun y => by
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]
    exact hXc y
  obtain ⟨b1, b2, b3⟩ := blk_keep (hidl := fun e => absurd e hci)
    (htm := TmFr.of_blkfoot h hX.1 hSg.sub hcl (fun _ => hr) w2) h hB hX hS hcl w2.1 w2.2.1 (fun y hy K hK hK8 _ _ hy' => k1 y hy K hK hK8 hy')
    (fun a ha hne => k2 a ha hne) (fun o ho => k3 o (by omega) (by omega) (by omega)) a2
    (fun _ => ⟨by rw [rp2]; exact hr, by rw [rp2]; exact rt2⟩) (fun _ => ⟨hr, Or.inl hr0⟩)
    (fun e => absurd (v2.symm.trans e) (by rw [reply_val]; obtain ⟨-, -, r3, -⟩ := ts_vals; rw [r3]; decide))
    hcold (fun _ => ⟨rt2, rp2, Or.inl v2⟩) hcA
  exact ⟨h2', b1, b2, b3, ⟨hSg.sub, fun b hb => by rw [w2.1]; exact hSg.ks b hb,
      fun o h1 h2 => by rw [w2.1]; exact hSg.ksΩ o h1 h2⟩,
    k1, fun a ha hne => k2 a ha (fun _ => hne), a2, k3 _ (by rw [curth0]; omega) (by rw [curth0]) (by rw [curth0]; omega),
    k3 _ (by rw [idle8]; omega) (by rw [idle8]) (by rw [idle8]; omega), v2⟩

/-- seL4 `reply_push` (MCS): the caller blocks on the reply object, which goes
on top of the caller's SC's reply stack when the SC is donated to the callee. a64: the callee runs no VCPU
(`hcrv`, `RUN_VCPU` 0), for the donation's `migrate_tcb`. -/
theorem ipc.reply_push.ipc {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {X : Set U64} (s : S) (a : A)
    (caller callee r : U64) (can_donate : Bool) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hXc : ExcT X caller)
    (hx : caller ∈ X ∨ ¬ Blocked (L.mem s (stA caller)))
    (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s)
    (hcl : caller ∈ T) (hcq : (L.mem s (inqA caller) &&& sched.Q_QUEUED) = 0#u64)
    (hcr : (L.mem s (inqA caller) &&& sched.Q_RELEASE) = 0#u64) (hca : L.actionW s ≠ caller)
    (hci : L.idleW s ≠ caller)
    (hcold : L.mem s (stA caller) ≠ sched.TS_BLOCKED_ON_REPLY ∧ L.mem s (stA caller) ≠ sched.TS_BLOCKED_ON_RECV)
    (hr : r ∈ Rp) (hr00 : r ≠ 0#u64) (hr0 : L.mem s (rTcbA r) = 0#u64)
    (hce : callee ∈ T) (hne : callee ≠ caller) (heq : (L.mem s (inqA callee) &&& sched.Q_QUEUED) = 0#u64)
    (her : (L.mem s (inqA callee) &&& sched.Q_RELEASE) = 0#u64) (hea : L.actionW s ≠ callee)
    (hcei : L.idleW s ≠ callee)
    (hcA : L.mem s (scA caller) ≠ 0#u64 → L.mem s (scA caller) ∈ Ac)
    (hcrv : L.mem s (runVcpuA callee) = 0#u64) :
    ipc.reply_push st ar s a caller callee r can_donate ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      (∀ y ∈ T, y ≠ caller → L.mem s' (stA y) = L.mem s (stA y)) ∧
      (L.mem s' (scA callee) = L.mem s (scA callee) ∨ L.mem s' (scA callee) = L.mem s (scA caller)) ⦄ := by
  have hT := h.tcbs
  have hO := hX.1
  have hsub := hSg.sub
  obtain ⟨hrΩ, hcΩ⟩ := objs_omega hO hsub
  unfold ipc.reply_push
  step with obj.Tcb.sc.spec as ⟨i, ei⟩
  step with obj.Reply.set_tcb.spec as ⟨s1, e1⟩
  subst e1
  refine WP.spec_bind (sched.set_blocked_on_reply.ipc s caller r Q R h hXc hx hB hX hS hSg hcl hcq hcr hca hci
    hcold hr hr00 hr0 hcA) ?_
  rintro s2 ⟨h2, hB2, hX2, hS2, hSg2, f2, o2, a2, c2, id2, v2⟩
  have K5 : ∀ (K : U64), K.val ≠ 3328 → K.val ≠ 3336 → K.val ≠ 3344 → K.val ≠ 3352 → K.val ≠ 3360 →
      ∀ y, y = caller → K.val ≠ 3328 ∧ K.val ≠ 3336 ∧ K.val ≠ 3344 ∧ K.val ≠ 3352 ∧ K.val ≠ 3360 :=
    fun K a b c d e _ _ => ⟨a, b, c, d, e⟩
  have sc2 : ∀ y ∈ T, L.mem s2 (scA y) = L.mem s (scA y) := fun y hy => by
    rw [scA_eq]; exact f2 y hy _ (by simp) (by simp) (K5 _ (by simp) (by simp) (by simp) (by simp) (by simp) y)
  have iq2 : ∀ y ∈ T, L.mem s2 (inqA y) = L.mem s (inqA y) := fun y hy => by
    rw [inqA_eq]; exact f2 y hy _ (by simp) (by simp) (K5 _ (by simp) (by simp) (by simp) (by simp) (by simp) y)
  have st2 : ∀ y ∈ T, y ≠ caller → L.mem s2 (stA y) = L.mem s (stA y) := fun y hy hyc => by
    rw [stA_eq]; exact f2 y hy _ (by simp) (by simp) (fun e => absurd e hyc)
  have rv2 : L.mem s2 (runVcpuA callee) = 0#u64 :=
    (f2 callee hce 3672#u64 (by simp) (by simp) (K5 _ (by simp) (by simp) (by simp) (by simp) (by simp) callee)).trans
      hcrv
  have ok2 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s2 ∧ (∀ y ∈ T, y ≠ caller → L.mem s2 (stA y) = L.mem s (stA y)) ∧
      (L.mem s2 (scA callee) = L.mem s (scA callee) ∨ L.mem s2 (scA callee) = L.mem s (scA caller)) :=
    ⟨⟨⟨Q, R, h2⟩, hB2, hX2, hS2, hSg2⟩, st2, Or.inl (sc2 callee hce)⟩
  step with obj.Sc.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 ok2
  rename_i hb
  have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
  have hci0 : L.mem s (scA caller) ≠ 0#u64 := by rw [← ei]; exact hi0
  obtain ⟨hiS, hitc, hicore⟩ := hX.2.2.bound caller hcl hci0
  have hiA : i ∈ Ac := by rw [ei]; exact hcA hci0
  rw [← ei] at hiS hitc hicore
  step with obj.Tcb.sc.spec as ⟨i1, ei1⟩
  split
  · split
    · rename_i hi1 hcd
      have hd0 : L.mem s2 (scA callee) = 0#u64 := by rw [← ei1, hi1]
      have hiv := sc_facts hO hiS
      have hi8 := (sc_lo (hO.sc i hiS).1 (hO.sc i hiS).2).1
      step with obj.Sc.reply.val as ⟨i2, ei2⟩
      have hi2 : i2 ≠ 0#u64 → i2 ∈ Rp := fun h0 => by rw [ei2] at h0 ⊢; exact hX2.2.1.screp i hiS h0
      -- the four stack writes
      have pre : ∀ (s3 : S), SchedQueuesInv st T Cs Ω H s3 Q R → BoundInv st T Ac s3 → XInv st T Cs Ω Sg Rp Scs Nt Z s3 →
          SCsOK st T Ω Sg Scs Z Ac s3 → SgOK st Ω Sg s3 →
          (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
            L.mem s3 (core.num.U64.wrapping_add y K) = L.mem s2 (core.num.U64.wrapping_add y K)) →
          (L.actionW s3 = L.actionW s2) → L.idleW s3 = L.idleW s2 →
          L.mem s3 (scReplyA i) = i2 → (i2 ≠ 0#u64 → headBit (L.mem s3 (rNextA i2)) = false) →
          (do
            let s4 ← obj.Reply.set_prev st r s3 i2
            let s5 ← obj.Sc.set_reply st i s4 r
            let s6 ← obj.Reply.set_next st r s5 i true
            schedcontext.donate st ar s6 a i callee) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
              (∀ y ∈ T, y ≠ caller → L.mem s' (stA y) = L.mem s (stA y)) ∧
              (L.mem s' (scA callee) = L.mem s (scA callee) ∨ L.mem s' (scA callee) = L.mem s (scA caller)) ⦄ := by
        intro s3 h3 hB3 hX3 hS3 hSg3 f3 a3 i3 hr3 hn3
        obtain ⟨r32, rt0, rp8, rn16⟩ := rp_facts hO hr
        have ri : ∀ c ∈ Scs, r.val + 32 ≤ c.val ∨ c.val + 2 ^ Z c ≤ r.val := hO.rpSc r hr
        have rr : ∀ r' ∈ Rp, r'.val % 32 = 0 := fun r' hr' => (hO.rp r' hr').1
        -- `r.prev := i2`
        step with obj.Reply.set_prev.val as ⟨s4, e4⟩
        obtain ⟨h4, hB4, hX4, hS4, hSg4, a4, -, i4, f4, o4⟩ := link_all (w := i2 &&& ~~~1#u64) h3 hB3 hX3 hS3 hSg3
          ((hrΩ r hr).2.1)
          (fun r' hr' e => by rw [rp8, rTcbA_val (hO.rp r' hr')] at e; have := rr r' hr'; omega)
          (rword_ne_sc hO hr (by rw [rp8]; omega))
          (fun r' hr' e => by rw [rp8, rNextA_val (hO.rp r' hr')] at e; have := rr r' hr'; omega)
          (fun r' hr' _ hne => by
            by_cases h0 : i2 = 0#u64
            · subst h0; exact absurd (by rw [zero_or_masked, zero_or_masked]) hne
            · have hp := hi2 h0
              have hev : i2.val % 2 = 0 := by have := rr i2 hp; omega
              rw [mask1_of_even (x := i2) hev, mask1_of_even (x := i2) hev]
              exact hp)
          (fun c hc e => absurd e (rword_ne_screp hO hr (by rw [rp8]; omega) c hc))
          (fun n hn e => by rw [rp8] at e; have := hO.ntRp n hn r hr; omega)
          (fun n hn e => by rw [rp8, ntfnBtA_val (hO.ntP n hn)] at e; have := hO.ntORp n hn r hr; omega)
          (rword_ne_scn hO hr (by rw [rp8]; omega)) (rword_ne_scy hO hr (by rw [rp8]; omega))
          (rword_ne_spor hO hr (by rw [rp8]; omega))
          (fun r' hr' e => by rw [rp8, rNextA_val (hO.rp r' hr')] at e; have := rr r' hr'; omega)
          (fun c hc e => absurd e (rword_ne_screp hO hr (by rw [rp8]; omega) c hc))
        rw [← e4] at h4 hB4 hX4 hS4 hSg4 a4 i4 f4 o4
        have tci4 : L.mem s4 (scTcbA i) = caller := by
          have e : L.mem s4 (scA caller) = i := by
            rw [scA_eq, f4 caller hcl _ (by simp) (by simp), f3 caller hcl _ (by simp) (by simp), ← scA_eq,
              sc2 caller hcl, ei]
          have := (hX4.2.2.bound caller hcl (by rw [e]; exact hi0)).2.1
          rw [e] at this; exact this
        have id4 : L.idleW s4 = L.idleW s := i4.trans (i3.trans id2)
        have hr4 : L.mem s4 (scReplyA i) = i2 := by
          rw [o4 _ (hsub _ (hO.repW i hiS)) (rword_ne_screp hO hr (by rw [rp8]; omega) i hiS)]; exact hr3
        have hn4 : i2 ≠ 0#u64 → headBit (L.mem s4 (rNextA i2)) = false := fun h0 => by
          rw [o4 _ (hrΩ i2 (hi2 h0)).2.2 (by rw [rp8, rNextA_val (hO.rp i2 (hi2 h0))]; have := rr i2 (hi2 h0); omega)]
          exact hn3 h0
        -- `sc.reply := r`
        step with obj.Sc.set_reply.spec as ⟨s5, e5⟩
        have hiR : ∀ c ∈ Scs, c ≠ i → i.val + 2 ^ Z i ≤ c.val ∨ c.val + 2 ^ Z c ≤ i.val := fun c hc hne =>
          hO.scDisj i hiS c hc (Ne.symm hne)
        obtain ⟨h5, hB5, hX5, hS5, hSg5, a5, -, i5, f5, -⟩ := link_all (w := r) h4 hB4 hX4 hS4 hSg4
          (hsub _ (hO.repW i hiS))
          (fun r' hr' e => by
            rw [hiv.2.2.2.2.2.2.1, rTcbA_val (hO.rp r' hr')] at e
            have := hO.rpSc r' hr' i hiS; have := hiv.1; omega)
          (fun c hc => by
            obtain ⟨h128c, e1, e2, e3, e4, e5, -⟩ := sc_facts hO hc
            rw [hiv.2.2.2.2.2.2.1, e1, e2, e3, e4, e5]
            have := hiv.1
            by_cases hci : c = i
            · subst hci; omega
            · have := hiR c hc hci; omega)
          (fun r' hr' e => by
            rw [hiv.2.2.2.2.2.2.1, rNextA_val (hO.rp r' hr')] at e
            have := hO.rpSc r' hr' i hiS; have := hiv.1; omega)
          (fun r' hr' e => by
            rw [hiv.2.2.2.2.2.2.1, rPrevA_val (hO.rp r' hr')] at e
            have := hO.rpSc r' hr' i hiS; have := hiv.1; omega)
          (fun c hc e _ => by
            by_cases hci' : c = i
            · rw [hci', tci4, id4]; exact ⟨hr, hiA, fun e' => hci e'.symm⟩
            · exfalso; have := hiR c hc hci'
              rw [hiv.2.2.2.2.2.2.1, (sc_facts hO hc).2.2.2.2.2.2.1] at e
              have := hiv.1; have := (sc_facts hO hc).1; omega)
          (fun n hn e => by rw [hiv.2.2.2.2.2.2.1] at e; have := hO.ntSc n hn i hiS; have := hiv.1; omega)
          (fun n hn e => by
            rw [hiv.2.2.2.2.2.2.1, ntfnBtA_val (hO.ntP n hn)] at e; have := hO.ntOSc n hn i hiS; have := hiv.1; omega)
          (fun c hc e => by
            obtain ⟨hPc, hzc⟩ := hO.sc c hc
            rw [hiv.2.2.2.2.2.2.1, scNtfnA_val hPc hzc] at e
            have := hiv.1; have := (sc_facts hO hc).1
            by_cases hci : c = i
            · subst hci; omega
            · have := hiR c hc hci; omega)
          (fun c hc e => by
            rw [hiv.2.2.2.2.2.2.1, show scYieldFromA c = core.num.U64.wrapping_add c layout.sc.YIELD_FROM from rfl,
              (sc_facts hO hc).2.2.2.2.2.2.2] at e
            have := hiv.1; have := (sc_facts hO hc).1
            by_cases hci : c = i
            · subst hci; omega
            · have := hiR c hc hci; omega)
          (scw_ne_spor hO hiS hiv.2.2.2.2.2.2.1 (by omega) (by omega))
          (fun r' hr' e => by
            rw [hiv.2.2.2.2.2.2.1, rNextA_val (hO.rp r' hr')] at e
            have := hO.rpSc r' hr' i hiS; have := hiv.1; omega)
          (fun c hc e r' hr' hb h0 ec => by
            exfalso
            have hci : c = i := by
              by_contra hci
              have := hiR c hc hci
              rw [hiv.2.2.2.2.2.2.1, (sc_facts hO hc).2.2.2.2.2.2.1] at e
              have := hiv.1; have := (sc_facts hO hc).1; omega
            subst hci
            have hh := hX4.2.1.head r' hr' hb h0
            rw [ec, hr4] at hh
            by_cases hz : i2 = 0#u64
            · exact hO.rp0 r' hr' (hh.symm.trans hz)
            · have := hn4 hz; rw [hh] at this; rw [this] at hb; exact absurd hb (by decide))
        rw [← e5] at h5 hB5 hX5 hS5 hSg5 a5 i5 f5
        -- `r.next := i` (head)
        step with obj.Reply.set_next.val1 as ⟨s6, e6⟩
        have hi_ev : i &&& ~~~1#u64 = i := mask1_of_even (by omega)
        obtain ⟨h6, hB6, hX6, hS6, hSg6, a6, -, i6, f6, -⟩ := link_all (w := (i &&& ~~~1#u64) ||| 1#u64)
          h5 hB5 hX5 hS5 hSg5 ((hrΩ r hr).2.2)
          (fun r' hr' e => by rw [rn16, rTcbA_val (hO.rp r' hr')] at e; have := rr r' hr'; omega)
          (rword_ne_sc hO hr (by rw [rn16]; omega))
          (fun r' hr' _ _ => by
            refine ⟨fun _ => ?_, fun hb0 => absurd hb0 (by rw [nx_head1]; simp)⟩
            rw [nx_mask _ _ (Or.inr rfl), hi_ev]; exact hiS)
          (fun r' hr' e => by rw [rn16, rPrevA_val (hO.rp r' hr')] at e; have := rr r' hr'; omega)
          (fun c hc e => absurd e (rword_ne_screp hO hr (by rw [rn16]; omega) c hc))
          (fun n hn e => by rw [rn16] at e; have := hO.ntRp n hn r hr; omega)
          (fun n hn e => by rw [rn16, ntfnBtA_val (hO.ntP n hn)] at e; have := hO.ntORp n hn r hr; omega)
          (rword_ne_scn hO hr (by rw [rn16]; omega)) (rword_ne_scy hO hr (by rw [rn16]; omega))
          (rword_ne_spor hO hr (by rw [rn16]; omega))
          (fun r' hr' e _ _ => by
            have : r' = r := UScalar.eq_of_val_eq (by
              rw [rn16, rNextA_val (hO.rp r' hr')] at e; have := rr r' hr'; omega)
            subst this
            rw [nx_mask _ _ (Or.inr rfl), hi_ev, e5]
            exact L.mem_wr_same (h4.omega _ (hsub _ (hO.repW i hiS))).1)
          (fun c hc e => absurd e (rword_ne_screp hO hr (by rw [rn16]; omega) c hc))
        rw [← e6] at h6 hB6 hX6 hS6 hSg6 a6 i6 f6
        -- the donation
        have F : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → L.mem s6 (core.num.U64.wrapping_add y K) =
            L.mem s2 (core.num.U64.wrapping_add y K) := fun y hy K hK hK8 =>
          ((f6 y hy K hK hK8).trans ((f5 y hy K hK hK8).trans (f4 y hy K hK hK8))).trans (f3 y hy K hK hK8)
        have ea6 : L.actionW s6 = L.actionW s2 := (a6.trans (a5.trans a4)).trans a3
        have ei6 : L.idleW s6 = L.idleW s2 := (i6.trans (i5.trans i4)).trans i3
        refine WP.spec_mono (schedcontext.donate.ipc hA s6 a i callee caller Q R h6 hB6 hX6 hS6 hSg6 hcl ?_ hi0
          ⟨?_, ?_, ?_⟩ ?_ hce ?_ ?_ ?_ ?_ hne (by rw [ei]; exact hcA hci0) (by rw [ei6, id2]; exact hcei)
          ((F callee hce 3672#u64 (by simp) (by simp)).trans rv2))
          fun r' hh => ?_
        · rw [scA_eq, F caller hcl _ (by simp) (by simp), ← scA_eq, sc2 caller hcl, ← ei]
        · rw [inqA_eq, F caller hcl _ (by simp) (by simp), ← inqA_eq, iq2 caller hcl]; exact hcq
        · rw [inqA_eq, F caller hcl _ (by simp) (by simp), ← inqA_eq, iq2 caller hcl]; exact hcr
        · rw [ea6]; rcases a2 with e | e
          · rw [e]; exact hca
          · rw [e]; exact fun e' => notT_small hT (by simp) (e' ▸ hcl)
        · rw [ei6, id2]; exact hci
        · rw [scA_eq, F callee hce _ (by simp) (by simp), ← scA_eq]; exact hd0
        · rw [inqA_eq, F callee hce _ (by simp) (by simp), ← inqA_eq, iq2 callee hce]; exact heq
        · rw [inqA_eq, F callee hce _ (by simp) (by simp), ← inqA_eq, iq2 callee hce]; exact her
        · rw [ea6]; rcases a2 with e | e
          · rw [e]; exact hea
          · rw [e]; exact fun e' => notT_small hT (by simp) (e' ▸ hce)
        · obtain ⟨s', a'⟩ := r'
          simp only [WP.uncurry'_pair] at hh ⊢
          refine ⟨hh.1, fun y hy hyc => ?_, Or.inr (by rw [hh.2.2.2, ei])⟩
          rw [hh.2.1 y hy, stA_eq, F y hy _ (by simp) (by simp), ← stA_eq]; exact st2 y hy hyc
      split
      · rename_i hne0
        have h0 : i2 ≠ 0#u64 := by simpa using hne0
        have hp2 := hi2 h0
        obtain ⟨p32, pt0, pp8, pn16⟩ := rp_facts hO hp2
        have rr : ∀ r' ∈ Rp, r'.val % 32 = 0 := fun r' hr' => (hO.rp r' hr').1
        step with obj.Reply.set_next.val0 as ⟨s3, e3⟩
        obtain ⟨h3, hB3, hX3, hS3, hSg3, a3, -, i3, f3, -⟩ := link_all (w := (r &&& ~~~1#u64) ||| 0#u64)
          h2 hB2 hX2 hS2 hSg2 ((hrΩ i2 hp2).2.2)
          (fun r' hr' e => by rw [pn16, rTcbA_val (hO.rp r' hr')] at e; have := rr r' hr'; omega)
          (rword_ne_sc hO hp2 (by rw [pn16]; omega))
          (fun r' hr' _ _ => by
            refine ⟨fun hb1 => absurd hb1 (by rw [nx_head0]; simp), fun _ => ?_⟩
            rw [nx_mask _ _ (Or.inl rfl), mask1_of_even (x := r) (by have := rr r hr; omega)]; exact hr)
          (fun r' hr' e => by rw [pn16, rPrevA_val (hO.rp r' hr')] at e; have := rr r' hr'; omega)
          (fun c hc e => absurd e (rword_ne_screp hO hp2 (by rw [pn16]; omega) c hc))
          (fun n hn e => by rw [pn16] at e; have := hO.ntRp n hn i2 hp2; omega)
          (fun n hn e => by rw [pn16, ntfnBtA_val (hO.ntP n hn)] at e; have := hO.ntORp n hn i2 hp2; omega)
          (rword_ne_scn hO hp2 (by rw [pn16]; omega)) (rword_ne_scy hO hp2 (by rw [pn16]; omega))
          (rword_ne_spor hO hp2 (by rw [pn16]; omega))
          (fun r' hr' _ hb1 => absurd hb1 (by rw [nx_head0]; simp))
          (fun c hc e => absurd e (rword_ne_screp hO hp2 (by rw [pn16]; omega) c hc))
        rw [← e3] at h3 hB3 hX3 hS3 hSg3 a3 i3 f3
        refine pre s3 h3 hB3 hX3 hS3 hSg3 f3 a3 i3 ?_ (fun _ => ?_)
        · rw [e3, L.mem_wr_ne (h2.omega _ (hrΩ i2 hp2).2.2).1 (h2.omega _ (hsub _ (hO.repW i hiS))).1
            (rword_ne_screp hO hp2 (by rw [pn16]; omega) i hiS)]; exact ei2.symm
        · rw [e3, L.mem_wr_same (h2.omega _ (hrΩ i2 hp2).2.2).1]; exact nx_head0 _
      · try simp only [Aeneas.Std.bind_ok]
        rename_i hz
        have hz' : i2 = 0#u64 := UScalar.eq_of_val_eq (by simpa using hz)
        exact pre s2 h2 hB2 hX2 hS2 hSg2 (fun _ _ _ _ _ => rfl) rfl rfl ei2.symm (fun h0 => absurd hz' h0)
    · exact (WP.spec_ok _).2 ok2
  · exact (WP.spec_ok _).2 ok2

/-! ## `unblock_sporadic` -/

/-- `unblock_sporadic` (the sporadic SC of `t`, unless it is the current SC,
gets its refills unblocked) keeps the invariants and the TCB fields. -/
theorem endpoint.unblock_sporadic.all {X : Set U64} (s : S) (t : obj.Tcb) {Q : U64 → U64 → List U64}
    {R : U64 → List U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T Ac s)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T) :
    endpoint.unblock_sporadic st s t ⦃ s' => SchedQueuesInvX st T Cs Ω H X s' Q R ∧ BoundInv st T Ac s' ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧ SCsOK st T Ω Sg Scs Z Ac s' ∧ SgOK st Ω Sg s' ∧
      L.actionW s' = L.actionW s ∧ L.curW s' = L.curW s ∧ L.idleW s' = L.idleW s ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ r ∈ Rp, L.mem s' (rTcbA r) = L.mem s (rTcbA r)) ⦄ := by
  have hT := h.tcbs
  have hsub := hSg.sub
  have triv : SchedQueuesInvX st T Cs Ω H X s Q R ∧ BoundInv st T Ac s ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z s ∧ SCsOK st T Ω Sg Scs Z Ac s ∧ SgOK st Ω Sg s ∧
      L.actionW s = L.actionW s ∧ L.curW s = L.curW s ∧ L.idleW s = L.idleW s ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        L.mem s (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ r ∈ Rp, L.mem s (rTcbA r) = L.mem s (rTcbA r)) :=
    ⟨h, hB, hX, hS, hSg, rfl, rfl, rfl, fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩
  unfold endpoint.unblock_sporadic
  step with obj.Tcb.sc.spec as ⟨i, i_post⟩
  step with sporadic.sc_sporadic.spec as ⟨b1, b1_post⟩
  split
  · rename_i hb1
    obtain ⟨hi0, hsp⟩ := b1_post hb1
    have hbt : L.mem s (scA t) ≠ 0#u64 := by rw [← i_post]; exact hi0
    obtain ⟨hiS, -, -⟩ := hX.2.2.bound t ht hbt
    rw [← i_post] at hiS
    have hW : RefillsWF st s i (Z i) := hS.wf hiS (hS.spor i hiS hsp)
    have hSCin : SCin st s Ω i (Z i) := ⟨hW, hX.1.scW i hiS⟩
    step with sched.cur_sc.spec as ⟨c4, _⟩
    step with sc_ne.spec as ⟨b2⟩
    split
    · have hN' := h.nodes _ h.cur
      have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
      have aR : Aligned (L.nodeA s layout.node.REPROGRAM) := nodeAt_aligned hN' (by rw [rp]; omega) (by rw [rp])
      have oR : Outside (L.nodeA s layout.node.REPROGRAM) i (Z i) :=
        hSCin.node_out h.omega h.cur hN' (by rw [rp]; omega) (by rw [rp])
      refine WP.spec_mono (WP.spec_and (sporadic.unblock_check.fr hW ⟨aR, oR⟩)
        (sporadic.unblock_check.wf hW ⟨aR, oR⟩)) fun s3 hw3 => ?_
      have w3 := hw3.1
      have hS3 := SCsOK.ring h hS hX hiS w3 hw3.2
      have wF : WritesIn st s s3 (L.Free s Ω Cs) := w3.mono' fun b hb hh => by
        rcases hh with hh | hh
        · exact Or.inl (hX.1.scW i hiS b hb hh.inSC)
        · exact hh ▸ free_cur_node h.cur (by simp [rp, LowFree])
      have nP : ∀ b, (InRing i (Z i) b ∨ b = L.nodeA s layout.node.REPROGRAM) → Aligned b →
          ¬ Prot T Rp Scs Nt b := fun b hh hb => by
        rcases hh with hh | hh
        · exact not_prot_ring h hX.1 hiS hb (Or.inl hh)
        · exact hh ▸ not_prot_node h hX.1 hsub h.cur (by rw [rp]; omega)
      have kn : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 56 →
          L.mem s3 (L.nodeA s o) = L.mem s (L.nodeA s o) := fun o ho h8 h56 => by
        refine w3.mem_eq (nodeAt_aligned hN' ho h8) ?_
        rintro (hh | hh)
        · have hm := hX.1.scW i hiS _ (nodeAt_aligned hN' ho h8) hh.inSC
          exact out_ne_node (h.omega _ hm) h.cur hN' ho rfl
        · have := congrArg UScalar.val hh
          simp only [LawfulStore.nodeA] at this
          rw [nodeAt_val hN' ho, nodeAt_val hN' (by rw [rp]; omega), rp] at this; omega
      have nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 56 →
          L.mem s3 (L.nodeAt s3 (L.cpu s3) o) = L.mem s (L.nodeAt s (L.cpu s) o) := fun o ho h8 h56 => by
        rw [w3.2.1, nodeAt_of_ksb w3.1]; exact kn o ho h8 h56
      have hX3 : XInv st T Cs Ω Sg Rp Scs Nt Z s3 := hX.writes hT
        (w3.mono' fun b hb hh => fun hp => nP b hh hb hp) (fun b hb => hb) (by
          unfold LawfulStore.cscW; rw [cscW_eq w3.1 w3.2.1, kn _ (by simp [layout.node.CUR_SC])
            (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])]; exact hX.2.2.cur)
          (hX.tn (TmFr.of_ring h hX hsub hiS w3)) (nd _ (by rw [idle8]; omega) (by rw [idle8]) (by rw [idle8]; omega))
      refine ⟨inv_of_free h wF, hB.free h wF, hX3, hS3, ⟨hsub, fun b hb => by rw [w3.1]; exact hSg.ks b hb,
        fun o h1' h2'' => by rw [w3.1]; exact hSg.ksΩ o h1' h2''⟩,
        nd _ (by rw [act_val]; omega) (by rw [act_val]) (by rw [act_val]; omega),
        nd _ (by rw [curth0]; omega) (by rw [curth0]) (by rw [curth0]; omega),
        nd _ (by rw [idle8]; omega) (by rw [idle8]) (by rw [idle8]; omega), fun y hy K hK hK8 => ?_,
        fun r hr => ?_⟩
      rotate_left
      · obtain ⟨hrΩ, -⟩ := objs_omega hX.1 hsub
        have hm := (hrΩ r hr).1
        refine w3.mem_eq (h.omega _ hm).1 ?_
        rintro (hh | hh)
        · have := hX.1.rpSc r hr i hiS
          have := hh.1; have := hh.2
          rw [rTcbA_val (hX.1.rp r hr)] at *
          omega
        · exact out_ne_node (h.omega _ hm) h.cur hN' (by rw [rp]; omega) (congrArg UScalar.val hh).symm
      refine w3.mem_eq (field_aligned (hT y hy) hK hK8) ?_
      rintro (hh | hh)
      · have hm := hX.1.scW i hiS _ (field_aligned (hT y hy) hK hK8) hh.inSC
        exact out_ne_field (h.omega _ hm) hy (hT y hy) hK rfl
      · exact node_ne_field hN' (by rw [rp]; omega) hy (hT y hy) hK hh.symm
    · exact (WP.spec_ok _).2 triv
  · exact (WP.spec_ok _).2 triv

/-- `unblock_check` on the SC of a bound thread keeps the invariants. -/
theorem sporadic.unblock_check.all {X : Set U64} (s : S) (t i : U64) {Q : U64 → U64 → List U64}
    {R : U64 → List U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T Ac s)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T)
    (i_post : i = L.mem s (scA t)) (hi0 : i ≠ 0#u64) (hiA : i ∈ Ac) :
    sporadic.unblock_check st s i ⦃ s' => SchedQueuesInvX st T Cs Ω H X s' Q R ∧ BoundInv st T Ac s' ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧ SCsOK st T Ω Sg Scs Z Ac s' ∧ SgOK st Ω Sg s' ∧
      L.actionW s' = L.actionW s ∧ L.curW s' = L.curW s ∧ L.idleW s' = L.idleW s ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ r ∈ Rp, L.mem s' (rTcbA r) = L.mem s (rTcbA r)) ⦄ := by
  have hT := h.tcbs
  have hsub := hSg.sub
  have hbt : L.mem s (scA t) ≠ 0#u64 := by rw [← i_post]; exact hi0
  obtain ⟨hiS, -, -⟩ := hX.2.2.bound t ht hbt
  rw [← i_post] at hiS
  have hW : RefillsWF st s i (Z i) := hS.wf hiS hiA
  have hSCin : SCin st s Ω i (Z i) := ⟨hW, hX.1.scW i hiS⟩
  have hN' := h.nodes _ h.cur
  have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
  have aR : Aligned (L.nodeA s layout.node.REPROGRAM) := nodeAt_aligned hN' (by rw [rp]; omega) (by rw [rp])
  have oR : Outside (L.nodeA s layout.node.REPROGRAM) i (Z i) :=
    hSCin.node_out h.omega h.cur hN' (by rw [rp]; omega) (by rw [rp])
  refine WP.spec_mono (WP.spec_and (sporadic.unblock_check.fr hW ⟨aR, oR⟩)
    (sporadic.unblock_check.wf hW ⟨aR, oR⟩)) fun s3 hw3 => ?_
  have w3 := hw3.1
  have hS3 := SCsOK.ring h hS hX hiS w3 hw3.2
  have wF : WritesIn st s s3 (L.Free s Ω Cs) := w3.mono' fun b hb hh => by
    rcases hh with hh | hh
    · exact Or.inl (hX.1.scW i hiS b hb hh.inSC)
    · exact hh ▸ free_cur_node h.cur (by simp [rp, LowFree])
  have nP : ∀ b, (InRing i (Z i) b ∨ b = L.nodeA s layout.node.REPROGRAM) → Aligned b →
      ¬ Prot T Rp Scs Nt b := fun b hh hb => by
    rcases hh with hh | hh
    · exact not_prot_ring h hX.1 hiS hb (Or.inl hh)
    · exact hh ▸ not_prot_node h hX.1 hsub h.cur (by rw [rp]; omega)
  have kn : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 56 →
      L.mem s3 (L.nodeA s o) = L.mem s (L.nodeA s o) := fun o ho h8 h56 => by
    refine w3.mem_eq (nodeAt_aligned hN' ho h8) ?_
    rintro (hh | hh)
    · have hm := hX.1.scW i hiS _ (nodeAt_aligned hN' ho h8) hh.inSC
      exact out_ne_node (h.omega _ hm) h.cur hN' ho rfl
    · have := congrArg UScalar.val hh
      simp only [LawfulStore.nodeA] at this
      rw [nodeAt_val hN' ho, nodeAt_val hN' (by rw [rp]; omega), rp] at this; omega
  have nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 56 →
      L.mem s3 (L.nodeAt s3 (L.cpu s3) o) = L.mem s (L.nodeAt s (L.cpu s) o) := fun o ho h8 h56 => by
    rw [w3.2.1, nodeAt_of_ksb w3.1]; exact kn o ho h8 h56
  have hX3 : XInv st T Cs Ω Sg Rp Scs Nt Z s3 := hX.writes hT
    (w3.mono' fun b hb hh => fun hp => nP b hh hb hp) (fun b hb => hb) (by
      unfold LawfulStore.cscW; rw [cscW_eq w3.1 w3.2.1, kn _ (by simp [layout.node.CUR_SC])
        (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])]; exact hX.2.2.cur)
      (hX.tn (TmFr.of_ring h hX hsub hiS w3)) (nd _ (by rw [idle8]; omega) (by rw [idle8]) (by rw [idle8]; omega))
  refine ⟨inv_of_free h wF, hB.free h wF, hX3, hS3, ⟨hsub, fun b hb => by rw [w3.1]; exact hSg.ks b hb,
    fun o h1' h2'' => by rw [w3.1]; exact hSg.ksΩ o h1' h2''⟩,
    nd _ (by rw [act_val]; omega) (by rw [act_val]) (by rw [act_val]; omega),
    nd _ (by rw [curth0]; omega) (by rw [curth0]) (by rw [curth0]; omega),
    nd _ (by rw [idle8]; omega) (by rw [idle8]) (by rw [idle8]; omega), fun y hy K hK hK8 => ?_,
    fun r hr => ?_⟩
  rotate_left
  · obtain ⟨hrΩ, -⟩ := objs_omega hX.1 hsub
    have hm := (hrΩ r hr).1
    refine w3.mem_eq (h.omega _ hm).1 ?_
    rintro (hh | hh)
    · have := hX.1.rpSc r hr i hiS
      have := hh.1; have := hh.2
      rw [rTcbA_val (hX.1.rp r hr)] at *
      omega
    · exact out_ne_node (h.omega _ hm) h.cur hN' (by rw [rp]; omega) (congrArg UScalar.val hh).symm
  refine w3.mem_eq (field_aligned (hT y hy) hK hK8) ?_
  rintro (hh | hh)
  · have hm := hX.1.scW i hiS _ (field_aligned (hT y hy) hK hK8) hh.inSC
    exact out_ne_field (h.omega _ hm) hy (hT y hy) hK rfl
  · exact node_ne_field hN' (by rw [rp]; omega) hy (hT y hy) hK hh.symm

/-! ## `set_thread_state` with the other invariants -/

theorem sts_all {X : Set U64} (s : S) (t : obj.Tcb) (v : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T) (hv : ¬ Blocked v)
    (hvr : v ≠ sched.TS_BLOCKED_ON_REPLY ∧ v ≠ sched.TS_BLOCKED_ON_RECV)
    (hx : t ∈ X ∨ ¬ Blocked (L.mem s (stA t)))
    (hnoref : ∀ r ∈ Rp, L.mem s (rTcbA r) ≠ t)
    (hq : (∀ c ∈ Cs, ∀ p : U64, p.val < 256 → t ∈ Q c p → Runnable v) ∧ (∀ c ∈ Cs, t ∈ R c → Runnable v) ∧
      (L.actionW s = t → Runnable v)) :
    sched.set_thread_state st s t v ⦃ s' => SchedQueuesInvX st T Cs Ω H {y | y ∈ X ∧ y ≠ t} s' Q R ∧
      BoundInv st T Ac s' ∧ XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧ SCsOK st T Ω Sg Scs Z Ac s' ∧ SgOK st Ω Sg s' ∧
      L.mem s' (stA t) = v ∧ KeepT st T Cs Rp Scs Nt t s s' ⦄ := by
  refine WP.spec_mono (WP.spec_and (sched.set_thread_state.inv s t v Q R h ht hv hx hq)
    (sched.set_thread_state.state s t v Q R h ht hX.1 hSg.sub)) fun s' ⟨h', e', k'⟩ => ?_
  exact ⟨h', hB.keepT h k' (by rw [e']; exact hv) (by rw [e']; exact hvr.1), hX.keepT k' (by rw [e']; exact hvr)
    (fun r hr e => absurd e (hnoref r hr)), hS.keepT hX k',
    ⟨hSg.sub, fun b hb => by rw [k'.ksb]; exact hSg.ks b hb, fun o h1 h2 => by rw [k'.ksb]; exact hSg.ksΩ o h1 h2⟩,
    e', k'⟩

/-! ## Endpoint dequeue of the head -/

/-- `BoundInv`, `XInv`, `SCsOK` and `SgOK` across a change that keeps the TCB
fields (other than the `Ep` links), the words of `Ω` and the node words. -/
theorem frame_bx {X : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s)
    (fld : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K))
    (om : ∀ a ∈ Ω, L.mem s' a = L.mem s a)
    (nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem s' (L.nodeAt s' (L.cpu s') o) = L.mem s (L.nodeAt s (L.cpu s) o))
    (hk : L.ksb s' = L.ksb s) (htm : TmFr st T Cs Nt s s') :
    BoundInv st T Ac s' ∧ XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧ SCsOK st T Ω Sg Scs Z Ac s' ∧ SgOK st Ω Sg s' ∧
      L.actionW s' = L.actionW s ∧ L.curW s' = L.curW s ∧ L.idleW s' = L.idleW s := by
  obtain ⟨hrΩ, hcΩ⟩ := objs_omega hX.1 hSg.sub
  have scf : ∀ y ∈ T, L.mem s' (scA y) = L.mem s (scA y) := fun y hy => by
    rw [scA_eq]; exact fld y hy _ (by simp) (by simp) (by simp) (by simp)
  have iqf : ∀ y ∈ T, L.mem s' (inqA y) = L.mem s (inqA y) := fun y hy => by
    rw [inqA_eq]; exact fld y hy _ (by simp) (by simp) (by simp) (by simp)
  have ea : L.actionW s' = L.actionW s := nd _ (by rw [act_val]; omega) (by rw [act_val])
  have ec : L.curW s' = L.curW s := nd _ (by rw [curth0]; omega) (by rw [curth0])
  have ei : L.idleW s' = L.idleW s := nd _ (by rw [idle8]; omega) (by rw [idle8])
  have ecs : L.cscW s' = L.cscW s := nd _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  refine ⟨hB.keep scf iqf ea ec ei
      (fun y hy => by rw [stA_eq]; exact fld y hy _ (by simp) (by simp) (by simp) (by simp)) h.curT h.idleT,
    hX.keep (fun r hr => ⟨om _ (hrΩ r hr).1, om _ (hrΩ r hr).2.1, om _ (hrΩ r hr).2.2⟩)
      (fun c hc => ⟨om _ (hcΩ c hc).1, om _ (hcΩ c hc).2.1⟩) scf
      (fun y hy => fld y hy _ (by simp) (by simp) (by simp) (by simp))
      (fun y hy => by rw [stA_eq]; exact fld y hy _ (by simp) (by simp) (by simp) (by simp))
      (by rw [ecs]; exact hX.2.2.cur) (fun c hc => om _ (hSg.sub _ (hX.1.repW c hc)))
      (fun y hy => fld y hy _ (by simp) (by simp) (by simp) (by simp)) (fun n hn => om _ (hSg.sub _ (hX.1.ntW n hn)))
      (hX.tn htm) (fun c hc => om _ (hSg.sub _ (hX.1.snW c hc)))
      (fun y hy => fld y hy _ (by simp) (by simp) (by simp) (by simp)) (fun c hc => om _ (hSg.sub _ (hX.1.syW c hc)))
      (fun c hc => om _ (hcΩ c hc).2.2.1) ei (fun y hy => fld y hy _ (by simp) (by simp) (by simp) (by simp)),
    SCsOK.keep hS hX hk scf ecs (fun c hc => ⟨om _ (hcΩ c hc).2.2.1, om _ (hcΩ c hc).2.2.2.1, om _ (hcΩ c hc).2.2.2.2⟩)
      (fun c hc => om _ (spor_omega hX.1 hc)) (fun c hc => om _ (hSg.sub _ (hX.1.repW c hc))),
    ⟨hSg.sub, fun b hb => by rw [hk]; exact hSg.ks b hb, fun o h1 h2 => by rw [hk]; exact hSg.ksΩ o h1 h2⟩,
    ea, ec, ei⟩

/-- The head of a sending (or receiving) endpoint's queue: a TCB blocked on
the endpoint in the state of the queue. -/
theorem ep_head {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {e w : U64}
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hH : H e = some .ep) (hw : w = 1#u64 ∨ w = 2#u64)
    (hst : L.epState s e = w) :
    (L.epQ s e).head ∈ T ∧ L.mem s (blockA (L.epQ s e).head) = e ∧
      (w = 1#u64 → L.mem s (stA (L.epQ s e).head) = sched.TS_BLOCKED_ON_SEND) ∧
      (w = 2#u64 → L.mem s (stA (L.epQ s e).head) = sched.TS_BLOCKED_ON_RECV) := by
  obtain ⟨E, EQ, hEW⟩ := h.eps
  have he : e ∈ E := (hEW.2.2.2.2.2.2.2.1 e).2 (Or.inl hH)
  obtain ⟨hE, -, hq⟩ := hEW.1 e he
  obtain ⟨k1, k2, -, -, k4, k5⟩ := hEW.2.2.2.2.2
  have hne : EQ e ≠ [] := fun h0 => by
    have := (k5 e he h0).1 hH; rw [hst] at this; rcases hw with rfl | rfl <;> exact absurd this (by decide)
  obtain ⟨y, ys, hys⟩ := List.exists_cons_of_ne_nil hne
  have hhd : (L.epQ s e).head = y := by rw [hq.head, hys]; rfl
  have hy : y ∈ EQ e := by rw [hys]; exact List.mem_cons_self
  obtain ⟨-, hbe, hbl⟩ := hEW.2.2.2.1 e he y hy
  have hyT := hq.mem y hy
  obtain ⟨c1, c2, c3⟩ := k4 e he y hy
  obtain ⟨-, -, r3, r4, r6⟩ := ts_vals
  rw [hhd]
  refine ⟨hyT, hbe, fun hw1 => ?_, fun hw2 => ?_⟩
  · rcases hbl with hb | hb | hb
    · exact hb
    · have := c2 hb; rw [hst, hw1] at this; exact absurd this (by decide)
    · have := k2 y hyT (by simp) hb; rw [hbe, hH] at this; cases this
  · rcases hbl with hb | hb | hb
    · have := c1 hb; rw [hst, hw2] at this; exact absurd this (by decide)
    · exact hb
    · have := k2 y hyT (by simp) hb; rw [hbe, hH] at this; cases this

/-! ## State values -/

theorem runnable_running : Runnable sched.TS_RUNNING := Or.inl rfl
theorem not_blocked_running : ¬ Blocked sched.TS_RUNNING := fun hb => blocked_not_runnable hb runnable_running
theorem running_ne : sched.TS_RUNNING ≠ sched.TS_BLOCKED_ON_REPLY ∧ sched.TS_RUNNING ≠ sched.TS_BLOCKED_ON_RECV :=
  ⟨runnable_ne_reply runnable_running, runnable_ne_recv runnable_running⟩
theorem inactive_ne : sched.TS_INACTIVE ≠ sched.TS_BLOCKED_ON_REPLY ∧ sched.TS_INACTIVE ≠ sched.TS_BLOCKED_ON_RECV := by
  obtain ⟨-, -, r3, -⟩ := ts_vals
  rw [ts_inactive, reply_val, r3]; decide
theorem send_ne : sched.TS_BLOCKED_ON_SEND ≠ sched.TS_BLOCKED_ON_REPLY ∧
    sched.TS_BLOCKED_ON_SEND ≠ sched.TS_BLOCKED_ON_RECV := by
  obtain ⟨-, -, r3, r4, -⟩ := ts_vals
  rw [reply_val, r3, r4]; decide
theorem recv_ne_reply : sched.TS_BLOCKED_ON_RECV ≠ sched.TS_BLOCKED_ON_REPLY := by
  obtain ⟨-, -, r3, -⟩ := ts_vals
  rw [reply_val, r3]; decide

/-- An endpoint's state word is idle, sending or receiving. -/
theorem ep_state3 {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {e : U64}
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hH : H e = some .ep) :
    L.epState s e = 0#u64 ∨ L.epState s e = 1#u64 ∨ L.epState s e = 2#u64 := by
  obtain ⟨E, EQ, hEW⟩ := h.eps
  have he : e ∈ E := (hEW.2.2.2.2.2.2.2.1 e).2 (Or.inl hH)
  obtain ⟨k1, k2, -, -, k4, k5⟩ := hEW.2.2.2.2.2
  by_cases h0 : EQ e = []
  · exact Or.inl ((k5 e he h0).1 hH)
  obtain ⟨y, ys, hys⟩ := List.exists_cons_of_ne_nil h0
  have hy : y ∈ EQ e := by rw [hys]; exact List.mem_cons_self
  obtain ⟨-, hbe, hbl⟩ := hEW.2.2.2.1 e he y hy
  have hyT := (hEW.1 e he).2.2.mem y hy
  obtain ⟨c1, c2, -⟩ := k4 e he y hy
  rcases hbl with hb | hb | hb
  · exact Or.inr (Or.inl (c1 hb))
  · exact Or.inr (Or.inr (c2 hb))
  · have := k2 y hyT (by simp) hb; rw [hbe, hH] at this; cases this

/-! ## `receive_from_sender` -/

theorem empty_congr' {t : U64} : ∀ y, y ∈ {y : U64 | (y ∈ (∅ : Set U64) ∨ y = t) ∧ y ≠ t} ↔ y ∈ (∅ : Set U64) := by
  intro y; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, false_or, iff_false, not_and]; exact fun a b => b a

/-- The frame of a message transfer: the scheduler words, the TCB fields from
`STATE`, the reply objects' `TCB` words and the kernel base. -/
def XferFr (st : machine.Store S) [L : LawfulStore st] (T Rp : Set U64) (s s' : S) : Prop :=
  L.actionW s' = L.actionW s ∧ L.curW s' = L.curW s ∧ L.idleW s' = L.idleW s ∧ L.cscW s' = L.cscW s ∧
    (∀ y ∈ T, ∀ K : U64, 3328 ≤ K.val → K.val < 4096 → K.val % 8 = 0 →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
    (∀ r ∈ Rp, L.mem s' (rTcbA r) = L.mem s (rTcbA r)) ∧ L.ksb s' = L.ksb s

/-- The message transfer between two TCBs keeps the invariants, within
`XferFr`.  It writes the receiver's user context and IPC buffer (`XferFoot`),
a granted cap's receive slot and CDT neighbours (cap-slot words) and, for a
timeout fault, the sender's SC's `CONSUMED` word; `xferOK_of` (QueueXfer)
proves it from the placement facts. -/
def XferOK (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (G : S → Prop) : Prop :=
  ∀ (Ac X : Set U64) (Q : U64 → U64 → List U64) (R : U64 → List U64) (s : S) (a : A) (snd ep badge : U64)
    (grant : Bool) (rcv : U64), snd ∈ T → rcv ∈ T →
    SchedQueuesInvX st T Cs Ω H X s Q R → BoundInv st T Ac s → XInv st T Cs Ω Sg Rp Scs Nt Z s →
    SCsOK st T Ω Sg Scs Z Ac s → SgOK st Ω Sg s → UserOK st T Cs Ω H U s → G s →
    ipc.do_ipc_transfer st ar s a snd ep badge grant rcv ⦃ s' =>
      SchedQueuesInvX st T Cs Ω H X s' Q R ∧ BoundInv st T Ac s' ∧ XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧
      SCsOK st T Ω Sg Scs Z Ac s' ∧ SgOK st Ω Sg s' ∧ XferFr st T Rp s s' ∧ G s' ⦄

/-- seL4 `receiveIPC`'s end on a sending endpoint: the head sender is
dequeued, the message transferred, and the sender either becomes blocked on
the receiver's reply (a call, with the reply bookkeeping and SC donation),
inactive, or running. a64: named premise **[J] `hRV`** (`RunVcpuInv`), with the receiver not in
`TS_RUNNING_VM` (`hvm`): the receiver, to which a call donates its SC, runs no VCPU. -/
theorem endpoint.receive_from_sender.ipc {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {U : Set U64} {G : S → Prop} (hxf : XferOK st ar T Cs Ω H Sg Rp Scs Nt Z U G) (s : S) (a : A)
    (thread e reply : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (hG : ∀ s1, H e = some .ep → (L.epState s e = 1#u64 ∨ L.epState s e = 2#u64) →
      endpoint.ep_dequeue st s e (L.epQ s e).head = ok s1 → G s1)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hU : UserOK st T Cs Ω H U s)
    (hc : CanBlock st T Ac s thread)
    (hH : H e = some .ep) (hst : L.epState s e ≠ 0#u64 ∧ L.epState s e ≠ 2#u64)
    (hr : reply ≠ 0#u64 → reply ∈ Rp ∧ (L.mem s (rTcbA reply) = 0#u64 ∨ L.mem s (rTcbA reply) = thread))
    (hRV : RunVcpuInv st T s) (hvm : L.mem s (stA thread) ≠ sched.TS_RUNNING_VM) :
    endpoint.receive_from_sender st ar s a thread e reply ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  have hT := h.tcbs
  have ht := hc.mem
  have hst1 : L.epState s e = 1#u64 := by
    rcases ep_state3 h hH with e0 | e0 | e0
    · exact absurd e0 hst.1
    · exact e0
    · exact absurd e0 hst.2
  obtain ⟨hdT, hbe, hds, -⟩ := ep_head h hH (Or.inl rfl) hst1
  have hds := hds rfl
  set hd := (L.epQ s e).head with hhd
  have hdt : hd ≠ thread := fun e' => hc.nb (by rw [← e', hds]; exact Or.inl rfl)
  have hdi : L.idleW s ≠ hd := fun e' => hB.idleNB (by rw [e', hds]; exact Or.inl (Or.inl rfl))
  -- the reply object is unused
  have hr' : reply ≠ 0#u64 → reply ∈ Rp ∧ L.mem s (rTcbA reply) = 0#u64 := fun h0 => by
    obtain ⟨h1, h2⟩ := hr h0
    refine ⟨h1, h2.resolve_right fun e' => hX.noref (hT _ ht) hc.nrp (fun e2 => hc.nb (Or.inr (Or.inl e2))) _ h1 e'⟩
  unfold endpoint.receive_from_sender
  step with endpoint.get_queue.spec as ⟨q, eq⟩
  subst eq
  have hdq := endpoint.ep_dequeue.inv s hd Q R h hdT (by simp) (Or.inl hds)
  rw [hbe] at hdq
  refine WP.spec_bind (spec_eq' hdq) ?_
  rintro s1 ⟨eq1, h1, f1, o1, n1, k1, c1, nc1⟩
  obtain ⟨hB1, hX1, hS1, hSg1, ea1, ec1, ei1⟩ := frame_bx h hB hX hS hSg f1 o1 n1 k1
    (TmFr.mk0 ⟨k1, fun y hy K a b c => f1 y hy K (by omega) c (by omega) (by omega),
      fun c hc o ho => nc1 c hc o (by omega) (by omega), fun n' hn' => o1 _ (hSg.sub _ (hX.1.ntB n' hn').2)⟩)
  step with obj.Tcb.block_badge.any as ⟨badge, _⟩
  step with obj.Tcb.block_flags.any as ⟨flags, _⟩
  simp only [lift, Aeneas.Std.bind_ok]
  refine WP.spec_bind (hxf _ _ _ _ s1 a hd e badge _ thread hdT ht h1 hB1 hX1 hS1 hSg1 (hU.ksb k1) (hG s1 hH (Or.inl hst1) eq1)) ?_
  rintro s2 ⟨h2, hB2, hX2, hS2, hSg2, ⟨ea2, ec2, ei2, ecs2, f2, o2, -⟩, -⟩
  refine WP.spec_bind (endpoint.unblock_sporadic.all s2 hd h2 hB2 hX2 hS2 hSg2 hdT) ?_
  rintro s3 ⟨h3, hB3, hX3, hS3, hSg3, ea3, ec3, ei3, f3, r3⟩
  step with obj.Tcb.fault_type.any as ⟨ftype, _⟩
  -- facts at `s3`
  have F : ∀ y ∈ T, ∀ K : U64, 3328 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
      L.mem s3 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K h0 hK hK8 h1 h2' => (f3 y hy K hK hK8).trans ((f2 y hy K h0 hK hK8).trans (f1 y hy K hK hK8 h1 h2'))
  have st3 : ∀ y ∈ T, L.mem s3 (stA y) = L.mem s (stA y) := fun y hy => by
    rw [stA_eq]; exact F y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)
  have iq3 : ∀ y ∈ T, L.mem s3 (inqA y) = L.mem s (inqA y) := fun y hy => by
    rw [inqA_eq]; exact F y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)
  have ea : L.actionW s3 = L.actionW s := ea3.trans (ea2.trans ea1)
  have ei : L.idleW s3 = L.idleW s := ei3.trans (ei2.trans ei1)
  have hds3 : L.mem s3 (stA hd) = sched.TS_BLOCKED_ON_SEND := (st3 hd hdT).trans hds
  have rv3 : L.mem s3 (runVcpuA thread) = 0#u64 :=
    (F thread ht 3672#u64 (by simp) (by simp) (by simp) (by simp) (by simp)).trans (hRV.zero ht hvm)
  obtain ⟨dq, dr, da⟩ := blocked_out h3 hdT (by rw [hds3]; exact blocked_not_runnable (Or.inl rfl))
  have hXc : ExcT {y | y ∈ (∅ : Set U64) ∨ y = hd} hd := fun y hy => by simpa using hy
  have hx3 : hd ∈ {y | y ∈ (∅ : Set U64) ∨ y = hd} := Or.inr rfl
  have rt3 : ∀ r ∈ Rp, L.mem s3 (rTcbA r) = L.mem s (rTcbA r) := fun r hr0 =>
    (r3 r hr0).trans ((o2 r hr0).trans (o1 _ (hSg.sub _ (hX.1.tcbW hr0))))
  have sc3 : L.mem s3 (scA hd) = L.mem s (scA hd) := by
    rw [scA_eq]; exact F hd hdT _ (by simp) (by simp) (by simp) (by simp) (by simp)
  have hdA : L.mem s3 (scA hd) ≠ 0#u64 → L.mem s3 (scA hd) ∈ Ac := fun h0 => by
    rw [sc3] at h0 ⊢
    exact hB.sact hd hdT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [hds]; exact Or.inl rfl)))))))
      h0
  have E1 : ∀ cd : Bool, reply ≠ 0#u64 → ipc.reply_push st ar s3 a hd thread reply cd ⦃ s' _ =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := fun cd h0 =>
    WP.spec_mono (ipc.reply_push.ipc hA s3 a hd thread reply cd Q R h3 hXc (Or.inl hx3) hB3 hX3 hS3 hSg3 hdT dq dr da
      (by rw [ei]; exact hdi) (by rw [hds3]; exact send_ne) (hr' h0).1 h0 (by rw [rt3 _ (hr' h0).1]; exact (hr' h0).2)
      ht (Ne.symm hdt) (by rw [iq3 _ ht]; exact hc.nq) (by rw [iq3 _ ht]; exact hc.nr) (by rw [ea]; exact hc.na)
      (by rw [ei]; exact hc.ni) hdA rv3)
      fun r hh => by obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at hh ⊢; exact hh.1
  have E1' : reply ≠ 0#u64 → (do
      let i3 ← obj.Tcb.sc st hd s3
      let can_donate ← if (i3 != 0#u64) = true then ok (ftype != fl4_abi.consts.fault.Timeout) else ok false
      ipc.reply_push st ar s3 a hd thread reply can_donate) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
    intro h0
    step with obj.Tcb.sc.spec as ⟨i3, _⟩
    split <;> (try simp only [Aeneas.Std.bind_ok]) <;> exact E1 _ h0
  have E2 : (do
      let s4 ← sched.set_thread_state st s3 hd sched.TS_INACTIVE
      ok (s4, a)) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
    refine WP.spec_bind (sts_all s3 hd _ Q R h3 hB3 hX3 hS3 hSg3 hdT not_blocked_inactive inactive_ne
      (Or.inl hx3) (hX3.noref (h3.tcbs _ hdT) (by rw [hds3]; exact send_ne.1) (by rw [hds3]; exact send_ne.2))
      ⟨fun c hc' p hp hm => absurd hm (h3.notQ hdT dq hc' hp),
        fun c hc' hm => absurd hm (h3.notR hdT dr hc'), fun e' => absurd e' da⟩) fun s4 hh => ?_
    obtain ⟨h4, hB4, hX4, hS4, hSg4, -, -⟩ := hh
    exact (WP.spec_ok _).2 ⟨⟨Q, R, h4.congrX empty_congr'⟩, hB4, hX4, hS4, hSg4⟩
  have E3 : (do
      let s4 ← sched.set_thread_state st s3 hd sched.TS_RUNNING
      let s5 ← sched.possible_switch_to st s4 hd
      ok (s5, a)) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
    refine WP.spec_bind (sts_all s3 hd _ Q R h3 hB3 hX3 hS3 hSg3 hdT not_blocked_running running_ne
      (Or.inl hx3) (hX3.noref (h3.tcbs _ hdT) (by rw [hds3]; exact send_ne.1) (by rw [hds3]; exact send_ne.2))
      ⟨fun _ _ _ _ _ => runnable_running, fun _ _ _ => runnable_running,
        fun _ => runnable_running⟩) fun s4 hh => ?_
    obtain ⟨h4, hB4, hX4, hS4, hSg4, e4, k4⟩ := hh
    have h4' := h4.congrX empty_congr'
    refine WP.spec_bind (sched.possible_switch_to.sch s4 hd Q R h4' hB4 hSg4 hdT (by rw [e4]; exact runnable_running)
      (fun h0 => by rw [k4.scf hdT] at h0 ⊢; exact hdA h0))
      fun s5 hh => ?_
    obtain ⟨p5, -, -⟩ := hh
    exact (WP.spec_ok _).2 ⟨p5.inv, p5.bnd, hX4.fr p5.fr, hS4.fr p5.fr, hSg4.fr p5.fr⟩
  repeat' split
  all_goals first
    | exact E2
    | exact E3
    | (rename_i hh; exact E1' (by simpa using hh))

/-! ## `send_ipc` -/

/-- No reply names a thread whose reply field is clear. -/
theorem XInv.noref0 {s : S} {t : U64} (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hta : TcbAddr t)
    (h0 : L.mem s (replyA t) = 0#u64) : ∀ r ∈ Rp, L.mem s (rTcbA r) ≠ t := fun r hr e => by
  obtain ⟨b0, -, b2, -⟩ := hX.2.1.back r hr (by rw [e]; exact fun e0 => hta.ne0 (by rw [e0]; rfl))
  rw [e, h0] at b2; exact b0 b2.symm

theorem excT_congr {X : Set U64} {t : U64} (hX : ExcT X t) :
    ∀ y, y ∈ {y : U64 | y ∈ X ∧ y ≠ t} ↔ y ∈ (∅ : Set U64) := by
  intro y
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]
  exact hX y

/-- The end of `send_ipc` on a receiving endpoint: the receiver runs, its
sporadic SC is unblocked, and it may preempt. -/
theorem send_tail {X : Set U64} (s4 : S) {A : Type _} (a1 : A) (hd : U64) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h4 : SchedQueuesInvX st T Cs Ω H X s4 Q R) (hB4 : BoundInv st T Ac s4)
    (hX4 : XInv st T Cs Ω Sg Rp Scs Nt Z s4) (hS4 : SCsOK st T Ω Sg Scs Z Ac s4) (hSg4 : SgOK st Ω Sg s4) (hdT : hd ∈ T)
    (hXc : ExcT X hd) (hx : hd ∈ X ∨ ¬ Blocked (L.mem s4 (stA hd))) (hnr : ∀ r ∈ Rp, L.mem s4 (rTcbA r) ≠ hd)
    (hdA : L.mem s4 (scA hd) ≠ 0#u64 → L.mem s4 (scA hd) ∈ Ac) :
    (do
      let s5 ← sched.set_thread_state st s4 hd sched.TS_RUNNING
      let s6 ← endpoint.unblock_sporadic st s5 hd
      let s7 ← sched.possible_switch_to st s6 hd
      ok (s7, a1)) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  refine WP.spec_bind (sts_all s4 hd _ Q R h4 hB4 hX4 hS4 hSg4 hdT not_blocked_running running_ne hx hnr
    ⟨fun _ _ _ _ _ => runnable_running, fun _ _ _ => runnable_running, fun _ => runnable_running⟩) fun s5 hh => ?_
  obtain ⟨h5, hB5, hX5, hS5, hSg5, e5, k5⟩ := hh
  have h5' := h5.congrX (excT_congr hXc)
  refine WP.spec_bind (endpoint.unblock_sporadic.all s5 hd h5' hB5 hX5 hS5 hSg5 hdT) fun s6 hh => ?_
  obtain ⟨h6, hB6, hX6, hS6, hSg6, -, -, -, f6, -⟩ := hh
  have e6 : L.mem s6 (stA hd) = sched.TS_RUNNING := by
    rw [stA_eq, f6 hd hdT _ (by simp) (by simp), ← stA_eq]; exact e5
  have sc6 : L.mem s6 (scA hd) = L.mem s4 (scA hd) := by
    rw [scA_eq, f6 hd hdT _ (by simp) (by simp), ← scA_eq]; exact k5.scf hdT
  refine WP.spec_bind (sched.possible_switch_to.sch s6 hd Q R h6 hB6 hSg6 hdT (by rw [e6]; exact runnable_running)
    (fun h0 => by rw [sc6] at h0 ⊢; exact hdA h0))
    fun s7 hh => ?_
  obtain ⟨p7, -, -⟩ := hh
  exact (WP.spec_ok _).2 ⟨p7.inv, p7.bnd, hX6.fr p7.fr, hS6.fr p7.fr, hSg6.fr p7.fr⟩

/-- seL4 `sendIPC`: on an idle or sending endpoint the sender blocks (or
returns); on a receiving endpoint the head receiver is dequeued, gets the
message, the reply bookkeeping is done (reply object unlinked from the
receiver, pushed for a call or a fault, with SC donation), and the receiver
runs.  Caller-level preconditions: `t` can block (`CanBlock`: not blocked,
queued, the switch-to candidate or the idle thread), and if it may donate it
is bound (`hdon`): on the syscall path the sender is the current thread,
which has an SC in MCS, and on the fault path FL4 sets `can_donate` to
`t.sc != 0`. a64: named premise **[J] `hRV`** (`RunVcpuInv`): the receiver, blocked on the endpoint, runs
no VCPU, for the donation's `migrate_tcb`. -/
theorem endpoint.send_ipc.ipc {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {U : Set U64}
    {G : S → Prop} (hxf : XferOK st ar T Cs Ω H Sg Rp Scs Nt Z U G) (s : S) (a : A) (blocking do_call : Bool)
    (badge : U64) (can_grant can_grant_reply can_donate : Bool) (t e : U64)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (hG : ∀ s1, H e = some .ep → (L.epState s e = 1#u64 ∨ L.epState s e = 2#u64) →
      endpoint.ep_dequeue st s e (L.epQ s e).head = ok s1 → G s1)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hU : UserOK st T Cs Ω H U s)
    (hc : CanBlock st T Ac s t) (hdon : can_donate = true → L.mem s (scA t) ≠ 0#u64)
    (hH : H e = some .ep) (hRV : RunVcpuInv st T s) :
    endpoint.send_ipc st ar s a blocking do_call badge can_grant can_grant_reply can_donate t e
      ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  have hidle := hc.ni
  have hT := h.tcbs
  have ht := hc.mem
  have hta := hT t ht
  rcases ep_state3 h hH with e0 | e0 | e0
  · exact WP.spec_mono (endpoint.send_ipc.block ar s a blocking do_call badge can_grant can_grant_reply can_donate
      t e Q R h hB hX hS hSg (fun _ => hc) hH (Or.inl e0)) fun r hh => by
        obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at hh ⊢; exact ⟨⟨Q, R, hh.1⟩, hh.2⟩
  · exact WP.spec_mono (endpoint.send_ipc.block ar s a blocking do_call badge can_grant can_grant_reply can_donate
      t e Q R h hB hX hS hSg (fun _ => hc) hH (Or.inr e0)) fun r hh => by
        obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at hh ⊢; exact ⟨⟨Q, R, hh.1⟩, hh.2⟩
  -- a receiving endpoint
  obtain ⟨hdT, hbe, -, hds⟩ := ep_head h hH (Or.inr rfl) e0
  have hds := hds rfl
  set hd := (L.epQ s e).head with hhd
  have hdt : hd ≠ t := fun e' => hc.nb (by rw [← e', hds]; exact Or.inr (Or.inl rfl))
  have hdi : L.idleW s ≠ hd := fun e' => hB.idleNB (by rw [e', hds]; exact Or.inl (Or.inr (Or.inl rfl)))
  have hdta := hT hd hdT
  unfold endpoint.send_ipc
  step with obj.Ep.state.spec as ⟨v, hv⟩
  have hv2 : v = 2#u64 := hv.trans e0
  rw [hv2]
  simp only [ep_idle_val, ep_send_val', show ¬ ((2#u64) = 0#u64) from by decide,
    show ¬ ((2#u64) = 1#u64) from by decide, ↓reduceIte]
  have hsub := hSg.sub
  step with endpoint.get_queue.spec as ⟨q, eq⟩
  subst eq
  have hdq := endpoint.ep_dequeue.inv s hd Q R h hdT (by simp) (Or.inr (Or.inl hds))
  rw [hbe] at hdq
  refine WP.spec_bind (spec_eq' hdq) ?_
  rintro s1 ⟨eq1, h1, f1, o1, n1, k1, c1, nc1⟩
  obtain ⟨hB1, hX1, hS1, hSg1, ea1, ec1, ei1⟩ := frame_bx h hB hX hS hSg f1 o1 n1 k1
    (TmFr.mk0 ⟨k1, fun y hy K a b c => f1 y hy K (by omega) c (by omega) (by omega),
      fun c hc o ho => nc1 c hc o (by omega) (by omega), fun n' hn' => o1 _ (hSg.sub _ (hX.1.ntB n' hn').2)⟩)
  refine WP.spec_bind (hxf _ _ _ _ s1 a t e badge can_grant hd ht hdT h1 hB1 hX1 hS1 hSg1 (hU.ksb k1) (hG s1 hH (Or.inr e0) eq1)) ?_
  rintro s2 ⟨h2, hB2, hX2, hS2, hSg2, ⟨ea2, ec2, ei2, ecs2, f2, o2, -⟩, -⟩
  have F : ∀ y ∈ T, ∀ K : U64, 3328 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
      L.mem s2 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K h0 hK hK8 h1' h2' => (f2 y hy K h0 hK hK8).trans (f1 y hy K hK hK8 h1' h2')
  have Fst : ∀ y ∈ T, L.mem s2 (stA y) = L.mem s (stA y) := fun y hy => by
    rw [stA_eq]; exact F y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)
  have Frp : ∀ y ∈ T, L.mem s2 (replyA y) = L.mem s (replyA y) := fun y hy =>
    F y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)
  have Fiq : ∀ y ∈ T, L.mem s2 (inqA y) = L.mem s (inqA y) := fun y hy => by
    rw [inqA_eq]; exact F y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)
  have Fsc : ∀ y ∈ T, L.mem s2 (scA y) = L.mem s (scA y) := fun y hy => by
    rw [scA_eq]; exact F y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)
  have ea2' : L.actionW s2 = L.actionW s := ea2.trans ea1
  have ei2' : L.idleW s2 = L.idleW s := ei2.trans ei1
  step with obj.Tcb.reply_obj.spec as ⟨i, ei⟩
  have hds2 : L.mem s2 (stA hd) = sched.TS_BLOCKED_ON_RECV := (Fst hd hdT).trans hds
  have rv2 : L.mem s2 (runVcpuA hd) = 0#u64 :=
    (F hd hdT 3672#u64 (by simp) (by simp) (by simp) (by simp) (by simp)).trans
      (hRV.blocked hdT (by rw [hds]; exact Or.inr (Or.inl rfl)))
  -- the reply object leaves the receiver
  refine WP.spec_bind (Pₘ := fun s3 => ∃ X3 : Set U64, SchedQueuesInvX st T Cs Ω H X3 s3 Q R ∧ BoundInv st T Ac s3 ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z s3 ∧ SCsOK st T Ω Sg Scs Z Ac s3 ∧ SgOK st Ω Sg s3 ∧ ExcT X3 hd ∧
      (hd ∈ X3 ∨ ¬ Blocked (L.mem s3 (stA hd))) ∧ ¬ Runnable (L.mem s3 (stA hd)) ∧
      (hd ∈ X3 → L.mem s3 (replyA hd) = 0#u64) ∧ (hd ∉ X3 → L.mem s3 (stA hd) = sched.TS_INACTIVE) ∧
      ((i != 0#u64) = true → hd ∉ X3 ∧ i ∈ Rp ∧ L.mem s3 (rTcbA i) = 0#u64) ∧
      L.mem s3 (stA t) = L.mem s (stA t) ∧ L.mem s3 (inqA t) = L.mem s (inqA t) ∧
      L.mem s3 (scA t) = L.mem s (scA t) ∧ L.actionW s3 ≠ t ∧ L.idleW s3 = L.idleW s ∧
      L.mem s3 (scA hd) = L.mem s (scA hd) ∧ L.mem s3 (runVcpuA hd) = 0#u64) ?_ ?_
  · split
    · rename_i hi
      have hi0 : i ≠ 0#u64 := by simpa using hi
      obtain ⟨hiR, hit⟩ := hX2.2.1.recv hd hdT hds2 (by rw [← ei]; exact hi0)
      rw [← ei] at hiR hit
      refine WP.spec_mono (ipc.reply_unlink.inv s2 i hd Q R h2 hdT hX2.1 hsub hiR hit
        (by rw [hds2]; exact blocked_not_runnable (Or.inr (Or.inl rfl))) (Or.inl (Or.inr rfl))) fun s3 hh => ?_
      obtain ⟨h3, e3, k3, z3⟩ := hh
      have hclr : ∀ r ∈ Rp, L.mem s2 (rTcbA r) = hd → L.mem s3 (rTcbA r) = 0#u64 := by
        intro r hr er
        obtain ⟨-, -, b2, -⟩ := hX2.2.1.back r hr (by rw [er]; exact fun e0 => hdta.ne0 (by rw [e0]; rfl))
        rw [er, ← ei] at b2; rw [← b2]; exact z3
      refine ⟨_, h3, hB2.keepT h2 k3 (by rw [e3]; exact not_blocked_inactive) (by rw [e3]; exact inactive_ne.1),
        hX2.keepT k3 (by rw [e3]; exact inactive_ne) hclr, hS2.keepT hX2 k3,
        ⟨hsub, fun b hb => by rw [k3.ksb]; exact hSg2.ks b hb, fun o h1' h2' => by rw [k3.ksb]; exact hSg2.ksΩ o h1' h2'⟩,
        fun y hy => ?_, Or.inr (by rw [e3]; exact not_blocked_inactive), by rw [e3]; exact not_runnable_inactive,
        fun hm => absurd rfl hm.2, fun _ => e3, fun _ => ⟨fun hm => hm.2 rfl, hiR, z3⟩,
        (k3.stf ht (Ne.symm hdt)).trans (Fst t ht), (k3.inqf ht).trans (Fiq t ht), (k3.scf ht).trans (Fsc t ht),
        ?_, k3.idleW.trans ei2', (k3.scf hdT).trans (Fsc hd hdT),
        (k3.fld hd hdT 3672#u64 (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)).trans rv2⟩
      · obtain ⟨hy1, hy2⟩ := hy
        rcases hy1 with hy1 | hy1
        · exact absurd hy1 (Set.notMem_empty _)
        · exact absurd hy1 hy2
      · rcases k3.act with e' | e'
        · rw [e', ea2']; exact hc.na
        · rw [e']; exact fun e2 => notT_small hT (by simp) (e2 ▸ ht)
    · rename_i hi
      have hi0 : i = 0#u64 := by simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hi; exact hi
      refine (WP.spec_ok _).2 ⟨_, h2, hB2, hX2, hS2, hSg2, fun y hy => by simpa using hy, Or.inl (Or.inr rfl),
        by rw [hds2]; exact blocked_not_runnable (Or.inr (Or.inl rfl)), fun _ => by rw [← ei, hi0],
        fun hm => absurd (Or.inr rfl) hm, fun hi' => absurd hi0 (by simpa using hi'),
        Fst t ht, Fiq t ht, Fsc t ht, by rw [ea2']; exact hc.na, ei2', Fsc hd hdT, rv2⟩
  rintro s3 ⟨X3, h3, hB3, hX3, hS3, hSg3, hXc3, hx3, hnr3, hz3, hin3, hpu3, st3, iq3, sc3, na3, ei3, shd3, rv3⟩
  have hdA3 : L.mem s3 (scA hd) ≠ 0#u64 → L.mem s3 (scA hd) ∈ Ac := fun h0 => by
    rw [shd3] at h0 ⊢
    exact hB.sact hd hdT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [hds]; exact Or.inr (Or.inl rfl))))))))
      h0
  have htA3 : L.mem s3 (scA t) ≠ 0#u64 → L.mem s3 (scA t) ∈ Ac := fun h0 => by
    rw [sc3] at h0 ⊢; exact hc.ac h0
  have htq3 : (L.mem s3 (inqA t) &&& sched.Q_QUEUED) = 0#u64 := by rw [iq3]; exact hc.nq
  have htr3 : (L.mem s3 (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by rw [iq3]; exact hc.nr
  have hnb3 : ¬ Blocked (L.mem s3 (stA t)) := by rw [st3]; exact hc.nb
  have hnrp3 : L.mem s3 (stA t) ≠ sched.TS_BLOCKED_ON_REPLY := by rw [st3]; exact hc.nrp
  have hcold3 : L.mem s3 (stA t) ≠ sched.TS_BLOCKED_ON_REPLY ∧ L.mem s3 (stA t) ≠ sched.TS_BLOCKED_ON_RECV :=
    ⟨hnrp3, fun e' => hnb3 (Or.inr (Or.inl e'))⟩
  obtain ⟨dq, dr, da⟩ := blocked_out h3 hdT hnr3
  have hidle3 : L.idleW s3 ≠ t := by rw [ei3]; exact hidle
  have hnt3 : ∀ r ∈ Rp, L.mem s3 (rTcbA r) ≠ t := hX3.noref hta hcold3.1 hcold3.2
  have hnd3 : ∀ r ∈ Rp, L.mem s3 (rTcbA r) ≠ hd := by
    by_cases hm : hd ∈ X3
    · exact hX3.noref0 hdta (hz3 hm)
    · have e' := hin3 hm
      exact hX3.noref hdta (by rw [e']; exact inactive_ne.1) (by rw [e']; exact inactive_ne.2)
  refine WP.spec_bind (Pₘ := fun r : S × A => ∃ X4 : Set U64, (∃ Q4 R4, SchedQueuesInvX st T Cs Ω H X4 r.1 Q4 R4) ∧
      BoundInv st T Ac r.1 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ SCsOK st T Ω Sg Scs Z Ac r.1 ∧ SgOK st Ω Sg r.1 ∧
      ExcT X4 hd ∧ (hd ∈ X4 ∨ ¬ Blocked (L.mem r.1 (stA hd))) ∧ (∀ r' ∈ Rp, L.mem r.1 (rTcbA r') ≠ hd) ∧
      (L.mem r.1 (scA hd) ≠ 0#u64 → L.mem r.1 (scA hd) ∈ Ac)) ?_ ?_
  rotate_left
  · rintro ⟨s4, a1⟩ ⟨X4, ⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4, hXc4, hx4, hnr4, hdA4⟩
    try simp only [WP.uncurry'_pair]
    exact send_tail s4 a1 hd Q4 R4 h4 hB4 hX4 hS4 hSg4 hdT hXc4 hx4 hnr4 hdA4
  have Ppush : ∀ cd : Bool, (i != 0#u64) = true → ipc.reply_push st ar s3 a t hd i cd ⦃ r => ∃ X4 : Set U64,
      (∃ Q4 R4, SchedQueuesInvX st T Cs Ω H X4 r.1 Q4 R4) ∧
      BoundInv st T Ac r.1 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ SCsOK st T Ω Sg Scs Z Ac r.1 ∧ SgOK st Ω Sg r.1 ∧
      ExcT X4 hd ∧ (hd ∈ X4 ∨ ¬ Blocked (L.mem r.1 (stA hd))) ∧ (∀ r' ∈ Rp, L.mem r.1 (rTcbA r') ≠ hd) ∧
      (L.mem r.1 (scA hd) ≠ 0#u64 → L.mem r.1 (scA hd) ∈ Ac) ⦄ := by
    intro cd hi
    obtain ⟨hdX, hiR, hiz⟩ := hpu3 hi
    have hi0 : i ≠ 0#u64 := by simpa using hi
    refine WP.spec_mono (ipc.reply_push.ipc hA s3 a t hd i cd Q R h3
      (fun y hy => absurd (hXc3 y hy ▸ hy) hdX) (Or.inr hnb3) hB3 hX3 hS3 hSg3 ht htq3 htr3 na3 hidle3 hcold3
      hiR hi0 hiz hdT hdt dq dr da (by rw [ei3]; exact hdi) htA3 rv3) fun r hh => ?_
    obtain ⟨s4, a4⟩ := r
    simp only [WP.uncurry'_pair] at hh
    obtain ⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, st4, sc4⟩ := hh
    have e4 : L.mem s4 (stA hd) = sched.TS_INACTIVE := (st4 hd hdT hdt).trans (hin3 hdX)
    exact ⟨∅, ⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4, fun y hy => absurd hy (Set.notMem_empty _),
      Or.inr (by rw [e4]; exact not_blocked_inactive),
      hX4.noref hdta (by rw [e4]; exact inactive_ne.1) (by rw [e4]; exact inactive_ne.2), fun h0 => by
        rcases sc4 with e | e
        · rw [e] at h0 ⊢; exact hdA3 h0
        · rw [e] at h0 ⊢; exact htA3 h0⟩
  have Pinact : (do
      let s5 ← sched.set_thread_state st s3 t sched.TS_INACTIVE
      ok (s5, a)) ⦃ r => ∃ X4 : Set U64, (∃ Q4 R4, SchedQueuesInvX st T Cs Ω H X4 r.1 Q4 R4) ∧
      BoundInv st T Ac r.1 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ SCsOK st T Ω Sg Scs Z Ac r.1 ∧ SgOK st Ω Sg r.1 ∧
      ExcT X4 hd ∧ (hd ∈ X4 ∨ ¬ Blocked (L.mem r.1 (stA hd))) ∧ (∀ r' ∈ Rp, L.mem r.1 (rTcbA r') ≠ hd) ∧
      (L.mem r.1 (scA hd) ≠ 0#u64 → L.mem r.1 (scA hd) ∈ Ac) ⦄ := by
    refine WP.spec_bind (sts_all s3 t _ Q R h3 hB3 hX3 hS3 hSg3 ht not_blocked_inactive inactive_ne (Or.inr hnb3)
      hnt3 ⟨fun c hc' p hp hm => absurd hm (h3.notQ ht htq3 hc' hp), fun c hc' hm => absurd hm (h3.notR ht htr3 hc'),
        fun e' => absurd e' na3⟩) fun s4 hh => ?_
    obtain ⟨h4, hB4, hX4, hS4, hSg4, -, k4⟩ := hh
    refine (WP.spec_ok _).2 ⟨{y | y ∈ X3 ∧ y ≠ t}, ⟨Q, R, h4⟩, hB4, hX4, hS4, hSg4,
      fun y hy => hXc3 y hy.1, ?_, fun r hr => ?_, fun h0 => by rw [k4.scf hdT] at h0 ⊢; exact hdA3 h0⟩
    · rcases hx3 with hm | hnb
      · exact Or.inl ⟨hm, hdt⟩
      · exact Or.inr (by rw [k4.stf hdT hdt]; exact hnb)
    · rcases k4.rtcb r hr with e' | ⟨-, e'⟩
      · rw [e']; exact hnd3 r hr
      · rw [e']; exact fun e2 => hdta.ne0 (by rw [← e2]; rfl)
  have Pok : (ok (s3, a) : Result (S × A)) ⦃ r => ∃ X4 : Set U64, (∃ Q4 R4, SchedQueuesInvX st T Cs Ω H X4 r.1 Q4 R4) ∧
      BoundInv st T Ac r.1 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ SCsOK st T Ω Sg Scs Z Ac r.1 ∧ SgOK st Ω Sg r.1 ∧
      ExcT X4 hd ∧ (hd ∈ X4 ∨ ¬ Blocked (L.mem r.1 (stA hd))) ∧ (∀ r' ∈ Rp, L.mem r.1 (rTcbA r') ≠ hd) ∧
      (L.mem r.1 (scA hd) ≠ 0#u64 → L.mem r.1 (scA hd) ∈ Ac) ⦄ :=
    (WP.spec_ok _).2 ⟨X3, ⟨Q, R, h3⟩, hB3, hX3, hS3, hSg3, hXc3, hx3, hnd3, hdA3⟩
  have Pdon : can_donate = true → (do
      let i2 ← obj.Tcb.sc st hd s3
      if i2 = 0#u64 then do
          let i3 ← obj.Tcb.sc st t s3
          schedcontext.donate st ar s3 a i3 hd
        else ok (s3, a)) ⦃ r => ∃ X4 : Set U64, (∃ Q4 R4, SchedQueuesInvX st T Cs Ω H X4 r.1 Q4 R4) ∧
      BoundInv st T Ac r.1 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ SCsOK st T Ω Sg Scs Z Ac r.1 ∧ SgOK st Ω Sg r.1 ∧
      ExcT X4 hd ∧ (hd ∈ X4 ∨ ¬ Blocked (L.mem r.1 (stA hd))) ∧ (∀ r' ∈ Rp, L.mem r.1 (rTcbA r') ≠ hd) ∧
      (L.mem r.1 (scA hd) ≠ 0#u64 → L.mem r.1 (scA hd) ∈ Ac) ⦄ := by
    intro hcd
    step with obj.Tcb.sc.spec as ⟨i2, ei2⟩
    split
    · rename_i hi2
      step with obj.Tcb.sc.spec as ⟨i3, ei3'⟩
      refine WP.spec_mono (schedcontext.donate.ipc hA s3 a i3 hd t Q R h3 hB3 hX3 hS3 hSg3 ht ei3'.symm
        (by rw [ei3', sc3]; exact hdon hcd) ⟨htq3, htr3, na3⟩ hidle3 hdT (by rw [← ei2, hi2]) dq dr da hdt
        (by rw [ei3']; exact htA3 (by rw [sc3]; exact hdon hcd)) (by rw [ei3]; exact hdi) rv3)
        fun r hh => ?_
      obtain ⟨s4, a4⟩ := r
      simp only [WP.uncurry'_pair] at hh
      obtain ⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, st4, rp4, sd4⟩ := hh
      refine ⟨X3, ⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4, hXc3, ?_, ?_,
        fun _ => by rw [sd4, ei3']; exact htA3 (by rw [sc3]; exact hdon hcd)⟩
      · rcases hx3 with hm | hnb
        · exact Or.inl hm
        · exact Or.inr (by rw [st4 hd hdT]; exact hnb)
      · by_cases hm : hd ∈ X3
        · exact hX4.noref0 hdta (by rw [rp4 hd hdT]; exact hz3 hm)
        · have e' : L.mem s4 (stA hd) = sched.TS_INACTIVE := (st4 hd hdT).trans (hin3 hm)
          exact hX4.noref hdta (by rw [e']; exact inactive_ne.1) (by rw [e']; exact inactive_ne.2)
    · exact Pok
  split
  · repeat' split
    all_goals first
      | exact Pinact
      | exact Ppush _ (by assumption)
  · step with obj.Tcb.fault_type.any as ⟨i1, _⟩
    repeat' split
    all_goals first
      | exact Pinact
      | exact Ppush _ (by assumption)
      | exact Pdon (by assumption)
      | exact Pok

/-! ## `complete_signal` -/

theorem ntfn_idle_val0 : obj.NTFN_IDLE &&& 3#u64 = 0#u64 := by unfold obj.NTFN_IDLE; decide

/-- An active notification has no waiters; setting it idle keeps the
invariants. -/
theorem ntfn_idle_all {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {n : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hn : H n = some .ntfn) (hact : L.epState s n = 2#u64) :
    SchedQueuesInvX st T Cs Ω H X
        (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64))) Q R ∧
      BoundInv st T Ac (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64))) ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64))) ∧
      SCsOK st T Ω Sg Scs Z Ac (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64))) ∧
      SgOK st Ω Sg (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64))) ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
        L.mem (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64)))
          (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ a ∈ Ω, L.mem (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64))) a =
        L.mem s a) ∧
      L.actionW (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64))) = L.actionW s ∧
      L.idleW (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64))) = L.idleW s ∧
      L.curW (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64))) = L.curW s := by
  obtain ⟨E, EQ, hEW⟩ := h.eps
  have he : n ∈ E := (hEW.2.2.2.2.2.2.2.1 n).2 (Or.inr hn)
  obtain ⟨hE, -, hq⟩ := hEW.1 n he
  obtain ⟨k1, k2, -, -, k4, -⟩ := hEW.2.2.2.2.2
  have h0 : EQ n = [] := by
    by_contra hne
    obtain ⟨y, ys, hys⟩ := List.exists_cons_of_ne_nil hne
    have hy : y ∈ EQ n := by rw [hys]; exact List.mem_cons_self
    obtain ⟨hyX, hbe, hbl⟩ := hEW.2.2.2.1 n he y hy
    have hyT := hq.mem y hy
    obtain ⟨-, -, c3⟩ := k4 n he y hy
    rcases hbl with hb | hb | hb
    · have := k1 y hyT hyX (Or.inl hb); rw [hbe, hn] at this; cases this
    · have := k1 y hyT hyX (Or.inr hb); rw [hbe, hn] at this; cases this
    · have := c3 hb; rw [hact] at this; exact absurd this (by decide)
  obtain ⟨a1, a2⟩ := ep_aligned hE
  set w := (L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64) with hw0
  have hw : WritesIn st s (L.wr s (epTSA n) w) (EpFoot (EQ n) n) :=
    (writesIn_wr a2).mono fun b hb => Or.inr (Or.inr hb)
  have hhd : L.mem (L.wr s (epTSA n) w) (epHeadA n) = L.mem s (epHeadA n) :=
    L.mem_wr_ne a2 a1 (by rw [epTSA_val hE, epHeadA_val]; omega)
  have hq_eq : L.epQ (L.wr s (epTSA n) w) n = L.epQ s n := by
    simp only [LawfulStore.epQ, hhd]; rw [L.mem_wr_same a2, hw0, ts_end]
  have hst' : L.epState (L.wr s (epTSA n) w) n = 0#u64 := by
    simp only [LawfulStore.epState]; rw [L.mem_wr_same a2, hw0, ts_state, ntfn_idle_val0]
  have hq' : QueueRel (L.mem (L.wr s (epTSA n) w)) T .Ep (L.epQ (L.wr s (epTSA n) w) n) [] := by
    rw [hq_eq]; rw [h0] at hq
    exact ⟨hq.nodup, hq.mem, hq.head, hq.last, by simp⟩
  have hinv := inv_ep_step (X' := X) h hEW he hw hq' (fun hne => absurd rfl hne)
    (fun _ => ⟨fun _ => hst', fun _ => by rw [hst']; decide⟩) (fun y hy => absurd hy (by simp))
    (fun y hy => absurd hy (by rw [h0]; simp)) (fun y hy => hy) (fun y hy => Or.inl hy)
    (fun y hy => absurd hy (by simp))
  have hWT : ∀ y ∈ EQ n, y ∈ T := fun y hy => absurd hy (by rw [h0]; simp)
  obtain ⟨kf, kΩ, kn⟩ := epfoot_keep h hEW he hWT hw
  obtain ⟨b1, b2, b3, b4, ea, ec, ei⟩ := frame_bx h hB hX hS hSg kf kΩ (fun o h1 h2 => kn o h1 h2) hw.1
    (TmFr.of_epfoot h hEW he hWT hw hX.1 hSg.sub)
  exact ⟨hinv, b1, b2, b3, b4, kf, kΩ, ea, ei, ec⟩

/-- `donate` of an SC bound to no thread. -/
theorem schedcontext.donate.unbound {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {X : Set U64}
    (s : S) (a : A) (sc dst : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hdst : dst ∈ T)
    (hdq : (L.mem s (inqA dst) &&& sched.Q_QUEUED) = 0#u64) (hdr : (L.mem s (inqA dst) &&& sched.Q_RELEASE) = 0#u64)
    (hsc : sc ∈ Scs) (hsc0 : sc ≠ 0#u64) (htc0 : L.mem s (scTcbA sc) = 0#u64)
    (hcore : L.mem s (scCoreA sc) ∈ Cs) (hsA : Sch st s dst → sc ∈ Ac) (hd0 : L.mem s (scA dst) = 0#u64)
    (hdi : L.idleW s ≠ dst) (hrv : L.mem s (runVcpuA dst) = 0#u64) :
    schedcontext.donate st ar s a sc dst ⦃ s' _ => BlkOKX st T Cs Ω H Sg Rp Scs Nt Z Ac X s' ∧
      (∀ y ∈ T, L.mem s' (stA y) = L.mem s (stA y)) ∧ (∀ y ∈ T, L.mem s' (replyA y) = L.mem s (replyA y)) ∧
      TmFr st T Cs Nt s s' ∧
      (L.mem s' (scA dst) = sc ∧ L.mem s' (scTcbA sc) = dst ∧ L.actionW s' = L.actionW s) ⦄ := by
  have hO := hX.1
  have hnb : ∀ y ∈ T, L.mem s (scA y) ≠ sc := fun y hy e => by
    obtain ⟨-, h2, -⟩ := hX.2.2.bound y hy (by rw [e]; exact hsc0)
    rw [e, htc0] at h2; exact (h.tcbs y hy).ne0 (by rw [← h2]; rfl)
  have hdisj : sc ≠ L.cscW s → ∀ b, InSC sc (Z sc) b → Outside b (L.cscW s) (Z (L.cscW s)) := by
    intro hne b hb
    have := hO.scDisj sc hsc _ hX.2.2.cur hne
    unfold Outside; unfold InSC at hb; omega
  unfold schedcontext.donate
  step with obj.Sc.tcb.spec as ⟨i, ei⟩
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · try simp only [Aeneas.Std.bind_ok]
    exact donate_tail hA s a sc dst Q R h hB hX.x0 hX.2.2.tsc.x hX.2.2.aff hd0 hS hSg hdst hdq hdr hsc hsc0 hnb hcore hdisj hsA hdi hrv
  · rename_i hb; exfalso; exact hb (by rw [eb, ei, htc0]; rfl)

/-- seL4 `maybeDonateSchedContext`: an unbound notification SC goes to the
unbound receiver, which resumes. -/
theorem notification.maybe_donate_sched_context.ipc {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (t n : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T)
    (htq : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64) (htr : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64)
    (hta' : L.actionW s ≠ t) (hti : L.idleW s ≠ t)
    (hns : L.mem s (ntfnScA n) ≠ 0#u64 → L.mem s (scTcbA (L.mem s (ntfnScA n))) = 0#u64 →
      L.mem s (scA t) = 0#u64 → L.mem s (ntfnScA n) ∈ Scs ∧
        L.mem s (scCoreA (L.mem s (ntfnScA n))) ∈ Cs ∧ (Sch st s t → L.mem s (ntfnScA n) ∈ Ac))
    (hrv : L.mem s (runVcpuA t) = 0#u64) :
    notification.maybe_donate_sched_context st ar s a t n ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  have ok0 : (ok (s, a) : Result (S × A)) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ :=
    (WP.spec_ok _).2 ⟨⟨Q, R, h⟩, hB, hX, hS, hSg⟩
  unfold notification.maybe_donate_sched_context
  step with obj.Tcb.sc.spec as ⟨i, ei⟩
  split
  · rename_i hi
    step with obj.Ntfn.sc.val as ⟨i1, ei1⟩
    step with obj.Sc.is_null.spec as ⟨b, eb⟩
    split
    · exact ok0
    rename_i hb
    have hi10 : i1 ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    step with obj.Sc.tcb.spec as ⟨i2, ei2⟩
    split
    · rename_i hi2
      have htc0 : L.mem s (scTcbA i1) = 0#u64 := by rw [← ei2, hi2]
      obtain ⟨hS1, hcore1, hsA1⟩ := hns (by rw [← ei1]; exact hi10) (by rw [← ei1]; exact htc0) (by rw [← ei, hi])
      rw [← ei1] at hS1 hcore1 hsA1
      refine WP.spec_bind (schedcontext.donate.unbound hA s a i1 t Q R h hB hX hS hSg ht htq htr hS1 hi10 htc0
        hcore1 hsA1 (by rw [← ei, hi]) hti hrv) ?_
      rintro ⟨s4, a4⟩ ⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, -, -, -, sc4, tc4, ea4⟩
      try simp only [WP.uncurry'_pair]
      refine WP.spec_mono (schedcontext.resume.all hA s4 a4 i1 Q4 R4 h4 hB4 hX4 hSg4 hS4 fun _ _ => ?_) ?_
      · obtain ⟨-, -, hc4⟩ := hX4.2.2.bound t ht (by rw [sc4]; exact hi10)
        rw [sc4] at hc4
        rw [tc4]
        exact ⟨ht, h4.omega _ ((objs_omega hX4.1 hSg4.sub).2 i1 hS1).2.1, hc4, by rw [ea4]; exact hta'⟩
      · rintro ⟨s5, a5⟩ ⟨Q5, R5, h5, hB5, hX5, hSg5, f5⟩
        exact ⟨⟨Q5, R5, h5⟩, hB5, hX5, hS4.fr f5, hSg5⟩
    · exact ok0
  · exact ok0

/-- A badge-register write keeps the invariants. -/
theorem badge_all {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t v : U64}
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T) :
    SchedQueuesInv st T Cs Ω H (L.wr s (core.num.U64.wrapping_add t 256#u64) v) Q R ∧
      BoundInv st T Ac (L.wr s (core.num.U64.wrapping_add t 256#u64) v) ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z (L.wr s (core.num.U64.wrapping_add t 256#u64) v) ∧
      SCsOK st T Ω Sg Scs Z Ac (L.wr s (core.num.U64.wrapping_add t 256#u64) v) ∧
      SgOK st Ω Sg (L.wr s (core.num.U64.wrapping_add t 256#u64) v) := by
  obtain ⟨b1, b2⟩ := bx_field (K := 256#u64) (v := v) h hB hX hSg.sub ht (by simp) (by simp) (by simp) (by simp)
  exact ⟨inv_wr_field h ht (by simp) (by simp) (by simp), b1, b2,
    SCsOK.field h hS hX ht (by simp) (by simp) (by simp),
    ⟨hSg.sub, fun b hb => by rw [L.ksb_wr]; exact hSg.ks b hb, fun o h1 h2 => by rw [L.ksb_wr]; exact hSg.ksΩ o h1 h2⟩⟩

theorem ntfn_active_ne {i : U64} (hi : ¬ (i != obj.NTFN_ACTIVE) = true) : i = 2#u64 := by
  simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hi
  rw [hi]; unfold obj.NTFN_ACTIVE; rfl

/-- seL4 `completeSignal` for a receiver in no ready or release queue and not
the switch-to candidate, on a notification whose SC word is one of the other
objects' words and holds an SC object (or nothing). a64: named premise **[J] `hRV`** (`RunVcpuInv`), with the
receiver not in `TS_RUNNING_VM` (`hvm`): the receiver, to which `maybe_donate_sched_context` may donate the
notification's SC, runs no VCPU. -/
theorem notification.complete_signal.ipc {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (n t : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T)
    (htq : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64) (htr : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64)
    (hta' : L.actionW s ≠ t) (hti : L.idleW s ≠ t) (hn : H n = some .ntfn) (hnΩ : ntfnScA n ∈ Ω)
    (hns : L.mem s (ntfnScA n) ≠ 0#u64 → L.mem s (ntfnScA n) ∈ Scs ∧
      L.mem s (scCoreA (L.mem s (ntfnScA n))) ∈ Cs)
    (hdA : L.mem s (ntfnScA n) ≠ 0#u64 → L.mem s (scA t) = 0#u64 → Sch st s t → L.mem s (ntfnScA n) ∈ Ac)
    (hRV : RunVcpuInv st T s) (hvm : L.mem s (stA t) ≠ sched.TS_RUNNING_VM) :
    notification.complete_signal st ar s a n t ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  have hT := h.tcbs
  have hta := hT t ht
  have hN := h.nodes _ h.cur
  have ok0 : (ok (s, a) : Result (S × A)) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ :=
    (WP.spec_ok _).2 ⟨⟨Q, R, h⟩, hB, hX, hS, hSg⟩
  obtain ⟨E, EQ, hEW⟩ := h.eps
  have he : n ∈ E := (hEW.2.2.2.2.2.2.2.1 n).2 (Or.inr hn)
  obtain ⟨hE, -, -⟩ := hEW.1 n he
  unfold notification.complete_signal
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · exact ok0
  step with obj.Ntfn.state.spec as ⟨i, ei⟩
  split
  · exact ok0
  rename_i hia
  have hact : L.epState s n = 2#u64 := by rw [← ei]; exact ntfn_active_ne hia
  step with obj.Ntfn.badge.any as ⟨b1, _⟩
  refine WP.spec_bind (obj.Tcb.set_reg.badge s t b1 hta) fun s1 e1 => ?_
  subst e1
  obtain ⟨h1, hB1, hX1, hS1, hSg1⟩ := badge_all (v := b1) h hB hX hS hSg ht
  have ha1 : Aligned (core.num.U64.wrapping_add t 256#u64) := field_aligned hta (by simp) (by simp)
  have f1 : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (y = t → K.val ≠ 256) →
      L.mem (L.wr s (core.num.U64.wrapping_add t 256#u64) b1) (core.num.U64.wrapping_add y K) =
        L.mem s (core.num.U64.wrapping_add y K) := fun y hy K hK hK8 hne =>
    L.mem_wr_ne ha1 (field_aligned (hT y hy) hK hK8)
      (fun e => field_ne hta (hT y hy) (by simp) hK (fun e' => by subst e'; exact fun h' => hne rfl h'.symm)
        (UScalar.eq_of_val_eq e))
  have o1 : ∀ x ∈ Ω, L.mem (L.wr s (core.num.U64.wrapping_add t 256#u64) b1) x = L.mem s x := fun x hx =>
    L.mem_wr_ne ha1 (h.omega x hx).1 (fun e => out_ne_field (h.omega x hx) ht hta (by simp) e)
  have ts1 : L.mem (L.wr s (core.num.U64.wrapping_add t 256#u64) b1) (epTSA n) = L.mem s (epTSA n) :=
    L.mem_wr_ne ha1 (ep_aligned hE).2 (by
      rw [field_val hta (by simp), epTSA_val hE]; have := hE.disj t ht; simp; omega)
  have hact1 : L.epState (L.wr s (core.num.U64.wrapping_add t 256#u64) b1) n = 2#u64 := by
    simp only [LawfulStore.epState]; rw [ts1]; exact hact
  have ei1 : L.idleW (L.wr s (core.num.U64.wrapping_add t 256#u64) b1) = L.idleW s := by
    unfold LawfulStore.idleW; rw [LawfulStore.cpu_wr, nodeAt_wr]
    exact L.mem_wr_ne ha1 (nodeAt_aligned hN (by rw [idle8]; omega) (by rw [idle8]))
      (fun e => node_ne_field (K := 256#u64) hN (by rw [idle8]; omega) ht hta (by simp) (UScalar.eq_of_val_eq e).symm)
  set s1 := L.wr s (core.num.U64.wrapping_add t 256#u64) b1 with hs1
  refine WP.spec_bind (obj.Ntfn.set_state.val s1 n _) fun s2 e2 => ?_
  subst e2
  obtain ⟨h2, hB2, hX2, hS2, hSg2, f2, o2, ea2, ei2, ec2⟩ := ntfn_idle_all h1 hB1 hX1 hS1 hSg1 hn hact1
  set s2 := L.wr s1 (epTSA n) ((L.mem s1 (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64)) with hs2
  have F : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 → (y = t → K.val ≠ 256) →
      L.mem s2 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K hK hK8 h1' h2' h3' => (f2 y hy K hK hK8 h1' h2').trans (f1 y hy K hK hK8 h3')
  have O : ∀ x ∈ Ω, L.mem s2 x = L.mem s x := fun x hx => (o2 x hx).trans (o1 x hx)
  have iq2 : L.mem s2 (inqA t) = L.mem s (inqA t) := by
    rw [inqA_eq]; exact F t ht _ (by simp) (by simp) (by simp) (by simp) (fun _ => by simp)
  have sc2 : L.mem s2 (scA t) = L.mem s (scA t) := by
    rw [scA_eq]; exact F t ht _ (by simp) (by simp) (by simp) (by simp) (fun _ => by simp)
  have ea2' : L.actionW s2 = L.actionW s := by
    rw [ea2, hs1, act_wr_field hN ht hta rfl (by simp) (by simp)]
  have hc2 : L.mem s2 (ntfnScA n) = L.mem s (ntfnScA n) := O _ hnΩ
  have rv2 : L.mem s2 (runVcpuA t) = 0#u64 :=
    (F t ht 3672#u64 (by simp) (by simp) (by simp) (by simp) (fun _ => by simp)).trans (hRV.zero ht hvm)
  refine WP.spec_bind (notification.maybe_donate_sched_context.ipc hA s2 a t n Q R h2 hB2 hX2 hS2 hSg2 ht
    (by rw [iq2]; exact htq) (by rw [iq2]; exact htr) (by rw [ea2']; exact hta') (by rw [ei2, ei1]; exact hti)
    (fun h0 _ _ => ?_) rv2) ?_
  · rw [hc2] at h0 ⊢
    obtain ⟨c1, c3⟩ := hns h0
    obtain ⟨-, hcΩ⟩ := objs_omega hX.1 hSg.sub
    refine ⟨c1, by rw [O _ (hcΩ _ c1).2.1]; exact c3, fun hS2t => hdA h0 (by rw [← sc2]; assumption) ?_⟩
    have f21 : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
        L.mem s2 (core.num.U64.wrapping_add t K) = L.mem s1 (core.num.U64.wrapping_add t K) :=
      fun K a1 a2 a3 a4 => f2 t ht K a1 a2 a3 a4
    have hS1t : Sch st s1 t := Sch.of_eq
      (fun hf => by rwa [inqA_eq, f21 _ (by simp) (by simp) (by simp) (by simp)] at hf)
      (fun hf => by rwa [inqA_eq, f21 _ (by simp) (by simp) (by simp) (by simp)] at hf)
      ea2 ei2 ec2 (by rw [stA_eq]; exact f21 _ (by simp) (by simp) (by simp) (by simp)) hS2t
    exact Sch.wr_field h ht (by simp) (by simp) (by simp) ht hS1t
  rintro ⟨s3, a1⟩ ⟨⟨Q3, R3, h3⟩, hB3, hX3, hS3, hSg3⟩
  try simp only [WP.uncurry'_pair]
  have ok3 : (ok (s3, a1) : Result (S × A)) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ :=
    (WP.spec_ok _).2 ⟨⟨Q3, R3, h3⟩, hB3, hX3, hS3, hSg3⟩
  step with obj.Tcb.sc.spec as ⟨i1, ei1⟩
  step with sporadic.sc_sporadic.spec as ⟨b2, eb2⟩
  split
  · rename_i hb2
    step with obj.Ntfn.sc.val as ⟨i2, _⟩
    split
    · step with sched.cur_sc.spec as ⟨c4, _⟩
      step with sc_ne.spec as ⟨b3⟩
      split
      · have hi1S : i1 ∈ Scs := (hX3.2.2.bound t ht (by rw [← ei1]; exact (eb2 hb2).1)).1 |> fun h => by
          rw [← ei1] at h; exact h
        refine WP.spec_bind (sporadic.unblock_check.all s3 t i1 h3 hB3 hX3 hS3 hSg3 ht ei1 (eb2 hb2).1
          (hS3.spor i1 hi1S (eb2 hb2).2)) fun s5 hh => ?_
        obtain ⟨h5, hB5, hX5, hS5, hSg5, -⟩ := hh
        exact (WP.spec_ok _).2 ⟨⟨Q3, R3, h5⟩, hB5, hX5, hS5, hSg5⟩
      · exact ok3
    · exact ok3
  · exact ok3

/-! ## `receive_ipc` -/

/-- An active bound notification is a heap notification whose `SC` word is
one of the other objects' words and holds an SC object, if any. -/
def BoundNtfnOK (st : machine.Store S) [L : LawfulStore st] (Cs Ω : Set U64) (H : Heap) (Sg Scs : Set U64)
    (Z : U64 → Nat) (n : U64) (s : S) : Prop :=
  H n = some .ntfn ∧ ntfnScA n ∈ Ω ∧ (L.mem s (ntfnScA n) ≠ 0#u64 → L.mem s (ntfnScA n) ∈ Scs ∧
    L.mem s (scCoreA (L.mem s (ntfnScA n))) ∈ Cs)

/-- A bound notification is well typed (from `ScExtra.bnd`, `ScExtra.nsc`,
`SCsOK.all` and `ScExtra.core`), given that `Nt` are heap notifications. -/
theorem BoundNtfnOK.of_inv {s : S} {t : U64} (hNt : ∀ n ∈ Nt, H n = some .ntfn) (ht : t ∈ T)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s)
    (hn0 : L.mem s (boundA t) ≠ 0#u64) : BoundNtfnOK st Cs Ω H Sg Scs Z (L.mem s (boundA t)) s := by
  have hn := hX.2.2.bnd t ht hn0
  refine ⟨hNt _ hn, hSg.sub _ (hX.1.ntW _ hn), fun hc0 => ?_⟩
  obtain ⟨hc, -⟩ := hX.2.2.nsc _ hn hc0
  exact ⟨hc, hX.2.2.core _ hc⟩

/-- a64: `endpoint.receive_ipc.inv` (QueueBlock) with the `complete_signal` continuation also told that its state
is a `RecvPre` state (the state right after `take_reply`), as the `receive_from_sender` one is. The proof is
QueueBlock's, verbatim. -/
theorem endpoint.receive_ipc.inv_rp {A : Type _} (ar : machine.Arch A) (s : S) (a : A) (t : U64)
    (cap : capability.Cap) (blocking : Bool) (reply_cap : capability.Cap) (e : U64)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hc : CanBlock st T Ac s t)
    (hptr : capability.Cap.ptr cap = ok e) (hH : H e = some .ep)
    (hcap : ∀ p g, reply_cap = .Reply p g → p ∈ Rp)
    (hcs : ∀ (s1 : S) (a1 : A) (n : U64), BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1 → CanBlock st T Ac s1 t →
      n = L.mem s1 (boundA t) → n ≠ 0#u64 → L.epState s1 n = 2#u64 →
      RecvPre st ar s a t reply_cap s1 →
      notification.complete_signal st ar s1 a1 n t ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄)
    (hrfs : ∀ (s2 : S) (a2 : A) (r : U64), BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s2 → CanBlock st T Ac s2 t →
      (r ≠ 0#u64 → r ∈ Rp ∧ (L.mem s2 (rTcbA r) = 0#u64 ∨ L.mem s2 (rTcbA r) = t)) →
      L.ksb s2 = L.ksb s → ¬ BlockedR (L.mem s2 (stA (L.idleW s2))) →
      L.epState s2 e ≠ 0#u64 → L.epState s2 e ≠ 2#u64 → RecvPre st ar s a t reply_cap s2 →
      endpoint.receive_from_sender st ar s2 a2 t e r ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄) :
    endpoint.receive_ipc st ar s a t cap blocking reply_cap ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  unfold endpoint.receive_ipc
  rw [hptr]
  simp only [Aeneas.Std.bind_ok]
  refine WP.spec_bind (spec_eq' (endpoint.take_reply.inv ar s a t reply_cap Q R h hB hX hS hSg hc hcap)) ?_
  rintro ⟨reply, s1, a1⟩ ⟨eq1, h1, hB1, hX1, hS1, hSg1, hc1, hi1, hr1, kb1, ib1⟩
  have hidle := hc.ni
  have ib1 := ib1 hB.idleNB
  try simp only [WP.uncurry'_pair]
  have ht := hc.mem
  -- the end on the endpoint
  have tail : ∀ (s2 : S) (a2 : A) (Q2 : U64 → U64 → List U64) (R2 : U64 → List U64),
      SchedQueuesInv st T Cs Ω H s2 Q2 R2 → BoundInv st T Ac s2 → XInv st T Cs Ω Sg Rp Scs Nt Z s2 →
      SCsOK st T Ω Sg Scs Z Ac s2 → SgOK st Ω Sg s2 → CanBlock st T Ac s2 t →
      (reply ≠ 0#u64 → reply ∈ Rp ∧ (L.mem s2 (rTcbA reply) = 0#u64 ∨ L.mem s2 (rTcbA reply) = t)) →
      L.ksb s2 = L.ksb s → ¬ BlockedR (L.mem s2 (stA (L.idleW s2))) →
      (s2 = s1 ∨ ∃ i, notification.maybe_return_sched_context st s1 i t = ok s2) →
      (do
        let st0 ← obj.Ep.state st e s2
        if st0 = obj.EP_IDLE then do
          let s3 ← endpoint.wait_for_sender st s2 t e blocking reply
          ok (s3, a2)
        else if st0 = obj.EP_RECV then do
          let s3 ← endpoint.wait_for_sender st s2 t e blocking reply
          ok (s3, a2)
        else endpoint.receive_from_sender st ar s2 a2 t e reply) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
    intro s2 a2 Q2 R2 h2 hB2 hX2 hS2 hSg2 hc2 hr2 kb2 ib2 hp2
    step with obj.Ep.state.spec as ⟨v, hv⟩
    split
    · rename_i h0
      refine WP.spec_bind (endpoint.wait_for_sender.inv s2 t e blocking reply Q2 R2 h2 hB2 hX2 hS2 hSg2 ht
        (fun _ => hc2) hH (Or.inl (by rw [← hv, h0, ep_idle_val])) hr2) fun s3 hh => ?_
      exact (WP.spec_ok _).2 ⟨⟨Q2, R2, hh.1⟩, hh.2.1, hh.2.2.1, hh.2.2.2.1, hh.2.2.2.2⟩
    · split
      · rename_i _ h0
        refine WP.spec_bind (endpoint.wait_for_sender.inv s2 t e blocking reply Q2 R2 h2 hB2 hX2 hS2 hSg2 ht
          (fun _ => hc2) hH (Or.inr (by rw [← hv, h0, ep_recv_val'])) hr2) fun s3 hh => ?_
        exact (WP.spec_ok _).2 ⟨⟨Q2, R2, hh.1⟩, hh.2.1, hh.2.2.1, hh.2.2.2.1, hh.2.2.2.2⟩
      · rename_i h01 h02
        exact hrfs s2 a2 reply ⟨⟨Q2, R2, h2⟩, hB2, hX2, hS2, hSg2⟩ hc2 hr2 kb2 ib2
          (fun e0 => h01 (by rw [hv, e0, ep_idle_val])) (fun e0 => h02 (by rw [hv, e0, ep_recv_val']))
          ⟨reply, s1, a1, eq1, hp2⟩
  -- the bound notification's SC
  have mid : ∀ (i : U64), (if blocking then notification.maybe_return_sched_context st s1 i t else ok s1)
      ⦃ s2 => ∃ Q2 R2, SchedQueuesInv st T Cs Ω H s2 Q2 R2 ∧ BoundInv st T Ac s2 ∧
        XInv st T Cs Ω Sg Rp Scs Nt Z s2 ∧ SCsOK st T Ω Sg Scs Z Ac s2 ∧ SgOK st Ω Sg s2 ∧ CanBlock st T Ac s2 t ∧
        (reply ≠ 0#u64 → reply ∈ Rp ∧ (L.mem s2 (rTcbA reply) = 0#u64 ∨ L.mem s2 (rTcbA reply) = t)) ∧
        L.ksb s2 = L.ksb s ∧ ¬ BlockedR (L.mem s2 (stA (L.idleW s2))) ∧
        (s2 = s1 ∨ ∃ i, notification.maybe_return_sched_context st s1 i t = ok s2) ⦄ := by
    intro i
    split
    · refine WP.spec_mono (spec_eq' (notification.maybe_return_sched_context.inv s1 i t Q R h1 hB1 hX1 hS1 hSg1 ht
        ⟨hc1.nq, hc1.nr, hc1.na⟩ (by rw [hi1]; exact hidle))) fun s2 ⟨eq2, hh⟩ => ?_
      obtain ⟨⟨Q2, R2, h2⟩, hB2, hX2, hS2, hSg2, q2, st2, na2, ii2, rt2, sa2, ks2, sc2⟩ := hh
      refine ⟨Q2, R2, h2, hB2, hX2, hS2, hSg2, hc1.mrsc q2 st2 na2 ii2 sc2, fun hn => ?_, ks2.trans kb1, ?_,
        Or.inr ⟨i, eq2⟩⟩
      · obtain ⟨r1, r2⟩ := hr1 hn
        rw [rt2 _ r1]; exact ⟨r1, r2⟩
      · rw [ii2, sa2 (L.idleW s1) h1.idleT]; exact ib1
    · exact (WP.spec_ok _).2 ⟨Q, R, h1, hB1, hX1, hS1, hSg1, hc1, hr1, kb1, ib1, Or.inl rfl⟩
  step with obj.Tcb.bound_ntfn.val as ⟨i, ei⟩
  split
  · rename_i hi0
    step with obj.Ntfn.state.spec as ⟨v1, hv1⟩
    split
    · rename_i hva
      exact hcs s1 a1 i ⟨⟨Q, R, h1⟩, hB1, hX1, hS1, hSg1⟩ hc1 ei (by simpa using hi0)
        (by rw [← hv1, hva]; unfold obj.NTFN_ACTIVE; rfl) ⟨reply, s1, a1, eq1, Or.inl rfl⟩
    · refine WP.spec_bind (mid i) ?_
      rintro s2 ⟨Q2, R2, h2, hB2, hX2, hS2, hSg2, hc2, hr2, kb2, ib2, p2⟩
      exact tail s2 a1 Q2 R2 h2 hB2 hX2 hS2 hSg2 hc2 hr2 kb2 ib2 p2
  · try simp only [Aeneas.Std.bind_ok]
    exact tail s1 a1 Q R h1 hB1 hX1 hS1 hSg1 hc1 hr1 kb1 ib1 (Or.inl rfl)


/-- seL4 `receiveIPC`, all of it: the reply bookkeeping (`take_reply`), the
active bound notification (`complete_signal`), the bound notification's SC
going back (`maybe_return_sched_context`), blocking or polling on an idle or
receiving endpoint, and receiving from a sending endpoint.  Besides the
invariants, only caller-level facts: `t` can block, the cap names a heap
endpoint, a reply cap names a reply object, and `Nt` are heap notifications
(true of the instantiation `Nt := H.ntfns`). a64: named premise **[J] `hRV`**: `RunVcpuInv` at the states
`receive_ipc` reaches before its end on the endpoint (`RecvPre`, after `take_reply` and
`maybe_return_sched_context`), and the caller-level fact `hvm` that the receiver is not in `TS_RUNNING_VM`
(`take_reply` and `maybe_return_sched_context` keep its state, `RecvPre.stt`): the SC donations of a call
(`receive_from_sender`) and of the bound notification (`complete_signal`) go to the receiver, which then runs
no VCPU. Proved through `endpoint.receive_ipc.inv_rp`. -/
theorem endpoint.receive_ipc.ipc {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {U : Set U64}
    {G : S → Prop} (hxf : XferOK st ar T Cs Ω H Sg Rp Scs Nt Z U G) (s : S) (a : A) (t : U64)
    (cap : capability.Cap) (blocking : Bool)
    (reply_cap : capability.Cap) (e : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (hG : ∀ s2 s1, RecvPre st ar s a t reply_cap s2 → H e = some .ep →
      (L.epState s2 e = 1#u64 ∨ L.epState s2 e = 2#u64) → endpoint.ep_dequeue st s2 e (L.epQ s2 e).head = ok s1 → G s1)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hU : UserOK st T Cs Ω H U s)
    (hc : CanBlock st T Ac s t)
    (hptr : capability.Cap.ptr cap = ok e) (hH : H e = some .ep)
    (hcap : ∀ p g, reply_cap = .Reply p g → p ∈ Rp)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (hRV : ∀ s2, RecvPre st ar s a t reply_cap s2 → RunVcpuInv st T s2)
    (hvm : L.mem s (stA t) ≠ sched.TS_RUNNING_VM) :
    endpoint.receive_ipc st ar s a t cap blocking reply_cap ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ :=
  endpoint.receive_ipc.inv_rp ar s a t cap blocking reply_cap e Q R h hB hX hS hSg hc hptr hH hcap
    (fun s1 a1 n hok hc1 hn hn0 hst hp1 => by
      obtain ⟨⟨Q1, R1, h1⟩, hB1, hX1, hS1, hSg1⟩ := hok
      subst hn
      obtain ⟨hn1, hn2, hn3⟩ := BoundNtfnOK.of_inv hNt hc1.mem hX1 hS1 hSg1 hn0
      refine notification.complete_signal.ipc hA s1 a1 _ t Q1 R1 h1 hB1 hX1 hS1 hSg1 hc1.mem hc1.nq hc1.nr hc1.na
        hc1.ni hn1 hn2 hn3 (fun _ h0 hS => ?_) (hRV s1 hp1)
        (by rw [RecvPre.stt Q R h hB hX hS hSg hc hcap hp1]; exact hvm)
      exfalso
      rcases hS with e | e | e | e | ⟨e1, e2⟩ | e
      · exact e hc1.nq
      · exact e hc1.nr
      · exact hc1.na e
      · exact hc1.ni e
      · exact hB1.resume e1 (by rw [e2]; exact h0)
      · rcases e with e | e
        · exact hc1.nb e
        · exact hc1.nrp e)
    (fun s2 a2 r hok hc2 hr kb ib hs0 hs2 hp => by
      obtain ⟨⟨Q2, R2, h2⟩, hB2, hX2, hS2, hSg2⟩ := hok
      exact endpoint.receive_from_sender.ipc hA hxf s2 a2 t e r Q2 R2 (fun s1 => hG s2 s1 hp) h2 hB2 hX2 hS2 hSg2 (hU.ksb kb) hc2 hH
        ⟨hs0, hs2⟩ hr (hRV s2 hp) (by rw [RecvPre.stt Q R h hB hX hS hSg hc hcap hp]; exact hvm))

end

end Fl4ProofsA64.P1
