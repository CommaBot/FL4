/-
P1: the non-blocking ends of IPC: the message transfer (`do_ipc_transfer`,
taken as an opaque write to the threads' user context and to user memory),
`reply_push` with SC donation, `receive_from_sender`, the `send_ipc` branch
on a receiving endpoint and `complete_signal`; then the whole `send_ipc` and
`receive_ipc`.
-/
import Fl4Proofs.P1.QueueBlock
import Fl4Proofs.P1.QueueBudget2
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

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
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z s) (hSg : SgOK st Ω Sg s) (hU : UserOK st T Cs Ω H U s)
    (hw : WritesIn st s s' (XferFoot T U)) :
    SchedQueuesInvX st T Cs Ω H X s' Q R ∧ BoundInv st T s' ∧ XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧
      SCsOK st T Ω Sg Scs Z s' ∧ SgOK st Ω Sg s' ∧ L.actionW s' = L.actionW s ∧ L.curW s' = L.curW s ∧
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
    hB.mk' scf (fun y hy hf => Or.inl (by rw [← iqf y hy]; exact hf))
      (fun y hy hf => Or.inr (Or.inl (by rw [← iqf y hy]; exact hf)))
      (fun haT => by rw [ea] at haT ⊢; exact ⟨haT, hB.act haT⟩) (by rw [ei]; exact ⟨h.idleT, hB.idle⟩)
      (fun h0 => by rw [ea] at h0; rw [ec]; exact ⟨h.curT, hB.resume h0⟩) (hB.nb ei (stf (L.idleW s) h.idleT)),
    hX.keep (fun r hr => ⟨f2 _ (hrΩ r hr).1, f2 _ (hrΩ r hr).2.1, f2 _ (hrΩ r hr).2.2⟩)
      (fun c hc => ⟨f2 _ (hcΩ c hc).1, f2 _ (hcΩ c hc).2.1⟩) scf rpf stf (by rw [ecs]; exact hX.2.2.cur)
      (fun c hc => f2 _ (hSg.sub _ (hX.1.repW c hc)))
      (fun y hy => F y hy _ (by simp) (by simp) (by simp)) (fun n hn => f2 _ (hSg.sub _ (hX.1.ntW n hn)))
      (hX.tn ⟨hw.1, fun y hy K a b c => f1 y hy K (by omega) (by omega) c, fun c hc o ho => f3 c hc o (by omega) (by omega),
        fun n hn => f2 _ (hSg.sub _ (hX.1.ntB n hn).2)⟩) (fun c hc => f2 _ (hSg.sub _ (hX.1.snW c hc)))
      (fun y hy => F y hy _ (by simp) (by simp) (by simp)) (fun c hc => f2 _ (hSg.sub _ (hX.1.syW c hc))),
    SCsOK.keep hS hX hw.1 scf ecs (fun c hc => ⟨f2 _ (hcΩ c hc).2.2.1, f2 _ (hcΩ c hc).2.2.2.1,
      f2 _ (hcΩ c hc).2.2.2.2⟩),
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
    (hnode : ∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → (o.val = 64 ∨ o.val = 72 ∨ 128 ≤ o.val) →
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
  have hn : ∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → (o.val = 64 ∨ o.val = 72 ∨ 128 ≤ o.val) →
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

/-- A write to the current core's `IPI_PENDING`. -/
theorem ipi_all {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {v : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z s) (hSg : SgOK st Ω Sg s) :
    SchedQueuesInvX st T Cs Ω H X (L.wr s (L.nodeAt s (L.cpu s) layout.node.IPI_PENDING) v) Q R ∧
      BoundInv st T (L.wr s (L.nodeAt s (L.cpu s) layout.node.IPI_PENDING) v) ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z (L.wr s (L.nodeAt s (L.cpu s) layout.node.IPI_PENDING) v) ∧
      SCsOK st T Ω Sg Scs Z (L.wr s (L.nodeAt s (L.cpu s) layout.node.IPI_PENDING) v) ∧
      SgOK st Ω Sg (L.wr s (L.nodeAt s (L.cpu s) layout.node.IPI_PENDING) v) ∧
      L.actionW (L.wr s (L.nodeAt s (L.cpu s) layout.node.IPI_PENDING) v) = L.actionW s ∧
      L.curW (L.wr s (L.nodeAt s (L.cpu s) layout.node.IPI_PENDING) v) = L.curW s ∧
      L.idleW (L.wr s (L.nodeAt s (L.cpu s) layout.node.IPI_PENDING) v) = L.idleW s ∧
      L.cscW (L.wr s (L.nodeAt s (L.cpu s) layout.node.IPI_PENDING) v) = L.cscW s ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        L.mem (L.wr s (L.nodeAt s (L.cpu s) layout.node.IPI_PENDING) v) (core.num.U64.wrapping_add y K) =
          L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ a ∈ Ω, L.mem (L.wr s (L.nodeAt s (L.cpu s) layout.node.IPI_PENDING) v) a = L.mem s a) := by
  have hN' := h.nodes _ h.cur
  have ip := ipi_val
  obtain ⟨h1, hB1, hX1, hSg1, ea, ec, ecs, -⟩ := node_bx (v := v) h hB hX hSg (o := layout.node.IPI_PENDING)
    (by rw [ip]; simp [LowFree]) (by rw [ip]; omega) (by rw [ip]; omega)
  have ha : Aligned (L.nodeAt s (L.cpu s) layout.node.IPI_PENDING) := nodeAt_aligned hN' (by rw [ip]; omega) (by rw [ip])
  obtain ⟨-, hcΩ⟩ := objs_omega hX.1 hS.sub
  refine ⟨h1, hB1, hX1, SCsOK.wr h hS hX ha (fun y hy e => ?_) ?_ (fun c hc => ?_), hSg1, ea, ec, ?_, ecs,
    fun y hy K hK hK8 => field_wr_node h h.cur (by rw [ip]; omega) (by rw [ip]) hy hK hK8, fun a ha' => ?_⟩
  · rw [scA_eq] at e
    exact node_ne_field hN' (by rw [ip]; omega) hy (h.tcbs y hy) (by simp) (UScalar.eq_of_val_eq e)
  · intro e
    simp only [LawfulStore.nodeA] at e
    rw [nodeAt_val hN' (by rw [ip]; omega), nodeAt_val hN' (by simp [layout.node.CUR_SC]), ip] at e
    simp [layout.node.CUR_SC] at e
  · obtain ⟨-, -, c3, c4, c5⟩ := hcΩ c hc
    exact ⟨out_ne_node (h.omega _ c3) h.cur hN' (by rw [ip]; omega),
      out_ne_node (h.omega _ c4) h.cur hN' (by rw [ip]; omega), out_ne_node (h.omega _ c5) h.cur hN' (by rw [ip]; omega)⟩
  · exact rd_cur_node h (by rw [ip]; omega) (by rw [ip]) (by rw [idle8]; omega) (by rw [idle8]) (by rw [ip, idle8]; omega)
  · have ho := h.omega a ha'
    exact L.mem_wr_ne ha ho.1 (fun e => out_ne_node ho h.cur hN' (by rw [ip]; omega) e)

/-- `XInv` when the SC fields are kept or cleared. -/
theorem XInv.keep0 {s s' : S} (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
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
    (htn : TimerOK st T Cs s' ∧ NtbOK st T Nt s')
    (hsn : ∀ c ∈ Scs, L.mem s' (scNtfnA c) = L.mem s (scNtfnA c))
    (hyl : ∀ t ∈ T, L.mem s' (yieldA t) = L.mem s (yieldA t))
    (hyf : ∀ c ∈ Scs, L.mem s' (scYieldFromA c) = L.mem s (scYieldFromA c)) : XInv st T Cs Ω Sg Rp Scs Nt Z s' := by
  obtain ⟨hO, hR, hE⟩ := hX
  refine ⟨hO.ksb, ⟨fun t ht hs => ?_, fun t ht hs hn => ?_, fun r hr => ?_, fun r hr => ?_, fun r hr hn => ?_,
      fun c hc => by rw [hsr c hc]; exact hR.screp c hc⟩,
    ⟨fun t ht hb => ?_, hcs, fun c hc => by rw [(hfx c hc).2]; exact hE.core c hc,
      fun t ht => by rw [hbd t ht]; exact hE.bnd t ht, fun n hn => by rw [hns n hn]; exact hE.nsc n hn,
      htn.1, htn.2, fun c hc => by rw [hsn c hc]; exact hE.scn c hc,
      hE.yt.keep (fun c hc => (hfx c hc).1) hyl hyf⟩⟩
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
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T s) (ht : t ∈ T) (hc : c ≠ 0#u64) :
    BoundInv st T (L.wr s (scA t) c) := by
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
    hB.nb ei (by rw [stA_eq]; exact fk (L.idleW s) h.idleT _ (by simp) (by simp) (fun _ => by simp))⟩
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

/-- `XInv` after writing the `TCB` word of an SC no thread is bound to. -/
theorem XInv.set_sctcb {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {c0 v : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (hc0 : c0 ∈ Scs) (hnb : ∀ y ∈ T, L.mem s (scA y) ≠ c0) (hvT : v ≠ 0#u64 → v ∈ T) :
    XInv st T Cs Ω Sg Rp Scs Nt Z (L.wr s (scTcbA c0) v) := by
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
  refine ⟨hO.ksb, ⟨fun u hu hs => ?_, fun u hu hs hn => ?_, fun r hr => ?_, fun r hr => ?_, fun r hr hn => ?_,
      fun c hc => ?_⟩, ⟨fun u hu hb => ?_, by rw [ecs]; exact hE.cur, fun c hc => by rw [scw c hc _ (hcΩ _ hc).2.1 (Or.inl (sc_facts hO hc).2.2.1)]; exact hE.core c hc,
      fun u hu => by
        rw [show L.mem (L.wr s (scTcbA c0) v) (boundA u) = L.mem s (boundA u) from fk u hu _ (by simp) (by simp)]
        exact hE.bnd u hu,
      fun n hn => by
        rw [k _ (hO.ntAl n hn) (fun e => by rw [hv0.2.1] at e; have := hO.ntSc n hn c0 hc0; have := hv0.1; omega)]
        exact hE.nsc n hn,
      hE.tm.tmfr tmS, hE.ntb.tmfr tmS,
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
        exact hE.yt.2.2 c hc⟩⟩⟩
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

/-- `XInv` after binding `t` to the SC `c0`, which names `t` and a core. -/
theorem XInv.bind {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t c0 : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (ht : t ∈ T) (hc0 : c0 ∈ Scs) (htc : L.mem s (scTcbA c0) = t) (hcore : L.mem s (scCoreA c0) ∈ Cs) :
    XInv st T Cs Ω Sg Rp Scs Nt Z (L.wr s (scA t) c0) := by
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
  refine ⟨hO.ksb, ⟨fun u hu hs => ?_, fun u hu hs hn => ?_, fun r hr => ?_, fun r hr => ?_, fun r hr hn => ?_,
      fun c hc => ?_⟩, ⟨fun u hu hb => ?_, by rw [ecs]; exact hE.cur, fun c hc => by rw [ok _ (hcΩ _ hc).2.1]; exact hE.core c hc,
      fun u hu => by
        rw [show L.mem (L.wr s (scA t) c0) (boundA u) = L.mem s (boundA u) from
          fk u hu _ (by simp) (by simp) (fun _ => by simp)]
        exact hE.bnd u hu,
      fun n hn => by rw [ok _ (hsub _ (hO.ntW n hn))]; exact hE.nsc n hn,
      hE.tm.tmfr tmB, hE.ntb.tmfr tmB, fun c hc => by rw [ok _ (hsub _ (hO.snW c hc))]; exact hE.scn c hc,
      hE.yt.keep (fun c hc => ok _ (hcΩ c hc).1)
        (fun u hu => fk u hu _ (by simp) (by simp) (fun _ => by simp))
        (fun c hc => ok _ (hsub _ (hO.syW c hc)))⟩⟩
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
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hS : SCsOK st T Ω Sg Scs Z s) (ht : t ∈ T)
    (hin : SCin st s Sg c0 (Z c0))
    (hdisj : c0 ≠ L.cscW s → ∀ b, InSC c0 (Z c0) b → Outside b (L.cscW s) (Z (L.cscW s))) :
    SCsOK st T Ω Sg Scs Z (L.wr s (scA t) c0) := by
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
    fun y hy hb => ?_, ?_, fun y hy hb hne => ?_, fun c hc => (hS.all c hc).agree ag⟩
  · by_cases e : y = t
    · subst e; rw [L.mem_wr_same ha]; exact hin.agree (fun b hb => ag b hb)
    · rw [scy y hy e] at hb ⊢; exact (hS.bound y hy hb).agree ag
  · rw [ecs]; exact hS.cur.agree ag
  · rw [ecs] at hne ⊢
    by_cases e : y = t
    · subst e; rw [L.mem_wr_same ha] at hne ⊢; exact hdisj hne
    · rw [scy y hy e] at hb hne ⊢; exact hS.disj y hy hb hne

/-- Clearing the SC field of a thread in no ready or release queue, not the
switch-to candidate and not the idle thread. -/
theorem clear_sc_state {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T)
    (hout : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64 ∧
      L.actionW s ≠ t)
    (hidle : L.idleW s ≠ t) :
    SchedQueuesInvX st T Cs Ω H X (L.wr s (scA t) 0#u64) Q R ∧
      ((L.curW (L.wr s (scA t) 0#u64) = t → L.actionW (L.wr s (scA t) 0#u64) ≠ 0#u64) →
        BoundInv st T (L.wr s (scA t) 0#u64)) ∧
      BoundInv st T (L.wr (L.wr s (scA t) 0#u64)
        (L.nodeAt (L.wr s (scA t) 0#u64) (L.cpu (L.wr s (scA t) 0#u64)) layout.node.SCHED_ACTION) 1#u64) ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z (L.wr s (scA t) 0#u64) ∧ SCsOK st T Ω Sg Scs Z (L.wr s (scA t) 0#u64) ∧
      SgOK st Ω Sg (L.wr s (scA t) 0#u64) ∧
      L.actionW (L.wr s (scA t) 0#u64) = L.actionW s ∧ L.curW (L.wr s (scA t) 0#u64) = L.curW s ∧
      L.idleW (L.wr s (scA t) 0#u64) = L.idleW s ∧ L.cscW (L.wr s (scA t) 0#u64) = L.cscW s ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (y = t → K.val ≠ 3464) →
        L.mem (L.wr s (scA t) 0#u64) (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ a ∈ Ω, L.mem (L.wr s (scA t) 0#u64) a = L.mem s a) ∧ L.mem (L.wr s (scA t) 0#u64) (scA t) = 0#u64 := by
  obtain ⟨hq0, hr0, hna⟩ := hout
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
  have bnb : ¬ Blocked (L.mem s2 (stA (L.idleW s2))) := by
    rw [ei, stA_eq, F1 (L.idleW s) h.idleT _ (by simp) (by simp) (fun _ => by simp), ← stA_eq]; exact hB.idleNB
  refine ⟨h2, fun hcur => ⟨bq, br, fun haT => ?_, bidle, fun h0 => ?_, bnb⟩, BoundInv.choose h2 bq br bidle bnb,
    hX.keep0 (fun r hr => ⟨F2 _ (hrΩ r hr).1, F2 _ (hrΩ r hr).2.1, F2 _ (hrΩ r hr).2.2⟩)
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
      (fun y hy => F1 y hy _ (by simp) (by simp) (fun _ => by simp)) (fun c hc => F2 _ (hSg.sub _ (hX.1.syW c hc))),
    SCsOK.keep' hS hX (by simp [hs2]) (fun y hy => by
        by_cases e : y = t
        · subst e; exact Or.inr sct
        · exact Or.inl (scy y hy e)) ecs
      (fun c hc => ⟨F2 _ (hcΩ c hc).2.2.1, F2 _ (hcΩ c hc).2.2.2.1, F2 _ (hcΩ c hc).2.2.2.2⟩),
    ⟨hSg.sub, fun b hb => by simp only [hs2, LawfulStore.ksb_wr]; exact hSg.ks b hb,
      fun o h1 h2 => by simp only [hs2, LawfulStore.ksb_wr]; exact hSg.ksΩ o h1 h2⟩,
    ea, ec, ei, ecs, F1, F2, sct⟩
  · rw [ea] at haT ⊢; rw [scy _ haT hna]; exact hB.act haT
  · rw [ea] at h0; rw [ec]
    have hct : L.curW s ≠ t := fun e => hcur (by rw [ec]; exact e) (by rw [ea]; exact h0)
    rw [scy (L.curW s) h.curT hct]; exact hB.resume h0

/-! ## Scheduler steps with an exception set -/

theorem sched.enqueue.schX {X : Set U64} (s : S) (t : obj.Tcb) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T s) (hS : SgOK st Ω Sg s) (ht : t ∈ T)
    (hr : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 → (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64)
    (hrun : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 → Runnable (L.mem s (stA t)))
    (hbd : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 → L.mem s (scA t) ≠ 0#u64) :
    sched.enqueue st s t ⦃ s' => (∃ Q' R', SchedQueuesInvX st T Cs Ω H X s' Q' R') ∧ BoundInv st T s' ∧
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
  refine ⟨⟨_, _, h1⟩, hB.qstep h f.sc hi ea ec ei ?_ (fun hf => Or.inr (Or.inl (rf hf))) (f.st _ h.idleT), f, ea, ec,
    ⟨fun y hy => (hsb y hy).1, fun y hy hf => ?_⟩, ei, hi⟩
  · intro hf; rw [hinq] at hf
    by_cases e : (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64
    · exact Or.inl e
    · exact Or.inr (Or.inr (hbd (not_not.1 e)))
  · by_cases e : y = t
    · subst e; exact rf hf
    · rw [hi y hy e] at hf; exact hf

/-- `reschedule_required` with an exception set; the `IN_QUEUES` word of a
thread other than the switch-to candidate and the idle thread are kept. -/
theorem sched.reschedule_required.schX {X : Set U64} (s : S) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T s) (hS : SgOK st Ω Sg s) :
    sched.reschedule_required st s ⦃ s' => (∃ Q' R', SchedQueuesInvX st T Cs Ω H X s' Q' R') ∧ BoundInv st T s' ∧
      Fr st T Sg s s' ∧ L.actionW s' = 1#u64 ∧ L.curW s' = L.curW s ∧ Keeps st T s s' ∧ L.idleW s' = L.idleW s ∧
      ∀ y ∈ T, L.actionW s ≠ y → L.mem s' (inqA y) = L.mem s (inqA y) ⦄ := by
  unfold sched.reschedule_required
  step with sched.action.spec as ⟨act, act_post⟩
  refine WP.spec_bind (Pₘ := fun s1 => (∃ Q1 R1, SchedQueuesInvX st T Cs Ω H X s1 Q1 R1) ∧ BoundInv st T s1 ∧
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
            (fun _ => hbd)) fun s1 h1 => ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2.1, h1.2.2.2.2.2.2.1,
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
      (fun e => by rw [act_val] at e; omega)
    have f := fr_node (Sg := Sg) (v := 1#u64) h1 (hS.fr f1) h1.cur (by rw [act_val]; omega) (by rw [act_val])
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

/-! ## `donate` -/

/-- The IPC invariants with an exception set. -/
def BlkOKX (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (X : Set U64) (s : S) : Prop :=
  (∃ Q R, SchedQueuesInvX st T Cs Ω H X s Q R) ∧ BoundInv st T s ∧ XInv st T Cs Ω Sg Rp Scs Nt Z s ∧
    SCsOK st T Ω Sg Scs Z s ∧ SgOK st Ω Sg s

/-- The second half of `donate`: the SC `sc` (bound to no thread) gets `to`
(in no ready or release queue), which migrates to the SC's core. -/
theorem donate_tail {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {X : Set U64} (s6 : S) (a : A) (sc dst : U64)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h6 : SchedQueuesInvX st T Cs Ω H X s6 Q R) (hB6 : BoundInv st T s6) (hX6 : XInv st T Cs Ω Sg Rp Scs Nt Z s6)
    (hS6 : SCsOK st T Ω Sg Scs Z s6) (hSg6 : SgOK st Ω Sg s6) (hto : dst ∈ T)
    (htq : (L.mem s6 (inqA dst) &&& sched.Q_QUEUED) = 0#u64) (htr : (L.mem s6 (inqA dst) &&& sched.Q_RELEASE) = 0#u64)
    (hsc : sc ∈ Scs) (hsc0 : sc ≠ 0#u64) (hnb : ∀ y ∈ T, L.mem s6 (scA y) ≠ sc)
    (hcore : L.mem s6 (scCoreA sc) ∈ Cs) (hin : SCin st s6 Sg sc (Z sc))
    (hdisj : sc ≠ L.cscW s6 → ∀ b, InSC sc (Z sc) b → Outside b (L.cscW s6) (Z (L.cscW s6))) :
    (do
      let s2 ← obj.Sc.set_tcb st sc s6 dst
      let s3 ← obj.Tcb.set_sc st dst s2 sc
      let i1 ← obj.Sc.cpu st sc s3
      smp.migrate_tcb st ar s3 a dst i1) ⦃ s' _ => BlkOKX st T Cs Ω H Sg Rp Scs Nt Z X s' ∧
        (∀ y ∈ T, L.mem s' (stA y) = L.mem s6 (stA y)) ∧ (∀ y ∈ T, L.mem s' (replyA y) = L.mem s6 (replyA y)) ∧
        TmFr st T Cs Nt s6 s' ∧
        (L.mem s' (scA dst) = sc ∧ L.mem s' (scTcbA sc) = dst ∧ L.actionW s' = L.actionW s6) ⦄ := by
  have hT := h6.tcbs
  have hta := hT dst hto
  have hN := h6.nodes _ h6.cur
  have hO := hX6.1
  have hv0 := sc_facts hO hsc
  obtain ⟨hrΩ, hcΩ⟩ := objs_omega hO hSg6.sub
  have hm : scTcbA sc ∈ Ω := hSg6.sub _ (hO.fixW sc hsc).1
  have ho := h6.omega _ hm
  step with obj.Sc.set_tcb.wr as ⟨s7, e7⟩
  have tm7 : TmFr st T Cs Nt s6 s7 := by
    rw [e7]
    exact TmFr.wr hT h6.nodes hO ho.1 (notTmW_omega hT h6.nodes ho
      (fun n hn => by
        rw [hv0.2.1, ntfnBtA_val (hO.ntP n hn)]; have := hO.ntOSc n hn sc hsc; have := hv0.1; omega))
  -- the `TCB` word of `sc`
  obtain ⟨h7, a7, f7⟩ := omega_wr (v := dst) h6 hm
  have hB7 := BoundInv.owr (v := dst) h6 hB6 hm
  have hX7 := XInv.set_sctcb (v := dst) h6 hX6 hSg6.sub hsc hnb (fun _ => hto)
  have nh : ∀ c ∈ Scs, (scTcbA sc).val ≠ (maxA c).val ∧ (scTcbA sc).val ≠ (headA c).val ∧
      (scTcbA sc).val ≠ (tailA c).val := by
    intro c hc
    obtain ⟨h128, -, -, e3, e4, e5, -⟩ := sc_facts hO hc
    rw [hv0.2.1, e3, e4, e5]
    by_cases hcc : c = sc
    · subst hcc; omega
    · have := hO.scDisj c hc sc hsc hcc; have := hv0.1; omega
  have hS7 := SCsOK.wr (v := dst) h6 hS6 hX6 ho.1
    (fun y hy => (out_ne_field (K := 3464#u64) ho hy (hT y hy) (by simp)).symm)
    (out_ne_node ho h6.cur hN (by simp [layout.node.CUR_SC])).symm nh
  rw [← e7] at h7 a7 f7 hB7 hX7 hS7
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
  -- the SC is still well formed
  have hin7 : SCin st s7 Sg sc (Z sc) := by
    refine ⟨hin.1.of_hdr ?_ ?_ ?_, hin.2⟩
    · exact k7 _ (hcΩ _ hsc).2.2.1 (Ne.symm (nh sc hsc).1)
    · rw [show L.rhead s7 sc = L.mem s7 (headA sc) from rfl, k7 _ (hcΩ _ hsc).2.2.2.1 (Ne.symm (nh sc hsc).2.1)]
      exact hin.1.head_lt
    · rw [show L.rtail s7 sc = L.mem s7 (tailA sc) from rfl, k7 _ (hcΩ _ hsc).2.2.2.2 (Ne.symm (nh sc hsc).2.2)]
      exact hin.1.tail_lt
  -- `dst` gets the SC
  step with obj.Tcb.set_sc.wr as ⟨s8, e8⟩
  have tm8 : TmFr st T Cs Nt s7 s8 := by
    rw [e8]
    exact TmFr.wr hT h7.nodes hX7.1 (scA_aligned hta)
      (notTmW_field (K := 3464#u64) hT h7.nodes (fun n hn => h7.omega _ (hSg6.sub _ (hO.ntB n hn).2)) hto
        (by simp) (by simp))
  have h8 : SchedQueuesInvX st T Cs Ω H X s8 Q R := by
    rw [e8]; exact inv_wr_field (K := 3464#u64) h7 hto (by simp) (by simp) (by simp)
  have hB8 : BoundInv st T s8 := by rw [e8]; exact BoundInv.set_sc h7 hB7 hto hsc0
  have hX8 : XInv st T Cs Ω Sg Rp Scs Nt Z s8 := by
    rw [e8]; exact XInv.bind h7 hX7 hSg6.sub hto hsc t7 (by rw [core7]; exact hcore)
  have hS8 : SCsOK st T Ω Sg Scs Z s8 := by
    rw [e8]; exact SCsOK.bind h7 hS7 hto hin7 (by rw [ecs7]; exact hdisj)
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
  step with obj.Sc.cpu.spec as ⟨cpu, ecpu⟩
  -- migration
  unfold smp.migrate_tcb
  step with obj.Tcb.affinity.spec as ⟨af, _⟩
  have hc' : cpu ∈ Cs := by rw [ecpu, core8]; exact hcore
  have iq8 : L.mem s8 (inqA dst) = L.mem s6 (inqA dst) := by
    rw [inqA_eq]; exact fld8 dst hto _ (by simp) (by simp) (fun _ => by simp)
  have fin : ∀ a1 : A, (do
      let s1 ← obj.Tcb.set_affinity st dst s8 cpu
      ok (s1, a1)) ⦃ s' _ => BlkOKX st T Cs Ω H Sg Rp Scs Nt Z X s' ∧ (∀ y ∈ T, L.mem s' (stA y) = L.mem s6 (stA y)) ∧
        (∀ y ∈ T, L.mem s' (replyA y) = L.mem s6 (replyA y)) ∧
          TmFr st T Cs Nt s6 s' ∧
        (L.mem s' (scA dst) = sc ∧ L.mem s' (scTcbA sc) = dst ∧ L.actionW s' = L.actionW s6) ⦄ := by
    intro a1
    refine WP.spec_bind (obj.Tcb.set_affinity.wr s8 dst cpu) fun s9 e9 => ?_
    subst e9
    have tm9 : TmFr st T Cs Nt s8 (L.wr s8 (affA dst) cpu) :=
      TmFr.wr hT h8.nodes hX8.1 (field_aligned (K := 3520#u64) hta (by simp) (by simp))
        (notTmW_field (K := 3520#u64) hT h8.nodes (fun n hn => h8.omega _ (hSg6.sub _ (hO.ntB n hn).2)) hto
          (by simp) (by simp))
    obtain ⟨b1, b2⟩ := bx_field (K := 3520#u64) (v := cpu) h8 hB8 hX8 hSg6.sub hto (by simp) (by simp) (by simp) (by simp)
    refine (WP.spec_ok _).2 ⟨⟨⟨Q, R, inv_wr_aff h8 hto (by rw [iq8]; exact htq) (by rw [iq8]; exact htr) hc'⟩, b1, b2,
      SCsOK.field (K := 3520#u64) h8 hS8 hX8 hto (by simp) (by simp) (by simp),
      ⟨hSg6.sub, fun b hb => by rw [L.ksb_wr]; exact hSg8.ks b hb, fun o h1 h2 => by rw [L.ksb_wr]; exact hSg8.ksΩ o h1 h2⟩⟩,
      fun y hy => ?_, fun y hy => ?_, tm7.trans (tm8.trans tm9), ?_⟩
    rotate_left
    · have e1 : L.mem (L.wr s8 (affA dst) cpu) (replyA y) = L.mem s8 (replyA y) :=
        L.mem_wr_ne (field_aligned (K := 3520#u64) hta (by simp) (by simp))
          (field_aligned (K := 3360#u64) (hT y hy) (by simp) (by simp))
          (fun e => field_ne (K1 := 3520#u64) (K2 := 3360#u64) hta (hT y hy) (by simp) (by simp) (fun _ => by simp)
            (UScalar.eq_of_val_eq e))
      rw [e1]; exact fld8 y hy _ (by simp) (by simp) (fun _ => by simp)
    · have sc8 : L.mem s8 (scA dst) = sc := by rw [e8]; exact L.mem_wr_same (scA_aligned hta)
      have t8 : L.mem s8 (scTcbA sc) = dst := by
        rw [e8, L.mem_wr_ne (scA_aligned hta) ho.1 (fun e => out_ne_field (K := 3464#u64) ho hto hta (by simp) e)]
        exact t7
      have a8 : L.actionW s8 = L.actionW s6 := by
        rw [e8, act_wr_field (K := 3464#u64) (a := scA dst) (h7.nodes _ h7.cur) hto hta rfl (by simp) (by simp)]
        exact a7
      refine ⟨?_, ?_, ?_⟩
      · rw [L.mem_wr_ne (a := affA dst) (field_aligned (K := 3520#u64) hta (by simp) (by simp)) (scA_aligned hta)
          (fun e => field_ne (K1 := 3520#u64) (K2 := 3464#u64) hta hta (by simp) (by simp) (fun _ => by simp)
            (UScalar.eq_of_val_eq e))]; exact sc8
      · rw [L.mem_wr_ne (a := affA dst) (field_aligned (K := 3520#u64) hta (by simp) (by simp)) ho.1
          (fun e => out_ne_field ho hto hta (by simp) e)]; exact t8
      · rw [act_wr_field (K := 3520#u64) (a := affA dst) (h8.nodes _ h8.cur) hto hta rfl (by simp) (by simp)]
        exact a8
    have e1 : L.mem (L.wr s8 (affA dst) cpu) (stA y) = L.mem s8 (stA y) :=
      L.mem_wr_ne (field_aligned (K := 3520#u64) hta (by simp) (by simp))
        (by rw [stA_eq]; exact field_aligned (hT y hy) (by simp) (by simp))
        (fun e => by
          rw [stA_eq] at e
          exact field_ne (K1 := 3520#u64) (K2 := 3328#u64) hta (hT y hy) (by simp) (by simp) (fun _ => by simp)
            (UScalar.eq_of_val_eq e))
    rw [e1, stA_eq]; exact fld8 y hy _ (by simp) (by simp) (fun _ => by simp)
  split
  · refine WP.spec_bind (Pₘ := fun r : A × U64 => r.2 = dst) ?_ ?_
    · refine WP.spec_bind (hA.fpu_flush _ _) fun a2 _ => ?_
      refine WP.spec_bind (hA.fpu_release _ _) fun a3 _ => ?_
      exact (WP.spec_ok _).2 rfl
    · rintro ⟨a1, t1⟩ e
      simp only at e
      subst e
      exact fin a1
  · try simp only [Aeneas.Std.bind_ok]
    exact fin a

/-- `remote_tcb_stall` keeps the invariants. -/
theorem smp.remote_tcb_stall.all {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t : obj.Tcb) {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z s) (hSg : SgOK st Ω Sg s) :
    smp.remote_tcb_stall st ar s a t ⦃ s' _ => SchedQueuesInvX st T Cs Ω H X s' Q R ∧ BoundInv st T s' ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧ SCsOK st T Ω Sg Scs Z s' ∧ SgOK st Ω Sg s' ∧
      L.actionW s' = L.actionW s ∧ L.curW s' = L.curW s ∧ L.idleW s' = L.idleW s ∧ L.cscW s' = L.cscW s ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ a ∈ Ω, L.mem s' a = L.mem s a) ⦄ := by
  refine WP.spec_mono (smp.remote_tcb_stall.spec hA s a t) fun r hr => ?_
  obtain ⟨s', a'⟩ := r
  simp only [WP.uncurry'_pair] at hr ⊢
  rcases hr with rfl | ⟨v, rfl⟩
  · exact ⟨h, hB, hX, hS, hSg, rfl, rfl, rfl, rfl, fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩
  · exact ipi_all h hB hX hS hSg

/-- seL4 `schedContext_donate` of the SC `sc` of `fr` (in no ready or
release queue, not the switch-to candidate, not idle) to `dst` (unbound, in no
queue, not the candidate). -/
theorem schedcontext.donate.ipc {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {X : Set U64} (s : S) (a : A)
    (sc dst fr : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z s) (hSg : SgOK st Ω Sg s) (hfr : fr ∈ T) (hscf : L.mem s (scA fr) = sc)
    (hsc0 : sc ≠ 0#u64)
    (hfout : (L.mem s (inqA fr) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s (inqA fr) &&& sched.Q_RELEASE) = 0#u64 ∧
      L.actionW s ≠ fr)
    (hfi : L.idleW s ≠ fr) (hdst : dst ∈ T) (hd0 : L.mem s (scA dst) = 0#u64)
    (hdq : (L.mem s (inqA dst) &&& sched.Q_QUEUED) = 0#u64) (hdr : (L.mem s (inqA dst) &&& sched.Q_RELEASE) = 0#u64)
    (hda : L.actionW s ≠ dst) (hne : dst ≠ fr) :
    schedcontext.donate st ar s a sc dst ⦃ s' _ => BlkOKX st T Cs Ω H Sg Rp Scs Nt Z X s' ∧
      (∀ y ∈ T, L.mem s' (stA y) = L.mem s (stA y)) ∧ ∀ y ∈ T, L.mem s' (replyA y) = L.mem s (replyA y) ⦄ := by
  have hT := h.tcbs
  have hfa := hT fr hfr
  obtain ⟨hscS, htcb, hcore⟩ := hX.2.2.bound fr hfr (by rw [hscf]; exact hsc0)
  rw [hscf] at hscS htcb hcore
  have hin0 : SCin st s Sg sc (Z sc) := by
    have := (hS.bound fr hfr (by rw [hscf]; exact hsc0)); rw [hscf] at this; exact this
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
      BoundInv st T r.1 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ SCsOK st T Ω Sg Scs Z r.1 ∧ SgOK st Ω Sg r.1 ∧
      (∀ y ∈ T, L.mem r.1 (stA y) = L.mem s (stA y)) ∧ (∀ y ∈ T, L.mem r.1 (replyA y) = L.mem s (replyA y)) ∧
      L.mem r.1 (scA i) = 0#u64 ∧
      (∀ y ∈ T, y ≠ i → L.mem r.1 (scA y) = L.mem s (scA y)) ∧ L.mem r.1 (inqA dst) = L.mem s (inqA dst) ∧
      (∀ b ∈ Sg, L.mem r.1 b = L.mem s b) ∧ L.cscW r.1 = L.cscW s) ?_ ?_
  rotate_left
  · rintro ⟨s6, a6⟩ ⟨Q6, R6, h6, hB6, hX6, hS6, hSg6, st6, rp6, sf6, sy6, iq6, sg6, cs6⟩
    try simp only [WP.uncurry'_pair]
    refine WP.spec_mono (donate_tail hA s6 a6 sc dst Q6 R6 h6 hB6 hX6 hS6 hSg6 hdst
      (by rw [iq6]; exact hdq) (by rw [iq6]; exact hdr) hscS hsc0 (fun y hy => ?_)
      (by rw [sg6 _ hfixΩ.2]; exact hcore) (hin0.agree sg6) (by rw [cs6]; exact hdisj0)) fun r hh => ?_
    · by_cases e : y = i
      · subst e; rw [sf6]; exact Ne.symm hsc0
      · rw [sy6 y hy e]; exact hnb0 y hy e
    · obtain ⟨s', a'⟩ := r
      simp only [WP.uncurry'_pair] at hh ⊢
      exact ⟨hh.1, fun y hy => (hh.2.1 y hy).trans (st6 y hy), fun y hy => (hh.2.2.1 y hy).trans (rp6 y hy)⟩
  split
  · rename_i hbt; rw [hb] at hbt; exact absurd hbt (by simp)
  refine WP.spec_bind (smp.remote_tcb_stall.all hA s a i h hB hX hS hSg) ?_
  rintro ⟨s2, a2⟩ ⟨h2, hB2, hX2, hS2, hSg2, ea2, ec2, ei2, ecs2, f2, o2⟩
  try simp only [WP.uncurry'_pair]
  have iq2 : L.mem s2 (inqA i) = L.mem s (inqA i) := by rw [inqA_eq]; exact f2 i hfr _ (by simp) (by simp)
  refine WP.spec_bind (sched.dequeue.noop s2 i (by rw [iq2]; exact hfout.1)) fun s3 e3 => ?_
  subst e3
  refine WP.spec_bind (sched.release_remove.noop s3 i (by rw [iq2]; exact hfout.2.1)) fun s4 e4 => ?_
  subst e4
  step with obj.Tcb.set_sc.wr as ⟨s5, e5⟩
  have key := clear_sc_state h2 hB2 hX2 hS2 hSg2 hfr
    ⟨by rw [iq2]; exact hfout.1, by rw [iq2]; exact hfout.2.1, by rw [ea2]; exact hfout.2.2⟩ (by rw [ei2]; exact hfi)
  rw [← e5] at key
  obtain ⟨k1, kB, kB3, k3, k4, k5, ka, kc, ki, kcs, kf, kΩ, ks0⟩ := key
  have sg5 : ∀ b ∈ Sg, L.mem s5 b = L.mem s b := fun b hb => (kΩ b (hSg.sub b hb)).trans (o2 b (hSg.sub b hb))
  have sy5 : ∀ y ∈ T, y ≠ i → L.mem s5 (scA y) = L.mem s (scA y) := fun y hy hyi =>
    (kf y hy 3464#u64 (by simp) (by simp) (fun e => absurd e hyi)).trans (f2 y hy _ (by simp) (by simp))
  have st5 : ∀ y ∈ T, L.mem s5 (stA y) = L.mem s (stA y) := fun y hy => by
    rw [stA_eq]; exact (kf y hy _ (by simp) (by simp) (fun _ => by simp)).trans (f2 y hy _ (by simp) (by simp))
  have rp5 : ∀ y ∈ T, L.mem s5 (replyA y) = L.mem s (replyA y) := fun y hy =>
    (kf y hy _ (by simp) (by simp) (fun _ => by simp)).trans (f2 y hy _ (by simp) (by simp))
  have iq5 : L.mem s5 (inqA dst) = L.mem s (inqA dst) := by
    rw [inqA_eq]; exact (kf dst hdst _ (by simp) (by simp) (fun _ => by simp)).trans (f2 dst hdst _ (by simp) (by simp))
  have cs5 : L.cscW s5 = L.cscW s := kcs.trans ecs2
  have ea5 : L.actionW s5 = L.actionW s := ka.trans ea2
  step with sched.cur_thread.spec as ⟨t1, et1⟩
  step with tcb_eq.blk as ⟨b1, eb1⟩
  split
  · by_cases ha0 : L.actionW s5 = 0#u64
    · refine WP.spec_bind (sched.reschedule_required.resume s5 ha0) fun s6 e6 => ?_
      subst e6
      have f := fr_node (Sg := Sg) (v := 1#u64) k1 k5 k1.cur (by rw [act_val]; omega) (by rw [act_val])
        (hto := ⟨by rw [act_val]; omega, by rw [act_val]; omega⟩)
        (fun _ => by rw [act_val]; omega)
      obtain ⟨j1, -⟩ := inv_set_action k1 (Or.inr (Or.inl rfl)) (fun h1T => absurd h1T (notT_small k1.tcbs (by simp)))
      have fw : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
          L.mem (L.wr s5 (L.nodeAt s5 (L.cpu s5) layout.node.SCHED_ACTION) 1#u64) (core.num.U64.wrapping_add y K) =
            L.mem s5 (core.num.U64.wrapping_add y K) := fun y hy K hK hK8 =>
        field_wr_node k1 k1.cur (by rw [act_val]; omega) (by rw [act_val]) hy hK hK8
      refine (WP.spec_ok _).2 ⟨Q, R, j1, kB3, k3.fr f, k4.fr f, k5.fr f, fun y hy => ?_,
        fun y hy => (fw y hy _ (by simp) (by simp)).trans (rp5 y hy), ?_, fun y hy hyi => ?_, ?_,
        fun b hb => (f.sig b hb).trans (sg5 b hb), f.csc.trans cs5⟩
      · rw [stA_eq, fw y hy _ (by simp) (by simp), ← stA_eq]; exact st5 y hy
      · rw [scA_eq, fw i hfr _ (by simp) (by simp), ← scA_eq]; exact ks0
      · rw [scA_eq, fw y hy _ (by simp) (by simp), ← scA_eq]; exact sy5 y hy hyi
      · rw [inqA_eq, fw dst hdst _ (by simp) (by simp), ← inqA_eq]; exact iq5
    · have kB2 := kB (fun _ => ha0)
      have hda5 : L.actionW s5 ≠ dst := by rw [ea5]; exact hda
      refine WP.spec_bind (sched.reschedule_required.schX s5 Q R k1 kB2 k5) fun s6 hh => ?_
      obtain ⟨⟨Q6, R6, h6⟩, hB6, fr6, -, -, kp6, -, iq6⟩ := hh
      refine (WP.spec_ok _).2 ⟨Q6, R6, h6, hB6, k3.fr fr6, k4.fr fr6, k5.fr fr6,
        fun y hy => (kp6.1 y hy).trans (st5 y hy), fun y hy => (fr6.rep y hy).trans (rp5 y hy), (fr6.sc i hfr).trans ks0,
        fun y hy hyi => (fr6.sc y hy).trans (sy5 y hy hyi), (iq6 dst hdst hda5).trans iq5,
        fun b hb => (fr6.sig b hb).trans (sg5 b hb), fr6.csc.trans cs5⟩
  · rename_i hb1
    have hne' : i ≠ t1 := fun e => hb1 (by rw [eb1, decide_eq_true_eq]; exact e)
    have kB2 := kB (fun e => absurd (by rw [et1]; exact e.symm) hne')
    step with sched.action.spec as ⟨i1, ei1⟩
    split
    · rename_i hii; exfalso; exact hfout.2.2 (by rw [← ea5, ← ei1, hii])
    · try simp only [Aeneas.Std.bind_ok]
      refine (WP.spec_ok _).2 ?_
      exact ⟨Q, R, k1, kB2, k3, k4, k5, st5, rp5, ks0, sy5, iq5, sg5, cs5⟩

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
theorem XInv.wr_linkT {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {a w : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (haΩ : a ∈ Ω) (ht : ∀ r ∈ Rp, a.val ≠ (rTcbA r).val)
    (hc : ∀ c ∈ Scs, a.val ≠ (scTcbA c).val ∧ a.val ≠ (scCoreA c).val)
    (hn : ∀ r ∈ Rp, a.val = (rNextA r).val → w &&& ~~~1#u64 ≠ 0#u64 →
      (headBit w = true → w &&& ~~~1#u64 ∈ Scs) ∧ (headBit w = false → w &&& ~~~1#u64 ∈ Rp))
    (hp : ∀ r ∈ Rp, a.val = (rPrevA r).val → w &&& ~~~1#u64 ≠ 0#u64 → w &&& ~~~1#u64 ∈ Rp)
    (hs : ∀ c ∈ Scs, a.val = (scReplyA c).val → w ≠ 0#u64 → w ∈ Rp)
    (hnt : ∀ n ∈ Nt, a.val = (ntfnScA n).val → w ≠ 0#u64 → w ∈ Scs)
    (hnb : ∀ n ∈ Nt, a.val = (ntfnBtA n).val → Tz T w)
    (hsnT : ∀ c ∈ Scs, a.val = (scNtfnA c).val → w ≠ 0#u64 → w ∈ Nt)
    (hsyT : ∀ c ∈ Scs, a.val = (scYieldFromA c).val → w ≠ 0#u64 → w ∈ T) :
    XInv st T Cs Ω Sg Rp Scs Nt Z (L.wr s a w) := by
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
  refine ⟨hO.ksb, ⟨fun u hu hs => ?_, fun u hu hs hn' => ?_, fun r hr => ?_, fun r hr => ?_, fun r hr hn' => ?_,
      fun c hcs => ?_⟩, ⟨fun u hu hb => ?_, by rw [ecs]; exact hE.cur, fun c' hc' => by rw [k _ (al _ (hcΩ _ hc').2.1) (hc _ hc').2]; exact hE.core c' hc',
      fun u hu => by
        rw [show L.mem (L.wr s a w) (boundA u) = L.mem s (boundA u) from fk u hu _ (by simp) (by simp)]
        exact hE.bnd u hu,
      fun n hn => by
        rw [L.mem_wr_val ho.1 (hO.ntAl n hn)]
        split
        · exact hnt n hn ‹_›
        · exact hE.nsc n hn,
      hE.tm.wr_out h.tcbs h.nodes ho, hE.ntb.wr_tz hO ho.1 hnb, fun c hc => by
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
        · exact hE.yt.2.2 c hc⟩⟩⟩
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
    · exact hs c hcs ‹_›
    · exact hR.screp c hcs
  · rw [sc' u hu] at hb ⊢
    obtain ⟨h1, h2, h3⟩ := hE.bound u hu hb
    rw [k _ (al _ (hcΩ _ h1).1) (hc _ h1).1, k _ (al _ (hcΩ _ h1).2.1) (hc _ h1).2]
    exact ⟨h1, h2, h3⟩

theorem XInv.wr_link {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {a w : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (haΩ : a ∈ Ω) (ht : ∀ r ∈ Rp, a.val ≠ (rTcbA r).val)
    (hc : ∀ c ∈ Scs, a.val ≠ (scTcbA c).val ∧ a.val ≠ (scCoreA c).val)
    (hn : ∀ r ∈ Rp, a.val = (rNextA r).val → w &&& ~~~1#u64 ≠ 0#u64 →
      (headBit w = true → w &&& ~~~1#u64 ∈ Scs) ∧ (headBit w = false → w &&& ~~~1#u64 ∈ Rp))
    (hp : ∀ r ∈ Rp, a.val = (rPrevA r).val → w &&& ~~~1#u64 ≠ 0#u64 → w &&& ~~~1#u64 ∈ Rp)
    (hs : ∀ c ∈ Scs, a.val = (scReplyA c).val → w ≠ 0#u64 → w ∈ Rp)
    (hnt : ∀ n ∈ Nt, a.val ≠ (ntfnScA n).val) (hnb : ∀ n ∈ Nt, a.val ≠ (ntfnBtA n).val)
    (hsn : ∀ c ∈ Scs, a.val ≠ (scNtfnA c).val) (hsy : ∀ c ∈ Scs, a.val ≠ (scYieldFromA c).val) :
    XInv st T Cs Ω Sg Rp Scs Nt Z (L.wr s a w) :=
  hX.wr_linkT h hsub haΩ ht hc hn hp hs (fun n hn e => absurd e (hnt n hn)) (fun n hn e => absurd e (hnb n hn))
    (fun c hc e => absurd e (hsn c hc)) fun c hc e => absurd e (hsy c hc)

/-- The invariants after a write of a word of another object (a reply link,
an SC `REPLY` word, a notification's badge or `BOUND_TCB`). -/
theorem link_allT {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {a w : U64}
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z s) (hSg : SgOK st Ω Sg s)
    (haΩ : a ∈ Ω) (ht : ∀ r ∈ Rp, a.val ≠ (rTcbA r).val)
    (hc : ∀ c ∈ Scs, a.val ≠ (scTcbA c).val ∧ a.val ≠ (scCoreA c).val ∧ a.val ≠ (maxA c).val ∧
      a.val ≠ (headA c).val ∧ a.val ≠ (tailA c).val)
    (hn : ∀ r ∈ Rp, a.val = (rNextA r).val → w &&& ~~~1#u64 ≠ 0#u64 →
      (headBit w = true → w &&& ~~~1#u64 ∈ Scs) ∧ (headBit w = false → w &&& ~~~1#u64 ∈ Rp))
    (hp : ∀ r ∈ Rp, a.val = (rPrevA r).val → w &&& ~~~1#u64 ≠ 0#u64 → w &&& ~~~1#u64 ∈ Rp)
    (hs : ∀ c ∈ Scs, a.val = (scReplyA c).val → w ≠ 0#u64 → w ∈ Rp)
    (hnt : ∀ n ∈ Nt, a.val = (ntfnScA n).val → w ≠ 0#u64 → w ∈ Scs)
    (hnb : ∀ n ∈ Nt, a.val = (ntfnBtA n).val → Tz T w)
    (hsnT : ∀ c ∈ Scs, a.val = (scNtfnA c).val → w ≠ 0#u64 → w ∈ Nt)
    (hsyT : ∀ c ∈ Scs, a.val = (scYieldFromA c).val → w ≠ 0#u64 → w ∈ T) :
    SchedQueuesInv st T Cs Ω H (L.wr s a w) Q R ∧ BoundInv st T (L.wr s a w) ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z (L.wr s a w) ∧ SCsOK st T Ω Sg Scs Z (L.wr s a w) ∧ SgOK st Ω Sg (L.wr s a w) ∧
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
  refine ⟨h1, BoundInv.owr h hB haΩ, XInv.wr_linkT h hX hSg.sub haΩ ht (fun c hcs => ⟨(hc c hcs).1, (hc c hcs).2.1⟩)
      hn hp hs hnt hnb hsnT hsyT,
    SCsOK.wr h hS hX ho.1 (fun y hy => (out_ne_field (K := 3464#u64) ho hy (h.tcbs y hy) (by simp)).symm)
      (out_ne_node ho h.cur hN (by simp [layout.node.CUR_SC])).symm (fun c hcs => (hc c hcs).2.2),
    ⟨hSg.sub, fun b hb => by rw [L.ksb_wr]; exact hSg.ks b hb, fun o h1 h2 => by rw [L.ksb_wr]; exact hSg.ksΩ o h1 h2⟩,
    ea, nd _ (by rw [curth0]; omega) (by rw [curth0]), nd _ (by rw [idle8]; omega) (by rw [idle8]), f,
    fun b hb hne => L.mem_wr_ne ho.1 (h.omega b hb).1 hne⟩

/-- The invariants after a reply-link or SC `REPLY` write. -/
theorem link_all {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {a w : U64}
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z s) (hSg : SgOK st Ω Sg s)
    (haΩ : a ∈ Ω) (ht : ∀ r ∈ Rp, a.val ≠ (rTcbA r).val)
    (hc : ∀ c ∈ Scs, a.val ≠ (scTcbA c).val ∧ a.val ≠ (scCoreA c).val ∧ a.val ≠ (maxA c).val ∧
      a.val ≠ (headA c).val ∧ a.val ≠ (tailA c).val)
    (hn : ∀ r ∈ Rp, a.val = (rNextA r).val → w &&& ~~~1#u64 ≠ 0#u64 →
      (headBit w = true → w &&& ~~~1#u64 ∈ Scs) ∧ (headBit w = false → w &&& ~~~1#u64 ∈ Rp))
    (hp : ∀ r ∈ Rp, a.val = (rPrevA r).val → w &&& ~~~1#u64 ≠ 0#u64 → w &&& ~~~1#u64 ∈ Rp)
    (hs : ∀ c ∈ Scs, a.val = (scReplyA c).val → w ≠ 0#u64 → w ∈ Rp)
    (hnt : ∀ n ∈ Nt, a.val ≠ (ntfnScA n).val) (hnb : ∀ n ∈ Nt, a.val ≠ (ntfnBtA n).val)
    (hsn : ∀ c ∈ Scs, a.val ≠ (scNtfnA c).val) (hsy : ∀ c ∈ Scs, a.val ≠ (scYieldFromA c).val) :
    SchedQueuesInv st T Cs Ω H (L.wr s a w) Q R ∧ BoundInv st T (L.wr s a w) ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z (L.wr s a w) ∧ SCsOK st T Ω Sg Scs Z (L.wr s a w) ∧ SgOK st Ω Sg (L.wr s a w) ∧
      L.actionW (L.wr s a w) = L.actionW s ∧ L.curW (L.wr s a w) = L.curW s ∧ L.idleW (L.wr s a w) = L.idleW s ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        L.mem (L.wr s a w) (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ b ∈ Ω, a.val ≠ b.val → L.mem (L.wr s a w) b = L.mem s b) :=
  link_allT h hB hX hS hSg haΩ ht hc hn hp hs (fun n hn e => absurd e (hnt n hn)) (fun n hn e => absurd e (hnb n hn))
    (fun c hc e => absurd e (hsn c hc)) fun c hc e => absurd e (hsy c hc)

/-! ## `reply_push` -/

theorem reply_val : sched.TS_BLOCKED_ON_REPLY = 5#u64 := by unfold sched.TS_BLOCKED_ON_REPLY; rfl

theorem not_blocked_reply' : ¬ Blocked sched.TS_BLOCKED_ON_REPLY := fun hb => blocked_ne_reply hb rfl

/-- The reply object names the caller, which blocks on it (`set_blocked_on_reply`). -/
theorem sched.set_blocked_on_reply.ipc {X : Set U64} (s : S) (caller r : U64) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hXc : ExcT X caller)
    (hx : caller ∈ X ∨ ¬ Blocked (L.mem s (stA caller)))
    (hB : BoundInv st T s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z s) (hSg : SgOK st Ω Sg s)
    (hcl : caller ∈ T) (hcq : (L.mem s (inqA caller) &&& sched.Q_QUEUED) = 0#u64)
    (hcr : (L.mem s (inqA caller) &&& sched.Q_RELEASE) = 0#u64) (hca : L.actionW s ≠ caller)
    (hcold : L.mem s (stA caller) ≠ sched.TS_BLOCKED_ON_REPLY ∧ L.mem s (stA caller) ≠ sched.TS_BLOCKED_ON_RECV)
    (hr : r ∈ Rp) (hr00 : r ≠ 0#u64) (hr0 : L.mem s (rTcbA r) = 0#u64) :
    sched.set_blocked_on_reply st (L.wr s (rTcbA r) caller) caller r ⦃ s2 =>
      SchedQueuesInv st T Cs Ω H s2 Q R ∧ BoundInv st T s2 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z s2 ∧
      SCsOK st T Ω Sg Scs Z s2 ∧ SgOK st Ω Sg s2 ∧
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
  obtain ⟨b1, b2, b3⟩ := blk_keep (hidl := fun _ => by rw [v2]; exact not_blocked_reply')
    (htm := TmFr.of_blkfoot h hX.1 hSg.sub hcl (fun _ => hr) w2) h hB hX hS hcl w2.1 w2.2.1 (fun y hy K hK hK8 _ _ hy' => k1 y hy K hK hK8 hy')
    (fun a ha hne => k2 a ha hne) (fun o ho => k3 o (by omega) (by omega) (by omega)) a2
    (fun _ => ⟨by rw [rp2]; exact hr, by rw [rp2]; exact rt2⟩) (fun _ => ⟨hr, Or.inl hr0⟩)
    (fun e => absurd (v2.symm.trans e) (by rw [reply_val]; obtain ⟨-, -, r3, -⟩ := ts_vals; rw [r3]; decide))
    hcold (fun _ => ⟨rt2, rp2, Or.inl v2⟩)
  exact ⟨h2', b1, b2, b3, ⟨hSg.sub, fun b hb => by rw [w2.1]; exact hSg.ks b hb,
      fun o h1 h2 => by rw [w2.1]; exact hSg.ksΩ o h1 h2⟩,
    k1, fun a ha hne => k2 a ha (fun _ => hne), a2, k3 _ (by rw [curth0]; omega) (by rw [curth0]) (by rw [curth0]; omega),
    k3 _ (by rw [idle8]; omega) (by rw [idle8]) (by rw [idle8]; omega), v2⟩

/-- seL4 `reply_push` (MCS): the caller blocks on the reply object, which goes
on top of the caller's SC's reply stack when the SC is donated to the callee. -/
theorem ipc.reply_push.ipc {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {X : Set U64} (s : S) (a : A)
    (caller callee r : U64) (can_donate : Bool) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hXc : ExcT X caller)
    (hx : caller ∈ X ∨ ¬ Blocked (L.mem s (stA caller)))
    (hB : BoundInv st T s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z s) (hSg : SgOK st Ω Sg s)
    (hcl : caller ∈ T) (hcq : (L.mem s (inqA caller) &&& sched.Q_QUEUED) = 0#u64)
    (hcr : (L.mem s (inqA caller) &&& sched.Q_RELEASE) = 0#u64) (hca : L.actionW s ≠ caller)
    (hci : L.idleW s ≠ caller)
    (hcold : L.mem s (stA caller) ≠ sched.TS_BLOCKED_ON_REPLY ∧ L.mem s (stA caller) ≠ sched.TS_BLOCKED_ON_RECV)
    (hr : r ∈ Rp) (hr00 : r ≠ 0#u64) (hr0 : L.mem s (rTcbA r) = 0#u64)
    (hce : callee ∈ T) (hne : callee ≠ caller) (heq : (L.mem s (inqA callee) &&& sched.Q_QUEUED) = 0#u64)
    (her : (L.mem s (inqA callee) &&& sched.Q_RELEASE) = 0#u64) (hea : L.actionW s ≠ callee) :
    ipc.reply_push st ar s a caller callee r can_donate ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z s' ∧
      ∀ y ∈ T, y ≠ caller → L.mem s' (stA y) = L.mem s (stA y) ⦄ := by
  have hT := h.tcbs
  have hO := hX.1
  have hsub := hSg.sub
  obtain ⟨hrΩ, hcΩ⟩ := objs_omega hO hsub
  unfold ipc.reply_push
  step with obj.Tcb.sc.spec as ⟨i, ei⟩
  step with obj.Reply.set_tcb.spec as ⟨s1, e1⟩
  subst e1
  refine WP.spec_bind (sched.set_blocked_on_reply.ipc s caller r Q R h hXc hx hB hX hS hSg hcl hcq hcr hca
    hcold hr hr00 hr0) ?_
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
  have ok2 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z s2 ∧ ∀ y ∈ T, y ≠ caller → L.mem s2 (stA y) = L.mem s (stA y) :=
    ⟨⟨⟨Q, R, h2⟩, hB2, hX2, hS2, hSg2⟩, st2⟩
  step with obj.Sc.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 ok2
  rename_i hb
  have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
  have hci0 : L.mem s (scA caller) ≠ 0#u64 := by rw [← ei]; exact hi0
  obtain ⟨hiS, hitc, hicore⟩ := hX.2.2.bound caller hcl hci0
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
      have pre : ∀ (s3 : S), SchedQueuesInv st T Cs Ω H s3 Q R → BoundInv st T s3 → XInv st T Cs Ω Sg Rp Scs Nt Z s3 →
          SCsOK st T Ω Sg Scs Z s3 → SgOK st Ω Sg s3 →
          (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
            L.mem s3 (core.num.U64.wrapping_add y K) = L.mem s2 (core.num.U64.wrapping_add y K)) →
          (L.actionW s3 = L.actionW s2) → L.idleW s3 = L.idleW s2 →
          (do
            let s4 ← obj.Reply.set_prev st r s3 i2
            let s5 ← obj.Sc.set_reply st i s4 r
            let s6 ← obj.Reply.set_next st r s5 i true
            schedcontext.donate st ar s6 a i callee) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z s' ∧
              ∀ y ∈ T, y ≠ caller → L.mem s' (stA y) = L.mem s (stA y) ⦄ := by
        intro s3 h3 hB3 hX3 hS3 hSg3 f3 a3 i3
        obtain ⟨r32, rt0, rp8, rn16⟩ := rp_facts hO hr
        have ri : ∀ c ∈ Scs, r.val + 32 ≤ c.val ∨ c.val + 2 ^ Z c ≤ r.val := hO.rpSc r hr
        have rr : ∀ r' ∈ Rp, r'.val % 32 = 0 := fun r' hr' => (hO.rp r' hr').1
        -- `r.prev := i2`
        step with obj.Reply.set_prev.val as ⟨s4, e4⟩
        obtain ⟨h4, hB4, hX4, hS4, hSg4, a4, -, i4, f4, -⟩ := link_all (w := i2 &&& ~~~1#u64) h3 hB3 hX3 hS3 hSg3
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
        rw [← e4] at h4 hB4 hX4 hS4 hSg4 a4 i4 f4
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
          (fun _ _ _ _ => hr)
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
        rw [← e6] at h6 hB6 hX6 hS6 hSg6 a6 i6 f6
        -- the donation
        have F : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → L.mem s6 (core.num.U64.wrapping_add y K) =
            L.mem s2 (core.num.U64.wrapping_add y K) := fun y hy K hK hK8 =>
          ((f6 y hy K hK hK8).trans ((f5 y hy K hK hK8).trans (f4 y hy K hK hK8))).trans (f3 y hy K hK hK8)
        have ea6 : L.actionW s6 = L.actionW s2 := (a6.trans (a5.trans a4)).trans a3
        have ei6 : L.idleW s6 = L.idleW s2 := (i6.trans (i5.trans i4)).trans i3
        refine WP.spec_mono (schedcontext.donate.ipc hA s6 a i callee caller Q R h6 hB6 hX6 hS6 hSg6 hcl ?_ hi0
          ⟨?_, ?_, ?_⟩ ?_ hce ?_ ?_ ?_ ?_ hne) fun r' hh => ?_
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
          refine ⟨hh.1, fun y hy hyc => ?_⟩
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
        rw [← e3] at h3 hB3 hX3 hS3 hSg3 a3 i3 f3
        exact pre s3 h3 hB3 hX3 hS3 hSg3 f3 a3 i3
      · try simp only [Aeneas.Std.bind_ok]
        exact pre s2 h2 hB2 hX2 hS2 hSg2 (fun _ _ _ _ _ => rfl) rfl rfl
    · exact (WP.spec_ok _).2 ok2
  · exact (WP.spec_ok _).2 ok2

/-! ## `unblock_sporadic` -/

/-- `unblock_sporadic` (the sporadic SC of `t`, unless it is the current SC,
gets its refills unblocked) keeps the invariants and the TCB fields. -/
theorem endpoint.unblock_sporadic.all {X : Set U64} (s : S) (t : obj.Tcb) {Q : U64 → U64 → List U64}
    {R : U64 → List U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T s)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T) :
    endpoint.unblock_sporadic st s t ⦃ s' => SchedQueuesInvX st T Cs Ω H X s' Q R ∧ BoundInv st T s' ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧ SCsOK st T Ω Sg Scs Z s' ∧ SgOK st Ω Sg s' ∧
      L.actionW s' = L.actionW s ∧ L.curW s' = L.curW s ∧ L.idleW s' = L.idleW s ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ r ∈ Rp, L.mem s' (rTcbA r) = L.mem s (rTcbA r)) ⦄ := by
  have hT := h.tcbs
  have hsub := hSg.sub
  have triv : SchedQueuesInvX st T Cs Ω H X s Q R ∧ BoundInv st T s ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z s ∧ SCsOK st T Ω Sg Scs Z s ∧ SgOK st Ω Sg s ∧
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
    have hi0 : i ≠ 0#u64 := b1_post hb1
    have hbt : L.mem s (scA t) ≠ 0#u64 := by rw [← i_post]; exact hi0
    obtain ⟨hiS, -, -⟩ := hX.2.2.bound t ht hbt
    rw [← i_post] at hiS
    have hW : RefillsWF st s i (Z i) := by
      have := (hS.bound t ht hbt).1; rw [← i_post] at this; exact this
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
          (hX.tn (TmFr.of_ring h hX hsub hiS w3))
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
    {R : U64 → List U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T s)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T)
    (i_post : i = L.mem s (scA t)) (hi0 : i ≠ 0#u64) :
    sporadic.unblock_check st s i ⦃ s' => SchedQueuesInvX st T Cs Ω H X s' Q R ∧ BoundInv st T s' ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧ SCsOK st T Ω Sg Scs Z s' ∧ SgOK st Ω Sg s' ∧
      L.actionW s' = L.actionW s ∧ L.curW s' = L.curW s ∧ L.idleW s' = L.idleW s ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ r ∈ Rp, L.mem s' (rTcbA r) = L.mem s (rTcbA r)) ⦄ := by
  have hT := h.tcbs
  have hsub := hSg.sub
  have hbt : L.mem s (scA t) ≠ 0#u64 := by rw [← i_post]; exact hi0
  obtain ⟨hiS, -, -⟩ := hX.2.2.bound t ht hbt
  rw [← i_post] at hiS
  have hW : RefillsWF st s i (Z i) := by
    have := (hS.bound t ht hbt).1; rw [← i_post] at this; exact this
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
      (hX.tn (TmFr.of_ring h hX hsub hiS w3))
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
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T) (hv : ¬ Blocked v)
    (hvr : v ≠ sched.TS_BLOCKED_ON_REPLY ∧ v ≠ sched.TS_BLOCKED_ON_RECV)
    (hx : t ∈ X ∨ ¬ Blocked (L.mem s (stA t)))
    (hnoref : ∀ r ∈ Rp, L.mem s (rTcbA r) ≠ t)
    (hq : (∀ c ∈ Cs, ∀ p : U64, p.val < 256 → t ∈ Q c p → Runnable v) ∧ (∀ c ∈ Cs, t ∈ R c → Runnable v) ∧
      (L.actionW s = t → Runnable v)) :
    sched.set_thread_state st s t v ⦃ s' => SchedQueuesInvX st T Cs Ω H {y | y ∈ X ∧ y ≠ t} s' Q R ∧
      BoundInv st T s' ∧ XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧ SCsOK st T Ω Sg Scs Z s' ∧ SgOK st Ω Sg s' ∧
      L.mem s' (stA t) = v ∧ KeepT st T Cs Rp Scs Nt t s s' ⦄ := by
  refine WP.spec_mono (WP.spec_and (sched.set_thread_state.inv s t v Q R h ht hv hx hq)
    (sched.set_thread_state.state s t v Q R h ht hX.1 hSg.sub)) fun s' ⟨h', e', k'⟩ => ?_
  exact ⟨h', hB.keepT h k' (by rw [e']; exact hv), hX.keepT k' (by rw [e']; exact hvr)
    (fun r hr e => absurd e (hnoref r hr)), hS.keepT hX k',
    ⟨hSg.sub, fun b hb => by rw [k'.ksb]; exact hSg.ks b hb, fun o h1 h2 => by rw [k'.ksb]; exact hSg.ksΩ o h1 h2⟩,
    e', k'⟩

/-! ## Endpoint dequeue of the head -/

/-- `BoundInv`, `XInv`, `SCsOK` and `SgOK` across a change that keeps the TCB
fields (other than the `Ep` links), the words of `Ω` and the node words. -/
theorem frame_bx {X : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z s) (hSg : SgOK st Ω Sg s)
    (fld : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K))
    (om : ∀ a ∈ Ω, L.mem s' a = L.mem s a)
    (nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem s' (L.nodeAt s' (L.cpu s') o) = L.mem s (L.nodeAt s (L.cpu s) o))
    (hk : L.ksb s' = L.ksb s) (htm : TmFr st T Cs Nt s s') :
    BoundInv st T s' ∧ XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧ SCsOK st T Ω Sg Scs Z s' ∧ SgOK st Ω Sg s' ∧
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
  refine ⟨hB.mk' scf (fun y hy hf => Or.inl (by rw [← iqf y hy]; exact hf))
      (fun y hy hf => Or.inr (Or.inl (by rw [← iqf y hy]; exact hf)))
      (fun haT => by rw [ea] at haT ⊢; exact ⟨haT, hB.act haT⟩) (by rw [ei]; exact ⟨h.idleT, hB.idle⟩)
      (fun h0 => by rw [ea] at h0; rw [ec]; exact ⟨h.curT, hB.resume h0⟩)
      (hB.nb ei (by rw [stA_eq]; exact fld (L.idleW s) h.idleT _ (by simp) (by simp) (by simp) (by simp))),
    hX.keep (fun r hr => ⟨om _ (hrΩ r hr).1, om _ (hrΩ r hr).2.1, om _ (hrΩ r hr).2.2⟩)
      (fun c hc => ⟨om _ (hcΩ c hc).1, om _ (hcΩ c hc).2.1⟩) scf
      (fun y hy => fld y hy _ (by simp) (by simp) (by simp) (by simp))
      (fun y hy => by rw [stA_eq]; exact fld y hy _ (by simp) (by simp) (by simp) (by simp))
      (by rw [ecs]; exact hX.2.2.cur) (fun c hc => om _ (hSg.sub _ (hX.1.repW c hc)))
      (fun y hy => fld y hy _ (by simp) (by simp) (by simp) (by simp)) (fun n hn => om _ (hSg.sub _ (hX.1.ntW n hn)))
      (hX.tn htm) (fun c hc => om _ (hSg.sub _ (hX.1.snW c hc)))
      (fun y hy => fld y hy _ (by simp) (by simp) (by simp) (by simp)) (fun c hc => om _ (hSg.sub _ (hX.1.syW c hc))),
    SCsOK.keep hS hX hk scf ecs (fun c hc => ⟨om _ (hcΩ c hc).2.2.1, om _ (hcΩ c hc).2.2.2.1, om _ (hcΩ c hc).2.2.2.2⟩),
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

/-- The footprint of the message transfer, as a hypothesis on the opaque
`do_ipc_transfer`. -/
def XferOK (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A) (T U : Set U64) : Prop :=
  ∀ (s : S) (a : A) (snd ep badge : U64) (grant : Bool) (rcv : U64),
    ipc.do_ipc_transfer st ar s a snd ep badge grant rcv ⦃ s' => WritesIn st s s' (XferFoot T U) ⦄

/-- seL4 `receiveIPC`'s end on a sending endpoint: the head sender is
dequeued, the message transferred, and the sender either becomes blocked on
the receiver's reply (a call, with the reply bookkeeping and SC donation),
inactive, or running. -/
theorem endpoint.receive_from_sender.ipc {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {U : Set U64} (hxf : XferOK st ar T U) (s : S) (a : A) (thread e reply : U64)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z s) (hSg : SgOK st Ω Sg s) (hU : UserOK st T Cs Ω H U s)
    (hc : CanBlock st T s thread)
    (hH : H e = some .ep) (hst : L.epState s e ≠ 0#u64 ∧ L.epState s e ≠ 2#u64)
    (hr : reply ≠ 0#u64 → reply ∈ Rp ∧ (L.mem s (rTcbA reply) = 0#u64 ∨ L.mem s (rTcbA reply) = thread)) :
    endpoint.receive_from_sender st ar s a thread e reply ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z s' ⦄ := by
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
  have hdi : L.idleW s ≠ hd := fun e' => hB.idleNB (by rw [e', hds]; exact Or.inl rfl)
  -- the reply object is unused
  have hr' : reply ≠ 0#u64 → reply ∈ Rp ∧ L.mem s (rTcbA reply) = 0#u64 := fun h0 => by
    obtain ⟨h1, h2⟩ := hr h0
    refine ⟨h1, h2.resolve_right fun e' => hX.noref (hT _ ht) hc.nrp (fun e2 => hc.nb (Or.inr (Or.inl e2))) _ h1 e'⟩
  unfold endpoint.receive_from_sender
  step with endpoint.get_queue.spec as ⟨q, eq⟩
  subst eq
  have hdq := endpoint.ep_dequeue.inv s hd Q R h hdT (by simp) (Or.inl hds)
  rw [hbe] at hdq
  refine WP.spec_bind hdq ?_
  rintro s1 ⟨h1, f1, o1, n1, k1, c1, nc1⟩
  obtain ⟨hB1, hX1, hS1, hSg1, ea1, ec1, ei1⟩ := frame_bx h hB hX hS hSg f1 o1 n1 k1
    ⟨k1, fun y hy K a b c => f1 y hy K (by omega) c (by omega) (by omega),
      fun c hc o ho => nc1 c hc o (by omega) (by omega), fun n' hn' => o1 _ (hSg.sub _ (hX.1.ntB n' hn').2)⟩
  step with obj.Tcb.block_badge.any as ⟨badge, _⟩
  step with obj.Tcb.block_flags.any as ⟨flags, _⟩
  simp only [lift, Aeneas.Std.bind_ok]
  refine WP.spec_bind (hxf s1 a hd e badge _ thread) ?_
  rintro s2 hw2
  obtain ⟨h2, hB2, hX2, hS2, hSg2, ea2, ec2, ei2, ecs2, f2, o2⟩ :=
    xfer_all h1 hB1 hX1 hS1 hSg1 (hU.ksb k1) hw2
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
  obtain ⟨dq, dr, da⟩ := blocked_out h3 hdT (by rw [hds3]; exact blocked_not_runnable (Or.inl rfl))
  have hXc : ExcT {y | y ∈ (∅ : Set U64) ∨ y = hd} hd := fun y hy => by simpa using hy
  have hx3 : hd ∈ {y | y ∈ (∅ : Set U64) ∨ y = hd} := Or.inr rfl
  have rt3 : ∀ r ∈ Rp, L.mem s3 (rTcbA r) = L.mem s (rTcbA r) := fun r hr0 =>
    (r3 r hr0).trans ((o2 _ (hSg.sub _ (hX.1.tcbW hr0))).trans (o1 _ (hSg.sub _ (hX.1.tcbW hr0))))
  have E1 : ∀ cd : Bool, reply ≠ 0#u64 → ipc.reply_push st ar s3 a hd thread reply cd ⦃ s' _ =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z s' ⦄ := fun cd h0 =>
    WP.spec_mono (ipc.reply_push.ipc hA s3 a hd thread reply cd Q R h3 hXc (Or.inl hx3) hB3 hX3 hS3 hSg3 hdT dq dr da
      (by rw [ei]; exact hdi) (by rw [hds3]; exact send_ne) (hr' h0).1 h0 (by rw [rt3 _ (hr' h0).1]; exact (hr' h0).2)
      ht (Ne.symm hdt) (by rw [iq3 _ ht]; exact hc.nq) (by rw [iq3 _ ht]; exact hc.nr) (by rw [ea]; exact hc.na))
      fun r hh => by obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at hh ⊢; exact hh.1
  have E1' : reply ≠ 0#u64 → (do
      let i3 ← obj.Tcb.sc st hd s3
      let can_donate ← if (i3 != 0#u64) = true then ok (ftype != fl4_abi.consts.fault.Timeout) else ok false
      ipc.reply_push st ar s3 a hd thread reply can_donate) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z s' ⦄ := by
    intro h0
    step with obj.Tcb.sc.spec as ⟨i3, _⟩
    split <;> (try simp only [Aeneas.Std.bind_ok]) <;> exact E1 _ h0
  have E2 : (do
      let s4 ← sched.set_thread_state st s3 hd sched.TS_INACTIVE
      ok (s4, a)) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z s' ⦄ := by
    refine WP.spec_bind (sts_all s3 hd _ Q R h3 hB3 hX3 hS3 hSg3 hdT not_blocked_inactive inactive_ne
      (Or.inl hx3) (hX3.noref (h3.tcbs _ hdT) (by rw [hds3]; exact send_ne.1) (by rw [hds3]; exact send_ne.2))
      ⟨fun c hc' p hp hm => absurd hm (h3.notQ hdT dq hc' hp),
        fun c hc' hm => absurd hm (h3.notR hdT dr hc'), fun e' => absurd e' da⟩) fun s4 hh => ?_
    obtain ⟨h4, hB4, hX4, hS4, hSg4, -, -⟩ := hh
    exact (WP.spec_ok _).2 ⟨⟨Q, R, h4.congrX empty_congr'⟩, hB4, hX4, hS4, hSg4⟩
  have E3 : (do
      let s4 ← sched.set_thread_state st s3 hd sched.TS_RUNNING
      let s5 ← sched.possible_switch_to st s4 hd
      ok (s5, a)) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z s' ⦄ := by
    refine WP.spec_bind (sts_all s3 hd _ Q R h3 hB3 hX3 hS3 hSg3 hdT not_blocked_running running_ne
      (Or.inl hx3) (hX3.noref (h3.tcbs _ hdT) (by rw [hds3]; exact send_ne.1) (by rw [hds3]; exact send_ne.2))
      ⟨fun _ _ _ _ _ => runnable_running, fun _ _ _ => runnable_running,
        fun _ => runnable_running⟩) fun s4 hh => ?_
    obtain ⟨h4, hB4, hX4, hS4, hSg4, e4, -⟩ := hh
    have h4' := h4.congrX empty_congr'
    refine WP.spec_bind (sched.possible_switch_to.sch s4 hd Q R h4' hB4 hSg4 hdT (by rw [e4]; exact runnable_running))
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
    (R : U64 → List U64) (h4 : SchedQueuesInvX st T Cs Ω H X s4 Q R) (hB4 : BoundInv st T s4)
    (hX4 : XInv st T Cs Ω Sg Rp Scs Nt Z s4) (hS4 : SCsOK st T Ω Sg Scs Z s4) (hSg4 : SgOK st Ω Sg s4) (hdT : hd ∈ T)
    (hXc : ExcT X hd) (hx : hd ∈ X ∨ ¬ Blocked (L.mem s4 (stA hd))) (hnr : ∀ r ∈ Rp, L.mem s4 (rTcbA r) ≠ hd) :
    (do
      let s5 ← sched.set_thread_state st s4 hd sched.TS_RUNNING
      let s6 ← endpoint.unblock_sporadic st s5 hd
      let s7 ← sched.possible_switch_to st s6 hd
      ok (s7, a1)) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z s' ⦄ := by
  refine WP.spec_bind (sts_all s4 hd _ Q R h4 hB4 hX4 hS4 hSg4 hdT not_blocked_running running_ne hx hnr
    ⟨fun _ _ _ _ _ => runnable_running, fun _ _ _ => runnable_running, fun _ => runnable_running⟩) fun s5 hh => ?_
  obtain ⟨h5, hB5, hX5, hS5, hSg5, e5, -⟩ := hh
  have h5' := h5.congrX (excT_congr hXc)
  refine WP.spec_bind (endpoint.unblock_sporadic.all s5 hd h5' hB5 hX5 hS5 hSg5 hdT) fun s6 hh => ?_
  obtain ⟨h6, hB6, hX6, hS6, hSg6, -, -, -, f6, -⟩ := hh
  have e6 : L.mem s6 (stA hd) = sched.TS_RUNNING := by
    rw [stA_eq, f6 hd hdT _ (by simp) (by simp), ← stA_eq]; exact e5
  refine WP.spec_bind (sched.possible_switch_to.sch s6 hd Q R h6 hB6 hSg6 hdT (by rw [e6]; exact runnable_running))
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
`t.sc != 0`. -/
theorem endpoint.send_ipc.ipc {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {U : Set U64}
    (hxf : XferOK st ar T U) (s : S) (a : A) (blocking do_call : Bool)
    (badge : U64) (can_grant can_grant_reply can_donate : Bool) (t e : U64)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z s) (hSg : SgOK st Ω Sg s) (hU : UserOK st T Cs Ω H U s)
    (hc : CanBlock st T s t) (hdon : can_donate = true → L.mem s (scA t) ≠ 0#u64)
    (hH : H e = some .ep) :
    endpoint.send_ipc st ar s a blocking do_call badge can_grant can_grant_reply can_donate t e
      ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z s' ⦄ := by
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
  refine WP.spec_bind hdq ?_
  rintro s1 ⟨h1, f1, o1, n1, k1, c1, nc1⟩
  obtain ⟨hB1, hX1, hS1, hSg1, ea1, ec1, ei1⟩ := frame_bx h hB hX hS hSg f1 o1 n1 k1
    ⟨k1, fun y hy K a b c => f1 y hy K (by omega) c (by omega) (by omega),
      fun c hc o ho => nc1 c hc o (by omega) (by omega), fun n' hn' => o1 _ (hSg.sub _ (hX.1.ntB n' hn').2)⟩
  refine WP.spec_bind (hxf s1 a t e badge can_grant hd) ?_
  rintro s2 hw2
  obtain ⟨h2, hB2, hX2, hS2, hSg2, ea2, ec2, ei2, ecs2, f2, o2⟩ := xfer_all h1 hB1 hX1 hS1 hSg1 (hU.ksb k1) hw2
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
  -- the reply object leaves the receiver
  refine WP.spec_bind (Pₘ := fun s3 => ∃ X3 : Set U64, SchedQueuesInvX st T Cs Ω H X3 s3 Q R ∧ BoundInv st T s3 ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z s3 ∧ SCsOK st T Ω Sg Scs Z s3 ∧ SgOK st Ω Sg s3 ∧ ExcT X3 hd ∧
      (hd ∈ X3 ∨ ¬ Blocked (L.mem s3 (stA hd))) ∧ ¬ Runnable (L.mem s3 (stA hd)) ∧
      (hd ∈ X3 → L.mem s3 (replyA hd) = 0#u64) ∧ (hd ∉ X3 → L.mem s3 (stA hd) = sched.TS_INACTIVE) ∧
      ((i != 0#u64) = true → hd ∉ X3 ∧ i ∈ Rp ∧ L.mem s3 (rTcbA i) = 0#u64) ∧
      L.mem s3 (stA t) = L.mem s (stA t) ∧ L.mem s3 (inqA t) = L.mem s (inqA t) ∧
      L.mem s3 (scA t) = L.mem s (scA t) ∧ L.actionW s3 ≠ t ∧ L.idleW s3 = L.idleW s) ?_ ?_
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
      refine ⟨_, h3, hB2.keepT h2 k3 (by rw [e3]; exact not_blocked_inactive), hX2.keepT k3 (by rw [e3]; exact inactive_ne) hclr, hS2.keepT hX2 k3,
        ⟨hsub, fun b hb => by rw [k3.ksb]; exact hSg2.ks b hb, fun o h1' h2' => by rw [k3.ksb]; exact hSg2.ksΩ o h1' h2'⟩,
        fun y hy => ?_, Or.inr (by rw [e3]; exact not_blocked_inactive), by rw [e3]; exact not_runnable_inactive,
        fun hm => absurd rfl hm.2, fun _ => e3, fun _ => ⟨fun hm => hm.2 rfl, hiR, z3⟩,
        (k3.stf ht (Ne.symm hdt)).trans (Fst t ht), (k3.inqf ht).trans (Fiq t ht), (k3.scf ht).trans (Fsc t ht),
        ?_, k3.idleW.trans ei2'⟩
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
        Fst t ht, Fiq t ht, Fsc t ht, by rw [ea2']; exact hc.na, ei2'⟩
  rintro s3 ⟨X3, h3, hB3, hX3, hS3, hSg3, hXc3, hx3, hnr3, hz3, hin3, hpu3, st3, iq3, sc3, na3, ei3⟩
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
      BoundInv st T r.1 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ SCsOK st T Ω Sg Scs Z r.1 ∧ SgOK st Ω Sg r.1 ∧
      ExcT X4 hd ∧ (hd ∈ X4 ∨ ¬ Blocked (L.mem r.1 (stA hd))) ∧ ∀ r' ∈ Rp, L.mem r.1 (rTcbA r') ≠ hd) ?_ ?_
  rotate_left
  · rintro ⟨s4, a1⟩ ⟨X4, ⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4, hXc4, hx4, hnr4⟩
    try simp only [WP.uncurry'_pair]
    exact send_tail s4 a1 hd Q4 R4 h4 hB4 hX4 hS4 hSg4 hdT hXc4 hx4 hnr4
  have Ppush : ∀ cd : Bool, (i != 0#u64) = true → ipc.reply_push st ar s3 a t hd i cd ⦃ r => ∃ X4 : Set U64,
      (∃ Q4 R4, SchedQueuesInvX st T Cs Ω H X4 r.1 Q4 R4) ∧
      BoundInv st T r.1 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ SCsOK st T Ω Sg Scs Z r.1 ∧ SgOK st Ω Sg r.1 ∧
      ExcT X4 hd ∧ (hd ∈ X4 ∨ ¬ Blocked (L.mem r.1 (stA hd))) ∧ ∀ r' ∈ Rp, L.mem r.1 (rTcbA r') ≠ hd ⦄ := by
    intro cd hi
    obtain ⟨hdX, hiR, hiz⟩ := hpu3 hi
    have hi0 : i ≠ 0#u64 := by simpa using hi
    refine WP.spec_mono (ipc.reply_push.ipc hA s3 a t hd i cd Q R h3
      (fun y hy => absurd (hXc3 y hy ▸ hy) hdX) (Or.inr hnb3) hB3 hX3 hS3 hSg3 ht htq3 htr3 na3 hidle3 hcold3
      hiR hi0 hiz hdT hdt dq dr da) fun r hh => ?_
    obtain ⟨s4, a4⟩ := r
    simp only [WP.uncurry'_pair] at hh
    obtain ⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, st4⟩ := hh
    have e4 : L.mem s4 (stA hd) = sched.TS_INACTIVE := (st4 hd hdT hdt).trans (hin3 hdX)
    exact ⟨∅, ⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4, fun y hy => absurd hy (Set.notMem_empty _),
      Or.inr (by rw [e4]; exact not_blocked_inactive),
      hX4.noref hdta (by rw [e4]; exact inactive_ne.1) (by rw [e4]; exact inactive_ne.2)⟩
  have Pinact : (do
      let s5 ← sched.set_thread_state st s3 t sched.TS_INACTIVE
      ok (s5, a)) ⦃ r => ∃ X4 : Set U64, (∃ Q4 R4, SchedQueuesInvX st T Cs Ω H X4 r.1 Q4 R4) ∧
      BoundInv st T r.1 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ SCsOK st T Ω Sg Scs Z r.1 ∧ SgOK st Ω Sg r.1 ∧
      ExcT X4 hd ∧ (hd ∈ X4 ∨ ¬ Blocked (L.mem r.1 (stA hd))) ∧ ∀ r' ∈ Rp, L.mem r.1 (rTcbA r') ≠ hd ⦄ := by
    refine WP.spec_bind (sts_all s3 t _ Q R h3 hB3 hX3 hS3 hSg3 ht not_blocked_inactive inactive_ne (Or.inr hnb3)
      hnt3 ⟨fun c hc' p hp hm => absurd hm (h3.notQ ht htq3 hc' hp), fun c hc' hm => absurd hm (h3.notR ht htr3 hc'),
        fun e' => absurd e' na3⟩) fun s4 hh => ?_
    obtain ⟨h4, hB4, hX4, hS4, hSg4, -, k4⟩ := hh
    refine (WP.spec_ok _).2 ⟨{y | y ∈ X3 ∧ y ≠ t}, ⟨Q, R, h4⟩, hB4, hX4, hS4, hSg4,
      fun y hy => hXc3 y hy.1, ?_, fun r hr => ?_⟩
    · rcases hx3 with hm | hnb
      · exact Or.inl ⟨hm, hdt⟩
      · exact Or.inr (by rw [k4.stf hdT hdt]; exact hnb)
    · rcases k4.rtcb r hr with e' | ⟨-, e'⟩
      · rw [e']; exact hnd3 r hr
      · rw [e']; exact fun e2 => hdta.ne0 (by rw [← e2]; rfl)
  have Pok : (ok (s3, a) : Result (S × A)) ⦃ r => ∃ X4 : Set U64, (∃ Q4 R4, SchedQueuesInvX st T Cs Ω H X4 r.1 Q4 R4) ∧
      BoundInv st T r.1 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ SCsOK st T Ω Sg Scs Z r.1 ∧ SgOK st Ω Sg r.1 ∧
      ExcT X4 hd ∧ (hd ∈ X4 ∨ ¬ Blocked (L.mem r.1 (stA hd))) ∧ ∀ r' ∈ Rp, L.mem r.1 (rTcbA r') ≠ hd ⦄ :=
    (WP.spec_ok _).2 ⟨X3, ⟨Q, R, h3⟩, hB3, hX3, hS3, hSg3, hXc3, hx3, hnd3⟩
  have Pdon : can_donate = true → (do
      let i2 ← obj.Tcb.sc st hd s3
      if i2 = 0#u64 then do
          let i3 ← obj.Tcb.sc st t s3
          schedcontext.donate st ar s3 a i3 hd
        else ok (s3, a)) ⦃ r => ∃ X4 : Set U64, (∃ Q4 R4, SchedQueuesInvX st T Cs Ω H X4 r.1 Q4 R4) ∧
      BoundInv st T r.1 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ SCsOK st T Ω Sg Scs Z r.1 ∧ SgOK st Ω Sg r.1 ∧
      ExcT X4 hd ∧ (hd ∈ X4 ∨ ¬ Blocked (L.mem r.1 (stA hd))) ∧ ∀ r' ∈ Rp, L.mem r.1 (rTcbA r') ≠ hd ⦄ := by
    intro hcd
    step with obj.Tcb.sc.spec as ⟨i2, ei2⟩
    split
    · rename_i hi2
      step with obj.Tcb.sc.spec as ⟨i3, ei3'⟩
      refine WP.spec_mono (schedcontext.donate.ipc hA s3 a i3 hd t Q R h3 hB3 hX3 hS3 hSg3 ht ei3'.symm
        (by rw [ei3', sc3]; exact hdon hcd) ⟨htq3, htr3, na3⟩ hidle3 hdT (by rw [← ei2, hi2]) dq dr da hdt)
        fun r hh => ?_
      obtain ⟨s4, a4⟩ := r
      simp only [WP.uncurry'_pair] at hh
      obtain ⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, st4, rp4⟩ := hh
      refine ⟨X3, ⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4, hXc3, ?_, ?_⟩
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
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z s) (hSg : SgOK st Ω Sg s) (hn : H n = some .ntfn) (hact : L.epState s n = 2#u64) :
    SchedQueuesInvX st T Cs Ω H X
        (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64))) Q R ∧
      BoundInv st T (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64))) ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64))) ∧
      SCsOK st T Ω Sg Scs Z (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64))) ∧
      SgOK st Ω Sg (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64))) ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
        L.mem (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64)))
          (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ a ∈ Ω, L.mem (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64))) a =
        L.mem s a) ∧
      L.actionW (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64))) = L.actionW s ∧
      L.idleW (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64))) = L.idleW s := by
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
  obtain ⟨b1, b2, b3, b4, ea, -, ei⟩ := frame_bx h hB hX hS hSg kf kΩ (fun o h1 h2 => kn o h1 h2) hw.1
    (TmFr.of_epfoot h hEW he hWT hw hX.1 hSg.sub)
  exact ⟨hinv, b1, b2, b3, b4, kf, kΩ, ea, ei⟩

/-- `donate` of an SC bound to no thread. -/
theorem schedcontext.donate.unbound {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {X : Set U64}
    (s : S) (a : A) (sc dst : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z s) (hSg : SgOK st Ω Sg s) (hdst : dst ∈ T)
    (hdq : (L.mem s (inqA dst) &&& sched.Q_QUEUED) = 0#u64) (hdr : (L.mem s (inqA dst) &&& sched.Q_RELEASE) = 0#u64)
    (hsc : sc ∈ Scs) (hsc0 : sc ≠ 0#u64) (htc0 : L.mem s (scTcbA sc) = 0#u64)
    (hcore : L.mem s (scCoreA sc) ∈ Cs) (hin : SCin st s Sg sc (Z sc)) :
    schedcontext.donate st ar s a sc dst ⦃ s' _ => BlkOKX st T Cs Ω H Sg Rp Scs Nt Z X s' ∧
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
    exact donate_tail hA s a sc dst Q R h hB hX hS hSg hdst hdq hdr hsc hsc0 hnb hcore hin hdisj
  · rename_i hb; exfalso; exact hb (by rw [eb, ei, htc0]; rfl)

/-- seL4 `maybeDonateSchedContext`: an unbound notification SC goes to the
unbound receiver, which resumes. -/
theorem notification.maybe_donate_sched_context.ipc {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (t n : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T)
    (htq : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64) (htr : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64)
    (hta' : L.actionW s ≠ t)
    (hns : L.mem s (ntfnScA n) ≠ 0#u64 → L.mem s (scTcbA (L.mem s (ntfnScA n))) = 0#u64 →
      L.mem s (scA t) = 0#u64 → L.mem s (ntfnScA n) ∈ Scs ∧ SCin st s Sg (L.mem s (ntfnScA n)) (Z (L.mem s (ntfnScA n))) ∧
        L.mem s (scCoreA (L.mem s (ntfnScA n))) ∈ Cs) :
    notification.maybe_donate_sched_context st ar s a t n ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z s' ⦄ := by
  have ok0 : (ok (s, a) : Result (S × A)) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z s' ⦄ :=
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
      obtain ⟨hS1, hin1, hcore1⟩ := hns (by rw [← ei1]; exact hi10) (by rw [← ei1]; exact htc0) (by rw [← ei, hi])
      rw [← ei1] at hS1 hin1 hcore1
      refine WP.spec_bind (schedcontext.donate.unbound hA s a i1 t Q R h hB hX hS hSg ht htq htr hS1 hi10 htc0
        hcore1 hin1) ?_
      rintro ⟨s4, a4⟩ ⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, -, -, -, sc4, tc4, ea4⟩
      try simp only [WP.uncurry'_pair]
      refine WP.spec_mono (schedcontext.resume.all hA s4 a4 i1 Q4 R4 h4 hB4 hX4 hSg4 fun _ _ => ?_) ?_
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
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T) :
    SchedQueuesInv st T Cs Ω H (L.wr s (core.num.U64.wrapping_add t 256#u64) v) Q R ∧
      BoundInv st T (L.wr s (core.num.U64.wrapping_add t 256#u64) v) ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z (L.wr s (core.num.U64.wrapping_add t 256#u64) v) ∧
      SCsOK st T Ω Sg Scs Z (L.wr s (core.num.U64.wrapping_add t 256#u64) v) ∧
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
objects' words and holds an SC object (or nothing). -/
theorem notification.complete_signal.ipc {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (n t : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T)
    (htq : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64) (htr : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64)
    (hta' : L.actionW s ≠ t) (hn : H n = some .ntfn) (hnΩ : ntfnScA n ∈ Ω)
    (hns : L.mem s (ntfnScA n) ≠ 0#u64 → L.mem s (ntfnScA n) ∈ Scs ∧
      SCin st s Sg (L.mem s (ntfnScA n)) (Z (L.mem s (ntfnScA n))) ∧ L.mem s (scCoreA (L.mem s (ntfnScA n))) ∈ Cs) :
    notification.complete_signal st ar s a n t ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z s' ⦄ := by
  have hT := h.tcbs
  have hta := hT t ht
  have hN := h.nodes _ h.cur
  have ok0 : (ok (s, a) : Result (S × A)) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z s' ⦄ :=
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
  set s1 := L.wr s (core.num.U64.wrapping_add t 256#u64) b1 with hs1
  refine WP.spec_bind (obj.Ntfn.set_state.val s1 n _) fun s2 e2 => ?_
  subst e2
  obtain ⟨h2, hB2, hX2, hS2, hSg2, f2, o2, ea2, ei2⟩ := ntfn_idle_all h1 hB1 hX1 hS1 hSg1 hn hact1
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
  refine WP.spec_bind (notification.maybe_donate_sched_context.ipc hA s2 a t n Q R h2 hB2 hX2 hS2 hSg2 ht
    (by rw [iq2]; exact htq) (by rw [iq2]; exact htr) (by rw [ea2']; exact hta') fun h0 _ _ => ?_) ?_
  · rw [hc2] at h0 ⊢
    obtain ⟨c1, c2, c3⟩ := hns h0
    obtain ⟨-, hcΩ⟩ := objs_omega hX.1 hSg.sub
    refine ⟨c1, c2.agree (fun b hb => O b (hSg.sub b hb)), ?_⟩
    rw [O _ (hcΩ _ c1).2.1]; exact c3
  rintro ⟨s3, a1⟩ ⟨⟨Q3, R3, h3⟩, hB3, hX3, hS3, hSg3⟩
  try simp only [WP.uncurry'_pair]
  have ok3 : (ok (s3, a1) : Result (S × A)) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z s' ⦄ :=
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
      · refine WP.spec_bind (sporadic.unblock_check.all s3 t i1 h3 hB3 hX3 hS3 hSg3 ht ei1 (eb2 hb2)) fun s5 hh => ?_
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
    SCin st s Sg (L.mem s (ntfnScA n)) (Z (L.mem s (ntfnScA n))) ∧ L.mem s (scCoreA (L.mem s (ntfnScA n))) ∈ Cs)

/-- A bound notification is well typed (from `ScExtra.bnd`, `ScExtra.nsc`,
`SCsOK.all` and `ScExtra.core`), given that `Nt` are heap notifications. -/
theorem BoundNtfnOK.of_inv {s : S} {t : U64} (hNt : ∀ n ∈ Nt, H n = some .ntfn) (ht : t ∈ T)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z s) (hSg : SgOK st Ω Sg s)
    (hn0 : L.mem s (boundA t) ≠ 0#u64) : BoundNtfnOK st Cs Ω H Sg Scs Z (L.mem s (boundA t)) s := by
  have hn := hX.2.2.bnd t ht hn0
  refine ⟨hNt _ hn, hSg.sub _ (hX.1.ntW _ hn), fun hc0 => ?_⟩
  have hc := hX.2.2.nsc _ hn hc0
  exact ⟨hc, hS.all _ hc, hX.2.2.core _ hc⟩

/-- seL4 `receiveIPC`, all of it: the reply bookkeeping (`take_reply`), the
active bound notification (`complete_signal`), the bound notification's SC
going back (`maybe_return_sched_context`), blocking or polling on an idle or
receiving endpoint, and receiving from a sending endpoint.  Besides the
invariants, only caller-level facts: `t` can block, the cap names a heap
endpoint, a reply cap names a reply object, and `Nt` are heap notifications
(true of the instantiation `Nt := H.ntfns`). -/
theorem endpoint.receive_ipc.ipc {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {U : Set U64}
    (hxf : XferOK st ar T U) (s : S) (a : A) (t : U64) (cap : capability.Cap) (blocking : Bool)
    (reply_cap : capability.Cap) (e : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z s) (hSg : SgOK st Ω Sg s) (hU : UserOK st T Cs Ω H U s)
    (hc : CanBlock st T s t)
    (hptr : capability.Cap.ptr cap = ok e) (hH : H e = some .ep)
    (hcap : ∀ p g, reply_cap = .Reply p g → p ∈ Rp)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) :
    endpoint.receive_ipc st ar s a t cap blocking reply_cap ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z s' ⦄ :=
  endpoint.receive_ipc.inv ar s a t cap blocking reply_cap e Q R h hB hX hS hSg hc hptr hH hcap
    (fun s1 a1 n hok hc1 hn hn0 hst => by
      obtain ⟨⟨Q1, R1, h1⟩, hB1, hX1, hS1, hSg1⟩ := hok
      subst hn
      obtain ⟨hn1, hn2, hn3⟩ := BoundNtfnOK.of_inv hNt hc1.mem hX1 hS1 hSg1 hn0
      exact notification.complete_signal.ipc hA s1 a1 _ t Q1 R1 h1 hB1 hX1 hS1 hSg1 hc1.mem hc1.nq hc1.nr hc1.na
        hn1 hn2 hn3)
    (fun s2 a2 r hok hc2 hr kb ib hs0 hs2 => by
      obtain ⟨⟨Q2, R2, h2⟩, hB2, hX2, hS2, hSg2⟩ := hok
      exact endpoint.receive_from_sender.ipc hA hxf s2 a2 t e r Q2 R2 h2 hB2 hX2 hS2 hSg2 (hU.ksb kb) hc2 hH
        ⟨hs0, hs2⟩ hr)

end

end Fl4Proofs.P1
