/-
P3 (DESIGN.md §9), scheduler: **`switch_to_thread` and
`switch_to_idle_thread` refine l4v's** (`switch_to_thread_refines`,
`switch_to_idle_thread_refines`): the address-space switch is the arch
hypothesis `hvm` (FL4 `vspace::set_vm_root` / `set_kernel_vm_root` against
`arch_switch_to_thread` / `arch_switch_to_idle_thread`, which also restores
the FPU lazily); then the thread is dequeued and becomes current.
`SchedRel.set_cur_thread`: writing the `CUR_THREAD` word (with `CAgreeT`, the
agreement except that word).
-/
import Fl4Proofs.P3.ScSwitch
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- `s'` agrees with `s` on what `SchedCore` reads, except the current thread. -/
structure CAgreeT (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (c : U64) (s s' : S) : Prop where
  ksb : L.ksb s' = L.ksb s
  cpu : L.cpu s' = L.cpu s
  node : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 16 → o.val ≠ 56 → o.val ≠ 40 → o.val ≠ 48 → o.val ≠ 24 → o.val ≠ 0 →
    L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o)
  tcb : ∀ y ∈ T, ∀ K, CoreField K → L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)

theorem CAgreeT.aff {T : Set U64} {c : U64} {s s' : S} (h : CAgreeT st T c s s') {y : U64} (hy : y ∈ T) :
    L.mem s' (affA y) = L.mem s (affA y) := h.tcb y hy _ (by simp [CoreField])
theorem CAgreeT.prio {T : Set U64} {c : U64} {s s' : S} (h : CAgreeT st T c s s') {y : U64} (hy : y ∈ T) :
    L.mem s' (prioA y) = L.mem s (prioA y) := h.tcb y hy _ (by simp [CoreField])
theorem CAgreeT.inq {T : Set U64} {c : U64} {s s' : S} (h : CAgreeT st T c s s') {y : U64} (hy : y ∈ T) :
    L.mem s' (inqA y) = L.mem s (inqA y) := h.tcb y hy _ (by simp [CoreField])
theorem CAgreeT.next {T : Set U64} {c : U64} {s s' : S} (h : CAgreeT st T c s s') {y : U64} (hy : y ∈ T) :
    L.mem s' (nextA .Sched y) = L.mem s (nextA .Sched y) := h.tcb y hy _ (by simp [CoreField, nextOff])
theorem CAgreeT.prev {T : Set U64} {c : U64} {s s' : S} (h : CAgreeT st T c s s') {y : U64} (hy : y ∈ T) :
    L.mem s' (prevA .Sched y) = L.mem s (prevA .Sched y) := h.tcb y hy _ (by simp [CoreField, prevOff])

theorem CAgreeT.views {T : Set U64} {c : U64} {s s' : S} (h : CAgreeT st T c s s') : ViewsEq st s s' c := by
  refine ⟨fun p hp => ?_, ?_, fun g hg => ?_⟩
  · simp only [LawfulStore.rqQ, nodeAt_ksb h.ksb]
    rw [h.node _ (by rw [rqOff_val hp]; omega) (by rw [rqOff_val hp]; omega) (by rw [rqOff_val hp]; omega)
        (by rw [rqOff_val hp]; omega) (by rw [rqOff_val hp]; omega) (by rw [rqOff_val hp]; omega) (by rw [rqOff_val hp]; omega) (by rw [rqOff_val hp]; omega),
      h.node _ (by rw [rqTailOff_val hp]; omega) (by rw [rqTailOff_val hp]; omega)
        (by rw [rqTailOff_val hp]; omega) (by rw [rqTailOff_val hp]; omega) (by rw [rqTailOff_val hp]; omega) (by rw [rqTailOff_val hp]; omega) (by rw [rqTailOff_val hp]; omega) (by rw [rqTailOff_val hp]; omega)]
  · simp only [LawfulStore.l1W, nodeAt_ksb h.ksb]
    exact h.node _ (by rw [l1Off_val]; omega) (by rw [l1Off_val]) (by rw [l1Off_val]; omega) (by rw [l1Off_val]; omega)
      (by rw [l1Off_val]; omega) (by rw [l1Off_val]; omega) (by rw [l1Off_val]; omega) (by rw [l1Off_val]; omega)
  · simp only [LawfulStore.l2W, nodeAt_ksb h.ksb]
    exact h.node _ (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega)
      (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega)
      (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega)

theorem CAgreeT.links {T : Set U64} {c : U64} {s s' : S} (h : CAgreeT st T c s s') {q xs}
    (hq : QueueRel (L.mem s) T .Sched q xs) : QueueRel (L.mem s') T .Sched q xs :=
  ⟨hq.nodup, hq.mem, hq.head, hq.last, hq.seg.congr fun y hy =>
    ⟨h.prev (hq.mem y hy), h.next (hq.mem y hy)⟩⟩

theorem SchedCore.agreeT {T : Set U64} {c : U64} {s s' : S} {Q : U64 → List U64} {R : List U64}
    (h : SchedCore st T c s Q R) (ha : CAgreeT st T c s s')
    (hct : nodeW st s' c layout.node.CUR_THREAD ∈ T) : SchedCore st T c s' Q R := by
  have hv := ha.views
  have hrel : L.relQ s' c = L.relQ s c := by
    simp only [LawfulStore.relQ, nodeAt_ksb ha.ksb]
    rw [ha.node _ (by rw [relh_val]; omega) (by rw [relh_val]) (by rw [relh_val]; omega) (by rw [relh_val]; omega)
        (by rw [relh_val]; omega) (by rw [relh_val]; omega) (by rw [relh_val]; omega) (by rw [relh_val]; omega),
      ha.node _ (by rw [relt_val]; omega) (by rw [relt_val]) (by rw [relt_val]; omega) (by rw [relt_val]; omega)
        (by rw [relt_val]; omega) (by rw [relt_val]; omega) (by rw [relt_val]; omega) (by rw [relt_val]; omega)]
  refine ⟨h.tcbs, nodePlaced_ksb h.node ha.ksb, ha.cpu.trans h.cur, fun t ht => (ha.aff ht).trans (h.aff t ht),
    fun t ht => (ha.prio ht) ▸ h.prio t ht,
    ⟨h.ready.1.agree hv.1 fun p hp y hy =>
      ⟨ha.next ((h.ready.1.rel p hp).mem y hy), ha.prev ((h.ready.1.rel p hp).mem y hy)⟩, h.ready.2.views hv⟩,
    hrel ▸ ha.links h.release,
    fun p hp t ht => (ha.prio ((h.ready.1.rel p hp).mem t ht)).trans (h.inQ p hp t ht),
    fun t ht => by rw [ha.inq ht, ha.prio ht]; exact h.queued t ht,
    fun t ht => by rw [ha.inq ht]; exact h.released t ht,
    fun t ht => by rw [ha.prio ht]; exact h.excl t ht, ?_, ?_, by rw [ha.ksb]; exact h.ksOut⟩
  · exact hct
  · have e : nodeW st s' c layout.node.IDLE_THREAD = nodeW st s c layout.node.IDLE_THREAD := by
      unfold Fl4Proofs.P3.Sched.nodeW; rw [nodeAt_ksb ha.ksb]
      exact ha.node _ (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD])
        (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD])
    rw [e]
    exact h.idleT


end

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- Writing the node's `CUR_THREAD` word with a TCB of `T`. -/
theorem SchedRel.set_cur_thread {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {v : U64} (hv : v ∈ T) :
    SchedRel st N T C c (L.wr s (L.nodeAt s c layout.node.CUR_THREAD) v) { σ with curThread := v.bv } ∧
      FootEq N T (L.mem s) (L.mem (L.wr s (L.nodeAt s c layout.node.CUR_THREAD) v)) ∧
      ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 0 →
        nodeW st (L.wr s (L.nodeAt s c layout.node.CUR_THREAD) v) c o = nodeW st s c o := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hN := hc.node
  have h0 : layout.node.CUR_THREAD.val = 0 := by simp [layout.node.CUR_THREAD]
  have hA : Aligned (L.nodeAt s c layout.node.CUR_THREAD) := nodeAt_aligned hN (by omega) (by omega)
  set s' := L.wr s (L.nodeAt s c layout.node.CUR_THREAD) v
  have hk : L.ksb s' = L.ksb s := L.ksb_wr _ _ _
  have hne : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 0 →
      L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o) := by
    intro o ho h8 hne
    refine rd_wr_ne hA (nodeAt_aligned hN ho h8) fun e => hne ?_
    have := congrArg UScalar.val e
    rw [nodeAt_val hN (by omega), nodeAt_val hN ho] at this; omega
  have nw : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 0 → nodeW st s' c o = nodeW st s c o := by
    intro o ho h8 h; unfold Fl4Proofs.P3.Sched.nodeW; rw [nodeAt_ksb hk]; exact hne o ho h8 h
  have htf : ∀ y ∈ T, ∀ K, SchedField K →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
    intro y hy K hK
    obtain ⟨h1, h2, -⟩ := schedField_ok hK
    exact rd_wr_ne hA (field_aligned (hc.tcbs y hy) h1 h2) (nodeAt_ne_tfield hN (by omega) hy (hc.tcbs y hy) h1)
  have hdom : L.mem s' (curDomA st s) = L.mem s (curDomA st s) := by
    refine rd_wr_ne hA (curDomA_aligned hN) fun e => ?_
    have := congrArg UScalar.val e
    rw [nodeAt_val hN (by omega), curDomA_val hN] at this
    simp only [LawfulStore.nodeBase] at this; omega
  have hscw : ∀ sc ∈ C, ScAgree st s s' sc := by
    intro sc hsc a hal hin
    refine rd_wr_ne hA hal fun e => ?_
    have := congrArg UScalar.val e
    rw [nodeAt_val hN (by omega)] at this
    have := (hS.scOutIn hsc hin).2.1; omega
  have hca : CAgreeT st T c s s' := ⟨hk, L.cpu_wr _ _ _, fun o ho h8 _ _ _ _ _ h => hne o ho h8 h,
    fun y hy K hK => htf y hy K (by rcases hK with h | h | h | h | h <;> simp [SchedField, h])⟩
  have hm := hs.rmax_eq hscw
  refine ⟨⟨hS.placed, fun o ho => by rw [nodeAt_ksb hk]; exact hS.nodeNW o ho,
    by rw [curDomA_ksb hk]; exact hS.domNW, by rw [dtA_ksb hk]; exact hS.dtNW,
    scOut_transfer hk (SzKeep.of_kheap rfl) hS.scOut, scDisj_transfer (SzKeep.of_kheap rfl) hS.scDisj,
    by rw [nw _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
      (by simp [layout.node.SCHED_ACTION])]; exact hS.actW,
    by rw [nw _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
      (by simp [layout.node.SCHED_ACTION])]; exact hS.act,
    by rw [nw _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
      (by simp [layout.node.REPROGRAM])]; exact hS.repr,
    hs.core_eq hscw hS.core, Q, R, hc.agreeT hca (by show L.mem s' (L.nodeAt s' c layout.node.CUR_THREAD) ∈ T; rw [nodeAt_ksb hk, rd_wr_eq hA]; exact hv), ?_⟩, node_wr_foot hS (by omega) (by omega), nw⟩
  refine ⟨hs.rq, hs.rqDom, hs.rel, ?_, ?_, ?_, ?_, ?_, fun y hy => ?_, fun y hy => ?_, fun sc hsc => ?_,
    by rw [nw layout.node.IDLE_SC (by simp [layout.node.IDLE_SC]) (by simp [layout.node.IDLE_SC]) (by simp [layout.node.IDLE_SC])]; exact hs.idleSc,
    by rw [dtA_ksb hk, dt_wr_node hN (by omega) (by omega)]; exact hs.domTime,
    by rw [nw layout.node.IDLE_THREAD (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD])]; exact hs.idleTh⟩
  · show v.bv = _
    unfold Fl4Proofs.P3.Sched.nodeW; rw [nodeAt_ksb hk, rd_wr_eq hA]
  · rw [nw layout.node.CUR_SC (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      (by simp [layout.node.CUR_SC])]; exact hs.curSc
  · rw [nw layout.node.CUR_TIME (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
      (by simp [layout.node.CUR_TIME])]; exact hs.curTime
  · rw [nw layout.node.CONSUMED (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
      (by simp [layout.node.CONSUMED])]; exact hs.consumed
  · rw [curDomA_ksb hk, hdom]; exact hs.curDom
  · obtain ⟨x, hkx, h1, h2, h3, h4⟩ := hs.tcb y hy
    have e1 : L.mem s' (domA y) = L.mem s (domA y) := htf y hy _ (by simp [SchedField])
    have e2 : L.mem s' (scA y) = L.mem s (scA y) := htf y hy _ (by simp [SchedField])
    have e3 : L.mem s' (prioA y) = L.mem s (prioA y) := htf y hy _ (by simp [SchedField])
    exact ⟨x, hkx, h1, by rw [e1]; exact h2, by rw [e2]; exact h3, by rw [e3]; exact h4⟩
  · have e2 : L.mem s' (scA y) = L.mem s (scA y) := htf y hy _ (by simp [SchedField])
    rw [e2]; exact hs.scMem y hy
  · obtain ⟨x, n, hkx, e⟩ := hs.scs sc hsc
    exact ⟨x, n, hkx, e.agree (hscw sc hsc)⟩


theorem sched.idle_thread.spec2 (s : S) :
    sched.idle_thread st s ⦃ v => v = nodeW st s (L.cpu s) layout.node.IDLE_THREAD ⦄ := by
  unfold sched.idle_thread; step*; simp_all [nodeW]

theorem sched.set_cur_thread.spec2 (s : S) (t : obj.Tcb) :
    sched.set_cur_thread st s t ⦃ s' => s' = L.wr s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) t ⦄ := by
  unfold sched.set_cur_thread; step*; simp_all

/-- A total triple and a partial fact: the post and the fact. -/
theorem spec_and_eq {α : Type} {m : Result α} {P Q : α → Prop} (h : m ⦃ P ⦄) (hq : ∀ r, m = ok r → Q r) :
    m ⦃ fun r => P r ∧ Q r ⦄ := by
  cases hm : m with
  | ret r => rw [hm] at h hq; rw [WP.spec_ok] at h ⊢; exact ⟨h, hq r rfl⟩
  | _ => rw [hm] at h; simp [WP.spec_vis, WP.spec_div] at h

theorem bind_pair_s {s : S} {x : Result A} {r : S × A} (h : (do let a1 ← x; ok (s, a1)) = ok r) : r.1 = s := by
  cases x <;> simp at h
  subst h; rfl

/-- **`set_kernel_vm_root` writes no store word.** -/
theorem set_kernel_vm_root_s {s : S} {a : A} {r : S × A} (h : vspace.set_kernel_vm_root st ar s a = ok r) :
    r.1 = s := by
  unfold vspace.set_kernel_vm_root at h
  cases h1 : vspace.kernel_root st s <;> simp [h1] at h
  exact bind_pair_s h

/-- **`set_vm_root` writes no store word.** -/
theorem set_vm_root_s {s : S} {a : A} {t : obj.Tcb} {r : S × A} (h : vspace.set_vm_root st ar s a t = ok r) :
    r.1 = s := by
  unfold vspace.set_vm_root at h
  cases h1 : obj.Tcb.slot t layout.tcb.SLOT_VTABLE <;> simp [h1] at h
  rename_i sl
  cases h2 : obj.Slot.cap st sl s <;> simp [h2] at h
  split at h <;> first | exact set_kernel_vm_root_s h | skip
  split at h
  · rename_i asid _
    cases h3 : vspace.find_vspace_for_asid st s asid <;> simp [h3] at h
    split at h
    · split at h
      · exact bind_pair_s h
      · exact set_kernel_vm_root_s h
    · exact set_kernel_vm_root_s h
  · exact set_kernel_vm_root_s h

/-- What the arch part of a thread switch keeps (it changes the arch and
machine state). -/
def ArchKeeps (σ σ' : Fl4Spec.State Unit) : Prop :=
  σ'.kheap = σ.kheap ∧ σ'.readyQueues = σ.readyQueues ∧ σ'.releaseQueue = σ.releaseQueue ∧
    σ'.curThread = σ.curThread ∧ σ'.curSc = σ.curSc ∧ σ'.curTime = σ.curTime ∧
    σ'.consumedTime = σ.consumedTime ∧ σ'.schedulerAction = σ.schedulerAction ∧ σ'.idleThread = σ.idleThread ∧
    σ'.curDomain = σ.curDomain ∧ σ'.domainTime = σ.domainTime ∧ σ'.idleSc = σ.idleSc

/-- What a thread switch keeps besides the heap: the times, the idle thread
and the domain. -/
def TK (σ σ' : Fl4Spec.State Unit) : Prop :=
  σ'.curTime = σ.curTime ∧ σ'.consumedTime = σ.consumedTime ∧ σ'.idleThread = σ.idleThread ∧
    σ'.curDomain = σ.curDomain ∧ σ'.domainTime = σ.domainTime ∧ σ'.idleSc = σ.idleSc

/-- **`switch_to_thread` refines l4v `switch_to_thread`**, keeping `Inv`. The
address-space and FPU switch is the arch hypothesis `hvm`. -/
theorem switch_to_thread_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ)
    {t : U64} (ht : t ∈ T)
    (hvm : vspace.set_vm_root st ar s a t ⦃ r => ∃ σ1, Fl4Spec.archSwitchToThread (Z := Unit) t.bv σ =
      ({((), σ1)}, False) ∧ SchedRel st N T C c r.1 σ1 ∧ NtfnStateRel N T (L.mem r.1) σ1 ∧ ArchKeeps σ σ1 ⦄) :
    sched.switch_to_thread st ar s a t ⦃ r => ∃ σ', Fl4Spec.switchToThread (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ (Inv σ → Inv σ') ∧
      σ'.curThread = t.bv ∧ σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ σ'.kheap = σ.kheap ∧
      σ'.schedulerAction = σ.schedulerAction ∧ TK σ σ' ∧ WritesIn st s r.1 (SFoot st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨xt, hkt, -⟩ := hs.tcb t ht
  unfold sched.switch_to_thread
  refine WP.spec_bind (spec_and_eq hvm fun r hr => set_vm_root_s hr) ?_
  rintro ⟨s1, a1⟩ ⟨⟨σ1, h1, hS1, hR1, ek, eq, er, ect, esc, etm, ecn, eact, eid, ecd, edt, eisc⟩, hs1⟩
  simp only at hs1; subst s1
  have hkt1 : σ1.kheap t.bv = some (.tcb xt) := by rw [ek]; exact hkt
  refine WP.spec_bind (WP.spec_and (dequeue_refines s σ1 hS1 t ht) (dequeue_sfoot hS1 ht)) ?_
  rintro s2 ⟨⟨σ2, h2, ek2, er2, hf2, hS2⟩, hw2⟩
  refine WP.spec_bind (sched.set_cur_thread.spec2 s2 t) ?_
  rintro s3 rfl
  rw [WP.spec_ok]
  show ∃ σ', _ ∧ SchedRel st N T C c (L.wr s2 (L.nodeAt s2 (L.cpu s2) layout.node.CUR_THREAD) t) σ' ∧ _
  rw [hS2.lists.choose_spec.choose_spec.1.cur]
  obtain ⟨hS3, hf3, -⟩ := hS2.set_cur_thread ht
  have hkv2 : KView σ1 σ2 := KView.of_kheap ek2
  have hR2 := hR1.frame hS1.placed hf2 hkv2
  rw [tcbSchedAction_gen hkt1] at h2
  have e2 := pair_eq h2
  refine ⟨{ σ2 with curThread := t.bv }, ?_, hS3, hR2.frame hS2.placed hf3 (KView.of_kheap rfl), ?_, ?_, rfl, ?_, ?_,
    ?_, ?_, ?_, WritesIn.sfoot_trans hw2 (sfoot_wr_node hS2.lists.choose_spec.choose_spec.1.node
      (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD]) t)⟩
  · unfold Fl4Spec.switchToThread
    rw [nd_bind_one (show Fl4Spec.NonDet.get (σ := Fl4Spec.State Unit) σ = ({(σ, σ)}, False) from rfl),
      nd_bind_one (assert_true (by simp [Fl4Spec.getTcb, Fl4Spec.readObject, hkt, Fl4Spec.Lookup.oreturn]) σ),
      nd_bind_one h1, nd_bind_one (tcbSchedAction_gen hkt1 _), ← e2]
    rfl
  · intro n hn x p hx hp; rw [ek2, ek] at hx; exact hN n hn x p hx hp
  · intro hI
    have hI1 : Inv σ1 := hI.congr ek eq er etm
    rw [e2]
    exact (hI1.qchange (qchange_dequeue hkt1)).congr rfl rfl rfl rfl
  · rw [e2]; exact esc
  · rw [er2, er]
  · rw [ek2, ek]
  · rw [e2]; exact eact
  · rw [e2]; exact ⟨etm, ecn, eid, ecd, edt, eisc⟩

/-- **`switch_to_idle_thread` refines l4v `switch_to_idle_thread`**, keeping
`Inv`. -/
theorem switch_to_idle_thread_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ)
    (hidleT : (nodeW st s c layout.node.IDLE_THREAD).bv = σ.idleThread)
    (hvm : vspace.set_kernel_vm_root st ar s a ⦃ r => ∃ σ1, Fl4Spec.archSwitchToIdleThread (Z := Unit) σ =
      ({((), σ1)}, False) ∧ SchedRel st N T C c r.1 σ1 ∧ NtfnStateRel N T (L.mem r.1) σ1 ∧ ArchKeeps σ σ1 ⦄) :
    sched.switch_to_idle_thread st ar s a ⦃ r => ∃ σ', Fl4Spec.switchToIdleThread (Z := Unit) σ = ({((), σ')}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ (Inv σ → Inv σ') ∧
      σ'.curThread = σ.idleThread ∧ σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ σ'.kheap = σ.kheap ∧
      σ'.schedulerAction = σ.schedulerAction ∧ TK σ σ' ∧ WritesIn st s r.1 (SFoot st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hiT := hc.idleT
  unfold sched.switch_to_idle_thread
  step with sched.idle_thread.spec2 as ⟨it, hit⟩
  rw [hc.cur] at hit
  subst it
  refine WP.spec_bind (spec_and_eq hvm fun r hr => set_kernel_vm_root_s hr) ?_
  rintro ⟨s1, a1⟩ ⟨⟨σ1, h1, hS1, hR1, ek, eq, er, ect, esc, etm, ecn, eact, eid, ecd, edt, eisc⟩, hs1⟩
  simp only at hs1; subst s1
  refine WP.spec_bind (sched.set_cur_thread.spec2 s _) ?_
  rintro s2 rfl
  rw [WP.spec_ok]
  show ∃ σ', _ ∧ SchedRel st N T C c (L.wr s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD)
    (nodeW st s c layout.node.IDLE_THREAD)) σ' ∧ _
  rw [hS1.lists.choose_spec.choose_spec.1.cur]
  obtain ⟨hS2, hf2, -⟩ := hS1.set_cur_thread hiT
  refine ⟨{ σ1 with curThread := (nodeW st s c layout.node.IDLE_THREAD).bv }, ?_, hS2,
    hR1.frame hS1.placed hf2 (KView.of_kheap rfl), ?_, fun hI => (hI.congr ek eq er etm).congr rfl rfl rfl rfl,
    hidleT, esc, er, ek, eact, ⟨etm, ecn, eid, ecd, edt, eisc⟩,
    sfoot_wr_node hc.node (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD]) _⟩
  · unfold Fl4Spec.switchToIdleThread
    rw [nd_gets_bind, nd_bind_one h1, ← hidleT]
    rfl
  · intro n hn x p hx hp; rw [ek] at hx; exact hN n hn x p hx hp

end

end

end Fl4Proofs.P3.Sched
