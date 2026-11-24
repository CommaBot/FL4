/-
P2 (p2j, KWN step 2): `.kwN` footprints of the scheduler steps the stall and
`schedule` run beside the queue operations (`P2/FootN.lean`): `append`,
`set_cur_thread`, `switch_to_thread`, `postpone`, `set_reprogram`,
`set_reprogram_on`, `update_timestamp`, `commit_time`, the current node's
`CUR_SC` / `CONSUMED` writes and `send_pending`. No premise.
-/
import Fl4Proofs.P2.FootN
import Fl4Proofs.P1.QueueFootS
import Fl4Proofs.P1.QueueKeeps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Es : Set U64} {Ac : Set U64} {Kp : Set U64} {Nd : Prop}
variable {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}

/-- A write of a current-node word other than the idle words. -/
theorem footN_cur {s : S} {o v : U64} (NP : ∀ c ∈ Cs, NodePlaced st T s c) (hc : L.cpu s ∈ Cs)
    (ho : o.val < 4288) (h8 : o.val % 8 = 0) (h88 : o.val ≠ 88) (hi8 : o.val ≠ 8) (hi32 : o.val ≠ 32)
    (h0 : Nd → o.val ≠ 0) :
    FootN st Kp Nd T Cs Sg Scs Z Es s (L.wr s (L.nodeAt s (L.cpu s) o) v) :=
  footN_node NP hc ho h8 h88 (idOff_cur hi8 hi32 h0)

theorem sched.append.kwN (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) :
    sched.append st s t ⦃ s' => FootN st Kp Nd T Cs Sg Scs Z Es s s' ⦄ := by
  have hc := h.aff t ht
  have hp := h.prio t ht
  have hR1 := h.ready _ hc
  refine WP.spec_mono (sched.append.foot s t _ h.tcbs ht hp (h.nodes _ hc) (h.nodes _ h.cur) (hR1.1.rel _ hp)
    (fun h0 => h.notQ ht h0 hc hp)) fun s' hh => hh.1.mono fun b hb =>
      LawfulStore.QFoot.kwN h.tcbs h.nodes ?_ hc h.cur ht (fun o ho => by omega) (fun o ho => idOff_ge (by omega)) hb
  intro w hw
  rcases List.mem_cons.1 hw with rfl | hw
  · exact ht
  · exact (hR1.1.rel _ hp).mem w hw

theorem sched.set_cur_thread.kwN (s : S) (t : obj.Tcb) (NP : ∀ c ∈ Cs, NodePlaced st T s c) (hc : L.cpu s ∈ Cs)
    (hNd : ¬ Nd) :
    sched.set_cur_thread st s t ⦃ s' => FootN st Kp Nd T Cs Sg Scs Z Es s s' ⦄ :=
  WP.spec_mono (sched.set_cur_thread.spec s t) fun s' e => by
    subst e
    exact footN_cur NP hc (by rw [curth0]; omega) (by rw [curth0]) (by rw [curth0]; omega)
      (by rw [curth0]; omega) (by rw [curth0]; omega) (fun h => absurd h hNd)

theorem sched.switch_to_thread.kwN {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t : obj.Tcb) {Q : U64 → U64 → List U64} {R : U64 → List U64} (h : SchedQueuesInv st T Cs Ω H s Q R)
    (ht : t ∈ T) (hNd : ¬ Nd) : sched.switch_to_thread st ar s a t ⦃ s' _ => FootN st Kp Nd T Cs Sg Scs Z Es s s' ⦄ := by
  unfold sched.switch_to_thread
  refine WP.spec_bind (set_vm_root_same hA s a t) ?_
  rintro ⟨s1, a1⟩ e
  simp only [WP.uncurry'_pair] at e
  subst e
  refine WP.spec_bind (sched.dequeue.kwN (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) (Es := Es) s1 t h ht) ?_
  intro s2 f2
  refine WP.spec_bind (sched.set_cur_thread.kwN (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) (Es := Es) s2 t
    (fun c hc => (h.nodes c hc).ksb f2.1) (by rw [f2.2.1]; exact h.cur) hNd) ?_
  intro s3 f3
  simp only [WP.spec_ok, WP.uncurry'_pair]
  exact f2.trans f3

theorem sched.set_reprogram.kwN (s : S) (NP : ∀ c ∈ Cs, NodePlaced st T s c) (hc : L.cpu s ∈ Cs) :
    sched.set_reprogram st s ⦃ s' => FootN st Kp Nd T Cs Sg Scs Z Es s s' ⦄ :=
  WP.spec_mono (sched.set_reprogram.spec s) fun s' e => by
    subst e
    have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
    exact footN_cur NP hc (by rw [rp]; omega) (by rw [rp]) (by rw [rp]; omega) (by rw [rp]; omega)
      (by rw [rp]; omega) (fun _ => by rw [rp]; omega)

theorem sched.set_reprogram_on.kwN (s : S) (cpu : U64) (NP : ∀ c ∈ Cs, NodePlaced st T s c) (hc : cpu ∈ Cs) :
    sched.set_reprogram_on st s cpu ⦃ s' => FootN st Kp Nd T Cs Sg Scs Z Es s s' ⦄ :=
  WP.spec_mono (sched.set_reprogram_on.spec s cpu) fun s' e => by
    subst e
    have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
    exact footN_node NP hc (by rw [rp]; omega) (by rw [rp]) (by rw [rp]; omega) (idOff_ge (by rw [rp]; omega))

/-- **The footprint of `postpone`** in `KWN` (P1 `postpone.kwB`). -/
theorem sched.postpone.kwN (s : S) (sc : obj.Sc) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInv st T Cs Ω H s Q R) (ht : L.mem s (scTcbA sc) ∈ T)
    (hr0 : (L.mem s (inqA (L.mem s (scTcbA sc))) &&& sched.Q_RELEASE) = 0#u64)
    (hcore : OutsideObjs st T Cs s (scCoreA sc)) (hcs : L.mem s (scCoreA sc) ∈ Cs) :
    sched.postpone st s sc ⦃ s' => FootN st Kp Nd T Cs Sg Scs Z Es s s' ⦄ := by
  unfold sched.postpone
  step with obj.Sc.tcb.spec as ⟨t, t_post⟩
  subst t_post
  set t := L.mem s (scTcbA sc) with ht_def
  have hT := h.tcbs
  have hc := h.aff t ht
  have hp := h.prio t ht
  have hN := h.nodes _ hc
  have hN' := h.nodes _ h.cur
  have hR1 := h.ready _ hc
  have hmemq := (h.queued t ht).1
  refine WP.spec_bind (WP.spec_and (sched.dequeue.inv s t Q R h ht)
    (sched.dequeue.foot s t _ hT ht hp hN hN' (hR1.1.rel _ hp) hmemq)) ?_
  rintro s1 ⟨h1, hw1, -⟩
  have hW1 : ∀ w ∈ Q (L.mem s (affA t)) (L.mem s (prioA t)), w ∈ T := fun w hw => h.memT hc hp hw
  have F1 : FootN st Kp Nd T Cs Sg Scs Z Es s s1 :=
    hw1.mono fun b hb => LawfulStore.QFoot.kwN hT h.nodes hW1 hc h.cur ht (fun o ho => by omega)
      (fun o ho => idOff_ge (by omega)) hb
  have core1 : L.mem s1 (scCoreA sc) = L.mem s (scCoreA sc) :=
    hw1.mem_eq hcore.1 (qfoot_out hT hW1 hN hN' ht hc h.cur hcore)
  have hr1 : (L.mem s1 (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
    by_contra hcn
    exact h.notR ht hr0 (h1.aff t ht) ((h1.released t ht).1 hcn)
  have hT1 := h1.tcbs
  have hc1 := h1.aff t ht
  have hN1 := h1.nodes _ hc1
  have hN1' := h1.nodes _ h1.cur
  refine WP.spec_bind (sched.release_enqueue.foot s1 t _ hT1 ht (h1.notR ht hr1 hc1) hN1 hN1'
    (h1.release _ hc1)) ?_
  rintro s2 ⟨hw2, -⟩
  have hW2 : ∀ w ∈ t :: R (L.mem s1 (affA t)), w ∈ T := by
    intro w hw; rcases List.mem_cons.1 hw with rfl | hw
    · exact ht
    · exact h1.memTR hc1 hw
  have F2 : FootN st Kp Nd T Cs Sg Scs Z Es s1 s2 :=
    hw2.mono fun b hb => LawfulStore.QFoot.kwN hT1 h1.nodes hW2 hc1 h1.cur ht
      (fun o ho => by unfold RelOffs at ho; omega) (fun o ho => idOff_ge (by unfold RelOffs at ho; omega)) hb
  have core2 : L.mem s2 (scCoreA sc) = L.mem s (scCoreA sc) :=
    (hw2.mem_eq hcore.1 (qfoot_out hT1 hW2 hN1 hN1' ht hc1 h1.cur (hcore.ksb hw1.1))).trans core1
  step with obj.Sc.cpu.spec as ⟨cpu, cpu_post⟩
  rw [core2] at cpu_post
  subst cpu_post
  have NP2 : ∀ c ∈ Cs, NodePlaced st T s2 c := fun c hc => (h.nodes c hc).ksb (hw2.1.trans hw1.1)
  exact WP.spec_mono (sched.set_reprogram_on.kwN s2 _ NP2 hcs) fun s3 f3 => (F1.trans F2).trans f3

/-- `update_timestamp` writes the current core's `CUR_TIME` and `CONSUMED`. -/
theorem sched.update_timestamp.kwN {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (NP : ∀ c ∈ Cs, NodePlaced st T s c) (hc : L.cpu s ∈ Cs) :
    sched.update_timestamp st ar s a ⦃ s' _ => FootN st Kp Nd T Cs Sg Scs Z Es s s' ⦄ := by
  unfold sched.update_timestamp
  step with sched.cur_time.spec as ⟨prev⟩
  refine WP.spec_bind (hA.now a) ?_
  rintro ⟨now, a1⟩ -
  try simp only [WP.uncurry'_pair]
  step with LawfulStore.cur_cpu_spec as ⟨c, ec⟩
  step with obj.node_set.spec as ⟨s1, e1⟩
  subst ec e1
  have f1 : FootN st Kp Nd T Cs Sg Scs Z Es s (L.wr s (L.nodeAt s (L.cpu s) layout.node.CUR_TIME) now) :=
    footN_cur NP hc (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
      (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
      (fun _ => by simp [layout.node.CUR_TIME])
  step as ⟨used, _⟩
  step with sched.consumed.spec as ⟨i⟩
  step as ⟨total, _⟩
  step with sched.set_consumed.spec as ⟨s2, e2⟩
  rw [show ∀ s0 : S, L.nodeA s0 layout.node.CONSUMED = L.nodeAt s0 (L.cpu s0) layout.node.CONSUMED from
    fun _ => rfl] at e2
  subst e2
  have f2 := footN_cur (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) (Es := Es) (v := total)
    (s := L.wr s (L.nodeAt s (L.cpu s) layout.node.CUR_TIME) now)
    (fun c hc' => (NP c hc').ksb (L.ksb_wr _ _ _)) (by rw [LawfulStore.cpu_wr]; exact hc)
    (o := layout.node.CONSUMED) (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
    (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
    (fun _ => by simp [layout.node.CONSUMED])
  simp only [layout.NUM_DOMAINS, fl4_abi.config.NUM_DOMAINS]
  have hnd : ¬ ((1#u64) > (1#u64)) := by simp
  simp only [hnd, ↓reduceIte, WP.spec_ok, WP.uncurry'_pair]
  exact f1.trans f2

/-- `commit_time` writes the current SC's ring and `CONSUMED` word and the
current node's `CONSUMED`. -/
theorem sched.commit_time.kwN {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (a : A) {s : S}
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    sched.commit_time st ar s a ⦃ s' => FootN st Kp Nd T Cs Sg Scs Z Es s s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hO := hX.1
  have hc : L.cscW s ∈ Scs := hX.2.2.cur
  have hN' := h0.nodes _ h0.cur
  obtain ⟨hP, hz⟩ := hO.sc _ hc
  have cnv : layout.node.CONSUMED.val = 40 := by simp [layout.node.CONSUMED]
  have aC : Aligned (L.nodeA s layout.node.CONSUMED) := nodeAt_aligned hN' (by rw [cnv]; omega) (by rw [cnv])
  have oC : Outside (L.nodeA s layout.node.CONSUMED) (L.cscW s) (Z (L.cscW s)) :=
    node_out_place (fun b hb hin => hO.scW _ hc b hb hin) h0.omega h0.cur hN' (by rw [cnv]; omega) (by rw [cnv])
  refine WP.spec_mono (sched.commit_time.fr hA a (hS.all _ hc).1 rfl aC oC) fun s' hw => ?_
  refine FootN.of' hw.1 fun b hb hh => ?_
  rcases hh with (hh | rfl) | rfl
  · exact ⟨kw_sc hc hh.inSC, notIdW_out h0.nodes (h0.omega _ (hO.scW _ hc b hb hh.inSC)) (noHdr_ring hO hc hh)⟩
  · obtain ⟨-, h128, -⟩ := sc_lo hP hz
    have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
    have hin : InSC (L.cscW s) (Z (L.cscW s)) (core.num.U64.wrapping_add (L.cscW s) layout.sc.CONSUMED) :=
      ⟨by rw [hv]; simp, by rw [hv]; simp [layout.sc.CONSUMED]; omega⟩
    exact ⟨kw_sc hc hin, notIdW_out h0.nodes (h0.omega _ (hO.scW _ hc _ hb hin))
      (noHdr_sc hO hc hin (by rw [hv]; simp [layout.sc.CONSUMED]) (by rw [hv]; simp [layout.sc.CONSUMED]))⟩
  · exact ⟨kw_node h0.cur (by rw [cnv]; omega) (by rw [cnv]; omega),
      notIdW_node h0.nodes h0.cur (by rw [cnv]; omega) (idOff_ge (by simp [cnv]))⟩

/-- `send_pending` only clears the current core's `IPI_PENDING`. -/
theorem smp.send_pending.kwN {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (NP : ∀ c ∈ Cs, NodePlaced st T s c) (hc : L.cpu s ∈ Cs) :
    smp.send_pending st ar s a ⦃ s' _ => FootN st Kp Nd T Cs Sg Scs Z Es s s' ⦄ :=
  smp.send_pending.fp hA s a (NP _ hc)
    ⟨kw_node hc (by simp [layout.node.IPI_PENDING]) (by simp [layout.node.IPI_PENDING]),
      notIdW_node NP hc (by simp [layout.node.IPI_PENDING]) (idOff_ge (by simp [layout.node.IPI_PENDING]))⟩

end

end Fl4Proofs.P1
