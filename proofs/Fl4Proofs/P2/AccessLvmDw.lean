/-
# P2 (line lvm, gen 6): **a declined `local_vm_exit` on the guarded store**

`vexit_decG`: from a state with P1's invariant (`BXI`), a declined run of `handle_vcpu_exit_local` is the same run
on any store `gS` answering the reads of `IrqRd`, the two kernel-global words, the VCPU's `PENDING` (when `v ≠ 0`)
and the bound notification's `TAIL_STATE` (when `n` is the current thread's bound notification) as `st`, and
writing `update_timestamp`'s two node words as `st` (`IrqDec`). A declined run stops in the head's checks (no
write) or after `update_timestamp`, at `sufficient` or `awaken_quiet` (`vexitTail`); the walk carries the real
run's values step by step (`tr_bind_same` / `tr_ite`, as `irq_dec_guard`).

The current thread's home words are read before `current_vm_ok` checks its affinity, so `gRd` is unconditional
here: `AccessLvmOwn` discharges it from `VexitEnt`'s `curAff` / `cscCore` [J] (as `IoPre`'s, p2j's
`OwnJ.curAff` / `EntryInv.cur_sc_core`).

No named premises.
-/
import Fl4Proofs.P2.AccessLvmSplit
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (ScAcc rhA tmA RdHead NodeSt tr_bind_same tr_ite)

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 32000000 in
/-- **A declined VM exit on the guarded store** (module docstring). -/
theorem vexit_decG {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
    (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {v n : U64}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (gRd : ∀ w, Aligned w → IrqRd st Z s w → R w)
    (hD1 : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hD2 : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME))
    (hRp : v ≠ 0#u64 → R (core.num.U64.wrapping_add v vcpu.PENDING))
    (hRn : ∀ n', L.mem s (boundA (L.curW s)) = n' → n' ≠ 0#u64 →
      R (core.num.U64.wrapping_add n' layout.ntfn.TAIL_STATE))
    (hW1 : W (ctA (L := L) s)) (hW2 : W (cnA (L := L) s))
    (h : localvm.handle_vcpu_exit_local st ar s a v n = ok (false, s', a')) :
    localvm.handle_vcpu_exit_local gS ar s a v n = ok (false, s', a') := by
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  have hcC : L.cpu s ∈ Cs := h0.cur
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ hcC
  have hcT : L.curW s ∈ T := h0.curT
  have ht' := hT _ hcT
  have hX := hI.2.2.1
  have hS := hI.2.2.2.2
  have hO := hX.1
  have hcs : L.cscW s ∈ Scs := hX.2.2.cur
  have hcq : SCq st s Ω (L.cscW s) (Z (L.cscW s)) := scq_of hO hS hcs
  have hmaxΩ : maxA (L.cscW s) ∈ Ω := hcq.2.1 _ hcq.2.2.2.2 hcq.2.2.2.1
  have nR : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o) := fun o h1 h2 =>
    gRd _ (nodeAt_aligned hN h1 h2) (Or.inl ⟨o, h1, h2, rfl⟩)
  have cR : ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → (K.val < 3528 ∨ 3576 ≤ K.val) →
      K.val ≠ 3496 → K.val ≠ 3504 → R (core.num.U64.wrapping_add (L.curW s) K) := fun K h1 h2 h3 h4 h5 h6 =>
    gRd _ (field_aligned ht' h2 h3) (Or.inr (Or.inl ⟨K, h1, h2, h3, h4, h5, h6, rfl⟩))
  have scR : ∀ b, InSC (L.cscW s) (Z (L.cscW s)) b → Aligned b → R b := fun b hb ha =>
    gRd _ ha (Or.inr (Or.inr (Or.inl hb)))
  have hSc : ScAcc R (fun _ => True) (L.cscW s) (Z (L.cscW s)) :=
    ⟨fun b ha hb => scR b hb ha, fun _ _ _ => trivial, trivial⟩
  have rSt : R (stA (L.curW s)) := by rw [stA_eq]; exact cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rSc : R (scA (L.curW s)) := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rIq : R (inqA (L.curW s)) := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rYt : R (yieldA (L.curW s)) := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rAf : R (affA (L.curW s)) := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rDm : R (domA (L.curW s)) := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rVc : R (core.num.U64.wrapping_add (L.curW s) 3664#u64) :=
    cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rBn : R (core.num.U64.wrapping_add (L.curW s) 3368#u64) :=
    cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rMx : R (maxA (L.cscW s)) := scR _ hcq.2.2.2.1 hcq.2.2.2.2
  have rCore : R (scCoreA (L.cscW s)) := by
    obtain ⟨hP, hz⟩ := hO.sc _ hcs
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hv := sc_word_val hP hz (o := layout.sc.CORE) (by simp [layout.sc.CORE])
    have hcv : layout.sc.CORE.val = 16 := by simp [layout.sc.CORE]
    exact scR _ ⟨by unfold scCoreA; rw [hv]; omega, by unfold scCoreA; rw [hv, hcv]; omega⟩
      (by unfold Aligned scCoreA; rw [hv, hcv]; omega)
  -- the work, declining
  have tailD : localtimer.sched_quiet st s (L.cpu s) = ok true → L.mem s (scA (L.curW s)) = L.cscW s →
      vexitTail st ar s a (L.curW s) (L.cscW s) (L.cpu s) = ok (false, s', a') →
      vexitTail gS ar s a (L.curW s) (L.cscW s) (L.cpu s) = ok (false, s', a') := by
    intro eq hsct
    have hact0 : L.actionW s = sched.ACTION_RESUME_CURRENT := sq_true eq
    have hsc0 : L.mem s (scA (L.curW s)) ≠ 0#u64 := hI.2.1.resume (hact0.trans resume_val)
    have hAc : L.cscW s ∈ Ac := by
      rw [← hsct]
      exact hI.2.1.sact _ hcT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hact0.trans resume_val, rfl⟩))))) hsc0
    have hmx0 : L.rmax s (L.cscW s) ≠ 0#u64 := (hS.act _ hcs).1 hAc
    have hdC : ∀ Y : S, (∀ b ∈ Ω, L.mem Y b = L.mem s b) → RdHead (L := L) R Y (L.cscW s) := fun Y ag =>
      hSc.head ((SCq.agree hcq ag).1 (by
        unfold LawfulStore.rmax; rw [ag _ hmaxΩ]; exact hmx0))
    unfold vexitTail
    rw [PathObl.sched.update_timestamp.guard (gS := gS) ar s a
      (nR _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])) hW1
      (nR _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])) hW2]
    refine tr_bind_same (fun q eu => ?_)
    obtain ⟨s1, a1⟩ := q
    try simp only [uncurry_apply_pair]
    -- `s → s1`: the timestamp update
    obtain ⟨n1, -, er⟩ := ut_now ar hA hN eu
    simp only at er
    have k1 : L.ksb s1 = L.ksb s := by rw [er, utW_ksb]
    have c1 : L.cpu s1 = L.cpu s := by rw [er, utW_cpu]
    have m1 : ∀ b, Aligned b → b ≠ ctA (L := L) s → b ≠ cnA (L := L) s → L.mem s1 b = L.mem s b :=
      fun b hb h1 h2 => by rw [er]; exact utW_mem hN n1 hb h1 h2
    have e1N : ∀ o, L.nodeAt s1 (L.cpu s1) o = L.nodeAt s (L.cpu s) o := fun o => by rw [c1, nodeAt_of_ksb k1]
    have hnode1 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 40 → o.val ≠ 48 →
        L.mem s1 (L.nodeAt s (L.cpu s) o) = L.mem s (L.nodeAt s (L.cpu s) o) := by
      intro o ho h8 h40 h48
      refine m1 _ (nodeAt_aligned hN ho h8) (fun e => ?_) (fun e => ?_)
      · have e' := congrArg UScalar.val e
        unfold ctA at e'
        rw [nodeAt_val hN ho, nodeAt_val hN (by simp [layout.node.CUR_TIME])] at e'
        simp [layout.node.CUR_TIME] at e'; omega
      · have e' := congrArg UScalar.val e
        unfold cnA at e'
        rw [nodeAt_val hN ho, nodeAt_val hN (by simp [layout.node.CONSUMED])] at e'
        simp [layout.node.CONSUMED] at e'; omega
    have htcb1 : ∀ {y K : U64}, y ∈ T → K.val < 4096 → K.val % 8 = 0 →
        L.mem s1 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
      intro y K hy hK h8
      exact m1 _ (field_aligned (hT y hy) hK h8) (tcb_node_ne hN hy (hT y hy) hK (by simp [layout.node.CUR_TIME]))
        (tcb_node_ne hN hy (hT y hy) hK (by simp [layout.node.CONSUMED]))
    have hout1 : ∀ b, OutsideObjs st T Cs s b → L.mem s1 b = L.mem s b := fun b hb =>
      m1 b hb.1 (fun e => out_ne_node hb hcC hN (by simp [layout.node.CUR_TIME]) (congrArg UScalar.val e).symm)
        (fun e => out_ne_node hb hcC hN (by simp [layout.node.CONSUMED]) (congrArg UScalar.val e).symm)
    have agΩ1 : ∀ b ∈ Ω, L.mem s1 b = L.mem s b := fun b hb => hout1 b (h0.omega b hb)
    have ndR : ∀ (Y : S), (∀ o, L.nodeAt Y (L.cpu Y) o = L.nodeAt s (L.cpu s) o) → ∀ o : U64, o.val < 4288 →
        o.val % 8 = 0 → R (L.nodeAt Y (L.cpu Y) o) := fun Y e o h1 h2 => by rw [e]; exact nR o h1 h2
    have scK1 : ∀ y ∈ T, L.mem s1 (scA y) = L.mem s (scA y) := fun y hy => by
      rw [scA_eq]; exact htcb1 hy (by simp) (by simp)
    have rh1 : L.mem s1 (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) =
        L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) :=
      hnode1 _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
        (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
    have rhd : L.mem s1 (rhA (L := L) s1) ≠ 0#u64 → R (scA (L.mem s1 (rhA (L := L) s1))) ∧
        RdHead (L := L) R s1 (L.mem s1 (scA (L.mem s1 (rhA (L := L) s1)))) := by
      have e0 : L.mem s1 (rhA (L := L) s1) = L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) := by
        show L.mem s1 (L.nodeAt s1 (L.cpu s1) _) = _
        rw [c1, nodeAt_of_ksb k1, rh1]
      rw [e0]
      intro hne
      obtain ⟨r1, -, -, r4, r5⟩ := rel_facts hI hne
      rw [scK1 _ r1]
      have hqr := scq_of hO hS r4
      refine ⟨gRd _ ?_ (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne, Or.inl rfl⟩)))), ?_⟩
      · rw [scA_eq]; exact field_aligned (hT _ r1) (by simp) (by simp)
      · refine PathObl.ScAcc.head (W := fun _ => True) ⟨fun b ha hb => gRd _ ha
          (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne, Or.inr hb⟩)))), fun _ _ _ => trivial, trivial⟩ ?_
        refine (SCq.agree hqr agΩ1).1 ?_
        unfold LawfulStore.rmax
        rw [agΩ1 _ (hqr.2.1 _ hqr.2.2.2.2 hqr.2.2.2.1)]; exact r5
    have tm1e : L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.TIMER_MIN) =
        L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) := by
      rw [e1N]
      exact hnode1 _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
        (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
    have tm1 : L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.TIMER_MIN) ≠ 0#u64 →
        R (tdA (L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.TIMER_MIN))) := fun hne => by
      rw [tm1e] at hne ⊢
      have q1 := (tmin_facts (BXI.blk hI) hcC hne).1
      exact gRd _ (field_aligned (hT _ q1) (by simp) (by simp))
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne, Or.inl ⟨3528#u64, by simp, rfl⟩⟩)))))
    rw [PathObl.sched.cur_time.guard (gS := gS) s1 (ndR s1 e1N _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])),
      PathObl.sched.consumed.guard (gS := gS) s1 (ndR s1 e1N _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))]
    refine tr_bind_same (fun now _ => ?_)
    refine tr_bind_same (fun i4 _ => ?_)
    rw [PathObl.sporadic.sufficient.guard (gS := gS) ar s1 a1 (L.cscW s) i4 (hdC s1 agΩ1)]
    refine tr_bind_same (fun b4 _ => ?_)
    refine tr_ite (fun _ => ?_) (fun _ h => h)
    have gaq := localvm.awaken_quiet.guard (gS := gS) s1 now
      (ndR s1 e1N _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])) tm1
      (ndR s1 e1N _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])) rhd
      (ndR s1 e1N _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
    rw [c1] at gaq
    rw [gaq]
    refine tr_bind_same (fun b5 _ => ?_)
    refine tr_ite (fun _ h => ?_) (fun _ h => h)
    exfalso
    obtain ⟨⟨s2, a2⟩, -, h⟩ := bind_eq_ok h
    try simp only [uncurry_apply_pair] at h
    obtain ⟨⟨x, s3, a3⟩, -, h⟩ := bind_eq_ok h
    try simp only [uncurry_apply_pair] at h
    obtain ⟨⟨s4, a4⟩, -, h⟩ := bind_eq_ok h
    try simp only [uncurry_apply_pair] at h
    have e := ok_inj_ff h
    simp at e
  -- the checks
  have hcsc : sched.cur_sc st s = ok (L.cscW s) := eq_of_spec_fd (sched.cur_sc.spec (L := L) s)
  revert h
  rw [vexit_eq, vexit_eq]
  unfold vexitHead
  rw [PathObl.sched.cur_thread.guard (gS := gS) s (nR _ (by rw [curth_val]; omega) (by rw [curth_val])), cur_thread_ok,
    PathObl.gst_cur_cpu (g := gS), L.cur_cpu_eq,
    PathObl.sched.cur_sc.guard (gS := gS) s (nR _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])),
    hcsc]
  simp only [bind_ok]
  rw [PathObl.obj.Tcb.state.guard (gS := gS) _ s rSt, vcpu.bound.guardT (gS := gS) s _ rVc, PathObl.obj.Tcb.bound_ntfn.guard (gS := gS) _ s rBn,
    current_vm_ok.guard (gS := gS) s _ _ _ rAf rYt rSc rCore
      (nR _ (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD])) rDm hD1,
    sched_quiet.guard (gS := gS) s (nR _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])) hD2
      (nR _ (by simp [layout.node.IPI_PENDING]) (by simp [layout.node.IPI_PENDING]))]
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  refine tr_bind_same (fun i _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  refine tr_ite (fun _ h => h) (fun hv => ?_)
  refine tr_bind_same (fun i1 _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  refine tr_bind_same (fun i2 ei2 => ?_)
  refine tr_ite (fun _ h => h) (fun hb2 => ?_)
  have hn2 : i2 = n := by
    by_contra hne; exact hb2 (bne_iff_ne.mpr hne)
  have hbn := ei2
  rw [eq_of_spec_fd (obj.Tcb.bound_ntfn.val (L := L) s _)] at hbn
  have hbn' : L.mem s (boundA (L.curW s)) = n := (ok_inj_ff hbn).trans hn2
  rw [vcpu.get.guard (gS := gS) s v _ (hRp hv), ntfn_quiet.guard (gS := gS) s n (hRn n hbn')]
  refine tr_bind_same (fun i3 _ => ?_)
  refine tr_ite (fun _ => tr_bind_same (fun b _ => tr_ite (fun _ => ?_) (fun _ h => h))) (fun _ => ?_)
  all_goals
    refine tr_bind_same (fun b1 eb1 => ?_)
    refine tr_ite (fun hb1 => ?_) (fun _ h => h)
    subst hb1
    obtain ⟨-, -, hsct, -⟩ := current_vm_ok_true eb1
    rw [PathObl.sched.is_schedulable.guard (gS := gS) s _ rSt rSc (by rw [hsct]; exact rMx) rIq]
    refine tr_bind_same (fun b2 _ => ?_)
    refine tr_ite (fun _ => ?_) (fun _ h => h)
    refine tr_bind_same (fun b3 eb3 => ?_)
    refine tr_ite (fun hb3 => ?_) (fun _ h => h)
    subst hb3
    exact tailD eb3 hsct

end main

end Fl4Proofs.P2
