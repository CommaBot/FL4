/-
P3 (DESIGN.md §9), scheduler: pieces of **`schedule`**.

* `checkDomainTime_eq`, `check_domain_time_refines`: with one domain the
  current domain never expires, so `check_domain_time` does nothing.
* `guardedSwitchTo_eq`: a ready-queue head is schedulable (`Inv.rq`, the
  queues are disjoint from the release queue) and in the current domain, so
  `guarded_switch_to` is `switch_to_thread`.
* `choose_thread_refines`: `choose_thread` against l4v `choose_thread`; the
  chosen thread is schedulable, or it is the idle thread.
-/
import Fl4Proofs.P3.ScSwitchTo
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

theorem checkDomainTime_eq (hnd : numDomains = 1) (σ : State Unit) :
    checkDomainTime (Z := Unit) σ = ({((), σ)}, False) := by
  unfold checkDomainTime
  rw [nd_gets_bind]
  have : isCurDomainExpired σ = false := by simp [isCurDomainExpired, hnd]
  rw [this]; rfl

theorem guardedSwitchTo_eq {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    {scp : ObjRef} (hsc : x.tcbSchedContext = some scp) (hs : schedulable t σ = true)
    (hd : x.tcbDomain = σ.curDomain) :
    guardedSwitchTo (Z := Unit) t σ = switchToThread t σ := by
  unfold guardedSwitchTo
  rw [nd_bind_one (threadGet_eq _ hk), hsc,
    nd_bind_one (show NonDet.assertOpt (σ := State Unit) (some scp) σ = ({(scp, σ)}, False) from rfl),
    nd_gets_bind, hs, nd_bind_one (assert_true rfl σ), nd_gets_bind, nd_bind_one (threadGet_eq _ hk), hd,
    nd_bind_one (assert_true rfl σ)]

end Spec

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- **A ready-queue member is schedulable and in the current domain.** -/
theorem ready_sched {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (hI : Inv σ) {u : Fl4Spec.ObjRef} {d : Fl4Spec.Domain} {p : Fl4Spec.Priority}
    (hu : u ∈ σ.readyQueues d p) : Fl4Spec.schedulable u σ = true ∧
      ∃ x scp, σ.kheap u = some (.tcb x) ∧ x.tcbSchedContext = some scp ∧ x.tcbDomain = σ.curDomain := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x, scp, y, n, h1, h2, h3, h4, h5⟩ := hI.rq d p u hu
  by_cases hd : d = 0
  · subst hd
    obtain ⟨p', hp', rfl⟩ := prio_of_spec p
    rw [hs.rq p' hp'] at hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hu
    have hvT := (hc.ready.1.rel p' hp').mem v hv
    have hnr : v ∉ R := hc.excl v hvT (by rw [hc.inQ p' hp' v hv]; exact hv)
    have hnr' : v.bv ∉ σ.releaseQueue := by rw [hs.rel, mem_map_bv]; exact hnr
    obtain ⟨x', hk', hd', -⟩ := hs.tcb v hvT
    rw [h1] at hk'; cases hk'
    exact ⟨schedulable_of h1 h2 h3 h4 h5 hnr', x, scp, h1, h2, by rw [hd', hs.curDom.1]⟩
  · rw [hs.rqDom d p hd] at hu; cases hu

theorem check_domain_time_refines (s : S) : sched.check_domain_time st s = ok s := by
  unfold sched.check_domain_time
  rw [is_cur_domain_expired_eq]; simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]

/-- **`choose_thread` refines l4v `choose_thread`.** -/
theorem choose_thread_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hvm : ∀ t ∈ T, vspace.set_vm_root st ar s a t ⦃ r => ∃ σ1, Fl4Spec.archSwitchToThread (Z := Unit) t.bv σ =
      ({((), σ1)}, False) ∧ SchedRel st N T C c r.1 σ1 ∧ NtfnStateRel N T (L.mem r.1) σ1 ∧ ArchKeeps σ σ1 ⦄)
    (hvmi : vspace.set_kernel_vm_root st ar s a ⦃ r => ∃ σ1, Fl4Spec.archSwitchToIdleThread (Z := Unit) σ =
      ({((), σ1)}, False) ∧ SchedRel st N T C c r.1 σ1 ∧ NtfnStateRel N T (L.mem r.1) σ1 ∧ ArchKeeps σ σ1 ⦄)
    (hidleT : (nodeW st s c layout.node.IDLE_THREAD).bv = σ.idleThread) :
    sched.choose_thread st ar s a ⦃ r => ∃ σ', Fl4Spec.chooseThread (Z := Unit) σ = ({((), σ')}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      (σ'.curThread = σ.idleThread ∨ Fl4Spec.schedulable σ'.curThread σ = true) ∧
      σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ σ'.kheap = σ.kheap ∧
      σ'.schedulerAction = σ.schedulerAction ∧ TK σ σ' ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  unfold sched.choose_thread
  rw [num_domains_eq, if_neg (by decide)]
  simp only [bind_ok]
  step with LawfulStore.cur_cpu_spec as ⟨cpu, hcpu⟩
  rw [hc.cur] at hcpu
  subst cpu
  unfold sched.bitmap_dom sched.l1_off
  rw [num_domains_eq, if_neg (by decide)]
  simp only [bind_ok, lift]
  step with obj.node_get.spec as ⟨l1, hl1⟩
  have hl1' : l1 = L.l1W s c := by
    rw [hl1]; unfold LawfulStore.l1W; congr 2
    unfold layout.node.L1_BITMAP l1Off w64; rfl
  subst hl1'
  split
  · rename_i hne0
    have hne : L.l1W s c ≠ 0#u64 := by simpa using hne0
    refine choose_pick_k s σ hS hne _ _ ?_
    rintro t ⟨ht, hteq, p, hmem⟩
    refine WP.spec_mono (switch_to_thread_refines s a σ hS hR hN ht (hvm t ht)) ?_
    rintro r ⟨σ', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    obtain ⟨hsch, x, scp, hk, hsc, hdom⟩ := ready_sched hS hI hmem
    refine ⟨σ', ?_, h2, h3, h4, h5 hI, Or.inr (by rw [h6]; exact hsch), h7, h8, h9, h10, h11⟩
    unfold Fl4Spec.chooseThread
    rw [nd_gets_bind, nd_gets_bind, if_neg (by rw [← choose_empty hS]; exact hne), ← hteq,
      guardedSwitchTo_eq hk hsc hsch hdom]
    exact h1
  · rename_i hne0
    have he : L.l1W s c = 0#u64 := by apply UScalar.eq_of_val_eq; simpa using hne0
    refine WP.spec_mono (switch_to_idle_thread_refines s a σ hS hR hN hidleT hvmi) ?_
    rintro r ⟨σ', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    refine ⟨σ', ?_, h2, h3, h4, h5 hI, Or.inl h6, h7, h8, h9, h10, h11⟩
    unfold Fl4Spec.chooseThread
    rw [nd_gets_bind, nd_gets_bind, if_pos ((choose_empty hS).1 he)]
    exact h1

end

end

end Fl4Proofs.P3.Sched
