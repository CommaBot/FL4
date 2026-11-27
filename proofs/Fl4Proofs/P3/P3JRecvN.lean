/-
P3 (p3J gen 28): **the blocking notification receive in `KWN`** (P1 EntryXG's `ntfn_block.kw` and QueueRecv's
`maybe_return_sched_context.kw` mirrored at `Kp = ∅`, `Nd = False`, as P2 FootN4 mirrored `send_block`; P1 and P2
untouched). P2-level, namespace `Fl4Proofs.P1`, FL4 only.

* `notification.maybe_return_sched_context.kwN0`: the unbind (`Tcb.set_sc`, `Sc.set_tcb`, P1 `unbind_state`) and the
  `reschedule_required` (P2 `reschedule_required.kwN`) write only `KWN ∅ False` words: the TCB field by
  `notIdW_field`, the SC's `TCB` word by `notIdW_out` (it lies in `Ω`, outside the nodes).
* `ntfn_append_kwN0`: `ntfn_append` of the thread being blocked (P1 `ntfn_append_kw` with P2 `EpFoot.kwN`).
* **`ntfn_block.footN0`**: the whole blocking path (state, block object, `schedule_tcb`, append, return of the
  notification's SC) is a `FootN ∅ False` footprint (P1 `blk_tail` for the invariants before the return).

`AcK` is vacuous at `Kp = ∅`. No premise; no sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JSysYield
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}
variable {A : Type _} {ar : machine.Arch A} {Ac : Set U64}

/-- `AcK` at no protected thread. -/
theorem acK_empty {s s' : S} : AcK st T ∅ s s' := fun _ h => absurd h (Set.notMem_empty _)

/-- `ActOut` at no protected thread. -/
theorem actOut_empty {s : S} : ActOut st T ∅ s := fun _ => Set.notMem_empty _

set_option maxHeartbeats 4000000 in
/-- **`maybe_return_sched_context` in `KWN ∅ False`** (module docstring). -/
theorem notification.maybe_return_sched_context.kwN0 (s : S) (n t : U64)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T)
    (hout : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64 ∧
      L.actionW s ≠ t)
    (hidle : L.idleW s ≠ t) {Es : Set U64} :
    notification.maybe_return_sched_context st s n t ⦃ s' => FootN st ∅ False T Cs Sg Scs Z Es s s' ⦄ := by
  have hT := h.tcbs
  have hta := hT t ht
  unfold notification.maybe_return_sched_context
  step with obj.Ntfn.sc.any as ⟨i, _⟩
  step with obj.Sc.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 (FootN.refl s)
  rename_i hb
  have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
  step with obj.Tcb.sc.spec as ⟨i1, ei1⟩
  split
  · rename_i hii
    have hsc : L.mem s (scA t) = i := by rw [← ei1, hii]
    step with obj.Tcb.set_sc.wr as ⟨s1, e1⟩
    step with obj.Sc.set_tcb.wr as ⟨s2, e2⟩
    have key := unbind_state h hB hX hS hSg ht hout hidle hsc hi0
    rw [← e1, ← e2] at key
    have k1 := key.1
    obtain ⟨hiS, -, -⟩ := hX.2.2.bound t ht (by rw [hsc]; exact hi0)
    rw [hsc] at hiS
    obtain ⟨hP, hz⟩ := hX.1.sc i hiS
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hv := scTcbA_val (c := i) hP hz
    have hal1 : Aligned (scA t) := by rw [scA_eq]; exact field_aligned hta (by simp) (by simp)
    have hal2 : Aligned (scTcbA i) := by unfold Aligned; rw [hv]; omega
    have hin : InSC i (Z i) (scTcbA i) := ⟨by rw [hv]; omega, by rw [hv]; omega⟩
    have w2 : WritesIn st s s2 (fun b => b = scA t ∨ b = scTcbA i) := by
      rw [e2, e1]; exact (writesIn_wr hal1).trans (writesIn_wr hal2)
    have F2 : FootN st ∅ False T Cs Sg Scs Z Es s s2 := by
      refine FootN.of' w2 (fun b _ hb => ?_) acK_empty
      rcases hb with rfl | rfl
      · rw [scA_eq]
        exact ⟨kw_field ht (by simp) (by simp) (by simp),
          notIdW_field hT h.nodes ht (by simp) ⟨fun h => absurd h (Set.notMem_empty _), fun h => h.elim⟩⟩
      · exact ⟨kw_sc hiS hin, notIdW_out h.nodes (h.omega _ (hX.1.scW i hiS _ hal2 hin)) (fun h => h.elim)⟩
    step with sched.cur_thread.spec as ⟨t1, et1⟩
    step with tcb_eq.blk as ⟨b1, eb1⟩
    split
    · exact WP.spec_mono (sched.reschedule_required.kwN (Sg := Sg) (Kp := ∅) (Nd := False) (Scs := Scs) (Z := Z)
        (Es := Es) s2 k1 actOut_empty) fun s3 f3 => F2.trans f3
    · exact (WP.spec_ok _).2 F2
  · exact (WP.spec_ok _).2 (FootN.refl s)

/-- `ntfn_append` of a thread being blocked in `KWN ∅ False` (P1 `ntfn_append_kw`). -/
theorem ntfn_append_kwN0 {s : S} {n t : U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H {y | y ∈ (∅ : Set U64) ∨ y = t} s Q R) (ht : t ∈ T) (hH : H n = some .ntfn) :
    notification.ntfn_append st s n t ⦃ s' => FootN st ∅ False T Cs Sg Scs Z (EH H) s s' ⦄ := by
  obtain ⟨E5, EQ5, hEW5⟩ := h.eps
  have he5 : n ∈ E5 := (hEW5.2.2.2.2.2.2.2.1 n).2 (Or.inr hH)
  obtain ⟨hE5, hEN5, hq5⟩ := hEW5.1 n he5
  have htn : t ∉ EQ5 n := fun hm => (hEW5.2.2.2.1 n he5 t hm).1 (Or.inr rfl)
  have hW : ∀ w ∈ t :: EQ5 n, w ∈ T := by
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact ht
    · exact hq5.mem w hw
  refine WP.spec_mono (notification.ntfn_append.foot s n t (EQ5 n) h.tcbs hE5 hq5 ht htn) fun s' w => ?_
  exact FootN.of' w (fun b _ hb => EpFoot.kwN (Sg := Sg) (Kp := ∅) (Nd := False) (Scs := Scs) (Z := Z)
    (Es := EH H) h.tcbs h.nodes hW (Or.inr hH) hE5 hEN5 (hEW5.2.2.1 n he5) (fun h => h.elim) hb) acK_empty

set_option maxHeartbeats 4000000 in
/-- **The blocking receive on a notification in `KWN ∅ False`** (module docstring). -/
theorem ntfn_block.footN0 (s : S) (a : A) (t n : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hc : CanBlock st T Ac s t) (hidle : L.idleW s ≠ t)
    (hH : H n = some .ntfn) (hst0 : L.epState s n = 0#u64 ∨ L.epState s n = 1#u64) :
    (do
      let s1 ← obj.Tcb.set_state st t s sched.TS_BLOCKED_ON_NTFN
      let s2 ← obj.Tcb.set_block_obj st t s1 n
      let s3 ← sched.schedule_tcb st s2 t
      let s4 ← notification.ntfn_append st s3 n t
      let s5 ← notification.maybe_return_sched_context st s4 n t
      ok (s5, a)) ⦃ s' _ => FootN st ∅ False T Cs Sg Scs Z (EH H) s s' ⦄ := by
  have ht := hc.mem
  have hta := h.tcbs t ht
  have hN := h.nodes _ h.cur
  step with obj.Tcb.set_state.spec as ⟨s1, e1⟩
  step with obj.Tcb.set_block_obj.wr as ⟨s2, e2⟩
  have h1 : SchedQueuesInvX st T Cs Ω H {y | y ∈ (∅ : Set U64) ∨ y = t} s1 Q R := by
    rw [e1]; exact blk_set_state h hc
  have h2 : SchedQueuesInvX st T Cs Ω H {y | y ∈ (∅ : Set U64) ∨ y = t} s2 Q R := by
    rw [e2]; exact inv_wr_fieldX (K := 3336#u64) h1 ht (Or.inr rfl) (by simp) (by simp) (by simp)
  rw [stA_eq] at e1
  have w2 : WritesIn st s s2 (BlkFoot st s t 0#u64) := by
    rw [e2, e1]; exact blk_wr_field hta (blk_wr_field (K := 3328#u64) hta (WritesIn.refl _ _) (by simp)) (by simp)
  have v2 : L.mem s2 (stA t) = sched.TS_BLOCKED_ON_NTFN := by
    rw [e2, fld_wr_ne' hta (blockA_eq t) (stA_eq t) (by simp) (by simp) (by simp) (by simp) (by simp), e1, stA_eq]
    exact L.mem_wr_same (field_aligned hta (by simp) (by simp))
  have b2 : L.mem s2 (blockA t) = n := by
    rw [e2]; exact L.mem_wr_same (field_aligned hta (by simp) (by simp))
  have a2 : L.actionW s2 = L.actionW s := by
    rw [e2, act_wr_field (h1.nodes _ h1.cur) ht hta (blockA_eq t) (by simp) (by simp),
      e1, act_wr_field hN ht hta rfl (by simp) (by simp)]
  have hbl : Blocked sched.TS_BLOCKED_ON_NTFN := Or.inr (Or.inr rfl)
  refine WP.spec_bind (sched.schedule_tcb.blk s2 t h2 (by rw [v2]; exact blocked_not_runnable hbl)) ?_
  rintro s3 ⟨h3, e3, hc3⟩
  obtain ⟨w3, a3, v3, b3, -, -⟩ := blk_sched h2 ht w2 a2 e3
  rw [v2] at v3; rw [b2] at b3
  have F3 : FootN st ∅ False T Cs Sg Scs Z (EH H) s s3 := blkfoot_footN h ht (Set.notMem_empty _) w3 acK_empty
  obtain ⟨-, -, r3, -, r6⟩ := ts_vals
  refine WP.spec_bind (WP.spec_and (blk_tail (f := notification.ntfn_append st s3 n t) (r0 := 0#u64) (hidl := hidle)
    h hB hX hS hSg ht
    (Or.inr (Or.inr ⟨rfl, hH, rfl⟩)) hst0 h3 w3 a3 v3 b3 (fun h0 => absurd rfl h0)
    (fun h1 => absurd (v3.symm.trans h1) (by rw [r3, r6]; decide)) hc.old (fun h0 => absurd rfl h0) hc.ac
    (fun xs hE hq hn => WP.spec_mono (WP.spec_and
      (notification.ntfn_append.rel s3 n t xs h3.tcbs hE hq ht hn)
      (notification.ntfn_append.foot s3 n t xs h3.tcbs hE hq ht hn))
      fun s4 hh => ⟨hh.1.1, by rw [hh.1.2, ntfn_wait_val], hh.2⟩))
    (ntfn_append_kwN0 (Sg := Sg) (Scs := Scs) (Z := Z) h3 ht hH)) ?_
  rintro s4 ⟨⟨h4, hB4, hX4, hS4, hSg4, ea4, ec4, v4, ei4⟩, F4⟩
  refine WP.spec_bind (notification.maybe_return_sched_context.kwN0 (Es := EH H) s4 n t Q R h4 hB4 hX4 hS4 hSg4 ht
    (blocked_out h4 ht (by rw [v4]; exact blocked_not_runnable hbl)) (by rw [ei4]; exact hidle)) ?_
  rintro s5 F5
  simp only [WP.spec_ok, WP.uncurry'_pair]
  exact F3.trans (F4.trans F5)

end

end Fl4Proofs.P1
