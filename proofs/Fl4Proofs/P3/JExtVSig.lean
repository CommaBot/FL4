/-
P3 (line mmuAD, gen 22): **`complete_signal`'s footprint in VM epochs, and `vcpu.enter` of a bound thread without
`hcs`.**

## The footprint (P1 level, namespace `Fl4Proofs.P1`)

`notification.complete_signal.vmK`: from P1's `BlkOK` at the call state, a TCB `t ∈ T` that is not `BlockedR`
(the thread entering the VM is running) and a heap notification `n ∈ Nt`, `complete_signal` (the badge register,
the notification's state word, `maybe_donate_sched_context` — `donate` + `resume` — and the sporadic
`unblock_check`) ends in

* `BlkOK` again,
* **every TCB's VCPU word (offset 3664) unchanged** (`FFoot.vc` of P2's no-donation-protected footprint
  `maybe_donate_sched_context.ffB`; the badge / notification / refill writes miss it),
* **every TCB's `STATE` word unchanged** (so no `TS_RUNNING_VM` is written; `maybe_donate_sched_context.stK`
  below: `donate.unbound`'s state frame and `resume.all`'s `Fr.st`),
* a `FootDB` footprint (`KW` without the `IPC_BUFFER` word, plus the debug-list words; P1
  `maybe_donate_sched_context.tinvFBK`), with `Es` the heap endpoints / notifications `EH H`.

**Why `BlkOK` is the right bundle.** It is the native joint invariant's own P1 field (`JAtZ.blk`, P3/JointAt
`joint`), and none of its statements mentions a VCPU: it is about scheduler queues, endpoint queues, SC
bindings and the frame words, and P1 already treats `TS_RUNNING_VM` as a runnable state (`Runnable`,
`QueueFootS` #63). It is stated over arbitrary P1 sets (`T Cs Ω H Sg Rp Scs Nt Z Ac`); the VM-epoch invariant
(not yet built) would carry it as a field, as `JAtZ` does natively. P1 has no weaker bundle for these three
functions: every one of their P1 / P2 footprint lemmas takes the five `BlkOK` components.

`capw_not_dbgB`, `capw_keep_footDB`: a cap-slot-class word (`CapW`: a TCB low word, or a word of `Ω` outside the
frame words `Sg`) is no `FootDB` word, so a `FootDB` step keeps it (with P1's `capw_not_kw`).

## `vcpu.enter` (namespace `Fl4Proofs.P3`)

**`vcpu_enter_boundK`**: `vcpu_enter_boundB` (P3/JExtVStepsB) with `hcs` discharged. Every branch of
`vcpu.enter` on a bound thread keeps `JExtV` and `RunVmB`. Its new premises, all [J] (placement / joint-state
facts that a VM-epoch joint invariant would provide; natively `JAtZ.blk`, `JAtZ.slotCapW`, P1's heap sets):

* `Bk` [J]: `BlkOK` at the entry state (the joint invariant's P1 field, as `JAtZ.blk`);
* `hTt` [J]: the abstract TCBs are P1 TCBs (`th t = some .tcb → t ∈ T`; natively `JPlaced.tcb`);
* `hSC` [J]: `Sched.SlotCapW th T Ω Sg` (every slot word is a cap-slot word; natively `JAtZ.slotCapW`);
* `hVo` [J]: every aligned word of a VCPU of `V` (2^15 bytes) is a word of `Ω` outside `Sg` — a VCPU is a
  heap `.other 15` object, whose words are `Heap.omega` and not `Heap.frame` (P1/QueueHeap);
* `hNt` [J]: `Nt`'s members are heap notifications (true of the instantiation `Nt := H.ntfns`);
* `hRt` [J]: the entering thread is not `BlockedR` (it is the running caller of `SysVMEnter`).

The other premises are `vcpu_enter_boundB`'s (`DetPl`, `DetAtB`, `hvi`, all [J], derived from `JAtZ` + `JVm`
by P3/JExtVLay). No [P] / [W] / [S] premise. No existing statement changed. No P2 [S] item is discharged:
there is still no reachable VM-epoch joint invariant (module docstring of P3/JExtVStepsB, handoff gen 22).
-/
import Fl4Proofs.P3.JExtVStepsB
import Fl4Proofs.P3.ScInstFoot
import Fl4Proofs.P2.FootN8
import Fl4Proofs.P1.QueueFootS
open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- A cap-slot-class word is no debug-list word. -/
theorem capw_not_dbgB {s : S} {w : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hw : CapW T Ω Sg w)
    (hd : DbgW st T Cs s w) : False := by
  obtain ⟨⟨Q, R, h0⟩, -, -, -, -⟩ := h
  have hT := h0.tcbs
  rcases hd with ⟨y, hy, e | e⟩ | ⟨c, hc, e⟩
  · rcases hw with hl | ⟨hm, -⟩
    · exact (tlow_ne_field (K := 3576#u64) hT hy (by simp) (by simp) hl) e
    · exact out_ne_field (K := 3576#u64) (h0.omega _ hm) hy (hT y hy) (by simp) (congrArg UScalar.val e).symm
  · rcases hw with hl | ⟨hm, -⟩
    · exact (tlow_ne_field (K := 3584#u64) hT hy (by simp) (by simp) hl) e
    · exact out_ne_field (K := 3584#u64) (h0.omega _ hm) hy (hT y hy) (by simp) (congrArg UScalar.val e).symm
  · rcases hw with hl | ⟨hm, -⟩
    · exact (tlow_ne_node hT (h0.nodes c hc) (by rw [debug_val]; omega) hl) e.symm
    · exact out_ne_node (h0.omega _ hm) hc (h0.nodes c hc) (by rw [debug_val]; omega)
        (congrArg UScalar.val e).symm

/-- **A `FootDB` step keeps every cap-slot-class word.** -/
theorem capw_keep_footDB {s s' : S} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (f : FootDB st T Cs Sg Scs Z (EH H) s s') {w : U64} (hw : CapW T Ω Sg w) (hwa : Aligned w) :
    L.mem s' w = L.mem s w :=
  WritesIn.mem_eq f hwa fun hb => hb.elim (fun hk => capw_not_kw h hw hwa (le_refl _) (by omega) (KWB.kw hk))
    (fun hd => capw_not_dbgB h hw hd)

/-- **`maybe_donate_sched_context` keeps every TCB's `STATE` word** (under `ffB`'s / `tinvFBK`'s hypotheses):
the donation (`donate.unbound`) keeps the states, `resume` keeps them (`Fr.st`). -/
theorem notification.maybe_donate_sched_context.stK {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (t n : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T)
    (hns : L.mem s (ntfnScA n) ≠ 0#u64 → L.mem s (scTcbA (L.mem s (ntfnScA n))) = 0#u64 →
      L.mem s (scA t) = 0#u64 → L.mem s (ntfnScA n) ∈ Scs ∧ L.mem s (scCoreA (L.mem s (ntfnScA n))) ∈ Cs ∧
        (Sch st s t → L.mem s (ntfnScA n) ∈ Ac)) :
    notification.maybe_donate_sched_context st ar s a t n ⦃ s' _ => ∀ y ∈ T, L.mem s' (stA y) = L.mem s (stA y) ⦄ := by
  have ok0 : (ok (s, a) : Result (S × A)) ⦃ s' _ => ∀ y ∈ T, L.mem s' (stA y) = L.mem s (stA y) ⦄ :=
    (WP.spec_ok _).2 fun _ _ => rfl
  by_cases h0 : L.mem s (scA t) = 0#u64
  swap
  · unfold notification.maybe_donate_sched_context
    step with obj.Tcb.sc.spec as ⟨i, ei⟩
    rw [if_neg (by rw [ei]; exact h0)]
    exact ok0
  have htq : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 := by by_contra hq; exact hB.q t ht hq h0
  have htr : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by by_contra hq; exact hB.r t ht hq h0
  have hta' : L.actionW s ≠ t := fun e => hB.act (by rw [e]; exact ht) (by rw [e]; exact h0)
  have hti : L.idleW s ≠ t := fun e => hB.idle (by rw [e]; exact h0)
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
        hcore1 hsA1 (by rw [← ei, hi]) hti) ?_
      rintro ⟨s4, a4⟩ ⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, st4, -, -, sc4, tc4, ea4⟩
      try simp only [WP.uncurry'_pair]
      refine WP.spec_mono (schedcontext.resume.all hA s4 a4 i1 Q4 R4 h4 hB4 hX4 hSg4 hS4 fun _ _ => ?_) ?_
      · obtain ⟨-, -, hc4⟩ := hX4.2.2.bound t ht (by rw [sc4]; exact hi10)
        rw [sc4] at hc4
        rw [tc4]
        exact ⟨ht, h4.omega _ ((objs_omega hX4.1 hSg4.sub).2 i1 hS1).2.1, hc4, by rw [ea4]; exact hta'⟩
      · rintro ⟨s5, a5⟩ ⟨Q5, R5, h5, hB5, hX5, hSg5, f5⟩
        exact fun y hy => (f5.st y hy).trans (st4 y hy)
    · exact ok0
  · exact ok0

set_option maxHeartbeats 8000000 in
/-- **`complete_signal` in a VM epoch** (module docstring): `BlkOK` kept, every TCB's VCPU and `STATE` word
unchanged, a `FootDB` footprint. -/
theorem notification.complete_signal.vmK {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (n t : U64) (Bk : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T)
    (hR : ¬ BlockedR (L.mem s (stA t))) (hn : n ∈ Nt) (hnH : H n = some .ntfn) :
    notification.complete_signal st ar s a n t ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      (∀ y ∈ T, L.mem s' (core.num.U64.wrapping_add y 3664#u64) = L.mem s (core.num.U64.wrapping_add y 3664#u64)) ∧
      (∀ y ∈ T, L.mem s' (stA y) = L.mem s (stA y)) ∧ FootDB st T Cs Sg Scs Z (EH H) s s' ⦄ := by
  obtain ⟨⟨Q, R, h⟩, hB, hX, hS, hSg⟩ := Bk
  have hT := h.tcbs
  have hta := hT t ht
  have hN := h.nodes _ h.cur
  have ok0 : (ok (s, a) : Result (S × A)) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      (∀ y ∈ T, L.mem s' (core.num.U64.wrapping_add y 3664#u64) = L.mem s (core.num.U64.wrapping_add y 3664#u64)) ∧
      (∀ y ∈ T, L.mem s' (stA y) = L.mem s (stA y)) ∧ FootDB st T Cs Sg Scs Z (EH H) s s' ⦄ :=
    (WP.spec_ok _).2 ⟨⟨⟨Q, R, h⟩, hB, hX, hS, hSg⟩, fun _ _ => rfl, fun _ _ => rfl, FootB.d (FootB.refl _)⟩
  obtain ⟨E, EQ, hEW⟩ := h.eps
  have he : n ∈ E := (hEW.2.2.2.2.2.2.2.1 n).2 (Or.inr hnH)
  obtain ⟨hE, -, -⟩ := hEW.1 n he
  have hnE : n ∈ EH H := Or.inr hnH
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
  have ts1 : L.mem (L.wr s (core.num.U64.wrapping_add t 256#u64) b1) (epTSA n) = L.mem s (epTSA n) :=
    L.mem_wr_ne ha1 (ep_aligned hE).2 (by
      rw [field_val hta (by simp), epTSA_val hE]; have := hE.disj t ht; simp; omega)
  have hact1 : L.epState (L.wr s (core.num.U64.wrapping_add t 256#u64) b1) n = 2#u64 := by
    simp only [LawfulStore.epState]; rw [ts1]; exact hact
  have B1 : FootDB st T Cs Sg Scs Z (EH H) s (L.wr s (core.num.U64.wrapping_add t 256#u64) b1) :=
    FootB.d (footB_field hT ht (by simp) (by simp) (by simp) (by simp))
  set s1 := L.wr s (core.num.U64.wrapping_add t 256#u64) b1 with hs1
  refine WP.spec_bind (obj.Ntfn.set_state.val s1 n _) fun s2 e2 => ?_
  subst e2
  obtain ⟨h2, hB2, hX2, hS2, hSg2, f2, o2, ea2, ei2, ec2⟩ := ntfn_idle_all h1 hB1 hX1 hS1 hSg1 hnH hact1
  have B2 : FootDB st T Cs Sg Scs Z (EH H) s1
      (L.wr s1 (epTSA n) ((L.mem s1 (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64))) :=
    FootB.d (footB_wr (ep_aligned hE).2 (kwB_ep hnE (Or.inr rfl)))
  set s2 := L.wr s1 (epTSA n) ((L.mem s1 (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64)) with hs2
  have F : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 → (y = t → K.val ≠ 256) →
      L.mem s2 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K hK hK8 h1' h2' h3' => (f2 y hy K hK hK8 h1' h2').trans (f1 y hy K hK hK8 h3')
  have vk2 : ∀ y ∈ T, L.mem s2 (core.num.U64.wrapping_add y 3664#u64) = L.mem s (core.num.U64.wrapping_add y 3664#u64) :=
    fun y hy => F y hy _ (by simp) (by simp) (by simp) (by simp) (fun _ => by simp)
  have st2 : ∀ y ∈ T, L.mem s2 (stA y) = L.mem s (stA y) := fun y hy => by
    rw [stA_eq]; exact F y hy _ (by simp) (by simp) (by simp) (by simp) (fun _ => by simp)
  have sc2 : L.mem s2 (scA t) = L.mem s (scA t) := by
    rw [scA_eq]; exact F t ht _ (by simp) (by simp) (by simp) (by simp) (fun _ => by simp)
  have hsA2 : L.mem s2 (scA t) = 0#u64 → ¬ Sch st s2 t := fun h0 hS2t => by
    have f21 : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
        L.mem s2 (core.num.U64.wrapping_add t K) = L.mem s1 (core.num.U64.wrapping_add t K) :=
      fun K a1 a2 a3 a4 => f2 t ht K a1 a2 a3 a4
    have hS1t : Sch st s1 t := Sch.of_eq
      (fun hf => by rwa [inqA_eq, f21 _ (by simp) (by simp) (by simp) (by simp)] at hf)
      (fun hf => by rwa [inqA_eq, f21 _ (by simp) (by simp) (by simp) (by simp)] at hf)
      ea2 ei2 ec2 (by rw [stA_eq]; exact f21 _ (by simp) (by simp) (by simp) (by simp)) hS2t
    have hSt : Sch st s t := Sch.wr_field h ht (by simp) (by simp) (by simp) ht hS1t
    have h0' : L.mem s (scA t) = 0#u64 := by rw [← sc2]; exact h0
    rcases hSt with e | e | e | e | ⟨e1, e2⟩ | e
    · exact hB.q t ht e h0'
    · exact hB.r t ht e h0'
    · exact hB.act (by rw [e]; exact ht) (by rw [e]; exact h0')
    · exact hB.idle (by rw [e]; exact h0')
    · exact hB.resume e1 (by rw [e2]; exact h0')
    · exact hR e
  have hns2 := ntfn_sc_ok (Ac := Ac) hX2 hn hsA2
  refine WP.spec_bind (WP.spec_and (WP.spec_and
    (Fl4Proofs.P2.Stall.notification.maybe_donate_sched_context.ffB (Kp := ∅) (Il := ∅) (Ks := ∅) (Es := EH H)
      (U := ∅) hA s2 a t n Q R h2 hB2 hX2 hS2 hSg2 ht hns2 (Set.notMem_empty t) (Set.notMem_empty t)
      (fun k hk => absurd hk (Set.notMem_empty k)))
    (notification.maybe_donate_sched_context.tinvFBK (Es := EH H) hA s2 a t n Q R h2 hB2 hX2 hS2 hSg2 ht hns2))
    (notification.maybe_donate_sched_context.stK hA s2 a t n Q R h2 hB2 hX2 hS2 hSg2 ht hns2)) ?_
  rintro ⟨s3, a1⟩ ⟨⟨⟨⟨⟨Q3, R3, h3⟩, hB3, hX3, hS3, hSg3⟩, F3⟩, -, -, B3, -⟩, st3⟩
  try simp only [WP.uncurry'_pair]
  have vk3 : ∀ y ∈ T, L.mem s3 (core.num.U64.wrapping_add y 3664#u64) =
      L.mem s (core.num.U64.wrapping_add y 3664#u64) := fun y hy =>
    (Fl4Proofs.P2.Stall.FFoot.vc h2 hX2.1 F3 y hy).trans (vk2 y hy)
  have sk3 : ∀ y ∈ T, L.mem s3 (stA y) = L.mem s (stA y) := fun y hy => (st3 y hy).trans (st2 y hy)
  have B03 : FootDB st T Cs Sg Scs Z (EH H) s s3 := (B1.trans B2).trans B3
  have ok3 : (ok (s3, a1) : Result (S × A)) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      (∀ y ∈ T, L.mem s' (core.num.U64.wrapping_add y 3664#u64) = L.mem s (core.num.U64.wrapping_add y 3664#u64)) ∧
      (∀ y ∈ T, L.mem s' (stA y) = L.mem s (stA y)) ∧ FootDB st T Cs Sg Scs Z (EH H) s s' ⦄ :=
    (WP.spec_ok _).2 ⟨⟨⟨Q3, R3, h3⟩, hB3, hX3, hS3, hSg3⟩, vk3, sk3, B03⟩
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
        have hiA : i1 ∈ Ac := hS3.spor i1 hi1S (eb2 hb2).2
        have hW : RefillsWF st s3 i1 (Z i1) := hS3.wf hi1S hiA
        have hSCin : SCin st s3 Ω i1 (Z i1) := ⟨hW, hX3.1.scW i1 hi1S⟩
        have hN' := h3.nodes _ h3.cur
        have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
        have aR : Aligned (L.nodeA s3 layout.node.REPROGRAM) := nodeAt_aligned hN' (by rw [rp]; omega) (by rw [rp])
        have oR : Outside (L.nodeA s3 layout.node.REPROGRAM) i1 (Z i1) :=
          hSCin.node_out h3.omega h3.cur hN' (by rw [rp]; omega) (by rw [rp])
        refine WP.spec_bind (WP.spec_and (sporadic.unblock_check.all s3 t i1 h3 hB3 hX3 hS3 hSg3 ht ei1 (eb2 hb2).1
          hiA) (sporadic.unblock_check.fr hW ⟨aR, oR⟩)) fun s5 ⟨hh, w5⟩ => ?_
        obtain ⟨h5, hB5, hX5, hS5, hSg5, -, -, -, f5, -⟩ := hh
        have B5 : FootDB st T Cs Sg Scs Z (EH H) s3 s5 := by
          refine FootB.d (FootB.of' w5 fun b _ hh => ?_)
          rcases hh with hr | rfl
          · exact InRing.kwB hi1S hr
          · exact kwB_node h3.cur (by rw [rp]; omega) (by rw [rp]; omega)
        exact (WP.spec_ok _).2 ⟨⟨⟨Q3, R3, h5⟩, hB5, hX5, hS5, hSg5⟩,
          fun y hy => (f5 y hy _ (by simp) (by simp)).trans (vk3 y hy),
          fun y hy => by have e := sk3 y hy; rw [stA_eq] at e ⊢; exact (f5 y hy _ (by simp) (by simp)).trans e,
          B03.trans B5⟩
      · exact ok3
    · exact ok3
  · exact ok3

end

end Fl4Proofs.P1
