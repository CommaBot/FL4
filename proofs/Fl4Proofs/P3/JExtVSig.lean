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

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A}
variable {V X : Set U64} {th : TypedHeap} {Ub : U64 → Set U64}
variable {T Cs Ω Sg Rp Scs Nt : Set U64} {H : P1.Heap} {Z : U64 → Nat} {Ac : Set U64}

/-- **[J] The VCPU objects are `Ω` words outside the frame words `Sg`** (every aligned word of a VCPU of `V`,
2^15 bytes): a VCPU is a heap `.other 15` object, whose words are `Heap.omega` and not `Heap.frame`
(P1/QueueHeap), so they are cap-slot-class words (`CapW`) to P1's invariants. -/
def VcpuOm (V Ω Sg : Set U64) : Prop :=
  ∀ v ∈ V, ∀ o : U64, o.val < 32768 → o.val % 8 = 0 →
    core.num.U64.wrapping_add v o ∈ Ω ∧ core.num.U64.wrapping_add v o ∉ Sg

set_option maxHeartbeats 16000000 in
/-- **`vcpu.enter` of a bound thread, every branch, without `hcs`** (module docstring): `vcpu_enter_boundB`'s
premise `hcs` [J] replaced by `notification.complete_signal.vmK` under the P1 bundle `Bk` [J] and the placement
facts `hTt`, `hSC`, `hVo`, `hNt`, `hRt` (all [J]). The VCPU writes are cap-slot-class writes (`hVo`), which keep
`BlkOK` (`P1.blk_of_capw`); `complete_signal` keeps every TCB's VCPU and state word and has a `FootDB` footprint,
which misses every slot word (`hSC`), every VCPU's `TCB` word (`hVo`) and the buffer words (`BufKeep`). Keeps
`JExtV` and `RunVmB`. -/
theorem vcpu_enter_boundK (hA : P0.ArchTotal ar) (D : DetPl V th Ub) {s : S} (Da : DetAtB st V th Ub s)
    (E : JExtV (L := L) V X th s) (R : RunVmB (L := L) th s) (a : A) {t : U64} (ht : th t = some .tcb)
    (hv0 : L.mem s (tVcpuA t) ≠ 0#u64)
    (hvi : ∀ b, VW (L.mem s (tVcpuA t)) b → P1.Aligned b ∧ ¬ JW V th b ∧ ¬ SW th b)
    (Bk : P1.BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hTt : ∀ y, th y = some .tcb → y ∈ T)
    (hSC : Sched.SlotCapW th T Ω Sg) (hVo : VcpuOm V Ω Sg) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (hRt : ¬ P1.BlockedR (L.mem s (P1.stA t))) :
    vcpu.enter st ar s a t ⦃ r => JExtV (L := L) V X th r.1 ∧ RunVmB (L := L) th r.1 ⦄ := by
  have P := D.pl
  have JWt : JW V th (tVcpuA t) := Or.inr (Or.inl ⟨t, ht, rfl⟩)
  have htT := hTt t ht
  obtain ⟨⟨Q0, R0, h0⟩, -, -, -, -⟩ := id Bk
  have hta := h0.tcbs t htT
  unfold vcpu.enter vcpu.bound
  refine WP.spec_bind (hA.vcpu_barrier a) fun a1 _ => ?_
  step as ⟨o, ho⟩
  simp only [lift, bind_ok]
  refine WP.spec_bind (P1.LawfulStore.read_spec s _) fun v ev => ?_
  subst ho
  have ev' : v = L.mem s (tVcpuA t) := ev
  have hvV : v ∈ V := by
    have := ((E.bnd t ht).resolve_left hv0).1
    rw [← ev'] at this; exact this
  rw [← ev'] at hv0 hvi
  rw [if_neg hv0]
  have VS : ∀ s1, P1.WritesIn st s s1 (VW v) → ∀ (o x : U64), o.val < 32768 → o.val % 8 = 0 →
      o.val ≠ 20480 → vcpu.set st s1 v o x ⦃ s' => P1.WritesIn st s s' (VW v) ⦄ := by
    intro s1 w1 o x h1 h2 h3
    have hb : VW v (core.num.U64.wrapping_add v o) := ⟨o, h1, h2, h3, rfl⟩
    unfold vcpu.set
    simp only [lift, bind_ok]
    exact WP.spec_mono (P1.LawfulStore.write_spec s1 _ _) fun s' e => by
      subst e
      exact (w1.trans (P1.writesIn_wr (hvi _ hb).1)).mono fun b h => h.elim id fun e => e ▸ hb
  have VM : ∀ s1, P1.WritesIn st s s1 (VW v) → ∀ (f x : U64),
      vcpu.write_vmcs st s1 v f x ⦃ s' => P1.WritesIn st s s' (VW v) ⦄ := by
    intro s1 w1 f x
    unfold vcpu.write_vmcs
    refine WP.spec_bind (P1.vcpu.vmcs_addr.off v f) ?_
    rintro _ ⟨o, h1, h2, rfl⟩
    have hb : VW v (core.num.U64.wrapping_add v o) := ⟨o, by omega, h2, by omega, rfl⟩
    exact WP.spec_mono (P1.LawfulStore.write_spec s1 _ _) fun s' e => by
      subst e
      exact (w1.trans (P1.writesIn_wr (hvi _ hb).1)).mono fun b h => h.elim id fun e => e ▸ hb
  refine WP.spec_bind (P0.msg.lookup_ipc_buffer.p0 _ _ _ _ L.total) fun b _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 _ _ _ _ _ L.total) fun ip _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 _ _ _ _ _ L.total) fun ctl _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 _ _ _ _ _ L.total) fun intr _ => ?_
  refine WP.spec_bind (hA.virtualization a1) fun i _ => ?_
  refine WP.spec_bind (Pₘ := fun s1 => P1.WritesIn st s s1 (VW v)) ?_ fun s1 w1 => ?_
  · split
    · have hRIP : vcpu.svm.RIP = ok 1400#u64 := by unfold vcpu.svm.RIP vcpu.svm.SAVE; rfl
      simp only [hRIP, bind_ok, lift, vcpu.get, shl_eq _ 32#i32 (by decide) (by decide)]
      refine WP.spec_bind (VS _ (P1.WritesIn.refl _ _) 1400#u64 _ (by simp) (by simp) (by simp)) fun s2 w2 => ?_
      refine WP.spec_bind (P1.LawfulStore.read_spec s2 _) fun old _ => ?_
      refine WP.spec_bind (VS _ w2 vcpu.svm.INTERCEPT_EXC _ (by simp [vcpu.svm.INTERCEPT_EXC])
        (by simp [vcpu.svm.INTERCEPT_EXC]) (by simp [vcpu.svm.INTERCEPT_EXC])) fun s3 w3 => ?_
      refine WP.spec_bind (P0.vcpu.full_reply.p0 _ _ _ L.total) fun b1 _ => ?_
      refine WP.spec_bind (Pₘ := fun _ => True) ?_ fun intr1 _ => ?_
      · cases b1
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact (WP.spec_ok _).2 trivial
        · simp only [↓reduceIte]
          exact WP.spec_bind (P1.LawfulStore.read_spec _ _) fun _ _ => (WP.spec_ok _).2 trivial
      exact VS _ w3 vcpu.svm.EVENT_INJ _ (by simp [vcpu.svm.EVENT_INJ]) (by simp [vcpu.svm.EVENT_INJ])
        (by simp [vcpu.svm.EVENT_INJ])
    · try simp only [lift, bind_ok]
      refine WP.spec_bind (VM _ (P1.WritesIn.refl _ _) _ _) fun s2 w2 => ?_
      refine WP.spec_bind (P0.vcpu.sanitize_vmcs.p0 _ _ _ _ hA) fun r _ => ?_
      refine WP.spec_bind P0.vcpu.PRIMARY_FORCED.p0 fun i1 _ => ?_
      refine WP.spec_bind (VM _ w2 _ _) fun s3 w3 => ?_
      exact VM _ w3 _ _
  refine WP.spec_bind (VS _ w1 vcpu.VALID 0#u64 (by simp [vcpu.VALID]) (by simp [vcpu.VALID])
    (by simp [vcpu.VALID])) fun s2 w2 => ?_
  refine WP.spec_bind (VS _ w2 vcpu.PENDING 0#u64 (by simp [vcpu.PENDING]) (by simp [vcpu.PENDING])
    (by simp [vcpu.PENDING])) fun s3 w3 => ?_
  have E3 := E.of_writes P w3 fun b h => (hvi b h).2.1
  have R3 := R.of_clean P w3 fun b h => (hvi b h).2
  have e3 : L.mem s3 (tVcpuA t) = v := by rw [w3.mem_eq (P.jw _ JWt) fun h => (hvi _ h).2.1 JWt, ← ev']
  have m3 : L.mem s3 (tVcpuA t) ≠ 0#u64 := by rw [e3]; exact hv0
  have vwT : ∀ K : U64, K.val < 4096 → ¬ VW v (core.num.U64.wrapping_add t K) := fun K hK hb => by
    obtain ⟨o, h1, h2, -, e⟩ := hb
    exact P1.out_ne_field (h0.omega _ (hVo v hvV o h1 h2).1) htT hta hK (congrArg UScalar.val e)
  have hcw3 : ∀ b, VW v b → P1.CapW T Ω Sg b := fun b hb => by
    obtain ⟨o, h1, h2, -, e⟩ := hb
    rw [e]; exact Or.inr (hVo v hvV o h1 h2)
  obtain ⟨Bk3, -, -, -, -, fld3, -, -⟩ := P1.blk_of_capw Bk w3 hcw3
  have hact : P1.Aligned (actA st s3) ∧ ¬ JW V th (actA st s3) ∧ ¬ SW th (actA st s3) := by
    rw [actA_of w3]; exact ⟨Da.actA_al, (Da.nd _ (Or.inr rfl)).1, (Da.nd _ (Or.inr rfl)).2⟩
  have FIN : (do
      let s4 ← sched.set_thread_state st s3 t sched.TS_RUNNING_VM
      ok (s4, a1)) ⦃ r => JExtV (L := L) V X th r.1 ∧ RunVmB (L := L) th r.1 ⦄ :=
    WP.spec_bind (sts_jv P E3 R3 ht hact (Or.inr m3)) fun s4 h4 => (WP.spec_ok _).2 h4
  refine WP.spec_bind (P1.obj.Tcb.bound_ntfn.val s3 t) fun n en => ?_
  split
  · rename_i hn0
    refine WP.spec_bind (P0.obj.Ntfn.state.p0 st n s3 L.total) fun x _ => ?_
    split
    · have hn0' : n ≠ 0#u64 := by simpa using hn0
      have hnN : n ∈ Nt := by rw [en]; exact Bk3.2.2.1.2.2.bnd t htT (by rw [← en]; exact hn0')
      have hR3 : ¬ P1.BlockedR (L.mem s3 (P1.stA t)) := by
        rw [P1.stA_eq, fld3 t htT _ (by simp) (by simp) (by simp), ← P1.stA_eq]; exact hRt
      refine WP.spec_bind (P1.notification.complete_signal.vmK hA s3 a1 n t Bk3 htT hR3 hnN (hNt n hnN)) ?_
      rintro ⟨s4, a2⟩ ⟨Bk4, vk4, sk4, B4⟩
      try simp only [uncurry_apply_pair]
      obtain ⟨⟨Q3, R3', h3⟩, -, hX3, -, hSg3⟩ := id Bk3
      have kw : ∀ w, P1.CapW T Ω Sg w → P1.Aligned w → L.mem s4 w = L.mem s3 w := fun w hw hwa =>
        P1.capw_keep_footDB Bk3 B4 hw hwa
      have E4 : JExtV (L := L) V X th s4 := by
        refine E3.of_eq (fun y hy => ?_) (fun t' ht' => vk4 t' (hTt t' ht')) (fun w hw => ?_)
        · have c0 : P1.CapW T Ω Sg y := hSC y ⟨y, hy, 0#u64, Or.inl rfl, (wordOf_zero y).symm⟩
          have c8 : P1.CapW T Ω Sg (wordOf y 8#u64) := hSC _ ⟨y, hy, 8#u64, Or.inr (Or.inl rfl), rfl⟩
          unfold capV
          rw [kw y c0 (P.jw y (Or.inl ⟨y, hy, Or.inl rfl⟩)), kw _ c8 (P.jw _ (Or.inl ⟨y, hy, Or.inr rfl⟩))]
        · exact kw _ (Or.inr (hVo w hw vcpu.TCB (by simp [vcpu.TCB]) (by simp [vcpu.TCB])))
            (P.jw _ (Or.inr (Or.inr ⟨w, hw, rfl⟩)))
      have R4 : RunVmB (L := L) th s4 := fun t' ht' h8 => by
        have e' : L.mem s4 (tVcpuA t') = L.mem s3 (tVcpuA t') := vk4 t' (hTt t' ht')
        rw [e']
        exact R3 t' ht' (by rw [← sk4 t' (hTt t' ht')]; exact h8)
      have m4 : L.mem s4 (tVcpuA t) = v := (vk4 t htT).trans e3
      have bk := P1.BufKeep.of_footDB h3 hX3.1 hSg3.sub (fun e he => he) B4
      have hI : P1.IbSame (L := L) s s4 t := by
        refine ⟨(bk t htT).1.trans (fld3 t htT 3512#u64 (by simp) (by simp) (by simp)),
          (bk t htT).2.1.trans ?_, (bk t htT).2.2.trans ?_⟩
        · show L.mem s3 (P1.sbWordA t) = L.mem s (P1.sbWordA t)
          rw [P1.sbWordA_eq]; exact w3.mem_eq (P1.field_aligned hta (by simp) (by simp)) (vwT 64#u64 (by simp))
        · show L.mem s3 (core.num.U64.wrapping_add (P1.sbWordA t) 8#u64) =
            L.mem s (core.num.U64.wrapping_add (P1.sbWordA t) 8#u64)
          rw [P1.sbWordA8_eq]; exact w3.mem_eq (P1.field_aligned hta (by simp) (by simp)) (vwT 72#u64 (by simp))
      have hbuf4 : msg.lookup_ipc_buffer st s4 true t ⦃ P1.BufOK (Ub t) ⦄ := by
        rw [P1.lookup_ipc_buffer_same hI]; exact Da.buf s (P1.WritesIn.refl _ _) t ht
      have hA4 : actA st s4 = actA st s := actA_of (P1.WritesIn.trans w3 B4)
      have al4 : P1.Aligned (actA st s4) := by rw [hA4]; exact Da.actA_al
      refine WP.spec_bind (P0.vcpu.full_reply.p0 st s4 t L.total) fun b1 _ => ?_
      split
      · refine WP.spec_bind (P0.obj.Tcb.reg.p0 st t s4 _ L.total) fun i3 _ => ?_
        have hpa : P1.Aligned (pendA (L.mem s4 (tVcpuA t))) := by rw [m4]; exact (D.vca v hvV).1
        have hne : actA st s4 ≠ P1.stA t := fun e => (Da.nd _ (Or.inr rfl)).2 ⟨t, ht, hA4.symm.trans e⟩
        refine WP.spec_bind (vcpu_report_w hA a2 (D.ta t ht) (D.ua t ht) hbuf4
          hpa (P.sw _ ⟨t, ht, rfl⟩) al4 hne) fun s5 ⟨w, e5⟩ => ?_
        have cl : ∀ b, (P1.RepW t (Ub t) b ∨ b = pendA (L.mem s4 (tVcpuA t)) ∨ b = P1.stA t ∨ b = actA st s4) →
            ¬ JW V th b := by
          rintro b (h | e | e | e)
          · exact (D.rep t ht b h).1
          · rw [m4] at e; exact (D.vc v hvV b (Or.inl e)).1
          · exact P.swjw b ⟨t, ht, e⟩
          · exact (Da.nd b (Or.inr (e.trans hA4))).1
        refine (WP.spec_ok _).2 ⟨E4.of_writes P w cl, R4.of_foot P w (fun t' ht' hw => ?_) (fun t' ht' hw => ?_)⟩
        · rcases hw with h | e | e | e
          · exact ((D.rep t ht _ h).2 ⟨t', ht', rfl⟩).elim
          · rw [m4] at e; exact ((D.vc v hvV _ (Or.inl e)).2 ⟨t', ht', rfl⟩).elim
          · left; rw [stA_inj e, e5]; simp [sched.TS_RUNNING]
          · exact ((Da.nd _ (Or.inr (e.trans hA4))).2 ⟨t', ht', rfl⟩).elim
        · exact ((cl _ hw) (Or.inr (Or.inl ⟨t', ht', rfl⟩))).elim
      · refine WP.spec_bind (P1.obj.Tcb.set_reg.wrS s4 t layout.reg.MSG_INFO 0#u64 (D.ta t ht)
          (by simp [layout.reg.MSG_INFO, layout.reg.RSI])) fun s5 ⟨K, hK, e⟩ => ?_
        subst e
        have hr : (layout.reg.MSG_INFO).val = 1 := by simp [layout.reg.MSG_INFO, layout.reg.RSI]
        have hw := P1.writesIn_wr (st := st) (s := s4) (v := 0#u64)
          (P1.field_aligned (D.ta t ht) (K := K) (by omega) (by omega))
        have hR : P1.RepW t (Ub t) (core.num.U64.wrapping_add t K) := Or.inl ⟨K, by omega, by omega, by omega, rfl⟩
        have hd : ∀ b, b = core.num.U64.wrapping_add t K → ¬ JW V th b ∧ ¬ SW th b := fun b e =>
          e ▸ D.rep t ht _ hR
        exact (WP.spec_ok _).2 ⟨E4.of_writes P hw fun b h => (hd b h).1, R4.of_clean P hw hd⟩
    · exact FIN
  · exact FIN


end

end

end Fl4Proofs.P3
