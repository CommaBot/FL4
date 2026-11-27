/-
P1 (aarch64, gen 32): **the Thread kind's finalisation over `JV`, with the refuted [P] `rcw` replaced by `VcTy`.**

`W7.R.finRv_thread` (QueueFinRvSt) and QueueUnbindB's `fin_thread.ubR` read the run VCPU's and the bound VCPU's
facts through placements stated at every `Fr0 ∧ BXI` state ([P] `rcw`, [P] `VcPl`), refuted in gen 28–29. Here the
same chain is re-walked from **one state's `VcTy`** (QueueVcTy), which every step of `vcpu::detach` keeps:

* **`VKeepZ`**: the `VcTy` words kept **or zeroed** (a VCPU's `TCB` / `OWNER_CPU` / `RUN_CALLER` word, never its
  `RUN_OFFSET` word; a thread's bound-VCPU / `RUN_VCPU` word), the buffer slots' caps kept or `Null`.
  `VcTy.keepZ`: `VcTy` accepts `0` in every zeroed word (`VcObj`: `0` or a thread; links: `0` or in `Vc`; a thread
  whose `RUN_VCPU` is `0` has no run frame to type).
* **`DS s s'`** = `OSKeep OS s s'` (every `OS` word kept, so `SlotTy`) ∧ `VKeepZ`. The steps:
  `DS.of_fr` (`remote_tcb_stall`: it keeps every TCB field and every word of `Ω`), `DS.vc0` (a VCPU word below
  offset 32 := 0: no `OS` word by `VcOK.os`, no other VCPU's `RUN_OFFSET` by `VcOK.disj`), `DS.lnk0` (a thread's
  3664 / 3672 word := 0: no `OS` word, `capw_ne_hi`), `DS.regs` (register words, offsets 256–3327), `DS.usr` (the
  run-frame copy into `Ub` words: `VcOK.ubos` / `ubv`), `DS.sts` (`set_thread_state`'s `STATE` and `SCHED_ACTION`
  words).
* **`vcpu.complete_run.ubV`**, **`vcpu.unbind.ubV`**, **`vcpu.detach.ubV`**: QueueUnbindB's `.ub` texts with every
  [P] `VcPl` use replaced by `VcTy` at the step's state (`rcv`: the run VCPU is in `Vc`, so its words are
  `VcWords`; `rbuf`: `VcTy.buf`; `vcb`: the bound VCPU is in `Vc`, `VcObj`), carried by `DS`.
* `K8.finThrRest.blk` (QueueFinThr7's `finThrRest.blk` text over QueueFoot8T's `K8` lemmas: the rest of the thread
  finalisation writes no VCPU-link word), **`fin_thread.ubV`** (`Cur0` and `RunVcpuInv` after, `OSKeep`, `VcTy`),
  **`finJV_thread`**: the finalisation of a thread cap in an `OS` slot, from `JV`, ends in `JV` with QueueFinCap's
  remainder (`Zombie p ZOMBIE_TCB 7` when final, `Null` otherwise), **with a bound VCPU or a run in flight**. Case
  hypotheses (facts of the state the finalisation starts from): the slot holds `Thread p`, and `p` is not the idle
  thread (P3's `FinPl` thread clause without its "no bound VCPU" part, which gen 25 found false).

No [P] `rcw`, no [P] `VcPl`, no new named premise (the hypotheses are `JV`, `OSOK`, `VcOK`, `ScApart` and the case).
Not covered here: the deletion of a **final** thread cap, whose remainder is a Zombie that `finalise_slot_immediate`
writes into the slot and reduces through `delete_deferred` (the Zombie kind). No existing statement changed.
-/
import Fl4ProofsA64.P1.QueueVcTy
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {P3Ok : S → Prop} {U : Set U64}
variable {A : Type _} {ar : machine.Arch A}

namespace K8

/-- QueueFinThr7's `finThrRest.blk` over the `K8` footprint (the text unchanged; inside `K8` its lemma names
resolve to QueueFoot8 / QueueFoot8T's copies). -/
theorem finThrRest.blk (hA : P0.ArchTotal ar) (s1 : S) (a1 : A) (p : U64)
    (h1 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1) (hp : p ∈ T) (hna : L.actionW s1 ≠ p)
    (hidle : L.idleW s1 ≠ p) (rv1 : L.mem s1 (runVcpuA p) = 0#u64) :
    finThrRest st ar s1 a1 p ⦃ r =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ∧ FootD st T Cs Sg Scs Z (EH H) s1 r.2.1 ⦄ := by
  unfold finThrRest
  refine WP.spec_bind (WP.spec_and (notification.unbind_notification.blkF s1 p h1 hp)
    (notification.unbind_notification.rvst s1 p h1 hp)) fun s2 hh2 => ?_
  obtain ⟨⟨h2, f2, n2⟩, r2⟩ := hh2
  refine WP.spec_bind (timer.remove.tf (s0 := s2) s2 p (TF.start h2) hp) fun s3 ⟨h3, f3, n3, k3, _⟩ => ?_
  have rv3 : L.mem s3 (runVcpuA p) = 0#u64 :=
    (k3 p hp 3672#u64 (by simp) (by simp) (Or.inr (by simp))).trans ((r2 p hp).2.trans rv1)
  have ea3 : L.actionW s3 = L.actionW s1 := by rw [n3.1, n2.1]
  have ei3 : L.idleW s3 = L.idleW s1 := by rw [n3.2.1, n2.2.1]
  have f03 : Foot st T Cs Sg Scs Z ∅ s1 s3 := f2.trans f3
  step with obj.Tcb.sc.spec as ⟨i, ei⟩
  step with obj.Sc.is_null.spec as ⟨b, eb⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
      Foot st T Cs Sg Scs Z ∅ s1 r.1 ∧ L.actionW r.1 ≠ p ∧ L.mem r.1 (runVcpuA p) = 0#u64) ?_ ?_
  · split
    · exact (WP.spec_ok _).2 ⟨h3, f03, by rw [ea3]; exact hna, rv3⟩
    rename_i hb
    have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    obtain ⟨hiS, hit, -⟩ := h3.2.2.1.2.2.bound p hp (by rw [← ei]; exact hi0)
    rw [← ei] at hiS hit
    refine WP.spec_bind (schedcontext.unbind_tcb.blkR s3 i h3 hiS hi0 (fun _ => by rw [hit, ea3]; exact hna)
      (fun _ => by rw [hit, ei3]; exact hidle)) fun s5 hh5 => ?_
    obtain ⟨h5, f5, ea5, -, -, -, r5⟩ := hh5
    have rv5 : L.mem s5 (runVcpuA p) = 0#u64 := (r5 p hp).2.trans rv3
    have na5 : L.actionW s5 ≠ p := by
      rcases ea5 with e | e
      · rw [e, ea3]; exact hna
      · rw [e]; exact fun e' => notT_small h5.1.choose_spec.choose_spec.tcbs (by simp) (e' ▸ hp)
    step with obj.Sc.yield_from.val as ⟨y, ey⟩
    step with obj.Tcb.is_null.spec as ⟨b1, eb1⟩
    split
    · exact (WP.spec_ok _).2 ⟨h5, f03.trans f5, na5, rv5⟩
    · have hiS5 : i ∈ Scs := hiS
      have hyy : y ≠ 0#u64 → y ∈ T := fun hy0 => by
        rw [ey]; exact h5.2.2.1.2.2.yt.2.2 i hiS5 (by rw [← ey]; exact hy0)
      refine WP.spec_mono (WP.spec_and (schedcontext.complete_yield_to.blk hA s5 a1 y h5 hyy)
        (schedcontext.complete_yield_to.rvst hA s5 a1 y h5 hyy)) ?_
      rintro ⟨s6, a6⟩ ⟨⟨h6, f6, n6⟩, r6⟩
      exact ⟨h6, (f03.trans f5).trans f6, by rw [n6.1]; exact na5, (r6 p hp).2.trans rv5⟩
  rintro ⟨s4, a2⟩ ⟨h4, f4, na4, rv4⟩
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (sched.suspend.blk s4 a2 p h4 hp na4 rv4) ?_
  rintro ⟨s5, a3⟩ ⟨h5, f5⟩
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (objects.debug_remove.blk s5 p h5 hp) fun s6 ⟨h6, f6⟩ => ?_
  refine WP.spec_bind (hA.fpu_release a3 p) fun a4 _ => ?_
  refine WP.spec_bind (P0.obj.Tcb.slot.p0 p _) fun s7 _ => ?_
  exact (WP.spec_ok _).2 ⟨h6, ((f4.mono (Set.empty_subset _)).trans f5).d.trans (f6.mono (Set.empty_subset _))⟩

end K8

namespace W7
namespace R
namespace ST

local notation "wa" => core.num.U64.wrapping_add

local macro "vno" : tactic => `(tactic| first | omega | (simp; omega) | simp_all | (simp at *; omega))

/-! ## The `VcTy` words kept or zeroed -/

/-- **The `VcTy` words kept or zeroed** (module docstring). -/
structure VKeepZ (st : machine.Store S) [L : LawfulStore st] (T Vc : Set U64) (s s' : S) : Prop where
  ksb : L.ksb s' = L.ksb s
  vc : ∀ b, VcW Vc b → L.mem s' b = L.mem s b ∨ (L.mem s' b = 0#u64 ∧ ∀ v ∈ Vc, b ≠ wa v vcpu.RUN_OFFSET)
  lnk : ∀ t ∈ T, ∀ K : U64, (K.val = 3664 ∨ K.val = 3672) →
    L.mem s' (wa t K) = L.mem s (wa t K) ∨ L.mem s' (wa t K) = 0#u64
  cap : ∀ t ∈ T, obj.Slot.cap st (sbWordA t) s' = obj.Slot.cap st (sbWordA t) s ∨
    obj.Slot.cap st (sbWordA t) s' = ok .Null

theorem VKeepZ.refl {Vc : Set U64} (s : S) : VKeepZ st T Vc s s :=
  ⟨rfl, fun _ _ => Or.inl rfl, fun _ _ _ _ => Or.inl rfl, fun _ _ => Or.inl rfl⟩

theorem VKeepZ.trans {Vc : Set U64} {s1 s2 s3 : S} (h1 : VKeepZ st T Vc s1 s2) (h2 : VKeepZ st T Vc s2 s3) :
    VKeepZ st T Vc s1 s3 := by
  refine ⟨h2.ksb.trans h1.ksb, fun b hb => ?_, fun t ht K hK => ?_, fun t ht => ?_⟩
  · rcases h2.vc b hb with e2 | e2
    · rw [e2]; exact h1.vc b hb
    · exact Or.inr e2
  · rcases h2.lnk t ht K hK with e2 | e2
    · rw [e2]; exact h1.lnk t ht K hK
    · exact Or.inr e2
  · rcases h2.cap t ht with e2 | e2
    · rw [e2]; exact h1.cap t ht
    · exact Or.inr e2

/-- **`VcTy` along a `VKeepZ` step.** -/
theorem VcTy.keepZ {Vc Ub : Set U64} {s s' : S} (h : VcTy st T Cs Ω H Sg Scs Z Vc Ub s)
    (k : VKeepZ st T Vc s s') : VcTy st T Cs Ω H Sg Scs Z Vc Ub s' := by
  refine ⟨fun v hv => ?_, fun t ht => ?_, fun t ht => ?_, fun b hb => (h.usr b hb).ksb k.ksb, fun t ht hne => ?_,
    fun b hb o ho => by rw [k.ksb]; exact h.ks b hb o ho⟩
  · have o := h.obj v hv
    unfold VcObj at o ⊢
    obtain ⟨w, ht, hr⟩ := o
    refine ⟨w, ?_, ?_⟩
    · rcases k.vc _ (vcw_of (o := vcpu.TCB) hv (by simp [vcpu.TCB]) (by simp [vcpu.TCB])) with e | ⟨z, -⟩
      · rw [e]; exact ht
      · rw [z]; exact Or.inl rfl
    · rcases k.vc _ (vcw_of (o := vcpu.RUN_CALLER) hv (by simp [vcpu.RUN_CALLER]) (by simp [vcpu.RUN_CALLER]))
        with e | ⟨z, -⟩
      · rw [e]; exact hr
      · rw [z]; exact Or.inl rfl
  · rcases k.lnk t ht 3664#u64 (Or.inl (by simp)) with e | z
    · rw [e]; exact h.bnd t ht
    · rw [z]; exact Or.inl rfl
  · show L.mem s' (wa t 3672#u64) = 0#u64 ∨ L.mem s' (wa t 3672#u64) ∈ Vc
    rcases k.lnk t ht 3672#u64 (Or.inr (by simp)) with e | z
    · rw [e]; exact h.run t ht
    · rw [z]; exact Or.inl rfl
  · have e : L.mem s' (runVcpuA t) = L.mem s (runVcpuA t) := by
      rcases k.lnk t ht 3672#u64 (Or.inr (by simp)) with e | z
      · exact e
      · exact absurd z hne
    have hne0 : L.mem s (runVcpuA t) ≠ 0#u64 := by rwa [e] at hne
    have hvc : L.mem s (runVcpuA t) ∈ Vc := (h.run t ht).resolve_left hne0
    have ho : L.mem s' (runOffA (L.mem s (runVcpuA t))) = L.mem s (runOffA (L.mem s (runVcpuA t))) := by
      rcases k.vc _ (vcw_of (o := vcpu.RUN_OFFSET) hvc (by simp [vcpu.RUN_OFFSET]) (by simp [vcpu.RUN_OFFSET]))
        with e' | ⟨-, n⟩
      · exact e'
      · exact absurd rfl (n _ hvc)
    rcases k.cap t ht with hc | hc
    · exact RunBuf.of_eq (h.buf t ht hne0) hc e ho
    · intro ptr size rights dev x1 x2 x3 x4 bits sz e1
      rw [hc] at e1
      cases okinj e1

/-! ## The detach frame `DS` -/

/-- **The detach frame**: every `OS` word kept, the `VcTy` words kept or zeroed. -/
abbrev DS (st : machine.Store S) [L : LawfulStore st] (T OS Vc : Set U64) (s s' : S) : Prop :=
  OSKeep st OS s s' ∧ VKeepZ st T Vc s s'

theorem DS.refl {OS Vc : Set U64} (s : S) : DS st T OS Vc s s :=
  ⟨fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, VKeepZ.refl s⟩

theorem DS.trans {OS Vc : Set U64} {s1 s2 s3 : S} (h1 : DS st T OS Vc s1 s2) (h2 : DS st T OS Vc s2 s3) :
    DS st T OS Vc s1 s3 :=
  ⟨fun y hy => ⟨(h2.1 y hy).1.trans (h1.1 y hy).1, (h2.1 y hy).2.1.trans (h1.1 y hy).2.1,
    (h2.1 y hy).2.2.1.trans (h1.1 y hy).2.2.1, (h2.1 y hy).2.2.2.trans (h1.1 y hy).2.2.2⟩, h1.2.trans h2.2⟩

section ds
variable {OS Vc Ub : Set U64} {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}

/-- The buffer slots' caps from `OSKeep`. -/
theorem cap_of_os (hV : VcOK T Scs Z OS Vc Ub) {s s' : S} (k : OSKeep st OS s s') (t : U64) (ht : t ∈ T) :
    obj.Slot.cap st (sbWordA t) s' = obj.Slot.cap st (sbWordA t) s ∨ obj.Slot.cap st (sbWordA t) s' = ok .Null := by
  left
  obtain ⟨e0, e8, -, -⟩ := k _ (hV.bcov t ht)
  rw [DPF.slot_cap_dec, DPF.slot_cap_dec, e0, e8]

/-- **A write set missing every VCPU word and every VCPU-link word**, with `OSKeep`, is a `DS` step. -/
theorem DS.of_w {s s' : S} {F : U64 → Prop} (hV : VcOK T Scs Z OS Vc Ub) (hT : TcbPlaced T)
    (hal : ∀ b, VcW Vc b → Aligned b) (hw : WritesIn st s s' F) (k : OSKeep st OS s s')
    (hvc : ∀ b, VcW Vc b → ¬ F b) (hl : ∀ t ∈ T, ∀ K : U64, (K.val = 3664 ∨ K.val = 3672) → ¬ F (wa t K)) :
    DS st T OS Vc s s' :=
  ⟨k, hw.1, fun b hb => Or.inl (hw.mem_eq (hal b hb) (hvc b hb)),
    fun t ht K hK => Or.inl (hw.mem_eq (field_aligned (hT t ht) (by omega) (by omega)) (hl t ht K hK)),
    cap_of_os hV k⟩

/-- A `W7.CapW` word kept by a step that keeps every TCB field and every word of `Ω`. -/
theorem capw_kept {s s' : S} (q : SchedQueuesInvX st T Cs Ω H X s Q R)
    (kT : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem s' (wa y K) = L.mem s (wa y K)) (kΩ : ∀ a ∈ Ω, L.mem s' a = L.mem s a) {b : U64}
    (hb : W7.CapW T Ω Sg b) (hal : Aligned b) : L.mem s' b = L.mem s b := by
  rcases hb with ⟨t, ht, K, hK, rfl⟩ | ⟨hΩ, -⟩
  · have h1 := field_val (q.tcbs t ht) (by omega : K.val < 4096)
    have a2 := tcb4096 (q.tcbs t ht)
    unfold Aligned at hal
    rw [h1] at hal
    exact kT t ht K (by omega) (by omega)
  · exact kΩ _ hΩ

/-- **The stall's frame** (every TCB field and every word of `Ω` kept) is a `DS` step. -/
theorem DS.of_fr (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {s s' : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q R) (hW : ∀ v ∈ Vc, VcWords Ω Sg v) (hk : L.ksb s' = L.ksb s)
    (kT : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem s' (wa y K) = L.mem s (wa y K)) (kΩ : ∀ a ∈ Ω, L.mem s' a = L.mem s a) :
    DS st T OS Vc s s' := by
  have k : OSKeep st OS s s' := fun y hy =>
    ⟨by have := capw_kept q kT kΩ (hO.cw0 hy) (hO.al0 hy); exact this,
     capw_kept q kT kΩ (hO.cw hy (k := 8#u64) (by simp) (by simp)) (hO.al hy (by simp) (by simp)),
     capw_kept q kT kΩ (hO.cw hy (k := 16#u64) (by simp) (by simp)) (hO.al hy (by simp) (by simp)),
     capw_kept q kT kΩ (hO.cw hy (k := 24#u64) (by simp) (by simp)) (hO.al hy (by simp) (by simp))⟩
  refine ⟨k, hk, fun b hb => ?_, fun t ht K hK => Or.inl (kT t ht K (by omega) (by omega)), cap_of_os hV k⟩
  obtain ⟨v, hv, o, ho, h8, rfl⟩ := hb
  exact Or.inl (kΩ _ (hW v hv o ho h8).2.1)

theorem wvv {x k : U64} (h : x.val + k.val < 2 ^ 64) : (wa x k).val = x.val + k.val := by
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega

/-- **A VCPU word below offset 32 := 0** is a `DS` step. -/
theorem DS.vc0 (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q R) (hW : ∀ v ∈ Vc, VcWords Ω Sg v) {v o : U64} (hv : v ∈ Vc)
    (ho : o.val < 32) (h8 : o.val % 8 = 0) : DS st T OS Vc s (L.wr s (wa v o) 0#u64) := by
  have hw := hW v hv o (by omega) h8
  have hvo : VcW Vc (wa v o) := vcw_of hv (by omega) h8
  have hal : ∀ b, VcW Vc b → Aligned b := fun b ⟨v', hv', o', h1, h2, e⟩ => e ▸ (hW v' hv' o' h1 h2).1
  have hfit := hV.fit v hv
  have k : OSKeep st OS s (L.wr s (wa v o) 0#u64) :=
    OSKeep.wr1 hO hw.1 fun y hy hin => hV.os _ hvo ⟨y, hy, hin⟩
  refine ⟨k, L.ksb_wr _ _ _, fun b hb => ?_, fun t ht K hK => Or.inl ?_, cap_of_os hV k⟩
  · by_cases e : wa v o = b
    · subst e
      refine Or.inr ⟨L.mem_wr_same hw.1, fun v' hv' e' => ?_⟩
      have h1 : (wa v o).val = v.val + o.val := wvv (by omega)
      have hfit' := hV.fit v' hv'
      have h2 : (wa v' vcpu.RUN_OFFSET).val = v'.val + 32 := by
        rw [wvv (by simp [vcpu.RUN_OFFSET]; omega)]; simp [vcpu.RUN_OFFSET]
      have hvv := congrArg UScalar.val e'
      rw [h1, h2] at hvv
      by_cases ev : v = v'
      · subst ev; omega
      · rcases hV.disj v hv v' hv' ev with h3 | h3 <;> omega
    · exact Or.inl (L.mem_wr_ne hw.1 (hal b hb) (fun e' => e (UScalar.eq_of_val_eq e')))
  · exact L.mem_wr_ne hw.1 (field_aligned (q.tcbs t ht) (by omega) (by omega))
      (fun e => out_ne_field (q.omega _ hw.2.1) ht (q.tcbs t ht) (by omega) e.symm)

/-- **A thread's VCPU-link word (3664 or 3672) := 0** is a `DS` step. -/
theorem DS.lnk0 (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q R) (hW : ∀ v ∈ Vc, VcWords Ω Sg v) {t K : U64} (ht : t ∈ T)
    (hK : K.val = 3664 ∨ K.val = 3672) : DS st T OS Vc s (L.wr s (wa t K) 0#u64) := by
  have hta := q.tcbs t ht
  have ha : Aligned (wa t K) := field_aligned hta (by omega) (by omega)
  have hal : ∀ b, VcW Vc b → Aligned b := fun b ⟨v', hv', o', h1, h2, e⟩ => e ▸ (hW v' hv' o' h1 h2).1
  have k : OSKeep st OS s (L.wr s (wa t K) 0#u64) :=
    OSKeep.of_writes hO (writesIn_wr ha) fun b hb e => capw_ne_hi q hb ht (by omega) (by omega) e
  refine ⟨k, L.ksb_wr _ _ _, fun b hb => Or.inl ?_, fun t' ht' K' hK' => ?_, cap_of_os hV k⟩
  · obtain ⟨v, hv, o, ho, h8, rfl⟩ := hb
    exact L.mem_wr_ne ha (hal _ ⟨v, hv, o, ho, h8, rfl⟩)
      (fun e => out_ne_field (q.omega _ (hW v hv o ho h8).2.1) ht hta (by omega) e)
  · by_cases e : t' = t ∧ K'.val = K.val
    · obtain ⟨rfl, e2⟩ := e
      have : K' = K := UScalar.eq_of_val_eq e2
      subst this
      exact Or.inr (L.mem_wr_same ha)
    · refine Or.inl (L.mem_wr_ne ha (field_aligned (q.tcbs t' ht') (by omega) (by omega)) fun ev => ?_)
      refine field_ne hta (q.tcbs t' ht') (by omega) (by omega) (fun et => ?_) (UScalar.eq_of_val_eq ev)
      intro e3; exact e ⟨et.symm, e3.symm⟩

/-- **Register writes of a thread** are a `DS` step. -/
theorem DS.regs (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {s s' : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q R) (hW : ∀ v ∈ Vc, VcWords Ω Sg v) {y : U64} (hy : y ∈ T)
    (hw : WritesIn st s s' (RegW y)) : DS st T OS Vc s s' := by
  have hal : ∀ b, VcW Vc b → Aligned b := fun b ⟨v', hv', o', h1, h2, e⟩ => e ▸ (hW v' hv' o' h1 h2).1
  have k : OSKeep st OS s s' :=
    OSKeep.of_writes hO hw fun b hb ⟨K, k1, k2, _, e⟩ => capw_ne_hi q hb hy (by omega) (by omega) e
  refine DS.of_w hV q.tcbs hal hw k (fun b hb ⟨K, _, k2, _, e⟩ => ?_) (fun t ht K' hK' ⟨K, _, k2, _, e⟩ => ?_)
  · obtain ⟨v, hv, o, ho, h8, rfl⟩ := hb
    exact out_ne_field (K := K) (q.omega _ (hW v hv o ho h8).2.1) hy (q.tcbs y hy) (by omega) (by rw [e])
  · exact field_ne (q.tcbs t ht) (q.tcbs y hy) (by omega) (by omega)
      (fun _ => by rcases hK' with h | h <;> omega) e

/-- **The run-frame copy into `Ub` words** is a `DS` step. -/
theorem DS.usr (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {s s' : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q R) (hW : ∀ v ∈ Vc, VcWords Ω Sg v)
    (hU : ∀ b ∈ Ub, UsrW st T Cs H Sg Scs Z s b) (hw : WritesIn st s s' (· ∈ Ub)) : DS st T OS Vc s s' := by
  have hal : ∀ b, VcW Vc b → Aligned b := fun b ⟨v', hv', o', h1, h2, e⟩ => e ▸ (hW v' hv' o' h1 h2).1
  have k : OSKeep st OS s s' := OSKeep.of_in hO hw fun x hx b _ h1 h2 hbU => hV.ubos b hbU ⟨x, hx, h1, h2⟩
  refine DS.of_w hV q.tcbs hal hw k (fun b hb hbU => hV.ubv b hbU hb) (fun t ht K hK hbU => ?_)
  exact out_ne_field (hU _ hbU).out ht (q.tcbs t ht) (by omega) rfl

/-- **`set_thread_state`'s words** (`STATE`, the current core's `SCHED_ACTION`) are a `DS` step. -/
theorem DS.sts (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {s s' : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q R) (hW : ∀ v ∈ Vc, VcWords Ω Sg v) {t : U64} (ht : t ∈ T)
    (hw : WritesIn st s s' (fun b => b = stA t ∨ b = L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION)) :
    DS st T OS Vc s s' := by
  have hal : ∀ b, VcW Vc b → Aligned b := fun b ⟨v', hv', o', h1, h2, e⟩ => e ▸ (hW v' hv' o' h1 h2).1
  have k : OSKeep st OS s s' := OSKeep.of_writes hO hw fun b hb hF => by
    rcases hF with e | e
    · rw [stA_eq] at e
      exact capw_ne_hi q hb ht (K := 3328#u64) (by simp) (by simp) e
    · exact capw_ne_node q hb q.cur (by rw [act_val]; omega) e
  refine DS.of_w hV q.tcbs hal hw k (fun b hb hF => ?_) (fun t' ht' K hK hF => ?_)
  · obtain ⟨v, hv, o, ho, h8, rfl⟩ := hb
    have hO' := q.omega _ (hW v hv o ho h8).2.1
    rcases hF with e | e
    · exact out_ne_field hO' ht (q.tcbs t ht) (K := 3328#u64) (by simp) (by rw [e, stA_eq])
    · exact out_ne_node hO' q.cur (q.nodes _ q.cur) (by rw [act_val]; omega) (by rw [e])
  · rcases hF with e | e
    · rw [stA_eq] at e
      exact field_ne (q.tcbs t' ht') (q.tcbs t ht) (by omega) (by simp)
        (fun _ => by rcases hK with h | h <;> simp [h]) e
    · exact node_ne_field (q.nodes _ q.cur) (by rw [act_val]; omega) ht' (q.tcbs t' ht') (by omega) e.symm

end ds

/-- A `Cur0` state's queue invariant. -/
theorem Cur0.q {s0 s : S} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) :
    ∃ X Q R, SchedQueuesInvX st T Cs Ω H X s Q R := by
  obtain ⟨Ac', hb⟩ := h.bxi
  exact ⟨_, _, _, hb.1.choose_spec.choose_spec⟩

/-- **The stall's `DS` frame.** -/
theorem smp.remote_tcb_stall.ds (hA : P0.ArchTotal ar) {OS Vc Ub : Set U64} (hO : OSOK T Ω Sg OS)
    (hV : VcOK T Scs Z OS Vc Ub) (hW : ∀ v ∈ Vc, VcWords Ω Sg v) {s0 s : S}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (a : A) (y : U64) :
    smp.remote_tcb_stall st ar s a y ⦃ s' _ => DS st T OS Vc s s' ⦄ := by
  obtain ⟨Ac1, hb1⟩ := h.bxi
  have hb := hb1.blk
  obtain ⟨⟨Q0, R0, hq0⟩, hb0, hx0, hs0, hg0⟩ := hb1.blk
  refine WP.spec_mono (WP.spec_and (smp.remote_tcb_stall.blk hA s a y hb)
    (smp.remote_tcb_stall.all hA s a y hq0 hb0 hx0 hs0 hg0)) ?_
  rintro ⟨s1, a1⟩ ⟨⟨-, f1, -⟩, _, _, _, _, _, _, _, _, _, keep, kΩ⟩
  exact DS.of_fr hO hV hq0 hW f1.1 keep kΩ

/-! ## `vcpu::detach` from `VcTy` -/

section walk
variable {OS Vc Ub : Set U64}

set_option maxHeartbeats 4000000 in
/-- **`complete_run` of any thread in `TS_RUNNING_VM`, from `VcTy`** (QueueUnbindB's `complete_run.ub` with its
`hrc` / `hbuf` from `VcTy`), with the `DS` frame. -/
theorem vcpu.complete_run.ubV (hA : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub)
    {s0 s : S} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s) (a : A)
    (y stop m1 m2 m3 : U64) (hy : y ∈ T) (hvm : L.mem s (stA y) = sched.TS_RUNNING_VM) :
    vcpu.complete_run st ar s a y stop m1 m2 m3 ⦃ s' _ => UbF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s s' ∧
      BndK st T s s' ∧ DS st T OS Vc s s' ⦄ := by
  obtain ⟨Ac1, hb1⟩ := h.bxi
  have q := hb1.1.choose_spec.choose_spec
  have hT := q.tcbs
  have hta := hT y hy
  have hW : ∀ v ∈ Vc, VcWords Ω Sg v := fun v hv' => (hv.obj v hv').1
  have hU := hv.usr
  have hal : ∀ b ∈ Ub, Aligned b := fun b hb => (hU b hb).out.1
  unfold vcpu.complete_run
  rw [eq_of_spec_fd P0.Consts.layout.tcb.RUN_VCPU.spec]
  simp only [lift, bind_ok, L.read_eq, L.write_eq]
  by_cases hv0 : L.mem s (core.num.U64.wrapping_add y 3672#u64) = 0#u64
  · rw [if_pos hv0]; exact (WP.spec_ok _).2 ⟨UbF.refl h, BndK.refl s, DS.refl s⟩
  rw [if_neg hv0]
  have hvc : L.mem s (wa y 3672#u64) ∈ Vc := (hv.run y hy).resolve_left hv0
  have hbuf : RunBuf st Ub s y := hv.buf y hy hv0
  refine WP.spec_bind (hA.vcpu_flush_state _ _ _) fun a1 _ => ?_
  refine WP.spec_bind (Pₘ := fun s2 => WritesIn st s s2 (· ∈ Ub)) ?_ fun s2 w2 => ?_
  · split
    · have hs : obj.Tcb.slot y layout.tcb.SLOT_BUFFER = ok (sbWordA y) := by
        simp [obj.Tcb.slot, lift, sbWordA]
      rw [hs, bind_ok]
      refine WP.spec_bind (spec_eq' (P0.obj.Slot.cap.p0 st (sbWordA y) s L.total)) fun c hc0 => ?_
      obtain ⟨hc, -⟩ := hc0
      cases c
      all_goals try exact (WP.spec_ok _).2 (WritesIn.refl _ _)
      rename_i ptr size rights dev c1 c2 c3 c4
      refine WP.spec_bind (spec_eq' (P0.capability.FrameSize.bits.p0 size)) fun bits ⟨hbits, _⟩ => ?_
      have h63 : (bits &&& 63#u64).val < 64 := by
        rw [UScalar.val_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by simp)
      refine WP.spec_bind (spec_eq' (P0.one_shift_positive _ h63)) fun sz ⟨hsz, _⟩ => ?_
      by_cases hd : dev = true
      · rw [if_pos hd]; exact (WP.spec_ok _).2 (WritesIn.refl _ _)
      rw [if_neg hd]
      split
      · rename_i hrw
        split
        · rename_i ho
          split
          · rename_i hlt
            have hlt' : (L.mem s (core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add y 3672#u64))
                vcpu.RUN_OFFSET)).val < sz.val := hlt
            step as ⟨i7, hi7⟩
            split
            · rename_i hge
              have hge' : 1024 ≤ i7.val := by scalar_tac
              have hF := hbuf ptr size rights dev c1 c2 c3 c4 bits sz hc (by simpa using hd) hrw hbits hsz
                ho hlt' (by unfold runOffA runVcpuA; omega)
              exact vcpu.read_state_to_frame.fw hA s a1 _ _ _ hF hal
            · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
          · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
        · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
      · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
    · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  obtain ⟨F2, B2, S2⟩ := UbF.usr h hU w2
  have D2 := DS.usr hO hV q hW hU w2
  have hw : VcWords Ω Sg (L.mem s (core.num.U64.wrapping_add y 3672#u64)) := hW _ hvc
  have hx := hw vcpu.RUN_CALLER (by simp [vcpu.RUN_CALLER]) (by simp [vcpu.RUN_CALLER])
  obtain ⟨F3, B3, S3⟩ := UbF.omega (v := 0#u64) F2.cur hx.1 hx.2.1 hx.2.2
  obtain ⟨_, _, _, q2⟩ := Cur0.q F2.cur
  have D3 := DS.vc0 (o := vcpu.RUN_CALLER) hO hV q2 hW hvc (by simp [vcpu.RUN_CALLER]) (by simp [vcpu.RUN_CALLER])
  obtain ⟨F4, B4, S4, rv4⟩ := UbF.rv0w F3.cur hy
  obtain ⟨_, _, _, q3⟩ := Cur0.q F3.cur
  have D4 := DS.lnk0 (K := 3672#u64) hO hV q3 hW hy (Or.inr (by simp))
  refine vck_regs _ y stop m1 m2 m3 hta fun s10 w10 => ?_
  obtain ⟨F10, B10, S10⟩ := UbF.regs F4.cur hy w10
  obtain ⟨_, _, _, q4⟩ := Cur0.q F4.cur
  have D10 := DS.regs hO hV q4 hW hy w10
  have F := ((F2.trans F3).trans F4).trans F10
  have B := ((B2.trans B3).trans B4).trans B10
  have D := D2.trans (D3.trans (D4.trans D10))
  have st10 : L.mem s10 (stA y) = sched.TS_RUNNING_VM := by
    rw [(((S2.trans S3).trans S4).trans S10) y hy]; exact hvm
  obtain ⟨_, _, _, q10⟩ := Cur0.q F.cur
  refine WP.spec_bind (WP.spec_and (sched.set_thread_state.running_ub F.cur hy st10 (F10.rv0 y hy rv4))
    (sts_fine s10 y sched.TS_RUNNING (q10.nodes _ q10.cur) (q10.tcbs y hy))) fun s11 ⟨⟨F11, B11⟩, w11⟩ =>
    vck_vm_tail hA s11 a1 y ⟨F.trans F11, B.trans B11, D.trans (DS.sts hO hV q10 hW hy w11)⟩

set_option maxHeartbeats 4000000 in
/-- **`vcpu::unbind` of a VCPU of `Vc`, from `VcTy`** (QueueUnbindB's `unbind.ub` with every [P] `VcPl` use
replaced by `VcTy` at the step's state), with the `DS` frame. -/
theorem vcpu.unbind.ubV (hA : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s) (a : A) (v : U64)
    (hvV : v ∈ Vc) :
    vcpu.unbind st ar s a v ⦃ s' _ => UbF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s s' ∧ DS st T OS Vc s s' ⦄ := by
  have hW : ∀ v ∈ Vc, VcWords Ω Sg v := fun v hv' => (hv.obj v hv').1
  have V0 := hv.obj v hvV
  unfold vcpu.unbind vcpu.set_bound
  rw [eq_of_spec_fd P0.Consts.layout.tcb.RUN_VCPU.spec, eq_of_spec_fd P0.Consts.layout.tcb.VCPU.spec]
  simp only [lift, bind_ok, L.read_eq, L.write_eq]
  refine WP.spec_bind (Pₘ := fun r : S × A => UbF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s r.1 ∧ BndK st T s r.1 ∧
    DS st T OS Vc s r.1) ?_ ?_
  · split
    · rename_i hne
      have hc0 : L.mem s (core.num.U64.wrapping_add v vcpu.RUN_CALLER) ≠ 0#u64 := by simpa using hne
      have hcT := V0.2.2.resolve_left hc0
      refine WP.spec_bind (WP.spec_and (smp.remote_tcb_stall.ub hA h a _)
        (smp.remote_tcb_stall.ds hA hO hV hW h a _)) ?_
      rintro ⟨s2, a2⟩ ⟨⟨F2, B2, -⟩, D2⟩
      try simp only [uncurry_apply_pair, WP.uncurry'_pair]
      step with obj.Tcb.state.spec as ⟨i1, ei1⟩
      split
      · rename_i hvm
        refine WP.spec_mono (vcpu.complete_run.ubV hA hO hV F2.cur (hv.keepZ D2.2) a2 _ _ _ _ _ hcT
          (by rw [← ei1]; exact hvm)) ?_
        rintro ⟨s3, a3⟩ ⟨F3, B3, D3⟩
        exact ⟨F2.trans F3, B2.trans B3, D2.trans D3⟩
      · have hx := V0.1 vcpu.RUN_CALLER (by simp [vcpu.RUN_CALLER]) (by simp [vcpu.RUN_CALLER])
        obtain ⟨F3, B3, -⟩ := UbF.omega (v := 0#u64) F2.cur hx.1 hx.2.1 hx.2.2
        obtain ⟨_, _, _, q2⟩ := Cur0.q F2.cur
        have D3 := DS.vc0 (o := vcpu.RUN_CALLER) hO hV q2 hW hvV (by simp [vcpu.RUN_CALLER])
          (by simp [vcpu.RUN_CALLER])
        obtain ⟨F4, B4, -, -⟩ := UbF.rv0w F3.cur hcT
        obtain ⟨_, _, _, q3⟩ := Cur0.q F3.cur
        have D4 := DS.lnk0 (K := 3672#u64) hO hV q3 hW hcT (Or.inr (by simp))
        exact (WP.spec_ok _).2 ⟨(F2.trans F3).trans F4, (B2.trans B3).trans B4, D2.trans (D3.trans D4)⟩
    · exact (WP.spec_ok _).2 ⟨UbF.refl h, BndK.refl s, DS.refl s⟩
  rintro ⟨s1, a1⟩ ⟨F1, B1, D1⟩
  try simp only [uncurry_apply_pair, WP.uncurry'_pair]
  have V1 := (hv.keepZ D1.2).obj v hvV
  split
  · exact (WP.spec_ok _).2 ⟨F1, D1⟩
  rename_i ht0
  have htT := V1.2.1.resolve_left ht0
  refine WP.spec_bind (WP.spec_and (smp.remote_tcb_stall.ub hA F1.cur a1 _)
    (smp.remote_tcb_stall.ds hA hO hV hW F1.cur a1 _)) ?_
  rintro ⟨s2, a2⟩ ⟨⟨F2, -, -⟩, D2⟩
  try simp only [uncurry_apply_pair, WP.uncurry'_pair]
  refine WP.spec_bind (hA.vcpu_flush a2 v) fun a3 _ => ?_
  have hx0 := V1.1 vcpu.TCB (by simp [vcpu.TCB]) (by simp [vcpu.TCB])
  have hx8 := V1.1 vcpu.OWNER_CPU (by simp [vcpu.OWNER_CPU]) (by simp [vcpu.OWNER_CPU])
  obtain ⟨F3, -, -⟩ := UbF.omega (v := 0#u64) F2.cur hx0.1 hx0.2.1 hx0.2.2
  obtain ⟨_, _, _, q2⟩ := Cur0.q F2.cur
  have D3 := DS.vc0 (o := vcpu.TCB) hO hV q2 hW hvV (by simp [vcpu.TCB]) (by simp [vcpu.TCB])
  obtain ⟨F4, -, -⟩ := UbF.omega (v := 0#u64) F3.cur hx8.1 hx8.2.1 hx8.2.2
  obtain ⟨_, _, _, q3⟩ := Cur0.q F3.cur
  have D4 := DS.vc0 (o := vcpu.OWNER_CPU) hO hV q3 hW hvV (by simp [vcpu.OWNER_CPU]) (by simp [vcpu.OWNER_CPU])
  obtain ⟨F5, -⟩ := UbF.bnd0 (v := 0#u64) F4.cur htT
  obtain ⟨_, _, _, q4⟩ := Cur0.q F4.cur
  have D5 := DS.lnk0 (K := 3664#u64) hO hV q4 hW htT (Or.inl (by simp))
  obtain ⟨Ac5, hb5⟩ := F5.cur.bxi
  have hT5 := hb5.1.choose_spec.choose_spec.tcbs
  refine WP.spec_bind (P0.obj.Tcb.reg.p0 st _ _ _ L.total) fun old _ => ?_
  refine WP.spec_bind (P0.regs.sanitise.p0 _ _) fun i4 _ => ?_
  refine WP.spec_bind (obj.Tcb.set_reg.regW _ (hT5 _ htT) (by simp [layout.reg.SPSR_EL1]) (WritesIn.refl _ _))
    fun s6 w6 => ?_
  obtain ⟨F6, -, -⟩ := UbF.regs F5.cur htT w6
  have D6 := DS.regs hO hV hb5.1.choose_spec.choose_spec hW htT w6
  exact vck_vm_tail hA s6 a3 _ ⟨(((((F1.trans F2).trans F3).trans F4).trans F5).trans F6),
    D1.trans (D2.trans (D3.trans (D4.trans (D5.trans D6))))⟩

set_option maxHeartbeats 2000000 in
/-- **`vcpu::detach` of any thread, from `VcTy`** (QueueUnbindB's `detach.ub` with [P] `VcPl` replaced): ends
with `RUN_VCPU p = 0`, with the `DS` frame. -/
theorem vcpu.detach.ubV (hA : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s) (a : A) (p : U64)
    (hp : p ∈ T) :
    vcpu.detach st ar s a p ⦃ s' _ => UbF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s s' ∧
      L.mem s' (runVcpuA p) = 0#u64 ∧ DS st T OS Vc s s' ⦄ := by
  have hW : ∀ v ∈ Vc, VcWords Ω Sg v := fun v hv' => (hv.obj v hv').1
  obtain ⟨_, _, _, q⟩ := Cur0.q h
  unfold vcpu.detach
  refine WP.spec_bind (Pₘ := fun r : S × A => UbF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s r.1 ∧ BndK st T s r.1 ∧
    L.mem r.1 (runVcpuA p) = 0#u64 ∧ DS st T OS Vc s r.1) ?_ ?_
  · unfold vcpu.cancel_run
    rw [eq_of_spec_fd P0.Consts.layout.tcb.RUN_VCPU.spec]
    simp only [lift, bind_ok, L.read_eq, L.write_eq]
    split
    · rename_i hne
      have hv' : L.mem s (runVcpuA p) ≠ 0#u64 := by simpa [runVcpuA] using hne
      have hvc : L.mem s (runVcpuA p) ∈ Vc := (hv.run p hp).resolve_left hv'
      have hx := hW _ hvc vcpu.RUN_CALLER (by simp [vcpu.RUN_CALLER]) (by simp [vcpu.RUN_CALLER])
      obtain ⟨F1, B1, -⟩ := UbF.omega (v := 0#u64) h hx.1 hx.2.1 hx.2.2
      have D1 := DS.vc0 (o := vcpu.RUN_CALLER) hO hV q hW hvc (by simp [vcpu.RUN_CALLER])
        (by simp [vcpu.RUN_CALLER])
      obtain ⟨F2, B2, -, e2⟩ := UbF.rv0w F1.cur hp
      obtain ⟨_, _, _, q1⟩ := Cur0.q F1.cur
      have D2 := DS.lnk0 (K := 3672#u64) hO hV q1 hW hp (Or.inr (by simp))
      exact (WP.spec_ok _).2 ⟨F1.trans F2, B1.trans B2, e2, D1.trans D2⟩
    · rename_i heq
      exact (WP.spec_ok _).2 ⟨UbF.refl h, BndK.refl s, UScalar.eq_of_val_eq (by simpa [runVcpuA] using heq),
        DS.refl s⟩
  rintro ⟨s1, a1⟩ ⟨F1, B1, rv1, D1⟩
  try simp only [WP.uncurry'_pair, uncurry_apply_pair]
  have hv1 := hv.keepZ D1.2
  step with vcpu.bound.spec as ⟨v, ev⟩
  split
  · rename_i hne
    have hv0 : v ≠ 0#u64 := by simpa using hne
    have hvV : v ∈ Vc := by
      rcases hv1.bnd p hp with e | e
      · exact absurd (ev.trans e) hv0
      · rw [ev]; exact e
    refine WP.spec_mono (vcpu.unbind.ubV hA hO hV F1.cur hv1 a1 v hvV) ?_
    rintro ⟨s2, a2⟩ ⟨F2, D2⟩
    exact ⟨F1.trans F2, F2.rv0 p hp rv1, D1.trans D2⟩
  · exact (WP.spec_ok _).2 ⟨F1, rv1, D1⟩

/-- A `K8.FootD` footprint is a `K7.FootD` one. -/
theorem K8.FootD.to7 {Es : Set U64} {s s' : S} (f : K8.FootD st T Cs Sg Scs Z Es s s') :
    K7.FootD st T Cs Sg Scs Z Es s s' :=
  WritesIn.mono f fun _ hb => hb.imp K8.KW.to7 id

set_option maxHeartbeats 2000000 in
/-- **The thread kind's `finalise_cap_object`, a bound VCPU or a run in flight, from `VcTy`**: `Cur0` and
`RunVcpuInv` after (QueueUnbindB's `fin_thread.ubR` with [P] `VcPl` replaced), every `OS` word kept, `VcTy`. -/
theorem fin_thread.ubV (hA : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub)
    (hSA : ScApart Scs Z OS) {s0 s : S} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hRV : RunVcpuInv st T s)
    (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s) (a : A) (p : U64) (fin : Bool) (hp : p ∈ T)
    (hid : p ≠ L.idleW s) :
    objects.finalise_cap_object st ar s a (.Thread p) fin ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧
      RunVcpuInv st T r.2.1 ∧ OSKeep st OS s r.2.1 ∧ VcTy st T Cs Ω H Sg Scs Z Vc Ub r.2.1 ⦄ := by
  have hW : ∀ v ∈ Vc, VcWords Ω Sg v := fun v hv' => (hv.obj v hv').1
  cases fin
  · unfold objects.finalise_cap_object
    dsimp only
    split
    · rename_i hf; exact absurd hf (by simp)
    · exact (WP.spec_ok _).2 ⟨h, hRV, (DS.refl (st := st) (T := T) (Vc := Vc) s).1, hv⟩
  rw [fin_thread_split]
  refine WP.spec_bind (WP.spec_and (smp.remote_tcb_stall.ub hA h a p) (smp.remote_tcb_stall.ds hA hO hV hW h a p)) ?_
  rintro ⟨s1, a1⟩ ⟨⟨F1, -, -⟩, D1⟩
  try simp only [WP.uncurry'_pair, uncurry_apply_pair]
  refine WP.spec_bind (vcpu.detach.ubV hA hO hV F1.cur (hv.keepZ D1.2) a1 p hp) ?_
  rintro ⟨s2, a2⟩ ⟨F2, rv2, D2⟩
  try simp only [WP.uncurry'_pair, uncurry_apply_pair]
  have F12 := F1.trans F2
  have D12 := D1.trans D2
  have hv2 := hv.keepZ D12.2
  obtain ⟨Ac2, hb2⟩ := F12.cur.bxi
  have q2 := hb2.1.choose_spec.choose_spec
  obtain ⟨-, -, hX2, -, hSg2⟩ := hb2.blk
  have hna : L.actionW s2 ≠ p := F12.cur.na p hp
  have hidle : L.idleW s2 ≠ p := by rw [F12.idle]; exact Ne.symm hid
  have hct : L.curW s2 ∈ T := q2.curT
  refine WP.spec_mono (WP.spec_and (WP.spec_and (WP.spec_and (finThrRest.blk hA s2 a2 p hb2.blk hp hna hidle rv2)
    (finThrRest.curR hA s2 a2 p (L.curW s2) hb2.blk hp hna hidle hct rv2))
    (finThrRest.rvi hA s2 a2 p hb2.blk hp hna hidle rv2 (F12.rvi hRV)))
    (K8.finThrRest.blk hA s2 a2 p hb2.blk hp hna hidle rv2)) ?_
  rintro ⟨r1, s3, a3⟩ ⟨⟨⟨⟨h3, f3⟩, ec, ecs, esc, ea, enb⟩, r3⟩, -, f8⟩
  have k3 : OSKeep st OS s2 s3 := OSKeep.of_kwd7 hO q2 hSg2.sub hSA (fun e he => he) (K8.FootD.to7 f8)
  refine ⟨Cur0.mk F12.cur (BlkOK.bxi h3) ec ecs esc ea (Or.inr (enb F12.cur.nb)) (FootD.cur0w f3 le_rfl), r3,
    fun y hy => ⟨(k3 y hy).1.trans (D12.1 y hy).1, (k3 y hy).2.1.trans (D12.1 y hy).2.1,
      (k3 y hy).2.2.1.trans (D12.1 y hy).2.2.1, (k3 y hy).2.2.2.trans (D12.1 y hy).2.2.2⟩, hv2.keep (VKeep.of_kwd8 hO hV hSA q2 hX2.1 hSg2.sub (fun e he => he) hv2 f8)⟩

end walk

/-! ## The thread kind over `JV` -/

set_option maxHeartbeats 2000000 in
/-- **The finalisation of a thread cap of an `OS` slot, any finality, a bound VCPU or a run in flight, keeps
`JV`**, with QueueFinCap's remainder (`Zombie p ZOMBIE_TCB 7` when final, `Null` otherwise); no [P] `rcw` /
`VcPl`. Case hypothesis: the slot's cap is `Thread p` with `p` not the idle thread. -/
theorem finJV_thread {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {OS Vc Ub : Set U64}
    (hO : OSOK T Ω Sg OS) (hSA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S} {x p : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS)
    (hc : obj.Slot.cap st x s = ok (.Thread p)) (hid : p ≠ L.idleW s) (a : A) (fin : Bool) :
    objects.finalise_cap st ar s a (.Thread p) fin false ⦃ r =>
      r.1 = (if fin then .Zombie p capability.ZOMBIE_TCB 7#u64 else .Null, .Null) ∧
      JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ := by
  have hty := (h.1.2 x hx).1 _ (by rw [DPF.slot_cap_dec] at hc; exact hc)
  have hp : p ∈ T := hty.1.2.2.2.2.2 p rfl
  rw [fin_cap_eq_obj (by simp)]
  refine WP.spec_mono (WP.spec_and (fin_thread.rem hA s a p fin)
    (fin_thread.ubV hA hO hV hSA h.1.1.1 h.1.1.2 h.2 a p fin hp hid)) ?_
  rintro r ⟨e, c0, rv, k, v⟩
  exact ⟨e, And.intro (And.intro (And.intro c0 rv) (h.1.2.keep k)) v⟩

end ST
end R
end W7

end

end Fl4ProofsA64.P1
