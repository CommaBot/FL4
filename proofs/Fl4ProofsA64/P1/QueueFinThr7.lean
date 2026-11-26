/-
P1 (aarch64): **the thread kind's finalisation on AArch64** (closes `FinGapsAt.thread` in the W7 forms), and
the W7 finalisation kinds.

QueueFinThr left the thread kind a named gap (`FinGapsAt.thread`) for two reasons, both handled here:
1. *A thread in an `ARMVCPURun`* (`TS_RUNNING_VM`, `RUN_VCPU ≠ 0`, possibly on another core) can be finalised;
   `objects::finalise_cap_object`'s `vcpu::detach` then starts with a non-idle `vcpu::cancel_run`
   (crates/fl4-core/src/arch/aarch64/vcpu.rs: `RUN_CALLER(v) := 0`, `RUN_VCPU(t) := 0`). New frame
   **`vcpu.cancel_run.w7`** / **`vcpu.detach.w7`**: with the run VCPU's `RUN_CALLER` word a user word (`UserW`,
   the [P] `W7.DelPlaceAt.rcw` field) the two writes keep `BlkOK` (`bufw_xfer`, `rv_all`), write only that user
   word and the TCB's `RUN_VCPU` word, keep action / idle / current thread / current SC and every TCB field from
   3328 except `RUN_VCPU t`, and end with `RUN_VCPU t = 0`. The rest of the finalisation (`finThrRest`, the
   extraction's text after `detach`, `fin_thread_split`) is then QueueFinal's / QueueFinThr's proof text from a
   state with `RUN_VCPU t = 0` (`finThrRest.blk`, `finThrRest.curR`). So `fin_thread.blk7` / `fin_thread.curR7`
   need no `hrv0` (x86-shaped `fin_thread.blk` / `.curR` keep theirs, unchanged).
2. *The 7-slot Zombie remainder* (`.Zombie p ZOMBIE_TCB 7`): typed in the W7 sense (`W7.tcb_zombieOK`, slot words
   below 224, QueueSlots7).

`W7.finGap_thread` is the thread kind's `W7.FinGapAt` from `W7.DelPlaceAt` (its `rcw`). With the W7 copies of
`finGap_irq` / `finGap_reply` (QueueFinCur's text) and `W7.FinGapAt.ofOld` for the kinds whose caps are no CNode /
Zombie (ep, ntfn, sc, ioPort), **`W7.FinGapsAt` has only the `arch` field** (VCPU / Stage-2 / device-frame
kinds, as before); `W7.FinGapsAt.kinds` gives `W7.FinKindsAt`, `W7.delGaps_of_gaps` the W7 `DelGapsAt`.

Named premises: none new here (the [P] `rcw` and [J] `rv` are `W7.DelPlaceAt` fields, QueueSlots7); the gap
`W7.FinGapsAt.arch` is the existing `FinGapsAt.arch`.
-/
import Fl4ProofsA64.P1.QueueSlots7
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}

/-! ## The non-idle `cancel_run` / `detach` frame -/

/-- **`vcpu::cancel_run` of any thread** (an `ARMVCPURun` in flight or not), its run VCPU's `RUN_CALLER` word a
user word. -/
theorem vcpu.cancel_run.w7 {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (p : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hp : p ∈ T)
    (hrc : L.mem s (runVcpuA p) ≠ 0#u64 →
      UserW st T Cs Ω H s (core.num.U64.wrapping_add (L.mem s (runVcpuA p)) vcpu.RUN_CALLER)) :
    vcpu.cancel_run st ar s a p ⦃ r => r.2 = a ∧ BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
      L.mem r.1 (runVcpuA p) = 0#u64 ∧ WritesIn st s r.1 (fun b => UserW st T Cs Ω H s b ∨ b = runVcpuA p) ∧
      ANI st s r.1 ∧ L.cscW r.1 = L.cscW s ∧
      (∀ y ∈ T, ∀ K : U64, 3328 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → (y = p → K.val ≠ 3672) →
        L.mem r.1 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ⦄ := by
  have q := h.1.choose_spec.choose_spec
  have hT := q.tcbs
  have hN := q.nodes _ q.cur
  unfold vcpu.cancel_run
  rw [eq_of_spec_fd P0.Consts.layout.tcb.RUN_VCPU.spec]
  simp only [lift, bind_ok, L.read_eq, L.write_eq]
  split
  · rename_i hne
    have hv : L.mem s (runVcpuA p) ≠ 0#u64 := by simpa [runVcpuA] using hne
    have hU := hrc hv
    have arc := hU.1.1
    have hU1 : ∀ b ∈ ({core.num.U64.wrapping_add (L.mem s (runVcpuA p)) vcpu.RUN_CALLER} : Set U64),
        UsrW st T Cs H Sg Scs Z s b :=
      UserOK.usrW (fun b hb => by rw [Set.mem_singleton_iff.1 hb]; exact hU) h
    have w3 := writesIn_wr (st := st) (s := s) (v := 0#u64) arc
    obtain ⟨h3, f3⟩ := bufw_xfer h hU1 (w3.mono fun b hb => (Or.inr (Set.mem_singleton_iff.2 hb) :
      XferFoot T {core.num.U64.wrapping_add (L.mem s (runVcpuA p)) vcpu.RUN_CALLER} b))
    have q3 := h3.1.choose_spec.choose_spec
    obtain ⟨h4, -⟩ := rv_all (K := 3672#u64) (v := 0#u64) h3 hp (by simp)
    have a4 : Aligned (core.num.U64.wrapping_add p 3672#u64) := field_aligned (hT p hp) (by simp) (by simp)
    have c3 : L.cscW (L.wr s (core.num.U64.wrapping_add (L.mem s (runVcpuA p)) vcpu.RUN_CALLER) 0#u64) =
        L.cscW s := by
      unfold LawfulStore.cscW; rw [nodeA_wr]
      exact L.mem_wr_ne arc (nodeAt_aligned hN (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))
        (fun e => out_ne_node hU.1 q.cur hN (by simp [layout.node.CUR_SC]) e.symm)
    refine (WP.spec_ok _).2 ⟨rfl, h4, L.mem_wr_same a4, ?_, ?_, ?_, ?_⟩
    · refine (w3.trans (writesIn_wr a4)).mono fun b hb => ?_
      rcases hb with e | e
      · subst e; exact Or.inl hU
      · exact Or.inr e
    · exact (ani_out hN q.cur hU.1).trans (ani_field (q3.tcbs) (q3.nodes _ q3.cur) hp (by simp) (by simp))
    · exact (cscW_wr_field q3.tcbs (q3.nodes _ q3.cur) hp (by simp) (by simp)).trans c3
    · intro y hy K hK0 hK hK8 hne
      rw [L.mem_wr_ne a4 (field_aligned (hT y hy) hK hK8) ?_]
      · exact f3 y hy K hK0 hK hK8
      · intro e
        exact field_ne (hT p hp) (hT y hy) (by simp) hK (fun ep e2 => hne ep.symm (by simp at e2; omega))
          (UScalar.eq_of_val_eq e)
  · rename_i heq
    have hv : L.mem s (runVcpuA p) = 0#u64 := UScalar.eq_of_val_eq (by simpa [runVcpuA] using heq)
    exact (WP.spec_ok _).2 ⟨rfl, h, hv, WritesIn.refl _ _, ANI.refl _, rfl, fun _ _ _ _ _ _ _ => rfl⟩

/-- **`vcpu::detach` of a native TCB** (no bound VCPU, field 3664 zero; an `ARMVCPURun` may be in flight). -/
theorem vcpu.detach.w7 {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (p : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hp : p ∈ T)
    (hv0 : L.mem s (core.num.U64.wrapping_add p 3664#u64) = 0#u64)
    (hrc : L.mem s (runVcpuA p) ≠ 0#u64 →
      UserW st T Cs Ω H s (core.num.U64.wrapping_add (L.mem s (runVcpuA p)) vcpu.RUN_CALLER)) :
    vcpu.detach st ar s a p ⦃ r => r.2 = a ∧ BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
      L.mem r.1 (runVcpuA p) = 0#u64 ∧ WritesIn st s r.1 (fun b => UserW st T Cs Ω H s b ∨ b = runVcpuA p) ∧
      ANI st s r.1 ∧ L.cscW r.1 = L.cscW s ∧
      (∀ y ∈ T, ∀ K : U64, 3328 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → (y = p → K.val ≠ 3672) →
        L.mem r.1 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ⦄ := by
  unfold vcpu.detach
  refine WP.spec_bind (vcpu.cancel_run.w7 s a p h hp hrc) ?_
  rintro ⟨s1, a1⟩ ⟨e1, h1, rv1, w1, an1, cs1, fl1⟩
  dsimp only at e1 h1 rv1 w1 an1 cs1 fl1
  subst e1
  try simp only [WP.uncurry'_pair]
  step with vcpu.bound.spec as ⟨v, ev⟩
  have hv : v = 0#u64 := by
    rw [ev, fl1 p hp 3664#u64 (by simp) (by simp) (by simp) (fun _ => by simp)]; exact hv0
  subst hv
  rw [if_neg (by simp)]
  exact (WP.spec_ok _).2 ⟨rfl, h1, rv1, w1, an1, cs1, fl1⟩

/-! ## The finalisation after `detach` -/

/-- The thread kind's finalisation after `vcpu::detach` (the extraction's text of
`objects::finalise_cap_object`'s `Thread` arm from `notification::unbind_notification` on). -/
def finThrRest {A : Type _} (st : machine.Store S) (ar : machine.Arch A) (s2 : S) (a2 : A) (ptr : U64) :
    Result ((capability.Cap × capability.Cap) × S × A) := do
  let s3 ← notification.unbind_notification st s2 ptr
  let s4 ← timer.remove st s3 ptr
  let i ← obj.Tcb.sc st ptr s4
  let b ← obj.Sc.is_null i
  let (s5, a3) ←
    if b
    then ok (s4, a2)
    else
      do
      let s6 ← schedcontext.unbind_tcb st s4 i
      let i1 ← obj.Sc.yield_from st i s6
      let b1 ← obj.Tcb.is_null i1
      if b1
      then ok (s6, a2)
      else
        schedcontext.complete_yield_to st ar s6 a2 i1
  let (s6, a4) ← sched.suspend st ar s5 a3 ptr
  let s7 ← objects.debug_remove st s6 ptr
  let a5 ← ar.fpu_release a4 ptr
  let s8 ← obj.Tcb.slot ptr layout.tcb.SLOT_CTABLE
  ok ((capability.Cap.Zombie s8 capability.ZOMBIE_TCB layout.tcb.NUM_SLOTS, capability.Cap.Null), s7, a5)

theorem fin_thread_split {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (p : U64) :
    objects.finalise_cap_object st ar s a (.Thread p) true =
      (do
        let (s1, a1) ← smp.remote_tcb_stall st ar s a p
        let (s2, a2) ← vcpu.detach st ar s1 a1 p
        finThrRest st ar s2 a2 p) := by
  unfold objects.finalise_cap_object; rfl

/-- `finThrRest` keeps `BlkOK` (QueueFinal `fin_thread.blk`'s text from `unbind_notification` on). -/
theorem finThrRest.blk {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s1 : S) (a1 : A) (p : U64)
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

/-- `finThrRest`'s current-thread frame (QueueFinThr `fin_thread.curR`'s text from `unbind_notification` on). -/
theorem finThrRest.curR {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s1 : S) (a1 : A) (p u : U64)
    (h1 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1) (hp : p ∈ T) (hna : L.actionW s1 ≠ p)
    (hidle : L.idleW s1 ≠ p) (hu : u ∈ T) (rv1 : L.mem s1 (runVcpuA p) = 0#u64) :
    finThrRest st ar s1 a1 p ⦃ r => CurR st u s1 r.2.1 ⦄ := by
  have c1 : CurR st u s1 s1 := CurR.refl _ _
  unfold finThrRest
  refine WP.spec_bind (WP.spec_and (WP.spec_and (notification.unbind_notification.blkF s1 p h1 hp)
    (notification.unbind_notification.curR s1 p u h1 hp hu)) (notification.unbind_notification.rvst s1 p h1 hp))
    fun s2 ⟨⟨⟨h2, f2, n2⟩, c2⟩, r2⟩ => ?_
  refine WP.spec_bind (WP.spec_and (timer.remove.tf (s0 := s2) s2 p (TF.start h2) hp)
    (timer.remove.curR s2 p u h2 hp hu)) fun s3 ⟨⟨h3, f3, n3, k3, _⟩, c3⟩ => ?_
  have rv3 : L.mem s3 (runVcpuA p) = 0#u64 :=  -- a64
    (k3 p hp 3672#u64 (by simp) (by simp) (Or.inr (by simp))).trans ((r2 p hp).2.trans rv1)
  have ea3 : L.actionW s3 = L.actionW s1 := by rw [n3.1, n2.1]
  have ei3 : L.idleW s3 = L.idleW s1 := by rw [n3.2.1, n2.2.1]
  have c13 := (c1.trans c2).trans c3
  step with obj.Tcb.sc.spec as ⟨i, ei⟩
  step with obj.Sc.is_null.spec as ⟨b, eb⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
      L.actionW r.1 ≠ p ∧ CurR st u s1 r.1 ∧ L.mem r.1 (runVcpuA p) = 0#u64) ?_ ?_
  · split
    · exact (WP.spec_ok _).2 ⟨h3, by rw [ea3]; exact hna, c13, rv3⟩
    rename_i hb
    have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    obtain ⟨hiS, hit, -⟩ := h3.2.2.1.2.2.bound p hp (by rw [← ei]; exact hi0)
    rw [← ei] at hiS hit
    refine WP.spec_bind (WP.spec_and (schedcontext.unbind_tcb.blkR s3 i h3 hiS hi0
      (fun _ => by rw [hit, ea3]; exact hna) (fun _ => by rw [hit, ei3]; exact hidle))
      (schedcontext.unbind_tcb.curR s3 i u h3 hiS hi0 (fun _ => by rw [hit, ea3]; exact hna)
        (fun _ => by rw [hit, ei3]; exact hidle) hu)) fun s5 ⟨hh5, c5⟩ => ?_
    obtain ⟨h5, f5, ea5, -, -, -, r5⟩ := hh5  -- a64: `blkR` (its `RvSt`)
    have rv5 : L.mem s5 (runVcpuA p) = 0#u64 := (r5 p hp).2.trans rv3
    have na5 : L.actionW s5 ≠ p := by
      rcases ea5 with e | e
      · rw [e, ea3]; exact hna
      · rw [e]; exact fun e' => notT_small h5.1.choose_spec.choose_spec.tcbs (by simp) (e' ▸ hp)
    step with obj.Sc.yield_from.val as ⟨y, ey⟩
    step with obj.Tcb.is_null.spec as ⟨b1, eb1⟩
    split
    · exact (WP.spec_ok _).2 ⟨h5, na5, c13.trans c5, rv5⟩
    · have hiS5 : i ∈ Scs := hiS
      have hy : y ≠ 0#u64 → y ∈ T := fun hy0 => by
        rw [ey]; exact h5.2.2.1.2.2.yt.2.2 i hiS5 (by rw [← ey]; exact hy0)
      refine WP.spec_mono (WP.spec_and (WP.spec_and (schedcontext.complete_yield_to.blk hA s5 a1 y h5 hy)
        (schedcontext.complete_yield_to.curR hA s5 a1 y u h5 hy hu))
        (schedcontext.complete_yield_to.rvst hA s5 a1 y h5 hy)) ?_
      rintro ⟨s6, a6⟩ ⟨⟨⟨h6, f6, n6⟩, c6⟩, r6⟩
      exact ⟨h6, by rw [n6.1]; exact na5, (c13.trans c5).trans c6, (r6 p hp).2.trans rv5⟩
  rintro ⟨s4, a2⟩ ⟨h4, na4, c4, rv4⟩
  try simp only [WP.uncurry'_pair]
  obtain ⟨⟨Q, R, q4⟩, hB4, hX4, hS4, hSg4⟩ := id h4
  refine WP.spec_bind (WP.spec_and (sched.suspend.blk s4 a2 p h4 hp na4 rv4)
    (sched.suspend.curR s4 a2 p u Q R q4 hp hB4 hX4 hSg4 hS4 na4 (hX4.2.2.yt.2.1 p hp) hu rv4)) ?_
  rintro ⟨s5, a3⟩ ⟨⟨h5, f5⟩, c5⟩
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (objects.debug_remove.curR s5 p u h5 hp hu) fun s6 c6 => ?_
  refine WP.spec_bind (hA.fpu_release a3 p) fun a4 _ => ?_
  refine WP.spec_bind (P0.obj.Tcb.slot.p0 p _) fun s7 _ => ?_
  exact (WP.spec_ok _).2 ((c4.trans c5).trans c6)

/-! ## The thread kind without `hrv0` -/

/-- **`finalise_cap` of a thread cap on AArch64, an `ARMVCPURun` possibly in flight**: `BlkOK` and a `Cur0W`
frame. The run VCPU's `RUN_CALLER` word is a user word (`hrc`). -/
theorem fin_thread.blk7 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (p : U64)
    (fin : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hp : p ∈ T) (hna : L.actionW s ≠ p)
    (hidle : L.idleW s ≠ p)
    (hv0 : L.mem s (core.num.U64.wrapping_add p 3664#u64) = 0#u64)
    (hrc : L.mem s (runVcpuA p) ≠ 0#u64 →
      UserW st T Cs Ω H s (core.num.U64.wrapping_add (L.mem s (runVcpuA p)) vcpu.RUN_CALLER)) :
    objects.finalise_cap_object st ar s a (.Thread p) fin ⦃ r =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ∧ WritesIn st s r.2.1 (Cur0W st T Cs Ω H Sg Scs Z s) ⦄ := by
  cases fin
  · unfold objects.finalise_cap_object
    dsimp only
    split
    · rename_i hf; exact absurd hf (by simp)
    · exact (WP.spec_ok _).2 ⟨h, WritesIn.refl _ _⟩
  rw [fin_thread_split]
  have hStart := h
  obtain ⟨⟨Q0, R0, hq0⟩, hb0, hx0, hs0, hg0⟩ := hStart
  refine WP.spec_bind (WP.spec_and (smp.remote_tcb_stall.blk hA s a p h)
    (smp.remote_tcb_stall.all hA s a p hq0 hb0 hx0 hs0 hg0)) ?_
  rintro ⟨s1, a1⟩ ⟨⟨h1, f1, ea1, -, ei1⟩, _, _, _, _, _, _, _, _, _, keep, _⟩
  try simp only [WP.uncurry'_pair]
  have hv1 : L.mem s1 (core.num.U64.wrapping_add p 3664#u64) = 0#u64 := by
    rw [keep p hp 3664#u64 (by simp) (by simp)]; exact hv0
  have erv : L.mem s1 (runVcpuA p) = L.mem s (runVcpuA p) := keep p hp 3672#u64 (by simp) (by simp)
  have hrc1 : L.mem s1 (runVcpuA p) ≠ 0#u64 →
      UserW st T Cs Ω H s1 (core.num.U64.wrapping_add (L.mem s1 (runVcpuA p)) vcpu.RUN_CALLER) := fun h0 => by
    rw [erv] at h0 ⊢
    obtain ⟨u1, u2, u3⟩ := hrc h0
    exact ⟨u1.ksb f1.1, u2, u3⟩
  refine WP.spec_bind (vcpu.detach.w7 s1 a1 p h1 hp hv1 hrc1) ?_
  rintro ⟨s2, a2⟩ ⟨-, h2, rv2, w2, an2, -, -⟩
  dsimp only at h2 rv2 w2 an2
  try simp only [WP.uncurry'_pair]
  refine WP.spec_mono (finThrRest.blk hA s2 a2 p h2 hp (by rw [an2.1, ea1]; exact hna)
    (by rw [an2.2.1, ei1]; exact hidle) rv2) ?_
  rintro ⟨r1, s3, a3⟩ ⟨h3, f3⟩
  refine ⟨h3, ?_⟩
  have w01 : WritesIn st s s1 (Cur0W st T Cs Ω H Sg Scs Z s) := Foot.cur0w f1 (Set.empty_subset _)
  have w12 : WritesIn st s1 s2 (Cur0W st T Cs Ω H Sg Scs Z s1) := w2.mono fun b hb => by
    rcases hb with hu | e
    · exact Or.inr (Or.inr (Or.inr hu))
    · subst e; exact Or.inl (Or.inl ⟨p, hp, 3672#u64, by simp, by simp, by simp, by simp, rfl⟩)
  exact Cur0W.trans (Cur0W.trans w01 w12) (FootD.cur0w f3 le_rfl)

/-- **The thread kind's current-thread frame on AArch64**, without `hrv0`. -/
theorem fin_thread.curR7 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (p u : U64)
    (fin : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hp : p ∈ T) (hna : L.actionW s ≠ p)
    (hidle : L.idleW s ≠ p)
    (hv0 : L.mem s (core.num.U64.wrapping_add p 3664#u64) = 0#u64) (hu : u ∈ T)
    (hrc : L.mem s (runVcpuA p) ≠ 0#u64 →
      UserW st T Cs Ω H s (core.num.U64.wrapping_add (L.mem s (runVcpuA p)) vcpu.RUN_CALLER)) :
    objects.finalise_cap_object st ar s a (.Thread p) fin ⦃ r => CurR st u s r.2.1 ⦄ := by
  cases fin
  · unfold objects.finalise_cap_object
    dsimp only
    split
    · rename_i hf; exact absurd hf (by simp)
    · exact (WP.spec_ok _).2 (CurR.refl _ _)
  rw [fin_thread_split]
  have hStart := h
  obtain ⟨⟨Q0, R0, hq0⟩, hb0, hx0, hs0, hg0⟩ := hStart
  refine WP.spec_bind (WP.spec_and (smp.remote_tcb_stall.blk hA s a p h)
    (smp.remote_tcb_stall.all hA s a p hq0 hb0 hx0 hs0 hg0)) ?_
  rintro ⟨s1, a1⟩ ⟨⟨h1, f1, ea1, -, ei1⟩, _, _, _, _, _, ea1', ec1', _, ecs1, keep, _⟩
  try simp only [WP.uncurry'_pair]
  have c1 : CurR st u s s1 := ⟨ec1', ecs1, Or.inl (by rw [scA_eq]; exact keep u hu _ (by simp) (by simp)),
    Or.inl ea1', fun hb => by rw [stA_eq, keep u hu _ (by simp) (by simp), ← stA_eq]; exact hb⟩
  have hv1 : L.mem s1 (core.num.U64.wrapping_add p 3664#u64) = 0#u64 := by
    rw [keep p hp 3664#u64 (by simp) (by simp)]; exact hv0
  have erv : L.mem s1 (runVcpuA p) = L.mem s (runVcpuA p) := keep p hp 3672#u64 (by simp) (by simp)
  have hrc1 : L.mem s1 (runVcpuA p) ≠ 0#u64 →
      UserW st T Cs Ω H s1 (core.num.U64.wrapping_add (L.mem s1 (runVcpuA p)) vcpu.RUN_CALLER) := fun h0 => by
    rw [erv] at h0 ⊢
    obtain ⟨u1, u2, u3⟩ := hrc h0
    exact ⟨u1.ksb f1.1, u2, u3⟩
  refine WP.spec_bind (vcpu.detach.w7 s1 a1 p h1 hp hv1 hrc1) ?_
  rintro ⟨s2, a2⟩ ⟨-, h2, rv2, -, an2, cs2, fl2⟩
  dsimp only at h2 rv2 an2 cs2 fl2
  try simp only [WP.uncurry'_pair]
  have c2 : CurR st u s1 s2 := ⟨an2.2.2, cs2,
    Or.inl (by rw [scA_eq]; exact fl2 u hu _ (by simp) (by simp) (by simp) (fun _ => by simp)),
    Or.inl an2.1, fun hb => by
      rw [stA_eq, fl2 u hu _ (by simp) (by simp) (by simp) (fun _ => by simp), ← stA_eq]; exact hb⟩
  refine WP.spec_mono (finThrRest.curR hA s2 a2 p u h2 hp (by rw [an2.1, ea1]; exact hna)
    (by rw [an2.2.1, ei1]; exact hidle) hu rv2) ?_
  rintro ⟨r1, s3, a3⟩ c3
  exact (c1.trans c2).trans c3

namespace W7

/-! ## The W7 thread kind -/

theorem tcb_slotIdxW {Ω Sg : Set U64} {t i : U64} (hT : TcbPlaced T) (ht : t ∈ T) (hi : i.val < 7) :
    SlotW T Ω Sg (slotIdx t i) := by
  have ha := hT t ht
  have := ha.align; have := ha.fits
  refine ⟨?_, fun o ho h8 => Or.inl ⟨t, ht, core.num.U64.wrapping_add (core.num.U64.wrapping_mul i 32#u64) o, ?_, ?_⟩⟩
  · simp [slotIdx, Aligned, core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def,
      U64.numBits]
    omega
  · simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]; omega
  · apply UScalar.eq_of_val_eq
    simp [slotIdx, core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
    omega

theorem tcb_zombieOK {Ω Sg : Set U64} {p : U64} (hT : TcbPlaced T) (hp : p ∈ T) :
    DelCapOK T Ω Sg H Rp Nt (.Zombie p capability.ZOMBIE_TCB 7#u64) := by
  have h0 : slotIdx p 0#u64 = p := by
    apply UScalar.eq_of_val_eq
    simp [slotIdx, core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, fun p' t' n e => ?_, ?_⟩ <;> try (intros; simp_all; done)
  simp only [capability.Cap.Zombie.injEq] at e
  obtain ⟨rfl, rfl, rfl⟩ := e
  exact ⟨h0 ▸ tcb_slotIdxW hT hp (by simp), fun i hi => tcb_slotIdxW hT hp (by simpa using hi)⟩

/-- **The thread kind's finalisation on AArch64** (W7 forms), from `W7.DelPlaceAt` (its [P] `rcw`). -/
theorem finGap_thread {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop} {s0 : S}
    (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) :
    FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (fun c => ∃ x1, c = .Thread x1) s0 := by
  intro Ac s a c fin h hc hpl ⟨p, e⟩
  subst e
  have hp := hc.2.2.2.2.2 p rfl
  obtain ⟨hid, hv0⟩ := hpl.1 p rfl
  obtain ⟨Ac', hb⟩ := h.bxi
  have hb' := hb.blk
  have hT := hb.1.choose_spec.choose_spec.tcbs
  have hct : L.curW s ∈ T := hb.1.choose_spec.choose_spec.curT
  have hna := h.na p hp
  have hrc := P.rcw Ac' s p h.fr hb hp
  rw [fin_cap_eq_obj (by simp)]
  refine WP.spec_mono (WP.spec_and (WP.spec_and (fin_thread.rem hA s a p fin)
    (fin_thread.blk7 hA s a p fin hb' hp hna (Ne.symm hid) hv0 hrc))
    (fin_thread.curR7 hA s a p (L.curW s) fin hb' hp hna (Ne.symm hid) hv0 hct hrc)) ?_
  rintro ⟨⟨r1, r2⟩, s', a'⟩ ⟨⟨e, hb2, f2⟩, ec, ecs, esc, ea, enb⟩
  simp only at e hb2 f2 ec ecs esc ea enb ⊢
  refine ⟨Cur0.mk h (BlkOK.bxi hb2) ec ecs esc ea (Or.inr (enb h.nb)) f2, ?_, ?_⟩
  · simp only [Prod.mk.injEq] at e
    rw [e.1]; split
    · exact tcb_zombieOK hT hp
    · exact DelCapOK.null
  · simp only [Prod.mk.injEq] at e
    rw [e.2]; exact DelCapOK.null

/-! ## The other kinds in the W7 forms -/

/-- An x86_64-shaped finalisation of caps that are no CNode / Zombie is a W7 one. -/
theorem FinGapAt.ofOld {A : Type _} {ar : machine.Arch A} {P : capability.Cap → Prop} {s0 : S}
    (g : Fl4ProofsA64.P1.FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z P s0)
    (hP : ∀ c, P c → (∀ p r g b, c ≠ .CNode p r g b) ∧ ∀ p t n, c ≠ .Zombie p t n) :
    FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z P s0 := by
  intro Ac s a c fin h hc hpl hpc
  obtain ⟨h1, h2⟩ := hP c hpc
  exact WP.spec_mono (g Ac s a c fin h (delCapOK_of7 hc h1 h2) hpl hpc) fun r hr =>
    ⟨hr.1, delCapOK_to7 hr.2.1, delCapOK_to7 hr.2.2⟩

/-- **The IRQ handler kind's finalisation** (`FinGaps.irq`), from `DelPlace`. -/
theorem finGap_irq {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) :
    FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (fun c => ∃ x1, c = .IrqHandler x1) s0 := by
  have hS : P0.StoreTotal st := L.total
  intro Ac s a c fin h hc _ ⟨irq, e⟩
  subst e
  have hi := hc.2.1 irq rfl
  obtain ⟨Ac', hb⟩ := h.bxi
  unfold objects.finalise_cap
  simp only [bind_ok]
  refine WP.spec_bind (Pₘ := fun r : S × A => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1) ?_ ?_
  · split
    · unfold interrupt.deleting_irq_handler
      refine WP.spec_bind (interrupt.irq_slot.val s irq) fun isl eisl => ?_
      subst eisl
      have hW := slotW_to7 (irq_slotW hb hi)
      unfold cdt.delete_one
      refine WP.spec_bind (WP.spec_and (P.irq Ac' s irq h.fr hb hi) (P.cap Ac' s _ h.fr hb hW)) fun c ⟨hc', hcd⟩ => ?_
      refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
      split
      · exact (WP.spec_ok _).2 h
      refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s _ c hS) fun f _ => ?_
      rcases hc' with rfl | ⟨n, b0, b1, b2, rfl⟩
      · simp [objects.finalise_cap_object]
        exact cdt.empty_slot.cur0 hA P h hW DelCapOK.null
      · obtain ⟨hn, hH⟩ := hcd.1.1.2.1 n b0 b1 b2 rfl
        refine WP.spec_bind (fin_ntfn_obj.cur0 (ar := ar) (a := a) (fin := f) (b0 := b0) (b1 := b1) (b2 := b2) h hn hH) ?_
        rintro ⟨_, s1, a1⟩ ⟨-, h1⟩
        exact cdt.empty_slot.cur0 hA P h1 hW DelCapOK.null
    · exact (WP.spec_ok _).2 h
  rintro ⟨s1, a1⟩ h1
  simp only at h1 ⊢
  unfold objects.finalise_cap_object
  dsimp only
  split
  · exact (WP.spec_ok _).2 ⟨h1, DelCapOK.null, hc⟩
  · exact (WP.spec_ok _).2 ⟨h1, DelCapOK.null, DelCapOK.null⟩


/-- **The reply kind's finalisation** (`FinGaps.reply`). a64: from `DelPlaceAt` (its [J] `rv`, `RunVcpuInv`
along the deletion), so a `FinGapAt` at the deletion's start. -/
theorem finGap_reply {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop} {s0 : S}
    (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) :
    FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (fun c => ∃ x1 x2, c = .Reply x1 x2) s0 := by
  intro Ac s a c fin h hc _ ⟨p, x, e⟩
  subst e
  have hp := hc.1.2.2 p x rfl
  obtain ⟨Ac', hb⟩ := h.bxi
  have hRV : RunVcpuInv st T s := P.rv Ac' s h.fr hb  -- a64: [J]
  have hb' := hb.blk
  have hct : L.curW s ∈ T := hb.1.choose_spec.choose_spec.curT
  have hnb := h.nb
  rw [fin_cap_eq_obj (by simp)]
  have CS : objects.finalise_cap_object st ar s a (.Reply p x) fin ⦃ r => CurR st (L.curW s) s r.2.1 ⦄ := by
    unfold objects.finalise_cap_object
    dsimp only
    split
    swap
    · exact (WP.spec_ok _).2 (CurR.refl _ _)
    refine WP.spec_bind (obj.Reply.tcb.blk s p) fun i ei => ?_
    step with obj.Tcb.is_null.spec as ⟨b, eb⟩
    split
    · exact (WP.spec_ok _).2 (CurR.refl _ _)
    rename_i hbn
    have hi0 : i ≠ 0#u64 := fun e => hbn (by rw [eb, e]; rfl)
    have hX := hb'.2.2.1
    obtain ⟨-, hiT, -, -⟩ := hX.2.1.back p hp (by rw [← ei]; exact hi0)
    rw [← ei] at hiT
    step with obj.Tcb.state.spec as ⟨v, ev⟩
    split
    · rename_i hv
      have hst : L.mem s (stA i) = sched.TS_BLOCKED_ON_REPLY := by rw [← ev, hv]
      have hne : i ≠ L.curW s := fun e => hnb (by rw [← e, hst]; exact Or.inr rfl)
      refine WP.spec_bind (ipc.reply_remove.curR hA s a p i _ hb' hp hiT ei.symm hst hct hne
        (hRV.zero hiT fun e => not_runnable_reply (by rw [← hst, e]; exact Or.inr (Or.inr rfl)))) ?_
      rintro ⟨s1, a1⟩ c1
      exact (WP.spec_ok _).2 c1
    split
    · rename_i _ hv
      obtain ⟨⟨Q, R, h0⟩, hB, -, hS, hSg⟩ := hb'
      refine WP.spec_bind (ipc.cancel_ipc.all s a i Q R h0 hiT hB hX hSg.sub) ?_
      rintro ⟨s1, a1⟩ ⟨-, -, -, hnb1, hnr1, -, k1, -⟩
      refine (WP.spec_ok _).2 ⟨k1.curW, k1.cscW, Or.inl (k1.scf hct), k1.act, fun hb0 => ?_⟩
      by_cases e : i = L.curW s
      · rw [← e]; exact fun h' => h'.elim hnb1 hnr1
      · rw [stA_eq, k1.fld _ hct _ (by simp) (by simp) (by simp) (by simp) (fun e' => absurd e'.symm e),
          ← stA_eq]; exact hb0
    · exact (WP.spec_ok _).2 (CurR.refl _ _)
  refine WP.spec_mono (WP.spec_and (fin_reply.blk hA s a p x fin hb' hp hRV) CS) ?_
  rintro ⟨⟨r1, r2⟩, s', a'⟩ ⟨⟨e, hb2, f2⟩, ec, ecs, esc, ea, enb⟩
  simp only at e hb2 f2 ec ecs esc ea enb ⊢
  cases e
  exact ⟨Cur0.mk h (BlkOK.bxi hb2) ec ecs esc ea (Or.inr (enb hnb)) (FootD.cur0w f2 le_rfl), DelCapOK.null,
    DelCapOK.null⟩



/-- The finalisations still named on AArch64 in the W7 forms: only the VCPU / Stage-2 / device-frame kinds
(`FinGapsAt.arch`, unchanged). The thread kind is `finGap_thread`, the I/O-port kind `finGap_ioPort`. -/
structure FinGapsAt (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (s0 : S) : Prop where
  arch : FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (fun c => (∃ x1, c = .Vcpu x1) ∨
    (∃ x1 x2 x3 x4 x5, c = .Ept x1 x2 x3 x4 x5) ∨
    (∃ x1 x2 x3 x4 x5 x6 x7, c = .Frame x1 x2 x3 x4 x5 true x6 x7)) s0

/-- `W7.FinGapsAt` gives every kind (`W7.FinKindsAt`). -/
theorem FinGapsAt.kinds {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop} {s0 : S}
    (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (G : FinGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) :
    FinKindsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0 :=
  ⟨FinGapAt.ofOld (finGap_ep.at s0) (by
      rintro c ⟨_, _, _, _, _, _, rfl⟩; exact ⟨fun _ _ _ _ h => (nomatch h), fun _ _ _ h => (nomatch h)⟩),
    FinGapAt.ofOld (finGap_ntfn.at s0) (by
      rintro c ⟨_, _, _, _, rfl⟩; exact ⟨fun _ _ _ _ h => (nomatch h), fun _ _ _ h => (nomatch h)⟩),
    finGap_reply hA P,
    FinGapAt.ofOld ((finGap_sc hA).at s0) (by
      rintro c ⟨_, _, rfl⟩; exact ⟨fun _ _ _ _ h => (nomatch h), fun _ _ _ h => (nomatch h)⟩),
    finGap_thread hA P, finGap_irq hA P,
    FinGapAt.ofOld (finGap_ioPort.at s0) (by
      rintro c ⟨_, _, _, rfl⟩; exact ⟨fun _ _ _ _ h => (nomatch h), fun _ _ _ h => (nomatch h)⟩),
    G.arch⟩

/-- **The W7 `DelGapsAt`** from the W7 placement and the one remaining gap (`arch`). -/
theorem delGaps_of_gaps {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop} {s0 : S}
    (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (G : FinGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) :
    DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0 :=
  delGaps_of hA P (G.kinds hA P)

end W7

end

end Fl4ProofsA64.P1
