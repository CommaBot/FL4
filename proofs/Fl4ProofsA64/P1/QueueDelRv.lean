/-
P1 (aarch64): **[J] `DelPlaceAt.rv` / `W7.DelPlaceAt.rv` replaced by `RunVcpuInv` carried along the deletion**
(namespace `W7.R`).

Gen 17 found [J] `W7.DelPlaceAt.rv` unjustifiable as stated: it asserts `RunVcpuInv st T s` at **every** state `s`
with `Fr0 s0 s ∧ BXI s`, and `Fr0` lets a state write any `Cur0W` word, `STATE` (3328) and `RUN_VCPU` (3672) of
any TCB included, so such states need not satisfy it. It is used only by the reply kind's finalisation
(`W7.finGap_reply`: the donation of `reply_remove` needs the replier, `TS_BLOCKED_ON_REPLY`, to run no VCPU).

This module carries `RunVcpuInv` **as part of the step relation** instead: `Cur0R s0 s := Cur0 … s0 s ∧
RunVcpuInv st T s`, and restates the W7 deletion chain over it (QueueSlots7 / QueueDelFin text, `Cur0` →
`Cur0R`), new definitions only:
* `Cur0R` and its steps: `Cur0R.capw7` / `.cw7` / `.vs` / `.ks` (W7 cap-slot, VSpace and kernel-global writes
  keep every `STATE` / `RUN_VCPU` word: `W7.blk_of_capw`'s TCB-field frame), `sched.preemption_point.cur0`
  (its `PPW` words are no TCB field), **`Cur0R.restart`** (the decode's restart of the caller: `RunVcpuInv` at the
  decode start is [J] `DecPre.rv`, the existing `P3Place.rvAt`; the caller is not `TS_RUNNING_VM`,
  `DecPre.nvm`, so `RunVcpuInv.restart`).
* `R.DelGapsAt` / `R.DelGaps` (`fin` / `deferred` / `empty` over `Cur0R`), `cdt.finalise_slot_immediate.cur0`,
  `cdt.delete.cur0`, `cdt.revoke.cur0`, `cnode_del`, `cnode_rev`, `cnode.decode.dec2`, **`decGap_cnode2`**;
  `R.FinGap(At)`, `fin_noop` / `fin_cnode` / `fin_zombie` / `fin_vs`, `ioport.apply` / `set_mask`,
  `post_cap_deletion`, `empty_slot`, `swap`, `cap_swap_for_delete`, `finalise_slot_deferred`, `delete_deferred`,
  `fin_all`, `delGaps_of`, **`delGaps_of_gaps`**.
* **`R.DelPlaceAt`**: `W7.DelPlaceAt`'s fields **without `rv`** ([P] placements `vs` / `cap` / `next` / `prev` /
  `ptw` / `elw` / `ptslot` / `pool` / `aset` / `rcw` / `irq`, unchanged).
* The reply kind (`finGap_reply0`) takes `RunVcpuInv` at the state it starts from, which `Cur0R` supplies.

What is still named (the kinds whose `RunVcpuInv` preservation is not yet proved):
* **[J] `R.FinRvAt`** (field `rv` of `R.FinGapsAt`): `objects.finalise_cap` of an endpoint, notification, reply,
  SC, thread, IRQ-handler, VCPU, Stage-2 or device-frame cap (`FinRvKind`), **from a `Cur0` state of the
  deletion where `RunVcpuInv` holds**, ends in a state where it holds. A Hoare triple about the actual
  finalisation code, so it holds or fails by the code, not by arbitrary states: the writes are `STATE` writes to
  threads blocked on the endpoint / notification / reply (`Blocked` ⇒ `RUN_VCPU = 0`), the finalised thread's
  `cancel_run` (`RUN_VCPU := 0`) before its `INACTIVE`, and no `STATE` / `RUN_VCPU` writes for SC / IRQ /
  arch kinds. The per-kind frames (`RvW`, `set_thread_state.rvi`, `RunVcpuInv.keepT`, RunVcpuFam) are the
  ingredients of its discharge, kind by kind.
* `R.FinGapsAt.arch`: the existing `W7.FinGapsAt.arch` gap (Cur0 form, unchanged).

The noop / CNode / Zombie / VSpace / I/O-port kinds and every deletion step around the finalisations
(slot writes, CDT unlinking, `post_cap_deletion`, preemption points) are proved to keep `RunVcpuInv`.
-/
import Fl4ProofsA64.P1.QueueFinThr7
import Fl4ProofsA64.P1.RunVcpuFam
import Fl4ProofsA64.P1.RunVcpuKeep
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}

namespace W7
namespace R

/-- **The deletion's step relation with [J] `RunVcpuInv` carried**: `Cur0` and `RunVcpuInv` at the state. -/
def Cur0R (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (Ac : Set U64) (s0 s : S) : Prop :=
  Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s ∧ RunVcpuInv st T s

theorem Cur0R.fr {s0 s : S} (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) : Fr0 st T Cs Ω H Sg Scs Z s0 s :=
  h.1.fr

theorem Cur0R.bxi {s0 s : S} (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) :
    ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s := h.1.bxi

theorem Cur0R.post {s0 s : S} {r : core.result.Result Unit error.Exc}
    (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) : DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r s := h.1.post

/-- W7 cap-slot writes keep `Cur0R` (they write no `STATE` / `RUN_VCPU` word). -/
theorem Cur0R.capw7 {s0 s s' : S} {B : U64 → Prop} (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (hw : WritesIn st s s' B) (hB : ∀ b, B b → W7.CapW T Ω Sg b) : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' := by
  obtain ⟨Ac', hb⟩ := h.1.bxi
  obtain ⟨-, -, -, -, -, fld, -, -⟩ := W7.blk_of_capw hb.blk hw hB
  exact ⟨h.1.capw7 hw hB, h.2.rvSt fun y hy =>
    ⟨by rw [stA_eq]; exact fld y hy 3328#u64 (by simp) (by simp) (by simp),
      fld y hy 3672#u64 (by simp) (by simp) (by simp)⟩⟩

theorem Cur0R.cw7 {s0 s : S} {m : Result S} (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (hm : m ⦃ s' => WritesIn st s s' (W7.CapW T Ω Sg) ⦄) : m ⦃ s' => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ :=
  WP.spec_mono hm fun _ w => h.capw7 w fun _ hb => hb

theorem Cur0R.vs {s0 s s' : S} {V : U64 → Prop} (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hV : VsOK Ω Sg V)
    (hw : WritesIn st s s' V) : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' :=
  h.capw7 hw fun b hb => Or.inr ⟨(hV b hb).2.1, (hV b hb).2.2⟩

/-- A kernel-global word write. -/
theorem Cur0R.ks {s0 s : S} {o v : U64} (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (ho : o.val < 223488)
    (h8 : o.val % 8 = 0) : obj.ks_set st s o v ⦃ s' => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  obtain ⟨Ac', hb⟩ := h.1.bxi
  have q := hb.1.choose_spec.choose_spec
  have hSg := hb.2.2.2.1
  refine WP.spec_mono (obj.ks_set.spec s o v) fun s' e => ?_
  subst e
  exact h.capw7 (writesIn_wr (ks_aligned q ho h8)) fun b e => e ▸ Or.inr ⟨hSg.ksΩ o ho h8, fun hb' => by
    have := hSg.ks _ hb'; rw [ks_val q ho] at this; omega⟩

/-- **The decode's restart of the caller** starts `Cur0R`: [J] `DecPre.rv` (the existing `P3Place.rvAt`) at the
decode start, the caller not `TS_RUNNING_VM` (`DecPre.nvm`) so running no VCPU. -/
theorem Cur0R.restart {s : S} {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) :
    sched.set_thread_state st s (L.curW s) sched.TS_RESTART ⦃ s1 => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s s1 ⦄ := by
  have hct : L.curW s ∈ T := D.bxi.1.choose_spec.choose_spec.curT
  refine WP.spec_mono (WP.spec_and (Cur0.restart D) (sched.set_thread_state.restart_blk (Es := ∅) s _ D.bxi.blk hct
    (runnable_ok D.run).1 (runnable_ok D.run).2)) fun s1 hh => ⟨hh.1, D.rv.restart hh.2.2.2.2 (D.rv.zero hct D.nvm)⟩

/-- A preemption point keeps `Cur0R` (its words are `WORK_UNITS` and two node words, no TCB field). -/
theorem sched.preemption_point.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s0 s : S} {a : A}
    (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) :
    sched.preemption_point st ar s a ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄ := by
  have hh := h.1
  obtain ⟨-, Ac', h1, -, -, -, -, -⟩ := hh
  have q := h1.1.choose_spec.choose_spec
  have hT := q.tcbs
  have hN := q.nodes _ q.cur
  obtain ⟨-, hΩ, -⟩ := ks_work_units h1.blk
  have ho := q.omega _ hΩ
  refine WP.spec_mono (WP.spec_and (Fl4ProofsA64.P1.sched.preemption_point.cur0 hA h.1)
    (sched.preemption_point.pp (Ac := Ac') hA s a h1.blk)) fun r hr => ⟨hr.1, h.2.rvSt ?_⟩
  have w := hr.2.2
  have ffld : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem r.2.1 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K hK hK8 => by
    refine w.mem_eq (field_aligned (hT _ hy) hK hK8) fun hp => ?_
    rcases hp with e | e | e
    · exact out_ne_field (K := K) ho hy (hT _ hy) hK (congrArg UScalar.val e)
    · exact node_ne_field (K := K) (o := layout.node.CUR_TIME) hN (by simp [layout.node.CUR_TIME]) hy
        (hT _ hy) hK (by unfold LawfulStore.nodeA at e; exact e.symm)
    · exact node_ne_field (K := K) (o := layout.node.CONSUMED) hN (by simp [layout.node.CONSUMED]) hy
        (hT _ hy) hK (by unfold LawfulStore.nodeA at e; exact e.symm)
  exact fun y hy => ⟨by rw [stA_eq]; exact ffld y hy _ (by simp) (by simp), ffld y hy 3672#u64 (by simp) (by simp)⟩

/-- The finalisation steps (P3's), each `Cur0R` in and `Cur0R` out (a64: `RunVcpuInv` carried): the caps
in cap slots are typed for deletion (`DelCapOK`); each typed cap's
finalisation, with typed remainder and cleanup caps; the deferred delete of
a cap slot; emptying a cap slot with its CDT unlinking and the typed cleanup
cap's `post_cap_deletion`; and the CDT's `NEXT` links of cap slots name cap
slots.  QueueDelFin proves this from placement (`DelPlace`) and the named
per-kind finalisations (`FinGaps`). -/
structure DelGapsAt (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (s0 : S) : Prop where
  cap : ∀ (Ac : Set U64) (s : S) (x : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    SlotW T Ω Sg x → obj.Slot.cap st x s ⦃ c => DelCapOK T Ω Sg H Rp Nt c ∧ FinPl st Scs s c ⦄
  fin : ∀ (Ac : Set U64) (s : S) (a : A) (c : capability.Cap) (fin : Bool),
    Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s → DelCapOK T Ω Sg H Rp Nt c → FinPl st Scs s c →
    objects.finalise_cap st ar s a c fin false ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧
      DelCapOK T Ω Sg H Rp Nt r.1.1 ∧ DelCapOK T Ω Sg H Rp Nt r.1.2 ⦄
  deferred : ∀ (Ac : Set U64) (s : S) (a : A) (x : U64), Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s →
    SlotW T Ω Sg x → cdt.delete_deferred st ar s a x ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄
  empty : ∀ (Ac : Set U64) (s : S) (a : A) (x : U64) (c : capability.Cap),
    Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s → SlotW T Ω Sg x → DelCapOK T Ω Sg H Rp Nt c →
    cdt.empty_slot st ar s a x c ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ⦄
  next : ∀ (Ac : Set U64) (s : S) (x : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    SlotW T Ω Sg x → obj.Slot.next st x s ⦃ n => n = 0#u64 ∨ SlotW T Ω Sg n ⦄

/-- The deletion gaps at every decode start reached from a `P3Ok` entry. -/
def DelGaps (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (P3Ok : S → Prop) : Prop :=
  ∀ s0, EntAt st P3Ok s0 → DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0
theorem zombie_last {T Ω Sg : Set U64} {H : Heap} {Rp Nt : Set U64} {p t n : U64}
    (hc : DelCapOK T Ω Sg H Rp Nt (.Zombie p t n)) (hn : n ≠ 0#u64) :
    SlotW T Ω Sg (slotIdx p (core.num.U64.wrapping_sub n 1#u64)) := by
  refine (hc.2.2.2.2.1 p t n rfl).2 _ ?_
  have : n.val ≠ 0 := fun e => hn (UScalar.eq_of_val_eq (by simpa using e))
  simp [core.num.U64.wrapping_sub_val_eq, U64.size_def, U64.numBits]; omega

set_option hygiene false in
/-- The preemption-point tail of a loop round (`Cur0` at `s2`). -/
local macro "pptail" : tactic => `(tactic| (
  refine WP.spec_bind (sched.preemption_point.cur0 hA h2) ?_
  rintro ⟨rr, s3, a3⟩ h3
  try simp only [WP.uncurry'_pair] at h3 ⊢
  try simp only [uncurry_apply_pair] at h3 ⊢
  rcases rr with _ | ee
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok]
    refine (WP.spec_ok _).2 ⟨h3, ?_⟩
    show fuel1.val < fuel.val
    omega
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    first | exact (WP.spec_ok _).2 h3 | exact h3 | exact (WP.spec_ok _).2 ⟨h3, by intro v hv; simp_all⟩ |
      exact ⟨h3, by intro v hv; simp_all⟩))

set_option maxHeartbeats 4000000 in
theorem cdt.finalise_slot_immediate.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {s0 s : S} (G : DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) {a : A} {x : U64}
    (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : SlotW T Ω Sg x) :
    cdt.finalise_slot_immediate st ar s a x ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧
      ∀ v, r.1 = .Ok v → DelCapOK T Ω Sg H Rp Nt v.cleanup ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.finalise_slot_immediate cdt.finalise_slot_immediate_loop
  apply loop.spec_decr_nat (measure := fun y => y.2.2.val)
    (inv := fun y => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 y.1)
  · rintro ⟨s1, a1, fuel⟩ h1
    simp only at h1
    dsimp only
    unfold cdt.finalise_slot_immediate_loop.body
    split
    swap
    · exact (WP.spec_ok _).2 ⟨h1, by intro v hv; simp_all⟩
    rename_i hf
    step as ⟨fuel1, hf1⟩
    obtain ⟨Acx, hbx⟩ := h1.bxi
    refine WP.spec_bind (G.cap Acx s1 x h1.fr hbx hx) fun c ⟨hc, hpl⟩ => ?_
    refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h1, fun v hv => by cases hv; exact DelCapOK.null⟩
    refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s1 x c hS) fun fin _ => ?_
    refine WP.spec_bind (G.fin Ac s1 a1 c fin h1 hc hpl) ?_
    rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨h2', hrem, hcl⟩
    try simp only [uncurry_apply_pair, WP.uncurry'_pair]
    refine WP.spec_bind (cdt.cap_removable.zombie rem x) fun br hbr => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h2', fun v hv => by cases hv; exact hcl⟩
    rename_i hbr0
    have hbr' := hbr (by simpa using hbr0)
    refine WP.spec_bind (obj.Slot.set_cap.capw (c := rem) (s := s2) hx) fun s2' w2 => ?_
    have h2 := h2'.capw7 w2 fun _ hb => hb
    have hf' : 0 < fuel.val := by simpa using hf
    split
    all_goals try pptail
    -- the zombie: the deferred delete of its last slot, then the count
    simp only [lift, bind_ok]
    rename_i zp zt zn
    have hen := zombie_last hrem (hbr' zp zt zn rfl)
    unfold obj.Slot.index
    simp only [lift, bind_ok, cte_size]
    refine WP.spec_bind (G.deferred Ac s2' a2 _ h2 hen) ?_
    rintro ⟨r, s3, a3⟩ h3
    try simp only [uncurry_apply_pair] at h3 ⊢
    rcases r with _ | e
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      refine WP.spec_bind (P0.obj.Slot.cap.p0 st x s3 hS) fun c _ => ?_
      have SC : ∀ c', obj.Slot.set_cap st x s3 c' ⦃ s' => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := fun c' =>
        WP.spec_mono (obj.Slot.set_cap.capw hx) fun s' w => h3.capw7 w fun _ hb => hb
      refine WP.spec_bind (Pₘ := fun r : S × A => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1) ?_ ?_
      · split
        all_goals try exact (WP.spec_ok _).2 h3
        split
        · split
          · refine WP.spec_bind (Pₘ := fun s' => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s') ?_
              fun s' h' => (WP.spec_ok _).2 h'
            split
            · try simp only [lift, bind_ok]
              exact SC _
            · exact (WP.spec_ok _).2 h3
          · exact (WP.spec_ok _).2 h3
        · exact (WP.spec_ok _).2 h3
      · rintro ⟨s4, a4⟩ h2
        try simp only [uncurry_apply_pair] at h2 ⊢
        pptail
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      exact (WP.spec_ok _).2 ⟨h3, by intro v hv; simp_all⟩
  · exact h

/-- `cdt.delete` (exposed) of a cap slot. -/
theorem cdt.delete.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {s0 s : S} (G : DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) {a : A} {x : U64}
    (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : SlotW T Ω Sg x) :
    cdt.delete st ar s a x true ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄ := by
  unfold cdt.delete
  simp only [↓reduceIte]
  refine WP.spec_bind (cdt.finalise_slot_immediate.cur0 hA G h hx) ?_
  rintro ⟨r, s1, a1⟩ ⟨h1, hv1⟩
  try simp only [uncurry_apply_pair] at h1 hv1 ⊢
  rcases r with v | e
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    refine WP.spec_bind (G.empty Ac s1 a1 x _ h1 hx (hv1 v rfl)) ?_
    rintro ⟨s2, a2⟩ h2
    try simp only [uncurry_apply_pair] at h2 ⊢
    exact (WP.spec_ok _).2 h2
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 h1

set_option maxHeartbeats 2000000 in
/-- `cdt.revoke` of a cap slot. -/
theorem cdt.revoke.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {s0 s : S} (G : DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) {a : A} {x : U64}
    (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : SlotW T Ω Sg x) :
    cdt.revoke st ar s a x ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.revoke cdt.revoke_loop
  apply loop.spec_decr_nat (measure := fun y => y.2.2.val)
    (inv := fun y => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 y.1)
  · rintro ⟨s1, a1, fuel⟩ h1
    simp only at h1
    dsimp only
    unfold cdt.revoke_loop.body
    split
    swap
    · exact (WP.spec_ok _).2 h1
    rename_i hf
    have hf' : 0 < fuel.val := by simpa using hf
    step as ⟨fuel1, hf1⟩
    have h1' := h1
    obtain ⟨-, Acx, hbx, -, -, -, -, -⟩ := h1'.1
    refine WP.spec_bind (G.next Acx s1 x h1.fr hbx hx) fun nx hnx => ?_
    simp only [obj.Slot.is_null, bind_ok]
    split
    · exact (WP.spec_ok _).2 h1
    rename_i hn0
    have hnW : SlotW T Ω Sg nx := hnx.resolve_left (by simpa using hn0)
    refine WP.spec_bind (P0.cdt.is_mdb_parent_of.p0 st s1 x nx hS) fun bp _ => ?_
    split
    · refine WP.spec_bind (cdt.delete.cur0 hA G h1 hnW) ?_
      rintro ⟨r, s2', a2⟩ h2
      try simp only [uncurry_apply_pair] at h2 ⊢
      rcases r with _ | e
      · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        refine WP.spec_bind (sched.preemption_point.cur0 hA h2) ?_
        rintro ⟨rr, s3, a3⟩ h3
        try simp only [uncurry_apply_pair] at h3 ⊢
        rcases rr with _ | ee
        · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok]
          refine (WP.spec_ok _).2 ⟨h3, ?_⟩
          show fuel1.val < fuel.val
          omega
        · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
            bind_tc_ok]
          exact (WP.spec_ok _).2 h3
      · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
          bind_tc_ok]
        exact (WP.spec_ok _).2 h2
    · exact (WP.spec_ok _).2 h1
  · exact h

/-- **CNode `Delete`** from `DelGaps`. -/
theorem cnode_del {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {s : S} (G : DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s) {a : A} {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {x : U64}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hx : SlotW T Ω Sg x) :
    (do
      let s1 ← sched.set_thread_state st s (L.curW s) sched.TS_RESTART
      cdt.delete st ar s1 a x true) ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ :=
  WP.spec_bind (Cur0R.restart D) fun s1 h1 => WP.spec_mono (cdt.delete.cur0 hA G h1 hx) fun r hr => by
    obtain ⟨r', s', a'⟩ := r; exact hr.post

/-- **CNode `Revoke`** from `DelGaps`. -/
theorem cnode_rev {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {s : S} (G : DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s) {a : A} {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {x : U64}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hx : SlotW T Ω Sg x) :
    (do
      let s1 ← sched.set_thread_state st s (L.curW s) sched.TS_RESTART
      cdt.revoke st ar s1 a x) ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ :=
  WP.spec_bind (Cur0R.restart D) fun s1 h1 => WP.spec_mono (cdt.revoke.cur0 hA G h1 hx) fun r hr => by
    obtain ⟨r', s', a'⟩ := r; exact hr.post

set_option hygiene false in
local macro "errleaf2" : tactic => `(tactic| first
  | exact D.err _
  | exact (WP.spec_ok _).2 (D.err _)
  | (simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, error.illegal, error.truncated, cnode.missing_source]
     first | exact D.err _ | exact (WP.spec_ok _).2 (D.err _)))

set_option maxHeartbeats 4000000 in
/-- **`cnode.decode`**, Delete and Revoke included. -/
theorem cnode.decode.dec2 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (C : CdtHyps2 st T Cs Ω H Sg Rp Scs Nt Z P3Ok) {s : S} (G : DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s)
    {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) (lbl len buf : U64)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hE : EntAt st P3Ok s) (c : capability.Cap) :
    cnode.decode st ar s a lbl len c buf extra ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cnode.decode
  simp only [error.illegal, error.truncated, bind_ok]
  split
  · errleaf2
  split
  · errleaf2
  split
  · errleaf2
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun idx _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun dep _ => ?_
  refine WP.spec_bind (WP.spec_and (C.tgt Ac s c idx dep hE D.bxi) (C.tgtW Ac s c idx dep hE D.bxi)) fun r hr => ?_
  rcases r with v | e
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    errleaf2
  have hv := hr.1 v rfl
  have hvW := slotW_to7 (hr.2 v rfl)
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  repeat' (first
    | exact (WP.spec_ok _).2 (D.err _)
    | exact lift2 (cnode.decode_copy.dec C.toCdtHyps lbl len buf v D hE hv)
    | exact lift2 (cnode.decode_cancel_badged_sends.dec C.toCdtHyps v D hE hv)
    | exact lift2 (cnode.decode_rotate.dec C.toCdtHyps len buf v D hE hv)
    | exact cnode_del hA G D hvW
    | exact cnode_rev hA G D hvW
    | split)

/-- **InvGaps' `cnode`, discharged** from `CdtHyps2` and `DelGaps`. -/
theorem decGap_cnode2 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (C : CdtHyps2 st T Cs Ω H Sg Rp Scs Nt Z P3Ok) (G : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) :
    DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .cnode := by
  intro Ac s a lbl len slot cap blk call don fp buf extra hf D _hslot hE
  cases cap <;> simp [capFam] at hf
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec as ⟨ct, _⟩
  try dsimp only
  split
  · exact (WP.spec_ok _).2 (DecPost.keep D.bxi (by simp))
  · exact cnode.decode.dec2 hA C (G s hE) a lbl len buf D hE _




/-- **The finalisation shape**: `finalise_cap` of a typed cap with `P`, from
`Cur0` to `Cur0`, with typed remainder and cleanup caps. -/
def FinGap (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A) (T Cs Ω : Set U64)
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (P : capability.Cap → Prop) : Prop :=
  ∀ (Ac : Set U64) (s0 s : S) (a : A) (c : capability.Cap) (fin : Bool),
    Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s → DelCapOK T Ω Sg H Rp Nt c → FinPl st Scs s c → P c →
    objects.finalise_cap st ar s a c fin false ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧
      DelCapOK T Ω Sg H Rp Nt r.1.1 ∧ DelCapOK T Ω Sg H Rp Nt r.1.2 ⦄

/-- `FinGap` from one decode start `s0`. -/
def FinGapAt (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A) (T Cs Ω : Set U64)
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (P : capability.Cap → Prop) (s0 : S) : Prop :=
  ∀ (Ac : Set U64) (s : S) (a : A) (c : capability.Cap) (fin : Bool),
    Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s → DelCapOK T Ω Sg H Rp Nt c → FinPl st Scs s c → P c →
    objects.finalise_cap st ar s a c fin false ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧
      DelCapOK T Ω Sg H Rp Nt r.1.1 ∧ DelCapOK T Ω Sg H Rp Nt r.1.2 ⦄

theorem FinGap.at {A : Type _} {ar : machine.Arch A} {P : capability.Cap → Prop}
    (g : FinGap st ar T Cs Ω H Sg Rp Scs Nt Z P) (s0 : S) : FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z P s0 :=
  fun Ac s a c fin => g Ac s0 s a c fin

theorem fin_noop {A : Type _} {ar : machine.Arch A} {s0 s : S} {a : A} {c : capability.Cap} {fin : Bool}
    (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (hc : c = .Null ∨ (∃ x y z w, c = .Untyped x y z w) ∨ c = .IrqControl ∨ c = .Domain ∨
      (∃ x, c = .SchedControl x) ∨ c = .AsidControl ∨ c = .IoPortControl ∨ c = .TdxControl) :
    objects.finalise_cap st ar s a c fin false ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧
      DelCapOK T Ω Sg H Rp Nt r.1.1 ∧ DelCapOK T Ω Sg H Rp Nt r.1.2 ⦄ := by
  rcases hc with rfl | ⟨_, _, _, _, rfl⟩ | rfl | rfl | ⟨_, rfl⟩ | rfl | rfl | rfl <;>
    simp [objects.finalise_cap, objects.finalise_cap_object, h, DelCapOK.null]

theorem fin_cnode {A : Type _} {ar : machine.Arch A} {s0 s : S} {a : A} {p r g b : U64} {fin : Bool}
    (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hc : DelCapOK T Ω Sg H Rp Nt (.CNode p r g b)) :
    objects.finalise_cap st ar s a (.CNode p r g b) fin false ⦃ x => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 x.2.1 ∧
      DelCapOK T Ω Sg H Rp Nt x.1.1 ∧ DelCapOK T Ω Sg H Rp Nt x.1.2 ⦄ := by
  obtain ⟨hp, hi⟩ := hc.2.2.2.1 p r g b rfl
  simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok]
  split
  · simp only [lift, bind_ok]
    step as ⟨n, hn⟩
    refine ⟨h, ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, DelCapOK.null⟩ <;> try (intros; simp_all; done)
    intro p' t' n' e
    simp only [capability.Cap.Zombie.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    refine ⟨hp, fun i hlt => hi i ?_⟩
    have : (r &&& 63#u64).val = r.val % 64 := by
      simp [UScalar.val_and]; exact Nat.and_two_pow_sub_one_eq_mod r.val 6
    rw [hn, this] at hlt; exact hlt
  · exact (WP.spec_ok _).2 ⟨h, DelCapOK.null, DelCapOK.null⟩

theorem fin_zombie {A : Type _} {ar : machine.Arch A} {s0 s : S} {a : A} {p t n : U64} {fin : Bool}
    (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hc : DelCapOK T Ω Sg H Rp Nt (.Zombie p t n)) :
    objects.finalise_cap st ar s a (.Zombie p t n) fin false ⦃ x => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 x.2.1 ∧
      DelCapOK T Ω Sg H Rp Nt x.1.1 ∧ DelCapOK T Ω Sg H Rp Nt x.1.2 ⦄ := by
  simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok]
  exact (WP.spec_ok _).2 ⟨h, hc, DelCapOK.null⟩


/-- **`W7.DelPlaceAt` without [J] `rv`** (a64: `RunVcpuInv` is carried by `Cur0R` instead). The placement facts of a deletion (P3's): the caps in cap slots are typed
for their deletion (`DelCapOK`); the CDT links of a cap slot are cap slots
or null; the VSpace lookups of the unmaps name VSpace words `V` (aligned
words of the other objects outside `Sg`), and so do the ASID tables. -/
structure DelPlaceAt (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (V : U64 → Prop) (s0 : S) : Prop where
  vs : VsOK Ω Sg V
  cap : ∀ (Ac : Set U64) (s : S) (x : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → SlotW T Ω Sg x →
    obj.Slot.cap st x s ⦃ c => DelCapOK T Ω Sg H Rp Nt c ∧ FinPl st Scs s c ⦄
  next : ∀ (Ac : Set U64) (s : S) (x : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → SlotW T Ω Sg x →
    obj.Slot.next st x s ⦃ n => n = 0#u64 ∨ SlotW T Ω Sg n ⦄
  prev : ∀ (Ac : Set U64) (s : S) (x : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → SlotW T Ω Sg x →
    obj.Slot.prev st x s ⦃ n => n = 0#u64 ∨ SlotW T Ω Sg n ⦄
  /-- a64: the slot the TTBR0/TTBR1 walk of `unmap_page_table` finds is a VSpace word. -/
  ptw : ∀ (Ac : Set U64) (s : S) (v pt table shift level : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s →
    BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    vspace.unmap_page_table_loop st s v pt table shift level ⦃ r => ∀ x, r = some x → V x ⦄
  /-- a64: the slot the Stage-2 walk (`ept.unmap_table_loop`) finds is a VSpace word. -/
  elw : ∀ (Ac : Set U64) (s : S) (v pt table shift mask rem : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s →
    BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    ept.unmap_table_loop st s v pt table shift mask rem ⦃ r => ∀ x, r = some x → V x ⦄
  /-- a64: `lookup_pt_slot`'s slot (`unmap_page`) is a VSpace word. -/
  ptslot : ∀ (Ac : Set U64) (s : S) (root v : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s →
    BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → vspace.lookup_pt_slot st s root v ⦃ lu => V lu.slot ⦄
  pool : ∀ (Ac : Set U64) (s : S) (asid i : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    vspace.asid_table st s i ⦃ pool => pool ≠ 0#u64 →
      V (core.num.U64.wrapping_add pool (core.num.U64.wrapping_mul (asid &&& 511#u64) 8#u64)) ⦄
  aset : ∀ (Ac : Set U64) (s : S) (hi : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    vspace.set_asid_table st s hi 0#u64 ⦃ s1 => WritesIn st s s1 V ⦄
  /-- **[P] (a64) `rcw`**: a thread's run VCPU's `RUN_CALLER` word is a user word (`UserW`; the kind and shape
  of VcpuCheckInv's [P] `hpw`), so `vcpu::cancel_run` of a finalised thread in an `ARMVCPURun` writes no
  kernel-object word (QueueFinThr7 `finGap_thread`). -/
  rcw : ∀ (Ac : Set U64) (s : S) (p : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    p ∈ T → L.mem s (runVcpuA p) ≠ 0#u64 →
    UserW st T Cs Ω H s (core.num.U64.wrapping_add (L.mem s (runVcpuA p)) vcpu.RUN_CALLER)
  /-- An IRQ's handler slot holds no cap or a notification cap
  (`deleting_irq_handler`). -/
  irq : ∀ (Ac : Set U64) (s : S) (i : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → i.val < 128 →
    obj.Slot.cap st (irqSlotA (L.ksb s) i) s ⦃ c => c = .Null ∨ ∃ n b0 b1 b2, c = .Notification n b0 b1 b2 ⦄


/-- **The deletion placement facts** (P3's), at every decode start reached
from a `P3Ok` entry, along the decode's frame (`Fr0`). -/
def DelPlace (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (V : U64 → Prop) (P3Ok : S → Prop) : Prop :=
  ∀ s0, EntAt st P3Ok s0 → DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0

set_option maxHeartbeats 2000000 in
/-- The VSpace kinds QueueVsFin covers. a64: PageDirectory / Pdpt are `unmap_page_table` on AArch64, and
`HighVSpace` is `delete_asid` of the tagged root. -/
theorem fin_vs {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 s : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) {a : A} {c : capability.Cap} {fin : Bool}
    (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (hc : (∃ x y z w, c = .PageTable x y z w) ∨ (∃ x y z w m asid vaddr, c = .Frame x y z w m false asid vaddr) ∨
      (∃ x y z, c = .Pml4 x y z) ∨ (∃ x y, c = .AsidPool x y) ∨ (∃ x y z w, c = .PageDirectory x y z w) ∨
      (∃ x y z w, c = .Pdpt x y z w) ∨ (∃ x y z, c = .HighVSpace x y z)) :
    objects.finalise_cap st ar s a c fin false ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧
      DelCapOK T Ω Sg H Rp Nt r.1.1 ∧ DelCapOK T Ω Sg H Rp Nt r.1.2 ⦄ := by
  have hb := h.bxi
  obtain ⟨Ac', hb⟩ := hb
  have W : ∀ (m : Result (S × A)), m ⦃ r => WritesIn st s r.1 V ⦄ →
      (do let (s1, a1) ← m; ok ((capability.Cap.Null, capability.Cap.Null), s1, a1)) ⦃ r =>
        Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧ DelCapOK T Ω Sg H Rp Nt r.1.1 ∧
        DelCapOK T Ω Sg H Rp Nt r.1.2 ⦄ := fun m hm =>
    WP.spec_bind hm fun r hr => by
      obtain ⟨s1, a1⟩ := r
      exact (WP.spec_ok _).2 ⟨h.vs P.vs hr, DelCapOK.null, DelCapOK.null⟩
  have K : (ok ((capability.Cap.Null, capability.Cap.Null), s, a) : Result _) ⦃ r =>
      Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧ DelCapOK T Ω Sg H Rp Nt r.1.1 ∧
      DelCapOK T Ω Sg H Rp Nt r.1.2 ⦄ := (WP.spec_ok _).2 ⟨h, DelCapOK.null, DelCapOK.null⟩
  have UPT : ∀ asid vaddr pt, vspace.unmap_page_table st ar s a asid vaddr pt ⦃ r => WritesIn st s r.1 V ⦄ :=
    fun asid vaddr pt => vspace.unmap_page_table.vs hA s a asid vaddr pt P.vs
      (fun table shift level => P.ptw Ac' s vaddr pt table shift level h.fr hb)
      (fun table shift mask rem => P.elw Ac' s vaddr pt table shift mask rem h.fr hb)
  rcases hc with ⟨x, y, z, w, rfl⟩ | ⟨x, y, z, w, m, asid, vaddr, rfl⟩ | ⟨x, y, z, rfl⟩ | ⟨x, y, rfl⟩ |
    ⟨x, y, z, w, rfl⟩ | ⟨x, y, z, w, rfl⟩ | ⟨x, y, z, rfl⟩
  · simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok]
    split
    · split
      · exact W _ (UPT z w x)
      · exact K
    · exact K
  · simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok, Bool.false_eq_true, ↓reduceIte]
    apply WP.spec_bind (Pₘ := fun r => WritesIn st s r.1 V)
    · split
      · split
        · exact vspace.unmap_page.vs hA s a y asid vaddr x P.vs (fun root => P.ptslot Ac' s root vaddr h.fr hb)
        · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
      · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
    · rintro ⟨s1, a1⟩ hw
      cases fin <;> cases w <;> simp only [↓reduceIte, Bool.false_eq_true, uncurry_apply_pair]
      all_goals first
        | exact (WP.spec_ok _).2 ⟨h.vs P.vs hw, DelCapOK.null, DelCapOK.null⟩
        | exact WP.spec_bind (P0.objects.retire_dma_frame.p0 st ar s1 a1 x y L.total hA) fun _ _ =>
            (WP.spec_ok _).2 ⟨h.vs P.vs hw, DelCapOK.null, DelCapOK.null⟩
  · simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok]
    split
    · split
      · exact W _ (vspace.delete_asid.vs hA s a z x P.vs fun i => P.pool Ac' s z i h.fr hb)
      · exact K
    · exact K
  · simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok]
    split
    · exact W _ (vspace.delete_asid_pool.vs hA s a y x fun hi => P.aset Ac' s hi h.fr hb)
    · exact K
  · simp only [objects.finalise_cap, objects.finalise_cap_object, vspace.unmap_page_directory, bind_ok]
    split
    · split
      · exact W _ (UPT z w x)
      · exact K
    · exact K
  · simp only [objects.finalise_cap, objects.finalise_cap_object, vspace.unmap_pdpt, bind_ok]
    split
    · split
      · exact W _ (UPT z w x)
      · exact K
    · exact K
  · simp only [objects.finalise_cap, objects.finalise_cap_object, lift, bind_ok]
    split
    · split
      · exact W _ (vspace.delete_asid.vs hA s a z _ P.vs fun i => P.pool Ac' s z i h.fr hb)
      · exact K
    · exact K


theorem ioport.apply.cur0 {s0 s : S} {w p : U64} {set : Bool} (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (hw : w.val < 1024) : ioport.apply st s w p set ⦃ s' => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold ioport.apply ioport.word_off
  simp only [lift, bind_ok]
  refine WP.spec_bind (Pₘ := fun o : U64 => o.val = 215264 + 8 * w.val) ?_ fun o ho => ?_  -- a64: 5344->215264
  · refine WP.spec_bind P0.Consts.layout.ks.IOPORT_BITMAP.spec fun b eb => ?_
    subst eb
    refine (WP.spec_ok _).2 ?_
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]; omega
  refine WP.spec_bind (P0.obj.ks_get.p0 st s _ hS) fun v _ => ?_
  split
  · exact h.ks (by omega) (by omega)
  · exact h.ks (by omega) (by omega)


theorem ioport.set_mask.cur0 {s0 s : S} {f l : U64} {set : Bool} (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (hl : l.val < 65536) (hfl : f.val ≤ l.val) :
    ioport.set_mask st s f l set ⦃ s' => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  unfold ioport.set_mask
  step as ⟨lw, hlw⟩
  step as ⟨hw, hhw⟩
  have b1 : lw.val ≤ hw.val := by
    rw [hlw, hhw, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]; exact Nat.div_le_div_right hfl
  have b2 : hw.val < 1024 := by rw [hhw, Nat.shiftRight_eq_div_pow]; omega
  simp only [lift, bind_ok]
  split
  · refine WP.spec_bind (P0.ioport.pattern.p0 _ _) fun _ _ => ?_
    exact ioport.apply.cur0 h (by omega)
  · rename_i hne
    have b3 : lw.val < hw.val := by
      rcases Nat.lt_or_eq_of_le b1 with e | e
      · exact e
      · exact absurd (UScalar.eq_of_val_eq e) hne
    refine WP.spec_bind (P0.ioport.pattern.p0 _ _) fun _ _ => ?_
    refine WP.spec_bind (ioport.apply.cur0 h (by omega)) fun s1 h1 => ?_
    step as ⟨w, hw1⟩
    refine WP.spec_bind (Pₘ := fun s2 => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s2) ?_ fun s2 h2 => ?_
    · unfold ioport.set_mask_loop
      apply loop.spec_decr_nat (measure := fun y : S × U64 => hw.val - y.2.val)
        (inv := fun y => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 y.1)
      · rintro ⟨s3, w3⟩ h3
        simp only at h3
        dsimp only
        unfold ioport.set_mask_loop.body
        split
        · rename_i hlt
          have hlt' : w3.val < hw.val := by simpa using hlt
          refine WP.spec_bind (ioport.apply.cur0 h3 (by omega)) fun s4 h4 => ?_
          step as ⟨w4, hw4⟩
          exact ⟨h4, by omega⟩
        · exact (WP.spec_ok _).2 h3
      · exact h1
    · refine WP.spec_bind (P0.ioport.pattern.p0 _ _) fun _ _ => ?_
      exact ioport.apply.cur0 h2 b2


theorem objects.post_cap_deletion.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s0 s : S} {a : A}
    {c : capability.Cap} (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hc : DelCapOK T Ω Sg H Rp Nt c) :
    objects.post_cap_deletion st ar s a c ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ⦄ := by
  unfold objects.post_cap_deletion
  cases c
  all_goals try exact (WP.spec_ok _).2 h
  · rename_i irq
    have hi := hc.2.1 irq rfl
    unfold interrupt.deleted_irq_handler
    refine WP.spec_bind (Pₘ := fun r : S × A => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1) ?_ ?_
    · unfold interrupt.set_irq_state interrupt.state_off
      simp only [lift, bind_ok]
      refine WP.spec_bind (Pₘ := fun o : U64 => o.val = 224 + 8 * irq.val) ?_ fun o ho => ?_
      · refine WP.spec_bind P0.Consts.layout.ks.IRQ_STATE.spec fun b eb => ?_
        subst eb
        refine (WP.spec_ok _).2 ?_
        simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]; omega
      refine WP.spec_bind (h.ks (v := interrupt.IRQ_INACTIVE) (by omega) (by omega)) fun s1 h1 => ?_
      exact WP.spec_bind (hA.mask_irq a irq _) fun a1 _ => (WP.spec_ok _).2 h1
    rintro ⟨s1, a1⟩ h1
    exact WP.spec_bind (hA.irq_free a1 irq) fun a2 _ => (WP.spec_ok _).2 h1
  · rename_i f l o
    obtain ⟨hfl, hl⟩ := hc.2.2.1 f l o rfl
    unfold ioport.free_ioports
    exact WP.spec_bind (ioport.set_mask.cur0 h hl hfl) fun s1 h1 => (WP.spec_ok _).2 h1

set_option maxHeartbeats 1000000 in
/-- **`empty_slot`** of a cap slot, its cleanup cap typed. -/
theorem cdt.empty_slot.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 s : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) {a : A} {x : U64} {c : capability.Cap}
    (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : SlotW T Ω Sg x) (hc : DelCapOK T Ω Sg H Rp Nt c) :
    cdt.empty_slot st ar s a x c ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  obtain ⟨Ac', hb⟩ := h.bxi
  unfold cdt.empty_slot
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st x s hS) fun c0 _ => ?_
  refine WP.spec_bind (P0.capability.Cap.is_null.p0 c0) fun bn _ => ?_
  split
  · exact (WP.spec_ok _).2 h
  refine WP.spec_bind (P.prev Ac' s x h.fr hb hx) fun pv hpv => ?_
  refine WP.spec_bind (P.next Ac' s x h.fr hb hx) fun nx hnx => ?_
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st x s hS) fun fb _ => ?_
  simp only [obj.Slot.is_null, bind_ok]
  refine WP.spec_bind (Pₘ := fun s1 => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s1) ?_ fun s1 h1 => ?_
  · split
    · exact (WP.spec_ok _).2 h
    · rename_i hp0
      exact WP.spec_mono (obj.Slot.set_next.capw (hpv.resolve_left (by simpa using hp0))) fun s' w =>
        h.capw7 w fun _ hb => hb
  refine WP.spec_bind (Pₘ := fun s2 => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s2) ?_ fun s2 h2 => ?_
  · split
    · exact (WP.spec_ok _).2 h1
    · rename_i hn0
      have hnW := hnx.resolve_left (by simpa using hn0)
      refine WP.spec_bind (obj.Slot.set_prev.capw hnW) fun s3 w3 => ?_
      have h3 := h1.capw7 w3 fun _ hb => hb
      refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st nx s3 hS) fun nfb _ => ?_
      split <;> exact WP.spec_mono (obj.Slot.set_first_badged.capw hnW) fun s' w => h3.capw7 w fun _ hb => hb
  refine WP.spec_bind (obj.Slot.clear.capw hx) fun s3 w3 => ?_
  exact objects.post_cap_deletion.cur0 hA (h2.capw7 w3 fun _ hb => hb) hc
set_option maxHeartbeats 2000000 in
/-- **`cdt.swap`** of two cap slots. -/
theorem cdt.swap.cur0 {V : U64 → Prop} {s0 s : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0)
    {c1 c2 : capability.Cap} {x1 x2 : U64} (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (h1 : SlotW T Ω Sg x1) (h2 : SlotW T Ω Sg x2) :
    cdt.swap st s c1 x1 c2 x2 ⦃ s' => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.swap
  refine WP.spec_bind (h.cw7 (obj.Slot.set_cap.capw h1)) fun sa ha => ?_
  refine WP.spec_bind (ha.cw7 (obj.Slot.set_cap.capw h2)) fun sb hb => ?_
  obtain ⟨Acb, hbb⟩ := hb.bxi
  refine WP.spec_bind (P.prev Acb sb x1 hb.fr hbb h1) fun p1 hp1 => ?_
  refine WP.spec_bind (P.next Acb sb x1 hb.fr hbb h1) fun n1 hn1 => ?_
  refine WP.spec_bind (P0.obj.Slot.revocable.p0 st x1 sb hS) fun r1 _ => ?_
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st x1 sb hS) fun f1 _ => ?_
  simp only [obj.Slot.is_null, bind_ok]
  refine WP.spec_bind (Pₘ := fun s' => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s') ?_ fun sc hc => ?_
  · split
    · exact (WP.spec_ok _).2 hb
    · rename_i e; exact hb.cw7 (obj.Slot.set_next.capw (hp1.resolve_left (by simpa using e)))
  refine WP.spec_bind (Pₘ := fun s' => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s') ?_ fun sd hd => ?_
  · split
    · exact (WP.spec_ok _).2 hc
    · rename_i e; exact hc.cw7 (obj.Slot.set_prev.capw (hn1.resolve_left (by simpa using e)))
  obtain ⟨Acd, hbd⟩ := hd.bxi
  refine WP.spec_bind (P.prev Acd sd x2 hd.fr hbd h2) fun p2 hp2 => ?_
  refine WP.spec_bind (P.next Acd sd x2 hd.fr hbd h2) fun n2 hn2 => ?_
  refine WP.spec_bind (P0.obj.Slot.revocable.p0 st x2 sd hS) fun r2 _ => ?_
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st x2 sd hS) fun f2 _ => ?_
  refine WP.spec_bind (hd.cw7 (obj.Slot.set_prev.capw h1)) fun s5 h5 => ?_
  refine WP.spec_bind (h5.cw7 (obj.Slot.set_next_flags.capw h1)) fun s6 h6 => ?_
  refine WP.spec_bind (h6.cw7 (obj.Slot.set_prev.capw h2)) fun s7 h7 => ?_
  refine WP.spec_bind (h7.cw7 (obj.Slot.set_next_flags.capw h2)) fun s12 h12 => ?_
  refine WP.spec_bind (Pₘ := fun s' => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s') ?_ fun s13 h13 => ?_
  · split
    · exact (WP.spec_ok _).2 h12
    · rename_i e; exact h12.cw7 (obj.Slot.set_next.capw (hp2.resolve_left (by simpa using e)))
  split
  · exact (WP.spec_ok _).2 h13
  · rename_i e; exact h13.cw7 (obj.Slot.set_prev.capw (hn2.resolve_left (by simpa using e)))

theorem cdt.cap_swap_for_delete.cur0 {V : U64 → Prop} {s0 s : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0)
    {x1 x2 : U64} (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (h1 : SlotW T Ω Sg x1) (h2 : SlotW T Ω Sg x2) :
    cdt.cap_swap_for_delete st s x1 x2 ⦃ s' => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.cap_swap_for_delete obj.Slot.Insts.CoreCmpPartialEqSlot.eq
  simp only [bind_ok]
  split
  · exact (WP.spec_ok _).2 h
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st x1 s hS) fun c1 _ => ?_
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st x2 s hS) fun c2 _ => ?_
  exact cdt.swap.cur0 P h h1 h2

set_option hygiene false in
/-- The preemption-point tail of a deferred round (`Cur0` at `s3`). -/
local macro "dtail" : tactic => `(tactic| (
  refine WP.spec_bind (sched.preemption_point.cur0 hA h3) ?_
  rintro ⟨rr, s4, a4⟩ h4
  try simp only [uncurry_apply_pair] at h4 ⊢
  rcases rr with _ | ee
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok]
    refine (WP.spec_ok _).2 ⟨h4, ?_⟩
    show fuel1.val < fuel.val
    omega
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 ⟨h4, fun v hv => by cases hv⟩))

set_option maxHeartbeats 4000000 in
/-- **`finalise_slot_deferred`** of a cap slot: `Cur0`, the cleanup cap typed. -/
theorem cdt.finalise_slot_deferred.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 s : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (F : FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (fun _ => True) s0)
    {a : A} {x : U64} (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : SlotW T Ω Sg x) :
    cdt.finalise_slot_deferred st ar s a x ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧
      ∀ v, r.1 = .Ok v → DelCapOK T Ω Sg H Rp Nt v.cleanup ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.finalise_slot_deferred cdt.finalise_slot_deferred_loop
  apply loop.spec_decr_nat (measure := fun y => y.2.2.val)
    (inv := fun y => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 y.1)
  · rintro ⟨s1, a1, fuel⟩ h1
    simp only at h1
    dsimp only
    unfold cdt.finalise_slot_deferred_loop.body
    split
    swap
    · exact (WP.spec_ok _).2 ⟨h1, fun v hv => by cases hv⟩
    rename_i hf
    have hf' : 0 < fuel.val := by simpa using hf
    step as ⟨fuel1, hf1⟩
    obtain ⟨Acx, hbx⟩ := h1.bxi
    refine WP.spec_bind (P.cap Acx s1 x h1.fr hbx hx) fun c ⟨hc, hpl⟩ => ?_
    refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h1, fun v hv => by cases hv; exact DelCapOK.null⟩
    refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s1 x c hS) fun fin _ => ?_
    refine WP.spec_bind (F Ac s1 a1 c fin h1 hc hpl trivial) ?_
    rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨h2', hrem, hcl⟩
    try simp only [uncurry_apply_pair]
    refine WP.spec_bind (P0.cdt.cap_removable.p0 rem x) fun br _ => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h2', fun v hv => by cases hv; exact hcl⟩
    refine WP.spec_bind (h2'.cw7 (obj.Slot.set_cap.capw (c := rem) hx)) fun s2 h2 => ?_
    refine WP.spec_bind (P0.cdt.cap_cyclic_zombie.p0 rem x) fun bz _ => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h2, fun v hv => by cases hv; exact hcl⟩
    refine WP.spec_bind (Pₘ := fun s' => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s') ?_ fun s3 h3 => ?_
    · split
      all_goals try exact (WP.spec_ok _).2 h2
      rename_i zp zt zn
      exact cdt.cap_swap_for_delete.cur0 P h2 (hrem.2.2.2.2.1 zp zt zn rfl).1 hx
    dtail
  · exact h

/-- **`delete_deferred`** of a cap slot. -/
theorem cdt.delete_deferred.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 s : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (F : FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (fun _ => True) s0)
    {a : A} {x : U64} (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : SlotW T Ω Sg x) :
    cdt.delete_deferred st ar s a x ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄ := by
  unfold cdt.delete_deferred
  refine WP.spec_bind (cdt.finalise_slot_deferred.cur0 hA P F h hx) ?_
  rintro ⟨r, s1, a1⟩ ⟨h1, hv1⟩
  try simp only [uncurry_apply_pair] at h1 hv1 ⊢
  rcases r with v | e
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    split
    · refine WP.spec_bind (cdt.empty_slot.cur0 hA P h1 hx (hv1 v rfl)) ?_
      rintro ⟨s2, a2⟩ h2
      exact (WP.spec_ok _).2 h2
    · exact (WP.spec_ok _).2 h1
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 h1


def C0Gap (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A) (T Cs Ω : Set U64)
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (P : capability.Cap → Prop) (s0 : S) : Prop :=
  ∀ (Ac : Set U64) (s : S) (a : A) (c : capability.Cap) (fin : Bool),
    Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s → RunVcpuInv st T s → DelCapOK T Ω Sg H Rp Nt c → FinPl st Scs s c →
    P c → objects.finalise_cap st ar s a c fin false ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧
      DelCapOK T Ω Sg H Rp Nt r.1.1 ∧ DelCapOK T Ω Sg H Rp Nt r.1.2 ⦄

set_option maxHeartbeats 1000000 in
/-- `W7.cdt.empty_slot.cur0` (`Cur0` only) from the `rv`-free placement `R.DelPlaceAt`. -/
theorem cdt.empty_slot.c0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 s : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) {a : A} {x : U64} {c : capability.Cap}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : SlotW T Ω Sg x) (hc : DelCapOK T Ω Sg H Rp Nt c) :
    cdt.empty_slot st ar s a x c ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  obtain ⟨Ac', hb⟩ := h.bxi
  unfold cdt.empty_slot
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st x s hS) fun c0 _ => ?_
  refine WP.spec_bind (P0.capability.Cap.is_null.p0 c0) fun bn _ => ?_
  split
  · exact (WP.spec_ok _).2 h
  refine WP.spec_bind (P.prev Ac' s x h.fr hb hx) fun pv hpv => ?_
  refine WP.spec_bind (P.next Ac' s x h.fr hb hx) fun nx hnx => ?_
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st x s hS) fun fb _ => ?_
  simp only [obj.Slot.is_null, bind_ok]
  refine WP.spec_bind (Pₘ := fun s1 => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s1) ?_ fun s1 h1 => ?_
  · split
    · exact (WP.spec_ok _).2 h
    · rename_i hp0
      exact WP.spec_mono (obj.Slot.set_next.capw (hpv.resolve_left (by simpa using hp0))) fun s' w =>
        h.capw7 w fun _ hb => hb
  refine WP.spec_bind (Pₘ := fun s2 => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s2) ?_ fun s2 h2 => ?_
  · split
    · exact (WP.spec_ok _).2 h1
    · rename_i hn0
      have hnW := hnx.resolve_left (by simpa using hn0)
      refine WP.spec_bind (obj.Slot.set_prev.capw hnW) fun s3 w3 => ?_
      have h3 := h1.capw7 w3 fun _ hb => hb
      refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st nx s3 hS) fun nfb _ => ?_
      split <;> exact WP.spec_mono (obj.Slot.set_first_badged.capw hnW) fun s' w => h3.capw7 w fun _ hb => hb
  refine WP.spec_bind (obj.Slot.clear.capw hx) fun s3 w3 => ?_
  exact W7.objects.post_cap_deletion.cur0 hA (h2.capw7 w3 fun _ hb => hb) hc

/-- `W7.finGap_thread` (`Cur0` part) from the `rv`-free placement (its [P] `rcw`). -/
theorem finGap_thread0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop} {s0 : S}
    (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) :
    C0Gap st ar T Cs Ω H Sg Rp Scs Nt Z (fun c => ∃ x1, c = .Thread x1) s0 := by
  intro Ac s a c fin h _ hc hpl ⟨p, e⟩
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


/-- `W7.finGap_irq` (`Cur0` part) from the `rv`-free placement. -/
theorem finGap_irq0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) :
    C0Gap st ar T Cs Ω H Sg Rp Scs Nt Z (fun c => ∃ x1, c = .IrqHandler x1) s0 := by
  have hS : P0.StoreTotal st := L.total
  intro Ac s a c fin h _ hc _ ⟨irq, e⟩
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
        exact cdt.empty_slot.c0 hA P h hW DelCapOK.null
      · obtain ⟨hn, hH⟩ := hcd.1.1.2.1 n b0 b1 b2 rfl
        refine WP.spec_bind (fin_ntfn_obj.cur0 (ar := ar) (a := a) (fin := f) (b0 := b0) (b1 := b1) (b2 := b2) h hn hH) ?_
        rintro ⟨_, s1, a1⟩ ⟨-, h1⟩
        exact cdt.empty_slot.c0 hA P h1 hW DelCapOK.null
    · exact (WP.spec_ok _).2 h
  rintro ⟨s1, a1⟩ h1
  simp only at h1 ⊢
  unfold objects.finalise_cap_object
  dsimp only
  split
  · exact (WP.spec_ok _).2 ⟨h1, DelCapOK.null, hc⟩
  · exact (WP.spec_ok _).2 ⟨h1, DelCapOK.null, DelCapOK.null⟩


/-- **The reply kind's finalisation**, `Cur0` part, from `RunVcpuInv` **at the state it starts from** (a64: the
donation of `reply_remove` needs the replier, `TS_BLOCKED_ON_REPLY`, to run no VCPU: `RunVcpuInv.zero`).
`W7.finGap_reply`'s text with `hRV` a hypothesis instead of [J] `W7.DelPlaceAt.rv`. -/
theorem finGap_reply0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s0 : S} :
    C0Gap st ar T Cs Ω H Sg Rp Scs Nt Z (fun c => ∃ x1 x2, c = .Reply x1 x2) s0 := by
  intro Ac s a c fin h hRV hc _ ⟨p, x, e⟩
  subst e
  have hp := hc.1.2.2 p x rfl
  obtain ⟨Ac', hb⟩ := h.bxi
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


/-! ## The kinds, and what stays named -/

/-- The cap kinds whose finalisation is not yet proved to keep `RunVcpuInv` (the [J] `FinRvAt` kinds). -/
def FinRvKind (c : capability.Cap) : Prop :=
  (∃ x1 x2 x3 x4 x5 x6, c = .Endpoint x1 x2 x3 x4 x5 x6) ∨ (∃ x1 x2 x3 x4, c = .Notification x1 x2 x3 x4) ∨
  (∃ x1 x2, c = .Reply x1 x2) ∨ (∃ x1 x2, c = .SchedContext x1 x2) ∨ (∃ x1, c = .Thread x1) ∨
  (∃ x1, c = .IrqHandler x1) ∨ (∃ x1, c = .Vcpu x1) ∨ (∃ x1 x2 x3 x4 x5, c = .Ept x1 x2 x3 x4 x5) ∨
  (∃ x1 x2 x3 x4 x5 x6 x7, c = .Frame x1 x2 x3 x4 x5 true x6 x7)

/-- **[J] (a64) `FinRvAt`**: the finalisation of an endpoint, notification, reply, SC, thread, IRQ-handler, VCPU,
Stage-2 or device-frame cap (`FinRvKind`), started **from a `Cur0` state of the deletion from `s0` where
`RunVcpuInv` holds**, ends in a state where `RunVcpuInv` holds. It replaces [J] `W7.DelPlaceAt.rv` (which asserted
`RunVcpuInv` at every `Fr0 ∧ BXI` state, false in general: `Fr0` allows arbitrary `STATE` / `RUN_VCPU` writes).
Being a Hoare triple of the finalisation code it is true or false by that code: the `STATE` writes are to threads
blocked on the object (`Blocked` ⇒ `RUN_VCPU = 0` under `RunVcpuInv`), the finalised thread's `cancel_run`
clears its `RUN_VCPU` before its `INACTIVE`, and the SC / IRQ / arch kinds write no `STATE` to a non-VM value
of a thread running a VCPU. Discharge: per kind, with `RvW` (QueueDeleteRv), `set_thread_state.rvi`,
`RunVcpuInv.keepT` (RunVcpuFam). -/
def FinRvAt (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A) (T Cs Ω : Set U64)
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (s0 : S) : Prop :=
  ∀ (Ac : Set U64) (s : S) (a : A) (c : capability.Cap) (fin : Bool),
    Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s → RunVcpuInv st T s → DelCapOK T Ω Sg H Rp Nt c → FinPl st Scs s c →
    FinRvKind c → objects.finalise_cap st ar s a c fin false ⦃ r => RunVcpuInv st T r.2.1 ⦄

/-- The finalisation gaps of the `Cur0R` chain: the existing `arch` gap (`W7.FinGapsAt.arch`, `Cur0` form,
unchanged) and **[J] `rv`** (`FinRvAt`). -/
structure FinGapsAt (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (s0 : S) : Prop where
  arch : W7.FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (fun c => (∃ x1, c = .Vcpu x1) ∨
    (∃ x1 x2 x3 x4 x5, c = .Ept x1 x2 x3 x4 x5) ∨
    (∃ x1 x2 x3 x4 x5 x6 x7, c = .Frame x1 x2 x3 x4 x5 true x6 x7)) s0
  /-- **[J] (a64)** `FinRvAt` (above). -/
  rv : FinRvAt st ar T Cs Ω H Sg Rp Scs Nt Z s0

/-- `FinGapsAt` at every decode start reached from a `P3Ok` entry. -/
def FinGaps (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (P3Ok : S → Prop) : Prop :=
  ∀ s0, EntAt st P3Ok s0 → FinGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0

theorem C0Gap.ofW7 {A : Type _} {ar : machine.Arch A} {Pk : capability.Cap → Prop} {s0 : S}
    (g : W7.FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z Pk s0) : C0Gap st ar T Cs Ω H Sg Rp Scs Nt Z Pk s0 :=
  fun Ac s a c fin h _ => g Ac s a c fin h

/-- A `Cur0` finalisation (with `RunVcpuInv` at its start) and [J] `FinRvAt` give a `Cur0R` one. -/
theorem ofC0 {A : Type _} {ar : machine.Arch A} {Pk : capability.Cap → Prop} {s0 : S}
    (g : C0Gap st ar T Cs Ω H Sg Rp Scs Nt Z Pk s0) (R : FinRvAt st ar T Cs Ω H Sg Rp Scs Nt Z s0)
    (hk : ∀ c, Pk c → FinRvKind c) : FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z Pk s0 :=
  fun Ac s a c fin h hc hpl hp =>
    WP.spec_mono (WP.spec_and (g Ac s a c fin h.1 h.2 hc hpl hp) (R Ac s a c fin h.1 h.2 hc hpl (hk c hp)))
      fun _ ⟨⟨a1, a2, a3⟩, b⟩ => ⟨⟨a1, b⟩, a2, a3⟩

/-- The I/O-port kind: `revoke_ports` is a no-op on AArch64, the state is kept. -/
theorem fin_ioPort {A : Type _} {ar : machine.Arch A} {s0 s : S} {a : A} {c : capability.Cap} {fin : Bool}
    (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hc : DelCapOK T Ω Sg H Rp Nt c)
    (he : ∃ x1 x2 x3, c = .IoPort x1 x2 x3) :
    objects.finalise_cap st ar s a c fin false ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧
      DelCapOK T Ω Sg H Rp Nt r.1.1 ∧ DelCapOK T Ω Sg H Rp Nt r.1.2 ⦄ := by
  obtain ⟨f, l, o, rfl⟩ := he
  simp only [objects.finalise_cap, objects.finalise_cap_object, vcpu.revoke_ports.same, bind_ok]
  split
  · exact (WP.spec_ok _).2 ⟨h, DelCapOK.null, hc⟩
  · exact (WP.spec_ok _).2 ⟨h, DelCapOK.null, DelCapOK.null⟩

/-- **Every cap kind's finalisation over `Cur0R`**, from the `rv`-free placement and `FinGapsAt`. -/
theorem fin_all {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (G : FinGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) :
    FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (fun _ => True) s0 := by
  have ep := ofC0 (C0Gap.ofW7 (W7.FinGapAt.ofOld (finGap_ep.at s0) (by
      rintro c ⟨_, _, _, _, _, _, rfl⟩; exact ⟨fun _ _ _ _ h => (nomatch h), fun _ _ _ h => (nomatch h)⟩))) G.rv
    (by rintro c ⟨_, _, _, _, _, _, rfl⟩; exact Or.inl ⟨_, _, _, _, _, _, rfl⟩)
  have ntfn := ofC0 (C0Gap.ofW7 (W7.FinGapAt.ofOld (finGap_ntfn.at s0) (by
      rintro c ⟨_, _, _, _, rfl⟩; exact ⟨fun _ _ _ _ h => (nomatch h), fun _ _ _ h => (nomatch h)⟩))) G.rv
    (by rintro c ⟨_, _, _, _, rfl⟩; exact Or.inr (Or.inl ⟨_, _, _, _, rfl⟩))
  have reply := ofC0 (finGap_reply0 hA) G.rv
    (by rintro c ⟨_, _, rfl⟩; exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩)))
  have sc := ofC0 (C0Gap.ofW7 (W7.FinGapAt.ofOld ((finGap_sc hA).at s0) (by
      rintro c ⟨_, _, rfl⟩; exact ⟨fun _ _ _ _ h => (nomatch h), fun _ _ _ h => (nomatch h)⟩))) G.rv
    (by rintro c ⟨_, _, rfl⟩; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))))
  have thread := ofC0 (finGap_thread0 hA P) G.rv
    (by rintro c ⟨_, rfl⟩; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩)))))
  have irq := ofC0 (finGap_irq0 hA P) G.rv
    (by rintro c ⟨_, rfl⟩; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))))))
  have arch := ofC0 (C0Gap.ofW7 G.arch) G.rv (by
    rintro c (⟨_, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, _, rfl⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _, rfl⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, _, _, _, _, _, rfl⟩))))))))
  intro Ac s a c fin h hc hpl _
  cases c with
  | Null => exact fin_noop h (Or.inl rfl)
  | Untyped => exact fin_noop h (Or.inr (Or.inl ⟨_, _, _, _, rfl⟩))
  | IrqControl => exact fin_noop h (Or.inr (Or.inr (Or.inl rfl)))
  | Domain => exact fin_noop h (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | SchedControl => exact fin_noop h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩)))))
  | AsidControl => exact fin_noop h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  | IoPortControl => exact fin_noop h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  | TdxControl => exact fin_noop h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))
  | CNode => exact fin_cnode h hc
  | Zombie => exact fin_zombie h hc
  | PageTable => exact fin_vs hA P h (Or.inl ⟨_, _, _, _, rfl⟩)
  | HighVSpace => exact fin_vs hA P h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, _, rfl⟩))))))
  | Pml4 => exact fin_vs hA P h (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl⟩)))
  | AsidPool => exact fin_vs hA P h (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))))
  | Frame x1 x2 x3 x4 x5 e x6 x7 =>
    cases e
    · exact fin_vs hA P h (Or.inr (Or.inl ⟨_, _, _, _, _, _, _, rfl⟩))
    · exact arch _ _ _ _ _ h hc hpl (Or.inr (Or.inr ⟨_, _, _, _, _, _, _, rfl⟩))
  | Endpoint => exact ep _ _ _ _ _ h hc hpl ⟨_, _, _, _, _, _, rfl⟩
  | Notification => exact ntfn _ _ _ _ _ h hc hpl ⟨_, _, _, _, rfl⟩
  | Reply => exact reply _ _ _ _ _ h hc hpl ⟨_, _, rfl⟩
  | SchedContext => exact sc _ _ _ _ _ h hc hpl ⟨_, _, rfl⟩
  | Thread => exact thread _ _ _ _ _ h hc hpl ⟨_, rfl⟩
  | IrqHandler => exact irq _ _ _ _ _ h hc hpl ⟨_, rfl⟩
  | PageDirectory => exact fin_vs hA P h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl⟩)))))
  | Pdpt => exact fin_vs hA P h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl⟩))))))
  | Vcpu => exact arch _ _ _ _ _ h hc hpl (Or.inl ⟨_, rfl⟩)
  | Ept => exact arch _ _ _ _ _ h hc hpl (Or.inr (Or.inl ⟨_, _, _, _, _, rfl⟩))
  | IoPort => exact fin_ioPort h hc ⟨_, _, _, rfl⟩

/-- **`R.DelGapsAt`, discharged** from the `rv`-free placement and `FinGapsAt`. -/
theorem delGaps_of {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (G : FinGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) :
    DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0 where
  cap := P.cap
  fin Ac s a c fin h hc hpl := fin_all hA P G Ac s a c fin h hc hpl trivial
  deferred _ _ _ _ h hx := cdt.delete_deferred.cur0 hA P (fin_all hA P G) h hx
  empty _ _ _ _ _ h hx hc := cdt.empty_slot.cur0 hA P h hx hc
  next := P.next

/-- **`R.DelGaps`** at every decode start, from `R.DelPlace` and `R.FinGaps`: with `decGap_cnode2` (CNode
`Delete` / `Revoke`) **no [J] `DelPlaceAt.rv`** is needed. -/
theorem delGaps_of_gaps {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    (P : DelPlace st T Cs Ω H Sg Rp Scs Nt Z V P3Ok) (G : FinGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) :
    DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok :=
  fun s0 hE => delGaps_of hA (P s0 hE) (G s0 hE)

/-- The `CNode` family's decode gap over the `Cur0R` chain. -/
theorem decGap_cnode_rv {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    (C : CdtHyps2 st T Cs Ω H Sg Rp Scs Nt Z P3Ok) (P : DelPlace st T Cs Ω H Sg Rp Scs Nt Z V P3Ok)
    (G : FinGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .cnode :=
  decGap_cnode2 hA C (delGaps_of_gaps hA P G)

end R
end W7

end

end Fl4ProofsA64.P1
