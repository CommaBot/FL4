/-
P3 (issue #16, g7b): **`ScStepP1` of the SchedContext and SchedControl
decodes at `JAtZ`** (INV-PLAN §1.U3L C9 / C14, the `rest` premises of
`JSchedCtxPathU4` / `JSchedCPathU4`), from ScRestP1's P1 lemmas.

At a dispatch state with `JAtZ` and `Entered`:
* P1's `BlkOK` is `JAtZ.blk`; the current thread is runnable (`curRunnable`,
  `ct_schedulable`, `schedulable_eq`) and no switch is pending (the action
  word is 0, `SchedRel.act`);
* every TCB's affinity and every SC's core is the current core
  (`SchedRel`'s one core: `SchedCore.aff`, `SchedSpec.core`), so a Bind's or
  Configure's `migrate_tcb` is a no-op;
* the invoked SC is an `H` SC (`JPlaced.cobj`, `JAtZ.scCtxCap`), not bound to
  the idle thread; the first extra slot (`ExtraRel`) is a typed-heap slot, its
  notification / thread / SC cap names an `H` object (`JAtZ.capN`,
  `CapValid`, `JPlaced.cobj`), and the slot's words miss the current node,
  the only words `remote_tcb_stall` writes (`JAtZ.nodeW_notSlot`).

Then the decode writes within P1's `Foot` (`KW`), which keeps core 0's
`DEBUG_TCBS` word and every debug word (`JAtZ.kw_dbg`, `JAtZ.kw_dbgKeep`),
and leaves `BlkOK`: `ScStepP1` after every outcome
(`JAtZ.scCtxStepP1`, `JAtZ.scCtlStepP1`), so after the ones the `rest`
premises ask about.
-/
import Fl4Proofs.P3.ScRestP1
import Fl4Proofs.P3.XTopJointEntry
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **P1's footprint gives `ScStepP1`** (`JAtZ.kw_dbg`, `JAtZ.kw_dbgKeep`). -/
theorem JAtZ.stepP1_of_foot {s s' : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {Ac' : Set U64}
    (hb : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac' s')
    (hf : P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) ∅ s s') :
    ScStepP1 (L := L) Z H Cs s s' := by
  have hw : P1.WritesIn st s s' (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H)
      (P1.EH H) s) := P1.WritesIn.mono hf fun _ h => P1.KW.mono h (Set.empty_subset _)
  exact ⟨Ac', J.kw_dbg hw, J.kw_dbgKeep hw, hb⟩

/-- A word of the current node is no slot word. -/
theorem JAtZ.nodeW_notSlot {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {b : U64} (hb : P1.NodeW st s b) : ¬ SlotW Z.th b := by
  obtain ⟨o, ho, -, rfl⟩ := hb
  rintro ⟨x, hx, e⟩
  have hfit := hx.fit J.xtop.rel.1
  have hsn := J.slot_node hx J.kern.cpuCs
  have hN : P1.NodePlaced st (P1.Heap.tcbs H) s (L.cpu s) := P1.TInv.nodes J.blk _ J.kern.cpuCs
  have hv := P1.nodeAt_val hN ho
  rcases e with e | e
  · have := congrArg UScalar.val e
    omega
  · have := congrArg UScalar.val e
    have h8 : (core.num.U64.wrapping_add x 8#u64).val = x.val + 8 := by
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    omega

/-- The current thread's FL4 facts at an `Entered` dispatch state: it is
`L.curW s`, one of the TCBs, runnable, and the action word is 0. -/
theorem JAtZ.curFacts {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) :
    ct = L.curW s ∧ ct ∈ Z.T ∧ P1.Runnable (L.mem s (P1.stA (L.curW s))) ∧ L.actionW s = 0#u64 := by
  have hS := J.xtop.fin.1.1.1
  have hR := J.xtop.fin.1.1.2.2.1
  obtain ⟨Q, R, hcq, hs⟩ := hS.lists
  have hct' : ct = nodeW st s Z.c layout.node.CUR_THREAD := by
    have h := sched.cur_thread.spec' (L := L) s
    rw [hct, WP.spec_ok, hcq.cur] at h; exact h
  have ht : ct ∈ Z.T := by rw [hct']; exact hcq.curT
  have hcw : ct = L.curW s := by
    have h := P1.sched.cur_thread.spec (st := st) s
    rw [hct, WP.spec_ok] at h; exact h
  obtain ⟨hcur, xc, hkc, hrun⟩ := J.curRunnable hni hct
  have hcs := ct_schedulable (J.curInv (by rw [hni.2]; simp)) J.act J.inv (hcur ▸ hkc) hrun
  rw [hcur] at hcs
  obtain ⟨hrw, -, -, -⟩ := of_decide_eq_true ((schedulable_eq hR hS ht).trans hcs)
  have ha0 : L.actionW s = 0#u64 := by
    have h := hS.act
    rw [hni.2] at h
    unfold P1.LawfulStore.actionW; rw [hcq.cur]; exact h
  refine ⟨hcw, ht, ?_, ha0⟩
  rw [← hcw, stA_tStA]; exact hrw

set_option maxHeartbeats 4000000 in
/-- **C9: `ScStepP1` after the SchedContext decode** (Consumed, Bind,
UnbindObject) at an `Entered` `JAtZ` state (module docstring). -/
theorem JAtZ.scCtxStepP1 (hA : P0.ArchTotal arI) {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) {lbl length sc sb : U64} {blk call don fp : Bool} {buf : U64}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slot : U64} (hslot : IsSlot Z.th slot)
    (hc : capAt (L.mem s) slot = ok (.SchedContext sc sb)) (hl : ScJLabel s lbl sc)
    {excaps : List Fl4Spec.Cap} (hex : ExtraRel Z.th (L.mem s) (exAt extra 0) excaps) :
    syscall.decode_invocation st arI s ar lbl length slot (.SchedContext sc sb) blk call don fp buf extra
      ⦃ r => ScStepP1 (L := L) Z H Cs s r.2.1 ⦄ := by
  obtain ⟨hcw, hctT, hrun, hact⟩ := J.curFacts hni hct
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R, hcq, hs⟩ := hS.lists
  have hTe : Z.T = P1.Heap.tcbs H := J.tcbs_eq.1
  obtain ⟨hpC, hpi, hsb, -, hback, -⟩ := J.scCtxCap arI hslot hc
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hO := hJ.cobj _ hslot
  rw [capV_of_capAt hc] at hO
  have hpS : sc ∈ P1.Heap.scs H := ⟨_, hO.1⟩
  have hp0 : sc ≠ 0#u64 := J.c0 sc hpC
  have hidle : L.mem s (P1.scTcbA sc) ≠ 0#u64 → L.mem s (P1.scTcbA sc) ≠ L.idleW s := fun h0 e => by
    rw [scTcbA_eq] at h0 e
    exact (hback h0).2.2 (by rw [e, JAtZ.idleThread_eq arI J])
  have haff : ∀ t ∈ P1.Heap.tcbs H, L.mem s (P1.affA t) = L.mem s (P1.scCoreA sc) := fun t ht => by
    rw [hcq.aff t (hTe ▸ ht), scCoreA_eq, hS.core sc hpC]
  have hx : ∀ s', P1.WritesIn st s s' (P1.NodeW st s) → ∀ sl, Aeneas.Std.Array.index_usize extra 0#usize = ok sl →
      sl ≠ 0#u64 → obj.Slot.cap st sl s' ⦃ c => P1.ScExtraOK (P1.Heap.tcbs H) (P1.Heap.ntfns H) c ⦄ := by
    intro s' hw sl hsl h0
    obtain rfl : exAt extra 0 = sl := eq_of_ok_eq ((exAt_idx0 extra).symm.trans hsl)
    rcases hex with ⟨e, -⟩ | ⟨-, hxs, c, a, rest, hcx, -, hcv, -⟩
    · exact absurd e h0
    rw [slot_cap_eq, capAt_of_writes J.xtop.rel.1 hw (fun b hb => J.nodeW_notSlot hb) _ hxs, hcx, WP.spec_ok]
    refine ⟨fun p x y z e => ?_, fun p e => ?_⟩
    · subst e
      exact J.zH.2.2.2 p (J.capN ⟨_, x, y, z, hxs, capV_of_capAt hcx⟩).1
    · subst e
      exact J.zH.1 p (J.thT p hcv)
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec' as ⟨ct', _⟩
  try dsimp only
  split
  · exact (WP.spec_ok _).2 ⟨Ac, rfl, P1.DbgKeep.refl _, J.blk⟩
  · refine WP.spec_mono (P1.schedcontext.decode.footK hA s ar lbl sc call extra J.blk hl hpS hp0 hidle hrun hact
      hx haff) fun r hr => ?_
    obtain ⟨r1, s', a'⟩ := r
    obtain ⟨⟨Ac', hb⟩, hf⟩ := hr
    exact J.stepP1_of_foot hb hf

set_option maxHeartbeats 4000000 in
/-- **C14: `ScStepP1` after the SchedControl decode** at an `Entered`
`JAtZ` state, the cap's core the current one (module docstring). -/
theorem JAtZ.scCtlStepP1 (hA : P0.ArchTotal arI) {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) {lbl length cpu : U64} {blk call don fp : Bool} {buf : U64}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slot : U64} (hcpu : cpu = Z.c)
    {excaps : List Fl4Spec.Cap} (hex : ExtraRel Z.th (L.mem s) (exAt extra 0) excaps) :
    syscall.decode_invocation st arI s ar lbl length slot (.SchedControl cpu) blk call don fp buf extra
      ⦃ r => ScStepP1 (L := L) Z H Cs s r.2.1 ⦄ := by
  obtain ⟨hcw, hctT, hrun, hact⟩ := J.curFacts hni hct
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R, hcq, hs⟩ := hS.lists
  have hcC : cpu ∈ Cs := by rw [hcpu, ← hcq.cur]; exact J.kern.cpuCs
  have hx : ∀ sl, Aeneas.Std.Array.index_usize extra 0#usize = ok sl → sl ≠ 0#u64 →
      obj.Slot.cap st sl s ⦃ c => ∀ ptr sz, c = .SchedContext ptr sz →
        ptr ∈ P1.Heap.scs H ∧ ptr ≠ 0#u64 ∧ sz.val = P1.Heap.scBits H ptr ∧
        (L.mem s (P1.scTcbA ptr) ≠ 0#u64 → L.mem s (P1.affA (L.mem s (P1.scTcbA ptr))) = cpu) ⦄ := by
    intro sl hsl h0
    obtain rfl : exAt extra 0 = sl := eq_of_ok_eq ((exAt_idx0 extra).symm.trans hsl)
    rcases hex with ⟨e, -⟩ | ⟨-, hxs, c, a, rest, hcx, -, -, -⟩
    · exact absurd e h0
    rw [slot_cap_eq, hcx, WP.spec_ok]
    rintro ptr sz rfl
    obtain ⟨hpC, -, -, -, hback, -⟩ := J.scCtxCap arI hxs hcx
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    have hO := hJ.cobj _ hxs
    rw [capV_of_capAt hcx] at hO
    refine ⟨⟨_, hO.1⟩, J.c0 ptr hpC, (P1.Heap.scBits_eq hO.1).symm, fun h0' => ?_⟩
    rw [scTcbA_eq] at h0' ⊢
    rw [hcq.aff _ (hback h0').1, hcpu]
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec' as ⟨ct', _⟩
  try dsimp only
  split
  · exact (WP.spec_ok _).2 ⟨Ac, rfl, P1.DbgKeep.refl _, J.blk⟩
  · refine WP.spec_mono (P1.schedcontext.decode_sched_control.footK hA J.blk hcC hrun hact hx) fun r hr => ?_
    obtain ⟨r1, s', a'⟩ := r
    obtain ⟨⟨Ac', hb⟩, hf⟩ := hr
    exact J.stepP1_of_foot hb hf

end

end

end Fl4Proofs.P3
