/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN g4d): **FL4's decoders of the
quiet cap kinds keep `MR`** (`MKD.*`, arch only): MachKeepF's walk extended to
the arch-threading call graphs of `domain.decode`, `schedcontext.decode`,
`schedcontext.decode_sched_control`, `vspace.decode` (Frame / page tables /
ASID control / ASID pool), `ioport.decode_control` and `ipc.do_reply_transfer`
(scripted: scratch/mr6/topo.py + mkdgen.py on scratch/g4d/dec_order.txt).
Every arch operation reached is a field of `MRKeepD` or a query returning no
arch state (`virtualization`, `private_device_frame`, `kernel_wcet_ticks`,
`ticks_to_us`, `us_to_ticks`, `max_us`). `MKD.decode_quiet`: FL4's
`decode_invocation` of a cap of a quiet kind (`QuietF`: not CNode, Thread,
Untyped, IrqControl, IrqHandler, IoPort, Vcpu, Ept) keeps `MR`;
`MKD.decode_cnode_nrd`: a CNode cap's decode at a label other than Revoke /
Delete keeps the arch state. `LoudF`: the kinds left (Thread, Untyped,
IrqControl, IrqHandler, IoPort).
-/
import Fl4Proofs.P3.MachKeepF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

/-- **The quiet FL4 cap kinds** (module docstring): their decoders reach no
clock, interrupt or port operation. -/
def QuietF : capability.Cap → Prop
  | .CNode .. => False
  | .Thread _ => False
  | .Untyped .. => False
  | .IrqControl => False
  | .IrqHandler _ => False
  | .IoPort .. => False
  | .Vcpu _ => False
  | .Ept .. => False
  | _ => True

/-- **The loud FL4 cap kinds** (the decoders that reach a clock, interrupt or
port operation; CNode only at Revoke / Delete, handled apart). -/
def LoudF : capability.Cap → Prop
  | .Thread _ => True
  | .Untyped .. => True
  | .IrqControl => True
  | .IrqHandler _ => True
  | .IoPort .. => True
  | _ => False

theorem MKD.spec_exists {α : Type _} {m : Result α} {P : α → Prop} (h : m ⦃ r => P r ⦄) : ∃ v, m = ok v ∧ P v := by
  revert h; cases m <;> simp [WP.spec_vis, WP.spec_div, WP.spec_ok]

theorem MKD.ok_inj {α : Type _} {x y : α} (h : (ok x : Result α) = ok y) : x = y := by simpa using h

/-- Reduce a tuple-`let` continuation applied to a pair (`uncurry`). -/
macro "fb_red" : tactic =>
  `(tactic| ((try simp only [WP.uncurry'_pair]) <;> (try simp only [uncurry_apply_pair]) <;> (try simp only [Aeneas.Std.uncurry]) <;> (try dsimp only)))

theorem MKD.walk_fuel_pos : 0 < layout.WALK_FUEL.val := by
  unfold layout.WALK_FUEL; simp [core.num.U64.MAX, U64.rMax]

/-- The loop's batch record. -/
def MKD.fbB (root asid op depth i i1 i2 : Std.U64) (bb : Bool) (cnode dest_cnode : capability.Cap) : vspace.Batch :=
  { root := root, asid := asid, op := op, depth := depth, map_rights := i, cap_rights := i1, attr := i2,
    defer_delete := bb, cnode := cnode, dest_cnode := dest_cnode }

section
variable {S A C : Type} {st : machine.Store S} {arI : machine.Arch A} {AR : A → C → Prop}
  (hS : P0.StoreTotal st) (hA : P0.ArchTotal arI) (hK : MRKeepD arI AR) {c₀ : C}
include hS hA hK
set_option linter.unusedSectionVars false

set_option maxHeartbeats 4000000 in
theorem MKD.debug_configure_single_stepping {s : S} {a : A} {t : obj.Tcb} {bp : Std.U64} {n_instr : Std.U64} {is_reply : Bool} (h : AR a c₀) :
    debug.configure_single_stepping st arI s a t bp n_instr is_reply ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold debug.configure_single_stepping; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.domain_decode {s : S} {a : A} {lbl : Std.U64} {length : Std.U64} {buf : Std.U64} {extra : Array obj.Slot 3#usize} (h : AR a c₀) :
    domain.decode st arI s a lbl length buf extra ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold domain.decode; mkd_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 200000 in
theorem MKD.ept_map_frame {s : S} {a : A} {length : Std.U64} {cap : capability.Cap} {dest : obj.Slot} {buf : Std.U64} {ex : Array obj.Slot 3#usize} (h : AR a c₀) :
    ept.map_frame st arI s a length cap dest buf ex ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold ept.map_frame; mkd_walk
  all_goals (rw [WP.spec_ok]; exact h)

set_option maxHeartbeats 4000000 in
theorem MKD.faults_handle_fault_reply {s : S} {a : A} {receiver : obj.Tcb} {sender : obj.Tcb} (h : AR a c₀) :
    faults.handle_fault_reply st arI s a receiver sender ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold faults.handle_fault_reply; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.ioport_decode_control {s : S} {a : A} {lbl : Std.U64} {length : Std.U64} {slot : obj.Slot} {buf : Std.U64} {extra : Array obj.Slot 3#usize} (h : AR a c₀) :
    ioport.decode_control st arI s a lbl length slot buf extra ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold ioport.decode_control; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.ipc_do_reply_transfer {s : S} {a : A} {sender : obj.Tcb} {r : obj.Reply} {grant : Bool} (h : AR a c₀) :
    ipc.do_reply_transfer st arI s a sender r grant ⦃ r => AR r.2 c₀ ⦄ := by
  unfold ipc.do_reply_transfer; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.schedcontext_bind_tcb {s : S} {a : A} {sc : obj.Sc} {t : obj.Tcb} (h : AR a c₀) :
    schedcontext.bind_tcb st arI s a sc t ⦃ r => AR r.2 c₀ ⦄ := by
  unfold schedcontext.bind_tcb; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.schedcontext_configure_flags {s : S} {a : A} {target : obj.Sc} {cpu : Std.U64} {budget : Std.U64} {period : Std.U64} {max_refills : Std.U64} {badge : Std.U64} {flags : Std.U64} (h : AR a c₀) :
    schedcontext.configure_flags st arI s a target cpu budget period max_refills badge flags ⦃ r => AR r.2 c₀ ⦄ := by
  unfold schedcontext.configure_flags; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.schedcontext_yield_to {s : S} {a : A} {sc : obj.Sc} {call : Bool} (h : AR a c₀) :
    schedcontext.yield_to st arI s a sc call ⦃ r => AR r.2 c₀ ⦄ := by
  unfold schedcontext.yield_to; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.schedcontext_decode {s : S} {a : A} {lbl : Std.U64} {sc : obj.Sc} {call : Bool} {extra : Array obj.Slot 3#usize} (h : AR a c₀) :
    schedcontext.decode st arI s a lbl sc call extra ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold schedcontext.decode; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.schedcontext_decode_sched_control {s : S} {a : A} {lbl : Std.U64} {cpu : Std.U64} {length : Std.U64} {buf : Std.U64} {extra : Array obj.Slot 3#usize} (h : AR a c₀) :
    schedcontext.decode_sched_control st arI s a lbl cpu length buf extra ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold schedcontext.decode_sched_control; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.vspace_write_mapping {s : S} {a : A} {slot : Std.U64} {e : Std.U64} {asid : Std.U64} {vaddr : Std.U64} {defer : Bool} (h : AR a c₀) :
    vspace.write_mapping st arI s a slot e asid vaddr defer ⦃ r => AR r.2 c₀ ⦄ := by
  unfold vspace.write_mapping; mkd_walk

/-! ## FrameBatch (KENTRY-PLAN fb3m): the batch's deletes hit frame caps -/

/-- A frame cap's finalisation returns `(Null, Null)` (unmap / EPT unmap /
DMA retire: `MRKeepD` fields). -/
theorem MKD.objects_finalise_cap_frame {s : S} {a : A} {p : Std.U64} {sz : capability.FrameSize} {r : Std.U64}
    {d m e : Bool} {asd va : Std.U64} {fin exposed : Bool} (h : AR a c₀) :
    objects.finalise_cap st arI s a (.Frame p sz r d m e asd va) fin exposed ⦃ x =>
      AR x.2.2 c₀ ∧ x.1 = (.Null, .Null) ⦄ := by
  unfold objects.finalise_cap objects.finalise_cap_object
  mkd_walk

/-- `finalise_slot_immediate` on a slot holding a frame cap: one round,
`done` with cleanup `Null` (no preemption point). -/
theorem MKD.cdt_finalise_frame {s : S} {a : A} {slot : obj.Slot} {p : Std.U64} {sz : capability.FrameSize}
    {r : Std.U64} {d m e : Bool} {asd va : Std.U64}
    (hc : obj.Slot.cap st slot s = ok (.Frame p sz r d m e asd va)) (h : AR a c₀) :
    cdt.finalise_slot_immediate st arI s a slot ⦃ x =>
      AR x.2.2 c₀ ∧ x.1 = .Ok { success := true, cleanup := .Null } ⦄ := by
  unfold cdt.finalise_slot_immediate cdt.finalise_slot_immediate_loop
  apply loop.spec_decr_nat (measure := fun y => y.2.2.val)
    (inv := fun y => y.1 = s ∧ AR y.2.1 c₀ ∧ 0 < y.2.2.val)
  · rintro ⟨s1, a1, fuel⟩ ⟨e1, h1, hf⟩
    dsimp only at e1 h1 hf ⊢
    subst e1
    unfold cdt.finalise_slot_immediate_loop.body
    rw [if_pos (by scalar_tac)]
    step as ⟨fuel1, hf1⟩
    rw [hc]
    simp only [bind_ok, capability.Cap.is_null, Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s1 slot _ hS) fun fin _ => ?_
    refine WP.spec_bind (MKD.objects_finalise_cap_frame hS hA hK h1) ?_
    rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨h2, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    fb_red
    try simp only [cdt.cap_removable, bind_ok, ↓reduceIte]
    simp only [WP.spec_ok]
    first | exact ⟨h2, rfl⟩ | exact ⟨h2, trivial⟩ | exact h2
  · exact ⟨rfl, h, MKD.walk_fuel_pos⟩

/-- **The exposed delete of a slot holding a frame cap keeps `AR` and
succeeds** (finalise = unmap + DMA retire, then `empty_slot` with a `Null`
cleanup). -/
theorem MKD.cdt_delete_frame {s : S} {a : A} {slot : obj.Slot} {c : capability.Cap} {f : vspace.FrameCap}
    (hc : obj.Slot.cap st slot s = ok c) (hf : vspace.as_frame c = ok (some f)) (h : AR a c₀) :
    cdt.delete st arI s a slot true ⦃ x => AR x.2.2 c₀ ∧ x.1 = .Ok () ⦄ := by
  have hcf : ∃ p sz r d m e asd va, c = .Frame p sz r d m e asd va := by
    cases c <;> simp [vspace.as_frame] at hf
    exact ⟨_, _, _, _, _, _, _, _, rfl⟩
  obtain ⟨p, sz, r, d, m, e, asd, va, rfl⟩ := hcf
  unfold cdt.delete
  simp only [↓reduceIte]
  refine WP.spec_bind (MKD.cdt_finalise_frame hS hA hK hc h) ?_
  rintro ⟨x, s1, a1⟩ ⟨h1, hx⟩
  dsimp only at hx h1
  subst hx
  fb_red
  try simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  refine WP.spec_bind (MKD.cdt_empty_slot hS hA hK h1) ?_
  rintro ⟨s2, a2⟩ h2
  fb_red
  exact (WP.spec_ok _).2 ⟨h2, rfl⟩

set_option maxHeartbeats 4000000 in
theorem MKD.vspace_batch_map {s : S} {a : A} {slot : obj.Slot} {b : vspace.Batch} {vaddr : Std.U64} (h : AR a c₀) :
    vspace.batch_map st arI s a slot b vaddr ⦃ x => AR x.2.2 c₀ ⦄ := by
  unfold vspace.batch_map; mkd_walk

set_option maxHeartbeats 4000000 in
/-- `batch_map` writes only on its `Ok` path: every `Err` returns the input
state. -/
theorem MKD.vspace_batch_map_err {s : S} {a : A} {slot : obj.Slot} {b : vspace.Batch} {vaddr : Std.U64}
    (h : AR a c₀) :
    vspace.batch_map st arI s a slot b vaddr ⦃ x => AR x.2.2 c₀ ∧ ∀ e, x.1 = .Err e → x.2.1 = s ⦄ := by
  unfold vspace.batch_map; mkd_walk

/-- **[gap, KENTRY-PLAN fb3m] The slot facts at a batch entry's two
`cdt.delete`s**, at the entry's state `s`: (`del`) after the deferred unmap,
writing the cleared frame cap to the DELETE target and reading it back gives
it (with `LawfulStore`: `SetCap.capAt_wr2_self`, needs the target slot
aligned and the cap `EncWf`); (`cpy`) the COPY_MAP insert leaves the derived
cap in the destination (`Insert.InsWords.capAt'`, needs the CDT placement of
the source's next slot). Both hold at the decode's own state from P3's
placement facts; at the later entries' states they need the mid-batch
relation (the same gap as P1 QueueDecVs's lookups, fb3 handoff). -/
structure FbDelOK (st : machine.Store S) (s : S) (b : vspace.Batch) (w0 w1 : Std.U64) : Prop where
  del : ∀ val, cspace.lookup_target_slot st s b.cnode w0 b.depth = ok (.Ok val) →
    ∀ (c0 : capability.Cap) (f : vspace.FrameCap), obj.Slot.cap st val s = ok c0 →
      vspace.as_frame c0 = ok (some f) → ∀ s' s'' : S,
      obj.Slot.set_cap st val s' (.Frame f.ptr f.size f.rights f.is_device false false 0#u64 0#u64) = ok s'' →
      obj.Slot.cap st val s'' = ok (.Frame f.ptr f.size f.rights f.is_device false false 0#u64 0#u64)
  cpy : ∀ val val1, cspace.lookup_target_slot st s b.dest_cnode w1 b.depth = ok (.Ok val) →
    cspace.lookup_source_slot st s b.cnode w0 b.depth = ok (.Ok val1) →
    ∀ (c0 m c : capability.Cap) (f : vspace.FrameCap) (rt : capability.Rights) (s' : S),
      obj.Slot.cap st val1 s = ok c0 → vspace.as_frame c0 = ok (some f) →
      capability.mask_cap_rights rt c0 = ok m → objects.derive_cap st s val1 m = ok (.Ok c) →
      cdt.insert_with_cap st s c c0 val1 val = ok s' → obj.Slot.cap st val s' = ok c

/-- The derived copy of a frame cap is a frame cap. -/
theorem MKD.derive_frame {s : S} {x : obj.Slot} {c0 m c : capability.Cap} {f : vspace.FrameCap}
    {rt : capability.Rights} (ho : vspace.as_frame c0 = ok (some f))
    (hm : capability.mask_cap_rights rt c0 = ok m) (hd : objects.derive_cap st s x m = ok (.Ok c)) :
    ∃ f', vspace.as_frame c = ok (some f') := by
  cases c0 <;> simp [vspace.as_frame] at ho
  simp only [capability.mask_cap_rights] at hm
  obtain ⟨i, hi, -⟩ := MKD.spec_exists (P0.capability.mask_vm_rights.p0 _ rt)
  rw [hi, bind_ok] at hm
  have hm' := MKD.ok_inj hm
  subst hm'
  simp only [objects.derive_cap] at hd
  have hd' := MKD.ok_inj hd
  cases hd'
  exact ⟨_, rfl⟩

set_option maxHeartbeats 4000000 in
/-- **A batch entry keeps `AR`, given its delete slots' facts** (`FbDelOK`):
DELETE deletes the frame it read (or, after the deferred unmap, the cleared
frame it wrote back); COPY_MAP's rollback deletes the derived frame copy
(`batch_map`'s `Err` leaves the insert's state); REMAP has no delete. -/
theorem MKD.vspace_frame_batch_entry {s : S} {a : A} {b : vspace.Batch} {w0 w1 w2 : Std.U64} {df : Bool}
    (hD : FbDelOK st s b w0 w1) (h : AR a c₀) :
    vspace.frame_batch_entry st arI s a b w0 w1 w2 df ⦃ x => AR x.2.2.1 c₀ ⦄ := by
  unfold vspace.frame_batch_entry
  split
  · -- COPY_MAP
    obtain ⟨rt, hrt, -⟩ := MKD.spec_exists (P0.cspace.lookup_target_slot.p0 st s b.dest_cnode w1 b.depth hS)
    rw [hrt, bind_ok]
    rcases rt with val | e
    swap
    · mkd_walk
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    obtain ⟨re, hre, -⟩ := MKD.spec_exists (P0.cdt.ensure_empty_slot.p0 st s val hS)
    rw [hre, bind_ok]
    rcases re with _ | e
    swap
    · mkd_walk
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    obtain ⟨rs, hrs, -⟩ := MKD.spec_exists (P0.cspace.lookup_source_slot.p0 st s b.cnode w0 b.depth hS)
    rw [hrs, bind_ok]
    rcases rs with val1 | e
    swap
    · mkd_walk
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    obtain ⟨c0, hc0, -⟩ := MKD.spec_exists (P0.obj.Slot.cap.p0 st val1 s hS)
    rw [hc0, bind_ok]
    obtain ⟨o, ho, -⟩ := MKD.spec_exists (P0.vspace.as_frame.p0 c0)
    rw [ho, bind_ok]
    rcases o with _ | f
    · mkd_walk
    simp only [core.option.Option.is_none, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨rr, hrr, -⟩ := MKD.spec_exists (P0.capability.Rights.from_word.p0 b.cap_rights)
    rw [hrr, bind_ok]
    obtain ⟨mk, hmk, -⟩ := MKD.spec_exists (P0.capability.mask_cap_rights.p0 rr c0)
    rw [hmk, bind_ok]
    obtain ⟨rd, hrd, -⟩ := MKD.spec_exists (P0.objects.derive_cap.p0 st s val1 mk hS)
    rw [hrd, bind_ok]
    rcases rd with c | e
    swap
    · mkd_walk
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    obtain ⟨s1, hs1, -⟩ := MKD.spec_exists (P0.cdt.insert_with_cap.p0 st s c c0 val1 val hS)
    rw [hs1, bind_ok]
    refine WP.spec_bind (MKD.vspace_batch_map_err hS hA hK h) ?_
    rintro ⟨r5, s2, a1⟩ ⟨h1, herr⟩
    dsimp only at h1 herr
    rcases r5 with _ | e
    · fb_red
      try simp only [core.result.Result.is_err, bind_ok, Bool.false_eq_true, ↓reduceIte]
      exact (WP.spec_ok _).2 h1
    · fb_red
      try simp only [core.result.Result.is_err, bind_ok, ↓reduceIte]
      have e2 : s2 = s1 := herr e rfl
      subst e2
      obtain ⟨f', hf'⟩ := MKD.derive_frame hS hA hK ho hmk hrd
      have hcv := hD.cpy val val1 hrt hrs c0 mk c f rr s2 hc0 ho hmk hrd hs1
      refine WP.spec_bind (MKD.cdt_delete_frame hS hA hK hcv hf' h1) ?_
      rintro ⟨r6, s3, a2⟩ ⟨h2, -⟩
      fb_red
      exact (WP.spec_ok _).2 h2
  split
  · -- REMAP
    mkd_walk
  · -- DELETE
    obtain ⟨rt, hrt, -⟩ := MKD.spec_exists (P0.cspace.lookup_target_slot.p0 st s b.cnode w0 b.depth hS)
    rw [hrt, bind_ok]
    rcases rt with val | e
    swap
    · mkd_walk
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    obtain ⟨c0, hc0, -⟩ := MKD.spec_exists (P0.obj.Slot.cap.p0 st val s hS)
    rw [hc0, bind_ok]
    obtain ⟨bn, hbn, -⟩ := MKD.spec_exists (P0.capability.Cap.is_null.p0 c0)
    rw [hbn, bind_ok]
    split
    · exact (WP.spec_ok _).2 h
    obtain ⟨o, ho, -⟩ := MKD.spec_exists (P0.vspace.as_frame.p0 c0)
    rw [ho, bind_ok]
    rcases o with _ | f
    · mkd_walk
    try dsimp only
    refine WP.spec_bind (Pₘ := fun y : S × Bool => ∃ c1 f1, obj.Slot.cap st val y.1 = ok c1 ∧
      vspace.as_frame c1 = ok (some f1)) ?_ ?_
    · have hk : ok (s, df) ⦃ y => ∃ c1 f1, obj.Slot.cap st val y.1 = ok c1 ∧ vspace.as_frame c1 = ok (some f1) ⦄ :=
        (WP.spec_ok _).2 ⟨c0, f, hc0, ho⟩
      repeat' (first | exact hk | split)
      obtain ⟨⟨b2, s2⟩, hs2, -⟩ := MKD.spec_exists (P0.vspace.unmap_page_unflushed.p0 st s b.root f.size f.vaddr f.ptr hS)
      rw [hs2, bind_ok]
      fb_red
      obtain ⟨d2, hd2, -⟩ := MKD.spec_exists (show (if b2 then ok true else ok df : Result Bool) ⦃ _ => True ⦄ by
        split <;> exact (WP.spec_ok _).2 trivial)
      rw [hd2, bind_ok]
      obtain ⟨s3, hs3, -⟩ := MKD.spec_exists (P0.obj.Slot.set_cap.p0 st val s2
        (.Frame f.ptr f.size f.rights f.is_device false false 0#u64 0#u64) hS)
      rw [hs3, bind_ok]
      exact (WP.spec_ok _).2 ⟨_, _, hD.del val hrt c0 f hc0 ho s2 s3 hs3, rfl⟩
    · rintro ⟨s1, d1⟩ ⟨c1, f1, hc1, hf1⟩
      dsimp only at hc1
      fb_red
      refine WP.spec_bind (MKD.cdt_delete_frame hS hA hK hc1 hf1 h) ?_
      rintro ⟨r1, s2, a1⟩ ⟨h1, -⟩
      fb_red
      exact (WP.spec_ok _).2 h1

set_option maxHeartbeats 4000000 in
/-- **The batch loop keeps `AR`, given a mid-batch invariant `P`** that
yields every entry's delete-slot facts (`FbDelOK`) and is kept by every entry
(KENTRY-PLAN fb3m: the open gap). `words ≤ 3`, `n ≤ 255`: P0's loop
precondition (checked entry-index arithmetic). -/
theorem MKD.vspace_decode_frame_batch_loop {s : S} {a : A} {buf : Std.U64} {ct : obj.Tcb}
    {n words root asid op depth i i1 i2 : Std.U64} {bb : Bool} {cnode dest_cnode : capability.Cap}
    {done1 : Std.U64} {df : Bool} (hw : words.val ≤ 3) (hn : n.val ≤ 255) (P : S → Prop) (hP : P s)
    (hPD : ∀ s', P s' → ∀ w0 w1, FbDelOK st s' (MKD.fbB root asid op depth i i1 i2 bb cnode dest_cnode) w0 w1)
    (hPE : ∀ s' (a' : A) w0 w1 w2 d, P s' → vspace.frame_batch_entry st arI s' a' (MKD.fbB root asid op depth i i1 i2 bb cnode dest_cnode)
      w0 w1 w2 d ⦃ x => P x.2.1 ⦄)
    (h : AR a c₀) :
    vspace.decode_frame_batch_loop st arI s a buf ct n words root asid op depth i i1 i2 bb cnode dest_cnode
      done1 df ⦃ x => AR x.2.1 c₀ ⦄ := by
  unfold vspace.decode_frame_batch_loop
  apply loop.spec_decr_nat (measure := fun x => match x with | (_, _, d, _) => n.val - d.val)
    (inv := fun x => P x.1 ∧ AR x.2.1 c₀)
  · rintro ⟨x0, x1, x2, x3⟩ ⟨hp, h1⟩
    dsimp only at hp h1
    unfold vspace.decode_frame_batch_loop.body
    dsimp only
    by_cases hd : x2 < n
    · rw [if_pos hd]
      have hx : x2.val < n.val := hd
      have hm : words.val * x2.val ≤ 3 * 255 := Nat.mul_le_mul hw (by omega)
      have hE : ∀ w0 w1 w2, vspace.frame_batch_entry st arI x0 x1 (MKD.fbB root asid op depth i i1 i2 bb cnode dest_cnode)
          w0 w1 w2 x3 ⦃ y => P y.2.1 ∧ AR y.2.2.1 c₀ ⦄ := fun w0 w1 w2 => by
        obtain ⟨y, hy, hy1⟩ := MKD.spec_exists (hPE x0 x1 w0 w1 w2 x3 hp)
        obtain ⟨y', hy', hy2⟩ := MKD.spec_exists
          (MKD.vspace_frame_batch_entry hS hA hK (w2 := w2) (df := x3) (hPD x0 hp w0 w1) h1)
        rw [hy] at hy' ⊢
        have e' := MKD.ok_inj hy'
        subst e'
        exact (WP.spec_ok _).2 ⟨hy1, hy2⟩
      step as ⟨i3, hi3⟩
      step as ⟨i4, hi4⟩
      refine WP.spec_bind (P0.msg.syscall_arg.p0 st x0 ct buf i4 hS) fun w0 _ => ?_
      refine WP.spec_bind (Pₘ := fun _ => True) (by split <;> p0_split) fun w1 _ => ?_
      refine WP.spec_bind (Pₘ := fun _ => True) (by split <;> p0_split) fun w2 _ => ?_
      refine WP.spec_bind (hE w0 w1 w2) ?_
      rintro ⟨r, s1, a1, d1⟩ ⟨hp1, h2⟩
      fb_red
      rcases r with _ | e
      · fb_red
        step as ⟨done2, hd2⟩
        try simp only [WP.spec_ok]
        try dsimp only
        first
          | (refine ⟨hp1, h2, ?_⟩; scalar_tac)
          | (refine ⟨⟨hp1, h2⟩, ?_⟩; scalar_tac)
      · fb_red
        split <;> (try step) <;>
          first | exact h2 | exact (WP.spec_ok _).2 h2 | (simp only [WP.spec_ok]; exact h2)
    · rw [if_neg hd]; exact (WP.spec_ok _).2 h1
  · exact ⟨hP, h⟩

set_option maxHeartbeats 4000000 in
theorem MKD.vspace_decode_page_map {s : S} {a : A} {length : Std.U64} {slot : obj.Slot} {f : vspace.FrameCap} {buf : Std.U64} {ex : Array obj.Slot 3#usize} (h : AR a c₀) :
    vspace.decode_page_map st arI s a length slot f buf ex ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold vspace.decode_page_map; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.vspace_derive_subframe {s : S} {a : A} {length : Std.U64} {src : obj.Slot} {cap : capability.Cap} {buf : Std.U64} {ex : Array obj.Slot 3#usize} (h : AR a c₀) :
    vspace.derive_subframe st arI s a length src cap buf ex ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold vspace.derive_subframe; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.vspace_decode_frame {s : S} {a : A} {lbl : Std.U64} {length : Std.U64} {slot : obj.Slot} {cap : capability.Cap} {call : Bool} {buf : Std.U64} {ex : Array obj.Slot 3#usize} (h : AR a c₀) :
    vspace.decode_frame st arI s a lbl length slot cap call buf ex ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold vspace.decode_frame; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.vspace_decode_table_map {s : S} {a : A} {length : Std.U64} {slot : obj.Slot} {cap : capability.Cap} {level : Std.U64} {ptr : Std.U64} {buf : Std.U64} {ex : Array obj.Slot 3#usize} (h : AR a c₀) :
    vspace.decode_table_map st arI s a length slot cap level ptr buf ex ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold vspace.decode_table_map; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.vspace_decode_table_unmap {s : S} {a : A} {slot : obj.Slot} {cap : capability.Cap} {level : Std.U64} {ptr : Std.U64} {mapped : Bool} {masid : Std.U64} {mvaddr : Std.U64} (h : AR a c₀) :
    vspace.decode_table_unmap st arI s a slot cap level ptr mapped masid mvaddr ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold vspace.decode_table_unmap; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.vspace_decode_table {s : S} {a : A} {lbl : Std.U64} {length : Std.U64} {slot : obj.Slot} {cap : capability.Cap} {buf : Std.U64} {ex : Array obj.Slot 3#usize} (h : AR a c₀) :
    vspace.decode_table st arI s a lbl length slot cap buf ex ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold vspace.decode_table; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.vspace_decode {s : S} {a : A} {lbl : Std.U64} {length : Std.U64} {slot : obj.Slot} {cap : capability.Cap} {call : Bool} {buf : Std.U64} {ex : Array obj.Slot 3#usize} (h : AR a c₀) :
    vspace.decode st arI s a lbl length slot cap call buf ex ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold vspace.decode; mkd_walk

set_option maxHeartbeats 4000000 in
/-- **FL4's decode of a quiet cap keeps `MR`** (module docstring). -/
theorem MKD.decode_quiet {s : S} {a : A} {lbl length : Std.U64} {slot : obj.Slot} {c : capability.Cap}
    {blk call don fp : Bool} {buf : Std.U64} {extra : Array obj.Slot 3#usize} (hq : QuietF c) (h : AR a c₀) :
    syscall.decode_invocation st arI s a lbl length slot c blk call don fp buf extra ⦃ r => AR r.2.2 c₀ ⦄ := by
  cases c <;> simp only [QuietF] at hq <;> unfold syscall.decode_invocation <;> mkd_walk

set_option maxHeartbeats 4000000 in
/-- **FL4's CNode decode at a label other than Revoke and Delete keeps the arch
state** (its other branches return the arch state they are given). -/
theorem MKD.decode_cnode_nrd {s : S} {a : A} {lbl length : Std.U64} {slot : obj.Slot} {p r gs g : Std.U64}
    {blk call don fp : Bool} {buf : Std.U64} {extra : Array obj.Slot 3#usize}
    (hr : lbl ≠ fl4_abi.label.CNodeRevoke) (hd : lbl ≠ fl4_abi.label.CNodeDelete) (h : AR a c₀) :
    syscall.decode_invocation st arI s a lbl length slot (.CNode p r gs g) blk call don fp buf extra ⦃ r =>
      AR r.2.2 c₀ ⦄ := by
  unfold syscall.decode_invocation cnode.decode
  mkd_walk
  all_goals first | exact absurd ‹lbl = fl4_abi.label.CNodeRevoke› hr | exact absurd ‹lbl = fl4_abi.label.CNodeDelete› hd

end

end Fl4Proofs.P3
