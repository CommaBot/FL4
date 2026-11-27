/-
P3x for virtualization (line virt, gen 24, item 1a): **FL4's `untyped::decode` for the VT-x types with the gate
open**, and the decode against the gated spec decoder for both gate outcomes.

FL4 source: `crates/fl4-core/src/untyped.rs` l. 25-72 (`untyped::decode`): after the label, length and extra-cap
checks and the six message words, l. 42-43 `if new_type >= ot::X86Vcpu && new_type < ot::Count &&
a.virtualization() == 0 { return invalid_arg(0); }` (extracted: `if nt ≥ 14 then if nt < 19 then (do let i ←
virtualization a; if i = 0 then invalid_arg 0 else K) else K else K`, Funs.lean l. 43029-43040), then the same
continuation `K` (`retype_size`, `retype_dest`, `ensure_empty_slots`, `ensure_no_children`, the memory and device
checks, `align_up`, `set_thread_state Restart`, `retype`) for every type. Spec: `Fl4Spec/Ext/VirtFinalise`
`fl4DecodeUntypedInvocationV` (= `untypedVtxGate` ? `invalidArgument 0` : the ported `fl4DecodeUntypedInvocation`,
l4v `Decode_A.decode_untyped_invocation` with FL4's object sizes); `objTypeOf 14 = .archObject .vcpuObj`
(`archDataToObjType 7`, l4v `ArchDecode_A.arch_data_to_obj_type`), `zOf 14 = 15 = fl4ObjBitsApi` (`objTypeOf_fl4`
holds for every type number).

* **`untyped_decode_refines_withV`**: UntypedDecode's `untyped_decode_refines_with` with `hNative` (the type below 14
  or at least 19) replaced by **`hGate`**: whenever the decode reaches the gate (label `UntypedRetype`, ≥ 6 words, a
  non-empty first extra slot) with a type in 14..18, `virtualization()` reports a nonzero backend. Same proof, the
  gate collapsing to the shared continuation (`hcollapse`). This is a generalisation: `hNative` gives `hGate`
  vacuously.
* **`untyped_decode_refines_fl4V`**: the same against `fl4DecodeUntypedInvocation` (FL4's object sizes, every type).

(The decode against the gated spec decoder, both gate outcomes: VirtUtGateV. This file imports UntypedDecode only,
so `step` sees the same spec set as there.)

Named premises: none beyond `untyped_decode_refines_with`'s (state relations, message words, extra caps) and
`hGate` (a hypothesis on the arch state, discharged in VirtUtGateV from the [P] platform agreement). New file only;
no existing statement changed.
-/
import Fl4Proofs.P3.UntypedDecode
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`untyped_decode_refines_with` with the VT-x gate open** (module docstring). -/
theorem untyped_decode_refines_withV [Fl4Proofs.P1.PlainStore st] (bitsApi : Fl4Spec.ApiObjectType → Nat → Nat) {A : Type} (arI : machine.Arch A) (th : TypedHeap) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .untypedRetype ↔ lbl = fl4_abi.label.UntypedRetype)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hbits : ∀ (x : U64) t, args.head? = some x → objTypeOf x.val = some t → ∀ n, bitsApi t n = zOf x.val n)
    (slot : obj.Slot) (sl : Fl4Spec.CslotPtr) (hsl : slot = cslotAddr sl) (hAs : AbsSlot th sl)
    (p sb fi : U64) (dev : Bool) (hcap : capAt (L.mem s) slot = ok (.Untyped p sb fi dev))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List Fl4Spec.Cap) (hex : ExtraRel th (L.mem s) x0 excaps)
    (hGate : lbl = fl4_abi.label.UntypedRetype → 6 ≤ args.length → x0 ≠ 0#u64 →
      ∀ x, args.head? = some x → 14 ≤ x.val → x.val < 19 → ∃ v, arI.virtualization ar = ok v ∧ v ≠ 0#u64)
    (hfan : Fl4Spec.retypeFanOutLimit = 256#64)
    (Q : Fl4Spec.UntypedInvocation → core.result.Result Unit error.Exc × S × A → Prop)
    (hQ : ∀ (nt us dest off win : U64) (t : Fl4Spec.ApiObjectType) (r : Nat) (reset : Bool) (fiv : U64),
      args.head? = some nt → RetCtx (L := L) th s σ sl sb fi dev nt us dest off win t r reset fiv →
      (do
        let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
        untyped.retype st arI s2 ar slot reset ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ nt us dest off win
          dev) ⦃ res =>
        Q (.retype sl reset p.bv (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val
          (windowSlots dest r off.val win.val) dev) res ⦄) :
    untyped.decode st arI s ar lbl length slot (.Untyped p sb fi dev) buf extra ⦃ res =>
      UPost σ (Fl4Spec.decodeUntypedInvocationWith bitsApi slbl (args.map UScalar.bv) sl (absCap (.Untyped p sb fi dev)) excaps)
        s ar Q res ⦄ := by
  rw [show absCap (.Untyped p sb fi dev) = .untypedCap dev p.bv sb.val fi.val from rfl]
  unfold untyped.decode Fl4Spec.decodeUntypedInvocationWith
  by_cases hl : lbl = fl4_abi.label.UntypedRetype
  swap
  · have : (lbl != fl4_abi.label.UntypedRetype) = true := by simpa using hl
    simp only [this, P1.plain_sharing, bind_ok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ite_self, error.illegal]
    apply UPost.err (e := .Sys .IllegalOperation) (e' := .illegalOperation) _ trivial
    have : ¬ Fl4Spec.genInvocationType slbl = .untypedRetype := fun h => hl (hlbl.1 h)
    simp only [Fl4Spec.NonDetE.unlessE, this, ↓reduceIte]
    rw [show ∀ (f : Unit → Fl4Spec.SEMonad Unit Fl4Spec.UntypedInvocation),
      (Fl4Spec.NonDetE.throwError .illegalOperation >>= f) = Fl4Spec.NonDetE.throwError .illegalOperation from
      fun f => ndE_throw_bind _ f]
    rfl
  have hne : (lbl != fl4_abi.label.UntypedRetype) = false := by simpa using hl
  have hsl' : Fl4Spec.genInvocationType slbl = .untypedRetype := hlbl.2 hl
  simp only [hne, Bool.false_eq_true, ↓reduceIte, Fl4Spec.NonDetE.unlessE, hsl', ndE_pure_bind]
  by_cases h6 : length < 6#u64
  · simp only [h6, ↓reduceIte, error.truncated, bind_ok]
    apply UPost.err (e := .Sys .TruncatedMessage) (e' := .truncatedMessage) _ trivial
    have : (args.map UScalar.bv).length < 6 := by simp; scalar_tac
    simp only [Fl4Spec.NonDetE.whenE, this, ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
  have h6' : ¬ (args.map UScalar.bv).length < 6 := by simp; scalar_tac
  simp only [h6, ↓reduceIte, Fl4Spec.NonDetE.whenE, h6', ndE_pure_bind, hx0, bind_ok, obj.Slot.is_null]
  rcases hex with ⟨rfl, rfl⟩ | ⟨hx0n, hx0s, c0, a0, rest0, hc0, hca0, hcv0, rfl⟩
  · simp only [↓reduceIte, error.truncated, bind_ok, decide_true]
    apply UPost.err (e := .Sys .TruncatedMessage) (e' := .truncatedMessage) _ trivial
    simp only [List.length_nil, ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
  simp only [hx0n, decide_false, Bool.false_eq_true, ↓reduceIte, List.length_cons, Nat.add_one_ne_zero,
    ndE_pure_bind, List.getElem?_cons_zero, Fl4Spec.the]
  obtain ⟨nt, us, idx, dep, off, win, rest, rfl⟩ : ∃ nt us idx dep off win rest,
      args = nt :: us :: idx :: dep :: off :: win :: rest := by
    match args with
    | nt :: us :: idx :: dep :: off :: win :: rest => exact ⟨nt, us, idx, dep, off, win, rest, rfl⟩
    | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] => exfalso; simp at hlen; scalar_tac
  simp only [hct, hargs 0#u64 nt (by simp), hargs 1#u64 us (by simp), hargs 2#u64 idx (by simp),
    hargs 3#u64 dep (by simp), hargs 4#u64 off (by simp), hargs 5#u64 win (by simp), bind_ok,
    List.map_cons, List.getElem?_cons_zero, List.getElem?_cons_succ, Fl4Spec.the]
  simp only [Fl4Spec.NonDetE.returnOk, ndE_pure_bind, Fl4Spec.dataToNat, Fl4Spec.unat, UScalar.bv_toNat]
  have hd := dataToObjType_run nt.bv σ
  have hcollapse (m k : Result (core.result.Result Unit error.Exc × S × A)) :
      (if nt ≥ 14#u64 then if nt < 19#u64 then (do
          let i ← arI.virtualization ar
          if i = 0#u64 then m else k) else k else k) = k := by
    by_cases hg : nt ≥ 14#u64
    · by_cases hl19 : nt < 19#u64
      · obtain ⟨v, hv, hv0⟩ := hGate hl (by simp) hx0n nt rfl (by scalar_tac) (by scalar_tac)
        simp only [hg, hl19, ↓reduceIte, hv, bind_ok, hv0]
      · simp only [hg, hl19, ↓reduceIte]
    · simp only [hg, ↓reduceIte]
  simp only [fl4_abi.consts.object.X86Vcpu, fl4_abi.consts.object.Count]
  rw [hcollapse]
  rw [retype_size_cases]
  simp only [bind_ok]
  by_cases h14 : nt.val ≥ 19
  · have hn : objTypeOf nt.bv.toNat = none := (objTypeOf_none _).2 (by simpa using h14)
    rw [hn] at hd
    simp only [h14, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, core.convert.FromSame.from, bind_tc_ok]
    exact UPost.err (run_bind_error hd _) (show (0 : Nat) = (0#u64 : U64).val from rfl)
  obtain ⟨t, ht⟩ : ∃ t, objTypeOf nt.val = some t := by
    cases h : objTypeOf nt.val with
    | none => exact absurd ((objTypeOf_none _).1 h) h14
    | some t => exact ⟨t, rfl⟩
  obtain ⟨-, -, hfr, hut, hct', hsc, -⟩ := objTypeOf_fl4 ht us.val
  have hz : bitsApi t us.val = zOf nt.val us.val := hbits nt t rfl ht us.val
  rw [UScalar.bv_toNat, ht] at hd
  simp only [h14, ↓reduceIte]
  refine UPost.congr (run_bind_ok hd _) ?_
  simp only [hz]
  by_cases hsA : us.val ≥ 64 ∨ zOf nt.val us.val > 47
  · rw [if_pos hsA]; fl4_break
    refine UPost.err (e' := .rangeError 0 (BitVec.ofNat 64 47)) ?_ ⟨rfl, rfl⟩
    have : ¬ (us.val < Fl4Spec.wordBits ∧ zOf nt.val us.val ≤ Fl4Spec.untypedMaxBits) := by
      simp only [Fl4Spec.wordBits, Fl4Spec.untypedMaxBits]; omega
    simp only [this, and_self, ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
  have hsA' : us.val < Fl4Spec.wordBits ∧ zOf nt.val us.val ≤ Fl4Spec.untypedMaxBits := by
    simp only [Fl4Spec.wordBits, Fl4Spec.untypedMaxBits]; omega
  simp only [hsA, hsA', and_self, ↓reduceIte, ndE_pure_bind]
  by_cases hsB : nt.val = 4 ∧ us.val = 0
  · rw [if_pos hsB]; fl4_break
    refine UPost.err (e := .Sys (.InvalidArgument 1#u64)) (e' := .invalidArgument 1) ?_ rfl
    have : t = .capTableObject ∧ us.val = 0 := ⟨hct'.2 hsB.1, hsB.2⟩
    simp only [this, and_self, ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
  have hsB' : ¬ (t = .capTableObject ∧ us.val = 0) := fun h => hsB ⟨hct'.1 h.1, h.2⟩
  simp only [hsB, hsB', and_self, ↓reduceIte, ndE_pure_bind]
  by_cases hsC : nt.val = 0 ∧ us.val < 4
  · rw [if_pos hsC]; fl4_break
    refine UPost.err (e := .Sys (.InvalidArgument 1#u64)) (e' := .invalidArgument 1) ?_ rfl
    have : t = .untyped ∧ us.val < Fl4Spec.untypedMinBits := ⟨hut.2 hsC.1, hsC.2⟩
    simp only [this, and_self, ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
  have hsC' : ¬ (t = .untyped ∧ us.val < Fl4Spec.untypedMinBits) := fun h => hsC ⟨hut.1 h.1, h.2⟩
  simp only [hsC, hsC', and_self, ↓reduceIte, ndE_pure_bind]
  by_cases hsD : nt.val = 5 ∧ us.val < 7
  · rw [if_pos hsD]; fl4_break
    refine UPost.err (e := .Sys (.InvalidArgument 1#u64)) (e' := .invalidArgument 1) ?_ rfl
    have : t = .schedContextObject ∧ us.val < Fl4Spec.minSchedContextBits := ⟨hsc.2 hsD.1, hsD.2⟩
    simp only [this, and_self, ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
  have hsD' : ¬ (t = .schedContextObject ∧ us.val < Fl4Spec.minSchedContextBits) := fun h => hsD ⟨hsc.1 h.1, h.2⟩
  simp only [hsD, hsD', and_self, ↓reduceIte, ndE_pure_bind, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  -- the node cap
  have hnode : (∃ e e', untyped.retype_dest st s x0 idx dep off win = ok (.Err e) ∧
      (if dep.val = 0 then pure a0 else do
          let nodeSlot ← Fl4Spec.lookupTargetSlot a0 (Fl4Spec.dataToCptr idx.bv) dep.val
          Fl4Spec.NonDetE.liftE (Fl4Spec.getCap nodeSlot) : Fl4Spec.SEMonad Unit Fl4Spec.Cap).run σ =
        ({(.error e', σ)}, False) ∧ SysErrRel e e') ∨
      (∃ nc, CapWf nc ∧ CapValid th nc ∧ (∃ y, IsSlot th y ∧ capAt (L.mem s) y = ok nc) ∧
        untyped.retype_dest st s x0 idx dep off win = ok (tailOf dep off win nc) ∧
      (if dep.val = 0 then pure a0 else do
          let nodeSlot ← Fl4Spec.lookupTargetSlot a0 (Fl4Spec.dataToCptr idx.bv) dep.val
          Fl4Spec.NonDetE.liftE (Fl4Spec.getCap nodeSlot) : Fl4Spec.SEMonad Unit Fl4Spec.Cap).run σ =
        ({(.ok (absCap nc), σ)}, False)) := by
    by_cases h0 : dep = 0#u64
    · subst h0
      refine Or.inr ⟨c0, hca0.1, hcv0, ⟨x0, hx0s, hc0⟩, retype_dest_zero s x0 idx off win c0 hc0 hca0.1, ?_⟩
      simp only [show (0#u64 : U64).val = 0 from rfl, ↓reduceIte, ← hca0.abs]; rfl
    have h0' : dep.val ≠ 0 := fun h => h0 (UScalar.eq_of_val_eq h)
    simp only [h0', ↓reduceIte]
    obtain ⟨r, hr, e1, he1, hrel⟩ := spec_exists
      (lookup_slot_for_cnode_op_refines (Z := Unit) th s σ hR hV false c0 a0 hca0 hcv0 idx dep)
    have hl' : cspace.lookup_target_slot st s c0 idx dep = ok r := hr
    have hlt : (Fl4Spec.lookupTargetSlot (Z := Unit) a0 (Fl4Spec.dataToCptr idx.bv) dep.val).run σ =
        ({(e1, σ)}, False) := he1
    cases r with
    | Err e =>
      cases e1 with
      | ok _ => exact hrel.elim
      | error e' =>
        exact Or.inl ⟨e, e', retype_dest_err s x0 idx dep off win h0 c0 hc0 e hl', run_bind_error hlt _, hrel⟩
    | Ok v =>
      cases e1 with
      | error _ => exact hrel.elim
      | ok sl' =>
        obtain ⟨rfl, pp, hpp1, hpp, -⟩ := hrel
        obtain ⟨c', a', hc', hca', hg⟩ := hR.slot_cap hpp1 hpp
        have hcv' : CapValid th c' := hV.abs ⟨pp, hpp1, Or.inl hpp⟩ hc'
        refine Or.inr ⟨c', hca'.1, hcv', ⟨_, AbsSlot.isSlot ⟨pp, hpp1, Or.inl hpp⟩, hc'⟩,
          retype_dest_ok s x0 idx dep off win h0 c0 hc0 _ hl' c' hc' hca'.1, ?_⟩
        rw [run_bind_ok hlt, run_liftE hg, ← hca'.abs]
  rcases hnode with ⟨e, e', hrd, hsn, hrel⟩ | ⟨nc, hncw, hncv, hncy, hrd, hsn⟩
  · rw [hrd]; fl4_break
    exact UPost.err (run_bind_error hsn _) hrel
  rw [hrd]
  refine UPost.congr (run_bind_ok hsn _) ?_
  simp only [bind_ok]
  by_cases hcn : ∃ ptr r gs g, nc = .CNode ptr r gs g
  swap
  · have ht' : tailOf dep off win nc = .Err (.Sys (.FailedLookup false (.MissingCapability dep))) := by
      cases nc <;> first | rfl | exact absurd ⟨_, _, _, _, rfl⟩ hcn
    have hi : Fl4Spec.isCnodeCap (absCap nc) = false := by
      cases nc <;> first | rfl | exact absurd ⟨_, _, _, _, rfl⟩ hcn
    rw [ht']; fl4_break
    refine UPost.err (e' := .failedLookup false (.missingCapability dep.val)) ?_ ⟨rfl, rfl⟩
    simp only [hi, Bool.false_eq_true, ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
  obtain ⟨ptr, r, gs, g, rfl⟩ := hcn
  have hr64 : r.val < 64 := hncw.1
  obtain ⟨hthp, hr0⟩ := hncv
  have hpow : 2 ^ r.val < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hr64
  have hpow1 : 1 ≤ 2 ^ r.val := Nat.one_le_two_pow
  rw [show absCap (.CNode ptr r gs g) = .cnodeCap ptr.bv r.val (bitsOf g.val gs.val) from rfl]
  simp only [Fl4Spec.isCnodeCap, ↓reduceIte, Fl4Spec.bitsOf, Fl4Spec.objRefOf, tailOf, destRes, ndE_pure_bind,
    hfan]
  by_cases e1 : off.val > 2 ^ r.val - 1
  · rw [if_pos e1]; fl4_break
    refine UPost.err (e' := .rangeError 0 (BitVec.ofNat 64 (2 ^ r.val - 1))) ?_ ⟨rfl, rfl⟩
    simp only [e1, or_true, ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
  have e1' : ¬ (off.val < 0 ∨ off.val > 2 ^ r.val - 1) := by omega
  simp only [e1', ↓reduceIte, ndE_pure_bind]; rw [if_neg e1]
  have h256 : Fl4Spec.unat (256#64 : BitVec 64) = 256 := rfl
  by_cases e2 : win.val < 1 ∨ win.val > 256
  · rw [if_pos e2]; fl4_break
    refine UPost.err (e' := .rangeError 1 256#64) ?_ ⟨rfl, rfl⟩
    simp only [h256, e2, ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
  simp only [h256, e2, ↓reduceIte, ndE_pure_bind]
  by_cases e3 : win.val > 2 ^ r.val - off.val
  · rw [if_pos e3]; fl4_break
    refine UPost.err (e' := .rangeError 1 (BitVec.ofNat 64 (2 ^ r.val - off.val))) ?_ ⟨rfl, rfl⟩
    simp only [e3, or_true, ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
  have e3' : ¬ (win.val < 1 ∨ win.val > 2 ^ r.val - off.val) := by omega
  simp only [e3', ↓reduceIte, ndE_pure_bind]; rw [if_neg e3]; simp only [bind_ok]
  -- the window is empty
  have hw1 : 1 ≤ win.val ∧ win.val ≤ 256 := by omega
  have hwin : off.val + win.val ≤ 2 ^ r.val := by omega
  have hsum : (core.num.U64.wrapping_add off win).val = off.val + win.val := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
  simp only [lift, bind_ok]
  simp only [ensure_empty_slots_eq s ptr off _ (show off.val ≤ (core.num.U64.wrapping_add off win).val by omega), hsum,
    bind_ok]
  have hsl2 : List.map (fun cref => (ptr.bv, cref)) (List.map (Fl4Spec.natToCref r.val)
      (List.range' off.val (off.val + win.val - off.val))) = windowSlots ptr r.val off.val win.val := by
    simp [windowSlots, List.map_map]
  simp only [hsl2]
  have hwe := window_empty_run th s σ hR ptr r.val hr64 hthp off.val win.val hwin
  by_cases hemp : ∀ i : Nat, off.val ≤ i → i < off.val + win.val →
      capAt (L.mem s) (slotAddr ptr.bv (BitVec.ofNat 64 i)) = ok .Null
  swap
  · rw [if_neg hemp] at hwe; simp only [hemp, ↓reduceIte]; fl4_break
    exact UPost.err (run_bind_error hwe _) trivial
  rw [if_pos hemp] at hwe; rw [if_pos hemp]
  refine UPost.congr (run_bind_ok hwe _) ?_
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, untyped.as_untyped]
  -- reset: no children
  have hnc : NoChildrenRel (st := st) s σ slot sl := by
    subst hsl
    exact noChildren_of_adj th hP s σ G hM hC (hI.parentAdj (th := th)) sl hAs
      ((hM.members _).2 ⟨hAs.isSlot, _, hcap, by simp⟩)
  unfold NoChildrenRel at hnc
  have hres := constOnFailure_run σ sl
  simp only [Fl4Spec.NonDetE.returnOk] at hres
  refine UPost.congr (run_bind_ok (run_liftE hres) _) ?_
  rw [hnc]; simp only [bind_ok]
  by_cases hch : ∃ x, σ.cdt x = some sl
  case' pos =>
    rw [if_pos hch]; dsimp only
    rw [show ((fi, false) : U64 × Bool) = (if (∃ x, σ.cdt x = some sl) then fi else 0#u64,
      decide (¬ ∃ x, σ.cdt x = some sl)) by simp [hch]]
  case' neg =>
    rw [if_neg hch]; dsimp only
    rw [show ((0#u64, true) : U64 × Bool) = (if (∃ x, σ.cdt x = some sl) then fi else 0#u64,
      decide (¬ ∃ x, σ.cdt x = some sl)) by simp [hch]]
  all_goals clear hch
  all_goals
    generalize hRv : decide (¬ ∃ x, σ.cdt x = some sl) = R
    obtain ⟨fiv, hfiv⟩ : ∃ fiv, fiv = (if (∃ x, σ.cdt x = some sl) then fi else 0#u64) := ⟨_, rfl⟩
    rw [← hfiv]
    have hfiv' : fiv = if R then 0#u64 else fi := by
      rw [hfiv, ← hRv]; by_cases h : ∃ x, σ.cdt x = some sl <;> simp [h]
    clear hfiv
    simp only [bind_ok, uncurry_apply_pair]
    have hsb : sb.val < 64 := capAt_untyped_inv hcap
    have hfivv : fiv.val = if R then 0 else fi.val := by rw [hfiv']; cases R <;> rfl
    have hspec_fi : (if R = true then 0 else Fl4Spec.freeIndexOf (Fl4Spec.Cap.untypedCap dev p.bv sb.val fi.val)) =
        fiv.val := by rw [hfivv]; cases R <;> rfl
    have hfb : BitVec.ofNat 64 fiv.val = fiv.bv := (bv_eq_ofNat fiv).symm
    simp only [hspec_fi, objSize_untyped, Fl4Spec.getFreeRef, hfb]
    have h63 : (sb &&& 63#u64).val = sb.val := by
      have : (sb &&& 63#u64).val = sb.val % 64 := by simp; exact Nat.and_two_pow_sub_one_eq_mod sb.val 6
      omega
    have hz47 : zOf nt.val us.val ≤ 47 := by omega
    have hzv : (⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64).val = zOf nt.val us.val := by
      show (BitVec.ofNat 64 (zOf nt.val us.val)).toNat = _
      simp; omega
    have hz63 : ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64).val = zOf nt.val us.val := by
      have : ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64).val =
          (⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64).val % 64 := by
        simp only [UScalar.val_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 6
      omega
    step as ⟨i2, hi2a, hi2b⟩
    have hp64 : 2 ^ sb.val < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hsb
    have hi2v : i2.val = 2 ^ sb.val := by
      rw [hi2a, h63, Nat.one_shiftLeft]; simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
    have hi2 : i2.bv = 1#64 <<< sb.val := by
      apply BitVec.eq_of_toNat_eq
      show i2.val = _
      rw [hi2v]; simp [Nat.shiftLeft_eq]; omega
    step as ⟨i4, hi4a, hi4b⟩
    have hFB : (core.num.U64.wrapping_sub i2 fiv).bv = 1#64 <<< sb.val - fiv.bv := by
      rw [core.num.U64.wrapping_sub_bv_eq, hi2]
    have hi4 : i4.val = (1#64 <<< sb.val - fiv.bv).toNat >>> zOf nt.val us.val := by
      first | (rw [hi4b, hz63, ← hFB]; rfl) | (rw [hi4a, hz63, ← hFB]; rfl)
    by_cases hm : i4 < win
    · rw [if_pos hm]
      refine UPost.err (e' := .notEnoughMemory (1#64 <<< sb.val - fiv.bv)) ?_ hFB.symm
      have : ((1#64 <<< sb.val - fiv.bv) >>> zOf nt.val us.val).toNat < win.val := by
        simp only [BitVec.toNat_ushiftRight]; rw [← hi4]; exact hm
      simp only [this, ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
    rw [if_neg hm]
    have hm' : ¬ ((1#64 <<< sb.val - fiv.bv) >>> zOf nt.val us.val).toNat < win.val := by
      simp only [BitVec.toNat_ushiftRight]; rw [← hi4]; exact hm
    simp only [hm', ↓reduceIte, ndE_pure_bind]
    have h64 : ¬ (⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) ≥ 64#u64 := by
      intro h; have : (⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64).val ≥ 64 := h; omega
    rw [if_neg h64]
    have hal : untyped.align_up (core.num.U64.wrapping_add p fiv) ⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ =
        ok ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ := by
      rw [align_up_eq _ _ (by omega), hzv, core.num.U64.wrapping_add_bv_eq]
    have hctx : ∀ (hdev : dev = true → Fl4Spec.isFrameType t = true ∨ t = .untyped),
        RetCtx (L := L) th s σ sl sb fi dev nt us ptr off win t r.val R fiv :=
      fun hdev => ⟨ht, ⟨by omega, hz47, hsB, hsC, hsD⟩, ⟨hthp, hr64, hr0, let ⟨y, hy, hcy⟩ := hncy; ⟨y, r, gs, g, hy, hcy⟩⟩, ⟨hw1.1, hw1.2, hwin⟩, hemp,
        hRv.symm, hfiv', hsb, by rw [← hi4]; have : ¬ i4.val < win.val := hm; omega, hdev⟩
    have hsucc : ∀ (hdev : dev = true → Fl4Spec.isFrameType t = true ∨ t = .untyped),
        (do
          let aligned ← untyped.align_up (core.num.U64.wrapping_add p fiv) ⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩
          let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
          untyped.retype st arI s2 ar slot R aligned nt us ptr off win dev) ⦃ res =>
        UPost σ (pure (Fl4Spec.UntypedInvocation.retype sl R p.bv (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
          t us.val (windowSlots ptr r.val off.val win.val) dev)) s ar Q res ⦄ := by
      intro hdev
      rw [hal, bind_ok]
      exact WP.spec_mono (hQ nt us ptr off win t r.val R fiv rfl (hctx hdev)) (fun res h => Or.inr ⟨_, rfl, h⟩)
    simp only [ndE_exceptT_pure_bind]
    cases dev
    · rw [if_neg (by simp)]
      refine UPost.congr ?_ (hsucc (by simp))
      simp only [Bool.false_eq_true, false_and, ↓reduceIte, ndE_exceptT_pure_bind]; rfl
    rw [if_pos rfl, is_frame_type_eq, bind_ok]
    by_cases hfrm : nt.val = 9 ∨ nt.val = 10 ∨ nt.val = 11
    · rw [if_pos (by simpa using hfrm)]
      refine UPost.congr ?_ (hsucc (fun _ => Or.inl (hfr.2 hfrm)))
      simp only [hfr.2 hfrm, not_true_eq_false, false_and, and_false, ↓reduceIte, ndE_exceptT_pure_bind]; rfl
    rw [if_neg (by simpa using hfrm)]
    have hnf : ¬ Fl4Spec.isFrameType t = true := fun h => hfrm (hfr.1 h)
    by_cases hu : nt.val = 0
    · have : (nt != fl4_abi.consts.object.Untyped) = false := by
        simp only [fl4_abi.consts.object.Untyped, bne_eq_false_iff_eq]; exact UScalar.eq_of_val_eq hu
      rw [this, if_neg (by simp)]
      refine UPost.congr ?_ (hsucc (fun _ => Or.inr (hut.2 hu)))
      simp only [hut.2 hu, ne_eq, not_true_eq_false, and_false, ↓reduceIte, ndE_exceptT_pure_bind]; rfl
    · have : (nt != fl4_abi.consts.object.Untyped) = true := by
        simp only [fl4_abi.consts.object.Untyped, bne_iff_ne, ne_eq]
        intro h; exact hu (by rw [h]; rfl)
      rw [this, if_pos rfl]
      simp only [error.invalid_arg, bind_ok]
      refine UPost.err (e := .Sys (.InvalidArgument 1#u64)) (e' := .invalidArgument 1) ?_ rfl
      have : ¬ t = .untyped := fun h => hu (hut.1 h)
      simp only [hnf, this, ne_eq, true_and, Bool.false_eq_true, not_false_eq_true, and_self, ↓reduceIte,
        Fl4Spec.NonDetE.throwError, ndE_throw_bind]
      rfl



/-- **`untyped_decode_refines_fl4` with the VT-x gate open** (module docstring): every type number. -/
theorem untyped_decode_refines_fl4V [Fl4Proofs.P1.PlainStore st] {A : Type} (arI : machine.Arch A) (th : TypedHeap) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .untypedRetype ↔ lbl = fl4_abi.label.UntypedRetype)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (slot : obj.Slot) (sl : Fl4Spec.CslotPtr) (hsl : slot = cslotAddr sl) (hAs : AbsSlot th sl)
    (p sb fi : U64) (dev : Bool) (hcap : capAt (L.mem s) slot = ok (.Untyped p sb fi dev))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List Fl4Spec.Cap) (hex : ExtraRel th (L.mem s) x0 excaps)
    (hGate : lbl = fl4_abi.label.UntypedRetype → 6 ≤ args.length → x0 ≠ 0#u64 →
      ∀ x, args.head? = some x → 14 ≤ x.val → x.val < 19 → ∃ v, arI.virtualization ar = ok v ∧ v ≠ 0#u64)
    (hfan : Fl4Spec.retypeFanOutLimit = 256#64)
    (Q : Fl4Spec.UntypedInvocation → core.result.Result Unit error.Exc × S × A → Prop)
    (hQ : ∀ (nt us dest off win : U64) (t : Fl4Spec.ApiObjectType) (r : Nat) (reset : Bool) (fiv : U64),
      args.head? = some nt → RetCtx (L := L) th s σ sl sb fi dev nt us dest off win t r reset fiv →
      (do
        let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
        untyped.retype st arI s2 ar slot reset ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ nt us dest off win
          dev) ⦃ res =>
        Q (.retype sl reset p.bv (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val
          (windowSlots dest r off.val win.val) dev) res ⦄) :
    untyped.decode st arI s ar lbl length slot (.Untyped p sb fi dev) buf extra ⦃ res =>
      UPost σ (Fl4Spec.fl4DecodeUntypedInvocation slbl (args.map UScalar.bv) sl (absCap (.Untyped p sb fi dev)) excaps)
        s ar Q res ⦄ :=
  untyped_decode_refines_withV Fl4Spec.fl4ObjBitsApi arI th s ar σ G hR hV hP hM hC hI lbl slbl hlbl length buf ct hct
    args hlen hargs (fun _ _ _ ht n => (objTypeOf_fl4 ht n).2.1) slot sl hsl hAs p sb fi dev hcap extra x0 hx0 excaps
    hex hGate hfan Q hQ

end

end
end Fl4Proofs.P3
