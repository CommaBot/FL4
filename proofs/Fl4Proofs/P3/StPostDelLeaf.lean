/-
P3 (line stpost, generation 9): **CNode Delete of the plan's small frame at stable ghosts**
(the leaf that lets StPostInvTop's route cover every label `localinv.plan` accepts).

fl4-sync's plan for `CNodeDelete` (`localinv.plan_with`) requires that the target slot (named by the
first two message registers through the invoked CNode cap) holds a small RAM frame cap. Deleting a frame
cap (`cdt::delete … exposed = true`) reaches no preemption point: `finalise_slot_immediate`'s first round
finalises the cap to a null remainder (`finalise_cap_object`'s `Frame` arm), which is removable, so it
returns at once and `delete` empties the slot and returns `Ok`.

* `finObj_frame_null`, `finCap_frame_null`: a frame cap's finalisation leaves no remainder (partial: at
  every `ok` outcome).
* `finImm_frame`, **`delete_frame_ok`**: `finalise_slot_immediate` on a slot holding a frame cap returns
  `Ok` at its first round, so `delete` returns `Ok ()`.
* **`cnode_delete_frame_noPre`**: FL4's CNode decode at `CNodeDelete` whose target holds a frame cap is
  never preempted (the target is a slot of the typed heap by `lookup_slot_for_cnode_op_refines`, so
  `set_thread_state Restart` keeps its cap: `set_thread_state_slots`).
* `cn_del_topJStM`: XTopJointKEntry38's `cn_del_topJLMM` at `X := JStabM Z H Cs`, `XP := False`, given
  the outcome is not preempted: the deletion loop's invariant `EJLM` is at `Z.mv G V`, `H`, `Cs`.
* **`decode_cnodeDeleteJSt`**: a CNode cap at `CNodeDelete` whose target holds a frame cap:
  `decode_invocation_cnode_deleteJLMM`'s route (`cnode_delete_refinesW` at `EJLM`, `JDelHypLM` from
  `JDelParts`, here built from `ArchRefines` / `ARKeep` / the tick facts as `JDelPartsN32.toN.toJ`)
  with `cn_del_topJStM`, the preempted case refuted by `cnode_delete_frame_noPre` (`spec_and_eq`).

No premise added (the platform facts read are among U29's).
-/
import Fl4Proofs.P3.StPostInvLeaf
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section StDelFrame
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- (stpost) A frame cap's finalisation leaves no remainder. -/
theorem finObj_frame_null {s : S} {a : A} {p0 : U64} {sz : capability.FrameSize} {rt : U64}
    {dv mp ep : Bool} {asid va : U64} {fin : Bool} {y : (capability.Cap × capability.Cap) × S × A}
    (h : objects.finalise_cap_object st arI s a (.Frame p0 sz rt dv mp ep asid va) fin = ok y) :
    y.1.1 = .Null := by
  simp only [objects.finalise_cap_object] at h
  obtain ⟨⟨s1, a1⟩, -, h⟩ := P1.bind_eq_ok h
  try dsimp only at h
  repeat' split at h
  all_goals first
    | (cases P1.ok_inj_ff h; rfl)
    | (obtain ⟨a2, -, h⟩ := P1.bind_eq_ok h; cases P1.ok_inj_ff h; rfl)

/-- (stpost) `finalise_cap` of a frame cap leaves no remainder. -/
theorem finCap_frame_null {s : S} {a : A} {p0 : U64} {sz : capability.FrameSize} {rt : U64}
    {dv mp ep : Bool} {asid va : U64} {fin : Bool} {y : (capability.Cap × capability.Cap) × S × A}
    (h : objects.finalise_cap st arI s a (.Frame p0 sz rt dv mp ep asid va) fin false = ok y) :
    y.1.1 = .Null := by
  unfold objects.finalise_cap at h
  simp only [bind_ok] at h
  exact finObj_frame_null arI (s := s) (a := a) (p0 := p0) (sz := sz) (rt := rt) (dv := dv) (mp := mp) (ep := ep)
    (asid := asid) (va := va) (fin := fin) h

set_option maxHeartbeats 4000000 in
/-- (stpost) **`finalise_slot_immediate` on a frame cap returns at its first round** (the remainder is
null, so removable): never preempted. -/
theorem finImm_frame {s : S} {a : A} {slot : obj.Slot} {p0 : U64} {sz : capability.FrameSize} {rt : U64}
    {dv mp ep : Bool} {asid va : U64}
    (hc : capAt (L.mem s) slot = ok (.Frame p0 sz rt dv mp ep asid va))
    {y : core.result.Result cdt.Finalised error.Exc × S × A}
    (h : cdt.finalise_slot_immediate st arI s a slot = ok y) : ∃ f, y.1 = .Ok f := by
  unfold cdt.finalise_slot_immediate cdt.finalise_slot_immediate_loop at h
  rw [loop] at h
  obtain ⟨cf, hb, h⟩ := P1.bind_eq_ok h
  have hf : layout.WALK_FUEL > 0#u64 := by simp [layout.WALK_FUEL, U64.rMax]
  obtain ⟨v, hv, -⟩ := spec_exists (U64.sub_spec (x := layout.WALK_FUEL) (y := 1#u64)
    (by simp [layout.WALK_FUEL, U64.rMax]))
  unfold cdt.finalise_slot_immediate_loop.body at hb
  have hcn : capability.Cap.Frame p0 sz rt dv mp ep asid va ≠ .Null := by simp
  simp only [hf, ↓reduceIte, hv, bind_ok, slot_cap_eq, hc, cap_is_null_ne hcn, Bool.false_eq_true] at hb
  rw [is_final_with_cap_eq _ _ _ hc] at hb
  obtain ⟨fin, -, hb⟩ := P1.bind_eq_ok hb
  obtain ⟨⟨⟨rem, cl⟩, s1, a1⟩, hfc, -⟩ := P1.bind_eq_ok hb
  have hrem := finCap_frame_null arI hfc
  simp only at hrem
  subst hrem
  rw [hfc] at hb
  simp only [cdt.cap_removable, bind_ok, ↓reduceIte, uncurry_apply_pair] at hb
  cases P1.ok_inj_ff hb
  try dsimp only at h
  cases P1.ok_inj_ff h
  exact ⟨_, rfl⟩

/-- (stpost) **Deleting (`exposed`) a slot that holds a frame cap returns `Ok`.** -/
theorem delete_frame_ok {s : S} {a : A} {slot : obj.Slot} {p0 : U64} {sz : capability.FrameSize} {rt : U64}
    {dv mp ep : Bool} {asid va : U64}
    (hc : capAt (L.mem s) slot = ok (.Frame p0 sz rt dv mp ep asid va))
    {y : core.result.Result Unit error.Exc × S × A}
    (h : cdt.delete st arI s a slot true = ok y) : y.1 = .Ok () := by
  unfold cdt.delete at h
  simp only [↓reduceIte] at h
  obtain ⟨⟨r, s1, a1⟩, hf, h⟩ := P1.bind_eq_ok h
  obtain ⟨f, hrf⟩ := finImm_frame arI hc hf
  simp only at hrf
  subst hrf
  obtain ⟨cf, ecf, h⟩ := P1.bind_eq_ok h
  simp only [core.result.Result.Insts.CoreOpsTry.branch] at ecf
  cases P1.ok_inj_ff ecf
  try dsimp only at h
  obtain ⟨⟨s2, a2⟩, -, h⟩ := P1.bind_eq_ok h
  cases P1.ok_inj_ff h
  rfl

set_option maxHeartbeats 8000000 in
/-- (stpost) **CNode Delete of a target holding a frame cap is never preempted** (partial: every `ok`
outcome of FL4's decode). -/
theorem cnode_delete_frame_noPre [Fl4Proofs.P1.PlainStore st] (th : TypedHeap) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct)
    (cap : capability.Cap) (a : Fl4Spec.Cap) (hca : CapRel cap a) (hcv : CapValid th cap)
    (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION)) (htcb : th ct = some .tcb)
    (hfr : ∀ y0 y1, msg.syscall_arg st s ct buf 0#u64 = ok y0 → msg.syscall_arg st s ct buf 1#u64 = ok y1 →
      ∃ dest, cspace.lookup_target_slot st s cap y0 y1 = ok (.Ok dest) ∧
        ∃ p0 sz rt dv mp ep asid va, obj.Slot.cap st dest s = ok (.Frame p0 sz rt dv mp ep asid va)) :
    ∀ x, cnode.decode st arI s ar fl4_abi.label.CNodeDelete length cap buf extra = ok x →
      x.1 ≠ .Err .Preempted := by
  intro x h
  unfold cnode.decode at h
  have n1 : ¬ fl4_abi.label.CNodeDelete < fl4_abi.label.CNodeRevoke := by
    have := lbl_revoke_val; have := lbl_delete_val; scalar_tac
  have n2 : ¬ fl4_abi.label.CNodeDelete > fl4_abi.label.CNodeRotate := by
    have := lbl_delete_val; have := lbl_rotate_val; scalar_tac
  rw [if_neg n1, if_neg n2] at h
  by_cases h2 : length < 2#u64
  · rw [if_pos h2] at h
    simp only [error.truncated, bind_ok] at h
    cases P1.ok_inj_ff h
    intro e; cases e
  rw [if_neg h2, hct] at h
  simp only [bind_ok] at h
  obtain ⟨y0, e0, h⟩ := P1.bind_eq_ok h
  obtain ⟨y1, e1, h⟩ := P1.bind_eq_ok h
  obtain ⟨dest, hl, p0, sz, rt, dv, mp, ep, asid, va, hfc⟩ := hfr y0 y1 e0 e1
  rw [hl] at h
  have g1 : ¬ fl4_abi.label.CNodeDelete ≥ fl4_abi.label.CNodeCopy := by
    have := lbl_copy_val; have := lbl_delete_val; scalar_tac
  have k1 : ¬ fl4_abi.label.CNodeDelete = fl4_abi.label.CNodeRevoke := by rw [u64_eq_iff]; simp
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, g1, k1, ↓reduceIte] at h
  -- the target is a slot of the typed heap
  unfold cspace.lookup_target_slot at hl
  obtain ⟨r1, hr1, e1', he1, hrel1⟩ := spec_exists
    (lookup_slot_for_cnode_op_refines (Z := Unit) th s σ hR hV false cap a hca hcv y0 y1)
  rw [hl] at hr1
  cases P1.ok_inj_ff hr1
  cases e1' with
  | error _ => exact hrel1.elim
  | ok dsl =>
    obtain ⟨rfl, pd, hpd1, hpd, -⟩ := hrel1
    have hAd : AbsSlot th dsl := ⟨pd, hpd1, Or.inl hpd⟩
    obtain ⟨s2, hs2, hS⟩ := spec_exists (set_thread_state_slots th hP s ct sched.TS_RESTART htcb hact)
    rw [hs2] at h
    simp only [bind_ok] at h
    have hc2 : capAt (L.mem s2) (cslotAddr dsl) = ok (.Frame p0 sz rt dv mp ep asid va) := by
      rw [hS.capAt hAd.isSlot, ← slot_cap_eq, hfc]
    rw [delete_frame_ok arI hc2 h]
    intro e; cases e

end StDelFrame

section StDelLeaf
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- (stpost) **A Delete's outcome at `EJL`, stable ghosts, given it is not preempted**
(`cn_del_topJLMM` with `X := JStabM Z H Cs`, `XP := False`). -/
theorem cn_del_topJStM {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    [VxE Z] (hR : MR ar σ.machineState)
    {kb : U64} {K : Nat} {blk call don : Bool}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.CnodeInvocation} {res : core.result.Result Unit error.Exc × S × A}
    (hq : PInvPostW (L := L) Z.th σ Z.G m (EJLM (L := L) arI AR MR Z H Cs kb K) (EJPM (L := L) arI AR MR Z H Cs kb K)
      s ar res)
    (hnp : res.1 ≠ .Err .Preempted) :
    TopPostDMXP (L := L) (JStabM (L := L) arI AR MR Z H Cs) (fun _ _ _ => False) σ blk call don
      (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeCNode m) s res := by
  obtain ⟨r, s', a'⟩ := res
  rcases hq with ⟨e, rfl, rfl, rfl, e', h1, h2⟩ |
    ⟨inv, hrun, σ1, hst, σ', G', hcase, hCR', hFI', -, hE'⟩
  · have hne : e ≠ .Preempted := by rintro rfl; cases e' <;> exact h2.elim
    refine Or.inl ⟨e, rfl, rfl, ⟨e', run_liftME_err h1, Or.inl h2⟩, ?_⟩
    simp only [core.result.Result.Err.injEq, hne, if_false]
    exact ⟨J.stab, hR⟩
  · rcases hcase with ⟨rfl, hx⟩ | ⟨rfl, -⟩
    · obtain ⟨-, ⟨⟨V, Ac', Lst', D', J', -⟩, -⟩, hmv'⟩ := hE'
      have hX' := J'.xtop
      refine Or.inr ⟨_, DecOut.of_eq (run_liftME_ok hrun), σ1, hst, (.ok [], σ'),
        mem_bindE_ok hx (Set.mem_singleton _), ⟨Z.th, G', Or.inl ⟨rfl, rfl⟩, hX'.rel.1, hX'.rel.2.1,
          hX'.rel.2.2.1, hX'.rel.2.2.2.1, hX'.rel.2.2.2.2.1⟩, ?_⟩
      simp only [reduceCtorEq, if_false]
      exact ⟨⟨G', V, Ac', Lst', D', J'⟩, hmv'.1⟩
    · exact absurd rfl hnp

set_option maxHeartbeats 8000000 in
/-- (stpost) **A CNode cap at `CNodeDelete` whose target holds a frame cap, stable ghosts, `MR` after**:
`decode_invocation_cnode_deleteJLMM`'s route (`cnode_delete_refinesW` at `EJLM`) with the outcome by
`cn_del_topJStM`, the preempted case refuted by `cnode_delete_frame_noPre`. -/
theorem decode_cnodeDeleteJSt [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z] (hni : Entered σ)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI) (hRef : ArchRefines arI AR)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hnd : Fl4Spec.numDomains = 1) (hMP : MachPlat arI MR) (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR)
    (hmv : MRV MR ar σ) (hsg : SpecGlob σ)
    (hRd0 : σ.consumedTime = 0 → ∀ y n, σ.kheap σ.curSc = some (.schedContext y n) → Fl4Spec.scActive y = true →
      Fl4Spec.refillReady σ.curTime (Fl4Spec.refillHd y) = true)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl) (p r gs g : U64)
    (hsc : capV (L.mem s) (cslotAddr sl) = .CNode p r gs g)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hfr : ∀ y0 y1, msg.syscall_arg st s ct buf 0#u64 = ok y0 → msg.syscall_arg st s ct buf 1#u64 = ok y1 →
      ∃ dest, cspace.lookup_target_slot st s (.CNode p r gs g) y0 y1 = ok (.Ok dest) ∧
        ∃ p0 sz rt dv mp ep asid va, obj.Slot.cap st dest s = ok (.Frame p0 sz rt dv mp ep asid va)) :
    XCapP (L := L) arI (JStabM (L := L) arI AR MR Z H Cs) (fun _ _ _ => False) s ar σ fl4_abi.label.CNodeDelete
      length (cslotAddr sl) (.CNode p r gs g) blk call don fp buf extra fl4_abi.label.CNodeDelete.bv
      (args.map UScalar.bv) ci sl excaps buffer ct := by
  obtain ⟨sl', hl', hd⟩ := cnode_canon fl4_abi.label.CNodeDelete
  have hlbl : Fl4Spec.genInvocationType sl' = .cnodeDelete := by rw [hl']; simp [cnodeLabelOf]
  refine XCapP.lbl_congr arI (specDec_cnode p r gs g hd) ?_
  have hX := J.xtop
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨hwf, hcv⟩ := slot_cap_wf hX hAs hsc
  have hP0 := J.ppr0_start arI hni hRd0 hnq
  have hDP : JDelParts (L := L) arI AR Z.th :=
    (JDelPartsN32.toN (L := L) (⟨hRef, hARI.toARKeep, hmax, htu⟩ : JDelPartsN32 arI AR Z.th)).toJ
  have hJD := hDP.jDelHypLM arI hT hnd hMP hKD hPA hARI.toMask
  obtain ⟨K, hK, hK6, hDE⟩ := J.delE
  obtain ⟨⟨hR, hV, hM, hCd, hI⟩, -⟩ := And.intro hX.rel.2.1 hX.rel.2.2.1
  have htcb := (hX.curTcb hcur).1
  have hP := hX.rel.1
  unfold XCapP
  left
  unfold DecOKDMXP syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact WP.spec_mono (spec_and_eq (cnode_delete_refinesW arI Z.th s ar σ Z.G hR hV hP hM hCd sl' hlbl length buf
      ct hct args hlen hargs _ _ ⟨hwf, rfl⟩ hcv extra _ hI J.kern.act hcur htcb
      (EJLM (L := L) arI AR MR Z H Cs (L.ksb s) K) (EJPM (L := L) arI AR MR Z H Cs (L.ksb s) K)
      psiD (hJD Z H Cs (L.ksb s) K rfl hK hK6) (EJLM.restart arI J hni hMP hmv hsg hP0 J.live hDE hct)
      (fun _ _ _ G1 hCR hE1 => ⟨hE1.1.2.2.1, hE1.1.2.2.2 G1 hCR.2.2.1⟩)
      (fun _ _ _ G1 hCR hE1 => ⟨hE1.1.2.2.1, hE1.1.2.2.2 G1 hCR.2.2.1⟩))
      (cnode_delete_frame_noPre arI Z.th s ar σ hR hV hP length buf ct hct _ _ ⟨hwf, rfl⟩ hcv extra J.kern.act
        htcb hfr))
      fun res ⟨h, hnp⟩ => cn_del_topJStM arI J hmv.1 h hnp
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    refine Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, ?_⟩
    show if _ = _ then _ else _
    rw [if_neg (by simp)]
    exact ⟨J.stab, hmv.1⟩

end StDelLeaf

end

end Fl4Proofs.P3
