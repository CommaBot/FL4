/-
P3 (DESIGN.md §9), VSpace: **`MakePool`'s decode with any perform**
(handoff/utj.md Round 15): VsMakePoolRel's `makepool_rel` and VsDecFrame's
`decode_invocation_asid_controlXG` with the perform after the decode checks
given as a hypothesis (`makepool_relP`, `decode_invocation_asid_controlXP`),
for the dirty case of the ASID control path at `J` (XTopJointMakePoolD),
where the perform runs from the restart's state detyped at the region.
The proofs are those of `makepool_rel` and `decode_invocation_asid_controlXG`.
-/
import Fl4Proofs.P3.VsDecFrame
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3 Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- `MpDecPost` with any post `Post` of the perform (`makepool_relP`): an error, as the spec's, the state unchanged; or one of the
spec's invocations, with no failure, performed (`MpPost`). -/
def MpDecPostP {A : Type}
    (Post : U64 → Fl4Spec.CslotPtr → Fl4Spec.CslotPtr → Fl4Spec.Asid → core.result.Result Unit error.Exc × S × A → Prop)
    (σ : Fl4Spec.State Unit) (D : Set (Except Fl4Spec.SyscallError Fl4Spec.ArchInvocation × Fl4Spec.State Unit) × Prop)
    (s : S) (a : A) (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  (∃ e e', res.1 = .Err e ∧ VsErrRel e e' ∧ D = ({(.error e', σ)}, False) ∧ res.2.1 = s ∧ res.2.2 = a) ∨
  (res.1 = .Ok () ∧ ∃ (p : U64) (dest ps : Fl4Spec.CslotPtr) (base : Fl4Spec.Asid),
    (.ok (.invokeASIDControl (.makePool p.bv dest ps base)), σ) ∈ D.1 ∧ ¬ D.2 ∧
    Post p dest ps base res)

/-- **`makepool_rel` with any perform** (`hPf`, its post `Post`; for the
dirty case of XTopJointMakePoolD): FL4's error is the spec decode's single outcome, or the
spec decodes an invocation (FL4's choice of the free table entry, the first,
among l4v's), with no failure, and `MpPost` holds. -/
theorem makepool_relP {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} {RegOK : S → Fl4Spec.State Unit → U64 → Prop}
    (hH : VsMpHyps st A th P L4 L3 L2 L1 SR RegOK)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hPl : Placed th) (hSt : StateRel th (L.mem s) σ) (hSV : SlotsValid th (L.mem s))
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hU : UtInv (L.mem s) G) (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (hS : SR s a σ) (hVP : VsPlaced P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    (hVO : ∀ b, VsWrite P (L.ksb s) b → OutsideObjects th b)
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b)
    (hPV : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : ct.bv = σ.curThread)
    {xct : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xct))
    (hrun : Fl4Spec.runnable xct.tcbState = true)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    {slbl : Fl4Spec.Data} (hl : Fl4Spec.invocationType slbl = .archInvocationLabel .x64ASIDControlMakePool)
    (length buf : U64) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (xs : Fl4Spec.CapRef) (cte : Fl4Spec.CslotPtr) (slot : obj.Slot) (call : Bool)
    (ex : Array obj.Slot 3#usize)
    {pp : U64} {rs : Nat} (hpp : th pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    (hex0 : vspace.extra ex 0#usize = ok (some (cslotAddr (pp.bv, idx))))
    {y : obj.Slot} (hex1 : vspace.extra ex 1#usize = ok (some y))
    {uc : capability.Cap} (hcx : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok uc) {uc' : Fl4Spec.Cap}
    (hur : CapRel uc uc')
    {rc : capability.Cap} (hcy : capAt (L.mem s) y = ok rc) {rc' : Fl4Spec.Cap} (hrr : CapRel rc rc')
    (hrv : CapValid th rc)
    (ysl : Fl4Spec.CslotPtr) (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    {Post : U64 → Fl4Spec.CslotPtr → Fl4Spec.CslotPtr → Fl4Spec.Asid → core.result.Result Unit error.Exc × S × A → Prop}
    (hPf : ∀ (p sb fi : U64), sb = fl4_abi.consts.bits.ASID_POOL →
      capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false) →
      (¬ ∃ sl, σ.cdt sl = some (pp.bv, idx)) →
      ∀ (pd : U64) (rd : Nat) (idxd : List Bool), th pd = some (.cnode rd) → idxd.length = rd →
      capAt (L.mem s) (cslotAddr (pd.bv, idxd)) = ok .Null → CnRef th (L.mem s) rc pd →
      ∀ (i base : U64), i.val < 2048 → base.val = i.val * 512 →
      (do
        let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
        let i1 ← lift (sb &&& 63#u64)
        let i2 ← 1#u64 <<< i1
        let s2 ← obj.Slot.set_cap st (cslotAddr (pp.bv, idx)) s1 (capability.Cap.Untyped p sb i2 false)
        let s3 ← st.clear_free s2 p 4096#u64
        let s4 ← cdt.insert st s3 (capability.Cap.AsidPool p base) (cslotAddr (pp.bv, idx)) (cslotAddr (pd.bv, idxd))
        let s5 ← vspace.set_asid_table st s4 i p
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, a)) ⦃ res =>
        res.1 = .Ok () ∧ res.2.2 = a ∧ Post p (pd.bv, idxd) (pp.bv, idx) base.bv res ⦄) :
    vspace.decode st ar s a fl4_abi.label.X86ASIDControlMakePool length slot .AsidControl call buf ex ⦃ res =>
      MpDecPostP Post σ (ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) slbl
        (args.map UScalar.bv) xs cte .asidControlCap ((uc', (pp.bv, idx)) :: (rc', ysl) :: rest)) σ) s a res ⦄ := by
  unfold vspace.decode
  rw [hct]
  apply ok_bind_spec
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [hex0, hex1]
  simp only [bind_ok]
  by_cases hl2 : length >= 2#u64
  swap
  · rw [if_neg hl2]
    simp only [error.truncated, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, .truncatedMessage, rfl, Or.inl trivial, ?_, rfl, rfl⟩)
    have h2 : ¬ 1 < (args.map UScalar.bv).length := by
      rw [List.length_map, ← hlen]; intro h; apply hl2
      show (2#u64).val ≤ length.val; simp; omega
    unfold Fl4Spec.archDecodeInvocation
    dsimp only
    rw [if_pos hl, if_neg (fun h => h2 h.1)]; rfl
  rw [if_pos hl2]
  obtain ⟨a0, a1, rs', rfl⟩ : ∃ a0 a1 r, args = a0 :: a1 :: r := by
    have : 2 ≤ args.length := by rw [← hlen]; have := hl2; simp at this; scalar_tac
    match args, this with
    | a0 :: a1 :: r, _ => exact ⟨a0, a1, r, rfl⟩
  rw [hargs 0#u64 a0 rfl, hargs 1#u64 a1 rfl]
  simp only [bind_ok]
  rw [slot_cap_eq, hcx, slot_cap_eq, hcy]
  simp only [bind_ok, List.map_cons]
  refine WP.spec_bind (decode_loop0_spec (L := L) s) ?_
  rintro i ⟨hi5, hall, hfree⟩
  have hN2 : vspace.N_ASID_POOLS = 2048#u64 := by unfold vspace.N_ASID_POOLS; rfl
  rw [hN2]
  by_cases hi2 : i = 2048#u64
  · rw [if_pos hi2]
    have hF := table_full_of_none hR (fun j hj => hall j (by rw [hi2]; simpa using hj))
    exact (WP.spec_ok _).2 (Or.inl ⟨_, .deleteFirst, rfl, Or.inl trivial, mp_full hl _ _ _ _ _ _ _ _ _ _ σ hF,
      rfl, rfl⟩)
  rw [if_neg hi2]
  have hi : i.val < 2048 := by
    have : i.val ≠ 2048 := fun h => hi2 (UScalar.eq_of_val_eq h)
    omega
  have hfi := table_free_of_found hR hi (hfree hi)
  have hF : (Fl4Spec.dom σ.archState.x64AsidTable)ᶜ ≠ ∅ := fun h => by rw [h] at hfi; exact hfi
  have hsel := mp_sel hl (UScalar.bv a0) (UScalar.bv a1) (rs'.map UScalar.bv) xs cte uc' (pp.bv, idx) rc' ysl rest σ hF
  step as ⟨base, hbase⟩
  have hbv : base.val = i.val * 512 := by
    have h9 : vspace.ASID_LOW_BITS.val = 9 := by unfold vspace.ASID_LOW_BITS; rfl
    rw [hbase, h9, Nat.shiftLeft_eq]
    simp only [U64.size_def, U64.numBits, UScalarTy.U64_numBits_eq]
    rw [Nat.mod_eq_of_lt (by omega)]
  have hbase' : (Fl4Spec.ucast Fl4Spec.asidRepLen (Fl4Spec.ucast 11 i.bv : BitVec 11) <<< Fl4Spec.asidLowBits :
      BitVec 64) = base.bv := by
    apply BitVec.eq_of_toNat_eq
    simp only [Fl4Spec.ucast, Fl4Spec.asidLowBits, Fl4Spec.asidLowLen, BitVec.toNat_shiftLeft,
      BitVec.toNat_setWidth, Nat.shiftLeft_eq]
    show (i.val % 2 ^ 11 % 2 ^ 64 * 2 ^ 9) % 2 ^ 64 = base.val
    rw [hbv, Nat.mod_eq_of_lt (show i.val < 2 ^ 11 by omega), Nat.mod_eq_of_lt (show i.val < 2 ^ 64 by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  -- the untyped cap
  have hAs : AbsSlot th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hbad : (∀ p n fi, uc' ≠ .untypedCap false p n fi) → (Fl4Spec.SyscallError.invalidCapability 1 :
      Fl4Spec.SyscallError) = .invalidCapability 1 → ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) slbl
        (UScalar.bv a0 :: UScalar.bv a1 :: rs'.map UScalar.bv) xs cte .asidControlCap
        ((uc', (pp.bv, idx)) :: (rc', ysl) :: rest)) σ = ({(.error (.invalidCapability 1), σ)}, False) :=
    fun h _ => by rw [hsel]; exact mpSel_const hF (fun f _ => mpRest_bad h)
  cases uc with
  | Untyped p sb fi dev =>
    have huc : uc' = .untypedCap dev p.bv sb.val fi.val := hur.abs
    subst huc
    cases dev
    swap
    · simp only [↓reduceIte, error.invalid_cap, bind_ok]
      exact (WP.spec_ok _).2 (Or.inl ⟨_, .invalidCapability 1, rfl, Or.inr ⟨1#u64, rfl, rfl⟩,
        hbad (fun p n fi h => by cases h) rfl, rfl, rfl⟩)
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hsb : sb = fl4_abi.consts.bits.ASID_POOL
    swap
    · rw [if_neg hsb]
      simp only [error.invalid_cap, bind_ok]
      have hsbv : sb.val ≠ Fl4Spec.pageBits := fun h => hsb (UScalar.eq_of_val_eq (by
        rw [h]; unfold fl4_abi.consts.bits.ASID_POOL; rfl))
      refine (WP.spec_ok _).2 (Or.inl ⟨_, .invalidCapability 1, rfl, Or.inr ⟨1#u64, rfl, rfl⟩, ?_, rfl, rfl⟩)
      rw [hsel]; exact mpSel_const hF (fun f _ => mpRest_size hsbv)
    rw [if_pos hsb]
    have hsbv : sb.val = Fl4Spec.pageBits := by rw [hsb]; unfold fl4_abi.consts.bits.ASID_POOL; rfl
    rw [hsbv] at hsel ⊢
    -- no children
    have hxm : cslotAddr (pp.bv, idx) ∈ G.chains.flatten := (hM.members _).2 ⟨hAs.isSlot, _, hcx, by simp⟩
    have hnc := noChildren_of_adj (st := st) th hPl s σ G hM hC (hI.parentAdj (th := th)) (pp.bv, idx) hAs hxm
    unfold NoChildrenRel at hnc
    rw [hnc]
    simp only [bind_ok]
    by_cases hch : ∃ x, σ.cdt x = some (pp.bv, idx)
    · rw [if_pos hch]
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
        core.convert.FromSame.from, bind_tc_ok]
      exact (WP.spec_ok _).2 (Or.inl ⟨_, .revokeFirst, rfl, Or.inl trivial,
        by rw [hsel]; exact mpSel_const hF (fun f _ => mpRest_children hch), rfl, rfl⟩)
    rw [if_neg hch]
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    -- the target slot
    unfold cspace.lookup_target_slot
    obtain ⟨r1, hr1, e1, he1, hrel1⟩ := spec_exists
      (lookup_slot_for_cnode_op_refines (Z := Unit) th s σ hSt hSV false rc rc' hrr hrv a0 a1)
    rw [hr1]; simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
    have hlt : (Fl4Spec.lookupTargetSlot (Z := Unit) rc' (Fl4Spec.toBl a0.bv) (Fl4Spec.unat a1.bv)).run σ =
        ({(e1, σ)}, False) := he1
    cases r1 with
    | Err e =>
      cases e1 with
      | ok _ => exact hrel1.elim
      | error e' =>
        simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame, core.convert.FromSame.from, bind_ok, bind_tc_ok]
        exact (WP.spec_ok _).2 (Or.inl ⟨_, e', rfl, Or.inl hrel1,
          by rw [hsel]; exact mpSel_const hF (fun f _ => by rw [mpRest_slot hch hlt]), rfl, rfl⟩)
    | Ok dest =>
      cases e1 with
      | error _ => exact hrel1.elim
      | ok dsl =>
        obtain ⟨rfl, pd, hpd1, hpd, hcn1⟩ := hrel1
        obtain ⟨cd, ad, hcd, hcad, hgd⟩ := hSt.slot_cap (Z := Unit) hpd1 hpd
        unfold cdt.ensure_empty_slot
        simp only [slot_cap_eq, hcd, bind_ok]
        have hee := ensureEmpty_run dsl σ hgd
        by_cases hdn : cd = .Null
        swap
        · rw [cap_is_null_ne hdn]
          simp only [bind_ok, Bool.false_eq_true, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
            core.convert.FromSame.from, bind_tc_ok]
          have : ad ≠ .nullCap := fun h => hdn ((hcad.null_iff).1 h)
          simp only [this, ↓reduceIte] at hee
          exact (WP.spec_ok _).2 (Or.inl ⟨_, .deleteFirst, rfl, Or.inl trivial,
            by rw [hsel]; exact mpSel_const hF (fun f _ => mpRest_full hch hlt hee), rfl, rfl⟩)
        subst hdn
        have hadn : ad = .nullCap := (hcad.null_iff).2 rfl
        simp only [hadn, ↓reduceIte] at hee
        rw [cap_is_null_null]
        simp only [bind_ok, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch]
        obtain ⟨o, idxd⟩ := dsl
        simp only at hpd1 hpd
        subst hpd1
        refine WP.spec_mono (hPf p sb fi hsb hcx hch pd _ idxd hpd rfl hcd hcn1 i base hi hbv) ?_
        rintro res ⟨h1, -, hpost⟩
        have hk : ExceptT.run (mpRest a0.bv a1.bv (.untypedCap false p.bv Fl4Spec.pageBits fi.val) (pp.bv, idx) rc'
            (Fl4Spec.ucast Fl4Spec.asidRepLen (Fl4Spec.ucast 11 i.bv : BitVec 11) <<< Fl4Spec.asidLowBits)) σ =
            ({(.ok (.invokeASIDControl (.makePool p.bv (pd.bv, idxd) (pp.bv, idx) base.bv)), σ)}, False) := by
          rw [mpRest_ok hch hlt hee, hbase']
        have hm := mpSel_mem hfi hk (fun f' _ => by rw [mpRest_ok hch hlt hee]; exact id)
        rw [← hsel] at hm
        exact Or.inr ⟨h1, p, (pd.bv, idxd), (pp.bv, idx), base.bv, hm.1, hm.2, hpost⟩
  | _ =>
    simp only [error.invalid_cap, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, .invalidCapability 1, rfl, Or.inr ⟨1#u64, rfl, rfl⟩,
      hbad (fun p n fi h => by rw [hur.abs] at h; simp [absCap] at h) rfl, rfl, rfl⟩)

end

end

end Fl4Proofs.P3.Vs

namespace Fl4Proofs.P3
open fl4_core Classical Vs

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

set_option maxHeartbeats 8000000 in
/-- **The ASID control cap with any perform** (`decode_invocation_asid_controlXG`
with `MakePool`'s perform given, `makepool_relP`; for XTopJointMakePoolD). -/
theorem decode_invocation_asid_controlXP (th : TypedHeap) (hP : Placed th) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hU : UtInv (L.mem s) G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 : Set U64} {SR : S → A → Fl4Spec.State Unit → Prop}
    {Q : S → Prop} {RegOK : S → Fl4Spec.State Unit → U64 → Prop}
    (hH : VsMpHyps st A th P L4 L3 L2 L1 SR RegOK) (hS : SR s ar σ)
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (hVP : VsPlaced P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    (hVO : ∀ b, VsWrite P (L.ksb s) b → OutsideObjects th b)
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b)
    (hPV : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlM : lbl = fl4_abi.label.X86ASIDControlMakePool ↔
      Fl4Spec.invocationType slbl = .archInvocationLabel .x64ASIDControlMakePool)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    {X : S → A → Fl4Spec.State Unit → Prop}
    (hext : (∃ o0 o1, vspace.extra extra 0#usize = ok o0 ∧ vspace.extra extra 1#usize = ok o1 ∧
        (o0 = none ∨ o1 = none) ∧ excaps.length ≤ 1) ∨
      ∃ (pp : U64) (rs : Nat) (idx : List Bool) (y : obj.Slot) (uc : capability.Cap) (uc' : Fl4Spec.Cap)
        (rc : capability.Cap) (rc' : Fl4Spec.Cap) (ysl : Fl4Spec.CslotPtr)
        (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)),
        th pp = some (.cnode rs) ∧ idx.length = rs ∧
        vspace.extra extra 0#usize = ok (some (cslotAddr (pp.bv, idx))) ∧ vspace.extra extra 1#usize = ok (some y) ∧
        capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok uc ∧ CapRel uc uc' ∧
        capAt (L.mem s) y = ok rc ∧ CapRel rc rc' ∧ CapValid th rc ∧
        excaps = (uc', (pp.bv, idx)) :: (rc', ysl) :: rest ∧
        ∀ (p sb fi : U64), sb = fl4_abi.consts.bits.ASID_POOL →
      capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false) →
      (¬ ∃ sl, σ.cdt sl = some (pp.bv, idx)) →
      ∀ (pd : U64) (rd : Nat) (idxd : List Bool), th pd = some (.cnode rd) → idxd.length = rd →
      capAt (L.mem s) (cslotAddr (pd.bv, idxd)) = ok .Null → CnRef th (L.mem s) rc pd →
      ∀ (i base : U64), i.val < 2048 → base.val = i.val * 512 →
      (do
        let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
        let i1 ← lift (sb &&& 63#u64)
        let i2 ← 1#u64 <<< i1
        let s2 ← obj.Slot.set_cap st (cslotAddr (pp.bv, idx)) s1 (capability.Cap.Untyped p sb i2 false)
        let s3 ← st.clear_free s2 p 4096#u64
        let s4 ← cdt.insert st s3 (capability.Cap.AsidPool p base) (cslotAddr (pp.bv, idx)) (cslotAddr (pd.bv, idxd))
        let s5 ← vspace.set_asid_table st s4 i p
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, ar)) ⦃ res =>
        res.1 = .Ok () ∧ res.2.2 = ar ∧ ∃ σ' th' G',
          ((), σ') ∈ ((Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart >>= fun _ =>
            Fl4Spec.performAsidControlInvocation (.makePool p.bv (pd.bv, idxd) (pp.bv, idx) base.bv)) σ).1 ∧
          ¬ ((Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart >>= fun _ =>
            Fl4Spec.performAsidControlInvocation (.makePool p.bv (pd.bv, idxd) (pp.bv, idx) base.bv)) σ).2 ∧
          Placed th' ∧ CRel th' (L.mem res.2.1) σ' G' ∧ FinInv th' (L.mem res.2.1) σ' G' ∧
          MdbOKV (L.ksb s) (L.mem res.2.1) G' ∧ Q res.2.1 ∧ X res.2.1 res.2.2 σ' ⦄)
    (hX0 : X s ar σ)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    DecOKMQX (L := L) arI Q X s ar σ lbl length slot .AsidControl blk call don fp buf extra slbl (args.map UScalar.bv) ci sl
      excaps buffer := by
  have hCR0 := hCR
  obtain ⟨hSt, hSV, hM, hC, hI⟩ := hCR0
  obtain ⟨xct, hkt0, -⟩ := hSt.tcb ct htcb
  have hkt : σ.kheap σ.curThread = some (.tcb xct) := by rw [hcur]; exact hkt0
  unfold DecOKMQX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  have hspec : specDec fp slbl (args.map UScalar.bv) ci sl .AsidControl excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeArchObject
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4ArchInvocation.spec (Fl4Spec.archDecodeInvocation (Z := Unit) slbl
          (args.map UScalar.bv) ci sl .asidControlCap excaps)) := rfl
  rw [hspec]
  by_cases hl : lbl = fl4_abi.label.X86ASIDControlMakePool
  swap
  · unfold vspace.decode
    rw [hct]; simp only [bind_ok]
    have : (lbl != fl4_abi.label.X86ASIDControlMakePool) = true := by simpa using hl
    simp only [this, ↓reduceIte, error.illegal, bind_ok, WP.spec_ok]
    exact topMQX_err (⟨_, rfl, rfl, .illegalOperation,
      decodeMP_illegal (fun h => hl (hlM.2 h)) _ _ _ _ σ, Or.inl trivial⟩) hX0
  subst hl
  have hl' := hlM.1 rfl
  rcases hext with ⟨o0, o1, h0, h1, hn, hlen1⟩ |
    ⟨pp, rs, idx, y, uc, uc', rc, rc', ysl, rest, hpp, hidx, hex0, hex1, hcx, hur, hcy, hrr, hrv, rfl, hRg⟩
  · unfold vspace.decode
    rw [hct]; simp only [bind_ok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    rw [h0, h1]; simp only [bind_ok]
    rcases hn with rfl | rfl
    · simp only [error.truncated, bind_ok, WP.spec_ok]
      exact topMQX_err (⟨_, rfl, rfl, .truncatedMessage, decodeMP_trunc hl' _ _ _ _ hlen1 σ, Or.inl trivial⟩) hX0
    · cases o0 <;> simp only [error.truncated, bind_ok, WP.spec_ok] <;>
        exact topMQX_err (⟨_, rfl, rfl, .truncatedMessage, decodeMP_trunc hl' _ _ _ _ hlen1 σ, Or.inl trivial⟩) hX0
  have hd := makepool_relP (L := L) (ar := arI) hH s ar σ G hP hSt hSV hM hC hI hU hR hPt hS hVP hPP hVO hPO hPV ct hct
    hcur.symm hkt (hrun _ hkt) htcb hact hl' length buf args hlen hargs ci sl slot call extra hpp hidx hex0 hex1 hcx hur hcy hrr hrv
    ysl rest (Post := fun p dest ps base res => ∃ σ' th' G',
          ((), σ') ∈ ((Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart >>= fun _ =>
            Fl4Spec.performAsidControlInvocation (.makePool p.bv dest ps base)) σ).1 ∧
          ¬ ((Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart >>= fun _ =>
            Fl4Spec.performAsidControlInvocation (.makePool p.bv dest ps base)) σ).2 ∧
          Placed th' ∧ CRel th' (L.mem res.2.1) σ' G' ∧ FinInv th' (L.mem res.2.1) σ' G' ∧
          MdbOKV (L.ksb s) (L.mem res.2.1) G' ∧ Q res.2.1 ∧ X res.2.1 res.2.2 σ') hRg
  refine WP.spec_mono hd ?_
  rintro res (⟨e, e', h1, he, hD, h2, h2a⟩ | ⟨h1, p, dest, ps, base, hmem, hnf, σ', th', G', hm, hnf', hP', hCR',
    hF', hMO', hQ', hX'⟩)
  · exact topMQX_err (⟨e, h1, h2, e', hD, he⟩) (by rw [h2, h2a]; exact hX0)
  · have hst1 : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ =
        ({((), Notif.stsAct (Notif.updK σ ct.bv (.tcb { xct with tcbState := .restart })) ct.bv)}, False) := by
      rw [hcur]; exact Notif.setThreadState_eq .restart hkt0
    have hm' := hm
    rw [nd_bind_one hst1] at hm'
    exact ⟨topMX_of_lift2M ⟨_, ⟨hmem, hnf⟩, _, hst1, (.ok [], σ'),
      mem_liftE (ε := Unit) (x := ([], σ')) (mem_bind_nd (x := ((), σ')) hm' (Set.mem_singleton _)), ⟨th', G',
      Or.inl ⟨h1, [], rfl⟩, hP', hCR', hF', hMO'⟩, hX'⟩, Or.inr hQ'⟩

end

end

end Fl4Proofs.P3
