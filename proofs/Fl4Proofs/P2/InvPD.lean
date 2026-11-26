/-
# P2 (line hpzg, generation 9): `hPDw` discharged, and `huf` of the frame-cap invocation path without it (`InvPD`)

`hufQL_of` (P2/InvHuf.lean) left [J] `hPDw`: the plan (`InvPlanD`, `plan_with` at `CNodeDelete` on the plan's slot)
survives a write of a user word at a bundle state. `plan_with`'s Delete arm reads

* the plan's slot's cap (a capability slot: `IoPre.cap_userWr`);
* the message registers R10 / R8 of the current thread (TCB words: `tcbReg_wr`);
* the target lookup `lookup_target_slot` from the invoked CNode cap: radix-masked slots of the walk's CNodes, all
  capability slots (`lts_userWr`, from `rab_loop_congr2`);
* the target's cap words and its `PREV` / `NEXT` words (a capability slot's words: `planRead_userWr`,
  `planReadCap_userWr`);
* `localinv.small_page_entry`'s ASID / page-table words: none is a user word (P3's new
  `JAtZ.smallPageEntry_userWr`, P3/VsUserApart.lean, from `TopPlaced.disj`).

So it answers alike (`planDel_userWr`), and:

* **`invPlanD_wr`**: `hPDw` for `InvQL`, no premise;
* **`hufQL_of2`**: `inv_pathsKF`'s `huf` from [J] `hIw` and [P] `hlk` alone.

No statement of an existing declaration changes; no `kernel_entry_reach*` is touched.
-/
import Fl4Proofs.P2.InvHuf
import Fl4Proofs.P3.VsUserApart
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout fld)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {s : S} {b : U64}
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}

/-- A word of a capability slot is no user word (at an `IoPre` state). -/
theorem IoPre.slotW_nu (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) {sl w : U64} (hsl : sl ∈ K.slots)
    (hw : OwnMap.InW sl 32 w) : w ∉ K.user :=
  P.region_kernel (Or.inl (by rw [P.lay.slotw sl hsl w hw]; simp))

/-- `Plan.read` of a non-user aligned word answers alike after a user write. -/
theorem planRead_userWr (hb : b ∈ K.user) (hba : Aligned b) (v : U64) {a : U64} (ha : Aligned a)
    (hau : a ∉ K.user) (q : localinv.Plan) :
    localinv.Plan.read st q (L.wr s b v) a = localinv.Plan.read st q s a := by
  unfold localinv.Plan.read
  by_cases h : q.nseen >= localinv.MAX_LOCKS
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, L.read_eq, L.read_eq, mem_wr_ne' hba ha (fun e => hau (e ▸ hb))]

/-- `Plan.read_cap` of a capability slot answers alike after a user write. -/
theorem planReadCap_userWr (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) (hb : b ∈ K.user) (hba : Aligned b)
    (v : U64) {sl : U64} (hsl : sl ∈ K.slots) (q : localinv.Plan) :
    localinv.Plan.read_cap st q (L.wr s b v) sl = localinv.Plan.read_cap st q s sl := by
  obtain ⟨h8, hf⟩ := P.lay.slot8 sl hsl
  have e0 : core.num.U64.wrapping_add sl layout.cte.CAP0 = sl := by
    apply UScalar.eq_of_val_eq
    simp [core.num.U64.wrapping_add_val_eq, layout.cte.CAP0, U64.size_def, U64.numBits]
  have hv : (core.num.U64.wrapping_add sl layout.cte.CAP1).val = sl.val + 8 := by
    simp [core.num.U64.wrapping_add_val_eq, layout.cte.CAP1, U64.size_def, U64.numBits]; omega
  unfold localinv.Plan.read_cap
  simp only [lift, bind_ok]
  rw [e0, planRead_userWr hb hba v h8 (P.slotW_nu hsl ⟨le_refl _, by omega⟩)]
  refine bind_guard_congr rfl (fun ⟨w0, q1⟩ _ => ?_)
  simp only [Aeneas.Std.uncurry_apply_pair]
  rw [planRead_userWr hb hba v (by unfold Aligned; omega) (P.slotW_nu hsl ⟨by omega, by omega⟩)]

/-- The target lookup from a CNode cap of a closed walk set answers as at `s` after a user write. -/
theorem lts_userWr (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) (hb : b ∈ K.user) (hba : Aligned b) (v : U64)
    {C : U64 → U64 → Prop}
    (hCs : ∀ p r m y, C p r → cspace.mask r = ok m → cnSlot p (y &&& m) ∈ K.slots)
    (hcl : WalkCl (st := st) s C) {cp cr cg cgb cptr depth : U64} (hc : C cp cr)
    {r : core.result.Result obj.Slot error.Exc}
    (h : cspace.lookup_target_slot st s (.CNode cp cr cg cgb) cptr depth = ok r) :
    cspace.lookup_target_slot st (L.wr s b v) (.CNode cp cr cg cgb) cptr depth = ok r := by
  unfold cspace.lookup_target_slot cspace.lookup_slot_for_cnode_op at h ⊢
  simp only [bind_ok, ↓reduceIte] at h ⊢
  by_cases d1 : depth < 1#u64
  · rw [if_pos d1] at h ⊢; exact h
  rw [if_neg d1] at h ⊢
  by_cases d2 : depth > cspace.WORD_BITS
  · rw [if_pos d2] at h ⊢; exact h
  rw [if_neg d2] at h ⊢
  obtain ⟨res, eres, hl⟩ := bind_eq_ok h
  unfold cspace.resolve_address_bits at eres ⊢
  rw [rab_loop_congr2 st C (fun p r hp m hm y => P.cap_userWr hb hba v (hCs p r m y hp hm)) hcl 66 _ depth 65#u64
    res (by simp) (fun p r gs g e => by cases e; exact hc) eres]
  simp only [bind_ok]
  exact hl

set_option maxHeartbeats 4000000 in
/-- **`plan_with` at `CNodeDelete` answers alike after a user write** (module docstring), at a bundle state with
`IoPre`: the current thread `t`, the invoked slot a capability slot with a CNode cap of a closed walk set `C`. -/
theorem planDel_userWr (hJ : SlJAt (L := L) K s)
    (P : IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hb : b ∈ K.user) (hba : Aligned b) (v : U64) {sl : obj.Slot} (hsl : sl ∈ K.slots)
    {cp cr cg cgb : U64} (hcap : obj.Slot.cap st sl s = ok (.CNode cp cr cg cgb)) {C : U64 → U64 → Prop}
    (hC : C cp cr) (hcl : WalkCl (st := st) s C)
    (hCs : ∀ p r m y, C p r → cspace.mask r = ok m → cnSlot p (y &&& m) ∈ K.slots)
    (ex : Array obj.Slot 3#usize) :
    localinv.plan_with st (L.wr s b v) (L.curW s) fl4_abi.label.CNodeDelete sl ex =
      localinv.plan_with st s (L.curW s) fl4_abi.label.CNodeDelete sl ex := by
  have hT : K.heap (L.curW s) = some .tcb := P.cT
  have e10 := tcbReg_wr hJ hb hba v hT P.tA (r := layout.reg.R10) (by simp [layout.reg.R10])
  have e8 := tcbReg_wr hJ hb hba v hT P.tA (r := layout.reg.R8) (by simp [layout.reg.R8])
  have er0 : localinv.reg_arg st (L.wr s b v) (L.curW s) 0#u64 = localinv.reg_arg st s (L.curW s) 0#u64 := by
    unfold localinv.reg_arg; rw [sarg0_reg, sarg0_reg, reg_ok, reg_ok, e10]
  have er1 : localinv.reg_arg st (L.wr s b v) (L.curW s) 1#u64 = localinv.reg_arg st s (L.curW s) 1#u64 := by
    unfold localinv.reg_arg; rw [sarg1_reg, sarg1_reg, reg_ok, reg_ok, e8]
  have elts : ∀ cptr depth, cspace.lookup_target_slot st (L.wr s b v) (.CNode cp cr cg cgb) cptr depth =
      cspace.lookup_target_slot st s (.CNode cp cr cg cgb) cptr depth := by
    intro cptr depth
    obtain ⟨r, hr, -⟩ := spec_ex_fd (P0.cspace.lookup_target_slot.p0 st s (.CNode cp cr cg cgb) cptr depth L.total)
    rw [hr, lts_userWr P hb hba v hCs hcl hC hr]
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := id hJ
  have hb' := hb
  rw [B.user] at hb'
  obtain ⟨wp, hwB, ewp⟩ := hb'
  have espe : ∀ asid va, localinv.small_page_entry st (L.wr s b v) asid va =
      localinv.small_page_entry st s asid va := by
    intro asid va
    subst ewp
    exact B.j.smallPageEntry_userWr hwB hba v asid va
  unfold localinv.plan_with
  rw [P.cap_userWr hb hba v hsl, hcap]
  simp only [bind_ok, if_neg lbl_del_ne_copy, if_neg lbl_del_ne_mint, ↓reduceIte, er0, er1, elts]
  obtain ⟨i, hi⟩ : ∃ i, localinv.reg_arg st s (L.curW s) 0#u64 = ok i := by
    unfold localinv.reg_arg; rw [sarg0_reg, reg_ok]; exact ⟨_, rfl⟩
  obtain ⟨i1, hi1⟩ : ∃ i1, localinv.reg_arg st s (L.curW s) 1#u64 = ok i1 := by
    unfold localinv.reg_arg; rw [sarg1_reg, reg_ok]; exact ⟨_, rfl⟩
  rw [hi, hi1]
  simp only [bind_ok]
  obtain ⟨r, hr, -⟩ := spec_ex_fd (P0.cspace.lookup_target_slot.p0 st s (.CNode cp cr cg cgb) i i1 L.total)
  rw [hr]
  simp only [bind_ok]
  cases r with
  | Err e =>
    simp only [core.result.Result.ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, bind_ok]
  | Ok dest =>
    obtain ⟨q, rq, m, y, hq, hm, rfl⟩ := lts_cn (fun p r gs g e => by cases e; exact hC) hcl hr
    have hdK := hCs q rq m y hq hm
    obtain ⟨h8, hf⟩ := P.lay.slot8 _ hdK
    have hvP : (core.num.U64.wrapping_add (cnSlot q (y &&& m)) layout.cte.PREV).val = (cnSlot q (y &&& m)).val + 16 := by
      generalize cnSlot q (y &&& m) = d at hf ⊢
      simp [core.num.U64.wrapping_add_val_eq, layout.cte.PREV, U64.size_def, U64.numBits]; omega
    have hvN : (core.num.U64.wrapping_add (cnSlot q (y &&& m)) layout.cte.NEXT).val = (cnSlot q (y &&& m)).val + 24 := by
      generalize cnSlot q (y &&& m) = d at hf ⊢
      simp [core.num.U64.wrapping_add_val_eq, layout.cte.NEXT, U64.size_def, U64.numBits]; omega
    have ePr := planRead_userWr (st := st) (s := s) hb hba v (a := core.num.U64.wrapping_add (cnSlot q (y &&& m)) layout.cte.PREV)
      (by unfold Aligned; omega) (P.slotW_nu hdK ⟨by omega, by omega⟩)
    have eNx := planRead_userWr (st := st) (s := s) hb hba v (a := core.num.U64.wrapping_add (cnSlot q (y &&& m)) layout.cte.NEXT)
      (by unfold Aligned; omega) (P.slotW_nu hdK ⟨by omega, by omega⟩)
    simp only [core.result.Result.ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, bind_ok, lift,
      planReadCap_userWr P hb hba v hdK, ePr, eNx, espe]

/-- (hpzg gen 9) **`hPDw` of `hufQL_of`, discharged**: the plan survives a user write at a bundle state with `InvQL`. -/
theorem invPlanD_wr {Locks : S → U64 → Prop} {p : localinv.Plan} :
    ∀ K m s b v, SlJAt (L := L) K s → InvQL st Cs Ω Sg Ac Locks p K m s → b ∈ K.user → Aligned b →
      InvPlanD st p (L.wr s b v) := by
  intro K m s b v hJ hq hb hba
  have hqf := hq.1
  obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, C, hcap, hsK, -, -, hC, hcl, hCs, -⟩ := del_core hqf
  obtain ⟨⟨hio, ⟨t, info, ex, ht, hi, hpw⟩, harm, -⟩, -⟩ := hqf
  have P := hio.1
  have hT : K.heap (L.curW s) = some .tcb := P.cT
  have et : t = L.curW s := by rw [cur_thread_ok] at ht; exact (ok_inj_ff ht).symm
  subst et
  have hlbl := (harm _ info (cur_thread_ok s) hi).1
  rw [hlbl] at hpw
  refine ⟨L.curW s, info, ex, ?_, ?_, ?_⟩
  · rw [cur_thread_ok, hJ.curW_wr hb hba v]
  · rw [msgInfo_wr hJ hb hba v hT P.tA]; exact hi
  · rw [hlbl, planDel_userWr hJ P hb hba v hsK hcap hC hcl (fun p r m y hp hm => (hCs p r m y hp hm).1) ex]
    exact hpw

/-- (hpzg gen 9) **`inv_pathsKF`'s `huf`** at `Pre := SlJAt K ∧ InvQL …` from [J] `hIw` (`IoPre` survives a user
write at a bundle state) and [P] `hlk` (the locks are kept) alone. -/
theorem hufQL_of2 {Locks : S → U64 → Prop} {p : localinv.Plan}
    (hIw : ∀ K s b v, SlJAt (L := L) K s →
      IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s →
      b ∈ K.user → Aligned b →
      IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac (L.wr s b v))
    (hlk : ∀ K s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s) :
    ∀ K m s b v, SlJAt (L := L) K s → InvQL st Cs Ω Sg Ac Locks p K m s → b ∈ K.user → Aligned b →
      (SlJAt (L := L) K (L.wr s b v) ∧ InvQL st Cs Ω Sg Ac Locks p K m (L.wr s b v)) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s :=
  hufQL_of hIw invPlanD_wr hlk

end

end Fl4Proofs.P2.PathObl
