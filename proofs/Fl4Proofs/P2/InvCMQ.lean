/-
# P2 (line slhuf, gen 13): a user-write-stable canonical `Q` for the Copy / Mint path

`InvQCMF := InvQCM ∧ InvLk ∧ InvEx` (P2/InvCMEnt.lean) is not kept by a user write: `InvEx` states
`ipc.lookup_extra_caps … = ok (Ok p.extra)`, which reads the caller's IPC buffer (user words). What the arm's entry
facts need of it is only (a) `plan_with` on the plan's own extra caps and (b) that the first extra cap is the slot of
a CSpace lookup. Both read kernel words only:

* `InvExW` (msg_info, `plan_with … p.slot p.extra = ok (some p)`, the first extra cap a `lookup_slot` result),
  `invExW_of_ex` (`InvEx → InvExW`, by `lec_slot0`), `InvQCMW := InvQCM ∧ InvLk ∧ InvExW`, `invQCMW_of_plan`;
* `cm_coreW`, `cmEnt_ofW`, `cmSl_ofW`, `cmPs_ofW`, `cmSeen_ofW`: InvCMCore's lemmas over `InvQCMW`;
* user writes: `lookupSlot_userWr`, `lss_userWr`, **`planCM_userWr`** (`plan_with`'s Copy / Mint arm answers alike
  after a user write: it reads the invoked slot's cap, R10 / R8 / R9 / R15, CNode-walk slots of the closure, the
  first extra cap's cap, the target's and the source's slot words), `invExW_wr`;
* **`hufQCMW_of`**: the `huf` of `Pre := SlJAt K ∧ InvQCMW …` from [J] `hIw` and [P] `hlk` (invj's `hufQF_of2`
  shape).

Named premises: [J] `hIw`, [P] `hlk` (`hufQCMW_of`); [J] `InvCdtJ`, `hz` (`cmEnt_ofW`, `cmSeen_ofW`, as InvCMCore).
No existing statement changes.
-/
import Fl4Proofs.P2.InvCMCore
import Fl4Proofs.P2.InvJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot)

section defs
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

variable (st) in
/-- (slhuf gen 13) **The plan's extra caps at the entry, kernel words only**: the message info, `plan_with` on the
plan's own slot and extra caps returning the plan, and the first extra cap (when not null) the slot of a
`lookup_slot` from the current thread. -/
def InvExW (p : localinv.Plan) (s : S) : Prop :=
  ∃ info, msg.msg_info st s (L.curW s) = ok info ∧
    localinv.plan_with st s (L.curW s) info.label p.slot p.extra = ok (some p) ∧
    ∀ s1, Aeneas.Std.Array.index_usize p.extra 0#usize = ok s1 → s1 ≠ 0#u64 →
      ∃ c r, cspace.lookup_slot st s (L.curW s) c = ok (core.result.Result.Ok r) ∧ r.slot = s1

/-- (slhuf gen 13) `InvEx` gives `InvExW` (`lec_slot0`). -/
theorem invExW_of_ex {p : localinv.Plan} {s : S} (h : InvEx st p s) : InvExW st p s := by
  obtain ⟨info, buf, ei, -, ee, hpw⟩ := h
  exact ⟨info, ei, hpw, fun s1 h0 hs => lec_slot0 ee h0 hs⟩

variable (st) in
/-- (slhuf gen 13) **The canonical `Q` of the Copy / Mint path, user-write stable**: `InvQCM ∧ InvLk ∧ InvExW`. -/
def InvQCMW (Cs Ω Sg Ac : Set U64) (Locks : S → U64 → Prop) (p : localinv.Plan) (K : KLayout)
    (m : U64 → U64) (s : S) : Prop :=
  InvQCM st Cs Ω Sg Ac Locks p K m s ∧ InvLk st p s ∧ InvExW st p s

/-- (slhuf gen 13) `InvQCMF` gives `InvQCMW`. -/
theorem invQCMW_of_F {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayout}
    {m : U64 → U64} {s : S} (h : InvQCMF st Cs Ω Sg Ac Locks p K m s) : InvQCMW st Cs Ω Sg Ac Locks p K m s :=
  ⟨h.1, h.2.1, invExW_of_ex h.2.2⟩

end defs

/-! ## The entry facts from `InvQCMW` -/

section ent
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayout} {μ : U64 → U64}
  {s : S}

/-- (slhuf gen 13) **`cm_core` over `InvQCMW`** (no premise). -/
theorem cm_coreW (hq : InvQCMW st Cs Ω Sg Ac Locks p K μ s) :
    ∃ (cp cr cg cgb dest s1 rp rr rg rgb src fp rt asid va : U64) (sz : capability.FrameSize) (d mp : Bool)
      (c1 : capability.Cap) (C : U64 → U64 → Prop),
      obj.Slot.cap st p.slot s = ok (.CNode cp cr cg cgb) ∧ p.slot ∈ K.slots ∧
      Aeneas.Std.Array.index_usize p.extra 0#usize = ok s1 ∧ s1 ≠ 0#u64 ∧
      cspace.lookup_target_slot st s (.CNode cp cr cg cgb) (L.mem s (regA (L.curW s) layout.reg.R10))
        (L.mem s (regA (L.curW s) layout.reg.R8)) = ok (.Ok dest) ∧
      obj.Slot.cap st s1 s = ok (.CNode rp rr rg rgb) ∧
      cspace.lookup_source_slot st s (.CNode rp rr rg rgb) (L.mem s (regA (L.curW s) layout.reg.R9))
        (L.mem s (regA (L.curW s) layout.reg.R15)) = ok (.Ok src) ∧
      obj.Slot.cap st src s = ok (.Frame fp sz rt d mp false asid va) ∧
      capability.Cap.decode (L.mem s (core.num.U64.wrapping_add dest layout.cte.CAP0)) 0#u64 = ok c1 ∧
      capability.Cap.is_null c1 = ok true ∧
      C cp cr ∧ C rp rr ∧ WalkCl (st := st) s C ∧
      (∀ p r m y, C p r → cspace.mask r = ok m → cnSlot p (y &&& m) ∈ K.slots ∧
        OutsideObjs st K.heap.tcbs Cs s (cnSlot p (y &&& m)) ∧
        OutsideObjs st K.heap.tcbs Cs s (core.num.U64.wrapping_add (cnSlot p (y &&& m)) 8#u64)) ∧
      s1 ∈ K.slots ∧ OutsideObjs st K.heap.tcbs Cs s s1 ∧
      dest ∈ K.slots ∧ OutsideObjs st K.heap.tcbs Cs s dest ∧ (dest ≠ 0#u64 → Locks s dest) ∧
      src ∈ K.slots ∧ OutsideObjs st K.heap.tcbs Cs s src ∧ (src ≠ 0#u64 → Locks s src) ∧
      (∀ nx, obj.Slot.next st src s = ok nx → nx ≠ 0#u64 → Locks s nx) ∧
      (∀ x, SeenW p x → CMW dest src x) := by
  obtain ⟨⟨⟨PE, -⟩, -, harm, hlk⟩, ⟨x, hx, hxs⟩, ⟨info, ei, hpw, hlec⟩⟩ := hq
  have hl := harm _ _ (cur_thread_ok s) ei
  obtain ⟨cp, cr, cg, cgb, dest, s1, src, fp, rt, asid, va, sz, d, mp, rc, c1, hcap, hex, hs10, htg, erc, er1,
    hsc, ec1, eb1, hHd, hHs, hHn, hSn⟩ := plan_with_cmF hl hpw
  obtain ⟨rp, rr, rg, rgb, hrc⟩ := lss_root er1
  subst hrc
  obtain ⟨C, hroot, hcl, hC⟩ := PE.walk
  obtain ⟨q0, r0, m0, y0, hq0, hm0, hs0⟩ := lookup_slot_cn hroot hcl hx
  rw [hxs] at hs0
  have hCc : C cp cr := hcl q0 r0 m0 y0 cp cr cg cgb hq0 hm0 (by rw [← hs0]; exact hcap)
  obtain ⟨c2, x2, hx2, hxs2⟩ := hlec s1 hex hs10
  obtain ⟨q2, r2, m2, y2, hq2, hm2, hs2⟩ := lookup_slot_cn hroot hcl hx2
  rw [hxs2] at hs2
  have hCr : C rp rr := hcl q2 r2 m2 y2 rp rr rg rgb hq2 hm2 (by rw [← hs2]; exact erc)
  have hS1 := hC q2 r2 m2 y2 hq2 hm2
  rw [← hs2] at hS1
  obtain ⟨q1, r1, m1, y1, hq1, hm1, hs1⟩ := lts_cn (fun p r gs g e => by cases e; exact hCc) hcl htg
  have hD := hC q1 r1 m1 y1 hq1 hm1
  rw [← hs1] at hD
  obtain ⟨q3, r3, m3, y3, hq3, hm3, hs3⟩ := lss_cn (fun p r gs g e => by cases e; exact hCr) hcl er1
  have hR := hC q3 r3 m3 y3 hq3 hm3
  rw [← hs3] at hR
  have held : ∀ y, PHeld p y → Locks s y := fun y ⟨j, hj, hy⟩ => hlk j y hj hy
  refine ⟨cp, cr, cg, cgb, dest, s1, rp, rr, rg, rgb, src, fp, rt, asid, va, sz, d, mp, c1, C, hcap, ?_, hex,
    hs10, htg, erc, er1, hsc, ec1, eb1, hCc, hCr, hcl, hC, hS1.1, hS1.2.1, hD.1, hD.2.1,
    fun hd => held _ (hHd hd), hR.1, hR.2.1, fun hd => held _ (hHs hd), fun nx e hne => held _ (hHn nx e hne), ?_⟩
  · rw [hs0]; exact (hC q0 r0 m0 y0 hq0 hm0).1
  · intro w ⟨i, q, hi, hiM, hidx, hq⟩
    have hM : localinv.MAX_LOCKS.val = 4 := maxLocks_val
    have hiv : i.val < 4 := by have : i.val < localinv.MAX_LOCKS.val := hiM; omega
    have hlen : p.seen.val.length = 4 := by have hp := p.seen.property; simpa using hp
    have hl : i.val < p.seen.length := by simp only [Aeneas.Std.Array.length]; omega
    rw [eq_of_spec_fd (Aeneas.Std.Array.index_usize_spec p.seen i hl)] at hidx
    have e := ok_inj_ff hidx
    subst e hq
    exact hSn i.val (by omega) hi

/-- (slhuf gen 13) **`CMEnt` at the entry from `InvQCMW`** ([J] `InvCdtJ`, [J] `hz`). -/
theorem cmEnt_ofW {P : S → Prop} (hPs : P s) (hq : InvQCMW st Cs Ω Sg Ac Locks p K μ s)
    (hcdt : InvCdtJ st K P) (hz : (0#u64) ∉ K.slots) : CMEnt st K Cs Locks p s := by
  obtain ⟨cp, cr, cg, cgb, dest, s1, rp, rr, rg, rgb, src, fp, rt, asid, va, sz, d, mp, c1, C, hcap, -, hex,
    hs10, htg, erc, er1, hsc, ec1, eb1, hCc, hCr, hcl, hC, hs1K, hs1O, hdK, hdO, hLd, hsK, hsO, hLs, hLn, -⟩ :=
    cm_coreW hq
  have hd0 : dest ≠ 0#u64 := fun e => hz (e ▸ hdK)
  have hsr0 : src ≠ 0#u64 := fun e => hz (e ▸ hsK)
  obtain ⟨-, hcN⟩ := hcdt s src hPs hsK
  exact ⟨cp, cr, cg, cgb, dest, s1, rp, rr, rg, rgb, src, fp, rt, asid, va, sz, d, mp, c1, C, hcap, hex, hs10,
    htg, erc, er1, hsc, ec1, eb1, hCc, hCr, hcl, hC, hs1K, hs1O, hdK, hdO, hLd hd0, hsK, hsO, hLs hsr0,
    fun nx e hne => ⟨hcN nx e hne, hLn nx e hne⟩⟩

/-- (slhuf gen 13) The invoked slot is a capability slot (no premise). -/
theorem cmSl_ofW (hq : InvQCMW st Cs Ω Sg Ac Locks p K μ s) : p.slot ∈ K.slots := by
  obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hsK, -⟩ := cm_coreW hq
  exact hsK

/-- (slhuf gen 13) **`hps` for `Q := InvQCMW`** (no premise). -/
theorem cmPs_ofW :
    ∀ K μ s, SlJAt (L := L) K s → InvQCMW st Cs Ω Sg Ac Locks p K μ s →
      IoRS (st := st) K Locks s p.slot ∧ IoRS (st := st) K Locks s (core.num.U64.wrapping_add p.slot 8#u64) := by
  intro K μ s _ hq
  have PE := hq.1.1.1
  obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcap, hsK, -⟩ := cm_coreW hq
  exact PE.slot hsK (Or.inr (cap_not_nof hcap (Or.inl ⟨_, _, _, _, rfl⟩)))

/-- (slhuf gen 13) **`hSeen` for `Q := InvQCMW`** ([J] `hz`). -/
theorem cmSeen_ofW
    (hz : ∀ K μ s, SlJAt (L := L) K s → InvQCMW st Cs Ω Sg Ac Locks p K μ s → (0#u64) ∉ K.slots) :
    InvSeenRS st Locks p (InvQCMW st Cs Ω Sg Ac Locks p) := by
  intro K μ s hJ hq x hx
  have PE := hq.1.1.1
  obtain ⟨cp, cr, cg, cgb, dest, s1, rp, rr, rg, rgb, src, fp, rt, asid, va, sz, d, mp, c1, C, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, hdK, -, hLd, hsK, -, hLs, -, hSn⟩ := cm_coreW hq
  have hd0 : dest ≠ 0#u64 := fun e => hz K μ s hJ hq (e ▸ hdK)
  have hsr0 : src ≠ 0#u64 := fun e => hz K μ s hJ hq (e ▸ hsK)
  rcases hSn x hx with rfl | rfl | rfl | rfl
  · exact (PE.lockSlot hdK (hLd hd0) (by simp [layout.cte.CAP0]) (by simp [layout.cte.CAP0])).1
  · exact (PE.lockSlot hsK (hLs hsr0) (by simp [layout.cte.CAP0]) (by simp [layout.cte.CAP0])).1
  · exact (PE.lockSlot hsK (hLs hsr0) (by simp [layout.cte.CAP1]) (by simp [layout.cte.CAP1])).1
  · exact (PE.lockSlot hsK (hLs hsr0) (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT])).1

end ent

/-! ## User writes -/

section wr
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {s : S} {b : U64}
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}

/-- (slhuf gen 13) **A successful `lookup_slot` from the current thread is kept by a user write** (as `invLk_wr`). -/
theorem lookupSlot_userWr (hJ : SlJAt (L := L) K s)
    (P : IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hb : b ∈ K.user) (hba : Aligned b) (v : U64) {c : U64} {r : cspace.Resolved}
    (h : cspace.lookup_slot st s (L.curW s) c = ok (core.result.Result.Ok r)) :
    cspace.lookup_slot st (L.wr s b v) (L.curW s) c = ok (core.result.Result.Ok r) := by
  have hT : K.heap (L.curW s) = some .tcb := P.cT
  obtain ⟨C, hroot, hcl, hC⟩ := P.walk
  obtain ⟨res, hres, -⟩ := spec_ex_fd (P0.cspace.lookup_slot.p0 st (L.wr s b v) (L.curW s) c L.total)
  have back := lookup_slot_back (tcb_slot_ctable (L.curW s))
    (P.cap_userWr hb hba v (slJAt_root hJ hT))
    (fun p r m y hp hm => P.cap_userWr hb hba v (hC p r m y hp hm).1) hcl hroot hres
  rw [h] at back
  have e := ok_inj_ff back
  rw [hres, ← e]

/-- (slhuf gen 13) The source lookup from a cap whose CNode (if any) is in a closed walk set answers as at `s`
after a user write (`lts_userWr` for the source). -/
theorem lss_userWr (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) (hb : b ∈ K.user) (hba : Aligned b) (v : U64)
    {C : U64 → U64 → Prop}
    (hCs : ∀ p r m y, C p r → cspace.mask r = ok m → cnSlot p (y &&& m) ∈ K.slots)
    (hcl : WalkCl (st := st) s C) {root : capability.Cap} (hroot : ∀ p r g k, root = .CNode p r g k → C p r)
    (cptr depth : U64) :
    cspace.lookup_source_slot st (L.wr s b v) root cptr depth = cspace.lookup_source_slot st s root cptr depth := by
  obtain ⟨r, hr, -⟩ := spec_ex_fd (P0.cspace.lookup_source_slot.p0 st s root cptr depth L.total)
  rw [hr]
  unfold cspace.lookup_source_slot cspace.lookup_slot_for_cnode_op at hr ⊢
  obtain ⟨bb, eb, h⟩ := bind_eq_ok hr
  rw [eb]
  simp only [bind_ok]
  cases bb
  · simpa using h
  · have hcn : ∃ p r g k, root = .CNode p r g k := by cases root <;> simp at eb ⊢
    obtain ⟨cp, cr, cg, cgb, rfl⟩ := hcn
    have hc := hroot cp cr cg cgb rfl
    simp only [↓reduceIte] at h ⊢
    by_cases d1 : depth < 1#u64
    · rw [if_pos d1] at h ⊢; exact h
    rw [if_neg d1] at h ⊢
    by_cases d2 : depth > cspace.WORD_BITS
    · rw [if_pos d2] at h ⊢; exact h
    rw [if_neg d2] at h ⊢
    obtain ⟨res, eres, hl⟩ := bind_eq_ok h
    unfold cspace.resolve_address_bits at eres ⊢
    rw [rab_loop_congr2 st C (fun p r hp m hm y => P.cap_userWr hb hba v (hCs p r m y hp hm)) hcl 66 _ depth
      65#u64 res (by simp) (fun p r gs g e => by cases e; exact hc) eres]
    simp only [bind_ok]
    exact hl

set_option hygiene false in
/-- The Copy / Mint arm of `plan_with` after a user write (the two labels' arms are the same text). -/
local macro "cmw_arm" : tactic => `(tactic| (
    simp only [bind_ok, ↓reduceIte]
    rw [hs1]
    simp only [bind_ok]
    unfold obj.Slot.is_null
    by_cases h0 : s1 = 0#u64
    · simp [h0]
    · simp only [bind_ok, h0, decide_false, Bool.false_eq_true, ↓reduceIte, er0, er1, elts]
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
        obtain ⟨q2, r2, m2, y2, hq2, hm2, hs2⟩ := hex0 s1 hs1 h0
        have hs1K : s1 ∈ K.slots := by rw [hs2]; exact hCs q2 r2 m2 y2 hq2 hm2
        obtain ⟨rc, hrc, -⟩ := spec_ex_fd (P0.obj.Slot.cap.p0 st s1 s L.total)
        have hrcC : ∀ p r g k, rc = .CNode p r g k → C p r := fun p r g k e =>
          hcl q2 r2 m2 y2 p r g k hq2 hm2 (by rw [← hs2, ← e]; exact hrc)
        simp only [core.result.Result.ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, bind_ok,
          P.cap_userWr hb hba v hs1K, hrc, er2, er3, lss_userWr P hb hba v hCs hcl hrcC]
        obtain ⟨i2, hi2⟩ : ∃ i2, localinv.reg_arg st s (L.curW s) 2#u64 = ok i2 := by
          unfold localinv.reg_arg; rw [sarg2_reg, reg_ok]; exact ⟨_, rfl⟩
        obtain ⟨i3, hi3⟩ : ∃ i3, localinv.reg_arg st s (L.curW s) 3#u64 = ok i3 := by
          unfold localinv.reg_arg; rw [sarg3_reg, reg_ok]; exact ⟨_, rfl⟩
        rw [hi2, hi3]
        simp only [bind_ok]
        obtain ⟨r1, hr1, -⟩ := spec_ex_fd (P0.cspace.lookup_source_slot.p0 st s rc i2 i3 L.total)
        rw [hr1]
        simp only [bind_ok]
        cases r1 with
        | Err e =>
          simp only [core.result.Result.ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, bind_ok]
        | Ok src =>
          obtain ⟨q3, r3, m3, y3, hq3, hm3, hs3⟩ := lss_cn hrcC hcl hr1
          have hsK : src ∈ K.slots := by rw [hs3]; exact hCs q3 r3 m3 y3 hq3 hm3
          obtain ⟨h8, hf⟩ := P.lay.slot8 _ hdK
          obtain ⟨h8', hf'⟩ := P.lay.slot8 _ hsK
          have hv0 : (core.num.U64.wrapping_add (cnSlot q (y &&& m)) layout.cte.CAP0).val =
              (cnSlot q (y &&& m)).val := by
            generalize cnSlot q (y &&& m) = d at hf ⊢
            first
              | (simp [core.num.U64.wrapping_add_val_eq, layout.cte.CAP0, U64.size_def, U64.numBits]; done)
              | (simp [core.num.U64.wrapping_add_val_eq, layout.cte.CAP0, U64.size_def, U64.numBits]; omega)
          have hvN : (core.num.U64.wrapping_add src layout.cte.NEXT).val = src.val + 24 := by
            simp [core.num.U64.wrapping_add_val_eq, layout.cte.NEXT, U64.size_def, U64.numBits]; omega
          have eC0 := planRead_userWr (st := st) (s := s) hb hba v
            (a := core.num.U64.wrapping_add (cnSlot q (y &&& m)) layout.cte.CAP0)
            (by unfold Aligned; omega) (P.slotW_nu hdK ⟨by omega, by omega⟩)
          have eNx := planRead_userWr (st := st) (s := s) hb hba v (a := core.num.U64.wrapping_add src layout.cte.NEXT)
            (by unfold Aligned; omega) (P.slotW_nu hsK ⟨by omega, by omega⟩)
          simp only [core.result.Result.ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, bind_ok, lift,
            planReadCap_userWr P hb hba v hsK, eC0, eNx]))

set_option maxHeartbeats 4000000 in
/-- (slhuf gen 13) **`plan_with` at `CNodeCopy` / `CNodeMint` answers alike after a user write** (module
docstring), at a bundle state with `IoPre`: the invoked slot a capability slot with a CNode cap of a closed walk set
`C`, the first extra cap (when not null) a radix-masked slot of a `C` CNode. -/
theorem planCM_userWr (hJ : SlJAt (L := L) K s)
    (P : IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hb : b ∈ K.user) (hba : Aligned b) (v : U64) {sl : obj.Slot} (hsl : sl ∈ K.slots)
    {cp cr cg cgb : U64} (hcap : obj.Slot.cap st sl s = ok (.CNode cp cr cg cgb)) {C : U64 → U64 → Prop}
    (hC : C cp cr) (hcl : WalkCl (st := st) s C)
    (hCs : ∀ p r m y, C p r → cspace.mask r = ok m → cnSlot p (y &&& m) ∈ K.slots)
    (ex : Array obj.Slot 3#usize)
    (hex0 : ∀ s1, Aeneas.Std.Array.index_usize ex 0#usize = ok s1 → s1 ≠ 0#u64 →
      ∃ q r m y, C q r ∧ cspace.mask r = ok m ∧ s1 = cnSlot q (y &&& m))
    {lbl : U64} (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint) :
    localinv.plan_with st (L.wr s b v) (L.curW s) lbl sl ex = localinv.plan_with st s (L.curW s) lbl sl ex := by
  have hT : K.heap (L.curW s) = some .tcb := P.cT
  have e10 := tcbReg_wr hJ hb hba v hT P.tA (r := layout.reg.R10) (by simp [layout.reg.R10])
  have e8 := tcbReg_wr hJ hb hba v hT P.tA (r := layout.reg.R8) (by simp [layout.reg.R8])
  have e9 := tcbReg_wr hJ hb hba v hT P.tA (r := layout.reg.R9) (by simp [layout.reg.R9])
  have e15 := tcbReg_wr hJ hb hba v hT P.tA (r := layout.reg.R15) (by simp [layout.reg.R15])
  have er0 : localinv.reg_arg st (L.wr s b v) (L.curW s) 0#u64 = localinv.reg_arg st s (L.curW s) 0#u64 := by
    unfold localinv.reg_arg; rw [sarg0_reg, sarg0_reg, reg_ok, reg_ok, e10]
  have er1 : localinv.reg_arg st (L.wr s b v) (L.curW s) 1#u64 = localinv.reg_arg st s (L.curW s) 1#u64 := by
    unfold localinv.reg_arg; rw [sarg1_reg, sarg1_reg, reg_ok, reg_ok, e8]
  have er2 : localinv.reg_arg st (L.wr s b v) (L.curW s) 2#u64 = localinv.reg_arg st s (L.curW s) 2#u64 := by
    unfold localinv.reg_arg; rw [sarg2_reg, sarg2_reg, reg_ok, reg_ok, e9]
  have er3 : localinv.reg_arg st (L.wr s b v) (L.curW s) 3#u64 = localinv.reg_arg st s (L.curW s) 3#u64 := by
    unfold localinv.reg_arg; rw [sarg3_reg, sarg3_reg, reg_ok, reg_ok, e15]
  have elts : ∀ cptr depth, cspace.lookup_target_slot st (L.wr s b v) (.CNode cp cr cg cgb) cptr depth =
      cspace.lookup_target_slot st s (.CNode cp cr cg cgb) cptr depth := by
    intro cptr depth
    obtain ⟨r, hr, -⟩ := spec_ex_fd (P0.cspace.lookup_target_slot.p0 st s (.CNode cp cr cg cgb) cptr depth L.total)
    rw [hr, lts_userWr P hb hba v hCs hcl hC hr]
  have hlen : ex.val.length = 3 := by have hp := ex.property; simpa using hp
  obtain ⟨s1, hs1⟩ : ∃ s1, Aeneas.Std.Array.index_usize ex 0#usize = ok s1 :=
    ⟨_, eq_of_spec_fd (Aeneas.Std.Array.index_usize_spec ex 0#usize
      (by simp only [Aeneas.Std.Array.length]; first | omega | (simp; omega) | simp))⟩
  unfold localinv.plan_with
  rw [P.cap_userWr hb hba v hsl, hcap]
  rcases hl with rfl | rfl
  · simp only [bind_ok, localinv.Plan.new]
    cmw_arm
  · simp only [bind_ok, localinv.Plan.new, if_neg lbl_mint_ne_copy]
    cmw_arm

/-- (slhuf gen 13) **`InvExW` is kept by a user write** at a bundle state with `IoPre` and the Copy / Mint label. -/
theorem invExW_wr (hJ : SlJAt (L := L) K s)
    (P : IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    {p : localinv.Plan} (hx : InvExW st p s) (harm : InvCMArm st s) (hlk : InvLk st p s)
    (hb : b ∈ K.user) (hba : Aligned b) (v : U64) : InvExW st p (L.wr s b v) := by
  obtain ⟨info, ei, hpw, hlec⟩ := hx
  have hT : K.heap (L.curW s) = some .tcb := P.cT
  have ecur := hJ.curW_wr hb hba v
  have hl := harm _ _ (cur_thread_ok s) ei
  obtain ⟨C, hroot, hcl, hC⟩ := P.walk
  obtain ⟨x, hx, hxs⟩ := hlk
  obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, -, -, -, -, -, hcap, hex, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    plan_with_cmF hl hpw
  obtain ⟨q0, r0, m0, y0, hq0, hm0, hs0⟩ := lookup_slot_cn hroot hcl hx
  rw [hxs] at hs0
  have hCc : C cp cr := hcl q0 r0 m0 y0 cp cr cg cgb hq0 hm0 (by rw [← hs0]; exact hcap)
  have hsl : p.slot ∈ K.slots := by rw [hs0]; exact (hC q0 r0 m0 y0 hq0 hm0).1
  have hex0 : ∀ s1, Aeneas.Std.Array.index_usize p.extra 0#usize = ok s1 → s1 ≠ 0#u64 →
      ∃ q r m y, C q r ∧ cspace.mask r = ok m ∧ s1 = cnSlot q (y &&& m) := by
    intro s1 h1 h0
    obtain ⟨c2, x2, hx2, hxs2⟩ := hlec s1 h1 h0
    obtain ⟨q2, r2, m2, y2, hq2, hm2, hs2⟩ := lookup_slot_cn hroot hcl hx2
    exact ⟨q2, r2, m2, y2, hq2, hm2, by rw [← hxs2]; exact hs2⟩
  refine ⟨info, ?_, ?_, ?_⟩
  · rw [ecur, msgInfo_wr hJ hb hba v hT P.tA]; exact ei
  · rw [ecur, planCM_userWr hJ P hb hba v hsl hcap hCc hcl (fun p r m y hp hm => (hC p r m y hp hm).1) p.extra
      hex0 hl]
    exact hpw
  · intro s1 h1 h0
    obtain ⟨c2, x2, hx2, hxs2⟩ := hlec s1 h1 h0
    exact ⟨c2, x2, by rw [ecur]; exact lookupSlot_userWr hJ P hb hba v hx2, hxs2⟩

end wr

/-! ## `huf` -/

section huf
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {Cs Ω Sg Ac : Set U64}

/-- (slhuf gen 13) **The `huf` of the Copy / Mint path** at `Pre := SlJAt K ∧ InvQCMW …`, from [J] `hIw`
(`IoPre` survives a user write at a bundle state) and [P] `hlk` (the locks are kept) — invj's `hufQF_of2` shape. -/
theorem hufQCMW_of {Locks : S → U64 → Prop} {p : localinv.Plan}
    (hIw : ∀ K s b v, SlJAt (L := L) K s →
      IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s →
      b ∈ K.user → Aligned b →
      IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac (L.wr s b v))
    (hlk : ∀ K s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s) :
    ∀ K m s b v, SlJAt (L := L) K s → InvQCMW st Cs Ω Sg Ac Locks p K m s → b ∈ K.user → Aligned b →
      (SlJAt (L := L) K (L.wr s b v) ∧ InvQCMW st Cs Ω Sg Ac Locks p K m (L.wr s b v)) ∧
        Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s := by
  intro K m s b v hJ hq hb hba
  obtain ⟨⟨hio, hpd, harm, hlks⟩, hlk0, hx⟩ := hq
  have P := hio.1
  have hT : K.heap (L.curW s) = some .tcb := P.cT
  have el := hlk K s b v hJ hb hba
  have ecur := hJ.curW_wr hb hba v
  have emsg := msgInfo_wr hJ hb hba v hT P.tA
  have hct : ∀ t, sched.cur_thread st (L.wr s b v) = ok t → t = L.curW s := by
    intro t ht
    rw [cur_thread_ok, ecur] at ht
    exact (ok_inj_ff ht).symm
  have hx' := invExW_wr hJ P hx harm hlk0 hb hba v
  have hpd' : InvPlanD st p (L.wr s b v) := by
    obtain ⟨info, ei, hpw, -⟩ := hx'
    exact ⟨L.curW (L.wr s b v), info, p.extra, cur_thread_ok _, ei, hpw⟩
  refine ⟨⟨hJ.userWr hb v, ⟨ioQ_wr hIw K m s b v hJ hio hb hba, hpd', ?_, ?_⟩,
    invLk_wr hJ P hlk0 hb hba v, hx'⟩, el, hJ.ioRWDS_wrSt hb hba v el⟩
  · intro t info ht hi
    obtain rfl := hct t ht
    rw [emsg] at hi
    exact harm _ info (cur_thread_ok s) hi
  · intro i x hi hx
    rw [el]
    exact hlks i x hi hx

end huf

end Fl4Proofs.P2.PathObl
