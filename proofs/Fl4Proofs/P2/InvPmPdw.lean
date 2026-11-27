/-
# P2 (line pte, generation 13): `pdw` of the PageMap slot — the plan survives a user write

Gen 12's [J] `pdw` (`PmPdw`): at a `PmPreF` state, `InvPlanD` (`plan_with` at `X86PageMap` gives the plan) holds
after an aligned user-word write. `plan_with`'s PageMap arm reads

* the invoked slot's cap (twice: the arm's `cap` and `Plan.read_cap`): a capability slot (`IoPre.cap_userWr`,
  `planReadCap_userWr`);
* `extra[0]`'s cap: **a capability slot only if `extra[0]` is one** — new start fact **`PmEx`** (`extra[0]` is a slot
  the current thread's `lookup_slot` finds), satisfiable from the glue's plan (**`pmEx_of_plan`**: `lookup_extra_caps`
  puts only `lookup_slot` results or `0` into the array, `lookup_extra_loop_slot`, and the arm needs `extra[0] ≠ 0`),
  stable under user writes (`pmEx_wr`, `lookup_slot_back`), and in `K.slots` (`pmEx_slots`, the CSpace walk set);
* the message registers `R10` / `R9` (TCB words, `tcbReg_wr`);
* the page-table walk `page_entry root vaddr` from the PML4 cap's `root`. P3 puts `root` in `Zx.L4` only while the ASID
  table reaches it (`VsCapW` for a mapped PML4 cap: `(mp = false → p ∈ L4)`; deleting an ASID pool's last cap leaves
  an orphaned mapped PML4 behind, KENTRY-PLAN jc4), and the walk from a table outside the VSpace sets may read any
  word (entries of an orphaned PML4 are not cleared when a PDPT under it is deleted, since the unmap's ASID lookup
  fails; the freed PDPT may become a user frame). So **`pdw` is not true at every `PmPreF` state**; it is true where
  the PML4 cap is not orphaned: new start fact **`PmRoot`** (the cap's ASID finds `root`, exactly what
  `check_vspace` in `decode_page_map` tests), stable under user writes (`pmRoot_wr`, `find_vspace_for_asid_ag`).
  With it `root ∈ Zx.L4` (`find_vspace_for_asid_L4`) and the walk reads only `VObj` words, none of them a user word
  (`pageEntry_userWr`, from P3's `lookup_pt_slot_ag` / `JAtZ.userNotVObj`).

**Coverage**: `PmRoot` is not implied by the plan (the plan does not look at the ASID table): a PageMap whose PML4
cap is orphaned is planned, then fails in `check_vspace`; the narrowed start fact leaves those runs out.

* **`planMap_userWr`**: `plan_with` at `X86PageMap` answers alike after a user write (given the arm's PML4 cap and
  `PmRoot`);
* **`PmPreG`** = `PmPreF ∧ PmEx ∧ PmRoot`, **`pm_pdwG`**: `InvPlanD` after a user write at a `PmPreG` state (gen 12's
  `pdw`, no premise).

No named premise. New module; no existing statement changes.
-/
import Fl4Proofs.P2.InvPmU
import Fl4Proofs.P2.InvPD
import Fl4Proofs.P3.IpcGrant
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP

noncomputable section

/-! ## The extra caps -/

section extra
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- A slot the thread's `lookup_slot` finds, or `0`. -/
def LkOr0 (st : machine.Store S) (s : S) (t x : U64) : Prop :=
  x = 0#u64 ∨ ∃ c r1, cspace.lookup_slot st s t c = ok (.Ok r1) ∧ r1.slot = x

/-- **`lookup_extra_caps`' loop puts only `lookup_slot` results (or `0`) at index 0.** -/
theorem lookup_extra_loop_slot (s : S) (t buf n : U64) :
    ipc.lookup_extra_caps_loop st s t buf ipc.NO_EXTRA_CAPS n 0#u64 ⦃ r => ∀ e, r = .Ok e →
      LkOr0 st s t (Fl4Proofs.P3.Ipc.exAt e 0) ⦄ := by
  unfold ipc.lookup_extra_caps_loop
  refine loop.spec_decr_nat (fun x => 3 - x.2.val)
    (fun x => LkOr0 st s t (Fl4Proofs.P3.Ipc.exAt x.1 0)) _ _ _ (fun x hx => ?_) ?_
  · obtain ⟨arr, i⟩ := x
    dsimp only at hx ⊢
    unfold ipc.lookup_extra_caps_loop.body
    by_cases hin : i < n
    · by_cases hi3 : i < 3#u64
      · have hi3' : i.val < 3 := by scalar_tac
        rw [if_pos hin, if_pos hi3, Fl4Proofs.P3.Ipc.buf_caps_eq]
        simp only [lift, bind_ok]
        obtain ⟨w, hw, -⟩ := spec_ex_fd (P0.msg.buf_get.p0 st s buf (core.num.U64.wrapping_add 122#u64 i) L.total)
        rw [hw, bind_ok]
        obtain ⟨r, hr, -⟩ := spec_ex_fd (P0.cspace.lookup_slot.p0 st s t w L.total)
        rw [hr, bind_ok]
        cases r with
        | Ok r1 =>
          simp only []
          obtain ⟨a', ha', ha'v⟩ := Fl4Proofs.P3.spec_exists (Aeneas.Std.Array.update_spec arr (UScalar.cast .Usize i) r1.slot
            (by have hl : arr.val.length = 3 := by simpa using arr.property
                rw [Fl4Proofs.P3.Ipc.cast_us_val i hi3']; simp [Aeneas.Std.Array.length, hl]; omega))
          rw [ha']
          simp only [bind_ok]
          obtain ⟨i4, h4e, h4v⟩ := Fl4Proofs.P3.spec_exists (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
          rw [h4e, bind_ok, WP.spec_ok]
          have hi4 : i4.val = i.val + 1 := by simpa using h4v
          subst ha'v
          refine ⟨?_, by rw [hi4]; omega⟩
          show LkOr0 st s t (Fl4Proofs.P3.Ipc.exAt (arr.set (UScalar.cast .Usize i) r1.slot) 0)
          rw [Fl4Proofs.P3.Ipc.exAt_set, Fl4Proofs.P3.Ipc.cast_us_val i hi3']
          by_cases h0 : i.val = 0
          · rw [if_pos ⟨h0, by omega⟩]; exact Or.inr ⟨w, r1, hr, rfl⟩
          · rw [if_neg (fun h => h0 h.1)]; exact hx
        | Err lf =>
          simp only [WP.spec_ok]
          intro e he
          cases he
      · rw [if_pos hin, if_neg hi3, WP.spec_ok]
        intro e he
        cases he
        exact hx
    · rw [if_neg hin, WP.spec_ok]
      intro e he
      cases he
      exact hx
  · exact Or.inl (Fl4Proofs.P3.Ipc.exAt_none 0 (by omega))

/-- **`lookup_extra_caps` puts only `lookup_slot` results (or `0`) at index 0.** -/
theorem lookup_extra_slot {s : S} {t buf : U64} {info : msginfo.MessageInfo} {e : Array obj.Slot 3#usize}
    (h : ipc.lookup_extra_caps st s t buf info = ok (.Ok e)) : LkOr0 st s t (Fl4Proofs.P3.Ipc.exAt e 0) := by
  unfold ipc.lookup_extra_caps at h
  by_cases hb : buf = 0#u64
  · rw [if_pos hb] at h
    have e' := ok_inj_ff h
    cases e'
    exact Or.inl (Fl4Proofs.P3.Ipc.exAt_none 0 (by omega))
  · rw [if_neg hb] at h
    obtain ⟨r, hr, hp⟩ := spec_ex_fd (lookup_extra_loop_slot (st := st) s t buf info.extra_caps)
    rw [h] at hr
    have e' := ok_inj_ff hr
    subst e'
    exact hp e rfl

variable (st) in
/-- **The arm's `extra[0]` is a slot the current thread's `lookup_slot` finds** (start fact). -/
def PmEx (p : localinv.Plan) (s : S) : Prop :=
  ∃ x, Array.index_usize p.extra 0#usize = ok x ∧ ∃ c r1, cspace.lookup_slot st s (L.curW s) c = ok (.Ok r1) ∧
    r1.slot = x

/-- **`PmEx` from the glue's plan** (satisfiability): `lookup_extra_caps`' array holds only lookups or `0` at index
0, and the PageMap arm needs `extra[0] ≠ 0`. -/
theorem pmEx_of_plan {s : S} {n : I64} {p : localinv.Plan} (hp : localinv.plan st s n = ok (some p))
    (harm : PmArm st s) : PmEx st p s := by
  obtain ⟨t, info, cptr, r, buf, e, et, ei, -, -, -, ex, hpw⟩ := plan_fieldsW hp
  have ht : t = L.curW s := ok_inj_ff (et.symm.trans (cur_thread_ok s))
  subst ht
  obtain ⟨hlbl, -⟩ := harm _ info (cur_thread_ok s) ei
  rw [hlbl] at hpw
  obtain ⟨-, -, -, -, -, -, -, x, -, -, hx, hx0, -⟩ := plan_with_mapF hpw
  have hkp := (plan_with_kp hpw).2
  have hx' : x = Fl4Proofs.P3.Ipc.exAt e 0 := by
    rw [Fl4Proofs.P3.Ipc.index_exAt e 0#usize (by simp)] at hx; simpa using (ok_inj_ff hx).symm
  refine ⟨x, by rw [hkp]; exact hx, ?_⟩
  rcases lookup_extra_slot ex with h0 | h
  · exact absurd (hx'.trans h0) hx0
  · rw [hx']; exact h

end extra

/-! ## Stability under a user write -/

section wr
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : OwnMap.KLayout} {s : S} {b : U64}
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}

/-- `PmEx`'s slot is a capability slot (the CSpace walk set). -/
theorem pmEx_slots (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) {p : localinv.Plan} (h : PmEx st p s) :
    ∃ x, Array.index_usize p.extra 0#usize = ok x ∧ x ∈ K.slots := by
  obtain ⟨x, hx, c, r1, hl, hs⟩ := h
  obtain ⟨C, hroot, hcl, hC⟩ := P.walk
  obtain ⟨q0, r0, m0, y0, hq0, hm0, hs0⟩ := lookup_slot_cn hroot hcl hl
  exact ⟨x, hx, by rw [← hs, hs0]; exact (hC q0 r0 m0 y0 hq0 hm0).1⟩

/-- **`PmEx` is kept by a user write** (as `invLk_wr`). -/
theorem pmEx_wr (hJ : SlJAt (L := L) K s)
    (P : IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    {p : localinv.Plan} (hl : PmEx st p s) (hb : b ∈ K.user) (hba : Aligned b) (v : U64) :
    PmEx st p (L.wr s b v) := by
  obtain ⟨x, hx, c, r1, hr1, hs⟩ := hl
  have hT : K.heap (L.curW s) = some .tcb := P.cT
  have ecur := hJ.curW_wr hb hba v
  obtain ⟨C, hroot, hcl, hC⟩ := P.walk
  obtain ⟨res, hres, -⟩ := spec_ex_fd (P0.cspace.lookup_slot.p0 st (L.wr s b v) (L.curW s) c L.total)
  have back := lookup_slot_back (tcb_slot_ctable (L.curW s))
    (P.cap_userWr hb hba v (slJAt_root hJ hT))
    (fun p r m y hp hm => P.cap_userWr hb hba v (hC p r m y hp hm).1) hcl hroot hres
  rw [hr1] at back
  have e := ok_inj_ff back
  subst e
  exact ⟨x, hx, c, r1, by rw [ecur]; exact hres, hs⟩

/-- Two states a user write apart agree on the VSpace objects (`JAtZ.userNotVObj`). -/
theorem vsAg_userWr {A' : Type} {arI : machine.Arch A'} {AR : A' → Fl4Spec.Cr3 → Prop} {Zx : Fl4Proofs.P3.XSets}
    {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64} {a' : A'} {σ : Fl4Spec.State Unit}
    (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) (hb : b ∈ K.user) (hba : Aligned b) (v : U64) :
    Fl4Proofs.P3.Vs.VsAg (L := L) Zx.th Zx.P Zx.L4 Zx.L3 Zx.L2 Zx.L1 (L.wr s b v) s := by
  have hb' := hb
  rw [B.user] at hb'
  obtain ⟨wp, hwB, ewp⟩ := hb'
  subst ewp
  exact ⟨L.ksb_wr s wp.1 v, fun a ha hal => mem_wr_ne' hba hal (fun e => B.j.userNotVObj hwB (e ▸ ha))⟩

/-- **The walk from a root the ASID table names reads no user word** (P3's `lookup_pt_slot_ag`). -/
theorem pageEntry_userWr (hJ : SlJAt (L := L) K s) (hb : b ∈ K.user) (hba : Aligned b) (v : U64) {asid root : U64}
    (hf : vspace.find_vspace_for_asid st s asid = ok (.Ok root)) (va : U64) :
    localinv.page_entry st (L.wr s b v) root va = localinv.page_entry st s root va := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := id hJ
  have hA := vsAg_userWr B hb hba v
  obtain ⟨hSR, hVs, hPt, hPI, -⟩ := B.j.xtop.fin
  have hTP := hSR.2
  have hroot : root ∈ Zx.L4 := by
    obtain ⟨r, hr, hL4⟩ := spec_ex_fd (Fl4Proofs.P3.Vs.find_vspace_for_asid_L4 (st := st) s σ hVs hPI asid)
    rw [hf] at hr
    exact hL4 root (ok_inj_ff hr).symm
  unfold localinv.page_entry
  by_cases hu : va > fl4_abi.consts.USER_TOP
  · rw [if_pos hu, if_pos hu]
  · rw [if_neg hu, if_neg hu]
    unfold vspace.small_page_entry
    rw [Fl4Proofs.P3.Vs.lookup_pt_slot_ag hA hPt hTP.pt hroot va (userV_of_not_gt hu)]

variable (st) in
/-- **The arm's PML4 cap is not orphaned** (start fact): its ASID finds its root (what `check_vspace` tests). -/
def PmRoot (p : localinv.Plan) (s : S) : Prop :=
  ∀ x root rasid, Array.index_usize p.extra 0#usize = ok x → obj.Slot.cap st x s = ok (.Pml4 root true rasid) →
    vspace.find_vspace_for_asid st s rasid = ok (.Ok root)

/-- **`PmRoot` is kept by a user write** (`find_vspace_for_asid_ag`). -/
theorem pmRoot_wr (hJ : SlJAt (L := L) K s)
    (P : IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    {p : localinv.Plan} (hx : PmEx st p s) (hr : PmRoot st p s) (hb : b ∈ K.user) (hba : Aligned b) (v : U64) :
    PmRoot st p (L.wr s b v) := by
  intro x root rasid hx' hc
  obtain ⟨x0, hx0, hxK⟩ := pmEx_slots P hx
  rw [hx0] at hx'
  have e := ok_inj_ff hx'
  subst e
  rw [P.cap_userWr hb hba v hxK] at hc
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := id hJ
  obtain ⟨hSR, hVs, -, -, -⟩ := B.j.xtop.fin
  rw [Fl4Proofs.P3.Vs.find_vspace_for_asid_ag (vsAg_userWr B hb hba v) hVs hSR.2.vs]
  exact hr x0 root rasid hx0 hc

theorem sarg2_reg (s : S) (t buf : U64) :
    msg.syscall_arg st s t buf 2#u64 = obj.Tcb.reg st t s layout.reg.R9 := by
  unfold msg.syscall_arg
  rw [if_pos (by simp [msg.N_MSG_REGISTERS])]
  simp [msg.msg_register]

/-- **`plan_with` at `X86PageMap` answers alike after a user write** (module docstring), at a bundle state with
`IoPre`, for a capability slot `sl`, an `extra[0]` in `K.slots` holding a mapped PML4 cap whose root the ASID
table names. -/
theorem planMap_userWr (hJ : SlJAt (L := L) K s)
    (P : IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hb : b ∈ K.user) (hba : Aligned b) (v : U64) {sl : obj.Slot} (hsl : sl ∈ K.slots)
    {ex : Array obj.Slot 3#usize} {x : obj.Slot} (hx : Array.index_usize ex 0#usize = ok x) (hxK : x ∈ K.slots)
    {root rasid : U64} (hcx : obj.Slot.cap st x s = ok (.Pml4 root true rasid))
    (hf : vspace.find_vspace_for_asid st s rasid = ok (.Ok root)) :
    localinv.plan_with st (L.wr s b v) (L.curW s) fl4_abi.label.X86PageMap sl ex =
      localinv.plan_with st s (L.curW s) fl4_abi.label.X86PageMap sl ex := by
  have hT : K.heap (L.curW s) = some .tcb := P.cT
  have e10 := tcbReg_wr hJ hb hba v hT P.tA (r := layout.reg.R10) (by simp [layout.reg.R10])
  have e9 := tcbReg_wr hJ hb hba v hT P.tA (r := layout.reg.R9) (by simp [layout.reg.R9])
  have er0 : localinv.reg_arg st (L.wr s b v) (L.curW s) 0#u64 = localinv.reg_arg st s (L.curW s) 0#u64 := by
    unfold localinv.reg_arg; rw [sarg0_reg, sarg0_reg, reg_ok, reg_ok, e10]
  have er2 : localinv.reg_arg st (L.wr s b v) (L.curW s) 2#u64 = localinv.reg_arg st s (L.curW s) 2#u64 := by
    unfold localinv.reg_arg; rw [sarg2_reg, sarg2_reg, reg_ok, reg_ok, e9]
  have ecx := P.cap_userWr hb hba v hxK
  have hpe := pageEntry_userWr (st := st) hJ hb hba v hf
  have efind : vspace.find_vspace_for_asid st (L.wr s b v) rasid = vspace.find_vspace_for_asid st s rasid := by
    obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := id hJ
    obtain ⟨hSR, hVs, -, -, -⟩ := B.j.xtop.fin
    exact Fl4Proofs.P3.Vs.find_vspace_for_asid_ag (vsAg_userWr B hb hba v) hVs hSR.2.vs rasid
  unfold localinv.plan_with
  rw [P.cap_userWr hb hba v hsl]
  simp only [bind_ok, if_neg lbl_map_ne_copy, if_neg lbl_map_ne_mint, if_neg lbl_map_ne_del, er0, er2,
    planReadCap_userWr P hb hba v hsl, hx, ecx, hcx, hpe, efind]

end wr

/-! ## `pdw` at the narrowed start fact -/

section pdw
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}

variable (st) in
/-- **The PageMap path's start fact with `PmEx` and `PmRoot`** (module docstring). -/
def PmPreG (Cs Ω Sg Ac : Set U64) (Locks : S → U64 → Prop) (p : localinv.Plan) (K : KLayoutP) (m : U64 → U64)
    (s : S) : Prop :=
  PmPreF st Cs Ω Sg Ac Locks p K m s ∧ PmEx st p s ∧ PmRoot st p s

/-- **`pdw` at `PmPreG`** (gen 12's [J] `pdw`, proved): `InvPlanD` survives a user write. -/
theorem pm_pdwG : ∀ (j : I64 × localinv.Plan) (K : KLayoutP) m s b v, PmPreG st Cs Ω Sg Ac Locks j.2 K m s →
    b ∈ K.user → Aligned b → InvPlanD st j.2 (L.wr s b v) := by
  rintro j K m s b v ⟨⟨hJ, hq, -⟩, hEx, hR⟩ hb hba
  have hq0 := hq
  obtain ⟨⟨hio, ⟨t, info, ex, ht, hi, hpw⟩, harm, -⟩, -⟩ := hq0
  have P := hio.1
  have hT : K.heap (L.curW s) = some .tcb := P.cT
  have et : t = L.curW s := by rw [cur_thread_ok] at ht; exact (ok_inj_ff ht).symm
  subst et
  have hlbl := (harm _ info (cur_thread_ok s) hi).1
  rw [hlbl] at hpw
  obtain ⟨-, -, -, -, -, -, hsK, -, -, -⟩ := pm_core hq
  obtain ⟨x, hx, hxK⟩ := pmEx_slots P hEx
  have hkp := plan_with_kp hpw
  obtain ⟨-, -, -, -, root, rasid, -, x0, -, -, hx0, -, hcx, -⟩ := plan_with_mapF hpw
  rw [← hkp.2, hx] at hx0
  obtain rfl := ok_inj_ff hx0
  refine ⟨L.curW s, info, ex, ?_, ?_, ?_⟩
  · rw [cur_thread_ok, hJ.curW_wr hb hba v]
  · rw [msgInfo_wr hJ hb hba v hT P.tA]; exact hi
  · rw [hlbl, planMap_userWr hJ P hb hba v hsK (by rw [← hkp.2]; exact hx) hxK hcx (hR x root rasid hx hcx)]
    exact hpw

end pdw

end
end Fl4Proofs.P2.E2EP
