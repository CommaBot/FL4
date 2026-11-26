/-
# P2 (line vmscope, gen 9): the invocation entry's user-write closure proved — `serializable_fl4_localVX9`

`serializable_fl4_localVX8` (P2/E2EPVX8.lean) runs CNodeDelete (no PTE lock) and Copy / Mint in VM epochs with the
start entry `InvEntV` [S], whose field `cl` asks, **at every state reached from the start by aligned user-word
writes** (`UReach`), the kernel-word facts `InvLXS` (`cdt`, `buf8`, `bufS8`, `vs`) and U1's entry fact (`InvQF ∧ VsXW`
resp. `InvQCMW`). At native states that closure is a theorem (`SlJAt.userWr`, `hufQF_of2`, `hufQCMW_of`), proved
through P3's bundle (`SlJAt.tcbW_wr`, `SlJAt.curW_wr`, `slJAt_root`, `JAtZ.smallPageEntry_userWr`) and the [J]
`hIw`. This module proves it in VM epochs from the epoch's layout facts alone, so the start entry only asks the
facts **at the start state**.

## 1. Frame lemmas without a P3 bundle (`PathObl`)
* `tcbReg_wrP`, `msgInfo_wrP` (the current thread's registers: `IoPre.reg`), `curW_wrP` (VX8's `curW_wrI`),
  `rootSlot_of` (CTable slot: `IoLay.tslot`), `ioQ_wrX` (VX5's `ioPre_wrL` + `nu_tcb`: **no `hIw`**).
* The walk: `vsRdG_trX` (copy of unify's `vsRdG_tr`, P2/InvPmWalk.lean, not an ancestor here), `spe_congrX`
  (`small_page_entry` from its two lookups), **`vsRdG_wrX`**: a walk reading only words `V` that the write keeps is
  itself kept, with the same `small_page_entry` (this replaces P3's `JAtZ.smallPageEntry_userWr`: the walk facts
  `vs` / `VsXW` already say which words it reads, and those are no user words).
* Copies with `SlJAt` replaced by `IoPre` (+ `UserLayX` for `curW`): `invLk_wrX` (`invLk_wr`), `planDel_userWrX`
  (`planDel_userWr`, its `small_page_entry` read through the walk fact of the target's frame cap, `hspe`, instead of
  P3's unconditional `smallPageEntry_userWr`), `invPlanD_wrFX` (`invPlanD_wrF`), `lookupSlot_userWrX`,
  `planCM_userWrX` (`planCM_userWr`), `invExW_wrX` (`invExW_wr`).
* Closures under one write: **`invLXS_wrX`** (`InvLXS`: CDT words and caps are slot words, the IPC-buffer lookup
  reads TCB words and a TCB slot, `vs` by `vsRdG_wrX`), **`vsXW_wrX`**, **`invQF_wrX`** (`hufQF_of2`'s body),
  **`invQCMW_wrX`** (`hufQCMW_of`'s body), the locks kept by hypothesis.
* `ureach_cl`: closure along `UReach` of a property whose one-write step may use the closure of a lock-free part.

## 2. Start facts and tops (`E2EP`)
* Start entry **`InvEntV9 K G s`** [S]: `hz`, `ent : InvLXS ∧ G` **at the start state only**, `qps`.
* **`invEntV_of9D`** / **`invEntV_of9C`**: `InvEntV9` + the epoch's `VtxBundle4` + `InvPremX.lk` [P] + the index's
  core range ⇒ VX8's `InvEntV` (its `cl` proved: `ureach_cl` with the lock-free part `InvLXS ∧ IoPre`, the locks by
  `lk` at `InvLX (fun _ => True)` states, which that part gives).
* `InvStartX9` / `CMStartX9` (VX8's start facts with `InvEntV9` and the index convention `cs : ∀ c ∈ j.Cs, c.val <
  K.ncores`, as VX5's `IoPremX5.hCs`), `invStartX_of9` / `cmStartX_of9`, `StartVX9`, `serializable_fl4_localVX9G`,
  **`serializable_fl4_localVX9`** (VX8's family; same paths and slots).

## Premise diff vs `serializable_fl4_localVX8`
| where | VX8 | VX9 |
|---|---|---|
| CNodeDelete / Copy-Mint start entry | `InvEntV.cl` [S]: `InvLXS ∧ G` at **every** `UReach` state | `InvEntV9.ent` [S]: `InvLXS ∧ G` at the start state; the closure is the theorem `invEntV_of9D` / `invEntV_of9C` |
| | `InvEntV.hz`, `InvEntV.qps` [S] | unchanged (`InvEntV9.hz`, `InvEntV9.qps`) |
| index | — | convention `cs : ∀ c ∈ j.Cs, c.val < K.ncores` (as `IoPremX5.hCs`; natively `InvPremW.hCs` from the bundle's `csLt`) |
| everything else | | unchanged |
No new [J], no [W], no new [S].

## What remains in the start entry, and why (Rust: fl4-core `cspace.rs`, `msg.rs`, `localinv.rs`,
`arch/x86_64/vspace.rs`, `arch/x86_64/objects.rs`)
The remaining fields are facts about the **kernel words of the start state** that only P3's invariant gives
natively; P3 has no guest-running state (`JExt.vw`), so they stay [S], each the fact P3 gives at the last native
state, unchanged by the guest (a guest writes only its VCPU's data words and guest frames, `HwStepP`; VCPUs are
`bits::VCPU` objects, never frames, slots, TCBs or paging structures):
* `hz`: no capability slot at address 0 (untyped retype never places an object at 0; natively `slJAt_slot0`).
  A layout fact; not derivable from `RegionOK` / `UserLayX` (they say nothing about address 0).
* `ent.1.cdt`: CDT links name capability slots (`mdb_insert` / `mdb_remove`; natively `slJAt_cdt`). A heap invariant.
* `ent.1.buf8` / `bufS8`: the caller's IPC buffer (`lookup_ipc_buffer`, the `SLOT_BUFFER` frame cap) is user frame
  memory (natively `JAtZ.bufOK` / `xferH`). A cap-content invariant.
* `ent.1.vs`, `VsXW`: a mapped small frame cap's walk (`find_vspace_for_asid`, `lookup_pt_slot`) reads only
  ASID-table / pool / paging-structure words, no user, VCPU or leaf-PTE word (natively `invVsJ_of`, `SlJAtZ.vsJX`,
  `ptesR_sub`). A paging invariant.
* `ent.2` (U1's `InvQF` / `InvQCMW`): the P1 entry facts (`IoPre`: current thread, SC, CSpace walk, timer tree) and
  the plan / lookup of the invocation (`plan_with`), as every other VM-epoch slot's entry [S] (`IoStartX5` etc.).
* `qps`: as VX4's / VX7's `qps`.

No sorry / admit / native_decide / bv_decide. No existing statement or file changed except the root import list.
-/
import Fl4Proofs.P2.E2EPVX8
open Aeneas Aeneas.Std Result

/-! ## Part 1: frame lemmas of the invocation entry facts without a P3 bundle -/

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout fld oAFFINITY)

section wr
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {s : S} {b : U64}
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}

/-- The current thread's register word is kept by a user write (at an `IoPre` state; `tcbReg_wr` without the
bundle). -/
theorem tcbReg_wrP (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) (hb : b ∈ K.user) (hba : Aligned b) (v : U64)
    {r : U64} (hr : r.val < 384) :
    L.mem (L.wr s b v) (regA (L.curW s) r) = L.mem s (regA (L.curW s) r) := by
  have h := (P.reg (Locks := fun _ _ => True) hr).1
  exact wr_nu hba hb v ⟨h.1, h.2.1⟩

/-- The current thread's message info is kept by a user write (`msgInfo_wr` without the bundle). -/
theorem msgInfo_wrP (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) (hb : b ∈ K.user) (hba : Aligned b) (v : U64) :
    msg.msg_info st (L.wr s b v) (L.curW s) = msg.msg_info st s (L.curW s) := by
  unfold msg.msg_info
  rw [reg_ok, reg_ok, tcbReg_wrP P hb hba v (r := layout.reg.MSG_INFO) (by simp [layout.reg.MSG_INFO])]

/-- The current thread is kept by a user write (VX8's `curW_wrI` at an `IoPre` state). -/
theorem curW_wrP (U : Fl4Proofs.P2.E2EP.UserLayX L K) (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hb : b ∈ K.user) (hba : Aligned b) (v : U64) : L.curW (L.wr s b v) = L.curW s :=
  curW_wrI U P.np P.kb.symm (Nat.lt_of_lt_of_le P.nc U.nc) hb hba v

/-- The current thread's CTable slot is a capability slot (`slJAt_root` without the bundle: `IoLay.tslot`). -/
theorem rootSlot_of (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) (hT : K.heap (L.curW s) = some .tcb) :
    L.curW s ∈ K.slots :=
  (P.lay.tslot _ hT _ _ (tcb_slot_ctable (L.curW s)) (by simp [layout.tcb.SLOT_CTABLE])).1

/-- **`IoQ` is kept by a user write** at any layout with `UserLayX` (stpost's `ioQ_wr` without its [J] `hIw`:
VX5's `ioPre_wrL`; the affinity words are TCB words, `nu_tcb`). -/
theorem ioQ_wrX {m : U64 → U64} (U : Fl4Proofs.P2.E2EP.UserLayX L K) (hCs : ∀ c ∈ Cs, c.val < 64)
    (q : IoQ st Cs Ω Sg Ac K m s) (hb : b ∈ K.user) (hba : Aligned b) (v : U64) :
    IoQ st Cs Ω Sg Ac K m (L.wr s b v) :=
  ⟨Fl4Proofs.P2.E2EP.ioPre_wrL U hCs q.1 hb hba v, fun d hd => by
    rw [show L.mem (L.wr s b v) (fld d oAFFINITY) = L.mem s (fld d oAFFINITY) from
      wr_nu hba hb v (nu_tcb U.rx hd (o := oAFFINITY) (by simp [oAFFINITY]) (by simp [oAFFINITY])
        (by simp [oAFFINITY]))]
    exact q.2 d hd⟩

end wr

/-! ### The page walk across a write -/

section walk
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {V : U64 → Prop} {m' : machine.Store S} {x' s : S}

/-- Copy of unify's `vsRdG_tr` (P2/InvPmWalk.lean): **the walk transfers to any store reading the `V` words
alike**. -/
theorem vsRdG_trX {asid va : U64} (hV : VsRdG st V s asid va) (hr : ∀ a, V a → m'.read x' a = st.read s a)
    (hk : m'.ks_base x' = st.ks_base s) :
    vspace.find_vspace_for_asid m' x' asid = vspace.find_vspace_for_asid st s asid ∧
      ∀ root, vspace.find_vspace_for_asid st s asid = ok (.Ok root) →
        vspace.lookup_pt_slot m' x' root va = vspace.lookup_pt_slot st s root va := by
  obtain ⟨h1, h2⟩ := hV
  refine ⟨?_, fun root hroot => ?_⟩
  · obtain ⟨r, hr', -⟩ := spec_ex_fd (P0.vspace.find_vspace_for_asid.p0 st s asid L.total)
    rw [hr']
    rw [hr'] at h1
    exact vspace.find_vspace_for_asid.trV (W := fun _ => False) hr hk h1
  · obtain ⟨r, hr', -⟩ := spec_ex_fd (P0.vspace.lookup_pt_slot.p0 st s root va L.total)
    have h2' := h2 root hroot
    rw [hr'] at h2' ⊢
    exact vspace.lookup_pt_slot.trV (W := fun _ => False) hr h2'

/-- `small_page_entry` from its two lookups. -/
theorem spe_congrX {asid va : U64}
    (hf : vspace.find_vspace_for_asid m' x' asid = vspace.find_vspace_for_asid st s asid)
    (hl : ∀ root, vspace.find_vspace_for_asid st s asid = ok (.Ok root) →
      vspace.lookup_pt_slot m' x' root va = vspace.lookup_pt_slot st s root va) :
    localinv.small_page_entry m' x' asid va = localinv.small_page_entry st s asid va := by
  unfold localinv.small_page_entry
  rw [hf]
  obtain ⟨r, hr, -⟩ := spec_ex_fd (P0.vspace.find_vspace_for_asid.p0 st s asid L.total)
  rw [hr]
  simp only [bind_ok]
  cases r with
  | Err e =>
    simp only [core.result.Result.ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, bind_ok]
  | Ok root =>
    simp only [core.result.Result.ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, bind_ok]
    unfold localinv.page_entry vspace.small_page_entry
    rw [hl root hr]

/-- **A walk reading only words the step keeps is kept, with its `small_page_entry`** (module docstring). -/
theorem vsRdG_wrX {s' : S} (hV : ∀ a, V a → st.read s' a = st.read s a) (hk : st.ks_base s' = st.ks_base s)
    {asid va : U64} (h : VsRdG st V s asid va) :
    VsRdG st V s' asid va ∧ localinv.small_page_entry st s' asid va = localinv.small_page_entry st s asid va := by
  have t1 := vsRdG_trX (m' := st) (x' := s') h hV hk
  have t2 := vsRdG_trX (m' := guard st V (fun _ => False)) (x' := s') h
    (fun a ha => by rw [guard_read ha]; exact hV a ha) hk
  refine ⟨⟨t2.1.trans t1.1.symm, fun root hroot => ?_⟩, spe_congrX t1.1 t1.2⟩
  have hroot' : vspace.find_vspace_for_asid st s asid = ok (.Ok root) := by rw [← t1.1]; exact hroot
  exact (t2.2 root hroot').trans (t1.2 root hroot').symm

/-- An aligned non-user word reads alike after a user write. -/
theorem read_wr_nu {K : KLayout} {b : U64} (hb : b ∈ K.user) (hba : Aligned b) (v : U64) {a : U64}
    (ha : Aligned a) (hau : a ∉ K.user) : st.read (L.wr s b v) a = st.read s a := by
  rw [L.read_eq, L.read_eq, mem_wr_ne' hba ha (fun e => hau (e ▸ hb))]

theorem ksBase_wr (b v : U64) : st.ks_base (L.wr s b v) = st.ks_base s := by
  rw [L.ks_base_eq, L.ks_base_eq, L.ksb_wr]

end walk

/-! ### The plan and the lookup across a write (copies with `SlJAt` replaced by `IoPre`) -/

section plan
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {s : S} {b : U64}
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}

/-- `invLk_wr` without the bundle: **the plan's lookup is kept by a user write**. -/
theorem invLk_wrX (U : Fl4Proofs.P2.E2EP.UserLayX L K)
    (P : IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    {p : localinv.Plan} (hl : InvLk st p s) (hb : b ∈ K.user) (hba : Aligned b) (v : U64) :
    InvLk st p (L.wr s b v) := by
  obtain ⟨x, hx, ex⟩ := hl
  have hT : K.heap (L.curW s) = some .tcb := P.cT
  have ecur := curW_wrP U P hb hba v
  have ecap := tcbReg_wrP P hb hba v (r := layout.reg.CAP) (by simp [layout.reg.CAP])
  obtain ⟨C, hroot, hcl, hC⟩ := P.walk
  obtain ⟨res, hres, -⟩ := spec_ex_fd (P0.cspace.lookup_slot.p0 st (L.wr s b v) (L.curW s)
    (L.mem s (regA (L.curW s) layout.reg.CAP)) L.total)
  have back := lookup_slot_back (tcb_slot_ctable (L.curW s))
    (P.cap_userWr hb hba v (rootSlot_of P hT))
    (fun p r m y hp hm => P.cap_userWr hb hba v (hC p r m y hp hm).1) hcl hroot hres
  rw [hx] at back
  have e := ok_inj_ff back
  subst e
  refine ⟨x, ?_, ex⟩
  rw [ecur, ecap]
  exact hres

/-- `small_ram_frame` accepts only small non-device non-EPT frames. -/
theorem srf_true {c : capability.Cap} (h : localinv.small_ram_frame c = ok true) :
    ∃ fp rt mp asid va, c = .Frame fp .Small rt false mp false asid va := by
  unfold localinv.small_ram_frame at h
  cases c with
  | Frame fp fs rt dv mp ep asid va =>
    cases fs <;> cases dv <;> cases ep <;> first | exact ⟨fp, rt, mp, asid, va, rfl⟩ | (simp at h)
  | _ => simp at h

/-- `small_ram_frame` answers `true` or `false`. -/
theorem srf_false {c : capability.Cap} (h : ¬ localinv.small_ram_frame c = ok true) :
    localinv.small_ram_frame c = ok false := by
  unfold localinv.small_ram_frame at h ⊢
  cases c with
  | Frame fp fs rt dv mp ep asid va =>
    cases fs <;> cases dv <;> cases ep <;> simp at h ⊢
  | _ => rfl

set_option maxHeartbeats 4000000 in
/-- `planDel_userWr` without the bundle: **`plan_with` at `CNodeDelete` answers alike after a user write**, at an
`IoPre` state, the target's `small_page_entry` kept by `hspe` (from the target's walk fact) instead of P3's
`smallPageEntry_userWr`. -/
theorem planDel_userWrX
    (P : IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hb : b ∈ K.user) (hba : Aligned b) (v : U64) {sl : obj.Slot} (hsl : sl ∈ K.slots)
    {cp cr cg cgb : U64} (hcap : obj.Slot.cap st sl s = ok (.CNode cp cr cg cgb)) {C : U64 → U64 → Prop}
    (hC : C cp cr) (hcl : WalkCl (st := st) s C)
    (hCs : ∀ p r m y, C p r → cspace.mask r = ok m → cnSlot p (y &&& m) ∈ K.slots)
    (hspe : ∀ d, d ∈ K.slots → ∀ fp rt asid va,
      obj.Slot.cap st d s = ok (.Frame fp .Small rt false true false asid va) → asid ≠ 0#u64 →
      localinv.small_page_entry st (L.wr s b v) asid va = localinv.small_page_entry st s asid va)
    (ex : Array obj.Slot 3#usize) :
    localinv.plan_with st (L.wr s b v) (L.curW s) fl4_abi.label.CNodeDelete sl ex =
      localinv.plan_with st s (L.curW s) fl4_abi.label.CNodeDelete sl ex := by
  have e10 := tcbReg_wrP P hb hba v (r := layout.reg.R10) (by simp [layout.reg.R10])
  have e8 := tcbReg_wrP P hb hba v (r := layout.reg.R8) (by simp [layout.reg.R8])
  have er0 : localinv.reg_arg st (L.wr s b v) (L.curW s) 0#u64 = localinv.reg_arg st s (L.curW s) 0#u64 := by
    unfold localinv.reg_arg; rw [sarg0_reg, sarg0_reg, reg_ok, reg_ok, e10]
  have er1 : localinv.reg_arg st (L.wr s b v) (L.curW s) 1#u64 = localinv.reg_arg st s (L.curW s) 1#u64 := by
    unfold localinv.reg_arg; rw [sarg1_reg, sarg1_reg, reg_ok, reg_ok, e8]
  have elts : ∀ cptr depth, cspace.lookup_target_slot st (L.wr s b v) (.CNode cp cr cg cgb) cptr depth =
      cspace.lookup_target_slot st s (.CNode cp cr cg cgb) cptr depth := by
    intro cptr depth
    obtain ⟨r, hr, -⟩ := spec_ex_fd (P0.cspace.lookup_target_slot.p0 st s (.CNode cp cr cg cgb) cptr depth L.total)
    rw [hr, lts_userWr P hb hba v hCs hcl hC hr]
  unfold localinv.plan_with
  rw [P.cap_userWr hb hba v hsl, hcap]
  simp only [bind_ok, localinv.Plan.new, if_neg lbl_del_ne_copy, if_neg lbl_del_ne_mint, ↓reduceIte, er0, er1,
    elts]
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
      planReadCap_userWr P hb hba v hdK, ePr, eNx]
    refine bind_guard_congr rfl (fun x hx => ?_)
    obtain ⟨c, p1⟩ := x
    have hc := read_cap_val hx (by simp)
    try simp only at hc
    simp only [Aeneas.Std.uncurry_apply_pair]
    by_cases hsr : localinv.small_ram_frame c = ok true
    · obtain ⟨fp, rt, mp, asid, va, rfl⟩ := srf_true hsr
      rw [hsr]
      simp only [bind_ok, ↓reduceIte]
      cases mp with
      | false => simp only [Bool.false_eq_true, ↓reduceIte]
      | true =>
        by_cases ha : asid = 0#u64
        · subst ha
          simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        · rw [hspe _ hdK _ _ _ _ hc ha]
    · rw [srf_false hsr]
      simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]

/-- `invPlanD_wrF` without the bundle: the plan survives a user write at an `InvQF` state whose target's walk
fact `hspe` holds. -/
theorem invPlanD_wrFX {Locks : S → U64 → Prop} {p : localinv.Plan} {m : U64 → U64}
    (U : Fl4Proofs.P2.E2EP.UserLayX L K) (hqf : InvQF st Cs Ω Sg Ac Locks p K m s)
    (hb : b ∈ K.user) (hba : Aligned b) (v : U64)
    (hspe : ∀ d, d ∈ K.slots → ∀ fp rt asid va,
      obj.Slot.cap st d s = ok (.Frame fp .Small rt false true false asid va) → asid ≠ 0#u64 →
      localinv.small_page_entry st (L.wr s b v) asid va = localinv.small_page_entry st s asid va) :
    InvPlanD st p (L.wr s b v) := by
  obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, C, hcap, hsK, -, -, hC, hcl, hCs, -⟩ := del_core hqf
  obtain ⟨⟨hio, ⟨t, info, ex, ht, hi, hpw⟩, harm, -⟩, -⟩ := hqf
  have P := hio.1
  have et : t = L.curW s := by rw [cur_thread_ok] at ht; exact (ok_inj_ff ht).symm
  subst et
  have hlbl := (harm _ info (cur_thread_ok s) hi).1
  rw [hlbl] at hpw
  refine ⟨L.curW s, info, ex, ?_, ?_, ?_⟩
  · rw [cur_thread_ok, curW_wrP U P hb hba v]
  · rw [msgInfo_wrP P hb hba v]; exact hi
  · rw [hlbl, planDel_userWrX P hb hba v hsK hcap hC hcl (fun p r m y hp hm => (hCs p r m y hp hm).1) hspe ex]
    exact hpw

/-- `lookupSlot_userWr` without the bundle. -/
theorem lookupSlot_userWrX
    (P : IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hb : b ∈ K.user) (hba : Aligned b) (v : U64) {c : U64} {r : cspace.Resolved}
    (h : cspace.lookup_slot st s (L.curW s) c = ok (core.result.Result.Ok r)) :
    cspace.lookup_slot st (L.wr s b v) (L.curW s) c = ok (core.result.Result.Ok r) := by
  have hT : K.heap (L.curW s) = some .tcb := P.cT
  obtain ⟨C, hroot, hcl, hC⟩ := P.walk
  obtain ⟨res, hres, -⟩ := spec_ex_fd (P0.cspace.lookup_slot.p0 st (L.wr s b v) (L.curW s) c L.total)
  have back := lookup_slot_back (tcb_slot_ctable (L.curW s))
    (P.cap_userWr hb hba v (rootSlot_of P hT))
    (fun p r m y hp hm => P.cap_userWr hb hba v (hC p r m y hp hm).1) hcl hroot hres
  rw [h] at back
  have e := ok_inj_ff back
  rw [hres, ← e]

set_option hygiene false in
/-- The Copy / Mint arm of `plan_with` after a user write (copy of InvCMQ's local `cmw_arm`). -/
local macro "cmw_armX" : tactic => `(tactic| (
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
/-- `planCM_userWr` without the bundle: **`plan_with` at `CNodeCopy` / `CNodeMint` answers alike after a user
write** at an `IoPre` state. -/
theorem planCM_userWrX
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
  have e10 := tcbReg_wrP P hb hba v (r := layout.reg.R10) (by simp [layout.reg.R10])
  have e8 := tcbReg_wrP P hb hba v (r := layout.reg.R8) (by simp [layout.reg.R8])
  have e9 := tcbReg_wrP P hb hba v (r := layout.reg.R9) (by simp [layout.reg.R9])
  have e15 := tcbReg_wrP P hb hba v (r := layout.reg.R15) (by simp [layout.reg.R15])
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
    cmw_armX
  · simp only [bind_ok, localinv.Plan.new, if_neg lbl_mint_ne_copy]
    cmw_armX

/-- `invExW_wr` without the bundle. -/
theorem invExW_wrX (U : Fl4Proofs.P2.E2EP.UserLayX L K)
    (P : IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    {p : localinv.Plan} (hx : InvExW st p s) (harm : InvCMArm st s) (hlk : InvLk st p s)
    (hb : b ∈ K.user) (hba : Aligned b) (v : U64) : InvExW st p (L.wr s b v) := by
  obtain ⟨info, ei, hpw, hlec⟩ := hx
  have ecur := curW_wrP U P hb hba v
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
  · rw [ecur, msgInfo_wrP P hb hba v]; exact ei
  · rw [ecur, planCM_userWrX P hb hba v hsl hcap hCc hcl (fun p r m y hp hm => (hC p r m y hp hm).1) p.extra
      hex0 hl]
    exact hpw
  · intro s1 h1 h0
    obtain ⟨c2, x2, hx2, hxs2⟩ := hlec s1 h1 h0
    exact ⟨c2, x2, by rw [ecur]; exact lookupSlot_userWrX P hb hba v hx2, hxs2⟩

end plan

/-! ### The closures under one write -/

section cl
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {s : S} {b : U64}
variable {Cs Ω Sg Ac : Set U64}

/-- **`InvLXS` is kept by a user write** at an `IoPre` state with `UserLayX` (module docstring). -/
theorem invLXS_wrX (U : Fl4Proofs.P2.E2EP.UserLayX L K)
    (P : IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (X : InvLXS st K s) (hb : b ∈ K.user) (hba : Aligned b) (v : U64) : InvLXS st K (L.wr s b v) := by
  have ecur := curW_wrP U P hb hba v
  have hcH : K.heap (L.curW s) = some .tcb := P.cT
  have hpr : ∀ sl, sl ∈ K.slots → L.mem (L.wr s b v) (core.num.U64.wrapping_add sl layout.cte.PREV) =
      L.mem s (core.num.U64.wrapping_add sl layout.cte.PREV) := by
    intro sl hsl
    obtain ⟨h8, hf⟩ := P.lay.slot8 _ hsl
    have hv : (core.num.U64.wrapping_add sl layout.cte.PREV).val = sl.val + 16 := by
      simp [core.num.U64.wrapping_add_val_eq, layout.cte.PREV, U64.size_def, U64.numBits]; omega
    exact mem_wr_ne' hba (by unfold Aligned; omega)
      (fun e => P.slotW_nu hsl ⟨by omega, by omega⟩ (e ▸ hb))
  have hnx : ∀ sl, sl ∈ K.slots → obj.Slot.next st sl (L.wr s b v) = obj.Slot.next st sl s := by
    intro sl hsl
    obtain ⟨h8, hf⟩ := P.lay.slot8 _ hsl
    have hv : (core.num.U64.wrapping_add sl layout.cte.NEXT).val = sl.val + 24 := by
      simp [core.num.U64.wrapping_add_val_eq, layout.cte.NEXT, U64.size_def, U64.numBits]; omega
    have e : L.mem (L.wr s b v) (core.num.U64.wrapping_add sl layout.cte.NEXT) =
        L.mem s (core.num.U64.wrapping_add sl layout.cte.NEXT) :=
      mem_wr_ne' hba (by unfold Aligned; omega) (fun e => P.slotW_nu hsl ⟨by omega, by omega⟩ (e ▸ hb))
    unfold obj.Slot.next obj.Slot.next_word
    simp only [lift, bind_ok, L.read_eq, e]
  have hsb : obj.Tcb.slot (L.curW s) layout.tcb.SLOT_BUFFER = ok (sbA (L.curW s)) := by
    simp [obj.Tcb.slot, lift, sbA]
  have hsbK := (P.lay.tslot _ hcH _ _ hsb (by simp [layout.tcb.SLOT_BUFFER])).1
  have nts := slot_nu U.lp hsbK
  have e1 : L.mem (L.wr s b v) (ibA (L.curW s)) = L.mem s (ibA (L.curW s)) :=
    wr_nu hba hb v (nu_tcb U.rx hcH (o := 3512#u64) (by simp) (by simp) (by simp))
  have e2 : L.mem (L.wr s b v) (sbA (L.curW s)) = L.mem s (sbA (L.curW s)) := wr_nu hba hb v nts.1
  have e3 : L.mem (L.wr s b v) (core.num.U64.wrapping_add (sbA (L.curW s)) 8#u64) =
      L.mem s (core.num.U64.wrapping_add (sbA (L.curW s)) 8#u64) := wr_nu hba hb v nts.2
  refine ⟨fun sl hsl => ?_, ?_, ?_, fun sl fp rt asid va hsl hc ha => ?_⟩
  · rw [hpr sl hsl, hnx sl hsl]; exact X.cdt sl hsl
  · intro bb hbb hb0 i hi
    rw [ecur, lookup_buf_agreeB true e1 e2 e3] at hbb
    exact X.buf8 bb hbb hb0 i hi
  · intro bb hbb hb0 i hi
    rw [ecur, lookup_buf_agreeB false e1 e2 e3] at hbb
    exact X.bufS8 bb hbb hb0 i hi
  · rw [Fl4Proofs.P2.E2EP.cap_wrL U.lp hb hba v hsl] at hc
    obtain ⟨h1, h2, h3⟩ := X.vs sl fp rt asid va hsl hc ha
    obtain ⟨h3', e⟩ := vsRdG_wrX (V := VsW K) (fun a ha => read_wr_nu hb hba v ha.1 ha.2.2) (ksBase_wr b v) h3
    exact ⟨h1, by rw [e]; exact h2, h3'⟩

/-- **`InvQF` is kept by a user write** at an `InvLXS` state with `UserLayX`, the locks kept (`hufQF_of2`'s body
without the bundle and without [J] `hIw`). -/
theorem invQF_wrX {Locks : S → U64 → Prop} {p : localinv.Plan} {m : U64 → U64}
    (U : Fl4Proofs.P2.E2EP.UserLayX L K) (hCs : ∀ c ∈ Cs, c.val < 64) (X : InvLXS st K s)
    (hq : InvQF st Cs Ω Sg Ac Locks p K m s) (hb : b ∈ K.user) (hba : Aligned b) (v : U64)
    (el : Locks (L.wr s b v) = Locks s) : InvQF st Cs Ω Sg Ac Locks p K m (L.wr s b v) := by
  have hq0 := hq
  obtain ⟨⟨hio, hpd, harm, hlks⟩, hlk0⟩ := hq
  have P := hio.1
  have ecur := curW_wrP U P hb hba v
  have emsg := msgInfo_wrP P hb hba v
  have hct : ∀ t, sched.cur_thread st (L.wr s b v) = ok t → t = L.curW s := by
    intro t ht
    rw [cur_thread_ok, ecur] at ht
    exact (ok_inj_ff ht).symm
  have hspe : ∀ d, d ∈ K.slots → ∀ fp rt asid va,
      obj.Slot.cap st d s = ok (.Frame fp .Small rt false true false asid va) → asid ≠ 0#u64 →
      localinv.small_page_entry st (L.wr s b v) asid va = localinv.small_page_entry st s asid va :=
    fun d hd fp rt asid va hc ha =>
      (vsRdG_wrX (V := VsW K) (fun a ha => read_wr_nu hb hba v ha.1 ha.2.2) (ksBase_wr b v)
        (X.vs d fp rt asid va hd hc ha).2.2).2
  refine ⟨⟨ioQ_wrX U hCs hio hb hba v, invPlanD_wrFX U hq0 hb hba v hspe, ?_, ?_⟩,
    invLk_wrX U P hlk0 hb hba v⟩
  · intro t info ht hi
    obtain rfl := hct t ht
    rw [emsg] at hi
    exact harm _ info (cur_thread_ok s) hi
  · intro i x hi hx
    rw [el]
    exact hlks i x hi hx

/-- **`InvQCMW` is kept by a user write** at a state with `UserLayX`, the locks kept (`hufQCMW_of`'s body without
the bundle and without [J] `hIw`). -/
theorem invQCMW_wrX {Locks : S → U64 → Prop} {p : localinv.Plan} {m : U64 → U64}
    (U : Fl4Proofs.P2.E2EP.UserLayX L K) (hCs : ∀ c ∈ Cs, c.val < 64)
    (hq : InvQCMW st Cs Ω Sg Ac Locks p K m s) (hb : b ∈ K.user) (hba : Aligned b) (v : U64)
    (el : Locks (L.wr s b v) = Locks s) : InvQCMW st Cs Ω Sg Ac Locks p K m (L.wr s b v) := by
  obtain ⟨⟨hio, hpd, harm, hlks⟩, hlk0, hx⟩ := hq
  have P := hio.1
  have ecur := curW_wrP U P hb hba v
  have emsg := msgInfo_wrP P hb hba v
  have hct : ∀ t, sched.cur_thread st (L.wr s b v) = ok t → t = L.curW s := by
    intro t ht
    rw [cur_thread_ok, ecur] at ht
    exact (ok_inj_ff ht).symm
  have hx' := invExW_wrX U P hx harm hlk0 hb hba v
  have hpd' : InvPlanD st p (L.wr s b v) := by
    obtain ⟨info, ei, hpw, -⟩ := hx'
    exact ⟨L.curW (L.wr s b v), info, p.extra, cur_thread_ok _, ei, hpw⟩
  refine ⟨⟨ioQ_wrX U hCs hio hb hba v, hpd', ?_, ?_⟩, invLk_wrX U P hlk0 hb hba v, hx'⟩
  · intro t info ht hi
    obtain rfl := hct t ht
    rw [emsg] at hi
    exact harm _ info (cur_thread_ok s) hi
  · intro i x hi hx
    rw [el]
    exact hlks i x hi hx

/-- **Closure along `UReach`** of a property `P` whose one-write step may use the closure of a lock-free part
`P1` (module docstring). -/
theorem ureach_cl {P1 P : S → Prop}
    (h1 : ∀ s b v, P1 s → b ∈ K.user → Aligned b → P1 (L.wr s b v))
    (h2 : ∀ s b v, (∀ s', UReach (L := L) K s s' → P1 s') → P s → b ∈ K.user → Aligned b → P (L.wr s b v))
    (h12 : ∀ s, P s → P1 s) :
    ∀ s s', UReach (L := L) K s s' → P s → P s' := by
  have c1 : ∀ s s', UReach (L := L) K s s' → P1 s → P1 s' := by
    intro s s' hr
    induction hr with
    | refl s => exact id
    | wr v hb hba _ ih => exact fun h => ih (h1 _ _ v h hb hba)
  intro s s' hr
  induction hr with
  | refl s => exact id
  | wr v hb hba _ ih => exact fun h => ih (h2 _ _ v (fun s' hr' => c1 _ _ hr' (h12 _ h)) h hb hba)

end cl

end Fl4Proofs.P2.PathObl

/-! ## Part 2: VsXW across a write, start facts, tops (`E2EP`) -/

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout own region TcbSlot NullOrFrame)
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg)

noncomputable section
open Classical

section vsx
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **`VsXW` is kept by a user write** (its walk reads only `VsW` words, no user word: `vsRdG_wrX`). -/
theorem vsXW_wrX {K : KLayoutP} (U : UserLayX L K.toKLayout) {s : S} {b : U64} (hb : b ∈ K.toKLayout.user)
    (hba : Aligned b) (v : U64) (h : VsXW st K s) : VsXW st K (L.wr s b v) := by
  intro sl fp rt asid va hsl hc ha
  rw [cap_wrL U.lp hb hba v hsl] at hc
  obtain ⟨h1, h2, h3⟩ := h sl fp rt asid va hsl hc ha
  obtain ⟨h3', e⟩ := vsRdG_wrX (V := fun b => VsW K.toKLayout b ∧ ¬ XD K b)
    (fun a ha => read_wr_nu hb hba v ha.1.1 ha.1.2.2) (ksBase_wr b v) h3
  exact ⟨h1, by rw [e]; exact h2, h3'⟩

end vsx

section slot
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- **The invocation entry's facts at a guest-running start state** [S] (module docstring): VX8's `InvEntV` with
`cl` (every `UReach` state) replaced by `ent` (the start state only). -/
structure InvEntV9 (K : KLayoutP) (G : S → Prop) (s : S) : Prop where
  /-- [S] no capability slot at address 0 (natively `slJAt_slot0`; = VX8's `InvEntV.hz`). -/
  hz : (0#u64) ∉ K.slots
  /-- [S] `InvLXS` and the entry fact at the start state (natively `slJAt_cdt`, `invBufJ8_of`, `invBufSJ8_of`,
  `invVsJ_of`, `SlJAtZ.vsJX` + `ptesR_sub`, and U1's `InvQF` / `InvQCMW`). -/
  ent : InvLXS st K.toKLayout s ∧ G s
  /-- [S] the PTE facts at the start state (= VX8's `InvEntV.qps`). -/
  qps : QPs K st s

variable {st}

/-- **VX8's `InvEntV` of the CNodeDelete slot from `InvEntV9`** (the closure proved: `ureach_cl` with the
lock-free part `InvLXS ∧ IoPre`; the locks by `InvPremX.lk` [P] at `InvLX (fun _ => True)` states). -/
theorem invEntV_of9D {K : KLayoutP} {j : InvArg S} {μ : U64 → U64} {σ : S} (hK : RegionOKP K) (hU : UserOKP K)
    (E : VtxBundle4 st L K) (hl : InvPremX st j K) (hCs : ∀ c ∈ j.Cs, c.val < 64)
    (he : InvEntV9 st K (fun s => InvQF st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K.toKLayout μ s ∧ VsXW st K s) σ) :
    InvEntV st K (fun s => InvQF st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K.toKLayout μ s ∧ VsXW st K s) σ := by
  have U := E.b.ul
  refine ⟨he.hz, fun s' hr => ?_, he.qps⟩
  refine ureach_cl (K := K.toKLayout)
    (P1 := fun s => InvLXS st K.toKLayout s ∧ IoPre st K.toKLayout K.heap.tcbs j.Cs j.Ω K.heap j.Sg K.heap.replies
      K.heap.scs K.heap.ntfns K.heap.scBits j.Ac s)
    (P := fun s => InvLXS st K.toKLayout s ∧
      (InvQF st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K.toKLayout μ s ∧ VsXW st K s))
    (fun s b v h hb hba => ⟨invLXS_wrX U h.2 h.1 hb hba v, ioPre_wrL U hCs h.2 hb hba v⟩)
    (fun s b v hc h hb hba => ?_) (fun s h => ⟨h.1, h.2.1.1.1.1⟩) σ s' hr he.ent
  have hX : InvLX st (fun _ => True) K.toKLayout s :=
    ⟨hK.base.base, hU.base.base, E.la, U, he.hz, fun s'' hr'' => ⟨(hc s'' hr'').1, trivial⟩⟩
  have el := hl.lk s b v ⟨_, hX⟩ hb hba
  exact ⟨invLXS_wrX U h.2.1.1.1.1 h.1 hb hba v, invQF_wrX U hCs h.1 h.2.1 hb hba v el,
    vsXW_wrX U hb hba v h.2.2⟩

/-- **VX8's `InvEntV` of the Copy / Mint slot from `InvEntV9`** (as `invEntV_of9D`). -/
theorem invEntV_of9C {K : KLayoutP} {j : InvArg S} {μ : U64 → U64} {σ : S} (hK : RegionOKP K) (hU : UserOKP K)
    (E : VtxBundle4 st L K) (hl : InvPremX st j K) (hCs : ∀ c ∈ j.Cs, c.val < 64)
    (he : InvEntV9 st K (fun s => InvQCMW st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K.toKLayout μ s) σ) :
    InvEntV st K (fun s => InvQCMW st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K.toKLayout μ s) σ := by
  have U := E.b.ul
  refine ⟨he.hz, fun s' hr => ?_, he.qps⟩
  refine ureach_cl (K := K.toKLayout)
    (P1 := fun s => InvLXS st K.toKLayout s ∧ IoPre st K.toKLayout K.heap.tcbs j.Cs j.Ω K.heap j.Sg K.heap.replies
      K.heap.scs K.heap.ntfns K.heap.scBits j.Ac s)
    (P := fun s => InvLXS st K.toKLayout s ∧ InvQCMW st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K.toKLayout μ s)
    (fun s b v h hb hba => ⟨invLXS_wrX U h.2 h.1 hb hba v, ioPre_wrL U hCs h.2 hb hba v⟩)
    (fun s b v hc h hb hba => ?_) (fun s h => ⟨h.1, h.2.1.1.1⟩) σ s' hr he.ent
  have hX : InvLX st (fun _ => True) K.toKLayout s :=
    ⟨hK.base.base, hU.base.base, E.la, U, he.hz, fun s'' hr'' => ⟨(hc s'' hr'').1, trivial⟩⟩
  have el := hl.lk s b v ⟨_, hX⟩ hb hba
  exact ⟨invLXS_wrX U h.2.1.1.1 h.1 hb hba v, invQCMW_wrX U hCs h.2 hb hba v el⟩

variable (st)

/-- **The CNodeDelete slot's start fact in a VM epoch, gen 9**: VX8's `InvStartX` with `InvEntV9` (start-state
facts only) and the index convention `cs` (the index's cores are the layout's, as VX5's `IoPremX5.hCs`). -/
def InvStartX9 (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64) (hs : U64 → Prop)
    (q : SP) (j : InvArg S) : Prop :=
  K.vcpus ≠ ∅ ∧ (∀ c ∈ j.Cs, c.val < K.ncores) ∧ ∃ h : InvPremX st j K, ∃ (σ : S) (a : A),
    InvEntV9 st K (fun s => InvQF st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K.toKLayout m s ∧ VsXW st K s) σ ∧
    L.cpu σ = c ∧ j.Locks σ = hs ∧ (∀ x, Aligned x → ¬ x ∈ K.user → L.mem σ x = m x) ∧
    q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c
      ((invPathVX st ar hA hm j K m hK hU h).body σ a) ∅

/-- **The Copy / Mint slot's start fact in a VM epoch, gen 9** (as `InvStartX9`). -/
def CMStartX9 (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64) (hs : U64 → Prop)
    (q : SP) (j : InvArg S) : Prop :=
  K.vcpus ≠ ∅ ∧ (∀ c ∈ j.Cs, c.val < K.ncores) ∧ ∃ h : InvPremX st j K, ∃ (σ : S) (a : A),
    InvEntV9 st K (fun s => InvQCMW st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K.toKLayout m s) σ ∧
    L.cpu σ = c ∧ j.Locks σ = hs ∧ (∀ x, Aligned x → ¬ x ∈ K.user → L.mem σ x = m x) ∧
    q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c
      ((cmPathVX st ar hA hm j K m hK hU h).body σ a) ∅

variable {st ar hA hm}

/-- `InvStartX9` gives VX8's `InvStartX` (`invEntV_of9D`). -/
theorem invStartX_of9 {K : KLayoutP} {μ : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64}
    {hs : U64 → Prop} {q : SP} {j : InvArg S} (E : VtxBundle4 st L K)
    (h : InvStartX9 st ar hA hm K μ hK hU c hs q j) : InvStartX st ar hA hm K μ hK hU c hs q j := by
  obtain ⟨hv, hcs, hp, σ, a, he, hc, hl, hμ, hq⟩ := h
  exact ⟨hv, hp, σ, a,
    invEntV_of9D hK hU E hp (fun c hc' => Nat.lt_of_lt_of_le (hcs c hc') E.b.ul.nc) he, hc, hl, hμ, hq⟩

/-- `CMStartX9` gives VX8's `CMStartX` (`invEntV_of9C`). -/
theorem cmStartX_of9 {K : KLayoutP} {μ : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64}
    {hs : U64 → Prop} {q : SP} {j : InvArg S} (E : VtxBundle4 st L K)
    (h : CMStartX9 st ar hA hm K μ hK hU c hs q j) : CMStartX st ar hA hm K μ hK hU c hs q j := by
  obtain ⟨hv, hcs, hp, σ, a, he, hc, hl, hμ, hq⟩ := h
  exact ⟨hv, hp, σ, a,
    invEntV_of9C hK hU E hp (fun c hc' => Nat.lt_of_lt_of_le (hcs c hc') E.b.ul.nc) he, hc, hl, hμ, hq⟩

end slot

/-! ## The tops -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **The start facts, gen 9** (VX8's, with `InvStartX9` / `CMStartX9` for the two invocation slots). -/
def StartVX9 {ιN : Type}
    (SFN : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ιN → Prop)
    (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (q : SP) :
    (((((((ιN ⊕ VxArg S) ⊕ VtArg S) ⊕ IoArg S) ⊕ StArg S) ⊕ IrqArg S) ⊕ SlArg S) ⊕ InvArg S) ⊕ InvArg S → Prop
  | .inl (.inl i) => StartVX7 st ar hA hm hSt a0 SFN Ch K m hK hU c hs q i
  | .inl (.inr j) => InvStartX9 st ar hA hm K m hK hU c hs q j
  | .inr j => CMStartX9 st ar hA hm K m hK hU c hs q j

/-- **FL4 end to end, gen 9, generic in the native family** (`serializable_fl4_localVX8G` with the invocation
slots' start entry at the start state only). -/
theorem serializable_fl4_localVX9G (P : LocPlat st arI AR MR) {ιN : Type} (LN : PathsP ιN)
    {SFN : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ιN → Prop}
    (hSFN : ∀ (Ch : S → Prop) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) c hs q i,
      (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) →
      (∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → s.mem x = s1.mem x) →
      SFN Ch K s.mem hK hU c hs q i → StartAt (LN i K s.mem hK hU) c hs s.mem q)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecVX4 (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum LN
        (vxSlotPV st ar hA hm)) (vtSlotPV st ar hA hm)) (ioSlotPX st ar hA hm)) (stSlotPX st ar hA hm))
        (irqSlotPX st ar hA hm)) (slSlotPX st ar hA hm hSt a0)) (invSlotVX st ar hA hm)) (cmSlotVX st ar hA hm))
      (StartVX9 st ar hA hm hSt a0 SFN) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  obtain ⟨hK0, hU0⟩ := okP_R hB hc0
  have hX := (execVX_of_VX4 hc0.1 h).1
  refine serializable_e2eP _ h0 hA0 hK0 hU0 hM0 (execP_of_VX P ?_ h0 hA0 hB hc0 hM0 hX).1 hq
  intro Ch K s hK hU c hs q i hN hsf
  obtain ⟨hV, hsf⟩ := hsf
  rcases i with (((((((i | j) | j) | j) | j) | j) | j) | j) | j
  · have hsf' : K.vcpus = ∅ ∧ SFN Ch K s.mem hK hU c hs q i := hsf
    obtain ⟨nv, hsf'⟩ := hsf'
    obtain ⟨hX, hE⟩ := hN nv
    exact hSFN Ch K s hK hU c hs q i hX.chainOf hE hsf'
  · have hsf' : VxStartV2 st ar hA hm K s.mem hK hU c hs q j := hsf
    exact vxStartV_at st ar hA hm (vxStartV_of_V2 (hV (vxStartV2_ne hsf')).b hsf')
  · have hsf' : VtStartV4 st ar hA hm K s.mem hK hU c hs q j := hsf
    exact vtStartV2_at (hV hsf'.1).b (vtStartV2_of_V4 (hV hsf'.1).b hsf')
  · have hsf' : IoStartX5 st ar hA hm K s.mem hK hU c hs q j := hsf
    exact ioStartX_at (hV hsf'.1) (ioStartX_of_X5 (hV hsf'.1) hsf')
  · have hsf' : StStartX st ar hA hm K s.mem hK hU c hs q j := hsf
    exact stStartX_at (hV hsf'.1) hsf'
  · have hsf' : IrqStartX st ar hA hm K s.mem hK hU c hs q j := hsf
    exact irqStartX_at (hV hsf'.1) hsf'
  · have hsf' : SlStartX st ar hA hm hSt a0 K s.mem hK hU c hs q j := hsf
    exact slStartX_at (hV hsf'.1) hsf'
  · have hsf' : InvStartX9 st ar hA hm K s.mem hK hU c hs q j := hsf
    exact invStartX_at (hV hsf'.1) (invStartX_of9 (hV hsf'.1) hsf')
  · have hsf' : CMStartX9 st ar hA hm K s.mem hK hU c hs q j := hsf
    exact cmStartX_at (hV hsf'.1) (cmStartX_of9 (hV hsf'.1) hsf')

/-- **FL4 end to end with every U1 slot in native epochs and the VM-exit, VM-timer, I/O-port, `TCB_SetTimer`,
timer-interrupt, syscall, CNodeDelete and Copy / Mint slots in VM epochs, gen 9** (module docstring):
`serializable_fl4_localVX8` with the invocation slots' start entry `InvEntV9` [S] asked at the start state only
(the closure under user writes is `invEntV_of9D` / `invEntV_of9C`). No new [J], no [W], no new [S]. -/
theorem serializable_fl4_localVX9 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecVX4 (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum
        (PathsP.sum (fl4LocW11JA st ar hA hm hSt a0)
          (PathsP.sum (PathsP.sum (delPteSlot st ar hA hm) (invSlotU st ar hA hm)) (cmSlotU st ar hA hm)))
        (vxSlotPV st ar hA hm)) (vtSlotPV st ar hA hm)) (ioSlotPX st ar hA hm)) (stSlotPX st ar hA hm))
        (irqSlotPX st ar hA hm)) (slSlotPX st ar hA hm hSt a0)) (invSlotVX st ar hA hm)) (cmSlotVX st ar hA hm))
      (StartVX9 st ar hA hm hSt a0 (StartU1 st ar hA hm hSt a0 arI AR MR (StartInvU2 st ar hA hm)))
      P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  refine serializable_fl4_localVX9G st ar hA hm hSt a0 P _ ?_ h0 hA0 hB hc0 hM0 h hq
  intro Ch K s hK hU c hs q i hC hE hsf
  rcases i with i | ((j | j) | j)
  · exact startAt_U st ar hA hm hSt a0 P hIoa hC hE hsf
  · exact delPteStart_at st ar hA hm hC hE hsf
  · exact invStartU2_at st ar hA hm hC hE hsf
  · exact cmStartU2_at st ar hA hm hC hE hsf

end top

end
end Fl4Proofs.P2.E2EP
