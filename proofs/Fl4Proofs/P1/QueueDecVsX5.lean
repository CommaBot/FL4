/-
P1 (x86_64): **the VSpace family over root-restricted walks** (namespace `X5`): QueueDecVs's decode with
`DelPlaceAt.pt` / `.pd` / `.pdpt` (false as stated, QueueDelVsX5) replaced by `X5.DelPlaceAt.walk0` / `.walk` /
`.va` and the invoked cap's address (`InvVa`), and the deletes over `X5.DelGapsAt`.

Every paging lookup of the decode is from a root the ASID table names at the decode's start (`check_vspace`,
vspace.rs:393–408, `find_vspace_for_asid`; FrameBatch keeps that root in `Batch.root`), at an address the code
has checked (`vaddr ≤ USER_TOP`, vspace.rs:578, 835, 1114) or the invoked / slot cap's own mapped address
(remaps, TestAndClearAccessed, Unmap: `VaOK`). So the lookups are `WalkOK` (`walk_of`, from [J] `walk0`) at an
address below `2^47` (`va_lt`, `va_eq`, `VaOK.fr`, `VaOK.as_frame`, `VaOK.tbl`).

New premise: **[J] `InvVa`**: the invoked cap of a decode is `VaOK` (as `X5.DelPlaceAt.va` for slot caps: the
invoked cap is read from the current thread's CSpace; same sources, QueueDelVsX5's docstring).

Proved (QueueDecVs text by script, `handoff/a64-wip/gen24/gen_decvsx5.py`, with the lookups' hypotheses
changed): `vspace.check_vspace.named`, `vspace.table_entry_slot.vs5`, `vspace.page_entry_slot.vs5`,
`vspace.mapped_entry.vs5`, `decode_table_unmap` / `decode_table_map` / `decode_table` / `decode_page_map` /
`decode_test_and_clear_accessed` / `decode_frame` / `batch_map` / `frame_batch_entry` / `decode_frame_batch` /
`vspace.decode.dec`, **`X5.decGap_vspace`** (premises: `X5.DelPlace`, `VsPlace`, `EptPlace`, `CdtHyps`,
`XferHyps`, `IrqPlace`, `X5.DelGaps`, [J] `InvVa`).
-/
import Fl4Proofs.P1.QueueDelVsX5
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}

namespace X5

/-- **[J] (x86) The invoked cap's mapping address** (`VaOK`): at every decode start reached from a `P3Ok` entry,
the invoked cap, if a mapped frame / page table / page directory / PDPT cap, names an address below `2^47`. The
invoked cap is read from a cap slot of the current thread's CSpace, so this is `X5.DelPlaceAt.va` for that slot
(sources in QueueDelVsX5's docstring). -/
def InvVa (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop) : Prop :=
  ∀ (Ac : Set U64) (s : S) (cap : capability.Cap) (extra : Aeneas.Std.Array obj.Slot 3#usize),
    EntAt st P3Ok s → DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra → VaOK cap

theorem ok_injX {α : Type _} {x y : α} (h : (ok x : Result α) = ok y) : x = y := by simpa using h

/-- An address that passed `vaddr > USER_TOP` is below `2^47`. -/
theorem va_lt {v : U64} (h : ¬ v > fl4_abi.consts.USER_TOP) : v.val < 2 ^ 47 := by
  have e := fl4_abi.consts.USER_TOP.val_eq
  first
  | (have h' : ¬ fl4_abi.consts.USER_TOP.val < v.val := fun hl => h hl
     omega)
  | scalar_tac

/-- An address equal to a mapped frame's (a remap) is below `2^47`. -/
theorem va_eq {m : Bool} {fv v : U64} (hfv : m = true → fv.val < 2 ^ 47) (hm : m = true)
    (he : ¬ (fv != v) = true) : v.val < 2 ^ 47 := by
  have e : fv = v := by
    by_contra hne
    exact he (by simpa using hne)
  rw [← e]; exact hfv hm

theorem VaOK.fr {p r v asid : U64} {sz : capability.FrameSize} {d m e : Bool}
    (h : VaOK (.Frame p sz r d m e asid v)) (hm : m = true) : v.val < 2 ^ 47 :=
  h.1 p sz r d e asid v (by rw [hm])

theorem VaOK.as_frame {c : capability.Cap} {f : vspace.FrameCap} (h : VaOK c)
    (hf : vspace.as_frame c = ok (some f)) (hm : f.mapped = true) : f.vaddr.val < 2 ^ 47 := by
  cases c with
  | Frame p sz r d m ee asid v =>
    simp only [vspace.as_frame] at hf
    cases ok_injX hf
    exact h.1 p sz r d ee asid v (by simp only at hm; rw [hm])
  | _ => simp only [vspace.as_frame] at hf; cases ok_injX hf

theorem VaOK.tbl {c : capability.Cap} {p asid v : U64} {b : Bool} (h : VaOK c)
    (hc : c = .PageTable p b asid v ∨ c = .PageDirectory p b asid v ∨ c = .Pdpt p b asid v) (hb : b = true) :
    v.val < 2 ^ 47 := by
  subst hb
  rcases hc with rfl | rfl | rfl
  · exact h.2.1 p asid v rfl
  · exact h.2.2.1 p asid v rfl
  · exact h.2.2.2 p asid v rfl

/-- **The walks from a root named at the decode's start** (`walk0`). -/
theorem walk_of {V : U64 → Prop} {s0 s : S} (Pd : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0)
    (hf : Fr0 st T Cs Ω H Sg Scs Z s0 s) (hb : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) {asid r : U64}
    (he : vspace.find_vspace_for_asid st s0 asid = ok (.Ok r)) : WalkOK st V s r := by
  have h := Pd.walk0 Ac s asid hf hb
  rw [he] at h
  exact (WP.spec_ok _).1 h r rfl

/-- `check_vspace`'s root is the one the ASID table names, and the vspace cap's (`mapped_root`). -/
theorem vspace.check_vspace.named {s : S} (vcap : capability.Cap) :
    vspace.check_vspace st s vcap ⦃ x => ∀ p, x = .Ok p →
      vspace.find_vspace_for_asid st s p.2 = ok (.Ok p.1) ∧
      ∀ r : vspace.VRoot, vspace.mapped_root vcap = ok (some r) → r.pml4 = p.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vspace.check_vspace
  split
  all_goals try (simp only [error.invalid_cap]; exact (WP.spec_ok _).2 (fun p hp => by cases hp))
  rename_i ptr b asid
  split
  · rename_i hb'
    refine WP.spec_bind (spec_eqv (P0.vspace.find_vspace_for_asid.p0 st s asid hS)) fun r hr' => ?_
    have er := hr'.1
    rcases r with r1 | lf
    · dsimp only
      split
      · simp only [error.invalid_cap]; exact (WP.spec_ok _).2 (fun p hp => by cases hp)
      · rename_i hne
        have e : r1 = ptr := UScalar.eq_of_val_eq (by simpa using hne)
        subst e
        refine (WP.spec_ok _).2 (fun p hp => ?_)
        cases hp
        refine ⟨er, fun r hr => ?_⟩
        simp only [vspace.mapped_root, hb', ↓reduceIte] at hr
        cases ok_injX hr
        rfl
    · exact (WP.spec_ok _).2 (fun p hp => by cases hp)
  · simp only [error.invalid_cap]; exact (WP.spec_ok _).2 (fun p hp => by cases hp)

/-- FrameBatch's root is `check_vspace`'s. -/
theorem fb_map_ok {A : Type _} (ar : machine.Arch A) {T' : Type _} (r : core.result.Result T' error.Exc) :
    core.result.Result.map_err (vspace.decode_frame_batch.closure.Insts.CoreOpsFunctionFnOnceTupleExcExc st ar) r ()
      ⦃ x => ∀ q, x = .Ok q → r = .Ok q ⦄ := by
  cases r <;> simp [core.result.Result.map_err,
    vspace.decode_frame_batch.closure.Insts.CoreOpsFunctionFnOnceTupleExcExc,
    vspace.decode_frame_batch.closure.Insts.CoreOpsFunctionFnOnceTupleExcExc.call_once]

set_option hygiene false in
/-- A checked or remapped address is below `2^47`. -/
local macro "vatac" : tactic => `(tactic| first
  | exact va_lt (by assumption)
  | exact va_eq hfv (by assumption) (by assumption))

theorem vspace.check_vspace.vs {V : U64 → Prop} {s0 : S} (Pd : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) {s : S}
    (hf : Fr0 st T Cs Ω H Sg Scs Z s0 s) (hb : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (vcap : capability.Cap) :
    vspace.check_vspace st s vcap ⦃ r => ∀ p, r = .Ok p → ∀ i : U64,
      V (core.num.U64.wrapping_add p.1 (core.num.U64.wrapping_mul (i &&& 511#u64) 8#u64)) ⦄ := by
  unfold vspace.check_vspace
  split
  all_goals try (simp only [error.invalid_cap]; exact (WP.spec_ok _).2 (fun p hp => by cases hp))
  rename_i ptr b asid
  split
  · refine WP.spec_bind (Pd.pml Ac s asid hf hb) fun r hr => ?_
    rcases r with r1 | lf
    · dsimp only
      split
      · simp only [error.invalid_cap]; exact (WP.spec_ok _).2 (fun p hp => by cases hp)
      · rename_i hne
        have e : r1 = ptr := UScalar.eq_of_val_eq (by simpa using hne)
        subst e
        exact (WP.spec_ok _).2 (fun p hp => by cases hp; exact hr _ rfl)
    · exact (WP.spec_ok _).2 (fun p hp => by cases hp)
  · simp only [error.invalid_cap]; exact (WP.spec_ok _).2 (fun p hp => by cases hp)

theorem vspace.table_entry_slot.vs5 {V : U64 → Prop} {s : S} {root : U64}
    (hroot : ∀ i : U64, V (core.num.U64.wrapping_add root (core.num.U64.wrapping_mul (i &&& 511#u64) 8#u64)))
    (hw : WalkOK st V s root) (vaddr level : U64) (hv : vaddr.val < 2 ^ 47) :
    vspace.table_entry_slot st s root vaddr level ⦃ r => ∀ x, r = .Ok x → V x ⦄ := by
  unfold vspace.table_entry_slot
  refine WP.spec_bind (Pₘ := fun r => ∀ x, r = .Ok x → V x) ?_ fun r hr => ?_
  · split
    · exact (hw vaddr hv).2.1
    split
    · exact (hw vaddr hv).2.2
    · refine WP.spec_bind (P0.vspace.idx.p0 vaddr _) fun ix _ => ?_
      unfold vspace.entry_addr
      simp only [lift, bind_ok, WP.spec_ok]
      exact fun x hx => by cases hx; exact hroot ix
  rcases r with x | lf
  · exact (WP.spec_ok _).2 fun x' hx => by cases hx; exact hr x rfl
  · simp only [vspace.failed_lookup]; exact (WP.spec_ok _).2 fun x' hx => by cases hx

theorem vspace.page_entry_slot.vs5 {V : U64 → Prop} {s : S} {root : U64} (hw : WalkOK st V s root)
    (vaddr : U64) (hv : vaddr.val < 2 ^ 47) (fs : capability.FrameSize) :
    vspace.page_entry_slot st s root vaddr fs ⦃ r => ∀ x, r = .Ok x → V x ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vspace.page_entry_slot
  refine WP.spec_bind (Pₘ := fun r => ∀ x, r = .Ok x → V x) ?_ fun r hr => ?_
  · cases fs
    · exact (hw vaddr hv).1
    · exact (hw vaddr hv).2.1
    · exact (hw vaddr hv).2.2
  rcases r with x | lf
  · have hx := hr x rfl
    dsimp only
    refine WP.spec_bind (Pₘ := fun _ => True) (by cases fs <;> exact (WP.spec_ok _).2 trivial) fun b _ => ?_
    split
    · exact (WP.spec_ok _).2 fun x' hx' => by cases hx'; exact hx
    refine WP.spec_bind (LawfulStore.read_spec s x) fun old _ => ?_
    repeat' (first
      | exact (WP.spec_ok _).2 fun x' hx' => by cases hx'; exact hx
      | exact (WP.spec_ok _).2 fun x' hx' => by cases hx'
      | (simp only [lift, bind_ok])
      | (refine WP.spec_bind (Pₘ := fun _ => True) (by p0_auto) fun _ _ => ?_)
      | split)
  · simp only [vspace.failed_lookup]; exact (WP.spec_ok _).2 fun x' hx => by cases hx


theorem vspace.mapped_entry.vs5 {V : U64 → Prop} {s : S} {root : U64} (hw : WalkOK st V s root)
    (f : vspace.FrameCap) (hv : f.vaddr.val < 2 ^ 47) :
    vspace.mapped_entry st s f root ⦃ o => ∀ x, o = some x → V x ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vspace.mapped_entry
  refine WP.spec_bind (P0.layout.paddr.p0 _) fun pa _ => ?_
  refine WP.spec_bind (Pₘ := fun _ => True) (by cases f.size <;> exact (WP.spec_ok _).2 trivial) fun large _ => ?_
  refine WP.spec_bind (Pₘ := fun r => ∀ x, r = .Ok x → V x) ?_ fun r hr => ?_
  · split
    · exact (hw f.vaddr hv).2.1
    · exact (hw f.vaddr hv).1
  rcases r with x | lf
  · have hx := hr x rfl
    dsimp only
    refine WP.spec_bind (LawfulStore.read_spec s x) fun e _ => ?_
    repeat' (first
      | exact (WP.spec_ok _).2 fun x' hx' => by cases hx'; exact hx
      | exact (WP.spec_ok _).2 fun x' hx' => by cases hx'
      | (simp only [lift, bind_ok])
      | (refine WP.spec_bind (Pₘ := fun _ => True) (by p0_auto) fun _ _ => ?_)
      | split)
  · exact (WP.spec_ok _).2 fun x' hx => by cases hx

set_option hygiene false in
/-- An error leaf with the state unchanged. -/
local macro "errV" : tactic => `(tactic| first
  | exact D.err _
  | exact (WP.spec_ok _).2 (D.err _)
  | (simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok,
      error.illegal, error.truncated, error.range, error.invalid_cap, error.invalid_arg, vspace.failed_lookup]
     first | exact D.err _ | exact (WP.spec_ok _).2 (D.err _)))

set_option maxHeartbeats 4000000 in
/-- **A table's unmap**: the restart, the unmap of its mapping (VSpace
words), the table's clearing, and the cap's update. -/
theorem vspace.decode_table_unmap.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s : S} (Pd : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s)  {cap0 : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap0 extra)
    (a : A) (slot : U64) (cap : capability.Cap) (level ptr : U64) (mapped : Bool) (masid mvaddr : U64)
    (hslot : CapSlotW T Ω Sg slot) (hz : FreeRegion Ω Sg ptr 4096#u64)
    (hva : mapped = true → mvaddr.val < 2 ^ 47) :
    vspace.decode_table_unmap st ar s a slot cap level ptr mapped masid mvaddr ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vspace.decode_table_unmap
  refine WP.spec_bind (P0.cdt.is_final_capability.p0 st s slot hS) fun b _ => ?_
  split
  swap
  · errV
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e
  refine WP.spec_bind (Cur0.restart D) fun s1 h1 => ?_
  obtain ⟨Ac1, hb1⟩ := h1.bxi
  refine WP.spec_bind (Pₘ := fun r : S × A => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s r.1) ?_ ?_
  · split
    · refine WP.spec_bind (Pₘ := fun r : S × A => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s r.1) ?_ ?_
      · split
        · exact WP.spec_mono (vspace.unmap_page_table.vs5 hA s1 a masid mvaddr ptr Pd.vs
            (hva (by assumption)) (Pd.walk Ac1 s1 masid h1.fr hb1)) fun r w => h1.vs Pd.vs w
        split
        · exact WP.spec_mono (vspace.unmap_page_directory.vs5 hA s1 a masid mvaddr ptr Pd.vs
            (hva (by assumption)) (Pd.walk Ac1 s1 masid h1.fr hb1)) fun r w => h1.vs Pd.vs w
        · exact WP.spec_mono (vspace.unmap_pdpt.vs hA s1 a masid mvaddr ptr Pd.vs (Pd.pml Ac1 s1 masid h1.fr hb1))
            fun r w => h1.vs Pd.vs w
      rintro ⟨s3, a2⟩ h3
      try simp only [uncurry_apply_pair]
      refine WP.spec_bind (LawfulStore.zero_spec s3 ptr 4096#u64) fun s4 e4 => ?_
      subst e4
      exact (WP.spec_ok _).2 (Cur0.zr h3 hz)
    · exact (WP.spec_ok _).2 h1
  rintro ⟨s2, a1⟩ h2
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (P0.vspace.with_mapping.p0 cap false masid mvaddr) fun c _ => ?_
  refine WP.spec_bind (obj.Slot.set_cap.capw (c := c) (s := s2) hslot) fun s3 w3 => ?_
  exact (WP.spec_ok _).2 (h2.capw w3 fun _ hb => hb).post

set_option maxHeartbeats 4000000 in
/-- **A table's map**: the restart, the cap's update and the table entry's
write (a VSpace word). -/
theorem vspace.decode_table_map.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s : S} (Pd : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s)  {cap0 : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap0 extra)
    (a : A) (len slot : U64) (cap : capability.Cap) (level ptr buf : U64) (hslot : CapSlotW T Ω Sg slot) :
    vspace.decode_table_map st ar s a len slot cap level ptr buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hb := D.bxi
  unfold vspace.decode_table_map
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e
  refine WP.spec_bind (P0.vspace.extra.p0 extra 0#usize) fun o _ => ?_
  rcases o with _ | x
  · errV
  try dsimp only
  split
  swap
  · errV
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun i0 _ => ?_
  try simp only [lift, bind_ok]
  refine WP.spec_bind (Pₘ := fun _ => True) (by p0_auto) fun i2 _ => ?_
  try simp only [lift, bind_ok]
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun attr _ => ?_
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st x s hS) fun vcap _ => ?_
  refine WP.spec_bind (P0.vspace.is_valid_vtable_root.p0 vcap) fun bv _ => ?_
  split
  swap
  · errV
  split
  · errV
  rename_i hvt
  refine WP.spec_bind (WP.spec_and (vspace.check_vspace.vs Pd (WritesIn.refl _ _) hb vcap)
    (vspace.check_vspace.named vcap)) fun r hr => ?_
  rcases r with ⟨root, asid⟩ | e
  swap
  · errV
  have hroot := hr.1 _ rfl
  have hw := walk_of Pd (WritesIn.refl _ _) hb (hr.2 _ rfl).1
  simp only [irq_branch_ok, bind_ok]
  refine WP.spec_bind (vspace.table_entry_slot.vs5 hroot hw _ level (va_lt hvt)) fun r1 hr1 => ?_
  rcases r1 with v | e
  swap
  · errV
  have hv := hr1 v rfl
  simp only [irq_branch_ok, bind_ok]
  refine WP.spec_bind (LawfulStore.read_spec s v) fun i5 _ => ?_
  refine WP.spec_bind (Pₘ := fun _ => True) (by p0_auto) fun i6 _ => ?_
  try simp only [lift, bind_ok]
  split
  · errV
  refine WP.spec_bind (P0.layout.paddr.p0 ptr) fun i8 _ => ?_
  refine WP.spec_bind (P0.vspace.make_user_table.p0 i8 attr) fun en _ => ?_
  refine WP.spec_bind (Cur0.restart D) fun s1 h1 => ?_
  refine WP.spec_bind (P0.vspace.with_mapping.p0 cap true asid _) fun c _ => ?_
  refine WP.spec_bind (obj.Slot.set_cap.capw (c := c) (s := s1) hslot) fun s2 w2 => ?_
  have h2 := h1.capw w2 fun _ hb => hb
  refine WP.spec_bind (LawfulStore.write_spec s2 v en) fun s3 e3 => ?_
  subst e3
  have h3 := h2.vs Pd.vs (writesIn_wr_V (v := en) Pd.vs hv)
  refine WP.spec_bind (hA.invalidate_page_structures a asid) fun a1 _ => ?_
  exact (WP.spec_ok _).2 h3.post

set_option maxHeartbeats 4000000 in
/-- **The paging-structure caps' decode** (map, unmap). -/
theorem vspace.decode_table.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s : S} (Pd : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s) (Vs : VsPlace st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) 
    {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hE : EntAt st P3Ok s)
    (a : A) (lbl len slot buf : U64) (hslot : CapSlotW T Ω Sg slot) (hvi : VaOK cap) :
    vspace.decode_table st ar s a lbl len slot cap buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  unfold vspace.decode_table
  cases cap
  all_goals simp only [vspace.as_table, bind_ok]
  all_goals try errV
  all_goals
    rename_i ptr m asd va
    try dsimp only
    split
    · exact vspace.decode_table_unmap.dec hA Pd D a slot _ _ ptr m asd va hslot
        (Vs.tbl _ _ _ _ hE D ptr m asd va (by simp))
        (fun hm => VaOK.tbl (p := ptr) (asid := asd) hvi (by simp) hm)
    split
    swap
    · errV
    split
    · refine WP.spec_bind (P0.vspace.extra.p0 extra 0#usize) fun o _ => ?_
      rcases o with _ | x
      · errV
      try dsimp only
      split <;> errV
    · exact vspace.decode_table_map.dec hA Pd D a len slot _ _ ptr buf hslot


set_option hygiene false in
/-- The page map's tail, from the frame size's match: the entry slot (a
VSpace word), the restart, the cap's update and the entry's write. -/
local macro "pmtail" : tactic => `(tactic| (
  try simp only [bind_ok, uncurry_apply_pair, Bool.false_eq_true, ↓reduceIte]
  -- #65: a 1 GiB frame needs `huge_pages` (else IllegalOperation); every
  -- size then rebinds `large` by a match on the size.
  try (refine WP.spec_bind (P0.vspace.huge_pages.p0 st s hS) fun hp _ => ?_
       split
       swap
       · errV)
  try refine WP.spec_bind (Pₘ := fun _ => True) ((WP.spec_ok _).2 trivial) fun _ _ => ?_
  refine WP.spec_bind (vspace.page_entry_slot.vs5 (by rw [hrp _ emr]; exact hw) _ (by vatac) _)
    fun r3 hr3 => ?_
  rcases r3 with v | e
  swap
  · errV
  have hv := hr3 v rfl
  simp only [irq_branch_ok, bind_ok]
  refine WP.spec_bind (P0.vspace.frame_address.p0 st ar s a _ hS hA) fun _ _ => ?_
  refine WP.spec_bind (P0.vspace.make_user_page.p0 st s _ _ _ _ hS) fun en _ => ?_
  refine WP.spec_bind (Cur0.restart D) fun s1 h1 => ?_
  refine WP.spec_bind (obj.Slot.set_cap.capw (s := s1) hslot) fun s2 w2 => ?_
  refine WP.spec_bind (vspace.write_mapping.cur0 hA Pd.vs (h1.capw w2 fun _ hb => hb) a hv en _ _ _) ?_
  rintro ⟨s3, a1⟩ h3
  exact (WP.spec_ok _).2 h3.post))

set_option hygiene false in
/-- The pure steps and error leaves before the page map's tail. -/
local macro "pmpre" : tactic => `(tactic| (
  repeat' (first
    | (refine WP.spec_bind (vspace.check_vspace.named _) fun r1 hr1 => ?_
       rcases r1 with p | e
       swap
       · errV
       have hw := walk_of Pd (WritesIn.refl _ _) hb (hr1 p rfl).1
       have hrp := (hr1 p rfl).2
       simp only [irq_branch_ok, bind_ok])
    | (simp only [lift, bind_ok])
    -- #65: the size's `huge` test (`if false = true` / `if true = true`).
    | (simp only [Bool.false_eq_true, eq_self_iff_true, ↓reduceIte])
    | (refine WP.spec_bind (P0.capability.Rights.from_word.p0 _) fun _ _ => ?_)
    | (refine WP.spec_bind (P0.capability.mask_vm_rights.p0 _ _) fun _ _ => ?_)
    | (refine WP.spec_bind (P0.capability.FrameSize.bits.p0 _) fun _ _ => ?_)
    | (refine WP.spec_bind (shl_and63 _) fun _ _ => ?_)
    | (split; · errV))))

set_option maxHeartbeats 8000000 in
/-- **The page map**: the restart, the frame cap's update and the entry's
write (a VSpace word). -/
theorem vspace.decode_page_map.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s : S} (Pd : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s)  {cap0 : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap0 extra)
    (a : A) (len slot : U64) (f : vspace.FrameCap) (buf : U64) (hslot : CapSlotW T Ω Sg slot)
    (hfv : f.mapped = true → f.vaddr.val < 2 ^ 47) :
    vspace.decode_page_map st ar s a len slot f buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hb := D.bxi
  obtain ⟨fptr, fsize, frights, fdev, fmapped, fept, fasid, fva⟩ := f
  unfold vspace.decode_page_map
  cases fsize
  all_goals try dsimp only
  all_goals
    step with sched.cur_thread.spec as ⟨ct, ect⟩
    have e : ct = L.curW s := ect
    subst e
    refine WP.spec_bind (P0.vspace.extra.p0 extra 0#usize) fun o _ => ?_
    rcases o with _ | x
    · errV
    try dsimp only
    -- #65: `split` on the grown body exceeds simp's step limit.
    by_cases hl3 : len ≥ 3#u64
    swap
    · rw [if_neg hl3]; errV
    rw [if_pos hl3]
    refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun vaddr _ => ?_
    refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
    refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
    try simp only [lift, bind_ok]
    refine WP.spec_bind (P0.obj.Slot.cap.p0 st x s hS) fun vcap _ => ?_
    refine WP.spec_bind (spec_eqv (P0.vspace.mapped_root.p0 vcap)) fun o1 ⟨emr, _⟩ => ?_
    rcases o1 with _ | r
    · errV
    all_goals
      try dsimp only
      split
      · split
        · split
          · errV
          split
          · errV
          pmpre
          pmtail
        · pmpre
          pmtail
      · pmpre
        pmtail


set_option maxHeartbeats 4000000 in
/-- **TestAndClearAccessed**: the entry's accessed bit cleared (a VSpace
word), then the reply. -/
theorem vspace.decode_test_and_clear_accessed.dec {V : U64 → Prop} {s : S} (Pd : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)  {cap0 : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap0 extra)
    (f : vspace.FrameCap) (call : Bool) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s)
    (hfv : f.mapped = true → f.vaddr.val < 2 ^ 47) :
    vspace.decode_test_and_clear_accessed st s f call ⦃ r =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r.1 r.2 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hb := D.bxi
  have hct : L.curW s ∈ T := hb.1.choose_spec.choose_spec.curT
  obtain ⟨fptr, fsize, frights, fdev, fmapped, fept, fasid, fva⟩ := f
  unfold vspace.decode_test_and_clear_accessed
  cases fsize
  all_goals simp only [bind_ok, uncurry_apply_pair, Bool.false_eq_true, ite_false]
  all_goals try (simp only [error.illegal, bind_ok, ite_true]; exact (WP.spec_ok _).2 (D.err _))
  all_goals
    try dsimp only
    split
    swap
    · errV
    split
    · errV
    refine WP.spec_bind (Pd.walk Ac s _ (WritesIn.refl _ _) hb) fun r hwr => ?_
    rcases r with r1 | e
    swap
    · errV
    try dsimp only
    refine WP.spec_bind (vspace.mapped_entry.vs5 (hwr r1 rfl) _ (by exact hfv (by assumption))) fun o ho => ?_
    rcases o with _ | x
    · errV
    have hx := ho x rfl
    try dsimp only
    step with sched.cur_thread.spec as ⟨ct, ect⟩
    have e : ct = L.curW s := ect
    subst e
    refine WP.spec_bind (Pₘ := fun _ => True) (by p0_auto) fun i _ => ?_
    try simp only [lift, bind_ok]
    refine WP.spec_bind (LawfulStore.fetch_and_spec s x _) ?_
    rintro ⟨old, s1⟩ e1
    try simp only [uncurry_apply_pair]
    try dsimp only
    obtain ⟨hold, e1⟩ := Prod.mk.inj e1
    rw [← hold] at e1
    subst e1
    obtain ⟨h1, -, -, ec, -, fld, -, -⟩ := blk_of_vs hb.blk Pd.vs (writesIn_wr_V (v := old &&& ~~~i) Pd.vs hx)
    have hU1 : UserOK st T Cs Ω H U (L.wr s x (old &&& ~~~i)) := D.user.ksb (L.ksb_wr _ _ _)
    have hr1 : Runnable (L.mem (L.wr s x (old &&& ~~~i)) (stA (L.curW s))) := by
      rw [stA_eq, fld _ hct _ (by simp) (by simp) (by simp), ← stA_eq]; exact D.run
    have hG1 : XG st T Cs Ω H Sg Scs Z P3Ok (L.wr s x (old &&& ~~~i)) :=
      hG.of_fr ((writesIn_wr_V (v := old &&& ~~~i) Pd.vs hx).mono fun b hb =>
        Or.inr (Or.inr (Or.inl (Or.inr (Pd.vs b hb).2))))
    split
    · exact WP.spec_bind (vspace.reply1.bxi E (BlkOK.bxi h1) hU1 hct hr1 call _ hG1) fun s2 h2 =>
        (WP.spec_ok _).2 (DecPost.ok_bxi h2)
    · exact WP.spec_bind (vspace.reply1.bxi E (BlkOK.bxi h1) hU1 hct hr1 call _ hG1) fun s2 h2 =>
        (WP.spec_ok _).2 (DecPost.ok_bxi h2)


set_option maxHeartbeats 8000000 in
/-- **The frame caps' decode**. -/
theorem vspace.decode_frame.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s : S} (Pd : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s) (Vs : VsPlace st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (Pe : EptPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok) (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) 
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (fp fsz : _) (fr : U64) (fd fm fe : Bool) (fa fv : U64)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Frame fp fsz fr fd fm fe fa fv) extra) (hE : EntAt st P3Ok s)
    (a : A) (lbl len slot : U64) (call : Bool) (buf : U64) (hslot : CapSlotW T Ω Sg slot)
    (hvi : VaOK (.Frame fp fsz fr fd fm fe fa fv)) :
    vspace.decode_frame st ar s a lbl len slot (.Frame fp fsz fr fd fm fe fa fv) call buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hb := D.bxi
  have hct : L.curW s ∈ T := hb.1.choose_spec.choose_spec.curT
  unfold vspace.decode_frame
  simp only [vspace.as_frame, bind_ok]
  split
  · exact Vs.eptMap _ _ _ _ _ _ _ _ hE D
  split
  · split
    · split
      · errV
      · exact vspace.decode_page_map.dec hA Pd D a len slot _ buf hslot (by intro hm; exact VaOK.fr hvi hm)
    · exact vspace.decode_page_map.dec hA Pd D a len slot _ buf hslot (by intro hm; exact VaOK.fr hvi hm)
  split
  · step with sched.cur_thread.spec as ⟨ct, ect⟩
    have e : ct = L.curW s := ect
    subst e
    refine WP.spec_bind (Cur0.restart D) fun s1 h1 => ?_
    obtain ⟨Ac1, hb1⟩ := h1.bxi
    refine WP.spec_bind (Pₘ := fun r : S × A => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s r.1) ?_ ?_
    · split
      · split
        · split
          · refine WP.spec_bind (P0.capability.FrameSize.bits.p0 _) fun i _ => ?_
            exact ept.unmap.cur0 hA _ _ _ _ _ _ (Pe.find Ac1 s s1 _ hE h1.fr hb1) h1
          · exact WP.spec_mono (vspace.unmap_page.vs5 hA s1 a _ _ _ _ Pd.vs (by exact VaOK.fr hvi (by assumption))
              (Pd.walk Ac1 s1 _ h1.fr hb1)) fun r w => h1.vs Pd.vs w
        · exact (WP.spec_ok _).2 h1
      · exact (WP.spec_ok _).2 h1
    rintro ⟨s2, a1⟩ h2
    try simp only [uncurry_apply_pair]
    refine WP.spec_bind (obj.Slot.set_cap.capw (s := s2) hslot) fun s3 w3 => ?_
    exact (WP.spec_ok _).2 (h2.capw w3 fun _ hb => hb).post
  split
  · step with sched.cur_thread.spec as ⟨ct, ect⟩
    have e : ct = L.curW s := ect
    subst e
    refine WP.spec_bind (sched.set_thread_state.restart_blk (Es := ∅) s _ D.bxi.blk hct (runnable_ok D.run).1
      (runnable_ok D.run).2) fun s1 ⟨h1, f1, hst1, _⟩ => ?_
    refine WP.spec_bind (P0.layout.paddr.p0 _) fun i _ => ?_
    refine WP.spec_bind (vspace.reply1.bxi E (BlkOK.bxi h1) (D.user.ksb f1.1) hct (hst1 ▸ runnable_restart) call i (hE.xg.of_fr (Foot.cur0w f1 (Set.empty_subset _))))
      fun s2 h2 => ?_
    exact (WP.spec_ok _).2 (DecPost.ok_bxi h2)
  split
  · refine WP.spec_bind (vspace.decode_test_and_clear_accessed.dec Pd E D _ call hE.xg
      (by intro hm; exact VaOK.fr hvi hm)) ?_
    rintro ⟨r, s1⟩ hr
    exact (WP.spec_ok _).2 hr
  split
  · exact vspace.derive_subframe.dec C Vs D hE a len slot _ buf hslot
  · errV

/-- An `if` at the head of the program (or of its first bind), by cases on the
condition (`split` on the batch's grown bodies exceeds simp's step limit). -/
local macro "ihead" : tactic => `(tactic| first
  | (refine p0_if _ _ _ _ ?_ ?_ <;> intro)
  | (refine p0_if_bind _ _ _ _ _ ?_ ?_ <;> intro))

set_option hygiene false in
/-- A batch leaf with the state unchanged (`h : Cur0 … s0 s`). -/
local macro "cleaf" : tactic => `(tactic| first
  | exact (WP.spec_ok _).2 h
  | (simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok,
      error.illegal, error.truncated, error.range, error.invalid_cap, error.invalid_arg, vspace.failed_lookup]
     exact (WP.spec_ok _).2 h))

set_option maxHeartbeats 8000000 in
/-- **`batch_map`**: the frame cap's update in its slot and the entry's write
(a VSpace word), all at a state inside the batch. -/
theorem vspace.batch_map.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 s : S} (Pd : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (a : A) (slot : U64) (hslot : SlotW T Ω Sg slot) (b : vspace.Batch) (vaddr : U64)
    (hrt : ∃ a0, vspace.find_vspace_for_asid st s0 a0 = ok (.Ok b.root)) :
    vspace.batch_map st ar s a slot b vaddr ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  obtain ⟨Ac1, hb⟩ := h.bxi
  have hf := h.fr
  unfold vspace.batch_map
  have hw : WalkOK st V s b.root := by obtain ⟨a0, e0⟩ := hrt; exact walk_of Pd hf hb e0
  refine WP.spec_bind (Pd.va Ac1 s slot hf hb hslot) fun c hvc => ?_
  refine WP.spec_bind (spec_eqv (P0.vspace.as_frame.p0 c)) fun o ⟨eo, _⟩ => ?_
  rcases o with _ | f
  · cleaf
  have hfv := VaOK.as_frame hvc eo
  obtain ⟨fptr, fsize, frights, fdev, fmapped, fept, fasid, fva⟩ := f
  cases fsize <;> simp only [bind_ok, Bool.false_eq_true, ↓reduceIte] <;>
    (repeat' (first
      | cleaf
      | (refine WP.spec_bind (vspace.page_entry_slot.vs5 hw _ (by vatac) _) fun r3 hr3 => ?_
         rcases r3 with v | e
         · have hv := hr3 v rfl
           simp only [irq_branch_ok, bind_ok]
           refine WP.spec_bind (P0.vspace.frame_address.p0 st ar s a _ hS hA) fun _ _ => ?_
           refine WP.spec_bind (P0.vspace.make_user_page.p0 st s _ _ _ _ hS) fun en _ => ?_
           refine WP.spec_bind (obj.Slot.set_cap.capw (s := s) hslot) fun s2 w2 => ?_
           refine WP.spec_bind (vspace.write_mapping.cur0 hA Pd.vs (h.capw w2 fun _ hb => hb) a hv en _ _ _) ?_
           rintro ⟨s3, a1⟩ h3
           exact (WP.spec_ok _).2 h3
         · cleaf)
      | (simp only [lift, bind_ok, bind_tc_ok])
      | (refine WP.spec_bind (P0.vspace.huge_pages.p0 st s hS) fun _ _ => ?_)
      | (refine WP.spec_bind (P0.capability.Rights.from_word.p0 _) fun _ _ => ?_)
      | (refine WP.spec_bind (P0.capability.mask_vm_rights.p0 _ _) fun _ _ => ?_)
      | (refine WP.spec_bind (P0.capability.FrameSize.bits.p0 _) fun _ _ => ?_)
      | (refine WP.spec_bind (shl_and63 _) fun _ _ => ?_)
      | (refine WP.spec_bind (Pₘ := fun _ => True) (by p0_auto) fun _ _ => ?_)
      | ihead
      | split))

set_option maxHeartbeats 8000000 in
/-- **One batch entry** (`frame_batch_entry`) at a state inside the batch:
COPY_MAP's insertion (`CdtHyps.ins`), map (`batch_map.cur0`) and rollback
delete (`cdt.delete.cur0`), REMAP's map, DELETE's deferred unmap (VSpace
words), the cap's update and the delete. The lookups through the batch's
CNode caps (read from cap slots at the decode's start) give cap slots
(`VsPlace.fbTgt` / `fbSrc`). -/
theorem vspace.frame_batch_entry.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 s : S} (Pd : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (G : DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0)
    (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok) (Vs : VsPlace st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (hE : EntAt st P3Ok s0) (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (a : A) (b : vspace.Batch)
    (hcn : ∃ x, CapSlotW T Ω Sg x ∧ obj.Slot.cap st x s0 = ok b.cnode)
    (hdn : ∃ x, CapSlotW T Ω Sg x ∧ obj.Slot.cap st x s0 = ok b.dest_cnode) (w0 w1 w2 : U64) (d : Bool)
    (hrt : ∃ a0, vspace.find_vspace_for_asid st s0 a0 = ok (.Ok b.root)) :
    vspace.frame_batch_entry st ar s a b w0 w1 w2 d ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  obtain ⟨Ac1, hb⟩ := h.bxi
  obtain ⟨xc, hxc, ec⟩ := hcn
  obtain ⟨xd, hxd, ed⟩ := hdn
  have hw : WalkOK st V s b.root := by obtain ⟨a0, e0⟩ := hrt; exact walk_of Pd h.fr hb e0
  unfold vspace.frame_batch_entry
  ihead
  · -- COPY_MAP
    refine WP.spec_bind (Vs.fbTgt Ac1 s0 s xd _ w1 b.depth hE h.fr hb hxd ed) fun r hr => ?_
    rcases r with v | e
    swap
    · cleaf
    have hv := hr v rfl
    simp only [irq_branch_ok, bind_ok]
    refine WP.spec_bind (P0.cdt.ensure_empty_slot.p0 st s v hS) fun r1 _ => ?_
    rcases r1 with _ | e
    swap
    · cleaf
    simp only [irq_branch_ok, bind_ok]
    refine WP.spec_bind (Vs.fbSrc Ac1 s0 s xc _ w0 b.depth hE h.fr hb hxc ec) fun r2 hr2 => ?_
    rcases r2 with v1 | e
    swap
    · cleaf
    have hv1 := hr2 v1 rfl
    simp only [irq_branch_ok, bind_ok]
    refine WP.spec_bind (P0.obj.Slot.cap.p0 st v1 s hS) fun sc _ => ?_
    refine WP.spec_bind (P0.vspace.as_frame.p0 sc) fun o _ => ?_
    try dsimp only
    ihead
    · cleaf
    refine WP.spec_bind (P0.capability.Rights.from_word.p0 _) fun r3 _ => ?_
    refine WP.spec_bind (P0.capability.mask_cap_rights.p0 _ _) fun masked _ => ?_
    refine WP.spec_bind (P0.objects.derive_cap.p0 st s v1 masked hS) fun r4 _ => ?_
    rcases r4 with c4 | e
    swap
    · cleaf
    simp only [irq_branch_ok, bind_ok]
    refine WP.spec_bind (C.ins Ac1 s0 s c4 sc v1 v hE h.fr hb (SlotW.capw0 hv1) (SlotW.capw0 hv)) fun s1 w1' => ?_
    have h1 := h.capw w1' fun _ hb => hb
    refine WP.spec_bind (vspace.batch_map.cur0 hA Pd h1 a v hv b w2 hrt) ?_
    rintro ⟨r5, s2, a1⟩ h2
    try dsimp only
    refine WP.spec_bind (P0.core.result.Result.is_err.spec r5) fun b2 _ => ?_
    ihead
    · refine WP.spec_bind (cdt.delete.cur0 hA G h2 hv) ?_
      rintro ⟨r6, s3, a2⟩ h3
      exact (WP.spec_ok _).2 h3
    · exact (WP.spec_ok _).2 h2
  ihead
  · -- REMAP
    refine WP.spec_bind (Vs.fbSrc Ac1 s0 s xc _ w0 b.depth hE h.fr hb hxc ec) fun r hr => ?_
    rcases r with v | e
    swap
    · cleaf
    have hv := hr v rfl
    simp only [irq_branch_ok, bind_ok]
    refine WP.spec_bind (vspace.batch_map.cur0 hA Pd h a v hv b w1 hrt) ?_
    rintro ⟨r1, s1, a1⟩ h1
    exact (WP.spec_ok _).2 h1
  -- DELETE
  refine WP.spec_bind (Vs.fbTgt Ac1 s0 s xc _ w0 b.depth hE h.fr hb hxc ec) fun r hr => ?_
  rcases r with v | e
  swap
  · cleaf
  have hv := hr v rfl
  simp only [irq_branch_ok, bind_ok]
  refine WP.spec_bind (Pd.va Ac1 s v h.fr hb hv) fun c hvc => ?_
  refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
  ihead
  · cleaf
  refine WP.spec_bind (spec_eqv (P0.vspace.as_frame.p0 c)) fun o ⟨eo, _⟩ => ?_
  rcases o with _ | f
  · cleaf
  have hfv := VaOK.as_frame hvc eo
  try dsimp only
  refine WP.spec_bind (Pₘ := fun r : S × Bool => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1) ?_ ?_
  · repeat' (first
      | exact (WP.spec_ok _).2 h
      | (have hk := hw f.vaddr (hfv (by assumption))
         refine WP.spec_bind (vspace.unmap_page_unflushed.vs s b.root f.size f.vaddr f.ptr Pd.vs
            hk.1 hk.2.1 hk.2.2) ?_
         rintro ⟨b2, s2⟩ w2
         have h2 := h.vs Pd.vs w2
         try dsimp only
         refine WP.spec_bind (Pₘ := fun _ => True) (by split <;> exact (WP.spec_ok _).2 trivial) fun _ _ => ?_
         refine WP.spec_bind (obj.Slot.set_cap.capw (s := s2) hv) fun s3 w3 => ?_
         exact (WP.spec_ok _).2 (h2.capw w3 fun _ hb => hb))
      | ihead
      | split)
  rintro ⟨s1, d1⟩ h1
  try dsimp only
  refine WP.spec_bind (cdt.delete.cur0 hA G h1 hv) ?_
  rintro ⟨r2, s2, a2⟩ h2
  exact (WP.spec_ok _).2 h2
set_option maxHeartbeats 8000000 in
/-- **FrameBatch** (`decode_frame_batch`, #71): the decode's checks (no
state change), the loop (`Cur0` from the decode's start, no restart), the
deferred flush (machine state only), the reply's message registers (`XS`) and
the thread set running. -/
theorem vspace.decode_frame_batch.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s : S} (Pd : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s) (G : DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s)
    (Vs : VsPlace st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok) (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hE : EntAt st P3Ok s)
    (hx : ∀ sl ∈ extra.val, sl ≠ 0#u64 → CapSlotW T Ω Sg sl)
    (a : A) (len ptr : U64) (mapped : Bool) (asid : U64) (call : Bool) (buf : U64) :
    vspace.decode_frame_batch st ar s a len ptr mapped asid call buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hb := D.bxi
  have hct : L.curW s ∈ T := hb.1.choose_spec.choose_spec.curT
  have and255 : ∀ x : U64, (x &&& 255#u64).val ≤ 255 := fun x => by
    rw [UScalar.val_and]; exact Nat.le_trans Nat.and_le_right (by decide)
  unfold vspace.decode_frame_batch
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e
  ihead
  swap
  · errV
  refine WP.spec_bind (vspace.check_vspace.named _) fun r hr => ?_
  refine WP.spec_bind (fb_map_ok ar r) fun r1 hr1 => ?_
  rcases r1 with ⟨root, x0⟩ | e
  swap
  · errV
  have hroot : ∃ a0, vspace.find_vspace_for_asid st s a0 = ok (.Ok root) := ⟨_, (hr _ (hr1 _ rfl)).1⟩
  simp only [irq_branch_ok, bind_ok]
  try dsimp only
  ihead
  · errV
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun hdr _ => ?_
  try simp only [lift, bind_ok]
  refine WP.spec_bind (Pₘ := fun _ => True) (by p0_auto) fun i _ => ?_
  try simp only [lift, bind_ok]
  refine WP.spec_bind (Pₘ := fun _ => True) (by p0_auto) fun i1 _ => ?_
  try simp only [lift, bind_ok]
  refine WP.spec_bind (P0.vspace.frame_batch.entry_words.spec _) fun words hw => ?_
  refine WP.spec_bind (P0.vspace.frame_batch.DEFINED.p0) fun i2 _ => ?_
  try simp only [lift, bind_ok]
  ihead
  · errV
  ihead
  · errV
  ihead
  · errV
  ihead
  · errV
  have hm : words.val * (i &&& 255#u64).val ≤ 3 * 255 := Nat.mul_le_mul hw (and255 i)
  step as ⟨i5, hi5⟩
  step as ⟨i6, hi6⟩
  ihead
  · errV
  refine WP.spec_bind (vspace.extra.mem extra 0#usize) fun o ho => ?_
  rcases o with _ | x
  · errV
  obtain ⟨hxm, hx0⟩ := ho x rfl
  have hxs := hx x hxm hx0
  try dsimp only
  refine WP.spec_bind (spec_eqv (P0.obj.Slot.cap.p0 st x s hS)) fun cnode ⟨ecn, _⟩ => ?_
  refine WP.spec_bind (Pₘ := fun _ => True) (by split <;> exact (WP.spec_ok _).2 trivial) fun bc _ => ?_
  ihead
  swap
  · errV
  refine WP.spec_bind (vspace.extra.mem extra 1#usize) fun o1 ho1 => ?_
  refine WP.spec_bind (Pₘ := fun dc => ∃ y, CapSlotW T Ω Sg y ∧ obj.Slot.cap st y s = ok dc) (by
    rcases o1 with _ | x1
    · exact (WP.spec_ok _).2 ⟨x, hxs, ecn⟩
    obtain ⟨hxm1, hx01⟩ := ho1 x1 rfl
    try dsimp only
    split
    · exact WP.spec_mono (spec_eqv (P0.obj.Slot.cap.p0 st x1 s hS)) fun c hc => ⟨x1, hx x1 hxm1 hx01, hc.1⟩
    · exact (WP.spec_ok _).2 ⟨x, hxs, ecn⟩) fun dcn hdcn => ?_
  refine WP.spec_bind (Pₘ := fun _ => True) (by split <;> exact (WP.spec_ok _).2 trivial) fun bd _ => ?_
  ihead
  swap
  · errV
  try simp only [lift, bind_ok]
  refine WP.spec_bind (Pₘ := fun _ => True) (by p0_auto) fun _ _ => ?_
  try simp only [lift, bind_ok]
  refine WP.spec_bind (Pₘ := fun _ => True) (by p0_auto) fun _ _ => ?_
  try simp only [lift, bind_ok]
  refine WP.spec_bind (Pₘ := fun _ => True) (by p0_auto) fun _ _ => ?_
  try simp only [lift, bind_ok]
  refine WP.spec_bind (P0.vspace.frame_batch.DEFER_DELETE_FLUSH.p0) fun _ _ => ?_
  try simp only [lift, bind_ok]
  refine WP.spec_bind (vspace.decode_frame_batch_loop.cur0 a buf (L.curW s) _ words root asid _ _ _ _ _ _ _ _ 0#u64
    false hw (and255 _)
    (fun s1 a1 w0 w1 w2 d h1 => vspace.frame_batch_entry.cur0 hA Pd G C Vs hE h1 a1 _ ⟨x, hxs, ecn⟩ hdcn
      w0 w1 w2 d (by exact hroot)) (Cur0.ofPreV D)) ?_
  rintro ⟨s1, a1, done1, err, deferred⟩ h1
  try dsimp only
  refine WP.spec_bind (Pₘ := fun _ => True) (by
    split
    · exact hA.invalidate_asid a1 asid
    · exact (WP.spec_ok _).2 trivial) fun a2 _ => ?_
  obtain ⟨-, Ac1, hb1, ec1, -, -, -, nb1, f1⟩ := h1
  have hU1 : UserOK st T Cs Ω H U s1 := D.user.ksb f1.1
  have hG1 : XG st T Cs Ω H Sg Scs Z P3Ok s1 := hE.xg.of_fr f1
  refine WP.spec_bind (Pₘ := fun s2 => ∃ Ac2, BXI st T Cs Ω H Sg Rp Scs Nt Z Ac2 s2 ∧
      ¬ BlockedR (L.mem s2 (stA (L.curW s)))) ?_ ?_
  · split
    · obtain ⟨Q, R, x1⟩ := BXI.xs hb1 hU1
      refine WP.spec_bind (E.buf Ac1 ∅ Q R s1 _ hG1 x1.1 hct) fun bf hbf => ?_
      refine WP.spec_bind (obj.Tcb.set_reg.xs (v := 0#u64) x1 hct (by simp [layout.reg.BADGE, layout.reg.RDI]))
        fun s3 x3 => ?_
      refine WP.spec_bind (msg.set_mr.xs x3 hct hbf (by simp)) ?_
      rintro ⟨n1, s4⟩ ⟨x4, -⟩
      try simp only [uncurry_apply_pair]
      refine WP.spec_bind (msg.set_mr.xs x4 hct hbf (by simp)) ?_
      rintro ⟨len1, s5⟩ ⟨x5, -⟩
      try simp only [uncurry_apply_pair]
      refine WP.spec_bind (P0.msginfo.MessageInfo.new.p0 _ _ _ _) fun mi _ => ?_
      unfold msg.set_msg_info
      refine WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 _) fun w _ => ?_
      refine WP.spec_mono (obj.Tcb.set_reg.xs (v := w) x5 hct (by simp [layout.reg.MSG_INFO, layout.reg.RSI]))
        fun s6 x6 => ⟨_, x6.bxi, ?_⟩
      rw [stA_eq, x6.fr.2.2.2.2.1 _ hct _ (by simp) (by simp) (by simp), ← stA_eq]
      exact nb1
    · exact (WP.spec_ok _).2 ⟨Ac1, hb1, nb1⟩
  rintro s2 ⟨Ac2, hb2, nb2⟩
  refine WP.spec_bind (sched.set_thread_state.running_bxi_nbr hb2 hct nb2) fun s3 h3 => ?_
  exact (WP.spec_ok _).2 (DecPost.ok_bxi h3)
set_option maxHeartbeats 16000000 in
/-- **`vspace.decode`** over the VSpace family's caps. -/
theorem vspace.decode.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s : S} (Pd : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s) (Vs : VsPlace st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (G : DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s) (Pe : EptPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok) (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) 
    {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hE : EntAt st P3Ok s)
    (hx : ∀ sl ∈ extra.val, sl ≠ 0#u64 → CapSlotW T Ω Sg sl)
    (a : A) (lbl len slot : U64) (call : Bool) (buf : U64) (hslot : CapSlotW T Ω Sg slot) (hvi : VaOK cap) :
    vspace.decode st ar s a lbl len slot cap call buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hb := D.bxi
  unfold vspace.decode
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e
  cases cap
  all_goals try (simp only [error.invalid_cap, bind_ok]; exact (WP.spec_ok _).2 (D.err _))
  case Frame fp fsz fr fd fm fe fa fv =>
    exact vspace.decode_frame.dec hA Pd Vs Pe C E fp fsz fr fd fm fe fa fv D hE a lbl len slot call buf hslot hvi
  case PageTable => exact vspace.decode_table.dec hA Pd Vs D hE a lbl len slot buf hslot hvi
  case PageDirectory => exact vspace.decode_table.dec hA Pd Vs D hE a lbl len slot buf hslot hvi
  case Pdpt => exact vspace.decode_table.dec hA Pd Vs D hE a lbl len slot buf hslot hvi
  case Pml4 ptr mapped asid =>
    try dsimp only
    split
    swap
    · split
      · exact vspace.decode_frame_batch.dec hA Pd G Vs C E D hE hx a len ptr mapped asid call buf
      · errV
    split
    swap
    · errV
    -- #39: the ASID must still name the PML4
    refine WP.spec_bind (P0.vspace.find_vspace_for_asid.p0 st s asid hS) fun r _ => ?_
    rcases r with r1 | lf
    swap
    · errV
    try dsimp only
    split
    · errV
    refine WP.spec_bind (Cur0.restart D) fun s1 h1 => ?_
    refine WP.spec_bind (hA.invalidate_asid a asid) fun a1 _ => ?_
    exact (WP.spec_ok _).2 h1.post
  case AsidControl =>
    try dsimp only
    split
    · errV
    refine WP.spec_bind (vspace.extra.mem extra 0#usize) fun o ho => ?_
    refine WP.spec_bind (vspace.extra.mem extra 1#usize) fun o1 ho1 => ?_
    rcases o with _ | x
    · errV
    obtain ⟨hxm, hx0⟩ := ho x rfl
    try dsimp only
    rcases o1 with _ | y
    · errV
    try dsimp only
    split
    swap
    · errV
    refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun idx _ => ?_
    refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun dep _ => ?_
    refine WP.spec_bind (WP.spec_and (P0.obj.Slot.cap.p0 st x s hS) (Vs.pool _ _ _ _ hE D x hxm hx0)) fun ut ⟨_, hut⟩ => ?_
    refine WP.spec_bind (P0.obj.Slot.cap.p0 st y s hS) fun root _ => ?_
    refine WP.spec_bind (P0.vspace.decode_loop0.p0 st s 0#u64 hS) fun i _ => ?_
    split
    · errV
    refine WP.spec_bind (Pₘ := fun _ => True) (by p0_auto) fun base _ => ?_
    cases ut
    all_goals try (simp only [error.invalid_cap, bind_ok]; exact (WP.spec_ok _).2 (D.err _))
    case Untyped uptr usb ufi udev =>
      have hz := hut _ _ _ _ rfl
      try dsimp only
      split
      · errV
      split
      swap
      · errV
      refine WP.spec_bind (P0.cdt.ensure_no_children.p0 st s x hS) fun r _ => ?_
      rcases r with _ | e
      swap
      · errV
      simp only [irq_branch_ok, bind_ok]
      refine WP.spec_bind (C.tgt Ac s root idx dep hE hb) fun r1 hr1 => ?_
      rcases r1 with v | e
      swap
      · errV
      have hv := hr1 v rfl
      simp only [irq_branch_ok, bind_ok]
      refine WP.spec_bind (P0.cdt.ensure_empty_slot.p0 st s v hS) fun r2 _ => ?_
      rcases r2 with _ | e
      swap
      · errV
      simp only [irq_branch_ok, bind_ok]
      refine WP.spec_bind (Cur0.restart D) fun s1 h1 => ?_
      try simp only [lift, bind_ok]
      refine WP.spec_bind (shl_and63 _) fun i2 _ => ?_
      have hxs := hx x hxm hx0
      refine WP.spec_bind (obj.Slot.set_cap.capw (s := s1) hxs) fun s2 w2 => ?_
      have h2 := h1.capw w2 fun _ hb => hb
      refine WP.spec_bind (LawfulStore.clear_free_spec s2 _ 4096#u64) fun s3 e3 => ?_
      subst e3
      have h3 := Cur0.zr h2 hz
      obtain ⟨Ac3, hb3⟩ := h3.bxi
      refine WP.spec_bind (Pₘ := fun s4 => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s s4) ?_ fun s4 h4 => ?_
      · unfold cdt.insert
        refine WP.spec_bind (P0.obj.Slot.cap.p0 st x _ hS) fun c0 _ => ?_
        exact WP.spec_mono (C.ins Ac3 s _ _ c0 x v hE h3.fr hb3 (SlotW.capw0 hxs) hv) fun s5 w => h3.capw w fun _ hb => hb
      obtain ⟨Ac4, hb4⟩ := h4.bxi
      refine WP.spec_bind (Vs.aset Ac4 s s4 i _ hE h4.fr hb4) fun s5 w5 => ?_
      exact (WP.spec_ok _).2 (h4.capw w5 fun b hb => Or.inr hb).post
  case AsidPool pptr abase =>
    try dsimp only
    split
    · errV
    refine WP.spec_bind (vspace.extra.mem extra 0#usize) fun o ho => ?_
    rcases o with _ | x
    · errV
    obtain ⟨hxm, hx0⟩ := ho x rfl
    have hxs := hx x hxm hx0
    try dsimp only
    refine WP.spec_bind (P0.obj.Slot.cap.p0 st x s hS) fun c _ => ?_
    cases c
    all_goals try (simp only [error.invalid_cap, bind_ok]; exact (WP.spec_ok _).2 (D.err _))
    case Pml4 ptr1 b1 _ =>
      try dsimp only
      split
      · errV
      refine WP.spec_bind (Pₘ := fun _ => True) (by p0_auto) fun i _ => ?_
      obtain ⟨pool, epool, -⟩ := spec_exists' (P0.vspace.asid_table.p0 st s i hS)
      have hpool : ∀ asid, pool ≠ 0#u64 →
          V (core.num.U64.wrapping_add pool (core.num.U64.wrapping_mul (asid &&& 511#u64) 8#u64)) := by
        intro asid
        have := Pd.pool Ac s asid i (WritesIn.refl _ _) hb
        rw [epool] at this
        exact (WP.spec_ok _).1 this
      rw [epool]
      simp only [bind_ok]
      split
      · errV
      rename_i hp0
      split
      · errV
      refine WP.spec_bind (P0.vspace.decode_loop1.p0 st s abase pool 0#u64 hS) fun i1 _ => ?_
      split
      · errV
      try simp only [lift, bind_ok]
      refine WP.spec_bind (Cur0.restart D) fun s1 h1 => ?_
      refine WP.spec_bind (obj.Slot.set_cap.capw (s := s1) hxs) fun s2 w2 => ?_
      have h2 := h1.capw w2 fun _ hb => hb
      step as ⟨i3, hi3⟩
      try simp only [lift, bind_ok]
      refine WP.spec_bind (LawfulStore.write_spec s2 _ ptr1) fun s3 e3 => ?_
      subst e3
      rw [mask511_mul8 _ i3 hi3]
      exact (WP.spec_ok _).2 (h2.vs Pd.vs (writesIn_wr_V (v := ptr1) Pd.vs (hpool _ hp0))).post
    case Ept ptr1 i b1 _ _ =>
      try dsimp only
      split
      · try dsimp only
        split
        · errV
        try simp only [lift, bind_ok]
        refine WP.spec_bind (Pₘ := fun _ => True) (by p0_auto) fun i1 _ => ?_
        obtain ⟨pool, epool, -⟩ := spec_exists' (P0.vspace.asid_table.p0 st s i1 hS)
        have hpool : ∀ asid, pool ≠ 0#u64 →
            V (core.num.U64.wrapping_add pool (core.num.U64.wrapping_mul (asid &&& 511#u64) 8#u64)) := by
          intro asid
          have := Pd.pool Ac s asid i1 (WritesIn.refl _ _) hb
          rw [epool] at this
          exact (WP.spec_ok _).1 this
        rw [epool]
        simp only [bind_ok]
        split
        · errV
        rename_i hp0
        split
        · errV
        refine WP.spec_bind (P0.vspace.decode_loop2.p0 st s abase pool 0#u64 hS) fun i2 _ => ?_
        split
        · errV
        try simp only [lift, bind_ok]
        refine WP.spec_bind (Cur0.restart D) fun s1 h1 => ?_
        try simp only [lift, bind_ok]
        refine WP.spec_bind (obj.Slot.set_cap.capw (s := s1) hxs) fun s2 w2 => ?_
        have h2 := h1.capw w2 fun _ hb => hb
        step as ⟨i6, hi6⟩
        try simp only [lift, bind_ok]
        refine WP.spec_bind (LawfulStore.write_spec s2 _ _) fun s3 e3 => ?_
        subst e3
        rw [mask511_mul8 _ i6 hi6]
        exact (WP.spec_ok _).2 (h2.vs Pd.vs (writesIn_wr_V Pd.vs (hpool _ hp0))).post
      · errV

/-- **InvGaps' `vspace`, discharged** from the deletion and CSpace
placement facts, the transfer's (a reply's buffer), `IrqPlace.extra` (the
extra caps' slots) and `VsPlace`. -/
theorem decGap_vspace {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    (Pd : DelPlace st T Cs Ω H Sg Rp Scs Nt Z V P3Ok) (Vs : VsPlace st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (Pe : EptPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok) (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (Pl : IrqPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (DG : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    (Iv : InvVa st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) :
    DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .vspace := by
  intro Ac s a lbl len slot cap blk call don fp buf extra hf D hslot hE
  cases cap <;> simp [capFam] at hf
  all_goals
    unfold syscall.decode_invocation
    step with sched.cur_thread.spec as ⟨ct, _⟩
    try dsimp only
    exact vspace.decode.dec hA (Pd s hE) Vs (DG s hE) Pe C E D hE (Pl.extra _ _ _ _ hE D) a lbl len slot call buf hslot
      (Iv _ _ _ _ hE D)


end X5

end

end Fl4Proofs.P1
