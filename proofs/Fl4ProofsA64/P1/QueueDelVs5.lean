/-
P1 (aarch64): **the deletion chain with root-restricted VSpace walks** (namespace `W7.R.A5`), replacing the
VSpace fields of `DelPlaceAt` that are false as stated.

`DelPlaceAt.ptw` / `.elw` / `.ptslot` (QueueDelFin), `W7.DelPlaceAt.*` (QueueSlots7) and `W7.R.DelPlaceAt.*`
(QueueDelRv) quantify over **every** walk start (`∀ table shift level`, `∀ table shift mask rem`, `∀ root`).
`lookup_pt_slot st s root v` returns `entry_addr root v 39` unchanged when that word is no table descriptor, and
`unmap_page_table_loop` / `ept.unmap_table_loop` return a slot of the start table whenever its word is a table
descriptor naming `pt`; with the start a TCB (whose register words are user-chosen) the returned slot is a TCB
word, but `VsOK` puts `V` inside `Ω`, which has no TCB word (QueueHeap `Heap.omega`). So these fields fail at
every reachable state with a TCB (gen 22, verified by the reviewer). They are not changed here; this module
gives new forms and re-proves the deletion chain on them.

New premises (each a field of a new structure; see their docstrings):
* **[J] `VsDelAt`** (the walks of the deletion's unmaps, from roots the ASID table names):
  - `ptw`: the walk `unmap_page_table` starts from the root `find_asid_raw asid` returned (not a Stage-2 root;
    `ptWalkStart`: a TTBR0 root at level 0, a high VSpace at level 1 in the table its L0[511] names) finds only
    VSpace words;
  - `elw`: the Stage-2 walk from the root `ept::find asid` returned, at the arch's IPA size, finds only VSpace
    words;
  - `ptslot`: `lookup_pt_slot` from the root `unmap_root asid` returned, at a user or window address (`HiOK`),
    gives a VSpace word.
  Source (crates/fl4-core/src/arch/aarch64): roots are read from the ASID pool (`find_asid_raw` vspace.rs:229–242,
  `unmap_root` 420–433, `ept::find` ept.rs:143–150); the pool entries are written only by ASIDPoolAssign with a
  VSpace / Stage-2 / HighVSpace cap's object (vspace.rs:1230–1268); the walks follow only table descriptors,
  written only by `decode_page_table`'s Map / `map_high_page_table` / `ept::map_table` with a PageTable cap's
  object (vspace.rs:1091–1166, ept.rs:174–199); a HighVSpace's L0[0..511) copy the kernel TTBR1 L0, which uses only
  L0[256..510] (layout.rs:1–4), so a high walk at an address `< 2^47` stops at a zero L0 entry and one in the
  window goes through L0[511], the HighVSpace's own level-1 table (vspace.rs:283–299); `unmap_page_table`'s
  high walk starts at that level-1 table (vspace.rs:483–492). These are the restrictions of the false fields to
  the roots the code actually walks from, as `VsPlaceA.s1` / `.hi` / `.s2` / `.fr` (QueueDecVs).
* **[J] `DelPlaceAt.frm`** (new field): a mapped Stage-1 frame cap with an ASID in a cap slot has a user or window
  address (`FrMapOK`). Needed because a high VSpace's walk at a kernel-window address enters the kernel's TTBR1
  tables (not in `Ω`), where `unmap_page` could clear a kernel block mapping: without it `fin_vs` (and so
  `DelGapsAt.fin` for every `DelCapOK` cap) is not provable from true placements. Source: the mapped frame caps
  are made by `decode_page_map` (`last ≤ USER_TOP`, vspace.rs:771–782), `decode_high_page_map` (window,
  806–816), the boot image frames (user addresses, boot.rs:206–217), and copies of an existing frame cap's
  fields (vspace.rs:1463, 1688); every other constructor has `mapped: false, asid: 0`.

So the deletion's finalisation takes `FrMapOK c` (`R.FinGapAt … FrMapOK`, `A5.DelGapsAt.fin`), read with the cap
from its slot (`A5.DelGapsAt.frm` / `A5.DelPlaceAt.frm`). `A5.DelPlaceAt` is `W7.R.DelPlaceAt` without `ptw` /
`elw` / `ptslot` and with `frm`; its other fields (`vs`, [P] `cap` / `next` / `prev` / `pool` / `aset` / `rcw` /
`irq`) are unchanged in statement.

Proved (QueueVsFin's consumers on the new forms): `vspace.unmap_page_table.vsA`, `ept.unmap_table.vsA`,
`vspace.unmap_page.vsA` (hypotheses root-restricted, as Hoare triples of the root lookups), `A5.fin_vs`, and the
deletion chain over `A5.DelGapsAt` / `A5.DelPlaceAt` (QueueDelRv / QueueFinRv / QueueFinRvSt text by script,
`handoff/a64-wip/gen23/gen_delvs5.py`): `cdt.finalise_slot_immediate.cur0` … `decGap_cnode2`, the slot writes,
`finalise_slot_deferred`, `delete_deferred`, `finGap_thread0`, `finGap_irq0`, `finRv_irq`, `finRvAt_of`,
`finRv_thread`, `finRvRest_of3`, `fin_all`, `delGaps_of`, `delGaps_of_gaps4`, **`decGap_cnode_rv4`**.

Caveat (unchanged in kind, as every existing `DelPlaceAt` field): the placements are stated at every `Fr0 ∧ BXI`
state of the deletion, and `Fr0` allows any `Cur0W` (cap-slot, VSpace) word to change, so read literally at an
arbitrary such state they are not implied by reachability; they are meant along the deletion's own states.
-/
import Fl4ProofsA64.P1.QueueDecVs
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}

/-! ## QueueVsFin's unmaps from root-restricted walks -/

/-- The start of `unmap_page_table`'s TTBR0 / TTBR1 walk from the ASID table's tagged root `r1`
(vspace.rs:483–492): a high VSpace (`ROOT_HIGH`) starts at level 1 in the table its L0[`HIGH_L0_INDEX`] names,
any other (TTBR0) root at level 0. -/
def ptWalkStart (st : machine.Store S) (s : S) (r1 : U64) : Result (U64 × U64 × U64) :=
  if (r1 &&& vspace.ROOT_TAG) = vspace.ROOT_HIGH then do
    let i1 ← vspace.HIGH_L0_INDEX * 8#u64
    let i3 ← st.read s (core.num.U64.wrapping_add (r1 &&& ~~~ vspace.ROOT_TAG) i1)
    let i4 ← vspace.table_of i3
    ok (i4, 30#u64, 1#u64)
  else ok (r1 &&& ~~~ vspace.ROOT_TAG, vspace.TOP_LEVEL_SHIFT, 0#u64)

/-- **The Stage-2 `unmap_table`** writes only the slot its walk finds, the walk starting at the root `ept::find`
returned, with the arch's geometry (`hel`; QueueVsFin `ept.unmap_table.vs` with the start restricted). -/
theorem ept.unmap_table.vsA {A : Type _} {ar : machine.Arch A} (s : S) (a : A)
    (asid ipa pt : U64) {V : U64 → Prop} (hV : VsOK Ω Sg V)
    (hel : ept.find st s asid ⦃ r => ∀ r1, r = .Ok r1 → ar.s2_ipa_bits a ⦃ ib => ept.geom ib ⦃ g =>
      ept.unmap_table_loop st s ipa pt r1 g.top_shift g.top_mask (core.num.U64.wrapping_sub g.levels 1#u64) ⦃ f =>
        ∀ x, f = some x → V x ⦄ ⦄ ⦄ ⦄) (hA : P0.ArchTotal ar) :
    ept.unmap_table st ar s a asid ipa pt ⦃ r => WritesIn st s r.1 V ⦄ := by
  unfold ept.unmap_table
  refine WP.spec_bind hel fun r hr => ?_
  rcases r with r1 | e
  · refine WP.spec_bind (hr r1 rfl) fun ib hib => ?_
    refine WP.spec_bind hib fun g hg => ?_
    simp only [lift, bind_ok]
    refine WP.spec_bind hg fun f hf => ?_
    rcases f with _ | slot
    · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
    · have hx := hf slot rfl
      step with LawfulStore.write_spec as ⟨s1, e1⟩
      refine WP.spec_bind (hA.invalidate_stage2_vmid a asid) fun a1 _ => ?_
      rw [WP.spec_ok, e1]; exact writesIn_wr_V hV hx
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)

/-- **`unmap_page_table`** writes only the slot its walk finds, the walk starting at the root the ASID table
names (`hlk`, through `ptWalkStart`; Stage-2 roots by `hel`). QueueVsFin `unmap_page_table.vs` with the walk
start restricted. -/
theorem vspace.unmap_page_table.vsA {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (asid vaddr pt : U64) {V : U64 → Prop} (hV : VsOK Ω Sg V)
    (hlk : vspace.find_asid_raw st s asid ⦃ r => ∀ r1, r = .Ok r1 → (r1 &&& vspace.ROOT_TAG) ≠ vspace.ROOT_S2 →
      ptWalkStart st s r1 ⦃ x => vspace.unmap_page_table_loop st s vaddr pt x.1 x.2.1 x.2.2 ⦃ f =>
        ∀ y, f = some y → V y ⦄ ⦄ ⦄)
    (hel : ept.find st s asid ⦃ r => ∀ r1, r = .Ok r1 → ar.s2_ipa_bits a ⦃ ib => ept.geom ib ⦃ g =>
      ept.unmap_table_loop st s vaddr pt r1 g.top_shift g.top_mask (core.num.U64.wrapping_sub g.levels 1#u64) ⦃ f =>
        ∀ x, f = some x → V x ⦄ ⦄ ⦄ ⦄) :
    vspace.unmap_page_table st ar s a asid vaddr pt ⦃ r => WritesIn st s r.1 V ⦄ := by
  unfold vspace.unmap_page_table
  refine WP.spec_bind hlk fun r hr => ?_
  rcases r with r1 | e
  · simp only [lift, bind_ok]
    by_cases h2 : (r1 &&& vspace.ROOT_TAG) = vspace.ROOT_S2
    · rw [if_pos h2]; exact ept.unmap_table.vsA s a asid vaddr pt hV hel hA
    rw [if_neg h2]
    have hst := hr r1 rfl h2
    simp only [ptWalkStart] at hst
    refine WP.spec_bind hst fun x hx => ?_
    obtain ⟨table, shift, level⟩ := x
    try dsimp only at hx ⊢
    refine WP.spec_bind hx fun f hf => ?_
    rcases f with _ | slot
    · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
    · have hx := hf slot rfl
      try dsimp only
      step with LawfulStore.write_spec as ⟨s1, e1⟩
      split
      · refine WP.spec_bind (hA.invalidate_high_vspace a _) fun a1 _ => ?_
        rw [WP.spec_ok, e1]; exact writesIn_wr_V hV hx
      · refine WP.spec_bind (hA.invalidate_asid a asid) fun a1 _ => ?_
        rw [WP.spec_ok, e1]; exact writesIn_wr_V hV hx
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)

/-- **`unmap_page`** writes only the slot `lookup_pt_slot` finds from the root `unmap_root` returned (`hpt`;
QueueVsFin `unmap_page.vs` with the root restricted). -/
theorem vspace.unmap_page.vsA {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (size : capability.FrameSize) (asid vaddr pptr : U64) {V : U64 → Prop} (hV : VsOK Ω Sg V)
    (hpt : vspace.unmap_root st s asid ⦃ o => ∀ root high, o = some (root, high) →
      vspace.lookup_pt_slot st s root vaddr ⦃ lu => V lu.slot ⦄ ⦄) :
    vspace.unmap_page st ar s a size asid vaddr pptr ⦃ r => WritesIn st s r.1 V ⦄ := by
  unfold vspace.unmap_page
  refine WP.spec_bind hpt fun o ho => ?_
  rcases o with _ | ⟨root, high⟩
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  try dsimp only
  refine WP.spec_bind (ho root high rfl) fun lu hlu => ?_
  refine WP.spec_bind (P0.vspace.page_shift.p0 size) fun sh _ => ?_
  split
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  step with LawfulStore.read_spec as ⟨e, _⟩
  refine WP.spec_bind (P0.vspace.is_page.p0 e lu.shift) fun b _ => ?_
  split
  · refine WP.spec_bind (P0.vspace.page_base.p0 e lu.shift) fun pb _ => ?_
    refine WP.spec_bind (P0.layout.paddr.p0 pptr) fun pa _ => ?_
    split
    · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
    step with LawfulStore.write_spec as ⟨s1, e1⟩
    split
    · refine WP.spec_bind (hA.invalidate_high_page a vaddr) fun a1 _ => ?_
      rw [WP.spec_ok, e1]; exact writesIn_wr_V hV hlu
    · refine WP.spec_bind (hA.invalidate_page a asid vaddr) fun a1 _ => ?_
      rw [WP.spec_ok, e1]; exact writesIn_wr_V hV hlu
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)

/-- A mapped Stage-1 frame cap with an ASID names a user or window address (`HiOK`). -/
def FrMapOK (c : capability.Cap) : Prop :=
  ∀ p sz r d asid v, c = .Frame p sz r d true false asid v → asid ≠ 0#u64 → HiOK v

theorem FrMapOK.null : FrMapOK .Null := fun _ _ _ _ _ _ h => nomatch h

namespace W7
namespace R
namespace A5

/-- **`R.DelGapsAt` with the frame-address fact** (`frm`, read with the cap from its slot) and the finalisation
of caps that satisfy it (`fin`); otherwise `W7.R.DelGapsAt`'s fields. -/
structure DelGapsAt (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (s0 : S) : Prop where
  cap : ∀ (Ac : Set U64) (s : S) (x : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    SlotW T Ω Sg x → obj.Slot.cap st x s ⦃ c => DelCapOK T Ω Sg H Rp Nt c ∧ FinPl st Scs s c ⦄
  frm : ∀ (Ac : Set U64) (s : S) (x : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    SlotW T Ω Sg x → obj.Slot.cap st x s ⦃ c => FrMapOK c ⦄
  fin : ∀ (Ac : Set U64) (s : S) (a : A) (c : capability.Cap) (fin : Bool),
    Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s → DelCapOK T Ω Sg H Rp Nt c → FinPl st Scs s c → FrMapOK c →
    objects.finalise_cap st ar s a c fin false ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧
      DelCapOK T Ω Sg H Rp Nt r.1.1 ∧ DelCapOK T Ω Sg H Rp Nt r.1.2 ⦄
  deferred : ∀ (Ac : Set U64) (s : S) (a : A) (x : U64), Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s →
    SlotW T Ω Sg x → cdt.delete_deferred st ar s a x ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄
  empty : ∀ (Ac : Set U64) (s : S) (a : A) (x : U64) (c : capability.Cap),
    Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s → SlotW T Ω Sg x → DelCapOK T Ω Sg H Rp Nt c →
    cdt.empty_slot st ar s a x c ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ⦄
  next : ∀ (Ac : Set U64) (s : S) (x : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    SlotW T Ω Sg x → obj.Slot.next st x s ⦃ n => n = 0#u64 ∨ SlotW T Ω Sg n ⦄

/-- The deletion gaps at every decode start reached from a `P3Ok` entry. -/
def DelGaps (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (P3Ok : S → Prop) : Prop :=
  ∀ s0, EntAt st P3Ok s0 → DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0

set_option hygiene false in
/-- The preemption-point tail of a loop round (`Cur0` at `s2`). -/
local macro "pptail" : tactic => `(tactic| (
  refine WP.spec_bind (sched.preemption_point.cur0 hA h2) ?_
  rintro ⟨rr, s3, a3⟩ h3
  try simp only [WP.uncurry'_pair] at h3 ⊢
  try simp only [uncurry_apply_pair] at h3 ⊢
  rcases rr with _ | ee
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok]
    refine (WP.spec_ok _).2 ⟨h3, ?_⟩
    show fuel1.val < fuel.val
    omega
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    first | exact (WP.spec_ok _).2 h3 | exact h3 | exact (WP.spec_ok _).2 ⟨h3, by intro v hv; simp_all⟩ |
      exact ⟨h3, by intro v hv; simp_all⟩))

set_option maxHeartbeats 4000000 in
theorem cdt.finalise_slot_immediate.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {s0 s : S} (G : DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) {a : A} {x : U64}
    (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : SlotW T Ω Sg x) :
    cdt.finalise_slot_immediate st ar s a x ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧
      ∀ v, r.1 = .Ok v → DelCapOK T Ω Sg H Rp Nt v.cleanup ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.finalise_slot_immediate cdt.finalise_slot_immediate_loop
  apply loop.spec_decr_nat (measure := fun y => y.2.2.val)
    (inv := fun y => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 y.1)
  · rintro ⟨s1, a1, fuel⟩ h1
    simp only at h1
    dsimp only
    unfold cdt.finalise_slot_immediate_loop.body
    split
    swap
    · exact (WP.spec_ok _).2 ⟨h1, by intro v hv; simp_all⟩
    rename_i hf
    step as ⟨fuel1, hf1⟩
    obtain ⟨Acx, hbx⟩ := h1.bxi
    refine WP.spec_bind (WP.spec_and (G.cap Acx s1 x h1.fr hbx hx) (G.frm Acx s1 x h1.fr hbx hx))
      fun c ⟨⟨hc, hpl⟩, hfr⟩ => ?_
    refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h1, fun v hv => by cases hv; exact DelCapOK.null⟩
    refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s1 x c hS) fun fin _ => ?_
    refine WP.spec_bind (G.fin Ac s1 a1 c fin h1 hc hpl hfr) ?_
    rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨h2', hrem, hcl⟩
    try simp only [uncurry_apply_pair, WP.uncurry'_pair]
    refine WP.spec_bind (cdt.cap_removable.zombie rem x) fun br hbr => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h2', fun v hv => by cases hv; exact hcl⟩
    rename_i hbr0
    have hbr' := hbr (by simpa using hbr0)
    refine WP.spec_bind (obj.Slot.set_cap.capw (c := rem) (s := s2) hx) fun s2' w2 => ?_
    have h2 := h2'.capw7 w2 fun _ hb => hb
    have hf' : 0 < fuel.val := by simpa using hf
    split
    all_goals try pptail
    -- the zombie: the deferred delete of its last slot, then the count
    simp only [lift, bind_ok]
    rename_i zp zt zn
    have hen := zombie_last hrem (hbr' zp zt zn rfl)
    unfold obj.Slot.index
    simp only [lift, bind_ok, cte_size]
    refine WP.spec_bind (G.deferred Ac s2' a2 _ h2 hen) ?_
    rintro ⟨r, s3, a3⟩ h3
    try simp only [uncurry_apply_pair] at h3 ⊢
    rcases r with _ | e
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      refine WP.spec_bind (P0.obj.Slot.cap.p0 st x s3 hS) fun c _ => ?_
      have SC : ∀ c', obj.Slot.set_cap st x s3 c' ⦃ s' => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := fun c' =>
        WP.spec_mono (obj.Slot.set_cap.capw hx) fun s' w => h3.capw7 w fun _ hb => hb
      refine WP.spec_bind (Pₘ := fun r : S × A => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1) ?_ ?_
      · split
        all_goals try exact (WP.spec_ok _).2 h3
        split
        · split
          · refine WP.spec_bind (Pₘ := fun s' => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s') ?_
              fun s' h' => (WP.spec_ok _).2 h'
            split
            · try simp only [lift, bind_ok]
              exact SC _
            · exact (WP.spec_ok _).2 h3
          · exact (WP.spec_ok _).2 h3
        · exact (WP.spec_ok _).2 h3
      · rintro ⟨s4, a4⟩ h2
        try simp only [uncurry_apply_pair] at h2 ⊢
        pptail
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      exact (WP.spec_ok _).2 ⟨h3, by intro v hv; simp_all⟩
  · exact h

/-- `cdt.delete` (exposed) of a cap slot. -/
theorem cdt.delete.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {s0 s : S} (G : DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) {a : A} {x : U64}
    (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : SlotW T Ω Sg x) :
    cdt.delete st ar s a x true ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄ := by
  unfold cdt.delete
  simp only [↓reduceIte]
  refine WP.spec_bind (cdt.finalise_slot_immediate.cur0 hA G h hx) ?_
  rintro ⟨r, s1, a1⟩ ⟨h1, hv1⟩
  try simp only [uncurry_apply_pair] at h1 hv1 ⊢
  rcases r with v | e
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    refine WP.spec_bind (G.empty Ac s1 a1 x _ h1 hx (hv1 v rfl)) ?_
    rintro ⟨s2, a2⟩ h2
    try simp only [uncurry_apply_pair] at h2 ⊢
    exact (WP.spec_ok _).2 h2
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 h1

set_option maxHeartbeats 2000000 in
/-- `cdt.revoke` of a cap slot. -/
theorem cdt.revoke.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {s0 s : S} (G : DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) {a : A} {x : U64}
    (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : SlotW T Ω Sg x) :
    cdt.revoke st ar s a x ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.revoke cdt.revoke_loop
  apply loop.spec_decr_nat (measure := fun y => y.2.2.val)
    (inv := fun y => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 y.1)
  · rintro ⟨s1, a1, fuel⟩ h1
    simp only at h1
    dsimp only
    unfold cdt.revoke_loop.body
    split
    swap
    · exact (WP.spec_ok _).2 h1
    rename_i hf
    have hf' : 0 < fuel.val := by simpa using hf
    step as ⟨fuel1, hf1⟩
    have h1' := h1
    obtain ⟨-, Acx, hbx, -, -, -, -, -⟩ := h1'.1
    refine WP.spec_bind (G.next Acx s1 x h1.fr hbx hx) fun nx hnx => ?_
    simp only [obj.Slot.is_null, bind_ok]
    split
    · exact (WP.spec_ok _).2 h1
    rename_i hn0
    have hnW : SlotW T Ω Sg nx := hnx.resolve_left (by simpa using hn0)
    refine WP.spec_bind (P0.cdt.is_mdb_parent_of.p0 st s1 x nx hS) fun bp _ => ?_
    split
    · refine WP.spec_bind (cdt.delete.cur0 hA G h1 hnW) ?_
      rintro ⟨r, s2', a2⟩ h2
      try simp only [uncurry_apply_pair] at h2 ⊢
      rcases r with _ | e
      · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        refine WP.spec_bind (sched.preemption_point.cur0 hA h2) ?_
        rintro ⟨rr, s3, a3⟩ h3
        try simp only [uncurry_apply_pair] at h3 ⊢
        rcases rr with _ | ee
        · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok]
          refine (WP.spec_ok _).2 ⟨h3, ?_⟩
          show fuel1.val < fuel.val
          omega
        · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
            bind_tc_ok]
          exact (WP.spec_ok _).2 h3
      · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
          bind_tc_ok]
        exact (WP.spec_ok _).2 h2
    · exact (WP.spec_ok _).2 h1
  · exact h

/-- **CNode `Delete`** from `DelGaps`. -/
theorem cnode_del {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {s : S} (G : DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s) {a : A} {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {x : U64}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hx : SlotW T Ω Sg x) :
    (do
      let s1 ← sched.set_thread_state st s (L.curW s) sched.TS_RESTART
      cdt.delete st ar s1 a x true) ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ :=
  WP.spec_bind (Cur0R.restart D) fun s1 h1 => WP.spec_mono (cdt.delete.cur0 hA G h1 hx) fun r hr => by
    obtain ⟨r', s', a'⟩ := r; exact hr.post

/-- **CNode `Revoke`** from `DelGaps`. -/
theorem cnode_rev {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {s : S} (G : DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s) {a : A} {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {x : U64}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hx : SlotW T Ω Sg x) :
    (do
      let s1 ← sched.set_thread_state st s (L.curW s) sched.TS_RESTART
      cdt.revoke st ar s1 a x) ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ :=
  WP.spec_bind (Cur0R.restart D) fun s1 h1 => WP.spec_mono (cdt.revoke.cur0 hA G h1 hx) fun r hr => by
    obtain ⟨r', s', a'⟩ := r; exact hr.post

set_option hygiene false in
local macro "errleaf2" : tactic => `(tactic| first
  | exact D.err _
  | exact (WP.spec_ok _).2 (D.err _)
  | (simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, error.illegal, error.truncated, cnode.missing_source]
     first | exact D.err _ | exact (WP.spec_ok _).2 (D.err _)))

set_option maxHeartbeats 4000000 in
/-- **`cnode.decode`**, Delete and Revoke included. -/
theorem cnode.decode.dec2 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (C : CdtHyps2 st T Cs Ω H Sg Rp Scs Nt Z P3Ok) {s : S} (G : DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s)
    {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) (lbl len buf : U64)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hE : EntAt st P3Ok s) (c : capability.Cap) :
    cnode.decode st ar s a lbl len c buf extra ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cnode.decode
  simp only [error.illegal, error.truncated, bind_ok]
  split
  · errleaf2
  split
  · errleaf2
  split
  · errleaf2
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun idx _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun dep _ => ?_
  refine WP.spec_bind (WP.spec_and (C.tgt Ac s c idx dep hE D.bxi) (C.tgtW Ac s c idx dep hE D.bxi)) fun r hr => ?_
  rcases r with v | e
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    errleaf2
  have hv := hr.1 v rfl
  have hvW := slotW_to7 (hr.2 v rfl)
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  repeat' (first
    | exact (WP.spec_ok _).2 (D.err _)
    | exact lift2 (cnode.decode_copy.dec C.toCdtHyps lbl len buf v D hE hv)
    | exact lift2 (cnode.decode_cancel_badged_sends.dec C.toCdtHyps v D hE hv)
    | exact lift2 (cnode.decode_rotate.dec C.toCdtHyps len buf v D hE hv)
    | exact cnode_del hA G D hvW
    | exact cnode_rev hA G D hvW
    | split)

/-- **InvGaps' `cnode`, discharged** from `CdtHyps2` and `DelGaps`. -/
theorem decGap_cnode2 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (C : CdtHyps2 st T Cs Ω H Sg Rp Scs Nt Z P3Ok) (G : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) :
    DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .cnode := by
  intro Ac s a lbl len slot cap blk call don fp buf extra hf D _hslot hE
  cases cap <;> simp [capFam] at hf
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec as ⟨ct, _⟩
  try dsimp only
  split
  · exact (WP.spec_ok _).2 (DecPost.keep D.bxi (by simp))
  · exact cnode.decode.dec2 hA C (G s hE) a lbl len buf D hE _



/-! ## The placements: `W7.R.DelPlaceAt` without the walk fields, with `frm`; the walks root-restricted -/

/-- **The deletion placement facts** (P3's): `W7.R.DelPlaceAt`'s fields without `ptw` / `elw` / `ptslot` (false
as stated: every walk start) and with **[J] `frm`**. -/
structure DelPlaceAt (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (V : U64 → Prop) (s0 : S) : Prop where
  vs : VsOK Ω Sg V
  cap : ∀ (Ac : Set U64) (s : S) (x : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → SlotW T Ω Sg x →
    obj.Slot.cap st x s ⦃ c => DelCapOK T Ω Sg H Rp Nt c ∧ FinPl st Scs s c ⦄
  /-- **[J] (a64) `frm`**: a mapped Stage-1 frame cap with an ASID in a cap slot has a user or window address
  (`FrMapOK`): the map decodes check it (vspace.rs:771, 806), boot maps the image at user addresses, every other
  frame cap constructor is unmapped with ASID 0. -/
  frm : ∀ (Ac : Set U64) (s : S) (x : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    SlotW T Ω Sg x → obj.Slot.cap st x s ⦃ c => FrMapOK c ⦄
  next : ∀ (Ac : Set U64) (s : S) (x : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → SlotW T Ω Sg x →
    obj.Slot.next st x s ⦃ n => n = 0#u64 ∨ SlotW T Ω Sg n ⦄
  prev : ∀ (Ac : Set U64) (s : S) (x : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → SlotW T Ω Sg x →
    obj.Slot.prev st x s ⦃ n => n = 0#u64 ∨ SlotW T Ω Sg n ⦄
  pool : ∀ (Ac : Set U64) (s : S) (asid i : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    vspace.asid_table st s i ⦃ pool => pool ≠ 0#u64 →
      V (core.num.U64.wrapping_add pool (core.num.U64.wrapping_mul (asid &&& 511#u64) 8#u64)) ⦄
  aset : ∀ (Ac : Set U64) (s : S) (hi : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    vspace.set_asid_table st s hi 0#u64 ⦃ s1 => WritesIn st s s1 V ⦄
  /-- [P] (as `W7.R.DelPlaceAt.rcw`) a thread's run VCPU's `RUN_CALLER` word is a user word. -/
  rcw : ∀ (Ac : Set U64) (s : S) (p : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    p ∈ T → L.mem s (runVcpuA p) ≠ 0#u64 →
    UserW st T Cs Ω H s (core.num.U64.wrapping_add (L.mem s (runVcpuA p)) vcpu.RUN_CALLER)
  /-- [P] (as `W7.R.DelPlaceAt.irq`) an IRQ's handler slot holds no cap or a notification cap. -/
  irq : ∀ (Ac : Set U64) (s : S) (i : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → i.val < 128 →
    obj.Slot.cap st (irqSlotA (L.ksb s) i) s ⦃ c => c = .Null ∨ ∃ n b0 b1 b2, c = .Notification n b0 b1 b2 ⦄

/-- `DelPlaceAt` at every decode start reached from a `P3Ok` entry. -/
def DelPlace (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (V : U64 → Prop) (P3Ok : S → Prop) : Prop :=
  ∀ s0, EntAt st P3Ok s0 → DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0

/-- **[J] (a64) The deletion's VSpace walks, from the roots the ASID table names** (module docstring): the
restrictions of the false `DelPlaceAt.ptw` / `.elw` / `.ptslot` to the walk starts the unmaps use. -/
structure VsDelAt (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (V : U64 → Prop) (s0 : S) : Prop where
  /-- [J] `unmap_page_table`'s TTBR0 / TTBR1 walk from the root `find_asid_raw` returned finds VSpace words. -/
  ptw : ∀ (Ac : Set U64) (s : S), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    ∀ asid v pt, vspace.find_asid_raw st s asid ⦃ r => ∀ r1, r = .Ok r1 →
      (r1 &&& vspace.ROOT_TAG) ≠ vspace.ROOT_S2 →
      ptWalkStart st s r1 ⦃ x => vspace.unmap_page_table_loop st s v pt x.1 x.2.1 x.2.2 ⦃ f =>
        ∀ y, f = some y → V y ⦄ ⦄ ⦄
  /-- [J] The Stage-2 walk from the root `ept::find` returned, at the arch's IPA size, finds VSpace words. -/
  elw : ∀ (Ac : Set U64) (s : S), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    ∀ (a : A) asid v pt, ept.find st s asid ⦃ r => ∀ r1, r = .Ok r1 → ar.s2_ipa_bits a ⦃ ib => ept.geom ib ⦃ g =>
      ept.unmap_table_loop st s v pt r1 g.top_shift g.top_mask (core.num.U64.wrapping_sub g.levels 1#u64) ⦃ f =>
        ∀ y, f = some y → V y ⦄ ⦄ ⦄ ⦄
  /-- [J] `lookup_pt_slot` from the root `unmap_root` returned, at a user or window address, is a VSpace word. -/
  ptslot : ∀ (Ac : Set U64) (s : S), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    ∀ asid v, HiOK v → vspace.unmap_root st s asid ⦃ o => ∀ root high, o = some (root, high) →
      vspace.lookup_pt_slot st s root v ⦃ lu => V lu.slot ⦄ ⦄

/-- `VsDelAt` at every decode start reached from a `P3Ok` entry. -/
def VsDel (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (V : U64 → Prop) (P3Ok : S → Prop) :
    Prop :=
  ∀ s0, EntAt st P3Ok s0 → VsDelAt st ar T Cs Ω H Sg Rp Scs Nt Z V s0

set_option maxHeartbeats 2000000 in
/-- **The VSpace kinds** (`W7.R.fin_vs`) from the root-restricted walks (`VsDelAt`) and, for a mapped frame,
its address (`FrMapOK`). -/
theorem fin_vs {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 s : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (W : VsDelAt st ar T Cs Ω H Sg Rp Scs Nt Z V s0)
    {a : A} {c : capability.Cap} {fin : Bool}
    (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hfr : FrMapOK c)
    (hc : (∃ x y z w, c = .PageTable x y z w) ∨ (∃ x y z w m asid vaddr, c = .Frame x y z w m false asid vaddr) ∨
      (∃ x y z, c = .Pml4 x y z) ∨ (∃ x y, c = .AsidPool x y) ∨ (∃ x y z w, c = .PageDirectory x y z w) ∨
      (∃ x y z w, c = .Pdpt x y z w) ∨ (∃ x y z, c = .HighVSpace x y z)) :
    objects.finalise_cap st ar s a c fin false ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧
      DelCapOK T Ω Sg H Rp Nt r.1.1 ∧ DelCapOK T Ω Sg H Rp Nt r.1.2 ⦄ := by
  have hb := h.bxi
  obtain ⟨Ac', hb⟩ := hb
  have W' : ∀ (m : Result (S × A)), m ⦃ r => WritesIn st s r.1 V ⦄ →
      (do let (s1, a1) ← m; ok ((capability.Cap.Null, capability.Cap.Null), s1, a1)) ⦃ r =>
        Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧ DelCapOK T Ω Sg H Rp Nt r.1.1 ∧
        DelCapOK T Ω Sg H Rp Nt r.1.2 ⦄ := fun m hm =>
    WP.spec_bind hm fun r hr => by
      obtain ⟨s1, a1⟩ := r
      exact (WP.spec_ok _).2 ⟨h.vs P.vs hr, DelCapOK.null, DelCapOK.null⟩
  have K : (ok ((capability.Cap.Null, capability.Cap.Null), s, a) : Result _) ⦃ r =>
      Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧ DelCapOK T Ω Sg H Rp Nt r.1.1 ∧
      DelCapOK T Ω Sg H Rp Nt r.1.2 ⦄ := (WP.spec_ok _).2 ⟨h, DelCapOK.null, DelCapOK.null⟩
  have UPT : ∀ asid vaddr pt, vspace.unmap_page_table st ar s a asid vaddr pt ⦃ r => WritesIn st s r.1 V ⦄ :=
    fun asid vaddr pt => vspace.unmap_page_table.vsA hA s a asid vaddr pt P.vs
      (W.ptw Ac' s h.fr hb asid vaddr pt) (W.elw Ac' s h.fr hb a asid vaddr pt)
  rcases hc with ⟨x, y, z, w, rfl⟩ | ⟨x, y, z, w, m, asid, vaddr, rfl⟩ | ⟨x, y, z, rfl⟩ | ⟨x, y, rfl⟩ |
    ⟨x, y, z, w, rfl⟩ | ⟨x, y, z, w, rfl⟩ | ⟨x, y, z, rfl⟩
  · simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok]
    split
    · split
      · exact W' _ (UPT z w x)
      · exact K
    · exact K
  · simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok, Bool.false_eq_true, ↓reduceIte]
    apply WP.spec_bind (Pₘ := fun r => WritesIn st s r.1 V)
    · split
      · split
        · rename_i hm hz
          have hv : HiOK vaddr := hfr x y z w asid vaddr (by subst hm; rfl) (by simpa using hz)
          exact vspace.unmap_page.vsA hA s a y asid vaddr x P.vs (W.ptslot Ac' s h.fr hb asid vaddr hv)
        · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
      · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
    · rintro ⟨s1, a1⟩ hw
      cases fin <;> cases w <;> simp only [↓reduceIte, Bool.false_eq_true, uncurry_apply_pair]
      all_goals first
        | exact (WP.spec_ok _).2 ⟨h.vs P.vs hw, DelCapOK.null, DelCapOK.null⟩
        | exact WP.spec_bind (P0.objects.retire_dma_frame.p0 st ar s1 a1 x y L.total hA) fun _ _ =>
            (WP.spec_ok _).2 ⟨h.vs P.vs hw, DelCapOK.null, DelCapOK.null⟩
  · simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok]
    split
    · split
      · exact W' _ (vspace.delete_asid.vs hA s a z x P.vs fun i => P.pool Ac' s z i h.fr hb)
      · exact K
    · exact K
  · simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok]
    split
    · exact W' _ (vspace.delete_asid_pool.vs hA s a y x fun hi => P.aset Ac' s hi h.fr hb)
    · exact K
  · simp only [objects.finalise_cap, objects.finalise_cap_object, vspace.unmap_page_directory, bind_ok]
    split
    · split
      · exact W' _ (UPT z w x)
      · exact K
    · exact K
  · simp only [objects.finalise_cap, objects.finalise_cap_object, vspace.unmap_pdpt, bind_ok]
    split
    · split
      · exact W' _ (UPT z w x)
      · exact K
    · exact K
  · simp only [objects.finalise_cap, objects.finalise_cap_object, lift, bind_ok]
    split
    · split
      · exact W' _ (vspace.delete_asid.vs hA s a z _ P.vs fun i => P.pool Ac' s z i h.fr hb)
      · exact K
    · exact K

set_option maxHeartbeats 1000000 in
/-- **`empty_slot`** of a cap slot, its cleanup cap typed. -/
theorem cdt.empty_slot.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 s : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) {a : A} {x : U64} {c : capability.Cap}
    (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : SlotW T Ω Sg x) (hc : DelCapOK T Ω Sg H Rp Nt c) :
    cdt.empty_slot st ar s a x c ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  obtain ⟨Ac', hb⟩ := h.bxi
  unfold cdt.empty_slot
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st x s hS) fun c0 _ => ?_
  refine WP.spec_bind (P0.capability.Cap.is_null.p0 c0) fun bn _ => ?_
  split
  · exact (WP.spec_ok _).2 h
  refine WP.spec_bind (P.prev Ac' s x h.fr hb hx) fun pv hpv => ?_
  refine WP.spec_bind (P.next Ac' s x h.fr hb hx) fun nx hnx => ?_
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st x s hS) fun fb _ => ?_
  simp only [obj.Slot.is_null, bind_ok]
  refine WP.spec_bind (Pₘ := fun s1 => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s1) ?_ fun s1 h1 => ?_
  · split
    · exact (WP.spec_ok _).2 h
    · rename_i hp0
      exact WP.spec_mono (obj.Slot.set_next.capw (hpv.resolve_left (by simpa using hp0))) fun s' w =>
        h.capw7 w fun _ hb => hb
  refine WP.spec_bind (Pₘ := fun s2 => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s2) ?_ fun s2 h2 => ?_
  · split
    · exact (WP.spec_ok _).2 h1
    · rename_i hn0
      have hnW := hnx.resolve_left (by simpa using hn0)
      refine WP.spec_bind (obj.Slot.set_prev.capw hnW) fun s3 w3 => ?_
      have h3 := h1.capw7 w3 fun _ hb => hb
      refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st nx s3 hS) fun nfb _ => ?_
      split <;> exact WP.spec_mono (obj.Slot.set_first_badged.capw hnW) fun s' w => h3.capw7 w fun _ hb => hb
  refine WP.spec_bind (obj.Slot.clear.capw hx) fun s3 w3 => ?_
  exact objects.post_cap_deletion.cur0 hA (h2.capw7 w3 fun _ hb => hb) hc
set_option maxHeartbeats 2000000 in
/-- **`cdt.swap`** of two cap slots. -/
theorem cdt.swap.cur0 {V : U64 → Prop} {s0 s : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0)
    {c1 c2 : capability.Cap} {x1 x2 : U64} (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (h1 : SlotW T Ω Sg x1) (h2 : SlotW T Ω Sg x2) :
    cdt.swap st s c1 x1 c2 x2 ⦃ s' => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.swap
  refine WP.spec_bind (h.cw7 (obj.Slot.set_cap.capw h1)) fun sa ha => ?_
  refine WP.spec_bind (ha.cw7 (obj.Slot.set_cap.capw h2)) fun sb hb => ?_
  obtain ⟨Acb, hbb⟩ := hb.bxi
  refine WP.spec_bind (P.prev Acb sb x1 hb.fr hbb h1) fun p1 hp1 => ?_
  refine WP.spec_bind (P.next Acb sb x1 hb.fr hbb h1) fun n1 hn1 => ?_
  refine WP.spec_bind (P0.obj.Slot.revocable.p0 st x1 sb hS) fun r1 _ => ?_
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st x1 sb hS) fun f1 _ => ?_
  simp only [obj.Slot.is_null, bind_ok]
  refine WP.spec_bind (Pₘ := fun s' => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s') ?_ fun sc hc => ?_
  · split
    · exact (WP.spec_ok _).2 hb
    · rename_i e; exact hb.cw7 (obj.Slot.set_next.capw (hp1.resolve_left (by simpa using e)))
  refine WP.spec_bind (Pₘ := fun s' => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s') ?_ fun sd hd => ?_
  · split
    · exact (WP.spec_ok _).2 hc
    · rename_i e; exact hc.cw7 (obj.Slot.set_prev.capw (hn1.resolve_left (by simpa using e)))
  obtain ⟨Acd, hbd⟩ := hd.bxi
  refine WP.spec_bind (P.prev Acd sd x2 hd.fr hbd h2) fun p2 hp2 => ?_
  refine WP.spec_bind (P.next Acd sd x2 hd.fr hbd h2) fun n2 hn2 => ?_
  refine WP.spec_bind (P0.obj.Slot.revocable.p0 st x2 sd hS) fun r2 _ => ?_
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st x2 sd hS) fun f2 _ => ?_
  refine WP.spec_bind (hd.cw7 (obj.Slot.set_prev.capw h1)) fun s5 h5 => ?_
  refine WP.spec_bind (h5.cw7 (obj.Slot.set_next_flags.capw h1)) fun s6 h6 => ?_
  refine WP.spec_bind (h6.cw7 (obj.Slot.set_prev.capw h2)) fun s7 h7 => ?_
  refine WP.spec_bind (h7.cw7 (obj.Slot.set_next_flags.capw h2)) fun s12 h12 => ?_
  refine WP.spec_bind (Pₘ := fun s' => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s') ?_ fun s13 h13 => ?_
  · split
    · exact (WP.spec_ok _).2 h12
    · rename_i e; exact h12.cw7 (obj.Slot.set_next.capw (hp2.resolve_left (by simpa using e)))
  split
  · exact (WP.spec_ok _).2 h13
  · rename_i e; exact h13.cw7 (obj.Slot.set_prev.capw (hn2.resolve_left (by simpa using e)))

theorem cdt.cap_swap_for_delete.cur0 {V : U64 → Prop} {s0 s : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0)
    {x1 x2 : U64} (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (h1 : SlotW T Ω Sg x1) (h2 : SlotW T Ω Sg x2) :
    cdt.cap_swap_for_delete st s x1 x2 ⦃ s' => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.cap_swap_for_delete obj.Slot.Insts.CoreCmpPartialEqSlot.eq
  simp only [bind_ok]
  split
  · exact (WP.spec_ok _).2 h
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st x1 s hS) fun c1 _ => ?_
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st x2 s hS) fun c2 _ => ?_
  exact cdt.swap.cur0 P h h1 h2

set_option hygiene false in
/-- The preemption-point tail of a deferred round (`Cur0` at `s3`). -/
local macro "dtail" : tactic => `(tactic| (
  refine WP.spec_bind (sched.preemption_point.cur0 hA h3) ?_
  rintro ⟨rr, s4, a4⟩ h4
  try simp only [uncurry_apply_pair] at h4 ⊢
  rcases rr with _ | ee
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok]
    refine (WP.spec_ok _).2 ⟨h4, ?_⟩
    show fuel1.val < fuel.val
    omega
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 ⟨h4, fun v hv => by cases hv⟩))

set_option maxHeartbeats 4000000 in
/-- **`finalise_slot_deferred`** of a cap slot: `Cur0`, the cleanup cap typed. -/
theorem cdt.finalise_slot_deferred.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 s : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (F : FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z FrMapOK s0)
    {a : A} {x : U64} (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : SlotW T Ω Sg x) :
    cdt.finalise_slot_deferred st ar s a x ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧
      ∀ v, r.1 = .Ok v → DelCapOK T Ω Sg H Rp Nt v.cleanup ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.finalise_slot_deferred cdt.finalise_slot_deferred_loop
  apply loop.spec_decr_nat (measure := fun y => y.2.2.val)
    (inv := fun y => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 y.1)
  · rintro ⟨s1, a1, fuel⟩ h1
    simp only at h1
    dsimp only
    unfold cdt.finalise_slot_deferred_loop.body
    split
    swap
    · exact (WP.spec_ok _).2 ⟨h1, fun v hv => by cases hv⟩
    rename_i hf
    have hf' : 0 < fuel.val := by simpa using hf
    step as ⟨fuel1, hf1⟩
    obtain ⟨Acx, hbx⟩ := h1.bxi
    refine WP.spec_bind (WP.spec_and (P.cap Acx s1 x h1.fr hbx hx) (P.frm Acx s1 x h1.fr hbx hx))
      fun c ⟨⟨hc, hpl⟩, hfr⟩ => ?_
    refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h1, fun v hv => by cases hv; exact DelCapOK.null⟩
    refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s1 x c hS) fun fin _ => ?_
    refine WP.spec_bind (F Ac s1 a1 c fin h1 hc hpl hfr) ?_
    rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨h2', hrem, hcl⟩
    try simp only [uncurry_apply_pair]
    refine WP.spec_bind (P0.cdt.cap_removable.p0 rem x) fun br _ => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h2', fun v hv => by cases hv; exact hcl⟩
    refine WP.spec_bind (h2'.cw7 (obj.Slot.set_cap.capw (c := rem) hx)) fun s2 h2 => ?_
    refine WP.spec_bind (P0.cdt.cap_cyclic_zombie.p0 rem x) fun bz _ => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h2, fun v hv => by cases hv; exact hcl⟩
    refine WP.spec_bind (Pₘ := fun s' => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s') ?_ fun s3 h3 => ?_
    · split
      all_goals try exact (WP.spec_ok _).2 h2
      rename_i zp zt zn
      exact cdt.cap_swap_for_delete.cur0 P h2 (hrem.2.2.2.2.1 zp zt zn rfl).1 hx
    dtail
  · exact h

/-- **`delete_deferred`** of a cap slot. -/
theorem cdt.delete_deferred.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 s : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (F : FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z FrMapOK s0)
    {a : A} {x : U64} (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : SlotW T Ω Sg x) :
    cdt.delete_deferred st ar s a x ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄ := by
  unfold cdt.delete_deferred
  refine WP.spec_bind (cdt.finalise_slot_deferred.cur0 hA P F h hx) ?_
  rintro ⟨r, s1, a1⟩ ⟨h1, hv1⟩
  try simp only [uncurry_apply_pair] at h1 hv1 ⊢
  rcases r with v | e
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    split
    · refine WP.spec_bind (cdt.empty_slot.cur0 hA P h1 hx (hv1 v rfl)) ?_
      rintro ⟨s2, a2⟩ h2
      exact (WP.spec_ok _).2 h2
    · exact (WP.spec_ok _).2 h1
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 h1

set_option maxHeartbeats 1000000 in
/-- `W7.cdt.empty_slot.cur0` (`Cur0` only) from the `rv`-free placement `R.DelPlaceAt`. -/
theorem cdt.empty_slot.c0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 s : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) {a : A} {x : U64} {c : capability.Cap}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : SlotW T Ω Sg x) (hc : DelCapOK T Ω Sg H Rp Nt c) :
    cdt.empty_slot st ar s a x c ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  obtain ⟨Ac', hb⟩ := h.bxi
  unfold cdt.empty_slot
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st x s hS) fun c0 _ => ?_
  refine WP.spec_bind (P0.capability.Cap.is_null.p0 c0) fun bn _ => ?_
  split
  · exact (WP.spec_ok _).2 h
  refine WP.spec_bind (P.prev Ac' s x h.fr hb hx) fun pv hpv => ?_
  refine WP.spec_bind (P.next Ac' s x h.fr hb hx) fun nx hnx => ?_
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st x s hS) fun fb _ => ?_
  simp only [obj.Slot.is_null, bind_ok]
  refine WP.spec_bind (Pₘ := fun s1 => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s1) ?_ fun s1 h1 => ?_
  · split
    · exact (WP.spec_ok _).2 h
    · rename_i hp0
      exact WP.spec_mono (obj.Slot.set_next.capw (hpv.resolve_left (by simpa using hp0))) fun s' w =>
        h.capw7 w fun _ hb => hb
  refine WP.spec_bind (Pₘ := fun s2 => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s2) ?_ fun s2 h2 => ?_
  · split
    · exact (WP.spec_ok _).2 h1
    · rename_i hn0
      have hnW := hnx.resolve_left (by simpa using hn0)
      refine WP.spec_bind (obj.Slot.set_prev.capw hnW) fun s3 w3 => ?_
      have h3 := h1.capw7 w3 fun _ hb => hb
      refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st nx s3 hS) fun nfb _ => ?_
      split <;> exact WP.spec_mono (obj.Slot.set_first_badged.capw hnW) fun s' w => h3.capw7 w fun _ hb => hb
  refine WP.spec_bind (obj.Slot.clear.capw hx) fun s3 w3 => ?_
  exact W7.objects.post_cap_deletion.cur0 hA (h2.capw7 w3 fun _ hb => hb) hc

/-- `W7.finGap_thread` (`Cur0` part) from the `rv`-free placement (its [P] `rcw`). -/
theorem finGap_thread0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop} {s0 : S}
    (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) :
    C0Gap st ar T Cs Ω H Sg Rp Scs Nt Z (fun c => ∃ x1, c = .Thread x1) s0 := by
  intro Ac s a c fin h _ hc hpl ⟨p, e⟩
  subst e
  have hp := hc.2.2.2.2.2 p rfl
  obtain ⟨hid, hv0⟩ := hpl.1 p rfl
  obtain ⟨Ac', hb⟩ := h.bxi
  have hb' := hb.blk
  have hT := hb.1.choose_spec.choose_spec.tcbs
  have hct : L.curW s ∈ T := hb.1.choose_spec.choose_spec.curT
  have hna := h.na p hp
  have hrc := P.rcw Ac' s p h.fr hb hp
  rw [fin_cap_eq_obj (by simp)]
  refine WP.spec_mono (WP.spec_and (WP.spec_and (fin_thread.rem hA s a p fin)
    (fin_thread.blk7 hA s a p fin hb' hp hna (Ne.symm hid) hv0 hrc))
    (fin_thread.curR7 hA s a p (L.curW s) fin hb' hp hna (Ne.symm hid) hv0 hct hrc)) ?_
  rintro ⟨⟨r1, r2⟩, s', a'⟩ ⟨⟨e, hb2, f2⟩, ec, ecs, esc, ea, enb⟩
  simp only at e hb2 f2 ec ecs esc ea enb ⊢
  refine ⟨Cur0.mk h (BlkOK.bxi hb2) ec ecs esc ea (Or.inr (enb h.nb)) f2, ?_, ?_⟩
  · simp only [Prod.mk.injEq] at e
    rw [e.1]; split
    · exact tcb_zombieOK hT hp
    · exact DelCapOK.null
  · simp only [Prod.mk.injEq] at e
    rw [e.2]; exact DelCapOK.null


/-- `W7.finGap_irq` (`Cur0` part) from the `rv`-free placement. -/
theorem finGap_irq0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) :
    C0Gap st ar T Cs Ω H Sg Rp Scs Nt Z (fun c => ∃ x1, c = .IrqHandler x1) s0 := by
  have hS : P0.StoreTotal st := L.total
  intro Ac s a c fin h _ hc _ ⟨irq, e⟩
  subst e
  have hi := hc.2.1 irq rfl
  obtain ⟨Ac', hb⟩ := h.bxi
  unfold objects.finalise_cap
  simp only [bind_ok]
  refine WP.spec_bind (Pₘ := fun r : S × A => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1) ?_ ?_
  · split
    · unfold interrupt.deleting_irq_handler
      refine WP.spec_bind (interrupt.irq_slot.val s irq) fun isl eisl => ?_
      subst eisl
      have hW := slotW_to7 (irq_slotW hb hi)
      unfold cdt.delete_one
      refine WP.spec_bind (WP.spec_and (P.irq Ac' s irq h.fr hb hi) (P.cap Ac' s _ h.fr hb hW)) fun c ⟨hc', hcd⟩ => ?_
      refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
      split
      · exact (WP.spec_ok _).2 h
      refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s _ c hS) fun f _ => ?_
      rcases hc' with rfl | ⟨n, b0, b1, b2, rfl⟩
      · simp [objects.finalise_cap_object]
        exact cdt.empty_slot.c0 hA P h hW DelCapOK.null
      · obtain ⟨hn, hH⟩ := hcd.1.1.2.1 n b0 b1 b2 rfl
        refine WP.spec_bind (fin_ntfn_obj.cur0 (ar := ar) (a := a) (fin := f) (b0 := b0) (b1 := b1) (b2 := b2) h hn hH) ?_
        rintro ⟨_, s1, a1⟩ ⟨-, h1⟩
        exact cdt.empty_slot.c0 hA P h1 hW DelCapOK.null
    · exact (WP.spec_ok _).2 h
  rintro ⟨s1, a1⟩ h1
  simp only at h1 ⊢
  unfold objects.finalise_cap_object
  dsimp only
  split
  · exact (WP.spec_ok _).2 ⟨h1, DelCapOK.null, hc⟩
  · exact (WP.spec_ok _).2 ⟨h1, DelCapOK.null, DelCapOK.null⟩

set_option maxHeartbeats 1000000 in
/-- The IRQ-handler kind keeps [J] `RunVcpuInv` (the handler slot's notification cap, then `empty_slot` over
`Cur0R`), from the `rv`-free placement. -/
theorem finRv_irq {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop} {s0 s : S}
    (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) {a : A} {irq : U64} {fin : Bool}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hRV : RunVcpuInv st T s)
    (hc : DelCapOK T Ω Sg H Rp Nt (.IrqHandler irq)) :
    objects.finalise_cap st ar s a (.IrqHandler irq) fin false ⦃ r => RunVcpuInv st T r.2.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hi := hc.2.1 irq rfl
  obtain ⟨Ac', hb⟩ := h.bxi
  unfold objects.finalise_cap
  simp only [bind_ok]
  refine WP.spec_bind (Pₘ := fun r : S × A => RunVcpuInv st T r.1) ?_ ?_
  · split
    · unfold interrupt.deleting_irq_handler
      refine WP.spec_bind (interrupt.irq_slot.val s irq) fun isl eisl => ?_
      subst eisl
      have hW := slotW_to7 (irq_slotW hb hi)
      unfold cdt.delete_one
      refine WP.spec_bind (WP.spec_and (P.irq Ac' s irq h.fr hb hi) (P.cap Ac' s _ h.fr hb hW)) fun c ⟨hc', hcd⟩ => ?_
      refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
      split
      · exact (WP.spec_ok _).2 hRV
      refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s _ c hS) fun f _ => ?_
      rcases hc' with rfl | ⟨n, b0, b1, b2, rfl⟩
      · simp [objects.finalise_cap_object]
        exact WP.spec_mono (cdt.empty_slot.cur0 hA P ⟨h, hRV⟩ hW DelCapOK.null) fun r hr => hr.2
      · obtain ⟨hn, hH⟩ := hcd.1.1.2.1 n b0 b1 b2 rfl
        refine WP.spec_bind (WP.spec_and (fin_ntfn_obj.cur0 (ar := ar) (a := a) (fin := f) (b0 := b0) (b1 := b1)
          (b2 := b2) h hn hH) (fin_ntfn_obj.rvi (ar := ar) s a n b0 b1 b2 f hb.blk hn hH hRV)) ?_
        rintro ⟨_, s1, a1⟩ ⟨⟨_, h1⟩, r1⟩
        exact WP.spec_mono (cdt.empty_slot.cur0 hA P ⟨h1, r1⟩ hW DelCapOK.null) fun r hr => hr.2
    · exact (WP.spec_ok _).2 hRV
  rintro ⟨s1, a1⟩ h1
  simp only at h1 ⊢
  unfold objects.finalise_cap_object
  dsimp only
  split
  · exact (WP.spec_ok _).2 h1
  · exact (WP.spec_ok _).2 h1

/-- **[J] `FinRvAt` from the `rv`-free placement and [J] `FinRvRest`.** -/
theorem finRvAt_of {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop} {s0 : S}
    (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (G : FinRvRest st ar T Cs Ω H Sg Rp Scs Nt Z s0) :
    FinRvAt st ar T Cs Ω H Sg Rp Scs Nt Z s0 := by
  intro Ac s a c fin h hRV hc hpl hk
  rcases hk with ⟨x1, x2, x3, x4, x5, x6, rfl⟩ | ⟨x1, x2, x3, x4, rfl⟩ | hk | hk | hk | ⟨x1, rfl⟩ | hk | hk | hk
  · exact finRv_ep h hRV hc
  · exact finRv_ntfn h hRV hc
  · exact G Ac s a _ fin h hRV hc hpl (Or.inl hk)
  · exact G Ac s a _ fin h hRV hc hpl (Or.inr (Or.inl hk))
  · exact G Ac s a _ fin h hRV hc hpl (Or.inr (Or.inr (Or.inl hk)))
  · exact finRv_irq hA P h hRV hc
  · exact G Ac s a _ fin h hRV hc hpl (Or.inr (Or.inr (Or.inr (Or.inl hk))))
  · exact G Ac s a _ fin h hRV hc hpl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hk)))))
  · exact G Ac s a _ fin h hRV hc hpl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hk)))))

/-- The thread kind keeps [J] `RunVcpuInv`, from the `rv`-free placement (its [P] `rcw`). -/
theorem finRv_thread {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop} {s0 s : S}
    (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) {a : A} {p : U64} {fin : Bool}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hRV : RunVcpuInv st T s)
    (hc : DelCapOK T Ω Sg H Rp Nt (.Thread p)) (hpl : FinPl st Scs s (.Thread p)) :
    objects.finalise_cap st ar s a (.Thread p) fin false ⦃ r => RunVcpuInv st T r.2.1 ⦄ := by
  have hp := hc.2.2.2.2.2 p rfl
  obtain ⟨hid, hv0⟩ := hpl.1 p rfl
  obtain ⟨Ac', hb⟩ := h.bxi
  have hna := h.na p hp
  have hrc := P.rcw Ac' s p h.fr hb hp
  rw [fin_cap_eq_obj (by simp)]
  exact fin_thread.rvi hA s a p fin hb.blk hp hna (Ne.symm hid) hv0 hrc hRV

/-- **[J] `FinRvRest` from the `rv`-free placement and [J] `FinRvRest3`.** -/
theorem finRvRest_of3 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop} {s0 : S}
    (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (G : FinRvRest3 st ar T Cs Ω H Sg Rp Scs Nt Z s0) :
    FinRvRest st ar T Cs Ω H Sg Rp Scs Nt Z s0 := by
  intro Ac s a c fin h hRV hc hpl hk
  rcases hk with hk | ⟨p, x, rfl⟩ | ⟨p, rfl⟩ | hk | hk | hk
  · exact G Ac s a _ fin h hRV hc hpl (Or.inl hk)
  · exact finRv_sc hA h hRV hpl
  · exact finRv_thread hA P h hRV hc hpl
  · exact G Ac s a _ fin h hRV hc hpl (Or.inr (Or.inl hk))
  · exact G Ac s a _ fin h hRV hc hpl (Or.inr (Or.inr (Or.inl hk)))
  · exact G Ac s a _ fin h hRV hc hpl (Or.inr (Or.inr (Or.inr hk)))


/-! ## Every kind, the deletion gaps, the CNode family -/

/-- **Every cap kind's finalisation over `Cur0R`** for caps with `FrMapOK` (`W7.R.fin_all` with the VSpace kinds
from `A5.fin_vs`). -/
theorem fin_all {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (W : VsDelAt st ar T Cs Ω H Sg Rp Scs Nt Z V s0)
    (G : FinGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) :
    FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z FrMapOK s0 := by
  have ep := ofC0 (C0Gap.ofW7 (W7.FinGapAt.ofOld (finGap_ep.at s0) (by
      rintro c ⟨_, _, _, _, _, _, rfl⟩; exact ⟨fun _ _ _ _ h => (nomatch h), fun _ _ _ h => (nomatch h)⟩))) G.rv
    (by rintro c ⟨_, _, _, _, _, _, rfl⟩; exact Or.inl ⟨_, _, _, _, _, _, rfl⟩)
  have ntfn := ofC0 (C0Gap.ofW7 (W7.FinGapAt.ofOld (finGap_ntfn.at s0) (by
      rintro c ⟨_, _, _, _, rfl⟩; exact ⟨fun _ _ _ _ h => (nomatch h), fun _ _ _ h => (nomatch h)⟩))) G.rv
    (by rintro c ⟨_, _, _, _, rfl⟩; exact Or.inr (Or.inl ⟨_, _, _, _, rfl⟩))
  have reply := ofC0 (finGap_reply0 hA) G.rv
    (by rintro c ⟨_, _, rfl⟩; exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩)))
  have sc := ofC0 (C0Gap.ofW7 (W7.FinGapAt.ofOld ((finGap_sc hA).at s0) (by
      rintro c ⟨_, _, rfl⟩; exact ⟨fun _ _ _ _ h => (nomatch h), fun _ _ _ h => (nomatch h)⟩))) G.rv
    (by rintro c ⟨_, _, rfl⟩; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))))
  have thread := ofC0 (finGap_thread0 hA P) G.rv
    (by rintro c ⟨_, rfl⟩; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩)))))
  have irq := ofC0 (finGap_irq0 hA P) G.rv
    (by rintro c ⟨_, rfl⟩; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))))))
  have arch := ofC0 (C0Gap.ofW7 G.arch) G.rv (by
    rintro c (⟨_, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, _, rfl⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _, rfl⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, _, _, _, _, _, rfl⟩))))))))
  intro Ac s a c fin h hc hpl hfr
  cases c with
  | Null => exact fin_noop h (Or.inl rfl)
  | Untyped => exact fin_noop h (Or.inr (Or.inl ⟨_, _, _, _, rfl⟩))
  | IrqControl => exact fin_noop h (Or.inr (Or.inr (Or.inl rfl)))
  | Domain => exact fin_noop h (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | SchedControl => exact fin_noop h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩)))))
  | AsidControl => exact fin_noop h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  | IoPortControl => exact fin_noop h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  | TdxControl => exact fin_noop h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))
  | CNode => exact fin_cnode h hc
  | Zombie => exact fin_zombie h hc
  | PageTable => exact fin_vs hA P W h hfr (Or.inl ⟨_, _, _, _, rfl⟩)
  | HighVSpace => exact fin_vs hA P W h hfr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, _, rfl⟩))))))
  | Pml4 => exact fin_vs hA P W h hfr (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl⟩)))
  | AsidPool => exact fin_vs hA P W h hfr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))))
  | Frame x1 x2 x3 x4 x5 e x6 x7 =>
    cases e
    · exact fin_vs hA P W h hfr (Or.inr (Or.inl ⟨_, _, _, _, _, _, _, rfl⟩))
    · exact arch _ _ _ _ _ h hc hpl (Or.inr (Or.inr ⟨_, _, _, _, _, _, _, rfl⟩))
  | Endpoint => exact ep _ _ _ _ _ h hc hpl ⟨_, _, _, _, _, _, rfl⟩
  | Notification => exact ntfn _ _ _ _ _ h hc hpl ⟨_, _, _, _, rfl⟩
  | Reply => exact reply _ _ _ _ _ h hc hpl ⟨_, _, rfl⟩
  | SchedContext => exact sc _ _ _ _ _ h hc hpl ⟨_, _, rfl⟩
  | Thread => exact thread _ _ _ _ _ h hc hpl ⟨_, rfl⟩
  | IrqHandler => exact irq _ _ _ _ _ h hc hpl ⟨_, rfl⟩
  | PageDirectory => exact fin_vs hA P W h hfr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl⟩)))))
  | Pdpt => exact fin_vs hA P W h hfr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl⟩))))))
  | Vcpu => exact arch _ _ _ _ _ h hc hpl (Or.inl ⟨_, rfl⟩)
  | Ept => exact arch _ _ _ _ _ h hc hpl (Or.inr (Or.inl ⟨_, _, _, _, _, rfl⟩))
  | IoPort => exact fin_ioPort h hc ⟨_, _, _, rfl⟩

/-- **`A5.DelGapsAt`, discharged** from `A5.DelPlaceAt`, [J] `VsDelAt` and `R.FinGapsAt`. -/
theorem delGaps_of {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (W : VsDelAt st ar T Cs Ω H Sg Rp Scs Nt Z V s0)
    (G : FinGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) :
    DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0 where
  cap := P.cap
  frm := P.frm
  fin Ac s a c fin h hc hpl hfr := fin_all hA P W G Ac s a c fin h hc hpl hfr
  deferred _ _ _ _ h hx := cdt.delete_deferred.cur0 hA P (fin_all hA P W G) h hx
  empty _ _ _ _ _ h hx hc := cdt.empty_slot.cur0 hA P h hx hc
  next := P.next

/-- `R.FinGapsAt` from `A5.DelPlaceAt` and `FinGapsAt4` ([J] `FinRvRest4`; the thread / IRQ kinds read `rcw` /
`irq`). -/
theorem finGapsAt_of4 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop} {s0 : S}
    (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (G : FinGapsAt4 st ar T Cs Ω H Sg Rp Scs Nt Z s0) :
    FinGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0 :=
  ⟨G.arch, finRvAt_of hA P (finRvRest_of3 hA P (finRvRest3_of4 hA G.rv))⟩

/-- **`A5.DelGaps`** at every decode start from `A5.DelPlace`, [J] `VsDel` and `FinGaps4`. -/
theorem delGaps_of_gaps4 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    (P : DelPlace st T Cs Ω H Sg Rp Scs Nt Z V P3Ok) (W : VsDel st ar T Cs Ω H Sg Rp Scs Nt Z V P3Ok)
    (G : FinGaps4 st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok :=
  fun s0 hE => delGaps_of hA (P s0 hE) (W s0 hE) (finGapsAt_of4 hA (P s0 hE) (G s0 hE))

/-- **The `CNode` family's decode gap** from `CdtHyps2`, `A5.DelPlace`, [J] `VsDel` and `FinGaps4`: no walk
field quantified over every root. -/
theorem decGap_cnode_rv4 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    (C : CdtHyps2 st T Cs Ω H Sg Rp Scs Nt Z P3Ok) (P : DelPlace st T Cs Ω H Sg Rp Scs Nt Z V P3Ok)
    (W : VsDel st ar T Cs Ω H Sg Rp Scs Nt Z V P3Ok)
    (G : FinGaps4 st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .cnode :=
  decGap_cnode2 hA C (delGaps_of_gaps4 hA P W G)

end A5
end R
end W7

end

end Fl4ProofsA64.P1
