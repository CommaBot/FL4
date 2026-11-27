/-
P1 (x86_64): **the deletion chain with root-restricted paging walks** (namespace `X5`), replacing the walk
fields of `DelPlaceAt` (QueueDelFin) that are false as stated.

`DelPlaceAt.pt` / `.pd` / `.pdpt` say `∀ r1 v, vspace.lookup_p{t,d,dpt}_slot st s r1 v ⦃ r => ∀ x, r = .Ok x → V x ⦄`
for **every** start word `r1`. `lookup_pdpt_slot st s r1 v` reads `e = mem (r1 + 8·idx39 v)` and, when
`e &&& P_PRESENT ≠ 0`, returns `table_of e + 8·idx30 v` (Funs `vspace.lookup_pdpt_slot`, vspace.rs:119–125);
`lookup_pd_slot` / `lookup_pt_slot` add one or two more such reads. With `r1` a TCB `t` and `v` with
`idx39 v = 32 + k` (a user address), `e` is the saved user register `k` at `t + 0x100 + 8k` (layout.rs:19), which
the thread chooses: `e = paddr(t) ||| 1` gives the slot `t + 8·idx30 v`, a TCB word, and other choices give any
4 KiB-aligned kernel address plus an offset; `VsOK` puts `V` inside `Ω` and off `Sg`, so the field fails at every
state with a thread whose register `k` has bit 0 set. These fields are not changed here; this module gives new
forms and re-proves the deletion chain on them.

New premises (fields of `X5.DelPlaceAt`; see their docstrings):
* **[J] `walk`**: the three lookups from a root `find_vspace_for_asid` returns at the current state, at a user
  address (`v < 2^47`), give VSpace words (`WalkOK`). Source (crates/fl4-core/src/arch/x86_64/vspace.rs):
  ASID-pool entries are written only by ASIDPoolAssign with a `Pml4` cap's object (1246; EPT roots carry tag
  bit 0, which `find_vspace_for_asid` refuses, 169–172); a user PML4's entries 0..255 are written only by
  `decode_table_map` / boot with table descriptors of `Pdpt` objects (1124–1127, boot.rs:33–37), PDPT / PD entries
  only with `PageDirectory` / `PageTable` objects or leaf frames (`P_PS`, refused by the next lookup); entries
  256..511 copy the kernel's (`copy_global_mappings`, 219–227), whose tables are not heap objects — hence the
  bound `v < 2^47` (`idx39 v < 256`).
* **[J] `walk0`**: the same walks at a state inside the decode for a root `find_vspace_for_asid` returned at the
  decode's start `s0` (FrameBatch keeps the root it checked at `s0`, `vspace.Batch.root`).
* **[J] `va`**: a cap in a cap slot that is a mapped frame (native or EPT) or a mapped page table / page directory /
  PDPT has an address below `2^47` (`VaOK`). Needed because `finalise_cap` of such a cap at a kernel-half address
  would unmap through the kernel's tables (outside `Ω`): without it `fin_vs` (and so the old
  `DelGapsAt.fin`, stated for every `DelCapOK` cap) is not provable from true placements. Source: mapped frame
  caps are made by `decode_page_map` / `decode_frame_batch` (`vaddr, vtop ≤ USER_TOP`, or the cap's own address
  on a remap, 569–582, 826–839), `ept::map_frame` (`gpa < LIMIT = 2^47`, ept.rs:13, 134, 173), the boot image
  (user addresses, boot.rs:206–217); tables by `decode_table_map` (`vaddr ≤ USER_TOP`, 1114) and boot (the image's
  range); `derive_cap` and the rights masks keep or clear them.

So the deletion's finalisation takes `VaOK c` (`FinGapAt … VaOK`, `X5.DelGapsAt.fin`), read with the cap from its
slot (`X5.DelGapsAt.va` / `X5.DelPlaceAt.va`). `X5.DelPlaceAt` is `DelPlaceAt` without `pt` / `pd` / `pdpt` and
with `walk` / `walk0` / `va`; its other fields (`vs`, `cap`, `next`, `prev`, `pool`, `aset`, `irq`, `pml`) are
unchanged in statement.

Proved: `vspace.unmap_page_table.vs5`, `vspace.unmap_page_directory.vs5`, `vspace.unmap_page.vs5` (QueueVsFin /
QueueDelFin's unmaps with the walk hypotheses restricted to the root `find_vspace_for_asid` returns and a user
address), `X5.fin_vs`, `X5.fin_all`, and the deletion chain over `X5.DelGapsAt` / `X5.DelPlaceAt` (QueueDecDel /
QueueDelFin / QueueFinCur / QueueFinThr / QueueDecIrq text by script, `handoff/a64-wip/gen24/gen_delx5.py`):
`cdt.finalise_slot_immediate.cur0` … **`decGap_cnode2`**, `empty_slot`, `swap`, `cap_swap_for_delete`,
`finalise_slot_deferred`, `delete_deferred`, **`delGaps_of`**, `finGap_irq`, `FinGapsAt.kinds`,
`cdt.delete_one.irq_cur0`, `interrupt.decode_irq_handler.dec`, **`decGap_irqHandler`**.

Caveat (unchanged in kind, as every existing `DelPlaceAt` field): the placements are stated at every `Fr0 ∧ BXI`
state of the decode, and `Fr0` allows any `Cur0W` word to change, so read literally at an arbitrary such state
they are not implied by reachability; they are meant along the decode's own states.
-/
import Fl4Proofs.P1.QueueEntryGaps4
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}

/-- **The walks from a root at a user address give VSpace words**: `lookup_pt_slot`, `lookup_pd_slot` and
`lookup_pdpt_slot` from `r1` at every `v < 2^47` (PML4 index below 256). -/
def WalkOK (st : machine.Store S) (V : U64 → Prop) (s : S) (r1 : U64) : Prop :=
  ∀ v : U64, v.val < 2 ^ 47 →
    vspace.lookup_pt_slot st s r1 v ⦃ r => ∀ x, r = .Ok x → V x ⦄ ∧
    vspace.lookup_pd_slot st s r1 v ⦃ r => ∀ x, r = .Ok x → V x ⦄ ∧
    vspace.lookup_pdpt_slot st s r1 v ⦃ r => ∀ x, r = .Ok x → V x ⦄

/-- **A mapping cap's address is a user address**: a mapped frame cap (native or EPT), a mapped page table,
page directory or PDPT cap names an address below `2^47` (`USER_TOP` = `2^47 - 1`; EPT's `LIMIT` = `2^47`). -/
def VaOK (c : capability.Cap) : Prop :=
  (∀ p sz r d e asid v, c = .Frame p sz r d true e asid v → v.val < 2 ^ 47) ∧
  (∀ p asid v, c = .PageTable p true asid v → v.val < 2 ^ 47) ∧
  (∀ p asid v, c = .PageDirectory p true asid v → v.val < 2 ^ 47) ∧
  (∀ p asid v, c = .Pdpt p true asid v → v.val < 2 ^ 47)

theorem VaOK.null : VaOK .Null :=
  ⟨fun _ _ _ _ _ _ _ h => (by cases h), fun _ _ _ h => (by cases h), fun _ _ _ h => (by cases h),
    fun _ _ _ h => (by cases h)⟩

/-- **`unmap_page_table`** writes only the PD slot it looks up, from the root `find_vspace_for_asid` returns
(`WalkOK`) at a user address. -/
theorem vspace.unmap_page_table.vs5 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (asid vaddr pt : U64) {V : U64 → Prop} (hV : VsOK Ω Sg V) (hv : vaddr.val < 2 ^ 47)
    (hw : vspace.find_vspace_for_asid st s asid ⦃ r => ∀ r1, r = .Ok r1 → WalkOK st V s r1 ⦄) :
    vspace.unmap_page_table st ar s a asid vaddr pt ⦃ r => WritesIn st s r.1 V ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have i1 := hA.invalidate_asid
  have i2 := hA.invalidate_page_structures
  unfold vspace.unmap_page_table
  refine WP.spec_bind hw fun r hr => ?_
  rcases r with r1 | e
  · refine WP.spec_bind (hr r1 rfl vaddr hv).2.1 fun r2 hr2 => ?_
    rcases r2 with x | e
    · have hx := hr2 x rfl
      step*
      all_goals first | exact WritesIn.refl _ _ | (subst_vars; exact writesIn_wr_V hV hx)
    · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)

/-- **`unmap_page_directory`** writes only the PDPT slot it looks up, from the root `find_vspace_for_asid`
returns (`WalkOK`) at a user address. -/
theorem vspace.unmap_page_directory.vs5 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (asid vaddr pd : U64) {V : U64 → Prop} (hV : VsOK Ω Sg V) (hv : vaddr.val < 2 ^ 47)
    (hw : vspace.find_vspace_for_asid st s asid ⦃ r => ∀ r1, r = .Ok r1 → WalkOK st V s r1 ⦄) :
    vspace.unmap_page_directory st ar s a asid vaddr pd ⦃ r => WritesIn st s r.1 V ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have i1 := hA.invalidate_asid
  have i2 := hA.invalidate_page_structures
  unfold vspace.unmap_page_directory
  refine WP.spec_bind hw fun r hr => ?_
  rcases r with r1 | e
  · refine WP.spec_bind (hr r1 rfl vaddr hv).2.2 fun r2 hr2 => ?_
    rcases r2 with x | e
    · have hx := hr2 x rfl
      step*
      all_goals first | exact WritesIn.refl _ _ | (subst_vars; exact writesIn_wr_V hV hx)
    · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)

/-- **`unmap_page`** writes only the PT/PD/PDPT slot it looks up, from the root `find_vspace_for_asid` returns
(`WalkOK`) at a user address. -/
theorem vspace.unmap_page.vs5 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (size : capability.FrameSize) (asid vaddr pptr : U64) {V : U64 → Prop} (hV : VsOK Ω Sg V)
    (hv : vaddr.val < 2 ^ 47)
    (hw : vspace.find_vspace_for_asid st s asid ⦃ r => ∀ r1, r = .Ok r1 → WalkOK st V s r1 ⦄) :
    vspace.unmap_page st ar s a size asid vaddr pptr ⦃ r => WritesIn st s r.1 V ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have i1 := hA.invalidate_page
  unfold vspace.unmap_page
  refine WP.spec_bind hw fun r hr => ?_
  rcases r with r1 | e
  · have hk := hr r1 rfl vaddr hv
    step with P0.layout.paddr.p0 as ⟨pa, _⟩
    cases size
    · refine WP.spec_bind hk.1 fun r2 hr2 => ?_
      rcases r2 with x | e
      · have hx := hr2 x rfl
        repeat step
        try split
        all_goals try simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
        all_goals try step*
        all_goals first | exact WritesIn.refl _ _ | (subst_vars; exact writesIn_wr_V hV hx)
      · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
    · refine WP.spec_bind hk.2.1 fun r2 hr2 => ?_
      rcases r2 with x | e
      · have hx := hr2 x rfl
        repeat step
        try split
        all_goals try simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
        all_goals try step*
        all_goals first | exact WritesIn.refl _ _ | (subst_vars; exact writesIn_wr_V hV hx)
      · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
    · refine WP.spec_bind hk.2.2 fun r2 hr2 => ?_
      rcases r2 with x | e
      · have hx := hr2 x rfl
        repeat step
        try split
        all_goals try simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
        all_goals try step*
        all_goals first | exact WritesIn.refl _ _ | (subst_vars; exact writesIn_wr_V hV hx)
      · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)

namespace X5

/-- **`DelGapsAt` with the user-address fact** (`va`, read with the cap from its slot) and the finalisation of
caps that satisfy it (`fin`); otherwise `DelGapsAt`'s fields. -/
structure DelGapsAt (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (s0 : S) : Prop where
  cap : ∀ (Ac : Set U64) (s : S) (x : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    SlotW T Ω Sg x → obj.Slot.cap st x s ⦃ c => DelCapOK T Ω Sg H Rp Nt c ∧ FinPl st Scs s c ⦄
  va : ∀ (Ac : Set U64) (s : S) (x : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    SlotW T Ω Sg x → obj.Slot.cap st x s ⦃ c => VaOK c ⦄
  fin : ∀ (Ac : Set U64) (s : S) (a : A) (c : capability.Cap) (fin : Bool),
    Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s → DelCapOK T Ω Sg H Rp Nt c → FinPl st Scs s c → VaOK c →
    objects.finalise_cap st ar s a c fin false ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧
      DelCapOK T Ω Sg H Rp Nt r.1.1 ∧ DelCapOK T Ω Sg H Rp Nt r.1.2 ⦄
  deferred : ∀ (Ac : Set U64) (s : S) (a : A) (x : U64), Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s →
    SlotW T Ω Sg x → cdt.delete_deferred st ar s a x ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄
  empty : ∀ (Ac : Set U64) (s : S) (a : A) (x : U64) (c : capability.Cap),
    Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s → SlotW T Ω Sg x → DelCapOK T Ω Sg H Rp Nt c →
    cdt.empty_slot st ar s a x c ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ⦄
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
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : SlotW T Ω Sg x) :
    cdt.finalise_slot_immediate st ar s a x ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧
      ∀ v, r.1 = .Ok v → DelCapOK T Ω Sg H Rp Nt v.cleanup ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.finalise_slot_immediate cdt.finalise_slot_immediate_loop
  apply loop.spec_decr_nat (measure := fun y => y.2.2.val)
    (inv := fun y => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 y.1)
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
    refine WP.spec_bind (WP.spec_and (G.cap Acx s1 x h1.fr hbx hx) (G.va Acx s1 x h1.fr hbx hx))
      fun c ⟨⟨hc, hpl⟩, hva⟩ => ?_
    refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h1, fun v hv => by cases hv; exact DelCapOK.null⟩
    refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s1 x c hS) fun fin _ => ?_
    refine WP.spec_bind (G.fin Ac s1 a1 c fin h1 hc hpl hva) ?_
    rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨h2', hrem, hcl⟩
    try simp only [uncurry_apply_pair, WP.uncurry'_pair]
    refine WP.spec_bind (cdt.cap_removable.zombie rem x) fun br hbr => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h2', fun v hv => by cases hv; exact hcl⟩
    rename_i hbr0
    have hbr' := hbr (by simpa using hbr0)
    refine WP.spec_bind (obj.Slot.set_cap.capw (c := rem) (s := s2) hx) fun s2' w2 => ?_
    have h2 := h2'.capw w2 fun _ hb => hb
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
      have SC : ∀ c', obj.Slot.set_cap st x s3 c' ⦃ s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := fun c' =>
        WP.spec_mono (obj.Slot.set_cap.capw hx) fun s' w => h3.capw w fun _ hb => hb
      refine WP.spec_bind (Pₘ := fun r : S × A => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1) ?_ ?_
      · split
        all_goals try exact (WP.spec_ok _).2 h3
        split
        · split
          · refine WP.spec_bind (Pₘ := fun s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s') ?_
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
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : SlotW T Ω Sg x) :
    cdt.delete st ar s a x true ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄ := by
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
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : SlotW T Ω Sg x) :
    cdt.revoke st ar s a x ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.revoke cdt.revoke_loop
  apply loop.spec_decr_nat (measure := fun y => y.2.2.val)
    (inv := fun y => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 y.1)
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
    obtain ⟨-, Acx, hbx, -, -, -, -, -⟩ := h1'
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
  WP.spec_bind (Cur0.restart D) fun s1 h1 => WP.spec_mono (cdt.delete.cur0 hA G h1 hx) fun r hr => by
    obtain ⟨r', s', a'⟩ := r; exact hr.post

/-- **CNode `Revoke`** from `DelGaps`. -/
theorem cnode_rev {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {s : S} (G : DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s) {a : A} {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {x : U64}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hx : SlotW T Ω Sg x) :
    (do
      let s1 ← sched.set_thread_state st s (L.curW s) sched.TS_RESTART
      cdt.revoke st ar s1 a x) ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ :=
  WP.spec_bind (Cur0.restart D) fun s1 h1 => WP.spec_mono (cdt.revoke.cur0 hA G h1 hx) fun r hr => by
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
  have hvW := hr.2 v rfl
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


/-! ## The placements: `DelPlaceAt` without the walk fields, with root-restricted walks and `va` -/

/-- **The deletion placement facts** (P3's): `DelPlaceAt`'s fields without `pt` / `pd` / `pdpt` (false as stated:
every start word) and with **[J] `walk`**, **[J] `walk0`**, **[J] `va`**. -/
structure DelPlaceAt (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (V : U64 → Prop) (s0 : S) : Prop where
  vs : VsOK Ω Sg V
  cap : ∀ (Ac : Set U64) (s : S) (x : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → SlotW T Ω Sg x →
    obj.Slot.cap st x s ⦃ c => DelCapOK T Ω Sg H Rp Nt c ∧ FinPl st Scs s c ⦄
  /-- **[J] (x86) `va`**: a mapped frame cap, a mapped page table, page directory or PDPT cap in a cap slot names
  an address below `2^47` (`VaOK`; module docstring). -/
  va : ∀ (Ac : Set U64) (s : S) (x : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    SlotW T Ω Sg x → obj.Slot.cap st x s ⦃ c => VaOK c ⦄
  next : ∀ (Ac : Set U64) (s : S) (x : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → SlotW T Ω Sg x →
    obj.Slot.next st x s ⦃ n => n = 0#u64 ∨ SlotW T Ω Sg n ⦄
  prev : ∀ (Ac : Set U64) (s : S) (x : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → SlotW T Ω Sg x →
    obj.Slot.prev st x s ⦃ n => n = 0#u64 ∨ SlotW T Ω Sg n ⦄
  /-- **[J] (x86) `walk`**: the walks from a root the ASID table names at the current state, at a user address,
  give VSpace words (`WalkOK`; module docstring). -/
  walk : ∀ (Ac : Set U64) (s : S) (asid : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    vspace.find_vspace_for_asid st s asid ⦃ r => ∀ r1, r = .Ok r1 → WalkOK st V s r1 ⦄
  /-- **[J] (x86) `walk0`**: the walks at a state inside the decode from a root the ASID table named at the
  decode's start `s0` (FrameBatch's checked root), at a user address, give VSpace words. -/
  walk0 : ∀ (Ac : Set U64) (s : S) (asid : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    vspace.find_vspace_for_asid st s0 asid ⦃ r => ∀ r1, r = .Ok r1 → WalkOK st V s r1 ⦄
  pool : ∀ (Ac : Set U64) (s : S) (asid i : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    vspace.asid_table st s i ⦃ pool => pool ≠ 0#u64 →
      V (core.num.U64.wrapping_add pool (core.num.U64.wrapping_mul (asid &&& 511#u64) 8#u64)) ⦄
  aset : ∀ (Ac : Set U64) (s : S) (hi : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    vspace.set_asid_table st s hi 0#u64 ⦃ s1 => WritesIn st s s1 V ⦄
  /-- An IRQ's handler slot holds no cap or a notification cap (`deleting_irq_handler`). -/
  irq : ∀ (Ac : Set U64) (s : S) (i : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → i.val < 128 →
    obj.Slot.cap st (irqSlotA (L.ksb s) i) s ⦃ c => c = .Null ∨ ∃ n b0 b1 b2, c = .Notification n b0 b1 b2 ⦄
  /-- The PML4 entries of an ASID's root are VSpace words (`unmap_pdpt`). -/
  pml : ∀ (Ac : Set U64) (s : S) (asid : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    vspace.find_vspace_for_asid st s asid ⦃ r => ∀ r1, r = .Ok r1 → ∀ i : U64,
      V (core.num.U64.wrapping_add r1 (core.num.U64.wrapping_mul (i &&& 511#u64) 8#u64)) ⦄

/-- `DelPlaceAt` at every decode start reached from a `P3Ok` entry. -/
def DelPlace (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (V : U64 → Prop) (P3Ok : S → Prop) : Prop :=
  ∀ s0, EntAt st P3Ok s0 → DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0

set_option maxHeartbeats 2000000 in
/-- **The VSpace kinds** (`fin_vs`) from the root-restricted walks (`walk`) and the cap's user address
(`VaOK`). -/
theorem fin_vs {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 s : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) {a : A} {c : capability.Cap} {fin : Bool}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hva : VaOK c)
    (hc : (∃ x y z w, c = .PageTable x y z w) ∨ (∃ x y z w m asid vaddr, c = .Frame x y z w m false asid vaddr) ∨
      (∃ x y z, c = .Pml4 x y z) ∨ (∃ x y, c = .AsidPool x y) ∨ (∃ x y z w, c = .PageDirectory x y z w) ∨
      (∃ x y z w, c = .Pdpt x y z w)) :
    objects.finalise_cap st ar s a c fin false ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧
      DelCapOK T Ω Sg H Rp Nt r.1.1 ∧ DelCapOK T Ω Sg H Rp Nt r.1.2 ⦄ := by
  have hb := h.bxi
  obtain ⟨Ac', hb⟩ := hb
  have W : ∀ (m : Result (S × A)), m ⦃ r => WritesIn st s r.1 V ⦄ →
      (do let (s1, a1) ← m; ok ((capability.Cap.Null, capability.Cap.Null), s1, a1)) ⦃ r =>
        Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧ DelCapOK T Ω Sg H Rp Nt r.1.1 ∧
        DelCapOK T Ω Sg H Rp Nt r.1.2 ⦄ := fun m hm =>
    WP.spec_bind hm fun r hr => by
      obtain ⟨s1, a1⟩ := r
      exact (WP.spec_ok _).2 ⟨h.vs P.vs hr, DelCapOK.null, DelCapOK.null⟩
  have K : (ok ((capability.Cap.Null, capability.Cap.Null), s, a) : Result _) ⦃ r =>
      Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧ DelCapOK T Ω Sg H Rp Nt r.1.1 ∧
      DelCapOK T Ω Sg H Rp Nt r.1.2 ⦄ := (WP.spec_ok _).2 ⟨h, DelCapOK.null, DelCapOK.null⟩
  have WK : ∀ asid, vspace.find_vspace_for_asid st s asid ⦃ r => ∀ r1, r = .Ok r1 → WalkOK st V s r1 ⦄ :=
    fun asid => P.walk Ac' s asid h.fr hb
  rcases hc with ⟨x, y, z, w, rfl⟩ | ⟨x, y, z, w, m, asid, vaddr, rfl⟩ | ⟨x, y, z, rfl⟩ | ⟨x, y, rfl⟩ |
    ⟨x, y, z, w, rfl⟩ | ⟨x, y, z, w, rfl⟩
  · simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok]
    split
    · split
      · rename_i hm
        exact W _ (vspace.unmap_page_table.vs5 hA s a z w x P.vs (hva.2.1 x z w (by rw [hm])) (WK z))
      · exact K
    · exact K
  · simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok, Bool.false_eq_true, ↓reduceIte]
    apply WP.spec_bind (Pₘ := fun r => WritesIn st s r.1 V)
    · split
      · split
        · rename_i hm _
          have hv : vaddr.val < 2 ^ 47 := hva.1 x y z w false asid vaddr (by rw [hm])
          exact vspace.unmap_page.vs5 hA s a y asid vaddr x P.vs hv (WK asid)
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
      · exact W _ (vspace.delete_asid.vs hA s a z x P.vs fun i => P.pool Ac' s z i h.fr hb)
      · exact K
    · exact K
  · simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok]
    split
    · exact W _ (vspace.delete_asid_pool.vs hA s a y x fun hi => P.aset Ac' s hi h.fr hb)
    · exact K
  · simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok]
    split
    · split
      · rename_i hm
        exact W _ (vspace.unmap_page_directory.vs5 hA s a z w x P.vs (hva.2.2.1 x z w (by rw [hm])) (WK z))
      · exact K
    · exact K
  · simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok]
    split
    · split
      · exact W _ (vspace.unmap_pdpt.vs hA s a z w x P.vs (P.pml Ac' s z h.fr hb))
      · exact K
    · exact K

set_option maxHeartbeats 1000000 in
/-- **`empty_slot`** of a cap slot, its cleanup cap typed. -/
theorem cdt.empty_slot.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
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
        h.capw w fun _ hb => hb
  refine WP.spec_bind (Pₘ := fun s2 => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s2) ?_ fun s2 h2 => ?_
  · split
    · exact (WP.spec_ok _).2 h1
    · rename_i hn0
      have hnW := hnx.resolve_left (by simpa using hn0)
      refine WP.spec_bind (obj.Slot.set_prev.capw hnW) fun s3 w3 => ?_
      have h3 := h1.capw w3 fun _ hb => hb
      refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st nx s3 hS) fun nfb _ => ?_
      split <;> exact WP.spec_mono (obj.Slot.set_first_badged.capw hnW) fun s' w => h3.capw w fun _ hb => hb
  refine WP.spec_bind (obj.Slot.clear.capw hx) fun s3 w3 => ?_
  exact objects.post_cap_deletion.cur0 hA (h2.capw w3 fun _ hb => hb) hc

set_option maxHeartbeats 2000000 in
/-- **`cdt.swap`** of two cap slots. -/
theorem cdt.swap.cur0 {V : U64 → Prop} {s0 s : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0)
    {c1 c2 : capability.Cap} {x1 x2 : U64} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (h1 : SlotW T Ω Sg x1) (h2 : SlotW T Ω Sg x2) :
    cdt.swap st s c1 x1 c2 x2 ⦃ s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.swap
  refine WP.spec_bind (h.cw (obj.Slot.set_cap.capw h1)) fun sa ha => ?_
  refine WP.spec_bind (ha.cw (obj.Slot.set_cap.capw h2)) fun sb hb => ?_
  obtain ⟨Acb, hbb⟩ := hb.bxi
  refine WP.spec_bind (P.prev Acb sb x1 hb.fr hbb h1) fun p1 hp1 => ?_
  refine WP.spec_bind (P.next Acb sb x1 hb.fr hbb h1) fun n1 hn1 => ?_
  refine WP.spec_bind (P0.obj.Slot.revocable.p0 st x1 sb hS) fun r1 _ => ?_
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st x1 sb hS) fun f1 _ => ?_
  simp only [obj.Slot.is_null, bind_ok]
  refine WP.spec_bind (Pₘ := fun s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s') ?_ fun sc hc => ?_
  · split
    · exact (WP.spec_ok _).2 hb
    · rename_i e; exact hb.cw (obj.Slot.set_next.capw (hp1.resolve_left (by simpa using e)))
  refine WP.spec_bind (Pₘ := fun s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s') ?_ fun sd hd => ?_
  · split
    · exact (WP.spec_ok _).2 hc
    · rename_i e; exact hc.cw (obj.Slot.set_prev.capw (hn1.resolve_left (by simpa using e)))
  obtain ⟨Acd, hbd⟩ := hd.bxi
  refine WP.spec_bind (P.prev Acd sd x2 hd.fr hbd h2) fun p2 hp2 => ?_
  refine WP.spec_bind (P.next Acd sd x2 hd.fr hbd h2) fun n2 hn2 => ?_
  refine WP.spec_bind (P0.obj.Slot.revocable.p0 st x2 sd hS) fun r2 _ => ?_
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st x2 sd hS) fun f2 _ => ?_
  refine WP.spec_bind (hd.cw (obj.Slot.set_prev.capw h1)) fun s5 h5 => ?_
  refine WP.spec_bind (h5.cw (obj.Slot.set_next_flags.capw h1)) fun s6 h6 => ?_
  refine WP.spec_bind (h6.cw (obj.Slot.set_prev.capw h2)) fun s7 h7 => ?_
  refine WP.spec_bind (h7.cw (obj.Slot.set_next_flags.capw h2)) fun s12 h12 => ?_
  refine WP.spec_bind (Pₘ := fun s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s') ?_ fun s13 h13 => ?_
  · split
    · exact (WP.spec_ok _).2 h12
    · rename_i e; exact h12.cw (obj.Slot.set_next.capw (hp2.resolve_left (by simpa using e)))
  split
  · exact (WP.spec_ok _).2 h13
  · rename_i e; exact h13.cw (obj.Slot.set_prev.capw (hn2.resolve_left (by simpa using e)))

theorem cdt.cap_swap_for_delete.cur0 {V : U64 → Prop} {s0 s : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0)
    {x1 x2 : U64} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (h1 : SlotW T Ω Sg x1) (h2 : SlotW T Ω Sg x2) :
    cdt.cap_swap_for_delete st s x1 x2 ⦃ s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
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
    {s0 s : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (F : FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z VaOK s0)
    {a : A} {x : U64} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : SlotW T Ω Sg x) :
    cdt.finalise_slot_deferred st ar s a x ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧
      ∀ v, r.1 = .Ok v → DelCapOK T Ω Sg H Rp Nt v.cleanup ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.finalise_slot_deferred cdt.finalise_slot_deferred_loop
  apply loop.spec_decr_nat (measure := fun y => y.2.2.val)
    (inv := fun y => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 y.1)
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
    refine WP.spec_bind (WP.spec_and (P.cap Acx s1 x h1.fr hbx hx) (P.va Acx s1 x h1.fr hbx hx))
      fun c ⟨⟨hc, hpl⟩, hva⟩ => ?_
    refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h1, fun v hv => by cases hv; exact DelCapOK.null⟩
    refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s1 x c hS) fun fin _ => ?_
    refine WP.spec_bind (F Ac s1 a1 c fin h1 hc hpl hva) ?_
    rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨h2', hrem, hcl⟩
    try simp only [uncurry_apply_pair]
    refine WP.spec_bind (P0.cdt.cap_removable.p0 rem x) fun br _ => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h2', fun v hv => by cases hv; exact hcl⟩
    refine WP.spec_bind (h2'.cw (obj.Slot.set_cap.capw (c := rem) hx)) fun s2 h2 => ?_
    refine WP.spec_bind (P0.cdt.cap_cyclic_zombie.p0 rem x) fun bz _ => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h2, fun v hv => by cases hv; exact hcl⟩
    refine WP.spec_bind (Pₘ := fun s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s') ?_ fun s3 h3 => ?_
    · split
      all_goals try exact (WP.spec_ok _).2 h2
      rename_i zp zt zn
      exact cdt.cap_swap_for_delete.cur0 P h2 (hrem.2.2.2.2.1 zp zt zn rfl).1 hx
    dtail
  · exact h

/-- **`delete_deferred`** of a cap slot. -/
theorem cdt.delete_deferred.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 s : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (F : FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z VaOK s0)
    {a : A} {x : U64} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : SlotW T Ω Sg x) :
    cdt.delete_deferred st ar s a x ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄ := by
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

/-- **The IRQ handler kind's finalisation** (`FinGaps.irq`), from `DelPlace`. -/
theorem finGap_irq {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) :
    FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (fun c => ∃ x1, c = .IrqHandler x1) s0 := by
  have hS : P0.StoreTotal st := L.total
  intro Ac s a c fin h hc _ ⟨irq, e⟩
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
      have hW := irq_slotW hb hi
      unfold cdt.delete_one
      refine WP.spec_bind (WP.spec_and (P.irq Ac' s irq h.fr hb hi) (P.cap Ac' s _ h.fr hb hW)) fun c ⟨hc', hcd⟩ => ?_
      refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
      split
      · exact (WP.spec_ok _).2 h
      refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s _ c hS) fun f _ => ?_
      rcases hc' with rfl | ⟨n, b0, b1, b2, rfl⟩
      · simp [objects.finalise_cap_object]
        exact cdt.empty_slot.cur0 hA P h hW DelCapOK.null
      · obtain ⟨hn, hH⟩ := hcd.1.1.2.1 n b0 b1 b2 rfl
        refine WP.spec_bind (fin_ntfn_obj.cur0 (ar := ar) (a := a) (fin := f) (b0 := b0) (b1 := b1) (b2 := b2) h hn hH) ?_
        rintro ⟨_, s1, a1⟩ ⟨-, h1⟩
        exact cdt.empty_slot.cur0 hA P h1 hW DelCapOK.null
    · exact (WP.spec_ok _).2 h
  rintro ⟨s1, a1⟩ h1
  simp only at h1 ⊢
  unfold objects.finalise_cap_object
  dsimp only
  split
  · exact (WP.spec_ok _).2 ⟨h1, DelCapOK.null, hc⟩
  · exact (WP.spec_ok _).2 ⟨h1, DelCapOK.null, DelCapOK.null⟩

/-- **Every cap kind's finalisation**, for caps with a user address (`VaOK`), from `FinKindsAt`. -/
theorem fin_all {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (G : FinKindsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) :
    FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z VaOK s0 := by
  intro Ac s a c fin h hc hpl hva
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
  | PageTable => exact fin_vs hA P h hva (Or.inl ⟨_, _, _, _, rfl⟩)
  | Pml4 => exact fin_vs hA P h hva (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl⟩)))
  | AsidPool => exact fin_vs hA P h hva (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))))
  | Frame x1 x2 x3 x4 x5 e x6 x7 =>
    cases e
    · exact fin_vs hA P h hva (Or.inr (Or.inl ⟨_, _, _, _, _, _, _, rfl⟩))
    · exact G.arch _ _ _ _ _ h hc hpl (Or.inr (Or.inr ⟨_, _, _, _, _, _, _, rfl⟩))
  | Endpoint => exact G.ep _ _ _ _ _ h hc hpl ⟨_, _, _, _, _, _, rfl⟩
  | Notification => exact G.ntfn _ _ _ _ _ h hc hpl ⟨_, _, _, _, rfl⟩
  | Reply => exact G.reply _ _ _ _ _ h hc hpl ⟨_, _, rfl⟩
  | SchedContext => exact G.sc _ _ _ _ _ h hc hpl ⟨_, _, rfl⟩
  | Thread => exact G.thread _ _ _ _ _ h hc hpl ⟨_, rfl⟩
  | IrqHandler => exact G.irq _ _ _ _ _ h hc hpl ⟨_, rfl⟩
  | PageDirectory => exact fin_vs hA P h hva (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl⟩)))))
  | Pdpt => exact fin_vs hA P h hva (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, _, _, rfl⟩)))))
  | Vcpu => exact G.arch _ _ _ _ _ h hc hpl (Or.inl ⟨_, rfl⟩)
  | Ept => exact G.arch _ _ _ _ _ h hc hpl (Or.inr (Or.inl ⟨_, _, _, _, _, rfl⟩))
  | IoPort => exact G.ioPort _ _ _ _ _ h hc hpl ⟨_, _, _, rfl⟩

/-! ## `empty_slot` and `post_cap_deletion` -/


/-- **`X5.DelGapsAt`, discharged** from the placement and the named finalisations. -/
theorem delGaps_of {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (G : FinKindsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) :
    DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0 where
  cap := P.cap
  va := P.va
  fin Ac s a c fin h hc hpl hva := fin_all hA P G Ac s a c fin h hc hpl hva
  deferred _ _ _ _ h hx := cdt.delete_deferred.cur0 hA P (fin_all hA P G) h hx
  empty _ _ _ _ _ h hx hc := cdt.empty_slot.cur0 hA P h hx hc
  next := P.next

/-- `FinGapsAt` with the proved kinds gives every kind (`FinKindsAt`), the IRQ handler kind from
`X5.DelPlaceAt` (`X5.finGap_irq`). -/
theorem FinGapsAt.kinds {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop} {s0 : S}
    (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (G : FinGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) :
    FinKindsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0 :=
  ⟨finGap_ep.at s0, finGap_ntfn.at s0, (finGap_reply hA).at s0, (finGap_sc hA).at s0, (finGap_thread hA).at s0,
    finGap_irq hA P, G.ioPort, G.arch⟩

set_option hygiene false in
/-- An error leaf with the state unchanged. -/
local macro "errI" : tactic => `(tactic| first
  | exact D.err _
  | exact (WP.spec_ok _).2 (D.err _)
  | (simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok,
      error.illegal, error.truncated, error.range, error.invalid_cap, error.invalid_arg]
     first | exact D.err _ | exact (WP.spec_ok _).2 (D.err _)))

/-- **`delete_one` of an IRQ's handler slot**: no cap, or a notification
cap's finalisation and the slot's emptying (as `finGap_irq`). -/
theorem cdt.delete_one.irq_cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 s : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) {a : A} {irq : U64}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hi : irq.val < 128) :
    cdt.delete_one st ar s a (irqSlotA (L.ksb s) irq) ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  obtain ⟨Ac', hb⟩ := h.bxi
  have hW := irq_slotW hb hi
  unfold cdt.delete_one
  refine WP.spec_bind (WP.spec_and (P.irq Ac' s irq h.fr hb hi) (P.cap Ac' s _ h.fr hb hW)) fun c ⟨hc', hcd⟩ => ?_
  refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
  split
  · exact (WP.spec_ok _).2 h
  refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s _ c hS) fun f _ => ?_
  rcases hc' with rfl | ⟨n, b0, b1, b2, rfl⟩
  · simp [objects.finalise_cap_object]
    exact cdt.empty_slot.cur0 hA P h hW DelCapOK.null
  · obtain ⟨hn, hH⟩ := hcd.1.1.2.1 n b0 b1 b2 rfl
    refine WP.spec_bind (fin_ntfn_obj.cur0 (ar := ar) (a := a) (fin := f) (b0 := b0) (b1 := b1) (b2 := b2) h hn hH) ?_
    rintro ⟨_, s1, a1⟩ ⟨-, h1⟩
    exact cdt.empty_slot.cur0 hA P h1 hW DelCapOK.null

set_option maxHeartbeats 4000000 in
/-- **`decode_irq_handler`** (Ack, SetIRQHandler, ClearIRQHandler) keeps the
invariants. -/
theorem interrupt.decode_irq_handler.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok) {V : U64 → Prop} {s : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s)
    {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) (lbl irq : U64)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hE : EntAt st P3Ok s) (hi : irq.val < 128)
    (hx : ∀ sl ∈ extra.val, sl ≠ 0#u64 → CapW T Ω Sg sl) :
    interrupt.decode_irq_handler st ar s a lbl irq extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold interrupt.decode_irq_handler
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e
  split
  · refine WP.spec_bind (Cur0.restart D) fun s1 h1 => ?_
    refine WP.spec_bind (hA.mask_irq a irq false) fun a1 _ => ?_
    exact (WP.spec_ok _).2 h1.post
  split
  · have hl0 : (0#usize).val < extra.val.length := by rw [extra.property]; simp
    refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec extra 0#usize hl0) fun sl hsl => ?_
    have hmem : sl ∈ extra.val := hsl ▸ List.getElem_mem hl0
    simp only [obj.Slot.is_null, bind_ok]
    split
    · errI
    rename_i h0
    have hne : sl ≠ 0#u64 := by simpa using h0
    refine WP.spec_bind (P0.obj.Slot.cap.p0 st sl s hS) fun c _ => ?_
    rcases c with _ | _ | _ | ⟨n, b0, b1, b2⟩
    all_goals try (simp only [error.invalid_cap, bind_ok]; exact (WP.spec_ok _).2 (D.err _))
    all_goals try errI
    try dsimp only
    split
    swap
    · errI
    refine WP.spec_bind (Cur0.restart D) fun s1 h1 => ?_
    refine WP.spec_bind (interrupt.irq_slot.val s1 irq) fun isl e => ?_
    subst e
    obtain ⟨Ac1, hb1⟩ := h1.bxi
    have hW := (irq_slotW hb1 hi).capw0
    refine WP.spec_bind (cdt.delete_one.irq_cur0 hA P h1 hi) ?_
    rintro ⟨s2, a1⟩ h2
    try simp only [uncurry_apply_pair]
    obtain ⟨Ac2, hb2⟩ := h2.bxi
    refine WP.spec_bind (Pₘ := fun s3 => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s s3) ?_
      fun s3 h3 => (WP.spec_ok _).2 h3.post
    unfold cdt.insert
    refine WP.spec_bind (P0.obj.Slot.cap.p0 st sl s2 hS) fun c0 _ => ?_
    exact WP.spec_mono (C.ins Ac2 s s2 _ c0 sl _ hE h2.fr hb2 (hx sl hmem hne) hW) fun s3 w => h2.capw w fun _ hb => hb
  split
  · refine WP.spec_bind (Cur0.restart D) fun s1 h1 => ?_
    refine WP.spec_bind (interrupt.irq_slot.val s1 irq) fun isl e => ?_
    subst e
    refine WP.spec_bind (cdt.delete_one.irq_cur0 hA P h1 hi) ?_
    rintro ⟨s2, a1⟩ h2
    exact (WP.spec_ok _).2 h2.post
  · errI

/-- **InvGaps' `irqHandler`, discharged** from the CSpace and deletion
placement facts and `IrqPlace`. -/
theorem decGap_irqHandler {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok) {V : U64 → Prop} (P : DelPlace st T Cs Ω H Sg Rp Scs Nt Z V P3Ok)
    (Pl : IrqPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .irqHandler := by
  intro Ac s a lbl len slot cap blk call don fp buf extra hf D _hslot hE
  cases cap <;> simp [capFam] at hf
  rename_i irq
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec as ⟨ct, _⟩
  try dsimp only
  exact interrupt.decode_irq_handler.dec hA C (P s hE) a lbl irq D hE (Pl.irq _ _ _ _ hE D irq rfl)
    (fun sl h1 h2 => SlotW.capw0 (Pl.extra _ _ _ _ hE D sl h1 h2))



end X5

end

end Fl4Proofs.P1
