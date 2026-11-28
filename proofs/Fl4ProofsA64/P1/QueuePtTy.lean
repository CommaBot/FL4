/-
P1 (aarch64, gen 38): **page-table caps** — the `unmap_page_table` walk over the VSpace typing `VsTy`
(QueueVsTy) — and **device frames**, as `Wr0` steps (one `Pt` word written `0`, or nothing), and both as top-level
deletion targets over `JV`.

Source (crates/fl4-core/src/arch/aarch64/vspace.rs):
* `unmap_page_table` (474–517): `find_asid_raw`; a `ROOT_S2` (tag 1) entry goes to `ept::unmap_table` (Stage 2);
  otherwise `root = raw & !ROOT_TAG`; a `ROOT_HIGH` (tag 2) root starts at `table_of(root[511])` with shift 30,
  level 1, any other tag at `root` with shift 39, level 0; the loop (495–508) follows table descriptors
  (`is_table`) while `level < 3` and stops at the slot whose `table_of` is `pt`; that slot is written `0`
  (509–516), then an `Arch` TLB flush. `unmap_page_directory` / `unmap_pdpt` (520–526) are `unmap_page_table`.
* `init_high_vspace` (283–297): a `HighVSpace`'s level-0 entry 511 is a table descriptor of its own level-1 table;
  `unmap_page_table` never targets it (the high walk starts at level 1), `unmap_page` writes only `is_page`
  descriptors (`e & 3 = 1` above level 3, 99–105, 458–462) and the map paths only invalid slots (1136, 1157).
* objects.rs `finalise_cap_object`, `Frame` arm: a device frame, final, additionally runs `retire_dma_frame`, which
  writes only `Arch` state.

**`PtTy kb Pp Tb Lv s`** = `VsTy` + `tag` (every nonzero entry of a pool of `Pp` has tag 0 or 2: no Stage-2 /
tag-3 entry) + `high` (a tag-2 entry's root has entry 511 a table descriptor). **`VsS1`** (every nonzero pool
entry has tag 0) is kept by every `VsZ` step (`VsS1.keepZ`) and gives `PtTy` with `VsTy` (`PtTy.of_s1`).

* **`vspace.unmap_page_table_loop.z`** (invariant `UpI`: below level 3 the table is a table of `Tb` at its level):
  a found slot is a `PtW Tb` word; **`vspace.unmap_page_table.z`** (and `unmap_page_directory.z`, `unmap_pdpt.z`):
  a `Wr0 Tb` step at a `PtTy` state.
* `fin_pt.z`, `fin_pd.z`, `fin_pdpt.z` (any finality, mapped or not), **`fin_dframe.z`** (a non-EPT device frame).
* Tops over `JV`: **`finJV_ptP`** / **`cdt.delete.ptP`** (`PtTy` at the deletion's start state),
  **`finJV_dframeP`** / **`cdt.delete.dframeP`** (QueueVsPt's `PtWalk` at the start state).

Case hypotheses (facts of the deletion's start state or state-free): `PtTy (ks) Pp Tb Lv s`, `Tb ⊆ Pt`, QueueVsPt's
`PtOK`. Is `PtTy` true on reachable states? `VsTy`: QueueVsTy's docstring. `tag`: pool entries are written only by
`assign` with tag 0 (`Pml4`), 1 (`Ept`) or 2 (`HighVSpace`) — so `tag` restricts to states whose pools hold no
Stage-2 VSpace (the EPT branch is not covered); `high`: above. No named premise; new definitions and theorems only.
-/
import Fl4ProofsA64.P1.QueueVsPool
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

local notation "wa" => core.num.U64.wrapping_add

/-! ## The typing -/

/-- **The VSpace typing for page-table unmaps** (module docstring). -/
structure PtTy (st : machine.Store S) [L : LawfulStore st] (kb : U64) (Pp Tb : Set U64) (Lv : U64 → Nat) (s : S) :
    Prop where
  ty : VsTy st kb Pp Tb Lv s
  tag : ∀ p ∈ Pp, ∀ o : U64, o.val < 4096 → o.val % 8 = 0 → L.mem s (wa p o) ≠ 0#u64 →
    (L.mem s (wa p o) &&& 3#u64) = 0#u64 ∨ (L.mem s (wa p o) &&& 3#u64) = 2#u64
  high : ∀ p ∈ Pp, ∀ o : U64, o.val < 4096 → o.val % 8 = 0 → L.mem s (wa p o) ≠ 0#u64 →
    (L.mem s (wa p o) &&& 3#u64) = 2#u64 →
    (L.mem s (wa (L.mem s (wa p o) &&& ~~~3#u64) 4088#u64) &&& 3#u64) = 3#u64

/-- **Stage-1 pools only**: every nonzero entry of a pool of `Pp` has tag 0 (`ROOT_S1`). -/
def VsS1 (st : machine.Store S) [L : LawfulStore st] (Pp : Set U64) (s : S) : Prop :=
  ∀ p ∈ Pp, ∀ o : U64, o.val < 4096 → o.val % 8 = 0 → L.mem s (wa p o) ≠ 0#u64 →
    (L.mem s (wa p o) &&& 3#u64) = 0#u64

/-- `VsS1` along a `VsZ` step. -/
theorem VsS1.keepZ {kb : U64} {Pp Pt : Set U64} {s s' : S} (hPp : Pp ⊆ Pt) (h : VsS1 st Pp s)
    (k : VsZ st kb Pt s s') : VsS1 st Pp s' := fun p hp o ho h8 hne => by
  rcases k _ (Or.inl (ptw_mono hPp ⟨p, hp, o, ho, h8, rfl⟩)) with e | e
  · rw [e] at hne ⊢; exact h p hp o ho h8 hne
  · exact absurd e hne

/-- `VsTy` with Stage-1 pools only is a `PtTy`. -/
theorem PtTy.of_s1 {kb : U64} {Pp Tb : Set U64} {Lv : U64 → Nat} {s : S} (h : VsTy st kb Pp Tb Lv s)
    (h1 : VsS1 st Pp s) : PtTy st kb Pp Tb Lv s :=
  ⟨h, fun p hp o ho h8 hne => Or.inl (h1 p hp o ho h8 hne), fun p hp o ho h8 hne h2 => by
    rw [h1 p hp o ho h8 hne] at h2; exact absurd h2 (by decide)⟩

theorem and_not_of (x M : U64) (h : x &&& M = 0#u64) : x &&& ~~~M = x := by
  rw [UScalar.eq_equiv_bv_eq] at h ⊢
  apply BitVec.eq_of_getLsbD_eq; intro i
  have h1 := congrArg (fun x => BitVec.getLsbD x i) h
  simp only [UScalar.bv_and, UScalar.bv_not, BitVec.getLsbD_and, BitVec.getLsbD_not] at h1 ⊢
  revert h1
  cases x.bv.getLsbD i <;> cases M.bv.getLsbD i <;> (try simp) <;> omega

theorem rs2 : vspace.ROOT_S2 = 1#u64 := by unfold vspace.ROOT_S2; rfl

/-! ## The walk -/

/-- The loop invariant of `unmap_page_table_loop`: below level 3 the table is a table of `Tb` at its level. -/
abbrev UpI (Tb : Set U64) (Lv : U64 → Nat) (x : U64 × U64 × U64) : Prop :=
  x.2.2.val ≤ 3 ∧ (x.2.2.val < 3 → x.1 ∈ Tb ∧ Lv x.1 = x.2.2.val)

set_option maxHeartbeats 2000000 in
/-- **The `unmap_page_table` walk stays in `Tb`**: a found slot is a `PtW Tb` word. -/
theorem vspace.unmap_page_table_loop.z {kb : U64} {Pp Tb : Set U64} {Lv : U64 → Nat} {s : S}
    (h : VsTy st kb Pp Tb Lv s) (vaddr pt table shift level : U64) (hi : UpI Tb Lv (table, shift, level)) :
    vspace.unmap_page_table_loop st s vaddr pt table shift level ⦃ r => ∀ sl, r = some sl → PtW Tb sl ⦄ := by
  unfold vspace.unmap_page_table_loop
  apply loop.spec_decr_nat (measure := fun x => 3 - x.2.2.val) (inv := UpI Tb Lv)
  · rintro ⟨t, sh, lv⟩ ⟨hl3, hT⟩
    simp only at hl3 hT
    dsimp only
    unfold vspace.unmap_page_table_loop.body
    split
    · rename_i hlt
      have hlt' : lv.val < 3 := by first | simpa using hlt | scalar_tac
      obtain ⟨ht, hlv⟩ := hT hlt'
      refine WP.spec_bind (vspace.entry_addr.off t vaddr sh) fun sl hsl => ?_
      obtain ⟨o, ho, h8, e⟩ := hsl
      subst e
      rw [L.read_eq, bind_ok]
      refine WP.spec_bind (vspace.is_table.tag _ sh) fun b hb => ?_
      split
      · rename_i hbt
        obtain ⟨hT', hL'⟩ := h.desc t ht (by omega) o ho h8 (hb hbt)
        simp only [lift, bind_ok, vspace.table_of, layout.pptr]
        split
        · exact (WP.spec_ok _).2 fun sl e' => by cases e'; exact ⟨t, ht, o, ho, h8, rfl⟩
        · try simp only [lift, bind_ok]
          step as ⟨lv1, hlv1⟩
          try simp only [lift, bind_ok]
          try rw [WP.spec_ok]
          try dsimp only
          refine ⟨?_, fun _ => ⟨hT', ?_⟩, ?_⟩
          · omega
          · rw [hL', hlv]; omega
          · omega
      · exact (WP.spec_ok _).2 fun sl e' => by cases e'
    · exact (WP.spec_ok _).2 fun sl e' => by cases e'
  · exact hi

set_option maxHeartbeats 4000000 in
/-- **`unmap_page_table` at a `PtTy` state**: unchanged, or one `PtW Tb` word written `0`. -/
theorem vspace.unmap_page_table.z {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {kb : U64}
    {Pp Tb : Set U64} {Lv : U64 → Nat} {s : S} (h : PtTy st kb Pp Tb Lv s) (hk : L.ksb s = kb) (a : A)
    (asid vaddr pt : U64) :
    vspace.unmap_page_table st ar s a asid vaddr pt ⦃ r => Wr0 st Tb s r.1 ⦄ := by
  unfold vspace.unmap_page_table
  refine WP.spec_bind (vspace.find_asid_raw.ty h.ty hk asid) fun r hr => ?_
  rcases r with r1 | e
  · obtain ⟨p, hp, o, ho, h8, er, hr0⟩ := hr r1 rfl
    have hpl := h.ty.pool p hp o ho h8 (by rw [← er]; exact hr0)
    have htg := h.tag p hp o ho h8 (by rw [← er]; exact hr0)
    have hhi := h.high p hp o ho h8 (by rw [← er]; exact hr0)
    rw [← er] at hpl htg hhi
    simp only [lift, bind_ok, rtag, rs2, rhigh]
    split
    · rename_i h1
      exfalso
      rcases htg with e | e <;> rw [e] at h1 <;> exact absurd h1 (by decide)
    · refine WP.spec_bind (Pₘ := fun x : U64 × U64 × U64 => UpI Tb Lv x) ?_ ?_
      · split
        · rename_i h2
          obtain ⟨hrT, hr0'⟩ := hpl.2 h2
          have he := hhi h2
          step as ⟨i1, hi1⟩
          have e1 : i1 = 4088#u64 := UScalar.eq_of_val_eq (by scalar_tac)
          subst e1
          simp only [lift, bind_ok, L.read_eq, vspace.table_of, layout.pptr]
          obtain ⟨hT1, hL1⟩ := h.ty.desc _ hrT (by omega) 4088#u64 (by simp) (by simp) he
          rw [WP.spec_ok]
          refine ⟨by simp, fun _ => ⟨hT1, ?_⟩⟩
          simp only; rw [hL1, hr0']; simp
        · rename_i h2
          have h0 : (r1 &&& 3#u64) = 0#u64 := htg.resolve_right h2
          rw [WP.spec_ok]
          refine ⟨by simp, fun _ => ?_⟩
          simp only
          rw [and_not_of r1 3#u64 h0]
          obtain ⟨hT0, hL0⟩ := hpl.1 h0
          exact ⟨hT0, by rw [hL0]; simp⟩
      · rintro ⟨t, sh, lv⟩ hi
        try dsimp only
        refine WP.spec_bind (vspace.unmap_page_table_loop.z h.ty vaddr pt t sh lv hi) fun found hf => ?_
        rcases found with _ | sl
        · exact (WP.spec_ok _).2 (Wr0.refl _)
        · try dsimp only
          step with LawfulStore.write_spec as ⟨s1, e1⟩
          split
          · refine WP.spec_bind (hA.invalidate_high_vspace a _) fun a1 _ => ?_
            rw [WP.spec_ok, e1]; exact Or.inr ⟨_, hf sl rfl, rfl⟩
          · refine WP.spec_bind (hA.invalidate_asid a asid) fun a1 _ => ?_
            rw [WP.spec_ok, e1]; exact Or.inr ⟨_, hf sl rfl, rfl⟩
  · exact (WP.spec_ok _).2 (Wr0.refl _)

theorem vspace.unmap_page_directory.z {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {kb : U64}
    {Pp Tb : Set U64} {Lv : U64 → Nat} {s : S} (h : PtTy st kb Pp Tb Lv s) (hk : L.ksb s = kb) (a : A)
    (asid vaddr pt : U64) :
    vspace.unmap_page_directory st ar s a asid vaddr pt ⦃ r => Wr0 st Tb s r.1 ⦄ := by
  unfold vspace.unmap_page_directory; exact vspace.unmap_page_table.z hA h hk a asid vaddr pt

theorem vspace.unmap_pdpt.z {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {kb : U64}
    {Pp Tb : Set U64} {Lv : U64 → Nat} {s : S} (h : PtTy st kb Pp Tb Lv s) (hk : L.ksb s = kb) (a : A)
    (asid vaddr pt : U64) :
    vspace.unmap_pdpt st ar s a asid vaddr pt ⦃ r => Wr0 st Tb s r.1 ⦄ := by
  unfold vspace.unmap_pdpt; exact vspace.unmap_page_table.z hA h hk a asid vaddr pt

theorem Wr0.mono {P Q : Set U64} (hPQ : P ⊆ Q) {s s' : S} (h : Wr0 st P s s') : Wr0 st Q s s' := by
  rcases h with e | ⟨b, hb, e⟩
  · exact Or.inl e
  · exact Or.inr ⟨b, ptw_mono hPQ hb, e⟩

/-! ## The finalisers -/

/-- **A page-table cap's finalisation** (any finality, mapped or not) at a `PtTy` state: `(Null, Null)`, a
`Wr0 Tb` step. -/
theorem fin_pt.z {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (ptr : U64) (mapped : Bool) (asid vaddr : U64) (fin : Bool) {kb : U64} {Pp Tb : Set U64} {Lv : U64 → Nat}
    (h : PtTy st kb Pp Tb Lv s) (hk : L.ksb s = kb) :
    objects.finalise_cap_object st ar s a (.PageTable ptr mapped asid vaddr) fin ⦃ r =>
      r.1 = (.Null, .Null) ∧ Wr0 st Tb s r.2.1 ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  split
  · split
    · refine WP.spec_bind (vspace.unmap_page_table.z hA h hk a asid vaddr ptr) ?_
      rintro ⟨s1, a1⟩ w1
      exact (WP.spec_ok _).2 ⟨rfl, w1⟩
    · exact (WP.spec_ok _).2 ⟨rfl, Wr0.refl _⟩
  · exact (WP.spec_ok _).2 ⟨rfl, Wr0.refl _⟩

/-- **A `PageDirectory` cap's finalisation** (as `fin_pt.z`). -/
theorem fin_pd.z {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (ptr : U64) (mapped : Bool) (asid vaddr : U64) (fin : Bool) {kb : U64} {Pp Tb : Set U64} {Lv : U64 → Nat}
    (h : PtTy st kb Pp Tb Lv s) (hk : L.ksb s = kb) :
    objects.finalise_cap_object st ar s a (.PageDirectory ptr mapped asid vaddr) fin ⦃ r =>
      r.1 = (.Null, .Null) ∧ Wr0 st Tb s r.2.1 ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  split
  · split
    · refine WP.spec_bind (vspace.unmap_page_directory.z hA h hk a asid vaddr ptr) ?_
      rintro ⟨s1, a1⟩ w1
      exact (WP.spec_ok _).2 ⟨rfl, w1⟩
    · exact (WP.spec_ok _).2 ⟨rfl, Wr0.refl _⟩
  · exact (WP.spec_ok _).2 ⟨rfl, Wr0.refl _⟩

/-- **A `Pdpt` cap's finalisation** (as `fin_pt.z`). -/
theorem fin_pdpt.z {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (ptr : U64) (mapped : Bool) (asid vaddr : U64) (fin : Bool) {kb : U64} {Pp Tb : Set U64} {Lv : U64 → Nat}
    (h : PtTy st kb Pp Tb Lv s) (hk : L.ksb s = kb) :
    objects.finalise_cap_object st ar s a (.Pdpt ptr mapped asid vaddr) fin ⦃ r =>
      r.1 = (.Null, .Null) ∧ Wr0 st Tb s r.2.1 ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  split
  · split
    · refine WP.spec_bind (vspace.unmap_pdpt.z hA h hk a asid vaddr ptr) ?_
      rintro ⟨s1, a1⟩ w1
      exact (WP.spec_ok _).2 ⟨rfl, w1⟩
    · exact (WP.spec_ok _).2 ⟨rfl, Wr0.refl _⟩
  · exact (WP.spec_ok _).2 ⟨rfl, Wr0.refl _⟩

/-- **A non-EPT device frame's finalisation** (any finality, mapped or not): `(Null, Null)`, a `Wr0` step
(`retire_dma_frame` writes only `Arch` state). -/
theorem fin_dframe.z {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (ptr : U64) (size : capability.FrameSize) (rights : U64) (mapped : Bool) (asid vaddr : U64) (fin : Bool)
    {Pt : Set U64} (hpt : PtWalk st Pt s asid vaddr) :
    objects.finalise_cap_object st ar s a (.Frame ptr size rights true mapped false asid vaddr) fin ⦃ r =>
      r.1 = (.Null, .Null) ∧ Wr0 st Pt s r.2.1 ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  refine WP.spec_bind (Pₘ := fun r : S × A => Wr0 st Pt s r.1) ?_ ?_
  · split
    · split
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact vspace.unmap_page.z hA s a size asid vaddr ptr hpt
      · exact (WP.spec_ok _).2 (Wr0.refl _)
    · exact (WP.spec_ok _).2 (Wr0.refl _)
  rintro ⟨s1, a1⟩ w1
  try dsimp only
  cases fin
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact (WP.spec_ok _).2 ⟨rfl, w1⟩
  · simp only [↓reduceIte]
    exact WP.spec_bind (P0.objects.retire_dma_frame.p0 st ar s1 a1 ptr size L.total hA) fun a2 _ =>
      (WP.spec_ok _).2 ⟨rfl, w1⟩

namespace W7
namespace R
namespace ST

section ptc
variable {OS Vc Ub : Set U64}

/-- **A page-table cap's finalisation over `JV`** (any finality, mapped or not) at a `PtTy` state. -/
theorem finJV_ptP (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {A : Type _} {ar : machine.Arch A}
    (hP : P0.ArchTotal ar) {Pt : Set U64} (hPt : PtOK T Ω Sg OS Vc Pt) {kb : U64} {Pp Tb : Set U64}
    {Lv : U64 → Nat} (hTb : Tb ⊆ Pt) {s0 s : S} (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s)
    (hY : PtTy st kb Pp Tb Lv s) (hk : L.ksb s = kb) {x ptr asid vaddr : U64} {mapped : Bool}
    (hc : obj.Slot.cap st x s = ok (.PageTable ptr mapped asid vaddr)) :
    FinJV st ar T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s x := by
  intro a c fin hc'
  rw [hc] at hc'
  obtain rfl := okinj hc'
  rw [fin_cap_eq_obj (by simp)]
  exact WP.spec_mono (fin_pt.z hP s a ptr mapped asid vaddr fin hY hk) fun r hr =>
    ⟨hr.1, (JV.ptw hO hV hPt h (Wr0.w (fun b hb => (hPt.vs b hb).1) (Wr0.mono hTb hr.2))).1⟩

/-- **The exposed `cdt.delete` of a page-table slot of `OS` keeps `JV`** (`PtTy` at the start state). -/
theorem cdt.delete.ptP {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS)
    (hV : VcOK T Scs Z OS Vc Ub) {Pt : Set U64} (hPt : PtOK T Ω Sg OS Vc Pt) {Pp Tb : Set U64}
    {Lv : U64 → Nat} (hTb : Tb ⊆ Pt) {s0 s : S} {a : A} (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s)
    (hY : PtTy st (L.ksb s) Pp Tb Lv s) {x ptr asid vaddr : U64} {mapped : Bool} (hx : x ∈ OS)
    (hc : obj.Slot.cap st x s = ok (.PageTable ptr mapped asid vaddr)) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  cdt.delete.finJV hO hV h hx (finJV_ptP hO hV hP hPt hTb h hY rfl hc)

/-- **A non-EPT device frame's finalisation over `JV`** (mapped or not, any finality). -/
theorem finJV_dframeP (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {A : Type _} {ar : machine.Arch A}
    (hP : P0.ArchTotal ar) {Pt : Set U64} (hPt : PtOK T Ω Sg OS Vc Pt) {s0 s : S}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) {x ptr rights asid vaddr : U64}
    {size : capability.FrameSize} {mapped : Bool}
    (hc : obj.Slot.cap st x s = ok (.Frame ptr size rights true mapped false asid vaddr))
    (hpt : PtWalk st Pt s asid vaddr) :
    FinJV st ar T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s x := by
  intro a c fin hc'
  rw [hc] at hc'
  obtain rfl := okinj hc'
  rw [fin_cap_eq_obj (by simp)]
  exact WP.spec_mono (fin_dframe.z hP s a ptr size rights mapped asid vaddr fin hpt) fun r hr =>
    ⟨hr.1, (JV.ptw hO hV hPt h (Wr0.w (fun b hb => (hPt.vs b hb).1) hr.2)).1⟩

/-- **The exposed `cdt.delete` of a non-EPT device-frame slot of `OS` keeps `JV`.** -/
theorem cdt.delete.dframeP {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS)
    (hV : VcOK T Scs Z OS Vc Ub) {Pt : Set U64} (hPt : PtOK T Ω Sg OS Vc Pt) {s0 s : S} {a : A}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) {x ptr rights asid vaddr : U64}
    {size : capability.FrameSize} {mapped : Bool} (hx : x ∈ OS)
    (hc : obj.Slot.cap st x s = ok (.Frame ptr size rights true mapped false asid vaddr))
    (hpt : PtWalk st Pt s asid vaddr) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  cdt.delete.finJV hO hV h hx (finJV_dframeP hO hV hP hPt h hc hpt)

end ptc

end ST
end R
end W7

end

end Fl4ProofsA64.P1
