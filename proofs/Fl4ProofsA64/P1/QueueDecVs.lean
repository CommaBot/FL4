/-
P1 (aarch64): InvGaps' `vspace` family — the AArch64 MMU decode (`vspace.decode`,
crates/fl4-core/src/arch/aarch64/vspace.rs:1168–1273, with `decode_frame` 687, `decode_page_map` 731,
`decode_high_page_map` 790, `install_page` 854, `decode_page_flush` 884, `decode_vspace_flush` 923,
`decode_test_and_clear_accessed` 970, `derive_subframe` 1012, `decode_page_table` 1091,
`map_high_page_table` 1149, and the Stage-2 calls `ept::map_frame` / `map_table` / `unmap` / `flush_frame`,
ept.rs:236–368). New A64 proof, not a port: x86_64's Fl4Proofs.P1.QueueDecVs is the 4-level x86 page-table
decode (with FrameBatch, EPT through `EptPlace`).

The work is within `Cur0` after the caller's restart: VSpace words `V` (`VsOK`, `Cur0.vs`), cap-slot words
(`Cur0.capw`), cleared regions (`Cur0.zr`); a TestAndClearAccessed / GetAddress reply is `XS` then the
thread set running.

Named premises (all in `VsPlaceA`, each **[J]**: facts of the reachable states about where the page tables
are, which P1 has no invariant for yet):
* `s1` / `hi` / `s2` / `fr`: the slot `lookup_pt_slot` (`ept::lookup_slot`) finds from a root that
  `check_vspace` / `check_high_vspace` (in the high window only) / `ept::root` / `frame_root` returned is a
  VSpace word (the roots are named by the ASID table; the walks follow only table descriptors the kernel
  wrote, into `PageTable` objects; a high VSpace's level-0 entries other than 511 copy the kernel's TTBR1
  tables, hence the window, and a high walk at a user address `< 2^47` stops at the zero level-0 entry).
  These are narrower than `DelPlaceAt.ptslot` (every root), which is false as stated (a root that is a TCB).
* `fva`: an invoked mapped Stage-1 frame cap's address is a user address or in the high window.
* `pool`: an ASID table entry's pool entries are VSpace words.
* `pgUnmap` / `ptUnmap` / `s2Unmap`: `unmap_page` (at such an address), `unmap_page_table`, `ept::unmap`
  write only VSpace words.
* `tbl`: an invoked PageTable cap's table holds no tracked word (cleared by its unmap, vspace.rs:1101).
* `mkPool` / `aset`: MakePool's untyped page and the ASID table (as x86_64's `VsPlace.pool` / `aset`;
  the untyped page being in `Ω` presumes P3's heap already holds the pool object, the decode being a
  fixed-heap `DecGap`).
* `sub`: the subframe destination slots are cap slots (as x86_64's `VsPlace.sub`).
-/
import Fl4ProofsA64.P1.QueueDecEpt
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {P3Ok : S → Prop}
variable {T Cs Ω : Set U64} {H : Heap} {Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {U Ac : Set U64}

/-- A region holding no word P1 tracks: aligned, not wrapping, its words in `Ω` and off the frame words. -/
def FreeRegion (Ω Sg : Set U64) (p n : U64) : Prop :=
  Aligned p ∧ n.val % 8 = 0 ∧ p.val + n.val ≤ 2 ^ 64 ∧
    ∀ b : U64, p.val ≤ b.val → b.val < p.val + n.val → b ∈ Ω ∧ b ∉ Sg

theorem writesIn_zrV {s : S} {p n : U64} (ha : Aligned p) (hn : n.val % 8 = 0) (hw : p.val + n.val ≤ 2 ^ 64) :
    WritesIn st s (L.zr s p n) (fun b => p.val ≤ b.val ∧ b.val < p.val + n.val) :=
  ⟨L.ksb_zr _ _ _, L.cpu_zr _ _ _, fun b hb hnb => by rw [L.mem_zr _ _ _ _ ha hn hw hb, if_neg hnb]⟩

/-- Clearing a free region. -/
theorem Cur0.zr {s0 s : S} {p n : U64} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hR : FreeRegion Ω Sg p n) :
    Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 (L.zr s p n) :=
  h.capw (writesIn_zrV hR.1 hR.2.1 hR.2.2.1) fun b hb => Or.inr (hR.2.2.2 b hb.1 hb.2)

/-- The `ArmHighVSpace` window (`HIGH_VSPACE_BASE` .. `HIGH_VSPACE_TOP`). -/
def InWin (v : U64) : Prop :=
  fl4_abi.consts.HIGH_VSPACE_BASE.val ≤ v.val ∧ v.val < fl4_abi.consts.HIGH_VSPACE_TOP.val

/-- A user address (TTBR0 half) or one in the high window. -/
def HiOK (v : U64) : Prop := v.val < 2 ^ 47 ∨ InWin v

/-- **The AArch64 VSpace family's placement facts** (see the module docstring; every field [J]). -/
structure VsPlaceA (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (V : U64 → Prop)
    (P3Ok : S → Prop) : Prop where
  vs : VsOK Ω Sg V
  /-- [J] A Stage-1 VSpace root `check_vspace` returns: every walk slot is a VSpace word. -/
  s1 : ∀ (Ac : Set U64) (s : S), EntAt st P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → ∀ vcap arg,
    vspace.check_vspace st s vcap arg ⦃ r => ∀ p, r = .Ok p → ∀ v,
      vspace.lookup_pt_slot st s p.1 v ⦃ lu => V lu.slot ⦄ ⦄
  /-- [J] A high VSpace root `check_high_vspace` returns: walk slots in the window are VSpace words. -/
  hi : ∀ (Ac : Set U64) (s : S), EntAt st P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → ∀ vcap arg,
    vspace.check_high_vspace st s vcap arg ⦃ r => ∀ p, r = .Ok p → ∀ v, InWin v →
      vspace.lookup_pt_slot st s p.1 v ⦃ lu => V lu.slot ⦄ ⦄
  /-- [J] A Stage-2 root `ept::root` returns: walk slots (the arch's IPA size) are VSpace words. -/
  s2 : ∀ (Ac : Set U64) (s : S), EntAt st P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → ∀ vcap arg,
    ept.root st s vcap arg ⦃ r => ∀ p, r = .Ok p → ∀ a, ar.s2_ipa_bits a ⦃ ib => ∀ ipa,
      ept.lookup_slot st s p.1 ipa ib ⦃ lu => V lu.slot ⦄ ⦄ ⦄
  /-- [J] A frame's root `frame_root` returns: walk slots at user or window addresses are VSpace words. -/
  fr : ∀ (Ac : Set U64) (s : S), EntAt st P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → ∀ asid,
    vspace.frame_root st s asid ⦃ r => ∀ p, r = .Ok p → ∀ v, HiOK v →
      vspace.lookup_pt_slot st s p.1 v ⦃ lu => V lu.slot ⦄ ⦄
  /-- [J] An invoked mapped Stage-1 frame cap's address is a user or window address. -/
  fva : ∀ (Ac : Set U64) (s : S) (cap : capability.Cap) (extra : Aeneas.Std.Array obj.Slot 3#usize),
    EntAt st P3Ok s → DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra →
    ∀ fp fsz fr fd fm fa fv, cap = .Frame fp fsz fr fd fm false fa fv → fa ≠ 0#u64 → HiOK fv
  /-- [J] An ASID table entry's pool entries are VSpace words (ASIDPoolAssign's write). -/
  pool : ∀ (Ac : Set U64) (s : S), EntAt st P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → ∀ asid i,
    vspace.asid_table st s i ⦃ pool => pool ≠ 0#u64 →
      V (core.num.U64.wrapping_add pool (core.num.U64.wrapping_mul (asid &&& 511#u64) 8#u64)) ⦄
  /-- [J] `unmap_page` at a user or window address writes only VSpace words. -/
  pgUnmap : ∀ (Ac : Set U64) (s0 s : S), EntAt st P3Ok s0 → Fr0 st T Cs Ω H Sg Scs Z s0 s →
    BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → ∀ (a : A) size asid v pptr, HiOK v →
    vspace.unmap_page st ar s a size asid v pptr ⦃ r => WritesIn st s r.1 V ⦄
  /-- [J] `unmap_page_table` writes only VSpace words. -/
  ptUnmap : ∀ (Ac : Set U64) (s0 s : S), EntAt st P3Ok s0 → Fr0 st T Cs Ω H Sg Scs Z s0 s →
    BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → ∀ (a : A) asid v pt,
    vspace.unmap_page_table st ar s a asid v pt ⦃ r => WritesIn st s r.1 V ⦄
  /-- [J] `ept::unmap` writes only VSpace words. -/
  s2Unmap : ∀ (Ac : Set U64) (s0 s : S), EntAt st P3Ok s0 → Fr0 st T Cs Ω H Sg Scs Z s0 s →
    BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → ∀ (a : A) asid ipa ptr sh b,
    ept.unmap st ar s a asid ipa ptr sh b ⦃ r => WritesIn st s r.1 V ⦄
  /-- [J] An invoked PageTable cap's table holds no tracked word. -/
  tbl : ∀ (Ac : Set U64) (s : S) (cap : capability.Cap) (extra : Aeneas.Std.Array obj.Slot 3#usize),
    EntAt st P3Ok s → DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra → ∀ ptr m asd va,
      cap = .PageTable ptr m asd va → FreeRegion Ω Sg ptr 4096#u64
  /-- [J] MakePool's untyped (its first page is cleared for the pool; x86_64 `VsPlace.pool`). -/
  mkPool : ∀ (Ac : Set U64) (s : S) (cap : capability.Cap) (extra : Aeneas.Std.Array obj.Slot 3#usize),
    EntAt st P3Ok s → DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra → ∀ x ∈ extra.val, x ≠ 0#u64 →
      obj.Slot.cap st x s ⦃ c => ∀ ptr sb fi dev, c = .Untyped ptr sb fi dev → FreeRegion Ω Sg ptr 4096#u64 ⦄
  /-- [J] The ASID table's entries hold no tracked words (MakePool's pool install; x86_64 `VsPlace.aset`). -/
  aset : ∀ (Ac : Set U64) (s0 s : S) (hi v : U64), EntAt st P3Ok s0 → Fr0 st T Cs Ω H Sg Scs Z s0 s →
    BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    vspace.set_asid_table st s hi v ⦃ s1 => WritesIn st s s1 (fun b => b ∈ Ω ∧ b ∉ Sg) ⦄
  /-- [J] The subframe destination slots (x86_64 `VsPlace.sub`). -/
  sub : ∀ (Ac : Set U64) (s : S) (x i d off cnt : U64), EntAt st P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    vspace.subframe_dest st s x i d off cnt ⦃ r => ∀ dst, r = .Ok dst → ∀ j : U64, j.val < cnt.val →
      obj.Slot.index dst (core.num.U64.wrapping_add off j) ⦃ sl => CapW T Ω Sg sl ⦄ ⦄

set_option hygiene false in
/-- An error leaf with the state unchanged. -/
local macro "errV" : tactic => `(tactic| first
  | exact (WP.spec_ok _).2 (D.err _)
  | (simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok,
      error.illegal, error.truncated, error.range, error.invalid_cap, error.invalid_arg, vspace.failed_lookup]
     first | exact D.err _ | exact (WP.spec_ok _).2 (D.err _)))

set_option hygiene false in
/-- The caller (`sched.cur_thread`) named `L.curW s`. -/
local macro "curT" : tactic => `(tactic| (
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e))

theorem inWin_of {v l : U64} (h1 : ¬ v < fl4_abi.consts.HIGH_VSPACE_BASE)
    (h2 : ¬ l ≥ fl4_abi.consts.HIGH_VSPACE_TOP) (h3 : ¬ l < v) : InWin v := by
  unfold InWin; constructor <;> scalar_tac

theorem inWin_of' {v : U64} (h1 : ¬ v < fl4_abi.consts.HIGH_VSPACE_BASE)
    (h2 : ¬ v ≥ fl4_abi.consts.HIGH_VSPACE_TOP) : InWin v := by
  unfold InWin; constructor <;> scalar_tac

/-! ## Descriptor writes -/

/-- A write of a VSpace word keeps `Cur0`. -/
theorem Cur0.wrV {V : U64 → Prop} (hV : VsOK Ω Sg V) {s0 s : S} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    {x : U64} (hx : V x) (v : U64) : st.write s x v ⦃ s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ :=
  WP.spec_mono (LawfulStore.write_spec s x v) fun s' e => by subst e; exact h.vs hV (writesIn_wr_V hV hx)

set_option hygiene false in
/-- The cache maintenance before a descriptor write (arch calls and pure steps only). -/
local macro "copT" : tactic => `(tactic| (repeat' (first
  | exact (WP.spec_ok _).2 trivial
  | exact hA.cache_op _ _ _ _ _ _ _
  | (refine WP.spec_bind (shl_and63u _) fun _ _ => ?_)
  | (refine WP.spec_bind (P0.layout.paddr.p0 _) fun _ _ => ?_)
  | (refine WP.spec_bind (Pₘ := fun _ => True) ?_ fun _ _ => ?_)
  | split)))

set_option maxHeartbeats 4000000 in
/-- **`install_page`** at a VSpace word (break-before-make: at most two writes of the slot). -/
theorem vspace.install_page.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    (hV : VsOK Ω Sg V) {s0 s : S} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (a : A) (lu : vspace.PtSlot)
    (hx : V lu.slot) (e root asid vaddr : U64) (f : vspace.FrameCap) (attr : U64) (high : Bool) :
    vspace.install_page st ar s a lu e root asid vaddr f attr high ⦃ r =>
      Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vspace.install_page
  refine WP.spec_bind (LawfulStore.read_spec s lu.slot) fun old _ => ?_
  refine WP.spec_bind (P0.vspace.is_page.p0 old lu.shift) fun b _ => ?_
  try simp only [lift, bind_ok]
  refine spec_ite (fun _ => ?_) (fun _ => ?_)
  · refine WP.spec_bind P0.vspace.BBM_MASK.p0 fun mk _ => ?_
    refine spec_ite (fun _ => ?_) (fun _ => ?_)
    · refine WP.spec_bind (Cur0.wrV hV h hx e) fun s1 h1 => ?_
      refine WP.spec_bind (P0.vspace.invalidate_mapping.p0 ar a high asid vaddr hA) fun a1 _ => ?_
      exact (WP.spec_ok _).2 h1
    · refine WP.spec_bind (Cur0.wrV hV h hx 0#u64) fun s1 h1 => ?_
      refine WP.spec_bind (P0.vspace.invalidate_mapping.p0 ar a high asid vaddr hA) fun a1 _ => ?_
      refine WP.spec_bind (Pₘ := fun _ => True) (by copT) fun a2 _ => ?_
      refine WP.spec_bind (Cur0.wrV hV h1 hx e) fun s2 h2 => ?_
      exact (WP.spec_ok _).2 h2
  · refine WP.spec_bind (Pₘ := fun _ => True) (by copT) fun a1 _ => ?_
    refine WP.spec_bind (Cur0.wrV hV h hx e) fun s1 h1 => ?_
    exact (WP.spec_ok _).2 h1

set_option maxHeartbeats 4000000 in
/-- **`ept::install_s2_leaf`** at a VSpace word. -/
theorem ept.install_s2_leaf.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    (hV : VsOK Ω Sg V) {s0 s : S} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (a : A) (lu : ept.S2Slot)
    (hx : V lu.slot) (e root asid ipa ptr : U64) (dev : Bool) (attr : U64) :
    ept.install_s2_leaf st ar s a lu e root asid ipa ptr dev attr ⦃ r =>
      Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold ept.install_s2_leaf
  refine WP.spec_bind (LawfulStore.read_spec s lu.slot) fun old _ => ?_
  refine WP.spec_bind (P0.ept.is_leaf.p0 old lu.shift) fun b _ => ?_
  try simp only [lift, bind_ok]
  have tl : ∀ (s1 : S), Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s1 → ∀ a1 : A, ∀ m : Result A, m ⦃ _ => True ⦄ →
      (do
        let a2 ← m
        let s2 ← st.write s1 lu.slot e
        ok (s2, a2)) ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ⦄ := fun s1 h1 a1 m hm =>
    WP.spec_bind hm fun a2 _ => WP.spec_bind (Cur0.wrV hV h1 hx e) fun s2 h2 => (WP.spec_ok _).2 h2
  refine spec_ite (fun _ => ?_) (fun _ => ?_)
  · refine spec_ite (fun _ => ?_) (fun _ => ?_)
    · refine WP.spec_bind P0.ept.S2_BBM_MASK.p0 fun mk _ => ?_
      refine spec_ite (fun _ => ?_) (fun _ => ?_)
      · refine WP.spec_bind (Cur0.wrV hV h hx e) fun s1 h1 => ?_
        refine WP.spec_bind (hA.invalidate_stage2_page a asid ipa) fun a1 _ => ?_
        exact (WP.spec_ok _).2 h1
      · refine WP.spec_bind (Cur0.wrV hV h hx 0#u64) fun s1 h1 => ?_
        refine WP.spec_bind (hA.invalidate_stage2_page a asid ipa) fun a1 _ => ?_
        exact tl s1 h1 a1 _ (by copT)
    · refine WP.spec_bind (Cur0.wrV hV h hx 0#u64) fun s1 h1 => ?_
      refine WP.spec_bind (hA.invalidate_stage2_page a asid ipa) fun a1 _ => ?_
      exact tl s1 h1 a1 _ (by copT)
  · exact tl s h a _ (by copT)

/-! ## Page tables -/

set_option maxHeartbeats 4000000 in
/-- **`map_high_page_table`**: a level-2/3 table entry in the high window (a VSpace word, `VsPlaceA.hi`). -/
theorem vspace.map_high_page_table.dec {A : Type _} {ar : machine.Arch A} {V : U64 → Prop}
    (P : VsPlaceA st ar T Cs Ω H Sg Rp Scs Nt Z U V P3Ok) {s : S} {cap0 : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap0 extra)
    (hE : EntAt st P3Ok s) (slot ptr : U64) (vcap : capability.Cap) (vaddr : U64) (hslot : CapSlotW T Ω Sg slot) :
    vspace.map_high_page_table st s slot ptr vcap vaddr ⦃ r =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r.1 r.2 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hb := D.bxi
  unfold vspace.map_high_page_table
  curT
  refine WP.spec_bind (P.hi Ac s hE hb vcap 1#u64) fun r hr => ?_
  rcases r with ⟨root, asid⟩ | e
  swap
  · errV
  have hroot := hr _ rfl
  simp only [irq_branch_ok, bind_ok, lift]
  refine spec_ite (fun _ => by errV) (fun hv1 => ?_)
  refine spec_ite (fun _ => by errV) (fun hv2 => ?_)
  refine WP.spec_bind (hroot vaddr (inWin_of' hv1 hv2)) fun lu hlu => ?_
  refine spec_ite (fun _ => by errV) (fun _ => ?_)
  refine spec_ite (fun _ => by errV) (fun _ => ?_)
  refine WP.spec_bind (LawfulStore.read_spec s lu.slot) fun _ _ => ?_
  refine WP.spec_bind P0.vspace.D_VALID.p0 fun _ _ => ?_
  try simp only [lift, bind_ok]
  refine spec_ite (fun _ => by errV) (fun _ => ?_)
  refine WP.spec_bind (shl_and63u _) fun _ _ => ?_
  try simp only [lift, bind_ok]
  refine WP.spec_bind (Cur0.restart D) fun s1 h1 => ?_
  refine WP.spec_bind (obj.Slot.set_cap.capw (s := s1) hslot) fun s2 w2 => ?_
  have h2 := h1.capw w2 fun _ hb => hb
  refine WP.spec_bind (P0.layout.paddr.p0 ptr) fun _ _ => ?_
  refine WP.spec_bind (P0.vspace.make_user_table.p0 _) fun _ _ => ?_
  refine WP.spec_bind (Cur0.wrV P.vs h2 hlu _) fun s3 h3 => ?_
  exact (WP.spec_ok _).2 h3.post

set_option maxHeartbeats 4000000 in
/-- **`ept::map_table`**: a Stage-2 table entry (a VSpace word, from the root's walk `hroot`). -/
theorem ept.map_table.dec {A : Type _} {ar : machine.Arch A} {V : U64 → Prop} (hV : VsOK Ω Sg V)
    {s : S} {cap0 : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap0 extra) (a : A) (root asid ipa pt slot : U64)
    (hslot : CapSlotW T Ω Sg slot)
    (hroot : ∀ a, ar.s2_ipa_bits a ⦃ ib => ∀ ipa, ept.lookup_slot st s root ipa ib ⦃ lu => V lu.slot ⦄ ⦄) :
    ept.map_table st ar s a root asid ipa pt slot ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold ept.map_table
  refine WP.spec_bind (hroot a) fun ib hib => ?_
  refine WP.spec_bind (P0.ept.ipa_limit.p0 ib) fun _ _ => ?_
  refine spec_ite (fun _ => by errV) (fun _ => ?_)
  refine WP.spec_bind (hib ipa) fun lu hlu => ?_
  refine spec_ite (fun _ => by errV) (fun _ => ?_)
  refine WP.spec_bind (LawfulStore.read_spec s lu.slot) fun _ _ => ?_
  refine WP.spec_bind P0.ept.D_VALID.p0 fun _ _ => ?_
  try simp only [lift, bind_ok]
  refine spec_ite (fun _ => by errV) (fun _ => ?_)
  refine WP.spec_bind (shl_and63u _) fun _ _ => ?_
  try simp only [lift, bind_ok]
  curT
  refine WP.spec_bind (Cur0.restart D) fun s1 h1 => ?_
  refine WP.spec_bind (obj.Slot.set_cap.capw (s := s1) hslot) fun s2 w2 => ?_
  have h2 := h1.capw w2 fun _ hb => hb
  refine WP.spec_bind (P0.layout.paddr.p0 pt) fun _ _ => ?_
  refine WP.spec_bind (P0.ept.make_s2_table.p0 _) fun _ _ => ?_
  refine WP.spec_bind (Cur0.wrV hV h2 hlu _) fun s3 h3 => ?_
  exact (WP.spec_ok _).2 h3.post

set_option maxHeartbeats 8000000 in
/-- **The PageTable cap's decode** (Unmap: the walk's slot cleared and the table zeroed; Map: into a
VSpace, a high VSpace or a Stage-2 VSpace). -/
theorem vspace.decode_page_table.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    (P : VsPlaceA st ar T Cs Ω H Sg Rp Scs Nt Z U V P3Ok) {s : S} (ptr : U64) (mapped : Bool) (masid mvaddr : U64)
    {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.PageTable ptr mapped masid mvaddr) extra)
    (hE : EntAt st P3Ok s) (a : A) (lbl len slot buf : U64) (hslot : CapSlotW T Ω Sg slot) :
    vspace.decode_page_table st ar s a lbl len slot (.PageTable ptr mapped masid mvaddr) buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hb := D.bxi
  unfold vspace.decode_page_table
  curT
  try dsimp only
  refine spec_ite (fun _ => ?_) (fun _ => ?_)
  · refine WP.spec_bind (P0.cdt.is_final_capability.p0 st s slot hS) fun b _ => ?_
    refine spec_ite (fun _ => ?_) (fun _ => by errV)
    refine WP.spec_bind (Cur0.restart D) fun s1 h1 => ?_
    obtain ⟨Ac1, hb1⟩ := h1.bxi
    refine WP.spec_bind (Pₘ := fun r : S × A => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s r.1) ?_ ?_
    · split
      · refine WP.spec_bind (WP.spec_mono (P.ptUnmap Ac1 s s1 hE h1.fr hb1 a masid mvaddr ptr)
          fun r w => h1.vs P.vs w) ?_
        rintro ⟨s3, a2⟩ h3
        try simp only [uncurry_apply_pair]
        refine WP.spec_bind (LawfulStore.zero_spec s3 ptr 4096#u64) fun s4 e4 => ?_
        subst e4
        exact (WP.spec_ok _).2 (Cur0.zr h3 (P.tbl _ _ _ _ hE D ptr mapped masid mvaddr rfl))
      · exact (WP.spec_ok _).2 h1
    rintro ⟨s2, a1⟩ h2
    try simp only [uncurry_apply_pair]
    refine WP.spec_bind (obj.Slot.set_cap.capw (s := s2) hslot) fun s3 w3 => ?_
    exact (WP.spec_ok _).2 (h2.capw w3 fun _ hb => hb).post
  refine spec_ite (fun _ => by errV) (fun _ => ?_)
  refine WP.spec_bind (P0.vspace.extra.p0 extra 0#usize) fun o _ => ?_
  rcases o with _ | x
  · errV
  try dsimp only
  refine spec_ite (fun _ => ?_) (fun _ => by errV)
  refine spec_ite (fun _ => by errV) (fun _ => ?_)
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun vaddr1 _ => ?_
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st x s hS) fun vcap _ => ?_
  refine WP.spec_bind (Pₘ := fun _ => True) (by split <;> exact (WP.spec_ok _).2 trivial) fun b _ => ?_
  refine spec_ite (fun _ => ?_) (fun _ => ?_)
  · refine WP.spec_bind (vspace.map_high_page_table.dec P D hE slot ptr vcap vaddr1 hslot) ?_
    rintro ⟨r, s1⟩ h1
    exact (WP.spec_ok _).2 h1
  refine WP.spec_bind (P0.vspace.is_valid_vtable_root.p0 vcap) fun b1 _ => ?_
  refine spec_ite (fun _ => ?_) (fun _ => by errV)
  refine WP.spec_bind (Pₘ := fun _ => True) (by split <;> exact (WP.spec_ok _).2 trivial) fun b2 _ => ?_
  refine spec_ite (fun _ => ?_) (fun _ => ?_)
  · refine WP.spec_bind (P.s2 Ac s hE hb vcap 1#u64) fun r hr => ?_
    rcases r with ⟨root, asid1⟩ | e
    swap
    · errV
    have hroot := hr _ rfl
    simp only [irq_branch_ok, bind_ok]
    exact ept.map_table.dec P.vs D a root asid1 vaddr1 ptr slot hslot hroot
  refine spec_ite (fun _ => by errV) (fun _ => ?_)
  refine WP.spec_bind (P.s1 Ac s hE hb vcap 1#u64) fun r hr => ?_
  rcases r with ⟨root, asid1⟩ | e
  swap
  · errV
  simp only [irq_branch_ok, bind_ok]
  refine WP.spec_bind (hr _ rfl vaddr1) fun lu hlu => ?_
  refine spec_ite (fun _ => by errV) (fun _ => ?_)
  refine WP.spec_bind (LawfulStore.read_spec s lu.slot) fun _ _ => ?_
  refine WP.spec_bind P0.vspace.D_VALID.p0 fun _ _ => ?_
  try simp only [lift, bind_ok]
  refine spec_ite (fun _ => by errV) (fun _ => ?_)
  refine WP.spec_bind (shl_and63u _) fun _ _ => ?_
  try simp only [lift, bind_ok]
  refine WP.spec_bind (Cur0.restart D) fun s1 h1 => ?_
  refine WP.spec_bind (obj.Slot.set_cap.capw (s := s1) hslot) fun s2 w2 => ?_
  have h2 := h1.capw w2 fun _ hb => hb
  refine WP.spec_bind (P0.layout.paddr.p0 ptr) fun _ _ => ?_
  refine WP.spec_bind (P0.vspace.make_user_table.p0 _) fun _ _ => ?_
  refine WP.spec_bind (Cur0.wrV P.vs h2 hlu _) fun s3 h3 => ?_
  exact (WP.spec_ok _).2 h3.post

/-! ## Frames: reads, the reply -/

/-- `mapped_entry`'s slot is the walk's slot. -/
theorem vspace.mapped_entry.vs {V : U64 → Prop} {s : S} (f : vspace.FrameCap) (root : U64)
    (hl : vspace.lookup_pt_slot st s root f.vaddr ⦃ lu => V lu.slot ⦄) :
    vspace.mapped_entry st s f root ⦃ o => ∀ x, o = some x → V x.slot ⦄ := by
  unfold vspace.mapped_entry
  refine WP.spec_bind hl fun lu hlu => ?_
  refine WP.spec_bind (LawfulStore.read_spec s lu.slot) fun e _ => ?_
  refine WP.spec_bind (P0.vspace.page_shift.p0 _) fun _ _ => ?_
  repeat' (first
    | exact (WP.spec_ok _).2 fun x hx => by cases hx; exact hlu
    | exact (WP.spec_ok _).2 fun x hx => by cases hx
    | (refine WP.spec_bind (P0.vspace.is_page.p0 _ _) fun _ _ => ?_)
    | (refine WP.spec_bind (P0.vspace.page_base.p0 _ _) fun _ _ => ?_)
    | (refine WP.spec_bind (P0.layout.paddr.p0 _) fun _ _ => ?_)
    | split)

/-- **`reply1`**: the reply's message registers (`XS`), then the thread set running. -/
theorem vspace.reply1.bxiA (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) {s : S}
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hU : UserOK st T Cs Ω H U s) {t : U64} (ht : t ∈ T)
    (hr : ¬ BlockedR (L.mem s (stA t))) (call : Bool) (v : U64) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) :
    vspace.reply1 st s t call v ⦃ s' => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  obtain ⟨Q, R, x1⟩ := BXI.xs (sx := 0#u64) h hU
  unfold vspace.reply1
  refine WP.spec_bind (Pₘ := fun s2 => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q R 0#u64 s s2) ?_ ?_
  · split
    · refine WP.spec_bind (E.buf Ac ∅ Q R s _ hG x1.1 ht) fun b hb => ?_
      refine WP.spec_bind (obj.Tcb.set_reg.xs (v := 0#u64) x1 ht (by simp [layout.reg.BADGE, layout.reg.X0]))
        fun s3 x3 => ?_
      refine WP.spec_bind (msg.set_mr.xs x3 ht hb (by simp)) ?_
      rintro ⟨n, s4⟩ ⟨x4, -⟩
      try simp only [uncurry_apply_pair]
      refine WP.spec_bind (P0.msginfo.MessageInfo.new.p0 _ _ _ _) fun mi _ => ?_
      unfold msg.set_msg_info
      exact WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 _) fun w _ =>
        obj.Tcb.set_reg.xs (v := w) x4 ht (by simp [layout.reg.MSG_INFO, layout.reg.X1])
    · exact (WP.spec_ok _).2 x1
  intro s2 x2
  have hst : L.mem s2 (stA t) = L.mem s (stA t) := by
    rw [stA_eq]; exact x2.fr.2.2.2.2.1 _ ht 3328#u64 (by simp) (by simp) (by simp) (fun _ => by simp)
  exact sched.set_thread_state.running_nbr x2.bxi ht (hst ▸ hr)

/-- The flushes' total steps. -/
syntax "rdT" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rdT) => `(tactic| first
      | exact (WP.spec_ok _).2 trivial
      | exact P0.msg.syscall_arg.p0 st s _ buf _ hS
      | exact P0.vspace.page_shift.p0 _
      | exact P0.vspace.is_page.p0 _ _
      | exact P0.vspace.page_base.p0 _ _
      | exact P0.vspace.rights_of.p0 _
      | exact P0.vspace.page_cache_op.p0 _
      | exact P0.vspace.is_invalidate.p0 _
      | exact P0.layout.paddr.p0 _
      | exact P0.capability.FrameSize.bits.p0 _
      | exact P0.ept.is_leaf.p0 _ _
      | exact P0.ept.leaf_base.p0 _ _
      | exact P0.ept.s2_rights_of.p0 _
      | exact P0.ept.lookup_slot.p0 st s _ _ _ hS
      | exact P0.vspace.lookup_pt_slot.p0 st s _ _ hS
      | exact P0.ept.find.p0 st s _ hS
      | exact hS.read s _
      | exact hA.cache_op _ _ _ _ _ _ _
      | exact hA.s2_ipa_bits _
      | exact shl_and63u _
      | exact ept_sub1 (by assumption)
      | exact ept_sub2 (by assumption))

/-- One committed step of a flush's walk. -/
syntax "rdOne" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rdOne) => `(tactic| first
      | refine WP.spec_bind (Cur0.restart D) fun s1 h1 => ?_
      | refine spec_ite (fun _ => ?_) (fun _ => ?_)
      | (step with sched.cur_thread.spec as ⟨ct, ect⟩
         have e : ct = L.curW s := ect
         subst e)
      | (refine WP.spec_bind (P0.vspace.find_vspace_for_asid.p0 st s _ hS) fun r _ => ?_
         rcases r with _ | _ <;> (try simp only [irq_branch_ok, bind_ok]))
      | (refine WP.spec_bind (P0.vspace.frame_root.p0 st s _ hS) fun r _ => ?_
         rcases r with ⟨_, _⟩ | _ <;> (try simp only [irq_branch_ok, bind_ok]))
      | (refine WP.spec_bind (P0.vspace.mapped_entry.p0 st s _ _ hS) fun o _ => ?_
         rcases o with _ | _ <;> (try simp only [irq_branch_ok, bind_ok]))
      | (refine WP.spec_bind (P0.flush_frame_map_total st ar _) fun r _ => ?_
         rcases r with _ | _ <;> (try simp only [irq_branch_ok, bind_ok]))
      | refine WP.spec_bind (Pₘ := fun _ => True) (by rdT) fun _ _ => ?_)

/-- A flush's walk: error leaves (state unchanged), the restarted leaf, or one step and on. -/
syntax "rdW" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rdW) => `(tactic| first
      | exact (WP.spec_ok _).2 h1.post
      | errV
      | (rdOne <;> rdW))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **Page `Clean_Data` … `Unify_Instruction`**: reads (the frame's root, its descriptor; Stage-2:
`ept::flush_frame`), the caller's restart and the arch's `cache_op`. -/
theorem vspace.decode_page_flush.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s : S}
    {cap0 : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap0 extra) (a : A) (lbl len : U64) (f : vspace.FrameCap)
    (buf : U64) :
    vspace.decode_page_flush st ar s a lbl len f buf ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vspace.decode_page_flush ept.flush_frame
  try simp only [lift, bind_ok]
  rdW

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **VSpace `Clean_Data` … `Unify_Instruction`**: reads, the caller's restart and `cache_op`. -/
theorem vspace.decode_vspace_flush.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s : S}
    {cap0 : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap0 extra) (a : A) (lbl len ptr : U64) (m : Bool)
    (asid buf : U64) :
    vspace.decode_vspace_flush st ar s a lbl len (.Pml4 ptr m asid) buf ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vspace.decode_vspace_flush
  try simp only [lift, bind_ok]
  rdW

set_option maxHeartbeats 4000000 in
/-- **TestAndClearAccessed**: the descriptor's access flag cleared (a VSpace word, `VsPlaceA.fr` at the
cap's address, `VsPlaceA.fva`), then the reply. -/
theorem vspace.decode_test_and_clear_accessed.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {V : U64 → Prop} (P : VsPlaceA st ar T Cs Ω H Sg Rp Scs Nt Z U V P3Ok)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) {s : S} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (fp : U64) (fsz : capability.FrameSize) (fr : U64) (fd fm fe : Bool) (fa fv : U64)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Frame fp fsz fr fd fm fe fa fv) extra) (hE : EntAt st P3Ok s)
    (a : A) (call : Bool) :
    vspace.decode_test_and_clear_accessed st ar s a ⟨fp, fsz, fr, fd, fm, fe, fa, fv⟩ call ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hb := D.bxi
  have hct : L.curW s ∈ T := hb.1.choose_spec.choose_spec.curT
  unfold vspace.decode_test_and_clear_accessed
  try simp only [lift, bind_ok]
  refine spec_ite (fun _ => by errV) (fun hfe => ?_)
  have hfe' : fe = false := by simpa using hfe
  subst hfe'
  refine WP.spec_bind (Pₘ := fun _ => True) (by cases fsz <;> exact (WP.spec_ok _).2 trivial) ?_
  rintro ⟨fs, bh⟩ _
  try simp only [uncurry_apply_pair]
  refine spec_ite (fun _ => by errV) (fun _ => ?_)
  refine spec_ite (fun _ => ?_) (fun _ => by errV)
  refine spec_ite (fun _ => by errV) (fun hfa => ?_)
  refine WP.spec_bind (hA.hw_access_flag a) fun b1 _ => ?_
  refine spec_ite (fun _ => ?_) (fun _ => by errV)
  refine WP.spec_bind (P.fr Ac s hE hb fa) fun r hr => ?_
  rcases r with ⟨r1, r2⟩ | e
  swap
  · errV
  try dsimp only
  have hl := hr _ rfl fv (P.fva Ac s _ extra hE D fp fsz fr fd fm fa fv rfl hfa)
  refine WP.spec_bind (vspace.mapped_entry.vs _ r1 hl) fun o ho => ?_
  rcases o with _ | x
  · errV
  have hx := ho x rfl
  try dsimp only
  curT
  refine WP.spec_bind P0.vspace.D_AF.p0 fun i _ => ?_
  try simp only [lift, bind_ok]
  refine WP.spec_bind (LawfulStore.fetch_and_spec s x.slot _) ?_
  rintro ⟨old, s1⟩ e1
  try simp only [uncurry_apply_pair]
  try dsimp only
  obtain ⟨hold, e1⟩ := Prod.mk.inj e1
  rw [← hold] at e1
  subst e1
  obtain ⟨h1, -, -, ec, -, fld, -, -⟩ := blk_of_vs hb.blk P.vs (writesIn_wr_V (v := old &&& ~~~i) P.vs hx)
  have hU1 : UserOK st T Cs Ω H U (L.wr s x.slot (old &&& ~~~i)) := D.user.ksb (L.ksb_wr _ _ _)
  have hr1 : ¬ BlockedR (L.mem (L.wr s x.slot (old &&& ~~~i)) (stA (L.curW s))) := by
    rw [stA_eq, fld _ hct _ (by simp) (by simp) (by simp), ← stA_eq]; exact nbr_runnable D.run
  have hG1 : XG st T Cs Ω H Sg Scs Z P3Ok (L.wr s x.slot (old &&& ~~~i)) :=
    hE.xg.of_fr ((writesIn_wr_V (v := old &&& ~~~i) P.vs hx).mono fun b hb =>
      Or.inr (Or.inr (Or.inl (Or.inr (P.vs b hb).2))))
  split
  · exact WP.spec_bind (vspace.reply1.bxiA E (BlkOK.bxi h1) hU1 hct hr1 call _ hG1) fun s2 h2 =>
      (WP.spec_ok _).2 (DecPost.ok_bxi h2)
  · exact WP.spec_bind (vspace.reply1.bxiA E (BlkOK.bxi h1) hU1 hct hr1 call _ hG1) fun s2 h2 =>
      (WP.spec_ok _).2 (DecPost.ok_bxi h2)

/-! ## Frames: maps -/

set_option hygiene false in
/-- The Stage-2 frame map's tail, from the walk's slot `hlu` on. -/
local macro "mfTail" : tactic => `(tactic| (
  refine spec_ite (fun _ => by errV) (fun _ => ?_)
  refine WP.spec_bind (P0.vspace.rights_readable.p0 _) fun _ _ => ?_
  refine WP.spec_bind (P0.layout.paddr.p0 _) fun _ _ => ?_
  refine WP.spec_bind (P0.ept.make_s2_leaf.p0 _ _ _ _ _) fun en _ => ?_
  curT
  refine WP.spec_bind (Cur0.restart D) fun s1 h1 => ?_
  refine spec_ite (fun _ => ?_) (fun _ => ?_) <;> refine spec_ite (fun _ => ?_) (fun _ => ?_) <;>
  (refine WP.spec_bind (obj.Slot.set_cap.capw (s := s1) hslot) fun s2 w2 => ?_
   refine WP.spec_bind (ept.install_s2_leaf.cur0 hA hV (h1.capw w2 fun _ hb => hb) a _ hlu _ _ _ _ _ _ _) ?_
   rintro ⟨s3, a1⟩ h3
   exact (WP.spec_ok _).2 h3.post)))

set_option maxHeartbeats 8000000 in
/-- **`ept::map_frame`**: a Stage-2 leaf (a VSpace word, from the root's walk `hroot`). -/
theorem ept.map_frame.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    (hV : VsOK Ω Sg V) {s : S} {cap0 : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap0 extra) (a : A) (root asid ipa vm attr ptr : U64)
    (size : capability.FrameSize) (rights : U64) (dev : Bool) (masid mva slot : U64)
    (hslot : CapSlotW T Ω Sg slot)
    (hroot : ∀ a, ar.s2_ipa_bits a ⦃ ib => ∀ ipa, ept.lookup_slot st s root ipa ib ⦃ lu => V lu.slot ⦄ ⦄) :
    ept.map_frame st ar s a root asid ipa vm attr ptr size rights dev masid mva slot ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold ept.map_frame
  refine WP.spec_bind (P0.capability.FrameSize.bits.p0 size) fun shift _ => ?_
  refine WP.spec_bind (hroot a) fun ib hib => ?_
  try simp only [lift, bind_ok]
  refine WP.spec_bind (shl_and63u _) fun _ _ => ?_
  try simp only [lift, bind_ok]
  refine spec_ite (fun _ => by errV) (fun _ => ?_)
  refine spec_ite (fun _ => ?_) (fun _ => ?_)
  · refine spec_ite (fun _ => by errV) (fun _ => ?_)
    refine spec_ite (fun _ => by errV) (fun _ => ?_)
    refine WP.spec_bind (hib ipa) fun lu hlu => ?_
    mfTail
  · refine WP.spec_bind (shl_and63u _) fun _ _ => ?_
    try simp only [lift, bind_ok]
    refine WP.spec_bind (P0.ept.ipa_limit.p0 ib) fun _ _ => ?_
    refine spec_ite (fun _ => by errV) (fun _ => ?_)
    refine spec_ite (fun _ => by errV) (fun _ => ?_)
    refine WP.spec_bind (hib ipa) fun lu hlu => ?_
    mfTail

set_option hygiene false in
/-- A Stage-1 page map's tail, from the walk `hroot` on. -/
local macro "pmTail" : tactic => `(tactic| (
  refine WP.spec_bind (by first | exact hroot () | exact hroot _) fun lu hlu => ?_
  refine spec_ite (fun _ => by errV) (fun _ => ?_)
  refine WP.spec_bind (P0.vspace.rights_readable.p0 _) fun _ _ => ?_
  refine WP.spec_bind (P0.layout.paddr.p0 _) fun _ _ => ?_
  refine WP.spec_bind (P0.vspace.make_user_page.p0 _ _ _ _ _) fun en _ => ?_
  refine WP.spec_bind (Cur0.restart D) fun s1 h1 => ?_
  refine WP.spec_bind (obj.Slot.set_cap.capw (s := s1) hslot) fun s2 w2 => ?_
  refine WP.spec_bind (vspace.install_page.cur0 hA P.vs (h1.capw w2 fun _ hb => hb) a _ hlu _ _ _ _ _ _ _) ?_
  rintro ⟨s3, a1⟩ h3
  exact (WP.spec_ok _).2 h3.post))

set_option maxHeartbeats 8000000 in
/-- **ARMPageMap into an `ArmHighVSpace`**: in the window (`VsPlaceA.hi`). -/
theorem vspace.decode_high_page_map.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {V : U64 → Prop} (P : VsPlaceA st ar T Cs Ω H Sg Rp Scs Nt Z U V P3Ok) {s : S} {cap0 : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap0 extra)
    (hE : EntAt st P3Ok s) (a : A) (slot : U64) (f : vspace.FrameCap) (vcap : capability.Cap)
    (vaddr vm attr : U64) (hslot : CapSlotW T Ω Sg slot) :
    vspace.decode_high_page_map st ar s a slot f vcap vaddr vm attr ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hb := D.bxi
  unfold vspace.decode_high_page_map
  curT
  refine WP.spec_bind (P.hi Ac s hE hb vcap 1#u64) fun r hr => ?_
  rcases r with ⟨root, asid⟩ | e
  swap
  · errV
  have hroot0 := hr _ rfl
  simp only [irq_branch_ok, bind_ok, lift]
  refine WP.spec_bind (P0.vspace.page_shift.p0 _) fun shift _ => ?_
  refine WP.spec_bind (shl_and63u _) fun _ _ => ?_
  try simp only [lift, bind_ok]
  refine spec_ite (fun _ => by errV) (fun _ => ?_)
  refine spec_ite (fun _ => ?_) (fun _ => ?_)
  · refine spec_ite (fun _ => by errV) (fun _ => ?_)
    refine spec_ite (fun _ => by errV) (fun _ => ?_)
    refine WP.spec_bind (shl_and63u _) fun _ _ => ?_
    try simp only [lift, bind_ok]
    refine spec_ite (fun _ => by errV) (fun hw1 => ?_)
    refine spec_ite (fun _ => by errV) (fun hw2 => ?_)
    refine spec_ite (fun _ => by errV) (fun hw3 => ?_)
    have hroot : ∀ _ : Unit, vspace.lookup_pt_slot st s root vaddr ⦃ lu => V lu.slot ⦄ :=
      fun _ => hroot0 vaddr (inWin_of hw1 hw2 hw3)
    pmTail
  · refine WP.spec_bind (shl_and63u _) fun _ _ => ?_
    try simp only [lift, bind_ok]
    refine spec_ite (fun _ => by errV) (fun hw1 => ?_)
    refine spec_ite (fun _ => by errV) (fun hw2 => ?_)
    refine spec_ite (fun _ => by errV) (fun hw3 => ?_)
    have hroot : ∀ _ : Unit, vspace.lookup_pt_slot st s root vaddr ⦃ lu => V lu.slot ⦄ :=
      fun _ => hroot0 vaddr (inWin_of hw1 hw2 hw3)
    pmTail

set_option hygiene false in
/-- The Stage-1 arm of ARMPageMap (`check_vspace`, `VsPlaceA.s1`). -/
local macro "s1Map" : tactic => `(tactic| (
  refine WP.spec_bind (P.s1 Ac s hE hb vcap 1#u64) fun r hr => ?_
  rcases r with ⟨root, asid⟩ | e
  swap
  · errV
  have hroot := hr _ rfl
  simp only [irq_branch_ok, bind_ok, lift]
  refine WP.spec_bind (P0.vspace.page_shift.p0 _) fun shift _ => ?_
  refine WP.spec_bind (shl_and63u _) fun _ _ => ?_
  try simp only [lift, bind_ok]
  refine spec_ite (fun _ => by errV) (fun _ => ?_)
  refine spec_ite (fun _ => ?_) (fun _ => ?_)
  · refine spec_ite (fun _ => by errV) (fun _ => ?_)
    refine spec_ite (fun _ => by errV) (fun _ => ?_)
    pmTail
  · refine WP.spec_bind (shl_and63u _) fun _ _ => ?_
    try simp only [lift, bind_ok]
    refine spec_ite (fun _ => by errV) (fun _ => ?_)
    refine spec_ite (fun _ => by errV) (fun _ => ?_)
    pmTail))

set_option maxHeartbeats 16000000 in
/-- **ARMPageMap**: into a Stage-2 VSpace (`ept::map_frame`), a high VSpace or a VSpace. -/
theorem vspace.decode_page_map.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {V : U64 → Prop} (P : VsPlaceA st ar T Cs Ω H Sg Rp Scs Nt Z U V P3Ok) {s : S} {cap0 : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap0 extra)
    (hE : EntAt st P3Ok s) (a : A) (len slot : U64) (f : vspace.FrameCap) (buf : U64)
    (hslot : CapSlotW T Ω Sg slot) :
    vspace.decode_page_map st ar s a len slot f buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hb := D.bxi
  unfold vspace.decode_page_map
  curT
  refine WP.spec_bind (P0.vspace.extra.p0 extra 0#usize) fun o _ => ?_
  rcases o with _ | x
  · errV
  try dsimp only
  by_cases hl3 : len ≥ 3#u64
  swap
  · rw [if_neg hl3]; errV
  rw [if_pos hl3]
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun vaddr _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun attr _ => ?_
  refine WP.spec_bind (P0.capability.Rights.from_word.p0 _) fun _ _ => ?_
  refine WP.spec_bind (P0.capability.mask_vm_rights.p0 _ _) fun vm _ => ?_
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st x s hS) fun vcap _ => ?_
  refine WP.spec_bind (Pₘ := fun _ => True) (by split <;> exact (WP.spec_ok _).2 trivial) fun b _ => ?_
  refine spec_ite (fun _ => ?_) (fun _ => ?_)
  · refine WP.spec_bind (P.s2 Ac s hE hb vcap 1#u64) fun r hr => ?_
    rcases r with ⟨root, asid⟩ | e
    swap
    · errV
    have hroot := hr _ rfl
    simp only [irq_branch_ok, bind_ok]
    refine spec_ite (fun _ => ?_) (fun _ => ?_)
    · refine spec_ite (fun _ => ?_) (fun _ => by errV)
      exact ept.map_frame.dec hA P.vs D a root asid _ _ _ _ _ _ _ _ _ slot hslot hroot
    · exact ept.map_frame.dec hA P.vs D a root asid _ _ _ _ _ _ _ _ _ slot hslot hroot
  refine spec_ite (fun _ => ?_) (fun _ => ?_)
  · refine spec_ite (fun _ => by errV) (fun _ => ?_)
    refine WP.spec_bind (Pₘ := fun _ => True) (by split <;> exact (WP.spec_ok _).2 trivial) fun b1 _ => ?_
    refine spec_ite (fun _ => ?_) (fun _ => ?_)
    · exact vspace.decode_high_page_map.dec hA P D hE a slot f vcap vaddr vm attr hslot
    s1Map
  · refine WP.spec_bind (Pₘ := fun _ => True) (by split <;> exact (WP.spec_ok _).2 trivial) fun b1 _ => ?_
    refine spec_ite (fun _ => ?_) (fun _ => ?_)
    · exact vspace.decode_high_page_map.dec hA P D hE a slot f vcap vaddr vm attr hslot
    s1Map

/-! ## DeriveSubframe (l4h 0029) -/

/-- **`insert_subframes`**: the subframe caps' insertions under the source slot, into cap slots. -/
theorem vspace.insert_subframes.cur0 (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok) {s0 s : S}
    (hE : EntAt st P3Ok s0) (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) {src dest first base count vm : U64}
    (hsrc : CapW T Ω Sg src)
    (hd : ∀ j : U64, j.val < count.val → obj.Slot.index dest (core.num.U64.wrapping_add first j) ⦃ sl =>
      CapW T Ω Sg sl ⦄) :
    vspace.insert_subframes st s src dest first base count vm ⦃ s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vspace.insert_subframes vspace.insert_subframes_loop
  apply loop.spec_decr_nat (measure := fun y : S × U64 => count.val - y.2.val)
    (inv := fun y => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 y.1)
  · rintro ⟨s3, i3⟩ h3
    simp only at h3
    dsimp only
    unfold vspace.insert_subframes_loop.body
    split
    · rename_i hlt
      have hlt' : i3.val < count.val := by simpa using hlt
      refine WP.spec_bind (Pₘ := fun _ => True) (by p0_auto) fun _ _ => ?_
      try simp only [lift, bind_ok]
      refine WP.spec_bind (hd i3 hlt') fun sl hsl => ?_
      obtain ⟨Ac', hb⟩ := h3.bxi
      refine WP.spec_bind (Pₘ := fun s4 => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s4) ?_ fun s4 h4 => ?_
      · unfold cdt.insert
        refine WP.spec_bind (P0.obj.Slot.cap.p0 st src s3 hS) fun c0 _ => ?_
        exact WP.spec_mono (C.ins Ac' s0 s3 _ c0 src sl hE h3.fr hb hsrc hsl) fun s5 w => h3.capw w fun _ hb => hb
      step as ⟨i4, hi4⟩
      exact ⟨h4, by scalar_tac⟩
    · exact (WP.spec_ok _).2 h3
  · exact h

set_option maxHeartbeats 4000000 in
/-- **DeriveSubframe**: the restart and the subframe caps' insertions. -/
theorem vspace.derive_subframe.dec {A : Type _} {ar : machine.Arch A} {V : U64 → Prop}
    (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok) (P : VsPlaceA st ar T Cs Ω H Sg Rp Scs Nt Z U V P3Ok) {s : S}
    {cap0 : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap0 extra) (hE : EntAt st P3Ok s) (len src : U64)
    (cap : capability.Cap) (buf : U64) (hsrc : CapSlotW T Ω Sg src) :
    vspace.derive_subframe st s len src cap buf extra ⦃ r =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r.1 r.2 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hb := D.bxi
  unfold vspace.derive_subframe
  curT
  refine WP.spec_bind (P0.vspace.extra.p0 extra 0#usize) fun o _ => ?_
  rcases o with _ | x
  · errV
  try dsimp only
  refine spec_ite (fun _ => ?_) (fun _ => by errV)
  refine WP.spec_bind (P0.vspace.large_ram_frame.p0 cap) fun o1 _ => ?_
  rcases o1 with _ | ⟨ptr, rights⟩
  · errV
  try dsimp only
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun ni _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun nd _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun no _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun off _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun cnt _ => ?_
  refine WP.spec_bind (Pₘ := fun _ => True) (by p0_auto) fun _ _ => ?_
  refine spec_ite (fun _ => by errV) (fun _ => ?_)
  try simp only [lift, bind_ok]
  refine spec_ite (fun _ => by errV) (fun _ => ?_)
  refine WP.spec_bind (Pₘ := fun _ => True) (by p0_auto) fun _ _ => ?_
  refine WP.spec_bind (Pₘ := fun _ => True) (by p0_auto) fun _ _ => ?_
  refine spec_ite (fun _ => by errV) (fun _ => ?_)
  refine spec_ite (fun _ => by errV) (fun _ => ?_)
  refine WP.spec_bind (P.sub Ac s x ni nd no cnt hE hb) fun r hr => ?_
  rcases r with dst | e
  swap
  · errV
  have hd := hr dst rfl
  simp only [irq_branch_ok, bind_ok]
  refine WP.spec_bind (P0.vspace.ensure_empty_run.p0 st s dst no cnt hS) fun r1 _ => ?_
  rcases r1 with _ | e
  swap
  · errV
  simp only [irq_branch_ok, bind_ok]
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
  refine WP.spec_bind (P0.capability.Rights.from_word.p0 _) fun _ _ => ?_
  refine WP.spec_bind (P0.capability.mask_vm_rights.p0 _ _) fun _ _ => ?_
  refine WP.spec_bind (Cur0.restart D) fun s1 h1 => ?_
  try simp only [lift, bind_ok]
  refine WP.spec_bind (vspace.insert_subframes.cur0 C hE h1 (SlotW.capw0 hsrc) hd) fun s2 h2 => ?_
  exact (WP.spec_ok _).2 h2.post

/-! ## The frame caps -/

set_option maxHeartbeats 8000000 in
/-- **The frame caps' decode** (Map, Unmap, the cache labels, GetAddress, TestAndClearAccessed,
DeriveSubframe). -/
theorem vspace.decode_frame.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    (P : VsPlaceA st ar T Cs Ω H Sg Rp Scs Nt Z U V P3Ok) (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) {s : S} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (fp : U64) (fsz : capability.FrameSize) (fr : U64) (fd fm fe : Bool) (fa fv : U64)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Frame fp fsz fr fd fm fe fa fv) extra) (hE : EntAt st P3Ok s)
    (a : A) (lbl len slot : U64) (call : Bool) (buf : U64) (hslot : CapSlotW T Ω Sg slot) :
    vspace.decode_frame st ar s a lbl len slot (.Frame fp fsz fr fd fm fe fa fv) call buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hb := D.bxi
  have hct : L.curW s ∈ T := hb.1.choose_spec.choose_spec.curT
  unfold vspace.decode_frame
  simp only [vspace.as_frame, bind_ok]
  curT
  refine spec_ite (fun _ => vspace.decode_page_map.dec hA P D hE a len slot _ buf hslot) (fun _ => ?_)
  refine spec_ite (fun _ => ?_) (fun _ => ?_)
  · refine WP.spec_bind (Cur0.restart D) fun s1 h1 => ?_
    obtain ⟨Ac1, hb1⟩ := h1.bxi
    refine WP.spec_bind (Pₘ := fun r : S × A => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s r.1) ?_ ?_
    · refine spec_ite (fun _ => ?_) (fun _ => (WP.spec_ok _).2 h1)
      refine spec_ite (fun hfa => ?_) (fun _ => (WP.spec_ok _).2 h1)
      refine spec_ite (fun _ => ?_) (fun hfe => ?_)
      · refine WP.spec_bind (P0.capability.FrameSize.bits.p0 _) fun i _ => ?_
        exact WP.spec_mono (P.s2Unmap Ac1 s s1 hE h1.fr hb1 a _ _ _ _ _) fun r w => h1.vs P.vs w
      · have hfe' : fe = false := by simpa using hfe
        have hfa' : fa ≠ 0#u64 := by simpa using hfa
        subst hfe'
        exact WP.spec_mono (P.pgUnmap Ac1 s s1 hE h1.fr hb1 a _ _ _ _
          (P.fva Ac s _ extra hE D fp fsz fr fd fm fa fv rfl hfa')) fun r w => h1.vs P.vs w
    rintro ⟨s2, a1⟩ h2
    try simp only [uncurry_apply_pair]
    refine WP.spec_bind (P0.vspace.unmapped_frame.p0 _) fun c _ => ?_
    refine WP.spec_bind (obj.Slot.set_cap.capw (s := s2) hslot) fun s3 w3 => ?_
    exact (WP.spec_ok _).2 (h2.capw w3 fun _ hb => hb).post
  refine WP.spec_bind (P0.vspace.is_cache_label.p0 lbl) fun bc _ => ?_
  refine spec_ite (fun _ => vspace.decode_page_flush.dec hA D a lbl len _ buf) (fun _ => ?_)
  refine spec_ite (fun _ => ?_) (fun _ => ?_)
  · refine WP.spec_bind (Cur0.restart D) fun s1 h1 => ?_
    obtain ⟨Ac1, hb1⟩ := h1.bxi
    refine WP.spec_bind (P0.layout.paddr.p0 _) fun i _ => ?_
    refine WP.spec_bind (vspace.reply1.bxiA E hb1 (D.user.ksb h1.fr.1) hct
      (by have nb := h1.nb; rwa [h1.2.choose_spec.2.1] at nb) call i (hE.xg.of_fr h1.fr))
      fun s2 h2 => ?_
    exact (WP.spec_ok _).2 (DecPost.ok_bxi h2)
  refine spec_ite (fun _ => vspace.decode_test_and_clear_accessed.dec hA P E fp fsz fr fd fm fe fa fv D hE a call)
    (fun _ => ?_)
  refine spec_ite (fun _ => ?_) (fun _ => by errV)
  refine WP.spec_bind (vspace.derive_subframe.dec C P D hE len slot _ buf hslot) ?_
  rintro ⟨r, s1⟩ hr
  exact (WP.spec_ok _).2 hr

/-! ## The decode -/

theorem vs_mask511_mul8 (x : U64) (y : U64) (hy : y.val = (x &&& 511#u64).val * 8) :
    y = core.num.U64.wrapping_mul (x &&& 511#u64) 8#u64 := by
  have hb : (x &&& 511#u64).val < 512 := by
    rw [UScalar.val_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  apply UScalar.eq_of_val_eq
  rw [core.num.U64.wrapping_mul_val_eq, hy]
  have h8 : (8#u64).val = 8 := rfl
  rw [h8]
  exact (Nat.mod_eq_of_lt (by first | (simp [UScalar.size, UScalarTy.numBits]; omega) | scalar_tac)).symm

theorem vspace.extra.memA (ex : Aeneas.Std.Array obj.Slot 3#usize) (i : Usize) :
    vspace.extra ex i ⦃ o => ∀ x, o = some x → x ∈ ex.val ∧ x ≠ 0#u64 ⦄ := by
  unfold vspace.extra
  split
  · exact (WP.spec_ok _).2 fun x hx => by cases hx
  rename_i hi
  refine WP.spec_bind (idx_mem ex i (by simp at hi; scalar_tac)) fun x hx => ?_
  simp only [obj.Slot.is_null, bind_ok]
  split
  · exact (WP.spec_ok _).2 fun x hx => by cases hx
  · rename_i h0
    exact (WP.spec_ok _).2 fun y hy => by cases hy; exact ⟨hx, by simpa using h0⟩

set_option hygiene false in
/-- ASIDPoolAssign's tail, from the pool lookup on (the caller's restart, the VSpace cap's update and the
pool entry's write, a VSpace word `VsPlaceA.pool`). -/
local macro "poolTail" : tactic => `(tactic| (
  refine WP.spec_bind (Pₘ := fun _ => True) (by p0_auto) fun i _ => ?_
  obtain ⟨pool, epool, -⟩ := spec_exists_dut (P0.vspace.asid_table.p0 st s i hS)
  have hpool : ∀ asid, pool ≠ 0#u64 →
      V (core.num.U64.wrapping_add pool (core.num.U64.wrapping_mul (asid &&& 511#u64) 8#u64)) := by
    intro asid
    have := P.pool Ac s hE hb asid i
    rw [epool] at this
    exact (WP.spec_ok _).1 this
  rw [epool]
  simp only [bind_ok]
  refine spec_ite (fun _ => by errV) (fun hp0 => ?_)
  refine spec_ite (fun _ => by errV) (fun _ => ?_)
  refine WP.spec_bind (Pₘ := fun _ => True) (by first
    | exact P0.vspace.decode_loop1.p0 st s _ _ _ hS
    | exact P0.vspace.decode_loop2.p0 st s _ _ _ hS
    | exact P0.vspace.decode_loop3.p0 st s _ _ _ hS) fun i1 _ => ?_
  refine spec_ite (fun _ => by errV) (fun _ => ?_)
  try simp only [lift, bind_ok]
  refine WP.spec_bind (Cur0.restart D) fun s1 h1 => ?_
  refine WP.spec_bind (Pₘ := fun s2 => WritesIn st s1 s2 (CapW T Ω Sg)) (by
    repeat' (first
      | exact obj.Slot.set_cap.capw hxs
      | split)) fun s2 w2 => ?_
  have h2 := h1.capw w2 fun _ hb => hb
  try simp only [lift, bind_ok]
  step as ⟨i3, hi3⟩
  try simp only [lift, bind_ok]
  refine WP.spec_bind (LawfulStore.write_spec s2 _ _) fun s3 e3 => ?_
  subst e3
  rw [vs_mask511_mul8 _ i3 hi3]
  exact (WP.spec_ok _).2 (h2.vs P.vs (writesIn_wr_V P.vs (hpool _ hp0))).post))

set_option maxHeartbeats 16000000 in
/-- **`vspace.decode`** over the VSpace family's caps. -/
theorem vspace.decode.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    (P : VsPlaceA st ar T Cs Ω H Sg Rp Scs Nt Z U V P3Ok) (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) {s : S} {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra)
    (hE : EntAt st P3Ok s) (hx : ∀ sl ∈ extra.val, sl ≠ 0#u64 → CapSlotW T Ω Sg sl)
    (a : A) (lbl len slot : U64) (call : Bool) (buf : U64) (hslot : CapSlotW T Ω Sg slot) :
    vspace.decode st ar s a lbl len slot cap call buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hb := D.bxi
  unfold vspace.decode
  curT
  cases cap
  case Frame fp fsz fr fd fm fe fa fv =>
    exact vspace.decode_frame.dec hA P C E fp fsz fr fd fm fe fa fv D hE a lbl len slot call buf hslot
  case PageTable ptr m asd va =>
    exact vspace.decode_page_table.dec hA P ptr m asd va D hE a lbl len slot buf hslot
  case Pml4 ptr m asid =>
    try dsimp only
    refine spec_ite (fun _ => vspace.decode_vspace_flush.dec hA D a lbl len ptr m asid buf) (fun _ => ?_)
    refine spec_ite (fun _ => vspace.decode_vspace_flush.dec hA D a lbl len ptr m asid buf) (fun _ => ?_)
    refine spec_ite (fun _ => vspace.decode_vspace_flush.dec hA D a lbl len ptr m asid buf) (fun _ => ?_)
    refine spec_ite (fun _ => vspace.decode_vspace_flush.dec hA D a lbl len ptr m asid buf) (fun _ => ?_)
    errV
  case AsidControl =>
    try dsimp only
    refine spec_ite (fun _ => by errV) (fun _ => ?_)
    refine WP.spec_bind (vspace.extra.memA extra 0#usize) fun o ho => ?_
    refine WP.spec_bind (vspace.extra.memA extra 1#usize) fun o1 ho1 => ?_
    rcases o with _ | x
    · errV
    obtain ⟨hxm, hx0⟩ := ho x rfl
    try dsimp only
    rcases o1 with _ | y
    · errV
    try dsimp only
    refine spec_ite (fun _ => ?_) (fun _ => by errV)
    refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun idx _ => ?_
    refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun dep _ => ?_
    refine WP.spec_bind (WP.spec_and (P0.obj.Slot.cap.p0 st x s hS) (P.mkPool _ _ _ _ hE D x hxm hx0))
      fun ut ⟨_, hut⟩ => ?_
    refine WP.spec_bind (P0.obj.Slot.cap.p0 st y s hS) fun root _ => ?_
    refine WP.spec_bind (P0.vspace.decode_loop0.p0 st s 0#u64 hS) fun i _ => ?_
    refine WP.spec_bind P0.vspace.N_ASID_POOLS.p0 fun np _ => ?_
    refine spec_ite (fun _ => by errV) (fun _ => ?_)
    refine WP.spec_bind (Pₘ := fun _ => True) (by p0_auto) fun base _ => ?_
    cases ut
    case Untyped uptr usb ufi udev =>
      have hz := hut _ _ _ _ rfl
      try dsimp only
      refine spec_ite (fun _ => by errV) (fun _ => ?_)
      refine spec_ite (fun _ => ?_) (fun _ => by errV)
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
      refine WP.spec_bind (shl_and63u _) fun i2 _ => ?_
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
        exact WP.spec_mono (C.ins Ac3 s _ _ c0 x v hE h3.fr hb3 (SlotW.capw0 hxs) hv) fun s5 w =>
          h3.capw w fun _ hb => hb
      obtain ⟨Ac4, hb4⟩ := h4.bxi
      refine WP.spec_bind (P.aset Ac4 s s4 i _ hE h4.fr hb4) fun s5 w5 => ?_
      exact (WP.spec_ok _).2 (h4.capw w5 fun b hb => Or.inr hb).post
    all_goals (simp only [error.invalid_cap, bind_ok]; exact (WP.spec_ok _).2 (D.err _))
  case AsidPool pptr abase =>
    try dsimp only
    refine spec_ite (fun _ => by errV) (fun _ => ?_)
    refine WP.spec_bind (vspace.extra.memA extra 0#usize) fun o ho => ?_
    rcases o with _ | x
    · errV
    obtain ⟨hxm, hx0⟩ := ho x rfl
    have hxs := hx x hxm hx0
    try dsimp only
    refine WP.spec_bind (P0.obj.Slot.cap.p0 st x s hS) fun c _ => ?_
    cases c
    case Pml4 ptr1 b1 _ =>
      try dsimp only
      refine spec_ite (fun _ => by errV) (fun _ => ?_)
      poolTail
    case HighVSpace ptr1 b1 _ =>
      try dsimp only
      refine spec_ite (fun _ => by errV) (fun _ => ?_)
      poolTail
    case Ept ptr1 i b1 _ _ =>
      try dsimp only
      split
      · try dsimp only
        refine spec_ite (fun _ => by errV) (fun _ => ?_)
        poolTail
      · errV
    all_goals (simp only [error.invalid_cap, bind_ok]; exact (WP.spec_ok _).2 (D.err _))
  all_goals (simp only [error.invalid_cap, error.illegal, bind_ok]; exact (WP.spec_ok _).2 (D.err _))

/-- **InvGaps' `vspace`, discharged** (AArch64) from `VsPlaceA` ([J] fields), the CSpace placement
facts, the transfer's (a reply's buffer) and `IrqPlace.extra` (the extra caps' slots). -/
theorem decGap_vspace {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    (P : VsPlaceA st ar T Cs Ω H Sg Rp Scs Nt Z U V P3Ok) (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (Pl : IrqPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) :
    DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .vspace := by
  intro Ac s a lbl len slot cap blk call don fp buf extra hf D hslot hE
  cases cap <;> simp [capFam] at hf
  all_goals
    unfold syscall.decode_invocation
    step with sched.cur_thread.spec as ⟨ct, _⟩
    try dsimp only
    exact vspace.decode.dec hA P C E D hE (Pl.extra _ _ _ _ hE D) a lbl len slot call buf hslot

end

end Fl4ProofsA64.P1
