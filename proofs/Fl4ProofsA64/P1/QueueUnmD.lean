/-
P1 (aarch64, gen 46): **ARMPageTableUnmap at decode level over the narrowed typings** (QueueUnmR's data steps
assembled): the case fact `PtFnd` is carried across `set_thread_state`, and the unmapped `PageTable` cap's
`set_cap` round trip is proved.

* `loopD_congr` (generic): two loop bodies equal on an invariant the second preserves with a decreasing measure
  give equal loops.
* The walks read only `VsR` words: `ept.unmap_table_loop.body_congr` / `.body_inv` / **`ept.unmap_table_loop.congr`**
  (invariant `UtI`, gen 40), `vspace.unmap_page_table_loop.body_congr` / `.body_inv` /
  **`vspace.unmap_page_table_loop.congr`** (invariant `UpI`, gen 38): at a typing over a table set `T'`, a state
  agreeing on the words of `T'` runs the loop to the same result. `AtOff`, `vspace.asid_table.eq` (the ASID-table
  word `asid_table` reads), **`vspace.find_asid_raw.congr`**, **`ept.find.congr`** (a `VsKeep` step with the same
  `ks` base: same results).
* **`PtFnd.vk`**: `PtFnd` along a `VsKeep` step with the same `ks` base (e.g. `set_thread_state`, `stt_vk`): the
  descriptors naming `ptr` after were there before (`S2Nm.vsz`, `VsNm.vsz`), and every walk of the fact is
  instantiated at the reachable tables (`S2Rt` / `VsRt`), whose words the step keeps.
* **`set_cap_ptu`**: `set_cap` of the unmapped `PageTable p false 0 0` into an `OS` slot (`p` canonical, e.g. by
  `canon_pt`): `VsKeep`, the other `OS` caps and `ks` kept, the slot decodes back to exactly that cap
  (`CapRt.decode_encode`).
* `zr_ptw`, `wa_fit`: `zero(p, 4096)` keeps the aligned words that are no word of `p`, zeroes those that are.
* **`vspace.decode_page_table.unmapR`** (vspace.rs:1094–1107, `decode_page_table` at `ARMPageTableUnmap` with a
  mapped `PageTable` cap): the state unchanged (not final), or `ks`, `VsTyR ∧ S2TyR` over the same `Tb` / `Te`,
  `UnmZ` over the reachable Stage-2 objects, `UnmT` over the reachable Stage-1 tables and `UnmU` of the end state
  (`PtFnd.vk`, `vspace.unmap_page_table.unr`, `zero`, `set_cap_ptu`, `unmapR.post`). Case facts / hypotheses at the
  decode's start state: `PtFnd` (for the cap's `(asid, vaddr)`), `hone` (no other `OS` slot names `ptr`: what
  `is_final_capability` gives under the MDB same-range adjacency, still owed to `RngOneA64`), the placement `hptr`
  (`ptr ∈ Pt`), `hal` / `hfit` (aligned, no wrap), `hD2` / `hD1` (`ptr`'s words meet no other `Te` object / `Tb`
  table; `hD1` also gives gen 43's "no `R + 4088` word" side condition, since `ptr` is no `HighVSpace` root by
  `PtFnd.root`).
* **`vspace.decode_page_table.unmapR0`** (the same with an unmapped `PageTable` cap: no walk, no zeroing): the same
  post from the typings alone (`UnmZ` gives the object's placement and zero words, `UnmU.one` that the slot holds
  its only cap).

No named premise; new definitions and theorems only.
-/
import Fl4ProofsA64.P1.QueueUnmR
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

/-! ## Loop congruence -/

/-- **Two loops with bodies equal on an invariant** (preserved by the second body with a decreasing measure) are
equal. -/
theorem loopD_congr {α β : Type} {f g : α → Result (ControlFlow α β)} (I : α → Prop) (μ : α → Nat)
    (hfg : ∀ x, I x → g x = f x)
    (hI : ∀ x, I x → f x ⦃ cf => ∀ y, cf = ControlFlow.cont y → I y ∧ μ y < μ x ⦄) :
    ∀ x, I x → loop g x = loop f x := by
  intro x
  induction hn : μ x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    intro hx
    conv_lhs => rw [loop]
    conv_rhs => rw [loop]
    rw [hfg x hx]
    obtain ⟨cf, hcf, hp⟩ := spec_exists_u (hI x hx)
    rw [hcf, bind_ok, bind_ok]
    cases cf with
    | done y => rfl
    | cont y =>
      obtain ⟨hy, hlt⟩ := hp y rfl
      exact ih (μ y) (hn ▸ hlt) y rfl hy

section walk
variable {kb n : U64} {Pp Tb Pt Hr Te : Set U64} {Lv Re bits : U64 → Nat}

/-! ## The walks read only the words of their tables -/

theorem ept.unmap_table_loop.body_congr {s s1 : S} (ipa pt t sh m rm : U64) (hm : m.val ≤ 1023)
    (hr : ∀ o : U64, o.val ≤ m.val * 8 → o.val % 8 = 0 → L.mem s1 (wa t o) = L.mem s (wa t o)) :
    ept.unmap_table_loop.body st s1 ipa pt t sh m rm = ept.unmap_table_loop.body st s ipa pt t sh m rm := by
  unfold ept.unmap_table_loop.body
  obtain ⟨sl, hsl, o, ho, h8, rfl⟩ := spec_exists_u (ept.entry_addr.off t ipa sh m hm)
  simp only [hsl, bind_ok, L.read_eq, hr o ho h8]

set_option maxHeartbeats 2000000 in
theorem ept.unmap_table_loop.body_inv {T' : Set U64} {s : S} (h2 : S2Ty st n Pp Hr T' Re bits s)
    (hS : S2OK T' bits Hr) (ipa pt t sh m rm : U64) (hx : UtI T' Re bits (t, sh, m, rm)) :
    ept.unmap_table_loop.body st s ipa pt t sh m rm ⦃ cf => ∀ y, cf = ControlFlow.cont y →
      UtI T' Re bits y ∧ y.2.2.2.val < rm.val ⦄ := by
  obtain ⟨ht, hre, hm, hm'⟩ := hx
  try simp only at ht hre hm hm'
  unfold ept.unmap_table_loop.body
  split
  · rename_i hpos
    have hpos' : 0 < rm.val := by first | simpa using hpos | scalar_tac
    refine WP.spec_bind (ept.entry_addr.off t ipa sh m hm') fun sl hsl => ?_
    obtain ⟨o, ho, h8, e⟩ := hsl
    subst e
    rw [L.read_eq, bind_ok]
    refine WP.spec_bind (ept.is_table.tag _ sh) fun b hb => ?_
    split
    · rename_i hbt
      obtain ⟨hT', hR'⟩ := h2.desc t ht (by omega) o (by omega) h8 (hb hbt)
      simp only [lift, bind_ok, ept.table_of, layout.pptr]
      split
      · exact (WP.spec_ok _).2 fun y e' => by cases e'
      · try simp only [lift, bind_ok]
        step as ⟨rm1, hrm1⟩
        try simp only [lift, bind_ok]
        try rw [WP.spec_ok]
        rintro y e'
        cases e'
        have hpw := pow_bits (hS.sz _ hT')
        have h511 : (511#u64 : U64).val = 511 := by simp
        refine ⟨hT', ?_, ?_, ?_, ?_⟩
        all_goals first | omega | (simp only [h511]; omega) | (simp only; omega) | simp [h511]
    · exact (WP.spec_ok _).2 fun y e' => by cases e'
  · exact (WP.spec_ok _).2 fun y e' => by cases e'

/-- **The `unmap_table` walk reads only words of its tables**: at a typing over `T'`, a state agreeing on the
words of `T'` runs it to the same result. -/
theorem ept.unmap_table_loop.congr {T' : Set U64} {s s1 : S} (h2 : S2Ty st n Pp Hr T' Re bits s)
    (hS : S2OK T' bits Hr) (hr : ∀ b, PtWb T' bits b → L.mem s1 b = L.mem s b)
    (ipa pt t sh m rm : U64) (hx : UtI T' Re bits (t, sh, m, rm)) :
    ept.unmap_table_loop st s1 ipa pt t sh m rm = ept.unmap_table_loop st s ipa pt t sh m rm := by
  unfold ept.unmap_table_loop
  refine loopD_congr (UtI T' Re bits) (fun x => x.2.2.2.val) ?_ ?_ _ hx
  · rintro ⟨t', sh', m', rm'⟩ hx'
    obtain ⟨ht, -, hm, hm'⟩ := hx'
    try simp only at ht hm hm'
    exact ept.unmap_table_loop.body_congr ipa pt t' sh' m' rm' hm' fun o ho h8 =>
      hr _ ⟨t', ht, o, by omega, h8, rfl⟩
  · rintro ⟨t', sh', m', rm'⟩ hx'
    exact ept.unmap_table_loop.body_inv h2 hS ipa pt t' sh' m' rm' hx'

theorem vspace.unmap_page_table_loop.body_congr {s s1 : S} (vaddr pt t sh lv : U64)
    (hr : lv.val < 3 → ∀ o : U64, o.val < 4096 → o.val % 8 = 0 → L.mem s1 (wa t o) = L.mem s (wa t o)) :
    vspace.unmap_page_table_loop.body st s1 vaddr pt t sh lv =
      vspace.unmap_page_table_loop.body st s vaddr pt t sh lv := by
  unfold vspace.unmap_page_table_loop.body
  by_cases hl : lv < 3#u64
  · have hl' : lv.val < 3 := by first | simpa using hl | scalar_tac
    obtain ⟨sl, hsl, o, ho, h8, rfl⟩ := spec_exists_u (vspace.entry_addr.off t vaddr sh)
    rw [if_pos hl, if_pos hl]
    simp only [hsl, bind_ok, L.read_eq, hr hl' o ho h8]
  · rw [if_neg hl, if_neg hl]

set_option maxHeartbeats 2000000 in
theorem vspace.unmap_page_table_loop.body_inv {T' : Set U64} {s : S} (h : VsTy st kb Pp T' Lv s)
    (vaddr pt t sh lv : U64) (hx : UpI T' Lv (t, sh, lv)) :
    vspace.unmap_page_table_loop.body st s vaddr pt t sh lv ⦃ cf => ∀ y, cf = ControlFlow.cont y →
      UpI T' Lv y ∧ 3 - y.2.2.val < 3 - lv.val ⦄ := by
  obtain ⟨hl3, hT⟩ := hx
  try simp only at hl3 hT
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
      · exact (WP.spec_ok _).2 fun y e' => by cases e'
      · try simp only [lift, bind_ok]
        step as ⟨lv1, hlv1⟩
        try simp only [lift, bind_ok]
        try rw [WP.spec_ok]
        rintro y e'
        cases e'
        refine ⟨?_, fun _ => ⟨hT', ?_⟩, ?_⟩
        · try simp only
          omega
        · try simp only
          rw [hL', hlv]; omega
        · try simp only
          omega
    · exact (WP.spec_ok _).2 fun y e' => by cases e'
  · exact (WP.spec_ok _).2 fun y e' => by cases e'

/-- **The Stage-1 `unmap_page_table` walk reads only words of its tables.** -/
theorem vspace.unmap_page_table_loop.congr {T' : Set U64} {s s1 : S} (h : VsTy st kb Pp T' Lv s)
    (hr : ∀ b, PtW T' b → L.mem s1 b = L.mem s b) (vaddr pt t sh lv : U64) (hx : UpI T' Lv (t, sh, lv)) :
    vspace.unmap_page_table_loop st s1 vaddr pt t sh lv = vspace.unmap_page_table_loop st s vaddr pt t sh lv := by
  unfold vspace.unmap_page_table_loop
  refine loopD_congr (UpI T' Lv) (fun x => 3 - x.2.2.val) ?_ ?_ _ hx
  · rintro ⟨t', sh', lv'⟩ hx'
    obtain ⟨-, hT⟩ := hx'
    exact vspace.unmap_page_table_loop.body_congr vaddr pt t' sh' lv' fun hl o ho h8 =>
      hr _ ⟨t', (hT hl).1, o, ho, h8, rfl⟩
  · rintro ⟨t', sh', lv'⟩ hx'
    exact vspace.unmap_page_table_loop.body_inv h vaddr pt t' sh' lv' hx'

/-! ## The ASID lookups -/

/-- The ASID-table offset `asid_table st s i` reads (from the `ks` base). -/
def AtOff (i : U64) : U64 := wa 772352#u64 (core.num.U64.wrapping_mul (i &&& 127#u64) 8#u64)

theorem AtOff.v (i : U64) : 772352 ≤ (AtOff i).val ∧ (AtOff i).val < 773376 ∧ (AtOff i).val % 8 = 0 := by
  unfold AtOff
  have : (i.val &&& 127) ≤ 127 := Nat.and_le_right
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits] <;> omega

theorem vspace.asid_table.eq (s : S) (i : U64) :
    vspace.asid_table st s i = ok (L.mem s (wa (L.ksb s) (AtOff i))) := by
  apply eq_of_spec_fd
  unfold vspace.asid_table AtOff
  rw [eq_of_spec_fd P0.Consts.vspace.N_ASID_POOLS.spec, eq_of_spec_fd P0.Consts.layout.ks.ASID_TABLE.spec]
  step as ⟨i1, hi1⟩
  try (have e1 : i1 = 127#u64 := UScalar.eq_of_val_eq (by scalar_tac)
       subst e1)
  simp only [lift, bind_ok]
  exact obj.ks_get.spec s _

/-- **`find_asid_raw` along a `VsKeep` step with the same `ks` base** returns the same result. -/
theorem vspace.find_asid_raw.congr {s s1 : S} (h : VsTyR st kb Pp Hr Tb Lv s) (hk : L.ksb s = kb)
    (hks : L.ksb s1 = L.ksb s) (hPp : Pp ⊆ Pt) (k : VsKeep st kb Pt s s1) (asid : U64) :
    vspace.find_asid_raw st s1 asid = vspace.find_asid_raw st s asid := by
  have hw : ∀ i, L.mem s1 (wa (L.ksb s) (AtOff i)) = L.mem s (wa (L.ksb s) (AtOff i)) := fun i => by
    obtain ⟨h1, h2, h8⟩ := AtOff.v i
    exact k _ (Or.inr ⟨AtOff i, h1, h2, h8, by rw [hk]⟩)
  have hrd : ∀ i, ¬ L.mem s (wa (L.ksb s) (AtOff i)) = 0#u64 →
      L.mem s1 (wa (L.mem s (wa (L.ksb s) (AtOff i))) (core.num.U64.wrapping_mul (asid &&& 511#u64) 8#u64)) =
        L.mem s (wa (L.mem s (wa (L.ksb s) (AtOff i))) (core.num.U64.wrapping_mul (asid &&& 511#u64) 8#u64)) := by
    intro i hne
    obtain ⟨h1, h2, h8⟩ := AtOff.v i
    have hp : L.mem s (wa (L.ksb s) (AtOff i)) ∈ Pp := by
      rw [hk] at hne ⊢; exact h.tbl _ h1 h2 h8 hne
    refine k _ (Or.inl ⟨_, hPp hp, _, ?_, ?_, rfl⟩)
    · rw [mul8_val (and511 asid)]; have := and511 asid; omega
    · rw [mul8_val (and511 asid)]; omega
  unfold vspace.find_asid_raw
  simp only [vspace.asid_table.eq, hks, hw, bind_ok, lift, L.read_eq]
  congr 1; funext i
  by_cases h1 : (i != 0#u64) = true
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1]
    congr 1; funext i1
    by_cases h0 : L.mem s (wa (L.ksb s) (AtOff i1)) = 0#u64
    · rw [if_pos h0, if_pos h0]
    · rw [if_neg h0, if_neg h0, hrd i1 h0]

/-- **`ept::find` along a `VsKeep` step with the same `ks` base** returns the same result. -/
theorem ept.find.congr {s s1 : S} (h : VsTyR st kb Pp Hr Tb Lv s) (hk : L.ksb s = kb)
    (hks : L.ksb s1 = L.ksb s) (hPp : Pp ⊆ Pt) (k : VsKeep st kb Pt s s1) (asid : U64) :
    ept.find st s1 asid = ept.find st s asid := by
  unfold ept.find
  rw [vspace.find_asid_raw.congr h hk hks hPp k asid]

/-! ## `PtFnd` along a `VsKeep` step -/

set_option maxHeartbeats 2000000 in
/-- **`PtFnd` along a `VsKeep` step with the same `ks` base** (e.g. `set_thread_state`): the walks of the fact read
only words of reachable tables, pool words and ASID-table words. -/
theorem PtFnd.vk {s s1 : S} (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hTe : Gran Te bits ⊆ Pt) (hS : S2OK Te bits Hr)
    (hH : HrOK kb Pp Tb Lv Hr) (h0 : VsTyR st kb Pp Hr Tb Lv s) (h2 : S2TyR st n Pp Hr Te Re bits s)
    (hk : L.ksb s = kb) (hks : L.ksb s1 = L.ksb s) (k : VsKeep st kb Pt s s1) {asid vaddr ptr : U64}
    (hF : PtFnd st n Pp Hr Lv Re bits s asid vaddr ptr) : PtFnd st n Pp Hr Lv Re bits s1 asid vaddr ptr := by
  have z : VsZ st kb Pt s s1 := VsKeep.vsz k
  have hraw := vspace.find_asid_raw.congr h0 hk hks hPp k asid
  have hfind := ept.find.congr h0 hk hks hPp k asid
  refine ⟨NoRoot.vsz hPp hF.root z, fun b hb => ?_, fun b hb => ?_⟩
  · obtain ⟨r1, root, g, hr, h1, hf, hg, hl⟩ := hF.s2 b (S2Nm.vsz hPp hTe hS h2 z hb).1
    refine ⟨r1, root, g, by rw [hraw]; exact hr, h1, by rw [hfind]; exact hf, hg, ?_⟩
    have hft := ept.find.tyR h0 h2 hk asid
    rw [hf, WP.spec_ok] at hft
    obtain ⟨hT, hre, hrb⟩ := hft root rfl
    have hgv := ept.geom.v n
    rw [hg, WP.spec_ok] at hgv
    obtain ⟨hl3, hm, hm'⟩ := hgv
    have h3 := s2lv_ge n
    have hsub := wsub1_le (x := g.levels) (by omega)
    have hpb : 2 ^ s2rb n ≤ 2 ^ bits root := Nat.pow_le_pow_right (by norm_num) hrb
    have hi : UtI (S2Rt st Pp Te Re bits s) Re bits
        (root, g.top_shift, g.top_mask, core.num.U64.wrapping_sub g.levels 1#u64) :=
      ⟨hT, by simp only; rw [hsub]; omega, by simp only; omega, hm'⟩
    rw [ept.unmap_table_loop.congr h2.sub (S2OK.sub hS S2Rt_sub)
      (fun b' hb' => k b' (Or.inl (ptw_mono hTe (ptwb_gran hS.sz (ptwb_mono S2Rt_sub hb'))))) _ _ _ _ _ _ hi]
    exact hl
  · obtain ⟨r1, t, sh, lv, hr, h1, hst, hl⟩ := hF.s1 b (VsNm.vsz hPp hTb hH.sub h0 z hb).1
    have hr1 := vspace.find_asid_raw.ty h0.sub hk asid
    rw [hr, WP.spec_ok] at hr1
    obtain ⟨p, hp, o, ho, h8, er, hr0⟩ := hr1 r1 rfl
    have hth := h2.tag p hp o ho h8 (by rw [← er]; exact hr0)
    have hpl := h0.pool p hp o ho h8 (by rw [← er]; exact hr0)
    rw [← er] at hth hpl
    have hR2 : (r1 &&& 3#u64) = 2#u64 → (r1 &&& ~~~3#u64) ∈ Hr := fun h2' => by
      rcases hth with ⟨e0, -⟩ | ⟨-, hR⟩ | ⟨e1, -⟩
      · rw [e0] at h2'; exact absurd h2' (by decide)
      · exact hR
      · rw [e1] at h2'; exact absurd h2' (by decide)
    have hi : UpI (VsRt st Pp Hr Tb Lv s) Lv (t, sh, lv) := by
      rcases hst with ⟨h2', rfl, rfl, rfl⟩ | ⟨hn2, rfl, rfl, rfl⟩
      · have hR := hR2 h2'
        have hRT := hH.sub hR
        have hL0 := hH.lv _ hR
        have he := h2.hi _ hR
        obtain ⟨hT1, hL1⟩ := h0.desc _ hRT (VsReach.hr hR) (by omega) 4088#u64 (by simp) (by simp) he
        refine ⟨by simp, fun _ => ⟨⟨hT1, VsReach.step (VsReach.hr hR) (by omega) (by simp) (by simp) he⟩, ?_⟩⟩
        simp only; rw [hL1, hL0]; simp
      · have h0' : (r1 &&& 3#u64) = 0#u64 := by
          rcases hth with ⟨e0, -⟩ | ⟨e2, -⟩ | ⟨e1, -⟩
          · exact e0
          · exact absurd e2 hn2
          · exact absurd e1 h1
        rw [and_not_of r1 3#u64 h0']
        obtain ⟨hT0, hL0⟩ := hpl.1 h0'
        have hre : VsReach st Pp Hr Lv s r1 := by
          have := VsReach.root0 (st := st) (Pp := Pp) (Hr := Hr) (Lv := Lv) (s := s) hp ho h8
            (by rw [← er]; exact hr0) (by rw [← er]; exact h0')
          rw [← er] at this; exact this
        refine ⟨by simp, fun _ => ⟨⟨hT0, hre⟩, ?_⟩⟩
        simp only; rw [hL0]; simp
    have hloop : vspace.unmap_page_table_loop st s1 vaddr ptr t sh lv = ok (some b) := by
      rw [vspace.unmap_page_table_loop.congr h0.sub
        (fun b' hb' => k b' (Or.inl (ptw_mono (VsRt_sub.trans hTb) hb'))) _ _ _ _ _ hi]
      exact hl
    refine ⟨r1, t, sh, lv, by rw [hraw]; exact hr, h1, ?_, hloop⟩
    rcases hst with ⟨h2', ht, hsh, hlv⟩ | hst
    · exact Or.inl ⟨h2', by rw [ht, k _ (hr_vsr hTb hH (hR2 h2'))], hsh, hlv⟩
    · exact Or.inr hst

end walk

/-! ## Store steps -/

section store
variable {OS Vc Ub : Set U64} {kb : U64} {Pt : Set U64}

/-- **`set_cap` of the unmapped `PageTable p false 0 0`** into a slot of `OS`: the exact round trip. -/
theorem set_cap_ptu (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hO : OSOK T Ω Sg OS) {x p : U64} (hx : x ∈ OS)
    (hp : CapRt.Canonical p) (s : S) :
    obj.Slot.set_cap st x s (.PageTable p false 0#u64 0#u64) ⦃ s' => VsKeep st kb Pt s s' ∧
      (∀ y ∈ OS, y ≠ x → obj.Slot.cap st y s' = obj.Slot.cap st y s) ∧
      obj.Slot.cap st x s' = ok (.PageTable p false 0#u64 0#u64) ∧ L.ksb s' = L.ksb s ⦄ := by
  obtain ⟨w0, w1, he, hd⟩ := CapRt.decode_encode (.PageTable p false 0#u64 0#u64)
    ⟨hp, by simp, Or.inl fun j hj _ => by simp⟩
  rw [set_cap_eq he, WP.spec_ok]
  obtain ⟨k, c2o, c2x⟩ := wr2_cap (st := st) (s := s) hR hO hx (w0 := w0) (w1 := w1)
  exact ⟨k, c2o, by rw [c2x, hd], by rw [L.ksb_wr, L.ksb_wr]⟩

theorem wa_fit {p o : U64} (hfit : p.val + 4096 ≤ 2 ^ 64) (ho : o.val < 4096) : (wa p o).val = p.val + o.val := by
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega

/-- `zero(p, 4096)` keeps an aligned word that is no word of `p`. -/
theorem zr_ptw {s : S} {p : U64} (hp : Aligned p) (hfit : p.val + 4096 ≤ 2 ^ 64) {b : U64} (hb : Aligned b)
    (hn : ¬ ∃ o : U64, o.val < 4096 ∧ o.val % 8 = 0 ∧ b = wa p o) : L.mem (L.zr s p 4096#u64) b = L.mem s b := by
  rw [L.mem_zr s p 4096#u64 b hp (by simp) (by simpa using hfit) hb]
  split
  · rename_i hin
    exfalso
    have h4 : (4096#u64 : U64).val = 4096 := rfl
    have hb8 : b.val % 8 = 0 := hb
    have hp8 : p.val % 8 = 0 := hp
    obtain ⟨e, hv⟩ := wa_sub_of_le (p := p) (b := b) hin.1
    exact hn ⟨_, by rw [hv]; omega, by rw [hv]; omega, e.symm⟩
  · rfl

/-- `zero(p, 4096)` zeroes the words of `p`. -/
theorem zr_ptw0 {s : S} {p : U64} (hp : Aligned p) (hfit : p.val + 4096 ≤ 2 ^ 64) {o : U64} (ho : o.val < 4096)
    (h8 : o.val % 8 = 0) : L.mem (L.zr s p 4096#u64) (wa p o) = 0#u64 := by
  have hv := wa_fit hfit ho
  have hp8 : p.val % 8 = 0 := hp
  have hb : Aligned (wa p o) := by show (wa p o).val % 8 = 0; rw [hv]; omega
  rw [L.mem_zr s p 4096#u64 _ hp (by simp) (by simpa using hfit) hb, if_pos]
  have h4 : (4096#u64 : U64).val = 4096 := rfl
  rw [hv, h4]; omega

end store

/-! ## ARMPageTableUnmap at decode level -/

section dec
variable {OS Vc Ub : Set U64} {kb n : U64} {Pp Tb Pt Hr Te : Set U64} {Lv Re bits : U64 → Nat}
variable {A : Type _} {ar : machine.Arch A}

set_option maxHeartbeats 4000000 in
/-- **ARMPageTableUnmap of a mapped `PageTable` cap at decode level** (vspace.rs:1094–1107; module docstring): the
state unchanged (the cap not final), or `ks`, `VsTyR ∧ S2TyR` over the same `Tb` / `Te`, `UnmZ` over the reachable
Stage-2 objects, `UnmT` over the reachable Stage-1 tables and `UnmU` of the end state. -/
theorem vspace.decode_page_table.unmapR (hA : P0.ArchTotal ar) (hPl : ArchPlat ar)
    (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hO : OSOK T Ω Sg OS)
    {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) (hk : L.ksb s = kb) (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt)
    (hTe : Gran Te bits ⊆ Pt) (hH : HrOK kb Pp Tb Lv Hr) (hS : S2OK Te bits Hr)
    (hY : VsTyR st kb Pp Hr Tb Lv s) (h2 : S2TyR st hPl.ipa Pp Hr Te Re bits s)
    (hU : UnmZ st OS Pt (S2Rt st Pp Te Re bits s) bits s) (hT : UnmT st OS (VsRt st Pp Hr Tb Lv s) s)
    (hV : UnmU st OS Pp s)
    (a : A) (len slot buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) {ptr masid mvaddr : U64}
    (hsl : slot ∈ OS) (hc : obj.Slot.cap st slot s = ok (.PageTable ptr true masid mvaddr))
    (hF : PtFnd st hPl.ipa Pp Hr Lv Re bits s masid mvaddr ptr)
    (hone : ∀ y ∈ OS, y ≠ slot → ¬ NmC st y ptr s)
    (hptr : ptr ∈ Pt) (hal : Aligned ptr) (hfit : ptr.val + 4096 ≤ 2 ^ 64)
    (hD2 : ∀ q ∈ Te, q ≠ ptr → ∀ o o' : U64, o.val < 4096 → o.val % 8 = 0 → o'.val < 2 ^ bits q →
      o'.val % 8 = 0 → wa q o' ≠ wa ptr o)
    (hD1 : ∀ q ∈ Tb, q ≠ ptr → ∀ o o' : U64, o.val < 4096 → o.val % 8 = 0 → o'.val < 4096 → o'.val % 8 = 0 →
      wa q o' ≠ wa ptr o) :
    vspace.decode_page_table st ar s a fl4_abi.label.ARMPageTableUnmap len slot
      (.PageTable ptr true masid mvaddr) buf extra ⦃ r => r.2.1 = s ∨
        (L.ksb r.2.1 = kb ∧ VsTyR st kb Pp Hr Tb Lv r.2.1 ∧ S2TyR st hPl.ipa Pp Hr Te Re bits r.2.1 ∧
          UnmZ st OS Pt (S2Rt st Pp Te Re bits r.2.1) bits r.2.1 ∧ UnmT st OS (VsRt st Pp Hr Tb Lv r.2.1) r.2.1 ∧
          UnmU st OS Pp r.2.1) ⦄ := by
  have hS' : P0.StoreTotal st := L.total
  have hRal : ∀ R ∈ Hr, Aligned (wa R 4088#u64) := fun R hR' => hR.al _ (hr_vsr hTb hH hR')
  have hh : ∀ R ∈ Hr, ∀ o : U64, o.val < 4096 → o.val % 8 = 0 → wa ptr o ≠ wa R 4088#u64 :=
    fun R hR' o ho h8 e => hD1 R (hH.sub hR') (fun e' => hF.root.1 (e' ▸ hR')) o 4088#u64 ho h8 (by simp) (by simp)
      e.symm
  have hX0 : TbO (VsRt st Pp Hr Tb Lv s) Hr ∪ Gran (S2Rt st Pp Te Re bits s) bits ⊆ Pt :=
    Set.union_subset (fun _ h => hTb h.1.1) ((gran_mono S2Rt_sub).trans hTe)
  unfold vspace.decode_page_table
  refine WP.spec_bind (sched.cur_thread.spec s) fun ct ect => ?_
  have hct : ct ∈ T := by rw [ect]; exact q.curT
  try dsimp only
  refine spec_ite (fun _ => ?_) (fun hne => absurd rfl hne)
  refine WP.spec_bind (P0.cdt.is_final_capability.p0 st s slot hS') fun b _ => ?_
  refine spec_ite (fun _ => ?_) (fun _ => (WP.spec_ok _).2 (Or.inl rfl))
  refine WP.spec_bind (stt_vk hR q hct) fun s1 ⟨w1, k1⟩ => ?_
  have hks1 : L.ksb s1 = L.ksb s := w1.1
  have hk1 : L.ksb s1 = kb := by rw [hks1, hk]
  have z1 : VsZ st kb Pt s s1 := VsKeep.vsz k1
  have hw1 : HrW st Hr s s1 := fun R hR' => k1 _ (hr_vsr hTb hH hR')
  have hY1 : VsTyR st kb Pp Hr Tb Lv s1 := VsTyR.keepZ hPp hTb hH.sub hY z1
  have h21 : S2TyR st hPl.ipa Pp Hr Te Re bits s1 := S2TyR.keep hPp hTe hS h2 z1 hw1
  have hF1 := PtFnd.vk hPp hTb hTe hS hH hY h2 hk hks1 k1 hF
  have hc1 := stt_capk hO q hct w1
  have hsub2 : S2Rt st Pp Te Re bits s1 ⊆ S2Rt st Pp Te Re bits s :=
    fun p hp => ⟨hp.1, S2Reach.vsz hPp hTe hS h2 z1 hp.2⟩
  have hsub1 : VsRt st Pp Hr Tb Lv s1 ⊆ VsRt st Pp Hr Tb Lv s :=
    fun p hp => ⟨hp.1, VsReach.vsz hPp hTb hH.sub hY z1 hp.2⟩
  have hsubT : TbO (VsRt st Pp Hr Tb Lv s1) Hr ⊆ TbO (VsRt st Pp Hr Tb Lv s) Hr :=
    fun q hq => (⟨hsub1 hq.1, hq.2⟩ : q ∈ TbO (VsRt st Pp Hr Tb Lv s) Hr)
  have hX1 : ∀ b, PtW (TbO (VsRt st Pp Hr Tb Lv s1) Hr ∪ Gran (S2Rt st Pp Te Re bits s1) bits) b →
      PtW (TbO (VsRt st Pp Hr Tb Lv s) Hr ∪ Gran (S2Rt st Pp Te Re bits s) bits) b := fun b hb =>
    ptw_mono (Set.union_subset_union hsubT (gran_mono hsub2)) hb
  have hX1P : TbO (VsRt st Pp Hr Tb Lv s1) Hr ∪ Gran (S2Rt st Pp Te Re bits s1) bits ⊆ Pt :=
    Set.union_subset (fun _ h => hTb h.1.1) ((gran_mono S2Rt_sub).trans hTe)
  have hal1 : ∀ b, PtW (TbO (VsRt st Pp Hr Tb Lv s1) Hr ∪ Gran (S2Rt st Pp Te Re bits s1) bits) b → Aligned b :=
    fun b hb => hR.al b (Or.inl (ptw_mono hX1P hb))
  refine WP.spec_bind (Pₘ := fun r : S × A => ∃ s3 : S, VsZ st kb Pt s s3 ∧ HrW st Hr s s3 ∧
      (¬ ∃ b, S2Nm st Pp Re bits s3 ptr b) ∧ (¬ ∃ b, VsNm st Pp Hr Lv s3 ptr b) ∧
      r.1 = L.zr s3 ptr 4096#u64 ∧ (∀ x ∈ OS, obj.Slot.cap st x s3 = obj.Slot.cap st x s) ∧ L.ksb s3 = kb ∧
      ∀ b, VsR kb Pt b → ¬ PtW (TbO (VsRt st Pp Hr Tb Lv s) Hr ∪ Gran (S2Rt st Pp Te Re bits s) bits) b →
        L.mem s3 b = L.mem s b) ?_ ?_
  · split
    · refine WP.spec_bind (vspace.unmap_page_table.unr hA hPl hH hS hR.al hPp hTb hTe hY1 h21 hk1 a hF1) ?_
      rintro ⟨s3, a2⟩ ⟨w3, hn2, hn1⟩
      try simp only [uncurry_apply_pair]
      refine WP.spec_bind (LawfulStore.zero_spec s3 ptr 4096#u64) fun s4 e4 => ?_
      have ww := Wr0.w hal1 w3
      refine (WP.spec_ok _).2 ⟨s3, z1.trans (Wr0.vsz hR.al hX1P w3), fun R hR' => ?_, hn2, hn1, e4,
        fun x hx => ?_, by rw [ww.1, hk1], fun b hb hn => ?_⟩
      · exact (Wr0.hrw hal1 hRal (fun b hb => s2_ne (hH.mono VsRt_sub (hr_rt hH.sub)) (S2OK.sub hS S2Rt_sub) hb)
          w3 R hR').trans (hw1 R hR')
      · exact (capk_vsr hR hO (ww.mono fun b hb => Or.inl (ptw_mono hX1P hb)) x hx).trans (hc1 x hx)
      · rw [ww.mem_eq (hR.al b hb) (fun h => hn (hX1 b h))]
        exact k1 b hb
    · rename_i hn; exact absurd rfl hn
  rintro ⟨s4, a1⟩ ⟨s3, z3, hk3, hn2, hn1, e4, hc3, hks3, hm3⟩
  obtain rfl : s4 = L.zr s3 ptr 4096#u64 := e4
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (set_cap_ptu (kb := kb) (Pt := Pt) hR hO hsl (canon_pt hc) _) fun s5 ⟨k5, c5o, c5x, hk5'⟩ => ?_
  have hz4w : WritesIn st s3 (L.zr s3 ptr 4096#u64) (VsR kb Pt) :=
    ⟨L.ksb_zr _ _ _, L.cpu_zr _ _ _, fun b hb hn =>
      zr_ptw hal hfit hb fun ⟨o, ho, h8, e⟩ => hn (Or.inl ⟨ptr, hptr, o, ho, h8, e⟩)⟩
  have z5 : VsZ st kb Pt s3 s5 := (zr_vsz hR.al hal hfit).trans (VsKeep.vsz k5)
  have hk5 : HrW st Hr s s5 := fun R hR' =>
    (k5 _ (hr_vsr hTb hH hR')).trans ((zr_hrw hRal hal hfit hh R hR').trans (hk3 R hR'))
  have hc5 : ∀ x ∈ OS, x ≠ slot → obj.Slot.cap st x s5 = obj.Slot.cap st x s := fun x hx hne =>
    (c5o x hx hne).trans ((capk_vsr hR hO hz4w x hx).trans (hc3 x hx))
  have hz : ∀ o : U64, o.val < 4096 → o.val % 8 = 0 → L.mem s5 (wa ptr o) = 0#u64 := fun o ho h8 => by
    rw [k5 _ (Or.inl ⟨ptr, hptr, o, ho, h8, rfl⟩)]
    exact zr_ptw0 hal hfit ho h8
  have hm : ∀ b, VsR kb Pt b → ¬ (PtW (TbO (VsRt st Pp Hr Tb Lv s) Hr ∪ Gran (S2Rt st Pp Te Re bits s) bits) b ∨
      ∃ o : U64, o.val < 4096 ∧ o.val % 8 = 0 ∧ b = wa ptr o) → L.mem s5 b = L.mem s b := fun b hb hn => by
    rw [k5 b hb, zr_ptw hal hfit (hR.al b hb) (fun h => hn (Or.inr h))]
    exact hm3 b hb (fun h => hn (Or.inl h))
  obtain ⟨y5, t5, u5, v5, w5⟩ := unmapR.post hPp hTb hTe hS hH.sub hsl hY h2 hU hT hV hF.root z3 hk3 hn2 hn1 z5 hk5
    hc5 ⟨0#u64, 0#u64, c5x⟩ ⟨true, masid, mvaddr, hc⟩ hone hptr hz hm hD2 hD1
  exact (WP.spec_ok _).2 (Or.inr ⟨by rw [hk5', L.ksb_zr, hks3], y5, t5, u5, v5, w5⟩)

set_option maxHeartbeats 4000000 in
/-- **ARMPageTableUnmap of an unmapped `PageTable` cap at decode level**: no walk and no zeroing, the cap rewritten
`PageTable ptr false 0 0`; the state unchanged, or `ks`, `VsTyR ∧ S2TyR`, `UnmZ` / `UnmT` over the reachable parts
and `UnmU` of the end state — no case hypothesis beyond the typings (the cap's object is placed and zero by `UnmZ`,
and is its only cap by `UnmU`). -/
theorem vspace.decode_page_table.unmapR0 (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hO : OSOK T Ω Sg OS)
    {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) (hk : L.ksb s = kb) (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt)
    (hTe : Gran Te bits ⊆ Pt) (hH : HrOK kb Pp Tb Lv Hr) (hS : S2OK Te bits Hr)
    (hY : VsTyR st kb Pp Hr Tb Lv s) (h2 : S2TyR st n Pp Hr Te Re bits s)
    (hU : UnmZ st OS Pt (S2Rt st Pp Te Re bits s) bits s) (hT : UnmT st OS (VsRt st Pp Hr Tb Lv s) s)
    (hV : UnmU st OS Pp s)
    (a : A) (len slot buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) {ptr masid mvaddr : U64}
    (hsl : slot ∈ OS) (hc : obj.Slot.cap st slot s = ok (.PageTable ptr false masid mvaddr)) :
    vspace.decode_page_table st ar s a fl4_abi.label.ARMPageTableUnmap len slot
      (.PageTable ptr false masid mvaddr) buf extra ⦃ r => r.2.1 = s ∨
        (L.ksb r.2.1 = kb ∧ VsTyR st kb Pp Hr Tb Lv r.2.1 ∧ S2TyR st n Pp Hr Te Re bits r.2.1 ∧
          UnmZ st OS Pt (S2Rt st Pp Te Re bits r.2.1) bits r.2.1 ∧ UnmT st OS (VsRt st Pp Hr Tb Lv r.2.1) r.2.1 ∧
          UnmU st OS Pp r.2.1) ⦄ := by
  have hS' : P0.StoreTotal st := L.total
  unfold vspace.decode_page_table
  refine WP.spec_bind (sched.cur_thread.spec s) fun ct ect => ?_
  have hct : ct ∈ T := by rw [ect]; exact q.curT
  try dsimp only
  refine spec_ite (fun _ => ?_) (fun hne => absurd rfl hne)
  refine WP.spec_bind (P0.cdt.is_final_capability.p0 st s slot hS') fun b _ => ?_
  refine spec_ite (fun _ => ?_) (fun _ => (WP.spec_ok _).2 (Or.inl rfl))
  refine WP.spec_bind (stt_vk hR q hct) fun s1 ⟨w1, k1⟩ => ?_
  have hks1 : L.ksb s1 = L.ksb s := w1.1
  have hc1 := stt_capk hO q hct w1
  refine WP.spec_bind (Pₘ := fun r : S × A => r.1 = s1) ?_ ?_
  · split
    · rename_i hm; exact absurd hm (by decide)
    · exact (WP.spec_ok _).2 rfl
  rintro ⟨s2, a1⟩ e2
  obtain rfl : s2 = s1 := e2
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (set_cap_ptu (kb := kb) (Pt := Pt) hR hO hsl (canon_pt hc) _) fun s5 ⟨k5, c5o, c5x, hk5'⟩ => ?_
  have k : VsKeep st kb Pt s s5 := k1.trans k5
  have z : VsZ st kb Pt s s5 := VsKeep.vsz k
  have hw : HrW st Hr s s5 := fun R hR' => k _ (hr_vsr hTb hH hR')
  have hc5 : ∀ x ∈ OS, x ≠ slot → obj.Slot.cap st x s5 = obj.Slot.cap st x s := fun x hx hne =>
    (c5o x hx hne).trans (hc1 x hx)
  obtain ⟨hpt, hf⟩ := hU.pt slot hsl ptr masid mvaddr hc
  have hsub2 : S2Rt st Pp Te Re bits s5 ⊆ S2Rt st Pp Te Re bits s :=
    fun p hp => ⟨hp.1, S2Reach.vsz hPp hTe hS h2 z hp.2⟩
  have hsub1 : VsRt st Pp Hr Tb Lv s5 ⊆ VsRt st Pp Hr Tb Lv s :=
    fun p hp => ⟨hp.1, VsReach.vsz hPp hTb hH.sub hY z hp.2⟩
  have hu0 : UnmC st slot ptr 4096 s := Or.inl ⟨rfl, masid, mvaddr, hc⟩
  have hone : ∀ y ∈ OS, y ≠ slot → ¬ NmC st y ptr s := fun y hy hne hn => hne (hV.one slot hsl y hy ptr 4096 hu0 hn)
  obtain ⟨hUZ, hUU⟩ := UnmZ.unmap (kb := kb) (W := fun _ => False) (Te' := S2Rt st Pp Te Re bits s5) hsl hU hV hc5
    ⟨0#u64, 0#u64, c5x⟩ ⟨false, masid, mvaddr, hc⟩ hone hpt
    (fun o ho h8 => by rw [k _ (Or.inl ⟨ptr, hpt, o, ho, h8, rfl⟩)]; exact (hf o ho h8).2)
    (fun o ho h8 hw' => (hf o ho h8).1 (ptwb_mono hsub2 hw'))
    (fun b hb _ => k b hb) (fun _ _ _ _ _ _ _ _ _ h => h) (fun b hb => ptwb_mono hsub2 hb)
  have hUT : UnmT st OS (VsRt st Pp Hr Tb Lv s5) s5 := by
    intro x hx p m hu o ho h8 hw'
    by_cases hxn : x = slot
    · subst hxn
      have hp : p = ptr ∧ m = 4096 := by
        rcases hu with ⟨hn, a', v', e'⟩ | ⟨hn, a', v', e'⟩ <;> rw [c5x] at e' <;> (cases okinj e')
        exact ⟨rfl, hn⟩
      obtain ⟨rfl, rfl⟩ := hp
      exact hT x hx p 4096 hu0 o ho h8 (ptw_mono hsub1 hw')
    · exact hT x hx p m ((UnmC.congr (hc5 x hx hxn)).1 hu) o ho h8 (ptw_mono hsub1 hw')
  exact (WP.spec_ok _).2 (Or.inr ⟨by rw [hk5', hks1, hk], VsTyR.keepZ hPp hTb hH.sub hY z,
    S2TyR.keep hPp hTe hS h2 z hw, hUZ, hUT, hUU⟩)

end dec

end ST
end R
end W7

end

end Fl4ProofsA64.P1
