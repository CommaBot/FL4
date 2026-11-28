/-
P1 (aarch64, gen 57): **`UtRev` along `swap`, `cap_swap_for_delete` and `empty_slot`** (bit 48 of the `NEXT` word,
`MDB_REVOCABLE`, obj.rs:276–282), the last three MDB writers gen 56 left (MdbTreeK has `insert_new_cap`,
`insert_with_cap`, `move_cap`).

* **`cdt.swap.rvb`** (cdt.rs:67–94): the two slots exchange their flags (`set_next_flags slot1 … r2 f2`,
  `set_next_flags slot2 … r1 f1`, with `r1` read before and `r2` after the first two link writes, which keep bit 48:
  `bit_next`, `w24_wr16`), every other `OS` slot keeps its bit (`set_next` rewrites pointer bits only). The link
  hypotheses are those of `cdt.swap.lrW` (MdbStepF), whose `LR` bookkeeping the first two stages repeat to know that
  slot 2's links are `OS` slots.
* **`cdt.swap.utRev`**: `UtRev` kept when each cap written is untyped only if the slot it comes from holds an untyped
  (case hypotheses `hu1` / `hu2`; for `cap_swap_for_delete` they hold by construction).
* **`cdt.cap_swap_for_delete.utRev`** (cdt.rs:96–103) on two members of the ghost (links from `MdbLk.lkF`, as
  `cdt.cap_swap_for_delete.mdb`). **`cdt.cap_swap_for_delete.utRevN`**: `x1` any `OS` slot (null ones linkless by
  `NullLk`), the deletion loops' `cap_swap_for_delete(Slot(ptr), slot)` (as `cdt.cap_swap_for_delete.mdbN`).
* **`cdt.empty_slot.rvb`** (cdt.rs:198–215): every `OS` slot but the emptied one keeps bit 48 (`set_next` of the
  `PREV`, `set_prev` of the `NEXT`, the first-badged update `(w &&& ~~~FB) ||| v` touches bit 49 only, `fb_bits`;
  `clear` touches the slot itself; `post_cap_deletion` writes outside `OS`, the hypothesis form of
  `cdt.empty_slot.mdbFLG`); **`cdt.empty_slot.utRev`**: the emptied slot ends `Null` (`mdbFLG`'s frame).

No named premise; new theorems only (case hypotheses `hu1` / `hu2` on `swap.utRev`).
-/
import Fl4ProofsA64.P1.MdbTreeK
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts Fl4Proofs.P3

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {Sg : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

section sw
variable {OS : Set U64}

set_option maxHeartbeats 4000000 in
/-- **`swap` and bit 48** (cdt.rs:67–94): the two slots exchange their bits, every other `OS` slot keeps its own.
Hypotheses as `cdt.swap.lrW`. -/
theorem cdt.swap.rvb (hO : OSOK T Ω Sg OS) {s : S} {pv nx : U64 → U64} (hL : LR st OS s pv nx) {x1 x2 : U64}
    {c1 c2 : capability.Cap} (hx1 : x1 ∈ OS) (hx2 : x2 ∈ OS) (hne : x1 ≠ x2) (hs1 : obj.sext48 x1 = ok x1)
    (hs2 : obj.sext48 x2 = ok x2) (hw1 : CapRt.EncWf c1) (hw2 : CapRt.EncWf c2)
    (hp1 : pv x1 ≠ 0#u64 → pv x1 ∈ OS) (hn1 : nx x1 ≠ 0#u64 → nx x1 ∈ OS)
    (hp2 : pv x2 ≠ 0#u64 → pv x2 ∈ OS) (hn2 : nx x2 ≠ 0#u64 → nx x2 ∈ OS) :
    cdt.swap st s c1 x1 c2 x2 ⦃ s' =>
      (∀ y ∈ OS, y ≠ x1 → y ≠ x2 → L.mem s' (wa y 24#u64) &&& RVB = L.mem s (wa y 24#u64) &&& RVB) ∧
      (((L.mem s (wa x2 24#u64) &&& RVB) != 0#u64) = true → L.mem s' (wa x1 24#u64) &&& RVB = RVB) ∧
      (((L.mem s (wa x1 24#u64) &&& RVB) != 0#u64) = true → L.mem s' (wa x2 24#u64) &&& RVB = RVB) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  obtain ⟨a1, b1, he1, -⟩ := CapRt.decode_encode c1 hw1
  obtain ⟨a2, b2, he2, -⟩ := CapRt.decode_encode c2 hw2
  unfold cdt.swap
  rw [set_cap_eq he2, bind_ok, set_cap_eq he1, bind_ok]
  have L2 : LR st OS (L.wr (L.wr (L.wr (L.wr s x1 a2) (wa x1 8#u64) b2) x2 a1) (wa x2 8#u64) b1) pv nx :=
    (hL.wr2 hO hx1).wr2 hO hx2
  have K2 : ∀ y ∈ OS, L.mem (L.wr (L.wr (L.wr (L.wr s x1 a2) (wa x1 8#u64) b2) x2 a1) (wa x2 8#u64) b1)
      (wa y 24#u64) = L.mem s (wa y 24#u64) := fun y hy =>
    ((set_cap_links hO hx2 y hy).2).trans ((set_cap_links hO hx1 y hy).2)
  generalize L.wr (L.wr (L.wr (L.wr s x1 a2) (wa x1 8#u64) b2) x2 a1) (wa x2 8#u64) b1 = s2 at L2 K2 ⊢
  rw [slot_prev_eq s2 x1, bind_ok, (L2 x1 hx1).1, next_eq, bind_ok, (L2 x1 hx1).2, revocable_eqA, bind_ok]
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st x1 s2 hS) fun f1 _ => ?_
  simp only [obj.Slot.is_null, bind_ok]
  -- stage 3: `P1.NEXT := x2`
  refine WP.spec_bind (Pₘ := fun s3 => LR st OS s3 pv (LkAbs.s3 0#u64 pv nx x1 x2) ∧
      ∀ y ∈ OS, L.mem s3 (wa y 24#u64) &&& RVB = L.mem s (wa y 24#u64) &&& RVB) ?_ fun s3 h3 => ?_
  · split
    · rename_i hp0
      have hP0 : pv x1 = 0#u64 := by simpa using hp0
      refine (WP.spec_ok _).2 ⟨L2.congr (fun _ _ => rfl) fun z _ => ?_, fun y hy => by rw [K2 y hy]⟩
      unfold LkAbs.s3; simp [hP0]
    · rename_i hp0
      have hP0 : pv x1 ≠ 0#u64 := by simpa using hp0
      rw [set_next_eq, WP.spec_ok]
      refine ⟨(L2.nw hO (hp1 hP0) (link_bits _ _) hs2).congr (fun _ _ => rfl) fun z _ => ?_,
        fun y hy => by rw [bit_next hO s2 (hp1 hP0) hy x2, K2 y hy]⟩
      unfold LkAbs.s3; by_cases e : z = pv x1 <;> simp [e, hP0]
  obtain ⟨L3, B3⟩ := h3
  -- stage 4: `N1.PREV := x2`
  refine WP.spec_bind (Pₘ := fun s4 => LR st OS s4 (LkAbs.s4 0#u64 pv nx x1 x2) (LkAbs.s3 0#u64 pv nx x1 x2) ∧
      ∀ y ∈ OS, L.mem s4 (wa y 24#u64) &&& RVB = L.mem s (wa y 24#u64) &&& RVB) ?_ fun s4 h4 => ?_
  · split
    · rename_i hn0
      have hN0 : nx x1 = 0#u64 := by simpa using hn0
      refine (WP.spec_ok _).2 ⟨L3.congr (fun z _ => ?_) (fun _ _ => rfl), B3⟩
      unfold LkAbs.s4; simp [hN0]
    · rename_i hn0
      have hN0 : nx x1 ≠ 0#u64 := by simpa using hn0
      rw [set_prev_eq, WP.spec_ok]
      refine ⟨(L3.prev hO (hn1 hN0) x2).congr (fun z _ => ?_) (fun _ _ => rfl),
        fun y hy => by rw [w24_wr16 hO s3 (hn1 hN0) hy]; exact B3 y hy⟩
      unfold LkAbs.s4; by_cases e : z = nx x1 <;> simp [e, hN0]
  obtain ⟨L4, B4⟩ := h4
  have hP2 : LkAbs.s4 0#u64 pv nx x1 x2 x2 ≠ 0#u64 → LkAbs.s4 0#u64 pv nx x1 x2 x2 ∈ OS := by
    unfold LkAbs.s4; split
    · exact fun _ => hx2
    · exact hp2
  have hN2 : LkAbs.s3 0#u64 pv nx x1 x2 x2 ≠ 0#u64 → LkAbs.s3 0#u64 pv nx x1 x2 x2 ∈ OS := by
    unfold LkAbs.s3; split
    · exact fun _ => hx2
    · exact hn2
  rw [slot_prev_eq s4 x2, bind_ok, (L4 x2 hx2).1, next_eq, bind_ok, (L4 x2 hx2).2, revocable_eqA, bind_ok]
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st x2 s4 hS) fun f2 _ => ?_
  -- stages 5–8: slot 1 and slot 2 get each other's flags
  rw [set_prev_eq s4 x1 _, bind_ok]
  refine WP.spec_bind (set_nf_rv _ x1 _ _ f2) ?_
  rintro s6 ⟨w6, rfl, hw6⟩
  rw [set_prev_eq _ x2 _, bind_ok]
  refine WP.spec_bind (set_nf_rv _ x2 _ _ f1) ?_
  rintro s8 ⟨w8, rfl, hw8⟩
  have B8 : ∀ y ∈ OS, y ≠ x1 → y ≠ x2 → L.mem (L.wr (L.wr (L.wr (L.wr s4 (wa x1 16#u64)
      (LkAbs.s4 0#u64 pv nx x1 x2 x2)) (wa x1 24#u64) w6) (wa x2 16#u64) (pv x1)) (wa x2 24#u64) w8)
      (wa y 24#u64) &&& RVB = L.mem s (wa y 24#u64) &&& RVB := fun y hy e1 e2 => by
    rw [w24_wr24 hO _ hx2 hy e2, w24_wr16 hO _ hx2 hy, w24_wr24 hO _ hx1 hy e1, w24_wr16 hO _ hx1 hy]
    exact B4 y hy
  have X1 : ((L.mem s (wa x2 24#u64) &&& RVB) != 0#u64) = true → L.mem (L.wr (L.wr (L.wr (L.wr s4 (wa x1 16#u64)
      (LkAbs.s4 0#u64 pv nx x1 x2 x2)) (wa x1 24#u64) w6) (wa x2 16#u64) (pv x1)) (wa x2 24#u64) w8)
      (wa x1 24#u64) &&& RVB = RVB := fun h => by
    rw [w24_wr24 hO _ hx2 hx1 hne, w24_wr16 hO _ hx2 hx1, w24_self hO _ hx1]
    exact hw6 (by rw [B4 x2 hx2]; exact h)
  have X2 : ((L.mem s (wa x1 24#u64) &&& RVB) != 0#u64) = true → L.mem (L.wr (L.wr (L.wr (L.wr s4 (wa x1 16#u64)
      (LkAbs.s4 0#u64 pv nx x1 x2 x2)) (wa x1 24#u64) w6) (wa x2 16#u64) (pv x1)) (wa x2 24#u64) w8)
      (wa x2 24#u64) &&& RVB = RVB := fun h => by
    rw [w24_self hO _ hx2]
    exact hw8 (by rw [K2 x1 hx1]; exact h)
  generalize L.wr (L.wr (L.wr (L.wr s4 (wa x1 16#u64) (LkAbs.s4 0#u64 pv nx x1 x2 x2)) (wa x1 24#u64) w6)
    (wa x2 16#u64) (pv x1)) (wa x2 24#u64) w8 = s8 at B8 X1 X2 ⊢
  try simp only [obj.Slot.is_null, bind_ok]
  -- stage 9: `P2.NEXT := x1`
  refine WP.spec_bind (Pₘ := fun s9 => ∀ y ∈ OS, L.mem s9 (wa y 24#u64) &&& RVB = L.mem s8 (wa y 24#u64) &&& RVB)
    ?_ fun s9 h9 => ?_
  · split
    · exact (WP.spec_ok _).2 fun _ _ => rfl
    · rename_i hp0
      have hP0 : LkAbs.s4 0#u64 pv nx x1 x2 x2 ≠ 0#u64 := by simpa using hp0
      rw [set_next_eq, WP.spec_ok]
      exact fun y hy => bit_next hO s8 (hP2 hP0) hy x1
  have fin : ∀ s10 : S, (∀ y ∈ OS, L.mem s10 (wa y 24#u64) = L.mem s9 (wa y 24#u64)) →
      (∀ y ∈ OS, y ≠ x1 → y ≠ x2 → L.mem s10 (wa y 24#u64) &&& RVB = L.mem s (wa y 24#u64) &&& RVB) ∧
      (((L.mem s (wa x2 24#u64) &&& RVB) != 0#u64) = true → L.mem s10 (wa x1 24#u64) &&& RVB = RVB) ∧
      (((L.mem s (wa x1 24#u64) &&& RVB) != 0#u64) = true → L.mem s10 (wa x2 24#u64) &&& RVB = RVB) :=
    fun s10 h10 => ⟨fun y hy e1 e2 => by rw [h10 y hy, h9 y hy]; exact B8 y hy e1 e2,
      fun h => by rw [h10 x1 hx1, h9 x1 hx1]; exact X1 h, fun h => by rw [h10 x2 hx2, h9 x2 hx2]; exact X2 h⟩
  -- stage 10: `N2.PREV := x1`
  split
  · exact (WP.spec_ok _).2 (fin s9 fun _ _ => rfl)
  · rename_i hn0
    have hN0 : LkAbs.s3 0#u64 pv nx x1 x2 x2 ≠ 0#u64 := by simpa using hn0
    rw [set_prev_eq, WP.spec_ok]
    exact fin _ fun y hy => w24_wr16 hO s9 (hN2 hN0) hy x1

/-- **`swap` keeps `UtRev`** when each cap written is untyped only if the slot it comes from holds an untyped
(`hu1`, `hu2`). -/
theorem cdt.swap.utRev (hO : OSOK T Ω Sg OS) {s : S} (hR : UtRev st OS s) {x1 x2 : U64}
    {c1 c2 : capability.Cap} (hx1 : x1 ∈ OS) (hx2 : x2 ∈ OS) (hne : x1 ≠ x2) (hs1 : obj.sext48 x1 = ok x1)
    (hs2 : obj.sext48 x2 = ok x2) (hw1 : CapRt.EncWf c1) (hw2 : CapRt.EncWf c2)
    (hp1 : L.mem s (wa x1 16#u64) ≠ 0#u64 → L.mem s (wa x1 16#u64) ∈ OS)
    (hn1 : NxA st s x1 ≠ 0#u64 → NxA st s x1 ∈ OS)
    (hp2 : L.mem s (wa x2 16#u64) ≠ 0#u64 → L.mem s (wa x2 16#u64) ∈ OS)
    (hn2 : NxA st s x2 ≠ 0#u64 → NxA st s x2 ∈ OS)
    (hu1 : isUtA c1 = true → isUtA (capA st s x1) = true) (hu2 : isUtA c2 = true → isUtA (capA st s x2) = true) :
    cdt.swap st s c1 x1 c2 x2 ⦃ s' => UtRev st OS s' ⦄ := by
  refine WP.spec_mono (WP.spec_and (cdt.swap.lrW hO (LR.self s) hx1 hx2 hne hs1 hs2 hw1 hw2 hp1 hn1 hp2 hn2)
    (cdt.swap.rvb hO (LR.self s) hx1 hx2 hne hs1 hs2 hw1 hw2 hp1 hn1 hp2 hn2)) ?_
  rintro s' ⟨⟨-, e1, e2, ek⟩, hb, h1b, h2b⟩
  intro u hu hc
  by_cases a1 : u = x1
  · rw [a1] at hc ⊢
    rw [e1] at hc
    have r := hR x2 hx2 (hu2 hc)
    rw [revocable_eqA] at r
    rw [revocable_eqA, h1b (okinj r)]; first | rfl | decide | simp
  · by_cases a2 : u = x2
    · rw [a2] at hc ⊢
      rw [e2] at hc
      have r := hR x1 hx1 (hu1 hc)
      rw [revocable_eqA] at r
      rw [revocable_eqA, h2b (okinj r)]; first | rfl | decide | simp
    · rw [ek u hu a1 a2] at hc
      exact revocable_of_bit (hR u hu hc) (hb u hu a1 a2)

variable {G : List (List U64)}

/-- **`cap_swap_for_delete` keeps `UtRev`** on two canonical members (cdt.rs:96–103; the caps are the slots' own). -/
theorem cdt.cap_swap_for_delete.utRev (hO : OSOK T Ω Sg OS) (h0 : ∀ y ∈ OS, y ≠ 0#u64) {s : S}
    (hM : MdbLk st OS G s) (hR : UtRev st OS s) {x1 x2 : U64} (hx1 : x1 ∈ G.flatten)
    (hx2 : x2 ∈ G.flatten) (hs1 : obj.sext48 x1 = ok x1) (hs2 : obj.sext48 x2 = ok x2) :
    cdt.cap_swap_for_delete st s x1 x2 ⦃ s' => UtRev st OS s' ⦄ := by
  have inOS : ∀ y ∈ G.flatten, y ∈ OS := fun y hy => ((hM.members y).1 hy).1
  have F := hM.lkF h0
  unfold cdt.cap_swap_for_delete
  simp only [obj.Slot.Insts.CoreCmpPartialEqSlot.eq, bind_ok]
  split
  · exact (WP.spec_ok _).2 hR
  · rename_i hne'
    have hne : x1 ≠ x2 := by simpa using hne'
    rw [capA_eq, bind_ok, capA_eq, bind_ok]
    exact cdt.swap.utRev hO hR (inOS x1 hx1) (inOS x2 hx2) hne hs1 hs2 (CapRt.decodeF_encWf _ _)
      (CapRt.decodeF_encWf _ _) (fun h => inOS _ (F.pvm _ hx1 h)) (fun h => inOS _ (F.nxm _ hx1 h))
      (fun h => inOS _ (F.pvm _ hx2 h)) (fun h => inOS _ (F.nxm _ hx2 h)) id id

/-- **`cap_swap_for_delete` keeps `UtRev`** with `x1` any `OS` slot (a null one is linkless by `NullLk`) and `x2` a
member: the deletion loops' call `cap_swap_for_delete(Slot(ptr), slot)` (the hypotheses of
`cdt.cap_swap_for_delete.mdbN`). -/
theorem cdt.cap_swap_for_delete.utRevN (hO : OSOK T Ω Sg OS) (h0 : ∀ y ∈ OS, y ≠ 0#u64) {s : S}
    (hM : MdbLk st OS G s) (hN : NullLk st OS s) (hR : UtRev st OS s) {x1 x2 : U64} (hx1 : x1 ∈ OS)
    (hx2 : x2 ∈ G.flatten) (hs1 : obj.sext48 x1 = ok x1) (hs2 : obj.sext48 x2 = ok x2) :
    cdt.cap_swap_for_delete st s x1 x2 ⦃ s' => UtRev st OS s' ⦄ := by
  have inOS : ∀ y ∈ G.flatten, y ∈ OS := fun y hy => ((hM.members y).1 hy).1
  have F := hM.lkF h0
  have N1 : x1 ∈ G.flatten ∨ (L.mem s (wa x1 16#u64) = 0#u64 ∧ NxA st s x1 = 0#u64) := by
    by_cases m : x1 ∈ G.flatten
    · exact Or.inl m
    · refine Or.inr (hN x1 hx1 ?_)
      by_contra h; exact m ((hM.members x1).2 ⟨hx1, h⟩)
  have hp1 : L.mem s (wa x1 16#u64) ≠ 0#u64 → L.mem s (wa x1 16#u64) ∈ OS := fun h => by
    rcases N1 with m | ⟨e, -⟩
    · exact inOS _ (F.pvm _ m h)
    · exact absurd e h
  have hn1 : NxA st s x1 ≠ 0#u64 → NxA st s x1 ∈ OS := fun h => by
    rcases N1 with m | ⟨-, e⟩
    · exact inOS _ (F.nxm _ m h)
    · exact absurd e h
  unfold cdt.cap_swap_for_delete
  simp only [obj.Slot.Insts.CoreCmpPartialEqSlot.eq, bind_ok]
  split
  · exact (WP.spec_ok _).2 hR
  · rename_i hne'
    have hne : x1 ≠ x2 := by simpa using hne'
    rw [capA_eq, bind_ok, capA_eq, bind_ok]
    exact cdt.swap.utRev hO hR hx1 (inOS x2 hx2) hne hs1 hs2 (CapRt.decodeF_encWf _ _)
      (CapRt.decodeF_encWf _ _) hp1 hn1
      (fun h => inOS _ (F.pvm _ hx2 h)) (fun h => inOS _ (F.nxm _ hx2 h)) id id

end sw

/-! ## `empty_slot` -/

section es
variable {OS : Set U64} {A : Type _} {ar : machine.Arch A}

set_option maxHeartbeats 2000000 in
/-- **`empty_slot` and bit 48** (cdt.rs:198–215): every `OS` slot but the emptied one keeps its bit. Link
hypotheses on the non-null path; the cleanup's `post_cap_deletion` as in `cdt.empty_slot.mdbFLG`. -/
theorem cdt.empty_slot.rvb (hO : OSOK T Ω Sg OS) {s : S} {a : A} {x : U64} (hx : x ∈ OS)
    {cl : capability.Cap} {Pw : U64 → Prop} (hpw : ∀ b, Pw b → ¬ InOS OS b)
    (hpcd : ∀ (s1 : S) (a1 : A), L.ksb s1 = L.ksb s →
      objects.post_cap_deletion st ar s1 a1 cl ⦃ r => WritesIn st s1 r.1 Pw ⦄)
    (hpP : capA st s x ≠ .Null → L.mem s (wa x 16#u64) ≠ 0#u64 → L.mem s (wa x 16#u64) ∈ OS)
    (hnN : capA st s x ≠ .Null → NxA st s x ≠ 0#u64 → NxA st s x ∈ OS) :
    cdt.empty_slot st ar s a x cl ⦃ r =>
      ∀ y ∈ OS, y ≠ x → L.mem r.1 (wa y 24#u64) &&& RVB = L.mem s (wa y 24#u64) &&& RVB ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.empty_slot
  rw [capA_eq, bind_ok]
  by_cases hn : capA st s x = .Null
  · rw [hn, is_null_t, bind_ok, if_pos rfl]
    exact (WP.spec_ok _).2 fun _ _ _ => rfl
  rw [is_null_f hn, bind_ok, if_neg (by simp)]
  rw [slot_prev_eq, bind_ok, next_eq, bind_ok]
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st x s hS) fun fb _ => ?_
  simp only [obj.Slot.is_null, bind_ok]
  -- stage 1: `set_next(P, N)`
  refine WP.spec_bind (Pₘ := fun s1 => (∀ y ∈ OS, L.mem s1 (wa y 24#u64) &&& RVB = L.mem s (wa y 24#u64) &&& RVB) ∧
      L.ksb s1 = L.ksb s) ?_ fun s1 h1 => ?_
  · split
    · exact (WP.spec_ok _).2 ⟨fun _ _ => rfl, rfl⟩
    · rename_i hp0
      have hP0 : L.mem s (wa x 16#u64) ≠ 0#u64 := by simpa using hp0
      rw [set_next_eq, WP.spec_ok]
      exact ⟨fun y hy => bit_next hO s (hpP hn hP0) hy _, L.ksb_wr _ _ _⟩
  obtain ⟨b1, k1⟩ := h1
  -- stage 2: `set_prev(N, P)` and the first-badged update of `N`
  refine WP.spec_bind (Pₘ := fun s2 => (∀ y ∈ OS, L.mem s2 (wa y 24#u64) &&& RVB = L.mem s (wa y 24#u64) &&& RVB) ∧
      L.ksb s2 = L.ksb s) ?_ fun s2 h2 => ?_
  · split
    · exact (WP.spec_ok _).2 ⟨b1, k1⟩
    · rename_i hn0
      have hN0 : NxA st s x ≠ 0#u64 := by simpa using hn0
      have hNO := hnN hn hN0
      rw [set_prev_eq, bind_ok]
      refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st _ _ hS) fun nfb _ => ?_
      have key : ∀ v, (v = FB ∨ v = 0#u64) →
          let s3 := L.wr s1 (wa (NxA st s x) 16#u64) (L.mem s (wa x 16#u64))
          let s2 := L.wr s3 (wa (NxA st s x) 24#u64) ((L.mem s3 (wa (NxA st s x) 24#u64) &&& ~~~ FB) ||| v)
          (∀ y ∈ OS, L.mem s2 (wa y 24#u64) &&& RVB = L.mem s (wa y 24#u64) &&& RVB) ∧ L.ksb s2 = L.ksb s := by
        intro v hv
        refine ⟨fun y hy => ?_, by simp only [L.ksb_wr]; exact k1⟩
        have hvR : v &&& RVB = 0#u64 := by rcases hv with rfl | rfl <;> rfl
        by_cases e : y = NxA st s x
        · rw [e, w24_self hO _ hNO, fb_bits _ _ _ _ hvR (by rfl), w24_wr16 hO s1 hNO hNO, ← e]; exact b1 y hy
        · rw [w24_wr24 hO _ hNO hy e, w24_wr16 hO s1 hNO hy]; exact b1 y hy
      split
      · rw [set_fb_eq_t]; exact (WP.spec_ok _).2 (key FB (Or.inl rfl))
      · cases fb
        · rw [set_fb_eq_f]; exact (WP.spec_ok _).2 (key 0#u64 (Or.inr rfl))
        · rw [set_fb_eq_t]; exact (WP.spec_ok _).2 (key FB (Or.inl rfl))
  obtain ⟨b2, k2⟩ := h2
  -- stage 3: `clear(x)`, stage 4: `post_cap_deletion`
  rw [clear_eq, bind_ok]
  refine WP.spec_mono (hpcd _ a (by simp only [L.ksb_wr]; exact k2)) fun r hr => ?_
  intro y hy hne
  have kx : SK st s2
      (L.wr (L.wr (L.wr (L.wr s2 x 0#u64) (wa x 8#u64) 0#u64) (wa x 16#u64) 0#u64) (wa x 24#u64) 0#u64) y :=
    (((SK.wr0 hO s2 hx hy hne _).trans (SK.wr hO _ hx hy hne (by simp) (by simp) _)).trans
      (SK.wr hO _ hx hy hne (by simp) (by simp) _)).trans (SK.wr hO _ hx hy hne (by simp) (by simp) _)
  rw [(SK.of_w hO hr hpw hy).2.2.2, kx.2.2.2]; exact b2 y hy

variable {G : List (List U64)}

/-- **`empty_slot` keeps `UtRev`** (hypotheses of `cdt.empty_slot.mdbFLG`; the emptied slot ends `Null`). -/
theorem cdt.empty_slot.utRev (hO : OSOK T Ω Sg OS) (h0 : ∀ y ∈ OS, y ≠ 0#u64) {s : S}
    (hM : MdbLk st OS G s) (hRO : RngOneA64 st G s) (hK : KindA st OS s) (hR : UtRev st OS s) {a : A} {x : U64}
    (hx : x ∈ OS) {cl : capability.Cap} {Pw : U64 → Prop} (hpw : ∀ b, Pw b → ¬ InOS OS b)
    (hpcd : ∀ (s1 : S) (a1 : A), L.ksb s1 = L.ksb s →
      objects.post_cap_deletion st ar s1 a1 cl ⦃ r => WritesIn st s1 r.1 Pw ⦄) :
    cdt.empty_slot st ar s a x cl ⦃ r => UtRev st OS r.1 ⦄ := by
  have inOS : ∀ y ∈ G.flatten, y ∈ OS := fun y hy => ((hM.members y).1 hy).1
  have F := hM.lkF h0
  have hxG : capA st s x ≠ .Null → x ∈ G.flatten := fun hn => (hM.members x).2 ⟨hx, hn⟩
  refine WP.spec_mono (WP.spec_and (cdt.empty_slot.mdbFLG hO h0 hM hRO hK hx hpw hpcd)
    (cdt.empty_slot.rvb hO hx hpw hpcd (fun hn h => inOS _ (F.pvm _ (hxG hn) h))
      (fun hn h => inOS _ (F.nxm _ (hxG hn) h)))) ?_
  rintro r ⟨⟨⟨G', -, -, -, -, -, hcr, -, hxn, -⟩, -, -⟩, hb⟩
  intro u hu hc
  by_cases e : u = x
  · rw [e, hxn] at hc; simp [isUtA] at hc
  · rw [hcr u hu e] at hc
    exact revocable_of_bit (hR u hu hc) (hb u hu e)

end es

end ST
end R
end W7

end

end Fl4ProofsA64.P1
