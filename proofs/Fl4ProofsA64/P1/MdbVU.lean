/-
P1 (aarch64, gen 58): **the heap-level free-region fact `ValidUntypedA`** (Architect ruling, option (c): l4v
`valid_untyped` on the existing heap ghost `H`), its boot case, its transfer along the cap steps, and the slot
apartness it gives for a grown `OS`.

* **`ValidUntypedA st H OS s`**: no object of `H` meets the free part `[p + i, p + 2^b)` of any RAM `Untyped p b i
  false` cap held in an `OS` slot. l4v: Invariants_AI `valid_untyped` (an object meeting an untyped's range lies in
  it and misses its usable range `usable_untyped_range`), stated on the free part only (the part retype reads).
  FL4 source: untyped.rs:61–70 (`free_ref = ptr + free_index`, new objects start at `align_up(free_ref, ·)`),
  untyped.rs:266–288 (`retype` raises `free_index` past the new objects), untyped.rs:225–262 (`reset_untyped`
  clears `[ptr, ptr + free_index)` and sets it to 0). **Device untypeds are left out**: since losfair/FL4#34 a
  device untyped's region may hold the kernel image (QueueUtRetype `UtRetypeP3`), whose statics include the idle
  TCBs (crates/fl4-kernel-aarch64/src/lib.rs:67–73, `IdleArea`), heap objects with a device free index 0. Device
  retype only creates frames / untypeds (untyped.rs:66), so neither the slot apartness nor `create_object`'s frame
  ever needs it.
* **`UB d c`** (the step relation the fact needs: a RAM `Untyped` written is a RAM `Untyped` of the same region with
  a smaller or equal free index before) with `UB.refl`, `UB.of_not`, **`FullA.ub`** (`set_untyped_cap_as_full`).
* **`ValidUntypedA.of_ub`** (every `OS` slot after is `UB` some `OS` slot before, the heap smaller), `.recap`,
  `.heap` (smaller heap), `.sub` (smaller `OS`), **`ValidUntypedA.empty`** (boot: all `OS` slots null, as
  `MdbSW.boot`).
* Steps (cap equalities from the existing link lemmas): **`.keepO`** (`OSKeep`), **`.wr2`** (a two-word cap
  write), **`obj.Slot.set_cap.vuZ`** (a `Zombie` write), **`cdt.swap.vu`**, **`cdt.cap_swap_for_delete.vu`**,
  **`cdt.move_cap.vu`**, **`cdt.insert_with_cap.vu`**, **`cdt.empty_slot.vu`**; `MdbS.lnk` (an `OS` slot's links
  are `OS` slots or null, from `MdbLk` / `NullLk`).
* **Slot apartness** (goal 0's use): **`ValidUntypedA.word_off`** (every word of an `OS` slot placed over the
  heap's sets — `OSOK H.tcbs H.omega Sg OS`, as `UtRetypeP3.sets` gives — lies off a RAM untyped's free part:
  a TCB low word lies in its TCB, an `Ω` word in its object), **`ValidUntypedA.apart`** (an 8-aligned 32-byte slot
  inside the free part is apart from every `OS` slot), **`OSOK.growV`**: `OSOK` of `OS ∪ N` for new slots `N` in
  the free part (the apartness half `hap` of gen 56's `OSOK.union`). `WinOK` of the grown heap stays gen 53's
  `HeapWin.retype` → `WinOK.ofHeap`.

No named premise; new definitions and theorems only.
-/
import Fl4ProofsA64.P1.MdbTreeZ
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts Fl4Proofs.P3

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {Sg : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

/-- **l4v `valid_untyped` on the heap ghost** (module docstring): no object of `H` meets the free part of a RAM
untyped cap of `OS`. -/
def ValidUntypedA (st : machine.Store S) [L : LawfulStore st] (H : Heap) (OS : Set U64) (s : S) : Prop :=
  ∀ u ∈ OS, ∀ p b i, capA st s u = .Untyped p b i false → ∀ q k, H q = some k →
    q.val + 2 ^ k.bits ≤ p.val + i.val ∨ p.val + 2 ^ b.val ≤ q.val

/-- **A written cap for an old one** (module docstring). -/
def UB (d c : capability.Cap) : Prop :=
  ∀ p b i, d = .Untyped p b i false → ∃ i0, c = .Untyped p b i0 false ∧ i0.val ≤ i.val

theorem UB.refl (c : capability.Cap) : UB c c := fun _ _ i h => ⟨i, h, le_refl _⟩

theorem UB.of_not {d c : capability.Cap} (h : ∀ p b i, d ≠ .Untyped p b i false) : UB d c :=
  fun p b i e => absurd e (h p b i)

theorem UB.null (c : capability.Cap) : UB .Null c := UB.of_not fun _ _ _ h => by cases h

theorem FullA.ub {d c : capability.Cap} (h : FullA d c)
    (hf : ∀ p b i e, c = .Untyped p b i e → i.val ≤ 2 ^ b.val) : UB d c := by
  rcases h with rfl | ⟨p, b, i, e, i1, rfl, rfl, hi⟩
  · exact UB.refl _
  · intro p' b' i' h
    injection h with a1 a2 a3 a4
    subst a1 a2 a3 a4
    exact ⟨i, rfl, by have := hf _ _ _ _ rfl; omega⟩

variable {OS : Set U64} {H : Heap}

/-! ## Transfer -/

theorem ValidUntypedA.of_ub {H' : Heap} {s s' : S} (h : ValidUntypedA st H OS s)
    (hH : ∀ q k, H' q = some k → H q = some k)
    (hc : ∀ y ∈ OS, ∃ y0 ∈ OS, UB (capA st s' y) (capA st s y0)) : ValidUntypedA st H' OS s' := by
  intro u hu p b i hcu q k hq
  obtain ⟨y0, hy0, hb⟩ := hc u hu
  obtain ⟨i0, hc0, hle⟩ := hb p b i hcu
  rcases h y0 hy0 p b i0 hc0 q k (hH q k hq) with g | g
  · left; omega
  · right; exact g

theorem ValidUntypedA.recap {s s' : S} (h : ValidUntypedA st H OS s)
    (hc : ∀ y ∈ OS, UB (capA st s' y) (capA st s y)) : ValidUntypedA st H OS s' :=
  h.of_ub (fun _ _ e => e) fun y hy => ⟨y, hy, hc y hy⟩

theorem ValidUntypedA.heap {H' : Heap} {s : S} (h : ValidUntypedA st H OS s)
    (hH : ∀ q k, H' q = some k → H q = some k) : ValidUntypedA st H' OS s :=
  h.of_ub hH fun y hy => ⟨y, hy, UB.refl _⟩

theorem ValidUntypedA.sub {OS' : Set U64} {s : S} (h : ValidUntypedA st H OS s) (hs : OS' ⊆ OS) :
    ValidUntypedA st H OS' s :=
  fun u hu => h u (hs hu)

/-- **Boot**: null `OS` slots. -/
theorem ValidUntypedA.empty {s : S} (h : ∀ x ∈ OS, capA st s x = .Null) : ValidUntypedA st H OS s :=
  fun u hu p b i hc => by rw [h u hu] at hc; cases hc

/-! ## Steps -/

theorem ValidUntypedA.keepO {s s' : S} (h : ValidUntypedA st H OS s) (k : OSKeep st OS s s') :
    ValidUntypedA st H OS s' :=
  h.recap fun y hy => by rw [k.capA hy]; exact UB.refl _

theorem ValidUntypedA.wr2 (hO : OSOK T Ω Sg OS) {s : S} (h : ValidUntypedA st H OS s) {x0 w0 w1 : U64}
    (hx0 : x0 ∈ OS) {c : capability.Cap} (hd : capability.Cap.decode w0 w1 = ok c) (hb : UB c (capA st s x0)) :
    ValidUntypedA st H OS (L.wr (L.wr s x0 w0) (wa x0 8#u64) w1) :=
  h.recap fun y hy => by
    by_cases e : y = x0
    · rw [e, capA_wr2_self hO hx0 hd]; exact hb
    · rw [capA_wr2_other hO hx0 hy e]; exact UB.refl _

/-- **A `Zombie` write** keeps the fact (a `Zombie` is no `Untyped`). -/
theorem obj.Slot.set_cap.vuZ (hO : OSOK T Ω Sg OS) {s : S} (h : ValidUntypedA st H OS s) {x p t n : U64}
    (hx : x ∈ OS) (hp : Canon p) :
    obj.Slot.set_cap st x s (.Zombie p t n) ⦃ s' => ValidUntypedA st H OS s' ⦄ := by
  rw [set_cap_zombie, WP.spec_ok]
  exact h.wr2 hO hx (decode_zw p t n hp) (UB.of_not fun _ _ _ e => by cases e)

/-- An `OS` slot's links are `OS` slots or null (`MdbLk` for members, `NullLk` for null slots). -/
theorem MdbS.lnk (hO : OSOK T Ω Sg OS) {s : S} (h : MdbS st OS s) {x : U64} (hx : x ∈ OS) :
    (L.mem s (wa x 16#u64) ≠ 0#u64 → L.mem s (wa x 16#u64) ∈ OS) ∧ (NxA st s x ≠ 0#u64 → NxA st s x ∈ OS) := by
  obtain ⟨G, hM, -, -, hN, -⟩ := h
  have F := hM.lkF hO.nz
  have inOS : ∀ y ∈ G.flatten, y ∈ OS := fun y hy => ((hM.members y).1 hy).1
  by_cases hn : capA st s x = .Null
  · obtain ⟨a, b⟩ := hN x hx hn
    exact ⟨fun e => absurd a e, fun e => absurd b e⟩
  · have hxG : x ∈ G.flatten := (hM.members x).2 ⟨hx, hn⟩
    exact ⟨fun e => inOS _ (F.pvm _ hxG e), fun e => inOS _ (F.nxm _ hxG e)⟩

/-- (gen 60) **The cap map of a step**: every `OS` slot after holds a cap `UB` some `OS` slot's cap before (what
`ValidUntypedA.of_ub` / `UtZeroA.capw` read off a step). -/
def UBm (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (s s' : S) : Prop :=
  ∀ y ∈ OS, ∃ y0 ∈ OS, UB (capA st s' y) (capA st s y0)

/-- (gen 60) **`swap`'s cap map and write frame** (`swap.vu`'s argument, `cdt.swap.lrWF`). -/
theorem cdt.swap.ubF (hO : OSOK T Ω Sg OS) {s : S} (hS : MdbS st OS s)
    {x1 x2 : U64} {c1 c2 : capability.Cap} (hx1 : x1 ∈ OS) (hx2 : x2 ∈ OS) (hne : x1 ≠ x2)
    (hs1 : obj.sext48 x1 = ok x1) (hs2 : obj.sext48 x2 = ok x2) (hw1 : CapRt.EncWf c1) (hw2 : CapRt.EncWf c2)
    (hb1 : UB c1 (capA st s x1)) (hb2 : UB c2 (capA st s x2)) :
    cdt.swap st s c1 x1 c2 x2 ⦃ s' =>
      WritesIn st s s' (W7.CapW T Ω Sg) ∧ UBm st OS s s' ⦄ := by
  obtain ⟨p1, n1⟩ := hS.lnk hO hx1
  obtain ⟨p2, n2⟩ := hS.lnk hO hx2
  refine WP.spec_mono (cdt.swap.lrWF hO (LR.self s) hx1 hx2 hne hs1 hs2 hw1 hw2 p1 n1 p2 n2) ?_
  rintro s' ⟨hW, -, e1, e2, ek⟩
  refine ⟨hW, fun y hy => ?_⟩
  by_cases a1 : y = x1
  · exact ⟨x2, hx2, by rw [a1, e1]; exact hb2⟩
  · by_cases a2 : y = x2
    · exact ⟨x1, hx1, by rw [a2, e2]; exact hb1⟩
    · exact ⟨y, hy, by rw [ek y hy a1 a2]; exact UB.refl _⟩

/-- **`swap`**: the two slots exchange caps `UB` the replaced ones. -/
theorem cdt.swap.vu (hO : OSOK T Ω Sg OS) {s : S} (h : ValidUntypedA st H OS s) (hS : MdbS st OS s)
    {x1 x2 : U64} {c1 c2 : capability.Cap} (hx1 : x1 ∈ OS) (hx2 : x2 ∈ OS) (hne : x1 ≠ x2)
    (hs1 : obj.sext48 x1 = ok x1) (hs2 : obj.sext48 x2 = ok x2) (hw1 : CapRt.EncWf c1) (hw2 : CapRt.EncWf c2)
    (hb1 : UB c1 (capA st s x1)) (hb2 : UB c2 (capA st s x2)) :
    cdt.swap st s c1 x1 c2 x2 ⦃ s' => ValidUntypedA st H OS s' ⦄ :=
  WP.spec_mono (cdt.swap.ubF hO hS hx1 hx2 hne hs1 hs2 hw1 hw2 hb1 hb2) fun _ h' => h.of_ub (fun _ _ e => e) h'.2
/-- **`cap_swap_for_delete`** of two canonical `OS` slots. -/
theorem cdt.cap_swap_for_delete.vu (hO : OSOK T Ω Sg OS) {s : S} (h : ValidUntypedA st H OS s)
    (hS : MdbS st OS s) {x1 x2 : U64} (hx1 : x1 ∈ OS) (hx2 : x2 ∈ OS) (hs1 : obj.sext48 x1 = ok x1)
    (hs2 : obj.sext48 x2 = ok x2) :
    cdt.cap_swap_for_delete st s x1 x2 ⦃ s' => ValidUntypedA st H OS s' ⦄ := by
  unfold cdt.cap_swap_for_delete
  simp only [obj.Slot.Insts.CoreCmpPartialEqSlot.eq, bind_ok]
  split
  · exact (WP.spec_ok _).2 h
  · rename_i hne'
    have hne : x1 ≠ x2 := by simpa using hne'
    rw [capA_eq, bind_ok, capA_eq, bind_ok]
    exact cdt.swap.vu hO h hS hx1 hx2 hne hs1 hs2 (CapRt.decodeF_encWf _ _) (CapRt.decodeF_encWf _ _)
      (UB.refl _) (UB.refl _)

/-- (gen 60) **`move_cap`'s cap map and write frame** (`move_cap.vu`'s argument, `cdt.move_cap.lrF`). -/
theorem cdt.move_cap.ubF (hO : OSOK T Ω Sg OS) {s : S} (hS : MdbS st OS s)
    {src dest : U64} {nc : capability.Cap} (hsrc : src ∈ OS) (hd : dest ∈ OS) (hsd : src ≠ dest)
    (hdc : obj.sext48 dest = ok dest) (hw : CapRt.EncWf nc) (hb : UB nc (capA st s src)) :
    cdt.move_cap st s nc src dest ⦃ s' =>
      WritesIn st s s' (W7.CapW T Ω Sg) ∧ UBm st OS s s' ⦄ := by
  obtain ⟨pp, nn⟩ := hS.lnk hO hsrc
  refine WP.spec_mono (cdt.move_cap.lrF hO (LR.self s) hsrc hd hsd hdc hw pp nn) ?_
  rintro s' ⟨hW, -, ed, es, ek⟩
  refine ⟨hW, fun y hy => ?_⟩
  by_cases a1 : y = dest
  · exact ⟨src, hsrc, by rw [a1, ed]; exact hb⟩
  · by_cases a2 : y = src
    · exact ⟨src, hsrc, by rw [a2, es]; exact UB.null _⟩
    · exact ⟨y, hy, by rw [ek y hy a2 a1]; exact UB.refl _⟩

/-- **`move_cap`**: `dest` takes a cap `UB` the source's, the source is emptied. -/
theorem cdt.move_cap.vu (hO : OSOK T Ω Sg OS) {s : S} (h : ValidUntypedA st H OS s) (hS : MdbS st OS s)
    {src dest : U64} {nc : capability.Cap} (hsrc : src ∈ OS) (hd : dest ∈ OS) (hsd : src ≠ dest)
    (hdc : obj.sext48 dest = ok dest) (hw : CapRt.EncWf nc) (hb : UB nc (capA st s src)) :
    cdt.move_cap st s nc src dest ⦃ s' => ValidUntypedA st H OS s' ⦄ :=
  WP.spec_mono (cdt.move_cap.ubF hO hS hsrc hd hsd hdc hw hb) fun _ h' => h.of_ub (fun _ _ e => e) h'.2
/-- (gen 60) **`insert_with_cap`'s cap map and write frame** (`insert_with_cap.vu`'s argument,
`cdt.insert_with_cap.lrF`). -/
theorem cdt.insert_with_cap.ubF (hO : OSOK T Ω Sg OS) {s : S} (hS : MdbS st OS s)
    {src dest : U64} {nc sc : capability.Cap} (hsrc : src ∈ OS) (hd : dest ∈ OS) (hsd : src ≠ dest)
    (hdc : obj.sext48 dest = ok dest) (hsc : capA st s src = sc) (hsc0 : sc ≠ .Null) (hw : CapRt.EncWf nc)
    (hb : UB nc sc) (hfib : ∀ p b i e, sc = .Untyped p b i e → i.val ≤ 2 ^ b.val) :
    cdt.insert_with_cap st s nc sc src dest ⦃ s' =>
      WritesIn st s s' (W7.CapW T Ω Sg) ∧ UBm st OS s s' ⦄ := by
  obtain ⟨-, nn⟩ := hS.lnk hO hsrc
  refine WP.spec_mono (spec_andA (cdt.insert_with_cap.lrF hO (LR.self s) hsrc hd hsd hdc hsc hsc0 hw nn)
    (cdt.insert_with_cap.srcU hO hsrc hd hsd hsc hw nn)) ?_
  rintro s' ⟨⟨hW, -, ed, -, -, ek, -⟩, hU⟩
  refine ⟨hW, fun y hy => ?_⟩
  by_cases a1 : y = dest
  · exact ⟨src, hsrc, by rw [a1, ed, hsc]; exact hb⟩
  · by_cases a2 : y = src
    · exact ⟨src, hsrc, by rw [a2, hsc]; exact FullA.ub hU.1 hfib⟩
    · exact ⟨y, hy, by rw [ek y hy a2 a1]; exact UB.refl _⟩

/-- **`insert_with_cap`**: `dest` takes a cap `UB` the source's, the source made full at most
(`set_untyped_cap_as_full`, `FullA.ub` with the free index bound `hfib`, `UtInvA.fib`). -/
theorem cdt.insert_with_cap.vu (hO : OSOK T Ω Sg OS) {s : S} (h : ValidUntypedA st H OS s) (hS : MdbS st OS s)
    {src dest : U64} {nc sc : capability.Cap} (hsrc : src ∈ OS) (hd : dest ∈ OS) (hsd : src ≠ dest)
    (hdc : obj.sext48 dest = ok dest) (hsc : capA st s src = sc) (hsc0 : sc ≠ .Null) (hw : CapRt.EncWf nc)
    (hb : UB nc sc) (hfib : ∀ p b i e, sc = .Untyped p b i e → i.val ≤ 2 ^ b.val) :
    cdt.insert_with_cap st s nc sc src dest ⦃ s' => ValidUntypedA st H OS s' ⦄ :=
  WP.spec_mono (cdt.insert_with_cap.ubF hO hS hsrc hd hsd hdc hsc hsc0 hw hb hfib) fun _ h' =>
    h.of_ub (fun _ _ e => e) h'.2
section emp
variable {A : Type _} {ar : machine.Arch A}

/-- **`empty_slot`**: the slot emptied, the other `OS` slots kept (`cdt.empty_slot.mdbFLG`). -/
theorem cdt.empty_slot.vu (hO : OSOK T Ω Sg OS) {s : S} (h : ValidUntypedA st H OS s) (hS : MdbS st OS s)
    {a : A} {x : U64} (hx : x ∈ OS) {cl : capability.Cap} {Pw : U64 → Prop} (hpw : ∀ b, Pw b → ¬ InOS OS b)
    (hpcd : ∀ (s1 : S) (a1 : A), L.ksb s1 = L.ksb s →
      objects.post_cap_deletion st ar s1 a1 cl ⦃ r => WritesIn st s1 r.1 Pw ⦄) :
    cdt.empty_slot st ar s a x cl ⦃ r => ValidUntypedA st H OS r.1 ⦄ := by
  obtain ⟨G, hM, hRO, hK, -, -⟩ := hS
  refine WP.spec_mono (cdt.empty_slot.mdbFLG hO hO.nz hM hRO hK hx hpw hpcd) ?_
  rintro r ⟨⟨G', -, -, -, -, -, hcr, -, hx0, -⟩, -, -⟩
  refine h.recap fun y hy => ?_
  by_cases e : y = x
  · rw [e, hx0]; exact UB.null _
  · rw [hcr y hy e]; exact UB.refl _

end emp

/-! ## Slot apartness -/

/-- **Every word of an `OS` slot lies off a RAM untyped's free part** (module docstring). -/
theorem ValidUntypedA.word_off {Sg : Set U64} (hH : HeapOK H) (hO : OSOK H.tcbs H.omega Sg OS) {s : S}
    (hV : ValidUntypedA st H OS s) {u p b i : U64} (hu : u ∈ OS) (hc : capA st s u = .Untyped p b i false)
    {x : U64} (hx : x ∈ OS) {o : U64} (ho : o.val < 32) (h8 : o.val % 8 = 0) :
    (wa x o).val < p.val + i.val ∨ p.val + 2 ^ b.val ≤ (wa x o).val := by
  rcases hO.cw hx ho h8 with ⟨t, ht, K, hK, e⟩ | ⟨⟨-, q, k, hq, -, hin⟩, -⟩
  · rw [e, wa_val]
    have ht' : H t = some .tcb := ht
    have hf := hH.fits t _ ht'
    have g := hV u hu p b i hc t .tcb ht'
    simp only [HKind.bits] at hf g
    rcases g with g | g
    · left; rw [Nat.mod_eq_of_lt (by omega)]; omega
    · right; rw [Nat.mod_eq_of_lt (by omega)]; omega
  · unfold InObj at hin
    rcases hV u hu p b i hc q k hq with g | g
    · left; omega
    · right; omega

/-- **An 8-aligned slot inside the free part is apart from every `OS` slot.** -/
theorem ValidUntypedA.apart {Sg : Set U64} (hH : HeapOK H) (hO : OSOK H.tcbs H.omega Sg OS) {s : S}
    (hV : ValidUntypedA st H OS s) {u p b i : U64} (hu : u ∈ OS) (hc : capA st s u = .Untyped p b i false)
    {x : U64} (hx : x ∈ OS) {y : U64} (hy8 : y.val % 8 = 0) (hlo : p.val + i.val ≤ y.val)
    (hhi : y.val + 32 ≤ p.val + 2 ^ b.val) : x.val + 32 ≤ y.val ∨ y.val + 32 ≤ x.val := by
  have hx8 : x.val % 8 = 0 := hO.al0 hx
  have hf := hO.fit x hx
  have W : ∀ o : U64, o.val < 32 → o.val % 8 = 0 →
      x.val + o.val < p.val + i.val ∨ p.val + 2 ^ b.val ≤ x.val + o.val := fun o ho h8 => by
    have := hV.word_off hH hO hu hc hx ho h8
    rwa [wv hf ho] at this
  by_contra hcn
  by_cases hxy : x.val ≤ y.val
  · have : y.val = x.val + 0 ∨ y.val = x.val + 8 ∨ y.val = x.val + 16 ∨ y.val = x.val + 24 := by omega
    rcases this with e | e | e | e
    · have := W 0#u64 (by simp) (by simp); simp at this; omega
    · have := W 8#u64 (by simp) (by simp); simp at this; omega
    · have := W 16#u64 (by simp) (by simp); simp at this; omega
    · have := W 24#u64 (by simp) (by simp); simp at this; omega
  · have := W 0#u64 (by simp) (by simp); simp at this; omega

/-- **`OSOK` of the grown slot set** (module docstring): old slots placed over the heap's sets, new slots `N`
placed over the new sets and lying in a RAM untyped's free part. -/
theorem OSOK.growV {Sg T' Ω' Sg' N : Set U64} (hH : HeapOK H) (hO : OSOK H.tcbs H.omega Sg OS) {s : S}
    (hV : ValidUntypedA st H OS s) {u p b i : U64} (hu : u ∈ OS) (hc : capA st s u = .Untyped p b i false)
    (hN : OSOK T' Ω' Sg' N) (hNin : ∀ y ∈ N, p.val + i.val ≤ y.val ∧ y.val + 32 ≤ p.val + 2 ^ b.val)
    (hw : ∀ w, W7.CapW H.tcbs H.omega Sg w → W7.CapW T' Ω' Sg' w) : OSOK T' Ω' Sg' (OS ∪ N) :=
  OSOK.union (hO.mono hw) hN fun x hx y hy =>
    hV.apart hH hO hu hc hx (hN.al0 hy) (hNin y hy).1 (hNin y hy).2

end ST
end R
end W7

end

end Fl4ProofsA64.P1
