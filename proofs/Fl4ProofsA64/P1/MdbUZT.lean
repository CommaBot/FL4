/-
P1 (aarch64, gen 59): **retype's `create_object` step for all 15 kinds** (`Tcb` included, Architect option (a):
`UtZeroA`, no kernel change), and the retype top without `hCO`.

* **`ZTc st H s0 base z len s j`** (the loop invariant MdbUZL's bundle carries, `j` objects created): the kernel-
  state base as at the retype's start `s0`, the not-yet-created part `[base + j·2^z, base + len·2^z)` of the
  window zero (from `UtZeroA` at `s0`: the window lies in the source's free part), and node 0's debug-list head
  (`nwA st s0`, `DEBUG_TCBS`) null, a heap TCB, or one of the `j` new objects (**`HeadOK`**).
* **`field_not_capw`** (a TCB word at offset `≥ 224` is no cap-slot word, `HeapOK`), `in_free_not_capw` (a word of
  the source's free part is none, `capw_off`).
* **`ZTc.capw`** (the bundle's `hZW`: cap-slot writes miss the window and the head word), **`ZTc.start`** (`hZ0`).
* **`create_object.hCOZ`** (the bundle's `hCOZ`) for every type `< 15`: the 12 pure types (`create_object.pureA`),
  `ArmVcpu` / `ArmHighVSpace` (gen 58's `hCO_vcpu` / `hCO_high` and `vcpuW` / `highW`: writes in the first 4 KiB),
  and **`Tcb`** (MdbUZ's `create_object.tcbW`): the affinity word reads 0 (`ZTc`'s zero part), so `debug_append`
  writes node 0's head word (off every `OS` word and the source's free part: case hypotheses `hnC` / `hnF`, the
  P1 `NodePlaced` / P3 `RegionOffNodes` facts) and the old head's `DEBUG_PREV` (a heap TCB's word at offset 3584:
  `field_not_capw`, off the free part by `ValidUntypedA`; or an earlier new TCB's, inside the window's created
  part). Device untypeds create only frames / untypeds (`hdev`, decode: untyped.rs:66).
* **`untyped.retype.mdbSTVU`**: gen 58's `untyped.retype.mdbSTV` with no `hCO` (for `T = H.tcbs`, `Ω = H.omega`):
  from `MdbST ∧ UtRev ∧ ValidUntypedA ∧ UtZeroA` and the node-word facts, `Ok` and `MdbST ∧ UtRev ∧ ValidUntypedA`
  over the grown heap.

No named premise; new definitions and theorems only (case hypotheses: those of `mdbSTV` without `hCO`, plus
`hdev`, `hal`, `hnA` / `hnC` / `hnF` / `hhd0`).
-/
import Fl4ProofsA64.P1.MdbUZL
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts Fl4Proofs.P3

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {Sg : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

/-- **The debug head after `j` objects** (module docstring). -/
def HeadOK (H : Heap) (base z : U64) (j : Nat) (h : U64) : Prop :=
  h = 0#u64 ∨ H h = some .tcb ∨ ∃ j', j' < j ∧ h = bjA base z j'

/-- **The `Tcb` loop invariant** (module docstring). -/
def ZTc (st : machine.Store S) [L : LawfulStore st] (H : Heap) (s0 : S) (base z : U64) (len : Nat) (s : S)
    (j : Nat) : Prop :=
  L.ksb s = L.ksb s0 ∧
  (∀ b : U64, Aligned b → base.val + j * 2 ^ z.val ≤ b.val → b.val < base.val + len * 2 ^ z.val →
    L.mem s b = 0#u64) ∧
  HeadOK H base z j (L.mem s (nwA st s0))

theorem HeadOK.mono {H : Heap} {base z : U64} {j : Nat} {h : U64} (g : HeadOK H base z j h) :
    HeadOK H base z (j + 1) h := by
  rcases g with g | g | ⟨j', hj', e⟩
  · exact Or.inl g
  · exact Or.inr (Or.inl g)
  · exact Or.inr (Or.inr ⟨j', by omega, e⟩)

variable {OS : Set U64} {H : Heap}

/-- **A TCB word at offset `≥ 224` is no cap-slot word.** -/
theorem field_not_capw {Sg : Set U64} (hH : HeapOK H) {t K : U64} (ht : H t = some .tcb) (hK0 : 224 ≤ K.val)
    (hK : K.val < 4096) : ¬ W7.CapW H.tcbs H.omega Sg (wa t K) := by
  have hf := hH.fits t _ ht
  simp only [HKind.bits] at hf
  have hv : (wa t K).val = t.val + K.val := by rw [wa_val]; exact Nat.mod_eq_of_lt (by omega)
  rintro (⟨t', ht', K', hK', e⟩ | ⟨⟨-, q, k, hq, hk, hin⟩, -⟩)
  · have ht'' : H t' = some .tcb := ht'
    have hf' := hH.fits t' _ ht''
    simp only [HKind.bits] at hf'
    have hv' : (wa t' K').val = t'.val + K'.val := by rw [wa_val]; exact Nat.mod_eq_of_lt (by omega)
    have e' := congrArg UScalar.val e
    rw [hv, hv'] at e'
    by_cases htt : t = t'
    · subst htt; omega
    · have hd := hH.disj t _ t' _ ht ht'' htt
      have e12 : 2 ^ HKind.tcb.bits = 4096 := by simp [HKind.bits]
      rw [e12] at hd
      rcases hd with g | g <;> omega
  · unfold InObj at hin
    have hqt : q ≠ t := by
      rintro rfl
      rw [ht] at hq
      injection hq with hq
      subst hq
      rcases hk with h | ⟨z, h⟩ | ⟨z, h⟩ | ⟨h, -⟩ <;> cases h
    rw [hv] at hin
    have hd := hH.disj t _ q k ht hq hqt.symm
    have e12 : 2 ^ HKind.tcb.bits = 4096 := by simp [HKind.bits]
    rw [e12] at hd
    generalize 2 ^ k.bits = d at hd hin
    rcases hd with g | g <;> omega

/-- A word of a RAM untyped's free part is no cap-slot word. -/
theorem in_free_not_capw {Sg : Set U64} (hH : HeapOK H) {s : S} (hV : ValidUntypedA st H OS s) {u p b i : U64}
    (hu : u ∈ OS) (hc : capA st s u = .Untyped p b i false) {w : U64} (h1 : p.val + i.val ≤ w.val)
    (h2 : w.val < p.val + 2 ^ b.val) : ¬ W7.CapW H.tcbs H.omega Sg w := fun hw => by
  rcases capw_off hH hV hu hc hw with g | g <;> omega

section ctx
variable {Sg : Set U64} (hH : HeapOK H) (hO : OSOK H.tcbs H.omega Sg OS) {s0 : S}
  (hV : ValidUntypedA st H OS s0) {src p sb fi : U64} (hsrc : src ∈ OS)
  (hcs : capA st s0 src = .Untyped p sb fi false) {base z : U64} {len : Nat}
  (hA0 : p.val + fi.val ≤ base.val) (hAw : base.val + len * 2 ^ z.val ≤ p.val + 2 ^ sb.val)
  (hnA : Aligned (nwA st s0)) (hnC : ¬ W7.CapW H.tcbs H.omega Sg (nwA st s0))
include hH hO hV hsrc hcs hA0 hAw hnA hnC

/-- **Cap-slot writes keep `ZTc`** (the bundle's `hZW`). -/
theorem ZTc.capw {s s' : S} {j : Nat} (h : ZTc st H s0 base z len s j)
    (hw : WritesIn st s s' (W7.CapW H.tcbs H.omega Sg)) : ZTc st H s0 base z len s' j := by
  obtain ⟨hk, hz0, hhd⟩ := h
  have hk1 : 1 ≤ 2 ^ z.val := Nat.one_le_two_pow
  refine ⟨hw.1.trans hk, fun b hb h1 h2 => ?_, ?_⟩
  · rw [hw.mem_eq hb (in_free_not_capw hH hV hsrc hcs (by omega) (by omega))]
    exact hz0 b hb h1 h2
  · rw [hw.mem_eq hnA hnC]; exact hhd

/-- **`ZTc` at the loop's start** (the bundle's `hZ0`), from `UtZeroA` at the retype's start. -/
theorem ZTc.start (hUZ : UtZeroA st OS s0) (hhd0 : L.mem s0 (nwA st s0) = 0#u64 ∨ H (L.mem s0 (nwA st s0)) = some .tcb)
    {s1 : S} (hw : WritesIn st s0 s1 (fun b => b = src ∨ b = wa src 8#u64)) : ZTc st H s0 base z len s1 0 := by
  have hW : WritesIn st s0 s1 (W7.CapW H.tcbs H.omega Sg) := hw.mono fun b hb => by
    rcases hb with e | e
    · subst e; exact hO.cw0 hsrc
    · subst e; exact hO.cw hsrc (by simp) (by simp)
  refine ⟨hW.1, fun b hb h1 h2 => ?_, ?_⟩
  · rw [hW.mem_eq hb (in_free_not_capw hH hV hsrc hcs (by omega) (by omega))]
    exact hUZ src hsrc p sb fi hcs b hb (by omega) (by omega)
  · rw [hW.mem_eq hnA hnC]
    rcases hhd0 with g | g
    · exact Or.inl g
    · exact Or.inr (Or.inl g)

end ctx

section arch
variable {A : Type _} {ar : machine.Arch A}

theorem zA_1 (us : U64) : (zA 1 us).val = 12 := by simp [zA]

set_option maxHeartbeats 4000000 in
/-- **`create_object`'s step for all 15 kinds** (module docstring; the bundle's `hCOZ` at `ZTc`). -/
theorem create_object.hCOZ {Sg : Set U64} (hA : P0.ArchTotal ar) (hH : HeapOK H)
    (hO : OSOK H.tcbs H.omega Sg OS) {s0 : S} (hV : ValidUntypedA st H OS s0) {src p sb fi : U64} {dev : Bool}
    (hsrc : src ∈ OS) (hcs : capA st s0 src = .Untyped p sb fi dev) (nt us len base : U64) (device : Bool)
    (hn : nt.val < 15) (hdev : dev = true → nt.val ≠ 1 ∧ nt.val ≠ 12 ∧ nt.val ≠ 14)
    (hal : base.val % 8 = 0) (hA0 : p.val + fi.val ≤ base.val)
    (hAw : base.val + len.val * 2 ^ (zA nt.val us).val ≤ p.val + 2 ^ sb.val) (hpf : p.val + 2 ^ sb.val ≤ 2 ^ 64)
    (hnA : Aligned (nwA st s0)) (hnC : ¬ W7.CapW H.tcbs H.omega Sg (nwA st s0))
    (hnF : (nwA st s0).val < p.val + fi.val ∨ p.val + 2 ^ sb.val ≤ (nwA st s0).val) :
    ∀ (s' : S) (a' : A) (j : Nat), j < len.val → ZTc st H s0 base (zA nt.val us) len.val s' j →
      objects.create_object st ar s' a' nt (bjA base (zA nt.val us) j) us device ⦃ r =>
        r.1 = newCapA nt.val (bjA base (zA nt.val us) j) us device ∧ OSKeep st OS s' r.2.1 ∧
        ZTc st H s0 base (zA nt.val us) len.val r.2.1 (j + 1) ⦄ := by
  intro s' a' j hj hZ
  obtain ⟨hk, hzero, hhd⟩ := hZ
  have hnw : nwA st s' = nwA st s0 := nodeAt_of_ksb hk _ _
  have hjk : (j + 1) * 2 ^ (zA nt.val us).val ≤ len.val * 2 ^ (zA nt.val us).val := Nat.mul_le_mul_right _ hj
  rw [Nat.add_mul, Nat.one_mul] at hjk
  have hX1 : 1 ≤ 2 ^ (zA nt.val us).val := Nat.one_le_two_pow
  have hRAM : nt.val = 1 ∨ nt.val = 12 ∨ nt.val = 14 → dev = false := fun h => by
    cases e : dev
    · rfl
    · obtain ⟨a1, a2, a3⟩ := hdev e; omega
  by_cases h1 : nt.val = 1
  · -- `Tcb`
    have hd := hRAM (Or.inl h1)
    subst hd
    have hz12 : (zA nt.val us).val = 12 := by rw [h1]; exact zA_1 us
    have hX : 2 ^ (zA nt.val us).val = 4096 := by rw [hz12]; norm_num
    obtain ⟨hv, h8, hle⟩ := bj_win (z := zA nt.val us) hj (by omega) hal (by omega)
    have hbw : ∀ j', j' < len.val → (bjA base (zA nt.val us) j').val = base.val + j' * 2 ^ (zA nt.val us).val ∧
        (bjA base (zA nt.val us) j').val % 8 = 0 ∧
        (bjA base (zA nt.val us) j').val + 2 ^ (zA nt.val us).val ≤ base.val + len.val * 2 ^ (zA nt.val us).val :=
      fun j' hj' => bj_win (z := zA nt.val us) hj' (by omega) hal (by omega)
    generalize hb0 : bjA base (zA nt.val us) j = b0 at hv h8 hle ⊢
    have hav : (affA b0).val = b0.val + 3520 := by
      unfold affA; rw [wa_val]; have : (3520#u64 : U64).val = 3520 := by simp
      rw [this]; exact Nat.mod_eq_of_lt (by omega)
    have haf : L.mem s' (affA b0) = 0#u64 := by
      have g1 : base.val + j * 2 ^ (zA nt.val us).val ≤ (affA b0).val := by rw [hav]; omega
      have g2 : (affA b0).val < base.val + len.val * 2 ^ (zA nt.val us).val := by rw [hav]; omega
      exact hzero _ (by show _ % 8 = 0; rw [hav]; omega) g1 g2
    have hnW : ¬ InWin b0 4096 (nwA st s0) := fun h => by unfold InWin at h; rcases hnF with g | g <;> omega
    have hh8 : L.mem s' (nwA st s0) ≠ 0#u64 → (L.mem s' (nwA st s0)).val % 8 = 0 := fun h0 => by
      rcases hhd with e | e | ⟨j', hj', e⟩
      · exact absurd e h0
      · have := hH.align _ _ e; simp only [HKind.bits] at this; omega
      · rw [e]; exact (hbw j' (by omega)).2.1
    -- the frame: the new TCB, node 0's head word, the old head's `DEBUG_PREV`
    have hF : ∀ b, TcbWA st s' b0 b → InWin b0 4096 b ∨ b = nwA st s0 ∨
        (L.mem s' (nwA st s0) ≠ 0#u64 ∧ b = dpA (L.mem s' (nwA st s0))) := fun b h => by
      unfold TcbWA at h; rw [hnw] at h; exact h
    have hdpv : ∀ t : U64, t.val + 4096 ≤ 2 ^ 64 → (dpA t).val = t.val + 3584 := fun t ht => by
      unfold dpA; rw [wa_val]; have : (3584#u64 : U64).val = 3584 := by simp
      rw [this]; exact Nat.mod_eq_of_lt (by omega)
    -- every frame word is no cap-slot word and lies below the window's uncreated part or off the free part
    have hoff : ∀ b, TcbWA st s' b0 b → ¬ W7.CapW H.tcbs H.omega Sg b ∧
        (b.val < b0.val + 4096 ∨ b.val < p.val + fi.val ∨ p.val + 2 ^ sb.val ≤ b.val) := fun b hb => by
      rcases hF b hb with h | e | ⟨h0, e⟩
      · unfold InWin at h
        exact ⟨in_free_not_capw hH hV hsrc hcs (by omega) (by omega), Or.inl h.2⟩
      · subst e; exact ⟨hnC, Or.inr hnF⟩
      · rcases hhd with g | g | ⟨j', hj', g⟩
        · exact absurd g h0
        · have hf := hH.fits _ _ g
          simp only [HKind.bits] at hf
          have e3 := hdpv _ hf
          refine ⟨by rw [e]; exact field_not_capw hH g (by simp) (by simp), Or.inr ?_⟩
          have g' := hV src hsrc p sb fi hcs _ .tcb g
          simp only [HKind.bits] at g'
          rw [e, e3]
          rcases g' with g' | g'
          · left; omega
          · right; omega
        · obtain ⟨hv', -, hle'⟩ := hbw j' (by omega)
          have e3 := hdpv (bjA base (zA nt.val us) j') (by omega)
          rw [g] at e
          have hj'' : (j' + 1) * 2 ^ (zA nt.val us).val ≤ j * 2 ^ (zA nt.val us).val := Nat.mul_le_mul_right _ hj'
          rw [Nat.add_mul, Nat.one_mul] at hj''
          refine ⟨by rw [e]; exact in_free_not_capw hH hV hsrc hcs (by rw [e3]; omega) (by rw [e3]; omega),
            Or.inl (by rw [e, e3]; omega)⟩
    refine WP.spec_mono (create_object.tcbW (ar := ar) s' a' nt b0 us device h1 h8 (by omega) haf
      (by rw [hnw]; exact hnA) (by rw [hnw]; exact hnW) (by rw [hnw]; exact hh8)) ?_
    rintro r ⟨hc, hw, hm⟩
    refine ⟨hc, OSKeep.of_writes hO hw fun b hb hF' => (hoff b hF').1 hb, hw.1.trans hk, fun b hb hb1 hb2 => ?_, ?_⟩
    · rw [Nat.add_mul, Nat.one_mul] at hb1
      have g1 : base.val + j * 2 ^ (zA nt.val us).val ≤ b.val := by omega
      rw [hw.mem_eq hb fun hF' => by rcases (hoff b hF').2 with g | g | g <;> omega]
      exact hzero b hb g1 hb2
    · rw [hnw] at hm
      exact Or.inr (Or.inr ⟨j, by omega, hm.trans hb0.symm⟩)
  -- the 4 KiB-writing arch types
  have hwin4 : ∀ (zv : Nat), (zA nt.val us).val = zv → 4096 ≤ 2 ^ zv → 3 ≤ zv → nt.val = 12 ∨ nt.val = 14 →
      (∀ (s1 : S) (a1 : A), objects.create_object st ar s1 a1 nt (bjA base (zA nt.val us) j) us device ⦃ r =>
        r.1 = newCapA nt.val (bjA base (zA nt.val us) j) us device ∧ OSKeep st OS s1 r.2.1 ⦄) →
      (∀ (s1 : S) (a1 : A), (bjA base (zA nt.val us) j).val % 8 = 0 →
        (bjA base (zA nt.val us) j).val + 4096 ≤ 2 ^ 64 →
        objects.create_object st ar s1 a1 nt (bjA base (zA nt.val us) j) us device ⦃ r =>
          r.1 = newCapA nt.val (bjA base (zA nt.val us) j) us device ∧
          WritesIn st s1 r.2.1 (InWin (bjA base (zA nt.val us) j) 4096) ⦄) →
      objects.create_object st ar s' a' nt (bjA base (zA nt.val us) j) us device ⦃ r =>
        r.1 = newCapA nt.val (bjA base (zA nt.val us) j) us device ∧ OSKeep st OS s' r.2.1 ∧
        ZTc st H s0 base (zA nt.val us) len.val r.2.1 (j + 1) ⦄ := by
    intro zv hzv h4 h3 hnt hK hW
    have hX : 4096 ≤ 2 ^ (zA nt.val us).val := by rw [hzv]; exact h4
    obtain ⟨hv, h8, hle⟩ := bj_win (z := zA nt.val us) hj (by omega) hal (by rw [hzv]; exact h3)
    refine WP.spec_mono (spec_andA (hK s' a') (hW s' a' h8 (by omega))) ?_
    rintro r ⟨⟨hc, hk'⟩, -, hw⟩
    refine ⟨hc, hk', hw.1.trans hk, fun b hb hb1 hb2 => ?_, ?_⟩
    · rw [Nat.add_mul, Nat.one_mul] at hb1
      rw [hw.mem_eq hb fun h => by unfold InWin at h; omega]
      exact hzero b hb (by omega) hb2
    · rw [hw.mem_eq hnA fun h => by unfold InWin at h; rcases hnF with g | g <;> omega]
      exact hhd.mono
  by_cases h12 : nt.val = 12
  · have hd := hRAM (Or.inr (Or.inl h12))
    subst hd
    exact hwin4 12 (by rw [h12]; exact zA_12 us) (by norm_num) (by norm_num) (Or.inl h12)
      (fun s1 a1 => create_object.hCO_vcpu hA hH hO hV hsrc hcs nt us len base device h12 hal hA0 hAw hpf s1 a1 j hj)
      (fun s1 a1 h8 hf => create_object.vcpuW hA s1 a1 nt _ us device h12 h8 hf)
  by_cases h14 : nt.val = 14
  · have hd := hRAM (Or.inr (Or.inr h14))
    subst hd
    exact hwin4 13 (by rw [h14]; exact zA_14 us) (by norm_num) (by norm_num) (Or.inr h14)
      (fun s1 a1 => create_object.hCO_high hA hH hO hV hsrc hcs nt us len base device h14 hal hA0 hAw hpf s1 a1 j hj)
      (fun s1 a1 h8 hf => create_object.highW hA s1 a1 nt _ us device h14 h8 hf)
  · rw [create_object.pureA ar s' a' nt _ us device hn h1 h12 h14, WP.spec_ok]
    refine ⟨rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, hk, fun b hb hb1 hb2 => hzero b hb ?_ hb2, hhd.mono⟩
    rw [Nat.add_mul, Nat.one_mul] at hb1
    omega

/-- **Retype (no reset) without `hCO`** (module docstring): gen 58's `untyped.retype.mdbSTV` with the bundle
discharged at `ZTc`. -/
theorem untyped.retype.mdbSTVU {Sg : Set U64} (hA : P0.ArchTotal ar) (hH : HeapOK H)
    (hO : OSOK H.tcbs H.omega Sg OS) {s : S} {H' : Heap} (hS : MdbST st OS s) (hR : UtRev st OS s)
    (hV : ValidUntypedA st H OS s) (hUZ : UtZeroA st OS s) (a : A)
    {src p sb fi : U64} {dev : Bool} (hsrc : src ∈ OS) (hcs : capA st s src = .Untyped p sb fi dev)
    (nt us dcn off len base : U64) (device : Bool) (hdv : device = dev) (hn : nt.val < 15)
    (hz : (zA nt.val us).val < 64) (hdev : dev = true → nt.val ≠ 1 ∧ nt.val ≠ 12 ∧ nt.val ≠ 14)
    (hal : base.val % 8 = 0)
    (hfi : fi.val < 2 ^ sb.val) (hA0 : p.val + fi.val ≤ base.val)
    (hAw : base.val + len.val * 2 ^ (zA nt.val us).val ≤ p.val + 2 ^ sb.val)
    (hH' : ∀ q k, H' q = some k → H q = some k ∨
      (nt.val ≠ 0 ∧ base.val ≤ q.val ∧ q.val + 2 ^ k.bits ≤ base.val + len.val * 2 ^ (zA nt.val us).val))
    (hnA : Aligned (nwA st s)) (hnC : ¬ W7.CapW H.tcbs H.omega Sg (nwA st s))
    (hnF : (nwA st s).val < p.val + fi.val ∨ p.val + 2 ^ sb.val ≤ (nwA st s).val)
    (hhd0 : L.mem s (nwA st s) = 0#u64 ∨ H (L.mem s (nwA st s)) = some .tcb)
    (hdO : ∀ j, j < len.val → djA dcn off j ∈ OS)
    (hdn : ∀ j, j < len.val → capA st s (djA dcn off j) = .Null)
    (hdc : ∀ j, j < len.val → obj.sext48 (djA dcn off j) = ok (djA dcn off j))
    (hinj : ∀ j l, j < len.val → l < len.val → djA dcn off j = djA dcn off l → j = l)
    (hcan : ∀ j, j < len.val → CapRt.Canonical (bjA base (zA nt.val us) j)) (hus : us.val < 64) :
    untyped.retype st ar s a src false base nt us dcn off len device ⦃ r => r.1 = .Ok () ∧
      MdbST st OS r.2.1 ∧ UtRev st OS r.2.1 ∧ ValidUntypedA st H' OS r.2.1 ⦄ := by
  obtain ⟨G, par, hM, -, -, -, -, -, hU⟩ := id hS
  obtain ⟨-, -, hpf⟩ := ut_rangeA (capA_ut_b hcs) (by
    have := hU.reg src hsrc (by rw [hcs]; exact physA_ut _ _ _ _); rwa [hcs] at this)
  -- the RAM facts are needed only for `Tcb` / `ArmVcpu` / `ArmHighVSpace`; for a device source every kind is pure
  by_cases hdv0 : dev = false
  · subst hdv0
    refine WP.spec_mono (untyped.retype.mdbSTVZ ar hO hS hR hV a hsrc hcs nt us dcn off len base device hdv hn hz
      hfi hA0 hAw hH' (Zq := ZTc st H s base (zA nt.val us) len.val)
      (create_object.hCOZ hA hH hO hV hsrc hcs nt us len base device hn hdev hal hA0 hAw hpf hnA hnC hnF)
      (fun s1 s2 j h w => ZTc.capw hH hO hV hsrc hcs hA0 hAw hnA hnC h w)
      (fun s1 w => ZTc.start hH hO hV hsrc hcs hA0 hAw hnA hnC hUZ hhd0 w) hdO hdn hdc hinj hcan hus) ?_
    rintro r ⟨h1, h2, h3, h4, -⟩
    exact ⟨h1, h2, h3, h4⟩
  · have hdt : dev = true := by
      cases dev
      · exact absurd rfl hdv0
      · rfl
    obtain ⟨n1, n12, n14⟩ := hdev hdt
    refine WP.spec_mono (untyped.retype.mdbSTVZ ar hO hS hR hV a hsrc hcs nt us dcn off len base device hdv hn hz
      hfi hA0 hAw hH' (Zq := fun _ _ => True)
      (fun s' a' j _ _ => WP.spec_mono (create_object.pureCO ar (OS := OS) nt us base _ device hn n1 n12 n14 s' a' j)
        fun r ⟨e1, e2⟩ => ⟨e1, e2, trivial⟩)
      (fun _ _ _ _ _ => trivial) (fun _ _ => trivial) hdO hdn hdc hinj hcan hus) ?_
    rintro r ⟨h1, h2, h3, h4, -⟩
    exact ⟨h1, h2, h3, h4⟩

end arch

end ST
end R
end W7

end

end Fl4ProofsA64.P1
