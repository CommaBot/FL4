/-
P1 (aarch64, gen 59): **retype (no reset) keeps `UtZeroA`** — retype consumes the free part it creates in, writes
nothing else of any RAM free part — and the bundle top with it.

* **`RFw`**: the words a retype may write after `j` objects: cap-slot words, the created part
  `[base, base + j·2^z)` of the window (only for the memory-writing kinds `WKA`: `Tcb`, `ArmVcpu`,
  `ArmHighVSpace`), node 0's debug head word and heap TCBs' `DEBUG_PREV` words.
* **`create_object.frZ`**: `create_object` of object `j` under `ZTc` writes only in the created part up to `j + 1`
  (for `WKA` kinds), the head word, and a `DEBUG_PREV` word (of a heap TCB, or of an earlier new TCB: in the created
  part) — MdbUZ's `tcbW` / MdbVUC's `vcpuW` / `highW` / gen 55's `pureA`.
* **`uz_end`**: after a retype whose write frame lies in `RFw` at `len`, `UtZeroA`: the source's free part starts
  past the window (untouched, zero at the start); a new RAM untyped (type 0, which writes nothing) has its region
  inside the source's old free part; any other RAM untyped keeps its cap, and its free part misses the window
  (`DisjA` / `drange` / `inc`, as gen 58's `untyped.retype.vu`), the cap-slot words (`capw_off`), the head word
  (`hnF`, all RAM untypeds) and heap TCB words (`ValidUntypedA`).
* **`untyped.retype.uzR`** (RAM source: MdbUZL's `genFZ` with `LoopV` and `ZTc ∧ RFw`), **`untyped.retype.uzD`**
  (device source: only pure kinds, `hdev`), **`untyped.retype.mdbSTVUZ`**: gen 58's `untyped.retype.mdbSTV`
  without `hCO` and with `UtZeroA` before and after.
* **Gen 60**: the loop runs of `uzR` / `uzD` are `untyped.retype.lvR` / `lvD` (`LoopV` and the frame `RFw`, via
  MdbVUR's `loopVG`), shared with MdbCovR.

No named premise; new definitions and theorems only (case hypotheses: those of `mdbSTVU`, with `hnF` stated for
every RAM untyped).
-/
import Fl4ProofsA64.P1.MdbCov
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts Fl4Proofs.P3

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {Sg : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

/-- The memory-writing kinds of `create_object`. -/
def WKA (nt : U64) : Prop := nt.val = 1 ∨ nt.val = 12 ∨ nt.val = 14

/-- **A retype's write frame after `j` objects** (module docstring). -/
def RFw (st : machine.Store S) [L : LawfulStore st] (H : Heap) (Sg : Set U64) (s0 : S) (wk : Prop) (base z : U64)
    (j : Nat) (b : U64) : Prop :=
  W7.CapW H.tcbs H.omega Sg b ∨ (wk ∧ base.val ≤ b.val ∧ b.val < base.val + j * 2 ^ z.val) ∨ b = nwA st s0 ∨
    ∃ t, H t = some .tcb ∧ b = dpA t

variable {OS : Set U64} {H : Heap}

theorem RFw.mono {Sg : Set U64} {s0 : S} {wk : Prop} {base z : U64} {j : Nat} {b : U64}
    (h : RFw st H Sg s0 wk base z j b) : RFw st H Sg s0 wk base z (j + 1) b := by
  rcases h with h | ⟨w, h1, h2⟩ | h | h
  · exact Or.inl h
  · refine Or.inr (Or.inl ⟨w, h1, ?_⟩)
    have := Nat.mul_le_mul_right (2 ^ z.val) (Nat.le_add_right j 1)
    omega
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

section arch
variable {A : Type _} {ar : machine.Arch A}

set_option maxHeartbeats 2000000 in
/-- **`create_object`'s write frame under `ZTc`** (module docstring). -/
theorem create_object.frZ (hA : P0.ArchTotal ar) (hH : HeapOK H) {s0 : S} {p sb fi : U64}
    (nt us len base : U64) (device : Bool) (hn : nt.val < 15) (hal : base.val % 8 = 0)
    (hA0 : p.val + fi.val ≤ base.val)
    (hAw : base.val + len.val * 2 ^ (zA nt.val us).val ≤ p.val + 2 ^ sb.val) (hpf : p.val + 2 ^ sb.val ≤ 2 ^ 64)
    (hnA : Aligned (nwA st s0))
    (hnF : (nwA st s0).val < p.val + fi.val ∨ p.val + 2 ^ sb.val ≤ (nwA st s0).val) :
    ∀ (s' : S) (a' : A) (j : Nat), j < len.val → ZTc st H s0 base (zA nt.val us) len.val s' j →
      objects.create_object st ar s' a' nt (bjA base (zA nt.val us) j) us device ⦃ r =>
        WritesIn st s' r.2.1 (fun b => (WKA nt ∧ base.val ≤ b.val ∧
          b.val < base.val + (j + 1) * 2 ^ (zA nt.val us).val) ∨ b = nwA st s0 ∨ ∃ t, H t = some .tcb ∧ b = dpA t) ⦄ := by
  intro s' a' j hj hZ
  obtain ⟨hk, hzero, hhd⟩ := hZ
  have hnw : nwA st s' = nwA st s0 := nodeAt_of_ksb hk _ _
  have hX1 : 1 ≤ 2 ^ (zA nt.val us).val := Nat.one_le_two_pow
  have hjk : (j + 1) * 2 ^ (zA nt.val us).val ≤ len.val * 2 ^ (zA nt.val us).val := Nat.mul_le_mul_right _ hj
  rw [Nat.add_mul, Nat.one_mul] at hjk
  have hj1 : (j + 1) * 2 ^ (zA nt.val us).val = j * 2 ^ (zA nt.val us).val + 2 ^ (zA nt.val us).val := by ring
  have hgoal : ∀ (F : U64 → Prop) (r : capability.Cap × S × A), WritesIn st s' r.2.1 F →
      (∀ b, F b → (WKA nt ∧ base.val ≤ b.val ∧ b.val < base.val + (j + 1) * 2 ^ (zA nt.val us).val) ∨
        b = nwA st s0 ∨ ∃ t, H t = some .tcb ∧ b = dpA t) →
      WritesIn st s' r.2.1 (fun b => (WKA nt ∧ base.val ≤ b.val ∧
        b.val < base.val + (j + 1) * 2 ^ (zA nt.val us).val) ∨ b = nwA st s0 ∨ ∃ t, H t = some .tcb ∧ b = dpA t) :=
    fun F r hw hF => hw.mono hF
  by_cases h1 : nt.val = 1
  · have hz12 : (zA nt.val us).val = 12 := by rw [h1]; exact zA_1 us
    have hX : 2 ^ (zA nt.val us).val = 4096 := by rw [hz12]; norm_num
    have hbw : ∀ j', j' < len.val → (bjA base (zA nt.val us) j').val = base.val + j' * 2 ^ (zA nt.val us).val ∧
        (bjA base (zA nt.val us) j').val % 8 = 0 ∧
        (bjA base (zA nt.val us) j').val + 2 ^ (zA nt.val us).val ≤ base.val + len.val * 2 ^ (zA nt.val us).val :=
      fun j' hj' => bj_win (z := zA nt.val us) hj' (by omega) hal (by omega)
    obtain ⟨hv, h8, hle⟩ := hbw j hj
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
    have hdpv : ∀ t : U64, t.val + 4096 ≤ 2 ^ 64 → (dpA t).val = t.val + 3584 := fun t ht => by
      unfold dpA; rw [wa_val]; have : (3584#u64 : U64).val = 3584 := by simp
      rw [this]; exact Nat.mod_eq_of_lt (by omega)
    refine WP.spec_mono (create_object.tcbW (ar := ar) s' a' nt b0 us device h1 h8 (by omega) haf
      (by rw [hnw]; exact hnA) (by rw [hnw]; exact hnW) (by rw [hnw]; exact hh8)) ?_
    rintro r ⟨-, hw, -⟩
    refine hgoal _ r hw fun b hb => ?_
    unfold TcbWA at hb
    rw [hnw] at hb
    rcases hb with h | e | ⟨h0, e⟩
    · unfold InWin at h; exact Or.inl ⟨Or.inl h1, by omega, by omega⟩
    · exact Or.inr (Or.inl e)
    · rcases hhd with g | g | ⟨j', hj', g⟩
      · exact absurd g h0
      · exact Or.inr (Or.inr ⟨_, g, e⟩)
      · obtain ⟨hv', -, hle'⟩ := hbw j' (by omega)
        have e3 := hdpv (bjA base (zA nt.val us) j') (by omega)
        rw [g] at e
        have hj'' : (j' + 1) * 2 ^ (zA nt.val us).val ≤ j * 2 ^ (zA nt.val us).val := Nat.mul_le_mul_right _ hj'
        rw [Nat.add_mul, Nat.one_mul] at hj''
        exact Or.inl ⟨Or.inl h1, by rw [e, e3]; omega, by rw [e, e3]; omega⟩
  have hwin : (nt.val = 12 ∨ nt.val = 14) → 4096 ≤ 2 ^ (zA nt.val us).val → 3 ≤ (zA nt.val us).val →
      (∀ (s1 : S) (a1 : A), (bjA base (zA nt.val us) j).val % 8 = 0 →
        (bjA base (zA nt.val us) j).val + 4096 ≤ 2 ^ 64 →
        objects.create_object st ar s1 a1 nt (bjA base (zA nt.val us) j) us device ⦃ r =>
          r.1 = newCapA nt.val (bjA base (zA nt.val us) j) us device ∧
          WritesIn st s1 r.2.1 (InWin (bjA base (zA nt.val us) j) 4096) ⦄) →
      objects.create_object st ar s' a' nt (bjA base (zA nt.val us) j) us device ⦃ r =>
        WritesIn st s' r.2.1 (fun b => (WKA nt ∧ base.val ≤ b.val ∧
          b.val < base.val + (j + 1) * 2 ^ (zA nt.val us).val) ∨ b = nwA st s0 ∨ ∃ t, H t = some .tcb ∧ b = dpA t) ⦄ := by
    intro hnt h4 h3 hW
    obtain ⟨hv, h8, hle⟩ := bj_win (z := zA nt.val us) hj (by omega) hal h3
    refine WP.spec_mono (hW s' a' h8 (by omega)) ?_
    rintro r ⟨-, hw⟩
    refine hgoal _ r hw fun b hb => ?_
    unfold InWin at hb
    exact Or.inl ⟨Or.inr hnt, by omega, by omega⟩
  by_cases h12 : nt.val = 12
  · have hz' : (zA nt.val us).val = 12 := by rw [h12]; exact zA_12 us
    exact hwin (Or.inl h12) (by rw [hz']; norm_num) (by omega)
      (fun s1 a1 h8 hf => create_object.vcpuW hA s1 a1 nt _ us device h12 h8 hf)
  by_cases h14 : nt.val = 14
  · have hz' : (zA nt.val us).val = 13 := by rw [h14]; exact zA_14 us
    exact hwin (Or.inr h14) (by rw [hz']; norm_num) (by omega)
      (fun s1 a1 h8 hf => create_object.highW hA s1 a1 nt _ us device h14 h8 hf)
  · rw [create_object.pureA ar s' a' nt _ us device hn h1 h12 h14, WP.spec_ok]
    exact (WritesIn.refl _ (fun _ => False)).mono fun b hb => hb.elim

end arch

set_option maxHeartbeats 4000000 in
/-- **`UtZeroA` at the end of a retype** (module docstring). -/
theorem uz_end {Sg : Set U64} (hH : HeapOK H) {par : U64 → Option U64} {s sf : S} (hU : UtInvA st OS par s)
    (hV : ValidUntypedA st H OS s) (hUZ : UtZeroA st OS s) {src p sb fi : U64} {dev : Bool} (hsrc : src ∈ OS)
    (hcs : capA st s src = .Untyped p sb fi dev) (nt us dcn off len base : U64) (device : Bool) (hdv : device = dev)
    (hz : (zA nt.val us).val < 64) (hA0 : p.val + fi.val ≤ base.val)
    (hAw : base.val + len.val * 2 ^ (zA nt.val us).val ≤ p.val + 2 ^ sb.val)
    {nf : U64} (hnf : nf.val = base.val + len.val * 2 ^ (zA nt.val us).val - p.val)
    (hsr : capA st sf src = .Untyped p sb nf dev)
    (hold : ∀ x ∈ OS, x ≠ src → (∀ l, l < len.val → x ≠ djA dcn off l) → capA st sf x = capA st s x)
    (hnew : ∀ l, l < len.val → capA st sf (djA dcn off l) = newCapA nt.val (bjA base (zA nt.val us) l) us device)
    {F : U64 → Prop} {wk : Prop} (hwk : wk → nt.val ≠ 0) (hW : WritesIn st s sf F)
    (hF : ∀ b, F b → RFw st H Sg s wk base (zA nt.val us) len.val b)
    (hnF : ∀ u ∈ OS, ∀ p b i, capA st s u = .Untyped p b i false →
      (nwA st s).val < p.val + i.val ∨ p.val + 2 ^ b.val ≤ (nwA st s).val) :
    UtZeroA st OS sf := by
  set z := zA nt.val us with hzdef
  have R : ∀ x ∈ OS, ∀ p b i d, capA st s x = .Untyped p b i d →
      baseA (capA st s x) = p.val ∧ topA (capA st s x) = p.val + 2 ^ b.val - 1 ∧ p.val + 2 ^ b.val ≤ 2 ^ 64 :=
    fun x hx p b i d h => by
      rw [h]
      exact ut_rangeA (capA_ut_b h) (by
        have := hU.reg x hx (by rw [h]; exact physA_ut _ _ _ _); rwa [h] at this)
  obtain ⟨sb0, st0, hpfit⟩ := R src hsrc p sb fi dev hcs
  have hk1 : 1 ≤ 2 ^ z.val := Nat.one_le_two_pow
  have hbj : ∀ j, j < len.val → (bjA base z j).val = base.val + j * 2 ^ z.val ∧
      base.val + j * 2 ^ z.val + 2 ^ z.val ≤ base.val + len.val * 2 ^ z.val := fun j hj => by
    have : (j + 1) * 2 ^ z.val ≤ len.val * 2 ^ z.val := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at this
    exact ⟨bjA_val (by omega), by omega⟩
  -- a heap TCB's `DEBUG_PREV` word lies off every RAM free part
  have hdpOff : ∀ u ∈ OS, ∀ p' b' i', capA st s u = .Untyped p' b' i' false → ∀ t, H t = some .tcb →
      (dpA t).val < p'.val + i'.val ∨ p'.val + 2 ^ b'.val ≤ (dpA t).val := fun u hu p' b' i' hc t ht => by
    have hf := hH.fits t _ ht
    simp only [HKind.bits] at hf
    have e3 : (dpA t).val = t.val + 3584 := by
      unfold dpA; rw [wa_val]; have : (3584#u64 : U64).val = 3584 := by simp
      rw [this]; exact Nat.mod_eq_of_lt (by omega)
    have g := hV u hu p' b' i' hc t .tcb ht
    simp only [HKind.bits] at g
    rw [e3]; omega
  -- a word of the free part of a RAM untyped `u` at the start, outside the window when `wk`, is kept
  have keep : ∀ u ∈ OS, ∀ p' b' i', capA st s u = .Untyped p' b' i' false → ∀ a : U64, Aligned a →
      p'.val + i'.val ≤ a.val → a.val < p'.val + 2 ^ b'.val →
      (wk → a.val < base.val ∨ base.val + len.val * 2 ^ z.val ≤ a.val) → L.mem sf a = 0#u64 := by
    intro u hu p' b' i' hc a ha h1 h2 hw
    rw [hW.mem_eq ha fun hFa => by
      rcases hF a hFa with g | ⟨w, g1, g2⟩ | g | ⟨t, ht, g⟩
      · rcases capw_off hH hV hu hc g with g' | g' <;> omega
      · rcases hw w with g' | g' <;> omega
      · rcases hnF u hu p' b' i' hc with g' | g' <;> rw [g] at h1 h2 <;> omega
      · rcases hdpOff u hu p' b' i' hc t ht with g' | g' <;> rw [g] at h1 h2 <;> omega]
    exact hUZ u hu p' b' i' hc a ha h1 h2
  intro y hy p' b' i' hcy a ha h1 h2
  by_cases hys : y = src
  · -- the source: its free part starts past the window
    rw [hys, hsr] at hcy
    injection hcy with a1 a2 a3 a4
    subst a1 a2 a3 a4
    exact keep src hsrc p sb fi hcs a ha (by omega) h2 fun _ => Or.inr (by omega)
  by_cases hyd : ∃ l, l < len.val ∧ y = djA dcn off l
  · -- a new cap: a RAM untyped only for `nt = 0`, inside the source's old free part
    obtain ⟨l, hl, rfl⟩ := hyd
    have e1 : newCapA nt.val (bjA base z l) us device = .Untyped p' b' i' false := (hnew l hl).symm.trans hcy
    obtain ⟨hn0, he⟩ := newCapA_ut (n := nt.val) (base := bjA base z l) (us := us) (dev := device)
      (by rw [e1]; rfl)
    rw [he] at e1
    injection e1 with a1 a2 a3 a4
    subst a1 a2 a3 a4
    have hdv' : dev = false := hdv.symm
    subst hdv'
    have hzu : z = us := by rw [hzdef, hn0]; first | rfl | simp [zA]
    obtain ⟨hbl, hbl2⟩ := hbj l hl
    have h0v : (0#u64 : U64).val = 0 := by simp
    rw [h0v] at h1
    rw [← hzu] at h2
    exact keep src hsrc p sb fi hcs a ha (by omega) (by omega) fun w => absurd hn0 (hwk w)
  · -- another RAM untyped: unchanged; the window by `drange` / `inc`
    have hyn : ∀ l, l < len.val → y ≠ djA dcn off l := fun l hl e => hyd ⟨l, hl, e⟩
    rw [hold y hy hys hyn] at hcy
    refine keep y hy p' b' i' hcy a ha h1 h2 fun _ => ?_
    obtain ⟨yb, yt, -⟩ := R y hy p' b' i' false hcy
    have hb1 : 1 ≤ 2 ^ b'.val := Nat.one_le_two_pow
    have hsb1 : 1 ≤ 2 ^ sb.val := Nat.one_le_two_pow
    by_cases hD : DisjA (capA st s src) (capA st s y)
    · unfold DisjA at hD
      rw [sb0, st0, yb, yt] at hD
      rcases hD with g | g
      · right; omega
      · left; omega
    · rcases hU.drange y hy p' b' i' false hcy src hsrc (fun e => hys e.symm)
          (by rw [hcs]; exact physA_ut _ _ _ _) hD with g | g
      · obtain ⟨-, -, g3⟩ := hU.inc y hy p' b' i' false hcy src g
        rw [st0] at g3
        right; omega
      · obtain ⟨-, -, g3⟩ := hU.inc src hsrc p sb fi dev hcs y g
        rw [yt] at g3
        left; omega


/-- `create_object.frZ`'s frame is in `RFw` at `j + 1`. -/
theorem RFw.ofFr {Sg : Set U64} {s0 : S} {nt base z : U64} {j : Nat} {b : U64}
    (h : (WKA nt ∧ base.val ≤ b.val ∧ b.val < base.val + (j + 1) * 2 ^ z.val) ∨ b = nwA st s0 ∨
      ∃ t, H t = some .tcb ∧ b = dpA t) : RFw st H Sg s0 (WKA nt) base z (j + 1) b := by
  rcases h with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

section arch2
variable {A : Type _} {ar : machine.Arch A}

set_option maxHeartbeats 4000000 in
/-- **The `LoopV` run of retype (no reset) from a RAM source, no `hCO`** (gen 60: `uzR`'s loop part, shared
with MdbCovR's `untyped.retype.cov`): `LoopV` after `len` objects and the write frame `RFw`. -/
theorem untyped.retype.lvR {Sg : Set U64} (hA : P0.ArchTotal ar) (hH : HeapOK H)
    (hO : OSOK H.tcbs H.omega Sg OS) {G : List (List U64)} {par : U64 → Option U64} {s : S}
    (hT : TreeA st OS G par s) (hN : NullLk st OS s) (hV : ValidUntypedA st H OS s) (hUZ : UtZeroA st OS s)
    (a : A) {src p sb fi : U64} (hsrc : src ∈ OS) (hcs : capA st s src = .Untyped p sb fi false)
    (nt us dcn off len base : U64) (device : Bool) (hdv : device = false) (hn : nt.val < 15)
    (hz : (zA nt.val us).val < 64) (hal : base.val % 8 = 0)
    (hfi : fi.val < 2 ^ sb.val) (hA0 : p.val + fi.val ≤ base.val)
    (hAw : base.val + len.val * 2 ^ (zA nt.val us).val ≤ p.val + 2 ^ sb.val)
    (hnA : Aligned (nwA st s)) (hnC : ¬ W7.CapW H.tcbs H.omega Sg (nwA st s))
    (hnF : ∀ u ∈ OS, ∀ p b i, capA st s u = .Untyped p b i false →
      (nwA st s).val < p.val + i.val ∨ p.val + 2 ^ b.val ≤ (nwA st s).val)
    (hhd0 : L.mem s (nwA st s) = 0#u64 ∨ H (L.mem s (nwA st s)) = some .tcb)
    (hdO : ∀ j, j < len.val → djA dcn off j ∈ OS)
    (hdn : ∀ j, j < len.val → capA st s (djA dcn off j) = .Null)
    (hdc : ∀ j, j < len.val → obj.sext48 (djA dcn off j) = ok (djA dcn off j))
    (hinj : ∀ j l, j < len.val → l < len.val → djA dcn off j = djA dcn off l → j = l)
    (hcan : ∀ j, j < len.val → CapRt.Canonical (bjA base (zA nt.val us) j)) (hus : us.val < 64) :
    untyped.retype st ar s a src false base nt us dcn off len device ⦃ r => r.1 = .Ok () ∧
      LoopV st OS s src p sb false (base.val + len.val * 2 ^ (zA nt.val us).val - p.val) (djA dcn off)
        (fun j => newCapA nt.val (bjA base (zA nt.val us) j) us device) r.2.1 len.val ∧
      WritesIn st s r.2.1 (RFw st H Sg s (WKA nt) base (zA nt.val us) len.val) ⦄ := by
  have hU := hT.ut
  obtain ⟨-, -, hpfit⟩ := ut_rangeA (capA_ut_b hcs) (by
    have := hU.reg src hsrc (by rw [hcs]; exact physA_ut _ _ _ _); rwa [hcs] at this)
  have hsb : 2 ^ sb.val < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (capA_ut_b hcs)
  have hk1 : 1 ≤ 2 ^ (zA nt.val us).val := Nat.one_le_two_pow
  have hnFs := hnF src hsrc p sb fi hcs
  have hsw : ∀ b, (b = src ∨ b = wa src 8#u64) → W7.CapW H.tcbs H.omega Sg b := fun b hb => by
    rcases hb with e | e
    · subst e; exact hO.cw0 hsrc
    · subst e; exact hO.cw hsrc (by simp) (by simp)
  refine WP.spec_mono (untyped.retype.loopVG ar hO hT hN a hsrc hcs nt us dcn off len base device hn hz hA0 hAw
    (Zq := fun s' j => ZTc st H s base (zA nt.val us) len.val s' j ∧
      WritesIn st s s' (RFw st H Sg s (WKA nt) base (zA nt.val us) j))
    (fun s' a' j hj hq => WP.spec_mono (spec_andA
      (create_object.hCOZ hA hH hO hV hsrc hcs nt us len base device hn (fun h => by cases h) hal hA0 hAw hpfit
        hnA hnC hnFs s' a' j hj hq.1)
      (create_object.frZ hA hH nt us len base device hn hal hA0 hAw hpfit hnA hnFs s' a' j hj hq.1))
      fun r ⟨⟨hc, hk, hz'⟩, hw⟩ => ⟨hc, hk, hz', (hq.2.trans hw).mono fun b hb =>
        hb.elim RFw.mono RFw.ofFr⟩)
    (fun s1 s2 j hq w => ⟨ZTc.capw hH hO hV hsrc hcs hA0 hAw hnA hnC hq.1 w,
      (hq.2.trans w).mono fun b hb => hb.elim id Or.inl⟩)
    (fun s1 w => ⟨ZTc.start hH hO hV hsrc hcs hA0 hAw hnA hnC hUZ hhd0 w, w.mono fun b hb => Or.inl (hsw b hb)⟩)
    hdO hdn hdc hinj hcan hus) ?_
  rintro r ⟨hok, hLV, -, hW⟩
  exact ⟨hok, hLV, hW⟩

/-- **Retype (no reset) from a RAM source keeps `UtZeroA`** (module docstring). -/
theorem untyped.retype.uzR {Sg : Set U64} (hA : P0.ArchTotal ar) (hH : HeapOK H)
    (hO : OSOK H.tcbs H.omega Sg OS) {G : List (List U64)} {par : U64 → Option U64} {s : S}
    (hT : TreeA st OS G par s) (hN : NullLk st OS s) (hV : ValidUntypedA st H OS s) (hUZ : UtZeroA st OS s)
    (a : A) {src p sb fi : U64} (hsrc : src ∈ OS) (hcs : capA st s src = .Untyped p sb fi false)
    (nt us dcn off len base : U64) (device : Bool) (hdv : device = false) (hn : nt.val < 15)
    (hz : (zA nt.val us).val < 64) (hal : base.val % 8 = 0)
    (hfi : fi.val < 2 ^ sb.val) (hA0 : p.val + fi.val ≤ base.val)
    (hAw : base.val + len.val * 2 ^ (zA nt.val us).val ≤ p.val + 2 ^ sb.val)
    (hnA : Aligned (nwA st s)) (hnC : ¬ W7.CapW H.tcbs H.omega Sg (nwA st s))
    (hnF : ∀ u ∈ OS, ∀ p b i, capA st s u = .Untyped p b i false →
      (nwA st s).val < p.val + i.val ∨ p.val + 2 ^ b.val ≤ (nwA st s).val)
    (hhd0 : L.mem s (nwA st s) = 0#u64 ∨ H (L.mem s (nwA st s)) = some .tcb)
    (hdO : ∀ j, j < len.val → djA dcn off j ∈ OS)
    (hdn : ∀ j, j < len.val → capA st s (djA dcn off j) = .Null)
    (hdc : ∀ j, j < len.val → obj.sext48 (djA dcn off j) = ok (djA dcn off j))
    (hinj : ∀ j l, j < len.val → l < len.val → djA dcn off j = djA dcn off l → j = l)
    (hcan : ∀ j, j < len.val → CapRt.Canonical (bjA base (zA nt.val us) j)) (hus : us.val < 64) :
    untyped.retype st ar s a src false base nt us dcn off len device ⦃ r => r.1 = .Ok () ∧
      UtZeroA st OS r.2.1 ⦄ := by
  have hU := hT.ut
  refine WP.spec_mono (untyped.retype.lvR hA hH hO hT hN hV hUZ a hsrc hcs nt us dcn off len base device hdv hn hz hal
    hfi hA0 hAw hnA hnC hnF hhd0 hdO hdn hdc hinj hcan hus) ?_
  rintro r ⟨hok, ⟨⟨G', -, -, -, hold, -, hnew⟩, nf, hnf, hsr⟩, hW⟩
  refine ⟨hok, uz_end hH hU hV hUZ hsrc hcs nt us dcn off len base device hdv hz hA0 hAw hnf hsr hold hnew
    (wk := WKA nt) (fun w h0 => by rcases w with e | e | e <;> omega) hW (fun b hb => hb) hnF⟩

set_option maxHeartbeats 4000000 in
/-- **The `LoopV` run of retype (no reset) from a device source, no `hCO`** (gen 60: `uzD`'s loop part, shared
with MdbCovR's `untyped.retype.cov`): `LoopV` after `len` objects and the write frame `RFw`. -/
theorem untyped.retype.lvD {Sg : Set U64} (hH : HeapOK H) (hO : OSOK H.tcbs H.omega Sg OS)
    {G : List (List U64)} {par : U64 → Option U64} {s : S}
    (hT : TreeA st OS G par s) (hN : NullLk st OS s) (hV : ValidUntypedA st H OS s) (hUZ : UtZeroA st OS s)
    (a : A) {src p sb fi : U64} (hsrc : src ∈ OS) (hcs : capA st s src = .Untyped p sb fi true)
    (nt us dcn off len base : U64) (device : Bool) (hdv : device = true) (hn : nt.val < 15)
    (hz : (zA nt.val us).val < 64) (hdev : nt.val ≠ 1 ∧ nt.val ≠ 12 ∧ nt.val ≠ 14)
    (hfi : fi.val < 2 ^ sb.val) (hA0 : p.val + fi.val ≤ base.val)
    (hAw : base.val + len.val * 2 ^ (zA nt.val us).val ≤ p.val + 2 ^ sb.val)
    (hnF : ∀ u ∈ OS, ∀ p b i, capA st s u = .Untyped p b i false →
      (nwA st s).val < p.val + i.val ∨ p.val + 2 ^ b.val ≤ (nwA st s).val)
    (hdO : ∀ j, j < len.val → djA dcn off j ∈ OS)
    (hdn : ∀ j, j < len.val → capA st s (djA dcn off j) = .Null)
    (hdc : ∀ j, j < len.val → obj.sext48 (djA dcn off j) = ok (djA dcn off j))
    (hinj : ∀ j l, j < len.val → l < len.val → djA dcn off j = djA dcn off l → j = l)
    (hcan : ∀ j, j < len.val → CapRt.Canonical (bjA base (zA nt.val us) j)) (hus : us.val < 64) :
    untyped.retype st ar s a src false base nt us dcn off len device ⦃ r => r.1 = .Ok () ∧
      LoopV st OS s src p sb true (base.val + len.val * 2 ^ (zA nt.val us).val - p.val) (djA dcn off)
        (fun j => newCapA nt.val (bjA base (zA nt.val us) j) us device) r.2.1 len.val ∧
      WritesIn st s r.2.1 (RFw st H Sg s False base (zA nt.val us) len.val) ⦄ := by
  have hU := hT.ut
  obtain ⟨-, -, hpfit⟩ := ut_rangeA (capA_ut_b hcs) (by
    have := hU.reg src hsrc (by rw [hcs]; exact physA_ut _ _ _ _); rwa [hcs] at this)
  have hsb : 2 ^ sb.val < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (capA_ut_b hcs)
  have hk1 : 1 ≤ 2 ^ (zA nt.val us).val := Nat.one_le_two_pow
  have hsw : ∀ b, (b = src ∨ b = wa src 8#u64) → W7.CapW H.tcbs H.omega Sg b := fun b hb => by
    rcases hb with e | e
    · subst e; exact hO.cw0 hsrc
    · subst e; exact hO.cw hsrc (by simp) (by simp)
  obtain ⟨n1, n12, n14⟩ := hdev
  refine WP.spec_mono (untyped.retype.loopVG ar hO hT hN a hsrc hcs nt us dcn off len base device hn hz hA0 hAw
    (Zq := fun s' j => WritesIn st s s' (RFw st H Sg s False base (zA nt.val us) j))
    (fun s' a' j hj hq => by
      rw [create_object.pureA ar s' a' nt _ us device hn n1 n12 n14, WP.spec_ok]
      exact ⟨rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, hq.mono fun b hb => RFw.mono hb⟩)
    (fun s1 s2 j hq w => (hq.trans w).mono fun b hb => hb.elim id Or.inl)
    (fun s1 w => w.mono fun b hb => Or.inl (hsw b hb))
    hdO hdn hdc hinj hcan hus) ?_
  rintro r ⟨hok, hLV, hW⟩
  exact ⟨hok, hLV, hW⟩

/-- **Retype (no reset) from a device source keeps `UtZeroA`** (only pure kinds, `hdev`). -/
theorem untyped.retype.uzD {Sg : Set U64} (hH : HeapOK H) (hO : OSOK H.tcbs H.omega Sg OS)
    {G : List (List U64)} {par : U64 → Option U64} {s : S}
    (hT : TreeA st OS G par s) (hN : NullLk st OS s) (hV : ValidUntypedA st H OS s) (hUZ : UtZeroA st OS s)
    (a : A) {src p sb fi : U64} (hsrc : src ∈ OS) (hcs : capA st s src = .Untyped p sb fi true)
    (nt us dcn off len base : U64) (device : Bool) (hdv : device = true) (hn : nt.val < 15)
    (hz : (zA nt.val us).val < 64) (hdev : nt.val ≠ 1 ∧ nt.val ≠ 12 ∧ nt.val ≠ 14)
    (hfi : fi.val < 2 ^ sb.val) (hA0 : p.val + fi.val ≤ base.val)
    (hAw : base.val + len.val * 2 ^ (zA nt.val us).val ≤ p.val + 2 ^ sb.val)
    (hnF : ∀ u ∈ OS, ∀ p b i, capA st s u = .Untyped p b i false →
      (nwA st s).val < p.val + i.val ∨ p.val + 2 ^ b.val ≤ (nwA st s).val)
    (hdO : ∀ j, j < len.val → djA dcn off j ∈ OS)
    (hdn : ∀ j, j < len.val → capA st s (djA dcn off j) = .Null)
    (hdc : ∀ j, j < len.val → obj.sext48 (djA dcn off j) = ok (djA dcn off j))
    (hinj : ∀ j l, j < len.val → l < len.val → djA dcn off j = djA dcn off l → j = l)
    (hcan : ∀ j, j < len.val → CapRt.Canonical (bjA base (zA nt.val us) j)) (hus : us.val < 64) :
    untyped.retype st ar s a src false base nt us dcn off len device ⦃ r => r.1 = .Ok () ∧
      UtZeroA st OS r.2.1 ⦄ := by
  have hU := hT.ut
  refine WP.spec_mono (untyped.retype.lvD hH hO hT hN hV hUZ a hsrc hcs nt us dcn off len base device hdv hn hz hdev hfi
    hA0 hAw hnF hdO hdn hdc hinj hcan hus) ?_
  rintro r ⟨hok, ⟨⟨G', -, -, -, hold, -, hnew⟩, nf, hnf, hsr⟩, hW⟩
  exact ⟨hok, uz_end hH hU hV hUZ hsrc hcs nt us dcn off len base device hdv hz hA0 hAw hnf hsr hold hnew
    (wk := False) False.elim hW (fun b hb => hb) hnF⟩

/-- **Retype (no reset) without `hCO`, `UtZeroA` carried** (module docstring). -/
theorem untyped.retype.mdbSTVUZ {Sg : Set U64} (hA : P0.ArchTotal ar) (hH : HeapOK H)
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
    (hnF : ∀ u ∈ OS, ∀ p b i, capA st s u = .Untyped p b i false →
      (nwA st s).val < p.val + i.val ∨ p.val + 2 ^ b.val ≤ (nwA st s).val)
    (hhd0 : L.mem s (nwA st s) = 0#u64 ∨ H (L.mem s (nwA st s)) = some .tcb)
    (hdO : ∀ j, j < len.val → djA dcn off j ∈ OS)
    (hdn : ∀ j, j < len.val → capA st s (djA dcn off j) = .Null)
    (hdc : ∀ j, j < len.val → obj.sext48 (djA dcn off j) = ok (djA dcn off j))
    (hinj : ∀ j l, j < len.val → l < len.val → djA dcn off j = djA dcn off l → j = l)
    (hcan : ∀ j, j < len.val → CapRt.Canonical (bjA base (zA nt.val us) j)) (hus : us.val < 64) :
    untyped.retype st ar s a src false base nt us dcn off len device ⦃ r => r.1 = .Ok () ∧
      MdbST st OS r.2.1 ∧ UtRev st OS r.2.1 ∧ ValidUntypedA st H' OS r.2.1 ∧ UtZeroA st OS r.2.1 ⦄ := by
  obtain ⟨G, par, hM, -, -, hN, -, hTr, hU⟩ := id hS
  have hT : TreeA st OS G par s := ⟨hM, hTr, hU⟩
  cases dev
  · refine WP.spec_mono (spec_andA
      (untyped.retype.mdbSTVU hA hH hO hS hR hV hUZ a hsrc hcs nt us dcn off len base device hdv hn hz hdev hal hfi
        hA0 hAw hH' hnA hnC (hnF src hsrc p sb fi hcs) hhd0 hdO hdn hdc hinj hcan hus)
      (untyped.retype.uzR hA hH hO hT hN hV hUZ a hsrc hcs nt us dcn off len base device hdv hn hz hal hfi hA0 hAw
        hnA hnC hnF hhd0 hdO hdn hdc hinj hcan hus)) ?_
    rintro r ⟨⟨h1, h2, h3, h4⟩, -, h5⟩
    exact ⟨h1, h2, h3, h4, h5⟩
  · obtain ⟨n1, n12, n14⟩ := hdev rfl
    refine WP.spec_mono (spec_andA
      (untyped.retype.mdbSTVZ ar hO hS hR hV a hsrc hcs nt us dcn off len base device hdv hn hz hfi hA0 hAw hH'
        (Zq := fun _ _ => True)
        (fun s' a' j _ _ => WP.spec_mono
          (create_object.pureCO ar (OS := OS) nt us base _ device hn n1 n12 n14 s' a' j)
          fun r ⟨e1, e2⟩ => ⟨e1, e2, trivial⟩)
        (fun _ _ _ _ _ => trivial) (fun _ _ => trivial) hdO hdn hdc hinj hcan hus)
      (untyped.retype.uzD hH hO hT hN hV hUZ a hsrc hcs nt us dcn off len base device hdv hn hz ⟨n1, n12, n14⟩ hfi
        hA0 hAw hnF hdO hdn hdc hinj hcan hus)) ?_
    rintro r ⟨⟨h1, h2, h3, h4, -⟩, -, h5⟩
    exact ⟨h1, h2, h3, h4, h5⟩

end arch2

end ST
end R
end W7

end

end Fl4ProofsA64.P1
