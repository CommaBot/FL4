/-
P1 (aarch64, gen 57): **retype (no reset) keeps `NullLk` and `ClsA`**, so retype produces `MdbST` itself.

* **`untyped.retype.gen`**: `untyped::retype` with `reset = false` (untyped.rs:266–288) for any loop invariant `I`:
  `I` at the state after the source's free index is rewritten (only the source's two cap words change, the source
  stays `Untyped p sb _ dev`, every link word kept), kept by the `OSKeep` steps of `create_object` (`hCO`) and by each
  `insert_new_cap` ⇒ `Ok` and `I` after `len` objects. The prelude of gen 56's `untyped.retype.rk`, the invariant
  abstracted; the fit `base + len·2^z ≤ 2^64` is a hypothesis here (`rk` derives it from `UtInvA`).
* **`LoopN`** (ghost + `MdbLk` + `src` a member + `NullLk`, old slots but the source as at the start, the source
  untyped, the first `i` new slots holding `cj j`), `LoopN.start` / `.keep` / **`.step`** (one `insert_new_cap`: a
  null slot after is null before and none of `src`, `dest`, `src.NEXT`, so its link words are kept — x86 has no
  `NullLk`; the argument of `cdt.insert_with_cap.mdbN`, MdbNull).
* **`untyped.retype.nl`** (gen 55's hypotheses of `untyped.retype.tree`, with `NullLk` / `ClsA` at the start):
  `NullLk ∧ ClsA` at the end. `ClsA`: two new caps of one base are one cap (`bjA_inj`); a new cap's base is no old
  key cap's base (`UtInvA.freeFresh`: old key caps lie off `[p + fi, p + 2^sb)`, the new bases in it); the source
  is untyped, not a key cap.
* **`untyped.retype.mdbST`**: `MdbST ∧ UtRev` before ⇒ `Ok` and `MdbST ∧ UtRev` after (`untyped.retype.treeK` for the
  ghost-carrying facts, `nl` for the two ghost-free ones).
* **Gen 60**: `gen` is an instance of MdbTreeL's `untyped.retype.genFG`; `untyped.retype.nlG` is the one proof of
  `nl` (`Zq := True`) and MdbUZL's `nlZ`.

No named premise; new definitions / theorems only (case hypotheses: those of gen 55/56, `hCO` included).
-/
import Fl4ProofsA64.P1.MdbTreeU
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts Fl4Proofs.P3

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {Sg : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

/-- **`untyped::retype` (no reset) for any loop invariant** (module docstring). -/
theorem untyped.retype.gen {A : Type _} (ar : machine.Arch A) {OS : Set U64} (hO : OSOK T Ω Sg OS) {s : S} (a : A)
    {src p sb fi : U64} {dev : Bool} (hsrc : src ∈ OS) (hcs : capA st s src = .Untyped p sb fi dev)
    (nt us dcn off len base : U64) (device : Bool) (hn : nt.val < 15) (hz : (zA nt.val us).val < 64)
    (hfit : base.val + len.val * 2 ^ (zA nt.val us).val ≤ 2 ^ 64)
    (hCO : ∀ (s' : S) (a' : A) (j : Nat), j < len.val →
      objects.create_object st ar s' a' nt (bjA base (zA nt.val us) j) us device ⦃ r =>
        r.1 = newCapA nt.val (bjA base (zA nt.val us) j) us device ∧ OSKeep st OS s' r.2.1 ⦄)
    {I : S → Nat → Prop}
    (hstart : ∀ (s1 : S) (nfi : U64), capA st s1 src = .Untyped p sb nfi dev →
      (∀ x ∈ OS, x ≠ src → capA st s1 x = capA st s x) →
      (∀ y ∈ OS, L.mem s1 (wa y 16#u64) = L.mem s (wa y 16#u64) ∧ L.mem s1 (wa y 24#u64) = L.mem s (wa y 24#u64)) →
      I s1 0)
    (hkeep : ∀ (s s' : S) (i : Nat), i < len.val → I s i → OSKeep st OS s s' → I s' i)
    (hstep : ∀ (s : S) (i : Nat), i < len.val → I s i →
      cdt.insert_new_cap st s src (djA dcn off i) (newCapA nt.val (bjA base (zA nt.val us) i) us device) ⦃ s' =>
        I s' (i + 1) ⦄) :
    untyped.retype st ar s a src false base nt us dcn off len device ⦃ r => r.1 = .Ok () ∧ I r.2.1 len.val ⦄ :=
  WP.spec_mono (untyped.retype.genFG ar hO a hsrc hcs nt us dcn off len base device hn hz hfit
    (Zq := fun _ _ => True) (fun s' a' j hj _ => WP.spec_mono (hCO s' a' j hj) fun r h => ⟨h.1, h.2, trivial⟩)
    (fun _ _ => trivial) (fun s1 nfi _ h1 h2 h3 => hstart s1 nfi h1 h2 h3) hkeep
    (fun s i hi h _ => WP.spec_mono (hstep s i hi h) fun _ h' => ⟨h', trivial⟩)) fun _ h => ⟨h.1, h.2.1⟩

/-! ## The loop invariant for `NullLk` -/

/-- **After `i` objects** (module docstring). -/
def LoopN (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (s0 : S) (src p sb : U64) (dev : Bool)
    (dslot : Nat → U64) (cj : Nat → capability.Cap) (s : S) (i : Nat) : Prop :=
  ∃ G : List (List U64), MdbLk st OS G s ∧ src ∈ G.flatten ∧ NullLk st OS s ∧
    (∀ x ∈ OS, x ≠ src → (∀ j, j < i → x ≠ dslot j) → capA st s x = capA st s0 x) ∧
    (∃ nfi : U64, capA st s src = .Untyped p sb nfi dev) ∧
    (∀ j, j < i → capA st s (dslot j) = cj j)

section loopn
variable {OS : Set U64} {s0 : S} {src p sb : U64} {dev : Bool} {dslot : Nat → U64} {cj : Nat → capability.Cap}

theorem LoopN.start {G : List (List U64)} (hM : MdbLk st OS G s0) (hsG : src ∈ G.flatten) (hN : NullLk st OS s0)
    {fi : U64} (hcs : capA st s0 src = .Untyped p sb fi dev) {s1 : S} {nfi : U64}
    (h1 : capA st s1 src = .Untyped p sb nfi dev) (h2 : ∀ x ∈ OS, x ≠ src → capA st s1 x = capA st s0 x)
    (h3 : ∀ y ∈ OS, L.mem s1 (wa y 16#u64) = L.mem s0 (wa y 16#u64) ∧
      L.mem s1 (wa y 24#u64) = L.mem s0 (wa y 24#u64)) :
    LoopN st OS s0 src p sb dev dslot cj s1 0 := by
  have hn : ∀ x ∈ OS, (capA st s1 x = .Null ↔ capA st s0 x = .Null) := fun x hx => by
    by_cases e : x = src
    · rw [e, h1, hcs]; constructor <;> intro h <;> cases h
    · rw [h2 x hx e]
  refine ⟨G, hM.keep h3 hn, hsG, hN.keep fun x hx h0 => ⟨(hn x hx).1 h0, (h3 x hx).1, ?_⟩,
    fun x hx hne _ => h2 x hx hne, ⟨nfi, h1⟩, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  unfold NxA; rw [(h3 x hx).2]

theorem LoopN.keep {s s' : S} {i : Nat} (h : LoopN st OS s0 src p sb dev dslot cj s i)
    (hdO : ∀ j, j < i → dslot j ∈ OS) (hsO : src ∈ OS) (k : OSKeep st OS s s') :
    LoopN st OS s0 src p sb dev dslot cj s' i := by
  obtain ⟨G, hM, hs, hN, h1, ⟨nf, hsc⟩, h2⟩ := h
  refine ⟨G, hM.keep (fun x hx => ⟨(k x hx).2.2.1, (k x hx).2.2.2⟩) (fun x hx => by rw [k.capA hx]), hs,
    hN.keep fun x hx h0 => ⟨by rw [← k.capA hx]; exact h0, (k x hx).2.2.1, ?_⟩,
    fun x hx a b => (k.capA hx).trans (h1 x hx a b), ⟨nf, (k.capA hsO).trans hsc⟩,
    fun j hj => (k.capA (hdO j hj)).trans (h2 j hj)⟩
  unfold NxA; rw [(k x hx).2.2.2]

set_option maxHeartbeats 1000000 in
/-- **One `insert_new_cap`**: `NullLk` kept (a null slot after is null before and none of `src`, `dest`,
`src.NEXT`), the cap facts as `LoopK.step`. -/
theorem LoopN.step (hO : OSOK T Ω Sg OS) {s : S} {i w : Nat} (hi : i < w)
    (h : LoopN st OS s0 src p sb dev dslot cj s i) (hdO : ∀ j, j < w → dslot j ∈ OS)
    (hdn : ∀ j, j < w → capA st s0 (dslot j) = .Null) (hdc : ∀ j, j < w → obj.sext48 (dslot j) = ok (dslot j))
    (hinj : ∀ j l, j < w → l < w → dslot j = dslot l → j = l) (hsn : ∀ j, j < w → src ≠ dslot j)
    (hwf : ∀ j, j < w → CapRt.EncWf (cj j)) (hcn : ∀ j, j < w → cj j ≠ .Null) :
    cdt.insert_new_cap st s src (dslot i) (cj i) ⦃ s' => LoopN st OS s0 src p sb dev dslot cj s' (i + 1) ⦄ := by
  obtain ⟨G, hM, hs, hN, h1, ⟨nf, hsc⟩, h2⟩ := h
  have hne : ∀ j, j < i → dslot i ≠ dslot j := fun j hj e => by
    have := hinj i j hi (by omega) e; omega
  have hsOS : src ∈ OS := ((hM.members src).1 hs).1
  have hs0 : capA st s src ≠ .Null := ((hM.members src).1 hs).2
  have hsd : src ≠ dslot i := hsn i hi
  have hd0 : capA st s (dslot i) = .Null := by
    rw [h1 _ (hdO i hi) (fun e => hsd e.symm) hne]; exact hdn i hi
  have dG : dslot i ∉ G.flatten := fun hm => ((hM.members _).1 hm).2 hd0
  have F := hM.lkF hO.nz
  have hNm : NxA st s src ≠ 0#u64 → NxA st s src ∈ G.flatten := F.nxm _ hs
  have hnN : NxA st s src ≠ 0#u64 → NxA st s src ∈ OS := fun hN0 => ((hM.members _).1 (hNm hN0)).1
  refine WP.spec_mono (spec_andA (cdt.insert_new_cap.lk hO hM hs (hdO i hi) hd0 (hdc i hi) (hwf i hi) (hcn i hi))
    (cdt.insert_new_cap.lr hO (LR.self s) hsOS (hdO i hi) hsd (hdc i hi) (hwf i hi) hnN)) ?_
  rintro s' ⟨⟨hM', ed, ek⟩, hL, -, -⟩
  refine ⟨_, hM', (hM'.members src).2 ⟨hsOS, by rw [ek src hsOS hsd]; exact hs0⟩, fun z hz hz0 => ?_,
    fun x hx hxs hn => ?_, ⟨nf, by rw [ek src hsOS hsd]; exact hsc⟩, fun j hj => ?_⟩
  · have zd : z ≠ dslot i := fun e => hcn i hi (by rw [← ed, ← e]; exact hz0)
    rw [ek z hz zd] at hz0
    have zs : z ≠ src := fun e => hs0 (by rw [← e]; exact hz0)
    have nz : z ∉ G.flatten := fun m => ((hM.members z).1 m).2 hz0
    have zN : z ≠ NxA st s src := fun e => by
      by_cases hh : NxA st s src = 0#u64
      · exact hO.nz z hz (e.trans hh)
      · exact nz (e ▸ hNm hh)
    obtain ⟨p0, n0⟩ := hN z hz hz0
    rw [(hL z hz).1, (hL z hz).2]
    simp only [zN, zd, zs, and_false, if_false]
    exact ⟨p0, n0⟩
  · rw [ek x hx (hn i (by omega))]; exact h1 x hx hxs fun j hj => hn j (by omega)
  · by_cases hji : j = i
    · subst hji; exact ed
    · rw [ek _ (hdO j (by omega)) (fun e => hji (hinj j i (by omega) hi e))]; exact h2 j (by omega)

end loopn

/-! ## Retype (no reset) -/

set_option maxHeartbeats 4000000 in
/-- **Retype (no reset) keeps `NullLk` and `ClsA`, with an extra invariant** (gen 60: the common proof of gen
57's `untyped.retype.nl` (`Zq := fun _ _ => True`) and gen 59's `nlZ`): `LoopN` along `untyped.retype.genFG`. -/
theorem untyped.retype.nlG {A : Type _} (ar : machine.Arch A) {OS : Set U64} (hO : OSOK T Ω Sg OS)
    {G : List (List U64)} {par : U64 → Option U64} {s : S} (hT : TreeA st OS G par s) (hN : NullLk st OS s)
    (hC : ClsA st OS s) (a : A)
    {src p sb fi : U64} {dev : Bool} (hsrc : src ∈ OS) (hcs : capA st s src = .Untyped p sb fi dev)
    (nt us dcn off len base : U64) (device : Bool) (hn : nt.val < 15) (hz : (zA nt.val us).val < 64)
    (hfi : fi.val < 2 ^ sb.val) (hA : p.val + fi.val ≤ base.val)
    (hAw : base.val + len.val * 2 ^ (zA nt.val us).val ≤ p.val + 2 ^ sb.val)
    {Zq : S → Nat → Prop}
    (hCOZ : ∀ (s' : S) (a' : A) (j : Nat), j < len.val → Zq s' j →
      objects.create_object st ar s' a' nt (bjA base (zA nt.val us) j) us device ⦃ r =>
        r.1 = newCapA nt.val (bjA base (zA nt.val us) j) us device ∧ OSKeep st OS s' r.2.1 ∧ Zq r.2.1 (j + 1) ⦄)
    (hZW : ∀ (s1 s2 : S) (j : Nat), Zq s1 j → WritesIn st s1 s2 (W7.CapW T Ω Sg) → Zq s2 j)
    (hZ0 : ∀ s1 : S, WritesIn st s s1 (fun b => b = src ∨ b = wa src 8#u64) → Zq s1 0)
    (hdO : ∀ j, j < len.val → djA dcn off j ∈ OS)
    (hdn : ∀ j, j < len.val → capA st s (djA dcn off j) = .Null)
    (hdc : ∀ j, j < len.val → obj.sext48 (djA dcn off j) = ok (djA dcn off j))
    (hinj : ∀ j l, j < len.val → l < len.val → djA dcn off j = djA dcn off l → j = l)
    (hcan : ∀ j, j < len.val → CapRt.Canonical (bjA base (zA nt.val us) j)) (hus : us.val < 64) :
    untyped.retype st ar s a src false base nt us dcn off len device ⦃ r => r.1 = .Ok () ∧
      (NullLk st OS r.2.1 ∧ ClsA st OS r.2.1) ∧ Zq r.2.1 len.val ⦄ := by
  have hU := hT.ut
  have hM := hT.lk
  have hF := hU.freeFresh
  set z := zA nt.val us with hzdef
  have hk1 : 1 ≤ 2 ^ z.val := Nat.one_le_two_pow
  obtain ⟨-, -, hpfit⟩ := ut_rangeA (capA_ut_b hcs) (by
    have := hU.reg src hsrc (by rw [hcs]; exact physA_ut _ _ _ _); rwa [hcs] at this)
  have hs0 : capA st s src ≠ .Null := by rw [hcs]; exact fun h => by cases h
  have hsG : src ∈ G.flatten := (hM.members src).2 ⟨hsrc, hs0⟩
  have hsn : ∀ j, j < len.val → src ≠ djA dcn off j := fun j hj e => hs0 (by rw [e]; exact hdn j hj)
  have hbj : ∀ j, j < len.val → (bjA base z j).val = base.val + j * 2 ^ z.val := fun j hj => by
    have : (j + 1) * 2 ^ z.val ≤ len.val * 2 ^ z.val := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at this
    exact bjA_val (by omega)
  have hfo : ∀ j, j < len.val → ∀ x ∈ OS, RngKeyA (capA st s x) →
      ptrA (capA st s x) ≠ ptrA (newCapA nt.val (bjA base z j) us device) := by
    intro j hj x hx kx e
    rw [newCapA_ptr] at e
    have jk : (j + 1) * 2 ^ z.val ≤ len.val * 2 ^ z.val := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at jk
    refine hF.fresh src hsrc p sb fi dev hcs x hx kx ⟨?_, ?_⟩ <;> rw [e, hbj j hj] <;> omega
  have hfn : ∀ j l, j < len.val → l < len.val → j ≠ l →
      ptrA (newCapA nt.val (bjA base z l) us device) ≠ ptrA (newCapA nt.val (bjA base z j) us device) := by
    intro j l hj hl hjl e
    rw [newCapA_ptr, newCapA_ptr] at e
    exact hjl (bjA_inj (by omega) hl hj e).symm
  have hwf : ∀ j, j < len.val → CapRt.EncWf (newCapA nt.val (bjA base z j) us device) := fun j hj =>
    newCapA_encWf _ _ _ _ (hcan j hj) hus
  have hfit : base.val + len.val * 2 ^ z.val ≤ 2 ^ 64 := by omega
  refine WP.spec_mono (untyped.retype.genFG ar hO a hsrc hcs nt us dcn off len base device hn hz hfit hCOZ hZ0
    (I := LoopN st OS s src p sb dev (djA dcn off) (fun j => newCapA nt.val (bjA base z j) us device))
    (fun s1 nfi _ h1 h2 h3 => LoopN.start hM hsG hN hcs h1 h2 h3)
    (fun s s' i hi h k => h.keep (fun j hj => hdO j (by omega)) hsrc k)
    (fun s i hi h hz => spec_andA (LoopN.step hO hi h hdO hdn hdc hinj hsn hwf (fun j _ => newCapA_ne _ _ _ _))
      (cdt.insert_new_cap.zqW hO hZW (hdO i hi)
        (by obtain ⟨G1, hM1, hs1, -⟩ := h; exact MdbLk.nxG hO hM1 hs1) hz))) ?_
  rintro r ⟨hok, ⟨G', -, -, hN', hF2b, ⟨nf, hsr⟩, hF2a⟩, hZf⟩
  have old : ∀ y ∈ OS, (∀ l, l < len.val → y ≠ djA dcn off l) → RngKeyA (capA st r.2.1 y) →
      capA st r.2.1 y = capA st s y := fun y hy hyn ky => by
    have ys : y ≠ src := fun e => by rw [e, hsr] at ky; exact rngKey_ut ky
    exact hF2b y hy ys hyn
  exact ⟨hok, ⟨hN', ⟨keyPairA clsA hF2a old hfn hfo hC.cls⟩⟩, hZf⟩

/-- **`untyped::retype` without reset keeps `NullLk` and `ClsA`** (module docstring; the hypotheses of
`untyped.retype.tree`). -/
theorem untyped.retype.nl {A : Type _} (ar : machine.Arch A) {OS : Set U64} (hO : OSOK T Ω Sg OS)
    {G : List (List U64)} {par : U64 → Option U64} {s : S} (hT : TreeA st OS G par s) (hN : NullLk st OS s)
    (hC : ClsA st OS s) (a : A)
    {src p sb fi : U64} {dev : Bool} (hsrc : src ∈ OS) (hcs : capA st s src = .Untyped p sb fi dev)
    (nt us dcn off len base : U64) (device : Bool) (hn : nt.val < 15) (hz : (zA nt.val us).val < 64)
    (hfi : fi.val < 2 ^ sb.val) (hA : p.val + fi.val ≤ base.val)
    (hAw : base.val + len.val * 2 ^ (zA nt.val us).val ≤ p.val + 2 ^ sb.val)
    (hCO : ∀ (s' : S) (a' : A) (j : Nat), j < len.val →
      objects.create_object st ar s' a' nt (bjA base (zA nt.val us) j) us device ⦃ r =>
        r.1 = newCapA nt.val (bjA base (zA nt.val us) j) us device ∧ OSKeep st OS s' r.2.1 ⦄)
    (hdO : ∀ j, j < len.val → djA dcn off j ∈ OS)
    (hdn : ∀ j, j < len.val → capA st s (djA dcn off j) = .Null)
    (hdc : ∀ j, j < len.val → obj.sext48 (djA dcn off j) = ok (djA dcn off j))
    (hinj : ∀ j l, j < len.val → l < len.val → djA dcn off j = djA dcn off l → j = l)
    (hcan : ∀ j, j < len.val → CapRt.Canonical (bjA base (zA nt.val us) j)) (hus : us.val < 64) :
    untyped.retype st ar s a src false base nt us dcn off len device ⦃ r => r.1 = .Ok () ∧
      NullLk st OS r.2.1 ∧ ClsA st OS r.2.1 ⦄ :=
  WP.spec_mono (untyped.retype.nlG ar hO hT hN hC a hsrc hcs nt us dcn off len base device hn hz hfi hA hAw
    (Zq := fun _ _ => True) (fun s' a' j hj _ => WP.spec_mono (hCO s' a' j hj) fun r h => ⟨h.1, h.2, trivial⟩)
    (fun _ _ _ _ _ => trivial) (fun _ _ => trivial) hdO hdn hdc hinj hcan hus) fun _ h => ⟨h.1, h.2.1⟩

/-- **Retype (no reset) keeps `MdbST` and `UtRev`** (`untyped.retype.treeK` and `untyped.retype.nl`). -/
theorem untyped.retype.mdbST {A : Type _} (ar : machine.Arch A) {OS : Set U64} (hO : OSOK T Ω Sg OS) {s : S}
    (hS : MdbST st OS s) (hR : UtRev st OS s) (a : A)
    {src p sb fi : U64} {dev : Bool} (hsrc : src ∈ OS) (hcs : capA st s src = .Untyped p sb fi dev)
    (nt us dcn off len base : U64) (device : Bool) (hn : nt.val < 15) (hz : (zA nt.val us).val < 64)
    (hfi : fi.val < 2 ^ sb.val) (hA : p.val + fi.val ≤ base.val)
    (hAw : base.val + len.val * 2 ^ (zA nt.val us).val ≤ p.val + 2 ^ sb.val)
    (hCO : ∀ (s' : S) (a' : A) (j : Nat), j < len.val →
      objects.create_object st ar s' a' nt (bjA base (zA nt.val us) j) us device ⦃ r =>
        r.1 = newCapA nt.val (bjA base (zA nt.val us) j) us device ∧ OSKeep st OS s' r.2.1 ⦄)
    (hdO : ∀ j, j < len.val → djA dcn off j ∈ OS)
    (hdn : ∀ j, j < len.val → capA st s (djA dcn off j) = .Null)
    (hdc : ∀ j, j < len.val → obj.sext48 (djA dcn off j) = ok (djA dcn off j))
    (hinj : ∀ j l, j < len.val → l < len.val → djA dcn off j = djA dcn off l → j = l)
    (hcan : ∀ j, j < len.val → CapRt.Canonical (bjA base (zA nt.val us) j)) (hus : us.val < 64) :
    untyped.retype st ar s a src false base nt us dcn off len device ⦃ r => r.1 = .Ok () ∧
      MdbST st OS r.2.1 ∧ UtRev st OS r.2.1 ⦄ := by
  obtain ⟨G, par, hM, hRO, hK, hN, hC, hTr, hU⟩ := hS
  have hT : TreeA st OS G par s := ⟨hM, hTr, hU⟩
  refine WP.spec_mono (spec_andA
    (untyped.retype.treeK ar hO hT hRO hK hR a hsrc hcs nt us dcn off len base device hn hz hfi hA hAw hCO hdO hdn
      hdc hinj hcan hus)
    (untyped.retype.nl ar hO hT hN hC a hsrc hcs nt us dcn off len base device hn hz hfi hA hAw hCO hdO hdn
      hdc hinj hcan hus)) ?_
  rintro r ⟨⟨hok, G1, par1, hT1, hRO1, hK1, hR1⟩, -, hN1, hC1⟩
  exact ⟨hok, ⟨G1, par1, hT1.lk, hRO1, hK1, hN1, hC1, hT1.tree, hT1.ut⟩, hR1⟩

end ST
end R
end W7

end

end Fl4ProofsA64.P1
