/-
P1 (aarch64, gen 58): **retype (no reset) keeps `ValidUntypedA` over the grown heap**, and the bundle top.

* **`untyped.retype.genF`**: gen 57's `untyped.retype.gen` (untyped.rs:266–288) with the source's new free index
  exposed to the loop invariant's start: `nfi = base + len·2^z − p` (`free_index = free_ref − ptr`, untyped.rs:286).
  The same proof with `htv` / `hnv` of gen 55's `untyped.retype.tree`; hypotheses `hpb` (`p ≤ base`) and `hlt`
  (the new index fits) replace what `tree` derived from `UtInvA`.
* **`LoopV`** (gen 57's `LoopN` with the source's free index pinned), `LoopV.step` (`LoopN.step` and
  `cdt.insert_new_cap.lr`).
* **`untyped.retype.vu`**: from `ValidUntypedA H` at the start, `TreeA` (its `UtInvA`: `reg`, `inc`, `drange`), the
  hypotheses of gen 57's `untyped.retype.nl`, and the device flag of the call being the source's (`hdv`, decode:
  untyped.rs:56 `device = u.is_device`) — `ValidUntypedA H'` at the end for every heap `H'` whose objects are `H`'s or
  new objects inside the window `[base, base + len·2^z)` (none for `nt = 0`: `newKind 0 = none`, QueueRetype). The
  source's free part starts past the window; a new RAM untyped's free part is its whole region, inside the source's
  free part; another RAM untyped `y` sees the window by `drange` / `inc` (disjoint from the source, the source below
  `y`'s free index, or `y` below the source's free index `≤ base`).
* **`untyped.retype.mdbSTV`**: `MdbST ∧ UtRev ∧ ValidUntypedA H` before ⇒ `Ok` and the three after (gen 57's
  `untyped.retype.mdbST` with `vu`).
* **Gen 60**: `genF` is an instance of MdbTreeL's `untyped.retype.genFG`; `untyped.retype.loopVG` is the `LoopV`
  run shared by `vuG` and MdbUZR's `lvR` / `lvD`; `vuG` / `mdbSTVG` are the one proofs of `vu` / `mdbSTV`
  (`Zq := True`) and MdbUZL's `vuZ` / `mdbSTVZ`.

No named premise; case hypotheses those of gen 55–57 (`hCO` included) and `hdv`, `hH'`.
-/
import Fl4ProofsA64.P1.MdbVU
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts Fl4Proofs.P3

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {Sg : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

/-- **`untyped::retype` (no reset) for any loop invariant, the new free index exposed** (module docstring). -/
theorem untyped.retype.genF {A : Type _} (ar : machine.Arch A) {OS : Set U64} (hO : OSOK T Ω Sg OS) {s : S}
    (a : A) {src p sb fi : U64} {dev : Bool} (hsrc : src ∈ OS) (hcs : capA st s src = .Untyped p sb fi dev)
    (nt us dcn off len base : U64) (device : Bool) (hn : nt.val < 15) (hz : (zA nt.val us).val < 64)
    (hfit : base.val + len.val * 2 ^ (zA nt.val us).val ≤ 2 ^ 64) (hpb : p.val ≤ base.val)
    (hlt : base.val + len.val * 2 ^ (zA nt.val us).val - p.val < 2 ^ 64)
    (hCO : ∀ (s' : S) (a' : A) (j : Nat), j < len.val →
      objects.create_object st ar s' a' nt (bjA base (zA nt.val us) j) us device ⦃ r =>
        r.1 = newCapA nt.val (bjA base (zA nt.val us) j) us device ∧ OSKeep st OS s' r.2.1 ⦄)
    {I : S → Nat → Prop}
    (hstart : ∀ (s1 : S) (nfi : U64), nfi.val = base.val + len.val * 2 ^ (zA nt.val us).val - p.val →
      capA st s1 src = .Untyped p sb nfi dev →
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
    (fun _ _ => trivial) (fun s1 nfi hv h1 h2 h3 => hstart s1 nfi (hv hpb hlt) h1 h2 h3) hkeep
    (fun s i hi h _ => WP.spec_mono (hstep s i hi h) fun _ h' => ⟨h', trivial⟩)) fun _ h => ⟨h.1, h.2.1⟩

/-- **After `i` objects, the source's free index pinned** (module docstring). -/
def LoopV (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (s0 : S) (src p sb : U64) (dev : Bool)
    (F : Nat) (dslot : Nat → U64) (cj : Nat → capability.Cap) (s : S) (i : Nat) : Prop :=
  LoopN st OS s0 src p sb dev dslot cj s i ∧ ∃ nfi : U64, nfi.val = F ∧ capA st s src = .Untyped p sb nfi dev

section loopv
variable {OS : Set U64} {s0 : S} {src p sb : U64} {dev : Bool} {F : Nat} {dslot : Nat → U64}
variable {cj : Nat → capability.Cap}

theorem LoopV.step (hO : OSOK T Ω Sg OS) {s : S} {i w : Nat} (hi : i < w)
    (h : LoopV st OS s0 src p sb dev F dslot cj s i) (hsrc : src ∈ OS) (hdO : ∀ j, j < w → dslot j ∈ OS)
    (hdn : ∀ j, j < w → capA st s0 (dslot j) = .Null) (hdc : ∀ j, j < w → obj.sext48 (dslot j) = ok (dslot j))
    (hinj : ∀ j l, j < w → l < w → dslot j = dslot l → j = l) (hsn : ∀ j, j < w → src ≠ dslot j)
    (hwf : ∀ j, j < w → CapRt.EncWf (cj j)) (hcn : ∀ j, j < w → cj j ≠ .Null) :
    cdt.insert_new_cap st s src (dslot i) (cj i) ⦃ s' => LoopV st OS s0 src p sb dev F dslot cj s' (i + 1) ⦄ := by
  obtain ⟨hN', nf, hnf, hsc⟩ := h
  obtain ⟨G, hM, hs, -⟩ := id hN'
  have Fl := hM.lkF hO.nz
  have hnN : NxA st s src ≠ 0#u64 → NxA st s src ∈ OS := fun h0 => ((hM.members _).1 (Fl.nxm _ hs h0)).1
  refine WP.spec_mono (spec_andA (LoopN.step hO hi hN' hdO hdn hdc hinj hsn hwf hcn)
    (cdt.insert_new_cap.lr hO (LR.self s) hsrc (hdO i hi) (hsn i hi) (hdc i hi) (hwf i hi) hnN)) ?_
  rintro s' ⟨h1, -, -, ek⟩
  exact ⟨h1, nf, hnf, by rw [ek src hsrc (hsn i hi)]; exact hsc⟩

end loopv

set_option maxHeartbeats 4000000 in
/-- **The `LoopV` run of retype (no reset), with an extra invariant** (gen 60: the common loop part of `vuG`,
MdbUZR's `uzR` / `uzD` and MdbCovR's retype run): `Ok`, `LoopV` after `len` objects (the source's free index pinned
at `base + len·2^z − p`) and `Zq`. -/
theorem untyped.retype.loopVG {A : Type _} (ar : machine.Arch A) {OS : Set U64} (hO : OSOK T Ω Sg OS)
    {G : List (List U64)} {par : U64 → Option U64} {s : S} (hT : TreeA st OS G par s) (hN : NullLk st OS s)
    (a : A) {src p sb fi : U64} {dev : Bool} (hsrc : src ∈ OS) (hcs : capA st s src = .Untyped p sb fi dev)
    (nt us dcn off len base : U64) (device : Bool) (hn : nt.val < 15) (hz : (zA nt.val us).val < 64)
    (hA : p.val + fi.val ≤ base.val)
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
      LoopV st OS s src p sb dev (base.val + len.val * 2 ^ (zA nt.val us).val - p.val) (djA dcn off)
        (fun j => newCapA nt.val (bjA base (zA nt.val us) j) us device) r.2.1 len.val ∧ Zq r.2.1 len.val ⦄ := by
  have hU := hT.ut
  have hM := hT.lk
  obtain ⟨-, -, hpfit⟩ := ut_rangeA (capA_ut_b hcs) (by
    have := hU.reg src hsrc (by rw [hcs]; exact physA_ut _ _ _ _); rwa [hcs] at this)
  have hsb : 2 ^ sb.val < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (capA_ut_b hcs)
  have hk1 : 1 ≤ 2 ^ (zA nt.val us).val := Nat.one_le_two_pow
  have hs0 : capA st s src ≠ .Null := by rw [hcs]; exact fun h => by cases h
  have hsG : src ∈ G.flatten := (hM.members src).2 ⟨hsrc, hs0⟩
  have hsn : ∀ j, j < len.val → src ≠ djA dcn off j := fun j hj e => hs0 (by rw [e]; exact hdn j hj)
  have hwf : ∀ j, j < len.val → CapRt.EncWf (newCapA nt.val (bjA base (zA nt.val us) j) us device) := fun j hj =>
    newCapA_encWf _ _ _ _ (hcan j hj) hus
  have hfit : base.val + len.val * 2 ^ (zA nt.val us).val ≤ 2 ^ 64 := by omega
  have hpb : p.val ≤ base.val := by omega
  have hlt : base.val + len.val * 2 ^ (zA nt.val us).val - p.val < 2 ^ 64 := by omega
  exact untyped.retype.genFG ar hO a hsrc hcs nt us dcn off len base device hn hz hfit hCOZ hZ0
    (I := LoopV st OS s src p sb dev (base.val + len.val * 2 ^ (zA nt.val us).val - p.val) (djA dcn off)
      (fun j => newCapA nt.val (bjA base (zA nt.val us) j) us device))
    (fun s1 nfi hv h1 h2 h3 => ⟨LoopN.start hM hsG hN hcs h1 h2 h3, nfi, hv hpb hlt, h1⟩)
    (fun s s' i hi h k => ⟨h.1.keep (fun j hj => hdO j (by omega)) hsrc k, h.2.elim fun nf hnf =>
      ⟨nf, hnf.1, (k.capA hsrc).trans hnf.2⟩⟩)
    (fun s i hi h hz => spec_andA
      (LoopV.step hO hi h hsrc hdO hdn hdc hinj hsn hwf (fun j _ => newCapA_ne _ _ _ _))
      (cdt.insert_new_cap.zqW hO hZW (hdO i hi)
        (by obtain ⟨⟨G1, hM1, hs1, -⟩, -⟩ := h; exact MdbLk.nxG hO hM1 hs1) hz))

set_option maxHeartbeats 4000000 in
/-- **Retype (no reset) keeps `ValidUntypedA` over the grown heap, with an extra invariant** (gen 60: the common
proof of gen 58's `untyped.retype.vu` (`Zq := fun _ _ => True`) and gen 59's `vuZ`): `LoopV` along
`untyped.retype.genFG`. -/
theorem untyped.retype.vuG {A : Type _} (ar : machine.Arch A) {OS : Set U64} (hO : OSOK T Ω Sg OS)
    {G : List (List U64)} {par : U64 → Option U64} {s : S} (hT : TreeA st OS G par s) (hN : NullLk st OS s)
    {H H' : Heap} (hV : ValidUntypedA st H OS s) (a : A)
    {src p sb fi : U64} {dev : Bool} (hsrc : src ∈ OS) (hcs : capA st s src = .Untyped p sb fi dev)
    (nt us dcn off len base : U64) (device : Bool) (hdv : device = dev) (hn : nt.val < 15)
    (hz : (zA nt.val us).val < 64)
    (hfi : fi.val < 2 ^ sb.val) (hA : p.val + fi.val ≤ base.val)
    (hAw : base.val + len.val * 2 ^ (zA nt.val us).val ≤ p.val + 2 ^ sb.val)
    (hH' : ∀ q k, H' q = some k → H q = some k ∨
      (nt.val ≠ 0 ∧ base.val ≤ q.val ∧ q.val + 2 ^ k.bits ≤ base.val + len.val * 2 ^ (zA nt.val us).val))
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
      ValidUntypedA st H' OS r.2.1 ∧ Zq r.2.1 len.val ⦄ := by
  have hU := hT.ut
  have hM := hT.lk
  set z := zA nt.val us with hzdef
  have R : ∀ x ∈ OS, ∀ p b i d, capA st s x = .Untyped p b i d →
      baseA (capA st s x) = p.val ∧ topA (capA st s x) = p.val + 2 ^ b.val - 1 ∧ p.val + 2 ^ b.val ≤ 2 ^ 64 :=
    fun x hx p b i d h => by
      rw [h]
      exact ut_rangeA (capA_ut_b h) (by
        have := hU.reg x hx (by rw [h]; exact physA_ut _ _ _ _); rwa [h] at this)
  obtain ⟨sb0, st0, hpfit⟩ := R src hsrc p sb fi dev hcs
  have hsb : 2 ^ sb.val < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (capA_ut_b hcs)
  have hk1 : 1 ≤ 2 ^ z.val := Nat.one_le_two_pow
  have hbj : ∀ j, j < len.val → (bjA base z j).val = base.val + j * 2 ^ z.val ∧
      base.val + j * 2 ^ z.val + 2 ^ z.val ≤ base.val + len.val * 2 ^ z.val := fun j hj => by
    have : (j + 1) * 2 ^ z.val ≤ len.val * 2 ^ z.val := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at this
    exact ⟨bjA_val (by omega), by omega⟩
  refine WP.spec_mono (untyped.retype.loopVG ar hO hT hN a hsrc hcs nt us dcn off len base device hn hz hA hAw
    hCOZ hZW hZ0 hdO hdn hdc hinj hcan hus) ?_
  rintro r ⟨hok, ⟨⟨G', -, -, -, hold, -, hnew⟩, nf, hnf, hsr⟩, hZf⟩
  replace hnf : nf.val = base.val + len.val * 2 ^ z.val - p.val := hnf
  refine ⟨hok, ?_, hZf⟩
  intro y hy p' b' i' hcy q k hq
  by_cases hys : y = src
  · -- the source: its free part starts past the window
    rw [hys, hsr] at hcy
    injection hcy with a1 a2 a3 a4
    subst a1 a2 a3 a4
    rcases hH' q k hq with ho | ⟨-, hq1, hq2⟩
    · rcases hV src hsrc p sb fi hcs q k ho with g | g
      · left; omega
      · right; exact g
    · left; omega
  by_cases hyd : ∃ l, l < len.val ∧ y = djA dcn off l
  · -- a new cap: a RAM untyped only for `nt = 0`, inside the source's free part
    obtain ⟨l, hl, rfl⟩ := hyd
    have e1 : newCapA nt.val (bjA base z l) us device = .Untyped p' b' i' false := (hnew l hl).symm.trans hcy
    obtain ⟨hn0, he⟩ := newCapA_ut (n := nt.val) (base := bjA base z l) (us := us) (dev := device)
      (by rw [e1]; rfl)
    rw [he] at e1
    injection e1 with a1 a2 a3 a4
    subst a1 a2 a3 a4
    subst hdv
    have hzu : z = us := by rw [hzdef, hn0]; first | rfl | simp [zA]
    obtain ⟨hbl, hbl2⟩ := hbj l hl
    have h0v : (0#u64 : U64).val = 0 := by simp
    rcases hH' q k hq with ho | ⟨hn1, -, -⟩
    · rcases hV src hsrc p sb fi hcs q k ho with g | g
      · left; rw [h0v]; omega
      · right; rw [← hzu]; omega
    · exact absurd hn0 hn1
  · -- another RAM untyped: unchanged; the window by `drange` / `inc`
    have hyn : ∀ l, l < len.val → y ≠ djA dcn off l := fun l hl e => hyd ⟨l, hl, e⟩
    rw [hold y hy hys hyn] at hcy
    rcases hH' q k hq with ho | ⟨-, hq1, hq2⟩
    · exact hV y hy p' b' i' hcy q k ho
    obtain ⟨yb, yt, -⟩ := R y hy p' b' i' false hcy
    have hb1 : 1 ≤ 2 ^ b'.val := Nat.one_le_two_pow
    have hsb1 : 1 ≤ 2 ^ sb.val := Nat.one_le_two_pow
    by_cases hD : DisjA (capA st s src) (capA st s y)
    · unfold DisjA at hD
      rw [sb0, st0, yb, yt] at hD
      rcases hD with g | g
      · left; omega
      · right; omega
    · rcases hU.drange y hy p' b' i' false hcy src hsrc (fun e => hys e.symm) (by rw [hcs]; exact physA_ut _ _ _ _) hD with g | g
      · obtain ⟨-, -, g3⟩ := hU.inc y hy p' b' i' false hcy src g
        rw [st0] at g3
        left; omega
      · obtain ⟨-, -, g3⟩ := hU.inc src hsrc p sb fi dev hcs y g
        rw [yt] at g3
        right; omega

/-- **`untyped::retype` without reset keeps `ValidUntypedA` over the grown heap** (module docstring). -/
theorem untyped.retype.vu {A : Type _} (ar : machine.Arch A) {OS : Set U64} (hO : OSOK T Ω Sg OS)
    {G : List (List U64)} {par : U64 → Option U64} {s : S} (hT : TreeA st OS G par s) (hN : NullLk st OS s)
    {H H' : Heap} (hV : ValidUntypedA st H OS s) (a : A)
    {src p sb fi : U64} {dev : Bool} (hsrc : src ∈ OS) (hcs : capA st s src = .Untyped p sb fi dev)
    (nt us dcn off len base : U64) (device : Bool) (hdv : device = dev) (hn : nt.val < 15)
    (hz : (zA nt.val us).val < 64)
    (hfi : fi.val < 2 ^ sb.val) (hA : p.val + fi.val ≤ base.val)
    (hAw : base.val + len.val * 2 ^ (zA nt.val us).val ≤ p.val + 2 ^ sb.val)
    (hH' : ∀ q k, H' q = some k → H q = some k ∨
      (nt.val ≠ 0 ∧ base.val ≤ q.val ∧ q.val + 2 ^ k.bits ≤ base.val + len.val * 2 ^ (zA nt.val us).val))
    (hCO : ∀ (s' : S) (a' : A) (j : Nat), j < len.val →
      objects.create_object st ar s' a' nt (bjA base (zA nt.val us) j) us device ⦃ r =>
        r.1 = newCapA nt.val (bjA base (zA nt.val us) j) us device ∧ OSKeep st OS s' r.2.1 ⦄)
    (hdO : ∀ j, j < len.val → djA dcn off j ∈ OS)
    (hdn : ∀ j, j < len.val → capA st s (djA dcn off j) = .Null)
    (hdc : ∀ j, j < len.val → obj.sext48 (djA dcn off j) = ok (djA dcn off j))
    (hinj : ∀ j l, j < len.val → l < len.val → djA dcn off j = djA dcn off l → j = l)
    (hcan : ∀ j, j < len.val → CapRt.Canonical (bjA base (zA nt.val us) j)) (hus : us.val < 64) :
    untyped.retype st ar s a src false base nt us dcn off len device ⦃ r => r.1 = .Ok () ∧
      ValidUntypedA st H' OS r.2.1 ⦄ :=
  WP.spec_mono (untyped.retype.vuG ar hO hT hN hV a hsrc hcs nt us dcn off len base device hdv hn hz hfi hA hAw hH'
    (Zq := fun _ _ => True) (fun s' a' j hj _ => WP.spec_mono (hCO s' a' j hj) fun r h => ⟨h.1, h.2, trivial⟩)
    (fun _ _ _ _ _ => trivial) (fun _ _ => trivial) hdO hdn hdc hinj hcan hus) fun _ h => ⟨h.1, h.2.1⟩

/-- **Retype (no reset) keeps `MdbST`, `UtRev`, `ValidUntypedA` over the grown heap, and an extra invariant**
(gen 60: the common proof of gen 58's `untyped.retype.mdbSTV` (`Zq := fun _ _ => True`) and gen 59's `mdbSTVZ`). -/
theorem untyped.retype.mdbSTVG {A : Type _} (ar : machine.Arch A) {OS : Set U64} (hO : OSOK T Ω Sg OS) {s : S}
    {H H' : Heap} (hS : MdbST st OS s) (hR : UtRev st OS s) (hV : ValidUntypedA st H OS s) (a : A)
    {src p sb fi : U64} {dev : Bool} (hsrc : src ∈ OS) (hcs : capA st s src = .Untyped p sb fi dev)
    (nt us dcn off len base : U64) (device : Bool) (hdv : device = dev) (hn : nt.val < 15)
    (hz : (zA nt.val us).val < 64)
    (hfi : fi.val < 2 ^ sb.val) (hA : p.val + fi.val ≤ base.val)
    (hAw : base.val + len.val * 2 ^ (zA nt.val us).val ≤ p.val + 2 ^ sb.val)
    (hH' : ∀ q k, H' q = some k → H q = some k ∨
      (nt.val ≠ 0 ∧ base.val ≤ q.val ∧ q.val + 2 ^ k.bits ≤ base.val + len.val * 2 ^ (zA nt.val us).val))
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
      MdbST st OS r.2.1 ∧ UtRev st OS r.2.1 ∧ ValidUntypedA st H' OS r.2.1 ∧ Zq r.2.1 len.val ⦄ := by
  obtain ⟨G, par, hM, hRO, hK, hN, hC, hTr, hU⟩ := id hS
  have hT : TreeA st OS G par s := ⟨hM, hTr, hU⟩
  refine WP.spec_mono (spec_andA (spec_andA (spec_andA
    (untyped.retype.treeG ar hO hT a hsrc hcs nt us dcn off len base device hn hz hfi hA hAw hCOZ hZW hZ0 hdO hdn
      hdc hinj hcan hus)
    (untyped.retype.rkG ar hO hT hRO hK hR a hsrc hcs nt us dcn off len base device hn hz hfi hA hAw hCOZ hZW hZ0
      hdO hdn hdc hinj hcan hus))
    (untyped.retype.nlG ar hO hT hN hC a hsrc hcs nt us dcn off len base device hn hz hfi hA hAw hCOZ hZW hZ0
      hdO hdn hdc hinj hcan hus))
    (untyped.retype.vuG ar hO hT hN hV a hsrc hcs nt us dcn off len base device hdv hn hz hfi hA hAw hH' hCOZ hZW
      hZ0 hdO hdn hdc hinj hcan hus)) ?_
  rintro r ⟨⟨⟨⟨hok, ⟨G1, par1, hT1⟩, hZf⟩, -, ⟨G2, hM2, hRO2, hK2, hR2⟩, -⟩, -, ⟨hN1, hC1⟩, -⟩, -, hV1, -⟩
  exact ⟨hok, ⟨G1, par1, hT1.lk, hRO2.congr (hM2.chains_iff hT1.lk hO.nz), hK2, hN1, hC1, hT1.tree, hT1.ut⟩, hR2,
    hV1, hZf⟩

/-- **Retype (no reset) keeps `MdbST`, `UtRev` and `ValidUntypedA` over the grown heap.** -/
theorem untyped.retype.mdbSTV {A : Type _} (ar : machine.Arch A) {OS : Set U64} (hO : OSOK T Ω Sg OS) {s : S}
    {H H' : Heap} (hS : MdbST st OS s) (hR : UtRev st OS s) (hV : ValidUntypedA st H OS s) (a : A)
    {src p sb fi : U64} {dev : Bool} (hsrc : src ∈ OS) (hcs : capA st s src = .Untyped p sb fi dev)
    (nt us dcn off len base : U64) (device : Bool) (hdv : device = dev) (hn : nt.val < 15)
    (hz : (zA nt.val us).val < 64)
    (hfi : fi.val < 2 ^ sb.val) (hA : p.val + fi.val ≤ base.val)
    (hAw : base.val + len.val * 2 ^ (zA nt.val us).val ≤ p.val + 2 ^ sb.val)
    (hH' : ∀ q k, H' q = some k → H q = some k ∨
      (nt.val ≠ 0 ∧ base.val ≤ q.val ∧ q.val + 2 ^ k.bits ≤ base.val + len.val * 2 ^ (zA nt.val us).val))
    (hCO : ∀ (s' : S) (a' : A) (j : Nat), j < len.val →
      objects.create_object st ar s' a' nt (bjA base (zA nt.val us) j) us device ⦃ r =>
        r.1 = newCapA nt.val (bjA base (zA nt.val us) j) us device ∧ OSKeep st OS s' r.2.1 ⦄)
    (hdO : ∀ j, j < len.val → djA dcn off j ∈ OS)
    (hdn : ∀ j, j < len.val → capA st s (djA dcn off j) = .Null)
    (hdc : ∀ j, j < len.val → obj.sext48 (djA dcn off j) = ok (djA dcn off j))
    (hinj : ∀ j l, j < len.val → l < len.val → djA dcn off j = djA dcn off l → j = l)
    (hcan : ∀ j, j < len.val → CapRt.Canonical (bjA base (zA nt.val us) j)) (hus : us.val < 64) :
    untyped.retype st ar s a src false base nt us dcn off len device ⦃ r => r.1 = .Ok () ∧
      MdbST st OS r.2.1 ∧ UtRev st OS r.2.1 ∧ ValidUntypedA st H' OS r.2.1 ⦄ :=
  WP.spec_mono (untyped.retype.mdbSTVG ar hO hS hR hV a hsrc hcs nt us dcn off len base device hdv hn hz hfi hA hAw
    hH' (Zq := fun _ _ => True) (fun s' a' j hj _ => WP.spec_mono (hCO s' a' j hj) fun r h => ⟨h.1, h.2, trivial⟩)
    (fun _ _ _ _ _ => trivial) (fun _ _ => trivial) hdO hdn hdc hinj hcan hus)
    fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

end ST
end R
end W7

end

end Fl4ProofsA64.P1
