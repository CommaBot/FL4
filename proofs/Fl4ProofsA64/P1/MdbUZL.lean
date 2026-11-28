/-
P1 (aarch64, gen 59): **retype in the loop form whose `create_object` step takes a loop invariant** (Architect
ruling for `Tcb`'s `hCO`): every gen-55…58 retype lemma restated with the ∀-state `hCO` replaced by a bundle over an
abstract extra invariant `Zq : S → Nat → Prop` (`Zq s j`: `j` objects created).

* **The bundle** (the replaced hypothesis `hCO`): `hCOZ` (`create_object` of object `j` from a state with `Zq · j`
  returns `newCapA`, keeps every `OS` word and gives `Zq · (j + 1)`), `hZW` (`Zq` survives any write frame of
  cap-slot words `CapW T Ω Sg`: each `insert_new_cap`), `hZ0` (`Zq · 0` after the source's two cap words are
  rewritten). The ∀-state form is the instance `Zq := fun _ _ => True`; MdbUZT discharges the bundle for all 15
  kinds with the `Tcb` invariant.
* **`cdt.insert_new_cap.capw`**: `insert_new_cap` writes only cap-slot words (its slot, the parent, the parent's old
  `NEXT`; cdt.rs:187–196), from `OSOK` (the slots are `SlotW`); `MdbLk.nxOS` / `LoopA.nx` / `LoopK.nx` /
  `LoopN.nx` (the parent's `NEXT` is null or an `OS` slot, from the loop invariants' `MdbLk`).
* **`objects.create_new_objects_loop.invZ`**: gen 57's `create_new_objects_loop.inv` with the bundle (the invariant
  pair `I ∧ Zq`).
* The gen-55…58 retype runs with the bundle, proofs unchanged but for the loop call: **`untyped.retype.genFZ`**
  (gen 58 `genF`), **`untyped.retype.treeZ`** (gen 55 `tree`, rerouted from `loopA` through `invZ` with `LoopA`),
  **`untyped.retype.rkZ`** (gen 56 `rk`), **`untyped.retype.nlZ`** (gen 57 `nl`, through `genFZ`),
  **`untyped.retype.vuZ`** (gen 58 `vu`), and the bundle top **`untyped.retype.mdbSTVZ`** (gen 58 `mdbSTV`:
  `MdbST ∧ UtRev ∧ ValidUntypedA` and `Zq` at the end).
* **Gen 60**: every theorem here is a one-line instance of the general proofs — `invZ` of MdbTreeL's
  `create_new_objects_loop.genJK`, `genFZ` of `untyped.retype.genFG`, `treeZ` / `rkZ` / `nlZ` / `vuZ` / `mdbSTVZ` of
  `treeG` / `rkG` (MdbTreeK) / `nlG` (MdbTreeN) / `vuG` / `mdbSTVG` (MdbVUR); `capw` of `capwG`.

No named premise; new definitions and theorems only (case hypotheses: those of gen 55–58 with `hCO` replaced by the
bundle).
-/
import Fl4ProofsA64.P1.MdbUZ
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts Fl4Proofs.P3

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {Sg : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

section helpers
variable {OS : Set U64}

/-- The source's two cap words rewritten. -/
theorem wr2_srcW (hO : OSOK T Ω Sg OS) {x : U64} (hx : x ∈ OS) {s : S} {w0 w1 : U64} :
    WritesIn st s (L.wr (L.wr s x w0) (wa x 8#u64) w1) (fun b => b = x ∨ b = wa x 8#u64) :=
  (writesIn_wr (hO.al0 hx)).trans (writesIn_wr (hO.al hx (k := 8#u64) (by simp) (by simp)))

theorem MdbLk.nxOS (hO : OSOK T Ω Sg OS) {G : List (List U64)} {s : S} (hM : MdbLk st OS G s) {src : U64}
    (hs : src ∈ G.flatten) : src ∈ OS ∧ (NxA st s src ≠ 0#u64 → NxA st s src ∈ OS) :=
  MdbLk.nxG hO hM hs

theorem LoopA.nx (hO : OSOK T Ω Sg OS) {par0 : U64 → Option U64} {s1 : S} {src : U64} {dslot : Nat → U64}
    {cj : Nat → capability.Cap} {s : S} {i : Nat} (h : LoopA st OS par0 s1 src dslot cj s i) :
    src ∈ OS ∧ (NxA st s src ≠ 0#u64 → NxA st s src ∈ OS) := by
  obtain ⟨G, par, hM, -, hs, -⟩ := h
  exact MdbLk.nxOS hO hM hs

theorem LoopK.nx (hO : OSOK T Ω Sg OS) {s1 : S} {src : U64} {dslot : Nat → U64}
    {cj : Nat → capability.Cap} {s : S} {i : Nat} (h : LoopK st OS s1 src dslot cj s i) :
    src ∈ OS ∧ (NxA st s src ≠ 0#u64 → NxA st s src ∈ OS) := by
  obtain ⟨G, hM, -, hs, -⟩ := h
  exact MdbLk.nxOS hO hM hs

theorem LoopN.nx (hO : OSOK T Ω Sg OS) {s0 : S} {src p sb : U64} {dev : Bool} {dslot : Nat → U64}
    {cj : Nat → capability.Cap} {s : S} {i : Nat} (h : LoopN st OS s0 src p sb dev dslot cj s i) :
    src ∈ OS ∧ (NxA st s src ≠ 0#u64 → NxA st s src ∈ OS) := by
  obtain ⟨G, hM, hs, -⟩ := h
  exact MdbLk.nxOS hO hM hs

/-- **`insert_new_cap` writes only cap-slot words** (module docstring). -/
theorem cdt.insert_new_cap.capw (hO : OSOK T Ω Sg OS) {s : S} {src dest : U64} {nc : capability.Cap}
    (hsrc : src ∈ OS) (hd : dest ∈ OS) (hnN : NxA st s src ≠ 0#u64 → NxA st s src ∈ OS) :
    cdt.insert_new_cap st s src dest nc ⦃ s' => WritesIn st s s' (W7.CapW T Ω Sg) ⦄ :=
  cdt.insert_new_cap.capwG hO hsrc hd hnN

end helpers

/-- **`create_new_objects`' loop with the invariant-taking `create_object` step** (module docstring). -/
theorem objects.create_new_objects_loop.invZ {A : Type _} (ar : machine.Arch A) {OS : Set U64}
    (hO : OSOK T Ω Sg OS) {cj : Nat → capability.Cap} {I Zq : S → Nat → Prop} (t src dcn off w base us z : U64)
    (dev : Bool) (hz : z.val < 64) (hfit : base.val + w.val * 2 ^ z.val ≤ 2 ^ 64)
    (hCOZ : ∀ (s : S) (a : A) (j : Nat), j < w.val → Zq s j →
      objects.create_object st ar s a t (bjA base z j) us dev ⦃ r => r.1 = cj j ∧ OSKeep st OS s r.2.1 ∧
        Zq r.2.1 (j + 1) ⦄)
    (hZW : ∀ (s1 s2 : S) (j : Nat), Zq s1 j → WritesIn st s1 s2 (W7.CapW T Ω Sg) → Zq s2 j)
    (hkeep : ∀ (s s' : S) (i : Nat), i < w.val → I s i → OSKeep st OS s s' → I s' i)
    (hstep : ∀ (s : S) (i : Nat), i < w.val → I s i →
      cdt.insert_new_cap st s src (djA dcn off i) (cj i) ⦃ s' => I s' (i + 1) ⦄)
    (hnx : ∀ (s : S) (i : Nat), i < w.val → I s i → src ∈ OS ∧ (NxA st s src ≠ 0#u64 → NxA st s src ∈ OS))
    (hdO : ∀ j, j < w.val → djA dcn off j ∈ OS)
    (s : S) (a : A) (hinv : I s 0) (hz0 : Zq s 0) :
    objects.create_new_objects_loop st ar s a t src dcn off w base us dev z 0#u64 ⦃ r =>
      I r.1 w.val ∧ Zq r.1 w.val ⦄ :=
  objects.create_new_objects_loop.genJK ar (J := fun s i => I s i ∧ Zq s i) (K := fun s i => I s i ∧ Zq s (i + 1))
    t src dcn off w base us z dev hz hfit
    (fun s a j hj h => WP.spec_mono (hCOZ s a j hj h.2) fun r hr => ⟨hr.1, hkeep s r.2.1 j hj h.1 hr.2.1, hr.2.2⟩)
    (fun s i hi h => spec_andA (hstep s i hi h.1)
      (cdt.insert_new_cap.zqW hO hZW (hdO i hi) (hnx s i hi h.1) h.2)) s a ⟨hinv, hz0⟩

/-- See the module docstring. -/
theorem untyped.retype.genFZ {A : Type _} (ar : machine.Arch A) {OS : Set U64} (hO : OSOK T Ω Sg OS) {s : S}
    (a : A) {src p sb fi : U64} {dev : Bool} (hsrc : src ∈ OS) (hcs : capA st s src = .Untyped p sb fi dev)
    (nt us dcn off len base : U64) (device : Bool) (hn : nt.val < 15) (hz : (zA nt.val us).val < 64)
    (hfit : base.val + len.val * 2 ^ (zA nt.val us).val ≤ 2 ^ 64) (hpb : p.val ≤ base.val)
    (hlt : base.val + len.val * 2 ^ (zA nt.val us).val - p.val < 2 ^ 64)
    {Zq : S → Nat → Prop}
    (hCOZ : ∀ (s' : S) (a' : A) (j : Nat), j < len.val → Zq s' j →
      objects.create_object st ar s' a' nt (bjA base (zA nt.val us) j) us device ⦃ r =>
        r.1 = newCapA nt.val (bjA base (zA nt.val us) j) us device ∧ OSKeep st OS s' r.2.1 ∧ Zq r.2.1 (j + 1) ⦄)
    (hZW : ∀ (s1 s2 : S) (j : Nat), Zq s1 j → WritesIn st s1 s2 (W7.CapW T Ω Sg) → Zq s2 j)
    (hZ0 : ∀ s1 : S, WritesIn st s s1 (fun b => b = src ∨ b = wa src 8#u64) → Zq s1 0)
    {I : S → Nat → Prop}
    (hstart : ∀ (s1 : S) (nfi : U64), nfi.val = base.val + len.val * 2 ^ (zA nt.val us).val - p.val →
      capA st s1 src = .Untyped p sb nfi dev →
      (∀ x ∈ OS, x ≠ src → capA st s1 x = capA st s x) →
      (∀ y ∈ OS, L.mem s1 (wa y 16#u64) = L.mem s (wa y 16#u64) ∧ L.mem s1 (wa y 24#u64) = L.mem s (wa y 24#u64)) →
      I s1 0)
    (hkeep : ∀ (s s' : S) (i : Nat), i < len.val → I s i → OSKeep st OS s s' → I s' i)
    (hstep : ∀ (s : S) (i : Nat), i < len.val → I s i →
      cdt.insert_new_cap st s src (djA dcn off i) (newCapA nt.val (bjA base (zA nt.val us) i) us device) ⦃ s' =>
        I s' (i + 1) ⦄)
    (hnx : ∀ (s : S) (i : Nat), i < len.val → I s i → src ∈ OS ∧ (NxA st s src ≠ 0#u64 → NxA st s src ∈ OS))
    (hdO : ∀ j, j < len.val → djA dcn off j ∈ OS) :
    untyped.retype st ar s a src false base nt us dcn off len device ⦃ r => r.1 = .Ok () ∧ I r.2.1 len.val ∧
      Zq r.2.1 len.val ⦄ :=
  untyped.retype.genFG ar hO a hsrc hcs nt us dcn off len base device hn hz hfit hCOZ hZ0
    (fun s1 nfi hv h1 h2 h3 => hstart s1 nfi (hv hpb hlt) h1 h2 h3) hkeep
    (fun s i hi h hz => spec_andA (hstep s i hi h) (cdt.insert_new_cap.zqW hO hZW (hdO i hi) (hnx s i hi h) hz))

/-- See the module docstring. -/
theorem untyped.retype.treeZ {A : Type _} (ar : machine.Arch A) {OS : Set U64} (hO : OSOK T Ω Sg OS)
    {G : List (List U64)} {par : U64 → Option U64} {s : S} (hT : TreeA st OS G par s) (a : A)
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
      (∃ G' : List (List U64), ∃ par' : U64 → Option U64, TreeA st OS G' par' r.2.1) ∧ Zq r.2.1 len.val ⦄ :=
  untyped.retype.treeG ar hO hT a hsrc hcs nt us dcn off len base device hn hz hfi hA hAw hCOZ hZW hZ0 hdO hdn hdc
    hinj hcan hus

/-- See the module docstring. -/
theorem untyped.retype.rkZ {A : Type _} (ar : machine.Arch A) {OS : Set U64} (hO : OSOK T Ω Sg OS)
    {G : List (List U64)} {par : U64 → Option U64} {s : S} (hT : TreeA st OS G par s) (hRO : RngOneA64 st G s)
    (hK : KindA st OS s) (hR : UtRev st OS s) (a : A)
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
      (∃ G' : List (List U64), MdbLk st OS G' r.2.1 ∧ RngOneA64 st G' r.2.1 ∧ KindA st OS r.2.1 ∧
        UtRev st OS r.2.1) ∧ Zq r.2.1 len.val ⦄ :=
  untyped.retype.rkG ar hO hT hRO hK hR a hsrc hcs nt us dcn off len base device hn hz hfi hA hAw hCOZ hZW hZ0
    hdO hdn hdc hinj hcan hus

/-- See the module docstring. -/
theorem untyped.retype.nlZ {A : Type _} (ar : machine.Arch A) {OS : Set U64} (hO : OSOK T Ω Sg OS)
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
      (NullLk st OS r.2.1 ∧ ClsA st OS r.2.1) ∧ Zq r.2.1 len.val ⦄ :=
  untyped.retype.nlG ar hO hT hN hC a hsrc hcs nt us dcn off len base device hn hz hfi hA hAw hCOZ hZW hZ0
    hdO hdn hdc hinj hcan hus

/-- See the module docstring. -/
theorem untyped.retype.vuZ {A : Type _} (ar : machine.Arch A) {OS : Set U64} (hO : OSOK T Ω Sg OS)
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
      ValidUntypedA st H' OS r.2.1 ∧ Zq r.2.1 len.val ⦄ :=
  untyped.retype.vuG ar hO hT hN hV a hsrc hcs nt us dcn off len base device hdv hn hz hfi hA hAw hH' hCOZ hZW
    hZ0 hdO hdn hdc hinj hcan hus

/-- **Retype (no reset) keeps `MdbST`, `UtRev`, `ValidUntypedA` over the grown heap, and the extra invariant**
(gen 58's `untyped.retype.mdbSTV` with the bundle). -/
theorem untyped.retype.mdbSTVZ {A : Type _} (ar : machine.Arch A) {OS : Set U64} (hO : OSOK T Ω Sg OS) {s : S}
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
      MdbST st OS r.2.1 ∧ UtRev st OS r.2.1 ∧ ValidUntypedA st H' OS r.2.1 ∧ Zq r.2.1 len.val ⦄ :=
  untyped.retype.mdbSTVG ar hO hS hR hV a hsrc hcs nt us dcn off len base device hdv hn hz hfi hA hAw hH' hCOZ
    hZW hZ0 hdO hdn hdc hinj hcan hus

end ST
end R
end W7

end

end Fl4ProofsA64.P1
