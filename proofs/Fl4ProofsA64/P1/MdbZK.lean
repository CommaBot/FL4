/-
P1 (aarch64, gen 62): **`ZombiesFinal` and `KsOffA` in the carried bundle** — `StZ H Cs OS := StA H OS ∧
ZombiesFinal OS ∧ KsOffA Cs OS` (gen 61's two state facts beside gen 60's `StA`; `StZ.toA` gives `StA` back)
through the CNode decode tops and through retype.

* **The CNode decode tops** run MdbUZS's one traversal `cnode.decode.cnodeQ` (gen 62: any invariant `P` with a
  restart step `RsStep` and the cap steps `MvStep` / `InsStep` / `SwStep`):
  - the cap map with the state block kept, **`cnode.decode.cnode_ubm`** (`UBm s s' ∧ ksb s' = ksb s` from the
    decode's start; steps from MdbVU's `ubF` forms) — the `UBm` step form gen 61 owed; **`cnode_ks`**: `KsOffA`
    (`KsOffA.of_ub`);
  - **`cnode.decode.cnode_zf`**: `ZombiesFinal`. Data lemma **`ZombiesFinal.mapA`**: every key cap after is
    `AlikeA` the cap of a witness slot before, witnesses of a `Zombie` and another key cap distinct (a `Zombie` is a
    key cap of its own kind, so its witness held a `Zombie` of the same base). Steps `cdt.move_cap.zfS` (the source
    emptied), `cdt.insert_with_cap.zfS` (the new cap no `Zombie`: MdbTreeD's `copied_cap.nz`, `derive_cap` turns a
    `Zombie` into `Null`; the source kept or made full), `cdt.swap.zfS` (an involution).
  - Bundle tops **`cnode.decode.cnode_stZ`** / **`syscall.decode_invocation.cnode_stZ`** (`StZ` before ⇒ after).
* **Retype** (no reset): MdbUZR's `lvR` / `lvD` (instances of the one function-level proof `untyped.retype.genJK`)
  give `LoopV` and the write frame; **`LoopV.zfK`** (data level): `ZombiesFinal` (a new cap is no `Zombie`,
  `newCapA_nz`, and its base lies in the source's free part, off every old key cap by `FreeFresh`), `KsOffA` (a new
  RAM untyped's region lies in the source's, `RegionOffNodes.sub`; the state block kept by the frame). Top
  **`untyped.retype.stZ`**: `StZ H` before ⇒ `Ok` and `StZ H'` after, gen 59's `hnA` / `hnF` from `KsOffA` and node 0's
  placement (MdbUZK); **`untyped.retype.stZD`**: the destination from `retype_dest` (MdbCovU's `stAD` form).

No named premise; new definitions and theorems only. Case hypotheses as `untyped.retype.stA` / `stAD` minus `hnA`
/ `hnF`, plus node 0's placement (`h0`, `hN0`).
-/
import Fl4ProofsA64.P1.MdbCovU
import Fl4ProofsA64.P1.MdbCovR
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts Fl4Proofs.P3

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {Sg : Set U64}
variable {H : Heap} {Cs Rp Nt : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

variable {OS : Set U64}

/-! ## The cap map through the CNode decode -/

theorem ubmR (s0 : S) : RsStep st OS s0 fun x => UBm st OS s0 x ∧ L.ksb x = L.ksb s0 :=
  fun _ k w => ⟨UBm.keepO k, w.1⟩

theorem cdt.move_cap.ubmS (hO : OSOK T Ω Sg OS) (s0 : S) :
    MvStep st OS fun x => UBm st OS s0 x ∧ L.ksb x = L.ksb s0 :=
  fun _ _ _ _ hma hq hx hy hxy hyc hw hb _ =>
    WP.spec_mono (cdt.move_cap.ubF hO hma hx hy hxy hyc hw hb) fun _ h' => ⟨hq.1.trans h'.2, h'.1.1.trans hq.2⟩

theorem cdt.insert_with_cap.ubmS (hO : OSOK T Ω Sg OS) (s0 : S) :
    InsStep st OS fun x => UBm st OS s0 x ∧ L.ksb x = L.ksb s0 :=
  fun _ _ _ _ _ hma hq hx hy hxy hyc hsc hsc0 hw hb _ _ hfib =>
    WP.spec_mono (cdt.insert_with_cap.ubF hO hma hx hy hxy hyc hsc hsc0 hw hb hfib) fun _ h' =>
      ⟨hq.1.trans h'.2, h'.1.1.trans hq.2⟩

theorem cdt.swap.ubmS (hO : OSOK T Ω Sg OS) (s0 : S) :
    SwStep st OS fun x => UBm st OS s0 x ∧ L.ksb x = L.ksb s0 :=
  fun _ _ _ _ _ hma hq hx1 hx2 hne hs1 hs2 hw1 hw2 hb1 hb2 _ _ =>
    WP.spec_mono (cdt.swap.ubF hO hma hx1 hx2 hne hs1 hs2 hw1 hw2 hb1 hb2) fun _ h' =>
      ⟨hq.1.trans h'.2, h'.1.1.trans hq.2⟩

/-- **`cnode.decode` at the CNode copy family: the cap map from the start, the state block kept** (module
docstring). -/
theorem cnode.decode.cnode_ubm {A : Type _} {ar : machine.Arch A}
    (hO : OSOK H.tcbs H.omega Sg OS) (hW : WinOK H.tcbs H.omega)
    {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st H.tcbs Cs H.omega H X s Q Rq) (hT : SlotTy st H.tcbs H.omega Sg H Rp Nt OS s)
    (hm : MdbST st OS s) {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) {lbl len buf : U64}
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate ∨ lbl = fl4_abi.label.CNodeRotate)
    (c : capability.Cap) (hc : RootOK OS c) (hx : ∀ x ∈ extra.val, x ≠ 0#u64 → x ∈ OS) :
    cnode.decode st ar s a lbl len c buf extra ⦃ r s' _ => UBm st OS s s' ∧ L.ksb s' = L.ksb s ⦄ :=
  cnode.decode.cnodeQ hO hW q hT hm ⟨UBm.refl s, rfl⟩ (ubmR s) (cdt.move_cap.ubmS hO s)
    (cdt.insert_with_cap.ubmS hO s) (cdt.swap.ubmS hO s) a hl c hc hx

/-- **`cnode.decode` at the CNode copy family keeps `KsOffA`.** -/
theorem cnode.decode.cnode_ks {A : Type _} {ar : machine.Arch A}
    (hO : OSOK H.tcbs H.omega Sg OS) (hW : WinOK H.tcbs H.omega)
    {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st H.tcbs Cs H.omega H X s Q Rq) (hT : SlotTy st H.tcbs H.omega Sg H Rp Nt OS s)
    (hm : MdbST st OS s) {Cs' : Set U64} (hK : KsOffA st Cs' OS s)
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) {lbl len buf : U64}
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate ∨ lbl = fl4_abi.label.CNodeRotate)
    (c : capability.Cap) (hc : RootOK OS c) (hx : ∀ x ∈ extra.val, x ≠ 0#u64 → x ∈ OS) :
    cnode.decode st ar s a lbl len c buf extra ⦃ r s' _ => KsOffA st Cs' OS s' ⦄ :=
  WP.spec_mono (cnode.decode.cnode_ubm hO hW q hT hm a hl c hc hx) fun ⟨_, _, _⟩ h => hK.of_ub h.2 h.1

/-! ## `ZombiesFinal` through the CNode decode -/

theorem zombie_of_kind {c : capability.Cap} (h : kindA c = 9) : ∃ p t n, c = .Zombie p t n := by
  cases c <;> first | exact ⟨_, _, _, rfl⟩ | (simp [kindA] at h)

/-- **`ZombiesFinal` along a cap map with `AlikeA` witnesses** (module docstring). -/
theorem ZombiesFinal.mapA {s s' : S} (h : ZombiesFinal st OS s) (f : U64 → U64) (hf : ∀ y ∈ OS, f y ∈ OS)
    (hc : ∀ y ∈ OS, RngKeyA (capA st s' y) → AlikeA (capA st s' y) (capA st s (f y)))
    (hinj : ∀ y1 ∈ OS, ∀ y2 ∈ OS, y1 ≠ y2 → (∃ p t n, capA st s' y1 = .Zombie p t n) →
      RngKeyA (capA st s' y2) → f y1 ≠ f y2) :
    ZombiesFinal st OS s' := by
  intro z hz p t n hcz y hy hyz hky e
  have az := hc z hz (by rw [hcz]; exact RngKeyA.zombie p t n)
  rw [hcz] at az
  obtain ⟨c1, k1⟩ := az.2 (az.1.1 (RngKeyA.zombie p t n))
  obtain ⟨p0, t0, n0, ez⟩ := zombie_of_kind k1.symm
  have pz : p0 = p := by
    have e1 := ptrA_of_cls c1
    rw [ez, ptrA_zombie, ptrA_zombie] at e1
    exact e1.symm
  have ay := hc y hy hky
  have ky0 := ay.1.1 hky
  have py : ptrA (capA st s (f y)) = ptrA (capA st s' y) := (ptrA_of_cls (ay.2 ky0).1).symm
  exact h (f z) (hf z hz) p0 t0 n0 ez (f y) (hf y hy)
    (fun e' => hinj z hz y hy (Ne.symm hyz) ⟨p, t, n, hcz⟩ hky e'.symm) ky0 (by rw [py, e, pz])

/-- **`move_cap`** keeps `ZombiesFinal` (the source emptied). -/
theorem cdt.move_cap.zfS (hO : OSOK T Ω Sg OS) : MvStep st OS (ZombiesFinal st OS) := by
  intro a nc x y hma hq hx hy hxy hyc hw _ ha
  obtain ⟨pp, nn⟩ := hma.lnk hO hx
  refine WP.spec_mono (cdt.move_cap.lrF hO (LR.self a) hx hy hxy hyc hw pp nn) ?_
  rintro s' ⟨-, -, ed, es, ek⟩
  refine hq.mapA (fun z => if z = y then x else z) (fun z hz => by (try dsimp only); split <;> assumption)
    (fun z hz hk => ?_) (fun y1 _ y2 _ hne hz hk e => ?_)
  · try dsimp only
    by_cases a1 : z = y
    · rw [if_pos a1, a1, ed]; exact ha
    · rw [if_neg a1]
      by_cases a2 : z = x
      · rw [a2, es] at hk; exact absurd hk RngKeyA.not_null
      · rw [ek z hz a2 a1]; exact AlikeA.refl _
  · try dsimp only at e
    by_cases a1 : y1 = y
    · have a2 : y2 ≠ y := fun e2 => hne (a1.trans e2.symm)
      rw [if_pos a1, if_neg a2] at e
      rw [← e, es] at hk; exact RngKeyA.not_null hk
    · rw [if_neg a1] at e
      by_cases a2 : y2 = y
      · rw [if_pos a2] at e
        obtain ⟨p, t, n, hz⟩ := hz
        rw [e, es] at hz; cases hz
      · rw [if_neg a2] at e; exact hne e

/-- **`insert_with_cap`** of a non-`Zombie` cap keeps `ZombiesFinal`. -/
theorem cdt.insert_with_cap.zfS (hO : OSOK T Ω Sg OS) : InsStep st OS (ZombiesFinal st OS) := by
  intro a nc sc x y hma hq hx hy hxy hyc hsc hsc0 hw _ ha hnz _
  obtain ⟨-, nn⟩ := hma.lnk hO hx
  refine WP.spec_mono (spec_andA (cdt.insert_with_cap.lrF hO (LR.self a) hx hy hxy hyc hsc hsc0 hw nn)
    (cdt.insert_with_cap.srcU hO hx hy hxy hsc hw nn)) ?_
  rintro s' ⟨⟨-, -, ed, -, -, ek, -⟩, hU⟩
  have hsx : RngKeyA (capA st s' x) → capA st s' x = sc := fun k => by
    rcases hU.1 with e | ⟨p, b, i, e0, i1, -, e1, -⟩
    · exact e
    · rw [e1] at k; exact absurd k rngKey_ut
  refine hq.mapA (fun z => if z = y then x else z) (fun z hz => by (try dsimp only); split <;> assumption)
    (fun z hz hk => ?_) (fun y1 _ y2 _ hne hz hk e => ?_)
  · try dsimp only
    by_cases a1 : z = y
    · rw [if_pos a1, a1, ed, hsc]; exact ha
    · rw [if_neg a1]
      by_cases a2 : z = x
      · rw [a2] at hk ⊢; rw [hsx hk, hsc]; exact AlikeA.refl _
      · rw [ek z hz a2 a1]; exact AlikeA.refl _
  · try dsimp only at e
    by_cases a1 : y1 = y
    · obtain ⟨p, t, n, hz⟩ := hz
      rw [a1, ed] at hz; exact hnz p t n hz
    · rw [if_neg a1] at e
      by_cases a2 : y2 = y
      · rw [if_pos a2] at e
        obtain ⟨p, t, n, hz⟩ := hz
        rw [e] at hz
        have e1 := hsx (by rw [hz]; exact RngKeyA.zombie p t n)
        rw [hz] at e1
        have ksc : RngKeyA sc := by rw [← e1]; exact RngKeyA.zombie p t n
        have kn : kindA nc = 9 := by rw [(ha.2 ksc).2, ← e1] <;> rfl
        obtain ⟨p', t', n', e'⟩ := zombie_of_kind kn
        exact hnz p' t' n' e'
      · rw [if_neg a2] at e; exact hne e

/-- The exchange of two slots. -/
def swF (x1 x2 y : U64) : U64 := if y = x1 then x2 else if y = x2 then x1 else y

theorem swF_inv {x1 x2 : U64} (hne : x1 ≠ x2) (y : U64) : swF x1 x2 (swF x1 x2 y) = y := by
  unfold swF
  by_cases a : y = x1
  · rw [if_pos a, if_neg (Ne.symm hne), if_pos rfl, a]
  · by_cases b : y = x2
    · rw [if_neg a, if_pos b, if_pos rfl, b]
    · rw [if_neg a, if_neg b, if_neg a, if_neg b]

/-- **`swap`** keeps `ZombiesFinal` (the caps exchanged, each `AlikeA` the replaced one). -/
theorem cdt.swap.zfS (hO : OSOK T Ω Sg OS) : SwStep st OS (ZombiesFinal st OS) := by
  intro a c1 c2 x1 x2 hma hq hx1 hx2 hne hs1 hs2 hw1 hw2 _ _ ha1 ha2
  obtain ⟨p1, n1⟩ := hma.lnk hO hx1
  obtain ⟨p2, n2⟩ := hma.lnk hO hx2
  refine WP.spec_mono (cdt.swap.lrWF hO (LR.self a) hx1 hx2 hne hs1 hs2 hw1 hw2 p1 n1 p2 n2) ?_
  rintro s' ⟨-, -, e1, e2, ek⟩
  refine hq.mapA (swF x1 x2) (fun y hy => ?_) (fun y hy _ => ?_) (fun y1 _ y2 _ hne' _ _ e => hne' (by
    rw [← swF_inv hne y1, e, swF_inv hne y2]))
  · unfold swF; split
    · exact hx2
    · split
      · exact hx1
      · exact hy
  · unfold swF
    by_cases a1 : y = x1
    · rw [if_pos a1, a1, e1]; exact ha2
    · rw [if_neg a1]
      by_cases a2 : y = x2
      · rw [if_pos a2, a2, e2]; exact ha1
      · rw [if_neg a2, ek y hy a1 a2]; exact AlikeA.refl _

/-- **`cnode.decode` at the CNode copy family keeps `ZombiesFinal`** (module docstring). -/
theorem cnode.decode.cnode_zf {A : Type _} {ar : machine.Arch A}
    (hO : OSOK H.tcbs H.omega Sg OS) (hW : WinOK H.tcbs H.omega)
    {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st H.tcbs Cs H.omega H X s Q Rq) (hT : SlotTy st H.tcbs H.omega Sg H Rp Nt OS s)
    (hm : MdbST st OS s) (hz : ZombiesFinal st OS s)
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) {lbl len buf : U64}
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate ∨ lbl = fl4_abi.label.CNodeRotate)
    (c : capability.Cap) (hc : RootOK OS c) (hx : ∀ x ∈ extra.val, x ≠ 0#u64 → x ∈ OS) :
    cnode.decode st ar s a lbl len c buf extra ⦃ r s' _ => ZombiesFinal st OS s' ⦄ :=
  cnode.decode.cnodeQ hO hW q hT hm hz (fun _ k _ => hz.recap fun _ hy => Or.inl (k.capA hy))
    (cdt.move_cap.zfS hO) (cdt.insert_with_cap.zfS hO) (cdt.swap.zfS hO) a hl c hc hx

/-! ## The bundle -/

/-- **The carried bundle with `ZombiesFinal` and `KsOffA`** (module docstring). -/
def StZ (st : machine.Store S) [L : LawfulStore st] (H : Heap) (Cs OS : Set U64) (s : S) : Prop :=
  StA st H OS s ∧ ZombiesFinal st OS s ∧ KsOffA st Cs OS s

theorem StZ.toA {s : S} (h : StZ st H Cs OS s) : StA st H OS s := h.1

/-- **`cnode.decode` at CNode Copy / Mint / Move / Mutate / Rotate keeps `StZ`.** -/
theorem cnode.decode.cnode_stZ {A : Type _} {ar : machine.Arch A} (hH : HeapOK H)
    (hO : OSOK H.tcbs H.omega Sg OS) (hW : WinOK H.tcbs H.omega)
    {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st H.tcbs Cs H.omega H X s Q Rq) (hT : SlotTy st H.tcbs H.omega Sg H Rp Nt OS s)
    (hSt : StZ st H Cs OS s) {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) {lbl len buf : U64}
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate ∨ lbl = fl4_abi.label.CNodeRotate)
    (c : capability.Cap) (hc : RootOK OS c) (hh : Held st OS s c) (hx : ∀ x ∈ extra.val, x ≠ 0#u64 → x ∈ OS) :
    cnode.decode st ar s a lbl len c buf extra ⦃ r s' _ => StZ st H Cs OS s' ⦄ := by
  obtain ⟨hA, hz, hK⟩ := hSt
  exact WP.spec_mono (WP.spec_and (cnode.decode.cnode_stAK hH hO hW q hT hA hK a hl c hc hh hx)
    (WP.spec_and (cnode.decode.cnode_zf hO hW q hT hA.1 hz a hl c hc hx)
      (cnode.decode.cnode_ks hO hW q hT hA.1 hK a hl c hc hx)))
    fun ⟨_, _, _⟩ ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩

/-- **CNode Copy / Mint / Move / Mutate / Rotate at `decode_invocation`** of a CNode cap read from an `OS` slot keep
`StZ`. -/
theorem syscall.decode_invocation.cnode_stZ {A : Type _} {ar : machine.Arch A} (hH : HeapOK H)
    (hO : OSOK H.tcbs H.omega Sg OS) (hW : WinOK H.tcbs H.omega)
    {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st H.tcbs Cs H.omega H X s Q Rq) (hT : SlotTy st H.tcbs H.omega Sg H Rp Nt OS s)
    (hSt : StZ st H Cs OS s)
    (a : A) {lbl : U64} (len : U64) (slot : obj.Slot) (cap : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate ∨ lbl = fl4_abi.label.CNodeRotate)
    (hf : capFam cap = .cnode) (hslot : slot ∈ OS) (hcap : obj.Slot.cap st slot s = ok cap)
    (hx : ∀ x ∈ extra.val, x ≠ 0#u64 → x ∈ OS) :
    syscall.decode_invocation st ar s a lbl len slot cap blk call don fp buf extra ⦃ r s' _ =>
      StZ st H Cs OS s' ⦄ :=
  syscall.decode_invocation.cnodeG (P := StZ st H Cs OS) hSt a len slot cap blk call don fp buf extra hf
    (cnode.decode.cnode_stZ hH hO hW q hT hSt a hl cap (RootOK.of_slot hT hslot hcap)
      ⟨slot, hslot, okinj ((capA_eq s slot).symm.trans hcap)⟩ hx)

/-! ## Retype -/

theorem newCapA_nz (n : Nat) (base us : U64) (dev : Bool) : NZA (newCapA n base us dev) := by
  intro p t m
  apply newCapA_ind (fun c => c ≠ .Zombie p t m) <;> intros <;> exact fun h => by cases h

/-- A sub-region of a region off the nodes is off the nodes. -/
theorem RegionOffNodes.sub {s : S} {lo hi lo' hi' : Nat} (h : RegionOffNodes st Cs s lo hi) (h1 : lo ≤ lo')
    (h2 : hi' ≤ hi) (h3 : lo' ≤ hi') : RegionOffNodes st Cs s lo' hi' :=
  ⟨fun c hc => (h.1 c hc).elim (fun e => Or.inl (by omega)) fun e => Or.inr (by omega),
    h.2.elim (fun e => Or.inl (by omega)) fun e => Or.inr (by omega)⟩

/-- **`ZombiesFinal ∧ KsOffA` after the loop** (module docstring). -/
theorem LoopV.zfK {s sf : S} (hZ : ZombiesFinal st OS s) {Cs' : Set U64} (hK : KsOffA st Cs' OS s)
    (hF : FreeFresh st OS s) {src p sb fi : U64} {dev : Bool} (hsrc : src ∈ OS)
    (hcs : capA st s src = .Untyped p sb fi dev) {F w : Nat} {dslot : Nat → U64} {nt : Nat} {base z us : U64}
    {device : Bool} (hdv : device = dev)
    (hA0 : p.val + fi.val ≤ base.val) (hAw : base.val + w * 2 ^ z.val ≤ p.val + 2 ^ sb.val)
    (hfit : base.val + w * 2 ^ z.val ≤ 2 ^ 64) (hz0 : nt = 0 → z = us)
    (h : LoopV st OS s src p sb dev F dslot (fun j => newCapA nt (bjA base z j) us device) sf w)
    (hks : L.ksb sf = L.ksb s) :
    ZombiesFinal st OS sf ∧ KsOffA st Cs' OS sf := by
  obtain ⟨⟨G, -, -, -, hold, ⟨nfi, hsf⟩, hnew⟩, -⟩ := h
  have hbj : ∀ j, j < w → (bjA base z j).val = base.val + j * 2 ^ z.val := fun j hj => by
    have : (j + 1) * 2 ^ z.val ≤ w * 2 ^ z.val := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at this
    exact bjA_val (by have := Nat.one_le_two_pow (n := z.val); omega)
  have hbw : ∀ j, j < w → base.val + j * 2 ^ z.val + 2 ^ z.val ≤ base.val + w * 2 ^ z.val := fun j hj => by
    have : (j + 1) * 2 ^ z.val ≤ w * 2 ^ z.val := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  have hk1 : 1 ≤ 2 ^ z.val := Nat.one_le_two_pow
  -- each `OS` slot after: the source, a new slot, or an old slot with its cap
  have cases3 : ∀ y ∈ OS, y = src ∨ (∃ j, j < w ∧ y = dslot j) ∨ capA st sf y = capA st s y := fun y hy => by
    by_cases ys : y = src
    · exact Or.inl ys
    · by_cases hyd : ∃ j, j < w ∧ y = dslot j
      · exact Or.inr (Or.inl hyd)
      · exact Or.inr (Or.inr (hold y hy ys fun j hj e => hyd ⟨j, hj, e⟩))
  refine ⟨?_, ?_⟩
  · intro z' hz' p' t n hcz y hy hyz hky
    rcases cases3 z' hz' with e | ⟨j, hj, e⟩ | e
    · rw [e, hsf] at hcz; cases hcz
    · rw [e, hnew j hj] at hcz; exact (newCapA_nz _ _ _ _ p' t n hcz).elim
    · rw [e] at hcz
      rcases cases3 y hy with e' | ⟨l, hl, e'⟩ | e'
      · rw [e', hsf] at hky; exact absurd hky rngKey_ut
      · rw [e', hnew l hl, newCapA_ptr]
        intro ep
        have kz : RngKeyA (capA st s z') := by rw [hcz]; exact RngKeyA.zombie p' t n
        have pz : ptrA (capA st s z') = p' := by rw [hcz, ptrA_zombie]
        refine hF.fresh src hsrc p sb fi dev hcs z' hz' kz ⟨?_, ?_⟩ <;> rw [pz, ← ep, hbj l hl] <;>
          have := hbw l hl <;> omega
      · rw [e'] at hky ⊢; exact hZ z' hz' p' t n hcz y hy hyz hky
  · intro u hu p' b i hcu
    have tr : ∀ lo hi, RegionOffNodes st Cs' s lo hi → RegionOffNodes st Cs' sf lo hi := fun lo hi g => by
      unfold RegionOffNodes LawfulStore.nodeBase at g ⊢; rw [hks]; exact g
    rcases cases3 u hu with e | ⟨j, hj, e⟩ | e
    · rw [e, hsf] at hcu
      injection hcu with e1 e2 _ e4
      subst e1 e2 e4
      exact tr _ _ (hK src hsrc p sb fi hcs)
    · rw [e, hnew j hj] at hcu
      try beta_reduce at hcu
      obtain ⟨hn0, hnc⟩ := newCapA_ut (n := nt) (base := bjA base z j) (us := us) (dev := device)
        (by rw [hcu]; rfl)
      rw [hnc] at hcu
      injection hcu with e1 e2 _ e4
      subst e1 e2
      have hz := hz0 hn0
      subst hz
      have hd0 : dev = false := by rw [← hdv, e4]
      rw [hd0] at hcs
      refine tr _ _ (RegionOffNodes.sub (hK src hsrc p sb fi hcs) ?_ ?_ ?_) <;> rw [hbj j hj] <;> have := hbw j hj <;> omega
    · rw [e] at hcu; exact tr _ _ (hK u hu p' b i hcu)

section arch
variable {A : Type _} {ar : machine.Arch A}

set_option maxHeartbeats 1000000 in
/-- **Retype (no reset) carries `StZ`** (module docstring). -/
theorem untyped.retype.stZ (hA : P0.ArchTotal ar) (hH : HeapOK H)
    (hO : OSOK H.tcbs H.omega Sg OS) {s : S} {H' : Heap} {Cs : Set U64} (hSt : StZ st H Cs OS s) (a : A)
    {src p sb fi : U64} {dev : Bool} (hsrc : src ∈ OS) (hcs : capA st s src = .Untyped p sb fi dev)
    (nt us dcn off len base : U64) (device : Bool) (hdv : device = dev) (hn : nt.val < 15)
    (hz : (zA nt.val us).val < 64) (hdev : dev = true → nt.val ≠ 1 ∧ nt.val ≠ 12 ∧ nt.val ≠ 14)
    (hal : base.val % 8 = 0)
    (hfi : fi.val < 2 ^ sb.val) (hA0 : p.val + fi.val ≤ base.val)
    (hAw : base.val + len.val * 2 ^ (zA nt.val us).val ≤ p.val + 2 ^ sb.val)
    (hH' : ∀ q k, H' q = some k → H q = some k ∨
      (nt.val ≠ 0 ∧ base.val ≤ q.val ∧ q.val + 2 ^ k.bits ≤ base.val + len.val * 2 ^ (zA nt.val us).val))
    (h0 : 0#u64 ∈ Cs) (hN0 : NodePlaced st H.tcbs s 0#u64)
    (hnC : ¬ W7.CapW H.tcbs H.omega Sg (nwA st s))
    (hhd0 : L.mem s (nwA st s) = 0#u64 ∨ H (L.mem s (nwA st s)) = some .tcb)
    (hdO : ∀ j, j < len.val → djA dcn off j ∈ OS)
    (hdn : ∀ j, j < len.val → capA st s (djA dcn off j) = .Null)
    (hdc : ∀ j, j < len.val → obj.sext48 (djA dcn off j) = ok (djA dcn off j))
    (hinj : ∀ j l, j < len.val → l < len.val → djA dcn off j = djA dcn off l → j = l)
    (hcan : ∀ j, j < len.val → CapRt.Canonical (bjA base (zA nt.val us) j)) (hus : us.val < 64)
    (hcd : ∀ j, j < len.val → ∃ z ∈ OS, CovBy (capA st s z) (djA dcn off j)) :
    untyped.retype st ar s a src false base nt us dcn off len device ⦃ r => r.1 = .Ok () ∧
      StZ st H' Cs OS r.2.1 ⦄ := by
  obtain ⟨hSA, hZ, hK⟩ := hSt
  have hnA := nodeAt_aligned hN0 (by rw [debug_val]; omega) (by rw [debug_val])
  have hnF := KsOffA.node hK h0 hN0 (by rw [debug_val]; omega)
  obtain ⟨hS, -, hV, hUZ, -⟩ := id hSA
  obtain ⟨G, par, hM, -, -, hN, -, hTr, hU⟩ := id hS
  have hT : TreeA st OS G par s := ⟨hM, hTr, hU⟩
  have hF := hT.ut.freeFresh
  obtain ⟨-, -, hpfit⟩ := ut_rangeA (capA_ut_b hcs) (by
    have := hT.ut.reg src hsrc (by rw [hcs]; exact physA_ut _ _ _ _); rwa [hcs] at this)
  have hz0 : nt.val = 0 → zA nt.val us = us := fun e => by simp [zA, e]
  refine WP.spec_mono (spec_andA
    (untyped.retype.stA hA hH hO hSA a hsrc hcs nt us dcn off len base device hdv hn hz hdev hal hfi hA0 hAw hH'
      hnA hnC hnF hhd0 hdO hdn hdc hinj hcan hus hcd) ?_) fun r ⟨⟨hok, h1⟩, h2⟩ => ⟨hok, h1, h2⟩
  cases dev
  · exact WP.spec_mono (untyped.retype.lvR hA hH hO hT hN hV hUZ a hsrc hcs nt us dcn off len base device hdv hn hz
      hal hfi hA0 hAw hnA hnC hnF hhd0 hdO hdn hdc hinj hcan hus) fun r ⟨_, hLV, hW⟩ =>
      LoopV.zfK hZ hK hF hsrc hcs hdv hA0 hAw (by omega) hz0 hLV hW.1
  · exact WP.spec_mono (untyped.retype.lvD hH hO hT hN hV hUZ a hsrc hcs nt us dcn off len base device hdv hn hz
      (hdev rfl) hfi hA0 hAw hnF hdO hdn hdc hinj hcan hus) fun r ⟨_, hLV, hW⟩ =>
      LoopV.zfK hZ hK hF hsrc hcs hdv hA0 hAw (by omega) hz0 hLV hW.1

/-- **Retype carrying `StZ`, the destination from `retype_dest`** (MdbCovU's `stAD` form). -/
theorem untyped.retype.stZD (hA : P0.ArchTotal ar) (hH : HeapOK H)
    (hO : OSOK H.tcbs H.omega Sg OS) {s : S} {H' : Heap} {Cs : Set U64} (hSt : StZ st H Cs OS s) (a : A)
    {src p sb fi : U64} {dev : Bool} (hsrc : src ∈ OS) (hcs : capA st s src = .Untyped p sb fi dev)
    (nt us dcn off len base : U64) (device : Bool) (hdv : device = dev) (hn : nt.val < 15)
    (hz : (zA nt.val us).val < 64) (hdev : dev = true → nt.val ≠ 1 ∧ nt.val ≠ 12 ∧ nt.val ≠ 14)
    (hal : base.val % 8 = 0)
    (hfi : fi.val < 2 ^ sb.val) (hA0 : p.val + fi.val ≤ base.val)
    (hAw : base.val + len.val * 2 ^ (zA nt.val us).val ≤ p.val + 2 ^ sb.val)
    (hH' : ∀ q k, H' q = some k → H q = some k ∨
      (nt.val ≠ 0 ∧ base.val ≤ q.val ∧ q.val + 2 ^ k.bits ≤ base.val + len.val * 2 ^ (zA nt.val us).val))
    (h0 : 0#u64 ∈ Cs) (hN0 : NodePlaced st H.tcbs s 0#u64)
    (hnC : ¬ W7.CapW H.tcbs H.omega Sg (nwA st s))
    (hhd0 : L.mem s (nwA st s) = 0#u64 ∨ H (L.mem s (nwA st s)) = some .tcb)
    (hdn : ∀ j, j < len.val → capA st s (djA dcn off j) = .Null)
    (hdc : ∀ j, j < len.val → obj.sext48 (djA dcn off j) = ok (djA dcn off j))
    (hinj : ∀ j l, j < len.val → l < len.val → djA dcn off j = djA dcn off l → j = l)
    (hcan : ∀ j, j < len.val → CapRt.Canonical (bjA base (zA nt.val us) j)) (hus : us.val < 64)
    (hT : SlotTy st H.tcbs H.omega Sg H Rp Nt OS s) {x idx dep : U64} (hx : x ∈ OS)
    (hd : untyped.retype_dest st s x idx dep off len = ok (.Ok dcn)) :
    untyped.retype st ar s a src false base nt us dcn off len device ⦃ r => r.1 = .Ok () ∧
      StZ st H' Cs OS r.2.1 ⦄ :=
  have hdc' := untyped.retype_dest.cov hO hT hSt.1.1 hx hd
  untyped.retype.stZ hA hH hO hSt a hsrc hcs nt us dcn off len base device hdv hn hz hdev hal hfi hA0 hAw hH' h0 hN0
    hnC hhd0 (fun j hj => (hdc' j hj).1) hdn hdc hinj hcan hus fun j hj => (hdc' j hj).2

/-- **Retype carrying `StZ`, node 0's words from the scheduler invariant and the debug lists** (gen 62 goal 4:
gen 59's `hnC` from `capw_ne_node` — the nodes lie off every cap-slot word, `SchedQueuesInvX`'s `omega` / `nodes`
placement — and `hhd0` from `DbgTz.dh`; `hN0` from `SchedQueuesInvX.nodes`). -/
theorem untyped.retype.stZQ (hA : P0.ArchTotal ar) (hH : HeapOK H)
    (hO : OSOK H.tcbs H.omega Sg OS) {s : S} {H' : Heap} {Cs : Set U64} (hSt : StZ st H Cs OS s)
    {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64}
    (q : SchedQueuesInvX st H.tcbs Cs H.omega H X s Q Rq) (hDb : DbgTz st H.tcbs Cs s) (h0 : 0#u64 ∈ Cs) (a : A)
    {src p sb fi : U64} {dev : Bool} (hsrc : src ∈ OS) (hcs : capA st s src = .Untyped p sb fi dev)
    (nt us dcn off len base : U64) (device : Bool) (hdv : device = dev) (hn : nt.val < 15)
    (hz : (zA nt.val us).val < 64) (hdev : dev = true → nt.val ≠ 1 ∧ nt.val ≠ 12 ∧ nt.val ≠ 14)
    (hal : base.val % 8 = 0)
    (hfi : fi.val < 2 ^ sb.val) (hA0 : p.val + fi.val ≤ base.val)
    (hAw : base.val + len.val * 2 ^ (zA nt.val us).val ≤ p.val + 2 ^ sb.val)
    (hH' : ∀ q k, H' q = some k → H q = some k ∨
      (nt.val ≠ 0 ∧ base.val ≤ q.val ∧ q.val + 2 ^ k.bits ≤ base.val + len.val * 2 ^ (zA nt.val us).val))
    (hdO : ∀ j, j < len.val → djA dcn off j ∈ OS)
    (hdn : ∀ j, j < len.val → capA st s (djA dcn off j) = .Null)
    (hdc : ∀ j, j < len.val → obj.sext48 (djA dcn off j) = ok (djA dcn off j))
    (hinj : ∀ j l, j < len.val → l < len.val → djA dcn off j = djA dcn off l → j = l)
    (hcan : ∀ j, j < len.val → CapRt.Canonical (bjA base (zA nt.val us) j)) (hus : us.val < 64)
    (hcd : ∀ j, j < len.val → ∃ z ∈ OS, CovBy (capA st s z) (djA dcn off j)) :
    untyped.retype st ar s a src false base nt us dcn off len device ⦃ r => r.1 = .Ok () ∧
      StZ st H' Cs OS r.2.1 ⦄ :=
  untyped.retype.stZ hA hH hO hSt a hsrc hcs nt us dcn off len base device hdv hn hz hdev hal hfi hA0 hAw hH' h0
    (q.nodes _ h0) (fun hb => capw_ne_node q hb h0 (by rw [debug_val]; omega) rfl) (hDb.dh _ h0) hdO hdn hdc hinj
    hcan hus hcd

end arch

end ST
end R
end W7

end

end Fl4ProofsA64.P1
