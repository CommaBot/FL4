/-
P1 (aarch64, gen 51): **`cdt::move_cap` keeps the MDB facts** (cdt.rs `move_cap`: the source's cap — or, for
CNode Mutate, an `AlikeA` one — and links into the empty destination, the source cleared, the neighbours relinked),
for CNode Move / Mutate (cnode.rs:48–73, 77–102).

* **The move's link algebra, abstractly** (`LkAbs`, as gen 48's swap): `mN` / `mP` (the final `NEXT` / `PREV` of
  `move_cap`'s six link writes, the last write first), **`LkAbs.mv_ok`**: under `LkF`, `x1` (the destination) a
  non-member no member links to, `x2` (the source) a member — `mN (tr y) = tr (nx y)` and `mP (tr y) = tr (pv y)`
  for every member `y`, i.e. the members' links renamed by the transposition (gen 47's `renG`); **`mv_src`** (the
  source ends linkless), **`mv_fix`** (other non-members keep their links).
* **`cdt.move_cap.lr`** (function level, over gen 48's `LR`): links at `mP` / `mN`, the new cap at the
  destination, `Null` at the source, other caps kept.
* **`MdbS.alike`**: `MdbS` carries to a state with the same `OS` links and pointwise `AlikeA` caps of the same
  null-ness (each of the five facts reads caps only through `RngKeyA` / `clsA` / `kindA` / null-ness).
* **`cdt.move_cap.mdbS`**: `move_cap` of a non-null new cap `AlikeA` the source's cap, encodable, from a non-null
  `OS` source into a null canonical `OS` destination keeps `MdbS` — the renaming lemmas (`MdbLk.ren`,
  `RngOneA64.ren`, `KindA.ren`, `ClsA.ren`) at the state with the source's own cap words written back into the
  destination (a two-word write, links unchanged), then `MdbS.alike` to the real one.
* **`cnode.copied_cap.mv`**: for Move / Mutate, every `Ok (nc, b)` of `copied_cap` has `b = true`, `AlN nc src_cap`
  and `EncWf nc` (Move returns the source cap, Mutate `update_cap_data true`).

No named premise; new definitions and theorems only.
-/
import Fl4ProofsA64.P1.MdbCopy
import Fl4ProofsA64.P1.MdbLoop
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1

namespace LkAbs
variable {α : Type} [DecidableEq α]

/-- `NEXT` at the end of `move_cap x2 → x1`: `P2.NEXT := x1` (last), `x2` cleared, `x1.NEXT := nx x2`. -/
def mN (o : α) (pv nx : α → α) (x1 x2 : α) (z : α) : α :=
  if pv x2 ≠ o ∧ z = pv x2 then x1 else if z = x2 then o else if z = x1 then nx x2 else nx z

/-- `PREV` at the end of `move_cap x2 → x1`: `N2.PREV := x1` (last), `x2` cleared, `x1.PREV := pv x2`. -/
def mP (o : α) (pv nx : α → α) (x1 x2 : α) (z : α) : α :=
  if nx x2 ≠ o ∧ z = nx x2 then x1 else if z = x2 then o else if z = x1 then pv x2 else pv z

/-- **The move renames the members' links** (module docstring). -/
theorem mv_ok {o : α} {M : α → Prop} {pv nx : α → α} (h : LkF o M pv nx) {x1 x2 : α} (n1 : ¬ M x1)
    (r1 : ∀ y, M y → nx y ≠ x1 ∧ pv y ≠ x1) (m2 : M x2) {y : α} (my : M y) :
    mN o pv nx x1 x2 (tr x1 x2 y) = tr x1 x2 (nx y) ∧ mP o pv nx x1 x2 (tr x1 x2 y) = tr x1 x2 (pv y) := by
  have z := h.z; have nxm := h.nxm; have pvm := h.pvm; have nxpv := h.nxpv; have pvnx := h.pvnx
  have nxne := h.nxne; have pvne := h.pvne
  constructor
  · unfold mN tr
    grind
  · unfold mP tr
    grind

/-- The source ends linkless. -/
theorem mv_src {o : α} {M : α → Prop} {pv nx : α → α} (h : LkF o M pv nx) {x1 x2 : α} (m2 : M x2) :
    mN o pv nx x1 x2 x2 = o ∧ mP o pv nx x1 x2 x2 = o := by
  have nxne := h.nxne; have pvne := h.pvne
  constructor
  · unfold mN
    grind
  · unfold mP
    grind

/-- A non-member other than the two slots keeps its links. -/
theorem mv_fix {o : α} {M : α → Prop} {pv nx : α → α} (h : LkF o M pv nx) {x1 x2 : α} (m2 : M x2)
    {w : α} (nw : ¬ M w) (w1 : w ≠ x1) (w2 : w ≠ x2) :
    mN o pv nx x1 x2 w = nx w ∧ mP o pv nx x1 x2 w = pv w := by
  have nxm := h.nxm; have pvm := h.pvm
  constructor
  · unfold mN
    grind
  · unfold mP
    grind

end LkAbs

open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {Sg : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

variable {OS : Set U64}

set_option maxHeartbeats 4000000 in
/-- (gen 60) **`move_cap`'s links and caps, and its write frame** (`move_cap.lr`'s proof with the written words
tracked: every word written is a cap-slot word of `OS`, `W7.CapW`). -/
theorem cdt.move_cap.lrF (hO : OSOK T Ω Sg OS) {s : S} {pv nx : U64 → U64} (hL : LR st OS s pv nx)
    {src dest : U64} {nc : capability.Cap} (hsrc : src ∈ OS) (hd : dest ∈ OS) (hsd : src ≠ dest)
    (hdc : obj.sext48 dest = ok dest) (hw : CapRt.EncWf nc)
    (hpP : pv src ≠ 0#u64 → pv src ∈ OS) (hnN : nx src ≠ 0#u64 → nx src ∈ OS) :
    cdt.move_cap st s nc src dest ⦃ s' => WritesIn st s s' (W7.CapW T Ω Sg) ∧
      LR st OS s' (LkAbs.mP 0#u64 pv nx dest src) (LkAbs.mN 0#u64 pv nx dest src) ∧
      capA st s' dest = nc ∧ capA st s' src = .Null ∧ ∀ y ∈ OS, y ≠ src → y ≠ dest → capA st s' y = capA st s y ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have cnN : obj.sext48 (nx src) = ok (nx src) := by rw [← (hL src hsrc).2]; exact nxA_can s src
  unfold cdt.move_cap
  rw [slot_prev_eq s src, bind_ok, (hL src hsrc).1, next_eq, bind_ok, (hL src hsrc).2]
  refine WP.spec_bind (P0.obj.Slot.revocable.p0 st src s hS) fun r1 _ => ?_
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st src s hS) fun f1 _ => ?_
  obtain ⟨w0, w1, he, hr⟩ := CapRt.decode_encode nc hw
  rw [set_cap_eq he, bind_ok]
  have L1 := hL.wr2 hO hd (w0 := w0) (w1 := w1)
  have C1 : capA st (L.wr (L.wr s dest w0) (wa dest 8#u64) w1) dest = nc ∧
      ∀ y ∈ OS, y ≠ dest → capA st (L.wr (L.wr s dest w0) (wa dest 8#u64) w1) y = capA st s y :=
    ⟨capA_wr2_self hO hd hr, fun y hy n => capA_wr2_other hO hd hy n⟩
  have W1 : WritesIn st s (L.wr (L.wr s dest w0) (wa dest 8#u64) w1) (W7.CapW T Ω Sg) :=
    WritesIn.cw2 hO (WritesIn.refl (st := st) s (W7.CapW T Ω Sg)) hd w0 w1
  generalize L.wr (L.wr s dest w0) (wa dest 8#u64) w1 = s1 at L1 C1 W1 ⊢
  rw [set_prev_eq, bind_ok]
  have L2 := L1.prev hO hd (pv src)
  refine WP.spec_bind (set_nf_spec _ dest _ r1 f1) ?_
  rintro s3 ⟨w3, rfl, hw3⟩
  have L3 := L2.nw hO hd hw3 cnN
  have C3 := ((CK.refl (st := st) (OS := OS) s1).p hO hd (pv src)).n hO hd w3
  have W3 := WritesIn.cwn hO (WritesIn.cwp hO W1 hd (pv src)) hd w3
  generalize L.wr (L.wr s1 (wa dest 16#u64) (pv src)) (wa dest 24#u64) w3 = s3 at L3 C3 W3 ⊢
  -- clear the source
  rw [clear_eq, bind_ok]
  have L4a := L3.wr2 hO hsrc (w0 := 0#u64) (w1 := 0#u64)
  have C4a : capA st (L.wr (L.wr s3 src 0#u64) (wa src 8#u64) 0#u64) src = .Null ∧
      ∀ y ∈ OS, y ≠ src → capA st (L.wr (L.wr s3 src 0#u64) (wa src 8#u64) 0#u64) y = capA st s3 y :=
    ⟨capA_wr2_self hO hsrc (decode_zero _), fun y hy n => capA_wr2_other hO hsrc hy n⟩
  have W4a := WritesIn.cw2 hO W3 hsrc 0#u64 0#u64
  generalize L.wr (L.wr s3 src 0#u64) (wa src 8#u64) 0#u64 = s4a at L4a C4a W4a ⊢
  have L4 := (L4a.prev hO hsrc 0#u64).nw hO hsrc (n := 0#u64) (w := 0#u64) rfl sx0
  have C4 := ((CK.refl (st := st) (OS := OS) s4a).p hO hsrc 0#u64).n hO hsrc 0#u64
  have W4 := WritesIn.cwn hO (WritesIn.cwp hO W4a hsrc 0#u64) hsrc 0#u64
  generalize L.wr (L.wr s4a (wa src 16#u64) 0#u64) (wa src 24#u64) 0#u64 = s4 at L4 C4 W4 ⊢
  simp only [obj.Slot.is_null, bind_ok]
  have fin : ∀ s' : S, CK st OS s4 s' →
      capA st s' dest = nc ∧ capA st s' src = .Null ∧ ∀ y ∈ OS, y ≠ src → y ≠ dest → capA st s' y = capA st s y :=
    fun s' hc => ⟨by rw [hc dest hd, C4 dest hd, C4a.2 dest hd hsd.symm, C3 dest hd]; exact C1.1,
      by rw [hc src hsrc, C4 src hsrc]; exact C4a.1,
      fun y hy n1 n2 => by rw [hc y hy, C4 y hy, C4a.2 y hy n1, C3 y hy]; exact C1.2 y hy n2⟩
  -- stage 5: `P2.NEXT := dest`
  refine WP.spec_bind (Pₘ := fun s5 => LR st OS s5
      (fun z => if z = src then 0#u64 else if z = dest then pv src else pv z)
      (LkAbs.mN 0#u64 pv nx dest src) ∧ CK st OS s4 s5 ∧ WritesIn st s s5 (W7.CapW T Ω Sg)) ?_
    fun s5 h5 => ?_
  · split
    · rename_i hp0
      have hP0 : pv src = 0#u64 := by simpa using hp0
      refine (WP.spec_ok _).2 ⟨L4.congr (fun _ _ => rfl) fun z _ => ?_, CK.refl s4, W4⟩
      unfold LkAbs.mN; simp [hP0]
    · rename_i hp0
      have hP0 : pv src ≠ 0#u64 := by simpa using hp0
      rw [set_next_eq, WP.spec_ok]
      refine ⟨(L4.nw hO (hpP hP0) (link_bits _ _) hdc).congr (fun _ _ => rfl) fun z _ => ?_,
        (CK.refl s4).n hO (hpP hP0) _, WritesIn.cwn hO W4 (hpP hP0) _⟩
      unfold LkAbs.mN; by_cases e : z = pv src <;> simp [e, hP0]
  obtain ⟨L5, C5, W5⟩ := h5
  -- stage 6: `N2.PREV := dest`
  split
  · rename_i hn0
    have hN0 : nx src = 0#u64 := by simpa using hn0
    refine (WP.spec_ok _).2 ⟨W5, L5.congr (fun z _ => ?_) (fun _ _ => rfl), fin _ C5⟩
    unfold LkAbs.mP; simp [hN0]
  · rename_i hn0
    have hN0 : nx src ≠ 0#u64 := by simpa using hn0
    rw [set_prev_eq, WP.spec_ok]
    refine ⟨WritesIn.cwp hO W5 (hnN hN0) dest,
      (L5.prev hO (hnN hN0) dest).congr (fun z _ => ?_) (fun _ _ => rfl),
      fin _ (C5.p hO (hnN hN0) dest)⟩
    unfold LkAbs.mP; by_cases e : z = nx src <;> simp [e, hN0]

/-- **`move_cap`'s links and caps** (module docstring). -/
theorem cdt.move_cap.lr (hO : OSOK T Ω Sg OS) {s : S} {pv nx : U64 → U64} (hL : LR st OS s pv nx)
    {src dest : U64} {nc : capability.Cap} (hsrc : src ∈ OS) (hd : dest ∈ OS) (hsd : src ≠ dest)
    (hdc : obj.sext48 dest = ok dest) (hw : CapRt.EncWf nc)
    (hpP : pv src ≠ 0#u64 → pv src ∈ OS) (hnN : nx src ≠ 0#u64 → nx src ∈ OS) :
    cdt.move_cap st s nc src dest ⦃ s' => LR st OS s' (LkAbs.mP 0#u64 pv nx dest src) (LkAbs.mN 0#u64 pv nx dest src) ∧
      capA st s' dest = nc ∧ capA st s' src = .Null ∧ ∀ y ∈ OS, y ≠ src → y ≠ dest → capA st s' y = capA st s y ⦄ :=
  WP.spec_mono (cdt.move_cap.lrF hO hL hsrc hd hsd hdc hw hpP hnN) fun _ h => h.2

/-- **`MdbS` along pointwise `AlikeA` caps** of the same null-ness, links unchanged (module docstring). -/
theorem MdbS.alike {s s' : S} (h : MdbS st OS s)
    (hl : ∀ x ∈ OS, L.mem s' (wa x 16#u64) = L.mem s (wa x 16#u64) ∧ L.mem s' (wa x 24#u64) = L.mem s (wa x 24#u64))
    (hn : ∀ x ∈ OS, (capA st s' x = .Null ↔ capA st s x = .Null))
    (ha : ∀ x ∈ OS, AlikeA (capA st s' x) (capA st s x)) : MdbS st OS s' := by
  obtain ⟨G, hM, hRO, hK, hN, hC⟩ := h
  have inOS : ∀ y ∈ G.flatten, y ∈ OS := fun y hy => ((hM.members y).1 hy).1
  have nx : ∀ y ∈ OS, NxA st s' y = NxA st s y := fun y hy => by unfold NxA; rw [(hl y hy).2]
  refine ⟨G, hM.keep hl hn, hRO.keep fun y hy => ?_, hK.keep fun y hy => ?_, hN.keep fun y hy hy0 => ?_,
    hC.of fun y hy k => ?_⟩
  · exact ⟨(ha y (inOS y hy)).1, fun k => ((ha y (inOS y hy)).2 k).1⟩
  · exact ⟨(ha y hy).1, fun k => ⟨ptrA_of_cls ((ha y hy).2 k).1, ((ha y hy).2 k).2⟩⟩
  · exact ⟨(hn y hy).1 hy0, (hl y hy).1, nx y hy⟩
  · exact ⟨y, hy, (ha y hy).1.1 k, ((ha y hy).2 ((ha y hy).1.1 k)).1⟩

set_option maxHeartbeats 2000000 in
/-- **`move_cap` keeps `MdbS`** (module docstring). -/
theorem cdt.move_cap.mdbS (hO : OSOK T Ω Sg OS) {s : S} (hm : MdbS st OS s) {src dest : U64}
    {nc : capability.Cap} (hsrc : src ∈ OS) (hs0 : capA st s src ≠ .Null) (hd : dest ∈ OS)
    (hd0 : capA st s dest = .Null) (hdc : obj.sext48 dest = ok dest) (hw : CapRt.EncWf nc) (hn : nc ≠ .Null)
    (hal : AlikeA nc (capA st s src)) :
    cdt.move_cap st s nc src dest ⦃ s' => MdbS st OS s' ⦄ := by
  obtain ⟨G, hM, hRO, hK, hN, hC⟩ := hm
  have h0 : ∀ y ∈ OS, y ≠ 0#u64 := hO.nz
  have inOS : ∀ y ∈ G.flatten, y ∈ OS := fun y hy => ((hM.members y).1 hy).1
  have F := hM.lkF h0
  have hsG : src ∈ G.flatten := (hM.members src).2 ⟨hsrc, hs0⟩
  have hdG : dest ∉ G.flatten := fun m => ((hM.members dest).1 m).2 hd0
  have hsd : src ≠ dest := fun e => hs0 (e ▸ hd0)
  have r1 : ∀ y, y ∈ G.flatten → NxA st s y ≠ dest ∧ L.mem s (wa y 16#u64) ≠ dest :=
    fun y hy => ⟨fun e => hdG (by rw [← e]; exact F.nxm y hy (by rw [e]; exact h0 dest hd)),
      fun e => hdG (by rw [← e]; exact F.pvm y hy (by rw [e]; exact h0 dest hd))⟩
  refine WP.spec_mono (cdt.move_cap.lr hO (LR.self s) hsrc hd hsd hdc hw (fun h => inOS _ (F.pvm _ hsG h))
    (fun h => inOS _ (F.nxm _ hsG h))) ?_
  rintro s' ⟨hL, e1, e2, ek⟩
  have hdsrc : capability.Cap.decode (L.mem s src) (L.mem s (wa src 8#u64)) = ok (capA st s src) := by
    have e := capA_eq (st := st) s src; rw [DPF.slot_cap_dec] at e; exact e
  have hl'' := set_cap_links (st := st) (s := s') (w0 := L.mem s src) (w1 := L.mem s (wa src 8#u64)) hO hd
  have c''d : capA st (L.wr (L.wr s' dest (L.mem s src)) (wa dest 8#u64) (L.mem s (wa src 8#u64))) dest =
      capA st s src := capA_wr2_self hO hd hdsrc
  have c''o : ∀ y ∈ OS, y ≠ dest →
      capA st (L.wr (L.wr s' dest (L.mem s src)) (wa dest 8#u64) (L.mem s (wa src 8#u64))) y = capA st s' y :=
    fun y hy n => capA_wr2_other hO hd hy n
  have L'' := hL.wr2 hO hd (w0 := L.mem s src) (w1 := L.mem s (wa src 8#u64))
  generalize L.wr (L.wr s' dest (L.mem s src)) (wa dest 8#u64) (L.mem s (wa src 8#u64)) = s'' at hl'' c''d c''o L''
  have hc : ∀ y ∈ OS, capA st s'' (swp dest src y) = capA st s y := by
    intro y hy
    unfold swp
    by_cases a1 : y = dest
    · rw [a1, if_pos rfl, c''o src hsrc hsd, e2, hd0]
    · rw [if_neg a1]
      by_cases a2 : y = src
      · rw [a2, if_pos rfl, c''d]
      · rw [if_neg a2, c''o y hy a1]; exact ek y hy a2 a1
  have sw : ∀ y ∈ G.flatten, swp dest src y ∈ OS := fun y hy => swp_os hd hsrc (inOS y hy)
  have key : ∀ y ∈ G.flatten,
      LkAbs.mN 0#u64 (fun z => L.mem s (wa z 16#u64)) (NxA st s) dest src (LkAbs.tr dest src y) =
        LkAbs.tr dest src (NxA st s y) ∧
      LkAbs.mP 0#u64 (fun z => L.mem s (wa z 16#u64)) (NxA st s) dest src (LkAbs.tr dest src y) =
        LkAbs.tr dest src (L.mem s (wa y 16#u64)) :=
    fun y hy => LkAbs.mv_ok F hdG r1 hsG hy
  have hS'' : MdbS st OS s'' := by
    refine ⟨renG dest src G, hM.ren h0 hd hsrc hc (fun y hy => ?_) (fun y hy => ?_),
      hRO.ren fun y hy => hc y (inOS y hy), hK.ren hd hsrc hc, fun z hz hz0 => ?_, hC.ren hd hsrc hc⟩
    · rw [(L'' _ (sw y hy)).2, swp_tr, swp_tr]; exact (key y hy).1
    · rw [(L'' _ (sw y hy)).1, swp_tr, swp_tr]; exact (key y hy).2
    · rw [(L'' z hz).1, (L'' z hz).2]
      by_cases a1 : z = dest
      · subst a1; rw [c''d] at hz0; exact absurd hz0 hs0
      by_cases a2 : z = src
      · subst a2
        obtain ⟨a, b⟩ := LkAbs.mv_src F (x1 := dest) hsG
        exact ⟨b, a⟩
      rw [c''o z hz a1, ek z hz a2 a1] at hz0
      have nz : z ∉ G.flatten := fun m => ((hM.members z).1 m).2 hz0
      have fx := LkAbs.mv_fix F hsG nz a1 a2
      rw [fx.1, fx.2]
      exact hN z hz hz0
  refine MdbS.alike hS'' (fun x hx => ⟨(hl'' x hx).1.symm, (hl'' x hx).2.symm⟩) (fun x hx => ?_) (fun x hx => ?_)
  · by_cases a1 : x = dest
    · subst a1; rw [e1, c''d]; exact ⟨fun h => absurd h hn, fun h => absurd h hs0⟩
    · rw [c''o x hx a1]
  · by_cases a1 : x = dest
    · subst a1; rw [e1, c''d]; exact hal
    · rw [c''o x hx a1]; exact AlikeA.refl _

theorem alN_refl (c : capability.Cap) : AlN c c := by
  by_cases h : c = .Null
  · exact Or.inl h
  · exact Or.inr ⟨AlikeA.refl c, h⟩

/-- **CNode Move / Mutate's new cap** (module docstring). -/
theorem cnode.copied_cap.mv (s : S) (lbl length buf src : U64) (src_cap : capability.Cap)
    (hl : lbl = fl4_abi.label.CNodeMove ∨ lbl = fl4_abi.label.CNodeMutate) (hc : CapRt.EncWf src_cap) :
    cnode.copied_cap st s lbl length buf src src_cap ⦃ r => ∀ nc b, r = .Ok (nc, b) →
      b = true ∧ AlN nc src_cap ∧ CapRt.EncWf nc ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have h1 : ¬ lbl = fl4_abi.label.CNodeCopy := by
    rcases hl with rfl | rfl <;> (first | decide | (simp only [fl4_abi.label.CNodeCopy, fl4_abi.label.CNodeMint, fl4_abi.label.CNodeMove, fl4_abi.label.CNodeMutate]; decide) | simp [fl4_abi.label.CNodeCopy, fl4_abi.label.CNodeMint, fl4_abi.label.CNodeMove, fl4_abi.label.CNodeMutate])
  have h2 : ¬ lbl = fl4_abi.label.CNodeMint := by
    rcases hl with rfl | rfl <;> (first | decide | (simp only [fl4_abi.label.CNodeCopy, fl4_abi.label.CNodeMint, fl4_abi.label.CNodeMove, fl4_abi.label.CNodeMutate]; decide) | simp [fl4_abi.label.CNodeCopy, fl4_abi.label.CNodeMint, fl4_abi.label.CNodeMove, fl4_abi.label.CNodeMutate])
  unfold cnode.copied_cap
  refine WP.spec_bind (P0.sched.cur_thread.p0 st s hS) fun ct _ => ?_
  rw [if_neg h1, if_neg h2]
  split
  · rw [WP.spec_ok]; intro nc b h; cases h; exact ⟨rfl, alN_refl _, hc⟩
  · split
    · simp only [error.truncated, WP.spec_ok]; intro nc b h; cases h
    · refine WP.spec_bind (P0.msg.syscall_arg.p0 st s ct buf _ hS) fun data _ => ?_
      refine WP.spec_bind (WP.spec_and (objects.update_cap_data.al true data src_cap)
        (objects.update_cap_data.wf true data src_cap hc)) fun c ⟨ha, hw⟩ => ?_
      rw [WP.spec_ok]; intro nc b h; cases h; exact ⟨rfl, ha, hw⟩

end ST
end R
end W7

end

end Fl4ProofsA64.P1
