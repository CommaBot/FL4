/-
P3x for virtualization (line virt, gen 23, item 1, first part): **`VCapped` as an invariant — its preservation
obligations, and the steps that create or move caps.**

`VCapped V mem G` (P3/VirtResetV: every VCPU of `V` has a `Vcpu` cap in a slot of the MDB) is what makes the region of
a childless untyped VCPU-free (`vcpu_out_of_reset`). Its preservation obligations, by what a step does to the caps and
to `V` (= the VCPU list's members, `VList`):

1. **No old `Vcpu` cap lost unless its VCPU leaves `V`**: for every slot whose cap was `Vcpu v` with `v` still in `V'`,
   some slot after holds `Vcpu v` (`VCappedM.of_caps`, the generic form);
2. **every new member of `V` gets a cap**: only the VT-x retype grows `V` (`vcpu::init`, vcpu.rs l. 644-650), and it
   inserts the cap in the same step.

`V` shrinks only by `vcpu::finalise` (vcpu.rs l. 737-753, the only writer of a VCPU's `PREV`/`NEXT` words besides
`init`), which `finalise_cap` runs exactly when the deleted cap is final (objects.rs l. 265); P3/VirtVCappedDel proves
the deletion half. Steps that rewrite a slot's cap in place (cdt.rs l. 21 `set_untyped_cap_as_full`, untyped.rs l. 123 /
241 / 247 / 286, ept.rs l. 174 / 273 / 301, vcpu.rs l. 1046 (an `IoPort` cap), vspace.rs l. 506 / 597 / 787 / 850 /
1082 / 1124 / 1210 / 1247) all overwrite a cap of another kind (untyped, EPT, frame, page-table, PML4, IO port), never a
`Vcpu` cap: `VCappedM.of_update` covers them.

Here:

* `VCappedM V th mem` (the ghost-free form over the typed heap's slots) and `VCapped.toM` / `VCappedM.toG` (equivalent
  under `MdbLinks`: the MDB's slots are exactly the slots with a non-null cap, `MdbLinks.members`).
* Generic: **`VCappedM.of_caps`**, **`VCappedM.of_update`** (one slot rewritten, its old cap not a `Vcpu` cap).
* Retype: **`VCapped.of_retExp`** — `RetExp` with the VCPU caps `vcj A` (P3/UntypedExp; also what a reset followed by
  a retype gives, `RetExp.of_reset`, and a reset alone, `RetExp.reset_only` with no new object) gives
  `VCapped (VsI V A w)`; **`retype_vcpu_capped`**: FL4's `untyped.retype` of type 14 (P3/VirtRetFullV's
  `retype_full_vcpu`) keeps `VCapped` with the new VCPUs added.
* Copy / Mint: **`VCappedM.of_insWords`**, **`insert_vcapped`** (`cdt::insert`, cdt.rs l. 28-46, into an empty slot:
  only the source's cap may change, and only when it is untyped).
* Move / Mutate / Rotate: **`update_cap_data_vcpu`** (`update_cap_data` keeps a `Vcpu` cap, objects.rs l. 180),
  **`VCappedM.of_move`**, **`move_cap_vcapped`** (`cdt::move_cap`, cdt.rs l. 49-64: the source's cap goes to the empty
  destination).
* Swap (`cdt::swap`, Rotate onto itself and `cap_swap_for_delete`): **`VCappedM.of_swap`** at the cap level.

No [J]/[P]/[W] premise. New file only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtRetFullV
import Fl4Proofs.P3.VirtResetV
import Fl4Proofs.P3.CnodeRotate
import Fl4Proofs.P3.Insert
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtVCapped
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.VirtRetypeLoop Fl4Proofs.P3.VirtLoopFrame Fl4Proofs.P3.VirtResetV
open Fl4Proofs.P3.VirtRetFullV Fl4Proofs.P3.VirtSanEq Fl4Proofs.P3.VirtInitWalk Classical

noncomputable section

/-- **`VCapped` over the typed heap's slots** (module docstring). -/
def VCappedM (V : Set U64) (th : TypedHeap) (mem : U64 → U64) : Prop :=
  ∀ v ∈ V, ∃ y, IsSlot th y ∧ capV mem y = .Vcpu v

theorem vcpu_ne_null (v : U64) : (capability.Cap.Vcpu v) ≠ .Null := fun h => by cases h

theorem VCapped.toM {V : Set U64} {th : TypedHeap} {mem : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G)
    (h : VCapped V mem G) : VCappedM V th mem := by
  intro v hv
  obtain ⟨y, hy, hc⟩ := h v hv
  exact ⟨y, ((hM.members y).1 hy).1, hc⟩

theorem VCappedM.toG {V : Set U64} {th : TypedHeap} {mem : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G)
    (h : VCappedM V th mem) : VCapped V mem G := by
  intro v hv
  obtain ⟨y, hy, hc⟩ := h v hv
  exact ⟨y, (hM.members y).2 ⟨hy, capV mem y, capAt_capV mem y, by rw [hc]; exact vcpu_ne_null v⟩, hc⟩

theorem vcapped_iff {V : Set U64} {th : TypedHeap} {mem : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G) :
    VCapped V mem G ↔ VCappedM V th mem :=
  ⟨VCapped.toM hM, VCappedM.toG hM⟩

/-- **The generic obligation** (module docstring, 1.). -/
theorem VCappedM.of_caps {V V' : Set U64} {th th' : TypedHeap} {m m' : U64 → U64} (h : VCappedM V th m)
    (hV : V' ⊆ V)
    (hk : ∀ y, IsSlot th y → ∀ v ∈ V', capV m y = .Vcpu v → ∃ y', IsSlot th' y' ∧ capV m' y' = .Vcpu v) :
    VCappedM V' th' m' := fun v hv => by
  obtain ⟨y, hy, hc⟩ := h v (hV hv)
  exact hk y hy v hv hc

/-- **An in-place cap update** of slot `x` whose old cap is no `Vcpu` cap (module docstring). -/
theorem VCappedM.of_update {V : Set U64} {th : TypedHeap} {m m' : U64 → U64} {x : U64} (h : VCappedM V th m)
    (hx : ∀ v, capV m x ≠ .Vcpu v) (hk : ∀ y, IsSlot th y → y ≠ x → capV m' y = capV m y) :
    VCappedM V th m' :=
  VCappedM.of_caps h (fun _ h => h) fun y hy v _ hc => by
    have hyx : y ≠ x := by rintro rfl; exact hx v hc
    exact ⟨y, hy, (hk y hy hyx).trans hc⟩

/-! ## Retype -/

/-- **The VT-x retype's `RetExp` keeps `VCapped`, the new VCPUs added.** -/
theorem VCapped.of_retExp {th th' : TypedHeap} {m m' : U64 → U64} {G G' : MdbGhost} {A k w : Nat}
    {dslot : Nat → U64} {xs : U64} {V : Set U64} (hE : RetExp th th' m m' G G' A k w dslot (vcj A) xs)
    (h : VCapped V m G) : VCapped (VsI V A w) m' G' := by
  rintro u (hu | ⟨j, hj, rfl⟩)
  · obtain ⟨y, hy, hc⟩ := h u hu
    obtain ⟨hy', e⟩ := hE.keep y hy (by rw [hc]; rfl)
    exact ⟨y, hy', e.trans hc⟩
  · exact ⟨dslot j, hE.newm j hj, hE.newc j hj⟩

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **FL4's VT-x retype keeps `VCapped`** (P3/VirtRetFullV's `retype_full_vcpu`, same hypotheses, plus `VCapped V`
at the start): after it every VCPU of `VsI V A n` (the old ones and the new ones) has a cap. -/
theorem retype_vcpu_capped {A' : Type} (arI : machine.Arch A') (ar : A') (hA : P0.ArchTotal arI)
    (hcA : CapAgree arI ar) (hkA : VirtCodeAgree arI ar)
    (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hU : UtInv (L.mem s) G)
    {pp : U64} {rs : Nat} (hpp : th pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    {p sb fi : U64} {dev : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi dev))
    (hpal : p.val % 2 ^ sb.val = 0) (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64) (hfi : fi.val ≤ 2 ^ sb.val)
    (hhigh : 2 ^ 64 - 2 ^ 47 ≤ p.val) (htop : p.val + 2 ^ sb.val < 2 ^ 64)
    (nt us : U64) (hnt : nt.val = 14)
    {dest : U64} {r : Nat} (hdest : th dest = some (.cnode r)) (hr : r < 64)
    (off win : U64) (hwin : off.val + win.val ≤ 2 ^ r) (hw1 : 1 ≤ win.val)
    (hmem : win.val ≤ ((1#64 <<< sb.val : BitVec 64) - fi.bv).toNat >>> zOf nt.val us.val)
    (hempty : ∀ i : Nat, off.val ≤ i → i < off.val + win.val →
      capAt (L.mem s) (slotAddr dest.bv (BitVec.ofNat 64 i)) = ok .Null)
    (hfree : RegionFree th (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hzero : ZeroRegion (L.mem s) (p.val + fi.val) (p.val + 2 ^ sb.val))
    {V X : Set U64} (Vl : VList st V th s) (E : JExtV (L := L) V X th s)
    (hVf : ∀ w ∈ V, w.val % 32768 = 0 ∧ w.val + 32768 ≤ 2 ^ 64)
    (hVV : ∀ w ∈ V, ∀ w' ∈ V, w ≠ w' → w.val + 32768 ≤ w'.val ∨ w'.val + 32768 ≤ w.val)
    (hVreg : ∀ w ∈ V, w.val + 32768 ≤ p.val + fi.val ∨ p.val + 2 ^ sb.val ≤ w.val)
    (hhdV : ∀ w ∈ V, (P1.vHeadA st s).val < w.val ∨ w.val + 32768 ≤ (P1.vHeadA st s).val)
    (hhdreg : (P1.vHeadA st s).val + 8 ≤ p.val + fi.val ∨ p.val + 2 ^ sb.val ≤ (P1.vHeadA st s).val)
    (hSV : ∀ y, IsSlot th y → ((P1.vHeadA st s).val + 8 ≤ y.val ∨ y.val + 32 ≤ (P1.vHeadA st s).val) ∧
      ∀ w ∈ V, y.val + 32 ≤ w.val ∨ w.val + 32768 ≤ y.val)
    (hTV : ∀ t, th t = some .tcb → P1.TcbAddr t ∧ tVcpuA t ≠ P1.vHeadA st s ∧
      (∀ w ∈ V, t.val + 4096 ≤ w.val ∨ w.val + 32768 ≤ t.val) ∧
      ∀ y, IsSlot th y → ¬ (y.val ≤ (tVcpuA t).val ∧ (tVcpuA t).val < y.val + 32))
    (hVC : VCapped V (L.mem s) G) :
    untyped.retype st arI s ar (cslotAddr (pp.bv, idx)) false
      ⟨Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)⟩ nt us dest off win dev ⦃ res =>
      VCappedM (VsI V (Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)).toNat win.val) th (L.mem res.2.1) ⦄ := by
  refine WP.spec_mono (retype_full_vcpu arI ar hA hcA hkA th s σ G hR hV hP hM hC hI hU hpp hidx hcap hpal hpfit hfi
    hhigh htop nt us hnt hdest hr off win hwin hw1 hmem hempty hfree hzero Vl E hVf hVV hVreg hhdV hhdreg hSV hTV)
    fun res h => ?_
  obtain ⟨-, -, σ', G', -, -, -, hM', -, -, -, -, -, -, -, -, dslot, hE, -, -⟩ := h
  exact VCapped.toM hM' (VCapped.of_retExp hE hVC)

/-! ## Copy, Mint: `cdt::insert` -/

theorem capV_of_words {m m' : U64 → U64} {a : U64} (h0 : m' a = m a) (h8 : m' (wordOf a 8#u64) = m (wordOf a 8#u64)) :
    capV m' a = capV m a := by
  unfold capV; rw [h0, h8]

/-- `cdt::insert`'s words keep every slot's cap but the destination's (and an untyped source's). -/
theorem VCappedM.of_insWords {V : Set U64} {th : TypedHeap} {s s' : S} {c srcC : capability.Cap} {src dest : U64}
    (h : VCappedM V th (L.mem s)) (hW : InsWords (L := L) th s s' c srcC src dest)
    (hsrc : capAt (L.mem s) src = ok srcC) (hdn : capV (L.mem s) dest = .Null) :
    VCappedM V th (L.mem s') :=
  VCappedM.of_caps h (fun _ h => h) fun y hy v _ hc => by
    have hyd : y ≠ dest := by rintro rfl; rw [hdn] at hc; cases hc
    refine ⟨y, hy, ?_⟩
    rw [← hc]
    have e0 := hW y hy 0#u64 off0
    have e8 := hW y hy 8#u64 off8
    rw [wordOf_zero] at e0
    by_cases hys : y = src
    · subst hys
      have hsC : srcC = .Vcpu v := by
        have := capV_of_capAt hsrc; rw [hc] at this; exact this.symm
      have hf : fullF srcC c = none := by rw [hsC]; rfl
      simp [hyd, hf] at e0 e8
      exact capV_of_words e0 e8
    · simp [hyd, hys] at e0 e8
      exact capV_of_words e0 e8

/-- **`cdt::insert` into an empty slot keeps `VCapped`.** -/
theorem insert_vcapped {V : Set U64} {th : TypedHeap} (hP : Placed th) (s : S) (c : capability.Cap) (src dest : U64)
    (hs : IsSlot th src) (hd : IsSlot th dest) (hne : src ≠ dest)
    (srcC : capability.Cap) (hsrcC : capAt (L.mem s) src = ok srcC)
    (hnx : nextOf (L.mem s) src = 0#u64 ∨
      (IsSlot th (nextOf (L.mem s) src) ∧ nextOf (L.mem s) src ≠ dest ∧ nextOf (L.mem s) src ≠ src))
    (hdn : capV (L.mem s) dest = .Null) (h : VCappedM V th (L.mem s)) :
    cdt.insert st s c src dest ⦃ s' => VCappedM V th (L.mem s') ⦄ :=
  WP.spec_mono (insert_mem hP s c src dest hs hd hne srcC hsrcC hnx) fun _ hW => h.of_insWords hW hsrcC hdn

/-! ## Move, Mutate, Rotate: `cdt::move_cap`; swap -/

/-- `update_cap_data` keeps a `Vcpu` cap (objects.rs l. 180, `other => other`). -/
theorem update_cap_data_vcpu (b : Bool) (d v : U64) :
    objects.update_cap_data b d (.Vcpu v) = ok (.Vcpu v) := by
  unfold objects.update_cap_data; rfl

/-- A move of the source's cap (or a cap naming the same VCPU) into an empty destination keeps `VCapped`. -/
theorem VCappedM.of_move {V : Set U64} {th : TypedHeap} {m m' : U64 → U64} {src dest : U64} {c : capability.Cap}
    (h : VCappedM V th m) (hd : IsSlot th dest) (hdn : capV m dest = .Null)
    (hc : ∀ v, capV m src = .Vcpu v → c = .Vcpu v)
    (hW : ∀ a, IsSlot th a → capAt m' a = if a = dest then ok c else if a = src then ok .Null else capAt m a) :
    VCappedM V th m' :=
  VCappedM.of_caps h (fun _ h => h) fun y hy v _ hcv => by
    have hyd : y ≠ dest := by rintro rfl; rw [hdn] at hcv; cases hcv
    by_cases hys : y = src
    · subst hys
      refine ⟨dest, hd, ?_⟩
      have e := hW dest hd
      simp only [↓reduceIte] at e
      rw [← hc v hcv]; exact capV_of_capAt e
    · refine ⟨y, hy, ?_⟩
      have e := hW y hy
      simp only [hyd, hys, ↓reduceIte, capAt_capV] at e
      rw [← hcv]; exact ok_inj e

/-- **`cdt::move_cap` from a linked slot to a free one keeps `VCapped`** (with the moved cap naming the source's VCPU:
Move moves the cap itself, Mutate / Rotate its `update_cap_data`, `update_cap_data_vcpu`). -/
theorem move_cap_vcapped {V : Set U64} {th : TypedHeap} (hP : Placed th) (s : S) (G : MdbGhost)
    (hM : MdbLinks th (L.mem s) G) {src dest : U64} (hsrcm : src ∈ G.chains.flatten) (hd : IsSlot th dest)
    (hdestm : dest ∉ G.chains.flatten) (c : capability.Cap) (he : EncWf c)
    (hc : ∀ v, capV (L.mem s) src = .Vcpu v → c = .Vcpu v) (h : VCappedM V th (L.mem s)) :
    cdt.move_cap st s c src dest ⦃ s' => VCappedM V th (L.mem s') ⦄ := by
  have hdn : capV (L.mem s) dest = .Null := by
    by_contra hn
    exact hdestm ((hM.members dest).2 ⟨hd, capV (L.mem s) dest, capAt_capV _ _, hn⟩)
  exact WP.spec_mono (move_caps hP s G hM hsrcm hd hdestm c he) fun _ hW => h.of_move hd hdn hc hW

/-- A swap of two slots' caps keeps `VCapped`. -/
theorem VCappedM.of_swap {V : Set U64} {th : TypedHeap} {m m' : U64 → U64} {s1 s2 : U64}
    (h : VCappedM V th m) (h1 : IsSlot th s1) (h2 : IsSlot th s2)
    (hW : ∀ a, IsSlot th a → capV m' a = if a = s1 then capV m s2 else if a = s2 then capV m s1 else capV m a) :
    VCappedM V th m' :=
  VCappedM.of_caps h (fun _ h => h) fun y hy v _ hcv => by
    by_cases e1 : y = s1
    · subst e1
      refine ⟨s2, h2, ?_⟩
      rw [hW s2 h2]
      by_cases e : s2 = y
      · subst e; simp [hcv]
      · simp [e, hcv]
    · by_cases e2 : y = s2
      · subst e2
        refine ⟨s1, h1, ?_⟩
        rw [hW s1 h1]; simp [hcv]
      · exact ⟨y, hy, by rw [hW y hy]; simp [e1, e2, hcv]⟩

end

end
end Fl4Proofs.P3.VirtVCapped
