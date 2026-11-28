/-
P3 (p3J gen 44): **bucket 3, `hfin` of `DelHypsWRZ.foot` closed at the deletion loop's invariant**, by carrying the
spec's cap-kind invariant `CKI` (P3JCkW) through the loop.

FL4 `cdt.rs` l.271–316 (`finalise_slot_immediate`'s loop) / l4v `rec_delete`: the loop's spec side is
`finalise_cap`, `preemption_point`, `post_cap_deletion`, a zombie `set_cap`, `cap_swap_for_delete`,
`empty_slot` — every one keeps `CKI` (P3JCkW / P3JCkX: `ck_finaliseCap`, `ck_postCapDeletion`, `ck_setCap` of
a zombie, `ck_capSwapForDelete`, `ck_emptySlot`; SInvV's `hv_preemptionPoint` at `CKI`). So with `WCk W := W ∧
CKI σ` the loop sees only `CKI` states, and there every typed slot holds a `NatFinKind` or IRQ handler cap
(P3JFinAll's `natFinKind_of_kw`): the arch finalisers (frames, IO ports, VSpace, VT-x; FL4 `objects.rs`
l.264–303) are never reached.

* `WCk`, `WPost.map`, `ck_pp`, and the bundle's fields at `WCk`, each field's `CKI` from its spec step:
  `FinObjHypWRcZ.ck` (a finaliser from `WCk` states with its post at `W`, the post given `CKI`), `PPHypDW.ckMap`
  (along maps of the invariants, for both `WCk W` and `WMR MR (WCk W)`), `RdTrivHyp.ck`, `PostDelHypW.ck`,
  `kw_zombie`, `ZombieHypWZ.ck`, `SwapHypWZ.ck`, `EmptyHypWR.ck`; `natFin_notArch`.
* **`finJLZck`**: XTopJointWJLDel's `finJLZ` at `CKI` states: the native kinds only (the `jFinAtL_*` leaves and
  `jFin_nonfinalLO`), so **no `JVtHyps`, no `ArchRefines`, no `JThreadFinHypsU.obj`** (the VCPU word by
  XTopJointKEntry32's `jThrObj_ofExt`, from `JExt.vw`; only `ticks` [P], a global of every top, `hmax` / `htu`).
* **`delHypsJLck`** / **`delHypsJLMck`**: the bundle at `WCk WJL` / `WMR MR (WCk WJL)` (after a preemption
  `WCk WJP` / `WCk WJPM`) from platform facts only (`ARKeep`, `ARMask`, `PPPlat` / `PPPlatA`, `MachPlat`,
  `MRKeepD`, `ticks`).
* **`JAtZ.finSlotProjW`**: `finalise_cap` of a `NatFinKind` slot cap at a `JAtZ` state with `NoSwitch` /
  `SpecGlob` writes only `ProjW` (per kind; the facts P3JFinAll's `fin_cap.kwDN0` asks through `DelCapOK` /
  `FinPl` / the action word, derived: `JPlaced.typed`, `JAtZ.scCapFacts` (the SC not the idle SC by
  `JPlaced.cobj` + `ne_idleSc`), `JAtZ.capNotIdle`, `JAtZ.action_ne_of_noSwitch`, `jThrObj_ofExt`).
* **`hfinWJL`** (`hfin` at `WCk WJL`), `JAtZ.postCapDelWf` (`hpost` from the cleanup cap's `CapWf`), and the footprinted bundles **`delHypsJLft`** / **`delHypsJLMft`**:
  `DelHypsWRZ (WFt s0 (WCk WJL)) …` / `DelHypsWRZ (WFt s0 (WMR MR (WCk WJL))) …` (P3JDelFt's `DelHypsWRZ.foot` with
  `hfin` here, `hpp` / `hsl` / `hpost` by P3JDelFt / P3JFinAll).

* (p3J gen 46) **The generic lift**: `WSp P W := W ∧ P σ`, `SpLoopK P` (the loop's six spec steps keep `P`),
  `SpLoopK.and`, `FinObjHypWRcZ.sp`, `PPHypDW.spMap`, `RdTrivHyp.sp`, `PostDelHypW.sp`, `ZombieHypWZ.sp`,
  `SwapHypWZ.sp`, `EmptyHypWR.sp`, **`DelHypsWRZ.sp`**; `spLoopK_ck`. Gen 44's `CKI` lifts (`FinObjHypWRcZ.ck`,
  `PPHypDW.ckMap`, `RdTrivHyp.ck`, `PostDelHypW.ck`, `ZombieHypWZ.ck`, `SwapHypWZ.ck`, `EmptyHypWR.ck`, `ck_pp`) keep
  their statements and are now the `P := CKI` instances (one proof each). `RR` / `NativeScope`: P3JDelSp.

No premise (only lemma hypotheses that are platform facts of every top); no sorry. New module; no existing
statement changed.
-/
import Fl4Proofs.P3.P3JFinIrqFt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

/-! ## `CKI` through the loop's bundle -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- (p3J gen 44) **An invariant with `CKI`** (module docstring). -/
abbrev WCk (W : S → A → Fl4Spec.State Unit → MdbGhost → Prop) : S → A → Fl4Spec.State Unit → MdbGhost → Prop :=
  fun s a σ G => W s a σ G ∧ SInvCk.CKI σ

/-- (p3J gen 44) `WPost` along maps of both invariants. -/
theorem WPost.map {α : Type} {W Wp W' Wp' : S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    {r : core.result.Result α error.Exc} {s : S} {a : A} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    (h : WPost W Wp r s a σ G) (f : W s a σ G → W' s a σ G) (g : Wp s a σ G → Wp' s a σ G) :
    WPost W' Wp' r s a σ G := by
  cases r with
  | Ok x => exact f h
  | Err e => cases e <;> first | exact f h | exact g h

/-- (p3J gen 46) **An invariant with a spec predicate `P` beside it** (`WCk W = WSp CKI W`). -/
abbrev WSp (P : Fl4Spec.State Unit → Prop) (W : S → A → Fl4Spec.State Unit → MdbGhost → Prop) :
    S → A → Fl4Spec.State Unit → MdbGhost → Prop :=
  fun s a σ G => W s a σ G ∧ P σ

/-- (p3J gen 46) **The deletion loop's spec steps keep `P`** (l4v `rec_delete`'s steps: `finalise_cap`,
`preemption_point`, `post_cap_deletion`, a zombie `set_cap`, `cap_swap_for_delete`, `empty_slot`). -/
structure SpLoopK (P : Fl4Spec.State Unit → Prop) : Prop where
  fin : ∀ c b, SInv.IK P (Fl4Spec.finaliseCap (Z := Unit) c b)
  pp : SInv.IKE P (Fl4Spec.preemptionPoint (Z := Unit))
  post : ∀ c, SInv.IK P (Fl4Spec.postCapDeletion (Z := Unit) c)
  zomb : ∀ p zt n sl, SInv.IK P (Fl4Spec.setCap (Z := Unit) (absCap (.Zombie p zt n)) sl)
  swap : ∀ s1 s2, SInv.IK P (Fl4Spec.capSwapForDelete (Z := Unit) s1 s2)
  empty : ∀ sl c, SInv.IK P (Fl4Spec.emptySlot (Z := Unit) sl c)

/-- (p3J gen 46) Both predicates kept, so their conjunction. -/
theorem SpLoopK.and {P Q : Fl4Spec.State Unit → Prop} (hP : SpLoopK P) (hQ : SpLoopK Q) :
    SpLoopK (fun σ => P σ ∧ Q σ) where
  fin c b σ h x hx := ⟨hP.fin c b σ h.1 x hx, hQ.fin c b σ h.2 x hx⟩
  pp σ h x hx := ⟨hP.pp σ h.1 x hx, hQ.pp σ h.2 x hx⟩
  post c σ h x hx := ⟨hP.post c σ h.1 x hx, hQ.post c σ h.2 x hx⟩
  zomb p zt n sl σ h x hx := ⟨hP.zomb p zt n sl σ h.1 x hx, hQ.zomb p zt n sl σ h.2 x hx⟩
  swap s1 s2 σ h x hx := ⟨hP.swap s1 s2 σ h.1 x hx, hQ.swap s1 s2 σ h.2 x hx⟩
  empty sl c σ h x hx := ⟨hP.empty sl c σ h.1 x hx, hQ.empty sl c σ h.2 x hx⟩

theorem kw_zombie (p zt n : U64) : SInvCk.KW (absCap (.Zombie p zt n)) := by
  simp [absCap, SInvCk.KW]

/-- (p3J gen 46) **The loop's steps keep `CKI`** (gen 44's per-step facts). -/
theorem spLoopK_ck : SpLoopK SInvCk.CKI where
  fin := SInvCk.ck_finaliseCap
  pp := SInvV.hv_preemptionPoint (P := SInvCk.CKI)
  post := SInvCk.ck_postCapDeletion
  zomb p zt n sl := SInvCk.ck_setCap _ sl (kw_zombie p zt n)
  swap := SInvCk.ck_capSwapForDelete
  empty := SInvCk.ck_emptySlot

variable {P : Fl4Spec.State Unit → Prop}

theorem SpLoopK.ppStep (hP : SpLoopK P) {σ σ' : Fl4Spec.State Unit} {x : Except Unit Unit} (h0 : P σ)
    (h : (x, σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1) : P σ' :=
  hP.pp σ h0 (x, σ') h

theorem ck_pp {σ σ' : Fl4Spec.State Unit} {x : Except Unit Unit} (hC : SInvCk.CKI σ)
    (h : (x, σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1) : SInvCk.CKI σ' :=
  spLoopK_ck.ppStep hC h

variable {th : TypedHeap} {Rd Rz : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop}

/-- (p3J gen 46) A finaliser from `WSp P` states with its post at `W` gives one at `WSp P`. -/
theorem FinObjHypWRcZ.sp (hP : SpLoopK P) {W Wx : S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    (h : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (c : capability.Cap),
      DState (L := L) th s σ G → WSp P W s a σ G → AbsSlot th sl → capAt (L.mem s) (cslotAddr sl) = ok c →
      FinObjKind c → True →
      objects.finalise_cap st arI s a c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) false ⦃ r =>
        r.1.1 = finRem c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) ∧ CleanCap r.1.2 ∧ CapWf r.1.2 ∧
        ∃ σ' G', ((absCap r.1.1, absCap r.1.2), σ') ∈
            (Fl4Spec.finaliseCap (Z := Unit) (absCap c) (decide (Fl4Spec.isFinalCap' (absCap c) σ)) σ).1 ∧
          DState (L := L) th r.2.1 σ' G' ∧ capV (L.mem r.2.1) (cslotAddr sl) = c ∧
          (∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem r.2.1) y = capV (L.mem s) y ∨
            (capV (L.mem r.2.1) y = .Null ∧ isZb (capV (L.mem s) y) = false)) ∧
          MdbStep (L.mem s) G (L.mem r.2.1) G' ∧ WF W Wx r.1.1 (cslotAddr sl) r.2.1 r.2.2 σ' G' ∧
          (RmOK r.1.1 (cslotAddr sl) → Rd r.2.1 r.2.2 σ' G' (cslotAddr sl)) ∧
          (∀ p zt n, r.1.1 = .Zombie p zt n → Rz r.2.1 r.2.2 σ' G' (cslotAddr sl)) ⦄) :
    FinObjHypWRcZ (L := L) arI (WSp P W) (WSp P Wx) Rd Rz th := by
  intro s a σ G sl c hDS hW hA hc hk ht
  refine WP.spec_mono (h s a σ G sl c hDS hW hA hc hk ht) ?_
  rintro r ⟨h1, h2, h3, σ', G', h4, h5, h6, h7, h8, ⟨hw1, hw2⟩, h10, h11⟩
  have hC : P σ' := hP.fin _ _ σ hW.2 _ h4
  exact ⟨h1, h2, h3, σ', G', h4, h5, h6, h7, h8, ⟨fun hn => ⟨hw1 hn, hC⟩, fun hr => ⟨hw2 hr, hC⟩⟩, h10, h11⟩

-- (p3J gen 44) A finaliser from `WCk` states with its post at `W` gives one at `WCk` (`ck_finaliseCap`). -/
theorem FinObjHypWRcZ.ck {W Wx : S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    (h : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (c : capability.Cap),
      DState (L := L) th s σ G → WCk W s a σ G → AbsSlot th sl → capAt (L.mem s) (cslotAddr sl) = ok c →
      FinObjKind c → True →
      objects.finalise_cap st arI s a c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) false ⦃ r =>
        r.1.1 = finRem c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) ∧ CleanCap r.1.2 ∧ CapWf r.1.2 ∧
        ∃ σ' G', ((absCap r.1.1, absCap r.1.2), σ') ∈
            (Fl4Spec.finaliseCap (Z := Unit) (absCap c) (decide (Fl4Spec.isFinalCap' (absCap c) σ)) σ).1 ∧
          DState (L := L) th r.2.1 σ' G' ∧ capV (L.mem r.2.1) (cslotAddr sl) = c ∧
          (∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem r.2.1) y = capV (L.mem s) y ∨
            (capV (L.mem r.2.1) y = .Null ∧ isZb (capV (L.mem s) y) = false)) ∧
          MdbStep (L.mem s) G (L.mem r.2.1) G' ∧ WF W Wx r.1.1 (cslotAddr sl) r.2.1 r.2.2 σ' G' ∧
          (RmOK r.1.1 (cslotAddr sl) → Rd r.2.1 r.2.2 σ' G' (cslotAddr sl)) ∧
          (∀ p zt n, r.1.1 = .Zombie p zt n → Rz r.2.1 r.2.2 σ' G' (cslotAddr sl)) ⦄) :
    FinObjHypWRcZ (L := L) arI (WCk W) (WCk Wx) Rd Rz th :=
  FinObjHypWRcZ.sp arI spLoopK_ck h

/-- (p3J gen 46) The preemption point along maps of the invariants, `P` from the spec's preemption point. -/
theorem PPHypDW.spMap (hP : SpLoopK P) {W Wp W' Wp' : S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    (h : PPHypDW (L := L) arI W Wp th)
    (pW : ∀ s a σ G, W' s a σ G → W s a σ G ∧ P σ)
    (iW : ∀ s a σ G, W s a σ G → P σ → W' s a σ G)
    (iWp : ∀ s a σ G, Wp s a σ G → P σ → Wp' s a σ G) :
    PPHypDW (L := L) arI W' Wp' th := by
  intro s a σ G hDS hW
  obtain ⟨hW0, hC⟩ := pW s a σ G hW
  refine WP.spec_mono (h s a σ G hDS hW0) ?_
  rintro r ⟨h1, σ', h2, h3, h4⟩
  have hC' : P σ' := by
    rcases h2 with ⟨-, hm⟩ | ⟨-, hm⟩
    · exact hP.ppStep hC hm
    · exact hP.ppStep hC hm
  exact ⟨h1, σ', h2, h3, WPost.map h4 (fun x => iW _ _ _ _ x hC') (fun x => iWp _ _ _ _ x hC')⟩

/-- (p3J gen 44) The preemption point along maps of the invariants, `CKI` from the spec's preemption point. -/
theorem PPHypDW.ckMap {W Wp W' Wp' : S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    (h : PPHypDW (L := L) arI W Wp th)
    (pW : ∀ s a σ G, W' s a σ G → W s a σ G ∧ SInvCk.CKI σ)
    (iW : ∀ s a σ G, W s a σ G → SInvCk.CKI σ → W' s a σ G)
    (iWp : ∀ s a σ G, Wp s a σ G → SInvCk.CKI σ → Wp' s a σ G) :
    PPHypDW (L := L) arI W' Wp' th :=
  h.spMap arI spLoopK_ck pW iW iWp

/-- (p3J gen 46) `RdTrivHyp` at `WSp P W`. -/
theorem RdTrivHyp.sp {W : S → A → Fl4Spec.State Unit → MdbGhost → Prop} (h : RdTrivHyp (L := L) W Rd th) :
    RdTrivHyp (L := L) (WSp P W) Rd th :=
  fun s a σ G sl c hDS hW => h s a σ G sl c hDS hW.1

theorem RdTrivHyp.ck {W : S → A → Fl4Spec.State Unit → MdbGhost → Prop} (h : RdTrivHyp (L := L) W Rd th) :
    RdTrivHyp (L := L) (WCk W) Rd th :=
  h.sp

/-- (p3J gen 46) `PostDelHypW` at `WSp P W`. -/
theorem PostDelHypW.sp (hP : SpLoopK P) {W : S → A → Fl4Spec.State Unit → MdbGhost → Prop} (h : PostDelHypW (L := L) arI W th) :
    PostDelHypW (L := L) arI (WSp P W) th := by
  intro s a σ G cl hDS hW h1 h2 h3
  refine WP.spec_mono (h s a σ G cl hDS hW.1 h1 h2 h3) ?_
  rintro r ⟨hSS, σ', hm, hCR, hW'⟩
  exact ⟨hSS, σ', hm, hCR, hW', hP.post _ σ hW.2 _ hm⟩

theorem PostDelHypW.ck {W : S → A → Fl4Spec.State Unit → MdbGhost → Prop} (h : PostDelHypW (L := L) arI W th) :
    PostDelHypW (L := L) arI (WCk W) th :=
  h.sp arI spLoopK_ck

/-- (p3J gen 46) `ZombieHypWZ` at `WSp P W`. -/
theorem ZombieHypWZ.sp (hP : SpLoopK P) {W : S → A → Fl4Spec.State Unit → MdbGhost → Prop} (h : ZombieHypWZ (L := L) (A := A) W Rz th) :
    ZombieHypWZ (L := L) (A := A) (WSp P W) Rz th := by
  intro s s' a σ σ' G sl p zt n hW hRz hcd hZF hD1 hD2 hF hsc hA hxn hz hal hoth hmS
  exact ⟨h s s' a σ σ' G sl p zt n hW.1 hRz hcd hZF hD1 hD2 hF hsc hA hxn hz hal hoth hmS,
    hP.zomb p zt n sl σ hW.2 ((), σ') (mem_of_single hsc)⟩

theorem ZombieHypWZ.ck {W : S → A → Fl4Spec.State Unit → MdbGhost → Prop} (h : ZombieHypWZ (L := L) (A := A) W Rz th) :
    ZombieHypWZ (L := L) (A := A) (WCk W) Rz th :=
  h.sp spLoopK_ck

/-- (p3J gen 46) `SwapHypWZ` at `WSp P W`. -/
theorem SwapHypWZ.sp (hP : SpLoopK P) {W : S → A → Fl4Spec.State Unit → MdbGhost → Prop} (h : SwapHypWZ (L := L) (A := A) W th) :
    SwapHypWZ (L := L) (A := A) (WSp P W) th := by
  intro s s' a σ σ' G G' sl p zt n hW hn1 hD1 hD2 hF hsw hA hz hpx hG' hcap hmS
  exact ⟨h s s' a σ σ' G G' sl p zt n hW.1 hn1 hD1 hD2 hF hsw hA hz hpx hG' hcap hmS,
    hP.swap _ _ σ hW.2 ((), σ') (mem_of_single hsw)⟩

theorem SwapHypWZ.ck {W : S → A → Fl4Spec.State Unit → MdbGhost → Prop} (h : SwapHypWZ (L := L) (A := A) W th) :
    SwapHypWZ (L := L) (A := A) (WCk W) th :=
  h.sp spLoopK_ck

/-- (p3J gen 46) `EmptyHypWR` at `WSp P W`. -/
theorem EmptyHypWR.sp (hP : SpLoopK P) {W Wx : S → A → Fl4Spec.State Unit → MdbGhost → Prop} (h : EmptyHypWR (L := L) W Wx Rd th) :
    EmptyHypWR (L := L) (WSp P W) (WSp P Wx) Rd th := by
  intro s s' a σ σ' G G' sl hW hRd hD1 hD2 hF hes hA hxn hx0 hoth hmS
  exact ⟨h s s' a σ σ' G G' sl hW.1 hRd hD1 hD2 hF hes hA hxn hx0 hoth hmS,
    hP.empty _ _ σ hW.2 ((), σ') hes⟩

theorem EmptyHypWR.ck {W Wx : S → A → Fl4Spec.State Unit → MdbGhost → Prop} (h : EmptyHypWR (L := L) W Wx Rd th) :
    EmptyHypWR (L := L) (WCk W) (WCk Wx) Rd th :=
  h.sp spLoopK_ck

/-- (p3J gen 46) **The whole deletion bundle at `WSp P`** (each field by its lift above). -/
theorem DelHypsWRZ.sp (hP : SpLoopK P) {W Wx Wp : S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    (h : DelHypsWRZ (L := L) arI W Wx Wp Rd Rz th) :
    DelHypsWRZ (L := L) arI (WSp P W) (WSp P Wx) (WSp P Wp) Rd Rz th :=
  ⟨FinObjHypWRcZ.sp arI hP (fun s a σ G sl c hDS hW hA hc hk ht => h.fin s a σ G sl c hDS hW.1 hA hc hk ht), h.triv.sp, h.pp.spMap arI hP (fun _ _ _ _ h => h) (fun _ _ _ _ h c => ⟨h, c⟩)
      (fun _ _ _ _ h c => ⟨h, c⟩),
    h.post.sp arI hP, h.zomb.sp hP, h.swap.sp hP, h.empty.sp hP, fun _ _ _ _ x => ⟨h.wx _ _ _ _ x.1, x.2⟩⟩

end

/-! ## The native finalisers at `CKI` states of `WJL` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap}

/-- (p3J gen 44) A `NatFinKind` or IRQ handler cap is no frame / IO port / VSpace / VT-x cap. -/
theorem natFin_notArch {c : capability.Cap} (h : P1.NatFinKind c ∨ ∃ i, c = .IrqHandler i) :
    ¬ FrIoK c ∧ ¬ VsK c ∧ ¬ (EptK c ∨ VcpuK c) ∧ ¬ EptRootK c := by
  rcases h with h | ⟨i, rfl⟩
  · cases c <;> simp_all [P1.NatFinKind, FrIoK, VsK, EptK, VcpuK, EptRootK, isFrame]
  · simp [FrIoK, VsK, EptK, VcpuK, EptRootK, isFrame]

set_option maxHeartbeats 4000000 in
/-- (p3J gen 44) **XTopJointWJLDel's `finJLZ` at `CKI` states** (module docstring): no VT-x / VSpace / frame
hypotheses. -/
theorem finJLZck [Fl4Proofs.P1.PlainStore st] (hT : P0.ArchTotal arI) (hK : ARKeep arI AR)
    (hticks : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      ∀ (a : A) (v : U64), arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (hth : Z.th = th) :
    FinObjHypWRcZ (L := L) arI (WCk (WJL (L := L) arI AR Z H Cs kb)) (WCk (WJLx (L := L) arI AR Z H Cs kb))
      (RdLX (L := L) (A := A) th H Z.vx) (RzJ (L := L) (A := A) H Cs) th := by
  have hF : JThreadFinHypsU (L := L) arI AR th := ⟨jThrObj_ofExt (L := L) arI AR th, hticks⟩
  refine FinObjHypWRcZ.ck arI ?_
  intro s a σ G sl c hDS hW hA hc hk _
  show objects.finalise_cap st arI s a c _ false ⦃ r => FinPostLX (L := L) arI AR Z H Cs kb th s σ G sl c r ⦄
  obtain ⟨hW, hC⟩ := hW
  have hkw : P1.NatFinKind c ∨ ∃ i, c = .IrqHandler i := by
    obtain ⟨V, Ac, Lst, D, J, -⟩ := hW.1
    subst hth
    have := JAtZ.natFinKind_of_cki J hC hA.isSlot
    rw [capV_of_capAt hc] at this
    exact this
  obtain ⟨hfi, hvs, hvt, hrt⟩ := natFin_notArch hkw
  by_cases hfin : Fl4Spec.isFinalCap' (absCap c) σ
  · have hkc := vkey_none_of_not_vsK hvs
    refine WP.spec_mono ?_ fun r h => FinPostL.liftK arI hth h hkc
    by_cases hn : NtfnK c
    · exact jFinAtL_ntfn arI Z H Cs kb hth s a σ G sl c hDS hW hA hc hk hn hfin
    by_cases hq : IrqK c
    · exact jFinAtL_irq arI Z H Cs kb hth s a σ G sl c hDS hW hA hc hk hq hfin
    by_cases he : EpK c
    · exact jFinAtL_ep arI Z H Cs kb hth s a σ G sl c hDS hW hA hc hk he hfin
    by_cases hr : RpK c
    · exact jFinAtL_reply arI hT Z H Cs kb hth s a σ G sl c hDS hW hA hc hk hr hfin
    by_cases hsc : ScK c
    · exact jFinAtL_sc arI hT hF.ticks Z H Cs kb hth s a σ G sl c hDS hW hA hc hk hsc hfin
    by_cases ht : TcbK c
    · exact jFinAtL_thread arI hT hK hF
        (fun _ _ _ s a p hb hp hna hid hv => P1.fin_cap_thread.td0 (ar := arI) hT s a p false hb hp hna hid hv)
        Z H Cs kb hth s a σ G sl c hDS hW hA hc hk ht hfin
    · exact (finObjKind_covered hk hn hfi hq he hr hvs hsc ht hvt hrt).elim
  · exact WP.spec_mono (jFin_nonfinalLO arI Z H Cs kb hth s a σ G sl c hDS hW hA hc hk hfi hfin)
      fun r h => FinPostL.lift arI h.1 h.2

/-- (p3J gen 44) **The deletion bundle at `WCk WJL`** (module docstring). -/
theorem delHypsJLck [Fl4Proofs.P1.PlainStore st] (hT : P0.ArchTotal arI) (hK : ARKeep arI AR)
    (hticks : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      ∀ (a : A) (v : U64), arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR) (hAM : ARMask arI AR)
    (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (hth : Z.th = th) :
    DelHypsWRZ (L := L) arI (WCk (WJL (L := L) arI AR Z H Cs kb)) (WCk (WJLx (L := L) arI AR Z H Cs kb))
      (WCk (WJP (L := L) arI AR Z H Cs kb)) (RdLX (L := L) (A := A) th H Z.vx) (RzJ (L := L) (A := A) H Cs) th := by
  have hmask : ∀ (a : A) (irq : U64) (b : Bool), ∃ a', arI.mask_irq a irq b = ok a' := fun a i m => by
    obtain ⟨a', h, -⟩ := spec_exists (hT.mask_irq a i m); exact ⟨a', h⟩
  have hfree : ∀ (a : A) (irq : U64), ∃ a', arI.irq_free a irq = ok a' := fun a i => by
    obtain ⟨a', h, -⟩ := spec_exists (hT.irq_free a i); exact ⟨a', h⟩
  exact ⟨finJLZck arI hT hK hticks Z H Cs kb hth, (rdTrivJLX arI Z H Cs kb hth).ck,
    (jPreemptHypL arI hK hT hnd hPP Z H Cs kb hth).ckMap arI (fun _ _ _ _ h => h) (fun _ _ _ _ h c => ⟨h, c⟩)
      (fun _ _ _ _ h c => ⟨h, c⟩),
    (jPostDelHypL arI hAM hmask hfree Z H Cs kb hth).ck arI,
    (jZombieHypL arI Z H Cs kb hth).ck, (jSwapHypL arI Z H Cs kb hth).ck, (emptyHypJL arI Z H Cs kb hth).ck,
    fun _ _ _ _ h => ⟨h.1.x arI, h.2⟩⟩

variable {MR : A → Fl4Spec.MachineState → Prop}

/-- (p3J gen 44) **The deletion bundle at `WMR MR (WCk WJL)`** (module docstring). -/
theorem delHypsJLMck [Fl4Proofs.P1.PlainStore st] (hT : P0.ArchTotal arI) (hK : ARKeep arI AR)
    (hticks : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      ∀ (a : A) (v : U64), arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR)
    (hAM : ARMask arI AR) (Z : XSets) [VxE Z] (H : P1.Heap) (Cs : Set U64) (kb : U64) (hth : Z.th = th) :
    DelHypsWRZ (L := L) arI (WMR MR (WCk (WJL (L := L) arI AR Z H Cs kb)))
      (WMR MR (WCk (WJLx (L := L) arI AR Z H Cs kb)))
      (WCk (WJPM (L := L) arI AR MR Z H Cs kb)) (RdLX (L := L) (A := A) th H Z.vx) (RzJ (L := L) (A := A) H Cs) th := by
  have hmask : ∀ (a : A) (irq : U64) (b : Bool), ∃ a', arI.mask_irq a irq b = ok a' := fun a i m => by
    obtain ⟨a', h, -⟩ := spec_exists (hT.mask_irq a i m); exact ⟨a', h⟩
  have hfree : ∀ (a : A) (irq : U64), ∃ a', arI.irq_free a irq = ok a' := fun a i => by
    obtain ⟨a', h, -⟩ := spec_exists (hT.irq_free a i); exact ⟨a', h⟩
  exact ⟨(finJLZck arI hT hK hticks Z H Cs kb hth).mrv arI hM hKD hT, (rdTrivJLX arI Z H Cs kb hth).ck.mrv,
    (jPreemptHypLM arI hK hT hnd hM hPA Z H Cs kb hth).ckMap arI (fun _ _ _ _ h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩)
      (fun _ _ _ _ h c => ⟨⟨h.1, c⟩, h.2⟩) (fun _ _ _ _ h c => ⟨h, c⟩),
    ((jPostDelHypL arI hAM hmask hfree Z H Cs kb hth).ck arI).mrv arI hM hKD,
    (jZombieHypL arI Z H Cs kb hth).ck.mrv hM, (jSwapHypL arI Z H Cs kb hth).ck.mrv hM,
    (emptyHypJL arI Z H Cs kb hth).ck.mrv hM, fun _ _ _ _ h => ⟨⟨h.1.1.x arI, h.1.2⟩, h.2⟩⟩

end

/-! ## `hfin` at `CKI` states, and the footprinted bundles -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 44) **`finalise_cap` of a `NatFinKind` slot cap at a `JAtZ` state writes only `ProjW`** (module
docstring). -/
theorem JAtZ.finSlotProjW (hA : P0.ArchTotal arI) {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hns : Vs.NoSwitch σ) (hsg : SpecGlob σ)
    (hDS : DState (L := L) Z.th s σ G) {sl : Fl4Spec.CslotPtr} (hAs : AbsSlot Z.th sl) {c : capability.Cap}
    (hc : capAt (L.mem s) (cslotAddr sl) = ok c) (hk : P1.NatFinKind c) (fin ex : Bool) :
    objects.finalise_cap st arI s a c fin ex ⦃ r => P1.WritesIn st s r.2.1 (Mc.ProjW (L := L) H Cs s) ⦄ := by
  have h0 := J.blk.1.choose_spec.choose_spec
  have hcv := capV_of_capAt hc
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hty := hJ.typed _ hAs.isSlot
  rw [hcv] at hty
  cases c with
  | Null => exact finNoopProjW s a _ fin ex (Or.inl rfl)
  | Untyped p b f d => exact finNoopProjW s a _ fin ex (Or.inr (Or.inl ⟨_, _, _, _, rfl⟩))
  | Endpoint e b0 b1 b2 b3 b4 =>
    exact WP.spec_mono (P1.fin_cap_ep.kwN0 s a e b0 b1 b2 b3 b4 fin ex J.blk (hty.1 e b0 b1 b2 b3 b4 rfl))
      fun _ F => (P1.WritesA.w F).mono fun _ hb => Mc.kwN_projW J.kern.heap h0.nodes hb
  | Notification n b0 b1 b2 =>
    obtain ⟨hn, hH⟩ := hty.2.1 n b0 b1 b2 rfl
    exact WP.spec_mono (P1.fin_cap_ntfn.kwN0 s a n b0 b1 b2 fin ex J.blk hn hH)
      fun _ F => (P1.WritesA.w F).mono fun _ hb => Mc.kwN_projW J.kern.heap h0.nodes hb
  | Reply p g =>
    exact WP.spec_mono (P1.fin_cap_reply.kwDN0 hA s a p g fin ex J.blk (hty.2.2 p g rfl)) fun _ F =>
      footDN_projW J.kern.heap h0.nodes F
  | CNode p r g b => exact finCnodeProjW s a p r g b fin ex
  | Thread p =>
    have hthp : Z.th p = some .tcb := hDS.1.2.1.abs hAs hc
    have hpT : p ∈ Z.T := J.thT p hthp
    have hna : L.actionW s ≠ p := J.action_ne_of_noSwitch hpT hns
    have hv0 := jThrObj_ofExt (L := L) arI AR Z.th Z H Cs Ac Lst D s a σ rfl J _ p hAs.isSlot hcv
    obtain ⟨c0, ac0, hc0, hca0, hg0⟩ := hDS.1.1.abs_cap hAs
    rw [hc] at hc0
    cases eq_of_ok_eq hc0
    rw [hca0.abs] at hg0
    exact J.finThreadProjW hA hpT hna (Ne.symm (J.capNotIdle hsg hg0)) hv0 fin ex
  | IrqControl => exact finNoopProjW s a _ fin ex (Or.inr (Or.inr (Or.inl rfl)))
  | IrqHandler i => simp [P1.NatFinKind] at hk
  | Zombie p t n => exact finZombieProjW s a p t n fin ex
  | Domain => exact finNoopProjW s a _ fin ex (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | SchedContext p sb =>
    have hC' := J.scCap arI hAs hc
    obtain ⟨hHp, -, hpz, hna, hidle, -, -⟩ :=
      JAtZ.scCapFacts arI J hAs hc ⟨hC'.1, hC'.2, fun _ _ _ _ _ u hu => (hns u hu).elim⟩
    exact J.finScProjW hA ⟨_, hHp⟩ hpz hna hidle sb fin ex
  | SchedControl x =>
    exact finNoopProjW s a _ fin ex (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩)))))
  | Frame _ _ _ _ _ _ _ _ => simp [P1.NatFinKind] at hk
  | PageTable _ _ _ _ => simp [P1.NatFinKind] at hk
  | PageDirectory _ _ _ _ => simp [P1.NatFinKind] at hk
  | Pdpt _ _ _ _ => simp [P1.NatFinKind] at hk
  | Pml4 _ _ _ => simp [P1.NatFinKind] at hk
  | Vcpu _ => simp [P1.NatFinKind] at hk
  | Ept _ _ _ _ _ => simp [P1.NatFinKind] at hk
  | AsidControl => exact finNoopProjW s a _ fin ex (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  | AsidPool _ _ => simp [P1.NatFinKind] at hk
  | IoPortControl =>
    exact finNoopProjW s a _ fin ex (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  | IoPort _ _ _ => simp [P1.NatFinKind] at hk
  | TdxControl =>
    exact finNoopProjW s a _ fin ex (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))

set_option maxHeartbeats 4000000 in
/-- (p3J gen 44) **`hfin` of `DelHypsWRZ.foot` at `WCk WJL`** (module docstring): a slot cap at a `CKI` state of
`WJL` is `NatFinKind` (`JAtZ.finSlotProjW`) or an IRQ handler cap (P3JFinIrqFt's `finIrqProjW`, its bound the
cap's `CapWf`). -/
theorem hfinWJL [Fl4Proofs.P1.PlainStore st] (hA : P0.ArchTotal arI) (Z : XSets) (H : P1.Heap) (Cs : Set U64)
    (kb : U64) {s : S} {a : A} {σ : Fl4Spec.State Unit} {G : MdbGhost} {sl : Fl4Spec.CslotPtr}
    {c : capability.Cap} (hDS : DState (L := L) Z.th s σ G) (hW : WCk (WJL (L := L) arI AR Z H Cs kb) s a σ G)
    (hAs : AbsSlot Z.th sl) (hc : capAt (L.mem s) (cslotAddr sl) = ok c) (fin ex : Bool) :
    objects.finalise_cap st arI s a c fin ex ⦃ r => P1.WritesIn st s r.2.1 (Mc.ProjW (L := L) H Cs s) ⦄ := by
  obtain ⟨V, Ac, Lst, D, J, -, hns, hsg, -⟩ := hW.1.1
  have hkw := JAtZ.natFinKind_of_cki J hW.2 hAs.isSlot
  rw [capV_of_capAt hc] at hkw
  rcases hkw with hk | ⟨i, rfl⟩
  · exact J.finSlotProjW hA hns hsg hDS hAs hc hk fin ex
  · obtain ⟨c0, ac0, hc0, hca0, -⟩ := hDS.1.1.abs_cap hAs
    rw [hc] at hc0
    cases eq_of_ok_eq hc0
    exact finIrqProjW arI Z H Cs kb hDS hW.1 hca0.1 fin ex

/-- (p3J gen 44) `hpost` of `DelHypsWRZ.foot` from a `JAtZ` state (bounds from the cleanup cap's `CapWf`). -/
theorem JAtZ.postCapDelWf (hA : P0.ArchTotal arI) {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {cl : capability.Cap} (hwf : CapWf cl) :
    objects.post_cap_deletion st arI s a cl ⦃ r => P1.WritesIn st s r.1 (Mc.ProjW (L := L) H Cs s) ⦄ :=
  J.postCapDelProjW hA (fun i e => by subst e; exact hwf)
    (fun f l o e => by
      subst e
      have h' : f.val < 2 ^ 16 ∧ l.val < 2 ^ 16 ∧ f.val ≤ l.val := hwf
      exact ⟨h'.2.2, lt_of_lt_of_eq h'.2.1 (by norm_num)⟩)

set_option maxHeartbeats 4000000 in
/-- (p3J gen 44) **The deletion bundle at `WCk WJL` with the `ProjW` footprint from `s0`** (module docstring). -/
theorem delHypsJLft [Fl4Proofs.P1.PlainStore st] {th : TypedHeap} (hT : P0.ArchTotal arI) (hK : ARKeep arI AR)
    (hticks : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      ∀ (a : A) (v : U64), arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR) (hAM : ARMask arI AR)
    (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (hth : Z.th = th) (s0 : S) :
    DelHypsWRZ (L := L) arI (WFt (L := L) H Cs s0 (WCk (WJL (L := L) arI AR Z H Cs kb)))
      (WFt (L := L) H Cs s0 (WCk (WJLx (L := L) arI AR Z H Cs kb)))
      (WFt (L := L) H Cs s0 (WCk (WJP (L := L) arI AR Z H Cs kb)))
      (RdLX (L := L) (A := A) th H Z.vx) (RzJ (L := L) (A := A) H Cs) th := by
  subst hth
  refine (delHypsJLck arI hT hK hticks hnd hPP hAM Z H Cs kb rfl).foot arI s0 ?_ ?_ ?_ ?_
  · intro s a σ G sl c hDS hW hAs hc _
    exact hfinWJL hT Z H Cs kb hDS hW hAs hc _ false
  · intro s a σ G _ hW
    obtain ⟨V, Ac, Lst, D, J, -⟩ := hW.1.1
    exact J.ppProjW hT
  · intro s a σ G cl _ hW _ _ hwf
    obtain ⟨V, Ac, Lst, D, J, -⟩ := hW.1.1
    exact J.postCapDelWf hT hwf
  · intro s a σ G hW b hb
    obtain ⟨E, ⟨V, Ac, Lst, D, J, -⟩, -⟩ := hW.1
    exact J.slotWdProjW hb

set_option maxHeartbeats 4000000 in
/-- (p3J gen 44) **The deletion bundle at `WMR MR (WCk WJL)` with the `ProjW` footprint from `s0`** (module
docstring; the installs' form, XTopJointMRDel's `delHypsJLM` at `CKI` states). -/
theorem delHypsJLMft [Fl4Proofs.P1.PlainStore st] {th : TypedHeap} {MR : A → Fl4Spec.MachineState → Prop}
    (hT : P0.ArchTotal arI) (hK : ARKeep arI AR)
    (hticks : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      ∀ (a : A) (v : U64), arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR)
    (hAM : ARMask arI AR) (Z : XSets) [VxE Z] (H : P1.Heap) (Cs : Set U64) (kb : U64) (hth : Z.th = th) (s0 : S) :
    DelHypsWRZ (L := L) arI (WFt (L := L) H Cs s0 (WMR MR (WCk (WJL (L := L) arI AR Z H Cs kb))))
      (WFt (L := L) H Cs s0 (WMR MR (WCk (WJLx (L := L) arI AR Z H Cs kb))))
      (WFt (L := L) H Cs s0 (WCk (WJPM (L := L) arI AR MR Z H Cs kb)))
      (RdLX (L := L) (A := A) th H Z.vx) (RzJ (L := L) (A := A) H Cs) th := by
  subst hth
  refine (delHypsJLMck arI hT hK hticks hnd hM hKD hPA hAM Z H Cs kb rfl).foot arI s0 ?_ ?_ ?_ ?_
  · intro s a σ G sl c hDS hW hAs hc _
    exact hfinWJL hT Z H Cs kb hDS hW.1 hAs hc _ false
  · intro s a σ G _ hW
    obtain ⟨V, Ac, Lst, D, J, -⟩ := hW.1.1.1
    exact J.ppProjW hT
  · intro s a σ G cl _ hW _ _ hwf
    obtain ⟨V, Ac, Lst, D, J, -⟩ := hW.1.1.1
    exact J.postCapDelWf hT hwf
  · intro s a σ G hW b hb
    obtain ⟨E, ⟨V, Ac, Lst, D, J, -⟩, -⟩ := hW.1.1
    exact J.slotWdProjW hb

end

end

end Fl4Proofs.P3
