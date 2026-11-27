/-
P3x for virtualization (line virt, gen 20, item 2): **the VCPU retype loop at the untyped invoke's setup point**,
and the capability / binding halves of `JExtV` after it.

* **`LoopInv.cj_zero`**: at `i = 0`, UntypedLoop's `LoopInv` does not depend on the cap family `cj` (its only `cj`
  clause is `∀ j < i`). So the native retype's loop start (UntypedSuccess / UtTcbRetC's `hinv0`, stated over
  `cjOf nt …`) *is* the start the VCPU loop needs (over `vcj B`).
* **`LoopInv.zero`**: `LoopInv … s 0` from exactly the facts the untyped invoke proofs establish before the loop
  (after the untyped cap update and `extend_*_rel`): `StateRel`, `SlotsValid`, `MdbLinks`, `CdtRel`, `MdbInv` at the
  grown typed heap, the source cap, the empty window slots, the chain-range and descendant-range facts, the zero
  region; with `G0 := G`, `m0 :=` the memory, `σ1 :=` the spec state.
* **`create_new_objects_vcpu_setup`**: VirtLoopFrame's `create_new_objects_vcpu_loopR` with its `hinv` replaced by
  those setup facts: the VCPU loop is callable at the point where the untyped invoke proofs call
  `create_loop_frame`.
* `JExtV` after the loop (the parts that follow from the loop's own post):
  - `VtxCap.mono` (larger VCPU set);
  - **`loop_vtxCap`**: from `LoopInv … (vcj B) s n` and old caps `VtxCap V X` at `m0` for the chain members of
    `G0`: every slot cap of `th'` at the end is `VtxCap (VsI V B n) X` (null, an old cap, or `Vcpu (vI B j)`);
  - **`new_tcb0`**: a new VCPU's `TCB` word is 0 (`VRelInit`: `initVcpu`'s `tcb = none`), i.e. `JExtV.back` for the
    new VCPUs; `vI_ne0`: they are nonzero (`JExtV.nz`).
  Not derivable from the loop's post (open): `JExtV.bnd` for the old TCBs and `JExtV.back` for the old VCPUs —
  `create_new_objects_vcpu`'s frame obligation is stated over the coarse footprint `CrW` (the window, the head word,
  *all* of `V`'s objects), so its `M` cannot carry "`V`'s `TCB` words kept"; this needs `create_new_objects_vcpu`
  re-run with `iter_create`'s sharper per-object footprint (`InitL`: only the old head's `PREV` link).

No premise (no [J]/[P]/[W]); the hypotheses are state facts as in `create_new_objects_vcpu_loopR` (unchanged:
`CapAgree ar a` [P], `VirtCodeAgree ar a` [P]). New file only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtLoopFrame
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtLoopInv0
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.VirtSanEq Fl4Proofs.P3.VirtSanRel Fl4Proofs.P3.VirtVcpuRel
open Fl4Proofs.P3.VirtInitWalk Fl4Proofs.P3.VirtRetypeInit Fl4Proofs.P3.VirtRetypeLoop Fl4Proofs.P3.VirtLoopFrame

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {th' : TypedHeap} {srcSl : Fl4Spec.CslotPtr} {srcC : capability.Cap} {σ1 : Fl4Spec.State Unit}
  {f : Fl4Spec.CslotPtr × Fl4Spec.ObjRef → Fl4Spec.NonDet (Fl4Spec.State Unit) Unit}
  {pairs : List (Fl4Spec.CslotPtr × Fl4Spec.ObjRef)} {A k win : Nat} {dslot : Nat → U64} {zlo zhi : Nat}
  {G0 : MdbGhost} {m0 : U64 → U64}

/-- **At `i = 0` the loop invariant does not depend on the cap family.** -/
theorem LoopInv.cj_zero {cj cj' : Nat → capability.Cap} {s : S}
    (h : LoopInv (L := L) th' srcSl srcC σ1 f pairs A k win dslot zlo zhi G0 m0 cj s 0) :
    LoopInv (L := L) th' srcSl srcC σ1 f pairs A k win dslot zlo zhi G0 m0 cj' s 0 := by
  obtain ⟨σi, Gi, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, -, h15, h16, h17, h18, h19, h20⟩ := h
  exact ⟨σi, Gi, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    fun j hj => absurd hj (Nat.not_lt_zero _), h15, h16, h17, h18, h19, h20⟩

/-- **The loop start from the untyped invoke's setup facts** (module docstring). -/
theorem LoopInv.zero {s : S} {σb : Fl4Spec.State Unit} {G : MdbGhost} (cj : Nat → capability.Cap)
    (hR : StateRel th' (L.mem s) σb) (hV : SlotsValid th' (L.mem s)) (hM : MdbLinks th' (L.mem s) G)
    (hC : CdtRel th' (L.mem s) σb G) (hI : MdbInv (L.mem s) G)
    (hsrc : capAt (L.mem s) (cslotAddr srcSl) = ok srcC)
    (hdst : ∀ j, 0 ≤ j → j < win → capAt (L.mem s) (dslot j) = ok .Null)
    (hph : ∀ x ∈ G.chains.flatten, physF (capV (L.mem s) x) = true →
      baseF (capV (L.mem s) x) ≤ topF (capV (L.mem s) x) ∧
      (DisjR (capV (L.mem s) x) (A + 0 * k) (A + win * k) ∨
        (isUt (capV (L.mem s) x) = true ∧ Within srcC (capV (L.mem s) x))))
    (hds : ∀ y, Mdb.Desc G.par y (cslotAddr srcSl) → DisjR (capV (L.mem s) y) (A + 0 * k) (A + win * k))
    (hz : ZeroRegion (L.mem s) zlo zhi) :
    LoopInv (L := L) th' srcSl srcC σb f pairs A k win dslot zlo zhi G (L.mem s) cj s 0 :=
  ⟨σb, G, fun σf h => h, hR, hV, hM, hC, hI, hsrc, hdst, hph, hds, hz, fun x hx => Or.inl hx, fun x hx => hx,
    fun j hj => absurd hj (Nat.not_lt_zero _), fun x _ => rfl, fun y x => ⟨Or.inl, by
      rintro (h | ⟨j, hj, -⟩)
      · exact h
      · exact absurd hj (Nat.not_lt_zero _)⟩, fun h => h, fun ch hch => ⟨ch, hch, fun z hz => hz⟩,
    fun x _ => rfl, NullKeep.refl _ _⟩

end

/-! ## The VCPU loop at the setup point -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A} {a : A}
variable {V : Set U64} {th : TypedHeap}

set_option maxHeartbeats 4000000 in
/-- **The VCPU retype loop from the untyped invoke's setup facts** (module docstring; premises `CapAgree`,
`VirtCodeAgree`, both [P], as `create_new_objects_vcpu_loopR`). -/
theorem create_new_objects_vcpu_setup {Z : Type} (hA : P0.ArchTotal ar) (hc : CapAgree ar a)
    (hk : VirtCodeAgree ar a)
    {B n : Nat} {hd : U64} (R : RPl st V B n hd) {s : S}
    (hhd : ∀ s' : S, L.ksb s' = L.ksb s → P1.vHeadA st s' = hd)
    (Vl : VList st V th s) (hwz : WinZero (L.mem s) B 32768 n False)
    (th' : TypedHeap) (hP' : Placed th') {pp : U64} {rs : Nat} (hpp : th' pp = some (.cnode rs))
    {idx : List Bool} (hidx : idx.length = rs) {p sb fi : U64} {d : Bool}
    (hsb : sb.val < 64) (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64)
    (σb : Fl4Spec.State Unit) {dest : U64} {r : Nat} (hdest : th' dest = some (.cnode r)) (hr : r ≤ 64)
    (off nW base us : U64) (hnW : nW.val = n) (hbase : base.val = B) (dev : Bool)
    (hwin : off.val + n ≤ 2 ^ r) (hcan : CanonR B (B + n * 32768))
    (hpA : p.val ≤ B) (hAp : B + n * 32768 ≤ p.val + 2 ^ sb.val)
    (zlo zhi : Nat) (hzs : ∀ a, IsSlot th' a → a.val + 32 ≤ zlo ∨ zhi ≤ a.val)
    (hzW : ∀ b, CrW V B n hd b → ¬ (zlo ≤ b.val ∧ b.val < zhi))
    (hSW : ∀ y, IsSlot th' y → (y.val + 32 ≤ B ∨ B + n * 32768 ≤ y.val) ∧
      (hd.val + 8 ≤ y.val ∨ y.val + 32 ≤ hd.val) ∧ ∀ w ∈ V, y.val + 32 ≤ w.val ∨ w.val + 32768 ≤ y.val)
    (G : MdbGhost)
    (hsrcd : ∀ j, j < n → cslotAddr (pp.bv, idx) ≠ slotAddr dest.bv (BitVec.ofNat 64 (off.val + j)))
    -- the setup facts (as the untyped invoke proofs have them before the loop)
    (hR : StateRel th' (L.mem s) σb) (hV : SlotsValid th' (L.mem s)) (hM : MdbLinks th' (L.mem s) G)
    (hC : CdtRel th' (L.mem s) σb G) (hI : MdbInv (L.mem s) G)
    (hsrc : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi d))
    (hdst : ∀ j, 0 ≤ j → j < n → capAt (L.mem s) (slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) = ok .Null)
    (hph : ∀ x ∈ G.chains.flatten, physF (capV (L.mem s) x) = true →
      baseF (capV (L.mem s) x) ≤ topF (capV (L.mem s) x) ∧
      (DisjR (capV (L.mem s) x) (B + 0 * 32768) (B + n * 32768) ∨
        (isUt (capV (L.mem s) x) = true ∧ Within (.Untyped p sb fi d) (capV (L.mem s) x))))
    (hds : ∀ y, Mdb.Desc G.par y (cslotAddr (pp.bv, idx)) →
      DisjR (capV (L.mem s) y) (B + 0 * 32768) (B + n * 32768))
    (hz : ZeroRegion (L.mem s) zlo zhi) :
    objects.create_new_objects st ar s a fl4_abi.consts.object.X86Vcpu (cslotAddr (pp.bv, idx)) dest off nW base us
      dev ⦃ res =>
      res.2 = a ∧ VList st (VsI V B n) th res.1 ∧
        LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σb
          (Fl4Spec.createCap (Z := Unit) (.archObject .vcpuObj) us.val (pp.bv, idx) dev)
          ((windowSlots dest r off.val n).zip (regionPtrs (BitVec.ofNat 64 B) n 32768))
          B 32768 n (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) zlo zhi G (L.mem s) (vcj B) res.1 n ∧
        ∀ j, j < n → ∀ (l : List Fl4Spec.ObjRef) (σ : Fl4Spec.State Z) (x : Unit × Fl4Spec.State Z),
          x ∈ (Fl4Spec.NonDet.mapMx (fun v => Fl4Spec.setVcpu (Z := Z) v (Fl4Spec.initVcpu Fl4Spec.virtKind)) l σ).1 →
          (vI B j).bv ∈ l → VRelAt (memW st res.1) x.2 (vI B j).bv ⦄ :=
  create_new_objects_vcpu_loopR (Z := Z) hA hc hk R hhd Vl hwz th' hP' hpp hidx hsb hpfit σb hdest hr off nW base us
    hnW hbase dev hwin hcan hpA hAp zlo zhi hzs hzW hSW G (L.mem s) hsrcd
    (LoopInv.zero (vcj B) hR hV hM hC hI hsrc hdst hph hds hz)

end

/-! ## `JExtV` after the loop: caps, new VCPUs -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem VtxCap.mono {V V' X : Set U64} (h : V ⊆ V') {c : capability.Cap} (hc : VtxCap V X c) :
    VtxCap V' X c := by
  cases c with
  | Vcpu p => exact h hc
  | IoPort f l o => exact fun ho => h (hc ho)
  | _ => exact hc

theorem sub_vsI (V : Set U64) (B n : Nat) : V ⊆ VsI V B n := fun _ hw => Or.inl hw

/-- **Every slot cap after the VCPU loop is a VM-epoch cap at the grown VCPU set** (module docstring). -/
theorem loop_vtxCap {th' : TypedHeap} {srcSl : Fl4Spec.CslotPtr} {srcC : capability.Cap} {σ1 : Fl4Spec.State Unit}
    {f : Fl4Spec.CslotPtr × Fl4Spec.ObjRef → Fl4Spec.NonDet (Fl4Spec.State Unit) Unit}
    {pairs : List (Fl4Spec.CslotPtr × Fl4Spec.ObjRef)} {B win : Nat} {dslot : Nat → U64} {zlo zhi : Nat}
    {G0 : MdbGhost} {m0 : U64 → U64} {s : S} {V X : Set U64} {n : Nat}
    (h : LoopInv (L := L) th' srcSl srcC σ1 f pairs B 32768 win dslot zlo zhi G0 m0 (vcj B) s n)
    (hold : ∀ x ∈ G0.chains.flatten, VtxCap V X (capV m0 x)) :
    ∀ y, IsSlot th' y → VtxCap (VsI V B n) X (capV (L.mem s) y) := by
  obtain ⟨σi, Gi, -, -, -, hM, -, -, -, -, -, -, -, hsub, -, hcj, hm0, -⟩ := h
  intro y hy
  by_cases hn : capV (L.mem s) y = .Null
  · rw [hn]; trivial
  · have hyc : y ∈ Gi.chains.flatten := (hM.members y).2 ⟨hy, _, capAt_capV _ _, hn⟩
    rcases hsub y hyc with hg | ⟨j, hj, rfl⟩
    · rw [hm0 y hg]; exact VtxCap.mono (sub_vsI V B n) (hold y hg)
    · rw [hcj j hj]
      show vI B j ∈ VsI V B n
      exact Or.inr ⟨j, hj, rfl⟩

theorem tcb_bv : (vcpu.TCB).bv = Fl4Spec.VcpuLay.TCB := by unfold vcpu.TCB Fl4Spec.VcpuLay.TCB; decide

/-- **A new VCPU's `TCB` word is 0** (`JExtV.back` for the new VCPUs). -/
theorem new_tcb0 {s : S} {v : U64} (h : VRelInit (memW st s) v.bv) : L.mem s (vTcbA v) = 0#u64 := by
  have hc : Fl4Spec.VcpuRelCommon (memW st s) v.bv (Fl4Spec.initVcpu Fl4Spec.virtKind) := by
    by_cases hk : Fl4Spec.virtKind = .svm
    · exact (h.1 hk).toVcpuRelCommon
    · exact (h.2 hk).toVcpuRelCommon
  have e := hc.tcb
  simp only [Fl4Spec.initVcpu, Fl4Spec.vcpuTcbRef] at e
  split_ifs at e with hw
  have hb : vTcbA v = ⟨v.bv + Fl4Spec.VcpuLay.TCB⟩ := by
    have := VirtMsrEq.wadd_bv v vcpu.TCB
    rw [tcb_bv] at this
    unfold vTcbA
    rw [← this]
  unfold memW at hw
  rw [hb]
  exact UScalar.eq_of_val_eq (congrArg BitVec.toNat hw)

/-- The new VCPUs are nonzero (`JExtV.nz`). -/
theorem vI_ne0 {V : Set U64} {B n : Nat} {hd : U64} (R : RPl st V B n hd) {j : Nat} (hj : j < n) :
    vI B j ≠ 0#u64 := by
  intro e
  have h1 := R.vIv hj
  rw [e] at h1
  have := R.b0
  simp at h1
  omega

end

end
end Fl4Proofs.P3.VirtLoopInv0
