/-
P3x for virtualization (line virt, gen 27, item 1): **the VCPU retype loop and the full `X86Vcpu` retype at
`JExtV2`** (P3/JExtV2: `JExtV` without the IO-port owner clause, which gen 26 refuted on a reachable state).

* `loop_vtxCap2`: VirtLoopInv0's `loop_vtxCap` at `VtxCap2` (same proof, `VtxCap2.mono`).
* **`create_new_objects_vcpu_jext2`**: VirtLoopSharp's `create_new_objects_vcpu_jext` with `JExtV2` at the entry
  and after the loop (same proof).
* `ChSub G G'`: every chain of `G` lies inside one chain of `G'` (the loop invariant's chain clause, UntypedLoop's
  `LoopInv`; carried out so that `VcpuOneChain` can be shown across the retype, P3/VirtVChunkIns).
* **`retype_full_vcpu2`**: VirtRetFullV's `retype_full_vcpu` with `JExtV2` for `JExtV` (entry and post) and, in
  addition, `ChSub G G'` in the post. Same proof (the cap update's `E1` at `JExtV2`: the source's new cap is an
  `Untyped`, `VtxCap2` of it is `True`), at 4M heartbeats (gen 22's needed 16M; see the handoff for the split).
* **`noIoTcb_retExp`**: `NoIoTcb` across any retype described by `RetExp` (the new caps are not IO-port caps; old
  non-untyped caps are kept, untyped ones stay untyped): with `retype_full_vcpu2`, the VCPU retype keeps `NoIoTcb`.

Named premises: `CapAgree arI ar` [P], `VirtCodeAgree arI ar` [P] (unchanged, from `create_new_objects_vcpu_jext2`'s
per-object step). No new premise. New file only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtRetFullV
import Fl4Proofs.P3.JExtV2
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtRetFullV2
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.VirtSanEq Fl4Proofs.P3.VirtSanRel Fl4Proofs.P3.VirtVcpuRel
open Fl4Proofs.P3.VirtInitWalk Fl4Proofs.P3.VirtRetypeInit Fl4Proofs.P3.VirtRetypeLoop Fl4Proofs.P3.VirtLoopFrame
open Fl4Proofs.P3.VirtLoopInv0 Fl4Proofs.P3.VirtLoopSharp Fl4Proofs.P3.VirtRetVcpuPre Fl4Proofs.P3.VirtRetFullV Classical

noncomputable section
set_option linter.unusedSimpArgs false

/-- Every chain of `G` lies inside one chain of `G'`. -/
def ChSub (G G' : MdbGhost) : Prop := ∀ ch ∈ G.chains, ∃ ch' ∈ G'.chains, ∀ z ∈ ch, z ∈ ch'

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **Every slot cap after the VCPU loop is a `VtxCap2` cap at the grown VCPU set** (`loop_vtxCap`). -/
theorem loop_vtxCap2 {th' : TypedHeap} {srcSl : Fl4Spec.CslotPtr} {srcC : capability.Cap} {σ1 : Fl4Spec.State Unit}
    {f : Fl4Spec.CslotPtr × Fl4Spec.ObjRef → Fl4Spec.NonDet (Fl4Spec.State Unit) Unit}
    {pairs : List (Fl4Spec.CslotPtr × Fl4Spec.ObjRef)} {B win : Nat} {dslot : Nat → U64} {zlo zhi : Nat}
    {G0 : MdbGhost} {m0 : U64 → U64} {s : S} {V X : Set U64} {n : Nat}
    (h : LoopInv (L := L) th' srcSl srcC σ1 f pairs B 32768 win dslot zlo zhi G0 m0 (vcj B) s n)
    (hold : ∀ x ∈ G0.chains.flatten, VtxCap2 V X (capV m0 x)) :
    ∀ y, IsSlot th' y → VtxCap2 (VsI V B n) X (capV (L.mem s) y) := by
  obtain ⟨σi, Gi, -, -, -, hM, -, -, -, -, -, -, -, hsub, -, hcj, hm0, -⟩ := h
  intro y hy
  by_cases hn : capV (L.mem s) y = .Null
  · rw [hn]; trivial
  · have hyc : y ∈ Gi.chains.flatten := (hM.members y).2 ⟨hy, _, capAt_capV _ _, hn⟩
    rcases hsub y hyc with hg | ⟨j, hj, rfl⟩
    · rw [hm0 y hg]; exact VtxCap2.mono (sub_vsI V B n) (fun _ h => h) (hold y hg)
    · rw [hcj j hj]
      show vI B j ∈ VsI V B n
      exact Or.inr ⟨j, hj, rfl⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A} {a : A}
variable {V : Set U64} {th : TypedHeap}

set_option maxHeartbeats 4000000 in
/-- **The VCPU retype loop with all of `JExtV2` after it** (VirtLoopSharp's `create_new_objects_vcpu_jext` at
`JExtV2`, same proof; caps by `loop_vtxCap2`). -/
theorem create_new_objects_vcpu_jext2 {Z : Type} (hA : P0.ArchTotal ar) (hc : CapAgree ar a)
    (hk : VirtCodeAgree ar a)
    {B n : Nat} {hd : U64} (R : RPl st V B n hd) {s : S}
    (hhd : ∀ s' : S, L.ksb s' = L.ksb s → P1.vHeadA st s' = hd)
    (Vl : VList st V th s) (hwz : WinZero (L.mem s) B 32768 n False)
    (th' : TypedHeap) (hP' : Placed th') {pp : U64} {rs : Nat} (hpp : th' pp = some (.cnode rs))
    {idx : List Bool} (hidx : idx.length = rs) {p sb fi : U64} {d : Bool}
    (hsb : sb.val < 64) (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64)
    (σ1 : Fl4Spec.State Unit) {dest : U64} {r : Nat} (hdest : th' dest = some (.cnode r)) (hr : r ≤ 64)
    (off nW base us : U64) (hnW : nW.val = n) (hbase : base.val = B) (dev : Bool)
    (hwin : off.val + n ≤ 2 ^ r) (hcan : CanonR B (B + n * 32768))
    (hpA : p.val ≤ B) (hAp : B + n * 32768 ≤ p.val + 2 ^ sb.val)
    (zlo zhi : Nat) (hzs : ∀ a, IsSlot th' a → a.val + 32 ≤ zlo ∨ zhi ≤ a.val)
    (hzW : ∀ b, CrW V B n hd b → ¬ (zlo ≤ b.val ∧ b.val < zhi))
    (hSW : ∀ y, IsSlot th' y → (y.val + 32 ≤ B ∨ B + n * 32768 ≤ y.val) ∧
      (hd.val + 8 ≤ y.val ∨ y.val + 32 ≤ hd.val) ∧ ∀ w ∈ V, y.val + 32 ≤ w.val ∨ w.val + 32768 ≤ y.val)
    (G0 : MdbGhost)
    (hsrcd : ∀ j, j < n → cslotAddr (pp.bv, idx) ≠ slotAddr dest.bv (BitVec.ofNat 64 (off.val + j)))
    (hinv : LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) (.archObject .vcpuObj) us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val n).zip (regionPtrs (BitVec.ofNat 64 B) n 32768))
      B 32768 n (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) zlo zhi G0 (L.mem s) (vcj B) s 0)
    {X : Set U64} (E : JExtV2 (L := L) V X th' s) (hMl : MdbLinks th' (L.mem s) G0)
    (hTW : ∀ t, th' t = some .tcb → P1.TcbAddr t ∧ ((t.val + 4096 ≤ B ∨ B + n * 32768 ≤ t.val) ∧ tVcpuA t ≠ hd ∧
        ∀ w ∈ V, t.val + 4096 ≤ w.val ∨ w.val + 32768 ≤ t.val) ∧
        ∀ y, IsSlot th' y → ¬ (y.val ≤ (tVcpuA t).val ∧ (tVcpuA t).val < y.val + 32)) :
    objects.create_new_objects st ar s a fl4_abi.consts.object.X86Vcpu (cslotAddr (pp.bv, idx)) dest off nW base us
      dev ⦃ res =>
      res.2 = a ∧ VList st (VsI V B n) th res.1 ∧
        LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
          (Fl4Spec.createCap (Z := Unit) (.archObject .vcpuObj) us.val (pp.bv, idx) dev)
          ((windowSlots dest r off.val n).zip (regionPtrs (BitVec.ofNat 64 B) n 32768))
          B 32768 n (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) zlo zhi G0 (L.mem s) (vcj B) res.1 n ∧
        (∀ j, j < n → ∀ (l : List Fl4Spec.ObjRef) (σ : Fl4Spec.State Z) (x : Unit × Fl4Spec.State Z),
          x ∈ (Fl4Spec.NonDet.mapMx (fun v => Fl4Spec.setVcpu (Z := Z) v (Fl4Spec.initVcpu Fl4Spec.virtKind)) l σ).1 →
          (vI B j).bv ∈ l → VRelAt (memW st res.1) x.2 (vI B j).bv) ∧
        JExtV2 (L := L) (VsI V B n) X th' res.1 ⦄ := by
  obtain ⟨hMc, hFW, hIns⟩ := mv_obligations (L := L) R th' hP' hpp hidx hsb hpfit σ1 hdest hr off us dev hwin hcan
    hpA hAp zlo zhi hzs hzW hSW G0 (L.mem s) hsrcd
  have hvT := fun v (hv : v ∈ V) => vtcb_off (L := L) R hSW hv
  have htT := fun t (ht : th' t = some .tcb) => tvcpu_off (V := V) (hTW t ht)
  refine WP.spec_mono (create_new_objects_vcpuL hA hc hk R hhd
    (fun s' i => MV (L := L) th' pp idx p sb fi d σ1 us dev dest r off B n zlo zhi G0 (L.mem s) s' i ∧
      VirtLoopSharp.MK st th' (L.mem s) V s')
    (fun s1 s2 i h hw => ⟨hMc s1 s2 i h.1 (hw.mono fun b hb => CrL.crW hb),
      fun v hv => (hw.mem_eq (hvT v hv).1 (hvT v hv).2.1).trans (h.2.1 v hv),
      fun t ht => (hw.mem_eq (htT t ht).1 (htT t ht).2).trans (h.2.2 t ht)⟩)
    hFW (cslotAddr (pp.bv, idx)) dest off
    (fun iw hiw s2 h => WP.spec_mono (hIns iw hiw s2 h.1) fun s3 ⟨h1, hw⟩ =>
      ⟨⟨h1, fun v hv => (hw.mem_eq (hvT v hv).1 fun hs => by
          obtain ⟨-, y, hy, g1, g2⟩ := hs
          exact (hvT v hv).2.2 y hy ⟨g1, g2⟩).trans (h.2.1 v hv),
        fun t ht => (hw.mem_eq (htT t ht).1 fun hs => by
          obtain ⟨-, y, hy, g1, g2⟩ := hs
          exact (hTW t ht).2.2 y hy ⟨g1, g2⟩).trans (h.2.2 t ht)⟩, hw⟩)
    Vl hwz ⟨⟨hinv, Nat.zero_le _⟩, fun _ _ => rfl, fun _ _ => rfl⟩ nW base us hnW hbase dev) ?_
  rintro res ⟨h1, h2, h3, ⟨hI, -⟩, hK⟩
  refine ⟨h1, h2, hI, fun j hj l σ x hx hm => retype_vcpu_rel (h3 j hj) l hx hm, ?_⟩
  refine ⟨loop_vtxCap2 hI (fun x hx => E.cap x ((hMl.members x).1 hx).1), fun t ht => ?_, fun v hv => ?_,
    fun v hv => ?_⟩
  · rw [hK.2 t ht]
    rcases E.bnd t ht with h0 | ⟨hw, hb⟩
    · exact Or.inl h0
    · exact Or.inr ⟨Or.inl hw, by rw [hK.1 _ hw]; exact hb⟩
  · rcases hv with hv | ⟨j, hj, rfl⟩
    · rw [hK.1 v hv]
      rcases E.back v hv with h0 | ⟨ht, hb⟩
      · exact Or.inl h0
      · exact Or.inr ⟨ht, by rw [hK.2 _ ht]; exact hb⟩
    · exact Or.inl (new_tcb0 (h3 j hj))
  · rcases hv with hv | ⟨j, hj, rfl⟩
    · exact E.nz v hv
    · exact vI_ne0 R hj

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The full `X86Vcpu` retype against `fl4InvokeUntypedV`, at `JExtV2`** (module docstring). -/
theorem retype_full_vcpu2 {A' : Type} (arI : machine.Arch A') (ar : A') (hA : P0.ArchTotal arI)
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
    {V X : Set U64} (Vl : VList st V th s) (E : JExtV2 (L := L) V X th s)
    (hVf : ∀ w ∈ V, w.val % 32768 = 0 ∧ w.val + 32768 ≤ 2 ^ 64)
    (hVV : ∀ w ∈ V, ∀ w' ∈ V, w ≠ w' → w.val + 32768 ≤ w'.val ∨ w'.val + 32768 ≤ w.val)
    (hVreg : ∀ w ∈ V, w.val + 32768 ≤ p.val + fi.val ∨ p.val + 2 ^ sb.val ≤ w.val)
    (hhdV : ∀ w ∈ V, (P1.vHeadA st s).val < w.val ∨ w.val + 32768 ≤ (P1.vHeadA st s).val)
    (hhdreg : (P1.vHeadA st s).val + 8 ≤ p.val + fi.val ∨ p.val + 2 ^ sb.val ≤ (P1.vHeadA st s).val)
    (hSV : ∀ y, IsSlot th y → ((P1.vHeadA st s).val + 8 ≤ y.val ∨ y.val + 32 ≤ (P1.vHeadA st s).val) ∧
      ∀ w ∈ V, y.val + 32 ≤ w.val ∨ w.val + 32768 ≤ y.val)
    (hTV : ∀ t, th t = some .tcb → P1.TcbAddr t ∧ tVcpuA t ≠ P1.vHeadA st s ∧
      (∀ w ∈ V, t.val + 4096 ≤ w.val ∨ w.val + 32768 ≤ t.val) ∧
      ∀ y, IsSlot th y → ¬ (y.val ≤ (tVcpuA t).val ∧ (tVcpuA t).val < y.val + 32)) :
    untyped.retype st arI s ar (cslotAddr (pp.bv, idx)) false
      ⟨Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)⟩ nt us dest off win dev ⦃ res =>
      res.1 = .Ok () ∧ res.2.2 = ar ∧ ∃ σ' G',
        (Fl4Spec.fl4InvokeUntypedV (Z := Unit) (.retype (pp.bv, idx) false p.bv
          (Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)) (.archObject .vcpuObj) us.val
          (windowSlots dest r off.val win.val) dev)).run σ = ({(.ok (), σ')}, False) ∧
        StateRel th (L.mem res.2.1) σ' ∧ SlotsValid th (L.mem res.2.1) ∧
        MdbLinks th (L.mem res.2.1) G' ∧ CdtRel th (L.mem res.2.1) σ' G' ∧ MdbInv (L.mem res.2.1) G' ∧
        (UtInv (L.mem res.2.1) G' ∧ MdbStep (L.mem s) G (L.mem res.2.1) G') ∧
        ZeroRegion (L.mem res.2.1)
          ((Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)).toNat + win.val * 32768) (p.val + 2 ^ sb.val) ∧
        (FinInv th (L.mem s) σ G → FinInv th (L.mem res.2.1) σ' G') ∧
        VList st (VsI V (Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)).toNat win.val) th res.2.1 ∧
        JExtV2 (L := L) (VsI V (Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)).toNat win.val) X th res.2.1 ∧
        ChSub G G' ∧
        (∀ j, j < win.val →
          VRelAt (memW st res.2.1) σ' (vI (Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)).toNat j).bv) ∧
        ∃ dslot, RetExp th th (L.mem s) (L.mem res.2.1) G G'
          (Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)).toNat 32768 win.val dslot
          (vcj (Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)).toNat) (cslotAddr (pp.bv, idx)) ∧
          ThX th th (Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)).toNat 32768 win.val nt.val us.val ∧
          DslotC th dslot win.val ⦄ := by
  -- sizes and the region
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  have hz15 : zOf nt.val us.val = 15 := by rw [hnt]; simp [zOf]
  rw [hz15] at hmem
  rw [hz15]
  have hk1 : 1 ≤ 32768 := by norm_num
  obtain ⟨hA1, hA2, hA3, hA4⟩ := retype_region p fi sb.val 15 win.val hsb (by norm_num) hpal hpfit hfi hw1 hmem
  rw [show (2 : Nat) ^ 15 = 32768 by norm_num] at hA2 hA3 hA4
  set Ab := Fl4Spec.alignUp (p.bv + fi.bv) 15 with hAbdef
  set A := Ab.toNat with hAdef
  set aligned : U64 := ⟨Ab⟩ with halig
  have halv : aligned.val = A := rfl
  set n := win.val with hndef
  set src := cslotAddr (pp.bv, idx) with hsrcdef
  have hAs : AbsSlot th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hs : IsSlot th src := hAs.isSlot
  have hsrcm : src ∈ G.chains.flatten := (hM.members src).2 ⟨hs, _, hcap, by simp⟩
  have hcv0 := capV_of_capAt hcap
  obtain ⟨hsb', hst'⟩ := topF_ut p sb fi dev hsb hpfit
  -- FL4: the cap update, then the loop
  obtain ⟨total, htot, hret⟩ := retype_noreset_eq14 (L := L) arI s ar src aligned nt us dest off win dev hnt
    (by rw [hz15]; norm_num) p sb fi dev hcap
  rw [hz15] at htot
  rw [hret]
  set nfi := core.num.U64.wrapping_sub (core.num.U64.wrapping_add aligned total) p with hnfi
  set srcC' : capability.Cap := .Untyped p sb nfi dev with hsrcC'
  have he' : EncWf srcC' := by
    have : EncWf (capability.Cap.Untyped p sb fi dev) := by rw [capAt_words] at hcap; exact decode_encWf hcap
    exact ⟨this.1, this.2⟩
  obtain ⟨s1, hs1, hU1⟩ := spec_exists (set_cap_upd (L := L) hP s hs srcC' he')
  obtain ⟨s1', hs1', σa, hσa, hR1, hV1, hcdt1, hio1⟩ := spec_exists
    (retype_set_untyped_rel (L := L) th s σ hR hV hP hpp hidx hcap aligned total win 15 htot)
  rw [hs1] at hs1'; have e := eq_of_ok_eq hs1'; subst e
  rw [hs1]; simp only [bind_ok]
  obtain ⟨hcs1, hco1, hlk1, hfr1⟩ := hU1
  have hupd : CapShapeUpd th (L.mem s) (L.mem s1) src :=
    { links := hlk1, caps := hco1
      shp := by rw [hcs1, hcv0]; rfl
      bdg := by rw [hcs1, hcv0]; rfl
      nn := by rw [hcs1]; simp [srcC'] }
  have hM1 := hupd.mdbLinks hM hsrcm
  have hI1 := hupd.mdbInv hM hI
  have hC1 := hupd.cdtRel hC hcdt1 hio1
  have hksb1 : L.ksb s1 = L.ksb s := by
    obtain ⟨s', h', h''⟩ := spec_exists (set_cap_ksb (L := L) src s srcC')
    rw [hs1] at h'; cases eq_of_ok_eq h'; exact h''
  -- the spec's pieces
  have hgs : Fl4Spec.getCap (Z := Unit) (pp.bv, idx) σ = ({(.untypedCap dev p.bv sb.val fi.val, σ)}, False) := by
    obtain ⟨c, a, hc, hca, hg⟩ := hR.slot_cap (sl := (pp.bv, idx)) (p := pp) rfl (by simpa [hidx] using hpp)
    rw [hcap] at hc; have := eq_of_ok_eq hc; subst this
    rw [hg, hca.abs]; rfl
  have hwl : (windowSlots dest r off.val n).length = n := by simp [windowSlots]
  have hss : Fl4Spec.setCap (Z := Unit) (.untypedCap dev p.bv (Fl4Spec.bitsOf (.untypedCap dev p.bv sb.val fi.val))
      (Fl4Spec.unat (Ab + (BitVec.ofNat 64 (windowSlots dest r off.val n).length <<<
        Fl4Spec.fl4ObjBitsApi (.archObject .vcpuObj) us.val) - p.bv)))
      (pp.bv, idx) σ = ({((), σa)}, False) := by
    rw [hwl, fl4ObjBitsApi_vcpu]; exact hσa
  set ko : Fl4Spec.KernelObject := Fl4Spec.defaultObject (.archObject .vcpuObj) dev us.val σa.curDomain with hko
  set σb := regionHeap σa (regionPtrs Ab n 32768) ko with hσb
  have hrb : Fl4Spec.retypeRegionWith (Z := Unit) Fl4Spec.fl4ObjBitsApi Ab (windowSlots dest r off.val n).length
      us.val (.archObject .vcpuObj) dev σa =
        ({(regionPtrs Ab (windowSlots dest r off.val n).length 32768, σb)}, False) := by
    rw [retypeRegionWith_eq, if_pos (by simp), hwl]; rfl
  -- the free region after the cap update
  have hzero1 : ZeroRegion (L.mem s1) (p.val + fi.val) (p.val + 2 ^ sb.val) := by
    intro w hw h1 h2
    obtain ⟨q, kq, hq, hq1, hq2, -⟩ := slot_in_object hP hs
    have hne : w.val ≠ src.val ∧ w.val ≠ src.val + 8 := by
      rcases hfree q kq hq with h | h <;> constructor <;> omega
    rw [hfr1 w hw hne.1 hne.2]; exact hzero w hw h1 h2
  have hrf : RegionFree th A (A + n * 32768) := by
    intro q kd hq
    rcases hfree q kd hq with h | h
    · left; omega
    · right; omega
  have hfitA : A + n * 32768 ≤ 2 ^ 64 := by omega
  obtain ⟨hRb, hCb⟩ := extend_other_rel th (L.mem s1) σa G hR1 hC1 Ab A n 32768 rfl hk1 hfitA hrf ko
  have hzsOld : ∀ a, IsSlot th a → a.val + 32 ≤ A + n * 32768 ∨ p.val + 2 ^ sb.val ≤ a.val := by
    intro a ha
    obtain ⟨q, kq, hq, hq1, hq2, -⟩ := slot_in_object hP ha
    rcases hfree q kq hq with h | h
    · left; omega
    · right; omega
  have hold : ∀ a, IsSlot th a → a.val + 32 ≤ A ∨ p.val + 2 ^ sb.val ≤ a.val := by
    intro a ha
    obtain ⟨q, kq, hq, hq1, hq2, -⟩ := slot_in_object hP ha
    rcases hfree q kq hq with h | h
    · left; omega
    · right; omega
  have hsrc1 : capAt (L.mem s1) src = ok srcC' := by rw [capAt_capV, hcs1]
  have hsrcd : ∀ j, j < n → src ≠ slotAddr dest.bv (BitVec.ofNat 64 (off.val + j)) := by
    intro j hj e
    have := hempty (off.val + j) (by omega) (by omega)
    rw [← e, hcap] at this; cases eq_of_ok_eq this
  have hbA : (BitVec.ofNat 64 aligned.val : BitVec 64) = Ab := by rw [← bv_eq_ofNat]
  -- the VCPU placement at the loop's start
  set hd := P1.vHeadA st s with hhddef
  have hd1 : ∀ s' : S, L.ksb s' = L.ksb s1 → P1.vHeadA st s' = hd := fun s' h => hd_of_ksb (h.trans hksb1)
  have RP : RPl st V A n hd :=
    { bal := hA2, b0 := by omega, bfit := by omega, vf := hVf, vv := hVV
      vw := fun w hw => by rcases hVreg w hw with h | h <;> [left; right] <;> omega
      hv := hhdV
      hw := by rcases hhdreg with h | h <;> [left; right] <;> omega }
  have hSW : ∀ y, IsSlot th y → (y.val + 32 ≤ A ∨ A + n * 32768 ≤ y.val) ∧
      (hd.val + 8 ≤ y.val ∨ y.val + 32 ≤ hd.val) ∧ ∀ w ∈ V, y.val + 32 ≤ w.val ∨ w.val + 32768 ≤ y.val := by
    intro y hy
    refine ⟨?_, (hSV y hy).1, (hSV y hy).2⟩
    rcases hold y hy with h | h
    · left; exact h
    · right; omega
  have hTW : ∀ t, th t = some .tcb → P1.TcbAddr t ∧ ((t.val + 4096 ≤ A ∨ A + n * 32768 ≤ t.val) ∧ tVcpuA t ≠ hd ∧
      ∀ w ∈ V, t.val + 4096 ≤ w.val ∨ w.val + 32768 ≤ t.val) ∧
      ∀ y, IsSlot th y → ¬ (y.val ≤ (tVcpuA t).val ∧ (tVcpuA t).val < y.val + 32) := by
    intro t ht
    obtain ⟨h1, h2, h3, h4⟩ := hTV t ht
    have e4 : objSize ObjKind.tcb = 4096 := rfl
    refine ⟨h1, ⟨?_, h2, h3⟩, h4⟩
    rcases hfree t _ ht with h | h
    · left; omega
    · right; omega
  have hzW : ∀ b, CrW V A n hd b → ¬ (A + n * 32768 ≤ b.val ∧ b.val < p.val + 2 ^ sb.val) := by
    rintro b (⟨h1, h2⟩ | rfl | ⟨w, hw, h1, h2⟩) ⟨h3, h4⟩
    · omega
    · rcases hhdreg with h | h <;> omega
    · rcases hVreg w hw with h | h <;> omega
  -- VList and JExtV at the state after the cap update
  have hslot_ne : ∀ b : U64, (∀ y, IsSlot th y → ¬ (y.val ≤ b.val ∧ b.val < y.val + 32)) →
      b.val ≠ src.val ∧ b.val ≠ src.val + 8 := by
    intro b hb
    constructor <;> intro e <;> exact hb src hs ⟨by omega, by omega⟩
  have Vl1 : VList st V th s1 := by
    refine Vl.frame hksb1 (fun b hb => ?_) (fun _ h => h) (fun _ h => h)
    have hal := Vl.lw_al hVf hb
    refine hfr1 b hal ?_ ?_ <;> intro e
    · rcases hb with rfl | ⟨w, hw, rfl | rfl⟩
      · have := (hSV src hs).1; first | omega | (rw [hhddef] at this; omega) | (rw [← hhddef] at e; omega)
      · have := lay_next_val (hVf w hw).2; have := (hSV src hs).2 w hw; omega
      · have := lay_prev_val (hVf w hw).2; have := (hSV src hs).2 w hw; omega
    · rcases hb with rfl | ⟨w, hw, rfl | rfl⟩
      · have := (hSV src hs).1; first | omega | (rw [hhddef] at this; omega) | (rw [← hhddef] at e; omega)
      · have := lay_next_val (hVf w hw).2; have := (hSV src hs).2 w hw; omega
      · have := lay_prev_val (hVf w hw).2; have := (hSV src hs).2 w hw; omega
  have hvT := fun v (hv : v ∈ V) => vtcb_off (L := L) RP hSW hv
  have htT := fun t (ht : th t = some .tcb) => tvcpu_off (V := V) (B := A) (n := n) (hd := hd) (hTW t ht)
  have E1 : JExtV2 (L := L) V X th s1 := by
    have hvk : VKeep (L := L) th s s1 := fun t ht => by
      obtain ⟨n1, n2⟩ := hslot_ne _ (hTW t ht).2.2
      exact hfr1 _ (htT t ht).1 n1 n2
    have hbk : ∀ v ∈ V, L.mem s1 (vTcbA v) = L.mem s (vTcbA v) := fun v hv => by
      obtain ⟨n1, n2⟩ := hslot_ne _ (hvT v hv).2.2
      exact hfr1 _ (hvT v hv).1 n1 n2
    refine ⟨fun y hy => ?_, fun t ht => ?_, fun v hv => ?_, E.nz⟩
    · by_cases hys : y = src
      · rw [hys, hcs1]; trivial
      · rw [hco1 y hy hys]; exact E.cap y hy
    · rw [hvk t ht]
      rcases E.bnd t ht with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, by rw [hbk _ h1]; exact h2⟩
    · rw [hbk v hv]
      rcases E.back v hv with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, by rw [hvk _ h1]; exact h2⟩
  have hwz : WinZero (L.mem s1) A 32768 n False := fun w hw h1 h2 =>
    Or.inl (hzero1 w hw (by omega) (by omega))
  -- the loop start (UntypedSuccess's `hinv0`, over the VCPU caps)
  have hinv0 : LoopInv (L := L) th (pp.bv, idx) srcC' σb
      (Fl4Spec.createCap (Z := Unit) (.archObject .vcpuObj) us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val n).zip (regionPtrs (BitVec.ofNat 64 A) n 32768))
      A 32768 n (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j)))
      (A + n * 32768) (p.val + 2 ^ sb.val) G (L.mem s1) (vcj A) s1 0 := by
    refine ⟨σb, G, fun σf h => h, hRb, hV1, hM1, hCb, hI1, hsrc1, ?_, ?_, ?_,
      fun w hw h1 h2 => hzero1 w hw (by omega) h2, fun x hx => Or.inl hx, fun x hx => hx,
      fun j hj => absurd hj (by omega), fun x _ => rfl, fun y x => ⟨Or.inl, by
        rintro (h | ⟨j, hj, -⟩)
        · exact h
        · omega⟩, fun h => h, fun ch hch => ⟨ch, hch, fun z hz => hz⟩, fun x _ => rfl, NullKeep.refl _ _⟩
    · intro j _ hj
      have hj' : off.val + j < 2 ^ r := by omega
      have hd' : IsSlot th (slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) :=
        ⟨dest, off.val + j, Or.inl ⟨r, hdest, hj'⟩, rfl⟩
      have hnull := hempty (off.val + j) (by omega) (by omega)
      have hne : slotAddr dest.bv (BitVec.ofNat 64 (off.val + j)) ≠ src := by
        intro e; rw [e, hcap] at hnull; cases eq_of_ok_eq hnull
      rw [capAt_capV, hco1 _ hd' hne, ← capAt_capV]; exact hnull
    · intro x hx hp
      have hxs : IsSlot th x := ((hM.members x).1 hx).1
      by_cases hxa : x = src
      · subst hxa
        rw [hcs1]
        refine ⟨?_, Or.inr ⟨rfl, ⟨le_refl _, le_refl _⟩⟩⟩
        obtain ⟨e1, e2, -⟩ := range_of_shape (show shape srcC' = shape (capability.Cap.Untyped p sb fi dev) from rfl)
        rw [e1, e2, hsb', hst']; have := Nat.one_le_two_pow (n := sb.val); omega
      · rw [hco1 x hxs hxa] at hp ⊢
        refine ⟨hU.reg x hx hp, ?_⟩
        rcases hU.noov src hsrcm p sb fi dev hcv0 x hx hp with h | ⟨hu, hw⟩
        · left; unfold DisjR at h ⊢; simp only [Nat.zero_mul, Nat.add_zero]; omega
        · right; refine ⟨hu, ?_⟩
          obtain ⟨e1, e2, -⟩ := range_of_shape (show shape srcC' = shape (capability.Cap.Untyped p sb fi dev) from rfl)
          unfold Within at hw ⊢; rw [hcv0] at hw; rw [e1, e2]; exact hw
    · intro y hy
      obtain ⟨hp1, hp2, hp3⟩ := hU.inc src hsrcm p sb fi dev hcv0 y hy
      have hym := (desc_mem hM hy).1
      have hys : IsSlot th y := ((hM.members y).1 hym).1
      have hya : y ≠ src := by
        intro e; subst e
        rw [hcv0, hst'] at hp3
        have : (1#64 <<< sb.val - fi.bv : BitVec 64).toNat = 2 ^ sb.val - fi.val := by
          rw [BitVec.toNat_sub, BitVec.toNat_shiftLeft]
          simp only [BitVec.toNat_ofNat, Nat.shiftLeft_eq, show fi.bv.toNat = fi.val from rfl]
          have hM' : 2 ^ sb.val < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hsb
          rw [show (1 % 2 ^ 64 * 2 ^ sb.val) % 2 ^ 64 = 2 ^ sb.val by
            rw [show (1 : Nat) % 2 ^ 64 = 1 from rfl, Nat.one_mul, Nat.mod_eq_of_lt hM']]
          omega
        rw [this, Nat.shiftRight_eq_div_pow, show 2 ^ sb.val - fi.val = 0 by omega] at hmem
        simp at hmem; omega
      rw [hco1 y hys hya]
      unfold DisjR; left; simp only [Nat.zero_mul, Nat.add_zero]; omega
  -- the loop
  have hntc : nt = fl4_abi.consts.object.X86Vcpu := by unfold fl4_abi.consts.object.X86Vcpu; scalar_tac
  obtain ⟨⟨s2, a2⟩, hres, ha2, hVl2, hfin, hrel2, hE2⟩ := spec_exists
    (create_new_objects_vcpu_jext2 (Z := Unit) hA hcA hkA RP hd1 Vl1 hwz th hP hpp hidx hsb hpfit σb hdest
      (by omega) off win aligned us rfl halv dev hwin (CanonR.of_high (by omega)) (by omega) hA3
      (A + n * 32768) (p.val + 2 ^ sb.val) hzsOld hzW hSW G hsrcd hinv0 E1 hM1 hTW)
  have hres' : objects.create_new_objects st arI s1 ar nt src dest off win aligned us dev = ok (s2, a2) := by
    rw [hntc]; exact hres
  rw [hres']
  simp only [bind_ok, uncurry_apply_pair]
  rw [WP.spec_ok]
  simp only at ha2 hVl2 hfin hrel2 hE2
  obtain ⟨σf, Gf, hchain, hRf, hVf', hMf, hCf, hIf, -, -, -, -, hZf, hT1, hT1b, hT2a, hT2b, hT3, hFf, hChf, hRvf,
    hNKf⟩ := hfin
  have hdrop : ((windowSlots dest r off.val n).zip (regionPtrs (BitVec.ofNat 64 A) n 32768)).drop n = [] := by
    apply List.drop_of_length_le; simp [windowSlots, regionPtrs]
  rw [hdrop] at hchain
  have hmx := hchain σf (mapMx_nil _ _)
  rw [show (BitVec.ofNat 64 A : BitVec 64) = Ab from hbA] at hmx
  -- the spec's invocation without the hook
  have hinvU : (Fl4Spec.invokeUntypedWith (Z := Unit) Fl4Spec.fl4ObjBitsApi (.retype (pp.bv, idx) false p.bv Ab
      (.archObject .vcpuObj) us.val (windowSlots dest r off.val n) dev)).run σ = ({(.ok (), σf)}, False) := by
    apply invokeUntyped_noreset_eq Fl4Spec.fl4ObjBitsApi (pp.bv, idx) p.bv Ab (.archObject .vcpuObj) us.val _ dev
      σ σa σb σf _ _ hgs hss hrb
    · simp
    · rw [hwl]; exact hmx
  -- the hook
  set l := regionPtrs Ab n 32768 with hldef
  have hkT : khT σf = khT σb := by
    exact kt_mapMx_createCap (.archObject .vcpuObj) us.val (pp.bv, idx) dev
      ((windowSlots dest r off.val n).zip l) σb ((), σf) (by rw [hmx]; exact Set.mem_singleton _)
  have hpre : ∀ v ∈ l, ∃ k, σf.kheap v = some k ∧
      Fl4Spec.aType k = Fl4Spec.aType (.archObj (.vcpu (Fl4Spec.initVcpu Fl4Spec.virtKind))) := by
    intro v hv
    have h1 : khT σf v = some (Fl4Spec.aType ko) := by
      rw [hkT]; unfold khT; simp only [hσb, regionHeap]; rw [foldr_update_apply, if_pos hv]; rfl
    unfold khT at h1
    cases hk : σf.kheap v with
    | none => rw [hk] at h1; cases h1
    | some k =>
      rw [hk] at h1
      have h2 : Fl4Spec.aType k = Fl4Spec.aType ko := by simpa using h1
      exact ⟨k, rfl, h2.trans rfl⟩
  set σh : Fl4Spec.State Unit :=
    { σf with kheap := fun q => if q ∈ l then some (.archObj (.vcpu (Fl4Spec.initVcpu Fl4Spec.virtKind))) else σf.kheap q }
    with hσh
  have hhook : Fl4Spec.NonDet.mapMx (fun v => Fl4Spec.setVcpu (Z := Unit) v (Fl4Spec.initVcpu Fl4Spec.virtKind))
      (Fl4Spec.retypeAddrs Fl4Spec.fl4ObjBitsApi Ab (windowSlots dest r off.val n).length us.val
        (.archObject .vcpuObj)) σf = ({((), σh)}, False) := by
    rw [retypeAddrs_vcpu, hwl]
    exact mapMx_setVcpu_det _ l σf hpre
  have hrun := fl4InvokeUntypedV_vcpu_run (pp.bv, idx) p.bv Ab us.val (windowSlots dest r off.val n) dev hinvU hhook
  have hnl : ∀ q kd, th q = some kd → 1 ≤ objSize kd → q.bv ∉ l := fun q kd hq hs1 hm =>
    not_newP hk1 hrf hq hs1 ((mem_regionPtrs Ab A 32768 n rfl hk1 hfitA q).1 hm)
  have hRh : StateRel th (L.mem s2) σh := StateRel.of_agree hRf (fun q kd hq hs1 => by
    show (if q.bv ∈ l then _ else _) = _
    rw [if_neg (hnl q kd hq hs1)])
  have hCh : CdtRel th (L.mem s2) σh Gf := hCf.of_cdt rfl rfl
  -- the MDB delta
  have hfiL : fi.val < 2 ^ sb.val := by
    have : (1#64 <<< sb.val - fi.bv : BitVec 64).toNat = 2 ^ sb.val - fi.val := by
      rw [BitVec.toNat_sub, BitVec.toNat_shiftLeft]
      simp only [BitVec.toNat_ofNat, Nat.shiftLeft_eq, show fi.bv.toNat = fi.val from rfl]
      have hM' : 2 ^ sb.val < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hsb
      rw [show (1 % 2 ^ 64 * 2 ^ sb.val) % 2 ^ 64 = 2 ^ sb.val by
        rw [show (1 : Nat) % 2 ^ 64 = 1 from rfl, Nat.one_mul, Nat.mod_eq_of_lt hM']]
      omega
    rw [this, Nat.shiftRight_eq_div_pow] at hmem
    by_contra hc
    rw [show 2 ^ sb.val - fi.val = 0 by omega] at hmem; simp at hmem; omega
  have hnfiv : nfi.val = A + n * 32768 - p.val := by
    rw [← hA4]
    show (core.num.U64.wrapping_sub (core.num.U64.wrapping_add aligned total) p).bv.toNat = _
    rw [core.num.U64.wrapping_sub_bv_eq, core.num.U64.wrapping_add_bv_eq, htot, ← bv_eq_ofNat]
  have hRD : RetypeDelta th (L.mem s) (L.mem s1) (L.mem s2) G Gf src p sb fi nfi dev A 32768 n
      (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) (vcj A) := by
    refine ⟨hM, hsrcm, hcv0, hcs1, fun x hx hxs => hco1 x ((hM.members x).1 hx).1 hxs, hfiL, hA1,
      by omega, by omega, hk1, fun j _ => physF_vcpu _, fun j hj => vcj_base (RP.vIv hj),
      fun j hj => vcj_top RP.bfit hj (RP.vIv hj), fun j hj hu => by simp [vcj, isUt] at hu,
      fun j _ q us' f d hc => by simp [vcj] at hc, fun j hj hm => ?_, fun j l' hj hl he => ?_, hT1, hT1b,
      hT2a, hT2b, hT3⟩
    · obtain ⟨-, c0, h0, hn0⟩ := (hM.members _).1 hm
      rw [hempty (off.val + j) (by omega) (by omega)] at h0
      exact hn0 (eq_of_ok_eq h0).symm
    · have hj' : IsSlotAt th dest (off.val + j) := Or.inl ⟨r, hdest, by omega⟩
      have hl' : IsSlotAt th dest (off.val + l') := Or.inl ⟨r, hdest, by omega⟩
      by_contra hne
      rcases hj'.apart hP hl' (fun ⟨_, h2⟩ => hne (by omega)) with h | h <;>
        (change slotOf dest (off.val + j) = slotOf dest (off.val + l') at he; rw [he] at h; omega)
  -- the post
  refine ⟨rfl, ha2, σh, Gf, hrun, hRh, hVf', hMf, hCh, hIf,
    ⟨hRD.utinv hU, MdbStep.retype hRD hI hChf
      (fun z hz => by rw [hRvf z hz, hupd.rv ((hM.members z).1 hz).1]) (fun _ _ _ => trivial)⟩,
    hZf, fun hFI => ⟨?_, hFf (hFI.fm.recap hM.tree.nodup src (by rw [hcs1, hcv0]; exact CapSim.of_shape rfl rfl)
      (fun z hz hzs => hco1 z ((hM.members z).1 hz).1 hzs))⟩, hVl2, hE2, hChf, ?_,
    fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j)),
    hRD.toExp hU hMf (th_same_shape hk1 hrf) (fun hN => (hupd.nullClr hN).of_keep hNKf),
    ⟨fun q => by have : ¬ nt.val = 1 := by omega
                 have : ¬ nt.val = 4 := by omega
                 simp [thKindN, *], hrf⟩,
    fun j hj => ⟨dest, r, hdest, off.val + j, by omega, rfl⟩⟩
  · -- KTyped at the hook's state
    have hKf : KTyped th σf := by
      have hKa : KTyped th σa := hFI.kt.sub (ksub_of_eq (nks_setCap _ _) hσa)
      refine (ktyped_region hKa Ab A n 32768 rfl hk1 hfitA hrf (fun _ _ _ _ => rfl) ko
        (fun q _ => ⟨?_, ?_⟩)).sub (ksub_of_eq (nks_mapMx (nks_createCap _ _ _ _) _) hmx)
      · intro r' cs he _; simp [hko, Fl4Spec.defaultObject] at he
      · intro t' he; simp [hko, Fl4Spec.defaultObject] at he
    intro o
    by_cases ho : o ∈ l
    · refine ⟨fun r' cs h _ => ?_, fun t' h => ?_⟩
      · simp only [hσh, if_pos ho] at h; cases h
      · simp only [hσh, if_pos ho] at h; cases h
    · refine ⟨fun r' cs h hw => ?_, fun t' h => ?_⟩
      · simp only [hσh, if_neg ho] at h; exact (hKf o).1 r' cs h hw
      · simp only [hσh, if_neg ho] at h; exact (hKf o).2 t' h
  · -- the new VCPUs at the hook's state
    intro j hj
    refine hrel2 j hj _ σf ((), σh) (by rw [hhook]; rfl) ?_
    rw [retypeAddrs_vcpu, hwl]
    refine (mem_regionPtrs Ab A 32768 n rfl hk1 hfitA (vI A j)).2 ⟨j, hj, RP.vIv hj⟩

/-- **`NoIoTcb` across a retype described by `RetExp`** (module docstring). -/
theorem noIoTcb_retExp {th : TypedHeap} {m m' : U64 → U64} {G G' : MdbGhost} {A k w : Nat} {dslot : Nat → U64}
    {cj : Nat → capability.Cap} {xs : U64} (hE : RetExp th th m m' G G' A k w dslot cj xs)
    (hM' : MdbLinks th m' G') (hcj : ∀ j, j < w → ∀ f l o, cj j ≠ .IoPort f l o)
    (hT : NoIoTcb th m) : NoIoTcb th m' := by
  intro y hy f l o hc
  have hys : IsSlot th y := isSlot_thTcb hy
  have hym : y ∈ G'.chains.flatten := (hM'.members y).2 ⟨hys, _, capAt_capV _ _, by rw [hc]; simp⟩
  rcases hE.gmem y hym with hg | ⟨j, hj, rfl⟩
  · cases hu : isUt (capV m y)
    · rw [(hE.keep y hg hu).2] at hc; exact hT y hy f l o hc
    · have := hE.utk y hg hu; rw [hc] at this; simp [isUt] at this
  · rw [hE.newc j hj] at hc; exact absurd hc (hcj j hj f l o)

end

end
end Fl4Proofs.P3.VirtRetFullV2
