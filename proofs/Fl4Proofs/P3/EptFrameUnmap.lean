/-
P3 (line mmuAD, gen 42b15): **the EPT frame unmap** — FL4's `vspace::decode_frame` at `X86PageUnmap` on a mapped
`is_ept` frame cap (crates/fl4-core/src/arch/x86_64/vspace.rs l. 500-507: the caller's restart, when `asid ≠ 0`
`ept::unmap(asid, vaddr, ptr, size.bits(), false)`, then `set_cap` of `Frame { mapped: false, is_ept: false, asid: 0,
vaddr: 0 }`) against the extended decoder's EPT-mapped `X86PageUnmap` arm (Fl4Spec/Ext/VirtDispatch l. 71-72:
`.ept (.frameUnmap cap slot)`), `setThreadState cur Restart` and `performEptInvocation (.frameUnmap …)`
(Fl4Spec/Ext/VirtEptInv: `when (asid ≠ 0) guestUnmap asid gpa p (pageBitsForSize sz) false`, then `setCap` of the
unmapped page cap), modelled on P3/EptTableUnmapDec + P3/EptTableUnmapV.

* Spec: **`zv_decV_frameUnmap`** (the extended decoder's single outcome), **`performFrameUnmap_eq`**,
  `EptFrameUnmapSpec` (restart, then perform).
* FL4 at decode level: **`EptCore.frameUnmapF`** (restart, then for `asid ≠ 0` P3/EptUnmapRel's `EptCore.unmapRel`
  with `table = false` at the level `fbits size`, then `set_cap`; the guest address bound from `JExtEpt.vtop`'s
  frame conjunct, gen 42b15).
* **`VmEptState.frameUnmapSlot`**: `VmEptState` across the `set_cap` / `setCap` of an EPT-mapped frame cap's slot to
  the unmapped frame cap (P3/EptFrameMapV's slot step: `set_cap_refines`, `Vs.Recap.carryIo`, `MdbStep.recap`,
  `XTopAt.slotStep`, `JAtZB.vsStepJXB`, `VcpuCore.ofWG`, P3/EptFrameMap's `EptCore.frameSlot`).
* **`VmEptState.frameUnmap`** — the top: from `VmEptState` at an `Entered` spec state and the invoked
  `Frame ptr size rights dev true true asid va` cap in a CNode slot: FL4's `decode_frame` ⦃ `Ok ()`, and for some `σ'`
  the restart + perform has the single outcome `σ'` (`EptFrameUnmapSpec`) and `VmEptState` holds after ⦄. The hit of
  `ept::unmap` by P3/EptTableUnmapV's `VmEptState.unmapEntry` (a frame entry is no walk step, `frameEntryG`).
* **`eptFrameUnmap_decode_vmEpt`**: the same through `syscall.decode_invocation` (**`zv_sysdec_frame`**: through `vspace::decode`) and the
  extended decoder (`DecOut`).

Premise: `ArchRefines arI AR` [P] (as P3/EptUnmapRel). No new named premise. New file; root import after
`P3.EptTableUnmapV`. No existing statement changed.
-/
import Fl4Proofs.P3.EptTableUnmapV
import Fl4Proofs.P3.FrontEndLabel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-! ## Spec side -/

section Spec
open Fl4Spec

/-- **The extended decoder at an EPT-mapped page cap with the unmap label** (module docstring). -/
theorem zv_decV_frameUnmap (fp : Bool) {label : Data} (args : List Data) (cref : CapRef) (slot : CslotPtr)
    (dev : Bool) (p : ObjRef) (R : CapRights) (sz : VMPageSize) (x : Asid × VSpaceRef)
    (ec : List (Cap × CslotPtr)) (buffer : Option ObjRef) (h1 : dataToNat label ≠ fl4PageMapEptLabel)
    (h2 : invocationType label = .archInvocationLabel .x64PageUnmap) :
    fl4DecodeInvocationV (Z := Unit) fp label args cref slot (.archObjectCap (.pageCap dev p R .vmEptMap sz (some x)))
        ec buffer =
      NonDetE.returnOk (.ept (.frameUnmap (.pageCap dev p R .vmEptMap sz (some x)) slot)) := by
  unfold fl4DecodeInvocationV
  dsimp only
  rw [if_neg h1, if_neg (by rintro ⟨-, -, h⟩; rw [h2] at h; cases h), if_pos ⟨rfl, rfl, h2⟩]

/-- **The spec's perform of the EPT frame unmap**: `when (asid ≠ 0) guestUnmap` (single outcome `σ2`), then the CNode
slot set to the unmapped page cap. -/
theorem performFrameUnmap_eq {σ σ2 : State Unit} {dev : Bool} {p : ObjRef} {R : CapRights} {mt : VMMapType}
    {sz : VMPageSize} {asid gpa : Word}
    (hG : NonDet.when (asid ≠ 0) (guestUnmap (Z := Unit) asid gpa p (pageBitsForSize sz) false) σ =
      ({((), σ2)}, False))
    {pc : ObjRef} {r : Nat} {cs : CnodeContents} {idx : List Bool} (hkc : σ2.kheap pc = some (.cnode r cs))
    (hwf : wellFormedCnodeN r cs) (hidx : idx.length = r) :
    performEptInvocation (Z := Unit) (.frameUnmap (.pageCap dev p R mt sz (some (asid, gpa))) (pc, idx)) σ =
      ({((), setCnodeSlot σ2 pc r cs idx (.archObjectCap (.pageCap dev p R .vmNoMap sz none)))}, False) := by
  unfold performEptInvocation
  dsimp only
  rw [Notif.nd_bind_one hG]
  exact setCap_cnode _ hkc hwf hidx

/-- The spec after the frame unmap's decode: `set_thread_state cur Restart`, then the perform, with the single
outcome `σ'`. -/
def EptFrameUnmapSpec (σ : State Unit) (cap : ArchCap) (sl : CslotPtr) (σ' : State Unit) : Prop :=
  (setThreadState (Z := Unit) σ.curThread .restart >>= fun _ =>
    performEptInvocation (.frameUnmap cap sl)) σ = ({((), σ')}, False)

end Spec

/-! ## FL4 side -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
  {AR : A → Fl4Spec.Cr3 → Prop}

/-- FL4's `decode_invocation` at a `Frame` cap is `vspace.decode_frame`. -/
theorem zv_sysdec_frame (s : S) (a : A) (lbl len : U64) (slot : obj.Slot) (ptr rights asid va : U64)
    (size : capability.FrameSize) (dev m ep : Bool) (block call cd fp : Bool) (buf : U64)
    (ex : Array obj.Slot 3#usize) :
    syscall.decode_invocation st arI s a lbl len slot (.Frame ptr size rights dev m ep asid va) block call cd fp buf ex =
      vspace.decode_frame st arI s a lbl len slot (.Frame ptr size rights dev m ep asid va) call buf ex := by
  obtain ⟨ct, hct, -⟩ := P1.spec_ex_fd (P1.sched.cur_thread.spec (st := st) s)
  unfold syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  unfold vspace.decode
  rw [hct]; simp only [bind_ok]
  try rfl

/-- The unmap label is not the EPT map label. -/
theorem zv_unmapLbl_ne : fl4_abi.label.X86PageUnmap.val ≠ Fl4Spec.fl4PageMapEptLabel := by
  rw [← zv_frameEptLbl]
  intro h
  exact absurd (UScalar.eq_of_val_eq h) (by unfold fl4_abi.label.X86PageUnmap fl4_abi.label.X86PageMapEPT; decide)

/-- The spec's label type of `X86PageUnmap` (P3/FrontEndLabel's `fl4_label_table`). -/
theorem zv_unmapLbl_ty :
    Fl4Spec.invocationType fl4_abi.label.X86PageUnmap.bv = .archInvocationLabel .x64PageUnmap :=
  fl4_label_table.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem fbits_lvl (size : capability.FrameSize) :
    (fbits size).val = 39 ∨ (fbits size).val = 30 ∨ (fbits size).val = 21 ∨ (fbits size).val = 12 := by
  cases size <;> simp [fbits]

variable {X : Set U64} {XL : U64 → Nat} {th : TypedHeap}

open Fl4Proofs.P3.Vs in
set_option maxHeartbeats 4000000 in
/-- **FL4's unmap of an EPT-mapped frame cap, at decode level** (module docstring). -/
theorem EptCore.frameUnmapF {s s1 : S} {σ1 : Fl4Spec.State Unit} (C1 : EptCore (L := L) X XL th s1 σ1)
    {P : Set U64} (hR1 : VsRel P (L.mem s1) (L.ksb s1) σ1) (hA : ArchRefines arI AR) (a : A) {c : Fl4Spec.Cr3}
    (hAR : AR a c) {len ptr rights asid va : U64} {size : capability.FrameSize} {dev : Bool} (call : Bool)
    (dest buf : U64) (ex : Array obj.Slot 3#usize) (hva : va.val < 2 ^ 47) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) (hs1 : sched.set_thread_state st s ct sched.TS_RESTART = ok s1) :
    vspace.decode_frame st arI s a fl4_abi.label.X86PageUnmap len dest (.Frame ptr size rights dev true true asid va)
        call buf ex ⦃ res =>
      res.1 = .Ok () ∧ AR res.2.2 c ∧ ∃ s3 : S,
        ((asid = 0#u64 ∧ s3 = s1) ∨
          (asid ≠ 0#u64 ∧ UnmapOut (L := L) X XL σ1 s1 asid va ptr (fbits size) false s3
            (Fl4Spec.guestUnmap (Z := Unit) asid.bv va.bv ptr.bv (fbits size).val false σ1))) ∧
        res.2.1 = wrCap (L := L) s3 dest (.Frame ptr size rights dev false false 0#u64 0#u64) ⦄ := by
  have hne : ¬ fl4_abi.label.X86PageUnmap = fl4_abi.label.X86PageMap := by
    unfold fl4_abi.label.X86PageUnmap fl4_abi.label.X86PageMap; decide
  have hneEpt : ¬ fl4_abi.label.X86PageUnmap = fl4_abi.label.X86PageMapEPT := by
    unfold fl4_abi.label.X86PageUnmap fl4_abi.label.X86PageMapEPT; decide
  unfold vspace.decode_frame
  simp only [vspace.as_frame, bind_ok, hne, hneEpt, ↓reduceIte, hct, hs1]
  refine WP.spec_bind (Pₘ := fun r : S × A => AR r.2 c ∧ ∃ s3 : S,
      ((asid = 0#u64 ∧ s3 = s1) ∨
        (asid ≠ 0#u64 ∧ UnmapOut (L := L) X XL σ1 s1 asid va ptr (fbits size) false s3
          (Fl4Spec.guestUnmap (Z := Unit) asid.bv va.bv ptr.bv (fbits size).val false σ1))) ∧
      r.1 = s3) ?_ ?_
  · by_cases h0 : asid = 0#u64
    · rw [if_neg (by simp [h0])]
      exact (WP.spec_ok _).2 ⟨hAR, s1, Or.inl ⟨h0, rfl⟩, rfl⟩
    · rw [if_pos (by simpa using h0), bits_eq, bind_ok]
      refine WP.spec_mono (C1.unmapRel hR1 hA a hAR asid va ptr (fbits size) false hva (fbits_lvl size)) ?_
      rintro ⟨s3, a2⟩ ⟨h1, h2⟩
      exact ⟨h1, s3, Or.inr ⟨h0, h2⟩, rfl⟩
  · rintro ⟨s2, a1⟩ ⟨h1, s3, h2, h3⟩
    simp only at h3
    subst h3
    show (Std.bind (obj.Slot.set_cap st dest s2 (.Frame ptr size rights dev false false 0#u64 0#u64)) fun s4 =>
        ok (core.result.Result.Ok (), s4, a1)) ⦃ res => res.1 = .Ok () ∧ AR res.2.2 c ∧ ∃ s3 : S,
      ((asid = 0#u64 ∧ s3 = s1) ∨
        (asid ≠ 0#u64 ∧ UnmapOut (L := L) X XL σ1 s1 asid va ptr (fbits size) false s3
          (Fl4Spec.guestUnmap (Z := Unit) asid.bv va.bv ptr.bv (fbits size).val false σ1))) ∧
      res.2.1 = wrCap (L := L) s3 dest (.Frame ptr size rights dev false false 0#u64 0#u64) ⦄
    rw [set_cap_eq, bind_ok]
    exact (WP.spec_ok _).2 ⟨rfl, h1, s2, h2, rfl⟩

end

/-! ## `VmEptState` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64} {XL : U64 → Nat}

open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
  Fl4Proofs.P1

set_option maxHeartbeats 4000000 in
/-- **`VmEptState` across the `set_cap` of an EPT-mapped frame cap's slot to the unmapped frame cap** (module
docstring). -/
theorem VmEptState.frameUnmapSlot (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ)
    {pc : U64} {r : Nat} (hpc : Z.th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {ptr rights a0 v0 : U64} {size : capability.FrameSize} {dev : Bool}
    (hcv : capV (L.mem s) (cslotAddr (pc.bv, idx)) = .Frame ptr size rights dev true true a0 v0) :
    ∃ cs, σ.kheap pc.bv = some (.cnode r cs) ∧ Fl4Spec.wellFormedCnodeN r cs ∧
      VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D
        (wrCap (L := L) s (cslotAddr (pc.bv, idx)) (.Frame ptr size rights dev false false 0#u64 0#u64)) a
        (setCnodeSlot σ pc.bv r cs idx
          (.archObjectCap (.pageCap dev ptr.bv (vmRightsOf rights) .vmNoMap (frameSizeOf size) none))) := by
  have B := J.1.1
  have Cv := J.1.2
  have C := J.2
  set x := cslotAddr (pc.bv, idx) with hxdef
  have hP : Placed Z.th := B.xtop.rel.1
  have hA : AbsSlot Z.th (pc.bv, idx) := ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩
  have hxs : IsSlot Z.th x := hA.isSlot
  obtain ⟨t, ht⟩ : X.Nonempty := by
    have h := C.exte.cap x hxs
    rw [hcv] at h
    exact h ⟨rfl, rfl⟩
  obtain ⟨cs, hkc, hwf, hsl⟩ := B.xtop.rel.2.1.1.cnode pc r hpc
  have hcx : capAt (L.mem s) x = ok (.Frame ptr size rights dev true true a0 v0) := by rw [capAt_capV, hcv]
  have hrw : 1 ≤ rights.val ∧ rights.val ≤ 3 := by
    obtain ⟨c0, ac, hc0, -, hca0⟩ := hsl idx hidx
    have hc0' : capAt (L.mem s) x = ok c0 := hc0
    rw [hcx] at hc0'
    have e : c0 = .Frame ptr size rights dev true true a0 v0 := (ok_inj hc0').symm
    subst e
    exact hca0.1
  set c : capability.Cap := .Frame ptr size rights dev false false 0#u64 0#u64 with hc
  set nc : Fl4Spec.ArchCap := .pageCap dev ptr.bv (vmRightsOf rights) .vmNoMap (frameSizeOf size) none with hnc_def
  have hcl := hcx
  rw [capAt_words] at hcl
  have hew0 := decode_encWf hcl
  have hew : EncWf c := ⟨hew0.1, hew0.2.1, by decide, by decide⟩
  have hca : CapRel c (.archObjectCap nc) := ⟨hrw, rfl⟩
  obtain ⟨hSt, hSV, -, -, -⟩ := B.xtop.rel.2.1
  have hcvd : CapValid Z.th c := by have h := hSV.abs hA hcx; exact h
  have hSC := set_cap_refines (L := L) Z.th s σ hSt hSV hP hpc hidx c (.archObjectCap nc) hca hcvd hew
  rw [set_cap_eq, WP.spec_ok] at hSC
  obtain ⟨σ2, hsc, hSt2, hSV2, -, -, -, -⟩ := hSC
  have hσ2 : σ2 = setCnodeSlot σ pc.bv r cs idx (.archObjectCap nc) := by
    rw [setCap_cnode _ hkc hwf hidx] at hsc
    have := congrArg Prod.fst hsc
    simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at this
    exact this.symm
  subst hσ2
  set s2c := wrCap (L := L) s x c with hs2c
  have hF3 := set_cap_foot (L := L) hP hxs s c hew
  rw [set_cap_eq, WP.spec_ok] at hF3
  obtain ⟨hSF3, hcv3⟩ := hF3
  have hfx := hxs.fit hP
  have hal32 := hxs.align hP
  have hWF := set_cap_frame (L := L) s x c (by omega) (by omega)
  rw [set_cap_eq, WP.spec_ok] at hWF
  have h8 : (wordOf x 8#u64).val = x.val + 8 := wa8_val (by omega)
  have hW3 : P1.WritesIn st s s2c (fun b => b = x ∨ b = wordOf x 8#u64) := by
    refine ⟨hWF.1, hWF.2.1, fun b hb hn => hWF.2.2 b hb fun hr => hn (by
      obtain ⟨g1, g2⟩ := hr
      have hb8 : b.val % 8 = 0 := hb
      by_cases e : b.val = x.val
      · exact Or.inl (UScalar.eq_of_val_eq e)
      · exact Or.inr (UScalar.eq_of_val_eq (by rw [h8]; omega)))⟩
  have hks3 : L.ksb s2c = L.ksb s := hW3.1
  have hcap3 : ∀ y, IsSlot Z.th y → y ≠ x → capV (L.mem s2c) y = capV (L.mem s) y := fun y hy hne => by
    unfold capV; rw [((hSF3 y hy).2.2 hne).1, ((hSF3 y hy).2.2 hne).2]
  have hLk : Vs.IoLike (capV (L.mem s2c) x) (capV (L.mem s) x) := by
    rw [hcv3, hcv]; exact ⟨rfl, rfl, rfl, trivial⟩
  have hsh : shape (capV (L.mem s2c) x) = shape (capV (L.mem s) x) := hLk.1
  have hok : okey (capV (L.mem s2c) x) = okey (capV (L.mem s) x) := hLk.2.1
  have hnu : isUt (capV (L.mem s) x) = false := by rw [hcv]; rfl
  have hK3 : KFoot σ (setCnodeSlot σ pc.bv r cs idx (.archObjectCap nc)) := KFoot.cnode hkc hwf idx _
  obtain ⟨-, ⟨-, -, hM, hCd, hI⟩, hFI, -, hMO, -, -⟩ := B.xtop.rel
  obtain ⟨hM', hCd', hI', hFI'⟩ := Vs.Recap.carryIo hM hCd hI hFI hSF3 hLk hK3
  have hvok : ∀ P L4 L3 L2 L1 : Set U64, VCapOK P L4 L3 L2 L1 (capV (L.mem s) x) →
      VCapOK P L4 L3 L2 L1 (capV (L.mem s2c) x) := by
    intro P L4 L3 L2 L1 hv
    rw [hcv] at hv
    obtain ⟨-, hpa, -⟩ := hv
    rw [hcv3]
    exact (show (false = true → (0#u64 : U64) ≠ 0#u64) ∧ PaM ptr (frameMaskOf size) ∧
      (false = true → UserV (0#u64 : U64)) from ⟨(fun h => nomatch h), hpa, (fun h => nomatch h)⟩)
  have hMO3 : MdbOKV (L.ksb s) (L.mem s2c) Z.G :=
    (MdbStep.recap hM x (CapAlike.of_shape hsh hok fun h => by rw [hnu] at h; cases h) hvok
      (fun z hz hne => hcap3 z ((hM.members z).1 hz).1 hne)
      (fun z hz => by unfold revOf; rw [(hSF3 z ((hM.members z).1 hz).1).2.1])).okv hMO
  have hTS : ∀ t', Z.th t' = some .tcb → capAt (L.mem s2c) (slotOf t' 1) = capAt (L.mem s) (slotOf t' 1) := by
    intro t' ht'
    have hs : IsSlot Z.th (slotOf t' 1) := ⟨t', 1, Or.inr ⟨ht', by simp [tcbSlots]⟩, rfl⟩
    have he : cslotAddr (t'.bv, Fl4Spec.tcbCnodeIndex 1) = slotOf t' 1 := by
      show slotAddr t'.bv (Fl4Spec.ofBl _) = _
      rw [slotAddr_ofBl, tcbCnodeIndex_blVal 1 (by decide)]
    have hne : slotOf t' 1 ≠ x := fun e => cnode_slot_ne_tcb hP hpc hidx ht' 1 (by decide) (by rw [he, e])
    rw [capAt_capV, capAt_capV, hcap3 _ hs hne]
  have hSW : ∀ b, (b = x ∨ b = wordOf x 8#u64) → SlotWd Z.th b := by
    rintro b (rfl | rfl)
    · exact ⟨x, hxs, 0#u64, Or.inl rfl, by rw [wordOf_zero]⟩
    · exact ⟨x, hxs, 8#u64, Or.inr (Or.inl rfl), rfl⟩
  have hX3 : XTopAt (L := L) AR { Z with G := Z.G } s2c a (setCnodeSlot σ pc.bv r cs idx (.archObjectCap nc)) :=
    XTopAt.slotStep B.xtop (hW3.mono hSW) (cnK_setCnodeSlot hkc hwf hidx _) (keepC_setCnodeSlot hkc _)
      ⟨hSt2, hSV2, hM', hCd', hI'⟩ hFI' hMO3 hTS
  have hvc : Vs.VsSlotsW Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.mem s2c) := fun y hy => by
    by_cases e : y = x
    · rw [e]
      have h0 := B.vsc x hxs
      rw [hcv] at h0
      have h1 : VCapOK Z.P Z.L4 Z.L3 Z.L2 Z.L1 (capV (L.mem s) x) := by rw [hcv]; exact h0
      have h2 := hvok _ _ _ _ _ h1
      rw [hcv3] at h2 ⊢
      exact h2
    · rw [hcap3 y hy e]; exact B.vsc y hy
  have hvn : Z.vx = ∅ → Vs.VsNamed Z.th (L.mem s2c) (L.ksb s2c) :=
    B.vsShr (G' := Z.G) hX3 hks3 (VsKeep.of_vk fun y hy => by
      by_cases e : y = x
      · rw [e, hcv3, hcv]; exact ⟨rfl, rfl⟩
      · rw [hcap3 y hy e]; exact ⟨rfl, rfl⟩)
      (ArchShr.of_keep rfl fun q ao hq => by
        have hq' : q ≠ pc.bv := fun e => by rw [e, hkc] at hq; cases hq
        simp [setCnodeSlot, hq'])
  have B2 : JAtZB (L := L) arI AR Z H Cs Ac Lst D s2c a (setCnodeSlot σ pc.bv r cs idx (.archObjectCap nc)) :=
    B.vsStepJXB ⟨B.scOut⟩ hpc hidx (TabsArch.empty σ) (L3' := Z.L3) (L2' := Z.L2) (L1' := Z.L1) hX3
      (vsSFr_setCnodeSlot hkc hwf hidx _) (hW3.mono fun b hb => Or.inl (Or.inr hb)) hcap3 hsh hok hnu
      (fun y hy => ⟨(hSF3 y hy).1, (hSF3 y hy).2.1⟩) hvc ⟨subset_rfl, subset_rfl, subset_rfl⟩ hvn
  -- `VcpuCore` after the slot step
  obtain ⟨Q, R0, hcq, -⟩ := B.xtop.fin.1.1.1.lists
  have hT := hcq.tcbs
  have hothc : ∀ q, q ≠ pc.bv → (setCnodeSlot σ pc.bv r cs idx (.archObjectCap nc)).kheap q = σ.kheap q :=
    fun q hq => by simp [setCnodeSlot, hq]
  have hvpc : ∀ u ∈ V, u.bv ≠ pc.bv := fun u hu e => by
    obtain ⟨vx, hvx⟩ := Cv.vm.spec u hu
    rw [e, hkc] at hvx; cases hvx
  have Cv2 : VcpuCore (L := L) V Z H s2c (setCnodeSlot σ pc.bv r cs idx (.archObjectCap nc)) :=
    Cv.ofWG B B2 hW3
      (fun y hy => by
        by_cases e : y = x
        · right
          rw [e, hcv3, hcv]
          exact ⟨rfl, trivial, fun f l o h => by rw [hc] at h; cases h⟩
        · exact Or.inl (hcap3 y hy e))
      (fun u hu b hb => B.slotWd_vcpu Cv.vm (hSW b hb) u hu)
      (fun b hb => B.slotWd_head (hSW b hb))
      (fun t' ht' => by
        have htT := B.thT t' ht'
        have ev := tVcpuA_val hT htT
        exact hW3.mem_eq (tVcpuA_aligned hT htT) fun hb =>
          B.slotWd_tcb (hSW _ hb) ht' (by omega) (by omega) rfl)
      (fun u hu => hothc _ (hvpc u hu))
      (fun o ko' ho => by
        by_cases e : o = pc.bv
        · subst e
          simp only [setCnodeSlot, Function.update_self, Option.some.injEq] at ho
          subst ho
          exact ⟨_, hkc, rfl⟩
        · rw [hothc _ e] at ho; exact ⟨ko', ho, rfl⟩)
      (fun o x' ho hx => by
        have e : o ≠ pc.bv := fun e => by subst e; simp [setCnodeSlot] at ho
        rw [hothc _ e] at ho; exact ⟨x', ho, hx⟩)
      (fun p vs hp => by
        have e : p ≠ pc.bv := fun e => by subst e; simp [setCnodeSlot] at hp
        rw [hothc _ e] at hp; exact hp)
  -- `EptCore` after the slot step
  have hxa : ∀ b, (b = x ∨ b = wordOf x 8#u64) → ∀ u ∈ X, b.val < u.val ∨ u.val + 4096 ≤ b.val :=
    fun b hb => B.slotWd_ept C b (hSW b hb)
  have C2 : EptCore (L := L) X XL Z.th s2c (setCnodeSlot σ pc.bv r cs idx (.archObjectCap nc)) :=
    C.frameSlot ht hW3 hxa hcv hcv3 (fun h => by cases h) hcap3 (cnK_setCnodeSlot hkc hwf hidx _)
  exact ⟨cs, hkc, hwf, ⟨B2, Cv2⟩, C2⟩

set_option maxHeartbeats 4000000 in
/-- **The EPT frame unmap at `VmEptState`** (module docstring). -/
theorem VmEptState.frameUnmap (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (hA : ArchRefines arI AR) {len ptr rights asid va : U64} {size : capability.FrameSize} {dev : Bool}
    (call : Bool) (buf : U64) (ex : Array obj.Slot 3#usize)
    {pc : U64} {r : Nat} (hpc : Z.th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    (hcx : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Frame ptr size rights dev true true asid va)) :
    vspace.decode_frame st arI s a fl4_abi.label.X86PageUnmap len (cslotAddr (pc.bv, idx))
        (.Frame ptr size rights dev true true asid va) call buf ex ⦃ res =>
      res.1 = .Ok () ∧ ∃ σ' : Fl4Spec.State Unit,
        EptFrameUnmapSpec σ (.pageCap dev ptr.bv (vmRightsOf rights) .vmEptMap (frameSizeOf size)
          (some (asid.bv, va.bv))) (pc.bv, idx) σ' ∧
        ∃ Lst' : U64 → List U64, VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst' D res.2.1 res.2.2 σ' ⦄ := by
  have B := J.1.1
  have C := J.2
  set x := cslotAddr (pc.bv, idx) with hxdef
  have hP : Placed Z.th := B.xtop.rel.1
  have hA0 : AbsSlot Z.th (pc.bv, idx) := ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩
  have hxs : IsSlot Z.th x := hA0.isSlot
  have hcv0 : capV (L.mem s) x = .Frame ptr size rights dev true true asid va := capV_of_capAt hcx
  have hva : va.val < 2 ^ 47 := C.exte.vtop.2 _ hxs _ _ _ _ _ _ hcv0
  -- the restart
  have hct := P1.cur_thread_ok (L := L) s
  obtain ⟨hcur, xct, hkt, -⟩ := B.curRunnable hni hct
  have hAR : AR a σ.archState.x64CurrentCr3 := B.xtop.fin.1.1.2.2.2.2.2.2
  obtain ⟨s1, σ1, Lst1, hs1, hst1, J1⟩ := VmEptState.restart (arI := arI) J hni
  have e1 : σ1 = stsAct (updK σ (L.curW s).bv (.tcb { xct with tcbState := .restart })) (L.curW s).bv := by
    have hst := hst1
    rw [hcur, Notif.setThreadState_eq .restart hkt] at hst
    have := congrArg (fun q => ((), σ1) ∈ q.1) hst
    simp only [Set.mem_singleton_iff, Prod.mk.injEq, true_and] at this
    exact of_eq_true this
  have har1 : σ1.archState = σ.archState := by rw [e1]; unfold stsAct; split <;> rfl
  have hSS1 : SlotsSame Z.th (L.mem s) (L.mem s1) := by
    have h := set_thread_state_slots (L := L) Z.th hP s (L.curW s) sched.TS_RESTART (B.xtop.curTcb hcur).1
      B.kern.act
    rw [hs1, WP.spec_ok] at h; exact h
  have hcv1 : capV (L.mem s1) x = .Frame ptr size rights dev true true asid va := by
    rw [hSS1.capV hxs]; exact hcv0
  refine WP.spec_mono (J1.2.frameUnmapF J1.1.1.xtop.fin.2.1 hA a hAR call x buf ex hva hct hs1) ?_
  rintro res ⟨h1, hAR2, s3, hcase, hres⟩
  refine ⟨h1, ?_⟩
  have hAR2' : AR res.2.2 σ1.archState.x64CurrentCr3 := by rw [har1]; exact hAR2
  -- the unmap
  obtain ⟨σ2, J3, hSS3, har2, hG⟩ : ∃ σ2 : Fl4Spec.State Unit,
      VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst1 D s3 a σ2 ∧ SlotsSame Z.th (L.mem s1) (L.mem s3) ∧
      σ2.archState = σ1.archState ∧
      Fl4Spec.NonDet.when (asid.bv ≠ 0) (Fl4Spec.guestUnmap (Z := Unit) asid.bv va.bv ptr.bv
        (Fl4Spec.pageBitsForSize (frameSizeOf size)) false) σ1 = ({((), σ2)}, False) := by
    rcases hcase with ⟨h0, rfl⟩ | ⟨h0, hU⟩
    · refine ⟨σ1, J1, SlotsSame.refl _ _, rfl, ?_⟩
      have hb : ¬ asid.bv ≠ 0 := by rw [h0]; exact fun h => h rfl
      unfold Fl4Spec.NonDet.when; rw [if_neg hb]; rfl
    · have hb : asid.bv ≠ 0 := fun h => h0 (P1.eq_of_bv (by rw [h]; rfl))
      rw [← fbits_val]
      rcases hU with ⟨rfl, hG⟩ | ⟨t, ht, es, hXt, hPt, hk, -, rfl, hG⟩
      · refine ⟨σ1, J1, SlotsSame.refl _ _, rfl, ?_⟩
        unfold Fl4Spec.NonDet.when; rw [if_pos hb]; exact hG
      · obtain ⟨J3, hSS3⟩ := J1.unmapEntry ht (g := va.bv) hva (by rw [hXt]; exact hPt) hk _
        refine ⟨_, J3, hSS3, rfl, ?_⟩
        unfold Fl4Spec.NonDet.when; rw [if_pos hb, hG, storeGuestEntry_eq hk]
  have hcv3 : capV (L.mem s3) x = .Frame ptr size rights dev true true asid va := by
    rw [hSS3.capV hxs]; exact hcv1
  obtain ⟨cs, hkc3, hwf, J5⟩ := J3.frameUnmapSlot hpc hidx hcv3
  refine ⟨setCnodeSlot σ2 pc.bv r cs idx
    (.archObjectCap (.pageCap dev ptr.bv (vmRightsOf rights) .vmNoMap (frameSizeOf size) none)), ?_, Lst1, ?_⟩
  · show (Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart >>= fun _ =>
      Fl4Spec.performEptInvocation (.frameUnmap (.pageCap dev ptr.bv (vmRightsOf rights) .vmEptMap (frameSizeOf size)
        (some (asid.bv, va.bv))) (pc.bv, idx))) σ = _
    rw [Notif.nd_bind_one hst1]
    exact performFrameUnmap_eq hG hkc3 hwf hidx
  · rw [hres]
    refine J5.archV ?_
    show AR res.2.2 σ2.archState.x64CurrentCr3
    rw [har2]; exact hAR2'

set_option maxHeartbeats 4000000 in
/-- **The extended decoder and FL4's `syscall.decode_invocation` on an EPT-mapped frame cap with the unmap label, at
`VmEptState`** (module docstring). -/
theorem eptFrameUnmap_decode_vmEpt (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ)
    (hni : Entered σ) (hA : ArchRefines arI AR) {lbl len ptr rights asid va : U64} {size : capability.FrameSize}
    {dev : Bool} (hl : lbl = fl4_abi.label.X86PageUnmap) (block call cd fp : Bool) (buf : U64)
    (ex : Array obj.Slot 3#usize)
    {pc : U64} {r : Nat} (hpc : Z.th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    (hcx : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Frame ptr size rights dev true true asid va))
    (args : List Fl4Spec.Data) (ec : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (fp' : Bool) (cref : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    DecOut (Fl4Spec.fl4DecodeInvocationV (Z := Unit) fp' lbl.bv args cref (pc.bv, idx)
        (absCap (.Frame ptr size rights dev true true asid va)) ec buffer) σ
      (.ept (.frameUnmap (.pageCap dev ptr.bv (vmRightsOf rights) .vmEptMap (frameSizeOf size)
        (some (asid.bv, va.bv))) (pc.bv, idx))) ∧
    syscall.decode_invocation st arI s a lbl len (cslotAddr (pc.bv, idx)) (.Frame ptr size rights dev true true asid va)
        block call cd fp buf ex ⦃ res =>
      res.1 = .Ok () ∧ ∃ σ' : Fl4Spec.State Unit,
        EptFrameUnmapSpec σ (.pageCap dev ptr.bv (vmRightsOf rights) .vmEptMap (frameSizeOf size)
          (some (asid.bv, va.bv))) (pc.bv, idx) σ' ∧
        ∃ Lst' : U64 → List U64, VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst' D res.2.1 res.2.2 σ' ⦄ := by
  subst hl
  have habs : absCap (.Frame ptr size rights dev true true asid va) =
      .archObjectCap (.pageCap dev ptr.bv (vmRightsOf rights) .vmEptMap (frameSizeOf size)
        (some (asid.bv, va.bv))) := rfl
  refine ⟨?_, by rw [zv_sysdec_frame]; exact VmEptState.frameUnmap J hni hA call buf ex hpc hidx hcx⟩
  rw [habs, zv_decV_frameUnmap _ _ _ _ _ _ _ _ _ _ _ (by rw [zv_dataToNat]; exact zv_unmapLbl_ne) zv_unmapLbl_ty]
  exact DecOut.of_eq rfl

end

end

end Fl4Proofs.P3
